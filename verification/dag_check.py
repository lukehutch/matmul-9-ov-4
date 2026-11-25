"""Check that a paper, and its check file, follow the backward-only DAG rule.

Usage:  python3 dag_check.py PAPER.tex [CHECKFILE.py]

STANDARDS.md ("Backward DAG structure" and "No forward references to
supplemental material") allows a reference to point forward only from the
abstract or the introduction, or to a float (table, figure) or an appendix.
The main text may never point into the supplement, which is everything after
the bibliography. An appendix, and the supplement, may point only backward
within themselves.

The paper is split into regions by its markers:
  abstract      \\begin{abstract} ... \\end{abstract}
  intro         \\section{Introduction} up to the next \\section
  main          from there up to \\appendix or the bibliography
  appendix      \\appendix up to the bibliography
  supplement    after the bibliography
Each \\ref, \\eqref, \\cref, \\Cref and \\autoref is compared with the position
of its \\label. A reference whose label lies later in the file, from a region
where that is not allowed, is a violation. A label inside a table or figure
environment (or a longtable) is a float and is exempt.

Prose pointers to later text ("shown below", "discussed later", "the next
section", "will be derived", "we will") are forward references without a
\\ref, and fail the check in the main text, appendix and supplement. A bare
"below" or "later" is not matched, because in these papers it is almost always
mathematical ("bounded below", "below the threshold") or temporal ("an
instant later").

With a check file (sgm_check.py, sgm_wavefn_check.py), it also checks that
  (a) the eq() blocks appear in the order of their .tex lines, and
  (b) every label named on a "Derived from:" comment line of a block is
      defined in the paper before that block's equation, so that the check
      file never derives an equation from a later one. The exemptions of
      the paper check apply: a main-text block may depend on an appendix,
      and a float, as the dependency or as the block itself, is exempt.

Exit status 1 when any violation is found.
"""
import re
import sys

REF = re.compile(r"\\(?:eqref|ref|cref|Cref|autoref|pageref)\*?\{([^}]*)\}")
LABEL = re.compile(r"\\label\{([^}]*)\}")
POINTER = re.compile(
    r"\b((?:see|shown|given|derived|discussed|treated|proved|defined|stated|"
    r"computed|described|explained|listed|returned to)\s+(?:in detail\s+)?"
    r"(?:below|later)|(?:next|following|subsequent|later) (?:section|subsection|appendix)|"
    r"will be (?:shown|derived|proved|discussed|treated|given)|we will)\b", re.I)


def strip_comments(text):
    """Blank out % comments (keeping \\%), preserving line structure."""
    return "\n".join(re.sub(r"(?<!\\)%.*", "", ln) for ln in text.split("\n"))


def line_of(text, pos):
    return text.count("\n", 0, pos) + 1


def regions(text):
    """Return a function mapping a character offset to its region name."""
    def find(pat, start=0):
        m = re.compile(pat).search(text, start)
        return m.start() if m else None
    abs_a, abs_b = find(r"\\begin\{abstract\}"), find(r"\\end\{abstract\}")
    intro = find(r"\\section\*?\{Introduction\}")
    after_intro = find(r"\\section", intro + 1) if intro is not None else None
    appendix = find(r"\\appendix")
    bib = find(r"\\bibliography\{")
    end = len(text)
    bounds = []
    if abs_a is not None:
        bounds.append((abs_a, abs_b, "abstract"))
    if intro is not None:
        bounds.append((intro, after_intro, "intro"))
    main_end = min(x for x in (appendix, bib, end) if x is not None)
    bounds.append((after_intro or 0, main_end, "main"))
    if appendix is not None:
        bounds.append((appendix, bib or end, "appendix"))
    if bib is not None:
        bounds.append((bib, end, "supplement"))

    def region(pos):
        for a, b, name in bounds:
            if a <= pos < b:
                return name
        return "front"
    return region


def float_spans(text):
    spans = []
    for m in re.finditer(r"\\begin\{(table|figure|longtable)\*?\}.*?\\end\{\1\*?\}", text, re.S):
        spans.append((m.start(), m.end()))
    return spans


def check_paper(path):
    text = strip_comments(open(path, encoding="utf-8").read())
    region = regions(text)
    floats = float_spans(text)
    labels = {}
    bad = []
    for m in LABEL.finditer(text):
        key = m.group(1)
        if key in labels:
            bad.append((line_of(text, m.start()), key,
                        f"duplicate label (first defined at L{line_of(text, labels[key])})"))
        else:
            labels[key] = m.start()
    n_refs = 0
    for m in REF.finditer(text):
        src = m.start()
        src_reg = region(src)
        for key in (k.strip() for k in m.group(1).split(",")):
            n_refs += 1
            if key not in labels:
                bad.append((line_of(text, src), key, "label not defined"))
                continue
            tgt = labels[key]
            tgt_reg = region(tgt)
            is_float = any(a <= tgt < b for a, b in floats)
            if src_reg in ("main", "intro", "abstract") and tgt_reg == "supplement":
                bad.append((line_of(text, src), key,
                            f"{src_reg} text points into the supplement (L{line_of(text, tgt)})"))
                continue
            if tgt <= src or is_float or src_reg in ("abstract", "intro", "front"):
                continue
            if src_reg == "main" and tgt_reg == "appendix":
                continue
            bad.append((line_of(text, src), key,
                        f"forward reference from {src_reg} to {tgt_reg} L{line_of(text, tgt)}"))
    pointers = []
    for m in POINTER.finditer(text):
        if region(m.start()) in ("main", "appendix", "supplement"):
            ln = line_of(text, m.start())
            ctx = text[max(0, m.start() - 70):m.end() + 50].replace("\n", " ")
            pointers.append((ln, ctx))
    print(f"{path}: {len(labels)} labels, {n_refs} references checked")
    for ln, key, why in bad:
        print(f"  VIOLATION L{ln}: \\ref{{{key}}}: {why}")
    for ln, s in pointers:
        print(f"  VIOLATION L{ln}: prose pointer to later text: ...{s}...")
        bad.append((ln, "", "prose pointer"))
    return labels, text, bad


def check_checkfile(path, labels, text):
    src = open(path, encoding="utf-8").read().split("\n")
    # Match any colon-qualified label token (including numeric/underscore prefixes) so unknown prefixes are rejected too.
    label_pat = re.compile(r"(?<![\w.-])([\w.-]+:[\w:.\-]+)")
    bad = []
    blocks = []      # (line in check file, tex line, label)
    for i, ln in enumerate(src, 1):
        m = re.match(r'\s*eq\("([^"]*)",\s*(\d+)', ln)
        if m:
            lbl, tln = m.group(1), int(m.group(2))
            blocks.append((i, tln, lbl))
            if lbl not in labels:
                bad.append(f"{path}:{i}: eq() label {lbl!r} is not defined in paper")
            else:
                actual_ln = line_of(text, labels[lbl])
                if tln != actual_ln:
                    bad.append(f"{path}:{i}: eq() line for {lbl} is L{tln}, but paper defines it at L{actual_ln}")
    for (i0, t0, l0), (i1, t1, l1) in zip(blocks, blocks[1:]):
        if t1 < t0:
            bad.append(f"{path}:{i1}: block {l1} (L{t1}) comes after {l0} (L{t0})")
    # Each "Derived from:" comment (with its continuation lines) belongs to the
    # next eq() call below it.
    # The exemptions of check_paper apply here too: main text may depend on an
    # appendix, and a float (as dependency or as the block itself) is exempt.
    region = regions(text)
    floats = float_spans(text)
    line_start = [0] + [m.end() for m in re.finditer("\n", text)]
    in_float = lambda pos: any(a <= pos < b for a, b in floats)
    for k, (i, tex_line, label) in enumerate(blocks):
        start = blocks[k - 1][0] if k else 0
        chunk = src[start:i]
        derived = []
        on = False
        for ln in chunk:
            s = ln.strip()
            scan = s
            if s.startswith("# Derived from:"):
                on = True
                scan = s[len("# Derived from:"):]
            elif on and (not s.startswith("#") or re.match(r"#\s*(Test|Mutant|States):", s)):
                on = False
            if on:
                derived += label_pat.findall(scan)
        for d in derived:
            d = d.rstrip(".:")
            if d not in labels:
                bad.append(f"{path}:{i}: {label} cites unknown label {d}")
            elif d == label:
                bad.append(f"{path}:{i}: {label} lists itself in Derived from")
            else:
                d_line = line_of(text, labels[d])
                actual_line = line_of(text, labels[label]) if label in labels else tex_line
                pos = line_start[actual_line - 1]
                if (in_float(pos) or in_float(labels[d])
                        or (region(pos) == "main" and region(labels[d]) == "appendix")):
                    continue
                if d_line > actual_line:
                    bad.append(f"{path}:{i}: {label} (L{actual_line}) is derived from later {d} (L{d_line})")
    print(f"{path}: {len(blocks)} equation blocks checked for order and derivation sources")
    for b in bad:
        print("  VIOLATION " + b)
    return bad


if __name__ == "__main__":
    labels, text, bad = check_paper(sys.argv[1])
    if len(sys.argv) > 2:
        bad = bad + check_checkfile(sys.argv[2], labels, text)
    sys.exit(1 if bad else 0)
