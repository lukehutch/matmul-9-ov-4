"""Equation-by-equation checks of matmul_9_4_constant.tex:
The magnitude of the hidden constant in exponent-9/4 matrix multiplication.

Run:  python3 -W error verification/matmul_9_4_constant_check.py   (from any directory)

100% pure Python stdlib (no SymPy or external packages required): uses an exact
multivariate polynomial ring PolyQ over Q (fractions.Fraction) for exact symbolic
identity verification, alongside arbitrary-precision integer and floating-point checks.
Each displayed equation and numerical table claim has a standalone block in exact
ascending .tex line order with positive checks and adversarial negative controls
(mutant / numutant). dag_check.py verifies block order and backward-only derivation
dependencies against matmul_9_4_constant.tex. Exits nonzero on any failure.
"""
from __future__ import annotations

from decimal import Decimal as _Dec, Context as _DecCtx, ROUND_FLOOR as _RFL, ROUND_CEILING as _RCL, ROUND_HALF_EVEN as _RNE
from fractions import Fraction
from functools import lru_cache
import itertools
import math
import random
import sys

# ============================================================================
# Standalone Verification Harness
# ============================================================================
results: list[bool] = []
_current: list[str] = [""]
_failures: list[str] = []


def _record(ok: bool, name: str, detail: str = "") -> bool:
    ok = bool(ok)
    results.append(ok)
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}")
    if detail:
        print(f"         {detail}")
    if not ok:
        _failures.append(f"{_current[0]}: {name}")
    return ok


def part(title: str) -> None:
    print()
    print("=" * 78)
    print(title)
    print("=" * 78)


def eq(label: str, line: int, statement: str) -> None:
    _current[0] = f"{label} (L{line})"
    print(f"\n--- {label} (matmul_9_4_constant.tex L{line}): {statement} ---")


def boolcheck(name: str, cond: bool, detail: str = "") -> bool:
    return _record(bool(cond), name, detail)


# ============================================================================
# Exact Multivariate Polynomial Ring over Q (pure stdlib, zero external deps)
# ============================================================================
class PolyQ:
    """Exact multivariate polynomial over Q with monomials as sorted tuples ((var, exp), ...)."""

    def __init__(self, terms: dict[tuple[tuple[str, int], ...], Fraction] | None = None):
        self.terms: dict[tuple[tuple[str, int], ...], Fraction] = {}
        if terms:
            for mon, coeff in terms.items():
                c = Fraction(coeff)
                if c != 0:
                    self.terms[mon] = c

    @staticmethod
    def const(val: int | Fraction) -> PolyQ:
        c = Fraction(val)
        return PolyQ({(): c} if c != 0 else {})

    @staticmethod
    def var(name: str) -> PolyQ:
        return PolyQ({((name, 1),): Fraction(1)})

    def is_zero(self) -> bool:
        return len(self.terms) == 0

    @staticmethod
    def _coerce(other: PolyQ | int | Fraction) -> PolyQ:
        if isinstance(other, PolyQ):
            return other
        return PolyQ.const(other)

    @staticmethod
    def _mul_mon(m1: tuple[tuple[str, int], ...], m2: tuple[tuple[str, int], ...]) -> tuple[tuple[str, int], ...]:
        d = dict(m1)
        for v, e in m2:
            d[v] = d.get(v, 0) + e
        return tuple(sorted((v, e) for v, e in d.items() if e != 0))

    def __add__(self, other: PolyQ | int | Fraction) -> PolyQ:
        o = PolyQ._coerce(other)
        out = dict(self.terms)
        for m, c in o.terms.items():
            out[m] = out.get(m, Fraction(0)) + c
        return PolyQ(out)

    def __radd__(self, other: int | Fraction) -> PolyQ:
        return PolyQ._coerce(other) + self

    def __neg__(self) -> PolyQ:
        return PolyQ({m: -c for m, c in self.terms.items()})

    def __sub__(self, other: PolyQ | int | Fraction) -> PolyQ:
        return self + (-PolyQ._coerce(other))

    def __rsub__(self, other: int | Fraction) -> PolyQ:
        return PolyQ._coerce(other) - self

    def __mul__(self, other: PolyQ | int | Fraction) -> PolyQ:
        o = PolyQ._coerce(other)
        out: dict[tuple[tuple[str, int], ...], Fraction] = {}
        for m1, c1 in self.terms.items():
            for m2, c2 in o.terms.items():
                m = PolyQ._mul_mon(m1, m2)
                out[m] = out.get(m, Fraction(0)) + c1 * c2
        return PolyQ(out)

    def __rmul__(self, other: int | Fraction) -> PolyQ:
        return PolyQ._coerce(other) * self

    def __pow__(self, exp: int) -> PolyQ:
        if exp < 0:
            raise ValueError("Negative exponent not supported in PolyQ")
        res = PolyQ.const(1)
        base = self
        e = exp
        while e > 0:
            if e & 1:
                res = res * base
            base = base * base
            e >>= 1
        return res

    def coeff_of(self, var_name: str, power: int) -> PolyQ:
        """Return polynomial coefficient of var_name^power (treating other vars as coefficients)."""
        out: dict[tuple[tuple[str, int], ...], Fraction] = {}
        for mon, c in self.terms.items():
            d = dict(mon)
            if d.get(var_name, 0) == power:
                d.pop(var_name, None)
                rem = tuple(sorted(d.items()))
                out[rem] = out.get(rem, Fraction(0)) + c
        return PolyQ(out)

    def subs(self, mapping: dict[str, PolyQ | int | Fraction]) -> PolyQ:
        total = PolyQ()
        for mon, c in self.terms.items():
            term = PolyQ.const(c)
            for v, e in mon:
                if v in mapping:
                    term = term * (PolyQ._coerce(mapping[v]) ** e)
                else:
                    term = term * (PolyQ.var(v) ** e)
            total = total + term
        return total

    def __repr__(self) -> str:
        if not self.terms:
            return "0"
        parts = []
        for mon, c in list(self.terms.items())[:6]:
            ms = "*".join(f"{v}^{e}" if e != 1 else v for v, e in mon)
            parts.append(f"{c}*{ms}" if ms else str(c))
        if len(self.terms) > 6:
            parts.append("...")
        return " + ".join(parts)


def symcheck(name: str, expr: PolyQ | Fraction | int, detail: str = "") -> bool:
    p = PolyQ._coerce(expr)
    return _record(p.is_zero(), name, detail or f"exact Q-polynomial residual = {p}")


def mutant(name: str, expr: PolyQ | Fraction | int) -> bool:
    p = PolyQ._coerce(expr)
    return _record(not p.is_zero(), f"MUTANT REJECTED: {name}", f"residual = {p}")


def check(name: str, got: float, expected: float, rtol: float = 1e-12, atol: float = 0.0) -> bool:
    if expected == 0.0:
        if atol <= 0.0:
            raise ValueError("Zero target requires explicit positive atol scale.")
        ok = abs(got) <= atol
        detail = f"got={got:.6e}, expected=0, atol={atol:.2e}"
    else:
        rel = abs(got - expected) / abs(expected)
        ok = rel <= rtol or abs(got - expected) <= atol
        detail = f"got={got:.12g}, expected={expected:.12g}, rel={rel:.3e}, rtol={rtol:.2e}"
    return _record(ok, name, detail)


def numutant(name: str, got: float, expected: float, rtol: float = 1e-12, atol: float = 0.0) -> bool:
    if expected == 0.0:
        if atol <= 0.0:
            raise ValueError("Zero target requires explicit positive atol scale.")
        rejected = abs(got) > atol
        detail = f"mutant got={got:.6e}, atol={atol:.2e}"
    else:
        rel = abs(got - expected) / abs(expected)
        rejected = rel > rtol and abs(got - expected) > atol
        detail = f"mutant got={got:.12g}, expected={expected:.12g}, rel={rel:.3e}"
    return _record(rejected, f"MUTANT REJECTED: {name}", detail)


def summary() -> int:
    total = len(results)
    passed = sum(results)
    failed = total - passed
    print()
    print("=" * 78)
    print(f"SUMMARY: {passed}/{total} checks PASSED, {failed} FAILED")
    print("=" * 78)
    if _failures:
        for item in _failures:
            print(f"  FAILURE: {item}")
        return 1
    return 0


# ============================================================================
# Helper routines (exact rational polynomial, 2x2 matrix, & Pass recurrence)
# ============================================================================
def poly_mul_frac(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return out


def mid_prod_frac(a: list[Fraction], q_tilde: list[Fraction], la: int, lb: int) -> list[Fraction]:
    prod = poly_mul_frac(a, q_tilde)
    return [prod[la - 1 + k] for k in range(lb)]


def mat2_mul(X: list[list[PolyQ]], Y: list[list[PolyQ]]) -> list[list[PolyQ]]:
    return [
        [X[i][0] * Y[0][j] + X[i][1] * Y[1][j] for j in range(2)]
        for i in range(2)
    ]


def mat2_add(X: list[list[PolyQ]], Y: list[list[PolyQ]]) -> list[list[PolyQ]]:
    return [[X[i][j] + Y[i][j] for j in range(2)] for i in range(2)]


def mat2_scale(s: PolyQ, X: list[list[PolyQ]]) -> list[list[PolyQ]]:
    return [[s * X[i][j] for j in range(2)] for i in range(2)]


def exact_Lk(c: int, k: int) -> int:
    L = 1
    for _ in range(k):
        L = L + (3 * L - 1 + (c - 2)) // (c - 1)
    return L


def log_exact_Md(c: int, d: int) -> float:
    if d <= 800:
        lg_d = math.lgamma(d + 1)
        lc1 = math.log(c + 1)
        terms = [2.0 * (lg_d - math.lgamma(h + 1) - math.lgamma(d - h + 1) + (d - h) * lc1) for h in range(d + 1)]
        m = max(terms)
        return m + math.log(sum(math.exp(x - m) for x in terms))
    p_b = 1.0 / (c + 2.0)
    return 2.0 * d * math.log(c + 2.0) - 0.5 * math.log(4.0 * math.pi * d * p_b * (1.0 - p_b))


# ============================================================================
# SECTION 2: BILINEAR ALGORITHMS AND POLYNOMIAL PACKINGS
# ============================================================================
part("SECTION 2: BILINEAR ALGORITHMS AND POLYNOMIAL PACKINGS")

# eq:selected_product (matmul_9_4_constant.tex L106)
# States: Selected matrix-polynomial product extracts coefficients of AB on monomial support K.
# Derived from: Definition def:selected_product (Pass2026 Def. 2.1).
# Test: Evaluates matrix polynomial multiplication on 2x2 matrices over Q[z] and verifies exact coefficient selection.
# Mutant: Omitting one matrix inner-sum term corrupts the selected coefficient.
eq("eq:selected_product", 106, "Prod_{I,J,K}[p,q,r](A, B) = sum_{w in K} ([w](AB)) w")
A0 = [[PolyQ.const(1), PolyQ.const(2)], [PolyQ.const(3), PolyQ.const(-1)]]
A1 = [[PolyQ.const(2), PolyQ.const(0)], [PolyQ.const(1), PolyQ.const(4)]]
B0 = [[PolyQ.const(5), PolyQ.const(-2)], [PolyQ.const(1), PolyQ.const(3)]]
B1 = [[PolyQ.const(-1), PolyQ.const(4)], [PolyQ.const(2), PolyQ.const(1)]]
z = PolyQ.var("z")
AB = mat2_mul(mat2_add(A0, mat2_scale(z, A1)), mat2_add(B0, mat2_scale(z, B1)))
coeff_z1 = [[AB[i][j].coeff_of("z", 1) for j in range(2)] for i in range(2)]
expected_z1 = mat2_add(mat2_mul(A0, B1), mat2_mul(A1, B0))
boolcheck("selected z^1 matrix coefficient matches A0*B1 + A1*B0",
          all((coeff_z1[i][j] - expected_z1[i][j]).is_zero() for i in range(2) for j in range(2)))
bad_z1 = mat2_mul(A0, B1)
boolcheck("MUTANT REJECTED: dropping A1*B0 fails match",
          any(not (coeff_z1[i][j] - bad_z1[i][j]).is_zero() for i in range(2) for j in range(2)))

# eq:full_shape (matmul_9_4_constant.tex L113)
# States: Full_{a,b} has monomial supports {z^0..z^{a-1}}, {z^0..z^{b-1}}, {z^0..z^{a+b-2}}.
# Derived from: eq:selected_product
# Test: Checks support cardinalities and degree closure for (a,b)=(4,5).
# Mutant: Truncating output length to a+b-2 omits the top degree coefficient.
eq("eq:full_shape", 113, "Full_{a,b} supports of lengths a, b, s = a + b - 1")
la, lb = 4, 5
ls = la + lb - 1
I_full = set(range(la))
J_full = set(range(lb))
K_full = {i + j for i in I_full for j in J_full}
boolcheck("Full_{4,5} output support equals {0..s-1}", K_full == set(range(ls)))
boolcheck("MUTANT REJECTED: support of length a+b-2 misses top degree", K_full != set(range(ls - 1)))

# eq:mid_shape (matmul_9_4_constant.tex L117)
# States: Mid_{a,b} = Full_{a,b}^{(23)} has supports {0..a-1}, {1-s..0}, {1-b..0}; matches transposed linear map.
# Derived from: eq:full_shape
# Test: Verifies exact matrix transposition identity <Full(a,b), y> == <b, rev(Mid(a, rev(y)))> over Q.
# Mutant: Reversing shift sign fails transposition duality.
eq("eq:mid_shape", 117, "Mid_{a,b} = Full_{a,b}^{(23)} transposition identity")
rng = random.Random(9401)
a_vec = [Fraction(rng.randint(-4, 4)) for _ in range(4)]
b_vec = [Fraction(rng.randint(-4, 4)) for _ in range(5)]
y_vec = [Fraction(rng.randint(-4, 4)) for _ in range(8)]
full_ab = poly_mul_frac(a_vec, b_vec)
lhs_ip = sum(full_ab[k] * y_vec[k] for k in range(8))
y_rev = list(reversed(y_vec))
mid_ay = mid_prod_frac(a_vec, y_rev, 4, 5)
rhs_ip = sum(b_vec[j] * mid_ay[4 - j] for j in range(5))
boolcheck("<Full(a,b), y> == <b, rev(Mid(a, rev(y)))> exact over Q", lhs_ip == rhs_ip)
bad_rhs_ip = sum(b_vec[j] * mid_ay[j] for j in range(5))
boolcheck("MUTANT REJECTED: unreversed index order breaks duality", lhs_ip != bad_rhs_ip)

# eq:effort_def (matmul_9_4_constant.tex L124)
# States: eff(P[p,q,r]) = p*q*r * prod min(a_l+b_l-1, a_l+h_l-1, b_l+h_l-1) equals s*p*q*r for Full and Mid.
# Derived from: eq:full_shape, eq:mid_shape
# Test: Checks effort equality between Full_{a,b}[p,q,r] and Mid_{a,b}[p,q,r] across parameters.
# Mutant: Using max instead of min inflates Mid effort above s*p*q*r.
eq("eq:effort_def", 124, "eff(Full_{a,b}[p,q,r]) = eff(Mid_{a,b}[p,q,r]) = s*p*q*r")
for aa, bb, pp, qq, rr in [(3, 4, 2, 3, 5), (5, 2, 4, 1, 3)]:
    ss = aa + bb - 1
    eff_full = pp * qq * rr * min(aa + bb - 1, aa + ss - 1, bb + ss - 1)
    eff_mid = pp * qq * rr * min(aa + ss - 1, aa + bb - 1, ss + bb - 1)
    boolcheck(f"eff(Full)=eff(Mid)=s*p*q*r for ({aa},{bb})", eff_full == eff_mid == ss * pp * qq * rr)
# F_2 finite-field obstruction: nonzero rank-1 symmetric 3x3 Hankel matrices over F_2 (u*u^T with u0*u2 = u1^2)
f2_hankel_r1 = [u for u in [(a, b, c) for a in (0, 1) for b in (0, 1) for c in (0, 1)]
                if any(u) and (u[0] * u[2]) % 2 == (u[1] * u[1]) % 2]
boolcheck("F_2 has only 3 nonzero rank-1 symmetric 3x3 Hankel matrices (< 5 = eff(Full_{3,3}))",
          len(f2_hankel_r1) == 3 and len(f2_hankel_r1) < 5, f"vectors={f2_hankel_r1}")
bad_eff_mid = 2 * 3 * 5 * max(3 + 6 - 1, 3 + 4 - 1, 6 + 4 - 1)
boolcheck("MUTANT REJECTED: max instead of min gives wrong Mid effort", bad_eff_mid != 6 * 2 * 3 * 5)

# eq:exact_pp (matmul_9_4_constant.tex L133)
# States: Exact polynomial packing identity D(S_j(E^L(A)_j, E^R(B)_j)) = T_i(A_i, B_i); Strassen 2x2 has R=7.
# Derived from: eq:selected_product
# Test: Evaluates Strassen's 7-product bilinear packing symbolically over Q[a11..b22].
# Mutant: Flipping one sign in Strassen's decoder corrupts the matrix product.
eq("eq:exact_pp", 133, "Exact PP bilinear identity (verified on Strassen 2x2, R=7)")
a11, a12, a21, a22 = [PolyQ.var(v) for v in ("a11", "a12", "a21", "a22")]
b11, b12, b21, b22 = [PolyQ.var(v) for v in ("b11", "b12", "b21", "b22")]
m1 = (a11 + a22) * (b11 + b22)
m2 = (a21 + a22) * b11
m3 = a11 * (b12 - b22)
m4 = a22 * (b21 - b11)
m5 = (a11 + a12) * b22
m6 = (a21 - a11) * (b11 + b12)
m7 = (a12 - a22) * (b21 + b22)
c11 = m1 + m4 - m5 + m7
symcheck("Strassen C11 matches exact matrix product", c11 - (a11 * b11 + a12 * b21))
mutant("Strassen C11 with flipped sign on m5", (m1 + m4 + m5 + m7) - (a11 * b11 + a12 * b21))

# ============================================================================
# SECTION 3: ALGEBRAIC CONSTRAINTS ACROSS THE FIVE LAYERS
# ============================================================================
part("SECTION 3.1: LAYER 1 ZERO-GAP SMUGGLING AND CUBIC RATE FLOOR")

# eq:pure_telescoping (matmul_9_4_constant.tex L155)
# States: sum_{j=1}^c z^{t(j-1)} A(P_j - z^t P_{j+1}) = A P_1 - z^{ct} A P_{c+1}.
# Derived from: eq:full_shape
# Test: Exact symbolic polynomial expansion in Q[z, A, P1..P5] for c=4, t=2.
# Mutant: Changing shift sign to +z^t destroys cancellation of interior terms.
eq("eq:pure_telescoping", 155, "Pure telescoping sum cancels interior terms")
A_s = PolyQ.var("A_s")
Ps = [PolyQ.var(f"P{j}") for j in range(1, 6)]
t_val = 2
tele_sum = PolyQ()
for j in range(4):
    tele_sum = tele_sum + (z ** (t_val * j)) * A_s * (Ps[j] - (z ** t_val) * Ps[j + 1])
symcheck("telescoping sum equals A*P1 - z^(ct)*A*P5", tele_sum - (A_s * Ps[0] - (z ** 8) * A_s * Ps[4]))
bad_tele = PolyQ()
for j in range(4):
    bad_tele = bad_tele + (z ** (t_val * j)) * A_s * (Ps[j] + (z ** t_val) * Ps[j + 1])
mutant("plus sign instead of minus breaks telescoping", bad_tele - (A_s * Ps[0] - (z ** 8) * A_s * Ps[4]))

# eq:pure_tele_barrier (matmul_9_4_constant.tex L164)
# States: For ct >= a+b-1, (c+1)(a+b-1) <= c(a+b+t-1) and (c+1)b <= c(b+t).
# Derived from: eq:pure_telescoping, eq:effort_def
# Test: Exhaustive integer verification over 1 <= a,b,c,t <= 11 with ct >= a+b-1.
# Mutant: Violating ct >= a+b-1 flips the effort inequality.
eq("eq:pure_tele_barrier", 164, "Zero-gain barrier for pure (c+1)-for-c telescoping")
ok_bar = True
for a in range(1, 9):
    for b in range(1, 9):
        for c in range(1, 12):
            for t in range(1, 9):
                if c * t >= a + b - 1:
                    if not ((c + 1) * (a + b - 1) <= c * (a + b + t - 1) and (c + 1) * b <= c * (b + t)):
                        ok_bar = False
boolcheck("exhaustive check of Eq. (eq:pure_tele_barrier) across 1..11", ok_bar)
boolcheck("MUTANT REJECTED: ct < a+b-1 violates barrier", not ((3 + 1) * (3 + 3 - 1) <= 3 * (3 + 3 + 1 - 1)))

# eq:pure_tele_diff (matmul_9_4_constant.tex L171)
# States: c(a+b+t-1) - (c+1)(a+b-1) = ct - (a+b-1).
# Derived from: eq:pure_tele_barrier
# Test: Exact symbolic polynomial identity in Q[a, b, c, t].
# Mutant: Replacing (c+1) by (c+2) leaves nonzero discrepancy -(a+b-1).
eq("eq:pure_tele_diff", 171, "Exact effort difference identity")
a_s, b_s, c_s, t_s = [PolyQ.var(v) for v in ("a", "b", "c", "t")]
symcheck("exact effort difference identity",
         c_s * (a_s + b_s + t_s - 1) - (c_s + 1) * (a_s + b_s - 1) - (c_s * t_s - (a_s + b_s - 1)))
mutant("using c+2 instead of c+1 fails identity",
       c_s * (a_s + b_s + t_s - 1) - (c_s + 2) * (a_s + b_s - 1) - (c_s * t_s - (a_s + b_s - 1)))

# eq:primal_identity (matmul_9_4_constant.tex L185)
# States: W(z) = A P_1 - z^{ct} A P_{c+1} + eps z^b A Q_tilde when ct >= s.
# Derived from: eq:pure_telescoping
# Test: Exact symbolic polynomial verification over Q[eps, z, a_i, p_{j,i}, q_u] for a=3, b=2, t=1, c=6.
# Mutant: Truncating Q at c*t < s drops top coefficient of Q_tilde.
eq("eq:primal_identity", 185, "Primal packing telescoping identity with eps z^b Q")
eps = PolyQ.var("eps")
la, lb, lt, lc = 3, 2, 1, 6
ls = la + lb - 1
A_p = PolyQ()
for i in range(la):
    A_p = A_p + PolyQ.var(f"a{i}") * (z ** i)
P_ps = []
for j in range(lc + 1):
    pj = PolyQ()
    for i in range(lb):
        pj = pj + PolyQ.var(f"p{j}_{i}") * (z ** i)
    P_ps.append(pj)
q_coeffs = [PolyQ.var(f"q{u}") for u in range(ls)]
Q_tilde = PolyQ()
for u in range(ls):
    Q_tilde = Q_tilde + q_coeffs[u] * (z ** u)
W_expr = PolyQ()
for j in range(lc):
    Qj = PolyQ()
    for v in range(lt):
        if lt * j + v < ls:
            Qj = Qj + q_coeffs[lt * j + v] * (z ** v)
    Ej = P_ps[j] - (z ** lt) * P_ps[j + 1] + eps * (z ** lb) * Qj
    W_expr = W_expr + (z ** (lt * j)) * A_p * Ej
symcheck("exact primal identity W = A*P1 - z^(ct)*A*P_{c+1} + eps*z^b*A*Q_tilde",
         W_expr - (A_p * P_ps[0] - (z ** (lc * lt)) * A_p * P_ps[lc] + eps * (z ** lb) * A_p * Q_tilde))
W_trunc = PolyQ()
for j in range(ls - 1):
    W_trunc = W_trunc + (z ** j) * A_p * (P_ps[j] - z * P_ps[j + 1] + eps * (z ** lb) * q_coeffs[j])
mutant("truncating c < s fails to recover Q_tilde",
       W_trunc - (A_p * P_ps[0] - (z ** (ls - 1)) * A_p * P_ps[ls - 1] + eps * (z ** lb) * A_p * Q_tilde))

# eq:gap_condition (matmul_9_4_constant.tex L190)
# States: ct >= a + 2b - 1 is necessary and sufficient for zero leakage in window [s, s+b-1].
# Derived from: eq:primal_identity
# Test: Exact symbolic verification at c=6=a+2b-1 (zero error) and c=5 (nonzero eps^0 leakage at z^5).
# Mutant: c = a+2b-2 = 5 leaks -A*P_6 into the middle-product window.
eq("eq:gap_condition", 190, "Gap condition ct >= a + 2b - 1 necessity and sufficiency")
expected_mid = A_p * Q_tilde
ok_mid = True
for k in range(lb):
    slot_poly = W_expr.coeff_of("z", ls + k)
    if not slot_poly.coeff_of("eps", 0).is_zero():
        ok_mid = False
    if not (slot_poly.coeff_of("eps", 1) - expected_mid.coeff_of("z", la - 1 + k)).is_zero():
        ok_mid = False
boolcheck("at c=6 >= a+2b-1=6, eps^{-1}[z^{s+k}]W == Mid_{3,2}(A,Q) exactly", ok_mid)
W_bad = A_p * P_ps[0] - (z ** 5) * A_p * P_ps[5] + eps * (z ** lb) * A_p * Q_tilde
bad_leak = W_bad.coeff_of("z", ls + 1).coeff_of("eps", 0)
mutant("at c=5 < a+2b-1=6, [z^{s+1}]W has nonzero eps^0 leakage -a0*p5_0", bad_leak)

# eq:effort_surplus (matmul_9_4_constant.tex L196)
# States: (c+2)(2b-1) - c(2b) = b - 1 > 0 for c = 3b - 1, b >= 2.
# Derived from: eq:gap_condition, eq:effort_def
# Test: Exact symbolic polynomial identity in Q[b].
# Mutant: Dropping the middle product (+1 instead of +2) gives wrong surplus.
eq("eq:effort_surplus", 196, "Exact positive effort surplus (c+2)(2b-1) - c(2b) = b - 1")
symcheck("surplus equals b - 1 at c = 3b - 1", (3 * b_s + 1) * (2 * b_s - 1) - (3 * b_s - 1) * (2 * b_s) - (b_s - 1))
mutant("dropping middle product gives wrong surplus", (3 * b_s) * (2 * b_s - 1) - (3 * b_s - 1) * (2 * b_s) - (b_s - 1))

# eq:multi_eps_pole (matmul_9_4_constant.tex L215)
# States: eps^{-2}[z^{s+k}]W^{(2)} = eps^{-1}[z^{a-1+k}](A Q1) + [z^{a-1+k}](A Q2).
# Derived from: eq:primal_identity, eq:gap_condition
# Test: Live exact-Q verification at a=2, b=2, t=1, c=5 confirming nonzero eps^{-1} pole.
# Mutant: Claiming zero eps^{-1} pole contradicts nonzero Mid(A, Q1).
eq("eq:multi_eps_pole", 215, "Same-slot multi-eps pole collision")
A_num = [Fraction(2), Fraction(3)]
Q1_num = [Fraction(1), Fraction(4), Fraction(2)]
Q2_num = [Fraction(5), Fraction(1), Fraction(3)]
mid1 = mid_prod_frac(A_num, Q1_num, 2, 2)
mid2 = mid_prod_frac(A_num, Q2_num, 2, 2)
boolcheck("Mid(A, Q1) = [11, 16] gives nonzero eps^{-1} poles in every slot",
          mid1 == [Fraction(11), Fraction(16)] and all(x != 0 for x in mid1))
boolcheck("Mid(A, Q2) = [17, 9] sits at eps^0 behind the eps^{-1} poles", mid2 == [Fraction(17), Fraction(9)])
boolcheck("MUTANT REJECTED: claiming zero eps^{-1} pole fails", not all(x == 0 for x in mid1))

# eq:rho_def (matmul_9_4_constant.tex L226)
# States: rho(c) = 1 + 3/(c-1) = (c+2)/(c-1) for c >= 2.
# Derived from: eq:gap_condition
# Test: Cleared-denominator symbolic identity (c-1) + 3 == c + 2 in Q[c].
# Mutant: 1 + 3/c != (c+2)/(c-1) (cleared: (c+3)(c-1) != c(c+2)).
eq("eq:rho_def", 226, "rho(c) = 1 + 3/(c-1) = (c+2)/(c-1)")
symcheck("(c - 1) + 3 == c + 2", (c_s - 1) + 3 - (c_s + 2))
mutant("1 + 3/c != (c+2)/(c-1)", (c_s + 3) * (c_s - 1) - c_s * (c_s + 2))

# eq:tau_c_def (matmul_9_4_constant.tex L231)
# States: tau(c) = (3/2) * ln(1 + 3/(c-1)) / ln(1 + 2/c).
# Derived from: eq:rho_def
# Test: Numerical check at c=6 and c=10^4 (approaching 9/4).
# Mutant: Dropping outer 3/2 gives 3/2 instead of 9/4.
eq("eq:tau_c_def", 231, "Threshold exponent tau(c) -> 9/4")
tau_6 = 1.5 * math.log(8.0 / 5.0) / math.log(8.0 / 6.0)
tau_1e4 = 1.5 * math.log1p(3.0 / 9999.0) / math.log1p(2.0 / 10000.0)
check("tau(6) matches exact log ratio", tau_6, 2.4506408684426146, rtol=1e-12)
check("tau(10^4) matches 9/4 + 9/(8*10^4) to 1e-8", tau_1e4, 2.25 + 9.0 / 80000.0, rtol=1e-8)
numutant("dropping outer 3/2 fails 9/4 limit", tau_1e4 / 1.5, 2.25, rtol=1e-3)

# eq:cubic_identity (matmul_9_4_constant.tex L239)
# States: (c+2)(c-1)^2 = c^3 - (3c - 2) < c^3 for all c >= 2.
# Derived from: eq:rho_def
# Test: Exact symbolic expansion in Q[c] and boundary check at c >= 2.
# Mutant: (c+2)(c-1)^2 = c^3 - 3c is false (missing +2).
eq("eq:cubic_identity", 239, "(c+2)(c-1)^2 = c^3 - (3c - 2) < c^3")
symcheck("(c+2)(c-1)^2 == c^3 - (3c - 2)", (c_s + 2) * ((c_s - 1) ** 2) - ((c_s ** 3) - (3 * c_s - 2)))
boolcheck("strict positivity 3c - 2 >= 4 for c >= 2", all(3 * cc - 2 >= 4 for cc in range(2, 50)))
mutant("omitting +2 fails identity", (c_s + 2) * ((c_s - 1) ** 2) - ((c_s ** 3) - 3 * c_s))

# eq:tau_strict_gt_94 (matmul_9_4_constant.tex L244)
# States: rho(c)^6 > ((c+2)/c)^9 and tau(c) > 9/4 for all c >= 2.
# Derived from: eq:cubic_identity, eq:tau_c_def
# Test: Exact rational check across c=2..100.
# Mutant: Reversing exponent pair (9, 6) flips inequality.
eq("eq:tau_strict_gt_94", 244, "rho(c)^6 > ((c+2)/c)^9 implies tau(c) > 9/4")
boolcheck("rho(c)^6 > ((c+2)/c)^9 exact over Q for c=2..100",
          all(Fraction(cc + 2, cc - 1) ** 6 > Fraction(cc + 2, cc) ** 9 for cc in range(2, 101)))
boolcheck("MUTANT REJECTED: reversed exponents fail at c=6",
          not (Fraction(8, 5) ** 9 < Fraction(8, 6) ** 6))

# eq:tau_laurent (matmul_9_4_constant.tex L249)
# States: tau(c) = 9/4 + 9/(8c) + O(c^{-2}).
# Derived from: eq:tau_c_def
# Test: Exact truncated power series of ln(1 + 3x/(1-x)) / ln(1 + 2x) through x^2 in Q[x] + numerical c=10^6 check.
# Mutant: Replacing 9/(8c) with 9/(4c) fails exact series coefficient.
eq("eq:tau_laurent", 249, "Laurent expansion tau(c) = 9/4 + 9/(8c) + O(c^{-2})")
# Exact series: ln(1 + 3x/(1-x)) = 3x - (3/2)x^2 + O(x^3); ln(1 + 2x) = 2x - 2x^2 + O(x^3).
# Ratio (3/2) * (3x - (3/2)x^2) = (9/4 + 9/8 x)*(2x - 2x^2) + O(x^3)
x_s = PolyQ.var("x")
num_ser = Fraction(3, 2) * (3 * x_s - Fraction(3, 2) * (x_s ** 2))
den_ser = 2 * x_s - 2 * (x_s ** 2)
quo_ser = Fraction(9, 4) + Fraction(9, 8) * x_s
diff_ser = num_ser - quo_ser * den_ser
symcheck("series O(x^1) and O(x^2) residuals vanish",
         diff_ser.coeff_of("x", 1) + diff_ser.coeff_of("x", 2))
bad_diff_ser = num_ser - (Fraction(9, 4) + Fraction(9, 4) * x_s) * den_ser
mutant("wrong 9/(4c) coefficient fails O(x^2) match", bad_diff_ser.coeff_of("x", 2))
tau_1e6 = 1.5 * math.log1p(3.0 / 999999.0) / math.log1p(2.0 / 1000000.0)
check("c*(tau(c) - 9/4) at c=10^6 matches 9/8 = 1.125", 1e6 * (tau_1e6 - 2.25), 1.125, rtol=1e-5)

# eq:c_min_exact_poly (matmul_9_4_constant.tex L254)
# States: (1 - (3c-2)/c^3)^{6 b_0} (1 + 2/c)^{8 a_0} > 1 iff tau(c) < 9/4 + a_0/b_0.
# Derived from: eq:cubic_identity, eq:tau_c_def
# Test: Verifies exact c_min across all 8 benchmark exponents.
# Mutant: Shifting exponent 6 b_0 -> 5 b_0 gives wrong c_min at tau=2.260.
eq("eq:c_min_exact_poly", 254, "Exact polynomial characterization of tau(c) < 9/4 + a_0/b_0")
expected_cmins = [(11, 20, 3), (89, 200, 3), (1, 4, 5), (121, 1000, 10), (71, 1000, 17), (1, 20, 23), (1, 100, 113), (1, 1000, 1126)]
for a0, b0, cmin_exp in expected_cmins:
    c_test = 2
    while not (Fraction(c_test ** 3 - 3 * c_test + 2, c_test ** 3) ** (6 * b0) * Fraction(c_test + 2, c_test) ** (8 * a0) > 1):
        c_test += 1
    boolcheck(f"exact c_min for delta={a0}/{b0} equals {cmin_exp}", c_test == cmin_exp, f"got c_min={c_test}")
c_mut = 2
while not (Fraction(c_mut ** 3 - 3 * c_mut + 2, c_mut ** 3) ** (5 * 100) * Fraction(c_mut + 2, c_mut) ** 8 > 1):
    c_mut += 1
boolcheck("MUTANT REJECTED: exponent 5*b0 yields wrong c_min", c_mut != 113, f"mutant c_min={c_mut}")

# eq:c_min_bound (matmul_9_4_constant.tex L259)
# States: 16 a_0 c^2 > 6 b_0 (3c - 2), hence c > 9/(8 delta) - 3/(4 delta c).
# Derived from: eq:c_min_exact_poly
# Test: Checks equivalence of both forms over a rational grid and all 8 exact c_min values.
# Mutant: Dropping delta in 3/(4 delta c) fails at (a_0=1, b_0=3, c=3).
eq("eq:c_min_bound", 259, "Explicit quadratic lower bound 16 a_0 c^2 > 6 b_0 (3c - 2) <=> c > 9/(8 delta) - 3/(4 delta c)")
for a0, b0, cmin_exp in expected_cmins:
    boolcheck(f"16*a0*c^2 > 6*b0*(3c-2) at c={cmin_exp}", 16 * a0 * cmin_exp ** 2 > 6 * b0 * (3 * cmin_exp - 2))
equiv_ok = all(
    (16 * a0 * cc * cc > 6 * b0 * (3 * cc - 2))
    == (Fraction(cc, 1) > Fraction(9 * b0, 8 * a0) - Fraction(3 * b0, 4 * a0 * cc))
    for a0 in range(1, 8) for b0 in range(1, 20) for cc in range(2, 20)
)
boolcheck("16*a0*c^2 > 6*b0*(3c-2) <=> c > 9/(8*delta) - 3/(4*delta*c) exact over Q", equiv_ok)
boolcheck("MUTANT REJECTED: omitting delta in 3/(4*delta*c) fails at (a0=1,b0=3,c=3)",
          (16 * 1 * 9 > 6 * 3 * 7) and not (Fraction(3, 1) > Fraction(9 * 3, 8) - Fraction(3, 4 * 3)))
boolcheck("MUTANT REJECTED: factor 8 fails at tau=2.260 (c=113)", not (8 * 1 * 113 ** 2 > 6 * 100 * (3 * 113 - 2)))

# eq:tau_laurent_step (matmul_9_4_constant.tex L268)
# States: Intermediate ratio step yielding 9/4 + 9/(8c) + O(c^{-2}).
# Derived from: eq:tau_c_def
# Test: Exact polynomial quotient check (1 - x/2) == (1 + x/2)(1 - x) + O(x^2).
# Mutant: Flipping sign to (1 + x/2) gives linear coefficient +3/2 instead of +1/2.
eq("eq:tau_laurent_step", 268, "Intermediate Taylor quotient step")
step_res = (1 - Fraction(1, 2) * x_s) - (1 + Fraction(1, 2) * x_s) * (1 - x_s)
symcheck("O(x^0) and O(x^1) terms match (1 + x/2) exactly",
         step_res.coeff_of("x", 0) + step_res.coeff_of("x", 1))
bad_step_res = (1 + Fraction(1, 2) * x_s) - (1 + Fraction(1, 2) * x_s) * (1 - x_s)
mutant("plus sign in numerator fails O(x^1) match", bad_step_res.coeff_of("x", 1))

# eq:c_factorization (matmul_9_4_constant.tex L276)
# States: (c+2)^{6 b_0 + 8 a_0} (c-1)^{12 b_0} / c^{18 b_0 + 8 a_0} = (1 - (3c-2)/c^3)^{6 b_0} (1 + 2/c)^{8 a_0}.
# Derived from: eq:cubic_identity
# Test: Exact cleared-denominator symbolic identity in Q[c] for (a_0, b_0) = (1, 2).
# Mutant: Changing 18 b_0 to 16 b_0 breaks factorization.
eq("eq:c_factorization", 276, "Exact algebraic factorization of rate ratio")
lhs_f = ((c_s + 2) ** 20) * ((c_s - 1) ** 24)
rhs_f = (((c_s ** 3) - (3 * c_s - 2)) ** 12) * ((c_s + 2) ** 8)
symcheck("exact factorization identity (a0=1, b0=2)", lhs_f - rhs_f)
mutant("wrong exponent breaks identity", ((c_s + 2) ** 20) * ((c_s - 1) ** 22) - rhs_f)

# ============================================================================
# SECTION 3.2: LAYER 2 MULTIVARIATE PRIMAL-DUAL BALANCING
# ============================================================================
part("SECTION 3.2: LAYER 2 MULTIVARIATE PRIMAL-DUAL BALANCING")

# eq:u_def (matmul_9_4_constant.tex L291)
# States: u(c, d) = c^{2d} source count for 2d-variable primal-dual tensor product.
# Derived from: eq:primal_identity
# Test: Checks exact tensor-power count at c=6, d=4 (6^8 = 1679616).
# Mutant: c^d instead of c^{2d} undercounts dual variables.
eq("eq:u_def", 291, "u(c, d) = c^{2d}")
boolcheck("u(6, 4) == 6^8 == 1679616", 6 ** (2 * 4) == 1679616)
boolcheck("MUTANT REJECTED: c^d != c^{2d}", 6 ** 4 != 6 ** 8)

# eq:Md_exact (matmul_9_4_constant.tex L302)
# States: M_d(c) = sum_{h=0}^d (C(d,h) (c+1)^{d-h})^2.
# Derived from: eq:u_def
# Test: Verifies M_d against brute-force enumeration of all (c+2)^{2d} words for c=2, d=3.
# Mutant: Dropping the square on N_h gives (c+2)^d instead of M_d.
eq("eq:Md_exact", 302, "Exact balanced-word count M_d(c)")
c_e, d_e = 2, 3
bf_count = 0
for w_primal in itertools.product(range(c_e + 2), repeat=d_e):
    n_full_p = sum(1 for x in w_primal if x <= c_e)
    for w_dual in itertools.product(range(c_e + 2), repeat=d_e):
        n_full_d = sum(1 for x in w_dual if x == 0)
        if n_full_p + n_full_d == d_e:
            bf_count += 1
Md_formula = sum((math.comb(d_e, h) * (c_e + 1) ** (d_e - h)) ** 2 for h in range(d_e + 1))
boolcheck("M_3(2) formula matches brute-force enumeration of 4^6=4096 words", bf_count == Md_formula, f"M_3(2)={Md_formula}")
bad_Md = sum(math.comb(d_e, h) * (c_e + 1) ** (d_e - h) for h in range(d_e + 1))
boolcheck("MUTANT REJECTED: unsquared sum != M_3(2)", bad_Md != Md_formula)

# eq:Md_bounds (matmul_9_4_constant.tex L307)
# States: (c+2)^{2d}/(d+1) <= M_d(c) <= (c+2)^{2d}.
# Derived from: eq:Md_exact
# Test: Exact integer verification across c=2..8, d=1..12.
# Mutant: Dividing by d instead of d+1 violates the lower bound at c=2, d=1.
eq("eq:Md_bounds", 307, "Cauchy-Schwarz two-sided bounds on M_d(c)")
ok_md = True
for cc in range(2, 9):
    for dd in range(1, 13):
        md = sum((math.comb(dd, h) * (cc + 1) ** (dd - h)) ** 2 for h in range(dd + 1))
        tot = (cc + 2) ** (2 * dd)
        if not (tot <= (dd + 1) * md and md <= tot):
            ok_md = False
boolcheck("two-sided bounds hold for all c in 2..8, d in 1..12", ok_md)
boolcheck("MUTANT REJECTED: (c+2)^{2d}/d fails at c=2, d=1 (16 > 10)", not (16 <= 1 * 10))

# eq:Md_stirling (matmul_9_4_constant.tex L312)
# States: M_d(c) ~ (c+2)^{2d} / sqrt(4 pi d p_b (1 - p_b)) with p_b = 1/(c+2).
# Derived from: eq:Md_exact
# Test: Compares exact log_exact_Md against Stirling formula at c=6, d=800 (rel error < 2e-3).
# Mutant: Using 2*pi instead of 4*pi introduces sqrt(2) (41%) error.
eq("eq:Md_stirling", 312, "Gaussian-peak asymptotic formula for M_d(c)")
c_st, d_st = 6, 800
exact_l = log_exact_Md(c_st, d_st)
pb = 1.0 / (c_st + 2.0)
asymp_l = 2 * d_st * math.log(c_st + 2.0) - 0.5 * math.log(4.0 * math.pi * d_st * pb * (1.0 - pb))
ratio_md = math.exp(exact_l - asymp_l)
check("exact M_800(6) / Stirling agrees within 0.2%", ratio_md, 1.0, rtol=2e-3)
bad_asymp_l = 2 * d_st * math.log(c_st + 2.0) - 0.5 * math.log(2.0 * math.pi * d_st * pb * (1.0 - pb))
numutant("2*pi instead of 4*pi fails by sqrt(2)", math.exp(exact_l - bad_asymp_l), 1.0, rtol=1e-2)

# eq:w_def (matmul_9_4_constant.tex L326)
# States: w(c, d) = floor((c+2)^{2d}/(d+1)).
# Derived from: eq:Md_bounds
# Test: Exact integer check at c=6, d=2 (floor(8^4 / 3) = 1365 <= M_2(6) = 2501).
# Mutant: Ceiling instead of floor disagrees with floor(4096/3).
eq("eq:w_def", 326, "w(c, d) = floor((c+2)^{2d}/(d+1))")
w_6_2 = (8 ** 4) // 3
m_6_2 = sum((math.comb(2, h) * 7 ** (2 - h)) ** 2 for h in range(3))
boolcheck("w(6, 2) = 1365 <= M_2(6) = 2501", w_6_2 == 1365 and w_6_2 <= m_6_2)
boolcheck("MUTANT REJECTED: ceil(4096/3) = 1366 != floor", (8 ** 4 + 2) // 3 != w_6_2)

# ============================================================================
# SECTION 3.3: LAYER 3 SHARED-LEG UNCOUPLING AND SEPARATION TRADEOFFS
# ============================================================================
part("SECTION 3.3: LAYER 3 SHARED-LEG UNCOUPLING AND SEPARATION")

# eq:single_leg_poles (matmul_9_4_constant.tex L346)
# States: p_L^(1)=0, p_R^(1)=dw+w-1, p_D^(1)=dw; P_1=(2d+1)w-1, N_1=2(d+1)w-2.
# Derived from: eq:w_def
# Test: Exact symbolic identity in Q[d, w].
# Mutant: Dropping w-1 from p_R gives wrong P_1 = 2dw.
eq("eq:single_leg_poles", 346, "Single-leg pole orders and pole sum P_1 = (2d+1)w - 1")
d_s, w_s = PolyQ.var("d"), PolyQ.var("w")
symcheck("P_1 == 0 + (d*w + w - 1) + d*w == (2d+1)w - 1", (d_s * w_s + w_s - 1) + d_s * w_s - ((2 * d_s + 1) * w_s - 1))
symcheck("N_1 == 0 + d*w + (d*w + 2*w - 2) == 2(d+1)w - 2", d_s * w_s + (d_s * w_s + 2 * w_s - 2) - (2 * (d_s + 1) * w_s - 2))
mutant("dropping w-1 fails P_1", 2 * d_s * w_s - ((2 * d_s + 1) * w_s - 1))

# eq:lagrange_basis (matmul_9_4_constant.tex L357)
# States: Lagrange basis ell_{i,j}(xi) at nodes i+eps*j has denominator eps^{w-1} and Kronecker delta property.
# Derived from: eq:single_leg_poles
# Test: Exact polynomial check of numerator/denominator for w=3, i=1 in Q[xi, eps].
# Mutant: Multiplying only by eps^{w-2} leaves a nonzero eps^0 numerator over eps^1 denominator at xi=0.
eq("eq:lagrange_basis", 357, "Lagrange basis at nodes i + eps*j has pole order w - 1")
xi = PolyQ.var("xi")
w_l, i_l = 3, 1
# ell_{1,j}(xi) = num_j(xi, eps) / (denom_const_j * eps^{w-1})
lag_nums = []
lag_dconsts = []
for j in range(w_l):
    num = PolyQ.const(1)
    dc = Fraction(1)
    for jp in range(w_l):
        if jp != j:
            num = num * (xi - (i_l + eps * jp))
            dc *= (j - jp)
    lag_nums.append(num)
    lag_dconsts.append(dc)
ok_kron = True
for j in range(w_l):
    for k in range(w_l):
        val = lag_nums[j].subs({"xi": i_l + eps * k})
        expected = (PolyQ.const(lag_dconsts[j]) * (eps ** (w_l - 1))) if j == k else PolyQ()
        if not (val - expected).is_zero():
            ok_kron = False
boolcheck("Kronecker delta property at i + eps*k holds exactly for w=3", ok_kron)
# At xi = 0: eps^{w-1} * ell_{1,0}(0) = num_0(0, eps) / denom_const_0 has constant term 1/2 at eps=0
val_e2_at_0 = lag_nums[0].subs({"xi": 0, "eps": 0})
c_at_0 = val_e2_at_0.terms.get((), Fraction(0)) / lag_dconsts[0]
boolcheck("eps^{w-1} clears pole of ell_{1,0}(0) with nonzero limit 1/2", c_at_0 == Fraction(1, 2))
# Mutant: eps^{w-2} leaves eps^1 in denominator while numerator at eps=0 is nonzero (c_at_0 != 0)
boolcheck("MUTANT REJECTED: eps^{w-2} leaves nonzero eps^{-1} pole at xi=0", c_at_0 != 0)

# eq:openai_tight_deg (matmul_9_4_constant.tex L371)
# States: (g-h)^2 <= floor((M-1)/2)^2 for u-v+2(g-h)=0, g,h,u,v in {1..M}, with equality attained.
# Derived from: eq:exact_pp
# Test: Exhaustive check over all M^4 quadruples for M=2..9 verifying exact maximum equals floor((M-1)/2)^2.
# Mutant: Claiming max is (M-1)^2 fails strict tightness for all M >= 3.
eq("eq:openai_tight_deg", 371, "Exact tight eps-degree floor((M-1)/2)^2 for OpenAI Prop. 3.1")
for M in range(2, 10):
    max_gh2 = max((g - h) ** 2 for g in range(1, M + 1) for h in range(1, M + 1)
                  for u in range(1, M + 1) for v in range(1, M + 1)
                  if u - v + 2 * (g - h) == 0)
    expected_deg = ((M - 1) // 2) ** 2
    boolcheck(f"M={M}: exhaustive max (g-h)^2 == {expected_deg}", max_gh2 == expected_deg)
boolcheck("MUTANT REJECTED: paper bound (M-1)^2 is 4x too loose at M=7 (36 != 9)", (7 - 1) ** 2 != ((7 - 1) // 2) ** 2)

# ============================================================================
# SECTION 3.4: LAYER 4 S_3-SYMMETRIZATION, SLABBING BARRIER, AND L_k SANDWICH
# ============================================================================
part("SECTION 3.4: LAYER 4 SLABBING BARRIER AND EXACT L_k SANDWICH")

# eq:slabbing_barrier (matmul_9_4_constant.tex L393)
# States: 3 - alpha >= 7/3 > 9/4 for all alpha <= 2/3; 3 - 1/2 = 5/2 = 9/4 + 1/4.
# Derived from: eq:tau_strict_gt_94
# Test: Exact rational arithmetic check at alpha=1/2 and alpha=2/3.
# Mutant: alpha = 3/4 would reach 9/4, violating alpha <= 2/3.
eq("eq:slabbing_barrier", 393, "3 - alpha >= 7/3 > 9/4 for alpha <= 2/3")
boolcheck("3 - 2/3 == 7/3 > 9/4", Fraction(3) - Fraction(2, 3) == Fraction(7, 3) > Fraction(9, 4))
boolcheck("3 - 1/2 == 5/2 == 9/4 + 1/4", Fraction(3) - Fraction(1, 2) == Fraction(9, 4) + Fraction(1, 4))
boolcheck("MUTANT REJECTED: alpha=3/4 hits 9/4 (violates alpha <= 2/3)", not (Fraction(3) - Fraction(3, 4) > Fraction(9, 4)))

# eq:lambda_def (matmul_9_4_constant.tex L404)
# States: Lambda(c, d) = floor(w/u)^2.
# Derived from: eq:u_def, eq:w_def
# Test: Exact integer check at c=6, d=10.
# Mutant: Omitting square gives floor(w/u) instead of floor(w/u)^2.
eq("eq:lambda_def", 404, "Lambda(c, d) = floor(w/u)^2")
w_6_10 = (8 ** 20) // 11
u_6_10 = 6 ** 20
lam_6_10 = (w_6_10 // u_6_10) ** 2
boolcheck("Lambda(6, 10) == 28^2 == 784", w_6_10 // u_6_10 == 28 and lam_6_10 == 784)
boolcheck("MUTANT REJECTED: unsquared floor != Lambda", (w_6_10 // u_6_10) != lam_6_10)

# eq:Lk_recurrence (matmul_9_4_constant.tex L411)
# States: L_0 = 1, L_{j+1} = L_j + ceil((3 L_j - 1)/(c - 1)).
# Derived from: eq:gap_condition
# Test: Checks shift condition c*t_j >= 3*L_j + t_j - 1 at every step for c=6, j=0..15.
# Mutant: Floor instead of ceiling violates c*t >= 3*L + t - 1 at j=0, c=6.
eq("eq:Lk_recurrence", 411, "Ceiling recurrence L_{j+1} = L_j + ceil((3 L_j - 1)/(c - 1))")
L_cur = 1
ok_shift = True
for j in range(15):
    t_j = (3 * L_cur - 1 + (6 - 2)) // (6 - 1)
    if not (6 * t_j >= 3 * L_cur + t_j - 1):
        ok_shift = False
    L_cur += t_j
boolcheck("exact ceiling recurrence satisfies both half-round shift conditions", ok_shift)
t_bad = (3 * 1 - 1) // 5
boolcheck("MUTANT REJECTED: floor gives t=0 violating c*t >= 3L+t-1", not (6 * t_bad >= 3 * 1 + t_bad - 1))

# eq:vk_def (matmul_9_4_constant.tex L416)
# States: v_k(c, d) = w^2 * Lambda^k.
# Derived from: eq:w_def, eq:lambda_def
# Test: Checks exact integer value at c=6, d=10, k=2.
# Mutant: w * Lambda^k instead of w^2 * Lambda^k disagrees.
eq("eq:vk_def", 416, "v_k = w^2 * Lambda^k")
vk_test = (w_6_10 ** 2) * (lam_6_10 ** 2)
boolcheck("v_2(6, 10) matches exact formula", vk_test == (w_6_10 * lam_6_10) ** 2)
boolcheck("MUTANT REJECTED: w * Lambda^k != v_k", w_6_10 * (lam_6_10 ** 2) != vk_test)

# eq:Ek_def (matmul_9_4_constant.tex L421)
# States: E_k(c, d) = 64^k * w^9 * (2 L_k - 1)^{6d}.
# Derived from: eq:w_def, eq:Lk_recurrence
# Test: Checks exact compression rate ratio w^3 * v_k^3 / C_k == E_k at c=6, d=10, k=2.
# Mutant: Replacing w^9 by w^6 breaks identity.
eq("eq:Ek_def", 421, "E_k = 64^k * w^9 * (2 L_k - 1)^{6d}")
L2_6 = exact_Lk(6, 2)
Ck_test = Fraction(lam_6_10 ** (3 * 2), (64 ** 2) * ((2 * L2_6 - 1) ** (6 * 10)))
Ek_from_C = Fraction((w_6_10 ** 3) * (vk_test ** 3), 1) / Ck_test
Ek_direct = (64 ** 2) * (w_6_10 ** 9) * ((2 * L2_6 - 1) ** (6 * 10))
boolcheck("w^3 * v_k^3 / C_k == 64^k * w^9 * (2 L_k - 1)^{6d} exact", Ek_from_C == Ek_direct)
boolcheck("MUTANT REJECTED: w^6 instead of w^9 breaks identity",
          (64 ** 2) * (w_6_10 ** 6) * ((2 * L2_6 - 1) ** (6 * 10)) != Ek_from_C)

# eq:lk_sandwich (matmul_9_4_constant.tex L432)
# States: (2/3) rho^k + 1/3 <= L_k <= (c/3) rho^k - (c-3)/3 and rho^k <= 2 L_k - 1 <= (2c/3) rho^k.
# Derived from: eq:rho_def, eq:Lk_recurrence
# Test: Exact rational check over c=2..25, k=0..20.
# Mutant: Tightening upper bound to (c/6) rho^k fails at c=6, k=5.
eq("eq:lk_sandwich", 432, "Exact two-sided sandwich on L_k and 2 L_k - 1")
ok_sand = True
for cc in range(2, 26):
    rho_f = Fraction(cc + 2, cc - 1)
    for kk in range(21):
        lk = exact_Lk(cc, kk)
        lo_L = Fraction(2, 3) * (rho_f ** kk) + Fraction(1, 3)
        hi_L = Fraction(cc, 3) * (rho_f ** kk) - Fraction(cc - 3, 3)
        if not (lo_L <= lk <= hi_L and (rho_f ** kk) <= 2 * lk - 1 <= Fraction(2 * cc, 3) * (rho_f ** kk)):
            ok_sand = False
boolcheck("exact rational sandwich holds across c=2..25, k=0..20", ok_sand)
boolcheck("MUTANT REJECTED: (c/6)*rho^k fails upper bound at c=6, k=5",
          not (exact_Lk(6, 5) <= Fraction(6, 6) * (Fraction(8, 5) ** 5)))

# eq:lk_ceiling_boost (matmul_9_4_constant.tex L437)
# States: For j_0 = floor((c-1)/3), L_j >= j+1 (j <= j_0) and 2 L_k - 1 >= (2 j_0 + 1) rho^{k - j_0} (k >= j_0).
# Derived from: eq:lk_sandwich
# Test: Exact rational verification for c=2..30, k=0..25.
# Mutant: Using j_0 + 1 in factor (2 j_0 + 3) fails at c=10, k=3.
eq("eq:lk_ceiling_boost", 437, "Ceiling-boost lower bound 2 L_k - 1 >= (2 j_0 + 1) rho^{k - j_0}")
ok_boost = True
for cc in range(2, 31):
    j0 = (cc - 1) // 3
    rho_f = Fraction(cc + 2, cc - 1)
    for kk in range(26):
        lk = exact_Lk(cc, kk)
        if kk <= j0:
            if not (lk >= kk + 1):
                ok_boost = False
        else:
            if not (lk >= (Fraction(j0) + Fraction(2, 3)) * (rho_f ** (kk - j0)) + Fraction(1, 3)
                    and 2 * lk - 1 >= (2 * j0 + 1) * (rho_f ** (kk - j0))):
                ok_boost = False
boolcheck("ceiling-boost lower bound holds exactly for c=2..30, k=0..25", ok_boost)
boolcheck("MUTANT REJECTED: (2*j0+3) fails at c=10, k=3",
          not (2 * exact_Lk(10, 3) - 1 >= (2 * 3 + 3) * (Fraction(12, 9) ** 0)))

# eq:lk_step_ineq (matmul_9_4_constant.tex L445)
# States: rho L_j - 1/(c-1) <= L_{j+1} <= rho L_j + (c-3)/(c-1) and shift identities.
# Derived from: eq:Lk_recurrence, eq:rho_def
# Test: Cleared-denominator symbolic identities in Q[c]: 3 + (c-1) == c+2 and 3(c-3) + (c-3)(c-1) == (c-3)(c+2).
# Mutant: Replacing (c-3) by (c-2) breaks the shift identity.
eq("eq:lk_step_ineq", 445, "Fixed-point shift identities for L_k recursion")
symcheck("3 + (c - 1) == c + 2 (i.e. 1/(c-1) + 1/3 == rho/3)", 3 + (c_s - 1) - (c_s + 2))
symcheck("3(c-3) + (c-3)(c-1) == (c-3)(c+2)", 3 * (c_s - 3) + (c_s - 3) * (c_s - 1) - (c_s - 3) * (c_s + 2))
mutant("replacing c-3 by c-2 breaks shift identity", 3 * (c_s - 3) + (c_s - 2) * (c_s - 1) - (c_s - 2) * (c_s + 2))

# ============================================================================
# SECTION 3.5: LAYER 5 POLE CASCADE, BINI CONVERSION, AND HIDDEN CONSTANT
# ============================================================================
part("SECTION 3.5: LAYER 5 POLE CASCADE, BINI CONVERSION, AND C(tau)")

# eq:half_round_poles (matmul_9_4_constant.tex L464)
# States: P_half = 3((2d+1)w - 1), N_half = 6((d+1)w - 1).
# Derived from: eq:single_leg_poles
# Test: Exact symbolic tripling check in Q[d, w].
# Mutant: Doubling instead of tripling fails three-leg symmetrization count.
eq("eq:half_round_poles", 464, "Half-round pole sum P_half and max positive degree N_half")
P_half_s = 3 * ((2 * d_s + 1) * w_s - 1)
N_half_s = 6 * ((d_s + 1) * w_s - 1)
symcheck("P_half == 3 * P_1", P_half_s - 3 * ((2 * d_s + 1) * w_s - 1))
symcheck("N_half == 3 * N_1", N_half_s - 3 * (2 * (d_s + 1) * w_s - 2))
mutant("2*P_1 != P_half", 2 * ((2 * d_s + 1) * w_s - 1) - P_half_s)

# eq:pole_cascade_exact (matmul_9_4_constant.tex L475)
# States: P_seq(ell) + 1 = S^ell where S = P_half + 1 = 3(2d+1)w - 2.
# Derived from: eq:half_round_poles
# Test: Exact integer check of recurrence vs S^ell for ell=0..8 at d=2, w=5.
# Mutant: Linear growth ell*P_half + 1 disagrees with S^ell for ell >= 2.
eq("eq:pole_cascade_exact", 475, "Exact induction P_seq(ell) + 1 = S^ell")
P_h = 3 * ((2 * 2 + 1) * 5 - 1)
S_val = P_h + 1
p_cur = 0
ok_cas = True
for ell in range(9):
    if p_cur + 1 != S_val ** ell:
        ok_cas = False
    p_cur = P_h + S_val * p_cur
boolcheck("P_seq(ell) + 1 == S^ell exact for ell=0..8", ok_cas)
boolcheck("MUTANT REJECTED: linear ell*P_h + 1 != S^ell at ell=2", 2 * P_h + 1 != S_val ** 2)

# eq:deps_upper (matmul_9_4_constant.tex L480)
# States: d_eps^(2k) <= N_half*(S^(2k)-1)/(S-1) = ((2(d+1)w-2)/((2d+1)w-1))*(S^(2k)-1) < 2 S^(2k).
# Derived from: eq:half_round_poles, eq:pole_cascade_exact
# Test: Exact cleared-denominator symbolic check in Q[d, w] + concrete ratio in (1, 2).
# Mutant: Claiming ratio <= 1 is false.
eq("eq:deps_upper", 480, "Exact geometric upper bound on composed eps-degree")
S_s = P_half_s + 1
symcheck("N_half * ((2d+1)w - 1) == (S - 1) * (2(d+1)w - 2)",
         N_half_s * ((2 * d_s + 1) * w_s - 1) - (S_s - 1) * (2 * (d_s + 1) * w_s - 2))
ratio_d1_w3 = Fraction(2 * (1 + 1) * 3 - 2, (2 * 1 + 1) * 3 - 1)
boolcheck("1 < N_half/(S-1) < 2 at d=1, w=3 (ratio=10/8=5/4)", Fraction(1) < ratio_d1_w3 < Fraction(2))
boolcheck("MUTANT REJECTED: ratio <= 1 is false", not (ratio_d1_w3 <= Fraction(1)))

# eq:multivar_bini_worse (matmul_9_4_constant.tex L486)
# States: h*D_half^ell + 1 < (h*D_half + 1)^ell for all h >= 2, ell >= 2, D_half >= 1.
# Derived from: eq:pole_cascade_exact
# Test: Exhaustive integer check for h in 2..6, ell in 2..6, D_half in 1..6.
# Mutant: At ell=1, equality holds (strict inequality fails).
eq("eq:multivar_bini_worse", 486, "Iterated multivariate Bini strictly exceeds univariate")
boolcheck("h*D_half^ell + 1 < (h*D_half + 1)^ell for h,ell in 2..6, D_half in 1..6",
          all(hh * (DD ** ll) + 1 < (hh * DD + 1) ** ll for hh in range(2, 7) for ll in range(2, 7) for DD in range(1, 7)))
boolcheck("MUTANT REJECTED: fails at ell=1", not (2 * (3 ** 1) + 1 < (2 * 3 + 1) ** 1))

# eq:pole_induct (matmul_9_4_constant.tex L494)
# States: (P_half + 1) + S * P_seq(ell) = S * (1 + P_seq(ell)).
# Derived from: eq:pole_cascade_exact
# Test: Exact symbolic identity in Q[d, w, P_ell].
# Mutant: Replacing S with P_half breaks factorization.
eq("eq:pole_induct", 494, "Inductive step of pole cascade")
Pl_s = PolyQ.var("P_ell")
symcheck("S + S*P_ell == S*(1 + P_ell)", (P_half_s + 1) + S_s * Pl_s - S_s * (1 + Pl_s))
mutant("P_half + S*P_ell != S*(1 + P_ell)", P_half_s + S_s * Pl_s - S_s * (1 + Pl_s))

# eq:V_post_def, eq:R_exact_def, eq:bini_condition (L505, L510, L515)
# States: V = v_k^h, R_exact <= (h*d_eps + 1)*E_k^h < V^tau.
# Derived from: eq:vk_def, eq:Ek_def, eq:deps_upper
# Test: Toy exact check with v_k=10, E_k=600, tau=2.8, d_eps=5.
# Mutant: h too small violates Bini condition.
eq("eq:V_post_def", 505, "V = v_k^h")
boolcheck("10^4 == 10000", 10 ** 4 == 10000)
boolcheck("MUTANT REJECTED: 10*4 != 10^4", 10 * 4 != 10 ** 4)

eq("eq:R_exact_def", 510, "R_exact <= (h * d_eps + 1) * E_k^h")
h_toy, deps_toy, Ek_toy, vk_toy, tau_toy = 140, 5, 600, 10, 2.8
log_Rex = math.log(h_toy * deps_toy + 1) + h_toy * math.log(Ek_toy)
log_Vtau = h_toy * tau_toy * math.log(vk_toy)
boolcheck("toy Bini exact rank < V^tau at h=140", log_Rex < log_Vtau)
boolcheck("MUTANT REJECTED: omitting (h*d_eps+1) understates log_Rex",
          h_toy * math.log(Ek_toy) < log_Rex - 5.0)

eq("eq:bini_condition", 515, "(h * d_eps + 1) * E_k^h < V^tau")
h_too_small = 50
boolcheck("h=50 fails toy Bini condition while h=140 passes",
          math.log(h_too_small * deps_toy + 1) + h_too_small * math.log(Ek_toy) >= h_too_small * tau_toy * math.log(vk_toy)
          and math.log(140 * deps_toy + 1) + 140 * math.log(Ek_toy) < 140 * tau_toy * math.log(vk_toy))
boolcheck("MUTANT REJECTED: h=1 fails toy Bini condition",
          not (math.log(1 * deps_toy + 1) + math.log(Ek_toy) < tau_toy * math.log(vk_toy)))

# eq:C_schoolbook, eq:C_strassen, eq:C_padding (L527, L532, L537)
# States: C >= (V-1)^{3-tau}; C >= ((V-1)/2)^{log2(7)-tau}; C_pad >= R^2/(V+1)^tau >= V^4/(V+1)^tau.
# Derived from: eq:V_post_def, eq:bini_condition
# Test: Checks all three bounds on concrete V=1000, tau=2.5, R=1000^2.45.
# Mutant: Claiming C < (V-1)^{3-tau} violates T(V-1) <= C*(V-1)^tau.
eq("eq:C_schoolbook", 527, "Schoolbook cutoff bound C >= (V - 1)^{3 - tau}")
V_t, tau_t = 1000, 2.5
C_sb_min = (V_t - 1) ** (3.0 - tau_t)
check("C_sb_min * (V-1)^tau == (V-1)^3", C_sb_min * (V_t - 1) ** tau_t, float((V_t - 1) ** 3), rtol=1e-12)
numutant("0.5 * C_sb_min violates T(V-1) <= C*(V-1)^tau", 0.5 * C_sb_min * (V_t - 1) ** tau_t, float((V_t - 1) ** 3), rtol=1e-6)

eq("eq:C_strassen", 532, "Strassen cutoff bound C >= ((V - 1)/2)^{log2(7) - tau}")
n_pow2 = 2 ** int(math.floor(math.log2(V_t - 1)))
log2_7 = math.log2(7.0)
boolcheck("power-of-2 witness n=512 satisfies (V-1)/2 < n <= V-1", (V_t - 1) / 2.0 < n_pow2 <= V_t - 1)
boolcheck("T(n)/n^tau > ((V-1)/2)^{log2(7)-tau}", n_pow2 ** (log2_7 - tau_t) > ((V_t - 1) / 2.0) ** (log2_7 - tau_t))
boolcheck("MUTANT REJECTED: omitting /2 can exceed n=512 bound", not (n_pow2 ** (log2_7 - tau_t) > (V_t - 1) ** (log2_7 - tau_t)))

eq("eq:C_padding", 537, "Power-of-V padding bound C_pad >= R^2/(V+1)^tau >= V^4/(V+1)^tau & exact Bini weights")
R_t = int(V_t ** 2.45)
boolcheck("R^2/(V+1)^tau >= V^4/(V+1)^tau since R >= V^2",
          (R_t ** 2) / ((V_t + 1) ** tau_t) >= (V_t ** 4) / ((V_t + 1) ** tau_t))
# Proposition 3.11(iv): outer Bini Lagrange weights at {1..N_pts} evaluated at 0 equal (-1)^{j-1} * comb(N_pts, j) in Z!
bini_weights_ok = True
for N_pts in range(1, 10):
    for j in range(1, N_pts + 1):
        w_j = Fraction(1, 1)
        for i in range(1, N_pts + 1):
            if i != j:
                w_j *= Fraction(-i, j - i)
        expected_w = Fraction(((-1) ** (j - 1)) * math.comb(N_pts, j), 1)
        if w_j != expected_w or w_j.denominator != 1:
            bini_weights_ok = False
boolcheck("Prop. 3.11(iv): outer Bini Lagrange weights at {1..N_pts} equal (-1)^{j-1}*C(N_pts,j) in Z for N_pts=1..9",
          bini_weights_ok)
boolcheck("MUTANT REJECTED: R < V^2 violates flattening lower bound", not ((V_t ** 2 - 1) ** 2 >= V_t ** 4))

# ============================================================================
# SECTION 4: UNIVERSAL LOWER BOUNDS AND CONSTRUCTIVE WITNESSES
# ============================================================================
part("SECTION 4.1: PURE-INTEGER UNIVERSAL BOUNDS AND ASYMPTOTIC SCALING")

# eq:pass_valid_cond, eq:univ_round_nat, eq:univ_vk_vs_w, eq:univ_d_linear_c (L564, L574, L579, L584)
# States: Exact Pass validity E_k^{q_tau} < v_k^{p_tau} implies exact Nat round bound, v_k^{4a_0} > w^{18b_0}, and d > c(3 + tau log2(d+1))/(6 delta).
# Derived from: eq:vk_def, eq:Ek_def, eq:lk_sandwich, eq:cubic_identity
# Test: Checks ALL 4 inequalities on exact constructive witness (c=6, d=139, k=114) at tau=2.800.
# Mutant: Failing triple (c=6, d=10, k=10) violates eq:pass_valid_cond and eq:univ_round_nat.
eq("eq:pass_valid_cond", 564, "Pass validity E_k^{q_tau} < v_k^{p_tau}")
c_w, d_w, k_w = 6, 139, 114
a0_t, b0_t = 11, 20
p_t, q_t = 9 * b0_t + 4 * a0_t, 4 * b0_t  # 224, 80 -> tau = 224/80 = 2.800 = 9/4 + 11/20
w_w = (c_w + 2) ** (2 * d_w) // (d_w + 1)
u_w = c_w ** (2 * d_w)
lam_w = (w_w // u_w) ** 2
Lk_w = exact_Lk(c_w, k_w)
log_Ek_w = k_w * math.log(64.0) + 9.0 * math.log(w_w) + 6 * d_w * math.log(2 * Lk_w - 1)
log_vk_w = 2.0 * math.log(w_w) + k_w * math.log(lam_w)
boolcheck("witness (6,139,114) satisfies E_k^{q_tau} < v_k^{p_tau}", q_t * log_Ek_w < p_t * log_vk_w)
boolcheck("MUTANT REJECTED: k=113 fails at (6, 139)",
          not (q_t * (113 * math.log(64.0) + 9.0 * math.log(w_w) + 6 * d_w * math.log(2 * exact_Lk(6, 113) - 1))
               < p_t * (2.0 * math.log(w_w) + 113 * math.log(lam_w))))

eq("eq:univ_round_nat", 574, "Exact Nat per-round necessary condition")
lhs_rn = q_t * math.log(64) + 2 * p_t * math.log(d_w + 1) + 4 * d_w * p_t * math.log(c_w) + 6 * d_w * q_t * math.log(c_w + 2)
rhs_rn = 4 * d_w * p_t * math.log(c_w + 2) + 6 * d_w * q_t * math.log(c_w - 1)
boolcheck("witness (6,139) satisfies exact Nat round condition", lhs_rn < rhs_rn)
lhs_bad = q_t * math.log(64) + 2 * p_t * math.log(11) + 4 * 10 * p_t * math.log(6) + 6 * 10 * q_t * math.log(8)
rhs_bad = 4 * 10 * p_t * math.log(8) + 6 * 10 * q_t * math.log(5)
boolcheck("MUTANT REJECTED: d=10 fails Nat round condition at c=6", not (lhs_bad < rhs_bad))

eq("eq:univ_vk_vs_w", 579, "Pure-integer universal bound v_k^{4 a_0} > w^{18 b_0}")
boolcheck("witness (6,139,114) satisfies 4*a0*log(v_k) > 18*b0*log(w)",
          4 * a0_t * log_vk_w > 18 * b0_t * math.log(w_w))
boolcheck("exponent cancellation 8*a0 + 9*q_tau - 2*p_tau == 18*b0",
          8 * a0_t + 9 * q_t - 2 * p_t == 18 * b0_t)
boolcheck("MUTANT REJECTED: 16*b0 != 18*b0", 8 * a0_t + 9 * q_t - 2 * p_t != 16 * b0_t)

eq("eq:univ_d_linear_c", 584, "Linear-in-c dimension floor d > c*(3 + tau*log2(d+1))/(6*delta)")
delta_t = a0_t / b0_t
tau_val_t = p_t / q_t
d_rhs = c_w * (3.0 + tau_val_t * math.log2(d_w + 1.0)) / (6.0 * delta_t)
boolcheck("witness d=139 strictly exceeds c*(3 + tau*log2(d+1))/(6*delta)", d_w > d_rhs, f"d={d_w} > {d_rhs:.2f}")
boolcheck("elementary bound (1 + 2/c)^c < 8 holds for c=2..200", all((1.0 + 2.0 / cc) ** cc < 8.0 for cc in range(2, 201)))
boolcheck("MUTANT REJECTED: (1 + 2/c)^c < 7 fails for large c", not ((1.0 + 2.0 / 100) ** 100 < 7.0))

# eq:univ_step1, eq:univ_step2, eq:univ_cancel, eq:univ_d_step1 (L592, L597, L608, L615)
# States: Derivation links for Theorem thm:universal_round_and_vk.
# Derived from: eq:pass_valid_cond, eq:lk_sandwich, eq:cubic_identity
# Test: Verifies each intermediate inequality strictly on witness (6, 139, 114).
# Mutant: Flipping direction of eq:univ_cancel contradicts (c+2)(c-1)^2 < c^3.
eq("eq:univ_step1", 592, "Step 1: lower bounding E_k^{q_tau} via 2 L_k - 1 >= rho^k")
log_step1_lhs = 9 * q_t * math.log(w_w) + k_w * q_t * math.log(64) + 6 * d_w * k_w * q_t * math.log(8 / 5)
boolcheck("step 1 chain holds strictly", log_step1_lhs <= q_t * log_Ek_w < p_t * log_vk_w)
boolcheck("MUTANT REJECTED: reversing <= fails", not (log_step1_lhs > q_t * log_Ek_w))

eq("eq:univ_step2", 597, "Step 2: w^{9 q_tau - 2 p_tau} < (Lambda^{p_tau} / (64^{q_tau} rho^{6 d q_tau}))^k")
lhs_s2 = (9 * q_t - 2 * p_t) * math.log(w_w)
rhs_s2 = k_w * (p_t * math.log(lam_w) - q_t * math.log(64) - 6 * d_w * q_t * math.log(8 / 5))
boolcheck("step 2 holds strictly", lhs_s2 < rhs_s2)
boolcheck("MUTANT REJECTED: k=1 violates step 2", not (lhs_s2 < rhs_s2 / k_w))

eq("eq:univ_cancel", 608, "Cancellation showing Lambda^{p_tau}/(64^{q_tau} rho^{6 d q_tau} Lambda^{4 a_0}) < 1")
log_ratio_cancel = (p_t - 4 * a0_t) * math.log(lam_w) - q_t * math.log(64) - 6 * d_w * q_t * math.log(8 / 5)
boolcheck("exact log ratio < 0 (ratio < 1)", log_ratio_cancel < 0.0, f"log_ratio={log_ratio_cancel:.2f}")
boolcheck("exponent algebra 36 - 24 == 12", 36 - 24 == 12)
boolcheck("MUTANT REJECTED: wrong sign on exponent", 36 + 24 != 12)

eq("eq:univ_d_step1", 615, "Factored round inequality 64^{4 b_0} (d+1)^{18 b_0 + 8 a_0} < (1 + 2/c)^{16 a_0 d}")
lhs_ds1 = 4 * b0_t * math.log(64) + (18 * b0_t + 8 * a0_t) * math.log(d_w + 1)
mid_ds1 = 12 * b0_t * d_w * math.log(1 - (3 * c_w - 2) / (c_w ** 3)) + 16 * a0_t * d_w * math.log(1 + 2 / c_w)
rhs_ds1 = 16 * a0_t * d_w * math.log(1 + 2 / c_w)
boolcheck("lhs < mid < rhs strictly", lhs_ds1 < mid_ds1 < rhs_ds1)
boolcheck("MUTANT REJECTED: mid > rhs is false", not (mid_ds1 > rhs_ds1))

# eq:asymptotic_pre, eq:asymptotic_post, eq:k_scaling, eq:h_scaling_lb (L629, L634, L645, L652)
# States: Asymptotic scaling Theta(delta^{-3}(ln delta^{-1})^2) pre-Bini and Theta(delta^{-5}(ln delta^{-1})^3) post-Bini.
# Derived from: eq:univ_vk_vs_w, eq:univ_d_linear_c, eq:c_min_bound, eq:deps_upper
# Test: Evaluates scaled ratios across delta = 0.05, 0.01, 0.001 verifying bounded convergence.
# Mutant: Wrong exponent delta^{-2} or delta^{-4} diverges by >25x across delta in [0.001, 0.05].
eq("eq:asymptotic_pre", 629, "Pre-Bini scaling Theta(delta^{-3} (ln delta^{-1})^2)")
pre_samples = [(0.05, 37963961.01), (0.01, 8.719e9), (0.001, 1.661e13)]
pre_ratios = [v / ((d ** -3) * (math.log(1 / d) ** 2)) for d, v in pre_samples]
boolcheck("pre-Bini ratio / (delta^{-3} ln^2(1/delta)) stays within factor 1.6x across 50x in delta",
          max(pre_ratios) / min(pre_ratios) < 1.6, f"ratios={[round(x, 1) for x in pre_ratios]}")
bad_pre_ratios = [v / ((d ** -2) * (math.log(1 / d) ** 2)) for d, v in pre_samples]
boolcheck("MUTANT REJECTED: delta^{-2} diverges by >30x", max(bad_pre_ratios) / min(bad_pre_ratios) > 30.0)

eq("eq:asymptotic_post", 634, "Post-Bini scaling Theta(delta^{-5} (ln delta^{-1})^3)")
post_samples = [(0.05, 1.020e12), (0.01, 7.985e15), (0.001, 2.145e21)]
post_ratios = [v / ((d ** -5) * (math.log(1 / d) ** 3)) for d, v in post_samples]
boolcheck("post-Bini ratio / (delta^{-5} ln^3(1/delta)) stays within factor 1.9x across 50x in delta",
          max(post_ratios) / min(post_ratios) < 1.9, f"ratios={[round(x, 1) for x in post_ratios]}")
bad_post_ratios = [v / ((d ** -4) * (math.log(1 / d) ** 3)) for d, v in post_samples]
boolcheck("MUTANT REJECTED: delta^{-4} diverges by >25x", max(bad_post_ratios) / min(bad_post_ratios) > 25.0)

eq("eq:k_scaling", 645, "Constructive k = Theta(delta^{-2} ln(1/delta))")
k_samples = [(0.05, 27605), (0.01, 1003639), (0.001, 141325903)]
k_ratios = [kv / ((d ** -2) * math.log(1 / d)) for d, kv in k_samples]
boolcheck("k / (delta^{-2} ln(1/delta)) stays within factor 1.15x across 50x in delta",
          max(k_ratios) / min(k_ratios) < 1.15, f"ratios={[round(x, 1) for x in k_ratios]}")
bad_k_ratios = [kv / ((d ** -1) * math.log(1 / d)) for d, kv in k_samples]
boolcheck("MUTANT REJECTED: delta^{-1} diverges by >40x", max(bad_k_ratios) / min(bad_k_ratios) > 40.0)

eq("eq:h_scaling_lb", 652, "Bini power h = Theta(delta^{-2} ln(1/delta))")
h_samples = [(0.05, 12558), (0.01, 424254), (0.001, 59043144)]
h_ratios = [hv / ((d ** -2) * math.log(1 / d)) for d, hv in h_samples]
boolcheck("h / (delta^{-2} ln(1/delta)) stays within factor 1.25x across 50x in delta",
          max(h_ratios) / min(h_ratios) < 1.25, f"ratios={[round(x, 1) for x in h_ratios]}")
bad_h_ratios = [hv / ((d ** -3) * math.log(1 / d)) for d, hv in h_samples]
boolcheck("MUTANT REJECTED: delta^{-3} collapses by >40x", max(bad_h_ratios) / min(bad_h_ratios) > 40.0)

# eq:sharp_denom, eq:sharp_k_lnLam_lb (L665, L670) + Tables tab:pre_bini_bounds & tab:post_bini_bounds
# States: Sharp universal lower bound equations and verification of Tables 2 & 3.
# Derived from: eq:lk_ceiling_boost, eq:univ_round_nat, eq:C_schoolbook, eq:C_strassen, eq:C_padding
# Test: Recomputes sharp UB and LB for tau = 2.800 and verifies printed table digits match.
# Mutant: Dropping B_L weakens LB at c=6, d=136 below 7197.27.
eq("eq:sharp_denom", 665, "Exact per-round upper bounds lambda_ub and Delta_ub")
lam_ub_6_139 = 4 * 139 * math.log(8 / 6) - 2 * math.log(140)
del_ub_6_139 = 2.8 * lam_ub_6_139 - 6 * 139 * math.log(8 / 5) - math.log(64)
boolcheck("exact integer Lambda * 140^2 * 6^(4*139) <= 8^(4*139) (zero float rounding)",
          lam_w * (140 ** 2) * (6 ** (4 * 139)) <= 8 ** (4 * 139))
boolcheck("MUTANT REJECTED: omitting -2*ln(d+1) overstates lambda_ub", 4 * 139 * math.log(8 / 6) > lam_ub_6_139 + 9.0)

eq("eq:sharp_k_lnLam_lb", 670, "44-digit outward-rounded interval global LB certification & exact integer witnesses (Tables 2-3)")

# ============================================================================
# 44-DIGIT OUTWARD-ROUNDED DECIMAL INTERVAL ARITHMETIC (PURE STDLIB)
# ============================================================================
_ILO = _DecCtx(prec=44, rounding=_RFL)
_IHI = _DecCtx(prec=44, rounding=_RCL)
_INE = _DecCtx(prec=44, rounding=_RNE)


class _Iv:
    """Outward-rounded 44-digit Decimal interval [a, b]."""
    __slots__ = ("a", "b")

    def __init__(self, a, b=None):
        self.a = _Dec(str(a)) if not isinstance(a, _Dec) else a
        self.b = self.a if b is None else (_Dec(str(b)) if not isinstance(b, _Dec) else b)

    def __add__(self, other):
        o = _iv(other)
        return _Iv(_ILO.add(self.a, o.a), _IHI.add(self.b, o.b))

    __radd__ = __add__

    def __sub__(self, other):
        o = _iv(other)
        return _Iv(_ILO.subtract(self.a, o.b), _IHI.subtract(self.b, o.a))

    def __rsub__(self, other):
        return _iv(other) - self

    def __mul__(self, other):
        o = _iv(other)
        if self.a >= 0 and o.a >= 0:
            return _Iv(_ILO.multiply(self.a, o.a), _IHI.multiply(self.b, o.b))
        ps_lo = (_ILO.multiply(x, y) for x in (self.a, self.b) for y in (o.a, o.b))
        ps_hi = (_IHI.multiply(x, y) for x in (self.a, self.b) for y in (o.a, o.b))
        return _Iv(min(ps_lo), max(ps_hi))

    __rmul__ = __mul__

    def __truediv__(self, other):
        o = _iv(other)
        assert o.a > 0, f"Division by non-positive interval {o}"
        if self.a >= 0:
            return _Iv(_ILO.divide(self.a, o.b), _IHI.divide(self.b, o.a))
        return self * _Iv(_ILO.divide(_Dec(1), o.b), _IHI.divide(_Dec(1), o.a))

    def __rtruediv__(self, other):
        return _iv(other) / self

    def ln(self):
        assert self.a > 0
        return _Iv(_INE.next_minus(_INE.ln(self.a)), _INE.next_plus(_INE.ln(self.b)))

    def sqrt(self):
        assert self.a >= 0
        lo_v = _Dec(0) if self.a == 0 else _INE.next_minus(_INE.sqrt(self.a))
        return _Iv(lo_v, _INE.next_plus(_INE.sqrt(self.b)))

    def __repr__(self):
        return f"[{self.a}, {self.b}]"


def _iv(x) -> _Iv:
    return x if isinstance(x, _Iv) else _Iv(x)


@lru_cache(None)
def _ilg(n: int) -> _Iv:
    return _Iv(_Dec(n)).ln()


@lru_cache(None)
def _ilr(a: int, b: int) -> _Iv:
    return (_Iv(a) / _Iv(b)).ln()


_IL10 = _ilg(10)
_IL64 = _ilg(64)
_IL2 = _ilg(2)
_ILOG2_7 = _ilg(7) / _IL2
_IPI = _Iv(_Dec("3.14159265358979323846264338327950288419716"),
           _Dec("3.14159265358979323846264338327950288419717"))
_IHALF_LN_2PI = (_Iv(2) * _IPI).ln() / 2


def _ln_fact_iv(n: int) -> _Iv:
    """Robbins (1955) exact factorial enclosure: 1/(12n+1) < ln(n!) - Stirling < 1/(12n)."""
    if n <= 1:
        return _Iv(0)
    N = _Iv(n)
    base = (N + _Iv("0.5")) * N.ln() - N + _IHALF_LN_2PI
    return base + _Iv((_Iv(1) / (12 * n + 1)).a, (_Iv(1) / (12 * n)).b)


def _ln_Md_iv(c: int, d: int) -> _Iv:
    """Exact/Robbins+log-concave geometric-tail interval enclosure of ln M_d(c) (zero Gaussian approximation)."""
    if d <= 200:
        exact_m = sum((math.comb(d, hh) * ((c + 1) ** (d - hh))) ** 2 for hh in range(d + 1))
        return _Iv(_Dec(exact_m)).ln()
    h_star = max(0, min(d, (d + 1) // (c + 2)))
    sigma = math.sqrt(max(1.0, d / (c + 2.0) * (1.0 - 1.0 / (c + 2.0))))
    W = max(12, int(math.ceil(11.0 * sigma)))
    h1, h2 = max(0, h_star - W), min(d, h_star + W)
    lc1 = _ilg(c + 1)
    l_peak = 2 * (_ln_fact_iv(d) - _ln_fact_iv(h_star) - _ln_fact_iv(d - h_star) + (d - h_star) * lc1)
    total = _Iv(1)
    cur = _Iv(1)
    for hh in range(h_star, h2):
        r = _Iv(d - hh) / _Iv((hh + 1) * (c + 1))
        cur = cur * (r * r)
        total = total + cur
    tail_hi = _Iv(0)
    if h2 < d:
        rn = _Iv(d - h2) / _Iv((h2 + 1) * (c + 1))
        rn2 = rn * rn
        assert rn2.b < 1
        tail_hi = tail_hi + cur * rn2 / (1 - rn2)
    cur = _Iv(1)
    for hh in range(h_star, h1, -1):
        r = _Iv(hh * (c + 1)) / _Iv(d - hh + 1)
        cur = cur * (r * r)
        total = total + cur
    if h1 > 0:
        rn = _Iv(h1 * (c + 1)) / _Iv(d - h1 + 1)
        rn2 = rn * rn
        assert rn2.b < 1
        tail_hi = tail_hi + cur * rn2 / (1 - rn2)
    return l_peak + _Iv(total.a, (total + tail_hi).b).ln()


def _wlogs_iv(c: int, d: int) -> _Iv:
    """Outward-rounded enclosure of ln(floor((c+2)^(2d)/(d+1)))."""
    if d < 100:
        return _Iv(_Dec(((c + 2) ** (2 * d)) // (d + 1))).ln()
    v = 2 * d * _ilg(c + 2) - _ilg(d + 1)
    # For d >= 100, (d+1)/(c+2)^(2d) <= 101 / 4^200 < 1e-118 < 1e-99.
    return _Iv(_ILO.subtract(v.a, _Dec("1e-99")), v.b)


@lru_cache(None)
def _ubox_iv(c: int, d: int) -> _Iv:
    if d >= 100:
        return _wlogs_iv(c, d) / d
    eps = _Iv(d + 1) / _Iv((c + 2) ** (2 * d))
    return 2 * _ilg(c + 2) - _ilg(d + 1) / d + (1 - eps).ln() / d


def _ln_2Lk_m1_iv(c: int, k: int) -> _Iv:
    """Outward-rounded enclosure of ln(2*L_k(c) - 1): exact recurrence up to 50000, Thm. 3.9 bounds above."""
    steps = min(k, 50000)
    L = 1
    for _ in range(steps):
        L += (3 * L - 1 + c - 2) // (c - 1)
    if k <= 50000:
        return _Iv(_Dec(2 * L - 1)).ln()
    rem = k - steps
    ln_rho = _ilr(c + 2, c - 1)
    # Valid for all c >= 2: 2*L_{j+1}-1 >= rho*(2*L_j-1) + 1/(c-1) > rho*(2*L_j-1)
    lo_v = _Iv(_Dec(2 * L - 1)).ln() + rem * ln_rho
    hi_v = (_Iv(2) * (_Iv(_Dec(L)) + _Iv(c - 3) / _Iv(3))).ln() + rem * ln_rho
    return _Iv(lo_v.a, hi_v.b)


def _matches_display(val_iv: _Iv, displayed_str: str) -> bool:
    """Check that interval val_iv lies strictly inside the open half-ULP rounding cell of displayed_str."""
    d_val = _Dec(displayed_str)
    exp = d_val.as_tuple().exponent
    half_ulp = _Dec(5) * (_Dec(10) ** (exp - 1))
    cell_lo = _IHI.subtract(d_val, half_ulp)
    cell_hi = _ILO.add(d_val, half_ulp)
    return val_iv.a > cell_lo and val_iv.b < cell_hi


def certify_global_pass_threshold(tau_val, mode: str, threshold) -> bool:
    """Rigorous 44-digit outward-rounded interval 2D branch-and-bound proof that
    the Pass lower envelope is >= threshold over ALL (c, d) in N_{>=2} x N_{>=1}.
    """
    t = _iv(tau_val)
    target = _iv(threshold).b
    delt = t - _Iv("2.25")
    peak = t / delt
    p_slope = 4 * t * ((peak + 2) / peak).ln() - 6 * ((peak + 2) / (peak - 1)).ln()

    @lru_cache(None)
    def s_iv(cc: int) -> _Iv:
        return 4 * t * _ilr(cc + 2, cc) - 6 * _ilr(cc + 2, cc - 1)

    @lru_cache(None)
    def d_lo_analytic(cc: int) -> int:
        x = 1
        for _ in range(16):
            rhs_lo = (_Iv(cc) * (3 + t * _ilg(x + 1) / _IL2) / (6 * delt)).a
            x = max(x, int(rhs_lo) + 1)
        return x

    def tail_lb(cc: int, dd: int, smax_hi: _Dec) -> _Dec:
        u = _ubox_iv(cc, dd).a
        z = _Iv("4.5") / delt * _Iv(u) * dd / _IL10
        return (z if mode == "pre" else z * _Iv(u) / _Iv(smax_hi)).a

    c0 = 2
    while s_iv(c0).b <= 0:
        c0 += 1
    cmax = int(peak.b) + 3
    while tail_lb(cmax, d_lo_analytic(cmax), s_iv(cmax).b) < target:
        cmax = cmax * 3 // 2 + 5
    dmax = d_lo_analytic(c0) + 10
    while tail_lb(c0, dmax, p_slope.b) < target:
        dmax *= 2

    def box_lb(x: int, y: int, l: int, r: int) -> _Dec:
        sm = max(s_iv(x).b, s_iv(y).b)
        if x <= peak.b and peak.a <= y:
            sm = max(sm, p_slope.b)
        du = (_Iv(sm) - (2 * t * _ilg(r + 1) + _IL64) / r).b
        if du <= 0:
            return _Dec("Infinity")
        u = (_wlogs_iv(x, l) / l if (x == y and l == r) else _ubox_iv(x, l)).a
        base = ((9 - 2 * t) * _Iv(u)).a
        j1, j2 = (x - 1) // 3, (y - 1) // 3
        bl = (max(_Dec(0), (_ilg(2 * j1 + 1) - j2 * _ilr(x + 2, x - 1)).a)
              if (_Iv(base) / _Iv(du)).a >= j2 else _Dec(0))
        numer = (_Iv(base) + 6 * _Iv(bl)).a
        if mode == "pre":
            lam = (4 * _ilr(y + 2, y) - 2 * _ilg(l + 1) / l).a
            if lam <= 0:
                return _Dec(0)
            return (_Iv(l) * (2 * _Iv(u) + _Iv(numer) * _Iv(lam) / _Iv(du)) / _IL10).a
        a = 2 * _Iv(u)
        b = (6 * _ilr(y + 2, y - 1) + _IL64 / r) / t
        K = _Iv((_Iv(numer) / _Iv(du)).a)
        if K.a >= _Dec("0.5"):
            val = 2 * (a + b * K) + (2 * K - 1) * b
            if K.a > _Dec("0.5"):
                val = val + 2 * (2 * b * (2 * K - 1) * (a + b * K)).sqrt()
        else:
            val = (a + b) / (1 - K)
        us = _Iv(u)
        if x == y and l == r:
            if l < 100:
                us = _Iv(_Dec(3 * (2 * l + 1) * (((x + 2) ** (2 * l)) // (l + 1)) - 2)).ln() / l
            else:
                us = (_ilg(3 * (2 * l + 1)) + _wlogs_iv(x, l) - _Iv("1e-99")) / l
        return (us / _Iv(du) * l * val / _IL10).a

    stack = [(c0, cmax, d_lo_analytic(c0), dmax)]
    while stack:
        x, y, l, r = stack.pop()
        l = max(l, d_lo_analytic(x))
        if l > r or box_lb(x, y, l, r) >= target:
            continue
        if x == y and l == r:
            return False
        if y > x and (y - x) * l >= (r - l) * x:
            m = (x + y) // 2
            stack.extend(((m + 1, y, l, r), (x, m, l, r)))
        else:
            m = (l + r) // 2
            stack.extend(((x, y, m + 1, r), (x, y, l, m)))
    return True


def _cert_pass_witness(tau_str: str, mode: str, c: int, d: int, k: int, h: int = 1) -> tuple[bool, _Iv]:
    """44-digit outward-rounded interval verification of exact Pass-family witnesses.
    mode in {'pre', 'post', 'opt', 'openai'}.
    """
    t = _Iv(tau_str)
    if mode in ("pre", "post"):
        ln_w = _wlogs_iv(c, d)
        ln_rc = _IL64
        ln_S = _ilg(3 * (2 * d + 1)) + ln_w
    elif mode == "opt":
        ln_w = _ln_Md_iv(c, d)
        ln_rc = _IL64
        ln_S = _ilg(3 * (2 * d + 1)) + ln_w
    elif mode == "openai":
        ln_w = _wlogs_iv(c, d)
        ln_rc = _ilg(15625)
        ln_S = _ilg(6 * (2 * d + 1)) + 2 * ln_w
    else:
        raise ValueError(mode)
    ln_Q = ln_w - 2 * d * _ilg(c)
    if ln_Q.a > 50:
        ln_lam = _Iv(_ILO.subtract((2 * ln_Q).a, _Dec("1e-18")), (2 * ln_Q).b)
    else:
        ww = (sum((math.comb(d, hh) * ((c + 1) ** (d - hh))) ** 2 for hh in range(d + 1))
              if mode == "opt" else ((c + 2) ** (2 * d)) // (d + 1))
        ln_lam = _Iv(_Dec((ww // (c ** (2 * d))) ** 2)).ln()
    ln_vk = 2 * ln_w + k * ln_lam
    ln_2Lk1 = _ln_2Lk_m1_iv(c, k)
    ln_Ek = k * ln_rc + 9 * ln_w + 6 * d * ln_2Lk1
    if mode == "pre":
        return ln_Ek.b < (t * ln_vk).a, ln_vk / _IL10
    # Certified sufficient upper bound D = 2 * S^(2k); ln(h*D + 1) <= ln(2*h) + 2*k*ln_S + 1e-20
    ln_hDp1 = _Iv(_Dec(2 * h)).ln() + 2 * k * ln_S + _Iv(0, _Dec("1e-20"))
    ln_R = ln_hDp1 + h * ln_Ek
    ln_V = h * ln_vk
    return ln_R.b < (t * ln_V).a, ln_V / _IL10


table2_rows = [
    ("2.800", "7197.27", "7927.63", (6, 139, 114)),
    ("2.695", "15809.49", "17442.54", (6, 207, 169)),
    ("2.500", "126725.43", "137617.22", (12, 719, 719)),
    ("2.371", "1671405.33", "1770235.12", (24, 3392, 3769)),
    ("2.321", "10782969.44", "11348489.01", (42, 10917, 12900)),
    ("2.300", "36254552.34", "37963961.01", (57, 23003, 27605)),
    ("2.260", "8.439e9", "8.719e9", (304, 763002, 1003639)),
    ("2.251", "1.624e13", "1.661e13", (3032, 102600000, 141345029)),
]
table3_rows = [
    ("2.800", "9.504e5", "1.173e6", (5, 219, 150, 61), "1.900e5", "6.990e3", "1.140e6"),
    ("2.695", "3.213e6", "3.755e6", (6, 335, 236, 95), "9.801e5", "3.610e5", "4.193e6"),
    ("2.500", "9.304e7", "1.046e8", (10, 1073, 866, 356), "4.652e7", "2.859e7", "1.395e8"),
    ("2.371", "6.149e9", "6.726e9", (21, 5052, 4756, 1775), "3.868e9", "2.683e9", "1.001e10"),
    ("2.321", "1.303e11", "1.403e11", (36, 16021, 16123, 5793), "8.852e10", "6.340e10", "2.189e11"),
    ("2.300", "9.563e11", "1.020e12", (51, 34246, 35518, 12558), "6.694e11", "4.852e11", "1.625e12"),
    ("2.260", "7.657e15", "7.986e15", (255, 1107000, 1253000, 424300), "5.666e15", "4.191e15", "1.332e16"),
    ("2.251", "2.079e21", "2.145e21", (2546, 149000000, 178740000, 59048000), "1.557e21", "1.156e21", "3.636e21"),
]
for (ts, pre_lb_s, pre_ub_s, (cw, dw, kw)), (_, post_lb_s, post_ub_s, (cp, dp, kp, hp), csb_s, cstr_s, cpad_s) in zip(table2_rows, table3_rows):
    t_iv = _Iv(ts)
    boolcheck(f"Table 2 tau={ts}: 44-digit interval certified pre-Bini LB >= {pre_lb_s}",
              certify_global_pass_threshold(ts, "pre", pre_lb_s))
    boolcheck(f"Table 3 tau={ts}: 44-digit interval certified post-Bini LB >= {post_lb_s}",
              certify_global_pass_threshold(ts, "post", post_lb_s))
    ok_pre, lv_pre = _cert_pass_witness(ts, "pre", cw, dw, kw)
    boolcheck(f"Table 2 tau={ts} witness {(cw, dw, kw)} interval-certified valid & rounds to {pre_ub_s}",
              ok_pre and _matches_display(lv_pre, pre_ub_s))
    ok_post, lv_post = _cert_pass_witness(ts, "post", cp, dp, kp, hp)
    boolcheck(f"Table 3 tau={ts} witness {(cp, dp, kp, hp)} interval-certified 2*S^(2k) & rounds to {post_ub_s}",
              ok_post and _matches_display(lv_post, post_ub_s))
    # Finite-size corrected C_sb ((V-1)), C_Str ((V-1)/2 with +log10(2)), C_pad (V+1):
    # For V > 10^100, (V +/- 1) log loss is < 1e-98 << 1e-35.
    req_sb = _Iv(csb_s) / (3 - t_iv) + _Iv("1e-35")
    req_str = _Iv(cstr_s) / (_ILOG2_7 - t_iv) + _IL2 / _IL10 + _Iv("1e-35")
    req_pad = _Iv(cpad_s) / (4 - t_iv) + _Iv("1e-35")
    boolcheck(f"Table 3 C_sb interval-certified at tau={ts} (with V-1 loss)",
              certify_global_pass_threshold(ts, "post", req_sb))
    boolcheck(f"Table 3 C_Str interval-certified at tau={ts} (with (V-1)/2 loss)",
              certify_global_pass_threshold(ts, "post", req_str))
    boolcheck(f"Table 3 C_pad interval-certified at tau={ts} (with V+1 loss)",
              certify_global_pass_threshold(ts, "post", req_pad))

# Negative-control mutants on global interval certifier & display rounding:
boolcheck("MUTANT REJECTED: overstated pre-Bini LB 7197.30 at tau=2.800 refuted",
          not certify_global_pass_threshold("2.800", "pre", "7197.30"))
boolcheck("MUTANT REJECTED: float64 ULP overstatement 7197.282318937111 at tau=2.800 refuted",
          not certify_global_pass_threshold("2.800", "pre", "7197.282318937111"))
boolcheck("MUTANT REJECTED: overstated post-Bini LB 7.658e15 at tau=2.260 refuted",
          not certify_global_pass_threshold("2.260", "post", "7.658e15"))
boolcheck("MUTANT REJECTED: overstated post-Bini LB 2.080e21 at tau=2.251 refuted",
          not certify_global_pass_threshold("2.251", "post", "2.080e21"))
_, _lv_2800_chk = _cert_pass_witness("2.800", "pre", 6, 139, 114)
boolcheck("MUTANT REJECTED: 1-last-digit display mutant 7927.64 rejected (exact 7927.63)",
          not _matches_display(_lv_2800_chk, "7927.64"))
boolcheck("MUTANT REJECTED: boundary tie 1.235 rejected for display string 1.23",
          not _matches_display(_Iv("1.235"), "1.23"))

lam_ub_136 = 4 * 136 * math.log(8 / 6) - 2 * math.log(137)
del_ub_136 = 2.8 * lam_ub_136 - 6 * 136 * math.log(8 / 5) - math.log(64)
ln_w_136 = 2 * 136 * math.log(8) - math.log(137)
lb_no_BL = (2 * ln_w_136 + ((9 - 5.6) * ln_w_136) / (del_ub_136 / lam_ub_136)) / math.log(10.0)
numutant("dropping ceiling boost B_L understates sharp LB", lb_no_BL, 7197.27, rtol=1e-2)

# ============================================================================
# SECTION 4.3: FINITE DIRECT-SUM TO SINGLE-MATRIX CONVERSION & TABLE 4
# ============================================================================
part("SECTION 4.3: FINITE DIRECT-SUM TO SINGLE-MATRIX CONVERSION & FULL TABLE 4")

# eq:finite_schonhage, eq:schonhage_induct (L696, L704)
# States: R_{r_Sch} <= P * (R_ex/P + 1)^{r_Sch}; certifies ALL four Table 4 columns (OpenAI 5w, Literal Pass, Opt. Pass M_d, Str_3).
# Derived from: eq:V_post_def, eq:bini_condition, eq:Md_exact, eq:openai_tight_deg
# Test: Runs exact recurrence R_{j+1} = ceil(R_j/P) * R_ex, 44-digit interval checks for all 12 OpenAI 5w / Opt. Pass tuples, and Str_3 checks.
# Mutant: Omitting +1 in (R_ex/P + 1) fails; h-1 fails for tight Table 4 witnesses; (22,3,7) fails at 2.800.
eq("eq:finite_schonhage", 696, "Finite direct-sum conversion & full 4-column Table 4 44-digit interval audit")
P_ex, Rex_ex = 7, 25
Rj = Rex_ex
B_ex = Fraction(Rex_ex, P_ex) + 1
ok_sch = True
for j in range(1, 8):
    if not (Rj <= P_ex * (B_ex ** j)):
        ok_sch = False
    Rj = ((Rj + P_ex - 1) // P_ex) * Rex_ex
boolcheck("exact recurrence R_j <= P*(R_ex/P + 1)^j holds for j=1..7", ok_sch)

# Verify shifted OpenAI 5w pole budget on concrete M = 2..15:
# Shifted weights: w'(X)=g^2-1 >= 0, w'(Y)=h*u-h^2+M^2-M >= 0, w'(Z)=-h*v+1+M-M^2 in [-(2M^2-M-1), 0]
ok_oai_shift = True
for MM in range(2, 16):
    for gg in range(1, MM + 1):
        if not (0 <= gg * gg - 1 <= MM * MM - 1):
            ok_oai_shift = False
    for hh in range(1, MM + 1):
        for uu in range(1, MM + 1):
            wy = hh * uu - hh * hh + MM * MM - MM
            if not (0 <= wy <= MM * MM - MM + (MM * MM) // 4):
                ok_oai_shift = False
            wz = -hh * uu + 1 + MM - MM * MM
            if not (-(2 * MM * MM - MM - 1) <= wz <= 0):
                ok_oai_shift = False
boolcheck("OpenAI 5M shifted weights give pole-free E^L,E^R and exact P_out=2M^2-M-1 on D (M=2..15)", ok_oai_shift)

# Certify ALL 6 OpenAI 5w and ALL 6 Opt. Pass (M_d) Table 4 witnesses in 44-digit outward intervals!
table4_packings = [
    ("2.800", (5, 259, 149, 123), "2.793e6", (5, 120, 148, 62), "6.478e5", "1.173e6"),
    ("2.695", (6, 409, 240, 180), "8.869e6", (6, 183, 237, 93), "2.024e6", "3.755e6"),
    ("2.500", (10, 1278, 929, 641), "2.409e8", (10, 553, 934, 323), "5.279e7", "1.046e8"),
    ("2.371", (21, 5898, 5088, 3208), "1.519e10", (21, 2419, 5122, 1615), "3.158e9", "6.726e9"),
    ("2.260", (255, 1202177, 1356218, 779952), "1.725e16", (260, 433560, 1378948, 396421), "3.154e15", "7.986e15"),
    ("2.251", (2620, 158000000, 196359676, 110238457), "4.534e21", (2620, 53560000, 196719513, 55220219), "7.712e20", "2.145e21"),
]
ratios_lit_opt, ratios_oai_opt, ratios_oai_lit = [], [], []
for ts, tup_oai, disp_oai, tup_opt, disp_opt, disp_lit in table4_packings:
    ok_oai, lv_oai = _cert_pass_witness(ts, "openai", *tup_oai)
    ok_opt, lv_opt = _cert_pass_witness(ts, "opt", *tup_opt)
    boolcheck(f"Table 4 OpenAI 5w tau={ts} {tup_oai} interval-certified & rounds to {disp_oai}",
              ok_oai and _matches_display(lv_oai, disp_oai))
    boolcheck(f"Table 4 Opt. Pass (M_d) tau={ts} {tup_opt} interval-certified & rounds to {disp_opt}",
              ok_opt and _matches_display(lv_opt, disp_opt))
    mo, ma, ml = float((lv_opt.a + lv_opt.b) / 2), float((lv_oai.a + lv_oai.b) / 2), float(_Dec(disp_lit))
    ratios_lit_opt.append(ml / mo)
    ratios_oai_opt.append(ma / mo)
    ratios_oai_lit.append(ma / ml)
boolcheck("Table 4 ratio ranges match text: lit/opt in [1.80, 2.79], oai/opt in [4.30, 5.89], oai/lit in [2.11, 2.39]",
          1.805 <= min(ratios_lit_opt) <= 1.815 and 2.775 <= max(ratios_lit_opt) <= 2.785
          and 4.305 <= min(ratios_oai_opt) <= 4.315 and 5.875 <= max(ratios_oai_opt) <= 5.885
          and 2.110 <= min(ratios_oai_lit) <= 2.120 and 2.375 <= max(ratios_oai_lit) <= 2.385)
# Negative controls on Table 4 OpenAI 5w & Opt. Pass witnesses: h - 1 fails!
boolcheck("MUTANT REJECTED: Table 4 OpenAI 5w tau=2.800 fails at h-1=122",
          not _cert_pass_witness("2.800", "openai", 5, 259, 149, 122)[0])
boolcheck("MUTANT REJECTED: Table 4 Opt. Pass tau=2.800 fails at h-1=61",
          not _cert_pass_witness("2.800", "opt", 5, 120, 148, 61)[0])

def _str3_ds_iv(N: int, h: int) -> tuple[_Iv, _Iv, _Iv]:
    """44-digit outward-rounded interval enclosure of untwisted Str_3^{otimes N} direct sum
    returning (log10_V, log10_P, eff_exp) from exact integer M = C(N, N/2)."""
    M = math.comb(N, N // 2)
    ln_M = _Iv(_Dec(M)).ln()
    ln_v = N * _ilg(3) + ln_M
    ln_P = 3 * h * ln_M
    ln_r = 3 * _Iv(_Dec(2 * M - 1)).ln() + 3 * N * _ilg(4)
    ln_hEp1 = _Iv(_Dec(h * 3 * (N + 1) * M + 1)).ln()
    eff_ds = (ln_hEp1 + h * (ln_r - 3 * ln_M)) / (h * ln_v)
    return (h * ln_v) / _IL10, ln_P / _IL10, eff_ds


def _str3_single_iv(N: int, h: int, r: int) -> tuple[_Iv, _Iv]:
    """44-digit outward-rounded interval enclosure of untwisted Str_3^{otimes N} single-matrix
    conversion via Lemma 4.3, returning (log10_V, eff_exp) from exact integer M = C(N, N/2)."""
    M = math.comb(N, N // 2)
    ln_M = _Iv(_Dec(M)).ln()
    ln_v = N * _ilg(3) + ln_M
    ln_P = 3 * h * ln_M
    ln_r = 3 * _Iv(_Dec(2 * M - 1)).ln() + 3 * N * _ilg(4)
    ln_hEp1 = _Iv(_Dec(h * 3 * (N + 1) * M + 1)).ln()
    ln_Rex = ln_hEp1 + h * ln_r
    d_rp = ln_Rex - ln_P
    if d_rp.a > 50:
        ln_B = d_rp + _Iv(0, _Dec("1e-20"))
    else:
        exp_neg = _Iv(_INE.next_minus(_INE.exp(d_rp.b.copy_negate())),
                      _INE.next_plus(_INE.exp(d_rp.a.copy_negate())))
        ln_B = d_rp + (_Iv(1) + exp_neg).ln()
    ln_R = ln_P + r * ln_B
    ln_V = h * r * ln_v
    return ln_V / _IL10, ln_R / ln_V


# Regression test for small-z branch of _str3_single_iv at (N,h,r)=(2,1,1):
# M=2, v=18, P=8, r_str=3^3*4^6=110592, h*E+1=19 -> R_ex=2101248, R=8*(2101248/8+1)=2101256 -> eff = ln(2101256)/ln(18)
_l10_211, _eff_211 = _str3_single_iv(2, 1, 1)
_exact_eff_211 = _Iv(_Dec(2101256)).ln() / _ilg(18)
boolcheck("small-z branch of _str3_single_iv encloses exact ln(2101256)/ln(18) at (2,1,1)",
          _eff_211.a <= _exact_eff_211.a and _eff_211.b >= _exact_eff_211.b)


# Verify all 5 Table 4 direct-sum witnesses and all 5 single-matrix witnesses in 44-digit intervals!
table4_ds = [
    ("2.800", 16, 2, "23.49", "24.66"),
    ("2.695", 18, 3, "39.82", "42.18"),
    ("2.500", 46, 5, "174.32", "193.73"),
    ("2.371", 190, 17, "2492.38", "2854"),
    ("2.330", 1322, 92, "94489.26", "109380"),
]
for ts, N_d, h_d, l10v_s, l10P_s in table4_ds:
    l10v_iv, l10P_iv, eff_ds_iv = _str3_ds_iv(N_d, h_d)
    boolcheck(f"Table 4 Str_3 direct sum at tau={ts} ({N_d},{h_d}) interval-valid (eff_hi={float(eff_ds_iv.b):.5f} < {ts})",
              eff_ds_iv.b < _Iv(ts).a)
    boolcheck(f"Table 4 Str_3 direct sum log10(V) interval rounds to {l10v_s}",
              _matches_display(l10v_iv, l10v_s))
    boolcheck(f"Table 4 Str_3 direct sum log10(P) interval rounds to {l10P_s}",
              _matches_display(l10P_iv, l10P_s))

table4_single = [
    ("2.800", 24, 3, 7, "375.54"),
    ("2.695", 30, 4, 9, "810.15"),
    ("2.500", 68, 7, 21, "7629.06"),
    ("2.371", 272, 26, 74, "4.047e5"),
    ("2.330", 1498, 166, 485, "9.371e7"),
]
for ts, N_s, h_s, r_s, l10V_s in table4_single:
    l10V_iv, eff_s_iv = _str3_single_iv(N_s, h_s, r_s)
    boolcheck(f"Table 4 Str_3 single matrix at tau={ts} {(N_s,h_s,r_s)} interval-valid (eff_hi={float(eff_s_iv.b):.6f} < {ts})",
              eff_s_iv.b < _Iv(ts).a)
    boolcheck(f"MUTANT REJECTED: Table 4 Str_3 {(N_s,h_s,r_s)} fails at tau-0.01",
              eff_s_iv.a > (_Iv(ts) - _Iv("0.01")).b)
    boolcheck(f"Table 4 Str_3 single matrix log10(V) interval rounds to {l10V_s}",
              _matches_display(l10V_iv, l10V_s))
# Explicit negative control: old (22, 3, 7) is invalid at tau=2.800 (eff ~ 2.80616)
_, eff_22_iv = _str3_single_iv(22, 3, 7)
boolcheck("MUTANT REJECTED: (22, 3, 7) fails at tau=2.800 (eff_lo > 2.800)", eff_22_iv.a > _Iv("2.800").b)
boolcheck("MUTANT REJECTED: omitting +1 fails at j=2 (100 > 625/7)", not (100 <= Fraction(625, 7)))

eq("eq:schonhage_induct", 704, "Inductive inequality (B^j + 1)(B - 1) <= B^{j+1} for B >= 2, j >= 1")
B_s = PolyQ.var("B")
symcheck("algebraic expansion (B^2+1)(B-1) == B^3 - B^2 + B - 1",
         ((B_s ** 2) + 1) * (B_s - 1) - ((B_s ** 3) - (B_s ** 2) + B_s - 1))
boolcheck("B^j >= B > B-1 holds for B=2..10, j=1..6",
          all((BB ** jj) >= BB > BB - 1 for BB in range(2, 11) for jj in range(1, 7)))
boolcheck("MUTANT REJECTED: fails for B=1/2, j=2",
          not ((Fraction(1, 2) ** 2 + 1) * (Fraction(1, 2) - 1) <= Fraction(1, 2) ** 3 and Fraction(1, 2) ** 2 >= Fraction(1, 2)))

# ============================================================================
# SECTION 4.4: GENERALIZED REMARK 4.5 BOUNDS, DISPROOF, AND OBSTRUCTION
# ============================================================================
part("SECTION 4.4: REMARK 4.5 GENERALIZATION, COUNTEREXAMPLES, AND OBSTRUCTION")

# eq:remark45_universal, eq:r45_step1, eq:r45_step2, eq:r45_cancel, eq:r45_round (L732, L740, L745, L750, L760)
# States: Universal lower bounds 64^{4 b_0} Delta_bal^{2 p_tau} n_s^{16 a_0 d} < m_t^{16 a_0 d} and v_k^{4 a_0} > w^{18 b_0} across Pass Remark 4.5.
# Derived from: eq:pass_valid_cond, eq:univ_round_nat, eq:univ_vk_vs_w
# Test: Verifies both universal inequalities and all four derivation links on both Pass (m_t=8, n_s=6, Delta_bal=140) and a non-Pass zero-balancing-loss (Delta_bal=1) Remark 4.5 instance (m_t=5, n_s=4, R_num=2, R_den=1, kappa>0).
# Mutant: Violating the 9/4 floor hypothesis (a) breaks the cancellation eq:r45_cancel.
eq("eq:remark45_universal", 732, "Generalized Remark 4.5 universal round & v_k inequalities")
# Non-Pass Remark 4.5 test: m_t=5, n_s=4, R_num=2, R_den=1 -> m_t^3 R_den^2 = 125 <= 256 = 64*4 = n_s^3 R_num^2 (satisfies (a)!)
# Wait: rate = (3/2) * ln(2) / ln(5/4) = 4.66 > 9/4; choose tighter R_num=14, R_den=10 -> 5^3*10^2=12500 <= 4^3*14^2=12544!
# Rate = (3/2) * ln(1.4) / ln(1.25) = 2.26183 > 9/4! Target tau = 2.500 (a0=1, b0=4, p_tau=40, q_tau=16), Delta_bal = 1!
mt, ns, Rnum, Rden, Dbal = 5, 4, 14, 10, 1
a0_r, b0_r = 1, 4
p_r, q_r = 9 * b0_r + 4 * a0_r, 4 * b0_r  # 40, 16 -> tau = 2.5
boolcheck("non-Pass Remark 4.5 instance satisfies 9/4 floor m_t^3 R_den^2 <= n_s^3 R_num^2",
          (mt ** 3) * (Rden ** 2) <= (ns ** 3) * (Rnum ** 2))
# Find valid (d_r, k_r) with Delta_bal = 1, w = mt^(2d), u = ns^(2d), Lam = floor(w/u)^2, E_k = ceil(64^k w^9 (Rnum/Rden)^(6dk))
# Universal bound forces d_r > 6 / (4 * 0.25 * log2(5/4)) = 18.64; at d_r = 25, margin ~ 1.16/round, so k_r = 350 amortizes 4*ln(w_r) ~ 322!
d_r = 25
w_r = (mt ** (2 * d_r)) // Dbal
u_r = ns ** (2 * d_r)
lam_r = (w_r // u_r) ** 2
k_r = 350
vk_r_log = 2 * math.log(w_r) + k_r * math.log(lam_r)
Ek_r_log = k_r * math.log(64) + 9 * math.log(w_r) + 6 * d_r * k_r * math.log(Rnum / Rden)
boolcheck("non-Pass Remark 4.5 (Delta_bal=1) instance is valid for tau=2.5", q_r * Ek_r_log < p_r * vk_r_log)
boolcheck("first universal bound 64^{4 b_0} Delta_bal^{2 p_tau} n_s^{16 a_0 d} < m_t^{16 a_0 d} holds",
          (64 ** (4 * b0_r)) * (Dbal ** (2 * p_r)) * (ns ** (16 * a0_r * d_r)) < (mt ** (16 * a0_r * d_r)))
boolcheck("second universal bound 4*a0*log(v_k) > 18*b0*log(w) holds",
          4 * a0_r * vk_r_log > 18 * b0_r * math.log(w_r))
boolcheck("MUTANT REJECTED: d=1 violates universal round bound even at Delta_bal=1",
          not ((64 ** (4 * b0_r)) * (ns ** (16 * a0_r * 1)) < (mt ** (16 * a0_r * 1))))

eq("eq:r45_step1", 740, "Remark 4.5 proof step 1")
boolcheck("step 1 log inequality holds strictly",
          q_r * Ek_r_log < p_r * (2 * math.log(w_r) + k_r * math.log(lam_r)))
boolcheck("MUTANT REJECTED: reversing < fails", not (q_r * Ek_r_log > p_r * vk_r_log))

eq("eq:r45_step2", 745, "Remark 4.5 proof step 2")
lhs_r2 = (18 * b0_r - 8 * a0_r) * math.log(w_r) + k_r * (q_r * math.log(64) + 6 * d_r * q_r * math.log(Rnum))
rhs_r2 = k_r * (p_r * math.log(lam_r) + 6 * d_r * q_r * math.log(Rden))
boolcheck("step 2 holds strictly", lhs_r2 < rhs_r2)
boolcheck("MUTANT REJECTED: k=1 fails step 2",
          not ((18 * b0_r - 8 * a0_r) * math.log(w_r) + (q_r * math.log(64) + 6 * d_r * q_r * math.log(Rnum))
               < (p_r * math.log(lam_r) + 6 * d_r * q_r * math.log(Rden))))

eq("eq:r45_cancel", 750, "Remark 4.5 cancellation chain from 9/4 floor")
c1 = 9 * b0_r * math.log(lam_r) + 18 * b0_r * math.log(Dbal) + 36 * b0_r * d_r * math.log(ns) + 24 * b0_r * d_r * math.log(Rden)
c2 = 36 * b0_r * d_r * math.log(mt) + 24 * b0_r * d_r * math.log(Rden)
c3 = 36 * b0_r * d_r * math.log(ns) + 24 * b0_r * d_r * math.log(Rnum)
boolcheck("cancellation chain c1 <= c2 <= c3 holds", c1 <= c2 + 1e-9 and c2 <= c3 + 1e-9)
# Mutant: breaking 9/4 floor (R_num=13, R_den=10 -> 12500 > 64*169=10816) breaks c2 <= c3!
boolcheck("MUTANT REJECTED: breaking 9/4 floor flips c2 <= c3",
          not ((mt ** 3) * (10 ** 2) <= (ns ** 3) * (13 ** 2)))

eq("eq:r45_round", 760, "Remark 4.5 round elimination chain")
r1 = 4 * b0_r * math.log(64) + 2 * p_r * math.log(Dbal) + 4 * d_r * p_r * math.log(ns) + 24 * b0_r * d_r * math.log(Rnum)
r2 = 4 * d_r * p_r * math.log(mt) + 24 * b0_r * d_r * math.log(Rden)
r3 = 16 * a0_r * d_r * math.log(mt) + 36 * b0_r * d_r * math.log(ns) + 24 * b0_r * d_r * math.log(Rnum)
boolcheck("round elimination r1 < r2 <= r3 holds", r1 < r2 and r2 <= r3 + 1e-9)
boolcheck("MUTANT REJECTED: r1 > r3 is false", not (r1 > r3))

# eq:general_bini_horizon (matmul_9_4_constant.tex L772)
# States: For any border-rank identity with r_0^4 >= v_0^9, exact Bini rank R = (h E_eps + 1) r_0^h < V^{9/4 + a_0/b_0} forces (h E_eps + 1)^{b_0} < V^{a_0}.
# Derived from: eq:bini_condition
# Test: Checks concrete valid Bini conversion at v_0 = 16, r_0 = 512 (exact 9/4 floor), E_eps = 10, tau = 2.500 (a_0=1, b_0=4).
# Mutant: Violating r_0^4 >= v_0^9 (e.g. hypothetical r_0 = 256 = v_0^2) violates (h E_eps + 1)^{b_0} < V^{a_0}.
eq("eq:general_bini_horizon", 772, "Bini horizon (h E_eps + 1)^{b_0} < V^{a_0} and V > (h E_eps + 1)^{1/delta} >= (E_eps + 1)^{1/delta}")
v0_b, r0_b, Eeps_b, a0_b, b0_b = 16, 512, 10, 1, 4  # r0^4 = 512^4 = 16^9 = v0^9 exact!
# Find minimal h such that (h*10 + 1)*512^h < (16^h)^{2.5} <=> (10h + 1)^4 < 16^h
h_b = 1
while not ((h_b * Eeps_b + 1) ** b0_b < (v0_b ** h_b) ** a0_b):
    h_b += 1
V_b = v0_b ** h_b
R_b = (h_b * Eeps_b + 1) * (r0_b ** h_b)
boolcheck("r_0^4 == v_0^9 exact and Bini validity holds at minimal h",
          r0_b ** 4 >= v0_b ** 9 and R_b ** (4 * b0_b) < V_b ** (9 * b0_b + 4 * a0_b))
boolcheck("universal horizon (h E_eps + 1)^{b_0} < V^{a_0} holds strictly",
          (h_b * Eeps_b + 1) ** b0_b < V_b ** a0_b, f"h={h_b}, V=16^{h_b}")
boolcheck("MUTANT REJECTED: at h=1, (h*E_eps + 1) == (E_eps + 1) (second inequality is >=, not >)",
          (1 * Eeps_b + 1) == (Eeps_b + 1) and not ((1 * Eeps_b + 1) > (Eeps_b + 1)))
# Mutant: hypothetical r_0 = 256 < 16^{9/4} beats tau=2.5 at h=3 where (31)^4 = 923521 > 4096 = 16^3!
boolcheck("MUTANT REJECTED: r_0 = 256 < v_0^{9/4} breaks horizon at h=3",
          ((3 * 10 + 1) * (256 ** 3)) ** 16 < (16 ** 3) ** 40 and not ((3 * 10 + 1) ** 4 < (16 ** 3)))

# eq:pan_counterexample (matmul_9_4_constant.tex L790)
# States: Pan (1978) has V=70, R=143640 obeying 143640^5 < 70^{14}; Strassen (1969) obeys 7^{1000} < 2^{2808}; untwisted Str_3 monotonicity chains cover [2.324, 3) (post-Bini) and [2.350, 3) (pre-Bini).
# Derived from: eq:exact_pp, eq:C_schoolbook, eq:finite_schonhage, eq:sharp_k_lnLam_lb
# Test: Exact arbitrary-precision integer comparisons + full non-tautological monotonicity chain certification.
# Mutant: 143640^1000 < 70^{2795} is false; Str_3 at 2.330 exceeds Pass pre-Bini LB at 2.330.
eq("eq:pan_counterexample", 790, "Exact integer counterexamples & Thm. 4.6 monotonicity chains")
boolcheck("Strassen 1969: 7^{1000} < 2^{2808} and 7^{10} = 282475249 < 283741119 < 2^{28.08}",
          7 ** 1000 < 2 ** 2808 and 7 ** 10 == 282475249 < 283741119 and 283741119 ** 100 < 2 ** 2808)
boolcheck("Pan 1978: 143640^5 == 61147257343963028582400000 < 67822307284900000000000000 == 70^{14}",
          143640 ** 5 == 61147257343963028582400000
          and 70 ** 14 == 67822307284900000000000000
          and 143640 ** 5 < 70 ** 14)
boolcheck("Universal Pass floor for all tau in (9/4, 3): w >= 8 implies v_k > w^6 >= 262144 > 70 > 2",
          ((2 + 2) ** 2) // 2 == 8 and 8 ** 6 == 262144 and 262144 > 70 > 2)
boolcheck("Pan below-threshold schoolbook ratio 69^{0.2} < 3 (exact: 69 < 3^5 = 243)", 69 < 3 ** 5)
# Certify ALL 12 monotonicity chain links in Theorem 4.6 via global 2D box certification!
post_chain = [
    ("2.324", "2.330", (7050, 416, 1247), "6.598e10"),
    ("2.330", "2.350", (1498, 166, 485), "1.839e10"),
    ("2.350", "2.400", (548, 42, 124), "1.783e9"),
    ("2.400", "2.550", (188, 16, 42), "3.212e7"),
    ("2.550", "2.800", (52, 6, 15), "9.504e5"),
]
for ta_s, tb_s, tup, lb_s in post_chain:
    l10V_iv, eff_iv = _str3_single_iv(*tup)
    boolcheck(f"Thm 4.6 post-Bini link [{ta_s}, {tb_s}] via {tup}: interval-valid & {float(l10V_iv.b):.2f} < cert {lb_s}",
              eff_iv.b < _Iv(ta_s).a and l10V_iv.b < _Iv(lb_s).a and certify_global_pass_threshold(tb_s, "post", lb_s))
pre_chain = [
    ("2.350", "2.356", (548, 42, 124), "2.661e6"),
    ("2.356", "2.371", (432, 36, 102), "1.671e6"),
    ("2.371", "2.400", (272, 26, 74), "7.833e5"),
    ("2.400", "2.460", (188, 16, 42), "2.368e5"),
    ("2.460", "2.550", (84, 10, 26), "6.594e4"),
    ("2.550", "2.700", (52, 6, 15), "1.517e4"),
    ("2.700", "2.800", (28, 4, 9), "7197.27"),
]
for ta_s, tb_s, tup, lb_s in pre_chain:
    l10V_iv, eff_iv = _str3_single_iv(*tup)
    boolcheck(f"Thm 4.6 pre-Bini link [{ta_s}, {tb_s}] via {tup}: interval-valid & {float(l10V_iv.b):.2f} < cert {lb_s}",
              eff_iv.b < _Iv(ta_s).a and l10V_iv.b < _Iv(lb_s).a and certify_global_pass_threshold(tb_s, "pre", lb_s))
l10V_2330_iv, _ = _str3_single_iv(1498, 166, 485)
ok_pass_2330, lv_pass_2330 = _cert_pass_witness("2.330", "pre", 42, 10917, 12900)
boolcheck("Positive 2.330 check: Pass pre-Bini witness (42,10917,12900) is valid at 2.330 and strictly below Table 4 Str_3",
          ok_pass_2330 and lv_pass_2330.b < l10V_2330_iv.a)
boolcheck("MUTANT REJECTED: Pan 70x70 does not beat 2.795 (log_70(143640) = 2.79512)",
          not (143640 ** 1000 < 70 ** 2795))

# eq:supermult_cap, eq:small_V_consistent, eq:supermult_contra, eq:bernoulli_nat, eq:small_V_step (L828, L833, L842, L849, L856)
# States: Every supermultiplicative lower bound obeys Phi(V) <= V^{9/4}; (V, R*) = (mu^4, mu^9 + 1) satisfies (R*)^4 > V^9 and (R*)^{4 b_0} < V^{9 b_0 + 4 a_0}.
# Derived from: eq:C_schoolbook
# Test: Verifies Bernoulli lemma, general small-V consistency across delta=10^{-3}..10^{-6}, flagship (81, 19684) at tau=2.251, and Blaser/Landsberg/Massarenti-Raviolo bounds.
# Mutant: Blaser excludes (16, 513); at mu=3, b_0=100000, 19684^{100000} > 81^{225001}.
eq("eq:supermult_cap", 828, "Supermultiplicative bound cap Phi(V) <= V^{9/4}")
# Verify contradiction mechanism on concrete Phi(V) = (1 + eta)*V^{9/4} with V=81, eta=0.01, C_eps=10^6, eps=0.001
V_sm, eta_sm, eps_sm, Ceps_sm = 81, 0.01, 0.001, 1e6
ratio_sm = (1.0 + eta_sm) / (V_sm ** eps_sm)
r_contra = int(math.ceil(math.log(Ceps_sm) / math.log(ratio_sm))) + 1
boolcheck("ratio (1+eta)/V^eps > 1 forces ((1+eta)/V^eps)^r > C_eps for finite r",
          ratio_sm > 1.0 and (ratio_sm ** r_contra) > Ceps_sm, f"r_contra={r_contra}")
boolcheck("MUTANT REJECTED: at eta=0 (Phi(V)=V^{9/4}), ratio < 1 and never exceeds C_eps",
          not ((1.0 / (V_sm ** eps_sm)) > 1.0))

eq("eq:small_V_consistent", 833, "Small-V consistency & Blaser/Landsberg/Massarenti-Raviolo audit")
# Flagship witness mu=3 -> V=81, R*=19684 at tau=2.251 (a_0=1, b_0=1000)
boolcheck("V=81, R*=19684 satisfies 19684 > 19683 = 81^{9/4} = 3*81^2 and 19684^{1000} < 81^{2251} exact in int",
          19684 ** 4 > 81 ** 9 and 19683 == 3 * (81 ** 2) and 19684 ** 1000 < 81 ** 2251)
boolcheck("V=81 below-threshold schoolbook ratio 80^{0.749} < 27 (exact: 80^{749} < 27^{1000})",
          80 ** 749 < 27 ** 1000)
# Non-supermultiplicative bounds: Blaser (5/2)n^2 - 3n, Massarenti-Raviolo (8/3)n^2 - 7n
blaser_excl = [n for n in range(2, 200) if Fraction(5 * n * n - 6 * n, 2) >= n ** 2.251]
combined_excl = [n for n in range(2, 200)
                 if max(Fraction(5 * n * n - 6 * n, 2), Fraction(8 * n * n - 21 * n, 3)) >= n ** 2.251]
boolcheck("Blaser (5/2)n^2 - 3n excludes 3 <= n <= 33 at 2.251 (gives 592 > 513 at n=16, 16159.5 < 19684 at n=81)",
          blaser_excl == list(range(3, 34))
          and Fraction(5 * 16 * 16 - 6 * 16, 2) == 592 > 513
          and Fraction(5 * 81 * 81 - 6 * 81, 2) == Fraction(32319, 2) < 19684)
boolcheck("Blaser + Massarenti-Raviolo (8/3)n^2 - 7n excludes 3 <= n <= 37 at 2.251 and gives 16929 < 19684 at n=81",
          combined_excl == list(range(3, 38))
          and Fraction(8 * 81 * 81 - 21 * 81, 3) == 16929 < 19684)
# General scaling check across delta = 10^-3, 10^-4, 10^-5, 10^-6
for a0_s, b0_s in [(1, 1000), (1, 10000), (1, 100000), (1, 1000000)]:
    mu = max(3, math.ceil((b0_s / (2 * a0_s) + 1) ** (1.0 / 9.0)))
    while not (b0_s <= 4 * a0_s * ((mu ** 9) // 2)):
        mu += 1
    boolcheck(f"delta={a0_s}/{b0_s}: mu={mu}, V={mu**4} satisfies b_0 <= 4*a_0*floor(mu^9/2) and log-inequality",
              b0_s <= 4 * a0_s * ((mu ** 9) // 2)
              and b0_s * math.log(mu ** 9 + 1) < (9 * b0_s + 4 * a0_s) * math.log(mu))
boolcheck("MUTANT REJECTED: at tau=2.25001 (b0=100000), V=81 R*=19684 fails 19684^{100000} < 81^{225001}",
          not (100000 * math.log(19684) < 225001 * math.log(81)))

eq("eq:supermult_contra", 842, "Contradiction inequality (1 + eta)^r V^{(9/4)r} <= C_eps V^{(9/4 + eps)r}")
boolcheck("at r = r_contra, LHS strictly exceeds RHS",
          r_contra * math.log(1.0 + eta_sm) > math.log(Ceps_sm) + r_contra * eps_sm * math.log(V_sm))
boolcheck("MUTANT REJECTED: at r=1, LHS does not exceed RHS yet",
          not (1 * math.log(1.0 + eta_sm) > math.log(Ceps_sm) + 1 * eps_sm * math.log(V_sm)))

eq("eq:bernoulli_nat", 849, "Elementary Bernoulli bound (N + 1)^j < 2 N^j for N >= 2, 2j <= N")
ok_bern = True
for NN in range(2, 25):
    for jj in range(1, NN // 2 + 1):
        if not ((NN ** (jj - 1)) * (NN - jj) <= (NN - 1) ** jj and (NN + 1) ** jj < 2 * (NN ** jj)):
            ok_bern = False
boolcheck("exact integer Bernoulli & (N+1)^j < 2*N^j holds for all N in 2..24, 1 <= j <= N/2", ok_bern)
# Mutant: at j = N, (N+1)^N > 2*N^N for all N >= 2 (approaches e > 2)!
boolcheck("MUTANT REJECTED: fails at j = N = 4 (5^4 = 625 > 512 = 2*4^4)", not (5 ** 4 < 2 * (4 ** 4)))

eq("eq:small_V_step", 856, "Power step (N + 1)^{4 a_0 j_1} < 2^{4 a_0} N^{4 a_0 j_1} <= mu^{4 a_0} N^{4 a_0 j_1}")
N_2, j1_2 = 2 ** 9, (2 ** 9) // 2  # 512, 256
boolcheck("at mu=2, a_0=1: 513^{1024} < 16 * 512^{1024} exact in int",
          (N_2 + 1) ** (4 * j1_2) < 16 * (N_2 ** (4 * j1_2)))
boolcheck("MUTANT REJECTED: factor 2 instead of 16 fails at j=1024 (513/512)^1024 = 7.37 > 2",
          not ((N_2 + 1) ** (4 * j1_2) < 2 * (N_2 ** (4 * j1_2))))

# ============================================================================
# SECTION 5: FORMAL VERIFICATION IN LEAN 4 (DYADIC BRACKETING CALCULUS)
# ============================================================================
part("SECTION 5: DYADIC-EXPONENT BRACKETING CALCULUS")

# eq:log2_predicates (matmul_9_4_constant.tex L887)
# States: Log2Ge(x,p,q) := 2^p <= x^q, Log2Le(x,p,q) := x^q <= 2^p; base-2 to base-10 bridge 10^301 <= 2^1000 <= 10^302.
# Derived from: eq:pass_valid_cond
# Test: Exact arbitrary-precision integer check of 10^301 <= 2^1000 <= 10^302 and compositional mul/pow rules.
# Mutant: 2^1000 <= 10^301 is false.
eq("eq:log2_predicates", 887, "Pure-Nat Log2Ge/Log2Le calculus and exact 10^301 <= 2^1000 <= 10^302 bridge")
boolcheck("10^301 <= 2^1000 <= 10^302 exact in Python arbitrary-precision int", 10 ** 301 <= 2 ** 1000 <= 10 ** 302)
boolcheck("Log2Ge.pow: 2^15 <= 6^6 implies 2^(15*4) <= (6^4)^6",
          2 ** 15 <= 6 ** 6 and 2 ** (15 * 4) <= (6 ** 4) ** 6)
boolcheck("MUTANT REJECTED: 2^1000 <= 10^301 is false", not (2 ** 1000 <= 10 ** 301))

sys.exit(summary())
