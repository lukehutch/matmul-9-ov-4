# Citation Verification Record: `matmul_9_4_constant.tex`

This file is the primary-source verification record for `matmul_9_4_constant.tex` and `matmul_9_4_constant.bib`.
All metadata has been cross-checked against Crossref, OpenAlex, arXiv, or primary-source preprints read in full.
Quoted passages below are transcribed from the named primary source (with ASCII math normalization noted where extracted from PDF); paywalled historical articles (1969--1999) with no open full-text copy are explicitly marked `ABSTRACT-ONLY` or `METADATA-ONLY` without fabricated quotes.

## Pass2026
- **Verified authors**: Rafael Pass
- **Verified title**: Matrix Multiplication from Polynomial Packings: A Constructive Proof of \omega <= 9/4
- **Journal**: Preprint (2026)
- **DOI**: N/A
- **arXiv**: 2610.28627v2 [cs.CC] (30 Oct 2026)
- **Source URL**: https://arxiv.org/abs/2610.28627 (full text read from extracted PDF)
- **Claims supported**:
  - Claim: Explicit recursive integer-arithmetic algorithm attaining exponent 9/4 + gamma for every gamma > 0 via polynomial packings, with galactic hidden constants.
    Quote: "For every gamma > 0, there is an explicit recursive algorithm that, for every positive integer n, multiplies two n x n integer matrices with O(n^{9/4+gamma}) integer arithmetic operations. In particular, omega <= 9/4. The algorithm remains 'galactic': the constants hidden in the O(.) notation are enormous." (Sec. 1, Theorem 1.1, p. 1)
  - Claim: Pure (c+1)-for-c telescoping gives no saving in right-input coefficients, whereas taking c >= a + 2b - 1 opens a b-wide zero gap holding the middle product via a formal parameter epsilon.
    Quote: "This still gives no saving in the total number of right-input coefficients: c(b + 1) >= (c + 1)b. But notice the empty space in the combined output: AP_1 ends before position a + b - 1, while z^c AP_{c+1} starts at position c. Taking c >= a + 2b - 1 leaves at least b zero coefficient positions between them." (Sec. 1.1, p. 2)
  - Claim: Same-left primal packing (Theorem 3.1) packs c+1 full products and one middle product into c full products of length b+t when ct >= a+2b-1; dual packing follows from role exchange (23) (Lemma 2.8); 2d-variable amplification retains w = floor((c+2)^{2d}/(d+1)) balanced targets via Cauchy-Schwarz (Lemma 3.2, Claim 3.3).
    Quote: "For all integers a, b, c, t, p, q, r >= 1 with ct >= a + 2b - 1, there exists an SL-PP modulo epsilon of c + 1 copies of Full_{a,b}[p, q, r] and one middle product Mid_{a,b}[p, q, r] using c copies of Full_{a,b+t}[p, q, r]." (Sec. 3.1, Theorem 3.1, p. 12)
  - Claim: Removing the same-left requirement (Lemma 3.4) interpolates at i + epsilon*j using 2w-1 evaluation points and substitutes eta = epsilon^w into the inner packing.
    Quote: "The Lagrange formula for B'_i has denominators equal to nonzero rational multiples of epsilon^{w-1}. ... Before substituting the right inputs, the error is divisible by epsilon^w. Since it is linear in those inputs, their denominators cancel at most w - 1 powers of epsilon." (Sec. 3.3, Proof of Lemma 3.4, p. 15)
  - Claim: Composition modulo epsilon (Lemma 2.9) replaces epsilon by epsilon^{p_L + p_R + p_D + 1} in the inner packing; Bini conversion (Lemma 2.4) tensors h copies and interpolates at h d_epsilon + 1 nonzero rational points.
    Quote: "Modulo epsilon, choose nonnegative integers p_L, p_R, p_D such that epsilon^{p_L} E_1^L, epsilon^{p_R} E_1^R, and epsilon^{p_D} D_1 have entries polynomial in epsilon. First replace epsilon by epsilon^{p_L + p_R + p_D + 1} in (E_2, D_2)." (Appendix A.2, Proof of Lemma 2.9, p. 22)
  - Claim: Theorem 4.3 recurrence uses L_{j+1} = L_j + ceil((3 L_j - 1)/(c - 1)), v_k = w^2 Lambda^k, Lambda = floor(w/u)^2, and E_k = 64^k w^9 (2 L_k - 1)^{6d}, with asymptotic exponent threshold (3/2) log(1 + 3/(c-1)) / log(1 + 2/c).
    Quote: "The definition of compression rate and Lemma 2.3 therefore bound the scalar multiplications needed to evaluate all sources by E_k := w^3 v_k^3 / C_k = 64^k w^9 (2 L_k - 1)^{6d}" (Sec. 4.2, Proof of Theorem 4.3, p. 18)
  - Claim: Remark 4.5 generalizes the scheme to arbitrary symmetric shapes P_{a,b} (P_{b,a} =~ P_{a,b}, P_{1,1}[p,q,r] = <p,q,r>) with eff(P_{L,L}) = O(L^kappa), m targets from n sources, and length inflation rho, yielding exponent threshold (3 kappa log rho) / (2 log(m/n)).
    Quote: "Fix integers m > n >= 1 and constants rho > 1, C >= 0. Suppose eff(P_{L,L}) = O(L^kappa) for some fixed kappa > 0. ... Since eff(Q_{L,L}) = eff(P_{L,L})^{6d}, the same iteration as in Theorem 4.3 gives, for every tau > 3 kappa log rho / (2 log(m/n)), there exists an exact rational bilinear algorithm for matrix multiplication using r < v^tau scalar multiplications for some v >= 2." (Sec. 4.3, Remark 4.5, p. 19)
- **Status**: VERIFIED
- **Notes**: Full text read in-session. Exact formulas checked line by line against `verification/matmul_9_4_constant_check.py` and `verification/lean/`.

## OpenAI2026Upper
- **Verified authors**: OpenAI
- **Verified title**: An Upper Bound of 9/4 for the Matrix Multiplication Exponent
- **Journal**: Preprint, October 2, 2026
- **DOI**: N/A
- **arXiv**: N/A (official OpenAI preprint)
- **Source URL**: Local primary-source copy `openai_omega94_upper.pdf` / `openai_omega94_upper.txt`
- **Claims supported**:
  - Claim: Proved omega <= 9/4 over the complex numbers using tensor characters (Strassen's asymptotic spectrum) and a 5M-copy finite Fourier shared-leg separation degeneration, without specifying a competitive finite matrix size.
    Quote: "Theorem 1.1. For every epsilon > 0, two n x n complex matrices can be multiplied using O_epsilon(n^{9/4+epsilon}) arithmetic operations. In particular, omega <= 9/4." / "Theorem 1.1 concerns the asymptotic arithmetic exponent; its proof does not specify a competitive finite matrix size." (Sec. 1, pp. 1--2)
  - Claim: Proposition 3.1 separates M matched blocks sharing one leg using L = 5M source copies, Fourier condition u - v + 2(g - h) = 0, quadratic weights (g - h)^2, and states an epsilon-degree upper bound of (M - 1)^2.
    Quote: "Since |u - v + 2(g - h)| <= 3(M - 1) < L, precisely the terms satisfying u - v + 2(g - h) = 0 (3.2) survive. ... On every surviving term, (3.2) gives g^2 + hu - h^2 - hv = (g - h)^2 >= 0. ... The transformed tensor has degree at most (M - 1)^2, even though some individual variable weights are negative." (Sec. 3, Proof of Proposition 3.1, pp. 4--5)
- **Status**: VERIFIED
- **Notes**: Full text read in-session. Proposition 3.1 equation (3.2) directly yields our tighter exact bound floor((M - 1)/2)^2.

## OpenAI2026Lower
- **Verified authors**: OpenAI
- **Verified title**: The matrix multiplication exponent is nine fourths
- **Journal**: Preprint, November 24, 2026
- **DOI**: N/A
- **arXiv**: N/A (official OpenAI preprint)
- **Source URL**: Local primary-source copy `openai_omega94.pdf` / `openai_omega94.txt`
- **Claims supported**:
  - Claim: Reports a matching lower bound omega_F = 9/4 over every field F for formal arithmetic circuits, with geometric border rank at least n^{9/4} and dual rectangular exponent bounded by 1/2 <= alpha_F <= 2/3.
    Quote: "Theorem 1.1. Over every field F, the exponent of square matrix multiplication is omega_F = 9/4." / "Corollary 1.2. For every n >= 2 and every field F, the geometric border rank of T_n is at least n^{9/4}, and the asymptotic rank of T_n over F equals n^{9/4}." / "Over every field, 1/2 <= alpha_F <= 2/3." (Sec. 1, pp. 1--2)
- **Status**: VERIFIED
- **Notes**: Full text read in-session. Cited explicitly as an unrefereed companion preprint where referenced for the matching lower bound and alpha_F <= 2/3 context.

## Lu2026
- **Verified authors**: Houxi Lu (Houxi L\"u)
- **Verified title**: Polynomial Separation of a Shared Tensor Leg and Matrix Multiplication in Arbitrary Characteristic
- **Journal**: Preprint (2026)
- **DOI**: N/A
- **arXiv**: 2610.18914v1 [cs.CC] (12 Oct 2026)
- **Source URL**: https://arxiv.org/abs/2610.18914 (full text read from extracted PDF)
- **Claims supported**:
  - Claim: Replaces OpenAI's 5M-copy Fourier separation with a characteristic-free polynomial substitution t = a_h + epsilon*u mod u^n using M + n - 1 copies (2M - 1 for n = M) and linear epsilon-degree at most min(M - 1, n - 1).
    Quote: "If M tensor blocks have a common first space and independent matched sectors on their other two spaces, then M + n - 1 copies of their matched sum degenerate to the full direct sum of the blocks, each tensored with an n-dimensional dot product. For n = M, this reduces the number of source copies from 5M to 2M - 1." (Abstract, p. 1)
    Quote: "The family Phi has degree at most min(M - 1, n - 1) in epsilon, since powers u^n and higher vanish in J." (Sec. 2, Proof of Proposition 2.1, p. 3)
- **Status**: VERIFIED
- **Notes**: Full text read in-session.

## Uznanski2026
- **Verified authors**: Przemyslaw Uznanski (Przemys{\l}aw Uzna{\'n}ski)
- **Verified title**: Rectangular matrix multiplication from polynomial products
- **Journal**: Preprint (2026)
- **DOI**: N/A
- **arXiv**: 2610.10494v2 [cs.DS] (11 Oct 2026)
- **Source URL**: https://arxiv.org/abs/2610.10494 (full text read from extracted PDF)
- **Claims supported**:
  - Claim: Extends polynomial-product degenerations to rectangular matrix multiplication, proving omega(1, k, 1) <= 2 for 0 <= k <= 1/2 and omega(1, k, 1) <= 1 + k + 1/(4k) for k >= 1/2 (hence alpha >= 1/2), and improves the Fourier shared-leg copy count from 5M to 2M (with epsilon-degree (M - 1)^2).
    Quote: "In this note, we extend the matrix-multiplication analysis in [9] to rectangular products and prove omega(1, k, 1) <= 2 (0 <= k <= 1/2), 1 + k + 1/(4k) (k >= 1/2). In particular, omega(1, 1/2, 1) = 2 and the dual exponent satisfies alpha >= 1/2." (Abstract, p. 1)
- **Status**: VERIFIED
- **Notes**: Full text read in-session.

## Amanov2026
- **Verified authors**: Alimzhan Amanov, Maxim van den Berg, Jeroen Zuiddam
- **Verified title**: Multiplying matrices via polynomials: exposition and barriers
- **Journal**: Preprint (2026)
- **DOI**: N/A
- **arXiv**: 2610.30054v1 [cs.CC] (21 Oct 2026)
- **Source URL**: https://arxiv.org/abs/2610.30054 (full text read from extracted PDF)
- **Claims supported**:
  - Claim: Proves omega_F <= 9/4 and rectangular bounds over every field F, and establishes an operational barrier showing that the current polynomial degeneration ingredients and combination rules cannot improve below 9/4 or raise alpha above 1/2.
    Quote: "We moreover prove an operational barrier (which can be thought of as coming from an operational asymptotic spectrum) showing that the current analysis of all these upper bounds on omega_F and omega_F(a, b, c) is optimal and that in fact the current degeneration ingredients cannot improve the bounds." (Abstract, p. 1)
- **Status**: VERIFIED
- **Notes**: Full text read in-session.

## Li2026
- **Verified authors**: Baitian Li
- **Verified title**: Semidirect sums of tensors and the matrix multiplication exponent
- **Journal**: Preprint (2026)
- **DOI**: N/A
- **arXiv**: 2611.04175v1 [cs.CC] (3 Nov 2026)
- **Source URL**: https://arxiv.org/abs/2611.04175 (full text read from extracted PDF)
- **Claims supported**:
  - Claim: Formulates shared-leg separation as an untwisting lemma for semidirect sums of tensors, resolving the index-role "schizophrenia" of the Strassen tensor Str_q (border rank q + 1) and yielding omega <= 3 log(q + 1) / log(2q), which at q = 3 gives omega < 2.322 (3 log(4)/log(6) < 2.32112).
    Quote: "We argue that the heart of these preprints is a new technique, which we formulate as the untwisting lemma for semidirect sums of tensors." (Abstract, p. 1)
    Quote: "The tensor Str_q has minimal border rank q + 1... Taking q = 3, this would give omega < 2.322." (Sec. 1.1, pp. 2--3)
- **Status**: VERIFIED
- **Notes**: Full text read in-session.

## Dogan2026
- **Verified authors**: Mahmut Levent Dogan (M. Levent Do{\u{g}}an), Vladimir Lysikov, Keiya Sakabe, Michael Walter
- **Verified title**: Tensor value and the 9/4 bound for matrix multiplication
- **Journal**: Preprint (2026)
- **DOI**: N/A
- **arXiv**: 2611.09716v1 [cs.CC] (6 Nov 2026)
- **Source URL**: https://arxiv.org/abs/2611.09716 (full text read from extracted PDF)
- **Claims supported**:
  - Claim: Proves omega_F <= 9/4 over every field using fractional symmetrized tensor value without spectral points, and shows that superadditivity on partially direct sums immediately yields omega <= 3 log(4)/log(6) < 2.32112 from Strassen's tensor S_3.
    Quote: "Taking n = 3 gives omega <= 3 log(4) / log(6) < 2.32112, improving on the upper bounds obtained using the Coppersmith-Winograd tensor" (Sec. 1.2, p. 2)
- **Status**: VERIFIED
- **Notes**: Full text read in-session.

## ADWXXZ2025
- **Verified authors**: Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu, Renfei Zhou
- **Verified title**: More Asymmetry Yields Faster Matrix Multiplication
- **Journal**: Proceedings of the 2025 Annual ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 2005-2039 (2025)
- **DOI**: 10.1137/1.9781611978322.63
- **arXiv**: 2404.16349v3
- **Source URL**: paperclip `/papers/arx_2404.16349/content.lines` and OpenAlex `10.1137/1.9781611978322.63`
- **Claims supported**:
  - Claim: Refined the asymmetric laser method on the Coppersmith-Winograd tensor to establish omega < 2.371339.
    Quote: "The method yields a new bound on the square matrix multiplication exponent omega < 2.371339, improved from the previous bound of omega < 2.371552." (Abstract, `arx_2404.16349/content.lines` L4--L6)
- **Status**: VERIFIED
- **Notes**: Verified via paperclip full text and OpenAlex metadata.

## DEK2026
- **Verified authors**: Emilien Dupont, Marvin Eisenberger, Borislav Kozlovskii, Abbas Mehrabian, Francisco J. R. Ruiz, Abigail See, Renfei Zhou, Josh Alman, Virginia Vassilevska Williams, Matej Balog
- **Verified title**: Improving the matrix multiplication exponent with modern optimization and AlphaEvolve
- **Journal**: Preprint (2026)
- **DOI**: N/A
- **arXiv**: 2608.16884v1 [cs.DS]
- **Source URL**: paperclip `/papers/arx_2608.16884/content.lines` and `export.arxiv.org`
- **Claims supported**:
  - Claim: Achieved omega < 2.371177 via gradient-based optimization and AlphaEvolve on combination-loss laser-method trees.
    Quote: "Our combined approach yields an upper bound of omega < 2.371177, improving the previous best bound of 2.371339." (Abstract, `arx_2608.16884/content.lines` L4)
- **Status**: VERIFIED
- **Notes**: Verified via paperclip full text and arXiv metadata.

## BLS2003
- **Verified authors**: Alin Bostan, Gregoire Lecerf, Eric Schost
- **Verified title**: Tellegen's principle into practice
- **Journal**: Proceedings of the 2003 International Symposium on Symbolic and Algebraic Computation (ISSAC), pp. 37-44 (2003)
- **DOI**: 10.1145/860854.860870
- **arXiv**: N/A
- **Source URL**: https://specfun.inria.fr/bostan/publications/BoLeSc03.pdf (author institutional copy)
- **Claims supported**:
  - Claim: Formalizes transposed polynomial multiplication as the middle product via Tellegen's transposition principle.
    Quote: "The transposition principle, also called Tellegen's principle, is a set of transformation rules for linear programs. ... The above formula explains why the transposed multiplication is also called the middle product [9]." (Abstract, p. 37; Sec. 4, p. 40)
- **Status**: VERIFIED
- **Notes**: Full text downloaded from author's INRIA webpage and cross-checked with OpenAlex metadata.

## Schonhage1981
- **Verified authors**: Arnold Schonhage (Arnold Sch{\"o}nhage)
- **Verified title**: Partial and Total Matrix Multiplication
- **Journal**: SIAM Journal on Computing, Vol. 10, No. 3, pp. 434-455 (1981)
- **DOI**: 10.1137/0210032
- **arXiv**: N/A
- **Source URL**: Crossref & OpenAlex `https://api.openalex.org/works/https://doi.org/10.1137/0210032` (paywalled full text; publisher abstract retrieved)
- **Claims supported**:
  - Claim: Established the asymptotic sum inequality converting border-rank bounds for direct sums of partial matrix multiplication tensors into bounds on omega.
    Quote: "Here the new techniques and recent results are presented, based upon the notion of approximate rank and the observation that certain patterns of partial matrix multiplication (some of the entries of the matrices may be zero) can efficiently be utilized to perform multiplication of large total matrices." (OpenAlex publisher abstract)
- **Status**: ABSTRACT-ONLY (Crossref & OpenAlex metadata verified; paywalled SIAM full text)
- **Notes**: Standard historical citation; only the textbook asymptotic sum inequality attribution is cited.

## Strassen1988
- **Verified authors**: Volker Strassen
- **Verified title**: The asymptotic spectrum of tensors
- **Journal**: Journal fur die reine und angewandte Mathematik (Crelle's Journal), Vol. 384, pp. 102-152 (1988)
- **DOI**: 10.1515/crll.1988.384.102
- **arXiv**: N/A
- **Source URL**: OpenAlex `https://api.openalex.org/works/https://doi.org/10.1515/crll.1988.384.102` (paywalled full text; publisher abstract retrieved)
- **Claims supported**:
  - Claim: Introduced the asymptotic spectrum of tensors, associating a compact Hausdorff space of multiplicative, additive, restriction-monotone functionals to bilinear maps.
    Quote: "A un ensemble X d'informations bilineaires entre des espaces vectoriels de dimension finie on associe un espace de Hausdorff compact Delta(X) avec une application phi de X a l'anneau des fonctions reelles continues sur Delta(X), appele le spectre asymptotique de X" (OpenAlex publisher abstract)
- **Status**: ABSTRACT-ONLY (OpenAlex metadata verified; paywalled De Gruyter full text)
- **Notes**: Standard historical citation for Strassen's asymptotic spectrum framework.

## Strassen1969
- **Verified authors**: Volker Strassen
- **Verified title**: Gaussian elimination is not optimal
- **Journal**: Numerische Mathematik, Vol. 13, No. 4, pp. 354-356 (1969)
- **DOI**: 10.1007/BF02165411
- **arXiv**: N/A
- **Source URL**: OpenAlex `https://api.openalex.org/works/https://doi.org/10.1007/BF02165411` (EuDML/Springer paywalled full text; verified metadata)
- **Claims supported**:
  - Claim: Established the 2 x 2 seven-multiplication bilinear identity yielding recursive matrix multiplication with exponent log_2(7) < 2.81.
- **Status**: METADATA-ONLY (OpenAlex & EuDML verified; cited strictly for the standard 2 x 2 seven-product exponent log_2(7), also cross-quoted verbatim in ADWXXZ2025 L14 and Pass2026 p. 1)
- **Notes**: No fabricated quote; channels tried: paperclip, Unpaywall, OpenAlex.

## Pan1978
- **Verified authors**: Victor Ya. Pan
- **Verified title**: Strassen's algorithm is not optimal: Trilinear technique of aggregating, uniting and canceling for constructing fast algorithms for matrix operations
- **Journal**: Proceedings of the 19th Annual Symposium on Foundations of Computer Science (FOCS), pp. 166-176, IEEE (1978)
- **DOI**: 10.1109/SFCS.1978.34
- **arXiv**: N/A
- **Source URL**: OpenAlex `https://api.openalex.org/works/https://doi.org/10.1109/sfcs.1978.34`
- **Claims supported**:
  - Claim: Constructed an explicit bilinear algorithm multiplying 70 x 70 matrices in 143,640 scalar multiplications, achieving exponent log_70(143,640) < 2.796 < 2.800 (exact: 143,640^5 < 70^14).
- **Status**: METADATA-ONLY (the 1978 IEEE FOCS article is paywalled; Pan's 2018 author retrospective `Pan2018` explicitly corroborates the 70 x 70 side and 143,640 rank, and the rank-exponent inequality 143,640^5 < 70^14 is recomputed independently)
- **Notes**: No fabricated quote; channels tried: paperclip, Crossref, OpenAlex.

## Pan2018
- **Verified authors**: Victor Y. Pan
- **Verified title**: Fast Feasible and Unfeasible Matrix Multiplication
- **Journal**: Preprint (2018)
- **DOI**: N/A
- **arXiv**: 1804.04102 [cs.DS]
- **Source URL**: https://arxiv.org/abs/1804.04102 (submitted LaTeX source read via allpapers)
- **Claims supported**:
  - Claim: Author retrospective confirming that Pan (1978) constructed an explicit bilinear algorithm of rank 143,640 for 70 x 70 matrix multiplication.
    Quote: "was decreased only in 1978, when the paper [P78] presented a bilinear algorithm of rank 143,640 for 70 x 70 MM. This implied the exponent omega = log_70 (143,640) < 2.7962" (`1804.04102.tex`, lines 921--924)
- **Status**: VERIFIED
- **Notes**: Full submitted arXiv LaTeX source retrieved and checked.

## Blaser1999
- **Verified authors**: Markus Blaser (Markus Bl{\"a}ser)
- **Verified title**: A 5/2 n^2-lower bound for the rank of n x n-matrix multiplication over arbitrary fields
- **Journal**: Proceedings of the 40th Annual Symposium on Foundations of Computer Science (FOCS), pp. 45-50, IEEE (1999)
- **DOI**: 10.1109/SFFCS.1999.814576
- **arXiv**: N/A
- **Source URL**: Crossref `https://doi.org/10.1109/SFFCS.1999.814576`
- **Claims supported**:
  - Claim: Established the field-independent lower bound R(<n, n, n>) >= (5/2) n^2 - 3n on the bilinear rank of n x n matrix multiplication.
- **Status**: METADATA-ONLY (paywalled IEEE FOCS full text; the exact formula (5/2) n^2 - 3n over every field is corroborated verbatim in `Landsberg2014` (`1206.1530.tex`, Abstract L68 & Sec. 1 L124), `MassarentiRaviolo2013` (`1211.6320.tex`, Abstract L200 & Intro L217), and `OpenAI2026Lower` Sec. 1)
- **Notes**: No fabricated quote; channels tried: paperclip, Crossref, OpenAlex.

## Landsberg2014
- **Verified authors**: J. M. Landsberg
- **Verified title**: New lower bounds for the rank of matrix multiplication
- **Journal**: SIAM Journal on Computing, Vol. 43, No. 1, pp. 144-149 (2014)
- **DOI**: 10.1137/120880276
- **arXiv**: 1206.1530 [cs.CC]
- **Source URL**: https://arxiv.org/abs/1206.1530 (submitted LaTeX source read via allpapers)
- **Claims supported**:
  - Claim: Over the complex numbers, for every integer 1 <= p <= n - 1, R(<n, n, n>) >= (3 - 1/(p + 1)) n^2 - (1 + 2p binom(2p, p - 1)) n, improving Blaser's (5/2) n^2 - 3n bound for all n > 84.
    Quote: "More precisely, for any integer p <= n - 1 the rank is at least (3 - 1/(p + 1)) n^2 - (1 + 2p binom(2p, p - 1)) n. The previous lower bound, due to Blaser, was (5/2) n^2 - 3n (the case p = 1). The new bounds improve Blaser's bound for all n > 84." (`1206.1530.tex`, Abstract L66--70; Theorem 1.2 L116--124)
- **Status**: VERIFIED
- **Notes**: Full submitted arXiv LaTeX source retrieved and checked.

## MassarentiRaviolo2013
- **Verified authors**: Alex Massarenti, Emanuele Raviolo
- **Verified title**: On the rank of n x n matrix multiplication
- **Journal**: Preprint (2013; corrected arXiv:1211.6320v2)
- **DOI**: N/A (see published corrigendum `MassarentiRaviolo2014`, DOI 10.1016/j.laa.2013.12.009)
- **arXiv**: 1211.6320v2 [cs.CC]
- **Source URL**: https://arxiv.org/abs/1211.6320v2 (submitted LaTeX source read via allpapers)
- **Claims supported**:
  - Claim: Over C, establishes R(<n, n, n>) >= (8/3) n^2 - 7n (at p = 2), matching Blaser's (5/2) n^2 - 3n at n = 24 and strictly improving it for every n > 24 (excluding 7 <= n <= 37 at tau = 2.251 on its own, and 3 <= n <= 37 when combined with Blaser's bound, while giving 16,929 < 19,684 at n = 81).
    Quote: "Finally, for p = 2, with a sligtly different strategy we menage to obtain the lower bound (8/3) n^2 - 7n which improves Blaser's bound for any n >= 24." (`1211.6320.tex`, Abstract L200; Remark 3.4 L638--642)
- **Status**: VERIFIED
- **Notes**: Full submitted arXiv LaTeX source (`1211.6320v2`, primary class `cs.CC`) retrieved and checked.

## MassarentiRaviolo2014
- **Verified authors**: Alex Massarenti, Emanuele Raviolo
- **Verified title**: Corrigendum to "The rank of n x n matrix multiplication is at least 3n^2 - 2\sqrt{2}n^{3/2} - 3n" [Linear Algebra Appl. 438 (11) (2013) 4500-4509]
- **Journal**: Linear Algebra and its Applications, Vol. 445, pp. 369-371 (2014)
- **DOI**: 10.1016/j.laa.2013.12.009
- **arXiv**: N/A (companion to arXiv:1211.6320v2)
- **Source URL**: https://doi.org/10.1016/j.laa.2013.12.009 (open-access PDF retrieved and checked)
- **Claims supported**:
  - Claim: Withdraws the uncorrected 2013 LAA bound inherited from the first preprint version of Landsberg and states the corrected bound rk(M_{n,n,n}) >= (8/3) n^2 - 7n (Eq. (0.3), p. 370).
    Quote: "The main result in [3] is incorrect, because of a mistake in the first version of [2], which was propagated in our paper. For the full and correct version of our paper see [4]." (p. 369; Eq. (0.3), p. 370)
- **Status**: VERIFIED
- **Notes**: Published corrigendum PDF verified directly.

## Robbins1955
- **Verified authors**: Herbert Robbins
- **Verified title**: A Remark on Stirling's Formula
- **Journal**: The American Mathematical Monthly, Vol. 62, No. 1, pp. 26-29 (1955)
- **DOI**: 10.2307/2308012
- **arXiv**: N/A
- **Source URL**: https://dornsife.usc.edu/sergey-lototsky/wp-content/uploads/sites/211/2024/02/Stirling-Robbins.pdf (original journal scan checked)
- **Claims supported**:
  - Claim: For every positive integer n >= 1, n! = sqrt(2*pi) n^{n+1/2} e^{-n} e^{r_n} with 1/(12n + 1) < r_n < 1/(12n) (Eqs. (1)-(2), p. 26).
    Quote: "We shall prove Stirling's formula by showing that for n = 1, 2, ... (1) n! = sqrt(2*pi) n^{n+1/2} e^{-n} e^{r_n} where r_n satisfies the double inequality (2) 1/(12n+1) < r_n < 1/(12n)." (p. 26)
- **Status**: VERIFIED
- **Notes**: Original journal article verified directly (pp. 26-29).

## BCRL1979
- **Verified authors**: Dario Bini, Milvio Capovani, Francesco Romani, Grazia Lotti
- **Verified title**: O(n^{2.7799}) complexity for n x n approximate matrix multiplication
- **Journal**: Information Processing Letters, Vol. 8, No. 5, pp. 234-235 (1979)
- **DOI**: 10.1016/0020-0190(79)90113-3
- **arXiv**: N/A
- **Source URL**: OpenAlex `https://api.openalex.org/works/https://doi.org/10.1016/0020-0190(79)90113-3`
- **Claims supported**:
  - Claim: Introduced approximate bilinear algorithms (border rank) for matrix multiplication.
- **Status**: METADATA-ONLY (OpenAlex verified; paywalled Elsevier full text; channels tried: paperclip, Unpaywall, OpenAlex)
- **Notes**: Standard historical citation for approximate bilinear algorithms.

## Bini1980
- **Verified authors**: Dario Bini
- **Verified title**: Relations between exact and approximate bilinear algorithms. Applications
- **Journal**: Calcolo, Vol. 17, No. 1, pp. 87-97 (1980)
- **DOI**: 10.1007/BF02575865
- **arXiv**: N/A
- **Source URL**: Crossref `https://api.crossref.org/works/10.1007/BF02575865`
- **Claims supported**:
  - Claim: Proved that approximate bilinear algorithms modulo epsilon convert to exact bilinear algorithms at the same asymptotic exponent via tensor powering and interpolation in epsilon.
- **Status**: METADATA-ONLY (Crossref verified; paywalled Springer full text; self-contained proof of the conversion lemma is also verified in Pass2026 Appendix A.3, p. 23)
- **Notes**: Channels tried: paperclip, Unpaywall, Crossref, OpenAlex.

## Strassen1987
- **Verified authors**: Volker Strassen
- **Verified title**: Relative bilinear complexity and matrix multiplication
- **Journal**: Journal fur die reine und angewandte Mathematik (Crelle's Journal), Vol. 375/376, pp. 406-443 (1987)
- **DOI**: 10.1515/crll.1987.375-376.406
- **arXiv**: N/A
- **Source URL**: OpenAlex `https://api.openalex.org/works/https://doi.org/10.1515/crll.1987.375-376.406`
- **Claims supported**:
  - Claim: Introduced the laser method and the Strassen tensor Str_q of border rank q + 1.
- **Status**: METADATA-ONLY (OpenAlex verified; paywalled De Gruyter full text; Str_q definition and border rank cross-verified in Li2026 Sec. 1.1 and Dogan2026 Sec. 1.2)
- **Notes**: Channels tried: paperclip, Unpaywall, OpenAlex.

## CW1990
- **Verified authors**: Don Coppersmith, Shmuel Winograd
- **Verified title**: Matrix multiplication via arithmetic progressions
- **Journal**: Journal of Symbolic Computation, Vol. 9, No. 3, pp. 251-280 (1990)
- **DOI**: 10.1016/S0747-7171(08)80013-2
- **arXiv**: N/A
- **Source URL**: OpenAlex `https://api.openalex.org/works/https://doi.org/10.1016/S0747-7171(08)80013-2`
- **Claims supported**:
  - Claim: Refined the laser method with progression-free sets and the Coppersmith-Winograd tensor to achieve omega < 2.3755.
- **Status**: METADATA-ONLY (OpenAlex verified; publisher HTML gated against automated fetch; channels tried: paperclip, Unpaywall, OpenAlex)
- **Notes**: Standard historical benchmark citation.

## BCS1997
- **Verified authors**: Peter Burgisser (Peter B{\"u}rgisser), Michael Clausen, Mohammad Amin Shokrollahi
- **Verified title**: Algebraic Complexity Theory
- **Journal**: Grundlehren der mathematischen Wissenschaften, Vol. 315, Springer (1997)
- **DOI**: 10.1007/978-3-662-03338-8
- **arXiv**: N/A
- **Source URL**: OpenAlex `https://api.openalex.org/works/https://doi.org/10.1007/978-3-662-03338-8`
- **Claims supported**:
  - Claim: Standard reference for bilinear algorithms, tensor rank, border rank, and the transposition principle (Chapters 13--15).
- **Status**: METADATA-ONLY (OpenAlex verified; closed monograph; channels tried: paperclip, Unpaywall, OpenAlex)
- **Notes**: Standard textbook reference.
