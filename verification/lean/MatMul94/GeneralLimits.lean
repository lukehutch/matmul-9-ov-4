/-
  MatMul94/GeneralLimits.lean

  Exact logical boundary of universal constant lower bounds across three
  successively broader algorithm classes (Section 4.4 of the paper):
  1. Generalized Universal Lower Bounds (Salvage):
     - Pass Remark 4.5 meta-family (`remark45_universal_round_necessary`,
       `remark45_universal_vk_pow_gt_w_pow`).
     - Universal Bini-conversion degree horizon (`general_bini_deg_horizon`).
  2. Pointwise arithmetic comparisons for the arbitrary-algorithm disproof (intervals in text/Python):
     - Strassen 1969 (`counterexample_strassen_1969`),
     - Pan 1978 (`counterexample_pan_1978`),
     - Single-matrix `Str_3^{⊗N}` strictly beating Pass's pre-Bini universal
       lower bounds at `τ ∈ {2.807, 2.500, 2.371}`
       (`counterexample_str3_beats_pass_2807`, `_2500`, `_2371`).
  3. Arithmetic form of the supermultiplicative obstruction at `τ > 9/4`:
     - Every rational-valued supermultiplicative rank lower bound obeys `Φ(V) ≤ V^{9/4}`
       under `ω ≤ 9/4` (`supermultiplicative_bound_le_9_4`).
     - Polynomial-size pairs `(V, R*) = (m^4, m^9 + 1)` strictly exceed every
       supermultiplicative lower bound while achieving exponent `< 9/4 + a0/b0`
       (`bernoulli_add_one_lt_two`, `small_V_consistent_with_9_4_general`,
       `small_V_16_witness_2251`, `exact_V_16_witness_9_4`, `small_V_81_witness_2251`).

  Pure-kernel Lean 4.36.0, zero Mathlib, zero `sorry`, zero `native_decide`.
-/

import MatMul94.ConstructiveWitnesses

namespace MatMul94

/-! ### Part 1: Generalized Universal Lower Bounds (Pass Remark 4.5 & Bini Horizon) -/

/-- Shared cancellation step for Pass's Remark 4.5 meta-family (Eq. (r45_step2)). -/
private theorem remark45_step2
    {R_num R_den d k w Λ E_k a0 b0 : Nat}
    (hRden : 1 ≤ R_den) (_hw : 1 ≤ w) (h4a : 4 * a0 < 3 * b0)
    (hH3 : 64 ^ k * w ^ 9 * R_num ^ (6 * d * k) ≤ E_k * R_den ^ (6 * d * k))
    (hH4 : E_k ^ (4 * b0) < (w ^ 2 * Λ ^ k) ^ (9 * b0 + 4 * a0)) :
    w ^ (18 * b0 - 8 * a0) * (64 ^ (4 * b0) * R_num ^ (24 * b0 * d)) ^ k
      < (Λ ^ (9 * b0 + 4 * a0) * R_den ^ (24 * b0 * d)) ^ k := by
  let p := 9 * b0 + 4 * a0
  let q := 4 * b0
  have h1 := Nat.pow_le_pow_left hH3 q
  rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow] at h1
  rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at h1
  have h2 := Nat.mul_lt_mul_of_pos_right hH4 (pow_pos_of_pos hRden (6 * d * k * q))
  have hcomb := Nat.lt_of_le_of_lt h1 h2
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hcomb
  have hwsplit : w ^ (9 * q) = w ^ (18 * b0 - 8 * a0) * w ^ (2 * p) := by
    rw [← Nat.pow_add]
    have : 18 * b0 - 8 * a0 + 2 * p = 9 * q := by dsimp only [p, q]; omega
    rw [this]
  rw [hwsplit] at hcomb
  have eL : 64 ^ (k * q) * (w ^ (18 * b0 - 8 * a0) * w ^ (2 * p)) * R_num ^ (6 * d * k * q)
      = (w ^ (18 * b0 - 8 * a0) * (64 ^ (4 * b0) * R_num ^ (24 * b0 * d)) ^ k) * w ^ (2 * p) := by
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
    have a1 : 4 * b0 * k = k * q := by dsimp only [q]; ac_rfl
    have a2 : 24 * b0 * d * k = 6 * d * k * q := by dsimp only [q]; ac_rfl
    rw [a1, a2]; ac_rfl
  have eR : w ^ (2 * p) * Λ ^ (k * p) * R_den ^ (6 * d * k * q)
      = (Λ ^ (9 * b0 + 4 * a0) * R_den ^ (24 * b0 * d)) ^ k * w ^ (2 * p) := by
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
    have a1 : (9 * b0 + 4 * a0) * k = k * p := by dsimp only [p]; ac_rfl
    have a2 : 24 * b0 * d * k = 6 * d * k * q := by dsimp only [q]; ac_rfl
    rw [a1, a2]; ac_rfl
  rw [eL, eR] at hcomb
  exact Nat.lt_of_mul_lt_mul_right hcomb

/-- Theorem `thm:remark45_universal` (Part 1): universal round-length lower bound across
    Pass's entire Remark 4.5 meta-family (even with zero balancing loss `D = 1`). -/
theorem remark45_universal_round_necessary
    {m n R_num R_den d k D w Λ E_k a0 b0 : Nat}
    (_hm : n < m) (hn : 1 ≤ n) (_hR : R_den < R_num) (hRden : 1 ≤ R_den)
    (_hd : 1 ≤ d) (_hk : 1 ≤ k) (_hD : 1 ≤ D) (hw : 1 ≤ w) (_hLam : 1 ≤ Λ)
    (_ha0 : 1 ≤ a0) (_hb0 : 1 ≤ b0) (htau : 4 * a0 < 3 * b0)
    (hH1 : m ^ 3 * R_den ^ 2 ≤ n ^ 3 * R_num ^ 2)
    (hH2 : Λ * D ^ 2 * n ^ (4 * d) ≤ m ^ (4 * d))
    (hH3 : 64 ^ k * w ^ 9 * R_num ^ (6 * d * k) ≤ E_k * R_den ^ (6 * d * k))
    (hH4 : E_k ^ (4 * b0) < (w ^ 2 * Λ ^ k) ^ (9 * b0 + 4 * a0)) :
    64 ^ (4 * b0) * D ^ (2 * (9 * b0 + 4 * a0)) * n ^ (16 * a0 * d) < m ^ (16 * a0 * d) := by
  let p := 9 * b0 + 4 * a0
  have hst := remark45_step2 hRden hw htau hH3 hH4
  have h1 : (64 ^ (4 * b0) * R_num ^ (24 * b0 * d)) ^ k
      < (Λ ^ p * R_den ^ (24 * b0 * d)) ^ k := by
    have hwge : 1 ≤ w ^ (18 * b0 - 8 * a0) := pow_pos_of_pos hw _
    have hm := Nat.mul_le_mul_right ((64 ^ (4 * b0) * R_num ^ (24 * b0 * d)) ^ k) hwge
    rw [Nat.one_mul] at hm
    exact Nat.lt_of_le_of_lt hm hst
  have hroot : 64 ^ (4 * b0) * R_num ^ (24 * b0 * d) < Λ ^ p * R_den ^ (24 * b0 * d) :=
    lt_of_pow_lt_pow_left h1
  have hpos_m : 0 < D ^ (2 * p) * n ^ (4 * d * p) :=
    Nat.mul_pos (pow_pos_of_pos _hD _) (pow_pos_of_pos hn _)
  have hmul := Nat.mul_lt_mul_of_pos_right hroot hpos_m
  have hH2p := Nat.pow_le_pow_left hH2 p
  rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hH2p
  have hH1p := Nat.pow_le_pow_left hH1 (12 * b0 * d)
  rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hH1p
  have hstep1 : 64 ^ (4 * b0) * D ^ (2 * p) * n ^ (4 * d * p) * R_num ^ (24 * b0 * d)
      < m ^ (4 * d * p) * R_den ^ (24 * b0 * d) := by
    have eL : 64 ^ (4 * b0) * R_num ^ (24 * b0 * d) * (D ^ (2 * p) * n ^ (4 * d * p))
        = 64 ^ (4 * b0) * D ^ (2 * p) * n ^ (4 * d * p) * R_num ^ (24 * b0 * d) := by ac_rfl
    have eR : Λ ^ p * R_den ^ (24 * b0 * d) * (D ^ (2 * p) * n ^ (4 * d * p))
        = (Λ ^ p * D ^ (2 * p) * n ^ (4 * d * p)) * R_den ^ (24 * b0 * d) := by ac_rfl
    rw [eL, eR] at hmul
    exact Nat.lt_of_lt_of_le hmul (Nat.mul_le_mul_right _ hH2p)
  have hstep2 : m ^ (4 * d * p) * R_den ^ (24 * b0 * d)
      ≤ m ^ (16 * a0 * d) * n ^ (36 * b0 * d) * R_num ^ (24 * b0 * d) := by
    have hmsplit : m ^ (4 * d * p) = m ^ (16 * a0 * d) * m ^ (36 * b0 * d) := by
      rw [← Nat.pow_add]
      have : 16 * a0 * d + 36 * b0 * d = 4 * d * p := by dsimp only [p]; grind
      rw [this]
    rw [hmsplit, Nat.mul_assoc]
    have e1 : 3 * (12 * b0 * d) = 36 * b0 * d := by ac_rfl
    have e2 : 2 * (12 * b0 * d) = 24 * b0 * d := by ac_rfl
    rw [e1, e2] at hH1p
    have hm := Nat.mul_le_mul_left (m ^ (16 * a0 * d)) hH1p
    rwa [← Nat.mul_assoc (m ^ (16 * a0 * d)) (n ^ (36 * b0 * d))] at hm
  have hfin := Nat.lt_of_lt_of_le hstep1 hstep2
  have hnsplit : n ^ (4 * d * p) = n ^ (16 * a0 * d) * n ^ (36 * b0 * d) := by
    rw [← Nat.pow_add]
    have : 16 * a0 * d + 36 * b0 * d = 4 * d * p := by dsimp only [p]; grind
    rw [this]
  rw [hnsplit] at hfin
  have eL : 64 ^ (4 * b0) * D ^ (2 * p) * (n ^ (16 * a0 * d) * n ^ (36 * b0 * d)) * R_num ^ (24 * b0 * d)
      = (64 ^ (4 * b0) * D ^ (2 * p) * n ^ (16 * a0 * d)) * (n ^ (36 * b0 * d) * R_num ^ (24 * b0 * d)) := by ac_rfl
  have eR : m ^ (16 * a0 * d) * n ^ (36 * b0 * d) * R_num ^ (24 * b0 * d)
      = m ^ (16 * a0 * d) * (n ^ (36 * b0 * d) * R_num ^ (24 * b0 * d)) := by ac_rfl
  rw [eL, eR] at hfin
  exact Nat.lt_of_mul_lt_mul_right hfin

/-- Theorem `thm:remark45_universal` (Part 2): universal base-side amplification `w^{18 b0} < v_k^{4 a0}`
    across Pass's entire Remark 4.5 meta-family. -/
theorem remark45_universal_vk_pow_gt_w_pow
    {m n R_num R_den d k D w Λ E_k a0 b0 : Nat}
    (_hm : n < m) (hn : 1 ≤ n) (_hR : R_den < R_num) (hRden : 1 ≤ R_den)
    (_hd : 1 ≤ d) (_hk : 1 ≤ k) (hD : 1 ≤ D) (hw : 1 ≤ w) (_hLam : 1 ≤ Λ)
    (_ha0 : 1 ≤ a0) (hb0 : 1 ≤ b0) (htau : 4 * a0 < 3 * b0)
    (hH1 : m ^ 3 * R_den ^ 2 ≤ n ^ 3 * R_num ^ 2)
    (hH2 : Λ * D ^ 2 * n ^ (4 * d) ≤ m ^ (4 * d))
    (hH3 : 64 ^ k * w ^ 9 * R_num ^ (6 * d * k) ≤ E_k * R_den ^ (6 * d * k))
    (hH4 : E_k ^ (4 * b0) < (w ^ 2 * Λ ^ k) ^ (9 * b0 + 4 * a0)) :
    w ^ (18 * b0) < (w ^ 2 * Λ ^ k) ^ (4 * a0) := by
  have hst := remark45_step2 hRden hw htau hH3 hH4
  have hH2_9 := Nat.pow_le_pow_left hH2 (9 * b0)
  rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hH2_9
  have hH1_12 := Nat.pow_le_pow_left hH1 (12 * b0 * d)
  rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hH1_12
  have hcancel : Λ ^ (9 * b0) * R_den ^ (24 * b0 * d) ≤ R_num ^ (24 * b0 * d) := by
    have hD1 : 1 ≤ D ^ (2 * (9 * b0)) := pow_pos_of_pos hD _
    have hdrop : Λ ^ (9 * b0) * n ^ (4 * d * (9 * b0)) ≤ m ^ (4 * d * (9 * b0)) := by
      have hm := Nat.mul_le_mul_right (n ^ (4 * d * (9 * b0))) (Nat.mul_le_mul_left (Λ ^ (9 * b0)) hD1)
      rw [Nat.mul_one] at hm
      exact Nat.le_trans hm hH2_9
    have hm1 := Nat.mul_le_mul_right (R_den ^ (24 * b0 * d)) hdrop
    have e1 : 4 * d * (9 * b0) = 36 * b0 * d := by ac_rfl
    have e2 : 3 * (12 * b0 * d) = 36 * b0 * d := by ac_rfl
    have e3 : 2 * (12 * b0 * d) = 24 * b0 * d := by ac_rfl
    rw [e1] at hm1
    rw [e2, e3] at hH1_12
    have htr := Nat.le_trans hm1 hH1_12
    have eL : Λ ^ (9 * b0) * n ^ (36 * b0 * d) * R_den ^ (24 * b0 * d)
        = (Λ ^ (9 * b0) * R_den ^ (24 * b0 * d)) * n ^ (36 * b0 * d) := by ac_rfl
    have eR : n ^ (36 * b0 * d) * R_num ^ (24 * b0 * d)
        = R_num ^ (24 * b0 * d) * n ^ (36 * b0 * d) := Nat.mul_comm _ _
    rw [eL, eR] at htr
    exact Nat.le_of_mul_le_mul_right htr (pow_pos_of_pos hn _)
  have h64_ge : 1 ≤ 64 ^ (4 * b0) := pow_pos_of_pos (by decide) _
  have hstep_lam : Λ ^ (9 * b0 + 4 * a0) * R_den ^ (24 * b0 * d)
      ≤ Λ ^ (4 * a0) * (64 ^ (4 * b0) * R_num ^ (24 * b0 * d)) := by
    have h1 := Nat.mul_le_mul_left (Λ ^ (4 * a0)) hcancel
    have h2 := Nat.mul_le_mul_right (R_num ^ (24 * b0 * d)) h64_ge
    rw [Nat.one_mul] at h2
    have h3 := Nat.le_trans h1 (Nat.mul_le_mul_left (Λ ^ (4 * a0)) h2)
    have eL : Λ ^ (4 * a0) * (Λ ^ (9 * b0) * R_den ^ (24 * b0 * d))
        = Λ ^ (9 * b0 + 4 * a0) * R_den ^ (24 * b0 * d) := by
      rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm]
    rwa [eL] at h3
  have hpow_k := Nat.pow_le_pow_left hstep_lam k
  rw [Nat.mul_pow (Λ ^ (4 * a0))] at hpow_k
  have hlt := Nat.lt_of_lt_of_le hst hpow_k
  have hlt_c : w ^ (18 * b0 - 8 * a0) < (Λ ^ (4 * a0)) ^ k :=
    Nat.lt_of_mul_lt_mul_right hlt
  have hmul_w := Nat.mul_lt_mul_of_pos_left hlt_c (pow_pos_of_pos hw (8 * a0))
  have eL2 : w ^ (8 * a0) * w ^ (18 * b0 - 8 * a0) = w ^ (18 * b0) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
  have eR2 : w ^ (8 * a0) * (Λ ^ (4 * a0)) ^ k = (w ^ 2 * Λ ^ k) ^ (4 * a0) := by
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
    have a1 : 2 * (4 * a0) = 8 * a0 := by ac_rfl
    have a2 : 4 * a0 * k = k * (4 * a0) := Nat.mul_comm _ _
    rw [a1, a2]
  rwa [eL2, eR2] at hmul_w

/-- Proposition `prop:general_bini_horizon`: Universal Bini-conversion degree horizon for ANY
    border-rank identity obeying the `9/4` floor `v0^9 ≤ r0^4`. -/
theorem general_bini_deg_horizon
    {v0 r0 E_eps h a0 b0 : Nat}
    (_hv0 : 2 ≤ v0) (_hr0 : 1 ≤ r0) (_hE : 1 ≤ E_eps) (hh : 1 ≤ h)
    (_ha0 : 1 ≤ a0) (_hb0 : 1 ≤ b0)
    (hfloor : v0 ^ 9 ≤ r0 ^ 4)
    (hvalid : ((h * E_eps + 1) * r0 ^ h) ^ (4 * b0) < (v0 ^ h) ^ (9 * b0 + 4 * a0)) :
    (h * E_eps + 1) ^ b0 < (v0 ^ h) ^ a0 ∧ (E_eps + 1) ^ b0 < (v0 ^ h) ^ a0 := by
  have hfl := Nat.pow_le_pow_left hfloor (b0 * h)
  rw [← Nat.pow_mul, ← Nat.pow_mul] at hfl
  rw [Nat.mul_pow, ← Nat.pow_mul, Nat.pow_add] at hvalid
  have h1 : (h * E_eps + 1) ^ (4 * b0) * (v0 ^ h) ^ (9 * b0)
      < (v0 ^ h) ^ (4 * a0) * (v0 ^ h) ^ (9 * b0) := by
    have eV : (v0 ^ h) ^ (9 * b0) = v0 ^ (9 * (b0 * h)) := by
      rw [← Nat.pow_mul]
      have : h * (9 * b0) = 9 * (b0 * h) := by ac_rfl
      rw [this]
    have eR : r0 ^ (h * (4 * b0)) = r0 ^ (4 * (b0 * h)) := by
      have : h * (4 * b0) = 4 * (b0 * h) := by ac_rfl
      rw [this]
    rw [eR] at hvalid
    have hm := Nat.mul_le_mul_left ((h * E_eps + 1) ^ (4 * b0)) hfl
    rw [← eV] at hm
    have eC : (v0 ^ h) ^ (9 * b0) * (v0 ^ h) ^ (4 * a0)
        = (v0 ^ h) ^ (4 * a0) * (v0 ^ h) ^ (9 * b0) := Nat.mul_comm _ _
    exact Nat.lt_of_le_of_lt hm (eC ▸ hvalid)
  have hcancel : (h * E_eps + 1) ^ (4 * b0) < (v0 ^ h) ^ (4 * a0) :=
    Nat.lt_of_mul_lt_mul_right h1
  have hroot : (h * E_eps + 1) ^ b0 < (v0 ^ h) ^ a0 := by
    apply lt_of_pow_lt_pow_left (n := 4)
    rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm b0 4, Nat.mul_comm a0 4]
    exact hcancel
  have hle : (E_eps + 1) ^ b0 ≤ (h * E_eps + 1) ^ b0 := by
    apply Nat.pow_le_pow_left
    have := Nat.mul_le_mul_right E_eps hh
    rw [Nat.one_mul] at this
    omega
  exact ⟨hroot, Nat.lt_of_le_of_lt hle hroot⟩

/-! ### Part 2: Pointwise arithmetic comparisons for the arbitrary-algorithm disproof -/

private theorem lt_pow_of_log2_two {E p1 Q a b : Nat}
    (hE : Log2Le E p1 Q) (hcmp : p1 * b < Q * a) : E ^ b < 2 ^ a :=
  lt_pow_of_log2 hE (Log2Ge.two Q) hcmp

/-- Strassen (1969): `V = 2, R = 7` beats `τ = 2.808` (`7^1000 < 2^2808`). -/
theorem counterexample_strassen_1969 : 7 ^ 1000 < 2 ^ 2808 :=
  lt_pow_of_log2_two (E := 7) (a := 2808) (b := 1000) log2Le_7 (by decide)

/-- Pan (1978): `V = 70, R = 143640` beats `τ = 2.800 = 14/5` with `70 < 10^2 < v_k_pass`. -/
theorem counterexample_pan_1978 :
    143640 ^ 5 < 70 ^ 14 ∧ 70 < 10 ^ 2 ∧
    (∀ c d k, ValidPassTriple 14 5 c d k → 70 < v_k_pass c d k) := by
  refine ⟨by decide, by decide, ?_⟩
  intro c d k hV
  have hlb := universal_vk_lb_2800 hV
  have h1 : 70 < 10 ^ 2 := by decide
  have h2 : 10 ^ 2 ≤ 10 ^ 6153 := Nat.pow_le_pow_right (n := 10) (i := 2) (j := 6153) (by decide) (by decide)
  exact Nat.lt_trans (Nat.lt_of_lt_of_le h1 h2) hlb

/-- Single-matrix `Str_3^{⊗22}` (`V ≤ 10^344`) strictly beats Pass's universal pre-Bini LB (`> 10^5909`) at `τ = 2.807`. -/
theorem counterexample_str3_beats_pass_2807 :
    ∀ c d k, ValidPassTriple 2807 1000 c d k →
      (R_single_str3 22 3 7) ^ 1000 < (V_single_str3 22 3 7) ^ 2807 ∧
      V_single_str3 22 3 7 < v_k_pass c d k := by
  intro c d k hV
  have hw := witness_str3_single_matrix_2807
  have hlb := universal_vk_lb_2807 hV
  have hpow : 10 ^ 344 ≤ 10 ^ 5909 := Nat.pow_le_pow_right (n := 10) (i := 344) (j := 5909) (by decide) (by decide)
  exact ⟨hw.2.2, Nat.lt_of_le_of_lt (Nat.le_trans hw.2.1 hpow) hlb⟩

/-- Single-matrix `Str_3^{⊗90}` (`V ≤ 10^19610`) strictly beats Pass's universal pre-Bini LB (`> 10^100884`) at `τ = 2.500`. -/
theorem counterexample_str3_beats_pass_2500 :
    ∀ c d k, ValidPassTriple 5 2 c d k →
      (R_single_str3 90 10 28) ^ 2 < (V_single_str3 90 10 28) ^ 5 ∧
      V_single_str3 90 10 28 < v_k_pass c d k := by
  intro c d k hV
  have hw := witness_str3_single_matrix_2500
  have hlb := universal_vk_lb_2500 hV
  have hpow : 10 ^ 19610 ≤ 10 ^ 100884 := Nat.pow_le_pow_right (n := 10) (i := 19610) (j := 100884) (by decide) (by decide)
  exact ⟨hw.2.2, Nat.lt_of_le_of_lt (Nat.le_trans hw.2.1 hpow) hlb⟩

/-- Single-matrix `Str_3^{⊗340}` (`V ≤ 10^899543`) strictly beats Pass's universal pre-Bini LB (`> 10^1276692`) at `τ = 2.371`. -/
theorem counterexample_str3_beats_pass_2371 :
    ∀ c d k, ValidPassTriple 2371 1000 c d k →
      (R_single_str3 340 34 100) ^ 1000 < (V_single_str3 340 34 100) ^ 2371 ∧
      V_single_str3 340 34 100 < v_k_pass c d k := by
  intro c d k hV
  have hw := witness_str3_single_matrix_2371
  have hlb := universal_vk_lb_2371 hV
  have hpow : 10 ^ 899543 ≤ 10 ^ 1276692 := Nat.pow_le_pow_right (n := 10) (i := 899543) (j := 1276692) (by decide) (by decide)
  exact ⟨hw.2.2, Nat.lt_of_le_of_lt (Nat.le_trans hw.2.1 hpow) hlb⟩

/-! ### Part 3: Arithmetic form of the supermultiplicative obstruction -/

/-- Zero-subtraction `Nat` Bernoulli inequality: `B^(k + 1) + k * B^k ≤ B * (B + 1)^k`. -/
private theorem nat_bernoulli_mul (B : Nat) : ∀ k, B ^ (k + 1) + k * B ^ k ≤ B * (B + 1) ^ k
  | 0 => by simp
  | k + 1 => by
    have ih := nat_bernoulli_mul B k
    have hm := Nat.mul_le_mul_right (B + 1) ih
    have eR : B * (B + 1) ^ k * (B + 1) = B * (B + 1) ^ (k + 1) := by
      rw [Nat.pow_succ (B + 1) k, Nat.mul_assoc]
    have eL : (B ^ (k + 1) + k * B ^ k) * (B + 1)
        = B ^ (k + 2) + (k + 1) * B ^ (k + 1) + k * B ^ k := by
      rw [Nat.pow_succ B (k + 1), Nat.pow_succ B k]; grind
    rw [eL, eR] at hm
    exact Nat.le_trans (Nat.le_add_right _ (k * B ^ k)) hm

/-- Theorem `thm:supermult_obstruction` (Part (i)): Under `ω ≤ 9/4`, EVERY supermultiplicative
    rank lower bound `Φ(n) = Φ_num(n) / Φ_den(n) ≤ R(n)` obeys `Φ(V) ≤ V^{9/4}` for all `V ≥ 1`. -/
theorem supermultiplicative_bound_le_9_4
    (R Φ_num Φ_den : Nat → Nat)
    (hω : ∀ b, 1 ≤ b → ∃ C, 1 ≤ C ∧ ∀ n, 1 ≤ n → R n ^ (4 * b) ≤ C ^ (4 * b) * n ^ (9 * b + 4))
    (hden : ∀ n, 1 ≤ n → 1 ≤ Φ_den n)
    (hbound : ∀ n, 1 ≤ n → Φ_num n ≤ R n * Φ_den n)
    (hsuper : ∀ V r, 1 ≤ V → 1 ≤ r → Φ_num V ^ r * Φ_den (V ^ r) ≤ Φ_num (V ^ r) * Φ_den V ^ r) :
    ∀ V, 1 ≤ V → Φ_num V ^ 4 ≤ Φ_den V ^ 4 * V ^ 9 := by
  intro V hV
  by_cases hle : Φ_num V ^ 4 ≤ Φ_den V ^ 4 * V ^ 9
  · exact hle
  · exfalso
    let A := Φ_num V ^ 4
    let B := Φ_den V ^ 4 * V ^ 9
    have hB_pos : 1 ≤ B := Nat.mul_pos (pow_pos_of_pos (hden V hV) 4) (pow_pos_of_pos hV 9)
    have hAB : B + 1 ≤ A := by omega
    -- Step 1: pick b so that B^b * V^4 < A^b
    let b := B * V ^ 4 + 1
    have hb_pos : 1 ≤ b := by dsimp only [b]; omega
    have hstep1 : B ^ b * V ^ 4 < A ^ b := by
      have hbern := nat_bernoulli_mul B b
      have hpow := Nat.mul_le_mul_left B (Nat.pow_le_pow_left hAB b)
      have hBpos_b : 0 < B ^ b := pow_pos_of_pos hB_pos b
      have hgt : B * (B ^ b * V ^ 4) < b * B ^ b := by
        have h1 : B * V ^ 4 < b := by dsimp only [b]; omega
        have hm := Nat.mul_lt_mul_of_pos_right h1 hBpos_b
        have eL : B * V ^ 4 * B ^ b = B * (B ^ b * V ^ 4) := by ac_rfl
        rwa [eL] at hm
      have hcomb : B * (B ^ b * V ^ 4) < B * A ^ b := by omega
      exact Nat.lt_of_mul_lt_mul_left hcomb
    -- Step 2: apply hω b to get finite constant C ≥ 1
    rcases hω b hb_pos with ⟨C, hC_pos, hRC⟩
    let A' := A ^ b
    let B' := B ^ b * V ^ 4
    have hB'_pos : 1 ≤ B' := Nat.mul_pos (pow_pos_of_pos hB_pos b) (pow_pos_of_pos hV 4)
    have hA'B' : B' + 1 ≤ A' := hstep1
    -- Step 3: pick r so that C^(4*b) * B'^r < A'^r
    let r := B' * C ^ (4 * b) + 1
    have hr_pos : 1 ≤ r := by dsimp only [r]; omega
    have hstep2 : C ^ (4 * b) * B' ^ r < A' ^ r := by
      have hbern := nat_bernoulli_mul B' r
      have hpow := Nat.mul_le_mul_left B' (Nat.pow_le_pow_left hA'B' r)
      have hB'pos_r : 0 < B' ^ r := pow_pos_of_pos hB'_pos r
      have hgt : B' * (C ^ (4 * b) * B' ^ r) < r * B' ^ r := by
        have h1 : B' * C ^ (4 * b) < r := by dsimp only [r]; omega
        have hm := Nat.mul_lt_mul_of_pos_right h1 hB'pos_r
        have eL : B' * C ^ (4 * b) * B' ^ r = B' * (C ^ (4 * b) * B' ^ r) := by ac_rfl
        rwa [eL] at hm
      have hcomb : B' * (C ^ (4 * b) * B' ^ r) < B' * A' ^ r := by omega
      exact Nat.lt_of_mul_lt_mul_left hcomb
    -- Step 4: supermultiplicativity + hbound + hRC gives A'^r ≤ C^(4*b) * B'^r
    have hVr_pos : 1 ≤ V ^ r := pow_pos_of_pos hV r
    have hsup := Nat.pow_le_pow_left (hsuper V r hV hr_pos) (4 * b)
    rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hsup
    have hbd := Nat.pow_le_pow_left (hbound (V ^ r) hVr_pos) (4 * b)
    rw [Nat.mul_pow] at hbd
    have hRbd := hRC (V ^ r) hVr_pos
    have hchain : Φ_num V ^ (r * (4 * b)) * Φ_den (V ^ r) ^ (4 * b)
        ≤ (C ^ (4 * b) * (V ^ r) ^ (9 * b + 4) * Φ_den V ^ (r * (4 * b))) * Φ_den (V ^ r) ^ (4 * b) := by
      have s1 := Nat.mul_le_mul_right (Φ_den V ^ (r * (4 * b))) hbd
      have s2 := Nat.mul_le_mul_right (Φ_den (V ^ r) ^ (4 * b) * Φ_den V ^ (r * (4 * b))) hRbd
      have eM : R (V ^ r) ^ (4 * b) * Φ_den (V ^ r) ^ (4 * b) * Φ_den V ^ (r * (4 * b))
          = R (V ^ r) ^ (4 * b) * (Φ_den (V ^ r) ^ (4 * b) * Φ_den V ^ (r * (4 * b))) := by ac_rfl
      have eR : C ^ (4 * b) * (V ^ r) ^ (9 * b + 4) * (Φ_den (V ^ r) ^ (4 * b) * Φ_den V ^ (r * (4 * b)))
          = (C ^ (4 * b) * (V ^ r) ^ (9 * b + 4) * Φ_den V ^ (r * (4 * b))) * Φ_den (V ^ r) ^ (4 * b) := by ac_rfl
      exact Nat.le_trans hsup (Nat.le_trans s1 (eR ▸ (eM ▸ s2)))
    have hupper := Nat.le_of_mul_le_mul_right hchain (pow_pos_of_pos (hden (V ^ r) hVr_pos) (4 * b))
    have eA' : A' ^ r = Φ_num V ^ (r * (4 * b)) := by
      dsimp only [A', A]; rw [← Nat.pow_mul, ← Nat.pow_mul]
      have : 4 * (b * r) = r * (4 * b) := by ac_rfl
      rw [this]
    have eB' : C ^ (4 * b) * B' ^ r = C ^ (4 * b) * (V ^ r) ^ (9 * b + 4) * Φ_den V ^ (r * (4 * b)) := by
      dsimp only [B', B]
      rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul,
          ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
      have a1 : 4 * (b * r) = r * (4 * b) := by ac_rfl
      have a2 : 9 * (b * r) + 4 * r = r * (9 * b + 4) := by grind
      rw [a1]
      calc C ^ (4 * b) * (Φ_den V ^ (r * (4 * b)) * V ^ (9 * (b * r)) * V ^ (4 * r))
          = C ^ (4 * b) * (V ^ (9 * (b * r)) * V ^ (4 * r)) * Φ_den V ^ (r * (4 * b)) := by ac_rfl
        _ = C ^ (4 * b) * V ^ (r * (9 * b + 4)) * Φ_den V ^ (r * (4 * b)) := by rw [← Nat.pow_add, a2]
    rw [eA', eB'] at hstep2
    omega

/-- Elementary pure-`Nat` bound: `(N + 1)^k < 2 * N^k` for all `N ≥ 2` and `2 * k ≤ N`. -/
theorem bernoulli_add_one_lt_two (N k : Nat) (hN : 2 ≤ N) (hk : 2 * k ≤ N) :
    (N + 1) ^ k < 2 * N ^ k := by
  have he := e_sandwich N 1 (by omega) (by decide)
  have h1 : (1 : Nat) ^ (1 + 1) = 1 := by decide
  have h4 : (1 + 1 : Nat) ^ (1 + 1) = 4 := by decide
  rw [h1, Nat.mul_one, h4, Nat.mul_comm (N ^ N) 4] at he
  have h2k : ((N + 1) ^ k) ^ 2 < (2 * N ^ k) ^ 2 := by
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
    have hsub : (N + 1) ^ (k * 2) * N ^ (N - k * 2) < 4 * N ^ N := by
      have hle : N ^ (N - k * 2) ≤ (N + 1) ^ (N - k * 2) := Nat.pow_le_pow_left (by omega) _
      have hm := Nat.mul_le_mul_left ((N + 1) ^ (k * 2)) hle
      rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)] at hm
      exact Nat.lt_of_le_of_lt hm he
    have hsplit : 2 ^ 2 * N ^ (k * 2) * N ^ (N - k * 2) = 4 * N ^ N := by
      have h22 : (2 : Nat) ^ 2 = 4 := by decide
      rw [h22, Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le (by omega)]
    rw [← hsplit] at hsub
    exact Nat.lt_of_mul_lt_mul_right hsub
  exact lt_of_pow_lt_pow_left h2k

/-- Theorem `thm:supermult_obstruction` (Part (ii)): For every excess `δ = a0 / b0` and every `m ≥ 2`
    with `b0 ≤ 4 * a0 * (m^9 / 2)`, `V = m^4` and `R* = m^9 + 1` strictly exceed every
    supermultiplicative lower bound `Φ(V) ≤ V^{9/4}` while achieving exponent `< 9/4 + a0 / b0`. -/
theorem small_V_consistent_with_9_4_general
    {a0 b0 m : Nat} (ha0 : 1 ≤ a0) (_hb0 : 1 ≤ b0) (hm : 2 ≤ m)
    (hcond : b0 ≤ 4 * a0 * (m ^ 9 / 2)) :
    (m ^ 4) ^ 9 < (m ^ 9 + 1) ^ 4 ∧ (m ^ 9 + 1) ^ (4 * b0) < (m ^ 4) ^ (9 * b0 + 4 * a0) := by
  constructor
  · have h1 : (m ^ 4) ^ 9 = (m ^ 9) ^ 4 := by rw [← Nat.pow_mul, ← Nat.pow_mul]
    rw [h1]
    exact pow_lt_pow_left_of_lt (by decide) (by omega)
  · let N := m ^ 9
    let j1 := N / 2
    have hN2 : 2 ≤ N := by
      dsimp only [N]
      calc 2 ≤ 2 ^ 9 := by decide
        _ ≤ m ^ 9 := Nat.pow_le_pow_left hm 9
    have hbern := bernoulli_add_one_lt_two N j1 hN2 (by dsimp only [j1]; omega)
    have hpow := pow_lt_pow_left_of_lt (show 0 < 4 * a0 by omega) hbern
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hpow
    have h2m : 2 ^ (4 * a0) ≤ m ^ (4 * a0) := Nat.pow_le_pow_left hm (4 * a0)
    have hstep : (N + 1) ^ (j1 * (4 * a0)) < m ^ (4 * a0) * N ^ (j1 * (4 * a0)) :=
      Nat.lt_of_lt_of_le hpow (Nat.mul_le_mul_right _ h2m)
    have hb_le : b0 ≤ j1 * (4 * a0) := by
      dsimp only [j1, N]; rwa [Nat.mul_comm]
    have hred : (N + 1) ^ b0 < m ^ (4 * a0) * N ^ b0 := by
      have hgap : N ^ (j1 * (4 * a0) - b0) ≤ (N + 1) ^ (j1 * (4 * a0) - b0) :=
        Nat.pow_le_pow_left (by omega) _
      have hm1 := Nat.mul_le_mul_left ((N + 1) ^ b0) hgap
      rw [← Nat.pow_add, Nat.add_sub_of_le hb_le] at hm1
      have hcomb := Nat.lt_of_le_of_lt hm1 hstep
      have eR : m ^ (4 * a0) * N ^ (j1 * (4 * a0))
          = (m ^ (4 * a0) * N ^ b0) * N ^ (j1 * (4 * a0) - b0) := by
        rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le hb_le]
      rw [eR] at hcomb
      exact Nat.lt_of_mul_lt_mul_right hcomb
    have h4 := pow_lt_pow_left_of_lt (by decide : 0 < 4) hred
    rw [← Nat.pow_mul, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at h4
    have eL : b0 * 4 = 4 * b0 := Nat.mul_comm _ _
    have eR : m ^ (4 * a0 * 4) * N ^ (4 * b0) = (m ^ 4) ^ (9 * b0 + 4 * a0) := by
      dsimp only [N]
      rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add]
      have : 4 * a0 * 4 + 9 * (4 * b0) = 4 * (9 * b0 + 4 * a0) := by grind
      rw [this]
    rwa [eL, eR] at h4

private theorem lt_of_pow_four_eq {x y a b e : Nat}
    (he : e = 4 * b) (h : x ^ (4 * a) < y ^ e) :
    x ^ a < y ^ b := by
  subst he
  apply lt_of_pow_lt_pow_left (n := 4)
  rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm a 4, Nat.mul_comm b 4]
  exact h

/-- Supermultiplicative-only witness at `τ = 2.251`: `V = 16, R* = 513` satisfies
    `16^9 < 513^4` and `513^1000 < 16^2251` (excluded by Bläser's non-supermultiplicative bound `592 > 513`). -/
theorem small_V_16_witness_2251 : 16 ^ 9 < 513 ^ 4 ∧ 513 ^ 1000 < 16 ^ 2251 := by
  have h := small_V_consistent_with_9_4_general (a0 := 1) (b0 := 1000) (m := 2)
    (by decide) (by decide) (by decide) (by decide)
  have h16 : (2 : Nat) ^ 4 = 16 := by decide
  have h513 : (2 : Nat) ^ 9 + 1 = 513 := by decide
  rw [h16, h513] at h
  exact ⟨h.1, lt_of_pow_four_eq (x := 513) (y := 16) (a := 1000) (b := 2251) (by decide) h.2⟩

/-- Exact `9/4` equality arithmetic at `V = 16, R = 512`: `512^4 = 16^9`. -/
theorem exact_V_16_witness_9_4 : 512 ^ 4 = 16 ^ 9 := by decide

private theorem sb_bound_aux {a b c d e f : Nat}
    (h1 : a < b) (he : e ≠ 0) (hb : 0 < b)
    (h2 : b = c ^ 4) (h3 : d = c ^ 3) (h4 : 4 * (e + 1) = 3 * f) :
    a ^ e < d ^ f := by
  have p1 : a ^ e < b ^ e := Nat.pow_lt_pow_left h1 he
  have p2 : b ^ e ≤ b ^ (e + 1) := Nat.pow_le_pow_right hb (Nat.le_succ e)
  have p3 : b ^ (e + 1) = d ^ f := by
    rw [h2, h3, ← Nat.pow_mul, ← Nat.pow_mul, h4]
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le p1 p2) (Nat.le_of_eq p3)

/-- Concrete witness at `τ = 2.251` evading both supermultiplicative bounds and all known
    `O(V^2)` flattening bounds (`Bläser 16159.5`, `Massarenti–Raviolo 16929`, ideal `3 * 81^2 = 19683`):
    `μ = 3` gives `V = 81, R* = 19684` with `81^9 < 19684^4` and `19684^1000 < 81^2251`. -/
theorem small_V_81_witness_2251 :
    81 ^ 9 < 19684 ^ 4 ∧ 19684 ^ 1000 < 81 ^ 2251 ∧ 80 ^ 749 < 27 ^ 1000 := by
  have h := small_V_consistent_with_9_4_general (a0 := 1) (b0 := 1000) (m := 3)
    (by decide) (by decide) (by decide) (by decide)
  have h81 : (3 : Nat) ^ 4 = 81 := by decide
  have h19684 : (3 : Nat) ^ 9 + 1 = 19684 := by decide
  rw [h81, h19684] at h
  have hsb : 80 ^ 749 < 27 ^ 1000 :=
    sb_bound_aux (a := 80) (b := 81) (c := 3) (d := 27) (e := 749) (f := 1000)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨h.1, lt_of_pow_four_eq (x := 19684) (y := 81) (a := 1000) (b := 2251) (by decide) h.2, hsb⟩

/-- Exact `9/4` and `3*V^2` coincidence at `V = 81`: `19683^4 = 81^9` and `3 * 81^2 = 19683`. -/
theorem exact_V_81_witness_9_4 : 19683 ^ 4 = 81 ^ 9 ∧ 3 * 81 ^ 2 = 19683 := by decide

/-- Bläser's `(5/2)V^2 - 3V` bound excludes `V = 16, R = 513` (`592 > 513`) and passes `V = 81` (`16159.5 < 19684`). -/
theorem blaser_excludes_16_allows_81 :
    2 * 513 < 5 * 16 ^ 2 - 6 * 16 ∧ 5 * 81 ^ 2 - 6 * 81 < 2 * 19684 := by decide

end MatMul94
