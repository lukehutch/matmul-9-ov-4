/-
  MatMul94/ConstructiveWitnesses.lean

  Machine-checked constructive upper witnesses for:
  1. All 8 benchmark exponents of Pass's Theorem 4.3 pre-Bini (`ValidPassTriple`)
     and post-Bini (`ValidPostBini`), with exact `[10^M_lo, 10^M_hi]` brackets.
  2. Single-shot untwisted `Str_3^{⊗N}` benchmark (both multi-copy direct sum at
     `τ = 2.807` and single-matrix Schönhage conversion via `finite_schonhage` at
     `τ ∈ {2.807, 2.500, 2.371}`).

  Pure-kernel Lean 4.36.0, zero Mathlib, zero `sorry`, zero `native_decide`.
-/

import MatMul94.UniversalBounds

namespace MatMul94

/-! ### Generic symbolic-`Q` Pass Theorem 4.3 constructive witness engine -/

/-- Propagated `L_pass` upper bound starting from the exact linear-phase threshold `j0 = (c - 1) / 3`. -/
theorem pass_L_upper_j0 (c k : Nat) (hc : 2 ≤ c) (hk : (c - 1) / 3 ≤ k) :
    3 * (2 * L_pass c k - 1) * (c - 1) ^ (k - (c - 1) / 3)
      ≤ 2 * (3 * ((c - 1) / 3) + c) * (c + 2) ^ (k - (c - 1) / 3) := by
  let j0 := (c - 1) / 3
  have hup := exact_Lk_upper_from_j0 c j0 hc (k - j0)
  have hadd : j0 + (k - j0) = k := Nat.add_sub_of_le hk
  rw [hadd, L_pass_eq_add_one c hc j0 (Nat.le_refl j0)] at hup
  have heq : 3 * (j0 + 1) + c - 3 = 3 * j0 + c := by omega
  rw [heq] at hup
  have hLk := L_pass_pos c k
  have h32 : 3 * (2 * L_pass c k - 1) ≤ 2 * (3 * L_pass c k + c - 3) := by omega
  have s1 := Nat.mul_le_mul_right ((c - 1) ^ (k - j0)) h32
  have s2 := Nat.mul_le_mul_left 2 hup
  have eM : 2 * (3 * L_pass c k + c - 3) * (c - 1) ^ (k - j0)
      = 2 * ((3 * L_pass c k + c - 3) * (c - 1) ^ (k - j0)) := by ac_rfl
  have eR : 2 * ((3 * j0 + c) * (c + 2) ^ (k - j0))
      = 2 * (3 * j0 + c) * (c + 2) ^ (k - j0) := by ac_rfl
  exact Nat.le_trans s1 (eR ▸ (eM ▸ s2))

theorem log2Le_of_mul_add {a b x p1 p2 p_out q : Nat}
    (h : b * x ≤ a) (ha : Log2Le a p1 q) (hb : Log2Ge b p2 q) (hp : p1 ≤ p_out + p2) :
    Log2Le x p_out q := by
  unfold Log2Ge Log2Le at *
  have h1 : x ^ q * 2 ^ p2 ≤ 2 ^ p_out * 2 ^ p2 := by
    calc x ^ q * 2 ^ p2
        = 2 ^ p2 * x ^ q := Nat.mul_comm _ _
      _ ≤ b ^ q * x ^ q := Nat.mul_le_mul_right _ hb
      _ = (b * x) ^ q := (Nat.mul_pow b x q).symm
      _ ≤ a ^ q := Nat.pow_le_pow_left h q
      _ ≤ 2 ^ p1 := ha
      _ ≤ 2 ^ (p_out + p2) := Nat.pow_le_pow_right (by decide) hp
      _ = 2 ^ p_out * 2 ^ p2 := Nat.pow_add 2 _ _
  exact Nat.le_of_mul_le_mul_right h1 (Nat.two_pow_pos p2)

theorem pass_witness_core_of_log2
    {Q p q c d k lc2_lo lc2_hi lc_lo lc_hi lcm1_lo ld1_lo ld1_hi lcoef_hi l3_lo l1000_lo l1000_hi l1001_hi
     lw_lo lw_hi lr_lo lr_hi l2L_hi : Nat}
    (hQ : 0 < Q) (hc : 2 ≤ c) (hd : 1 ≤ d) (hk : 1 ≤ k) (hj0 : (c - 1) / 3 ≤ k)
    (hlc2_lo : Log2Ge (c + 2) lc2_lo Q) (hlc2_hi : Log2Le (c + 2) lc2_hi Q)
    (hlc_lo : Log2Ge c lc_lo Q) (hlc_hi : Log2Le c lc_hi Q)
    (hlcm1_lo : Log2Ge (c - 1) lcm1_lo Q)
    (hld1_lo : Log2Ge (d + 1) ld1_lo Q) (hld1_hi : Log2Le (d + 1) ld1_hi Q)
    (hlcoef_hi : Log2Le (2 * (3 * ((c - 1) / 3) + c)) lcoef_hi Q)
    (hl3_lo : Log2Ge 3 l3_lo Q)
    (hl1000_lo : Log2Ge 1000 l1000_lo Q) (hl1000_hi : Log2Le 1000 l1000_hi Q)
    (hl1001_hi : Log2Le 1001 l1001_hi Q)
    (hdiv1 : l1000_hi + ld1_hi ≤ 2 * d * lc2_lo)
    (hw_lo_c : lw_lo + ld1_hi + l1001_hi ≤ 2 * d * lc2_lo + l1000_lo)
    (hw_hi_c : 2 * d * lc2_hi ≤ lw_hi + ld1_lo)
    (hdiv2 : l1000_hi + 2 * d * lc_hi ≤ lw_lo)
    (hr_lo_c : lr_lo + 2 * d * lc_hi + l1001_hi ≤ lw_lo + l1000_lo)
    (hr_hi_c : lw_hi ≤ lr_hi + 2 * d * lc_lo)
    (h2L_c : lcoef_hi + (k - (c - 1) / 3) * lc2_hi ≤ l2L_hi + l3_lo + (k - (c - 1) / 3) * lcm1_lo)
    (hvalid : q * (6 * k * Q + 9 * lw_hi + 6 * d * l2L_hi) < p * (2 * lw_lo + 2 * k * lr_lo)) :
    ValidPassTriple p q c d k ∧
    Log2Ge (v_k_pass c d k) (2 * lw_lo + 2 * k * lr_lo) Q ∧
    Log2Le (v_k_pass c d k) (2 * lw_hi + 2 * k * lr_hi) Q ∧
    Log2Le (w_pass c d) lw_hi Q ∧
    Log2Le (E_k_pass c d k) (6 * k * Q + 9 * lw_hi + 6 * d * l2L_hi) Q := by
  have h1000_w : 1000 * (d + 1) ≤ (c + 2) ^ (2 * d) := by
    have hL := hl1000_hi.mul hld1_hi
    have hR := hlc2_lo.pow (2 * d)
    have hle := le_pow_of_log2 (a := 1) (b := 1) hL hR hQ (by simpa [Nat.mul_one] using hdiv1)
    simpa using hle
  have hw_pos : 1 ≤ w_pass c d := by
    unfold w_pass
    exact Nat.div_pos (Nat.le_trans (by omega) h1000_w) (by omega)
  have hw_ge : Log2Ge (w_pass c d) lw_lo Q := by
    have htight := nat_div_ge_tight (a := (c + 2) ^ (2 * d)) (b := d + 1) (m := 1000) (by omega) h1000_w
    have hA := hl1000_lo.mul (hlc2_lo.pow (2 * d))
    have hB := hl1001_hi.mul hld1_hi
    have hsub := Log2Ge.of_mul_ge (x := w_pass c d) htight hA hB (by omega)
    exact hsub.mono_exp (by omega)
  have hw_le : Log2Le (w_pass c d) lw_hi Q := by
    have hmul : (d + 1) * w_pass c d ≤ (c + 2) ^ (2 * d) := by
      unfold w_pass; rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
    exact log2Le_of_mul_add hmul (hlc2_hi.pow (2 * d)) hld1_lo hw_hi_c
  have h1000_r : 1000 * c ^ (2 * d) ≤ w_pass c d := by
    have hL := hl1000_hi.mul (hlc_hi.pow (2 * d))
    have hle := le_pow_of_log2 (a := 1) (b := 1) hL hw_ge hQ (by simpa [Nat.mul_one] using hdiv2)
    simpa using hle
  have hLam_pos : 1 ≤ Lambda_pass c d := by
    unfold Lambda_pass u_pass
    have hq1 : 1 ≤ w_pass c d / c ^ (2 * d) :=
      Nat.div_pos (Nat.le_trans (by
        have hcpos : 1 ≤ c ^ (2 * d) := pow_pos_of_pos (by omega) _
        omega) h1000_r) (pow_pos_of_pos (by omega) _)
    exact pow_pos_of_pos hq1 2
  have hr_ge : Log2Ge (w_pass c d / u_pass c d) lr_lo Q := by
    unfold u_pass
    have htight := nat_div_ge_tight (a := w_pass c d) (b := c ^ (2 * d)) (m := 1000)
      (pow_pos_of_pos (by omega) _) h1000_r
    have hA := hl1000_lo.mul hw_ge
    have hB := hl1001_hi.mul (hlc_hi.pow (2 * d))
    have hsub := Log2Ge.of_mul_ge htight hA hB (by omega)
    exact hsub.mono_exp (by omega)
  have hr_le : Log2Le (w_pass c d / u_pass c d) lr_hi Q := by
    unfold u_pass
    have hmul : c ^ (2 * d) * (w_pass c d / c ^ (2 * d)) ≤ w_pass c d := by
      rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
    exact log2Le_of_mul_add hmul hw_le (hlc_lo.pow (2 * d)) hr_hi_c
  have hLam_ge : Log2Ge (Lambda_pass c d) (2 * lr_lo) Q := hr_ge.pow 2
  have hLam_le : Log2Le (Lambda_pass c d) (2 * lr_hi) Q := hr_le.pow 2
  have hvk_ge : Log2Ge (v_k_pass c d k) (2 * lw_lo + 2 * k * lr_lo) Q := by
    unfold v_k_pass
    have h := (hw_ge.pow 2).mul (hLam_ge.pow k)
    have e : 2 * lw_lo + k * (2 * lr_lo) = 2 * lw_lo + 2 * k * lr_lo := by ac_rfl
    rwa [e] at h
  have hvk_le : Log2Le (v_k_pass c d k) (2 * lw_hi + 2 * k * lr_hi) Q := by
    unfold v_k_pass
    have h := (hw_le.pow 2).mul (hLam_le.pow k)
    have e : 2 * lw_hi + k * (2 * lr_hi) = 2 * lw_hi + 2 * k * lr_hi := by ac_rfl
    rwa [e] at h
  have h2L_le : Log2Le (2 * L_pass c k - 1) l2L_hi Q := by
    have hup := pass_L_upper_j0 c k hc hj0
    have hA := hlcoef_hi.mul (hlc2_hi.pow (k - (c - 1) / 3))
    have hB := hl3_lo.mul (hlcm1_lo.pow (k - (c - 1) / 3))
    have hmul : (3 * (c - 1) ^ (k - (c - 1) / 3)) * (2 * L_pass c k - 1)
        ≤ 2 * (3 * ((c - 1) / 3) + c) * (c + 2) ^ (k - (c - 1) / 3) := by
      have eL : (3 * (c - 1) ^ (k - (c - 1) / 3)) * (2 * L_pass c k - 1)
          = 3 * (2 * L_pass c k - 1) * (c - 1) ^ (k - (c - 1) / 3) := by ac_rfl
      rwa [eL]
    exact log2Le_of_mul_add hmul hA hB (by omega)
  have hEk_le : Log2Le (E_k_pass c d k) (6 * k * Q + 9 * lw_hi + 6 * d * l2L_hi) Q := by
    unfold E_k_pass
    have h64 : Log2Le (64 ^ k) (6 * k * Q) Q := by
      have h6 : Log2Le 64 (6 * Q) Q := by
        have : (64 : Nat) = 2 ^ 6 := by decide
        rw [this]; exact Log2Le.two_pow 6 Q
      have hp := h6.pow k
      have e : k * (6 * Q) = 6 * k * Q := by ac_rfl
      rwa [e] at hp
    exact (h64.mul (hw_le.pow 9)).mul (h2L_le.pow (6 * d))
  have hlt : E_k_pass c d k ^ q < v_k_pass c d k ^ p :=
    lt_pow_of_log2 hEk_le hvk_ge (by rw [Nat.mul_comm _ q, Nat.mul_comm _ p]; exact hvalid)
  exact ⟨⟨hc, hd, hk, hw_pos, hLam_pos, hlt⟩, hvk_ge, hvk_le, hw_le, hEk_le⟩

theorem pass_pre_witness_of_log2
    {Q p q c d k lc2_lo lc2_hi lc_lo lc_hi lcm1_lo ld1_lo ld1_hi lcoef_hi l3_lo l1000_lo l1000_hi l1001_hi
     lw_lo lw_hi lr_lo lr_hi l2L_hi M_lo M_hi : Nat}
    (hQ : 0 < Q) (hc : 2 ≤ c) (hd : 1 ≤ d) (hk : 1 ≤ k) (hj0 : (c - 1) / 3 ≤ k)
    (hlc2_lo : Log2Ge (c + 2) lc2_lo Q) (hlc2_hi : Log2Le (c + 2) lc2_hi Q)
    (hlc_lo : Log2Ge c lc_lo Q) (hlc_hi : Log2Le c lc_hi Q)
    (hlcm1_lo : Log2Ge (c - 1) lcm1_lo Q)
    (hld1_lo : Log2Ge (d + 1) ld1_lo Q) (hld1_hi : Log2Le (d + 1) ld1_hi Q)
    (hlcoef_hi : Log2Le (2 * (3 * ((c - 1) / 3) + c)) lcoef_hi Q)
    (hl3_lo : Log2Ge 3 l3_lo Q)
    (hl1000_lo : Log2Ge 1000 l1000_lo Q) (hl1000_hi : Log2Le 1000 l1000_hi Q)
    (hl1001_hi : Log2Le 1001 l1001_hi Q)
    (hdiv1 : l1000_hi + ld1_hi ≤ 2 * d * lc2_lo)
    (hw_lo_c : lw_lo + ld1_hi + l1001_hi ≤ 2 * d * lc2_lo + l1000_lo)
    (hw_hi_c : 2 * d * lc2_hi ≤ lw_hi + ld1_lo)
    (hdiv2 : l1000_hi + 2 * d * lc_hi ≤ lw_lo)
    (hr_lo_c : lr_lo + 2 * d * lc_hi + l1001_hi ≤ lw_lo + l1000_lo)
    (hr_hi_c : lw_hi ≤ lr_hi + 2 * d * lc_lo)
    (h2L_c : lcoef_hi + (k - (c - 1) / 3) * lc2_hi ≤ l2L_hi + l3_lo + (k - (c - 1) / 3) * lcm1_lo)
    (hvalid : q * (6 * k * Q + 9 * lw_hi + 6 * d * l2L_hi) < p * (2 * lw_lo + 2 * k * lr_lo))
    (hM_lo : M_lo * Q * 14267572528 ≤ (2 * lw_lo + 2 * k * lr_lo) * Q_SCALE)
    (hM_hi : (2 * lw_hi + 2 * k * lr_hi) * Q_SCALE ≤ M_hi * Q * 14267572527) :
    ValidPassTriple p q c d k ∧ 10 ^ M_lo ≤ v_k_pass c d k ∧ v_k_pass c d k ≤ 10 ^ M_hi := by
  rcases pass_witness_core_of_log2 hQ hc hd hk hj0 hlc2_lo hlc2_hi hlc_lo hlc_hi hlcm1_lo
    hld1_lo hld1_hi hlcoef_hi hl3_lo hl1000_lo hl1000_hi hl1001_hi
    hdiv1 hw_lo_c hw_hi_c hdiv2 hr_lo_c hr_hi_c h2L_c hvalid with ⟨hV, hge, hle, _, _⟩
  exact ⟨hV, pow10_le_of_log2 hge hQ hM_lo, le_pow10_of_log2 hle hQ hM_hi⟩

theorem pass_post_witness_of_log2
    {Q p q c d k h lc2_lo lc2_hi lc_lo lc_hi lcm1_lo ld1_lo ld1_hi lcoef_hi l3_lo l1000_lo l1000_hi l1001_hi
     lw_lo lw_hi lr_lo lr_hi l2L_hi lh1_hi l3d_hi P_lo P_hi : Nat}
    (hQ : 0 < Q) (hc : 2 ≤ c) (hd : 1 ≤ d) (hk : 1 ≤ k) (hh : 1 ≤ h) (hj0 : (c - 1) / 3 ≤ k)
    (hlc2_lo : Log2Ge (c + 2) lc2_lo Q) (hlc2_hi : Log2Le (c + 2) lc2_hi Q)
    (hlc_lo : Log2Ge c lc_lo Q) (hlc_hi : Log2Le c lc_hi Q)
    (hlcm1_lo : Log2Ge (c - 1) lcm1_lo Q)
    (hld1_lo : Log2Ge (d + 1) ld1_lo Q) (hld1_hi : Log2Le (d + 1) ld1_hi Q)
    (hlcoef_hi : Log2Le (2 * (3 * ((c - 1) / 3) + c)) lcoef_hi Q)
    (hl3_lo : Log2Ge 3 l3_lo Q)
    (hl1000_lo : Log2Ge 1000 l1000_lo Q) (hl1000_hi : Log2Le 1000 l1000_hi Q)
    (hl1001_hi : Log2Le 1001 l1001_hi Q)
    (hlh1_hi : Log2Le (h + 1) lh1_hi Q)
    (hl3d_hi : Log2Le (3 * (2 * d + 1)) l3d_hi Q)
    (hdiv1 : l1000_hi + ld1_hi ≤ 2 * d * lc2_lo)
    (hw_lo_c : lw_lo + ld1_hi + l1001_hi ≤ 2 * d * lc2_lo + l1000_lo)
    (hw_hi_c : 2 * d * lc2_hi ≤ lw_hi + ld1_lo)
    (hdiv2 : l1000_hi + 2 * d * lc_hi ≤ lw_lo)
    (hr_lo_c : lr_lo + 2 * d * lc_hi + l1001_hi ≤ lw_lo + l1000_lo)
    (hr_hi_c : lw_hi ≤ lr_hi + 2 * d * lc_lo)
    (h2L_c : lcoef_hi + (k - (c - 1) / 3) * lc2_hi ≤ l2L_hi + l3_lo + (k - (c - 1) / 3) * lcm1_lo)
    (hvalid : q * (6 * k * Q + 9 * lw_hi + 6 * d * l2L_hi) < p * (2 * lw_lo + 2 * k * lr_lo))
    (hpost : q * (lh1_hi + (2 * k - 1) * (l3d_hi + lw_hi) + h * (6 * k * Q + 9 * lw_hi + 6 * d * l2L_hi))
             < p * (h * (2 * lw_lo + 2 * k * lr_lo)))
    (hP_lo : P_lo * Q * 14267572528 ≤ (h * (2 * lw_lo + 2 * k * lr_lo)) * Q_SCALE)
    (hP_hi : (h * (2 * lw_hi + 2 * k * lr_hi)) * Q_SCALE ≤ P_hi * Q * 14267572527) :
    ValidPostBini p q c d k h ∧ 10 ^ P_lo ≤ (v_k_pass c d k) ^ h ∧ (v_k_pass c d k) ^ h ≤ 10 ^ P_hi := by
  rcases pass_witness_core_of_log2 hQ hc hd hk hj0 hlc2_lo hlc2_hi hlc_lo hlc_hi hlcm1_lo
    hld1_lo hld1_hi hlcoef_hi hl3_lo hl1000_lo hl1000_hi hl1001_hi
    hdiv1 hw_lo_c hw_hi_c hdiv2 hr_lo_c hr_hi_c h2L_c hvalid with ⟨hV, hvk_ge, hvk_le, hw_le, hEk_le⟩
  have hBini_le : h * (3 * (2 * d + 1) * w_pass c d - 2) ^ (2 * k - 1) + 1
      ≤ (h + 1) * (3 * (2 * d + 1) * w_pass c d) ^ (2 * k - 1) := by
    have h1 : (3 * (2 * d + 1) * w_pass c d - 2) ^ (2 * k - 1)
        ≤ (3 * (2 * d + 1) * w_pass c d) ^ (2 * k - 1) := Nat.pow_le_pow_left (by omega) _
    have hpos : 1 ≤ (3 * (2 * d + 1) * w_pass c d) ^ (2 * k - 1) :=
      pow_pos_of_pos (Nat.mul_pos (by omega) hV.2.2.2.1) _
    have hm := Nat.mul_le_mul_left h h1
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hBini_log : Log2Le (h * (3 * (2 * d + 1) * w_pass c d - 2) ^ (2 * k - 1) + 1)
      (lh1_hi + (2 * k - 1) * (l3d_hi + lw_hi)) Q :=
    (hlh1_hi.mul ((hl3d_hi.mul hw_le).pow (2 * k - 1))).mono_left hBini_le
  have hLHS_log := hBini_log.mul (hEk_le.pow h)
  have hRHS_log := hvk_ge.pow h
  have hlt_pb : ((h * (3 * (2 * d + 1) * w_pass c d - 2) ^ (2 * k - 1) + 1) * E_k_pass c d k ^ h) ^ q
      < (v_k_pass c d k ^ h) ^ p :=
    lt_pow_of_log2 hLHS_log hRHS_log (by rw [Nat.mul_comm _ q, Nat.mul_comm _ p]; exact hpost)
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hlt_pb
  exact ⟨⟨hV, hh, hlt_pb⟩, pow10_le_of_log2 (hvk_ge.pow h) hQ hP_lo, le_pow10_of_log2 (hvk_le.pow h) hQ hP_hi⟩

/-! ### Shared `Q_SCALE = 2^32` dyadic certificates for constructive witnesses -/

private theorem w_ge_3 : Log2Ge 3 6807362105 Q_SCALE := log2Ge_Q 3 6807362105 (by decide)
private theorem w_ge_4 : Log2Ge 4 8589934592 Q_SCALE := log2Ge_Q 4 8589934592 (by decide)
private theorem w_ge_5 : Log2Ge 5 9972605231 Q_SCALE := log2Ge_Q 5 9972605231 (by decide)
private theorem w_ge_6 : Log2Ge 6 11102329401 Q_SCALE := log2Ge_Q 6 11102329401 (by decide)
private theorem w_ge_7 : Log2Ge 7 12057497578 Q_SCALE := log2Ge_Q 7 12057497578 (by decide)
private theorem w_ge_8 : Log2Ge 8 12884901888 Q_SCALE := log2Ge_Q 8 12884901888 (by decide)
private theorem w_ge_9 : Log2Ge 9 13614724211 Q_SCALE := log2Ge_Q 9 13614724211 (by decide)
private theorem w_ge_10 : Log2Ge 10 14267572527 Q_SCALE := log2Ge_Q 10 14267572527 (by decide)
private theorem w_ge_11 : Log2Ge 11 14858145664 Q_SCALE := log2Ge_Q 11 14858145664 (by decide)
private theorem w_ge_12 : Log2Ge 12 15397296697 Q_SCALE := log2Ge_Q 12 15397296697 (by decide)
private theorem w_ge_14 : Log2Ge 14 16352464874 Q_SCALE := log2Ge_Q 14 16352464874 (by decide)
private theorem w_ge_20 : Log2Ge 20 18562539823 Q_SCALE := log2Ge_Q 20 18562539823 (by decide)
private theorem w_ge_21 : Log2Ge 21 18864859684 Q_SCALE := log2Ge_Q 21 18864859684 (by decide)
private theorem w_ge_23 : Log2Ge 23 19428550662 Q_SCALE := log2Ge_Q 23 19428550662 (by decide)
private theorem w_ge_24 : Log2Ge 24 19692263993 Q_SCALE := log2Ge_Q 24 19692263993 (by decide)
private theorem w_ge_26 : Log2Ge 26 20188234866 Q_SCALE := log2Ge_Q 26 20188234866 (by decide)
private theorem w_ge_35 : Log2Ge 35 22030102809 Q_SCALE := log2Ge_Q 35 22030102809 (by decide)
private theorem w_ge_36 : Log2Ge 36 22204658803 Q_SCALE := log2Ge_Q 36 22204658803 (by decide)
private theorem w_ge_38 : Log2Ge 38 22539677042 Q_SCALE := log2Ge_Q 38 22539677042 (by decide)
private theorem w_ge_41 : Log2Ge 41 23010510646 Q_SCALE := log2Ge_Q 41 23010510646 (by decide)
private theorem w_ge_42 : Log2Ge 42 23159826980 Q_SCALE := log2Ge_Q 42 23159826980 (by decide)
private theorem w_ge_44 : Log2Ge 44 23448080256 Q_SCALE := log2Ge_Q 44 23448080256 (by decide)
private theorem w_ge_50 : Log2Ge 50 24240177758 Q_SCALE := log2Ge_Q 50 24240177758 (by decide)
private theorem w_ge_51 : Log2Ge 51 24362881332 Q_SCALE := log2Ge_Q 51 24362881332 (by decide)
private theorem w_ge_53 : Log2Ge 53 24601231026 Q_SCALE := log2Ge_Q 53 24601231026 (by decide)
private theorem w_ge_56 : Log2Ge 56 24942399466 Q_SCALE := log2Ge_Q 56 24942399466 (by decide)
private theorem w_ge_57 : Log2Ge 57 25052071852 Q_SCALE := log2Ge_Q 57 25052071852 (by decide)
private theorem w_ge_59 : Log2Ge 59 25265759511 Q_SCALE := log2Ge_Q 59 25265759511 (by decide)
private theorem w_ge_140 : Log2Ge 140 30620037401 Q_SCALE := log2Ge_Q 140 30620037401 (by decide)
private theorem w_ge_208 : Log2Ge 208 33073136754 Q_SCALE := log2Ge_Q 208 33073136754 (by decide)
private theorem w_ge_220 : Log2Ge 220 33420685488 Q_SCALE := log2Ge_Q 220 33420685488 (by decide)
private theorem w_ge_254 : Log2Ge 254 34311139467 Q_SCALE := log2Ge_Q 254 34311139467 (by decide)
private theorem w_ge_255 : Log2Ge 255 34335486563 Q_SCALE := log2Ge_Q 255 34335486563 (by decide)
private theorem w_ge_257 : Log2Ge 257 34383895622 Q_SCALE := log2Ge_Q 257 34383895622 (by decide)
private theorem w_ge_303 : Log2Ge 303 35404162674 Q_SCALE := log2Ge_Q 303 35404162674 (by decide)
private theorem w_ge_304 : Log2Ge 304 35424578930 Q_SCALE := log2Ge_Q 304 35424578930 (by decide)
private theorem w_ge_306 : Log2Ge 306 35465210734 Q_SCALE := log2Ge_Q 306 35465210734 (by decide)
private theorem w_ge_336 : Log2Ge 336 36044728868 Q_SCALE := log2Ge_Q 336 36044728868 (by decide)
private theorem w_ge_720 : Log2Ge 720 40767198627 Q_SCALE := log2Ge_Q 720 40767198627 (by decide)
private theorem w_ge_1000 : Log2Ge 1000 42802717581 Q_SCALE := log2Ge_Q 1000 42802717581 (by decide)
private theorem w_ge_1074 : Log2Ge 1074 43245073414 Q_SCALE := log2Ge_Q 1074 43245073414 (by decide)
private theorem w_ge_2545 : Log2Ge 2545 48590897501 Q_SCALE := log2Ge_Q 2545 48590897501 (by decide)
private theorem w_ge_2546 : Log2Ge 2546 48593331729 Q_SCALE := log2Ge_Q 2546 48593331729 (by decide)
private theorem w_ge_2548 : Log2Ge 2548 48598197319 Q_SCALE := log2Ge_Q 2548 48598197319 (by decide)
private theorem w_ge_3031 : Log2Ge 3031 49673779856 Q_SCALE := log2Ge_Q 3031 49673779856 (by decide)
private theorem w_ge_3032 : Log2Ge 3032 49675823837 Q_SCALE := log2Ge_Q 3032 49675823837 (by decide)
private theorem w_ge_3034 : Log2Ge 3034 49679909777 Q_SCALE := log2Ge_Q 3034 49679909777 (by decide)
private theorem w_ge_3393 : Log2Ge 3393 50372861280 Q_SCALE := log2Ge_Q 3393 50372861280 (by decide)
private theorem w_ge_5053 : Log2Ge 5053 52840658220 Q_SCALE := log2Ge_Q 5053 52840658220 (by decide)
private theorem w_ge_10918 : Log2Ge 10918 57614499411 Q_SCALE := log2Ge_Q 10918 57614499411 (by decide)
private theorem w_ge_12870 : Log2Ge 12870 58633709974 Q_SCALE := log2Ge_Q 12870 58633709974 (by decide)
private theorem w_ge_16022 : Log2Ge 16022 59991100864 Q_SCALE := log2Ge_Q 16022 59991100864 (by decide)
private theorem w_ge_23004 : Log2Ge 23004 62232345772 Q_SCALE := log2Ge_Q 23004 62232345772 (by decide)
private theorem w_ge_34247 : Log2Ge 34247 64698055884 Q_SCALE := log2Ge_Q 34247 64698055884 (by decide)
private theorem w_ge_705432 : Log2Ge 705432 83443258115 Q_SCALE := log2Ge_Q 705432 83443258115 (by decide)
private theorem w_ge_763003 : Log2Ge 763003 83929369851 Q_SCALE := log2Ge_Q 763003 83929369851 (by decide)
private theorem w_ge_1107001 : Log2Ge 1107001 86235320143 Q_SCALE := log2Ge_Q 1107001 86235320143 (by decide)
private theorem w_ge_102600001 : Log2Ge 102600001 114299626056 Q_SCALE := log2Ge_Q 102600001 114299626056 (by decide)
private theorem w_ge_149000001 : Log2Ge 149000001 116611527904 Q_SCALE := log2Ge_Q 149000001 116611527904 (by decide)
private theorem w_le_3 : Log2Le 3 6807362106 Q_SCALE := log2Le_Q 3 6807362106 (by decide)
private theorem w_le_5 : Log2Le 5 9972605232 Q_SCALE := log2Le_Q 5 9972605232 (by decide)
private theorem w_le_6 : Log2Le 6 11102329402 Q_SCALE := log2Le_Q 6 11102329402 (by decide)
private theorem w_le_7 : Log2Le 7 12057497579 Q_SCALE := log2Le_Q 7 12057497579 (by decide)
private theorem w_le_8 : Log2Le 8 12884901888 Q_SCALE := log2Le_Q 8 12884901888 (by decide)
private theorem w_le_10 : Log2Le 10 14267572528 Q_SCALE := log2Le_Q 10 14267572528 (by decide)
private theorem w_le_12 : Log2Le 12 15397296698 Q_SCALE := log2Le_Q 12 15397296698 (by decide)
private theorem w_le_14 : Log2Le 14 16352464875 Q_SCALE := log2Le_Q 14 16352464875 (by decide)
private theorem w_le_16 : Log2Le 16 17179869184 Q_SCALE := log2Le_Q 16 17179869184 (by decide)
private theorem w_le_18 : Log2Le 18 17909691508 Q_SCALE := log2Le_Q 18 17909691508 (by decide)
private theorem w_le_21 : Log2Le 21 18864859685 Q_SCALE := log2Le_Q 21 18864859685 (by decide)
private theorem w_le_23 : Log2Le 23 19428550663 Q_SCALE := log2Le_Q 23 19428550663 (by decide)
private theorem w_le_24 : Log2Le 24 19692263994 Q_SCALE := log2Le_Q 24 19692263994 (by decide)
private theorem w_le_26 : Log2Le 26 20188234867 Q_SCALE := log2Le_Q 26 20188234867 (by decide)
private theorem w_le_36 : Log2Le 36 22204658804 Q_SCALE := log2Le_Q 36 22204658804 (by decide)
private theorem w_le_38 : Log2Le 38 22539677043 Q_SCALE := log2Le_Q 38 22539677043 (by decide)
private theorem w_le_42 : Log2Le 42 23159826981 Q_SCALE := log2Le_Q 42 23159826981 (by decide)
private theorem w_le_44 : Log2Le 44 23448080257 Q_SCALE := log2Le_Q 44 23448080257 (by decide)
private theorem w_le_51 : Log2Le 51 24362881333 Q_SCALE := log2Le_Q 51 24362881333 (by decide)
private theorem w_le_53 : Log2Le 53 24601231027 Q_SCALE := log2Le_Q 53 24601231027 (by decide)
private theorem w_le_57 : Log2Le 57 25052071853 Q_SCALE := log2Le_Q 57 25052071853 (by decide)
private theorem w_le_59 : Log2Le 59 25265759512 Q_SCALE := log2Le_Q 59 25265759512 (by decide)
private theorem w_le_62 : Log2Le 62 25573078428 Q_SCALE := log2Le_Q 62 25573078428 (by decide)
private theorem w_le_78 : Log2Le 78 26995596973 Q_SCALE := log2Le_Q 78 26995596973 (by decide)
private theorem w_le_90 : Log2Le 90 27882296740 Q_SCALE := log2Le_Q 90 27882296740 (by decide)
private theorem w_le_91 : Log2Le 91 27950765149 Q_SCALE := log2Le_Q 91 27950765149 (by decide)
private theorem w_le_97 : Log2Le 97 28346409814 Q_SCALE := log2Le_Q 97 28346409814 (by decide)
private theorem w_le_138 : Log2Le 138 30530880065 Q_SCALE := log2Le_Q 138 30530880065 (by decide)
private theorem w_le_140 : Log2Le 140 30620037402 Q_SCALE := log2Le_Q 140 30620037402 (by decide)
private theorem w_le_162 : Log2Le 162 31524415720 Q_SCALE := log2Le_Q 162 31524415720 (by decide)
private theorem w_le_198 : Log2Le 198 32767837173 Q_SCALE := log2Le_Q 198 32767837173 (by decide)
private theorem w_le_208 : Log2Le 208 33073136755 Q_SCALE := log2Le_Q 208 33073136755 (by decide)
private theorem w_le_220 : Log2Le 220 33420685489 Q_SCALE := log2Le_Q 220 33420685489 (by decide)
private theorem w_le_222 : Log2Le 222 33476761238 Q_SCALE := log2Le_Q 222 33476761238 (by decide)
private theorem w_le_255 : Log2Le 255 34335486564 Q_SCALE := log2Le_Q 255 34335486564 (by decide)
private theorem w_le_257 : Log2Le 257 34383895623 Q_SCALE := log2Le_Q 257 34383895623 (by decide)
private theorem w_le_304 : Log2Le 304 35424578931 Q_SCALE := log2Le_Q 304 35424578931 (by decide)
private theorem w_le_306 : Log2Le 306 35465210735 Q_SCALE := log2Le_Q 306 35465210735 (by decide)
private theorem w_le_326 : Log2Le 326 35857514386 Q_SCALE := log2Le_Q 326 35857514386 (by decide)
private theorem w_le_336 : Log2Le 336 36044728869 Q_SCALE := log2Le_Q 336 36044728869 (by decide)
private theorem w_le_341 : Log2Le 341 36136256796 Q_SCALE := log2Le_Q 341 36136256796 (by decide)
private theorem w_le_720 : Log2Le 720 40767198628 Q_SCALE := log2Le_Q 720 40767198628 (by decide)
private theorem w_le_1000 : Log2Le 1000 42802717582 Q_SCALE := log2Le_Q 1000 42802717582 (by decide)
private theorem w_le_1001 : Log2Le 1001 42808910814 Q_SCALE := log2Le_Q 1001 42808910814 (by decide)
private theorem w_le_1014 : Log2Le 1014 42888864543 Q_SCALE := log2Le_Q 1014 42888864543 (by decide)
private theorem w_le_1074 : Log2Le 1074 43245073415 Q_SCALE := log2Le_Q 1074 43245073415 (by decide)
private theorem w_le_1214 : Log2Le 1214 44004313803 Q_SCALE := log2Le_Q 1214 44004313803 (by decide)
private theorem w_le_1317 : Log2Le 1317 44508916300 Q_SCALE := log2Le_Q 1317 44508916300 (by decide)
private theorem w_le_1601 : Log2Le 1601 45718885734 Q_SCALE := log2Le_Q 1601 45718885734 (by decide)
private theorem w_le_2013 : Log2Le 2013 47137830677 Q_SCALE := log2Le_Q 2013 47137830677 (by decide)
private theorem w_le_2546 : Log2Le 2546 48593331730 Q_SCALE := log2Le_Q 2546 48593331730 (by decide)
private theorem w_le_2548 : Log2Le 2548 48598197320 Q_SCALE := log2Le_Q 2548 48598197320 (by decide)
private theorem w_le_3032 : Log2Le 3032 49675823838 Q_SCALE := log2Le_Q 3032 49675823838 (by decide)
private theorem w_le_3034 : Log2Le 3034 49679909778 Q_SCALE := log2Le_Q 3034 49679909778 (by decide)
private theorem w_le_3393 : Log2Le 3393 50372861281 Q_SCALE := log2Le_Q 3393 50372861281 (by decide)
private theorem w_le_5053 : Log2Le 5053 52840658221 Q_SCALE := log2Le_Q 5053 52840658221 (by decide)
private theorem w_le_5412 : Log2Le 5412 53265953010 Q_SCALE := log2Le_Q 5412 53265953010 (by decide)
private theorem w_le_5462 : Log2Le 5462 53322936380 Q_SCALE := log2Le_Q 5462 53322936380 (by decide)
private theorem w_le_6441 : Log2Le 6441 54344517449 Q_SCALE := log2Le_Q 6441 54344517449 (by decide)
private theorem w_le_10180 : Log2Le 10180 57180832094 Q_SCALE := log2Le_Q 10180 57180832094 (by decide)
private theorem w_le_10918 : Log2Le 10918 57614499412 Q_SCALE := log2Le_Q 10918 57614499412 (by decide)
private theorem w_le_11699 : Log2Le 11699 58042607214 Q_SCALE := log2Le_Q 11699 58042607214 (by decide)
private theorem w_le_12124 : Log2Le 12124 58263714449 Q_SCALE := log2Le_Q 12124 58263714449 (by decide)
private theorem w_le_12870 : Log2Le 12870 58633709975 Q_SCALE := log2Le_Q 12870 58633709975 (by decide)
private theorem w_le_16022 : Log2Le 16022 59991100865 Q_SCALE := log2Le_Q 16022 59991100865 (by decide)
private theorem w_le_23004 : Log2Le 23004 62232345773 Q_SCALE := log2Le_Q 23004 62232345773 (by decide)
private theorem w_le_25739 : Log2Le 25739 62928436538 Q_SCALE := log2Le_Q 25739 62928436538 (by decide)
private theorem w_le_30315 : Log2Le 30315 63942374459 Q_SCALE := log2Le_Q 30315 63942374459 (by decide)
private theorem w_le_34247 : Log2Le 34247 64698055885 Q_SCALE := log2Le_Q 34247 64698055885 (by decide)
private theorem w_le_69566 : Log2Le 69566 69089250866 Q_SCALE := log2Le_Q 69566 69089250866 (by decide)
private theorem w_le_96129 : Log2Le 96129 71093236895 Q_SCALE := log2Le_Q 96129 71093236895 (by decide)
private theorem w_le_205479 : Log2Le 205479 75800294821 Q_SCALE := log2Le_Q 205479 75800294821 (by decide)
private theorem w_le_391256 : Log2Le 391256 79790843075 Q_SCALE := log2Le_Q 391256 79790843075 (by decide)
private theorem w_le_705432 : Log2Le 705432 83443258116 Q_SCALE := log2Le_Q 705432 83443258116 (by decide)
private theorem w_le_763003 : Log2Le 763003 83929369852 Q_SCALE := log2Le_Q 763003 83929369852 (by decide)
private theorem w_le_1107001 : Log2Le 1107001 86235320144 Q_SCALE := log2Le_Q 1107001 86235320144 (by decide)
private theorem w_le_1312741 : Log2Le 1312741 87291563324 Q_SCALE := log2Le_Q 1312741 87291563324 (by decide)
private theorem w_le_1410863 : Log2Le 1410863 87738221020 Q_SCALE := log2Le_Q 1410863 87738221020 (by decide)
private theorem w_le_6642003 : Log2Le 6642003 97337646747 Q_SCALE := log2Le_Q 6642003 97337646747 (by decide)
private theorem w_le_54300809 : Log2Le 54300809 110356909869 Q_SCALE := log2Le_Q 54300809 110356909869 (by decide)
private theorem w_le_102600001 : Log2Le 102600001 114299626057 Q_SCALE := log2Le_Q 102600001 114299626057 (by decide)
private theorem w_le_146024425 : Log2Le 146024425 116486533033 Q_SCALE := log2Le_Q 146024425 116486533033 (by decide)
private theorem w_le_149000001 : Log2Le 149000001 116611527905 Q_SCALE := log2Le_Q 149000001 116611527905 (by decide)
private theorem w_le_894000003 : Log2Le 894000003 127713857286 Q_SCALE := log2Le_Q 894000003 127713857286 (by decide)

/-! ### Verified Pass Theorem 4.3 Pre-Bini constructive witnesses (all 8 targets) -/

theorem witness_pre_2800 :
    ValidPassTriple 14 5 6 139 127 ∧
    10 ^ 8774 ≤ v_k_pass 6 139 127 ∧ v_k_pass 6 139 127 ≤ 10 ^ 8775 :=
  pass_pre_witness_of_log2 (Q := Q_SCALE) (p := 14) (q := 5) (c := 6) (d := 139) (k := 127)
    (lw_lo := 3551376494229) (lw_hi := 3551382687463) (lr_lo := 464922727240) (lr_hi := 464935113985)
    (l2L_hi := 378051708185) (M_lo := 8774) (M_hi := 8775)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    w_ge_8 w_le_8 w_ge_6 w_le_6 w_ge_5 w_ge_140 w_le_140 w_le_18
    w_ge_3 w_ge_1000 w_le_1000 w_le_1001
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem witness_pre_2695 :
    ValidPassTriple 539 200 6 207 188 ∧
    10 ^ 19319 ≤ v_k_pass 6 207 188 ∧ v_k_pass 6 207 188 ≤ 10 ^ 19320 :=
  pass_pre_witness_of_log2 (Q := Q_SCALE) (p := 539) (q := 200) (c := 6) (d := 207) (k := 188)
    (lw_lo := 5301270051644) (lw_hi := 5301276244878) (lr_lo := 704899485983) (lr_hi := 704911872864)
    (l2L_hi := 555701804262) (M_lo := 19319) (M_hi := 19320)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    w_ge_8 w_le_8 w_ge_6 w_le_6 w_ge_5 w_ge_208 w_le_208 w_le_18
    w_ge_3 w_ge_1000 w_le_1000 w_le_1001
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem witness_pre_2500 :
    ValidPassTriple 5 2 12 719 758 ∧
    10 ^ 144902 ≤ v_k_pass 12 719 758 ∧ v_k_pass 12 719 758 ≤ 10 ^ 144904 :=
  pass_pre_witness_of_log2 (Q := Q_SCALE) (p := 5) (q := 2) (c := 12) (d := 719) (k := 758)
    (lw_lo := 23474071096951) (lw_hi := 23474077291623) (lr_lo := 1332752251994) (lr_hi := 1332764641337)
    (l2L_hi := 1144563469181) (M_lo := 144902) (M_hi := 144904)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    w_ge_14 w_le_14 w_ge_12 w_le_12 w_ge_11 w_ge_720 w_le_720 w_le_42
    w_ge_3 w_ge_1000 w_le_1000 w_le_1001
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem witness_pre_2371 :
    ValidPassTriple 2371 1000 24 3392 3939 ∧
    10 ^ 1849208 ≤ v_k_pass 24 3392 3939 ∧ v_k_pass 24 3392 3939 ≤ 10 ^ 1849216 :=
  pass_pre_witness_of_log2 (Q := Q_SCALE) (p := 2371) (q := 1000) (c := 24) (d := 3392) (k := 3939)
    (lw_lo := 136906606276430) (lw_hi := 136906612476448) (lr_lo := 3314281147901) (lr_hi := 3314293547936)
    (l2L_hi := 3008153228695) (M_lo := 1849208) (M_hi := 1849216)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    w_ge_26 w_le_26 w_ge_24 w_le_24 w_ge_23 w_ge_3393 w_le_3393 w_le_90
    w_ge_3 w_ge_1000 w_le_1000 w_le_1001
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem witness_pre_2321 :
    ValidPassTriple 2321 1000 42 10917 13349 ∧
    10 ^ 11740965 ≤ v_k_pass 42 10917 13349 ∧ v_k_pass 42 10917 13349 ≤ 10 ^ 11740990 :=
  pass_pre_witness_of_log2 (Q := Q_SCALE) (p := 2321) (q := 1000) (c := 42) (d := 10917) (k := 13349)
    (lw_lo := 511907763616859) (lw_hi := 511907769831927) (lr_lo := 6236095120472) (lr_hi := 6236107550607)
    (l2L_hi := 5860145385911) (M_lo := 11740965) (M_hi := 11740990)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    w_ge_44 w_le_44 w_ge_42 w_le_42 w_ge_41 w_ge_10918 w_le_10918 w_le_162
    w_ge_3 w_ge_1000 w_le_1000 w_le_1001
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem witness_pre_2300 :
    ValidPassTriple 23 10 57 23003 28481 ∧
    10 ^ 39163465 ≤ v_k_pass 57 23003 28481 ∧ v_k_pass 57 23003 28481 ≤ 10 ^ 39163516 :=
  pass_pre_witness_of_log2 (Q := Q_SCALE) (p := 23) (q := 10) (c := 57) (d := 23003) (k := 28481)
    (lw_lo := 1162314293524060) (lw_hi := 1162314299763300) (lr_lo := 9768669661709) (lr_hi := 9768682140188)
    (l2L_hi := 9230466388431) (M_lo := 39163465) (M_hi := 39163516)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    w_ge_59 w_le_59 w_ge_57 w_le_57 w_ge_56 w_ge_23004 w_le_23004 w_le_222
    w_ge_3 w_ge_1000 w_le_1000 w_le_1001
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem witness_pre_2260 :
    ValidPassTriple 113 50 304 763002 1024110 ∧
    10 ^ 8896730215 ≤ v_k_pass 304 763002 1024110 ∧ v_k_pass 304 763002 1024110 ≤ 10 ^ 8896732433 :=
  pass_pre_witness_of_log2 (Q := Q_SCALE) (p := 113) (q := 50) (c := 304) (d := 763002) (k := 1024110)
    (lw_lo := 54119969505363851) (lw_hi := 54119969513083089) (lr_lo := 61920352148894) (lr_hi := 61920367587369)
    (l2L_hi := 62550960848247) (M_lo := 8896730215) (M_hi := 8896732433)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    w_ge_306 w_le_306 w_ge_304 w_le_304 w_ge_303 w_ge_763003 w_le_763003 w_le_1214
    w_ge_3 w_ge_1000 w_le_1000 w_le_1001
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem witness_pre_2251 :
    ValidPassTriple 2251 1000 3032 102600000 143826653 ∧
    10 ^ 16903086653712 ≤ v_k_pass 3032 102600000 143826653 ∧ v_k_pass 3032 102600000 143826653 ≤ 10 ^ 16903095178837 :=
  pass_pre_witness_of_log2 (Q := Q_SCALE) (p := 2251) (q := 1000) (c := 3032) (d := 102600000) (k := 143826653)
    (lw_lo := 10194317371934580710) (lw_hi := 10194317372145973944) (lr_lo := 838320370787477) (lr_hi := 838320793573944)
    (l2L_hi := 881691429542190) (M_lo := 16903086653712) (M_hi := 16903095178837)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    w_ge_3034 w_le_3034 w_ge_3032 w_le_3032 w_ge_3031 w_ge_102600001 w_le_102600001 w_le_12124
    w_ge_3 w_ge_1000 w_le_1000 w_le_1001
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)


/-! ### Verified Pass Theorem 4.3 Post-Bini constructive witnesses (all 8 targets) -/

theorem witness_post_2800 :
    ValidPostBini 14 5 5 219 157 61 ∧
    10 ^ 1225923 ≤ (v_k_pass 5 219 157) ^ 61 ∧ (v_k_pass 5 219 157) ^ 61 ≤ 10 ^ 1225941 :=
  pass_post_witness_of_log2 (Q := Q_SCALE) (p := 14) (q := 5) (c := 5) (d := 219) (k := 157) (h := 61)
    (lw_lo := 5247757060442) (lw_hi := 5247763254114) (lr_lo := 879749775593) (lr_hi := 879762162936)
    (l2L_hi := 551312333051) (P_lo := 1225923) (P_hi := 1225941)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    w_ge_7 w_le_7 w_ge_5 w_le_5 w_ge_4 w_ge_220 w_le_220 w_le_16
    w_ge_3 w_ge_1000 w_le_1000 w_le_1001 w_le_62 w_le_1317
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem witness_post_2695 :
    ValidPostBini 539 200 6 335 259 96 ∧
    10 ^ 4152694 ≤ (v_k_pass 6 335 259) ^ 96 ∧ (v_k_pass 6 335 259) ^ 96 ≤ 10 ^ 4152738 :=
  pass_post_witness_of_log2 (Q := Q_SCALE) (p := 539) (q := 200) (c := 6) (d := 335) (k := 259) (h := 96)
    (lw_lo := 8596833342858) (lw_hi := 8596839536092) (lr_lo := 1158266450285) (lr_hi := 1158278837422)
    (l2L_hi := 762474866909) (P_lo := 4152694) (P_hi := 4152738)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    w_ge_8 w_le_8 w_ge_6 w_le_6 w_ge_5 w_ge_336 w_le_336 w_le_18
    w_ge_3 w_ge_1000 w_le_1000 w_le_1001 w_le_97 w_le_2013
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem witness_post_2500 :
    ValidPostBini 5 2 10 1073 995 325 ∧
    10 ^ 109440186 ≤ (v_k_pass 10 1073 995) ^ 325 ∧ (v_k_pass 10 1073 995) ^ 325 ≤ 10 ^ 109440749 :=
  pass_post_witness_of_log2 (Q := Q_SCALE) (p := 5) (q := 2) (c := 10) (d := 1073) (k := 995) (h := 325)
    (lw_lo := 32999347445114) (lw_hi := 32999353640494) (lr_lo := 2381130606793) (lr_hi := 2381142997552)
    (l2L_hi := 1784044222042) (P_lo := 109440186) (P_hi := 109440749)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    w_ge_12 w_le_12 w_ge_10 w_le_10 w_ge_9 w_ge_1074 w_le_1074 w_le_38
    w_ge_3 w_ge_1000 w_le_1000 w_le_1001 w_le_326 w_le_6441
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem witness_post_2371 :
    ValidPostBini 2371 1000 21 5052 5469 1600 ∧
    10 ^ 6965405961 ≤ (v_k_pass 21 5052 5469) ^ 1600 ∧ (v_k_pass 21 5052 5469) ^ 1600 ≤ 10 ^ 6965421182 :=
  pass_post_witness_of_log2 (Q := Q_SCALE) (p := 2371) (q := 1000) (c := 21) (d := 5052) (k := 5469) (h := 1600)
    (lw_lo := 196253229037394) (lw_hi := 196253235240732) (lr_lo := 5642680586921) (lr_hi := 5642692993596)
    (l2L_hi := 4751205453788) (P_lo := 6965405961) (P_hi := 6965421182)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    w_ge_23 w_le_23 w_ge_21 w_le_21 w_ge_20 w_ge_5053 w_le_5053 w_le_78
    w_ge_3 w_ge_1000 w_le_1000 w_le_1001 w_le_1601 w_le_30315
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem witness_post_2321 :
    ValidPostBini 2321 1000 36 16021 17735 5411 ∧
    10 ^ 144143748589 ≤ (v_k_pass 36 16021 17735) ^ 5411 ∧ (v_k_pass 36 16021 17735) ^ 5411 ≤ 10 ^ 144143916090 :=
  pass_post_witness_of_log2 (Q := Q_SCALE) (p := 2321) (q := 1000) (c := 36) (d := 16021) (k := 17735) (h := 5411)
    (lw_lo := 722156334485666) (lw_hi := 722156340710942) (lr_lo := 10674650894665) (lr_hi := 10674663345216)
    (l2L_hi := 9055417241376) (P_lo := 144143748589) (P_hi := 144143916090)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    w_ge_38 w_le_38 w_ge_36 w_le_36 w_ge_35 w_ge_16022 w_le_16022 w_le_138
    w_ge_3 w_ge_1000 w_le_1000 w_le_1001 w_le_5412 w_le_96129
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem witness_post_2300 :
    ValidPostBini 23 10 51 34246 39069 11698 ∧
    10 ^ 1044488581676 ≤ (v_k_pass 51 34246 39069) ^ 11698 ∧ (v_k_pass 51 34246 39069) ^ 11698 ≤ 10 ^ 1044489384081 :=
  pass_post_witness_of_log2 (Q := Q_SCALE) (p := 23) (q := 10) (c := 51) (d := 34246) (k := 39069) (h := 11698)
    (lw_lo := 1684922811183674) (lw_hi := 1684922817445400) (lr_lo := 16260336730605) (lr_hi := 16260349254056)
    (l2L_hi := 14126173789325) (P_lo := 1044488581676) (P_hi := 1044489384081)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    w_ge_53 w_le_53 w_ge_51 w_le_51 w_ge_50 w_ge_34247 w_le_34247 w_le_198
    w_ge_3 w_ge_1000 w_le_1000 w_le_1001 w_le_11699 w_le_205479
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem witness_post_2260 :
    ValidPostBini 113 50 255 1107000 1378300 391255 ∧
    10 ^ 8099572807271912 ≤ (v_k_pass 255 1107000 1378300) ^ 391255 ∧ (v_k_pass 255 1107000 1378300) ^ 391255 ≤ 10 ^ 8099574078901871 :=
  pass_post_witness_of_log2 (Q := Q_SCALE) (p := 113) (q := 50) (c := 255) (d := 1107000) (k := 1378300) (h := 391255)
    (lw_lo := 76125858665594623) (lw_hi := 76125858674001857) (lr_lo := 107091406705390) (lr_hi := 107091423519857)
    (l2L_hi := 100309779800134) (P_lo := 8099572807271912) (P_hi := 8099574078901871)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    w_ge_257 w_le_257 w_ge_255 w_le_255 w_ge_254 w_ge_1107001 w_le_1107001 w_le_1014
    w_ge_3 w_ge_1000 w_le_1000 w_le_1001 w_le_391256 w_le_6642003
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem witness_post_2251 :
    ValidPostBini 2251 1000 2546 149000000 196570000 54300808 ∧
    10 ^ 2169413092970112501391 ≤ (v_k_pass 2546 149000000 196570000) ^ 54300808 ∧ (v_k_pass 2546 149000000 196570000) ^ 54300808 ≤ 10 ^ 2169414003418894233191 :=
  pass_post_witness_of_log2 (Q := Q_SCALE) (p := 2251) (q := 1000) (c := 2546) (d := 149000000) (k := 196570000) (h := 54300808)
    (lw_lo := 14482262684444278862) (lw_hi := 14482262684748472096) (lr_lo := 1449828898085629) (lr_hi := 1449829506472096)
    (l2L_hi := 1434969604053477) (P_lo := 2169413092970112501391) (P_hi := 2169414003418894233191)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    w_ge_2548 w_le_2548 w_ge_2546 w_le_2546 w_ge_2545 w_ge_149000001 w_le_149000001 w_le_10180
    w_ge_3 w_ge_1000 w_le_1000 w_le_1001 w_le_54300809 w_le_894000003
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)


/-! ### Central binomial identities and single-shot untwisted `Str_3^{⊗N}` witnesses -/

/-- Exact binomial step identity: `C(n, k) * (n - k) = C(n, k + 1) * (k + 1)`. -/
theorem natChoose_step : ∀ n k, natChoose n k * (n - k) = natChoose n (k + 1) * (k + 1)
  | 0, k => by simp [natChoose]
  | n + 1, 0 => by
    simp only [natChoose, Nat.one_mul]
    have h1 : ∀ m, natChoose m 1 = m := by
      intro m; induction m with
      | zero => rfl
      | succ r ihr => simp [natChoose, ihr]; omega
    rw [h1 n]; omega
  | n + 1, k + 1 => by
    have ih1 := natChoose_step n k
    have ih2 := natChoose_step n (k + 1)
    by_cases hkn : k + 1 ≤ n
    · simp only [natChoose]
      have hs1 : n + 1 - (k + 1) = n - k := by omega
      have hs2 : n - k = (n - (k + 1)) + 1 := by omega
      rw [hs1, Nat.add_mul, ih1, Nat.add_mul]
      have hmid : natChoose n (k + 1) * (n - k)
          = natChoose n (k + 1) * (n - (k + 1)) + natChoose n (k + 1) := by
        rw [hs2, Nat.mul_add, Nat.mul_one]
      rw [hmid, ih2]
      grind
    · have hgt : n < k + 1 := by omega
      have hgt2 : n < k + 2 := by omega
      have hs : n + 1 - (k + 1) = 0 := by omega
      rw [hs, Nat.mul_zero]
      simp only [natChoose, natChoose_eq_zero_of_lt n (k + 1) hgt, natChoose_eq_zero_of_lt n (k + 2) hgt2,
                 Nat.add_zero, Nat.zero_mul]

/-- Exact central binomial step: `C(2m + 2, m + 1) * (m + 1) = (4m + 2) * C(2m, m)`. -/
theorem natChoose_central_step (m : Nat) :
    natChoose (2 * (m + 1)) (m + 1) * (m + 1) = (4 * m + 2) * natChoose (2 * m) m := by
  have hsym : natChoose (2 * m + 1) m = natChoose (2 * m + 1) (m + 1) := by
    have h := natChoose_step (2 * m + 1) m
    have hs : 2 * m + 1 - m = m + 1 := by omega
    rw [hs] at h
    exact Nat.eq_of_mul_eq_mul_right (by omega) h
  have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
  rw [h1, natChoose, hsym]
  have h2 : natChoose (2 * m + 1) (m + 1) * (m + 1) = (2 * m + 1) * natChoose (2 * m) m := by
    rw [natChoose, Nat.add_mul]
    have hs := natChoose_step (2 * m) m
    have hsub : 2 * m - m = m := by omega
    rw [hsub] at hs
    rw [← hs]
    grind
  grind

def centralBinom : Nat → Nat
  | 0 => 1
  | m + 1 => (4 * m + 2) * centralBinom m / (m + 1)

theorem natChoose_eq_centralBinom : ∀ m, natChoose (2 * m) m = centralBinom m
  | 0 => rfl
  | m + 1 => by
    unfold centralBinom
    rw [← natChoose_eq_centralBinom m, ← natChoose_central_step m, Nat.mul_div_cancel _ (by omega)]

theorem natChoose_16_8 : natChoose 16 8 = 12870 := by
  have h := natChoose_eq_centralBinom 8
  change natChoose 16 8 = centralBinom 8 at h
  rw [h]; decide

theorem natChoose_22_11 : natChoose 22 11 = 705432 := by
  have h := natChoose_eq_centralBinom 11
  change natChoose 22 11 = centralBinom 11 at h
  rw [h]; decide

theorem natChoose_le_central (m : Nat) : ∀ k, natChoose (2 * m) k ≤ natChoose (2 * m) m := by
  have hinc : ∀ k, k < m → natChoose (2 * m) k ≤ natChoose (2 * m) (k + 1) := by
    intro k hk
    have h := natChoose_step (2 * m) k
    have hge : natChoose (2 * m) k * (k + 1) ≤ natChoose (2 * m) k * (2 * m - k) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [h] at hge
    exact Nat.le_of_mul_le_mul_right hge (by omega)
  have hdec : ∀ k, m ≤ k → natChoose (2 * m) (k + 1) ≤ natChoose (2 * m) k := by
    intro k hk
    have h := natChoose_step (2 * m) k
    have hle : natChoose (2 * m) k * (2 * m - k) ≤ natChoose (2 * m) k * (k + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [h] at hle
    exact Nat.le_of_mul_le_mul_right hle (by omega)
  have hleft : ∀ d k, k + d = m → natChoose (2 * m) k ≤ natChoose (2 * m) m := by
    intro d; induction d with
    | zero =>
      intro k hk
      have heq : k = m := by omega
      rw [heq]; exact Nat.le_refl _
    | succ r ihr =>
      intro k hk
      exact Nat.le_trans (hinc k (by omega)) (ihr (k + 1) (by omega))
  have hright : ∀ d, natChoose (2 * m) (m + d) ≤ natChoose (2 * m) m := by
    intro d; induction d with
    | zero => exact Nat.le_refl _
    | succ r ihr => exact Nat.le_trans (hdec (m + r) (by omega)) ihr
  intro k
  by_cases hkm : k ≤ m
  · exact hleft (m - k) k (by omega)
  · have : k = m + (k - m) := by omega
    rw [this]; exact hright (k - m)

/-- Exact two-sided central binomial sandwich:
    `2^(2*m) ≤ (2*m + 1) * C(2*m, m)` and `C(2*m, m) ≤ 2^(2*m)`. -/
theorem natChoose_central_bounds (m : Nat) :
    2 ^ (2 * m) ≤ (2 * m + 1) * natChoose (2 * m) m ∧ natChoose (2 * m) m ≤ 2 ^ (2 * m) := by
  have hsum : natSum (2 * m + 1) (fun k => natChoose (2 * m) k) = 2 ^ (2 * m) := by
    have h := sum_choose_pow 1 (2 * m)
    have h1 : (1 : Nat) + 1 = 2 := rfl
    rw [h1] at h
    rw [← h]
    apply natSum_congr
    intro k _
    simp [Nat.one_pow, Nat.mul_one]
  have hle_sum : ∀ n (f : Nat → Nat) (M : Nat), (∀ i < n, f i ≤ M) → natSum n f ≤ n * M := by
    intro n f M hM
    induction n with
    | zero => simp [natSum]
    | succ r ihr =>
      simp only [natSum]
      have h1 := ihr (fun i hi => hM i (by omega))
      have h2 := hM r (by omega)
      rw [Nat.add_mul, Nat.one_mul]
      omega
  have hge_term : ∀ n (f : Nat → Nat) (j : Nat), j < n → f j ≤ natSum n f := by
    intro n f j hj
    induction n with
    | zero => omega
    | succ r ihr =>
      simp only [natSum]
      by_cases hjr : j = r
      · rw [hjr]; exact Nat.le_add_left _ _
      · exact Nat.le_trans (ihr (by omega)) (Nat.le_add_right _ _)
  rw [← hsum]
  exact ⟨hle_sum (2 * m + 1) _ _ (fun k _ => natChoose_le_central m k),
         hge_term (2 * m + 1) _ m (by omega)⟩

/-! ### Exact `Str_3^{⊗N}` single-shot untwisted parameters (Section 4.3, Table 3) -/

def M_str3 (N : Nat) : Nat := natChoose N (N / 2)
def v_str3 (N : Nat) : Nat := 3 ^ N * M_str3 N
def P_str3 (N s : Nat) : Nat := (M_str3 N) ^ (3 * s)
def r_str3 (N : Nat) : Nat := (2 * M_str3 N - 1) ^ 3 * 4 ^ (3 * N)
def E_str3 (N : Nat) : Nat := 3 * (N + 1) * M_str3 N
def R_ex_str3 (N s : Nat) : Nat := (s * E_str3 N + 1) * (r_str3 N) ^ s
def V_single_str3 (N s t : Nat) : Nat := (v_str3 N) ^ (s * t)
def R_single_str3 (N s t : Nat) : Nat := schonhageRank (P_str3 N s) (R_ex_str3 N s) t

theorem M_str3_pos_even (m : Nat) : 1 ≤ M_str3 (2 * m) := by
  unfold M_str3
  have hd : 2 * m / 2 = m := by omega
  rw [hd]
  have hb := (natChoose_central_bounds m).1
  have hpos : 1 ≤ 2 ^ (2 * m) := Nat.two_pow_pos _
  by_cases hz : natChoose (2 * m) m = 0
  · rw [hz, Nat.mul_zero] at hb; omega
  · omega

theorem P_str3_le_R_ex_even (m s : Nat) (_hs : 1 ≤ s) :
    P_str3 (2 * m) s ≤ R_ex_str3 (2 * m) s := by
  unfold P_str3 R_ex_str3 r_str3
  have hM := M_str3_pos_even m
  have h1 : M_str3 (2 * m) ≤ 2 * M_str3 (2 * m) - 1 := by omega
  have h2 : (M_str3 (2 * m)) ^ 3 ≤ (2 * M_str3 (2 * m) - 1) ^ 3 * 4 ^ (3 * (2 * m)) := by
    have h4 : 1 ≤ 4 ^ (3 * (2 * m)) := pow_pos_of_pos (by decide) _
    have hm := Nat.mul_le_mul (Nat.pow_le_pow_left h1 3) h4
    simpa [Nat.mul_one] using hm
  have h3 := Nat.pow_le_pow_left h2 s
  rw [← Nat.pow_mul] at h3
  have hE : 1 ≤ s * E_str3 (2 * m) + 1 := by omega
  have hm := Nat.mul_le_mul hE h3
  simpa [Nat.one_mul] using hm

/-- Generic symbolic-`Q` direct-sum `Str_3` witness verifier given exact `M = M_str3 N`. -/
theorem str3_direct_sum_exact_of_log2
    {Q p q N s M l3_lo l3_hi lM_lo lM_hi lE_hi l2M_hi P_lo P_hi V_lo V_hi : Nat}
    (hQ : 0 < Q) (hM_eq : M_str3 N = M)
    (hl3_lo : Log2Ge 3 l3_lo Q) (hl3_hi : Log2Le 3 l3_hi Q)
    (hlM_lo : Log2Ge M lM_lo Q) (hlM_hi : Log2Le M lM_hi Q)
    (hlE_hi : Log2Le (s * (3 * (N + 1) * M) + 1) lE_hi Q)
    (hl2M_hi : Log2Le (2 * M - 1) l2M_hi Q)
    (hP_lo : P_lo * Q * 14267572528 ≤ (3 * s * lM_lo) * Q_SCALE)
    (hP_hi : (3 * s * lM_hi) * Q_SCALE ≤ P_hi * Q * 14267572527)
    (hV_lo : V_lo * Q * 14267572528 ≤ (s * (N * l3_lo + lM_lo)) * Q_SCALE)
    (hV_hi : (s * (N * l3_hi + lM_hi)) * Q_SCALE ≤ V_hi * Q * 14267572527)
    (hvalid : q * (lE_hi + s * (3 * l2M_hi + 6 * N * Q))
              < q * (3 * s * lM_lo) + p * (s * (N * l3_lo + lM_lo))) :
    10 ^ P_lo ≤ P_str3 N s ∧ P_str3 N s ≤ 10 ^ P_hi ∧
    10 ^ V_lo ≤ (v_str3 N) ^ s ∧ (v_str3 N) ^ s ≤ 10 ^ V_hi ∧
    (R_ex_str3 N s) ^ q < (P_str3 N s) ^ q * ((v_str3 N) ^ s) ^ p := by
  have hP_ge : Log2Ge (P_str3 N s) (3 * s * lM_lo) Q := by
    unfold P_str3; rw [hM_eq]; exact hlM_lo.pow (3 * s)
  have hP_le : Log2Le (P_str3 N s) (3 * s * lM_hi) Q := by
    unfold P_str3; rw [hM_eq]; exact hlM_hi.pow (3 * s)
  have hv_ge : Log2Ge ((v_str3 N) ^ s) (s * (N * l3_lo + lM_lo)) Q := by
    unfold v_str3; rw [hM_eq]; exact ((hl3_lo.pow N).mul hlM_lo).pow s
  have hv_le : Log2Le ((v_str3 N) ^ s) (s * (N * l3_hi + lM_hi)) Q := by
    unfold v_str3; rw [hM_eq]; exact ((hl3_hi.pow N).mul hlM_hi).pow s
  have hr_le : Log2Le (r_str3 N) (3 * l2M_hi + 6 * N * Q) Q := by
    unfold r_str3; rw [hM_eq]
    have h4 : 4 ^ (3 * N) = 2 ^ (6 * N) := by
      have : (4 : Nat) = 2 ^ 2 := by decide
      rw [this, ← Nat.pow_mul]
      have h6 : 2 * (3 * N) = 6 * N := by omega
      rw [h6]
    rw [h4]
    exact (hl2M_hi.pow 3).mul (Log2Le.two_pow (6 * N) Q)
  have hRex_le : Log2Le (R_ex_str3 N s) (lE_hi + s * (3 * l2M_hi + 6 * N * Q)) Q := by
    unfold R_ex_str3 E_str3; rw [hM_eq]
    exact hlE_hi.mul (hr_le.pow s)
  have hLHS : Log2Le ((R_ex_str3 N s) ^ q) (q * (lE_hi + s * (3 * l2M_hi + 6 * N * Q))) Q :=
    hRex_le.pow q
  have hRHS : Log2Ge ((P_str3 N s) ^ q * ((v_str3 N) ^ s) ^ p)
      (q * (3 * s * lM_lo) + p * (s * (N * l3_lo + lM_lo))) Q :=
    (hP_ge.pow q).mul (hv_ge.pow p)
  have hlt := lt_pow_of_log2 (a := 1) (b := 1) hLHS hRHS (by simpa [Nat.mul_one] using hvalid)
  exact ⟨pow10_le_of_log2 hP_ge hQ hP_lo, le_pow10_of_log2 hP_le hQ hP_hi,
         pow10_le_of_log2 hv_ge hQ hV_lo, le_pow10_of_log2 hv_le hQ hV_hi, by simpa using hlt⟩

/-- Generic symbolic-`Q` single-matrix `Str_3` witness verifier given exact `M = M_str3 (2*m)`
    using `1000 * P ≤ R_ex` (tight `1001/1000` Schönhage conversion). -/
theorem str3_single_exact_of_log2
    {Q p q N m s t M l3_lo l3_hi lM_lo lM_hi lE_hi l2M_hi l1000_lo l1001_hi V_lo V_hi : Nat}
    (hQ : 0 < Q) (hN : N = 2 * m) (hm : 2 ≤ m) (hs : 1 ≤ s) (ht : 1 ≤ t) (hM_eq : M_str3 N = M)
    (hl3_lo : Log2Ge 3 l3_lo Q) (hl3_hi : Log2Le 3 l3_hi Q)
    (hlM_lo : Log2Ge M lM_lo Q) (hlM_hi : Log2Le M lM_hi Q)
    (hlE_hi : Log2Le (s * (3 * (N + 1) * M) + 1) lE_hi Q)
    (hl2M_hi : Log2Le (2 * M - 1) l2M_hi Q)
    (hl1000_lo : Log2Ge 1000 l1000_lo Q) (hl1001_hi : Log2Le 1001 l1001_hi Q)
    (hV_lo : V_lo * Q * 14267572528 ≤ (s * t * (N * l3_lo + lM_lo)) * Q_SCALE)
    (hV_hi : (s * t * (N * l3_hi + lM_hi)) * Q_SCALE ≤ V_hi * Q * 14267572527)
    (hvalid : q * t * (l1001_hi + lE_hi + s * (3 * l2M_hi + 6 * N * Q))
              < q * (t * l1000_lo + (t - 1) * (3 * s * lM_lo))
                + p * (s * t * (N * l3_lo + lM_lo))) :
    10 ^ V_lo ≤ V_single_str3 N s t ∧
    V_single_str3 N s t ≤ 10 ^ V_hi ∧
    (R_single_str3 N s t) ^ q < (V_single_str3 N s t) ^ p := by
  subst hN
  have hP_pos : 1 ≤ P_str3 (2 * m) s := pow_pos_of_pos (M_str3_pos_even m) _
  have hPR : P_str3 (2 * m) s ≤ R_ex_str3 (2 * m) s := P_str3_le_R_ex_even m s hs
  have h1000P : 1000 * P_str3 (2 * m) s ≤ R_ex_str3 (2 * m) s := by
    unfold P_str3 R_ex_str3 r_str3
    have h4_1000 : 1000 ≤ 4 ^ (3 * (2 * m)) := by
      have h5 : 1000 ≤ 4 ^ 5 := by decide
      exact Nat.le_trans h5 (Nat.pow_le_pow_right (by decide) (by omega))
    have h1 : M_str3 (2 * m) ≤ 2 * M_str3 (2 * m) - 1 := by have := M_str3_pos_even m; omega
    have h2 : 1000 * (M_str3 (2 * m)) ^ 3 ≤ (2 * M_str3 (2 * m) - 1) ^ 3 * 4 ^ (3 * (2 * m)) := by
      rw [Nat.mul_comm 1000]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left h1 3) h4_1000
    have h3 : 1000 ^ s * (M_str3 (2 * m)) ^ (3 * s) ≤ ((2 * M_str3 (2 * m) - 1) ^ 3 * 4 ^ (3 * (2 * m))) ^ s := by
      have hp := Nat.pow_le_pow_left h2 s
      rw [Nat.mul_pow, ← Nat.pow_mul] at hp
      exact hp
    have h1000_le : 1000 ≤ 1000 ^ s := by
      calc 1000 = 1000 ^ 1 := (Nat.pow_one 1000).symm
        _ ≤ 1000 ^ s := Nat.pow_le_pow_right (by decide) hs
    have hE1 : 1 ≤ s * E_str3 (2 * m) + 1 := by omega
    calc 1000 * (M_str3 (2 * m)) ^ (3 * s)
        ≤ 1000 ^ s * (M_str3 (2 * m)) ^ (3 * s) := Nat.mul_le_mul_right _ h1000_le
      _ ≤ ((2 * M_str3 (2 * m) - 1) ^ 3 * 4 ^ (3 * (2 * m))) ^ s := h3
      _ ≤ (s * E_str3 (2 * m) + 1) * ((2 * M_str3 (2 * m) - 1) ^ 3 * 4 ^ (3 * (2 * m))) ^ s := by
          have := Nat.mul_le_mul_right (((2 * M_str3 (2 * m) - 1) ^ 3 * 4 ^ (3 * (2 * m))) ^ s) hE1
          simpa [Nat.one_mul] using this
  have hP_ge : Log2Ge (P_str3 (2 * m) s) (3 * s * lM_lo) Q := by
    unfold P_str3; rw [hM_eq]; exact hlM_lo.pow (3 * s)
  have hV_ge : Log2Ge (V_single_str3 (2 * m) s t) (s * t * (2 * m * l3_lo + lM_lo)) Q := by
    unfold V_single_str3 v_str3; rw [hM_eq]; exact ((hl3_lo.pow (2 * m)).mul hlM_lo).pow (s * t)
  have hV_le : Log2Le (V_single_str3 (2 * m) s t) (s * t * (2 * m * l3_hi + lM_hi)) Q := by
    unfold V_single_str3 v_str3; rw [hM_eq]; exact ((hl3_hi.pow (2 * m)).mul hlM_hi).pow (s * t)
  have hr_le : Log2Le (r_str3 (2 * m)) (3 * l2M_hi + 6 * (2 * m) * Q) Q := by
    unfold r_str3; rw [hM_eq]
    have h4 : 4 ^ (3 * (2 * m)) = 2 ^ (6 * (2 * m)) := by
      have : (4 : Nat) = 2 ^ 2 := by decide
      rw [this, ← Nat.pow_mul]
      have h6 : 2 * (3 * (2 * m)) = 6 * (2 * m) := by omega
      rw [h6]
    rw [h4]
    exact (hl2M_hi.pow 3).mul (Log2Le.two_pow (6 * (2 * m)) Q)
  have hRex_le : Log2Le (R_ex_str3 (2 * m) s) (lE_hi + s * (3 * l2M_hi + 6 * (2 * m) * Q)) Q := by
    unfold R_ex_str3 E_str3; rw [hM_eq]
    exact hlE_hi.mul (hr_le.pow s)
  have hsch := finite_schonhage (P_str3 (2 * m) s) (R_ex_str3 (2 * m) s) hP_pos hPR t ht
  have h1001 : 1000 * (R_ex_str3 (2 * m) s + P_str3 (2 * m) s) ≤ 1001 * R_ex_str3 (2 * m) s := by
    rw [Nat.mul_add]; omega
  have hLHS_le : (1000 ^ t * P_str3 (2 * m) s ^ (t - 1) * R_single_str3 (2 * m) s t) ^ q
      ≤ (1001 * R_ex_str3 (2 * m) s) ^ (q * t) := by
    have h1 : 1000 ^ t * (P_str3 (2 * m) s ^ (t - 1) * R_single_str3 (2 * m) s t)
        ≤ (1001 * R_ex_str3 (2 * m) s) ^ t := by
      have hm := Nat.mul_le_mul_left (1000 ^ t) hsch
      rw [← Nat.mul_pow] at hm
      exact Nat.le_trans hm (Nat.pow_le_pow_left h1001 t)
    have hq := Nat.pow_le_pow_left h1 q
    rw [← Nat.pow_mul, Nat.mul_comm t q, ← Nat.mul_assoc] at hq
    exact hq
  have hL_log : Log2Le ((1001 * R_ex_str3 (2 * m) s) ^ (q * t))
      (q * t * (l1001_hi + lE_hi + s * (3 * l2M_hi + 6 * (2 * m) * Q))) Q := by
    have h := (hl1001_hi.mul hRex_le).pow (q * t)
    have e : q * t * (l1001_hi + (lE_hi + s * (3 * l2M_hi + 6 * (2 * m) * Q)))
        = q * t * (l1001_hi + lE_hi + s * (3 * l2M_hi + 6 * (2 * m) * Q)) := by ac_rfl
    rwa [e] at h
  have hR_log : Log2Ge ((1000 ^ t * P_str3 (2 * m) s ^ (t - 1)) ^ q * (V_single_str3 (2 * m) s t) ^ p)
      (q * (t * l1000_lo + (t - 1) * (3 * s * lM_lo)) + p * (s * t * (2 * m * l3_lo + lM_lo))) Q :=
    (((hl1000_lo.pow t).mul (hP_ge.pow (t - 1))).pow q).mul (hV_ge.pow p)
  have hlt := lt_pow_of_log2 (a := 1) (b := 1) hL_log hR_log (by simpa [Nat.mul_one] using hvalid)
  simp only [Nat.pow_one] at hlt
  have hcomb := Nat.lt_of_le_of_lt hLHS_le hlt
  rw [Nat.mul_pow (1000 ^ t * P_str3 (2 * m) s ^ (t - 1))] at hcomb
  exact ⟨pow10_le_of_log2 hV_ge hQ hV_lo, le_pow10_of_log2 hV_le hQ hV_hi,
         Nat.lt_of_mul_lt_mul_left hcomb⟩

/-- Generic symbolic-`Q` single-matrix `Str_3^{⊗N}` (`N = 2*m`) verifier using `natChoose_central_bounds` + `finite_schonhage`. -/
theorem str3_single_symbolic_of_log2
    {Q p q N m s t l3_lo l3_hi ln1_hi lcf_hi M_lo M_hi : Nat}
    (hQ : 0 < Q) (hN : N = 2 * m) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hMexp : 3 * s * q + t * q ≤ s * t * p)
    (hl3_lo : Log2Ge 3 l3_lo Q) (hl3_hi : Log2Le 3 l3_hi Q)
    (hln1_hi : Log2Le (N + 1) ln1_hi Q)
    (hlcf_hi : Log2Le (2 * (3 * s * (N + 1) + 1)) lcf_hi Q)
    (hvalid : t * q * (lcf_hi + (6 * N + 3) * s * Q)
              + (s * t * p - 3 * s * q - t * q) * ln1_hi
              < N * s * t * p * l3_lo + N * (s * t * p - 3 * s * q - t * q) * Q)
    (hM_lo : M_lo * Q * 14267572528 + s * t * ln1_hi * Q_SCALE
             ≤ s * t * (N * l3_lo + N * Q) * Q_SCALE)
    (hM_hi : s * t * (N * l3_hi + N * Q) * Q_SCALE ≤ M_hi * Q * 14267572527) :
    10 ^ M_lo ≤ V_single_str3 N s t ∧
    V_single_str3 N s t ≤ 10 ^ M_hi ∧
    (R_single_str3 N s t) ^ q < (V_single_str3 N s t) ^ p := by
  subst hN
  let M := M_str3 (2 * m)
  have hM_eq : M = natChoose (2 * m) m := by
    dsimp only [M, M_str3]
    have hdiv : 2 * m / 2 = m := by omega
    rw [hdiv]
  have hcb := natChoose_central_bounds m
  rw [← hM_eq] at hcb
  have hM_pos : 1 ≤ M := M_str3_pos_even m
  have hP_pos : 1 ≤ P_str3 (2 * m) s := pow_pos_of_pos hM_pos _
  have hPR : P_str3 (2 * m) s ≤ R_ex_str3 (2 * m) s := P_str3_le_R_ex_even m s hs
  have hv_ge : Log2Ge (v_str3 (2 * m)) (2 * m * l3_lo + 2 * m * Q - ln1_hi) Q := by
    unfold v_str3
    have hmul : 3 ^ (2 * m) * 2 ^ (2 * m) ≤ (2 * m + 1) * (3 ^ (2 * m) * M) := by
      have hm := Nat.mul_le_mul_left (3 ^ (2 * m)) hcb.1
      have eR : 3 ^ (2 * m) * ((2 * m + 1) * M) = (2 * m + 1) * (3 ^ (2 * m) * M) := by ac_rfl
      rwa [eR] at hm
    have hA : Log2Ge (3 ^ (2 * m) * 2 ^ (2 * m)) (2 * m * l3_lo + 2 * m * Q) Q :=
      (hl3_lo.pow (2 * m)).mul (Log2Ge.two_pow (2 * m) Q)
    have hle_exp : ln1_hi ≤ 2 * m * l3_lo + 2 * m * Q := by
      have h1 : s * t * ln1_hi * Q_SCALE ≤ s * t * (2 * m * l3_lo + 2 * m * Q) * Q_SCALE :=
        Nat.le_trans (Nat.le_add_left _ _) hM_lo
      have hpos : 0 < s * t * Q_SCALE := Nat.mul_pos (Nat.mul_pos hs ht) (by decide)
      have eL : s * t * ln1_hi * Q_SCALE = ln1_hi * (s * t * Q_SCALE) := by ac_rfl
      have eR : s * t * (2 * m * l3_lo + 2 * m * Q) * Q_SCALE = (2 * m * l3_lo + 2 * m * Q) * (s * t * Q_SCALE) := by ac_rfl
      exact Nat.le_of_mul_le_mul_right (eL ▸ (eR ▸ h1)) hpos
    exact Log2Ge.of_mul_ge hmul hA hln1_hi hle_exp
  have hv_le : Log2Le (v_str3 (2 * m)) (2 * m * l3_hi + 2 * m * Q) Q := by
    unfold v_str3
    have hmul : 3 ^ (2 * m) * M ≤ 3 ^ (2 * m) * 2 ^ (2 * m) := Nat.mul_le_mul_left _ hcb.2
    exact ((hl3_hi.pow (2 * m)).mul (Log2Le.two_pow (2 * m) Q)).mono_left hmul
  have hV_lo : 10 ^ M_lo ≤ V_single_str3 (2 * m) s t := by
    apply pow10_le_of_log2 (hv_ge.pow (s * t)) hQ
    have hsub : s * t * (2 * m * l3_lo + 2 * m * Q - ln1_hi)
        = s * t * (2 * m * l3_lo + 2 * m * Q) - s * t * ln1_hi := Nat.mul_sub _ _ _
    rw [hsub, Nat.sub_mul]
    exact Nat.le_sub_of_add_le hM_lo
  have hV_hi : V_single_str3 (2 * m) s t ≤ 10 ^ M_hi :=
    le_pow10_of_log2 (hv_le.pow (s * t)) hQ hM_hi
  have hsch := finite_schonhage (P_str3 (2 * m) s) (R_ex_str3 (2 * m) s) hP_pos hPR t ht
  have h2R : R_ex_str3 (2 * m) s + P_str3 (2 * m) s ≤ 2 * R_ex_str3 (2 * m) s := by omega
  let C_fac := 2 * (3 * s * (2 * m + 1) + 1) * 2 ^ ((6 * (2 * m) + 3) * s)
  have hR_ub : 2 * R_ex_str3 (2 * m) s ≤ C_fac * M ^ (3 * s + 1) := by
    unfold R_ex_str3 E_str3 r_str3
    have hE1 : s * (3 * (2 * m + 1) * M) + 1 ≤ (3 * s * (2 * m + 1) + 1) * M := by
      rw [Nat.add_mul, Nat.one_mul]
      have : s * (3 * (2 * m + 1) * M) = 3 * s * (2 * m + 1) * M := by ac_rfl
      omega
    have hr1 : (2 * M - 1) ^ 3 * 4 ^ (3 * (2 * m)) ≤ 2 ^ (6 * (2 * m) + 3) * M ^ 3 := by
      have h2m : (2 * M - 1) ^ 3 ≤ (2 * M) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      rw [Nat.mul_pow] at h2m
      have h42 : 4 ^ (3 * (2 * m)) = 2 ^ (6 * (2 * m)) := by
        have : (4 : Nat) = 2 ^ 2 := by decide
        rw [this, ← Nat.pow_mul]
        have : 2 * (3 * (2 * m)) = 6 * (2 * m) := by omega
        rw [this]
      rw [h42]
      have hm := Nat.mul_le_mul_right (2 ^ (6 * (2 * m))) h2m
      have eR : 2 ^ 3 * M ^ 3 * 2 ^ (6 * (2 * m)) = 2 ^ (6 * (2 * m) + 3) * M ^ 3 := by
        rw [Nat.pow_add]; ac_rfl
      rwa [eR] at hm
    have hrs := Nat.pow_le_pow_left hr1 s
    rw [Nat.mul_pow (2 ^ (6 * (2 * m) + 3)), ← Nat.pow_mul 2, ← Nat.pow_mul M] at hrs
    have hm := Nat.mul_le_mul_left 2 (Nat.mul_le_mul hE1 hrs)
    have eR : 2 * ((3 * s * (2 * m + 1) + 1) * M * (2 ^ ((6 * (2 * m) + 3) * s) * M ^ (3 * s)))
        = C_fac * M ^ (3 * s + 1) := by
      dsimp only [C_fac]; rw [Nat.pow_succ M (3 * s)]; ac_rfl
    rwa [eR] at hm
  let E_M := s * t * p - 3 * s * q - t * q
  have hC_lt : C_fac ^ (t * q) * (2 * m + 1) ^ E_M < 3 ^ ((2 * m) * s * t * p) * 2 ^ ((2 * m) * E_M) := by
    have hL : Log2Le (C_fac ^ (t * q) * (2 * m + 1) ^ E_M)
        (t * q * (lcf_hi + (6 * (2 * m) + 3) * s * Q) + E_M * ln1_hi) Q :=
      ((hlcf_hi.mul (Log2Le.two_pow ((6 * (2 * m) + 3) * s) Q)).pow (t * q)).mul (hln1_hi.pow E_M)
    have hR : Log2Ge (3 ^ ((2 * m) * s * t * p) * 2 ^ ((2 * m) * E_M))
        ((2 * m) * s * t * p * l3_lo + (2 * m) * E_M * Q) Q :=
      (hl3_lo.pow ((2 * m) * s * t * p)).mul (Log2Ge.two_pow ((2 * m) * E_M) Q)
    have hlt := lt_pow_of_log2 (a := 1) (b := 1) hL hR (by simpa [Nat.mul_one] using hvalid)
    simpa using hlt
  have hC_M : C_fac ^ (t * q) < 3 ^ ((2 * m) * s * t * p) * M ^ E_M := by
    have hcbE := Nat.pow_le_pow_left hcb.1 E_M
    rw [← Nat.pow_mul, Nat.mul_pow] at hcbE
    have hstep := Nat.lt_of_lt_of_le hC_lt (Nat.mul_le_mul_left (3 ^ ((2 * m) * s * t * p)) hcbE)
    have eR : 3 ^ ((2 * m) * s * t * p) * ((2 * m + 1) ^ E_M * M ^ E_M)
        = (3 ^ ((2 * m) * s * t * p) * M ^ E_M) * (2 * m + 1) ^ E_M := by ac_rfl
    rw [eR] at hstep
    exact Nat.lt_of_mul_lt_mul_right hstep
  have hLHS_bd : P_str3 (2 * m) s ^ ((t - 1) * q) * (R_single_str3 (2 * m) s t) ^ q
      ≤ C_fac ^ (t * q) * M ^ ((3 * s + 1) * (t * q)) := by
    have h1 := Nat.le_trans hsch (Nat.pow_le_pow_left (Nat.le_trans h2R hR_ub) t)
    have h2 := Nat.pow_le_pow_left h1 q
    rw [Nat.mul_pow (P_str3 (2 * m) s ^ (t - 1)), ← Nat.pow_mul (P_str3 (2 * m) s),
        Nat.mul_pow C_fac, ← Nat.pow_mul M, Nat.mul_pow (C_fac ^ t), ← Nat.pow_mul C_fac,
        ← Nat.pow_mul M] at h2
    have e1 : (3 * s + 1) * t * q = (3 * s + 1) * (t * q) := by ac_rfl
    rwa [e1] at h2
  have hM_eq_exp : (3 * s + 1) * (t * q) + E_M = 3 * s * ((t - 1) * q) + s * t * p := by
    dsimp only [E_M]
    have hsub : 3 * s * ((t - 1) * q) + 3 * s * q = 3 * s * (t * q) := by
      have : (t - 1) * q + q = t * q := by
        calc (t - 1) * q + q = (t - 1) * q + 1 * q := by rw [Nat.one_mul]
          _ = ((t - 1) + 1) * q := (Nat.add_mul _ _ _).symm
          _ = t * q := by rw [Nat.sub_add_cancel ht]
      rw [← Nat.mul_add, this]
    have h3 : (3 * s + 1) * (t * q) = 3 * s * (t * q) + t * q := by rw [Nat.add_mul, Nat.one_mul]
    omega
  have hRHS_lt : C_fac ^ (t * q) * M ^ ((3 * s + 1) * (t * q))
      < P_str3 (2 * m) s ^ ((t - 1) * q) * (V_single_str3 (2 * m) s t) ^ p := by
    have hm := Nat.mul_lt_mul_of_pos_right hC_M (pow_pos_of_pos hM_pos ((3 * s + 1) * (t * q)))
    have eR : 3 ^ ((2 * m) * s * t * p) * M ^ E_M * M ^ ((3 * s + 1) * (t * q))
        = P_str3 (2 * m) s ^ ((t - 1) * q) * (V_single_str3 (2 * m) s t) ^ p := by
      unfold P_str3 V_single_str3 v_str3
      rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
      rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm E_M, hM_eq_exp, Nat.pow_add]
      have a1 : (2 * m) * s * t * p = 2 * m * (s * t) * p := by ac_rfl
      rw [a1]; ac_rfl
    rwa [eR] at hm
  exact ⟨hV_lo, hV_hi, Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt hLHS_bd hRHS_lt)⟩

/-! ### Verified `Str_3^{⊗N}` constructive witnesses (Direct Sum & Single Matrix) -/

/-- Direct-sum `Str_3^{⊗16}` (`s = 2`) sub-Strassen witness:
    `P = 12870^6 ∈ [10^24, 10^25]` disjoint copies of side `v^2 ∈ [10^23, 10^24]`,
    amortized rank `R_ex / P < (v^2)^{2.807}`. -/
theorem witness_str3_direct_sum_2807 :
    10 ^ 24 ≤ P_str3 16 2 ∧ P_str3 16 2 ≤ 10 ^ 25 ∧
    10 ^ 23 ≤ (v_str3 16) ^ 2 ∧ (v_str3 16) ^ 2 ≤ 10 ^ 24 ∧
    (R_ex_str3 16 2) ^ 1000 < (P_str3 16 2) ^ 1000 * ((v_str3 16) ^ 2) ^ 2807 :=
  str3_direct_sum_exact_of_log2 (Q := Q_SCALE) (p := 2807) (q := 1000) (N := 16) (s := 2) (M := 12870)
    (P_lo := 24) (P_hi := 25) (V_lo := 23) (V_hi := 24)
    (by decide) (by unfold M_str3; exact natChoose_16_8)
    w_ge_3 w_le_3 w_ge_12870 w_le_12870 w_le_1312741 w_le_25739
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Single-matrix `Str_3^{⊗22}` (`s = 3, t = 7`) sub-Strassen witness via `finite_schonhage`:
    `V_single ∈ [10^343, 10^344]`, exact single-matrix rank `R_single < V_single^{2.807}`. -/
theorem witness_str3_single_matrix_2807 :
    10 ^ 343 ≤ V_single_str3 22 3 7 ∧ V_single_str3 22 3 7 ≤ 10 ^ 344 ∧
    (R_single_str3 22 3 7) ^ 1000 < (V_single_str3 22 3 7) ^ 2807 :=
  str3_single_exact_of_log2 (Q := Q_SCALE) (p := 2807) (q := 1000) (N := 22) (m := 11) (s := 3) (t := 7) (M := 705432)
    (V_lo := 343) (V_hi := 344)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by unfold M_str3; exact natChoose_22_11)
    w_ge_3 w_le_3 w_ge_705432 w_le_705432 w_le_146024425 w_le_1410863 w_ge_1000 w_le_1001
    (by decide) (by decide) (by decide)

/-- Single-matrix `Str_3^{⊗90}` (`s = 10, t = 28`) sub-2.500 witness via `finite_schonhage`:
    `V_single ∈ [10^19060, 10^19610]`, exact single-matrix rank `R_single < V_single^{5/2}`. -/
theorem witness_str3_single_matrix_2500 :
    10 ^ 19060 ≤ V_single_str3 90 10 28 ∧ V_single_str3 90 10 28 ≤ 10 ^ 19610 ∧
    (R_single_str3 90 10 28) ^ 2 < (V_single_str3 90 10 28) ^ 5 :=
  str3_single_symbolic_of_log2 (Q := Q_SCALE) (p := 5) (q := 2) (N := 90) (m := 45) (s := 10) (t := 28)
    (M_lo := 19060) (M_hi := 19610)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    w_ge_3 w_le_3 w_le_91 w_le_5462
    (by decide) (by decide) (by decide)

/-- Single-matrix `Str_3^{⊗340}` (`s = 34, t = 100`) sub-CW (`τ = 2.371`) witness via `finite_schonhage`:
    `V_single ∈ [10^890931, 10^899543]`, exact single-matrix rank `R_single < V_single^{2.371}`. -/
theorem witness_str3_single_matrix_2371 :
    10 ^ 890931 ≤ V_single_str3 340 34 100 ∧ V_single_str3 340 34 100 ≤ 10 ^ 899543 ∧
    (R_single_str3 340 34 100) ^ 1000 < (V_single_str3 340 34 100) ^ 2371 :=
  str3_single_symbolic_of_log2 (Q := Q_SCALE) (p := 2371) (q := 1000) (N := 340) (m := 170) (s := 34) (t := 100)
    (M_lo := 890931) (M_hi := 899543)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    w_ge_3 w_le_3 w_le_341 w_le_69566
    (by decide) (by decide) (by decide)

end MatMul94

