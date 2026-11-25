/-
  MatMul94/UniversalBounds.lean

  Formal Pass Theorem 4.3 model, universal pure-integer structural theorems,
  exact `c_min` lower bounds, and completely universal pre-Bini (`v_k`) and
  post-Bini (`V = v_k^h`) lower bounds across ALL `(c, d, k) ∈ ℕ³` and
  `(c, d, k, h) ∈ ℕ⁴` for all 8 benchmark exponents
  (`2.800, 2.695, 2.500, 2.371, 2.321, 2.300, 2.260, 2.251`).
-/

import MatMul94.LayerConstraints

namespace MatMul94

/-! ### Exact Pass Theorem 4.3 parameter definitions -/

def w_pass (c d : Nat) : Nat := (c + 2) ^ (2 * d) / (d + 1)
def u_pass (c d : Nat) : Nat := c ^ (2 * d)
def Lambda_pass (c d : Nat) : Nat := (w_pass c d / u_pass c d) ^ 2
def v_k_pass (c d k : Nat) : Nat := (w_pass c d) ^ 2 * (Lambda_pass c d) ^ k
def E_k_pass (c d k : Nat) : Nat := 64 ^ k * (w_pass c d) ^ 9 * (2 * L_pass c k - 1) ^ (6 * d)

def ValidPassTriple (p q c d k : Nat) : Prop :=
  2 ≤ c ∧ 1 ≤ d ∧ 1 ≤ k ∧ 1 ≤ w_pass c d ∧ 1 ≤ Lambda_pass c d ∧
  (E_k_pass c d k) ^ q < (v_k_pass c d k) ^ p

def ValidPostBini (p q c d k h : Nat) : Prop :=
  ValidPassTriple p q c d k ∧ 1 ≤ h ∧
  (h * (3 * (2 * d + 1) * w_pass c d - 2) ^ (2 * k - 1) + 1) ^ q * (E_k_pass c d k) ^ (h * q)
    < (v_k_pass c d k) ^ (h * p)

/-! ### Core universal structural inequalities (ALL `(c, d, k) ∈ ℕ³`, ZERO floats) -/

theorem Lambda_pass_mul_le (c d : Nat) :
    Lambda_pass c d * (d + 1) ^ 2 * c ^ (4 * d) ≤ (c + 2) ^ (4 * d) := by
  unfold Lambda_pass u_pass w_pass
  have h1 : ((c + 2) ^ (2 * d) / (d + 1)) / c ^ (2 * d) * c ^ (2 * d)
      ≤ (c + 2) ^ (2 * d) / (d + 1) := Nat.div_mul_le_self _ _
  have h2 : ((c + 2) ^ (2 * d) / (d + 1)) * (d + 1) ≤ (c + 2) ^ (2 * d) :=
    Nat.div_mul_le_self _ _
  have h3 : (((c + 2) ^ (2 * d) / (d + 1)) / c ^ (2 * d) * c ^ (2 * d)) * (d + 1)
      ≤ (c + 2) ^ (2 * d) := Nat.le_trans (Nat.mul_le_mul_right (d + 1) h1) h2
  have hsq := Nat.pow_le_pow_left h3 2
  rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hsq
  have h4 : 2 * d * 2 = 4 * d := by omega
  rw [h4] at hsq
  have eL : ((c + 2) ^ (2 * d) / (d + 1) / c ^ (2 * d)) ^ 2 * (d + 1) ^ 2 * c ^ (4 * d) =
      ((c + 2) ^ (2 * d) / (d + 1) / c ^ (2 * d)) ^ 2 * c ^ (4 * d) * (d + 1) ^ 2 := by ac_rfl
  rwa [eL]

/-- Fundamental universal pre-round inequality:
    `64^q * (d + 1)^(2*p) * c^(4*d*p) * (c + 2)^(6*d*q) < (c + 2)^(4*d*p) * (c - 1)^(6*d*q)`. -/
theorem universal_round_necessary {p q c d k : Nat}
    (hV : ValidPassTriple p q c d k) (hτ : 2 * p ≤ 9 * q) :
    64 ^ q * (d + 1) ^ (2 * p) * c ^ (4 * d * p) * (c + 2) ^ (6 * d * q) <
    (c + 2) ^ (4 * d * p) * (c - 1) ^ (6 * d * q) := by
  rcases hV with ⟨hc, hd, hk, hw, _hL, hlt⟩
  unfold E_k_pass v_k_pass at hlt
  rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow] at hlt
  rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hlt
  have hw_le : w_pass c d ^ (2 * p) ≤ w_pass c d ^ (9 * q) := Nat.pow_le_pow_right hw hτ
  have hlt1 : 64 ^ (k * q) * (2 * L_pass c k - 1) ^ (6 * d * q) < Lambda_pass c d ^ (k * p) := by
    have hmul : (64 ^ (k * q) * (2 * L_pass c k - 1) ^ (6 * d * q)) * w_pass c d ^ (2 * p)
        < Lambda_pass c d ^ (k * p) * w_pass c d ^ (2 * p) := by
      have s1 : (64 ^ (k * q) * (2 * L_pass c k - 1) ^ (6 * d * q)) * w_pass c d ^ (2 * p)
          ≤ 64 ^ (k * q) * w_pass c d ^ (9 * q) * (2 * L_pass c k - 1) ^ (6 * d * q) := by
        have hm := Nat.mul_le_mul_left (64 ^ (k * q) * (2 * L_pass c k - 1) ^ (6 * d * q)) hw_le
        have eR : 64 ^ (k * q) * (2 * L_pass c k - 1) ^ (6 * d * q) * w_pass c d ^ (9 * q)
            = 64 ^ (k * q) * w_pass c d ^ (9 * q) * (2 * L_pass c k - 1) ^ (6 * d * q) := by ac_rfl
        rwa [eR] at hm
      have eR2 : w_pass c d ^ (2 * p) * Lambda_pass c d ^ (k * p)
          = Lambda_pass c d ^ (k * p) * w_pass c d ^ (2 * p) := Nat.mul_comm _ _
      exact Nat.lt_of_le_of_lt s1 (eR2 ▸ hlt)
    exact Nat.lt_of_mul_lt_mul_right hmul
  have hLk := ((exact_Lk_sandwich c hc).1 k).2
  have hLk_pow := Nat.pow_le_pow_left hLk (6 * d * q)
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hLk_pow
  have hLam := Lambda_pass_mul_le c d
  have hLam_pow := Nat.pow_le_pow_left hLam (k * p)
  rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hLam_pow
  have hpos : 0 < (d + 1) ^ (2 * (k * p)) * c ^ (4 * d * (k * p)) * (c - 1) ^ (k * (6 * d * q)) :=
    Nat.mul_pos (Nat.mul_pos (pow_pos_of_pos (by omega) _) (pow_pos_of_pos (by omega) _))
      (pow_pos_of_pos (by omega) _)
  have hlt2 := Nat.mul_lt_mul_of_pos_right hlt1 hpos
  have hLHS : (64 ^ q * (d + 1) ^ (2 * p) * c ^ (4 * d * p) * (c + 2) ^ (6 * d * q)) ^ k
      ≤ 64 ^ (k * q) * (2 * L_pass c k - 1) ^ (6 * d * q) *
        ((d + 1) ^ (2 * (k * p)) * c ^ (4 * d * (k * p)) * (c - 1) ^ (k * (6 * d * q))) := by
    rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
    have hm := Nat.mul_le_mul_left (64 ^ (k * q) * (d + 1) ^ (2 * (k * p)) * c ^ (4 * d * (k * p))) hLk_pow
    have e1 : q * k = k * q := Nat.mul_comm _ _
    have e2 : 2 * p * k = 2 * (k * p) := by ac_rfl
    have e3 : 4 * d * p * k = 4 * d * (k * p) := by ac_rfl
    have e4 : 6 * d * q * k = k * (6 * d * q) := Nat.mul_comm _ _
    rw [e1, e2, e3, e4]
    have eR : 64 ^ (k * q) * (d + 1) ^ (2 * (k * p)) * c ^ (4 * d * (k * p)) *
        ((2 * L_pass c k - 1) ^ (6 * d * q) * (c - 1) ^ (k * (6 * d * q)))
        = 64 ^ (k * q) * (2 * L_pass c k - 1) ^ (6 * d * q) *
          ((d + 1) ^ (2 * (k * p)) * c ^ (4 * d * (k * p)) * (c - 1) ^ (k * (6 * d * q))) := by ac_rfl
    rwa [eR] at hm
  have hRHS : Lambda_pass c d ^ (k * p) *
      ((d + 1) ^ (2 * (k * p)) * c ^ (4 * d * (k * p)) * (c - 1) ^ (k * (6 * d * q)))
      ≤ ((c + 2) ^ (4 * d * p) * (c - 1) ^ (6 * d * q)) ^ k := by
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
    have hm := Nat.mul_le_mul_right ((c - 1) ^ (k * (6 * d * q))) hLam_pow
    have e1 : 4 * d * (k * p) = 4 * d * p * k := by ac_rfl
    have e2 : k * (6 * d * q) = 6 * d * q * k := Nat.mul_comm _ _
    have eL : Lambda_pass c d ^ (k * p) *
        ((d + 1) ^ (2 * (k * p)) * c ^ (4 * d * (k * p)) * (c - 1) ^ (k * (6 * d * q)))
        = Lambda_pass c d ^ (k * p) * (d + 1) ^ (2 * (k * p)) * c ^ (4 * d * (k * p)) *
          (c - 1) ^ (k * (6 * d * q)) := by ac_rfl
    rw [eL, ← e1, ← e2]
    exact hm
  exact lt_of_pow_lt_pow_left (Nat.lt_of_le_of_lt hLHS (Nat.lt_of_lt_of_le hlt2 hRHS))

/-- Unconditional structural floor: `w^18 * v_k^9 < E_k^4` for ALL `c ≥ 2, d ≥ 1, k ≥ 1, w ≥ 1`. -/
theorem w18_vk9_lt_Ek4 {c d k : Nat} (hc : 2 ≤ c) (hd : 1 ≤ d) (hk : 1 ≤ k) (hw : 1 ≤ w_pass c d) :
    (w_pass c d) ^ 18 * (v_k_pass c d k) ^ 9 < (E_k_pass c d k) ^ 4 := by
  unfold v_k_pass E_k_pass
  rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow]
  rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
  have h1 : Lambda_pass c d ^ (k * 9) < (2 * L_pass c k - 1) ^ (6 * d * 4) := by
    have hcub := (pass_rate_strictly_above_9_4 c hc).2
    have hcub_pow : ((c + 2) ^ 9 * (c - 1) ^ 6) ^ (4 * d * k) < ((c + 2) ^ 6 * c ^ 9) ^ (4 * d * k) :=
      pow_lt_pow_left_of_lt (Nat.mul_pos (Nat.mul_pos (by decide) hd) hk) hcub
    rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hcub_pow
    have hLam : Lambda_pass c d * c ^ (4 * d) ≤ (c + 2) ^ (4 * d) := by
      have h0 := Lambda_pass_mul_le c d
      have hd1 : 1 ≤ (d + 1) ^ 2 := pow_pos_of_pos (by omega) 2
      have hmul : Lambda_pass c d * c ^ (4 * d) ≤ Lambda_pass c d * (d + 1) ^ 2 * c ^ (4 * d) := by
        have hm := Nat.mul_le_mul_left (Lambda_pass c d) hd1
        have hm2 := Nat.mul_le_mul_right (c ^ (4 * d)) hm
        simpa [Nat.mul_one] using hm2
      exact Nat.le_trans hmul h0
    have hLam_p := Nat.pow_le_pow_left hLam (k * 9)
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hLam_p
    have hLk := ((exact_Lk_sandwich c hc).1 k).2
    have hLk_p := Nat.pow_le_pow_left hLk (6 * d * 4)
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hLk_p
    have hcomb : Lambda_pass c d ^ (k * 9) * (c ^ (4 * d * (k * 9)) * (c - 1) ^ (k * (6 * d * 4)))
        < (2 * L_pass c k - 1) ^ (6 * d * 4) * (c ^ (4 * d * (k * 9)) * (c - 1) ^ (k * (6 * d * 4))) := by
      have e1 : 4 * d * (k * 9) = 9 * (4 * d * k) := by ac_rfl
      have e2 : k * (6 * d * 4) = 6 * (4 * d * k) := by ac_rfl
      have s1 : Lambda_pass c d ^ (k * 9) * (c ^ (4 * d * (k * 9)) * (c - 1) ^ (k * (6 * d * 4)))
          ≤ (c + 2) ^ (9 * (4 * d * k)) * (c - 1) ^ (6 * (4 * d * k)) := by
        have hm := Nat.mul_le_mul_right ((c - 1) ^ (k * (6 * d * 4))) hLam_p
        rw [← e1, ← e2]
        simpa [Nat.mul_assoc] using hm
      have s2 : (c + 2) ^ (6 * (4 * d * k)) * c ^ (9 * (4 * d * k))
          ≤ (2 * L_pass c k - 1) ^ (6 * d * 4) * (c ^ (4 * d * (k * 9)) * (c - 1) ^ (k * (6 * d * 4))) := by
        have hm := Nat.mul_le_mul_right (c ^ (9 * (4 * d * k))) hLk_p
        rw [e1, e2]
        have eR : (2 * L_pass c k - 1) ^ (6 * d * 4) * (c - 1) ^ (6 * (4 * d * k)) * c ^ (9 * (4 * d * k))
            = (2 * L_pass c k - 1) ^ (6 * d * 4) * (c ^ (9 * (4 * d * k)) * (c - 1) ^ (6 * (4 * d * k))) := by ac_rfl
        rwa [e2, eR] at hm
      exact Nat.lt_of_le_of_lt s1 (Nat.lt_of_lt_of_le hcub_pow s2)
    exact Nat.lt_of_mul_lt_mul_right hcomb
  have hw36 : w_pass c d ^ 18 * w_pass c d ^ (2 * 9) = w_pass c d ^ (9 * 4) := by rw [← Nat.pow_add]
  have h64 : 1 ≤ 64 ^ (k * 4) := pow_pos_of_pos (by decide) _
  have hpos_w : 0 < w_pass c d ^ (9 * 4) := pow_pos_of_pos hw _
  have hlt2 := Nat.mul_lt_mul_of_pos_left h1 hpos_w
  have hle3 : w_pass c d ^ (9 * 4) * (2 * L_pass c k - 1) ^ (6 * d * 4)
      ≤ 64 ^ (k * 4) * w_pass c d ^ (9 * 4) * (2 * L_pass c k - 1) ^ (6 * d * 4) := by
    have hm := Nat.mul_le_mul_right (w_pass c d ^ (9 * 4) * (2 * L_pass c k - 1) ^ (6 * d * 4)) h64
    simpa [Nat.one_mul, Nat.mul_assoc] using hm
  have eL : w_pass c d ^ 18 * (w_pass c d ^ (2 * 9) * Lambda_pass c d ^ (k * 9))
      = w_pass c d ^ (9 * 4) * Lambda_pass c d ^ (k * 9) := by rw [← Nat.mul_assoc, hw36]
  rw [eL]
  exact Nat.lt_of_lt_of_le hlt2 hle3

/-- General pure-integer lower bound on `v_k` in terms of `w`:
    `w^(18*q) < v_k^(4*p - 9*q)` for every valid triple with `4*p ≥ 9*q`. -/
theorem universal_vk_pow_gt_w_pow_general {p q c d k : Nat}
    (hV : ValidPassTriple p q c d k) (hq : 1 ≤ q) (h94 : 9 * q ≤ 4 * p) :
    (w_pass c d) ^ (18 * q) < (v_k_pass c d k) ^ (4 * p - 9 * q) := by
  rcases hV with ⟨hc, hd, hk, hw, _hL, hlt⟩
  have hbase := w18_vk9_lt_Ek4 hc hd hk hw
  have h1 : (w_pass c d ^ 18 * v_k_pass c d k ^ 9) ^ q < (E_k_pass c d k ^ 4) ^ q :=
    pow_lt_pow_left_of_lt hq hbase
  have h2 : (E_k_pass c d k ^ q) ^ 4 < (v_k_pass c d k ^ p) ^ 4 :=
    pow_lt_pow_left_of_lt (by decide) hlt
  have hEq : (E_k_pass c d k ^ 4) ^ q = (E_k_pass c d k ^ q) ^ 4 := by
    rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
  have hcomb := Nat.lt_trans h1 (hEq ▸ h2)
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hcomb
  have hsplit : v_k_pass c d k ^ (p * 4) = v_k_pass c d k ^ (4 * p - 9 * q) * v_k_pass c d k ^ (9 * q) := by
    rw [← Nat.pow_add]
    have : 4 * p - 9 * q + 9 * q = p * 4 := by omega
    rw [this]
  rw [hsplit] at hcomb
  exact Nat.lt_of_mul_lt_mul_right hcomb

/-- Exact Pass-paper corollary at `τ = 9/4 + a/b` (`p = 9*b + 4*a, q = 4*b`):
    `(v_k_pass c d k) ^ (4 * a) > (w_pass c d) ^ (18 * b)`. -/
theorem universal_vk_pow_gt_w_pow {a b c d k : Nat} (hb : 1 ≤ b)
    (hV : ValidPassTriple (9 * b + 4 * a) (4 * b) c d k) :
    (w_pass c d) ^ (18 * b) < (v_k_pass c d k) ^ (4 * a) := by
  have h := universal_vk_pow_gt_w_pow_general hV (by omega) (by omega)
  have e1 : 18 * (4 * b) = (18 * b) * 4 := by omega
  have e2 : 4 * (9 * b + 4 * a) - 9 * (4 * b) = (4 * a) * 4 := by omega
  rw [e1, e2, Nat.pow_mul (w_pass c d) (18 * b) 4, Nat.pow_mul (v_k_pass c d k) (4 * a) 4] at h
  exact lt_of_pow_lt_pow_left h

/-! ### Universal `c ≥ c_min` criterion via unimodality -/

theorem universal_c_min_of_step {p q c_min c d k : Nat}
    (hV : ValidPassTriple p q c d k) (hτ : 2 * p ≤ 9 * q) (h94 : 9 * q ≤ 4 * p)
    (hcm : 3 ≤ c_min)
    (hmono : (4 * p - 9 * q) * (c_min - 2) ≤ 9 * q)
    (hf_le : (c_min + 1) ^ (2 * p - 3 * q) * (c_min - 2) ^ (3 * q) ≤ (c_min - 1) ^ (2 * p)) :
    c_min ≤ c := by
  have hround := universal_round_necessary hV hτ
  rcases hV with ⟨hc, hd, _hk, _hw, _hL, _hlt⟩
  have hdrop : c ^ (4 * d * p) * (c + 2) ^ (6 * d * q) < (c + 2) ^ (4 * d * p) * (c - 1) ^ (6 * d * q) := by
    have hge1 : 1 ≤ 64 ^ q * (d + 1) ^ (2 * p) :=
      Nat.mul_pos (pow_pos_of_pos (by decide) q) (pow_pos_of_pos (by omega) _)
    have hm := Nat.mul_le_mul_right (c ^ (4 * d * p) * (c + 2) ^ (6 * d * q)) hge1
    simp only [Nat.one_mul] at hm
    have eR : 64 ^ q * (d + 1) ^ (2 * p) * (c ^ (4 * d * p) * (c + 2) ^ (6 * d * q))
        = 64 ^ q * (d + 1) ^ (2 * p) * c ^ (4 * d * p) * (c + 2) ^ (6 * d * q) := by ac_rfl
    exact Nat.lt_of_le_of_lt (eR ▸ hm) hround
  have hsplit : (c + 2) ^ (4 * d * p) = (c + 2) ^ (2 * d * (2 * p - 3 * q)) * (c + 2) ^ (6 * d * q) := by
    rw [← Nat.pow_add]
    have : 2 * d * (2 * p - 3 * q) + 6 * d * q = 4 * d * p := by
      have h1 : 2 * d * (2 * p - 3 * q) + 2 * d * (3 * q) = 2 * d * (2 * p) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
      have h2 : 2 * d * (3 * q) = 6 * d * q := by ac_rfl
      have h3 : 2 * d * (2 * p) = 4 * d * p := by ac_rfl
      omega
    rw [this]
  rw [hsplit] at hdrop
  have hcancel : c ^ (4 * d * p) < (c + 2) ^ (2 * d * (2 * p - 3 * q)) * (c - 1) ^ (6 * d * q) := by
    have eR : (c + 2) ^ (2 * d * (2 * p - 3 * q)) * (c + 2) ^ (6 * d * q) * (c - 1) ^ (6 * d * q)
        = ((c + 2) ^ (2 * d * (2 * p - 3 * q)) * (c - 1) ^ (6 * d * q)) * (c + 2) ^ (6 * d * q) := by ac_rfl
    rw [eR] at hdrop
    exact Nat.lt_of_mul_lt_mul_right hdrop
  have hroot : c ^ (2 * p) < (c + 2) ^ (2 * p - 3 * q) * (c - 1) ^ (3 * q) := by
    apply lt_of_pow_lt_pow_left (n := 2 * d)
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
    have e1 : 2 * p * (2 * d) = 4 * d * p := by ac_rfl
    have e2 : (2 * p - 3 * q) * (2 * d) = 2 * d * (2 * p - 3 * q) := Nat.mul_comm _ _
    have e3 : 3 * q * (2 * d) = 6 * d * q := by ac_rfl
    rwa [e1, e2, e3]
  by_cases hge : c_min ≤ c
  · exact hge
  · exfalso
    have hle : c ≤ c_min - 1 := by omega
    have hinc := f_mono_inc_range p q c (c_min - 1) hc hle h94 (by
      have : c_min - 1 - 1 = c_min - 2 := by omega
      rwa [this])
    have he1 : (c_min - 1) + 2 = c_min + 1 := by omega
    have he2 : (c_min - 1) - 1 = c_min - 2 := by omega
    rw [he1, he2] at hinc
    have hmul := Nat.mul_le_mul_right (c ^ (2 * p)) hf_le
    have hcomb := Nat.le_trans hinc hmul
    have hlt_c := Nat.mul_lt_mul_of_pos_right hroot (pow_pos_of_pos (a := c_min - 1) (by omega) (2 * p))
    have eR : (c_min - 1) ^ (2 * p) * c ^ (2 * p) = c ^ (2 * p) * (c_min - 1) ^ (2 * p) := Nat.mul_comm _ _
    rw [eR] at hcomb
    omega

/-! ### Generic pure-`Nat` dyadic band and tail universal lower-bound engines (symbolic `Q`) -/

theorem succ_le_four_pow (d : Nat) : d + 1 ≤ 4 ^ d := by
  induction d with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

theorem succ_le_add_two_pow_two_mul (c d : Nat) (hc : 2 ≤ c) : d + 1 ≤ (c + 2) ^ (2 * d) := by
  calc d + 1 ≤ 4 ^ d := succ_le_four_pow d
    _ ≤ 4 ^ (2 * d) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ (c + 2) ^ (2 * d) := Nat.pow_le_pow_left (by omega) (2 * d)

theorem two_mul_succ_log2Le_linear (Q d0 pen_Q : Nat) (_hd0 : 1 ≤ d0)
    (hbase : Log2Le (2 * (d0 + 1)) (d0 * pen_Q) Q)
    (hstep : 2 * Q ≤ pen_Q * (d0 + 1)) :
    ∀ d, d0 ≤ d → Log2Le (2 * (d + 1)) (d * pen_Q) Q := by
  intro d hd
  induction hd with
  | refl => exact hbase
  | @step m hm ih =>
    have hm' : d0 ≤ m := hm
    have hes := Nat.le_of_lt (e_sandwich (m + 1) 1 (by omega) (by decide))
    have hes' : (m + 2) ^ (m + 1) ≤ (m + 1) ^ (m + 1) * 2 ^ 2 := by
      have h1 : 1 ^ (1 + 1) = 1 := by decide
      rw [h1, Nat.mul_one] at hes
      exact hes
    have hpowQ := Nat.pow_le_pow_left hes' Q
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hpowQ
    have h2Q : 2 * Q ≤ pen_Q * (m + 1) :=
      Nat.le_trans hstep (Nat.mul_le_mul_left pen_Q (by omega))
    have hpow2 : 2 ^ (2 * Q) ≤ 2 ^ (pen_Q * (m + 1)) := Nat.pow_le_pow_right (by decide) h2Q
    have hstep1 : ((m + 2) ^ Q) ^ (m + 1) ≤ (2 ^ pen_Q * (m + 1) ^ Q) ^ (m + 1) := by
      rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
      have hmul := Nat.mul_le_mul_left ((m + 1) ^ ((m + 1) * Q)) hpow2
      have htr := Nat.le_trans hpowQ hmul
      have eL : Q * (m + 1) = (m + 1) * Q := Nat.mul_comm _ _
      rw [eL]
      have eR : (m + 1) ^ ((m + 1) * Q) * 2 ^ (pen_Q * (m + 1))
          = 2 ^ (pen_Q * (m + 1)) * (m + 1) ^ ((m + 1) * Q) := Nat.mul_comm _ _
      rwa [eR] at htr
    have hroot : (m + 2) ^ Q ≤ 2 ^ pen_Q * (m + 1) ^ Q :=
      le_of_pow_le_pow_left (by omega) hstep1
    unfold Log2Le at ih ⊢
    calc (2 * (m + 1 + 1)) ^ Q
        = 2 ^ Q * (m + 2) ^ Q := Nat.mul_pow 2 (m + 2) Q
      _ ≤ 2 ^ Q * (2 ^ pen_Q * (m + 1) ^ Q) := Nat.mul_le_mul_left _ hroot
      _ = 2 ^ pen_Q * (2 ^ Q * (m + 1) ^ Q) := by ac_rfl
      _ = 2 ^ pen_Q * (2 * (m + 1)) ^ Q := by rw [Nat.mul_pow]
      _ ≤ 2 ^ pen_Q * 2 ^ (m * pen_Q) := Nat.mul_le_mul_left _ ih
      _ = 2 ^ ((m + 1) * pen_Q) := by
        rw [← Nat.pow_add, Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem w_pass_log2Ge_linear {Q c_lo c d0 d lc2 pen_Q : Nat}
    (hc_lo : 2 ≤ c_lo) (hc : c_lo ≤ c) (hd0 : 1 ≤ d0) (hd : d0 ≤ d)
    (hlc2 : Log2Ge (c_lo + 2) lc2 Q)
    (h2d : Log2Le (2 * (d0 + 1)) (d0 * pen_Q) Q)
    (hstep : 2 * Q ≤ pen_Q * (d0 + 1))
    (hpen : pen_Q ≤ 2 * lc2) :
    Log2Ge (w_pass c d) (d * (2 * lc2 - pen_Q)) Q := by
  have hlin := two_mul_succ_log2Le_linear Q d0 pen_Q hd0 h2d hstep d hd
  have hnum : Log2Ge ((c + 2) ^ (2 * d)) (d * (2 * lc2)) Q := by
    have h1 := (hlc2.mono_left (show c_lo + 2 ≤ c + 2 by omega)).pow (2 * d)
    have e : 2 * d * lc2 = d * (2 * lc2) := by ac_rfl
    rwa [e] at h1
  have hge_div : (c + 2) ^ (2 * d) ≤ (2 * (d + 1)) * w_pass c d := by
    unfold w_pass
    have hw1 : 1 ≤ (c + 2) ^ (2 * d) / (d + 1) :=
      Nat.div_pos (succ_le_add_two_pow_two_mul c d (by omega)) (by omega)
    have hlt := Nat.lt_div_mul_add (a := (c + 2) ^ (2 * d)) (b := d + 1) (by omega)
    have h1 : (d + 1) * 1 ≤ (d + 1) * ((c + 2) ^ (2 * d) / (d + 1)) := Nat.mul_le_mul_left _ hw1
    have e1 : (c + 2) ^ (2 * d) / (d + 1) * (d + 1) + (d + 1)
        = (d + 1) * ((c + 2) ^ (2 * d) / (d + 1)) + (d + 1) * 1 := by rw [Nat.mul_comm, Nat.mul_one]
    have e2 : 2 * (d + 1) * ((c + 2) ^ (2 * d) / (d + 1))
        = (d + 1) * ((c + 2) ^ (2 * d) / (d + 1)) + (d + 1) * ((c + 2) ^ (2 * d) / (d + 1)) := by
      rw [Nat.two_mul, Nat.add_mul]
    omega
  have hsub := Log2Ge.of_mul_ge hge_div hnum hlin (Nat.mul_le_mul_left d hpen)
  have heq : d * (2 * lc2) - d * pen_Q = d * (2 * lc2 - pen_Q) := (Nat.mul_sub d (2 * lc2) pen_Q).symm
  rwa [heq] at hsub

theorem ceiling_boost_univ {Q c_lo c k lj l22 BL : Nat}
    (hc_lo : 2 ≤ c_lo) (hc : c_lo ≤ c) (hk : (c - 1) / 3 ≤ k)
    (hlj : Log2Ge (2 * ((c_lo - 1) / 3) + 1) lj Q)
    (hl22 : Log2Le 22 l22 Q)
    (hBL : 3 * BL + l22 ≤ 3 * lj) :
    2 ^ BL * ((c + 2) ^ k) ^ Q ≤ ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ Q := by
  let j0 := (c - 1) / 3
  let j0_lo := (c_lo - 1) / 3
  have hj0_le : j0_lo ≤ j0 := Nat.div_le_div_right (by omega)
  have hsand := ((exact_Lk_sandwich c (by omega)).2.1.2) k hk
  have h1 : (2 * j0_lo + 1) * (c + 2) ^ (k - j0) ≤ (2 * L_pass c k - 1) * (c - 1) ^ (k - j0) :=
    Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hsand
  have h2 : (2 * j0_lo + 1) ^ 3 * (c + 2) ^ (3 * (k - j0)) * (c - 1) ^ (3 * j0)
      ≤ (2 * L_pass c k - 1) ^ 3 * (c - 1) ^ (3 * k) := by
    have hm := Nat.mul_le_mul_right ((c - 1) ^ j0) h1
    have hp := Nat.pow_le_pow_left hm 3
    rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hp
    have he1 : (k - j0) * 3 = 3 * (k - j0) := Nat.mul_comm _ _
    have he2 : j0 * 3 = 3 * j0 := Nat.mul_comm _ _
    have he3 : (c - 1) ^ (3 * (k - j0)) * (c - 1) ^ (3 * j0) = (c - 1) ^ (3 * k) := by
      rw [← Nat.pow_add]
      have : 3 * (k - j0) + 3 * j0 = 3 * k := by omega
      rw [this]
    rw [he1, he2, Nat.mul_assoc ((2 * L_pass c k - 1) ^ 3), he3] at hp
    exact hp
  have h22 : (c + 2) ^ (3 * j0) ≤ 22 * (c - 1) ^ (3 * j0) := by
    have hlt22 := Nat.le_of_lt (add_two_div_sub_one_pow_lt_22 c (by omega))
    have hrem : 3 * j0 ≤ c - 1 := by dsimp only [j0]; omega
    have hgap : (c - 1) ^ (c - 1 - 3 * j0) ≤ (c + 2) ^ (c - 1 - 3 * j0) :=
      Nat.pow_le_pow_left (by omega) _
    have hm := Nat.mul_le_mul_left ((c + 2) ^ (3 * j0)) hgap
    have eL : (c + 2) ^ (3 * j0) * (c + 2) ^ (c - 1 - 3 * j0) = (c + 2) ^ (c - 1) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hrem]
    have eR : 22 * (c - 1) ^ (c - 1) = (22 * (c - 1) ^ (3 * j0)) * (c - 1) ^ (c - 1 - 3 * j0) := by
      rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le hrem]
    rw [eL] at hm
    have hcomb := Nat.le_trans hm (eR ▸ hlt22)
    exact Nat.le_of_mul_le_mul_right hcomb (pow_pos_of_pos (a := c - 1) (by omega) _)
  have h3 : (2 * j0_lo + 1) ^ 3 * (c + 2) ^ (3 * k) ≤ 22 * ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ 3 := by
    have hm1 := Nat.mul_le_mul_left ((2 * j0_lo + 1) ^ 3 * (c + 2) ^ (3 * (k - j0))) h22
    have hm2 := Nat.mul_le_mul_left 22 h2
    have eL : (2 * j0_lo + 1) ^ 3 * (c + 2) ^ (3 * (k - j0)) * (c + 2) ^ (3 * j0)
        = (2 * j0_lo + 1) ^ 3 * (c + 2) ^ (3 * k) := by
      rw [Nat.mul_assoc, ← Nat.pow_add]
      have : 3 * (k - j0) + 3 * j0 = 3 * k := by omega
      rw [this]
    have eM : (2 * j0_lo + 1) ^ 3 * (c + 2) ^ (3 * (k - j0)) * (22 * (c - 1) ^ (3 * j0))
        = 22 * ((2 * j0_lo + 1) ^ 3 * (c + 2) ^ (3 * (k - j0)) * (c - 1) ^ (3 * j0)) := by ac_rfl
    have eR : 22 * ((2 * L_pass c k - 1) ^ 3 * (c - 1) ^ (3 * k))
        = 22 * ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ 3 := by
      rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm k 3]
    rw [← eL, ← eR]
    exact Nat.le_trans hm1 (eM ▸ hm2)
  have h3Q := Nat.pow_le_pow_left h3 Q
  rw [Nat.mul_pow, Nat.mul_pow] at h3Q
  have hlj3 : 2 ^ (3 * lj) ≤ ((2 * j0_lo + 1) ^ 3) ^ Q := hlj.pow 3
  have hchain : (2 ^ (3 * BL) * ((c + 2) ^ (3 * k)) ^ Q) * 2 ^ l22
      ≤ (((2 * L_pass c k - 1) * (c - 1) ^ k) ^ 3) ^ Q * 2 ^ l22 := by
    have s0 : 2 ^ (3 * BL) * 2 ^ l22 ≤ 2 ^ (3 * lj) := by
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) hBL
    have s1 := Nat.mul_le_mul_right (((c + 2) ^ (3 * k)) ^ Q) (Nat.le_trans s0 hlj3)
    have s2 := Nat.mul_le_mul_right ((((2 * L_pass c k - 1) * (c - 1) ^ k) ^ 3) ^ Q) hl22
    have eL : (2 ^ (3 * BL) * ((c + 2) ^ (3 * k)) ^ Q) * 2 ^ l22
        = 2 ^ (3 * BL) * 2 ^ l22 * ((c + 2) ^ (3 * k)) ^ Q := by ac_rfl
    have eR : 2 ^ l22 * (((2 * L_pass c k - 1) * (c - 1) ^ k) ^ 3) ^ Q
        = (((2 * L_pass c k - 1) * (c - 1) ^ k) ^ 3) ^ Q * 2 ^ l22 := Nat.mul_comm _ _
    rw [eL]
    exact Nat.le_trans s1 (Nat.le_trans h3Q (eR ▸ s2))
  have hcancel := Nat.le_of_mul_le_mul_right hchain (Nat.two_pow_pos _)
  have hcube : (2 ^ BL * ((c + 2) ^ k) ^ Q) ^ 3 ≤ (((2 * L_pass c k - 1) * (c - 1) ^ k) ^ Q) ^ 3 := by
    have eL : (2 ^ BL * ((c + 2) ^ k) ^ Q) ^ 3 = 2 ^ (3 * BL) * ((c + 2) ^ (3 * k)) ^ Q := by
      rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
      have a1 : BL * 3 = 3 * BL := Nat.mul_comm _ _
      have a2 : k * (Q * 3) = 3 * k * Q := by ac_rfl
      rw [a1, a2]
    have eR : (((2 * L_pass c k - 1) * (c - 1) ^ k) ^ Q) ^ 3
        = (((2 * L_pass c k - 1) * (c - 1) ^ k) ^ 3) ^ Q := by
      rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm Q 3]
    rw [eL, eR]
    exact hcancel
  exact le_of_pow_le_pow_left (by decide) hcube

theorem ceiling_boost_narrow {Q c_lo c_hi c k lj lc2_hi lcm1_lo BL : Nat}
    (hc_lo : 2 ≤ c_lo) (h1 : c_lo ≤ c) (h2 : c ≤ c_hi) (hk : (c_hi - 1) / 3 ≤ k)
    (hlj : Log2Ge (2 * ((c_lo - 1) / 3) + 1) lj Q)
    (hlc2 : Log2Le (c_lo + 2) lc2_hi Q)
    (hlcm1 : Log2Ge (c_lo - 1) lcm1_lo Q)
    (hBL : BL + ((c_hi - 1) / 3) * lc2_hi ≤ lj + ((c_hi - 1) / 3) * lcm1_lo) :
    2 ^ BL * ((c + 2) ^ k) ^ Q ≤ ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ Q := by
  let j0 := (c - 1) / 3
  let j0_lo := (c_lo - 1) / 3
  let j0_hi := (c_hi - 1) / 3
  have hj0_lo : j0_lo ≤ j0 := Nat.div_le_div_right (by omega)
  have hj0_hi : j0 ≤ j0_hi := Nat.div_le_div_right (by omega)
  have hsand := ((exact_Lk_sandwich c (by omega)).2.1.2) k (Nat.le_trans hj0_hi hk)
  have hstep1 : (2 * j0_lo + 1) * (c + 2) ^ (k - j0) * (c - 1) ^ j0
      ≤ (2 * L_pass c k - 1) * (c - 1) ^ k := by
    have hlo_le : 2 * j0_lo + 1 ≤ 2 * j0 + 1 := by omega
    have hm := Nat.mul_le_mul_right ((c - 1) ^ j0)
      (Nat.le_trans (Nat.mul_le_mul_right ((c + 2) ^ (k - j0)) hlo_le) hsand)
    have eR : (2 * L_pass c k - 1) * (c - 1) ^ (k - j0) * (c - 1) ^ j0
        = (2 * L_pass c k - 1) * (c - 1) ^ k := by
      rw [Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel (Nat.le_trans hj0_hi hk)]
    rwa [eR] at hm
  have hrat : (c + 2) * (c_lo - 1) ≤ (c_lo + 2) * (c - 1) := by
    apply nat_le_of_int
    have h1i : ((c - 1 : Nat) : Int) = (c : Int) - 1 := by omega
    have h2i : ((c_lo - 1 : Nat) : Int) = (c_lo : Int) - 1 := by omega
    simp only [Int.natCast_mul, Int.natCast_add]; rw [h1i, h2i]
    change ((c : Int) + 2) * ((c_lo : Int) - 1) ≤ ((c_lo : Int) + 2) * ((c : Int) - 1)
    have hid : ((c_lo : Int) + 2) * ((c : Int) - 1) - ((c : Int) + 2) * ((c_lo : Int) - 1)
        = 3 * ((c : Int) - c_lo) := by grind
    omega
  have hrat_j0 : (c + 2) ^ j0 * (c_lo - 1) ^ j0_hi ≤ (c_lo + 2) ^ j0_hi * (c - 1) ^ j0 := by
    have hp := Nat.pow_le_pow_left hrat j0
    rw [Nat.mul_pow, Nat.mul_pow] at hp
    have hgap : (c_lo - 1) ^ (j0_hi - j0) ≤ (c_lo + 2) ^ (j0_hi - j0) := Nat.pow_le_pow_left (by omega) _
    have hm := Nat.mul_le_mul hp hgap
    have eL : (c + 2) ^ j0 * (c_lo - 1) ^ j0 * (c_lo - 1) ^ (j0_hi - j0)
        = (c + 2) ^ j0 * (c_lo - 1) ^ j0_hi := by
      rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le hj0_hi]
    have eR : (c_lo + 2) ^ j0 * (c - 1) ^ j0 * (c_lo + 2) ^ (j0_hi - j0)
        = (c_lo + 2) ^ j0_hi * (c - 1) ^ j0 := by
      have : (c_lo + 2) ^ j0 * (c_lo + 2) ^ (j0_hi - j0) = (c_lo + 2) ^ j0_hi := by
        rw [← Nat.pow_add, Nat.add_sub_of_le hj0_hi]
      calc (c_lo + 2) ^ j0 * (c - 1) ^ j0 * (c_lo + 2) ^ (j0_hi - j0)
          = (c_lo + 2) ^ j0 * (c_lo + 2) ^ (j0_hi - j0) * (c - 1) ^ j0 := by ac_rfl
        _ = (c_lo + 2) ^ j0_hi * (c - 1) ^ j0 := by rw [this]
    rwa [eL, eR] at hm
  have hcomb : (2 * j0_lo + 1) * (c_lo - 1) ^ j0_hi * (c + 2) ^ k
      ≤ (c_lo + 2) ^ j0_hi * ((2 * L_pass c k - 1) * (c - 1) ^ k) := by
    have hm1 := Nat.mul_le_mul_left ((2 * j0_lo + 1) * (c + 2) ^ (k - j0)) hrat_j0
    have hm2 := Nat.mul_le_mul_left ((c_lo + 2) ^ j0_hi) hstep1
    have eL : (2 * j0_lo + 1) * (c + 2) ^ (k - j0) * ((c + 2) ^ j0 * (c_lo - 1) ^ j0_hi)
        = (2 * j0_lo + 1) * (c_lo - 1) ^ j0_hi * (c + 2) ^ k := by
      have hkpow : (c + 2) ^ (k - j0) * (c + 2) ^ j0 = (c + 2) ^ k := by
        rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_trans hj0_hi hk)]
      calc (2 * j0_lo + 1) * (c + 2) ^ (k - j0) * ((c + 2) ^ j0 * (c_lo - 1) ^ j0_hi)
          = (2 * j0_lo + 1) * (c_lo - 1) ^ j0_hi * ((c + 2) ^ (k - j0) * (c + 2) ^ j0) := by ac_rfl
        _ = (2 * j0_lo + 1) * (c_lo - 1) ^ j0_hi * (c + 2) ^ k := by rw [hkpow]
    have eM : (2 * j0_lo + 1) * (c + 2) ^ (k - j0) * ((c_lo + 2) ^ j0_hi * (c - 1) ^ j0)
        = (c_lo + 2) ^ j0_hi * ((2 * j0_lo + 1) * (c + 2) ^ (k - j0) * (c - 1) ^ j0) := by ac_rfl
    rw [← eL]
    exact Nat.le_trans hm1 (eM ▸ hm2)
  have hQ := Nat.pow_le_pow_left hcomb Q
  rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow] at hQ
  have hL_ge : 2 ^ (lj + j0_hi * lcm1_lo) ≤ (2 * j0_lo + 1) ^ Q * ((c_lo - 1) ^ j0_hi) ^ Q := by
    rw [Nat.pow_add]; exact Nat.mul_le_mul hlj (hlcm1.pow j0_hi)
  have hR_le : ((c_lo + 2) ^ j0_hi) ^ Q ≤ 2 ^ (j0_hi * lc2_hi) := hlc2.pow j0_hi
  have hfin : (2 ^ BL * ((c + 2) ^ k) ^ Q) * 2 ^ (j0_hi * lc2_hi)
      ≤ ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ Q * 2 ^ (j0_hi * lc2_hi) := by
    have s0 : 2 ^ BL * 2 ^ (j0_hi * lc2_hi) ≤ 2 ^ (lj + j0_hi * lcm1_lo) := by
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) hBL
    have s1 := Nat.mul_le_mul_right (((c + 2) ^ k) ^ Q) (Nat.le_trans s0 hL_ge)
    have s2 := Nat.mul_le_mul_right (((2 * L_pass c k - 1) * (c - 1) ^ k) ^ Q) hR_le
    have eL : (2 ^ BL * ((c + 2) ^ k) ^ Q) * 2 ^ (j0_hi * lc2_hi)
        = 2 ^ BL * 2 ^ (j0_hi * lc2_hi) * ((c + 2) ^ k) ^ Q := by ac_rfl
    have eR : 2 ^ (j0_hi * lc2_hi) * ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ Q
        = ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ Q * 2 ^ (j0_hi * lc2_hi) := Nat.mul_comm _ _
    rw [eL]
    exact Nat.le_trans s1 (Nat.le_trans hQ (eR ▸ s2))
  exact Nat.le_of_mul_le_mul_right hfin (Nat.two_pow_pos _)

theorem ceiling_boost_zero (Q c k : Nat) (hc : 2 ≤ c) :
    2 ^ 0 * ((c + 2) ^ k) ^ Q ≤ ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ Q := by
  rw [Nat.pow_zero, Nat.one_mul]
  exact Nat.pow_le_pow_left ((exact_Lk_sandwich c hc).1 k).2 Q

theorem band_hG_of_log2 {Q p q c_g lc2 lcm1 lc G : Nat}
    (hlc2 : Log2Le (c_g + 2) lc2 Q)
    (hlcm1 : Log2Le (c_g - 1) lcm1 Q)
    (hlc : Log2Ge c_g lc Q)
    (hG : (4 * p - 6 * q) * lc2 + 6 * q * lcm1 ≤ G + 4 * p * lc) :
    ((c_g + 2) ^ (4 * p - 6 * q) * (c_g - 1) ^ (6 * q)) ^ Q ≤ 2 ^ G * (c_g ^ (4 * p)) ^ Q := by
  have hL : ((c_g + 2) ^ (4 * p - 6 * q) * (c_g - 1) ^ (6 * q)) ^ Q
      ≤ 2 ^ ((4 * p - 6 * q) * lc2 + 6 * q * lcm1) :=
    (hlc2.pow (4 * p - 6 * q)).mul (hlcm1.pow (6 * q))
  have hR : 2 ^ (4 * p * lc) ≤ (c_g ^ (4 * p)) ^ Q := hlc.pow (4 * p)
  have hmid : 2 ^ ((4 * p - 6 * q) * lc2 + 6 * q * lcm1) ≤ 2 ^ G * 2 ^ (4 * p * lc) := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) hG
  exact Nat.le_trans hL (Nat.le_trans hmid (Nat.mul_le_mul_left (2 ^ G) hR))

theorem band_hG_transfer {Q p q c c_g G : Nat} (hcg : 2 ≤ c_g)
    (hmono : ((c + 2) ^ (2 * p - 3 * q) * (c - 1) ^ (3 * q)) * c_g ^ (2 * p)
           ≤ ((c_g + 2) ^ (2 * p - 3 * q) * (c_g - 1) ^ (3 * q)) * c ^ (2 * p))
    (hGg : ((c_g + 2) ^ (4 * p - 6 * q) * (c_g - 1) ^ (6 * q)) ^ Q ≤ 2 ^ G * (c_g ^ (4 * p)) ^ Q) :
    ((c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q)) ^ Q ≤ 2 ^ G * (c ^ (4 * p)) ^ Q := by
  have hsq := Nat.pow_le_pow_left hmono 2
  rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow, Nat.mul_pow] at hsq
  rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hsq
  have e1 : (2 * p - 3 * q) * 2 = 4 * p - 6 * q := by omega
  have e2 : 3 * q * 2 = 6 * q := by omega
  have e3 : 2 * p * 2 = 4 * p := by omega
  rw [e1, e2, e3] at hsq
  have hQ := Nat.pow_le_pow_left hsq Q
  rw [Nat.mul_pow _ (c_g ^ (4 * p)), Nat.mul_pow _ (c ^ (4 * p))] at hQ
  have hmul := Nat.mul_le_mul_right ((c ^ (4 * p)) ^ Q) hGg
  have hcomb := Nat.le_trans hQ hmul
  have eR : 2 ^ G * (c_g ^ (4 * p)) ^ Q * (c ^ (4 * p)) ^ Q
      = (2 ^ G * (c ^ (4 * p)) ^ Q) * (c_g ^ (4 * p)) ^ Q := by ac_rfl
  rw [eR] at hcomb
  exact Nat.le_of_mul_le_mul_right hcomb (pow_pos_of_pos (pow_pos_of_pos (by omega) _) _)

theorem d_bootstrap_step {Q p q d G d_prev ld_prev d_next : Nat}
    (hroundQ : (64 ^ q * (d + 1) ^ (2 * p)) ^ Q < 2 ^ (d * G))
    (hd_prev : d_prev ≤ d)
    (hld : Log2Ge (d_prev + 1) ld_prev Q)
    (hstep : (d_next - 1) * G ≤ 6 * q * Q + 2 * p * ld_prev) :
    d_next ≤ d := by
  have h64 : Log2Ge (64 ^ q) (6 * q * Q) Q := by
    have h6 : Log2Ge 64 (6 * Q) Q := by
      have : (64 : Nat) = 2 ^ 6 := by decide
      rw [this]; exact Log2Ge.two_pow 6 Q
    have hp := h6.pow q
    have e : q * (6 * Q) = 6 * q * Q := by ac_rfl
    rwa [e] at hp
  have hd1 : Log2Ge ((d + 1) ^ (2 * p)) (2 * p * ld_prev) Q :=
    (hld.mono_left (show d_prev + 1 ≤ d + 1 by omega)).pow (2 * p)
  have hge := h64.mul hd1
  unfold Log2Ge at hge
  have hlt : 2 ^ (6 * q * Q + 2 * p * ld_prev) < 2 ^ (d * G) :=
    Nat.lt_of_le_of_lt hge hroundQ
  have hexp : 6 * q * Q + 2 * p * ld_prev < d * G := by
    by_cases h : 6 * q * Q + 2 * p * ld_prev < d * G
    · exact h
    · have := Nat.pow_le_pow_right (n := 2) (by decide) (show d * G ≤ 6 * q * Q + 2 * p * ld_prev by omega)
      omega
  by_cases h : d_next ≤ d
  · exact h
  · have hmul : d * G ≤ (d_next - 1) * G := Nat.mul_le_mul_right G (by omega)
    omega

/-- **MASTER FINITE-BAND UNIVERSAL LOWER BOUND ENGINE** (Pre-Bini + Post-Bini, symbolic `Q`!). -/
theorem band_universal_lb
    {Q p q c_lo c_hi c d k G d_lb ld_lb pen_Q Lw k_lb0 BL S R k_lb : Nat}
    (hQ : 0 < Q)
    (hV : ValidPassTriple p q c d k)
    (hτ : 2 * p ≤ 9 * q) (h94 : 9 * q ≤ 4 * p)
    (hc_lo : 2 ≤ c_lo) (hc1 : c_lo ≤ c) (hc2 : c ≤ c_hi)
    (hG : ((c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q)) ^ Q ≤ 2 ^ G * (c ^ (4 * p)) ^ Q)
    (hd_lb_pos : 1 ≤ d_lb)
    (hd_lb : (64 ^ q * (d + 1) ^ (2 * p)) ^ Q < 2 ^ (d * G) → d_lb ≤ d)
    (hld_lb : Log2Ge (d_lb + 1) ld_lb Q)
    (hlc2 : Log2Ge (c_lo + 2) ((Lw + pen_Q) / 2) Q)
    (hLw_even : Lw + pen_Q = 2 * ((Lw + pen_Q) / 2))
    (h2d : Log2Le (2 * (d_lb + 1)) (d_lb * pen_Q) Q)
    (hpen_step : 2 * Q ≤ pen_Q * (d_lb + 1))
    (hk_lb0 : k_lb0 * G ≤ (9 * q - 2 * p) * Lw)
    (hBL : k_lb0 ≤ k → 2 ^ BL * ((c + 2) ^ k) ^ Q ≤ ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ Q)
    (hS : 2 ^ S * (c_hi - 1) ^ Q ≤ (c_hi + 2) ^ Q)
    (hklb_pos : 1 ≤ k_lb)
    (hklb_def : k_lb * G ≤ (9 * q - 2 * p) * Lw + 6 * q * BL)
    (hR : R ^ 2 ≤ 4 * ((9 * q * Lw + 6 * q * BL) * G + 6 * q * S * ((9 * q - 2 * p) * Lw + 6 * q * BL))
                    * (6 * q * S * ((9 * q - 2 * p) * Lw + 6 * q * BL))
                    * (6 * q * Q + 2 * p * ld_lb) ^ 2) :
    Log2Ge (v_k_pass c d k)
      (((9 * q * Lw + 6 * q * BL) * G + 2 * (6 * q * S * ((9 * q - 2 * p) * Lw + 6 * q * BL)))
       * (6 * q * Q + 2 * p * ld_lb) + R)
      (p * Q * G ^ 2) ∧
    (∀ h, ValidPostBini p q c d k h →
      Log2Ge ((v_k_pass c d k) ^ h)
        (6 * q * S * (27 * q * (2 * k_lb - 1) * Lw
         * ((9 * q - 2 * p) * Lw + 6 * q * BL)
         * (6 * q * Q + 2 * p * ld_lb)))
        (p * Q * k_lb * G ^ 3)) := by
  have hV_copy := hV
  rcases hV with ⟨hc, hd, hk, hw, _hLam, hlt⟩
  have hroundQ : (64 ^ q * (d + 1) ^ (2 * p)) ^ Q < 2 ^ (d * G) := by
    have hr := universal_round_necessary hV_copy hτ
    have hsplit : (c + 2) ^ (4 * d * p) = (c + 2) ^ (d * (4 * p - 6 * q)) * (c + 2) ^ (6 * d * q) := by
      rw [← Nat.pow_add]
      have : d * (4 * p - 6 * q) + 6 * d * q = 4 * d * p := by
        have h1 : d * (4 * p - 6 * q) + d * (6 * q) = d * (4 * p) := by
          rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
        have h2 : d * (6 * q) = 6 * d * q := by ac_rfl
        have h3 : d * (4 * p) = 4 * d * p := by ac_rfl
        omega
      rw [this]
    rw [hsplit] at hr
    have hr1 : 64 ^ q * (d + 1) ^ (2 * p) * c ^ (4 * d * p)
        < (c + 2) ^ (d * (4 * p - 6 * q)) * (c - 1) ^ (6 * d * q) := by
      have eR : (c + 2) ^ (d * (4 * p - 6 * q)) * (c + 2) ^ (6 * d * q) * (c - 1) ^ (6 * d * q)
          = ((c + 2) ^ (d * (4 * p - 6 * q)) * (c - 1) ^ (6 * d * q)) * (c + 2) ^ (6 * d * q) := by ac_rfl
      rw [eR] at hr
      exact Nat.lt_of_mul_lt_mul_right hr
    have hrQ := pow_lt_pow_left_of_lt hQ hr1
    rw [Nat.mul_pow] at hrQ
    have hGd := Nat.pow_le_pow_left hG d
    rw [← Nat.pow_mul ((c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q)),
        Nat.mul_pow (2 ^ G), ← Nat.pow_mul 2, ← Nat.pow_mul (c ^ (4 * p)), Nat.mul_comm G d] at hGd
    have eL : ((c + 2) ^ (d * (4 * p - 6 * q)) * (c - 1) ^ (6 * d * q)) ^ Q
        = ((c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q)) ^ (Q * d) := by
      rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
      have a1 : d * (4 * p - 6 * q) * Q = (4 * p - 6 * q) * (Q * d) := by ac_rfl
      have a2 : 6 * d * q * Q = 6 * q * (Q * d) := by ac_rfl
      rw [a1, a2]
    have eR1 : (c ^ (4 * d * p)) ^ Q = (c ^ (4 * p)) ^ (Q * d) := by
      rw [← Nat.pow_mul, ← Nat.pow_mul]
      have : 4 * d * p * Q = 4 * p * (Q * d) := by ac_rfl
      rw [this]
    rw [eL, eR1] at hrQ
    exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_lt_of_le hrQ hGd)
  have hd_ge : d_lb ≤ d := hd_lb hroundQ
  let C0 := 6 * q * Q + 2 * p * ld_lb
  have hC0_ge : 2 ^ C0 ≤ (64 ^ q * (d + 1) ^ (2 * p)) ^ Q := by
    have h64 : Log2Ge (64 ^ q) (6 * q * Q) Q := by
      have h6 : Log2Ge 64 (6 * Q) Q := by
        have : (64 : Nat) = 2 ^ 6 := by decide
        rw [this]; exact Log2Ge.two_pow 6 Q
      have hp := h6.pow q
      have e : q * (6 * Q) = 6 * q * Q := by ac_rfl
      rwa [e] at hp
    exact h64.mul ((hld_lb.mono_left (show d_lb + 1 ≤ d + 1 by omega)).pow (2 * p))
  have hC0_lt : C0 < d * G := by
    have h2lt := Nat.lt_of_le_of_lt hC0_ge hroundQ
    by_cases h : C0 < d * G
    · exact h
    · have := Nat.pow_le_pow_right (n := 2) (by decide) (show d * G ≤ C0 by omega)
      omega
  have hw_lin : Log2Ge (w_pass c d) (d * Lw) Q := by
    have hpen_le : pen_Q ≤ 2 * ((Lw + pen_Q) / 2) := by omega
    have h := w_pass_log2Ge_linear hc_lo hc1 hd_lb_pos hd_ge hlc2 h2d hpen_step hpen_le
    have hLw_eq : 2 * ((Lw + pen_Q) / 2) - pen_Q = Lw := by omega
    rwa [hLw_eq] at h
  have hmaster : ∀ BL',
      2 ^ BL' * ((c + 2) ^ k) ^ Q ≤ ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ Q →
      d * ((9 * q - 2 * p) * Lw + 6 * q * BL') + k * C0 < k * d * G := by
    intro BL' hBL'
    have hlt_raw : w_pass c d ^ (9 * q - 2 * p) * 64 ^ (k * q) * (2 * L_pass c k - 1) ^ (6 * d * q)
        < Lambda_pass c d ^ (k * p) := by
      unfold E_k_pass v_k_pass at hlt
      rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow] at hlt
      rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hlt
      have hwsplit : w_pass c d ^ (9 * q) = w_pass c d ^ (9 * q - 2 * p) * w_pass c d ^ (2 * p) := by
        rw [← Nat.pow_add, Nat.sub_add_cancel hτ]
      rw [hwsplit] at hlt
      have eL : 64 ^ (k * q) * (w_pass c d ^ (9 * q - 2 * p) * w_pass c d ^ (2 * p))
          * (2 * L_pass c k - 1) ^ (6 * d * q)
          = (w_pass c d ^ (9 * q - 2 * p) * 64 ^ (k * q) * (2 * L_pass c k - 1) ^ (6 * d * q))
            * w_pass c d ^ (2 * p) := by ac_rfl
      have eR : w_pass c d ^ (2 * p) * Lambda_pass c d ^ (k * p)
          = Lambda_pass c d ^ (k * p) * w_pass c d ^ (2 * p) := Nat.mul_comm _ _
      rw [eL, eR] at hlt
      exact Nat.lt_of_mul_lt_mul_right hlt
    have hpos_m : 0 < (d + 1) ^ (2 * (k * p)) * c ^ (4 * d * (k * p)) * (c - 1) ^ (k * (6 * d * q)) :=
      Nat.mul_pos (Nat.mul_pos (pow_pos_of_pos (by omega) _) (pow_pos_of_pos (by omega) _))
        (pow_pos_of_pos (by omega) _)
    have hlt_m := Nat.mul_lt_mul_of_pos_right hlt_raw hpos_m
    have hLam_p := Nat.pow_le_pow_left (Lambda_pass_mul_le c d) (k * p)
    rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hLam_p
    have hlt_b : w_pass c d ^ (9 * q - 2 * p) * (64 ^ q * (d + 1) ^ (2 * p)) ^ k
        * ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (6 * d * q) * c ^ (4 * d * (k * p))
        < (c + 2) ^ (4 * d * (k * p)) * (c - 1) ^ (k * (6 * d * q)) := by
      have hm := Nat.mul_le_mul_right ((c - 1) ^ (k * (6 * d * q))) hLam_p
      have eL : w_pass c d ^ (9 * q - 2 * p) * 64 ^ (k * q) * (2 * L_pass c k - 1) ^ (6 * d * q)
          * ((d + 1) ^ (2 * (k * p)) * c ^ (4 * d * (k * p)) * (c - 1) ^ (k * (6 * d * q)))
          = w_pass c d ^ (9 * q - 2 * p) * (64 ^ q * (d + 1) ^ (2 * p)) ^ k
            * ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (6 * d * q) * c ^ (4 * d * (k * p)) := by
        rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
        have a1 : q * k = k * q := Nat.mul_comm _ _
        have a2 : 2 * p * k = 2 * (k * p) := by ac_rfl
        rw [a1, a2]; ac_rfl
      have eR : Lambda_pass c d ^ (k * p) *
          ((d + 1) ^ (2 * (k * p)) * c ^ (4 * d * (k * p)) * (c - 1) ^ (k * (6 * d * q)))
          = Lambda_pass c d ^ (k * p) * (d + 1) ^ (2 * (k * p)) * c ^ (4 * d * (k * p))
            * (c - 1) ^ (k * (6 * d * q)) := by ac_rfl
      rw [eL, eR] at hlt_m
      exact Nat.lt_of_lt_of_le hlt_m hm
    have hltQ := pow_lt_pow_left_of_lt hQ hlt_b
    rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow] at hltQ
    have hBL_p := Nat.pow_le_pow_left hBL' (6 * d * q)
    rw [Nat.mul_pow (2 ^ BL'), ← Nat.pow_mul 2, ← Nat.pow_mul ((c + 2) ^ k),
        ← Nat.pow_mul ((2 * L_pass c k - 1) * (c - 1) ^ k)] at hBL_p
    have hC0_p := Nat.pow_le_pow_left hC0_ge k
    rw [← Nat.pow_mul, ← Nat.pow_mul] at hC0_p
    have hw_p := hw_lin.pow (9 * q - 2 * p)
    have hLHS_ge : 2 ^ (d * ((9 * q - 2 * p) * Lw + 6 * q * BL') + k * C0)
        * ((c + 2) ^ (6 * d * k * q) * c ^ (4 * d * (k * p))) ^ Q
        ≤ (w_pass c d ^ (9 * q - 2 * p)) ^ Q * ((64 ^ q * (d + 1) ^ (2 * p)) ^ k) ^ Q
          * (((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (6 * d * q)) ^ Q
          * (c ^ (4 * d * (k * p))) ^ Q := by
      have hm1 := Nat.mul_le_mul (Nat.mul_le_mul hw_p hC0_p) hBL_p
      have hm2 := Nat.mul_le_mul_right ((c ^ (4 * d * (k * p))) ^ Q) hm1
      have eExp : d * ((9 * q - 2 * p) * Lw + 6 * q * BL') + k * C0
          = (9 * q - 2 * p) * (d * Lw) + C0 * k + BL' * (6 * d * q) := by grind
      rw [eExp, Nat.pow_add, Nat.pow_add, Nat.mul_pow]
      have eA : ((c + 2) ^ k) ^ (Q * (6 * d * q)) = ((c + 2) ^ (6 * d * k * q)) ^ Q := by
        rw [← Nat.pow_mul, ← Nat.pow_mul]
        have : k * (Q * (6 * d * q)) = 6 * d * k * q * Q := by ac_rfl
        rw [this]
      have eB : (64 ^ q * (d + 1) ^ (2 * p)) ^ (Q * k) = ((64 ^ q * (d + 1) ^ (2 * p)) ^ k) ^ Q := by
        rw [← Nat.pow_mul, Nat.mul_comm Q k]
      have eC : ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (Q * (6 * d * q))
          = (((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (6 * d * q)) ^ Q := by
        rw [← Nat.pow_mul, Nat.mul_comm Q (6 * d * q)]
      rw [eA, eB, eC] at hm2
      have eL2 : 2 ^ ((9 * q - 2 * p) * (d * Lw)) * 2 ^ (C0 * k) * 2 ^ (BL' * (6 * d * q))
          * (((c + 2) ^ (6 * d * k * q)) ^ Q * (c ^ (4 * d * (k * p))) ^ Q)
          = 2 ^ ((9 * q - 2 * p) * (d * Lw)) * 2 ^ (C0 * k)
            * (2 ^ (BL' * (6 * d * q)) * ((c + 2) ^ (6 * d * k * q)) ^ Q)
            * (c ^ (4 * d * (k * p))) ^ Q := by ac_rfl
      rw [eL2]; exact hm2
    have hGdk := Nat.pow_le_pow_left hG (d * k)
    rw [← Nat.pow_mul ((c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q)),
        Nat.mul_pow (2 ^ G), ← Nat.pow_mul 2, ← Nat.pow_mul (c ^ (4 * p))] at hGdk
    have hRHS_le : ((c + 2) ^ (4 * d * (k * p)) * (c - 1) ^ (k * (6 * d * q))) ^ Q
        ≤ 2 ^ (k * d * G) * ((c + 2) ^ (6 * d * k * q) * c ^ (4 * d * (k * p))) ^ Q := by
      have hm := Nat.mul_le_mul_right (((c + 2) ^ (6 * d * k * q)) ^ Q) hGdk
      have eL : ((c + 2) ^ (4 * d * (k * p)) * (c - 1) ^ (k * (6 * d * q))) ^ Q
          = ((c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q)) ^ (Q * (d * k))
            * ((c + 2) ^ (6 * d * k * q)) ^ Q := by
        rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
        have hsum : (4 * p - 6 * q) * (Q * (d * k)) + 6 * d * k * q * Q = 4 * d * (k * p) * Q := by
          have h1 : (4 * p - 6 * q) * (d * k * Q) + (6 * q) * (d * k * Q) = (4 * p) * (d * k * Q) := by
            rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
          have a1 : (4 * p - 6 * q) * (Q * (d * k)) = (4 * p - 6 * q) * (d * k * Q) := by ac_rfl
          have a2 : 6 * d * k * q * Q = (6 * q) * (d * k * Q) := by ac_rfl
          have a3 : 4 * d * (k * p) * Q = (4 * p) * (d * k * Q) := by ac_rfl
          omega
        have e6 : 6 * q * (Q * (d * k)) = k * (6 * d * q) * Q := by ac_rfl
        rw [e6, ← hsum, Nat.pow_add]; ac_rfl
      have eR : 2 ^ (G * (d * k)) * (c ^ (4 * p)) ^ (Q * (d * k)) * ((c + 2) ^ (6 * d * k * q)) ^ Q
          = 2 ^ (k * d * G) * ((c + 2) ^ (6 * d * k * q) * c ^ (4 * d * (k * p))) ^ Q := by
        rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
        have a1 : G * (d * k) = k * d * G := by ac_rfl
        have a2 : 4 * p * (Q * (d * k)) = 4 * d * (k * p) * Q := by ac_rfl
        rw [a1, a2]; ac_rfl
      rw [eL, ← eR]; exact hm
    have h2lt := Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt hLHS_ge (Nat.lt_of_lt_of_le hltQ hRHS_le))
    by_cases h : d * ((9 * q - 2 * p) * Lw + 6 * q * BL') + k * C0 < k * d * G
    · exact h
    · have := Nat.pow_le_pow_right (n := 2) (by decide)
        (show k * d * G ≤ d * ((9 * q - 2 * p) * Lw + 6 * q * BL') + k * C0 by omega)
      omega
  have hk_ge0 : k_lb0 ≤ k := by
    have h0 := hmaster 0 (ceiling_boost_zero Q c k hc)
    rw [Nat.mul_zero, Nat.add_zero] at h0
    have h1 : d * ((9 * q - 2 * p) * Lw) < d * (k * G) := by
      have : k * d * G = d * (k * G) := by ac_rfl
      omega
    have h2 : (9 * q - 2 * p) * Lw < k * G := Nat.lt_of_mul_lt_mul_left h1
    by_cases h : k_lb0 ≤ k
    · exact h
    · have := Nat.mul_le_mul_right G (show k ≤ k_lb0 by omega)
      omega
  have hBL_eff := hBL hk_ge0
  let F := (9 * q - 2 * p) * Lw + 6 * q * BL
  have hF_ineq : d * F + k * C0 < k * d * G := hmaster BL hBL_eff
  have hk_ge : k_lb ≤ k := by
    have h1 : d * F < d * (k * G) := by
      have : k * d * G = d * (k * G) := by ac_rfl
      omega
    have h2 : F < k * G := Nat.lt_of_mul_lt_mul_left h1
    by_cases h : k_lb ≤ k
    · exact h
    · have := Nat.mul_le_mul_right G (show k ≤ k_lb by omega)
      omega
  have hSc : 2 ^ S * (c - 1) ^ Q ≤ (c + 2) ^ Q := by
    have hrat : (c_hi + 2) * (c - 1) ≤ (c + 2) * (c_hi - 1) := by
      apply nat_le_of_int
      have h1i : ((c - 1 : Nat) : Int) = (c : Int) - 1 := by omega
      have h2i : ((c_hi - 1 : Nat) : Int) = (c_hi : Int) - 1 := by omega
      simp only [Int.natCast_mul, Int.natCast_add]; rw [h1i, h2i]
      change ((c_hi : Int) + 2) * ((c : Int) - 1) ≤ ((c : Int) + 2) * ((c_hi : Int) - 1)
      have hid : ((c : Int) + 2) * ((c_hi : Int) - 1) - ((c_hi : Int) + 2) * ((c : Int) - 1)
          = 3 * ((c_hi : Int) - c) := by grind
      omega
    have hratQ := Nat.pow_le_pow_left hrat Q
    rw [Nat.mul_pow, Nat.mul_pow] at hratQ
    have hm := Nat.mul_le_mul_right ((c - 1) ^ Q) hS
    have htr := Nat.le_trans hm hratQ
    have eL : 2 ^ S * (c_hi - 1) ^ Q * (c - 1) ^ Q
        = (2 ^ S * (c - 1) ^ Q) * (c_hi - 1) ^ Q := by ac_rfl
    rw [eL] at htr
    exact Nat.le_of_mul_le_mul_right htr (pow_pos_of_pos (a := c_hi - 1) (by omega) _)
  have h2L_ge : Log2Ge (2 * L_pass c k - 1) (BL + k * S) Q := by
    unfold Log2Ge
    have hSc_k := Nat.pow_le_pow_left hSc k
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hSc_k
    have hm := Nat.mul_le_mul_left (2 ^ BL) hSc_k
    have eL : 2 ^ BL * (2 ^ (S * k) * (c - 1) ^ (Q * k))
        = 2 ^ (BL + k * S) * ((c - 1) ^ k) ^ Q := by
      rw [Nat.pow_add, ← Nat.pow_mul, Nat.mul_comm S k, Nat.mul_comm Q k]; ac_rfl
    have eM : 2 ^ BL * (c + 2) ^ (Q * k) = 2 ^ BL * ((c + 2) ^ k) ^ Q := by
      rw [← Nat.pow_mul, Nat.mul_comm Q k]
    rw [eL, eM] at hm
    have htr := Nat.le_trans hm hBL_eff
    rw [Nat.mul_pow] at htr
    exact Nat.le_of_mul_le_mul_right htr (pow_pos_of_pos (pow_pos_of_pos (a := c - 1) (by omega) k) _)
  have hvk_ge : Log2Ge (v_k_pass c d k)
      ((9 * q * Lw + 6 * q * BL) * d + 6 * q * S * d * k) (p * Q) := by
    unfold Log2Ge
    have hEk_ge : Log2Ge (E_k_pass c d k) (9 * (d * Lw) + 6 * d * (BL + k * S)) Q := by
      unfold E_k_pass
      have h1 : Log2Ge (64 ^ k) 0 Q := by
        unfold Log2Ge; rw [Nat.pow_zero]; exact pow_pos_of_pos (pow_pos_of_pos (by decide : 0 < 64) k) Q
      have hm := (h1.mul (hw_lin.pow 9)).mul (h2L_ge.pow (6 * d))
      rwa [Nat.zero_add] at hm
    have hEk_q := hEk_ge.pow q
    unfold Log2Ge at hEk_q
    have hltQ := Nat.le_of_lt (pow_lt_pow_left_of_lt hQ hlt)
    have htr := Nat.le_trans hEk_q hltQ
    rw [← Nat.pow_mul] at htr
    have eExp : q * (9 * (d * Lw) + 6 * d * (BL + k * S))
        = (9 * q * Lw + 6 * q * BL) * d + 6 * q * S * d * k := by grind
    rwa [eExp] at htr
  constructor
  · let A := 9 * q * Lw + 6 * q * BL
    let B := 6 * q * S * F
    let y := d * G - C0
    have hy_pos : 1 ≤ y := by dsimp only [y]; omega
    have hdG : d * G = y + C0 := by dsimp only [y]; omega
    have hky : d * F < k * y := by
      have : k * y + k * C0 = k * d * G := by rw [← Nat.mul_add, ← hdG]; ac_rfl
      omega
    have hnum_ge : (A * G + 2 * B) * C0 + R ≤ G ^ 2 * (A * d + 6 * q * S * d * k) := by
      have h1 : (A * G + B) * y ^ 2 + (A * G + 2 * B) * C0 * y + B * C0 ^ 2
          ≤ G ^ 2 * (A * d + 6 * q * S * d * k) * y := by
        have hstep1 : B * d ^ 2 ≤ (6 * q * S * d * k) * y := by
          have hm := Nat.mul_le_mul_left (6 * q * S * d) (Nat.le_of_lt hky)
          have eL : 6 * q * S * d * (d * F) = B * d ^ 2 := by dsimp only [B]; rw [Nat.pow_two d]; ac_rfl
          have eR : 6 * q * S * d * (k * y) = 6 * q * S * d * k * y := by ac_rfl
          rwa [eL, eR] at hm
        have hmulG := Nat.add_le_add_left (Nat.mul_le_mul_left (G ^ 2) hstep1) (G ^ 2 * (A * d * y))
        have hL_eq : G ^ 2 * (A * d + 6 * q * S * d * k) * y
            = G ^ 2 * (A * d * y) + G ^ 2 * (6 * q * S * d * k * y) := by grind
        have hR_eq : G ^ 2 * (A * d * y) + G ^ 2 * (B * d ^ 2)
            = (A * G + B) * y ^ 2 + (A * G + 2 * B) * C0 * y + B * C0 ^ 2 := by
          have hG2d2 : G ^ 2 * d ^ 2 = (y + C0) ^ 2 := by
            rw [← Nat.mul_pow, Nat.mul_comm G d, hdG]
          have hG2d : G ^ 2 * (A * d * y) = A * G * (y + C0) * y := by
            have : G ^ 2 * (A * d * y) = A * G * (d * G) * y := by rw [Nat.pow_two G]; ac_rfl
            rw [this, hdG]
          have hG2B : G ^ 2 * (B * d ^ 2) = B * (y + C0) ^ 2 := by
            have : G ^ 2 * (B * d ^ 2) = B * (G ^ 2 * d ^ 2) := by ac_rfl
            rw [this, hG2d2]
          rw [hG2d, hG2B]
          grind
        omega
      have hRy : R * y ≤ (A * G + B) * y ^ 2 + B * C0 ^ 2 := by
        apply le_of_pow_le_pow_left (n := 2) (by decide)
        have hq_am := nat_quad_amgm ((A * G + B) * y ^ 2) (B * C0 ^ 2)
        have hRmul := Nat.mul_le_mul_right (y ^ 2) hR
        rw [Nat.mul_pow]
        have e1 : 4 * (A * G + B) * B * C0 ^ 2 * y ^ 2
            = 4 * ((A * G + B) * y ^ 2) * (B * C0 ^ 2) := by ac_rfl
        have e2 : (B * C0 ^ 2 + (A * G + B) * y ^ 2) ^ 2
            = ((A * G + B) * y ^ 2 + B * C0 ^ 2) ^ 2 := by rw [Nat.add_comm]
        exact Nat.le_trans hRmul (e1 ▸ (e2 ▸ hq_am))
      have hmul_y : ((A * G + 2 * B) * C0 + R) * y ≤ G ^ 2 * (A * d + 6 * q * S * d * k) * y := by
        rw [Nat.add_mul]; omega
      exact Nat.le_of_mul_le_mul_right hmul_y hy_pos
    have hsc := hvk_ge.rescale (G ^ 2)
    have e1 : G ^ 2 * (p * Q) = p * Q * G ^ 2 := Nat.mul_comm _ _
    rw [e1] at hsc
    exact hsc.mono_exp hnum_ge
  · intro h hPB
    rcases hPB with ⟨_hV2, hh, hlt_pb⟩
    have hw_le_S : w_pass c d ≤ 3 * (2 * d + 1) * w_pass c d - 2 := by
      have h3 : 9 ≤ 3 * (2 * d + 1) := by omega
      have hm : 9 * w_pass c d ≤ 3 * (2 * d + 1) * w_pass c d := Nat.mul_le_mul_right _ h3
      omega
    have hpb1 : w_pass c d ^ ((2 * k - 1) * q) * (E_k_pass c d k) ^ (h * q) < (v_k_pass c d k) ^ (h * p) := by
      have hpow_le : w_pass c d ^ (2 * k - 1) ≤ h * (3 * (2 * d + 1) * w_pass c d - 2) ^ (2 * k - 1) + 1 := by
        have h1 := Nat.pow_le_pow_left hw_le_S (2 * k - 1)
        have h2 := Nat.mul_le_mul_right ((3 * (2 * d + 1) * w_pass c d - 2) ^ (2 * k - 1)) hh
        rw [Nat.one_mul] at h2
        omega
      have hq_le := Nat.pow_le_pow_left hpow_le q
      rw [← Nat.pow_mul] at hq_le
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hq_le) hlt_pb
    have hpb_exp : q * (2 * k - 1) * d * Lw + h * (d * F + k * C0) < h * k * d * G := by
      unfold E_k_pass v_k_pass at hpb1
      rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow] at hpb1
      rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hpb1
      have hwsplit : w_pass c d ^ (9 * (h * q))
          = w_pass c d ^ (h * (9 * q - 2 * p)) * w_pass c d ^ (2 * (h * p)) := by
        rw [← Nat.pow_add]
        have : h * (9 * q - 2 * p) + 2 * (h * p) = 9 * (h * q) := by
          have h1 : h * (9 * q - 2 * p) + h * (2 * p) = h * (9 * q) := by
            rw [← Nat.mul_add, Nat.sub_add_cancel hτ]
          have a1 : h * (2 * p) = 2 * (h * p) := by ac_rfl
          have a2 : h * (9 * q) = 9 * (h * q) := by ac_rfl
          omega
        rw [this]
      rw [hwsplit] at hpb1
      have hpb_c : w_pass c d ^ ((2 * k - 1) * q) * w_pass c d ^ (h * (9 * q - 2 * p))
          * 64 ^ (k * (h * q)) * (2 * L_pass c k - 1) ^ (6 * d * (h * q))
          < Lambda_pass c d ^ (k * (h * p)) := by
        have eL : w_pass c d ^ ((2 * k - 1) * q)
            * (64 ^ (k * (h * q)) * (w_pass c d ^ (h * (9 * q - 2 * p)) * w_pass c d ^ (2 * (h * p)))
               * (2 * L_pass c k - 1) ^ (6 * d * (h * q)))
            = (w_pass c d ^ ((2 * k - 1) * q) * w_pass c d ^ (h * (9 * q - 2 * p))
               * 64 ^ (k * (h * q)) * (2 * L_pass c k - 1) ^ (6 * d * (h * q)))
              * w_pass c d ^ (2 * (h * p)) := by ac_rfl
        have eR : w_pass c d ^ (2 * (h * p)) * Lambda_pass c d ^ (k * (h * p))
            = Lambda_pass c d ^ (k * (h * p)) * w_pass c d ^ (2 * (h * p)) := Nat.mul_comm _ _
        rw [eL, eR] at hpb1
        exact Nat.lt_of_mul_lt_mul_right hpb1
      have hpos_m : 0 < (d + 1) ^ (2 * (k * (h * p))) * c ^ (4 * d * (k * (h * p)))
          * (c - 1) ^ (k * (6 * d * (h * q))) :=
        Nat.mul_pos (Nat.mul_pos (pow_pos_of_pos (by omega) _) (pow_pos_of_pos (by omega) _))
          (pow_pos_of_pos (by omega) _)
      have hlt_m := Nat.mul_lt_mul_of_pos_right hpb_c hpos_m
      have hLam_p := Nat.pow_le_pow_left (Lambda_pass_mul_le c d) (k * (h * p))
      rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hLam_p
      have hlt_b : w_pass c d ^ ((2 * k - 1) * q + h * (9 * q - 2 * p))
          * (64 ^ q * (d + 1) ^ (2 * p)) ^ (h * k)
          * ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (6 * d * (h * q))
          * c ^ (4 * d * (k * (h * p)))
          < (c + 2) ^ (4 * d * (k * (h * p))) * (c - 1) ^ (k * (6 * d * (h * q))) := by
        have hm := Nat.mul_le_mul_right ((c - 1) ^ (k * (6 * d * (h * q)))) hLam_p
        have eL : w_pass c d ^ ((2 * k - 1) * q) * w_pass c d ^ (h * (9 * q - 2 * p))
            * 64 ^ (k * (h * q)) * (2 * L_pass c k - 1) ^ (6 * d * (h * q))
            * ((d + 1) ^ (2 * (k * (h * p))) * c ^ (4 * d * (k * (h * p)))
               * (c - 1) ^ (k * (6 * d * (h * q))))
            = w_pass c d ^ ((2 * k - 1) * q + h * (9 * q - 2 * p))
              * (64 ^ q * (d + 1) ^ (2 * p)) ^ (h * k)
              * ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (6 * d * (h * q))
              * c ^ (4 * d * (k * (h * p))) := by
          rw [Nat.pow_add, Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
          have a1 : q * (h * k) = k * (h * q) := by ac_rfl
          have a2 : 2 * p * (h * k) = 2 * (k * (h * p)) := by ac_rfl
          rw [a1, a2]; ac_rfl
        have eR : Lambda_pass c d ^ (k * (h * p)) *
            ((d + 1) ^ (2 * (k * (h * p))) * c ^ (4 * d * (k * (h * p)))
             * (c - 1) ^ (k * (6 * d * (h * q))))
            = Lambda_pass c d ^ (k * (h * p)) * (d + 1) ^ (2 * (k * (h * p)))
              * c ^ (4 * d * (k * (h * p))) * (c - 1) ^ (k * (6 * d * (h * q))) := by ac_rfl
        rw [eL, eR] at hlt_m
        exact Nat.lt_of_lt_of_le hlt_m hm
      have hltQ := pow_lt_pow_left_of_lt hQ hlt_b
      rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow] at hltQ
      have hBL_p := Nat.pow_le_pow_left hBL_eff (6 * d * (h * q))
      rw [Nat.mul_pow (2 ^ BL), ← Nat.pow_mul 2, ← Nat.pow_mul ((c + 2) ^ k),
          ← Nat.pow_mul ((2 * L_pass c k - 1) * (c - 1) ^ k)] at hBL_p
      have hC0_p := Nat.pow_le_pow_left hC0_ge (h * k)
      rw [← Nat.pow_mul, ← Nat.pow_mul] at hC0_p
      have hw_p := hw_lin.pow ((2 * k - 1) * q + h * (9 * q - 2 * p))
      have hLHS_ge : 2 ^ (q * (2 * k - 1) * d * Lw + h * (d * F + k * C0))
          * ((c + 2) ^ (6 * d * k * (h * q)) * c ^ (4 * d * (k * (h * p)))) ^ Q
          ≤ (w_pass c d ^ ((2 * k - 1) * q + h * (9 * q - 2 * p))) ^ Q
            * ((64 ^ q * (d + 1) ^ (2 * p)) ^ (h * k)) ^ Q
            * (((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (6 * d * (h * q))) ^ Q
            * (c ^ (4 * d * (k * (h * p)))) ^ Q := by
        have hm1 := Nat.mul_le_mul (Nat.mul_le_mul hw_p hC0_p) hBL_p
        have hm2 := Nat.mul_le_mul_right ((c ^ (4 * d * (k * (h * p)))) ^ Q) hm1
        have eExp : q * (2 * k - 1) * d * Lw + h * (d * F + k * C0)
            = ((2 * k - 1) * q + h * (9 * q - 2 * p)) * (d * Lw) + C0 * (h * k)
              + BL * (6 * d * (h * q)) := by dsimp only [F]; grind
        rw [eExp, Nat.pow_add, Nat.pow_add, Nat.mul_pow]
        have eA : ((c + 2) ^ k) ^ (Q * (6 * d * (h * q))) = ((c + 2) ^ (6 * d * k * (h * q))) ^ Q := by
          rw [← Nat.pow_mul, ← Nat.pow_mul]
          have : k * (Q * (6 * d * (h * q))) = 6 * d * k * (h * q) * Q := by ac_rfl
          rw [this]
        have eB : (64 ^ q * (d + 1) ^ (2 * p)) ^ (Q * (h * k))
            = ((64 ^ q * (d + 1) ^ (2 * p)) ^ (h * k)) ^ Q := by
          rw [← Nat.pow_mul, Nat.mul_comm Q (h * k)]
        have eC : ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (Q * (6 * d * (h * q)))
            = (((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (6 * d * (h * q))) ^ Q := by
          rw [← Nat.pow_mul, Nat.mul_comm Q (6 * d * (h * q))]
        rw [eA, eB, eC] at hm2
        have eL2 : 2 ^ (((2 * k - 1) * q + h * (9 * q - 2 * p)) * (d * Lw)) * 2 ^ (C0 * (h * k))
            * 2 ^ (BL * (6 * d * (h * q)))
            * (((c + 2) ^ (6 * d * k * (h * q))) ^ Q * (c ^ (4 * d * (k * (h * p)))) ^ Q)
            = 2 ^ (((2 * k - 1) * q + h * (9 * q - 2 * p)) * (d * Lw)) * 2 ^ (C0 * (h * k))
              * (2 ^ (BL * (6 * d * (h * q))) * ((c + 2) ^ (6 * d * k * (h * q))) ^ Q)
              * (c ^ (4 * d * (k * (h * p)))) ^ Q := by ac_rfl
        rw [eL2]; exact hm2
      have hGdhk := Nat.pow_le_pow_left hG (h * d * k)
      rw [← Nat.pow_mul ((c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q)),
          Nat.mul_pow (2 ^ G), ← Nat.pow_mul 2, ← Nat.pow_mul (c ^ (4 * p))] at hGdhk
      have hRHS_le : ((c + 2) ^ (4 * d * (k * (h * p))) * (c - 1) ^ (k * (6 * d * (h * q)))) ^ Q
          ≤ 2 ^ (h * k * d * G) * ((c + 2) ^ (6 * d * k * (h * q)) * c ^ (4 * d * (k * (h * p)))) ^ Q := by
        have hm := Nat.mul_le_mul_right (((c + 2) ^ (6 * d * k * (h * q))) ^ Q) hGdhk
        have eL : ((c + 2) ^ (4 * d * (k * (h * p))) * (c - 1) ^ (k * (6 * d * (h * q)))) ^ Q
            = ((c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q)) ^ (Q * (h * d * k))
              * ((c + 2) ^ (6 * d * k * (h * q))) ^ Q := by
          rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
          have hsum : (4 * p - 6 * q) * (Q * (h * d * k)) + 6 * d * k * (h * q) * Q
              = 4 * d * (k * (h * p)) * Q := by
            have h1 : (4 * p - 6 * q) * (h * d * k * Q) + (6 * q) * (h * d * k * Q)
                = (4 * p) * (h * d * k * Q) := by
              rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
            have a1 : (4 * p - 6 * q) * (Q * (h * d * k)) = (4 * p - 6 * q) * (h * d * k * Q) := by ac_rfl
            have a2 : 6 * d * k * (h * q) * Q = (6 * q) * (h * d * k * Q) := by ac_rfl
            have a3 : 4 * d * (k * (h * p)) * Q = (4 * p) * (h * d * k * Q) := by ac_rfl
            omega
          have e6 : 6 * q * (Q * (h * d * k)) = k * (6 * d * (h * q)) * Q := by ac_rfl
          rw [e6, ← hsum, Nat.pow_add]; ac_rfl
        have eR : 2 ^ (G * (h * d * k)) * (c ^ (4 * p)) ^ (Q * (h * d * k))
            * ((c + 2) ^ (6 * d * k * (h * q))) ^ Q
            = 2 ^ (h * k * d * G)
              * ((c + 2) ^ (6 * d * k * (h * q)) * c ^ (4 * d * (k * (h * p)))) ^ Q := by
          rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
          have a1 : G * (h * d * k) = h * k * d * G := by ac_rfl
          have a2 : 4 * p * (Q * (h * d * k)) = 4 * d * (k * (h * p)) * Q := by ac_rfl
          rw [a1, a2]; ac_rfl
        rw [eL, ← eR]; exact hm
      have h2lt := Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt hLHS_ge (Nat.lt_of_lt_of_le hltQ hRHS_le))
      by_cases hcmp : q * (2 * k - 1) * d * Lw + h * (d * F + k * C0) < h * k * d * G
      · exact hcmp
      · have := Nat.pow_le_pow_right (n := 2) (by decide)
          (show h * k * d * G ≤ q * (2 * k - 1) * d * Lw + h * (d * F + k * C0) by omega)
        omega
    let y := d * G - C0
    have hy_pos : 1 ≤ y := by dsimp only [y]; omega
    have hdG : d * G = y + C0 := by dsimp only [y]; omega
    let z := k * y - d * F
    have hky : d * F < k * y := by
      have : k * y + k * C0 = k * d * G := by rw [← Nat.mul_add, ← hdG]; ac_rfl
      omega
    have hz_pos : 1 ≤ z := by dsimp only [z]; omega
    have hkyz : k * y = z + d * F := by dsimp only [z]; omega
    have hhz : q * (2 * k - 1) * d * Lw < h * z := by
      have hid : h * z + h * (d * F + k * C0) = h * k * d * G := by
        have h1 : z + (d * F + k * C0) = k * d * G := by
          have : k * y + k * C0 = k * d * G := by rw [← Nat.mul_add, ← hdG]; ac_rfl
          omega
        rw [← Nat.mul_add, h1]; ac_rfl
      omega
    have h2k : (2 * k_lb - 1) * k ≤ k_lb * (2 * k - 1) := by
      apply nat_le_of_int
      have e1 : ((2 * k_lb - 1 : Nat) : Int) = 2 * (k_lb : Int) - 1 := by omega
      have e2 : ((2 * k - 1 : Nat) : Int) = 2 * (k : Int) - 1 := by omega
      simp only [Int.natCast_mul]; rw [e1, e2]
      have hid : (k_lb : Int) * (2 * (k : Int) - 1) - (2 * (k_lb : Int) - 1) * (k : Int)
          = (k : Int) - (k_lb : Int) := by grind
      omega
    have hstep_k : 4 * q * (2 * k_lb - 1) * Lw * F * d ^ 2 ≤ k_lb * h * k * y ^ 2 := by
      have hq_k := nat_quad_amgm (d * F) z
      rw [← hkyz, Nat.mul_pow] at hq_k
      have h1 := Nat.mul_le_mul_left (q * (2 * k_lb - 1) * d * Lw) hq_k
      have h2 : (q * (2 * k_lb - 1) * d * Lw) * k ≤ k_lb * (q * (2 * k - 1) * d * Lw) := by
        have hm := Nat.mul_le_mul_left (q * d * Lw) h2k
        have eL : q * d * Lw * ((2 * k_lb - 1) * k) = q * (2 * k_lb - 1) * d * Lw * k := by ac_rfl
        have eR : q * d * Lw * (k_lb * (2 * k - 1)) = k_lb * (q * (2 * k - 1) * d * Lw) := by ac_rfl
        rwa [eL, eR] at hm
      have h3 : (q * (2 * k_lb - 1) * d * Lw) * (k ^ 2 * y ^ 2) ≤ (k_lb * h * k * y ^ 2) * z := by
        have hm1 := Nat.mul_le_mul_right (k * y ^ 2) h2
        have hm2 := Nat.mul_le_mul_left (k_lb * k * y ^ 2) (Nat.le_of_lt hhz)
        have eL : q * (2 * k_lb - 1) * d * Lw * k * (k * y ^ 2)
            = q * (2 * k_lb - 1) * d * Lw * (k ^ 2 * y ^ 2) := by rw [Nat.pow_two k]; ac_rfl
        have eM : k_lb * (q * (2 * k - 1) * d * Lw) * (k * y ^ 2)
            = k_lb * k * y ^ 2 * (q * (2 * k - 1) * d * Lw) := by ac_rfl
        have eR : k_lb * k * y ^ 2 * (h * z) = (k_lb * h * k * y ^ 2) * z := by ac_rfl
        rw [← eL, ← eR]
        exact Nat.le_trans hm1 (eM ▸ hm2)
      have hcomb := Nat.le_trans h1 h3
      have eL : (q * (2 * k_lb - 1) * d * Lw) * (4 * (d * F) * z)
          = (4 * q * (2 * k_lb - 1) * Lw * F * d ^ 2) * z := by rw [Nat.pow_two d]; ac_rfl
      rw [eL] at hcomb
      exact Nat.le_of_mul_le_mul_right hcomb hz_pos
    have hdhk : 27 * q * (2 * k_lb - 1) * Lw * F * C0 ≤ k_lb * G ^ 3 * (d * h * k) := by
      have hc_d := nat_cubic_amgm C0 y
      rw [← hdG, Nat.mul_pow] at hc_d
      have h1 := Nat.mul_le_mul_left (q * (2 * k_lb - 1) * Lw * F) hc_d
      have h2 := Nat.mul_le_mul_left (d * G ^ 3) hstep_k
      have eL : q * (2 * k_lb - 1) * Lw * F * (27 * C0 * y ^ 2)
          = (27 * q * (2 * k_lb - 1) * Lw * F * C0) * y ^ 2 := by ac_rfl
      have eM : q * (2 * k_lb - 1) * Lw * F * (4 * (d ^ 3 * G ^ 3))
          = d * G ^ 3 * (4 * q * (2 * k_lb - 1) * Lw * F * d ^ 2) := by rw [Nat.pow_succ d 2]; ac_rfl
      have eR : d * G ^ 3 * (k_lb * h * k * y ^ 2)
          = (k_lb * G ^ 3 * (d * h * k)) * y ^ 2 := by ac_rfl
      have hcomb := Nat.le_trans (eL ▸ h1) (eR ▸ (eM ▸ h2))
      exact Nat.le_of_mul_le_mul_right hcomb (pow_pos_of_pos hy_pos 2)
    have hV_ge : Log2Ge ((v_k_pass c d k) ^ h) (6 * q * S * (d * h * k)) (p * Q) := by
      have h1 := (hvk_ge.mono_exp (Nat.le_add_left (6 * q * S * d * k) _)).pow h
      have e : h * (6 * q * S * d * k) = 6 * q * S * (d * h * k) := by ac_rfl
      rwa [e] at h1
    have hsc := hV_ge.rescale (k_lb * G ^ 3)
    have e1 : k_lb * G ^ 3 * (p * Q) = p * Q * k_lb * G ^ 3 := by ac_rfl
    rw [e1] at hsc
    apply hsc.mono_exp
    have hm := Nat.mul_le_mul_left (6 * q * S) hdhk
    have eR : 6 * q * S * (k_lb * G ^ 3 * (d * h * k)) = k_lb * G ^ 3 * (6 * q * S * (d * h * k)) := by ac_rfl
    rwa [eR] at hm

/-- **MASTER INFINITE-TAIL UNIVERSAL LOWER BOUND ENGINE** (`∀ c ≥ c_lo ≥ 4`, symbolic `Q`!). -/
theorem tail_universal_lb
    {Q p q c_lo c d k d_lb ld_lb pen_Q Lw BL k_lb : Nat}
    (hQ : 0 < Q)
    (hV : ValidPassTriple p q c d k)
    (hτ : 2 * p ≤ 9 * q) (h94 : 9 * q ≤ 4 * p)
    (hc_lo : 4 ≤ c_lo) (hc1 : c_lo ≤ c)
    (hd_lb_pos : 1 ≤ d_lb)
    (hd_lb : (64 ^ q * (d + 1) ^ (2 * p)) ^ (c * Q) < 2 ^ (d * (3 * (4 * p - 9 * q) * Q)) → d_lb ≤ d)
    (hld_lb : Log2Ge (d_lb + 1) ld_lb Q)
    (hlc2 : Log2Ge (c_lo + 2) ((Lw + pen_Q) / 2) Q)
    (hLw_even : Lw + pen_Q = 2 * ((Lw + pen_Q) / 2))
    (h2d : Log2Le (2 * (d_lb + 1)) (d_lb * pen_Q) Q)
    (hpen_step : 2 * Q ≤ pen_Q * (d_lb + 1))
    (hBL : ∀ c' k', c_lo ≤ c' → 3 * (9 * q - 2 * p) * Lw * c' ≤ k' * (3 * (4 * p - 9 * q) * Q) * 3 →
        2 ^ BL * ((c' + 2) ^ k') ^ Q ≤ ((2 * L_pass c' k' - 1) * (c' - 1) ^ k') ^ Q)
    (hklb_pos : 1 ≤ k_lb)
    (hklb_def : k_lb * (3 * (4 * p - 9 * q) * Q) ≤ c_lo * ((9 * q - 2 * p) * Lw + 6 * q * BL)) :
    Log2Ge (v_k_pass c d k)
      ((9 * q * Lw + 6 * q * BL) * d_lb * (3 * (4 * p - 9 * q) * Q) ^ 2
       + 24 * q * Q * 4 * c_lo * (6 * q * Q + 2 * p * ld_lb)
         * ((9 * q - 2 * p) * Lw + 6 * q * BL))
      (p * Q * (3 * (4 * p - 9 * q) * Q) ^ 2) ∧
    (∀ h, ValidPostBini p q c d k h →
      Log2Ge ((v_k_pass c d k) ^ h)
        (24 * q * Q * 27 * q * (2 * k_lb - 1) * Lw
         * ((9 * q - 2 * p) * Lw + 6 * q * BL)
         * (6 * q * Q + 2 * p * ld_lb) * c_lo ^ 2)
        (p * Q * k_lb * (3 * (4 * p - 9 * q) * Q) ^ 3)) := by
  have hV_copy := hV
  rcases hV with ⟨hc, hd, hk, hw, _hLam, hlt⟩
  let G_t := 3 * (4 * p - 9 * q) * Q
  have hG_tail : ((c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q)) ^ (c * Q)
      ≤ 2 ^ G_t * (c ^ (4 * p)) ^ (c * Q) := by
    have hcub := Nat.le_of_lt (cubic_rate_gap c hc).2
    have h1 : (c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q) ≤ (c + 2) ^ (4 * p - 9 * q) * c ^ (9 * q) := by
      have hf : (c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q)
          = (c + 2) ^ (4 * p - 9 * q) * ((c + 2) * (c - 1) ^ 2) ^ (3 * q) := by
        rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.mul_assoc, ← Nat.pow_add]
        have a1 : (4 * p - 9 * q) + 3 * q = 4 * p - 6 * q := by omega
        have a2 : 2 * (3 * q) = 6 * q := by omega
        rw [a1, a2]
      rw [hf]
      have hp := Nat.pow_le_pow_left hcub (3 * q)
      rw [← Nat.pow_mul] at hp
      have a3 : 3 * (3 * q) = 9 * q := by omega
      rw [a3] at hp
      exact Nat.mul_le_mul_left _ hp
    have h2 : ((c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q)) ^ c
        ≤ 2 ^ (3 * (4 * p - 9 * q)) * (c ^ (4 * p)) ^ c := by
      have hp1 := Nat.pow_le_pow_left h1 c
      rw [Nat.mul_pow ((c + 2) ^ (4 * p - 9 * q)), ← Nat.pow_mul (c + 2), ← Nat.pow_mul c] at hp1
      have h8 := Nat.pow_le_pow_left (Nat.le_of_lt (add_two_pow_lt_eight c hc)) (4 * p - 9 * q)
      rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at h8
      have h8_2 : 8 ^ (4 * p - 9 * q) = 2 ^ (3 * (4 * p - 9 * q)) := by
        have : (8 : Nat) = 2 ^ 3 := by decide
        rw [this, ← Nat.pow_mul]
      rw [h8_2] at h8
      have hm := Nat.mul_le_mul_right (c ^ (9 * q * c)) h8
      have eL : (c + 2) ^ ((4 * p - 9 * q) * c) * c ^ (9 * q * c)
          = (c + 2) ^ (c * (4 * p - 9 * q)) * c ^ (9 * q * c) := by rw [Nat.mul_comm c]
      have eR : 2 ^ (3 * (4 * p - 9 * q)) * c ^ (c * (4 * p - 9 * q)) * c ^ (9 * q * c)
          = 2 ^ (3 * (4 * p - 9 * q)) * (c ^ (4 * p)) ^ c := by
        rw [Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_mul]
        have : c * (4 * p - 9 * q) + 9 * q * c = 4 * p * c := by
          have hadd : c * (4 * p - 9 * q) + c * (9 * q) = c * (4 * p) := by
            rw [← Nat.mul_add, Nat.sub_add_cancel h94]
          have a1 : 9 * q * c = c * (9 * q) := Nat.mul_comm _ _
          have a2 : 4 * p * c = c * (4 * p) := Nat.mul_comm _ _
          omega
        rw [this]
      exact Nat.le_trans hp1 (eL ▸ (eR ▸ hm))
    have h3 := Nat.pow_le_pow_left h2 Q
    rw [← Nat.pow_mul ((c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q)),
        Nat.mul_pow (2 ^ (3 * (4 * p - 9 * q))), ← Nat.pow_mul 2, ← Nat.pow_mul (c ^ (4 * p))] at h3
    exact h3
  have hroundQ : (64 ^ q * (d + 1) ^ (2 * p)) ^ (c * Q) < 2 ^ (d * G_t) := by
    have hr := universal_round_necessary hV_copy hτ
    have hsplit : (c + 2) ^ (4 * d * p) = (c + 2) ^ (d * (4 * p - 6 * q)) * (c + 2) ^ (6 * d * q) := by
      rw [← Nat.pow_add]
      have : d * (4 * p - 6 * q) + 6 * d * q = 4 * d * p := by
        have h1 : d * (4 * p - 6 * q) + d * (6 * q) = d * (4 * p) := by
          rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
        have a1 : d * (6 * q) = 6 * d * q := by ac_rfl
        have a2 : d * (4 * p) = 4 * d * p := by ac_rfl
        omega
      rw [this]
    rw [hsplit] at hr
    have hr1 : 64 ^ q * (d + 1) ^ (2 * p) * c ^ (4 * d * p)
        < (c + 2) ^ (d * (4 * p - 6 * q)) * (c - 1) ^ (6 * d * q) := by
      have eR : (c + 2) ^ (d * (4 * p - 6 * q)) * (c + 2) ^ (6 * d * q) * (c - 1) ^ (6 * d * q)
          = ((c + 2) ^ (d * (4 * p - 6 * q)) * (c - 1) ^ (6 * d * q)) * (c + 2) ^ (6 * d * q) := by ac_rfl
      rw [eR] at hr
      exact Nat.lt_of_mul_lt_mul_right hr
    have hrQ := pow_lt_pow_left_of_lt (Nat.mul_pos (show 0 < c by omega) hQ) hr1
    rw [Nat.mul_pow] at hrQ
    have hGd := Nat.pow_le_pow_left hG_tail d
    rw [← Nat.pow_mul ((c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q)),
        Nat.mul_pow (2 ^ G_t), ← Nat.pow_mul 2, ← Nat.pow_mul (c ^ (4 * p)), Nat.mul_comm G_t d] at hGd
    have eL : ((c + 2) ^ (d * (4 * p - 6 * q)) * (c - 1) ^ (6 * d * q)) ^ (c * Q)
        = ((c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q)) ^ (c * Q * d) := by
      rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
      have a1 : d * (4 * p - 6 * q) * (c * Q) = (4 * p - 6 * q) * (c * Q * d) := by ac_rfl
      have a2 : 6 * d * q * (c * Q) = 6 * q * (c * Q * d) := by ac_rfl
      rw [a1, a2]
    have eR1 : (c ^ (4 * d * p)) ^ (c * Q) = (c ^ (4 * p)) ^ (c * Q * d) := by
      rw [← Nat.pow_mul, ← Nat.pow_mul]
      have : 4 * d * p * (c * Q) = 4 * p * (c * Q * d) := by ac_rfl
      rw [this]
    rw [eL, eR1] at hrQ
    exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_lt_of_le hrQ hGd)
  have hd_ge : d_lb ≤ d := hd_lb hroundQ
  let C0 := 6 * q * Q + 2 * p * ld_lb
  have hC0_ge : 2 ^ C0 ≤ (64 ^ q * (d + 1) ^ (2 * p)) ^ Q := by
    have h64 : Log2Ge (64 ^ q) (6 * q * Q) Q := by
      have h6 : Log2Ge 64 (6 * Q) Q := by
        have : (64 : Nat) = 2 ^ 6 := by decide
        rw [this]; exact Log2Ge.two_pow 6 Q
      have hp := h6.pow q
      have e : q * (6 * Q) = 6 * q * Q := by ac_rfl
      rwa [e] at hp
    exact h64.mul ((hld_lb.mono_left (show d_lb + 1 ≤ d + 1 by omega)).pow (2 * p))
  have hcC0_lt : c * C0 < d * G_t := by
    have h1 := Nat.pow_le_pow_left hC0_ge c
    rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm C0 c, Nat.mul_comm Q c] at h1
    have h2lt := Nat.lt_of_le_of_lt h1 hroundQ
    by_cases h : c * C0 < d * G_t
    · exact h
    · have := Nat.pow_le_pow_right (n := 2) (by decide) (show d * G_t ≤ c * C0 by omega)
      omega
  have hw_lin : Log2Ge (w_pass c d) (d * Lw) Q := by
    have hpen_le : pen_Q ≤ 2 * ((Lw + pen_Q) / 2) := by omega
    have h := w_pass_log2Ge_linear (by omega) hc1 hd_lb_pos hd_ge hlc2 h2d hpen_step hpen_le
    have hLw_eq : 2 * ((Lw + pen_Q) / 2) - pen_Q = Lw := by omega
    rwa [hLw_eq] at h
  have hmaster : ∀ BL',
      2 ^ BL' * ((c + 2) ^ k) ^ Q ≤ ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ Q →
      c * (d * ((9 * q - 2 * p) * Lw + 6 * q * BL') + k * C0) < k * d * G_t := by
    intro BL' hBL'
    have hlt_raw : w_pass c d ^ (9 * q - 2 * p) * 64 ^ (k * q) * (2 * L_pass c k - 1) ^ (6 * d * q)
        < Lambda_pass c d ^ (k * p) := by
      unfold E_k_pass v_k_pass at hlt
      rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow] at hlt
      rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hlt
      have hwsplit : w_pass c d ^ (9 * q) = w_pass c d ^ (9 * q - 2 * p) * w_pass c d ^ (2 * p) := by
        rw [← Nat.pow_add, Nat.sub_add_cancel hτ]
      rw [hwsplit] at hlt
      have eL : 64 ^ (k * q) * (w_pass c d ^ (9 * q - 2 * p) * w_pass c d ^ (2 * p))
          * (2 * L_pass c k - 1) ^ (6 * d * q)
          = (w_pass c d ^ (9 * q - 2 * p) * 64 ^ (k * q) * (2 * L_pass c k - 1) ^ (6 * d * q))
            * w_pass c d ^ (2 * p) := by ac_rfl
      have eR : w_pass c d ^ (2 * p) * Lambda_pass c d ^ (k * p)
          = Lambda_pass c d ^ (k * p) * w_pass c d ^ (2 * p) := Nat.mul_comm _ _
      rw [eL, eR] at hlt
      exact Nat.lt_of_mul_lt_mul_right hlt
    have hpos_m : 0 < (d + 1) ^ (2 * (k * p)) * c ^ (4 * d * (k * p)) * (c - 1) ^ (k * (6 * d * q)) :=
      Nat.mul_pos (Nat.mul_pos (pow_pos_of_pos (by omega) _) (pow_pos_of_pos (by omega) _))
        (pow_pos_of_pos (by omega) _)
    have hlt_m := Nat.mul_lt_mul_of_pos_right hlt_raw hpos_m
    have hLam_p := Nat.pow_le_pow_left (Lambda_pass_mul_le c d) (k * p)
    rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hLam_p
    have hlt_b : w_pass c d ^ (9 * q - 2 * p) * (64 ^ q * (d + 1) ^ (2 * p)) ^ k
        * ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (6 * d * q) * c ^ (4 * d * (k * p))
        < (c + 2) ^ (4 * d * (k * p)) * (c - 1) ^ (k * (6 * d * q)) := by
      have hm := Nat.mul_le_mul_right ((c - 1) ^ (k * (6 * d * q))) hLam_p
      have eL : w_pass c d ^ (9 * q - 2 * p) * 64 ^ (k * q) * (2 * L_pass c k - 1) ^ (6 * d * q)
          * ((d + 1) ^ (2 * (k * p)) * c ^ (4 * d * (k * p)) * (c - 1) ^ (k * (6 * d * q)))
          = w_pass c d ^ (9 * q - 2 * p) * (64 ^ q * (d + 1) ^ (2 * p)) ^ k
            * ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (6 * d * q) * c ^ (4 * d * (k * p)) := by
        rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
        have a1 : q * k = k * q := Nat.mul_comm _ _
        have a2 : 2 * p * k = 2 * (k * p) := by ac_rfl
        rw [a1, a2]; ac_rfl
      have eR : Lambda_pass c d ^ (k * p) *
          ((d + 1) ^ (2 * (k * p)) * c ^ (4 * d * (k * p)) * (c - 1) ^ (k * (6 * d * q)))
          = Lambda_pass c d ^ (k * p) * (d + 1) ^ (2 * (k * p)) * c ^ (4 * d * (k * p))
            * (c - 1) ^ (k * (6 * d * q)) := by ac_rfl
      rw [eL, eR] at hlt_m
      exact Nat.lt_of_lt_of_le hlt_m hm
    have hltQ := pow_lt_pow_left_of_lt (Nat.mul_pos (show 0 < c by omega) hQ) hlt_b
    rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow] at hltQ
    have hBL_p := Nat.pow_le_pow_left hBL' (6 * d * q * c)
    rw [Nat.mul_pow (2 ^ BL'), ← Nat.pow_mul 2, ← Nat.pow_mul ((c + 2) ^ k),
        ← Nat.pow_mul ((2 * L_pass c k - 1) * (c - 1) ^ k)] at hBL_p
    have hC0_p := Nat.pow_le_pow_left hC0_ge (k * c)
    rw [← Nat.pow_mul, ← Nat.pow_mul] at hC0_p
    have hw_p := hw_lin.pow ((9 * q - 2 * p) * c)
    have hLHS_ge : 2 ^ (c * (d * ((9 * q - 2 * p) * Lw + 6 * q * BL') + k * C0))
        * ((c + 2) ^ (6 * d * k * q) * c ^ (4 * d * (k * p))) ^ (c * Q)
        ≤ (w_pass c d ^ (9 * q - 2 * p)) ^ (c * Q)
          * ((64 ^ q * (d + 1) ^ (2 * p)) ^ k) ^ (c * Q)
          * (((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (6 * d * q)) ^ (c * Q)
          * (c ^ (4 * d * (k * p))) ^ (c * Q) := by
      have hm1 := Nat.mul_le_mul (Nat.mul_le_mul hw_p hC0_p) hBL_p
      have hm2 := Nat.mul_le_mul_right ((c ^ (4 * d * (k * p))) ^ (c * Q)) hm1
      have eExp : c * (d * ((9 * q - 2 * p) * Lw + 6 * q * BL') + k * C0)
          = (9 * q - 2 * p) * c * (d * Lw) + C0 * (k * c) + BL' * (6 * d * q * c) := by grind
      rw [eExp, Nat.pow_add, Nat.pow_add, Nat.mul_pow]
      have eW : (w_pass c d ^ ((9 * q - 2 * p) * c)) ^ Q
          = (w_pass c d ^ (9 * q - 2 * p)) ^ (c * Q) := by
        rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_assoc]
      have eA : ((c + 2) ^ k) ^ (Q * (6 * d * q * c)) = ((c + 2) ^ (6 * d * k * q)) ^ (c * Q) := by
        rw [← Nat.pow_mul, ← Nat.pow_mul]
        have : k * (Q * (6 * d * q * c)) = 6 * d * k * q * (c * Q) := by ac_rfl
        rw [this]
      have eB : (64 ^ q * (d + 1) ^ (2 * p)) ^ (Q * (k * c))
          = ((64 ^ q * (d + 1) ^ (2 * p)) ^ k) ^ (c * Q) := by
        rw [← Nat.pow_mul]
        have : Q * (k * c) = k * (c * Q) := by ac_rfl
        rw [this]
      have eC : ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (Q * (6 * d * q * c))
          = (((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (6 * d * q)) ^ (c * Q) := by
        rw [← Nat.pow_mul]
        have : Q * (6 * d * q * c) = 6 * d * q * (c * Q) := by ac_rfl
        rw [this]
      rw [eW, eA, eB, eC] at hm2
      have eL2 : 2 ^ ((9 * q - 2 * p) * c * (d * Lw)) * 2 ^ (C0 * (k * c)) * 2 ^ (BL' * (6 * d * q * c))
          * (((c + 2) ^ (6 * d * k * q)) ^ (c * Q) * (c ^ (4 * d * (k * p))) ^ (c * Q))
          = 2 ^ ((9 * q - 2 * p) * c * (d * Lw)) * 2 ^ (C0 * (k * c))
            * (2 ^ (BL' * (6 * d * q * c)) * ((c + 2) ^ (6 * d * k * q)) ^ (c * Q))
            * (c ^ (4 * d * (k * p))) ^ (c * Q) := by ac_rfl
      rw [eL2]; exact hm2
    have hGdk := Nat.pow_le_pow_left hG_tail (d * k)
    rw [← Nat.pow_mul ((c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q)),
        Nat.mul_pow (2 ^ G_t), ← Nat.pow_mul 2, ← Nat.pow_mul (c ^ (4 * p))] at hGdk
    have hRHS_le : ((c + 2) ^ (4 * d * (k * p)) * (c - 1) ^ (k * (6 * d * q))) ^ (c * Q)
        ≤ 2 ^ (k * d * G_t) * ((c + 2) ^ (6 * d * k * q) * c ^ (4 * d * (k * p))) ^ (c * Q) := by
      have hm := Nat.mul_le_mul_right (((c + 2) ^ (6 * d * k * q)) ^ (c * Q)) hGdk
      have eL : ((c + 2) ^ (4 * d * (k * p)) * (c - 1) ^ (k * (6 * d * q))) ^ (c * Q)
          = ((c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q)) ^ (c * Q * (d * k))
            * ((c + 2) ^ (6 * d * k * q)) ^ (c * Q) := by
        rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
        have hsum : (4 * p - 6 * q) * (c * Q * (d * k)) + 6 * d * k * q * (c * Q)
            = 4 * d * (k * p) * (c * Q) := by
          have h1 : (4 * p - 6 * q) * (c * Q * d * k) + (6 * q) * (c * Q * d * k)
              = (4 * p) * (c * Q * d * k) := by
            rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
          have a1 : (4 * p - 6 * q) * (c * Q * (d * k)) = (4 * p - 6 * q) * (c * Q * d * k) := by ac_rfl
          have a2 : 6 * d * k * q * (c * Q) = (6 * q) * (c * Q * d * k) := by ac_rfl
          have a3 : 4 * d * (k * p) * (c * Q) = (4 * p) * (c * Q * d * k) := by ac_rfl
          omega
        have e6 : 6 * q * (c * Q * (d * k)) = k * (6 * d * q) * (c * Q) := by ac_rfl
        rw [e6, ← hsum, Nat.pow_add]; ac_rfl
      have eR : 2 ^ (G_t * (d * k)) * (c ^ (4 * p)) ^ (c * Q * (d * k))
          * ((c + 2) ^ (6 * d * k * q)) ^ (c * Q)
          = 2 ^ (k * d * G_t)
            * ((c + 2) ^ (6 * d * k * q) * c ^ (4 * d * (k * p))) ^ (c * Q) := by
        rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
        have a1 : G_t * (d * k) = k * d * G_t := by ac_rfl
        have a2 : 4 * p * (c * Q * (d * k)) = 4 * d * (k * p) * (c * Q) := by ac_rfl
        rw [a1, a2]; ac_rfl
      rw [eL, ← eR]; exact hm
    have h2lt := Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt hLHS_ge (Nat.lt_of_lt_of_le hltQ hRHS_le))
    by_cases h : c * (d * ((9 * q - 2 * p) * Lw + 6 * q * BL') + k * C0) < k * d * G_t
    · exact h
    · have := Nat.pow_le_pow_right (n := 2) (by decide)
        (show k * d * G_t ≤ c * (d * ((9 * q - 2 * p) * Lw + 6 * q * BL') + k * C0) by omega)
      omega
  have hBL_eff : 2 ^ BL * ((c + 2) ^ k) ^ Q ≤ ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ Q := by
    have h0 := hmaster 0 (ceiling_boost_zero Q c k hc)
    rw [Nat.mul_zero, Nat.add_zero] at h0
    have h1 : d * (c * ((9 * q - 2 * p) * Lw)) < d * (k * G_t) := by
      have e1 : c * (d * ((9 * q - 2 * p) * Lw) + k * C0)
          = d * (c * ((9 * q - 2 * p) * Lw)) + c * (k * C0) := by rw [Nat.mul_add]; ac_rfl
      have e2 : k * d * G_t = d * (k * G_t) := by ac_rfl
      omega
    have h2 := Nat.lt_of_mul_lt_mul_left h1
    apply hBL c k hc1
    have hm := Nat.mul_le_mul_left 3 (Nat.le_of_lt h2)
    have eL : 3 * (c * ((9 * q - 2 * p) * Lw)) = 3 * (9 * q - 2 * p) * Lw * c := by ac_rfl
    have eR : 3 * (k * G_t) = k * G_t * 3 := by ac_rfl
    rwa [eL, eR] at hm
  let F := (9 * q - 2 * p) * Lw + 6 * q * BL
  have hF_ineq : c * (d * F + k * C0) < k * d * G_t := hmaster BL hBL_eff
  have hk_ge : k_lb ≤ k := by
    have h1 : d * (c * F) < d * (k * G_t) := by
      have e1 : c * (d * F + k * C0) = d * (c * F) + c * (k * C0) := by rw [Nat.mul_add]; ac_rfl
      have e2 : k * d * G_t = d * (k * G_t) := by ac_rfl
      omega
    have h2 := Nat.lt_of_mul_lt_mul_left h1
    have h3 : c_lo * F ≤ c * F := Nat.mul_le_mul_right F hc1
    have hklb_def' : k_lb * G_t ≤ c_lo * F := hklb_def
    by_cases h : k_lb ≤ k
    · exact h
    · have := Nat.mul_le_mul_right G_t (show k ≤ k_lb by omega)
      omega
  have h2L_c : Log2Ge (2 * L_pass c k - 1) (c * BL + 4 * k * Q) (c * Q) := by
    unfold Log2Ge
    have h16 : 2 ^ 4 * (c - 1) ^ c ≤ (c + 2) ^ c := sixteen_mul_sub_one_pow_le c (by omega)
    have h16_p := Nat.pow_le_pow_left h16 (k * Q)
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at h16_p
    have hBL_c := Nat.pow_le_pow_left hBL_eff c
    rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul,
        ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hBL_c
    have hm := Nat.mul_le_mul_left (2 ^ (BL * c)) h16_p
    have eL : 2 ^ (BL * c) * (2 ^ (4 * (k * Q)) * (c - 1) ^ (c * (k * Q)))
        = 2 ^ (c * BL + 4 * k * Q) * (c - 1) ^ (k * Q * c) := by
      rw [Nat.pow_add]
      have a1 : BL * c = c * BL := Nat.mul_comm _ _
      have a2 : 4 * (k * Q) = 4 * k * Q := by ac_rfl
      have a3 : c * (k * Q) = k * Q * c := by ac_rfl
      rw [a1, a2, a3]; ac_rfl
    have eM : 2 ^ (BL * c) * (c + 2) ^ (c * (k * Q)) = 2 ^ (BL * c) * (c + 2) ^ (k * Q * c) := by
      have : c * (k * Q) = k * Q * c := by ac_rfl
      rw [this]
    have eR : (2 * L_pass c k - 1) ^ (Q * c) * (c - 1) ^ (k * (Q * c))
        = (2 * L_pass c k - 1) ^ (c * Q) * (c - 1) ^ (k * Q * c) := by
      have a1 : Q * c = c * Q := Nat.mul_comm _ _
      have a2 : k * (Q * c) = k * Q * c := by ac_rfl
      rw [a2, a1]
    have eL_c : (c + 2) ^ (k * (Q * c)) = (c + 2) ^ (k * Q * c) := by rw [Nat.mul_assoc k Q c]
    rw [eL, eM] at hm
    rw [eL_c, eR] at hBL_c
    exact Nat.le_of_mul_le_mul_right (Nat.le_trans hm hBL_c) (pow_pos_of_pos (a := c - 1) (by omega) _)
  have hvk_ge : Log2Ge (v_k_pass c d k)
      ((9 * q * Lw + 6 * q * BL) * d * c + 24 * q * Q * d * k) (p * c * Q) := by
    unfold Log2Ge
    have hw_c : Log2Ge (w_pass c d) (c * (d * Lw)) (c * Q) := hw_lin.rescale c
    have hEk_ge : Log2Ge (E_k_pass c d k) (9 * (c * (d * Lw)) + 6 * d * (c * BL + 4 * k * Q)) (c * Q) := by
      unfold E_k_pass
      have h1 : Log2Ge (64 ^ k) 0 (c * Q) := by
        unfold Log2Ge; rw [Nat.pow_zero]; exact pow_pos_of_pos (pow_pos_of_pos (by decide : 0 < 64) k) _
      have hm := (h1.mul (hw_c.pow 9)).mul (h2L_c.pow (6 * d))
      rwa [Nat.zero_add] at hm
    have hEk_q := hEk_ge.pow q
    unfold Log2Ge at hEk_q
    have hltQ := Nat.le_of_lt (pow_lt_pow_left_of_lt (Nat.mul_pos (show 0 < c by omega) hQ) hlt)
    have htr := Nat.le_trans hEk_q hltQ
    rw [← Nat.pow_mul] at htr
    have eExp : q * (9 * (c * (d * Lw)) + 6 * d * (c * BL + 4 * k * Q))
        = (9 * q * Lw + 6 * q * BL) * d * c + 24 * q * Q * d * k := by grind
    have eP : p * (c * Q) = p * c * Q := by ac_rfl
    rwa [eExp, eP] at htr
  constructor
  · let y := d * G_t - c * C0
    have hy_pos : 1 ≤ y := by dsimp only [y]; omega
    have hdG : d * G_t = y + c * C0 := by dsimp only [y]; omega
    have hky : c * d * F < k * y := by
      have : k * y + c * (k * C0) = k * d * G_t := by
        have h1 : k * y + k * (c * C0) = k * (d * G_t) := by rw [← Nat.mul_add, ← hdG]
        have a1 : c * (k * C0) = k * (c * C0) := by ac_rfl
        have a2 : k * (d * G_t) = k * d * G_t := by ac_rfl
        omega
      have e1 : c * (d * F + k * C0) = c * d * F + c * (k * C0) := by rw [Nat.mul_add]; ac_rfl
      omega
    have hdk : 4 * c ^ 2 * C0 * F ≤ G_t ^ 2 * (d * k) := by
      have hq := nat_quad_amgm (c * C0) y
      rw [← hdG, Nat.mul_pow] at hq
      have h1 := Nat.mul_le_mul_left (c * F) hq
      have h2 := Nat.mul_le_mul_left (G_t ^ 2 * d) (Nat.le_of_lt hky)
      have eL : c * F * (4 * (c * C0) * y) = (4 * c ^ 2 * C0 * F) * y := by rw [Nat.pow_two c]; ac_rfl
      have eM : c * F * (d ^ 2 * G_t ^ 2) = G_t ^ 2 * d * (c * d * F) := by rw [Nat.pow_two d]; ac_rfl
      have eR : G_t ^ 2 * d * (k * y) = (G_t ^ 2 * (d * k)) * y := by ac_rfl
      have hcomb := Nat.le_trans (eL ▸ h1) (eR ▸ (eM ▸ h2))
      exact Nat.le_of_mul_le_mul_right hcomb hy_pos
    have hsc := hvk_ge.rescale (G_t ^ 2)
    unfold Log2Ge at hsc ⊢
    have hnum_c : c * ((9 * q * Lw + 6 * q * BL) * d_lb * G_t ^ 2 + 24 * q * Q * 4 * c_lo * C0 * F)
        ≤ G_t ^ 2 * ((9 * q * Lw + 6 * q * BL) * d * c + 24 * q * Q * d * k) := by
      rw [Nat.mul_add c, Nat.mul_add (G_t ^ 2)]
      apply Nat.add_le_add
      · have hm := Nat.mul_le_mul_right (c * G_t ^ 2) (Nat.mul_le_mul_left (9 * q * Lw + 6 * q * BL) hd_ge)
        have eL : (9 * q * Lw + 6 * q * BL) * d_lb * (c * G_t ^ 2)
            = c * ((9 * q * Lw + 6 * q * BL) * d_lb * G_t ^ 2) := by ac_rfl
        have eR : (9 * q * Lw + 6 * q * BL) * d * (c * G_t ^ 2)
            = G_t ^ 2 * ((9 * q * Lw + 6 * q * BL) * d * c) := by ac_rfl
        rwa [eL, eR] at hm
      · have hc_sq : c * c_lo ≤ c ^ 2 := by rw [Nat.pow_two c]; exact Nat.mul_le_mul_left c hc1
        have hm1 := Nat.mul_le_mul_left (24 * q * Q) hdk
        have hm2 := Nat.mul_le_mul_left (24 * q * Q * 4) (Nat.mul_le_mul_right (C0 * F) hc_sq)
        have eL : 24 * q * Q * 4 * (c * c_lo * (C0 * F))
            = c * (24 * q * Q * 4 * c_lo * C0 * F) := by ac_rfl
        have eM : 24 * q * Q * 4 * (c ^ 2 * (C0 * F))
            = 24 * q * Q * (4 * c ^ 2 * C0 * F) := by ac_rfl
        have eR : 24 * q * Q * (G_t ^ 2 * (d * k))
            = G_t ^ 2 * (24 * q * Q * d * k) := by ac_rfl
        exact Nat.le_trans (eL ▸ hm2) (eR ▸ (eM ▸ hm1))
    have hpow_c : (2 ^ ((9 * q * Lw + 6 * q * BL) * d_lb * G_t ^ 2 + 24 * q * Q * 4 * c_lo * C0 * F)) ^ c
        ≤ (v_k_pass c d k ^ (p * Q * G_t ^ 2)) ^ c := by
      rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm _ c]
      have eP : G_t ^ 2 * (p * c * Q) = p * Q * G_t ^ 2 * c := by ac_rfl
      rw [eP] at hsc
      exact Nat.le_trans (Nat.pow_le_pow_right (by decide) hnum_c) hsc
    exact le_of_pow_le_pow_left (by omega) hpow_c
  · intro h hPB
    rcases hPB with ⟨_hV2, hh, hlt_pb⟩
    have hw_le_S : w_pass c d ≤ 3 * (2 * d + 1) * w_pass c d - 2 := by
      have h3 : 9 ≤ 3 * (2 * d + 1) := by omega
      have hm : 9 * w_pass c d ≤ 3 * (2 * d + 1) * w_pass c d := Nat.mul_le_mul_right _ h3
      omega
    have hpb1 : w_pass c d ^ ((2 * k - 1) * q) * (E_k_pass c d k) ^ (h * q) < (v_k_pass c d k) ^ (h * p) := by
      have hpow_le : w_pass c d ^ (2 * k - 1) ≤ h * (3 * (2 * d + 1) * w_pass c d - 2) ^ (2 * k - 1) + 1 := by
        have h1 := Nat.pow_le_pow_left hw_le_S (2 * k - 1)
        have h2 := Nat.mul_le_mul_right ((3 * (2 * d + 1) * w_pass c d - 2) ^ (2 * k - 1)) hh
        rw [Nat.one_mul] at h2
        omega
      have hq_le := Nat.pow_le_pow_left hpow_le q
      rw [← Nat.pow_mul] at hq_le
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hq_le) hlt_pb
    have hpb_exp : c * (q * (2 * k - 1) * d * Lw + h * (d * F + k * C0)) < h * k * d * G_t := by
      unfold E_k_pass v_k_pass at hpb1
      rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow] at hpb1
      rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hpb1
      have hwsplit : w_pass c d ^ (9 * (h * q))
          = w_pass c d ^ (h * (9 * q - 2 * p)) * w_pass c d ^ (2 * (h * p)) := by
        rw [← Nat.pow_add]
        have : h * (9 * q - 2 * p) + 2 * (h * p) = 9 * (h * q) := by
          have h1 : h * (9 * q - 2 * p) + h * (2 * p) = h * (9 * q) := by
            rw [← Nat.mul_add, Nat.sub_add_cancel hτ]
          have a1 : h * (2 * p) = 2 * (h * p) := by ac_rfl
          have a2 : h * (9 * q) = 9 * (h * q) := by ac_rfl
          omega
        rw [this]
      rw [hwsplit] at hpb1
      have hpb_c : w_pass c d ^ ((2 * k - 1) * q) * w_pass c d ^ (h * (9 * q - 2 * p))
          * 64 ^ (k * (h * q)) * (2 * L_pass c k - 1) ^ (6 * d * (h * q))
          < Lambda_pass c d ^ (k * (h * p)) := by
        have eL : w_pass c d ^ ((2 * k - 1) * q)
            * (64 ^ (k * (h * q)) * (w_pass c d ^ (h * (9 * q - 2 * p)) * w_pass c d ^ (2 * (h * p)))
               * (2 * L_pass c k - 1) ^ (6 * d * (h * q)))
            = (w_pass c d ^ ((2 * k - 1) * q) * w_pass c d ^ (h * (9 * q - 2 * p))
               * 64 ^ (k * (h * q)) * (2 * L_pass c k - 1) ^ (6 * d * (h * q)))
              * w_pass c d ^ (2 * (h * p)) := by ac_rfl
        have eR : w_pass c d ^ (2 * (h * p)) * Lambda_pass c d ^ (k * (h * p))
            = Lambda_pass c d ^ (k * (h * p)) * w_pass c d ^ (2 * (h * p)) := Nat.mul_comm _ _
        rw [eL, eR] at hpb1
        exact Nat.lt_of_mul_lt_mul_right hpb1
      have hpos_m : 0 < (d + 1) ^ (2 * (k * (h * p))) * c ^ (4 * d * (k * (h * p)))
          * (c - 1) ^ (k * (6 * d * (h * q))) :=
        Nat.mul_pos (Nat.mul_pos (pow_pos_of_pos (by omega) _) (pow_pos_of_pos (by omega) _))
          (pow_pos_of_pos (by omega) _)
      have hlt_m := Nat.mul_lt_mul_of_pos_right hpb_c hpos_m
      have hLam_p := Nat.pow_le_pow_left (Lambda_pass_mul_le c d) (k * (h * p))
      rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at hLam_p
      have hlt_b : w_pass c d ^ ((2 * k - 1) * q + h * (9 * q - 2 * p))
          * (64 ^ q * (d + 1) ^ (2 * p)) ^ (h * k)
          * ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (6 * d * (h * q))
          * c ^ (4 * d * (k * (h * p)))
          < (c + 2) ^ (4 * d * (k * (h * p))) * (c - 1) ^ (k * (6 * d * (h * q))) := by
        have hm := Nat.mul_le_mul_right ((c - 1) ^ (k * (6 * d * (h * q)))) hLam_p
        have eL : w_pass c d ^ ((2 * k - 1) * q) * w_pass c d ^ (h * (9 * q - 2 * p))
            * 64 ^ (k * (h * q)) * (2 * L_pass c k - 1) ^ (6 * d * (h * q))
            * ((d + 1) ^ (2 * (k * (h * p))) * c ^ (4 * d * (k * (h * p)))
               * (c - 1) ^ (k * (6 * d * (h * q))))
            = w_pass c d ^ ((2 * k - 1) * q + h * (9 * q - 2 * p))
              * (64 ^ q * (d + 1) ^ (2 * p)) ^ (h * k)
              * ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (6 * d * (h * q))
              * c ^ (4 * d * (k * (h * p))) := by
          rw [Nat.pow_add, Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
          have a1 : q * (h * k) = k * (h * q) := by ac_rfl
          have a2 : 2 * p * (h * k) = 2 * (k * (h * p)) := by ac_rfl
          rw [a1, a2]; ac_rfl
        have eR : Lambda_pass c d ^ (k * (h * p)) *
            ((d + 1) ^ (2 * (k * (h * p))) * c ^ (4 * d * (k * (h * p)))
             * (c - 1) ^ (k * (6 * d * (h * q))))
            = Lambda_pass c d ^ (k * (h * p)) * (d + 1) ^ (2 * (k * (h * p)))
              * c ^ (4 * d * (k * (h * p))) * (c - 1) ^ (k * (6 * d * (h * q))) := by ac_rfl
        rw [eL, eR] at hlt_m
        exact Nat.lt_of_lt_of_le hlt_m hm
      have hltQ := pow_lt_pow_left_of_lt (Nat.mul_pos (show 0 < c by omega) hQ) hlt_b
      rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow] at hltQ
      have hBL_p := Nat.pow_le_pow_left hBL_eff (6 * d * (h * q) * c)
      rw [Nat.mul_pow (2 ^ BL), ← Nat.pow_mul 2, ← Nat.pow_mul ((c + 2) ^ k),
          ← Nat.pow_mul ((2 * L_pass c k - 1) * (c - 1) ^ k)] at hBL_p
      have hC0_p := Nat.pow_le_pow_left hC0_ge (h * k * c)
      rw [← Nat.pow_mul, ← Nat.pow_mul] at hC0_p
      have hw_p := hw_lin.pow (((2 * k - 1) * q + h * (9 * q - 2 * p)) * c)
      have hLHS_ge : 2 ^ (c * (q * (2 * k - 1) * d * Lw + h * (d * F + k * C0)))
          * ((c + 2) ^ (6 * d * k * (h * q)) * c ^ (4 * d * (k * (h * p)))) ^ (c * Q)
          ≤ (w_pass c d ^ ((2 * k - 1) * q + h * (9 * q - 2 * p))) ^ (c * Q)
            * ((64 ^ q * (d + 1) ^ (2 * p)) ^ (h * k)) ^ (c * Q)
            * (((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (6 * d * (h * q))) ^ (c * Q)
            * (c ^ (4 * d * (k * (h * p)))) ^ (c * Q) := by
        have hm1 := Nat.mul_le_mul (Nat.mul_le_mul hw_p hC0_p) hBL_p
        have hm2 := Nat.mul_le_mul_right ((c ^ (4 * d * (k * (h * p)))) ^ (c * Q)) hm1
        have eExp : c * (q * (2 * k - 1) * d * Lw + h * (d * F + k * C0))
            = ((2 * k - 1) * q + h * (9 * q - 2 * p)) * c * (d * Lw)
              + C0 * (h * k * c) + BL * (6 * d * (h * q) * c) := by dsimp only [F]; grind
        rw [eExp, Nat.pow_add, Nat.pow_add, Nat.mul_pow]
        have eW : (w_pass c d ^ (((2 * k - 1) * q + h * (9 * q - 2 * p)) * c)) ^ Q
            = (w_pass c d ^ ((2 * k - 1) * q + h * (9 * q - 2 * p))) ^ (c * Q) := by
          rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_assoc]
        have eA : ((c + 2) ^ k) ^ (Q * (6 * d * (h * q) * c))
            = ((c + 2) ^ (6 * d * k * (h * q))) ^ (c * Q) := by
          rw [← Nat.pow_mul, ← Nat.pow_mul]
          have : k * (Q * (6 * d * (h * q) * c)) = 6 * d * k * (h * q) * (c * Q) := by ac_rfl
          rw [this]
        have eB : (64 ^ q * (d + 1) ^ (2 * p)) ^ (Q * (h * k * c))
            = ((64 ^ q * (d + 1) ^ (2 * p)) ^ (h * k)) ^ (c * Q) := by
          rw [← Nat.pow_mul]
          have : Q * (h * k * c) = h * k * (c * Q) := by ac_rfl
          rw [this]
        have eC : ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (Q * (6 * d * (h * q) * c))
            = (((2 * L_pass c k - 1) * (c - 1) ^ k) ^ (6 * d * (h * q))) ^ (c * Q) := by
          rw [← Nat.pow_mul]
          have : Q * (6 * d * (h * q) * c) = 6 * d * (h * q) * (c * Q) := by ac_rfl
          rw [this]
        rw [eW, eA, eB, eC] at hm2
        have eL2 : 2 ^ (((2 * k - 1) * q + h * (9 * q - 2 * p)) * c * (d * Lw))
            * 2 ^ (C0 * (h * k * c)) * 2 ^ (BL * (6 * d * (h * q) * c))
            * (((c + 2) ^ (6 * d * k * (h * q))) ^ (c * Q)
               * (c ^ (4 * d * (k * (h * p)))) ^ (c * Q))
            = 2 ^ (((2 * k - 1) * q + h * (9 * q - 2 * p)) * c * (d * Lw)) * 2 ^ (C0 * (h * k * c))
              * (2 ^ (BL * (6 * d * (h * q) * c)) * ((c + 2) ^ (6 * d * k * (h * q))) ^ (c * Q))
              * (c ^ (4 * d * (k * (h * p)))) ^ (c * Q) := by ac_rfl
        rw [eL2]; exact hm2
      have hGdhk := Nat.pow_le_pow_left hG_tail (h * d * k)
      rw [← Nat.pow_mul ((c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q)),
          Nat.mul_pow (2 ^ G_t), ← Nat.pow_mul 2, ← Nat.pow_mul (c ^ (4 * p))] at hGdhk
      have hRHS_le : ((c + 2) ^ (4 * d * (k * (h * p))) * (c - 1) ^ (k * (6 * d * (h * q)))) ^ (c * Q)
          ≤ 2 ^ (h * k * d * G_t)
            * ((c + 2) ^ (6 * d * k * (h * q)) * c ^ (4 * d * (k * (h * p)))) ^ (c * Q) := by
        have hm := Nat.mul_le_mul_right (((c + 2) ^ (6 * d * k * (h * q))) ^ (c * Q)) hGdhk
        have eL : ((c + 2) ^ (4 * d * (k * (h * p))) * (c - 1) ^ (k * (6 * d * (h * q)))) ^ (c * Q)
            = ((c + 2) ^ (4 * p - 6 * q) * (c - 1) ^ (6 * q)) ^ (c * Q * (h * d * k))
              * ((c + 2) ^ (6 * d * k * (h * q))) ^ (c * Q) := by
          rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
          have hsum : (4 * p - 6 * q) * (c * Q * (h * d * k)) + 6 * d * k * (h * q) * (c * Q)
              = 4 * d * (k * (h * p)) * (c * Q) := by
            have h1 : (4 * p - 6 * q) * (c * Q * h * d * k) + (6 * q) * (c * Q * h * d * k)
                = (4 * p) * (c * Q * h * d * k) := by
              rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
            have a1 : (4 * p - 6 * q) * (c * Q * (h * d * k)) = (4 * p - 6 * q) * (c * Q * h * d * k) := by ac_rfl
            have a2 : 6 * d * k * (h * q) * (c * Q) = (6 * q) * (c * Q * h * d * k) := by ac_rfl
            have a3 : 4 * d * (k * (h * p)) * (c * Q) = (4 * p) * (c * Q * h * d * k) := by ac_rfl
            omega
          have e6 : 6 * q * (c * Q * (h * d * k)) = k * (6 * d * (h * q)) * (c * Q) := by ac_rfl
          rw [e6, ← hsum, Nat.pow_add]; ac_rfl
        have eR : 2 ^ (G_t * (h * d * k)) * (c ^ (4 * p)) ^ (c * Q * (h * d * k))
            * ((c + 2) ^ (6 * d * k * (h * q))) ^ (c * Q)
            = 2 ^ (h * k * d * G_t)
              * ((c + 2) ^ (6 * d * k * (h * q)) * c ^ (4 * d * (k * (h * p)))) ^ (c * Q) := by
          rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
          have a1 : G_t * (h * d * k) = h * k * d * G_t := by ac_rfl
          have a2 : 4 * p * (c * Q * (h * d * k)) = 4 * d * (k * (h * p)) * (c * Q) := by ac_rfl
          rw [a1, a2]; ac_rfl
        rw [eL, ← eR]; exact hm
      have h2lt := Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt hLHS_ge (Nat.lt_of_lt_of_le hltQ hRHS_le))
      by_cases hcmp : c * (q * (2 * k - 1) * d * Lw + h * (d * F + k * C0)) < h * k * d * G_t
      · exact hcmp
      · have := Nat.pow_le_pow_right (n := 2) (by decide)
          (show h * k * d * G_t ≤ c * (q * (2 * k - 1) * d * Lw + h * (d * F + k * C0)) by omega)
        omega
    let y := d * G_t - c * C0
    have hy_pos : 1 ≤ y := by dsimp only [y]; omega
    have hdG : d * G_t = y + c * C0 := by dsimp only [y]; omega
    let z := k * y - c * d * F
    have hky : c * d * F < k * y := by
      have : k * y + c * (k * C0) = k * d * G_t := by
        have h1 : k * y + k * (c * C0) = k * (d * G_t) := by rw [← Nat.mul_add, ← hdG]
        have a1 : c * (k * C0) = k * (c * C0) := by ac_rfl
        have a2 : k * (d * G_t) = k * d * G_t := by ac_rfl
        omega
      have e1 : c * (d * F + k * C0) = c * d * F + c * (k * C0) := by rw [Nat.mul_add]; ac_rfl
      omega
    have hz_pos : 1 ≤ z := by dsimp only [z]; omega
    have hkyz : k * y = z + c * d * F := by dsimp only [z]; omega
    have hhz : c * q * (2 * k - 1) * d * Lw < h * z := by
      have hid : h * z + c * (h * (d * F + k * C0)) = h * k * d * G_t := by
        have h1 : z + c * (d * F + k * C0) = k * d * G_t := by
          have : k * y + k * (c * C0) = k * (d * G_t) := by rw [← Nat.mul_add, ← hdG]
          have a1 : c * (d * F + k * C0) = c * d * F + k * (c * C0) := by rw [Nat.mul_add]; ac_rfl
          have a2 : k * (d * G_t) = k * d * G_t := by ac_rfl
          omega
        have h2 := congrArg (h * ·) h1
        rw [Nat.mul_add] at h2
        have a1 : h * (c * (d * F + k * C0)) = c * (h * (d * F + k * C0)) := by ac_rfl
        have a2 : h * (k * d * G_t) = h * k * d * G_t := by ac_rfl
        omega
      have e1 : c * (q * (2 * k - 1) * d * Lw + h * (d * F + k * C0))
          = c * q * (2 * k - 1) * d * Lw + c * (h * (d * F + k * C0)) := by rw [Nat.mul_add]; ac_rfl
      omega
    have h2k : (2 * k_lb - 1) * k ≤ k_lb * (2 * k - 1) := by
      apply nat_le_of_int
      have e1 : ((2 * k_lb - 1 : Nat) : Int) = 2 * (k_lb : Int) - 1 := by omega
      have e2 : ((2 * k - 1 : Nat) : Int) = 2 * (k : Int) - 1 := by omega
      simp only [Int.natCast_mul]; rw [e1, e2]
      have hid : (k_lb : Int) * (2 * (k : Int) - 1) - (2 * (k_lb : Int) - 1) * (k : Int)
          = (k : Int) - (k_lb : Int) := by grind
      omega
    have hstep_k : 4 * c ^ 2 * q * (2 * k_lb - 1) * Lw * F * d ^ 2 ≤ k_lb * h * k * y ^ 2 := by
      have hq_k := nat_quad_amgm (c * d * F) z
      rw [← hkyz, Nat.mul_pow] at hq_k
      have h1 := Nat.mul_le_mul_left (c * q * (2 * k_lb - 1) * d * Lw) hq_k
      have h2 : (c * q * (2 * k_lb - 1) * d * Lw) * k ≤ k_lb * (c * q * (2 * k - 1) * d * Lw) := by
        have hm := Nat.mul_le_mul_left (c * q * d * Lw) h2k
        have eL : c * q * d * Lw * ((2 * k_lb - 1) * k) = c * q * (2 * k_lb - 1) * d * Lw * k := by ac_rfl
        have eR : c * q * d * Lw * (k_lb * (2 * k - 1)) = k_lb * (c * q * (2 * k - 1) * d * Lw) := by ac_rfl
        rwa [eL, eR] at hm
      have h3 : (c * q * (2 * k_lb - 1) * d * Lw) * (k ^ 2 * y ^ 2) ≤ (k_lb * h * k * y ^ 2) * z := by
        have hm1 := Nat.mul_le_mul_right (k * y ^ 2) h2
        have hm2 := Nat.mul_le_mul_left (k_lb * k * y ^ 2) (Nat.le_of_lt hhz)
        have eL : c * q * (2 * k_lb - 1) * d * Lw * k * (k * y ^ 2)
            = c * q * (2 * k_lb - 1) * d * Lw * (k ^ 2 * y ^ 2) := by rw [Nat.pow_two k]; ac_rfl
        have eM : k_lb * (c * q * (2 * k - 1) * d * Lw) * (k * y ^ 2)
            = k_lb * k * y ^ 2 * (c * q * (2 * k - 1) * d * Lw) := by ac_rfl
        have eR : k_lb * k * y ^ 2 * (h * z) = (k_lb * h * k * y ^ 2) * z := by ac_rfl
        rw [← eL, ← eR]
        exact Nat.le_trans hm1 (eM ▸ hm2)
      have hcomb := Nat.le_trans h1 h3
      have eL : c * q * (2 * k_lb - 1) * d * Lw * (4 * (c * d * F) * z)
          = (4 * c ^ 2 * q * (2 * k_lb - 1) * Lw * F * d ^ 2) * z := by
        rw [Nat.pow_two c, Nat.pow_two d]; ac_rfl
      rw [eL] at hcomb
      exact Nat.le_of_mul_le_mul_right hcomb hz_pos
    have hdhk : 27 * c ^ 3 * q * (2 * k_lb - 1) * Lw * F * C0 ≤ k_lb * G_t ^ 3 * (d * h * k) := by
      have hc_d := nat_cubic_amgm (c * C0) y
      rw [← hdG, Nat.mul_pow] at hc_d
      have h1 := Nat.mul_le_mul_left (c ^ 2 * q * (2 * k_lb - 1) * Lw * F) hc_d
      have h2 := Nat.mul_le_mul_left (d * G_t ^ 3) hstep_k
      have eL : c ^ 2 * q * (2 * k_lb - 1) * Lw * F * (27 * (c * C0) * y ^ 2)
          = (27 * c ^ 3 * q * (2 * k_lb - 1) * Lw * F * C0) * y ^ 2 := by rw [Nat.pow_succ c 2]; ac_rfl
      have eM : c ^ 2 * q * (2 * k_lb - 1) * Lw * F * (4 * (d ^ 3 * G_t ^ 3))
          = d * G_t ^ 3 * (4 * c ^ 2 * q * (2 * k_lb - 1) * Lw * F * d ^ 2) := by
        rw [Nat.pow_succ d 2]; ac_rfl
      have eR : d * G_t ^ 3 * (k_lb * h * k * y ^ 2)
          = (k_lb * G_t ^ 3 * (d * h * k)) * y ^ 2 := by ac_rfl
      have hcomb := Nat.le_trans (eL ▸ h1) (eR ▸ (eM ▸ h2))
      exact Nat.le_of_mul_le_mul_right hcomb (pow_pos_of_pos hy_pos 2)
    have hV_ge : Log2Ge ((v_k_pass c d k) ^ h) (24 * q * Q * (d * h * k)) (p * c * Q) := by
      have h1 := (hvk_ge.mono_exp (Nat.le_add_left (24 * q * Q * d * k) _)).pow h
      have e : h * (24 * q * Q * d * k) = 24 * q * Q * (d * h * k) := by ac_rfl
      rwa [e] at h1
    have hsc := hV_ge.rescale (k_lb * G_t ^ 3)
    unfold Log2Ge at hsc ⊢
    have hc3 : c * c_lo ^ 2 ≤ c ^ 3 := by
      rw [Nat.pow_succ c 2, Nat.mul_comm]
      exact Nat.mul_le_mul_right c (Nat.pow_le_pow_left hc1 2)
    have hnum_c : c * (24 * q * Q * 27 * q * (2 * k_lb - 1) * Lw * F * C0 * c_lo ^ 2)
        ≤ k_lb * G_t ^ 3 * (24 * q * Q * (d * h * k)) := by
      have hm1 := Nat.mul_le_mul_left (24 * q * Q) hdhk
      have hm2 := Nat.mul_le_mul_left (24 * q * Q * 27 * q * (2 * k_lb - 1) * Lw * F * C0) hc3
      have eL : 24 * q * Q * 27 * q * (2 * k_lb - 1) * Lw * F * C0 * (c * c_lo ^ 2)
          = c * (24 * q * Q * 27 * q * (2 * k_lb - 1) * Lw * F * C0 * c_lo ^ 2) := by ac_rfl
      have eM : 24 * q * Q * 27 * q * (2 * k_lb - 1) * Lw * F * C0 * c ^ 3
          = 24 * q * Q * (27 * c ^ 3 * q * (2 * k_lb - 1) * Lw * F * C0) := by ac_rfl
      have eR : 24 * q * Q * (k_lb * G_t ^ 3 * (d * h * k))
          = k_lb * G_t ^ 3 * (24 * q * Q * (d * h * k)) := by ac_rfl
      exact Nat.le_trans (eL ▸ hm2) (eR ▸ (eM ▸ hm1))
    have hpow_c : (2 ^ (24 * q * Q * 27 * q * (2 * k_lb - 1) * Lw * F * C0 * c_lo ^ 2)) ^ c
        ≤ (((v_k_pass c d k) ^ h) ^ (p * Q * k_lb * G_t ^ 3)) ^ c := by
      rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm _ c]
      have eP : k_lb * G_t ^ 3 * (p * c * Q) = p * Q * k_lb * G_t ^ 3 * c := by ac_rfl
      rw [eP] at hsc
      exact Nat.le_trans (Nat.pow_le_pow_right (by decide) hnum_c) hsc
    exact le_of_pow_le_pow_left (by omega) hpow_c

theorem log2Ge_of_mul_two_pow {Q x a la s : Nat} (hle : a * 2 ^ s ≤ x) (ha : Log2Ge a la Q) :
    Log2Ge x (la + s * Q) Q :=
  (ha.mul (Log2Ge.two_pow s Q)).mono_left hle

theorem log2Le_of_mul_two_pow {Q x b lb s : Nat} (hle : x ≤ b * 2 ^ s) (hb : Log2Le b lb Q) :
    Log2Le x (lb + s * Q) Q :=
  (hb.mul (Log2Le.two_pow s Q)).mono_left hle

theorem tail_d_bootstrap_step {Q p q c_lo c d G_t d_prev ld_prev d_next : Nat}
    (hc1 : c_lo ≤ c)
    (hroundQ : (64 ^ q * (d + 1) ^ (2 * p)) ^ (c * Q) < 2 ^ (d * G_t))
    (hd_prev : d_prev ≤ d)
    (hld : Log2Ge (d_prev + 1) ld_prev Q)
    (hstep : (d_next - 1) * G_t ≤ c_lo * (6 * q * Q + 2 * p * ld_prev)) :
    d_next ≤ d := by
  have h64 : Log2Ge (64 ^ q) (6 * q * Q) Q := by
    have h6 : Log2Ge 64 (6 * Q) Q := by
      have : (64 : Nat) = 2 ^ 6 := by decide
      rw [this]; exact Log2Ge.two_pow 6 Q
    have hp := h6.pow q
    have e : q * (6 * Q) = 6 * q * Q := by ac_rfl
    rwa [e] at hp
  have hge := (h64.mul ((hld.mono_left (show d_prev + 1 ≤ d + 1 by omega)).pow (2 * p))).rescale c
  unfold Log2Ge at hge
  have hlt : 2 ^ (c * (6 * q * Q + 2 * p * ld_prev)) < 2 ^ (d * G_t) :=
    Nat.lt_of_le_of_lt hge hroundQ
  have hexp : c * (6 * q * Q + 2 * p * ld_prev) < d * G_t := by
    by_cases h : c * (6 * q * Q + 2 * p * ld_prev) < d * G_t
    · exact h
    · have := Nat.pow_le_pow_right (n := 2) (by decide)
        (show d * G_t ≤ c * (6 * q * Q + 2 * p * ld_prev) by omega)
      omega
  have hlo : c_lo * (6 * q * Q + 2 * p * ld_prev) ≤ c * (6 * q * Q + 2 * p * ld_prev) :=
    Nat.mul_le_mul_right _ hc1
  by_cases h : d_next ≤ d
  · exact h
  · have hmul : d * G_t ≤ (d_next - 1) * G_t := Nat.mul_le_mul_right G_t (by omega)
    omega


/-! ### Zero-unfolding symbolic wrappers for concrete instantiations -/

def RoundBound (Q p q G d : Nat) : Prop :=
  (64 ^ q * (d + 1) ^ (2 * p)) ^ Q < 2 ^ (d * G)

def TailRoundBound (Q p q G_t c d : Nat) : Prop :=
  (64 ^ q * (d + 1) ^ (2 * p)) ^ (c * Q) < 2 ^ (d * G_t)

def CeilBoost (Q c k BL : Nat) : Prop :=
  2 ^ BL * ((c + 2) ^ k) ^ Q ≤ ((2 * L_pass c k - 1) * (c - 1) ^ k) ^ Q

theorem tail_cb_univ {Q p q c_lo c' k' Lw lj l22 BL : Nat}
    (hc_lo : 2 ≤ c_lo) (hc' : c_lo ≤ c')
    (hk' : 3 * (9 * q - 2 * p) * Lw * c' ≤ k' * (3 * (4 * p - 9 * q) * Q) * 3)
    (hpos : 0 < 3 * (9 * q - 2 * p) * Lw)
    (hcoef : 3 * (4 * p - 9 * q) * Q ≤ 3 * (9 * q - 2 * p) * Lw)
    (hlj : Log2Ge (2 * ((c_lo - 1) / 3) + 1) lj Q) (hl22 : Log2Le 22 l22 Q)
    (hBL : 3 * BL + l22 ≤ 3 * lj) :
    CeilBoost Q c' k' BL := by
  have hk_div : (c' - 1) / 3 ≤ k' := by
    have h1 : k' * (3 * (4 * p - 9 * q) * Q) * 3 ≤ k' * (3 * (9 * q - 2 * p) * Lw) * 3 :=
      Nat.mul_le_mul_right 3 (Nat.mul_le_mul_left k' hcoef)
    have h2 : 3 * (9 * q - 2 * p) * Lw * c' ≤ 3 * (9 * q - 2 * p) * Lw * (3 * k') := by
      have eR : k' * (3 * (9 * q - 2 * p) * Lw) * 3 = 3 * (9 * q - 2 * p) * Lw * (3 * k') := by ac_rfl
      exact Nat.le_trans hk' (eR ▸ h1)
    have h3 : c' ≤ 3 * k' := Nat.le_of_mul_le_mul_left h2 hpos
    omega
  exact ceiling_boost_univ hc_lo hc' hk_div hlj hl22 hBL

theorem d_boot {Q p q d G d_prev ld_prev d_next : Nat}
    (hr : RoundBound Q p q G d) (hd : d_prev ≤ d)
    (hld : Log2Ge (d_prev + 1) ld_prev Q)
    (hstep : (d_next - 1) * G ≤ 6 * q * Q + 2 * p * ld_prev) : d_next ≤ d :=
  d_bootstrap_step hr hd hld hstep

theorem tail_d_boot {Q p q c_lo c d G_t d_prev ld_prev d_next : Nat}
    (hc1 : c_lo ≤ c) (hr : TailRoundBound Q p q G_t c d) (hd : d_prev ≤ d)
    (hld : Log2Ge (d_prev + 1) ld_prev Q)
    (hstep : (d_next - 1) * G_t ≤ c_lo * (6 * q * Q + 2 * p * ld_prev)) : d_next ≤ d :=
  tail_d_bootstrap_step hc1 hr hd hld hstep

theorem cb_zero (Q c k : Nat) (hc : 2 ≤ c) : CeilBoost Q c k 0 :=
  ceiling_boost_zero Q c k hc

theorem cb_narrow {Q c_lo c_hi c k lj lc2_hi lcm1_lo BL : Nat}
    (hc_lo : 2 ≤ c_lo) (h1 : c_lo ≤ c) (h2 : c ≤ c_hi) (hk : (c_hi - 1) / 3 ≤ k)
    (hlj : Log2Ge (2 * ((c_lo - 1) / 3) + 1) lj Q)
    (hlc2 : Log2Le (c_lo + 2) lc2_hi Q) (hlcm1 : Log2Ge (c_lo - 1) lcm1_lo Q)
    (hBL : BL + ((c_hi - 1) / 3) * lc2_hi ≤ lj + ((c_hi - 1) / 3) * lcm1_lo) :
    CeilBoost Q c k BL :=
  ceiling_boost_narrow hc_lo h1 h2 hk hlj hlc2 hlcm1 hBL

theorem cb_univ {Q c_lo c k lj l22 BL : Nat}
    (hc_lo : 2 ≤ c_lo) (hc : c_lo ≤ c) (hk : (c - 1) / 3 ≤ k)
    (hlj : Log2Ge (2 * ((c_lo - 1) / 3) + 1) lj Q) (hl22 : Log2Le 22 l22 Q)
    (hBL : 3 * BL + l22 ≤ 3 * lj) :
    CeilBoost Q c k BL :=
  ceiling_boost_univ hc_lo hc hk hlj hl22 hBL

theorem band_step_of_log2
    {Q p q c_lo c_hi c_g c d k G lc2_g lcm1_g lc_g d_lb ld_lb pen_Q Lw k_lb0 BL S lcm1_hi lc2_hi R k_lb M_pre M_post : Nat}
    (hQ : 0 < Q) (hV : ValidPassTriple p q c d k)
    (hτ : 2 * p ≤ 9 * q) (h94 : 9 * q ≤ 4 * p)
    (hc_lo : 2 ≤ c_lo) (hcg : 2 ≤ c_g) (hc1 : c_lo ≤ c) (hc2 : c ≤ c_hi)
    (hmono : ((c + 2) ^ (2 * p - 3 * q) * (c - 1) ^ (3 * q)) * c_g ^ (2 * p)
           ≤ ((c_g + 2) ^ (2 * p - 3 * q) * (c_g - 1) ^ (3 * q)) * c ^ (2 * p))
    (hlc2_g : Log2Le (c_g + 2) lc2_g Q) (hlcm1_g : Log2Le (c_g - 1) lcm1_g Q) (hlc_g : Log2Ge c_g lc_g Q)
    (hGc : (4 * p - 6 * q) * lc2_g + 6 * q * lcm1_g ≤ G + 4 * p * lc_g)
    (hd_lb_pos : 1 ≤ d_lb) (hd_lb : RoundBound Q p q G d → d_lb ≤ d)
    (hld_lb : Log2Ge (d_lb + 1) ld_lb Q)
    (hlc2 : Log2Ge (c_lo + 2) ((Lw + pen_Q) / 2) Q) (hLw_even : Lw + pen_Q = 2 * ((Lw + pen_Q) / 2))
    (h2d : Log2Le (2 * (d_lb + 1)) (d_lb * pen_Q) Q) (hpen_step : 2 * Q ≤ pen_Q * (d_lb + 1))
    (hk_lb0 : k_lb0 * G ≤ (9 * q - 2 * p) * Lw)
    (hBL : k_lb0 ≤ k → CeilBoost Q c k BL)
    (hlcm1_hi : Log2Le (c_hi - 1) lcm1_hi Q) (hlc2_hi : Log2Ge (c_hi + 2) lc2_hi Q)
    (hSc : S + lcm1_hi ≤ lc2_hi)
    (hklb_pos : 1 ≤ k_lb) (hklb_def : k_lb * G ≤ (9 * q - 2 * p) * Lw + 6 * q * BL)
    (hR : R ^ 2 ≤ 4 * ((9 * q * Lw + 6 * q * BL) * G + 6 * q * S * ((9 * q - 2 * p) * Lw + 6 * q * BL))
                    * (6 * q * S * ((9 * q - 2 * p) * Lw + 6 * q * BL))
                    * (6 * q * Q + 2 * p * ld_lb) ^ 2)
    (hpre : M_pre * (p * Q * G ^ 2) * 14267572528
            < (((9 * q * Lw + 6 * q * BL) * G + 2 * (6 * q * S * ((9 * q - 2 * p) * Lw + 6 * q * BL)))
               * (6 * q * Q + 2 * p * ld_lb) + R) * Q_SCALE)
    (hpost : M_post * (p * Q * k_lb * G ^ 3) * 14267572528
             < (6 * q * S * (27 * q * (2 * k_lb - 1) * Lw
               * ((9 * q - 2 * p) * Lw + 6 * q * BL)
               * (6 * q * Q + 2 * p * ld_lb))) * Q_SCALE) :
    10 ^ M_pre < v_k_pass c d k ∧
    (∀ h, ValidPostBini p q c d k h → 10 ^ M_post < (v_k_pass c d k) ^ h) := by
  have hG_g := band_hG_of_log2 hlc2_g hlcm1_g hlc_g hGc
  have hG := band_hG_transfer hcg hmono hG_g
  have hS : 2 ^ S * (c_hi - 1) ^ Q ≤ (c_hi + 2) ^ Q := by
    have hm := Nat.mul_le_mul_left (2 ^ S) hlcm1_hi
    rw [← Nat.pow_add] at hm
    exact Nat.le_trans hm (Nat.le_trans (Nat.pow_le_pow_right (by decide) hSc) hlc2_hi)
  have hres := band_universal_lb hQ hV hτ h94 hc_lo hc1 hc2 hG hd_lb_pos hd_lb hld_lb
    hlc2 hLw_even h2d hpen_step hk_lb0 hBL hS hklb_pos hklb_def hR
  exact ⟨pow10_lt_of_log2 hres.1 hpre, fun h hPB => pow10_lt_of_log2 (hres.2 h hPB) hpost⟩

theorem tail_step_of_log2
    {Q p q c_lo c d k d_lb ld_lb pen_Q Lw BL k_lb M_pre M_post : Nat}
    (hQ : 0 < Q) (hV : ValidPassTriple p q c d k)
    (hτ : 2 * p ≤ 9 * q) (h94 : 9 * q ≤ 4 * p)
    (hc_lo : 4 ≤ c_lo) (hc1 : c_lo ≤ c)
    (hd_lb_pos : 1 ≤ d_lb)
    (hd_lb : TailRoundBound Q p q (3 * (4 * p - 9 * q) * Q) c d → d_lb ≤ d)
    (hld_lb : Log2Ge (d_lb + 1) ld_lb Q)
    (hlc2 : Log2Ge (c_lo + 2) ((Lw + pen_Q) / 2) Q) (hLw_even : Lw + pen_Q = 2 * ((Lw + pen_Q) / 2))
    (h2d : Log2Le (2 * (d_lb + 1)) (d_lb * pen_Q) Q) (hpen_step : 2 * Q ≤ pen_Q * (d_lb + 1))
    (hBL : ∀ c' k', c_lo ≤ c' → 3 * (9 * q - 2 * p) * Lw * c' ≤ k' * (3 * (4 * p - 9 * q) * Q) * 3 →
        CeilBoost Q c' k' BL)
    (hklb_pos : 1 ≤ k_lb)
    (hklb_def : k_lb * (3 * (4 * p - 9 * q) * Q) ≤ c_lo * ((9 * q - 2 * p) * Lw + 6 * q * BL))
    (hpre : M_pre * (p * Q * (3 * (4 * p - 9 * q) * Q) ^ 2) * 14267572528
            < ((9 * q * Lw + 6 * q * BL) * d_lb * (3 * (4 * p - 9 * q) * Q) ^ 2
               + 24 * q * Q * 4 * c_lo * (6 * q * Q + 2 * p * ld_lb)
                 * ((9 * q - 2 * p) * Lw + 6 * q * BL)) * Q_SCALE)
    (hpost : M_post * (p * Q * k_lb * (3 * (4 * p - 9 * q) * Q) ^ 3) * 14267572528
             < (24 * q * Q * 27 * q * (2 * k_lb - 1) * Lw
               * ((9 * q - 2 * p) * Lw + 6 * q * BL)
               * (6 * q * Q + 2 * p * ld_lb) * c_lo ^ 2) * Q_SCALE) :
    10 ^ M_pre < v_k_pass c d k ∧
    (∀ h, ValidPostBini p q c d k h → 10 ^ M_post < (v_k_pass c d k) ^ h) := by
  have hres := tail_universal_lb hQ hV hτ h94 hc_lo hc1 hd_lb_pos hd_lb hld_lb
    hlc2 hLw_even h2d hpen_step hBL hklb_pos hklb_def
  exact ⟨pow10_lt_of_log2 hres.1 hpre, fun h hPB => pow10_lt_of_log2 (hres.2 h hPB) hpost⟩

theorem universal_c_min_of_log2 {Q p q c_min c d k l1 l2 l3 : Nat}
    (hQ : 0 < Q) (hV : ValidPassTriple p q c d k)
    (hτ : 2 * p ≤ 9 * q) (h94 : 9 * q ≤ 4 * p) (hcm : 3 ≤ c_min)
    (hmono : (4 * p - 9 * q) * (c_min - 2) ≤ 9 * q)
    (hl1 : Log2Le (c_min + 1) l1 Q) (hl2 : Log2Le (c_min - 2) l2 Q)
    (hl3 : Log2Ge (c_min - 1) l3 Q)
    (hcmp : (2 * p - 3 * q) * l1 + 3 * q * l2 ≤ 2 * p * l3) :
    c_min ≤ c := by
  apply universal_c_min_of_step hV hτ h94 hcm hmono
  have hL := (hl1.pow (2 * p - 3 * q)).mul (hl2.pow (3 * q))
  have hR := hl3.pow (2 * p)
  have hle := le_pow_of_log2 (a := 1) (b := 1) hL hR hQ (by simpa [Nat.mul_one] using hcmp)
  simpa using hle


/-! ### Shared `Q_SCALE = 2^32` dyadic certificates for band endpoints -/

private theorem u_ge_2 : Log2Ge 2 4294967296 Q_SCALE := log2Ge_Q 2 4294967296 (by decide)
private theorem u_ge_3 : Log2Ge 3 6807362105 Q_SCALE := log2Ge_Q 3 6807362105 (by decide)
private theorem u_ge_4 : Log2Ge 4 8589934592 Q_SCALE := log2Ge_Q 4 8589934592 (by decide)
private theorem u_ge_5 : Log2Ge 5 9972605231 Q_SCALE := log2Ge_Q 5 9972605231 (by decide)
private theorem u_ge_6 : Log2Ge 6 11102329401 Q_SCALE := log2Ge_Q 6 11102329401 (by decide)
private theorem u_ge_7 : Log2Ge 7 12057497578 Q_SCALE := log2Ge_Q 7 12057497578 (by decide)
private theorem u_ge_8 : Log2Ge 8 12884901888 Q_SCALE := log2Ge_Q 8 12884901888 (by decide)
private theorem u_ge_9 : Log2Ge 9 13614724211 Q_SCALE := log2Ge_Q 9 13614724211 (by decide)
private theorem u_ge_10 : Log2Ge 10 14267572527 Q_SCALE := log2Ge_Q 10 14267572527 (by decide)
private theorem u_ge_11 : Log2Ge 11 14858145664 Q_SCALE := log2Ge_Q 11 14858145664 (by decide)
private theorem u_ge_12 : Log2Ge 12 15397296697 Q_SCALE := log2Ge_Q 12 15397296697 (by decide)
private theorem u_ge_13 : Log2Ge 13 15893267570 Q_SCALE := log2Ge_Q 13 15893267570 (by decide)
private theorem u_ge_14 : Log2Ge 14 16352464874 Q_SCALE := log2Ge_Q 14 16352464874 (by decide)
private theorem u_ge_15 : Log2Ge 15 16779967337 Q_SCALE := log2Ge_Q 15 16779967337 (by decide)
private theorem u_ge_16 : Log2Ge 16 17179869184 Q_SCALE := log2Ge_Q 16 17179869184 (by decide)
private theorem u_ge_17 : Log2Ge 17 17555519226 Q_SCALE := log2Ge_Q 17 17555519226 (by decide)
private theorem u_ge_18 : Log2Ge 18 17909691507 Q_SCALE := log2Ge_Q 18 17909691507 (by decide)
private theorem u_ge_19 : Log2Ge 19 18244709746 Q_SCALE := log2Ge_Q 19 18244709746 (by decide)
private theorem u_ge_20 : Log2Ge 20 18562539823 Q_SCALE := log2Ge_Q 20 18562539823 (by decide)
private theorem u_ge_21 : Log2Ge 21 18864859684 Q_SCALE := log2Ge_Q 21 18864859684 (by decide)
private theorem u_ge_22 : Log2Ge 22 19153112960 Q_SCALE := log2Ge_Q 22 19153112960 (by decide)
private theorem u_ge_23 : Log2Ge 23 19428550662 Q_SCALE := log2Ge_Q 23 19428550662 (by decide)
private theorem u_ge_24 : Log2Ge 24 19692263993 Q_SCALE := log2Ge_Q 24 19692263993 (by decide)
private theorem u_ge_25 : Log2Ge 25 19945210462 Q_SCALE := log2Ge_Q 25 19945210462 (by decide)
private theorem u_ge_26 : Log2Ge 26 20188234866 Q_SCALE := log2Ge_Q 26 20188234866 (by decide)
private theorem u_ge_27 : Log2Ge 27 20422086317 Q_SCALE := log2Ge_Q 27 20422086317 (by decide)
private theorem u_ge_28 : Log2Ge 28 20647432170 Q_SCALE := log2Ge_Q 28 20647432170 (by decide)
private theorem u_ge_29 : Log2Ge 29 20864869498 Q_SCALE := log2Ge_Q 29 20864869498 (by decide)
private theorem u_ge_30 : Log2Ge 30 21074934633 Q_SCALE := log2Ge_Q 30 21074934633 (by decide)
private theorem u_ge_31 : Log2Ge 31 21278111131 Q_SCALE := log2Ge_Q 31 21278111131 (by decide)
private theorem u_ge_32 : Log2Ge 32 21474836480 Q_SCALE := log2Ge_Q 32 21474836480 (by decide)
private theorem u_ge_33 : Log2Ge 33 21665507770 Q_SCALE := log2Ge_Q 33 21665507770 (by decide)
private theorem u_ge_34 : Log2Ge 34 21850486522 Q_SCALE := log2Ge_Q 34 21850486522 (by decide)
private theorem u_ge_35 : Log2Ge 35 22030102809 Q_SCALE := log2Ge_Q 35 22030102809 (by decide)
private theorem u_ge_36 : Log2Ge 36 22204658803 Q_SCALE := log2Ge_Q 36 22204658803 (by decide)
private theorem u_ge_37 : Log2Ge 37 22374431835 Q_SCALE := log2Ge_Q 37 22374431835 (by decide)
private theorem u_ge_38 : Log2Ge 38 22539677042 Q_SCALE := log2Ge_Q 38 22539677042 (by decide)
private theorem u_ge_39 : Log2Ge 39 22700629676 Q_SCALE := log2Ge_Q 39 22700629676 (by decide)
private theorem u_ge_40 : Log2Ge 40 22857507119 Q_SCALE := log2Ge_Q 40 22857507119 (by decide)
private theorem u_ge_41 : Log2Ge 41 23010510646 Q_SCALE := log2Ge_Q 41 23010510646 (by decide)
private theorem u_ge_42 : Log2Ge 42 23159826980 Q_SCALE := log2Ge_Q 42 23159826980 (by decide)
private theorem u_ge_46 : Log2Ge 46 23723517958 Q_SCALE := log2Ge_Q 46 23723517958 (by decide)
private theorem u_ge_47 : Log2Ge 47 23856777460 Q_SCALE := log2Ge_Q 47 23856777460 (by decide)
private theorem u_ge_48 : Log2Ge 48 23987231289 Q_SCALE := log2Ge_Q 48 23987231289 (by decide)
private theorem u_ge_49 : Log2Ge 49 24114995157 Q_SCALE := log2Ge_Q 49 24114995157 (by decide)
private theorem u_ge_50 : Log2Ge 50 24240177758 Q_SCALE := log2Ge_Q 50 24240177758 (by decide)
private theorem u_ge_51 : Log2Ge 51 24362881332 Q_SCALE := log2Ge_Q 51 24362881332 (by decide)
private theorem u_ge_56 : Log2Ge 56 24942399466 Q_SCALE := log2Ge_Q 56 24942399466 (by decide)
private theorem u_ge_57 : Log2Ge 57 25052071852 Q_SCALE := log2Ge_Q 57 25052071852 (by decide)
private theorem u_ge_58 : Log2Ge 58 25159836794 Q_SCALE := log2Ge_Q 58 25159836794 (by decide)
private theorem u_ge_59 : Log2Ge 59 25265759511 Q_SCALE := log2Ge_Q 59 25265759511 (by decide)
private theorem u_ge_60 : Log2Ge 60 25369901929 Q_SCALE := log2Ge_Q 60 25369901929 (by decide)
private theorem u_ge_61 : Log2Ge 61 25472322905 Q_SCALE := log2Ge_Q 61 25472322905 (by decide)
private theorem u_ge_62 : Log2Ge 62 25573078427 Q_SCALE := log2Ge_Q 62 25573078427 (by decide)
private theorem u_ge_63 : Log2Ge 63 25672221790 Q_SCALE := log2Ge_Q 63 25672221790 (by decide)
private theorem u_ge_69 : Log2Ge 69 26235912768 Q_SCALE := log2Ge_Q 69 26235912768 (by decide)
private theorem u_ge_70 : Log2Ge 70 26325070105 Q_SCALE := log2Ge_Q 70 26325070105 (by decide)
private theorem u_ge_71 : Log2Ge 71 26412962756 Q_SCALE := log2Ge_Q 71 26412962756 (by decide)
private theorem u_ge_72 : Log2Ge 72 26499626099 Q_SCALE := log2Ge_Q 72 26499626099 (by decide)
private theorem u_ge_73 : Log2Ge 73 26585094048 Q_SCALE := log2Ge_Q 73 26585094048 (by decide)
private theorem u_ge_81 : Log2Ge 81 27229448423 Q_SCALE := log2Ge_Q 81 27229448423 (by decide)
private theorem u_ge_82 : Log2Ge 82 27305477942 Q_SCALE := log2Ge_Q 82 27305477942 (by decide)
private theorem u_ge_83 : Log2Ge 83 27380585868 Q_SCALE := log2Ge_Q 83 27380585868 (by decide)
private theorem u_ge_84 : Log2Ge 84 27454794276 Q_SCALE := log2Ge_Q 84 27454794276 (by decide)
private theorem u_ge_87 : Log2Ge 87 27672231604 Q_SCALE := log2Ge_Q 87 27672231604 (by decide)
private theorem u_ge_88 : Log2Ge 88 27743047552 Q_SCALE := log2Ge_Q 88 27743047552 (by decide)
private theorem u_ge_89 : Log2Ge 89 27813063303 Q_SCALE := log2Ge_Q 89 27813063303 (by decide)
private theorem u_ge_90 : Log2Ge 90 27882296739 Q_SCALE := log2Ge_Q 90 27882296739 (by decide)
private theorem u_ge_112 : Log2Ge 112 29237366762 Q_SCALE := log2Ge_Q 112 29237366762 (by decide)
private theorem u_ge_115 : Log2Ge 115 29401155893 Q_SCALE := log2Ge_Q 115 29401155893 (by decide)
private theorem u_ge_116 : Log2Ge 116 29454804090 Q_SCALE := log2Ge_Q 116 29454804090 (by decide)
private theorem u_ge_117 : Log2Ge 117 29507991782 Q_SCALE := log2Ge_Q 117 29507991782 (by decide)
private theorem u_ge_118 : Log2Ge 118 29560726807 Q_SCALE := log2Ge_Q 118 29560726807 (by decide)
private theorem u_ge_119 : Log2Ge 119 29613016805 Q_SCALE := log2Ge_Q 119 29613016805 (by decide)
private theorem u_ge_120 : Log2Ge 120 29664869225 Q_SCALE := log2Ge_Q 120 29664869225 (by decide)
private theorem u_ge_121 : Log2Ge 121 29716291329 Q_SCALE := log2Ge_Q 121 29716291329 (by decide)
private theorem u_ge_150 : Log2Ge 150 31047539864 Q_SCALE := log2Ge_Q 150 31047539864 (by decide)
private theorem u_ge_152 : Log2Ge 152 31129611634 Q_SCALE := log2Ge_Q 152 31129611634 (by decide)
private theorem u_ge_153 : Log2Ge 153 31170243438 Q_SCALE := log2Ge_Q 153 31170243438 (by decide)
private theorem u_ge_170 : Log2Ge 170 31823091753 Q_SCALE := log2Ge_Q 170 31823091753 (by decide)
private theorem u_ge_171 : Log2Ge 171 31859433957 Q_SCALE := log2Ge_Q 171 31859433957 (by decide)
private theorem u_ge_172 : Log2Ge 172 31895564252 Q_SCALE := log2Ge_Q 172 31895564252 (by decide)
private theorem u_ge_173 : Log2Ge 173 31931485095 Q_SCALE := log2Ge_Q 173 31931485095 (by decide)
private theorem u_ge_188 : Log2Ge 188 32446712052 Q_SCALE := log2Ge_Q 188 32446712052 (by decide)
private theorem u_ge_190 : Log2Ge 190 32512282273 Q_SCALE := log2Ge_Q 190 32512282273 (by decide)
private theorem u_ge_191 : Log2Ge 191 32544809004 Q_SCALE := log2Ge_Q 191 32544809004 (by decide)
private theorem u_ge_194 : Log2Ge 194 32641377109 Q_SCALE := log2Ge_Q 194 32641377109 (by decide)
private theorem u_ge_195 : Log2Ge 195 32673234907 Q_SCALE := log2Ge_Q 195 32673234907 (by decide)
private theorem u_ge_226 : Log2Ge 226 33587412892 Q_SCALE := log2Ge_Q 226 33587412892 (by decide)
private theorem u_ge_227 : Log2Ge 227 33614769793 Q_SCALE := log2Ge_Q 227 33614769793 (by decide)
private theorem u_ge_228 : Log2Ge 228 33642006444 Q_SCALE := log2Ge_Q 228 33642006444 (by decide)
private theorem u_ge_229 : Log2Ge 229 33669123896 Q_SCALE := log2Ge_Q 229 33669123896 (by decide)
private theorem u_ge_275 : Log2Ge 275 34803356127 Q_SCALE := log2Ge_Q 275 34803356127 (by decide)
private theorem u_ge_276 : Log2Ge 276 34825847360 Q_SCALE := log2Ge_Q 276 34825847360 (by decide)
private theorem u_ge_277 : Log2Ge 277 34848257251 Q_SCALE := log2Ge_Q 277 34848257251 (by decide)
private theorem u_ge_278 : Log2Ge 278 34870586385 Q_SCALE := log2Ge_Q 278 34870586385 (by decide)
private theorem u_ge_279 : Log2Ge 279 34892835343 Q_SCALE := log2Ge_Q 279 34892835343 (by decide)
private theorem u_ge_339 : Log2Ge 339 36099807702 Q_SCALE := log2Ge_Q 339 36099807702 (by decide)
private theorem u_ge_340 : Log2Ge 340 36118059049 Q_SCALE := log2Ge_Q 340 36118059049 (by decide)
private theorem u_ge_341 : Log2Ge 341 36136256795 Q_SCALE := log2Ge_Q 341 36136256795 (by decide)
private theorem u_ge_342 : Log2Ge 342 36154401253 Q_SCALE := log2Ge_Q 342 36154401253 (by decide)
private theorem u_ge_429 : Log2Ge 429 37558775341 Q_SCALE := log2Ge_Q 429 37558775341 (by decide)
private theorem u_ge_430 : Log2Ge 430 37573202188 Q_SCALE := log2Ge_Q 430 37573202188 (by decide)
private theorem u_ge_431 : Log2Ge 431 37587595523 Q_SCALE := log2Ge_Q 431 37587595523 (by decide)
private theorem u_ge_432 : Log2Ge 432 37601955501 Q_SCALE := log2Ge_Q 432 37601955501 (by decide)
private theorem u_ge_576 : Log2Ge 576 39384527987 Q_SCALE := log2Ge_Q 576 39384527987 (by decide)
private theorem u_ge_577 : Log2Ge 577 39395276174 Q_SCALE := log2Ge_Q 577 39395276174 (by decide)
private theorem u_ge_578 : Log2Ge 578 39406005749 Q_SCALE := log2Ge_Q 578 39406005749 (by decide)
private theorem u_ge_579 : Log2Ge 579 39416716777 Q_SCALE := log2Ge_Q 579 39416716777 (by decide)
private theorem u_ge_836 : Log2Ge 836 41692790002 Q_SCALE := log2Ge_Q 836 41692790002 (by decide)
private theorem u_ge_837 : Log2Ge 837 41700197449 Q_SCALE := log2Ge_Q 837 41700197449 (by decide)
private theorem u_ge_838 : Log2Ge 838 41707596050 Q_SCALE := log2Ge_Q 838 41707596050 (by decide)
private theorem u_ge_839 : Log2Ge 839 41714985828 Q_SCALE := log2Ge_Q 839 41714985828 (by decide)
private theorem u_ge_1125 : Log2Ge 1125 43532539905 Q_SCALE := log2Ge_Q 1125 43532539905 (by decide)
private theorem u_ge_1128 : Log2Ge 1128 43549041454 Q_SCALE := log2Ge_Q 1128 43549041454 (by decide)
private theorem u_ge_1358 : Log2Ge 1358 44698874688 Q_SCALE := log2Ge_Q 1358 44698874688 (by decide)
private theorem u_ge_1359 : Log2Ge 1359 44703435842 Q_SCALE := log2Ge_Q 1359 44703435842 (by decide)
private theorem u_ge_1501 : Log2Ge 1501 45319241900 Q_SCALE := log2Ge_Q 1501 45319241900 (by decide)
private theorem u_ge_1503 : Log2Ge 1503 45327492671 Q_SCALE := log2Ge_Q 1503 45327492671 (by decide)
private theorem u_ge_1504 : Log2Ge 1504 45331613940 Q_SCALE := log2Ge_Q 1504 45331613940 (by decide)
private theorem u_ge_1876 : Log2Ge 1876 46701086858 Q_SCALE := log2Ge_Q 1876 46701086858 (by decide)
private theorem u_ge_1878 : Log2Ge 1878 46707689232 Q_SCALE := log2Ge_Q 1878 46707689232 (by decide)
private theorem u_ge_1879 : Log2Ge 1879 46710987783 Q_SCALE := log2Ge_Q 1879 46710987783 (by decide)
private theorem u_ge_2251 : Log2Ge 2251 47830260513 Q_SCALE := log2Ge_Q 2251 47830260513 (by decide)
private theorem u_ge_2252 : Log2Ge 2252 47833012602 Q_SCALE := log2Ge_Q 2252 47833012602 (by decide)
private theorem u_ge_2253 : Log2Ge 2253 47835763469 Q_SCALE := log2Ge_Q 2253 47835763469 (by decide)
private theorem u_ge_2254 : Log2Ge 2254 47838513115 Q_SCALE := log2Ge_Q 2254 47838513115 (by decide)
private theorem u_ge_2746 : Log2Ge 2746 49061909252 Q_SCALE := log2Ge_Q 2746 49061909252 (by decide)
private theorem u_ge_2747 : Log2Ge 2747 49064165334 Q_SCALE := log2Ge_Q 2747 49064165334 (by decide)
private theorem u_ge_2748 : Log2Ge 2748 49066420594 Q_SCALE := log2Ge_Q 2748 49066420594 (by decide)
private theorem u_ge_2749 : Log2Ge 2749 49068675034 Q_SCALE := log2Ge_Q 2749 49068675034 (by decide)
private theorem u_ge_3376 : Log2Ge 3376 50341737688 Q_SCALE := log2Ge_Q 3376 50341737688 (by decide)
private theorem u_ge_3377 : Log2Ge 3377 50343572822 Q_SCALE := log2Ge_Q 3377 50343572822 (by decide)
private theorem u_ge_3378 : Log2Ge 3378 50345407412 Q_SCALE := log2Ge_Q 3378 50345407412 (by decide)
private theorem u_ge_3379 : Log2Ge 3379 50347241459 Q_SCALE := log2Ge_Q 3379 50347241459 (by decide)
private theorem u_ge_4276 : Log2Ge 4276 51806093684 Q_SCALE := log2Ge_Q 4276 51806093684 (by decide)
private theorem u_ge_4277 : Log2Ge 4277 51807542609 Q_SCALE := log2Ge_Q 4277 51807542609 (by decide)
private theorem u_ge_4278 : Log2Ge 4278 51808991195 Q_SCALE := log2Ge_Q 4278 51808991195 (by decide)
private theorem u_ge_4279 : Log2Ge 4279 51810439443 Q_SCALE := log2Ge_Q 4279 51810439443 (by decide)
private theorem u_ge_5740 : Log2Ge 5740 53630548048 Q_SCALE := log2Ge_Q 5740 53630548048 (by decide)
private theorem u_ge_5741 : Log2Ge 5741 53631627453 Q_SCALE := log2Ge_Q 5741 53631627453 (by decide)
private theorem u_ge_5742 : Log2Ge 5742 53632706671 Q_SCALE := log2Ge_Q 5742 53632706671 (by decide)
private theorem u_ge_5743 : Log2Ge 5743 53633785701 Q_SCALE := log2Ge_Q 5743 53633785701 (by decide)
private theorem u_ge_8328 : Log2Ge 8328 55936599018 Q_SCALE := log2Ge_Q 8328 55936599018 (by decide)
private theorem u_ge_8329 : Log2Ge 8329 55937343009 Q_SCALE := log2Ge_Q 8329 55937343009 (by decide)
private theorem u_ge_8330 : Log2Ge 8330 55938086910 Q_SCALE := log2Ge_Q 8330 55938086910 (by decide)
private theorem u_ge_8331 : Log2Ge 8331 55938830723 Q_SCALE := log2Ge_Q 8331 55938830723 (by decide)
private theorem u_ge_13508 : Log2Ge 13508 58933507414 Q_SCALE := log2Ge_Q 13508 58933507414 (by decide)
private theorem u_ge_13509 : Log2Ge 13509 58933966112 Q_SCALE := log2Ge_Q 13509 58933966112 (by decide)
private theorem u_le_1 : Log2Le 1 0 Q_SCALE := log2Le_Q 1 0 (by decide)
private theorem u_le_2 : Log2Le 2 4294967296 Q_SCALE := log2Le_Q 2 4294967296 (by decide)
private theorem u_le_3 : Log2Le 3 6807362106 Q_SCALE := log2Le_Q 3 6807362106 (by decide)
private theorem u_le_4 : Log2Le 4 8589934592 Q_SCALE := log2Le_Q 4 8589934592 (by decide)
private theorem u_le_5 : Log2Le 5 9972605232 Q_SCALE := log2Le_Q 5 9972605232 (by decide)
private theorem u_le_6 : Log2Le 6 11102329402 Q_SCALE := log2Le_Q 6 11102329402 (by decide)
private theorem u_le_7 : Log2Le 7 12057497579 Q_SCALE := log2Le_Q 7 12057497579 (by decide)
private theorem u_le_8 : Log2Le 8 12884901888 Q_SCALE := log2Le_Q 8 12884901888 (by decide)
private theorem u_le_9 : Log2Le 9 13614724212 Q_SCALE := log2Le_Q 9 13614724212 (by decide)
private theorem u_le_10 : Log2Le 10 14267572528 Q_SCALE := log2Le_Q 10 14267572528 (by decide)
private theorem u_le_11 : Log2Le 11 14858145665 Q_SCALE := log2Le_Q 11 14858145665 (by decide)
private theorem u_le_12 : Log2Le 12 15397296698 Q_SCALE := log2Le_Q 12 15397296698 (by decide)
private theorem u_le_13 : Log2Le 13 15893267571 Q_SCALE := log2Le_Q 13 15893267571 (by decide)
private theorem u_le_14 : Log2Le 14 16352464875 Q_SCALE := log2Le_Q 14 16352464875 (by decide)
private theorem u_le_15 : Log2Le 15 16779967338 Q_SCALE := log2Le_Q 15 16779967338 (by decide)
private theorem u_le_16 : Log2Le 16 17179869184 Q_SCALE := log2Le_Q 16 17179869184 (by decide)
private theorem u_le_17 : Log2Le 17 17555519227 Q_SCALE := log2Le_Q 17 17555519227 (by decide)
private theorem u_le_18 : Log2Le 18 17909691508 Q_SCALE := log2Le_Q 18 17909691508 (by decide)
private theorem u_le_19 : Log2Le 19 18244709747 Q_SCALE := log2Le_Q 19 18244709747 (by decide)
private theorem u_le_20 : Log2Le 20 18562539824 Q_SCALE := log2Le_Q 20 18562539824 (by decide)
private theorem u_le_21 : Log2Le 21 18864859685 Q_SCALE := log2Le_Q 21 18864859685 (by decide)
private theorem u_le_22 : Log2Le 22 19153112961 Q_SCALE := log2Le_Q 22 19153112961 (by decide)
private theorem u_le_23 : Log2Le 23 19428550663 Q_SCALE := log2Le_Q 23 19428550663 (by decide)
private theorem u_le_24 : Log2Le 24 19692263994 Q_SCALE := log2Le_Q 24 19692263994 (by decide)
private theorem u_le_25 : Log2Le 25 19945210463 Q_SCALE := log2Le_Q 25 19945210463 (by decide)
private theorem u_le_26 : Log2Le 26 20188234867 Q_SCALE := log2Le_Q 26 20188234867 (by decide)
private theorem u_le_27 : Log2Le 27 20422086318 Q_SCALE := log2Le_Q 27 20422086318 (by decide)
private theorem u_le_28 : Log2Le 28 20647432171 Q_SCALE := log2Le_Q 28 20647432171 (by decide)
private theorem u_le_29 : Log2Le 29 20864869499 Q_SCALE := log2Le_Q 29 20864869499 (by decide)
private theorem u_le_30 : Log2Le 30 21074934634 Q_SCALE := log2Le_Q 30 21074934634 (by decide)
private theorem u_le_31 : Log2Le 31 21278111132 Q_SCALE := log2Le_Q 31 21278111132 (by decide)
private theorem u_le_32 : Log2Le 32 21474836480 Q_SCALE := log2Le_Q 32 21474836480 (by decide)
private theorem u_le_33 : Log2Le 33 21665507771 Q_SCALE := log2Le_Q 33 21665507771 (by decide)
private theorem u_le_34 : Log2Le 34 21850486523 Q_SCALE := log2Le_Q 34 21850486523 (by decide)
private theorem u_le_35 : Log2Le 35 22030102810 Q_SCALE := log2Le_Q 35 22030102810 (by decide)
private theorem u_le_36 : Log2Le 36 22204658804 Q_SCALE := log2Le_Q 36 22204658804 (by decide)
private theorem u_le_37 : Log2Le 37 22374431836 Q_SCALE := log2Le_Q 37 22374431836 (by decide)
private theorem u_le_38 : Log2Le 38 22539677043 Q_SCALE := log2Le_Q 38 22539677043 (by decide)
private theorem u_le_39 : Log2Le 39 22700629677 Q_SCALE := log2Le_Q 39 22700629677 (by decide)
private theorem u_le_40 : Log2Le 40 22857507120 Q_SCALE := log2Le_Q 40 22857507120 (by decide)
private theorem u_le_41 : Log2Le 41 23010510647 Q_SCALE := log2Le_Q 41 23010510647 (by decide)
private theorem u_le_42 : Log2Le 42 23159826981 Q_SCALE := log2Le_Q 42 23159826981 (by decide)
private theorem u_le_45 : Log2Le 45 23587329444 Q_SCALE := log2Le_Q 45 23587329444 (by decide)
private theorem u_le_46 : Log2Le 46 23723517959 Q_SCALE := log2Le_Q 46 23723517959 (by decide)
private theorem u_le_47 : Log2Le 47 23856777461 Q_SCALE := log2Le_Q 47 23856777461 (by decide)
private theorem u_le_48 : Log2Le 48 23987231290 Q_SCALE := log2Le_Q 48 23987231290 (by decide)
private theorem u_le_49 : Log2Le 49 24114995158 Q_SCALE := log2Le_Q 49 24114995158 (by decide)
private theorem u_le_51 : Log2Le 51 24362881333 Q_SCALE := log2Le_Q 51 24362881333 (by decide)
private theorem u_le_55 : Log2Le 55 24830750897 Q_SCALE := log2Le_Q 55 24830750897 (by decide)
private theorem u_le_56 : Log2Le 56 24942399467 Q_SCALE := log2Le_Q 56 24942399467 (by decide)
private theorem u_le_59 : Log2Le 59 25265759512 Q_SCALE := log2Le_Q 59 25265759512 (by decide)
private theorem u_le_60 : Log2Le 60 25369901930 Q_SCALE := log2Le_Q 60 25369901930 (by decide)
private theorem u_le_63 : Log2Le 63 25672221791 Q_SCALE := log2Le_Q 63 25672221791 (by decide)
private theorem u_le_68 : Log2Le 68 26145453819 Q_SCALE := log2Le_Q 68 26145453819 (by decide)
private theorem u_le_69 : Log2Le 69 26235912769 Q_SCALE := log2Le_Q 69 26235912769 (by decide)
private theorem u_le_70 : Log2Le 70 26325070106 Q_SCALE := log2Le_Q 70 26325070106 (by decide)
private theorem u_le_72 : Log2Le 72 26499626100 Q_SCALE := log2Le_Q 72 26499626100 (by decide)
private theorem u_le_73 : Log2Le 73 26585094049 Q_SCALE := log2Le_Q 73 26585094049 (by decide)
private theorem u_le_80 : Log2Le 80 27152474416 Q_SCALE := log2Le_Q 80 27152474416 (by decide)
private theorem u_le_81 : Log2Le 81 27229448424 Q_SCALE := log2Le_Q 81 27229448424 (by decide)
private theorem u_le_84 : Log2Le 84 27454794277 Q_SCALE := log2Le_Q 84 27454794277 (by decide)
private theorem u_le_86 : Log2Le 86 27600596957 Q_SCALE := log2Le_Q 86 27600596957 (by decide)
private theorem u_le_87 : Log2Le 87 27672231605 Q_SCALE := log2Le_Q 87 27672231605 (by decide)
private theorem u_le_90 : Log2Le 90 27882296740 Q_SCALE := log2Le_Q 90 27882296740 (by decide)
private theorem u_le_111 : Log2Le 111 29181793942 Q_SCALE := log2Le_Q 111 29181793942 (by decide)
private theorem u_le_113 : Log2Le 113 29292445597 Q_SCALE := log2Le_Q 113 29292445597 (by decide)
private theorem u_le_114 : Log2Le 114 29347039149 Q_SCALE := log2Le_Q 114 29347039149 (by decide)
private theorem u_le_115 : Log2Le 115 29401155894 Q_SCALE := log2Le_Q 115 29401155894 (by decide)
private theorem u_le_116 : Log2Le 116 29454804091 Q_SCALE := log2Le_Q 116 29454804091 (by decide)
private theorem u_le_117 : Log2Le 117 29507991783 Q_SCALE := log2Le_Q 117 29507991783 (by decide)
private theorem u_le_118 : Log2Le 118 29560726808 Q_SCALE := log2Le_Q 118 29560726808 (by decide)
private theorem u_le_120 : Log2Le 120 29664869226 Q_SCALE := log2Le_Q 120 29664869226 (by decide)
private theorem u_le_121 : Log2Le 121 29716291330 Q_SCALE := log2Le_Q 121 29716291330 (by decide)
private theorem u_le_149 : Log2Le 149 31006092700 Q_SCALE := log2Le_Q 149 31006092700 (by decide)
private theorem u_le_152 : Log2Le 152 31129611635 Q_SCALE := log2Le_Q 152 31129611635 (by decide)
private theorem u_le_153 : Log2Le 153 31170243439 Q_SCALE := log2Le_Q 153 31170243439 (by decide)
private theorem u_le_169 : Log2Le 169 31786535141 Q_SCALE := log2Le_Q 169 31786535141 (by decide)
private theorem u_le_170 : Log2Le 170 31823091754 Q_SCALE := log2Le_Q 170 31823091754 (by decide)
private theorem u_le_173 : Log2Le 173 31931485096 Q_SCALE := log2Le_Q 173 31931485096 (by decide)
private theorem u_le_187 : Log2Le 187 32413664892 Q_SCALE := log2Le_Q 187 32413664892 (by decide)
private theorem u_le_190 : Log2Le 190 32512282274 Q_SCALE := log2Le_Q 190 32512282274 (by decide)
private theorem u_le_191 : Log2Le 191 32544809005 Q_SCALE := log2Le_Q 191 32544809005 (by decide)
private theorem u_le_225 : Log2Le 225 33559934675 Q_SCALE := log2Le_Q 225 33559934675 (by decide)
private theorem u_le_226 : Log2Le 226 33587412893 Q_SCALE := log2Le_Q 226 33587412893 (by decide)
private theorem u_le_228 : Log2Le 228 33642006445 Q_SCALE := log2Le_Q 228 33642006445 (by decide)
private theorem u_le_229 : Log2Le 229 33669123897 Q_SCALE := log2Le_Q 229 33669123897 (by decide)
private theorem u_le_274 : Log2Le 274 34780782959 Q_SCALE := log2Le_Q 274 34780782959 (by decide)
private theorem u_le_275 : Log2Le 275 34803356128 Q_SCALE := log2Le_Q 275 34803356128 (by decide)
private theorem u_le_278 : Log2Le 278 34870586386 Q_SCALE := log2Le_Q 278 34870586386 (by decide)
private theorem u_le_338 : Log2Le 338 36081502437 Q_SCALE := log2Le_Q 338 36081502437 (by decide)
private theorem u_le_339 : Log2Le 339 36099807703 Q_SCALE := log2Le_Q 339 36099807703 (by decide)
private theorem u_le_342 : Log2Le 342 36154401254 Q_SCALE := log2Le_Q 342 36154401254 (by decide)
private theorem u_le_428 : Log2Le 428 37544314826 Q_SCALE := log2Le_Q 428 37544314826 (by decide)
private theorem u_le_429 : Log2Le 429 37558775342 Q_SCALE := log2Le_Q 429 37558775342 (by decide)
private theorem u_le_432 : Log2Le 432 37601955502 Q_SCALE := log2Le_Q 432 37601955502 (by decide)
private theorem u_le_575 : Log2Le 575 39373761126 Q_SCALE := log2Le_Q 575 39373761126 (by decide)
private theorem u_le_576 : Log2Le 576 39384527988 Q_SCALE := log2Le_Q 576 39384527988 (by decide)
private theorem u_le_579 : Log2Le 579 39416716778 Q_SCALE := log2Le_Q 579 39416716778 (by decide)
private theorem u_le_835 : Log2Le 835 41685373691 Q_SCALE := log2Le_Q 835 41685373691 (by decide)
private theorem u_le_836 : Log2Le 836 41692790003 Q_SCALE := log2Le_Q 836 41692790003 (by decide)
private theorem u_le_839 : Log2Le 839 41714985829 Q_SCALE := log2Le_Q 839 41714985829 (by decide)
private theorem u_le_1124 : Log2Le 1124 43527029610 Q_SCALE := log2Le_Q 1124 43527029610 (by decide)
private theorem u_le_1127 : Log2Le 1127 43543545820 Q_SCALE := log2Le_Q 1127 43543545820 (by decide)
private theorem u_le_1128 : Log2Le 1128 43549041455 Q_SCALE := log2Le_Q 1128 43549041455 (by decide)
private theorem u_le_1355 : Log2Le 1355 44685171046 Q_SCALE := log2Le_Q 1355 44685171046 (by decide)
private theorem u_le_1500 : Log2Le 1500 45315112392 Q_SCALE := log2Le_Q 1500 45315112392 (by decide)
private theorem u_le_1503 : Log2Le 1503 45327492672 Q_SCALE := log2Le_Q 1503 45327492672 (by decide)
private theorem u_le_1504 : Log2Le 1504 45331613941 Q_SCALE := log2Le_Q 1504 45331613941 (by decide)
private theorem u_le_1875 : Log2Le 1875 46697783031 Q_SCALE := log2Le_Q 1875 46697783031 (by decide)
private theorem u_le_1878 : Log2Le 1878 46707689233 Q_SCALE := log2Le_Q 1878 46707689233 (by decide)
private theorem u_le_1879 : Log2Le 1879 46710987784 Q_SCALE := log2Le_Q 1879 46710987784 (by decide)
private theorem u_le_2250 : Log2Le 2250 47827507202 Q_SCALE := log2Le_Q 2250 47827507202 (by decide)
private theorem u_le_2251 : Log2Le 2251 47830260514 Q_SCALE := log2Le_Q 2251 47830260514 (by decide)
private theorem u_le_2253 : Log2Le 2253 47835763470 Q_SCALE := log2Le_Q 2253 47835763470 (by decide)
private theorem u_le_2254 : Log2Le 2254 47838513116 Q_SCALE := log2Le_Q 2254 47838513116 (by decide)
private theorem u_le_2745 : Log2Le 2745 49059652350 Q_SCALE := log2Le_Q 2745 49059652350 (by decide)
private theorem u_le_2746 : Log2Le 2746 49061909253 Q_SCALE := log2Le_Q 2746 49061909253 (by decide)
private theorem u_le_2749 : Log2Le 2749 49068675035 Q_SCALE := log2Le_Q 2749 49068675035 (by decide)
private theorem u_le_3375 : Log2Le 3375 50339902012 Q_SCALE := log2Le_Q 3375 50339902012 (by decide)
private theorem u_le_3376 : Log2Le 3376 50341737689 Q_SCALE := log2Le_Q 3376 50341737689 (by decide)
private theorem u_le_3379 : Log2Le 3379 50347241460 Q_SCALE := log2Le_Q 3379 50347241460 (by decide)
private theorem u_le_4275 : Log2Le 4275 51804644421 Q_SCALE := log2Le_Q 4275 51804644421 (by decide)
private theorem u_le_4276 : Log2Le 4276 51806093685 Q_SCALE := log2Le_Q 4276 51806093685 (by decide)
private theorem u_le_4279 : Log2Le 4279 51810439444 Q_SCALE := log2Le_Q 4279 51810439444 (by decide)
private theorem u_le_5739 : Log2Le 5739 53629468455 Q_SCALE := log2Le_Q 5739 53629468455 (by decide)
private theorem u_le_5740 : Log2Le 5740 53630548049 Q_SCALE := log2Le_Q 5740 53630548049 (by decide)
private theorem u_le_5743 : Log2Le 5743 53633785702 Q_SCALE := log2Le_Q 5743 53633785702 (by decide)
private theorem u_le_8327 : Log2Le 8327 55935854939 Q_SCALE := log2Le_Q 8327 55935854939 (by decide)
private theorem u_le_8328 : Log2Le 8328 55936599019 Q_SCALE := log2Le_Q 8328 55936599019 (by decide)
private theorem u_le_8331 : Log2Le 8331 55938830724 Q_SCALE := log2Le_Q 8331 55938830724 (by decide)
private theorem u_le_13505 : Log2Le 13505 58932131115 Q_SCALE := log2Le_Q 13505 58932131115 (by decide)

/-! ### Exact universal `c_min` lower bounds across ALL `(c, d, k) ∈ ℕ³` -/

theorem universal_c_min_2807 {c d k : Nat} (hV : ValidPassTriple 2807 1000 c d k) :
    3 ≤ c :=
  universal_c_min_of_log2 (by decide) hV (by decide) (by decide) (by decide) (by decide)
    u_le_4 u_le_1 u_ge_2 (by decide)

theorem universal_c_min_2800 {c d k : Nat} (hV : ValidPassTriple 14 5 c d k) :
    3 ≤ c :=
  universal_c_min_of_log2 (by decide) hV (by decide) (by decide) (by decide) (by decide)
    u_le_4 u_le_1 u_ge_2 (by decide)

theorem universal_c_min_2695 {c d k : Nat} (hV : ValidPassTriple 539 200 c d k) :
    3 ≤ c :=
  universal_c_min_of_log2 (by decide) hV (by decide) (by decide) (by decide) (by decide)
    u_le_4 u_le_1 u_ge_2 (by decide)

theorem universal_c_min_2500 {c d k : Nat} (hV : ValidPassTriple 5 2 c d k) :
    5 ≤ c :=
  universal_c_min_of_log2 (by decide) hV (by decide) (by decide) (by decide) (by decide)
    u_le_6 u_le_3 u_ge_4 (by decide)

theorem universal_c_min_2371 {c d k : Nat} (hV : ValidPassTriple 2371 1000 c d k) :
    10 ≤ c :=
  universal_c_min_of_log2 (by decide) hV (by decide) (by decide) (by decide) (by decide)
    u_le_11 u_le_8 u_ge_9 (by decide)

theorem universal_c_min_2321 {c d k : Nat} (hV : ValidPassTriple 2321 1000 c d k) :
    17 ≤ c :=
  universal_c_min_of_log2 (by decide) hV (by decide) (by decide) (by decide) (by decide)
    u_le_18 u_le_15 u_ge_16 (by decide)

theorem universal_c_min_2300 {c d k : Nat} (hV : ValidPassTriple 23 10 c d k) :
    23 ≤ c :=
  universal_c_min_of_log2 (by decide) hV (by decide) (by decide) (by decide) (by decide)
    u_le_24 u_le_21 u_ge_22 (by decide)

theorem universal_c_min_2260 {c d k : Nat} (hV : ValidPassTriple 113 50 c d k) :
    113 ≤ c :=
  universal_c_min_of_log2 (by decide) hV (by decide) (by decide) (by decide) (by decide)
    u_le_114 u_le_111 u_ge_112 (by decide)

theorem universal_c_min_2251 {c d k : Nat} (hV : ValidPassTriple 2251 1000 c d k) :
    1126 ≤ c :=
  universal_c_min_of_log2 (by decide) hV (by decide) (by decide) (by decide) (by decide)
    u_le_1127 u_le_1124 u_ge_1125 (by decide)

/-- Combined summary of exact universal `c_min` lower bounds for all 8 paper targets. -/
theorem universal_c_min_all :
    (∀ c d k, ValidPassTriple 14 5 c d k → 3 ≤ c) ∧
    (∀ c d k, ValidPassTriple 539 200 c d k → 3 ≤ c) ∧
    (∀ c d k, ValidPassTriple 5 2 c d k → 5 ≤ c) ∧
    (∀ c d k, ValidPassTriple 2371 1000 c d k → 10 ≤ c) ∧
    (∀ c d k, ValidPassTriple 2321 1000 c d k → 17 ≤ c) ∧
    (∀ c d k, ValidPassTriple 23 10 c d k → 23 ≤ c) ∧
    (∀ c d k, ValidPassTriple 113 50 c d k → 113 ≤ c) ∧
    (∀ c d k, ValidPassTriple 2251 1000 c d k → 1126 ≤ c) :=
  ⟨fun _ _ _ h => universal_c_min_2800 h,
   fun _ _ _ h => universal_c_min_2695 h,
   fun _ _ _ h => universal_c_min_2500 h,
   fun _ _ _ h => universal_c_min_2371 h,
   fun _ _ _ h => universal_c_min_2321 h,
   fun _ _ _ h => universal_c_min_2300 h,
   fun _ _ _ h => universal_c_min_2260 h,
   fun _ _ _ h => universal_c_min_2251 h⟩


/-! ### Completely universal Pre-Bini (`v_k`) and Post-Bini (`V = v_k^h`) lower bounds -/

private theorem universal_both_2807 {c d k : Nat} (hV : ValidPassTriple 2807 1000 c d k) :
    10 ^ 5909 < v_k_pass c d k ∧
    (∀ h, ValidPostBini 2807 1000 c d k h → 10 ^ 633063 < (v_k_pass c d k) ^ h) := by
  have hc_min : 3 ≤ c := universal_c_min_2807 hV
  have hd_pos : 1 ≤ d := hV.2.1
  refine if hb0 : c ≤ 3 then ?_ else if hb1 : c ≤ 4 then ?_ else if hb2 : c ≤ 5 then ?_ else if hb3 : c ≤ 6 then ?_ else if hb4 : c ≤ 7 then ?_ else if hb5 : c ≤ 9 then ?_ else if hb6 : c ≤ 12 then ?_ else if hb7 : c ≤ 18 then ?_ else if hb8 : c ≤ 30 then ?_ else ?_
  · have hd_lb : RoundBound Q_SCALE 2807 1000 1473522213956 d → 133 ≤ d := by
      intro hr
      have hd0 : 34 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 101 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 35) (a := 17) (s := 1) (by decide) u_ge_17) (by decide)
      have hd2 : 127 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 102) (a := 25) (s := 2) (by decide) u_ge_25) (by decide)
      have hd3 : 133 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 128) (a := 16) (s := 3) (by decide) u_ge_16) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 3) (c_hi := 3) (c_g := 3) (G := 1473522213956) (d_lb := 133) (ld_lb := 30064771072) (pen_Q := 261168334) (Lw := 19684042128) (k_lb0 := 45) (BL := 0) (S := 5677637935) (R := 932869966757172381479730494602766360776975) (k_lb := 45) (M_pre := 5909) (M_post := 633063)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb0
      (f_mono_inc_range 2807 1000 c 3 (by omega) hb0 (by decide) (by decide)) u_le_5 u_le_2 u_ge_3 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 134) (a := 16) (s := 3) (by decide) u_ge_16).mono_exp (by decide)) u_ge_5 (by decide)
      ((log2Le_of_mul_two_pow (x := 268) (b := 17) (s := 4) (by decide) u_le_17).mono_exp (by decide)) (by decide) (by decide)
      (fun _ => cb_zero Q_SCALE c k (by omega)) u_le_2 u_ge_5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2807 1000 2439365150680 d → 71 ≤ d := by
      intro hr
      have hd0 : 21 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 55 ≤ d := d_boot hr hd0 u_ge_22 (by decide)
      have hd2 : 68 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 56) (a := 28) (s := 1) (by decide) u_ge_28) (by decide)
      have hd3 : 71 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 69) (a := 17) (s := 2) (by decide) u_ge_17) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 4) (c_hi := 4) (c_g := 4) (G := 2439365150680) (d_lb := 71) (ld_lb := 26499626099) (pen_Q := 433726668) (Lw := 21770932134) (k_lb0 := 30) (BL := 2512394808) (S := 4294967295) (R := 884019081994175696124386757542546077302891) (k_lb := 36) (M_pre := 5909) (M_post := 633063)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb1
      (f_mono_inc_range 2807 1000 c 4 (by omega) hb1 (by decide) (by decide)) u_le_6 u_le_3 u_ge_4 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 72) (a := 18) (s := 2) (by decide) u_ge_18).mono_exp (by decide)) u_ge_6 (by decide)
      ((log2Le_of_mul_two_pow (x := 144) (b := 18) (s := 3) (by decide) u_le_18).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 4) (c_hi := 4) (by decide) (by omega) hb1 (by omega) u_ge_3 u_le_6 u_ge_3 (by decide)) u_le_3 u_ge_6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2807 1000 2603793361344 d → 66 ≤ d := by
      intro hr
      have hd0 : 20 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 51 ≤ d := d_boot hr hd0 u_ge_21 (by decide)
      have hd2 : 63 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 52) (a := 26) (s := 1) (by decide) u_ge_26) (by decide)
      have hd3 : 66 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 64) (a := 16) (s := 2) (by decide) u_ge_16) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 5) (c_hi := 5) (c_g := 5) (G := 2603793361344) (d_lb := 66) (ld_lb := 25769803776) (pen_Q := 461218502) (Lw := 23653776654) (k_lb0 := 30) (BL := 3339799118) (S := 3467562986) (R := 806921022790669868889274676240414023751468) (k_lb := 38) (M_pre := 5909) (M_post := 633063)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb2
      (f_mono_inc_range 2807 1000 c 5 (by omega) hb2 (by decide) (by decide)) u_le_7 u_le_4 u_ge_5 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 67) (a := 16) (s := 2) (by decide) u_ge_16).mono_exp (by decide)) u_ge_7 (by decide)
      ((log2Le_of_mul_two_pow (x := 134) (b := 17) (s := 3) (by decide) u_le_17).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 5) (c_hi := 5) (by decide) (by omega) hb2 (by omega) u_ge_3 u_le_7 u_ge_4 (by decide)) u_le_4 u_ge_7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2807 1000 2540943948036 d → 68 ≤ d := by
      intro hr
      have hd0 : 20 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 52 ≤ d := d_boot hr hd0 u_ge_21 (by decide)
      have hd2 : 65 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 53) (a := 26) (s := 1) (by decide) u_ge_26) (by decide)
      have hd3 : 68 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 66) (a := 16) (s := 2) (by decide) u_ge_16) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 6) (c_hi := 6) (c_g := 6) (G := 2540943948036) (d_lb := 68) (ld_lb := 26145453818) (pen_Q := 452861668) (Lw := 25316942108) (k_lb0 := 33) (BL := 3895065448) (S := 2912296656) (R := 760064378478989476548422258742700159314469) (k_lb := 42) (M_pre := 5909) (M_post := 633063)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb3
      (f_mono_dec_range 2807 1000 6 c (by decide) (by omega) (by decide) (by decide)) u_le_8 u_le_5 u_ge_6 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 69) (a := 17) (s := 2) (by decide) u_ge_17).mono_exp (by decide)) u_ge_8 (by decide)
      ((log2Le_of_mul_two_pow (x := 138) (b := 18) (s := 3) (by decide) u_le_18).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 6) (c_hi := 6) (by decide) (by omega) hb3 (by omega) u_ge_3 u_le_8 u_ge_5 (by decide)) u_le_5 u_ge_8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2807 1000 2410171786552 d → 72 ≤ d := by
      intro hr
      have hd0 : 21 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 56 ≤ d := d_boot hr hd0 u_ge_22 (by decide)
      have hd2 : 69 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 57) (a := 28) (s := 1) (by decide) u_ge_28) (by decide)
      have hd3 : 72 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 70) (a := 17) (s := 2) (by decide) u_ge_17) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 7) (c_hi := 7) (c_g := 7) (G := 2410171786552) (d_lb := 72) (ld_lb := 26499626099) (pen_Q := 432355718) (Lw := 26797092704) (k_lb0 := 37) (BL := 4947815609) (S := 2512394809) (R := 738883061750619277171761921263660780975577) (k_lb := 49) (M_pre := 5909) (M_post := 633063)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb4
      (f_mono_dec_range 2807 1000 7 c (by decide) (by omega) (by decide) (by decide)) u_le_9 u_le_6 u_ge_7 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 73) (a := 18) (s := 2) (by decide) u_ge_18).mono_exp (by decide)) u_ge_9 (by decide)
      ((log2Le_of_mul_two_pow (x := 146) (b := 19) (s := 3) (by decide) u_le_19).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 7) (c_hi := 7) (by decide) (by omega) hb4 (by omega) u_ge_5 u_le_9 u_ge_6 (by decide)) u_le_6 u_ge_9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2807 1000 2264176251920 d → 78 ≤ d := by
      intro hr
      have hd0 : 23 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 61 ≤ d := d_boot hr hd0 u_ge_24 (by decide)
      have hd2 : 75 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 62) (a := 31) (s := 1) (by decide) u_ge_31) (by decide)
      have hd3 : 78 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 76) (a := 19) (s := 2) (by decide) u_ge_19) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 8) (c_hi := 9) (c_g := 8) (G := 2264176251920) (d_lb := 78) (ld_lb := 26834644338) (pen_Q := 403172330) (Lw := 28131972724) (k_lb0 := 42) (BL := 5552455331) (S := 1973243776) (R := 641402004858298840000271703920978197830424) (k_lb := 56) (M_pre := 5909) (M_post := 633063)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb5
      (f_mono_dec_range 2807 1000 8 c (by decide) (by omega) (by decide) (by decide)) u_le_10 u_le_7 u_ge_8 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 79) (a := 19) (s := 2) (by decide) u_ge_19).mono_exp (by decide)) u_ge_10 (by decide)
      ((log2Le_of_mul_two_pow (x := 158) (b := 20) (s := 3) (by decide) u_le_20).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 8) (c_hi := 9) (by decide) (by omega) hb5 (by omega) u_ge_5 u_le_10 u_ge_7 (by decide)) u_le_8 u_ge_11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2807 1000 1989108075988 d → 92 ≤ d := by
      intro hr
      have hd0 : 26 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 71 ≤ d := d_boot hr hd0 u_ge_27 (by decide)
      have hd2 : 88 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 72) (a := 18) (s := 2) (by decide) u_ge_18) (by decide)
      have hd3 : 92 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 89) (a := 22) (s := 2) (by decide) u_ge_22) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 10) (c_hi := 12) (c_g := 10) (G := 1989108075988) (d_lb := 92) (ld_lb := 28018485254) (pen_Q := 354099630) (Lw := 30440493764) (k_lb0 := 51) (BL := 6709780117) (S := 1494319209) (R := 573630256929771283060129134261950853507220) (k_lb := 72) (M_pre := 5909) (M_post := 633063)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb6
      (f_mono_dec_range 2807 1000 10 c (by decide) (by omega) (by decide) (by decide)) u_le_12 u_le_9 u_ge_10 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 93) (a := 23) (s := 2) (by decide) u_ge_23).mono_exp (by decide)) u_ge_12 (by decide)
      ((log2Le_of_mul_two_pow (x := 186) (b := 24) (s := 3) (by decide) u_le_24).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 10) (c_hi := 12) (by decide) (by omega) hb6 (by omega) u_ge_7 u_le_12 u_ge_9 (by decide)) u_le_11 u_ge_14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2807 1000 1659841155104 d → 114 ≤ d := by
      intro hr
      have hd0 : 31 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 89 ≤ d := d_boot hr hd0 u_ge_32 (by decide)
      have hd2 : 110 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 90) (a := 22) (s := 2) (by decide) u_ge_22) (by decide)
      have hd3 : 114 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 111) (a := 27) (s := 2) (by decide) u_ge_27) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 13) (c_hi := 18) (c_g := 13) (G := 1659841155104) (d_lb := 114) (ld_lb := 29237366762) (pen_Q := 296050627) (Lw := 33263884047) (k_lb0 := 67) (BL := 7230353224) (S := 1007020596) (R := 453382951067372053741073231240262168007164) (k_lb := 93) (M_pre := 5909) (M_post := 633063)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb7
      (f_mono_dec_range 2807 1000 13 c (by decide) (by omega) (by decide) (by decide)) u_le_15 u_le_12 u_ge_13 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 115) (a := 28) (s := 2) (by decide) u_ge_28).mono_exp (by decide)) u_ge_15 (by decide)
      ((log2Le_of_mul_two_pow (x := 230) (b := 29) (s := 3) (by decide) u_le_29).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 13) (by decide) (by omega) (by omega) u_ge_9 log2Le_22 (by decide)) u_le_17 u_ge_20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2807 1000 1232034453092 d → 163 ≤ d := by
      intro hr
      have hd0 : 41 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 127 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 42) (a := 21) (s := 1) (by decide) u_ge_21) (by decide)
      have hd2 : 158 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 128) (a := 16) (s := 3) (by decide) u_ge_16) (by decide)
      have hd3 : 163 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 159) (a := 19) (s := 3) (by decide) u_ge_19) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 19) (c_hi := 30) (c_g := 19) (G := 1232034453092) (d_lb := 163) (ld_lb := 31447441711) (pen_Q := 221133306) (Lw := 37508586062) (k_lb0 := 103) (BL := 9508896583) (S := 609966981) (R := 357650659582972136766144838787255268301231) (k_lb := 149) (M_pre := 5909) (M_post := 633063)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb8
      (f_mono_dec_range 2807 1000 19 c (by decide) (by omega) (by decide) (by decide)) u_le_21 u_le_18 u_ge_19 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 164) (a := 20) (s := 3) (by decide) u_ge_20).mono_exp (by decide)) u_ge_21 (by decide)
      ((log2Le_of_mul_two_pow (x := 328) (b := 21) (s := 4) (by decide) u_le_21).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 19) (by decide) (by omega) (by omega) u_ge_13 log2Le_22 (by decide)) u_le_29 u_ge_32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : TailRoundBound Q_SCALE 2807 1000 (3 * (4 * 2807 - 9 * 1000) * Q_SCALE) c d → 232 ≤ d := by
      intro hr
      have hd0 : 54 ≤ d := tail_d_boot (c_lo := 31) (by omega) hr hd_pos u_ge_2 (by decide)
      have hd1 : 178 ≤ d := tail_d_boot (c_lo := 31) (by omega) hr hd0 (log2Ge_of_mul_two_pow (x := 55) (a := 27) (s := 1) (by decide) u_ge_27) (by decide)
      have hd2 : 223 ≤ d := tail_d_boot (c_lo := 31) (by omega) hr hd1 (log2Ge_of_mul_two_pow (x := 179) (a := 22) (s := 3) (by decide) u_ge_22) (by decide)
      have hd3 : 232 ≤ d := tail_d_boot (c_lo := 31) (by omega) hr hd2 (log2Ge_of_mul_two_pow (x := 224) (a := 28) (s := 3) (by decide) u_ge_28) (by decide)
      exact hd3
    exact tail_step_of_log2 (Q := Q_SCALE) (c_lo := 31) (d_lb := 232) (ld_lb := 33749771386) (pen_Q := 164891396) (Lw := 43166124144) (BL := 12480488697) (k_lb := 238) (M_pre := 5909) (M_post := 633063)
      (by decide) hV (by decide) (by decide) (by decide) (by omega) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 233) (a := 29) (s := 3) (by decide) u_ge_29).mono_exp (by decide)) u_ge_33 (by decide)
      ((log2Le_of_mul_two_pow (x := 466) (b := 30) (s := 4) (by decide) u_le_30).mono_exp (by decide)) (by decide)
      (fun c' k' hc' hk' => tail_cb_univ (p := 2807) (q := 1000) (Lw := 43166124144) (c_lo := 31) (by decide) hc' hk' (by decide) (by decide) u_ge_21 log2Le_22 (by decide)) (by decide) (by decide) (by decide) (by decide)

theorem universal_vk_lb_2807 {c d k : Nat} (hV : ValidPassTriple 2807 1000 c d k) :
    10 ^ 5909 < v_k_pass c d k :=
  (universal_both_2807 hV).1

theorem universal_post_bini_lb_2807 {c d k h : Nat} (hPB : ValidPostBini 2807 1000 c d k h) :
    10 ^ 633063 < (v_k_pass c d k) ^ h :=
  (universal_both_2807 hPB.1).2 h hPB

private theorem universal_both_2800 {c d k : Nat} (hV : ValidPassTriple 14 5 c d k) :
    10 ^ 6153 < v_k_pass c d k ∧
    (∀ h, ValidPostBini 14 5 c d k h → 10 ^ 689132 < (v_k_pass c d k) ^ h) := by
  have hc_min : 3 ≤ c := universal_c_min_2800 hV
  have hd_pos : 1 ≤ d := hV.2.1
  refine if hb0 : c ≤ 3 then ?_ else if hb1 : c ≤ 4 then ?_ else if hb2 : c ≤ 5 then ?_ else if hb3 : c ≤ 6 then ?_ else if hb4 : c ≤ 7 then ?_ else if hb5 : c ≤ 9 then ?_ else if hb6 : c ≤ 12 then ?_ else if hb7 : c ≤ 18 then ?_ else if hb8 : c ≤ 30 then ?_ else ?_
  · have hd_lb : RoundBound Q_SCALE 14 5 6924477032 d → 142 ≤ d := by
      intro hr
      have hd0 : 36 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 109 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 37) (a := 18) (s := 1) (by decide) u_ge_18) (by decide)
      have hd2 : 136 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 110) (a := 27) (s := 2) (by decide) u_ge_27) (by decide)
      have hd3 : 142 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 137) (a := 17) (s := 3) (by decide) u_ge_17) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 3) (c_hi := 3) (c_g := 3) (G := 6924477032) (d_lb := 142) (ld_lb := 30440421114) (pen_Q := 247109583) (Lw := 19698100879) (k_lb0 := 48) (BL := 0) (S := 5677637935) (R := 117797246640559933392629285313251479) (k_lb := 48) (M_pre := 6153) (M_post := 689132)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb0
      (f_mono_inc_range 14 5 c 3 (by omega) hb0 (by decide) (by decide)) u_le_5 u_le_2 u_ge_3 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 143) (a := 17) (s := 3) (by decide) u_ge_17).mono_exp (by decide)) u_ge_5 (by decide)
      ((log2Le_of_mul_two_pow (x := 286) (b := 18) (s := 4) (by decide) u_le_18).mono_exp (by decide)) (by decide) (by decide)
      (fun _ => cb_zero Q_SCALE c k (by omega)) u_le_2 u_ge_5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 14 5 11845090480 d → 74 ≤ d := by
      intro hr
      have hd0 : 22 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 57 ≤ d := d_boot hr hd0 u_ge_23 (by decide)
      have hd2 : 71 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 58) (a := 29) (s := 1) (by decide) u_ge_29) (by decide)
      have hd3 : 74 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 72) (a := 18) (s := 2) (by decide) u_ge_18) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 4) (c_hi := 4) (c_g := 4) (G := 11845090480) (d_lb := 74) (ld_lb := 26499626099) (pen_Q := 420670428) (Lw := 21783988374) (k_lb0 := 31) (BL := 2512394808) (S := 4294967295) (R := 110374331825781293168510926505354000) (k_lb := 37) (M_pre := 6153) (M_post := 689132)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb1
      (f_mono_inc_range 14 5 c 4 (by omega) hb1 (by decide) (by decide)) u_le_6 u_le_3 u_ge_4 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 75) (a := 18) (s := 2) (by decide) u_ge_18).mono_exp (by decide)) u_ge_6 (by decide)
      ((log2Le_of_mul_two_pow (x := 150) (b := 19) (s := 3) (by decide) u_le_19).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 4) (c_hi := 4) (by decide) (by omega) hb1 (by omega) u_ge_3 u_le_6 u_ge_3 (by decide)) u_le_3 u_ge_6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 14 5 12727081878 d → 67 ≤ d := by
      intro hr
      have hd0 : 20 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 52 ≤ d := d_boot hr hd0 u_ge_21 (by decide)
      have hd2 : 64 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 53) (a := 26) (s := 1) (by decide) u_ge_26) (by decide)
      have hd3 : 67 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 65) (a := 16) (s := 2) (by decide) u_ge_16) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 5) (c_hi := 5) (c_g := 5) (G := 12727081878) (d_lb := 67) (ld_lb := 26145453818) (pen_Q := 454334644) (Lw := 23660660512) (k_lb0 := 31) (BL := 3339799118) (S := 3467562986) (R := 101961668360143111804856802003761391) (k_lb := 39) (M_pre := 6153) (M_post := 689132)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb2
      (f_mono_inc_range 14 5 c 5 (by omega) hb2 (by decide) (by decide)) u_le_7 u_le_4 u_ge_5 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 68) (a := 17) (s := 2) (by decide) u_ge_17).mono_exp (by decide)) u_ge_7 (by decide)
      ((log2Le_of_mul_two_pow (x := 136) (b := 17) (s := 3) (by decide) u_le_17).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 5) (c_hi := 5) (by decide) (by omega) hb2 (by omega) u_ge_3 u_le_7 u_ge_4 (by decide)) u_le_4 u_ge_7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 14 5 12455159592 d → 69 ≤ d := by
      intro hr
      have hd0 : 21 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 54 ≤ d := d_boot hr hd0 u_ge_22 (by decide)
      have hd2 : 66 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 55) (a := 27) (s := 1) (by decide) u_ge_27) (by decide)
      have hd3 : 69 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 67) (a := 16) (s := 2) (by decide) u_ge_16) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 6) (c_hi := 6) (c_g := 6) (G := 12455159592) (d_lb := 69) (ld_lb := 26145453818) (pen_Q := 446298456) (Lw := 25323505320) (k_lb0 := 34) (BL := 3895065448) (S := 2912296656) (R := 94861612548563092220605510255107130) (k_lb := 43) (M_pre := 6153) (M_post := 689132)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb3
      (f_mono_dec_range 14 5 6 c (by decide) (by omega) (by decide) (by decide)) u_le_8 u_le_5 u_ge_6 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 70) (a := 17) (s := 2) (by decide) u_ge_17).mono_exp (by decide)) u_ge_8 (by decide)
      ((log2Le_of_mul_two_pow (x := 140) (b := 18) (s := 3) (by decide) u_le_18).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 6) (c_hi := 6) (by decide) (by omega) hb3 (by omega) u_ge_3 u_le_8 u_ge_5 (by decide)) u_le_5 u_ge_8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 14 5 11832847204 d → 74 ≤ d := by
      intro hr
      have hd0 : 22 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 57 ≤ d := d_boot hr hd0 u_ge_23 (by decide)
      have hd2 : 71 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 58) (a := 29) (s := 1) (by decide) u_ge_29) (by decide)
      have hd3 : 74 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 72) (a := 18) (s := 2) (by decide) u_ge_18) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 7) (c_hi := 7) (c_g := 7) (G := 11832847204) (d_lb := 74) (ld_lb := 26499626099) (pen_Q := 420670428) (Lw := 26808777994) (k_lb0 := 38) (BL := 4947815609) (S := 2512394809) (R := 92223381220036439192468878426427370) (k_lb := 51) (M_pre := 6153) (M_post := 689132)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb4
      (f_mono_dec_range 14 5 7 c (by decide) (by omega) (by decide) (by decide)) u_le_9 u_le_6 u_ge_7 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 75) (a := 18) (s := 2) (by decide) u_ge_18).mono_exp (by decide)) u_ge_9 (by decide)
      ((log2Le_of_mul_two_pow (x := 150) (b := 19) (s := 3) (by decide) u_le_19).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 7) (c_hi := 7) (by decide) (by omega) hb4 (by omega) u_ge_5 u_le_9 u_ge_6 (by decide)) u_le_6 u_ge_9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 14 5 11127307370 d → 80 ≤ d := by
      intro hr
      have hd0 : 23 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 62 ≤ d := d_boot hr hd0 u_ge_24 (by decide)
      have hd2 : 76 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 63) (a := 31) (s := 1) (by decide) u_ge_31) (by decide)
      have hd3 : 80 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 77) (a := 19) (s := 2) (by decide) u_ge_19) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 8) (c_hi := 9) (c_g := 8) (G := 11127307370) (d_lb := 80) (ld_lb := 27152474415) (pen_Q := 396872020) (Lw := 28138273034) (k_lb0 := 42) (BL := 5552455331) (S := 1973243776) (R := 80830936024395738483404283682894654) (k_lb := 57) (M_pre := 6153) (M_post := 689132)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb5
      (f_mono_dec_range 14 5 8 c (by decide) (by omega) (by decide) (by decide)) u_le_10 u_le_7 u_ge_8 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 81) (a := 20) (s := 2) (by decide) u_ge_20).mono_exp (by decide)) u_ge_10 (by decide)
      ((log2Le_of_mul_two_pow (x := 162) (b := 21) (s := 3) (by decide) u_le_21).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 8) (c_hi := 9) (by decide) (by omega) hb5 (by omega) u_ge_5 u_le_10 u_ge_7 (by decide)) u_le_8 u_ge_11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 14 5 9787378996 d → 93 ≤ d := by
      intro hr
      have hd0 : 26 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 72 ≤ d := d_boot hr hd0 u_ge_27 (by decide)
      have hd2 : 89 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 73) (a := 18) (s := 2) (by decide) u_ge_18) (by decide)
      have hd3 : 93 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 90) (a := 22) (s := 2) (by decide) u_ge_22) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 10) (c_hi := 12) (c_g := 10) (G := 9787378996) (d_lb := 93) (ld_lb := 28018485254) (pen_Q := 350292107) (Lw := 30444301287) (k_lb0 := 52) (BL := 6709780117) (S := 1494319209) (R := 71548234891620153420677894298969419) (k_lb := 73) (M_pre := 6153) (M_post := 689132)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb6
      (f_mono_dec_range 14 5 10 c (by decide) (by omega) (by decide) (by decide)) u_le_12 u_le_9 u_ge_10 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 94) (a := 23) (s := 2) (by decide) u_ge_23).mono_exp (by decide)) u_ge_12 (by decide)
      ((log2Le_of_mul_two_pow (x := 188) (b := 24) (s := 3) (by decide) u_le_24).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 10) (c_hi := 12) (by decide) (by omega) hb6 (by omega) u_ge_7 u_le_12 u_ge_9 (by decide)) u_le_11 u_ge_14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 14 5 8175067808 d → 116 ≤ d := by
      intro hr
      have hd0 : 31 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 90 ≤ d := d_boot hr hd0 u_ge_32 (by decide)
      have hd2 : 111 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 91) (a := 22) (s := 2) (by decide) u_ge_22) (by decide)
      have hd3 : 116 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 112) (a := 28) (s := 2) (by decide) u_ge_28) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 13) (c_hi := 18) (c_g := 13) (G := 8175067808) (d_lb := 116) (ld_lb := 29454804090) (pen_Q := 292757212) (Lw := 33267177462) (k_lb0 := 69) (BL := 7230353224) (S := 1007020596) (R := 56895704560630728243258324295322444) (k_lb := 95) (M_pre := 6153) (M_post := 689132)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb7
      (f_mono_dec_range 14 5 13 c (by decide) (by omega) (by decide) (by decide)) u_le_15 u_le_12 u_ge_13 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 117) (a := 29) (s := 2) (by decide) u_ge_29).mono_exp (by decide)) u_ge_15 (by decide)
      ((log2Le_of_mul_two_pow (x := 234) (b := 30) (s := 3) (by decide) u_le_30).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 13) (by decide) (by omega) (by omega) u_ge_9 log2Le_22 (by decide)) u_le_17 u_ge_20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 14 5 6073351274 d → 167 ≤ d := by
      intro hr
      have hd0 : 42 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 128 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 43) (a := 21) (s := 1) (by decide) u_ge_21) (by decide)
      have hd2 : 160 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 129) (a := 16) (s := 3) (by decide) u_ge_16) (by decide)
      have hd3 : 167 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 161) (a := 20) (s := 3) (by decide) u_ge_20) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 19) (c_hi := 30) (c_g := 19) (G := 6073351274) (d_lb := 167) (ld_lb := 31749761572) (pen_Q := 215836700) (Lw := 37513882668) (k_lb0 := 105) (BL := 9508896583) (S := 609966981) (R := 44956022258967394265158945965385726) (k_lb := 151) (M_pre := 6153) (M_post := 689132)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb8
      (f_mono_dec_range 14 5 19 c (by decide) (by omega) (by decide) (by decide)) u_le_21 u_le_18 u_ge_19 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 168) (a := 21) (s := 3) (by decide) u_ge_21).mono_exp (by decide)) u_ge_21 (by decide)
      ((log2Le_of_mul_two_pow (x := 336) (b := 21) (s := 4) (by decide) u_le_21).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 19) (by decide) (by omega) (by omega) u_ge_13 log2Le_22 (by decide)) u_le_29 u_ge_32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : TailRoundBound Q_SCALE 14 5 (3 * (4 * 14 - 9 * 5) * Q_SCALE) c d → 234 ≤ d := by
      intro hr
      have hd0 : 55 ≤ d := tail_d_boot (c_lo := 31) (by omega) hr hd_pos u_ge_2 (by decide)
      have hd1 : 181 ≤ d := tail_d_boot (c_lo := 31) (by omega) hr hd0 (log2Ge_of_mul_two_pow (x := 56) (a := 28) (s := 1) (by decide) u_ge_28) (by decide)
      have hd2 : 225 ≤ d := tail_d_boot (c_lo := 31) (by omega) hr hd1 (log2Ge_of_mul_two_pow (x := 182) (a := 22) (s := 3) (by decide) u_ge_22) (by decide)
      have hd3 : 234 ≤ d := tail_d_boot (c_lo := 31) (by omega) hr hd2 (log2Ge_of_mul_two_pow (x := 226) (a := 28) (s := 3) (by decide) u_ge_28) (by decide)
      exact hd3
    exact tail_step_of_log2 (Q := Q_SCALE) (c_lo := 31) (d_lb := 234) (ld_lb := 33749771386) (pen_Q := 163482068) (Lw := 43167533472) (BL := 12480488697) (k_lb := 242) (M_pre := 6153) (M_post := 689132)
      (by decide) hV (by decide) (by decide) (by decide) (by omega) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 235) (a := 29) (s := 3) (by decide) u_ge_29).mono_exp (by decide)) u_ge_33 (by decide)
      ((log2Le_of_mul_two_pow (x := 470) (b := 30) (s := 4) (by decide) u_le_30).mono_exp (by decide)) (by decide)
      (fun c' k' hc' hk' => tail_cb_univ (p := 14) (q := 5) (Lw := 43167533472) (c_lo := 31) (by decide) hc' hk' (by decide) (by decide) u_ge_21 log2Le_22 (by decide)) (by decide) (by decide) (by decide) (by decide)

theorem universal_vk_lb_2800 {c d k : Nat} (hV : ValidPassTriple 14 5 c d k) :
    10 ^ 6153 < v_k_pass c d k :=
  (universal_both_2800 hV).1

theorem universal_post_bini_lb_2800 {c d k h : Nat} (hPB : ValidPostBini 14 5 c d k h) :
    10 ^ 689132 < (v_k_pass c d k) ^ h :=
  (universal_both_2800 hPB.1).2 h hPB

private theorem universal_both_2695 {c d k : Nat} (hV : ValidPassTriple 539 200 c d k) :
    10 ^ 12816 < v_k_pass c d k ∧
    (∀ h, ValidPostBini 539 200 c d k h → 10 ^ 2442630 < (v_k_pass c d k) ^ h) := by
  have hc_min : 3 ≤ c := universal_c_min_2695 hV
  have hd_pos : 1 ≤ d := hV.2.1
  refine if hb0 : c ≤ 3 then ?_ else if hb1 : c ≤ 4 then ?_ else if hb2 : c ≤ 5 then ?_ else if hb3 : c ≤ 6 then ?_ else if hb4 : c ≤ 7 then ?_ else if hb5 : c ≤ 9 then ?_ else if hb6 : c ≤ 11 then ?_ else if hb7 : c ≤ 15 then ?_ else if hb8 : c ≤ 22 then ?_ else if hb9 : c ≤ 36 then ?_ else ?_
  · have hd_lb : RoundBound Q_SCALE 539 200 11098658612 d → 5635 ≤ d := by
      intro hr
      have hd0 : 882 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 4534 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 883) (a := 27) (s := 5) (by decide) u_ge_27) (by decide)
      have hd2 : 5507 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 4535) (a := 17) (s := 8) (by decide) u_ge_17) (by decide)
      have hd3 : 5635 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 5508) (a := 21) (s := 8) (by decide) u_ge_21) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 3) (c_hi := 3) (c_g := 3) (G := 11098658612) (d_lb := 5635) (ld_lb := 53512851328) (pen_Q := 10307588) (Lw := 19934902874) (k_lb0 := 1296) (BL := 0) (S := 5677637935) (R := 12349579212545544456218008535412963156746) (k_lb := 1296) (M_pre := 12816) (M_post := 2442630)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb0
      (f_mono_inc_range 539 200 c 3 (by omega) hb0 (by decide) (by decide)) u_le_5 u_le_2 u_ge_3 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 5636) (a := 22) (s := 8) (by decide) u_ge_22).mono_exp (by decide)) u_ge_5 (by decide)
      ((log2Le_of_mul_two_pow (x := 11272) (b := 23) (s := 9) (by decide) u_le_23).mono_exp (by decide)) (by decide) (by decide)
      (fun _ => cb_zero Q_SCALE c k (by omega)) u_le_2 u_ge_5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 539 200 262762455160 d → 145 ≤ d := by
      intro hr
      have hd0 : 38 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 113 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 39) (a := 19) (s := 1) (by decide) u_ge_19) (by decide)
      have hd2 : 140 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 114) (a := 28) (s := 2) (by decide) u_ge_28) (by decide)
      have hd3 : 145 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 141) (a := 17) (s := 3) (by decide) u_ge_17) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 4) (c_hi := 4) (c_g := 4) (G := 262762455160) (d_lb := 145) (ld_lb := 30794593395) (pen_Q := 244307441) (Lw := 21960351361) (k_lb0 := 60) (BL := 2512394808) (S := 4294967295) (R := 7876734179761905723218164093013918154410) (k_lb := 71) (M_pre := 12816) (M_post := 2442630)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb1
      (f_mono_inc_range 539 200 c 4 (by omega) hb1 (by decide) (by decide)) u_le_6 u_le_3 u_ge_4 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 146) (a := 18) (s := 3) (by decide) u_ge_18).mono_exp (by decide)) u_ge_6 (by decide)
      ((log2Le_of_mul_two_pow (x := 292) (b := 19) (s := 4) (by decide) u_le_19).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 4) (c_hi := 4) (by decide) (by omega) hb1 (by omega) u_ge_3 u_le_6 u_ge_3 (by decide)) u_le_3 u_ge_6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 539 200 333952317888 d → 109 ≤ d := by
      intro hr
      have hd0 : 30 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 85 ≤ d := d_boot hr hd0 u_ge_31 (by decide)
      have hd2 : 105 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 86) (a := 21) (s := 2) (by decide) u_ge_21) (by decide)
      have hd3 : 109 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 106) (a := 26) (s := 2) (by decide) u_ge_26) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 5) (c_hi := 5) (c_g := 5) (G := 333952317888) (d_lb := 109) (ld_lb := 29012020909) (pen_Q := 307636093) (Lw := 23807359063) (k_lb0 := 51) (BL := 3339799118) (S := 3467562986) (R := 6972953954730279491387210223109519872245) (k_lb := 63) (M_pre := 12816) (M_post := 2442630)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb2
      (f_mono_inc_range 539 200 c 5 (by omega) hb2 (by decide) (by decide)) u_le_7 u_le_4 u_ge_5 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 110) (a := 27) (s := 2) (by decide) u_ge_27).mono_exp (by decide)) u_ge_7 (by decide)
      ((log2Le_of_mul_two_pow (x := 220) (b := 28) (s := 3) (by decide) u_le_28).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 5) (c_hi := 5) (by decide) (by omega) hb2 (by omega) u_ge_3 u_le_7 u_ge_4 (by decide)) u_le_4 u_ge_7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 539 200 348470294772 d → 104 ≤ d := by
      intro hr
      have hd0 : 29 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 80 ≤ d := d_boot hr hd0 u_ge_30 (by decide)
      have hd2 : 99 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 81) (a := 20) (s := 2) (by decide) u_ge_20) (by decide)
      have hd3 : 104 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 100) (a := 25) (s := 2) (by decide) u_ge_25) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 6) (c_hi := 6) (c_g := 6) (G := 348470294772) (d_lb := 104) (ld_lb := 28778169458) (pen_Q := 320259502) (Lw := 25449544274) (k_lb0 := 52) (BL := 3895065448) (S := 2912296656) (R := 6433059908676833048509796836458301303840) (k_lb := 66) (M_pre := 12816) (M_post := 2442630)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb3
      (f_mono_inc_range 539 200 c 6 (by omega) hb3 (by decide) (by decide)) u_le_8 u_le_5 u_ge_6 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 105) (a := 26) (s := 2) (by decide) u_ge_26).mono_exp (by decide)) u_ge_8 (by decide)
      ((log2Le_of_mul_two_pow (x := 210) (b := 27) (s := 3) (by decide) u_le_27).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 6) (c_hi := 6) (by decide) (by omega) hb3 (by omega) u_ge_3 u_le_8 u_ge_5 (by decide)) u_le_5 u_ge_8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 539 200 342506850904 d → 105 ≤ d := by
      intro hr
      have hd0 : 29 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 82 ≤ d := d_boot hr hd0 u_ge_30 (by decide)
      have hd2 : 101 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 83) (a := 20) (s := 2) (by decide) u_ge_20) (by decide)
      have hd3 : 105 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 102) (a := 25) (s := 2) (by decide) u_ge_25) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 7) (c_hi := 7) (c_g := 7) (G := 342506850904) (d_lb := 105) (ld_lb := 28778169458) (pen_Q := 317209412) (Lw := 26912239010) (k_lb0 := 56) (BL := 4947815609) (S := 2512394809) (R := 6170833180651028429899060530877676386107) (k_lb := 74) (M_pre := 12816) (M_post := 2442630)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb4
      (f_mono_dec_range 539 200 7 c (by decide) (by omega) (by decide) (by decide)) u_le_9 u_le_6 u_ge_7 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 106) (a := 26) (s := 2) (by decide) u_ge_26).mono_exp (by decide)) u_ge_9 (by decide)
      ((log2Le_of_mul_two_pow (x := 212) (b := 27) (s := 3) (by decide) u_le_27).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 7) (c_hi := 7) (by decide) (by omega) hb4 (by omega) u_ge_5 u_le_9 u_ge_6 (by decide)) u_le_6 u_ge_9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 539 200 328947961040 d → 110 ≤ d := by
      intro hr
      have hd0 : 30 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 86 ≤ d := d_boot hr hd0 u_ge_31 (by decide)
      have hd2 : 106 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 87) (a := 21) (s := 2) (by decide) u_ge_21) (by decide)
      have hd3 : 110 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 107) (a := 26) (s := 2) (by decide) u_ge_26) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 8) (c_hi := 9) (c_g := 8) (G := 328947961040) (d_lb := 110) (ld_lb := 29012020909) (pen_Q := 304839401) (Lw := 28230305653) (k_lb0 := 61) (BL := 5552455331) (S := 1973243776) (R := 5310112364539991623419275632516621500671) (k_lb := 82) (M_pre := 12816) (M_post := 2442630)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb5
      (f_mono_dec_range 539 200 8 c (by decide) (by omega) (by decide) (by decide)) u_le_10 u_le_7 u_ge_8 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 111) (a := 27) (s := 2) (by decide) u_ge_27).mono_exp (by decide)) u_ge_10 (by decide)
      ((log2Le_of_mul_two_pow (x := 222) (b := 28) (s := 3) (by decide) u_le_28).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 8) (c_hi := 9) (by decide) (by omega) hb5 (by omega) u_ge_5 u_le_10 u_ge_7 (by decide)) u_le_8 u_ge_11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 539 200 296598329476 d → 126 ≤ d := by
      intro hr
      have hd0 : 33 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 97 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 34) (a := 17) (s := 1) (by decide) u_ge_17) (by decide)
      have hd2 : 121 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 98) (a := 24) (s := 2) (by decide) u_ge_24) (by decide)
      have hd3 : 126 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 122) (a := 30) (s := 2) (by decide) u_ge_30) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 10) (c_hi := 11) (c_g := 10) (G := 296598329476) (d_lb := 126) (ld_lb := 29868045723) (pen_Q := 272696337) (Lw := 30521897057) (k_lb0 := 74) (BL := 6709780117) (S := 1625695042) (R := 5034634947429082537374740163974011016949) (k_lb := 101) (M_pre := 12816) (M_post := 2442630)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb6
      (f_mono_dec_range 539 200 10 c (by decide) (by omega) (by decide) (by decide)) u_le_12 u_le_9 u_ge_10 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 127) (a := 31) (s := 2) (by decide) u_ge_31).mono_exp (by decide)) u_ge_12 (by decide)
      ((log2Le_of_mul_two_pow (x := 254) (b := 32) (s := 3) (by decide) u_le_32).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 10) (c_hi := 11) (by decide) (by omega) hb6 (by omega) u_ge_7 u_le_12 u_ge_9 (by decide)) u_le_10 u_ge_13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 539 200 266159539768 d → 143 ≤ d := by
      intro hr
      have hd0 : 37 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 111 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 38) (a := 19) (s := 1) (by decide) u_ge_19) (by decide)
      have hd2 : 138 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 112) (a := 28) (s := 2) (by decide) u_ge_28) (by decide)
      have hd3 : 143 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 139) (a := 17) (s := 3) (by decide) u_ge_17) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 12) (c_hi := 15) (c_g := 12) (G := 266159539768) (d_lb := 143) (ld_lb := 30794593395) (pen_Q := 245381544) (Lw := 32459548204) (k_lb0 := 88) (BL := 6080220734) (S := 1203054351) (R := 4018227025575422962262687973691608207377) (k_lb := 115) (M_pre := 12816) (M_post := 2442630)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb7
      (f_mono_dec_range 539 200 12 c (by decide) (by omega) (by decide) (by decide)) u_le_14 u_le_11 u_ge_12 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 144) (a := 18) (s := 3) (by decide) u_ge_18).mono_exp (by decide)) u_ge_14 (by decide)
      ((log2Le_of_mul_two_pow (x := 288) (b := 18) (s := 4) (by decide) u_le_18).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 12) (c_hi := 15) (by decide) (by omega) hb7 (by omega) u_ge_7 u_le_14 u_ge_11 (by decide)) u_le_14 u_ge_17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 539 200 217827926544 d → 183 ≤ d := by
      intro hr
      have hd0 : 45 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 142 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 46) (a := 23) (s := 1) (by decide) u_ge_23) (by decide)
      have hd2 : 175 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 143) (a := 17) (s := 3) (by decide) u_ge_17) (by decide)
      have hd3 : 183 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 176) (a := 22) (s := 3) (by decide) u_ge_22) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 16) (c_hi := 22) (c_g := 16) (G := 217827926544) (d_lb := 183) (ld_lb := 32313452550) (pen_Q := 200046011) (Lw := 35619337003) (k_lb0 := 118) (BL := 8473774677) (S := 827404308) (R := 3436218977121005365672742160974378792583) (k_lb := 164) (M_pre := 12816) (M_post := 2442630)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb8
      (f_mono_dec_range 539 200 16 c (by decide) (by omega) (by decide) (by decide)) u_le_18 u_le_15 u_ge_16 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 184) (a := 23) (s := 3) (by decide) u_ge_23).mono_exp (by decide)) u_ge_18 (by decide)
      ((log2Le_of_mul_two_pow (x := 368) (b := 23) (s := 4) (by decide) u_le_23).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 16) (by decide) (by omega) (by omega) u_ge_11 log2Le_22 (by decide)) u_le_21 u_ge_24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 539 200 163401528556 d → 257 ≤ d := by
      intro hr
      have hd0 : 60 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 199 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 61) (a := 30) (s := 1) (by decide) u_ge_30) (by decide)
      have hd2 : 249 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 200) (a := 25) (s := 3) (by decide) u_ge_25) (by decide)
      have hd3 : 257 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 250) (a := 31) (s := 3) (by decide) u_ge_31) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 23) (c_hi := 36) (c_g := 23) (G := 163401528556) (d_lb := 257) (ld_lb := 34359738368) (pen_Q := 151869089) (Lw := 39738551835) (k_lb0 := 175) (BL := 10395596350) (S := 509574232) (R := 2640647642347401342913261308824060318622) (k_lb := 251) (M_pre := 12816) (M_post := 2442630)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb9
      (f_mono_dec_range 539 200 23 c (by decide) (by omega) (by decide) (by decide)) u_le_25 u_le_22 u_ge_23 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 258) (a := 16) (s := 4) (by decide) u_ge_16).mono_exp (by decide)) u_ge_25 (by decide)
      ((log2Le_of_mul_two_pow (x := 516) (b := 17) (s := 5) (by decide) u_le_17).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 23) (by decide) (by omega) (by omega) u_ge_15 log2Le_22 (by decide)) u_le_35 u_ge_38 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : TailRoundBound Q_SCALE 539 200 (3 * (4 * 539 - 9 * 200) * Q_SCALE) c d → 355 ≤ d := by
      intro hr
      have hd0 : 79 ≤ d := tail_d_boot (c_lo := 37) (by omega) hr hd_pos u_ge_2 (by decide)
      have hd1 : 278 ≤ d := tail_d_boot (c_lo := 37) (by omega) hr hd0 (log2Ge_of_mul_two_pow (x := 80) (a := 20) (s := 2) (by decide) u_ge_20) (by decide)
      have hd2 : 344 ≤ d := tail_d_boot (c_lo := 37) (by omega) hr hd1 (log2Ge_of_mul_two_pow (x := 279) (a := 17) (s := 4) (by decide) u_ge_17) (by decide)
      have hd3 : 355 ≤ d := tail_d_boot (c_lo := 37) (by omega) hr hd2 (log2Ge_of_mul_two_pow (x := 345) (a := 21) (s := 4) (by decide) u_ge_21) (by decide)
      exact hd3
    exact tail_step_of_log2 (Q := Q_SCALE) (c_lo := 37) (d_lb := 355) (ld_lb := 36332982144) (pen_Q := 115220809) (Lw := 45286038543) (BL := 13560839475) (k_lb := 394) (M_pre := 12816) (M_post := 2442630)
      (by decide) hV (by decide) (by decide) (by decide) (by omega) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 356) (a := 22) (s := 4) (by decide) u_ge_22).mono_exp (by decide)) u_ge_39 (by decide)
      ((log2Le_of_mul_two_pow (x := 712) (b := 23) (s := 5) (by decide) u_le_23).mono_exp (by decide)) (by decide)
      (fun c' k' hc' hk' => tail_cb_univ (p := 539) (q := 200) (Lw := 45286038543) (c_lo := 37) (by decide) hc' hk' (by decide) (by decide) u_ge_25 log2Le_22 (by decide)) (by decide) (by decide) (by decide) (by decide)

theorem universal_vk_lb_2695 {c d k : Nat} (hV : ValidPassTriple 539 200 c d k) :
    10 ^ 12816 < v_k_pass c d k :=
  (universal_both_2695 hV).1

theorem universal_post_bini_lb_2695 {c d k h : Nat} (hPB : ValidPostBini 539 200 c d k h) :
    10 ^ 2442630 < (v_k_pass c d k) ^ h :=
  (universal_both_2695 hPB.1).2 h hPB

private theorem universal_both_2500 {c d k : Nat} (hV : ValidPassTriple 5 2 c d k) :
    10 ^ 100884 < v_k_pass c d k ∧
    (∀ h, ValidPostBini 5 2 c d k h → 10 ^ 64498444 < (v_k_pass c d k) ^ h) := by
  have hc_min : 5 ≤ c := universal_c_min_2500 hV
  have hd_pos : 1 ≤ d := hV.2.1
  refine if hb0 : c ≤ 6 then ?_ else if hb1 : c ≤ 8 then ?_ else if hb2 : c ≤ 10 then ?_ else if hb3 : c ≤ 12 then ?_ else if hb4 : c ≤ 15 then ?_ else if hb5 : c ≤ 19 then ?_ else if hb6 : c ≤ 25 then ?_ else if hb7 : c ≤ 37 then ?_ else if hb8 : c ≤ 60 then ?_ else ?_
  · have hd_lb : RoundBound Q_SCALE 5 2 703889868 d → 638 ≤ d := by
      intro hr
      have hd0 : 135 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 506 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 136) (a := 17) (s := 3) (by decide) u_ge_17) (by decide)
      have hd2 : 620 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 507) (a := 31) (s := 4) (by decide) u_ge_31) (by decide)
      have hd3 : 638 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 621) (a := 19) (s := 5) (by decide) u_ge_19) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 5) (c_hi := 6) (c_g := 6) (G := 703889868) (d_lb := 638) (ld_lb := 39719546226) (pen_Q := 69486432) (Lw := 24045508724) (k_lb0 := 273) (BL := 3339799118) (S := 2912296656) (R := 7438260779671009103513979608100782) (k_lb := 330) (M_pre := 100884) (M_post := 64498444)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb0
      (f_mono_inc_range 5 2 c 6 (by omega) hb0 (by decide) (by decide)) u_le_8 u_le_5 u_ge_6 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 639) (a := 19) (s := 5) (by decide) u_ge_19).mono_exp (by decide)) u_ge_7 (by decide)
      ((log2Le_of_mul_two_pow (x := 1278) (b := 20) (s := 6) (by decide) u_le_20).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 5) (c_hi := 6) (by decide) (by omega) hb0 (by omega) u_ge_3 u_le_7 u_ge_4 (by decide)) u_le_5 u_ge_8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 5 2 1132513412 d → 367 ≤ d := by
      intro hr
      have hd0 : 84 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 288 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 85) (a := 21) (s := 2) (by decide) u_ge_21) (by decide)
      have hd2 : 356 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 289) (a := 18) (s := 4) (by decide) u_ge_18) (by decide)
      have hd3 : 367 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 357) (a := 22) (s := 4) (by decide) u_ge_22) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 7) (c_hi := 8) (c_g := 8) (G := 1132513412) (d_lb := 367) (ld_lb := 36608419846) (pen_Q := 111453371) (Lw := 27117995051) (k_lb0 := 191) (BL := 4947815609) (S := 2210074948) (R := 6374547227955346952815671755407971) (k_lb := 243) (M_pre := 100884) (M_post := 64498444)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb1
      (f_mono_inc_range 5 2 c 8 (by omega) hb1 (by decide) (by decide)) u_le_10 u_le_7 u_ge_8 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 368) (a := 23) (s := 4) (by decide) u_ge_23).mono_exp (by decide)) u_ge_9 (by decide)
      ((log2Le_of_mul_two_pow (x := 736) (b := 23) (s := 5) (by decide) u_le_23).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 7) (c_hi := 8) (by decide) (by omega) hb1 (by omega) u_ge_5 u_le_9 u_ge_6 (by decide)) u_le_7 u_ge_10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 5 2 1203613588 d → 340 ≤ d := by
      intro hr
      have hd0 : 79 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 269 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 80) (a := 20) (s := 2) (by decide) u_ge_20) (by decide)
      have hd2 : 329 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 270) (a := 16) (s := 4) (by decide) u_ge_16) (by decide)
      have hd3 : 340 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 330) (a := 20) (s := 4) (by decide) u_ge_20) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 9) (c_hi := 10) (c_g := 10) (G := 1203613588) (d_lb := 340) (ld_lb := 36044728868) (pen_Q := 119493969) (Lw := 29596797359) (k_lb0 := 196) (BL := 4052873900) (S := 1782572485) (R := 5310948954851594565739549022388275) (k_lb := 237) (M_pre := 100884) (M_post := 64498444)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb2
      (f_mono_inc_range 5 2 c 10 (by omega) hb2 (by decide) (by decide)) u_le_12 u_le_9 u_ge_10 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 341) (a := 21) (s := 4) (by decide) u_ge_21).mono_exp (by decide)) u_ge_11 (by decide)
      ((log2Le_of_mul_two_pow (x := 682) (b := 22) (s := 5) (by decide) u_le_22).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 9) (c_hi := 10) (by decide) (by omega) hb2 (by omega) u_ge_5 u_le_11 u_ge_8 (by decide)) u_le_9 u_ge_12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 5 2 1194097624 d → 346 ≤ d := by
      intro hr
      have hd0 : 80 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 271 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 81) (a := 20) (s := 2) (by decide) u_ge_20) (by decide)
      have hd2 : 335 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 272) (a := 17) (s := 4) (by decide) u_ge_17) (by decide)
      have hd3 : 346 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 336) (a := 21) (s := 4) (by decide) u_ge_21) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 11) (c_hi := 12) (c_g := 11) (G := 1194097624) (d_lb := 346) (ld_lb := 36044728868) (pen_Q := 117421820) (Lw := 31669113320) (k_lb0 := 212) (BL := 7180412446) (S := 1494319209) (R := 5329553554928400743224951011881214) (k_lb := 284) (M_pre := 100884) (M_post := 64498444)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb3
      (f_mono_dec_range 5 2 11 c (by decide) (by omega) (by decide) (by decide)) u_le_13 u_le_10 u_ge_11 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 347) (a := 21) (s := 4) (by decide) u_ge_21).mono_exp (by decide)) u_ge_13 (by decide)
      ((log2Le_of_mul_two_pow (x := 694) (b := 22) (s := 5) (by decide) u_le_22).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 11) (c_hi := 12) (by decide) (by omega) hb3 (by omega) u_ge_7 u_le_13 u_ge_10 (by decide)) u_le_11 u_ge_14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 5 2 1141947680 d → 361 ≤ d := by
      intro hr
      have hd0 : 83 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 286 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 84) (a := 21) (s := 2) (by decide) u_ge_21) (by decide)
      have hd2 : 350 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 287) (a := 17) (s := 4) (by decide) u_ge_17) (by decide)
      have hd3 : 361 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 351) (a := 21) (s := 4) (by decide) u_ge_21) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 13) (c_hi := 15) (c_g := 13) (G := 1141947680) (d_lb := 361) (ld_lb := 36332982144) (pen_Q := 113305782) (Lw := 33446628892) (k_lb0 := 234) (BL := 8084041647) (S := 1203054351) (R := 4686688661691887144145965855386555) (k_lb := 319) (M_pre := 100884) (M_post := 64498444)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb4
      (f_mono_dec_range 5 2 13 c (by decide) (by omega) (by decide) (by decide)) u_le_15 u_le_12 u_ge_13 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 362) (a := 22) (s := 4) (by decide) u_ge_22).mono_exp (by decide)) u_ge_15 (by decide)
      ((log2Le_of_mul_two_pow (x := 724) (b := 23) (s := 5) (by decide) u_le_23).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 13) (c_hi := 15) (by decide) (by omega) hb4 (by omega) u_ge_9 u_le_15 u_ge_12 (by decide)) u_le_14 u_ge_17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 5 2 1039756440 d → 405 ≤ d := by
      intro hr
      have hd0 : 91 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 320 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 92) (a := 23) (s := 2) (by decide) u_ge_23) (by decide)
      have hd2 : 394 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 321) (a := 20) (s := 4) (by decide) u_ge_20) (by decide)
      have hd3 : 405 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 395) (a := 24) (s := 4) (by decide) u_ge_24) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 16) (c_hi := 19) (c_g := 16) (G := 1039756440) (d_lb := 405) (ld_lb := 37125079646) (pen_Q := 102871782) (Lw := 35716511232) (k_lb0 := 274) (BL := 8473774677) (S := 955168176) (R := 4069047652726078140120584181898456) (k_lb := 372) (M_pre := 100884) (M_post := 64498444)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb5
      (f_mono_dec_range 5 2 16 c (by decide) (by omega) (by decide) (by decide)) u_le_18 u_le_15 u_ge_16 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 406) (a := 25) (s := 4) (by decide) u_ge_25).mono_exp (by decide)) u_ge_18 (by decide)
      ((log2Le_of_mul_two_pow (x := 812) (b := 26) (s := 5) (by decide) u_le_26).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 16) (by decide) (by omega) (by omega) u_ge_11 log2Le_22 (by decide)) u_le_18 u_ge_21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 5 2 910624192 d → 472 ≤ d := by
      intro hr
      have hd0 : 104 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 373 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 105) (a := 26) (s := 2) (by decide) u_ge_26) (by decide)
      have hd2 : 459 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 374) (a := 23) (s := 4) (by decide) u_ge_23) (by decide)
      have hd3 : 472 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 460) (a := 28) (s := 4) (by decide) u_ge_28) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 20) (c_hi := 25) (c_g := 20) (G := 910624192) (d_lb := 472) (ld_lb := 38044738682) (pen_Q := 90147821) (Lw := 38216078099) (k_lb0 := 335) (BL := 9508896583) (S := 729822323) (R := 3477921473313848147759801351827577) (k_lb := 461) (M_pre := 100884) (M_post := 64498444)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb6
      (f_mono_dec_range 5 2 20 c (by decide) (by omega) (by decide) (by decide)) u_le_22 u_le_19 u_ge_20 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 473) (a := 29) (s := 4) (by decide) u_ge_29).mono_exp (by decide)) u_ge_22 (by decide)
      ((log2Le_of_mul_two_pow (x := 946) (b := 30) (s := 5) (by decide) u_le_30).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 20) (by decide) (by omega) (by omega) u_ge_13 log2Le_22 (by decide)) u_le_24 u_ge_27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 5 2 757285604 d → 584 ≤ d := by
      intro hr
      have hd0 : 125 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 463 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 126) (a := 31) (s := 2) (by decide) u_ge_31) (by decide)
      have hd2 : 571 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 464) (a := 29) (s := 4) (by decide) u_ge_29) (by decide)
      have hd3 : 584 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 572) (a := 17) (s := 5) (by decide) u_ge_17) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 26) (c_hi := 37) (c_g := 26) (G := 757285604) (d_lb := 584) (ld_lb := 39384527987) (pen_Q := 75367318) (Lw := 41219497022) (k_lb0 := 435) (BL := 11171148239) (S := 495970872) (R := 2738479782558157572688924073371941) (k_lb := 612) (M_pre := 100884) (M_post := 64498444)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb7
      (f_mono_dec_range 5 2 26 c (by decide) (by omega) (by decide) (by decide)) u_le_28 u_le_25 u_ge_26 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 585) (a := 18) (s := 5) (by decide) u_ge_18).mono_exp (by decide)) u_ge_28 (by decide)
      ((log2Le_of_mul_two_pow (x := 1170) (b := 19) (s := 6) (by decide) u_le_19).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 26) (by decide) (by omega) (by omega) u_ge_17 log2Le_22 (by decide)) u_le_36 u_ge_39 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 5 2 559698152 d → 833 ≤ d := by
      intro hr
      have hd0 : 169 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 660 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 170) (a := 21) (s := 3) (by decide) u_ge_21) (by decide)
      have hd2 : 808 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 661) (a := 20) (s := 5) (by decide) u_ge_20) (by decide)
      have hd3 : 833 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 809) (a := 25) (s := 5) (by decide) u_ge_25) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 38) (c_hi := 60) (c_g := 38) (G := 559698152) (d_lb := 833) (ld_lb := 41663071346) (pen_Q := 55452450) (Lw := 45659561788) (k_lb0 := 652) (BL := 13560839475) (S := 307318915) (R := 2065185612898207007548391449192379) (k_lb := 943) (M_pre := 100884) (M_post := 64498444)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb8
      (f_mono_dec_range 5 2 38 c (by decide) (by omega) (by decide) (by decide)) u_le_40 u_le_37 u_ge_38 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 834) (a := 26) (s := 5) (by decide) u_ge_26).mono_exp (by decide)) u_ge_40 (by decide)
      ((log2Le_of_mul_two_pow (x := 1668) (b := 27) (s := 6) (by decide) u_le_27).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 38) (by decide) (by omega) (by omega) u_ge_25 log2Le_22 (by decide)) u_le_59 u_ge_62 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : TailRoundBound Q_SCALE 5 2 (3 * (4 * 5 - 9 * 2) * Q_SCALE) c d → 1148 ≤ d := by
      intro hr
      have hd0 : 224 ≤ d := tail_d_boot (c_lo := 61) (by omega) hr hd_pos u_ge_2 (by decide)
      have hd1 : 916 ≤ d := tail_d_boot (c_lo := 61) (by omega) hr hd0 (log2Ge_of_mul_two_pow (x := 225) (a := 28) (s := 3) (by decide) u_ge_28) (by decide)
      have hd2 : 1120 ≤ d := tail_d_boot (c_lo := 61) (by omega) hr hd1 (log2Ge_of_mul_two_pow (x := 917) (a := 28) (s := 5) (by decide) u_ge_28) (by decide)
      have hd3 : 1148 ≤ d := tail_d_boot (c_lo := 61) (by omega) hr hd2 (log2Ge_of_mul_two_pow (x := 1121) (a := 17) (s := 6) (by decide) u_ge_17) (by decide)
      exact hd3
    exact tail_step_of_log2 (Q := Q_SCALE) (c_lo := 61) (d_lb := 1148) (ld_lb := 43325323002) (pen_Q := 41789602) (Lw := 51302653978) (BL := 16473136132) (k_lb := 1439) (M_pre := 100884) (M_post := 64498444)
      (by decide) hV (by decide) (by decide) (by decide) (by omega) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 1149) (a := 17) (s := 6) (by decide) u_ge_17).mono_exp (by decide)) u_ge_63 (by decide)
      ((log2Le_of_mul_two_pow (x := 2298) (b := 18) (s := 7) (by decide) u_le_18).mono_exp (by decide)) (by decide)
      (fun c' k' hc' hk' => tail_cb_univ (p := 5) (q := 2) (Lw := 51302653978) (c_lo := 61) (by decide) hc' hk' (by decide) (by decide) (log2Ge_of_mul_two_pow (x := 41) (a := 20) (s := 1) (by decide) u_ge_20) log2Le_22 (by decide)) (by decide) (by decide) (by decide) (by decide)

theorem universal_vk_lb_2500 {c d k : Nat} (hV : ValidPassTriple 5 2 c d k) :
    10 ^ 100884 < v_k_pass c d k :=
  (universal_both_2500 hV).1

theorem universal_post_bini_lb_2500 {c d k h : Nat} (hPB : ValidPostBini 5 2 c d k h) :
    10 ^ 64498444 < (v_k_pass c d k) ^ h :=
  (universal_both_2500 hPB.1).2 h hPB

private theorem universal_both_2371 {c d k : Nat} (hV : ValidPassTriple 2371 1000 c d k) :
    10 ^ 1276692 < v_k_pass c d k ∧
    (∀ h, ValidPostBini 2371 1000 c d k h → 10 ^ 4540659390 < (v_k_pass c d k) ^ h) := by
  have hc_min : 10 ≤ c := universal_c_min_2371 hV
  have hd_pos : 1 ≤ d := hV.2.1
  refine if hb0 : c ≤ 13 then ?_ else if hb1 : c ≤ 16 then ?_ else if hb2 : c ≤ 19 then ?_ else if hb3 : c ≤ 23 then ?_ else if hb4 : c ≤ 28 then ?_ else if hb5 : c ≤ 36 then ?_ else if hb6 : c ≤ 48 then ?_ else if hb7 : c ≤ 70 then ?_ else if hb8 : c ≤ 114 then ?_ else ?_
  · have hd_lb : RoundBound Q_SCALE 2371 1000 113436759712 d → 2203 ≤ d := by
      intro hr
      have hd0 : 407 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 1780 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 408) (a := 25) (s := 4) (by decide) u_ge_25) (by decide)
      have hd2 : 2159 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 1781) (a := 27) (s := 6) (by decide) u_ge_27) (by decide)
      have hd3 : 2203 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 2160) (a := 16) (s := 7) (by decide) u_ge_16) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 10) (c_hi := 13) (c_g := 13) (G := 113436759712) (d_lb := 2203) (ld_lb := 47620290298) (pen_Q := 23726478) (Lw := 30770866916) (k_lb0 := 1155) (BL := 5673126591) (S := 1382670639) (R := 697835431805068683296620790095922057978842) (k_lb := 1455) (M_pre := 1276692) (M_post := 4540659390)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb0
      (f_mono_inc_range 2371 1000 c 13 (by omega) hb0 (by decide) (by decide)) u_le_15 u_le_12 u_ge_13 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 2204) (a := 17) (s := 7) (by decide) u_ge_17).mono_exp (by decide)) u_ge_12 (by decide)
      ((log2Le_of_mul_two_pow (x := 4408) (b := 18) (s := 8) (by decide) u_le_18).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 10) (by decide) (by omega) (by omega) u_ge_7 log2Le_22 (by decide)) u_le_12 u_ge_15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2371 1000 143289900816 d → 1693 ≤ d := by
      intro hr
      have hd0 : 322 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 1363 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 323) (a := 20) (s := 4) (by decide) u_ge_20) (by decide)
      have hd2 : 1657 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 1364) (a := 21) (s := 6) (by decide) u_ge_21) (by decide)
      have hd3 : 1693 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 1658) (a := 25) (s := 6) (by decide) u_ge_25) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 14) (c_hi := 16) (c_g := 16) (G := 143289900816) (d_lb := 1693) (ld_lb := 45958038642) (pen_Q := 29820944) (Lw := 34329917424) (k_lb0 := 1020) (BL := 7230353224) (S := 1129724169) (R := 638451020367839425805123729225966878282052) (k_lb := 1322) (M_pre := 1276692) (M_post := 4540659390)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb1
      (f_mono_inc_range 2371 1000 c 16 (by omega) hb1 (by decide) (by decide)) u_le_18 u_le_15 u_ge_16 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 1694) (a := 26) (s := 6) (by decide) u_ge_26).mono_exp (by decide)) u_ge_16 (by decide)
      ((log2Le_of_mul_two_pow (x := 3388) (b := 27) (s := 7) (by decide) u_le_27).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 14) (by decide) (by omega) (by omega) u_ge_9 log2Le_22 (by decide)) u_le_15 u_ge_18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2371 1000 150492959476 d → 1604 ≤ d := by
      intro hr
      have hd0 : 307 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 1288 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 308) (a := 19) (s := 4) (by decide) u_ge_19) (by decide)
      have hd2 : 1569 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 1289) (a := 20) (s := 6) (by decide) u_ge_20) (by decide)
      have hd3 : 1604 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 1570) (a := 24) (s := 6) (by decide) u_ge_24) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 17) (c_hi := 19) (c_g := 19) (G := 150492959476) (d_lb := 1604) (ld_lb := 45715014238) (pen_Q := 31329805) (Lw := 36458089687) (k_lb0 := 1031) (BL := 8473774677) (S := 955168176) (R := 586599814241090128879492222264165080940149) (k_lb := 1369) (M_pre := 1276692) (M_post := 4540659390)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb2
      (f_mono_inc_range 2371 1000 c 19 (by omega) hb2 (by decide) (by decide)) u_le_21 u_le_18 u_ge_19 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 1605) (a := 25) (s := 6) (by decide) u_ge_25).mono_exp (by decide)) u_ge_19 (by decide)
      ((log2Le_of_mul_two_pow (x := 3210) (b := 26) (s := 7) (by decide) u_le_26).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 17) (by decide) (by omega) (by omega) u_ge_11 log2Le_22 (by decide)) u_le_18 u_ge_21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2371 1000 150576356792 d → 1603 ≤ d := by
      intro hr
      have hd0 : 307 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 1287 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 308) (a := 19) (s := 4) (by decide) u_ge_19) (by decide)
      have hd2 : 1568 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 1288) (a := 20) (s := 6) (by decide) u_ge_20) (by decide)
      have hd3 : 1603 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 1569) (a := 24) (s := 6) (by decide) u_ge_24) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 20) (c_hi := 23) (c_g := 20) (G := 150576356792) (d_lb := 1603) (ld_lb := 45715014238) (pen_Q := 31349349) (Lw := 38274876571) (k_lb0 := 1082) (BL := 9534445065) (S := 792097501) (R := 522087975093335035728053460753760442058582) (k_lb := 1462) (M_pre := 1276692) (M_post := 4540659390)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb3
      (f_mono_dec_range 2371 1000 20 c (by decide) (by omega) (by decide) (by decide)) u_le_22 u_le_19 u_ge_20 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 1604) (a := 25) (s := 6) (by decide) u_ge_25).mono_exp (by decide)) u_ge_22 (by decide)
      ((log2Le_of_mul_two_pow (x := 3208) (b := 26) (s := 7) (by decide) u_le_26).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 20) (c_hi := 23) (by decide) (by omega) hb3 (by omega) u_ge_13 u_le_22 u_ge_19 (by decide)) u_le_22 u_ge_25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2371 1000 145682545016 d → 1665 ≤ d := by
      intro hr
      have hd0 : 317 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 1330 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 318) (a := 19) (s := 4) (by decide) u_ge_19) (by decide)
      have hd2 : 1620 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 1331) (a := 20) (s := 6) (by decide) u_ge_20) (by decide)
      have hd3 : 1665 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 1621) (a := 25) (s := 6) (by decide) u_ge_25) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 24) (c_hi := 28) (c_g := 24) (G := 145682545016) (d_lb := 1665) (ld_lb := 45958038642) (pen_Q := 30322437) (Lw := 40346147295) (k_lb0 := 1179) (BL := 10395596350) (S := 652848315) (R := 461934587294170149844862400009301520692077) (k_lb := 1607) (M_pre := 1276692) (M_post := 4540659390)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb4
      (f_mono_dec_range 2371 1000 24 c (by decide) (by omega) (by decide) (by decide)) u_le_26 u_le_23 u_ge_24 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 1666) (a := 26) (s := 6) (by decide) u_ge_26).mono_exp (by decide)) u_ge_26 (by decide)
      ((log2Le_of_mul_two_pow (x := 3332) (b := 27) (s := 7) (by decide) u_le_27).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 24) (by decide) (by omega) (by omega) u_ge_15 log2Le_22 (by decide)) u_le_27 u_ge_30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2371 1000 135109890856 d → 1812 ≤ d := by
      intro hr
      have hd0 : 342 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 1456 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 343) (a := 21) (s := 4) (by decide) u_ge_21) (by decide)
      have hd2 : 1768 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 1457) (a := 22) (s := 6) (by decide) u_ge_22) (by decide)
      have hd3 : 1812 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 1769) (a := 27) (s := 6) (by decide) u_ge_27) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 29) (c_hi := 36) (c_g := 29) (G := 135109890856) (d_lb := 1812) (ld_lb := 46417235946) (pen_Q := 28106866) (Lw := 42528115396) (k_lb0 := 1340) (BL := 11860338759) (S := 509574232) (R := 394051936429618604278170729246989591919904) (k_lb := 1866) (M_pre := 1276692) (M_post := 4540659390)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb5
      (f_mono_dec_range 2371 1000 29 c (by decide) (by omega) (by decide) (by decide)) u_le_31 u_le_28 u_ge_29 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 1813) (a := 28) (s := 6) (by decide) u_ge_28).mono_exp (by decide)) u_ge_31 (by decide)
      ((log2Le_of_mul_two_pow (x := 3626) (b := 29) (s := 7) (by decide) u_le_29).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 29) (by decide) (by omega) (by omega) u_ge_19 log2Le_22 (by decide)) u_le_35 u_ge_38 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2371 1000 117835095528 d → 2120 ≤ d := by
      intro hr
      have hd0 : 392 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 1703 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 393) (a := 24) (s := 4) (by decide) u_ge_24) (by decide)
      have hd2 : 2069 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 1704) (a := 26) (s := 6) (by decide) u_ge_26) (by decide)
      have hd3 : 2120 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 2070) (a := 16) (s := 7) (by decide) u_ge_16) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 37) (c_hi := 48) (c_g := 37) (G := 117835095528) (d_lb := 2120) (ld_lb := 47244640256) (pen_Q := 24488330) (Lw := 45376771022) (k_lb0 := 1639) (BL := 13560839475) (S := 383400297) (R := 329674881592965378975002516804068736128186) (k_lb := 2330) (M_pre := 1276692) (M_post := 4540659390)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb6
      (f_mono_dec_range 2371 1000 37 c (by decide) (by omega) (by decide) (by decide)) u_le_39 u_le_36 u_ge_37 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 2121) (a := 16) (s := 7) (by decide) u_ge_16).mono_exp (by decide)) u_ge_39 (by decide)
      ((log2Le_of_mul_two_pow (x := 4242) (b := 17) (s := 8) (by decide) u_le_17).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 37) (by decide) (by omega) (by omega) u_ge_25 log2Le_22 (by decide)) u_le_47 u_ge_50 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2371 1000 97052235184 d → 2642 ≤ d := by
      intro hr
      have hd0 : 476 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 2125 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 477) (a := 29) (s := 4) (by decide) u_ge_29) (by decide)
      have hd2 : 2574 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 2126) (a := 16) (s := 7) (by decide) u_ge_16) (by decide)
      have hd3 : 2642 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 2575) (a := 20) (s := 7) (by decide) u_ge_20) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 49) (c_hi := 70) (c_g := 49) (G := 97052235184) (d_lb := 2642) (ld_lb := 48627310895) (pen_Q := 20145571) (Lw := 48705617093) (k_lb0 := 2136) (BL := 15090465493) (S := 263713330) (R := 254521316259790974968087728562386577034409) (k_lb := 3069) (M_pre := 1276692) (M_post := 4540659390)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb7
      (f_mono_dec_range 2371 1000 49 c (by decide) (by omega) (by decide) (by decide)) u_le_51 u_le_48 u_ge_49 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 2643) (a := 20) (s := 7) (by decide) u_ge_20).mono_exp (by decide)) u_ge_51 (by decide)
      ((log2Le_of_mul_two_pow (x := 5286) (b := 21) (s := 8) (by decide) u_le_21).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 49) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 33) (a := 16) (s := 1) (by decide) u_ge_16) log2Le_22 (by decide)) u_le_69 u_ge_72 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2371 1000 72349524812 d → 3681 ≤ d := by
      intro hr
      have hd0 : 638 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 2960 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 639) (a := 19) (s := 5) (by decide) u_ge_19) (by decide)
      have hd2 : 3601 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 2961) (a := 23) (s := 7) (by decide) u_ge_23) (by decide)
      have hd3 : 3681 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 3602) (a := 28) (s := 7) (by decide) u_ge_28) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 71) (c_hi := 114) (c_g := 71) (G := 72349524812) (d_lb := 3681) (ld_lb := 50712203242) (pen_Q := 15002611) (Lw := 53155185485) (k_lb0 := 3128) (BL := 17339146971) (S := 162358493) (R := 182246831182337568386446268086379232623894) (k_lb := 4566) (M_pre := 1276692) (M_post := 4540659390)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb8
      (f_mono_dec_range 2371 1000 71 c (by decide) (by omega) (by decide) (by decide)) u_le_73 u_le_70 u_ge_71 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 3682) (a := 28) (s := 7) (by decide) u_ge_28).mono_exp (by decide)) u_ge_73 (by decide)
      ((log2Le_of_mul_two_pow (x := 7364) (b := 29) (s := 8) (by decide) u_le_29).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 71) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 47) (a := 23) (s := 1) (by decide) u_ge_23) log2Le_22 (by decide)) u_le_113 u_ge_116 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : TailRoundBound Q_SCALE 2371 1000 (3 * (4 * 2371 - 9 * 1000) * Q_SCALE) c d → 5076 ≤ d := by
      intro hr
      have hd0 : 851 ≤ d := tail_d_boot (c_lo := 115) (by omega) hr hd_pos u_ge_2 (by decide)
      have hd1 : 4119 ≤ d := tail_d_boot (c_lo := 115) (by omega) hr hd0 (log2Ge_of_mul_two_pow (x := 852) (a := 26) (s := 5) (by decide) u_ge_26) (by decide)
      have hd2 : 4983 ≤ d := tail_d_boot (c_lo := 115) (by omega) hr hd1 (log2Ge_of_mul_two_pow (x := 4120) (a := 16) (s := 8) (by decide) u_ge_16) (by decide)
      have hd3 : 5076 ≤ d := tail_d_boot (c_lo := 115) (by omega) hr hd2 (log2Ge_of_mul_two_pow (x := 4984) (a := 19) (s := 8) (by decide) u_ge_19) (by decide)
      exact hd3
    exact tail_step_of_log2 (Q := Q_SCALE) (c_lo := 115) (d_lb := 5076) (ld_lb := 52604448114) (pen_Q := 11272113) (Lw := 59004711451) (BL := 20450273351) (k_lb := 6895) (M_pre := 1276692) (M_post := 4540659390)
      (by decide) hV (by decide) (by decide) (by decide) (by omega) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 5077) (a := 19) (s := 8) (by decide) u_ge_19).mono_exp (by decide)) u_ge_117 (by decide)
      ((log2Le_of_mul_two_pow (x := 10154) (b := 20) (s := 9) (by decide) u_le_20).mono_exp (by decide)) (by decide)
      (fun c' k' hc' hk' => tail_cb_univ (p := 2371) (q := 1000) (Lw := 59004711451) (c_lo := 115) (by decide) hc' hk' (by decide) (by decide) (log2Ge_of_mul_two_pow (x := 77) (a := 19) (s := 2) (by decide) u_ge_19) log2Le_22 (by decide)) (by decide) (by decide) (by decide) (by decide)

theorem universal_vk_lb_2371 {c d k : Nat} (hV : ValidPassTriple 2371 1000 c d k) :
    10 ^ 1276692 < v_k_pass c d k :=
  (universal_both_2371 hV).1

theorem universal_post_bini_lb_2371 {c d k h : Nat} (hPB : ValidPostBini 2371 1000 c d k h) :
    10 ^ 4540659390 < (v_k_pass c d k) ^ h :=
  (universal_both_2371 hPB.1).2 h hPB

private theorem universal_both_2321 {c d k : Nat} (hV : ValidPassTriple 2321 1000 c d k) :
    10 ^ 8275812 < v_k_pass c d k ∧
    (∀ h, ValidPostBini 2321 1000 c d k h → 10 ^ 96516675505 < (v_k_pass c d k) ^ h) := by
  have hc_min : 17 ≤ c := universal_c_min_2321 hV
  have hd_pos : 1 ≤ d := hV.2.1
  refine if hb0 : c ≤ 22 then ?_ else if hb1 : c ≤ 27 then ?_ else if hb2 : c ≤ 32 then ?_ else if hb3 : c ≤ 39 then ?_ else if hb4 : c ≤ 48 then ?_ else if hb5 : c ≤ 60 then ?_ else if hb6 : c ≤ 81 then ?_ else if hb7 : c ≤ 118 then ?_ else if hb8 : c ≤ 192 then ?_ else ?_
  · have hd_lb : RoundBound Q_SCALE 2321 1000 41052345656 d → 6769 ≤ d := by
      intro hr
      have hd0 : 1114 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 5527 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 1115) (a := 17) (s := 6) (by decide) u_ge_17) (by decide)
      have hd2 : 6647 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 5528) (a := 21) (s := 8) (by decide) u_ge_21) (by decide)
      have hd3 : 6769 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 6648) (a := 25) (s := 8) (by decide) u_ge_25) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 17) (c_hi := 22) (c_g := 22) (G := 41052345656) (d_lb := 6769) (ld_lb := 54547973234) (pen_Q := 8727551) (Lw := 36480691941) (k_lb0 := 3872) (BL := 8473774677) (S := 827404308) (R := 585535948150661927020189684637351472695994) (k_lb := 5111) (M_pre := 8275812) (M_post := 96516675505)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb0
      (f_mono_inc_range 2321 1000 c 22 (by omega) hb0 (by decide) (by decide)) u_le_24 u_le_21 u_ge_22 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 6770) (a := 26) (s := 8) (by decide) u_ge_26).mono_exp (by decide)) u_ge_19 (by decide)
      ((log2Le_of_mul_two_pow (x := 13540) (b := 27) (s := 9) (by decide) u_le_27).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 17) (by decide) (by omega) (by omega) u_ge_11 log2Le_22 (by decide)) u_le_21 u_ge_24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2321 1000 50991269688 d → 5324 ≤ d := by
      intro hr
      have hd0 : 897 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 4340 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 898) (a := 28) (s := 5) (by decide) u_ge_28) (by decide)
      have hd2 : 5198 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 4341) (a := 16) (s := 8) (by decide) u_ge_16) (by decide)
      have hd3 : 5324 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 5199) (a := 20) (s := 8) (by decide) u_ge_20) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 23) (c_hi := 27) (c_g := 27) (G := 50991269688) (d_lb := 5324) (ld_lb := 52922278191) (pen_Q := 10803826) (Lw := 39879617098) (k_lb0 := 3408) (BL := 10443187313) (S := 676634631) (R := 526936059937289979620338165767041421524109) (k_lb := 4637) (M_pre := 8275812) (M_post := 96516675505)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb1
      (f_mono_inc_range 2321 1000 c 27 (by omega) hb1 (by decide) (by decide)) u_le_29 u_le_26 u_ge_27 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 5325) (a := 20) (s := 8) (by decide) u_ge_20).mono_exp (by decide)) u_ge_25 (by decide)
      ((log2Le_of_mul_two_pow (x := 10650) (b := 21) (s := 9) (by decide) u_le_21).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_narrow (c_lo := 23) (c_hi := 27) (by decide) (by omega) hb1 (by omega) u_ge_15 u_le_25 u_ge_22 (by decide)) u_le_26 u_ge_29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2321 1000 53282653212 d → 5067 ≤ d := by
      intro hr
      have hd0 : 858 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 4114 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 859) (a := 26) (s := 5) (by decide) u_ge_26) (by decide)
      have hd2 : 4974 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 4115) (a := 16) (s := 8) (by decide) u_ge_16) (by decide)
      have hd3 : 5067 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 4975) (a := 19) (s := 8) (by decide) u_ge_19) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 28) (c_hi := 32) (c_g := 32) (G := 53282653212) (d_lb := 5067) (ld_lb := 52604448114) (pen_Q := 11292135) (Lw := 42138577131) (k_lb0 := 3446) (BL := 11860338759) (S := 572375390) (R := 478893592884219709111449851124833905318945) (k_lb := 4782) (M_pre := 8275812) (M_post := 96516675505)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb2
      (f_mono_inc_range 2321 1000 c 32 (by omega) hb2 (by decide) (by decide)) u_le_34 u_le_31 u_ge_32 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 5068) (a := 19) (s := 8) (by decide) u_ge_19).mono_exp (by decide)) u_ge_30 (by decide)
      ((log2Le_of_mul_two_pow (x := 10136) (b := 20) (s := 9) (by decide) u_le_20).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 28) (by decide) (by omega) (by omega) u_ge_19 log2Le_22 (by decide)) u_le_31 u_ge_34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2321 1000 53302371360 d → 5065 ≤ d := by
      intro hr
      have hd0 : 858 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 4112 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 859) (a := 26) (s := 5) (by decide) u_ge_26) (by decide)
      have hd2 : 4972 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 4113) (a := 16) (s := 8) (by decide) u_ge_16) (by decide)
      have hd3 : 5065 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 4973) (a := 19) (s := 8) (by decide) u_ge_19) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 33) (c_hi := 39) (c_g := 33) (G := 53302371360) (d_lb := 5065) (ld_lb := 52604448114) (pen_Q := 11296594) (Lw := 44048909024) (k_lb0 := 3601) (BL := 12480488697) (S := 470833603) (R := 413742659655435725683201794380268122771597) (k_lb := 5006) (M_pre := 8275812) (M_post := 96516675505)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb3
      (f_mono_dec_range 2321 1000 33 c (by decide) (by omega) (by decide) (by decide)) u_le_35 u_le_32 u_ge_33 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 5066) (a := 19) (s := 8) (by decide) u_ge_19).mono_exp (by decide)) u_ge_35 (by decide)
      ((log2Le_of_mul_two_pow (x := 10132) (b := 20) (s := 9) (by decide) u_le_20).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 33) (by decide) (by omega) (by omega) u_ge_21 log2Le_22 (by decide)) u_le_38 u_ge_41 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2321 1000 51553774808 d → 5266 ≤ d := by
      intro hr
      have hd0 : 887 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 4273 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 888) (a := 27) (s := 5) (by decide) u_ge_27) (by decide)
      have hd2 : 5141 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 4274) (a := 16) (s := 8) (by decide) u_ge_16) (by decide)
      have hd3 : 5266 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 5142) (a := 20) (s := 8) (by decide) u_ge_20) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 40) (c_hi := 48) (c_g := 40) (G := 51553774808) (d_lb := 5266) (ld_lb := 52922278191) (pen_Q := 10922820) (Lw := 46308731140) (k_lb0 := 3914) (BL := 14037715330) (S := 383400297) (R := 364155253992590262671043515056795571389107) (k_lb := 5548) (M_pre := 8275812) (M_post := 96516675505)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb4
      (f_mono_dec_range 2321 1000 40 c (by decide) (by omega) (by decide) (by decide)) u_le_42 u_le_39 u_ge_40 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 5267) (a := 20) (s := 8) (by decide) u_ge_20).mono_exp (by decide)) u_ge_42 (by decide)
      ((log2Le_of_mul_two_pow (x := 10534) (b := 21) (s := 9) (by decide) u_le_21).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 40) (by decide) (by omega) (by omega) u_ge_27 log2Le_22 (by decide)) u_le_47 u_ge_50 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2321 1000 47474999984 d → 5776 ≤ d := by
      intro hr
      have hd0 : 963 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 4704 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 964) (a := 30) (s := 5) (by decide) u_ge_30) (by decide)
      have hd2 : 5654 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 4705) (a := 18) (s := 8) (by decide) u_ge_18) (by decide)
      have hd3 : 5776 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 5655) (a := 22) (s := 8) (by decide) u_ge_22) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 49) (c_hi := 60) (c_g := 49) (G := 47474999984) (d_lb := 5776) (ld_lb := 53512851328) (pen_Q := 10055966) (Lw := 48715706698) (k_lb0 := 4471) (BL := 15090465493) (S := 307318915) (R := 313021894196589540633281276807415783924361) (k_lb := 6379) (M_pre := 8275812) (M_post := 96516675505)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb5
      (f_mono_dec_range 2321 1000 49 c (by decide) (by omega) (by decide) (by decide)) u_le_51 u_le_48 u_ge_49 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 5777) (a := 22) (s := 8) (by decide) u_ge_22).mono_exp (by decide)) u_ge_51 (by decide)
      ((log2Le_of_mul_two_pow (x := 11554) (b := 23) (s := 9) (by decide) u_le_23).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 49) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 33) (a := 16) (s := 1) (by decide) u_ge_16) log2Le_22 (by decide)) u_le_59 u_ge_62 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2321 1000 41942091624 d → 6625 ≤ d := by
      intro hr
      have hd0 : 1090 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 5410 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 1091) (a := 17) (s := 6) (by decide) u_ge_17) (by decide)
      have hd2 : 6506 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 5411) (a := 21) (s := 8) (by decide) u_ge_21) (by decide)
      have hd3 : 6625 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 6507) (a := 25) (s := 8) (by decide) u_ge_25) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 61) (c_hi := 81) (c_g := 61) (G := 41942091624) (d_lb := 6625) (ld_lb := 54304948830) (pen_Q := 8881954) (Lw := 51335561626) (k_lb0 := 5334) (BL := 16473136132) (S := 228111452) (R := 251782858409682253360510545654423539043436) (k_lb := 7690) (M_pre := 8275812) (M_post := 96516675505)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb6
      (f_mono_dec_range 2321 1000 61 c (by decide) (by omega) (by decide) (by decide)) u_le_63 u_le_60 u_ge_61 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 6626) (a := 25) (s := 8) (by decide) u_ge_25).mono_exp (by decide)) u_ge_63 (by decide)
      ((log2Le_of_mul_two_pow (x := 13252) (b := 26) (s := 9) (by decide) u_le_26).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 61) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 41) (a := 20) (s := 1) (by decide) u_ge_20) log2Le_22 (by decide)) u_le_80 u_ge_83 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2321 1000 34177736140 d → 8311 ≤ d := by
      intro hr
      have hd0 : 1338 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 6776 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 1339) (a := 20) (s := 6) (by decide) u_ge_20) (by decide)
      have hd2 : 8163 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 6777) (a := 26) (s := 8) (by decide) u_ge_26) (by decide)
      have hd3 : 8311 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 8164) (a := 31) (s := 8) (by decide) u_ge_31) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 82) (c_hi := 118) (c_g := 82) (G := 34177736140) (d_lb := 8311) (ld_lb := 55834574848) (pen_Q := 7280134) (Lw := 54902308418) (k_lb0 := 7000) (BL := 18332682626) (S := 156877442) (R := 193149106427103877008741783835307987470558) (k_lb := 10218) (M_pre := 8275812) (M_post := 96516675505)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb7
      (f_mono_dec_range 2321 1000 82 c (by decide) (by omega) (by decide) (by decide)) u_le_84 u_le_81 u_ge_82 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 8312) (a := 16) (s := 9) (by decide) u_ge_16).mono_exp (by decide)) u_ge_84 (by decide)
      ((log2Le_of_mul_two_pow (x := 16624) (b := 17) (s := 10) (by decide) u_le_17).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 82) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 55) (a := 27) (s := 1) (by decide) u_ge_27) log2Le_22 (by decide)) u_le_117 u_ge_120 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2321 1000 25413558100 d → 11574 ≤ d := by
      intro hr
      have hd0 : 1799 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 9493 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 1800) (a := 28) (s := 6) (by decide) u_ge_28) (by decide)
      have hd2 : 11346 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 9494) (a := 18) (s := 9) (by decide) u_ge_18) (by decide)
      have hd3 : 11574 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 11347) (a := 22) (s := 9) (by decide) u_ge_22) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 119) (c_hi := 192) (c_g := 119) (G := 25413558100) (d_lb := 11574) (ld_lb := 57807818624) (pen_Q := 5389514) (Lw := 59427193144) (k_lb0 := 10190) (BL := 20450273351) (S := 96568104) (R := 134912858658978504033601851635417225634080) (k_lb := 15018) (M_pre := 8275812) (M_post := 96516675505)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb8
      (f_mono_dec_range 2321 1000 119 c (by decide) (by omega) (by decide) (by decide)) u_le_121 u_le_118 u_ge_119 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 11575) (a := 22) (s := 9) (by decide) u_ge_22).mono_exp (by decide)) u_ge_121 (by decide)
      ((log2Le_of_mul_two_pow (x := 23150) (b := 23) (s := 10) (by decide) u_le_23).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 119) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 79) (a := 19) (s := 2) (by decide) u_ge_19) log2Le_22 (by decide)) u_le_191 u_ge_194 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : TailRoundBound Q_SCALE 2321 1000 (3 * (4 * 2321 - 9 * 1000) * Q_SCALE) c d → 15983 ≤ d := by
      intro hr
      have hd0 : 2411 ≤ d := tail_d_boot (c_lo := 193) (by omega) hr hd_pos u_ge_2 (by decide)
      have hd1 : 13105 ≤ d := tail_d_boot (c_lo := 193) (by omega) hr hd0 (log2Ge_of_mul_two_pow (x := 2412) (a := 18) (s := 7) (by decide) u_ge_18) (by decide)
      have hd2 : 15707 ≤ d := tail_d_boot (c_lo := 193) (by omega) hr hd1 (log2Ge_of_mul_two_pow (x := 13106) (a := 25) (s := 9) (by decide) u_ge_25) (by decide)
      have hd3 : 15983 ≤ d := tail_d_boot (c_lo := 193) (by omega) hr hd2 (log2Ge_of_mul_two_pow (x := 15708) (a := 30) (s := 9) (by decide) u_ge_30) (by decide)
      exact hd3
    exact tail_step_of_log2 (Q := Q_SCALE) (c_lo := 193) (d_lb := 15983) (ld_lb := 59932816795) (pen_Q := 4030815) (Lw := 65342438999) (BL := 23680400085) (k_lb := 22512) (M_pre := 8275812) (M_post := 96516675505)
      (by decide) hV (by decide) (by decide) (by decide) (by omega) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 15984) (a := 31) (s := 9) (by decide) u_ge_31).mono_exp (by decide)) u_ge_195 (by decide)
      ((log2Le_of_mul_two_pow (x := 31968) (b := 32) (s := 10) (by decide) u_le_32).mono_exp (by decide)) (by decide)
      (fun c' k' hc' hk' => tail_cb_univ (p := 2321) (q := 1000) (Lw := 65342438999) (c_lo := 193) (by decide) hc' hk' (by decide) (by decide) (log2Ge_of_mul_two_pow (x := 129) (a := 16) (s := 3) (by decide) u_ge_16) log2Le_22 (by decide)) (by decide) (by decide) (by decide) (by decide)

theorem universal_vk_lb_2321 {c d k : Nat} (hV : ValidPassTriple 2321 1000 c d k) :
    10 ^ 8275812 < v_k_pass c d k :=
  (universal_both_2321 hV).1

theorem universal_post_bini_lb_2321 {c d k h : Nat} (hPB : ValidPostBini 2321 1000 c d k h) :
    10 ^ 96516675505 < (v_k_pass c d k) ^ h :=
  (universal_both_2321 hPB.1).2 h hPB

private theorem universal_both_2300 {c d k : Nat} (hV : ValidPassTriple 23 10 c d k) :
    10 ^ 27646894 < v_k_pass c d k ∧
    (∀ h, ValidPostBini 23 10 c d k h → 10 ^ 717548091249 < (v_k_pass c d k) ^ h) := by
  have hc_min : 23 ≤ c := universal_c_min_2300 hV
  have hd_pos : 1 ≤ d := hV.2.1
  refine if hb0 : c ≤ 30 then ?_ else if hb1 : c ≤ 38 then ?_ else if hb2 : c ≤ 46 then ?_ else if hb3 : c ≤ 56 then ?_ else if hb4 : c ≤ 69 then ?_ else if hb5 : c ≤ 87 then ?_ else if hb6 : c ≤ 117 then ?_ else if hb7 : c ≤ 170 then ?_ else if hb8 : c ≤ 276 then ?_ else ?_
  · have hd_lb : RoundBound Q_SCALE 23 10 192951064 d → 15526 ≤ d := by
      intro hr
      have hd0 : 2360 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 12773 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 2361) (a := 18) (s := 7) (by decide) u_ge_18) (by decide)
      have hd2 : 15246 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 12774) (a := 24) (s := 9) (by decide) u_ge_24) (by decide)
      have hd3 : 15526 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 15247) (a := 29) (s := 9) (by decide) u_ge_29) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 23) (c_hi := 30) (c_g := 30) (G := 192951064) (d_lb := 15526) (ld_lb := 59729640297) (pen_Q := 4136789) (Lw := 39886284135) (k_lb0 := 9095) (BL := 10395596350) (S := 609966981) (R := 525695030385405551953671968248265511) (k_lb := 12328) (M_pre := 27646894) (M_post := 717548091249)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb0
      (f_mono_inc_range 23 10 c 30 (by omega) hb0 (by decide) (by decide)) u_le_32 u_le_29 u_ge_30 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 15527) (a := 30) (s := 9) (by decide) u_ge_30).mono_exp (by decide)) u_ge_25 (by decide)
      ((log2Le_of_mul_two_pow (x := 31054) (b := 31) (s := 10) (by decide) u_le_31).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 23) (by decide) (by omega) (by omega) u_ge_15 log2Le_22 (by decide)) u_le_29 u_ge_32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 23 10 255850136 d → 11349 ≤ d := by
      intro hr
      have hd0 : 1780 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 9313 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 1781) (a := 27) (s := 6) (by decide) u_ge_27) (by decide)
      have hd2 : 11178 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 9314) (a := 18) (s := 9) (by decide) u_ge_18) (by decide)
      have hd3 : 11349 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 11179) (a := 21) (s := 9) (by decide) u_ge_21) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 31) (c_hi := 38) (c_g := 38) (G := 255850136) (d_lb := 11349) (ld_lb := 57807818624) (pen_Q := 5496363) (Lw := 43325519177) (k_lb0 := 7450) (BL := 12480488697) (S := 483075283) (R := 452408334798195394228849254259439621) (k_lb := 10377) (M_pre := 27646894) (M_post := 717548091249)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb1
      (f_mono_inc_range 23 10 c 38 (by omega) hb1 (by decide) (by decide)) u_le_40 u_le_37 u_ge_38 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 11350) (a := 22) (s := 9) (by decide) u_ge_22).mono_exp (by decide)) u_ge_33 (by decide)
      ((log2Le_of_mul_two_pow (x := 22700) (b := 23) (s := 10) (by decide) u_le_23).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 31) (by decide) (by omega) (by omega) u_ge_21 log2Le_22 (by decide)) u_le_37 u_ge_40 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 23 10 267515784 d → 10802 ≤ d := by
      intro hr
      have hd0 : 1702 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 8866 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 1703) (a := 26) (s := 6) (by decide) u_ge_26) (by decide)
      have hd2 : 10629 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 8867) (a := 17) (s := 9) (by decide) u_ge_17) (by decide)
      have hd3 : 10802 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 10630) (a := 20) (s := 9) (by decide) u_ge_20) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 39) (c_hi := 46) (c_g := 46) (G := 267515784) (d_lb := 10802) (ld_lb := 57519565348) (pen_Q := 5749194) (Lw := 46015272098) (k_lb0 := 7568) (BL := 13560839475) (S := 399901845) (R := 399317902291296334016026560672658295) (k_lb := 10609) (M_pre := 27646894) (M_post := 717548091249)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb2
      (f_mono_inc_range 23 10 c 46 (by omega) hb2 (by decide) (by decide)) u_le_48 u_le_45 u_ge_46 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 10803) (a := 21) (s := 9) (by decide) u_ge_21).mono_exp (by decide)) u_ge_41 (by decide)
      ((log2Le_of_mul_two_pow (x := 21606) (b := 22) (s := 10) (by decide) u_le_22).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 39) (by decide) (by omega) (by omega) u_ge_25 log2Le_22 (by decide)) u_le_45 u_ge_48 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 23 10 267396276 d → 10807 ≤ d := by
      intro hr
      have hd0 : 1703 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 8870 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 1704) (a := 26) (s := 6) (by decide) u_ge_26) (by decide)
      have hd2 : 10634 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 8871) (a := 17) (s := 9) (by decide) u_ge_17) (by decide)
      have hd3 : 10807 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 10635) (a := 20) (s := 9) (by decide) u_ge_20) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 47) (c_hi := 56) (c_g := 47) (G := 267396276) (d_lb := 10807) (ld_lb := 57519565348) (pen_Q := 5746534) (Lw := 48224243780) (k_lb0 := 7935) (BL := 14893740144) (S := 329085897) (R := 349808199876246810833131207973854926) (k_lb := 11277) (M_pre := 27646894) (M_post := 717548091249)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb3
      (f_mono_dec_range 23 10 47 c (by decide) (by omega) (by decide) (by decide)) u_le_49 u_le_46 u_ge_47 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 10808) (a := 21) (s := 9) (by decide) u_ge_21).mono_exp (by decide)) u_ge_49 (by decide)
      ((log2Le_of_mul_two_pow (x := 21616) (b := 22) (s := 10) (by decide) u_le_22).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 47) (by decide) (by omega) (by omega) u_ge_31 log2Le_22 (by decide)) u_le_55 u_ge_58 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 23 10 257662020 d → 11270 ≤ d := by
      intro hr
      have hd0 : 1767 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 9247 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 1768) (a := 27) (s := 6) (by decide) u_ge_27) (by decide)
      have hd2 : 11099 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 9248) (a := 18) (s := 9) (by decide) u_ge_18) (by decide)
      have hd3 : 11270 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 11100) (a := 21) (s := 9) (by decide) u_ge_21) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 57) (c_hi := 69) (c_g := 57) (G := 257662020) (d_lb := 11270) (ld_lb := 57807818624) (pen_Q := 5534892) (Lw := 50525984130) (k_lb0 := 8628) (BL := 15820287816) (S := 267508937) (R := 301144312732727667779770942799905042) (k_lb := 12312) (M_pre := 27646894) (M_post := 717548091249)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb4
      (f_mono_dec_range 23 10 57 c (by decide) (by omega) (by decide) (by decide)) u_le_59 u_le_56 u_ge_57 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 11271) (a := 22) (s := 9) (by decide) u_ge_22).mono_exp (by decide)) u_ge_59 (by decide)
      ((log2Le_of_mul_two_pow (x := 22542) (b := 23) (s := 10) (by decide) u_le_23).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 57) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 37) (a := 18) (s := 1) (by decide) u_ge_18) log2Le_22 (by decide)) u_le_68 u_ge_71 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 23 10 236351680 d → 12395 ≤ d := by
      intro hr
      have hd0 : 1927 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 10208 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 1928) (a := 30) (s := 6) (by decide) u_ge_30) (by decide)
      have hd2 : 12165 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 10209) (a := 19) (s := 9) (by decide) u_ge_19) (by decide)
      have hd3 : 12395 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 12166) (a := 23) (s := 9) (by decide) u_ge_23) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 70) (c_hi := 87) (c_g := 70) (G := 236351680) (d_lb := 12395) (ld_lb := 58346969657) (pen_Q := 5074215) (Lw := 52994177983) (k_lb0 := 9865) (BL := 17339146971) (S := 212466346) (R := 256915970752708720279748873454681904) (k_lb := 14267) (M_pre := 27646894) (M_post := 717548091249)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb5
      (f_mono_dec_range 23 10 70 c (by decide) (by omega) (by decide) (by decide)) u_le_72 u_le_69 u_ge_70 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 12396) (a := 24) (s := 9) (by decide) u_ge_24).mono_exp (by decide)) u_ge_72 (by decide)
      ((log2Le_of_mul_two_pow (x := 24792) (b := 25) (s := 10) (by decide) u_le_25).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 70) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 47) (a := 23) (s := 1) (by decide) u_ge_23) log2Le_22 (by decide)) u_le_86 u_ge_89 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 23 10 207017196 d → 14372 ≤ d := by
      intro hr
      have hd0 : 2200 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 11827 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 2201) (a := 17) (s := 7) (by decide) u_ge_17) (by decide)
      have hd2 : 14152 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 11828) (a := 23) (s := 9) (by decide) u_ge_23) (by decide)
      have hd3 : 14372 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 14153) (a := 27) (s := 9) (by decide) u_ge_27) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 88) (c_hi := 117) (c_g := 88) (G := 207017196) (d_lb := 14372) (ld_lb := 59302137834) (pen_Q := 4440200) (Lw := 55760153278) (k_lb0 := 11851) (BL := 18775465807) (S := 158212714) (R := 206687233814284571102133430778789145) (k_lb := 17293) (M_pre := 27646894) (M_post := 717548091249)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb6
      (f_mono_dec_range 23 10 88 c (by decide) (by omega) (by decide) (by decide)) u_le_90 u_le_87 u_ge_88 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 14373) (a := 28) (s := 9) (by decide) u_ge_28).mono_exp (by decide)) u_ge_90 (by decide)
      ((log2Le_of_mul_two_pow (x := 28746) (b := 29) (s := 10) (by decide) u_le_29).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 88) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 59) (a := 29) (s := 1) (by decide) u_ge_29) log2Le_22 (by decide)) u_le_116 u_ge_119 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 23 10 168455968 d → 18052 ≤ d := by
      intro hr
      have hd0 : 2703 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 14891 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 2704) (a := 21) (s := 7) (by decide) u_ge_21) (by decide)
      have hd2 : 17783 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 14892) (a := 29) (s := 9) (by decide) u_ge_29) (by decide)
      have hd3 : 18052 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 17784) (a := 17) (s := 10) (by decide) u_ge_17) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 118) (c_hi := 170) (c_g := 118) (G := 168455968) (d_lb := 18052) (ld_lb := 60505192186) (pen_Q := 3609259) (Lw := 59326129191) (k_lb0 := 15495) (BL := 20450273351) (S := 109029111) (R := 156001197404853617517786829806150230) (k_lb := 22779) (M_pre := 27646894) (M_post := 717548091249)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb7
      (f_mono_dec_range 23 10 118 c (by decide) (by omega) (by decide) (by decide)) u_le_120 u_le_117 u_ge_118 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 18053) (a := 17) (s := 10) (by decide) u_ge_17).mono_exp (by decide)) u_ge_120 (by decide)
      ((log2Le_of_mul_two_pow (x := 36106) (b := 18) (s := 11) (by decide) u_le_18).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 118) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 79) (a := 19) (s := 2) (by decide) u_ge_19) log2Le_22 (by decide)) u_le_169 u_ge_172 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 23 10 125104268 d → 25093 ≤ d := by
      intro hr
      have hd0 : 3640 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 20707 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 3641) (a := 28) (s := 7) (by decide) u_ge_28) (by decide)
      have hd2 : 24678 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 20708) (a := 20) (s := 10) (by decide) u_ge_20) (by decide)
      have hd3 : 25093 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 24679) (a := 24) (s := 10) (by decide) u_ge_24) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 171) (c_hi := 276) (c_g := 171) (G := 125104268) (d_lb := 25093) (ld_lb := 62641936953) (pen_Q := 2677634) (Lw := 63860292556) (k_lb0 := 22460) (BL := 22852995775) (S := 67230257) (R := 108649090124483264273672800629308118) (k_lb := 33420) (M_pre := 27646894) (M_post := 717548091249)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb8
      (f_mono_dec_range 23 10 171 c (by decide) (by omega) (by decide) (by decide)) u_le_173 u_le_170 u_ge_171 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 25094) (a := 24) (s := 10) (by decide) u_ge_24).mono_exp (by decide)) u_ge_173 (by decide)
      ((log2Le_of_mul_two_pow (x := 50188) (b := 25) (s := 11) (by decide) u_le_25).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 171) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 113) (a := 28) (s := 2) (by decide) u_ge_28) log2Le_22 (by decide)) u_le_275 u_ge_278 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : TailRoundBound Q_SCALE 23 10 (3 * (4 * 23 - 9 * 10) * Q_SCALE) c d → 34626 ≤ d := by
      intro hr
      have hd0 : 4894 ≤ d := tail_d_boot (c_lo := 277) (by omega) hr hd_pos u_ge_2 (by decide)
      have hd1 : 28781 ≤ d := tail_d_boot (c_lo := 277) (by omega) hr hd0 (log2Ge_of_mul_two_pow (x := 4895) (a := 19) (s := 8) (by decide) u_ge_19) (by decide)
      have hd2 : 34216 ≤ d := tail_d_boot (c_lo := 277) (by omega) hr hd1 (log2Ge_of_mul_two_pow (x := 28782) (a := 28) (s := 10) (by decide) u_ge_28) (by decide)
      have hd3 : 34626 ≤ d := tail_d_boot (c_lo := 277) (by omega) hr hd2 (log2Ge_of_mul_two_pow (x := 34217) (a := 16) (s := 11) (by decide) u_ge_16) (by decide)
      exact hd3
    exact tail_step_of_log2 (Q := Q_SCALE) (c_lo := 277) (d_lb := 34626) (ld_lb := 64424509440) (pen_Q := 1995470) (Lw := 69783675216) (BL := 25929081563) (k_lb := 49727) (M_pre := 27646894) (M_post := 717548091249)
      (by decide) hV (by decide) (by decide) (by decide) (by omega) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 34627) (a := 16) (s := 11) (by decide) u_ge_16).mono_exp (by decide)) u_ge_279 (by decide)
      ((log2Le_of_mul_two_pow (x := 69254) (b := 17) (s := 12) (by decide) u_le_17).mono_exp (by decide)) (by decide)
      (fun c' k' hc' hk' => tail_cb_univ (p := 23) (q := 10) (Lw := 69783675216) (c_lo := 277) (by decide) hc' hk' (by decide) (by decide) (log2Ge_of_mul_two_pow (x := 185) (a := 23) (s := 3) (by decide) u_ge_23) log2Le_22 (by decide)) (by decide) (by decide) (by decide) (by decide)

theorem universal_vk_lb_2300 {c d k : Nat} (hV : ValidPassTriple 23 10 c d k) :
    10 ^ 27646894 < v_k_pass c d k :=
  (universal_both_2300 hV).1

theorem universal_post_bini_lb_2300 {c d k h : Nat} (hPB : ValidPostBini 23 10 c d k h) :
    10 ^ 717548091249 < (v_k_pass c d k) ^ h :=
  (universal_both_2300 hPB.1).2 h hPB

private theorem universal_both_2260 {c d k : Nat} (hV : ValidPassTriple 113 50 c d k) :
    10 ^ 6433782848 < v_k_pass c d k ∧
    (∀ h, ValidPostBini 113 50 c d k h → 10 ^ 5783603075788347 < (v_k_pass c d k) ^ h) := by
  have hc_min : 113 ≤ c := universal_c_min_2260 hV
  have hd_pos : 1 ≤ d := hV.2.1
  refine if hb0 : c ≤ 150 then ?_ else if hb1 : c ≤ 188 then ?_ else if hb2 : c ≤ 226 then ?_ else if hb3 : c ≤ 275 then ?_ else if hb4 : c ≤ 339 then ?_ else if hb5 : c ≤ 429 then ?_ else if hb6 : c ≤ 576 then ?_ else if hb7 : c ≤ 836 then ?_ else if hb8 : c ≤ 1356 then ?_ else ?_
  · have hd_lb : RoundBound Q_SCALE 113 50 40759992 d → 479492 ≤ d := by
      intro hr
      have hd0 : 55426 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 406801 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 55427) (a := 27) (s := 11) (by decide) u_ge_27) (by decide)
      have hd2 : 474196 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 406802) (a := 24) (s := 14) (by decide) u_ge_24) (by decide)
      have hd3 : 479492 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 474197) (a := 28) (s := 14) (by decide) u_ge_28) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 113) (c_hi := 150) (c_g := 150) (G := 40759992) (d_lb := 479492) (ld_lb := 80994411642) (pen_Q := 178313) (Lw := 58802133473) (k_lb0 := 323152) (BL := 20115255112) (S := 123518934) (R := 27914971353535703704282067755673007817) (k_lb := 471203) (M_pre := 6433782848) (M_post := 5783603075788347)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb0
      (f_mono_inc_range 113 50 c 150 (by omega) hb0 (by decide) (by decide)) u_le_152 u_le_149 u_ge_150 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 479493) (a := 29) (s := 14) (by decide) u_ge_29).mono_exp (by decide)) u_ge_115 (by decide)
      ((log2Le_of_mul_two_pow (x := 958986) (b := 30) (s := 15) (by decide) u_le_30).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 113) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 75) (a := 18) (s := 2) (by decide) u_ge_18) log2Le_22 (by decide)) u_le_149 u_ge_152 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 113 50 52525744 d → 364417 ≤ d := by
      intro hr
      have hd0 : 43011 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 308977 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 43012) (a := 21) (s := 11) (by decide) u_ge_21) (by decide)
      have hd2 : 360307 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 308978) (a := 18) (s := 14) (by decide) u_ge_18) (by decide)
      have hd3 : 364417 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 360308) (a := 21) (s := 14) (by decide) u_ge_21) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 151) (c_hi := 188) (c_g := 188) (G := 52525744) (d_lb := 364417) (ld_lb := 79282655104) (pen_Q := 230102) (Lw := 62340256774) (k_lb0 := 265854) (BL := 22150774067) (S := 98617381) (R := 23456570399873132447529697874940746647) (k_lb := 392368) (M_pre := 6433782848) (M_post := 5783603075788347)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb1
      (f_mono_inc_range 113 50 c 188 (by omega) hb1 (by decide) (by decide)) u_le_190 u_le_187 u_ge_188 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 364418) (a := 22) (s := 14) (by decide) u_ge_22).mono_exp (by decide)) u_ge_153 (by decide)
      ((log2Le_of_mul_two_pow (x := 728836) (b := 23) (s := 15) (by decide) u_le_23).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 151) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 101) (a := 25) (s := 2) (by decide) u_ge_25) log2Le_22 (by decide)) u_le_187 u_ge_190 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 113 50 54754956 d → 349580 ≤ d := by
      intro hr
      have hd0 : 41260 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 295150 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 41261) (a := 20) (s := 11) (by decide) u_ge_20) (by decide)
      have hd2 : 345638 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 295151) (a := 18) (s := 14) (by decide) u_ge_18) (by decide)
      have hd3 : 349580 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 345639) (a := 21) (s := 14) (by decide) u_ge_21) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 189) (c_hi := 226) (c_g := 226) (G := 54754956) (d_lb := 349580) (ld_lb := 78994401828) (pen_Q := 239081) (Lw := 65089378927) (k_lb0 := 266277) (BL := 23483674736) (S := 82071769) (R := 20421293627698448832533029735984203294) (k_lb := 394943) (M_pre := 6433782848) (M_post := 5783603075788347)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb2
      (f_mono_inc_range 113 50 c 226 (by omega) hb2 (by decide) (by decide)) u_le_228 u_le_225 u_ge_226 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 349581) (a := 21) (s := 14) (by decide) u_ge_21).mono_exp (by decide)) u_ge_191 (by decide)
      ((log2Le_of_mul_two_pow (x := 699162) (b := 22) (s := 15) (by decide) u_le_22).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 189) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 125) (a := 31) (s := 2) (by decide) u_ge_31) log2Le_22 (by decide)) u_le_225 u_ge_228 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 113 50 54753808 d → 349588 ≤ d := by
      intro hr
      have hd0 : 41261 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 295156 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 41262) (a := 20) (s := 11) (by decide) u_ge_20) (by decide)
      have hd2 : 345645 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 295157) (a := 18) (s := 14) (by decide) u_ge_18) (by decide)
      have hd3 : 349588 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 345646) (a := 21) (s := 14) (by decide) u_ge_21) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 227) (c_hi := 275) (c_g := 227) (G := 54753808) (d_lb := 349588) (ld_lb := 78994401828) (pen_Q := 239075) (Lw := 67338008717) (k_lb0 := 275482) (BL := 24410222408) (S := 67474292) (R := 17402948812632917889346950811699453151) (k_lb := 409227) (M_pre := 6433782848) (M_post := 5783603075788347)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb3
      (f_mono_dec_range 113 50 227 c (by decide) (by omega) (by decide) (by decide)) u_le_229 u_le_226 u_ge_227 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 349589) (a := 21) (s := 14) (by decide) u_ge_21).mono_exp (by decide)) u_ge_229 (by decide)
      ((log2Le_of_mul_two_pow (x := 699178) (b := 22) (s := 15) (by decide) u_le_22).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 227) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 151) (a := 18) (s := 3) (by decide) u_ge_18) log2Le_22 (by decide)) u_le_274 u_ge_277 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 113 50 52962352 d → 361412 ≤ d := by
      intro hr
      have hd0 : 42656 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 305140 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 42657) (a := 20) (s := 11) (by decide) u_ge_20) (by decide)
      have hd2 : 357337 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 305141) (a := 18) (s := 14) (by decide) u_ge_18) (by decide)
      have hd3 : 361412 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 357338) (a := 21) (s := 14) (by decide) u_ge_21) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 276) (c_hi := 339) (c_g := 276) (G := 52962352) (d_lb := 361412) (ld_lb := 79282655104) (pen_Q := 232016) (Lw := 69740940754) (k_lb0 := 294963) (BL := 25653643861) (S := 54754358) (R := 14752918598189976536964653118233594341) (k_lb := 440276) (M_pre := 6433782848) (M_post := 5783603075788347)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb4
      (f_mono_dec_range 113 50 276 c (by decide) (by omega) (by decide) (by decide)) u_le_278 u_le_275 u_ge_276 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 361413) (a := 22) (s := 14) (by decide) u_ge_22).mono_exp (by decide)) u_ge_278 (by decide)
      ((log2Le_of_mul_two_pow (x := 722826) (b := 23) (s := 15) (by decide) u_le_23).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 276) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 183) (a := 22) (s := 3) (by decide) u_ge_22) log2Le_22 (by decide)) u_le_338 u_ge_341 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 113 50 48611360 d → 396381 ≤ d := by
      intro hr
      have hd0 : 46474 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 335198 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 46475) (a := 22) (s := 11) (by decide) u_ge_22) (by decide)
      have hd2 : 392355 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 335199) (a := 20) (s := 14) (by decide) u_ge_20) (by decide)
      have hd3 : 396381 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 392356) (a := 23) (s := 14) (by decide) u_ge_23) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 340) (c_hi := 429) (c_g := 340) (G := 48611360) (d_lb := 396381) (ld_lb := 79821806137) (pen_Q := 212851) (Lw := 72308589655) (k_lb0 := 333196) (BL := 27147963071) (S := 43280697) (R := 12255736702812424873407119229625933601) (k_lb := 500737) (M_pre := 6433782848) (M_post := 5783603075788347)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb5
      (f_mono_dec_range 113 50 340 c (by decide) (by omega) (by decide) (by decide)) u_le_342 u_le_339 u_ge_340 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 396382) (a := 24) (s := 14) (by decide) u_ge_24).mono_exp (by decide)) u_ge_342 (by decide)
      ((log2Le_of_mul_two_pow (x := 792764) (b := 25) (s := 15) (by decide) u_le_25).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 340) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 227) (a := 28) (s := 3) (by decide) u_ge_28) log2Le_22 (by decide)) u_le_428 u_ge_431 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 113 50 42449928 d → 459204 ≤ d := by
      intro hr
      have hd0 : 53220 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 388067 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 53221) (a := 25) (s := 11) (by decide) u_ge_25) (by decide)
      have hd2 : 453915 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 388068) (a := 23) (s := 14) (by decide) u_ge_23) (by decide)
      have hd3 : 459204 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 453916) (a := 27) (s := 14) (by decide) u_ge_27) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 430) (c_hi := 576) (c_g := 430) (G := 42449928) (d_lb := 459204) (ld_lb := 80776974314) (pen_Q := 185734) (Lw := 75203725268) (k_lb0 := 396835) (BL := 28351017423) (S := 32244623) (R := 9620639840484623707162690710655320131) (k_lb := 597196) (M_pre := 6433782848) (M_post := 5783603075788347)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb6
      (f_mono_dec_range 113 50 430 c (by decide) (by omega) (by decide) (by decide)) u_le_432 u_le_429 u_ge_430 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 459205) (a := 28) (s := 14) (by decide) u_ge_28).mono_exp (by decide)) u_ge_432 (by decide)
      ((log2Le_of_mul_two_pow (x := 918410) (b := 29) (s := 15) (by decide) u_le_29).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 430) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 287) (a := 17) (s := 4) (by decide) u_ge_17) log2Le_22 (by decide)) u_le_575 u_ge_578 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 113 50 34516008 d → 574110 ≤ d := by
      intro hr
      have hd0 : 65453 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 485996 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 65454) (a := 31) (s := 11) (by decide) u_ge_31) (by decide)
      have hd2 : 567657 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 485997) (a := 29) (s := 14) (by decide) u_ge_29) (by decide)
      have hd3 : 574110 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 567658) (a := 17) (s := 15) (by decide) u_ge_17) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 577) (c_hi := 836) (c_g := 577) (G := 34516008) (d_lb := 574110) (ld_lb := 81980028666) (pen_Q := 150893) (Lw := 78833282661) (k_lb0 := 511607) (BL := 30487762190) (S := 22222359) (R := 7112723504062589656203003211823102164) (k_lb := 776595) (M_pre := 6433782848) (M_post := 5783603075788347)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb7
      (f_mono_dec_range 113 50 577 c (by decide) (by omega) (by decide) (by decide)) u_le_579 u_le_576 u_ge_577 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 574111) (a := 17) (s := 15) (by decide) u_ge_17).mono_exp (by decide)) u_ge_579 (by decide)
      ((log2Le_of_mul_two_pow (x := 1148222) (b := 18) (s := 16) (by decide) u_le_18).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 577) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 385) (a := 24) (s := 4) (by decide) u_ge_24) log2Le_22 (by decide)) u_le_835 u_ge_838 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 113 50 25599960 d → 790599 ≤ d := by
      intro hr
      have hd0 : 88249 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 671873 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 88250) (a := 21) (s := 12) (by decide) u_ge_21) (by decide)
      have hd2 : 782953 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 671874) (a := 20) (s := 15) (by decide) u_ge_20) (by decide)
      have hd3 : 790599 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 782954) (a := 23) (s := 15) (by decide) u_ge_23) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 837) (c_hi := 1356) (c_g := 837) (G := 25599960) (d_lb := 790599) (ld_lb := 84116773433) (pen_Q := 112149) (Lw := 83429859507) (k_lb0 := 730012) (BL := 32645984719) (S := 13703642) (R := 4778228315857217516892698189985277051) (k_lb := 1112583) (M_pre := 6433782848) (M_post := 5783603075788347)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb8
      (f_mono_dec_range 113 50 837 c (by decide) (by omega) (by decide) (by decide)) u_le_839 u_le_836 u_ge_837 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 790600) (a := 24) (s := 15) (by decide) u_ge_24).mono_exp (by decide)) u_ge_839 (by decide)
      ((log2Le_of_mul_two_pow (x := 1581200) (b := 25) (s := 16) (by decide) u_le_25).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 837) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 557) (a := 17) (s := 5) (by decide) u_ge_17) log2Le_22 (by decide)) u_le_1355 u_ge_1358 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : TailRoundBound Q_SCALE 113 50 (3 * (4 * 113 - 9 * 50) * Q_SCALE) c d → 1090124 ≤ d := by
      intro hr
      have hd0 : 118964 ≤ d := tail_d_boot (c_lo := 1357) (by omega) hr hd_pos u_ge_2 (by decide)
      have hd1 : 929524 ≤ d := tail_d_boot (c_lo := 1357) (by omega) hr hd0 (log2Ge_of_mul_two_pow (x := 118965) (a := 29) (s := 12) (by decide) u_ge_29) (by decide)
      have hd2 : 1080277 ≤ d := tail_d_boot (c_lo := 1357) (by omega) hr hd1 (log2Ge_of_mul_two_pow (x := 929525) (a := 28) (s := 15) (by decide) u_ge_28) (by decide)
      have hd3 : 1090124 ≤ d := tail_d_boot (c_lo := 1357) (by omega) hr hd2 (log2Ge_of_mul_two_pow (x := 1080278) (a := 16) (s := 16) (by decide) u_ge_16) (by decide)
      exact hd3
    exact tail_step_of_log2 (Q := Q_SCALE) (c_lo := 1357) (d_lb := 1090124) (ld_lb := 85899345920) (pen_Q := 83083) (Lw := 89406788601) (BL := 35737897663) (k_lb := 1619170) (M_pre := 6433782848) (M_post := 5783603075788347)
      (by decide) hV (by decide) (by decide) (by decide) (by omega) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 1090125) (a := 16) (s := 16) (by decide) u_ge_16).mono_exp (by decide)) u_ge_1359 (by decide)
      ((log2Le_of_mul_two_pow (x := 2180250) (b := 17) (s := 17) (by decide) u_le_17).mono_exp (by decide)) (by decide)
      (fun c' k' hc' hk' => tail_cb_univ (p := 113) (q := 50) (Lw := 89406788601) (c_lo := 1357) (by decide) hc' hk' (by decide) (by decide) (log2Ge_of_mul_two_pow (x := 905) (a := 28) (s := 5) (by decide) u_ge_28) log2Le_22 (by decide)) (by decide) (by decide) (by decide) (by decide)

theorem universal_vk_lb_2260 {c d k : Nat} (hV : ValidPassTriple 113 50 c d k) :
    10 ^ 6433782848 < v_k_pass c d k :=
  (universal_both_2260 hV).1

theorem universal_post_bini_lb_2260 {c d k h : Nat} (hPB : ValidPostBini 113 50 c d k h) :
    10 ^ 5783603075788347 < (v_k_pass c d k) ^ h :=
  (universal_both_2260 hPB.1).2 h hPB

private theorem universal_both_2251 {c d k : Nat} (hV : ValidPassTriple 2251 1000 c d k) :
    10 ^ 12383220964975 < v_k_pass c d k ∧
    (∀ h, ValidPostBini 2251 1000 c d k h → 10 ^ 1594546546944094792315 < (v_k_pass c d k) ^ h) := by
  have hc_min : 1126 ≤ c := universal_c_min_2251 hV
  have hd_pos : 1 ≤ d := hV.2.1
  refine if hb0 : c ≤ 1501 then ?_ else if hb1 : c ≤ 1876 then ?_ else if hb2 : c ≤ 2251 then ?_ else if hb3 : c ≤ 2746 then ?_ else if hb4 : c ≤ 3376 then ?_ else if hb5 : c ≤ 4276 then ?_ else if hb6 : c ≤ 5740 then ?_ else if hb7 : c ≤ 8328 then ?_ else if hb8 : c ≤ 13506 then ?_ else ?_
  · have hd_lb : RoundBound Q_SCALE 2251 1000 8271088 d → 63680130 ≤ d := by
      intro hr
      have hd0 : 5453424 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 55299295 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 5453425) (a := 20) (s := 18) (by decide) u_ge_20) (by decide)
      have hd2 : 63197495 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 55299296) (a := 26) (s := 21) (by decide) u_ge_26) (by decide)
      have hd3 : 63680130 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 63197496) (a := 30) (s := 21) (by decide) u_ge_30) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 1126) (c_hi := 1501) (c_g := 1501) (G := 8271088) (d_lb := 63680130) (ld_lb := 111269247849) (pen_Q := 1818) (Lw := 87098081090) (k_lb0 := 47365856) (BL := 34519016155) (S := 12380279) (R := 46866119266993638049068122838884174357790) (k_lb := 72406588) (M_pre := 12383220964975) (M_post := 1594546546944094792315)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb0
      (f_mono_inc_range 2251 1000 c 1501 (by omega) hb0 (by decide) (by decide)) u_le_1503 u_le_1500 u_ge_1501 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 63680131) (a := 30) (s := 21) (by decide) u_ge_30).mono_exp (by decide)) u_ge_1128 (by decide)
      ((log2Le_of_mul_two_pow (x := 127360262) (b := 31) (s := 22) (by decide) u_le_31).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 1126) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 751) (a := 23) (s := 5) (by decide) u_ge_23) log2Le_22 (by decide)) u_le_1500 u_ge_1503 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2251 1000 10572500 d → 49117233 ≤ d := by
      intro hr
      have hd0 : 4266328 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 42673024 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 4266329) (a := 16) (s := 18) (by decide) u_ge_16) (by decide)
      have hd2 : 48748466 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 42673025) (a := 20) (s := 21) (by decide) u_ge_20) (by decide)
      have hd3 : 49117233 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 48748467) (a := 23) (s := 21) (by decide) u_ge_23) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 1502) (c_hi := 1876) (c_g := 1876) (G := 10572500) (d_lb := 49117233) (ld_lb := 109622863878) (pen_Q := 2325) (Lw := 90663225555) (k_lb0 := 38572067) (BL := 36368576624) (S := 9906201) (R := 38649889514099129161238520271197607459370) (k_lb := 59211600) (M_pre := 12383220964975) (M_post := 1594546546944094792315)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb1
      (f_mono_inc_range 2251 1000 c 1876 (by omega) hb1 (by decide) (by decide)) u_le_1878 u_le_1875 u_ge_1876 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 49117234) (a := 23) (s := 21) (by decide) u_ge_23).mono_exp (by decide)) u_ge_1504 (by decide)
      ((log2Le_of_mul_two_pow (x := 98234468) (b := 24) (s := 22) (by decide) u_le_24).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 1502) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 1001) (a := 31) (s := 5) (by decide) u_ge_31) log2Le_22 (by decide)) u_le_1875 u_ge_1878 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2251 1000 11016828 d → 47023692 ≤ d := by
      intro hr
      have hd0 : 4094259 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 40871555 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 4094260) (a := 31) (s := 17) (by decide) u_ge_31) (by decide)
      have hd2 : 46652475 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 40871556) (a := 19) (s := 21) (by decide) u_ge_19) (by decide)
      have hd3 : 47023692 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 46652476) (a := 22) (s := 21) (by decide) u_ge_22) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 1877) (c_hi := 2251) (c_g := 2251) (G := 11016828) (d_lb := 47023692) (ld_lb := 109347426176) (pen_Q := 2423) (Lw := 93421973143) (k_lb0 := 38142742) (BL := 37630142535) (S := 8256267) (R := 33162381954934963176890513739028507035866) (k_lb := 58636922) (M_pre := 12383220964975) (M_post := 1594546546944094792315)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb2
      (f_mono_inc_range 2251 1000 c 2251 (by omega) hb2 (by decide) (by decide)) u_le_2253 u_le_2250 u_ge_2251 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 47023693) (a := 22) (s := 21) (by decide) u_ge_22).mono_exp (by decide)) u_ge_1879 (by decide)
      ((log2Le_of_mul_two_pow (x := 94047386) (b := 23) (s := 22) (by decide) u_le_23).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 1877) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 1251) (a := 19) (s := 6) (by decide) u_ge_19) log2Le_22 (by decide)) u_le_2250 u_ge_2253 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2251 1000 11016056 d → 47026987 ≤ d := by
      intro hr
      have hd0 : 4094546 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 40874419 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 4094547) (a := 31) (s := 17) (by decide) u_ge_31) (by decide)
      have hd2 : 46655744 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 40874420) (a := 19) (s := 21) (by decide) u_ge_19) (by decide)
      have hd3 : 47026987 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 46655745) (a := 22) (s := 21) (by decide) u_ge_22) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 2252) (c_hi := 2746) (c_g := 2252) (G := 11016056) (d_lb := 47026987) (ld_lb := 109347426176) (pen_Q := 2423) (Lw := 95677023807) (k_lb0 := 39066182) (BL := 38813983451) (S := 6768244) (R := 27912441973866348215629014185371398304876) (k_lb := 60206588) (M_pre := 12383220964975) (M_post := 1594546546944094792315)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb3
      (f_mono_dec_range 2251 1000 2252 c (by decide) (by omega) (by decide) (by decide)) u_le_2254 u_le_2251 u_ge_2252 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 47026988) (a := 22) (s := 21) (by decide) u_ge_22).mono_exp (by decide)) u_ge_2254 (by decide)
      ((log2Le_of_mul_two_pow (x := 94053976) (b := 23) (s := 22) (by decide) u_le_23).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 2252) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 1501) (a := 23) (s := 6) (by decide) u_ge_23) log2Le_22 (by decide)) u_le_2745 u_ge_2748 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2251 1000 10655804 d → 48733248 ≤ d := by
      intro hr
      have hd0 : 4232975 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 42339419 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 4232976) (a := 16) (s := 18) (by decide) u_ge_16) (by decide)
      have hd2 : 48367365 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 42339420) (a := 20) (s := 21) (by decide) u_ge_20) (by decide)
      have hd3 : 48733248 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 48367366) (a := 23) (s := 21) (by decide) u_ge_23) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 2747) (c_hi := 3376) (c_g := 2747) (G := 10655804) (d_lb := 48733248) (ld_lb := 109622863878) (pen_Q := 2343) (Lw := 98137347725) (k_lb0 := 41425479) (BL := 40032864959) (S := 5505400) (R := 23390462080305521514860727267953776362009) (k_lb := 63966921) (M_pre := 12383220964975) (M_post := 1594546546944094792315)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb4
      (f_mono_dec_range 2251 1000 2747 c (by decide) (by omega) (by decide) (by decide)) u_le_2749 u_le_2746 u_ge_2747 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 48733249) (a := 23) (s := 21) (by decide) u_ge_23).mono_exp (by decide)) u_ge_2749 (by decide)
      ((log2Le_of_mul_two_pow (x := 97466498) (b := 24) (s := 22) (by decide) u_le_24).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 2747) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 1831) (a := 28) (s := 6) (by decide) u_ge_28) log2Le_22 (by decide)) u_le_3375 u_ge_3378 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2251 1000 9790552 d → 53277685 ≤ d := by
      intro hr
      have hd0 : 4607069 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 46253952 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 4607070) (a := 17) (s := 18) (by decide) u_ge_17) (by decide)
      have hd2 : 52913454 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 46253953) (a := 22) (s := 21) (by decide) u_ge_22) (by decide)
      have hd3 : 53277685 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 52913455) (a := 25) (s := 21) (by decide) u_ge_25) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 3377) (c_hi := 4276) (c_g := 3377) (G := 9790552) (d_lb := 53277685) (ld_lb := 110139523678) (pen_Q := 2153) (Lw := 100694480765) (k_lb0 := 46261311) (BL := 41235919311) (S := 4346774) (R := 19060906771687398393605225186950840005685) (k_lb := 71532155) (M_pre := 12383220964975) (M_post := 1594546546944094792315)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb5
      (f_mono_dec_range 2251 1000 3377 c (by decide) (by omega) (by decide) (by decide)) u_le_3379 u_le_3376 u_ge_3377 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 53277686) (a := 25) (s := 21) (by decide) u_ge_25).mono_exp (by decide)) u_ge_3379 (by decide)
      ((log2Le_of_mul_two_pow (x := 106555372) (b := 26) (s := 22) (by decide) u_le_26).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 3377) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 2251) (a := 17) (s := 7) (by decide) u_ge_17) log2Le_22 (by decide)) u_le_4275 u_ge_4278 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2251 1000 8548340 d → 61504134 ≤ d := by
      intro hr
      have hd0 : 5276551 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 53505749 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 5276552) (a := 20) (s := 18) (by decide) u_ge_20) (by decide)
      have hd2 : 61019794 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 53505750) (a := 25) (s := 21) (by decide) u_ge_25) (by decide)
      have hd3 : 61504134 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 61019795) (a := 29) (s := 21) (by decide) u_ge_29) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 4277) (c_hi := 5740) (c_g := 4277) (G := 8548340) (d_lb := 61504134) (ld_lb := 111059182714) (pen_Q := 1879) (Lw := 103620877007) (k_lb0 := 54523650) (BL := 42833513045) (S := 3238216) (R := 14778191654756460762389615425521511763422) (k_lb := 84588093) (M_pre := 12383220964975) (M_post := 1594546546944094792315)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb6
      (f_mono_dec_range 2251 1000 4277 c (by decide) (by omega) (by decide) (by decide)) u_le_4279 u_le_4276 u_ge_4277 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 61504135) (a := 29) (s := 21) (by decide) u_ge_29).mono_exp (by decide)) u_ge_4279 (by decide)
      ((log2Le_of_mul_two_pow (x := 123008270) (b := 30) (s := 22) (by decide) u_le_30).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 4277) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 2851) (a := 22) (s := 7) (by decide) u_ge_22) log2Le_22 (by decide)) u_le_5739 u_ge_5742 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2251 1000 6955996 d → 76450587 ≤ d := by
      intro hr
      have hd0 : 6484442 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 66485281 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 6484443) (a := 24) (s := 18) (by decide) u_ge_24) (by decide)
      have hd2 : 75850915 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 66485282) (a := 31) (s := 21) (by decide) u_ge_31) (by decide)
      have hd3 : 76450587 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 75850916) (a := 18) (s := 22) (by decide) u_ge_18) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 5741) (c_hi := 8328) (c_g := 5741) (G := 6955996) (d_lb := 76450587) (ld_lb := 112398972019) (pen_Q := 1531) (Lw := 107267569871) (k_lb0 := 69363111) (BL := 44545269583) (S := 2231971) (R := 10683615052279245559654692808033168089983) (k_lb := 107786310) (M_pre := 12383220964975) (M_post := 1594546546944094792315)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb7
      (f_mono_dec_range 2251 1000 5741 c (by decide) (by omega) (by decide) (by decide)) u_le_5743 u_le_5740 u_ge_5741 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 76450588) (a := 18) (s := 22) (by decide) u_ge_18).mono_exp (by decide)) u_ge_5743 (by decide)
      ((log2Le_of_mul_two_pow (x := 152901176) (b := 19) (s := 23) (by decide) u_le_19).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 5741) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 3827) (a := 29) (s := 7) (by decide) u_ge_29) log2Le_22 (by decide)) u_le_8327 u_ge_8330 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : RoundBound Q_SCALE 2251 1000 5155860 d → 104699336 ≤ d := by
      intro hr
      have hd0 : 8748443 ≤ d := d_boot hr hd_pos u_ge_2 (by decide)
      have hd1 : 91254706 ≤ d := d_boot hr hd0 (log2Ge_of_mul_two_pow (x := 8748444) (a := 16) (s := 19) (by decide) u_ge_16) (by decide)
      have hd2 : 103976862 ≤ d := d_boot hr hd1 (log2Ge_of_mul_two_pow (x := 91254707) (a := 21) (s := 22) (by decide) u_ge_21) (by decide)
      have hd3 : 104699336 ≤ d := d_boot hr hd2 (log2Ge_of_mul_two_pow (x := 103976863) (a := 24) (s := 22) (by decide) u_ge_24) (by decide)
      exact hd3
    exact band_step_of_log2 (Q := Q_SCALE) (c_lo := 8329) (c_hi := 13506) (c_g := 8329) (G := 5155860) (d_lb := 104699336) (ld_lb := 114181544505) (pen_Q := 1135) (Lw := 111877660311) (k_lb0 := 97602672) (BL := 46840227065) (S := 1376299) (R := 6995610224755724416700562992153286482191) (k_lb := 152111787) (M_pre := 12383220964975) (M_post := 1594546546944094792315)
      (by decide) hV (by decide) (by decide) (by decide) (by decide) (by omega) hb8
      (f_mono_dec_range 2251 1000 8329 c (by decide) (by omega) (by decide) (by decide)) u_le_8331 u_le_8328 u_ge_8329 (by decide) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 104699337) (a := 24) (s := 22) (by decide) u_ge_24).mono_exp (by decide)) u_ge_8331 (by decide)
      ((log2Le_of_mul_two_pow (x := 209398674) (b := 25) (s := 23) (by decide) u_le_25).mono_exp (by decide)) (by decide) (by decide)
      (fun hk0 => cb_univ (c_lo := 8329) (by decide) (by omega) (by omega) (log2Ge_of_mul_two_pow (x := 5553) (a := 21) (s := 8) (by decide) u_ge_21) log2Le_22 (by decide)) u_le_13505 u_ge_13508 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hd_lb : TailRoundBound Q_SCALE 2251 1000 (3 * (4 * 2251 - 9 * 1000) * Q_SCALE) c d → 144015864 ≤ d := by
      intro hr
      have hd0 : 11820877 ≤ d := tail_d_boot (c_lo := 13507) (by omega) hr hd_pos u_ge_2 (by decide)
      have hd1 : 125631265 ≤ d := tail_d_boot (c_lo := 13507) (by omega) hr hd0 (log2Ge_of_mul_two_pow (x := 11820878) (a := 22) (s := 19) (by decide) u_ge_22) (by decide)
      have hd2 : 142852993 ≤ d := tail_d_boot (c_lo := 13507) (by omega) hr hd1 (log2Ge_of_mul_two_pow (x := 125631266) (a := 29) (s := 22) (by decide) u_ge_29) (by decide)
      have hd3 : 144015864 ≤ d := tail_d_boot (c_lo := 13507) (by omega) hr hd2 (log2Ge_of_mul_two_pow (x := 142852994) (a := 17) (s := 23) (by decide) u_ge_17) (by decide)
      exact hd3
    exact tail_step_of_log2 (Q := Q_SCALE) (c_lo := 13507) (d_lb := 144015864) (ld_lb := 116339767034) (pen_Q := 841) (Lw := 117867931383) (BL := 49825853903) (k_lb := 217289051) (M_pre := 12383220964975) (M_post := 1594546546944094792315)
      (by decide) hV (by decide) (by decide) (by decide) (by omega) (by decide) hd_lb
      ((log2Ge_of_mul_two_pow (x := 144015865) (a := 17) (s := 23) (by decide) u_ge_17).mono_exp (by decide)) u_ge_13509 (by decide)
      ((log2Le_of_mul_two_pow (x := 288031730) (b := 18) (s := 24) (by decide) u_le_18).mono_exp (by decide)) (by decide)
      (fun c' k' hc' hk' => tail_cb_univ (p := 2251) (q := 1000) (Lw := 117867931383) (c_lo := 13507) (by decide) hc' hk' (by decide) (by decide) (log2Ge_of_mul_two_pow (x := 9005) (a := 17) (s := 9) (by decide) u_ge_17) log2Le_22 (by decide)) (by decide) (by decide) (by decide) (by decide)

theorem universal_vk_lb_2251 {c d k : Nat} (hV : ValidPassTriple 2251 1000 c d k) :
    10 ^ 12383220964975 < v_k_pass c d k :=
  (universal_both_2251 hV).1

theorem universal_post_bini_lb_2251 {c d k h : Nat} (hPB : ValidPostBini 2251 1000 c d k h) :
    10 ^ 1594546546944094792315 < (v_k_pass c d k) ^ h :=
  (universal_both_2251 hPB.1).2 h hPB

end MatMul94
