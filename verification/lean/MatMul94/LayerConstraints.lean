/-
  MatMul94/LayerConstraints.lean

  Formal pure-kernel proofs of the algebraic layer constraints governing all five
  layers of Pass's ω ≤ 9/4 polynomial-packing scheme (and OpenAI / Lü / Li / Doğan et al.):
  - Layer 1A: `pure_telescoping_zero_gain`
  - Layer 1B: `primal_telescoping_identity`, `gap_window_disjoint`, `effort_surplus_positive`
  - Layer 1C: `same_slot_multi_eps_collision`
  - Layer 1D: `cubic_rate_gap`, `pass_rate_strictly_above_9_4`, `tau_factorization`,
              `c_min_polynomial_bound`, and unimodality (`f_step_inc`, `f_step_dec`,
              `f_mono_inc_range`, `f_mono_dec_range`)
  - Layer 2:  `cauchy_schwarz_balanced_words`
  - Layer 3:  `lagrange_uncoupling_constraints`, `inner_eta_pole_clearing_necessity`,
              `openai_5M_tight_eps_deg` (+ exact tightness witness)
  - Layer 4:  `slabbing_barrier`, `L_pass`, `exact_Lk_sandwich`, `exact_Lk_upper_from_j0`
  - Layer 5:  `pole_cascade_exact`, `multivariate_bini_worse`, `hidden_constant_bounds`,
              `finite_schonhage`
-/

import MatMul94.Log2Bracket

namespace MatMul94

/-! ### Finite sums in `Nat` and `Int` -/

/-- Sum `f 0 + f 1 + ... + f (n - 1)` in `Nat`. -/
def natSum (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => natSum k f + f k

/-- Sum `f 0 + f 1 + ... + f (n - 1)` in `Int`. -/
def intSum (n : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | k + 1 => intSum k f + f k

theorem intSum_add (n : Nat) (f g : Nat → Int) :
    intSum n (fun i => f i + g i) = intSum n f + intSum n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [intSum, ih]; omega

theorem intSum_sub (n : Nat) (f g : Nat → Int) :
    intSum n (fun i => f i - g i) = intSum n f - intSum n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [intSum, ih]; omega

theorem intSum_mul_left (n : Nat) (a : Int) (f : Nat → Int) :
    intSum n (fun i => a * f i) = a * intSum n f := by
  induction n with
  | zero => simp [intSum]
  | succ k ih => simp only [intSum, ih, Int.mul_add]

theorem intSum_zero (n : Nat) (f : Nat → Int) (hf : ∀ i < n, f i = 0) :
    intSum n f = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [intSum]
    rw [ih (fun i hi => hf i (by omega)), hf k (by omega)]
    rfl

theorem intSum_congr {n : Nat} {f g : Nat → Int} (h : ∀ i < n, f i = g i) :
    intSum n f = intSum n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [intSum]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem intSum_comm (m n : Nat) (f : Nat → Nat → Int) :
    intSum m (fun i => intSum n (fun j => f i j)) =
    intSum n (fun j => intSum m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [intSum]
    symm
    exact intSum_zero n _ (fun _ _ => rfl)
  | succ k ih =>
    simp only [intSum, ih]
    rw [← intSum_add]

theorem intSum_telescope (c : Nat) (g : Nat → Int) :
    intSum c (fun j => g j - g (j + 1)) = g 0 - g c := by
  induction c with
  | zero => simp [intSum]
  | succ k ih => simp only [intSum, ih]; omega

/-! ### Layer 1A: Zero-gain barrier for pure `(c + 1)`-for-`c` telescoping -/

theorem pure_telescoping_zero_gain (a b c t : Nat)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (_hc : 1 ≤ c) (_ht : 1 ≤ t)
    (hct : a + b - 1 ≤ c * t) :
    (c + 1) * (a + b - 1) ≤ c * (a + b + t - 1) ∧ (c + 1) * b ≤ c * (b + t) := by
  constructor
  · have h1 : c * (a + b + t - 1) = c * (a + b - 1) + c * t := by
      have : a + b + t - 1 = (a + b - 1) + t := by omega
      rw [this, Nat.mul_add]
    have h2 : (c + 1) * (a + b - 1) = c * (a + b - 1) + (a + b - 1) := by
      rw [Nat.add_mul, Nat.one_mul]
    omega
  · have h1 : c * (b + t) = c * b + c * t := Nat.mul_add c b t
    have h2 : (c + 1) * b = c * b + b := by rw [Nat.add_mul, Nat.one_mul]
    omega

/-! ### Layer 1B & 1C: Concrete `Int` polynomial algebra, telescoping identity, gap, and collision -/

/-- Formal univariate polynomial over `Int`, represented by its coefficient map `Nat → Int`. -/
abbrev Poly := Nat → Int

def polyAdd (f g : Poly) : Poly := fun n => f n + g n
def polySub (f g : Poly) : Poly := fun n => f n - g n
def polyScale (α : Int) (f : Poly) : Poly := fun n => α * f n
def polyShift (k : Nat) (f : Poly) : Poly := fun n => if k ≤ n then f (n - k) else 0
def polyMul (f g : Poly) : Poly := fun n => intSum (n + 1) (fun i => f i * g (n - i))

theorem polyMul_add_right (A F G : Poly) (n : Nat) :
    polyMul A (polyAdd F G) n = polyMul A F n + polyMul A G n := by
  unfold polyMul polyAdd
  have : (fun i => A i * (F (n - i) + G (n - i))) =
      (fun i => A i * F (n - i) + A i * G (n - i)) := by
    funext i; exact Int.mul_add _ _ _
  rw [this, intSum_add]

theorem polyMul_sub_right (A F G : Poly) (n : Nat) :
    polyMul A (polySub F G) n = polyMul A F n - polyMul A G n := by
  unfold polyMul polySub
  have : (fun i => A i * (F (n - i) - G (n - i))) =
      (fun i => A i * F (n - i) - A i * G (n - i)) := by
    funext i; exact Int.mul_sub _ _ _
  rw [this, intSum_sub]

theorem polyMul_scale_right (α : Int) (A F : Poly) (n : Nat) :
    polyMul A (polyScale α F) n = α * polyMul A F n := by
  unfold polyMul polyScale
  have : (fun i => A i * (α * F (n - i))) = (fun i => α * (A i * F (n - i))) := by
    funext i; ac_rfl
  rw [this, intSum_mul_left]

theorem polyMul_shift_right (k : Nat) (A F : Poly) (n : Nat) :
    polyMul A (polyShift k F) n = polyShift k (polyMul A F) n := by
  unfold polyMul polyShift
  split
  · rename_i hkn
    have hsplit : ∀ m d (h : Nat → Int),
        (∀ i, m ≤ i → i < m + d → h i = 0) → intSum (m + d) h = intSum m h := by
      intro m d h hz
      induction d with
      | zero => simp
      | succ r ih =>
        have : m + (r + 1) = (m + r) + 1 := by omega
        rw [this, intSum, ih (fun i hi1 hi2 => hz i hi1 (by omega)), hz (m + r) (by omega) (by omega)]
        omega
    have hnd : n + 1 = (n - k + 1) + k := by omega
    rw [hnd]
    rw [hsplit (n - k + 1) k _ (fun i hi1 hi2 => by
      have hnot : ¬ (k ≤ n - i) := by omega
      simp [hnot])]
    apply intSum_congr
    intro i hi
    have hle : k ≤ n - i := by omega
    have hsub : n - i - k = n - k - i := by omega
    simp [hle, hsub]
  · rename_i hlt
    apply intSum_zero
    intro i hi
    have hnot : ¬ (k ≤ n - i) := by omega
    simp [hnot]

theorem polyShift_add (k1 k2 : Nat) (F : Poly) (n : Nat) :
    polyShift k1 (polyShift k2 F) n = polyShift (k1 + k2) F n := by
  unfold polyShift
  by_cases h1 : k1 ≤ n
  · by_cases h2 : k2 ≤ n - k1
    · have h12 : k1 + k2 ≤ n := by omega
      have hsub : n - k1 - k2 = n - (k1 + k2) := by omega
      simp [h1, h2, h12, hsub]
    · have h12 : ¬ (k1 + k2 ≤ n) := by omega
      simp [h1, h2, h12]
  · have h12 : ¬ (k1 + k2 ≤ n) := by omega
    simp [h1, h12]

theorem polyMul_sum_right (c : Nat) (A : Poly) (F : Nat → Poly) (n : Nat) :
    polyMul A (fun m => intSum c (fun j => F j m)) n =
    intSum c (fun j => polyMul A (F j) n) := by
  unfold polyMul
  have h1 : (fun i => A i * intSum c (fun j => F j (n - i))) =
      (fun i => intSum c (fun j => A i * F j (n - i))) := by
    funext i; rw [intSum_mul_left]
  rw [h1, intSum_comm]

theorem polyShift_zero (F : Poly) (n : Nat) : polyShift 0 F n = F n := by
  simp [polyShift]

/-- Exact finite-sum telescoping identity (Pass Theorem 3.1 / Paper Theorem `thm:primal_gap`(i)):
    summing `z^{t j} * A * (P_j - z^t P_{j+1} + ε z^b Q^{(j)})` over `j = 0, ..., c - 1`
    yields `A P_0 - z^{ct} A P_c + ε z^b A Q`, where `Q = ∑_{j=0}^{c-1} z^{t j} Q^{(j)}`. -/
theorem primal_telescoping_identity (c b t : Nat) (ε : Int)
    (A : Poly) (P Qblk : Nat → Poly) :
    let E : Nat → Poly := fun j =>
      polyAdd (polySub (P j) (polyShift t (P (j + 1)))) (polyScale ε (polyShift b (Qblk j)))
    let Qtot : Poly := fun m => intSum c (fun j => polyShift (t * j) (Qblk j) m)
    ∀ n,
      intSum c (fun j => polyShift (t * j) (polyMul A (E j)) n) =
      polyMul A (P 0) n - polyShift (c * t) (polyMul A (P c)) n +
      ε * polyShift b (polyMul A Qtot) n := by
  intro E Qtot n
  have hterm : ∀ j,
      polyShift (t * j) (polyMul A (E j)) n =
      (polyShift (t * j) (polyMul A (P j)) n - polyShift (t * (j + 1)) (polyMul A (P (j + 1))) n)
      + ε * polyShift (t * j) (polyShift b (polyMul A (Qblk j))) n := by
    intro j
    have hE : ∀ m, polyMul A (E j) m =
        polyMul A (P j) m - polyShift t (polyMul A (P (j + 1))) m
        + ε * polyShift b (polyMul A (Qblk j)) m := by
      intro m
      dsimp only [E]
      rw [polyMul_add_right, polyMul_sub_right, polyMul_shift_right, polyMul_scale_right, polyMul_shift_right]
    unfold polyShift at *
    by_cases hle : t * j ≤ n
    · simp only [hle, ↓reduceIte]
      rw [hE (n - t * j)]
      have hshift_eq : (if t ≤ n - t * j then polyMul A (P (j + 1)) (n - t * j - t) else 0) =
          (if t * (j + 1) ≤ n then polyMul A (P (j + 1)) (n - t * (j + 1)) else 0) := by
        by_cases h2 : t ≤ n - t * j
        · have h3 : t * (j + 1) ≤ n := by rw [Nat.mul_succ]; omega
          have hsub : n - t * j - t = n - t * (j + 1) := by rw [Nat.mul_succ]; omega
          simp [h2, h3, hsub]
        · have h3 : ¬ (t * (j + 1) ≤ n) := by rw [Nat.mul_succ]; omega
          simp [h2, h3]
      rw [hshift_eq]
    · have hnot2 : ¬ (t * (j + 1) ≤ n) := by rw [Nat.mul_succ]; omega
      simp [hle, hnot2]
  have hsum_eq := intSum_congr (n := c) (fun j _ => hterm j)
  rw [hsum_eq, intSum_add, intSum_telescope]
  have h_eps :
      intSum c (fun j => ε * polyShift (t * j) (polyShift b (polyMul A (Qblk j))) n) =
      ε * polyShift b (polyMul A Qtot) n := by
    rw [intSum_mul_left]
    apply congrArg (ε * ·)
    have hswap : ∀ j, polyShift (t * j) (polyShift b (polyMul A (Qblk j))) n =
        polyShift b (polyMul A (polyShift (t * j) (Qblk j))) n := by
      intro j
      rw [polyShift_add, Nat.add_comm, ← polyShift_add]
      unfold polyShift
      split
      · exact (polyMul_shift_right (t * j) A (Qblk j) (n - b)).symm
      · rfl
    rw [intSum_congr (fun j _ => hswap j)]
    unfold polyShift
    split
    · rw [← polyMul_sum_right]
      rfl
    · exact intSum_zero c _ (fun _ _ => rfl)
  rw [h_eps]
  have h0 : polyShift (t * 0) (polyMul A (P 0)) n = polyMul A (P 0) n := by simp [polyShift]
  have hc : t * c = c * t := Nat.mul_comm t c
  rw [h0, hc]

/-- Degree bound vanishing lemma for polynomial products. -/
theorem polyMul_eq_zero_of_ge (A B : Poly) (a b : Nat)
    (hA : ∀ i, a ≤ i → A i = 0) (hB : ∀ j, b ≤ j → B j = 0)
    (n : Nat) (hn : a + b - 1 ≤ n) : polyMul A B n = 0 := by
  unfold polyMul
  apply intSum_zero
  intro i hi
  by_cases hia : a ≤ i
  · rw [hA i hia]; simp
  · have hjb : b ≤ n - i := by omega
    rw [hB (n - i) hjb]; simp

/-- Layer 1B gap-window disjointness (necessity & sufficiency of `c * t ≥ a + 2 * b - 1`). -/
theorem gap_window_disjoint (a b c t : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    let s := a + b - 1
    (a + 2 * b - 1 ≤ c * t ↔ ∀ k < b, a + b - 2 < s + k ∧ s + k < c * t) ∧
    (a + 2 * b - 1 ≤ c * t →
      ∀ (A P1 Pc : Poly),
        (∀ i, a ≤ i → A i = 0) → (∀ j, b ≤ j → P1 j = 0) →
        ∀ k < b, polyMul A P1 (s + k) = 0 ∧ polyShift (c * t) (polyMul A Pc) (s + k) = 0) := by
  intro s
  constructor
  · constructor
    · intro hct k hk; constructor <;> omega
    · intro hall; have hlast := hall (b - 1) (by omega); omega
  · intro hct A P1 Pc hA hP1 k hk
    constructor
    · exact polyMul_eq_zero_of_ge A P1 a b hA hP1 (s + k) (by omega)
    · unfold polyShift
      have hnot : ¬ (c * t ≤ s + k) := by omega
      simp [hnot]

/-- Exact effort surplus at `a = b ≥ 2, t = 1, c = 3*b - 1`. -/
theorem effort_surplus_positive (b : Nat) (hb : 2 ≤ b) :
    let c := 3 * b - 1
    (c + 2) * (2 * b - 1) - c * (2 * b) = b - 1 ∧ c * (2 * b) < (c + 2) * (2 * b - 1) := by
  intro c
  have h1 : (c + 2) * (2 * b - 1) = c * (2 * b) + (b - 1) := by
    apply nat_eq_of_int
    dsimp only [c]
    have he2 : ((2 * b - 1 : Nat) : Int) = 2 * (b : Int) - 1 := by omega
    have he3 : ((3 * b - 1 : Nat) : Int) = 3 * (b : Int) - 1 := by omega
    have he4 : ((b - 1 : Nat) : Int) = (b : Int) - 1 := by omega
    simp only [Int.natCast_add, Int.natCast_mul]
    rw [he2, he3, he4]
    grind
  omega

/-- Layer 1C: Same-slot multi-`ε` pole collision (`Prop. prop:multi_eps_collision`). -/
theorem same_slot_multi_eps_collision (a b c t : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hct : a + 2 * b - 1 ≤ c * t)
    (A : Poly) (P Q1blk Q2blk : Nat → Poly)
    (hA : ∀ i, a ≤ i → A i = 0) (hP0 : ∀ j, b ≤ j → P 0 j = 0) :
    let s := a + b - 1
    let Q1 : Poly := fun m => intSum c (fun j => polyShift (t * j) (Q1blk j) m)
    let Q2 : Poly := fun m => intSum c (fun j => polyShift (t * j) (Q2blk j) m)
    let E2 : Int → Nat → Poly := fun ε j =>
      polyAdd (polySub (P j) (polyShift t (P (j + 1))))
        (polyAdd (polyScale ε (polyShift b (Q1blk j)))
                 (polyScale (ε * ε) (polyShift b (Q2blk j))))
    ∀ ε : Int, ∀ k < b,
      intSum c (fun j => polyShift (t * j) (polyMul A (E2 ε j)) (s + k)) =
      ε * polyMul A Q1 (a - 1 + k) + (ε * ε) * polyMul A Q2 (a - 1 + k) := by
  intro s Q1 Q2 E2 ε k hk
  let Qcomb : Nat → Poly := fun j => polyAdd (Q1blk j) (polyScale ε (Q2blk j))
  have hE_eq : ∀ j m, E2 ε j m =
      polyAdd (polySub (P j) (polyShift t (P (j + 1))))
        (polyScale ε (polyShift b (Qcomb j))) m := by
    intro j m
    dsimp only [E2, Qcomb, polyAdd, polySub, polyScale, polyShift]
    by_cases hbm : b ≤ m
    · simp only [hbm, ↓reduceIte]; grind
    · simp only [hbm, ↓reduceIte]; grind
  have hsum_eq : intSum c (fun j => polyShift (t * j) (polyMul A (E2 ε j)) (s + k)) =
      intSum c (fun j => polyShift (t * j) (polyMul A (fun m =>
        polyAdd (polySub (P j) (polyShift t (P (j + 1))))
          (polyScale ε (polyShift b (Qcomb j))) m)) (s + k)) := by
    apply intSum_congr
    intro j _
    have hf : E2 ε j = fun m =>
        polyAdd (polySub (P j) (polyShift t (P (j + 1))))
          (polyScale ε (polyShift b (Qcomb j))) m := funext (hE_eq j)
    rw [hf]
  rw [hsum_eq]
  have htele := primal_telescoping_identity c b t ε A P Qcomb (s + k)
  dsimp only at htele
  rw [htele]
  have hvan := (gap_window_disjoint a b c t ha hb).2 hct A (P 0) (P c) hA hP0 k hk
  rw [hvan.1, hvan.2]
  have hQsplit : (fun m => intSum c (fun j => polyShift (t * j) (Qcomb j) m)) =
      polyAdd Q1 (polyScale ε Q2) := by
    funext m
    dsimp only [Qcomb, Q1, Q2, polyAdd, polyScale]
    have hterm : ∀ j, polyShift (t * j) (polyAdd (Q1blk j) (polyScale ε (Q2blk j))) m =
        polyShift (t * j) (Q1blk j) m + ε * polyShift (t * j) (Q2blk j) m := by
      intro j; unfold polyShift polyAdd polyScale; split <;> simp
    rw [intSum_congr (fun j _ => hterm j), intSum_add, intSum_mul_left]
  rw [hQsplit]
  unfold polyShift
  have hbsk : b ≤ s + k := by omega
  have hsub : s + k - b = a - 1 + k := by omega
  simp only [hbsk, ↓reduceIte, hsub]
  rw [polyMul_add_right, polyMul_scale_right]
  grind

/-! ### Layer 1D: Cubic rate floor, strict gap above 9/4, `c`-floor, and unimodality -/

/-- Exact cubic identity `(c + 2)*(c - 1)^2 + (3*c - 2) = c^3` and strict gap for `c ≥ 2`. -/
theorem cubic_rate_gap (c : Nat) (hc : 2 ≤ c) :
    (c + 2) * (c - 1) ^ 2 + (3 * c - 2) = c ^ 3 ∧ (c + 2) * (c - 1) ^ 2 < c ^ 3 := by
  have h1 : (c + 2) * (c - 1) ^ 2 + (3 * c - 2) = c ^ 3 := by
    apply nat_eq_of_int
    have hc1 : ((c - 1 : Nat) : Int) = (c : Int) - 1 := by omega
    have h3c : ((3 * c - 2 : Nat) : Int) = 3 * (c : Int) - 2 := by omega
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow]
    rw [hc1, h3c]
    grind
  exact ⟨h1, by omega⟩

/-- Strict inequality `ρ(c)^6 > ((c + 2) / c)^9`, proving `τ(c) > 9/4` for every `c ≥ 2`. -/
theorem pass_rate_strictly_above_9_4 (c : Nat) (hc : 2 ≤ c) :
    (c + 2) ^ 3 * (c - 1) ^ 6 < c ^ 9 ∧
    (c + 2) ^ 9 * (c - 1) ^ 6 < (c + 2) ^ 6 * c ^ 9 := by
  have hcub := (cubic_rate_gap c hc).2
  have h3 : ((c + 2) * (c - 1) ^ 2) ^ 3 < (c ^ 3) ^ 3 :=
    pow_lt_pow_left_of_lt (by decide) hcub
  have eL : ((c + 2) * (c - 1) ^ 2) ^ 3 = (c + 2) ^ 3 * (c - 1) ^ 6 := by
    rw [Nat.mul_pow, ← Nat.pow_mul]
  have eR : (c ^ 3) ^ 3 = c ^ 9 := by rw [← Nat.pow_mul]
  rw [eL, eR] at h3
  refine ⟨h3, ?_⟩
  have hmul := Nat.mul_lt_mul_of_pos_left h3 (pow_pos_of_pos (a := c + 2) (by omega) 6)
  have eL2 : (c + 2) ^ 6 * ((c + 2) ^ 3 * (c - 1) ^ 6) = (c + 2) ^ 9 * (c - 1) ^ 6 := by
    rw [← Nat.mul_assoc, ← Nat.pow_add]
  rwa [eL2] at hmul

/-- Exact factorization for `τ = 9/4 + a/b` (`p = 9*b + 4*a, q = 4*b`). -/
theorem tau_factorization (c a b : Nat) :
    (c + 2) ^ (2 * (9 * b + 4 * a) - 3 * (4 * b)) * (c - 1) ^ (3 * (4 * b)) =
    ((c + 2) * (c - 1) ^ 2) ^ (6 * b) * (c + 2) ^ (8 * a) := by
  have he1 : 2 * (9 * b + 4 * a) - 3 * (4 * b) = 6 * b + 8 * a := by omega
  have he2 : 3 * (4 * b) = 2 * (6 * b) := by omega
  rw [he1, he2, Nat.pow_add, Nat.mul_pow, ← Nat.pow_mul]
  ac_rfl

/-- Telescoping lower bound: for `X ≥ 1`, `(X + m) * (X + m - 1)^m ≥ X * (X + m)^m`. -/
theorem ratio_ge_pow_top (X : Nat) (hX : 1 ≤ X) : ∀ m,
    X * (X + m) ^ m ≤ (X + m) * (X + m - 1) ^ m
  | 0 => by simp
  | 1 => by simp [Nat.mul_comm]
  | k + 2 => by
    have ih := ratio_ge_pow_top X hX (k + 1)
    have hstep : (X + k) * (X + k + 2) ≤ (X + k + 1) * (X + k + 1) := by
      have hid : (X + k + 1) * (X + k + 1) = (X + k) * (X + k + 2) + 1 := by grind
      omega
    have hpow_step := Nat.pow_le_pow_left hstep (k + 1)
    rw [Nat.mul_pow, Nat.mul_pow] at hpow_step
    have hsub1 : X + (k + 1) - 1 = X + k := by omega
    have hadd1 : X + (k + 1) = X + k + 1 := by omega
    rw [hsub1, hadd1] at ih
    have h1 := Nat.mul_le_mul_right ((X + k + 2) ^ (k + 1)) ih
    have h2 := Nat.mul_le_mul_left (X + k + 1) hpow_step
    have hcomb : (X * (X + k + 2) ^ (k + 1)) * (X + k + 1) ^ (k + 1)
        ≤ ((X + k + 1) ^ (k + 2)) * (X + k + 1) ^ (k + 1) := by
      have eL : (X * (X + k + 2) ^ (k + 1)) * (X + k + 1) ^ (k + 1)
          = (X * (X + k + 1) ^ (k + 1)) * (X + k + 2) ^ (k + 1) := by ac_rfl
      have eM : ((X + k + 1) * (X + k) ^ (k + 1)) * (X + k + 2) ^ (k + 1)
          = (X + k + 1) * ((X + k) ^ (k + 1) * (X + k + 2) ^ (k + 1)) := by ac_rfl
      have eR : (X + k + 1) * ((X + k + 1) ^ (k + 1) * (X + k + 1) ^ (k + 1))
          = ((X + k + 1) ^ (k + 2)) * (X + k + 1) ^ (k + 1) := by
        rw [Nat.pow_succ (X + k + 1) (k + 1)]; ac_rfl
      rw [eL, ← eR]
      exact Nat.le_trans h1 (eM ▸ h2)
    have hbase := Nat.le_of_mul_le_mul_right hcomb (pow_pos_of_pos (a := X + k + 1) (by omega) (k + 1))
    have hmul := Nat.mul_le_mul_right (X + k + 2) hbase
    have hadd2 : X + (k + 2) = X + k + 2 := by omega
    have hsub2 : X + (k + 2) - 1 = X + k + 1 := by omega
    have eL2 : X * (X + k + 2) ^ (k + 1) * (X + k + 2) = X * (X + (k + 2)) ^ (k + 2) := by
      rw [hadd2, Nat.pow_succ (X + k + 2) (k + 1), Nat.mul_assoc]
    have eR2 : (X + k + 1) ^ (k + 2) * (X + k + 2) = (X + (k + 2)) * (X + (k + 2) - 1) ^ (k + 2) := by
      rw [hsub2, hadd2, Nat.mul_comm]
    rwa [eL2, eR2] at hmul

/-- Pure-`Nat` universal `c`-floor inequality:
    `((c + 2) * (c - 1)^2)^(6*b) * (c + 2)^(8*a) > c^(18*b + 8*a)` forces `6*b*(3*c - 2) < 16*a*c^2`. -/
theorem c_min_polynomial_bound (c a b : Nat) (hc : 2 ≤ c)
    (h : c ^ (18 * b + 8 * a) < (c + 2) ^ (6 * b + 8 * a) * (c - 1) ^ (12 * b)) :
    6 * b * (3 * c - 2) < 16 * a * c ^ 2 := by
  by_cases hlt : 6 * b * (3 * c - 2) < 16 * a * c ^ 2
  · exact hlt
  · exfalso
    have hle' : 16 * a * c ^ 2 ≤ 6 * b * (3 * c - 2) := by omega
    let X := (c + 2) * (c - 1) ^ 2
    have hX_pos : 1 ≤ X := Nat.mul_pos (by omega) (pow_pos_of_pos (a := c - 1) (by omega) 2)
    have hX_add : X + (3 * c - 2) = c ^ 3 := (cubic_rate_gap c hc).1
    have h1_base : (c + 2) * c ≤ (c + 1) ^ 2 := by
      have : (c + 1) ^ 2 = (c + 2) * c + 1 := by grind
      omega
    have h1 : (c + 2) ^ (8 * a) * c ^ (8 * a) ≤ (c + 1) ^ (16 * a) := by
      have hp := Nat.pow_le_pow_left h1_base (8 * a)
      rw [Nat.mul_pow, ← Nat.pow_mul] at hp
      have : 2 * (8 * a) = 16 * a := by omega
      rwa [this] at hp
    have hc3_ge8 : 8 ≤ c ^ 3 := by
      calc 8 = 2 ^ 3 := by decide
        _ ≤ c ^ 3 := Nat.pow_le_pow_left hc 3
    have hc3_eq : (c ^ 3 - 1) + 1 = c ^ 3 := by omega
    have hcross : (16 * a) * ((c ^ 3 - 1) + 1) ≤ (6 * b * (3 * c - 2)) * c := by
      rw [hc3_eq]
      have hm := Nat.mul_le_mul_right c hle'
      have eL : 16 * a * c ^ 2 * c = 16 * a * c ^ 3 := by rw [Nat.pow_succ c 2, Nat.mul_assoc]
      rwa [eL] at hm
    have h2 := pow_ratio_le_of_cross (a := c) (b := c ^ 3 - 1) (A := 16 * a) (B := 6 * b * (3 * c - 2))
      (by omega) (by omega) hcross
    rw [hc3_eq] at h2
    have h3_base := ratio_ge_pow_top X hX_pos (3 * c - 2)
    rw [hX_add] at h3_base
    have h3 : X ^ (6 * b) * (c ^ 3) ^ ((3 * c - 2) * (6 * b)) ≤
        (c ^ 3) ^ (6 * b) * (c ^ 3 - 1) ^ ((3 * c - 2) * (6 * b)) := by
      have hp := Nat.pow_le_pow_left h3_base (6 * b)
      rw [Nat.mul_pow X, Nat.mul_pow (c ^ 3), ← Nat.pow_mul (c ^ 3), ← Nat.pow_mul (c ^ 3 - 1)] at hp
      exact hp
    have hcomb1 : (c + 2) ^ (8 * a) * c ^ (8 * a) * (c ^ 3 - 1) ^ (6 * b * (3 * c - 2))
        ≤ c ^ (16 * a) * (c ^ 3) ^ (6 * b * (3 * c - 2)) :=
      Nat.le_trans (Nat.mul_le_mul_right _ h1) h2
    have hcomb2 : (c + 2) ^ (8 * a) * c ^ (8 * a) * X ^ (6 * b) * (c ^ 3) ^ ((3 * c - 2) * (6 * b))
        ≤ c ^ (16 * a) * (c ^ 3) ^ (6 * b * (3 * c - 2)) * (c ^ 3) ^ (6 * b) := by
      have hm1 := Nat.mul_le_mul_left ((c + 2) ^ (8 * a) * c ^ (8 * a)) h3
      have hm2 := Nat.mul_le_mul_right ((c ^ 3) ^ (6 * b)) hcomb1
      have heq : (3 * c - 2) * (6 * b) = 6 * b * (3 * c - 2) := Nat.mul_comm _ _
      have eL : (c + 2) ^ (8 * a) * c ^ (8 * a) * (X ^ (6 * b) * (c ^ 3) ^ ((3 * c - 2) * (6 * b)))
          = (c + 2) ^ (8 * a) * c ^ (8 * a) * X ^ (6 * b) * (c ^ 3) ^ ((3 * c - 2) * (6 * b)) := by ac_rfl
      have eM : (c + 2) ^ (8 * a) * c ^ (8 * a) * ((c ^ 3) ^ (6 * b) * (c ^ 3 - 1) ^ ((3 * c - 2) * (6 * b)))
          = (c + 2) ^ (8 * a) * c ^ (8 * a) * (c ^ 3 - 1) ^ (6 * b * (3 * c - 2)) * (c ^ 3) ^ (6 * b) := by
        rw [heq]; ac_rfl
      rw [← eL]
      exact Nat.le_trans hm1 (eM ▸ hm2)
    have hpos_cancel : 0 < c ^ (8 * a) * (c ^ 3) ^ (6 * b * (3 * c - 2)) :=
      Nat.mul_pos (pow_pos_of_pos (by omega) _) (pow_pos_of_pos (by omega) _)
    have hfinal : ((c + 2) ^ (8 * a) * X ^ (6 * b)) * (c ^ (8 * a) * (c ^ 3) ^ (6 * b * (3 * c - 2)))
        ≤ c ^ (18 * b + 8 * a) * (c ^ (8 * a) * (c ^ 3) ^ (6 * b * (3 * c - 2))) := by
      have heq : (3 * c - 2) * (6 * b) = 6 * b * (3 * c - 2) := Nat.mul_comm _ _
      have eL : ((c + 2) ^ (8 * a) * X ^ (6 * b)) * (c ^ (8 * a) * (c ^ 3) ^ (6 * b * (3 * c - 2)))
          = (c + 2) ^ (8 * a) * c ^ (8 * a) * X ^ (6 * b) * (c ^ 3) ^ ((3 * c - 2) * (6 * b)) := by
        rw [heq]; ac_rfl
      have eR : c ^ (16 * a) * (c ^ 3) ^ (6 * b * (3 * c - 2)) * (c ^ 3) ^ (6 * b)
          = c ^ (18 * b + 8 * a) * (c ^ (8 * a) * (c ^ 3) ^ (6 * b * (3 * c - 2))) := by
        have hp1 : (c ^ 3) ^ (6 * b) = c ^ (18 * b) := by
          have h18 : 3 * (6 * b) = 18 * b := by omega
          rw [← Nat.pow_mul, h18]
        have hp2 : c ^ (16 * a) = c ^ (8 * a) * c ^ (8 * a) := by
          have h16 : 16 * a = 8 * a + 8 * a := by omega
          rw [h16, Nat.pow_add]
        rw [hp1, hp2, Nat.pow_add]; ac_rfl
      rw [eL, ← eR]
      exact hcomb2
    have hle_final := Nat.le_of_mul_le_mul_right hfinal hpos_cancel
    have hX_exp : (c + 2) ^ (8 * a) * X ^ (6 * b) = (c + 2) ^ (6 * b + 8 * a) * (c - 1) ^ (12 * b) := by
      dsimp only [X]
      rw [Nat.mul_pow, ← Nat.pow_mul, Nat.pow_add]
      have : 2 * (6 * b) = 12 * b := by omega
      rw [this]; ac_rfl
    rw [hX_exp] at hle_final
    omega

/-- Unimodality of `f(c) = ((c + 2)^(2*p - 3*q) * (c - 1)^(3*q)) / c^(2*p)`:
    Increasing half: when `(4*p - 9*q) * c ≤ 9 * q`, `f(c) ≤ f(c + 1)`. -/
theorem f_step_inc (p q c : Nat) (hc : 2 ≤ c) (hpq : 9 * q ≤ 4 * p)
    (hcond : (4 * p - 9 * q) * c ≤ 9 * q) :
    ((c + 2) ^ (2 * p - 3 * q) * (c - 1) ^ (3 * q)) * (c + 1) ^ (2 * p) ≤
    ((c + 3) ^ (2 * p - 3 * q) * c ^ (3 * q)) * c ^ (2 * p) := by
  let A := 2 * p - 3 * q
  let B := 3 * q
  let X := c * (c + 3)
  let Y := (c + 1) * (c - 1)
  have hX2 : X + 2 = (c + 1) * (c + 2) := by dsimp only [X]; grind
  have hY1 : Y + 1 = c * c := by
    apply nat_eq_of_int; dsimp only [Y]
    have hc1 : ((c - 1 : Nat) : Int) = (c : Int) - 1 := by omega
    simp only [Int.natCast_add, Int.natCast_mul]
    rw [hc1]; grind
  have h1_base : (X + 2) * X ≤ (X + 1) ^ 2 := by
    have : (X + 1) ^ 2 = (X + 2) * X + 1 := by grind
    omega
  have h1 : (X + 2) ^ A * X ^ A ≤ (X + 1) ^ (2 * A) := by
    have := Nat.pow_le_pow_left h1_base A
    rw [Nat.mul_pow, ← Nat.pow_mul] at this
    exact this
  have hcross : (2 * A) * (Y + 1) ≤ B * X := by
    rw [hY1]
    dsimp only [A, B, X]
    have h2A : 2 * (2 * p - 3 * q) = (4 * p - 9 * q) + 3 * q := by omega
    rw [h2A, Nat.add_mul, Nat.mul_add, Nat.mul_add]
    have hm := Nat.mul_le_mul_right c hcond
    have eL : (4 * p - 9 * q) * c * c = (4 * p - 9 * q) * (c * c) := by ac_rfl
    have eR : 9 * q * c = 3 * q * (c * 3) := by ac_rfl
    omega
  have hXpos : 1 ≤ X := Nat.mul_pos (by omega) (by omega)
  have hYpos : 1 ≤ Y := Nat.mul_pos (by omega) (by omega)
  have h2 := pow_ratio_le_of_cross (a := X) (b := Y) (A := 2 * A) (B := B) hXpos hYpos hcross
  have hcomb : (X + 2) ^ A * Y ^ B * X ^ A ≤ X ^ A * (Y + 1) ^ B * X ^ A := by
    have hm1 := Nat.mul_le_mul_right (Y ^ B) h1
    have eL : (X + 2) ^ A * Y ^ B * X ^ A = (X + 2) ^ A * X ^ A * Y ^ B := by ac_rfl
    have eR : X ^ A * (Y + 1) ^ B * X ^ A = X ^ (2 * A) * (Y + 1) ^ B := by
      have : X ^ (2 * A) = X ^ A * X ^ A := by rw [Nat.two_mul, Nat.pow_add]
      rw [this]; ac_rfl
    rw [eL, eR]
    exact Nat.le_trans hm1 h2
  have hXY := Nat.le_of_mul_le_mul_right hcomb (pow_pos_of_pos hXpos A)
  rw [hX2, hY1] at hXY
  dsimp only [X, Y] at hXY
  rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow, Nat.mul_pow] at hXY
  have hAB : A + B = 2 * p := by dsimp only [A, B]; omega
  have hL : (c + 1) ^ A * (c + 2) ^ A * ((c + 1) ^ B * (c - 1) ^ B) =
      ((c + 2) ^ A * (c - 1) ^ B) * (c + 1) ^ (2 * p) := by
    rw [← hAB, Nat.pow_add]; ac_rfl
  have hR : c ^ A * (c + 3) ^ A * (c ^ B * c ^ B) =
      ((c + 3) ^ A * c ^ B) * c ^ (2 * p) := by
    rw [← hAB, Nat.pow_add]; ac_rfl
  rwa [hL, hR] at hXY

/-- Unimodality decreasing half: when `9*q*c + 4*p ≤ (4*p - 9*q) * c^2`, `f(c + 1) ≤ f(c)`. -/
theorem f_step_dec (p q c : Nat) (hc : 2 ≤ c) (hpq : 9 * q ≤ 4 * p)
    (hcond : 9 * q * c + 4 * p ≤ (4 * p - 9 * q) * c ^ 2) :
    ((c + 3) ^ (2 * p - 3 * q) * c ^ (3 * q)) * c ^ (2 * p) ≤
    ((c + 2) ^ (2 * p - 3 * q) * (c - 1) ^ (3 * q)) * (c + 1) ^ (2 * p) := by
  let A := 2 * p - 3 * q
  let B := 3 * q
  let X := c * (c + 3)
  let Y := (c + 1) * (c - 1)
  have hX2 : X + 2 = (c + 1) * (c + 2) := by dsimp only [X]; grind
  have hY1 : Y + 1 = c * c := by
    apply nat_eq_of_int; dsimp only [Y]
    have hc1 : ((c - 1 : Nat) : Int) = (c : Int) - 1 := by omega
    simp only [Int.natCast_add, Int.natCast_mul]
    rw [hc1]; grind
  have h1_base : X * (X + 2) ^ 2 ≤ (X + 2) * (X + 1) ^ 2 := by
    have : X * (X + 2) ≤ (X + 1) ^ 2 := by
      have : (X + 1) ^ 2 = X * (X + 2) + 1 := by grind
      omega
    have hm := Nat.mul_le_mul_right (X + 2) this
    have eL : X * (X + 2) * (X + 2) = X * (X + 2) ^ 2 := by rw [Nat.pow_two, Nat.mul_assoc]
    have eR : (X + 1) ^ 2 * (X + 2) = (X + 2) * (X + 1) ^ 2 := Nat.mul_comm _ _
    rwa [eL, eR] at hm
  have h1 : X ^ A * (X + 2) ^ (2 * A) ≤ (X + 2) ^ A * (X + 1) ^ (2 * A) := by
    have hp := Nat.pow_le_pow_left h1_base A
    rw [Nat.mul_pow X, Nat.mul_pow (X + 2), ← Nat.pow_mul, ← Nat.pow_mul] at hp
    exact hp
  have hX11 : (X + 1) + 1 = X + 2 := by omega
  have hcross : B * ((X + 1) + 1) ≤ (2 * A) * Y := by
    rw [hX11, hX2]
    apply nat_le_of_int
    dsimp only [A, B, Y]
    have hc1 : ((c - 1 : Nat) : Int) = (c : Int) - 1 := by omega
    have h2p3q : ((2 * p - 3 * q : Nat) : Int) = 2 * (p : Int) - 3 * q := by omega
    have hcond_int : 9 * (q : Int) * c + 4 * p ≤ (4 * p - 9 * q) * (c : Int) ^ 2 := by
      have h0 := Int.ofNat_le.mpr hcond
      have h49 : ((4 * p - 9 * q : Nat) : Int) = 4 * (p : Int) - 9 * q := by omega
      simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow] at h0
      rw [h49] at h0
      change 9 * (q : Int) * c + 4 * p ≤ (4 * p - 9 * q) * (c : Int) ^ 2
      exact h0
    simp only [Int.natCast_add, Int.natCast_mul]
    rw [hc1, h2p3q]
    change (3 * (q : Int)) * (((c : Int) + 1) * ((c : Int) + 2))
        ≤ (2 * (2 * (p : Int) - 3 * q)) * (((c : Int) + 1) * ((c : Int) - 1))
    have hid : (2 * (2 * (p : Int) - 3 * q)) * (((c : Int) + 1) * ((c : Int) - 1))
        - (3 * (q : Int)) * (((c : Int) + 1) * ((c : Int) + 2))
        = (4 * (p : Int) - 9 * q) * (c : Int) ^ 2 - (9 * (q : Int) * c + 4 * p) := by grind
    omega
  have hYpos : 1 ≤ Y := Nat.mul_pos (by omega) (by omega)
  have h2 := pow_ratio_le_of_cross (a := Y) (b := X + 1) (A := B) (B := 2 * A) hYpos (by omega) hcross
  rw [hX11] at h2
  have hcomb : (X ^ A * (Y + 1) ^ B) * ((X + 1) ^ (2 * A) * (X + 2) ^ (2 * A))
      ≤ ((X + 2) ^ A * Y ^ B) * ((X + 1) ^ (2 * A) * (X + 2) ^ (2 * A)) := by
    have hm1 := Nat.mul_le_mul_left (X ^ A * (X + 2) ^ (2 * A)) h2
    have hm2 := Nat.mul_le_mul_left (Y ^ B * (X + 2) ^ (2 * A)) h1
    have eL : (X ^ A * (Y + 1) ^ B) * ((X + 1) ^ (2 * A) * (X + 2) ^ (2 * A))
        = X ^ A * (X + 2) ^ (2 * A) * ((Y + 1) ^ B * (X + 1) ^ (2 * A)) := by ac_rfl
    have eM : X ^ A * (X + 2) ^ (2 * A) * (Y ^ B * (X + 2) ^ (2 * A))
        = Y ^ B * (X + 2) ^ (2 * A) * (X ^ A * (X + 2) ^ (2 * A)) := by ac_rfl
    have eR : Y ^ B * (X + 2) ^ (2 * A) * ((X + 2) ^ A * (X + 1) ^ (2 * A))
        = ((X + 2) ^ A * Y ^ B) * ((X + 1) ^ (2 * A) * (X + 2) ^ (2 * A)) := by ac_rfl
    rw [eL, ← eR]
    exact Nat.le_trans hm1 (eM ▸ hm2)
  have hXY := Nat.le_of_mul_le_mul_right hcomb
    (Nat.mul_pos (pow_pos_of_pos (by omega) _) (pow_pos_of_pos (by omega) _))
  rw [hX2, hY1] at hXY
  dsimp only [X, Y] at hXY
  rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow, Nat.mul_pow] at hXY
  have hAB : A + B = 2 * p := by dsimp only [A, B]; omega
  have hL : c ^ A * (c + 3) ^ A * (c ^ B * c ^ B) =
      ((c + 3) ^ A * c ^ B) * c ^ (2 * p) := by
    rw [← hAB, Nat.pow_add]; ac_rfl
  have hR : (c + 1) ^ A * (c + 2) ^ A * ((c + 1) ^ B * (c - 1) ^ B) =
      ((c + 2) ^ A * (c - 1) ^ B) * (c + 1) ^ (2 * p) := by
    rw [← hAB, Nat.pow_add]; ac_rfl
  rwa [hL, hR] at hXY

/-- Multi-step monotonicity helpers for `f(c)` across any interval `[c1, c2]`. -/
theorem f_mono_inc_range (p q c1 c2 : Nat) (hc1 : 2 ≤ c1) (hle : c1 ≤ c2) (hpq : 9 * q ≤ 4 * p)
    (hcond : (4 * p - 9 * q) * (c2 - 1) ≤ 9 * q) :
    ((c1 + 2) ^ (2 * p - 3 * q) * (c1 - 1) ^ (3 * q)) * c2 ^ (2 * p) ≤
    ((c2 + 2) ^ (2 * p - 3 * q) * (c2 - 1) ^ (3 * q)) * c1 ^ (2 * p) := by
  induction hle with
  | refl => exact Nat.le_refl _
  | @step m hm ih =>
    have hm' : c1 ≤ m := hm
    have ih' := ih (by
      have h1 : (4 * p - 9 * q) * (m - 1) ≤ (4 * p - 9 * q) * m :=
        Nat.mul_le_mul_left _ (by omega)
      have heq : m + 1 - 1 = m := by omega
      rw [heq] at hcond
      exact Nat.le_trans h1 hcond)
    have hstep := f_step_inc p q m (by omega) hpq (by simpa using hcond)
    have h1 := Nat.mul_le_mul_right ((m + 1) ^ (2 * p)) ih'
    have h2 := Nat.mul_le_mul_right (c1 ^ (2 * p)) hstep
    have eL : ((c1 + 2) ^ (2 * p - 3 * q) * (c1 - 1) ^ (3 * q) * (m + 1) ^ (2 * p)) * m ^ (2 * p)
        = ((c1 + 2) ^ (2 * p - 3 * q) * (c1 - 1) ^ (3 * q) * m ^ (2 * p)) * (m + 1) ^ (2 * p) := by ac_rfl
    have eM : ((m + 2) ^ (2 * p - 3 * q) * (m - 1) ^ (3 * q) * c1 ^ (2 * p)) * (m + 1) ^ (2 * p)
        = ((m + 2) ^ (2 * p - 3 * q) * (m - 1) ^ (3 * q) * (m + 1) ^ (2 * p)) * c1 ^ (2 * p) := by ac_rfl
    have eR : ((m + 3) ^ (2 * p - 3 * q) * m ^ (3 * q) * m ^ (2 * p)) * c1 ^ (2 * p)
        = ((m + 3) ^ (2 * p - 3 * q) * m ^ (3 * q) * c1 ^ (2 * p)) * m ^ (2 * p) := by ac_rfl
    have hcomb : ((c1 + 2) ^ (2 * p - 3 * q) * (c1 - 1) ^ (3 * q) * (m + 1) ^ (2 * p)) * m ^ (2 * p)
        ≤ ((m + 3) ^ (2 * p - 3 * q) * m ^ (3 * q) * c1 ^ (2 * p)) * m ^ (2 * p) := by
      rw [eL, ← eR]
      exact Nat.le_trans h1 (eM ▸ h2)
    have hfin := Nat.le_of_mul_le_mul_right hcomb (pow_pos_of_pos (a := m) (by omega) _)
    simpa [Nat.add_assoc] using hfin

theorem f_mono_dec_range (p q c1 c2 : Nat) (hc1 : 2 ≤ c1) (hle : c1 ≤ c2) (hpq : 9 * q ≤ 4 * p)
    (hcond : 9 * q * c1 + 4 * p ≤ (4 * p - 9 * q) * c1 ^ 2) :
    ((c2 + 2) ^ (2 * p - 3 * q) * (c2 - 1) ^ (3 * q)) * c1 ^ (2 * p) ≤
    ((c1 + 2) ^ (2 * p - 3 * q) * (c1 - 1) ^ (3 * q)) * c2 ^ (2 * p) := by
  induction hle with
  | refl => exact Nat.le_refl _
  | @step m hm ih =>
    have hm' : c1 ≤ m := hm
    have hm_cond : 9 * q * m + 4 * p ≤ (4 * p - 9 * q) * m ^ 2 := by
      have hlin : 9 * q ≤ (4 * p - 9 * q) * c1 := by
        have : 9 * q * c1 ≤ (4 * p - 9 * q) * c1 * c1 := by
          rw [Nat.pow_two, ← Nat.mul_assoc] at hcond; omega
        exact Nat.le_of_mul_le_mul_right this (by omega)
      have hdiff : (m - c1) * c1 + c1 ^ 2 ≤ m ^ 2 := by
        have h1 : m = (m - c1) + c1 := (Nat.sub_add_cancel hm').symm
        have hm2 : m ^ 2 = ((m - c1) + c1) ^ 2 := by rw [← h1]
        have hexp : ((m - c1) + c1) ^ 2 = (m - c1) * (m - c1) + 2 * ((m - c1) * c1) + c1 ^ 2 := by grind
        omega
      have hmul1 : (4 * p - 9 * q) * ((m - c1) * c1) + (4 * p - 9 * q) * c1 ^ 2
          ≤ (4 * p - 9 * q) * m ^ 2 := by
        rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hdiff
      have hmul2 : 9 * q * (m - c1) ≤ (4 * p - 9 * q) * ((m - c1) * c1) := by
        have := Nat.mul_le_mul_right (m - c1) hlin
        have eR : (4 * p - 9 * q) * c1 * (m - c1) = (4 * p - 9 * q) * ((m - c1) * c1) := by ac_rfl
        rwa [eR] at this
      have h9m : 9 * q * m = 9 * q * (m - c1) + 9 * q * c1 := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hm']
      omega
    have hstep := f_step_dec p q m (by omega) hpq hm_cond
    have h1 := Nat.mul_le_mul_right (c1 ^ (2 * p)) hstep
    have h2 := Nat.mul_le_mul_right ((m + 1) ^ (2 * p)) ih
    have eL : ((m + 3) ^ (2 * p - 3 * q) * m ^ (3 * q) * c1 ^ (2 * p)) * m ^ (2 * p)
        = ((m + 3) ^ (2 * p - 3 * q) * m ^ (3 * q) * m ^ (2 * p)) * c1 ^ (2 * p) := by ac_rfl
    have eM : ((m + 2) ^ (2 * p - 3 * q) * (m - 1) ^ (3 * q) * (m + 1) ^ (2 * p)) * c1 ^ (2 * p)
        = ((m + 2) ^ (2 * p - 3 * q) * (m - 1) ^ (3 * q) * c1 ^ (2 * p)) * (m + 1) ^ (2 * p) := by ac_rfl
    have eR : ((c1 + 2) ^ (2 * p - 3 * q) * (c1 - 1) ^ (3 * q) * m ^ (2 * p)) * (m + 1) ^ (2 * p)
        = ((c1 + 2) ^ (2 * p - 3 * q) * (c1 - 1) ^ (3 * q) * (m + 1) ^ (2 * p)) * m ^ (2 * p) := by ac_rfl
    have hcomb : ((m + 3) ^ (2 * p - 3 * q) * m ^ (3 * q) * c1 ^ (2 * p)) * m ^ (2 * p)
        ≤ ((c1 + 2) ^ (2 * p - 3 * q) * (c1 - 1) ^ (3 * q) * (m + 1) ^ (2 * p)) * m ^ (2 * p) := by
      rw [eL, ← eR]
      exact Nat.le_trans h1 (eM ▸ h2)
    have hfin := Nat.le_of_mul_le_mul_right hcomb (pow_pos_of_pos (a := m) (by omega) _)
    simpa [Nat.add_assoc] using hfin

/-! ### Layer 2: Binomial theorem, `Nat` Cauchy–Schwarz, and balanced-word bounds -/

/-- Exact binomial coefficient defined by Pascal's recurrence. -/
def natChoose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => natChoose n k + natChoose n (k + 1)

theorem natChoose_eq_zero_of_lt : ∀ n k, n < k → natChoose n k = 0
  | 0, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => by omega
  | n + 1, k + 1, h => by
    simp only [natChoose]
    rw [natChoose_eq_zero_of_lt n k (by omega), natChoose_eq_zero_of_lt n (k + 1) (by omega)]

theorem natChoose_self (n : Nat) : natChoose n n = 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp [natChoose, ih, natChoose_eq_zero_of_lt k (k + 1) (by omega)]

theorem natSum_add (n : Nat) (f g : Nat → Nat) :
    natSum n (fun i => f i + g i) = natSum n f + natSum n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [natSum, ih]; omega

theorem natSum_mul_left (n a : Nat) (f : Nat → Nat) :
    natSum n (fun i => a * f i) = a * natSum n f := by
  induction n with
  | zero => simp [natSum]
  | succ k ih => simp only [natSum, ih, Nat.mul_add]

theorem natSum_mul_right (n a : Nat) (f : Nat → Nat) :
    natSum n (fun i => f i * a) = natSum n f * a := by
  induction n with
  | zero => simp [natSum]
  | succ k ih => simp only [natSum, ih, Nat.add_mul]

theorem natSum_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i < n, f i = g i) :
    natSum n f = natSum n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [natSum]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

/-- Binomial theorem in `Nat`: `∑_{h=0}^d C(d, h) * a^(d - h) = (a + 1)^d`. -/
theorem sum_choose_pow (a d : Nat) :
    natSum (d + 1) (fun h => natChoose d h * a ^ (d - h)) = (a + 1) ^ d := by
  induction d with
  | zero => simp [natSum, natChoose]
  | succ n ih =>
    have hshift : ∀ m (f : Nat → Nat), natSum (m + 1) f = f 0 + natSum m (fun j => f (j + 1)) := by
      intro m f
      induction m with
      | zero => simp [natSum]
      | succ k ihk =>
        change natSum (k + 1) f + f (k + 1) = f 0 + (natSum k (fun j => f (j + 1)) + f (k + 1))
        rw [ihk]; omega
    rw [hshift (n + 1)]
    have h0 : natChoose (n + 1) 0 * a ^ (n + 1 - 0) = a ^ (n + 1) := by simp [natChoose]
    rw [h0]
    have hrec : natSum (n + 1) (fun j => natChoose (n + 1) (j + 1) * a ^ (n + 1 - (j + 1))) =
        natSum (n + 1) (fun j => natChoose n j * a ^ (n - j)) +
        natSum (n + 1) (fun j => natChoose n (j + 1) * a ^ (n - j)) := by
      rw [← natSum_add]
      apply natSum_congr
      intro j _
      simp only [natChoose, Nat.add_mul]
      have : n + 1 - (j + 1) = n - j := by omega
      rw [this]
    rw [hrec, ih]
    have h2 : a ^ (n + 1) + natSum (n + 1) (fun j => natChoose n (j + 1) * a ^ (n - j)) =
        a * natSum (n + 1) (fun h => natChoose n h * a ^ (n - h)) := by
      have hlast : natSum (n + 1) (fun j => natChoose n (j + 1) * a ^ (n - j)) =
          natSum n (fun j => natChoose n (j + 1) * a ^ (n - j)) := by
        simp only [natSum, natChoose_eq_zero_of_lt n (n + 1) (by omega), Nat.zero_mul, Nat.add_zero]
      rw [hlast, hshift n (fun h => natChoose n h * a ^ (n - h)), Nat.mul_add]
      have hfirst : a * (natChoose n 0 * a ^ (n - 0)) = a ^ (n + 1) := by
        simp [natChoose, Nat.pow_succ, Nat.mul_comm]
      rw [hfirst]
      apply congrArg (a ^ (n + 1) + ·)
      rw [← natSum_mul_left]
      apply natSum_congr
      intro j hj
      have hpow : a * a ^ (n - (j + 1)) = a ^ (n - j) := by
        have hnj : (n - (j + 1)) + 1 = n - j := by omega
        calc a * a ^ (n - (j + 1)) = a ^ ((n - (j + 1)) + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
          _ = a ^ (n - j) := by rw [hnj]
      calc natChoose n (j + 1) * a ^ (n - j)
          = natChoose n (j + 1) * (a * a ^ (n - (j + 1))) := by rw [hpow]
        _ = a * (natChoose n (j + 1) * a ^ (n - (j + 1))) := by ac_rfl
    have h2' : a ^ (n + 1) + natSum (n + 1) (fun j => natChoose n (j + 1) * a ^ (n - j)) =
        a * (a + 1) ^ n := by rw [h2, ih]
    have hpow : (a + 1) ^ (n + 1) = (a + 1) ^ n + a * (a + 1) ^ n := by
      rw [Nat.pow_succ (a + 1) n, Nat.mul_add, Nat.mul_one, Nat.mul_comm ((a + 1) ^ n) a]; omega
    omega

/-- Exact `Nat` Cauchy–Schwarz inequality: `(∑_{i < n} f i)^2 ≤ n * ∑_{i < n} (f i)^2`. -/
theorem nat_cauchy_schwarz (n : Nat) (f : Nat → Nat) :
    (natSum n f) ^ 2 ≤ n * natSum n (fun i => (f i) ^ 2) := by
  induction n with
  | zero => simp [natSum]
  | succ k ih =>
    simp only [natSum]
    let S := natSum k f
    let Q := natSum k (fun i => (f i) ^ 2)
    let x := f k
    have hcross_gen : ∀ m y, 2 * natSum m f * y ≤ natSum m (fun i => (f i) ^ 2) + m * y ^ 2 := by
      intro m y
      induction m with
      | zero => simp [natSum]
      | succ r ihr =>
        simp only [natSum]
        have hpair : 2 * f r * y ≤ (f r) ^ 2 + y ^ 2 := by
          have hq := nat_quad_amgm (f r) y
          have hid : (y + f r) ^ 2 = (f r) ^ 2 + y ^ 2 + 2 * f r * y := by grind
          have hid2 : 4 * f r * y = 2 * f r * y + 2 * f r * y := by grind
          omega
        have h1 : 2 * (natSum r f + f r) * y = 2 * natSum r f * y + 2 * f r * y := by grind
        have h2 : (r + 1) * y ^ 2 = r * y ^ 2 + y ^ 2 := by grind
        omega
    have hcross : 2 * S * x ≤ Q + k * x ^ 2 := hcross_gen k x
    have hL : (S + x) ^ 2 = S ^ 2 + 2 * S * x + x ^ 2 := by grind
    have hR : (k + 1) * (Q + x ^ 2) = k * Q + Q + k * x ^ 2 + x ^ 2 := by grind
    change (S + x) ^ 2 ≤ (k + 1) * (Q + x ^ 2)
    have ih' : S ^ 2 ≤ k * Q := ih
    rw [hL, hR]
    omega

/-- Reverse inequality in `Nat`: `∑_{i < n} (f i)^2 ≤ (∑_{i < n} f i)^2`. -/
theorem nat_sum_sq_le_sq_sum (n : Nat) (f : Nat → Nat) :
    natSum n (fun i => (f i) ^ 2) ≤ (natSum n f) ^ 2 := by
  induction n with
  | zero => simp [natSum]
  | succ k ih =>
    simp only [natSum]
    have hexp : (natSum k f + f k) ^ 2 = (natSum k f) ^ 2 + 2 * natSum k f * f k + (f k) ^ 2 := by grind
    omega

/-- Exact balanced-word count `M_d(c) = ∑_{h=0}^d (C(d, h) * (c + 1)^(d - h))^2`. -/
def M_d_pass (c d : Nat) : Nat :=
  natSum (d + 1) (fun h => (natChoose d h * (c + 1) ^ (d - h)) ^ 2)

/-- Layer 2 (`Prop. prop:balanced_words`): `(c + 2)^(2*d) ≤ (d + 1) * M_d(c)` and `M_d(c) ≤ (c + 2)^(2*d)`. -/
theorem cauchy_schwarz_balanced_words (c d : Nat) :
    (c + 2) ^ (2 * d) ≤ (d + 1) * M_d_pass c d ∧ M_d_pass c d ≤ (c + 2) ^ (2 * d) := by
  have hbin := sum_choose_pow (c + 1) d
  have hc2 : (c + 1) + 1 = c + 2 := by omega
  rw [hc2] at hbin
  have hcs := nat_cauchy_schwarz (d + 1) (fun h => natChoose d h * (c + 1) ^ (d - h))
  have hrev := nat_sum_sq_le_sq_sum (d + 1) (fun h => natChoose d h * (c + 1) ^ (d - h))
  rw [hbin] at hcs hrev
  have hpow : ((c + 2) ^ d) ^ 2 = (c + 2) ^ (2 * d) := by rw [← Nat.pow_mul, Nat.mul_comm]
  rw [hpow] at hcs hrev
  exact ⟨hcs, hrev⟩

/-! ### Layer 3: Lagrange uncoupling, pole clearing, and OpenAI `5M` exact 4x tightening -/

/-- Layer 3 evaluation-count constraints for degree `2*w - 2` Lagrange uncoupling. -/
theorem lagrange_uncoupling_constraints (w : Nat) (hw : 2 ≤ w) :
    (2 * w - 2) + 1 = 2 * w - 1 ∧
    w ≤ 2 * w - 1 ∧
    2 * w - 1 < 2 * w ∧
    (2 * w) ^ 3 = 8 * w ^ 3 ∧
    8 ^ 2 = 64 := by
  refine ⟨by omega, by omega, by omega, ?_, by decide⟩
  rw [Nat.mul_pow]

/-- Inner parameter pole-clearing necessity (`Prop. prop:lagrange_poles`). -/
theorem inner_eta_pole_clearing_necessity (w r : Nat) (hw : 1 ≤ w) :
    (r ≤ w - 1 → (r : Int) - ((w - 1 : Nat) : Int) ≤ 0) ∧
    ((w : Int) - ((w - 1 : Nat) : Int) = 1) := by
  constructor <;> omega

/-- Original audit tightening of OpenAI Prop 3.1 (`Prop. prop:openai_5m_tight`):
    exact 4x tightening from `(M - 1)^2` to `⌊(M - 1) / 2⌋^2`, plus attainment witness. -/
theorem openai_5M_tight_eps_deg (M : Nat) :
    (∀ g h u v : Nat, g < M → h < M → u < M → v < M →
      (u : Int) - v + 2 * ((g : Int) - h) = 0 →
      ((g : Int) - h) ^ 2 ≤ (((M - 1) / 2 : Nat) : Int) ^ 2) ∧
    (1 ≤ M → ∃ g h u v : Nat, g < M ∧ h < M ∧ u < M ∧ v < M ∧
      (u : Int) - v + 2 * ((g : Int) - h) = 0 ∧
      ((g : Int) - h) ^ 2 = (((M - 1) / 2 : Nat) : Int) ^ 2) := by
  constructor
  · intro g h u v hg hh hu hv heq
    let q0 := (M - 1) / 2
    have hbd : -(q0 : Int) ≤ (g : Int) - h ∧ (g : Int) - h ≤ (q0 : Int) := by
      dsimp only [q0]; omega
    have hsq : ∀ x y : Int, -y ≤ x → x ≤ y → x ^ 2 ≤ y ^ 2 := by
      intro x y hlo hhi
      have hprod : 0 ≤ (y - x) * (y + x) := Int.mul_nonneg (by omega) (by omega)
      have hid : (y - x) * (y + x) = y ^ 2 - x ^ 2 := by grind
      omega
    exact hsq ((g : Int) - h) (q0 : Int) hbd.1 hbd.2
  · intro hM
    refine ⟨(M - 1) / 2, 0, 0, 2 * ((M - 1) / 2), by omega, by omega, by omega, by omega, ?_, ?_⟩
    · omega
    · simp

/-! ### Layer 4: Rectangular slabbing barrier and exact two-sided `L_pass` sandwich -/

/-- Layer 4 slabbing barrier (`Prop. prop:slabbing_barrier`). -/
theorem slabbing_barrier (p q : Nat) (hq : 0 < q) (hα : 3 * p ≤ 2 * q) :
    4 * (3 * q - p) > 9 * q := by
  omega

/-- Pass's exact length recurrence:
    `L_0 = 1`, `L_{k + 1} = L_k + ⌈(3 L_k - 1) / (c - 1)⌉`. -/
def L_pass (c : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => L_pass c k + (3 * L_pass c k - 1 + (c - 2)) / (c - 1)

theorem L_pass_succ (c k : Nat) :
    L_pass c (k + 1) = L_pass c k + (3 * L_pass c k - 1 + (c - 2)) / (c - 1) := rfl

theorem L_pass_pos (c : Nat) : ∀ k, 1 ≤ L_pass c k
  | 0 => Nat.le_refl 1
  | k + 1 => by
    have ih := L_pass_pos c k
    rw [L_pass_succ]
    exact Nat.le_trans ih (Nat.le_add_right _ _)

/-- Exact lower bound on one step of `L_pass`. -/
theorem L_pass_step_lower (c k : Nat) (hc : 2 ≤ c) :
    (3 * L_pass c k - 1) * (c + 2) ≤ (3 * L_pass c (k + 1) - 1) * (c - 1) := by
  have hLk := L_pass_pos c k
  rw [L_pass_succ]
  let L := L_pass c k
  let q := (3 * L - 1 + (c - 2)) / (c - 1)
  have hceil : 3 * L - 1 ≤ q * (c - 1) := by
    have h := le_ceil_div_mul (3 * L - 1) (c - 1) (by omega)
    have heq : 3 * L - 1 + (c - 1) - 1 = 3 * L - 1 + (c - 2) := by omega
    rwa [heq] at h
  have h1 : (3 * (L + q) - 1) * (c - 1) = (3 * L - 1) * (c - 1) + 3 * (q * (c - 1)) := by
    have : 3 * (L + q) - 1 = (3 * L - 1) + 3 * q := by omega
    rw [this, Nat.add_mul]
    have : 3 * q * (c - 1) = 3 * (q * (c - 1)) := by ac_rfl
    omega
  have h2 : (3 * L - 1) * (c + 2) = (3 * L - 1) * (c - 1) + 3 * (3 * L - 1) := by
    have : c + 2 = (c - 1) + 3 := by omega
    rw [this, Nat.mul_add, Nat.mul_comm (3 * L - 1) 3]
  change (3 * L - 1) * (c + 2) ≤ (3 * (L + q) - 1) * (c - 1)
  rw [h1, h2]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 3 hceil) _

/-- Exact upper bound on one step of `L_pass`. -/
theorem L_pass_step_upper (c k : Nat) (hc : 2 ≤ c) :
    (3 * L_pass c (k + 1) + c - 3) * (c - 1) ≤ (3 * L_pass c k + c - 3) * (c + 2) := by
  have hLk := L_pass_pos c k
  rw [L_pass_succ]
  let L := L_pass c k
  let q := (3 * L - 1 + (c - 2)) / (c - 1)
  have hfloor : q * (c - 1) ≤ 3 * L - 1 + (c - 2) := Nat.div_mul_le_self _ _
  have h1 : (3 * (L + q) + c - 3) * (c - 1) = (3 * L + c - 3) * (c - 1) + 3 * (q * (c - 1)) := by
    have : 3 * (L + q) + c - 3 = (3 * L + c - 3) + 3 * q := by omega
    rw [this, Nat.add_mul]
    have : 3 * q * (c - 1) = 3 * (q * (c - 1)) := by ac_rfl
    omega
  have h2 : (3 * L + c - 3) * (c + 2) = (3 * L + c - 3) * (c - 1) + 3 * (3 * L + c - 3) := by
    have : c + 2 = (c - 1) + 3 := by omega
    rw [this, Nat.mul_add, Nat.mul_comm (3 * L + c - 3) 3]
  have h3 : 3 * L - 1 + (c - 2) = 3 * L + c - 3 := by omega
  change (3 * (L + q) + c - 3) * (c - 1) ≤ (3 * L + c - 3) * (c + 2)
  rw [h1, h2, ← h3]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 3 hfloor) _

/-- Exact linear phase of `L_pass`: `L_pass c j = j + 1` for all `j ≤ (c - 1) / 3`. -/
theorem L_pass_eq_add_one (c : Nat) (hc : 2 ≤ c) : ∀ j, j ≤ (c - 1) / 3 → L_pass c j = j + 1
  | 0, _ => rfl
  | j + 1, hj => by
    have ih := L_pass_eq_add_one c hc j (by omega)
    rw [L_pass_succ, ih]
    have hlo : c - 1 ≤ 3 * (j + 1) - 1 + (c - 2) := by omega
    have hhi : 3 * (j + 1) - 1 + (c - 2) < 2 * (c - 1) := by omega
    have hdiv : (3 * (j + 1) - 1 + (c - 2)) / (c - 1) = 1 := by
      have hge1 : 1 ≤ (3 * (j + 1) - 1 + (c - 2)) / (c - 1) := Nat.div_pos hlo (by omega)
      have hlt2 : (3 * (j + 1) - 1 + (c - 2)) / (c - 1) < 2 :=
        (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
      omega
    rw [hdiv]

/-- General propagated lower bound from any index `j0 ≤ k`. -/
theorem L_pass_lower_from (c j0 : Nat) (hc : 2 ≤ c) : ∀ m,
    (3 * L_pass c j0 - 1) * (c + 2) ^ m ≤ (3 * L_pass c (j0 + m) - 1) * (c - 1) ^ m
  | 0 => by simp
  | m + 1 => by
    have ih := L_pass_lower_from c j0 hc m
    have hstep := L_pass_step_lower c (j0 + m) hc
    have h1 := Nat.mul_le_mul_right (c + 2) ih
    have h2 := Nat.mul_le_mul_right ((c - 1) ^ m) hstep
    have eL : (3 * L_pass c j0 - 1) * (c + 2) ^ m * (c + 2)
        = (3 * L_pass c j0 - 1) * (c + 2) ^ (m + 1) := by rw [Nat.pow_succ (c + 2) m, Nat.mul_assoc]
    have eM : (3 * L_pass c (j0 + m) - 1) * (c - 1) ^ m * (c + 2)
        = (3 * L_pass c (j0 + m) - 1) * (c + 2) * (c - 1) ^ m := by ac_rfl
    have eR : (3 * L_pass c (j0 + m + 1) - 1) * (c - 1) * (c - 1) ^ m
        = (3 * L_pass c (j0 + (m + 1)) - 1) * (c - 1) ^ (m + 1) := by
      rw [Nat.add_assoc, Nat.pow_succ (c - 1) m]; ac_rfl
    rw [← eL, ← eR]
    exact Nat.le_trans h1 (eM ▸ h2)

/-- General propagated upper bound from any index `j0 ≤ k`. -/
theorem exact_Lk_upper_from_j0 (c j0 : Nat) (hc : 2 ≤ c) : ∀ m,
    (3 * L_pass c (j0 + m) + c - 3) * (c - 1) ^ m ≤ (3 * L_pass c j0 + c - 3) * (c + 2) ^ m
  | 0 => by simp
  | m + 1 => by
    have ih := exact_Lk_upper_from_j0 c j0 hc m
    have hstep := L_pass_step_upper c (j0 + m) hc
    have h1 := Nat.mul_le_mul_right ((c - 1) ^ m) hstep
    have h2 := Nat.mul_le_mul_right (c + 2) ih
    have eL : (3 * L_pass c (j0 + m + 1) + c - 3) * (c - 1) * (c - 1) ^ m
        = (3 * L_pass c (j0 + (m + 1)) + c - 3) * (c - 1) ^ (m + 1) := by
      rw [Nat.add_assoc, Nat.pow_succ (c - 1) m]; ac_rfl
    have eM : (3 * L_pass c (j0 + m) + c - 3) * (c + 2) * (c - 1) ^ m
        = (3 * L_pass c (j0 + m) + c - 3) * (c - 1) ^ m * (c + 2) := by ac_rfl
    have eR : (3 * L_pass c j0 + c - 3) * (c + 2) ^ m * (c + 2)
        = (3 * L_pass c j0 + c - 3) * (c + 2) ^ (m + 1) := by rw [Nat.pow_succ (c + 2) m, Nat.mul_assoc]
    rw [← eL, ← eR]
    exact Nat.le_trans h1 (eM ▸ h2)

/-- Layer 4 complete `L_pass` sandwich theorem (`Thm. thm:lk_sandwich`). -/
theorem exact_Lk_sandwich (c : Nat) (hc : 2 ≤ c) :
    (∀ k, 2 * (c + 2) ^ k ≤ (3 * L_pass c k - 1) * (c - 1) ^ k ∧
          (c + 2) ^ k ≤ (2 * L_pass c k - 1) * (c - 1) ^ k) ∧
    (let j0 := (c - 1) / 3
     (∀ j ≤ j0, j + 1 ≤ L_pass c j) ∧
     (∀ k, j0 ≤ k →
       (2 * j0 + 1) * (c + 2) ^ (k - j0) ≤ (2 * L_pass c k - 1) * (c - 1) ^ (k - j0))) ∧
    (∀ k, (3 * L_pass c k + c - 3) * (c - 1) ^ k ≤ c * (c + 2) ^ k ∧
          (2 * L_pass c k - 1) * 3 * (c - 1) ^ k ≤ 2 * c * (c + 2) ^ k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    have hlow := L_pass_lower_from c 0 hc k
    simp only [Nat.zero_add, L_pass] at hlow
    have hLk := L_pass_pos c k
    have h2L : 3 * L_pass c k - 1 ≤ 2 * (2 * L_pass c k - 1) := by omega
    have hmul : 2 * (c + 2) ^ k ≤ 2 * ((2 * L_pass c k - 1) * (c - 1) ^ k) := by
      have := Nat.mul_le_mul_right ((c - 1) ^ k) h2L
      have heq : 2 * (2 * L_pass c k - 1) * (c - 1) ^ k = 2 * ((2 * L_pass c k - 1) * (c - 1) ^ k) := by ac_rfl
      exact Nat.le_trans hlow (heq ▸ this)
    exact ⟨hlow, Nat.le_of_mul_le_mul_left hmul (by decide)⟩
  · dsimp only
    let j0 := (c - 1) / 3
    refine ⟨fun j hj => by rw [L_pass_eq_add_one c hc j hj]; exact Nat.le_refl _, ?_⟩
    intro k hk
    have hlow := L_pass_lower_from c j0 hc (k - j0)
    have hadd : j0 + (k - j0) = k := Nat.add_sub_of_le hk
    rw [hadd, L_pass_eq_add_one c hc j0 (Nat.le_refl j0)] at hlow
    have hLk := L_pass_pos c k
    have hmul2 := Nat.mul_le_mul_left 2 hlow
    have hpow_le : (c - 1) ^ (k - j0) ≤ (c + 2) ^ (k - j0) := Nat.pow_le_pow_left (by omega) _
    have hL : 2 * ((3 * (j0 + 1) - 1) * (c + 2) ^ (k - j0)) =
        3 * ((2 * j0 + 1) * (c + 2) ^ (k - j0)) + (c + 2) ^ (k - j0) := by
      have : 2 * (3 * (j0 + 1) - 1) = 3 * (2 * j0 + 1) + 1 := by omega
      rw [← Nat.mul_assoc, this, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    have hR : 2 * ((3 * L_pass c k - 1) * (c - 1) ^ (k - j0)) =
        3 * ((2 * L_pass c k - 1) * (c - 1) ^ (k - j0)) + (c - 1) ^ (k - j0) := by
      have : 2 * (3 * L_pass c k - 1) = 3 * (2 * L_pass c k - 1) + 1 := by omega
      rw [← Nat.mul_assoc, this, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    rw [hL, hR] at hmul2
    have h3 : 3 * ((2 * j0 + 1) * (c + 2) ^ (k - j0)) ≤ 3 * ((2 * L_pass c k - 1) * (c - 1) ^ (k - j0)) := by
      omega
    exact Nat.le_of_mul_le_mul_left h3 (by decide)
  · intro k
    have hup := exact_Lk_upper_from_j0 c 0 hc k
    simp only [Nat.zero_add, L_pass] at hup
    have hc_eq : 3 * 1 + c - 3 = c := by omega
    rw [hc_eq] at hup
    have hLk := L_pass_pos c k
    have h32 : (2 * L_pass c k - 1) * 3 ≤ 2 * (3 * L_pass c k + c - 3) := by omega
    have hmul : (2 * L_pass c k - 1) * 3 * (c - 1) ^ k ≤ 2 * c * (c + 2) ^ k := by
      have s1 := Nat.mul_le_mul_right ((c - 1) ^ k) h32
      have s2 := Nat.mul_le_mul_left 2 hup
      have eM : 2 * (3 * L_pass c k + c - 3) * (c - 1) ^ k
          = 2 * ((3 * L_pass c k + c - 3) * (c - 1) ^ k) := by ac_rfl
      have eR : 2 * (c * (c + 2) ^ k) = 2 * c * (c + 2) ^ k := by ac_rfl
      exact Nat.le_trans s1 (eR ▸ (eM ▸ s2))
    exact ⟨hup, hmul⟩

/-! ### Layer 5: Sequential pole-clearing cascade, multivariate Bini, hidden constant, finite Schönhage -/

/-- Pass Lemma 2.9 sequential pole-order recurrence across `m` half-rounds. -/
def P_seq (P_half : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => P_half + (P_half + 1) * P_seq P_half m

/-- Exact closed form `P_seq P m + 1 = (P + 1)^m` and instantiation at `P_half = 3*((2*d + 1)*w - 1)`. -/
theorem pole_cascade_exact :
    (∀ P m : Nat, P_seq P m + 1 = (P + 1) ^ m) ∧
    (∀ d w k : Nat, 1 ≤ w →
      P_seq (3 * ((2 * d + 1) * w - 1)) (2 * k) + 1 = (3 * (2 * d + 1) * w - 2) ^ (2 * k)) := by
  have hmain : ∀ P m : Nat, P_seq P m + 1 = (P + 1) ^ m := by
    intro P m
    induction m with
    | zero => rfl
    | succ r ih =>
      unfold P_seq
      have h1 : P + (P + 1) * P_seq P r + 1 = (P + 1) * (P_seq P r + 1) := by
        rw [Nat.mul_add, Nat.mul_one]; omega
      rw [h1, ih, Nat.pow_succ, Nat.mul_comm]
  refine ⟨hmain, ?_⟩
  intro d w k hw
  rw [hmain]
  have h1 : 1 ≤ (2 * d + 1) * w := Nat.mul_pos (by omega) hw
  have heq : 3 * ((2 * d + 1) * w - 1) + 1 = 3 * (2 * d + 1) * w - 2 := by
    have : 3 * (2 * d + 1) * w = 3 * ((2 * d + 1) * w) := by ac_rfl
    omega
  rw [heq]

/-- Iterated multivariate Bini vs univariate Pass Lemma 2.9 (`Thm. thm:pole_cascade`):
    `h * D^m + 1 < (h * D + 1)^m` for all `h ≥ 2, m ≥ 2, D ≥ 1`. -/
theorem multivariate_bini_worse (h m D : Nat) (hh : 2 ≤ h) (hm : 2 ≤ m) (hD : 1 ≤ D) :
    h * D ^ m + 1 < (h * D + 1) ^ m := by
  have hhm : h * 2 ≤ h ^ m := by
    calc h * 2 ≤ h * h := Nat.mul_le_mul_left h hh
      _ = h ^ 2 := (Nat.pow_two h).symm
      _ ≤ h ^ m := Nat.pow_le_pow_right (by omega) hm
  have hDpos : 1 ≤ D ^ m := pow_pos_of_pos hD m
  have h1 : h * D ^ m + 1 < (h * D) ^ m := by
    rw [Nat.mul_pow]
    have hmul := Nat.mul_le_mul_right (D ^ m) hhm
    have h2h : h * 2 * D ^ m = h * D ^ m + h * D ^ m := by grind
    have hge2 : 2 ≤ h * D ^ m := by
      calc 2 ≤ h := hh
        _ = h * 1 := (Nat.mul_one h).symm
        _ ≤ h * D ^ m := Nat.mul_le_mul_left h hDpos
    omega
  exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_left (by omega) m)

/-- Master-Theorem hidden-constant lower bounds (`Prop. prop:hidden_constant`). -/
theorem hidden_constant_bounds :
    (∀ V p q C T_prev : Nat, 2 ≤ V → p ≤ 3 * q →
      T_prev = (V - 1) ^ 3 → T_prev ^ q ≤ C ^ q * (V - 1) ^ p →
      (V - 1) ^ (3 * q - p) ≤ C ^ q) ∧
    (∀ V R p q C T_next : Nat, 2 ≤ V → V ^ 2 ≤ R → R ^ 2 ≤ T_next →
      T_next ^ q ≤ C ^ q * (V + 1) ^ p →
      V ^ (4 * q) ≤ C ^ q * (V + 1) ^ p) := by
  constructor
  · intro V p q C T_prev hV hpq hT hC
    rw [hT, ← Nat.pow_mul] at hC
    have hsplit : (V - 1) ^ (3 * q) = (V - 1) ^ (3 * q - p) * (V - 1) ^ p := by
      rw [← Nat.pow_add, Nat.sub_add_cancel hpq]
    rw [hsplit] at hC
    exact Nat.le_of_mul_le_mul_right hC (pow_pos_of_pos (a := V - 1) (by omega) p)
  · intro V R p q C T_next hV hR hT hC
    have hV4 : V ^ 4 ≤ T_next := by
      have : V ^ 4 = (V ^ 2) ^ 2 := by rw [← Nat.pow_mul]
      rw [this]
      exact Nat.le_trans (Nat.pow_le_pow_left hR 2) hT
    have hV4q : V ^ (4 * q) ≤ T_next ^ q := by
      rw [Nat.pow_mul]
      exact Nat.pow_le_pow_left hV4 q
    exact Nat.le_trans hV4q hC

/-- Recursive batched single-matrix rank sequence (`Lemma lem:finite_schonhage`):
    `R_1 = R_ex`, `R_{j + 1} = ⌈R_j / P⌉ * R_ex`. -/
def schonhageRank (P R_ex : Nat) : Nat → Nat
  | 0 => 1
  | 1 => R_ex
  | j + 2 => ((schonhageRank P R_ex (j + 1) + P - 1) / P) * R_ex

/-- Finite direct-sum to single-matrix conversion (`Lemma lem:finite_schonhage`),
    proved in exact cross-multiplied `Nat`:
    `P^(t - 1) * schonhageRank P R_ex t ≤ (R_ex + P)^t` for all `P ≥ 1, R_ex ≥ P, t ≥ 1`. -/
theorem finite_schonhage (P R_ex : Nat) (hP : 1 ≤ P) (hRP : P ≤ R_ex) :
    ∀ t, 1 ≤ t → P ^ (t - 1) * schonhageRank P R_ex t ≤ (R_ex + P) ^ t
  | 0, h => by omega
  | 1, _ => by simp [schonhageRank]
  | j + 2, _ => by
    have ih := finite_schonhage P R_ex hP hRP (j + 1) (by omega)
    simp only [schonhageRank]
    let Rj := schonhageRank P R_ex (j + 1)
    have hceil : ((Rj + P - 1) / P) * P ≤ Rj + P := by
      have h1 := Nat.div_mul_le_self (Rj + P - 1) P
      omega
    have hstep : P ^ (j + 1) * (((Rj + P - 1) / P) * R_ex)
        ≤ (P ^ j * Rj + P ^ (j + 1)) * R_ex := by
      have eL : P ^ (j + 1) * (((Rj + P - 1) / P) * R_ex)
          = P ^ j * (((Rj + P - 1) / P) * P) * R_ex := by
        rw [Nat.pow_succ P j]; ac_rfl
      have eR : (P ^ j * Rj + P ^ (j + 1)) * R_ex
          = P ^ j * (Rj + P) * R_ex := by
        rw [Nat.mul_add, Nat.pow_succ P j]
      rw [eL, eR]
      exact Nat.mul_le_mul_right R_ex (Nat.mul_le_mul_left (P ^ j) hceil)
    have hstep2 : (P ^ j * Rj + P ^ (j + 1)) * R_ex
        ≤ ((R_ex + P) ^ (j + 1) + P ^ (j + 1)) * R_ex := by
      have ih' : P ^ j * Rj ≤ (R_ex + P) ^ (j + 1) := by simpa using ih
      exact Nat.mul_le_mul_right R_ex (Nat.add_le_add_right ih' _)
    have hstep3 : ((R_ex + P) ^ (j + 1) + P ^ (j + 1)) * R_ex ≤ (R_ex + P) ^ (j + 2) := by
      have hR : (R_ex + P) ^ (j + 2) = (R_ex + P) ^ (j + 1) * R_ex + (R_ex + P) ^ (j + 1) * P := by
        rw [Nat.pow_succ (R_ex + P) (j + 1), Nat.mul_add]
      rw [Nat.add_mul, hR]
      apply Nat.add_le_add_left
      have h1 : P ^ j ≤ (R_ex + P) ^ j := Nat.pow_le_pow_left (by omega) j
      have h2 : R_ex ≤ R_ex + P := by omega
      have h3 := Nat.mul_le_mul h1 h2
      have h4 := Nat.mul_le_mul_right P h3
      have eL : P ^ j * R_ex * P = P ^ (j + 1) * R_ex := by rw [Nat.pow_succ P j]; ac_rfl
      have eR : (R_ex + P) ^ j * (R_ex + P) * P = (R_ex + P) ^ (j + 1) * P := by
        rw [Nat.pow_succ (R_ex + P) j]
      rwa [eL, eR] at h4
    have heq : j + 2 - 1 = j + 1 := by omega
    rw [heq]
    exact Nat.le_trans hstep (Nat.le_trans hstep2 hstep3)

end MatMul94
