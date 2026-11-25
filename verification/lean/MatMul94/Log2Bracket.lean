/-
  MatMul94/Log2Bracket.lean

  Pure-kernel, zero-Mathlib dyadic-exponent bracketing in `Nat` with:
  1. Compositional predicates `Log2Ge x p q := 2^p ≤ x^q` and `Log2Le x p q := x^q ≤ 2^p`.
  2. Verified fixed-point dyadic squaring engine (`checkLog2Ge` / `checkLog2Le`) achieving
     `Q = 2^32` (~9.5 digits) precision on arbitrary natural numbers using only small exponents
     (`≤ 129`), zero `native_decide`, zero floats, and zero external axioms.
  3. Base-2 to base-10 conversion theorems and universal elementary power inequalities
     (`(c+2)^c < 8*c^c`, `((a+1)/a)^a < ((b+1)/b)^(b+1)`, quadratic/cubic AM-GM in `Nat`).
-/

namespace MatMul94

/-- Dyadic lower bracket: `log2 x ≥ p / q`, encoded purely in `Nat` as `2^p ≤ x^q`. -/
def Log2Ge (x p q : Nat) : Prop := 2 ^ p ≤ x ^ q

/-- Dyadic upper bracket: `log2 x ≤ p / q`, encoded purely in `Nat` as `x^q ≤ 2^p`. -/
def Log2Le (x p q : Nat) : Prop := x ^ q ≤ 2 ^ p

/-! ### Elementary `Nat` / `Int` power helpers -/

theorem int_mul_self_nonneg (x : Int) : 0 ≤ x * x := by
  cases x with
  | ofNat n =>
    have hn : (0 : Int) ≤ (n : Int) := Int.natCast_nonneg n
    exact Int.mul_nonneg hn hn
  | negSucc n =>
    have hn : Int.negSucc n ≤ 0 := Int.le_of_lt (Int.negSucc_lt_zero n)
    exact Int.mul_nonneg_of_nonpos_of_nonpos hn hn

theorem pow_pos_of_pos {a : Nat} (ha : 0 < a) (n : Nat) : 0 < a ^ n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ k ih =>
    rw [Nat.pow_succ]
    exact Nat.mul_pos ih ha

theorem pow_lt_pow_left_of_lt {a b n : Nat} (hn : 0 < n) (h : a < b) : a ^ n < b ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => simpa using h
    | succ m =>
      have ih' := ih (Nat.succ_pos m)
      rw [Nat.pow_succ, Nat.pow_succ]
      have h1 : a ^ (m + 1) * a ≤ a ^ (m + 1) * b := Nat.mul_le_mul_left _ (Nat.le_of_lt h)
      have h2 : a ^ (m + 1) * b < b ^ (m + 1) * b :=
        Nat.mul_lt_mul_of_pos_right ih' (Nat.lt_of_le_of_lt (Nat.zero_le a) h)
      exact Nat.lt_of_le_of_lt h1 h2

theorem le_of_pow_le_pow_left {a b n : Nat} (hn : 0 < n) (h : a ^ n ≤ b ^ n) : a ≤ b := by
  by_cases hle : a ≤ b
  · exact hle
  · have hlt := pow_lt_pow_left_of_lt hn (show b < a by omega)
    omega

theorem lt_of_pow_lt_pow_left {a b n : Nat} (h : a ^ n < b ^ n) : a < b := by
  by_cases hlt : a < b
  · exact hlt
  · have := Nat.pow_le_pow_left (show b ≤ a by omega) n
    omega

theorem pow_lt_pow_right_two {i j : Nat} (h : i < j) : 2 ^ i < 2 ^ j := by
  have h1 : 2 ^ i < 2 ^ (i + 1) := by
    rw [Nat.pow_succ]
    have hp := Nat.two_pow_pos i
    omega
  exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) h)

theorem pow_mul_comm_nat (a b n : Nat) : (a * b) ^ n = a ^ n * b ^ n := Nat.mul_pow a b n

theorem le_ceil_div_mul (a d : Nat) (hd : 0 < d) : a ≤ (a + d - 1) / d * d := by
  have h := Nat.lt_div_mul_add (a := a + d - 1) hd
  omega

/-! ### Compositional `Log2Ge` / `Log2Le` calculus -/

theorem Log2Ge.one (q : Nat) : Log2Ge 1 0 q := by unfold Log2Ge; simp
theorem Log2Le.one (q : Nat) : Log2Le 1 0 q := by unfold Log2Le; simp
theorem Log2Ge.two (q : Nat) : Log2Ge 2 q q := Nat.le_refl _
theorem Log2Le.two (q : Nat) : Log2Le 2 q q := Nat.le_refl _

theorem Log2Ge.two_pow (k q : Nat) : Log2Ge (2 ^ k) (k * q) q := by
  unfold Log2Ge; rw [← Nat.pow_mul]; exact Nat.le_refl _

theorem Log2Le.two_pow (k q : Nat) : Log2Le (2 ^ k) (k * q) q := by
  unfold Log2Le; rw [← Nat.pow_mul]; exact Nat.le_refl _

theorem Log2Ge.mono_left {x y p q : Nat} (hxy : x ≤ y) (hx : Log2Ge x p q) : Log2Ge y p q :=
  Nat.le_trans hx (Nat.pow_le_pow_left hxy q)

theorem Log2Le.mono_left {x y p q : Nat} (hxy : x ≤ y) (hy : Log2Le y p q) : Log2Le x p q :=
  Nat.le_trans (Nat.pow_le_pow_left hxy q) hy

theorem Log2Ge.mono_exp {x p1 p2 q : Nat} (hp : p1 ≤ p2) (hx : Log2Ge x p2 q) : Log2Ge x p1 q :=
  Nat.le_trans (Nat.pow_le_pow_right (by decide) hp) hx

theorem Log2Le.mono_exp {x p1 p2 q : Nat} (hp : p1 ≤ p2) (hx : Log2Le x p1 q) : Log2Le x p2 q :=
  Nat.le_trans hx (Nat.pow_le_pow_right (by decide) hp)

theorem Log2Ge.mul {x y p1 p2 q : Nat} (hx : Log2Ge x p1 q) (hy : Log2Ge y p2 q) :
    Log2Ge (x * y) (p1 + p2) q := by
  unfold Log2Ge at *; rw [Nat.pow_add, Nat.mul_pow]; exact Nat.mul_le_mul hx hy

theorem Log2Le.mul {x y p1 p2 q : Nat} (hx : Log2Le x p1 q) (hy : Log2Le y p2 q) :
    Log2Le (x * y) (p1 + p2) q := by
  unfold Log2Le at *; rw [Nat.pow_add, Nat.mul_pow]; exact Nat.mul_le_mul hx hy

theorem Log2Ge.pow {x p q : Nat} (k : Nat) (hx : Log2Ge x p q) :
    Log2Ge (x ^ k) (k * p) q := by
  unfold Log2Ge at *
  calc 2 ^ (k * p)
      = (2 ^ p) ^ k := by rw [Nat.mul_comm, Nat.pow_mul]
    _ ≤ (x ^ q) ^ k := Nat.pow_le_pow_left hx k
    _ = (x ^ k) ^ q := by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]

theorem Log2Le.pow {x p q : Nat} (k : Nat) (hx : Log2Le x p q) :
    Log2Le (x ^ k) (k * p) q := by
  unfold Log2Le at *
  calc (x ^ k) ^ q
      = (x ^ q) ^ k := by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
    _ ≤ (2 ^ p) ^ k := Nat.pow_le_pow_left hx k
    _ = 2 ^ (k * p) := by rw [Nat.mul_comm, Nat.pow_mul]

theorem Log2Ge.rescale {x p q : Nat} (k : Nat) (hx : Log2Ge x p q) :
    Log2Ge x (k * p) (k * q) := by
  unfold Log2Ge at *
  calc 2 ^ (k * p)
      = (2 ^ p) ^ k := by rw [Nat.mul_comm, Nat.pow_mul]
    _ ≤ (x ^ q) ^ k := Nat.pow_le_pow_left hx k
    _ = x ^ (k * q) := by rw [← Nat.pow_mul, Nat.mul_comm]

theorem Log2Le.rescale {x p q : Nat} (k : Nat) (hx : Log2Le x p q) :
    Log2Le x (k * p) (k * q) := by
  unfold Log2Le at *
  calc x ^ (k * q)
      = (x ^ q) ^ k := by rw [Nat.mul_comm, Nat.pow_mul]
    _ ≤ (2 ^ p) ^ k := Nat.pow_le_pow_left hx k
    _ = 2 ^ (k * p) := by rw [Nat.mul_comm, Nat.pow_mul]

theorem Log2Ge.of_mul_ge {a b x p1 p2 q : Nat}
    (h : a ≤ b * x) (ha : Log2Ge a p1 q) (hb : Log2Le b p2 q) (hp : p2 ≤ p1) :
    Log2Ge x (p1 - p2) q := by
  unfold Log2Ge Log2Le at *
  have h1 : 2 ^ (p1 - p2) * 2 ^ p2 ≤ x ^ q * 2 ^ p2 := by
    calc 2 ^ (p1 - p2) * 2 ^ p2
        = 2 ^ ((p1 - p2) + p2) := (Nat.pow_add 2 _ _).symm
      _ = 2 ^ p1 := by rw [Nat.sub_add_cancel hp]
      _ ≤ a ^ q := ha
      _ ≤ (b * x) ^ q := Nat.pow_le_pow_left h q
      _ = b ^ q * x ^ q := Nat.mul_pow b x q
      _ ≤ 2 ^ p2 * x ^ q := Nat.mul_le_mul_right _ hb
      _ = x ^ q * 2 ^ p2 := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_right h1 (Nat.two_pow_pos p2)

theorem Log2Le.of_mul_le {a b x p1 p2 q : Nat}
    (h : b * x ≤ a) (ha : Log2Le a p1 q) (hb : Log2Ge b p2 q) (hp : p2 ≤ p1) :
    Log2Le x (p1 - p2) q := by
  unfold Log2Ge Log2Le at *
  have h1 : x ^ q * 2 ^ p2 ≤ 2 ^ (p1 - p2) * 2 ^ p2 := by
    calc x ^ q * 2 ^ p2
        = 2 ^ p2 * x ^ q := Nat.mul_comm _ _
      _ ≤ b ^ q * x ^ q := Nat.mul_le_mul_right _ hb
      _ = (b * x) ^ q := (Nat.mul_pow b x q).symm
      _ ≤ a ^ q := Nat.pow_le_pow_left h q
      _ ≤ 2 ^ p1 := ha
      _ = 2 ^ ((p1 - p2) + p2) := by rw [Nat.sub_add_cancel hp]
      _ = 2 ^ (p1 - p2) * 2 ^ p2 := Nat.pow_add 2 _ _
  exact Nat.le_of_mul_le_mul_right h1 (Nat.two_pow_pos p2)

theorem Log2Le.div_floor {a b p1 p2 q : Nat}
    (ha : Log2Le a p1 q) (hb : Log2Ge b p2 q) (hp : p2 ≤ p1) :
    Log2Le (a / b) (p1 - p2) q := by
  apply Log2Le.of_mul_le _ ha hb hp
  rw [Nat.mul_comm]
  exact Nat.div_mul_le_self a b

theorem Log2Ge.div_floor {a b p1 p2 q : Nat}
    (ha : Log2Ge a p1 q) (hb : Log2Le b p2 q) (hb_pos : 0 < b) (hba : b ≤ a) (hp : p2 + q ≤ p1) :
    Log2Ge (a / b) (p1 - p2 - q) q := by
  have h1 : 1 ≤ a / b := Nat.div_pos hba hb_pos
  have h2 : a ≤ (2 * b) * (a / b) := by
    have hlt := Nat.lt_div_mul_add (a := a) hb_pos
    have hmul : b * 1 ≤ b * (a / b) := Nat.mul_le_mul_left b h1
    have e1 : a / b * b + b = b * (a / b) + b * 1 := by rw [Nat.mul_comm, Nat.mul_one]
    have e2 : 2 * b * (a / b) = b * (a / b) + b * (a / b) := by rw [Nat.two_mul, Nat.add_mul]
    omega
  have h2b : Log2Le (2 * b) (q + p2) q := (Log2Le.two q).mul hb
  have hres := Log2Ge.of_mul_ge h2 ha h2b (by omega)
  have heq : p1 - (q + p2) = p1 - p2 - q := by omega
  rwa [heq] at hres

/-- Tighter floor-division lower bound: if `m * b ≤ a` (`m ≥ 1`), then
    `m * a ≤ ((m + 1) * b) * (a / b)`, losing only `log2 ((m + 1) / m)` bits. -/
theorem nat_div_ge_tight {a b m : Nat} (hb : 0 < b) (hm : m * b ≤ a) :
    m * a ≤ ((m + 1) * b) * (a / b) := by
  have hq : m ≤ a / b := (Nat.le_div_iff_mul_le hb).2 hm
  have hlt : a < a / b * b + b := Nat.lt_div_mul_add hb
  have h1 : m * a ≤ m * (a / b * b + b) := Nat.mul_le_mul_left m (Nat.le_of_lt hlt)
  have h2 : m * b ≤ (a / b) * b := Nat.mul_le_mul_right b hq
  have h3 : m * (a / b * b + b) = m * (a / b * b) + m * b := Nat.mul_add _ _ _
  have h4 : ((m + 1) * b) * (a / b) = m * (a / b * b) + (a / b) * b := by
    rw [Nat.add_mul, Nat.one_mul, Nat.add_mul]
    have e1 : m * b * (a / b) = m * (a / b * b) := by ac_rfl
    have e2 : b * (a / b) = a / b * b := Nat.mul_comm _ _
    omega
  omega

theorem lt_pow_of_log2 {E v p1 p2 q a b : Nat}
    (hE : Log2Le E p1 q) (hv : Log2Ge v p2 q) (hcmp : p1 * b < p2 * a) :
    E ^ b < v ^ a := by
  apply lt_of_pow_lt_pow_left (n := q)
  calc (E ^ b) ^ q
      = (E ^ q) ^ b := by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
    _ ≤ (2 ^ p1) ^ b := Nat.pow_le_pow_left hE b
    _ = 2 ^ (p1 * b) := (Nat.pow_mul 2 p1 b).symm
    _ < 2 ^ (p2 * a) := pow_lt_pow_right_two hcmp
    _ = (2 ^ p2) ^ a := Nat.pow_mul 2 p2 a
    _ ≤ (v ^ q) ^ a := Nat.pow_le_pow_left hv a
    _ = (v ^ a) ^ q := by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]

theorem le_pow_of_log2 {E v p1 p2 q a b : Nat}
    (hE : Log2Le E p1 q) (hv : Log2Ge v p2 q) (hq : 0 < q) (hcmp : p1 * b ≤ p2 * a) :
    E ^ b ≤ v ^ a := by
  apply le_of_pow_le_pow_left hq
  calc (E ^ b) ^ q
      = (E ^ q) ^ b := by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
    _ ≤ (2 ^ p1) ^ b := Nat.pow_le_pow_left hE b
    _ = 2 ^ (p1 * b) := (Nat.pow_mul 2 p1 b).symm
    _ ≤ 2 ^ (p2 * a) := Nat.pow_le_pow_right (by decide) hcmp
    _ = (2 ^ p2) ^ a := Nat.pow_mul 2 p2 a
    _ ≤ (v ^ q) ^ a := Nat.pow_le_pow_left hv a
    _ = (v ^ a) ^ q := by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]

/-! ### Pure-kernel fixed-point dyadic squaring engine (`Q = 2^32`) -/

/-- Precision scale: `Q = 2^32 = 4,294,967,296` (~9.5 decimal digits of `log2`). -/
abbrev Q_BITS : Nat := 32
abbrev Q_SCALE : Nat := 4294967296
/-- Mantissa bit-width `B = 64` (intermediate powers `≤ 2^129`, well below kernel threshold 256). -/
abbrev M_BITS : Nat := 64

def ScaledGe (B x a e : Nat) : Prop := a * 2 ^ e ≤ x * 2 ^ B
def ScaledLe (B x a e : Nat) : Prop := x * 2 ^ B ≤ a * 2 ^ e

def stepGe (B : Nat) (st : Nat × Nat) : Nat × Nat :=
  let sq := st.1 * st.1
  if 2 ^ (2 * B + 1) ≤ sq then
    (sq / 2 ^ (B + 1), 2 * st.2 + 1)
  else
    (sq / 2 ^ B, 2 * st.2)

def iterGe (B : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, st => st
  | m + 1, st => iterGe B m (stepGe B st)

def initGe (B x : Nat) : Nat × Nat :=
  let k := Nat.log2 x
  ((x * 2 ^ B) / 2 ^ k, k)

theorem stepGe_sound (B x a e : Nat) (h : ScaledGe B x a e) :
    ScaledGe B (x * x) (stepGe B (a, e)).1 (stepGe B (a, e)).2 := by
  unfold ScaledGe at h
  unfold stepGe ScaledGe
  dsimp only
  have hsq : (a * 2 ^ e) * (a * 2 ^ e) ≤ (x * 2 ^ B) * (x * 2 ^ B) := Nat.mul_le_mul h h
  have hsq2 : (a * a) * 2 ^ (2 * e) ≤ (x * x) * 2 ^ (2 * B) := by
    have h1 : (a * 2 ^ e) * (a * 2 ^ e) = (a * a) * 2 ^ (2 * e) := by
      rw [Nat.two_mul, Nat.pow_add]; ac_rfl
    have h2 : (x * 2 ^ B) * (x * 2 ^ B) = (x * x) * 2 ^ (2 * B) := by
      rw [Nat.two_mul, Nat.pow_add]; ac_rfl
    rw [← h1, ← h2]; exact hsq
  split
  · have hdiv : (a * a / 2 ^ (B + 1)) * 2 ^ (B + 1) ≤ a * a := Nat.div_mul_le_self _ _
    have hmul : (a * a / 2 ^ (B + 1)) * 2 ^ (2 * e + 1) * 2 ^ B ≤ (x * x) * 2 ^ B * 2 ^ B := by
      calc (a * a / 2 ^ (B + 1)) * 2 ^ (2 * e + 1) * 2 ^ B
          = ((a * a / 2 ^ (B + 1)) * 2 ^ (B + 1)) * 2 ^ (2 * e) := by
            rw [Nat.pow_succ, Nat.pow_succ]; ac_rfl
        _ ≤ (a * a) * 2 ^ (2 * e) := Nat.mul_le_mul_right _ hdiv
        _ ≤ (x * x) * 2 ^ (2 * B) := hsq2
        _ = (x * x) * 2 ^ B * 2 ^ B := by rw [Nat.two_mul, Nat.pow_add]; ac_rfl
    exact Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos B)
  · have hdiv : (a * a / 2 ^ B) * 2 ^ B ≤ a * a := Nat.div_mul_le_self _ _
    have hmul : (a * a / 2 ^ B) * 2 ^ (2 * e) * 2 ^ B ≤ (x * x) * 2 ^ B * 2 ^ B := by
      calc (a * a / 2 ^ B) * 2 ^ (2 * e) * 2 ^ B
          = ((a * a / 2 ^ B) * 2 ^ B) * 2 ^ (2 * e) := by ac_rfl
        _ ≤ (a * a) * 2 ^ (2 * e) := Nat.mul_le_mul_right _ hdiv
        _ ≤ (x * x) * 2 ^ (2 * B) := hsq2
        _ = (x * x) * 2 ^ B * 2 ^ B := by rw [Nat.two_mul, Nat.pow_add]; ac_rfl
    exact Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos B)

theorem iterGe_sound (B : Nat) : ∀ m x a e,
    ScaledGe B x a e → ScaledGe B (x ^ (2 ^ m)) (iterGe B m (a, e)).1 (iterGe B m (a, e)).2
  | 0, x, a, e, h => by simpa [iterGe] using h
  | m + 1, x, a, e, h => by
    have hstep := stepGe_sound B x a e h
    have ih := iterGe_sound B m (x * x) _ _ hstep
    have hpow : (x * x) ^ (2 ^ m) = x ^ (2 ^ (m + 1)) := by
      rw [← Nat.pow_two, ← Nat.pow_mul, Nat.pow_succ, Nat.mul_comm]
    simpa [iterGe, hpow] using ih

theorem initGe_sound (B x : Nat) : ScaledGe B x (initGe B x).1 (initGe B x).2 := by
  unfold ScaledGe initGe; exact Nat.div_mul_le_self _ _

def checkLog2Ge (B m x p : Nat) : Bool :=
  let st := iterGe B m (initGe B x)
  decide (2 ^ B ≤ st.1 ∧ p ≤ st.2)

theorem log2Ge_of_check (B m x p : Nat) (h : checkLog2Ge B m x p = true) :
    Log2Ge x p (2 ^ m) := by
  unfold checkLog2Ge at h
  have h' : 2 ^ B ≤ (iterGe B m (initGe B x)).1 ∧ p ≤ (iterGe B m (initGe B x)).2 :=
    of_decide_eq_true h
  have hsc := iterGe_sound B m x _ _ (initGe_sound B x)
  unfold ScaledGe at hsc; unfold Log2Ge
  have h1 : 2 ^ p * 2 ^ B ≤ (iterGe B m (initGe B x)).1 * 2 ^ (iterGe B m (initGe B x)).2 := by
    calc 2 ^ p * 2 ^ B
        = 2 ^ B * 2 ^ p := Nat.mul_comm _ _
      _ ≤ (iterGe B m (initGe B x)).1 * 2 ^ (iterGe B m (initGe B x)).2 :=
          Nat.mul_le_mul h'.1 (Nat.pow_le_pow_right (by decide) h'.2)
  exact Nat.le_of_mul_le_mul_right (Nat.le_trans h1 hsc) (Nat.two_pow_pos B)

def stepLe (B : Nat) (st : Nat × Nat) : Nat × Nat :=
  let sq := st.1 * st.1
  if sq ≤ 2 ^ (2 * B + 1) then
    ((sq + 2 ^ B - 1) / 2 ^ B, 2 * st.2)
  else
    ((sq + 2 ^ (B + 1) - 1) / 2 ^ (B + 1), 2 * st.2 + 1)

def iterLe (B : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, st => st
  | m + 1, st => iterLe B m (stepLe B st)

def initLe (B x : Nat) : Nat × Nat :=
  let k := Nat.log2 x
  ((x * 2 ^ B + 2 ^ k - 1) / 2 ^ k, k)

theorem stepLe_sound (B x a e : Nat) (h : ScaledLe B x a e) :
    ScaledLe B (x * x) (stepLe B (a, e)).1 (stepLe B (a, e)).2 := by
  unfold ScaledLe at h
  unfold stepLe ScaledLe
  dsimp only
  have hsq : (x * 2 ^ B) * (x * 2 ^ B) ≤ (a * 2 ^ e) * (a * 2 ^ e) := Nat.mul_le_mul h h
  have hsq2 : (x * x) * 2 ^ (2 * B) ≤ (a * a) * 2 ^ (2 * e) := by
    have h1 : (x * 2 ^ B) * (x * 2 ^ B) = (x * x) * 2 ^ (2 * B) := by
      rw [Nat.two_mul, Nat.pow_add]; ac_rfl
    have h2 : (a * 2 ^ e) * (a * 2 ^ e) = (a * a) * 2 ^ (2 * e) := by
      rw [Nat.two_mul, Nat.pow_add]; ac_rfl
    rw [← h1, ← h2]; exact hsq
  split
  · have hdiv : a * a ≤ ((a * a + 2 ^ B - 1) / 2 ^ B) * 2 ^ B :=
      le_ceil_div_mul (a * a) (2 ^ B) (Nat.two_pow_pos B)
    have hmul : (x * x) * 2 ^ B * 2 ^ B ≤ ((a * a + 2 ^ B - 1) / 2 ^ B) * 2 ^ (2 * e) * 2 ^ B := by
      calc (x * x) * 2 ^ B * 2 ^ B
          = (x * x) * 2 ^ (2 * B) := by rw [Nat.two_mul, Nat.pow_add]; ac_rfl
        _ ≤ (a * a) * 2 ^ (2 * e) := hsq2
        _ ≤ (((a * a + 2 ^ B - 1) / 2 ^ B) * 2 ^ B) * 2 ^ (2 * e) :=
            Nat.mul_le_mul_right _ hdiv
        _ = ((a * a + 2 ^ B - 1) / 2 ^ B) * 2 ^ (2 * e) * 2 ^ B := by ac_rfl
    exact Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos B)
  · have hdiv : a * a ≤ ((a * a + 2 ^ (B + 1) - 1) / 2 ^ (B + 1)) * 2 ^ (B + 1) :=
      le_ceil_div_mul (a * a) (2 ^ (B + 1)) (Nat.two_pow_pos (B + 1))
    have hmul : (x * x) * 2 ^ B * 2 ^ B ≤
        ((a * a + 2 ^ (B + 1) - 1) / 2 ^ (B + 1)) * 2 ^ (2 * e + 1) * 2 ^ B := by
      calc (x * x) * 2 ^ B * 2 ^ B
          = (x * x) * 2 ^ (2 * B) := by rw [Nat.two_mul, Nat.pow_add]; ac_rfl
        _ ≤ (a * a) * 2 ^ (2 * e) := hsq2
        _ ≤ (((a * a + 2 ^ (B + 1) - 1) / 2 ^ (B + 1)) * 2 ^ (B + 1)) * 2 ^ (2 * e) :=
            Nat.mul_le_mul_right _ hdiv
        _ = ((a * a + 2 ^ (B + 1) - 1) / 2 ^ (B + 1)) * 2 ^ (2 * e + 1) * 2 ^ B := by
            rw [Nat.pow_succ, Nat.pow_succ]; ac_rfl
    exact Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos B)

theorem iterLe_sound (B : Nat) : ∀ m x a e,
    ScaledLe B x a e → ScaledLe B (x ^ (2 ^ m)) (iterLe B m (a, e)).1 (iterLe B m (a, e)).2
  | 0, x, a, e, h => by simpa [iterLe] using h
  | m + 1, x, a, e, h => by
    have hstep := stepLe_sound B x a e h
    have ih := iterLe_sound B m (x * x) _ _ hstep
    have hpow : (x * x) ^ (2 ^ m) = x ^ (2 ^ (m + 1)) := by
      rw [← Nat.pow_two, ← Nat.pow_mul, Nat.pow_succ, Nat.mul_comm]
    simpa [iterLe, hpow] using ih

theorem initLe_sound (B x : Nat) : ScaledLe B x (initLe B x).1 (initLe B x).2 := by
  unfold ScaledLe initLe
  exact le_ceil_div_mul (x * 2 ^ B) (2 ^ Nat.log2 x) (Nat.two_pow_pos _)

def checkLog2Le (B m x p : Nat) : Bool :=
  let st := iterLe B m (initLe B x)
  decide ((st.1 ≤ 2 ^ B ∧ st.2 ≤ p) ∨ (st.1 ≤ 2 ^ (B + 1) ∧ st.2 + 1 ≤ p))

theorem log2Le_of_check (B m x p : Nat) (h : checkLog2Le B m x p = true) :
    Log2Le x p (2 ^ m) := by
  unfold checkLog2Le at h
  have h' := of_decide_eq_true h
  have hsc := iterLe_sound B m x _ _ (initLe_sound B x)
  unfold ScaledLe at hsc; unfold Log2Le
  cases h' with
  | inl hl =>
    have h1 : (iterLe B m (initLe B x)).1 * 2 ^ (iterLe B m (initLe B x)).2 ≤ 2 ^ p * 2 ^ B := by
      calc (iterLe B m (initLe B x)).1 * 2 ^ (iterLe B m (initLe B x)).2
          ≤ 2 ^ B * 2 ^ p := Nat.mul_le_mul hl.1 (Nat.pow_le_pow_right (by decide) hl.2)
        _ = 2 ^ p * 2 ^ B := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right (Nat.le_trans hsc h1) (Nat.two_pow_pos B)
  | inr hr =>
    have h1 : (iterLe B m (initLe B x)).1 * 2 ^ (iterLe B m (initLe B x)).2 ≤ 2 ^ p * 2 ^ B := by
      calc (iterLe B m (initLe B x)).1 * 2 ^ (iterLe B m (initLe B x)).2
          ≤ 2 ^ (B + 1) * 2 ^ (iterLe B m (initLe B x)).2 := Nat.mul_le_mul_right _ hr.1
        _ = 2 ^ ((iterLe B m (initLe B x)).2 + 1) * 2 ^ B := by
            rw [Nat.pow_succ, Nat.pow_succ]; ac_rfl
        _ ≤ 2 ^ p * 2 ^ B := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hr.2)
    exact Nat.le_of_mul_le_mul_right (Nat.le_trans hsc h1) (Nat.two_pow_pos B)

/-- Convenience wrappers pinned to `B = 64, m = 32` (`Q_SCALE = 2^32 = 4294967296`). -/
theorem log2Ge_Q (x p : Nat) (h : checkLog2Ge M_BITS Q_BITS x p = true) :
    Log2Ge x p Q_SCALE := log2Ge_of_check M_BITS Q_BITS x p h

theorem log2Le_Q (x p : Nat) (h : checkLog2Le M_BITS Q_BITS x p = true) :
    Log2Le x p Q_SCALE := log2Le_of_check M_BITS Q_BITS x p h

/-! ### Base-10 conversion certificates and verified small-integer `log2` table -/

theorem log2Ge_10 : Log2Ge 10 14267572527 Q_SCALE := log2Ge_Q 10 14267572527 (by decide)
theorem log2Le_10 : Log2Le 10 14267572528 Q_SCALE := log2Le_Q 10 14267572528 (by decide)

theorem pow10_le_of_log2 {x p q M : Nat}
    (hx : Log2Ge x p q) (hq : 0 < q) (h : M * q * 14267572528 ≤ p * Q_SCALE) :
    10 ^ M ≤ x := by
  have h10 : Log2Le 10 (14267572528 * q) (Q_SCALE * q) := by
    have := log2Le_10.rescale q; simpa [Nat.mul_comm] using this
  have hx' : Log2Ge x (p * Q_SCALE) (Q_SCALE * q) := by
    have := hx.rescale Q_SCALE; simpa [Nat.mul_comm] using this
  have hcmp : (14267572528 * q) * M ≤ (p * Q_SCALE) * 1 := by
    have heq : (14267572528 * q) * M = M * q * 14267572528 := by ac_rfl
    rw [heq, Nat.mul_one]; exact h
  have := le_pow_of_log2 h10 hx' (Nat.mul_pos (by decide) hq) hcmp
  simpa using this

theorem pow10_lt_of_log2 {x p q M : Nat}
    (hx : Log2Ge x p q) (h : M * q * 14267572528 < p * Q_SCALE) :
    10 ^ M < x := by
  have h10 : Log2Le 10 (14267572528 * q) (Q_SCALE * q) := by
    have := log2Le_10.rescale q; simpa [Nat.mul_comm] using this
  have hx' : Log2Ge x (p * Q_SCALE) (Q_SCALE * q) := by
    have := hx.rescale Q_SCALE; simpa [Nat.mul_comm] using this
  have hcmp : (14267572528 * q) * M < (p * Q_SCALE) * 1 := by
    have heq : (14267572528 * q) * M = M * q * 14267572528 := by ac_rfl
    rw [heq, Nat.mul_one]; exact h
  have := lt_pow_of_log2 h10 hx' hcmp
  simpa using this

theorem le_pow10_of_log2 {x p q M : Nat}
    (hx : Log2Le x p q) (hq : 0 < q) (h : p * Q_SCALE ≤ M * q * 14267572527) :
    x ≤ 10 ^ M := by
  have h10 : Log2Ge 10 (14267572527 * q) (Q_SCALE * q) := by
    have := log2Ge_10.rescale q; simpa [Nat.mul_comm] using this
  have hx' : Log2Le x (p * Q_SCALE) (Q_SCALE * q) := by
    have := hx.rescale Q_SCALE; simpa [Nat.mul_comm] using this
  have hcmp : (p * Q_SCALE) * 1 ≤ (14267572527 * q) * M := by
    have heq : (14267572527 * q) * M = M * q * 14267572527 := by ac_rfl
    rw [heq, Nat.mul_one]; exact h
  have := le_pow_of_log2 hx' h10 (Nat.mul_pos (by decide) hq) hcmp
  simpa using this

theorem pow10_le_pow2_of_mul (a b : Nat) (h : 14267572528 * a ≤ Q_SCALE * b) :
    10 ^ a ≤ 2 ^ b :=
  le_pow_of_log2 log2Le_10 (Log2Ge.two Q_SCALE) (by decide) h

theorem pow2_le_pow10_of_mul (a b : Nat) (h : Q_SCALE * b ≤ 14267572527 * a) :
    2 ^ b ≤ 10 ^ a :=
  le_pow_of_log2 (Log2Le.two Q_SCALE) log2Ge_10 (by decide) h

theorem pow10_301_le_pow2_1000 : 10 ^ 301 ≤ 2 ^ 1000 := pow10_le_pow2_of_mul 301 1000 (by decide)
theorem pow2_1000_le_pow10_302 : 2 ^ 1000 ≤ 10 ^ 302 := pow2_le_pow10_of_mul 302 1000 (by decide)
theorem pow10_1000_le_pow2_3322 : 10 ^ 1000 ≤ 2 ^ 3322 := pow10_le_pow2_of_mul 1000 3322 (by decide)
theorem pow2_3321_le_pow10_1000 : 2 ^ 3321 ≤ 10 ^ 1000 := pow2_le_pow10_of_mul 1000 3321 (by decide)

/-- Verified `Q_SCALE = 2^32` brackets for key small integers used across the paper. -/
theorem log2Ge_3   : Log2Ge 3   6807362105  Q_SCALE := log2Ge_Q 3   6807362105  (by decide)
theorem log2Le_3   : Log2Le 3   6807362106  Q_SCALE := log2Le_Q 3   6807362106  (by decide)
theorem log2Ge_5   : Log2Ge 5   9972605231  Q_SCALE := log2Ge_Q 5   9972605231  (by decide)
theorem log2Le_5   : Log2Le 5   9972605232  Q_SCALE := log2Le_Q 5   9972605232  (by decide)
theorem log2Ge_6   : Log2Ge 6   11102329401 Q_SCALE := log2Ge_Q 6   11102329401 (by decide)
theorem log2Le_6   : Log2Le 6   11102329402 Q_SCALE := log2Le_Q 6   11102329402 (by decide)
theorem log2Ge_7   : Log2Ge 7   12057497578 Q_SCALE := log2Ge_Q 7   12057497578 (by decide)
theorem log2Le_7   : Log2Le 7   12057497579 Q_SCALE := log2Le_Q 7   12057497579 (by decide)
theorem log2Ge_8   : Log2Ge 8   12884901888 Q_SCALE := log2Ge_Q 8   12884901888 (by decide)
theorem log2Le_8   : Log2Le 8   12884901888 Q_SCALE := log2Le_Q 8   12884901888 (by decide)
theorem log2Ge_9   : Log2Ge 9   13614724211 Q_SCALE := log2Ge_Q 9   13614724211 (by decide)
theorem log2Le_9   : Log2Le 9   13614724212 Q_SCALE := log2Le_Q 9   13614724212 (by decide)
theorem log2Ge_12  : Log2Ge 12  15397296697 Q_SCALE := log2Ge_Q 12  15397296697 (by decide)
theorem log2Le_12  : Log2Le 12  15397296698 Q_SCALE := log2Le_Q 12  15397296698 (by decide)
theorem log2Ge_14  : Log2Ge 14  16352464874 Q_SCALE := log2Ge_Q 14  16352464874 (by decide)
theorem log2Le_14  : Log2Le 14  16352464875 Q_SCALE := log2Le_Q 14  16352464875 (by decide)
theorem log2Ge_21  : Log2Ge 21  18864859684 Q_SCALE := log2Ge_Q 21  18864859684 (by decide)
theorem log2Le_21  : Log2Le 21  18864859685 Q_SCALE := log2Le_Q 21  18864859685 (by decide)
theorem log2Ge_22  : Log2Ge 22  19153112960 Q_SCALE := log2Ge_Q 22  19153112960 (by decide)
theorem log2Le_22  : Log2Le 22  19153112961 Q_SCALE := log2Le_Q 22  19153112961 (by decide)
theorem log2Ge_23  : Log2Ge 23  19428550662 Q_SCALE := log2Ge_Q 23  19428550662 (by decide)
theorem log2Le_23  : Log2Le 23  19428550663 Q_SCALE := log2Le_Q 23  19428550663 (by decide)
theorem log2Ge_24  : Log2Ge 24  19692263993 Q_SCALE := log2Ge_Q 24  19692263993 (by decide)
theorem log2Le_24  : Log2Le 24  19692263994 Q_SCALE := log2Le_Q 24  19692263994 (by decide)
theorem log2Ge_26  : Log2Ge 26  20188234866 Q_SCALE := log2Ge_Q 26  20188234866 (by decide)
theorem log2Le_26  : Log2Le 26  20188234867 Q_SCALE := log2Le_Q 26  20188234867 (by decide)
theorem log2Ge_42  : Log2Ge 42  23159826980 Q_SCALE := log2Ge_Q 42  23159826980 (by decide)
theorem log2Le_42  : Log2Le 42  23159826981 Q_SCALE := log2Le_Q 42  23159826981 (by decide)
theorem log2Ge_44  : Log2Ge 44  23448080256 Q_SCALE := log2Ge_Q 44  23448080256 (by decide)
theorem log2Le_44  : Log2Le 44  23448080257 Q_SCALE := log2Le_Q 44  23448080257 (by decide)
theorem log2Ge_57  : Log2Ge 57  25052071852 Q_SCALE := log2Ge_Q 57  25052071852 (by decide)
theorem log2Le_57  : Log2Le 57  25052071853 Q_SCALE := log2Le_Q 57  25052071853 (by decide)
theorem log2Ge_59  : Log2Ge 59  25265759511 Q_SCALE := log2Ge_Q 59  25265759511 (by decide)
theorem log2Le_59  : Log2Le 59  25265759512 Q_SCALE := log2Le_Q 59  25265759512 (by decide)
theorem log2Ge_64  : Log2Ge 64  25769803776 Q_SCALE := log2Ge_Q 64  25769803776 (by decide)
theorem log2Le_64  : Log2Le 64  25769803776 Q_SCALE := log2Le_Q 64  25769803776 (by decide)
theorem log2Ge_304 : Log2Ge 304 35424578930 Q_SCALE := log2Ge_Q 304 35424578930 (by decide)
theorem log2Le_304 : Log2Le 304 35424578931 Q_SCALE := log2Le_Q 304 35424578931 (by decide)
theorem log2Ge_306 : Log2Ge 306 35465210734 Q_SCALE := log2Ge_Q 306 35465210734 (by decide)
theorem log2Le_306 : Log2Le 306 35465210735 Q_SCALE := log2Le_Q 306 35465210735 (by decide)

/-! ### Universal elementary power inequalities in pure `Nat` -/

/-- Helper: lift `Nat` equality/inequality via `Int` ring `grind`. -/
theorem nat_eq_of_int {x y : Nat} (h : (x : Int) = (y : Int)) : x = y := Int.ofNat.inj h
theorem nat_le_of_int {x y : Nat} (h : (x : Int) ≤ (y : Int)) : x ≤ y := Int.ofNat_le.mp h

/-- Three-term binomial lower bound: `(a + 2)^n ≥ a^n + 2*n*a^(n-1) + 2*n*(n-1)*a^(n-2)` for `n ≥ 2`. -/
theorem pow_add_two_ge_quad (a : Nat) : ∀ n, 2 ≤ n →
    a ^ n + 2 * n * a ^ (n - 1) + 2 * n * (n - 1) * a ^ (n - 2) ≤ (a + 2) ^ n
  | 0, h => by omega
  | 1, h => by omega
  | 2, _ => by
    have : a ^ 2 + 2 * 2 * a ^ (2 - 1) + 2 * 2 * (2 - 1) * a ^ (2 - 2) = (a + 2) ^ 2 := by grind
    exact Nat.le_of_eq this
  | n + 3, _ => by
    have ih := pow_add_two_ge_quad a (n + 2) (by omega)
    have hsub1 : n + 2 - 1 = n + 1 := by omega
    have hsub2 : n + 2 - 2 = n := by omega
    rw [hsub1, hsub2] at ih
    have hmul : (a + 2) * (a ^ (n + 2) + 2 * (n + 2) * a ^ (n + 1) + 2 * (n + 2) * (n + 1) * a ^ n)
        ≤ (a + 2) ^ (n + 3) := by
      have hp : (a + 2) ^ (n + 3) = (a + 2) * (a + 2) ^ (n + 2) := by
        rw [Nat.pow_succ (a + 2) (n + 2), Nat.mul_comm]
      rw [hp]
      exact Nat.mul_le_mul_left (a + 2) ih
    have hexp : a ^ (n + 3) + 2 * (n + 3) * a ^ (n + 2) + 2 * (n + 3) * (n + 2) * a ^ (n + 1) ≤
        (a + 2) * (a ^ (n + 2) + 2 * (n + 2) * a ^ (n + 1) + 2 * (n + 2) * (n + 1) * a ^ n) := by
      have hp3 : a ^ (n + 3) = a * a ^ (n + 2) := by rw [Nat.pow_succ a (n + 2), Nat.mul_comm]
      have hp2 : a ^ (n + 2) = a * a ^ (n + 1) := by rw [Nat.pow_succ a (n + 1), Nat.mul_comm]
      have hp1 : a ^ (n + 1) = a * a ^ n := by rw [Nat.pow_succ a n, Nat.mul_comm]
      rw [hp3, hp2, hp1]
      have hid : (a + 2) * (a * (a * a ^ n) + 2 * (n + 2) * (a * a ^ n) + 2 * (n + 2) * (n + 1) * a ^ n)
          = a * (a * (a * a ^ n)) + 2 * (n + 3) * (a * (a * a ^ n)) + 2 * (n + 3) * (n + 2) * (a * a ^ n)
            + 4 * (n + 2) * (n + 1) * a ^ n := by grind
      omega
    have hsub3 : n + 3 - 1 = n + 2 := by omega
    have hsub4 : n + 3 - 2 = n + 1 := by omega
    rw [hsub3, hsub4]
    exact Nat.le_trans hexp hmul

/-- Monotone decrease of `((c + 2) / c)^(c + 1)` for `c ≥ 1`:
    `(c + 3)^(c + 2) * c^(c + 1) < (c + 1)^(c + 2) * (c + 2)^(c + 1)`. -/
theorem add_two_ratio_succ_dec (c : Nat) (hc : 1 ≤ c) :
    (c + 3) ^ (c + 2) * c ^ (c + 1) < (c + 1) ^ (c + 2) * (c + 2) ^ (c + 1) := by
  let a := c * (c + 3)
  have ha2 : a + 2 = (c + 1) * (c + 2) := by dsimp only [a]; grind
  have hbin := pow_add_two_ge_quad a (c + 1) (by omega)
  have heq1 : c + 1 - 1 = c := by omega
  have heq2 : c + 1 - 2 = c - 1 := by omega
  rw [heq1, heq2] at hbin
  have hmul : (c + 1) * (a ^ (c + 1) + 2 * (c + 1) * a ^ c + 2 * (c + 1) * c * a ^ (c - 1))
      ≤ (c + 1) * (a + 2) ^ (c + 1) := Nat.mul_le_mul_left (c + 1) hbin
  have hpoly_eq : (c + 3) * a ^ 2 + 8 * c = (c + 1) * (a ^ 2 + 2 * (c + 1) * a + 2 * (c + 1) * c) := by
    dsimp only [a]; grind
  have hpoly : (c + 3) * a ^ 2 < (c + 1) * (a ^ 2 + 2 * (c + 1) * a + 2 * (c + 1) * c) := by omega
  have ha_pos : 0 < a := Nat.mul_pos hc (by omega)
  have hpow_pos : 0 < a ^ (c - 1) := pow_pos_of_pos ha_pos (c - 1)
  have hlt_a : (c + 3) * a ^ (c + 1) < (c + 1) * (a + 2) ^ (c + 1) := by
    have h1 := Nat.mul_lt_mul_of_pos_right hpoly hpow_pos
    have h2c : 2 + (c - 1) = c + 1 := by omega
    have h1c : (c - 1) + 1 = c := by omega
    have f1 : a ^ 2 * a ^ (c - 1) = a ^ (c + 1) := by rw [← Nat.pow_add, h2c]
    have f2 : a * a ^ (c - 1) = a ^ c := by
      calc a * a ^ (c - 1) = a ^ ((c - 1) + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
        _ = a ^ c := by rw [h1c]
    have he1 : (c + 3) * a ^ 2 * a ^ (c - 1) = (c + 3) * a ^ (c + 1) := by
      rw [Nat.mul_assoc, f1]
    have he2 : (c + 1) * (a ^ 2 + 2 * (c + 1) * a + 2 * (c + 1) * c) * a ^ (c - 1)
        = (c + 1) * (a ^ (c + 1) + 2 * (c + 1) * a ^ c + 2 * (c + 1) * c * a ^ (c - 1)) := by
      rw [Nat.mul_assoc]
      apply congrArg ((c + 1) * ·)
      rw [Nat.add_mul, Nat.add_mul, f1, Nat.mul_assoc (2 * (c + 1)) a (a ^ (c - 1)), f2]
    rw [he1, he2] at h1
    exact Nat.lt_of_lt_of_le h1 hmul
  have hlhs_eq : (c + 3) ^ (c + 2) * c ^ (c + 1) = (c + 3) * a ^ (c + 1) := by
    dsimp only [a]; rw [Nat.mul_pow, Nat.pow_succ (c + 3) (c + 1)]; ac_rfl
  have hrhs_eq : (c + 1) ^ (c + 2) * (c + 2) ^ (c + 1) = (c + 1) * (a + 2) ^ (c + 1) := by
    rw [ha2, Nat.mul_pow, Nat.pow_succ (c + 1) (c + 1)]; ac_rfl
  rw [hlhs_eq, hrhs_eq]
  exact hlt_a

/-- For all `c ≥ 2`, `(c + 2)^(c + 1) ≤ 8 * c^(c + 1)`. -/
theorem add_two_pow_succ_le_eight : ∀ c, 2 ≤ c → (c + 2) ^ (c + 1) ≤ 8 * c ^ (c + 1)
  | 0, h => by omega
  | 1, h => by omega
  | 2, _ => by decide
  | c + 3, _ => by
    have ih := add_two_pow_succ_le_eight (c + 2) (by omega)
    have hdec := add_two_ratio_succ_dec (c + 2) (by omega)
    have h1 : (c + 5) ^ (c + 4) * (c + 2) ^ (c + 3)
        ≤ (c + 3) ^ (c + 4) * (c + 4) ^ (c + 3) := Nat.le_of_lt hdec
    have h2 : (c + 3) ^ (c + 4) * (c + 4) ^ (c + 3)
        ≤ (c + 3) ^ (c + 4) * (8 * (c + 2) ^ (c + 3)) := Nat.mul_le_mul_left _ ih
    have h3 : (c + 5) ^ (c + 4) * (c + 2) ^ (c + 3)
        ≤ (8 * (c + 3) ^ (c + 4)) * (c + 2) ^ (c + 3) := by
      have : (c + 3) ^ (c + 4) * (8 * (c + 2) ^ (c + 3))
          = (8 * (c + 3) ^ (c + 4)) * (c + 2) ^ (c + 3) := by ac_rfl
      exact Nat.le_trans h1 (this ▸ h2)
    exact Nat.le_of_mul_le_mul_right h3 (pow_pos_of_pos (by omega) (c + 3))

/-- Exact elementary bound `(c + 2)^c < 8 * c^c` for all `c ≥ 2` (i.e. `(1 + 2/c)^c < e^2 < 8`). -/
theorem add_two_pow_lt_eight (c : Nat) (hc : 2 ≤ c) : (c + 2) ^ c < 8 * c ^ c := by
  have h1 := add_two_pow_succ_le_eight c hc
  have h2 : c * (c + 2) ^ c < (c + 2) * (c + 2) ^ c :=
    Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos_of_pos (by omega) c)
  have h3 : (c + 2) * (c + 2) ^ c = (c + 2) ^ (c + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have h4 : 8 * c ^ (c + 1) = c * (8 * c ^ c) := by rw [Nat.pow_succ]; ac_rfl
  rw [h3] at h2
  have h5 : c * (c + 2) ^ c < c * (8 * c ^ c) := Nat.lt_of_lt_of_le h2 (h4 ▸ h1)
  exact Nat.lt_of_mul_lt_mul_left h5

/-- Bernoulli-type lower bound without subtraction: `N^a ≤ (N - 1)^a + a * N^(a - 1)`. -/
theorem bernoulli_sub_one (N : Nat) (hN : 1 ≤ N) : ∀ a, 1 ≤ a →
    N ^ a ≤ (N - 1) ^ a + a * N ^ (a - 1)
  | 0, h => by omega
  | 1, _ => by simp; omega
  | a + 2, _ => by
    have ih := bernoulli_sub_one N hN (a + 1) (by omega)
    have hsub1 : a + 1 - 1 = a := by omega
    rw [hsub1] at ih
    have hmul : (N - 1) * N ^ (a + 1) ≤ (N - 1) * ((N - 1) ^ (a + 1) + (a + 1) * N ^ a) :=
      Nat.mul_le_mul_left (N - 1) ih
    have hsplit : N ^ (a + 2) = (N - 1) * N ^ (a + 1) + N ^ (a + 1) := by
      have hN1 : (N - 1) + 1 = N := by omega
      calc N ^ (a + 2) = N * N ^ (a + 1) := by rw [Nat.pow_succ N (a + 1), Nat.mul_comm]
        _ = ((N - 1) + 1) * N ^ (a + 1) := by rw [hN1]
        _ = (N - 1) * N ^ (a + 1) + N ^ (a + 1) := by rw [Nat.add_mul, Nat.one_mul]
    have hstep : (N - 1) * ((a + 1) * N ^ a) ≤ (a + 1) * N ^ (a + 1) := by
      have hle : (N - 1) * N ^ a ≤ N * N ^ a := Nat.mul_le_mul_right _ (by omega)
      have h1 : (N - 1) * ((a + 1) * N ^ a) = (a + 1) * ((N - 1) * N ^ a) := by ac_rfl
      have h2 : (a + 1) * (N * N ^ a) = (a + 1) * N ^ (a + 1) := by rw [Nat.pow_succ N a]; ac_rfl
      rw [h1, ← h2]
      exact Nat.mul_le_mul_left (a + 1) hle
    have hpow_sub : (N - 1) * (N - 1) ^ (a + 1) = (N - 1) ^ (a + 2) := by
      rw [Nat.pow_succ (N - 1) (a + 1), Nat.mul_comm]
    rw [Nat.mul_add, hpow_sub] at hmul
    have hadd : (a + 1) * N ^ (a + 1) + N ^ (a + 1) = (a + 2) * N ^ (a + 1) := by grind
    have heq : a + 2 - 1 = a + 1 := by omega
    rw [heq, hsplit]
    omega

/-- Positive Bernoulli lower bound: `M^n + n * M^(n - 1) ≤ (M + 1)^n` for `n ≥ 1`. -/
theorem bernoulli_add_one (M : Nat) : ∀ n, 1 ≤ n → M ^ n + n * M ^ (n - 1) ≤ (M + 1) ^ n
  | 0, h => by omega
  | 1, _ => by simp
  | n + 2, _ => by
    have ih := bernoulli_add_one M (n + 1) (by omega)
    have hsub1 : n + 1 - 1 = n := by omega
    rw [hsub1] at ih
    have hmul : (M + 1) * (M ^ (n + 1) + (n + 1) * M ^ n) ≤ (M + 1) ^ (n + 2) := by
      have hp : (M + 1) ^ (n + 2) = (M + 1) * (M + 1) ^ (n + 1) := by
        rw [Nat.pow_succ (M + 1) (n + 1), Nat.mul_comm]
      rw [hp]
      exact Nat.mul_le_mul_left (M + 1) ih
    have hexp : M ^ (n + 2) + (n + 2) * M ^ (n + 1)
        ≤ (M + 1) * (M ^ (n + 1) + (n + 1) * M ^ n) := by
      have e1 : M ^ (n + 2) = M * M ^ (n + 1) := by rw [Nat.pow_succ M (n + 1), Nat.mul_comm]
      have e2 : M ^ (n + 1) = M * M ^ n := by rw [Nat.pow_succ M n, Nat.mul_comm]
      rw [e1, e2]
      have hid : (M + 1) * (M * M ^ n + (n + 1) * M ^ n)
          = M * (M * M ^ n) + (n + 2) * (M * M ^ n) + (n + 1) * M ^ n := by grind
      omega
    have heq : n + 2 - 1 = n + 1 := by omega
    rw [heq]
    exact Nat.le_trans hexp hmul

/-- Strict increase of `((a + 1) / a)^a`: `(a + 1)^(2*a + 1) < a^a * (a + 2)^(a + 1)`. -/
theorem e_mono_inc (a : Nat) (ha : 1 ≤ a) :
    (a + 1) ^ (2 * a + 1) < a ^ a * (a + 2) ^ (a + 1) := by
  let N := (a + 1) * (a + 1)
  have hN1 : N - 1 = a * (a + 2) := by
    have : N = a * (a + 2) + 1 := by dsimp only [N]; grind
    omega
  have hNpos0 : 1 ≤ N := Nat.mul_pos (by omega) (by omega)
  have hbern := bernoulli_sub_one N hNpos0 a ha
  have hmul : (a + 2) * N ^ a ≤ (a + 2) * (N - 1) ^ a + (a + 2) * a * N ^ (a - 1) := by
    have h0 := Nat.mul_le_mul_left (a + 2) hbern
    rw [Nat.mul_add] at h0
    have e1 : (a + 2) * (a * N ^ (a - 1)) = (a + 2) * a * N ^ (a - 1) := by ac_rfl
    omega
  have hNpow : N ^ a = N * N ^ (a - 1) := by
    have ha1 : (a - 1) + 1 = a := by omega
    calc N ^ a = N ^ ((a - 1) + 1) := by rw [ha1]
      _ = N * N ^ (a - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have hcoeff : (a + 1) * N + (a + 2) * a + 1 = (a + 2) * N := by dsimp only [N]; grind
  have hNpos : 0 < N ^ (a - 1) := pow_pos_of_pos hNpos0 _
  have hlt : (a + 1) * N ^ a < (a + 2) * (N - 1) ^ a := by
    have hstep : (a + 1) * N * N ^ (a - 1) + (a + 2) * a * N ^ (a - 1) + N ^ (a - 1)
        = (a + 2) * N * N ^ (a - 1) := by
      have : ((a + 1) * N + (a + 2) * a + 1) * N ^ (a - 1) = (a + 2) * N * N ^ (a - 1) := by
        rw [hcoeff]
      grind
    rw [hNpow] at hmul ⊢
    have e1 : (a + 1) * (N * N ^ (a - 1)) = (a + 1) * N * N ^ (a - 1) := by ac_rfl
    have e2 : (a + 2) * (N * N ^ (a - 1)) = (a + 2) * N * N ^ (a - 1) := by ac_rfl
    omega
  have hlhs : (a + 1) ^ (2 * a + 1) = (a + 1) * N ^ a := by
    dsimp only [N]
    rw [← Nat.pow_two, ← Nat.pow_mul, Nat.pow_succ (a + 1) (2 * a), Nat.mul_comm]
  have hrhs : a ^ a * (a + 2) ^ (a + 1) = (a + 2) * (N - 1) ^ a := by
    rw [hN1, Nat.mul_pow, Nat.pow_succ (a + 2) a]; ac_rfl
  rw [hlhs, hrhs]
  exact hlt

/-- Strict decrease of `((b + 1) / b)^(b + 1)`:
    `(b + 2)^(b + 2) * b^(b + 1) < (b + 1)^(2*b + 3)`. -/
theorem e_mono_dec (b : Nat) (hb : 1 ≤ b) :
    (b + 2) ^ (b + 2) * b ^ (b + 1) < (b + 1) ^ (2 * b + 3) := by
  let M := b * (b + 2)
  have hM1 : M + 1 = (b + 1) * (b + 1) := by dsimp only [M]; grind
  have hbern := bernoulli_add_one M (b + 1) (by omega)
  have hsub : b + 1 - 1 = b := by omega
  rw [hsub] at hbern
  have hmul : (b + 1) * (M ^ (b + 1) + (b + 1) * M ^ b) ≤ (b + 1) * (M + 1) ^ (b + 1) :=
    Nat.mul_le_mul_left (b + 1) hbern
  have hcoeff : (b + 2) * M + 1 = (b + 1) * M + (b + 1) * (b + 1) := by dsimp only [M]; grind
  have hMpos : 0 < M ^ b := pow_pos_of_pos (Nat.mul_pos hb (by omega)) b
  have hlt : (b + 2) * M ^ (b + 1) < (b + 1) * (M + 1) ^ (b + 1) := by
    have hp : M ^ (b + 1) = M * M ^ b := by rw [Nat.pow_succ M b, Nat.mul_comm]
    have h1 : (b + 2) * M ^ (b + 1) + M ^ b = (b + 1) * (M ^ (b + 1) + (b + 1) * M ^ b) := by
      rw [hp]; dsimp only [M]; grind
    omega
  have hlhs : (b + 2) ^ (b + 2) * b ^ (b + 1) = (b + 2) * M ^ (b + 1) := by
    dsimp only [M]; rw [Nat.mul_pow, Nat.pow_succ (b + 2) (b + 1)]; ac_rfl
  have hrhs : (b + 1) ^ (2 * b + 3) = (b + 1) * (M + 1) ^ (b + 1) := by
    have h2b : 2 * (b + 1) + 1 = 2 * b + 3 := by omega
    rw [hM1, ← Nat.pow_two, ← Nat.pow_mul, ← h2b, Nat.pow_succ (b + 1) (2 * (b + 1)), Nat.mul_comm]
  rw [hlhs, hrhs]
  exact hlt

/-- Induction helper: `((a + 1) / a)^a ≤ ((c + 1) / c)^c` for `1 ≤ a ≤ c`. -/
theorem e_inc_le (a c : Nat) (ha : 1 ≤ a) (hac : a ≤ c) :
    (a + 1) ^ a * c ^ c ≤ a ^ a * (c + 1) ^ c := by
  induction hac with
  | refl => exact Nat.le_of_eq (Nat.mul_comm _ _)
  | @step m hm ih =>
    have hm' : a ≤ m := hm
    have hstep := Nat.le_of_lt (e_mono_inc m (by omega))
    have h1 : (a + 1) ^ a * m ^ m * (m + 1) ^ (m + 1) ≤ a ^ a * (m + 1) ^ m * (m + 1) ^ (m + 1) :=
      Nat.mul_le_mul_right _ ih
    have h2 : a ^ a * ((m + 1) ^ m * (m + 1) ^ (m + 1)) ≤ a ^ a * (m ^ m * (m + 2) ^ (m + 1)) := by
      have hm2 : m + (m + 1) = 2 * m + 1 := by omega
      have heq : (m + 1) ^ m * (m + 1) ^ (m + 1) = (m + 1) ^ (2 * m + 1) := by
        rw [← Nat.pow_add, hm2]
      rw [heq]
      exact Nat.mul_le_mul_left _ hstep
    have h3 : ((a + 1) ^ a * (m + 1) ^ (m + 1)) * m ^ m ≤ (a ^ a * (m + 2) ^ (m + 1)) * m ^ m := by
      have e1 : ((a + 1) ^ a * (m + 1) ^ (m + 1)) * m ^ m = (a + 1) ^ a * m ^ m * (m + 1) ^ (m + 1) := by ac_rfl
      have e2 : a ^ a * (m + 1) ^ m * (m + 1) ^ (m + 1) = a ^ a * ((m + 1) ^ m * (m + 1) ^ (m + 1)) := by ac_rfl
      have e3 : a ^ a * (m ^ m * (m + 2) ^ (m + 1)) = (a ^ a * (m + 2) ^ (m + 1)) * m ^ m := by ac_rfl
      rw [e1, ← e3]
      exact Nat.le_trans h1 (e2 ▸ h2)
    exact Nat.le_of_mul_le_mul_right h3 (pow_pos_of_pos (by omega) m)

/-- Induction helper: `((c + 1) / c)^(c + 1) ≤ ((b + 1) / b)^(b + 1)` for `1 ≤ b ≤ c`. -/
theorem e_dec_le (b c : Nat) (hb : 1 ≤ b) (hbc : b ≤ c) :
    (c + 1) ^ (c + 1) * b ^ (b + 1) ≤ c ^ (c + 1) * (b + 1) ^ (b + 1) := by
  induction hbc with
  | refl => exact Nat.le_of_eq (Nat.mul_comm _ _)
  | @step m hm ih =>
    have hm' : b ≤ m := hm
    have hstep := Nat.le_of_lt (e_mono_dec m (by omega))
    have h1 : (m + 2) ^ (m + 2) * m ^ (m + 1) * b ^ (b + 1)
        ≤ (m + 1) ^ (2 * m + 3) * b ^ (b + 1) := Nat.mul_le_mul_right _ hstep
    have h2 : (m + 1) ^ (m + 2) * ((m + 1) ^ (m + 1) * b ^ (b + 1))
        ≤ (m + 1) ^ (m + 2) * (m ^ (m + 1) * (b + 1) ^ (b + 1)) :=
      Nat.mul_le_mul_left _ ih
    have h3 : ((m + 2) ^ (m + 2) * b ^ (b + 1)) * m ^ (m + 1)
        ≤ ((m + 1) ^ (m + 2) * (b + 1) ^ (b + 1)) * m ^ (m + 1) := by
      have e1 : ((m + 2) ^ (m + 2) * b ^ (b + 1)) * m ^ (m + 1)
          = (m + 2) ^ (m + 2) * m ^ (m + 1) * b ^ (b + 1) := by ac_rfl
      have hm23 : m + 2 + (m + 1) = 2 * m + 3 := by omega
      have e2 : (m + 1) ^ (2 * m + 3) * b ^ (b + 1)
          = (m + 1) ^ (m + 2) * ((m + 1) ^ (m + 1) * b ^ (b + 1)) := by
        rw [← Nat.mul_assoc, ← Nat.pow_add, hm23]
      have e3 : (m + 1) ^ (m + 2) * (m ^ (m + 1) * (b + 1) ^ (b + 1))
          = ((m + 1) ^ (m + 2) * (b + 1) ^ (b + 1)) * m ^ (m + 1) := by ac_rfl
      rw [e1, ← e3]
      exact Nat.le_trans h1 (e2 ▸ h2)
    exact Nat.le_of_mul_le_mul_right h3 (pow_pos_of_pos (by omega) (m + 1))

/-- Pure-`Nat` Euler-number sandwich: `((a + 1) / a)^a < ((b + 1) / b)^(b + 1)` for all `a, b ≥ 1`. -/
theorem e_sandwich (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a + 1) ^ a * b ^ (b + 1) < a ^ a * (b + 1) ^ (b + 1) := by
  let m := max a b
  have ham : a ≤ m := Nat.le_max_left a b
  have hbm : b ≤ m := Nat.le_max_right a b
  have hm : 1 ≤ m := Nat.le_trans ha ham
  have hinc := e_inc_le a m ha ham
  have hdec := e_dec_le b m hb hbm
  have hmul_lt : ((a + 1) ^ a * b ^ (b + 1)) * (m ^ m * (m + 1) ^ (m + 1))
      < (a ^ a * (b + 1) ^ (b + 1)) * (m ^ m * (m + 1) ^ (m + 1)) := by
    have s1 : (a + 1) ^ a * m ^ m * (b ^ (b + 1) * (m + 1) ^ (m + 1))
        ≤ a ^ a * (m + 1) ^ m * (b ^ (b + 1) * (m + 1) ^ (m + 1)) :=
      Nat.mul_le_mul_right _ hinc
    have s2 : a ^ a * (m + 1) ^ m * ((m + 1) ^ (m + 1) * b ^ (b + 1))
        ≤ a ^ a * (m + 1) ^ m * (m ^ (m + 1) * (b + 1) ^ (b + 1)) :=
      Nat.mul_le_mul_left _ hdec
    have s3 : a ^ a * (m + 1) ^ m * (m ^ (m + 1) * (b + 1) ^ (b + 1))
        < a ^ a * (m + 1) ^ (m + 1) * (m ^ m * (b + 1) ^ (b + 1)) := by
      have hp1 : m ^ (m + 1) = m * m ^ m := by rw [Nat.pow_succ m m, Nat.mul_comm]
      have hp2 : (m + 1) ^ (m + 1) = (m + 1) * (m + 1) ^ m := by rw [Nat.pow_succ (m + 1) m, Nat.mul_comm]
      rw [hp1, hp2]
      have e1 : a ^ a * (m + 1) ^ m * (m * m ^ m * (b + 1) ^ (b + 1))
          = m * (a ^ a * (m + 1) ^ m * m ^ m * (b + 1) ^ (b + 1)) := by ac_rfl
      have e2 : a ^ a * ((m + 1) * (m + 1) ^ m) * (m ^ m * (b + 1) ^ (b + 1))
          = (m + 1) * (a ^ a * (m + 1) ^ m * m ^ m * (b + 1) ^ (b + 1)) := by ac_rfl
      rw [e1, e2]
      apply Nat.mul_lt_mul_of_pos_right (by omega)
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (pow_pos_of_pos ha a)
        (pow_pos_of_pos (by omega) m)) (pow_pos_of_pos hm m)) (pow_pos_of_pos (by omega) (b + 1))
    have eL : ((a + 1) ^ a * b ^ (b + 1)) * (m ^ m * (m + 1) ^ (m + 1))
        = (a + 1) ^ a * m ^ m * (b ^ (b + 1) * (m + 1) ^ (m + 1)) := by ac_rfl
    have eM : a ^ a * (m + 1) ^ m * (b ^ (b + 1) * (m + 1) ^ (m + 1))
        = a ^ a * (m + 1) ^ m * ((m + 1) ^ (m + 1) * b ^ (b + 1)) := by ac_rfl
    have eR : a ^ a * (m + 1) ^ (m + 1) * (m ^ m * (b + 1) ^ (b + 1))
        = (a ^ a * (b + 1) ^ (b + 1)) * (m ^ m * (m + 1) ^ (m + 1)) := by ac_rfl
    rw [eL, ← eR]
    exact Nat.lt_of_le_of_lt (Nat.le_trans s1 (eM ▸ s2)) s3
  exact Nat.lt_of_mul_lt_mul_right hmul_lt

/-- Cross-exponent ratio comparison: if `A * (b + 1) ≤ B * a`, then `((a + 1)/a)^A ≤ ((b + 1)/b)^B`. -/
theorem pow_ratio_le_of_cross {a b A B : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hcross : A * (b + 1) ≤ B * a) :
    (a + 1) ^ A * b ^ B ≤ a ^ A * (b + 1) ^ B := by
  have hs := Nat.le_of_lt (e_sandwich a b ha hb)
  have h1 : ((a + 1) ^ a * b ^ (b + 1)) ^ A ≤ (a ^ a * (b + 1) ^ (b + 1)) ^ A :=
    Nat.pow_le_pow_left hs A
  have hgap : b ^ (B * a - A * (b + 1)) ≤ (b + 1) ^ (B * a - A * (b + 1)) :=
    Nat.pow_le_pow_left (by omega) _
  have h2 := Nat.mul_le_mul h1 hgap
  have hsub : (b + 1) * A + (B * a - A * (b + 1)) = B * a := by
    have : (b + 1) * A = A * (b + 1) := Nat.mul_comm _ _
    omega
  have hL : ((a + 1) ^ a * b ^ (b + 1)) ^ A * b ^ (B * a - A * (b + 1))
      = ((a + 1) ^ A * b ^ B) ^ a := by
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_assoc, ← Nat.pow_add, hsub]
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm a A, Nat.mul_comm B a]
  have hR : (a ^ a * (b + 1) ^ (b + 1)) ^ A * (b + 1) ^ (B * a - A * (b + 1))
      = (a ^ A * (b + 1) ^ B) ^ a := by
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_assoc, ← Nat.pow_add, hsub]
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm a A, Nat.mul_comm B a]
  rw [hL, hR] at h2
  exact le_of_pow_le_pow_left ha h2

/-- Universal upper bound on `((c + 2) / (c - 1))^(c - 1) < 22` for all `c ≥ 2` (since `< e^3 ≈ 20.09`). -/
theorem add_two_div_sub_one_pow_lt_22 (c : Nat) (hc : 2 ≤ c) :
    (c + 2) ^ (c - 1) < 22 * (c - 1) ^ (c - 1) := by
  have hc2 : c - 1 + 2 = c + 1 := by omega
  have hc1 : c - 1 + 1 = c := by omega
  have h1 : (c + 2) ^ (c - 1) * 20 ^ 21 ≤ (c + 1) ^ (c - 1) * 21 ^ 21 := by
    have hs := Nat.le_of_lt (e_sandwich (c + 1) 20 (by omega) (by decide))
    have hle : (c + 2) ^ (c - 1) * (c + 1) ^ 2 ≤ (c + 2) ^ (c + 1) := by
      have hp : (c + 2) ^ (c + 1) = (c + 2) ^ (c - 1) * (c + 2) ^ 2 := by
        rw [← Nat.pow_add, hc2]
      rw [hp]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    have hmul : (c + 2) ^ (c - 1) * 20 ^ 21 * (c + 1) ^ 2 ≤ (c + 1) ^ (c - 1) * 21 ^ 21 * (c + 1) ^ 2 := by
      have eL : (c + 2) ^ (c - 1) * 20 ^ 21 * (c + 1) ^ 2 = ((c + 2) ^ (c - 1) * (c + 1) ^ 2) * 20 ^ 21 := by ac_rfl
      have eR : (c + 1) ^ (c - 1) * 21 ^ 21 * (c + 1) ^ 2 = (c + 1) ^ (c + 1) * 21 ^ 21 := by
        have hp : (c + 1) ^ (c - 1) * (c + 1) ^ 2 = (c + 1) ^ (c + 1) := by
          rw [← Nat.pow_add, hc2]
        calc (c + 1) ^ (c - 1) * 21 ^ 21 * (c + 1) ^ 2
            = (c + 1) ^ (c - 1) * (c + 1) ^ 2 * 21 ^ 21 := by ac_rfl
          _ = (c + 1) ^ (c + 1) * 21 ^ 21 := by rw [hp]
      rw [eL, eR]
      exact Nat.le_trans (Nat.mul_le_mul_right _ hle) hs
    exact Nat.le_of_mul_le_mul_right hmul (pow_pos_of_pos (by omega) 2)
  have h2 : (c + 1) ^ (c - 1) * 20 ^ 21 ≤ c ^ (c - 1) * 21 ^ 21 := by
    have hs := Nat.le_of_lt (e_sandwich c 20 (by omega) (by decide))
    have hle : (c + 1) ^ (c - 1) * c ≤ (c + 1) ^ c := by
      have hp : (c + 1) ^ c = (c + 1) ^ (c - 1) * (c + 1) := by
        calc (c + 1) ^ c = (c + 1) ^ (c - 1 + 1) := by rw [hc1]
          _ = (c + 1) ^ (c - 1) * (c + 1) := Nat.pow_succ _ _
      rw [hp]
      exact Nat.mul_le_mul_left _ (by omega)
    have hmul : (c + 1) ^ (c - 1) * 20 ^ 21 * c ≤ c ^ (c - 1) * 21 ^ 21 * c := by
      have eL : (c + 1) ^ (c - 1) * 20 ^ 21 * c = ((c + 1) ^ (c - 1) * c) * 20 ^ 21 := by ac_rfl
      have eR : c ^ (c - 1) * 21 ^ 21 * c = c ^ c * 21 ^ 21 := by
        have hp : c ^ (c - 1) * c = c ^ c := by
          calc c ^ (c - 1) * c = c ^ (c - 1 + 1) := (Nat.pow_succ c _).symm
            _ = c ^ c := by rw [hc1]
        calc c ^ (c - 1) * 21 ^ 21 * c = c ^ (c - 1) * c * 21 ^ 21 := by ac_rfl
          _ = c ^ c * 21 ^ 21 := by rw [hp]
      rw [eL, eR]
      exact Nat.le_trans (Nat.mul_le_mul_right _ hle) hs
    exact Nat.le_of_mul_le_mul_right hmul (by omega)
  have h3 : c ^ (c - 1) * 20 ^ 21 ≤ (c - 1) ^ (c - 1) * 21 ^ 21 := by
    have hs := Nat.le_of_lt (e_sandwich (c - 1) 20 (by omega) (by decide))
    rw [hc1] at hs
    exact hs
  have hprod : ((c + 2) ^ (c - 1) * 20 ^ 63) * ((c + 1) ^ (c - 1) * c ^ (c - 1))
      ≤ ((c - 1) ^ (c - 1) * 21 ^ 63) * ((c + 1) ^ (c - 1) * c ^ (c - 1)) := by
    have hm := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    have eL : (c + 2) ^ (c - 1) * 20 ^ 21 * ((c + 1) ^ (c - 1) * 20 ^ 21) * (c ^ (c - 1) * 20 ^ 21)
        = ((c + 2) ^ (c - 1) * 20 ^ 63) * ((c + 1) ^ (c - 1) * c ^ (c - 1)) := by
      have : 20 ^ 21 * 20 ^ 21 * 20 ^ 21 = 20 ^ 63 := by rw [← Nat.pow_add, ← Nat.pow_add]
      rw [← this]; ac_rfl
    have eR : (c + 1) ^ (c - 1) * 21 ^ 21 * (c ^ (c - 1) * 21 ^ 21) * ((c - 1) ^ (c - 1) * 21 ^ 21)
        = ((c - 1) ^ (c - 1) * 21 ^ 63) * ((c + 1) ^ (c - 1) * c ^ (c - 1)) := by
      have : 21 ^ 21 * 21 ^ 21 * 21 ^ 21 = 21 ^ 63 := by rw [← Nat.pow_add, ← Nat.pow_add]
      rw [← this]; ac_rfl
    rw [← eL, ← eR]
    exact hm
  have hcancel : (c + 2) ^ (c - 1) * 20 ^ 63 ≤ (c - 1) ^ (c - 1) * 21 ^ 63 :=
    Nat.le_of_mul_le_mul_right hprod
      (Nat.mul_pos (pow_pos_of_pos (by omega) _) (pow_pos_of_pos (by omega) _))
  have h21 : 21 ^ 63 < 22 * 20 ^ 63 := by
    have hbase : 10 * 21 ^ 21 ≤ 28 * 20 ^ 21 := by decide
    have hcb := Nat.pow_le_pow_left hbase 3
    rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hcb
    have h28 : 28 ^ 3 < 22 * 10 ^ 3 := by decide
    have hlt1 : 10 ^ 3 * 21 ^ 63 < 10 ^ 3 * (22 * 20 ^ 63) := by
      have h2 := Nat.mul_lt_mul_of_pos_right h28 (pow_pos_of_pos (a := 20) (by decide) 63)
      have eR : 22 * 10 ^ 3 * 20 ^ 63 = 10 ^ 3 * (22 * 20 ^ 63) := by ac_rfl
      rw [eR] at h2
      exact Nat.lt_of_le_of_lt hcb h2
    exact Nat.lt_of_mul_lt_mul_left (a := 10 ^ 3) hlt1
  have hlt : (c + 2) ^ (c - 1) * 20 ^ 63 < (22 * (c - 1) ^ (c - 1)) * 20 ^ 63 := by
    have hstep : (c - 1) ^ (c - 1) * 21 ^ 63 < (c - 1) ^ (c - 1) * (22 * 20 ^ 63) :=
      Nat.mul_lt_mul_of_pos_left h21 (pow_pos_of_pos (by omega) _)
    have heq : (c - 1) ^ (c - 1) * (22 * 20 ^ 63) = (22 * (c - 1) ^ (c - 1)) * 20 ^ 63 := by ac_rfl
    rw [heq] at hstep
    exact Nat.lt_of_le_of_lt hcancel hstep
  exact Nat.lt_of_mul_lt_mul_right (a := 20 ^ 63) hlt

/-- Universal lower bound `16 * (c - 1)^c ≤ (c + 2)^c` for all `c ≥ 4` (since `(1 + 3/(c-1))^c ≥ 16`). -/
theorem sixteen_mul_sub_one_pow_le (c : Nat) (hc : 4 ≤ c) :
    16 * (c - 1) ^ c ≤ (c + 2) ^ c := by
  by_cases h11 : c < 11
  · have hcases : c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
  · have hc11 : 11 ≤ c := by omega
    have h1 : 13 ^ 11 * (c + 1) ^ c ≤ 12 ^ 11 * (c + 2) ^ c := by
      have hinc := e_inc_le 12 (c + 1) (by decide) (by omega)
      have hstep : 13 ^ 12 * (c + 1) ^ c * (c + 1) ≤ 12 ^ 12 * (c + 2) ^ c * (c + 2) := by
        have eL : 13 ^ 12 * (c + 1) ^ c * (c + 1) = 13 ^ 12 * (c + 1) ^ (c + 1) := by
          rw [Nat.pow_succ (c + 1) c, Nat.mul_assoc]
        have eR : 12 ^ 12 * (c + 2) ^ c * (c + 2) = 12 ^ 12 * (c + 2) ^ (c + 1) := by
          rw [Nat.pow_succ (c + 2) c, Nat.mul_assoc]
        rw [eL, eR]; exact hinc
      have hcross : 12 * (c + 2) ≤ 13 * (c + 1) := by omega
      have hmul : (13 ^ 11 * (c + 1) ^ c) * (13 * (c + 1)) ≤ (12 ^ 11 * (c + 2) ^ c) * (13 * (c + 1)) := by
        have eL : (13 ^ 11 * (c + 1) ^ c) * (13 * (c + 1)) = 13 ^ 12 * (c + 1) ^ c * (c + 1) := by
          rw [Nat.pow_succ 13 11]; ac_rfl
        have eR1 : 12 ^ 12 * (c + 2) ^ c * (c + 2) = (12 ^ 11 * (c + 2) ^ c) * (12 * (c + 2)) := by
          rw [Nat.pow_succ 12 11]; ac_rfl
        have hle := Nat.mul_le_mul_left (12 ^ 11 * (c + 2) ^ c) hcross
        rw [eL]
        exact Nat.le_trans hstep (eR1 ▸ hle)
      exact Nat.le_of_mul_le_mul_right hmul (by omega)
    have h2 : 12 ^ 11 * c ^ c ≤ 11 ^ 11 * (c + 1) ^ c :=
      e_inc_le 11 c (by decide) hc11
    have h3 : 11 ^ 10 * (c - 1) ^ c ≤ 10 ^ 10 * c ^ c := by
      have hinc := e_inc_le 10 (c - 1) (by decide) (by omega)
      have hc1 : (c - 1) + 1 = c := by omega
      rw [hc1] at hinc
      have hmul := Nat.mul_le_mul hinc (show c - 1 ≤ c by omega)
      have eL : 11 ^ 10 * (c - 1) ^ (c - 1) * (c - 1) = 11 ^ 10 * (c - 1) ^ c := by
        have hp : (c - 1) ^ (c - 1) * (c - 1) = (c - 1) ^ c := by
          calc (c - 1) ^ (c - 1) * (c - 1) = (c - 1) ^ ((c - 1) + 1) := (Nat.pow_succ _ _).symm
            _ = (c - 1) ^ c := by rw [hc1]
        rw [Nat.mul_assoc, hp]
      have eR : 10 ^ 10 * c ^ (c - 1) * c = 10 ^ 10 * c ^ c := by
        have hp : c ^ (c - 1) * c = c ^ c := by
          calc c ^ (c - 1) * c = c ^ ((c - 1) + 1) := (Nat.pow_succ _ _).symm
            _ = c ^ c := by rw [hc1]
        rw [Nat.mul_assoc, hp]
      rw [eL, eR] at hmul
      exact hmul
    have hm := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    have hnum : 16 * (11 * 10 ^ 10) ≤ 13 ^ 11 := by decide
    have hcancel_base : (13 ^ 11 * (c - 1) ^ c) * (12 ^ 11 * 11 ^ 10 * (c + 1) ^ c * c ^ c)
        ≤ ((11 * 10 ^ 10) * (c + 2) ^ c) * (12 ^ 11 * 11 ^ 10 * (c + 1) ^ c * c ^ c) := by
      have eL : 13 ^ 11 * (c + 1) ^ c * (12 ^ 11 * c ^ c) * (11 ^ 10 * (c - 1) ^ c)
          = (13 ^ 11 * (c - 1) ^ c) * (12 ^ 11 * 11 ^ 10 * (c + 1) ^ c * c ^ c) := by ac_rfl
      have eR : 12 ^ 11 * (c + 2) ^ c * (11 ^ 11 * (c + 1) ^ c) * (10 ^ 10 * c ^ c)
          = ((11 * 10 ^ 10) * (c + 2) ^ c) * (12 ^ 11 * 11 ^ 10 * (c + 1) ^ c * c ^ c) := by
        have : 11 ^ 11 = 11 * 11 ^ 10 := by rw [Nat.pow_succ 11 10, Nat.mul_comm]
        rw [this]; ac_rfl
      rw [← eL, ← eR]; exact hm
    have hstep2 : 13 ^ 11 * (c - 1) ^ c ≤ (11 * 10 ^ 10) * (c + 2) ^ c :=
      Nat.le_of_mul_le_mul_right hcancel_base
        (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (by decide))
          (pow_pos_of_pos (by omega) c)) (pow_pos_of_pos (by omega) c))
    have hfinal : (16 * (c - 1) ^ c) * (11 * 10 ^ 10) ≤ (c + 2) ^ c * (11 * 10 ^ 10) := by
      have eL : (16 * (c - 1) ^ c) * (11 * 10 ^ 10) = (16 * (11 * 10 ^ 10)) * (c - 1) ^ c := by ac_rfl
      have eR : (c + 2) ^ c * (11 * 10 ^ 10) = (11 * 10 ^ 10) * (c + 2) ^ c := Nat.mul_comm _ _
      rw [eL, eR]
      exact Nat.le_trans (Nat.mul_le_mul_right _ hnum) hstep2
    exact Nat.le_of_mul_le_mul_right hfinal (by decide)

/-! ### Exact quadratic and cubic AM-GM inequalities in `Nat` -/

/-- Exact quadratic AM-GM in `Nat`: `4 * a * y ≤ (y + a)^2`. -/
theorem nat_quad_amgm (a y : Nat) : 4 * a * y ≤ (y + a) ^ 2 := by
  apply nat_le_of_int
  have hsq : 0 ≤ ((y : Int) - a) * (y - a) := int_mul_self_nonneg _
  have hid : ((y : Int) + a) ^ 2 = 4 * a * y + ((y : Int) - a) * (y - a) := by grind
  have hL : ((4 * a * y : Nat) : Int) = 4 * (a : Int) * (y : Int) := by
    simp only [Int.natCast_mul]; rfl
  have hR : (((y + a) ^ 2 : Nat) : Int) = ((y : Int) + a) ^ 2 := by
    simp only [Int.natCast_pow, Int.natCast_add]
  omega

/-- Exact cubic AM-GM in `Nat`: `27 * a * y^2 ≤ 4 * (y + a)^3`
    (from `4*(y + a)^3 = 27*a*y^2 + (y - 2*a)^2 * (4*y + a)`). -/
theorem nat_cubic_amgm (a y : Nat) : 27 * a * y ^ 2 ≤ 4 * (y + a) ^ 3 := by
  apply nat_le_of_int
  have hsq : 0 ≤ ((y : Int) - 2 * a) * (y - 2 * a) * (4 * y + a) :=
    Int.mul_nonneg (int_mul_self_nonneg _) (by omega)
  have hid : 4 * ((y : Int) + a) ^ 3 =
      27 * a * (y : Int) ^ 2 + ((y : Int) - 2 * a) * (y - 2 * a) * (4 * y + a) := by grind
  have hL : ((27 * a * y ^ 2 : Nat) : Int) = 27 * (a : Int) * (y : Int) ^ 2 := by
    simp only [Int.natCast_mul, Int.natCast_pow]; rfl
  have hR : ((4 * (y + a) ^ 3 : Nat) : Int) = 4 * ((y : Int) + a) ^ 3 := by
    simp only [Int.natCast_mul, Int.natCast_pow, Int.natCast_add]; rfl
  omega

end MatMul94
