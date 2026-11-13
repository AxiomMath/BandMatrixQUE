module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.UnitInterval
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Kolmogorov–Chentsov continuity theorem on a compact interval

**Statement** (`exists_continuous_modification`).  Let `(Ω, μ)` be a measure space, `E` a
complete second-countable metric space with its Borel σ-algebra, `t > 0`, and
`X : ℝ → Ω → E` with every `X s` measurable.  Assume the Chentsov moment bound on `[0, t]`:
for some `p > 0`, `q > 1`, `M ≥ 0`,
`∫⁻ ω, edist (X a ω) (X b ω) ^ p ∂μ ≤ ofReal (M * |a - b| ^ q)` for all `a b ∈ [0, t]`.
Then there is `Y : ℝ → Ω → E` with
* every `Y s` measurable,
* **every** sample path `s ↦ Y s ω` continuous on all of `ℝ` (constant outside `[0, t]`,
  `Y s = Y (clamp t s)`, `modification_clamp`),
* `Y s =ᵐ[μ] X s` for **every** `s ∈ [0, t]` (in particular at all dyadic times, and hence the
  finite-dimensional laws of `Y` and `X` agree at all times in `[0, t]`).

**Dyadic form** (`exists_continuous_modification_of_dyadic`).  Only the bound for adjacent
dyadic pairs, `DyadicChentsovBound`, is needed to build `Y`; then `Y = X` a.s. at every dyadic
time, and at every `s` where `X (dyadicFloor t n s) → X s` in measure (stochastic continuity
along the dyadic floors of `s`).

**Proof.**  With `c = (q - 1)/2`, `r = 2^{-c/p} < 1`: by Markov's inequality, the level-`n`
dyadic bad event `max_k d(X_{k t 2^{-n}}, X_{(k+1) t 2^{-n}}) ≥ r^n` has measure at most
`M t^q 2^{-c n}`, which is summable; by Borel–Cantelli almost every `ω` is *good*: from some
level on every dyadic increment is `< r^n`.  For good `ω`, the values at the dyadic floors
`⌊s 2^n / t⌋ t 2^{-n}` form a Cauchy sequence with geometric increments, uniformly in `s`, and
`Y s ω` is its limit; the uniform modulus gives continuity.  For bad `ω`, `Y s ω = X 0 ω`.
Identification at a fixed `s` uses Borel–Cantelli once more on `d(X_{floor_n s}, X_s) ≥ r^n`.

No Hölder exponent is recorded (only continuity), and no claim is made for an uncountable
family simultaneously except through continuity of `Y`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace KolmogorovChentsov

/-!
### Dyadic grid on `[0, t]`
-/

/-- The dyadic node `t k 2^{-n}`. -/
def dyadicNode (t : ℝ) (n k : ℕ) : ℝ := t * k / 2 ^ n

/-- The clamp of `s` to `[0, t]`. -/
def clamp (t s : ℝ) : ℝ := max 0 (min s t)

/-- The index of the level-`n` dyadic floor of (the clamp of) `s`. -/
def dyadicIndex (t : ℝ) (n : ℕ) (s : ℝ) : ℕ := ⌊clamp t s * 2 ^ n / t⌋₊

/-- The level-`n` dyadic floor of (the clamp of) `s`. -/
def dyadicFloor (t : ℝ) (n : ℕ) (s : ℝ) : ℝ := dyadicNode t n (dyadicIndex t n s)

variable {t : ℝ}

theorem clamp_mem (ht : 0 ≤ t) (s : ℝ) : clamp t s ∈ Icc 0 t :=
  ⟨le_max_left _ _, max_le ht (min_le_right _ _)⟩

theorem clamp_of_mem {s : ℝ} (hs : s ∈ Icc 0 t) : clamp t s = s := by
  simp [clamp, hs.1, hs.2]

theorem abs_clamp_sub_clamp_le (s s' : ℝ) : |clamp t s - clamp t s'| ≤ |s - s'| := by
  unfold clamp
  have h1 : |min s t - min s' t| ≤ |s - s'| := abs_min_sub_min_le_max s t s' t |>.trans
    (by simp)
  exact (abs_max_sub_max_le_max 0 (min s t) 0 (min s' t)).trans (by simpa using h1)

theorem dyadicNode_mem (ht : 0 ≤ t) {n k : ℕ} (hk : k ≤ 2 ^ n) : dyadicNode t n k ∈ Icc 0 t := by
  unfold dyadicNode
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ h2]
  have : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast hk
  nlinarith

theorem dyadicNode_succ_two_mul (n k : ℕ) :
    dyadicNode t (n + 1) (2 * k) = dyadicNode t n k := by
  unfold dyadicNode
  push_cast
  rw [pow_succ]
  field_simp

theorem dyadicNode_sub (n k : ℕ) :
    dyadicNode t n (k + 1) - dyadicNode t n k = t / 2 ^ n := by
  unfold dyadicNode
  push_cast
  ring

theorem dyadicIndex_le (ht : 0 < t) (n : ℕ) (s : ℝ) : dyadicIndex t n s ≤ 2 ^ n := by
  unfold dyadicIndex
  refine Nat.floor_le_of_le ?_
  have hc := clamp_mem ht.le s
  rw [div_le_iff₀ ht]
  push_cast
  nlinarith [hc.2, show (0 : ℝ) < 2 ^ n by positivity]

theorem dyadicFloor_mem (ht : 0 < t) (n : ℕ) (s : ℝ) : dyadicFloor t n s ∈ Icc 0 t :=
  dyadicNode_mem ht.le (dyadicIndex_le ht n s)

theorem dyadicIndex_succ (ht : 0 < t) (n : ℕ) (s : ℝ) :
    dyadicIndex t (n + 1) s = 2 * dyadicIndex t n s ∨
      dyadicIndex t (n + 1) s = 2 * dyadicIndex t n s + 1 := by
  unfold dyadicIndex
  set x : ℝ := clamp t s * 2 ^ n / t with hx
  have hx0 : 0 ≤ x := by
    have := (clamp_mem ht.le s).1
    positivity
  have h2x : clamp t s * 2 ^ (n + 1) / t = 2 * x := by
    rw [hx, pow_succ]
    ring
  rw [h2x]
  have hk1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hk2 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  have hlo : 2 * ⌊x⌋₊ ≤ ⌊2 * x⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith
  have hhi : ⌊2 * x⌋₊ < 2 * ⌊x⌋₊ + 2 := by
    rw [Nat.floor_lt (by positivity)]
    push_cast
    linarith
  omega

theorem dyadicIndex_le_add_one (ht : 0 < t) (n : ℕ) {s s' : ℝ} (hss : |s - s'| ≤ t / 2 ^ n) :
    dyadicIndex t n s ≤ dyadicIndex t n s' + 1 := by
  unfold dyadicIndex
  set x : ℝ := clamp t s * 2 ^ n / t
  set x' : ℝ := clamp t s' * 2 ^ n / t
  have hx'0 : 0 ≤ x' := by
    have := (clamp_mem ht.le s').1
    positivity
  have hxx : x ≤ x' + 1 := by
    have hc := (abs_clamp_sub_clamp_le (t := t) s s').trans hss
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have : clamp t s - clamp t s' ≤ t / 2 ^ n := (le_abs_self _).trans hc
    simp only [x, x']
    rw [div_add_one ht.ne', div_le_div_iff_of_pos_right ht]
    rw [le_div_iff₀ h2] at this
    nlinarith
  have hx0 : 0 ≤ x := by
    have := (clamp_mem ht.le s).1
    positivity
  have hk1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hk2 : x' < ⌊x'⌋₊ + 1 := Nat.lt_floor_add_one x'
  have : (⌊x⌋₊ : ℝ) < ⌊x'⌋₊ + 2 := by linarith
  have : ⌊x⌋₊ < ⌊x'⌋₊ + 2 := by exact_mod_cast this
  omega

theorem abs_dyadicFloor_sub_le (ht : 0 < t) (n : ℕ) {s : ℝ} (hs : s ∈ Icc 0 t) :
    |dyadicFloor t n s - s| ≤ t / 2 ^ n := by
  unfold dyadicFloor dyadicNode dyadicIndex
  rw [clamp_of_mem hs]
  set x : ℝ := s * 2 ^ n / t
  have hx0 : 0 ≤ x := by have := hs.1; positivity
  have hk1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hk2 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hsx : s = t * x / 2 ^ n := by
    simp only [x]
    field_simp
  rw [abs_le]
  constructor
  · rw [hsx, ← sub_div, ← neg_div, div_le_div_iff_of_pos_right h2]
    nlinarith
  · rw [hsx, ← sub_div]
    have : t * ↑⌊x⌋₊ - t * x ≤ 0 := by nlinarith
    exact (div_nonpos_of_nonpos_of_nonneg this h2.le).trans (by positivity)

theorem dyadicFloor_dyadicNode (ht : 0 < t) {L j : ℕ} (hj : j ≤ 2 ^ L) {n : ℕ} (hn : L ≤ n) :
    dyadicFloor t n (dyadicNode t L j) = dyadicNode t L j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h2 : (0 : ℝ) < 2 ^ L := by positivity
  have h2' : (0 : ℝ) < 2 ^ d := by positivity
  have hidx : dyadicIndex t (L + d) (dyadicNode t L j) = j * 2 ^ d := by
    unfold dyadicIndex
    rw [clamp_of_mem (dyadicNode_mem ht.le hj)]
    have : dyadicNode t L j * 2 ^ (L + d) / t = ((j * 2 ^ d : ℕ) : ℝ) := by
      unfold dyadicNode
      push_cast
      rw [pow_add]
      field_simp
    rw [this, Nat.floor_natCast]
  unfold dyadicFloor
  rw [hidx]
  unfold dyadicNode
  push_cast
  rw [pow_add]
  field_simp

/-!
### Deterministic chaining on dyadics
-/

variable {E : Type*} [MetricSpace E]

/-- A path is *good from level `N`* (with rate `r`) if from level `N` on every level-`n` dyadic
increment on `[0, t]` is `< r ^ n`. -/
def GoodFrom (t r : ℝ) (N : ℕ) (f : ℝ → E) : Prop :=
  ∀ n, N ≤ n → ∀ k, k < 2 ^ n → dist (f (dyadicNode t n k)) (f (dyadicNode t n (k + 1))) < r ^ n

variable {r : ℝ} {N : ℕ} {f : ℝ → E}

theorem dist_dyadicNode_le_of_adjacent (hr : 0 ≤ r) (hf : GoodFrom t r N f) {n : ℕ}
    (hn : N ≤ n) {a b : ℕ} (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hab : a ≤ b + 1)
    (hba : b ≤ a + 1) :
    dist (f (dyadicNode t n a)) (f (dyadicNode t n b)) ≤ r ^ n := by
  rcases (show a = b ∨ a = b + 1 ∨ b = a + 1 by omega) with h | h | h
  · subst h
    simp only [dist_self]
    positivity
  · subst h
    rw [dist_comm]
    exact (hf n hn b (by omega)).le
  · subst h
    exact (hf n hn a (by omega)).le

theorem dist_dyadicFloor_succ_le (ht : 0 < t) (hr : 0 ≤ r) (hf : GoodFrom t r N f) {n : ℕ}
    (hn : N ≤ n) (s : ℝ) :
    dist (f (dyadicFloor t n s)) (f (dyadicFloor t (n + 1) s)) ≤ r ^ (n + 1) := by
  unfold dyadicFloor
  rw [← dyadicNode_succ_two_mul]
  have hk := dyadicIndex_le ht n s
  have hk' := dyadicIndex_le ht (n + 1) s
  rcases dyadicIndex_succ ht n s with h | h <;>
  refine dist_dyadicNode_le_of_adjacent hr hf (hn.trans n.le_succ) (by rw [pow_succ]; omega)
    hk' (by omega) (by omega)

/-- The limit along dyadic floors. -/
def dyadicLimit (t : ℝ) (f : ℝ → E) (s : ℝ) : E :=
  letI : Nonempty E := ⟨f 0⟩
  limUnder atTop fun n => f (dyadicFloor t n s)

section Complete

variable [CompleteSpace E]

theorem tendsto_dyadicLimit (ht : 0 < t) (hr0 : 0 ≤ r) (hr1 : r < 1) (hf : GoodFrom t r N f)
    (s : ℝ) :
    Tendsto (fun n => f (dyadicFloor t n s)) atTop (𝓝 (dyadicLimit t f s)) := by
  have hc : CauchySeq fun m => f (dyadicFloor t (m + N) s) := by
    refine cauchySeq_of_le_geometric r (r ^ (N + 1)) hr1 fun m => ?_
    have := dist_dyadicFloor_succ_le ht hr0 hf (Nat.le_add_left N m) s
    rw [show m + 1 + N = m + N + 1 by omega]
    calc _ ≤ r ^ (m + N + 1) := this
      _ = r ^ (N + 1) * r ^ m := by ring
  have hc' : CauchySeq fun n => f (dyadicFloor t n s) := (cauchySeq_shift N).1 hc
  let _ : Nonempty E := ⟨f 0⟩
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete hc')

theorem dist_dyadicFloor_dyadicLimit_le (ht : 0 < t) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : GoodFrom t r N f) {n : ℕ} (hn : N ≤ n) (s : ℝ) :
    dist (f (dyadicFloor t n s)) (dyadicLimit t f s) ≤ r ^ (n + 1) / (1 - r) := by
  have hu : ∀ m, dist (f (dyadicFloor t (n + m) s)) (f (dyadicFloor t (n + m + 1) s)) ≤
      r ^ (n + 1) * r ^ m := by
    intro m
    have := dist_dyadicFloor_succ_le ht hr0 hf (hn.trans (Nat.le_add_right n m)) s
    calc _ ≤ r ^ (n + m + 1) := this
      _ = r ^ (n + 1) * r ^ m := by ring
  have htend : Tendsto (fun m => f (dyadicFloor t (n + m) s)) atTop
      (𝓝 (dyadicLimit t f s)) := by
    have := tendsto_dyadicLimit ht hr0 hr1 hf s
    rw [← tendsto_add_atTop_iff_nat n] at this
    simpa [add_comm] using this
  have := dist_le_of_le_geometric_of_tendsto₀ r (r ^ (n + 1)) hr1 hu htend
  simpa using this

theorem dist_dyadicLimit_le (ht : 0 < t) (hr0 : 0 ≤ r) (hr1 : r < 1) (hf : GoodFrom t r N f)
    {n : ℕ} (hn : N ≤ n) {s s' : ℝ} (hss : |s - s'| ≤ t / 2 ^ n) :
    dist (dyadicLimit t f s) (dyadicLimit t f s') ≤
      2 * (r ^ (n + 1) / (1 - r)) + r ^ n := by
  have h1 := dist_dyadicFloor_dyadicLimit_le ht hr0 hr1 hf hn s
  have h2 := dist_dyadicFloor_dyadicLimit_le ht hr0 hr1 hf hn s'
  have h3 : dist (f (dyadicFloor t n s)) (f (dyadicFloor t n s')) ≤ r ^ n :=
    dist_dyadicNode_le_of_adjacent hr0 hf hn (dyadicIndex_le ht n s) (dyadicIndex_le ht n s')
      (dyadicIndex_le_add_one ht n hss)
      (dyadicIndex_le_add_one ht n (by rwa [abs_sub_comm]))
  calc dist (dyadicLimit t f s) (dyadicLimit t f s')
      ≤ dist (dyadicLimit t f s) (f (dyadicFloor t n s)) +
          dist (f (dyadicFloor t n s)) (f (dyadicFloor t n s')) +
          dist (f (dyadicFloor t n s')) (dyadicLimit t f s') := dist_triangle4 _ _ _ _
    _ ≤ r ^ (n + 1) / (1 - r) + r ^ n + r ^ (n + 1) / (1 - r) := by
        rw [dist_comm] at h1
        gcongr
    _ = 2 * (r ^ (n + 1) / (1 - r)) + r ^ n := by ring

/-- **Continuity of the dyadic limit of a good path** (on all of `ℝ`). -/
theorem continuous_dyadicLimit (ht : 0 < t) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : GoodFrom t r N f) : Continuous (dyadicLimit t f) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  have h1r : 0 < 1 - r := sub_pos.2 hr1
  have hlim : Tendsto (fun n : ℕ => 3 * (r ^ n / (1 - r))) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).div_const (1 - r)
    simpa using this.const_mul 3
  obtain ⟨n₀, hn₀⟩ := (tendsto_order.1 hlim).2 ε hε |>.exists_forall_of_atTop
  set n := max n₀ N
  refine ⟨t / 2 ^ n, by positivity, fun a hab => ?_⟩
  have hab' : |a - b| ≤ t / 2 ^ n := by
    rw [← Real.dist_eq]
    exact hab.le
  have hbound := dist_dyadicLimit_le ht hr0 hr1 hf (le_max_right n₀ N) hab'
  have hrn : r ^ (n + 1) ≤ r ^ n := pow_le_pow_of_le_one hr0 hr1.le n.le_succ
  have h3 : 2 * (r ^ (n + 1) / (1 - r)) + r ^ n ≤ 3 * (r ^ n / (1 - r)) := by
    have : r ^ n ≤ r ^ n / (1 - r) := by
      rw [le_div_iff₀ h1r]
      have : 0 ≤ r ^ n := by positivity
      nlinarith
    have : r ^ (n + 1) / (1 - r) ≤ r ^ n / (1 - r) := div_le_div_of_nonneg_right hrn h1r.le
    linarith
  have h4 : 3 * (r ^ n / (1 - r)) < ε := by
    have := hn₀ n (le_max_left _ _)
    exact this
  exact hbound.trans_lt (h3.trans_lt h4)

end Complete

/-!
### Probabilistic estimates
-/

/-- The modulus rate `r = 2^{-(q-1)/(2p)}`. -/
def kcRate (p q : ℝ) : ℝ := (2 : ℝ) ^ (-((q - 1) / 2 / p))

/-- The geometric ratio `2^{-(q-1)/2}` of the bad-event bounds. -/
def kcRatio (q : ℝ) : ℝ := (2 : ℝ) ^ (-((q - 1) / 2))

theorem kcRate_pos (p q : ℝ) : 0 < kcRate p q := Real.rpow_pos_of_pos two_pos _

theorem kcRate_lt_one {p q : ℝ} (hp : 0 < p) (hq : 1 < q) : kcRate p q < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg one_lt_two
    (neg_neg_of_pos (div_pos (div_pos (sub_pos.2 hq) two_pos) hp))

theorem kcRatio_pos (q : ℝ) : 0 < kcRatio q := Real.rpow_pos_of_pos two_pos _

theorem kcRatio_lt_one {q : ℝ} (hq : 1 < q) : kcRatio q < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos (div_pos (sub_pos.2 hq) two_pos))

/-- The exact level computation `2^n ⋅ (t 2^{-n})^q / (r^n)^p = t^q ⋅ ρ^n`. -/
theorem level_identity {p q : ℝ} (hp : 0 < p) (ht : 0 < t) (n : ℕ) :
    (2 : ℝ) ^ n * ((t / 2 ^ n) ^ q / (kcRate p q ^ n) ^ p) = t ^ q * kcRatio q ^ n := by
  have h2 : (0 : ℝ) < 2 := two_pos
  unfold kcRate kcRatio
  rw [Real.div_rpow ht.le (by positivity)]
  simp only [← Real.rpow_natCast, ← Real.rpow_mul h2.le]
  rw [div_div, ← Real.rpow_add h2]
  rw [mul_div_assoc', mul_comm ((2 : ℝ) ^ (n : ℝ)), mul_div_assoc, ← Real.rpow_sub h2]
  congr 2
  field_simp
  ring

theorem pair_identity_le {p q : ℝ} (hp : 0 < p) (ht : 0 < t) (n : ℕ) :
    (t / 2 ^ n) ^ q / (kcRate p q ^ n) ^ p ≤ t ^ q * kcRatio q ^ n := by
  rw [← level_identity hp ht n]
  have h0 : 0 ≤ (t / 2 ^ n) ^ q / (kcRate p q ^ n) ^ p := by
    have := kcRate_pos p q
    positivity
  have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- The Chentsov moment bound on `[0, t]`. -/
def ChentsovBound (μ : Measure Ω) (X : ℝ → Ω → E) (t p q M : ℝ) : Prop :=
  ∀ a ∈ Icc 0 t, ∀ b ∈ Icc 0 t,
    ∫⁻ ω, edist (X a ω) (X b ω) ^ p ∂μ ≤ ENNReal.ofReal (M * |a - b| ^ q)

variable {X : ℝ → Ω → E} {p q M : ℝ}

/-- Markov's inequality for one pair of times at scale `t 2^{-n}`. -/
theorem measure_rate_le_dist_le_of_moment (hX : ∀ s, Measurable (X s)) (hp : 0 < p) {a b : ℝ}
    (n : ℕ) (hab : ∫⁻ ω, edist (X a ω) (X b ω) ^ p ∂μ ≤ ENNReal.ofReal (M * (t / 2 ^ n) ^ q)) :
    μ {ω | kcRate p q ^ n ≤ dist (X a ω) (X b ω)} ≤
      ENNReal.ofReal (M * ((t / 2 ^ n) ^ q / (kcRate p q ^ n) ^ p)) := by
  set ε : ℝ := kcRate p q ^ n
  have hε : 0 < ε := pow_pos (kcRate_pos p q) n
  have hsub : {ω | ε ≤ dist (X a ω) (X b ω)} ⊆
      {ω | ENNReal.ofReal ε ^ p ≤ edist (X a ω) (X b ω) ^ p} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    rw [edist_dist]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hω) hp.le
  have hmeas : AEMeasurable (fun ω => edist (X a ω) (X b ω) ^ p) μ :=
    (((hX a).edist (hX b)).pow_const p).aemeasurable
  have hne0 : ENNReal.ofReal ε ^ p ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hε) ENNReal.ofReal_ne_top).ne'
  have hnetop : ENNReal.ofReal ε ^ p ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp.le
    ENNReal.ofReal_ne_top
  calc μ {ω | ε ≤ dist (X a ω) (X b ω)}
      ≤ μ {ω | ENNReal.ofReal ε ^ p ≤ edist (X a ω) (X b ω) ^ p} := measure_mono hsub
    _ ≤ (∫⁻ ω, edist (X a ω) (X b ω) ^ p ∂μ) / ENNReal.ofReal ε ^ p :=
        meas_ge_le_lintegral_div hmeas hne0 hnetop
    _ ≤ ENNReal.ofReal (M * (t / 2 ^ n) ^ q) / ENNReal.ofReal ε ^ p := by
        gcongr
    _ = ENNReal.ofReal (M * ((t / 2 ^ n) ^ q / ε ^ p)) := by
        rw [ENNReal.ofReal_rpow_of_pos hε, ← ENNReal.ofReal_div_of_pos (by positivity),
          mul_div_assoc]

/-- The Chentsov bound restricted to adjacent dyadic pairs (all that the construction of the
continuous modification uses). -/
def DyadicChentsovBound (μ : Measure Ω) (X : ℝ → Ω → E) (t p q M : ℝ) : Prop :=
  ∀ n k : ℕ, k < 2 ^ n →
    ∫⁻ ω, edist (X (dyadicNode t n k) ω) (X (dyadicNode t n (k + 1)) ω) ^ p ∂μ ≤
      ENNReal.ofReal (M * (t / 2 ^ n) ^ q)

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
theorem ChentsovBound.le_scale (hM : 0 ≤ M) (hq : 1 < q) (hmom : ChentsovBound μ X t p q M)
    {a b : ℝ} (ha : a ∈ Icc 0 t) (hb : b ∈ Icc 0 t) {n : ℕ} (hab : |a - b| ≤ t / 2 ^ n) :
    ∫⁻ ω, edist (X a ω) (X b ω) ^ p ∂μ ≤ ENNReal.ofReal (M * (t / 2 ^ n) ^ q) :=
  (hmom a ha b hb).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (abs_nonneg _) hab (by linarith)) hM))

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
theorem ChentsovBound.dyadic (hM : 0 ≤ M) (hq : 1 < q) (ht : 0 < t)
    (hmom : ChentsovBound μ X t p q M) : DyadicChentsovBound μ X t p q M := by
  intro n k hk
  refine hmom.le_scale hM hq (dyadicNode_mem ht.le hk.le) (dyadicNode_mem ht.le (by omega)) ?_
  rw [abs_sub_comm, dyadicNode_sub, abs_of_pos (by positivity)]

/-- The level-`n` dyadic bad event. -/
def badLevel (X : ℝ → Ω → E) (t r : ℝ) (n : ℕ) : Set Ω :=
  ⋃ k ∈ Finset.range (2 ^ n),
    {ω | r ^ n ≤ dist (X (dyadicNode t n k) ω) (X (dyadicNode t n (k + 1)) ω)}

theorem measure_badLevel_le (hX : ∀ s, Measurable (X s)) (hp : 0 < p) (ht : 0 < t)
    (hmom : DyadicChentsovBound μ X t p q M) (n : ℕ) :
    μ (badLevel X t (kcRate p q) n) ≤ ENNReal.ofReal (M * t ^ q * kcRatio q ^ n) := by
  have hpair : ∀ k ∈ Finset.range (2 ^ n),
      μ {ω | kcRate p q ^ n ≤ dist (X (dyadicNode t n k) ω) (X (dyadicNode t n (k + 1)) ω)} ≤
        ENNReal.ofReal (M * ((t / 2 ^ n) ^ q / (kcRate p q ^ n) ^ p)) := by
    intro k hk
    exact measure_rate_le_dist_le_of_moment hX hp n (hmom n k (Finset.mem_range.1 hk))
  calc μ (badLevel X t (kcRate p q) n)
      ≤ ∑ k ∈ Finset.range (2 ^ n),
          μ {ω | kcRate p q ^ n ≤
            dist (X (dyadicNode t n k) ω) (X (dyadicNode t n (k + 1)) ω)} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.range (2 ^ n),
          ENNReal.ofReal (M * ((t / 2 ^ n) ^ q / (kcRate p q ^ n) ^ p)) :=
        Finset.sum_le_sum hpair
    _ = ENNReal.ofReal ((2 : ℝ) ^ n * (M * ((t / 2 ^ n) ^ q / (kcRate p q ^ n) ^ p))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          show ((2 ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ n) by simp,
          ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (M * t ^ q * kcRatio q ^ n) := by
        rw [mul_left_comm, level_identity hp ht n]
        ring_nf

theorem tsum_geometric_ofReal_ne_top {K ρ : ℝ} (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∑' n : ℕ, ENNReal.ofReal (K * ρ ^ n) ≠ ∞ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    ((summable_geometric_of_lt_one hρ0 hρ1).mul_left K)]
  exact ENNReal.ofReal_ne_top

/-- The good set: from some level on, all dyadic increments are below the rate. -/
def goodSet (X : ℝ → Ω → E) (t r : ℝ) : Set Ω := {ω | ∃ N, GoodFrom t r N fun s => X s ω}

theorem measurableSet_goodSet (hX : ∀ s, Measurable (X s)) (t r : ℝ) :
    MeasurableSet (goodSet X t r) := by
  have : goodSet X t r = ⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n), ⋂ k : ℕ, ⋂ (_ : k < 2 ^ n),
      {ω | dist (X (dyadicNode t n k) ω) (X (dyadicNode t n (k + 1)) ω) < r ^ n} := by
    ext ω
    simp [goodSet, GoodFrom]
  rw [this]
  refine MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n => MeasurableSet.iInter
    fun _ => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_lt ((hX _).dist (hX _)) measurable_const

theorem ae_mem_goodSet (hX : ∀ s, Measurable (X s)) (hM : 0 ≤ M) (hp : 0 < p) (hq : 1 < q)
    (ht : 0 < t) (hmom : DyadicChentsovBound μ X t p q M) :
    ∀ᵐ ω ∂μ, ω ∈ goodSet X t (kcRate p q) := by
  have hsum : ∑' n, μ (badLevel X t (kcRate p q) n) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum
      (measure_badLevel_le hX hp ht hmom))
    exact tsum_geometric_ofReal_ne_top (by positivity) (kcRatio_pos q).le (kcRatio_lt_one hq)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine ⟨N, fun n hn k hk => ?_⟩
  have := hN n hn
  simp only [badLevel, mem_iUnion, mem_ofPred_eq, Finset.mem_range, not_exists, not_le] at this
  exact this k hk

/-- Almost-sure convergence along the dyadic floors at a fixed time `s ∈ [0, t]`. -/
theorem ae_tendsto_dyadicFloor (hX : ∀ s, Measurable (X s)) (hM : 0 ≤ M) (hp : 0 < p)
    (hq : 1 < q) (ht : 0 < t) (hmom : ChentsovBound μ X t p q M) {s : ℝ} (hs : s ∈ Icc 0 t) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X (dyadicFloor t n s) ω) atTop (𝓝 (X s ω)) := by
  have hbound : ∀ n, μ {ω | kcRate p q ^ n ≤ dist (X (dyadicFloor t n s) ω) (X s ω)} ≤
      ENNReal.ofReal (M * t ^ q * kcRatio q ^ n) := by
    intro n
    refine (measure_rate_le_dist_le_of_moment hX hp n (hmom.le_scale hM hq
      (dyadicFloor_mem ht n s) hs (abs_dyadicFloor_sub_le ht n hs))).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (pair_identity_le hp ht n) hM
  have hsum : ∑' n, μ {ω | kcRate p q ^ n ≤ dist (X (dyadicFloor t n s) ω) (X s ω)} ≠ ∞ :=
    ne_top_of_le_ne_top (tsum_geometric_ofReal_ne_top (by positivity) (kcRatio_pos q).le
      (kcRatio_lt_one hq)) (ENNReal.tsum_le_tsum hbound)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => dist_nonneg) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one (kcRate_pos p q).le (kcRate_lt_one hp hq))
  filter_upwards [hω] with n hn
  simp only [not_le] at hn
  exact hn.le

/-!
### The continuous modification
-/

variable [CompleteSpace E]

open Classical in
/-- **The Kolmogorov–Chentsov modification**: the dyadic limit on the good set, the constant
path `X 0 ω` off it. -/
def modification (X : ℝ → Ω → E) (t p q : ℝ) (s : ℝ) (ω : Ω) : E :=
  if ω ∈ goodSet X t (kcRate p q) then dyadicLimit t (fun u => X u ω) s else X 0 ω

omit [MeasurableSpace Ω] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_modification (ht : 0 < t) (hp : 0 < p) (hq : 1 < q) (ω : Ω) :
    Continuous fun s => modification X t p q s ω := by
  by_cases hω : ω ∈ goodSet X t (kcRate p q)
  · simp only [modification, ite_eq_left hω]
    obtain ⟨N, hN⟩ := hω
    exact continuous_dyadicLimit ht (kcRate_pos p q).le (kcRate_lt_one hp hq) hN
  · simp only [modification, ite_eq_right hω]
    exact continuous_const

omit [MeasurableSpace Ω] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
open Classical in
theorem tendsto_modification (ht : 0 < t) (hp : 0 < p) (hq : 1 < q) (s : ℝ) (ω : Ω) :
    Tendsto (fun n => (goodSet X t (kcRate p q)).piecewise (X (dyadicFloor t n s)) (X 0) ω)
      atTop (𝓝 (modification X t p q s ω)) := by
  by_cases hω : ω ∈ goodSet X t (kcRate p q)
  · simp only [Set.piecewise_eq_of_mem _ _ _ hω, modification, ite_eq_left hω]
    obtain ⟨N, hN⟩ := hω
    exact tendsto_dyadicLimit ht (kcRate_pos p q).le (kcRate_lt_one hp hq) hN s
  · simp only [Set.piecewise_eq_of_notMem _ _ _ hω, modification, ite_eq_right hω]
    exact tendsto_const_nhds

open Classical in
theorem measurable_modification (hX : ∀ s, Measurable (X s)) (ht : 0 < t) (hp : 0 < p)
    (hq : 1 < q) (s : ℝ) : Measurable (modification X t p q s) := by
  classical
  exact measurable_of_tendsto_metrizable
    (fun n => (hX _).piecewise (measurableSet_goodSet hX t _) (hX 0))
    (tendsto_pi_nhds.2 fun ω => tendsto_modification ht hp hq s ω)

open Classical in
theorem modification_ae_eq (hX : ∀ s, Measurable (X s)) (hM : 0 ≤ M) (hp : 0 < p)
    (hq : 1 < q) (ht : 0 < t) (hmom : ChentsovBound μ X t p q M) {s : ℝ} (hs : s ∈ Icc 0 t) :
    modification X t p q s =ᵐ[μ] X s := by
  filter_upwards [ae_mem_goodSet hX hM hp hq ht (hmom.dyadic hM hq ht),
    ae_tendsto_dyadicFloor hX hM hp hq ht hmom hs]
    with ω hgood hlim
  have h1 := tendsto_modification (X := X) ht hp hq s ω
  simp only [Set.piecewise_eq_of_mem _ _ _ hgood] at h1
  exact tendsto_nhds_unique h1 hlim

open Classical in
/-- Under the dyadic Chentsov bound only, the modification agrees almost surely with `X` at every
dyadic node. -/
theorem modification_dyadicNode_ae_eq (hX : ∀ s, Measurable (X s)) (hM : 0 ≤ M) (hp : 0 < p)
    (hq : 1 < q) (ht : 0 < t) (hdy : DyadicChentsovBound μ X t p q M) {L j : ℕ}
    (hj : j ≤ 2 ^ L) :
    modification X t p q (dyadicNode t L j) =ᵐ[μ] X (dyadicNode t L j) := by
  filter_upwards [ae_mem_goodSet hX hM hp hq ht hdy] with ω hgood
  have h1 := tendsto_modification (X := X) ht hp hq (dyadicNode t L j) ω
  simp only [Set.piecewise_eq_of_mem _ _ _ hgood] at h1
  refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop L] with n hn
  rw [dyadicFloor_dyadicNode ht hj hn]

open Classical in
/-- Under the dyadic Chentsov bound, the modification agrees almost surely with `X` at every
time `s` at which `X` is stochastically continuous along the dyadic floors. -/
theorem modification_ae_eq_of_tendstoInMeasure (hX : ∀ s, Measurable (X s)) (hM : 0 ≤ M)
    (hp : 0 < p) (hq : 1 < q) (ht : 0 < t) (hdy : DyadicChentsovBound μ X t p q M) {s : ℝ}
    (hs : TendstoInMeasure μ (fun n => X (dyadicFloor t n s)) atTop (X s)) :
    modification X t p q s =ᵐ[μ] X s := by
  obtain ⟨ns, hns, hlim⟩ := hs.exists_seq_tendsto_ae
  filter_upwards [ae_mem_goodSet hX hM hp hq ht hdy, hlim] with ω hgood hω
  have h1 := tendsto_modification (X := X) ht hp hq s ω
  simp only [Set.piecewise_eq_of_mem _ _ _ hgood] at h1
  exact tendsto_nhds_unique (h1.comp hns.tendsto_atTop) hω

omit [CompleteSpace E] [MeasurableSpace Ω] [SecondCountableTopology E] [MeasurableSpace E]
  [BorelSpace E] in
/-- The modification is constant outside `[0, t]`: it only depends on the clamped time. -/
theorem modification_clamp (ht : 0 ≤ t) (p q s : ℝ) (ω : Ω) :
    modification X t p q (clamp t s) ω = modification X t p q s ω := by
  have : ∀ n, dyadicFloor t n (clamp t s) = dyadicFloor t n s := by
    intro n
    have hc : clamp t (clamp t s) = clamp t s := clamp_of_mem (clamp_mem ht s)
    simp only [dyadicFloor, dyadicIndex, hc]
  simp only [modification, dyadicLimit, this]

end KolmogorovChentsov

open KolmogorovChentsov

/-- **Kolmogorov–Chentsov theorem on `[0, t]`.**  A process satisfying the Chentsov moment
bound `∫⁻ edist (X a) (X b) ^ p ≤ ofReal (M |a - b|^q)` on `[0, t]` (`p > 0`, `q > 1`) has a
modification `Y` with every `Y s` measurable, **every** path continuous on `ℝ`, and
`Y s = X s` almost everywhere for every `s ∈ [0, t]`. -/
theorem exists_continuous_modification {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E]
    [BorelSpace E] {X : ℝ → Ω → E} {t p q M : ℝ} (hX : ∀ s, Measurable (X s)) (ht : 0 < t)
    (hp : 0 < p) (hq : 1 < q) (hM : 0 ≤ M) (hmom : ChentsovBound μ X t p q M) :
    ∃ Y : ℝ → Ω → E, (∀ s, Measurable (Y s)) ∧ (∀ ω, Continuous fun s => Y s ω) ∧
      ∀ s ∈ Icc 0 t, Y s =ᵐ[μ] X s :=
  ⟨modification X t p q, measurable_modification hX ht hp hq,
    continuous_modification ht hp hq, fun _ hs => modification_ae_eq hX hM hp hq ht hmom hs⟩

/-- **Kolmogorov–Chentsov theorem, dyadic form.**  If only the adjacent dyadic increments satisfy
`∫⁻ edist (X_{k t 2^{-n}}) (X_{(k+1) t 2^{-n}}) ^ p ≤ ofReal (M (t 2^{-n})^q)` (`p > 0`,
`q > 1`), there is a modification `Y` with measurable marginals and **every** path continuous,
agreeing a.s. with `X` at every dyadic time of `[0, t]`, and at every `s` at which `X` is
stochastically continuous along the dyadic floors of `s`. -/
theorem exists_continuous_modification_of_dyadic {Ω E : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] {X : ℝ → Ω → E} {t p q M : ℝ}
    (hX : ∀ s, Measurable (X s)) (ht : 0 < t) (hp : 0 < p) (hq : 1 < q) (hM : 0 ≤ M)
    (hdy : DyadicChentsovBound μ X t p q M) :
    ∃ Y : ℝ → Ω → E, (∀ s, Measurable (Y s)) ∧ (∀ ω, Continuous fun s => Y s ω) ∧
      (∀ L j : ℕ, j ≤ 2 ^ L → Y (dyadicNode t L j) =ᵐ[μ] X (dyadicNode t L j)) ∧
      ∀ s, TendstoInMeasure μ (fun n => X (dyadicFloor t n s)) atTop (X s) →
        Y s =ᵐ[μ] X s :=
  ⟨modification X t p q, measurable_modification hX ht hp hq,
    continuous_modification ht hp hq,
    fun _ _ hj => modification_dyadicNode_ae_eq hX hM hp hq ht hdy hj,
    fun _ hs => modification_ae_eq_of_tendstoInMeasure hX hM hp hq ht hdy hs⟩

end BlockBand.Diffusion
