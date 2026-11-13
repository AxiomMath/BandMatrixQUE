module

public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF.Defs
public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF.Simple

/-!
# Reference flow jointly measurable in the path: grid approximation of the coefficients

**Scheme.** On the grid `x_i = a + i (c − a)/(n + 1)`, `i = 0, …, n + 1`, record the dyadic floors
`⌊2ⁿ v⌋` of the coefficient values `v` of `(shortRate, refDamping)` at `x_i` (the integer code
`coeffCode`), and interpolate the values `⌊2ⁿ v⌋/2ⁿ` with the hat functions
`hat((x − a)/h − i)`, `h = (c − a)/(n + 1)` (`interp`). This is the piecewise-linear interpolation
on `[a, c]`. Outside `[a, c]` the hat sum decays to `0` instead of being clamped. This keeps continuity, symmetry and nonnegativity everywhere, and
`Admissible` only looks at `[a, u] ⊆ [a, c]`.

* `codeCoeff a c n z`: the coefficient pair decoded from a code `z : CoeffCode N n`, a countable
  type; `gridCoeff F a c b₀ ℓ n ω = codeCoeff a c n (coeffCode F a c b₀ ℓ n ω)` by definition.
* **`measurable_coeffCode`**: the code is `pathSigma F a a c`-measurable (for `a ≤ c`).
* **`admissible_gridCoeff`**: for every `u`, `Admissible a u` holds for the rate and damping parts
  of `gridCoeff` (floors keep symmetry and nonnegativity; hat sums are continuous).
* **`tendstoUniformlyOn_gridCoeff`**: for `a < c` and `ω ∈ simpleRatSet F a c`, `gridCoeff n ω`
  converges to `(shortRate, refDamping)` uniformly on `[a, c]`. The general statement is
  `tendstoUniformlyOn_interp` (uniform continuity on the compact interval, partition of unity
  `sum_gridWeight`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint

open MeasureTheory Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Palm.MomentFlow (pathSigma)
open BlockBand.Palm.RelativeLocalization.StochasticBridge

/-!
## Hat functions and the interpolation on the grid
-/

/-- The hat function `max(0, 1 − |y|)`. -/
def hat (y : ℝ) : ℝ := max 0 (1 - |y|)

/-- The hat function is nonnegative. -/
theorem hat_nonneg (y : ℝ) : 0 ≤ hat y := le_max_left _ _

/-- The hat function vanishes for `|y| ≥ 1`. -/
theorem hat_eq_zero {y : ℝ} (hy : 1 ≤ |y|) : hat y = 0 := by
  simp only [hat]
  exact max_eq_left (by linarith)

/-- Where the hat function does not vanish, `|y| < 1`. -/
theorem abs_lt_one_of_hat_ne_zero {y : ℝ} (hy : hat y ≠ 0) : |y| < 1 := by
  by_contra h
  exact hy (hat_eq_zero (not_lt.1 h))

/-- The hat function is continuous. -/
theorem continuous_hat : Continuous hat :=
  continuous_const.max (continuous_const.sub continuous_abs)

/-- Two neighbouring hats sum to `1` between their peaks. -/
theorem hat_add_hat {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : hat y + hat (y - 1) = 1 := by
  simp only [hat, abs_of_nonneg h0, abs_of_nonpos (by linarith : y - 1 ≤ 0)]
  rw [max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

/-- The grid step `(c − a)/(n + 1)`. -/
def gridStep (a c : ℝ) (n : ℕ) : ℝ := (c - a) / (n + 1)

/-- The grid step is positive for `a < c`. -/
theorem gridStep_pos {a c : ℝ} (hac : a < c) (n : ℕ) : 0 < gridStep a c n := by
  simp only [gridStep]
  exact div_pos (sub_pos.2 hac) (by positivity)

/-- `(n + 1)` grid steps make up `c − a`. -/
theorem succ_mul_gridStep (a c : ℝ) (n : ℕ) : ((n : ℝ) + 1) * gridStep a c n = c - a := by
  simp only [gridStep]
  field_simp

/-- The grid node `x_i = a + i (c − a)/(n + 1)`, `i = 0, …, n + 1`. -/
def gridNode (a c : ℝ) (n : ℕ) (i : Fin (n + 2)) : ℝ := a + (i.val : ℝ) * gridStep a c n

/-- The grid nodes lie in `[a, c]`. -/
theorem gridNode_mem {a c : ℝ} (hac : a ≤ c) (n : ℕ) (i : Fin (n + 2)) :
    gridNode a c n i ∈ Icc a c := by
  have hs : 0 ≤ gridStep a c n := by
    simp only [gridStep]
    exact div_nonneg (sub_nonneg.2 hac) (by positivity)
  have hi : (i.val : ℝ) ≤ n + 1 := by
    have := i.2
    exact_mod_cast (by omega : i.val ≤ n + 1)
  have e := succ_mul_gridStep a c n
  have h1 := mul_le_mul_of_nonneg_right hi hs
  have h2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) i.val) hs
  simp only [gridNode]
  constructor <;> linarith

/-- The hat weight `hat((x − a)/h − i)` of the node `x_i` at `x`. -/
def gridWeight (a c : ℝ) (n : ℕ) (i : Fin (n + 2)) (x : ℝ) : ℝ :=
  hat ((x - a) / gridStep a c n - i.val)

/-- The weights are nonnegative. -/
theorem gridWeight_nonneg (a c : ℝ) (n : ℕ) (i : Fin (n + 2)) (x : ℝ) :
    0 ≤ gridWeight a c n i x := by
  simp only [gridWeight]
  exact hat_nonneg _

/-- The weights are continuous. -/
theorem continuous_gridWeight (a c : ℝ) (n : ℕ) (i : Fin (n + 2)) :
    Continuous (gridWeight a c n i) := by
  have e : gridWeight a c n i = fun x : ℝ => hat ((x - a) / gridStep a c n - i.val) := by
    funext x
    simp only [gridWeight]
  rw [e]
  exact continuous_hat.comp
    (((continuous_id.sub continuous_const).div_const _).sub continuous_const)

/-- **Partition of unity.** For `a < c` and `x ∈ [a, c]` the weights sum to `1`. -/
theorem sum_gridWeight {a c : ℝ} (hac : a < c) (n : ℕ) {x : ℝ} (hx : x ∈ Icc a c) :
    ∑ i, gridWeight a c n i x = 1 := by
  simp only [gridWeight]
  have hs := gridStep_pos hac n
  set t := (x - a) / gridStep a c n with ht
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.2 hx.1) hs.le
  have ht1 : t ≤ n + 1 := by
    rw [ht, div_le_iff₀ hs, succ_mul_gridStep]
    linarith [hx.2]
  set j := min ⌊t⌋₊ n with hj
  have hjn : j ≤ n := min_le_right _ _
  have hjt : (j : ℝ) ≤ t := (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le ht0)
  have htj : t ≤ j + 1 := by
    rcases le_total ⌊t⌋₊ n with h | h
    · rw [hj, min_eq_left h]
      exact (Nat.lt_floor_add_one t).le
    · rw [hj, min_eq_right h]
      exact ht1
  have hne : (⟨j, by omega⟩ : Fin (n + 2)) ≠ ⟨j + 1, by omega⟩ := by
    intro h
    exact absurd (Fin.mk.inj_iff.1 h) (by omega)
  rw [Fintype.sum_eq_add _ _ hne ?_]
  · have e : t - ((j + 1 : ℕ) : ℝ) = t - j - 1 := by
      push_cast
      ring
    simp only [e]
    exact hat_add_hat (sub_nonneg.2 hjt) (by linarith)
  · intro i hi
    have h' : i.val + 1 ≤ j ∨ j + 2 ≤ i.val := by
      have h1 : i.val ≠ j := fun e => hi.1 (Fin.ext e)
      have h2 : i.val ≠ j + 1 := fun e => hi.2 (Fin.ext e)
      omega
    apply hat_eq_zero
    rcases h' with h' | h'
    · have : (i.val : ℝ) + 1 ≤ j := by exact_mod_cast h'
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have : (j : ℝ) + 2 ≤ i.val := by exact_mod_cast h'
      rw [abs_of_nonpos (by linarith)]
      linarith

/-- Where the weight of `x_i` does not vanish, `|x − x_i| < h`. -/
theorem abs_sub_gridNode_lt {a c : ℝ} (hac : a < c) {n : ℕ} {i : Fin (n + 2)} {x : ℝ}
    (h : gridWeight a c n i x ≠ 0) : |x - gridNode a c n i| < gridStep a c n := by
  have hs := gridStep_pos hac n
  simp only [gridWeight] at h
  have h1 := abs_lt_one_of_hat_ne_zero h
  have e : x - gridNode a c n i = gridStep a c n * ((x - a) / gridStep a c n - i.val) := by
    simp only [gridNode]
    field_simp
    ring
  rw [e, abs_mul, abs_of_pos hs]
  calc _ < gridStep a c n * 1 := mul_lt_mul_of_pos_left h1 hs
    _ = _ := mul_one _

/-- The hat interpolation `Σ_i hat((x − a)/h − i) w_i` of the node values `w`. -/
def interp {E : Type*} [AddCommGroup E] [Module ℝ E] (a c : ℝ) (n : ℕ) (w : Fin (n + 2) → E)
    (x : ℝ) : E :=
  ∑ i, gridWeight a c n i x • w i

/-- The interpolation is continuous on `ℝ`. -/
theorem continuous_interp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a c : ℝ) (n : ℕ)
    (w : Fin (n + 2) → E) : Continuous (interp a c n w) := by
  have e : interp a c n w = fun x => ∑ i, gridWeight a c n i x • w i := by
    funext x
    simp only [interp]
  rw [e]
  exact continuous_finsetSum _ fun i _ => (continuous_gridWeight a c n i).smul continuous_const

/-- **Local error bound.** If `‖w_i − f(x)‖ ≤ ε` for every node with nonzero weight at
`x ∈ [a, c]`, then `‖interp w x − f(x)‖ ≤ ε`. -/
theorem norm_interp_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a c : ℝ}
    (hac : a < c) (n : ℕ) (w : Fin (n + 2) → E) (f : ℝ → E) {x : ℝ} (hx : x ∈ Icc a c) {ε : ℝ}
    (h : ∀ i, gridWeight a c n i x ≠ 0 → ‖w i - f x‖ ≤ ε) : ‖interp a c n w x - f x‖ ≤ ε := by
  have hsum := sum_gridWeight hac n hx
  have e : interp a c n w x - f x = ∑ i, gridWeight a c n i x • (w i - f x) := by
    simp only [interp, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
  rw [e]
  calc ‖∑ i, gridWeight a c n i x • (w i - f x)‖
        ≤ ∑ i, ‖gridWeight a c n i x • (w i - f x)‖ := norm_sum_le _ _
    _ ≤ ∑ i, gridWeight a c n i x * ε := Finset.sum_le_sum fun i _ => by
        rw [norm_smul, Real.norm_of_nonneg (gridWeight_nonneg a c n i x)]
        by_cases hi : gridWeight a c n i x = 0
        · rw [hi, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (h i hi) (gridWeight_nonneg a c n i x)
    _ = ε := by rw [← Finset.sum_mul, hsum, one_mul]

/-- **Uniform convergence of the interpolation.** For `a < c`, `f` continuous on `[a, c]` and node
values with `‖w_n(i) − f(x_i)‖ ≤ η_n → 0`, the interpolations converge to `f` uniformly on
`[a, c]`. -/
theorem tendstoUniformlyOn_interp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a c : ℝ}
    (hac : a < c) {f : ℝ → E} (hf : ContinuousOn f (Icc a c)) (w : (n : ℕ) → Fin (n + 2) → E)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hw : ∀ n i, ‖w n i - f (gridNode a c n i)‖ ≤ η n) :
    TendstoUniformlyOn (fun n => interp a c n (w n)) f atTop (Icc a c) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) (ε / 2) (half_pos hε)
  obtain ⟨M, hM⟩ := exists_nat_gt ((c - a) / δ)
  filter_upwards [(tendsto_order.1 hη).2 (ε / 2) (half_pos hε), eventually_ge_atTop M]
    with n hn hnM x hx
  have hstep : gridStep a c n < δ := by
    simp only [gridStep]
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hM
    have h1 : (M : ℝ) ≤ n := by exact_mod_cast hnM
    nlinarith
  rw [dist_comm, dist_eq_norm]
  refine lt_of_le_of_lt (norm_interp_sub_le hac n (w n) f hx (ε := η n + ε / 2) fun i hi => ?_)
    (by linarith)
  have hd := hfδ _ (gridNode_mem hac.le n i) x hx (by
    rw [Real.dist_eq, abs_sub_comm]
    exact (abs_sub_gridNode_lt hac hi).trans hstep)
  rw [dist_eq_norm] at hd
  calc ‖w n i - f x‖ = ‖(w n i - f (gridNode a c n i)) + (f (gridNode a c n i) - f x)‖ := by
        congr 1
        abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ η n + ε / 2 := add_le_add (hw n i) hd.le

/-- Dyadic floor error: `|⌊2ⁿ v⌋/2ⁿ − v| ≤ (1/2)ⁿ`. -/
theorem abs_dyadicFloor_sub_le (n : ℕ) (v : ℝ) :
    |(⌊(2 : ℝ) ^ n * v⌋ : ℝ) / 2 ^ n - v| ≤ (1 / 2) ^ n := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have h1 := Int.floor_le ((2 : ℝ) ^ n * v)
  have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ n * v)
  have e : (⌊(2 : ℝ) ^ n * v⌋ : ℝ) / 2 ^ n - v = ((⌊(2 : ℝ) ^ n * v⌋ : ℝ) - 2 ^ n * v) / 2 ^ n := by
    field_simp
  have e2 : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  rw [e, abs_div, abs_of_pos hp, div_le_iff₀ hp, e2, abs_le]
  constructor <;> linarith

/-- Dyadic floors of nonnegative numbers are nonnegative. -/
theorem dyadicFloor_nonneg (n : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ (⌊(2 : ℝ) ^ n * v⌋ : ℝ) / 2 ^ n :=
  div_nonneg (Int.cast_nonneg (Int.floor_nonneg.2 (mul_nonneg (by positivity) hv)))
    (by positivity)

/-!
## The coded grid coefficients
-/

variable {N : ℕ}

/-- The integer code of the grid coefficients: at each node, the integers `⌊2ⁿ v⌋` for the rate
and damping values `v`. A countable type. -/
abbrev CoeffCode (N n : ℕ) : Type := Fin (n + 2) → (Fin N → Fin N → ℤ) × (Fin N → ℤ)

/-- The code of the path `ω`: the dyadic floors of `shortRate` and `refDamping` at the nodes. -/
def coeffCode (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ n : ℕ) (ω : FlowSample N) :
    CoeffCode N n :=
  fun i => (fun k l => ⌊(2 : ℝ) ^ n * shortRate F a ω ℓ (gridNode a c n i) k l⌋,
    fun k => ⌊(2 : ℝ) ^ n * refDamping F a b₀ ω ℓ (gridNode a c n i) k⌋)

/-- The node values `z/2ⁿ` decoded from a code. -/
def decodeCoeff (n : ℕ) (z : CoeffCode N n) :
    Fin (n + 2) → (Fin N → Fin N → ℝ) × (Fin N → ℝ) :=
  fun i => (fun k l => ((z i).1 k l : ℝ) / 2 ^ n, fun k => ((z i).2 k : ℝ) / 2 ^ n)

/-- The coefficient pair (rates, damping) decoded from a code: hat interpolation on the grid. -/
def codeCoeff (a c : ℝ) (n : ℕ) (z : CoeffCode N n) :
    ℝ → (Fin N → Fin N → ℝ) × (Fin N → ℝ) :=
  interp a c n (decodeCoeff n z)

/-- **The grid coefficients** of the path `ω`: hat interpolation of the dyadic floors of
`(shortRate, refDamping)` at the nodes of `[a, c]`. -/
def gridCoeff (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ n : ℕ) (ω : FlowSample N) :
    ℝ → (Fin N → Fin N → ℝ) × (Fin N → ℝ) :=
  codeCoeff a c n (coeffCode F a c b₀ ℓ n ω)

/-- The rate part of `gridCoeff`. -/
def gridRate (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ n : ℕ) (ω : FlowSample N) (x : ℝ) :
    Fin N → Fin N → ℝ :=
  (gridCoeff F a c b₀ ℓ n ω x).1

/-- The damping part of `gridCoeff`. -/
def gridDamp (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ n : ℕ) (ω : FlowSample N) (x : ℝ) :
    Fin N → ℝ :=
  (gridCoeff F a c b₀ ℓ n ω x).2

/-- `gridCoeff` factors through the code. -/
theorem gridCoeff_eq_codeCoeff (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ n : ℕ)
    (ω : FlowSample N) : gridCoeff F a c b₀ ℓ n ω = codeCoeff a c n (coeffCode F a c b₀ ℓ n ω) :=
  rfl

/-- **The code is path measurable.** For `a ≤ c`, `ω ↦ coeffCode F a c b₀ ℓ n ω` is
`pathSigma F a a c`-measurable (into the countable discrete code type). -/
theorem measurable_coeffCode (F : Matrix (Fin N) (Fin N) ℂ) {a c : ℝ} (hac : a ≤ c) (b₀ : ℝ)
    (ℓ n : ℕ) : Measurable[pathSigma F a a c] (coeffCode F a c b₀ ℓ n) := by
  let _ : MeasurableSpace (FlowSample N) := pathSigma F a a c
  refine Measurable.of_eval fun i => Measurable.prodMk ?_ ?_
  · refine Measurable.of_eval fun k => Measurable.of_eval fun l => ?_
    exact (measurable_const.mul
      (measurable_shortRate_pathSigma F (gridNode_mem hac n i) ℓ k l)).floor
  · refine Measurable.of_eval fun k => ?_
    exact (measurable_const.mul
      (measurable_refDamping_pathSigma F (gridNode_mem hac n i) b₀ ℓ k)).floor

/-- **Factorization through a countable type.** `gridCoeff F a c b₀ ℓ n` is a function of a
`pathSigma F a a c`-measurable code with values in the countable type `CoeffCode N n`. -/
theorem gridCoeff_factors (F : Matrix (Fin N) (Fin N) ℂ) {a c : ℝ} (hac : a ≤ c) (b₀ : ℝ)
    (ℓ n : ℕ) : ∃ code : FlowSample N → CoeffCode N n, Measurable[pathSigma F a a c] code ∧
      ∀ ω, gridCoeff F a c b₀ ℓ n ω = codeCoeff a c n (code ω) :=
  ⟨coeffCode F a c b₀ ℓ n, measurable_coeffCode F hac b₀ ℓ n, fun _ => rfl⟩

/-- The rate entries of `gridCoeff` as weighted sums of dyadic floors. -/
theorem gridRate_apply (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ n : ℕ) (ω : FlowSample N)
    (x : ℝ) (k l : Fin N) : gridRate F a c b₀ ℓ n ω x k l = ∑ i, gridWeight a c n i x *
      ((⌊(2 : ℝ) ^ n * shortRate F a ω ℓ (gridNode a c n i) k l⌋ : ℝ) / 2 ^ n) := by
  simp only [gridRate, gridCoeff, codeCoeff, interp, decodeCoeff, coeffCode, Prod.fst_sum,
    Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The damping entries of `gridCoeff` as weighted sums of dyadic floors. -/
theorem gridDamp_apply (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ n : ℕ) (ω : FlowSample N)
    (x : ℝ) (k : Fin N) : gridDamp F a c b₀ ℓ n ω x k = ∑ i, gridWeight a c n i x *
      ((⌊(2 : ℝ) ^ n * refDamping F a b₀ ω ℓ (gridNode a c n i) k⌋ : ℝ) / 2 ^ n) := by
  simp only [gridDamp, gridCoeff, codeCoeff, interp, decodeCoeff, coeffCode, Prod.snd_sum,
    Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- `gridCoeff` is continuous on `ℝ`. -/
theorem continuous_gridCoeff (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ n : ℕ)
    (ω : FlowSample N) : Continuous (gridCoeff F a c b₀ ℓ n ω) := by
  simp only [gridCoeff, codeCoeff]
  exact continuous_interp a c n _

/-- **Admissibility of the grid coefficients.** For every `u`, the rate and damping parts of
`gridCoeff` satisfy `Admissible a u`. -/
theorem admissible_gridCoeff (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ n : ℕ)
    (ω : FlowSample N) (u : ℝ) :
    Admissible a u (gridRate F a c b₀ ℓ n ω) (gridDamp F a c b₀ ℓ n ω) := by
  have hc := continuous_gridCoeff F a c b₀ ℓ n ω
  refine ⟨?_, ?_, fun x k l => ?_, fun x k l => ?_, fun x k => ?_⟩
  · have e : gridRate F a c b₀ ℓ n ω = fun x => (gridCoeff F a c b₀ ℓ n ω x).1 := by
      funext x
      simp only [gridRate]
    rw [e]
    exact (continuous_fst.comp hc).continuousOn
  · have e : gridDamp F a c b₀ ℓ n ω = fun x => (gridCoeff F a c b₀ ℓ n ω x).2 := by
      funext x
      simp only [gridDamp]
    rw [e]
    exact (continuous_snd.comp hc).continuousOn
  · simp only [gridRate_apply, shortRate_comm F a ω ℓ _ k l]
  · rw [gridRate_apply]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (gridWeight_nonneg a c n i x)
      (dyadicFloor_nonneg n (shortRate_nonneg F a ω ℓ _ k l))
  · rw [gridDamp_apply]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (gridWeight_nonneg a c n i x)
      (dyadicFloor_nonneg n (refDamping_nonneg F a b₀ ω ℓ _ k))

/-- The decoded node values are `(1/2)ⁿ`-close to the coefficient values at the nodes. -/
theorem norm_decodeCoeff_sub_le (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ n : ℕ)
    (ω : FlowSample N) (i : Fin (n + 2)) :
    ‖decodeCoeff n (coeffCode F a c b₀ ℓ n ω) i -
        (shortRate F a ω ℓ (gridNode a c n i), refDamping F a b₀ ω ℓ (gridNode a c n i))‖ ≤
      (1 / 2) ^ n := by
  have hη : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
  rw [norm_prod_le_iff]
  refine ⟨(pi_norm_le_iff_of_nonneg hη).2 fun k => (pi_norm_le_iff_of_nonneg hη).2 fun l => ?_,
    (pi_norm_le_iff_of_nonneg hη).2 fun k => ?_⟩
  · simp only [decodeCoeff, coeffCode, Prod.fst_sub, Pi.sub_apply, Real.norm_eq_abs]
    exact abs_dyadicFloor_sub_le n _
  · simp only [decodeCoeff, coeffCode, Prod.snd_sub, Pi.sub_apply, Real.norm_eq_abs]
    exact abs_dyadicFloor_sub_le n _

/-- **Uniform convergence on simple paths.** For Hermitian `F`, `a < c` and
`ω ∈ simpleRatSet F a c`, the grid coefficients converge to `(shortRate, refDamping)` uniformly
on `[a, c]`. -/
theorem tendstoUniformlyOn_gridCoeff {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a c : ℝ} (hac : a < c) {ω : FlowSample N} (hω : ω ∈ RelativeDuhamel.simpleRatSet F a c) (b₀ : ℝ)
    (ℓ : ℕ) :
    TendstoUniformlyOn (fun n x => (gridRate F a c b₀ ℓ n ω x, gridDamp F a c b₀ ℓ n ω x))
      (fun x => (shortRate F a ω ℓ x, refDamping F a b₀ ω ℓ x)) atTop (Icc a c) := by
  have hf : ContinuousOn (fun x => (shortRate F a ω ℓ x, refDamping F a b₀ ω ℓ x)) (Icc a c) :=
    (continuousOn_shortRate_of_mem hF hac.le hω ℓ).prodMk
      (continuousOn_refDamping_of_mem hF hac.le hω b₀ ℓ)
  have h := tendstoUniformlyOn_interp hac hf (fun n => decodeCoeff n (coeffCode F a c b₀ ℓ n ω))
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    (norm_decodeCoeff_sub_le F a c b₀ ℓ · ω)
  simpa only [gridRate, gridDamp, gridCoeff, codeCoeff] using h

end BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint
