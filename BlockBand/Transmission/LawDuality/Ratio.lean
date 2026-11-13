module

public import BlockBand.Transmission.DualBoundary.LawValue

/-!
# Determination: the ratios `F_{x,y}` with `p` pairs

The one-pair lemmas on the ratios are lifted to `p` pairs through the factorization
* `ratioIntegrand_eq_sum`: `r_{x,y}(t) = Σ_i r_{x_i,y_i}(t)` (also at `t = 0`);
* **`transmissionRatio_eq_prod`**: `F_{x,y}(ν) = Π_i F_{x_i,y_i}(ν)` (`x ≥ 0`, `0 ≤ y < 1`);
* `measurable_transmissionRatio_vec` (Giry), `transmissionRatio_mem_vec` (`F ∈ (0,1]`),
  `tendsto_integral_ratio_vec` (dominated convergence in the parameters).

Then the first step of the determination (let `y_i ↓ 0` and permit repeated `x_i` by
continuity):
* **`integral_ratio_zero_eq`**: if two random finite measures on `[0,1]` have the same
  `E F_{x,y}` for all ordered interior parameters, they have the same `E F_{x,0}` for **every**
  `x : Fin n → ℝ` with `x ≥ 0` (repetitions and any order allowed).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.DualBoundary
open scoped NNReal ENNReal BoundedContinuousFunction

/-- `r_{x,y}(t) = Σ_i r_{x_i,y_i}(t)`. -/
theorem ratioIntegrand_eq_sum {p : ℕ} (x y : Fin p → ℝ) (t : ℝ) :
    ratioIntegrand x y t = ∑ i, ratioIntegrand ![x i] ![y i] t := by
  simp only [ratioIntegrand_one]
  unfold ratioIntegrand
  split_ifs with h
  · rw [← Finset.sum_neg_distrib]
  · rw [Finset.sum_div]

/-- Hypothesis bundle for the parameter range used below: `x ≥ 0`, `0 ≤ y < 1`. -/
def IsRatioRange {p : ℕ} (x y : Fin p → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∀ i, 0 ≤ y i ∧ y i < 1

theorem IsRatioParameter.isRatioRange {p : ℕ} {x y : Fin p → ℝ} (h : IsRatioParameter x y) :
    IsRatioRange x y :=
  ⟨fun i => (h.2.2.1 i).le, fun i => ⟨(h.2.2.2 i).1.le, (h.2.2.2 i).2⟩⟩

theorem isRatioRange_zero {p : ℕ} {x : Fin p → ℝ} (hx : ∀ i, 0 ≤ x i) :
    IsRatioRange x (fun _ => 0) :=
  ⟨hx, fun _ => ⟨le_rfl, zero_lt_one⟩⟩

theorem continuous_ratioIntegrand {p : ℕ} {x y : Fin p → ℝ} (h : IsRatioRange x y) :
    Continuous fun t : unitInterval => ratioIntegrand x y (t : ℝ) := by
  have e : (fun t : unitInterval => ratioIntegrand x y (t : ℝ)) =
      fun t : unitInterval => ∑ i, ratioIntegrand ![x i] ![y i] (t : ℝ) :=
    funext fun t => ratioIntegrand_eq_sum x y t
  rw [e]
  exact continuous_finsetSum _ fun i _ => (ratioBCF (h.1 i) (h.2 i).1 (h.2 i).2).continuous

theorem ratioIntegrand_bounds_vec {p : ℕ} {x y : Fin p → ℝ} (h : IsRatioRange x y) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    -(∑ i, (x i + y i / (1 - y i))) ≤ ratioIntegrand x y t ∧ ratioIntegrand x y t ≤ 0 := by
  rw [ratioIntegrand_eq_sum, ← Finset.sum_neg_distrib]
  exact ⟨Finset.sum_le_sum fun i _ =>
      (ratioIntegrand_bounds (h.1 i) (h.2 i).1 (h.2 i).2 ht0 ht1).1,
    Finset.sum_nonpos fun i _ => (ratioIntegrand_bounds (h.1 i) (h.2 i).1 (h.2 i).2 ht0 ht1).2⟩

theorem integrable_ratioIntegrand {p : ℕ} {x y : Fin p → ℝ} (h : IsRatioRange x y)
    (ν : FiniteMeasure unitInterval) :
    Integrable (fun t : unitInterval => ratioIntegrand x y (t : ℝ)) (ν : Measure unitInterval) :=
  (BoundedContinuousFunction.mkOfCompact ⟨_, continuous_ratioIntegrand h⟩).integrable _

/-- **`F_{x,y}(ν) = Π_i F_{x_i,y_i}(ν)`.** -/
theorem transmissionRatio_eq_prod {p : ℕ} {x y : Fin p → ℝ} (h : IsRatioRange x y)
    (ν : FiniteMeasure unitInterval) :
    transmissionRatio x y ν = ∏ i, transmissionRatio ![x i] ![y i] ν := by
  unfold transmissionRatio
  rw [← Real.exp_sum]
  rw [integral_congr_ae (Eventually.of_forall fun t : unitInterval =>
    ratioIntegrand_eq_sum x y (t : ℝ))]
  exact congrArg Real.exp (integral_finsetSum _ fun i _ =>
    (ratioBCF (h.1 i) (h.2 i).1 (h.2 i).2).integrable (ν : Measure unitInterval))

theorem transmissionRatio_mem_vec {p : ℕ} {x y : Fin p → ℝ} (h : IsRatioRange x y)
    (ν : FiniteMeasure unitInterval) :
    0 < transmissionRatio x y ν ∧ transmissionRatio x y ν ≤ 1 :=
  ⟨Real.exp_pos _, Real.exp_le_one_iff.2 (integral_nonpos fun t =>
    (ratioIntegrand_bounds_vec h t.2.1 t.2.2).2)⟩

theorem measurable_transmissionRatio_vec {p : ℕ} {x y : Fin p → ℝ} (h : IsRatioRange x y) :
    Measurable fun ν : FiniteMeasure unitInterval => transmissionRatio x y ν := by
  simp_rw [transmissionRatio_eq_prod h]
  exact Finset.measurable_prod _ fun i _ =>
    measurable_transmissionRatio (h.1 i) (h.2 i).1 (h.2 i).2

theorem norm_transmissionRatio_le {p : ℕ} {x y : Fin p → ℝ} (h : IsRatioRange x y)
    (ν : FiniteMeasure unitInterval) : ‖transmissionRatio x y ν‖ ≤ 1 := by
  have := transmissionRatio_mem_vec h ν
  rw [Real.norm_eq_abs, abs_of_pos this.1]; exact this.2

/-- **Dominated convergence in the parameters**, for a random finite measure `ν`. -/
theorem tendsto_integral_ratio_vec {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {ν : Ω → FiniteMeasure unitInterval} (hν : Measurable ν) {p : ℕ}
    {xs ys : ℕ → Fin p → ℝ} {x y : Fin p → ℝ} (hxs : ∀ i, Tendsto (fun n => xs n i) atTop (𝓝 (x i)))
    (hys : ∀ i, Tendsto (fun n => ys n i) atTop (𝓝 (y i))) (h : IsRatioRange x y)
    (hn : ∀ n, IsRatioRange (xs n) (ys n)) {ymax X : ℝ} (hymax : ∀ n i, ys n i ≤ ymax)
    (hymax1 : ymax < 1) (hX : ∀ n i, xs n i ≤ X) :
    Tendsto (fun n => ∫ ω, transmissionRatio (xs n) (ys n) (ν ω) ∂P) atTop
      (𝓝 (∫ ω, transmissionRatio x y (ν ω) ∂P)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => ((measurable_transmissionRatio_vec (hn n)).comp hν).aestronglyMeasurable)
    (integrable_const 1) (fun n => Eventually.of_forall fun ω => norm_transmissionRatio_le (hn n) _)
    (Eventually.of_forall fun ω => ?_)
  simp_rw [transmissionRatio_eq_prod (hn _), transmissionRatio_eq_prod h]
  exact tendsto_finsetProd _ fun i _ => tendsto_transmissionRatio_param (hxs i) (hys i)
    (h.1 i) (h.2 i).1 (h.2 i).2 (fun n => (hn n).1 i) (fun n => ((hn n).2 i).1)
    (fun n => hymax n i) hymax1 (fun n => hX n i) (ν ω)

/-!
## Repeated parameters and `y ↓ 0`
-/

theorem ratioIntegrand_comp_perm {p : ℕ} (x y : Fin p → ℝ) (σ : Equiv.Perm (Fin p)) (t : ℝ) :
    ratioIntegrand (x ∘ σ) (y ∘ σ) t = ratioIntegrand x y t := by
  rw [ratioIntegrand_eq_sum (x ∘ σ), ratioIntegrand_eq_sum x y]
  exact Equiv.sum_comp σ (fun i => ratioIntegrand ![x i] ![y i] t)

theorem transmissionRatio_comp_perm {p : ℕ} (x y : Fin p → ℝ) (σ : Equiv.Perm (Fin p))
    (ν : FiniteMeasure unitInterval) :
    transmissionRatio (x ∘ σ) (y ∘ σ) ν = transmissionRatio x y ν := by
  unfold transmissionRatio
  simp_rw [ratioIntegrand_comp_perm]

/-- Equality of the ratio transforms of two random finite measures on `[0,1]`. -/
def SameRatioTransforms {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω)
    (ν : Ω → FiniteMeasure unitInterval) (P' : Measure Ω') (ν' : Ω' → FiniteMeasure unitInterval) :
    Prop :=
  ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
    ∫ ω, transmissionRatio x y (ν ω) ∂P = ∫ ω, transmissionRatio x y (ν' ω) ∂P'

/-- The ordered interior approximants `x_i + (i+1)/(m+1)`, `(i+1)/(2(m+1)(p+1))` of a monotone
`x ≥ 0` and of `y = 0`. -/
def approxX {p : ℕ} (x : Fin p → ℝ) (m : ℕ) : Fin p → ℝ :=
  fun i => x i + ((i : ℝ) + 1) / ((m : ℝ) + 1)

def approxY (p m : ℕ) : Fin p → ℝ :=
  fun i => ((i : ℝ) + 1) / (2 * ((m : ℝ) + 1) * ((p : ℝ) + 1))

theorem approxY_le {p : ℕ} (m : ℕ) (i : Fin p) : approxY p m i ≤ 1 / 2 := by
  unfold approxY
  have hi : (i : ℝ) + 1 ≤ (p : ℝ) + 1 := by
    have := i.2; exact_mod_cast Nat.succ_le_succ this.le
  rw [div_le_iff₀ (by positivity)]
  have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  nlinarith [(Nat.cast_nonneg (i : ℕ) : (0 : ℝ) ≤ (i : ℕ))]

theorem approx_isRatioParameter {p : ℕ} {x : Fin p → ℝ} (hx : ∀ i, 0 ≤ x i) (hm : Monotone x)
    (m : ℕ) : IsRatioParameter (approxX x m) (approxY p m) := by
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i => ?_, fun i => ⟨?_, ?_⟩⟩
  · have h : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
    have := hm hij.le
    unfold approxX
    have : ((i : ℝ) + 1) / ((m : ℝ) + 1) < ((j : ℝ) + 1) / ((m : ℝ) + 1) :=
      div_lt_div_of_pos_right (by linarith) (by positivity)
    linarith
  · have h : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
    exact div_lt_div_of_pos_right (by linarith) (by positivity)
  · unfold approxX; have := hx i; positivity
  · unfold approxY; positivity
  · linarith [approxY_le m i]

theorem tendsto_approxX {p : ℕ} (x : Fin p → ℝ) (i : Fin p) :
    Tendsto (fun m => approxX x m i) atTop (𝓝 (x i)) := by
  unfold approxX
  have : Tendsto (fun m : ℕ => ((i : ℝ) + 1) / ((m : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((i : ℝ) + 1))
  simpa using tendsto_const_nhds.add this

theorem tendsto_approxY (p : ℕ) (i : Fin p) :
    Tendsto (fun m => approxY p m i) atTop (𝓝 0) := by
  unfold approxY
  have h : Tendsto (fun m : ℕ => ((i : ℝ) + 1) / (2 * ((p : ℝ) + 1)) * (1 / ((m : ℝ) + 1)))
      atTop (𝓝 (((i : ℝ) + 1) / (2 * ((p : ℝ) + 1)) * 0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
  rw [mul_zero] at h
  refine h.congr fun m => ?_
  field_simp

/-- **Repeated parameters and `y ↓ 0`**: equal ratio transforms give equal
`E F_{x,0}` for every `x ≥ 0` (any order, repetitions allowed). -/
theorem integral_ratio_zero_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → FiniteMeasure unitInterval}
    (hν : Measurable ν) {P' : Measure Ω'} [IsProbabilityMeasure P']
    {ν' : Ω' → FiniteMeasure unitInterval} (hν' : Measurable ν')
    (h : SameRatioTransforms P ν P' ν') {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∫ ω, transmissionRatio x (fun _ => 0) (ν ω) ∂P =
      ∫ ω, transmissionRatio x (fun _ => 0) (ν' ω) ∂P' := by
  set σ := Tuple.sort x
  set x' := x ∘ σ
  have hx' : ∀ i, 0 ≤ x' i := fun i => hx _
  have hmono : Monotone x' := Tuple.monotone_sort x
  have hperm : ∀ μ : FiniteMeasure unitInterval,
      transmissionRatio x (fun _ => 0) μ = transmissionRatio x' (fun _ => 0) μ := fun μ =>
    (transmissionRatio_comp_perm x (fun _ => 0) σ μ).symm
  simp_rw [hperm]
  have hrange : ∀ m, IsRatioRange (approxX x' m) (approxY n m) := fun m =>
    IsRatioParameter.isRatioRange (approx_isRatioParameter hx' hmono m)
  have hX : ∀ m i, approxX x' m i ≤ ∑ j, x' j + n := by
    intro m i
    unfold approxX
    have h1 : ((i : ℝ) + 1) / ((m : ℝ) + 1) ≤ (i : ℝ) + 1 :=
      div_le_self (by positivity) (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    have h2 : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast i.2
    have h3 : x' i ≤ ∑ j, x' j := Finset.single_le_sum (fun j _ => hx' j) (Finset.mem_univ i)
    linarith
  have t1 := tendsto_integral_ratio_vec (P := P) hν (xs := fun m => approxX x' m)
    (ys := fun m => approxY n m) (y := fun _ => 0) (tendsto_approxX x') (tendsto_approxY n)
    (isRatioRange_zero hx') hrange (fun m i => approxY_le m i) (by norm_num) hX
  have t2 := tendsto_integral_ratio_vec (P := P') hν' (xs := fun m => approxX x' m)
    (ys := fun m => approxY n m) (y := fun _ => 0) (tendsto_approxX x') (tendsto_approxY n)
    (isRatioRange_zero hx') hrange (fun m i => approxY_le m i) (by norm_num) hX
  exact tendsto_nhds_unique (t1.congr fun m => h n _ _ (approx_isRatioParameter hx' hmono m)) t2

end BlockBand.Transmission.LawDuality
