module

public import BlockBand.SourceProcess.Stochastic.Angular.Regularity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Complex angular contract: jets of random tests

The generator only sees a test through its values and its pair terms `(X_ij² + Y_ij²) f`. For a
`C²` test `g` and a radius `R` the **jet** `jet hg R ∈ C(B_R, ℝ × ℝ^{N×N})`,
`x ↦ (g x, (pairTerm g i j x)_{ij})`, lives in a separable metric space with its Borel
σ-algebra. For a random test whose values `ω ↦ f ω Z` are `m`-measurable, `ω ↦ jet (f ω)` is
`m`-measurable (`measurable_jet`): derivatives are limits of difference quotients
(`measurable_fderiv_apply`, `measurable_fderiv2_apply`), and measurability into `C(B_R, ·)` is
measurability of evaluations (`ContinuousMap.measurable_iff_eval`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionAngular

/-!
### Measurability of derivatives
-/

section Deriv
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tendsto_slope_seq {g : E → ℝ} {x : E} (hg : DifferentiableAt ℝ g x) (W : E) :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) * (g (x + (1 / ((k : ℝ) + 1)) • W) - g x)) atTop
      (𝓝 (fderiv ℝ g x W)) := by
  have hd : HasDerivAt (fun t : ℝ => g (x + t • W)) (fderiv ℝ g x W) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • W) W 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const W).const_add x
    have h2 : HasFDerivAt g (fderiv ℝ g x) (x + (0 : ℝ) • W) := by
      simpa using hg.hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  rw [hasDerivAt_iff_tendsto_slope_zero] at hd
  have ht : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => by simp only [mem_compl_iff, mem_singleton_iff]; positivity⟩
  refine (hd.comp ht).congr fun k => ?_
  simp [smul_eq_mul]

variable {Ω : Type*} {m : MeasurableSpace Ω}

theorem measurable_fderiv_apply {f : Ω → E → ℝ} {x : E}
    (hd : ∀ ω, DifferentiableAt ℝ (f ω) x) (hm : ∀ z, Measurable[m] fun ω => f ω z) (W : E) :
    Measurable[m] fun ω => fderiv ℝ (f ω) x W :=
  measurable_of_tendsto_metrizable
    (f := fun k ω => ((k : ℝ) + 1) * (f ω (x + (1 / ((k : ℝ) + 1)) • W) - f ω x))
    (fun _ => measurable_const.mul ((hm _).sub (hm _)))
    (tendsto_pi_nhds.2 fun ω => tendsto_slope_seq (hd ω) W)

theorem measurable_fderiv2_apply {f : Ω → E → ℝ} (hf : ∀ ω, ContDiff ℝ 2 (f ω))
    (hm : ∀ z, Measurable[m] fun ω => f ω z) (x W W' : E) :
    Measurable[m] fun ω => fderiv ℝ (fderiv ℝ (f ω)) x W W' := by
  have hD : ∀ ω, Differentiable ℝ (fderiv ℝ (f ω)) := fun ω =>
    ((hf ω).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hd1 : ∀ ω z, DifferentiableAt ℝ (f ω) z := fun ω z =>
    ((hf ω).differentiable (by norm_num)) z
  have hdg : ∀ ω, DifferentiableAt ℝ (fun y => fderiv ℝ (f ω) y W') x := fun ω =>
    (hD ω x).clm_apply (differentiableAt_const W')
  have hmg : ∀ z, Measurable[m] fun ω => fderiv ℝ (f ω) z W' := fun z =>
    measurable_fderiv_apply (fun ω => hd1 ω z) hm W'
  have key := measurable_fderiv_apply (f := fun ω y => fderiv ℝ (f ω) y W') hdg hmg W
  have e : (fun ω => fderiv ℝ (fun y => fderiv ℝ (f ω) y W') x W) =
      fun ω => fderiv ℝ (fderiv ℝ (f ω)) x W W' := by
    funext ω
    rw [fderiv_clm_apply (hD ω x) (differentiableAt_const W')]
    simp
  rw [← e]; exact key

end Deriv

/-!
### Jets
-/

variable {N r : ℕ}

/-- The closed ball of radius `R` in the array space. -/
abbrev Kb (N r : ℕ) (R : ℝ) : Type := Metric.closedBall (0 : AngularArray N r) R

/-- The jet space: value and pair terms. -/
abbrev JetSp (N : ℕ) : Type := ℝ × (Fin N → Fin N → ℝ)

/-- **The jet** of a `C²` test on the ball of radius `R`. -/
def jet {g : AngularArray N r → ℝ} (hg : ContDiff ℝ 2 g) (R : ℝ) : C(Kb N r R, JetSp N) :=
  ⟨fun x => (g x, fun i j => pairTerm g i j x),
    (hg.continuous.comp continuous_subtype_val).prodMk
      (continuous_pi fun i => continuous_pi fun j =>
        (continuous_pairTerm hg i j).comp continuous_subtype_val)⟩

@[simp] theorem jet_apply {g : AngularArray N r → ℝ} (hg : ContDiff ℝ 2 g) (R : ℝ)
    (x : Kb N r R) : jet hg R x = (g x, fun i j => pairTerm g i j x) := rfl

theorem abs_sub_le_dist_jet {g h : AngularArray N r → ℝ} (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 2 h) {R : ℝ} {Z : AngularArray N r} (hZ : ‖Z‖ ≤ R) :
    |g Z - h Z| ≤ dist (jet hg R) (jet hh R) := by
  have h1 := ContinuousMap.dist_apply_le_dist (f := jet hg R) (g := jet hh R)
    ⟨Z, mem_closedBall_zero_iff.2 hZ⟩
  rw [Prod.dist_eq] at h1
  rw [← Real.dist_eq]
  exact (le_max_left _ _).trans h1

theorem abs_pairTerm_sub_le_dist_jet {g h : AngularArray N r → ℝ} (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 2 h) {R : ℝ} {Z : AngularArray N r} (hZ : ‖Z‖ ≤ R) (i j : Fin N) :
    |pairTerm g i j Z - pairTerm h i j Z| ≤ dist (jet hg R) (jet hh R) := by
  have h1 := ContinuousMap.dist_apply_le_dist (f := jet hg R) (g := jet hh R)
    ⟨Z, mem_closedBall_zero_iff.2 hZ⟩
  rw [Prod.dist_eq] at h1
  rw [← Real.dist_eq]
  refine le_trans ?_ ((le_max_right _ _).trans h1)
  exact (dist_le_pi_dist (fun j => pairTerm g i j Z) (fun j => pairTerm h i j Z) j).trans
    (dist_le_pi_dist (fun i j => pairTerm g i j Z) (fun i j => pairTerm h i j Z) i)

theorem measurable_pairTerm {Ω : Type*} {m : MeasurableSpace Ω} {f : Ω → AngularArray N r → ℝ}
    (hf : ∀ ω, ContDiff ℝ 2 (f ω)) (hm : ∀ Z, Measurable[m] fun ω => f ω Z) (i j : Fin N)
    (Z : AngularArray N r) : Measurable[m] fun ω => pairTerm (f ω) i j Z := by
  have hd : ∀ ω, DifferentiableAt ℝ (f ω) Z := fun ω => ((hf ω).differentiable (by norm_num)) Z
  unfold pairTerm
  exact (((measurable_fderiv2_apply hf hm _ _ _).add (measurable_fderiv_apply hd hm _)).add
    (measurable_fderiv2_apply hf hm _ _ _)).add (measurable_fderiv_apply hd hm _)

/-- **Jets of random tests are measurable.** -/
theorem measurable_jet {Ω : Type*} {m : MeasurableSpace Ω} {f : Ω → AngularArray N r → ℝ}
    (hf : ∀ ω, ContDiff ℝ 2 (f ω)) (hm : ∀ Z, Measurable[m] fun ω => f ω Z) (R : ℝ) :
    Measurable[m] fun ω => jet (hf ω) R := by
  rw [ContinuousMap.measurable_iff_eval]
  intro x
  simp only [jet_apply]
  exact (hm x).prodMk (Measurable.of_eval fun i => Measurable.of_eval fun j =>
    measurable_pairTerm hf hm i j x)

/-!
### Approximation with values in the range
-/

/-- **Simple approximation with values in the range** (`SimpleFunc.approxOn`), stated without
simple-function coercions so that it can be used for a sub-σ-algebra. -/
theorem exists_approx_range {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {J : Ω → E} (hJ : Measurable J) (ω₀ : Ω) :
    ∃ (ap : ℕ → Ω → E) (T : ℕ → Finset E), (∀ k ω, ap k ω ∈ T k) ∧ (∀ k ω, ap k ω ∈ range J) ∧
      (∀ k c, MeasurableSet (ap k ⁻¹' {c})) ∧
      ∀ ω, Tendsto (fun k => ap k ω) atTop (𝓝 (J ω)) := by
  have : TopologicalSpace.SeparableSpace (range J) :=
    (TopologicalSpace.IsSeparable.of_separableSpace (range J)).separableSpace
  refine ⟨fun k => SimpleFunc.approxOn J hJ (range J) (J ω₀) ⟨ω₀, rfl⟩ k,
    fun k => (SimpleFunc.approxOn J hJ (range J) (J ω₀) ⟨ω₀, rfl⟩ k).range,
    fun k ω => SimpleFunc.mem_range_self _ ω, fun k ω => SimpleFunc.approxOn_mem hJ _ k ω,
    fun k c => SimpleFunc.measurableSet_fiber _ c,
    fun ω => SimpleFunc.tendsto_approxOn hJ _ (subset_closure ⟨ω, rfl⟩)⟩

end BlockBand.SourceProcess.Stochastic.ComplexAngular
