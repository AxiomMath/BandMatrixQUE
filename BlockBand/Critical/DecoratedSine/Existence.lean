module

public import BlockBand.Endpoints.Sine.Law
public import BlockBand.Internal.Contracts.CriticalEntire
public import Mathlib.Probability.ProductMeasure
public import BlockBand.Critical.DecoratedSine.Construction
public import BlockBand.Critical.DecoratedSine.MarkAverage

/-!
# Existence of the decorated sine process

The decorated sine process is the sine process with i.i.d. standard circular Gaussian marks in
`ℂ^r` attached to its points. `integral_decoratedLaw_exp_neg` computes its Laplace functional,
and `exists_isDecoratedSineProcess` gives a realization satisfying `IsDecoratedSineProcess`.

Law: on `Ω = VaguePointMeasure ℝ × (ℤ × ℕ → ℂ^r)`, `P = P₀ ⊗ γ^{⊗(ℤ × ℕ)}` (`decoratedLaw`), with
`P₀` any law satisfying `IsSineLaw` (one exists by `exists_isSineLaw`) and
`γ = circularVectorLaw (Fin r)`; `Ξ(ξ, m) = decoratedPoint ξ m` (`decoratedSine`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.DecoratedSine

open MeasureTheory Set Filter
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)
open scoped ENNReal Topology

theorem isProbabilityMeasure_circularVectorLaw (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (circularVectorLaw ι) := by
  unfold circularVectorLaw
  infer_instance

/-- Independence of the marks: the integral of a finite product of functions of distinct
coordinates under the infinite product law is the product of the integrals. -/
theorem integral_infinitePi_finset_prod {ι Y : Type*} [MeasurableSpace Y] (γ : Measure Y)
    [IsProbabilityMeasure γ] (T : Finset ι) (φ : ι → Y → ℝ)
    (hφ : ∀ i, AEStronglyMeasurable (φ i) γ) :
    ∫ m, ∏ p ∈ T, φ p (m p) ∂Measure.infinitePi (fun _ : ι => γ) = ∏ p ∈ T, ∫ y, φ p y ∂γ := by
  set F : (T → Y) → ℝ := fun y => ∏ i : T, φ i (y i)
  have h1 : (fun m : ι → Y => ∏ p ∈ T, φ p (m p)) = fun m => F (T.restrict m) := by
    funext m
    rw [← Finset.prod_coe_sort T]
    rfl
  have hF : AEStronglyMeasurable F (Measure.pi fun _ : T => γ) := by
    refine Finset.aestronglyMeasurable_fun_prod _ fun i _ => ?_
    exact (hφ i).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : T => γ) i)
  rw [h1]
  refine (integral_restrict_infinitePi (μ := fun _ : ι => γ) hF).trans ?_
  rw [integral_fintype_prod_eq_prod (𝕜 := ℝ)]
  exact Finset.prod_coe_sort T fun p => ∫ y, φ p y ∂γ

attribute [local instance] isProbabilityMeasure_circularVectorLaw

variable (r : ℕ)

/-- Sample space of the decorated sine process: a sine configuration and an i.i.d. family of
marks indexed by (window, rank) pairs. -/
abbrev DecoratedSpace : Type :=
  VaguePointMeasure ℝ × (ℤ × ℕ → (Fin r → ℂ))

/-- The decoration map `(ξ, m) ↦ Σ_{n, j < N_n(ξ)} δ_{(x_{n,j}(ξ), m(n,j))}`. -/
def decoratedSine (ω : DecoratedSpace r) : VaguePointMeasure (ℝ × (Fin r → ℂ)) :=
  decoratedPoint ω.1 ω.2

/-- Law of the marks: i.i.d. standard circular Gaussian vectors. -/
def markLaw : Measure (ℤ × ℕ → (Fin r → ℂ)) :=
  Measure.infinitePi fun _ : ℤ × ℕ => circularVectorLaw (Fin r)

instance : IsProbabilityMeasure (markLaw r) := by
  unfold markLaw
  infer_instance

/-- The decorated law: the sine law times the i.i.d. mark law. -/
def decoratedLaw (P₀ : ProbabilityMeasure (VaguePointMeasure ℝ)) : Measure (DecoratedSpace r) :=
  (P₀ : Measure (VaguePointMeasure ℝ)).prod (markLaw r)

instance (P₀ : ProbabilityMeasure (VaguePointMeasure ℝ)) :
    IsProbabilityMeasure (decoratedLaw r P₀) := by
  unfold decoratedLaw
  infer_instance

theorem measurable_decoratedSine : Measurable (decoratedSine r) :=
  measurable_decoratedPoint

variable {r}

/-- Conditional Laplace functional: for a fixed ground configuration `ξ`, averaging over the
i.i.d. marks replaces `f` by the averaged test `h = -log ∫ e^{-f(·, g)} dγ`. -/
theorem integral_markLaw_exp_neg (ξ : VaguePointMeasure ℝ)
    (f : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ) (hf0 : ∀ z, 0 ≤ f z) :
    ∫ m, Real.exp (-∫ z, f z ∂(decoratedPoint ξ m).measure) ∂markLaw r =
      Real.exp (-∫ x, markTest (circularVectorLaw (Fin r)) f hf0 x ∂ξ.measure) := by
  set γ := circularVectorLaw (Fin r)
  set h := markTest γ f hf0
  obtain ⟨R, hR⟩ : ∃ R : ℝ, Prod.fst '' tsupport f ⊆ Icc (-R) R := by
    obtain ⟨R, hR⟩ := (f.hasCompactSupport.image continuous_fst).isBounded.subset_closedBall 0
    refine ⟨R, fun y hy => ?_⟩
    have := hR hy
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact abs_le.mp this
  have hfR : ∀ z : ℝ × (Fin r → ℂ), R < |z.1| → f z = 0 := by
    intro z hz
    refine image_eq_zero_of_notMem_tsupport fun hzs => ?_
    have := hR ⟨z, hzs, rfl⟩
    have := abs_le.mpr this
    linarith
  have hhR : ∀ x : ℝ, R < |x| → h x = 0 := by
    intro x hx
    exact markTest_eq_zero f hf0 fun g => hfR (x, g) hx
  have hhint : Integrable h ξ.measure :=
    (map_continuous h).integrable_of_hasCompactSupport h.hasCompactSupport
  have hground := integral_ground_eq_sum ξ h hhint R hhR
  have hinner : ∀ m : ℤ × ℕ → (Fin r → ℂ),
      Real.exp (-∫ z, f z ∂(decoratedPoint ξ m).measure) =
        ∏ p ∈ atomIndex ξ R, Real.exp (-f (windowAtom ξ p.1 p.2, m p)) := by
    intro m
    have hfint : Integrable f (decoratedPoint ξ m).measure :=
      (map_continuous f).integrable_of_hasCompactSupport f.hasCompactSupport
    rw [decoratedPoint_measure] at hfint ⊢
    rw [integral_decorated_eq_sum ξ m f hfint R hfR, ← Finset.sum_neg_distrib, Real.exp_sum]
  simp_rw [hinner]
  rw [markLaw, integral_infinitePi_finset_prod γ (atomIndex ξ R)
      (fun p g => Real.exp (-f (windowAtom ξ p.1 p.2, g)))
      (fun p => (Real.continuous_exp.comp
        ((map_continuous f).comp (Continuous.prodMk_right _)).neg).aestronglyMeasurable),
    hground, ← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [exp_neg_markTest]
  rfl

/-- **The Laplace functional of the decorated process.** -/
theorem integral_decoratedLaw_exp_neg {P₀ : ProbabilityMeasure (VaguePointMeasure ℝ)}
    (hP₀ : IsSineLaw P₀) (f : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ)
    (hf0 : ∀ z, 0 ≤ f z) :
    ∫ ω, Real.exp (-∫ z, f z ∂(decoratedSine r ω).measure) ∂decoratedLaw r P₀ =
      decoratedSineLaplace r f := by
  have hmeas : Measurable fun ω : DecoratedSpace r =>
      Real.exp (-∫ z, f z ∂(decoratedSine r ω).measure) :=
    Real.measurable_exp.comp
      ((BlockBand.Model.Construction.continuous_vaguePointMeasure_coordinate f).measurable.comp
        (measurable_decoratedSine r)).neg
  have hint : Integrable (fun ω : DecoratedSpace r =>
      Real.exp (-∫ z, f z ∂(decoratedSine r ω).measure)) (decoratedLaw r P₀) := by
    refine (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    exact integral_nonneg hf0
  rw [decoratedLaw, integral_prod _ hint]
  simp only [decoratedSine]
  simp_rw [integral_markLaw_exp_neg _ f hf0]
  rw [hP₀.2 _ (markTest_nonneg f hf0), sineLaplaceFunctional, decoratedSineLaplace]
  congr 1
  funext k
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [exp_neg_markTest]
  rfl

theorem isDecoratedSineProcess_decoratedLaw {P₀ : ProbabilityMeasure (VaguePointMeasure ℝ)}
    (hP₀ : IsSineLaw P₀) : IsDecoratedSineProcess r (decoratedLaw r P₀) (decoratedSine r) where
  prob := inferInstance
  measurable := measurable_decoratedSine r
  simple := by
    have h := (Measure.quasiMeasurePreserving_fst (μ := (P₀ : Measure (VaguePointMeasure ℝ)))
      (ν := markLaw r)).ae hP₀.1
    filter_upwards [h] with ω hω x
    rw [decoratedSine, decoratedPoint_measure_prod_univ _ _ (measurableSet_singleton x)]
    exact hω x
  laplace f hf0 := integral_decoratedLaw_exp_neg hP₀ f hf0

/-- **Existence of the decorated sine process** (`IsDecoratedSineProcess`): for every
`r`, on `Ω = VaguePointMeasure ℝ × (ℤ × ℕ → ℂ^r)` with the sine law times i.i.d. standard circular
Gaussian marks, `Ξ(ξ, m) = Σ_{n ∈ ℤ, j < ξ[n, n+1)} δ_{(x_{n,j}(ξ), m(n,j))}` (`x_{n,j}` the
`j`-th point of `ξ` in `[n, n+1)`) is a decorated sine process.
-/
theorem exists_isDecoratedSineProcess (r : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))), IsDecoratedSineProcess r P Ξ := by
  obtain ⟨P₀, hP₀⟩ := BlockBand.Endpoints.exists_isSineLaw
  exact ⟨DecoratedSpace r, inferInstance, decoratedLaw r P₀, decoratedSine r,
    isDecoratedSineProcess_decoratedLaw hP₀⟩

end BlockBand.Critical.DecoratedSine
