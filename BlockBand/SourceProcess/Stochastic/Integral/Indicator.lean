module
public import BlockBand.SourceProcess.Stochastic.Basic
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Indicator multiplication operators

Multiplication by the indicator of a measurable set as a continuous linear operator of norm
at most one on `L²(ν)` (any measure `ν`), on the scalar predictable space
`PredictableL2 = lpMeas (raw predictable σ-algebra) 2 (dt ⊗ driverLaw μ)`, and coordinatewise
on the predictable family `PredictableFamily T`, for a set measurable for the raw enlarged
predictable σ-algebra. Only generic `L²` facts are used.
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion

section Generic
variable {α : Type*} [mα : MeasurableSpace α] {ν : Measure α}

/-- The linear map `f ↦ 1_R f` on `L²(ν)`. -/
def indicatorL2Linear (R : Set α) (hR : MeasurableSet R) :
    Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 ν where
  toFun f := ((Lp.memLp f).indicator hR.nullMeasurableSet).toLp (R.indicator (f : α → ℝ))
  map_add' f g := by
    have hae : R.indicator ((f + g : Lp ℝ 2 ν) : α → ℝ) =ᵐ[ν]
        R.indicator (f : α → ℝ) + R.indicator (g : α → ℝ) := by
      filter_upwards [Lp.coeFn_add f g] with x hx
      by_cases hxR : x ∈ R
      · simp only [Pi.add_apply, Set.indicator_of_mem hxR, hx]
      · simp only [Pi.add_apply, Set.indicator_of_notMem hxR, add_zero]
    exact (MemLp.toLp_congr _ (((Lp.memLp f).indicator hR.nullMeasurableSet).add
      ((Lp.memLp g).indicator hR.nullMeasurableSet)) hae).trans (MemLp.toLp_add _ _)
  map_smul' c f := by
    have hae : R.indicator ((c • f : Lp ℝ 2 ν) : α → ℝ) =ᵐ[ν]
        c • R.indicator (f : α → ℝ) := by
      filter_upwards [Lp.coeFn_smul c f] with x hx
      by_cases hxR : x ∈ R
      · simp only [Pi.smul_apply, Set.indicator_of_mem hxR, hx]
      · simp only [Pi.smul_apply, Set.indicator_of_notMem hxR, smul_zero]
    exact (MemLp.toLp_congr _ (((Lp.memLp f).indicator hR.nullMeasurableSet).const_smul c)
      hae).trans (MemLp.toLp_const_smul _ _)

theorem norm_indicator_toLp_le (R : Set α) (hR : MeasurableSet R) (f : Lp ℝ 2 ν) :
    ‖((Lp.memLp f).indicator hR.nullMeasurableSet).toLp (R.indicator (f : α → ℝ))‖ ≤ ‖f‖ := by
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_indicator_le _ hR.nullMeasurableSet)

/-- Multiplication by `1_R` on `L²(ν)`, a continuous linear operator of norm at most one. -/
def indicatorL2 (R : Set α) (hR : MeasurableSet R) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (indicatorL2Linear R hR).mkContinuous 1 fun f =>
    (norm_indicator_toLp_le R hR f).trans_eq (one_mul _).symm

theorem indicatorL2_apply (R : Set α) (hR : MeasurableSet R) (f : Lp ℝ 2 ν) :
    indicatorL2 R hR f = ((Lp.memLp f).indicator hR.nullMeasurableSet).toLp (R.indicator (f : α → ℝ)) :=
  rfl

theorem indicatorL2_coeFn (R : Set α) (hR : MeasurableSet R) (f : Lp ℝ 2 ν) :
    (indicatorL2 R hR f : α → ℝ) =ᵐ[ν] R.indicator (f : α → ℝ) := by
  rw [indicatorL2_apply]
  exact MemLp.coeFn_toLp (f := R.indicator (f : α → ℝ)) _

end Generic

section Family
variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} {T : ℝ≥0}

/-- The raw enlarged predictable σ-algebra on `ℝ × DriverSample S κ`. -/
abbrev rawPredictable (S κ : Type*) [MeasurableSpace S] :
    MeasurableSpace (ℝ × DriverSample S κ) :=
  predictableSpace (enlargedPredictableFiltration (S := S) (κ := κ))

/-- The scalar predictable `L²(dt ⊗ driverLaw μ)` space on `(0,T]`. -/
abbrev ScalarPredictable (μ : Measure S) (T : ℝ≥0) :=
  PredictableL2 (enlargedPredictableFiltration (S := S) (κ := κ)) T (driverLaw (κ := κ) μ)

theorem indicator_mem_lpMeas (R : Set (ℝ × DriverSample S κ))
    (hR : MeasurableSet[rawPredictable S κ] R) (f : ScalarPredictable (κ := κ) μ T) :
    indicatorL2 R (predictableSpace_le _ R hR) (f : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ)))
      ∈ lpMeas ℝ ℝ (rawPredictable S κ) 2 (timeProbMeasure T (driverLaw (κ := κ) μ)) := by
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  obtain ⟨g, hg, hfg⟩ := lpMeas.aestronglyMeasurable f
  refine ⟨R.indicator g, hg.indicator hR, ?_⟩
  filter_upwards [indicatorL2_coeFn R (predictableSpace_le _ R hR)
    (f : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))), hfg] with x hx hx'
  rw [hx]
  by_cases hxR : x ∈ R
  · simp only [Set.indicator_of_mem hxR, hx']
  · simp only [Set.indicator_of_notMem hxR]

/-- Multiplication by `1_R` for a raw predictable set `R`, on scalar predictable `L²`. -/
def indicatorScalar (R : Set (ℝ × DriverSample S κ))
    (hR : MeasurableSet[rawPredictable S κ] R) :
    ScalarPredictable (κ := κ) μ T →L[ℝ] ScalarPredictable (κ := κ) μ T :=
  ((indicatorL2 R (predictableSpace_le _ R hR)).comp
    (lpMeas ℝ ℝ (rawPredictable S κ) 2 (timeProbMeasure T (driverLaw (κ := κ) μ))).subtypeL).codRestrict
    _ (indicator_mem_lpMeas R hR)

theorem indicatorScalar_coeFn (R : Set (ℝ × DriverSample S κ))
    (hR : MeasurableSet[rawPredictable S κ] R) (f : ScalarPredictable (κ := κ) μ T) :
    (((indicatorScalar R hR f : ScalarPredictable (κ := κ) μ T) :
      Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) : ℝ × DriverSample S κ → ℝ)
      =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)]
      R.indicator ((f : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) :
        ℝ × DriverSample S κ → ℝ) :=
  indicatorL2_coeFn R (predictableSpace_le _ R hR) _

/-- Coordinatewise multiplication by the indicator of a raw predictable set on the predictable
`L²(dt ⊗ driverLaw μ)` family on `(0,T]`. -/
def indicatorFamily (R : Set (ℝ × DriverSample S κ)) (hR : MeasurableSet[rawPredictable S κ] R) :
    PredictableFamily (S := S) (κ := κ) (μ := μ) T →L[ℝ]
      PredictableFamily (S := S) (κ := κ) (μ := μ) T :=
  (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a =>
      (indicatorScalar R hR).comp
        (PiLp.proj 2 (fun _ : κ => ScalarPredictable (κ := κ) μ T) a))

theorem indicatorFamily_apply (R : Set (ℝ × DriverSample S κ))
    (hR : MeasurableSet[rawPredictable S κ] R)
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) (a : κ) :
    indicatorFamily R hR f a = indicatorScalar R hR (f a) := rfl

end Family
end BlockBand.SourceProcess.Stochastic.Integral
