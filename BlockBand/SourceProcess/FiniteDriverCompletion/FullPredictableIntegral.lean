module
public import BlockBand.SourceProcess.FiniteDriverCompletion.RectangleGridRealization

/-!
# Predictable rectangles as finite-grid classes

Each bounded-horizon rectangle `(s,t] × H` with `H` square integrable and measurable at time `s`,
in one noise direction, is a finite-grid predictable class; `nativeCoordinateEmbedding` places a
scalar predictable function in one coordinate of the predictable family.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open PredictableRectangle
variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ] (T : ℝ≥0)
variable [DecidableEq κ]
abbrev NativeScalarPredictable := PredictableL2
  (enlargedPredictableFiltration (S := S) (κ := κ)) T (driverLaw (κ := κ) μ)

omit [DecidableEq κ] in
/-- The time-probability law is supported on the time horizon `[0, T]`. -/
theorem timeProbMeasure_horizon : ∀ᵐ x ∂timeProbMeasure T (driverLaw (κ := κ) μ),
    x.1 ∈ Set.Ioc (0 : ℝ) (T : ℝ) := by
  unfold timeProbMeasure
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact Eventually.of_forall (fun _ => ht)

omit [DecidableEq κ] in
/-- The canonical representative of a coefficient rectangle. -/
theorem coefficientRectangle_class_coeFn {s t : ℝ≥0} (H : DriverSample S κ → ℝ)
    (hH : Measurable[commonWienerFiltration S κ s] H)
    (hHL2 : MemLp H 2 (driverLaw (κ := κ) μ)) :
    (((coefficientRectanglePredictableL2 enlargedPredictableFiltration T
      (driverLaw (κ := κ) μ) (s := s) (t := t) H hH hHL2 :
      NativeScalarPredictable (κ := κ) μ T) :
      Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) :
      ℝ × DriverSample S κ → ℝ) =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)]
      coefficientRectangle s t H :=
  (memLp_coefficientRectangle T s t hHL2).coeFn_toLp

/-- Each bounded-horizon rectangle in each noise direction is a finite-grid class. -/
theorem rectangle_single_mem_nativeFinite (s t : ℝ≥0) (hst : s < t) (htT : t ≤ T)
    (a : κ) (H : DriverSample S κ → ℝ)
    (hH : Measurable[commonWienerFiltration S κ s] H)
    (hHL2 : MemLp H 2 (driverLaw (κ := κ) μ)) :
    PiLp.single 2 a (coefficientRectanglePredictableL2 enlargedPredictableFiltration T
      (driverLaw (κ := κ) μ) (s := s) (t := t) H hH hHL2) ∈
      nativeFinitePredictable (κ := κ) μ T := by
  classical
  rcases exists_rectangle_presentation μ T s t hst htT a H hH hHL2 with ⟨d, hd⟩
  have he : d.predictableFamily = PiLp.single 2 a
      (coefficientRectanglePredictableL2 enlargedPredictableFiltration T
        (driverLaw (κ := κ) μ) (s := s) (t := t) H hH hHL2) := by
    apply PiLp.ext
    intro b
    change d.scalarPredictable b = _
    by_cases hb : b = a
    · subst b
      rw [PiLp.single_eq_same]
      apply (predictableL2_eq_iff_ae_eq _ _).2
      filter_upwards [d.scalarPredictable_coeFn a,
        coefficientRectangle_class_coeFn μ T H hH hHL2] with x hx hy
      rw [hx, hy, hd, ite_eq_left rfl]
    · rw [PiLp.single_eq_of_ne 2 hb]
      apply (predictableL2_eq_iff_ae_eq _ _).2
      filter_upwards [d.scalarPredictable_coeFn b,
        (Lp.coeFn_zero ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ)))] with x hx hy
      rw [hx, hd, ite_eq_right hb]
      exact hy.symm
  rw [← he]
  exact (nativePresentationClass μ T d).property

/-- The embedding of one coordinate into the predictable family. -/
def nativeCoordinateEmbedding (a : κ) : NativeScalarPredictable (κ := κ) μ T →ₗᵢ[ℝ]
    PredictableFamily (S := S) (κ := κ) (μ := μ) T where
  toFun f := PiLp.single 2 a f
  map_add' f g := PiLp.single_add 2 a
  map_smul' c f := by
    classical
    apply PiLp.ext
    intro b
    by_cases hb : b = a
    · subst b
      simp
    · simp [PiLp.smul_apply]
  norm_map' f := PiLp.norm_single 2 (fun _ : κ => NativeScalarPredictable (κ := κ) μ T) a f

end BlockBand.SourceProcess.FiniteDriverCompletion
