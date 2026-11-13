module
public import BlockBand.SourceProcess.Stochastic.Integral.Projection
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Integral over an adapted stochastic rectangle

Measure `driverLaw μ`, raw filtration `F`, integrand space `PredictableFamily T`
(`L²(dt ⊗ driverLaw μ)` on `(0,T]`). For `a ≤ b`, `B ∈ F_a` and every predictable family `f`,
writing `X = nativeAdaptedLimit μ T f` for the draft continuous representative,

  `I_T (1_{(a,b] × B} f) = 1_B (X_b − X_a)`   almost surely.

Proof: both sides are continuous linear in `f` (the right side through the projections
`processL2`), so by `family_clm_ext` it suffices to check single-direction rectangles, where
both sides are computed explicitly (`fullNativeIntegral_rectangle`,
`condExp_rectangle_increment`).
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open PredictableRectangle

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ] (T : ℝ≥0)

/-- Deterministic time bookkeeping behind the rectangle identity. -/
theorem rectangle_time_identity {s t a b : ℝ≥0} (hst : s < t) (htT : t ≤ T) (hab : a ≤ b)
    (w : ℝ≥0 → ℝ) :
    w (max (max s a) (min t b)) - w (max s a) =
      (w (max s (min t (min b T))) - w s) - (w (max s (min t (min a T))) - w s) := by
  have hb : min t (min b T) = min t b := by
    rw [← min_assoc, min_eq_left ((min_le_left _ _).trans htT)]
  have ha : min t (min a T) = min t a := by
    rw [← min_assoc, min_eq_left ((min_le_left _ _).trans htT)]
  rw [hb, ha]
  by_cases hat : a < t
  · rw [min_eq_right hat.le, max_assoc, max_eq_right (le_min hat.le hab)]
    ring
  · have hta : t ≤ a := le_of_not_gt hat
    rw [min_eq_left hta, min_eq_left (hta.trans hab),
      max_eq_left (hta.trans (le_max_right s a)), max_eq_right hst.le]
    ring

omit [MeasurableSpace S] [Fintype κ] in
set_option linter.unusedSimpArgs false in
theorem coefficientRectangle_restrict (s t a b : ℝ≥0) (B : Set (DriverSample S κ))
    (H : DriverSample S κ → ℝ) (p : ℝ × DriverSample S κ) :
    (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ B).indicator (coefficientRectangle s t H) p =
      coefficientRectangle (max s a) (min t b) (B.indicator H) p := by
  have hmem : p.1 ∈ Set.Ioc ((max s a : ℝ≥0) : ℝ) ((min t b : ℝ≥0) : ℝ) ↔
      p.1 ∈ Set.Ioc (s : ℝ) (t : ℝ) ∧ p.1 ∈ Set.Ioc (a : ℝ) (b : ℝ) := by
    simp only [Set.mem_Ioc, NNReal.coe_max, NNReal.coe_min, max_lt_iff, le_min_iff]
    tauto
  classical
  simp only [coefficientRectangle, Set.indicator_apply, Set.mem_prod, Set.mem_univ, and_true]
  by_cases h1 : p.1 ∈ Set.Ioc (s : ℝ) (t : ℝ) <;> by_cases h2 : p.1 ∈ Set.Ioc (a : ℝ) (b : ℝ) <;>
    by_cases h3 : p.2 ∈ B <;>
    simp only [h1, h2, h3, hmem, and_true, and_false, true_and, false_and, ite_true, ite_false]

variable [DecidableEq κ]

omit [IsProbabilityMeasure μ] in
theorem indicatorFamily_single (R : Set (ℝ × DriverSample S κ))
    (hR : MeasurableSet[rawPredictable S κ] R) (c : κ) (g : ScalarPredictable (κ := κ) μ T) :
    indicatorFamily (μ := μ) (T := T) R hR (PiLp.single 2 c g) =
      PiLp.single 2 c (indicatorScalar R hR g) := by
  apply PiLp.ext
  intro b
  rw [indicatorFamily_apply]
  by_cases hb : b = c
  · subst hb
    simp only [PiLp.single_eq_same]
  · rw [PiLp.single_eq_of_ne 2 hb, PiLp.single_eq_of_ne 2 hb, map_zero]

omit [Fintype κ] [DecidableEq κ] in
theorem measurable_restrictCoeff {s a : ℝ≥0} {B : Set (DriverSample S κ)}
    (hB : MeasurableSet[commonWienerFiltration S κ a] B) {H : DriverSample S κ → ℝ}
    (hH : Measurable[commonWienerFiltration S κ s] H) :
    Measurable[commonWienerFiltration S κ (max s a)] (B.indicator H) :=
  (hH.mono ((commonWienerFiltration S κ).mono (le_max_left s a)) le_rfl).indicator
    ((commonWienerFiltration S κ).mono (le_max_right s a) B hB)

omit [DecidableEq κ] in
theorem indicatorScalar_rectangle {s t a b : ℝ≥0} {B : Set (DriverSample S κ)}
    (hB : MeasurableSet[commonWienerFiltration S κ a] B) {H : DriverSample S κ → ℝ}
    (hH : Measurable[commonWienerFiltration S κ s] H)
    (hHL2 : MemLp H 2 (driverLaw (κ := κ) μ)) :
    indicatorScalar (μ := μ) (T := T) (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ B)
        (measurableSet_predictableRectangle enlargedPredictableFiltration (t := b) hB)
        (coefficientRectanglePredictableL2 enlargedPredictableFiltration T
          (driverLaw (κ := κ) μ) (s := s) (t := t) H hH hHL2) =
      coefficientRectanglePredictableL2 enlargedPredictableFiltration T
        (driverLaw (κ := κ) μ) (s := max s a) (t := min t b) (B.indicator H)
        (measurable_restrictCoeff hB hH)
        (hHL2.indicator (((commonWienerFiltration S κ).le a B hB).nullMeasurableSet)) := by
  apply (predictableL2_eq_iff_ae_eq _ _).2
  filter_upwards [indicatorScalar_coeFn (μ := μ) (T := T) _
      (measurableSet_predictableRectangle enlargedPredictableFiltration (t := b) hB)
      (coefficientRectanglePredictableL2 enlargedPredictableFiltration T
        (driverLaw (κ := κ) μ) (s := s) (t := t) H hH hHL2),
    coefficientRectangle_class_coeFn μ T (s := s) (t := t) H hH hHL2,
    coefficientRectangle_class_coeFn μ T (s := max s a) (t := min t b) (B.indicator H)
      (measurable_restrictCoeff hB hH)
      (hHL2.indicator (((commonWienerFiltration S κ).le a B hB).nullMeasurableSet))]
    with p h1 h2 h3
  rw [h1, h3]
  have hind : (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ B).indicator
      (((coefficientRectanglePredictableL2 enlargedPredictableFiltration T
        (driverLaw (κ := κ) μ) (s := s) (t := t) H hH hHL2 : ScalarPredictable (κ := κ) μ T) :
          Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) : ℝ × DriverSample S κ → ℝ) p =
      (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ B).indicator (coefficientRectangle s t H) p := by
    by_cases hp : p ∈ Set.Ioc (a : ℝ) (b : ℝ) ×ˢ B
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, h2]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]
  rw [hind, coefficientRectangle_restrict]

/-- **Rectangle identity.** For `a ≤ b` and `B ∈ F_a`,
`I_T(1_{(a,b]×B} f) = 1_B (X_b − X_a)` a.s., `X = nativeAdaptedLimit μ T f`. -/
theorem fullNativeIntegral_indicator_rectangle
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) {a b : ℝ≥0} (hab : a ≤ b)
    {B : Set (DriverSample S κ)} (hB : MeasurableSet[commonWienerFiltration S κ a] B) :
    (fullNativeIntegral (κ := κ) μ T (indicatorFamily (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ B)
      (measurableSet_predictableRectangle enlargedPredictableFiltration (t := b) hB) f) :
        DriverSample S κ → ℝ) =ᵐ[driverLaw (κ := κ) μ]
      B.indicator (fun x => nativeAdaptedLimit μ T f b x - nativeAdaptedLimit μ T f a x) := by
  have hBm : MeasurableSet B := (commonWienerFiltration S κ).le a B hB
  have hclm : (fullNativeIntegral (κ := κ) μ T).toContinuousLinearMap.comp
      (indicatorFamily (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ B)
        (measurableSet_predictableRectangle enlargedPredictableFiltration (t := b) hB)) =
      (indicatorL2 B hBm).comp (processL2 μ T b - processL2 μ T a) := by
    apply family_clm_ext μ T
    intro c s t hst htT H hH hHL2
    apply Lp.ext
    change (fullNativeIntegral (κ := κ) μ T (indicatorFamily _ _ (PiLp.single 2 c _)) :
      DriverSample S κ → ℝ) =ᵐ[driverLaw (κ := κ) μ]
        (indicatorL2 B hBm (processL2 μ T b (PiLp.single 2 c _) -
          processL2 μ T a (PiLp.single 2 c _)) : DriverSample S κ → ℝ)
    rw [indicatorFamily_single, indicatorScalar_rectangle μ T hB hH hHL2]
    have hrect := fullNativeIntegral_rectangle_lt μ T s t hst htT c H hH hHL2
    filter_upwards [fullNativeIntegral_rectangle μ T (max s a) (min t b)
        ((min_le_left t b).trans htT) c (B.indicator H) (measurable_restrictCoeff hB hH)
        (hHL2.indicator hBm.nullMeasurableSet),
      indicatorL2_coeFn B hBm (processL2 μ T b (rectFamily μ T t c H hH hHL2) -
        processL2 μ T a (rectFamily μ T t c H hH hHL2)),
      Lp.coeFn_sub (processL2 μ T b (rectFamily μ T t c H hH hHL2))
        (processL2 μ T a (rectFamily μ T t c H hH hHL2)),
      processL2_coeFn μ T b (rectFamily μ T t c H hH hHL2),
      processL2_coeFn μ T a (rectFamily μ T t c H hH hHL2),
      condExp_congr_ae (m := commonWienerFiltration S κ (min b T)) hrect,
      condExp_congr_ae (m := commonWienerFiltration S κ (min a T)) hrect,
      condExp_rectangle_increment μ c hst.le hH hHL2 (min b T),
      condExp_rectangle_increment μ c hst.le hH hHL2 (min a T)]
      with x h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [h1, h2]
    by_cases hx : x ∈ B
    · simp only [Set.indicator_of_mem hx]
      rw [h3, Pi.sub_apply, h4, h5, h6, h7, h8, h9]
      have ht := rectangle_time_identity T hst htT hab (fun r => commonRealBrownian r x c)
      linear_combination (H x) * ht
    · simp only [Set.indicator_of_notMem hx, zero_mul]
  have hf := congrArg (fun L => (L f : DriverSample S κ → ℝ)) hclm
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    sub_apply] at hf
  rw [hf]
  filter_upwards [indicatorL2_coeFn B hBm (processL2 μ T b f - processL2 μ T a f),
    Lp.coeFn_sub (processL2 μ T b f) (processL2 μ T a f),
    nativeAdaptedLimit_ae_processL2 μ T f b, nativeAdaptedLimit_ae_processL2 μ T f a]
    with x h1 h2 h3 h4
  rw [h1]
  by_cases hx : x ∈ B
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, h2, Pi.sub_apply, h3, h4]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

end BlockBand.SourceProcess.Stochastic.Integral
