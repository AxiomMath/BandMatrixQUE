module
public import BlockBand.SourceProcess.Stochastic.Integral.MultiplierOperator
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Bounded adapted multipliers

Measure `driverLaw μ` on the sample space, `dt ⊗ driverLaw μ` on `(0,T]` for integrands, raw
filtration `F` (and its augmentation `F_t ∨ N`). For `a ≤ b`, a bounded (`|H| ≤ C`)
`F_a`-measurable real `H` and an integrand `g` with draft continuous representative
`X = nativeAdaptedLimit μ T hg.family`, the product `H · 1_{(a,b]} · g`
(`multiplierIntegrand a b H g`) is an integrand and

  `I_T(H 1_{(a,b]} g) = H (X_b − X_a)`   `driverLaw μ`-a.s.

(`nativeIntegralOf_multiplier`; augmented `H`: `nativeIntegralOf_multiplier_aug`). No bound on
`a, b` relative to `T` is needed (`X` is constant after `T`).

Proof: both sides are continuous linear in the predictable family (left: the sup-norm
multiplier `mulFamily`; right: `processL2` and `mulL2 H`); on single-direction rectangles
`1_{(s,t]} K e_c` they agree by `fullNativeIntegral_rectangle` and
`condExp_rectangle_increment`, so `family_clm_ext` concludes.
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open PredictableRectangle

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]

section Congr
variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}

omit [IsProbabilityMeasure μ] in
/-- Integrands are stable under coordinatewise `dt ⊗ driverLaw μ`-a.e. equality. -/
theorem NativeIntegrand.congr {G G' : κ → ℝ × DriverSample S κ → ℝ} (hG : NativeIntegrand μ T G)
    (h : ∀ c, G c =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)] G' c) :
    NativeIntegrand μ T G' := fun c => ⟨(hG c).1.congr (h c), (hG c).2.ae_eq (h c)⟩

omit [IsProbabilityMeasure μ] in
/-- A.e. equal integrands have the same predictable family. -/
theorem NativeIntegrand.family_congr {G G' : κ → ℝ × DriverSample S κ → ℝ}
    (hG : NativeIntegrand μ T G) (hG' : NativeIntegrand μ T G')
    (h : ∀ c, G c =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)] G' c) :
    hG.family = hG'.family := by
  obtain ⟨_, he⟩ := nativeIntegrand_of_family hG'.family
    (fun c => (nativeIntegrand_family_coeFn hG' c).trans (h c).symm)
  exact he

theorem nativeIntegralOf_congr {G G' : κ → ℝ × DriverSample S κ → ℝ}
    (hG : NativeIntegrand μ T G) (hG' : NativeIntegrand μ T G')
    (h : ∀ c, G c =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)] G' c) :
    nativeIntegralOf hG = nativeIntegralOf hG' := by
  unfold nativeIntegralOf
  rw [NativeIntegrand.family_congr hG hG' h]

end Congr

variable (μ : Measure S) [IsProbabilityMeasure μ] (T : ℝ≥0)

/-- The integrand `H · 1_{(a,b]} · g`. -/
def multiplierIntegrand (a b : ℝ≥0) (H : DriverSample S κ → ℝ)
    (g : κ → ℝ × DriverSample S κ → ℝ) : κ → ℝ × DriverSample S κ → ℝ :=
  fun c p => coefficientRectangle a b H p * g c p

omit [IsProbabilityMeasure μ] in
theorem coefficientRectangle_aesm {a b : ℝ≥0} {H : DriverSample S κ → ℝ}
    (hH : Measurable[commonWienerFiltration S κ a] H) :
    AEStronglyMeasurable[rawPredictable S κ] (coefficientRectangle a b H)
      (timeProbMeasure T (driverLaw (κ := κ) μ)) :=
  (stronglyMeasurable_coefficientRectangle enlargedPredictableFiltration hH).aestronglyMeasurable

omit [MeasurableSpace S] [Fintype κ] in
theorem abs_coefficientRectangle_le {H : DriverSample S κ → ℝ} {C : ℝ} (hC : ∀ x, |H x| ≤ C)
    (a b : ℝ≥0) (p : ℝ × DriverSample S κ) : |coefficientRectangle a b H p| ≤ C := by
  unfold coefficientRectangle
  by_cases hp : p ∈ Set.Ioc (a : ℝ) (b : ℝ) ×ˢ (Set.univ : Set (DriverSample S κ))
  · rw [Set.indicator_of_mem hp]
    exact hC p.2
  · rw [Set.indicator_of_notMem hp, abs_zero]
    exact (abs_nonneg _).trans (hC p.2)

omit [MeasurableSpace S] [Fintype κ] in
theorem coefficientRectangle_mul (a b s t : ℝ≥0) (H K : DriverSample S κ → ℝ)
    (p : ℝ × DriverSample S κ) :
    coefficientRectangle a b H p * coefficientRectangle s t K p =
      coefficientRectangle (max s a) (min t b) (fun x => H x * K x) p := by
  have hmem : p.1 ∈ Set.Ioc ((max s a : ℝ≥0) : ℝ) ((min t b : ℝ≥0) : ℝ) ↔
      p.1 ∈ Set.Ioc (s : ℝ) (t : ℝ) ∧ p.1 ∈ Set.Ioc (a : ℝ) (b : ℝ) := by
    simp only [Set.mem_Ioc, NNReal.coe_max, NNReal.coe_min, max_lt_iff, le_min_iff]
    tauto
  classical
  simp only [coefficientRectangle, Set.indicator_apply, Set.mem_prod, Set.mem_univ, and_true]
  by_cases h1 : p.1 ∈ Set.Ioc (s : ℝ) (t : ℝ)
  · by_cases h2 : p.1 ∈ Set.Ioc (a : ℝ) (b : ℝ)
    · simp only [h1, h2, hmem.2 ⟨h1, h2⟩, ite_true]
    · have h3 : p.1 ∉ Set.Ioc ((max s a : ℝ≥0) : ℝ) ((min t b : ℝ≥0) : ℝ) :=
        fun h => h2 (hmem.1 h).2
      simp only [h1, h2, h3, ite_true, ite_false, zero_mul]
  · have h3 : p.1 ∉ Set.Ioc ((max s a : ℝ≥0) : ℝ) ((min t b : ℝ≥0) : ℝ) :=
      fun h => h1 (hmem.1 h).1
    simp only [h1, h3, ite_false, mul_zero]

theorem mulScalar_rectangle {a b s t : ℝ≥0} {H : DriverSample S κ → ℝ}
    (hH : Measurable[commonWienerFiltration S κ a] H) {C : ℝ} (hC : ∀ x, |H x| ≤ C)
    {K : DriverSample S κ → ℝ} (hK : Measurable[commonWienerFiltration S κ s] K)
    (hKL2 : MemLp K 2 (driverLaw (κ := κ) μ)) :
    mulScalar (μ := μ) (T := T) (coefficientRectangle a b H) (coefficientRectangle_aesm μ T hH) C
        (abs_coefficientRectangle_le hC a b)
        (coefficientRectanglePredictableL2 enlargedPredictableFiltration T
          (driverLaw (κ := κ) μ) (s := s) (t := t) K hK hKL2) =
      coefficientRectanglePredictableL2 enlargedPredictableFiltration T
        (driverLaw (κ := κ) μ) (s := max s a) (t := min t b) (fun x => H x * K x)
        ((hH.mono ((commonWienerFiltration S κ).mono (le_max_right s a)) le_rfl).mul
          (hK.mono ((commonWienerFiltration S κ).mono (le_max_left s a)) le_rfl))
        (memLp_mul_of_bound (hH.mono ((commonWienerFiltration S κ).le a) le_rfl).aestronglyMeasurable
          hC hKL2) := by
  apply (predictableL2_eq_iff_ae_eq _ _).2
  filter_upwards [mulScalar_coeFn (μ := μ) (T := T) _ (coefficientRectangle_aesm μ T hH) C
      (abs_coefficientRectangle_le hC a b)
      (coefficientRectanglePredictableL2 enlargedPredictableFiltration T
        (driverLaw (κ := κ) μ) (s := s) (t := t) K hK hKL2),
    coefficientRectangle_class_coeFn μ T (s := s) (t := t) K hK hKL2,
    coefficientRectangle_class_coeFn μ T (s := max s a) (t := min t b) (fun x => H x * K x)
      ((hH.mono ((commonWienerFiltration S κ).mono (le_max_right s a)) le_rfl).mul
        (hK.mono ((commonWienerFiltration S κ).mono (le_max_left s a)) le_rfl))
      (memLp_mul_of_bound (hH.mono ((commonWienerFiltration S κ).le a) le_rfl).aestronglyMeasurable
        hC hKL2)] with p h1 h2 h3
  rw [h1, h3, h2, coefficientRectangle_mul]

variable [DecidableEq κ]

/-- **Multiplier identity on predictable families.** For `a ≤ b` and a bounded
`F_a`-measurable `H`, `I_T(1_{(a,b]} H f) = H (X_b − X_a)` a.s., `X = nativeAdaptedLimit μ T f`. -/
theorem fullNativeIntegral_multiplier (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T)
    {a b : ℝ≥0} (hab : a ≤ b) {H : DriverSample S κ → ℝ}
    (hH : Measurable[commonWienerFiltration S κ a] H) {C : ℝ} (hC : ∀ x, |H x| ≤ C) :
    (fullNativeIntegral (κ := κ) μ T (mulFamily (coefficientRectangle a b H)
      (coefficientRectangle_aesm μ T hH) C (abs_coefficientRectangle_le hC a b) f) :
        DriverSample S κ → ℝ) =ᵐ[driverLaw (κ := κ) μ]
      fun x => H x * (nativeAdaptedLimit μ T f b x - nativeAdaptedLimit μ T f a x) := by
  have hHae : AEStronglyMeasurable H (driverLaw (κ := κ) μ) :=
    (hH.mono ((commonWienerFiltration S κ).le a) le_rfl).aestronglyMeasurable
  have hclm : (fullNativeIntegral (κ := κ) μ T).toContinuousLinearMap.comp
      (mulFamily (coefficientRectangle a b H) (coefficientRectangle_aesm μ T hH) C
        (abs_coefficientRectangle_le hC a b)) =
      (mulL2 H hHae C hC).comp (processL2 μ T b - processL2 μ T a) := by
    apply family_clm_ext μ T
    intro c s t hst htT K hK hKL2
    apply Lp.ext
    change (fullNativeIntegral (κ := κ) μ T (mulFamily _ _ C _ (PiLp.single 2 c _)) :
      DriverSample S κ → ℝ) =ᵐ[driverLaw (κ := κ) μ]
        (mulL2 H hHae C hC (processL2 μ T b (PiLp.single 2 c _) -
          processL2 μ T a (PiLp.single 2 c _)) : DriverSample S κ → ℝ)
    rw [mulFamily_single, mulScalar_rectangle μ T hH hC hK hKL2]
    have hrect := fullNativeIntegral_rectangle_lt μ T s t hst htT c K hK hKL2
    filter_upwards [fullNativeIntegral_rectangle μ T (max s a) (min t b)
        ((min_le_left t b).trans htT) c (fun x => H x * K x)
        ((hH.mono ((commonWienerFiltration S κ).mono (le_max_right s a)) le_rfl).mul
          (hK.mono ((commonWienerFiltration S κ).mono (le_max_left s a)) le_rfl))
        (memLp_mul_of_bound hHae hC hKL2),
      mulL2_coeFn H hHae C hC (processL2 μ T b (rectFamily μ T t c K hK hKL2) -
        processL2 μ T a (rectFamily μ T t c K hK hKL2)),
      Lp.coeFn_sub (processL2 μ T b (rectFamily μ T t c K hK hKL2))
        (processL2 μ T a (rectFamily μ T t c K hK hKL2)),
      processL2_coeFn μ T b (rectFamily μ T t c K hK hKL2),
      processL2_coeFn μ T a (rectFamily μ T t c K hK hKL2),
      condExp_congr_ae (m := commonWienerFiltration S κ (min b T)) hrect,
      condExp_congr_ae (m := commonWienerFiltration S κ (min a T)) hrect,
      condExp_rectangle_increment μ c hst.le hK hKL2 (min b T),
      condExp_rectangle_increment μ c hst.le hK hKL2 (min a T)]
      with x h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [h1, h2, h3, Pi.sub_apply, h4, h5, h6, h7, h8, h9]
    have ht := rectangle_time_identity T hst htT hab (fun r => commonRealBrownian r x c)
    linear_combination (H x * K x) * ht
  have hf := congrArg (fun L => (L f : DriverSample S κ → ℝ)) hclm
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    sub_apply] at hf
  rw [hf]
  filter_upwards [mulL2_coeFn H hHae C hC (processL2 μ T b f - processL2 μ T a f),
    Lp.coeFn_sub (processL2 μ T b f) (processL2 μ T a f),
    nativeAdaptedLimit_ae_processL2 μ T f b, nativeAdaptedLimit_ae_processL2 μ T f a]
    with x h1 h2 h3 h4
  rw [h1, h2, Pi.sub_apply, h3, h4]

variable {μ T}

omit [IsProbabilityMeasure μ] [DecidableEq κ] in
/-- `H · 1_{(a,b]} · g` is an integrand for bounded raw `F_a`-measurable `H`. -/
theorem multiplier_nativeIntegrand {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) {a b : ℝ≥0} {H : DriverSample S κ → ℝ}
    (hH : Measurable[commonWienerFiltration S κ a] H) {C : ℝ} (hC : ∀ x, |H x| ≤ C) :
    NativeIntegrand μ T (multiplierIntegrand a b H g) := fun c =>
  ⟨(coefficientRectangle_aesm μ T hH).mul (hg c).1,
    memLp_mul_of_bound ((coefficientRectangle_aesm μ T hH).mono (predictableSpace_le _))
      (abs_coefficientRectangle_le hC a b) (hg c).2⟩

omit [IsProbabilityMeasure μ] [DecidableEq κ] in
theorem multiplier_family {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) {a b : ℝ≥0} {H : DriverSample S κ → ℝ}
    (hH : Measurable[commonWienerFiltration S κ a] H) {C : ℝ} (hC : ∀ x, |H x| ≤ C)
    (hs : NativeIntegrand μ T (multiplierIntegrand a b H g)) :
    hs.family = mulFamily (coefficientRectangle a b H) (coefficientRectangle_aesm μ T hH) C
      (abs_coefficientRectangle_le hC a b) hg.family := by
  obtain ⟨_, he⟩ := nativeIntegrand_of_family (G := multiplierIntegrand a b H g)
    (mulFamily (coefficientRectangle a b H) (coefficientRectangle_aesm μ T hH) C
      (abs_coefficientRectangle_le hC a b) hg.family) (fun c => by
        rw [mulFamily_apply]
        filter_upwards [mulScalar_coeFn _ (coefficientRectangle_aesm μ T hH) C
          (abs_coefficientRectangle_le hC a b) (hg.family c),
          nativeIntegrand_family_coeFn hg c] with p h1 h2
        rw [h1, h2]
        rfl)
  exact he

/-- **Multiplier identity (raw `H`).** For `a ≤ b`, bounded raw `F_a`-measurable `H` and a native
integrand `g`, `I_T(H 1_{(a,b]} g) = H (X_b − X_a)` a.s., `X = nativeAdaptedLimit μ T hg.family`. -/
theorem nativeIntegralOf_multiplier {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) {a b : ℝ≥0} (hab : a ≤ b) {H : DriverSample S κ → ℝ}
    (hH : Measurable[commonWienerFiltration S κ a] H) {C : ℝ} (hC : ∀ x, |H x| ≤ C)
    (hs : NativeIntegrand μ T (multiplierIntegrand a b H g)) :
    (nativeIntegralOf hs : DriverSample S κ → ℝ) =ᵐ[driverLaw (κ := κ) μ]
      fun x => H x * (nativeAdaptedLimit μ T hg.family b x -
        nativeAdaptedLimit μ T hg.family a x) := by
  unfold nativeIntegralOf
  rw [multiplier_family hg hH hC hs]
  exact fullNativeIntegral_multiplier μ T hg.family hab hH hC

omit [DecidableEq κ] in
/-- `H · 1_{(a,b]} · g` is an integrand for bounded augmented `F_a ∨ N`-measurable `H`. -/
theorem multiplier_nativeIntegrand_aug {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) {a b : ℝ≥0} {H : DriverSample S κ → ℝ}
    (hH : StronglyMeasurable[driverAugmented (κ := κ) μ a] H) {C : ℝ} (hC : ∀ x, |H x| ≤ C) :
    NativeIntegrand μ T (multiplierIntegrand a b H g) := by
  obtain ⟨H', hH', hC', hHH'⟩ := exists_raw_bounded_version μ hH hC
  refine NativeIntegrand.congr (multiplier_nativeIntegrand hg hH' hC' (a := a) (b := b))
    fun c => ?_
  filter_upwards [ae_timeProb_of_ae (T := T) hHH'] with p hp
  simp only [multiplierIntegrand, coefficientRectangle, Set.indicator_apply, hp]

/-- **Multiplier identity (augmented `H`).** As `nativeIntegralOf_multiplier`, for a bounded
`F_a ∨ N`-measurable `H`. -/
theorem nativeIntegralOf_multiplier_aug {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) {a b : ℝ≥0} (hab : a ≤ b) {H : DriverSample S κ → ℝ}
    (hH : StronglyMeasurable[driverAugmented (κ := κ) μ a] H) {C : ℝ} (hC : ∀ x, |H x| ≤ C)
    (hs : NativeIntegrand μ T (multiplierIntegrand a b H g)) :
    (nativeIntegralOf hs : DriverSample S κ → ℝ) =ᵐ[driverLaw (κ := κ) μ]
      fun x => H x * (nativeAdaptedLimit μ T hg.family b x -
        nativeAdaptedLimit μ T hg.family a x) := by
  obtain ⟨H', hH', hC', hHH'⟩ := exists_raw_bounded_version μ hH hC
  have hs' := multiplier_nativeIntegrand hg hH' hC' (a := a) (b := b)
  have he : nativeIntegralOf hs = nativeIntegralOf hs' := by
    apply nativeIntegralOf_congr
    intro c
    filter_upwards [ae_timeProb_of_ae (T := T) hHH'] with p hp
    simp only [multiplierIntegrand, coefficientRectangle, Set.indicator_apply, hp]
  rw [he]
  filter_upwards [nativeIntegralOf_multiplier hg hab hH' hC' hs', hHH'] with x h1 h2
  rw [h1, h2]

end BlockBand.SourceProcess.Stochastic.Integral
