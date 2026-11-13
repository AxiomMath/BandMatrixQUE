module
public import BlockBand.SourceProcess.Stochastic.Integral.MultiplierStopped
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Horizon consistency of the integral

Sample space `Ω = DriverSample S κ`, `P = driverLaw μ`; integrands live in
`L²(timeProbMeasure T P)` (`dt ⊗ P` on `(0,T] × Ω`) and are a.e. raw predictable.

For `T ≤ T'` the window `(0,T] × Ω` carries `timeProbMeasure T P` as the restriction of
`timeProbMeasure T' P` (`timeProbMeasure_restrict_window`). Extension by zero is a
continuous linear map `extFamily` from the horizon-`T` predictable family to the horizon-`T'`
one, and `fullNativeIntegral T' ∘ extFamily = fullNativeIntegral T`
(`fullNativeIntegral_extFamily`: both agree on rectangles `1_{(s,t]} H e_a`, `t ≤ T`, and
`family_clm_ext` concludes).

Consequence used by the SDE layer (`nativeIntegralOf_horizon`): a horizon-`T'` native
integrand vanishing for times `> T` is a horizon-`T` integrand with the same integral.
-/

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral
open PredictableRectangle

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]

/-- The horizon window `(0,T] × Ω`. -/
abbrev window (S κ : Type*) [MeasurableSpace S] (T : ℝ≥0) : Set (ℝ × DriverSample S κ) :=
  Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ (Set.univ : Set (DriverSample S κ))

omit [Fintype κ] in
theorem measurableSet_window (T : ℝ≥0) : MeasurableSet (window S κ T) :=
  measurableSet_Ioc.prod MeasurableSet.univ

omit [Fintype κ] in
theorem measurableSet_window_pred (T : ℝ≥0) :
    MeasurableSet[rawPredictable S κ] (window S κ T) := by
  have h := measurableSet_predictableRectangle (enlargedPredictableFiltration (S := S) (κ := κ))
    (s := 0) (t := T) (A := Set.univ) MeasurableSet.univ
  simpa only [NNReal.coe_zero] using h

variable {T T' : ℝ≥0}

theorem timeProbMeasure_restrict_window (h : T ≤ T') :
    (timeProbMeasure T' (driverLaw (κ := κ) μ)).restrict (window S κ T) =
      timeProbMeasure T (driverLaw (κ := κ) μ) := by
  unfold timeProbMeasure window
  rw [← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_left.2 (Set.Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 h))]

theorem ae_window_of_ae (h : T ≤ T') {q : ℝ × DriverSample S κ → Prop}
    (hq : ∀ᵐ p ∂timeProbMeasure T (driverLaw (κ := κ) μ), q p) :
    ∀ᵐ p ∂timeProbMeasure T' (driverLaw (κ := κ) μ), p ∈ window S κ T → q p := by
  rw [← timeProbMeasure_restrict_window h] at hq
  exact (ae_restrict_iff' (measurableSet_window T)).1 hq

theorem timeProbMeasure_le_of_le (h : T ≤ T') :
    timeProbMeasure T (driverLaw (κ := κ) μ) ≤ timeProbMeasure T' (driverLaw (κ := κ) μ) := by
  rw [← timeProbMeasure_restrict_window h]
  exact Measure.restrict_le_self

/-- Representative of the extension by zero of a horizon-`T` class. -/
abbrev extRep (f : ScalarPredictable (κ := κ) μ T) : ℝ × DriverSample S κ → ℝ :=
  (window S κ T).indicator ((f : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) :
    ℝ × DriverSample S κ → ℝ)

theorem memLp_extRep (h : T ≤ T') (f : ScalarPredictable (κ := κ) μ T) :
    MemLp (extRep f) 2 (timeProbMeasure T' (driverLaw (κ := κ) μ)) := by
  rw [memLp_indicator_iff_restrict (measurableSet_window T).nullMeasurableSet,
    timeProbMeasure_restrict_window h]
  exact Lp.memLp _

theorem aesm_extRep (h : T ≤ T') (f : ScalarPredictable (κ := κ) μ T) :
    AEStronglyMeasurable[rawPredictable S κ] (extRep f)
      (timeProbMeasure T' (driverLaw (κ := κ) μ)) := by
  obtain ⟨g, hg, hfg⟩ := lpMeas.aestronglyMeasurable f
  refine ⟨(window S κ T).indicator g, hg.indicator (measurableSet_window_pred T), ?_⟩
  filter_upwards [ae_window_of_ae h hfg] with p hp
  by_cases hw : p ∈ window S κ T
  · simp only [extRep, Set.indicator_of_mem hw, hp hw]
  · simp only [extRep, Set.indicator_of_notMem hw]

/-- Extension by zero of one scalar coordinate (as a function). -/
def extScalarFun (h : T ≤ T') (f : ScalarPredictable (κ := κ) μ T) :
    ScalarPredictable (κ := κ) μ T' :=
  ⟨(memLp_extRep h f).toLp _, mem_lpMeas_iff_aestronglyMeasurable.2
    ((aesm_extRep h f).congr (memLp_extRep h f).coeFn_toLp.symm)⟩

theorem extScalarFun_coeFn (h : T ≤ T') (f : ScalarPredictable (κ := κ) μ T) :
    (((extScalarFun h f : ScalarPredictable (κ := κ) μ T') :
      Lp ℝ 2 (timeProbMeasure T' (driverLaw (κ := κ) μ))) : ℝ × DriverSample S κ → ℝ)
      =ᵐ[timeProbMeasure T' (driverLaw (κ := κ) μ)] extRep f :=
  (memLp_extRep h f).coeFn_toLp

theorem norm_extScalarFun (h : T ≤ T') (f : ScalarPredictable (κ := κ) μ T) :
    ‖extScalarFun h f‖ = ‖f‖ := by
  change ‖(memLp_extRep h f).toLp (extRep f)‖ =
    ‖(f : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ)))‖
  rw [Lp.norm_toLp, Lp.norm_def, extRep,
    eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_window T).nullMeasurableSet,
    timeProbMeasure_restrict_window h]

/-- Extension by zero of one scalar coordinate, `L²(dt ⊗ P; (0,T]) → L²(dt ⊗ P; (0,T'])`. -/
def extScalar (h : T ≤ T') :
    ScalarPredictable (κ := κ) μ T →L[ℝ] ScalarPredictable (κ := κ) μ T' :=
  LinearMap.mkContinuous
    { toFun := extScalarFun h
      map_add' := fun f g => by
        apply (predictableL2_eq_iff_ae_eq _ _).2
        have hfg : (((f + g : ScalarPredictable (κ := κ) μ T) :
            Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) : ℝ × DriverSample S κ → ℝ)
            =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)] fun p =>
              ((f : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) : _ → ℝ) p +
              ((g : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) : _ → ℝ) p :=
          Lp.coeFn_add _ _
        filter_upwards [extScalarFun_coeFn h (f + g), extScalarFun_coeFn h f,
          extScalarFun_coeFn h g, ae_window_of_ae h hfg,
          Lp.coeFn_add ((extScalarFun h f : ScalarPredictable (κ := κ) μ T') :
            Lp ℝ 2 (timeProbMeasure T' (driverLaw (κ := κ) μ)))
            ((extScalarFun h g : ScalarPredictable (κ := κ) μ T') :
            Lp ℝ 2 (timeProbMeasure T' (driverLaw (κ := κ) μ)))] with p h1 h2 h3 h4 h5
        change _ = (((extScalarFun h f : ScalarPredictable (κ := κ) μ T') :
            Lp ℝ 2 (timeProbMeasure T' (driverLaw (κ := κ) μ))) +
          ((extScalarFun h g : ScalarPredictable (κ := κ) μ T') :
            Lp ℝ 2 (timeProbMeasure T' (driverLaw (κ := κ) μ))) : _ → ℝ) p
        rw [h5, Pi.add_apply, h1, h2, h3]
        by_cases hw : p ∈ window S κ T
        · simp only [extRep, Set.indicator_of_mem hw, h4 hw]
        · simp only [extRep, Set.indicator_of_notMem hw, add_zero]
      map_smul' := fun c f => by
        apply (predictableL2_eq_iff_ae_eq _ _).2
        have hcf : (((c • f : ScalarPredictable (κ := κ) μ T) :
            Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) : ℝ × DriverSample S κ → ℝ)
            =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)] fun p =>
              c • ((f : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) : _ → ℝ) p :=
          Lp.coeFn_smul _ _
        filter_upwards [extScalarFun_coeFn h (c • f), extScalarFun_coeFn h f,
          ae_window_of_ae h hcf,
          Lp.coeFn_smul c ((extScalarFun h f : ScalarPredictable (κ := κ) μ T') :
            Lp ℝ 2 (timeProbMeasure T' (driverLaw (κ := κ) μ)))] with p h1 h2 h4 h5
        change _ = (c • ((extScalarFun h f : ScalarPredictable (κ := κ) μ T') :
            Lp ℝ 2 (timeProbMeasure T' (driverLaw (κ := κ) μ))) : _ → ℝ) p
        rw [h5, Pi.smul_apply, h1, h2]
        by_cases hw : p ∈ window S κ T
        · simp only [extRep, Set.indicator_of_mem hw, h4 hw]
        · simp only [extRep, Set.indicator_of_notMem hw, smul_zero] }
    1 fun f => by
      rw [one_mul]
      exact (norm_extScalarFun h f).le

theorem extScalar_apply (h : T ≤ T') (f : ScalarPredictable (κ := κ) μ T) :
    extScalar h f = extScalarFun h f := rfl

/-- Coordinatewise extension by zero of predictable families. -/
def extFamily (h : T ≤ T') :
    PredictableFamily (S := S) (κ := κ) (μ := μ) T →L[ℝ]
      PredictableFamily (S := S) (κ := κ) (μ := μ) T' :=
  LinearMap.mkContinuous
    { toFun := fun f => WithLp.toLp 2 fun a => extScalar h (f a)
      map_add' := fun f g => by
        apply PiLp.ext
        intro a
        simp only [PiLp.add_apply, map_add]
      map_smul' := fun c f => by
        apply PiLp.ext
        intro a
        simp only [PiLp.smul_apply, map_smul, RingHom.id_apply] }
    1 fun f => by
      rw [one_mul]
      apply le_of_eq
      change ‖(WithLp.toLp 2 fun a => extScalar h (f a) :
        PredictableFamily (S := S) (κ := κ) (μ := μ) T')‖ = ‖f‖
      rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [PiLp.toLp_apply, extScalar_apply, norm_extScalarFun]

theorem extFamily_apply (h : T ≤ T') (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T)
    (a : κ) : extFamily h f a = extScalar h (f a) := rfl

theorem extFamily_rectFamily [DecidableEq κ] (h : T ≤ T') {s t : ℝ≥0} (htT : t ≤ T) (a : κ)
    (H : DriverSample S κ → ℝ) (hH : Measurable[commonWienerFiltration S κ s] H)
    (hHL2 : MemLp H 2 (driverLaw (κ := κ) μ)) :
    extFamily h (rectFamily μ T t a H hH hHL2) = rectFamily μ T' t a H hH hHL2 := by
  apply PiLp.ext
  intro b
  rw [extFamily_apply]
  by_cases hb : b = a
  · subst hb
    simp only [rectFamily, PiLp.single_eq_same]
    apply (predictableL2_eq_iff_ae_eq _ _).2
    filter_upwards [extScalarFun_coeFn h (coefficientRectanglePredictableL2
        enlargedPredictableFiltration T (driverLaw (κ := κ) μ) (s := s) (t := t) H hH hHL2),
      ae_window_of_ae h (coefficientRectangle_class_coeFn μ T (s := s) (t := t) H hH hHL2),
      coefficientRectangle_class_coeFn μ T' (s := s) (t := t) H hH hHL2] with p h1 h2 h3
    rw [extScalar_apply, h1, h3]
    by_cases hw : p ∈ window S κ T
    · simp only [extRep, Set.indicator_of_mem hw, h2 hw]
    · simp only [extRep, Set.indicator_of_notMem hw]
      have hn : p ∉ Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (Set.univ : Set (DriverSample S κ)) := by
        intro hp
        apply hw
        refine ⟨⟨(NNReal.coe_nonneg s).trans_lt hp.1.1, hp.1.2.trans ?_⟩, Set.mem_univ _⟩
        exact_mod_cast htT
      simp only [coefficientRectangle, Set.indicator_of_notMem hn]
  · simp only [rectFamily, PiLp.single_eq_of_ne 2 hb, map_zero]

/-- **Horizon consistency.** Extending by zero from `(0,T]` to `(0,T']` does not change the
terminal integral. -/
theorem fullNativeIntegral_extFamily (h : T ≤ T') :
    (fullNativeIntegral (κ := κ) μ T').toContinuousLinearMap.comp (extFamily h) =
      (fullNativeIntegral (κ := κ) μ T).toContinuousLinearMap := by
  classical
  apply family_clm_ext μ T
  intro a s t hst htT H hH hHL2
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [extFamily_rectFamily h htT]
  apply Lp.ext
  filter_upwards [fullNativeIntegral_rectangle_lt μ T' s t hst (htT.trans h) a H hH hHL2,
    fullNativeIntegral_rectangle_lt μ T s t hst htT a H hH hHL2] with x h1 h2
  rw [h1, h2]

/-- A horizon-`T'` integrand vanishing at times `> T` is a horizon-`T` integrand
with the same terminal integral. -/
theorem nativeIntegralOf_horizon (h : T ≤ T') {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg' : NativeIntegrand μ T' g) (hsupp : ∀ c p, (T : ℝ) < p.1 → g c p = 0) :
    ∃ hg : NativeIntegrand μ T g, nativeIntegralOf hg = nativeIntegralOf hg' := by
  have hg : NativeIntegrand μ T g := fun c =>
    ⟨(hg' c).1.mono_measure (timeProbMeasure_le_of_le h),
      (hg' c).2.mono_measure (timeProbMeasure_le_of_le h)⟩
  refine ⟨hg, ?_⟩
  have hfam : extFamily h hg.family = hg'.family := by
    apply PiLp.ext
    intro c
    rw [extFamily_apply]
    apply (predictableL2_eq_iff_ae_eq _ _).2
    filter_upwards [extScalarFun_coeFn h (hg.family c),
      ae_window_of_ae h (nativeIntegrand_family_coeFn hg c), nativeIntegrand_family_coeFn hg' c,
      timeProbMeasure_horizon (κ := κ) μ T'] with p h1 h2 h3 h4
    rw [extScalar_apply, h1, h3]
    by_cases hw : p ∈ window S κ T
    · simp only [extRep, Set.indicator_of_mem hw, h2 hw]
    · simp only [extRep, Set.indicator_of_notMem hw]
      refine (hsupp c p ?_).symm
      by_contra hle
      exact hw ⟨⟨h4.1, le_of_not_gt hle⟩, Set.mem_univ _⟩
  unfold nativeIntegralOf
  rw [← hfam]
  exact (congrArg (fun L => L hg.family) (fullNativeIntegral_extFamily (μ := μ) h)).symm

/-- **Horizon consistency of the continuous integral.** For `t ≤ T ≤ T'` the horizon-`T` and
horizon-`T'` processes of the same integrand agree a.s. at time `t`. -/
theorem nativeAdaptedLimit_horizon (h : T ≤ T') {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) (hg' : NativeIntegrand μ T' g) {t : ℝ≥0} (ht : t ≤ T) :
    nativeAdaptedLimit μ T hg.family t =ᵐ[driverLaw (κ := κ) μ]
      nativeAdaptedLimit μ T' hg'.family t := by
  have htop : IsStoppingTime (driverAugmented (κ := κ) μ)
      (fun _ : DriverSample S κ => (⊤ : WithTop ℝ≥0)) := fun i => by
    simp only [top_le_iff, WithTop.coe_ne_top, Set.ofPred_false]
    exact @MeasurableSet.empty _ (driverAugmented (κ := κ) μ i)
  obtain ⟨hs, h1⟩ := nativeAdaptedLimit_stopped hg htop t
  obtain ⟨hs', h2⟩ := nativeAdaptedLimit_stopped hg' htop t
  have hst (X : ℝ≥0 → DriverSample S κ → ℝ) : stoppedProcess X (fun _ => ⊤) t = X t := by
    funext x
    exact stoppedProcess_eq_of_le le_top
  rw [hst] at h1 h2
  obtain ⟨hs'', he⟩ := nativeIntegralOf_horizon h hs' (fun c p hp => by
    have hlt : t < p.1.toNNReal := by
      rw [Real.lt_toNNReal_iff_coe_lt]
      exact lt_of_le_of_lt (NNReal.coe_le_coe.2 ht) hp
    have hn : ¬ ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) ⊤ := by
      rw [min_top_right, WithTop.coe_le_coe, not_le]
      exact hlt
    simp only [stopIntegrand, hn, ite_false])
  rw [nativeIntegralOf_congr hs hs'' (fun _ => EventuallyEq.rfl), he] at h1
  exact h1.trans h2.symm

end BlockBand.SourceProcess.Stochastic.NativeSDE
