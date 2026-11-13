module
public import BlockBand.SourceProcess.Stochastic.SDE.NativeEstimates
public import BlockBand.SourceProcess.Stochastic.SDE.NativeExit
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# One-step `L²` comparison of two Itô identities

`Ω = DriverSample S κ`, `P = driverLaw μ`, `ν_t = timeProbMeasure t P`, augmented
filtration `F_t ∨ N`, a fixed augmented stopping time `ρ` and horizon `T`.

`StoppedIdentity μ T ρ X β γ` is the `identity` clause of `IsNativeItoProcess` for the single
stopping time `ρ` and horizon `T`: for every functional `ℓ` and `t ≤ T`,
`ℓ(X_{t∧ρ}) − ℓ(X_0) − ℓ(∫_0^{t∧ρ} β) = ∫_0^T ℓ(γ) 1{s ≤ t∧ρ} dW` a.s.

`lintegral_sq_functional_sub_le`: if two processes satisfy such identities with the same
`ρ`, equal initial values, and the coefficient differences are dominated by `H(s,x)` on
`{0 < s ≤ ρ}`, then
`E|ℓ(X_{t∧ρ}) − ℓ(Y_{t∧ρ})|² ≤ 2‖ℓ‖² (t + |κ|) ∫⁻ H² dν_t`
(drift by pathwise Cauchy–Schwarz, noise by the Itô isometry). Also: continuous
modifications (`exists_continuous_modification`) and measurability of stopped values
(`aestronglyMeasurable_stoppedProcess`).
-/

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable (μ) in
/-- The `identity` clause of `IsNativeItoProcess` for one stopping time and one horizon. -/
def StoppedIdentity (T : ℝ≥0) (ρ : DriverSample S κ → WithTop ℝ≥0)
    (X : ℝ≥0 → DriverSample S κ → E) (β : ℝ≥0 → DriverSample S κ → E)
    (γ : κ → ℝ≥0 → DriverSample S κ → E) : Prop :=
  ∀ (ℓ : E →L[ℝ] ℝ) (t : ℝ≥0), t ≤ T →
    ∃ hs : NativeIntegrand μ T
        (stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x)) (functionalIntegrand ℓ γ)),
      (fun x => ℓ (stoppedProcess X ρ t x) - ℓ (X 0 x) - ℓ (stoppedDrift ρ β t x))
        =ᵐ[driverLaw (κ := κ) μ] (nativeIntegralOf hs : DriverSample S κ → ℝ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `IsNativeItoProcess.identity` gives `StoppedIdentity` for stopping times whose stopped
diffusion functionals are integrands. -/
theorem IsNativeItoProcess.stoppedIdentity [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {X β : ℝ≥0 → DriverSample S κ → E} {γ : κ → ℝ≥0 → DriverSample S κ → E}
    (h : IsNativeItoProcess μ X β γ) {ρ : DriverSample S κ → WithTop ℝ≥0}
    (hρ : IsStoppingTime (driverAugmented (κ := κ) μ) ρ) (T : ℝ≥0)
    (hn : ∀ ℓ : E →L[ℝ] ℝ, NativeIntegrand μ T (stopIntegrand ρ (functionalIntegrand ℓ γ))) :
    StoppedIdentity μ T ρ X β γ := fun ℓ t ht =>
  h.identity ℓ ρ hρ T (hn ℓ) t ht

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem measurableSet_toNNReal_le (c : WithTop ℝ≥0) :
    MeasurableSet {s : ℝ | ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ c} := by
  cases c with
  | top => simp only [le_top, ofPred_true, MeasurableSet.univ]
  | coe m =>
    have : {s : ℝ | ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ (m : WithTop ℝ≥0)} = Iic (m : ℝ) := by
      ext s
      simp only [mem_ofPred_eq, WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe, mem_Iic]
    rw [this]
    exact measurableSet_Iic

omit [IsProbabilityMeasure μ] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- A continuous modification of an augmented-adapted a.s. continuous process. -/
theorem exists_continuous_modification {X : ℝ≥0 → DriverSample S κ → E}
    (hXa : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (X t))
    (hXc : ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => X t x) :
    ∃ X' : ℝ≥0 → DriverSample S κ → E,
      (∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (X' t)) ∧
      (∀ x, Continuous fun t => X' t x) ∧ ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, X' t x = X t x := by
  classical
  obtain ⟨G, hG, hG0, hGc⟩ := exists_good_set μ hXc
  refine ⟨fun t => G.indicator (X t), fun t => (hXa t).indicator
    (measurableSet_aug_of_full μ hG hG0 t), fun x => ?_, ?_⟩
  · by_cases hx : x ∈ G
    · simp only [Set.indicator_of_mem hx]
      exact hGc x hx
    · simp only [Set.indicator_of_notMem hx]
      exact continuous_const
  · have hGae : ∀ᵐ x ∂driverLaw (κ := κ) μ, x ∈ G := by
      rw [ae_iff]
      simpa only [compl_def] using hG0
    filter_upwards [hGae] with x hx t
    simp only [Set.indicator_of_mem hx]

omit [IsProbabilityMeasure μ] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- Stopped values of an augmented-adapted a.s. continuous process at an augmented stopping
time are a.e. strongly measurable. -/
theorem aestronglyMeasurable_stoppedProcess {X : ℝ≥0 → DriverSample S κ → E}
    (hXa : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (X t))
    (hXc : ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => X t x)
    {ρ : DriverSample S κ → WithTop ℝ≥0} (hρ : IsStoppingTime (driverAugmented (κ := κ) μ) ρ)
    (t : ℝ≥0) : AEStronglyMeasurable (stoppedProcess X ρ t) (driverLaw (κ := κ) μ) := by
  obtain ⟨X', hX'a, hX'c, hXX'⟩ := exists_continuous_modification hXa hXc
  have hprog : IsStronglyProgressive (driverAugmented (κ := κ) μ) X' :=
    StronglyAdapted.isStronglyProgressive_of_continuous hX'a hX'c
  have hm := (hprog.stronglyAdapted_stoppedProcess hρ t).mono ((driverAugmented (κ := κ) μ).le t)
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [hXX'] with x hx
  simp only [stoppedProcess, hx]

omit [MeasurableSpace S] [Fintype κ] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
theorem integrableOn_driftPath {ρ : DriverSample S κ → WithTop ℝ≥0}
    {β : ℝ≥0 → DriverSample S κ → E} {x : DriverSample S κ} {T t : ℝ≥0} (htT : t ≤ T) {C : ℝ}
    (hm : AEStronglyMeasurable (fun s : ℝ => β s.toNNReal x) (volume.restrict (Ioc 0 (T : ℝ))))
    (hb : ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ x → ‖β s x‖ ≤ C) :
    IntegrableOn (fun s : ℝ => if ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ρ x then β s.toNNReal x
      else 0) (Ioc 0 (t : ℝ)) := by
  have hm' := (hm.mono_measure (Measure.restrict_mono
    (Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 htT)) le_rfl)).indicator
    (measurableSet_toNNReal_le (ρ x))
  refine Integrable.mono' (g := fun _ => max C 0) (integrableOn_const (by simp))
    (hm'.congr (Eventually.of_forall fun s => ?_)) ?_
  · simp only [Set.indicator_apply, mem_ofPred_eq]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    split_ifs with h
    · exact (hb _ (Real.toNNReal_pos.2 hs.1) h).trans (le_max_left _ _)
    · simp

omit [MeasurableSpace E] [BorelSpace E] in
/-- **One-step comparison.** Two identities with the same stopping time and equal
initial values, whose coefficient differences are dominated by `H` on `{0 < s ≤ ρ}`, satisfy
`E|ℓ(X_{t∧ρ}) − ℓ(Y_{t∧ρ})|² ≤ 2‖ℓ‖² (t + |κ|) ∫⁻ H² dν_t`. -/
theorem lintegral_sq_functional_sub_le {T : ℝ≥0} {ρ : DriverSample S κ → WithTop ℝ≥0}
    {X Y β β' : ℝ≥0 → DriverSample S κ → E} {γ γ' : κ → ℝ≥0 → DriverSample S κ → E}
    (h0 : ∀ᵐ x ∂driverLaw (κ := κ) μ, X 0 x = Y 0 x)
    (hX : StoppedIdentity μ T ρ X β γ) (hY : StoppedIdentity μ T ρ Y β' γ') {C : ℝ}
    (hbd : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ x →
      ‖β s x‖ ≤ C ∧ ‖β' s x‖ ≤ C)
    (hβ : ∀ᵐ x ∂driverLaw (κ := κ) μ,
      AEStronglyMeasurable (fun s : ℝ => β s.toNNReal x) (volume.restrict (Ioc 0 (T : ℝ))))
    (hβ' : ∀ᵐ x ∂driverLaw (κ := κ) μ,
      AEStronglyMeasurable (fun s : ℝ => β' s.toNNReal x) (volume.restrict (Ioc 0 (T : ℝ))))
    {H : ℝ × DriverSample S κ → ℝ≥0∞}
    (hHm : AEMeasurable H (timeProbMeasure T (driverLaw (κ := κ) μ)))
    (hHpath : ∀ᵐ x ∂driverLaw (κ := κ) μ,
      AEMeasurable (fun s : ℝ => H (s, x)) (volume.restrict (Ioc 0 (T : ℝ))))
    (hdom : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ x →
      ‖β s x - β' s x‖ₑ ≤ H (s, x) ∧ ∀ a, ‖γ a s x - γ' a s x‖ₑ ≤ H (s, x))
    (ℓ : E →L[ℝ] ℝ) {t : ℝ≥0} (htT : t ≤ T) :
    ∫⁻ x, ‖ℓ (stoppedProcess X ρ t x) - ℓ (stoppedProcess Y ρ t x)‖ₑ ^ 2 ∂driverLaw (κ := κ) μ ≤
      2 * ‖ℓ‖ₑ ^ 2 * (ENNReal.ofReal t + Fintype.card κ) *
        ∫⁻ p, H p ^ 2 ∂timeProbMeasure t (driverLaw (κ := κ) μ) := by
  obtain ⟨hsX, hidX⟩ := hX ℓ t htT
  obtain ⟨hsY, hidY⟩ := hY ℓ t htT
  set J := nativeIntegralOf (nativeIntegrand_sub hsX hsY) with hJdef
  have hJ : (J : DriverSample S κ → ℝ) =ᵐ[driverLaw (κ := κ) μ] fun x =>
      (nativeIntegralOf hsX : DriverSample S κ → ℝ) x -
        (nativeIntegralOf hsY : DriverSample S κ → ℝ) x := by
    rw [hJdef, nativeIntegralOf_sub]
    exact Lp.coeFn_sub _ _
  set D : DriverSample S κ → ℝ := fun x => ℓ (stoppedDrift ρ β t x) - ℓ (stoppedDrift ρ β' t x)
  have hdecomp : ∀ᵐ x ∂driverLaw (κ := κ) μ,
      ℓ (stoppedProcess X ρ t x) - ℓ (stoppedProcess Y ρ t x) = D x + J x := by
    filter_upwards [hidX, hidY, hJ, h0] with x h1 h2 h3 h4
    rw [h3, ← h1, ← h2, h4]
    ring
  have hJm : AEMeasurable (fun x => 2 * ‖(J : DriverSample S κ → ℝ) x‖ₑ ^ 2)
      (driverLaw (κ := κ) μ) :=
    ((Lp.aestronglyMeasurable J).enorm.pow_const 2).const_mul 2
  have hH2 : AEMeasurable (fun p => H p ^ 2) (timeProbMeasure t (driverLaw (κ := κ) μ)) :=
    (hHm.mono_measure (timeProbMeasure_le_of_le htT)).pow_const 2
  -- drift term
  have hDrift : ∫⁻ x, ‖D x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ ≤
      ‖ℓ‖ₑ ^ 2 * ENNReal.ofReal t * ∫⁻ p, H p ^ 2 ∂timeProbMeasure t (driverLaw (κ := κ) μ) := by
    calc ∫⁻ x, ‖D x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ
        ≤ ∫⁻ x, ‖ℓ‖ₑ ^ 2 * (ENNReal.ofReal t * (∫⁻ s in Ioc 0 (t : ℝ), H (s, x) ^ 2))
            ∂driverLaw (κ := κ) μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hbd, hβ, hβ', hHpath, hdom] with x hb hm hm' hp hd
          refine enorm_sq_functional_drift_sub_le
            (integrableOn_driftPath htT hm fun s h1 h2 => (hb s h1 h2).1)
            (integrableOn_driftPath htT hm' fun s h1 h2 => (hb s h1 h2).2) ?_
            (hp.mono_measure (Measure.restrict_mono
              (Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 htT)) le_rfl)) ℓ
          intro s hs
          split_ifs with h
          · have := (hd s.toNNReal (Real.toNNReal_pos.2 hs.1) h).1
            rwa [Real.coe_toNNReal _ hs.1.le] at this
          · simp
      _ = ‖ℓ‖ₑ ^ 2 * ENNReal.ofReal t *
            ∫⁻ x, (∫⁻ s in Ioc 0 (t : ℝ), H (s, x) ^ 2) ∂driverLaw (κ := κ) μ := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp), mul_assoc]
      _ = _ := by
          congr 1
          unfold timeProbMeasure
          exact (lintegral_prod_symm _ hH2).symm
  -- noise term
  have hNoise : ∫⁻ x, ‖(J : DriverSample S κ → ℝ) x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ ≤
      Fintype.card κ * (‖ℓ‖ₑ ^ 2 * ∫⁻ p, H p ^ 2 ∂timeProbMeasure t (driverLaw (κ := κ) μ)) := by
    rw [hJdef, lintegral_sq_nativeIntegralOf]
    have hterm : ∀ c, ∫⁻ p, ‖stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x))
          (functionalIntegrand ℓ γ) c p - stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x))
          (functionalIntegrand ℓ γ') c p‖ₑ ^ 2 ∂timeProbMeasure T (driverLaw (κ := κ) μ) ≤
        ‖ℓ‖ₑ ^ 2 * ∫⁻ p, H p ^ 2 ∂timeProbMeasure t (driverLaw (κ := κ) μ) := by
      intro c
      calc _ ≤ ∫⁻ p, (window S κ t).indicator (fun p => ‖ℓ‖ₑ ^ 2 * H p ^ 2) p
              ∂timeProbMeasure T (driverLaw (κ := κ) μ) := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_timeProb_of_ae (T := T) hdom,
              timeProbMeasure_horizon (κ := κ) μ T] with p hp hpT
            simp only [stopIntegrand, functionalIntegrand]
            split_ifs with h
            · have hpos : 0 < p.1.toNNReal := Real.toNNReal_pos.2 hpT.1
              have hw : p ∈ window S κ t := by
                refine ⟨⟨hpT.1, ?_⟩, mem_univ _⟩
                have h' := (le_min_iff.1 h).1
                rw [WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe] at h'
                exact h'
              rw [Set.indicator_of_mem hw]
              have hd := (hp p.1.toNNReal hpos (le_min_iff.1 h).2).2 c
              rw [Real.coe_toNNReal _ hpT.1.le] at hd
              rw [← map_sub, ← mul_pow]
              exact pow_le_pow_left₀ zero_le
                ((ContinuousLinearMap.le_opENorm ℓ _).trans (mul_le_mul_right hd _)) 2
            · simp
        _ = ‖ℓ‖ₑ ^ 2 * ∫⁻ p, H p ^ 2 ∂timeProbMeasure t (driverLaw (κ := κ) μ) := by
            rw [lintegral_indicator (measurableSet_window t), timeProbMeasure_restrict_window htT,
              lintegral_const_mul' _ _ (by simp)]
    calc _ ≤ ∑ _c : κ, ‖ℓ‖ₑ ^ 2 * ∫⁻ p, H p ^ 2 ∂timeProbMeasure t (driverLaw (κ := κ) μ) :=
          Finset.sum_le_sum fun c _ => hterm c
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc ∫⁻ x, ‖ℓ (stoppedProcess X ρ t x) - ℓ (stoppedProcess Y ρ t x)‖ₑ ^ 2 ∂driverLaw (κ := κ) μ
      ≤ ∫⁻ x, (2 * ‖D x‖ₑ ^ 2 + 2 * ‖(J : DriverSample S κ → ℝ) x‖ₑ ^ 2)
          ∂driverLaw (κ := κ) μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hdecomp] with x hx
        rw [hx]
        exact enorm_sq_add_le _ _
    _ = 2 * ∫⁻ x, ‖D x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ +
          2 * ∫⁻ x, ‖(J : DriverSample S κ → ℝ) x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ := by
        rw [lintegral_add_right' _ hJm, lintegral_const_mul' _ _ (by simp),
          lintegral_const_mul' _ _ (by simp)]
    _ ≤ 2 * (‖ℓ‖ₑ ^ 2 * ENNReal.ofReal t * ∫⁻ p, H p ^ 2 ∂timeProbMeasure t (driverLaw (κ := κ) μ)) +
          2 * (Fintype.card κ * (‖ℓ‖ₑ ^ 2 *
            ∫⁻ p, H p ^ 2 ∂timeProbMeasure t (driverLaw (κ := κ) μ))) := by
        gcongr
    _ = _ := by ring

end BlockBand.SourceProcess.Stochastic.NativeSDE
