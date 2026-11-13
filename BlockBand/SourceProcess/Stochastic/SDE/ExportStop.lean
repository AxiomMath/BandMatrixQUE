module
public import BlockBand.SourceProcess.Stochastic.SDE.ExportSolution
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Radius consistency of exit-time solutions

`Ω = DriverSample S κ`, `P = driverLaw μ`, augmented filtration `F_t ∨ N`.

* `IsStrongExitSolution.ae_eq_stoppedProcess`: for strong exit-time solutions `X` (radius `R`)
  and `Y` (radius `R' ≥ R`), almost surely `X_t = Y_{t ∧ exit_R(Y)}` for all `t`
  (the uniqueness clause of local strong well-posedness).
* `IsStrongExitSolution.ae_consistent`: hence almost surely `exit_R(X) = exit_R(Y) ≤ exit_{R'}(Y)`
  and `X_t = Y_t` for all `t ≤ exit_R(X)`.
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

/-- **Stopping an exit-time solution at a smaller exit time.** -/
theorem IsSDESolutionUntil.stop_exitTime {b : E → E} {σ : κ → E → E}
    (hb : LocallyLipschitz b) (hσ : ∀ a, LocallyLipschitz (σ a)) {ξ : DriverSample S κ → E}
    {R R' : ℝ} (hRR' : R ≤ R') {X : ℝ≥0 → DriverSample S κ → E}
    (hX : IsSDESolutionUntil μ b σ ξ (exitTime X R') X) (hc : ∀ x, Continuous fun t => X t x) :
    IsSDESolutionUntil μ b σ ξ (exitTime (stoppedProcess X (exitTime X R)) R)
      (stoppedProcess X (exitTime X R)) := by
  classical
  obtain ⟨hXi, hX0⟩ := hX
  set e : DriverSample S κ → WithTop ℝ≥0 := exitTime X R with hedef
  set e' : DriverSample S κ → WithTop ℝ≥0 := exitTime X R' with he'def
  have he : IsStoppingTime (driverAugmented (κ := κ) μ) e := isStoppingTime_exitTimeOf hXi.adapted hc R
  have he' : IsStoppingTime (driverAugmented (κ := κ) μ) e' :=
    isStoppingTime_exitTimeOf hXi.adapted hc R'
  have hee' : ∀ x, e x ≤ e' x := fun x => exitTimeOf_mono hRR' x
  set Z : ℝ≥0 → DriverSample S κ → E := stoppedProcess X e with hZdef
  have hZprog : IsStronglyProgressive (driverAugmented (κ := κ) μ) Z :=
    hXi.progressive.stoppedProcess he
  have hZa : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (Z t) :=
    hXi.progressive.stronglyAdapted_stoppedProcess he
  have hZc : ∀ x, Continuous fun t => Z t x := fun x => continuous_stoppedProcess (hc x) e
  have hZe : exitTime Z R = e := funext fun x => exitTimeOf_stoppedProcess (hc x)
  have hZX : ∀ x (s : ℝ≥0), (s : WithTop ℝ≥0) ≤ e x → Z s x = X s x := fun x s hs =>
    stoppedProcess_eq_of_le hs
  refine ⟨?_, ?_⟩
  swap
  · filter_upwards [hX0] with x hx
    rw [hZX x 0 zero_le, hx]
  have hloc : ∀ (τ : DriverSample S κ → WithTop ℝ≥0),
      IsStoppingTime (driverAugmented (κ := κ) μ) τ → ∀ (ℓ : E →L[ℝ] ℝ) (T : ℝ≥0),
      NativeIntegrand μ T (stopIntegrand τ (functionalIntegrand ℓ fun a =>
        switchOff e fun t x => σ a (Z t x))) := fun τ hτ ℓ T => by
    have h := nativeIntegrand_switched (μ := μ) hb hσ hZa (Eventually.of_forall hZc) hZc
      (Eventually.of_forall fun _ _ => rfl) (by rw [exitTimeOf_eq_exitTime, hZe]; exact he) hτ ℓ T
    rwa [hZe] at h
  rw [hZe]
  refine ⟨hZa, hZprog, Eventually.of_forall hZc,
    isStronglyProgressive_switchOff he fun i => hb.continuous.comp_stronglyMeasurable (hZprog i),
    fun a => isStronglyProgressive_switchOff he fun i =>
      (hσ a).continuous.comp_stronglyMeasurable (hZprog i), ?_,
    ⟨fun _ _ => ⊤, fun _ => isStoppingTime_top, Eventually.of_forall fun _ => tendsto_const_nhds,
      fun _ ℓ T => hloc _ isStoppingTime_top ℓ T⟩, ?_⟩
  · -- drift integrability: the new drift path is the old one cut at `e`
    filter_upwards [hXi.drift_integrable] with x hx t
    refine ((hx t).indicator (measurableSet_toNNReal_le (e x))).congr_fun (fun s _ => ?_)
      measurableSet_Ioc
    simp only [Set.indicator_apply, mem_ofPred_eq, switchOff]
    split_ifs with h1 h2
    · rw [hZX x _ h1]
    · exact absurd (h1.trans (hee' x)) h2
    · rfl
  · -- the identity, through `X` at `min τ e`
    intro ℓ τ hτ T _ t ht
    obtain ⟨hs', hid'⟩ := hXi.identity ℓ _ (hτ.min he) T
      (nativeIntegrand_switched (μ := μ) hb hσ hXi.adapted (Eventually.of_forall hc) hc
        (Eventually.of_forall fun _ _ => rfl) he' (hτ.min he) ℓ T) t ht
    have hint : ∀ a, stopIntegrand (fun x => min (t : WithTop ℝ≥0) (min (τ x) (e x)))
        (functionalIntegrand ℓ fun a => switchOff (exitTime X R') fun t x => σ a (X t x)) a =ᵐ[
          timeProbMeasure T (driverLaw (κ := κ) μ)] stopIntegrand
          (fun x => min (t : WithTop ℝ≥0) (τ x))
        (functionalIntegrand ℓ fun a => switchOff e fun t x => σ a (Z t x)) a := fun a =>
      Eventually.of_forall fun p => by
        simp only [stopIntegrand, functionalIntegrand, switchOff, le_min_iff]
        by_cases h1 : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ t
        · by_cases h2 : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ p.2
          · by_cases h3 : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ e p.2
            · have h4 : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ exitTime X R' p.2 :=
                h3.trans (hee' _)
              simp only [h1, h2, h3, h4, and_self, ite_true, hZX p.2 _ h3]
            · simp only [h1, h2, h3, and_self, ite_true, and_false, ite_false, map_zero]
          · simp only [h1, h2, and_false, false_and, ite_false]
        · simp only [h1, false_and, ite_false]
    refine ⟨NativeIntegrand.congr hs' hint, ?_⟩
    rw [← nativeIntegralOf_congr hs' _ hint]
    filter_upwards [hid'] with x hx
    have h1 : stoppedProcess Z τ t x = stoppedProcess X (fun x => min (τ x) (e x)) t x := by
      rw [hZdef, stoppedProcess_stoppedProcess']
    have h2 : stoppedDrift τ (switchOff e fun t x => b (Z t x)) t x =
        stoppedDrift (fun x => min (τ x) (e x))
          (switchOff (exitTime X R') fun t x => b (X t x)) t x := by
      unfold stoppedDrift
      refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
      simp only [switchOff, le_min_iff]
      by_cases h2 : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x
      · by_cases h3 : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ e x
        · have h4 : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ exitTime X R' x :=
            h3.trans (hee' _)
          simp only [h2, h3, h4, and_self, ite_true, hZX x _ h3]
        · simp only [h2, h3, and_false, ite_false, ite_true]
      · simp only [h2, false_and, ite_false]
    rw [h1, h2, hZX x 0 zero_le]
    exact hx

/-- Strong exit-time solutions of radii `R ≤ R'` are consistent: `X = Y` stopped at
`exit_R(Y)`, almost surely for all times. -/
theorem IsStrongExitSolution.ae_eq_stoppedProcess {b : E → E} {σ : κ → E → E}
    (hb : LocallyLipschitz b) (hσ : ∀ a, LocallyLipschitz (σ a)) {ξ : DriverSample S κ → E}
    {R R' : ℝ} (hRR' : R ≤ R') {X Y : ℝ≥0 → DriverSample S κ → E}
    (hX : IsStrongExitSolution μ b σ ξ R X) (hY : IsStrongExitSolution μ b σ ξ R' Y) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, X t x = stoppedProcess Y (exitTime Y R) t x :=
  ae_eq_of_isSDESolutionUntil_exitTime hb hσ hX.sol
    (IsSDESolutionUntil.stop_exitTime hb hσ hRR' hY.sol hY.continuous)

/-- Consistency of exit times and paths for strong exit-time solutions of radii `R ≤ R'`. -/
theorem IsStrongExitSolution.ae_consistent {b : E → E} {σ : κ → E → E}
    (hb : LocallyLipschitz b) (hσ : ∀ a, LocallyLipschitz (σ a)) {ξ : DriverSample S κ → E}
    {R R' : ℝ} (hRR' : R ≤ R') {X Y : ℝ≥0 → DriverSample S κ → E}
    (hX : IsStrongExitSolution μ b σ ξ R X) (hY : IsStrongExitSolution μ b σ ξ R' Y) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, exitTime X R x = exitTime Y R x ∧
      exitTime X R x ≤ exitTime Y R' x ∧
      ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ exitTime X R x → X t x = Y t x := by
  filter_upwards [hX.ae_eq_stoppedProcess hb hσ hRR' hY] with x hx
  have hfun : (fun t => X t x) = fun t => stoppedProcess Y (exitTime Y R) t x := funext hx
  have hex : exitTime X R x = exitTime Y R x := by
    have h1 : exitTime X R x = exitTime (stoppedProcess Y (exitTime Y R)) R x := by
      simp only [exitTime, hx]
    rw [h1]
    exact exitTimeOf_stoppedProcess (hY.continuous x)
  refine ⟨hex, hex ▸ exitTimeOf_mono hRR' x, fun t ht => ?_⟩
  rw [hx t, stoppedProcess_eq_of_le (hex ▸ ht)]

end BlockBand.SourceProcess.Stochastic.NativeSDE
