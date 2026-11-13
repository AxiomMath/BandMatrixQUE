module
public import BlockBand.SourceProcess.Stochastic.SDE.NativeWellPosed
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Strengthened existence until the exit time

`Ω = DriverSample S κ`, `P = driverLaw μ`, augmented filtration `F_t ∨ N`.

`exists_solutionUntil_exitTime_strong`: for locally Lipschitz `b, σ_a`, every
augmented-`F_0`-measurable `ξ` and every radius `R`, there is a solution `X` of
`dX = b(X) dt + ∑_a σ_a(X) dW^a`, `X_0 = ξ`, until its own exit time `e = exitTime X R`
(`IsSDESolutionUntil`) such that, in addition,
* every path `t ↦ X_t x` is continuous (not only almost every path);
* the initial value is `ξ` for every sample;
* the exit time `e` is an augmented stopping time;
* the solution is stopped at `e` for every sample: `X_{t ∧ e} = X_t`.
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
/-- A **strong exit-time solution**: a solution until its own exit time from the `R`-ball with
everywhere continuous paths, `X_0 = ξ` everywhere, an augmented stopping exit time, and
paths stopped at the exit time. -/
structure IsStrongExitSolution (b : E → E) (σ : κ → E → E) (ξ : DriverSample S κ → E) (R : ℝ)
    (X : ℝ≥0 → DriverSample S κ → E) : Prop where
  sol : IsSDESolutionUntil μ b σ ξ (exitTime X R) X
  continuous : ∀ x, Continuous fun t => X t x
  init : ∀ x, X 0 x = ξ x
  stopping : IsStoppingTime (driverAugmented (κ := κ) μ) (exitTime X R)
  stopped : ∀ t x, stoppedProcess X (exitTime X R) t x = X t x

/-- **Strengthened existence until the exit time.** -/
theorem exists_solutionUntil_exitTime_strong {b : E → E} {σ : κ → E → E}
    (hb : LocallyLipschitz b) (hσ : ∀ a, LocallyLipschitz (σ a)) {ξ : DriverSample S κ → E}
    (hξ : StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ) (R : ℝ) :
    ∃ X : ℝ≥0 → DriverSample S κ → E, IsStrongExitSolution μ b σ ξ R X := by
  classical
  obtain ⟨c, hC0, hceq⟩ := exists_truncCoeff hb hσ (lt_max_of_lt_right one_pos : (0 : ℝ) < max R 1)
  obtain ⟨Y, hYa, hYc, hY0, hYid⟩ := exists_globalLipSol c hξ
  set e : DriverSample S κ → WithTop ℝ≥0 := exitTimeOf Y R with hedef
  have he : IsStoppingTime (driverAugmented (κ := κ) μ) e := isStoppingTime_exitTimeOf hYa hYc R
  have hYprog : IsStronglyProgressive (driverAugmented (κ := κ) μ) Y :=
    StronglyAdapted.isStronglyProgressive_of_continuous hYa hYc
  set X : ℝ≥0 → DriverSample S κ → E := stoppedProcess Y e with hXdef
  have hXprog : IsStronglyProgressive (driverAugmented (κ := κ) μ) X := hYprog.stoppedProcess he
  have hXc : ∀ x, Continuous fun t => X t x := fun x => continuous_stoppedProcess (hYc x) e
  have hXe : exitTime X R = e := funext fun x => exitTimeOf_stoppedProcess (hYc x)
  have hXY : ∀ x (s : ℝ≥0), (s : WithTop ℝ≥0) ≤ e x → X s x = Y s x := fun x s hs =>
    stoppedProcess_eq_of_le hs
  have hco : ∀ x (s : ℝ≥0), 0 < s → (s : WithTop ℝ≥0) ≤ e x →
      b (X s x) = c.b (Y s x) ∧ ∀ a, σ a (X s x) = c.σ a (Y s x) := by
    intro x s hs0 hs
    have hn : ‖Y s x‖ ≤ max R 1 := (norm_le_of_le_exitTimeOf (hYc x) hs0 hs).trans (le_max_left _ _)
    rw [hXY x s hs]
    exact ⟨(hceq _ hn).1.symm, fun a => ((hceq _ hn).2 a).symm⟩
  have hX0 : ∀ x, X 0 x = ξ x := fun x => by rw [hXY x 0 zero_le]; exact hY0 x
  refine ⟨X, ⟨?_, Eventually.of_forall hX0⟩, hXc, hX0, hXe ▸ he, fun t x => ?_⟩
  swap
  · rw [hXe, hXdef, stoppedProcess_stoppedProcess', funext fun x => min_self (e x)]
  rw [hXe]
  refine ⟨hYprog.stronglyAdapted_stoppedProcess he, hXprog, Eventually.of_forall hXc,
    isStronglyProgressive_switchOff he fun i => hb.continuous.comp_stronglyMeasurable (hXprog i),
    fun a => isStronglyProgressive_switchOff he fun i =>
      (hσ a).continuous.comp_stronglyMeasurable (hXprog i), ?_, ?_, ?_⟩
  · -- drift integrability
    refine Eventually.of_forall fun x t => ?_
    refine Integrable.mono' (g := fun _ => c.C) (integrableOn_const (by simp)) ?_ ?_
    · refine (Measurable.ite (measurableSet_toNNReal_le (e x)) ?_ measurable_const).aestronglyMeasurable
      exact (hb.continuous.comp ((hXc x).comp continuous_real_toNNReal)).measurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      simp only [switchOff]
      split_ifs with h
      · rw [(hco x _ (Real.toNNReal_pos.2 hs.1) h).1]
        exact c.bd_b _
      · simpa using hC0
  · -- localizing sequence: constant `⊤`
    refine ⟨fun _ _ => ⊤, fun _ => isStoppingTime_top, Eventually.of_forall fun _ =>
      tendsto_const_nhds, fun n ℓ T => ?_⟩
    have h := nativeIntegrand_stopped_bounded (μ := μ) (X := Y) hYa (Eventually.of_forall hYc) he
      (φ := fun a y => ℓ (c.σ a y)) (fun a => ℓ.continuous.comp (c.lip_σ a).continuous)
      (M := ‖ℓ‖ * c.C) (Eventually.of_forall fun x s _ _ a => by
        rw [← Real.norm_eq_abs]
        exact (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (c.bd_σ a _) (norm_nonneg _))) T
    refine NativeIntegrand.congr h fun a => ?_
    filter_upwards [timeProbMeasure_horizon (κ := κ) μ T] with p hp
    simp only [stopIntegrand, functionalIntegrand, switchOff, le_top, ite_true]
    split_ifs with h1
    · rw [(hco p.2 _ (Real.toNNReal_pos.2 hp.1) h1).2 a]
    · simp
  · -- the identity, through the global solution at `min τ e`
    intro ℓ τ hτ T _ t ht
    obtain ⟨hs', hid'⟩ := hYid T _ (hτ.min he) ℓ t ht
    have hint : ∀ a, stopIntegrand (fun x => min (t : WithTop ℝ≥0) (min (τ x) (e x)))
        (functionalIntegrand ℓ fun a t x => c.σ a (Y t x)) a =ᵐ[timeProbMeasure T
          (driverLaw (κ := κ) μ)] stopIntegrand (fun x => min (t : WithTop ℝ≥0) (τ x))
        (functionalIntegrand ℓ fun a => switchOff e fun t x => σ a (X t x)) a := fun a => by
      filter_upwards [timeProbMeasure_horizon (κ := κ) μ T] with p hp
      have hpos : 0 < p.1.toNNReal := Real.toNNReal_pos.2 hp.1
      simp only [stopIntegrand, functionalIntegrand, switchOff, le_min_iff]
      by_cases h1 : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ t
      · by_cases h2 : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ p.2
        · by_cases h3 : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ e p.2
          · simp only [h1, h2, h3, and_self, ite_true, (hco p.2 _ hpos h3).2 a]
          · simp only [h1, h2, h3, and_self, ite_true, and_false, ite_false, map_zero]
        · simp only [h1, h2, and_false, false_and, ite_false]
      · simp only [h1, false_and, ite_false]
    refine ⟨NativeIntegrand.congr hs' hint, ?_⟩
    rw [← nativeIntegralOf_congr hs' _ hint]
    filter_upwards [hid'] with x hx
    have h1 : stoppedProcess X τ t x = stoppedProcess Y (fun x => min (τ x) (e x)) t x := by
      rw [hXdef, stoppedProcess_stoppedProcess']
    have h2 : stoppedDrift τ (switchOff e fun t x => b (X t x)) t x =
        stoppedDrift (fun x => min (τ x) (e x)) (fun t x => c.b (Y t x)) t x := by
      unfold stoppedDrift
      refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      have hpos : 0 < s.toNNReal := Real.toNNReal_pos.2 hs.1
      simp only [switchOff, le_min_iff]
      by_cases h2 : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x
      · by_cases h3 : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ e x
        · simp only [h2, h3, and_self, ite_true, (hco x _ hpos h3).1]
        · simp only [h2, h3, and_false, ite_false, ite_true]
      · simp only [h2, false_and, ite_false]
    rw [h1, h2, hXY x 0 zero_le]
    exact hx

end BlockBand.SourceProcess.Stochastic.NativeSDE
