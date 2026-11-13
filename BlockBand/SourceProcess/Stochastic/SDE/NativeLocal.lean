module
public import BlockBand.SourceProcess.Stochastic.SDE.NativeGlobalSol
public import BlockBand.SourceProcess.Stochastic.SDE.Truncation
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Truncation, switched coefficients, and existence until the exit time

`Ω = DriverSample S κ`, `P = driverLaw μ`, augmented filtration `F_t ∨ N`.

* `exists_truncCoeff`: locally Lipschitz `b, σ_a` agree on the closed `R`-ball (`R > 0`) with
  globally Lipschitz bounded coefficients (radial retraction, `SDE.Truncation`).
* `isStronglyProgressive_switchOff`: switching a progressive process off after an augmented
  stopping time keeps it progressive.
* `exists_solutionUntil_exitTime`: **the existence clause of `LocalWellPosednessFor`**: the
  global solution `Y` of the truncated equation stopped at its exit time `e` from the
  `R`-ball solves the original equation until its own exit time (which is `e`).
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

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Truncation** of locally Lipschitz coefficients on the closed `R`-ball. -/
theorem exists_truncCoeff {b : E → E} {σ : κ → E → E} (hb : LocallyLipschitz b)
    (hσ : ∀ a, LocallyLipschitz (σ a)) {R : ℝ} (hR : 0 < R) :
    ∃ c : LipCoeff κ E, 0 ≤ c.C ∧ ∀ y : E, ‖y‖ ≤ R → c.b y = b y ∧ ∀ a, c.σ a y = σ a y := by
  classical
  obtain ⟨⟨Kb, hKb⟩, hbeq⟩ := SDE.lipschitzWith_comp_radialRetraction_of_finiteDimensional hb hR
  choose hσl hσeq using fun a => SDE.lipschitzWith_comp_radialRetraction_of_finiteDimensional
    (hσ a) hR
  choose Ka hKa using hσl
  obtain ⟨Cb, hCb⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
    hb.continuous.continuousOn
  choose Ca hCa using fun a => (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
    (hσ a).continuous.continuousOn
  have hmem : ∀ y, SDE.radialRetraction R y ∈ Metric.closedBall (0 : E) R := fun y =>
    SDE.mem_closedBall_radialRetraction hR.le y
  refine ⟨⟨b ∘ SDE.radialRetraction R, fun a => σ a ∘ SDE.radialRetraction R,
    Kb + ∑ a, Ka a, max Cb 0 + ∑ a, max (Ca a) 0, hKb.weaken le_self_add,
    fun a => (hKa a).weaken ((Finset.single_le_sum (fun i _ => zero_le) (Finset.mem_univ a)).trans
      le_add_self), fun y => (hCb _ (hmem y)).trans ((le_max_left _ _).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun a _ => le_max_right _ _))),
    fun a y => (hCa a _ (hmem y)).trans ((le_max_left _ _).trans
      ((Finset.single_le_sum (fun i _ => le_max_right (Ca i) 0) (Finset.mem_univ a)).trans
        (le_add_of_nonneg_left (le_max_right _ _))))⟩,
    add_nonneg (le_max_right _ _) (Finset.sum_nonneg fun a _ => le_max_right _ _),
    fun y hy => ⟨hbeq y hy, fun a => hσeq a y hy⟩⟩

omit [IsProbabilityMeasure μ] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- Switching off after an augmented stopping time preserves progressive measurability. -/
theorem isStronglyProgressive_switchOff {e : DriverSample S κ → WithTop ℝ≥0}
    (he : IsStoppingTime (driverAugmented (κ := κ) μ) e) {f : ℝ≥0 → DriverSample S κ → E}
    (hf : IsStronglyProgressive (driverAugmented (κ := κ) μ) f) :
    IsStronglyProgressive (driverAugmented (κ := κ) μ) (switchOff e f) := by
  intro i
  set A : Set (Set.Iic i × DriverSample S κ) :=
    {p | (((p.1 : ℝ≥0) : WithTop ℝ≥0)) ≤ min (e p.2) (i : WithTop ℝ≥0)}
  have hA : MeasurableSet[Subtype.instMeasurableSpace.prod (driverAugmented (κ := κ) μ i)] A := by
    have h2 : Measurable[driverAugmented (κ := κ) μ i] fun x => min (e x) (i : WithTop ℝ≥0) :=
      (he.min_const i).measurable_of_le fun _ => min_le_right _ _
    refine @measurableSet_le _ _ _ _ _ (Subtype.instMeasurableSpace.prod
      (driverAugmented (κ := κ) μ i)) _ _ _ _ _ ?_ ?_
    · exact (WithTop.measurable_coe.comp measurable_subtype_coe).comp measurable_fst
    · exact h2.comp measurable_snd
  have he' : (fun p : Set.Iic i × DriverSample S κ => switchOff e f p.1 p.2) =
      A.indicator fun p => f p.1 p.2 := by
    funext p
    have hpi : (((p.1 : ℝ≥0) : WithTop ℝ≥0)) ≤ i := WithTop.coe_le_coe.2 p.1.2
    simp only [switchOff, Set.indicator_apply, A, mem_ofPred_eq, le_min_iff, hpi, and_true]
  rw [he']
  exact (hf i).indicator hA

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Stopped continuous composites with an a.s. bound on `{0 < s ≤ τ}` are integrands. -/
theorem nativeIntegrand_stopped_bounded {X : ℝ≥0 → DriverSample S κ → E}
    (hXa : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (X t))
    (hXc : ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => X t x)
    {τ : DriverSample S κ → WithTop ℝ≥0} (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ)
    {φ : κ → E → ℝ} (hφ : ∀ a, Continuous (φ a)) {M : ℝ}
    (hM : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ τ x →
      ∀ a, |φ a (X s x)| ≤ M) (T : ℝ≥0) :
    NativeIntegrand μ T (stopIntegrand τ (fun a p => φ a (X p.1.toNNReal p.2))) := by
  refine nativeIntegrand_stoppedComposite (Y := fun _ => X) (fun _ => hXa) (fun _ => hXc) hφ hτ
    fun a => MemLp.of_bound ((aestronglyMeasurable_stoppedComposite (T := T) hXa hXc (hφ a)
      hτ).mono (predictableSpace_le _)) (max M 0) ?_
  filter_upwards [ae_timeProb_of_ae (T := T) hM, timeProbMeasure_horizon (κ := κ) μ T] with p hp hpT
  simp only [stoppedComposite, Real.norm_eq_abs]
  split_ifs with h
  · exact (hp _ (Real.toNNReal_pos.2 hpT.1) h a).trans (le_max_left _ _)
  · simp

/-- **Existence until the exit time** (first clause of `LocalWellPosednessFor`). -/
theorem exists_solutionUntil_exitTime {b : E → E} {σ : κ → E → E} (hb : LocallyLipschitz b)
    (hσ : ∀ a, LocallyLipschitz (σ a)) {ξ : DriverSample S κ → E}
    (hξ : StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ) (R : ℝ) :
    ∃ X : ℝ≥0 → DriverSample S κ → E, IsSDESolutionUntil μ b σ ξ (exitTime X R) X := by
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
  refine ⟨X, ?_, Eventually.of_forall fun x => ?_⟩
  swap
  · rw [hXY x 0 zero_le]
    exact hY0 x
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
