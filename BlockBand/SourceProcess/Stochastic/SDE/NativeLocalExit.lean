module
public import BlockBand.SourceProcess.Stochastic.SDE.NativeLocalUnique
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Uniqueness of solutions until their own exit times

`Ω = DriverSample S κ`, `P = driverLaw μ`, augmented filtration `F_t ∨ N`.

`ae_eq_of_isSDESolutionUntil_exitTime` (second clause of `LocalWellPosednessFor`): two
solutions `X, Y` until their own exit times from the `R`-ball are indistinguishable.

Proof. With continuous modifications `X', Y'` and `e_X = exit(X'), e_Y = exit(Y')` (augmented
stopping times, a.s. equal to the exit times of `X, Y`):
1. up to `ρ = e_X ∧ e_Y` both solve the equation inside the closed `R`-ball, so
   `X_{·∧ρ} = Y_{·∧ρ}` (`stoppedProcess_ae_eq_local`);
2. hence `e_X = e_Y` a.s. (the exit level is attained by continuity);
3. with `ρ = ⊤` the switched coefficients are now either both active (inside the ball) or both
   off, and `stoppedProcess_ae_eq_local` again gives `X = Y`.
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
/-- Stopped functionals of exit-time-switched diffusions are integrands. -/
theorem nativeIntegrand_switched {b : E → E} {σ : κ → E → E} (hb : LocallyLipschitz b)
    (hσ : ∀ a, LocallyLipschitz (σ a)) {R : ℝ} {Z Z' : ℝ≥0 → DriverSample S κ → E}
    (hZa : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (Z t))
    (hZc : ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => Z t x)
    (hZ'c : ∀ x, Continuous fun t => Z' t x)
    (hZZ' : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, Z' t x = Z t x)
    (heZ : IsStoppingTime (driverAugmented (κ := κ) μ) (exitTimeOf Z' R))
    {τ : DriverSample S κ → WithTop ℝ≥0} (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ)
    (ℓ : E →L[ℝ] ℝ) (T : ℝ≥0) :
    NativeIntegrand μ T (stopIntegrand τ (functionalIntegrand ℓ fun a =>
      switchOff (exitTime Z R) fun t x => σ a (Z t x))) := by
  obtain ⟨c, -, hceq⟩ := exists_truncCoeff hb hσ (lt_max_of_lt_right one_pos : (0 : ℝ) < max R 1)
  have h := nativeIntegrand_stopped_bounded (μ := μ) hZa hZc (hτ.min heZ)
    (φ := fun a y => ℓ (σ a y)) (fun a => ℓ.continuous.comp (hσ a).continuous)
    (M := ‖ℓ‖ * c.C) (by
      filter_upwards [hZZ'] with x hx s hs0 hs a
      have hn : ‖Z s x‖ ≤ max R 1 := by
        rw [← hx s]
        exact (norm_le_of_le_exitTimeOf (hZ'c x) hs0 (hs.trans (min_le_right _ _))).trans
          (le_max_left _ _)
      rw [← Real.norm_eq_abs, ← (hceq _ hn).2 a]
      exact (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (c.bd_σ a _) (norm_nonneg _))) T
  refine NativeIntegrand.congr h fun a => ?_
  filter_upwards [ae_timeProb_of_ae (T := T) hZZ'] with p hp
  simp only [stopIntegrand, functionalIntegrand, switchOff, le_min_iff]
  rw [← exitTime_eq_of_forall hp R]
  by_cases h1 : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ p.2
  · by_cases h2 : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ exitTime Z R p.2
    · simp only [h1, h2, and_self, ite_true]
    · simp only [h1, h2, and_false, ite_false, ite_true, map_zero]
  · simp only [h1, false_and, ite_false]

/-- **Uniqueness until the exit time** (second clause of `LocalWellPosednessFor`). -/
theorem ae_eq_of_isSDESolutionUntil_exitTime {b : E → E} {σ : κ → E → E}
    (hb : LocallyLipschitz b) (hσ : ∀ a, LocallyLipschitz (σ a)) {ξ : DriverSample S κ → E}
    {R : ℝ} {X Y : ℝ≥0 → DriverSample S κ → E}
    (hX : IsSDESolutionUntil μ b σ ξ (exitTime X R) X)
    (hY : IsSDESolutionUntil μ b σ ξ (exitTime Y R) Y) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, X t x = Y t x := by
  classical
  obtain ⟨hXi, hX0⟩ := hX
  obtain ⟨hYi, hY0⟩ := hY
  obtain ⟨X', hX'a, hX'c, hXX'⟩ := exists_continuous_modification hXi.adapted hXi.continuous
  obtain ⟨Y', hY'a, hY'c, hYY'⟩ := exists_continuous_modification hYi.adapted hYi.continuous
  set eX := exitTimeOf X' R
  set eY := exitTimeOf Y' R
  have heX : IsStoppingTime (driverAugmented (κ := κ) μ) eX := isStoppingTime_exitTimeOf hX'a hX'c R
  have heY : IsStoppingTime (driverAugmented (κ := κ) μ) eY := isStoppingTime_exitTimeOf hY'a hY'c R
  have hR₁ : (0 : ℝ) < max R 1 := lt_max_of_lt_right one_pos
  have h0 : ∀ᵐ x ∂driverLaw (κ := κ) μ, X 0 x = Y 0 x := by
    filter_upwards [hX0, hY0] with x h1 h2
    rw [h1, h2]
  have hβX : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ T : ℝ≥0, AEStronglyMeasurable
      (fun s : ℝ => switchOff (exitTime X R) (fun t x => b (X t x)) s.toNNReal x)
      (volume.restrict (Ioc 0 (T : ℝ))) := by
    filter_upwards [hXi.continuous] with x hx T
    exact aesm_switchOff_path hb.continuous hx _ T
  have hβY : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ T : ℝ≥0, AEStronglyMeasurable
      (fun s : ℝ => switchOff (exitTime Y R) (fun t x => b (Y t x)) s.toNNReal x)
      (volume.restrict (Ioc 0 (T : ℝ))) := by
    filter_upwards [hYi.continuous] with x hx T
    exact aesm_switchOff_path hb.continuous hx _ T
  have hnX : ∀ {τ : DriverSample S κ → WithTop ℝ≥0},
      IsStoppingTime (driverAugmented (κ := κ) μ) τ → ∀ T,
      StoppedIdentity μ T τ X (switchOff (exitTime X R) fun t x => b (X t x))
        (fun a => switchOff (exitTime X R) fun t x => σ a (X t x)) := fun hτ T =>
    IsNativeItoProcess.stoppedIdentity hXi hτ T fun ℓ =>
      nativeIntegrand_switched hb hσ hXi.adapted hXi.continuous hX'c hXX' heX hτ ℓ T
  have hnY : ∀ {τ : DriverSample S κ → WithTop ℝ≥0},
      IsStoppingTime (driverAugmented (κ := κ) μ) τ → ∀ T,
      StoppedIdentity μ T τ Y (switchOff (exitTime Y R) fun t x => b (Y t x))
        (fun a => switchOff (exitTime Y R) fun t x => σ a (Y t x)) := fun hτ T =>
    IsNativeItoProcess.stoppedIdentity hYi hτ T fun ℓ =>
      nativeIntegrand_switched hb hσ hYi.adapted hYi.continuous hY'c hYY' heY hτ ℓ T
  -- step 1: agreement up to `ρ = e_X ∧ e_Y`
  have hρ : IsStoppingTime (driverAugmented (κ := κ) μ) (fun x => min (eX x) (eY x)) := heX.min heY
  have hstop := stoppedProcess_ae_eq_local hb hσ hR₁ hρ hXi.adapted hYi.adapted hXi.continuous
    hYi.continuous h0 (hnX hρ) (hnY hρ) (by
      filter_upwards [hXX', hYY'] with x hx hy s hs0 hs
      left
      have h1 : (s : WithTop ℝ≥0) ≤ exitTime X R x := by
        rw [exitTime_eq_of_forall hx R]
        exact hs.trans (min_le_left _ _)
      have h2 : (s : WithTop ℝ≥0) ≤ exitTime Y R x := by
        rw [exitTime_eq_of_forall hy R]
        exact hs.trans (min_le_right _ _)
      refine ⟨?_, ?_, by simp only [switchOff, h1, ite_true], by simp only [switchOff, h2, ite_true],
        fun a => ⟨by simp only [switchOff, h1, ite_true], by simp only [switchOff, h2, ite_true]⟩⟩
      · rw [← hx s]
        exact (norm_le_of_le_exitTimeOf (hX'c x) hs0 (hs.trans (min_le_left _ _))).trans
          (le_max_left _ _)
      · rw [← hy s]
        exact (norm_le_of_le_exitTimeOf (hY'c x) hs0 (hs.trans (min_le_right _ _))).trans
          (le_max_left _ _)) hβX hβY
  have hstopAll := indistinguishable_of_continuous
    (hXi.continuous.mono fun x hx => continuous_stoppedProcess hx _)
    (hYi.continuous.mono fun x hx => continuous_stoppedProcess hx _) hstop
  -- step 2: the exit times agree
  have heq : ∀ᵐ x ∂driverLaw (κ := κ) μ, eX x = eY x := by
    filter_upwards [hXX', hYY', hstopAll] with x hx hy hs
    have key : ∀ m : ℝ≥0, (m : WithTop ℝ≥0) ≤ min (eX x) (eY x) →
        X' m x = Y' m x := fun m hm => by
      have := hs m
      rw [stoppedProcess_eq_of_le (u := X) (τ := fun x => min (eX x) (eY x)) hm,
        stoppedProcess_eq_of_le (u := Y) (τ := fun x => min (eX x) (eY x)) hm] at this
      rw [hx, hy, this]
    apply le_antisymm
    · by_contra hlt
      rw [not_le] at hlt
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
      have hmin : min (eX x) (eY x) = m := by rw [min_eq_right hlt.le, hm]
      have hY'm := le_norm_exitTimeOf (hY'c x) hm.symm
      rw [← key m hmin.ge] at hY'm
      have := exitTimeOf_le (X := X') (x := x) hY'm
      exact absurd (this.trans_eq hm) (not_le.2 hlt)
    · by_contra hlt
      rw [not_le] at hlt
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
      have hmin : min (eX x) (eY x) = m := by rw [min_eq_left hlt.le, hm]
      have hX'm := le_norm_exitTimeOf (hX'c x) hm.symm
      rw [key m hmin.ge] at hX'm
      have := exitTimeOf_le (X := Y') (x := x) hX'm
      exact absurd (this.trans_eq hm) (not_le.2 hlt)
  -- step 3: full agreement with `ρ = ⊤`
  have hall := stoppedProcess_ae_eq_local hb hσ hR₁ (isStoppingTime_top (μ := μ)) hXi.adapted
    hYi.adapted hXi.continuous hYi.continuous h0 (hnX (isStoppingTime_top (μ := μ)))
    (hnY (isStoppingTime_top (μ := μ))) (by
      filter_upwards [hXX', hYY', heq] with x hx hy he s hs0 _
      have hXx : exitTime X R x = eX x := exitTime_eq_of_forall hx R
      have hYx : exitTime Y R x = eY x := exitTime_eq_of_forall hy R
      by_cases hsX : (s : WithTop ℝ≥0) ≤ eX x
      · have hsY : (s : WithTop ℝ≥0) ≤ eY x := he ▸ hsX
        left
        refine ⟨?_, ?_, by simp only [switchOff, hXx, hsX, ite_true],
          by simp only [switchOff, hYx, hsY, ite_true], fun a =>
          ⟨by simp only [switchOff, hXx, hsX, ite_true],
            by simp only [switchOff, hYx, hsY, ite_true]⟩⟩
        · rw [← hx s]
          exact (norm_le_of_le_exitTimeOf (hX'c x) hs0 hsX).trans (le_max_left _ _)
        · rw [← hy s]
          exact (norm_le_of_le_exitTimeOf (hY'c x) hs0 hsY).trans (le_max_left _ _)
      · have hsY : ¬ (s : WithTop ℝ≥0) ≤ eY x := he ▸ hsX
        right
        refine ⟨by simp only [switchOff, hXx, hsX, ite_false],
          by simp only [switchOff, hYx, hsY, ite_false], fun a =>
          ⟨by simp only [switchOff, hXx, hsX, ite_false],
            by simp only [switchOff, hYx, hsY, ite_false]⟩⟩) hβX hβY
  have hst (Z : ℝ≥0 → DriverSample S κ → E) (t : ℝ≥0) :
      stoppedProcess Z (fun _ => ⊤) t = Z t := funext fun _ => stoppedProcess_eq_of_le le_top
  refine indistinguishable_of_continuous hXi.continuous hYi.continuous fun t => ?_
  have := hall t
  rwa [hst, hst] at this

end BlockBand.SourceProcess.Stochastic.NativeSDE
