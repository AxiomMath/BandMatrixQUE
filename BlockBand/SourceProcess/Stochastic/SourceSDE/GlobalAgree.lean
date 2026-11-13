module
public import BlockBand.SourceProcess.Stochastic.SDE.ExportStop
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Global solutions agree with strong exit-time solutions

Used for the last clause of `FiniteSourceWellPosed` (every global solution satisfies the
constraint at all times a.s.). Generic: `Ω = DriverSample S κ`
(any universes), `P = driverLaw μ`, augmented filtration, `E` finite-dimensional real normed with
Borel σ-algebra, `b, σ_a` locally Lipschitz.

`ae_eq_strongExit_of_isSDESolution`: if `X` is a global solution, `X'` a continuous
augmented-adapted modification of `X`, and `Z` a strong exit-time solution of radius `R > 0` (same `ξ`), then almost
surely `exit_R(Z) = exit_R(X')` and `X_t = Z_t` for all `t ≤ exit_R(Z)`.

Proof: local uniqueness (`stoppedProcess_ae_eq_local`) at `ρ = exit_R(X') ∧ exit_R(Z)`,
indistinguishability of the stopped processes, and the exit levels: at the earlier of the two
exit times one path has norm `≥ R` while the other has norm `< R`, contradicting `X = Z` on
`[0, ρ]`.
-/

namespace BlockBand.SourceProcess.Stochastic.SourceSDE
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ] {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **A global solution coincides with a strong exit-time solution until its exit time.** -/
theorem ae_eq_strongExit_of_isSDESolution {b : E → E} {σ : κ → E → E}
    (hb : LocallyLipschitz b) (hσ : ∀ a, LocallyLipschitz (σ a)) {ξ : DriverSample S κ → E}
    {X Z X' : ℝ≥0 → DriverSample S κ → E} {R : ℝ} (hR : 0 < R)
    (hX : IsSDESolution μ b σ ξ X) (hZ : IsStrongExitSolution μ b σ ξ R Z)
    (hX'a : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (X' t))
    (hX'c : ∀ x, Continuous fun t => X' t x)
    (hXX' : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, X' t x = X t x) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, exitTime Z R x = exitTimeOf X' R x ∧
      ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ exitTime Z R x → X t x = Z t x := by
  classical
  obtain ⟨hXi, hX0⟩ := hX
  set ρ : DriverSample S κ → WithTop ℝ≥0 := fun x => min (exitTimeOf X' R x) (exitTime Z R x)
    with hρdef
  have hρ : IsStoppingTime (driverAugmented (κ := κ) μ) ρ :=
    (isStoppingTime_exitTimeOf hX'a hX'c R).min hZ.stopping
  obtain ⟨c, -, hceq⟩ := exists_truncCoeff hb hσ hR
  have hXb : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ x →
      ‖X s x‖ ≤ R := by
    filter_upwards [hXX'] with x hx s hs0 hs
    rw [← hx s]
    exact norm_le_of_le_exitTimeOf (hX'c x) hs0 (hs.trans (min_le_left _ _))
  have hZb : ∀ x, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ x → ‖Z s x‖ ≤ R :=
    fun x s hs0 hs => norm_le_of_le_exitTimeOf (hZ.continuous x) hs0 (hs.trans (min_le_right _ _))
  have hXid : ∀ T, StoppedIdentity μ T ρ X (switchOff (fun _ => ⊤) fun t x => b (X t x))
      (fun a => switchOff (fun _ => ⊤) fun t x => σ a (X t x)) := by
    intro T
    refine IsNativeItoProcess.stoppedIdentity hXi hρ T fun ℓ => ?_
    have h := nativeIntegrand_stopped_bounded (μ := μ) hXi.adapted hXi.continuous hρ
      (φ := fun a y => ℓ (σ a y)) (fun a => ℓ.continuous.comp (hσ a).continuous)
      (M := ‖ℓ‖ * c.C) (by
        filter_upwards [hXb] with x hx s hs0 hs a
        rw [← Real.norm_eq_abs, ← ((hceq _ (hx s hs0 hs)).2 a)]
        exact (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (c.bd_σ a _) (norm_nonneg _))) T
    refine NativeIntegrand.congr h fun a => Eventually.of_forall fun p => ?_
    simp only [stopIntegrand, functionalIntegrand, switchOff, le_top, ite_true]
  have hZid : ∀ T, StoppedIdentity μ T ρ Z (switchOff (exitTime Z R) fun t x => b (Z t x))
      (fun a => switchOff (exitTime Z R) fun t x => σ a (Z t x)) := fun T =>
    IsNativeItoProcess.stoppedIdentity hZ.sol.1 hρ T fun ℓ =>
      nativeIntegrand_switched (μ := μ) hb hσ hZ.sol.1.adapted
        (Eventually.of_forall hZ.continuous) hZ.continuous (Eventually.of_forall fun _ _ => rfl)
        (by rw [exitTimeOf_eq_exitTime]; exact hZ.stopping) hρ ℓ T
  have hst := stoppedProcess_ae_eq_local hb hσ hR hρ hXi.adapted hZ.sol.1.adapted hXi.continuous
    (Eventually.of_forall hZ.continuous)
    (by filter_upwards [hX0] with x hx; rw [hx, hZ.init]) hXid hZid ?_ ?_ ?_
  rotate_left
  · filter_upwards [hXb] with x hx s hs0 hs
    left
    have hse : (s : WithTop ℝ≥0) ≤ exitTime Z R x := hs.trans (min_le_right _ _)
    simp only [switchOff, le_top, hse, ↓reduceIte]
    exact ⟨hx s hs0 hs, hZb x s hs0 hs, trivial, trivial, fun a => ⟨trivial, trivial⟩⟩
  · filter_upwards [hXi.continuous] with x hx T
    exact aesm_switchOff_path hb.continuous hx _ T
  · exact Eventually.of_forall fun x T => aesm_switchOff_path hb.continuous (hZ.continuous x) _ T
  have hind := indistinguishable_of_continuous
    (hXi.continuous.mono fun x hx => continuous_stoppedProcess hx ρ)
    (Eventually.of_forall fun x => continuous_stoppedProcess (hZ.continuous x) ρ) hst
  filter_upwards [hind, hXX'] with x h1 h2
  have key : ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ ρ x → X t x = Z t x := fun t ht => by
    have := h1 t
    rwa [stoppedProcess_eq_of_le ht, stoppedProcess_eq_of_le ht] at this
  have hZc := hZ.continuous x
  have heq : exitTime Z R x = exitTimeOf X' R x := by
    refine le_antisymm ?_ ?_
    · by_contra hlt
      rw [not_le] at hlt
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
      have hρm : ρ x = m := by rw [hρdef]; exact (min_eq_left hlt.le).trans hm.symm
      have h3 := le_norm_exitTimeOf (hX'c x) hm.symm
      rw [h2 m, key m hρm.ge] at h3
      have h4 : ‖Z m x‖ < R := norm_lt_of_lt_exitTimeOf (X := Z) (by rw [hm]; exact hlt)
      linarith
    · by_contra hlt
      rw [not_le] at hlt
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
      have hρm : ρ x = m := by rw [hρdef]; exact (min_eq_right hlt.le).trans hm.symm
      have h3 := le_norm_exitTimeOf (X := Z) hZc hm.symm
      rw [← key m hρm.ge, ← h2 m] at h3
      have h4 : ‖X' m x‖ < R := norm_lt_of_lt_exitTimeOf (by rw [hm]; exact hlt)
      linarith
  refine ⟨heq, fun t ht => key t ?_⟩
  rw [hρdef]
  exact le_min (heq ▸ ht) ht

end BlockBand.SourceProcess.Stochastic.SourceSDE
