module
public import BlockBand.SourceProcess.Stochastic.SDE.NativeLocal
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Pathwise uniqueness for locally Lipschitz coefficients

`Ω = DriverSample S κ`, `P = driverLaw μ`, augmented filtration `F_t ∨ N`.

* `stoppedProcess_ae_eq_local`: two processes with identities at the same stopping
  time `ρ`, whose coefficient processes on `{0 < s ≤ ρ}` are either the true coefficients
  `b, σ` evaluated inside the closed `R`-ball or both switched off, agree at `t ∧ ρ` a.s.
  (truncation + `stoppedProcess_ae_eq_of_lipschitz`).
* `ae_eq_of_isSDESolution`: **global pathwise uniqueness** (third clause of
  `LocalWellPosednessFor`), localizing at the exit times of continuous modifications from
  the balls of radius `n + 1`.
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

/-- **Local uniqueness core.** -/
theorem stoppedProcess_ae_eq_local {b : E → E} {σ : κ → E → E} (hb : LocallyLipschitz b)
    (hσ : ∀ a, LocallyLipschitz (σ a)) {R : ℝ} (hR : 0 < R) {ρ : DriverSample S κ → WithTop ℝ≥0}
    (hρ : IsStoppingTime (driverAugmented (κ := κ) μ) ρ)
    {X Y β β' : ℝ≥0 → DriverSample S κ → E} {γ γ' : κ → ℝ≥0 → DriverSample S κ → E}
    (hXa : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (X t))
    (hYa : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (Y t))
    (hXc : ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => X t x)
    (hYc : ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => Y t x)
    (h0 : ∀ᵐ x ∂driverLaw (κ := κ) μ, X 0 x = Y 0 x)
    (hX : ∀ T, StoppedIdentity μ T ρ X β γ) (hY : ∀ T, StoppedIdentity μ T ρ Y β' γ')
    (hco : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ x →
      (‖X s x‖ ≤ R ∧ ‖Y s x‖ ≤ R ∧ β s x = b (X s x) ∧ β' s x = b (Y s x) ∧
        ∀ a, γ a s x = σ a (X s x) ∧ γ' a s x = σ a (Y s x)) ∨
      (β s x = 0 ∧ β' s x = 0 ∧ ∀ a, γ a s x = 0 ∧ γ' a s x = 0))
    (hβ : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ T : ℝ≥0,
      AEStronglyMeasurable (fun s : ℝ => β s.toNNReal x) (volume.restrict (Ioc 0 (T : ℝ))))
    (hβ' : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ T : ℝ≥0,
      AEStronglyMeasurable (fun s : ℝ => β' s.toNNReal x) (volume.restrict (Ioc 0 (T : ℝ)))) :
    ∀ t, stoppedProcess X ρ t =ᵐ[driverLaw (κ := κ) μ] stoppedProcess Y ρ t := by
  obtain ⟨c, hC0, hceq⟩ := exists_truncCoeff hb hσ hR
  intro t
  refine stoppedProcess_ae_eq_of_lipschitz hρ hXa hYa hXc hYc h0 (hX t) (hY t) (K := c.K)
    (C := c.C) ?_ ?_ (hβ.mono fun x h => h t) (hβ'.mono fun x h => h t) t le_rfl
  · filter_upwards [hco] with x hx s hs0 hs
    rcases hx s hs0 hs with ⟨hXR, hYR, h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rw [h1, h2, ← (hceq _ hXR).1, ← (hceq _ hYR).1]
      refine ⟨norm_sub_le_of_lip c.lip_b _ _, fun a => ?_⟩
      rw [(h3 a).1, (h3 a).2, ← (hceq _ hXR).2 a, ← (hceq _ hYR).2 a]
      exact norm_sub_le_of_lip (c.lip_σ a) _ _
    · have hK : 0 ≤ (c.K : ℝ) * ‖X s x - Y s x‖ := mul_nonneg c.K.2 (norm_nonneg _)
      refine ⟨by rw [h1, h2, sub_zero, norm_zero]; exact hK, fun a => ?_⟩
      rw [(h3 a).1, (h3 a).2, sub_zero, norm_zero]
      exact hK
  · filter_upwards [hco] with x hx s hs0 hs
    rcases hx s hs0 hs with ⟨hXR, hYR, h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rw [h1, h2, ← (hceq _ hXR).1, ← (hceq _ hYR).1]
      refine ⟨c.bd_b _, c.bd_b _, fun a => ?_⟩
      rw [(h3 a).1, (h3 a).2, ← (hceq _ hXR).2 a, ← (hceq _ hYR).2 a]
      exact ⟨c.bd_σ a _, c.bd_σ a _⟩
    · rw [h1, h2, norm_zero]
      exact ⟨hC0, hC0, fun a => by rw [(h3 a).1, (h3 a).2, norm_zero]; exact ⟨hC0, hC0⟩⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
omit [MeasurableSpace S] [Fintype κ] in
/-- Exit times computed from a modification agree with the original ones off a null set. -/
theorem exitTime_eq_of_forall {X X' : ℝ≥0 → DriverSample S κ → E} {x : DriverSample S κ}
    (hx : ∀ t, X' t x = X t x) (R : ℝ) : exitTime X R x = exitTimeOf X' R x := by
  simp only [exitTime, exitTimeOf, hx]

omit [MeasurableSpace S] [Fintype κ] in
/-- Measurability in time of a switched continuous drift path. -/
theorem aesm_switchOff_path {b : E → E} (hb : Continuous b) {X : ℝ≥0 → DriverSample S κ → E}
    {x : DriverSample S κ} (hx : Continuous fun t => X t x) (e : DriverSample S κ → WithTop ℝ≥0)
    (T : ℝ≥0) : AEStronglyMeasurable (fun s : ℝ => switchOff e (fun t x => b (X t x)) s.toNNReal x)
      (volume.restrict (Ioc 0 (T : ℝ))) :=
  (Measurable.ite (measurableSet_toNNReal_le (e x))
    (hb.comp (hx.comp continuous_real_toNNReal)).measurable measurable_const).aestronglyMeasurable

/-- **Global pathwise uniqueness** (third clause of `LocalWellPosednessFor`). -/
theorem ae_eq_of_isSDESolution {b : E → E} {σ : κ → E → E} (hb : LocallyLipschitz b)
    (hσ : ∀ a, LocallyLipschitz (σ a)) {ξ : DriverSample S κ → E}
    {X Y : ℝ≥0 → DriverSample S κ → E} (hX : IsSDESolution μ b σ ξ X)
    (hY : IsSDESolution μ b σ ξ Y) : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, X t x = Y t x := by
  classical
  obtain ⟨hXi, hX0⟩ := hX
  obtain ⟨hYi, hY0⟩ := hY
  obtain ⟨X', hX'a, hX'c, hXX'⟩ := exists_continuous_modification hXi.adapted hXi.continuous
  obtain ⟨Y', hY'a, hY'c, hYY'⟩ := exists_continuous_modification hYi.adapted hYi.continuous
  set ρ : ℕ → DriverSample S κ → WithTop ℝ≥0 := fun n x =>
    min (exitTimeOf X' ((n + 1 : ℕ) : ℝ) x) (exitTimeOf Y' ((n + 1 : ℕ) : ℝ) x)
  have hρ : ∀ n, IsStoppingTime (driverAugmented (κ := κ) μ) (ρ n) := fun n =>
    (isStoppingTime_exitTimeOf hX'a hX'c _).min (isStoppingTime_exitTimeOf hY'a hY'c _)
  have hball : ∀ n, ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ n x →
      ‖X s x‖ ≤ ((n + 1 : ℕ) : ℝ) ∧ ‖Y s x‖ ≤ ((n + 1 : ℕ) : ℝ) := fun n => by
    filter_upwards [hXX', hYY'] with x hx hy s hs0 hs
    rw [← hx s, ← hy s]
    exact ⟨norm_le_of_le_exitTimeOf (hX'c x) hs0 (hs.trans (min_le_left _ _)),
      norm_le_of_le_exitTimeOf (hY'c x) hs0 (hs.trans (min_le_right _ _))⟩
  have hnative : ∀ (n : ℕ) {Z : ℝ≥0 → DriverSample S κ → E}
      (hZ : IsNativeItoProcess μ Z (switchOff (fun _ => ⊤) fun t x => b (Z t x))
        (fun a => switchOff (fun _ => ⊤) fun t x => σ a (Z t x)))
      (hZb : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ n x →
        ‖Z s x‖ ≤ ((n + 1 : ℕ) : ℝ)) (T : ℝ≥0),
      StoppedIdentity μ T (ρ n) Z (switchOff (fun _ => ⊤) fun t x => b (Z t x))
        (fun a => switchOff (fun _ => ⊤) fun t x => σ a (Z t x)) := by
    intro n Z hZ hZb T
    obtain ⟨c, -, hceq⟩ := exists_truncCoeff hb hσ (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))
    refine IsNativeItoProcess.stoppedIdentity hZ (hρ n) T fun ℓ => ?_
    have h := nativeIntegrand_stopped_bounded (μ := μ) hZ.adapted hZ.continuous (hρ n)
      (φ := fun a y => ℓ (σ a y)) (fun a => ℓ.continuous.comp (hσ a).continuous)
      (M := ‖ℓ‖ * c.C) (by
        filter_upwards [hZb] with x hx s hs0 hs a
        rw [← Real.norm_eq_abs, ← ((hceq _ (hx s hs0 hs)).2 a)]
        exact (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (c.bd_σ a _) (norm_nonneg _))) T
    refine NativeIntegrand.congr h fun a => Eventually.of_forall fun p => ?_
    simp only [stopIntegrand, functionalIntegrand, switchOff, le_top, ite_true]
  have hstop : ∀ n t, stoppedProcess X (ρ n) t =ᵐ[driverLaw (κ := κ) μ] stoppedProcess Y (ρ n) t := by
    intro n
    refine stoppedProcess_ae_eq_local hb hσ (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)) (hρ n)
      hXi.adapted hYi.adapted hXi.continuous hYi.continuous
      (by filter_upwards [hX0, hY0] with x h1 h2; rw [h1, h2])
      (hnative n hXi ((hball n).mono fun x h s h1 h2 => (h s h1 h2).1))
      (hnative n hYi ((hball n).mono fun x h s h1 h2 => (h s h1 h2).2)) ?_ ?_ ?_
    · filter_upwards [hball n] with x hx s hs0 hs
      left
      simp only [switchOff, le_top, ite_true]
      exact ⟨(hx s hs0 hs).1, (hx s hs0 hs).2, trivial, trivial, fun a => ⟨trivial, trivial⟩⟩
    · filter_upwards [hXi.continuous] with x hx T
      exact aesm_switchOff_path hb.continuous hx _ T
    · filter_upwards [hYi.continuous] with x hx T
      exact aesm_switchOff_path hb.continuous hx _ T
  have hρtop : ∀ x, Tendsto (fun n => ρ n x) atTop (𝓝 ⊤) := by
    intro x
    have h1 := (tendsto_exitTimeOf_top (hX'c x)).comp (tendsto_add_atTop_nat 1)
    have h2 := (tendsto_exitTimeOf_top (hY'c x)).comp (tendsto_add_atTop_nat 1)
    have h3 := h1.min h2
    rw [min_self] at h3
    exact h3
  have hpt : ∀ t, X t =ᵐ[driverLaw (κ := κ) μ] Y t := by
    intro t
    filter_upwards [ae_all_iff.2 fun n => hstop n t] with x hx
    obtain ⟨n, hn⟩ := ((WithTop.tendsto_nhds_top_iff _).1 (hρtop x) t).exists
    have := hx n
    rwa [stoppedProcess_eq_of_le hn.le, stoppedProcess_eq_of_le hn.le] at this
  exact indistinguishable_of_continuous hXi.continuous hYi.continuous hpt

end BlockBand.SourceProcess.Stochastic.NativeSDE
