module
public import BlockBand.SourceProcess.Stochastic.RotationFlow.Coeff
public import BlockBand.SourceProcess.Stochastic.ItoNative.Main
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Pathwise contraction of the rotation–damping flow

Matrices carry the Frobenius norm; `Ω = DriverSample S ((Fin N × Fin N) × Fin 2)`,
`P = driverLaw μ`. Let `Y` be an Itô process with drift `λ_t A_t Y_t` and diffusion
`λ_t Σ_{α,t} Y_t`, where `A_t = rotationDrift (r_t) (κ_t)`, `Σ_{α,t} = rotationNoise r_t α`
(`r_t` symmetric `≥ 0`, `κ_t ≥ 0`) and `0 ≤ λ ≤ 1` (the radial truncation factor; `λ = 1` for the
flow itself).

`norm_le_of_rotationType`: almost surely `‖Y_t‖ ≤ ‖Y_0‖` for all `t`.

Proof: the Itô product rule (`itoProductRuleFor_holds`) for `‖Y‖² = Re Tr(YᴴY)` gives zero
diffusion (`frob_diffusion_eq_zero`, skew-Hermitian noise) and nonpositive drift
(`frob_drift_nonpos`); the identity at a fixed time then gives `‖Y_t‖² ≤ ‖Y_0‖²` a.s.,
and path continuity extends it to all `t` (`ae_forall_le_of_continuous`).
-/

namespace BlockBand.SourceProcess.Stochastic.RotationFlow
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic.NativeSDE BlockBand.SourceProcess.Stochastic.Integral
open BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.Internal.Contracts.TransmissionFlow

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace

/-- A fixed-time a.s. bound for a.s. continuous paths holds a.s. for all times. -/
theorem ae_forall_le_of_continuous {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : ℝ≥0 → Ω → ℝ} {g : Ω → ℝ} (hc : ∀ᵐ x ∂P, Continuous fun t => f t x)
    (h : ∀ t, ∀ᵐ x ∂P, f t x ≤ g x) : ∀ᵐ x ∂P, ∀ t, f t x ≤ g x := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hD := (ae_ball_iff hDc).2 fun t _ => h t
  filter_upwards [hD, hc] with x hx hcx t
  have hcl : IsClosed {t | f t x ≤ g x} := isClosed_le hcx continuous_const
  have hsub : closure D ⊆ {t | f t x ≤ g x} := hcl.closure_subset_iff.2 fun t ht => hx t ht
  exact hsub (hDd.closure_eq.symm ▸ mem_univ t)

variable {N : ℕ} {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

/-- **Contraction**: a.s. `‖Y_t‖ ≤ ‖Y_0‖` for all `t`. -/
theorem norm_le_of_rotationType {Y : ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) →
      Matrix (Fin N) (Fin N) ℂ}
    (rr : ℝ≥0 → Fin N → Fin N → ℝ) (kk : ℝ≥0 → Fin N → ℝ)
    (hs : ∀ t k l, rr t k l = rr t l k) (hr : ∀ t k l, 0 ≤ rr t k l) (hk : ∀ t k, 0 ≤ kk t k)
    (lam : ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → ℝ) (h0 : ∀ t x, 0 ≤ lam t x)
    (h1 : ∀ t x, lam t x ≤ 1)
    (hY : IsNativeItoProcess μ Y (fun t x => lam t x • (rotationDrift (rr t) (kk t) * Y t x))
      (fun α t x => lam t x • (rotationNoise (rr t) α * Y t x))) :
    ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ, ∀ t, ‖Y t x‖ ≤ ‖Y 0 x‖ := by
  have hP := ItoNative.itoProductRuleFor_holds (κ := (Fin N × Fin N) × Fin 2) μ
    (E := Matrix (Fin N) (Fin N) ℂ) (F := Matrix (Fin N) (Fin N) ℂ) (G := ℝ) _ _ _ _ _ _ hY hY
    reInner
  have hdiff : (fun (α : (Fin N × Fin N) × Fin 2) (t : ℝ≥0)
      (x : DriverSample S ((Fin N × Fin N) × Fin 2)) =>
      reInner (lam t x • (rotationNoise (rr t) α * Y t x)) (Y t x) +
        reInner (Y t x) (lam t x • (rotationNoise (rr t) α * Y t x))) = fun _ _ _ => 0 := by
    funext α t x
    exact frob_diffusion_eq_zero (rr t) (lam t x) (Y t x) α
  rw [hdiff] at hP
  set ℓ : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ
  have hzero : stopIntegrand (fun _ => ⊤) (functionalIntegrand ℓ
      (fun (_ : (Fin N × Fin N) × Fin 2) (_ : ℝ≥0)
        (_ : DriverSample S ((Fin N × Fin N) × Fin 2)) => (0 : ℝ))) = fun _ _ => 0 := by
    funext a p
    simp only [stopIntegrand, functionalIntegrand, le_top, ite_true, map_zero]
  have hsq : ∀ t, ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ,
      ‖Y t x‖ ^ 2 ≤ ‖Y 0 x‖ ^ 2 := by
    intro t
    have hG : NativeIntegrand μ t (stopIntegrand (fun _ => ⊤) (functionalIntegrand ℓ
        (fun (_ : (Fin N × Fin N) × Fin 2) (_ : ℝ≥0)
          (_ : DriverSample S ((Fin N × Fin N) × Fin 2)) => (0 : ℝ)))) := by
      rw [hzero]
      exact nativeIntegrand_zero
    obtain ⟨hs', hid⟩ := hP.identity ℓ (fun _ => ⊤) isStoppingTime_top t hG t le_rfl
    have hI : (nativeIntegralOf hs' : DriverSample S ((Fin N × Fin N) × Fin 2) → ℝ) =ᵐ[
        driverLaw (κ := (Fin N × Fin N) × Fin 2) μ] 0 := by
      rw [nativeIntegralOf_congr hs' (nativeIntegrand_zero (μ := μ) (T := t))
        (fun a => Eventually.of_forall fun p => by
          simp only [stopIntegrand, functionalIntegrand, map_zero]
          split_ifs <;> rfl), nativeIntegralOf_zero]
      exact Lp.coeFn_zero _ _ _
    filter_upwards [hid, hI] with x hx hx0
    rw [hx0, Pi.zero_apply] at hx
    have hD : stoppedDrift (fun _ => ⊤) (fun t x =>
        reInner (lam t x • (rotationDrift (rr t) (kk t) * Y t x)) (Y t x) +
          reInner (Y t x) (lam t x • (rotationDrift (rr t) (kk t) * Y t x)) +
          ∑ α, reInner (lam t x • (rotationNoise (rr t) α * Y t x))
            (lam t x • (rotationNoise (rr t) α * Y t x))) t x ≤ 0 := by
      unfold stoppedDrift
      refine integral_nonpos fun s => ?_
      simp only [le_top, ite_true]
      exact frob_drift_nonpos _ (hs _) (hr _) _ (hk _) (h0 _ _) (h1 _ _) _
    have hst : stoppedProcess (fun t x => reInner (Y t x) (Y t x)) (fun _ => ⊤) t x =
        reInner (Y t x) (Y t x) := stoppedProcess_eq_of_le le_top
    simp only [ℓ, ContinuousLinearMap.id_apply, hst] at hx
    rw [← reInner_self, ← reInner_self]
    linarith
  have hc : ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ,
      Continuous fun t => ‖Y t x‖ ^ 2 := by
    filter_upwards [hY.continuous] with x hx
    exact (continuous_norm.comp hx).pow 2
  filter_upwards [ae_forall_le_of_continuous hc hsq] with x hx t
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (hx t)

end BlockBand.SourceProcess.Stochastic.RotationFlow
