module
public import BlockBand.SourceProcess.Stochastic.RotationFlow.Existence
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Uniqueness of the rotation flow

Matrices carry the Frobenius norm; `Ω = DriverSample S ((Fin N × Fin N) × Fin 2)`,
`P = driverLaw μ`. Coefficients `r` (continuous, symmetric, `≥ 0`) and `κ` (continuous, `≥ 0`).

* `isRotationFlow_stoppedIdentity_top`: the identity at `ρ = ⊤` on every horizon (the
  stopped diffusion is bounded along the contracted paths, `nativeIntegrand_coeff_ae`).
* `isRotationFlow_unique`: two rotation flows with the same start are indistinguishable
  (`stoppedProcess_ae_eq_of_lipschitz` with `ρ = ⊤`: the coefficients `A_t M`, `Σ_{α,t} M` are
  `K`-Lipschitz in `M` and bounded by `K ‖1‖` along the contracted paths; then path continuity).
-/

namespace BlockBand.SourceProcess.Stochastic.RotationFlow
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.Stochastic.NativeSDE BlockBand.SourceProcess.Stochastic.Integral
open BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.Internal.Contracts.TransmissionFlow

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace

variable {N : ℕ} {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
variable {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ} {a c s : ℝ}

theorem continuous_noiseCoeff (hac : a ≤ c) (hrc : ContinuousOn r (Set.Icc a c))
    (α : (Fin N × Fin N) × Fin 2) :
    Continuous fun q : ℝ≥0 × Matrix (Fin N) (Fin N) ℂ => noiseAt r a c s α q.1 * q.2 := by
  have h := ((continuous_noiseAt s hac hrc α).comp
    (@continuous_fst ℝ≥0 (Matrix (Fin N) (Fin N) ℂ) _ _)).matrix_mul
    (@continuous_snd ℝ≥0 (Matrix (Fin N) (Fin N) ℂ) _ _)
  exact h

/-- The identity of a rotation flow at `ρ = ⊤`, on every horizon. -/
theorem isRotationFlow_stoppedIdentity_top (hac : a ≤ c) (hrc : ContinuousOn r (Set.Icc a c))
    (hκc : ContinuousOn κ (Set.Icc a c)) (hs : ∀ x k l, r x k l = r x l k)
    (hr : ∀ x k l, 0 ≤ r x k l) (hk : ∀ x k, 0 ≤ κ x k)
    {M : ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ} (hM : IsRotationFlow μ r κ a c s M)
    (T : ℝ≥0) :
    StoppedIdentity μ T (fun _ => ⊤) M
      (fun t x => rotationDrift (r (clampTime a c (s + t))) (κ (clampTime a c (s + t))) * M t x)
      (fun α t x => rotationNoise (r (clampTime a c (s + t))) α * M t x) := by
  obtain ⟨K, hK0, hK⟩ := exists_coeff_bound hac hrc hκc
  refine NativeSDE.IsNativeItoProcess.stoppedIdentity hM.1 isStoppingTime_top T fun ℓ => ?_
  have h := nativeIntegrand_coeff_ae (μ := μ) (σ := fun α t M => noiseAt r a c s α t * M)
    (fun α => continuous_noiseCoeff hac hrc α) hM.1.adapted hM.1.continuous
    (C := K * ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖) (by
      filter_upwards [isRotationFlow_norm_le hs hr hk hM] with x hx α t
      exact (frobenius_norm_mul _ _).trans (mul_le_mul ((hK s t).2 α) (hx t) (norm_nonneg _) hK0))
    ℓ T
  exact h

/-- **Uniqueness of the rotation flow**: any two are indistinguishable. -/
theorem isRotationFlow_unique (hac : a ≤ c) (hrc : ContinuousOn r (Set.Icc a c))
    (hκc : ContinuousOn κ (Set.Icc a c)) (hs : ∀ x k l, r x k l = r x l k)
    (hr : ∀ x k l, 0 ≤ r x k l) (hk : ∀ x k, 0 ≤ κ x k)
    {M M' : ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ} (hM : IsRotationFlow μ r κ a c s M)
    (hM' : IsRotationFlow μ r κ a c s M') :
    ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ, ∀ t, M t x = M' t x := by
  obtain ⟨K, hK0, hK⟩ := exists_coeff_bound hac hrc hκc
  have hb := isRotationFlow_norm_le hs hr hk hM
  have hb' := isRotationFlow_norm_le hs hr hk hM'
  set C : ℝ := K * ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖
  have hpath : ∀ {X : ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ} {x : FlowSample S N}
      (T : ℝ≥0), Continuous (fun t => X t x) → AEStronglyMeasurable (fun u : ℝ =>
        rotationDrift (r (clampTime a c (s + u.toNNReal))) (κ (clampTime a c (s + u.toNNReal))) *
          X u.toNNReal x) (volume.restrict (Ioc 0 (T : ℝ))) := fun {X x} T hx => by
    have h := ((continuous_driftAt s hac hrc hκc).comp continuous_real_toNNReal).matrix_mul
      (hx.comp continuous_real_toNNReal)
    have : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin N) (Fin N) ℂ) :=
      matrixPseudoMetrizable
    exact h.aestronglyMeasurable
  have heach : ∀ t : ℝ≥0, M t =ᵐ[driverLaw (κ := (Fin N × Fin N) × Fin 2) μ] M' t := by
    intro t
    have heq := stoppedProcess_ae_eq_of_lipschitz (isStoppingTime_top (μ := μ)) hM.1.adapted
      hM'.1.adapted hM.1.continuous hM'.1.continuous
      (Eventually.of_forall fun x => by rw [hM.2 x, hM'.2 x])
      (isRotationFlow_stoppedIdentity_top hac hrc hκc hs hr hk hM t)
      (isRotationFlow_stoppedIdentity_top hac hrc hκc hs hr hk hM' t) (K := K) (C := C)
      (Eventually.of_forall fun x u _ _ => ⟨by
        rw [← Matrix.mul_sub]
        exact (frobenius_norm_mul _ _).trans (mul_le_mul_of_nonneg_right (hK s u).1
          (norm_nonneg _)), fun α => by
        rw [← Matrix.mul_sub]
        exact (frobenius_norm_mul _ _).trans (mul_le_mul_of_nonneg_right ((hK s u).2 α)
          (norm_nonneg _))⟩)
      (by
        filter_upwards [hb, hb'] with x hx hx' u _ _
        exact ⟨(frobenius_norm_mul _ _).trans (mul_le_mul (hK s u).1 (hx u) (norm_nonneg _) hK0),
          (frobenius_norm_mul _ _).trans (mul_le_mul (hK s u).1 (hx' u) (norm_nonneg _) hK0),
          fun α => ⟨(frobenius_norm_mul _ _).trans (mul_le_mul ((hK s u).2 α) (hx u)
            (norm_nonneg _) hK0), (frobenius_norm_mul _ _).trans (mul_le_mul ((hK s u).2 α)
              (hx' u) (norm_nonneg _) hK0)⟩⟩)
      (by filter_upwards [hM.1.continuous] with x hx; exact hpath t hx)
      (by filter_upwards [hM'.1.continuous] with x hx; exact hpath t hx) t le_rfl
    have hst (Z : ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ) :
        stoppedProcess Z (fun _ => ⊤) t = Z t := funext fun _ => stoppedProcess_eq_of_le le_top
    rwa [hst, hst] at heq
  exact indistinguishable_of_continuous hM.1.continuous hM'.1.continuous heach

end BlockBand.SourceProcess.Stochastic.RotationFlow
