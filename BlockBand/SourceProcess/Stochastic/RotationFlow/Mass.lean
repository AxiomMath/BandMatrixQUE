module
public import BlockBand.SourceProcess.Stochastic.RotationFlow.MassTools
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The second moment of the rotation flow

Matrices carry the Frobenius norm; `Ω = DriverSample S ((Fin N × Fin N) × Fin 2)`,
`P = driverLaw μ`; coefficients `r` (continuous, symmetric, `≥ 0`) and `κ` (continuous, `≥ 0`);
`M` a rotation flow started at `s`.
`m_t(k,j) = E|M_t(k,j)|²` (`secondMoment`), `L(u) = massGenerator r κ (clampTime a c (s + u⁺))`.

* `continuous_secondMoment`: `t ↦ m_t(k,j)` is continuous (dominated convergence, `|M_kj| ≤ ‖1‖`).

The sibling module proves the identity `secondMoment_eq`: for all `t ≥ 0`,
`m_t(k,j) = δ_kj + ∫_{(0,t]} ∑_l L(u)_kl m_u(l,j) du`. Proof: the Itô product rule for
`entryForm k j (M, M) = |M_kj|²` has drift `∑_l L_kl |M_lj|²` (`entry_drift_eq_massGenerator`);
take expectations in the identity at `ρ = ⊤` (bounded integrands, mean-zero integral, Fubini on
`dt ⊗ P`).
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

variable (μ) in
/-- Second moments `m_t(k,j) = E|M_t(k,j)|²` under `driverLaw μ`. -/
def secondMoment (M : ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ) (t : ℝ≥0) (k j : Fin N) :
    ℝ :=
  ∫ x, ‖M t x k j‖ ^ 2 ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ

theorem continuous_entry_sq (k j : Fin N) :
    Continuous fun Y : Matrix (Fin N) (Fin N) ℂ => ‖Y k j‖ ^ 2 := by
  have h : Continuous fun Y : Matrix (Fin N) (Fin N) ℂ => Y k j :=
    (continuous_apply j).comp (continuous_apply k)
  exact (continuous_norm.comp h).pow 2

theorem integrable_entry_sq {M : ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ}
    (hMa : ∀ t, StronglyMeasurable[driverAugmented (κ := (Fin N × Fin N) × Fin 2) μ t] (M t))
    (hb : ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ, ∀ t,
      ‖M t x‖ ≤ ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖) (t : ℝ≥0) (k j : Fin N) :
    Integrable (fun x => ‖M t x k j‖ ^ 2) (driverLaw (κ := (Fin N × Fin N) × Fin 2) μ) := by
  refine Integrable.of_bound ((continuous_entry_sq k j).comp_aestronglyMeasurable
    ((hMa t).mono ((driverAugmented (κ := (Fin N × Fin N) × Fin 2) μ).le t)).aestronglyMeasurable)
    (‖(1 : Matrix (Fin N) (Fin N) ℂ)‖ ^ 2) ?_
  filter_upwards [hb] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) ((norm_entry_le _ k j).trans (hx t)) 2

theorem continuous_secondMoment {M : ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ}
    (hMa : ∀ t, StronglyMeasurable[driverAugmented (κ := (Fin N × Fin N) × Fin 2) μ t] (M t))
    (hMc : ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ, Continuous fun t => M t x)
    (hb : ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ, ∀ t,
      ‖M t x‖ ≤ ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖) (k j : Fin N) :
    Continuous fun t => secondMoment μ M t k j := by
  refine continuous_of_dominated (bound := fun _ => ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖ ^ 2)
    (fun t => (integrable_entry_sq hMa hb t k j).aestronglyMeasurable) (fun t => ?_)
    (integrable_const _) ?_
  · filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_entry_le _ k j).trans (hx t)) 2
  · filter_upwards [hMc] with x hx
    exact (continuous_entry_sq k j).comp hx

theorem norm_one_apply_sq (k j : Fin N) :
    ‖(1 : Matrix (Fin N) (Fin N) ℂ) k j‖ ^ 2 = if k = j then 1 else 0 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem secondMoment_zero {M : ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ}
    (h0 : ∀ x, M 0 x = 1) (k j : Fin N) :
    secondMoment μ M 0 k j = if k = j then 1 else 0 := by
  simp only [secondMoment, h0, norm_one_apply_sq, integral_const, probReal_univ, one_smul]

end BlockBand.SourceProcess.Stochastic.RotationFlow
