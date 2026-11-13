module

public import BlockBand.Transmission.PassiveLayer.BilMain
public import BlockBand.Transmission.PassiveLayer.FlucMain

/-!
# Assembly of the passive bounds lemma

`passiveBounds_of_traceMatrix`: `PassiveBoundsStatement` from `GaussianAbsorptionContract`,
`GaussianLpGradient` and the `traceMatrix` clause `TraceMatrixClause`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

/-- The `traceMatrix` field of `PassiveBoundsStatement` (proved by `traceMatrix_holds`). -/
def TraceMatrixClause : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ (Lw : ℕ) (Kd : ℝ),
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ w ∈ paramDisk b E,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ (ℓf ℓU : ℕ), ℓf ≤ Lw → ℓU ≤ Lw →
      ∀ (wf : Fin ℓf → Fin 6 × Bool) (Df : Fin (ℓf + 1) → Matrix (Fin W) (Fin W) ℂ)
        (wU : Fin ℓU → Fin 6 × Bool) (DU : Fin (ℓU + 1) → Matrix (Fin W) (Fin W) ℂ),
        (∀ j, ‖Df j‖ ≤ Kd) → (∀ j, ‖DU j‖ ≤ Kd) →
        let μ := freshLaw W b
        let f : LayerSample W .oneBlockOnePort → ℂ := fun ω =>
          (W : ℂ)⁻¹ * (passiveWord E w X wf Df ω).trace
        let U : LayerSample W .oneBlockOnePort → Matrix (Fin W) (Fin W) ℂ :=
          passiveWord E w X wU DU
        Integrable f μ ∧ (∀ x y, Integrable (fun ω => U ω x y) μ) ∧
          (∀ x y, Integrable (fun ω => f ω * U ω x y) μ) ∧
          ‖matrixExpect μ (fun ω => f ω • U ω) - (∫ ω, f ω ∂μ) • matrixExpect μ U‖ ≤
            C / (W : ℝ) ^ 2

/-- The passive bounds lemma from `GaussianAbsorptionContract`, `GaussianLpGradient` and
`TraceMatrixClause`. -/
theorem passiveBounds_of_traceMatrix (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (htr : TraceMatrixClause) : PassiveBoundsStatement :=
  ⟨moments_holds hGA, htr, bilinear_holds hGA hLp⟩

end BlockBand.Transmission.PassiveLayer
