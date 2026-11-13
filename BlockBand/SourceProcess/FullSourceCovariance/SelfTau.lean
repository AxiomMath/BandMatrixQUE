module

public import BlockBand.SourceProcess.FullSourceCovariance.TraceFluc
public import BlockBand.SourceProcess.FullSourceCovariance.PhiOpp

/-!
# The self-energy scalar `τ` is a weighted trace: `‖τ - Eτ‖_p ≤ C/W`

* `selfTau_eq_tauD` (`W ≠ 0`): `τ(G) = (c/W)Tr G₁₁ + (b/W)Tr G₂₂ = W⁻¹Tr(S̃G) = τ_{S̃}(G)`,
  `S̃ = diag(c, b)` (`sTilde`, `‖S̃‖ ≤ 1`);
* **`selfTau_fluct_bulk hGA hLp`**: for `p ≥ 1`, `‖τ(𝒢) - Eτ(𝒢)‖_{L^p} ≤ C/W`, every passive `X`,
  uniformly on `bulkInterval κ` (`traceFluct_bulk`). This is the `τ⁰ = O_{L^p}(W⁻¹)` input of
  `FirstTermBound`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open Matrix MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Internal.Contracts.Inputs BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped Matrix.Norms.L2Operator ComplexOrder NNReal ENNReal

variable {W : ℕ}

theorem selfTau_eq_tauD (b : ℝ) (hW : W ≠ 0) (G : LayerMat W) :
    selfTau b G = tauD (sTilde W b) G := by
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  rw [selfTau, tauD, Matrix.trace]
  simp only [sTilde, diagonal_mul, Matrix.diag]
  rw [sum_layerSite (fun γ => (W : ℂ) * physVar W b γ * G γ γ), mul_add, Finset.mul_sum,
    Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun k _ => ?_ <;> simp only [physVar] <;> field_simp

/-- **`τ⁰ = O_{L^p}(W⁻¹)`** for the self-energy scalar (every passive `X`, bulk-uniform). -/
theorem selfTau_fluct_bulk (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) (p : ℝ) (hp : 1 ≤ p) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        eLpNorm (fun ω => selfTau b (gRes b E X ω) -
            ∫ ω', selfTau b (gRes b E X ω') ∂freshLaw W b) (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal (C / W) := by
  obtain ⟨C, W₀, hC, h⟩ := traceFluct_bulk hGA hLp hb0 hb hκ p hp
  refine ⟨C, max W₀ 1, hC, fun W hW E hE X hY => ?_⟩
  have hW0 : W ≠ 0 := by have := le_of_max_le_right hW; omega
  have e : ∀ ω, selfTau b (gRes b E X ω) = tauDLayer (sTilde W b) E (boundaryZ b E) X ω :=
    fun ω => selfTau_eq_tauD b hW0 _
  simp only [e]
  exact h W (le_of_max_le_left hW) E hE X hY _ (norm_sTilde_le hb0 hb)

end BlockBand.SourceProcess.FullSourceCovariance
