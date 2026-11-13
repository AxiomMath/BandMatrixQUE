module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# The passive covariance lemma, uniform in the bulk energy

The bilinear covariance of `U = LL*` for one fresh one-port layer at a passive input, with
constants uniform over energies in a compact bulk set.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.TransmissionUniform4
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ComplexConjugate ComplexOrder Matrix

/-- **The passive covariance lemma, uniform on compact bulk sets.** Fixed `b`, the bulk
margin `κ` first, then `C, W₀`. For `W ≥ W₀`, every `E ∈ bulkInterval κ`, every stationary jet `s`
at `E`, every deterministic passive old input `X` (`Y = -Im X ⪰ 0`) and four deterministic vectors,
with `U = LL*` of one fresh one-port layer and `U⁰ = U - E(U ∣ X)`:
`|E[(v₁*U⁰v₂)(v₃*U⁰v₄)] - {(D₀/2W)[I⊗(I-T) + (I-T)⊗I] + (σ₋/W) f⊗f + (σ̄₋/W) f*⊗f*}|
 ≤ C[W⁻² + W⁻¹(δ₀ + δ₁ + q/W)] ∏‖v_j‖`, `A⊗B = (v₁*Av₄)(v₃*Bv₂)`, `T, f, q, δ₀, δ₁` of `X`. -/
def PassiveCovarianceEnergyUniformContract : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
      ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
        ∀ s : ℂ, IsStationaryJet b E s → ∀ X : Matrix (Fin W) (Fin W) ℂ,
        (passiveY X).PosSemidef → ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ,
        let T := passiveTransmission b E X
        let f := passiveF b E X
        let I : Matrix (Fin W) (Fin W) ℂ := 1
        ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
            ((((transportD0 b E / (2 * W) : ℝ)) : ℂ) *
                (crossedTensor v₁ v₂ v₃ v₄ I (I - T) + crossedTensor v₁ v₂ v₃ v₄ (I - T) I) +
              sigmaMinus b E s / W * crossedTensor v₁ v₂ v₃ v₄ f f +
              conj (sigmaMinus b E s) / W * crossedTensor v₁ v₂ v₃ v₄ fᴴ fᴴ)‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
            (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W)) *
            fourNorm v₁ v₂ v₃ v₄

end BlockBand.Internal.Contracts.TransmissionUniform4
