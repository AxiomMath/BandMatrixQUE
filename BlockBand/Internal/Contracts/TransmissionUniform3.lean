module

public import BlockBand.Internal.Contracts.TransmissionUniform

/-!
# The one-step clauses of the passive source-mixing lemma, uniform in the bulk energy

The one-step mean and fluctuation bounds of the passive source-mixing lemma, with constants
uniform over energies in a compact bulk set.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.TransmissionUniform3
open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix ComplexOrder Matrix.Norms.L2Operator

/-- **The one-step clauses of the passive source-mixing lemma, uniform on compact bulk sets.**
Fixed `b`; the bulk margin `κ` first.
* `oneStepMean`: then `C, W₀`. For `W ≥ W₀`, every `E ∈ bulkInterval κ`, every stationary jet `s` at
  `E` and every deterministic passive `X`,
  `‖E(Lf₊L* ∣ X) - θ_*(1 + αq/W)⁻¹ f‖ ≤ C(δ₀ + δ₁ + q/W + W⁻²)` (operator norm).
* `oneStepFluctuation`: for `p ≥ 1`, then `C, W₀`. For `W ≥ W₀`, every `E ∈ bulkInterval κ`, every
  passive `X` and all vectors `u, v`, the centered bilinear entries of `LL*` and of `Lf₊L*` have
  `L^p(freshLaw)` norm at most `C W^{-1/2}‖u‖‖v‖`. -/
structure PassiveSourceMixingEnergyUniformContract : Prop where
  oneStepMean : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ s : ℂ, IsStationaryJet b E s → ∀ X : Matrix (Fin W) (Fin W) ℂ,
        (passiveY X).PosSemidef →
        ‖matrixExpect (freshLaw W b) (freshTransportedF b E X) -
            (thetaStar b E s / (1 + alphaCoef b E * passiveMass b E X / W)) • passiveF b E X‖ ≤
          C * (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W +
            (W : ℝ)⁻¹ ^ 2)
  oneStepFluctuation : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∀ p : ℝ, 1 ≤ p → ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ u v : Fin W → ℂ,
        eLpNorm (fun ω => bilinear u (freshU b E X ω -
            matrixExpect (freshLaw W b) (freshU b E X)) v) (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) ∧
        eLpNorm (fun ω => bilinear u (freshTransportedF b E X ω -
            matrixExpect (freshLaw W b) (freshTransportedF b E X)) v) (ENNReal.ofReal p)
            (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v)

end BlockBand.Internal.Contracts.TransmissionUniform3
