module

public import BlockBand.Endpoints.Response.PassDerivativeFull
public import BlockBand.Endpoints.Response.PathFractionalInverseUniform
public import BlockBand.Endpoints.Response.PassDerivativeClause1Closed

/-!
# The pass-derivative lemma without the fractional inverse hypotheses

`passDerivative_of_contracts` proves both clauses of the pass-derivative lemma from
`FullSourceMomentsContract`, the energy-uniform transmission law and moment contracts,
`DualBoundaryStartContract` and `ConditionalBlockGUECount`; the fractional inverse moments
`PathFractionalInverse` and `PathFractionalInverseEnergyUniform` are derived from the GUE count.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.TransmissionUniform BlockBand.Internal.Contracts.Inputs

/-- **The pass-derivative lemma**, clauses 1 and 2, from `FullSourceMomentsContract`,
`TransmissionLawEnergyUniformContract`, `FullSourceMomentsEnergyUniformContract`,
`DualBoundaryStartContract` and `ConditionalBlockGUECount`.
The statement is that of `passDerivative`.
-/
theorem passDerivative_of_contracts (hMom : FullSourceMomentsContract)
    (hUnifLaw : TransmissionLawEnergyUniformContract)
    (hUnifMom : FullSourceMomentsEnergyUniformContract) (hBdry : DualBoundaryStartContract)
    (hCount : ConditionalBlockGUECount) :
    (∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
      ∀ τ : ℝ, 0 < τ → ∀ j : ℕ → ℕ, Tendsto (fun W : ℕ => (j W : ℝ) / W) atTop (𝓝 τ) →
      ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → y < 1 →
      ∀ q : ℝ → ℝ, (∀ t, 0 ≤ q t) → BddAbove (Set.range q) →
      ∀ s : ℝ, 0 < s → s < 1 →
      ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ κ : ℝ, 0 < κ →
        |(∫ ω, (portRatioSum b E x y W (j W) q κ ω - portRatioSum b E x y W (j W) q 0 ω) / κ
            ∂growthPathLaw W b) -
          ∫ ω, derivWithin (fun κ' => portRatioSum b E x y W (j W) q κ' ω) (Set.Ici 0) 0
            ∂growthPathLaw W b| ≤ C * (κ ^ (s / 2) + κ)) ∧
    (∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
      ∀ τ : ℝ, 0 < τ → ∀ j : ℕ → ℕ, Tendsto (fun W : ℕ => (j W : ℝ) / W) atTop (𝓝 τ) →
      ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → y < 1 →
      ∀ q : ℝ → ℝ, Continuous q → (∃ Q : ℝ, ∀ t, |q t| ≤ Q) →
      ∃ v : ℝ, IsSignedResponse (transportD0 b E) τ (fun s => q s + q (τ - s)) x y v ∧
        ∀ U : ℝ, ∀ ε : ℝ, 0 < ε → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ u ∈ Icc (-U) U,
          |signedPassDerivative b (unfoldedEnergy E W (j W) u) x y W (j W) q +
            4 * Real.pi * Parameters.semicircleDensity E * v| ≤ ε) :=
  passDerivative hMom (pathFractionalInverse_of_contracts hCount) hUnifLaw hUnifMom hBdry
    (pathFractionalInverseEnergyUniform_of_contracts hCount)

end BlockBand.Endpoints
