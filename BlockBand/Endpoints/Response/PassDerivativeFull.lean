module

public import BlockBand.Endpoints.Response.PassDerivativeLimit

/-!
# The pass-derivative lemma (both clauses)

`passDerivative` combines clause 1 (`passDerivative_clause1`: uniform passage of the physical
derivative, `O(κ^{s/2} + κ)` uniformly in `W`) and clause 2 (`passDerivative_clause2`: the signed
pass derivative converges to `-4πρ_sc(E) v`, with `v` the signed response, uniformly in the
unfolded energy window).

The hypotheses of clause 1 are `FullSourceMomentsContract` and `PathFractionalInverse`; those of
clause 2 are `TransmissionLawEnergyUniformContract`, `FullSourceMomentsEnergyUniformContract`,
`DualBoundaryStartContract` and `PathFractionalInverseEnergyUniform` (the energy-window form, which
implies `PathFractionalInverse` through `PathFractionalInverseEnergyUniform.fixed`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.TransmissionUniform

/-- The pass-derivative lemma: clause 1 (uniform passage of the physical derivative) and clause 2
(the signed limit, uniformly in the unfolded window). -/
theorem passDerivative (hMom : FullSourceMomentsContract) (hInv : PathFractionalInverse)
    (hUnifLaw : TransmissionLawEnergyUniformContract)
    (hUnifMom : FullSourceMomentsEnergyUniformContract) (hBdry : DualBoundaryStartContract)
    (hInvU : PathFractionalInverseEnergyUniform) :
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
  ⟨passDerivative_clause1 hMom hInv, passDerivative_clause2 hUnifLaw hUnifMom hBdry hInvU⟩

end BlockBand.Endpoints
