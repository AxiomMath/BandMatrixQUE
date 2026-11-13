module

public import BlockBand.Endpoints.Response.BridgeOccupationProofConsumer

/-!
# Nonzero response from the measurable bridge-occupation statement

This file restates the corollaries of the nonzero-response proposition with
`BridgeOccupationMeasStatement` in place of `BridgeOccupationStatement`.
`bridgeOccupationMeas_of_bridgeOccupation` shows that the measurable statement is weaker, so these
corollaries have weaker hypotheses than the originals.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform

/-- The measurable statement is weaker: `BridgeOccupationStatement` (every version `p`) implies
`BridgeOccupationMeasStatement` (every jointly measurable version `p`). -/
theorem bridgeOccupationMeas_of_bridgeOccupation (hOcc : BridgeOccupationStatement) :
    BridgeOccupationMeasStatement := by
  intro κ hκ
  obtain ⟨c, hc, C, hC, r₁, H⟩ := hOcc κ hκ
  exact ⟨c, hc, C, hC, r₁, fun D0 τ hD0 hτ hDτ p hp _ => H D0 τ hD0 hτ hDτ p hp⟩

/-- Every value of the signed response at the detecting start is positive (uniqueness of the
value, `rv_isSignedResponse_unique`); `nonzeroResponse_all` with the measurable occupation
statement. -/
theorem nonzeroResponse_all_of_occMeas (hBdry : DualBoundaryStartContract)
    (hLB : LifetimeBridgeStatement) (hOccM : BridgeOccupationMeasStatement) {D0 τ : ℝ}
    (hD0 : 0 < D0) (hτ : 0 < τ) {m : ℤ}
    (hm : m ≠ 0) : ∃ x : ℝ, 0 < x ∧ (∃ J, IsSignedResponse D0 τ (rvCosineTest τ m) x 0 J) ∧
      ∀ J, IsSignedResponse D0 τ (rvCosineTest τ m) x 0 J → 0 < J := by
  obtain ⟨x, hx, J, hJ, hS⟩ := nonzeroResponse_of_occMeas hBdry hLB hOccM D0 hD0 τ hτ m hm
  exact ⟨x, hx, ⟨J, hS⟩, fun J' hS' => (rv_isSignedResponse_unique hS hS').symm ▸ hJ⟩

/-- The instance `D₀ = transportD0 b E` (fixed `0 < b`, bulk `E`), the `J_{τ,m}` of
`responseVariance`; `nonzeroResponse_transport` with the measurable occupation statement. -/
theorem nonzeroResponse_transport_of_occMeas (hBdry : DualBoundaryStartContract)
    (hLB : LifetimeBridgeStatement) (hOccM : BridgeOccupationMeasStatement) {b E : ℝ}
    (hb : 0 < b) (hE1 : -2 < E) (hE2 : E < 2) {τ : ℝ} (hτ : 0 < τ) {m : ℤ} (hm : m ≠ 0) :
    ∃ x : ℝ, 0 < x ∧ (∃ J, IsSignedResponse (transportD0 b E) τ (rvCosineTest τ m) x 0 J) ∧
      ∀ J, IsSignedResponse (transportD0 b E) τ (rvCosineTest τ m) x 0 J → 0 < J :=
  nonzeroResponse_all_of_occMeas hBdry hLB hOccM (transportD0_pos hb hE1 hE2) hτ hm

end BlockBand.Endpoints
