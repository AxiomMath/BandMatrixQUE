module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# The first-jet path moments: statement

## The statement in the paper

The first-jet contraction together with the matched traces theorem gives
`‖δ₀‖_{L^p} + ‖δ₁‖_{L^p} ≤ C_p/W`, `δ₀ = |W⁻¹Tr R - a|`, `δ₁ = |∂_z(W⁻¹Tr R) - s_*|`,
after `C_p log W` layers, the derivative holding the far absorber fixed; fixed high moments pay
exits over `O(W)` layers.

## Lean reading

* **Measure and path.** The unabsorbed near-end-grown path under `growthPathLaw W b` (the same
  object as `PassiveInitialScalarContract.moment`), `R = R_r = (z - X_r)⁻¹`,
  `X_r = pathX b E W r` (far port eliminated with the matched lead `z = z_∂(E)`; `κ ≡ 0`).
* **The jet.** `δ_{1,r} = jetDistance1 b E s (pathX b E W r ω)`: the complex derivative of
  `w ↦ W⁻¹Tr(w - X_r)⁻¹` at `w = z`, with `X_r` (hence the far absorber) held fixed.
  `s` is any solution of the stationary jet equation (`IsStationaryJet`; it exists and is unique
  on the disk `|s| ≤ d_*`; existence: `PassiveCovariance.stationaryJet_exists`).
* **Quantifiers.** `0 < b < 1/2`, a bulk interval `bulkInterval κ` (`κ > 0`) and `p ≥ 1` first;
  then the layer constant `C₁` ("`C_p log W` layers": it may depend on `b, κ, p`, **not** on
  `T`); then the horizon `T`; then `C = C_{p,T}` and `W₀`. For `W ≥ W₀`, every `E` in the bulk
  interval (uniformly), every stationary jet `s` and every length `r` with `1 ≤ r`,
  `C₁ log W ≤ r ≤ TW`, the sum of the two `L^p` norms is `≤ C/W`.
  - the upper range `r ≤ TW` with `C` depending on `T` is that of the matched traces theorem
    (whose `δ₀` bound is used) and of the exits over `O(W)` layers; all later uses have lengths
    `r ≥ εW`;
  - uniformity in `E ∈ bulkInterval κ` matches `PassiveInitialScalarContract` and is stronger
    than the fixed-`E` uses need;
  - `1 ≤ r` is harmless (`C₁ log W ≥ 1` for large `W` once `C₁ > 0`); the length-`0` path has
    no physical block.
* **Norms.** `eLpNorm` at exponent `ENNReal.ofReal p`; the sum is taken in `ℝ≥0∞`.
* **Content.** The `δ₀` half is `PassiveInitialScalarContract.moment` (all `r ≥ 1`); the
  content is the `δ₁` half.

`PassiveJetExit` is the exit corollary used to pay jet exits; it follows from
`PassiveJetMoments` by Markov and a union bound (as `PathScalar.exit_of_moment`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathJet

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

/-- `δ_{1,r} = |∂_z(W⁻¹Tr R_r) - s|` along the unabsorbed near-end-grown path (far port held
fixed). -/
abbrev pathJet1 (b E : ℝ) (s : ℂ) (W r : ℕ) (ω : GrowthPath W) : ℝ :=
  jetDistance1 b E s (pathX b E W r ω)

/-- **The first-jet path moments**: `b, κ, p` first; then `C₁`; then `T`;
then `C, W₀`; for `W ≥ W₀`, `E ∈ bulkInterval κ`, every stationary jet `s` and every length
`1 ≤ r` with `C₁ log W ≤ r ≤ TW`, `‖δ_{0,r}‖_p + ‖δ_{1,r}‖_p ≤ C/W` under `growthPathLaw W b`. -/
def PassiveJetMoments : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ p : ℝ, 0 < κ → 1 ≤ p →
    ∃ C₁ : ℝ, ∀ T : ℝ, ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ s : ℂ, IsStationaryJet b E s → ∀ r : ℕ, 1 ≤ r → C₁ * Real.log W ≤ r →
        (r : ℝ) ≤ T * W →
          eLpNorm (fun ω => jetDistance0 b E (pathX b E W r ω)) (ENNReal.ofReal p)
              (growthPathLaw W b) +
            eLpNorm (fun ω => pathJet1 b E s W r ω) (ENNReal.ofReal p) (growthPathLaw W b) ≤
          ENNReal.ofReal (C / W)

/-- **Jet exit** (corollary of the moments, used to pay jet exits): for fixed
`d > 0` and every `D > 0`, `P(∃ r, 1 ≤ r, C₁ log W ≤ r ≤ TW, δ_{1,r} > d) ≤ W^{-D}`. -/
def PassiveJetExit : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ d D : ℝ, 0 < κ → 0 < d → 0 < D →
    ∃ C₁ : ℝ, ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ s : ℂ, IsStationaryJet b E s →
        growthPathLaw W b {ω | ∃ r : ℕ, 1 ≤ r ∧ C₁ * Real.log W ≤ r ∧ (r : ℝ) ≤ T * W ∧
          d < pathJet1 b E s W r ω} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D))

end BlockBand.Transmission.PathJet
