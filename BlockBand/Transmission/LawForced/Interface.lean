module

public import BlockBand.Transmission.LawDuality.Interface

/-!
# The forced finite-`W` ratio expansion: vocabulary and statement

The finite-`W` state at length `r` is `μ^r = traceMeasure T^κ_r` (so `μ_W(t) = μ^{⌊Wt⌋}`).
For a dual point `z = (x, y)` of the chamber:
* `ratioAt b E κ W r z = F_z(μ^r)`;
* `ratioDriftAt b E κ W r z = (𝒟_pF_·(μ^r))(z) − h(r/W) R(z) F_z(μ^r)` (`ratioDrift` at
  `D₀ = transportD0 b E`, time `r/W`);
* `ratioDriftError b E κ W z r = E[F_z(μ^{r+1}) − F_z(μ^r) ∣ 𝓕_r] − ratioDriftAt/W`.

**`RatioDriftSummable`** (the analogue of `PowerDriftSummable` for the determinant ratios,
with the forcing): for `0 < b < 1/2`, bulk
`E`, every admissible profile `κ`, every chamber point `z` and `0 < ε ≤ T`,
`Σ_{⌊εW⌋ ≤ r < ⌊TW⌋} E|ratioDriftError_r| → 0`.

It is stated at a fixed energy (the sub-limits of `SubLimitRatioMartingale` are at fixed `E`),
in `L¹` (the limit tests are bounded), and with the time argument `r/W` of `h` (the block added
at step `r + 1` carries `κ((r+1)/W)/W²`; the difference is `o(1)` after summation since `κ` is
uniformly continuous on compacts). `subLimitRatioMartingale_of` proves
`SubLimitRatioMartingale` from it, with no other input.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.LawDuality
open scoped NNReal ENNReal

variable {W : ℕ}

/-- `F_z(μ^r)`, `μ^r = traceMeasure T^κ_r`. -/
def ratioAt (b E : ℝ) (κ : ℝ → ℝ) (W r : ℕ) {p : ℕ} (z : DualCoord p) (ω : GrowthPath W) : ℝ :=
  transmissionRatio z.1 z.2 (traceMeasure (pathTransmission b E κ W r ω))

/-- `(𝒟_pF_·(μ^r))(z) − h(r/W)R(z)F_z(μ^r)`, `D₀ = transportD0 b E`. -/
def ratioDriftAt (b E : ℝ) (κ : ℝ → ℝ) (W r : ℕ) {p : ℕ} (z : DualCoord p)
    (ω : GrowthPath W) : ℝ :=
  ratioDrift (transportD0 b E) E κ ((r : ℝ) / W) z (traceMeasure (pathTransmission b E κ W r ω))

/-- The one-step drift error `E[F_z(μ^{r+1}) − F_z(μ^r) ∣ 𝓕_r] − ratioDriftAt/W`. -/
def ratioDriftError (b E : ℝ) (κ : ℝ → ℝ) (W : ℕ) {p : ℕ} (z : DualCoord p) (r : ℕ) :
    GrowthPath W → ℝ :=
  (growthPathLaw W b)[fun ω => ratioAt b E κ W (r + 1) z ω - ratioAt b E κ W r z ω |
      growthSigma W r] - fun ω => ratioDriftAt b E κ W r z ω / W

/-- **Summable forced ratio drift errors** (with the forcing). -/
def RatioDriftSummable : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    ∀ (p : ℕ) (z : DualCoord p), z ∈ dualChamber p → ∀ ε T : ℝ, 0 < ε → ε ≤ T →
      Tendsto (fun W : ℕ => ∑ r ∈ Finset.Ico ⌊(W : ℝ) * ε⌋₊ ⌊(W : ℝ) * T⌋₊,
        ∫ ω, |ratioDriftError b E κ W z r ω| ∂growthPathLaw W b) atTop (𝓝 0)

end BlockBand.Transmission.LawForced
