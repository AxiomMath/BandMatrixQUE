module

public import BlockBand.Endpoints.Response.LifetimeBridgeDefs

/-!
# Bridge occupation: the statement

This file defines the mean occupation of the base bridge and states the bridge-occupation lemma.

Fix `τ > 0`. Start the base bridge at `x = (cosh r₀ - 1)/2`, `y = 0`, end it at `(0,0)`, with
duration `0 < T ≤ τ`. For all sufficiently large `r₀`, uniformly in `T`,
`E^{br}_{r₀,T} ∫_0^T (X_s + Y_s) ds ≥ c_τ e^{r₀} T / r₀`. For every fixed `0 < δ < τ`, with the
late integral set to zero when `T < δ`,
`E^{br}∫_δ^T(X+Y) / E^{br}∫_0^T(X+Y) ≤ C_τ{e^{-δr₀/τ} + r₀e^{-r₀}}`. Constants may depend on `D₀τ`
and are independent of `T, r₀` in this range.

## Lean form (`BridgeOccupationStatement`)

* `bridgeMeanTotal p z T s = E^{br}_{z,T}[X_s + Y_s]`, the one-time marginal of the base bridge
  (`bridgeFddDensity` at `k = 1`; the law of `Z_s` under every `IsBaseBridge` realization).
* `bridgeOccupation p z T a b = ∫_{(a,b)} E^{br}_{z,T}[X_s + Y_s] ds`. By Tonelli this is
  `E^{br}_{z,T} ∫_a^b (X_s + Y_s) ds` for every realization with jointly measurable paths, and it
  is `0` when `b ≤ a` (the convention for `T < δ`).
* For every value `κ > 0` of `D₀τ` there are `c > 0`, `C ≥ 0`, `r₁`, depending on `D₀` and `τ`
  only through the product `D₀τ` (this holds by Brownian time scaling `s ↦ D₀s`), such that for all
  `D₀, τ > 0` with `D₀τ = κ`, every version `p` of the base density (`IsBaseDensity`), every
  `r₀ ≥ r₁` and `T ∈ (0, τ]`, with `z = ((cosh r₀ - 1)/2, 0)`: the full occupation is finite, at
  least `c e^{r₀} T / r₀`, and for every `δ ∈ (0, τ)` the late occupation is at most
  `C (e^{-δr₀/τ} + r₀e^{-r₀})` times the full one (the ratio form, multiplied out; the full
  occupation is positive).
* The constant `C` and the threshold for `r₀` are independent of `δ`: both come from the lower
  bound and the `δ`-free upper bound `E^{br}X_s ≤ C_τ e^{(1-s/T)r₀}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set
open scoped ENNReal NNReal

/-- `E^{br}_{z,T}[X_s + Y_s]`: the mean of the total coordinate at time `s` under the base bridge
from `z` to `(0,0)` of length `T` (its one-time marginal density). -/
def bridgeMeanTotal (p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ) (z : ℝ × ℝ) (T s : ℝ) : ℝ≥0∞ :=
  ∫⁻ zs : Fin 1 → ℝ × ℝ, ENNReal.ofReal ((zs 0).1 + (zs 0).2) *
    bridgeFddDensity p z (0, 0) T ![s] zs

/-- `E^{br}_{z,T} ∫_a^b (X_s + Y_s) ds` (Tonelli form; `0` if `b ≤ a`). -/
def bridgeOccupation (p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ) (z : ℝ × ℝ) (T a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioo a b, bridgeMeanTotal p z T s

/-- The bridge start `((cosh r₀ - 1)/2, 0)` (hyperbolic radius `r₀`, spherical radius `0`). -/
def bridgeStart (r₀ : ℝ) : ℝ × ℝ := ((Real.cosh r₀ - 1) / 2, 0)

/-- The bridge-occupation lemma; see the module docstring. -/
def BridgeOccupationStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ r₁ : ℝ,
    ∀ D0 τ : ℝ, 0 < D0 → 0 < τ → D0 * τ = κ →
    ∀ p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ, IsBaseDensity D0 p → ∀ r₀ : ℝ, r₁ ≤ r₀ →
      ∀ T ∈ Ioc 0 τ,
        bridgeOccupation p (bridgeStart r₀) T 0 T ≠ ⊤ ∧
        ENNReal.ofReal (c * Real.exp r₀ * T / r₀) ≤ bridgeOccupation p (bridgeStart r₀) T 0 T ∧
        ∀ δ ∈ Ioo 0 τ, bridgeOccupation p (bridgeStart r₀) T δ T ≤
          ENNReal.ofReal (C * (Real.exp (-(δ * r₀ / τ)) + r₀ * Real.exp (-r₀))) *
            bridgeOccupation p (bridgeStart r₀) T 0 T

end BlockBand.Endpoints
