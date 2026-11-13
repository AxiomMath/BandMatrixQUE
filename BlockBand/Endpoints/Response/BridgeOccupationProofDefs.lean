module

public import BlockBand.Endpoints.Response.BridgeOccupationProofCounter

/-!
# Bridge occupation for measurable versions: statement and analytic inputs

This file states `BridgeOccupationMeasStatement` and the deterministic statements about the
explicit kernel from which it is derived. With `x₀ = (cosh r₀ - 1)/2` and the one-dimensional
factors `pX = lbkKernelX D₀`, `pY = lbkKernelY D₀`:
* `bopXMass D₀ x₀ T s = ∫ pX_s(x₀,x') pX_{T-s}(x',0) dx'` and
  `bopXMoment D₀ x₀ T s = ∫ x' pX_s(x₀,x') pX_{T-s}(x',0) dx'` (their ratio is the hyperbolic
  radial bridge mean `E^{br}X_s`).
* `LbkCornerChapmanKolmogorov D₀`: `∫ p_s(z,z') p_{T-s}(z',(0,0)) dz' = p_T(z,(0,0))` for the
  explicit product kernel, `z` in the strip, `0 < s < T` (the bridge one-time marginal has mass
  one; the semigroup property of the radial heat kernels of `H²` and `S²`, read at the corner).
* `LbkHypBridgeMeanLower`: `E^{br}X_s ≥ c (cosh((1-s/T)r₀) - 1)/2` (by Jensen under the planar
  Bessel bridge, then the lower bridge density bound), ratio multiplied out.
* `LbkHypBridgeMeanUpper`: `E^{br}X_s ≤ C e^{(1-s/T)r₀}`, ratio multiplied out.

The constants depend on `κ = D₀τ` only, and the bounds hold for `r₀ ≥ 0`, `T ∈ (0, τ]`,
`s ∈ (0, T)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set
open scoped ENNReal

/-- `BridgeOccupationStatement` with the version `p` in addition jointly measurable. -/
def BridgeOccupationMeasStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ r₁ : ℝ,
    ∀ D0 τ : ℝ, 0 < D0 → 0 < τ → D0 * τ = κ →
    ∀ p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ, IsBaseDensity D0 p →
      Measurable (fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => p w.1 w.2.1 w.2.2) → ∀ r₀ : ℝ, r₁ ≤ r₀ →
      ∀ T ∈ Ioc 0 τ,
        bridgeOccupation p (bridgeStart r₀) T 0 T ≠ ⊤ ∧
        ENNReal.ofReal (c * Real.exp r₀ * T / r₀) ≤ bridgeOccupation p (bridgeStart r₀) T 0 T ∧
        ∀ δ ∈ Ioo 0 τ, bridgeOccupation p (bridgeStart r₀) T δ T ≤
          ENNReal.ofReal (C * (Real.exp (-(δ * r₀ / τ)) + r₀ * Real.exp (-r₀))) *
            bridgeOccupation p (bridgeStart r₀) T 0 T

/-- The hyperbolic radial bridge mass `∫ pX_s(x,x') pX_{T-s}(x',0) dx'`. -/
def bopXMass (D0 x T s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x', ENNReal.ofReal (lbkKernelX D0 s x x') * ENNReal.ofReal (lbkKernelX D0 (T - s) x' 0)

/-- The hyperbolic radial bridge first moment `∫ x' pX_s(x,x') pX_{T-s}(x',0) dx'`. -/
def bopXMoment (D0 x T s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x', ENNReal.ofReal x' *
    (ENNReal.ofReal (lbkKernelX D0 s x x') * ENNReal.ofReal (lbkKernelX D0 (T - s) x' 0))

/-- The spherical radial bridge mass `∫ pY_s(y,y') pY_{T-s}(y',0) dy'`. -/
def bopYMass (D0 y T s : ℝ) : ℝ≥0∞ :=
  ∫⁻ y', ENNReal.ofReal (lbkKernelY D0 s y y') * ENNReal.ofReal (lbkKernelY D0 (T - s) y' 0)

/-- The spherical radial bridge first moment `∫ y' pY_s(y,y') pY_{T-s}(y',0) dy'`. -/
def bopYMoment (D0 y T s : ℝ) : ℝ≥0∞ :=
  ∫⁻ y', ENNReal.ofReal y' *
    (ENNReal.ofReal (lbkKernelY D0 s y y') * ENNReal.ofReal (lbkKernelY D0 (T - s) y' 0))

/-- Chapman–Kolmogorov at the corner for the explicit product kernel:
`∫ p_s(z,z') p_{T-s}(z',(0,0)) dz' = p_T(z,(0,0))`, `z` in the strip, `0 < s < T`. This is the
semigroup property of the heat kernels of `e^{TΔ}` on `H²` (McKean) and `S²` (Legendre series),
radialised, at the pole (by continuity of both sides in the end point). For the sphere factor it is
Legendre orthogonality `∫_0^1 P̃_n P̃_m = δ_{nm}/(2n+1)`. -/
def LbkCornerChapmanKolmogorov (D0 : ℝ) : Prop :=
  ∀ T s : ℝ, 0 < s → s < T → ∀ z ∈ baseStrip,
    ∫⁻ z', ENNReal.ofReal (lbkKernel D0 s z z') * ENNReal.ofReal (lbkKernel D0 (T - s) z' (0, 0)) =
      ENNReal.ofReal (lbkKernel D0 T z (0, 0))

/-- Lower bound for the hyperbolic radial bridge mean: `E^{br}X_s ≥ c (cosh((1-s/T)r₀) - 1)/2`,
with `c > 0` depending on `D₀τ` only, in multiplied-out form
`c (cosh((1-s/T)r₀)-1)/2 · bopXMass ≤ bopXMoment`. -/
def LbkHypBridgeMeanLower : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ c : ℝ, 0 < c ∧ ∀ D0 τ : ℝ, 0 < D0 → 0 < τ → D0 * τ = κ →
    ∀ r₀ : ℝ, 0 ≤ r₀ → ∀ T ∈ Ioc 0 τ, ∀ s ∈ Ioo 0 T,
      ENNReal.ofReal (c * ((Real.cosh ((1 - s / T) * r₀) - 1) / 2)) *
          bopXMass D0 ((Real.cosh r₀ - 1) / 2) T s ≤
        bopXMoment D0 ((Real.cosh r₀ - 1) / 2) T s

/-- `δ`-free upper bound for the hyperbolic radial bridge mean: `E^{br}X_s ≤ C e^{(1-s/T)r₀}`,
with `C` depending on `D₀τ` only, in multiplied-out form. -/
def LbkHypBridgeMeanUpper : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ C : ℝ, 0 ≤ C ∧ ∀ D0 τ : ℝ, 0 < D0 → 0 < τ → D0 * τ = κ →
    ∀ r₀ : ℝ, 0 ≤ r₀ → ∀ T ∈ Ioc 0 τ, ∀ s ∈ Ioo 0 T,
      bopXMoment D0 ((Real.cosh r₀ - 1) / 2) T s ≤
        ENNReal.ofReal (C * Real.exp ((1 - s / T) * r₀)) * bopXMass D0 ((Real.cosh r₀ - 1) / 2) T s

end BlockBand.Endpoints
