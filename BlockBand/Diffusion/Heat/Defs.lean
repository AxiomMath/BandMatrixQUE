module

public import BlockBand.Diffusion.Base.TransitionLawHolds

/-!
# The corner heat identity: statement and notation

`ChLbkCornerHeatIdentity D0`: for `w` in the strip, `w ≠ (0, 0)`, and `t > 0`,
`∫ p_t(w, w') H(w') dw' + (D₀/2) ∫₀ᵗ p_s(w, (0, 0)) ds = H(w)`, `H(w) = (w₁ + w₂)⁻¹` (`chHarm`).

**Notation for the proof** (not part of the statement): `chP D0 t F z = ∫ p_t(z,z') F(z') dz'`;
`chExp l z = e^{-l(x+y)}`; `chGen D0 l = 𝒟₀ chExp l`
`= (D₀/2)(1+x-y)(l²(x+y) - 2l)e^{-l(x+y)}`; `chHL L z = ∫_0^L e^{-l(x+y)} dl` (the `l`-cutoff
of `H = ∫_0^∞ e^{-l(x+y)} dl`); `chPhi L z = L²(1+x-y)e^{-L(x+y)}`, so that
`∫_0^L chGen D0 l dl = -(D₀/2) chPhi L` (an approximate corner delta times `-(D₀/2)`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

/-- The harmonic function `H(x, y) = (x + y)⁻¹` of the `H` transform. -/
def chHarm (w : ℝ × ℝ) : ℝ := (w.1 + w.2)⁻¹

/-- **The corner heat identity** for the explicit kernel `p = exKernel D₀`:
`∫ p_t(z,z') H(z') dz' + (D₀/2) ∫_{(0,t]} p_s(z,(0,0)) ds = H(z)` for `z ∈ exBaseStrip`,
`z ≠ (0,0)`, `t > 0` (a copy of `LbkCornerHeatIdentity`; proved as `chLbkCornerHeatIdentity`).
-/
def ChLbkCornerHeatIdentity (D0 : ℝ) : Prop :=
  ∀ w ∈ exBaseStrip, w ≠ (0, 0) → ∀ t : ℝ, 0 < t →
    (∫⁻ w', ENNReal.ofReal (exKernel D0 t w w') * ENNReal.ofReal (chHarm w')) +
        ENNReal.ofReal (D0 / 2) * ∫⁻ s in Ioc 0 t, ENNReal.ofReal (exKernel D0 s w (0, 0)) =
      ENNReal.ofReal (chHarm w)

/-!
### Notation for the proof
-/

/-- `P_t F(z) = ∫ p_t(z, z') F(z') dz'` (real Bochner integral). -/
def chP (D0 t : ℝ) (F : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ := ∫ z', exKernel D0 t z z' * F z'

/-- The exponential test function `e^{-l(x+y)}`. -/
def chExp (l : ℝ) (w : ℝ × ℝ) : ℝ := Real.exp (-(l * (w.1 + w.2)))

/-- Its generator `𝒟₀ e^{-l(x+y)} = (D₀/2)(1+x-y)(l²(x+y) - 2l)e^{-l(x+y)}`. -/
def chGen (D0 l : ℝ) (w : ℝ × ℝ) : ℝ :=
  D0 / 2 * ((1 + w.1 - w.2) * (l ^ 2 * (w.1 + w.2) - 2 * l) * Real.exp (-(l * (w.1 + w.2))))

/-- The cutoff harmonic function `H_L(z) = ∫_0^L e^{-l(x+y)} dl` (`↑ H` as `L → ∞`). -/
def chHL (L : ℝ) (w : ℝ × ℝ) : ℝ := ∫ l in (0 : ℝ)..L, chExp l w

/-- The approximate corner delta `L²(1+x-y)e^{-L(x+y)}`. -/
def chPhi (L : ℝ) (w : ℝ × ℝ) : ℝ := L ^ 2 * (1 + w.1 - w.2) * Real.exp (-(L * (w.1 + w.2)))

end BlockBand.Diffusion
