module

public import BlockBand.Critical.MatrixClosing.Statement

/-!
# The middle-only shifted collar mean: statement

* `middleKernel b e s t X ω = 𝒫(t U_s 𝔯)`, `MiddleKernelIntegrable`, `expectedMiddleKernel`,
  `middleMeanError`.
* `MiddleShiftBoundaryMeanStatement`: the collar mean error bound for the middle-only shifted
  collar, with the extra error `C|s|`. It follows from `ExactBoundaryMeanContract`
  (`middleShiftBoundaryMean_of_exactBoundaryMean`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-!
## The middle-shifted kernel and the statement
-/

/-- `𝒫(t U_s 𝔯)` with the middle-only shifted collar scattering `U_s` (`t`: radial regulator). -/
def middleKernel (b e s t : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : CollarSample W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  BlockBand.Internal.Contracts.Critical.poissonKernel ((t : ℂ) • (middleScattering b e s ω * oldScattering b e X))

/-- The entries of `𝒫(tU_s𝔯)` are integrable over the collar. -/
def MiddleKernelIntegrable (b e s t : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : Prop :=
  ∀ x y, Integrable (fun ω => middleKernel b e s t X ω x y) (collarLaw W b)

/-- `E_collar 𝒫(tU_s𝔯)`. -/
def expectedMiddleKernel (b e s t : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  matrixExpect (collarLaw W b) (middleKernel b e s t X)

/-- The error `C{d(X) + ε_W + W^{-1/8} + gW^{-1/4} + |s|}`. -/
def middleMeanError (b e s : ℝ) (ε : ℕ → ℝ) (C : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : ℝ :=
  C * (matchedDistance b e X + ε W + (W : ℝ) ^ (-(1 : ℝ) / 8) +
    conductance (oldScattering b e X) * (W : ℝ) ^ (-(1 : ℝ) / 4) + |s|)

/-- **The middle-only shifted collar mean.** For `0 < b < 1/2` and `κ > 0` there are `ε_W → 0`,
`C`, `d₁ > 0`, `s₀ > 0` and `W₀` such that for `W ≥ W₀`, `e ∈ bulkInterval κ`, `|s| ≤ s₀` and `X`
with `d(X) ≤ d₁`: if `-Im X ≻ 0`, the entries of `𝒫(U_s𝔯)` are integrable and
`‖E𝒫(U_s𝔯) - I‖ ≤ middleMeanError`; if `-Im X ⪰ 0`, the same holds for `𝒫(tU_s𝔯)` up to `δ`
for all `t < 1` close to one.

Law `collarLaw W b`. Only the middle diagonal is shifted, `G - e ↦ G - (e+s)`
(`middleScattering b e s`); the end diagonals `A_j - e` and `z_b(e)` are unchanged, unlike
`collarShift`. With `s = x/(Wρ(e))` the extra term is `C|x|/(Wρ(e))`; at `s = 0` this is the bound
of `ExactBoundaryMeanContract`. -/
def MiddleShiftBoundaryMeanStatement : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (ε : ℕ → ℝ) (C d₁ s₀ : ℝ) (W₀ : ℕ), Tendsto ε atTop (𝓝 0) ∧ 0 < d₁ ∧ 0 < s₀ ∧
      ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ e ∈ bulkInterval κ, ∀ s ∈ Set.Icc (-s₀) s₀,
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, matchedDistance b e X ≤ d₁ →
        ((-imPart X).PosDef →
          MiddleKernelIntegrable b e s 1 X ∧
            ‖expectedMiddleKernel b e s 1 X - 1‖ ≤ middleMeanError b e s ε C X) ∧
        ((-imPart X).PosSemidef → ∀ δ : ℝ, 0 < δ → ∃ t₀ : ℝ, t₀ < 1 ∧ ∀ t ∈ Set.Ioo t₀ 1,
          MiddleKernelIntegrable b e s t X ∧
            ‖expectedMiddleKernel b e s t X - 1‖ ≤ middleMeanError b e s ε C X + δ)

end BlockBand.Critical.MatrixClosing
