module

public import BlockBand.Critical.Collar.Kernel

/-!
# Exact boundary mean: intermediate statements

* `StrictBoundaryMeanClause`: the strict (`Y ≻ 0`) clause of `ExactBoundaryMeanContract` with explicit constants
  and scalar regime `d(X) ≤ d₂`. `exactBoundaryMean_of_strict` proves that this clause
  implies the full statement (the radial regulator is removed at fixed `W`).
* `HermitianCollarMeanStatement`: the sharp collar density estimate, for a **Hermitian**
  old response, in the Poisson-regularized resolvent form used by the dilation argument:
  for `W ≥ W₀`, `e ∈ bulkInterval κ` and every `δ > 0` there is `ν₀ > 0` such that for `0 < ν < ν₀`,
  every Hermitian `X` with `d(X) ≤ d₂` and every `q`,
  `|E_collar Im⟨ρ*q, (ℋ_X - iν)⁻¹ ρ*q⟩ - η‖q‖²| ≤ (C(d(X) + ε_W) + δ)‖q‖²`,
  `ρ*q = ((conj(z_b + e) - A)q, -B*q)` (`Density.collarRowVec (Kernel.rowCoeff b e 0) q`).
  By the spectral theorem the left side is `π∫P_ν(x) q*(K_X - x)Ψ_X(x)(K_X - x)*q dx` (`P_ν` the
  Cauchy kernel, `Ψ_X` the expected top-top collar density, `K_X = z_b - X`). The sharp collar
  density estimate gives,
  uniformly in Hermitian `X` with `d(X)` small and in small real shifts `s` of the middle spectrum,
  `E_{A,B}[K_XTΣ_F(s)T*K_X*] = (η/π)I + O_op(d(X) + ε_W + W⁻¹ + |s|)` (`cγ = 1 - b`,
  `η = (1 - b)πρ(E)`; at `s = 0` the left side is `K_XΨ_X(0)K_X*`). The density of `ℋ_X` at `x`
  is the density at `0` of the collar with top response `X + x` (`K_X - x = K_{X+x}`,
  `d(X + x) ≤ d(X) + |x|/η²`) and middle shift `s = x`. With the total mass
  `∫ q*(K_X - x)Ψ_X(x)(K_X - x)*q dx = E‖ρ*q‖² ≤ C‖q‖²` for the Cauchy tail, this gives the
  displayed bound with `ν₀` independent of `X` and `q`.

`Reduction.exactBoundaryMean_of_hermitian : HermitianCollarMeanStatement → ExactBoundaryMeanContract`.

Law: `collarLaw W b` (the finite Gaussian collar), deterministic old response `X`.
Norms: `‖q‖² = ∑ₓ ‖q x‖²`; matrix norms are the Euclidean operator norm.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.BoundaryMean

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Critical.Collar.Density (collarMatrix collarRowVec)
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- The error term of the collar mean estimate: `C{d(X) + ε_W + W^{-1/8} + g W^{-1/4}}`. -/
def meanError (b e : ℝ) (ε : ℕ → ℝ) (C : ℝ) {W : ℕ}
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : ℝ :=
  C * (matchedDistance b e X + ε W + (W : ℝ) ^ (-(1 : ℝ) / 8) +
    conductance (oldScattering b e X) * (W : ℝ) ^ (-(1 : ℝ) / 4))

/-- The strict (`Y = -Im X ≻ 0`) clause of `ExactBoundaryMeanContract` with explicit constants and
scalar regime `d(X) ≤ d₂`: the collar kernel entries are integrable and
`‖E_collar 𝒫(Ur) - I‖ ≤ C{d(X) + ε_W + W^{-1/8} + g W^{-1/4}}`. -/
def StrictBoundaryMeanClause (b κ : ℝ) (ε : ℕ → ℝ) (C d₂ : ℝ) (W₀ : ℕ) : Prop :=
  ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ e ∈ bulkInterval κ,
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, (-imPart X).PosDef →
      matchedDistance b e X ≤ d₂ →
        CollarKernelIntegrable b e 0 0 1 X ∧
          ‖expectedCollarKernel b e 0 0 1 X - 1‖ ≤ meanError b e ε C X

/-- The Poisson-regularized Hermitian collar form
`h_ν(X, q) = E_collar Im⟨ρ*q, (ℋ_X - iν)⁻¹ ρ*q⟩`, `ρ*q = ((conj(z_b + e) - A)q, -B*q)`. -/
def hermitianCollarForm (W : ℕ) (b e ν : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (q : Fin 2 × Fin W → ℂ) : ℝ :=
  ∫ ω, (star (collarRowVec (Collar.Kernel.rowCoeff b e 0) q ω) ⬝ᵥ
    ((collarMatrix e X ω - ((ν : ℂ) * Complex.I) • 1)⁻¹ *ᵥ
      collarRowVec (Collar.Kernel.rowCoeff b e 0) q ω)).im ∂collarLaw W b

/-- **The sharp collar density estimate for Hermitian old responses, resolvent form.**
`b ∈ (0,1/2)` and `bulkInterval κ` first; then a sequence `ε_W → 0`, constants `C`, `d₂ > 0`, `W₀`;
for `W ≥ W₀`, `e ∈ bulkInterval κ` and `δ > 0` there is `ν₀ > 0` (independent of `X`, `q`) such that
for `0 < ν < ν₀`, every Hermitian `X` with `d(X) ≤ d₂` and every `q`:
`|h_ν(X, q) - η‖q‖²| ≤ (C(d(X) + ε_W) + δ)‖q‖²`, `η = Im z_b`. -/
def HermitianCollarMeanStatement : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (ε : ℕ → ℝ) (C d₂ : ℝ) (W₀ : ℕ), Tendsto ε atTop (𝓝 0) ∧ 0 < d₂ ∧
      ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ e ∈ bulkInterval κ, ∀ δ : ℝ, 0 < δ →
        ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Set.Ioo 0 ν₀,
          ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
            matchedDistance b e X ≤ d₂ → ∀ q : Fin 2 × Fin W → ℂ,
              |hermitianCollarForm W b e ν X q - (boundaryZ b e).im * ∑ x, ‖q x‖ ^ 2| ≤
                (C * (matchedDistance b e X + ε W) + δ) * ∑ x, ‖q x‖ ^ 2

end BlockBand.Critical.BoundaryMean
