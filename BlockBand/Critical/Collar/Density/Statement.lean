module

public import BlockBand.Internal.Contracts.Critical
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# The collar density bound: statement

*Law.* The finite Gaussian collar `collarLaw W b`: `ω = ((A, B), G)`, end diagonals
`A_j ~ GUE_W(c/W)`, `c = 1 - 2b`, bonds `B_j ~ Gin(b/W)`, middle diagonal `G ~ GUE_W(c/W)` (on the
port index `Fin 1 × Fin W`), all independent. `X` is a deterministic Hermitian `2W × 2W` matrix (an
independent `X` by Fubini). `K_X = z_b - X` is `matchedLeadK b e X`, and `d(X)` is
`matchedDistance b e X`. Loewner order: `M ⪯ cI ⇔ (c I - M).PosSemidef`.

* `collarMatrix e X ω = ℋ_X = [[A - e - X, B], [B*, G - e]]` on `LayerSite W .common`
  (physical sites `Fin 2 × Fin W` first, then the middle block).
* `collarTopProjector W b e X I = E_collar[1_I(ℋ_X)]₁₁`: the entrywise expectation of the top-top
  block of the spectral projector `1_I(ℋ_X) = cfc (I.indicator 1) ℋ_X` (Mathlib Hermitian
  functional calculus; `ℋ_X` is Hermitian almost surely), as in
  `WeightedDensity.expectedSpectralProjector`.
* `IsCollarTopDensity W b e X S`: `∫_{[a₁,a₂]} S = collarTopProjector (Icc a₁ a₂)` entrywise for all
  `a₁ ≤ a₂` (pattern of `WeightedDensity.IsMatrixSpectralDensity`). The expected top-top
  matrix spectral density at zero is `S 0` for a **continuous** such `S`.
* `CollarDensityStatement`: the collar density bound, stated as a `Prop`. It is proved from
  `FreshPalmContract`, `PointDensityContract`, `CommonPortMeanContract`, `TraceMatrixContract` and
  `PSSS.SourceContract` as `collarDensityStatement_of_inputs`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ComplexOrder

/-- The three-block collar matrix `ℋ_X = [[A - e - X, B], [B*, G - e]]` on
`LayerSite W.common = (Fin 2 × Fin W) ⊕ (Fin 1 × Fin W)`;
`A = diag(A₁, A₂)`,
`B = (B₁ᵀ, B₂ᵀ)ᵀ` are the `blockDiag`, `bondMatrix.common` of the common-port layer.
-/
def collarMatrix (e : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : CollarSample W) : Matrix (LayerSite W .common) (LayerSite W .common) ℂ :=
  Matrix.fromBlocks (blockDiag ω.1.1 - (e : ℂ) • 1 - X) (bondMatrix .common ω.1.2)
    (bondMatrix .common ω.1.2)ᴴ (ω.2 - (e : ℂ) • 1)

/-- `E_collar[1_I(ℋ_X)]₁₁`: expected top-top block of the spectral projector of `ℋ_X` on a
Borel set `I` (Mathlib functional calculus `cfc (I.indicator 1)`), entrywise expectation over
`collarLaw W b`. -/
def collarTopProjector (W : ℕ) (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (I : Set ℝ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  matrixExpect (collarLaw W b)
    (fun ω => (cfc (I.indicator (1 : ℝ → ℝ)) (collarMatrix e X ω)).toBlocks₁₁)

/-- `S` is an expected top-top matrix spectral density of `ℋ_X`:
`∫_{[a₁,a₂]} S(x) dx = E_collar[1_{[a₁,a₂]}(ℋ_X)]₁₁` entrywise, for all `a₁ ≤ a₂`. -/
def IsCollarTopDensity (W : ℕ) (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (S : ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : Prop :=
  ∀ a₁ a₂ : ℝ, a₁ ≤ a₂ → ∀ i j : Fin 2 × Fin W,
    ∫ x in Set.Icc a₁ a₂, S x i j = collarTopProjector W b e X (Set.Icc a₁ a₂) i j

/-- **The collar density bound.** Law `collarLaw W b` (the finite Gaussian collar, conditional
on a deterministic Hermitian `X`). For every `b ∈ (0, 1/2)` and `κ > 0` there are `d_* > 0`, `C` and
`W₀` such that, for every `W ≥ 1`, `e ∈ bulkInterval κ` and **every** Hermitian `X` (no norm
bound):
* the expected top-top matrix spectral density of `ℋ_X` has a continuous version;
* every continuous version `S` satisfies `K_X S(0) K_X* ⪯ C √W I`, `K_X = matchedLeadK b e X`
  (every `W ≥ 1`), and `K_X S(0) K_X* ⪯ C I` when moreover `W ≥ W₀` and
  `matchedDistance b e X ≤ d_*`.
Norms: Loewner order of complex matrices. -/
def CollarDensityStatement : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧
      ∀ (W : ℕ), 0 < W → ∀ e ∈ bulkInterval κ,
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
        (∃ S : ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
          Continuous S ∧ IsCollarTopDensity W b e X S) ∧
        ∀ S : ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, Continuous S →
          IsCollarTopDensity W b e X S →
          (((C * Real.sqrt W : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
              matchedLeadK b e X * S 0 * (matchedLeadK b e X)ᴴ).PosSemidef ∧
          (W₀ ≤ W → matchedDistance b e X ≤ dstar →
            (((C : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
              matchedLeadK b e X * S 0 * (matchedLeadK b e X)ᴴ).PosSemidef)

end BlockBand.Critical.Collar.Density
