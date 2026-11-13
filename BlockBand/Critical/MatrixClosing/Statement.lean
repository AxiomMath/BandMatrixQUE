module

public import BlockBand.Critical.Herglotz.Canonical

/-!
# The matrix closing theorem: statement

This file defines the closing matrices of the collar and states the matrix closing theorem as the
proposition `MatrixClosingStatement`; it contains no proofs.

* `microShift W e x = x/(Wρ(e))`, `ρ = Parameters.semicircleDensity`: the microscopic scale of a
  shift in the fresh middle diagonal only.
* `closingMatrix b e s X J ω = -iJ*{2(I - U𝔯)⁻¹ - I}J`, `U = middleScattering b e s ω`, for an old
  orthonormal frame `J : ℂ^r → ℂ^{2W}` (`Jᴴ J = I_r`): the matrix closing law at `s = 0` and its
  middle-shifted versions.
* `shiftedClosing b e x X J ω = (closingMatrix b e (x_a/(Wρ(e))) X J ω)_{a < k}`: a finite family
  of middle microscopic shifts `x_a`, all built from the same collar sample.
* `MatrixClosingStatement`: uniformly over widths `W ≥ W₀`, bulk energies, Hermitian old data `X`
  with `matchedDistance b e X ≤ δ` and orthonormal frames `J`, the law of `shiftedClosing` under
  `collarLaw W b` is `ε`-close, tested against a bounded continuous `Φ`, to the law of
  `(C(x_a))_a` for a canonical Cauchy matrix field `C`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Critical.Herglotz

variable {W : ℕ}

/-- The middle microscopic shift `s = x/(Wρ(e))`, `ρ = Parameters.semicircleDensity`. -/
def microShift (W : ℕ) (e x : ℝ) : ℝ :=
  x / ((W : ℝ) * Parameters.semicircleDensity e)

/-- The collar reaction with only the middle diagonal shifted:
`K_c = A - e - ξ - B(G - (e+s))⁻¹B*`, `ξ = Re z_b`; only the fresh middle block `G` is
shifted. -/
def middleReaction (b e s : ℝ) (ω : CollarSample W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  blockDiag ω.1.1 - ((e : ℂ) + ((boundaryZ b e).re : ℂ)) • 1 -
    bondMatrix .common ω.1.2 * (ω.2 - ((e + s : ℝ) : ℂ) • 1)⁻¹ * (bondMatrix .common ω.1.2)ᴴ

/-- The middle-shifted collar scattering `U = I - 2iη(K_c + iη)⁻¹`, `η = Im z_b`. -/
def middleScattering (b e s : ℝ) (ω : CollarSample W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  1 - (2 * ((boundaryZ b e).im : ℂ) * Complex.I) •
    (middleReaction b e s ω + (((boundaryZ b e).im : ℂ) * Complex.I) • 1)⁻¹

/-- The closing matrix `-iJ*{2(I - U𝔯)⁻¹ - I}J` with the middle diagonal shifted by `s`;
`𝔯 = oldScattering b e X`. -/
def closingMatrix {r : ℕ} (b e s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (ω : CollarSample W) : Matrix (Fin r) (Fin r) ℂ :=
  (-Complex.I) • (Jᴴ * ((2 : ℂ) • (1 - middleScattering b e s ω * oldScattering b e X)⁻¹ - 1) * J)

/-- The closing matrices at the middle microscopic shifts `x_a/(Wρ(e))`, `a < k`, jointly. -/
def shiftedClosing {r k : ℕ} (b e : ℝ) (x : Fin k → ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ)
    (ω : CollarSample W) : Fin k → Matrix (Fin r) (Fin r) ℂ :=
  fun a => closingMatrix b e (microShift W e (x a)) X J ω

/-- **The matrix closing theorem.** For `0 < b < 1/2`, `κ > 0`, a canonical Cauchy field `C` and a
bounded continuous test `Φ`, for every `ε > 0` there are `δ > 0` and `W₀` such that for all
`W ≥ W₀`, `e` in the bulk, Hermitian `X` with `matchedDistance b e X ≤ δ` and orthonormal frames
`J`, the shifted closing family is almost everywhere measurable and its `Φ`-expectation under
`collarLaw W b` is within `ε` of that of `(C(x_a))_a`. -/
def MatrixClosingStatement : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ (r k : ℕ) (x : Fin k → ℝ)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω')
    (Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))) (C : Ω' → ℂ → Matrix (Fin r) (Fin r) ℂ),
    IsCanonicalCauchy r P' Ξ C →
    ∀ Φ : BoundedContinuousFunction (Fin k → Matrix (Fin r) (Fin r) ℂ) ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ (δ : ℝ) (W₀ : ℕ), 0 < δ ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ e ∈ bulkInterval κ,
        ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
          matchedDistance b e X ≤ δ →
        ∀ J : Matrix (Fin 2 × Fin W) (Fin r) ℂ, Jᴴ * J = 1 →
          AEMeasurable (shiftedClosing b e x X J) (collarLaw W b) ∧
          |∫ ω, Φ (shiftedClosing b e x X J ω) ∂collarLaw W b -
              ∫ ω, Φ (fun a => C ω (x a)) ∂P'| ≤ ε

end BlockBand.Critical.MatrixClosing
