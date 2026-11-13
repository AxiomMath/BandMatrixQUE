module

public import BlockBand.Native.CEH.BlockBand.Published.LocalETHInput

/-!
# Published CEH single-resolvent contract

This module records the source-shaped conclusion of Cipolloni–Erdős–Henheik Theorem 2.3,
equations (2.8)--(2.9), for the normalized GUE specialization used by the block-band paper (the
external local law theorem).

The order of quantifiers is the stochastic-domination order from the source: the fixed
deformation and domain exponents precede the arbitrary loss and tail exponents, one
cutoff is then chosen, and that cutoff is uniform in the dimension-dependent variance,
Hermitian deformation, spectral parameter, MDE solution, and deterministic vectors or
observable.  The GUE normalization is `GUE_N(s/N)`, the trace is normalized, and both
half-planes are included.

These definitions are contracts, not assumptions or certificates.  In particular this
module does not postulate a value of `CEHLocalInput`; the external CEH development must
construct one.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open MeasureTheory
open scoped ComplexOrder Matrix ENNReal Matrix.Norms.L2Operator

/-- Complex matrices in the published CEH local-law contract. -/
abbrev CEHMatrix (N : ℕ) := Matrix (Fin N) (Fin N) ℂ

/-- A dimension- and variance-indexed family of Hermitian probability laws.
The intended value at `(N,t)` is `GUE_N(t)`. -/
abbrev CEHGUEFamily :=
  (N : ℕ) → ℝ → ProbabilityMeasure (HermitianMatrix (Fin N))

/-- Matrix imaginary part `(A-Aᴴ)/(2i)`. -/
noncomputable def cehImPart {N : ℕ} (A : CEHMatrix N) : CEHMatrix N :=
  (2 * Complex.I)⁻¹ • (A - Aᴴ)

/-- Resolvent convention used in the paper: `(A-z)⁻¹`. -/
noncomputable def cehResolvent {N : ℕ} (A : CEHMatrix N) (z : ℂ) : CEHMatrix N :=
  (A - z • (1 : CEHMatrix N))⁻¹

/-- The matrix Dyson equation
`M = (F-z-s⟨M⟩)⁻¹`, in one-sided inverse form, with its half-plane sign condition. -/
structure IsCEHMDESolution {N : ℕ} (s : ℝ) (F : CEHMatrix N)
    (z : ℂ) (M : CEHMatrix N) : Prop where
  inv :
    (F - (z + (s : ℂ) * Conventions.normalizedTrace M) •
      (1 : CEHMatrix N)) * M = 1
  pos : (((z.im : ℝ) : ℂ) • cehImPart M).PosDef

/-- The self-consistent density `ρ_s(z)=π⁻¹|Im ⟨M(z)⟩|`. -/
noncomputable def cehMDEDensity {N : ℕ} (M : CEHMatrix N) : ℝ :=
  |(Conventions.normalizedTrace M).im| / Real.pi

/-- The CEH relative matrix `Γ=Im M / Im ⟨M⟩`. -/
noncomputable def cehRelGamma {N : ℕ} (M : CEHMatrix N) : CEHMatrix N :=
  (((Conventions.normalizedTrace M).im : ℂ))⁻¹ • cehImPart M

/-- The large-deformation hypothesis `‖F‖ ≤ C N^κ √s`. -/
def CEHDeformationBound {N : ℕ} (κ C s : ℝ) (F : CEHMatrix N) : Prop :=
  ‖F‖ ≤ C * (N : ℝ) ^ κ * Real.sqrt s

/-- The exact CEH spectral domain
`N |Im z| ρ_s(z) ≥ N^ε`, `|z| ≤ √s N^(κ+1/ε)`. -/
def InCEHDomain {N : ℕ} (ε κ s : ℝ) (z : ℂ) (M : CEHMatrix N) : Prop :=
  z.im ≠ 0 ∧
    (N : ℝ) ^ ε ≤ N * |z.im| * cehMDEDensity M ∧
    ‖z‖ ≤ Real.sqrt s * (N : ℝ) ^ (κ + 1 / ε)

/-- Antilinear-first matrix quadratic form `x* A y`. -/
def cehQuadForm {N : ℕ} (A : CEHMatrix N) (x y : Fin N → ℂ) : ℂ :=
  star x ⬝ᵥ (A *ᵥ y)

/-- Isotropic error in CEH equation (2.9). -/
noncomputable def cehIsoError {N : ℕ} (F G M : CEHMatrix N)
    (z : ℂ) (x y : Fin N → ℂ) : ℝ :=
  ‖cehQuadForm (cehResolvent (F + G) z - M) x y‖

/-- Isotropic comparison scale in CEH equation (2.9), with no division by
the norms of `x,y`, so the formula also covers zero vectors. -/
noncomputable def cehIsoControl {N : ℕ} (M : CEHMatrix N)
    (z : ℂ) (x y : Fin N → ℂ) : ℝ :=
  Real.sqrt (cehMDEDensity M / (N * |z.im|)) *
    Real.sqrt
      ((cehQuadForm (cehRelGamma M) x x).re *
        (cehQuadForm (cehRelGamma M) y y).re)

/-- Averaged error in CEH equation (2.8), with normalized trace. -/
noncomputable def cehAvgError {N : ℕ} (F G M : CEHMatrix N)
    (z : ℂ) (B : CEHMatrix N) : ℝ :=
  ‖Conventions.normalizedTrace ((cehResolvent (F + G) z - M) * B)‖

/-- Averaged comparison scale in CEH equation (2.8), using the source's
normalized Hilbert–Schmidt convention. -/
noncomputable def cehAvgControl {N : ℕ} (M : CEHMatrix N)
    (z : ℂ) (B : CEHMatrix N) : ℝ :=
  Real.sqrt (Conventions.normalizedTrace (cehRelGamma M * B * Bᴴ)).re /
    (N * |z.im|)

/-- Pointwise averaged and isotropic CEH local law at fixed parameters.
The deterministic vectors and observable are fixed before probability. -/
def CEHLocalLawAt {N : ℕ} (gue : CEHGUEFamily) (δ D s : ℝ)
    (F : CEHMatrix N) (z : ℂ) (M : CEHMatrix N) : Prop :=
  (∀ x y : Fin N → ℂ,
    (gue N (s / N) : Measure (HermitianMatrix (Fin N)))
        {G | (N : ℝ) ^ δ * cehIsoControl M z x y <
          cehIsoError F G.1 M z x y} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
  ∀ B : CEHMatrix N,
    (gue N (s / N) : Measure (HermitianMatrix (Fin N)))
        {G | (N : ℝ) ^ δ * cehAvgControl M z B <
          cehAvgError F G.1 M z B} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D))

/-- The uniform form of CEH Theorem 2.3, equations (2.8)--(2.9).
The cutoff depends only on `(κ,C,ε,δ,D)` and is uniform in all data quantified
after it. -/
def CEHLocalLawBound (gue : CEHGUEFamily) : Prop :=
  ∀ κ C ε : ℝ, 0 ≤ κ → 0 < C → 0 < ε →
  ∀ δ D : ℝ, 0 < δ → 0 < D →
  ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ s : ℝ, 0 < s →
    ∀ F : HermitianMatrix (Fin N), CEHDeformationBound κ C s F.1 →
    ∀ (z : ℂ) (M : CEHMatrix N),
      IsCEHMDESolution s F.1 z M → InCEHDomain ε κ s z M →
      CEHLocalLawAt gue δ D s F.1 z M

/-- Source-shaped package for the complete published CEH local input.  No value
of this structure is introduced in this contract module. -/
structure CEHLocalInput (gue : CEHGUEFamily) : Prop where
  mde_exists :
    ∀ (N : ℕ) (s : ℝ), 0 < s →
    ∀ (F : HermitianMatrix (Fin N)) (z : ℂ), z.im ≠ 0 →
      ∃ M : CEHMatrix N, IsCEHMDESolution s F.1 z M
  mde_unique :
    ∀ (N : ℕ) (s : ℝ), 0 < s →
    ∀ (F : HermitianMatrix (Fin N)) (z : ℂ) (M M' : CEHMatrix N),
      IsCEHMDESolution s F.1 z M → IsCEHMDESolution s F.1 z M' → M = M'
  localLaw : CEHLocalLawBound gue

end CEHNative.BlockBand
