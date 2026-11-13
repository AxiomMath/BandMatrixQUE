module

public import BlockBand.External.CEH.SourceModel
public import BlockBand.External.CEH.SourceObservables

/-!
# The matrix Dyson equation and the typical spacing for the deformed Wigner model

This file defines, following CEH (arXiv:2607.02446v2), the solutions of the matrix Dyson
equation (MDE) of `H_λ = H₀ + λW`, a measurable MDE branch off the real axis, the associated
density, the local-law spectral domain, the typical eigenvalue spacing `η_f` and the MDE
evaluated at the inflated points `E_i + i N^ξ η_f(E_i)`, `E_i` the eigenvalues of `H_λ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.External.CEH

open Matrix MeasureTheory
open scoped ComplexOrder ENNReal Topology Matrix.Norms.L2Operator

/-- `M` solves the MDE `(H₀ - z - λ² ⟨M⟩) M = 1` with the half-plane condition
`Im z · Im M > 0`, as in CEH (2.4); `⟨·⟩` is the normalized trace. -/
structure IsMDESolution {N : ℕ} (lambda : ℝ) (H0 : SourceHermitian N)
    (z : ℂ) (M : SourceMatrix N) : Prop where
  inverse_equation :
    (H0.1 - (z + (lambda : ℂ) ^ 2 * normalizedTrace M) • (1 : SourceMatrix N)) * M = 1
  halfPlane_positive : ((z.im : ℂ) • imaginaryPart M).PosDef

/-- A measurable branch `z ↦ M(z)` of MDE solutions on `ℂ \ ℝ`, continuous off the real axis.
Its values on the real axis play no role. -/
structure MDEBranch {N : ℕ} (lambda : ℝ) (H0 : SourceHermitian N) where
  matrix : ℂ → SourceMatrix N
  solution : ∀ z, z.im ≠ 0 → IsMDESolution lambda H0 z (matrix z)
  continuous_off_real : ContinuousOn matrix {z : ℂ | z.im ≠ 0}
  measurable_entry : ∀ a b, Measurable (fun z => matrix z a b)

/-- The density `ρ = |Im ⟨M⟩| / π`; the absolute value makes it valid in both half-planes. -/
def sourceDensity {N : ℕ} (M : SourceMatrix N) : ℝ :=
  |(normalizedTrace M).im| / Real.pi

/-- The density is nonnegative. -/
theorem sourceDensity_nonneg {N : ℕ} (M : SourceMatrix N) : 0 ≤ sourceDensity M := by
  exact div_nonneg (abs_nonneg _) Real.pi_pos.le

/-- The spectral domain of the local law (CEH Theorem 2.3): `Im z ≠ 0`,
`N |Im z| ρ(z) ≥ N^ε` and `|z| ≤ λ N^{κ + 1/ε}`, with no restriction to a compact energy
window. -/
def InLocalLawDomain {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N}
    (M : MDEBranch lambda H0) (kappa epsilon : ℝ) (z : ℂ) : Prop :=
  z.im ≠ 0 ∧
    (N : ℝ) * |z.im| * sourceDensity (M.matrix z) ≥ (N : ℝ) ^ epsilon ∧
    ‖z‖ ≤ lambda * (N : ℝ) ^ (kappa + 1 / epsilon)

/-- The typical spacing: a measurable `η_f > 0` with `N η_f(E) ρ(E + iη_f(E)) = 1` for every
`E`. It is not assumed to be comparable to `1/N`. -/
structure TypicalSpacing {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N}
    (M : MDEBranch lambda H0) where
  eta : ℝ → ℝ
  positive : ∀ E, 0 < eta E
  measurable_eta : Measurable eta
  equation : ∀ E,
    (N : ℝ) * eta E *
      sourceDensity (M.matrix ((E : ℂ) + (eta E : ℂ) * Complex.I)) = 1

/-- The inflated spectral point `E + i N^ξ η_f(E)` of CEH (2.12). -/
def inflatedSpectralPoint {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N}
    {M : MDEBranch lambda H0} (spacing : TypicalSpacing M) (xi E : ℝ) : ℂ :=
  (E : ℂ) + (((N : ℝ) ^ xi * spacing.eta E : ℝ) : ℂ) * Complex.I

/-- `M_i = M(E_i + i N^ξ η_f(E_i))`, with `E_i` the `i`-th ordered eigenvalue of `H_λ`. -/
def eigenvalueMDE {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N}
    (M : MDEBranch lambda H0) (spacing : TypicalSpacing M)
    (selection : EigenpairSelection N) (xi : ℝ) (W : SourceHermitian N)
    (i : Fin N) : SourceMatrix N :=
  M.matrix (inflatedSpectralPoint spacing xi
    (selection.eigenvalue (deformedHermitian lambda H0 W) i))

end BlockBand.External.CEH
