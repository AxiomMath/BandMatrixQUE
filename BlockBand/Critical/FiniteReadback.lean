module

public import BlockBand.Critical.FiniteDeterminant
public import Mathlib.Tactic

/-!
# Exact finite energy-source normalization

Deterministic identities for the entire determinant and the first step of the joint
recovery theorem.  The finite source scale is exactly `(W : ℂ)⁻¹ ^ 2`;
coordinate zero is exactly the identity matrix. The unfolding is
`u = -(n/W) * rho * z`, with `z = -W² * (lambda-E)`.
These identities are pointwise for arbitrary finite complex matrices, with no
measure, norm estimate, asymptotic limit, or choice of physical law. In the
physical application `W > 0`, `rho = rho(E)`, and the denominator is
`det(H-E)`, whose almost-sure nonvanishing is a separate statement.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open scoped BigOperators Matrix
namespace BlockBand.Critical

/-- Energy variable in coordinate zero; all spatial sources vanish. -/
def energySource {m : ℕ} (z : ℂ) : Fin (m + 1) → ℂ :=
  Pi.single 0 z

/-- Exact physical `W⁻²` scale, with no replacement by `N⁻¹`. -/
def widthSourceScale (W : ℕ) : ℂ := (W : ℂ)⁻¹ ^ 2

/-- Setting all spatial sources to zero retains precisely the identity energy
source. This is an algebraic finite-width component, uniformly in all matrices. -/
theorem finiteCharacteristicPencil_energySource
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A : Matrix ι ι ℂ) (Q : Fin (m + 1) → Matrix ι ι ℂ)
    (scale z : ℂ) (hQ : Q 0 = 1) :
    finiteCharacteristicPencil A Q scale (energySource z) =
      A + scale • (z • (1 : Matrix ι ι ℂ)) := by
  classical
  simp [finiteCharacteristicPencil, energySource, Pi.single_apply, hQ]

/-- The finite entire quotient, normalized by its base determinant.
This requires exact nonvanishing at the given finite matrix; it is not a
probabilistic nonvanishing assertion. -/
def physicalFiniteDeterminant
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A : Matrix ι ι ℂ) (Q : Fin (m + 1) → Matrix ι ι ℂ)
    (W : ℕ) (hA : A.det ≠ 0) : (Fin (m + 1) → ℂ) → ℂ :=
  normalizedEntireDeterminant A Q (widthSourceScale W) ⟨A.det, hA⟩

/-- Exact `D_W(0)=1` for the complete finite quotient. -/
@[simp] theorem physicalFiniteDeterminant_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A : Matrix ι ι ℂ) (Q : Fin (m + 1) → Matrix ι ι ℂ)
    (W : ℕ) (hA : A.det ≠ 0) :
    physicalFiniteDeterminant A Q W hA 0 = 1 :=
  normalizedEntireDeterminant_zero_eq_one A Q (widthSourceScale W) ⟨A.det, hA⟩ rfl

/-- The complete physical finite quotient is complex differentiable in every
source coordinate; no first-trace exponential has been removed. -/
theorem differentiable_physicalFiniteDeterminant
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A : Matrix ι ι ℂ) (Q : Fin (m + 1) → Matrix ι ι ℂ)
    (W : ℕ) (hA : A.det ≠ 0) :
    Differentiable ℂ (physicalFiniteDeterminant A Q W hA) :=
  differentiable_normalizedEntireDeterminant A Q (widthSourceScale W) ⟨A.det, hA⟩

/-- Exact sign and volume relation from the original-ring zero variable to
physical unfolding. Requires only nonzero width, with arbitrary real energy,
spectral location and density. No parity assumption enters. -/
theorem originalRing_unfolding (n W : ℕ) (hW : W ≠ 0) (rho lam E : ℝ) :
    -((n : ℝ) / (W : ℝ)) * rho * (-(W : ℝ)^2 * (lam-E)) =
      ((n : ℝ) * (W : ℝ)) * rho * (lam-E) := by
  have hw : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hW
  field_simp

/-- Division-free source readback, for an arbitrary derivative vector with
nonzero energy coordinate.  That this vector is the determinant derivative at a
physical eigenpair is `finite_eigenpair_source_readback`. -/
theorem sourceRatio_mul_energy {m : ℕ} (d : Fin (m + 1) → ℂ)
    (hd : d 0 ≠ 0) (a : Fin (m + 1)) : (d a / d 0) * d 0 = d a :=
  div_mul_cancel₀ _ hd

/-- Exact probability normalization in the energy coordinate of source readback. -/
theorem sourceRatio_energy {m : ℕ} (d : Fin (m + 1) → ℂ)
    (hd : d 0 ≠ 0) : d 0 / d 0 = 1 := div_self hd

end BlockBand.Critical
