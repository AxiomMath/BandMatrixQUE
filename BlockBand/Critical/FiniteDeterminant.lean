module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The normalized finite entire determinant

This file isolates the finite-dimensional analytic object underlying the entire
determinant of the paper.  Given a
base matrix `A`, finitely many source matrices `Q a`, a source scale `s`, and
an explicit deterministic normalizer `N`, the source pencil is

`A + s • ∑ a, z a • Q a`

and its normalized characteristic determinant is its determinant divided by
`N`.  The sole denominator hypothesis is the exact one needed here, `N ≠ 0`.
In the application, `A = H - E`, `s = W⁻²`, `Q 0 = I`, and the
normalizer is the nonvanishing determinant chosen by the finite closing
construction.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped BigOperators Matrix

namespace BlockBand.Critical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {m : ℕ}

/-- An explicit deterministic denominator for a normalized finite determinant.

The nonvanishing field is deliberately part of the data: division by an
unspecified or almost-surely nonzero random denominator is not hidden in this
finite analytic definition. -/
structure EntireDeterminantNormalizer where
  value : ℂ
  nonzero : value ≠ 0

namespace EntireDeterminantNormalizer

instance : Coe EntireDeterminantNormalizer ℂ := ⟨EntireDeterminantNormalizer.value⟩

@[simp] theorem coe_ne_zero (N : EntireDeterminantNormalizer) : (N : ℂ) ≠ 0 :=
  N.nonzero

end EntireDeterminantNormalizer

/-- The finite affine characteristic pencil in the source variables.

The scalar `scale` is kept explicit; for the entire determinant it is
`W⁻²`.  Coordinate zero being the energy direction is expressed at the
specialization site by the exact hypothesis `Q 0 = 1`, rather than built into
this index-agnostic finite object. -/
def finiteCharacteristicPencil
    (A : Matrix ι ι ℂ) (Q : Fin m → Matrix ι ι ℂ) (scale : ℂ)
    (z : Fin m → ℂ) : Matrix ι ι ℂ :=
  A + scale • ∑ a, z a • Q a

/-- The unnormalized finite characteristic entire function. -/
def finiteCharacteristicDeterminant
    (A : Matrix ι ι ℂ) (Q : Fin m → Matrix ι ι ℂ) (scale : ℂ)
    (z : Fin m → ℂ) : ℂ :=
  (finiteCharacteristicPencil A Q scale z).det

/-- The normalized finite characteristic entire
function, divided by an explicit deterministic nonvanishing normalizer. -/
def normalizedEntireDeterminant
    (A : Matrix ι ι ℂ) (Q : Fin m → Matrix ι ι ℂ) (scale : ℂ)
    (N : EntireDeterminantNormalizer) (z : Fin m → ℂ) : ℂ :=
  finiteCharacteristicDeterminant A Q scale z / (N : ℂ)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem finiteCharacteristicPencil_zero
    (A : Matrix ι ι ℂ) (Q : Fin m → Matrix ι ι ℂ) (scale : ℂ) :
    finiteCharacteristicPencil A Q scale 0 = A := by
  simp [finiteCharacteristicPencil]

@[simp] theorem finiteCharacteristicDeterminant_zero
    (A : Matrix ι ι ℂ) (Q : Fin m → Matrix ι ι ℂ) (scale : ℂ) :
    finiteCharacteristicDeterminant A Q scale 0 = A.det := by
  simp [finiteCharacteristicDeterminant]

@[simp] theorem normalizedEntireDeterminant_zero
    (A : Matrix ι ι ℂ) (Q : Fin m → Matrix ι ι ℂ) (scale : ℂ)
    (N : EntireDeterminantNormalizer) :
    normalizedEntireDeterminant A Q scale N 0 = A.det / (N : ℂ) := by
  simp [normalizedEntireDeterminant]

/-- If the deterministic normalizer is exactly the base determinant, the
normalized entire determinant takes the value one at the origin. -/
theorem normalizedEntireDeterminant_zero_eq_one
    (A : Matrix ι ι ℂ) (Q : Fin m → Matrix ι ι ℂ) (scale : ℂ)
    (N : EntireDeterminantNormalizer) (hN : (N : ℂ) = A.det) :
    normalizedEntireDeterminant A Q scale N 0 = 1 := by
  rw [normalizedEntireDeterminant_zero, ← hN]
  exact div_self N.nonzero

omit [Fintype ι] [DecidableEq ι] in
/-- Every entry of the finite characteristic pencil is an affine, hence
entire, function of all source coordinates. -/
theorem differentiable_finiteCharacteristicPencil_apply
    (A : Matrix ι ι ℂ) (Q : Fin m → Matrix ι ι ℂ) (scale : ℂ) (i j : ι) :
    Differentiable ℂ (fun z : Fin m → ℂ => finiteCharacteristicPencil A Q scale z i j) := by
  simp only [finiteCharacteristicPencil, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sum_apply, Finset.smul_sum]
  fun_prop

/-- The determinant of the finite source pencil is entire in all source
variables. -/
theorem differentiable_finiteCharacteristicDeterminant
    (A : Matrix ι ι ℂ) (Q : Fin m → Matrix ι ι ℂ) (scale : ℂ) :
    Differentiable ℂ (finiteCharacteristicDeterminant A Q scale) := by
  rw [show finiteCharacteristicDeterminant A Q scale = fun z =>
      ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℂ) *
        ∏ i, finiteCharacteristicPencil A Q scale z (σ i) i by
    funext z
    exact Matrix.det_apply' (finiteCharacteristicPencil A Q scale z)]
  have hprod : ∀ σ : Equiv.Perm ι,
      Differentiable ℂ (fun z : Fin m → ℂ =>
        ∏ i, finiteCharacteristicPencil A Q scale z (σ i) i) := by
    intro σ z
    classical
    induction (Finset.univ : Finset ι) using Finset.induction with
    | empty =>
        simp
    | @insert i s hi ih =>
        simp only [Finset.prod_insert hi]
        exact
          (differentiable_finiteCharacteristicPencil_apply A Q scale (σ i) i z).mul ih
  fun_prop

/-- Division by the explicit nonzero deterministic normalizer preserves the
entire finite characteristic function. -/
theorem differentiable_normalizedEntireDeterminant
    (A : Matrix ι ι ℂ) (Q : Fin m → Matrix ι ι ℂ) (scale : ℂ)
    (N : EntireDeterminantNormalizer) :
    Differentiable ℂ (normalizedEntireDeterminant A Q scale N) := by
  intro z
  change DifferentiableAt ℂ
    (fun x => finiteCharacteristicDeterminant A Q scale x * (N : ℂ)⁻¹) z
  exact (differentiable_finiteCharacteristicDeterminant A Q scale z).mul
    (differentiableAt_const (c := (N : ℂ)⁻¹))

/-- Exact quotient identity, useful when a closing theorem supplies the
unnormalized determinant separately. -/
theorem normalizedEntireDeterminant_mul_normalizer
    (A : Matrix ι ι ℂ) (Q : Fin m → Matrix ι ι ℂ) (scale : ℂ)
    (N : EntireDeterminantNormalizer) (z : Fin m → ℂ) :
    normalizedEntireDeterminant A Q scale N z * (N : ℂ) =
      finiteCharacteristicDeterminant A Q scale z := by
  exact div_mul_cancel₀ _ N.nonzero

end BlockBand.Critical
