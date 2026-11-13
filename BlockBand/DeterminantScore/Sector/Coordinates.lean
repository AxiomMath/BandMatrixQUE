module

public import BlockBand.DeterminantScore.Sector.RealPolynomial
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Hermitian coordinates and the determinant and adjugate polynomials

Basic properties of the real coordinate map `hermOfCoord` onto Hermitian matrices, its inverse
`coordOfMatrix`, and the polynomials `detPoly K` and `adjPoly K a b` in the coordinates whose real
evaluations are `det(K + G(x))` and `adj(K + G(x))_ab`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.Sector

open Matrix MvPolynomial

variable {m : ℕ}

theorem hermOfCoord_apply (x : HermCoord m → ℝ) (a b : Fin m) :
    hermOfCoord x a b =
      if a = b then (x (a, a) : ℂ)
      else if a < b then (x (a, b) : ℂ) + (x (b, a) : ℂ) * Complex.I
      else (x (b, a) : ℂ) - (x (a, b) : ℂ) * Complex.I := rfl

theorem isHermitian_hermOfCoord (x : HermCoord m → ℝ) : (hermOfCoord x).IsHermitian := by
  ext a b
  simp only [conjTranspose_apply, hermOfCoord_apply]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.ne, h.ne', not_lt_of_gt h, h]
  · simp
  · simp [h.ne, h.ne', not_lt_of_gt h, h, sub_eq_add_neg]

theorem hermOfCoord_add (x y : HermCoord m → ℝ) :
    hermOfCoord (x + y) = hermOfCoord x + hermOfCoord y := by
  ext a b
  simp only [hermOfCoord_apply, Pi.add_apply, Matrix.add_apply, Complex.ofReal_add]
  split_ifs <;> ring

theorem hermOfCoord_smul (r : ℝ) (x : HermCoord m → ℝ) :
    hermOfCoord (r • x) = (r : ℂ) • hermOfCoord x := by
  ext a b
  simp only [hermOfCoord_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply,
    Complex.ofReal_mul]
  split_ifs <;> ring

theorem hermOfCoord_update (x : HermCoord m → ℝ) (c : HermCoord m) (s : ℝ) :
    hermOfCoord (Function.update x c s) =
      hermOfCoord (Function.update x c 0) + (s : ℂ) • hermOfCoord (Pi.single c 1) := by
  have h : Function.update x c s = Function.update x c 0 + s • Pi.single c 1 := by
    funext j
    by_cases hj : j = c
    · subst hj; simp
    · simp [hj]
  rw [h, hermOfCoord_add, hermOfCoord_smul]

theorem continuous_hermOfCoord : Continuous (hermOfCoord (m := m)) := by
  refine continuous_matrix fun a b => ?_
  simp only [hermOfCoord_apply]
  split_ifs <;> fun_prop

/-- Coordinates of a matrix: diagonal real parts, upper real parts and upper imaginary parts. -/
def coordOfMatrix (A : Matrix (Fin m) (Fin m) ℂ) : HermCoord m → ℝ :=
  fun c => if c.1 = c.2 then (A c.1 c.1).re
    else if c.1 < c.2 then (A c.1 c.2).re else (A c.2 c.1).im

theorem hermOfCoord_coordOfMatrix {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) :
    hermOfCoord (coordOfMatrix A) = A := by
  ext a b
  simp only [hermOfCoord_apply, coordOfMatrix]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.ne, h.ne', not_lt_of_gt h, h, Complex.re_add_im]
  · have h1 := hA.apply a a
    apply Complex.ext
    · simp
    · have := congrArg Complex.im h1
      simp at this ⊢
      linarith
  · have h1 := hA.apply a b
    simp only [h.ne', h.ne, ↓reduceIte, not_lt_of_gt h, h]
    rw [← h1]
    apply Complex.ext <;> simp

/-- The polynomial matrix `K + Σ_c X_c E_c` with real-coordinate evaluation `K + G(x)`. -/
def hermPolyMatrix (K : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (HermCoord m) ℂ) :=
  Matrix.of fun a b => C (K a b) +
    (if a = b then X (a, a)
    else if a < b then X (a, b) + C Complex.I * X (b, a)
    else X (b, a) - C Complex.I * X (a, b))

theorem mapMatrix_eval_hermPolyMatrix (K : Matrix (Fin m) (Fin m) ℂ) (x : HermCoord m → ℝ) :
    (MvPolynomial.eval fun i => (x i : ℂ)).mapMatrix (hermPolyMatrix K) =
      K + hermOfCoord x := by
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hermPolyMatrix, Matrix.of_apply,
    Matrix.add_apply, hermOfCoord_apply]
  split_ifs <;> simp <;> ring

/-- The determinant polynomial `det(K + G(x))`. -/
def detPoly (K : Matrix (Fin m) (Fin m) ℂ) : MvPolynomial (HermCoord m) ℂ :=
  (hermPolyMatrix K).det

/-- The adjugate-entry polynomial `adj(K + G(x))_ab`. -/
def adjPoly (K : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m) : MvPolynomial (HermCoord m) ℂ :=
  (hermPolyMatrix K).adjugate a b

theorem realEval_detPoly (K : Matrix (Fin m) (Fin m) ℂ) (x : HermCoord m → ℝ) :
    realEval (detPoly K) x = (K + hermOfCoord x).det := by
  unfold realEval detPoly
  rw [RingHom.map_det, mapMatrix_eval_hermPolyMatrix]

theorem realEval_adjPoly (K : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m) (x : HermCoord m → ℝ) :
    realEval (adjPoly K a b) x = (K + hermOfCoord x).adjugate a b := by
  unfold realEval adjPoly
  rw [← mapMatrix_eval_hermPolyMatrix, ← RingHom.map_adjugate]
  rfl

end BlockBand.DeterminantScore.Sector
