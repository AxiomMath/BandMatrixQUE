module

public import BlockBand.Coarea.Native.BlockBand.Coarea.SchurData
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Eigenvalue crossing for Hermitian affine families

The Hellmann–Feynman calculation behind the rank sector of the eigenpair coarea formula.
Parameters are real, matrices and vectors are complex, and vectors are normalized by
`vᴴv = 1`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Matrix

/-- Product rule for a real-parameterized complex matrix acting on a vector. -/
theorem hasDerivAt_matrix_mulVec
    {n : Type*} [Fintype n]
    {A : ℝ → Matrix n n ℂ} {v : ℝ → n → ℂ}
    {A' : Matrix n n ℂ} {v' : n → ℂ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => A s *ᵥ v s)
      (A' *ᵥ v t + A t *ᵥ v') t := by
  rw [hasDerivAt_pi]
  intro i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply]
  convert HasDerivAt.fun_sum (u := Finset.univ)
      (A := fun j s => A s i j * v s j)
      (A' := fun j => A' i j * v t j + A t i j * v' j) ?_ using 1 <;>
    simp only [Finset.sum_add_distrib, Finset.mem_univ]
  intro j _
  exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) j).mul
    (hasDerivAt_pi.mp hv j)

/-- Algebraic Hellmann–Feynman identity after differentiating an eigenpair equation.
The simplicity assumption needed to produce a differentiable local branch is deliberately
separate: once such a branch has been chosen, this calculation only uses Hermiticity and
unit normalization. -/
theorem hellmannFeynman_of_differentiated_eigenpair
    {n : Type*} [Fintype n]
    {A A' : Matrix n n ℂ} {v v' : n → ℂ} {e e' : ℝ}
    (hA : A.IsHermitian)
    (heig : A *ᵥ v = (e : ℂ) • v)
    (hnorm : star v ⬝ᵥ v = 1)
    (hderiv : A' *ᵥ v + A *ᵥ v' = (e : ℂ) • v' + (e' : ℂ) • v) :
    (e' : ℂ) = star v ⬝ᵥ (A' *ᵥ v) := by
  have hadj : star v ⬝ᵥ (A *ᵥ v') = (e : ℂ) * (star v ⬝ᵥ v') := by
    calc
      star v ⬝ᵥ (A *ᵥ v') = star (A *ᵥ v) ⬝ᵥ v' := by
        rw [Matrix.star_mulVec, hA.eq, ← Matrix.dotProduct_mulVec]
      _ = star ((e : ℂ) • v) ⬝ᵥ v' := by rw [heig]
      _ = (e : ℂ) * (star v ⬝ᵥ v') := by
        have hstar : star ((e : ℂ) • v) = (e : ℂ) • star v := by
          ext i
          simp
        rw [hstar]
        rw [smul_dotProduct]
        rfl
  have hdot := congrArg (fun w : n → ℂ => star v ⬝ᵥ w) hderiv
  simp only [dotProduct_add] at hdot
  simp only [dotProduct_smul, hnorm, smul_eq_mul] at hdot
  rw [hadj] at hdot
  rw [mul_one, add_comm ((e : ℂ) * (star v ⬝ᵥ v'))] at hdot
  exact (add_right_cancel hdot).symm

/-- A unit eigenvector spanning its entire eigenspace for a Hermitian matrix.
This packages the paper's "selected simple eigenpair" hypothesis without choosing
an ordered eigenvalue API. -/
structure SimpleHermitianEigenpair
    {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (e : ℝ) (v : n → ℂ) : Prop where
  hermitian : A.IsHermitian
  eigenvector : A *ᵥ v = (e : ℂ) • v
  normalized : star v ⬝ᵥ v = 1
  eigenspace_eq_span :
    ∀ w : n → ℂ, A *ᵥ w = (e : ℂ) • w → ∃ c : ℂ, w = c • v

/-- Hellmann–Feynman for a differentiable branch through a simple Hermitian eigenpair.
The parameter and eigenvalue are real, while matrices and eigenvectors are complex. -/
theorem hellmannFeynman_simpleEigenpairCurve
    {n : Type*} [Fintype n]
    {A : ℝ → Matrix n n ℂ} {v : ℝ → n → ℂ} {e : ℝ → ℝ}
    {A' : Matrix n n ℂ} {v' : n → ℂ} {e' t : ℝ}
    (hsimple : SimpleHermitianEigenpair (A t) (e t) (v t))
    (hAderiv : HasDerivAt A A' t)
    (hvderiv : HasDerivAt v v' t)
    (hederiv : HasDerivAt e e' t)
    (heigenpair : ∀ s : ℝ, A s *ᵥ v s = (e s : ℂ) • v s) :
    (e' : ℂ) = star (v t) ⬝ᵥ (A' *ᵥ v t) := by
  have hlhs := hasDerivAt_matrix_mulVec hAderiv hvderiv
  have hrhs := hederiv.ofReal_comp.smul hvderiv
  have hrhs' : HasDerivAt (fun s => A s *ᵥ v s)
      ((e t : ℂ) • v' + (e' : ℂ) • v t) t :=
    hrhs.congr_of_eventuallyEq (Filter.Eventually.of_forall heigenpair)
  have hdiff : A' *ᵥ v t + A t *ᵥ v' =
      (e t : ℂ) • v' + (e' : ℂ) • v t :=
    hlhs.unique hrhs'
  exact hellmannFeynman_of_differentiated_eigenpair
    hsimple.hermitian hsimple.eigenvector hsimple.normalized hdiff

/-- Crossing formula when the matrix derivative is `-D`.  This is the form used
for a Hermitian affine family, and also for the Schur complement after its derivative
has been identified. -/
theorem hellmannFeynman_crossing
    {n : Type*} [Fintype n]
    {A : ℝ → Matrix n n ℂ} (D : Matrix n n ℂ)
    {v : ℝ → n → ℂ} {e : ℝ → ℝ}
    {v' : n → ℂ} {e' t : ℝ}
    (hsimple : SimpleHermitianEigenpair (A t) (e t) (v t))
    (hAderiv : HasDerivAt A (-D) t)
    (hvderiv : HasDerivAt v v' t)
    (hederiv : HasDerivAt e e' t)
    (heigenpair : ∀ s : ℝ, A s *ᵥ v s = (e s : ℂ) • v s) :
    (e' : ℂ) = -(star (v t) ⬝ᵥ (D *ᵥ v t)) := by
  rw [hellmannFeynman_simpleEigenpairCurve hsimple hAderiv hvderiv hederiv
    heigenpair]
  simp [Matrix.neg_mulVec]

/-- Schur-clock specialization of the crossing formula.

Normalization: the branch vector has `vᴴv = 1`,
`𝒟 = I + TᴴT`, and the physical-energy derivative of the matrix family is
`-𝒟`; hence the real eigenvalue derivative, embedded in `ℂ`, is exactly
`-vᴴ𝒟v`.  The statement is finite-dimensional over arbitrary finite index
types and has no probabilistic uniformity or limiting operation. -/
theorem hellmannFeynman_schurClockCrossing
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    {A : ℝ → Matrix m m ℂ} (T : Matrix n m ℂ)
    {v : ℝ → m → ℂ} {e : ℝ → ℝ}
    {v' : m → ℂ} {e' t : ℝ}
    (hsimple : SimpleHermitianEigenpair (A t) (e t) (v t))
    (hAderiv : HasDerivAt A (-(schurClock T)) t)
    (hvderiv : HasDerivAt v v' t)
    (hederiv : HasDerivAt e e' t)
    (heigenpair : ∀ s : ℝ, A s *ᵥ v s = (e s : ℂ) • v s) :
    (e' : ℂ) =
      -(star (v t) ⬝ᵥ (schurClock T *ᵥ v t)) :=
  hellmannFeynman_crossing (schurClock T)
    hsimple hAderiv hvderiv hederiv heigenpair

/-- The Schur-clock crossing is strict: its real eigenvalue branch has negative
slope at the selected simple zero. Positivity comes
from the identity term in `𝒟 = I + TᴴT`.  This is an exact finite-dimensional
statement, with no asymptotic parameter or limit order. -/
theorem hellmannFeynman_schurClockCrossing_neg
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    {A : ℝ → Matrix m m ℂ} (T : Matrix n m ℂ)
    {v : ℝ → m → ℂ} {e : ℝ → ℝ}
    {v' : m → ℂ} {e' t : ℝ}
    (hsimple : SimpleHermitianEigenpair (A t) (e t) (v t))
    (hAderiv : HasDerivAt A (-(schurClock T)) t)
    (hvderiv : HasDerivAt v v' t)
    (hederiv : HasDerivAt e e' t)
    (heigenpair : ∀ s : ℝ, A s *ᵥ v s = (e s : ℂ) • v s) :
    e' < 0 := by
  have hv0 : v t ≠ 0 := by
    intro hv
    have hn := hsimple.normalized
    rw [hv] at hn
    simp at hn
  have hq := schurClock_quadratic_pos T hv0
  have hcross := hellmannFeynman_schurClockCrossing T hsimple hAderiv
    hvderiv hederiv heigenpair
  have hreal := congrArg Complex.re hcross
  simp only [Complex.ofReal_re] at hreal
  exact hreal.trans_lt (neg_lt_zero.mpr (Complex.pos_iff.mp hq).1)

end CoareaNative.BlockBand
