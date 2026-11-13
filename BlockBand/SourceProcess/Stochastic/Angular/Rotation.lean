module

public import BlockBand.SourceProcess.Stochastic.Angular.Conj
public import BlockBand.SourceProcess.Stochastic.Angular.Curve

/-!
# Complex angular contract: pair rotations in the eigenbasis

For labels `i ≠ j` and a generator `J` with `J* = -J`, `J² = -Π`, `ΠJ = JΠ = J`
(`Π = E_ii + E_jj`), the matrix `R(α) = 1 + (cos α - 1) Π + sin α J` is unitary
(`rot_star_mul`). The two generators are `jX = E_ji - E_ij` and `jY = i(E_ji + E_ij)`; acting on
arrays by `arrMul M Z = (∑_m M_mk Z_m)_k`, they are the contract's fields `X_ij`, `Y_ij`
(`arrMul_jX`, `arrMul_jY`).

These rotations are used with two results proved in the sibling module:
* `trigCurve`: curves `v₀ + (cos t - 1) v₁ + sin t v₂ + …`, with first and second derivatives;
* `hasDerivAt_deriv_comp`: the second-order chain rule `(g ∘ γ)''(0) = D²g[γ', γ'] + Dg[γ'']`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open Matrix Filter Topology
open scoped Matrix ComplexConjugate
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionAngular
open BlockBand.SourceProcess.Stochastic.Dyson

variable {N r : ℕ}

/-!
### Matrices acting on arrays
-/

/-- `(arrMul M Z)_k = ∑_m M_mk Z_m`: the array of the columns of `U M` when `Z` is that of `U`. -/
def arrMul (M : Matrix (Fin N) (Fin N) ℂ) (Z : AngularArray N r) : AngularArray N r :=
  fun k a => ∑ m, M m k * Z m a

theorem arrMul_one (Z : AngularArray N r) : arrMul 1 Z = Z := by
  funext k a; simp [arrMul, Matrix.one_apply]

theorem arrMul_add (M M' : Matrix (Fin N) (Fin N) ℂ) (Z : AngularArray N r) :
    arrMul (M + M') Z = arrMul M Z + arrMul M' Z := by
  funext k a; simp [arrMul, add_mul, Finset.sum_add_distrib]

theorem arrMul_smul (c : ℝ) (M : Matrix (Fin N) (Fin N) ℂ) (Z : AngularArray N r) :
    arrMul (c • M) Z = c • arrMul M Z := by
  funext k a
  simp only [arrMul, Matrix.smul_apply, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_mul_assoc]

theorem arrMul_neg (M : Matrix (Fin N) (Fin N) ℂ) (Z : AngularArray N r) :
    arrMul (-M) Z = -arrMul M Z := by
  funext k a; simp [arrMul, Finset.sum_neg_distrib]

theorem arrMul_mul (M M' : Matrix (Fin N) (Fin N) ℂ) (Z : AngularArray N r) :
    arrMul (M * M') Z = arrMul M' (arrMul M Z) := by
  funext k a
  simp only [arrMul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring

theorem angularArray_mul (V : Matrix (Fin N) (Fin r) ℂ) (U M : Matrix (Fin N) (Fin N) ℂ) :
    angularArray V (fun k b => (U * M) b k) = arrMul M (angularArray V fun k b => U b k) := by
  funext k a
  simp only [angularArray, arrMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun b _ => by ring

theorem arrZ_eq_eigMat (V : Matrix (Fin N) (Fin r) ℂ) (y : Fin (N * N) → ℝ) :
    arrZ V y = angularArray V fun k b => eigMat N y b k := rfl

/-!
### Pair matrices
-/

/-- `Π = E_ii + E_jj`. -/
def piM (i j : Fin N) : Matrix (Fin N) (Fin N) ℂ := single i i 1 + single j j 1

/-- The real rotation generator `E_ji - E_ij`. -/
def jX (i j : Fin N) : Matrix (Fin N) (Fin N) ℂ := single j i 1 - single i j 1

/-- The complex rotation generator `i(E_ji + E_ij)`. -/
def jY (i j : Fin N) : Matrix (Fin N) (Fin N) ℂ := Complex.I • (single j i 1 + single i j 1)

theorem star_piM (i j : Fin N) : star (piM (N := N) i j) = piM i j := by
  simp [piM, star_eq_conjTranspose, conjTranspose_single]

theorem star_jX (i j : Fin N) : star (jX (N := N) i j) = -jX i j := by
  simp [jX, star_eq_conjTranspose, conjTranspose_single]

theorem star_jY (i j : Fin N) : star (jY (N := N) i j) = -jY i j := by
  simp only [jY, star_eq_conjTranspose, conjTranspose_smul, conjTranspose_add,
    conjTranspose_single, star_one, Complex.star_def, Complex.conj_I, neg_smul]
  rw [add_comm]

section Pair
variable {i j : Fin N} (hij : i ≠ j)
include hij

theorem piM_mul_self : piM i j * piM i j = piM i j := by
  simp [piM, add_mul, mul_add, hij, hij.symm]

theorem jX_mul_self : jX i j * jX i j = -piM i j := by
  simp [jX, piM, sub_mul, mul_sub, hij, hij.symm]; abel

theorem piM_mul_jX : piM i j * jX i j = jX i j := by
  simp [jX, piM, mul_sub, add_mul, hij, hij.symm]

theorem jX_mul_piM : jX i j * piM i j = jX i j := by
  simp [jX, piM, sub_mul, mul_add, hij, hij.symm]; abel

theorem jY_mul_self : jY i j * jY i j = -piM i j := by
  have hK : (single j i 1 + single i j 1 : Matrix (Fin N) (Fin N) ℂ) *
      (single j i 1 + single i j 1) = piM i j := by
    simp [piM, add_mul, mul_add, hij, hij.symm, add_comm]
  rw [jY, smul_mul_smul_comm, hK, Complex.I_mul_I, neg_one_smul]

theorem piM_mul_jY : piM i j * jY i j = jY i j := by
  simp [jY, piM, add_mul, mul_add, hij, hij.symm, add_comm]

theorem jY_mul_piM : jY i j * piM i j = jY i j := by
  simp [jY, piM, add_mul, mul_add, hij, hij.symm]

theorem arrMul_jX (Z : AngularArray N r) : arrMul (jX i j) Z = pairRotX i j Z := by
  funext k a
  by_cases hki : k = i
  · subst hki
    simp [arrMul, jX, pairRotX, single_apply, hij.symm]
  · by_cases hkj : k = j
    · subst hkj
      simp [arrMul, jX, pairRotX, single_apply, hki, Ne.symm hki]
    · simp [arrMul, jX, pairRotX, hki, hkj, Ne.symm hki, Ne.symm hkj]

theorem arrMul_jY (Z : AngularArray N r) : arrMul (jY i j) Z = pairRotY i j Z := by
  funext k a
  by_cases hki : k = i
  · subst hki
    simp [arrMul, jY, pairRotY, single_apply, hij.symm]
  · by_cases hkj : k = j
    · subst hkj
      simp [arrMul, jY, pairRotY, single_apply, hki, Ne.symm hki]
    · simp [arrMul, jY, pairRotY, hki, hkj, Ne.symm hki, Ne.symm hkj]

end Pair

/-!
### The rotation `R(α) = 1 + (cos α - 1) Π + sin α J`
-/

/-- The pair rotation generated by `J` on the block `P`. -/
def rot (P J : Matrix (Fin N) (Fin N) ℂ) (α : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  1 + (Real.cos α - 1) • P + Real.sin α • J

section Rot
variable {P J : Matrix (Fin N) (Fin N) ℂ}

theorem star_rot (hPs : star P = P) (hJs : star J = -J) (α : ℝ) :
    star (rot P J α) = 1 + (Real.cos α - 1) • P - Real.sin α • J := by
  simp only [rot, star_add, star_smul, star_one, star_trivial, hPs, hJs, smul_neg,
    sub_eq_add_neg]

variable (hPs : star P = P) (hJs : star J = -J) (hPP : P * P = P) (hJJ : J * J = -P)
  (hPJ : P * J = J) (hJP : J * P = J)
include hPs hJs hPP hJJ hPJ hJP

theorem rot_star_mul (α : ℝ) : star (rot P J α) * rot P J α = 1 := by
  rw [star_rot hPs hJs]
  simp only [rot, add_mul, mul_add, sub_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    hPP, hJJ, hPJ, hJP]
  linear_combination (norm := module) (Real.cos_sq_add_sin_sq α) • P

theorem rot_mul_star (α : ℝ) : rot P J α * star (rot P J α) = 1 := by
  rw [star_rot hPs hJs]
  simp only [rot, add_mul, mul_add, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    hPP, hJJ, hPJ, hJP]
  linear_combination (norm := module) (Real.cos_sq_add_sin_sq α) • P

end Rot

theorem rot_mul_mul_star {P J : Matrix (Fin N) (Fin N) ℂ} (hPs : star P = P) (hJs : star J = -J)
    (D : Matrix (Fin N) (Fin N) ℂ) (α : ℝ) :
    rot P J α * D * star (rot P J α) = trigCurve D (P * D + D * P) (J * D - D * J) (P * D * P)
      (J * D * P - P * D * J) (J * D * J) α := by
  rw [star_rot hPs hJs]
  simp only [rot, trigCurve, add_mul, mul_add, mul_sub, sub_mul, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc]
  module

theorem arrMul_rot {P J : Matrix (Fin N) (Fin N) ℂ} (hJJ : J * J = -P) (Z : AngularArray N r)
    (α : ℝ) : arrMul (rot P J α) Z =
      trigCurve Z (-arrMul J (arrMul J Z)) (arrMul J Z) 0 0 0 α := by
  have hP : arrMul P Z = -arrMul J (arrMul J Z) := by
    rw [← arrMul_mul, hJJ, arrMul_neg, neg_neg]
  simp only [rot, arrMul_add, arrMul_smul, arrMul_one, hP, trigCurve, smul_zero, add_zero,
    sub_zero]

end BlockBand.SourceProcess.Stochastic.ComplexAngular
