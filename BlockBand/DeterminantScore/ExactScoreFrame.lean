module

public import BlockBand.Angular.DetFactor
public import BlockBand.DeterminantScore.HorizontalVariation

/-!
# The rotating frame along a horizontal great circle

Finite-dimensional linear algebra in `ℂ^ι`, no measure. Let `U` be an orthonormal frame of
`v^⊥` (`IsFrame U v`), `‖v‖ = ‖h‖ = 1`, `h*v = 0`, and `a = U*h`. Along the great circle
`γ(ε) = cos ε v + sin ε h` (`rotVec`, `γ(0) = v`, `γ'(0) = h`) the matrix
`U(ε) = U + w(ε)a*`, `w(ε) = (cos ε - 1)h - sin ε v` (`rotFrame`) is an orthonormal frame of
`γ(ε)^⊥` for every `ε` (`isFrame_rotFrame`: it is `Γ(ε)U` with `Γ(ε)` the rotation of the plane
`span(v, h)`). For Hermitian `K₀`, the compression `K(ε) = U(ε)*K₀U(ε)` has entrywise derivative
at `ε = 0` (`paramDeriv_rotCompress`)
`∂K = -(a c* + c a*)`, `c = U*K₀v`,
the horizontal rank-two direction of `realJacobi_horizontal_rankTwo`.
Using this frame instead of the Householder frame avoids the rotational (skew) part of the frame
derivative: the derivative is computed in the given frame `U` itself.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.ExactScore

open Matrix Filter
open BlockBand.Angular.DetFactor BlockBand.DeterminantScore.Sector
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- `w(ε) = (cos ε - 1) h - sin ε v`. -/
def rotDir (v h : ι → ℂ) (ε : ℝ) : ι → ℂ :=
  ((Real.cos ε : ℂ) - 1) • h - (Real.sin ε : ℂ) • v

/-- The great circle `γ(ε) = cos ε v + sin ε h`. -/
def rotVec (v h : ι → ℂ) (ε : ℝ) : ι → ℂ :=
  (Real.cos ε : ℂ) • v + (Real.sin ε : ℂ) • h

/-- The rotated frame `U(ε) = U + w(ε)(U*h)*` of `γ(ε)^⊥`. -/
def rotFrame (U : Matrix ι (Fin m) ℂ) (v h : ι → ℂ) (ε : ℝ) : Matrix ι (Fin m) ℂ :=
  U + vecMulVec (rotDir v h ε) (star (Uᴴ *ᵥ h))

/-- The compression `K(ε) = U(ε)*K₀U(ε)`. -/
def rotCompress (U : Matrix ι (Fin m) ℂ) (v h : ι → ℂ) (K : Matrix ι ι ℂ) (ε : ℝ) :
    Matrix (Fin m) (Fin m) ℂ :=
  (rotFrame U v h ε)ᴴ * K * rotFrame U v h ε

theorem star_ofReal (r : ℝ) : star (r : ℂ) = r := Complex.conj_ofReal r

theorem rotFrame_zero (U : Matrix ι (Fin m) ℂ) (v h : ι → ℂ) : rotFrame U v h 0 = U := by
  simp [rotFrame, rotDir]

theorem rotVec_zero (v h : ι → ℂ) : rotVec v h 0 = v := by
  simp [rotVec]

theorem rotCompress_zero (U : Matrix ι (Fin m) ℂ) (v h : ι → ℂ) (K : Matrix ι ι ℂ) :
    rotCompress U v h K 0 = Uᴴ * K * U := by
  simp [rotCompress, rotFrame_zero]

theorem star_rotDir (v h : ι → ℂ) (ε : ℝ) :
    star (rotDir v h ε) = ((Real.cos ε : ℂ) - 1) • star h - (Real.sin ε : ℂ) • star v := by
  simp only [rotDir, star_sub, star_smul, star_ofReal, star_one]

section Orthonormal

variable {v h : ι → ℂ} (hv : star v ⬝ᵥ v = 1) (hh : star h ⬝ᵥ h = 1) (hhv : star h ⬝ᵥ v = 0)
include hv hh hhv

theorem star_v_dot_h : star v ⬝ᵥ h = 0 := by
  rw [star_dotProduct, hhv, star_zero]

theorem cos_sq_add_sin_sq_complex (ε : ℝ) :
    (Real.cos ε : ℂ) ^ 2 + (Real.sin ε : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.cos_sq_add_sin_sq ε

theorem rotDir_dot_self (ε : ℝ) :
    star (rotDir v h ε) ⬝ᵥ rotDir v h ε =
      ((Real.cos ε : ℂ) - 1) ^ 2 + (Real.sin ε : ℂ) ^ 2 := by
  have hvh := star_v_dot_h hv hh hhv
  rw [star_rotDir]
  simp only [rotDir, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    hv, hh, hhv, hvh, smul_eq_mul]
  ring

theorem rotDir_dot_rotVec (ε : ℝ) :
    star (rotDir v h ε) ⬝ᵥ rotVec v h ε = -(Real.sin ε : ℂ) := by
  have hvh := star_v_dot_h hv hh hhv
  rw [star_rotDir]
  simp only [rotVec, sub_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    hv, hh, hhv, hvh, smul_eq_mul]
  ring

theorem rotVec_dot_self (ε : ℝ) : star (rotVec v h ε) ⬝ᵥ rotVec v h ε = 1 := by
  have hvh := star_v_dot_h hv hh hhv
  simp only [rotVec, star_add, star_smul, star_ofReal, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, hv, hh, hhv, hvh, smul_eq_mul]
  linear_combination cos_sq_add_sin_sq_complex hv hh hhv ε

theorem rotVec_ne_zero (ε : ℝ) : rotVec v h ε ≠ 0 := by
  intro h0
  have := rotVec_dot_self hv hh hhv ε
  rw [h0, dotProduct_zero] at this
  exact zero_ne_one this

/-- **The rotated frame is an orthonormal frame of `γ(ε)^⊥`.** -/
theorem isFrame_rotFrame {U : Matrix ι (Fin m) ℂ} (hU : IsFrame U v) (ε : ℝ) :
    IsFrame (rotFrame U v h ε) (rotVec v h ε) := by
  set a := Uᴴ *ᵥ h
  set w := rotDir v h ε
  have hUw : Uᴴ *ᵥ w = ((Real.cos ε : ℂ) - 1) • a := by
    simp only [w, rotDir, Matrix.mulVec_sub, Matrix.mulVec_smul, hU.2, smul_zero, sub_zero, a]
  have hUγ : Uᴴ *ᵥ rotVec v h ε = (Real.sin ε : ℂ) • a := by
    simp only [rotVec, Matrix.mulVec_add, Matrix.mulVec_smul, hU.2, smul_zero, zero_add, a]
  have hwU : star w ᵥ* U = ((Real.cos ε : ℂ) - 1) • star a := by
    have h1 := Matrix.star_mulVec Uᴴ w
    rw [conjTranspose_conjTranspose, hUw, star_smul, star_sub, star_ofReal, star_one] at h1
    exact h1.symm
  have hF : rotFrame U v h ε = U + vecMulVec w (star a) := rfl
  have hH : (rotFrame U v h ε)ᴴ = Uᴴ + vecMulVec a (star w) := by
    rw [hF, conjTranspose_add, conjTranspose_vecMulVec, star_star]
  constructor
  · rw [hH, hF, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hU.1, mul_vecMulVec, vecMulVec_mul,
      vecMulVec_mul_vecMulVec, hUw, hwU, rotDir_dot_self hv hh hhv, smul_vecMulVec,
      vecMulVec_smul, vecMulVec_smul]
    have hc := cos_sq_add_sin_sq_complex hv hh hhv ε
    have : ((Real.cos ε : ℂ) - 1) + (((Real.cos ε : ℂ) - 1) +
        (((Real.cos ε : ℂ) - 1) ^ 2 + (Real.sin ε : ℂ) ^ 2)) = 0 := by
      linear_combination hc
    rw [add_assoc, ← add_smul, ← add_smul, this, zero_smul, add_zero]
  · rw [hH, add_mulVec, hUγ, vecMulVec_mulVec, rotDir_dot_rotVec hv hh hhv]
    ext x
    simp

end Orthonormal

/-!
## The derivative of the compression
-/

/-- Entrywise derivative of `ε ↦ F(ε)*KF(ε)`. -/
theorem hasDerivAt_compress_apply (K : Matrix ι ι ℂ) (F : ℝ → Matrix ι (Fin m) ℂ)
    (F' : Matrix ι (Fin m) ℂ) (ε₀ : ℝ) (hF : ∀ x a, HasDerivAt (fun ε => F ε x a) (F' x a) ε₀)
    (a b : Fin m) :
    HasDerivAt (fun ε => ((F ε)ᴴ * K * F ε) a b)
      ((F'ᴴ * K * F ε₀ + (F ε₀)ᴴ * K * F') a b) ε₀ := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.add_apply]
  have := HasDerivAt.fun_sum (u := Finset.univ) fun y _ =>
    (HasDerivAt.fun_sum (u := Finset.univ) fun x _ =>
      ((hF x a).star.mul_const (K x y))).mul (hF y b)
  convert this using 1
  rw [← Finset.sum_add_distrib]

theorem hasDerivAt_rotFrame_apply (U : Matrix ι (Fin m) ℂ) (v h : ι → ℂ) (x : ι) (a : Fin m) :
    HasDerivAt (fun ε => rotFrame U v h ε x a) (vecMulVec (-v) (star (Uᴴ *ᵥ h)) x a) 0 := by
  have hc := (Real.hasDerivAt_cos 0).ofReal_comp
  have hs := (Real.hasDerivAt_sin 0).ofReal_comp
  have := (((hc.sub_const 1).mul_const (h x)).sub (hs.mul_const (v x))).mul_const
    (star (Uᴴ *ᵥ h) a) |>.const_add (U x a)
  convert this using 1
  · funext ε
    simp [rotFrame, rotDir, vecMulVec_apply]
  · simp [vecMulVec_apply]

/-- **The derivative of the rotated compression**: for Hermitian `K₀`,
`∂K = DK(0)[1] = -(a c* + c a*)`, `a = U*h`, `c = U*K₀v`. -/
theorem paramDeriv_rotCompress (U : Matrix ι (Fin m) ℂ) (v h : ι → ℂ) {K : Matrix ι ι ℂ}
    (hK : K.IsHermitian) :
    paramDeriv (rotCompress U v h K) 0 1 =
      -(rankOne (Uᴴ *ᵥ h) (Uᴴ *ᵥ (K *ᵥ v)) + rankOne (Uᴴ *ᵥ (K *ᵥ v)) (Uᴴ *ᵥ h)) := by
  ext a b
  have hd := hasDerivAt_compress_apply K (rotFrame U v h) _ 0
    (hasDerivAt_rotFrame_apply U v h) a b
  simp only [paramDeriv, Matrix.of_apply, rotCompress]
  rw [hd.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, rotFrame_zero]
  have h1 : (vecMulVec (-v) (star (Uᴴ *ᵥ h)))ᴴ * K * U =
      -rankOne (Uᴴ *ᵥ h) (Uᴴ *ᵥ (K *ᵥ v)) := by
    rw [conjTranspose_vecMulVec, star_star, vecMulVec_mul, vecMulVec_mul]
    ext i j
    simp only [rankOne, vecMulVec_apply, Matrix.neg_apply, star_neg, neg_vecMul, Pi.neg_apply,
      mul_neg]
    congr 2
    rw [← Pi.star_apply, Matrix.star_mulVec, Matrix.star_mulVec, conjTranspose_conjTranspose,
      hK.eq]
  have h2 : Uᴴ * K * vecMulVec (-v) (star (Uᴴ *ᵥ h)) =
      -rankOne (Uᴴ *ᵥ (K *ᵥ v)) (Uᴴ *ᵥ h) := by
    rw [mul_vecMulVec]
    ext i j
    simp only [rankOne, vecMulVec_apply, Matrix.neg_apply, Matrix.mulVec_neg, Pi.neg_apply,
      neg_mul, Matrix.mulVec_mulVec, Pi.star_apply]
  rw [h1, h2]
  simp only [Matrix.add_apply, Matrix.neg_apply]
  ring

end BlockBand.DeterminantScore.ExactScore
