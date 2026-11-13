module
public import BlockBand.Coarea.ProjectiveAffine

/-!
# The phase-fixed Householder frame and its derivative

The phase-fixed Householder matrix `-1 + (1 + Re vᵢ)⁻¹ w w*` built from the coordinate vector
`eᵢ` and a unit vector `v`, its unitarity and self-adjointness, and its algebraic real
differential. Composed with the unit representative of the projective affine chart it gives a
smooth unitary frame on the whole chart, with an explicit derivative.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Coarea
open Matrix
open scoped Matrix.Norms.Elementwise

def phaseFixedCoordinateVector {ι : Type*} [DecidableEq ι]
    (i : ι) : ι → ℂ := Pi.single i 1

def phaseFixedHouseholderShift {ι : Type*} [DecidableEq ι]
    (i : ι) (v : ι → ℂ) : ι → ℂ :=
  v + phaseFixedCoordinateVector i

def phaseFixedHouseholderFrame {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : ι → ℂ) : Matrix ι ι ℂ :=
  -(1 : Matrix ι ι ℂ) +
    (((1 + (v i).re)⁻¹ : ℝ) : ℂ) •
      Matrix.vecMulVec (phaseFixedHouseholderShift i v)
        (star (phaseFixedHouseholderShift i v))

theorem phaseFixedHouseholderFrame_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i a b : ι) (v : ι → ℂ) :
    phaseFixedHouseholderFrame i v a b =
      -(if a = b then 1 else 0) +
        (((1 + (v i).re)⁻¹ : ℝ) : ℂ) *
          phaseFixedHouseholderShift i v a *
          star (phaseFixedHouseholderShift i v b) := by
  simp [phaseFixedHouseholderFrame, Matrix.one_apply,
    Matrix.vecMulVec_apply, mul_assoc]

theorem phaseFixedHouseholderFrame_mulVec_coordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : ι → ℂ)
    (hreal : v i = ((v i).re : ℂ)) (hden : 1 + (v i).re ≠ 0) :
    (phaseFixedHouseholderFrame i v).mulVec
      (phaseFixedCoordinateVector i) = v := by
  let a : ℝ := (v i).re
  have hva : v i = (a : ℂ) := hreal
  have ha : 1 + a ≠ 0 := hden
  rw [phaseFixedCoordinateVector, Matrix.mulVec_single_one]
  funext j
  change phaseFixedHouseholderFrame i v j i = v j
  rw [phaseFixedHouseholderFrame_apply]
  have hshift_i :
      phaseFixedHouseholderShift i v i =
        (((1 + a : ℝ)) : ℂ) := by
    rw [phaseFixedHouseholderShift]
    change v i + phaseFixedCoordinateVector i i =
      (((1 + a : ℝ)) : ℂ)
    rw [hva]
    simp only [phaseFixedCoordinateVector, Pi.single_eq_same]
    push_cast
    ring
  by_cases hji : j = i
  · subst j
    rw [show (if i = i then (1 : ℂ) else 0) = 1 by simp, hshift_i, hva]
    change -(1 : ℂ) + (↑((1 + a)⁻¹) : ℂ) *
      (↑(1 + a) : ℂ) * star (↑(1 + a) : ℂ) = (a : ℂ)
    rw [show star (↑(1 + a) : ℂ) = (↑(1 + a) : ℂ) by simp]
    rw [show (↑((1 + a)⁻¹) : ℂ) * (↑(1 + a) : ℂ) = 1 by
      norm_cast
      exact inv_mul_cancel₀ ha]
    push_cast
    ring
  · have hshift_j : phaseFixedHouseholderShift i v j = v j := by
      rw [phaseFixedHouseholderShift]
      change v j + phaseFixedCoordinateVector i j = v j
      rw [phaseFixedCoordinateVector, Pi.single_eq_of_ne hji]
      exact add_zero _
    rw [show (if j = i then (1 : ℂ) else 0) = 0 by
      simp only [hji, ↓reduceIte], hshift_j, hshift_i]
    change -(0 : ℂ) + (↑((1 + a)⁻¹) : ℂ) *
      v j * star (↑(1 + a) : ℂ) = v j
    rw [show star (↑(1 + a) : ℂ) = (↑(1 + a) : ℂ) by simp]
    calc
      -(0 : ℂ) + (↑((1 + a)⁻¹) : ℂ) *
          v j * (↑(1 + a) : ℂ) =
          ((↑((1 + a)⁻¹) : ℂ) * (↑(1 + a) : ℂ)) * v j := by ring
      _ = v j := by
        rw [show (↑((1 + a)⁻¹) : ℂ) * (↑(1 + a) : ℂ) = 1 by
          norm_cast
          exact inv_mul_cancel₀ ha]
        exact one_mul _

def euclideanEvaluationCLM
    {ι : Type*} [Fintype ι] (i : ι) :
    EuclideanSpace ℂ ι →L[ℝ] ℂ :=
  ({ toFun := fun v => v i
     map_add' := by intro x y; rfl
     map_smul' := by intro c x; simp } :
    EuclideanSpace ℂ ι →ₗ[ℝ] ℂ).toContinuousLinearMap

def phaseFixedHouseholderAlgebraicDifferential
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι →ₗ[ℝ] Matrix ι ι ℂ where
  toFun u :=
    -((((1 + (v i).re)⁻¹ ^ 2 * (u i).re : ℝ) : ℂ) •
      Matrix.vecMulVec (phaseFixedHouseholderShift i v)
        (star (phaseFixedHouseholderShift i v))) +
    (((1 + (v i).re)⁻¹ : ℝ) : ℂ) •
      (Matrix.vecMulVec u (star (phaseFixedHouseholderShift i v)) +
       Matrix.vecMulVec (phaseFixedHouseholderShift i v) (star u))
  map_add' u z := by
    ext a b
    simp [Matrix.vecMulVec_apply]
    ring
  map_smul' c u := by
    ext a b
    simp [Matrix.vecMulVec_apply, smul_eq_mul]
    ring

def matrixEntryEvaluationCLM
    {ι : Type*} [Fintype ι] (a b : ι) :
    Matrix ι ι ℂ →L[ℝ] ℂ :=
  ({ toFun := fun A => A a b
     map_add' := by intro A B; rfl
     map_smul' := by intro c A; rfl } :
    Matrix ι ι ℂ →ₗ[ℝ] ℂ).toContinuousLinearMap

theorem hasFDerivAt_phaseFixedHouseholderFrame_algebraic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι)
    (hden : 1 + (v i).re ≠ 0) :
    HasFDerivAt (fun w : EuclideanSpace ℂ ι =>
      phaseFixedHouseholderFrame i w)
      (phaseFixedHouseholderAlgebraicDifferential i v).toContinuousLinearMap v := by
  have hentry (a b : ι) : HasFDerivAt
      (fun w : EuclideanSpace ℂ ι => phaseFixedHouseholderFrame i w a b)
      ((matrixEntryEvaluationCLM a b).comp
        (phaseFixedHouseholderAlgebraicDifferential i v).toContinuousLinearMap) v := by
    rw [show (fun w : EuclideanSpace ℂ ι =>
      phaseFixedHouseholderFrame i w a b) =
      fun w : EuclideanSpace ℂ ι => -(if a = b then 1 else 0) +
        (((1 + (w i).re)⁻¹ : ℝ) : ℂ) *
          (w a + phaseFixedCoordinateVector i a) *
          star (w b + phaseFixedCoordinateVector i b) by
    funext w
    rw [phaseFixedHouseholderFrame_apply]
    rfl]
    have hea (k : ι) : HasFDerivAt
        (fun w : EuclideanSpace ℂ ι => w k) (euclideanEvaluationCLM k) v :=
      (euclideanEvaluationCLM k).hasFDerivAt
    have hre : HasFDerivAt
        (fun w : EuclideanSpace ℂ ι => (w i).re)
        (Complex.reCLM.comp (euclideanEvaluationCLM i)) v :=
      Complex.reCLM.hasFDerivAt.comp v (hea i)
    have hdenom : HasFDerivAt
        (fun w : EuclideanSpace ℂ ι => 1 + (w i).re)
        (Complex.reCLM.comp (euclideanEvaluationCLM i)) v := by
      convert (hasFDerivAt_const (1 : ℝ) v).add hre using 1; simp
    have hinv := (hasFDerivAt_inv hden).comp v hdenom
    have hcoeff := Complex.ofRealCLM.hasFDerivAt.comp v hinv
    have hleft : HasFDerivAt
        (fun w : EuclideanSpace ℂ ι =>
          w a + phaseFixedCoordinateVector i a)
        (euclideanEvaluationCLM a) v := by
      convert (hea a).add
        (hasFDerivAt_const (phaseFixedCoordinateVector i a) v) using 1; simp
    have hright : HasFDerivAt
        (fun w : EuclideanSpace ℂ ι =>
          star (w b + phaseFixedCoordinateVector i b))
        (((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).comp
        (euclideanEvaluationCLM b)) v := by
      convert ((hea b).add
        (hasFDerivAt_const (phaseFixedCoordinateVector i b) v)).star using 1; simp
    apply ((hasFDerivAt_const
        (-(if a = b then (1 : ℂ) else 0)) v).add
        ((hcoeff.mul hleft).mul hright)).congr_fderiv
    apply ContinuousLinearMap.ext
    intro u
    simp [matrixEntryEvaluationCLM, euclideanEvaluationCLM,
      phaseFixedHouseholderAlgebraicDifferential, Matrix.vecMulVec_apply,
      phaseFixedHouseholderShift, smul_eq_mul]
    ring
  have hpi := hasFDerivAt_pi.mpr (fun a =>
    hasFDerivAt_pi.mpr (fun b => hentry a b))
  have heq :
      (phaseFixedHouseholderAlgebraicDifferential i v).toContinuousLinearMap =
        ContinuousLinearMap.pi (fun a => ContinuousLinearMap.pi (fun b =>
          (matrixEntryEvaluationCLM a b).comp
            (phaseFixedHouseholderAlgebraicDifferential i v).toContinuousLinearMap)) := by
    apply ContinuousLinearMap.ext
    intro u
    ext a b
    rfl
  rw [heq]
  exact hpi

theorem fderiv_phaseFixedHouseholderFrame_eq_algebraic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι)
    (hden : 1 + (v i).re ≠ 0) :
    fderiv ℝ (fun w : EuclideanSpace ℂ ι =>
      phaseFixedHouseholderFrame i w) v =
      (phaseFixedHouseholderAlgebraicDifferential i v).toContinuousLinearMap :=
  (hasFDerivAt_phaseFixedHouseholderFrame_algebraic i v hden).fderiv

theorem phaseFixedHouseholderShift_star_dotProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι)
    (hv : ‖v‖ = 1) (hreal : v i = ((v i).re : ℂ)) :
    star (phaseFixedHouseholderShift i v) ⬝ᵥ
        phaseFixedHouseholderShift i v =
      (((2 * (1 + (v i).re) : ℝ)) : ℂ) := by
  let e : EuclideanSpace ℂ ι := EuclideanSpace.single i 1
  have hw : WithLp.toLp 2 (phaseFixedHouseholderShift i v) = v + e := by
    ext j
    simp [phaseFixedHouseholderShift, phaseFixedCoordinateVector, e,
      Pi.single_apply]
  have hvv : inner ℂ v v = 1 := by
    rw [← inner_self_ofReal_re, inner_self_eq_norm_sq, hv]
    norm_num
  have hinner : inner ℂ (v + e) (v + e) =
      (((2 * (1 + (v i).re) : ℝ)) : ℂ) := by
    rw [inner_add_left, inner_add_right, inner_add_right]
    simp only [hvv, e, EuclideanSpace.inner_single_left,
      EuclideanSpace.inner_single_right, map_one, one_mul]
    rw [hreal]
    simp
    ring
  rw [← dotProduct_comm]
  rw [← EuclideanSpace.inner_eq_star_dotProduct]
  rw [hw, hinner]

theorem phaseFixedHouseholderFrame_unitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι)
    (hv : ‖v‖ = 1) (hreal : v i = ((v i).re : ℂ))
    (hpos : 0 < (v i).re) :
    (phaseFixedHouseholderFrame i v)ᴴ *
      phaseFixedHouseholderFrame i v = 1 := by
  let w : ι → ℂ := phaseFixedHouseholderShift i v
  let d : ℝ := 1 + (v i).re
  let c : ℂ := ((d⁻¹ : ℝ) : ℂ)
  let P : Matrix ι ι ℂ := c • Matrix.vecMulVec w (star w)
  have hd : d ≠ 0 := by
    dsimp [d]
    linarith
  have hc : c * (((2 * d : ℝ)) : ℂ) = 2 := by
    dsimp [c]
    push_cast
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
    field_simp [hdC]
  have hdot : star w ⬝ᵥ w = (((2 * d : ℝ)) : ℂ) := by
    simpa [w, d] using
      phaseFixedHouseholderShift_star_dotProduct i v hv hreal
  have hPstar : Pᴴ = P := by
    dsimp [P]
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec]
    simp [c, w]
  have hPsq : P * P = (2 : ℂ) • P := by
    dsimp [P]
    rw [smul_mul_smul, Matrix.vecMulVec_mul_vecMulVec, hdot]
    ext a b
    change c * c * (w a * (↑(2 * d) * star (w b))) =
      2 * (c * (w a * star (w b)))
    have hc' : c * c * (((2 * d : ℝ)) : ℂ) = 2 * c := by
      rw [mul_assoc, hc]
      ring
    calc
      c * c * (w a * (↑(2 * d) * star (w b))) =
          (c * c * ↑(2 * d)) * (w a * star (w b)) := by ring
      _ = 2 * c * (w a * star (w b)) := by rw [hc']
      _ = 2 * (c * (w a * star (w b))) := by ring
  have hframe : phaseFixedHouseholderFrame i v = -1 + P := by
    rfl
  rw [hframe, Matrix.conjTranspose_add, Matrix.conjTranspose_neg,
    Matrix.conjTranspose_one, hPstar]
  calc
    (-1 + P) * (-1 + P) = 1 - P - P + P * P := by noncomm_ring
    _ = 1 - P - P + (2 : ℂ) • P := by rw [hPsq]
    _ = 1 := by
      rw [two_smul ℂ P]
      abel

/-- The rank-one Householder formula is self-adjoint, without unit-norm hypotheses. -/
theorem phaseFixedHouseholderFrame_conjTranspose
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : ι → ℂ) :
    (phaseFixedHouseholderFrame i v)ᴴ = phaseFixedHouseholderFrame i v := by
  rw [phaseFixedHouseholderFrame, Matrix.conjTranspose_add,
    Matrix.conjTranspose_neg, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec]
  simp

/-- The smooth unitary frame on the whole affine projective chart. -/
def nonlinearProjectiveFrame {n : Type*} [Fintype n] [DecidableEq n]
    (z : n → ℂ) : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ :=
  phaseFixedHouseholderFrame (Sum.inl Unit.unit) (nonlinearProjectiveUnit z)

/-- Its real differential, composed with the normalization map. -/
def nonlinearProjectiveFrameDerivative {n : Type*} [Fintype n] [DecidableEq n]
    (z : n → ℂ) : (n → ℂ) →L[ℝ] Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ :=
  (phaseFixedHouseholderAlgebraicDifferential (Sum.inl Unit.unit)
    (nonlinearProjectiveUnit z)).toContinuousLinearMap.comp
      (nonlinearProjectiveUnitDerivative z)

theorem hasFDerivAt_nonlinearProjectiveFrame
    {n : Type*} [Fintype n] [DecidableEq n] (z : n → ℂ) :
    HasFDerivAt nonlinearProjectiveFrame (nonlinearProjectiveFrameDerivative z) z := by
  have hden : 1 + (nonlinearProjectiveUnit z (Sum.inl Unit.unit)).re ≠ 0 :=
    ne_of_gt (by linarith [nonlinearProjectiveUnit_selected_re_pos z])
  have hframe : HasFDerivAt
      (fun v : EuclideanSpace ℂ (Unit ⊕ n) =>
        phaseFixedHouseholderFrame (Sum.inl Unit.unit) v)
      (phaseFixedHouseholderAlgebraicDifferential (Sum.inl Unit.unit)
        (nonlinearProjectiveUnit z)).toContinuousLinearMap
      (nonlinearProjectiveUnit z) := by
    convert hasFDerivAt_phaseFixedHouseholderFrame_algebraic
      (Sum.inl Unit.unit) (nonlinearProjectiveUnit z) hden using 1
  have hunit : HasFDerivAt (fun w : n → ℂ => nonlinearProjectiveUnit w)
      (nonlinearProjectiveUnitDerivative z) z := by
    convert hasFDerivAt_nonlinearProjectiveUnit z using 1
  have hcomp := HasFDerivAt.comp (𝕜 := ℝ)
    (f := nonlinearProjectiveUnit (n := n))
    (f' := nonlinearProjectiveUnitDerivative z)
    (g := fun v : EuclideanSpace ℂ (Unit ⊕ n) =>
      phaseFixedHouseholderFrame (Sum.inl Unit.unit) v)
    (g' := (phaseFixedHouseholderAlgebraicDifferential (Sum.inl Unit.unit)
      (nonlinearProjectiveUnit z)).toContinuousLinearMap) z hframe hunit
  convert hcomp using 1 <;> rfl

theorem fderiv_nonlinearProjectiveFrame
    {n : Type*} [Fintype n] [DecidableEq n] (z : n → ℂ) :
    fderiv ℝ nonlinearProjectiveFrame z = nonlinearProjectiveFrameDerivative z :=
  (hasFDerivAt_nonlinearProjectiveFrame z).fderiv

theorem nonlinearProjectiveFrame_conjTranspose
    {n : Type*} [Fintype n] [DecidableEq n] (z : n → ℂ) :
    (nonlinearProjectiveFrame z)ᴴ = nonlinearProjectiveFrame z :=
  phaseFixedHouseholderFrame_conjTranspose _ _

theorem nonlinearProjectiveFrame_unitary
    {n : Type*} [Fintype n] [DecidableEq n] (z : n → ℂ) :
    (nonlinearProjectiveFrame z)ᴴ * nonlinearProjectiveFrame z = 1 := by
  apply phaseFixedHouseholderFrame_unitary _ _ (norm_nonlinearProjectiveUnit z)
  · rw [nonlinearProjectiveUnit_selected]
    simp
  · exact nonlinearProjectiveUnit_selected_re_pos z

theorem nonlinearProjectiveFrame_mulVec_coordinate
    {n : Type*} [Fintype n] [DecidableEq n] (z : n → ℂ) :
    (nonlinearProjectiveFrame z).mulVec (phaseFixedCoordinateVector (Sum.inl Unit.unit)) =
      nonlinearProjectiveUnit z := by
  apply phaseFixedHouseholderFrame_mulVec_coordinate
  · rw [nonlinearProjectiveUnit_selected]
    simp
  · exact ne_of_gt (by linarith [nonlinearProjectiveUnit_selected_re_pos z])

end BlockBand.Coarea
