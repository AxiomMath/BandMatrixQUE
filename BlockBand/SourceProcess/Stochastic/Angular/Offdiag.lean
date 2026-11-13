module

public import BlockBand.SourceProcess.Stochastic.Angular.Rotation

/-!
# Complex angular contract: second derivatives of `arrayFn` along adapted directions

Towards the proposition `ArrayLaplacianDiag`. Fix `y` of simple spectrum, `U = eigMat N y`,
`D = diag(λ)`, `Z = arrZ V y`, `F = arrayFn V f₀`.

* **Projection directions** (`fderiv_arrayFn_proj`, `fderiv2_arrayFn_proj`):
  `DF[P_m] = 0` and `D²F[P_m, P_m] = 0`. The second follows by differentiating the identity
  `DF(y')[P_m(y')] = 0` along `P_m`, since `dP_m[P_m] = 0`.
* **Rotation directions** (`offdiag_core`): along `γ(α) = hermVec(U R(α) D R(α)* U*)` the
  eigenvalues are fixed (`dysonEigenvalue_conj`), the eigenprojections rotate, and by phase
  invariance `F(γ(α)) = f₀(arrMul R(α) Z)`. Two applications of the second-order chain rule give
  `D²F[γ', γ'] + DF[γ''] = D²f₀[JZ, JZ] + Df₀[J²Z]` with `γ'(0) = hermVec(U[J, D]U*)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open Matrix Filter Topology
open scoped Matrix ComplexConjugate Matrix.Norms.Operator
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionAngular
open BlockBand.SourceProcess.Stochastic.Dyson

variable {N r : ℕ}

/-- `hermVec` as a continuous real-linear map. -/
def hermVecCLM (N : ℕ) : Matrix (Fin N) (Fin N) ℂ →L[ℝ] (Fin (N * N) → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := hermVec N
      map_add' := fun A B => by funext k; simp [hermVec, hermCoord, Matrix.mul_add]
      map_smul' := fun c A => by funext k; simp [hermVec, hermCoord] }

theorem hermVecCLM_apply (M : Matrix (Fin N) (Fin N) ℂ) : hermVecCLM N M = hermVec N M := rfl

variable {V : Matrix (Fin N) (Fin r) ℂ} {f₀ : AngularArray N r → ℝ}

/-! ### Projection directions -/

/-- `DF[P_m] = 0` (the computation inside `arrayFn_cross`). -/
theorem fderiv_arrayFn_proj (hf : ContDiff ℝ 2 f₀) (hp : IsPhaseInvariant f₀)
    {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (m : Fin N) :
    fderiv ℝ (arrayFn V f₀) y (hermVec N (proj N m y)) = 0 := by
  obtain ⟨κ, hκ⟩ := eventually_frame hy
  have hev : arrayFn V f₀ =ᶠ[𝓝 y] f₀ ∘ frameArr V κ := by
    filter_upwards [hκ] with y' hy'
    rw [arrayFn_of_mem hy'.1, phaseInv_frame hp V hy'.1 hy'.2]; rfl
  have hfr : DifferentiableAt ℝ (frameArr V κ) y :=
    (contDiffAt_frameArr (n := 1) V hy hκ.self_of_nhds.2).differentiableAt (by norm_num)
  rw [hev.fderiv_eq, fderiv_comp y ((hf.differentiable (by norm_num)) _) hfr,
    ContinuousLinearMap.comp_apply, fderiv_frameArr_along_proj V hy hκ.self_of_nhds.2 m, map_zero]

/-- **`D²F[P_m, P_m] = 0`.** -/
theorem fderiv2_arrayFn_proj (hf : ContDiff ℝ 2 f₀) (hp : IsPhaseInvariant f₀)
    {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (m : Fin N) :
    fderiv ℝ (fderiv ℝ (arrayFn V f₀)) y (hermVec N (proj N m y)) (hermVec N (proj N m y)) =
      0 := by
  have hDF : HasFDerivAt (fderiv ℝ (arrayFn V f₀)) (fderiv ℝ (fderiv ℝ (arrayFn V f₀)) y) y :=
    (((contDiffAt_arrayFn hf hp hy).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hg : HasFDerivAt (hermVecCLM N ∘ proj N m)
      ((hermVecCLM N).comp (fderiv ℝ (proj N m) y)) y :=
    (hermVecCLM N).hasFDerivAt.comp y (hasFDerivAt_proj hy m)
  have hφ := hDF.clm_apply hg
  have hzero : (fun y' => fderiv ℝ (arrayFn V f₀) y' ((hermVecCLM N ∘ proj N m) y')) =ᶠ[𝓝 y]
      fun _ => 0 := by
    filter_upwards [eventually_simpleSet hy] with y' hy'
    exact fderiv_arrayFn_proj hf hp hy' m
  have h0 := (hφ.congr_of_eventuallyEq hzero.symm).unique (hasFDerivAt_const 0 y)
  have h1 := congrArg (fun L => L (hermVec N (proj N m y))) h0
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, _root_.zero_apply, hermVecCLM_apply,
    Function.comp_apply,
    fderiv_proj_along_proj hy m m] at h1
  rw [show hermVec N (0 : Matrix (Fin N) (Fin N) ℂ) = 0 from map_zero (hermVecCLM N),
    map_zero, zero_add] at h1
  exact h1

/-! ### Rotation directions -/

theorem mul_cancel_left_of {A B : Matrix (Fin N) (Fin N) ℂ} (h : A * B = 1)
    (X : Matrix (Fin N) (Fin N) ℂ) : A * (B * X) = X := by
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

section Rot
variable {P J : Matrix (Fin N) (Fin N) ℂ} (hPs : star P = P) (hJs : star J = -J)
  (hPP : P * P = P) (hJJ : J * J = -P) (hPJ : P * J = J) (hJP : J * P = J)
include hPs hJs hPP hJJ hPJ hJP

/-- **Along the rotation curve, `F` is `f₀` of the rotated array.** -/
theorem arrayFn_rot (hp : IsPhaseInvariant f₀) {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N)
    (α : ℝ) :
    arrayFn V f₀ (conjVec (eigMat N y) (rot P J α * eigDiag N y * star (rot P J α))) =
      f₀ (arrMul (rot P J α) (arrZ V y)) := by
  set U := eigMat N y
  set R := rot P J α
  set D := eigDiag N y
  have hU1 : star U * U = 1 := eigMat_star_mul y
  have hU2 : U * star U = 1 := eigMat_mul_star y
  have hR1 : star R * R = 1 := rot_star_mul hPs hJs hPP hJJ hPJ hJP α
  have hR2 : R * star R = 1 := rot_mul_star hPs hJs hPP hJJ hPJ hJP α
  have hHe : vecHerm N y = U * D * star U := vecHerm_eq_eig y
  have hPe : ∀ k, proj N k y = U * single k k 1 * star U := proj_eq_eig hy
  set W := U * R * star U
  have hsW : star W = U * (star R * star U) := by
    simp only [W, star_mul, star_star, Matrix.mul_assoc]
  have hW1 : star W * W = 1 := by
    rw [hsW]; simp only [W, Matrix.mul_assoc, mul_cancel_left_of hU1, mul_cancel_left_of hR1, hU2]
  have hW2 : W * star W = 1 := by
    rw [hsW]; simp only [W, Matrix.mul_assoc, mul_cancel_left_of hU1, mul_cancel_left_of hR2, hU2]
  have hH : W * vecHerm N y * star W = U * (R * D * star R) * star U := by
    rw [hsW, hHe]
    simp only [W, Matrix.mul_assoc, mul_cancel_left_of hU1]
  have hD : D.IsHermitian := by
    rw [IsHermitian, ← star_eq_conjTranspose]; exact eigDiag_conjTranspose y
  have hM : (U * (R * D * star R) * star U).IsHermitian :=
    isHermitian_conj U (isHermitian_conj R hD)
  have hvec : vecHerm N (conjVec U (R * D * star R)) = W * vecHerm N y * star W := by
    rw [conjVec_apply, vecHerm_hermVec hM, hH]
  have hmem : conjVec U (R * D * star R) ∈ simpleSet N := by
    change HasSimpleSpectrum N _
    rw [hvec]; exact hasSimpleSpectrum_conj hW1 hy
  have hproj : ∀ k, proj N k (conjVec U (R * D * star R)) =
      vecMulVec (fun b => (U * R) b k) (star fun b => (U * R) b k) := by
    intro k
    rw [← mul_single_mul_star, proj, hvec, dysonProjection_conj hW1 hW2, ← proj, hPe]
    rw [hsW]
    simp only [W, star_mul, Matrix.mul_assoc, mul_cancel_left_of hU1]
  rw [arrayFn_of_mem hmem, phaseInv_of_proj hp V hmem _ hproj, angularArray_mul]
  rfl

/-- **The rotation identity**: `D²F[γ', γ'] + DF[γ''] = D²f₀[JZ, JZ] + Df₀[J²Z]`. -/
theorem offdiag_core (hf : ContDiff ℝ 2 f₀) (hp : IsPhaseInvariant f₀) {y : Fin (N * N) → ℝ}
    (hy : y ∈ simpleSet N) :
    fderiv ℝ (fderiv ℝ (arrayFn V f₀)) y
        (conjVec (eigMat N y) (J * eigDiag N y - eigDiag N y * J))
        (conjVec (eigMat N y) (J * eigDiag N y - eigDiag N y * J)) +
      fderiv ℝ (arrayFn V f₀) y
        (-conjVec (eigMat N y) (P * eigDiag N y + eigDiag N y * P) -
          (2 : ℝ) • conjVec (eigMat N y) (J * eigDiag N y * J)) =
    fderiv ℝ (fderiv ℝ f₀) (arrZ V y) (arrMul J (arrZ V y)) (arrMul J (arrZ V y)) +
      fderiv ℝ f₀ (arrZ V y) (arrMul J (arrMul J (arrZ V y))) := by
  set L := conjVec (eigMat N y)
  set D := eigDiag N y
  set Z := arrZ V y
  have hγ : ∀ α, trigCurve (L D) (L (P * D + D * P)) (L (J * D - D * J)) (L (P * D * P))
      (L (J * D * P - P * D * J)) (L (J * D * J)) α = L (rot P J α * D * star (rot P J α)) := by
    intro α
    rw [rot_mul_mul_star hPs hJs]
    simp only [trigCurve, map_add, map_sub, map_smul]
  have hcomp : arrayFn V f₀ ∘ trigCurve (L D) (L (P * D + D * P)) (L (J * D - D * J))
      (L (P * D * P)) (L (J * D * P - P * D * J)) (L (J * D * J)) =
      f₀ ∘ trigCurve Z (-arrMul J (arrMul J Z)) (arrMul J Z) 0 0 0 := by
    funext α
    simp only [Function.comp_apply]
    rw [hγ, arrayFn_rot hPs hJs hPP hJJ hPJ hJP hp hy, arrMul_rot hJJ]
  have h0 : L D = y := by
    rw [conjVec_apply, ← vecHerm_eq_eig, hermVec_vecHerm]
  have hg : ContDiffAt ℝ 2 (arrayFn V f₀) (trigCurve (L D) (L (P * D + D * P))
      (L (J * D - D * J)) (L (P * D * P)) (L (J * D * P - P * D * J)) (L (J * D * J)) 0) := by
    rw [trigCurve_zero, h0]; exact contDiffAt_arrayFn hf hp hy
  have hL := hasDerivAt_deriv_comp hg (hasDerivAt_trigCurve _ _ _ _ _ _) (hasDerivAt_trigCurveD _ _ _ _ _)
  have hR := hasDerivAt_deriv_comp (hf.contDiffAt (x := trigCurve Z (-arrMul J (arrMul J Z))
    (arrMul J Z) 0 0 0 0)) (hasDerivAt_trigCurve _ _ _ _ _ _) (hasDerivAt_trigCurveD _ _ _ _ _)
  rw [hcomp] at hL
  have key := hL.unique hR
  simp only [trigCurve_zero, trigCurveD_zero, h0, smul_zero, sub_zero, neg_neg] at key
  exact key

end Rot

end BlockBand.SourceProcess.Stochastic.ComplexAngular
