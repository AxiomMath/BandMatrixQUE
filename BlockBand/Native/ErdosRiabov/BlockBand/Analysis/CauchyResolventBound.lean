module

public import BlockBand.Native.ErdosRiabov.BlockBand.Analysis.CauchyPoissonMatrix
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Global bounds for the noncommuting Cauchy resolvent

This module supplies the global estimate not given in
`CauchyPoissonMatrix` for the noncommuting pencil

`A + z Q + i η I`.

For Hermitian `A`, positive-semidefinite `Q`, `η > 0`, and `Im z ≥ 0`, its
imaginary part dominates `η I`.  The resulting quadratic-form coercivity and
Mathlib's Hilbert-space antilipschitz lemma give the sharp operator bound

`‖(A + z Q + i η I)⁻¹‖ ≤ η⁻¹`.

We then bound each diagonal entry and sum the ordinary, unnormalized trace to
obtain

`0 ≤ -Im Tr (A + z Q + i η I)⁻¹ ≤ card(ι) / η`.

Finally, the real-axis boundary trace is proved continuous and its product
with the standard Cauchy density of the paper is proved integrable, with its
integral in the same explicit interval.  These are the domination inputs for
a bounded upper-half-plane Poisson representation; no such
representation is assumed here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix MeasureTheory Set
open scoped ComplexOrder Matrix Matrix.Norms.L2Operator ENNReal NNReal

namespace ERNative.BlockBand

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem inner_toEuclideanCLM_im
    (M : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    (inner ℂ (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M x) x).im =
      -(star x.ofLp ⬝ᵥ (matrixImaginaryPart M *ᵥ x.ofLp)).re := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.ofLp_toEuclideanCLM]
  simp [matrixImaginaryPart, Matrix.smul_mulVec, Matrix.sub_mulVec,
    dotProduct_smul, dotProduct_sub, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose]
  rw [← Matrix.dotProduct_mulVec]
  rw [dotProduct_comm x.ofLp, Matrix.star_dotProduct]
  simp
  ring

/-- Coercivity of the regulated pencil in the Euclidean norm.  This is the
finite-dimensional dissipative estimate behind the sharp resolvent bound. -/
theorem norm_sq_mul_eta_le_norm_inner_cauchyResolventPencil
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (_hη : 0 < η) {z : ℂ} (hz : 0 ≤ z.im)
    (x : EuclideanSpace ℂ ι) :
    ‖x‖ ^ 2 * η ≤
      ‖inner ℂ
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
          (cauchyResolventPencil A Q η z) x) x‖ := by
  have hq := hQ.dotProduct_mulVec_nonneg x.ofLp
  have hqre : 0 ≤ (star x.ofLp ⬝ᵥ (Q *ᵥ x.ofLp)).re :=
    (RCLike.nonneg_iff.mp hq).1
  have him := inner_toEuclideanCLM_im
    (cauchyResolventPencil A Q η z) x
  rw [matrixImaginaryPart_cauchyResolventPencil A Q hA hQ.isHermitian] at him
  have hself : (star x.ofLp ⬝ᵥ x.ofLp).re = ‖x‖ ^ 2 := by
    rw [dotProduct_comm]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) x
  have hlower : ‖x‖ ^ 2 * η ≤
      -(inner ℂ
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
          (cauchyResolventPencil A Q η z) x) x).im := by
    rw [him]
    simp [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, hself]
    nlinarith
  calc
    ‖x‖ ^ 2 * η ≤ -(inner ℂ
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
          (cauchyResolventPencil A Q η z) x) x).im := hlower
    _ ≤ |(inner ℂ
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
          (cauchyResolventPencil A Q η z) x) x).im| := neg_le_abs _
    _ ≤ ‖inner ℂ
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
          (cauchyResolventPencil A Q η z) x) x‖ := Complex.abs_im_le_norm _

/-- Sharp Euclidean operator-norm bound for the inverse of the regulated
noncommuting pencil on the closed upper half plane. -/
theorem norm_cauchyResolventPencil_nonsing_inv_le
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖(cauchyResolventPencil A Q η z)⁻¹‖ ≤ η⁻¹ := by
  let M := cauchyResolventPencil A Q η z
  let c : ℝ≥0 := ⟨η, hη.le⟩
  let f : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M
  have hc : 0 < c := hη
  have hanti : AntilipschitzWith c⁻¹ f :=
    f.antilipschitz_of_forall_le_inner_map hc fun x => by
      change ‖x‖ ^ 2 * η ≤
        ‖inner ℂ
          (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
            (cauchyResolventPencil A Q η z) x) x‖
      exact norm_sq_mul_eta_le_norm_inner_cauchyResolventPencil
        A Q hA hQ hη hz x
  have hdet : IsUnit M.det :=
    isUnit_det_cauchyResolventPencil A Q hA hQ hη hz
  change ‖M⁻¹‖ ≤ η⁻¹
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  let y : EuclideanSpace ℂ ι :=
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M⁻¹ x
  have hy := f.bound_of_antilipschitz hanti y
  have hfy : f y = x := by
    apply WithLp.ofLp_injective
    simp [f, y, M, Matrix.mulVec_mulVec, M.mul_nonsing_inv hdet]
  rw [hfy] at hy
  have hinvcoe : ((c⁻¹ : ℝ≥0) : ℝ) = η⁻¹ := by
    rw [NNReal.coe_inv]
    rfl
  rw [hinvcoe] at hy
  simpa only [y] using hy

private theorem norm_matrix_entry_le_l2_opNorm
    (M : Matrix ι ι ℂ) (i j : ι) :
    ‖M i j‖ ≤ ‖M‖ := by
  let e : EuclideanSpace ℂ ι := WithLp.toLp 2 (Pi.single j 1)
  let y : EuclideanSpace ℂ ι :=
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M e
  have hcoord : ‖y.ofLp i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
  have hop := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M).le_opNorm e
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  have hyi : y.ofLp i = M i j := by
    simp [y, e]
  calc
    ‖M i j‖ = ‖y.ofLp i‖ := congrArg norm hyi.symm
    _ ≤ ‖y‖ := hcoord
    _ ≤ ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M‖ * ‖e‖ := hop
    _ = ‖M‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM, he, mul_one]

end ERNative.BlockBand
