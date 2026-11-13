module

public import BlockBand.Transmission.PassiveCovariance.Scalars
public import BlockBand.Transmission.Bridge.Passive

/-!
# Deterministic passive bounds

For a passive old input (`Y = -Im X ⪰ 0`) and `η = Im z_∂ > 0`, with the Euclidean operator
norm:

* `‖R‖ ≤ η⁻¹` for `R = (z - X)⁻¹` (`Im(z - X) = η + Y ⪰ η`);
* `‖S‖ ≤ 3`, `‖I - T‖ = ‖S*S‖ ≤ 9`, `‖f‖ ≤ 3/(2η)` (`S = I - 2iηR`, `f = R - c₀I`);
* `|u*Mv| ≤ ‖u‖‖M‖‖v‖` and `|A ⊗ B| ≤ ‖A‖‖B‖∏‖v_j‖` for the crossed tensor.

These are the deterministic half of the off-domain argument.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open scoped ComplexOrder Matrix.Norms.L2Operator

section Vectors

variable {n : Type*} [Fintype n]

theorem vecNorm_eq (v : n → ℂ) : vecNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ := by
  rw [EuclideanSpace.norm_eq]; rfl

theorem vecNorm_nonneg (v : n → ℂ) : 0 ≤ vecNorm v := Real.sqrt_nonneg _

theorem norm_star_dotProduct_le (u w : n → ℂ) : ‖star u ⬝ᵥ w‖ ≤ vecNorm u * vecNorm w := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 u : EuclideanSpace ℂ n)
    (WithLp.toLp 2 w)
  rwa [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, ← vecNorm_eq, ← vecNorm_eq] at h

theorem star_self_eq (x : n → ℂ) : star x ⬝ᵥ x = ((vecNorm x ^ 2 : ℝ) : ℂ) := by
  rw [vecNorm, Real.sq_sqrt (by positivity)]
  simp [dotProduct, Complex.mul_conj', mul_comm]

theorem quad_conjTranspose (K : Matrix n n ℂ) (x : n → ℂ) :
    star x ⬝ᵥ (Kᴴ *ᵥ x) = star (star x ⬝ᵥ (K *ᵥ x)) := by
  rw [star_dotProduct]; congr 1
  rw [star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec]

theorem quad_im (K : Matrix n n ℂ) (x : n → ℂ) :
    star x ⬝ᵥ (matrixImaginaryPart K *ᵥ x) = ((star x ⬝ᵥ (K *ᵥ x)).im : ℂ) := by
  rw [matrixImaginaryPart, smul_mulVec, sub_mulVec, dotProduct_smul, dotProduct_sub,
    quad_conjTranspose]
  apply Complex.ext <;> simp
  ring

variable [DecidableEq n]

theorem vecNorm_mulVec_le (A : Matrix n n ℂ) (v : n → ℂ) :
    vecNorm (A *ᵥ v) ≤ ‖A‖ * vecNorm v := by
  have := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 v)
  rw [vecNorm_eq, vecNorm_eq]; exact this

theorem opNorm_le_of_vec (A : Matrix n n ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : n → ℂ, vecNorm (A *ᵥ x) ≤ C * vecNorm x) : ‖A‖ ≤ C := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  have := h x.ofLp
  rw [vecNorm_eq, vecNorm_eq] at this
  exact this

theorem norm_one_matrix_le : ‖(1 : Matrix n n ℂ)‖ ≤ 1 :=
  opNorm_le_of_vec _ zero_le_one fun x => by rw [one_mulVec, one_mul]

/-- `|u*Mv| ≤ ‖u‖‖M‖‖v‖`. -/
theorem norm_bilinear_le (u : n → ℂ) (M : Matrix n n ℂ) (v : n → ℂ) :
    ‖bilinear u M v‖ ≤ vecNorm u * ‖M‖ * vecNorm v := by
  rw [bilinear, mul_assoc]
  exact (norm_star_dotProduct_le u _).trans
    (mul_le_mul_of_nonneg_left (vecNorm_mulVec_le M v) (vecNorm_nonneg u))

/-- `|A ⊗ B| ≤ ‖A‖‖B‖∏‖v_j‖`. -/
theorem norm_crossedTensor_le (v₁ v₂ v₃ v₄ : n → ℂ) (A B : Matrix n n ℂ) :
    ‖crossedTensor v₁ v₂ v₃ v₄ A B‖ ≤ ‖A‖ * ‖B‖ * fourNorm v₁ v₂ v₃ v₄ := by
  rw [crossedTensor, norm_mul, fourNorm]
  have h1 := norm_bilinear_le v₁ A v₄
  have h2 := norm_bilinear_le v₃ B v₂
  calc ‖bilinear v₁ A v₄‖ * ‖bilinear v₃ B v₂‖
      ≤ (vecNorm v₁ * ‖A‖ * vecNorm v₄) * (vecNorm v₃ * ‖B‖ * vecNorm v₂) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by
          have := vecNorm_nonneg v₁; have := vecNorm_nonneg v₄; positivity)
    _ = _ := by ring

/-- Coercivity: `Im K = Y + η`, `Y ⪰ 0` gives `η‖x‖ ≤ ‖Kx‖`. -/
theorem coercive_of_im (K Y : Matrix n n ℂ) {η : ℝ} (hY : Y.PosSemidef)
    (him : matrixImaginaryPart K = Y + η • (1 : Matrix n n ℂ)) (x : n → ℂ) :
    η * vecNorm x ≤ vecNorm (K *ᵥ x) := by
  have hq := quad_im K x
  rw [him, add_mulVec, dotProduct_add, smul_mulVec, one_mulVec, dotProduct_smul,
    star_self_eq] at hq
  have hYx := Complex.nonneg_iff.mp (hY.dotProduct_mulVec_nonneg x)
  have hre := congrArg Complex.re hq
  simp only [Complex.add_re, Complex.ofReal_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hre
  have hw : (star x ⬝ᵥ (K *ᵥ x)).im ≤ vecNorm x * vecNorm (K *ᵥ x) :=
    (Complex.im_le_norm _).trans (norm_star_dotProduct_le _ _)
  have hx := vecNorm_nonneg x
  have key : η * vecNorm x ^ 2 ≤ vecNorm x * vecNorm (K *ᵥ x) := by nlinarith [hYx.1]
  rcases hx.lt_or_eq with hx | hx
  · nlinarith
  · rw [← hx, mul_zero]; exact vecNorm_nonneg _

/-- `‖K⁻¹‖ ≤ η⁻¹` when `Im K = Y + η`, `Y ⪰ 0`, `η > 0`. -/
theorem norm_inv_le_of_im (K Y : Matrix n n ℂ) {η : ℝ} (hη : 0 < η) (hY : Y.PosSemidef)
    (him : matrixImaginaryPart K = Y + η • (1 : Matrix n n ℂ)) : ‖K⁻¹‖ ≤ η⁻¹ := by
  have hK := (passive_inverse_constructed K Y hη hY him).2.1
  refine opNorm_le_of_vec _ (inv_nonneg.mpr hη.le) fun y => ?_
  have := coercive_of_im K Y hY him (K⁻¹ *ᵥ y)
  rw [mulVec_mulVec, hK, one_mulVec] at this
  rw [inv_mul_eq_div, le_div_iff₀ hη]; linarith

end Vectors

/-! ## The passive coordinates of one old input -/

variable {W : ℕ}

theorem matrixImaginaryPart_nearPencil (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    matrixImaginaryPart (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) =
      passiveY X + etaZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) := by
  have h := matrixImaginaryPart_portPencil_general X (boundaryZ b E)
  rw [portPencil] at h
  rw [h, passiveY, etaZ]; abel

section Passive

variable {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
  {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
include hb0 hb h1 h2 hY

theorem norm_passiveResolvent_le : ‖passiveResolvent b E X‖ ≤ (etaZ b E)⁻¹ :=
  norm_inv_le_of_im _ _ (etaZ_pos b E (by linarith) h1 h2) hY
    (matrixImaginaryPart_nearPencil b E X)

theorem norm_passiveS_le : ‖passiveS b E X‖ ≤ 3 := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hR := norm_passiveResolvent_le hb0 hb h1 h2 hY
  rw [passiveS]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hη, Complex.norm_ofNat]
  simp only [mul_one]
  have h1' := norm_one_matrix_le (n := Fin W)
  have : 2 * etaZ b E * ‖passiveResolvent b E X‖ ≤ 2 := by
    have := mul_le_mul_of_nonneg_left hR (by positivity : (0 : ℝ) ≤ 2 * etaZ b E)
    rwa [mul_inv_cancel_right₀ hη.ne'] at this
  linarith

/-- `‖I - T‖ = ‖S*S‖ ≤ 9`. -/
theorem norm_one_sub_transmission_le : ‖1 - passiveTransmission b E X‖ ≤ 9 := by
  rw [passiveTransmission_eq_one_sub, sub_sub_cancel, Matrix.l2_opNorm_conjTranspose_mul_self]
  have := norm_passiveS_le hb0 hb h1 h2 hY
  nlinarith [norm_nonneg (passiveS b E X)]

omit hb0 hb h1 h2 hY in
theorem norm_cZero (b E : ℝ) (hη : 0 < etaZ b E) : ‖cZero b E‖ = (2 * etaZ b E)⁻¹ := by
  rw [cZero, norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hη, Complex.norm_ofNat]
  ring

/-- `‖f‖ ≤ 3/(2η)`. -/
theorem norm_passiveF_le : ‖passiveF b E X‖ ≤ 3 / (2 * etaZ b E) := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  rw [passiveF]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_cZero b E hη]
  have hR := norm_passiveResolvent_le hb0 hb h1 h2 hY
  have h1' := norm_one_matrix_le (n := Fin W)
  have : (2 * etaZ b E)⁻¹ * ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ (2 * etaZ b E)⁻¹ :=
    mul_le_of_le_one_right (by positivity) h1'
  have heq : 3 / (2 * etaZ b E) = (etaZ b E)⁻¹ + (2 * etaZ b E)⁻¹ := by
    field_simp; ring
  rw [heq]; linarith

end Passive

end BlockBand.Transmission.PassiveCovariance
