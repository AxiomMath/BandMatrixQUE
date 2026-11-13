module

public import BlockBand.Endpoints.Response.ResponseVarianceDefs

/-!
# The signed response trace identity: abstract two-port algebra

* `rvD_ratioDetDeriv_eq`: `DF(T)[D] = -F(T) Tr(r(T) D)`, `r(T) = y(I - yT)⁻¹ + x(I + xT)⁻¹`;
* `rvD_ratioDetC_eq`: the two port defects have the same determinant ratio, `F(T₀) = F(T₁)`
  (unitarity and Sylvester's identity);
* `rvD_trace_weight_defectDeriv` (per port): `Tr(r(T₀)Ṫ₀) + Tr(r(T₁)Ṫ₁) = -(Z + Z̄)`, `Z = -2η Tr(B X)`,
  `X = Σᵢ Jᵢ r(Tᵢ) sᵢ* Jᵢ* S` (the signed ratio derivative `∂ = -4ηF Re Tr(BX)`);
* `rvD_K_eq`, `rvD_weight_sub_hs_le`: `‖X - r₀I‖_HS ≤ c √g`, `g = Tr T₀`, `r₀ = x + y`,
  `c = 2r₀ + 2(y²/(1-y) + x²)` (`rvD_const`);
* `rvD_abstract_bound`: `|Re DF(T₀)[Ṫ₀] + Re DF(T₁)[Ṫ₁]| ≤ 4η(r₀ |Re Tr B| + c √g ‖B‖_HS)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate

/-!
### Hilbert–Schmidt norm toolkit
-/

section HS

variable {k l m : Type*} [Fintype k] [Fintype l] [Fintype m] [DecidableEq k] [DecidableEq l]
  [DecidableEq m]

omit [DecidableEq k] [DecidableEq l] in
theorem rvD_hsSq_eq_vecNormSq (Y : Matrix k l ℂ) :
    hsSq Y = vecNormSq (fun z : k × l => Y z.1 z.2) := by
  simp only [hsSq, vecNormSq, Fintype.sum_prod_type]

omit [DecidableEq k] [DecidableEq l] in
theorem rvD_sqrt_hsSq_eq_norm (Y : Matrix k l ℂ) :
    Real.sqrt (hsSq Y) = ‖(EuclideanSpace.equiv (k × l) ℂ).symm (fun z => Y z.1 z.2)‖ := by
  rw [rvD_hsSq_eq_vecNormSq, vecNormSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

omit [DecidableEq k] [DecidableEq l] in
/-- Minkowski for the Hilbert–Schmidt norm. -/
theorem rvD_sqrt_hsSq_add_le (A B : Matrix k l ℂ) :
    Real.sqrt (hsSq (A + B)) ≤ Real.sqrt (hsSq A) + Real.sqrt (hsSq B) := by
  rw [rvD_sqrt_hsSq_eq_norm, rvD_sqrt_hsSq_eq_norm, rvD_sqrt_hsSq_eq_norm]
  have : (fun z : k × l => (A + B) z.1 z.2) = (fun z => A z.1 z.2) + (fun z => B z.1 z.2) := rfl
  rw [this, map_add]
  exact norm_add_le _ _

omit [DecidableEq k] [DecidableEq l] in
theorem rvD_hsSq_smul (c : ℂ) (Y : Matrix k l ℂ) : hsSq (c • Y) = ‖c‖ ^ 2 * hsSq Y := by
  simp only [hsSq, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

omit [DecidableEq k] [DecidableEq l] in
theorem rvD_sqrt_hsSq_smul (c : ℂ) (Y : Matrix k l ℂ) :
    Real.sqrt (hsSq (c • Y)) = ‖c‖ * Real.sqrt (hsSq Y) := by
  rw [rvD_hsSq_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

omit [DecidableEq k] [DecidableEq l] in
theorem rvD_hsSq_neg (Y : Matrix k l ℂ) : hsSq (-Y) = hsSq Y := by
  simp only [hsSq, Matrix.neg_apply, norm_neg]

omit [DecidableEq k] [DecidableEq l] in
theorem rvD_sqrt_hsSq_sub_le (A B : Matrix k l ℂ) :
    Real.sqrt (hsSq (A - B)) ≤ Real.sqrt (hsSq A) + Real.sqrt (hsSq B) := by
  rw [sub_eq_add_neg]
  exact (rvD_sqrt_hsSq_add_le _ _).trans (by rw [rvD_hsSq_neg])

omit [DecidableEq l] [DecidableEq m] in
theorem rvD_sqrt_hsSq_mul_le (X : Matrix m k ℂ) (Y : Matrix k l ℂ) :
    Real.sqrt (hsSq (X * Y)) ≤ ‖X‖ * Real.sqrt (hsSq Y) := by
  rw [← Real.sqrt_sq (norm_nonneg X), ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt (hsSq_mul_le X Y)

omit [DecidableEq l] [DecidableEq m] in
theorem rvD_hsSq_mul_le_of_norm {X : Matrix m k ℂ} (hX : ‖X‖ ≤ 1) (Y : Matrix k l ℂ) :
    hsSq (X * Y) ≤ hsSq Y := by
  refine (hsSq_mul_le X Y).trans ?_
  have h0 := norm_nonneg X
  have : ‖X‖ ^ 2 ≤ 1 := by nlinarith
  have := hsSq_nonneg Y
  nlinarith

omit [DecidableEq m] in
theorem rvD_hsSq_mul_le_of_norm_right {C : Matrix k l ℂ} (hC : ‖C‖ ≤ 1) (Y : Matrix m k ℂ) :
    hsSq (Y * C) ≤ hsSq Y := by
  refine (hsSq_mul_le_right Y C).trans ?_
  have h0 := norm_nonneg C
  have : ‖C‖ ^ 2 ≤ 1 := by nlinarith
  have := hsSq_nonneg Y
  nlinarith

omit [DecidableEq k] in
/-- Cauchy–Schwarz for `Tr(BK)`, `B` Hermitian. -/
theorem rvD_norm_trace_mul_le {B K : Matrix k k ℂ} (hB : B.IsHermitian) :
    ‖(B * K).trace‖ ≤ Real.sqrt (hsSq B) * Real.sqrt (hsSq K) := by
  have e : (B * K).trace = ∑ i, ∑ j, star (B i j) * K i j := by
    simp only [trace, diag, mul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hB.apply]
  rw [e, ← Real.sqrt_mul (hsSq_nonneg _)]
  exact Real.le_sqrt_of_sq_le (norm_hsPairing_sq_le B K)

end HS

/-!
### Sylvester's identity with a scalar
-/

theorem rvD_det_smul_one_add_mul_comm {n : Type*} [Fintype n] [DecidableEq n] (c : ℂ)
    (X Y : Matrix n n ℂ) : (c • 1 + X * Y).det = (c • 1 + Y * X).det := by
  by_cases hc : c = 0
  · subst hc
    simp [det_mul, mul_comm]
  · have e1 : c • (1 : Matrix n n ℂ) + X * Y = c • (1 + (c⁻¹ • X) * Y) := by
      rw [smul_add, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc, one_smul]
    have e2 : c • (1 : Matrix n n ℂ) + Y * X = c • (1 + Y * (c⁻¹ • X)) := by
      rw [smul_add, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
    rw [e1, e2, det_smul, det_smul, det_one_add_mul_comm]

/-!
### The abstract two-port setting
-/

section TwoPort

variable {p w : Type*} [Fintype p] [DecidableEq p] [Fintype w] [DecidableEq w]

/-- The zero-source defect derivative `Ṫ[B] = -(ṡ*s + s*ṡ)`, `s = J*SJ`, `ṡ = J*(-2ηSB)J`, with a
free source matrix `B` (the `pencilPortDefectDeriv` is the case `S = 𝕊₀`, `B = B_q`).
-/
def rvD_defectDeriv (η : ℝ) (S B : Matrix p p ℂ) (J : Matrix p w ℂ) : Matrix w w ℂ :=
  -((Jᴴ * (-(((2 * η : ℝ) : ℂ)) • (S * B)) * J)ᴴ * (Jᴴ * S * J) +
    (Jᴴ * S * J)ᴴ * (Jᴴ * (-(((2 * η : ℝ) : ℂ)) • (S * B)) * J))

/-- `r(T) = y(I - yT)⁻¹ + x(I + xT)⁻¹`. -/
def rvD_weight (x y : ℝ) (T : Matrix w w ℂ) : Matrix w w ℂ :=
  (y : ℂ) • (1 - (y : ℂ) • T)⁻¹ + (x : ℂ) • (1 + (x : ℂ) • T)⁻¹

/-- The constant `c_{x,y} = 2(x + y) + 2(y²/(1-y) + x²)` of the signed response trace bound. -/
def rvD_const (x y : ℝ) : ℝ := 2 * (x + y) + 2 * (y ^ 2 / (1 - y) + x ^ 2)

theorem rvD_const_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    0 ≤ rvD_const x y := by
  have : 0 ≤ y ^ 2 / (1 - y) := div_nonneg (sq_nonneg y) (by linarith)
  unfold rvD_const
  positivity

omit [DecidableEq p] [DecidableEq w] in
theorem rvD_defectDeriv_sub (η : ℝ) (S B₁ B₂ : Matrix p p ℂ) (J : Matrix p w ℂ) :
    rvD_defectDeriv η S (B₁ - B₂) J = rvD_defectDeriv η S B₁ J - rvD_defectDeriv η S B₂ J := by
  simp only [rvD_defectDeriv, Matrix.mul_sub, smul_sub, Matrix.sub_mul, conjTranspose_sub]
  abel

omit [Fintype p] [DecidableEq p] in
theorem rvD_ratioDetDeriv_eq (x y : ℝ) (T D : Matrix w w ℂ) :
    ratioDetDeriv x y T D = -(ratioDetC x y T * (rvD_weight x y T * D).trace) := by
  simp only [ratioDetDeriv, rvD_weight, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,
    trace_add, trace_smul, smul_eq_mul]
  ring

omit [Fintype p] [DecidableEq p] in
theorem rvD_weight_isHermitian {T : Matrix w w ℂ} (hT : T.IsHermitian) (x y : ℝ) :
    (rvD_weight x y T).IsHermitian := by
  have hy : (1 - (y : ℂ) • T).IsHermitian := by
    refine (isHermitian_one).sub ?_
    unfold IsHermitian
    rw [conjTranspose_smul, hT.eq, Complex.star_def, Complex.conj_ofReal]
  have hx : (1 + (x : ℂ) • T).IsHermitian := by
    refine (isHermitian_one).add ?_
    unfold IsHermitian
    rw [conjTranspose_smul, hT.eq, Complex.star_def, Complex.conj_ofReal]
  unfold IsHermitian rvD_weight
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, hy.inv.eq, hx.inv.eq]
  simp only [Complex.star_def, Complex.conj_ofReal]

omit [DecidableEq p] [DecidableEq w] in
/-- The per-port trace identity: `Tr(R Ṫ[B]) = -(z + z̄)`, `z = -2η Tr(B J R s* J* S)`. -/
theorem rvD_trace_weight_defectDeriv (η : ℝ) (S B : Matrix p p ℂ) (J : Matrix p w ℂ)
    {R : Matrix w w ℂ} (hR : R.IsHermitian) :
    (R * rvD_defectDeriv η S B J).trace =
      -((-(((2 * η : ℝ) : ℂ))) * (B * (J * R * (Jᴴ * S * J)ᴴ * Jᴴ * S)).trace +
        star ((-(((2 * η : ℝ) : ℂ))) * (B * (J * R * (Jᴴ * S * J)ᴴ * Jᴴ * S)).trace)) := by
  set c : ℂ := -(((2 * η : ℝ) : ℂ))
  set s := Jᴴ * S * J
  set sd := Jᴴ * (c • (S * B)) * J
  have hD : rvD_defectDeriv η S B J = -(sdᴴ * s + sᴴ * sd) := rfl
  have h1 : (R * (sᴴ * sd)).trace = c * (B * (J * R * sᴴ * Jᴴ * S)).trace := by
    have : R * (sᴴ * sd) = c • ((R * sᴴ * Jᴴ * S) * (B * J)) := by
      simp only [sd, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [this, trace_smul, smul_eq_mul, trace_mul_comm]
    simp only [Matrix.mul_assoc]
  clear_value c s sd
  have h2 : (R * (sdᴴ * s)).trace = star (R * (sᴴ * sd)).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      hR.eq, trace_mul_comm]
  rw [hD, Matrix.mul_neg, trace_neg, Matrix.mul_add, trace_add, h2, h1]
  ring

omit [DecidableEq p] in
theorem rvD_norm_le_one_of_gram {A : Matrix p w ℂ} (h : Aᴴ * A = 1) : ‖A‖ ≤ 1 := by
  have h1 := l2_opNorm_conjTranspose_mul_self A
  rw [h] at h1
  have h2 := l2_opNorm_one_le (n := w)
  have h0 := norm_nonneg A
  nlinarith

theorem rvD_norm_mul_le_one {m : Type*} [Fintype m] {A : Matrix m p ℂ} {C : Matrix p w ℂ}
    (hA : ‖A‖ ≤ 1) (hC : ‖C‖ ≤ 1) : ‖A * C‖ ≤ 1 :=
  (l2_opNorm_mul A C).trans (by nlinarith [norm_nonneg A, norm_nonneg C])

omit [DecidableEq w] in
/-- Column split: `Σⱼ (Jⱼ*SJ)*(Jⱼ*SJ) = J*(S*S)J`. -/
theorem rvD_col_split {J₀ J₁ : Matrix p w ℂ} (hP : J₀ * J₀ᴴ + J₁ * J₁ᴴ = 1)
    (S : Matrix p p ℂ) (J : Matrix p w ℂ) :
    (J₀ᴴ * S * J)ᴴ * (J₀ᴴ * S * J) + (J₁ᴴ * S * J)ᴴ * (J₁ᴴ * S * J) = Jᴴ * (Sᴴ * S) * J := by
  have : (J₀ᴴ * S * J)ᴴ * (J₀ᴴ * S * J) + (J₁ᴴ * S * J)ᴴ * (J₁ᴴ * S * J) =
      Jᴴ * Sᴴ * (J₀ * J₀ᴴ + J₁ * J₁ᴴ) * S * J := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_assoc]
  rw [this, hP, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

omit [DecidableEq w] in
/-- Row split: `Σⱼ (J*SJⱼ)(J*SJⱼ)* = J*(SS*)J`. -/
theorem rvD_row_split {J₀ J₁ : Matrix p w ℂ} (hP : J₀ * J₀ᴴ + J₁ * J₁ᴴ = 1)
    (S : Matrix p p ℂ) (J : Matrix p w ℂ) :
    (Jᴴ * S * J₀) * (Jᴴ * S * J₀)ᴴ + (Jᴴ * S * J₁) * (Jᴴ * S * J₁)ᴴ = Jᴴ * (S * Sᴴ) * J := by
  have : (Jᴴ * S * J₀) * (Jᴴ * S * J₀)ᴴ + (Jᴴ * S * J₁) * (Jᴴ * S * J₁)ᴴ =
      Jᴴ * S * (J₀ * J₀ᴴ + J₁ * J₁ᴴ) * Sᴴ * J := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_assoc]
  rw [this, hP, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

/-- By unitarity the defect of port `0` is the transmission Gram matrix: `T₀ = s₁₀*s₁₀`. -/
theorem rvD_portDefect_eq_gram {S : Matrix p p ℂ} {J₀ J₁ : Matrix p w ℂ} (hS : Sᴴ * S = 1)
    (hP : J₀ * J₀ᴴ + J₁ * J₁ᴴ = 1) (hJ₀ : J₀ᴴ * J₀ = 1) :
    portDefectOf S J₀ = (J₁ᴴ * S * J₀)ᴴ * (J₁ᴴ * S * J₀) := by
  have h := rvD_col_split hP S J₀
  rw [hS, Matrix.mul_one, hJ₀] at h
  exact sub_eq_of_eq_add (h.symm.trans (add_comm _ _))

/-- `‖s₁₀‖²_HS = Tr T₀ = g`. -/
theorem rvD_hsSq_trans_eq {S : Matrix p p ℂ} {J₀ J₁ : Matrix p w ℂ} (hS : Sᴴ * S = 1)
    (hP : J₀ * J₀ᴴ + J₁ * J₁ᴴ = 1) (hJ₀ : J₀ᴴ * J₀ = 1) :
    hsSq (J₁ᴴ * S * J₀) = (portDefectOf S J₀).trace.re := by
  rw [rvD_portDefect_eq_gram hS hP hJ₀, trace_conjTranspose_mul_self_re_eq_hsSq]

/-- `‖s₀₁‖²_HS = Tr T₀ = g` (row unitarity). -/
theorem rvD_hsSq_trans_eq' {S : Matrix p p ℂ} {J₀ J₁ : Matrix p w ℂ} (hS : Sᴴ * S = 1)
    (hP : J₀ * J₀ᴴ + J₁ * J₁ᴴ = 1) (hJ₀ : J₀ᴴ * J₀ = 1) :
    hsSq (J₀ᴴ * S * J₁) = (portDefectOf S J₀).trace.re := by
  have hS' : S * Sᴴ = 1 := mul_eq_one_comm.1 hS
  have h := rvD_row_split hP S J₀
  rw [hS', Matrix.mul_one, hJ₀] at h
  have e : (J₀ᴴ * S * J₁) * (J₀ᴴ * S * J₁)ᴴ = 1 - (J₀ᴴ * S * J₀) * (J₀ᴴ * S * J₀)ᴴ :=
    eq_sub_of_add_eq' h
  rw [← hsSq_conjTranspose, ← trace_conjTranspose_mul_self_re_eq_hsSq,
    conjTranspose_conjTranspose, e, portDefectOf, trace_sub, trace_sub,
    trace_mul_comm (J₀ᴴ * S * J₀)]

/-- Equal spectra of the two defects: `det(I + aT₀) = det(I + aT₁)` for every `a`. -/
theorem rvD_det_one_add_smul_eq {S : Matrix p p ℂ} {J₀ J₁ : Matrix p w ℂ} (hS : Sᴴ * S = 1)
    (hP : J₀ * J₀ᴴ + J₁ * J₁ᴴ = 1) (hJ₀ : J₀ᴴ * J₀ = 1) (hJ₁ : J₁ᴴ * J₁ = 1) (a : ℂ) :
    (1 + a • portDefectOf S J₀).det = (1 + a • portDefectOf S J₁).det := by
  have hS' : S * Sᴴ = 1 := mul_eq_one_comm.1 hS
  set s₁₀ := J₁ᴴ * S * J₀
  set s₁ := J₁ᴴ * S * J₁
  have h := rvD_row_split hP S J₁
  rw [hS', Matrix.mul_one, hJ₁] at h
  have e : s₁₀ * s₁₀ᴴ = 1 - s₁ * s₁ᴴ := eq_sub_of_add_eq h
  have e1 : (1 : Matrix w w ℂ) + a • (s₁₀ᴴ * s₁₀) = 1 + (a • s₁₀ᴴ) * s₁₀ := by
    rw [Matrix.smul_mul]
  have e2 : (1 : Matrix w w ℂ) + s₁₀ * (a • s₁₀ᴴ) = (1 + a) • 1 + ((-a) • s₁) * s₁ᴴ := by
    rw [Matrix.mul_smul, e, Matrix.smul_mul]
    module
  have e3 : (1 : Matrix w w ℂ) + a • portDefectOf S J₁ = (1 + a) • 1 + s₁ᴴ * ((-a) • s₁) := by
    rw [Matrix.mul_smul, portDefectOf]
    module
  rw [rvD_portDefect_eq_gram hS hP hJ₀, e1, det_one_add_mul_comm, e2, e3,
    rvD_det_smul_one_add_mul_comm]

/-- `F(T₀) = F(T₁)`. -/
theorem rvD_ratioDetC_eq {S : Matrix p p ℂ} {J₀ J₁ : Matrix p w ℂ} (hS : Sᴴ * S = 1)
    (hP : J₀ * J₀ᴴ + J₁ * J₁ᴴ = 1) (hJ₀ : J₀ᴴ * J₀ = 1) (hJ₁ : J₁ᴴ * J₁ = 1) (x y : ℝ) :
    ratioDetC x y (portDefectOf S J₀) = ratioDetC x y (portDefectOf S J₁) := by
  unfold ratioDetC
  rw [sub_eq_add_neg, ← neg_smul, sub_eq_add_neg, ← neg_smul,
    rvD_det_one_add_smul_eq hS hP hJ₀ hJ₁, rvD_det_one_add_smul_eq hS hP hJ₀ hJ₁]

omit [Fintype p] [DecidableEq p] in
theorem rvD_weight_sub_eq_of {x y : ℝ} {T Ai Bi : Matrix w w ℂ}
    (hA : Ai = 1 + (y : ℂ) • (Ai * T)) (hB : Bi = 1 - (x : ℂ) • (Bi * T)) :
    (y : ℂ) • Ai + (x : ℂ) • Bi - ((x + y : ℝ) : ℂ) • 1 =
      ((y : ℂ) * y) • (Ai * T) - ((x : ℂ) * x) • (Bi * T) := by
  conv_lhs => rw [hA, hB]
  push_cast
  module

omit [Fintype p] [DecidableEq p] in
/-- `‖r(T) - r₀I‖_HS ≤ (y²/(1-y) + x²) ‖T‖_HS` on the band `0 ⪯ T ⪯ I`. -/
theorem rvD_weight_sub_hs_le {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1)
    {T : Matrix w w ℂ} (h : IsUnitBand T) :
    Real.sqrt (hsSq (rvD_weight x y T - ((x + y : ℝ) : ℂ) • 1)) ≤
      (y ^ 2 / (1 - y) + x ^ 2) * Real.sqrt (hsSq T) := by
  obtain ⟨hAu, hnA⟩ := band_inv_sub h hy0 hy1
  obtain ⟨hBu, hnB⟩ := band_inv_add h hx
  have h1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hAu)
  have h2 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hBu)
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul] at h1
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul] at h2
  rw [rvD_weight, rvD_weight_sub_eq_of (sub_eq_iff_eq_add.1 h1) (eq_sub_of_add_eq h2)]
  have hny : ‖(y : ℂ) * y‖ = y ^ 2 := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      sq]
  have hnx : ‖(x : ℂ) * x‖ = x ^ 2 := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      sq]
  have hh := Real.sqrt_nonneg (hsSq T)
  refine (rvD_sqrt_hsSq_sub_le _ _).trans ?_
  rw [rvD_sqrt_hsSq_smul, rvD_sqrt_hsSq_smul, hny, hnx]
  calc y ^ 2 * Real.sqrt (hsSq ((1 - (y : ℂ) • T)⁻¹ * T)) +
        x ^ 2 * Real.sqrt (hsSq ((1 + (x : ℂ) • T)⁻¹ * T))
      ≤ y ^ 2 * ((1 - y)⁻¹ * Real.sqrt (hsSq T)) + x ^ 2 * (1 * Real.sqrt (hsSq T)) := by
        refine add_le_add (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
          (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
        · exact (rvD_sqrt_hsSq_mul_le _ _).trans (mul_le_mul_of_nonneg_right hnA hh)
        · exact (rvD_sqrt_hsSq_mul_le _ _).trans (mul_le_mul_of_nonneg_right hnB hh)
    _ = _ := by rw [div_eq_mul_inv]; ring

omit [DecidableEq w] in
/-- `Σᵢ PᵢS*PᵢS + P₀S*P₁S + P₁S*P₀S = S*S = I`. -/
theorem rvD_sum_one {S : Matrix p p ℂ} {J₀ J₁ : Matrix p w ℂ} (hS : Sᴴ * S = 1)
    (hP : J₀ * J₀ᴴ + J₁ * J₁ᴴ = 1) :
    J₀ * (J₀ᴴ * S * J₀)ᴴ * J₀ᴴ * S + J₁ * (J₁ᴴ * S * J₁)ᴴ * J₁ᴴ * S +
      (J₀ * (J₁ᴴ * S * J₀)ᴴ * (J₁ᴴ * S) + J₁ * (J₀ᴴ * S * J₁)ᴴ * (J₀ᴴ * S)) = 1 := by
  have : J₀ * (J₀ᴴ * S * J₀)ᴴ * J₀ᴴ * S + J₁ * (J₁ᴴ * S * J₁)ᴴ * J₁ᴴ * S +
      (J₀ * (J₁ᴴ * S * J₀)ᴴ * (J₁ᴴ * S) + J₁ * (J₀ᴴ * S * J₁)ᴴ * (J₀ᴴ * S)) =
      (J₀ * J₀ᴴ + J₁ * J₁ᴴ) * Sᴴ * (J₀ * J₀ᴴ + J₁ * J₁ᴴ) * S := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc]
    abel
  rw [this, hP, Matrix.one_mul, Matrix.mul_one, hS]

/-- The decomposition `X - r₀I = -r₀(P₀S*P₁S + P₁S*P₀S) + Σᵢ Jᵢ(Rᵢ - r₀)sᵢ*Jᵢ*S`. -/
theorem rvD_K_eq {S : Matrix p p ℂ} {J₀ J₁ : Matrix p w ℂ} (hS : Sᴴ * S = 1)
    (hP : J₀ * J₀ᴴ + J₁ * J₁ᴴ = 1) (R₀ R₁ : Matrix w w ℂ) (r : ℂ) :
    (J₀ * R₀ * (J₀ᴴ * S * J₀)ᴴ * J₀ᴴ * S + J₁ * R₁ * (J₁ᴴ * S * J₁)ᴴ * J₁ᴴ * S) - r • 1 =
      -(r • (J₀ * (J₁ᴴ * S * J₀)ᴴ * (J₁ᴴ * S) + J₁ * (J₀ᴴ * S * J₁)ᴴ * (J₀ᴴ * S))) +
        J₀ * (R₀ - r • 1) * (J₀ᴴ * S * J₀)ᴴ * J₀ᴴ * S +
        J₁ * (R₁ - r • 1) * (J₁ᴴ * S * J₁)ᴴ * J₁ᴴ * S := by
  rw [← rvD_sum_one hS hP]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    smul_add]
  abel

/-- Abstract signed response trace bound. For a unitary `S`, two complementary port inclusions, a
Hermitian `B`, `η ≥ 0`, `x ≥ 0`, `0 ≤ y < 1`:
`|Re DF(T₀)[Ṫ₀[B]] + Re DF(T₁)[Ṫ₁[B]]| ≤ 4η((x + y)|Re Tr B| + c √(Tr T₀) ‖B‖_HS)`. -/
theorem rvD_abstract_bound {x y η : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) (hη : 0 ≤ η)
    {S B : Matrix p p ℂ} {J₀ J₁ : Matrix p w ℂ} (hS : Sᴴ * S = 1)
    (hP : J₀ * J₀ᴴ + J₁ * J₁ᴴ = 1) (hJ₀ : J₀ᴴ * J₀ = 1) (hJ₁ : J₁ᴴ * J₁ = 1)
    (hB : B.IsHermitian) :
    |(ratioDetDeriv x y (portDefectOf S J₀) (rvD_defectDeriv η S B J₀)).re +
        (ratioDetDeriv x y (portDefectOf S J₁) (rvD_defectDeriv η S B J₁)).re| ≤
      4 * η * ((x + y) * |B.trace.re| +
        rvD_const x y * Real.sqrt ((portDefectOf S J₀).trace.re) * Real.sqrt (hsSq B)) := by
  have hP' : J₁ * J₁ᴴ + J₀ * J₀ᴴ = 1 := by rw [add_comm]; exact hP
  -- norms
  have nS : ‖S‖ ≤ 1 := rvD_norm_le_one_of_gram hS
  have nJ₀ : ‖J₀‖ ≤ 1 := rvD_norm_le_one_of_gram hJ₀
  have nJ₁ : ‖J₁‖ ≤ 1 := rvD_norm_le_one_of_gram hJ₁
  have nJ₀H : ‖J₀ᴴ‖ ≤ 1 := by rw [l2_opNorm_conjTranspose]; exact nJ₀
  have nJ₁H : ‖J₁ᴴ‖ ≤ 1 := by rw [l2_opNorm_conjTranspose]; exact nJ₁
  have nJS₀ : ‖J₀ᴴ * S‖ ≤ 1 := rvD_norm_mul_le_one nJ₀H nS
  have nJS₁ : ‖J₁ᴴ * S‖ ≤ 1 := rvD_norm_mul_le_one nJ₁H nS
  have ns₀ : ‖J₀ᴴ * S * J₀‖ ≤ 1 := rvD_norm_mul_le_one nJS₀ nJ₀
  have ns₁ : ‖J₁ᴴ * S * J₁‖ ≤ 1 := rvD_norm_mul_le_one nJS₁ nJ₁
  have ns₁₀ : ‖J₁ᴴ * S * J₀‖ ≤ 1 := rvD_norm_mul_le_one nJS₁ nJ₀
  have ns₀₁ : ‖J₀ᴴ * S * J₁‖ ≤ 1 := rvD_norm_mul_le_one nJS₀ nJ₁
  have ns₀H : ‖(J₀ᴴ * S * J₀)ᴴ‖ ≤ 1 := by rw [l2_opNorm_conjTranspose]; exact ns₀
  have ns₁H : ‖(J₁ᴴ * S * J₁)ᴴ‖ ≤ 1 := by rw [l2_opNorm_conjTranspose]; exact ns₁
  have ns₁₀H : ‖(J₁ᴴ * S * J₀)ᴴ‖ ≤ 1 := by rw [l2_opNorm_conjTranspose]; exact ns₁₀
  have ns₀₁H : ‖(J₀ᴴ * S * J₁)ᴴ‖ ≤ 1 := by rw [l2_opNorm_conjTranspose]; exact ns₀₁
  -- the conductance
  have hg₁₀ : hsSq (J₁ᴴ * S * J₀) = (portDefectOf S J₀).trace.re := rvD_hsSq_trans_eq hS hP hJ₀
  have hg₀₁ : hsSq (J₀ᴴ * S * J₁) = (portDefectOf S J₀).trace.re :=
    rvD_hsSq_trans_eq' hS hP hJ₀
  set g := (portDefectOf S J₀).trace.re with hg
  -- bands and weights
  have hb₀ : IsUnitBand (portDefectOf S J₀) := isUnitBand_one_sub_gram ns₀
  have hb₁ : IsUnitBand (portDefectOf S J₁) := isUnitBand_one_sub_gram ns₁
  have hT₀ : Real.sqrt (hsSq (portDefectOf S J₀)) ≤ Real.sqrt g := by
    rw [rvD_portDefect_eq_gram hS hP hJ₀]
    exact Real.sqrt_le_sqrt ((rvD_hsSq_mul_le_of_norm ns₁₀H _).trans hg₁₀.le)
  have hT₁ : Real.sqrt (hsSq (portDefectOf S J₁)) ≤ Real.sqrt g := by
    rw [rvD_portDefect_eq_gram hS hP' hJ₁]
    exact Real.sqrt_le_sqrt ((rvD_hsSq_mul_le_of_norm ns₀₁H _).trans hg₀₁.le)
  have hR₀ := rvD_weight_isHermitian hb₀.1 x y
  have hR₁ := rvD_weight_isHermitian hb₁.1 x y
  have hc' : 0 ≤ y ^ 2 / (1 - y) + x ^ 2 :=
    add_nonneg (div_nonneg (sq_nonneg y) (by linarith)) (sq_nonneg x)
  have hE₀ := (rvD_weight_sub_hs_le hx hy0 hy1 hb₀).trans (mul_le_mul_of_nonneg_left hT₀ hc')
  have hE₁ := (rvD_weight_sub_hs_le hx hy0 hy1 hb₁).trans (mul_le_mul_of_nonneg_left hT₁ hc')
  -- the Hilbert–Schmidt bound of `K = X - r₀I`
  have hr₀ : 0 ≤ x + y := add_nonneg hx hy0
  have hsg := Real.sqrt_nonneg g
  have hK : Real.sqrt (hsSq ((J₀ * rvD_weight x y (portDefectOf S J₀) * (J₀ᴴ * S * J₀)ᴴ *
        J₀ᴴ * S + J₁ * rvD_weight x y (portDefectOf S J₁) * (J₁ᴴ * S * J₁)ᴴ * J₁ᴴ * S) -
        ((x + y : ℝ) : ℂ) • 1)) ≤ rvD_const x y * Real.sqrt g := by
    rw [rvD_K_eq hS hP]
    refine (rvD_sqrt_hsSq_add_le _ _).trans ?_
    refine (add_le_add_left (rvD_sqrt_hsSq_add_le _ _) _).trans ?_
    rw [rvD_hsSq_neg, rvD_sqrt_hsSq_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr₀]
    have hQ := rvD_sqrt_hsSq_add_le (J₀ * (J₁ᴴ * S * J₀)ᴴ * (J₁ᴴ * S))
      (J₁ * (J₀ᴴ * S * J₁)ᴴ * (J₀ᴴ * S))
    have hQ₀ : Real.sqrt (hsSq (J₀ * (J₁ᴴ * S * J₀)ᴴ * (J₁ᴴ * S))) ≤ Real.sqrt g :=
      Real.sqrt_le_sqrt (((rvD_hsSq_mul_le_of_norm_right nJS₁ _).trans
        (rvD_hsSq_mul_le_of_norm nJ₀ _)).trans (by rw [hsSq_conjTranspose, hg₁₀]))
    have hQ₁ : Real.sqrt (hsSq (J₁ * (J₀ᴴ * S * J₁)ᴴ * (J₀ᴴ * S))) ≤ Real.sqrt g :=
      Real.sqrt_le_sqrt (((rvD_hsSq_mul_le_of_norm_right nJS₀ _).trans
        (rvD_hsSq_mul_le_of_norm nJ₁ _)).trans (by rw [hsSq_conjTranspose, hg₀₁]))
    have hY₀ : Real.sqrt (hsSq (J₀ * (rvD_weight x y (portDefectOf S J₀) -
        ((x + y : ℝ) : ℂ) • 1) * (J₀ᴴ * S * J₀)ᴴ * J₀ᴴ * S)) ≤
        Real.sqrt (hsSq (rvD_weight x y (portDefectOf S J₀) - ((x + y : ℝ) : ℂ) • 1)) :=
      Real.sqrt_le_sqrt ((rvD_hsSq_mul_le_of_norm_right nS _).trans
        ((rvD_hsSq_mul_le_of_norm_right nJ₀H _).trans
          ((rvD_hsSq_mul_le_of_norm_right ns₀H _).trans (rvD_hsSq_mul_le_of_norm nJ₀ _))))
    have hY₁ : Real.sqrt (hsSq (J₁ * (rvD_weight x y (portDefectOf S J₁) -
        ((x + y : ℝ) : ℂ) • 1) * (J₁ᴴ * S * J₁)ᴴ * J₁ᴴ * S)) ≤
        Real.sqrt (hsSq (rvD_weight x y (portDefectOf S J₁) - ((x + y : ℝ) : ℂ) • 1)) :=
      Real.sqrt_le_sqrt ((rvD_hsSq_mul_le_of_norm_right nS _).trans
        ((rvD_hsSq_mul_le_of_norm_right nJ₁H _).trans
          ((rvD_hsSq_mul_le_of_norm_right ns₁H _).trans (rvD_hsSq_mul_le_of_norm nJ₁ _))))
    have h1 := mul_le_mul_of_nonneg_left (hQ.trans (add_le_add hQ₀ hQ₁)) hr₀
    unfold rvD_const
    nlinarith
  -- the exact signed ratio derivative identity
  have hF := rvD_ratioDetC_eq hS hP hJ₀ hJ₁ x y
  have hFre : |(ratioDetC x y (portDefectOf S J₀)).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans (norm_ratioDetC_le_one hx hy0 hy1 hb₀)
  have e2 : ∀ z : ℂ, z + star z = ((2 * z.re : ℝ) : ℂ) := fun z => by
    rw [Complex.star_def]; exact Complex.add_conj z
  rw [rvD_ratioDetDeriv_eq, rvD_ratioDetDeriv_eq, ← hF,
    rvD_trace_weight_defectDeriv η S B J₀ hR₀, rvD_trace_weight_defectDeriv η S B J₁ hR₁,
    e2, e2]
  simp only [mul_neg, neg_neg, Complex.re_mul_ofReal, neg_mul, Complex.neg_re,
    Complex.re_ofReal_mul]
  set X := J₀ * rvD_weight x y (portDefectOf S J₀) * (J₀ᴴ * S * J₀)ᴴ * J₀ᴴ * S +
    J₁ * rvD_weight x y (portDefectOf S J₁) * (J₁ᴴ * S * J₁)ᴴ * J₁ᴴ * S with hX
  set K := X - ((x + y : ℝ) : ℂ) • 1 with hKdef
  have htr : (B * (J₀ * rvD_weight x y (portDefectOf S J₀) * (J₀ᴴ * S * J₀)ᴴ * J₀ᴴ * S)).trace.re +
      (B * (J₁ * rvD_weight x y (portDefectOf S J₁) * (J₁ᴴ * S * J₁)ᴴ * J₁ᴴ * S)).trace.re =
      (x + y) * B.trace.re + (B * K).trace.re := by
    have hXK : X = ((x + y : ℝ) : ℂ) • 1 + K := by rw [hKdef]; abel
    rw [← Complex.add_re, ← trace_add, ← Matrix.mul_add, ← hX, hXK, Matrix.mul_add,
      Matrix.mul_smul, Matrix.mul_one, trace_add, trace_smul, smul_eq_mul, Complex.add_re,
      Complex.re_ofReal_mul]
  set F := ratioDetC x y (portDefectOf S J₀)
  set t₀ := (B * (J₀ * rvD_weight x y (portDefectOf S J₀) * (J₀ᴴ * S * J₀)ᴴ * J₀ᴴ * S)).trace.re
  set t₁ := (B * (J₁ * rvD_weight x y (portDefectOf S J₁) * (J₁ᴴ * S * J₁)ᴴ * J₁ᴴ * S)).trace.re
  have hτ : |t₀ + t₁| ≤ (x + y) * |B.trace.re| +
      rvD_const x y * Real.sqrt g * Real.sqrt (hsSq B) := by
    rw [htr]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hr₀]
    · refine (Complex.abs_re_le_norm _).trans ((rvD_norm_trace_mul_le hB).trans ?_)
      have := mul_le_mul_of_nonneg_left hK (Real.sqrt_nonneg (hsSq B))
      linarith
  have e3 : -(F.re * (2 * (2 * η * t₀))) + -(F.re * (2 * (2 * η * t₁))) =
      -(4 * η) * F.re * (t₀ + t₁) := by ring
  rw [e3, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * η)]
  calc 4 * η * |F.re| * |t₀ + t₁| ≤ 4 * η * 1 * |t₀ + t₁| := by gcongr
    _ ≤ 4 * η * 1 * ((x + y) * |B.trace.re| +
        rvD_const x y * Real.sqrt g * Real.sqrt (hsSq B)) := by gcongr
    _ = _ := by ring

end TwoPort

end BlockBand.Endpoints
