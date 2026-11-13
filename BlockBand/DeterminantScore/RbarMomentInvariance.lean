module

public import BlockBand.DeterminantScore.RbarMomentEigen
public import BlockBand.DeterminantScore.ExactScoreDensity
public import BlockBand.Angular.DetFactorGUE

/-!
# Stabilizer invariance of the conditional inverse

For Hermitian `K` (on `Fin m`), `t ≥ 0`, sector `ℓ`, and the unnormalized inverse moment
`S = E[1{N_-(K+G)=ℓ} det(K+G)² (K+G)⁻¹]` (`ExactScore.sectorInvMoment`, `G ~ G_m(t)`):
* `sectorInvMoment_unitary_conj`: `S = W*SW` for unitary `W` with `W*KW = K` (unitary
  invariance `map_unitaryCoord_hermGaussian`, Sylvester inertia, `det` invariance);
* `sectorInvMoment_mulVec_eigen`: for every unit eigenvector `w` of `K`, `Sw = (w*Sw)w`, from
  the reflection `W = 1 - 2ww*`;
* `sectorInvMoment_eigen`: `S` maps every eigenvector of `K` to a multiple of itself (the
  hypothesis of `norm_le_of_eigen`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.RbarMoment

open MeasureTheory Matrix
open BlockBand.DeterminantScore.Sector BlockBand.DeterminantScore.ExactScore
open BlockBand.Angular.DetFactor
open BlockBand.Internal.Contracts.CoareaPalm
open scoped NNReal

variable {m : ℕ}

/-!
## Conjugation invariance
-/

/-- The matrix `1{N_-(K+G(x))=ℓ} det(K+G(x))² (K+G(x))⁻¹`. -/
def sectorInvMat (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (x : HermCoord m → ℝ) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun j k => sectorDetSqInv K ℓ j k x

theorem sectorInvMat_eq (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (x : HermCoord m → ℝ) :
    sectorInvMat K ℓ x = if InSector K ℓ x then
      (K + hermOfCoord x).det ^ 2 • (K + hermOfCoord x)⁻¹ else 0 := by
  ext j k
  unfold sectorInvMat sectorDetSqInv
  split_ifs <;> simp

theorem inv_unitary_conj (M : Matrix (Fin m) (Fin m) ℂ) {W : Matrix (Fin m) (Fin m) ℂ}
    (hW : Wᴴ * W = 1) : (Wᴴ * M * W)⁻¹ = Wᴴ * M⁻¹ * W := by
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.1 hW
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hW,
    Matrix.inv_eq_left_inv hW']
  simp only [Matrix.mul_assoc]

theorem sectorInvMat_unitaryCoord {K W : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian)
    (hW : Wᴴ * W = 1) (hKW : Wᴴ * K * W = K) (ℓ : ℕ) (x : HermCoord m → ℝ) :
    sectorInvMat K ℓ (unitaryCoord W x) = Wᴴ * sectorInvMat K ℓ x * W := by
  have hM : K + hermOfCoord (unitaryCoord W x) = Wᴴ * (K + hermOfCoord x) * W := by
    rw [hermOfCoord_unitaryCoord, Matrix.mul_add, Matrix.add_mul, hKW]
  have hH := hK.add (isHermitian_hermOfCoord x)
  rw [sectorInvMat_eq, sectorInvMat_eq]
  have hiff : InSector K ℓ (unitaryCoord W x) ↔ InSector K ℓ x := by
    unfold InSector; rw [hM, negativeCount_unitary_conj hH hW]
  by_cases hs : InSector K ℓ x
  · rw [ite_eq_left (hiff.2 hs), ite_eq_left hs, hM, det_unitary_conj _ hW, inv_unitary_conj _ hW,
      Matrix.mul_smul, Matrix.smul_mul]
  · rw [ite_eq_right (mt hiff.1 hs), ite_eq_right hs]
    simp

/-- **`S = W*SW`** for unitary `W` in the stabilizer of `K`. -/
theorem sectorInvMoment_unitary_conj (t : ℝ≥0) {K W : Matrix (Fin m) (Fin m) ℂ}
    (hK : K.IsHermitian) (hW : Wᴴ * W = 1) (hKW : Wᴴ * K * W = K) (ℓ : ℕ) :
    sectorInvMoment m t K ℓ = Wᴴ * sectorInvMoment m t K ℓ * W := by
  have hmap := map_unitaryCoord_hermGaussian t hW
  have hint : ∀ a b, Integrable (sectorDetSqInv K ℓ a b) (hermGaussian m t) :=
    integrable_sectorDetSqInv t hK ℓ
  ext j k
  have h1 : (∫ x, sectorDetSqInv K ℓ j k x ∂hermGaussian m t) =
      ∫ x, sectorDetSqInv K ℓ j k (unitaryCoord W x) ∂hermGaussian m t := by
    conv_lhs => rw [← hmap]
    rw [integral_map (continuous_unitaryCoord W).aemeasurable]
    rw [hmap]
    exact (hint j k).aestronglyMeasurable
  have h2 : ∀ x, sectorDetSqInv K ℓ j k (unitaryCoord W x) =
      ∑ b, ∑ a, Wᴴ j a * sectorDetSqInv K ℓ a b x * W b k := fun x => by
    have := congrFun (congrFun (sectorInvMat_unitaryCoord hK hW hKW ℓ x) j) k
    simp only [sectorInvMat, Matrix.of_apply, Matrix.mul_apply] at this
    rw [this]
    simp_rw [Finset.sum_mul]
  simp only [sectorInvMoment, Matrix.of_apply, Matrix.mul_apply]
  rw [h1]
  simp_rw [h2]
  rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ fun a _ =>
    ((hint a b).const_mul _).mul_const _)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_finsetSum _ (fun a _ => ((hint a b).const_mul _).mul_const _), Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_mul_const, integral_const_mul]

/-!
## Reflections in eigenvectors
-/

/-- The reflection `1 - 2ww*`. -/
def reflect (w : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  1 - (2 : ℂ) • vecMulVec w (star w)

theorem reflect_conjTranspose (w : Fin m → ℂ) : (reflect w)ᴴ = reflect w := by
  unfold reflect
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, conjTranspose_vecMulVec,
    star_star]
  simp

theorem reflect_mul_self {w : Fin m → ℂ} (hw : star w ⬝ᵥ w = 1) : reflect w * reflect w = 1 := by
  have hP : vecMulVec w (star w) * vecMulVec w (star w) = vecMulVec w (star w) := by
    rw [vecMulVec_mul_vecMulVec, hw, one_smul]
  unfold reflect
  simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    hP, smul_smul]
  module

theorem reflect_mulVec (w y : Fin m → ℂ) :
    reflect w *ᵥ y = y - (2 : ℂ) • ((star w ⬝ᵥ y) • w) := by
  unfold reflect
  rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem reflect_mulVec_self {w : Fin m → ℂ} (hw : star w ⬝ᵥ w = 1) : reflect w *ᵥ w = -w := by
  rw [reflect_mulVec, hw, one_smul]
  module

theorem reflect_comm {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) {w : Fin m → ℂ}
    {μ : ℝ} (hKw : K *ᵥ w = (μ : ℂ) • w) : K * reflect w = reflect w * K := by
  have h1 : K * vecMulVec w (star w) = (μ : ℂ) • vecMulVec w (star w) := by
    rw [mul_vecMulVec, hKw, smul_vecMulVec]
  have h2 : vecMulVec w (star w) * K = (μ : ℂ) • vecMulVec w (star w) := by
    have hs : star w ᵥ* K = (μ : ℂ) • star w := by
      have := star_mulVec K w
      rw [hK.eq, hKw, star_smul, Complex.star_def, Complex.conj_ofReal] at this
      exact this.symm
    rw [vecMulVec_mul, hs, vecMulVec_smul]
  unfold reflect
  rw [mul_sub, sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, h1, h2]

theorem reflect_conj {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) {w : Fin m → ℂ}
    (hw : star w ⬝ᵥ w = 1) {μ : ℝ} (hKw : K *ᵥ w = (μ : ℂ) • w) :
    (reflect w)ᴴ * K * reflect w = K := by
  rw [reflect_conjTranspose, Matrix.mul_assoc, reflect_comm hK hKw, ← Matrix.mul_assoc,
    reflect_mul_self hw, Matrix.one_mul]

/-- **`Sw = (w*Sw)w`** for every unit eigenvector `w` of `K`. -/
theorem sectorInvMoment_mulVec_eigen (t : ℝ≥0) {K : Matrix (Fin m) (Fin m) ℂ}
    (hK : K.IsHermitian) (ℓ : ℕ) {w : Fin m → ℂ} (hw : star w ⬝ᵥ w = 1) {μ : ℝ}
    (hKw : K *ᵥ w = (μ : ℂ) • w) :
    sectorInvMoment m t K ℓ *ᵥ w = (star w ⬝ᵥ (sectorInvMoment m t K ℓ *ᵥ w)) • w := by
  set S := sectorInvMoment m t K ℓ
  set R := reflect w
  have hRR : R * R = 1 := reflect_mul_self hw
  have hRu : Rᴴ * R = 1 := by rw [reflect_conjTranspose]; exact hRR
  have hS : S = Rᴴ * S * R := sectorInvMoment_unitary_conj t hK hRu (reflect_conj hK hw hKw) ℓ
  rw [reflect_conjTranspose] at hS
  have hcomm : R * S = S * R := by
    calc R * S = R * (R * S * R) := by rw [← hS]
      _ = (R * R) * S * R := by simp only [Matrix.mul_assoc]
      _ = S * R := by rw [hRR, Matrix.one_mul]
  have h : R *ᵥ (S *ᵥ w) = -(S *ᵥ w) := by
    rw [mulVec_mulVec, hcomm, ← mulVec_mulVec, reflect_mulVec_self hw, mulVec_neg]
  rw [reflect_mulVec] at h
  set c := star w ⬝ᵥ (S *ᵥ w)
  linear_combination (norm := module) (2⁻¹ : ℂ) • h

/-- Normalization of an eigenvector. -/
theorem eigen_of_unit {K X : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian)
    (h : ∀ (u : Fin m → ℂ) (μ : ℝ), star u ⬝ᵥ u = 1 → K *ᵥ u = (μ : ℂ) • u →
      X *ᵥ u = (star u ⬝ᵥ (X *ᵥ u)) • u) :
    ∀ (x : Fin m → ℂ) (μ : ℂ), K *ᵥ x = μ • x → ∃ c : ℂ, X *ᵥ x = c • x := by
  intro x μ hx
  by_cases hx0 : x = 0
  · exact ⟨0, by rw [hx0, mulVec_zero, smul_zero]⟩
  set s : ℝ := ∑ k, ‖x k‖ ^ 2
  have hs : 0 < s := by
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hx0
    exact lt_of_lt_of_le (by positivity : 0 < ‖x k‖ ^ 2)
      (Finset.single_le_sum (fun k _ => sq_nonneg ‖x k‖) (Finset.mem_univ k))
  set r : ℝ := Real.sqrt s
  have hr : 0 < r := Real.sqrt_pos.2 hs
  set u : Fin m → ℂ := ((r⁻¹ : ℝ) : ℂ) • x
  have hu : star u ⬝ᵥ u = 1 := by
    simp only [u, star_smul, Complex.star_def, Complex.conj_ofReal, smul_dotProduct,
      dotProduct_smul, star_dot_self_eq, smul_eq_mul]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    have : r⁻¹ * (r⁻¹ * s) = 1 := by
      rw [← mul_assoc, ← mul_inv, ← sq, Real.sq_sqrt hs.le, inv_mul_cancel₀ hs.ne']
    rw [this, Complex.ofReal_one]
  have hKu : K *ᵥ u = μ • u := by rw [mulVec_smul, hx, smul_comm]
  have hμ : μ = ((μ.re : ℝ) : ℂ) := by
    have h1 : star u ⬝ᵥ (K *ᵥ u) = μ := by rw [hKu, dotProduct_smul, hu, smul_eq_mul, mul_one]
    have him := hK.im_star_dotProduct_mulVec_self u
    rw [h1] at him
    exact Complex.ext (by simp) (by simpa using him)
  rw [hμ] at hKu
  have hXu := h u μ.re hu hKu
  set c := star u ⬝ᵥ (X *ᵥ u) with hc
  refine ⟨c, ?_⟩
  have hxu : x = ((r : ℝ) : ℂ) • u := by
    simp only [u, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one,
      one_smul]
  rw [hxu, mulVec_smul, hXu, smul_comm]

/-- **`S` maps every eigenvector of `K` to a multiple of itself.** -/
theorem sectorInvMoment_eigen (t : ℝ≥0) {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian)
    (ℓ : ℕ) : ∀ (x : Fin m → ℂ) (μ : ℂ), K *ᵥ x = μ • x →
      ∃ c : ℂ, sectorInvMoment m t K ℓ *ᵥ x = c • x :=
  eigen_of_unit hK fun _ _ hu hKu => sectorInvMoment_mulVec_eigen t hK ℓ hu hKu

end BlockBand.DeterminantScore.RbarMoment
