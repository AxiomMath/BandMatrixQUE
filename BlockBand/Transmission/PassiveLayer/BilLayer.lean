module

public import BlockBand.Transmission.PassiveLayer.BilDeriv
public import BlockBand.Transmission.PassiveLayer.RPlus

/-!
# The two bilinear entries of the passive bounds lemma as resolvent functionals

* `bilinear_uAt_eq`: `u*LL*v = psiMap (P_K*u) (P_K*v) 0 P₂ P₂ 𝒢`, `P_K = Kι₁`, `P₂ = ι₂*ι₂`.
* `bilinear_transportedFAt_eq`: if `R₊ = 𝒢₂₂`, `u*L(R₊ - c₀)L*v = psiMap … 1 P₂ (-c₀P₂) 𝒢`.
* `g22_eq_Rplus_of`, `isUnit_physBlock_reg`: `R₊ = 𝒢₂₂` at every sample of the
  ε-regularized layer with Hermitian `A` (Woodbury).
* Norms: `‖P₂‖ ≤ 1`, `‖P_K 𝒢‖ ≤ ‖K𝒢₁₁‖ + ‖L‖`, `‖xA‖ ≤ ‖A‖‖x‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator ComplexOrder NNReal

open BlockBand.Transmission

variable {W : ℕ}

/-- `R₊ = 𝒢₂₂` at a sample where `S` and `P = A - E - X` are invertible. -/
theorem g22_eq_Rplus_of {E : ℝ} {w : ℂ} (hw0 : w ≠ 0) {X : Matrix (Fin W) (Fin W) ℂ}
    {ω : LayerSample W .oneBlockOnePort} (hS : IsUnit (schurS E w X ω))
    (hP : IsUnit (BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1 - liftX X))
    (h : layerAt E w X ω = schurInv E w X ω) :
    g22 E w X ω = (w • 1 - freshSchur E X ω)⁻¹ := by
  set P := BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1 - liftX X
  have hg : g22 E w X ω = (w⁻¹ • 1 + (w⁻¹ ^ 2) • ((bondL ω)ᴴ * (schurS E w X ω)⁻¹ * bondL ω)).submatrix
      embedEquiv embedEquiv := by
    ext x y; simp [g22, h, schurInv, embedEquiv_coe, embed0]
  have hf : freshSchur E X ω = ((bondL ω)ᴴ * P⁻¹ * bondL ω).submatrix embedEquiv embedEquiv := by
    ext x y; simp [freshSchur, layerSchur, embedEquiv_coe, embed0, bondL, P, liftX]
  have hW' := woodbury P (bondL ω) hw0 hP hS
  have hsub : w • (1 : Matrix (Fin W) (Fin W) ℂ) -
      ((bondL ω)ᴴ * P⁻¹ * bondL ω).submatrix embedEquiv embedEquiv =
      (w • 1 - (bondL ω)ᴴ * P⁻¹ * bondL ω).submatrix embedEquiv embedEquiv := by
    ext x y
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply, Matrix.one_apply,
      embedEquiv.injective.eq_iff]
  rw [hg, hf, hsub, Matrix.inv_submatrix_equiv, inv_eq_right_inv hW']
  rfl

/-- `P = A - E - X_ε` is invertible for `ε > 0` and `A` Hermitian. -/
theorem isUnit_physBlock_reg (E : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) :
    IsUnit (BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1 - liftX (regX X ε)) := by
  have hH : (BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1).IsHermitian := by
    rw [blockDiag_one_eq]
    refine (liftX_isHermitian hA).sub ?_
    ext u v; simp [Matrix.conjTranspose_apply, Matrix.one_apply]; split_ifs <;> simp_all [eq_comm]
  refine (isUnit_and_norm_inv_le_of_coercive hε fun x => ?_).1
  rw [sub_mulVec, dotProduct_sub, Complex.sub_im, qf_im_eq_zero hH]
  linarith [qf_liftX_im_le_reg hY ε x]

/-- The row embedding `ι₁` (physical) and `ι₂` (port) of `Fin W` into the layer sites. -/
def iota1 (W : ℕ) : Matrix (Fin W) (LayerSite W .oneBlockOnePort) ℂ :=
  Matrix.of fun x z => if z = Sum.inl ((0 : Fin 1), x) then 1 else 0
def iota2 (W : ℕ) : Matrix (Fin W) (LayerSite W .oneBlockOnePort) ℂ :=
  Matrix.of fun x z => if z = Sum.inr ((0 : Fin 1), x) then 1 else 0

theorem g12_eq_iota (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    g12 E w X ω = iota1 W * layerAt E w X ω * (iota2 W)ᴴ := by
  ext x y
  simp [g12, iota1, iota2, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem g22_eq_iota (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    g22 E w X ω = iota2 W * layerAt E w X ω * (iota2 W)ᴴ := by
  ext x y
  simp [g22, iota2, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem bilinear_sandwich {m n : Type*} [Fintype m] [Fintype n] (u v : m → ℂ)
    (P : Matrix m n ℂ) (H : Matrix n n ℂ) :
    bilinear u (P * H * Pᴴ) v = star (Pᴴ *ᵥ u) ⬝ᵥ (H *ᵥ (Pᴴ *ᵥ v)) := by
  rw [bilinear, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec,
    conjTranspose_conjTranspose]

/-- `K ι₁`, `P₂ = ι₂*ι₂`. -/
def pK (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (LayerSite W .oneBlockOnePort) ℂ :=
  (w • 1 - X) * iota1 W
def pTwo (W : ℕ) : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  (iota2 W)ᴴ * iota2 W

theorem lAt_eq_iota (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    lAt E w X ω = pK w X * layerAt E w X ω * (iota2 W)ᴴ := by
  rw [lAt, g12_eq_iota, pK]; simp only [Matrix.mul_assoc]

/-- `u*LL*v = Ψ(𝒢)` with `θ = 0`, `Γ = P₂`. -/
theorem bilinear_uAt_eq (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) (u v : Fin W → ℂ) :
    bilinear u (uAt E w X ω) v = psiMap ((pK w X)ᴴ *ᵥ u) ((pK w X)ᴴ *ᵥ v) 0 (pTwo W) (pTwo W)
      (layerAt E w X ω) := by
  have h : uAt E w X ω = pK w X * (layerAt E w X ω * pTwo W * (layerAt E w X ω)ᴴ) * (pK w X)ᴴ := by
    rw [uAt, lAt_eq_iota, pTwo]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [h, bilinear_sandwich, psiMap, rMap, zero_smul, zero_add]

/-- `u*L(R₊ - c₀)L*v = Ψ(𝒢)` with `θ = 1`, `Γ = -c₀P₂`, given `R₊ = 𝒢₂₂`. -/
theorem bilinear_transportedFAt_eq (b E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) (u v : Fin W → ℂ)
    (hR : (w • 1 - freshSchur E X ω)⁻¹ = g22 E w X ω) :
    bilinear u (transportedFAt b E w X ω) v = psiMap ((pK w X)ᴴ *ᵥ u) ((pK w X)ᴴ *ᵥ v) 1
      (pTwo W) (-cZero b E • pTwo W) (layerAt E w X ω) := by
  have h : transportedFAt b E w X ω = pK w X * (layerAt E w X ω *
      rMap 1 (pTwo W) (-cZero b E • pTwo W) (layerAt E w X ω) * (layerAt E w X ω)ᴴ) *
        (pK w X)ᴴ := by
    rw [transportedFAt, hR, g22_eq_iota, lAt_eq_iota, rMap, pTwo]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.mul_assoc, neg_smul, Matrix.mul_neg, Matrix.neg_mul, sub_eq_add_neg]
  rw [h, bilinear_sandwich, psiMap]

theorem vecNorm_vecMul_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (x : m → ℂ) (A : Matrix m n ℂ) : vecNorm (x ᵥ* A) ≤ ‖A‖ * vecNorm x := by
  have h : x ᵥ* A = star (Aᴴ *ᵥ star x) := by
    rw [star_mulVec, star_star, conjTranspose_conjTranspose]
  rw [h, vecNorm_star, ← Matrix.l2_opNorm_conjTranspose A]
  have := vecNorm_mulVec_le' Aᴴ (star x)
  rwa [vecNorm_star] at this

theorem norm_pTwo_le : ‖pTwo W‖ ≤ 1 := by
  have h : pTwo W = Matrix.diagonal fun z : LayerSite W .oneBlockOnePort =>
      if ∃ x, z = Sum.inr ((0 : Fin 1), x) then (1 : ℂ) else 0 := by
    ext z z'
    rcases z with ⟨i, x⟩ | ⟨i, x⟩ <;> rcases z' with ⟨i', x'⟩ | ⟨i', x'⟩ <;>
      simp [pTwo, iota2, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
        Subsingleton.elim i 0, Subsingleton.elim i' 0, eq_comm]
  rw [h, Matrix.l2_opNorm_diagonal]
  refine pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun z => ?_
  split_ifs <;> simp

/-- Column splitting: `‖M‖ ≤ ‖M_left‖ + ‖M_right‖`. -/
theorem norm_le_cols {m n n' : Type*} [Fintype m] [Fintype n] [Fintype n'] [DecidableEq m]
    [DecidableEq n] [DecidableEq n'] (M : Matrix m (n ⊕ n') ℂ) :
    ‖M‖ ≤ ‖M.submatrix id Sum.inl‖ + ‖M.submatrix id Sum.inr‖ := by
  refine opNorm_le_of_vec' _ (by positivity) fun x => ?_
  have hx : M *ᵥ x = M.submatrix id Sum.inl *ᵥ (x ∘ Sum.inl) +
      M.submatrix id Sum.inr *ᵥ (x ∘ Sum.inr) := by
    ext i; simp [mulVec, dotProduct, Fintype.sum_sum_type]
  rw [hx]
  refine (vecNorm_add _ _).trans ?_
  have h1 := (vecNorm_mulVec_le' (M.submatrix id Sum.inl) (x ∘ Sum.inl)).trans
    (mul_le_mul_of_nonneg_left (vecNorm_comp_le x Sum.inl_injective) (norm_nonneg _))
  have h2 := (vecNorm_mulVec_le' (M.submatrix id Sum.inr) (x ∘ Sum.inr)).trans
    (mul_le_mul_of_nonneg_left (vecNorm_comp_le x Sum.inr_injective) (norm_nonneg _))
  linarith

/-- `‖K ι₁ 𝒢‖ ≤ ‖K𝒢₁₁‖ + ‖L‖`. -/
theorem norm_pK_mul_le (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    ‖pK w X * layerAt E w X ω‖ ≤ ‖kG11 E w X ω‖ + ‖lAt E w X ω‖ := by
  refine (norm_le_cols _).trans (add_le_add ?_ ?_)
  · have : (pK w X * layerAt E w X ω).submatrix id Sum.inl =
        (kG11 E w X ω).submatrix id Prod.snd := by
      ext x z
      obtain ⟨i, y⟩ := z
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp [pK, kG11, g11, iota1, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type]
    rw [this]; exact norm_submatrix_le _ Function.injective_id prodSnd_injective
  · have : (pK w X * layerAt E w X ω).submatrix id Sum.inr =
        (lAt E w X ω).submatrix id Prod.snd := by
      ext x z
      obtain ⟨i, y⟩ := z
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp [pK, lAt, g12, iota1, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type]
    rw [this]; exact norm_submatrix_le _ Function.injective_id prodSnd_injective

end BlockBand.Transmission.PassiveLayer
