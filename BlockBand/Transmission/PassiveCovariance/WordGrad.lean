module

public import BlockBand.Transmission.PassiveCovariance.WordCalc
public import BlockBand.Transmission.PassiveCovariance.WordCoord
public import BlockBand.Transmission.PassiveCovariance.LayerSmooth
public import BlockBand.Transmission.PassiveCovariance.SchwingerDyson

/-!
# The `W^{-1/2}` gradient of a bilinear form of a dressed word

For `f(ρ) = a*·w(𝒢(ρ))·c` (`wordForm`, `w` a dressed word of length `m`, insertions
`‖D_j‖ ≤ K_d`):

* `contDiff_wordForm`: `f` is `C¹`;
* `wordForm_fderiv`: `∂_i f = -Σ_{j<m} x_j·(∂_iM) y_j` with `‖x_j‖‖y_j‖ ≤ K_d^{m+1}B^{m+1}‖a‖‖c‖`,
  `B = ‖𝒢‖ + ‖K̂𝒢‖` at `ρ`;
* `wordForm_gradSq_le`: `Σ_i v_i |∂_i f|² ≤ m²(4/W)(K_d^{m+1}B^{m+1})²‖a‖²‖c‖²`
  (`PassiveLayer.layerDir_sum_le`, Cauchy–Schwarz over the `m` letters);
* `wordForm_partial_le`: `|∂_i f| ≤ m K_d^{m+1}B^{m+1}‖∂_iM‖‖a‖‖c‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped Matrix.Norms.L2Operator ComplexOrder NNReal

variable {W : ℕ}

/-- `layerDir b` as an ℝ-linear map (as `PassiveLayer.layerDirL`). -/
def layerDirL (W : ℕ) (b : ℝ) : (CoordW W → ℝ) →ₗ[ℝ] LayerMat W where
  toFun := layerDir b
  map_add' e e' := by
    have h := layerMatrix_line 0 1 b 0 e e' 1
    have h0 := layerMatrix_line 0 1 b 0 0 (e + e') 1
    have h1 := layerMatrix_line 0 1 b 0 0 e 1
    simp only [one_smul, zero_add, Complex.ofReal_one] at h h0 h1
    rw [h1, add_assoc] at h
    rw [h0] at h
    exact (add_left_cancel h)
  map_smul' c e := by
    have h0 := layerMatrix_line 0 1 b 0 0 (c • e) 1
    have h1 := layerMatrix_line 0 1 b 0 0 e c
    simp only [one_smul, zero_add, Complex.ofReal_one] at h0 h1
    rw [h0] at h1
    have := add_left_cancel h1
    rw [this, RingHom.id_apply]
    rfl

theorem coordMap_hermitian (b : ℝ) (ρ : CoordW W → ℝ) : ((coordMap W b ρ).1 0).IsHermitian :=
  gueRaw_isHermitian' _ _

/-- The layer resolvent at `z = z_∂` in the Gaussian coordinates. -/
abbrev gCoord (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ρ : CoordW W → ℝ) : LayerMat W :=
  gRes b E X (coordMap W b ρ)

section Strict
variable {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hη : 0 < etaZ b E) (hY : (passiveY X).PosDef)
include hη hY

theorem isUnit_coord (ρ : CoordW W → ℝ) :
    IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E) (liftX X) (coordMap W b ρ)) :=
  isUnit_layerMatrix_strict hη hY _ (coordMap_hermitian b ρ)

theorem contDiff_gCoord : ContDiff ℝ ⊤ (gCoord b E X) := by
  have hM : ContDiff ℝ ⊤ fun ρ => layerMatrix .oneBlockOnePort E (boundaryZ b E) (liftX X)
      (coordMap W b ρ) := by
    have h : (fun ρ => layerMatrix .oneBlockOnePort E (boundaryZ b E) (liftX X) (coordMap W b ρ)) =
        fun ρ => layerMatrix .oneBlockOnePort E (boundaryZ b E) (liftX X) (coordMap W b 0) +
          LinearMap.toContinuousLinearMap (layerDirL W b) ρ := by
      funext ρ
      have := layerMatrix_line E (boundaryZ b E) b X 0 ρ 1
      simp only [one_smul, zero_add, Complex.ofReal_one] at this
      exact this
    rw [h]
    exact contDiff_const.add (ContinuousLinearMap.contDiff _)
  refine contDiff_iff_contDiffAt.mpr fun ρ => ?_
  have hu := isUnit_coord hη hY ρ
  have hinv : ContDiffAt ℝ ⊤ (fun M : LayerMat W => M⁻¹)
      (layerMatrix .oneBlockOnePort E (boundaryZ b E) (liftX X) (coordMap W b ρ)) := by
    have h := (contDiffAt_ringInverse ℂ (n := ⊤) hu.unit).restrict_scalars ℝ
    have he : (fun M : LayerMat W => M⁻¹) = Ring.inverse := by
      funext M; exact Matrix.nonsing_inv_eq_ringInverse M
    rw [he]; exact h
  exact hinv.comp ρ hM.contDiffAt

end Strict

section Generic
variable {n : Type} [Fintype n] [DecidableEq n]

theorem contDiff_wordVal {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (Kh : Matrix n n ℂ)
    {G : V → Matrix n n ℂ} (hG : ContDiff ℝ 1 G) :
    ∀ {ℓ : ℕ} (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → Matrix n n ℂ),
      ContDiff ℝ 1 fun x => wordVal Kh (G x) wd D := by
  have hS : ∀ {F : V → Matrix n n ℂ}, ContDiff ℝ 1 F → ContDiff ℝ 1 fun x => (F x)ᴴ := fun hF =>
    (starL' ℝ : Matrix n n ℂ ≃L[ℝ] _).contDiff.comp hF
  have hL : ∀ k : Fin 4, ContDiff ℝ 1 fun x => wLetter Kh (G x) k := by
    intro k
    fin_cases k
    · exact hG
    · exact contDiff_const.mul hG
    · exact hS hG
    · exact hS (contDiff_const.mul hG)
  intro ℓ
  induction ℓ with
  | zero => intro wd D; simp only [wordVal_zero]; exact contDiff_const
  | succ ℓ ih =>
    intro wd D
    simp only [wordVal_succ]
    exact (contDiff_const.mul (hL _)).mul (ih _ _)

/-- `H ↦ a*Hc` as a continuous ℝ-linear map. -/
def formL (a c : n → ℂ) : Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun H => star a ⬝ᵥ (H *ᵥ c)
      map_add' := fun H H' => by simp [add_mulVec, dotProduct_add]
      map_smul' := fun r H => by simp [smul_mulVec, dotProduct_smul] }

omit [DecidableEq n] in
theorem formL_apply (a c : n → ℂ) (H : Matrix n n ℂ) : formL a c H = star a ⬝ᵥ (H *ᵥ c) := rfl

/-- The bilinear form `a*·w(G)·c` of a dressed word. -/
def wordForm (Kh : Matrix n n ℂ) (a c : n → ℂ) {ℓ : ℕ} (wd : Fin ℓ → Fin 4)
    (D : Fin (ℓ + 1) → Matrix n n ℂ) (G : Matrix n n ℂ) : ℂ :=
  star a ⬝ᵥ (wordVal Kh G wd D *ᵥ c)

theorem vecNorm_star_vecMul_le (a : n → ℂ) (A : Matrix n n ℂ) :
    vecNorm (star a ᵥ* A) ≤ ‖A‖ * vecNorm a := by
  have e : star a ᵥ* A = star (Aᴴ *ᵥ a) := by rw [star_mulVec, conjTranspose_conjTranspose]
  rw [e, vecNorm_star, ← Matrix.l2_opNorm_conjTranspose A]
  exact vecNorm_mulVec_le _ _

theorem norm_dot_le (x y : n → ℂ) (N : Matrix n n ℂ) :
    ‖x ⬝ᵥ (N *ᵥ y)‖ ≤ vecNorm x * ‖N‖ * vecNorm y := by
  have h := norm_bilinear_le (star x) N y
  rwa [bilinear, star_star, vecNorm_star] at h

end Generic

/-- The directional derivative is the line derivative (as `PassiveLayer.fderiv_apply_eq_of_line`). -/
theorem fderiv_apply_eq_of_line' {ι : Type} [Fintype ι] {f : (ι → ℝ) → ℂ} {ρ e : ι → ℝ}
    (hf : DifferentiableAt ℝ f ρ) {D : ℂ} (h : HasDerivAt (fun t : ℝ => f (ρ + t • e)) D 0) :
    fderiv ℝ f ρ e = D := by
  have hl : HasDerivAt (fun t : ℝ => ρ + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add ρ
  have h2 : HasDerivAt (fun t : ℝ => f (ρ + t • e)) (fderiv ℝ f ρ e) 0 :=
    hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact h2.unique h

section Strict2
variable {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hη : 0 < etaZ b E) (hY : (passiveY X).PosDef)
include hη hY

theorem contDiff_wordForm (Kh : LayerMat W) (a c : LayerSite W .oneBlockOnePort → ℂ) {ℓ : ℕ}
    (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W) :
    ContDiff ℝ 1 fun ρ => wordForm Kh a c wd D (gCoord b E X ρ) :=
  (formL a c).contDiff.comp (contDiff_wordVal Kh ((contDiff_gCoord hη hY).of_le le_top) wd D)

/-- **The coordinate derivatives of a dressed bilinear form**, in contracted form. -/
theorem wordForm_fderiv (Kh : LayerMat W) (a c : LayerSite W .oneBlockOnePort → ℂ) {Kd : ℝ}
    (hKd : 0 ≤ Kd) {ℓ : ℕ} (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W)
    (hD : ∀ j, ‖D j‖ ≤ Kd) (ρ : CoordW W → ℝ) :
    ∃ x y : Fin ℓ → LayerSite W .oneBlockOnePort → ℂ,
      (∀ j, vecNorm (x j) * vecNorm (y j) ≤
        Kd ^ (ℓ + 1) * wBound Kh (gCoord b E X ρ) ^ (ℓ + 1) * (vecNorm a * vecNorm c)) ∧
      ∀ i, fderiv ℝ (fun ρ => wordForm Kh a c wd D (gCoord b E X ρ)) ρ (Pi.single i 1) =
        -∑ j, x j ⬝ᵥ (layerDir b (Pi.single i 1) *ᵥ y j) := by
  set M := layerMatrix .oneBlockOnePort E (boundaryZ b E) (liftX X) (coordMap W b ρ)
  have hM : IsUnit M := isUnit_coord hη hY ρ
  obtain ⟨α, γ, hb, hd⟩ := word_line Kh M hM hKd wd D hD
  have hMinv : M⁻¹ = gCoord b E X ρ := rfl
  refine ⟨fun j => star a ᵥ* α j, fun j => γ j *ᵥ c, fun j => ?_, fun i => ?_⟩
  · have h1 := vecNorm_star_vecMul_le a (α j)
    have h2 := vecNorm_mulVec_le (γ j) c
    rw [← hMinv]
    calc vecNorm (star a ᵥ* α j) * vecNorm (γ j *ᵥ c)
        ≤ (‖α j‖ * vecNorm a) * (‖γ j‖ * vecNorm c) :=
          mul_le_mul h1 h2 (vecNorm_nonneg _) (mul_nonneg (norm_nonneg _) (vecNorm_nonneg _))
      _ = (‖α j‖ * ‖γ j‖) * (vecNorm a * vecNorm c) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hb j) (mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _))
  · refine fderiv_apply_eq_of_line'
      (((contDiff_wordForm hη hY Kh a c wd D).differentiable (by simp)) ρ) ?_
    have hline : (fun t : ℝ => wordForm Kh a c wd D (gCoord b E X (ρ + t • Pi.single i 1))) =
        fun t : ℝ => formL a c (wordVal Kh ((M + (t : ℂ) • layerDir b (Pi.single i 1))⁻¹) wd D) := by
      funext t
      simp only [gCoord, gRes, layerResolvent, wordForm, formL_apply]
      rw [show (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) = liftX X from rfl,
        layerMatrix_line]
    rw [hline]
    have h := (formL a c).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (hd _ (layerDir_isHermitian b (Pi.single i 1)))
    refine h.congr_deriv ?_
    rw [formL_apply, neg_mulVec, dotProduct_neg, sum_mulVec, dotProduct_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]

/-- **Gradient bound**: `Σ_i v_i |∂_i f|² ≤ m²(4/W)(K_d^{m+1}B^{m+1})²‖a‖²‖c‖²`. -/
theorem wordForm_gradSq_le (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) (Kh : LayerMat W)
    (a c : LayerSite W .oneBlockOnePort → ℂ) {Kd : ℝ} (hKd : 0 ≤ Kd) {ℓ : ℕ}
    (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W) (hD : ∀ j, ‖D j‖ ≤ Kd)
    (ρ : CoordW W → ℝ) :
    ∑ i, (coordVar W b i : ℝ) *
        ‖fderiv ℝ (fun ρ => wordForm Kh a c wd D (gCoord b E X ρ)) ρ (Pi.single i 1)‖ ^ 2 ≤
      (ℓ : ℝ) ^ 2 * (4 / W) * (Kd ^ (ℓ + 1) * wBound Kh (gCoord b E X ρ) ^ (ℓ + 1)) ^ 2 *
        (vecNorm a ^ 2 * vecNorm c ^ 2) := by
  obtain ⟨x, y, hxy, hf⟩ := wordForm_fderiv hη hY Kh a c hKd wd D hD ρ
  set Q := Kd ^ (ℓ + 1) * wBound Kh (gCoord b E X ρ) ^ (ℓ + 1) * (vecNorm a * vecNorm c)
  have hpt : ∀ i, (coordVar W b i : ℝ) *
      ‖fderiv ℝ (fun ρ => wordForm Kh a c wd D (gCoord b E X ρ)) ρ (Pi.single i 1)‖ ^ 2 ≤
      (ℓ : ℝ) * ∑ j, (coordVar W b i : ℝ) * ‖x j ⬝ᵥ (layerDir b (Pi.single i 1) *ᵥ y j)‖ ^ 2 := by
    intro i
    rw [hf i, norm_neg]
    have h1 := norm_sum_le Finset.univ fun j => x j ⬝ᵥ (layerDir b (Pi.single i 1) *ᵥ y j)
    have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun j => ‖x j ⬝ᵥ (layerDir b (Pi.single i 1) *ᵥ y j)‖)
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    have hv := (coordVar W b i).2
    have h3 : ‖∑ j, x j ⬝ᵥ (layerDir b (Pi.single i 1) *ᵥ y j)‖ ^ 2 ≤
        (ℓ : ℝ) * ∑ j, ‖x j ⬝ᵥ (layerDir b (Pi.single i 1) *ᵥ y j)‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
    rw [← Finset.mul_sum]
    nlinarith
  calc _ ≤ ∑ i, (ℓ : ℝ) * ∑ j, (coordVar W b i : ℝ) *
        ‖x j ⬝ᵥ (layerDir b (Pi.single i 1) *ᵥ y j)‖ ^ 2 := Finset.sum_le_sum fun i _ => hpt i
    _ = (ℓ : ℝ) * ∑ j, ∑ i, (coordVar W b i : ℝ) *
        ‖x j ⬝ᵥ (layerDir b (Pi.single i 1) *ᵥ y j)‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (ℓ : ℝ) * ∑ _j : Fin ℓ, 4 / W * Q ^ 2 := by
        gcongr with j
        refine (layerDir_sum_le hb0 hb hW (x j) (y j)).trans ?_
        have := hxy j
        have h0 : 0 ≤ vecNorm (x j) * vecNorm (y j) := mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)
        have : (vecNorm (x j) * vecNorm (y j)) ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ h0 this 2
        have hW' : (0 : ℝ) ≤ 4 / W := by positivity
        nlinarith
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Q]
        ring

/-- **Pointwise partial bound**: `|∂_i f| ≤ m K_d^{m+1}B^{m+1}‖∂_iM‖‖a‖‖c‖`. -/
theorem wordForm_partial_le (Kh : LayerMat W) (a c : LayerSite W .oneBlockOnePort → ℂ) {Kd : ℝ}
    (hKd : 0 ≤ Kd) {ℓ : ℕ} (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W)
    (hD : ∀ j, ‖D j‖ ≤ Kd) (ρ : CoordW W → ℝ) (i : CoordW W) :
    ‖fderiv ℝ (fun ρ => wordForm Kh a c wd D (gCoord b E X ρ)) ρ (Pi.single i 1)‖ ≤
      ℓ * (Kd ^ (ℓ + 1) * wBound Kh (gCoord b E X ρ) ^ (ℓ + 1) * (vecNorm a * vecNorm c)) *
        ‖layerDir b (Pi.single i 1)‖ := by
  obtain ⟨x, y, hxy, hf⟩ := wordForm_fderiv hη hY Kh a c hKd wd D hD ρ
  rw [hf i, norm_neg]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j, ‖x j ⬝ᵥ (layerDir b (Pi.single i 1) *ᵥ y j)‖
      ≤ ∑ _j : Fin ℓ, Kd ^ (ℓ + 1) * wBound Kh (gCoord b E X ρ) ^ (ℓ + 1) *
          (vecNorm a * vecNorm c) * ‖layerDir b (Pi.single i 1)‖ := by
        refine Finset.sum_le_sum fun j _ => (norm_dot_le _ _ _).trans ?_
        calc vecNorm (x j) * ‖layerDir b (Pi.single i 1)‖ * vecNorm (y j)
            = vecNorm (x j) * vecNorm (y j) * ‖layerDir b (Pi.single i 1)‖ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (hxy j) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Strict2

end BlockBand.Transmission.PassiveCovariance
