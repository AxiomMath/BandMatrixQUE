module

public import BlockBand.SourceProcess.FullSource.DeltaReduction
public import BlockBand.Transmission.PassiveLayer.BilMain
public import BlockBand.Transmission.PassiveLayer.TMWord

/-!
# The gradient of `x*K𝒢₁₁Ky` in the Gaussian coordinates

The functional `φ(𝒢) = x*(Kι₁ 𝒢 ι₁*K)y = x*K𝒢₁₁Ky` is `ℂ`-linear in `𝒢`. Along a line
`d𝒢 = -𝒢 dM 𝒢`, so `∂_iφ = -(x*Kι₁𝒢)(∂_iM)(𝒢ι₁*Ky)`: both gradient factors are weighted in the
displayed order. With the Hilbert–Schmidt contraction `layerDir_sum_le`,
`|∇φ|_v ≤ √(12/W) ‖Kι₁𝒢‖ ‖𝒢ι₁*K‖ ‖x‖‖y‖` (`grad_d_reg`, at the regularized input `X - iε`).

The right factor is bounded with no Schur hypothesis on the bond (`norm_gQ_le`): from `𝒢M = I`,
`𝒢ι₁*K = ι₁* + 𝒢R`, `R = ι₁*((w+E) - A) - ι₂*B*`, so `‖𝒢ι₁*K‖ ≤ 1 + ‖𝒢‖(|w| + |E| + ‖A‖ + ‖B‖)`
at every sample where the layer matrix is invertible. The left factor is bounded by
`‖Kι₁𝒢‖ ≤ ‖K𝒢₁₁‖ + ‖L‖` (`norm_pK_mul_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.PassiveLayer
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator NNReal

variable {W : ℕ}

/-- The right weight `ι₁*K`, `K = w - X`. -/
def qK (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) : Matrix (LayerSite W .oneBlockOnePort) (Fin W) ℂ :=
  (iota1 W)ᴴ * (w • 1 - X)

/-- `G ↦ x*(PGQ)y` as a continuous `ℂ`-linear map. -/
def dCLM (P : Matrix (Fin W) (LayerSite W .oneBlockOnePort) ℂ)
    (Q : Matrix (LayerSite W .oneBlockOnePort) (Fin W) ℂ) (x y : Fin W → ℂ) :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun G => bilinear x (P * G * Q) y
      map_add' := fun G H => by
        simp [bilinear, Matrix.mul_add, Matrix.add_mul, add_mulVec, dotProduct_add]
      map_smul' := fun c G => by
        simp [bilinear, Matrix.mul_smul, Matrix.smul_mul, smul_mulVec, dotProduct_smul] }

theorem dCLM_apply (P : Matrix (Fin W) (LayerSite W .oneBlockOnePort) ℂ)
    (Q : Matrix (LayerSite W .oneBlockOnePort) (Fin W) ℂ) (x y : Fin W → ℂ)
    (G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    dCLM P Q x y G = bilinear x (P * G * Q) y := rfl

/-- Derivative of `x*(P(M + tN)⁻¹Q)y` at `t = 0`, in contracted form. -/
theorem hasDerivAt_d_line (P : Matrix (Fin W) (LayerSite W .oneBlockOnePort) ℂ)
    (Q : Matrix (LayerSite W .oneBlockOnePort) (Fin W) ℂ) (x y : Fin W → ℂ)
    (M N : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ)
    (hM : IsUnit M) :
    HasDerivAt (fun t : ℝ => bilinear x (P * (M + (t : ℂ) • N)⁻¹ * Q) y)
      (-((star x ᵥ* (P * M⁻¹)) ⬝ᵥ (N *ᵥ ((M⁻¹ * Q) *ᵥ y)))) 0 := by
  have h := ((dCLM P Q x y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_inv_line M N hM)
  convert h using 1
  · funext t; rfl
  rw [ContinuousLinearMap.coe_restrictScalars', dCLM_apply, bilinear, Matrix.mul_neg,
    Matrix.neg_mul, neg_mulVec, dotProduct_neg]
  congr 1
  simp only [dotProduct_mulVec, vecMul_vecMul, Matrix.mul_assoc]

theorem contDiff_d_gReg (E : ℝ) {w : ℂ} (hw : 0 < w.im) (b : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε)
    (P : Matrix (Fin W) (LayerSite W .oneBlockOnePort) ℂ)
    (Q : Matrix (LayerSite W .oneBlockOnePort) (Fin W) ℂ) (x y : Fin W → ℂ) :
    ContDiff ℝ 1 fun ρ => bilinear x (P * gReg E w b X ε ρ * Q) y := by
  have hG : ContDiff ℝ 1 fun ρ => gReg E w b X ε ρ :=
    (contDiff_layerResolvent_reg E hw b hY hε).of_le le_top
  exact ((dCLM P Q x y).restrictScalars ℝ).contDiff.comp hG

/-- The directional derivatives of the regularized functional. -/
theorem fderiv_d_gReg (E : ℝ) {w : ℂ} (hw : 0 < w.im) (b : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε)
    (P : Matrix (Fin W) (LayerSite W .oneBlockOnePort) ℂ)
    (Q : Matrix (LayerSite W .oneBlockOnePort) (Fin W) ℂ) (x y : Fin W → ℂ)
    (ρ : CoordW W → ℝ) (i : CoordW W) :
    fderiv ℝ (fun ρ => bilinear x (P * gReg E w b X ε ρ * Q) y) ρ (Pi.single i 1) =
      -((star x ᵥ* (P * gReg E w b X ε ρ)) ⬝ᵥ
        (layerDir b (Pi.single i 1) *ᵥ ((gReg E w b X ε ρ * Q) *ᵥ y))) := by
  have hMu := (layer_isUnit_reg E hw hY hε (coordMap_hermitian b ρ)).2.1
  refine fderiv_apply_eq_of_line
    (((contDiff_d_gReg E hw b hY hε P Q x y).differentiable (by simp)) ρ) ?_
  have hline : (fun t : ℝ => bilinear x (P * gReg E w b X ε (ρ + t • Pi.single i 1) * Q) y) =
      fun t : ℝ => bilinear x (P * (layerMatrix .oneBlockOnePort E w (liftX (regX X ε))
        (coordMap W b ρ) + (t : ℂ) • layerDir b (Pi.single i 1))⁻¹ * Q) y := by
    funext t
    simp only [gReg, layerResolvent, layerMatrix_line]
  rw [hline]
  exact hasDerivAt_d_line P Q x y _ _ hMu

/-- **Gradient bound**: `|∇φ|_v ≤ √(12/W) ‖P𝒢‖ ‖𝒢Q‖ ‖x‖‖y‖` at the regularized input. -/
theorem grad_d_reg {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) {w : ℂ}
    (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) {ε : ℝ}
    (hε : 0 < ε) (P : Matrix (Fin W) (LayerSite W .oneBlockOnePort) ℂ)
    (Q : Matrix (LayerSite W .oneBlockOnePort) (Fin W) ℂ) (x y : Fin W → ℂ) (ρ : CoordW W → ℝ) :
    weightedGradientNorm (coordVar W b) (fun ρ => bilinear x (P * gReg E w b X ε ρ * Q) y) ρ ≤
      Real.sqrt (3 * (4 / W)) * (‖P * gReg E w b X ε ρ‖ * ‖gReg E w b X ε ρ * Q‖ *
        (vecNorm x * vecNorm y)) := by
  set G := gReg E w b X ε ρ
  have h := weightedGradientNorm_le (coordVar W b)
    (fun ρ => bilinear x (P * gReg E w b X ε ρ * Q) y) ρ (fun i => layerDir b (Pi.single i 1)) 0
    (star x ᵥ* (P * G)) ((G * Q) *ᵥ y) 0 0 0 0 (by positivity)
    (fun i => by rw [fderiv_d_gReg E hw b hY hε P Q x y ρ i]; simp [G])
    (fun a c => layerDir_sum_le hb0 hb hW a c)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  have hv0 : vecNorm (0 : LayerSite W .oneBlockOnePort → ℂ) = 0 := by simp [vecNorm]
  simp only [hv0, mul_zero, add_zero]
  have h1 : vecNorm (star x ᵥ* (P * G)) ≤ ‖P * G‖ * vecNorm x := by
    have := vecNorm_vecMul_le (star x) (P * G); rwa [vecNorm_star] at this
  have h2 : vecNorm ((G * Q) *ᵥ y) ≤ ‖G * Q‖ * vecNorm y := vecNorm_mulVec_le' _ _
  calc vecNorm (star x ᵥ* (P * G)) * vecNorm ((G * Q) *ᵥ y)
      ≤ (‖P * G‖ * vecNorm x) * (‖G * Q‖ * vecNorm y) :=
        mul_le_mul h1 h2 (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg _)
          (mul_nonneg (norm_nonneg _) (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg _))
    _ = _ := by ring

/-!
## The right factor `𝒢ι₁*K`
-/

/-- `R = ι₁*((w+E) - A) - ι₂*B*`. -/
def rightRem (E : ℝ) (w : ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (LayerSite W .oneBlockOnePort) (Fin W) ℂ :=
  (iota1 W)ᴴ * ((w + E) • (1 : Matrix (Fin W) (Fin W) ℂ) - ω.1 0) - (iota2 W)ᴴ * (ω.2 0 0)ᴴ

/-- `ι₁*K = Mι₁* + R` (the physical columns of the layer matrix). -/
theorem qK_eq (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    qK w X = layerMatrix .oneBlockOnePort E w (liftX X) ω * (iota1 W)ᴴ + rightRem E w ω := by
  ext s x
  rcases s with ⟨i, x'⟩ | ⟨i, x'⟩ <;> obtain rfl : i = 0 := Subsingleton.elim _ _
  · simp [qK, rightRem, layerMatrix, iota1, iota2, Matrix.mul_apply,
      Matrix.conjTranspose_apply, BlockBand.Internal.Contracts.Layers.blockDiag, liftX,
      Matrix.one_apply]
    split_ifs <;> ring
  · simp [qK, rightRem, layerMatrix, iota1, iota2, Matrix.mul_apply,
      Matrix.conjTranspose_apply, bondMatrix, liftX, Matrix.one_apply, LayerShape.incident]

theorem norm_rightRem_le (E : ℝ) (w : ℂ) (ω : LayerSample W .oneBlockOnePort) :
    ‖rightRem E w ω‖ ≤ ‖w‖ + |E| + ‖ω.1 0‖ + ‖ω.2 0 0‖ := by
  have h1 : ‖(iota1 W)ᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact norm_iota1_le
  have h2 : ‖(iota2 W)ᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact norm_iota2_le
  have hc : ‖(w + E) • (1 : Matrix (Fin W) (Fin W) ℂ) - ω.1 0‖ ≤ ‖w‖ + |E| + ‖ω.1 0‖ := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    rw [norm_smul]
    calc ‖w + E‖ * ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ (‖w‖ + |E|) * 1 := by
          gcongr
          · exact (norm_add_le _ _).trans (by simp)
          · exact BlockBand.Transmission.PassiveCovariance.norm_one_matrix_le
      _ = ‖w‖ + |E| := mul_one _
  have hB : ‖(ω.2 0 0)ᴴ‖ = ‖ω.2 0 0‖ := Matrix.l2_opNorm_conjTranspose _
  refine (norm_sub_le _ _).trans ?_
  have e1 := (Matrix.l2_opNorm_mul (iota1 W)ᴴ ((w + E) • (1 : Matrix (Fin W) (Fin W) ℂ) - ω.1 0))
  have e2 := (Matrix.l2_opNorm_mul (iota2 W)ᴴ (ω.2 0 0)ᴴ)
  rw [hB] at e2
  nlinarith [norm_nonneg ((w + E) • (1 : Matrix (Fin W) (Fin W) ℂ) - ω.1 0),
    norm_nonneg (ω.2 0 0), norm_nonneg (iota1 W)ᴴ, norm_nonneg (iota2 W)ᴴ]

/-- **`‖𝒢ι₁*K‖ ≤ 1 + ‖𝒢‖(|w| + |E| + ‖A‖ + ‖B‖)`** wherever the layer matrix is invertible. -/
theorem norm_gQ_le (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort)
    (hu : IsUnit (layerMatrix .oneBlockOnePort E w (liftX X) ω)) :
    ‖layerAt E w X ω * qK w X‖ ≤
      1 + ‖layerAt E w X ω‖ * (‖w‖ + |E| + ‖ω.1 0‖ + ‖ω.2 0 0‖) := by
  have hGM : layerAt E w X ω * layerMatrix .oneBlockOnePort E w (liftX X) ω = 1 :=
    Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hu)
  rw [qK_eq E w X ω, Matrix.mul_add, ← Matrix.mul_assoc, hGM, Matrix.one_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ((Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul_of_nonneg_left (norm_rightRem_le E w ω) (norm_nonneg _))))
  rw [Matrix.l2_opNorm_conjTranspose]; exact norm_iota1_le

/-- `K𝒢₁₁K = (Kι₁) 𝒢 (ι₁*K)`. -/
theorem kgk_eq (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    (w • 1 - X) * g11 E w X ω * (w • 1 - X) = pK w X * layerAt E w X ω * qK w X := by
  rw [g11_eq_iota, pK, qK]; simp only [Matrix.mul_assoc]

end BlockBand.SourceProcess.FullSource
