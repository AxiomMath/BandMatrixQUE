module

public import BlockBand.Transmission.PassiveLayer.BilCoord

/-!
# ε-regularized passive input: invertibility everywhere and smoothness in the coordinates

* `regX X ε = X - iε` is passive with `-Im X_ε = Y + ε` (`passiveY_regX`, `regX_posSemidef`).
* `schurS_coercive_reg`: for `ε > 0` and `A` Hermitian, `Im x*Sx ≥ ε‖x‖²` for **every** bond.
  Hence (`layer_isUnit_reg`) the layer matrix is invertible at every sample with Hermitian `A`
  (every `coordMap` sample), with the explicit Schur inverse.
* `contDiff_layerResolvent_reg`: `ρ ↦ 𝒢(X_ε)(coordMap ρ)` is `C^∞` (ring inverse at units and the
  affine `ρ ↦ M(ρ)`, `layerDirL`).
* `entryCLM`, `HasDerivAt.matrix_entry`, `ContDiff.matrix_entry`: matrix entries.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

open BlockBand.Transmission

section Entry
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The entry `(i, j)` as a continuous ℂ-linear functional on `Matrix n n ℂ` (operator norm). -/
def entryCLM (i j : n) : Matrix n n ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [DecidableEq n] in
theorem entryCLM_apply (i j : n) (M : Matrix n n ℂ) : entryCLM i j M = M i j := rfl

theorem HasDerivAt.matrix_entry {G : ℂ → Matrix n n ℂ} {G' : Matrix n n ℂ} {s : ℂ}
    (h : HasDerivAt G G' s) (i j : n) : HasDerivAt (fun s => G s i j) (G' i j) s :=
  (entryCLM i j).hasFDerivAt.comp_hasDerivAt s h

theorem ContDiff.matrix_entry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : E → Matrix n n ℂ} {k : ℕ∞} (h : ContDiff ℝ k G) (i j : n) :
    ContDiff ℝ k fun x => G x i j :=
  ((entryCLM i j).restrictScalars ℝ).contDiff.comp h

end Entry

variable {W : ℕ}

/-- The regularized input `X_ε = X - iε`. -/
def regX (X : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ) : Matrix (Fin W) (Fin W) ℂ :=
  X - ((ε : ℂ) * Complex.I) • 1

theorem passiveY_regX (X : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ) :
    passiveY (regX X ε) = passiveY X + (ε : ℂ) • 1 := by
  ext u v
  by_cases h : u = v
  · subst h
    simp [regX, passiveY, matrixImaginaryPart, Matrix.conjTranspose_apply]
    ring_nf; rw [Complex.I_sq]; ring
  · simp [regX, passiveY, matrixImaginaryPart, Matrix.conjTranspose_apply, h]

theorem regX_posSemidef {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) {ε : ℝ}
    (hε : 0 ≤ ε) : (passiveY (regX X ε)).PosSemidef := by
  rw [passiveY_regX]
  exact hY.add (Matrix.PosSemidef.one.smul (by exact_mod_cast hε))

theorem qf_liftX_im_le_reg {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) (ε : ℝ)
    (x : Fin 1 × Fin W → ℂ) : (star x ⬝ᵥ (liftX (regX X ε) *ᵥ x)).im ≤ -(ε * vecNorm x ^ 2) := by
  have h := quad_im (liftX (regX X ε)) x
  rw [matrixImaginaryPart_liftX] at h
  have hp := Complex.nonneg_iff.mp ((liftX_posSemidef hY).dotProduct_mulVec_nonneg x)
  have hneg : liftX (matrixImaginaryPart (regX X ε)) =
      -liftX (passiveY X) - (ε : ℂ) • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) := by
    have : matrixImaginaryPart (regX X ε) = -passiveY (regX X ε) := by simp [passiveY]
    rw [this, passiveY_regX]
    ext u v; simp [liftX, Matrix.one_apply, Prod.ext_iff, Subsingleton.elim u.1 v.1]; ring
  rw [hneg, sub_mulVec, neg_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_neg,
    dotProduct_smul, star_self_eq] at h
  have := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero] at this
  linarith [hp.1]

/-- With absorption `ε > 0`, the port Schur complement is coercive for **every** bond `B`. -/
theorem schurS_coercive_reg (E : ℝ) {w : ℂ} (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) (ε : ℝ) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (x : Fin 1 × Fin W → ℂ) :
    ε * vecNorm x ^ 2 ≤ (star x ⬝ᵥ (schurS E w (regX X ε) ω *ᵥ x)).im := by
  have hH : (BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1).IsHermitian := by
    rw [blockDiag_one_eq]
    refine (liftX_isHermitian hA).sub ?_
    ext u v; simp [Matrix.conjTranspose_apply, Matrix.one_apply]; split_ifs <;> simp_all [eq_comm]
  have hexp : (star x ⬝ᵥ (schurS E w (regX X ε) ω *ᵥ x)).im =
      (star x ⬝ᵥ ((BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1) *ᵥ x)).im -
      (star x ⬝ᵥ (liftX (regX X ε) *ᵥ x)).im -
        (w⁻¹ * ((vecNorm ((bondL ω)ᴴ *ᵥ x) ^ 2 : ℝ) : ℂ)).im := by
    rw [schurS, sub_mulVec, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_sub,
      dotProduct_smul, qf_conjTranspose_mul, smul_eq_mul]
    simp only [Complex.sub_im]
  rw [hexp, qf_im_eq_zero hH]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
    Complex.inv_im]
  have hq := qf_liftX_im_le_reg hY ε x
  have hns : 0 < Complex.normSq w := Complex.normSq_pos.mpr (fun h => by simp [h] at hw)
  have : 0 ≤ w.im / Complex.normSq w * vecNorm ((bondL ω)ᴴ *ᵥ x) ^ 2 := by positivity
  have e : -(-w.im / Complex.normSq w * vecNorm ((bondL ω)ᴴ *ᵥ x) ^ 2) =
      w.im / Complex.normSq w * vecNorm ((bondL ω)ᴴ *ᵥ x) ^ 2 := by ring
  linarith

/-- With `ε > 0` and `A` Hermitian the layer matrix is invertible for every bond. -/
theorem layer_isUnit_reg (E : ℝ) {w : ℂ} (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) :
    IsUnit (schurS E w (regX X ε) ω) ∧
      IsUnit (layerMatrix .oneBlockOnePort E w (liftX (regX X ε)) ω) ∧
      layerResolvent .oneBlockOnePort E w (liftX (regX X ε)) ω = schurInv E w (regX X ε) ω := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hSu := (isUnit_and_norm_inv_le_of_coercive hε (schurS_coercive_reg E hw hY ε hA)).1
  have hmul : layerMatrix .oneBlockOnePort E w (liftX (regX X ε)) ω * schurInv E w (regX X ε) ω = 1 := by
    rw [layerMatrix_eq]; exact fromBlocks_mul_schurInv _ _ hw0 hSu
  exact ⟨hSu, (isUnit_iff_isUnit_det _).mpr (IsUnit.of_mul_eq_one _ (by rw [← det_mul, hmul, det_one])),
    inv_eq_right_inv hmul⟩

/-- `layerDir b` as an ℝ-linear map. -/
def layerDirL (W : ℕ) (b : ℝ) :
    (CoordW W → ℝ) →ₗ[ℝ] Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ where
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

theorem contDiff_layerMatrix_coord (E : ℝ) (w : ℂ) (b : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    ContDiff ℝ ⊤ fun ρ => layerMatrix .oneBlockOnePort E w (liftX X) (coordMap W b ρ) := by
  have h : (fun ρ => layerMatrix .oneBlockOnePort E w (liftX X) (coordMap W b ρ)) =
      fun ρ => layerMatrix .oneBlockOnePort E w (liftX X) (coordMap W b 0) +
        LinearMap.toContinuousLinearMap (layerDirL W b) ρ := by
    funext ρ
    have := layerMatrix_line E w b X 0 ρ 1
    simp only [one_smul, zero_add, Complex.ofReal_one] at this
    exact this
  rw [h]
  exact contDiff_const.add (ContinuousLinearMap.contDiff _)

theorem coordMap_hermitian (b : ℝ) (ρ : CoordW W → ℝ) : ((coordMap W b ρ).1 0).IsHermitian :=
  gueRaw_isHermitian' _ _

theorem contDiff_layerResolvent_reg (E : ℝ) {w : ℂ} (hw : 0 < w.im) (b : ℝ)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ⊤ fun ρ => layerResolvent .oneBlockOnePort E w (liftX (regX X ε)) (coordMap W b ρ) := by
  have hM := contDiff_layerMatrix_coord E w b (regX X ε)
  refine contDiff_iff_contDiffAt.mpr fun ρ => ?_
  have hu := (layer_isUnit_reg E hw hY hε (coordMap_hermitian b ρ)).2.1
  have hinv : ContDiffAt ℝ ⊤ (fun M : Matrix (LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort) ℂ => M⁻¹)
      (layerMatrix .oneBlockOnePort E w (liftX (regX X ε)) (coordMap W b ρ)) := by
    have h := (contDiffAt_ringInverse ℂ (n := ⊤) hu.unit).restrict_scalars ℝ
    have he : (fun M : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ =>
        M⁻¹) = Ring.inverse := by funext M; exact Matrix.nonsing_inv_eq_ringInverse M
    rw [he]; exact h
  exact hinv.comp ρ hM.contDiffAt

end BlockBand.Transmission.PassiveLayer
