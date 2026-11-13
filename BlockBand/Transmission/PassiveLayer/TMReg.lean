module

public import BlockBand.Transmission.PassiveLayer.TMDeriv
public import BlockBand.Transmission.PassiveLayer.BilAux

/-!
# The regularized layer resolvent is bounded, smooth, with `d𝒢 = -𝒢 (dM) 𝒢`

For `ε > 0`, `Im w > 0` and passive `X`, the regularized input `X_ε = X - iε` (`regX`) gives
the resolvent `gReg E w b X ε ρ = 𝒢(X_ε)(coordMap ρ)` (`BilGrad`) in the Gaussian coordinates.

* `layer_coercive_reg`: `Im x*Mx ≥ min(ε, Im w)‖x‖²` for the **full** layer matrix
  `M = [[A - E - X_ε, B], [B*, w]]` with `A` Hermitian and **every** bond `B` (the bond blocks
  cancel in `M - M*`).
* `norm_gReg_le`: hence `‖𝒢(X_ε)(ρ)‖ ≤ min(ε, Im w)⁻¹` at **every** coordinate `ρ`: all
  letters, and `K_ε ι₁ 𝒢` for the deterministic `K_ε = w - X_ε`, are bounded functions of `ρ`.
  This is why the bounded `C¹` class of the OU identity (`OUCov`) applies without a cutoff.
* `gReg_hasFDerivAt`: `d𝒢(v) = -𝒢 (layerDirC v) 𝒢`, `layerDirC v = layerDir b v` Hermitian.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {W : ℕ}

theorem conjTranspose_form' {m : Type*} [Fintype m] (H : Matrix m m ℂ) (x y : m → ℂ) :
    star y ⬝ᵥ (Hᴴ *ᵥ x) = star (star x ⬝ᵥ (H *ᵥ y)) := by
  simp only [dotProduct, mulVec, conjTranspose_apply, star_sum, star_mul', star_star,
    Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Coercivity of the full regularized layer matrix**, for every bond. -/
theorem layer_coercive_reg (E : ℝ) {w : ℂ} {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) (ε : ℝ) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (x : LayerSite W .oneBlockOnePort → ℂ) :
    min ε w.im * vecNorm x ^ 2 ≤
      (star x ⬝ᵥ (layerMatrix .oneBlockOnePort E w (liftX (regX X ε)) ω *ᵥ x)).im := by
  set x₁ := x ∘ Sum.inl
  set x₂ := x ∘ Sum.inr
  have hH : (BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1).IsHermitian := by
    rw [blockDiag_one_eq]
    refine (liftX_isHermitian hA).sub ?_
    ext u v; simp [Matrix.conjTranspose_apply, Matrix.one_apply]; split_ifs <;> simp_all [eq_comm]
  have hexp : star x ⬝ᵥ (layerMatrix .oneBlockOnePort E w (liftX (regX X ε)) ω *ᵥ x) =
      star x₁ ⬝ᵥ ((BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1) *ᵥ x₁) -
        star x₁ ⬝ᵥ (liftX (regX X ε) *ᵥ x₁) +
        (star x₁ ⬝ᵥ (bondL ω *ᵥ x₂) + star x₂ ⬝ᵥ ((bondL ω)ᴴ *ᵥ x₁)) +
        w * (star x₂ ⬝ᵥ x₂) := by
    have h0 : star x ⬝ᵥ (layerMatrix .oneBlockOnePort E w (liftX (regX X ε)) ω *ᵥ x) =
        star x₁ ⬝ᵥ ((BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1 -
          liftX (regX X ε)) *ᵥ x₁ + bondL ω *ᵥ x₂) +
        star x₂ ⬝ᵥ ((bondL ω)ᴴ *ᵥ x₁ + (w • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)) *ᵥ x₂) := by
      rw [layerMatrix_eq, fromBlocks_mulVec]
      simp only [dotProduct, Fintype.sum_sum_type]
      rfl
    rw [h0, dotProduct_add, dotProduct_add, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec,
      dotProduct_smul, smul_eq_mul]
    ring
  have hcross : (star x₁ ⬝ᵥ (bondL ω *ᵥ x₂) + star x₂ ⬝ᵥ ((bondL ω)ᴴ *ᵥ x₁)).im = 0 := by
    rw [conjTranspose_form', Complex.add_im, Complex.star_def, Complex.conj_im]; ring
  have hnorm : (star x₂ ⬝ᵥ x₂) = ((vecNorm x₂ ^ 2 : ℝ) : ℂ) := by
    rw [vecNorm_sq_eq]
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hq := qf_liftX_im_le_reg hY ε x₁
  rw [hexp, Complex.add_im, Complex.add_im, Complex.sub_im, qf_im_eq_zero hH, hcross, hnorm,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero,
    vecNorm_sq_sum x]
  have h1 : min ε w.im ≤ ε := min_le_left _ _
  have h2 : min ε w.im ≤ w.im := min_le_right _ _
  have hn1 : 0 ≤ vecNorm x₁ ^ 2 := by positivity
  have hn2 : 0 ≤ vecNorm x₂ ^ 2 := by positivity
  nlinarith

/-- **The regularized resolvent is bounded**: `‖𝒢(X_ε)(ρ)‖ ≤ min(ε, Im w)⁻¹` for every `ρ`. -/
theorem norm_gReg_le (E : ℝ) {w : ℂ} (hw : 0 < w.im) (b : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε) (ρ : CoordW W → ℝ) :
    ‖gReg E w b X ε ρ‖ ≤ (min ε w.im)⁻¹ :=
  (isUnit_and_norm_inv_le_of_coercive (lt_min hε hw)
    (layer_coercive_reg E hY ε (coordMap_hermitian b ρ))).2

/-- `layerDir b` as a continuous linear map. -/
def layerDirC (W : ℕ) (b : ℝ) :
    (CoordW W → ℝ) →L[ℝ] Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  LinearMap.toContinuousLinearMap (layerDirL W b)

theorem layerDirC_apply (b : ℝ) (v : CoordW W → ℝ) : layerDirC W b v = layerDir b v := rfl

theorem layerDirC_herm (b : ℝ) (v : CoordW W → ℝ) : (layerDirC W b v)ᴴ = layerDirC W b v :=
  layerDir_isHermitian b v

theorem gReg_contDiff (E : ℝ) {w : ℂ} (hw : 0 < w.im) (b : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 1 (gReg E w b X ε) :=
  (contDiff_layerResolvent_reg E hw b hY hε).of_le le_top

/-- `d𝒢(v) = -𝒢 (layerDir v) 𝒢`. -/
theorem gReg_hasFDerivAt (E : ℝ) {w : ℂ} (hw : 0 < w.im) (b : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε) (ρ : CoordW W → ℝ) :
    ∃ T : (CoordW W → ℝ) →L[ℝ] Matrix (LayerSite W .oneBlockOnePort)
        (LayerSite W .oneBlockOnePort) ℂ,
      HasFDerivAt (gReg E w b X ε) T ρ ∧
        ∀ v, T v = -(gReg E w b X ε ρ * layerDirC W b v * gReg E w b X ε ρ) := by
  set M := fun ρ => layerMatrix .oneBlockOnePort E w (liftX (regX X ε)) (coordMap W b ρ) with hMdef
  have hM : M = fun ρ => M 0 + layerDirC W b ρ := by
    funext ρ
    have := layerMatrix_line E w b (regX X ε) 0 ρ 1
    simp only [one_smul, zero_add, Complex.ofReal_one] at this
    exact this
  have hu := (layer_isUnit_reg E hw hY hε (coordMap_hermitian b ρ)).2.1
  set u := hu.unit with hudef
  have hL : HasFDerivAt M (layerDirC W b) ρ := by
    rw [hM]; exact (ContinuousLinearMap.hasFDerivAt _).const_add _
  have h : HasFDerivAt Ring.inverse
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix (LayerSite W .oneBlockOnePort)
        (LayerSite W .oneBlockOnePort) ℂ) ↑u⁻¹ ↑u⁻¹)) (M ρ) := by
    have := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rwa [hudef, IsUnit.unit_spec] at this
  have hinv : (↑u⁻¹ : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) =
      gReg E w b X ε ρ := by
    rw [gReg, layerResolvent, Matrix.nonsing_inv_eq_ringInverse, ← Ring.inverse_unit, hudef,
      IsUnit.unit_spec]
  have hfun : gReg E w b X ε = Ring.inverse ∘ M := by
    funext ρ'
    simp only [Function.comp_apply, gReg, layerResolvent, hMdef, Matrix.nonsing_inv_eq_ringInverse]
  refine ⟨_, hfun ▸ h.comp ρ hL, fun v => ?_⟩
  simp only [ContinuousLinearMap.comp_apply, _root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, hinv]

end BlockBand.Transmission.PassiveLayer
