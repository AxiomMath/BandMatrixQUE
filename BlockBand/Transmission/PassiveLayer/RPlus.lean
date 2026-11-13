module

public import BlockBand.Transmission.PassiveLayer.Moments

/-!
# `R₊ = 𝒢₂₂` almost surely

Part of the passive bounds: `R₊ = (w - X₊)⁻¹`, `X₊ = B*(A-E-X)⁻¹B`.

* `woodbury`: `(w - B*P⁻¹B)(w⁻¹ + w⁻²B*S⁻¹B) = 1` for `S = P - w⁻¹BB*` (deterministic).
* `ae_isUnit_physBlock`: `A - E - X` is a.s. invertible for every fixed `X` (the GUE null
  set, `Bridge.ae_det_gue_add_ne_zero`).
* `ae_g22_eq_Rplus`: for `0 < b < 1/2`, `W ≥ 1`, `Im w > 0` and passive `X`,
  `𝒢₂₂ = (w - X₊)⁻¹` almost surely under `freshLaw W b`. Hence the second operator of the
  `bilinear` clause is a.s. the word `L(𝒢₂₂ - c₀I)L*`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator ComplexOrder ENNReal

open BlockBand.Transmission

variable {W : ℕ}

/-- The bijection `x ↦ (0, x)`. -/
def embedEquiv : Fin W ≃ Fin 1 × Fin W := (Equiv.uniqueProd (Fin W) (Fin 1)).symm

theorem embedEquiv_coe : (embedEquiv (W := W) : Fin W → Fin 1 × Fin W) = embed0 := rfl

/-- The Woodbury identity `(w - B*P⁻¹B)(w⁻¹ + w⁻²B*S⁻¹B) = 1`, `S = P - w⁻¹BB*`. -/
theorem woodbury {m : Type*} [Fintype m] [DecidableEq m] (P B : Matrix m m ℂ) {w : ℂ}
    (hw : w ≠ 0) (hP : IsUnit P) (hS : IsUnit (P - w⁻¹ • (B * Bᴴ))) :
    (w • 1 - Bᴴ * P⁻¹ * B) * (w⁻¹ • 1 + (w⁻¹ ^ 2) • (Bᴴ * (P - w⁻¹ • (B * Bᴴ))⁻¹ * B)) = 1 := by
  set S := P - w⁻¹ • (B * Bᴴ) with hSdef
  have hPP : P⁻¹ * P = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hP)
  have hSS : S * S⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hS)
  have hBB : B * Bᴴ = w • (P - S) := by
    rw [hSdef, sub_sub_cancel, smul_smul, mul_inv_cancel₀ hw, one_smul]
  have key : Bᴴ * P⁻¹ * (B * Bᴴ) * S⁻¹ * B = w • (Bᴴ * S⁻¹ * B - Bᴴ * P⁻¹ * B) := by
    rw [hBB]
    simp only [Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, mul_assoc]
    rw [← mul_assoc P⁻¹ P, hPP, one_mul, ← mul_assoc S S⁻¹, hSS, one_mul]
  have hw' : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
  simp only [sub_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul]
  have e : Bᴴ * P⁻¹ * B * (Bᴴ * S⁻¹ * B) = Bᴴ * P⁻¹ * (B * Bᴴ) * S⁻¹ * B := by
    simp only [mul_assoc]
  rw [e, key, smul_smul]
  linear_combination (norm := module) hw' • (1 : Matrix m m ℂ) + hw' • (w⁻¹ • (Bᴴ * P⁻¹ * B))

theorem det_liftX (M : Matrix (Fin W) (Fin W) ℂ) : (liftX M).det = M.det :=
  Matrix.det_submatrix_equiv_self (Equiv.uniqueProd (Fin W) (Fin 1)) M

theorem ae_isUnit_physBlock (W : ℕ) {b : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ)
    (X : Matrix (Fin W) (Fin W) ℂ) :
    ∀ᵐ ω ∂freshLaw W b, IsUnit (BlockBand.Internal.Contracts.Layers.blockDiag ω.1 -
      (E : ℂ) • 1 - liftX X) := by
  have h := Bridge.ae_det_gue_add_ne_zero W (Bridge.gueVariance_ne_zero hb hW) (-((E : ℂ) • 1) - X)
  rw [← layerLaw_map_block W b .oneBlockOnePort 0] at h
  filter_upwards [ae_of_ae_map ((measurable_pi_apply 0).comp measurable_fst).aemeasurable h]
    with ω hω
  have heq : BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1 - liftX X =
      liftX (ω.1 0 + (-((E : ℂ) • 1) - X)) := by
    rw [blockDiag_one_eq, show ω.1 0 + (-((E : ℂ) • 1) - X) = ω.1 0 - (E : ℂ) • 1 - X by abel,
      liftX_sub, liftX_sub, liftX_smul, liftX_one]
  rw [heq, isUnit_iff_isUnit_det, det_liftX]
  exact isUnit_iff_ne_zero.mpr hω

/-- **`R₊ = 𝒢₂₂` almost surely**: `(w - X₊)⁻¹ = 𝒢₂₂`, `X₊ = B*(A-E-X)⁻¹B`. -/
theorem ae_g22_eq_Rplus {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) {w : ℂ}
    (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    ∀ᵐ ω ∂freshLaw W b, g22 E w X ω = (w • 1 - freshSchur E X ω)⁻¹ := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  filter_upwards [ae_good W hb0 hW, ae_isUnit_physBlock W hb hW E X] with ω hω hP
  have h := (layer_schur E hw hY hω.1 hω.2).2.1
  have hS := isUnit_schurS E hw hY hω.1 hω.2
  set P := BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1 - liftX X
  have hg : g22 E w X ω = (w⁻¹ • 1 + (w⁻¹ ^ 2) • ((bondL ω)ᴴ * (schurS E w X ω)⁻¹ * bondL ω)).submatrix
      embedEquiv embedEquiv := by
    ext x y; simp [g22, layerAt, h, schurInv, embedEquiv_coe, embed0]
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

end BlockBand.Transmission.PassiveLayer
