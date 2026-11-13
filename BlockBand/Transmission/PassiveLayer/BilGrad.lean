module

public import BlockBand.Transmission.PassiveLayer.BilLayer

/-!
# The `W^{-1/2}` gradient bound for the regularized bilinear functionals

For `ε > 0`, `gReg E w b X ε ρ = 𝒢(X - iε)(coordMap ρ)` and
`f(ρ) = psiMap (P_K*u) (P_K*v) θ P₂ Γ (gReg ρ)` (`P_K = (w - X_ε)ι₁`, `|θ| ≤ 1`):

* `contDiff_psi_gReg`: `f` is `C¹` in the Gaussian coordinates;
* `fderiv_psi_gReg`: its coordinate derivatives in contracted form;
* `three_terms_le`: deterministic bound of the three contracted terms;
* `grad_psi_reg`: `|∇f|_v ≤ √(12/W) · 3‖P_K𝒢‖²‖𝒢‖(‖𝒢‖+‖Γ‖) ‖u‖‖v‖` at every `ρ`
  (`Inputs.weightedGradientNorm`, weights `coordVar W b`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Internal.Contracts.Inputs
open scoped Matrix.Norms.L2Operator ComplexOrder NNReal

open BlockBand.Transmission

variable {W : ℕ}

/-- The regularized resolvent in the Gaussian coordinates. -/
def gReg (E : ℝ) (w : ℂ) (b : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ) (ρ : CoordW W → ℝ) :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  layerResolvent .oneBlockOnePort E w (liftX (regX X ε)) (coordMap W b ρ)

theorem contDiff_psi_gReg (E : ℝ) {w : ℂ} (hw : 0 < w.im) (b : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε) (a c : LayerSite W .oneBlockOnePort → ℂ)
    (θ : ℂ) (P Γ : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    ContDiff ℝ 1 fun ρ => psiMap a c θ P Γ (gReg E w b X ε ρ) := by
  have hG : ContDiff ℝ 1 fun ρ => gReg E w b X ε ρ :=
    (contDiff_layerResolvent_reg E hw b hY hε).of_le le_top
  have hR : ContDiff ℝ 1 fun ρ => rMap θ P Γ (gReg E w b X ε ρ) :=
    (((contDiff_const.mul hG).mul contDiff_const).const_smul θ).add contDiff_const
  have hS : ContDiff ℝ 1 fun ρ => (gReg E w b X ε ρ)ᴴ :=
    (starL' ℝ : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ ≃L[ℝ] _).contDiff.comp hG
  have hH := (hG.mul hR).mul hS
  exact ((formCLM a c).restrictScalars ℝ).contDiff.comp hH

section Generic
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The three contracted terms are bounded by `3‖P_K𝒢‖²‖𝒢‖(‖𝒢‖+‖Γ‖)‖u‖‖v‖`. -/
theorem three_terms_le (pk : Matrix m n ℂ) (G P Γ : Matrix n n ℂ) {θ : ℂ} (hθ : ‖θ‖ ≤ 1)
    (hP : ‖P‖ ≤ 1) (u v : m → ℂ) :
    vecNorm (star (pkᴴ *ᵥ u) ᵥ* G) * vecNorm ((G * rMap θ P Γ G * Gᴴ) *ᵥ (pkᴴ *ᵥ v)) +
      ‖θ‖ * (vecNorm (star (pkᴴ *ᵥ u) ᵥ* (G * P * G)) * vecNorm ((G * P * Gᴴ) *ᵥ (pkᴴ *ᵥ v))) +
      vecNorm (star (pkᴴ *ᵥ u) ᵥ* (G * rMap θ P Γ G * Gᴴ)) * vecNorm (Gᴴ *ᵥ (pkᴴ *ᵥ v)) ≤
    3 * (‖pk * G‖ ^ 2 * ‖G‖ * (‖G‖ + ‖Γ‖)) * (vecNorm u * vecNorm v) := by
  have hq : 0 ≤ ‖pk * G‖ := norm_nonneg _
  have hg : 0 ≤ ‖G‖ := norm_nonneg _
  have hΓ := norm_nonneg Γ
  have hPn := norm_nonneg P
  have hGP : ‖G * P‖ ≤ ‖G‖ :=
    (Matrix.l2_opNorm_mul _ _).trans (by nlinarith)
  have hPGP : ‖P * G * P‖ ≤ ‖G‖ := by
    have h1 : ‖P * G‖ ≤ ‖G‖ := (Matrix.l2_opNorm_mul _ _).trans (by nlinarith)
    exact (Matrix.l2_opNorm_mul _ _).trans (by nlinarith [norm_nonneg (P * G)])
  have hRn : ‖rMap θ P Γ G‖ ≤ ‖G‖ + ‖Γ‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    rw [norm_smul]
    nlinarith [norm_nonneg θ, norm_nonneg (P * G * P)]
  have hr : 0 ≤ ‖rMap θ P Γ G‖ := norm_nonneg _
  have hsa : star (pkᴴ *ᵥ u) = star u ᵥ* pk := by
    simp only [star_mulVec, conjTranspose_conjTranspose]
  have hvx : ∀ A : Matrix n n ℂ, vecNorm (star (pkᴴ *ᵥ u) ᵥ* A) ≤ ‖pk * A‖ * vecNorm u := by
    intro A
    rw [hsa, vecMul_vecMul]
    have := vecNorm_vecMul_le (star u) (pk * A)
    rwa [vecNorm_star] at this
  have hvy : ∀ A : Matrix n n ℂ, vecNorm (A *ᵥ (pkᴴ *ᵥ v)) ≤ ‖A * pkᴴ‖ * vecNorm v := by
    intro A
    rw [mulVec_mulVec]
    exact vecNorm_mulVec_le' _ _
  have hGH : ‖Gᴴ‖ = ‖G‖ := Matrix.l2_opNorm_conjTranspose _
  have hpkGH : ‖(pk * G)ᴴ‖ = ‖pk * G‖ := Matrix.l2_opNorm_conjTranspose _
  have e1 : ‖G * rMap θ P Γ G * Gᴴ * pkᴴ‖ ≤ ‖G‖ * ‖rMap θ P Γ G‖ * ‖pk * G‖ := by
    rw [Matrix.mul_assoc (G * rMap θ P Γ G), ← conjTranspose_mul]
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    rw [hpkGH]
    exact mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) hq
  have e2 : ‖G * P * Gᴴ * pkᴴ‖ ≤ ‖G‖ * ‖pk * G‖ := by
    rw [Matrix.mul_assoc (G * P), ← conjTranspose_mul]
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    rw [hpkGH]
    exact mul_le_mul_of_nonneg_right hGP hq
  have e3 : ‖Gᴴ * pkᴴ‖ = ‖pk * G‖ := by rw [← conjTranspose_mul, hpkGH]
  have f2 : ‖pk * (G * P * G)‖ ≤ ‖pk * G‖ * ‖G‖ := by
    rw [show pk * (G * P * G) = pk * G * P * G by simp only [Matrix.mul_assoc]]
    refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ hg)
    exact (Matrix.l2_opNorm_mul _ _).trans (by nlinarith)
  have f3 : ‖pk * (G * rMap θ P Γ G * Gᴴ)‖ ≤ ‖pk * G‖ * ‖rMap θ P Γ G‖ * ‖G‖ := by
    rw [show pk * (G * rMap θ P Γ G * Gᴴ) = pk * G * rMap θ P Γ G * Gᴴ by
      simp only [Matrix.mul_assoc]]
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    rw [hGH]
    exact mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) hg
  have hu := vecNorm_nonneg u
  have hv := vecNorm_nonneg v
  have b1 : vecNorm (star (pkᴴ *ᵥ u) ᵥ* G) * vecNorm ((G * rMap θ P Γ G * Gᴴ) *ᵥ (pkᴴ *ᵥ v)) ≤
      (‖pk * G‖ * vecNorm u) * ((‖G‖ * ‖rMap θ P Γ G‖ * ‖pk * G‖) * vecNorm v) :=
    mul_le_mul (hvx G) ((hvy _).trans (mul_le_mul_of_nonneg_right e1 hv))
      (vecNorm_nonneg _) (mul_nonneg hq hu)
  have b2 : vecNorm (star (pkᴴ *ᵥ u) ᵥ* (G * P * G)) * vecNorm ((G * P * Gᴴ) *ᵥ (pkᴴ *ᵥ v)) ≤
      ((‖pk * G‖ * ‖G‖) * vecNorm u) * ((‖G‖ * ‖pk * G‖) * vecNorm v) :=
    mul_le_mul ((hvx _).trans (mul_le_mul_of_nonneg_right f2 hu))
      ((hvy _).trans (mul_le_mul_of_nonneg_right e2 hv)) (vecNorm_nonneg _)
      (mul_nonneg (mul_nonneg hq hg) hu)
  have b3 : vecNorm (star (pkᴴ *ᵥ u) ᵥ* (G * rMap θ P Γ G * Gᴴ)) * vecNorm (Gᴴ *ᵥ (pkᴴ *ᵥ v)) ≤
      ((‖pk * G‖ * ‖rMap θ P Γ G‖ * ‖G‖) * vecNorm u) * (‖pk * G‖ * vecNorm v) :=
    mul_le_mul ((hvx _).trans (mul_le_mul_of_nonneg_right f3 hu))
      ((hvy _).trans_eq (by rw [e3])) (vecNorm_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg hq hr) hg) hu)
  have hθ0 := norm_nonneg θ
  set X1 := vecNorm (star (pkᴴ *ᵥ u) ᵥ* G) * vecNorm ((G * rMap θ P Γ G * Gᴴ) *ᵥ (pkᴴ *ᵥ v))
  set X2 := vecNorm (star (pkᴴ *ᵥ u) ᵥ* (G * P * G)) * vecNorm ((G * P * Gᴴ) *ᵥ (pkᴴ *ᵥ v))
  set X3 := vecNorm (star (pkᴴ *ᵥ u) ᵥ* (G * rMap θ P Γ G * Gᴴ)) * vecNorm (Gᴴ *ᵥ (pkᴴ *ᵥ v))
  set q := ‖pk * G‖
  set g := ‖G‖
  set r := ‖rMap θ P Γ G‖
  set γ := ‖Γ‖
  set U := vecNorm u
  set V := vecNorm v
  have hX2 : 0 ≤ X2 := mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)
  have h2' : ‖θ‖ * X2 ≤ X2 := by nlinarith
  have hUV : 0 ≤ U * V := mul_nonneg hu hv
  have key : (q * U) * ((g * r * q) * V) + ((q * g) * U) * ((g * q) * V) +
      ((q * r * g) * U) * (q * V) ≤ 3 * (q ^ 2 * g * (g + γ)) * (U * V) := by
    have hqg : 0 ≤ q ^ 2 * g * (U * V) := by positivity
    have := mul_le_mul_of_nonneg_left hRn hqg
    nlinarith
  linarith

end Generic

/-- The directional derivatives of the regularized functional. -/
theorem fderiv_psi_gReg (E : ℝ) {w : ℂ} (hw : 0 < w.im) (b : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε) (a c : LayerSite W .oneBlockOnePort → ℂ)
    (θ : ℂ) (Γ : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ)
    (ρ : CoordW W → ℝ) (i : CoordW W) :
    fderiv ℝ (fun ρ => psiMap a c θ (pTwo W) Γ (gReg E w b X ε ρ)) ρ (Pi.single i 1) =
      -((star a ᵥ* gReg E w b X ε ρ) ⬝ᵥ (layerDir b (Pi.single i 1) *ᵥ
          ((gReg E w b X ε ρ * rMap θ (pTwo W) Γ (gReg E w b X ε ρ) * (gReg E w b X ε ρ)ᴴ) *ᵥ c)) +
        θ * ((star a ᵥ* (gReg E w b X ε ρ * pTwo W * gReg E w b X ε ρ)) ⬝ᵥ
          (layerDir b (Pi.single i 1) *ᵥ
            ((gReg E w b X ε ρ * pTwo W * (gReg E w b X ε ρ)ᴴ) *ᵥ c))) +
        (star a ᵥ* (gReg E w b X ε ρ * rMap θ (pTwo W) Γ (gReg E w b X ε ρ) *
          (gReg E w b X ε ρ)ᴴ)) ⬝ᵥ (layerDir b (Pi.single i 1) *ᵥ ((gReg E w b X ε ρ)ᴴ *ᵥ c))) := by
  have hMu := (layer_isUnit_reg E hw hY hε (coordMap_hermitian b ρ)).2.1
  refine fderiv_apply_eq_of_line
    (((contDiff_psi_gReg E hw b hY hε a c θ _ Γ).differentiable (by simp)) ρ) ?_
  have hline : (fun t : ℝ => psiMap a c θ (pTwo W) Γ (gReg E w b X ε (ρ + t • Pi.single i 1))) =
      fun t : ℝ => psiMap a c θ (pTwo W) Γ
        ((layerMatrix .oneBlockOnePort E w (liftX (regX X ε)) (coordMap W b ρ) +
          (t : ℂ) • layerDir b (Pi.single i 1))⁻¹) := by
    funext t
    simp only [gReg, layerResolvent, layerMatrix_line]
  rw [hline]
  have h := hasDerivAt_psi_line a c θ (pTwo W) Γ _ (layerDir b (Pi.single i 1)) hMu
  rw [psi_deriv_eq, (layerDir_isHermitian b _).eq] at h
  exact h

/-- **Gradient bound for the regularized bilinear functional** (`|θ| ≤ 1`). -/
theorem grad_psi_reg {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) {w : ℂ}
    (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) {ε : ℝ}
    (hε : 0 < ε) (u v : Fin W → ℂ) {θ : ℂ} (hθ : ‖θ‖ ≤ 1)
    (Γ : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) (ρ : CoordW W → ℝ) :
    weightedGradientNorm (coordVar W b)
        (fun ρ => psiMap ((pK w (regX X ε))ᴴ *ᵥ u) ((pK w (regX X ε))ᴴ *ᵥ v) θ (pTwo W) Γ
          (gReg E w b X ε ρ)) ρ ≤
      Real.sqrt (3 * (4 / W)) * (3 * (‖pK w (regX X ε) * gReg E w b X ε ρ‖ ^ 2 *
        ‖gReg E w b X ε ρ‖ * (‖gReg E w b X ε ρ‖ + ‖Γ‖)) * (vecNorm u * vecNorm v)) := by
  refine (weightedGradientNorm_le (coordVar W b) _ ρ (fun i => layerDir b (Pi.single i 1)) θ
    _ _ _ _ _ _ (by positivity) (fderiv_psi_gReg E hw b hY hε _ _ θ Γ ρ)
    (fun x y => layerDir_sum_le hb0 hb hW x y)).trans ?_
  exact mul_le_mul_of_nonneg_left (three_terms_le _ _ _ Γ hθ norm_pTwo_le u v)
    (Real.sqrt_nonneg _)

end BlockBand.Transmission.PassiveLayer
