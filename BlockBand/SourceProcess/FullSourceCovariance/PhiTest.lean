module

public import BlockBand.SourceProcess.FullSourceCovariance.PhiSameIBP
public import BlockBand.SourceProcess.FullSourceCovariance.TauTest

/-!
# `Φ` as a test functional: layer derivative and crossed term

* `qForm u v G = Σ_γ s_γ (u*G)_γ (Gv)_γ`; `phiSame_eq_qForm`: `Φ(x,y') = qForm (K̂ᴴa) (K̂c') 𝒢`;
* `qDer`, **`hasLayerDeriv_qForm`**: the layer derivative of `qForm u v 𝒢 - κ` at `Y ≻ 0`;
* `qDer_single`: `DΦ(E_{βγ}) = -[(u*𝒢)_β (𝒢S𝒢v)_γ + (u*𝒢S𝒢)_β (𝒢v)_γ]`;
* **`crossed_qDer_le`**: for physical `c` and `f = a'*K̂𝒢`, `u = K̂ᴴa`, the crossed sum
  `|Σ_{β,γ} c_βσ(β,γ) f_γ DΦ(E_{βγ})| ≤ 2W⁻²L³‖𝒢v‖‖a‖‖a'‖‖c‖` whenever `‖𝒢‖, ‖K̂𝒢‖ ≤ L`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `qForm u v G = Σ_γ s_γ (u*G)_γ (Gv)_γ`. -/
def qForm (b : ℝ) (u v : LayerSite W .oneBlockOnePort → ℂ) (G : LayerMat W) : ℂ :=
  ∑ γ, physVar W b γ * ((star u ⬝ᵥ (G *ᵥ Pi.single γ 1)) *
    (star (Pi.single γ (1 : ℂ)) ⬝ᵥ (G *ᵥ v)))

/-- The layer derivative of `qForm`. -/
def qDer (b : ℝ) (u v : LayerSite W .oneBlockOnePort → ℂ) (G : LayerMat W) :
    LayerMat W →ₗ[ℂ] ℂ :=
  ∑ γ, physVar W b γ • ((star (Pi.single γ (1 : ℂ)) ⬝ᵥ (G *ᵥ v)) •
    resFormDeriv G u (Pi.single γ 1) + (star u ⬝ᵥ (G *ᵥ Pi.single γ 1)) •
      resFormDeriv G (Pi.single γ 1) v)

theorem phiSame_eq_qForm (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x y' : Fin W → ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    phiSame b E X x y' ω = qForm b ((kHat b E X)ᴴ *ᵥ physVec x) (kHat b E X *ᵥ physVec y')
      (gRes b E X ω) := by
  rw [phiSame, qForm]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [vecMul_apply_single, star_dotProduct_mul_mulVec, single_dotProduct]

theorem hasLayerDeriv_qForm {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hη : 0 < etaZ b E)
    (hY : (passiveY X).PosDef) (u v : LayerSite W .oneBlockOnePort → ℂ) (κ : ℂ) :
    HasLayerDeriv (fun ω => qForm b u v (gRes b E X ω) - κ)
      (fun ω => qDer b u v (gRes b E X ω)) := by
  intro ω hω Δ _
  have h := hasDerivAt_layerResolvent E (boundaryZ b E) _ ω Δ
    (isUnit_layerMatrix_strict hη hY ω hω)
  have hp := fun γ => (formL u (Pi.single γ (1 : ℂ))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have hq := fun γ => (formL (Pi.single γ (1 : ℂ)) v).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have hs := (HasDerivAt.sum (u := Finset.univ) fun γ _ =>
    ((hp γ).mul (hq γ)).const_mul (physVar W b γ)).sub_const κ
  convert hs using 1
  · funext s; rw [Finset.sum_apply]; rfl
  · unfold qDer
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun γ _ => ?_
    simp only [LinearMap.smul_apply, LinearMap.add_apply, Function.comp_apply,
      formL_apply, neg_mulVec, dotProduct_neg, smul_eq_mul, Complex.ofReal_zero, zero_smul, add_zero]
    rw [resFormDeriv_apply, resFormDeriv_apply]
    ring

theorem mulVec_single_apply (G : LayerMat W) (μ γ : LayerSite W .oneBlockOnePort) :
    (G *ᵥ Pi.single μ (1 : ℂ)) γ = G γ μ := by
  simp [mulVec, dotProduct, Pi.single_apply]

theorem qDer_single (b : ℝ) (u v : LayerSite W .oneBlockOnePort → ℂ) (G : LayerMat W)
    (β γ : LayerSite W .oneBlockOnePort) :
    qDer b u v G (Matrix.single β γ 1) =
      -((star u ᵥ* G) β * ((G * diagonal (physVar W b)) *ᵥ (G *ᵥ v)) γ +
        (star u ᵥ* (G * diagonal (physVar W b) * G)) β * (G *ᵥ v) γ) := by
  have e1 : ((G * diagonal (physVar W b)) *ᵥ (G *ᵥ v)) γ =
      ∑ μ, G γ μ * physVar W b μ * (G *ᵥ v) μ := by
    simp only [mulVec, dotProduct, mul_diagonal]
  have e2 : (star u ᵥ* (G * diagonal (physVar W b) * G)) β =
      ∑ μ, (star u ᵥ* G) μ * physVar W b μ * G μ β := by
    rw [← vecMul_vecMul, ← vecMul_vecMul]
    show ∑ μ, ((star u ᵥ* G) ᵥ* diagonal (physVar W b)) μ * G μ β = _
    simp only [vecMul_diagonal]
  have e3 : ∀ μ, star u ⬝ᵥ (G *ᵥ Pi.single μ 1) = (star u ᵥ* G) μ := fun μ =>
    (vecMul_apply_single u G μ).symm
  unfold qDer
  rw [LinearMap.sum_apply, e1, e2, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
  rw [resFormDeriv_single, resFormDeriv_single, single_dotProduct, vecMul_single_apply,
    mulVec_single_apply, e3]
  ring

/-- `Σ_γ s_γ (a*M)_γ w_γ = a*(MS)w`. -/
theorem physVar_sum_form (b : ℝ) (a w : LayerSite W .oneBlockOnePort → ℂ) (M : LayerMat W) :
    ∑ γ, physVar W b γ * ((star a ᵥ* M) γ * w γ) =
      star a ⬝ᵥ ((M * diagonal (physVar W b)) *ᵥ w) := by
  rw [← mulVec_mulVec, dotProduct_mulVec]
  simp only [dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun γ _ => ?_
  ring

/-- The crossed identity for the test `Φ`. -/
theorem crossed_qDer_pt (b : ℝ) (c : LayerSite W .oneBlockOnePort → ℂ)
    (hc : ∀ j, c (port j) = 0) (f u v : LayerSite W .oneBlockOnePort → ℂ) (G : LayerMat W) :
    ∑ β, ∑ γ, c β * siteVar W b β γ * (f γ * qDer b u v G (Matrix.single β γ 1)) =
      -((∑ β, c β * (star u ᵥ* G) β) *
          ∑ γ, physVar W b γ * (f γ * ((G * diagonal (physVar W b)) *ᵥ (G *ᵥ v)) γ)) -
        (∑ β, c β * (star u ᵥ* (G * diagonal (physVar W b) * G)) β) *
          ∑ γ, physVar W b γ * (f γ * (G *ᵥ v) γ) := by
  have e : ∀ β γ, c β * siteVar W b β γ * (f γ * qDer b u v G (Matrix.single β γ 1)) =
      -(c β * siteVar W b β γ * (f γ * ((star u ᵥ* G) β *
          ((G * diagonal (physVar W b)) *ᵥ (G *ᵥ v)) γ))) -
        c β * siteVar W b β γ * (f γ * ((star u ᵥ* (G * diagonal (physVar W b) * G)) β *
          (G *ᵥ v) γ)) := fun β γ => by
    rw [qDer_single]; ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [crossed_same_pt b c hc, crossed_same_pt b c hc]

/-- **The crossed term of `Φ` is `O(W⁻²)`** pointwise. -/
theorem crossed_qDer_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (Kh G : LayerMat W)
    (a a' c v : LayerSite W .oneBlockOnePort → ℂ) (hc : ∀ j, c (port j) = 0) {L : ℝ}
    (hG : ‖G‖ ≤ L) (hKG : ‖Kh * G‖ ≤ L) :
    ‖∑ β, ∑ γ, c β * siteVar W b β γ * ((star a' ᵥ* (Kh * G)) γ *
        qDer b (Khᴴ *ᵥ a) v G (Matrix.single β γ 1))‖ ≤
      2 * ((W : ℝ)⁻¹) ^ 2 * L ^ 3 * vecNorm (G *ᵥ v) * (vecNorm a * vecNorm a' * vecNorm c) := by
  rw [crossed_qDer_pt b c hc, sum_mul_vecMul, sum_mul_vecMul, physVar_sum_form,
    physVar_sum_form, ← star_dotProduct_mul_mulVec, ← star_dotProduct_mul_mulVec]
  set S := diagonal (physVar W b)
  have hS : ‖S‖ ≤ (W : ℝ)⁻¹ := by
    have := norm_diag_physVar_le (W := W) hb0 hb; rwa [one_div] at this
  have hL : 0 ≤ L := (norm_nonneg _).trans hG
  have hw : 0 ≤ (W : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have na := vecNorm_nonneg a; have na' := vecNorm_nonneg a'; have nc := vecNorm_nonneg c
  have ng := vecNorm_nonneg (G *ᵥ v)
  have b1 : ‖star a ⬝ᵥ ((Kh * G) *ᵥ c)‖ ≤ vecNorm a * vecNorm c * L :=
    (norm_form_le _ _ _).trans (by gcongr)
  have hGS : ‖G * S‖ ≤ L * (W : ℝ)⁻¹ := (Matrix.l2_opNorm_mul _ _).trans (by gcongr)
  have hKGS : ‖Kh * G * S‖ ≤ L * (W : ℝ)⁻¹ := (Matrix.l2_opNorm_mul _ _).trans (by gcongr)
  have b2 : ‖star a' ⬝ᵥ ((Kh * G * S) *ᵥ ((G * S) *ᵥ (G *ᵥ v)))‖ ≤
      vecNorm a' * (L * (W : ℝ)⁻¹ * (L * (W : ℝ)⁻¹ * vecNorm (G *ᵥ v))) := by
    have v1 : vecNorm ((Kh * G * S) *ᵥ ((G * S) *ᵥ (G *ᵥ v))) ≤
        L * (W : ℝ)⁻¹ * (L * (W : ℝ)⁻¹ * vecNorm (G *ᵥ v)) :=
      (vecNorm_mulVec_le' _ _).trans (mul_le_mul hKGS ((vecNorm_mulVec_le' _ _).trans
        (mul_le_mul_of_nonneg_right hGS ng)) (vecNorm_nonneg _) (by positivity))
    exact (norm_star_dotProduct_le _ _).trans (mul_le_mul_of_nonneg_left v1 na')
  have b3 : ‖star a ⬝ᵥ ((Kh * (G * S * G)) *ᵥ c)‖ ≤ vecNorm a * vecNorm c * (L * (W : ℝ)⁻¹ * L) := by
    refine (norm_form_le _ _ _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hKGS hG (norm_nonneg _) (by positivity))
  have b4 : ‖star a' ⬝ᵥ ((Kh * G * S) *ᵥ (G *ᵥ v))‖ ≤
      vecNorm a' * (L * (W : ℝ)⁻¹ * vecNorm (G *ᵥ v)) :=
    (norm_star_dotProduct_le _ _).trans (mul_le_mul_of_nonneg_left ((vecNorm_mulVec_le' _ _).trans
      (mul_le_mul_of_nonneg_right hKGS ng)) na')
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg, norm_mul, norm_mul]
  calc _ ≤ vecNorm a * vecNorm c * L *
        (vecNorm a' * (L * (W : ℝ)⁻¹ * (L * (W : ℝ)⁻¹ * vecNorm (G *ᵥ v)))) +
      vecNorm a * vecNorm c * (L * (W : ℝ)⁻¹ * L) *
        (vecNorm a' * (L * (W : ℝ)⁻¹ * vecNorm (G *ᵥ v))) := by gcongr
    _ = _ := by ring

end BlockBand.SourceProcess.FullSourceCovariance
