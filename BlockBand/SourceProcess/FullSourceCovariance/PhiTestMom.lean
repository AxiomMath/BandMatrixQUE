module

public import BlockBand.SourceProcess.FullSourceCovariance.PhiTest
public import BlockBand.SourceProcess.FullSource.DeltaFlucReg

/-!
# Crude moments of the right-weighted vector `𝒢K̂c'`

An almost-sure bound on `‖𝒢K̂ι₁y‖` and uniform moment bounds for the corresponding weights. Law
`freshLaw W b`, `B = btFun`.

* `kHat_mulVec_physVec`: `K̂ι₁y = (ι₁*K)y` (`FullSource.qK`);
* `lamW = 1 + ‖𝒢‖(4 + ‖A‖ + ‖B‖)`; **`ae_norm_gK_le`**: `‖𝒢K̂ι₁y‖ ≤ lamW·‖y‖` a.s. at `Y ≻ 0`
  (`FullSource.norm_gQ_le`, `‖z‖ + |E| ≤ 4`);
* **`lam_mom hA`**: `‖(1+B)lamW‖₄, ‖(1+B)²·(1+B)lamW‖₂ ≤ C`, uniform on `bulkInterval κ`
  (`moments`, `blockA_mom`, `bondB_mom`, as in `FullSource.dWeight_mom`);
* `qForm_eq`, `qForm_eq_kHat`, `qDer_apply`: closed forms of the test and its derivative.
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

theorem kHat_mulVec_physVec (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (y : Fin W → ℂ) :
    kHat b E X *ᵥ physVec y = FullSource.qK (boundaryZ b E) X *ᵥ y := by
  funext γ
  rcases γ with ⟨i, j⟩ | ⟨i, j⟩ <;> obtain rfl : i = 0 := Subsingleton.elim _ _
  · simp [kHat, FullSource.qK, iota1, physVec, mulVec, dotProduct, liftX, Matrix.mul_apply,
      conjTranspose_apply, fromBlocks, Fintype.sum_prod_type]
  · simp [kHat, FullSource.qK, iota1, physVec, mulVec, dotProduct, liftX, Matrix.mul_apply,
      conjTranspose_apply, fromBlocks]

/-- `lamW = 1 + ‖𝒢‖(4 + ‖A‖ + ‖B‖)`. -/
def lamW (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) : ℝ :=
  1 + ‖gRes b E X ω‖ * (4 + ‖ω.1 0‖ + ‖ω.2 0 0‖)

theorem one_le_lamW (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    1 ≤ lamW b E X ω := by
  unfold lamW; have : 0 ≤ ‖gRes b E X ω‖ * (4 + ‖ω.1 0‖ + ‖ω.2 0 0‖) := by positivity
  linarith

theorem measurable_lamW (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (lamW (W := W) b E X) := by
  have hG := measurable_layerRes (W := W) E (boundaryZ b E) X
  have hA : Measurable fun ω : LayerSample W .oneBlockOnePort => ω.1 0 :=
    (measurable_pi_apply 0).comp measurable_fst
  have hB : Measurable fun ω : LayerSample W .oneBlockOnePort => ω.2 0 0 :=
    (measurable_pi_apply 0).comp ((measurable_pi_apply 0).comp measurable_snd)
  unfold lamW
  exact measurable_const.add (hG.norm.mul ((measurable_const.add hA.norm).add hB.norm))

/-- **`‖𝒢K̂ι₁y‖ ≤ lamW·‖y‖` a.s.** -/
theorem ae_norm_gK_le {b E : ℝ} (hη : 0 < etaZ b E) (hzE : ‖boundaryZ b E‖ + |E| ≤ 4)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosDef) :
    ∀ᵐ ω ∂freshLaw W b, ∀ y : Fin W → ℂ,
      vecNorm (gRes b E X ω *ᵥ (kHat b E X *ᵥ physVec y)) ≤ lamW b E X ω * vecNorm y := by
  filter_upwards [PathScalar.ae_layer_herm b] with ω hω y
  have hu := isUnit_layerMatrix_strict hη hY ω hω
  rw [kHat_mulVec_physVec, mulVec_mulVec]
  refine (vecNorm_mulVec_le' _ _).trans (mul_le_mul_of_nonneg_right ?_ (vecNorm_nonneg _))
  have h := FullSource.norm_gQ_le E (boundaryZ b E) X ω hu
  refine h.trans ?_
  unfold lamW
  have := norm_nonneg (layerAt E (boundaryZ b E) X ω)
  have e : layerAt E (boundaryZ b E) X ω = gRes b E X ω := rfl
  rw [e]
  gcongr

/-- **Crude moments** `‖(1+B)lamW‖₄`, `‖(1+B)²(1+B)lamW‖₂ ≤ C`. -/
theorem lam_mom (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        MomBd (freshLaw W b) (fun ω => (1 + btFun b E X ω) * lamW b E X ω) 4 C ∧
        MomBd (freshLaw W b) (fun ω => (1 + btFun b E X ω) ^ 2 *
          ((1 + btFun b E X ω) * lamW b E X ω)) 2 C := by
  obtain ⟨C₁, W₁, hC₁, hm⟩ := LengthUniform.btFun_moment_bulk hA hb0 hb hκ 16 (by norm_num)
  obtain ⟨CA, hCA0, hCA⟩ := blockA_mom hb (p := 16) (by norm_num)
  obtain ⟨CB, hCB0, hCB⟩ := bondB_mom hb0 (p := 16) (by norm_num)
  set CP := 4 + CA + CB
  set CL := 1 + C₁ * CP
  set C₄ := C₁ * CL
  refine ⟨max C₄ (C₁ * C₁ * C₄), max W₁ 1, by positivity, fun W hW E hE X hX => ?_⟩
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have hBm : Measurable (fun ω => 1 + btFun b E X ω) := measurable_const.add (measurable_btFun b E X)
  have hB16 : MomBd (freshLaw W b) (fun ω => 1 + btFun b E X ω) 16 C₁ :=
    ⟨hBm.aestronglyMeasurable, hm W (le_of_max_le_left hW) E hE X hX⟩
  have hG16 : MomBd (freshLaw W b) (fun ω => ‖gRes b E X ω‖) 16 C₁ :=
    hB16.mono (measurable_layerRes (W := W) E (boundaryZ b E) X).norm.aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [norm_norm]; exact norm_gRes_le_one_add b E X ω)
  have h4 : MomBd (freshLaw W b) (fun _ => (4 : ℝ)) 16 4 := by
    simpa using MomBd.const (μ := freshLaw W b) (4 : ℝ) 16 (by norm_num)
  have hP16 : MomBd (freshLaw W b) (fun ω => 4 + ‖ω.1 0‖ + ‖ω.2 0 0‖) 16 CP :=
    (h4.add (by norm_num) (hCA W hW1) (by norm_num) hCA0).add (by norm_num) (hCB W hW1)
      (by positivity) hCB0
  have hGP : MomBd (freshLaw W b) (fun ω => ‖gRes b E X ω‖ * (4 + ‖ω.1 0‖ + ‖ω.2 0 0‖)) 8
      (C₁ * CP) :=
    MomBd.mul (p := 8) (by norm_num) (by rw [show (2 : ℝ) * 8 = 16 by norm_num]; exact hG16)
      (by rw [show (2 : ℝ) * 8 = 16 by norm_num]; exact hP16) hC₁
  have h1 : MomBd (freshLaw W b) (fun _ => (1 : ℝ)) 8 1 := by
    simpa using MomBd.const (μ := freshLaw W b) (1 : ℝ) 8 (by norm_num)
  have hL8 : MomBd (freshLaw W b) (lamW b E X) 8 CL :=
    h1.add (by norm_num) hGP zero_le_one (by positivity)
  have hB8 : MomBd (freshLaw W b) (fun ω => 1 + btFun b E X ω) (2 * 4) C₁ :=
    hB16.exponent_mono (by norm_num)
  have hBL : MomBd (freshLaw W b) (fun ω => (1 + btFun b E X ω) * lamW b E X ω) 4 C₄ :=
    MomBd.mul (p := 4) (by norm_num) hB8 (by rw [show (2 : ℝ) * 4 = 8 by norm_num]; exact hL8) hC₁
  have hBB : MomBd (freshLaw W b) (fun ω => (1 + btFun b E X ω) * (1 + btFun b E X ω)) 4
      (C₁ * C₁) := MomBd.mul (p := 4) (by norm_num) hB8 hB8 hC₁
  have hB2 : MomBd (freshLaw W b) (fun ω => (1 + btFun b E X ω) ^ 2) (2 * 2) (C₁ * C₁) := by
    rw [show (2 : ℝ) * 2 = 4 by norm_num]
    exact hBB.mono (hBm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (by positivity), sq])
  have hfin := MomBd.mul (p := 2) (by norm_num) hB2
    (by rw [show (2 : ℝ) * 2 = 4 by norm_num]; exact hBL) (by positivity)
  exact ⟨hBL.of_le (le_max_left _ _), hfin.of_le (le_max_right _ _)⟩

theorem qForm_eq (b : ℝ) (u v : LayerSite W .oneBlockOnePort → ℂ) (G : LayerMat W) :
    qForm b u v G = star u ⬝ᵥ ((G * diagonal (physVar W b)) *ᵥ (G *ᵥ v)) := by
  have e : ∀ γ, (star u ⬝ᵥ (G *ᵥ Pi.single γ 1)) * (star (Pi.single γ (1 : ℂ)) ⬝ᵥ (G *ᵥ v)) =
      (star u ᵥ* G) γ * (G *ᵥ v) γ := fun γ => by rw [vecMul_apply_single, single_dotProduct]
  rw [qForm]; simp only [e]; exact physVar_sum_form b u (G *ᵥ v) G

theorem qForm_eq_kHat (b : ℝ) (Kh G : LayerMat W) (a v : LayerSite W .oneBlockOnePort → ℂ) :
    qForm b (Khᴴ *ᵥ a) v G = star a ⬝ᵥ ((Kh * G * diagonal (physVar W b)) *ᵥ (G *ᵥ v)) := by
  rw [qForm_eq, ← star_dotProduct_mul_mulVec, Matrix.mul_assoc]

theorem qDer_apply (b : ℝ) (u v : LayerSite W .oneBlockOnePort → ℂ) (G N : LayerMat W) :
    qDer b u v G N = -(star u ⬝ᵥ ((G * N * G * diagonal (physVar W b) * G) *ᵥ v)) -
      star u ⬝ᵥ ((G * diagonal (physVar W b) * G * N * G) *ᵥ v) := by
  have e1 : star u ⬝ᵥ ((G * N * G * diagonal (physVar W b) * G) *ᵥ v) =
      ∑ γ, physVar W b γ * ((star u ᵥ* (G * N * G)) γ * (G *ᵥ v) γ) := by
    rw [physVar_sum_form, mulVec_mulVec]
  have e2 : star u ⬝ᵥ ((G * diagonal (physVar W b) * G * N * G) *ᵥ v) =
      ∑ γ, physVar W b γ * ((star u ᵥ* G) γ * ((G * N * G) *ᵥ v) γ) := by
    rw [physVar_sum_form, mulVec_mulVec]
    simp only [Matrix.mul_assoc]
  rw [e1, e2, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  unfold qDer
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun γ _ => ?_
  simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
  rw [resFormDeriv_apply, resFormDeriv_apply]
  rw [single_dotProduct, single_dotProduct, ← vecMul_apply_single, ← vecMul_apply_single]
  ring

end BlockBand.SourceProcess.FullSourceCovariance
