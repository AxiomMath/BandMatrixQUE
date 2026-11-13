module

public import BlockBand.SourceProcess.FullSourceCovariance.PhiSameMean
public import BlockBand.Transmission.LengthUniform.BulkMeanExpansion

/-!
# Trace–form covariances for the equal-sign mean

Covariances between normalized traces and bilinear forms of short resolvent words are `O(W⁻²)`;
they control the error terms of the equal-sign mean. Law `freshLaw W b`, operator norm.

* `physVar_trace`: `Σ_γ s_γ M_γγ = σ₁(⟨M⟩₀, ⟨M⟩₁)` (`blkTr`), hence `selfTau_eq_sig1` and
  `tSame_eq_sig1`;
* `sTilde_mulVec_physVec`, `tOne_eq`: `S̃c' = c·c'`, so `T₁ = c·F(x,y')`;
* `integral_mul_form`: `E[f·(x*Gy)] = Ef·E[x*Gy] + x*(Cov(f,G))₀₀y`;
* **`traceCov_form_bulk hA`**: for words of length `≤ 2` with insertions `‖D‖ ≤ 1`,
  `|E[⟨w₁⟩_r·x*w₂y] - E⟨w₁⟩_r·E[x*w₂y]| ≤ C W⁻²‖x‖‖y‖`, with all integrands integrable
  (`wordTraceCov_bulk`, constants uniform on `bulkInterval κ`, every passive `X`).
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

theorem gueVar_eq {b : ℝ} (hb : b < 1 / 2) :
    ((gueVar W b : ℝ) : ℂ) = ((1 - 2 * b : ℝ) : ℂ) * (W : ℂ)⁻¹ := by
  have h : ((gueVar W b : ℝ≥0) : ℝ) = (1 - 2 * b) / W :=
    Real.coe_toNNReal _ (div_nonneg (by linarith) (Nat.cast_nonneg W))
  rw [h]; push_cast; ring

theorem ginVar_eq {b : ℝ} (hb0 : 0 < b) : ((ginVar W b : ℝ) : ℂ) = (b : ℂ) * (W : ℂ)⁻¹ := by
  have h : ((ginVar W b : ℝ≥0) : ℝ) = b / W :=
    Real.coe_toNNReal _ (div_nonneg hb0.le (Nat.cast_nonneg W))
  rw [h]; push_cast; ring

/-- `Σ_γ s_γ M_γγ = σ₁(⟨M⟩₀, ⟨M⟩₁)`. -/
theorem physVar_trace {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (M : LayerMat W) :
    ∑ γ, physVar W b γ * M γ γ = sig1 b (SourceMixing.blkTr M 0) (SourceMixing.blkTr M 1) := by
  rw [sum_layerSite, sig1, SourceMixing.blkTr_def, SourceMixing.blkTr_def, trace_blkAt,
    trace_blkAt, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun k _ => ?_
  · simp only [physVar, gueVar_eq hb, siteOf_zero]; ring
  · simp only [physVar, ginVar_eq hb0, siteOf_one]; ring

theorem selfTau_eq_sig1 {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (G : LayerMat W) :
    selfTau b G = sig1 b (SourceMixing.blkTr G 0) (SourceMixing.blkTr G 1) := by
  rw [← physVar_trace hb0 hb, sum_layerSite, selfTau]; rfl

theorem tSame_eq_sig1 {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (D G : LayerMat W) :
    tSame b D G = sig1 b (SourceMixing.blkTr (G * D * G) 0) (SourceMixing.blkTr (G * D * G) 1) :=
  physVar_trace hb0 hb _

/-- `S̃c' = c·c'` on physical vectors. -/
theorem sTilde_mulVec_physVec {b : ℝ} (hb : b < 1 / 2) (hW : W ≠ 0) (y : Fin W → ℂ) :
    sTilde W b *ᵥ physVec y = ((1 - 2 * b : ℝ) : ℂ) • physVec y := by
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  funext γ
  rw [sTilde, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rcases γ with γ | γ
  · simp only [physVar, gueVar_eq hb]; field_simp
  · simp [physVec]

/-- `T₁ = c·F(x,y')`. -/
theorem tOne_eq {b : ℝ} (hb : b < 1 / 2) (hW : W ≠ 0) (E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (x y' : Fin W → ℂ) (ω : LayerSample W .oneBlockOnePort) :
    tOne b E X x y' ω = ((1 - 2 * b : ℝ) : ℂ) * fForm b E X x y' ω := by
  rw [tOne, fForm, ← mulVec_mulVec, sTilde_mulVec_physVec hb hW, mulVec_smul, dotProduct_smul,
    smul_eq_mul]

section Generic
variable {μ : Measure (LayerSample W .oneBlockOnePort)}

/-- `E[f·(x*Gy)] = Ef·E[x*Gy] + x*(Cov(f,G))₀₀y`. -/
theorem integral_mul_form (f : LayerSample W .oneBlockOnePort → ℂ)
    (G : LayerSample W .oneBlockOnePort → LayerMat W) (hG : ∀ α β, Integrable (fun ω => G ω α β) μ)
    (hfG : ∀ α β, Integrable (fun ω => f ω * G ω α β) μ) (x y : Fin W → ℂ) :
    ∫ ω, f ω * (star (physVec x) ⬝ᵥ (G ω *ᵥ physVec y)) ∂μ =
      (∫ ω, f ω ∂μ) * (∫ ω, star (physVec x) ⬝ᵥ (G ω *ᵥ physVec y) ∂μ) +
        bilinear x (blkAt (covMat μ f G) 0 0) y := by
  have hfG' : ∀ α β, Integrable (fun ω => (f ω • G ω) α β) μ := fun α β => hfG α β
  have e : (fun ω => f ω * (star (physVec x) ⬝ᵥ (G ω *ᵥ physVec y))) =
      fun ω => star (physVec x) ⬝ᵥ ((f ω • G ω) *ᵥ physVec y) := funext fun ω => by
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [e, integral_form _ hfG', integral_form _ hG, covMat, blkAt_sub, SourceMixing.blkAt_smul]
  simp only [bilinear, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  ring

end Generic

/-- **Trace–form covariances are `O(W⁻²)`** (bulk-uniform, every passive `X`). -/
theorem traceCov_form_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ ℓ₁ : ℕ, ℓ₁ ≤ 2 →
      ∀ (wd₁ : Fin ℓ₁ → Fin 4) (D₁ : Fin (ℓ₁ + 1) → LayerMat W), (∀ j, ‖D₁ j‖ ≤ 1) →
      ∀ ℓ₂ : ℕ, ℓ₂ ≤ 2 → ∀ (wd₂ : Fin ℓ₂ → Fin 4) (D₂ : Fin (ℓ₂ + 1) → LayerMat W),
      (∀ j, ‖D₂ j‖ ≤ 1) → ∀ (r : Fin 2) (x y : Fin W → ℂ) (f T : LayerSample W .oneBlockOnePort → ℂ),
      (∀ ω, f ω = SourceMixing.blkTr (wordVal (kHat b E X) (gRes b E X ω) wd₁ D₁) r) →
      (∀ ω, T ω = star (physVec x) ⬝ᵥ (wordVal (kHat b E X) (gRes b E X ω) wd₂ D₂ *ᵥ physVec y)) →
        Integrable f (freshLaw W b) ∧ Integrable T (freshLaw W b) ∧
        Integrable (fun ω => f ω * T ω) (freshLaw W b) ∧
        ‖(∫ ω, f ω * T ω ∂freshLaw W b) - (∫ ω, f ω ∂freshLaw W b) * ∫ ω, T ω ∂freshLaw W b‖ ≤
          C / (W : ℝ) ^ 2 * (vecNorm x * vecNorm y) := by
  obtain ⟨C, W₀, hC, h⟩ := LengthUniform.wordTraceCov_bulk hA hb0 hb hκ 2 1
  refine ⟨C, W₀, hC, fun W hW E hE X hX ℓ₁ hℓ₁ wd₁ D₁ hD₁ ℓ₂ hℓ₂ wd₂ D₂ hD₂ r x y f T hf hT => ?_⟩
  obtain ⟨hi1, hi2, hi12, hcov⟩ := h W hW E hE X hX ℓ₁ hℓ₁ wd₁ D₁ hD₁ ℓ₂ hℓ₂ wd₂ D₂ hD₂ r
  have hform : ∀ (H : LayerSample W .oneBlockOnePort → LayerMat W),
      (∀ α β, Integrable (fun ω => H ω α β) (freshLaw W b)) →
      Integrable (fun ω => star (physVec x) ⬝ᵥ (H ω *ᵥ physVec y)) (freshLaw W b) := by
    intro H hH
    have e : (fun ω => star (physVec x) ⬝ᵥ (H ω *ᵥ physVec y)) = fun ω =>
        ∑ α, ∑ β, star (physVec x α) * physVec y β * H ω α β := funext fun ω => by
      simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      ring
    rw [e]
    exact integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
      (hH α β).const_mul _
  have hfe : f = fun ω => SourceMixing.blkTr (wordVal (kHat b E X) (gRes b E X ω) wd₁ D₁) r :=
    funext hf
  have hTe : T = fun ω => star (physVec x) ⬝ᵥ
      (wordVal (kHat b E X) (gRes b E X ω) wd₂ D₂ *ᵥ physVec y) := funext hT
  subst hfe hTe
  refine ⟨hi1, hform _ hi2, ?_, ?_⟩
  · refine (hform _ hi12).congr (Eventually.of_forall fun ω => ?_)
    show star (physVec x) ⬝ᵥ ((SourceMixing.blkTr (wordVal (kHat b E X) (gRes b E X ω) wd₁ D₁) r •
      wordVal (kHat b E X) (gRes b E X ω) wd₂ D₂) *ᵥ physVec y) = _
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
  have key := integral_mul_form (μ := freshLaw W b) _ _ hi2 hi12 x y
  rw [key, add_sub_cancel_left]
  refine (norm_bilinear_le _ _ _).trans ?_
  have hb := (norm_blkAt_le _ 0 0).trans hcov
  have := vecNorm_nonneg x; have := vecNorm_nonneg y
  calc _ ≤ vecNorm x * (C / (W : ℝ) ^ 2) * vecNorm y := by gcongr
    _ = _ := by ring

end BlockBand.SourceProcess.FullSourceCovariance
