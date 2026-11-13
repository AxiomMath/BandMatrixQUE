module

public import BlockBand.Transmission.PathScalar.MeanEqPhys

/-!
# The one-port mean equations for strictly passive inputs

`PassiveMeanEquations` restricted to strictly passive inputs: the witness `v = E⟨𝒢₁₁⟩` has
`Im v ≤ 0`, is bounded, and satisfies both mean equations with error `C/W²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem layerMatrix_im_posDef {b E : ℝ} (hη : 0 < etaZ b E)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosDef) (ω : LayerSample W .oneBlockOnePort)
    (hA : (ω.1 0).IsHermitian) :
    (matrixImaginaryPart (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω)).PosDef := by
  rw [layerMatrix, matrixImaginaryPart_fromBlocks_adj]
  refine posDef_fromBlocks_diag ?_ ?_
  · have hBD : (BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)).IsHermitian := by
      refine IsHermitian.sub ?_ ?_
      · ext u v
        simp only [conjTranspose_apply, BlockBand.Internal.Contracts.Layers.blockDiag]
        have hu : u.1 = 0 := Subsingleton.elim _ _
        have hv : v.1 = 0 := Subsingleton.elim _ _
        simp only [hu, hv, ite_true]
        have h := congrFun (congrFun hA u.2) v.2
        simpa [conjTranspose_apply] using h
      · exact isHermitian_one.smul (Complex.conj_ofReal E)
    have h0 : matrixImaginaryPart (BlockBand.Internal.Contracts.Layers.blockDiag ω.1 -
        (E : ℂ) • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)) = 0 := by
      rw [matrixImaginaryPart, hBD.eq, sub_self, smul_zero]
    rw [matrixImaginaryPart_sub, h0, zero_sub]
    have hl : -matrixImaginaryPart (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) =
        Matrix.of fun (u v : Fin 1 × Fin W) => passiveY X u.2 v.2 := by
      ext u v; simp [matrixImaginaryPart, passiveY]
    rw [hl]
    exact posDef_liftX hY
  · have h := matrixImaginaryPart_portPencil (0 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)
      isHermitian_zero (boundaryZ b E)
    simp only [portPencil, sub_zero] at h
    rw [h]
    exact Matrix.PosDef.one.smul hη

/-- `Im ⟨𝒢₁₁⟩ ≤ 0` at Hermitian samples (strictly passive `X`). -/
theorem im_physTr_nonpos {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosDef) (ω : LayerSample W .oneBlockOnePort) (hA : (ω.1 0).IsHermitian) :
    (physTr b E X ω).im ≤ 0 := by
  have h := neg_im_inv_posSemidef _ (layerMatrix_im_posDef hη hY ω hA).posSemidef
  have hd : ∀ x, (gRes b E X ω (phys x) (phys x)).im ≤ 0 := fun x => by
    have h1 := h.diag_nonneg (i := phys x)
    rw [diag_negIm] at h1
    have := (Complex.nonneg_iff.mp h1).1
    simp at this; exact this
  have e : (physTr b E X ω).im = (W : ℝ)⁻¹ * ∑ x, (gRes b E X ω (phys x) (phys x)).im := by
    simp [physTr, trace_letter0, Complex.im_sum]
  rw [e]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos fun x _ => hd x)

theorem norm_physTr_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    ‖physTr b E X ω‖ ≤ ‖gRes b E X ω‖ := by
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · simp [physTr]
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [physTr, trace_letter0, norm_mul, norm_inv, Complex.norm_natCast]
  calc (W : ℝ)⁻¹ * ‖∑ y, gRes b E X ω (phys y) (phys y)‖
      ≤ (W : ℝ)⁻¹ * ∑ _y : Fin W, ‖gRes b E X ω‖ := by
        gcongr; exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => norm_entry_le' _ _ _)
    _ = ‖gRes b E X ω‖ := by simp; field_simp

/-- `PassiveMeanEquations` for strictly passive inputs. -/
def PassiveMeanEquationsStrict : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (Cv C : ℝ) (W₀ : ℕ), 0 ≤ Cv ∧ 0 ≤ C ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
        (passiveY X).PosDef →
          ∃ v : ℂ, v.im ≤ 0 ∧ ‖v‖ ≤ Cv ∧
            ‖(∫ ω, freshPortTrace b E X ω ∂freshLaw W b) * (boundaryZ b E - (b : ℂ) * v) - 1‖ ≤
              C / (W : ℝ) ^ 2 ∧
            ‖v - stieltjes X (zetaOf b E v (∫ ω, freshPortTrace b E X ω ∂freshLaw W b))‖ ≤
              C / (W : ℝ) ^ 2

theorem passiveMeanEquationsStrict_holds (hA : PassiveBoundsStatement) :
    PassiveMeanEquationsStrict := by
  intro b hb0 hb κ hκ
  obtain ⟨C1, W1, m1⟩ := layer_moments_u hA hb0 hb hκ 1 le_rfl
  set Cv := max C1 0 with hCvdef
  have hCv : 0 ≤ Cv := le_max_right _ _
  have hQ := Q0c_pos hb0 hb hκ hCv
  have he1 := eps1_pos hb0 hb hκ hCv
  obtain ⟨Cp, Wp, hCp, hport⟩ := meanEq_port_u hA hb0 hb hκ
  obtain ⟨Cf, Wf, hCf, hphys⟩ := meanEq_phys_u hA hb0 hb hκ (ι₀ := Q0c b κ Cv / 2) (by positivity)
  refine ⟨Cv, max Cp Cf, max (max W1 Wp) (max Wf (⌈Cp / eps1 b κ Cv⌉₊ + 1)), hCv,
    le_trans hCp (le_max_left _ _), fun W hW E hE X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW1, hWp⟩, hWf, hWe⟩ := hW
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hx : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hx0 : (0 : ℝ) < W := by linarith
  set μ := layerLaw W b .oneBlockOnePort
  set v := ∫ ω, physTr b E X ω ∂freshLaw W b
  set u := ∫ ω, freshPortTrace b E X ω ∂freshLaw W b
  have hm := m1 W hW1 E hE X hX.posSemidef
  have hGm : Measurable fun ω => ‖gRes b E X ω‖ :=
    continuous_norm.measurable.comp (measurable_layerRes (W := W) E (boundaryZ b E) X)
  have hl : ∫⁻ ω, ‖‖gRes b E X ω‖‖ₑ ∂μ ≤ ENNReal.ofReal C1 := by
    have := hm
    rwa [show ENNReal.ofReal 1 = 1 by simp,
      eLpNorm_one_eq_lintegral_enorm hGm.aestronglyMeasurable] at this
  have hGi : Integrable (fun ω => ‖gRes b E X ω‖) μ :=
    ⟨hGm.aestronglyMeasurable, lt_of_le_of_lt hl ENNReal.ofReal_lt_top⟩
  have hPm : Measurable fun ω => physTr b E X ω := by
    simp only [physTr, trace_letter0]
    exact measurable_const.mul (Finset.measurable_sum _ fun y _ =>
      (measurable_layerRes (W := W) E (boundaryZ b E) X).eval_matrix)
  have hPi : Integrable (fun ω => physTr b E X ω) μ :=
    hGi.mono' hPm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => norm_physTr_le b E X ω)
  have hv0 : v.im ≤ 0 := by
    have : v.im = ∫ ω, (physTr b E X ω).im ∂μ := (integral_im hPi).symm
    rw [this]
    exact integral_nonpos_of_ae ((ae_layer_herm b).mono fun ω hA =>
      im_physTr_nonpos hη hX ω hA)
  have hvC : ‖v‖ ≤ Cv := by
    have hint : ∫ ω, ‖gRes b E X ω‖ ∂μ ≤ Cv := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => norm_nonneg _)
        hGm.aestronglyMeasurable]
      have hl' : ∫⁻ ω, ENNReal.ofReal ‖gRes b E X ω‖ ∂μ ≤ ENNReal.ofReal C1 := by
        simpa [Real.enorm_eq_ofReal (norm_nonneg _)] using hl
      exact ENNReal.toReal_le_of_le_ofReal hCv (hl'.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    calc ‖v‖ ≤ ∫ ω, ‖physTr b E X ω‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, ‖gRes b E X ω‖ ∂μ := integral_mono hPi.norm hGi fun ω => norm_physTr_le b E X ω
      _ ≤ Cv := hint
  have hεW : Cp / (W : ℝ) ^ 2 ≤ eps1 b κ Cv := by
    have hc := Nat.le_ceil (Cp / eps1 b κ Cv)
    have hc' : ((⌈Cp / eps1 b κ Cv⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast (by omega : ⌈Cp / eps1 b κ Cv⌉₊ ≤ W)
    have hWW : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
    have h1' : Cp / eps1 b κ Cv ≤ (W : ℝ) ^ 2 := by linarith
    rw [div_le_iff₀ he1] at h1'
    rw [div_le_iff₀ (by positivity)]; linarith
  have hs := hport W hWp E hE X hX
  obtain ⟨-, -, -, -, hζlow⟩ := stage_one_setup hb0 hb hκ hE hCv hv0 hvC hs (by positivity) hεW
  have hP : 0 ≤ ((1 - 2 * b) + b ^ 2 * ‖(boundaryZ b E - (b : ℂ) * v)⁻¹‖ ^ 2) * (-v.im) :=
    mul_nonneg (by have : 0 < 1 - 2 * b := by linarith
                   positivity) (by linarith)
  have hζ : Q0c b κ Cv / 2 ≤ (zetaOf b E v u).im := by linarith
  have hf := hphys W hWf E hE X hX hζ
  have hdiv : ∀ c : ℝ, c ≤ max Cp Cf → c / (W : ℝ) ^ 2 ≤ max Cp Cf / (W : ℝ) ^ 2 := fun c hc =>
    div_le_div_of_nonneg_right hc (by positivity)
  exact ⟨v, hv0, hvC, hs.trans (hdiv _ (le_max_left _ _)), hf.trans (hdiv _ (le_max_right _ _))⟩

end BlockBand.Transmission.PathScalar
