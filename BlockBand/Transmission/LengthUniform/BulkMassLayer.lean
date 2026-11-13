module

public import BlockBand.Transmission.SourceMixing.MassLayer
public import BlockBand.Transmission.LengthUniform.BulkMassMean

/-!
# Bulk-uniform fresh-layer mass moments

The fresh mass mean identity and fluctuation, and one fresh layer of the mass-moment recursion,
uniformly in `E ∈ bulkInterval κ`: the constants and `W₀` depend only on `b`, the bulk margin `κ`
and the moment order.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LengthUniform

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- Bulk-uniform copy of `oneStepFluctuation_of_passiveBounds` (the `bilinear` clause of
`PassiveBoundsStatement` at `w = z_∂`). -/
theorem oneStepFluctuation_bulk (h : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (p : ℝ) (hp : 1 ≤ p) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ u v : Fin W → ℂ,
        eLpNorm (fun ω => bilinear u (freshU b E X ω -
            matrixExpect (freshLaw W b) (freshU b E X)) v) (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) ∧
        eLpNorm (fun ω => bilinear u (freshTransportedF b E X ω -
            matrixExpect (freshLaw W b) (freshTransportedF b E X)) v) (ENNReal.ofReal p)
            (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) := by
  obtain ⟨C, W₀, hC⟩ := h.bilinear b hb0 hb κ hκ p hp
  refine ⟨C, W₀, fun W hW E hE X hX u v => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  exact hC W hW E hE (boundaryZ b E) (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hX u v

/-- Bulk-uniform copy of `ml_integrable_U`. -/
theorem ml_integrable_U_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef →
      ∀ i j, Integrable (fun ω => freshU b E X ω i j) (freshLaw W b) := by
  obtain ⟨C4, W4, h4⟩ := hA.moments b hb0 hb _ hκ 4 (by norm_num)
  refine ⟨W4, fun W hW E hE X hX i j => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hz := PassiveLayer.boundaryZ_mem_paramDisk (b := b) (by linarith) h1 h2
  have m4 : eLpNorm (fun ω => ‖freshL b E X ω‖) (ENNReal.ofReal (2 * (2 : ℕ))) (freshLaw W b) ≤
      ENNReal.ofReal C4 := by
    have := (h4 W hW E hE _ hz X hX).2.2.2
    norm_num at this ⊢; exact this
  have hb2 := eLpNorm_two_le_of_pow_bound ((measurable_freshU b E X).eval_matrix (i := i)
    (j := j)).aestronglyMeasurable (fun _ => norm_nonneg _)
    (measurable_norm_freshL b E X).aestronglyMeasurable zero_le_one 2 (by norm_num)
    (fun ω => by rw [one_mul]; exact (norm_entry_le _ i j).trans (norm_freshU_le b E X ω)) m4
  have fin : ENNReal.ofReal 1 * ENNReal.ofReal C4 ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hmem : MemLp (fun ω => freshU b E X ω i j) 2 (freshLaw W b) := hb2.trans_lt fin.lt_top
  exact hmem.integrable one_le_two

/-- Bulk-uniform copy of `ml_fresh`: the fresh mass mean identity and fluctuation. -/
theorem ml_fresh_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (Cf : ℝ) (W₀ : ℕ), 1 ≤ Cf ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        ∫ ω, qc b E (freshSchur E X ω) ∂freshLaw W b =
            (passiveQ b E X * matrixExpect (freshLaw W b) (freshU b E X)).trace.re ∧
          eLpNorm (fun ω => qc b E (freshSchur E X ω) - ∫ ω', qc b E (freshSchur E X ω')
              ∂freshLaw W b) n (freshLaw W b) ≤
            ENNReal.ofReal (Cf / Real.sqrt W * passiveMass b E X) := by
  obtain ⟨Wi, hint⟩ := ml_integrable_U_bulk hA hb0 hb hκ
  obtain ⟨Cb, Wb, hbil⟩ := oneStepFluctuation_bulk hA hb0 hb hκ n (by exact_mod_cast hn)
  refine ⟨max Cb 1, max (max Wi Wb) 1, le_max_right _ _, fun W hW E hE X hX => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWi, hWb⟩, hW1⟩ := hW
  set μ := freshLaw W b
  set Q := passiveQ b E X
  have hQ : Q.PosSemidef := hX.conjTranspose_mul_mul_same _
  have hU := hint W hWi E hE X hX
  have hTint : Integrable (fun ω => (Q * freshU b E X ω).trace) μ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hU j i).const_mul _
  have hae : ∀ᵐ ω ∂μ, qc b E (freshSchur E X ω) = (Q * freshU b E X ω).trace.re := by
    filter_upwards [ae_layer_herm (W := W) b, ae_passiveMass_freshSchur hb0 hb hW1 h1 h2 hX]
      with ω hA0 hm
    rw [qc_eq (PathScalar.passiveY_freshSchur E hX ω hA0), hm]
  have hmean : ∫ ω, qc b E (freshSchur E X ω) ∂μ =
      (Q * matrixExpect μ (freshU b E X)).trace.re := by
    rw [integral_congr_ae hae, ← ml_trace_matrixExpect μ Q hU]
    exact integral_re hTint
  refine ⟨hmean, ?_⟩
  have hB : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (freshU b E X ω -
      matrixExpect μ (freshU b E X)) v) n μ ≤
      ENNReal.ofReal (max Cb 1 / Real.sqrt W * vecNorm u * vecNorm v) := fun u v => by
    have := (hbil W hWb E hE X hX u v).1
    rw [ENNReal.ofReal_natCast] at this
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    have := vecNorm_nonneg u; have := vecNorm_nonneg v
    have : Cb / Real.sqrt W ≤ max Cb 1 / Real.sqrt W :=
      div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
    gcongr
  have hB0 : 0 ≤ max Cb 1 / Real.sqrt W :=
    div_nonneg (le_trans zero_le_one (le_max_right _ _)) (Real.sqrt_nonneg _)
  have hT : eLpNorm (fun ω => (Q * (freshU b E X ω - matrixExpect μ (freshU b E X))).trace) n μ ≤
      ENNReal.ofReal (max Cb 1 / Real.sqrt W * Q.trace.re) :=
    eLpNorm_trace_mul_le μ hQ (by exact_mod_cast hn) hB0 hB
  have hsm : AEStronglyMeasurable (fun ω => qc b E (freshSchur E X ω) -
      ∫ ω', qc b E (freshSchur E X ω') ∂μ) μ :=
    ((measurable_qc_fresh b E X).sub measurable_const).aestronglyMeasurable
  have hpm : passiveMass b E X = Q.trace.re := rfl
  rw [hpm]
  refine le_trans (eLpNorm_mono_ae hsm ?_) hT
  filter_upwards [hae] with ω hω
  have e : (Q * (freshU b E X ω - matrixExpect μ (freshU b E X))).trace.re =
      (Q * freshU b E X ω).trace.re - (Q * matrixExpect μ (freshU b E X)).trace.re := by
    rw [Matrix.mul_sub, trace_sub, Complex.sub_re]
  rw [hω, hmean, Real.norm_eq_abs, ← e]
  exact Complex.abs_re_le_norm _

/-- `q/(1+αq/W) ≤ q/(1+α'q/W)` for `α' ≤ α`, `q ≥ 0`. -/
theorem div_one_add_anti {q α α' W : ℝ} (hq : 0 ≤ q) (hW : 0 < W) (hα' : 0 ≤ α')
    (hαα : α' ≤ α) : q / (1 + α * q / W) ≤ q / (1 + α' * q / W) := by
  have h0 : 0 < 1 + α' * q / W := by have : 0 ≤ α' * q / W := by positivity
                                     linarith
  refine div_le_div_of_nonneg_left hq h0 ?_
  have : α' * q / W ≤ α * q / W :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hαα hq) hW.le
  linarith

/-- **One fresh layer of the mass-moment recursion, bulk-uniform** (copy of `massLayer_step`). -/
theorem massLayer_step_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (c D₁ D₂ : ℝ) (W₀ : ℕ), 0 < c ∧ 0 ≤ D₁ ∧ 0 ≤ D₂ ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ l : ℝ, 0 ≤ l →
        ∫ ω, qc b E (freshSchur E X ω) ^ n ∂freshLaw W b ≤
          qc b E X ^ n * (1 - c * l / W) +
            (c * l ^ (n + 1) + D₁ + D₂ * (W * jetDistance0 b E X) ^ (n + 1)) / W := by
  set ηL := etaLow b κ
  have hηL : 0 < ηL := etaLow_pos (by linarith) hκ
  set αL := (1 - b) ^ 2 / b
  have hαL : 0 < αL := by
    have : 0 < (1 - b) ^ 2 := by have : 0 < 1 - b := by linarith
                                 positivity
    exact div_pos this hb0
  obtain ⟨Cm, Wm, hCm, hmean⟩ := massMean_holds_bulk hA hb0 hb hκ
  obtain ⟨Cf, Wf, hCf, hfr⟩ := ml_fresh_bulk hA hb0 hb hκ n hn
  obtain ⟨c, D₁, D₂, hc, hD₁, hD₂, halg⟩ := mma_layer hn hαL (by positivity : 0 ≤ (4 * ηL)⁻¹)
    hCm hCf (by positivity : 0 ≤ ηL⁻¹ + 1)
  refine ⟨c, D₁, D₂, max (max Wm Wf) 1, hc, hD₁, hD₂, fun W hW E hE X hX l hl => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWm, hWf⟩, hW1⟩ := hW
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hηle : ηL ≤ etaZ b E := etaLow_le (by linarith) hκ hE
  have hη1 : etaZ b E ≤ 1 := bulk_eta_le_one hb0 hκ hE
  set μ := freshLaw W b
  obtain ⟨hm, hfl⟩ := hfr W hWf E hE X hX
  have hq0 := passiveMass_nonneg b E hX
  have hqc := qc_eq (b := b) (E := E) hX
  have hσ : 0 ≤ Cf / Real.sqrt W * passiveMass b E X := by
    have : 0 ≤ Cf := by linarith
    positivity
  have hexp := integral_pow_le_of_fluct μ n (measurable_qc_fresh b E X)
    (ae_of_all _ fun ω => qc_nonneg b E _) (ae_of_all _ fun ω => qc_le (by linarith) h1 h2 _) hσ
    hfl
  have hm0 : 0 ≤ ∫ ω, qc b E (freshSchur E X ω) ∂μ := integral_nonneg fun ω => qc_nonneg b E _
  have hqW : passiveMass b E X ≤ (4 * ηL)⁻¹ * W := by
    have := passiveMass_le_width (b := b) (by linarith) h1 h2 X
    rw [div_eq_inv_mul] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact inv_anti₀ (by positivity) (by linarith)
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hδb : jetDistance0 b E X ≤ ηL⁻¹ + 1 :=
    (jetDistance0_le_bound hb0 hb h1 h2 hX).trans (by linarith [inv_anti₀ hηL hηle])
  have hαα : αL ≤ alphaCoef b E := by
    rw [alphaCoef]
    have : 0 < (1 - b) ^ 2 := by have : 0 < 1 - b := by linarith
                                 positivity
    refine div_le_div_of_nonneg_left this.le (mul_pos hb0 hη) ?_
    nlinarith
  have hmq := hmean W hWm E hE X hX
  rw [← hm] at hmq
  have hmq' : ∫ ω, qc b E (freshSchur E X ω) ∂μ ≤
      passiveMass b E X / (1 + αL * passiveMass b E X / W) +
        Cm * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) * passiveMass b E X := by
    have := div_one_add_anti hq0 (by linarith : (0 : ℝ) < W) hαL.le hαα
    linarith
  rw [hqc]
  exact halg W (passiveMass b E X) _ (jetDistance0 b E X) _ hW1' hq0 hqW hδ0 hδb hm0 hmq' hexp l hl

end BlockBand.Transmission.LengthUniform
