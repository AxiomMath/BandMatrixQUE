module

public import BlockBand.SourceProcess.CompleteSourceGap.GapMeanHolds

/-!
# Integrability of the transported separators

Hypothesis: `GaussianAbsorptionContract` (through `fullSourceMoments_field_holds`).

**`integrable_transportedSep`**: for fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`, there is `W₀` such that for
`W ≥ W₀`, every Hermitian `𝕏` and **every** separator `σ`, the operator norm and every entry of
`N·sepOf(𝕏₊)σ·N*` are `freshLaw`-integrable, with `E‖N·sepOf(𝕏₊)σ·N*‖ ≤ C` uniformly in `𝕏`.
Proof: `𝕏₊ = freshTwoPortSchur E 𝕏 ω` is Hermitian a.s. (`freshTwoPortSchur_isHermitian`), so
`‖sepOf 𝕏₊ σ‖ ≤ 1` (`𝕊` unitary, `‖P‖ ≤ 1`), hence `‖N·sepOf·N*‖ ≤ ‖N‖²` a.s., and
`‖N‖ ∈ L²` uniformly (`fullSourceMoments_field_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGap

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem norm_nearProjection_le : ‖nearProjection W‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (nearProjection W)
  rw [nearProjection_conjTranspose, nearProjection_mul_self] at h
  have := norm_nonneg (nearProjection W)
  nlinarith

/-- `‖sepOf 𝕐 σ‖ ≤ 1` for Hermitian `𝕐`. -/
theorem norm_sepOf_le (b E : ℝ) {Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : Y.IsHermitian) (hη : 0 < etaZ b E) (σ : Separator) : ‖sepOf b E Y σ‖ ≤ 1 := by
  have hP := norm_nearProjection_le (W := W)
  have hS := norm_scat_le b E hY hη
  have hS' : ‖(twoPortScattering b E Y)ᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hS
  have m2 : ∀ A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ‖A * B‖ ≤ 1 :=
    fun A B hA hB => (Matrix.l2_opNorm_mul A B).trans (by nlinarith [norm_nonneg A, norm_nonneg B])
  cases σ
  · exact BlockBand.Transmission.PassiveCovariance.norm_one_matrix_le
  · exact hP
  · exact m2 _ _ hP hS
  · exact m2 _ _ hS' hP
  · exact m2 _ _ (m2 _ _ hP hS) hP
  · exact m2 _ _ (m2 _ _ hP hS') hP

theorem measurable_twoPortScattering (b E : ℝ) :
    Measurable fun Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => twoPortScattering b E Y := by
  have hR : Measurable fun Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
      twoPortResolvent b E Y :=
    measurable_matrix_inv.comp (measurable_const.sub measurable_id)
  exact measurable_const.sub (hR.const_smul (((2 * etaZ b E : ℝ) : ℂ) * Complex.I))

theorem measurable_sepOf (b E : ℝ) (σ : Separator) :
    Measurable fun Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => sepOf b E Y σ := by
  have hS := measurable_twoPortScattering (W := W) b E
  have hS' := measurable_matrix_conjTranspose' hS
  have hP : Measurable fun _ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => nearProjection W :=
    measurable_const
  cases σ
  · exact measurable_const
  · exact measurable_const
  · exact measurable_matrix_mul' hP hS
  · exact measurable_matrix_mul' hS' hP
  · exact measurable_matrix_mul' (measurable_matrix_mul' hP hS) hP
  · exact measurable_matrix_mul' (measurable_matrix_mul' hP hS') hP

theorem measurable_ofPortBlocks {α : Type*} [MeasurableSpace α]
    {f₀₀ f₀₁ f₁₀ f₁₁ : α → Matrix (Fin W) (Fin W) ℂ} (h₀₀ : Measurable f₀₀)
    (h₀₁ : Measurable f₀₁) (h₁₀ : Measurable f₁₀) (h₁₁ : Measurable f₁₁) :
    Measurable fun a => ofPortBlocks (f₀₀ a) (f₀₁ a) (f₁₀ a) (f₁₁ a) := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  fin_cases i <;> fin_cases j
  · exact h₀₀.eval_matrix
  · exact h₀₁.eval_matrix
  · exact h₁₀.eval_matrix
  · exact h₁₁.eval_matrix

theorem measurable_freshTwoPortSchur (E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable (freshTwoPortSchur E XX) := by
  have hA : Measurable fun ω : LayerSample W .oneBlockOnePort => ω.1 0 :=
    (measurable_pi_apply 0).comp measurable_fst
  have hB : Measurable fun ω : LayerSample W .oneBlockOnePort => ω.2 0 0 :=
    (measurable_pi_apply 0).comp ((measurable_pi_apply 0).comp measurable_snd)
  have hBs := measurable_matrix_conjTranspose' hB
  have hG : Measurable fun ω : LayerSample W .oneBlockOnePort =>
      (ω.1 0 - (E : ℂ) • 1 - portBlock XX 0 0)⁻¹ :=
    measurable_matrix_inv.comp ((hA.sub measurable_const).sub measurable_const)
  have hc : ∀ M : Matrix (Fin W) (Fin W) ℂ,
      Measurable fun _ : LayerSample W .oneBlockOnePort => M := fun M => measurable_const
  exact measurable_ofPortBlocks (measurable_matrix_mul' (measurable_matrix_mul' hBs hG) hB)
    (measurable_matrix_mul' (measurable_matrix_mul' hBs hG) (hc _)).neg
    (measurable_matrix_mul' (measurable_matrix_mul' (hc _) hG) hB).neg
    ((hc _).add (measurable_matrix_mul' (measurable_matrix_mul' (hc _) hG) (hc _)))

theorem measurable_transportedSep (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (σ : Separator) : Measurable (transportedSep b E XX σ) := by
  have hN : Measurable fun ω => freshTransport b E XX ω :=
    FullSource.measurable_freshTransport_comp b E measurable_const measurable_id
  have hS := (measurable_sepOf (W := W) b E σ).comp (measurable_freshTwoPortSchur E XX)
  exact measurable_matrix_mul' (measurable_matrix_mul' hN hS) (measurable_matrix_conjTranspose' hN)

/-- **Integrability of `N·sepOf(𝕏₊)σ·N*`**, uniformly over Hermitian `𝕏` and all separators. -/
theorem integrable_transportedSep (hGA : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {E : ℝ} (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian → ∀ σ : Separator,
        Integrable (fun ω => ‖transportedSep b E XX σ ω‖) (freshLaw W b) ∧
        ∫ ω, ‖transportedSep b E XX σ ω‖ ∂freshLaw W b ≤ C ∧
        ∀ a c, Integrable (fun ω => transportedSep b E XX σ ω a c) (freshLaw W b) := by
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hE := BlockBand.Transmission.PassiveLayer.mem_bulkInterval_min E
  have hη := BlockBand.Transmission.PassiveCovariance.etaZ_pos b E (by linarith) h1 h2
  obtain ⟨C, W₀, hM⟩ := FullSource.fullSourceMoments_field_holds hGA b hb0 hb _ hκ 2 (by norm_num)
  set Cm := max C 0
  have hCm : 0 ≤ Cm := le_max_right _ _
  refine ⟨Cm ^ 2, W₀, fun W hW XX hXX σ => ?_⟩
  set μ := freshLaw W b
  have hN : Measurable fun ω => freshTransport b E XX ω :=
    FullSource.measurable_freshTransport_comp b E measurable_const measurable_id
  have hNm : BlockBand.Transmission.PassiveLayer.MomBd μ (fun ω => ‖freshTransport b E XX ω‖)
      ((2 : ℕ) : ℝ) Cm := by
    refine ⟨(continuous_norm.measurable.comp hN).aestronglyMeasurable, ?_⟩
    have := (hM W hW E hE XX hXX).1
    rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]
    exact this.trans (ENNReal.ofReal_le_ofReal (le_max_left C 0))
  obtain ⟨hsq, hsqI⟩ := FullSource.integral_abs_pow_le (ν := μ) (n := 2) (by norm_num) hCm hNm
  have hTm := measurable_transportedSep b E XX σ
  have hT : ∀ᵐ ω ∂μ, ‖transportedSep b E XX σ ω‖ ≤ |‖freshTransport b E XX ω‖| ^ 2 := by
    filter_upwards [BlockBand.Transmission.PathScalar.ae_layer_herm (W := W) b] with ω hω
    have hS := norm_sepOf_le b E (freshTwoPortSchur_isHermitian E hXX hω) hη σ
    set Nω := freshTransport b E XX ω
    have hn := norm_nonneg Nω
    rw [abs_norm, sq]
    calc ‖transportedSep b E XX σ ω‖
        ≤ ‖Nω * sepOf b E (freshTwoPortSchur E XX ω) σ‖ * ‖Nωᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Nω‖ * 1) * ‖Nω‖ := by
          rw [Matrix.l2_opNorm_conjTranspose]
          exact mul_le_mul_of_nonneg_right ((Matrix.l2_opNorm_mul _ _).trans
            (mul_le_mul_of_nonneg_left hS hn)) hn
      _ = ‖Nω‖ * ‖Nω‖ := by ring
  have hTi : Integrable (fun ω => ‖transportedSep b E XX σ ω‖) μ :=
    hsq.mono' (continuous_norm.measurable.comp hTm).aestronglyMeasurable
      (hT.mono fun ω h => by rw [norm_norm]; exact h)
  refine ⟨hTi, (integral_mono_ae hTi hsq hT).trans hsqI, fun a c => ?_⟩
  exact hsq.mono' hTm.eval_matrix.aestronglyMeasurable
    (hT.mono fun ω h => (FullSource.norm_entry_le_op _ a c).trans h)

end BlockBand.SourceProcess.CompleteSourceGap
