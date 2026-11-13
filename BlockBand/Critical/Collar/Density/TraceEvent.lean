module

public import BlockBand.Critical.Collar.Density.Wegner
public import BlockBand.Layers.LayerContraction

/-!
# Trace concentration of the common port

Under `layerLaw W b .common`, `0 < b < 1/2`, conditional on a deterministic Hermitian `X` with
`matchedDistance b e X ≤ d_T` and for energies `e ∈ bulkInterval κ`, `0 < κ < 2`, the normalized
port trace of the layer resolvent deviates from `matchedA e` by more than `ε` with probability at
most `C_T / W²` (`layerLaw_trace_bad_le`).

Hypotheses: `TraceMatrixContract` and the external `PSSS.SourceContract`. The mean is the
common-port clause of `LayerContractionContract`, proved from PSSS as `Layers.layerContraction_holds`;
the fluctuation is the `fluctuation` field of `TraceMatrixContract` at `p = 2`, `D = Q_port`
(`‖Q_port‖ ≤ 1`), with Chebyshev's inequality.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ENNReal Matrix.Norms.L2Operator

variable {W : ℕ}

theorem norm_meqPortProj_le (j : Fin 1) :
    ‖(BlockBand.Layers.meqPortProj (W := W) (σ := .common) j)‖ ≤ 1 := by
  rw [BlockBand.Layers.meqPortProj, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun x => ?_
  rcases x with x | x
  · simp
  · simp only [Sum.elim_inr]
    split_ifs <;> simp

theorem portBlockTrace_eq_trace_mul (M : Matrix (LayerSite W .common) (LayerSite W .common) ℂ) :
    portBlockTrace M 0 = (W : ℂ)⁻¹ * (BlockBand.Layers.meqPortProj 0 * M).trace := by
  rw [BlockBand.Layers.meq_portBlockTrace_eq_word, BlockBand.Layers.meq_mul_eq_wordEval]

/-- **Trace concentration of the common port.** -/
theorem layerLaw_trace_bad_le (hTM : TraceMatrixContract)
    (source : BlockBand.External.PSSS.SourceContract.{0}) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ (dT CT : ℝ) (W₀ : ℕ), 0 < dT ∧ 0 ≤ CT ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ e ∈ bulkInterval κ, matchedDistance b e X ≤ dT →
        layerLaw W b .common {ω | ε < ‖portBlockTrace (layerResolvent .common e (commonZ b e) X ω) 0 -
            matchedA e‖} ≤ ENNReal.ofReal (CT / (W : ℝ) ^ 2) := by
  obtain ⟨dLC, CLC, qs, hdLC, -, -, hLC⟩ := BlockBand.Layers.layerContraction_holds
    (BlockBand.Wegner.conditionalBlockGUECount_holds source) b hb0 hb κ hκ
  have hm4 : 0 < 4 - (2 - κ) ^ 2 := BlockBand.Layers.four_sub_sq_pos hκ (by linarith)
  set η₀ : ℝ := (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 with hη₀
  have hη₀pos : 0 < η₀ := by
    have : 0 < 1 - 2 * b := by linarith
    have := Real.sqrt_pos.2 hm4
    positivity
  obtain ⟨ε₃, Cf, hε₃, hfl⟩ := hTM.fluctuation b hb0 hb η₀ 3 hη₀pos 1
  set CL : ℝ := max CLC 0
  set CF : ℝ := max Cf 0
  have hCL : 0 ≤ CL := le_max_right _ _
  have hCF : 0 ≤ CF := le_max_right _ _
  refine ⟨min dLC (ε / (4 * (CL + 1))), (2 / ε) ^ 2 * (CF * Real.sqrt 2) ^ 2,
    max (⌈2 / ε₃⌉₊) (⌈4 * CL / ε⌉₊ + 1), lt_min hdLC (by positivity), by positivity, ?_⟩
  intro W hW hW₀ X hX e he hd
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hWε₃ : 2 ≤ ε₃ * W := by
    have h1 : (⌈2 / ε₃⌉₊ : ℝ) ≤ W := by exact_mod_cast (le_max_left _ _).trans hW₀
    have h2 := Nat.le_ceil (2 / ε₃)
    rw [div_le_iff₀ hε₃] at h2
    nlinarith
  have hWC : 4 * CL / ε ≤ W := by
    have h1 : ((⌈4 * CL / ε⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast (le_max_right _ _).trans hW₀
    have h2 := Nat.le_ceil (4 * CL / ε)
    push_cast at h1
    linarith
  -- the mean
  have hmean := (hLC W hW X hX e he (hd.trans (min_le_left _ _))).2
  set f : LayerSample W .common → ℂ := fun ω =>
    (W : ℂ)⁻¹ * (BlockBand.Layers.meqPortProj 0 * layerResolvent .common e (commonZ b e) X ω).trace
    with hf
  have hfe : ∀ ω, portBlockTrace (layerResolvent .common e (commonZ b e) X ω) 0 = f ω := fun ω =>
    portBlockTrace_eq_trace_mul _
  simp_rw [hfe] at hmean ⊢
  have hzim : η₀ ≤ (commonZ b e).im := (BlockBand.Layers.commonZ_im_pos_of_mem_bulkInterval hb hκ he).2
  have he2 : |e| ≤ 2 := (BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ he).le
  have hz3 : ‖commonZ b e‖ ≤ 3 := BlockBand.Layers.norm_commonZ_le hb0.le (by linarith) he2
  have hflW := hfl W hW .common X hX e (commonZ b e) hzim hz3 (BlockBand.Layers.meqPortProj 0)
    (norm_meqPortProj_le 0) 2 le_rfl hWε₃
  simp only at hflW
  -- mean error at most `ε/2`
  have hmε : ‖(∫ ω, f ω ∂layerLaw W b .common) - matchedA e‖ ≤ ε / 2 := by
    refine hmean.trans ?_
    have h1 : CLC * matchedDistance b e X ≤ ε / 4 := by
      have hd' : matchedDistance b e X ≤ ε / (4 * (CL + 1)) := hd.trans (min_le_right _ _)
      have hd0 : 0 ≤ matchedDistance b e X := le_max_of_le_left (norm_nonneg _)
      calc CLC * matchedDistance b e X ≤ CL * matchedDistance b e X :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hd0
        _ ≤ (CL + 1) * (ε / (4 * (CL + 1))) := mul_le_mul (by linarith) hd' hd0 (by linarith)
        _ = ε / 4 := by field_simp
    have h2 : CLC / (W : ℝ) ^ 2 ≤ ε / 4 := by
      calc CLC / (W : ℝ) ^ 2 ≤ CL / W := by
            rw [div_le_div_iff₀ (by positivity) hWr]
            have h3 : CLC ≤ CL := le_max_left _ _
            have h4 : CLC * W ≤ CL * W := mul_le_mul_of_nonneg_right h3 hWr.le
            have h5 : CL * W ≤ CL * W ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hCL
            linarith
        _ ≤ ε / 4 := by
            rw [div_le_iff₀ hWr]
            rw [div_le_iff₀ hε] at hWC
            linarith
    linarith
  -- event inclusion
  set g : LayerSample W .common → ℂ := fun ω => f ω - ∫ ω', f ω' ∂layerLaw W b .common
  have hsub : {ω | ε < ‖f ω - matchedA e‖} ⊆ {ω | ENNReal.ofReal (ε / 2) ≤ ‖g ω‖ₑ} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    have : ‖f ω - matchedA e‖ ≤ ‖g ω‖ + ‖(∫ ω, f ω ∂layerLaw W b .common) - matchedA e‖ := by
      calc ‖f ω - matchedA e‖ = ‖g ω + ((∫ ω, f ω ∂layerLaw W b .common) - matchedA e)‖ := by
            simp only [g]; ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith
  refine (measure_mono hsub).trans ?_
  have hp : (ENNReal.ofReal 2).toReal = 2 := by simp
  have hcheb := mul_meas_ge_le_pow_eLpNorm' (layerLaw W b .common)
    (p := ENNReal.ofReal 2) (by simp) ENNReal.ofReal_ne_top (f := g) (ENNReal.ofReal (ε / 2))
  rw [hp, ENNReal.rpow_two, ENNReal.rpow_two] at hcheb
  have hε2 : (0 : ℝ) < ε / 2 := by positivity
  rw [← ENNReal.ofReal_pow hε2.le] at hcheb
  have hpos : ENNReal.ofReal ((ε / 2) ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl ENNReal.ofReal_ne_top)] at hcheb
  refine hcheb.trans ?_
  have hflW' : eLpNorm g (ENNReal.ofReal 2) (layerLaw W b .common) ≤
      ENNReal.ofReal (CF * Real.sqrt 2 / W) :=
    hflW.trans (ENNReal.ofReal_le_ofReal (by
      have : Cf ≤ CF := le_max_left _ _
      have := Real.sqrt_nonneg 2
      gcongr))
  have hL := pow_le_pow_left' hflW' 2
  refine (ENNReal.div_le_div_right hL _).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  field_simp

end BlockBand.Critical.Collar.Density
