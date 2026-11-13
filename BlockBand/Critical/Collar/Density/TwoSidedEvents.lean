module

public import BlockBand.Critical.Collar.Density.RegularBound
public import BlockBand.Layers.ScalarRecursion

/-!
# Events and the scalar error of the collar

*Law.* `layerLaw W b .common`, `0 < b < 1/2`, deterministic Hermitian `X` (no norm bound).

* `ae_isUnit_det_collarTopBlock`: `D = A - e - X` is a.s. invertible (polynomial null set,
  `Layers.srec_pi_gue_det_null`).
* `lintegral_traceDefect_sq_le` (**Step 1**): `E e_AB² ≤ C_χ(d(X) + W⁻¹)²`,
  `e_AB = |W⁻¹ Tr 𝒢_port - a|`, for `W ≥ W₀`, `d(X) ≤ d_T`, `e ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `D = A - e - X` is invertible `layerLaw`-a.s. (every `W ≥ 1`, `b < 1/2`, real `e`, every
`X`). -/
theorem ae_isUnit_det_collarTopBlock {b : ℝ} (hb : b < 1 / 2) (hW : 0 < W) (e : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ∀ᵐ ω ∂layerLaw W b .common, IsUnit (collarTopBlock e X ω).det := by
  set t := Real.toNNReal ((1 - 2 * b) / W)
  have ht : t ≠ 0 :=
    (Real.toNNReal_pos.2 (div_pos (by linarith) (by exact_mod_cast hW))).ne'
  have h1 : ∀ᵐ A ∂(Measure.pi fun _ : Fin 2 => gueMeasure (Fin W) t),
      IsUnit (BlockBand.Internal.Contracts.Layers.blockDiag A - (e : ℂ) • 1 - X).det := by
    rw [ae_iff]
    have := BlockBand.Layers.srec_pi_gue_det_null W 2 ht (-((e : ℂ) • 1) - X)
    refine measure_mono_null (fun A hA => ?_) this
    simp only [Set.mem_ofPred_eq, isUnit_iff_ne_zero, not_not] at hA ⊢
    rw [← hA]; congr 1; abel
  exact (Measure.quasiMeasurePreserving_fst (μ := Measure.pi fun _ : Fin 2 =>
    gueMeasure (Fin W) t) (ν := Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 1 =>
      ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)))).ae h1

/-- **Step 1 of the paper's proof** (`‖e_AB‖_{L²} ≤ C(d(X) + W⁻¹)`): the scalar error
`e_AB = |W⁻¹ Tr 𝒢_port - a|` of the conditional collar has
`E e_AB² ≤ C_χ (d(X) + W⁻¹)²` for `W ≥ W₀`, Hermitian `X` with `d(X) ≤ d_T`, `e ∈ bulkInterval κ`.
Mean: the common-port clause of `LayerContractionContract` (proved constructor
`Layers.layerContraction_holds` from PSSS); fluctuation: `TraceMatrixContract.fluctuation` at
`p = 2`. -/
theorem lintegral_traceDefect_sq_le (hTM : TraceMatrixContract)
    (source : BlockBand.External.PSSS.SourceContract.{0}) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ (dT Cχ : ℝ) (W₀ : ℕ), 0 < dT ∧ 0 ≤ Cχ ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ e ∈ bulkInterval κ, matchedDistance b e X ≤ dT →
        ∫⁻ ω, ENNReal.ofReal (‖portBlockTrace (layerResolvent .common e (commonZ b e) X ω) 0 -
            matchedA e‖ ^ 2) ∂layerLaw W b .common ≤
          ENNReal.ofReal (Cχ * (matchedDistance b e X + 1 / (W : ℝ)) ^ 2) := by
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
  refine ⟨dLC, 4 * CF ^ 2 + 2 * CL ^ 2, ⌈2 / ε₃⌉₊, hdLC, by positivity, ?_⟩
  intro W hW hW₀ X hX e he hd
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hWε₃ : 2 ≤ ε₃ * W := by
    have h1 : (⌈2 / ε₃⌉₊ : ℝ) ≤ W := by exact_mod_cast hW₀
    have h2 := Nat.le_ceil (2 / ε₃)
    rw [div_le_iff₀ hε₃] at h2
    nlinarith
  have hmean := (hLC W hW X hX e he hd).2
  have : IsProbabilityMeasure (layerLaw W b .common) := by unfold layerLaw; infer_instance
  set μ := layerLaw W b .common
  set f : LayerSample W .common → ℂ := fun ω =>
    (W : ℂ)⁻¹ * (BlockBand.Layers.meqPortProj 0 * layerResolvent .common e (commonZ b e) X ω).trace
    with hf
  have hfe : ∀ ω, portBlockTrace (layerResolvent .common e (commonZ b e) X ω) 0 = f ω := fun ω =>
    portBlockTrace_eq_trace_mul _
  simp_rw [hfe] at hmean ⊢
  have hzim : η₀ ≤ (commonZ b e).im :=
    (BlockBand.Layers.commonZ_im_pos_of_mem_bulkInterval hb hκ he).2
  have he2 : |e| ≤ 2 := (BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ he).le
  have hz3 : ‖commonZ b e‖ ≤ 3 := BlockBand.Layers.norm_commonZ_le hb0.le (by linarith) he2
  have hflW := hfl W hW .common X hX e (commonZ b e) hzim hz3 (BlockBand.Layers.meqPortProj 0)
    (norm_meqPortProj_le 0) 2 le_rfl hWε₃
  simp only at hflW
  set d := matchedDistance b e X
  have hd0 : 0 ≤ d := le_max_of_le_left (norm_nonneg _)
  set m := ‖(∫ ω, f ω ∂μ) - matchedA e‖
  have hm : m ≤ CL * (d + 1 / W) := by
    refine hmean.trans ?_
    have h1 : 1 / (W : ℝ) ^ 2 ≤ 1 / W := by
      rw [div_le_div_iff₀ (by positivity) hWr]; nlinarith
    calc CLC * d + CLC / (W : ℝ) ^ 2 ≤ CL * d + CL * (1 / (W : ℝ) ^ 2) := by
          rw [mul_one_div]
          gcongr
          · exact le_max_left _ _
          · exact le_max_left _ _
      _ ≤ CL * d + CL * (1 / W) := by gcongr
      _ = CL * (d + 1 / W) := by ring
  set g : LayerSample W .common → ℂ := fun ω => f ω - ∫ ω', f ω' ∂μ
  have hgm : Measurable g := by
    have : Measurable f := by
      have hc : Continuous fun M : Matrix (LayerSite W .common) (LayerSite W .common) ℂ =>
          (W : ℂ)⁻¹ * (BlockBand.Layers.meqPortProj 0 * M).trace :=
        continuous_const.mul ((continuous_const.matrix_mul continuous_id).matrix_trace)
      exact hc.measurable.comp (BlockBand.Layers.measurable_layerResolvent .common e _ X)
    exact this.sub measurable_const
  -- pointwise
  have hpt : ∀ ω, ENNReal.ofReal (‖f ω - matchedA e‖ ^ 2) ≤
      2 * ‖g ω‖ₑ ^ (2 : ℝ) + ENNReal.ofReal (2 * m ^ 2) := by
    intro ω
    have h1 : ‖f ω - matchedA e‖ ≤ ‖g ω‖ + m := by
      calc ‖f ω - matchedA e‖ = ‖g ω + ((∫ ω, f ω ∂μ) - matchedA e)‖ := by
            simp only [g]; ring_nf
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖f ω - matchedA e‖ ^ 2 ≤ 2 * ‖g ω‖ ^ 2 + 2 * m ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖g ω‖ - m)]
    calc ENNReal.ofReal (‖f ω - matchedA e‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖g ω‖ ^ 2 + 2 * m ^ 2) :=
          ENNReal.ofReal_le_ofReal h2
      _ = 2 * ‖g ω‖ₑ ^ (2 : ℝ) + ENNReal.ofReal (2 * m ^ 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_two]
          simp
  have hL2 : ∫⁻ ω, ‖g ω‖ₑ ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal ((CF * Real.sqrt 2 / W) ^ 2) := by
    have hflW' : eLpNorm g (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal (CF * Real.sqrt 2 / W) :=
      hflW.trans (ENNReal.ofReal_le_ofReal (by
        have : Cf ≤ CF := le_max_left _ _
        have := Real.sqrt_nonneg 2
        gcongr))
    rw [eLpNorm_eq_eLpNorm' (by simp) ENNReal.ofReal_ne_top hgm.aestronglyMeasurable] at hflW'
    have hp : (ENNReal.ofReal 2).toReal = 2 := by simp
    rw [hp] at hflW'
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_pow (by positivity), ← ENNReal.rpow_two]
    exact ENNReal.rpow_le_rpow hflW' (by norm_num)
  calc ∫⁻ ω, ENNReal.ofReal (‖f ω - matchedA e‖ ^ 2) ∂μ
      ≤ ∫⁻ ω, (2 * ‖g ω‖ₑ ^ (2 : ℝ) + ENNReal.ofReal (2 * m ^ 2)) ∂μ := lintegral_mono hpt
    _ = 2 * ∫⁻ ω, ‖g ω‖ₑ ^ (2 : ℝ) ∂μ + ENNReal.ofReal (2 * m ^ 2) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ ((hgm.enorm).pow_const _)]
    _ ≤ 2 * ENNReal.ofReal ((CF * Real.sqrt 2 / W) ^ 2) + ENNReal.ofReal (2 * m ^ 2) := by
        gcongr
    _ = ENNReal.ofReal (2 * (CF * Real.sqrt 2 / W) ^ 2 + 2 * m ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num)]
        simp
    _ ≤ ENNReal.ofReal ((4 * CF ^ 2 + 2 * CL ^ 2) * (d + 1 / W) ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have h1 : 2 * (CF * Real.sqrt 2 / W) ^ 2 = 4 * CF ^ 2 * (1 / W) ^ 2 := by
          rw [div_pow, mul_pow, hs]; field_simp; ring
        have h2 : (1 / (W : ℝ)) ^ 2 ≤ (d + 1 / W) ^ 2 := by
          have : (0 : ℝ) ≤ 1 / W := by positivity
          gcongr; linarith
        have h3 : m ^ 2 ≤ CL ^ 2 * (d + 1 / W) ^ 2 := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hm 2
        rw [h1]
        nlinarith

end BlockBand.Critical.Collar.Density
