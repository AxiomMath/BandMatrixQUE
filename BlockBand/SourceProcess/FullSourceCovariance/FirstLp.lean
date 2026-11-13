module

public import BlockBand.SourceProcess.FullSourceCovariance.SelfTau
public import BlockBand.SourceProcess.FullSource.DeltaMeanStrict

/-!
# Generic `L^p` tools for the first-term bound

Cauchy–Schwarz and Hölder bounds for integrals of products, and the three-way split of the first
term of the `Δ`-covariance.

* `norm_integral_mul_le_of`: `‖∫fg‖ ≤ AB` from `‖f‖₂ ≤ A`, `‖g‖₂ ≤ B` (Cauchy–Schwarz);
* `eLpNorm_mul_le_four`: `‖fg‖₂ ≤ ‖f‖₄‖g‖₄` (Hölder); `norm_integral_mul3_le`: `‖∫fgh‖ ≤ ABC`
  from `‖f‖₄, ‖g‖₄, ‖h‖₂`;
* `norm_integral_le_of`: `‖∫f‖ ≤ A` from `‖f‖₂ ≤ A`;
* **`first_split`**: `E[(Ω̄ + τ⁰)(m + F⁰)Ψ] = Ω̄E[F⁰Ψ] + mE[τ⁰Ψ] + E[τ⁰F⁰Ψ]` when `EΨ = 0`, and
  **`first_split_bound`**: `‖·‖ ≤ ‖Ω̄‖A_F A_Ψ + ‖m‖T + A_τA_FA_Ψ` when `‖E[τ⁰Ψ]‖ ≤ T`;
* **`poly_eLpNorm_bulk hA`**: `‖F‖₂ ≤ K·C_r` whenever `‖F‖ ≤ K(1+B)^r`, `B = btFun`, uniformly on
  `bulkInterval κ` (`moments` via `btFun_moment_bulk`).
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

section Generic
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem norm_integral_mul_le_of {f g : Ω → ℂ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hfA : eLpNorm f 2 μ ≤ ENNReal.ofReal A)
    (hgB : eLpNorm g 2 μ ≤ ENNReal.ofReal B) : ‖∫ ω, f ω * g ω ∂μ‖ ≤ A * B := by
  have h := (enorm_integral_mul_le μ f g hf hg).trans (mul_le_mul' hfA hgB)
  rw [← ENNReal.ofReal_mul hA, ← ofReal_norm] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA hB)).mp h

instance holderTriple_four_four_two : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := ⟨by
  change ((4 : ℝ≥0) : ℝ≥0∞)⁻¹ + ((4 : ℝ≥0) : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0) : ℝ≥0∞)⁻¹
  rw [← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
    ← ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ← ENNReal.coe_add]
  congr 1
  norm_num⟩

theorem eLpNorm_mul_le_four {f g : Ω → ℂ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun ω => f ω * g ω) 2 μ ≤ eLpNorm f 4 μ * eLpNorm g 4 μ := by
  exact eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (r := 2) (μ := μ) hf hg

theorem norm_integral_mul3_le {f g h : Ω → ℂ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hh : AEMeasurable h μ) {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hfA : eLpNorm f 4 μ ≤ ENNReal.ofReal A) (hgB : eLpNorm g 4 μ ≤ ENNReal.ofReal B)
    (hhC : eLpNorm h 2 μ ≤ ENNReal.ofReal C) : ‖∫ ω, f ω * g ω * h ω ∂μ‖ ≤ A * B * C := by
  have hfg : eLpNorm (fun ω => f ω * g ω) 2 μ ≤ ENNReal.ofReal (A * B) := by
    rw [ENNReal.ofReal_mul hA]
    exact (eLpNorm_mul_le_four hf hg).trans (mul_le_mul' hfA hgB)
  exact norm_integral_mul_le_of (hf.mul hg).aemeasurable hh (mul_nonneg hA hB) hC hfg hhC

theorem eLpNorm_two_le_four [IsProbabilityMeasure μ] (f : Ω → ℂ) :
    eLpNorm f 2 μ ≤ eLpNorm f 4 μ :=
  eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)

theorem norm_integral_le_of [IsProbabilityMeasure μ] {f : Ω → ℂ} (hf : AEMeasurable f μ) {A : ℝ}
    (hA : 0 ≤ A) (hfA : eLpNorm f 2 μ ≤ ENNReal.ofReal A) : ‖∫ ω, f ω ∂μ‖ ≤ A := by
  have h1 : eLpNorm (fun _ : Ω => (1 : ℂ)) 2 μ ≤ ENNReal.ofReal 1 := by
    rw [eLpNorm_const _ two_ne_zero (IsProbabilityMeasure.ne_zero μ)]; simp
  have := norm_integral_mul_le_of hf aemeasurable_const hA zero_le_one hfA h1
  simpa using this

/-- **The three-way split** of the first term (`EΨ = 0`). -/
theorem first_split [IsProbabilityMeasure μ] (Ωb m : ℂ) {τ0 F0 Ψ : Ω → ℂ} (hτ : MemLp τ0 4 μ)
    (hF : MemLp F0 4 μ) (hΨ : MemLp Ψ 2 μ) (hΨ0 : ∫ ω, Ψ ω ∂μ = 0) :
    ∫ ω, (Ωb + τ0 ω) * (m + F0 ω) * Ψ ω ∂μ =
      Ωb * ∫ ω, F0 ω * Ψ ω ∂μ + m * ∫ ω, τ0 ω * Ψ ω ∂μ + ∫ ω, τ0 ω * F0 ω * Ψ ω ∂μ := by
  have hτ2 : MemLp τ0 2 μ := hτ.mono_exponent (by norm_num)
  have hF2 : MemLp F0 2 μ := hF.mono_exponent (by norm_num)
  have i1 : Integrable (fun ω => F0 ω * Ψ ω) μ := hF2.integrable_mul hΨ
  have i2 : Integrable (fun ω => τ0 ω * Ψ ω) μ := hτ2.integrable_mul hΨ
  have hτF : MemLp (fun ω => τ0 ω * F0 ω) 2 μ := by
    exact hτ.smul (p := 4) (q := 4) (r := 2) hF
  have i3 : Integrable (fun ω => τ0 ω * F0 ω * Ψ ω) μ := hτF.integrable_mul hΨ
  have i4 : Integrable Ψ μ := hΨ.integrable one_le_two
  have e : (fun ω => (Ωb + τ0 ω) * (m + F0 ω) * Ψ ω) = fun ω =>
      Ωb * (F0 ω * Ψ ω) + (Ωb * m) * Ψ ω + m * (τ0 ω * Ψ ω) + τ0 ω * F0 ω * Ψ ω := by
    funext ω; ring
  have j1 : Integrable (fun ω => Ωb * (F0 ω * Ψ ω) + (Ωb * m) * Ψ ω) μ :=
    (i1.const_mul _).add (i4.const_mul _)
  have j2 : Integrable (fun ω => Ωb * (F0 ω * Ψ ω) + (Ωb * m) * Ψ ω + m * (τ0 ω * Ψ ω)) μ :=
    j1.add (i2.const_mul _)
  rw [e, integral_add j2 i3, integral_add j1 (i2.const_mul _),
    integral_add (i1.const_mul _) (i4.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, hΨ0, mul_zero, add_zero]

/-- **The three-way split, bounded.** -/
theorem first_split_bound [IsProbabilityMeasure μ] (Ωb m : ℂ) {τ0 F0 Ψ : Ω → ℂ}
    (hτ : MemLp τ0 4 μ) (hF : MemLp F0 4 μ) (hΨ : MemLp Ψ 2 μ) (hΨ0 : ∫ ω, Ψ ω ∂μ = 0)
    {Aτ AF AΨ T : ℝ} (hAτ : 0 ≤ Aτ) (hAF : 0 ≤ AF) (hAΨ : 0 ≤ AΨ)
    (hτA : eLpNorm τ0 4 μ ≤ ENNReal.ofReal Aτ) (hFA : eLpNorm F0 4 μ ≤ ENNReal.ofReal AF)
    (hΨA : eLpNorm Ψ 2 μ ≤ ENNReal.ofReal AΨ) (hT : ‖∫ ω, τ0 ω * Ψ ω ∂μ‖ ≤ T) :
    ‖∫ ω, (Ωb + τ0 ω) * (m + F0 ω) * Ψ ω ∂μ‖ ≤ ‖Ωb‖ * (AF * AΨ) + ‖m‖ * T + Aτ * AF * AΨ := by
  rw [first_split Ωb m hτ hF hΨ hΨ0]
  have h1 : ‖∫ ω, F0 ω * Ψ ω ∂μ‖ ≤ AF * AΨ :=
    norm_integral_mul_le_of hF.aestronglyMeasurable.aemeasurable
      hΨ.aestronglyMeasurable.aemeasurable hAF hAΨ ((eLpNorm_two_le_four F0).trans hFA) hΨA
  have h3 : ‖∫ ω, τ0 ω * F0 ω * Ψ ω ∂μ‖ ≤ Aτ * AF * AΨ :=
    norm_integral_mul3_le hτ.aestronglyMeasurable hF.aestronglyMeasurable
      hΨ.aestronglyMeasurable.aemeasurable hAτ hAF hAΨ hτA hFA hΨA
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) h3)
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_left hT (norm_nonneg _)

end Generic

variable {W : ℕ}

/-- **`‖F‖₂ ≤ K·C` from `‖F‖ ≤ K(1+B)^r`**, `C, W₀` uniform on `bulkInterval κ`. -/
theorem poly_eLpNorm_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (r : ℕ) (hr : 1 ≤ r) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ (F : LayerSample W .oneBlockOnePort → ℂ), AEStronglyMeasurable F (freshLaw W b) →
      ∀ K : ℝ, 0 ≤ K → (∀ ω, ‖F ω‖ ≤ K * (1 + btFun b E X ω) ^ r) →
        eLpNorm F 2 (freshLaw W b) ≤ ENNReal.ofReal (K * C) := by
  obtain ⟨C, W₀, hC, hm⟩ := LengthUniform.btFun_moment_bulk hA hb0 hb hκ (2 * (r : ℕ)) (by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith)
  refine ⟨C ^ r, W₀, by positivity, fun W hW E hE X hX F hF K hK hFK => ?_⟩
  have hg := eLpNorm_pow_le (μ := layerLaw W b .oneBlockOnePort)
    (g := fun ω => 1 + btFun b E X ω) (fun ω => by have := btFun_nonneg b E X ω; positivity)
    (measurable_const.add (measurable_btFun b E X)).aestronglyMeasurable r hr (hm W hW E hE X hX)
  have h1 : eLpNorm F 2 (freshLaw W b) ≤
      eLpNorm (fun ω => K * (1 + btFun b E X ω) ^ r) 2 (freshLaw W b) :=
    eLpNorm_mono_real hF hFK
  have h2 : eLpNorm (fun ω => K * (1 + btFun b E X ω) ^ r) 2 (freshLaw W b) =
      ‖K‖ₑ * eLpNorm (fun ω => (1 + btFun b E X ω) ^ r) 2 (freshLaw W b) := by
    have := eLpNorm_const_smul K (fun ω => (1 + btFun b E X ω) ^ r) 2 (freshLaw W b)
    simpa only [Pi.smul_def, smul_eq_mul] using this
  rw [h2] at h1
  refine h1.trans ((mul_le_mul' le_rfl hg).trans (le_of_eq ?_))
  rw [← ofReal_norm, Real.norm_of_nonneg hK, ← ENNReal.ofReal_pow hC, ← ENNReal.ofReal_mul hK]

end BlockBand.SourceProcess.FullSourceCovariance
