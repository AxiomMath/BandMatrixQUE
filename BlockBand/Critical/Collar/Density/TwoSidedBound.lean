module

public import BlockBand.Critical.Collar.Density.TwoSidedAlgebra
public import BlockBand.Critical.Collar.Density.TwoSidedEvents
public import BlockBand.Critical.Collar.Density.TwoSidedAbstract

/-!
# The two-sided conditional collar mean at `s = 0`

*Law.* `layerLaw W b .common` (end diagonals `A_j ~ GUE_W(c/W)`, bonds `Gin(b/W)`), `0 < b < 1/2`,
`c = 1 - 2b`; deterministic Hermitian `X` (no norm bound); `e ∈ bulkInterval κ`, `0 < κ < 2`.

**Main result** `lintegral_condCollarDensity_two_sided`: there are `d_S > 0`, `C_S ≥ 0`, a sequence
`ε_S W → 0` and `W₀` such that for `W ≥ W₀`, `e ∈ bulkInterval κ`, Hermitian `X` with `d(X) ≤ d_S`
and every `q`, `E_{A,B} q*K_X T Σ_F(0) T* K_X* q = (η/π)‖q‖² ± C_S(d(X) + ε_S W)‖q‖²`
(two lintegral inequalities), `η = Im z_b`, `ε_S W = W⁻¹ + ε_W^{rel} + W^{-1/2}`.

Proof. Regular event: `A` Hermitian, `D` invertible, `‖D⁻¹‖ ≤ W³`,
`Σ|B_xy|² ≤ W³`, `e_AB ≤ ε_t`; its complement has probability `≤ C_bad/W²`. On it, `F` is in the
fresh class (`‖F‖ ≤ W⁷`), `relativeMatrixDensity` and the certificate give
`|f - ρ(E)c‖L*q‖²| ≤ (k₁e_AB + k₂ε_W)‖L*q‖²` (`quadForm_condCollarDensity_two_sided`). Always
`0 ≤ f ≤ 2C_g√W‖L*q‖²` (`globalWeightedDensity_general`). Expectations:
`CommonPortMeanContract.mean`
(`E LL* = γI + O(d + W⁻²)`), `.moments` (`E‖L‖⁴ ≤ C`), the trace-defect bound
(`E e_AB² ≤ C(d + W⁻¹)²`, `lintegral_traceDefect_sq_le`), and `lintegral_two_sided_of_pointwise`.
The leading constant is `ρ(E)cγ = (1 - b)(-Im a)/π = η/π` (`boundaryZ_im`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem freshDyson_im_nonneg {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) :
    0 ≤ (freshDyson F s z).im := by
  unfold freshDyson
  split_ifs with h
  · exact (Classical.choose_spec h).1.le
  · simp

theorem measurable_traceDefect (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable fun ω : LayerSample W .common =>
      ‖portBlockTrace (layerResolvent .common e (commonZ b e) X ω) 0 - matchedA e‖ := by
  have hc : Continuous fun M : Matrix (LayerSite W .common) (LayerSite W .common) ℂ =>
      ‖(W : ℂ)⁻¹ * (BlockBand.Layers.meqPortProj 0 * M).trace - matchedA e‖ :=
    ((continuous_const.mul ((continuous_const.matrix_mul continuous_id).matrix_trace)).sub
      continuous_const).norm
  have h := hc.measurable.comp
    (BlockBand.Layers.measurable_layerResolvent .common e (commonZ b e) X)
  convert h using 2 with ω
  simp only [Function.comp_apply]
  rw [portBlockTrace_eq_trace_mul]

/-- The scalar step from the pointwise comparison to the `k₁χ + k₂` form. -/
theorem coef_le {Cc χ εt ε c Q : ℝ} (hCc : 0 ≤ Cc) (hχ0 : 0 ≤ χ) (hχ : χ ≤ εt) (hε : 0 ≤ ε)
    (hc : 0 ≤ c) (hQ : 0 ≤ Q) :
    (Cc * χ / Real.pi + ε + (Real.pi⁻¹ + Cc * χ / Real.pi + ε) * (Cc * χ)) * (c * Q) ≤
      c * (Cc / Real.pi + (Real.pi⁻¹ + Cc * εt / Real.pi) * Cc) * χ * Q +
        c * (1 + Cc * εt) * ε * Q := by
  have hpi := Real.pi_pos
  have hcq : 0 ≤ c * Q := mul_nonneg hc hQ
  have h1 : Cc * χ / Real.pi * (Cc * χ) ≤ Cc * εt / Real.pi * (Cc * χ) := by
    have : Cc * χ / Real.pi ≤ Cc * εt / Real.pi := by gcongr
    exact mul_le_mul_of_nonneg_right this (mul_nonneg hCc hχ0)
  have h2 : ε * (Cc * χ) ≤ ε * (Cc * εt) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hχ hCc) hε
  have key : Cc * χ / Real.pi + ε + (Real.pi⁻¹ + Cc * χ / Real.pi + ε) * (Cc * χ) ≤
      (Cc / Real.pi + (Real.pi⁻¹ + Cc * εt / Real.pi) * Cc) * χ + (1 + Cc * εt) * ε := by
    have e1 : (Real.pi⁻¹ + Cc * χ / Real.pi + ε) * (Cc * χ) =
        Real.pi⁻¹ * (Cc * χ) + Cc * χ / Real.pi * (Cc * χ) + ε * (Cc * χ) := by ring
    have e2 : (Cc / Real.pi + (Real.pi⁻¹ + Cc * εt / Real.pi) * Cc) * χ + (1 + Cc * εt) * ε =
        Cc * χ / Real.pi + Real.pi⁻¹ * (Cc * χ) + Cc * εt / Real.pi * (Cc * χ) + ε +
          ε * (Cc * εt) := by ring
    rw [e1, e2]
    linarith
  calc _ ≤ ((Cc / Real.pi + (Real.pi⁻¹ + Cc * εt / Real.pi) * Cc) * χ + (1 + Cc * εt) * ε) *
        (c * Q) := mul_le_mul_of_nonneg_right key hcq
    _ = _ := by ring

theorem one_div_sq_le_one_div {w : ℝ} (hw : 1 ≤ w) : 1 / w ^ 2 ≤ 1 / w := by
  have h0 : 0 < w := by linarith
  rw [div_le_div_iff₀ (by positivity) h0]; nlinarith

theorem aux_e3 {s nq : ℝ} (hs : 0 < s) (hnq : 0 < nq) (Cg Cbad C4 : ℝ) :
    nq * s * (2 * (Cg * s)) ^ 2 * (Cbad / (s ^ 2) ^ 2) + C4 ^ 4 * nq ^ 2 / (nq * s) =
      (4 * Cg ^ 2 * Cbad + C4 ^ 4) * nq * (1 / s) := by
  field_simp; ring

/-- The error budget of the two-sided bound (pure arithmetic). -/
theorem budget_two_sided {nq d εN w1 w2 s1 D1 Dt ρc IQ γ L c K₁ K₂ Cχ C4 Cbad Cg Cm δ₀ CS : ℝ}
    (hnq : 0 ≤ nq) (hd : 0 ≤ d) (hεN : 0 ≤ εN) (hw1 : 0 ≤ w1) (hs1 : 0 ≤ s1) (hw20 : 0 ≤ w2)
    (hw2 : w2 ≤ w1) (hδ₀ : 0 ≤ δ₀)
    (hw2' : w2 ≤ 1) (hD1 : D1 = d + w1) (hDt : Dt = d + (w1 + εN + s1)) (hρc : ρc ≤ c / Real.pi)
    (hρc0 : 0 ≤ ρc) (hIQ : |IQ - γ * nq| ≤ Cm * (d + w2) * nq) (hdδ : d ≤ δ₀)
    (hlead : ρc * (γ * nq) = L * nq)
    (hc : 0 ≤ c) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hCχ : 0 ≤ Cχ) (hCbad : 0 ≤ Cbad)
    (hCm : 0 ≤ Cm) (hγ : 0 ≤ γ)
    (hCS : CS = c / Real.pi * Cm + c * K₂ * (γ + Cm * (δ₀ + 1)) + c * K₁ * (Cχ + C4 ^ 4) / 2 +
      (4 * Cg ^ 2 * Cbad + C4 ^ 4) / 2 + c / Real.pi * (Cbad + C4 ^ 4) / 2) :
    L * nq - CS * Dt * nq ≤ ρc * IQ - (c * K₂ * εN * IQ +
        c * K₁ * ((Cχ + C4 ^ 4) * nq * D1) / 2 + ρc * ((Cbad + C4 ^ 4) * nq * w1) / 2) ∧
      ρc * IQ + c * K₂ * εN * IQ + c * K₁ * ((Cχ + C4 ^ 4) * nq * D1) / 2 +
          (4 * Cg ^ 2 * Cbad + C4 ^ 4) * nq * s1 / 2 ≤ L * nq + CS * Dt * nq := by
  have hIQ' := abs_le.1 hIQ
  have hb1 : d + w2 ≤ Dt := by rw [hDt]; linarith
  have hb2 : εN ≤ Dt := by rw [hDt]; linarith
  have hb3 : D1 ≤ Dt := by rw [hDt, hD1]; linarith
  have hb4 : w1 ≤ Dt := by rw [hDt]; linarith
  have hb5 : s1 ≤ Dt := by rw [hDt]; linarith
  have hDt0 : 0 ≤ Dt := hd.trans (by rw [hDt]; linarith)
  have hIQle : IQ ≤ (γ + Cm * (δ₀ + 1)) * nq := by
    have : Cm * (d + w2) * nq ≤ Cm * (δ₀ + 1) * nq :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hCm) hnq
    nlinarith [hIQ'.2]
  have t1 : ρc * (Cm * (d + w2) * nq) ≤ c / Real.pi * Cm * Dt * nq := by
    have h := mul_le_mul hρc (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb1 hCm) hnq)
      (by positivity) (by positivity)
    calc _ ≤ c / Real.pi * (Cm * Dt * nq) := h
      _ = _ := by ring
  have t2 : c * K₂ * εN * IQ ≤ c * K₂ * (γ + Cm * (δ₀ + 1)) * Dt * nq := by
    have h1 : c * K₂ * εN * IQ ≤ c * K₂ * εN * ((γ + Cm * (δ₀ + 1)) * nq) :=
      mul_le_mul_of_nonneg_left hIQle (by positivity)
    have h2 : c * K₂ * εN * ((γ + Cm * (δ₀ + 1)) * nq) ≤
        c * K₂ * Dt * ((γ + Cm * (δ₀ + 1)) * nq) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb2 (by positivity)) (by positivity)
    calc _ ≤ _ := h1.trans h2
      _ = _ := by ring
  have t3 : c * K₁ * ((Cχ + C4 ^ 4) * nq * D1) / 2 ≤ c * K₁ * (Cχ + C4 ^ 4) / 2 * Dt * nq := by
    have h := mul_le_mul_of_nonneg_left hb3 (show 0 ≤ c * K₁ * (Cχ + C4 ^ 4) / 2 * nq by positivity)
    calc _ = c * K₁ * (Cχ + C4 ^ 4) / 2 * nq * D1 := by ring
      _ ≤ _ := h
      _ = _ := by ring
  have t4 : ρc * ((Cbad + C4 ^ 4) * nq * w1) / 2 ≤ c / Real.pi * (Cbad + C4 ^ 4) / 2 * Dt * nq := by
    have h := mul_le_mul hρc (mul_le_mul_of_nonneg_left hb4
      (show 0 ≤ (Cbad + C4 ^ 4) * nq by positivity)) (by positivity) (by positivity)
    calc _ = ρc * ((Cbad + C4 ^ 4) * nq * w1) / 2 := rfl
      _ ≤ c / Real.pi * ((Cbad + C4 ^ 4) * nq * Dt) / 2 := by linarith
      _ = _ := by ring
  have t5 : (4 * Cg ^ 2 * Cbad + C4 ^ 4) * nq * s1 / 2 ≤
      (4 * Cg ^ 2 * Cbad + C4 ^ 4) / 2 * Dt * nq := by
    have h := mul_le_mul_of_nonneg_left hb5
      (show 0 ≤ (4 * Cg ^ 2 * Cbad + C4 ^ 4) / 2 * nq by positivity)
    calc _ = (4 * Cg ^ 2 * Cbad + C4 ^ 4) / 2 * nq * s1 := by ring
      _ ≤ _ := h
      _ = _ := by ring
  have hCSe : CS * Dt * nq = c / Real.pi * Cm * Dt * nq + c * K₂ * (γ + Cm * (δ₀ + 1)) * Dt * nq +
      c * K₁ * (Cχ + C4 ^ 4) / 2 * Dt * nq + (4 * Cg ^ 2 * Cbad + C4 ^ 4) / 2 * Dt * nq +
      c / Real.pi * (Cbad + C4 ^ 4) / 2 * Dt * nq := by
    rw [hCS]; ring
  have hp1 : 0 ≤ c / Real.pi * Cm * Dt * nq := by positivity
  have hp2 : 0 ≤ c / Real.pi * (Cbad + C4 ^ 4) / 2 * Dt * nq := by positivity
  have hp3 : 0 ≤ (4 * Cg ^ 2 * Cbad + C4 ^ 4) / 2 * Dt * nq := by positivity
  have hp4 : 0 ≤ c * K₁ * (Cχ + C4 ^ 4) / 2 * Dt * nq := by positivity
  have hp5 : 0 ≤ c * K₂ * (γ + Cm * (δ₀ + 1)) * Dt * nq := by positivity
  have hρIQ1 : ρc * IQ ≤ L * nq + ρc * (Cm * (d + w2) * nq) := by
    rw [← hlead, ← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith [hIQ'.2]) hρc0
  have hρIQ2 : L * nq - ρc * (Cm * (d + w2) * nq) ≤ ρc * IQ := by
    rw [← hlead, ← mul_sub]; exact mul_le_mul_of_nonneg_left (by linarith [hIQ'.1]) hρc0
  constructor
  · linarith
  · linarith

set_option maxHeartbeats 1600000 in
/-- **Sharp collar density at `s = 0`, conditional form.** There are
`d_S > 0`, `C_S ≥ 0`, `ε_S W → 0` and `W₀` such that for `W ≥ W₀`, `e ∈ bulkInterval κ`, Hermitian
`X` with `d(X) ≤ d_S` and every `q`,
`E_{A,B} q*K_X T Σ_F(0) T* K_X* q = (η/π)‖q‖² ± C_S (d(X) + ε_S W)‖q‖²` (lintegral form),
`η = Im z_b`. -/
theorem lintegral_condCollarDensity_two_sided (hP : FreshPalmContract)
    (hPD : PointDensityContract) (hCM : CommonPortMeanContract) (hTM : TraceMatrixContract)
    (source : BlockBand.External.PSSS.SourceContract.{0}) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ (dS CS : ℝ) (εS : ℕ → ℝ) (W₀ : ℕ), 0 < dS ∧ 0 ≤ CS ∧ Tendsto εS atTop (𝓝 0) ∧
      (∀ W, 0 ≤ εS W) ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ e ∈ bulkInterval κ, ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
        matchedDistance b e X ≤ dS → ∀ q : Fin 2 × Fin W → ℂ,
          ENNReal.ofReal ((boundaryZ b e).im / Real.pi * ∑ a, ‖q a‖ ^ 2 -
              CS * (matchedDistance b e X + εS W) * ∑ a, ‖q a‖ ^ 2) ≤
            ∫⁻ ω, ENNReal.ofReal (quadForm (matchedLeadK b e X * condCollarDensity b e X ω *
              (matchedLeadK b e X)ᴴ) q) ∂layerLaw W b .common ∧
          ∫⁻ ω, ENNReal.ofReal (quadForm (matchedLeadK b e X * condCollarDensity b e X ω *
              (matchedLeadK b e X)ᴴ) q) ∂layerLaw W b .common ≤
            ENNReal.ofReal ((boundaryZ b e).im / Real.pi * ∑ a, ‖q a‖ ^ 2 +
              CS * (matchedDistance b e X + εS W) * ∑ a, ‖q a‖ ^ 2) := by
  have hc : 0 < 1 - 2 * b := by linarith
  have hc1 : 1 - 2 * b < 1 := by linarith
  have hm4 : 0 < 4 - (2 - κ) ^ 2 := BlockBand.Layers.four_sub_sq_pos hκ (by linarith)
  have hV : 0 < Real.sqrt (4 - (2 - κ) ^ 2) / 2 := by
    have := Real.sqrt_pos.2 hm4; positivity
  have hpi := Real.pi_pos
  -- constants
  obtain ⟨εc, r, s₀, v₀, hεc, hK, hreg⟩ := freshRegular_of_chi hc hc1 hV
  obtain ⟨εc', rc, sc, vc, Cc, hεc', -, -, -, -, hCc, hcert⟩ :=
    BlockBand.Palm.certificate_full_uniform.{0} hc hc1 hV
  obtain ⟨εN, hεN, hεN0, hrel⟩ :=
    relativeMatrixDensity hP hPD 7 (1 - 2 * b) r s₀ v₀ hK (r₁ := r) hK.2.2.1
  obtain ⟨Cg, hCg0, hCg⟩ := globalWeightedDensity_general hc 1
  obtain ⟨δ₀, Cm, Wm, hδ₀, hmean⟩ := hCM.mean b hb0 hb κ hκ
  obtain ⟨C4, W4, hmom⟩ := hCM.moments b hb0 hb κ hκ 4 (by norm_num)
  obtain ⟨dχ, Cχ, Wχ, hdχ, hCχ, hχ2⟩ := lintegral_traceDefect_sq_le hTM source hb0 hb hκ hκ2
  set εt : ℝ := min εc εc' with hεt
  have hεt0 : 0 < εt := lt_min hεc hεc'
  obtain ⟨dT, CT, WT, hdT, hCT, htr⟩ := layerLaw_trace_bad_le hTM source hb0 hb hκ hκ2 hεt0
  obtain ⟨Cw, hCw, hweg⟩ := layerLaw_collarTopBlock_inv_bad_le source
  set c : ℝ := 1 - 2 * b with hcdef
  set γ : ℝ := commonPortGamma b with hγ
  have hγ0 : 0 ≤ γ := by
    rw [hγ, commonPortGamma]; exact div_nonneg (by linarith) hc.le
  set Cm' : ℝ := max Cm 0
  set C4' : ℝ := max C4 0
  have hCm' : 0 ≤ Cm' := le_max_right _ _
  have hC4' : 0 ≤ C4' := le_max_right _ _
  set K₁ : ℝ := Cc / Real.pi + (Real.pi⁻¹ + Cc * εt / Real.pi) * Cc with hK₁
  set K₂ : ℝ := 1 + Cc * εt with hK₂
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  set Cbad : ℝ := 4 * Cw / Real.sqrt (1 - 2 * b) + 2 * b + CT
  have hCbad : 0 ≤ Cbad := by
    have := Real.sqrt_nonneg (1 - 2 * b)
    have : 0 ≤ 4 * Cw / Real.sqrt (1 - 2 * b) := by positivity
    linarith
  set CS : ℝ := c / Real.pi * Cm' + c * K₂ * (γ + Cm' * (δ₀ + 1)) + c * K₁ * (Cχ + C4' ^ 4) / 2 +
    (4 * Cg ^ 2 * Cbad + C4' ^ 4) / 2 + c / Real.pi * (Cbad + C4' ^ 4) / 2 with hCS
  have hCS0 : 0 ≤ CS := by positivity
  set εS : ℕ → ℝ := fun W => 1 / (W : ℝ) + εN W + 1 / Real.sqrt W with hεS
  have hεS0 : ∀ W, 0 ≤ εS W := fun W => by
    have := hεN0 W
    simp only [hεS]; positivity
  refine ⟨min δ₀ (min dχ dT), CS, εS, max (max Wm W4) (max (max Wχ WT) 2),
    lt_min hδ₀ (lt_min hdχ hdT), hCS0, ?_, hεS0, ?_⟩
  · have h1 : Tendsto (fun W : ℕ => 1 / (W : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h2 : Tendsto (fun W : ℕ => 1 / Real.sqrt W) atTop (𝓝 0) := by
      have : Tendsto (fun W : ℕ => Real.sqrt W) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      have h := this.inv_tendsto_atTop
      refine h.congr fun W => ?_
      simp
    have := (h1.add hεN).add h2
    simp only [add_zero] at this
    exact this
  intro W hW hW₀ e he X hX hd q
  have : IsProbabilityMeasure (layerLaw W b .common) := by unfold layerLaw; infer_instance
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hW2 : (2 : ℝ) ≤ W := by
    have : 2 ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW₀)
    exact_mod_cast this
  have hWm : Wm ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW₀)
  have hW4 : W4 ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW₀)
  have hWχ : Wχ ≤ W :=
    (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hW₀))
  have hWT : WT ≤ W :=
    (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hW₀))
  have he2 : |e| < 2 := BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ he
  have hdδ : matchedDistance b e X ≤ δ₀ := hd.trans (min_le_left _ _)
  have hdχ' : matchedDistance b e X ≤ dχ := hd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdT' : matchedDistance b e X ≤ dT := hd.trans ((min_le_right _ _).trans (min_le_right _ _))
  set d := matchedDistance b e X with hddef
  have hd0 : 0 ≤ d := le_max_of_le_left (norm_nonneg _)
  set μ := layerLaw W b .common
  set K := matchedLeadK b e X
  set Q : LayerSample W .common → ℝ := fun ω => ∑ a, ‖((commonPortL b e X ω)ᴴ *ᵥ q) a‖ ^ 2
    with hQ
  set χ : LayerSample W .common → ℝ := fun ω =>
    ‖portBlockTrace (layerResolvent .common e (commonZ b e) X ω) 0 - matchedA e‖ with hχ
  set f : LayerSample W .common → ℝ := fun ω =>
    quadForm (K * condCollarDensity b e X ω * Kᴴ) q with hf
  set nq : ℝ := ∑ a, ‖q a‖ ^ 2
  have hnq : 0 ≤ nq := by positivity
  set ρ₀ : ℝ := (star (matchedA e)).im / Real.pi with hρ₀
  have hμim : 0 ≤ (star (matchedA e)).im := by
    rw [Complex.star_def, Complex.conj_im]
    linarith [BlockBand.Layers.matchedA_im_neg he2]
  have hμ1 : (star (matchedA e)).im ≤ 1 := by
    have := Complex.abs_im_le_norm (star (matchedA e))
    rw [norm_star, BlockBand.Layers.norm_matchedA he2.le] at this
    linarith [le_abs_self (star (matchedA e)).im]
  have hρ₀0 : 0 ≤ ρ₀ := div_nonneg hμim hpi.le
  have hρ₀1 : ρ₀ ≤ Real.pi⁻¹ := by
    rw [hρ₀, div_eq_mul_inv]; exact mul_le_of_le_one_left (inv_nonneg.2 hpi.le) hμ1
  have hlead : ρ₀ * c * γ = (boundaryZ b e).im / Real.pi := by
    rw [hρ₀, hγ, commonPortGamma, BlockBand.Layers.boundaryZ_im he2.le, Complex.star_def,
      Complex.conj_im, hcdef]
    have hc' : (1 - 2 * b) ≠ 0 := hc.ne'
    field_simp
  -- the shift `w = c a`
  have hw_eq := collarShiftW_eq (b := b) he2.le
  have hwim : (collarShiftW b e).im < 0 := by
    rw [hw_eq]
    have := BlockBand.Layers.matchedA_im_neg he2
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_neg_of_pos_of_neg hc this
  have hw1 : ‖collarShiftW b e‖ ≤ 1 := by
    rw [hw_eq, norm_mul, BlockBand.Layers.norm_matchedA he2.le, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hc]
    linarith
  -- the bad event
  set t : ℝ := ((W : ℝ) ^ 3)⁻¹
  have ht : 0 < t := by positivity
  set β : ℝ := (W : ℝ) ^ 3
  have hβ : 0 < β := by positivity
  set B1 : Set (LayerSample W .common) := {ω | ¬ ∀ j, (ω.1 j).IsHermitian}
  set B2 : Set (LayerSample W .common) := {ω | ¬ ∀ v, ∑ a,
    ‖((collarTopBlock e X ω)⁻¹ *ᵥ v) a‖ ^ 2 ≤ (t ^ 2)⁻¹ * ∑ a, ‖v a‖ ^ 2}
  set B3 : Set (LayerSample W .common) :=
    {ω | β < ∑ x, ∑ y, ‖bondMatrix .common ω.2 x y‖ ^ 2}
  set B4 : Set (LayerSample W .common) :=
    {ω | εt < ‖portBlockTrace (layerResolvent .common e (commonZ b e) X ω) 0 - matchedA e‖}
  set B5 : Set (LayerSample W .common) := {ω | ¬ IsUnit (collarTopBlock e X ω).det}
  set Bad := B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5
  have hB1 : μ B1 = 0 := by
    have := BlockBand.Layers.lct_ae_blocks_isHermitian W b .common
    rwa [ae_iff] at this
  have hB5 : μ B5 = 0 := by
    have := ae_isUnit_det_collarTopBlock (b := b) hb hW e X
    rwa [ae_iff] at this
  have hB2 : μ B2 ≤ ENNReal.ofReal (4 * Cw / Real.sqrt (1 - 2 * b) / (W : ℝ) ^ 2) := by
    refine (hweg W hW b hb e X hX t ht).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    simp only [t]; field_simp; ring
  have hB3 : μ B3 ≤ ENNReal.ofReal (2 * b / (W : ℝ) ^ 2) := by
    refine (layerLaw_frobenius_bad_le W b hβ).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [Real.coe_toNNReal _ (by positivity)]
    simp only [β]; field_simp
  have hB4 : μ B4 ≤ ENNReal.ofReal (CT / (W : ℝ) ^ 2) := htr W hW hWT X hX e he hdT'
  have hBad : μ Bad ≤ ENNReal.ofReal (Cbad / (W : ℝ) ^ 2) := by
    have h0 := measure_union_le (μ := μ) (B1 ∪ B2 ∪ B3 ∪ B4) B5
    have h1 := measure_union_le (μ := μ) (B1 ∪ B2 ∪ B3) B4
    have h2 := measure_union_le (μ := μ) (B1 ∪ B2) B3
    have h3 := measure_union_le (μ := μ) B1 B2
    rw [hB1, zero_add] at h3
    rw [hB5, add_zero] at h0
    refine h0.trans (h1.trans ((add_le_add (h2.trans (add_le_add (h3.trans hB2) hB3)) hB4).trans
      (le_of_eq ?_)))
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    simp only [Cbad]
    field_simp
  set T := toMeasurable μ Bad
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hBT : Bad ⊆ T := subset_toMeasurable _ _
  have hμT : μ T ≤ ENNReal.ofReal (Cbad / (W : ℝ) ^ 2) := by
    rw [measure_toMeasurable]; exact hBad
  -- measurability and moments
  have hLm := BlockBand.Critical.CommonPort.measurable_commonPortL b e X
  have hQm : Measurable Q := (continuous_sumsq_conjTranspose_mulVec q).measurable.comp hLm
  have hQ0 : ∀ ω, 0 ≤ Q ω := fun ω => by positivity
  have hχm : Measurable χ := measurable_traceDefect b e X
  have hnLm : Measurable fun ω => ‖commonPortL b e X ω‖ := continuous_norm.measurable.comp hLm
  obtain ⟨hint, hnorm⟩ := hmean W hW hWm X hX e he hdδ
  have hQeq : ∀ ω, Q ω = quadForm (commonPortLL b e X ω) q := fun ω =>
    sumsq_conjTranspose_mulVec_eq_quadForm _ q
  have hQi : Integrable Q μ := (integrable_quadForm hint q).congr
    (Eventually.of_forall fun ω => (hQeq ω).symm)
  have hQint : ∫ ω, Q ω ∂μ = quadForm (matrixExpect μ (commonPortLL b e X)) q := by
    rw [integral_congr_ae (Eventually.of_forall hQeq), integral_quadForm hint q]
  have hIQ : |∫ ω, Q ω ∂μ - γ * nq| ≤ Cm' * (d + 1 / (W : ℝ) ^ 2) * nq := by
    rw [hQint]
    set M := matrixExpect μ (commonPortLL b e X)
    have hsplit : quadForm M q - γ * nq =
        quadForm (M - ((γ : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) q := by
      rw [quadForm_sub, quadForm_real_smul, quadForm_one]
    have h2 : ‖M - ((γ : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ ≤
        Cm' * (d + 1 / (W : ℝ) ^ 2) :=
      hnorm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    rw [hsplit, abs_le]
    constructor
    · have h1 := quadForm_le_opNorm
        (-(M - ((γ : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))) q
      rw [norm_neg] at h1
      have h3 : quadForm (-(M - ((γ : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))) q =
          -quadForm (M - ((γ : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) q := by
        simp only [quadForm, neg_mulVec, dotProduct_neg, Complex.neg_re]
      have := mul_le_mul_of_nonneg_right h2 hnq
      linarith
    · have h1 := quadForm_le_opNorm
        (M - ((γ : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) q
      have := mul_le_mul_of_nonneg_right h2 hnq
      linarith
  have hmom4 := lintegral_ofReal_pow_four_le hnLm (fun ω => norm_nonneg _) hC4'
    (((hmom W hW hW4 X hX e he).1).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hQ2 : ∫⁻ ω, ENNReal.ofReal (Q ω ^ 2) ∂μ ≤ ENNReal.ofReal (C4' ^ 4 * nq ^ 2) := by
    have hpt : ∀ ω, ENNReal.ofReal (Q ω ^ 2) ≤
        ENNReal.ofReal (nq ^ 2) * ENNReal.ofReal (‖commonPortL b e X ω‖ ^ 4) := by
      intro ω
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hQL : Q ω ≤ ‖commonPortL b e X ω‖ ^ 2 * nq := by
        have := sumsq_mulVec_le_opNorm (commonPortL b e X ω)ᴴ q
        rwa [l2_opNorm_conjTranspose] at this
      have := pow_le_pow_left₀ (hQ0 ω) hQL 2
      nlinarith
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_const_mul _ (hnLm.pow_const 4).ennreal_ofReal]
    calc ENNReal.ofReal (nq ^ 2) * ∫⁻ ω, ENNReal.ofReal (‖commonPortL b e X ω‖ ^ 4) ∂μ
        ≤ ENNReal.ofReal (nq ^ 2) * ENNReal.ofReal (C4' ^ 4) := by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), mul_comm]
  have hχ2' := hχ2 W hW hWχ X hX e he hdχ'
  -- pointwise bounds
  have hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω := Eventually.of_forall fun ω => by
    have h1 : K * condCollarDensity b e X ω * Kᴴ = ((collarTW e X ω)ᴴ * Kᴴ)ᴴ *
        sigma (collarFW e X ω) c 0 * ((collarTW e X ω)ᴴ * Kᴴ) := by
      simp only [condCollarDensity, conjTranspose_mul, conjTranspose_conjTranspose,
        Matrix.mul_assoc]
      rfl
    simp only [hf]
    rw [h1, quadForm_conjTranspose_mul_mul]
    exact quadForm_sigma_nonneg _ _ _ _
  have hbad : ∀ᵐ ω ∂μ, ω ∈ T → f ω ≤ (2 * (Cg * Real.sqrt W)) * Q ω := by
    filter_upwards [BlockBand.Layers.lct_ae_blocks_isHermitian W b .common] with ω hA _
    have hF := collarFW_isHermitian e hX hA
    have hS := (hCg W hW (collarFW e X ω) hF).2 (sigma (collarFW e X ω) c)
      (continuous_sigma _ _) (isMatrixSpectralDensity_sigma hW hF hc) 0
    simp only [Complex.ofReal_zero, Complex.ofReal_one] at hS
    exact quadForm_condCollarDensity_le hX hA hwim hw1 (by positivity) hS q
  have hVμ : Real.sqrt (4 - (2 - κ) ^ 2) / 2 ≤ (star (matchedA e)).im := by
    have := BlockBand.Layers.matchedA_im_le_of_mem_bulkInterval he
    rw [Complex.star_def, Complex.conj_im]
    linarith
  have hμn : ‖star (matchedA e)‖ ≤ 1 := by
    rw [norm_star, BlockBand.Layers.norm_matchedA he2.le]
  have : Nonempty (Fin W) := ⟨⟨0, hW⟩⟩
  have hgood : ∀ᵐ ω ∂μ, ω ∉ T →
      |f ω - ρ₀ * c * Q ω| ≤ (c * K₁) * χ ω * Q ω + (c * K₂ * εN W) * Q ω := by
    refine Eventually.of_forall fun ω hωT => ?_
    have hωB : ω ∉ Bad := fun h => hωT (hBT h)
    simp only [Bad, Set.mem_union, not_or] at hωB
    obtain ⟨⟨⟨⟨hω1, hω2⟩, hω3⟩, hω4⟩, hω5⟩ := hωB
    simp only [B1, B2, B3, B4, B5, Set.mem_ofPred_eq, not_not, not_lt] at hω1 hω2 hω3 hω4 hω5
    have hF := collarFW_isHermitian e hX hω1
    have hA7 : |e| + β / t ≤ (W : ℝ) ^ (7 : ℝ) := by
      have h7 : (W : ℝ) ^ (7 : ℝ) = (W : ℝ) ^ (7 : ℕ) := by norm_cast
      have hβt : β / t = (W : ℝ) ^ 6 := by simp only [β, t]; field_simp
      rw [h7, hβt]
      have h6 : (2 : ℝ) ^ 6 ≤ (W : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) hW2 6
      have : (W : ℝ) ^ 7 = W * W ^ 6 := by ring
      nlinarith [abs_nonneg e]
    have hnb := normBound_collarFW ht hβ.le hω2 hω3 hA7
    have hχeq := norm_certificateChi_collarFW he2 hX hω1 hb hω5
    have hχt : ‖BlockBand.Palm.certificateChi (collarFW e X ω) (1 - 2 * b) 0
        (star (matchedA e))‖ ≤ εt := by rw [hχeq]; exact hω4
    have hFR := hreg W hW (collarFW e X ω) hF (star (matchedA e)) hVμ hμn
      (hχt.trans (min_le_left _ _))
    have hrel' := hrel W hW (collarFW e X ω) 0 ⟨hF, hnb, hFR⟩ 0 (by simp)
      (sigma (collarFW e X ω) c) (continuous_sigma _ _) (isMatrixSpectralDensity_sigma hW hF hc)
    obtain ⟨-, hm, hZ1, hZ2⟩ := hcert (Fin W) (collarFW e X ω) hF 0 (star (matchedA e)) hVμ hμn
      (hχt.trans (min_le_right _ _))
    have hm0 : 0 ≤ (BlockBand.Palm.certificateCanonicalDyson hF.eigenvalues (1 - 2 * b)
        ((0 : ℝ) : ℂ)).im := by
      rw [← BlockBand.Palm.CoarseRelative.freshDyson_eq_certificate hF hW hc (by simp)]
      exact freshDyson_im_nonneg _ _ _
    have key := quadForm_condCollarDensity_two_sided hW hb he2 hX hω1 hω5 (hεN0 W) hrel' hCc.le
      hm hZ1 hZ2 hm0 q
    rw [hχeq] at key
    have hle := coef_le hCc.le (norm_nonneg _) hω4 (hεN0 W) hc.le (hQ0 ω)
    have e1 : ρ₀ * c * Q ω = (star (matchedA e)).im / Real.pi * (c * Q ω) := by
      rw [hρ₀]; ring
    rw [e1]
    refine key.trans (hle.trans (le_of_eq ?_))
    simp only [hK₁, hK₂, hχ]
  -- the degenerate direction
  by_cases hq0 : nq = 0
  · have hq : q = 0 := by
      funext x
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖q i‖)).1 hq0 x
        (Finset.mem_univ _)
      simpa using this
    have hf00 : ∀ ω, f ω = 0 := fun ω => by simp [hf, hq, quadForm]
    simp only [hf] at hf00
    simp only [hf00, ENNReal.ofReal_zero, lintegral_zero, hq0, mul_zero, sub_zero, add_zero,
      le_refl, and_self]
  have hnq0 : 0 < nq := lt_of_le_of_ne hnq (Ne.symm hq0)
  set D1 : ℝ := d + 1 / (W : ℝ) with hD1
  have hD1pos : 0 < D1 := by positivity
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.2 hWr
  have hk₁ : 0 ≤ c * K₁ := by positivity
  have hk₂ : 0 ≤ c * K₂ * εN W := mul_nonneg (by positivity) (hεN0 W)
  obtain ⟨hlow, hup⟩ := lintegral_two_sided_of_pointwise hTm hQm hχm hQ0 hQi
    (ρ := ρ₀ * c) (k₁ := c * K₁) (k₂ := c * K₂ * εN W) (G := 2 * (Cg * Real.sqrt W))
    (pT := Cbad / (W : ℝ) ^ 2) (M₄ := C4' ^ 4 * nq ^ 2) (Mχ := Cχ * D1 ^ 2)
    (l := nq / D1) (l₁ := nq * Real.sqrt W) (l₂ := nq * W)
    (by positivity) hk₁ hk₂ (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) hgood hbad hf0 hμT hQ2 hχ2'
  have hsq : Real.sqrt W ^ 2 = W := Real.sq_sqrt hWr.le
  have e1 : nq / D1 * (Cχ * D1 ^ 2) + C4' ^ 4 * nq ^ 2 / (nq / D1) =
      (Cχ + C4' ^ 4) * nq * D1 := by
    field_simp
  have e2 : nq * W * (Cbad / (W : ℝ) ^ 2) + C4' ^ 4 * nq ^ 2 / (nq * W) =
      (Cbad + C4' ^ 4) * nq * (1 / W) := by
    field_simp
  have e3 := aux_e3 hsW hnq0 Cg Cbad C4'
  rw [hsq] at e3
  rw [e1, e2] at hlow
  rw [e1, e3] at hup
  have hεSW : εS W = 1 / (W : ℝ) + εN W + 1 / Real.sqrt W := rfl
  have hW1' : (1 : ℝ) ≤ W := by linarith
  have hW2' : 1 / (W : ℝ) ^ 2 ≤ 1 / W := one_div_sq_le_one_div hW1'
  have hρc : ρ₀ * c ≤ c / Real.pi := by
    rw [div_eq_mul_inv, mul_comm c]; exact mul_le_mul_of_nonneg_right hρ₀1 hc.le
  have hlead' : ρ₀ * c * (γ * nq) = (boundaryZ b e).im / Real.pi * nq := by
    rw [← hlead]; ring
  have hW2'' : 1 / (W : ℝ) ^ 2 ≤ 1 := hW2'.trans (by rw [div_le_one hWr]; exact hW1')
  obtain ⟨hL, hU⟩ := budget_two_sided (Dt := d + εS W) (s1 := 1 / Real.sqrt W) hnq hd0 (hεN0 W)
    (by positivity) (by positivity) (by positivity) hW2' hδ₀.le hW2'' hD1 (by rw [hεSW]) hρc
    (mul_nonneg hρ₀0 hc.le) hIQ
    hdδ hlead' hc.le hK₁0 hK₂0 hCχ hCbad hCm' hγ0 hCS
  exact ⟨(ENNReal.ofReal_le_ofReal hL).trans hlow, hup.trans (ENNReal.ofReal_le_ofReal hU)⟩

end BlockBand.Critical.Collar.Density
