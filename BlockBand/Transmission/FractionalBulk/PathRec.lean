module

public import BlockBand.Transmission.FractionalBulk.PathTools
public import BlockBand.Transmission.LengthUniform.ConductanceUniform
public import BlockBand.Transmission.Generator.DriftOneTools

/-!
# The logistic recursion for `y_r = E Tr T_r^p`, uniformly on the bulk

**`pathRec_bulk hMT hGA hLp hP`**: `b, κ, p` and a time floor `ε' > 0` first; then `c > 0`,
`K ≥ 0`; then the total length `T` and `W₀`; for `W ≥ W₀`, `E ∈ bulkInterval κ` and
`1 ≤ r`, `ε'W ≤ r ≤ TW`:
`y_{r+1} ≤ y_r - (c/W) y_r² + K/W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.FractionalBulk

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.Bridge
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.Generator
open scoped ENNReal ComplexOrder

variable {W : ℕ}

/-- `y_r = E Tr T_r^p`. -/
def pathFrac (p b E : ℝ) (W r : ℕ) : ℝ :=
  ∫ ω, fracTrace p (pathTransmission b E (fun _ => 0) W r ω) ∂growthPathLaw W b

/-- Measurability and bounds of `P_r = Tr T_r^p`. -/
theorem pathFrac_facts {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {b : ℝ} (hb : b < 1 / 2) {E : ℝ}
    (h1 : -2 < E) (h2 : E < 2) (r : ℕ) :
    AEStronglyMeasurable (fun ω => fracTrace p (pathTransmission b E (fun _ => 0) W r ω))
      (growthPathLaw W b) ∧
    (∀ᵐ ω ∂growthPathLaw W b, 0 ≤ fracTrace p (pathTransmission b E (fun _ => 0) W r ω) ∧
      fracTrace p (pathTransmission b E (fun _ => 0) W r ω) ≤ W) := by
  have hpas := mm_ae_passive (W := W) (b := b) (by linarith) h1 h2 r
  have hm : Measurable fun ω => fracInt p (passiveTransmission b E (pathX b E W r ω)) :=
    (measurable_fracInt p).comp ((measurable_passiveTransmission b E).comp
      (PathJet.measurable_pathX b E r))
  refine ⟨hm.aestronglyMeasurable.congr ?_, ?_⟩
  · filter_upwards [hpas] with ω hω
    exact (fracTrace_eq_fracInt (passiveTransmission_posSemidef (by linarith) h1 h2 hω)
      hp0 hp1).symm
  · filter_upwards [hpas] with ω hω
    have hT := passiveTransmission_posSemidef (by linarith : b < 1) h1 h2 hω
    have hle := fracTrace_le_card hT (one_sub_passiveTransmission_posSemidef b E _) hp0
    rw [Fintype.card_fin] at hle
    exact ⟨fracTrace_nonneg' _ _, hle⟩

/-- Linearity of the integral of the six-term bound. -/
theorem integral_six {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f₁ f₂ f₃ f₄ f₅ : Ω → ℝ} (a₂ a₃ a₄ a₅ a₆ : ℝ) (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ)
    (h₃ : Integrable f₃ μ) (h₄ : Integrable f₄ μ) (h₅ : Integrable f₅ μ) :
    ∫ ω, (f₁ ω + a₂ * f₂ ω + a₃ * f₃ ω + a₄ * f₄ ω + a₅ * f₅ ω + a₆) ∂μ =
      (∫ ω, f₁ ω ∂μ) + a₂ * (∫ ω, f₂ ω ∂μ) + a₃ * (∫ ω, f₃ ω ∂μ) + a₄ * (∫ ω, f₄ ω ∂μ) +
        a₅ * (∫ ω, f₅ ω ∂μ) + a₆ := by
  have i2 := h₂.const_mul a₂
  have i3 := h₃.const_mul a₃
  have i4 := h₄.const_mul a₄
  have i5 := h₅.const_mul a₅
  have j2 : Integrable (fun ω => f₁ ω + a₂ * f₂ ω) μ := h₁.add i2
  have j3 : Integrable (fun ω => f₁ ω + a₂ * f₂ ω + a₃ * f₃ ω) μ := j2.add i3
  have j4 : Integrable (fun ω => f₁ ω + a₂ * f₂ ω + a₃ * f₃ ω + a₄ * f₄ ω) μ := j3.add i4
  have j5 : Integrable (fun ω => f₁ ω + a₂ * f₂ ω + a₃ * f₃ ω + a₄ * f₄ ω + a₅ * f₅ ω) μ :=
    j4.add i5
  rw [integral_add j5 (integrable_const a₆), integral_add j4 i5, integral_add j3 i4,
    integral_add j2 i3, integral_add h₁ i2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const]
  simp

/-- **The recursion.** -/
theorem pathRec_bulk (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ (c K : ℝ), 0 < c ∧ 0 ≤ K ∧ ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ r : ℕ, 1 ≤ r → ε' * W ≤ r → (r : ℝ) ≤ T * W →
        pathFrac p b E W (r + 1) ≤ pathFrac p b E W r - c / W * pathFrac p b E W r ^ 2 + K / W := by
  obtain ⟨c, A, B, d, γ, W₁, hc, hA, hB, hd, hγ, hS⟩ := stepBound_bulk hGA hLp hP hp0 hp1 hb0 hb hκ
  have hLU := LengthUniform.transmissionLengthUniform_holds hMT hGA hLp
  obtain ⟨Cg, hCg⟩ := hLU.conductance b hb0 hb κ ε' 2 hκ hε' (by norm_num)
  obtain ⟨Cj, hCj⟩ := hLU.jet b hb0 hb κ ε' 2 hκ hε' (by norm_num)
  set Cg' := max Cg 0
  set Cj' := max Cj 0
  refine ⟨c, (A + 2 * B / d ^ 2) * Cj' ^ 2 + (A + B / γ ^ 2) * Cg' + A, hc, by positivity,
    fun T => ?_⟩
  obtain ⟨Wg, hWg⟩ := hCg T
  obtain ⟨Wj, hWj⟩ := hCj T
  refine ⟨max (max W₁ 1) (max Wg Wj), fun W hW E hE r hr1 hεr hrT => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hW1⟩, hWg', hWj'⟩ := hW
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWp : (0 : ℝ) < W := by linarith
  obtain ⟨s, hs⟩ := stationaryJet_exists hb0 hb h1 h2
  set μ := growthPathLaw W b
  set X := pathX b E W r
  have hXm : Measurable X := PathJet.measurable_pathX b E r
  have hpas := mm_ae_passive (W := W) (b := b) (by linarith) h1 h2 r
  -- `P_r`, `g_r`, `δ₀`, `δ₁`
  obtain ⟨hPm, hPb⟩ := pathFrac_facts (W := W) hp0 hp1 hb h1 h2 r
  set Pf := fun ω => fracTrace p (pathTransmission b E (fun _ => 0) W r ω)
  have hPi : Integrable Pf μ := Integrable.of_bound hPm W (by
    filter_upwards [hPb] with ω h; rw [Real.norm_of_nonneg h.1]; exact h.2)
  have hP2i : Integrable (fun ω => Pf ω ^ 2) μ := Integrable.of_bound (hPm.pow 2) (W ^ 2) (by
    filter_upwards [hPb] with ω h
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ h.1 h.2 2)
  set gf := fun ω => conductanceOf (passiveTransmission b E (X ω))
  have hgm : Measurable gf := measurable_pathConductance b E r
  have hgb : ∀ᵐ ω ∂μ, 0 ≤ gf ω ∧ gf ω ≤ W := by
    filter_upwards [pathPower_mem (W := W) (b := b) (by linarith) h1 h2] with ω h
    obtain ⟨-, -, h3⟩ := h 1 r le_rfl
    exact ⟨(h 1 r le_rfl).1.trans (h 1 r le_rfl).2.1, h3⟩
  have hg2i : Integrable (fun ω => gf ω ^ 2) μ := Integrable.of_bound (hgm.pow_const 2).aestronglyMeasurable
    (W ^ 2) (by
      filter_upwards [hgb] with ω h
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ h.1 h.2 2)
  have hg2 : ∫ ω, gf ω ^ 2 ∂μ ≤ Cg' := by
    have h := hWg W hWg' E hE r hεr hrT
    have h' : ∫⁻ ω, ‖gf ω‖ₑ ^ ((2 : ℕ) : ℝ) ∂μ ≤ ENNReal.ofReal Cg' := by
      refine le_trans (le_of_eq ?_) (h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      norm_num; rfl
    exact integral_pow_le_of_lintegral hgm (by filter_upwards [hgb] with ω h; exact h.1) 2
      (le_max_right _ _) h'
  have hjet := hWj W hWj' E hE s hs r hεr hrT
  have hCjW : ENNReal.ofReal (Cj / W) ≤ ENNReal.ofReal (Cj' / W) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hWp.le)
  have hδ0m : AEStronglyMeasurable (fun ω => jetDistance0 b E (X ω)) μ :=
    ((PathScalar.measurable_jetDistance0 b E).comp hXm).aestronglyMeasurable
  have hδ1m : AEStronglyMeasurable (fun ω => jetDistance1 b E s (X ω)) μ :=
    (PathJet.measurable_pathJetV b E s r).aestronglyMeasurable.congr
      (Filter.EventuallyEq.symm (PathJet.pathJet1_ae_eq (W := W) (b := b) (by linarith) h1 h2 s r))
  obtain ⟨hδ0i, hδ0⟩ := pow2_of_eLpNorm hδ0m (by positivity) ((le_self_add.trans hjet).trans hCjW)
  obtain ⟨hδ1i, hδ1⟩ := pow2_of_eLpNorm hδ1m (by positivity) ((le_add_self.trans hjet).trans hCjW)
  -- the step
  have hinner : Measurable fun ω => ∫ y, stepFrac p b E (X ω) y ∂freshLaw W b :=
    ((measurable_stepFrac p b E).stronglyMeasurable.integral_prod_right'
      (ν := freshLaw W b)).measurable.comp hXm
  have hinb : ∀ ω, |∫ y, stepFrac p b E (X ω) y ∂freshLaw W b| ≤ W := fun ω => by
    have h0 : 0 ≤ ∫ y, stepFrac p b E (X ω) y ∂freshLaw W b :=
      integral_nonneg fun y => stepFrac_nonneg _ _ _ _ _
    rw [abs_of_nonneg h0]
    calc ∫ y, stepFrac p b E (X ω) y ∂freshLaw W b ≤ ∫ _y, (W : ℝ) ∂freshLaw W b :=
          integral_mono (Integrable.of_bound ((measurable_stepFrac (W := W) p b E).comp
            (measurable_prodMk_left (x := X ω))).aestronglyMeasurable W
            (Filter.Eventually.of_forall fun y => by
              rw [Real.norm_of_nonneg (stepFrac_nonneg _ _ _ _ _)]; exact stepFrac_le _ _ _ _ _))
            (integrable_const _) fun y => stepFrac_le _ _ _ _ _
      _ = W := by simp
  have hini : Integrable (fun ω => ∫ y, stepFrac p b E (X ω) y ∂freshLaw W b) μ :=
    Integrable.of_bound hinner.aestronglyMeasurable W (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hinb ω)
  have hsucc : pathFrac p b E W (r + 1) = ∫ ω, (∫ y, stepFrac p b E (X ω) y ∂freshLaw W b) ∂μ := by
    rw [pathFrac, integral_congr_ae (ae_pathFrac_succ hp0 hp1 hb hW1 h1 h2 hr1)]
    exact integral_fresh_eq b E (measurable_stepFrac p b E) (M := W)
      (fun x => by rw [abs_of_nonneg (stepFrac_nonneg _ _ _ _ _)]; exact stepFrac_le _ _ _ _ _) r
  set u₀ := A * W + B * W / d ^ 2
  set u₁ := B * W / d ^ 2
  set u₂ := A / W + B * W / (γ * W) ^ 2
  have hbnd : ∀ᵐ ω ∂μ, ∫ y, stepFrac p b E (X ω) y ∂freshLaw W b ≤
      Pf ω + (-(c / W)) * Pf ω ^ 2 + u₀ * jetDistance0 b E (X ω) ^ 2 +
        u₁ * jetDistance1 b E s (X ω) ^ 2 + u₂ * gf ω ^ 2 + A / W := by
    filter_upwards [hpas] with ω hω
    have h := hS W hW₁ E hE s hs (X ω) hω
    have e : Pf ω = fracTrace p (passiveTransmission b E (X ω)) := rfl
    rw [e]
    refine h.trans (le_of_eq ?_)
    simp only [u₀, u₁, u₂, gf]
    field_simp
    ring
  have hRi : Integrable (fun ω => Pf ω + (-(c / W)) * Pf ω ^ 2 + u₀ * jetDistance0 b E (X ω) ^ 2 +
      u₁ * jetDistance1 b E s (X ω) ^ 2 + u₂ * gf ω ^ 2 + A / W) μ :=
    ((((hPi.add (hP2i.const_mul _)).add (hδ0i.const_mul _)).add (hδ1i.const_mul _)).add
      (hg2i.const_mul _)).add (integrable_const _)
  have hle := integral_mono_ae hini hRi hbnd
  rw [integral_six _ _ _ _ _ hPi hP2i hδ0i hδ1i hg2i] at hle
  have hy2 := sq_integral_le hPi hP2i
  have hu₀ : 0 ≤ u₀ := by positivity
  have hu₁ : 0 ≤ u₁ := by positivity
  have hu₂ : 0 ≤ u₂ := by positivity
  rw [hsucc]
  have hyr : pathFrac p b E W r = ∫ ω, Pf ω ∂μ := rfl
  rw [hyr]
  have k1 := mul_le_mul_of_nonneg_left hδ0 hu₀
  have k2 := mul_le_mul_of_nonneg_left hδ1 hu₁
  have k3 := mul_le_mul_of_nonneg_left hg2 hu₂
  have k4 : -(c / W) * ∫ ω, Pf ω ^ 2 ∂μ ≤ -(c / W) * (∫ ω, Pf ω ∂μ) ^ 2 :=
    mul_le_mul_of_nonpos_left hy2 (by have : 0 < c / W := by positivity
                                      linarith)
  have hK : u₀ * (Cj' / W) ^ 2 + u₁ * (Cj' / W) ^ 2 + u₂ * Cg' + A / W =
      ((A + 2 * B / d ^ 2) * Cj' ^ 2 + (A + B / γ ^ 2) * Cg' + A) / W := by
    simp only [u₀, u₁, u₂]
    field_simp
    ring
  have : -(c / W) * (∫ ω, Pf ω ∂μ) ^ 2 = -(c / W * (∫ ω, Pf ω ∂μ) ^ 2) := by ring
  linarith

end BlockBand.Transmission.FractionalBulk
