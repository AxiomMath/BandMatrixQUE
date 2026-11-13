module

public import BlockBand.Transmission.FractionalBulk.PathRec
public import BlockBand.Transmission.LawFractional.Inputs

/-!
# The logistic recursion for `y_r = E Tr T_r^p` with explicit forcing

**`pathRec_explicit hMT hGA hLp hP`**: `b, κ, p` first; then `c > 0`, `K₀, K₁ ≥ 0`; then the
time floor `ε > 0` and the total length `T`; then `W₀`; for `W ≥ W₀`, `E ∈ bulkInterval κ` and
`1 ≤ r`, `εW ≤ r ≤ TW`:
`y_{r+1} ≤ y_r - (c/W) y_r² + (K₀ + K₁(1 + ε⁻¹)²)/W`.

This is `FractionalBulk.pathRec_bulk` (same proof, same one-layer input
`stepBound_bulk`) with the forcing made explicit in `ε`: the jet constant of `jet_explicit` is
free of `ε`, and `E g_r² ≤ 16K²(1 + ε⁻¹)²` (`cond_explicit`). This gives the forcing bound
`C(1 + t⁻²)` of the paper.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFractional

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.Bridge
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.Generator
open BlockBand.Transmission.FractionalBulk
open scoped ENNReal ComplexOrder

/-- **The recursion with explicit forcing.** -/
theorem pathRec_explicit (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (c K₀ K₁ : ℝ), 0 < c ∧ 0 ≤ K₀ ∧ 0 ≤ K₁ ∧ ∀ ε : ℝ, 0 < ε → ∀ T : ℝ, ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ r : ℕ, 1 ≤ r → ε * W ≤ r → (r : ℝ) ≤ T * W →
        pathFrac p b E W (r + 1) ≤ pathFrac p b E W r - c / W * pathFrac p b E W r ^ 2 +
          (K₀ + K₁ * (1 + ε⁻¹) ^ 2) / W := by
  obtain ⟨c, A, B, d, γ, W₁, hc, hA, hB, hd, hγ, hS⟩ := stepBound_bulk hGA hLp hP hp0 hp1 hb0 hb hκ
  obtain ⟨K, hK, hCg⟩ := cond_explicit hMT hGA hLp hb0 hb hκ
  obtain ⟨Cj, hCj⟩ := jet_explicit hMT hGA hLp hb0 hb hκ
  set Cj' := max Cj 0
  refine ⟨c, (A + 2 * B / d ^ 2) * Cj' ^ 2 + A, (A + B / γ ^ 2) * (16 * K ^ 2), hc,
    by positivity, by positivity, fun ε hε T => ?_⟩
  set Cg' := (4 * K * (1 + ε⁻¹)) ^ 2
  obtain ⟨Wg, hWg⟩ := hCg ε hε T
  obtain ⟨Wj, hWj⟩ := hCj ε hε T
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
  have hg2i : Integrable (fun ω => gf ω ^ 2) μ :=
    Integrable.of_bound (hgm.pow_const 2).aestronglyMeasurable (W ^ 2) (by
      filter_upwards [hgb] with ω h
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ h.1 h.2 2)
  have hg2 : ∫ ω, gf ω ^ 2 ∂μ ≤ Cg' := by
    have h := hWg W hWg' E hE r hεr hrT
    rw [Real.rpow_two] at h
    have h' : ∫⁻ ω, ‖gf ω‖ₑ ^ ((2 : ℕ) : ℝ) ∂μ ≤ ENNReal.ofReal Cg' := by
      refine le_trans (le_of_eq ?_) h
      norm_num; rfl
    exact integral_pow_le_of_lintegral hgm (by filter_upwards [hgb] with ω h; exact h.1) 2
      (by positivity) h'
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
  have hK' : u₀ * (Cj' / W) ^ 2 + u₁ * (Cj' / W) ^ 2 + u₂ * Cg' + A / W =
      ((A + 2 * B / d ^ 2) * Cj' ^ 2 + A + (A + B / γ ^ 2) * (16 * K ^ 2) * (1 + ε⁻¹) ^ 2) / W := by
    simp only [u₀, u₁, u₂, Cg']
    field_simp
    ring
  have : -(c / W) * (∫ ω, Pf ω ∂μ) ^ 2 = -(c / W * (∫ ω, Pf ω ∂μ) ^ 2) := by ring
  linarith

end BlockBand.Transmission.LawFractional
