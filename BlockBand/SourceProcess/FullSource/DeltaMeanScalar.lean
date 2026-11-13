module

public import BlockBand.SourceProcess.FullSource.DeltaMeanEq

/-!
# The two scalar means are `a + O(δ₀ + W⁻²)` (strictly passive `X`, scalar domain)

**`meanScalars_close`**: there are `d₁ > 0`, `C`, `W₀` (depending on `b, κ`) such that for
`W ≥ W₀`, `E ∈ bulkInterval κ` and `(passiveY X).PosDef` with `δ₀(X) ≤ d₁`,
`|E⟨𝒢₁₁⟩ - a| ≤ C(δ₀ + W⁻²)` and `|E W⁻¹Tr R₊ - a| ≤ C(δ₀ + W⁻²)`.

Proof: the residuals `|u(z - bv) - 1|, |v - f(ζ)| ≤ C/W²` (`meanEq_port_u`,
`meanEq_phys_u`, with `Im ζ` from `stage_one_setup`, as in `passiveMeanEquationsStrict_holds`,
whose witness `v = E⟨𝒢₁₁⟩` is made explicit here), then `passiveMean_stability` for
`u - a`, and the exact identity `bu(v - a) = (u - a)a⁻¹ - (u(z - bv) - 1)` (`z - ba = a⁻¹`) with
`|u| ≥ 1/2` on `δ₀ ≤ d₁ ≤ 1/4` for `v - a`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `bu(v - a) = (u - a)a⁻¹ - (u(z - bv) - 1)`, so `b|u||v - a| ≤ |u - a| + |u(z - bv) - 1|`. -/
theorem v_sub_a_le {b E : ℝ} (ha : ‖matchedA E‖ = 1) (u v : ℂ) :
    b * ‖u‖ * ‖v - matchedA E‖ ≤ ‖u - matchedA E‖ + ‖u * (boundaryZ b E - (b : ℂ) * v) - 1‖ ∨
      b < 0 := by
  rcases lt_or_ge b 0 with hb | hb
  · exact Or.inr hb
  left
  have ha0 : matchedA E ≠ 0 := by intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  have e : (b : ℂ) * u * (v - matchedA E) =
      (u - matchedA E) * (matchedA E)⁻¹ - (u * (boundaryZ b E - (b : ℂ) * v) - 1) := by
    rw [boundaryZ]; field_simp; ring
  have h := congrArg norm e
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb] at h
  rw [h]
  refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
  rw [norm_mul, norm_inv, ha, inv_one, mul_one]

/-- **The scalar means on the scalar domain** (strictly passive `X`). -/
theorem meanScalars_close (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (d₁ C : ℝ) (W₀ : ℕ), 0 < d₁ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDistance0 b E X ≤ d₁ →
        ‖(∫ ω, physTr b E X ω ∂freshLaw W b) - matchedA E‖ ≤
            C * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) ∧
          ‖(∫ ω, freshPortTrace b E X ω ∂freshLaw W b) - matchedA E‖ ≤
            C * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by
  obtain ⟨C1, W1, m1⟩ := layer_moments_u hA hb0 hb hκ 1 le_rfl
  set Cv := max C1 0 with hCvdef
  have hCv : 0 ≤ Cv := le_max_right _ _
  have hQ := Q0c_pos hb0 hb hκ hCv
  have he1 := eps1_pos hb0 hb hκ hCv
  obtain ⟨Cp, Wp, hCp, hport⟩ := meanEq_port_u hA hb0 hb hκ
  obtain ⟨Cf, Wf, hCf, hphys⟩ := meanEq_phys_u hA hb0 hb hκ (ι₀ := Q0c b κ Cv / 2) (by positivity)
  obtain ⟨d₀, ρ, C', ε₀, hd₀, hρ0, hρ1, hC', hε₀, hst⟩ := passiveMean_stability hb0 hb hκ hCv
  set Cε := max Cp Cf
  have hCε : 0 ≤ Cε := le_trans hCp (le_max_left _ _)
  set C := (2 / b + 1) * (1 + (C' + 1) * Cε)
  refine ⟨min d₀ (1 / 4), C, max (max (max W1 Wp) (max Wf (⌈Cp / eps1 b κ Cv⌉₊ + 1)))
    (max (⌈Cε / ε₀⌉₊ + 1) (⌈4 * (C' * Cε)⌉₊ + 1)), lt_min hd₀ (by norm_num), by positivity,
    fun W hW E hE X hX hδ => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW1, hWp⟩, hWf, hWe⟩, hWε, hW4⟩ := hW
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hx : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hWW : (W : ℝ) ≤ (W : ℝ) ^ 2 := le_self_pow₀ hx (by norm_num)
  set μ := layerLaw W b .oneBlockOnePort
  set v := ∫ ω, physTr b E X ω ∂freshLaw W b
  set u := ∫ ω, freshPortTrace b E X ω ∂freshLaw W b
  -- `Im v ≤ 0`, `|v| ≤ Cv` (as in `passiveMeanEquationsStrict_holds`)
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
  -- the residuals
  have hεW : Cp / (W : ℝ) ^ 2 ≤ eps1 b κ Cv := by
    have hc := Nat.le_ceil (Cp / eps1 b κ Cv)
    have hc' : ((⌈Cp / eps1 b κ Cv⌉₊ : ℕ) : ℝ) ≤ W := by
      exact_mod_cast (by omega : ⌈Cp / eps1 b κ Cv⌉₊ ≤ W)
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
  set ε := Cε / (W : ℝ) ^ 2
  have hs' : ‖u * (boundaryZ b E - (b : ℂ) * v) - 1‖ ≤ ε :=
    hs.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  have hr' : ‖v - stieltjes X (zetaOf b E v u)‖ ≤ ε :=
    hf.trans (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))
  have hε0 : 0 ≤ ε := by positivity
  have hεε : ε ≤ ε₀ := by
    have hc := Nat.le_ceil (Cε / ε₀)
    have hc' : ((⌈Cε / ε₀⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast (by omega : ⌈Cε / ε₀⌉₊ ≤ W)
    have h1' : Cε / ε₀ ≤ (W : ℝ) ^ 2 := by linarith
    rw [div_le_iff₀ hε₀] at h1'
    rw [div_le_iff₀ (by positivity)]; linarith
  have hCεW : C' * ε ≤ 1 / 4 := by
    have hc := Nat.le_ceil (4 * (C' * Cε))
    have hc' : ((⌈4 * (C' * Cε)⌉₊ : ℕ) : ℝ) ≤ W := by
      exact_mod_cast (by omega : ⌈4 * (C' * Cε)⌉₊ ≤ W)
    have h1' : 4 * (C' * Cε) ≤ (W : ℝ) ^ 2 := by linarith
    have : C' * ε = C' * Cε / (W : ℝ) ^ 2 := by simp only [ε]; ring
    rw [this, div_le_iff₀ (by positivity)]; linarith
  have hδ0 : jetDistance0 b E X ≤ d₀ := hδ.trans (min_le_left _ _)
  have hδ4 : jetDistance0 b E X ≤ 1 / 4 := hδ.trans (min_le_right _ _)
  have hδnn : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hu := hst W E hE X hX.posSemidef v u ε hv0 hvC hs' hr' hε0 hεε hδ0
  have ha := bulk_norm_a hκ hE
  -- `u - a`
  have hua : ‖u - matchedA E‖ ≤ jetDistance0 b E X + C' * ε := by
    have := mul_le_of_le_one_left hδnn hρ1.le
    linarith
  have hWinv : ε = Cε * ((W : ℝ)⁻¹) ^ 2 := by simp only [ε]; field_simp
  have hC1 : 1 + (C' + 1) * Cε ≤ C :=
    le_mul_of_one_le_left (by positivity) (by have : 0 ≤ 2 / b := by positivity
                                              linarith)
  have hW2 : 0 ≤ ((W : ℝ)⁻¹) ^ 2 := by positivity
  -- `v - a`
  have hu2 : 1 / 2 ≤ ‖u‖ := by
    have := norm_sub_norm_le (matchedA E) u
    rw [ha, norm_sub_rev] at this
    linarith
  have hva := (v_sub_a_le ha u v).resolve_right (not_lt.mpr hb0.le)
  have hva' : ‖v - matchedA E‖ ≤ 2 / b * (jetDistance0 b E X + (C' + 1) * ε) := by
    have h3 : b * (1 / 2) * ‖v - matchedA E‖ ≤ jetDistance0 b E X + C' * ε + ε := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu2 hb0.le)
        (norm_nonneg (v - matchedA E))
      linarith
    rw [show 2 / b * (jetDistance0 b E X + (C' + 1) * ε) =
      (jetDistance0 b E X + C' * ε + ε) / (b * (1 / 2)) by field_simp; ring]
    rw [le_div_iff₀ (by positivity)]; linarith
  constructor
  · refine hva'.trans ?_
    rw [hWinv]
    have h4 : jetDistance0 b E X + (C' + 1) * (Cε * ((W : ℝ)⁻¹) ^ 2) ≤
        (1 + (C' + 1) * Cε) * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by
      have e : (1 + (C' + 1) * Cε) * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) =
          jetDistance0 b E X + (C' + 1) * (Cε * ((W : ℝ)⁻¹) ^ 2) +
            (((W : ℝ)⁻¹) ^ 2 + (C' + 1) * Cε * jetDistance0 b E X) := by ring
      have : 0 ≤ (C' + 1) * Cε * jetDistance0 b E X := by positivity
      rw [e]; linarith
    have hpos : 0 ≤ (1 + (C' + 1) * Cε) * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by positivity
    calc 2 / b * (jetDistance0 b E X + (C' + 1) * (Cε * ((W : ℝ)⁻¹) ^ 2))
        ≤ 2 / b * ((1 + (C' + 1) * Cε) * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ C * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by
          have e : C * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) =
              2 / b * ((1 + (C' + 1) * Cε) * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2)) +
                (1 + (C' + 1) * Cε) * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by
            simp only [C]; ring
          rw [e]; linarith
  · refine hua.trans ?_
    rw [hWinv]
    have h4 : jetDistance0 b E X + C' * (Cε * ((W : ℝ)⁻¹) ^ 2) ≤
        (1 + (C' + 1) * Cε) * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by
      have e : (1 + (C' + 1) * Cε) * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) =
          jetDistance0 b E X + C' * (Cε * ((W : ℝ)⁻¹) ^ 2) +
            (((W : ℝ)⁻¹) ^ 2 + Cε * ((W : ℝ)⁻¹) ^ 2 + (C' + 1) * Cε * jetDistance0 b E X) := by
        ring
      have : 0 ≤ (C' + 1) * Cε * jetDistance0 b E X := by positivity
      have : 0 ≤ Cε * ((W : ℝ)⁻¹) ^ 2 := by positivity
      rw [e]; linarith
    exact h4.trans (mul_le_mul_of_nonneg_right hC1 (by positivity))

end BlockBand.SourceProcess.FullSource
