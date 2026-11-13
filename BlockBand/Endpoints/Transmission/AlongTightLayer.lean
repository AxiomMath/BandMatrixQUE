module

public import BlockBand.Transmission.Absorbed.ModulusAlong

/-!
# Bulk-uniform absorbed layer and majorant bounds

Part of the transmission law theorem (tightness along the absorbed path), along moving
energies. The absorbed modulus of `ModulusAlong` is fixed-`E`: its inputs `shiftFour_layer`,
`shiftDrift_layer` carry constants in `etaZ b E` and `absorbed_modY_moment` fixes one bulk
energy. Here they are restated uniformly on `E ∈ bulkInterval κ`, with `etaZ b E` replaced by
the lower bound `etaLow b κ` (`PathScalar.etaLow_le`); the proofs are the same, with the
bulk-uniform inputs `modulusFour_layer_bulk`, `modulusDrift_layer_bulk`,
`absorbedConductance_bulk`, `absorbedDeltaUniform_holds`.

* `shiftFour_layer_bulk`, `shiftDrift_layer_bulk`: one absorbed step at a passive input;
* `absorbed_modY_moment_bulk`: `E Y'(X^κ_r)¹² ≤ M` uniformly on the bulk.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Transmission

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.Generator BlockBand.Transmission.Absorbed
open BlockBand.Transmission.LawFinite BlockBand.Transmission.PassiveCovariance
open scoped ENNReal ComplexOrder

variable {W : ℕ}

/-- The constants of `shift_scalars` at `E` are dominated by their values at `etaLow b κ`. -/
theorem shift_consts_le {b κ E Kε : ℝ} (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ)
    (hKε : 0 ≤ Kε) (k : ℕ) :
    ((1 + Kε / etaZ b E) ^ 2 + 4 * Kε / etaZ b E + 1) * (1 + Kε / etaZ b E ^ 2) ≤
        ((1 + Kε / etaLow b κ) ^ 2 + 4 * Kε / etaLow b κ + 1) * (1 + Kε / etaLow b κ ^ 2) ∧
      ((k + 1 : ℕ) : ℝ) * ((Kε / etaZ b E) * (2 + Kε / etaZ b E) + 4 * Kε / etaZ b E) ≤
        ((k + 1 : ℕ) : ℝ) * ((Kε / etaLow b κ) * (2 + Kε / etaLow b κ) + 4 * Kε / etaLow b κ) := by
  have hL := etaLow_pos (b := b) (by linarith) hκ
  have hLe := etaLow_le (b := b) (by linarith) hκ hE
  have hη : 0 < etaZ b E := lt_of_lt_of_le hL hLe
  have a1 : Kε / etaZ b E ≤ Kε / etaLow b κ := div_le_div_of_nonneg_left hKε hL hLe
  have a2 : Kε / etaZ b E ^ 2 ≤ Kε / etaLow b κ ^ 2 :=
    div_le_div_of_nonneg_left hKε (by positivity) (pow_le_pow_left₀ hL.le hLe 2)
  have a3 : 4 * Kε / etaZ b E ≤ 4 * Kε / etaLow b κ :=
    div_le_div_of_nonneg_left (by positivity) hL hLe
  have a0 : 0 ≤ Kε / etaZ b E := by positivity
  have a0' : 0 ≤ Kε / etaZ b E ^ 2 := by positivity
  have a0'' : 0 ≤ 4 * Kε / etaZ b E := by positivity
  constructor
  · refine mul_le_mul ?_ (by linarith) (by positivity) (by positivity)
    have := pow_le_pow_left₀ (by positivity) (by linarith : 1 + Kε / etaZ b E ≤ 1 + Kε / etaLow b κ) 2
    linarith
  · refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have := mul_le_mul a1 (by linarith : 2 + Kε / etaZ b E ≤ 2 + Kε / etaLow b κ)
      (by positivity) (by positivity)
    linarith

/-- **The fourth moment of one absorbed step at a passive input**, uniformly on the bulk
(`shiftFour_layer` with `etaZ b E` replaced by `etaLow b κ`). -/
theorem shiftFour_layer_bulk (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) {Kε : ℝ} (hKε : 0 ≤ Kε) (k : ℕ) :
    ∃ (K : ℝ) (W₀ : ℕ), 0 ≤ K ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ Kε / (W : ℝ) ^ 2 →
        ∫ y, (((passiveTransmission b E (freshSchur E (absorbedInput X ε) y)) ^ (k + 1)).trace.re -
            ((passiveTransmission b E X) ^ (k + 1)).trace.re) ^ 4 ∂freshLaw W b ≤
          K * (modY b E X ^ 12 / (W : ℝ) ^ 2) := by
  obtain ⟨K4, W4, hK4, h4⟩ := modulusFour_layer_bulk hGA hLp hb0 hb hκ k
  have hL := etaLow_pos (b := b) (by linarith) hκ
  obtain ⟨cY, hcY, hcYd⟩ : ∃ c : ℝ, 0 ≤ c ∧ c = ((1 + Kε / etaLow b κ) ^ 2 +
      4 * Kε / etaLow b κ + 1) * (1 + Kε / etaLow b κ ^ 2) := ⟨_, by positivity, rfl⟩
  obtain ⟨cK, hcK, hcKd⟩ : ∃ c : ℝ, 0 ≤ c ∧ c = ((k + 1 : ℕ) : ℝ) * ((Kε / etaLow b κ) *
      (2 + Kε / etaLow b κ) + 4 * Kε / etaLow b κ) := ⟨_, by positivity, rfl⟩
  refine ⟨8 * (K4 * cY ^ 12 + cK ^ 4), max W4 1, by positivity,
    fun W hW E hE X hX ε hε hεK => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have hX' := LawFinite.passiveY_absorbedInput hX hε
  obtain ⟨hFm, hFb⟩ := fresh_inc_facts hb0 hb h1 h2 hε hW1 hX k
  obtain ⟨hYa0, hYa, hY1, hd4, -⟩ := shift_scalars hb0 hb h1 h2 hKε k hε hεK hW1 hX
  obtain ⟨hcY', hcK'⟩ := shift_consts_le hb hκ hE hKε k
  rw [← hcYd] at hcY'
  rw [← hcKd] at hcK'
  have hYa' : modY b E (absorbedInput X ε) ≤ cY * modY b E X :=
    hYa.trans (mul_le_mul_of_nonneg_right hcY' (by linarith))
  have hd4' : (((passiveTransmission b E (absorbedInput X ε)) ^ (k + 1)).trace.re -
      ((passiveTransmission b E X) ^ (k + 1)).trace.re) ^ 4 ≤
      cK ^ 4 * (modY b E X ^ 12 / (W : ℝ) ^ 2) := by
    refine hd4.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have hη := etaZ_pos b E (by linarith) h1 h2
    have a0 : 0 ≤ Kε / etaZ b E := div_nonneg hKε hη.le
    have a1 : 0 ≤ 4 * Kε / etaZ b E := div_nonneg (by linarith) hη.le
    exact pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (mul_nonneg a0 (by linarith)) a1)) hcK' 4
  have iF : Integrable (fun y => freshIncAt b E (k + 1) (absorbedInput X ε) y ^ 4)
      (freshLaw W b) := by
    refine Integrable.of_bound (hFm.pow_const 4).aestronglyMeasurable ((W : ℝ) ^ 4) ?_
    filter_upwards [hFb] with y hy
    rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hy 4
  have hF4 : ∫ y, freshIncAt b E (k + 1) (absorbedInput X ε) y ^ 4 ∂freshLaw W b ≤
      K4 * (modY b E (absorbedInput X ε) ^ 12 / (W : ℝ) ^ 2) :=
    h4 W (le_of_max_le_left hW) E hE _ hX'
  have hY12 : modY b E (absorbedInput X ε) ^ 12 ≤ cY ^ 12 * modY b E X ^ 12 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hYa0 hYa' 12
  have a1 : K4 * (modY b E (absorbedInput X ε) ^ 12 / (W : ℝ) ^ 2) ≤
      K4 * cY ^ 12 * (modY b E X ^ 12 / (W : ℝ) ^ 2) := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hK4
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right hY12 (by positivity)
  have key := four_combine iF (hF4.trans a1) hd4'
  refine le_trans (le_of_eq (integral_congr_ae (ae_of_all _ fun y => ?_))) (key.trans_eq (by ring))
  simp only [freshIncAt]; ring

/-- **The conditional mean of one absorbed step at a passive input**, uniformly on the bulk
(`shiftDrift_layer` with `etaZ b E` replaced by `etaLow b κ`). -/
theorem shiftDrift_layer_bulk (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) {Kε : ℝ} (hKε : 0 ≤ Kε) (k : ℕ) :
    ∃ (K : ℝ) (W₀ : ℕ), 0 ≤ K ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ Kε / (W : ℝ) ^ 2 →
        |∫ y, (((passiveTransmission b E (freshSchur E (absorbedInput X ε) y)) ^ (k + 1)).trace.re -
            ((passiveTransmission b E X) ^ (k + 1)).trace.re) ∂freshLaw W b| ≤
          K * (modY b E X ^ 3 / W) := by
  obtain ⟨Kd, Wd, hKd, hdr⟩ := modulusDrift_layer_bulk hGA hLp hb0 hb hκ k
  have hL := etaLow_pos (b := b) (by linarith) hκ
  obtain ⟨cY, hcY, hcYd⟩ : ∃ c : ℝ, 0 ≤ c ∧ c = ((1 + Kε / etaLow b κ) ^ 2 +
      4 * Kε / etaLow b κ + 1) * (1 + Kε / etaLow b κ ^ 2) := ⟨_, by positivity, rfl⟩
  obtain ⟨cK, hcK, hcKd⟩ : ∃ c : ℝ, 0 ≤ c ∧ c = ((k + 1 : ℕ) : ℝ) * ((Kε / etaLow b κ) *
      (2 + Kε / etaLow b κ) + 4 * Kε / etaLow b κ) := ⟨_, by positivity, rfl⟩
  refine ⟨Kd * cY ^ 3 + cK, max Wd 1, by positivity, fun W hW E hE X hX ε hε hεK => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hX' := LawFinite.passiveY_absorbedInput hX hε
  obtain ⟨hFm, hFb⟩ := fresh_inc_facts hb0 hb h1 h2 hε hW1 hX k
  obtain ⟨hYa0, hYa, hY1, -, hd3⟩ := shift_scalars hb0 hb h1 h2 hKε k hε hεK hW1 hX
  obtain ⟨hcY', hcK'⟩ := shift_consts_le hb hκ hE hKε k
  rw [← hcYd] at hcY'
  rw [← hcKd] at hcK'
  have hYa' : modY b E (absorbedInput X ε) ≤ cY * modY b E X :=
    hYa.trans (mul_le_mul_of_nonneg_right hcY' (by linarith))
  have hd3' : |((passiveTransmission b E (absorbedInput X ε)) ^ (k + 1)).trace.re -
      ((passiveTransmission b E X) ^ (k + 1)).trace.re| ≤ cK * (modY b E X ^ 3 / W) :=
    hd3.trans (mul_le_mul_of_nonneg_right hcK' (by positivity))
  have iF : Integrable (freshIncAt b E (k + 1) (absorbedInput X ε)) (freshLaw W b) :=
    Integrable.of_bound hFm.aestronglyMeasurable (W : ℝ) (hFb.mono fun y h => by
      rwa [Real.norm_eq_abs])
  have hF : |∫ y, freshIncAt b E (k + 1) (absorbedInput X ε) y ∂freshLaw W b| ≤
      Kd * (modY b E (absorbedInput X ε) ^ 3 / W) :=
    hdr W (le_of_max_le_left hW) E hE _ hX'
  have hY3 : modY b E (absorbedInput X ε) ^ 3 ≤ cY ^ 3 * modY b E X ^ 3 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hYa0 hYa' 3
  have a1 : Kd * (modY b E (absorbedInput X ε) ^ 3 / W) ≤ Kd * cY ^ 3 * (modY b E X ^ 3 / W) := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hKd
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right hY3 hW0.le
  have key := drift_combine iF (hF.trans a1) hd3'
  refine le_trans (le_of_eq (congrArg abs (integral_congr_ae (ae_of_all _ fun y => ?_))))
    (key.trans_eq (by ring))
  simp only [freshIncAt]; ring

/-- **`E Y'(X^κ_r)¹² ≤ M` along the absorbed path, uniformly on the bulk** and over `0 ≤ κ ≤ K`
(`absorbed_modY_moment` with the base energy ranging over `bulkInterval κI`). -/
theorem absorbed_modY_moment_bulk (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {κI : ℝ} (hκI : 0 < κI) {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) (T : ℝ) :
    ∃ (M : ℝ) (W₀ : ℕ), 0 ≤ M ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ κ : ℝ → ℝ, (∀ s, 0 ≤ κ s ∧ κ s ≤ K) →
      ∀ r : ℕ, ε * W ≤ r → (r : ℝ) ≤ T * W →
        Integrable (fun ω => modY b E (pathNearSchur b E κ W r ω) ^ 12) (growthPathLaw W b) ∧
        ∫ ω, modY b E (pathNearSchur b E κ W r ω) ^ 12 ∂growthPathLaw W b ≤ M := by
  obtain ⟨Cg, hCg⟩ := absorbedConductance_bulk hMT hGA hLp b hb0 hb κI ε ((24 : ℕ) : ℝ) K hκI hε
    (by norm_num) hK
  obtain ⟨Wg, hg⟩ := hCg T
  obtain ⟨Cδ, hCδ, hδT⟩ := absorbedDeltaUniform_holds hMT hGA hLp b hb0 hb κI K ((24 : ℕ) : ℝ)
    hκI hK (by norm_num)
  obtain ⟨Wδ, hδ⟩ := hδT T
  set Cg' := max Cg 0
  refine ⟨2 ^ 24 * (Cg' + 1) + 2 ^ 24 * (Cδ ^ 24 + 1), max (max Wg Wδ) 1, by positivity,
    fun W hW E hE κ hκK r hεr hrT => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWg, hWδ⟩, hW1⟩ := hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hr1 : 1 ≤ r := by
    have : (0 : ℝ) < r := lt_of_lt_of_le (by positivity) hεr
    exact_mod_cast this
  have hκ0 : ∀ s, 0 ≤ κ s := fun s => (hκK s).1
  set μ := growthPathLaw W b
  have hXm := measurable_pathNearSchur' (W := W) b E κ r
  set g : GrowthPath W → ℝ := absorbedConductance b E κ W r
  have hgm : Measurable g := measurable_absorbedConductance b E κ r
  have hgB : ∀ᵐ ω ∂μ, 0 ≤ g ω ∧ g ω ≤ W := by
    filter_upwards [ae_passiveSample W hκ0 (by linarith : b < 1) h1 h2] with ω hP
    obtain ⟨a0, a1⟩ := trace_pow_le_card (b := b) (by linarith) h1 h2
      (pathNearSchur_passive hP r) (le_refl 1)
    simp only [pow_one] at a0 a1
    exact ⟨a0, a1⟩
  have hg0 : ∀ᵐ ω ∂μ, 0 ≤ g ω := hgB.mono fun _ h => h.1
  have hgi := integral_pow_le_of_lintegral (μ := μ) hgm hg0 24 (le_max_right Cg 0)
    ((hg W hWg E hE κ hκK r hεr hrT).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have mG : ∫ ω, (g ω + 1) ^ 24 ∂μ ≤ 2 ^ 24 * (Cg' + 1) :=
    (moment_shift hgm hg0 (hgB.mono fun _ h => h.2) 24).trans (by gcongr)
  have iG : Integrable (fun ω => (g ω + 1) ^ 24) μ :=
    integrable_of_bdd ((hgm.add_const 1).pow_const 24) (B := ((W : ℝ) + 1) ^ 24) (by
      filter_upwards [hgB] with ω h
      rw [abs_of_nonneg (by have := h.1; positivity)]
      exact pow_le_pow_left₀ (by linarith [h.1]) (by linarith [h.2]) 24)
  have hδm : AEStronglyMeasurable (absorbedDelta b E κ W r) μ :=
    ((measurable_jetDistance0 b E).comp hXm).aestronglyMeasurable
  obtain ⟨iA, mA⟩ := shifted_moment hδm (ae_of_all _ fun _ => norm_nonneg _) 24 (by norm_num)
    hCδ hW0 (hδ W hWδ E hE κ hκK r hr1 hrT)
  have hpt : ∀ᵐ ω ∂μ, modY b E (pathNearSchur b E κ W r ω) ^ 12 ≤
      (g ω + 1) ^ 24 + ((W : ℝ) * absorbedDelta b E κ W r ω + 1) ^ 24 := by
    exact ae_of_all _ fun ω => mul_pow_twelve_le _ _
  have iS := iG.add iA
  have hYm : AEStronglyMeasurable (fun ω => modY b E (pathNearSchur b E κ W r ω) ^ 12) μ :=
    (((measurable_modY b E).comp hXm).pow_const 12).aestronglyMeasurable
  have iY : Integrable (fun ω => modY b E (pathNearSchur b E κ W r ω) ^ 12) μ :=
    Integrable.mono' iS hYm (by
      filter_upwards [hpt] with ω h
      rw [Real.norm_of_nonneg (by positivity)]
      exact h)
  have e := integral_add iG iA
  refine ⟨iY, (integral_mono_ae iY iS hpt).trans ?_⟩
  exact le_of_eq_of_le e (add_le_add mG mA)

end BlockBand.Endpoints.Transmission
