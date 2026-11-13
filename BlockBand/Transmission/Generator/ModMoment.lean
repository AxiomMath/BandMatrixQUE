module

public import BlockBand.Transmission.Generator.ModCond
public import BlockBand.Transmission.Generator.BrFourLayer
public import BlockBand.Transmission.Generator.BrL1

/-!
# The one-step fourth moment along the path

**`fourth_increment_bound hMT hGA hLp`**: `b, κ, ε < T, k` first; then `K ≥ 0, W₀`; for
`W ≥ W₀`, `E' ∈ bulkInterval κ` and `εW ≤ r ≤ TW`, `r ≥ 1`:
`E(Δ^{k+1}_r)⁴ ≤ K/W²` (at path energy `E'`).

Route: `integral_powerIncrement_pow_four`, then `fourth_layer_bulk` at a.s. passive `X_r`
(`E[·⁴ ∣ 𝓕_r] ≤ K·Y_r¹²/W²`), then `Y¹² ≤ Σ(·+1)⁴⁸` (`br_Y12_le`) and the moments of
`TransmissionLengthUniformContract.conductance`, `.jet` and `passiveSourceMixingBulk_holds` at
`p = 48` (the `bracketError_L1` pattern with `24 → 48`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PathScalar BlockBand.Transmission.SourceMixing
open BlockBand.Transmission.LengthUniform
open scoped ENNReal ComplexOrder

variable {W : ℕ}

theorem br_Y12_le {x y z w : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    ((x + 1) * (y + 1) * (z + 1) * (w + 1)) ^ 12 ≤
      (x + 1) ^ 48 + (y + 1) ^ 48 + (z + 1) ^ 48 + (w + 1) ^ 48 := by
  have hA := amgm4 (x := (x + 1) ^ 12) (y := (y + 1) ^ 12) (z := (z + 1) ^ 12) (w := (w + 1) ^ 12)
    (by positivity) (by positivity) (by positivity) (by positivity)
  simp only [← pow_mul] at hA
  refine le_trans (le_of_eq ?_) hA
  rw [mul_pow, mul_pow, mul_pow]

/-- **`E(Δ^{k+1}_r)⁴ ≤ K/W²`** on `εW ≤ r ≤ TW`, bulk-uniform. -/
theorem fourth_increment_bound (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b κ ε T : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (hε : 0 < ε) (hεT : ε < T) (k : ℕ) :
    ∃ (K : ℝ) (W₀ : ℕ), 0 ≤ K ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E' ∈ bulkInterval κ,
      ∀ r : ℕ, 1 ≤ r → ε * W ≤ r → (r : ℝ) ≤ T * W →
        ∫ ω, powerIncrement b E' W (k + 1) r ω ^ 4 ∂growthPathLaw W b ≤ K / (W : ℝ) ^ 2 := by
  obtain ⟨K, Wd, hK, hd⟩ := fourth_layer_bulk hGA hLp hb0 hb hκ k
  have hLU := transmissionLengthUniform_holds hMT hGA hLp
  obtain ⟨Cg, hgT⟩ := hLU.conductance b hb0 hb κ ε ((48 : ℕ) : ℝ) hκ hε (by norm_num)
  obtain ⟨Wg, hg⟩ := hgT T
  obtain ⟨Cj, hjT⟩ := hLU.jet b hb0 hb κ ε ((48 : ℕ) : ℝ) hκ hε (by norm_num)
  obtain ⟨Wj, hj⟩ := hjT T
  obtain ⟨Cm, Wm, hm⟩ := SourceMixingBulk.passiveSourceMixingBulk_holds hMT hGA hLp b hb0 hb κ ε T
    ((48 : ℕ) : ℝ) hκ hε hεT (by norm_num)
  set Cg' := max Cg 0
  set Cj' := max Cj 0
  set Cm' := max Cm 0
  set Mg : ℝ := 2 ^ 48 * (Cg' + 1)
  set Ma : ℝ := 2 ^ 48 * (Cj' ^ 48 + 1)
  set Mt : ℝ := 2 ^ 48 * (Cm' ^ 48 + 1)
  set MY := Mg + Ma + Mt + Ma
  refine ⟨K * MY, max (max Wd Wg) (max Wj Wm), by positivity,
    fun W hW E' hE' r hr1 hεr hrT => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWd, hWg⟩, hWj, hWm⟩ := hW
  have h1 : -2 < E' := by have := hE'.1; linarith
  have h2 : E' < 2 := by have := hE'.2; linarith
  obtain ⟨s, hs⟩ := PassiveCovariance.stationaryJet_exists hb0 hb h1 h2
  have hW1 : 1 ≤ W := by
    rcases Nat.eq_zero_or_pos W with h | h
    · subst h
      have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
      rw [Nat.cast_zero, mul_zero] at hrT; linarith
    · exact h
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  have hs0 : 0 < Real.sqrt W := Real.sqrt_pos.mpr hWpos
  set μ := growthPathLaw W b
  have hXm := PathJet.measurable_pathX (W := W) b E' r
  -- the conductance factor
  have hgm : Measurable (pathG b E' W r) := measurable_pathConductance b E' r
  have hgB : ∀ᵐ ω ∂μ, 0 ≤ pathG b E' W r ω ∧ pathG b E' W r ω ≤ W := by
    filter_upwards [pathPower_mem (W := W) (by linarith : b < 1) h1 h2] with ω hω
    obtain ⟨h0, h1', h3⟩ := hω 1 r le_rfl
    exact ⟨h0.trans h1', h3⟩
  have hg0 : ∀ᵐ ω ∂μ, 0 ≤ pathG b E' W r ω := hgB.mono fun _ h => h.1
  have hgi := integral_pow_le_of_lintegral (μ := μ) hgm hg0 48 (le_max_right Cg 0)
    ((hg W hWg E' hE' r hεr hrT).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have mG : ∫ ω, (pathG b E' W r ω + 1) ^ 48 ∂μ ≤ Mg :=
    (moment_shift hgm hg0 (hgB.mono fun _ h => h.2) 48).trans (by simp only [Mg]; gcongr)
  have iG : Integrable (fun ω => (pathG b E' W r ω + 1) ^ 48) μ :=
    integrable_of_bdd ((hgm.add_const 1).pow_const 48) (B := ((W : ℝ) + 1) ^ 48) (by
      filter_upwards [hgB] with ω h
      rw [abs_of_nonneg (by linarith [h.1] |> fun h' => pow_nonneg h' 48)]
      exact pow_le_pow_left₀ (by linarith [h.1]) (by linarith [h.2]) 48)
  -- the jet factors
  have hjet := hj W hWj E' hE' s hs r hεr hrT
  have hδ0m : AEStronglyMeasurable (fun ω => jetDistance0 b E' (pathX b E' W r ω)) μ :=
    ((measurable_jetDistance0 b E').comp hXm).aestronglyMeasurable
  have hδ1m : AEStronglyMeasurable (fun ω => jetDistance1 b E' s (pathX b E' W r ω)) μ :=
    (PathJet.measurable_pathJetV b E' s r).aestronglyMeasurable.congr
      (Filter.EventuallyEq.symm (PathJet.pathJet1_ae_eq (W := W) (b := b) (by linarith) h1 h2 s r))
  have hCjW : ENNReal.ofReal (Cj / W) ≤ ENNReal.ofReal (Cj' / W) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hWpos.le)
  obtain ⟨iA, mA⟩ := shifted_moment hδ0m (ae_of_all _ fun _ => norm_nonneg _) 48 (by norm_num)
    (le_max_right Cj 0) hWpos ((le_self_add.trans hjet).trans hCjW)
  obtain ⟨iD, mD⟩ := shifted_moment hδ1m (ae_of_all _ fun _ => norm_nonneg _) 48 (by norm_num)
    (le_max_right Cj 0) hWpos ((le_add_self.trans hjet).trans hCjW)
  -- the mixing factor
  have hτm : AEStronglyMeasurable (fun ω =>
      ‖(passiveQ b E' (pathX b E' W r ω) * passiveF b E' (pathX b E' W r ω)).trace‖ +
        hsSandwich (passiveQ b E' (pathX b E' W r ω)) (passiveF b E' (pathX b E' W r ω))) μ :=
    ((((measurable_traceQF b E').comp hXm).norm).add
      ((measurable_hsQF b E').comp hXm)).aestronglyMeasurable
  have hτL : eLpNorm (fun ω =>
      ‖(passiveQ b E' (pathX b E' W r ω) * passiveF b E' (pathX b E' W r ω)).trace‖ +
        hsSandwich (passiveQ b E' (pathX b E' W r ω)) (passiveF b E' (pathX b E' W r ω)))
        (ENNReal.ofReal ((48 : ℕ) : ℝ)) μ ≤ ENNReal.ofReal (Cm' / Real.sqrt W) := by
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    rw [eLpNorm_norm (fun ω => (passiveQ b E' (pathX b E' W r ω) *
      passiveF b E' (pathX b E' W r ω)).trace)
      (((measurable_traceQF b E').comp hXm).aestronglyMeasurable)]
    exact (hm W hWm E' hE' r hεr hrT).trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))
  obtain ⟨iT, mT⟩ := shifted_moment hτm
    (ae_of_all _ fun _ => add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) 48 (by norm_num)
    (le_max_right Cm 0) hs0 hτL
  -- `Y¹²` and its integral
  set Y : GrowthPath W → ℝ := fun ω => brY b E' s (pathX b E' W r ω)
  set fG : GrowthPath W → ℝ := fun ω => (pathG b E' W r ω + 1) ^ 48
  set fA : GrowthPath W → ℝ := fun ω => ((W : ℝ) * jetDistance0 b E' (pathX b E' W r ω) + 1) ^ 48
  set fT : GrowthPath W → ℝ := fun ω => (Real.sqrt W *
    (‖(passiveQ b E' (pathX b E' W r ω) * passiveF b E' (pathX b E' W r ω)).trace‖ +
      hsSandwich (passiveQ b E' (pathX b E' W r ω)) (passiveF b E' (pathX b E' W r ω))) + 1) ^ 48
  set fD : GrowthPath W → ℝ := fun ω => ((W : ℝ) * jetDistance1 b E' s (pathX b E' W r ω) + 1) ^ 48
  set S : GrowthPath W → ℝ := fun ω => fG ω + fA ω + fT ω + fD ω
  have iG' : Integrable fG μ := iG
  have iA' : Integrable fA μ := iA
  have iT' : Integrable fT μ := iT
  have iD' : Integrable fD μ := iD
  have j1 : Integrable (fun ω => fG ω + fA ω) μ := iG'.add iA'
  have j2 : Integrable (fun ω => fG ω + fA ω + fT ω) μ := j1.add iT'
  have iS : Integrable S μ := j2.add iD'
  have hYS : ∀ᵐ ω ∂μ, Y ω ^ 12 ≤ S ω := by
    filter_upwards [hg0] with ω hω
    have a0 : 0 ≤ (W : ℝ) * jetDistance0 b E' (pathX b E' W r ω) :=
      mul_nonneg hWpos.le (norm_nonneg _)
    have t0 : 0 ≤ Real.sqrt W * (‖(passiveQ b E' (pathX b E' W r ω) *
        passiveF b E' (pathX b E' W r ω)).trace‖ +
        hsSandwich (passiveQ b E' (pathX b E' W r ω)) (passiveF b E' (pathX b E' W r ω))) :=
      mul_nonneg hs0.le (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    have d0 : 0 ≤ (W : ℝ) * jetDistance1 b E' s (pathX b E' W r ω) :=
      mul_nonneg hWpos.le (norm_nonneg _)
    exact br_Y12_le hω a0 t0 d0
  have hYm : AEStronglyMeasurable (fun ω => Y ω ^ 12) μ := by
    have : AEStronglyMeasurable Y μ :=
      ((((hgm.add_const 1).aestronglyMeasurable.mul
        ((hδ0m.const_mul (W : ℝ)).add aestronglyMeasurable_const)).mul
        ((hτm.const_mul (Real.sqrt W)).add aestronglyMeasurable_const)).mul
        ((hδ1m.const_mul (W : ℝ)).add aestronglyMeasurable_const))
    exact this.pow 12
  have iY : Integrable (fun ω => Y ω ^ 12) μ :=
    Integrable.mono' iS hYm (hYS.mono fun ω h => by
      rw [Real.norm_of_nonneg (by positivity)]; exact h)
  have mY : ∫ ω, Y ω ^ 12 ∂μ ≤ MY := by
    refine (integral_mono_ae iY iS hYS).trans ?_
    simp only [S]
    rw [integral_add j2 iD', integral_add j1 iT', integral_add iG' iA']
    have mA' : ∫ ω, fA ω ∂μ ≤ Ma := mA
    have mT' : ∫ ω, fT ω ∂μ ≤ Mt := mT
    have mD' : ∫ ω, fD ω ∂μ ≤ Ma := mD
    have mG' : ∫ ω, fG ω ∂μ ≤ Mg := mG
    simp only [MY]; linarith
  -- assemble
  rw [integral_powerIncrement_pow_four hb0 hb h1 h2 hW1 (by omega : 1 ≤ k + 1) hr1]
  have hpt : ∀ᵐ ω ∂μ, ∫ y, (((passiveTransmission b E' (freshSchur E' (pathX b E' W r ω) y)) ^
      (k + 1)).trace.re - ((passiveTransmission b E' (pathX b E' W r ω)) ^ (k + 1)).trace.re) ^ 4
        ∂freshLaw W b ≤ K * (Y ω ^ 12 / (W : ℝ) ^ 2) := by
    filter_upwards [mm_ae_passive (W := W) (b := b) (by linarith) h1 h2 r] with ω hω
    exact hd W hWd E' hE' s (pathX b E' W r ω) hω
  calc _ ≤ ∫ ω, K * (Y ω ^ 12 / (W : ℝ) ^ 2) ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => integral_nonneg fun y => by positivity)
          ((iY.div_const _).const_mul K) hpt
    _ = K / (W : ℝ) ^ 2 * ∫ ω, Y ω ^ 12 ∂μ := by
        rw [integral_const_mul, integral_div]; ring
    _ ≤ K / (W : ℝ) ^ 2 * MY := mul_le_mul_of_nonneg_left mY (by positivity)
    _ = K * MY / (W : ℝ) ^ 2 := by ring

end BlockBand.Transmission.Generator
