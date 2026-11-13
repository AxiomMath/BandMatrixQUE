module

public import BlockBand.Transmission.Generator.BrAe
public import BlockBand.Transmission.Generator.PowL2

/-!
# The bracket error in `L¹`, one length at a time

**`bracketError_L1 hMT hGA hLp hP`**: `b, κ, ε < T, k, l` first; then `K₁, K₂ ≥ 0, W₀`; for
`W ≥ W₀`, `E' ∈ bulkInterval κ`, every base energy `E` and `εW ≤ r ≤ TW`, `r ≥ 1`:
`‖bracketError b E E' W (k+1) (l+1) r‖₁ ≤ K₁W^{-3/2} + K₂|D₀(E) - D₀(E')|/W`.

Route: `bracketError_le` at a stationary jet of `E'`; `Y⁶ ≤ (g+1)²⁴ + (a+1)²⁴ + (t+1)²⁴ +
(d+1)²⁴` (`amgm4`); moments from `TransmissionLengthUniformContract.conductance` (`p = 24`),
`.jet` (`p = 24`) and `passiveSourceMixingBulk_holds` (`p = 24`).
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

theorem eLpNorm_one_le_of_ae_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z F : Ω → ℝ}
    (hZ : AEStronglyMeasurable Z μ) (hF : Integrable F μ) (hZF : ∀ᵐ ω ∂μ, |Z ω| ≤ F ω) :
    eLpNorm Z 1 μ ≤ ENNReal.ofReal (∫ ω, F ω ∂μ) := by
  have hF0 : 0 ≤ᵐ[μ] F := hZF.mono fun ω h => (abs_nonneg _).trans h
  calc eLpNorm Z 1 μ ≤ eLpNorm F 1 μ := eLpNorm_mono_ae hZ (hZF.mono fun ω h => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact h.trans (le_abs_self _))
    _ = ENNReal.ofReal (∫ ω, F ω ∂μ) := by
        rw [eLpNorm_one_eq_lintegral_enorm, ofReal_integral_eq_lintegral_ofReal hF hF0]
        refine lintegral_congr_ae ?_
        filter_upwards [hF0] with ω h
        exact Real.enorm_eq_ofReal h
        exact hF.aestronglyMeasurable

theorem br_Y6_le {x y z w : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    ((x + 1) * (y + 1) * (z + 1) * (w + 1)) ^ 6 ≤
      (x + 1) ^ 24 + (y + 1) ^ 24 + (z + 1) ^ 24 + (w + 1) ^ 24 := by
  have hA := amgm4 (x := (x + 1) ^ 6) (y := (y + 1) ^ 6) (z := (z + 1) ^ 6) (w := (w + 1) ^ 6)
    (by positivity) (by positivity) (by positivity) (by positivity)
  simp only [← pow_mul] at hA
  refine le_trans (le_of_eq ?_) hA
  rw [mul_pow, mul_pow, mul_pow]

/-- **`L¹` bound of the bracket error at one length.** -/
theorem bracketError_L1 (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) {b κ ε T : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (hε : 0 < ε) (hεT : ε < T) (k l : ℕ) :
    ∃ (K₁ K₂ : ℝ) (W₀ : ℕ), 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E' ∈ bulkInterval κ,
      ∀ E : ℝ, ∀ r : ℕ, 1 ≤ r → ε * W ≤ r → (r : ℝ) ≤ T * W →
        eLpNorm (bracketError b E E' W (k + 1) (l + 1) r) 1 (growthPathLaw W b) ≤
          ENNReal.ofReal (K₁ / Real.sqrt W ^ 3 +
            K₂ * |transportD0 b E - transportD0 b E'| / W) := by
  obtain ⟨K, Wd, hK, hd⟩ := bracketError_le hGA hLp hP hb0 hb hκ k l
  have hLU := transmissionLengthUniform_holds hMT hGA hLp
  obtain ⟨Cg, hgT⟩ := hLU.conductance b hb0 hb κ ε ((24 : ℕ) : ℝ) hκ hε (by norm_num)
  obtain ⟨Wg, hg⟩ := hgT T
  obtain ⟨Cj, hjT⟩ := hLU.jet b hb0 hb κ ε ((24 : ℕ) : ℝ) hκ hε (by norm_num)
  obtain ⟨Wj, hj⟩ := hjT T
  obtain ⟨Cm, Wm, hm⟩ := SourceMixingBulk.passiveSourceMixingBulk_holds hMT hGA hLp b hb0 hb κ ε T
    ((24 : ℕ) : ℝ) hκ hε hεT (by norm_num)
  set Cg' := max Cg 0
  set Cj' := max Cj 0
  set Cm' := max Cm 0
  set Mg : ℝ := 2 ^ 24 * (Cg' + 1)
  set Ma : ℝ := 2 ^ 24 * (Cj' ^ 24 + 1)
  set Mt : ℝ := 2 ^ 24 * (Cm' ^ 24 + 1)
  set MY := Mg + Ma + Mt + Ma
  set kl : ℝ := ((k + 1 : ℕ) : ℝ) * ((l + 1 : ℕ) : ℝ)
  refine ⟨K * MY, kl * MY, max (max Wd Wg) (max Wj Wm), by positivity, by positivity,
    fun W hW E' hE' E r hr1 hεr hrT => ?_⟩
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
  have hgi := integral_pow_le_of_lintegral (μ := μ) hgm hg0 24 (le_max_right Cg 0)
    ((hg W hWg E' hE' r hεr hrT).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have mG : ∫ ω, (pathG b E' W r ω + 1) ^ 24 ∂μ ≤ Mg :=
    (moment_shift hgm hg0 (hgB.mono fun _ h => h.2) 24).trans (by simp only [Mg]; gcongr)
  have iG : Integrable (fun ω => (pathG b E' W r ω + 1) ^ 24) μ :=
    integrable_of_bdd ((hgm.add_const 1).pow_const 24) (B := ((W : ℝ) + 1) ^ 24) (by
      filter_upwards [hgB] with ω h
      rw [abs_of_nonneg (by linarith [h.1] |> fun h' => pow_nonneg h' 24)]
      exact pow_le_pow_left₀ (by linarith [h.1]) (by linarith [h.2]) 24)
  -- the jet factors
  have hjet := hj W hWj E' hE' s hs r hεr hrT
  have hδ0m : AEStronglyMeasurable (fun ω => jetDistance0 b E' (pathX b E' W r ω)) μ :=
    ((measurable_jetDistance0 b E').comp hXm).aestronglyMeasurable
  have hδ1m : AEStronglyMeasurable (fun ω => jetDistance1 b E' s (pathX b E' W r ω)) μ :=
    (PathJet.measurable_pathJetV b E' s r).aestronglyMeasurable.congr
      (Filter.EventuallyEq.symm (PathJet.pathJet1_ae_eq (W := W) (b := b) (by linarith) h1 h2 s r))
  have hCjW : ENNReal.ofReal (Cj / W) ≤ ENNReal.ofReal (Cj' / W) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hWpos.le)
  obtain ⟨iA, mA⟩ := shifted_moment hδ0m (ae_of_all _ fun _ => norm_nonneg _) 24 (by norm_num)
    (le_max_right Cj 0) hWpos ((le_self_add.trans hjet).trans hCjW)
  obtain ⟨iD, mD⟩ := shifted_moment hδ1m (ae_of_all _ fun _ => norm_nonneg _) 24 (by norm_num)
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
        (ENNReal.ofReal ((24 : ℕ) : ℝ)) μ ≤ ENNReal.ofReal (Cm' / Real.sqrt W) := by
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    rw [eLpNorm_norm (fun ω => (passiveQ b E' (pathX b E' W r ω) *
      passiveF b E' (pathX b E' W r ω)).trace)
      (((measurable_traceQF b E').comp hXm).aestronglyMeasurable)]
    exact (hm W hWm E' hE' r hεr hrT).trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))
  obtain ⟨iT, mT⟩ := shifted_moment hτm
    (ae_of_all _ fun _ => add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) 24 (by norm_num)
    (le_max_right Cm 0) hs0 hτL
  -- `Y⁶` and its integral
  set Y : GrowthPath W → ℝ := fun ω => brY b E' s (pathX b E' W r ω)
  set fG : GrowthPath W → ℝ := fun ω => (pathG b E' W r ω + 1) ^ 24
  set fA : GrowthPath W → ℝ := fun ω => ((W : ℝ) * jetDistance0 b E' (pathX b E' W r ω) + 1) ^ 24
  set fT : GrowthPath W → ℝ := fun ω => (Real.sqrt W *
    (‖(passiveQ b E' (pathX b E' W r ω) * passiveF b E' (pathX b E' W r ω)).trace‖ +
      hsSandwich (passiveQ b E' (pathX b E' W r ω)) (passiveF b E' (pathX b E' W r ω))) + 1) ^ 24
  set fD : GrowthPath W → ℝ := fun ω => ((W : ℝ) * jetDistance1 b E' s (pathX b E' W r ω) + 1) ^ 24
  set S : GrowthPath W → ℝ := fun ω => fG ω + fA ω + fT ω + fD ω
  have iG' : Integrable fG μ := iG
  have iA' : Integrable fA μ := iA
  have iT' : Integrable fT μ := iT
  have iD' : Integrable fD μ := iD
  have j1 : Integrable (fun ω => fG ω + fA ω) μ := iG'.add iA'
  have j2 : Integrable (fun ω => fG ω + fA ω + fT ω) μ := j1.add iT'
  have iS : Integrable S μ := j2.add iD'
  have hYS : ∀ᵐ ω ∂μ, Y ω ^ 6 ≤ S ω := by
    filter_upwards [hg0] with ω hω
    have a0 : 0 ≤ (W : ℝ) * jetDistance0 b E' (pathX b E' W r ω) :=
      mul_nonneg hWpos.le (norm_nonneg _)
    have t0 : 0 ≤ Real.sqrt W * (‖(passiveQ b E' (pathX b E' W r ω) *
        passiveF b E' (pathX b E' W r ω)).trace‖ +
        hsSandwich (passiveQ b E' (pathX b E' W r ω)) (passiveF b E' (pathX b E' W r ω))) :=
      mul_nonneg hs0.le (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    have d0 : 0 ≤ (W : ℝ) * jetDistance1 b E' s (pathX b E' W r ω) :=
      mul_nonneg hWpos.le (norm_nonneg _)
    exact br_Y6_le hω a0 t0 d0
  have hYm : AEStronglyMeasurable (fun ω => Y ω ^ 6) μ := by
    have : AEStronglyMeasurable Y μ :=
      ((((hgm.add_const 1).aestronglyMeasurable.mul
        ((hδ0m.const_mul (W : ℝ)).add aestronglyMeasurable_const)).mul
        ((hτm.const_mul (Real.sqrt W)).add aestronglyMeasurable_const)).mul
        ((hδ1m.const_mul (W : ℝ)).add aestronglyMeasurable_const))
    exact this.pow 6
  have iY : Integrable (fun ω => Y ω ^ 6) μ :=
    Integrable.mono' iS hYm (hYS.mono fun ω h => by
      rw [Real.norm_of_nonneg (by positivity)]; exact h)
  have mY : ∫ ω, Y ω ^ 6 ∂μ ≤ MY := by
    refine (integral_mono_ae iY iS hYS).trans ?_
    simp only [S]
    rw [integral_add j2 iD', integral_add j1 iT', integral_add iG' iA']
    have mA' : ∫ ω, fA ω ∂μ ≤ Ma := mA
    have mT' : ∫ ω, fT ω ∂μ ≤ Mt := mT
    have mD' : ∫ ω, fD ω ∂μ ≤ Ma := mD
    have mG' : ∫ ω, fG ω ∂μ ≤ Mg := mG
    simp only [MY]; linarith
  -- assemble
  set c := K / Real.sqrt W ^ 3 + |transportD0 b E - transportD0 b E'| * kl / W
  have hc : 0 ≤ c := by positivity
  have hZm : AEStronglyMeasurable (bracketError b E E' W (k + 1) (l + 1) r) μ :=
    (stronglyMeasurable_condExp.mono (growthSigma_le W r)).aestronglyMeasurable.sub
      ((measurable_bracket_pathPowers b E E' (k + 1) (l + 1) r).mono (growthSigma_le W r)
        le_rfl).aestronglyMeasurable
  have hL := eLpNorm_one_le_of_ae_le hZm (iY.const_mul c) (hd W hWd E' hE' s hs E r hr1)
  refine hL.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [integral_const_mul]
  calc c * ∫ ω, Y ω ^ 6 ∂μ ≤ c * MY := mul_le_mul_of_nonneg_left mY hc
    _ = _ := by simp only [c]; ring

end BlockBand.Transmission.Generator
