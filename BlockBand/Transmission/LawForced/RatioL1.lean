module

public import BlockBand.Transmission.LawForced.RatioCond
public import BlockBand.Transmission.Generator.PowL2

/-!
# The `κ ≡ 0` ratio drift error in `L¹` at one length

* `prod27_le`: `(xyzw)²⁷ ≤ x¹⁰⁸ + y¹⁰⁸ + z¹⁰⁸ + w¹⁰⁸` (`x, y, z, w ≥ 0`, `amgm4`);
* **`ratioDriftError_zero_L1 hMT hGA hLp hP`**: `∃ K W₀`, for `W ≥ W₀`, `E ∈ bulkInterval κ_I`,
  `1 ≤ r`, `εW ≤ r ≤ TW`: `E|ratioDriftError b E 0 W z r| ≤ K·W^{-3/2}`. Moments:
  `TransmissionLengthUniformContract.conductance` and `.jet` (`p = 108`) and
  `SourceMixingBulk.passiveSourceMixingBulk_holds` (`p = 108`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PathScalar BlockBand.Transmission.SourceMixing
open BlockBand.Transmission.LengthUniform BlockBand.Transmission.Generator
open BlockBand.Transmission.LawDuality
open scoped ENNReal ComplexOrder

variable {p W : ℕ}

theorem prod27_le {x y z w : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    (x * y * z * w) ^ 27 ≤ x ^ 108 + y ^ 108 + z ^ 108 + w ^ 108 := by
  have h := amgm4 (pow_nonneg hx 27) (pow_nonneg hy 27) (pow_nonneg hz 27) (pow_nonneg hw 27)
  simp only [← pow_mul] at h
  calc (x * y * z * w) ^ 27 = x ^ 27 * y ^ 27 * z ^ 27 * w ^ 27 := by ring
    _ ≤ _ := h

theorem step27_le {K v x y z w : ℝ} (hK : 0 ≤ K) (hv : 0 ≤ v) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hw : 0 ≤ w) :
    K * ((x * y * z * w) ^ 27 * v ^ 3) ≤ K * v ^ 3 * (x ^ 108 + y ^ 108 + z ^ 108 + w ^ 108) := by
  rw [mul_comm ((x * y * z * w) ^ 27) (v ^ 3), ← mul_assoc]
  exact mul_le_mul_of_nonneg_left (prod27_le hx hy hz hw) (mul_nonneg hK (pow_nonneg hv 3))

/-- **`L¹` bound of the `κ ≡ 0` ratio drift error at one length.** -/
theorem ratioDriftError_zero_L1 (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) {b κ ε T : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (hε : 0 < ε) (hεT : ε < T) {z : DualCoord p}
    (hz : z ∈ dualChamber p) :
    ∃ (K : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ r : ℕ, 1 ≤ r →
      ε * W ≤ r → (r : ℝ) ≤ T * W →
        ∫ ω, |ratioDriftError b E (fun _ => 0) W z r ω| ∂growthPathLaw W b ≤
          K * (Real.sqrt W)⁻¹ ^ 3 := by
  obtain ⟨K, Wd, hK, hd⟩ := ratio_layer_bulk hGA hLp hP hb0 hb hκ hz
  have hLU := transmissionLengthUniform_holds hMT hGA hLp
  obtain ⟨Cg, hgT⟩ := hLU.conductance b hb0 hb κ ε ((108 : ℕ) : ℝ) hκ hε (by norm_num)
  obtain ⟨Wg, hg⟩ := hgT T
  obtain ⟨Cj, hjT⟩ := hLU.jet b hb0 hb κ ε ((108 : ℕ) : ℝ) hκ hε (by norm_num)
  obtain ⟨Wj, hj⟩ := hjT T
  obtain ⟨Cm, Wm, hm⟩ := SourceMixingBulk.passiveSourceMixingBulk_holds hMT hGA hLp b hb0 hb κ ε T
    ((108 : ℕ) : ℝ) hκ hε hεT (by norm_num)
  set Cg' := max Cg 0
  set Cj' := max Cj 0
  set Cm' := max Cm 0
  set Mg : ℝ := 2 ^ 108 * (Cg' + 1)
  set Ma : ℝ := 2 ^ 108 * (Cj' ^ 108 + 1)
  set Mt : ℝ := 2 ^ 108 * (Cm' ^ 108 + 1)
  refine ⟨K * (Mg + Ma + Mt + Ma), max (max Wd Wg) (max Wj Wm),
    fun W hW E hE r hr1 hεr hrT => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWd, hWg⟩, hWj, hWm⟩ := hW
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
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
  have hXm := PathJet.measurable_pathX (W := W) b E r
  -- the conductance factor
  have hgm : Measurable (pathG b E W r) := measurable_pathConductance b E r
  have hgB : ∀ᵐ ω ∂μ, 0 ≤ pathG b E W r ω ∧ pathG b E W r ω ≤ W := by
    filter_upwards [pathPower_mem (W := W) (by linarith : b < 1) h1 h2] with ω hω
    obtain ⟨h0, h1', h3⟩ := hω 1 r le_rfl
    exact ⟨h0.trans h1', h3⟩
  have hg0 : ∀ᵐ ω ∂μ, 0 ≤ pathG b E W r ω := hgB.mono fun _ h => h.1
  have hgi := integral_pow_le_of_lintegral (μ := μ) hgm hg0 108 (le_max_right Cg 0)
    ((hg W hWg E hE r hεr hrT).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have mG : ∫ ω, (pathG b E W r ω + 1) ^ 108 ∂μ ≤ Mg :=
    (moment_shift hgm hg0 (hgB.mono fun _ h => h.2) 108).trans (by simp only [Mg]; gcongr)
  have iG : Integrable (fun ω => (pathG b E W r ω + 1) ^ 108) μ :=
    integrable_of_bdd ((hgm.add_const 1).pow_const 108) (B := ((W : ℝ) + 1) ^ 108) (by
      filter_upwards [hgB] with ω h
      rw [abs_of_nonneg (pow_nonneg (by linarith [h.1]) 108)]
      exact pow_le_pow_left₀ (by linarith [h.1]) (by linarith [h.2]) 108)
  -- the jet factors
  have hjet := hj W hWj E hE s hs r hεr hrT
  have hδ0m : AEStronglyMeasurable (fun ω => jetDistance0 b E (pathX b E W r ω)) μ :=
    ((measurable_jetDistance0 b E).comp hXm).aestronglyMeasurable
  have hδ1m : AEStronglyMeasurable (fun ω => jetDistance1 b E s (pathX b E W r ω)) μ :=
    (PathJet.measurable_pathJetV b E s r).aestronglyMeasurable.congr
      (Filter.EventuallyEq.symm (PathJet.pathJet1_ae_eq (W := W) (b := b) (by linarith) h1 h2 s r))
  have hCjW : ENNReal.ofReal (Cj / W) ≤ ENNReal.ofReal (Cj' / W) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hWpos.le)
  obtain ⟨iA, mA⟩ := shifted_moment hδ0m (ae_of_all _ fun _ => norm_nonneg _) 108 (by norm_num)
    (le_max_right Cj 0) hWpos ((le_self_add.trans hjet).trans hCjW)
  obtain ⟨iD, mD⟩ := shifted_moment hδ1m (ae_of_all _ fun _ => norm_nonneg _) 108 (by norm_num)
    (le_max_right Cj 0) hWpos ((le_add_self.trans hjet).trans hCjW)
  -- the mixing factor
  have hτm : AEStronglyMeasurable (fun ω =>
      ‖(passiveQ b E (pathX b E W r ω) * passiveF b E (pathX b E W r ω)).trace‖ +
        hsSandwich (passiveQ b E (pathX b E W r ω)) (passiveF b E (pathX b E W r ω))) μ :=
    ((((measurable_traceQF b E).comp hXm).norm).add
      ((measurable_hsQF b E).comp hXm)).aestronglyMeasurable
  have hτL : eLpNorm (fun ω =>
      ‖(passiveQ b E (pathX b E W r ω) * passiveF b E (pathX b E W r ω)).trace‖ +
        hsSandwich (passiveQ b E (pathX b E W r ω)) (passiveF b E (pathX b E W r ω)))
        (ENNReal.ofReal ((108 : ℕ) : ℝ)) μ ≤ ENNReal.ofReal (Cm' / Real.sqrt W) := by
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    rw [eLpNorm_norm (fun ω => (passiveQ b E (pathX b E W r ω) *
      passiveF b E (pathX b E W r ω)).trace)
      (((measurable_traceQF b E).comp hXm).aestronglyMeasurable)]
    exact (hm W hWm E hE r hεr hrT).trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))
  obtain ⟨iT, mT⟩ := shifted_moment hτm
    (ae_of_all _ fun _ => add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) 108 (by norm_num)
    (le_max_right Cm 0) hs0 hτL
  -- the pointwise bound
  set v := (Real.sqrt W)⁻¹
  have hv0 : 0 ≤ v := inv_nonneg.2 hs0.le
  set B : GrowthPath W → ℝ := fun ω => K * v ^ 3 * ((pathG b E W r ω + 1) ^ 108 +
    ((W : ℝ) * jetDistance0 b E (pathX b E W r ω) + 1) ^ 108 +
    (Real.sqrt W * (‖(passiveQ b E (pathX b E W r ω) * passiveF b E (pathX b E W r ω)).trace‖ +
        hsSandwich (passiveQ b E (pathX b E W r ω)) (passiveF b E (pathX b E W r ω))) + 1) ^ 108 +
    ((W : ℝ) * jetDistance1 b E s (pathX b E W r ω) + 1) ^ 108)
  have iB : Integrable B μ := (((iG.add iA).add iT).add iD).const_mul _
  have hpt : ∀ᵐ ω ∂μ, |ratioDriftError b E (fun _ => 0) W z r ω| ≤ B ω := by
    filter_upwards [ratioDriftError_zero_ae hz hb0 hb h1 h2 hW1 hr1,
      SourceMixing.mm_ae_passive (W := W) (b := b) (by linarith) h1 h2 r, hg0] with ω he hX hg
    rw [he]
    refine (hd W hWd E hE s hs _ hX _).trans ?_
    have hT0 : 0 ≤ (W : ℝ) * jetDistance0 b E (pathX b E W r ω) :=
      mul_nonneg hWpos.le (norm_nonneg _)
    have hD0 : 0 ≤ (W : ℝ) * jetDistance1 b E s (pathX b E W r ω) :=
      mul_nonneg hWpos.le (norm_nonneg _)
    have hM0 : 0 ≤ Real.sqrt W * (‖(passiveQ b E (pathX b E W r ω) *
        passiveF b E (pathX b E W r ω)).trace‖ + hsSandwich (passiveQ b E (pathX b E W r ω))
          (passiveF b E (pathX b E W r ω))) :=
      mul_nonneg hs0.le (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    have e : ratioP b E s (pathX b E W r ω) = (pathG b E W r ω + 1) *
        ((W : ℝ) * jetDistance0 b E (pathX b E W r ω) + 1) *
        (Real.sqrt W * (‖(passiveQ b E (pathX b E W r ω) *
          passiveF b E (pathX b E W r ω)).trace‖ + hsSandwich (passiveQ b E (pathX b E W r ω))
            (passiveF b E (pathX b E W r ω))) + 1) *
        ((W : ℝ) * jetDistance1 b E s (pathX b E W r ω) + 1) := rfl
    rw [e]
    exact step27_le hK hv0 (by linarith [hg]) (by linarith) (by linarith) (by linarith)
  have hEi : Integrable (fun ω => |ratioDriftError b E (fun _ => 0) W z r ω|) μ :=
    (integrable_condExp.sub (integrable_ratioDriftAt isAbsorptionProfile_zero' (by linarith)
      h1 h2 hz r)).abs
  refine (integral_mono_ae hEi iB hpt).trans ?_
  have j1 : Integrable (fun ω => (pathG b E W r ω + 1) ^ 108 +
      ((W : ℝ) * jetDistance0 b E (pathX b E W r ω) + 1) ^ 108) μ := iG.add iA
  have j2 : Integrable (fun ω => (pathG b E W r ω + 1) ^ 108 +
      ((W : ℝ) * jetDistance0 b E (pathX b E W r ω) + 1) ^ 108 +
      (Real.sqrt W * (‖(passiveQ b E (pathX b E W r ω) * passiveF b E (pathX b E W r ω)).trace‖ +
        hsSandwich (passiveQ b E (pathX b E W r ω)) (passiveF b E (pathX b E W r ω))) + 1) ^ 108)
      μ := j1.add iT
  simp only [B]
  rw [integral_const_mul, integral_add j2 iD, integral_add j1 iT, integral_add iG iA]
  have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add mG mA) mT) mD)
    (mul_nonneg hK (pow_nonneg hv0 3))
  exact this.trans (le_of_eq (by ring))

end BlockBand.Transmission.LawForced
