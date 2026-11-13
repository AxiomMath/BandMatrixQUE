module

public import BlockBand.Transmission.Generator.PowAe
public import BlockBand.Transmission.Generator.PowL2Tools
public import BlockBand.Transmission.SourceMixingBulk.Mixing

/-!
# The `k = j + 2` drift error in `L²`, one length at a time

**`driftError_pow_L2 hMT hGA hLp hP`**: `b, κ, ε < T, j` first; then `K₁, K₂ ≥ 0, W₀`; for
`W ≥ W₀`, `E' ∈ bulkInterval κ`, every base energy `E` and `εW ≤ r ≤ TW`, `r ≥ 1`:
`‖driftError b E E' W (j+2) r‖₂ ≤ K₁W^{-3/2} + K₂|D₀(E) - D₀(E')|/W`.

Route: `driftError_pow_le` at a stationary jet `s` of `E'`, then `l2_prod4` with
`x = (g+1)⁵, y = (a+1)², z = (t+1)², w = d+1, v = (g+1)²`. Moments:
`∫(g+1)⁴⁰` (`TransmissionLengthUniformContract.conductance`, `p = 40`), `∫(a+1)¹⁶`, `∫(d+1)¹⁶`
(`.jet`, `p = 16`), `∫(t+1)¹⁶` (`passiveSourceMixingBulk_holds`, `p = 16`).
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

/-- **`L²` bound of the `k = j + 2` drift error at one length.** -/
theorem driftError_pow_L2 (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) {b κ ε T : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (hε : 0 < ε) (hεT : ε < T) (j : ℕ) :
    ∃ (K₁ K₂ : ℝ) (W₀ : ℕ), 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E' ∈ bulkInterval κ,
      ∀ E : ℝ, ∀ r : ℕ, 1 ≤ r → ε * W ≤ r → (r : ℝ) ≤ T * W →
        eLpNorm (driftError b E E' W (j + 2) r) 2 (growthPathLaw W b) ≤
          ENNReal.ofReal (K₁ / Real.sqrt W ^ 3 +
            K₂ * |transportD0 b E - transportD0 b E'| / W) := by
  obtain ⟨K, Wd, hK, hd⟩ := driftError_pow_le hGA hLp hP hb0 hb hκ j
  have hLU := transmissionLengthUniform_holds hMT hGA hLp
  obtain ⟨Cg, hgT⟩ := hLU.conductance b hb0 hb κ ε ((40 : ℕ) : ℝ) hκ hε (by norm_num)
  obtain ⟨Wg, hg⟩ := hgT T
  obtain ⟨Cj, hjT⟩ := hLU.jet b hb0 hb κ ε ((16 : ℕ) : ℝ) hκ hε (by norm_num)
  obtain ⟨Wj, hj⟩ := hjT T
  obtain ⟨Cm, Wm, hm⟩ := SourceMixingBulk.passiveSourceMixingBulk_holds hMT hGA hLp b hb0 hb κ ε T
    ((16 : ℕ) : ℝ) hκ hε hεT (by norm_num)
  set Cg' := max Cg 0
  set Cj' := max Cj 0
  set Cm' := max Cm 0
  set Mg : ℝ := 2 ^ 40 * (Cg' + 1)
  set Ma : ℝ := 2 ^ 16 * (Cj' ^ 16 + 1)
  set Mt : ℝ := 2 ^ 16 * (Cm' ^ 16 + 1)
  set n2 : ℝ := ((j + 2 : ℕ) : ℝ) ^ 2
  refine ⟨K * Real.sqrt (Mg + Ma + Mt + Ma), n2 * Real.sqrt Mg, max (max Wd Wg) (max Wj Wm),
    by positivity, by positivity, fun W hW E' hE' E r hr1 hεr hrT => ?_⟩
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
  have hs2 : Real.sqrt W ^ 2 = W := Real.sq_sqrt hWpos.le
  set μ := growthPathLaw W b
  have hXm := PathJet.measurable_pathX (W := W) b E' r
  -- the conductance factor
  have hgm : Measurable (pathG b E' W r) := measurable_pathConductance b E' r
  have hgB : ∀ᵐ ω ∂μ, 0 ≤ pathG b E' W r ω ∧ pathG b E' W r ω ≤ W := by
    filter_upwards [pathPower_mem (W := W) (by linarith : b < 1) h1 h2] with ω hω
    obtain ⟨h0, h1', h3⟩ := hω 1 r le_rfl
    exact ⟨h0.trans h1', h3⟩
  have hg0 : ∀ᵐ ω ∂μ, 0 ≤ pathG b E' W r ω := hgB.mono fun _ h => h.1
  have hgi := integral_pow_le_of_lintegral (μ := μ) hgm hg0 40 (le_max_right Cg 0)
    ((hg W hWg E' hE' r hεr hrT).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have mG : ∫ ω, (pathG b E' W r ω + 1) ^ 40 ∂μ ≤ Mg :=
    (moment_shift hgm hg0 (hgB.mono fun _ h => h.2) 40).trans (by simp only [Mg]; gcongr)
  have iG : ∀ m : ℕ, Integrable (fun ω => (pathG b E' W r ω + 1) ^ m) μ := fun m =>
    integrable_of_bdd ((hgm.add_const 1).pow_const m) (B := ((W : ℝ) + 1) ^ m) (by
      filter_upwards [hgB] with ω h
      rw [abs_of_nonneg (by linarith [h.1] |> fun h' => pow_nonneg h' m)]
      exact pow_le_pow_left₀ (by linarith [h.1]) (by linarith [h.2]) m)
  have hG1 : ∀ᵐ ω ∂μ, 1 ≤ pathG b E' W r ω + 1 := hg0.mono fun _ h => by linarith
  -- the jet factors
  have hjet := hj W hWj E' hE' s hs r hεr hrT
  have hδ0m : AEStronglyMeasurable (fun ω => jetDistance0 b E' (pathX b E' W r ω)) μ :=
    ((measurable_jetDistance0 b E').comp hXm).aestronglyMeasurable
  have hδ1m : AEStronglyMeasurable (fun ω => jetDistance1 b E' s (pathX b E' W r ω)) μ :=
    (PathJet.measurable_pathJetV b E' s r).aestronglyMeasurable.congr
      (Filter.EventuallyEq.symm (PathJet.pathJet1_ae_eq (W := W) (b := b) (by linarith) h1 h2 s r))
  have hCjW : ENNReal.ofReal (Cj / W) ≤ ENNReal.ofReal (Cj' / W) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hWpos.le)
  obtain ⟨iA, mA⟩ := shifted_moment hδ0m (ae_of_all _ fun _ => norm_nonneg _) 16 (by norm_num)
    (le_max_right Cj 0) hWpos ((le_self_add.trans hjet).trans hCjW)
  obtain ⟨iD, mD⟩ := shifted_moment hδ1m (ae_of_all _ fun _ => norm_nonneg _) 16 (by norm_num)
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
        (ENNReal.ofReal ((16 : ℕ) : ℝ)) μ ≤ ENNReal.ofReal (Cm' / Real.sqrt W) := by
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    rw [eLpNorm_norm (fun ω => (passiveQ b E' (pathX b E' W r ω) *
      passiveF b E' (pathX b E' W r ω)).trace)
      (((measurable_traceQF b E').comp hXm).aestronglyMeasurable)]
    exact (hm W hWm E' hE' r hεr hrT).trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))
  obtain ⟨iT, mT⟩ := shifted_moment hτm
    (ae_of_all _ fun _ => add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) 16 (by norm_num)
    (le_max_right Cm 0) hs0 hτL
  -- assemble
  have hZm : AEStronglyMeasurable (driftError b E E' W (j + 2) r) μ :=
    (stronglyMeasurable_condExp.mono (growthSigma_le W r)).aestronglyMeasurable.sub
      ((measurable_drift_pathPowers b E E' (j + 2) r).mono (growthSigma_le W r)
        le_rfl).aestronglyMeasurable
  have hgam : AEStronglyMeasurable (fun ω => pathG b E' W r ω + 1) μ :=
    (hgm.add_const 1).aestronglyMeasurable
  have hDm : AEStronglyMeasurable (fun ω => pathD b E' s W r ω + 1) μ :=
    ((hδ1m.const_mul (W : ℝ)).add aestronglyMeasurable_const)
  have hD1 : ∀ ω, 1 ≤ pathD b E' s W r ω + 1 := fun ω => by
    have : 0 ≤ (W : ℝ) * jetDistance1 b E' s (pathX b E' W r ω) :=
      mul_nonneg hWpos.le (norm_nonneg _)
    unfold pathD; linarith
  have iD8 : Integrable (fun ω => (pathD b E' s W r ω + 1) ^ 8) μ := by
    refine Integrable.mono' iD (hDm.pow 8) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (by linarith [hD1 ω]) 8)]
    exact pow_le_pow_right₀ (hD1 ω) (by norm_num)
  have eG : ∀ (m n : ℕ) ω, ((pathG b E' W r ω + 1) ^ m) ^ n = (pathG b E' W r ω + 1) ^ (m * n) :=
    fun m n ω => (pow_mul _ m n).symm
  have eA : ∀ ω, ((pathA b E' W r ω + 1) ^ 2) ^ 8 =
      ((W : ℝ) * jetDistance0 b E' (pathX b E' W r ω) + 1) ^ 16 := fun ω => by
    rw [← pow_mul]; rfl
  have eT : ∀ ω, ((pathT b E' W r ω + 1) ^ 2) ^ 8 = (Real.sqrt W *
      (‖(passiveQ b E' (pathX b E' W r ω) * passiveF b E' (pathX b E' W r ω)).trace‖ +
        hsSandwich (passiveQ b E' (pathX b E' W r ω)) (passiveF b E' (pathX b E' W r ω))) +
          1) ^ 16 := fun ω => by
    rw [← pow_mul]; rfl
  have hL := l2_prod4 (μ := μ) (Z := driftError b E E' W (j + 2) r)
    (x := fun ω => (pathG b E' W r ω + 1) ^ 5) (y := fun ω => (pathA b E' W r ω + 1) ^ 2)
    (z := fun ω => (pathT b E' W r ω + 1) ^ 2) (w := fun ω => pathD b E' s W r ω + 1)
    (v := fun ω => (pathG b E' W r ω + 1) ^ 2) (K := K)
    (Δ := |transportD0 b E - transportD0 b E'| * n2) (s := Real.sqrt W)
    (Mx := Mg) (My := Ma) (Mz := Mt) (Mw := Ma) (Mv := Mg) hZm (hgam.pow 5)
    (((hδ0m.const_mul (W : ℝ)).add aestronglyMeasurable_const).pow 2)
    (((hτm.const_mul (Real.sqrt W)).add aestronglyMeasurable_const).pow 2) hDm (hgam.pow 2)
    (hg0.mono fun _ h => by positivity) (ae_of_all _ fun _ => sq_nonneg _)
    (ae_of_all _ fun _ => sq_nonneg _)
    (ae_of_all _ fun ω => by linarith [hD1 ω]) hK (by positivity) hs0
    (hd W hWd E' hE' s hs E r hr1)
    ((iG 40).congr (ae_of_all _ fun ω => (eG 5 8 ω).symm))
    (iA.congr (ae_of_all _ fun ω => (eA ω).symm))
    (iT.congr (ae_of_all _ fun ω => (eT ω).symm)) iD8
    ((iG 4).congr (ae_of_all _ fun ω => (eG 2 2 ω).symm))
    ((le_of_eq (integral_congr_ae (ae_of_all _ fun ω => eG 5 8 ω))).trans mG)
    ((le_of_eq (integral_congr_ae (ae_of_all _ eA))).trans mA)
    ((le_of_eq (integral_congr_ae (ae_of_all _ eT))).trans mT)
    (le_trans (integral_mono_ae iD8 iD (ae_of_all _ fun ω =>
      pow_le_pow_right₀ (hD1 ω) (by norm_num))) mD)
    (by
      refine le_trans (le_of_eq (integral_congr_ae (ae_of_all _ fun ω => eG 2 2 ω))) ?_
      refine le_trans (integral_mono_ae (iG 4) (iG 40) ?_) mG
      filter_upwards [hG1] with ω h
      exact pow_le_pow_right₀ h (by norm_num))
  refine hL.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [hs2]; ring

end BlockBand.Transmission.Generator
