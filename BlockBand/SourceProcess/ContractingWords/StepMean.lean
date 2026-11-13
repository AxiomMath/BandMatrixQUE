module

public import BlockBand.SourceProcess.ContractingWords.StepState
public import BlockBand.Transmission.LengthUniform.ConductanceUniform
public import BlockBand.Transmission.SourceMixing.Conductance

/-!
# Path moments of the one-layer error

`errMoments`: along the growth path, the error `δ₀ + δ₁ + |g|/W + W⁻¹` at length `εW ≤ r ≤ TW` has
`L^p` norm at most `C/W`, uniformly on the bulk and in the stationary jet.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.LengthUniform
open BlockBand.Transmission.SourceMixing
open scoped ENNReal

variable {W : ℕ}

theorem eLpNorm_le_of_lintegral_rpow {f : GrowthPath W → ℝ} (hf : Measurable f) {μ : Measure (GrowthPath W)}
    {p C : ℝ} (hp : 1 ≤ p) (h : ∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ ≤ ENNReal.ofReal C) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (max C 0 ^ (1 / p)) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal (by linarith)]
  calc (∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal (max C 0) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
          (by positivity)
    _ = _ := ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) (by positivity)

/-- **Path moments of the mean error.** -/
theorem errMoments (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ)
    {ε T p : ℝ} (hε : 0 < ε) (hp : 1 ≤ p) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ s : ℂ, IsStationaryJet b E s → ∀ r : ℕ, ε * W ≤ r → (r : ℝ) ≤ T * W →
        eLpNorm (fun ω => jetDistance0 b E (pathX b E W r ω) +
            jetDistance1 b E s (pathX b E W r ω) + |pathConductance b E W r ω| / W + (W : ℝ)⁻¹)
          (ENNReal.ofReal p) (growthPathLaw W b) ≤ ENNReal.ofReal (C / W) := by
  obtain ⟨Cj, hCj⟩ := lengthUniform_jet_holds hMT hGA hLp b hb0 hb κ ε p hκ hε hp
  obtain ⟨Wj, hWj⟩ := hCj T
  obtain ⟨Cg, hCg⟩ := lengthUniform_conductance_holds hMT hGA hLp b hb0 hb κ ε p hκ hε hp
  obtain ⟨Wg, hWg⟩ := hCg T
  set Cg' := max Cg 0 ^ (1 / p)
  refine ⟨max Cj 0 + Cg' + 1, max (max Wj Wg) 1, by positivity, fun W hW E hE s hs r hr1 hr2 => ?_⟩
  simp only [max_le_iff] at hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using hp
  have hj := (hWj W hW.1.1 E hE s hs r hr1 hr2).trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (le_max_left Cj 0) hW0.le))
  have hg : eLpNorm (fun ω => |pathConductance b E W r ω|) (ENNReal.ofReal p) (growthPathLaw W b) ≤
      ENNReal.ofReal Cg' := by
    refine eLpNorm_le_of_lintegral_rpow (measurable_pathConductance b E r).abs hp ?_
    simpa only [Real.enorm_abs] using hWg W hW.1.2 E hE r hr1 hr2
  have hgW : eLpNorm (fun ω => |pathConductance b E W r ω| / W) (ENNReal.ofReal p)
      (growthPathLaw W b) ≤ ENNReal.ofReal (Cg' / W) := by
    have e : (fun ω => |pathConductance b E W r ω| / W) =
        (W : ℝ)⁻¹ • fun ω => |pathConductance b E W r ω| := by
      funext ω; simp [smul_eq_mul, div_eq_inv_mul]
    rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
    calc ENNReal.ofReal (W : ℝ)⁻¹ * eLpNorm (fun ω => |pathConductance b E W r ω|)
          (ENNReal.ofReal p) (growthPathLaw W b) ≤ ENNReal.ofReal (W : ℝ)⁻¹ * ENNReal.ofReal Cg' := by
          gcongr
      _ = ENNReal.ofReal (Cg' / W) := by
          rw [← ENNReal.ofReal_mul (by positivity), div_eq_inv_mul]
  have h1 : eLpNorm (fun _ : GrowthPath W => (W : ℝ)⁻¹) (ENNReal.ofReal p) (growthPathLaw W b) ≤
      ENNReal.ofReal (1 / W) := by
    refine (eLpNorm_le_of_ae_bound aestronglyMeasurable_const (C := (W : ℝ)⁻¹)
      (Eventually.of_forall fun _ => by rw [Real.norm_of_nonneg (by positivity)])).trans ?_
    have : IsProbabilityMeasure (growthPathLaw W b) := by unfold growthPathLaw; infer_instance
    simp
  have e : (fun ω => jetDistance0 b E (pathX b E W r ω) + jetDistance1 b E s (pathX b E W r ω) +
      |pathConductance b E W r ω| / W + (W : ℝ)⁻¹) =
      ((fun ω => jetDistance0 b E (pathX b E W r ω)) + fun ω => jetDistance1 b E s (pathX b E W r ω)) +
        (fun ω => |pathConductance b E W r ω| / W) + fun _ => (W : ℝ)⁻¹ := by
    funext ω; simp
  rw [e]
  refine (eLpNorm_add_le hp1).trans ((add_le_add ((eLpNorm_add_le hp1).trans
    (add_le_add ((eLpNorm_add_le hp1).trans hj) hgW)) h1).trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity)
    (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e2 : (max Cj 0 + Cg' + 1) / W = max Cj 0 / W + Cg' / W + 1 / W := by ring
  linarith

end BlockBand.SourceProcess.ContractingWords
