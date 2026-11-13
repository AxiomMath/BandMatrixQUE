module

public import BlockBand.Transmission.LengthUniform.ConductanceUniform

/-!
# Length-uniform moments with explicit time-floor dependence

* `jet_explicit hMT hGA hLp`: one `C` (before `ε` and `T`) with
  `‖δ₀‖₂ + ‖δ₁‖₂ ≤ C/W` on `εW ≤ r ≤ TW` (`passiveJetMomentsUniform_of`; `ε` enters only
  `W₀`, through `C₁ log W ≤ εW`);
* `cond_explicit hMT hGA hLp`: one `K ≥ 0` (before `ε` and `T`) with
  `E g_r² ≤ (4K(1 + ε⁻¹))²` on `εW ≤ r ≤ TW` (`massMomentBound_bulk`, `g = 4ηq`, `η ≤ 1`).

Both repeat the proofs of `LengthUniform.lengthUniform_jet_of` and
`LengthUniform.lengthUniform_conductance_holds` with the quantifiers reordered.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFractional

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission BlockBand.Transmission.PathScalar BlockBand.Transmission.SourceMixing
open BlockBand.Transmission.LengthUniform
open scoped ENNReal

/-- **Jet moments with a constant free of the time floor.** -/
theorem jet_explicit (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ s : ℂ, IsStationaryJet b E s → ∀ r : ℕ, ε * W ≤ r → (r : ℝ) ≤ T * W →
        eLpNorm (fun ω => jetDistance0 b E (pathX b E W r ω)) (ENNReal.ofReal 2)
            (growthPathLaw W b) +
          eLpNorm (fun ω => jetDistance1 b E s (pathX b E W r ω)) (ENNReal.ofReal 2)
            (growthPathLaw W b) ≤
          ENNReal.ofReal (C / W) := by
  have hU := passiveJetMomentsUniform_of (deltaZeroLengthUniform_holds hMT hGA hLp) hGA hLp
  obtain ⟨C₁, C, hC⟩ := hU b hb0 hb κ 2 hκ (by norm_num)
  refine ⟨C, fun ε hε T => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hC T
  obtain ⟨W₁, hlog⟩ := log_le_eps_mul C₁ hε
  refine ⟨max (max W₀ W₁) 1, fun W hW E hE s hs r hεr hrT => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW0, hW1⟩, hW1'⟩ := hW
  have hx : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hr1 : 1 ≤ r := by
    have : (0 : ℝ) < r := lt_of_lt_of_le (mul_pos hε hx) hεr
    exact_mod_cast this
  exact hW₀ W hW0 E hE s hs r hr1 ((hlog W hW1).trans hεr) hrT

/-- **Second conductance moment with explicit time-floor dependence.** -/
theorem cond_explicit (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ r : ℕ, ε * W ≤ r → (r : ℝ) ≤ T * W →
        ∫⁻ ω, ‖pathConductance b E W r ω‖ₑ ^ (2 : ℝ) ∂growthPathLaw W b ≤
          ENNReal.ofReal ((4 * K * (1 + ε⁻¹)) ^ (2 : ℝ)) := by
  obtain ⟨K, hK, hKT⟩ := massMomentBound_bulk hMT hGA hLp hb0 hb hκ 2 (by norm_num)
  refine ⟨K, hK, fun ε hε T => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hKT T
  refine ⟨max W₀ 1, fun W hW E hE r hεr hrT => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hWW : W₀ ≤ W := le_of_max_le_left hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_of_max_le_right hW
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by nlinarith) hεr
  have hr1 : 1 ≤ r := by
    have : 0 < r := by exact_mod_cast hr0
    omega
  have hη := PassiveCovariance.etaZ_pos b E (by linarith) h1 h2
  have hη1 : etaZ b E ≤ 1 := bulk_eta_le_one hb0 hκ hE
  set P := growthPathLaw W b
  have hq := hW₀ W hWW E hE r hr1 hrT
  have hgL : eLpNorm (pathConductance b E W r) (ENNReal.ofReal 2) P ≤
      ENNReal.ofReal (4 * etaZ b E * (K * (1 + W / r))) := by
    have e : pathConductance b E W r =
        (4 * etaZ b E) • fun ω => passiveMass b E (pathX b E W r ω) := by
      funext ω; rw [pathConductance_eq_mass]; rfl
    rw [e, eLpNorm_const_smul, ENNReal.ofReal_mul (by positivity), Real.enorm_eq_ofReal_abs,
      abs_of_pos (by positivity)]
    exact mul_le_mul_right hq _
  have hWr : (W : ℝ) / r ≤ ε⁻¹ := by
    rw [div_le_iff₀ hr0, inv_mul_eq_div, le_div_iff₀ hε]; linarith
  have hle : 4 * etaZ b E * (K * (1 + W / r)) ≤ 4 * K * (1 + ε⁻¹) := by
    have h3 : K * (1 + W / r) ≤ K * (1 + ε⁻¹) := mul_le_mul_of_nonneg_left (by linarith) hK
    have h4 : 0 ≤ K * (1 + W / r) := by positivity
    nlinarith
  have hg := (measurable_pathConductance (W := W) b E r).aestronglyMeasurable (μ := P)
  refine (cm_lintegral_le hg (by norm_num) (by positivity) hgL).trans
    (ENNReal.ofReal_le_ofReal ?_)
  exact Real.rpow_le_rpow (by positivity) hle (by norm_num)

end BlockBand.Transmission.LawFractional
