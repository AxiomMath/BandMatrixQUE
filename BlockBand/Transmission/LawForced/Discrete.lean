module

public import BlockBand.Transmission.LawForced.Interface
public import BlockBand.Transmission.LawDuality.TightAbsorbed
public import BlockBand.Transmission.LawDuality.RatioCompact
public import BlockBand.Transmission.LawDuality.RatioWeakGen
public import BlockBand.Transmission.Generator.Discrete

/-!
# The tested finite-`W` ratio identity

* `stateAt` (the clamped, measurable trace measure at length `r`), `measurable_stateAt`
  (`𝓕_r`-measurable), `ae_stateAt_eq` (a.s. `= traceMeasure T_r` for all `r`);
* `exists_bound_drift` (`exists_bound_ratioDrift` at the compact `{z}`: the drift is
  bounded uniformly in `u` and `ν`), `continuous_ratioDrift_nu`;
* `integrable_ratioAt`, `integrable_ratioDriftAt`;
* **`abs_integral_ratio_drift_le`**: for a bounded `𝓕_{r₀}`-measurable `ψ` and `r₀ ≤ r₁`,
  `|E[ψ(F(μ^{r₁}) − F(μ^{r₀}) − Σ_{r₀ ≤ r < r₁} ratioDriftAt_r/W)]| ≤ B Σ E|ratioDriftError_r|`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.LawDuality
open scoped NNReal ENNReal

variable {W : ℕ}

/-- `T_r` is `𝓕_r`-measurable. -/
theorem measurable_pathTransmission_adapted (b E : ℝ) (κ : ℝ → ℝ) (r : ℕ) :
    Measurable[growthSigma W r] (pathTransmission b E κ W r) := by
  have hc : Continuous fun Q : Matrix (Fin W) (Fin W) ℂ => (((4 * etaZ b E : ℝ)) : ℂ) • Q :=
    continuous_const_smul _
  exact hc.measurable.comp ((SourceMixing.mu_measurable_passiveQ b E).comp
    (Bridge.pathNearSchur_adapted b E κ W r))

/-- The measurable state at length `r` (`= μ^r` a.s.). -/
def stateAt (b E : ℝ) (κ : ℝ → ℝ) (W r : ℕ) (ω : GrowthPath W) : FiniteMeasure unitInterval :=
  clampedTraceMeasure (pathTransmission b E κ W r ω)

theorem measurable_stateAt (b E : ℝ) (κ : ℝ → ℝ) (r : ℕ) :
    Measurable[growthSigma W r] (stateAt b E κ W r) :=
  measurable_clampedTraceMeasure.comp (measurable_pathTransmission_adapted b E κ r)

theorem measurable_stateAt' (b E : ℝ) (κ : ℝ → ℝ) (r : ℕ) :
    Measurable (stateAt b E κ W r) :=
  (measurable_stateAt b E κ r).mono (Generator.growthSigma_le W r) le_rfl

theorem ae_stateAt_eq {b E : ℝ} {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) (hb : b < 1) (hE1 : -2 < E)
    (hE2 : E < 2) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ r : ℕ,
      stateAt b E κ W r ω = traceMeasure (pathTransmission b E κ W r ω) := by
  filter_upwards [Bridge.ae_passiveSample W hκ hb hE1 hE2] with ω hω r
  rw [stateAt, clampedTraceMeasure, ite_eq_left ⟨Bridge.pathTransmission_posSemidef hω _,
    Bridge.one_sub_pathTransmission_posSemidef b E κ W _ ω⟩]

/-- The drift at a chamber point is bounded uniformly in time and measure. -/
theorem exists_bound_drift (D0 E : ℝ) {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) {p : ℕ}
    {z : DualCoord p} (hz : z ∈ dualChamber p) :
    ∃ C, 0 ≤ C ∧ ∀ u : ℝ, ∀ ν : FiniteMeasure unitInterval, |ratioDrift D0 E κ u z ν| ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_ratioDrift D0 E hκ isCompact_singleton
    (Set.singleton_subset_iff.mpr hz)
  exact ⟨max C 0, le_max_right _ _, fun u ν =>
    (hC u z (Set.mem_singleton z) ν).trans (le_max_left _ _)⟩

theorem continuous_ratioDrift_nu (D0 E : ℝ) {κ : ℝ → ℝ} (hκ : Continuous κ) {p : ℕ}
    {z : DualCoord p} (hz : z ∈ dualChamber p) (u : ℝ) :
    Continuous fun ν : FiniteMeasure unitInterval => ratioDrift D0 E κ u z ν :=
  continuous_iff_continuousAt.mpr fun ν =>
    (continuousAt_ratioDrift D0 E hκ u hz ν).comp (f := fun ν : FiniteMeasure unitInterval =>
      ((u, (z, ν)) : ℝ × (DualCoord p × FiniteMeasure unitInterval)))
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousAt

theorem continuous_ratio_nu {p : ℕ} {z : DualCoord p} (hz : z ∈ dualChamber p) :
    Continuous fun ν : FiniteMeasure unitInterval => transmissionRatio z.1 z.2 ν :=
  continuous_transmissionRatio_vec (IsRatioParameter.isRatioRange hz)

section Integrable

variable {b E : ℝ} {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) (hb : b < 1) (hE1 : -2 < E)
  (hE2 : E < 2) {p : ℕ} {z : DualCoord p} (hz : z ∈ dualChamber p)
include hκ hb hE1 hE2 hz

omit hz in
theorem ratioAt_ae_eq (r : ℕ) :
    ratioAt b E κ W r z =ᵐ[growthPathLaw W b]
      fun ω => transmissionRatio z.1 z.2 (stateAt b E κ W r ω) := by
  filter_upwards [ae_stateAt_eq hκ.2.1 hb hE1 hE2] with ω hω
  rw [ratioAt, hω r]

theorem integrable_ratioAt (r : ℕ) : Integrable (ratioAt b E κ W r z) (growthPathLaw W b) := by
  have hm : Measurable fun ω => transmissionRatio z.1 z.2 (stateAt b E κ W r ω) :=
    (continuous_ratio_nu hz).measurable.comp (measurable_stateAt' b E κ r)
  refine (Generator.integrable_of_ae_bound hm (c := 1) (Eventually.of_forall fun ω => ?_)).congr
    (ratioAt_ae_eq hκ hb hE1 hE2 r).symm
  have h := transmissionRatio_mem_vec (IsRatioParameter.isRatioRange hz) (stateAt b E κ W r ω)
  rw [abs_of_pos h.1]; exact h.2

theorem integrable_ratioDriftAt (r : ℕ) :
    Integrable (fun ω => ratioDriftAt b E κ W r z ω / W) (growthPathLaw W b) := by
  obtain ⟨C, -, hC⟩ := exists_bound_drift (transportD0 b E) E hκ hz
  have hm : Measurable fun ω =>
      ratioDrift (transportD0 b E) E κ ((r : ℝ) / W) z (stateAt b E κ W r ω) / W :=
    ((continuous_ratioDrift_nu _ E hκ.1 hz _).measurable.comp
      (measurable_stateAt' b E κ r)).div_const _
  refine (Generator.integrable_of_ae_bound hm (c := C) (Eventually.of_forall fun ω => ?_)).congr ?_
  · rw [abs_div, Nat.abs_cast]
    rcases Nat.eq_zero_or_pos W with h | h
    · simp [h, (abs_nonneg _).trans (hC 0 (stateAt b E κ W r ω))]
    · exact (div_le_self (abs_nonneg _) (by exact_mod_cast h)).trans (hC _ _)
  · filter_upwards [ae_stateAt_eq hκ.2.1 hb hE1 hE2] with ω hω
    rw [ratioDriftAt, hω r]

/-- **The tested finite-`W` ratio identity.** -/
theorem abs_integral_ratio_drift_le {r₀ : ℕ} {ψ : GrowthPath W → ℝ}
    (hψ : Measurable[growthSigma W r₀] ψ) {B : ℝ} (hB : ∀ ω, |ψ ω| ≤ B) :
    ∀ r₁, r₀ ≤ r₁ →
    |∫ ω, ψ ω * (ratioAt b E κ W r₁ z ω - ratioAt b E κ W r₀ z ω -
        ∑ r ∈ Finset.Ico r₀ r₁, ratioDriftAt b E κ W r z ω / W) ∂growthPathLaw W b| ≤
      B * ∑ r ∈ Finset.Ico r₀ r₁, ∫ ω, |ratioDriftError b E κ W z r ω| ∂growthPathLaw W b := by
  set μ := growthPathLaw W b
  have hψm : Measurable ψ := hψ.mono (Generator.growthSigma_le W r₀) le_rfl
  have hP : ∀ r, Integrable (ratioAt b E κ W r z) μ := integrable_ratioAt hκ hb hE1 hE2 hz
  have hA : ∀ r, Integrable (fun ω => ratioDriftAt b E κ W r z ω / W) μ :=
    integrable_ratioDriftAt hκ hb hE1 hE2 hz
  have hψb : ∀ᵐ ω ∂μ, ‖ψ ω‖ ≤ B := Eventually.of_forall fun ω => by
    simpa [Real.norm_eq_abs] using hB ω
  intro r₁ h
  induction r₁, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hΔ : Integrable (fun ω => ratioAt b E κ W (n + 1) z ω - ratioAt b E κ W n z ω) μ :=
      (hP (n + 1)).sub (hP n)
    have hstep : ∫ ω, ψ ω * ((ratioAt b E κ W (n + 1) z ω - ratioAt b E κ W n z ω) -
          ratioDriftAt b E κ W n z ω / W) ∂μ =
        ∫ ω, ψ ω * ratioDriftError b E κ W z n ω ∂μ := by
      have hpull := Generator.integral_mul_condExp_eq (μ := μ) (Generator.growthSigma_le W n)
        (hψ.mono (Generator.growthSigma_mono hn) le_rfl) hB hΔ
      have h1 := hΔ.bdd_mul hψm.aestronglyMeasurable hψb
      have h2 := (hA n).bdd_mul hψm.aestronglyMeasurable hψb
      have h3 := (integrable_condExp (μ := μ) (m := growthSigma W n)
        (f := fun ω => ratioAt b E κ W (n + 1) z ω - ratioAt b E κ W n z ω)).bdd_mul
          hψm.aestronglyMeasurable hψb
      have e1 : (fun ω => ψ ω * ((ratioAt b E κ W (n + 1) z ω - ratioAt b E κ W n z ω) -
          ratioDriftAt b E κ W n z ω / W)) = fun ω =>
          ψ ω * (ratioAt b E κ W (n + 1) z ω - ratioAt b E κ W n z ω) -
            ψ ω * (ratioDriftAt b E κ W n z ω / W) := funext fun ω => mul_sub _ _ _
      have e2 : (fun ω => ψ ω * ratioDriftError b E κ W z n ω) = fun ω =>
          ψ ω * μ[fun ω => ratioAt b E κ W (n + 1) z ω - ratioAt b E κ W n z ω |
            growthSigma W n] ω - ψ ω * (ratioDriftAt b E κ W n z ω / W) :=
        funext fun ω => mul_sub _ _ _
      rw [e1, e2, integral_sub h1 h2, hpull, integral_sub h3 h2]
    have hsplit : ∫ ω, ψ ω * (ratioAt b E κ W (n + 1) z ω - ratioAt b E κ W r₀ z ω -
          ∑ r ∈ Finset.Ico r₀ (n + 1), ratioDriftAt b E κ W r z ω / W) ∂μ =
        ∫ ω, ψ ω * (ratioAt b E κ W n z ω - ratioAt b E κ W r₀ z ω -
          ∑ r ∈ Finset.Ico r₀ n, ratioDriftAt b E κ W r z ω / W) ∂μ +
        ∫ ω, ψ ω * ((ratioAt b E κ W (n + 1) z ω - ratioAt b E κ W n z ω) -
          ratioDriftAt b E κ W n z ω / W) ∂μ := by
      have hI1 : Integrable (fun ω => ratioAt b E κ W n z ω - ratioAt b E κ W r₀ z ω -
          ∑ r ∈ Finset.Ico r₀ n, ratioDriftAt b E κ W r z ω / W) μ :=
        ((hP n).sub (hP r₀)).sub (integrable_finsetSum _ fun r _ => hA r)
      have hI2 : Integrable (fun ω => (ratioAt b E κ W (n + 1) z ω - ratioAt b E κ W n z ω) -
          ratioDriftAt b E κ W n z ω / W) μ := hΔ.sub (hA n)
      rw [← integral_add (hI1.bdd_mul hψm.aestronglyMeasurable hψb)
        (hI2.bdd_mul hψm.aestronglyMeasurable hψb)]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [Finset.sum_Ico_succ_top hn]
      ring
    have herr : Integrable (ratioDriftError b E κ W z n) μ := integrable_condExp.sub (hA n)
    have hbd : |∫ ω, ψ ω * ratioDriftError b E κ W z n ω ∂μ| ≤
        B * ∫ ω, |ratioDriftError b E κ W z n ω| ∂μ := by
      refine (abs_integral_le_integral_abs).trans ?_
      rw [← integral_const_mul]
      refine integral_mono (herr.bdd_mul hψm.aestronglyMeasurable hψb).abs
        (herr.abs.const_mul B) fun ω => ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hB ω) (abs_nonneg _)
    rw [hsplit, hstep, Finset.sum_Ico_succ_top hn, mul_add]
    exact (abs_add_le _ _).trans (add_le_add ih hbd)

end Integrable

end BlockBand.Transmission.LawForced
