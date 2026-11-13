module

public import BlockBand.Transmission.Generator.Basic
public import BlockBand.Transmission.Generator.Coeff
public import BlockBand.Transmission.Bridge.Marginal
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# The finite-`W` drift identity tested against the past

For a bounded `𝓕_{r₀}`-measurable test `φ` and `r₀ ≤ r₁`:
`|E[φ(P_k(r₁) - P_k(r₀) - Σ_{r₀ ≤ r < r₁} A_k(P_r)/W)]| ≤ B Σ_{r₀ ≤ r < r₁} E|driftError_r|`
(`abs_integral_drift_le`). Only the tower property is used; `driftError` is
`E[Δ^k_r ∣ 𝓕_r] - A_k(P_r)/W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

variable {W : ℕ}

theorem growthSigma_mono {r r' : ℕ} (h : r ≤ r') : growthSigma W r ≤ growthSigma W r' := by
  have hp : Measurable[growthSigma W r'] (fun ω : GrowthPath W =>
      ((fun k : Fin r' => ω.1 k), (fun k : Fin (r' + 1) => ω.2 k))) := comap_measurable _
  have hf : Measurable (fun p : (Fin r' → Matrix (Fin W) (Fin W) ℂ) ×
      (Fin (r' + 1) → Matrix (Fin W) (Fin W) ℂ) =>
      ((fun k : Fin r => p.1 (Fin.castLE h k)),
        (fun k : Fin (r + 1) => p.2 (Fin.castLE (by omega) k)))) := by fun_prop
  exact (hf.comp hp).comap_le

/-- Pull-out for a bounded `m`-measurable factor. -/
theorem integral_mul_condExp_eq {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ m₀) {φ f : Ω → ℝ} (hφ : Measurable[m] φ) {B : ℝ}
    (hB : ∀ ω, |φ ω| ≤ B) (hf : Integrable f μ) :
    ∫ ω, φ ω * f ω ∂μ = ∫ ω, φ ω * μ[f | m] ω ∂μ := by
  rw [← integral_condExp hm (f := fun ω => φ ω * f ω)]
  refine integral_congr_ae ?_
  exact condExp_stronglyMeasurable_mul_of_bound hm hφ.stronglyMeasurable hf B
    (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hB ω)

/-- Bounded measurable functions are integrable under the path law. -/
theorem integrable_of_ae_bound {b : ℝ} {f : GrowthPath W → ℝ} (hf : Measurable f) {c : ℝ}
    (hc : ∀ᵐ ω ∂growthPathLaw W b, |f ω| ≤ c) : Integrable f (growthPathLaw W b) :=
  (memLp_top_of_bound hf.aestronglyMeasurable c
    (hc.mono fun ω h => by simpa [Real.norm_eq_abs] using h)).integrable le_top

theorem measurable_drift_pathPowers (b E E' : ℝ) (k r : ℕ) :
    Measurable[growthSigma W r] fun ω =>
      transmissionDrift (transportD0 b E) k (pathPowers b E' W r ω) / W := by
  have hc := continuous_transmissionDrift (transportD0 b E) k (v := fun x : ℕ → ℝ => x)
    (fun j => continuous_apply j)
  have hv : Measurable[growthSigma W r] (fun ω => pathPowers b E' W r ω) :=
    @Measurable.of_eval _ _ _ (growthSigma W r) _ _ fun j => measurable_pathPower_adapted b E' j r
  exact (measurable_id.div_const (W : ℝ)).comp (hc.measurable.comp hv)

/-- Almost-sure bounds at a bulk path energy. -/
theorem drift_pathPowers_bound {b E' : ℝ} (hb : b < 1) (hE1 : -2 < E') (hE2 : E' < 2)
    (D : ℝ) (hD : 0 ≤ D) (k r : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, |transmissionDrift D k (pathPowers b E' W r ω) / W| ≤
      D * k ^ 2 * (W : ℝ) ^ 2 := by
  filter_upwards [pathPower_mem (W := W) hb hE1 hE2] with ω hω
  have hb' : |transmissionDrift D k (pathPowers b E' W r ω)| ≤ D * k ^ 2 * (W : ℝ) ^ 2 :=
    abs_transmissionDrift_le hD k fun j hj _ => by
      obtain ⟨h0, h1, h2⟩ := hω j r hj
      show |pathPower b E' W j r ω| ≤ W
      rw [abs_of_nonneg h0]; exact h1.trans h2
  rcases Nat.eq_zero_or_pos W with h | h
  · simp [h]
  rw [abs_div, Nat.abs_cast]
  refine (div_le_self (abs_nonneg _) (by exact_mod_cast h)).trans hb'

theorem pathPower_bound {b E' : ℝ} (hb : b < 1) (hE1 : -2 < E') (hE2 : E' < 2) {k : ℕ}
    (hk : 1 ≤ k) (r : ℕ) : ∀ᵐ ω ∂growthPathLaw W b, |pathPower b E' W k r ω| ≤ W := by
  filter_upwards [pathPower_mem (W := W) hb hE1 hE2] with ω hω
  obtain ⟨h0, h1, h2⟩ := hω k r hk
  rw [abs_of_nonneg h0]; exact h1.trans h2

/-- **The tested finite-`W` drift identity.** -/
theorem abs_integral_drift_le {b E E' : ℝ} (hb : b < 1) (hE1 : -2 < E') (hE2 : E' < 2)
    (hD : 0 ≤ transportD0 b E) {k : ℕ} (hk : 1 ≤ k) {r₀ : ℕ} {φ : GrowthPath W → ℝ}
    (hφ : Measurable[growthSigma W r₀] φ) {B : ℝ} (hB : ∀ ω, |φ ω| ≤ B) :
    ∀ r₁, r₀ ≤ r₁ →
    |∫ ω, φ ω * (pathPower b E' W k r₁ ω - pathPower b E' W k r₀ ω -
        ∑ r ∈ Finset.Ico r₀ r₁, transmissionDrift (transportD0 b E) k (pathPowers b E' W r ω) / W)
        ∂growthPathLaw W b| ≤
      B * ∑ r ∈ Finset.Ico r₀ r₁, ∫ ω, |driftError b E E' W k r ω| ∂growthPathLaw W b := by
  set μ := growthPathLaw W b
  have hφm : Measurable φ := hφ.mono (growthSigma_le W r₀) le_rfl
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary _))
  have hP : ∀ r, Integrable (pathPower b E' W k r) μ := fun r =>
    integrable_of_ae_bound (measurable_pathPower b E' k r) (pathPower_bound hb hE1 hE2 hk r)
  have hA : ∀ r, Integrable (fun ω =>
      transmissionDrift (transportD0 b E) k (pathPowers b E' W r ω) / W) μ := fun r =>
    integrable_of_ae_bound ((measurable_drift_pathPowers b E E' k r).mono (growthSigma_le W r)
      le_rfl) (drift_pathPowers_bound hb hE1 hE2 _ hD k r)
  have hφb : ∀ᵐ ω ∂μ, ‖φ ω‖ ≤ B := Eventually.of_forall fun ω => by
    simpa [Real.norm_eq_abs] using hB ω
  intro r₁ h
  induction r₁, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hΔ : Integrable (powerIncrement b E' W k n) μ := (hP (n + 1)).sub (hP n)
    have hstep : ∫ ω, φ ω * (powerIncrement b E' W k n ω -
          transmissionDrift (transportD0 b E) k (pathPowers b E' W n ω) / W) ∂μ =
        ∫ ω, φ ω * driftError b E E' W k n ω ∂μ := by
      have hpull := integral_mul_condExp_eq (μ := μ) (growthSigma_le W n)
        (hφ.mono (growthSigma_mono hn) le_rfl) hB hΔ
      have h1 : Integrable (fun ω => φ ω * powerIncrement b E' W k n ω) μ :=
        hΔ.bdd_mul hφm.aestronglyMeasurable hφb
      have h2 : Integrable (fun ω => φ ω *
          transmissionDrift (transportD0 b E) k (pathPowers b E' W n ω) / W) μ := by
        simpa [mul_div_assoc] using (hA n).bdd_mul hφm.aestronglyMeasurable hφb
      have h3 : Integrable (fun ω => φ ω * μ[powerIncrement b E' W k n | growthSigma W n] ω) μ :=
        integrable_condExp.bdd_mul hφm.aestronglyMeasurable hφb
      simp only [driftError, Pi.sub_apply, mul_sub]
      rw [integral_sub h1 (by simpa [mul_div_assoc] using h2), hpull,
        integral_sub h3 (by simpa [mul_div_assoc] using h2)]
    have hsplit : ∫ ω, φ ω * (pathPower b E' W k (n + 1) ω - pathPower b E' W k r₀ ω -
          ∑ r ∈ Finset.Ico r₀ (n + 1),
            transmissionDrift (transportD0 b E) k (pathPowers b E' W r ω) / W) ∂μ =
        ∫ ω, φ ω * (pathPower b E' W k n ω - pathPower b E' W k r₀ ω -
          ∑ r ∈ Finset.Ico r₀ n,
            transmissionDrift (transportD0 b E) k (pathPowers b E' W r ω) / W) ∂μ +
        ∫ ω, φ ω * (powerIncrement b E' W k n ω -
          transmissionDrift (transportD0 b E) k (pathPowers b E' W n ω) / W) ∂μ := by
      have hI1 : Integrable (fun ω => pathPower b E' W k n ω - pathPower b E' W k r₀ ω -
          ∑ r ∈ Finset.Ico r₀ n,
            transmissionDrift (transportD0 b E) k (pathPowers b E' W r ω) / W) μ :=
        ((hP n).sub (hP r₀)).sub (integrable_finsetSum _ fun r _ => hA r)
      have hI2 : Integrable (fun ω => powerIncrement b E' W k n ω -
          transmissionDrift (transportD0 b E) k (pathPowers b E' W n ω) / W) μ :=
        ((hP (n + 1)).sub (hP n)).sub (hA n)
      rw [← integral_add (hI1.bdd_mul hφm.aestronglyMeasurable hφb)
        (hI2.bdd_mul hφm.aestronglyMeasurable hφb)]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [powerIncrement, Finset.sum_Ico_succ_top hn]
      ring
    have herr : Integrable (driftError b E E' W k n) μ := integrable_condExp.sub (hA n)
    have hbd : |∫ ω, φ ω * driftError b E E' W k n ω ∂μ| ≤
        B * ∫ ω, |driftError b E E' W k n ω| ∂μ := by
      refine (abs_integral_le_integral_abs).trans ?_
      rw [← integral_const_mul]
      refine integral_mono (herr.bdd_mul hφm.aestronglyMeasurable hφb).abs
        (herr.abs.const_mul B) fun ω => ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hB ω) (abs_nonneg _)
    rw [hsplit, hstep, Finset.sum_Ico_succ_top hn, mul_add]
    exact (abs_add_le _ _).trans (add_le_add ih hbd)

/-- `u ↦ c ⌊Wu⌋₊` is interval integrable (finitely many values on a bounded interval). -/
theorem intervalIntegrable_floor_comp (c : ℕ → ℝ) (x y : ℝ) :
    IntervalIntegrable (fun u => c ⌊(W : ℝ) * u⌋₊) MeasureTheory.volume x y := by
  have hWr : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  set N := ⌊(W : ℝ) * max x y⌋₊
  refine (intervalIntegrable_iff).mpr (Measure.integrableOn_of_bounded (M :=
    ∑ r ∈ Finset.range (N + 1), |c r|) (by simp) ?_ ?_)
  · exact ((measurable_from_nat (f := c)).comp
      (Nat.measurable_floor.comp (measurable_const.mul measurable_id))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun u hu => ?_)
    have hu' : u ≤ max x y := hu.2.trans (by simp)
    have hle : ⌊(W : ℝ) * u⌋₊ ≤ N := Nat.floor_mono (mul_le_mul_of_nonneg_left hu' hWr)
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun r => |c r|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))

/-- The piecewise-constant Riemann identity `Σ_{a ≤ r < b} c_r/W = ∫_{a/W}^{b/W} c_{⌊Wu⌋} du`. -/
theorem sum_div_eq_integral (hW : 0 < W) (c : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ r ∈ Finset.Ico a b, c r / W =
      ∫ u in (a : ℝ) / W..(b : ℝ) / W, c ⌊(W : ℝ) * u⌋₊ := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hone : ∀ r : ℕ, ∫ u in (r : ℝ) / W..((r + 1 : ℕ) : ℝ) / W, c ⌊(W : ℝ) * u⌋₊ = c r / W := by
    intro r
    have hle : (r : ℝ) / W ≤ ((r + 1 : ℕ) : ℝ) / W := by
      gcongr; exact_mod_cast Nat.le_succ r
    rw [intervalIntegral.integral_of_le hle]
    have : ∀ u ∈ Set.Ioo ((r : ℝ) / W) (((r + 1 : ℕ) : ℝ) / W), c ⌊(W : ℝ) * u⌋₊ = c r := by
      intro u hu
      congr 1
      rw [Nat.floor_eq_iff (by nlinarith [hu.1, (by positivity : (0 : ℝ) ≤ (r : ℝ) / W)])]
      obtain ⟨h1, h2⟩ := hu
      rw [div_lt_iff₀ hWr] at h1; rw [lt_div_iff₀ hWr] at h2
      push_cast at h2
      constructor <;> nlinarith
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.setIntegral_congr_fun
      measurableSet_Ioo this, MeasureTheory.setIntegral_const, Measure.real, Real.volume_Ioo]
    rw [ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    push_cast; field_simp; ring
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih, ← hone n,
      intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_floor_comp c _ _)
        (intervalIntegrable_floor_comp c _ _)]

end BlockBand.Transmission.Generator
