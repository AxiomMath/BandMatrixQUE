module

public import BlockBand.Transmission.Generator.LimitAux

/-!
# Steps of the limit drift martingale problem

* `abs_integral_le_of_sq`: `|∫f| ≤ 1 + K` from `∫⁻|f|² ≤ K` (probability).
* `boundary_le`: `|(∫_s^t c_{⌊Wu⌋}) - ∫_{⌊Ws⌋/W}^{⌊Wt⌋/W} c_{⌊Wu⌋}| ≤ (|c_{⌊Ws⌋}| + |c_{⌊Wt⌋}|)/W`.
* `errSum_tendsto`: `PowerDriftSummable` along the subsequence, as `Σ_r E|driftError_r| → 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal

theorem abs_integral_le_of_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal K) : |∫ x, f x ∂μ| ≤ 1 + K := by
  have h1 : ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ ≤ ENNReal.ofReal (1 + K) := by
    calc ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ ≤ ∫⁻ x, (1 + ‖f x‖ₑ ^ 2) ∂μ := by
          refine lintegral_mono fun x => ?_
          rw [ofReal_norm]; exact enorm_le_one_add_sq _
      _ = 1 + ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (1 + K) := by
          rw [ENNReal.ofReal_add zero_le_one hK, ENNReal.ofReal_one]; gcongr
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm f).trans ?_
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h1

/-- The two boundary cells of a piecewise-constant integral. -/
theorem boundary_le {W : ℕ} (hW : 0 < W) (c : ℕ → ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    |(∫ u in s..t, c ⌊(W : ℝ) * u⌋₊) -
      ∫ u in (⌊(W : ℝ) * s⌋₊ : ℝ) / W..(⌊(W : ℝ) * t⌋₊ : ℝ) / W, c ⌊(W : ℝ) * u⌋₊| ≤
      (|c ⌊(W : ℝ) * s⌋₊| + |c ⌊(W : ℝ) * t⌋₊|) / W := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hcell : ∀ x : ℝ, 0 ≤ x → ∫ u in (⌊(W : ℝ) * x⌋₊ : ℝ) / W..x, c ⌊(W : ℝ) * u⌋₊ =
      (x - (⌊(W : ℝ) * x⌋₊ : ℝ) / W) * c ⌊(W : ℝ) * x⌋₊ := by
    intro x hx
    have hle : (⌊(W : ℝ) * x⌋₊ : ℝ) / W ≤ x := by
      rw [div_le_iff₀ hWr, mul_comm]; exact Nat.floor_le (by positivity)
    rw [intervalIntegral.integral_congr (g := fun _ => c ⌊(W : ℝ) * x⌋₊), intervalIntegral.integral_const,
      smul_eq_mul]
    intro u hu
    rw [Set.uIcc_of_le hle] at hu
    simp only
    congr 1
    refine (Nat.floor_eq_iff (by nlinarith [hu.1, (by positivity : (0:ℝ) ≤ (⌊(W:ℝ) * x⌋₊ : ℝ) / W)])).mpr ⟨?_, ?_⟩
    · have := hu.1; rw [div_le_iff₀ hWr] at this; linarith
    · have := Nat.lt_floor_add_one ((W : ℝ) * x); nlinarith [hu.2]
  have hI := intervalIntegrable_floor_comp (W := W) c
  have e1 := intervalIntegral.integral_add_adjacent_intervals
    (hI ((⌊(W : ℝ) * s⌋₊ : ℝ) / W) s) (hI s ((⌊(W : ℝ) * t⌋₊ : ℝ) / W))
  have e2 := intervalIntegral.integral_add_adjacent_intervals
    (hI s t) (hI t ((⌊(W : ℝ) * t⌋₊ : ℝ) / W))
  have e3 : ∫ u in t..(⌊(W : ℝ) * t⌋₊ : ℝ) / W, c ⌊(W : ℝ) * u⌋₊ =
      -((t - (⌊(W : ℝ) * t⌋₊ : ℝ) / W) * c ⌊(W : ℝ) * t⌋₊) := by
    rw [intervalIntegral.integral_symm, hcell t (hs.trans hst)]
  rw [← e1, ← e2, e3, hcell s hs]
  have hgap : ∀ x : ℝ, 0 ≤ x → 0 ≤ x - (⌊(W : ℝ) * x⌋₊ : ℝ) / W ∧
      x - (⌊(W : ℝ) * x⌋₊ : ℝ) / W ≤ 1 / W := by
    intro x hx
    constructor
    · rw [sub_nonneg, div_le_iff₀ hWr, mul_comm]; exact Nat.floor_le (by positivity)
    · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hWr]
      have := Nat.lt_floor_add_one ((W : ℝ) * x); nlinarith
  obtain ⟨a1, a2⟩ := hgap s hs
  obtain ⟨b1, b2⟩ := hgap t (hs.trans hst)
  set A := c ⌊(W : ℝ) * s⌋₊
  set B := c ⌊(W : ℝ) * t⌋₊
  calc _ = |-((s - (⌊(W : ℝ) * s⌋₊ : ℝ) / W) * A) + (t - (⌊(W : ℝ) * t⌋₊ : ℝ) / W) * B| := by
        congr 1; ring
    _ ≤ |(s - (⌊(W : ℝ) * s⌋₊ : ℝ) / W) * A| + |(t - (⌊(W : ℝ) * t⌋₊ : ℝ) / W) * B| := by
        have := abs_add_le (-((s - (⌊(W : ℝ) * s⌋₊ : ℝ) / W) * A)) ((t - (⌊(W : ℝ) * t⌋₊ : ℝ) / W) * B)
        rwa [abs_neg] at this
    _ ≤ 1 / W * |A| + 1 / W * |B| := by
        rw [abs_mul, abs_mul, abs_of_nonneg a1, abs_of_nonneg b1]
        gcongr
    _ = (|A| + |B|) / W := by ring

theorem ofReal_integral_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) : ENNReal.ofReal (∫ x, |f x| ∂μ) ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := by
  by_cases hi : Integrable f μ
  · rw [ofReal_integral_eq_lintegral_ofReal hi.abs (Eventually.of_forall fun _ => abs_nonneg _)]
    exact le_of_eq (lintegral_congr fun x => (Real.enorm_eq_ofReal_abs _).symm)
  · have : ¬ Integrable (fun x => |f x|) μ := fun h =>
      hi ((integrable_norm_iff hf).mp (by simpa [Real.norm_eq_abs] using h))
    rw [integral_undef this, ENNReal.ofReal_zero]; exact zero_le

theorem aestronglyMeasurable_driftError (b E E' : ℝ) (W k r : ℕ) :
    AEStronglyMeasurable (driftError b E E' W k r) (growthPathLaw W b) :=
  ((stronglyMeasurable_condExp.mono (growthSigma_le W r)).sub
    ((measurable_drift_pathPowers b E E' k r).mono (growthSigma_le W r)
      le_rfl).stronglyMeasurable).aestronglyMeasurable

/-- `PowerDriftSummable` along a subsequence, in `L¹` real form. -/
theorem errSum_tendsto (hD : PowerDriftSummable) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e)
    {k : ℕ} (hk : 1 ≤ k) {ε T : ℝ} (hε : 0 < ε) (hεT : ε < T) {σ : ℕ → ℕ}
    (hσ : Tendsto σ atTop atTop) :
    Tendsto (fun n => ∑ r ∈ lengthWindow ε T (σ n),
      ∫ ω, |driftError b E (e (σ n)) (σ n) k r ω| ∂growthPathLaw (σ n) b) atTop (𝓝 0) := by
  have h2 := (hD b hb0 hb E hE1 hE2 Ce e he k hk ε T hε hεT).comp hσ
  have hle : ∀ n, ENNReal.ofReal (∑ r ∈ lengthWindow ε T (σ n),
      ∫ ω, |driftError b E (e (σ n)) (σ n) k r ω| ∂growthPathLaw (σ n) b) ≤
      ∑ r ∈ lengthWindow ε T (σ n),
        eLpNorm (driftError b E (e (σ n)) (σ n) k r) 2 (growthPathLaw (σ n) b) := by
    intro n
    rw [ENNReal.ofReal_sum_of_nonneg fun r _ => integral_nonneg fun _ => abs_nonneg _]
    refine Finset.sum_le_sum fun r _ => ?_
    refine (ofReal_integral_abs_le
      (aestronglyMeasurable_driftError b E (e (σ n)) (σ n) k r)).trans ?_
    rw [← eLpNorm_one_eq_lintegral_enorm (aestronglyMeasurable_driftError b E (e (σ n)) (σ n) k r)]
    exact eLpNorm_le_eLpNorm_of_exponent_le one_le_two
  have h3 : Tendsto (fun n => ENNReal.ofReal (∑ r ∈ lengthWindow ε T (σ n),
      ∫ ω, |driftError b E (e (σ n)) (σ n) k r ω| ∂growthPathLaw (σ n) b)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => zero_le) hle
  have h4 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h3
  simp only [ENNReal.toReal_zero] at h4
  refine h4.congr fun n => ?_
  simp only [Function.comp_apply]
  exact ENNReal.toReal_ofReal (Finset.sum_nonneg fun r _ => integral_nonneg fun _ => abs_nonneg _)

end BlockBand.Transmission.Generator
