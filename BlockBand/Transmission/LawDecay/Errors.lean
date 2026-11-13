module

public import BlockBand.Transmission.LawDecay.StepPath
public import BlockBand.Transmission.Generator.PowSum
public import BlockBand.Transmission.Generator.BrSum
public import BlockBand.Transmission.EnergyUniform.Window

/-!
# The summed one-step errors vanish

Along a moving energy `e` and on the window `W ≤ r < ⌊Wt⌋` (`lengthWindow 1 t W`), `t > 1`:
* **`stepErr_sum_tendsto`**: `Σ_r err_r → 0`, from `powerDriftSummable_holds` (`k = 1, 2`,
  `L²`) and `powerBracketSummable_holds` (`(1,1), (1,2)`, `L¹`), using `E|f| ≤ ‖f‖₁ ≤ ‖f‖₂`.

The cubic terms are handled in the sibling module, **`stepCubic_sum_tendsto`**:
`Σ_r E(|Δ¹|³ + (Δ¹)²|Δ²|) → 0`, from `fourth_increment_bound` (`E(Δ^k_r)⁴ ≤ K/W²`), the pointwise
`|x|³ ≤ √W x⁴ + W^{-3/2}` and `a²b ≤ 2a³ + b³`: each term is `≤ (2K₁ + K₂ + 3)W^{-3/2}`, at most
`tW` terms.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDecay

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Generator
open scoped ENNReal

theorem ofReal_integral_abs_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (f : Ω → ℝ) :
    ENNReal.ofReal (∫ ω, |f ω| ∂μ) ≤ eLpNorm f 1 μ := by
  refine le_trans ?_ lintegral_enorm_le_eLpNorm_one
  by_cases hf : Integrable (fun ω => |f ω|) μ
  · rw [ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall fun ω => abs_nonneg _)]
    refine le_of_eq (lintegral_congr fun ω => ?_)
    rw [Real.enorm_eq_ofReal_abs]
  · rw [integral_undef hf]; simp

theorem ofReal_add4 {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ENNReal.ofReal (a + b + c + d) =
      ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c + ENNReal.ofReal d := by
  rw [ENNReal.ofReal_add (by positivity) hd, ENNReal.ofReal_add (by positivity) hc,
    ENNReal.ofReal_add ha hb]

/-- A nonnegative real sequence dominated (through `ofReal`) by a null sequence is null. -/
theorem tendsto_of_ofReal_le {a : ℕ → ℝ} {B : ℕ → ℝ≥0∞} (ha : ∀ W, 0 ≤ a W)
    (hB : Tendsto B atTop (𝓝 0)) (h : ∀ W, ENNReal.ofReal (a W) ≤ B W) :
    Tendsto a atTop (𝓝 0) := by
  have h1 : Tendsto (fun W => ENNReal.ofReal (a W)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB (fun _ => bot_le) h
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
  simp only [ENNReal.toReal_zero] at h2
  exact h2.congr fun W => by simp [Function.comp, ENNReal.toReal_ofReal (ha W)]

theorem stepErr_nonneg (b E E' : ℝ) (W r : ℕ) : 0 ≤ stepErr b E E' W r := by
  unfold stepErr
  have := fun f : GrowthPath W → ℝ => integral_nonneg (μ := growthPathLaw W b)
    (fun ω => abs_nonneg (f ω))
  linarith [this (driftError b E E' W 1 r), this (driftError b E E' W 2 r),
    this (bracketError b E E' W 1 1 r), this (bracketError b E E' W 1 2 r)]

/-- **The summed drift and bracket errors vanish.** -/
theorem stepErr_sum_tendsto (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e) {t : ℝ}
    (ht : 1 < t) :
    Tendsto (fun W : ℕ => ∑ r ∈ lengthWindow 1 t W, stepErr b E (e W) W r) atTop (𝓝 0) := by
  have hD := powerDriftSummable_holds hMT hGA hLp hP b hb0 hb E h1 h2 Ce e he
  have hB := powerBracketSummable_holds hMT hGA hLp hP b hb0 hb E h1 h2 Ce e he
  have d1 := hD 1 le_rfl 1 t one_pos ht
  have d2 := hD 2 (by norm_num) 1 t one_pos ht
  have b11 := hB 1 1 le_rfl le_rfl 1 t one_pos ht
  have b12 := hB 1 2 le_rfl (by norm_num) 1 t one_pos ht
  have hsum := ((d1.add d2).add b11).add b12
  simp only [add_zero] at hsum
  refine tendsto_of_ofReal_le (fun W => Finset.sum_nonneg fun r _ => stepErr_nonneg _ _ _ _ _)
    hsum fun W => ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun r _ => stepErr_nonneg _ _ _ _ _), ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun r _ => ?_
  set μ := growthPathLaw W b
  have i : ∀ f : GrowthPath W → ℝ, 0 ≤ ∫ ω, |f ω| ∂μ := fun f =>
    integral_nonneg fun ω => abs_nonneg _
  have l2 : ∀ f : GrowthPath W → ℝ, ENNReal.ofReal (∫ ω, |f ω| ∂μ) ≤ eLpNorm f 2 μ := fun f =>
    (ofReal_integral_abs_le f).trans (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))
  unfold stepErr
  rw [ofReal_add4 (i _) (i _) (i _) (i _)]
  gcongr
  · exact l2 _
  · exact l2 _
  · exact ofReal_integral_abs_le _
  · exact ofReal_integral_abs_le _

end BlockBand.Transmission.LawDecay
