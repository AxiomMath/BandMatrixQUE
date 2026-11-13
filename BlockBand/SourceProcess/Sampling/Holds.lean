module

public import BlockBand.SourceProcess.Sampling.Bound
public import BlockBand.SourceProcess.SourcePins.Freq
public import BlockBand.SourceProcess.FullSource.DeltaHolds

/-!
# Positive-source sampling (`PhysicalSampling`, hence `PhysicalSamplingWeak`)

* `physicalSampling_of_moments (hFM : FullSourceMomentsContract) : PhysicalSampling` (error
  `C/M`): with `‖W⁻¹Tr Y_{n;k}‖_2 ≤ C₀` (field `tag` at `p = 2`, `k < n = ⌊WT⌋`, `W ≥ W₀`) and
  `m_i ≤ T Q_i` (`Q_i = max q_i`), `integral_condErr_le` gives
  `|S - S_M| ≤ Σ_i 4M₄ (Σ_j a_{ji})² (T Q_i)² C₀² / M`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Sampling

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.RawTag

theorem gridMass_le {W n : ℕ} (hW : 0 < W) {q : ℝ → ℝ} {Q T : ℝ} (hQ0 : 0 ≤ Q)
    (hQ : ∀ x, q x ≤ Q) (hn : (n : ℝ) ≤ T * W) : gridMass W n q ≤ T * Q := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  calc gridMass W n q ≤ ∑ _k ∈ Finset.range n, Q / W :=
        Finset.sum_le_sum fun k _ => div_le_div_of_nonneg_right (hQ _) hWr.le
    _ = n * Q / W := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_assoc]
    _ ≤ T * W * Q / W := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hn hQ0) hWr.le
    _ = T * Q := by field_simp

/-- **Positive-source sampling** (`PhysicalSampling`, error `C/M`) from the full tag clock
moments at `p = 2`. -/
theorem physicalSampling_of_moments (hFM : FullSourceMomentsContract) : PhysicalSampling := by
  intro b hb0 hb E hE1 hE2 s T hs hsT p q hq J a ha
  obtain ⟨C₀, W₀, hC₀⟩ := hFM.tag b hb0 hb E hE1 hE2 T 2 one_le_two
  have hbd : ∀ i, ∃ Q : ℝ, 0 ≤ Q ∧ ∀ x, q i x ≤ Q := fun i => by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hq i).2.2
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    by_cases hx : x ∈ Set.Icc s T
    · have h1 : |q i x| ≤ C := by simpa [Real.norm_eq_abs] using hC x hx
      exact (le_abs_self _).trans (h1.trans (le_max_left _ _))
    · rw [(hq i).2.1 x hx]; exact le_max_right _ _
  choose Q hQ0 hQ using hbd
  have hq0 : ∀ i x, 0 ≤ q i x := fun i => (hq i).1
  set C := max C₀ 0
  refine ⟨∑ i, 4 * gaussMoment 4 * (∑ j, a j i) ^ 2 * (T * Q i) ^ 2 * C ^ 2, fun M hM => ?_⟩
  filter_upwards [eventually_ge_atTop (max W₀ 1)] with W hW
  have hW0 : 0 < W := lt_of_lt_of_le zero_lt_one (le_of_max_le_right hW)
  have hWW₀ : W₀ ≤ W := le_of_max_le_left hW
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hT : 0 < T := hs.trans hsT
  have hnT : ((⌊(W : ℝ) * T⌋₊ : ℕ) : ℝ) ≤ T * W := by
    rw [mul_comm]; exact Nat.floor_le (by positivity)
  have htag : ∀ k ∈ Finset.range ⌊(W : ℝ) * T⌋₊, Integrable (fun ω =>
      ((tagResponse b E W ⌊(W : ℝ) * T⌋₊ k ω).trace.re / W) ^ 2) (growthPathLaw W b) ∧
      ∫ ω, ((tagResponse b E W ⌊(W : ℝ) * T⌋₊ k ω).trace.re / W) ^ 2 ∂growthPathLaw W b ≤
        C ^ 2 := fun k hk =>
    tag_sq_le (le_max_right _ _) ((hC₀ W hWW₀ _ hnT k (Finset.mem_range.1 hk)).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  refine (abs_sub_le_integral_condErr b E T hq0 ha hW0 hM fun k hk => (htag k hk).1).trans
    ((integral_condErr_le hq0 a hM htag).trans ?_)
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  have hm0 := gridMass_nonneg W ⌊(W : ℝ) * T⌋₊ (hq0 i)
  have hm := gridMass_le hW0 (hQ0 i) (hQ i) hnT
  have hc : 0 ≤ 4 * gaussMoment 4 * (∑ j, a j i) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (gaussMoment_nonneg _)) (sq_nonneg _)
  refine div_le_div_of_nonneg_right ?_ hMr.le
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hc) (sq_nonneg _)
  exact pow_le_pow_left₀ hm0 hm 2

/-- **`PhysicalSampling` from the input hypotheses.** -/
theorem physicalSampling_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) : PhysicalSampling :=
  physicalSampling_of_moments (FullSource.fullSourceMoments_holds hGA hLp hSR)

/-- **`PhysicalSamplingWeak`** from `GaussianAbsorptionContract`, `GaussianLpGradient` and
`ScalarRecursionContract`. -/
theorem physicalSamplingWeak_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) : SourcePins.PhysicalSamplingWeak :=
  SourcePins.physicalSamplingWeak_of (physicalSampling_holds hGA hLp hSR)

end BlockBand.SourceProcess.Sampling
