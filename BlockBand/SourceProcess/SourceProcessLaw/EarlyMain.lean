module

public import BlockBand.SourceProcess.SourceProcessLaw.EarlyHolds
public import BlockBand.SourceProcess.FullSource.DeltaHolds

/-!
# Sources before `s`

`earlySources_of_moments`: `EarlySources` follows from the full tag clock moments: truncating a test
on `[0,T]` to `[s,T]` changes the source transform by `O(s)` for large `W`. `earlySources_holds`
derives it from the Gaussian layer and scalar recursion hypotheses.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourceProcessLaw

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs

theorem integral_early_le {b E T s Q C : ℝ} {W : ℕ} (hW : 0 < W) (hs : 0 ≤ s) (hQ0 : 0 ≤ Q)
    (hC : 0 ≤ C) {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x) (hQ : ∀ x ∈ Set.Icc 0 T, q x ≤ Q)
    (htag : ∀ k ∈ Finset.range ⌊(W : ℝ) * T⌋₊,
      Integrable (fun ω => (tagResponse b E W ⌊(W : ℝ) * T⌋₊ k ω).trace.re) (growthPathLaw W b) ∧
      ∫ ω, (tagResponse b E W ⌊(W : ℝ) * T⌋₊ k ω).trace.re ∂growthPathLaw W b ≤ C * W) :
    Integrable (fun ω => ∑ k ∈ Finset.range ⌊(W : ℝ) * T⌋₊,
        earlyWeight W s T q k * (tagResponse b E W ⌊(W : ℝ) * T⌋₊ k ω).trace.re)
        (growthPathLaw W b) ∧
      ∫ ω, ∑ k ∈ Finset.range ⌊(W : ℝ) * T⌋₊,
        earlyWeight W s T q k * (tagResponse b E W ⌊(W : ℝ) * T⌋₊ k ω).trace.re
          ∂growthPathLaw W b ≤ C * (s * Q) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  refine ⟨integrable_finsetSum _ fun k hk => (htag k hk).1.const_mul _, ?_⟩
  rw [integral_finsetSum _ fun k hk => (htag k hk).1.const_mul _]
  calc ∑ k ∈ Finset.range ⌊(W : ℝ) * T⌋₊, ∫ ω, earlyWeight W s T q k *
        (tagResponse b E W ⌊(W : ℝ) * T⌋₊ k ω).trace.re ∂growthPathLaw W b
      ≤ ∑ k ∈ Finset.range ⌊(W : ℝ) * T⌋₊, earlyWeight W s T q k * (C * W) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (htag k hk).2 (earlyWeight_nonneg hq0 k)
    _ = (∑ k ∈ Finset.range ⌊(W : ℝ) * T⌋₊, earlyWeight W s T q k) * (C * W) :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ (s * Q / W) * (C * W) :=
        mul_le_mul_of_nonneg_right (sum_earlyWeight_le hW hs hQ0 hq0 hQ) (by positivity)
    _ = C * (s * Q) := by field_simp

/-- **`EarlySources`** from the full tag clock moments (`FullSourceMomentsContract.tag`). -/
theorem earlySources_of_moments (hM : FullSourceMomentsContract) : EarlySources := by
  intro b hb0 hb E hE1 hE2 T hT p q hq J a ha
  obtain ⟨C₀, W₀, hC₀⟩ := hM.tag b hb0 hb E hE1 hE2 T 1 le_rfl
  have hbd : ∀ i, ∃ Q : ℝ, ∀ x ∈ Set.Icc 0 T, q i x ≤ Q := fun i => by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hq i).2.2
    exact ⟨C, fun x hx => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC x hx)⟩
  choose Q hQ using hbd
  set C' := max C₀ 0
  refine ⟨C' * ∑ j, ∑ i, a j i * max (Q i) 0, fun s hs hsT => ?_⟩
  filter_upwards [eventually_ge_atTop (max W₀ 1)] with W hW
  have hW0 : 0 < W := lt_of_lt_of_le zero_lt_one (le_of_max_le_right hW)
  have hWW₀ : W₀ ≤ W := le_of_max_le_left hW
  have hq0 : ∀ i x, 0 ≤ q i x := fun i => (hq i).1
  have hnT : ((⌊(W : ℝ) * T⌋₊ : ℕ) : ℝ) ≤ T * W := by
    rw [mul_comm]; exact Nat.floor_le (by positivity)
  have htag : ∀ k ∈ Finset.range ⌊(W : ℝ) * T⌋₊,
      Integrable (fun ω => (tagResponse b E W ⌊(W : ℝ) * T⌋₊ k ω).trace.re) (growthPathLaw W b) ∧
      ∫ ω, (tagResponse b E W ⌊(W : ℝ) * T⌋₊ k ω).trace.re ∂growthPathLaw W b ≤ C' * W :=
    fun k hk => tag_mean_le hW0 (le_max_right _ _)
      ((hC₀ W hWW₀ _ hnT k (Finset.mem_range.1 hk)).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hi := fun i => integral_early_le (b := b) (E := E) hW0 hs.le (le_max_right (Q i) 0)
    (le_max_right C₀ 0) (hq0 i) (fun x hx => (hQ i x hx).trans (le_max_left _ _)) htag
  set n := ⌊(W : ℝ) * T⌋₊
  have hqs : ∀ i x, 0 ≤ Set.indicator (Set.Icc s T) (q i) x :=
    fun i x => Set.indicator_nonneg (fun y _ => hq0 i y) x
  have hF := integrable_srcIntegrand (W := W) b E n hq0 ha
  have hG := integrable_srcIntegrand (W := W) b E n hqs ha
  have hbi : Integrable (fun ω => ∑ j, ∑ i, a j i * ∑ k ∈ Finset.range n,
      earlyWeight W s T (q i) k * (tagResponse b E W n k ω).trace.re) (growthPathLaw W b) :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => (hi i).1.const_mul _
  change |∫ ω, srcIntegrand b E W n q a ω ∂growthPathLaw W b -
    ∫ ω, srcIntegrand b E W n (fun i => Set.indicator (Set.Icc s T) (q i)) a ω
      ∂growthPathLaw W b| ≤ _
  rw [← integral_sub hF hG]
  calc |∫ ω, (srcIntegrand b E W n q a ω -
        srcIntegrand b E W n (fun i => Set.indicator (Set.Icc s T) (q i)) a ω) ∂growthPathLaw W b|
      ≤ ∫ ω, |srcIntegrand b E W n q a ω -
        srcIntegrand b E W n (fun i => Set.indicator (Set.Icc s T) (q i)) a ω|
          ∂growthPathLaw W b := abs_integral_le_integral_abs
    _ ≤ ∫ ω, ∑ j, ∑ i, a j i * ∑ k ∈ Finset.range n,
          earlyWeight W s T (q i) k * (tagResponse b E W n k ω).trace.re ∂growthPathLaw W b :=
        integral_mono (hF.sub hG).abs hbi fun ω => abs_integrand_sub_le b E n s T hq0 ha ω
    _ = ∑ j, ∑ i, a j i * ∫ ω, ∑ k ∈ Finset.range n,
          earlyWeight W s T (q i) k * (tagResponse b E W n k ω).trace.re ∂growthPathLaw W b := by
        rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ =>
          (hi i).1.const_mul _]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_finsetSum _ fun i _ => (hi i).1.const_mul _]
        exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    _ ≤ ∑ j, ∑ i, a j i * (C' * (s * max (Q i) 0)) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hi i).2 (ha j i)
    _ = C' * (∑ j, ∑ i, a j i * max (Q i) 0) * s := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- **`EarlySources` from the input hypotheses** (via `FullSource.fullSourceMoments_holds`). -/
theorem earlySources_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) : EarlySources :=
  earlySources_of_moments (FullSource.fullSourceMoments_holds hGA hLp hSR)

end BlockBand.SourceProcess.SourceProcessLaw
