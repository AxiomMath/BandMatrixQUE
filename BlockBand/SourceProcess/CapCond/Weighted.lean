module

public import BlockBand.SourceProcess.CapCond.Limit

/-!
# Weighted cap tests: the cap event against a continuous weight of the entrance

For a continuous weight `w : FiniteMeasure [0,1] → ℝ` with `0 ≤ w ≤ B`, the weighted test
`wTest a c K w v = capTest a c K v · w (v 0)` is bounded continuous. With `t_K = seqExtract · K`,
on trace measures of transmission sequences
`1{t_K < a} w ≤ wTest a c K w ≤ 1{t_K < c} w` (`wTest_bounds`). These bounds give the one-sided
comparisons (finite width against `physCapEvent`, limit against `capSet`) used for
`tendsto_capWeighted`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapCond

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.ClosedIdent BlockBand.SourceProcess.ClosedPath
open scoped ENNReal

/-- The weighted cap test `v ↦ capTest a c K v · w (v 0)`. -/
def wTest (a c : ℝ) (ha : 0 < a) (K : ℕ) (w : BoundedContinuousFunction (FiniteMeasure unitInterval) ℝ) :
    BoundedContinuousFunction (Fin 1 → FiniteMeasure unitInterval) ℝ :=
  capTest a c ha K * w.compContinuous ⟨fun v => v 0, continuous_apply 0⟩

theorem wTest_apply (a c : ℝ) (ha : 0 < a) (K : ℕ)
    (w : BoundedContinuousFunction (FiniteMeasure unitInterval) ℝ)
    (v : Fin 1 → FiniteMeasure unitInterval) : wTest a c ha K w v = capTest a c ha K v * w (v 0) :=
  rfl

variable {w : BoundedContinuousFunction (FiniteMeasure unitInterval) ℝ}

/-- Lower and upper pointwise bounds on trace measures. -/
theorem wTest_bounds (hw : ∀ ν, 0 ≤ w ν) {a c : ℝ} (ha : 0 < a) (hac : a < c) (K : ℕ)
    {v : Fin 1 → FiniteMeasure unitInterval} {t : ℕ → ℝ}
    (hν : (v 0 : Measure unitInterval) = seqTraceMeasure t) (ht : IsTransmissionSequence t) :
    (t K < a → w (v 0) ≤ wTest a c ha K w v) ∧ (wTest a c ha K w v ≤ if t K < c then w (v 0) else 0) := by
  rw [wTest_apply]
  refine ⟨fun hK => by rw [capTest_eq_one ha hac hν ht hK, one_mul], ?_⟩
  rcases (capTest_nonneg a c ha K v).lt_or_eq with hpos | hz
  · rw [ite_eq_left (lt_of_capTest_pos ha hac hν ht hpos)]
    exact mul_le_of_le_one_left (hw _) (capTest_le_one _ _ _ _ _)
  · rw [← hz, zero_mul]
    split_ifs
    · exact hw _
    · exact le_rfl

end BlockBand.SourceProcess.CapCond
