module

public import BlockBand.SourceProcess.ClosedSumProof.Pins
public import BlockBand.SourceProcess.ClosedReduce.Lindeberg

/-!
# `ClosedFourth` is `ClosedLindeberg`

`ClosedReduce.ClosedLindeberg` states the same clause as `ClosedFourth`, with the indicator outside
the power. The two summed errors are equal (`closedFourthErr_eq`), hence
**`closedFourth_iff_lindeberg`**; every result stated with `ClosedFourth` holds with
`ClosedLindeberg`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSumProof

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.ClosedReduce

variable {W p K M : ℕ}

theorem closedFourthErr_eq (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (e : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M)) :
    closedFourthErr b E s T h q R W Vs e = closedLindebergErr b E s T h q R W Vs e := by
  refine Finset.sum_congr rfl fun j _ => lintegral_congr fun y => ?_
  by_cases hy : y ∈ closedAlive (M := M) b E s T h q R W j Vs ∩ noBirth j
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, enorm_zero]
    exact zero_pow (by norm_num)

theorem closedFourth_iff_lindeberg : ClosedFourth ↔ ClosedLindeberg := by
  unfold ClosedFourth ClosedLindeberg
  simp only [closedFourthErr_eq]

end BlockBand.SourceProcess.ClosedSumProof
