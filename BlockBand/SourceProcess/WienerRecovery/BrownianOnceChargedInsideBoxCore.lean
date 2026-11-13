module

public import BlockBand.SourceProcess.WienerRecovery.BrownianOnceChargedCoordinateBox

/-!
# Inside-box compact cores for Brownian cylinders

This module supplies the finite-dimensional part of the corrected
once-charged compact-core input.  After a common coordinate box has been
chosen, each measurable cylinder base is intersected with its finite box.
Finite-dimensional inner regularity gives a compact core in that intersection.
The errors are chosen from one summable positive family, so the stagewise
losses fit the budget remaining after the global box charge.

Combining this construction with `BrownianOnceChargedCoordinateBox` constructs
`BrownianCylinderOnceChargedCompactCore`.  The argument uses neither a measure
on the infinite path product nor continuity at empty, and it does not invoke
the later continuity conclusion.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery.CEH
namespace BrownianOnceChargedInsideBoxCore

open scoped NNReal Topology ENNReal
open Filter Set MeasureTheory ProbabilityTheory
open ScalarWienerRealizationClosure
open ScalarWienerMeasureConstruction
open BrownianCylinderTightnessClosure
open BrownianNestedCompactCoreProof
open BrownianOnceChargedCoordinateBox

/-- Simultaneous compact inner approximation of measurable cylinder bases
after intersection with a prescribed compact coordinate box.

The positive errors are chosen first with total strictly below `η`.  At stage
`n`, inner regularity is applied to the measurable finite-dimensional set
`S n ∩ finiteCoordinateCompactBox q (I n)`.  Thus the resulting compact core
has exactly the compatibility and loss fields required by the once-charged
residual. -/
theorem exists_summable_insideBox_compactCores
    (I : ℕ → Finset NNReal) (S : ∀ n, Set (I n → ℝ))
    (hSmeas : ∀ n, MeasurableSet (S n))
    (q : NNReal → Set ℝ) (hqcompact : ∀ t, IsCompact (q t))
    {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∃ (C : ∀ n, Set (I n → ℝ)) (δ : ℕ → ℝ≥0∞),
      (∑' n, δ n) < η ∧
      (∀ n, C n ⊆ S n ∩ finiteCoordinateCompactBox q (I n)) ∧
      (∀ n, IsCompact (C n)) ∧
      (∀ n, BrownianReal.projectiveFamily (I n)
        ((S n ∩ finiteCoordinateCompactBox q (I n)) \ C n) ≤ δ n) := by
  obtain ⟨δ, hδpos, hδsum⟩ :=
    ENNReal.exists_pos_sum_of_countable' hη ℕ
  have hboxCompact :
      ∀ n, IsCompact (finiteCoordinateCompactBox q (I n)) := by
    intro n
    simpa [finiteCoordinateCompactBox, Set.pi] using
      (isCompact_pi_infinite fun i : I n => hqcompact i)
  have hcore : ∀ n, ∃ C : Set (I n → ℝ),
      C ⊆ S n ∩ finiteCoordinateCompactBox q (I n) ∧
      IsCompact C ∧
      BrownianReal.projectiveFamily (I n)
        ((S n ∩ finiteCoordinateCompactBox q (I n)) \ C) < δ n := by
    intro n
    obtain ⟨C, hCsub, hCcompact, hCclosed, hCloss⟩ :=
      exists_compact_brownianProjectiveFamily_core (I n)
        ((hSmeas n).inter (hboxCompact n).isClosed.measurableSet)
        (hδpos n).ne'
    exact ⟨C, hCsub, hCcompact, hCloss⟩
  choose C hCsub hCcompact hCloss using hcore
  exact ⟨C, δ, hδsum, hCsub, hCcompact, fun n => (hCloss n).le⟩

/-- The once-charged compact-core data can be constructed directly from
finite-dimensional Brownian marginals.

Every measurable cylinder is first represented by a finite support and
measurable base.  Half of the common positive threshold is assigned to the
single global coordinate-box charge.  The other half funds a summable family
of inside-box compact approximation errors.  No monotonicity property is
needed for these constructions; it remains an explicit hypothesis because it
is part of the exact residual interface consumed later. -/
theorem brownianCylinderOnceChargedCompactCore :
    BrownianCylinderOnceChargedCompactCore := by
  intro A hAcyl hAanti r hr hlower
  have hrep : ∀ n, ∃ (I : Finset NNReal) (S : Set (I → ℝ)),
      MeasurableSet S ∧ A n = cylinder I S := by
    intro n
    exact (mem_measurableCylinders _).1 (hAcyl n)
  choose I S hSmeas hArep using hrep
  let β : ℝ≥0∞ := r / 2
  have hr0 : r ≠ 0 := hr.ne'
  have hrtop : r ≠ ∞ :=
    lt_top_iff_ne_top.mp ((hlower 0).trans_le le_top)
  have hβpos : 0 < β := ENNReal.half_pos hr0
  have hβ : β < r := ENNReal.half_lt_self hr0 hrtop
  obtain ⟨q, hqcompact, hqnonempty, hboxLoss⟩ :=
    exists_onceCharged_global_box_data A hAcyl I hβpos.ne'
  have hremaining : r - β ≠ 0 := (tsub_pos_iff_lt.mpr hβ).ne'
  obtain ⟨C, δ, hδsum, hCsub, hCcompact, hinsideLoss⟩ :=
    exists_summable_insideBox_compactCores
      I S hSmeas q hqcompact hremaining
  exact ⟨I, S, C, q, β, δ, hβ, hδsum, hSmeas, hArep, hCsub,
    hCcompact, hinsideLoss, hqcompact, hqnonempty, hboxLoss⟩

end BrownianOnceChargedInsideBoxCore
end BlockBand.SourceProcess.WienerRecovery.CEH
