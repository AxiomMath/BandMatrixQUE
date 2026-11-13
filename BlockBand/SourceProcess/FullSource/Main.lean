module

public import BlockBand.SourceProcess.FullSource.BirthZero
public import BlockBand.SourceProcess.FullSource.EdgeClock
public import BlockBand.Transmission.PassiveLayer.FlucMain

/-!
# Assembly: tags, clock and edge clock from `FullSourceEstimates`

The one-layer estimates `FullSourceEstimates` give the moments of the tag births, the tag
propagation bound, the edge clock moments, and, together with the bulk clock-square bound, the
full-source moments. Hypotheses: `GaussianAbsorptionContract`, `ScalarRecursionContract`,
`GaussianLpGradient` and `FullSourceEstimates`.

* `tagPropagationBulk_holds`: `TagPropagationBulk`;
* `edgeClockMoments_holds`: `EdgeClockMomentsContract`;
* `fullSourceMomentsBulk_of`, `fullSourceMoments_of_clockSquare`: the bulk `clock` and `tag`
  fields, and `FullSourceMomentsContract` given `ClockSquareBulk`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PathScalar BlockBand.Transmission.PassiveLayer
open scoped ENNReal

/-- **Births.** -/
theorem tagBirthMoments_of (hFS : FullSourceEstimates) (hGA : GaussianAbsorptionContract) :
    TagBirthMoments := by
  intro b hb0 hb κ hκ q hq
  obtain ⟨CD, WD, hD⟩ := hFS.moments b hb0 hb κ hκ ((2 * q : ℕ) : ℝ)
    (by exact_mod_cast (show 1 ≤ 2 * q by omega))
  obtain ⟨B0, W0, hB0, h0⟩ := birth_moment_zero hGA hb0 hb hκ hq
  refine ⟨max B0 ((max CD 0) ^ (2 * q)), max (max WD W0) 1, le_max_of_le_left hB0,
    fun W hW E hE k => ?_⟩
  have hWD : WD ≤ W := le_trans (by simp) hW
  have hW0 : W0 ≤ W := le_trans (by simp) hW
  have hW1 : 1 ≤ W := le_trans (by simp) hW
  obtain ⟨hE1, hE2⟩ := bulk_bounds hκ hE
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact (h0 W hW0 E hE).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · refine (birth_moment_succ hb0 hb hE1 hE2 hW1 hk hq (le_max_right CD 0) fun XX hXX =>
      (hD W hWD E hE XX hXX).2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))).trans ?_
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-- **The tag bound in its propagation form.** -/
theorem tagPropagationBulk_holds (hFS : FullSourceEstimates) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) : TagPropagationBulk :=
  tagPropagationBulk_of hFS (passiveMeanStep_holds (passiveBounds_holds hGA hLp))
    (passiveFluctuationStep_holds hGA hLp) (superexpExit_of hSR) (tagBirthMoments_of hFS hGA)

/-- **`EdgeClockMomentsContract`** from `FullSourceEstimates`, `GaussianAbsorptionContract`,
`GaussianLpGradient` and `ScalarRecursionContract`. -/
theorem edgeClockMoments_holds (hFS : FullSourceEstimates) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) : EdgeClockMomentsContract :=
  edgeClock_of_propagation (tagPropagationBulk_holds hFS hGA hLp hSR)

/-- The bulk `clockSquare` field: `E|Tr (𝒰_j*𝒰_j)²| ≤ CW(j+1)³` for `j ≤ TW`, uniformly on the
bulk. -/
def ClockSquareBulk : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ j : ℕ, (j : ℝ) ≤ T * W →
      ∫⁻ ω, ‖(((boundaryToInterior b E W j ω)ᴴ * boundaryToInterior b E W j ω) ^ 2).trace‖ₑ
          ∂growthPathLaw W b ≤ ENNReal.ofReal (C * W * ((j : ℝ) + 1) ^ 3)

/-- **`FullSourceMomentsBulk`** given the `clockSquare` field. -/
theorem fullSourceMomentsBulk_of (hFS : FullSourceEstimates) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hSq : ClockSquareBulk) :
    FullSourceMomentsBulk where
  clock := clock_of_tag (tag_of_propagation (tagPropagationBulk_holds hFS hGA hLp hSR))
  clockSquare := hSq
  tag := tag_of_propagation (tagPropagationBulk_holds hFS hGA hLp hSR)

/-- **`FullSourceMomentsContract`** given the `clockSquare` field `ClockSquareBulk` (proved as
`clockSquareBulk_holds`). -/
theorem fullSourceMoments_of_clockSquare (hFS : FullSourceEstimates)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hSq : ClockSquareBulk) : FullSourceMomentsContract :=
  fullSourceMoments_of_bulk (fullSourceMomentsBulk_of hFS hGA hLp hSR hSq)

end BlockBand.SourceProcess.FullSource
