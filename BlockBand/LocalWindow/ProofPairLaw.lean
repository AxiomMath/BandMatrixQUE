module

public import BlockBand.LocalWindow.Statements
public import BlockBand.DeterminantScore.PairRowMoment

/-!
# The pair-law clause

Bounds under the split law transfer to every pair law at the cost of one power of `W` in the
failure exponent.

## Main results

* `splitPairLaw_le`: for every set `Ω` of the split space (no measurability),
  `P♯_α(Ω) ≤ (n/2) P(Ω)`, from `pairMass ≤ 1` a.s. (`ScoreMoments.PairRow.ae_pairMass_le_one`).
* `splitPairLaw_le_of`: if `P(Ω) ≤ C W^{-(D+1)}` and `n ≤ TW`, then
  `P♯_α(Ω) ≤ (TC/2) W^{-D}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow

open MeasureTheory BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open scoped ENNReal

variable {p : Parameters} {i : ZMod p.n}

/-- `P♯_α(Ω) ≤ (n/2) P(Ω)` for every set `Ω` of the split space. -/
theorem splitPairLaw_le {model : p.GaussianRingModel} {Pω : Measure (SplitState p i)}
    (hPω : IsPairSplitting p i model (splitS p) Pω) (α : Fin p.N)
    (Ω : Set (SplitState p i × PairMatrix p i)) :
    splitPairLaw p i α Pω Ω ≤ ENNReal.ofReal ((p.n : ℝ) / 2) * splitLaw p i Pω Ω := by
  set Ω' := toMeasurable (splitLaw p i Pω) Ω
  have hmono : splitPairLaw p i α Pω Ω ≤ splitPairLaw p i α Pω Ω' :=
    measure_mono (subset_toMeasurable _ _)
  refine hmono.trans ?_
  unfold splitPairLaw
  rw [withDensity_apply _ (measurableSet_toMeasurable _ _)]
  have hae := BlockBand.DeterminantScore.ScoreMoments.PairRow.ae_pairMass_le_one hPω α
  calc ∫⁻ x in Ω', ENNReal.ofReal ((p.n : ℝ) / 2 * pairMass p i α (assemble p i x.1 x.2))
        ∂splitLaw p i Pω
      ≤ ∫⁻ _ in Ω', ENNReal.ofReal ((p.n : ℝ) / 2) ∂splitLaw p i Pω := by
        refine lintegral_mono_ae (ae_restrict_of_ae ?_)
        filter_upwards [hae] with x hx
        apply ENNReal.ofReal_le_ofReal
        have hn : 0 ≤ (p.n : ℝ) / 2 := by positivity
        calc (p.n : ℝ) / 2 * pairMass p i α (assemble p i x.1 x.2) ≤ (p.n : ℝ) / 2 * 1 :=
              mul_le_mul_of_nonneg_left hx hn
          _ = (p.n : ℝ) / 2 := mul_one _
    _ = ENNReal.ofReal ((p.n : ℝ) / 2) * splitLaw p i Pω Ω := by
        rw [setLIntegral_const, measure_toMeasurable]

/-- **The `+1` in the failure exponent.** If `n ≤ TW` and `P(Ω) ≤ C W^{-(D+1)}`, then every
pair law gives `P♯_α(Ω) ≤ (TC/2) W^{-D}`. -/
theorem splitPairLaw_le_of {model : p.GaussianRingModel} {Pω : Measure (SplitState p i)}
    (hPω : IsPairSplitting p i model (splitS p) Pω) (α : Fin p.N)
    {Ω : Set (SplitState p i × PairMatrix p i)} {T C D : ℝ} (hC : 0 ≤ C)
    (hn : (p.n : ℝ) ≤ T * (p.W : ℝ))
    (hΩ : splitLaw p i Pω Ω ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-(D + 1)))) :
    splitPairLaw p i α Pω Ω ≤ ENNReal.ofReal (T * C / 2 * (p.W : ℝ) ^ (-D)) := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hT : 0 ≤ T := by
    have : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
    by_contra h
    push Not at h
    nlinarith
  refine (splitPairLaw_le hPω α Ω).trans ?_
  calc ENNReal.ofReal ((p.n : ℝ) / 2) * splitLaw p i Pω Ω
      ≤ ENNReal.ofReal ((p.n : ℝ) / 2) * ENNReal.ofReal (C * (p.W : ℝ) ^ (-(D + 1))) :=
        mul_le_mul_right hΩ _
    _ = ENNReal.ofReal ((p.n : ℝ) / 2 * (C * (p.W : ℝ) ^ (-(D + 1)))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (T * C / 2 * (p.W : ℝ) ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        have hpow : (p.W : ℝ) ^ (-(D + 1)) = (p.W : ℝ) ^ (-D) * (p.W : ℝ)⁻¹ := by
          rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hW, Real.rpow_neg_one]
        rw [hpow]
        have hWD : 0 ≤ (p.W : ℝ) ^ (-D) := Real.rpow_nonneg hW.le _
        have key : (p.n : ℝ) * (p.W : ℝ)⁻¹ ≤ T := by
          rw [← div_eq_mul_inv, div_le_iff₀ hW]; exact hn
        have : (p.n : ℝ) / 2 * (C * ((p.W : ℝ) ^ (-D) * (p.W : ℝ)⁻¹)) =
            ((p.n : ℝ) * (p.W : ℝ)⁻¹) * (C / 2 * (p.W : ℝ) ^ (-D)) := by ring
        rw [this, show T * C / 2 * (p.W : ℝ) ^ (-D) = T * (C / 2 * (p.W : ℝ) ^ (-D)) by ring]
        exact mul_le_mul_of_nonneg_right key (by positivity)

end BlockBand.LocalWindow
