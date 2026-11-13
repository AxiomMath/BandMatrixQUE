module

public import BlockBand.LocalWindow.ProofPartTwoLargeEventsObs
public import BlockBand.LocalWindow.ProofNormEvent
public import BlockBand.LocalWindow.ProofPartTwoExterior

/-!
# The norm event `‖F_reg(E) - E + G‖ ≤ K` of the large-`ρ` branch

The fresh `GUE` block is bounded in operator norm with overwhelming probability, which bounds the
regular part `F_reg(E) - E + G` of the block form on the pole interval.

## Main results

* `gue_gueEvent_section_le`: the `GUE` norm event, section form.
* **`opNorm_regK_add_le`**: on the pole interval, off the norm event and with the exterior norm
  bounds `ExtNormBounds`, `‖F_reg(E) - E + G‖ ≤ nW + C_G + (nW)²/ε + |E| + C_G` (the `K` of the
  block form).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open MeasureTheory Matrix Set
open BlockBand.Coarea BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH BlockBand.LocalWindow.ProofCount
open BlockBand.LocalWindow.ProofNormEvent BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Matrix.Norms.L2Operator

variable {p : Parameters} {i : ZMod p.n}

theorem measurableSet_gueEvent (CG : ℝ) : MeasurableSet (gueEvent p i CG) :=
  measurableSet_lt measurable_const (continuous_norm.measurable.comp measurable_snd)

/-- **The `GUE` norm event, section form** (`gueNormTail_holds`): constants `C_G, c_G > 0`
first; for every `p, i` and exterior point `ω`, `GUE_{2W}(s/2W){‖G‖ > C_G} ≤ e^{-c_G · 2W}`. -/
theorem gue_gueEvent_section_le :
    ∃ CG cG : ℝ, 0 < CG ∧ 0 < cG ∧ ∀ (p : Parameters) (i : ZMod p.n) (om : SplitState p i),
      gueMeasure (PairSite p i) (pairTime p (splitS p)) (Prod.mk om ⁻¹' gueEvent p i CG) ≤
        ENNReal.ofReal (Real.exp (-(cG * (2 * (p.W : ℝ))))) := by
  obtain ⟨C, c, hC, hc, h⟩ := BlockBand.DeterminantScore.GUENormTail.gueNormTail_holds
  refine ⟨C, c, hC, hc, fun p i om => ?_⟩
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * p.W := by
    exact_mod_cast BlockBand.Angular.FiberAngular.card_pairSite p i
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hs : 0 < splitS p := lt_min p.c_pos p.b_pos
  have hs1 : splitS p ≤ 1 := by
    have := min_le_right p.c p.b
    unfold splitS; linarith [p.b_lt_half]
  have ht : ((pairTime p (splitS p) : ℝ≥0) : ℝ) * (Fintype.card (PairSite p i) : ℝ) ≤ 1 := by
    rw [hcard, pairTime, Real.coe_toNNReal _ (by positivity)]
    rw [div_mul_cancel₀ _ (by positivity)]
    exact hs1
  have hsub : Prod.mk om ⁻¹' gueEvent p i C ⊆
      {G : PairMatrix p i | C * Real.sqrt ((pairTime p (splitS p) : ℝ) *
        (Fintype.card (PairSite p i) : ℝ)) < ‖G‖} := by
    intro G hG
    have : Real.sqrt ((pairTime p (splitS p) : ℝ) * (Fintype.card (PairSite p i) : ℝ)) ≤ 1 :=
      Real.sqrt_le_one.mpr ht
    show _ < ‖G‖
    have hG' : C < ‖G‖ := hG
    nlinarith
  refine (measure_mono hsub).trans ((h (PairSite p i) (pairTime p (splitS p))).trans (le_of_eq ?_))
  rw [hcard]

/-- **The block-form constant `K`**: on the pole interval (`ε > 0`), with
`ExtNormBounds` (`‖C‖ ≤ nW`, `‖V‖ ≤ nW + C_G`) and `‖G‖ ≤ C_G`:
`‖F_reg(E) - E + G‖ ≤ nW + C_G + (nW)²/ε + |E| + C_G`. -/
theorem opNorm_regK_add_le {ε : ℝ} (hε : 0 < ε) {om : SplitState p i} (hH : om.1.IsHermitian)
    {CG : ℝ} (hext : ExtNormBounds p i CG om)
    {j₀ : ExteriorSite p i} {E : ℝ} (hsep : PoleSeparated ε hH j₀ E) {G : PairMatrix p i}
    (hG : ‖G‖ ≤ CG) :
    ‖regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1 + G‖ ≤
      ((p.n : ℝ) * p.W + CG) + ((p.n : ℝ) * p.W) ^ 2 / ε + |E| + CG := by
  have hnW : (0 : ℝ) ≤ (p.n : ℝ) * p.W := by positivity
  have hCG : 0 ≤ CG := (norm_nonneg _).trans hG
  have hC : ‖om.2.1‖ ≤ (p.n : ℝ) * p.W := opNorm_le_of_toE _ hnW hext.1
  have hV : ‖om.2.2‖ ≤ (p.n : ℝ) * p.W + CG := opNorm_le_of_toE _ (by positivity) hext.2.2
  have h1 := opNorm_regK_le hε om hH j₀ hsep
  have hC2 : ‖om.2.1‖ ^ 2 / ε ≤ ((p.n : ℝ) * p.W) ^ 2 / ε :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hC 2) hε.le
  refine (norm_add_le _ _).trans ?_
  linarith

end BlockBand.LocalWindow.ProofPartTwo
