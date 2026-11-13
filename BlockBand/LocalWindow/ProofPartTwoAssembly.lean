module

public import BlockBand.LocalWindow.ProofPartTwo

/-!
# Part (ii) of the physical local window: small `W` is absorbed into the constant

It suffices to prove the exterior-conditional form of part (ii) for `W` above a threshold chosen
together with the constant.

## Main results

* `PartTwoConditionalLargeStatement`: `PartTwoConditionalStatement` with an
  extra threshold `W₀` chosen together with `C`, the conclusion being required only for
  `W ≥ W₀`.
* **`partTwoConditional_of_large`**: `PartTwoConditionalLargeStatement →
  PartTwoConditionalStatement` (for `W < W₀`: `Ω_ext` = everything, `S = ∅`, and
  `Pω(Ω_ext) = 1 ≤ W₀^D W^{-D}`).

With `ProofPartTwo.physicalLocalWindow_partTwo_of_conditional`, `PartTwoConditionalLargeStatement`
implies `PhysicalLocalWindowPartTwoStatement` (`physicalLocalWindow_partTwo_of_large`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open MeasureTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open scoped ENNReal NNReal

/-- **Part (ii) of the physical local window, conditional on the exterior, for large `W`**: `PartTwoConditionalStatement` with a threshold `W₀` chosen with `C`; the
conclusion is required only for `p.W ≥ W₀`. -/
def PartTwoConditionalLargeStatement : Prop :=
  ∀ b T ϑ : ℝ, 0 < ϑ →
    ∃ (δ : ℝ) (k : ℕ), 0 < δ ∧ δ < 1 ∧
      ∀ ε : ℝ, 0 < ε → ∀ D : ℝ, 0 < D → ∀ K₀ : ℝ,
        ∃ (C : ℝ) (W₀ : ℕ), ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
          W₀ ≤ p.W →
          ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
            IsPairSplitting p i model (splitS p) Pω →
            ∀ B : SplitState p i → ℝ → PairMatrix p i, IsWindowObservable p i k K₀ B →
              ∃ (Ωext : Set (SplitState p i)) (S : Set (SplitState p i × PairMatrix p i)),
                MeasurableSet S ∧ Pω Ωext ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D)) ∧
                (∀ om ∉ Ωext, gueMeasure (PairSite p i) (pairTime p (splitS p))
                    (Prod.mk om ⁻¹' S) ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D))) ∧
                ∀ x : SplitState p i × PairMatrix p i, x.1 ∉ Ωext → x ∉ S →
                  PartTwoGood p i ϑ δ C ε B x

/-- `1 ≤ W₀^D W^{-D}` for `0 < W < W₀`, `D ≥ 0`. -/
theorem one_le_rpow_mul_rpow_neg {W W₀ D : ℝ} (hW : 0 < W) (hWW : W ≤ W₀) (hD : 0 ≤ D) :
    1 ≤ W₀ ^ D * W ^ (-D) := by
  rw [Real.rpow_neg hW.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hW _)]
  exact Real.rpow_le_rpow hW.le hWW hD

/-- **Small `W` is absorbed into the constant**: the large-`W` conditional
statement gives `PartTwoConditionalStatement`, with constant `max C (W₀^D)`. -/
theorem partTwoConditional_of_large (h : PartTwoConditionalLargeStatement) :
    PartTwoConditionalStatement := by
  intro b T ϑ hϑ
  obtain ⟨δ, k, hδ, hδ1, hcond⟩ := h b T ϑ hϑ
  refine ⟨δ, k, hδ, hδ1, fun ε hε D hD K₀ => ?_⟩
  obtain ⟨C, W₀, hC⟩ := hcond ε hε D hD K₀
  refine ⟨max C ((W₀ : ℝ) ^ D), fun p hpb hn model i Pω hPω B hB => ?_⟩
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hWD : 0 ≤ (p.W : ℝ) ^ (-D) := Real.rpow_nonneg hW.le _
  by_cases hlarge : W₀ ≤ p.W
  · obtain ⟨Ωext, S, hS, hext, hsec, hgood⟩ := hC p hpb hn hlarge model i Pω hPω B hB
    have hle : ENNReal.ofReal (C * (p.W : ℝ) ^ (-D)) ≤
        ENNReal.ofReal (max C ((W₀ : ℝ) ^ D) * (p.W : ℝ) ^ (-D)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hWD)
    refine ⟨Ωext, S, hS, hext.trans hle, fun om hom => (hsec om hom).trans hle,
      fun x hx1 hx2 => partTwoGood_mono (le_max_left _ _) (hgood x hx1 hx2)⟩
  · push Not at hlarge
    refine ⟨Set.univ, ∅, MeasurableSet.empty, ?_, fun om hom => absurd (Set.mem_univ om) hom,
      fun x hx1 _ => absurd (Set.mem_univ _) hx1⟩
    rw [measure_univ_of_isPairSplitting' hPω, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hWW : (p.W : ℝ) ≤ W₀ := by exact_mod_cast hlarge.le
    exact (one_le_rpow_mul_rpow_neg hW hWW hD.le).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hWD)

/-- `PartTwoConditionalLargeStatement → PhysicalLocalWindowPartTwoStatement`. -/
theorem physicalLocalWindow_partTwo_of_large (h : PartTwoConditionalLargeStatement) :
    PhysicalLocalWindowPartTwoStatement :=
  physicalLocalWindow_partTwo_of_conditional (partTwoConditional_of_large h)

end BlockBand.LocalWindow.ProofPartTwo
