module

public import BlockBand.LocalWindow.ProofPartTwoMeasurable
public import BlockBand.QUE.GUEInputs.Fields
public import BlockBand.QUE.GUEInputs.PartTwoPoint

/-!
# The measurable window ETH bad set at one grid point (GUE inputs)

`gridWindowBad`: the window ETH bad set is measurable and its sections have
`GUE_{2W}(s/2W)`-probability at most `(2W)^{-D}`.

The statements are those of `BlockBand.LocalWindow.ProofPartTwoMeasurable`, with `NativeInputs`
replaced by the hypotheses `EigenpairsExist` and `SpacingExists` (fields of
`External.CEH.SourceContract`) as needed, and without `GUEWignerFamilyAdapter`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo.GUEInputs

open MeasureTheory Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH BlockBand.LocalWindow.LawBridge
open scoped ENNReal Matrix.Norms.L2Operator

section

variable {p : Parameters} {i : ZMod p.n}

/-- **The measurable, GUE-small window ETH bad set at one grid point** (from
`gue_not_pairWindowGood_le` with `measurableSet_not_pairWindowGood`). Same constants and order of
quantifiers as `gue_not_pairWindowGood_le`. Uniformly in `p, i` with `2W ≥ N₀`, `s ∈ [sLo, sHi]`,
measurable spaces `X`, measurable `K, J : X → PairMatrix` with `K x` Hermitian and `J x` a
Hermitian contraction, `E₀` and eigenpair selections, the set
`S = {(x, G) | ¬ PairWindowGood (K x) _ sel s E₀ β ε (J x) G}` is measurable, and its section at
every `x` with `s^{-1/2}‖K x‖ ≤ C (2W)^A` and `PairRootRectangle (K x) s E₀ r v₀` has
`GUE_{2W}(s/2W)`-probability at most `(2W)^{-D}`. -/
theorem gridWindowBad (hSp : BlockBand.QUE.GUEInputs.SpacingExists)
    (hMDE : MDEBranchIdentification) (hETH : ExternalETH) (hBridge : PairGUELawBridgeStatement)
    (A C sLo sHi r v₀ : ℝ) (hsLo : 0 < sLo) (hsHi : sLo ≤ sHi) (hr : 0 < r) (hv₀ : 0 < v₀) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ 1 / 2 ∧ ∀ β : ℝ, 0 < β → β < β₀ → ∀ ε D : ℝ, 0 < ε → 0 < D →
      ∃ N₀ : ℕ, ∀ (p : Parameters) (i : ZMod p.n), N₀ ≤ 2 * p.W → ∀ s ∈ Icc sLo sHi,
        ∀ (X : Type) [MeasurableSpace X] (K J : X → PairMatrix p i), Measurable K →
          ∀ hH : ∀ x, (K x).IsHermitian, Measurable J → (∀ x, (J x).IsHermitian) →
          (∀ x, ‖J x‖ ≤ 1) → ∀ (E₀ : ℝ) (sel : CEH.EigenpairSelection (2 * p.W)),
          MeasurableSet {y : X × PairMatrix p i |
            ¬ PairWindowGood (K y.1) (hH y.1) sel s E₀ β ε (J y.1) y.2} ∧
          ∀ x : X, (Real.sqrt s)⁻¹ * ‖K x‖ ≤ C * ((2 * p.W : ℕ) : ℝ) ^ A →
            PairRootRectangle (K x) s E₀ r v₀ →
            gueMeasure (PairSite p i) (pairTime p s)
                (Prod.mk x ⁻¹' {y : X × PairMatrix p i |
                  ¬ PairWindowGood (K y.1) (hH y.1) sel s E₀ β ε (J y.1) y.2}) ≤
              ENNReal.ofReal (((2 * p.W : ℕ) : ℝ) ^ (-D)) := by
  obtain ⟨β₀, hβ₀, hβ₀2, h⟩ := BlockBand.LocalWindow.ProofPartTwo.GUEInputs.gue_not_pairWindowGood_le hSp hMDE hETH hBridge A C sLo sHi
    r v₀ hsLo hsHi hr hv₀
  refine ⟨β₀, hβ₀, hβ₀2, fun β hβ hββ ε D hε hD => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h β hβ hββ ε D hε hD
  refine ⟨N₀, fun p i hN s hsI X _ K J hKm hH hJm hJH hJn E₀ sel => ⟨?_, fun x hKx hR => ?_⟩⟩
  · exact measurableSet_not_pairWindowGood hKm hH hJm sel (hsLo.trans_le hsI.1) E₀ β ε
  · exact hN₀ p i hN s hsI (K x) (hH x) hKx E₀ hR sel (J x) (hJH x) (hJn x)

end

end BlockBand.LocalWindow.ProofPartTwo.GUEInputs
