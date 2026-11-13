module

public import BlockBand.LocalWindow.ProofPartTwoLargeRhoSection
public import BlockBand.QUE.GUEInputs.Fields
public import BlockBand.QUE.GUEInputs.PartTwoCompressETH

/-!
# Small sections from the compressed ETH (GUE inputs)

`gue_largeRhoCompBad_section_le`: the sections of the large-`ρ` bad set under `GUE_{2W}(s/2W)` are
small, by the compressed window estimate.

The statements are those of `BlockBand.LocalWindow.ProofPartTwoLargeRhoSection`, with `NativeInputs`
replaced by the hypotheses `EigenpairsExist` and `SpacingExists` (fields of
`External.CEH.SourceContract`) as needed, and without `GUEWignerFamilyAdapter`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo.GUEInputs

open MeasureTheory Matrix Set
open BlockBand.Coarea BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH BlockBand.LocalWindow.ProofCount
open scoped ENNReal Matrix.Norms.L2Operator

section

variable {p : Parameters} {i : ZMod p.n}
attribute [local instance] pairSite_nonempty

/-- **The sections are small, from the compressed ETH** (`ExternalETH` and
`CompressedGUELawBridgeStatement` through `gue_not_compressWindowGood_le`).
Constants `A, C, [sLo, sHi], r, v₀` first; then `β₀`; then `β < β₀`, `ε', D > 0`; then `N₀`.
For every `p, i` with `N₀ ≤ 2W - 1`, `s > 0` with `s' = compressVar p s ∈ [sLo, sHi]`, selections,
radius `ε`, grids `Es, Ms`, compressed observables `J` and exterior point `ω` at which every
labelled `(j₀, e, μ)` has the ETH hypotheses (`s'^{-1/2}‖compRegM‖ ≤ C(2W-1)^A`, a root
rectangle of `compRegM` at `μ`, `J j₀ e ω` a Hermitian contraction), the section of
`largeRhoCompBad` under `GUE_{2W}(s/2W)` is at most `|labels| |Es| |Ms| (2W - 1)^{-D}`. -/
theorem gue_largeRhoCompBad_section_le (hSp : BlockBand.QUE.GUEInputs.SpacingExists)
 (hMDE : MDEBranchIdentification) (hETH : ExternalETH)
    (hComp : CompressedGUELawBridgeStatement)
    (A C sLo sHi r v₀ : ℝ) (hsLo : 0 < sLo) (hsHi : sLo ≤ sHi) (hr : 0 < r) (hv₀ : 0 < v₀) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ 1 / 2 ∧ ∀ β : ℝ, 0 < β → β < β₀ → ∀ ε' D : ℝ, 0 < ε' → 0 < D →
      ∃ N₀ : ℕ, ∀ (p : Parameters) (i : ZMod p.n), N₀ ≤ 2 * p.W - 1 → ∀ s : ℝ, 0 < s →
        compressVar p s ∈ Icc sLo sHi →
        ∀ (sel : CEH.EigenpairSelection (2 * p.W)) (sel' : CEH.EigenpairSelection (2 * p.W - 1))
          (ε : ℝ) (Es Ms : Finset ℝ)
          (J : ExteriorSite p i → ℝ → SplitState p i →
            Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ) (om : SplitState p i),
          (∀ j₀ : ExteriorSite p i, ∀ e ∈ Es, ∀ μ ∈ Ms, om ∈ poleLabelSet ε j₀ e →
            (Real.sqrt (compressVar p s))⁻¹ * ‖compRegM sel ε j₀ e om‖ ≤
                C * ((2 * p.W - 1 : ℕ) : ℝ) ^ A ∧
              RootRectangle (compRegM sel ε j₀ e om) (compressVar p s) μ r v₀ ∧
              (J j₀ e om).IsHermitian ∧ ‖J j₀ e om‖ ≤ 1) →
          gueMeasure (PairSite p i) (pairTime p s)
              (Prod.mk om ⁻¹' largeRhoCompBad sel sel' ε Es Ms (compressVar p s) β ε' J) ≤
            (Fintype.card (ExteriorSite p i) * Es.card * Ms.card : ℝ≥0∞) *
              ENNReal.ofReal (((2 * p.W - 1 : ℕ) : ℝ) ^ (-D)) := by
  obtain ⟨β₀, hβ₀, hβ₀', h⟩ := BlockBand.LocalWindow.ProofPartTwo.GUEInputs.gue_not_compressWindowGood_le hSp hMDE hETH hComp A C sLo
    sHi r v₀ hsLo hsHi hr hv₀
  refine ⟨β₀, hβ₀, hβ₀', fun β hβ hββ ε' D hε' hD => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h β hβ hββ ε' D hε' hD
  refine ⟨N₀, fun p i hN s hs hsI sel sel' ε Es Ms J om hyp => ?_⟩
  refine largeRhoCompBad_section_le _ sel sel' ε Es Ms _ β ε' J om _ ?_
  intro j₀ e he μ hμ hl
  obtain ⟨hn, hR, hJh, hJn⟩ := hyp j₀ e he μ hμ hl
  have hU := (poleIsometry_spec sel hl.choose hl.choose_spec.1).1
  exact hN₀ p i hN s hs hsI (compRegF sel ε j₀ e om) hn μ hR sel' (J j₀ e om) hJh hJn _ hU

end

end BlockBand.LocalWindow.ProofPartTwo.GUEInputs
