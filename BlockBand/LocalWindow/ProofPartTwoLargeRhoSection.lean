module

public import BlockBand.LocalWindow.ProofPartTwoLargeRhoIsometry

/-!
# The measurable compressed bad set of the large-`ρ` branch

The joint bad set of the compressed window estimate over pole labels, grid energies and window
centres is measurable, and its sections satisfy a union bound.

## Main results

* `poleLabelSet ε j₀ e` (`H_R` Hermitian, `j₀` simple, `PoleSeparated ε j₀ e`; measurable by
  `measurableSet_poleLabel`).
* `compRegM sel ε j₀ e ω` (Hermitian part of `U(ω)*(regFm(e) - e)U(ω)`), `compRegF` (as an element of
  `CEH.SourceHermitian (2W - 1)`), **`measurable_compRegM`**, **`compRegM_eq`** (on the label event with `V`
  Hermitian: `= U*(F_reg(e) - e)U`, with `regF`).
* **`largeRhoCompBad`**: `⋃_{j₀} ⋃_{e ∈ Es} ⋃_{μ ∈ Ms} {(ω, G) | ω ∈ poleLabelSet ε j₀ e,
  ¬ NatWindowGood (compRegF ω) sel' s' μ β ε' (J j₀ e ω) (U(ω)* G U(ω))}` for measurable compressed
  observables `J j₀ e`; **`measurableSet_largeRhoCompBad`**.
* **`largeRhoCompBad_section_le`** (union bound): if each compressed window bad set at a labelled
  `(j₀, e, μ)` has `GUE`-probability at most `t` at `ω`, the section has probability at most
  `|labels| |Es| |Ms| t`.
* **`gue_largeRhoCompBad_section_le`**: under `ExternalETH` and
  `CompressedGUELawBridgeStatement` (through `gue_not_compressWindowGood_le`), at every `ω` where
  each labelled `(j₀, e, μ)` has the ETH hypotheses (norm bound, root rectangle of `compRegM` at
  `μ`, `J` a Hermitian contraction), the section is at most
  `|labels| |Es| |Ms| (2W - 1)^{-D}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open MeasureTheory Matrix Set
open BlockBand.Coarea BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH BlockBand.LocalWindow.ProofCount
open scoped ENNReal Matrix.Norms.L2Operator

variable {p : Parameters} {i : ZMod p.n}

attribute [local instance] pairSite_nonempty

/-!
## The compressed regular deformation in measurable form
-/

section Comp

/-- The pole-label event: `H_R` Hermitian, the `j₀`-th eigenvalue simple and alone within `ε`
of `e`. -/
def poleLabelSet (ε : ℝ) (j₀ : ExteriorSite p i) (e : ℝ) : Set (SplitState p i) :=
  {om | ∃ hH : om.1.IsHermitian, PoleSimple hH j₀ ∧ PoleSeparated ε hH j₀ e}

theorem measurableSet_poleLabelSet (ε : ℝ) (j₀ : ExteriorSite p i) (e : ℝ) :
    MeasurableSet (poleLabelSet (p := p) (i := i) ε j₀ e) :=
  measurableSet_poleLabel ε j₀ e

/-- The compressed regular deformation `U(ω)*(regFm(e) - e)U(ω)` (Hermitian part). -/
def compRegM (sel : CEH.EigenpairSelection (2 * p.W)) (ε : ℝ) (j₀ : ExteriorSite p i) (e : ℝ)
    (om : SplitState p i) : Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ :=
  (1 / 2 : ℂ) • ((poleIsometry sel j₀ om)ᴴ * (regFm ε j₀ om.1 om.2.1 om.2.2 e - (e : ℂ) • 1) *
      poleIsometry sel j₀ om +
    ((poleIsometry sel j₀ om)ᴴ * (regFm ε j₀ om.1 om.2.1 om.2.2 e - (e : ℂ) • 1) *
      poleIsometry sel j₀ om)ᴴ)

theorem isHermitian_compRegM (sel : CEH.EigenpairSelection (2 * p.W)) (ε : ℝ)
    (j₀ : ExteriorSite p i) (e : ℝ) (om : SplitState p i) :
    (compRegM sel ε j₀ e om).IsHermitian := by
  unfold compRegM Matrix.IsHermitian
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  congr 1
  simp

/-- `compRegM` as an element of `CEH.SourceHermitian (2W - 1)`. -/
def compRegF (sel : CEH.EigenpairSelection (2 * p.W)) (ε : ℝ) (j₀ : ExteriorSite p i) (e : ℝ)
    (om : SplitState p i) : CEH.SourceHermitian (2 * p.W - 1) :=
  ⟨compRegM sel ε j₀ e om, isHermitian_compRegM sel ε j₀ e om⟩

/-- **The compressed regular deformation is measurable** (`ε > 0`). -/
theorem measurable_compRegM (sel : CEH.EigenpairSelection (2 * p.W)) {ε : ℝ} (hε : 0 < ε)
    (j₀ : ExteriorSite p i) (e : ℝ) : Measurable (compRegM (p := p) (i := i) sel ε j₀ e) := by
  have hM : Measurable fun om : SplitState p i =>
      regFm ε j₀ om.1 om.2.1 om.2.2 e - (e : ℂ) • (1 : PairMatrix p i) :=
    (measurable_regFm hε j₀ e).sub measurable_const
  have hZ := measurable_poleCompress sel j₀ hM
  have hc : Continuous fun Z : Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ =>
      (1 / 2 : ℂ) • (Z + Zᴴ) :=
    (continuous_const_smul (1 / 2 : ℂ)).comp (continuous_id.add continuous_id.matrix_conjTranspose)
  exact hc.measurable.comp hZ

/-- **On the label event `compRegM` is the compression of `F_reg(e) - e`** (`V` Hermitian). -/
theorem compRegM_eq (sel : CEH.EigenpairSelection (2 * p.W)) (ε : ℝ) {om : SplitState p i}
    (hH : om.1.IsHermitian) (hV : om.2.2.IsHermitian) {j₀ : ExteriorSite p i}
    (hs : PoleSimple hH j₀) {e : ℝ} (hsep : PoleSeparated ε hH j₀ e) :
    compRegM sel ε j₀ e om = (poleIsometry sel j₀ om)ᴴ *
      (regF hH j₀ om.2.1 om.2.2 e - (e : ℂ) • 1) * poleIsometry sel j₀ om := by
  have hK := isHermitian_regK om hH hV j₀ e
  have hZ : ((poleIsometry sel j₀ om)ᴴ * (regF hH j₀ om.2.1 om.2.2 e - (e : ℂ) • 1) *
      poleIsometry sel j₀ om).IsHermitian := isHermitian_conjTranspose_mul_mul _ hK
  unfold compRegM
  rw [← regF_eq_regFm ε hH hs om.2.1 om.2.2 hsep, hZ.eq, ← two_smul ℂ, smul_smul]
  norm_num

end Comp

/-!
## The joint compressed bad set
-/

section Bad

/-- **The joint compressed bad set of the large-`ρ` branch**: over all pole labels `j₀`, grid
energies `e ∈ Es` and window centres `μ ∈ Ms`, the points `(ω, G)` with `ω` in the label event of
`(j₀, e)` and the compressed fresh noise `U(ω)* G U(ω)` violating the compressed window bound for
`compRegF` and the compressed observable `J j₀ e ω`. -/
def largeRhoCompBad (sel : CEH.EigenpairSelection (2 * p.W))
    (sel' : CEH.EigenpairSelection (2 * p.W - 1)) (ε : ℝ) (Es Ms : Finset ℝ) (s' β ε' : ℝ)
    (J : ExteriorSite p i → ℝ → SplitState p i →
      Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ) :
    Set (SplitState p i × PairMatrix p i) :=
  ⋃ j₀ : ExteriorSite p i, ⋃ e ∈ Es, ⋃ μ ∈ Ms,
    {x | x.1 ∈ poleLabelSet ε j₀ e ∧
      ¬ NatWindowGood (compRegF sel ε j₀ e x.1) sel' s' μ β ε' (J j₀ e x.1)
        ((poleIsometry sel j₀ x.1)ᴴ * x.2 * poleIsometry sel j₀ x.1)}

/-- **The joint compressed bad set is measurable** for `ε, s' > 0` and measurable compressed
observables. -/
theorem measurableSet_largeRhoCompBad (sel : CEH.EigenpairSelection (2 * p.W))
    (sel' : CEH.EigenpairSelection (2 * p.W - 1)) {ε : ℝ} (hε : 0 < ε) (Es Ms : Finset ℝ)
    {s' : ℝ} (hs' : 0 < s') (β ε' : ℝ)
    {J : ExteriorSite p i → ℝ → SplitState p i →
      Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ} (hJ : ∀ j₀ e, Measurable (J j₀ e)) :
    MeasurableSet (largeRhoCompBad sel sel' ε Es Ms s' β ε' J) := by
  unfold largeRhoCompBad
  refine MeasurableSet.iUnion fun j₀ => MeasurableSet.biUnion (Es.countable_toSet) fun e _ =>
    MeasurableSet.biUnion (Ms.countable_toSet) fun μ _ => ?_
  exact ((measurableSet_poleLabelSet ε j₀ e).preimage measurable_fst).inter
    (measurableSet_not_compressWindowGood sel j₀ (F := compRegF sel ε j₀ e)
      (measurable_compRegM sel hε j₀ e) (hJ j₀ e) sel' hs' μ β ε')

/-- **The union bound for a section** at a fixed exterior point `ω`: if every compressed window
bad set at a labelled `(j₀, e, μ)` has `ν`-probability at most `t`, the section of
`largeRhoCompBad` has probability at most `|labels| |Es| |Ms| t`. -/
theorem largeRhoCompBad_section_le (ν : Measure (PairMatrix p i))
    (sel : CEH.EigenpairSelection (2 * p.W)) (sel' : CEH.EigenpairSelection (2 * p.W - 1))
    (ε : ℝ) (Es Ms : Finset ℝ) (s' β ε' : ℝ)
    (J : ExteriorSite p i → ℝ → SplitState p i →
      Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ) (om : SplitState p i) (t : ℝ≥0∞)
    (h : ∀ j₀ : ExteriorSite p i, ∀ e ∈ Es, ∀ μ ∈ Ms, om ∈ poleLabelSet ε j₀ e →
      ν {G | ¬ NatWindowGood (compRegF sel ε j₀ e om) sel' s' μ β ε' (J j₀ e om)
        ((poleIsometry sel j₀ om)ᴴ * G * poleIsometry sel j₀ om)} ≤ t) :
    ν (Prod.mk om ⁻¹' largeRhoCompBad sel sel' ε Es Ms s' β ε' J) ≤
      (Fintype.card (ExteriorSite p i) * Es.card * Ms.card : ℝ≥0∞) * t := by
  unfold largeRhoCompBad
  simp only [preimage_iUnion]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  have hj : ∀ j₀ : ExteriorSite p i, ν (⋃ e ∈ Es, ⋃ μ ∈ Ms, Prod.mk om ⁻¹'
      {x : SplitState p i × PairMatrix p i | x.1 ∈ poleLabelSet ε j₀ e ∧
        ¬ NatWindowGood (compRegF sel ε j₀ e x.1) sel' s' μ β ε' (J j₀ e x.1)
          ((poleIsometry sel j₀ x.1)ᴴ * x.2 * poleIsometry sel j₀ x.1)}) ≤
      (Es.card * Ms.card : ℝ≥0∞) * t := by
    intro j₀
    refine (measure_biUnion_finset_le _ _).trans ?_
    have he : ∀ e ∈ Es, ν (⋃ μ ∈ Ms, Prod.mk om ⁻¹'
        {x : SplitState p i × PairMatrix p i | x.1 ∈ poleLabelSet ε j₀ e ∧
          ¬ NatWindowGood (compRegF sel ε j₀ e x.1) sel' s' μ β ε' (J j₀ e x.1)
            ((poleIsometry sel j₀ x.1)ᴴ * x.2 * poleIsometry sel j₀ x.1)}) ≤
        (Ms.card : ℝ≥0∞) * t := by
      intro e he
      refine (measure_biUnion_finset_le _ _).trans ?_
      have hμ : ∀ μ ∈ Ms, ν (Prod.mk om ⁻¹'
          {x : SplitState p i × PairMatrix p i | x.1 ∈ poleLabelSet ε j₀ e ∧
            ¬ NatWindowGood (compRegF sel ε j₀ e x.1) sel' s' μ β ε' (J j₀ e x.1)
              ((poleIsometry sel j₀ x.1)ᴴ * x.2 * poleIsometry sel j₀ x.1)}) ≤ t := by
        intro μ hμ
        by_cases hl : om ∈ poleLabelSet ε j₀ e
        · refine le_trans (measure_mono fun G hG => hG.2) (h j₀ e he μ hμ hl)
        · have : Prod.mk om ⁻¹' {x : SplitState p i × PairMatrix p i |
              x.1 ∈ poleLabelSet ε j₀ e ∧
              ¬ NatWindowGood (compRegF sel ε j₀ e x.1) sel' s' μ β ε' (J j₀ e x.1)
                ((poleIsometry sel j₀ x.1)ᴴ * x.2 * poleIsometry sel j₀ x.1)} = ∅ := by
            ext G; simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
            exact fun hG => hl hG.1
          rw [this, measure_empty]; exact bot_le
      refine (Finset.sum_le_sum hμ).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    refine (Finset.sum_le_sum he).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
  refine (Finset.sum_le_sum fun j₀ _ => hj j₀).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← mul_assoc, ← mul_assoc]

/-- **The sections are small, from the compressed ETH** (`ExternalETH`,
`CompressedGUELawBridgeStatement`, through `gue_not_compressWindowGood_le`).
Constants `A, C, [sLo, sHi], r, v₀` first; then `β₀`; then `β < β₀`, `ε', D > 0`; then `N₀`.
For every `p, i` with `N₀ ≤ 2W - 1`, `s > 0` with `s' = compressVar p s ∈ [sLo, sHi]`, selections,
radius `ε`, grids `Es, Ms`, compressed observables `J` and exterior point `ω` at which every
labelled `(j₀, e, μ)` has the ETH hypotheses (`s'^{-1/2}‖compRegM‖ ≤ C(2W-1)^A`, a root
rectangle of `compRegM` at `μ`, `J j₀ e ω` a Hermitian contraction), the section of
`largeRhoCompBad` under `GUE_{2W}(s/2W)` is at most `|labels| |Es| |Ms| (2W - 1)^{-D}`.
-/
theorem gue_largeRhoCompBad_section_le (inputs : NativeInputs.{0})
    (hAd : GUEWignerFamilyAdapter) (hMDE : MDEBranchIdentification) (hETH : ExternalETH)
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
  obtain ⟨β₀, hβ₀, hβ₀', h⟩ := gue_not_compressWindowGood_le inputs hAd hMDE hETH hComp A C sLo
    sHi r v₀ hsLo hsHi hr hv₀
  refine ⟨β₀, hβ₀, hβ₀', fun β hβ hββ ε' D hε' hD => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h β hβ hββ ε' D hε' hD
  refine ⟨N₀, fun p i hN s hs hsI sel sel' ε Es Ms J om hyp => ?_⟩
  refine largeRhoCompBad_section_le _ sel sel' ε Es Ms _ β ε' J om _ ?_
  intro j₀ e he μ hμ hl
  obtain ⟨hn, hR, hJh, hJn⟩ := hyp j₀ e he μ hμ hl
  have hU := (poleIsometry_spec sel hl.choose hl.choose_spec.1).1
  exact hN₀ p i hN s hs hsI (compRegF sel ε j₀ e om) hn μ hR sel' (J j₀ e om) hJh hJn _ hU

end Bad

end BlockBand.LocalWindow.ProofPartTwo
