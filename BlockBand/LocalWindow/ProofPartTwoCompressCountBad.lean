module

public import BlockBand.LocalWindow.ProofPartTwoCompressCount

/-!
# The measurable compressed window-count bad set

The large-`ρ` transfer `largeRho_actual_transfer` consumes the hypothesis `hcount`: at most
`n_S` eigenvalues of the compressed matrix `U(ω)*(F_reg(e) - e + G)U(ω)` lie in
`[μ - h_c, μ + h_c]`, `h_c = (2W - 1)^{-1+β}`. This file keeps the failure of that bound in a
measurable joint bad set and bounds its sections by the full-matrix count of
`gue_windowCount_le` through Cauchy interlacing (`natCount_le_two_windows_add_one`).

## Main results

* `NatCountGood F sel' a b c X`: `X` Hermitian and at most `c` selected eigenvalues of `F + X`
  in `[a, b]`; **`measurableSet_not_natCountGood_comp`**.
* **`largeRhoCountBad`**: `⋃_{j₀} ⋃_{e ∈ Es} ⋃_{μ ∈ Ms} {(ω, G) | ω ∈ poleLabelSet ε j₀ e,
  ¬ NatCountGood (compRegF ω) sel' (μ - h_c) (μ + h_c) c (U(ω)* G U(ω))}`;
  **`measurableSet_largeRhoCountBad`**.
* **`hcount_of_not_mem_largeRhoCountBad`**: off the bad set, the hypothesis `hcount` of
  `largeRho_actual_transfer` holds with `n_S = c`.
* `poleCompress_regK_rankOne_eq`: on the label event, `U*(F_reg(e) + ρww* - e)U = compRegM` for
  every `ρ` (`U*w = 0`).
* `natCountBad_subset_pairCountBad`: deterministic inclusion of the compressed bad event at
  threshold `2c + 1` in the union of two full-window bad events of a Hermitian `K` with
  `U*KU = compRegM`.
* `largeRhoCountBad_section_le`: the union bound at a fixed exterior point.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open MeasureTheory Matrix Set Filter Topology
open BlockBand.Coarea BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.LawBridge BlockBand.LocalWindow.ProofETH
open BlockBand.LocalWindow.ProofCount
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-!
## The count event
-/

section NatCount

variable {N : ℕ}

/-- **The count bound**: `X` is Hermitian and at most `c` selected eigenvalues of the
deformed matrix `F + X` lie in `[a, b]`. -/
def NatCountGood (F : CEH.SourceHermitian N) (sel : CEH.EigenpairSelection N) (a b c : ℝ)
    (X : CEH.SourceMatrix N) : Prop :=
  ∃ hX : X.IsHermitian,
    ((Finset.univ.filter fun k => sel.eigenvalue (natDeformed F X hX) k ∈ Icc a b).card : ℝ) ≤ c

variable {Y : Type*} [MeasurableSpace Y]

/-- **The count bad set is measurable along measurable data**: for measurable
`y ↦ F(y)` (Hermitian) and `y ↦ X(y)`, `{y | ¬ NatCountGood (F y) sel a b c (X y)}` is
measurable. -/
theorem measurableSet_not_natCountGood_comp {F : Y → CEH.SourceHermitian N}
    (hF : Measurable fun y => (F y).1) {X : Y → Matrix (Fin N) (Fin N) ℂ} (hX : Measurable X)
    (sel : CEH.EigenpairSelection N) (a b c : ℝ) :
    MeasurableSet {y | ¬ NatCountGood (F y) sel a b c (X y)} := by
  have hD := measurable_natDeformedH_comp hF hX
  have e : {y | ¬ NatCountGood (F y) sel a b c (X y)} =
      ({y | (X y).IsHermitian} ∩ {y | (∑ k : Fin N,
        if sel.eigenvalue (natDeformedH (F y).1 (X y)) k ∈ Icc a b then (1 : ℝ) else 0) ≤ c})ᶜ := by
    ext y
    simp only [mem_ofPred_eq, mem_compl_iff, mem_inter_iff, NatCountGood]
    constructor
    · intro hno ⟨hXh, hc⟩
      refine hno ⟨hXh, ?_⟩
      rw [← natDeformedH_eq (F y) hXh, Finset.card_filter]
      push_cast
      exact hc
    · rintro hno ⟨hXh, hc⟩
      refine hno ⟨hXh, ?_⟩
      rw [← natDeformedH_eq (F y) hXh, Finset.card_filter] at hc
      push_cast at hc
      exact hc
  rw [e]
  have hXH : MeasurableSet {y | (X y).IsHermitian} :=
    (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet.preimage hX
  refine MeasurableSet.compl (hXH.inter ?_)
  refine measurableSet_le (Finset.measurable_sum _ fun k _ => ?_) measurable_const
  exact Measurable.ite (measurableSet_Icc.preimage ((sel.measurable_eigenvalue k).comp hD))
    measurable_const measurable_const

end NatCount

variable {p : Parameters} {i : ZMod p.n}

attribute [local instance] pairSite_nonempty

/-!
## The joint compressed count bad set
-/

section Bad

/-- **The joint compressed window-count bad set of the large-`ρ` branch**: over all pole labels
`j₀`, grid energies `e ∈ Es` and window centres `μ ∈ Ms`, the points `(ω, G)` with `ω` in the
label event of `(j₀, e)` and more than `c` eigenvalues of the compressed matrix
`compRegF ω + U(ω)* G U(ω)` in `[μ - h_c, μ + h_c]` (`h_c = compressRadius p β`), or
`U(ω)* G U(ω)` not Hermitian. -/
def largeRhoCountBad (sel : CEH.EigenpairSelection (2 * p.W))
    (sel' : CEH.EigenpairSelection (2 * p.W - 1)) (ε : ℝ) (Es Ms : Finset ℝ) (β c : ℝ) :
    Set (SplitState p i × PairMatrix p i) :=
  ⋃ j₀ : ExteriorSite p i, ⋃ e ∈ Es, ⋃ μ ∈ Ms,
    {x | x.1 ∈ poleLabelSet ε j₀ e ∧
      ¬ NatCountGood (compRegF sel ε j₀ e x.1) sel' (μ - compressRadius p β)
        (μ + compressRadius p β) c ((poleIsometry sel j₀ x.1)ᴴ * x.2 * poleIsometry sel j₀ x.1)}

/-- **The joint compressed count bad set is measurable** (`ε > 0`). -/
theorem measurableSet_largeRhoCountBad (sel : CEH.EigenpairSelection (2 * p.W))
    (sel' : CEH.EigenpairSelection (2 * p.W - 1)) {ε : ℝ} (hε : 0 < ε) (Es Ms : Finset ℝ)
    (β c : ℝ) : MeasurableSet (largeRhoCountBad (p := p) (i := i) sel sel' ε Es Ms β c) := by
  unfold largeRhoCountBad
  refine MeasurableSet.iUnion fun j₀ => MeasurableSet.biUnion (Es.countable_toSet) fun e _ =>
    MeasurableSet.biUnion (Ms.countable_toSet) fun μ _ => ?_
  have hU : Measurable fun x : SplitState p i × PairMatrix p i => poleIsometry sel j₀ x.1 :=
    (measurable_poleIsometry sel j₀).comp measurable_fst
  have hX : Measurable fun x : SplitState p i × PairMatrix p i =>
      (poleIsometry sel j₀ x.1)ᴴ * x.2 * poleIsometry sel j₀ x.1 :=
    ProofCount.measurable_matrix_mul'
      (ProofCount.measurable_matrix_mul' (measurable_conjTranspose' hU) measurable_snd) hU
  have hF : Measurable fun x : SplitState p i × PairMatrix p i =>
      (compRegF sel ε j₀ e x.1).1 := (measurable_compRegM sel hε j₀ e).comp measurable_fst
  have h1 : MeasurableSet {x : SplitState p i × PairMatrix p i | x.1 ∈ poleLabelSet ε j₀ e} :=
    (measurableSet_poleLabelSet ε j₀ e).preimage measurable_fst
  have h2 : MeasurableSet {x : SplitState p i × PairMatrix p i |
      ¬ NatCountGood (compRegF sel ε j₀ e x.1) sel' (μ - compressRadius p β)
        (μ + compressRadius p β) c ((poleIsometry sel j₀ x.1)ᴴ * x.2 * poleIsometry sel j₀ x.1)} :=
    by
      have h := measurableSet_not_natCountGood_comp
        (F := fun x : SplitState p i × PairMatrix p i => compRegF sel ε j₀ e x.1) hF hX sel'
        (μ - compressRadius p β) (μ + compressRadius p β) c
      exact h
  exact h1.inter h2

/-- **Off the bad set, `hcount` holds** (the hypothesis `hcount` of `largeRho_actual_transfer`
with `n_S = c`): if `(ω, G) ∉ largeRhoCountBad`, `ω` is in the label event of `(j₀, e)`,
`e ∈ Es` and `μ ∈ Ms`, then for every Hermiticity proof of `U(ω)* G U(ω)` at most `c` compressed
eigenvalues lie in `[μ - h_c, μ + h_c]`. -/
theorem hcount_of_not_mem_largeRhoCountBad (sel : CEH.EigenpairSelection (2 * p.W))
    (sel' : CEH.EigenpairSelection (2 * p.W - 1)) {ε : ℝ} {Es Ms : Finset ℝ} {β c : ℝ}
    {om : SplitState p i} {G : PairMatrix p i}
    (hx : (om, G) ∉ largeRhoCountBad sel sel' ε Es Ms β c) {j₀ : ExteriorSite p i} {e μ : ℝ}
    (he : e ∈ Es) (hμ : μ ∈ Ms) (hl : om ∈ poleLabelSet ε j₀ e) :
    ∀ hX : ((poleIsometry sel j₀ om)ᴴ * G * poleIsometry sel j₀ om).IsHermitian,
      ((Finset.univ.filter fun k => sel'.eigenvalue (natDeformed (compRegF sel ε j₀ e om)
        ((poleIsometry sel j₀ om)ᴴ * G * poleIsometry sel j₀ om) hX) k ∈
          Icc (μ - compressRadius p β) (μ + compressRadius p β)).card : ℝ) ≤ c := by
  intro hX
  by_contra hc
  apply hx
  refine mem_iUnion.mpr ⟨j₀, mem_iUnion₂.mpr ⟨e, he, mem_iUnion₂.mpr ⟨μ, hμ, hl, ?_⟩⟩⟩
  rintro ⟨hX', h'⟩
  exact hc h'

/-- **The rank-one part is invisible after compression**: on the label event of
`(j₀, e)` with `V` Hermitian, for every real `ρ`,
`U(ω)*(F_reg(e) + ρww* - e)U(ω) = compRegM sel ε j₀ e ω` (`U*w = 0`). -/
theorem poleCompress_regK_rankOne_eq (sel : CEH.EigenpairSelection (2 * p.W)) (ε : ℝ)
    {om : SplitState p i} (hH : om.1.IsHermitian) (hV : om.2.2.IsHermitian)
    {j₀ : ExteriorSite p i} (hs : PoleSimple hH j₀) {e : ℝ} (hsep : PoleSeparated ε hH j₀ e)
    (ρ : ℝ) :
    (poleIsometry sel j₀ om)ᴴ * (regF hH j₀ om.2.1 om.2.2 e +
        (ρ : ℂ) • vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) -
          (e : ℂ) • (1 : PairMatrix p i)) * poleIsometry sel j₀ om =
      compRegM sel ε j₀ e om := by
  rw [compRegM_eq sel ε hH hV hs hsep]
  have hUw := (poleIsometry_spec sel hH hs).2.1
  have h0 : (poleIsometry sel j₀ om)ᴴ *
      ((ρ : ℂ) • vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1))) *
        poleIsometry sel j₀ om = 0 := by
    rw [Matrix.mul_smul, Matrix.smul_mul, ProofCertificate.mul_vecMulVec_mul, hUw]
    ext a b
    simp [vecMulVec]
  rw [show regF hH j₀ om.2.1 om.2.2 e +
      (ρ : ℂ) • vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) -
        (e : ℂ) • (1 : PairMatrix p i) =
      (regF hH j₀ om.2.1 om.2.2 e - (e : ℂ) • (1 : PairMatrix p i)) +
        (ρ : ℂ) • vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) by abel,
    Matrix.mul_add, Matrix.add_mul, h0, add_zero]

/-- **The compressed bad event lies in two full-window bad events** (Cauchy interlacing,
`natCount_le_two_windows_add_one`): at a point `ω` of the label event of `(j₀, e)`, for a
Hermitian `K` with `U(ω)*KU(ω) = compRegM sel ε j₀ e ω`, `0 ≤ β ≤ 1`, every centre `μ` and every
`c`, the compressed bad event at threshold `2c + 1` is contained in the union of the full bad
events of `gue_windowCount_le` (threshold `c`, radius `h_f = (2W)^{-1+β}`) at the centres
`μ - h_f` and `μ + h_f`. -/
theorem natCountBad_subset_pairCountBad (sel : CEH.EigenpairSelection (2 * p.W))
    (sel' : CEH.EigenpairSelection (2 * p.W - 1)) (ε : ℝ) {j₀ : ExteriorSite p i} {e : ℝ}
    {om : SplitState p i} (hl : om ∈ poleLabelSet ε j₀ e) {K : PairMatrix p i}
    (hK : K.IsHermitian)
    (hKU : (poleIsometry sel j₀ om)ᴴ * K * poleIsometry sel j₀ om = compRegM sel ε j₀ e om)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (μ c : ℝ) :
    {G : PairMatrix p i | ¬ NatCountGood (compRegF sel ε j₀ e om) sel' (μ - compressRadius p β)
        (μ + compressRadius p β) (2 * c + 1)
        ((poleIsometry sel j₀ om)ᴴ * G * poleIsometry sel j₀ om)} ⊆
      {G | ¬ ∃ hG : G.IsHermitian,
          ((Finset.univ.filter fun k => pairEigval sel (K + G) (hK.add hG) k ∈
              Icc ((μ - windowRadius p β) - windowRadius p β)
                ((μ - windowRadius p β) + windowRadius p β)).card : ℝ) ≤ c} ∪
        {G | ¬ ∃ hG : G.IsHermitian,
          ((Finset.univ.filter fun k => pairEigval sel (K + G) (hK.add hG) k ∈
              Icc ((μ + windowRadius p β) - windowRadius p β)
                ((μ + windowRadius p β) + windowRadius p β)).card : ℝ) ≤ c} := by
  intro G hG
  by_contra hno
  simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hno
  obtain ⟨⟨hG1, h1⟩, ⟨hG2, h2⟩⟩ := hno
  set U := poleIsometry sel j₀ om with hUdef
  have hUU : Uᴴ * U = 1 := (poleIsometry_spec sel hl.choose hl.choose_spec.1).1
  have hX : (Uᴴ * G * U).IsHermitian := isHermitian_conjTranspose_mul_mul U hG1
  apply hG
  refine ⟨hX, ?_⟩
  have hY : (natDeformed (compRegF sel ε j₀ e om) (Uᴴ * G * U) hX).1 = Uᴴ * (K + G) * U := by
    show compRegM sel ε j₀ e om + Uᴴ * G * U = _
    rw [← hKU, Matrix.mul_add, Matrix.add_mul]
  have h := natCount_le_two_windows_add_one sel sel' hUU (hK.add hG1) _ hY hβ hβ1 μ
  have h' : ((Finset.univ.filter fun k => sel'.eigenvalue
      (natDeformed (compRegF sel ε j₀ e om) (Uᴴ * G * U) hX) k ∈
        Icc (μ - compressRadius p β) (μ + compressRadius p β)).card : ℝ) ≤
      ((Finset.univ.filter fun j => pairEigval sel (K + G) (hK.add hG1) j ∈
          Icc ((μ - windowRadius p β) - windowRadius p β)
            ((μ - windowRadius p β) + windowRadius p β)).card : ℝ) +
        ((Finset.univ.filter fun j => pairEigval sel (K + G) (hK.add hG1) j ∈
          Icc ((μ + windowRadius p β) - windowRadius p β)
            ((μ + windowRadius p β) + windowRadius p β)).card : ℝ) + 1 := by
    exact_mod_cast h
  linarith

/-- **The union bound for a section** at a fixed exterior point `ω`: if every compressed count
bad set at a labelled `(j₀, e, μ)` has `ν`-probability at most `t`, the section of
`largeRhoCountBad` has probability at most `|labels| |Es| |Ms| t`. -/
theorem largeRhoCountBad_section_le (ν : Measure (PairMatrix p i))
    (sel : CEH.EigenpairSelection (2 * p.W)) (sel' : CEH.EigenpairSelection (2 * p.W - 1))
    (ε : ℝ) (Es Ms : Finset ℝ) (β c : ℝ) (om : SplitState p i) (t : ℝ≥0∞)
    (h : ∀ j₀ : ExteriorSite p i, ∀ e ∈ Es, ∀ μ ∈ Ms, om ∈ poleLabelSet ε j₀ e →
      ν {G | ¬ NatCountGood (compRegF sel ε j₀ e om) sel' (μ - compressRadius p β)
        (μ + compressRadius p β) c ((poleIsometry sel j₀ om)ᴴ * G * poleIsometry sel j₀ om)} ≤
        t) :
    ν (Prod.mk om ⁻¹' largeRhoCountBad sel sel' ε Es Ms β c) ≤
      (Fintype.card (ExteriorSite p i) * Es.card * Ms.card : ℝ≥0∞) * t := by
  unfold largeRhoCountBad
  simp only [preimage_iUnion]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  have hj : ∀ j₀ : ExteriorSite p i, ν (⋃ e ∈ Es, ⋃ μ ∈ Ms, Prod.mk om ⁻¹'
      {x : SplitState p i × PairMatrix p i | x.1 ∈ poleLabelSet ε j₀ e ∧
        ¬ NatCountGood (compRegF sel ε j₀ e x.1) sel' (μ - compressRadius p β)
          (μ + compressRadius p β) c
          ((poleIsometry sel j₀ x.1)ᴴ * x.2 * poleIsometry sel j₀ x.1)}) ≤
      (Es.card * Ms.card : ℝ≥0∞) * t := by
    intro j₀
    refine (measure_biUnion_finset_le _ _).trans ?_
    have he : ∀ e ∈ Es, ν (⋃ μ ∈ Ms, Prod.mk om ⁻¹'
        {x : SplitState p i × PairMatrix p i | x.1 ∈ poleLabelSet ε j₀ e ∧
          ¬ NatCountGood (compRegF sel ε j₀ e x.1) sel' (μ - compressRadius p β)
            (μ + compressRadius p β) c
            ((poleIsometry sel j₀ x.1)ᴴ * x.2 * poleIsometry sel j₀ x.1)}) ≤
        (Ms.card : ℝ≥0∞) * t := by
      intro e he
      refine (measure_biUnion_finset_le _ _).trans ?_
      have hμ : ∀ μ ∈ Ms, ν (Prod.mk om ⁻¹'
          {x : SplitState p i × PairMatrix p i | x.1 ∈ poleLabelSet ε j₀ e ∧
            ¬ NatCountGood (compRegF sel ε j₀ e x.1) sel' (μ - compressRadius p β)
              (μ + compressRadius p β) c
              ((poleIsometry sel j₀ x.1)ᴴ * x.2 * poleIsometry sel j₀ x.1)}) ≤ t := by
        intro μ hμ
        by_cases hl : om ∈ poleLabelSet ε j₀ e
        · exact le_trans (measure_mono fun G hG => hG.2) (h j₀ e he μ hμ hl)
        · have : Prod.mk om ⁻¹' {x : SplitState p i × PairMatrix p i |
              x.1 ∈ poleLabelSet ε j₀ e ∧
              ¬ NatCountGood (compRegF sel ε j₀ e x.1) sel' (μ - compressRadius p β)
                (μ + compressRadius p β) c
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

/-- Fixed `A, C`, `sLo > 0`, `Λ`, `r > 0`, `v₀ > 0` first; then
`0 < β < 1` and `D > 0`; then `N₀` and `C_c > 0`.
Uniformly in `p, i` with `2W ≥ N₀`, `s ≥ sLo`,
eigenpair selections `sel, sel'`, radius `ε`, grids `Es, Ms` and exterior points `ω` at which
every labelled `(j₀, e)` (`e ∈ Es`, `ω ∈ poleLabelSet ε j₀ e`) has a Hermitian full deformation
`K` with `U(ω)*KU(ω) = compRegM sel ε j₀ e ω` (e.g.
`K = F_reg(e) + ρww* - e`,
`poleCompress_regK_rankOne_eq`), `s^{-1/2}‖K‖ ≤ C(2W)^A` and, for every `μ ∈ Ms`, `|μ| ≤ Λ` and
`PairRootRectangle K s μ r v₀`: under `G ~ GUE_{2W}(s/2W)` the section of
`largeRhoCountBad sel sel' ε Es Ms β (C_c (2W)^β + 1)` has probability at most
`|labels| |Es| |Ms| · 4 (2W)^{-D}`.
-/
theorem gue_largeRhoCountBad_section_le (hBridge : PairGUELawBridgeStatement)
    (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification) (A C sLo Λ r v₀ : ℝ)
    (hsLo : 0 < sLo) (hr : 0 < r) (hv₀ : 0 < v₀) :
    ∀ β : ℝ, 0 < β → β < 1 → ∀ D : ℝ, 0 < D →
      ∃ (N₀ : ℕ) (Cc : ℝ), 0 < Cc ∧ ∀ (p : Parameters) (i : ZMod p.n), N₀ ≤ 2 * p.W →
        ∀ s : ℝ, sLo ≤ s →
        ∀ (sel : CEH.EigenpairSelection (2 * p.W)) (sel' : CEH.EigenpairSelection (2 * p.W - 1))
          (ε : ℝ) (Es Ms : Finset ℝ) (om : SplitState p i),
          (∀ j₀ : ExteriorSite p i, ∀ e ∈ Es, om ∈ poleLabelSet ε j₀ e →
            ∃ K : PairMatrix p i, K.IsHermitian ∧
              (poleIsometry sel j₀ om)ᴴ * K * poleIsometry sel j₀ om = compRegM sel ε j₀ e om ∧
              (Real.sqrt s)⁻¹ * ‖K‖ ≤ C * ((2 * p.W : ℕ) : ℝ) ^ A ∧
              ∀ μ ∈ Ms, |μ| ≤ Λ ∧ PairRootRectangle K s μ r v₀) →
          gueMeasure (PairSite p i) (pairTime p s)
              (Prod.mk om ⁻¹' largeRhoCountBad sel sel' ε Es Ms β
                (Cc * ((2 * p.W : ℕ) : ℝ) ^ β + 1)) ≤
            (Fintype.card (ExteriorSite p i) * Es.card * Ms.card : ℝ≥0∞) *
              (4 * ENNReal.ofReal (((2 * p.W : ℕ) : ℝ) ^ (-D))) := by
  intro β hβ hβ1 D hD
  obtain ⟨N₁, Cc₁, hCc₁, h⟩ := gue_windowCount_le hBridge hELG hMDE A C sLo (Λ + 1) (r / 2) v₀
    hsLo (half_pos hr) hv₀ β hβ hβ1.le D hD
  have e1 := eventually_const_mul_rpow_le (2 / r) (-1 + β) (by linarith)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((eventually_ge_atTop N₁).and
    ((eventually_ge_atTop 1).and e1))
  refine ⟨N₀, 2 * Cc₁, by positivity, fun p i hN s hs sel sel' ε Es Ms om hyp => ?_⟩
  obtain ⟨hN1, hd1, hsmall⟩ := hN₀ (2 * p.W) hN
  set d : ℝ := ((2 * p.W : ℕ) : ℝ) with hd
  have hd1' : (1 : ℝ) ≤ d := by rw [hd]; exact_mod_cast hd1
  have hf0 : 0 ≤ windowRadius p β := Real.rpow_nonneg (by linarith) _
  have hf1 : windowRadius p β ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hd1' (by linarith)
  have hfr : windowRadius p β ≤ r / 2 := by
    have : 2 / r * windowRadius p β ≤ 1 := hsmall
    rw [div_mul_eq_mul_div, div_le_one hr] at this
    linarith
  rw [show 2 * Cc₁ * d ^ β + 1 = 2 * (Cc₁ * d ^ β) + 1 by ring]
  refine largeRhoCountBad_section_le _ sel sel' ε Es Ms β _ om _ ?_
  intro j₀ e he μ hμ hl
  obtain ⟨K, hK, hKU, hKn, hR⟩ := hyp j₀ e he hl
  obtain ⟨hμΛ, hRμ⟩ := hR μ hμ
  have hsub := natCountBad_subset_pairCountBad sel sel' ε hl hK hKU hβ.le hβ1.le μ (Cc₁ * d ^ β)
  have hshift : ∀ c₀ : ℝ, |c₀ - μ| ≤ windowRadius p β →
      gueMeasure (PairSite p i) (pairTime p s)
          {G | ¬ ∃ hG : G.IsHermitian,
            ((Finset.univ.filter fun k => pairEigval sel (K + G) (hK.add hG) k ∈
                Icc (c₀ - windowRadius p β) (c₀ + windowRadius p β)).card : ℝ) ≤
              Cc₁ * d ^ β} ≤ 2 * ENNReal.ofReal (d ^ (-D)) := by
    intro c₀ hc₀
    have hc₀Λ : |c₀| ≤ Λ + 1 := by
      calc |c₀| = |(c₀ - μ) + μ| := by ring_nf
        _ ≤ |c₀ - μ| + |μ| := abs_add_le _ _
        _ ≤ 1 + Λ := add_le_add (hc₀.trans hf1) hμΛ
        _ = Λ + 1 := by ring
    exact h p i hN1 s hs K hK hKn c₀ hc₀Λ (pairRootRectangle_shift_half hRμ (hc₀.trans hfr)) sel
  have hm1 := hshift (μ - windowRadius p β) (by
    rw [show μ - windowRadius p β - μ = -windowRadius p β by ring, abs_neg, abs_of_nonneg hf0])
  have hm2 := hshift (μ + windowRadius p β) (by
    rw [show μ + windowRadius p β - μ = windowRadius p β by ring, abs_of_nonneg hf0])
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ 2 * ENNReal.ofReal (d ^ (-D)) + 2 * ENNReal.ofReal (d ^ (-D)) := add_le_add hm1 hm2
    _ = 4 * ENNReal.ofReal (d ^ (-D)) := by rw [← add_mul]; norm_num

end Bad

end BlockBand.LocalWindow.ProofPartTwo
