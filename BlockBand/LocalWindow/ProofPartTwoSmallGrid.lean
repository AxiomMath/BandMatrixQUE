module

public import BlockBand.LocalWindow.ProofPartTwoPoleMeasurableLargeRho
public import BlockBand.LocalWindow.ProofPartTwoCount
public import BlockBand.LocalWindow.ProofPartTwoFinal
public import BlockBand.LocalWindow.ProofPartTwoFinalGrid

/-!
# The measurable grid bad set of the small-`ρ` branch

The grid deformations and grid observables of the small-`ρ` branch are measurable, and so is the
union of the window bad sets over a finite index set, with a union bound for its sections.

## Main results

* `truncGridK ε e ω` (Hermitian part of `F̂(e) - e`; no exterior eigenvalue near `e`),
  `isHermitian_truncGridK`, `measurable_truncGridK`, `truncGridK_eq` (`= F̂(e) - e` for Hermitian
  `V`);
* `smallGridK ε l e ρ_g ω` for a pole label `l : Option (ExteriorSite)`: `truncGridK` for
  `l = none`, `poleGridK ε j₀ e ρ_g` for `l = some j₀`; `smallLabel ε l e` (`univ`, resp.
  `{H_R Hermitian, j₀ simple, PoleSeparated ε j₀ e}`), `measurableSet_smallLabel`;
* `measurable_spectralFn`: `X ↦ f(X)` is measurable for continuous `f`, hence so is `ω ↦ f(K(ω))`
  for measurable `K` (continuous functional calculus on the closed Hermitian set; the class (b) grid observables);
* `smallPointBad`: at one grid index `(l, e, ρ_g, μ)`, the label event intersected with the window
  ETH bad set (`¬ PairWindowGood`) and the window count bad set of `gue_windowCount_le`;
  `smallBadSet` (finite union over an index set), **`measurableSet_smallBadSet`**;
* **`smallBadSet_section_le`**: if at the exterior point `ω` every index whose label event
  contains `ω` has window-section `≤ a` and count-section `≤ c`, the section of `smallBadSet` is
  at most `|I| (a + c)`.
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

/-!
## The grid deformations
-/

/-- The Hermitian part of `F̂(e) - e` (truncation radius `ε`). -/
def truncGridK (ε e : ℝ) (om : SplitState p i) : PairMatrix p i :=
  (1 / 2 : ℂ) • ((truncF ε om.1 om.2.1 om.2.2 e - (e : ℂ) • 1) +
    (truncF ε om.1 om.2.1 om.2.2 e - (e : ℂ) • 1)ᴴ)

theorem isHermitian_truncGridK (ε e : ℝ) (om : SplitState p i) :
    (truncGridK ε e om).IsHermitian := by
  unfold truncGridK Matrix.IsHermitian
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  congr 1
  simp

theorem measurable_truncGridK {ε : ℝ} (hε : 0 < ε) (e : ℝ) :
    Measurable (truncGridK (p := p) (i := i) ε e) := by
  have h1 : Measurable fun om : SplitState p i =>
      truncF ε om.1 om.2.1 om.2.2 e - (e : ℂ) • (1 : PairMatrix p i) :=
    (measurable_truncF hε e).sub measurable_const
  have hc : Continuous fun X : PairMatrix p i => (1 / 2 : ℂ) • (X + Xᴴ) :=
    (continuous_const_smul (1 / 2 : ℂ)).comp (continuous_id.add continuous_id.matrix_conjTranspose)
  exact hc.measurable.comp h1

/-- For Hermitian `V`, `truncGridK = F̂(e) - e`. -/
theorem truncGridK_eq {ε e : ℝ} {om : SplitState p i} (hV : om.2.2.IsHermitian) :
    truncGridK ε e om = truncF ε om.1 om.2.1 om.2.2 e - (e : ℂ) • 1 := by
  have hX : (truncF ε om.1 om.2.1 om.2.2 e - (e : ℂ) • (1 : PairMatrix p i)).IsHermitian := by
    refine (ProofCertificate.isHermitian_truncF ε om.1 om.2.1 hV e).sub ?_
    rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  unfold truncGridK
  rw [hX.eq, ← two_smul ℂ (truncF ε om.1 om.2.1 om.2.2 e - (e : ℂ) • (1 : PairMatrix p i)),
    smul_smul]
  norm_num

/-- **The small-`ρ` grid deformation at a pole label** `l`: `F̂(e) - e` (Hermitian part) for
`l = none`, `poleGridK ε j₀ e ρ_g` (`= F_reg(e) + ρ_g ww* - e` on the label event) for
`l = some j₀`. -/
def smallGridK (ε : ℝ) : Option (ExteriorSite p i) → ℝ → ℝ → SplitState p i → PairMatrix p i
  | none, e, _, om => truncGridK ε e om
  | some j₀, e, ρg, om => poleGridK ε j₀ e ρg om

theorem isHermitian_smallGridK (ε : ℝ) (l : Option (ExteriorSite p i)) (e ρg : ℝ)
    (om : SplitState p i) : (smallGridK ε l e ρg om).IsHermitian := by
  cases l with
  | none => exact isHermitian_truncGridK ε e om
  | some j₀ => exact isHermitian_poleGridK ε j₀ e ρg om

theorem measurable_smallGridK {ε : ℝ} (hε : 0 < ε) (l : Option (ExteriorSite p i)) (e ρg : ℝ) :
    Measurable (smallGridK (p := p) (i := i) ε l e ρg) := by
  cases l with
  | none => exact measurable_truncGridK hε e
  | some j₀ => exact measurable_poleGridK hε j₀ e ρg

/-- The label event: everything for `l = none`; `{H_R Hermitian, j₀ simple, PoleSeparated ε j₀ e}`
for `l = some j₀`. -/
def smallLabel (ε : ℝ) : Option (ExteriorSite p i) → ℝ → Set (SplitState p i)
  | none, _ => univ
  | some j₀, e => {om | ∃ hH : om.1.IsHermitian, PoleSimple hH j₀ ∧ PoleSeparated ε hH j₀ e}

theorem measurableSet_smallLabel (ε : ℝ) (l : Option (ExteriorSite p i)) (e : ℝ) :
    MeasurableSet (smallLabel (p := p) (i := i) ε l e) := by
  cases l with
  | none => exact MeasurableSet.univ
  | some j₀ => exact measurableSet_poleLabel ε j₀ e

/-!
## Class (b) grid observables are measurable
-/

section SpectralFn

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem spectralFn_eq_cfc (f : ℝ → ℝ) (X : Matrix ι ι ℂ) :
    BlockBand.LocalWindow.spectralFn f X = cfc f X := by
  unfold BlockBand.LocalWindow.spectralFn
  split_ifs with hX
  · exact (hX.cfc_eq f).symm
  · exact (cfc_apply_of_not_predicate _ (fun h => hX h)).symm

/-- **`X ↦ f(X)` is Borel measurable** for continuous `f` (continuous on the closed Hermitian set,
`0` off it). -/
theorem measurable_spectralFn {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable (BlockBand.LocalWindow.spectralFn (ι := ι) f) := by
  have e : BlockBand.LocalWindow.spectralFn (ι := ι) f = fun X => cfc f X :=
    funext (spectralFn_eq_cfc f)
  rw [e]
  have hS : MeasurableSet {H : Matrix ι ι ℂ | H.IsHermitian} :=
    (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
  have hc : Continuous (fun H : {H : Matrix ι ι ℂ // H.IsHermitian} => cfc f H.1) :=
    Continuous.cfc_of_mem_nhdsSet (s := Set.univ) _ (by simp) continuous_subtype_val
      (fun H => H.2.isSelfAdjoint) hf.continuousOn
  refine measurable_of_restrict_of_restrict_compl hS hc.measurable ?_
  have : (({H : Matrix ι ι ℂ | H.IsHermitian}ᶜ).domRestrict fun H => cfc f H) = fun _ => 0 := by
    funext H
    exact cfc_apply_of_not_predicate _ (fun h => H.2 h)
  rw [this]
  exact measurable_const

end SpectralFn

/-!
## The bad set at one grid index and its union
-/

section Bad

variable (sel : CEH.EigenpairSelection (2 * p.W)) (ε₁ s β εw Cc : ℝ)
  (Jg : Option (ExteriorSite p i) → ℝ → ℝ → SplitState p i → PairMatrix p i)

/-- **The bad set at one grid index** `(l, e, ρ_g, μ)`: on the label event,
the window ETH fails for `K_g = smallGridK ε₁ l e ρ_g` and the grid observable `J_g`, or the
window `[μ ± (2W)^{-1+β}]` holds more than `C_c (2W)^β` eigenvalues of `K_g + G`. -/
def smallPointBad (l : Option (ExteriorSite p i)) (e ρg μ : ℝ) :
    Set (SplitState p i × PairMatrix p i) :=
  {x | x.1 ∈ smallLabel ε₁ l e} ∩
    ({x | ¬ PairWindowGood (smallGridK ε₁ l e ρg x.1) (isHermitian_smallGridK ε₁ l e ρg x.1) sel
        s μ β εw (Jg l e ρg x.1) x.2} ∪
      {x | ¬ ∃ hG : x.2.IsHermitian,
        ((Finset.univ.filter fun k => pairEigval sel (smallGridK ε₁ l e ρg x.1 + x.2)
            ((isHermitian_smallGridK ε₁ l e ρg x.1).add hG) k ∈
          Icc (μ - ((2 * p.W : ℕ) : ℝ) ^ (-1 + β)) (μ + ((2 * p.W : ℕ) : ℝ) ^ (-1 + β))).card :
            ℝ) ≤ Cc * ((2 * p.W : ℕ) : ℝ) ^ β})

/-- The union of the bad sets over a finite index set. -/
def smallBadSet (I : Finset (Option (ExteriorSite p i) × ℝ × ℝ × ℝ)) :
    Set (SplitState p i × PairMatrix p i) :=
  ⋃ q ∈ I, smallPointBad sel ε₁ s β εw Cc Jg q.1 q.2.1 q.2.2.1 q.2.2.2

variable {sel ε₁ s β εw Cc Jg}

theorem measurableSet_smallPointBad (hε₁ : 0 < ε₁) (hs : 0 < s)
    (hJm : ∀ l e ρg, Measurable (Jg l e ρg)) (l : Option (ExteriorSite p i)) (e ρg μ : ℝ) :
    MeasurableSet (smallPointBad sel ε₁ s β εw Cc Jg l e ρg μ) := by
  refine ((measurableSet_smallLabel ε₁ l e).preimage measurable_fst).inter
    (MeasurableSet.union ?_ ?_)
  · exact measurableSet_not_pairWindowGood (measurable_smallGridK hε₁ l e ρg)
      (isHermitian_smallGridK ε₁ l e ρg) (hJm l e ρg) sel hs μ β εw
  · exact measurableSet_not_windowCount_le (measurable_smallGridK hε₁ l e ρg)
      (isHermitian_smallGridK ε₁ l e ρg) sel _ _ _

/-- **The grid bad set is measurable**: only `smallGridK`, the label events and the measurable
observables `J_g` enter. -/
theorem measurableSet_smallBadSet (hε₁ : 0 < ε₁) (hs : 0 < s)
    (hJm : ∀ l e ρg, Measurable (Jg l e ρg)) (I : Finset (Option (ExteriorSite p i) × ℝ × ℝ × ℝ)) :
    MeasurableSet (smallBadSet sel ε₁ s β εw Cc Jg I) :=
  Finset.measurableSet_biUnion I fun _ _ => measurableSet_smallPointBad hε₁ hs hJm _ _ _ _

/-- **The section of the grid bad set** at an exterior point `ω`: if every index whose label event
contains `ω` has window-ETH section `≤ a` and count section `≤ c`, the section is at most
`|I| (a + c)`. -/
theorem smallBadSet_section_le (ν : Measure (PairMatrix p i))
    (I : Finset (Option (ExteriorSite p i) × ℝ × ℝ × ℝ)) (om : SplitState p i) {a c : ℝ≥0∞}
    (hwin : ∀ q ∈ I, om ∈ smallLabel ε₁ q.1 q.2.1 →
      ν {G | ¬ PairWindowGood (smallGridK ε₁ q.1 q.2.1 q.2.2.1 om)
        (isHermitian_smallGridK ε₁ q.1 q.2.1 q.2.2.1 om) sel s q.2.2.2 β εw
          (Jg q.1 q.2.1 q.2.2.1 om) G} ≤ a)
    (hcnt : ∀ q ∈ I, om ∈ smallLabel ε₁ q.1 q.2.1 →
      ν {G | ¬ ∃ hG : G.IsHermitian,
        ((Finset.univ.filter fun k => pairEigval sel (smallGridK ε₁ q.1 q.2.1 q.2.2.1 om + G)
            ((isHermitian_smallGridK ε₁ q.1 q.2.1 q.2.2.1 om).add hG) k ∈
          Icc (q.2.2.2 - ((2 * p.W : ℕ) : ℝ) ^ (-1 + β))
            (q.2.2.2 + ((2 * p.W : ℕ) : ℝ) ^ (-1 + β))).card : ℝ) ≤
          Cc * ((2 * p.W : ℕ) : ℝ) ^ β} ≤ c) :
    ν (Prod.mk om ⁻¹' smallBadSet sel ε₁ s β εw Cc Jg I) ≤ I.card * (a + c) := by
  unfold smallBadSet
  rw [Set.preimage_iUnion₂]
  refine (measure_biUnion_finset_le I _).trans ?_
  have hpt : ∀ q ∈ I, ν (Prod.mk om ⁻¹'
      smallPointBad sel ε₁ s β εw Cc Jg q.1 q.2.1 q.2.2.1 q.2.2.2) ≤ a + c := by
    intro q hq
    by_cases hl : om ∈ smallLabel ε₁ q.1 q.2.1
    · refine (measure_mono ?_).trans ((measure_union_le _ _).trans
        (add_le_add (hwin q hq hl) (hcnt q hq hl)))
      intro G hG
      exact hG.2
    · have : Prod.mk om ⁻¹' smallPointBad sel ε₁ s β εw Cc Jg q.1 q.2.1 q.2.2.1 q.2.2.2 = ∅ := by
        ext G
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        exact fun h => hl h.1
      rw [this, measure_empty]
      exact bot_le
  calc ∑ q ∈ I, ν (Prod.mk om ⁻¹' smallPointBad sel ε₁ s β εw Cc Jg q.1 q.2.1 q.2.2.1 q.2.2.2)
      ≤ ∑ _q ∈ I, (a + c) := Finset.sum_le_sum hpt
    _ = I.card * (a + c) := by rw [Finset.sum_const, nsmul_eq_mul]

end Bad

end BlockBand.LocalWindow.ProofPartTwo
