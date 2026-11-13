module

public import BlockBand.Internal.Contracts.CoareaPalm
public import BlockBand.Internal.Contracts.Inputs
public import BlockBand.Coarea.GUELaw
public import BlockBand.Coarea.ContractClauses
public import BlockBand.Palm.MomentFlow.LocalScaling

/-!
# The pair `GUE` law

The scaled source GUE law `√s · gueSourceLaw (2W)`, reindexed to the pair, is
`GUE_{2W}(s/(2W))` on the pair matrices.

*Measure.* `gueSourceLaw (2W) = GUE_{2W}(1/(2W))` on `CEH.SourceHermitian (2W)` and
`gueMeasure (PairSite p i) (pairTime p s) = GUE_{PairSite}(s/(2W))`. *Domain:* every parameter
set `p`, pair `i`, and `s > 0`. Exact identity of measures at fixed finite size; no norm, limit
or uniformity statement.

## Main results

* **`pairGUELawBridge_holds : PairGUELawBridgeStatement`**, unconditional. Proof:
  `pairSample = reindex e⁻¹ e⁻¹ ∘ (√s • ·.1)`; `map_gueSourceLaw_smul`
  gives
  `(gueSourceLaw (2W)).map (√s • ·.1) = gueMeasure (Fin (2W)) (s/(2W))`, and
  `gueMeasure_map_reindex` transports it to `PairSite p i`.
* `gueMeasure_pair_apply`: the set form, for measurable sets of pair matrices.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.LawBridge

open MeasureTheory Matrix BlockBand.Model.Construction BlockBand.QUE.Fourier
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs BlockBand.External
open BlockBand.SourceProcess

variable (p : Parameters) (i : ZMod p.n)

/-- The coordinate equivalence `PairSite p i ≃ Fin (2W)`. -/
def pairEquiv : PairSite p i ≃ Fin (2 * p.W) :=
  (Fintype.equivFin _).trans (finCongr (BlockBand.Coarea.ContractClauses.card_pairSite p i))

/-- The CEH sample transported to the pair: `W ↦ reindex e⁻¹ e⁻¹ (√s W)`. -/
def pairSample (s : ℝ) (W : CEH.SourceHermitian (2 * p.W)) : PairMatrix p i :=
  reindex (pairEquiv p i).symm (pairEquiv p i).symm (((Real.sqrt s : ℝ) : ℂ) • W.1)

/-- **The pair `GUE` law bridge**: for every parameter set, pair and `s > 0`,
`GUE_{2W}(s/2W)` on the pair is the image of `gueSourceLaw (2W)` under `pairSample`.

With both on one branch the
two statements should be identified by `rfl` (they differ only in the namespaces of `pairSample`
and `pairEquiv`, and in the `card_pairSite` proof term inside `pairEquiv`).
-/
def PairGUELawBridgeStatement : Prop :=
  ∀ (p : Parameters) (i : ZMod p.n) (s : ℝ), 0 < s →
    gueMeasure (PairSite p i) (pairTime p s) = (gueSourceLaw (2 * p.W)).map (pairSample p i s)

theorem measurable_reindex_pair :
    Measurable (reindex (pairEquiv p i).symm (pairEquiv p i).symm :
      Matrix (Fin (2 * p.W)) (Fin (2 * p.W)) ℂ → PairMatrix p i) :=
  Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply

theorem measurable_pairSample (s : ℝ) : Measurable (pairSample p i s) :=
  (measurable_reindex_pair p i).comp
    ((BlockBand.Palm.MomentFlow.measurable_matrix_const_smul _).comp measurable_subtype_coe)

/-- **The pair `GUE` law bridge** `PairGUELawBridgeStatement`, with no hypothesis. -/
theorem pairGUELawBridge_holds : PairGUELawBridgeStatement := by
  intro p i s hs
  have hm : Measurable (fun W : CEH.SourceHermitian (2 * p.W) => ((Real.sqrt s : ℝ) : ℂ) • W.1) :=
    (BlockBand.Palm.MomentFlow.measurable_matrix_const_smul _).comp measurable_subtype_coe
  have e : pairSample p i s = reindex (pairEquiv p i).symm (pairEquiv p i).symm ∘
      (fun W : CEH.SourceHermitian (2 * p.W) => ((Real.sqrt s : ℝ) : ℂ) • W.1) := rfl
  rw [e, ← Measure.map_map (measurable_reindex_pair p i) hm,
    BlockBand.Palm.MomentFlow.map_gueSourceLaw_smul hs.le,
    BlockBand.Coarea.GUELaw.gueMeasure_map_reindex]
  congr 1
  unfold pairTime
  push_cast
  rfl

/-- Set form of the pair law: for a measurable set `S` of pair matrices,
`GUE_{2W}(s/2W)(S) = gueSourceLaw (2W) {W | pairSample p i s W ∈ S}`. -/
theorem gueMeasure_pair_apply {s : ℝ} (hs : 0 < s) {S : Set (PairMatrix p i)}
    (hS : MeasurableSet S) :
    gueMeasure (PairSite p i) (pairTime p s) S =
      gueSourceLaw (2 * p.W) {W | pairSample p i s W ∈ S} := by
  rw [pairGUELawBridge_holds p i s hs, Measure.map_apply (measurable_pairSample p i s) hS]
  rfl

end BlockBand.Coarea.LawBridge
