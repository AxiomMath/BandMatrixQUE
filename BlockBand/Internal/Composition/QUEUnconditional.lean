module

public import BlockBand.QUE.GUEInputs.QUE
public import BlockBand.Native.PSSS.SourceContract
public import BlockBand.Native.CEH.Deterministic.Fields
public import BlockBand.Native.CEH.Deterministic.Eigenpairs
public import BlockBand.Native.CEH.LocalLaw.Holds
public import BlockBand.Native.CEH.ETH.Holds

/-!
# The QUE theorem without hypotheses

The quantum unique ergodicity bound for bulk eigenvectors, with the binders and conclusion of
`BlockBand.que`, proved with all inputs discharged.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Composition

open MeasureTheory

-- The linter option only silences the unused binders `hnW` and `hθ'` (kept as in `BlockBand.que`).
set_option linter.unusedVariables false in
/-- **The QUE theorem**, with the binders and conclusion of `BlockBand.que` and no further
hypotheses. -/
theorem que_unconditional
    (b θ T : ℝ)
    (hb : 0 < b) (hb' : b < 1 / 2)
    (hθ : 0 < θ) (hθ' : θ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n W : ℕ)
        (hn : 4 ≤ n) (hW : 0 < W)
        (hnW : (n : ℝ) ≤ T * (W : ℝ)),
      let p : Parameters := ⟨n, W, b, hn, hW, hb, hb'⟩
      Nonempty (FiniteRealization p) ∧
        ∀ (R : FiniteRealization p) (α : Fin p.N),
          IsBulkRank p θ α →
        ∀ v : p.Site → ℝ, (∀ x, |v x| ≤ 1) →
          R.spectral.queStatistic α v ≤
            C * (p.ratio + Real.rpow p.ratio (3 / 2 : ℝ)) +
              1 / ((W : ℝ) + 1) := by
  exact BlockBand.QUE.GUEInputs.que_of_gueInputs BlockBand.Native.PSSS.sourceContract_holds_zero
      BlockBand.Native.CEH.eigenpairs_exist BlockBand.Native.CEH.spacing_exists
      BlockBand.Native.CEH.externalLocalGUE_holds BlockBand.Native.CEH.externalETH_holds
      BlockBand.Native.CEH.mdeBranchIdentification_holds b θ T hb hb' hθ hθ'

end BlockBand.Internal.Composition
