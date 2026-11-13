module

public import BlockBand.Critical.MatrixClosing.Poles.RankPos
public import BlockBand.Critical.MatrixClosing.Poles.Average

/-!
# Matrix closing: hypothesis 1 at positive rank and the assembly

Hypothesis 1 of the Herglotz tail lemma for the collar function at a positive frame rank follows
from the decorated relative mixed vectors theorem and the collar good event.

* `collarPolesAt_of_goodEvent`: `CollarPolesAt r` for `r ≥ 1`, from
  `RelativeMixedVectorsStatement` and `CollarGoodEventAt r`, via
  `collarPolesLaplaceAt_of_goodEvent` (the collar atoms are the marked atoms of `F + G` with
  residues `π⁻¹zz^*`; Fubini over `collarLaw = layerLaw ⊗ GUE`).
* `matrixClosing_of_goodEvent`: `MatrixClosingStatement` from `RelativeMixedVectorsStatement`,
  the good event at every positive rank, `CollarMeanClause` and `ExactBoundaryMeanContract`, via
  `matrixClosing_of_clauses_pos` (the rank-zero case holds trivially).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Poles

open BlockBand.Critical.RelativeVectors
open BlockBand.Internal.Contracts.Critical

/-- Hypothesis 1 at a positive rank from the relative mixed vectors theorem and the good event. -/
theorem collarPolesAt_of_goodEvent (hRMV : RelativeMixedVectorsStatement) {r : ℕ} (hr : 0 < r)
    (hG : CollarGoodEventAt r) : CollarPolesAt r :=
  collarPolesAt_of_laplaceAt (collarPolesLaplaceAt_of_goodEvent hRMV.2 hr hG)

/-- The matrix closing theorem from the relative mixed vectors theorem, the good event at every
positive rank, the mean clause and the exact boundary mean statement. -/
theorem matrixClosing_of_goodEvent (hRMV : RelativeMixedVectorsStatement)
    (hG : ∀ r, 0 < r → CollarGoodEventAt r) (h2 : CollarMeanClause)
    (hEB : ExactBoundaryMeanContract) : MatrixClosingStatement :=
  matrixClosing_of_clauses_pos (fun r hr => collarPolesAt_of_goodEvent hRMV hr (hG r hr)) h2 hEB

end BlockBand.Critical.MatrixClosing.Poles
