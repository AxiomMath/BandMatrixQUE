module

public import BlockBand.RankLocation.RankLocationCount

/-!
# The rank-location theorem

Law and domain: the exact physical ring (raw `H`, row variance one), `N = nW`, `4 ≤ n ≤ TW`,
deterministic `E ∈ bulkInterval κ`, ϑ-bulk ranks (one-based `IsBulkRank`); norms `L^q`, `q ≥ 1`;
constants depend on `b, κ, T, q` (resp. `b, T, ϑ, q`) only and are the same under every mass law.

`rankLocation_of_contracts` proves `RankLocationContract` from `FreshCountContract`,
`RingCompensatedPhaseContract` and `MatchedTracesContract`, by composing two results of sibling
modules:
* `rkl_physicalCount_holds`: the two count clauses under the physical law, from these three
  hypotheses;
* `rankLocation_of_physicalCount`: location by monotonicity at `e_α ± t`, tail integration and
  polynomial norm moments; mass-law transport.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.RankLocation

open BlockBand.Internal.Contracts.Layers

/-- **The rank-location theorem** (`RankLocationContract`), from the fresh count lemma
(`FreshCountContract`), the `Ξ_{n-1}` estimate (`RingCompensatedPhaseContract`) and the
common-port trace of the matched traces theorem (`MatchedTracesContract`). -/
theorem rankLocation_of_contracts (hfc : FreshCountContract)
    (hring : RingCompensatedPhaseContract) (hmt : MatchedTracesContract) :
    RankLocationContract :=
  rankLocation_of_physicalCount (rkl_physicalCount_holds hfc hring hmt)

end BlockBand.RankLocation
