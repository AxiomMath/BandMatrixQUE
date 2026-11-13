module

public import BlockBand.Center.CenterSmall

/-!
# The center supply `IsCenterSupply pairCenterFamily0`

Given rank location, matched traces, the full energy trace bound and pole exclusion, the Dyson
center family `pairCenterFamily0` is a center supply with the constants `cst0`, combining
`pairCenterFamily0_isDyson`, `centerDomain_regular`, `centerDomain_small` and
`centerDomain_measurable`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm

/-- `CenterDomainContract cst0`, from the three clauses. -/
theorem centerDomainContract_cst0_of (hrank : RankLocationContract)
    (hmt : MatchedTracesContract) (hfe : FullEnergyTraceBound)
    (hpole : PairPoleExclusionContract) : CenterDomainContract cst0 :=
  ⟨centerDomain_regular, centerDomain_small hrank hmt hfe hpole, centerDomain_measurable cst0⟩

/-- **The center supply** for `pairCenterFamily0` (constants `cst0`). -/
theorem centerSupply_holds_of (hrank : RankLocationContract) (hmt : MatchedTracesContract)
    (hfe : FullEnergyTraceBound) (hpole : PairPoleExclusionContract) :
    IsCenterSupply pairCenterFamily0 :=
  ⟨cst0, pairCenterFamily0_isDyson, centerDomainContract_cst0_of hrank hmt hfe hpole⟩

end BlockBand.Center
