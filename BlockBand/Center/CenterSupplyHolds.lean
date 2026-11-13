module

public import BlockBand.Center.CenterSupply
public import BlockBand.Layers.FullEnergyTransfer
public import BlockBand.Layers.HeatMeanSquare
public import BlockBand.Layers.MatchedTraces

/-!
# `IsCenterSupply pairCenterFamily0`: assembled constructor

The center supply hypotheses are discharged by the proved theorems:
* `RankLocationContract` from `rankLocation_holds` (the rank location theorem);
* `MatchedTracesContract` from `matchedTraces_holds` (the matched traces theorem);
* `FullEnergyTraceBound` from `fullEnergyTraceBound_holds` (the full energy trace bound).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Inputs (GaussianLpGradient ConditionalBlockGUECount)

/-- **`CenterDomainContract cst0`** (the `regular`, `small` and `measurable` clauses) from the
input hypotheses `ConditionalBlockGUECount`, `GaussianLpGradient` and
`PairPoleExclusionContract` only. -/
theorem centerDomainContract_cst0_holds (hcount : ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) (hpole : PairPoleExclusionContract) : CenterDomainContract cst0 :=
  centerDomainContract_cst0_of (BlockBand.Layers.rankLocation_holds hcount hgrad)
    (BlockBand.Layers.matchedTraces_holds hcount hgrad)
    (BlockBand.Layers.fullEnergyTraceBound_holds hcount hgrad) hpole

/-- **`IsCenterSupply pairCenterFamily0`** (the simultaneous splitting and the domain clause of
the physical center theorem): the witness `cst0` with `pairCenterFamily0_isDyson`
(`IsDysonCenterFamily cst0`) and `centerDomainContract_cst0_holds` (`CenterDomainContract cst0`:
`regular`, `small`, `measurable`).

* Law: for every `(p, model, α, i)` the extension of `pairCenterFamily0` (product of the explicit
  residual splitting law and `GUE_{2W}(s/(2W))`, `s = min(c, b)`), carrying exactly the physical law;
  the domain clause under the exact pair law `extendedPairMeasure` of every extension with an edge
  splitting.
* Domain: `4 ≤ n ≤ TW`, `p.b = b ∈ (0, 1/2)`, every `ϑ`-bulk rank `α` (`0 < ϑ < 1/2`), every
  adjacent pair `i`; regular domain `D_e(E) = {E ∈ bulkInterval κ_α, ε_e(E) ≤ ε₁}` with
  `ε₁ = cst0.ε₁ b κ_α` (half the certificate threshold).
* Quantifier order and uniformity: `b, ϑ, T` (and `q`) first, then the constants; uniformly in the
  parameters, the model, the rank, the pair and the extension. Order of limits: none. -/
theorem centerSupply_holds (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient)
    (hpole : PairPoleExclusionContract) : IsCenterSupply pairCenterFamily0 :=
  centerSupply_holds_of (BlockBand.Layers.rankLocation_holds hcount hgrad)
    (BlockBand.Layers.matchedTraces_holds hcount hgrad)
    (BlockBand.Layers.fullEnergyTraceBound_holds hcount hgrad) hpole

end BlockBand.Center
