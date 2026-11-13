module

public import BlockBand.Layers.TaggedTrace
public import BlockBand.Center.CenterResidualEnergy

/-!
# The full-energy trace bound: the bridge to the center's domain clause

The `small` clause of `CenterDomainContract` uses the full-energy trace bound through
`BlockBand.Center.FullEnergyTraceBound`. This module shows that this is exactly the moment half of
`FullEnergyTraceStatement`:

* `fullEnergyTraceBound_of_statement : FullEnergyTraceStatement → FullEnergyTraceBound`;
* `fullEnergyTrace_of_bound : FullEnergyTraceBound → FullEnergyTraceStatement` (the almost-sure
  differentiability half is proved, `tgt_ae_eps_energy_hasDerivAt`).

Hence the energy clause of the tagged-trace lemma is equivalent to `FullEnergyTraceBound`, which
is proved by `fullEnergyTraceBound_holds`. Its integrand is `tgtEps` written out (`csmEps` of
`BlockBand.Center`), so the two statements agree definitionally.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE BlockBand.Model.Construction

/-- The integrand `csmEps` of `BlockBand.Center` is `tgtEps`. -/
theorem tgt_csm_integrand_eq {p : Parameters} (e : ZMod p.n) (Hres : p.SiteMatrix) (k : ZMod p.n)
    (E' : ℝ) :
    pairBlockTrace p e (compressedResolvent p e Hres E' ((splitS p : ℂ) *
        (starRingEnd ℂ) (matchedA E'))) k - (starRingEnd ℂ) (matchedA E') =
      tgtEps p e Hres E' k := rfl

/-- **Bridge** `FullEnergyTraceStatement → FullEnergyTraceBound` (drop the a.s. differentiability). -/
theorem fullEnergyTraceBound_of_statement (h : FullEnergyTraceStatement) :
    BlockBand.Center.FullEnergyTraceBound := by
  intro b hb0 hb1 κ T hκ q hq
  obtain ⟨C, W₀, hC⟩ := h b hb0 hb1 κ T hκ q hq
  exact ⟨C, W₀, fun p hpb hnT hW model i X G hs E hE k hk =>
    (hC p hpb hnT hW model i X G hs E hE k hk).2⟩

/-- **Converse bridge** `FullEnergyTraceBound → FullEnergyTraceStatement`: the almost-sure
differentiability is proved (`tgt_ae_eps_energy_hasDerivAt`). -/
theorem fullEnergyTrace_of_bound (h : BlockBand.Center.FullEnergyTraceBound) :
    FullEnergyTraceStatement := by
  intro b hb0 hb1 κ T hκ q hq
  obtain ⟨C, W₀, hC⟩ := h b hb0 hb1 κ T hκ q hq
  refine ⟨C, W₀, fun p hpb hnT hW model e X G hs E hE k hk => ⟨?_, hC p hpb hnT hW model e X G hs E hE k hk⟩⟩
  filter_upwards [tgt_ae_eps_energy_hasDerivAt X hs hκ hE k] with ω hω
  exact hω.2

/-- The full-energy trace bound in the form of `BlockBand.Center` is equivalent to
`FullEnergyTraceStatement`. -/
theorem fullEnergyTrace_iff : FullEnergyTraceStatement ↔ BlockBand.Center.FullEnergyTraceBound :=
  ⟨fullEnergyTraceBound_of_statement, fullEnergyTrace_of_bound⟩

end BlockBand.Layers
