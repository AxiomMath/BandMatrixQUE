module

public import BlockBand.Endpoints.Response.TaggedConvexOrderUniformSummed
public import BlockBand.Endpoints.Response.TaggedConvexOrderUniformRemoval
public import BlockBand.Endpoints.Response.TaggedConvexOrderStepComparison

/-!
# The energy-uniform tagged convex order from the energy-uniform contracts

Fixed `0 < b < 1/2`, base bulk `-2 < E < 2`, `s > 0`, and every tagged sequence with moving
energies `e_j → E` (`TcoTagSequence`), law `probedClockLaw W b`; the limit objects `D₀ = D₀(E)`,
`d = d_*` stay at the base energy. The hypotheses are `FullSourceMomentsEnergyUniformContract`,
`TagBirthValueEnergyUniformContract`, `FullSourceStopsEnergyUniformContract`,
`ConditionalBlockGUECount` and `ContractingWordsEnergyUniformContract`; each energy-uniform
contract is applied at a bulk margin `κ` with `e_j ∈ bulkInterval κ` eventually
(`tcu_eventually_bulk`).

## Main results

* `lmfTaggedFlat_of_uniformContracts : LmfTaggedFlat` (through `lmfTaggedFlat_holds`).
* `taggedConvexOrder_of_uniformContracts : TaggedConvexOrderStatement` (energy-uniform reading,
  through `taggedConvexOrder`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial Finset Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionUniform BlockBand.Internal.Contracts.TransmissionUniform2
open scoped ENNReal NNReal

/-- The split one-step input along moving energies with the explicit witness `tcw_deficit`: its
sign clause holds at every path energy `e_j` in the open bulk (`tcw_deficit_sign_clause`), and the
remainder clause is `TcwRemainderAlong`. Moving-energy version of
`tcsOneStepSplitCoreFixed_of_remainder`. -/
theorem tcu_splitAlong (hCount : ConditionalBlockGUECount) {b : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {s τ : ℝ} (σ : TcoTagSequence s τ E)
    (hM : TccMomentsAlong b σ) (hR : TcwRemainderAlong b σ) : TcsOneStepSplitAlong b σ := by
  intro M δ hδ
  obtain ⟨κ, hκ, hbulk⟩ := tcu_eventually_bulk σ hE1 hE2
  choose Cf hCf using hM
  have hmomE : ∀ᶠ j in atTop, ∀ p ∈ range (M + 3), ∀ l, σ.k j < l → l ≤ σ.n j →
      ∫⁻ x, ENNReal.ofReal (x ^ (2 * p)) ∂tcc_law b (σ.energy j) (σ.W j) l (σ.k j) ≤
        ENNReal.ofReal (Cf p) :=
    (eventually_all_finset _).2 fun p _ => hCf p
  filter_upwards [hmomE, hR M δ hδ, hbulk] with j hmj hRj he
  obtain ⟨he1, he2⟩ := tcu_bulk_bounds hκ he
  refine ⟨fun l m => tcw_deficit b (σ.energy j) (σ.W j) l (σ.k j) m, ?_, hRj⟩
  intro l hl ψ hψ hdeg
  obtain ⟨hl1, hl2⟩ := mem_Ico.1 hl
  exact tcw_deficit_sign_clause hCount hb hb' he1 he2 (σ.W_pos j) l (σ.k j) M
    (fun p hp => tcw_integrable_tagClock_pow (hmj p (by simp; omega) l (by omega) (by omega)))
    hψ hdeg

/-- **The prelimit convex comparison along one tagged sequence with moving energies** from the
energy-uniform contracts.
-/
theorem tcu_comparisonAlong (hMom : FullSourceMomentsEnergyUniformContract)
    (hBirth : TagBirthValueEnergyUniformContract) (hStops : FullSourceStopsEnergyUniformContract)
    (hCount : ConditionalBlockGUECount) (hCW : ContractingWordsEnergyUniformContract)
    {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {s τ : ℝ}
    (hs : 0 < s) (σ : TcoTagSequence s τ E) : TcoConvexComparisonAlong b σ := by
  have hM := tcu_momentsAlong hMom hb hb' hE1 hE2 σ
  have hSt := tcu_stoppedRemainderAlong hCW hMom hCount hb hb' hE1 hE2 hs σ
  have hR := tcu_remainderAlong_of_own hb hE1 hE2 σ hM
    (tcu_ownRemainderAlong hMom hStops hCount hb hb' hE1 hE2 hs σ hSt)
  exact tcs_comparisonAlongBV σ (tco_transportD0_nonneg hb hE1 hE2)
    (tcs_oneStepAlongBV_of_split hM (tcu_splitAlong hCount hb hb' hE1 hE2 σ hM hR)) hM
    (tcu_birthAlong hMom hBirth hb hb' hE1 hE2 hs σ)

/-- **`TcoTagComparisonCore` (energy-uniform) from the contracts**:
`FullSourceMomentsEnergyUniformContract`, `TagBirthValueEnergyUniformContract`,
`FullSourceStopsEnergyUniformContract`, `ContractingWordsEnergyUniformContract` and
`ConditionalBlockGUECount`. -/
theorem tcoTagComparisonCore_of_uniformContracts (hMom : FullSourceMomentsEnergyUniformContract)
    (hBirth : TagBirthValueEnergyUniformContract) (hStops : FullSourceStopsEnergyUniformContract)
    (hCount : ConditionalBlockGUECount) (hCW : ContractingWordsEnergyUniformContract) :
    TcoTagComparisonCore :=
  fun _ hb hb' _ hE1 hE2 _ _ hs σ =>
    tcu_comparisonAlong hMom hBirth hStops hCount hCW hb hb' hE1 hE2 hs σ

/-- **`LmfTaggedFlat`** (the energy-uniform averaged clause of the tagged convex order theorem,
and the `M_W` clause, used by the flat local-mass theorem) from the energy-uniform contracts.
-/
theorem lmfTaggedFlat_of_uniformContracts (hMom : FullSourceMomentsEnergyUniformContract)
    (hBirth : TagBirthValueEnergyUniformContract) (hStops : FullSourceStopsEnergyUniformContract)
    (hCount : ConditionalBlockGUECount) (hCW : ContractingWordsEnergyUniformContract) :
    LmfTaggedFlat :=
  lmfTaggedFlat_holds hMom (tcoTagComparisonCore_of_uniformContracts hMom hBirth hStops hCount hCW)

/-- **The tagged convex order theorem, energy-uniform reading** (`TaggedConvexOrderStatement`),
from the energy-uniform contracts. -/
theorem taggedConvexOrder_of_uniformContracts (hMom : FullSourceMomentsEnergyUniformContract)
    (hBirth : TagBirthValueEnergyUniformContract) (hStops : FullSourceStopsEnergyUniformContract)
    (hCount : ConditionalBlockGUECount) (hCW : ContractingWordsEnergyUniformContract) :
    TaggedConvexOrderStatement :=
  taggedConvexOrder hMom (tcoTagComparisonCore_of_uniformContracts hMom hBirth hStops hCount hCW)

end BlockBand.Endpoints
