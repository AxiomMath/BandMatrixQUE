module

public import BlockBand.Endpoints.Response.TaggedConvexOrderLimit

/-!
# The tagged convex order theorem

Law: the near-end-grown path `growthPathLaw W b` with an independent `h ~ CN(0, I_{2W})`
(`probedClockLaw`); `Z_{n;k} = W⁻¹h*Y_{n;k}h` (`lmf_tagResponseClock`), `M_W = h*Yh/(nW)`
(`rescaledClock`), `d = d_* = 1/(1-b)`, `D₀ = 2/(b(4-E²))`. The hypotheses are
`FullSourceMomentsEnergyUniformContract` and `TcoTagComparisonCore` (resp.
`TcoTagComparisonCoreFixed` for the fixed-energy statement).

## Main results

* `taggedConvexOrder`: `TaggedConvexOrderStatement` in the energy-uniform reading (moving
  energies `e_j → E` everywhere): for every tagged sequence and every weak limit `ν` of the laws
  of `Z_{n_j;k_j}` along a subsequence, every convex polynomial `φ` on `[0,∞)` satisfies
  `∫φ dν ≤ E φ(d e^{√D₀B_{τ-s}-D₀(τ-s)/2})` (and is `ν`-integrable), `∫ x dν = d`, all fixed
  moments converge along the subsequence; and the averaged clause `LmfTaggedFlat`.
* `taggedFlat_energyUniform` / `lmfTaggedFlat_holds`: the averaged clause in the form
  `LmfTaggedFlat` (the tagged flat bound and the `M_W` clause, one constant `C_{p,T₀}`
  depending on `b, E`, `τ ∈ (0,T₀]`, every `ClockSequence τ E`, limsups of lower integrals in
  `ℝ≥0∞`).
* `taggedConvexOrder_fixed`, `taggedFlat_fixedEnergy`: the fixed-energy statement, from the
  fixed-energy tag comparison core; `taggedFlat_fixedEnergy_of_uniform`: the fixed-`E` averaged
  clause as a corollary of the energy-uniform one.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open BlockBand.Internal.Contracts.TransmissionUniform

/-- The averaged clause of the tagged convex order theorem, energy-uniform (read at moving
energies): the form `LmfTaggedFlat`. -/
theorem taggedFlat_energyUniform (hMom : FullSourceMomentsEnergyUniformContract)
    (hCore : TcoTagComparisonCore) : LmfTaggedFlat := by
  intro b hb hb' E hE1 hE2 T₀ _ p hp
  obtain ⟨C, hC⟩ := tco_flat_of_along hMom hb hb' hE1 hE2 T₀ hp
  exact ⟨C, fun τ hτ hτT s => hC τ hτ hτT s fun s₀ σ hs₀ _ =>
    hCore b hb hb' E hE1 hE2 s₀ τ hs₀ σ⟩

/-- **`LmfTaggedFlat`** (the hypothesis of the flat local-mass theorem), from the energy-uniform
moments `FullSourceMomentsEnergyUniformContract` and `TcoTagComparisonCore`.
-/
theorem lmfTaggedFlat_holds (hMom : FullSourceMomentsEnergyUniformContract)
    (hCore : TcoTagComparisonCore) : LmfTaggedFlat :=
  taggedFlat_energyUniform hMom hCore

/-- The fixed-energy averaged clause is a corollary of the energy-uniform one. -/
theorem taggedFlat_fixedEnergy_of_uniform (h : LmfTaggedFlat) : TaggedFlatFixedEnergy := by
  intro b hb hb' E hE1 hE2 T₀ hT₀ p hp
  obtain ⟨C, hC⟩ := h b hb hb' E hE1 hE2 T₀ hT₀ p hp
  exact ⟨C, fun τ hτ hτT s _ => hC τ hτ hτT s⟩

/-- The energy-uniform tag comparison core contains the fixed-energy one. -/
theorem tco_coreFixed_of_core (h : TcoTagComparisonCore) : TcoTagComparisonCoreFixed :=
  fun b hb hb' E hE1 hE2 s τ hs σ _ => h b hb hb' E hE1 hE2 s τ hs σ

/-- The averaged clause at the fixed energy `E`, from the fixed-energy tag comparison core. -/
theorem taggedFlat_fixedEnergy (hMom : FullSourceMomentsEnergyUniformContract)
    (hCore : TcoTagComparisonCoreFixed) : TaggedFlatFixedEnergy := by
  intro b hb hb' E hE1 hE2 T₀ _ p hp
  obtain ⟨C, hC⟩ := tco_flat_of_along hMom hb hb' hE1 hE2 T₀ hp
  refine ⟨C, fun τ hτ hτT s hs => hC τ hτ hτT s fun s₀ σ hs₀ hen =>
    hCore b hb hb' E hE1 hE2 s₀ τ hs₀ σ fun i => ?_⟩
  obtain ⟨j, hj⟩ := hen i
  rw [← hj, hs j]

/-- The tagged convex order theorem, energy-uniform reading. -/
theorem taggedConvexOrder (hMom : FullSourceMomentsEnergyUniformContract)
    (hCore : TcoTagComparisonCore) : TaggedConvexOrderStatement :=
  ⟨fun b hb hb' E hE1 hE2 s τ hs σ =>
      tco_limitLaw_of_along hMom hb hb' hE1 hE2 σ (hCore b hb hb' E hE1 hE2 s τ hs σ),
    taggedFlat_energyUniform hMom hCore⟩

/-- The tagged convex order theorem at a fixed energy. -/
theorem taggedConvexOrder_fixed (hMom : FullSourceMomentsEnergyUniformContract)
    (hCore : TcoTagComparisonCoreFixed) : TaggedConvexOrderFixedStatement :=
  ⟨fun b hb hb' E hE1 hE2 s τ hs σ hσ =>
      tco_limitLaw_of_along hMom hb hb' hE1 hE2 σ (hCore b hb hb' E hE1 hE2 s τ hs σ hσ),
    taggedFlat_fixedEnergy hMom hCore⟩

end BlockBand.Endpoints
