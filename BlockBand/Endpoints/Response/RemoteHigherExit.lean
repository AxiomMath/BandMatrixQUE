module

public import BlockBand.Endpoints.Response.RemoteHigherExitMass
public import BlockBand.Endpoints.Response.RemoteHigherExitValue
public import BlockBand.Endpoints.Response.JetFixedRemote

/-!
# Exit and stop removal for the higher functional

This file proves the stopped exit and stop-removal inequality for the higher functional
(`rhfStoppedExitRemoval_holds`), hence the finite-width trace generator
`RhlFiniteTraceGenerator` (`rhlFiniteTraceGenerator_holds`), and from it `RemoteHigherStatement`
from the transmission, moment, word, stop and generator contracts
(`remoteHigher_of_contracts`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Filter Topology Set Finset Polynomial
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints BlockBand.Internal.Contracts.Layers
  BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.Inputs
  BlockBand.Internal.Contracts.LayersOnePort BlockBand.Internal.Contracts.TransmissionUniform

/-- **The end value is small for large `K`** (`tail`, `supMoments`). -/
theorem rhx_endValue_small (hStops : FullSourceStopsContract) {b E : ℝ} (hb : 0 < b)
    (hb1 : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) {t₁ R : ℝ} {q : ℝ → ℝ}
    (hq : IsUnitSource t₁ R q) {u₁ u₂ : ℝ} (hu₁ : t₁ + R < u₁) (hu : u₁ ≤ u₂) (k : ℕ) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ K : ℝ, K₀ ≤ K → ∀ᶠ W : ℕ in atTop,
      growthPathLaw W b (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ +
          ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ.indicator
            (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (k + 1)) ω ∂growthPathLaw W b ≤
        ENNReal.ofReal θ := by
  have hu₁0 : 0 < u₁ := by linarith [hq.1, hq.2.1]
  have hIT : IsIntervalTests (fun _ : Fin 1 => q) := fun _ => ⟨t₁, t₁ + R, hq.2.2.2.1⟩
  obtain ⟨K₁, hK₁, h1⟩ := nsx_eventually_dead_le hStops hb hb1 hE hE' hIT hu₁0 hu
    (ρ := θ / 2) (by positivity)
  obtain ⟨K₂, hK₂, h2⟩ := nsx_dead_small hStops hb hb1 hE hE' hIT hu₁0 hu _
    (nsx_ui_of_moment (b := b) (fun W ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (k + 1))
      (nsx_supQ_moment hStops hb hb1 hE hE' hIT (by positivity : 0 < u₁ / 2) (by linarith) k))
    (θ := θ / 2) (by positivity)
  refine ⟨max K₁ K₂, lt_max_of_lt_left hK₁, fun K hK => ?_⟩
  filter_upwards [h1 K ((le_max_left _ _).trans hK), h2 K ((le_max_right _ _).trans hK)]
    with W hW1 hW2
  calc _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) := add_le_add hW1 hW2
    _ = ENNReal.ofReal θ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- **`RhfStoppedExitRemoval`**: the exit value, the end
value and the after-stop dissipation of the stopped higher composite `G(Φ_π)`, from
`FullSourceGeneratorContract` (`tight`), `ConditionalBlockGUECount` (a.s. unitarity of `𝕊`) and
`FullSourceStopsContract` (`tail`, `supMoments`, `compensatorUI`).
Order of choices:
`K` (end
value and after-stop mass, uniform in `π, G`), then `δ₀ = min(1, ε^p/(2(K+1)), θ/(4(BK+1)))`,
then `π, G`, then `W` (exit overshoot on the jump event).
-/
theorem rhfStoppedExitRemoval_holds (hGen : FullSourceGeneratorContract)
    (hCount : ConditionalBlockGUECount) (hStops : FullSourceStopsContract) :
    RhfStoppedExitRemoval := by
  intro b hb hb1 E hE hE' p r hp hp1 hr hpr t₁ R q hq ε hε u₁ u₂ hu₁ hu₂ θ hθ
  have hq0 : ∀ x, 0 ≤ q x := hq.2.2.2.1.1
  have hrk : r ≤ (⌈r⌉₊ : ℕ) + 1 := by have := Nat.le_ceil r; linarith
  have hr0 : 0 ≤ r := by linarith
  have hc₀ := rhx_CEnd_nonneg (r := r) hp.le hε ⌈r⌉₊
  obtain ⟨K₁, hK₁, hA⟩ := rhx_afterStop_small hCount hStops hb hb1 hE hE' hp.le hp1.le hr hε hrk
    hq hu₁ hu₂ (θ := θ / 4) (by positivity)
  obtain ⟨K₂, hK₂, hB⟩ := rhx_endValue_small hStops hb hb1 hE hE' hq hu₁ hu₂ ⌈r⌉₊
    (θ := θ / 4 / (rhxCEnd p r ε ⌈r⌉₊ + 1)) (by positivity)
  set K := max K₁ K₂ with hKdef
  have hK : 0 < K := lt_max_of_lt_left hK₁
  have hB0 := rhf_B_nonneg (p := p) (r := r) (K := K) hε
  have hεp := Real.rpow_pos_of_pos hε p
  have hBK : 0 < rhfB p r ε K * K + 1 := by positivity
  refine ⟨K, hK, min (min 1 (ε ^ p / (2 * (K + 1)))) (θ / (4 * (rhfB p r ε K * K + 1))),
    lt_min (lt_min one_pos (by positivity)) (by positivity),
    fun δ hδ hδle a N G h0 hG0 => ?_⟩
  have hδ1 : δ ≤ 1 := hδle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδK : δ * (K + 1) ≤ ε ^ p / 2 := by
    have h' : δ ≤ ε ^ p / (2 * (K + 1)) := hδle.trans ((min_le_left _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h'
    linarith
  have hδw : δ * (rhfB p r ε K * K + 1) ≤ θ / 4 := by
    have h' : δ ≤ θ / (4 * (rhfB p r ε K * K + 1)) := hδle.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h'
    linarith
  filter_upwards [hA K (le_max_left _ _), hB K (le_max_right _ _),
    nsx_jump_value_small hGen hStops hb hb1 hE hE' hq hu₁ hu₂ (rhxCG a N G) (rhx_CG_nonneg a N G)
      (rhxExp N G.natDegree) (θ := θ / 4) (by positivity),
    nsx_eventually_index hq hu₁] with W hWA hWB hWJ ⟨hW0, hjW, _⟩
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW0
  have h12 : ⌊(W : ℝ) * u₁⌋₊ ≤ ⌊(W : ℝ) * u₂⌋₊ :=
    Nat.floor_le_floor (mul_le_mul_of_nonneg_left hu₂ hW'.le)
  have hj₂T : (⌊(W : ℝ) * u₂⌋₊ : ℝ) ≤ (u₂ + 1) * W := by
    have := Nat.floor_le (mul_nonneg hW'.le (show 0 ≤ u₂ by linarith [hq.1, hq.2.1]))
    nlinarith
  have hV := rhx_value_le (b := b) (E := E) hp.le hp1.le hε hr0 hrk hq0 hK.le hδ.le hδ1 hδK h0
    hG0 hjW h12 hj₂T
  exact nsx_final_combine hθ.le hV hWA (ENNReal.ofReal_le_ofReal hδw)
    (nsx_const_mul_le hc₀ (by positivity) hWB) hWJ

/-!
## The composites
-/

/-- **`RhlFiniteTraceGenerator` from `ContractingWordsContract`, `FullSourceStopsContract`,
`ConditionalBlockGUECount` and `FullSourceGeneratorContract`**:
`rhlFiniteTraceGenerator_of_exitRemoval` with `rhfStoppedExitRemoval_holds`.
-/
theorem rhlFiniteTraceGenerator_holds (hCW : ContractingWordsContract)
    (hStops : FullSourceStopsContract) (hCount : ConditionalBlockGUECount)
    (hGen : FullSourceGeneratorContract) : RhlFiniteTraceGenerator :=
  rhlFiniteTraceGenerator_of_exitRemoval hCW hStops hCount
    (rhfStoppedExitRemoval_holds hGen hCount hStops)

open BlockBand.Internal.Contracts.TransmissionUniform2 in

/-- **The remote higher-order theorem (`RemoteHigherStatement`) from the contracts and the
one-port contracts.** The hypotheses of `remoteHigher_of_scalarContraction` with
`RhlFiniteTraceGenerator` replaced by its inputs (`rhlFiniteTraceGenerator_holds`):
`ConditionalBlockGUECount`, `TransmissionLawContract`, `PassiveCovarianceContract`,
`PassiveSourceMixingContract`, `EdgeClockMomentsContract`, `TransmissionLengthUniformContract`,
the one-port contracts `OnePortPassiveMeanContract`, `OnePortOperatorMomentsContract`,
`PassiveScalarContractionContract`, and `ContractingWordsContract`,
`FullSourceStopsContract`, `FullSourceGeneratorContract`.
-/
theorem remoteHigher_of_contracts (hCount : ConditionalBlockGUECount)
    (hTL : TransmissionLawContract) (hPC : PassiveCovarianceContract)
    (hPSM : PassiveSourceMixingContract) (hECM : EdgeClockMomentsContract)
    (hTLU : TransmissionLengthUniformContract) (hPM : OnePortPassiveMeanContract)
    (hOM : OnePortOperatorMomentsContract) (hPSC : PassiveScalarContractionContract)
    (hCW : ContractingWordsContract) (hStops : FullSourceStopsContract)
    (hGen : FullSourceGeneratorContract) : RemoteHigherStatement :=
  remoteHigher_of_scalarContraction hCount hTL hPC hPSM hECM hTLU hPM hOM hPSC
    (rhlFiniteTraceGenerator_holds hCW hStops hCount hGen) hGen

end BlockBand.Endpoints
