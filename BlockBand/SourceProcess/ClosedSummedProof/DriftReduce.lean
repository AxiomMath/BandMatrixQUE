module

public import BlockBand.SourceProcess.ClosedSummedProof.DriftStep
public import BlockBand.SourceProcess.ClosedSumProof.SummedSplit

/-!
# `ClosedDriftSummed` from the Gaussian inputs and `ClosedChainPin`

`closedDriftSummed_of_chain` derives the drift part `ClosedDriftSummed` of `ClosedSummed` from
`GaussianAbsorptionContract`, `GaussianLpGradient`, `GaussianPoincare` and `ClosedChainPin`,
through the one-layer drift bound `gram_layer_drift`. `bulk_of_open` places every `E ∈ (-2, 2)` in
a bulk interval.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSummedProof

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.ClosedSumProof
open scoped ENNReal

theorem bulk_of_open {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    ∃ κ : ℝ, 0 < κ ∧ E ∈ bulkInterval κ := by
  refine ⟨min (E + 2) (2 - E), lt_min (by linarith) (by linarith), ?_, ?_⟩
  · have := min_le_left (E + 2) (2 - E); linarith
  · have := min_le_right (E + 2) (2 - E); linarith

/-- **`ClosedDriftSummed` from the input hypotheses and `ClosedChainPin`.** -/
theorem closedDriftSummed_of_chain (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hC : ClosedChainPin) : ClosedDriftSummed := by
  intro b hb0 hb E hE1 hE2 s T hs hsT p q hq h hh0 hh1 K M hM R Vs hVs e e'
  obtain ⟨σ, hσ, X, hX, hX0⟩ := hC b hb0 hb E hE1 hE2 s T hs hsT p q hq h hh0 hh1 K M hM R Vs hVs
  obtain ⟨κ, hκ, hEκ⟩ := bulk_of_open hE1 hE2
  obtain ⟨C, W₀, hC0, hD⟩ := gram_layer_drift hGA hLp hP hb0 hb hκ R
  obtain ⟨C₄, W₄, -, h4⟩ := fresh_pow_bound hGA hb0 hb hκ
  have hq' : ∀ i x, 0 ≤ q i x := fun i x => (hq i).1 x
  have hle : ∀ᶠ W in atTop, driftSum b E s T h q R W (Vs W) e e' ≤
      ENNReal.ofReal C * chainErrSum b E s T h q R W (Vs W) (X W) σ := by
    filter_upwards [hVs, hX, eventually_ge_atTop W₀, eventually_ge_atTop W₄] with W hV hXW hW hW4
    unfold driftSum chainErrSum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    obtain ⟨hXm, hXh, hrel⟩ := hXW j hj
    exact drift_step b E s T h hq' (by linarith) hE1 hE2 R (Finset.mem_Ico.mp hj).1 hV.1 hXm hXh
      hrel hC0 (fun XX hXX V hJ hTr e => hD W hW E hEκ σ hσ XX hXX V (sigVals K (Fin p × Fin M))
        (abs_sigVals_le K _) hJ hTr e) (h4 W hW4 E hEκ) e
  have hlim : Tendsto (fun W => ENNReal.ofReal C * chainErrSum b E s T h q R W (Vs W) (X W) σ)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hX0 (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) hle

end BlockBand.SourceProcess.ClosedSummedProof
