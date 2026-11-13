module

public import BlockBand.SourceProcess.ClosedSummedProof.BracketStep
public import BlockBand.SourceProcess.ClosedSummedProof.DriftReduce

/-!
# `ClosedBracketSummed` from the Gaussian inputs and `ClosedChainPin`

`closedBracketSummed_of_chain` derives the bracket part `ClosedBracketSummed` of `ClosedSummed`
from `GaussianAbsorptionContract`, `GaussianLpGradient`, `GaussianPoincare` and `ClosedChainPin`,
through the one-layer covariance bound `gram_layer_cov`.
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

/-- **`ClosedBracketSummed` from the input hypotheses and `ClosedChainPin`.** -/
theorem closedBracketSummed_of_chain (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hC : ClosedChainPin) : ClosedBracketSummed := by
  intro b hb0 hb E hE1 hE2 s T hs hsT p q hq h hh0 hh1 K M hM R Vs hVs e e'
  obtain ⟨σ, hσ, X, hX, hX0⟩ := hC b hb0 hb E hE1 hE2 s T hs hsT p q hq h hh0 hh1 K M hM R Vs hVs
  obtain ⟨κ, hκ, hEκ⟩ := bulk_of_open hE1 hE2
  obtain ⟨C, W₀, hC0, hD⟩ := gram_layer_cov hGA hLp hP hb0 hb hκ R
  obtain ⟨C₄, W₄, -, h4⟩ := fresh_pow_bound hGA hb0 hb hκ
  have hq' : ∀ i x, 0 ≤ q i x := fun i x => (hq i).1 x
  have hle : ∀ᶠ W in atTop, bracketSum b E s T h q R W (Vs W) e e' ≤
      ENNReal.ofReal C * chainErrSum b E s T h q R W (Vs W) (X W) σ := by
    filter_upwards [hVs, hX, eventually_ge_atTop W₀, eventually_ge_atTop W₄] with W hV hXW hW hW4
    unfold bracketSum chainErrSum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    obtain ⟨hXm, hXh, hrel⟩ := hXW j hj
    exact bracket_step b E s T h hq' (by linarith) hE1 hE2 R (Finset.mem_Ico.mp hj).1 hV.1 hXm hXh
      hrel hC0 (fun XX hXX V hJ hTr e e' => hD W hW E hEκ σ hσ XX hXX V (sigVals K (Fin p × Fin M))
        (abs_sigVals_le K _) hJ hTr e e') (h4 W hW4 E hEκ) e e'
  have hlim : Tendsto (fun W => ENNReal.ofReal C * chainErrSum b E s T h q R W (Vs W) (X W) σ)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hX0 (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) hle

end BlockBand.SourceProcess.ClosedSummedProof
