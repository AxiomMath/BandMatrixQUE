module

public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanInv
public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormJointCov

/-!
# The near-rows chain estimate from the Cayley chain

The mixed `(𝒦, Gram)` pairs need `B3ClosedChainNearPin`: `B3ClosedChainPin` with the near-rows
clause `ι𝕊(𝕏_j)V_j = ιP𝕊_clV_j`.

* `nearSel_twoPortScattering_b3ChainXX`: for the Cayley state, with `1 - 𝕊_pad` invertible,
  `ι𝕊(b3ChainXX)V = ιP𝕊C V = ι·b3ClosedPS·V`.
* **`b3ClosedChainNearPin_of_zeroDet : B3PadZeroDet → B3PadTransport → B3ClosedChainNearPin`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3LayerMean

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.PhysApprox.B3
open BlockBand.Transmission.Bridge

variable {W np K : ℕ}

theorem nearSel_mul_nearPortProj : nearSel W * ClosedLimit.nearPortProj W = nearSel W := by
  ext x c
  simp only [nearSel, ClosedLimit.nearPortProj, Matrix.mul_diagonal]
  by_cases hc : c = (0, x)
  · subst hc; simp
  · simp [hc]

/-- **The near outgoing rows of the Cayley state are the closed ones.** -/
theorem nearSel_twoPortScattering_b3ChainXX {b E s h : ℝ} (τ m : Fin np → ℝ) {n : ℕ}
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) {y : ProbedPath W np × ℝ}
    (hη : 0 < etaZ b E) (hD : IsUnit (1 - b3PadScatter b E s h W n y.1.1 (phase y.2)).det) :
    nearSel W * twoPortScattering b E (b3ChainXX b E s h W n y) *
        b3ClosedFrameAt b E s h τ m W n Vs y =
      nearSel W * b3ClosedPS b E s h W n y.1.1 (phase y.2) *
        b3ClosedFrameAt b E s h τ m W n Vs y := by
  have hV : (1 - farEmbed (omittedProj b E h W (closeLen s W) y.1.1)) *
      b3ClosedFrameAt b E s h τ m W n Vs y = b3ClosedFrameAt b E s h τ m W n Vs y := by
    rw [Matrix.sub_mul, Matrix.one_mul, A_mul_b3ClosedFrameAt, sub_zero]
  rw [twoPortScattering_b3ChainXX hη hD, ← nearSel_mul_nearPortProj, Matrix.mul_assoc (nearSel W),
    nearPortProj_mul_b3PadScatter, Matrix.mul_assoc, Matrix.mul_assoc, hV]
  simp only [b3ClosedPS, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (ClosedLimit.nearPortProj W) (ClosedLimit.nearPortProj W),
    nearPortProj_mul_self]

/-- **`B3ClosedChainNearPin` from the phase-free estimate and the transport estimate.** -/
theorem b3ClosedChainNearPin_of_zeroDet (h0 : B3PadZeroDet) (hT : B3PadTransport) :
    B3ClosedChainNearPin := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨-, -, -, hη, -⟩ := frameDomain_facts hF
  have hC := b3CayleyChain_of_zeroDet h0 hT b E np τ m T s h K Vs hF R
  have hI := b3PadInvertible_of_zeroDet h0 b E np τ m T s h K Vs hF
  refine ⟨1, zero_le_one, ?_⟩
  filter_upwards [hC, hI] with W hCW hIW j hj
  have hjc : closeLen s W ≤ j := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).1
  refine ⟨b3ChainXX b E s h W j, hCW j hj, ?_⟩
  filter_upwards [hIW j hjc] with y hy _
  exact nearSel_twoPortScattering_b3ChainXX τ m (Vs W) hη hy.2

end BlockBand.SourceProcess.PhysApprox.B3LayerMean
