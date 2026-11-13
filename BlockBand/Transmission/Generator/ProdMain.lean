module

public import BlockBand.Transmission.Generator.ProdLimit
public import BlockBand.Transmission.Generator.ProdFinite
public import BlockBand.Transmission.Generator.AssemblyMod

/-!
# `ProductMartingaleAlong` and the transmission generator theorem from the transmission inputs

* **`productMartingaleAlong_holds hMT hGA hLp hP : ProductMartingaleAlong`**. For a limit
  `(P, Π)` along `σ`, a past test `Φ` and `0 < s ≤ t`: the finite-`W` tested product
  `E_n[Φ(M^W_kM^W_l - Σ B/W)]` tends to `0` (`prod_finite_tendsto`) and to the expansion of
  `E[Φ(M_kM_l - ∫B)]` (`prod_conv`, `limit_pieces`); integrability is `limit_pieces` at `Φ = 1`.
* **`transmissionGenerator_holds hMT hGA hLp hP : TransmissionGeneratorContract`**
  (`transmissionGenerator_of_prod`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform

/-- **The product half of `martingale`, along a moving energy, from the input hypotheses.** -/
theorem productMartingaleAlong_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    ProductMartingaleAlong := by
  intro b hb0 hb E hE1 hE2 Ce e he Ω _ P Pk h obs M k l hk hl
  have hLU := LengthUniform.transmissionLengthUniform_holds hMT hGA hLp
  have := h.prob
  obtain ⟨σ, hσm, hσ⟩ := h.fdd
  have hS : LimitSetup b e P Pk σ := ⟨h.prob, h.measurable, hσm.tendsto_atTop, hσ⟩
  intro s t hs ht hst
  have hs0 : 0 < s := hs
  have hint := (limit_pieces hLU hb0 hb hE1 hE2 he hS h.continuous hk hl hs0 hst (m := 0)
    Fin.elim0 (fun l => l.elim0) (BoundedContinuousFunction.const _ 1)).1
  refine ⟨by simpa using hint, fun m i u hu Φ => ?_⟩
  set pts : Fin m → ℕ × ℝ := fun j => ((i j).1, u j)
  have hpts : ∀ j, 1 ≤ (pts j).1 ∧ 0 < (pts j).2 := fun j => ⟨(i j).2, (hu j).1⟩
  show ∫ ω, Φ (limVec Pk pts ω) * ((Pk k t ω - Pk k s ω -
      ∫ u in s..t, transmissionDrift (transportD0 b E) k (fun i => Pk i u ω)) *
      (Pk l t ω - Pk l s ω -
      ∫ u in s..t, transmissionDrift (transportD0 b E) l (fun i => Pk i u ω)) -
      ∫ u in s..t, transmissionBracket (transportD0 b E) k l (fun i => Pk i u ω)) ∂P = 0
  rw [(limit_pieces hLU hb0 hb hE1 hE2 he hS h.continuous hk hl hs0 hst pts hpts Φ).2]
  have hconv := prod_conv hLU hb0 hb hE1 hE2 he hS hk hl hs0 hst pts hpts Φ
  have hzero := prod_finite_tendsto hMT hGA hLp hP hb0 hb hE1 hE2 he hk hl hs0 hst
    hσm.tendsto_atTop (B := ‖Φ‖) (norm_nonneg _) (fun n ω => Φ (finVec b e (σ n) pts ω))
    (fun n => by
      have hWr : (0 : ℝ) ≤ (σ n : ℝ) := Nat.cast_nonneg _
      refine Φ.continuous.measurable.comp ?_
      refine @Measurable.of_eval _ _ _ (growthSigma (σ n) ⌊((σ n : ℕ) : ℝ) * s⌋₊) _ _
        fun j => ?_
      exact (measurable_pathPower_adapted b (e (σ n)) (pts j).1 _).mono
        (growthSigma_mono (Nat.floor_mono (mul_le_mul_of_nonneg_left (hu j).2 hWr))) le_rfl)
    (fun n ω => abs_bcf_le Φ _)
  exact tendsto_nhds_unique hconv hzero

/-- **The transmission generator theorem**: `TransmissionGeneratorContract` from the input
hypotheses `MatchedTracesContract`, `GaussianAbsorptionContract`, `GaussianLpGradient` and
`GaussianPoincare` (with `productMartingaleAlong_holds`).
-/
theorem transmissionGenerator_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    TransmissionGeneratorContract :=
  transmissionGenerator_of_prod hMT hGA hLp hP (productMartingaleAlong_holds hMT hGA hLp hP)

end BlockBand.Transmission.Generator
