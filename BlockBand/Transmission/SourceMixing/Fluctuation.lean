module

public import BlockBand.Transmission.PassiveLayer.TMMain
public import BlockBand.Transmission.PassiveLayer.Consistency

/-!
# One-step fluctuation bound for passive source mixing

Law `freshLaw W b` (one fresh layer, deterministic passive old input `X`); Euclidean vector norms;
constants depend on `b, E, p` only, uniform in `W ≥ W₀`, `X`, `u, v`. Hypotheses
`GaussianAbsorptionContract` and `GaussianLpGradient`; the proof applies
`PassiveLayer.oneStepFluctuation_of_passiveBounds` to `passiveBounds_holds`.

The `oneStepFluctuation` field of `PassiveSourceMixingContract`: for `p ≥ 1` the centred bilinear
forms `⟨u, (U - EU) v⟩` of the fresh-layer matrix `U` and of the transported `F` have `L^p` norm
`≤ C W^{-1/2} ‖u‖ ‖v‖`, deduced from the passive one-layer bounds.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveLayer
open scoped ComplexOrder

/-- **`PassiveSourceMixingContract.oneStepFluctuation`**, from `GaussianAbsorptionContract` and
`GaussianLpGradient`. -/
theorem oneStepFluctuation_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 1 ≤ p → ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ u v : Fin W → ℂ,
        eLpNorm (fun ω => bilinear u (freshU b E X ω -
            matrixExpect (freshLaw W b) (freshU b E X)) v) (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) ∧
        eLpNorm (fun ω => bilinear u (freshTransportedF b E X ω -
            matrixExpect (freshLaw W b) (freshTransportedF b E X)) v) (ENNReal.ofReal p)
            (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) :=
  oneStepFluctuation_of_passiveBounds (passiveBounds_holds hGA hLp)

example (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (P : PassiveSourceMixingContract) : PassiveSourceMixingContract :=
  ⟨P.mixing, P.finiteConductance, P.oneStepMean, oneStepFluctuation_holds hGA hLp⟩

end BlockBand.Transmission.SourceMixing
