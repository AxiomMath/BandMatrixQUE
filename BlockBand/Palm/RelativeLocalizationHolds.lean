module

public import BlockBand.Palm.RelativeLocalizationReference

/-!
# `RelativeLocalizationContract` (constructor)

The relative localization lemma, with the moving-centre short-flow forms.

Hypotheses (the Itô and Dyson Brownian motion hypotheses are needed for every matrix size `N`,
so they are quantified `∀ N`; stopping is used in dimension `1`):

* `hIto : ∀ N, SemimartingaleItoFormula (N + N)` (state `(λ, v) ∈ ℝ^{N+N}`),
* `hStop : StoppedSemimartingale 1` (the tilted weighted mass),
* `hDBM : ∀ N, DysonBrownianMotion N`,
* the Gaussian inputs `hLp : GaussianLpGradient`, `hIBP : MultivariateGaussianIBP`, through
  `BlockBand.Palm.GoodEvent.spectralGoodEvent_holds` (`SpectralGoodEventContract`) and
  `spectralGoodEvent_s8` (the finer-scale good event).

`relativeLocalization_of` takes `hR : SpectralGoodEventContract` for the reference field and the
Gaussian inputs for the short fields; `relativeLocalization_holds` discharges `hR` with
`spectralGoodEvent_holds hLp hIBP`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs

/-- The reference field from the Itô, stopping and Dyson Brownian motion hypotheses and the
good event. -/
theorem relativeLocalization_reference (hIto : ∀ N, SemimartingaleItoFormula (N + N))
    (hStop : StoppedSemimartingale 1) (hDBM : ∀ N, DysonBrownianMotion N)
    (hR : SpectralGoodEventContract) :
    ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
    ∀ b₀ : ℝ, 0 < b₀ → ∀ Cw D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
      let t : ℝ := (N : ℝ) ^ (-(1 / 500 : ℝ))
      let a : ℝ := c - t
      let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊
      let w : ℕ := ⌈(N : ℝ) * Real.sqrt t * (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊
      flowLaw N a {ω | ∃ k : Fin N, |flowEigenvalue F a ω c k - E| ≤ Cw / N ∧
          ∃ P, BackwardPropagator (referenceGenerator F a b₀ ω ℓ) a c P ∧
            ENNReal.ofReal ((N : ℝ) ^ (-D)) <
              ∫⁻ s in Set.Icc a c, ENNReal.ofReal (∑ j : Fin N,
                (if Int.natAbs ((j : ℤ) -
                    ((Finset.univ.filter fun l : Fin N => flowEigenvalue F a ω a l ≤ E).card : ℤ)) ≤ w
                  then 0 else 1) * P s k j)} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
  referenceFiniteSpeed_holds hIto hStop hDBM hR

/-- **`RelativeLocalizationContract`** from the Itô, stopping and Dyson Brownian motion
hypotheses, `SpectralGoodEventContract` and the Gaussian inputs (for the finer-scale good event
of the short fields). -/
theorem relativeLocalization_of (hIto : ∀ N, SemimartingaleItoFormula (N + N))
    (hStop : StoppedSemimartingale 1) (hDBM : ∀ N, DysonBrownianMotion N)
    (hR : SpectralGoodEventContract) (hLp : GaussianLpGradient)
    (hIBP : MultivariateGaussianIBP) : RelativeLocalizationContract :=
  ⟨referenceFiniteSpeed_holds hIto hStop hDBM hR, shortRow_holds hIto hStop hDBM hLp hIBP,
    shortColumn_holds hIto hStop hDBM hLp hIBP⟩

/-- **`RelativeLocalizationContract`**, with `SpectralGoodEventContract` discharged by
`spectralGoodEvent_holds hLp hIBP`. -/
theorem relativeLocalization_holds (hIto : ∀ N, SemimartingaleItoFormula (N + N))
    (hStop : StoppedSemimartingale 1) (hDBM : ∀ N, DysonBrownianMotion N)
    (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP) :
    RelativeLocalizationContract :=
  relativeLocalization_of hIto hStop hDBM
    (BlockBand.Palm.GoodEvent.spectralGoodEvent_holds hLp hIBP) hLp hIBP

end BlockBand.Palm.RelativeLocalization
