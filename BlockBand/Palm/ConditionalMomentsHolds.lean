module

public import BlockBand.Palm.MomentFlow.Step
public import BlockBand.Palm.MomentFlow.PropLongShortHolds
public import BlockBand.Palm.MomentFlow.PropP6Holds
public import BlockBand.Palm.MomentFlow.PropFlatHolds
public import BlockBand.Palm.MomentFlow.MultiFinal
public import BlockBand.Palm.MomentFlow.MultiColFinal
public import BlockBand.Palm.FreshPalmAssembly

/-!
# The conditional-moments lemma and the fresh Palm theorem

The conditional-moments lemma and the fresh Palm theorem, assembled from the propagation and
flattening estimates, under the stochastic-calculus, Gaussian and Dyson Brownian motion inputs
taken as hypotheses.

* `cmWin_holds`: the windowed form `∀ r M, CMWin r M`, i.e. the estimate for each fixed particle
  configuration whose labels lie in the shrinking bulk windows `InRank k₀ (M·w)`.
* `conditionalMoments_holds`: the conditional-moments lemma.
* `freshPalmContract_holds`: the fresh Palm theorem.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Palm

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.Transmission BlockBand.Palm.CoarseRelative
open BlockBand.Palm.MomentFlow

/-- **Conditional-moments lemma, windowed form**: `CMWin r M` for every `r` and window multiple
`M`. -/
theorem cmWin_holds (hIto : ∀ d, SemimartingaleItoFormula d)
    (hStop : StoppedSemimartingale 1) (hDBM : ∀ N : ℕ, DysonBrownianMotion N)
    (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification) (hLp : GaussianLpGradient)
    (hIBP : MultivariateGaussianIBP) : ∀ r : ℕ, ∀ M : ℝ, CMWin r M :=
  have hMS : MultiShortFiniteSpeed := multiShortFiniteSpeed_holds hIto hStop hDBM hLp hIBP
  have hCol : MultiShortColumnSpeed := multiShortColumnSpeed_holds hIto hStop hDBM hLp hIBP
  cmWin_all_of_step (cmWin_step hELG hMDE hLp hIBP hDBM
    (propagationP6_holds hCol hLp hIBP hDBM)
    (longShortPropagation_holds hMS hELG hMDE hLp hIBP hDBM)
    (flattening_holds hMS hCol hELG hMDE hLp hIBP hDBM))

/-- **Conditional-moments lemma**, single-site form `ConditionalMomentsStatement`. -/
theorem conditionalMoments_holds (hIto : ∀ d, SemimartingaleItoFormula d)
    (hStop : StoppedSemimartingale 1) (hDBM : ∀ N : ℕ, DysonBrownianMotion N)
    (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification) (hLp : GaussianLpGradient)
    (hIBP : MultivariateGaussianIBP) :
    FreshPalmAssembly.ConditionalMomentsStatement :=
  have hMS : MultiShortFiniteSpeed := multiShortFiniteSpeed_holds hIto hStop hDBM hLp hIBP
  have hCol : MultiShortColumnSpeed := multiShortColumnSpeed_holds hIto hStop hDBM hLp hIBP
  conditionalMoments_of hELG hMDE hLp hIBP hDBM
    (propagationP6_holds hCol hLp hIBP hDBM)
    (longShortPropagation_holds hMS hELG hMDE hLp hIBP hDBM)
    (flattening_holds hMS hCol hELG hMDE hLp hIBP hDBM)

/-- **Fresh Palm theorem** (`FreshPalmContract`). -/
theorem freshPalmContract_holds (hIto : ∀ d, SemimartingaleItoFormula d)
    (hStop : StoppedSemimartingale 1) (hDBM : ∀ N : ℕ, DysonBrownianMotion N)
    (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification) (hLp : GaussianLpGradient)
    (hIBP : MultivariateGaussianIBP) : FreshPalmContract :=
  FreshPalmAssembly.freshPalm_of_conditionalMoments
    (conditionalMoments_holds hIto hStop hDBM hELG hMDE hLp hIBP)

end BlockBand.Palm
