module

public import BlockBand.Layers.GaussianAbsorption
public import BlockBand.Layers.TraceCovariance
public import BlockBand.Layers.TraceFluctuation

/-!
# The trace–matrix lemma: assembled constructor

Both fields of `TraceMatrixContract` (`traceMatrix_holds`), from `ConditionalBlockGUECount` (through
`gaussianAbsorption_holds`) and `GaussianLpGradient`, each supplied by a result of another module:
* the covariance field (the trace–matrix covariance bound): `traceCovariance_holds` (Ornstein–Uhlenbeck
  covariance identity, contraction `‖𝒱(K)‖ ≤ 10‖K‖/W`, absorption moments, regularization
  `κ → 0`);
* the fluctuation field (the fresh trace fluctuation bound): `traceFluctuation_holds` (Gaussian `L^p`
  gradient inequality, gradient `≤ 4‖D‖‖𝒢‖²/W`, absorption moments).

Law: `layerLaw W b σ` (fresh layer; deterministic Hermitian `X`, i.e. conditional on the
independent deformation), operator norms, constants as in `TraceMatrixContract` (chosen before `W`
and all data).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open BlockBand.Internal.Contracts

/-- **The trace–matrix lemma**, constructor of `TraceMatrixContract`, from
`ConditionalBlockGUECount` (the PSSS count) and `GaussianLpGradient`. -/
theorem traceMatrix_holds (hcount : Inputs.ConditionalBlockGUECount)
    (hgrad : Inputs.GaussianLpGradient) : Layers.TraceMatrixContract :=
  ⟨traceCovariance_holds (gaussianAbsorption_holds hcount),
    traceFluctuation_holds hgrad (gaussianAbsorption_holds hcount)⟩

end BlockBand.Layers
