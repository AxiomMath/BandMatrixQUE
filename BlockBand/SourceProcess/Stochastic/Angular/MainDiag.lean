module

public import BlockBand.SourceProcess.Stochastic.Angular.Main
public import BlockBand.SourceProcess.Stochastic.Angular.LaplacianDiag

/-!
# Complex angular martingale problem: reduction to `GenericConditioning`

With `arrayLaplacianDiag`, the proposition `ArrayLaplacian` holds unconditionally, and the
complex angular martingale problem depends only on `GenericConditioning`:
`complexAngularContract_of_conditioning : (∀ N, GenericConditioning N) → ComplexAngularContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open BlockBand.Internal.Contracts.TransmissionAngular

/-- `ArrayLaplacian N r` (both halves) holds unconditionally. -/
theorem arrayLaplacian (N r : ℕ) : ArrayLaplacian N r :=
  arrayLaplacian_of_diag (arrayLaplacianDiag N r)

/-- **The complex angular martingale problem from `GenericConditioning` alone.** -/
theorem complexAngularContract_of_conditioning (hC : ∀ N, GenericConditioning N) :
    ComplexAngularContract :=
  complexAngularContract_of_diag arrayLaplacianDiag hC

end BlockBand.SourceProcess.Stochastic.ComplexAngular
