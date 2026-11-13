module

public import BlockBand.Critical.BoundaryMean.Strict
public import BlockBand.Critical.BoundaryMean.Radial

/-!
# Exact boundary mean: reduction to the Hermitian collar mean

`HermitianCollarMeanStatement` implies `ExactBoundaryMeanContract`, through the strict clause
and the removal of the radial regulator.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.BoundaryMean

/-- **Reduction of the exact boundary mean theorem** to the Hermitian collar mean statement
for Hermitian old responses. -/
theorem exactBoundaryMean_of_hermitian (hH : HermitianCollarMeanStatement) :
    BlockBand.Internal.Contracts.Critical.ExactBoundaryMeanContract :=
  exactBoundaryMean_of_strict (strictClause_of_hermitian hH)

end BlockBand.Critical.BoundaryMean
