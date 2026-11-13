module

public import BlockBand.DeterminantScore.GelfandTsetlin
public import BlockBand.DeterminantScore.BorderLaw
public import BlockBand.DeterminantScore.BrascampLieb
public import BlockBand.DeterminantScore.NegativeSpreadInverse

/-!
# The spectral chain from Prékopa's theorem

Assuming Prékopa's theorem on log-concave marginals (`External.Prekopa.SourceContract`), this file
derives the ordered eigenvalue density of `K + G_m(t)`, the indexed spectral convexity statement
and the negative-spread statement.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SpectralChainHolds

open BlockBand.DeterminantScore

/-- The ordered eigenvalue density of `K + G_m(t)`, from Prékopa's theorem, Weyl integration and the
Gelfand–Tsetlin border law. -/
theorem orderedEigenDensity_holds (hP : BlockBand.External.Prekopa.SourceContract) :
    SpectralConvexity.OrderedEigenDensityStatement :=
  EigenDensity.orderedEigenDensity_of_weyl_gt hP WeylIntegration.weylIntegration_holds
    (GelfandTsetlin.gelfandTsetlin_of_border WeylIntegration.diagonalBorderLaw_holds)

/-- **Indexed spectral convexity** from Prékopa's theorem. -/
theorem indexedSpectralConvexity_holds (hP : BlockBand.External.Prekopa.SourceContract) :
    IndexedSpectralConvexityStatement :=
  SpectralConvexity.indexedSpectralConvexity_of (orderedEigenDensity_holds hP)
    (SpectralConvexity.BrascampLieb.brascampLieb hP)

/-- **The negative-spread statement** from Prékopa's theorem. -/
theorem negativeSpread_holds (hP : BlockBand.External.Prekopa.SourceContract) :
    NegativeSpreadStatement :=
  NegativeSpread.negativeSpread_of_convexity_of_prekopa (indexedSpectralConvexity_holds hP) hP

end BlockBand.DeterminantScore.SpectralChainHolds
