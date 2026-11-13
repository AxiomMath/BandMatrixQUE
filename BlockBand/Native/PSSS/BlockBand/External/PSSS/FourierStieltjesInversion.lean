module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.FourierRatioTransform
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fourier–Stieltjes inversion used by the APSSS criterion

This module derives the measure-pairing form of Fourier inversion from Mathlib's
Bochner Fourier inversion theorem.  In particular, inversion and the exchange with
a finite Borel measure are proved rather than supplied as hypotheses.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex FourierTransform FourierTransformInv MeasureTheory
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- The absolutely integrable product kernel occurring when Fourier inversion is
paired with a finite measure. -/
def fourierStieltjesKernel (f : V → ℂ) (p : V × V) : ℂ :=
  Complex.exp (((2 * Real.pi * inner ℝ p.2 p.1 : ℝ) : ℂ) * Complex.I) *
    𝓕 f p.2

end PSSSNative.BlockBand.PSSS
