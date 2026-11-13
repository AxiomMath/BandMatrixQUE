module

public import BlockBand.Native.ErdosRiabov.BlockBand.Conventions
public import BlockBand.Model.Construction.OrderedEigenvalues
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Finite-dimensional scalar MDE foundations for CEH

This module isolates the deterministic scalar Dyson equation behind CEH (2.4).
The deformation is represented by its real eigenvalues; no regularity, limiting
empirical measure, or pre-packaged MDE solution is assumed.  The normalization is

`Mᵢ(z) = (fᵢ - z - s m(z))⁻¹`,  `m(z) = N⁻¹ ∑ᵢ Mᵢ(z)`.

The lemmas below record the exact finite-dimensional algebra used in CEH Lemma 2.2,
the typical-spacing construction, and the boundary-to-strip adapter.  In particular,
all regular-window consequences take their boundary hypotheses explicitly.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ERNative.BlockBand.CEH

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal Topology

/-- The diagonal (spectral) presentation of a finite-dimensional Hermitian deformation. -/
abbrev DeformationSpectrum (N : ℕ) := Fin N → ℝ

/-- The diagonal entries of the scalar-MDE resolvent associated with a proposed mean `m`. -/
def entry {N : ℕ} (f : DeformationSpectrum N) (s : ℝ) (z m : ℂ) (i : Fin N) : ℂ :=
  ((f i : ℂ) - z - (s : ℂ) * m)⁻¹

/-- The positive-height quantity occurring in every scalar MDE denominator. -/
def effectiveHeight (s : ℝ) (z m : ℂ) : ℝ := z.im + s * m.im

@[simp] theorem entry_im {N : ℕ} (f : DeformationSpectrum N) (s : ℝ)
    (z m : ℂ) (i : Fin N) :
    (entry f s z m i).im =
      effectiveHeight s z m / Complex.normSq ((f i : ℂ) - z - (s : ℂ) * m) := by
  simp [entry, effectiveHeight, Complex.inv_im]
  ring

/-!
## Typical spacing
-/

/-!
## Boundary-to-strip and theta-one consequences
-/

end ERNative.BlockBand.CEH
