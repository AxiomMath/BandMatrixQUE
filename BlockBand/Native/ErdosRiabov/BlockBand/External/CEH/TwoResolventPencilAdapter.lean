module

public import BlockBand.Native.ErdosRiabov.BlockBand.Analysis.ResolventIdentities
public import BlockBand.Native.ErdosRiabov.BlockBand.Conventions
public import Mathlib.Analysis.Real.Sqrt
public import BlockBand.Native.ErdosRiabov.BlockBand.External.CEH.MDE

/-!
# Concrete CEH MDE and resolvent pencils

This module connects the scalar finite-dimensional CEH MDE to the matrix
pencils used by the exact two-resolvent identities.  The coupling `lambda` is
real and nonnegative, the self-energy is `lambda ^ 2`, and the deformation and
noise matrices are Hermitian.  The lower-half-plane objects are obtained by
conjugate transpose, rather than postulated independently.

The final four theorems are the `++`, `+-`, `-+`, and `--` versions of the
exact algebraic identity CEH (5.20).  They contain no local-law estimate,
stochastic domination, Gaussian integration by parts, or assumption packaging
CEH Lemma 5.6.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand.External.CEH

open Matrix
open scoped BigOperators ComplexConjugate

namespace PencilAdapter

abbrev Spectrum (N : ℕ) := ERNative.BlockBand.CEH.DeformationSpectrum N

/-- Upper spectral parameter `E+iη`. -/
def plusParameter (E eta : ℝ) : ℂ := (E : ℂ) + Complex.I * eta

/-- Lower spectral parameter `E-iη`. -/
def minusParameter (E eta : ℝ) : ℂ := (E : ℂ) - Complex.I * eta

@[simp] theorem star_plusParameter (E eta : ℝ) :
    star (plusParameter E eta) = minusParameter E eta := by
  apply Complex.ext <;> simp [plusParameter, minusParameter]

@[simp] theorem mdeEntry_star {N : ℕ} (f : Spectrum N)
    (s : ℝ) (z m : ℂ) (i : Fin N) :
    ERNative.BlockBand.CEH.entry f s (star z) (star m) i =
      star (ERNative.BlockBand.CEH.entry f s z m i) := by
  simp [ERNative.BlockBand.CEH.entry]

end PencilAdapter
end ERNative.BlockBand.External.CEH
