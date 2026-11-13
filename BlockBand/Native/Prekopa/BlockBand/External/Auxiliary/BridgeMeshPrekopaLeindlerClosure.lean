module

public import BlockBand.Native.Prekopa.BlockBand.External.Auxiliary.ScalarPrekopaLeindlerClosure
public import BlockBand.Native.Prekopa.BlockBand.External.Auxiliary.BridgeMeshPrekopaLeindlerTensorization

/-!
# Unconditional Prékopa–Leindler on finite bridge meshes

This module proves Prékopa–Leindler for every finite Cartesian power of real
Lebesgue measure, hence on the finite bridge meshes: the scalar theorem
`scalarPrekopaLeindler` is tensorized by `measurePrekopaLeindler_euclidean_pi`.
The empty product is included, so the result holds in every dimension with no
positivity assumption.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PrekopaNative.BlockBand

open MeasureTheory

/-- The Prékopa–Leindler property for every finite Cartesian power of real
Lebesgue measure. -/
theorem measurePrekopaLeindler_euclidean_pi_unconditional (n : ℕ) :
    MeasurePrekopaLeindler (Fin n → ℝ)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) :=
  measurePrekopaLeindler_euclidean_pi scalarPrekopaLeindler n

end PrekopaNative.BlockBand
