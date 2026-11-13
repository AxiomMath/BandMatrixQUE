module

public import BlockBand.Native.CEH.ETH.BlockBand.Basic.Parameters
public import BlockBand.Native.CEH.BlockBand.Spectral.Measurable.OrderedSpectrum

/-!
# Physical bulk unfolding of ordered eigenvalues

This module implements the physical bulk unfolding.  For finite parameters `p`, bulk reference energy `E`, and the
increasing physical eigenvalue of rank `α`, the unfolded location is exactly

`p.L * ρ(E) * (λ_α - E)`,

The definition reuses the scalar affine unfolding from `Conventions` and the
increasing ordered spectrum `orderedEigenvalue`.  The continuity and measurability facts
below are the coordinate and finite-spectrum facts needed when the locations
are assembled into the later marked spectral process.  No random-matrix law,
bulk asymptotic, point-process convergence, eigenvector mark, or intensity
claim is made here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open Conventions

/-- The physical ordered
eigenvalue of rank `α`, centered at `E` and rescaled by the full dimension
`L = nW` and the semicircle density `ρ(E)`.

The definition imposes no bulk hypothesis: `IsBulkEnergy E` is needed only
when positivity or invertibility of the unfolding scale is used downstream. -/
def unfoldedEigenvalue (p : Params) (E : ℝ)
    (A : HermitianMatrix (Fin p.L)) (α : Fin p.L) : ℝ :=
  unfoldEigenvalue p.L E
    (orderedEigenvalue A (Fin.cast (Fintype.card_fin p.L).symm α))

/-- Expansion of the physical unfolding with the exact
factor `L ρ(E) (λ_α - E)`. -/
theorem unfoldedEigenvalue_eq (p : Params) (E : ℝ)
    (A : HermitianMatrix (Fin p.L)) (α : Fin p.L) :
    unfoldedEigenvalue p E A α =
      (p.L : ℝ) * semicircleDensity E *
        (orderedEigenvalue A (Fin.cast (Fintype.card_fin p.L).symm α) - E) := by
  rfl

/-- At fixed finite parameters, energy, and rank, the unfolded location is
continuous as a function of the physical Hermitian matrix. -/
theorem continuous_unfoldedEigenvalue (p : Params) (E : ℝ) (α : Fin p.L) :
    Continuous (fun A : HermitianMatrix (Fin p.L) =>
      unfoldedEigenvalue p E A α) := by
  rw [show (fun A : HermitianMatrix (Fin p.L) =>
      unfoldedEigenvalue p E A α) =
      fun A => (p.L : ℝ) * semicircleDensity E *
        (orderedEigenvalue A (Fin.cast (Fintype.card_fin p.L).symm α) - E) by
    funext A
    exact unfoldedEigenvalue_eq p E A α]
  exact continuous_const.mul
    ((continuous_orderedEigenvalue
      (Fin.cast (Fintype.card_fin p.L).symm α)).sub continuous_const)

/-- At fixed finite parameters, energy, and rank, the unfolded location is
Borel measurable in the physical Hermitian matrix. -/
theorem measurable_unfoldedEigenvalue (p : Params) (E : ℝ) (α : Fin p.L) :
    Measurable (fun A : HermitianMatrix (Fin p.L) =>
      unfoldedEigenvalue p E A α) :=
  (continuous_unfoldedEigenvalue p E α).measurable

/-- The complete finite vector of physically unfolded locations is continuous
in the entrywise topology on Hermitian matrices. -/
theorem continuous_unfoldedSpectrum (p : Params) (E : ℝ) :
    Continuous (fun A : HermitianMatrix (Fin p.L) =>
      fun α : Fin p.L => unfoldedEigenvalue p E A α) :=
  continuous_pi fun α => continuous_unfoldedEigenvalue p E α

/-- The complete finite vector of physically unfolded locations is Borel
measurable, ready for assembly into the finite marked spectral process. -/
theorem measurable_unfoldedSpectrum (p : Params) (E : ℝ) :
    Measurable (fun A : HermitianMatrix (Fin p.L) =>
      fun α : Fin p.L => unfoldedEigenvalue p E A α) :=
  (continuous_unfoldedSpectrum p E).measurable

end CEHNative.BlockBand
