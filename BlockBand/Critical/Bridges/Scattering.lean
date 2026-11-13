module

public import BlockBand.Internal.Contracts.Critical
public import BlockBand.Internal.Contracts.TransmissionStatements
public import BlockBand.Transmission.PositiveResolvent

/-!
# Scattering vocabulary: identification of two definitions

The old-port scattering matrix, the conductance and the imaginary part of a matrix used in the
critical statements agree with the corresponding transmission-path objects:
`Critical.oldScattering = TransmissionStatements.twoPortScattering`,
`Critical.conductance r = conductanceOf (1 - rᴴ r)` and
`Critical.imPart = Transmission.matrixImaginaryPart`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Critical.Bridges

open BlockBand.Internal.Contracts
open scoped Matrix

/-- The old-port scattering matrix is the two-port scattering matrix. -/
theorem oldScattering_eq_twoPortScattering (b e : ℝ) {W : ℕ}
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Critical.oldScattering b e X = TransmissionStatements.twoPortScattering b e X := by
  unfold Critical.oldScattering TransmissionStatements.twoPortScattering
    TransmissionStatements.twoPortResolvent TransmissionPath.etaZ
  congr 2
  push_cast
  ring

/-- The conductance of `r` is `conductanceOf (1 - rᴴ r)`. -/
theorem conductance_eq_conductanceOf {W : ℕ} (r : Matrix (Fin W) (Fin W) ℂ) :
    Critical.conductance r = TransmissionPath.conductanceOf (1 - rᴴ * r) := rfl

/-- The two definitions of the imaginary part of a matrix agree. -/
theorem imPart_eq_matrixImaginaryPart {ι : Type*} [Fintype ι] (K : Matrix ι ι ℂ) :
    Critical.imPart K = BlockBand.Transmission.matrixImaginaryPart K := by
  unfold Critical.imPart BlockBand.Transmission.matrixImaginaryPart
  congr 1
  field_simp
  ring_nf
  simp [Complex.I_sq]

end BlockBand.Critical.Bridges
