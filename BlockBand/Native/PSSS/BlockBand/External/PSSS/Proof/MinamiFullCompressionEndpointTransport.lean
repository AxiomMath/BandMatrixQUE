module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.PublicAmbientCompressionEndpointNull
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFixedPredecessorJointMeasurability

/-!
# Fixed-endpoint nullity after the sphere and block-product splits

This module transports the full-public ambient-compression endpoint
statement first through the exterior/selected product equivalence and then
through the uniform-sphere law.  The target interval remains the fixed
`Icc a b`; no auxiliary radial interval occurs here.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- For almost every sphere direction, exterior sample, and selected sample,
the full public deformation compressed along the embedded direction has no
fixed-endpoint atom except its canonical forced zero.  This is the
sphere-times-split-product endpoint transport used by the corrected Minami
Fatou step. -/
theorem uniformSphere_ae_exterior_ae_selected_fullCompression_fixedEndpoints
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (a b : ℝ) :
    ∀ᵐ φ ∂uniformSphere (dims j),
      ∀ᵐ Gext ∂BlockProductDisintegration.exteriorMeasure dims hd j,
        ∀ᵐ Gj ∂BlockProductDisintegration.selectedMeasure dims hd j,
          eigenCount
              (compressHermitian
                (publicBlockDeformation A₀
                  ((BlockProductDisintegration.split dims j).symm (Gext, Gj)))
                (selectedAmbientDirection j φ)) {a} =
              (if a = 0 then 1 else 0) ∧
            eigenCount
              (compressHermitian
                (publicBlockDeformation A₀
                  ((BlockProductDisintegration.split dims j).symm (Gext, Gj)))
                (selectedAmbientDirection j φ)) {b} =
              (if b = 0 then 1 else 0) := by
  filter_upwards [uniformSphere_norm_eq_one (hd j)] with φ hφ
  have hu : ‖selectedAmbientDirection j φ‖ = 1 := by simpa using hφ
  have hpublic := ae_publicBlock_compressHermitian_fixedEndpoints
    dims hd A₀ (selectedAmbientDirection j φ) hu a b
  have hpair :
      ∀ᵐ p ∂(BlockProductDisintegration.exteriorMeasure dims hd j).prod
          (BlockProductDisintegration.selectedMeasure dims hd j),
        eigenCount
              (compressHermitian
                (publicBlockDeformation A₀
                  ((BlockProductDisintegration.split dims j).symm p))
                (selectedAmbientDirection j φ)) {a} =
              (if a = 0 then 1 else 0) ∧
            eigenCount
              (compressHermitian
                (publicBlockDeformation A₀
                  ((BlockProductDisintegration.split dims j).symm p))
                (selectedAmbientDirection j φ)) {b} =
              (if b = 0 then 1 else 0) := by
    exact ((BlockProductDisintegration.measurePreserving_split dims hd j).symm
      (BlockProductDisintegration.split dims j)).quasiMeasurePreserving.ae hpublic
  exact MeasureTheory.Measure.ae_ae_of_ae_prod hpair

end PSSSNative.BlockBand.PSSS
