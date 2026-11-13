module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFullCompressionFactorialBound
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFixedSelectedPredecessor
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.UniformVector

/-!
# Integrated fixed-target selected predecessor bound

The selected/exterior representation of the corrected predecessor is returned
to the public block-product law, direction by direction.  The full
ambient endpoint theorem and rank-one Fatou bound then control it uniformly,
and probability normalization of the sphere law removes the direction
integral.  The interval remains the fixed target `Icc a b` throughout.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 900000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- For a unit selected direction, exterior/selected disintegration of the
fixed-target weight is bounded by the order-`r` public factorial estimate. -/
theorem lintegral_fixedSelectedPredecessor_le_of_norm_eq_one
    {C : ℝ} {r k : ℕ} (hind : PublicFactorialAtOrder C r)
    (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (φ : EuclideanSpace ℂ (Fin (dims j))) (hφ : ‖φ‖ = 1)
    {a b : ℝ} (hab : a ≤ b) :
    (∫⁻ Gext, ∫⁻ Gj,
      fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
        ∂BlockProductDisintegration.selectedMeasure dims hd j
      ∂BlockProductDisintegration.exteriorMeasure dims hd j) ≤
      ENNReal.ofReal (C * (∑ i, (dims i : ℝ)) * (b - a)) ^ r := by
  let F : BlockGUE.PublicBlockSample dims → ℝ≥0∞ := fun G =>
    fixedSelectedPredecessorWeight A₀ j φ a b r
      (BlockProductDisintegration.split dims j G)
  have hF : Measurable F :=
    (measurable_fixedSelectedPredecessorWeight dims A₀ j φ a b r).comp
      (BlockProductDisintegration.split dims j).measurable
  have hdis := BlockProductDisintegration.lintegral_publicBlockProduct_eq_iterated
    dims hd j F hF
  have hiter :
      (∫⁻ Gext, ∫⁻ Gj,
        fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
          ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂BlockProductDisintegration.exteriorMeasure dims hd j) =
      ∫⁻ G, F G ∂BlockGUE.publicBlockProductMeasure dims hd := by
    rw [hdis]
    simp only [F, MeasurableEquiv.apply_symm_apply]
  rw [hiter]
  have hpoint : F = fun G =>
      ((eigenCount
        (compressHermitian (publicBlockDeformation A₀ G)
          (selectedAmbientDirection j φ)) (Set.Icc a b) -
        (if (0 : ℝ) ∈ Set.Icc a b then 1 else 0)).descFactorial r : ℝ≥0∞) := by
    funext G
    simpa [F] using fixedSelectedPredecessorWeight_eq_literal_compression
      A₀ j φ hφ a b r
      (BlockProductDisintegration.split dims j G).1
      (BlockProductDisintegration.split dims j G).2
  rw [hpoint]
  exact publicBlock_lintegral_compressionPredecessor_le_of_publicFactorialAtOrder'
    hind dims hd A₀ (selectedAmbientDirection j φ)
      (by simpa using hφ) hab

/-- The complete sphere/exterior/selected average of the corrected fixed-target
predecessor is bounded by the same order-`r` public factorial constant. -/
theorem lintegral_uniformSphere_fixedSelectedPredecessor_le
    {C : ℝ} {r k : ℕ} (hind : PublicFactorialAtOrder C r)
    (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {a b : ℝ} (hab : a ≤ b) :
    (∫⁻ φ, ∫⁻ Gext, ∫⁻ Gj,
      fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
        ∂BlockProductDisintegration.selectedMeasure dims hd j
      ∂BlockProductDisintegration.exteriorMeasure dims hd j
      ∂uniformSphere (dims j)) ≤
      ENNReal.ofReal (C * (∑ i, (dims i : ℝ)) * (b - a)) ^ r := by
  let B : ℝ≥0∞ :=
    ENNReal.ofReal (C * (∑ i, (dims i : ℝ)) * (b - a)) ^ r
  calc
    _ ≤ ∫⁻ _φ, B ∂uniformSphere (dims j) := by
      apply lintegral_mono_ae
      filter_upwards [uniformSphere_norm_eq_one (hd j)] with φ hφ
      exact lintegral_fixedSelectedPredecessor_le_of_norm_eq_one
        hind dims hd j A₀ φ hφ hab
    _ = B := by simp

end PSSSNative.BlockBand.PSSS
