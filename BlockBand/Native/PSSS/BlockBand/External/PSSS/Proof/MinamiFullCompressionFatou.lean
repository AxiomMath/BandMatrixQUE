module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFixedSphereInsertion
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiRankOneConditioning

/-!
# Fixed-target full-public compression Fatou bridge

After the direction-independent sphere insertion in PSSS (2.13), the fixed
`Icc a b` predecessor may be passed to the ambient compression of the full
original public deformation.  This module performs the positive rank-one-ray
Fatou passage directly under the full public block-product law.  No moving
`Icc (-xi) xi` predecessor or dyadic compression weight is imported or used.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 700000

namespace PSSSNative.BlockBand.PSSS

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- Every fixed-target factorial count on a full public rank-one ray is
measurable in the public block sample. -/
theorem measurable_publicBlock_rankOneRay_descFactorial
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (u : EuclideanSpace ℂ (BlockGUE.Index dims)) (a b : ℝ) (r n : ℕ) :
    Measurable (fun G : BlockGUE.PublicBlockSample dims =>
      ((eigenCount
        (rankOneShift (publicBlockDeformation A₀ G) u (n : ℝ))
        (Set.Icc a b)).descFactorial r : ℝ≥0∞)) := by
  rw [show (fun G : BlockGUE.PublicBlockSample dims =>
      ((eigenCount
        (rankOneShift (publicBlockDeformation A₀ G) u (n : ℝ))
        (Set.Icc a b)).descFactorial r : ℝ≥0∞)) =
    fun G => ((eigenCount
      (publicBlockDeformation (rankOneShift A₀ u (n : ℝ)) G)
      (Set.Icc a b)).descFactorial r : ℝ≥0∞) by
      funext G
      rw [rankOneShift_publicBlockDeformation]]
  exact (measurable_of_countable
    (f := fun q : ℕ => (q.descFactorial r : ℝ≥0∞))).comp
      ((measurable_eigenCount_Icc a b).comp
        (measurable_publicBlockDeformation dims
          (rankOneShift A₀ u (n : ℝ))))

/-- Fatou passage from the canonical-zero-subtracted compression predecessor
of the full public deformation to its positive ambient rank-one ray. -/
theorem publicBlock_lintegral_compressionPredecessor_le_liminf_rankOneRay
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (u : EuclideanSpace ℂ (BlockGUE.Index dims)) (hu : ‖u‖ = 1)
    {a b : ℝ} (hab : a ≤ b) (r : ℕ)
    (hend : ∀ᵐ G ∂BlockGUE.publicBlockProductMeasure dims hd,
      eigenCount (compressHermitian (publicBlockDeformation A₀ G) u) {a} =
          (if a = 0 then 1 else 0) ∧
        eigenCount (compressHermitian (publicBlockDeformation A₀ G) u) {b} =
          (if b = 0 then 1 else 0)) :
    (∫⁻ G,
      ((eigenCount (compressHermitian (publicBlockDeformation A₀ G) u)
        (Set.Icc a b) -
          (if (0 : ℝ) ∈ Set.Icc a b then 1 else 0)).descFactorial r : ℝ≥0∞)
      ∂BlockGUE.publicBlockProductMeasure dims hd) ≤
      liminf (fun n : ℕ =>
        ∫⁻ G,
          ((eigenCount
            (rankOneShift (publicBlockDeformation A₀ G) u (n : ℝ))
            (Set.Icc a b)).descFactorial r : ℝ≥0∞)
          ∂BlockGUE.publicBlockProductMeasure dims hd) atTop := by
  let μ := BlockGUE.publicBlockProductMeasure dims hd
  let F : ℕ → BlockGUE.PublicBlockSample dims → ℝ≥0∞ := fun n G =>
    ((eigenCount (rankOneShift (publicBlockDeformation A₀ G) u (n : ℝ))
      (Set.Icc a b)).descFactorial r : ℝ≥0∞)
  have hpoint : ∀ᵐ G ∂μ,
      ((eigenCount (compressHermitian (publicBlockDeformation A₀ G) u)
          (Set.Icc a b) -
        (if (0 : ℝ) ∈ Set.Icc a b then 1 else 0)).descFactorial r : ℝ≥0∞) =
        liminf (fun n => F n G) atTop := by
    filter_upwards [hend] with G hG
    have hreal := eventually_rankOne_predecessorFactorial_eq_compression
      (publicBlockDeformation A₀ G) u hu hab hG.1 hG.2 r
    have hnat : ∀ᶠ n : ℕ in atTop,
        (eigenCount
          (rankOneShift (publicBlockDeformation A₀ G) u (n : ℝ))
          (Set.Icc a b)).descFactorial r =
        (eigenCount (compressHermitian (publicBlockDeformation A₀ G) u)
          (Set.Icc a b) -
          (if (0 : ℝ) ∈ Set.Icc a b then 1 else 0)).descFactorial r :=
      tendsto_natCast_atTop_atTop.eventually hreal
    let q : ℝ≥0∞ :=
      ((eigenCount (compressHermitian (publicBlockDeformation A₀ G) u)
        (Set.Icc a b) -
        (if (0 : ℝ) ∈ Set.Icc a b then 1 else 0)).descFactorial r : ℝ≥0∞)
    have hevent : ∀ᶠ n : ℕ in atTop, F n G = q := by
      filter_upwards [hnat] with n hn
      dsimp only [F, q]
      exact_mod_cast hn
    have hevent' : ∀ᶠ n : ℕ in atTop, q = F n G := by
      filter_upwards [hevent] with n hn
      exact hn.symm
    have ht : Tendsto (fun n => F n G) atTop (𝓝 q) :=
      tendsto_const_nhds.congr' hevent'
    exact ht.liminf_eq.symm
  calc
    _ = ∫⁻ G, liminf (fun n => F n G) atTop ∂μ :=
      lintegral_congr_ae hpoint
    _ ≤ liminf (fun n => ∫⁻ G, F n G ∂μ) atTop := by
      apply lintegral_liminf_le
      intro n
      exact measurable_publicBlock_rankOneRay_descFactorial
        dims A₀ u a b r n

/-- The full-public fixed-target compression predecessor is bounded directly
by the order-`r` public factorial induction hypothesis. -/
theorem publicBlock_lintegral_compressionPredecessor_le_of_publicFactorialAtOrder
    {C : ℝ} {r k : ℕ} (hind : PublicFactorialAtOrder C r)
    (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (u : EuclideanSpace ℂ (BlockGUE.Index dims)) (hu : ‖u‖ = 1)
    {a b : ℝ} (hab : a ≤ b)
    (hend : ∀ᵐ G ∂BlockGUE.publicBlockProductMeasure dims hd,
      eigenCount (compressHermitian (publicBlockDeformation A₀ G) u) {a} =
          (if a = 0 then 1 else 0) ∧
        eigenCount (compressHermitian (publicBlockDeformation A₀ G) u) {b} =
          (if b = 0 then 1 else 0)) :
    (∫⁻ G,
      ((eigenCount (compressHermitian (publicBlockDeformation A₀ G) u)
        (Set.Icc a b) -
          (if (0 : ℝ) ∈ Set.Icc a b then 1 else 0)).descFactorial r : ℝ≥0∞)
      ∂BlockGUE.publicBlockProductMeasure dims hd) ≤
      ENNReal.ofReal (C * (∑ i, (dims i : ℝ)) * (b - a)) ^ r := by
  refine (publicBlock_lintegral_compressionPredecessor_le_liminf_rankOneRay
    dims hd A₀ u hu hab r hend).trans ?_
  apply Filter.liminf_le_of_frequently_le'
  apply Filter.Eventually.frequently
  filter_upwards with n
  rw [show (fun G : BlockGUE.PublicBlockSample dims =>
      ((eigenCount
        (rankOneShift (publicBlockDeformation A₀ G) u (n : ℝ))
        (Set.Icc a b)).descFactorial r : ℝ≥0∞)) =
    fun G => ((eigenCount
      (publicBlockDeformation (rankOneShift A₀ u (n : ℝ)) G)
      (Set.Icc a b)).descFactorial r : ℝ≥0∞) by
      funext G
      rw [rankOneShift_publicBlockDeformation]]
  exact hind dims hd (rankOneShift A₀ u (n : ℝ)) a b hab

end PSSSNative.BlockBand.PSSS
