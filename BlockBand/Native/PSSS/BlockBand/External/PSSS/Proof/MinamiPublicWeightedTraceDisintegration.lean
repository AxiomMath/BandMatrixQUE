module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiPublicWeightedPerronFatou
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WegnerTonelliAssembly

/-!
# Full-public predecessor weighted trace disintegration

The weight is `(N_[a,b] - 1).descFactorial r` for the original full
public deformation.  This module carries it through the full trace's block
sum and through the exact exterior/selected product split.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 1500000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- The full-public predecessor is measurable. -/
theorem measurable_fullPublicFixedPredecessorWeight
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (a b : ℝ) (r : ℕ) :
    Measurable (fullPublicFixedPredecessorWeight A₀ a b r) := by
  unfold fullPublicFixedPredecessorWeight
  have hcount :=
    measurable_publicBlockDeformation_eigenCount_Icc dims A₀ a b
  have hn : Measurable (fun G : BlockGUE.PublicBlockSample dims =>
      eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b) - 1) := by
    fun_prop
  exact Measurable.ennreal_descFactorial _ hn r

/-- Fixed-energy weighted full trace is bounded by the sum of the exactly
split weighted selected-block traces. -/
theorem lintegral_fullPublicPredecessor_mul_regulatedTrace_le_sum_split
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (a b : ℝ) (r : ℕ) (e eta : ℝ) :
    (∫⁻ G,
      fullPublicFixedPredecessorWeight A₀ a b r G *
        publicBlockRegulatedTrace A₀ e eta G
      ∂BlockGUE.publicBlockProductMeasure dims hd) ≤
    ∑ j : Fin k, ∫⁻ Gext, ∫⁻ Gj,
      fullPublicFixedPredecessorWeight A₀ a b r
          ((BlockProductDisintegration.split dims j).symm (Gext, Gj)) *
        publicBlockRegulatedSelectedTrace A₀ j e eta
          ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
      ∂BlockProductDisintegration.selectedMeasure dims hd j
      ∂BlockProductDisintegration.exteriorMeasure dims hd j := by
  let q := fullPublicFixedPredecessorWeight A₀ a b r
  have hq : Measurable q :=
    measurable_fullPublicFixedPredecessorWeight dims A₀ a b r
  calc
    _ ≤ ∫⁻ G, ∑ j : Fin k,
        q G * publicBlockRegulatedSelectedTrace A₀ j e eta G
        ∂BlockGUE.publicBlockProductMeasure dims hd := by
      apply lintegral_mono
      intro G
      unfold publicBlockRegulatedTrace publicBlockRegulatedSelectedTrace
      dsimp only
      rw [neg_im_publicBlockRegulatedTrace_eq_sum]
      rw [← Finset.mul_sum]
      apply mul_le_mul_right
      simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
        ofReal_finsetSum_le Finset.univ (fun j : Fin k =>
          -(((((((publicBlockDeformation A₀ G).1 -
            (e : ℂ) • (1 : Matrix (BlockGUE.Index dims)
              (BlockGUE.Index dims) ℂ)) +
            Complex.I • (eta • (1 : Matrix (BlockGUE.Index dims)
              (BlockGUE.Index dims) ℂ)))⁻¹).submatrix
                (fun x : Fin (dims j) => ⟨j, x⟩)
                (fun x : Fin (dims j) => ⟨j, x⟩)).trace).im))
    _ = ∑ j : Fin k, ∫⁻ G,
        q G * publicBlockRegulatedSelectedTrace A₀ j e eta G
        ∂BlockGUE.publicBlockProductMeasure dims hd := by
      rw [MeasureTheory.lintegral_finsetSum]
      intro j hj
      exact hq.mul
        (measurable_publicBlockRegulatedSelectedTrace dims A₀ j e eta)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact BlockProductDisintegration.lintegral_publicBlockProduct_eq_iterated
        dims hd j _
        (hq.mul (measurable_publicBlockRegulatedSelectedTrace dims A₀ j e eta))

end PSSSNative.BlockBand.PSSS
