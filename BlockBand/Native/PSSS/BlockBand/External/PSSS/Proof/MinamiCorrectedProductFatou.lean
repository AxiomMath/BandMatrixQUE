module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedFatouOrderSuccessor

/-!
# Product-measure reordering for the corrected Minami Fatou step

This module reorders the endpoint-null statement into the selected-first form
needed by cellwise sphere insertion.  The reordering is performed through the
product measure and `Measure.ae_ae_comm`; no analytic limit or
predecessor is changed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 4000000

namespace PSSSNative.BlockBand.PSSS

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- Endpoint-null transport in exterior/selected/sphere order.  Measurability
is proved using the reconstructed compression; on the almost-sure unit sphere
it is exactly the compression of the original public deformation. -/
theorem exterior_ae_selected_ae_uniformSphere_fullCompression_fixedEndpoints
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (a b : ℝ) :
    ∀ᵐ Gext ∂BlockProductDisintegration.exteriorMeasure dims hd j,
      ∀ᵐ Gj ∂BlockProductDisintegration.selectedMeasure dims hd j,
        ∀ᵐ φ ∂uniformSphere (dims j),
          ‖φ‖ = 1 ∧
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
  let Good := fun φ : EuclideanSpace ℂ (Fin (dims j)) =>
      fun p : BlockProductDisintegration.ExteriorSample dims j ×
          BlockProductDisintegration.SelectedSample dims j =>
        ‖φ‖ ≠ 1 ∨
          (eigenCount
              (reconstructedFullCompression A₀ j φ p.1
                (orthProj φ * (p.2 ⟨j, by simp⟩).1 * orthProj φ)) {a} =
              (if a = 0 then 1 else 0) ∧
            eigenCount
              (reconstructedFullCompression A₀ j φ p.1
                (orthProj φ * (p.2 ⟨j, by simp⟩).1 * orthProj φ)) {b} =
              (if b = 0 then 1 else 0))
  have hH := measurable_joint_reconstructedFullCompression_selected dims A₀ j
  have hca : Measurable (fun q : EuclideanSpace ℂ (Fin (dims j)) ×
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) =>
      eigenCount
        (reconstructedFullCompression A₀ j q.1 q.2.1
          (orthProj q.1 * (q.2.2 ⟨j, by simp⟩).1 * orthProj q.1)) {a}) := by
    simpa only [Set.Icc_self, Function.comp_def] using
      (measurable_eigenCount_Icc a a).comp hH
  have hcb : Measurable (fun q : EuclideanSpace ℂ (Fin (dims j)) ×
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) =>
      eigenCount
        (reconstructedFullCompression A₀ j q.1 q.2.1
          (orthProj q.1 * (q.2.2 ⟨j, by simp⟩).1 * orthProj q.1)) {b}) := by
    simpa only [Set.Icc_self, Function.comp_def] using
      (measurable_eigenCount_Icc b b).comp hH
  have hGood : MeasurableSet {q : EuclideanSpace ℂ (Fin (dims j)) ×
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) | Good q.1 q.2} := by
    apply MeasurableSet.union
    · exact (measurableSet_eq_fun
        (measurable_norm.comp measurable_fst) measurable_const).compl
    · exact (measurableSet_eq_fun hca measurable_const).inter
        (measurableSet_eq_fun hcb measurable_const)
  have hsrc :=
    uniformSphere_ae_exterior_ae_selected_fullCompression_fixedEndpoints
      dims hd A₀ j a b
  have hsrcGood : ∀ᵐ φ ∂uniformSphere (dims j),
      ∀ᵐ Gext ∂BlockProductDisintegration.exteriorMeasure dims hd j,
        ∀ᵐ Gj ∂BlockProductDisintegration.selectedMeasure dims hd j,
          Good φ (Gext, Gj) := by
    filter_upwards [hsrc] with φ hφ
    filter_upwards [hφ] with Gext hGext
    filter_upwards [hGext] with Gj hGj
    by_cases hn : ‖φ‖ = 1
    · right
      rw [reconstructedFullCompression_projected_eq_compressHermitian
        A₀ j φ hn Gext Gj]
      exact hGj
    · exact Or.inl hn
  have hprod : ∀ᵐ φ ∂uniformSphere (dims j),
      ∀ᵐ p ∂(BlockProductDisintegration.exteriorMeasure dims hd j).prod
        (BlockProductDisintegration.selectedMeasure dims hd j), Good φ p := by
    filter_upwards [hsrcGood] with φ hφ
    exact (Measure.ae_prod_iff_ae_ae
      (hGood.preimage (measurable_const.prodMk measurable_id))).2 hφ
  have hswap : ∀ᵐ p ∂(BlockProductDisintegration.exteriorMeasure dims hd j).prod
      (BlockProductDisintegration.selectedMeasure dims hd j),
      ∀ᵐ φ ∂uniformSphere (dims j), Good φ p :=
    (Measure.ae_ae_comm hGood).1 hprod
  have hn := uniformSphere_norm_eq_one (hd j)
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with Gext hGext
  filter_upwards [hGext] with Gj hGj
  filter_upwards [hGj, hn] with φ hgood hnorm
  refine ⟨hnorm, ?_⟩
  rcases hgood with hne | hend
  · exact (hne hnorm).elim
  · rw [reconstructedFullCompression_projected_eq_compressHermitian
      A₀ j φ hnorm Gext Gj] at hend
    exact hend

/-- Selected-law Fatou passage while the predecessor is still the
full public `(N_[a,b]-1).descFactorial r`: the full predecessor is not
replaced before the common corrected mesh index is introduced. -/
theorem selected_lintegral_correctedOpenCount_fullPredecessor_le_liminf_grid
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (e t a b : ℝ) {xi : ℝ} (hxi : 0 < xi) (r : ℕ) :
    (∫⁻ Gj,
      (eigenCount
        (correctedSelectedAuxiliaryHermitian A₀ j heta
          ((((Gext, Gj), e), t), xi)) (Set.Ioo (-xi) xi) : ℝ≥0∞) *
        fullPublicFixedPredecessorWeight A₀ a b r
          ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
      ∂BlockProductDisintegration.selectedMeasure dims hd j) ≤
    liminf (fun M => ∫⁻ Gj,
      (correctedSelectedGridOccupiedCount A₀ j heta Gext e t xi M Gj : ℝ≥0∞) *
        fullPublicFixedPredecessorWeight A₀ a b r
          ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
      ∂BlockProductDisintegration.selectedMeasure dims hd j) atTop := by
  let μ := BlockProductDisintegration.selectedMeasure dims hd j
  let W := fun Gj : BlockProductDisintegration.SelectedSample dims j =>
    fullPublicFixedPredecessorWeight A₀ a b r
      ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
  let F : ℕ → BlockProductDisintegration.SelectedSample dims j → ℝ≥0∞ :=
    fun M Gj =>
      (correctedSelectedGridOccupiedCount A₀ j heta Gext e t xi M Gj : ℝ≥0∞) *
        W Gj
  have hW : Measurable W :=
    (measurable_fullPublicFixedPredecessorWeight dims A₀ a b r).comp
      ((BlockProductDisintegration.split dims j).symm.measurable.comp
        (measurable_const.prodMk measurable_id))
  calc
    _ ≤ ∫⁻ Gj, liminf (fun M => F M Gj) atTop ∂μ := by
      apply lintegral_mono_ae
      filter_upwards
        [ae_selectedBlock_correctedAuxiliary_orderedEigenvalue_injective
          dims hd j A₀ heta Gext e t xi] with Gj hGj
      apply Filter.le_liminf_of_le (by isBoundedDefault)
      exact eventually_correctedSelected_openCount_mul_weight_le_gridOccupied
        A₀ j heta Gext Gj e t hxi hGj (W Gj)
    _ ≤ _ := by
      apply lintegral_liminf_le
      intro M
      exact ((measurable_of_countable
        (f := fun q : ℕ => (q : ℝ≥0∞))).comp
          (measurable_correctedSelectedGridOccupiedCount
            dims j A₀ heta Gext e t xi M)).mul hW

end PSSSNative.BlockBand.PSSS
