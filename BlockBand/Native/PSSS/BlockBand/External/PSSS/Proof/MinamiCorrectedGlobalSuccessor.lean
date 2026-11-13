module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedProductFatou

/-!
# Global normalization for the corrected successor Fatou chain

Finite energy, Cauchy, and radial normalizations are commuted through the one
common corrected-mesh liminf.  The predecessor
`fullPublicFixedPredecessorWeight` is unchanged throughout this passage.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 4000000

namespace PSSSNative.BlockBand.PSSS

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- Selected-law Fatou with all finite analytic normalization factors already
commuted through the common mesh liminf.  Finiteness, rather than a formal
reversal of an inequality, is what justifies the commutation. -/
theorem selected_lintegral_normalizedOpenCount_fullPredecessor_le_liminf_grid
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (e t a b : ℝ) {xi : ℝ} (hxi : 0 < xi) (r : ℕ) :
    (∫⁻ Gj,
      ENNReal.ofReal (1 / Real.pi) *
        ENNReal.ofReal (standardCauchyWeight t) *
        ((eigenCount
          (correctedSelectedAuxiliaryHermitian A₀ j heta
            ((((Gext, Gj), e), t), xi)) (Set.Ioo (-xi) xi) : ℝ≥0∞) *
          fullPublicFixedPredecessorWeight A₀ a b r
            ((BlockProductDisintegration.split dims j).symm (Gext, Gj))) *
        ENNReal.ofReal (poissonRadialWeight eta xi)
      ∂BlockProductDisintegration.selectedMeasure dims hd j) ≤
    liminf (fun M => ∫⁻ Gj,
      ENNReal.ofReal (1 / Real.pi) *
        ENNReal.ofReal (standardCauchyWeight t) *
        ((correctedSelectedGridOccupiedCount
          A₀ j heta Gext e t xi M Gj : ℝ≥0∞) *
          fullPublicFixedPredecessorWeight A₀ a b r
            ((BlockProductDisintegration.split dims j).symm (Gext, Gj))) *
        ENNReal.ofReal (poissonRadialWeight eta xi)
      ∂BlockProductDisintegration.selectedMeasure dims hd j) atTop := by
  let μ := BlockProductDisintegration.selectedMeasure dims hd j
  let c : ℝ≥0∞ := ENNReal.ofReal (1 / Real.pi) *
    ENNReal.ofReal (standardCauchyWeight t) *
    ENNReal.ofReal (poissonRadialWeight eta xi)
  let W := fun Gj : BlockProductDisintegration.SelectedSample dims j =>
    fullPublicFixedPredecessorWeight A₀ a b r
      ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
  let u := fun M : ℕ => ∫⁻ Gj,
    (correctedSelectedGridOccupiedCount A₀ j heta Gext e t xi M Gj : ℝ≥0∞) *
      W Gj ∂μ
  have hc : c ≠ ⊤ := by
    unfold c
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hW : Measurable W :=
    (measurable_fullPublicFixedPredecessorWeight dims A₀ a b r).comp
      ((BlockProductDisintegration.split dims j).symm.measurable.comp
        (measurable_const.prodMk measurable_id))
  have hopen : Measurable (fun Gj =>
      (eigenCount
        (correctedSelectedAuxiliaryHermitian A₀ j heta
          ((((Gext, Gj), e), t), xi)) (Set.Ioo (-xi) xi) : ℝ≥0∞) * W Gj) := by
    exact ((measurable_correctedSelectedAuxiliaryOpenCount
      dims A₀ j heta).comp (by fun_prop)).mul hW
  have hgrid : ∀ M, Measurable (fun Gj =>
      (correctedSelectedGridOccupiedCount A₀ j heta Gext e t xi M Gj : ℝ≥0∞) *
        W Gj) := by
    intro M
    exact ((measurable_of_countable (f := fun q : ℕ => (q : ℝ≥0∞))).comp
      (measurable_correctedSelectedGridOccupiedCount
        dims j A₀ heta Gext e t xi M)).mul hW
  have hfatou := selected_lintegral_correctedOpenCount_fullPredecessor_le_liminf_grid
    dims hd j A₀ heta Gext e t a b hxi r
  calc
    _ = ∫⁻ Gj, c * ((eigenCount
          (correctedSelectedAuxiliaryHermitian A₀ j heta
            ((((Gext, Gj), e), t), xi)) (Set.Ioo (-xi) xi) : ℝ≥0∞) * W Gj) ∂μ := by
      apply lintegral_congr
      intro Gj
      unfold c W
      ac_rfl
    _ = c * (∫⁻ Gj,
        (eigenCount
          (correctedSelectedAuxiliaryHermitian A₀ j heta
            ((((Gext, Gj), e), t), xi)) (Set.Ioo (-xi) xi) : ℝ≥0∞) * W Gj ∂μ) := by
      rw [MeasureTheory.lintegral_const_mul _ hopen]
    _ ≤ c * liminf u atTop := by gcongr
    _ = liminf (fun M => c * u M) atTop := by
      symm
      exact ENNReal.liminf_const_mul_of_ne_top hc
    _ = _ := by
      apply liminf_congr
      filter_upwards with M
      unfold u
      rw [← MeasureTheory.lintegral_const_mul _ (hgrid M)]
      apply lintegral_congr
      intro Gj
      unfold c W
      ac_rfl

/-- The normalized selected-law open-count kernel is bounded by the liminf of
the generic-midpoint mesh-event integrals.  The same mesh index `M`
is used on both sides of the finite-stage comparison. -/
theorem selected_lintegral_normalizedOpenCount_fullPredecessor_le_liminf_mesh
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (e t xi : ℝ) {eta : ℝ} (heta : 0 < eta)
    {a b : ℝ} (hab : a ≤ b) (hxi : 0 < xi) (r : ℕ)
    (hend : ∀ᵐ Gj ∂BlockProductDisintegration.selectedMeasure dims hd j,
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
              (if b = 0 then 1 else 0)) :
    (∫⁻ Gj,
      ENNReal.ofReal (1 / Real.pi) *
        ENNReal.ofReal (standardCauchyWeight t) *
        ((eigenCount
          (correctedSelectedAuxiliaryHermitian A₀ j heta
            ((((Gext, Gj), e), t), xi)) (Set.Ioo (-xi) xi) : ℝ≥0∞) *
          fullPublicFixedPredecessorWeight A₀ a b r
            ((BlockProductDisintegration.split dims j).symm (Gext, Gj))) *
        ENNReal.ofReal (poissonRadialWeight eta xi)
      ∂BlockProductDisintegration.selectedMeasure dims hd j) ≤
    liminf (fun M => 2 * ∫⁻ Gj, ∫⁻ φ,
      correctedMeshEventKernel A₀ j heta Gext a b M r
        ((φ, Gj), ((e, t), xi))
      ∂uniformSphere (dims j)
      ∂BlockProductDisintegration.selectedMeasure dims hd j) atTop := by
  refine (selected_lintegral_normalizedOpenCount_fullPredecessor_le_liminf_grid
    dims hd j A₀ heta Gext e t a b hxi r).trans ?_
  refine liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards with M
  exact selected_lintegral_correctedGridFullPredecessor_le_two_meshEventKernel
    dims hd j A₀ Gext e t xi heta hab M r hend

/-- Almost-everywhere exterior form of the complete selected-law liminf
bridge.  This is the maximal global statement available from the current
joint-measurability API: the remaining exterior and parameter Fatou steps
require joint measurability in `Gext` of the corrected grid/event families. -/
theorem ae_exterior_selected_normalizedOpenCount_le_liminf_mesh
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (e t xi : ℝ) {eta : ℝ} (heta : 0 < eta)
    {a b : ℝ} (hab : a ≤ b) (hxi : 0 < xi) (r : ℕ) :
    ∀ᵐ Gext ∂BlockProductDisintegration.exteriorMeasure dims hd j,
      (∫⁻ Gj,
        ENNReal.ofReal (1 / Real.pi) *
          ENNReal.ofReal (standardCauchyWeight t) *
          ((eigenCount
            (correctedSelectedAuxiliaryHermitian A₀ j heta
              ((((Gext, Gj), e), t), xi)) (Set.Ioo (-xi) xi) : ℝ≥0∞) *
            fullPublicFixedPredecessorWeight A₀ a b r
              ((BlockProductDisintegration.split dims j).symm (Gext, Gj))) *
          ENNReal.ofReal (poissonRadialWeight eta xi)
        ∂BlockProductDisintegration.selectedMeasure dims hd j) ≤
      liminf (fun M => 2 * ∫⁻ Gj, ∫⁻ φ,
        correctedMeshEventKernel A₀ j heta Gext a b M r
          ((φ, Gj), ((e, t), xi))
        ∂uniformSphere (dims j)
        ∂BlockProductDisintegration.selectedMeasure dims hd j) atTop := by
  have hend :=
    exterior_ae_selected_ae_uniformSphere_fullCompression_fixedEndpoints
      dims hd A₀ j a b
  filter_upwards [hend] with Gext hGext
  exact selected_lintegral_normalizedOpenCount_fullPredecessor_le_liminf_mesh
    dims hd j A₀ Gext e t xi heta hab hxi r hGext

end PSSSNative.BlockBand.PSSS
