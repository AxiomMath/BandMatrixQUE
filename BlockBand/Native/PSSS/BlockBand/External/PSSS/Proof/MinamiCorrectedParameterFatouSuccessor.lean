module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedGlobalKernelMeasurability

/-!
# Parameter-product Fatou passage for the corrected successor kernel

The energy, Cauchy, and positive-radial parameters are treated as one
product measure.  Consequently a single common mesh index passes through the
whole parameter integral by one application of Fatou.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 5000000

namespace PSSSNative.BlockBand.PSSS

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- For every common mesh index, the fully nested exterior/selected/sphere
mesh integral is jointly measurable in `(e,t,xi)`. -/
theorem measurable_parameters_exterior_selected_sphere_correctedMesh
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta) (a b : ℝ) (M r : ℕ) :
    Measurable (fun q : (ℝ × ℝ) × ℝ =>
      ∫⁻ Gext, 2 * ∫⁻ Gj, ∫⁻ φ,
        correctedMeshEventKernel A₀ j heta Gext a b M r
          ((φ, Gj), q)
        ∂uniformSphere (dims j)
        ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂BlockProductDisintegration.exteriorMeasure dims hd j) := by
  let f := fun p : ((((ℝ × ℝ) × ℝ) ×
      BlockProductDisintegration.ExteriorSample dims j) ×
        BlockProductDisintegration.SelectedSample dims j) ×
          EuclideanSpace ℂ (Fin (dims j)) =>
    correctedFactoredGlobalMeshKernel A₀ j heta a b M r
      ((p.2, (p.1.1.2, p.1.2)), p.1.1.1)
  have hf : Measurable f :=
    (measurable_correctedFactoredGlobalMeshKernel
      dims A₀ j heta a b M r).comp (by fun_prop)
  have hφ : Measurable (fun p : (((ℝ × ℝ) × ℝ) ×
      BlockProductDisintegration.ExteriorSample dims j) ×
        BlockProductDisintegration.SelectedSample dims j =>
      ∫⁻ φ, f (p, φ) ∂uniformSphere (dims j)) :=
    hf.lintegral_prod_right
  have hGj : Measurable (fun p : ((ℝ × ℝ) × ℝ) ×
      BlockProductDisintegration.ExteriorSample dims j =>
      ∫⁻ Gj, ∫⁻ φ, f ((p, Gj), φ) ∂uniformSphere (dims j)
        ∂BlockProductDisintegration.selectedMeasure dims hd j) :=
    hφ.lintegral_prod_right
  have hGext : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      ∫⁻ Gext, ∫⁻ Gj, ∫⁻ φ, f (((q, Gext), Gj), φ)
        ∂uniformSphere (dims j)
        ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂BlockProductDisintegration.exteriorMeasure dims hd j) :=
    hGj.lintegral_prod_right
  let g := fun q : (ℝ × ℝ) × ℝ =>
      fun Gext : BlockProductDisintegration.ExteriorSample dims j =>
      2 * ∫⁻ Gj, ∫⁻ φ, f (((q, Gext), Gj), φ)
        ∂uniformSphere (dims j)
        ∂BlockProductDisintegration.selectedMeasure dims hd j
  have htwo : Measurable (Function.uncurry g) := by
    exact measurable_const.mul hGj
  have hout := htwo.lintegral_prod_right
    (ν := BlockProductDisintegration.exteriorMeasure dims hd j)
  simpa only [g, f, correctedFactoredGlobalMeshKernel_eq] using hout

/-- The complete parameter-product Fatou step in the unchanged common mesh
limit order.  The positivity restriction on `xi` is read directly from the
`Ioi 0` factor. -/
theorem parameterProduct_lintegral_normalizedOpenCount_le_liminf_mesh
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {eta : ℝ} (heta : 0 < eta) {a b : ℝ} (hab : a ≤ b) (r : ℕ) :
    let μp := ((volume.restrict (Set.Ioc a b)).prod volume).prod
      (volume.restrict (Set.Ioi 0))
    (∫⁻ q, ∫⁻ Gext, ∫⁻ Gj,
      ENNReal.ofReal (1 / Real.pi) *
        ENNReal.ofReal (standardCauchyWeight q.1.2) *
        ((eigenCount
          (correctedSelectedAuxiliaryHermitian A₀ j heta
            ((((Gext, Gj), q.1.1), q.1.2), q.2))
            (Set.Ioo (-q.2) q.2) : ℝ≥0∞) *
          fullPublicFixedPredecessorWeight A₀ a b r
            ((BlockProductDisintegration.split dims j).symm (Gext, Gj))) *
        ENNReal.ofReal (poissonRadialWeight eta q.2)
      ∂BlockProductDisintegration.selectedMeasure dims hd j
      ∂BlockProductDisintegration.exteriorMeasure dims hd j ∂μp) ≤
    liminf (fun M => ∫⁻ q, ∫⁻ Gext, 2 * ∫⁻ Gj, ∫⁻ φ,
      correctedMeshEventKernel A₀ j heta Gext a b M r
        ((φ, Gj), q)
      ∂uniformSphere (dims j)
      ∂BlockProductDisintegration.selectedMeasure dims hd j
      ∂BlockProductDisintegration.exteriorMeasure dims hd j ∂μp) atTop := by
  dsimp only
  let μet : Measure (ℝ × ℝ) := (volume.restrict (Set.Ioc a b)).prod volume
  let μxi : Measure ℝ := volume.restrict (Set.Ioi 0)
  let μp := μet.prod μxi
  have hpos : ∀ᵐ q : (ℝ × ℝ) × ℝ ∂μp, 0 < q.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt
      (measurable_const : Measurable (fun _q : (ℝ × ℝ) × ℝ => (0 : ℝ)))
      measurable_snd)).2
    filter_upwards with et
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with xi hxi
    exact hxi
  calc
    _ ≤ ∫⁻ q, liminf (fun M => ∫⁻ Gext, 2 * ∫⁻ Gj, ∫⁻ φ,
        correctedMeshEventKernel A₀ j heta Gext a b M r
          ((φ, Gj), q)
        ∂uniformSphere (dims j)
        ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂BlockProductDisintegration.exteriorMeasure dims hd j) atTop ∂μp := by
      apply lintegral_mono_ae
      filter_upwards [hpos] with q hq
      exact exterior_lintegral_normalizedOpenCount_le_liminf_mesh
        dims hd j A₀ q.1.1 q.1.2 q.2 heta hab hq r
    _ ≤ _ := by
      apply lintegral_liminf_le
      intro M
      exact measurable_parameters_exterior_selected_sphere_correctedMesh
        dims hd A₀ j heta a b M r

end PSSSNative.BlockBand.PSSS
