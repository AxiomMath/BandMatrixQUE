module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedJointMeasurability

/-!
# Factored joint measurability of the corrected global mesh kernel

The normalized single-cell kernel is split into small named factors to keep
elaboration bounded.  The finite mesh sum is then measurable without freezing
the exterior sample.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 4000000

namespace PSSSNative.BlockBand.PSSS

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- A reassociation whose first component is the sphere direction and
whose second component is the split public sample. -/
abbrev CorrectedFactoredGlobalVariables {k : ℕ} (dims : Fin k → ℕ) (j : Fin k) :=
  (EuclideanSpace ℂ (Fin (dims j)) ×
    (BlockProductDisintegration.ExteriorSample dims j ×
      BlockProductDisintegration.SelectedSample dims j)) × ((ℝ × ℝ) × ℝ)

/-- Measurable reassociation to the exterior-first global variable space. -/
def correctedFactoredToGlobal
    {k : ℕ} {dims : Fin k → ℕ} {j : Fin k}
    (p : CorrectedFactoredGlobalVariables dims j) :
    CorrectedGlobalEventVariables dims j :=
  (p.1.2.1, ((p.1.1, p.1.2.2), p.2))

theorem measurable_correctedFactoredToGlobal
    {k : ℕ} {dims : Fin k → ℕ} {j : Fin k} :
    Measurable (correctedFactoredToGlobal :
      CorrectedFactoredGlobalVariables dims j →
        CorrectedGlobalEventVariables dims j) := by
  unfold correctedFactoredToGlobal
  fun_prop

/-- One fully normalized cell on the measurability-friendly association. -/
def correctedFactoredGlobalCellKernel
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta) (a b : ℝ) (M r : ℕ)
    (n : Fin (2 ^ M)) (p : CorrectedFactoredGlobalVariables dims j) : ℝ≥0∞ :=
  let q := correctedFactoredToGlobal p
  ENNReal.ofReal (1 / Real.pi) *
    ENNReal.ofReal (standardCauchyWeight p.2.1.2) *
    correctedCellOccupiedIndicator A₀ j heta q.1 M n q.2 *
    correctedCellLargeImageIndicator A₀ j heta q.1 M n q.2 *
    fixedSelectedPredecessorWeight A₀ j p.1.1 a b r p.1.2 *
    ENNReal.ofReal (poissonRadialWeight eta p.2.2)

/-- Joint measurability of one factored normalized cell. -/
theorem measurable_correctedFactoredGlobalCellKernel
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta) (a b : ℝ) (M r : ℕ)
    (n : Fin (2 ^ M)) :
    Measurable (correctedFactoredGlobalCellKernel A₀ j heta a b M r n) := by
  have hq := measurable_correctedFactoredToGlobal
    (dims := dims) (j := j)
  have hc : Measurable (fun p : CorrectedFactoredGlobalVariables dims j =>
      ENNReal.ofReal (standardCauchyWeight p.2.1.2)) := by
    apply ENNReal.measurable_ofReal.comp
    unfold standardCauchyWeight
    fun_prop (discharger := intro x; positivity)
  have ho := (measurable_correctedGlobalCellOccupiedIndicator
    dims A₀ j heta M n).comp hq
  have hl := (measurable_correctedGlobalCellLargeImageIndicator
    dims A₀ j heta M n).comp hq
  have hw : Measurable (fun p : CorrectedFactoredGlobalVariables dims j =>
      fixedSelectedPredecessorWeight A₀ j p.1.1 a b r p.1.2) :=
    (measurable_joint_fixedSelectedPredecessorWeight
      dims A₀ j a b r).comp measurable_fst
  have hp : Measurable (fun p : CorrectedFactoredGlobalVariables dims j =>
      ENNReal.ofReal (poissonRadialWeight eta p.2.2)) := by
    apply ENNReal.measurable_ofReal.comp
    unfold poissonRadialWeight
    fun_prop
  unfold correctedFactoredGlobalCellKernel
  exact (((((measurable_const.mul hc).mul ho).mul hl).mul hw).mul hp)

/-- Finite sum of the factored global cells. -/
def correctedFactoredGlobalMeshKernel
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta) (a b : ℝ) (M r : ℕ)
    (p : CorrectedFactoredGlobalVariables dims j) : ℝ≥0∞ :=
  ∑ n : Fin (2 ^ M),
    correctedFactoredGlobalCellKernel A₀ j heta a b M r n p

/-- Full joint measurability of the corrected mesh kernel for every common
mesh index `M`. -/
theorem measurable_correctedFactoredGlobalMeshKernel
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta) (a b : ℝ) (M r : ℕ) :
    Measurable (correctedFactoredGlobalMeshKernel A₀ j heta a b M r) := by
  unfold correctedFactoredGlobalMeshKernel
  apply Finset.measurable_sum
  intro n hn
  exact measurable_correctedFactoredGlobalCellKernel
    dims A₀ j heta a b M r n

/-- The factored joint kernel is exactly the existing corrected mesh event
kernel after reassociation. -/
theorem correctedFactoredGlobalMeshKernel_eq
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta) (a b : ℝ) (M r : ℕ)
    (p : CorrectedFactoredGlobalVariables dims j) :
    correctedFactoredGlobalMeshKernel A₀ j heta a b M r p =
      correctedMeshEventKernel A₀ j heta p.1.2.1 a b M r
        ((p.1.1, p.1.2.2), p.2) := by
  rfl

/-- For fixed analytic parameters, the sphere/selected integral of the mesh
kernel is measurable in the exterior sample.  This is the exact hypothesis
needed by the exterior `lintegral_liminf_le` step. -/
theorem measurable_exterior_lintegral_selected_sphere_correctedMesh
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta) (a b e t xi : ℝ) (M r : ℕ) :
    Measurable (fun Gext : BlockProductDisintegration.ExteriorSample dims j =>
      ∫⁻ Gj, ∫⁻ φ,
        correctedMeshEventKernel A₀ j heta Gext a b M r
          ((φ, Gj), ((e, t), xi))
        ∂uniformSphere (dims j)
        ∂BlockProductDisintegration.selectedMeasure dims hd j) := by
  let f := fun p :
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) ×
          EuclideanSpace ℂ (Fin (dims j)) =>
    correctedFactoredGlobalMeshKernel A₀ j heta a b M r
      ((p.2, p.1), ((e, t), xi))
  have hf : Measurable f :=
    (measurable_correctedFactoredGlobalMeshKernel
      dims A₀ j heta a b M r).comp
        (((measurable_snd.prodMk measurable_fst).prodMk measurable_const))
  have hpair : Measurable (fun p :
      BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j =>
      ∫⁻ φ, f (p, φ) ∂uniformSphere (dims j)) :=
    hf.lintegral_prod_right
  simpa only [f, correctedFactoredGlobalMeshKernel_eq] using
    hpair.lintegral_prod_right

/-- Exterior Fatou passage for the normalized corrected open-count kernel,
with the one common mesh index retained. -/
theorem exterior_lintegral_normalizedOpenCount_le_liminf_mesh
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (e t xi : ℝ) {eta : ℝ} (heta : 0 < eta)
    {a b : ℝ} (hab : a ≤ b) (hxi : 0 < xi) (r : ℕ) :
    (∫⁻ Gext, ∫⁻ Gj,
      ENNReal.ofReal (1 / Real.pi) *
        ENNReal.ofReal (standardCauchyWeight t) *
        ((eigenCount
          (correctedSelectedAuxiliaryHermitian A₀ j heta
            ((((Gext, Gj), e), t), xi)) (Set.Ioo (-xi) xi) : ℝ≥0∞) *
          fullPublicFixedPredecessorWeight A₀ a b r
            ((BlockProductDisintegration.split dims j).symm (Gext, Gj))) *
        ENNReal.ofReal (poissonRadialWeight eta xi)
      ∂BlockProductDisintegration.selectedMeasure dims hd j
      ∂BlockProductDisintegration.exteriorMeasure dims hd j) ≤
    liminf (fun M => ∫⁻ Gext, 2 * ∫⁻ Gj, ∫⁻ φ,
      correctedMeshEventKernel A₀ j heta Gext a b M r
        ((φ, Gj), ((e, t), xi))
      ∂uniformSphere (dims j)
      ∂BlockProductDisintegration.selectedMeasure dims hd j
      ∂BlockProductDisintegration.exteriorMeasure dims hd j) atTop := by
  calc
    _ ≤ ∫⁻ Gext, liminf (fun M => 2 * ∫⁻ Gj, ∫⁻ φ,
        correctedMeshEventKernel A₀ j heta Gext a b M r
          ((φ, Gj), ((e, t), xi))
        ∂uniformSphere (dims j)
        ∂BlockProductDisintegration.selectedMeasure dims hd j) atTop
        ∂BlockProductDisintegration.exteriorMeasure dims hd j := by
      exact lintegral_mono_ae
        (ae_exterior_selected_normalizedOpenCount_le_liminf_mesh
          dims hd j A₀ e t xi heta hab hxi r)
    _ ≤ _ := by
      apply lintegral_liminf_le
      intro M
      exact measurable_const.mul
        (measurable_exterior_lintegral_selected_sphere_correctedMesh
          dims hd A₀ j heta a b e t xi M r)

end PSSSNative.BlockBand.PSSS
