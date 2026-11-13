module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedSphereKernelBridge

/-!
# Order-successor assembly

This module integrates the generic midpoint sphere kernel through the finite
mesh.  The predecessor remains fixed on `Icc a b`; only the
auxiliary multiplicity uses `Ioo (-xi) xi`.  No mesh cell is specialized to
the regulated resolvent itself.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 4000000

namespace PSSSNative.BlockBand.PSSS

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- The normalized event-kernel integral at fixed exterior and analytic
parameters is controlled by the finite-mesh estimate.  Its exposed
mesh coefficient is exactly `10`, before the exact radial integration.

Source: formula (2.13) of PSSS, arXiv:1608.02922. -/
theorem correctedMeshEventKernel_sample_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
      (A₀ : HermitianMatrix (BlockGUE.Index dims)) {eta : ℝ} (heta : 0 < eta)
      (Gext : BlockProductDisintegration.ExteriorSample dims j)
      (e t a b xi : ℝ), 0 < xi → ∀ (M r : ℕ),
      (∫⁻ φ, ∫⁻ Gj,
        correctedMeshEventKernel A₀ j heta Gext a b M r
          ((φ, Gj), ((e, t), xi))
        ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂uniformSphere (dims j)) ≤
      ENNReal.ofReal (1 / Real.pi) *
        ENNReal.ofReal (standardCauchyWeight t) *
        ENNReal.ofReal (10 * C * dims j * xi) *
        (∫⁻ φ, ∫⁻ Gj,
          fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
          ∂BlockProductDisintegration.selectedMeasure dims hd j
          ∂uniformSphere (dims j)) *
        ENNReal.ofReal (poissonRadialWeight eta xi) := by
  obtain ⟨C, hC, hmesh⟩ :=
    correctedSelected_occupiedLargeImage_weighted_finiteMesh
  refine ⟨C, hC, ?_⟩
  intro k dims hd j A₀ eta heta Gext e t a b xi hxi M r
  let R : ℝ≥0∞ := ENNReal.ofReal (1 / Real.pi) *
    ENNReal.ofReal (standardCauchyWeight t) *
    ENNReal.ofReal (poissonRadialWeight eta xi)
  have hm := hmesh dims hd j A₀ heta Gext e t a b xi hxi M r
  let base := fun n : Fin (2 ^ M) =>
    fun s : EuclideanSpace ℂ (Fin (dims j)) ×
        BlockProductDisintegration.SelectedSample dims j =>
      correctedCellOccupiedIndicator A₀ j heta Gext M n
          (s, ((e, t), xi)) *
        correctedCellLargeImageIndicator A₀ j heta Gext M n
          (s, ((e, t), xi)) *
        fixedSelectedPredecessorWeight A₀ j s.1 a b r (Gext, s.2)
  have hbase : ∀ n, Measurable (base n) := by
    intro n
    exact (((measurable_correctedCellOccupiedIndicator
      dims A₀ j heta Gext M n).mul
        (measurable_correctedCellLargeImageIndicator
          dims A₀ j heta Gext M n)).mul
        (measurable_correctedCellFixedPredecessor
          dims A₀ j Gext a b r)).comp
      (measurable_id.prodMk measurable_const)
  have hcell : ∀ n : Fin (2 ^ M),
      (∫⁻ φ, ∫⁻ Gj,
        correctedCellEventKernel A₀ j heta Gext a b M r n
          ((φ, Gj), ((e, t), xi))
        ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂uniformSphere (dims j)) =
      R * (∫⁻ φ, ∫⁻ Gj, base n (φ, Gj)
        ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂uniformSphere (dims j)) := by
    intro n
    let μs := (uniformSphere (dims j)).prod
      (BlockProductDisintegration.selectedMeasure dims hd j)
    calc
      _ = ∫⁻ s, correctedCellEventKernel A₀ j heta Gext a b M r n
          (s, ((e, t), xi)) ∂μs := by
        symm
        exact MeasureTheory.lintegral_prod
          (fun s => correctedCellEventKernel A₀ j heta Gext a b M r n
            (s, ((e, t), xi)))
          (((measurable_correctedCellEventKernel
            dims A₀ j heta Gext a b M r n).comp
              (measurable_id.prodMk measurable_const)).aemeasurable)
      _ = ∫⁻ s, R * base n s ∂μs := by
        apply lintegral_congr
        intro s
        unfold correctedCellEventKernel R base
        ac_rfl
      _ = R * ∫⁻ s, base n s ∂μs := by
        rw [MeasureTheory.lintegral_const_mul]
        exact hbase n
      _ = _ := by
        apply congrArg (fun z : ℝ≥0∞ => R * z)
        exact MeasureTheory.lintegral_prod (base n) (hbase n).aemeasurable
  calc
    _ = ∑ n : Fin (2 ^ M),
        ∫⁻ φ, ∫⁻ Gj,
          correctedCellEventKernel A₀ j heta Gext a b M r n
            ((φ, Gj), ((e, t), xi))
          ∂BlockProductDisintegration.selectedMeasure dims hd j
          ∂uniformSphere (dims j) := by
      let μs := (uniformSphere (dims j)).prod
        (BlockProductDisintegration.selectedMeasure dims hd j)
      rw [← lintegral_correctedMeshEvent_sampleProduct_eq_nested
        dims hd A₀ j heta Gext a b M r ((e, t), xi)]
      unfold correctedMeshEventKernel
      rw [MeasureTheory.lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro n hn
        exact MeasureTheory.lintegral_prod
          (fun s => correctedCellEventKernel A₀ j heta Gext a b M r n
            (s, ((e, t), xi)))
          (((measurable_correctedCellEventKernel
            dims A₀ j heta Gext a b M r n).comp
              (measurable_id.prodMk measurable_const)).aemeasurable)
      · intro n hn
        exact (measurable_correctedCellEventKernel
          dims A₀ j heta Gext a b M r n).comp
            (measurable_id.prodMk measurable_const)
    _ = R * (∑ n : Fin (2 ^ M),
        ∫⁻ φ, ∫⁻ Gj, base n (φ, Gj)
          ∂BlockProductDisintegration.selectedMeasure dims hd j
          ∂uniformSphere (dims j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      exact hcell n
    _ ≤ R * (ENNReal.ofReal (10 * C * dims j * xi) *
        (∫⁻ φ, ∫⁻ Gj,
          fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
          ∂BlockProductDisintegration.selectedMeasure dims hd j
          ∂uniformSphere (dims j))) := by
      apply mul_le_mul_right
      simpa only [base, correctedCellOccupiedIndicator,
        correctedCellLargeImageIndicator, correctedCellMidpointInverse,
        correctedCellAuxiliary, correctedSelectedAuxiliaryHermitian,
        correctedSelectedAuxiliaryBackground, addHermitian] using hm
    _ = _ := by unfold R; ac_rfl

/-- Tonelli-symmetric form of the integrated fixed-predecessor bound, with the
exterior sample outside the sphere direction. -/
theorem lintegral_exterior_uniformSphere_fixedSelectedPredecessor_le
    {C : ℝ} {r k : ℕ} (hind : PublicFactorialAtOrder C r)
    (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {a b : ℝ} (hab : a ≤ b) :
    (∫⁻ Gext, ∫⁻ φ, ∫⁻ Gj,
      fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
      ∂BlockProductDisintegration.selectedMeasure dims hd j
      ∂uniformSphere (dims j)
      ∂BlockProductDisintegration.exteriorMeasure dims hd j) ≤
      ENNReal.ofReal (C * (∑ i, (dims i : ℝ)) * (b - a)) ^ r := by
  let f := fun p : BlockProductDisintegration.ExteriorSample dims j ×
      EuclideanSpace ℂ (Fin (dims j)) =>
    ∫⁻ Gj, fixedSelectedPredecessorWeight A₀ j p.2 a b r (p.1, Gj)
      ∂BlockProductDisintegration.selectedMeasure dims hd j
  let pull := fun q :
      (BlockProductDisintegration.ExteriorSample dims j ×
        EuclideanSpace ℂ (Fin (dims j))) ×
          BlockProductDisintegration.SelectedSample dims j =>
    (q.1.2, (q.1.1, q.2))
  have hpull : Measurable pull :=
    (measurable_snd.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hjoint : Measurable (fun q :
      (BlockProductDisintegration.ExteriorSample dims j ×
        EuclideanSpace ℂ (Fin (dims j))) ×
          BlockProductDisintegration.SelectedSample dims j =>
      fixedSelectedPredecessorWeight A₀ j q.1.2 a b r (q.1.1, q.2)) := by
    simpa only [pull, Function.comp_def] using
      (measurable_joint_fixedSelectedPredecessorWeight
        dims A₀ j a b r).comp hpull
  have hf : Measurable f := hjoint.lintegral_prod_right
  calc
    _ = ∫⁻ Gext, ∫⁻ φ, f (Gext, φ)
        ∂uniformSphere (dims j)
        ∂BlockProductDisintegration.exteriorMeasure dims hd j := rfl
    _ = ∫⁻ φ, ∫⁻ Gext, f (Gext, φ)
        ∂BlockProductDisintegration.exteriorMeasure dims hd j
        ∂uniformSphere (dims j) := by
      exact lintegral_lintegral_swap hf.aemeasurable
    _ = ∫⁻ φ, ∫⁻ Gext, ∫⁻ Gj,
        fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
        ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂BlockProductDisintegration.exteriorMeasure dims hd j
        ∂uniformSphere (dims j) := rfl
    _ ≤ _ := lintegral_uniformSphere_fixedSelectedPredecessor_le
      hind dims hd j A₀ hab

/-- Exact radial normalization of the mesh coefficient.  The
finite-mesh factor `10 C d ξ` is `2 · (5 C d) · ξ`; Poisson radial integration
therefore contributes `π · 5 C d`.  After the energy normalization and the
single sphere-insertion factor two, the coefficient is exactly `10 C d`, not
`20 C d`. -/
theorem two_mul_normalized_correctedMesh_radial_eq_ten
    {eta C : ℝ} (heta : 0 < eta) (hC : 0 ≤ C) (d : ℕ) :
    2 * ENNReal.ofReal (1 / Real.pi) *
        (∫⁻ xi : ℝ in Set.Ioi 0,
          ENNReal.ofReal (10 * C * d * xi) *
            ENNReal.ofReal (poissonRadialWeight eta xi)) =
      ENNReal.ofReal (10 * C * d) := by
  let K : ℝ := 5 * C * d
  have hK : 0 ≤ K := by unfold K; positivity
  have hrad := lintegral_two_mul_radius_mul_poissonRadialWeight heta hK
  rw [show (∫⁻ xi : ℝ in Set.Ioi 0,
      ENNReal.ofReal (10 * C * d * xi) *
        ENNReal.ofReal (poissonRadialWeight eta xi)) =
      ∫⁻ xi : ℝ in Set.Ioi 0,
        ENNReal.ofReal (2 * K * xi) *
          ENNReal.ofReal (poissonRadialWeight eta xi) by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro xi hxi
    unfold K
    ring_nf]
  rw [hrad]
  calc
    2 * ENNReal.ofReal (1 / Real.pi) * ENNReal.ofReal (Real.pi * K) =
        ENNReal.ofReal 2 * ENNReal.ofReal (1 / Real.pi) *
          ENNReal.ofReal (Real.pi * K) := by norm_num
    _ = ENNReal.ofReal (2 * (1 / Real.pi)) *
          ENNReal.ofReal (Real.pi * K) := by
      rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by positivity)]
    _ = ENNReal.ofReal (2 * (1 / Real.pi) * (Real.pi * K)) := by
      symm
      exact ENNReal.ofReal_mul
        (show 0 ≤ 2 * (1 / Real.pi) by positivity)
    _ = ENNReal.ofReal (10 * C * d) := by
      congr 1
      unfold K
      field_simp [Real.pi_ne_zero]
      ring

end PSSSNative.BlockBand.PSSS
