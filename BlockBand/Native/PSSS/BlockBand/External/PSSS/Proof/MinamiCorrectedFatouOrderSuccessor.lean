module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedOrderSuccessorAssembly

/-!
# Fatou bridge for the order-successor step

The full predecessor is retained while the open auxiliary count is
replaced by occupied mesh cells.  Sphere insertion is then applied cellwise,
before the predecessor is replaced by its fixed-compression counterpart.  The
mesh uses `Ioo (-xi) xi` and the generic midpoint inverse throughout.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 4000000

namespace PSSSNative.BlockBand.PSSS

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- Cellwise sphere insertion summed over the entire mesh.  This is
the finite stage of the Fatou argument: the predecessor
`fullPublicFixedPredecessorWeight` occurs on the left, while replacement by the fixed selected
compression predecessor happens only inside the already-inserted sphere
event on the right.

Source: formula (2.13) of PSSS, arXiv:1608.02922. -/
theorem correctedGridOccupied_fullPredecessor_le_two_sphereMesh
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (Gj : BlockProductDisintegration.SelectedSample dims j)
    (e t xi : ℝ) {eta : ℝ} (heta : 0 < eta)
    {a b : ℝ} (hab : a ≤ b) (M r : ℕ)
    (hend : ∀ᵐ φ ∂uniformSphere (dims j),
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
    (correctedSelectedGridOccupiedCount A₀ j heta Gext e t xi M Gj : ℝ≥0∞) *
        fullPublicFixedPredecessorWeight A₀ a b r
          ((BlockProductDisintegration.split dims j).symm (Gext, Gj)) ≤
      2 * ∫⁻ φ,
        ∑ n : Fin (2 ^ M),
          correctedCellOccupiedIndicator A₀ j heta Gext M n
              ((φ, Gj), ((e, t), xi)) *
            correctedCellLargeImageIndicator A₀ j heta Gext M n
              ((φ, Gj), ((e, t), xi)) *
            fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
        ∂uniformSphere (dims j) := by
  let W : ℝ≥0∞ := fullPublicFixedPredecessorWeight A₀ a b r
    ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
  have hcount :
      (correctedSelectedGridOccupiedCount A₀ j heta Gext e t xi M Gj : ℝ≥0∞) =
        ∑ n : Fin (2 ^ M),
          correctedCellOccupiedIndicator A₀ j heta Gext M n
            ((0, Gj), ((e, t), xi)) := by
    unfold correctedSelectedGridOccupiedCount correctedCellOccupiedIndicator
      correctedCellAuxiliary
    simp [gridOccupiedCount, Set.indicator]
  rw [hcount, Finset.sum_mul, MeasureTheory.lintegral_finsetSum,
    Finset.mul_sum]
  · apply Finset.sum_le_sum
    intro n hn
    have hcell := occupied_fullPredecessor_le_two_midpointSphere_fixedPredecessor
      dims hd j A₀ Gext Gj e t xi heta hab M r n hend
    simpa only [W, correctedCellOccupiedIndicator,
      correctedCellLargeImageIndicator, correctedCellMidpointInverse,
      correctedCellAuxiliary] using hcell
  · intro n hn
    exact (((measurable_correctedCellOccupiedIndicator
      dims A₀ j heta Gext M n).mul
        (measurable_correctedCellLargeImageIndicator
          dims A₀ j heta Gext M n)).mul
        (measurable_correctedCellFixedPredecessor
          dims A₀ j Gext a b r)).comp (by fun_prop)

/-- Normalized form of the summed cellwise bridge, stated directly with
`correctedMeshEventKernel`.  Thus every finite stage on the right is exactly
the generic-midpoint event kernel to which the coefficient-`10` finite-mesh
estimate applies. -/
theorem correctedGridOccupied_normalizedFullPredecessor_le_two_meshEventKernel
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (Gj : BlockProductDisintegration.SelectedSample dims j)
    (e t xi : ℝ) {eta : ℝ} (heta : 0 < eta)
    {a b : ℝ} (hab : a ≤ b) (M r : ℕ)
    (hend : ∀ᵐ φ ∂uniformSphere (dims j),
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
    ENNReal.ofReal (1 / Real.pi) *
        ENNReal.ofReal (standardCauchyWeight t) *
        ((correctedSelectedGridOccupiedCount
          A₀ j heta Gext e t xi M Gj : ℝ≥0∞) *
          fullPublicFixedPredecessorWeight A₀ a b r
            ((BlockProductDisintegration.split dims j).symm (Gext, Gj))) *
        ENNReal.ofReal (poissonRadialWeight eta xi) ≤
      2 * ∫⁻ φ,
        correctedMeshEventKernel A₀ j heta Gext a b M r
          ((φ, Gj), ((e, t), xi))
        ∂uniformSphere (dims j) := by
  let R : ℝ≥0∞ := ENNReal.ofReal (1 / Real.pi) *
    ENNReal.ofReal (standardCauchyWeight t) *
    ENNReal.ofReal (poissonRadialWeight eta xi)
  let base := fun φ : EuclideanSpace ℂ (Fin (dims j)) =>
    ∑ n : Fin (2 ^ M),
      correctedCellOccupiedIndicator A₀ j heta Gext M n
          ((φ, Gj), ((e, t), xi)) *
        correctedCellLargeImageIndicator A₀ j heta Gext M n
          ((φ, Gj), ((e, t), xi)) *
        fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
  have hbase : Measurable base := by
    unfold base
    apply Finset.measurable_sum
    intro n hn
    exact (((measurable_correctedCellOccupiedIndicator
      dims A₀ j heta Gext M n).mul
        (measurable_correctedCellLargeImageIndicator
          dims A₀ j heta Gext M n)).mul
        (measurable_correctedCellFixedPredecessor
          dims A₀ j Gext a b r)).comp (by fun_prop)
  have hraw := correctedGridOccupied_fullPredecessor_le_two_sphereMesh
    dims hd j A₀ Gext Gj e t xi heta hab M r hend
  calc
    _ = R * ((correctedSelectedGridOccupiedCount
          A₀ j heta Gext e t xi M Gj : ℝ≥0∞) *
          fullPublicFixedPredecessorWeight A₀ a b r
            ((BlockProductDisintegration.split dims j).symm (Gext, Gj))) := by
      unfold R
      ac_rfl
    _ ≤ R * (2 * ∫⁻ φ, base φ ∂uniformSphere (dims j)) := by
      gcongr
    _ = 2 * ∫⁻ φ,
        correctedMeshEventKernel A₀ j heta Gext a b M r
          ((φ, Gj), ((e, t), xi))
        ∂uniformSphere (dims j) := by
      rw [show R * (2 * ∫⁻ φ, base φ ∂uniformSphere (dims j)) =
          2 * (R * ∫⁻ φ, base φ ∂uniformSphere (dims j)) by ac_rfl,
        ← MeasureTheory.lintegral_const_mul _ hbase]
      apply congrArg (fun z : ℝ≥0∞ => 2 * z)
      apply lintegral_congr
      intro φ
      unfold correctedMeshEventKernel correctedCellEventKernel R base
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ac_rfl

/-- Selected-block integral of the normalized finite-stage bridge.  The
endpoint premise is deliberately in the `Gj`-then-sphere order required by
cellwise insertion; the other order is obtained by an
interchange of integrals (`MinamiCorrectedProductFatou`). -/
theorem selected_lintegral_correctedGridFullPredecessor_le_two_meshEventKernel
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (e t xi : ℝ) {eta : ℝ} (heta : 0 < eta)
    {a b : ℝ} (hab : a ≤ b) (M r : ℕ)
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
          ((correctedSelectedGridOccupiedCount
            A₀ j heta Gext e t xi M Gj : ℝ≥0∞) *
            fullPublicFixedPredecessorWeight A₀ a b r
              ((BlockProductDisintegration.split dims j).symm (Gext, Gj))) *
          ENNReal.ofReal (poissonRadialWeight eta xi)
      ∂BlockProductDisintegration.selectedMeasure dims hd j) ≤
      2 * ∫⁻ Gj, ∫⁻ φ,
        correctedMeshEventKernel A₀ j heta Gext a b M r
          ((φ, Gj), ((e, t), xi))
        ∂uniformSphere (dims j)
        ∂BlockProductDisintegration.selectedMeasure dims hd j := by
  calc
    _ ≤ ∫⁻ Gj, 2 * ∫⁻ φ,
        correctedMeshEventKernel A₀ j heta Gext a b M r
          ((φ, Gj), ((e, t), xi))
        ∂uniformSphere (dims j)
        ∂BlockProductDisintegration.selectedMeasure dims hd j := by
      apply lintegral_mono_ae
      filter_upwards [hend] with Gj hGj
      exact
        correctedGridOccupied_normalizedFullPredecessor_le_two_meshEventKernel
          dims hd j A₀ Gext Gj e t xi heta hab M r hGj
    _ = _ := by
      rw [MeasureTheory.lintegral_const_mul]
      let f := fun p : BlockProductDisintegration.SelectedSample dims j ×
          EuclideanSpace ℂ (Fin (dims j)) =>
        correctedMeshEventKernel A₀ j heta Gext a b M r
          ((p.2, p.1), ((e, t), xi))
      have hf : Measurable f :=
        (measurable_correctedMeshEventKernel
          dims A₀ j heta Gext a b M r).comp
            ((measurable_snd.prodMk measurable_fst).prodMk measurable_const)
      exact hf.lintegral_prod_right

end PSSSNative.BlockBand.PSSS
