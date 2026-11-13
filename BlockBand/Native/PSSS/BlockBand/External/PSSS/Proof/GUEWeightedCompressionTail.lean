module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiRankOneConditioning
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUECanonicalFixedVectorTail

/-!
# Weighted random-compression Schur tail

The factorial induction needs the fixed-vector tail after multiplication by a
nonnegative functional of the orthogonal compression.  This module proves the
Tonelli step in the first-row/compression product coordinates.  The
weight is arbitrary measurable and depends only on the compression coordinate;
no conditional law is assumed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- A uniform bound on the first-coordinate fibers of a product event remains
valid after multiplication by any measurable nonnegative function of the
second coordinate. -/
theorem lintegral_prod_indicator_mul_snd_le_of_fiber
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (E : Set (X × Y))
    [SFinite μ] [SFinite ν]
    (hE : MeasurableSet E) (W : Y → ℝ≥0∞) (hW : Measurable W)
    (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hfiber : ∀ᵐ y ∂ν, μ ((fun x => (x, y)) ⁻¹' E) ≤ c) :
    (∫⁻ z, Set.indicator E (fun _ => (1 : ℝ≥0∞)) z * W z.2 ∂μ.prod ν) ≤
      c * ∫⁻ y, W y ∂ν := by
  rw [MeasureTheory.lintegral_prod_symm']
  · calc
      (∫⁻ y, ∫⁻ x, Set.indicator E (fun _ => (1 : ℝ≥0∞)) (x, y) * W y ∂μ ∂ν) =
          ∫⁻ y, μ ((fun x => (x, y)) ⁻¹' E) * W y ∂ν := by
        apply lintegral_congr
        intro y
        let S := (fun x => (x, y)) ⁻¹' E
        have hS : MeasurableSet S :=
          hE.preimage (measurable_id.prodMk measurable_const)
        rw [show (fun x => Set.indicator E (fun _ => (1 : ℝ≥0∞)) (x, y) * W y) =
            Set.indicator S (fun _ => W y) by
          funext x
          by_cases hx : (x, y) ∈ E
          · simp [S, hx]
          · simp [S, hx]]
        rw [lintegral_indicator hS]
        rw [setLIntegral_const]
        simp only [S]
        ac_rfl
      _ ≤ ∫⁻ y, c * W y ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [hfiber] with y hy
        exact mul_le_mul_of_nonneg_right hy bot_le
      _ = c * ∫⁻ y, W y ∂ν := by
        rw [lintegral_const_mul']
        exact hc
  · exact (measurable_const.indicator hE).mul (hW.comp measurable_snd)

/-- Weighted form of the random-compression enlarged Schur estimate.  The
constant precedes the dimension, deformation, threshold, and compression
weight. -/
theorem randomCompression_enlargedSchur_tail_weighted :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (n : ℕ), 0 < n → ∀ (A : HermitianMatrix (Fin (n + 1)))
      (c : ℝ) (b : Fin (2 * n) → ℝ) (t : ℝ), 1 ≤ t →
      ∀ (W : (CompressionGUECoordinate (n + 1) → ℝ) → ℝ≥0∞), Measurable W →
      let μ := (gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (2 * n) => gaussianReal 0 1)
      let ν := Measure.map (compressionGUECoordinates (n + 1))
        (hermitianGUECoordinateMeasure (n + 1)
          (canonicalGUEVariance (n + 1))
          (canonicalGUEVariance_nonneg (n + 1)))
      let D := fun u => zerothBlockCompression
        (A.1 + (compressionGUEHermitian (n + 1) u).1)
      (∫⁻ z, Set.indicator {z | enlargedRealSchurEvent
          (normalizedCompressionRealMatrix n (D z.2)) c b t z.1}
          (fun _ => (1 : ℝ≥0∞)) z * W z.2 ∂μ.prod ν) ≤
        ENNReal.ofReal (K / t) * ∫⁻ u, W u ∂ν := by
  obtain ⟨K, hK, htail⟩ := enlargedRealSchurEvent_conditional_tail
  refine ⟨K, hK, ?_⟩
  intro n hn A c b t ht W hW μ ν D
  have hcD : Continuous fun H : HermitianMatrix (Fin (n + 1)) =>
      zerothBlockCompression (A.1 + H.1) := by
    rw [show (fun H : HermitianMatrix (Fin (n + 1)) =>
        zerothBlockCompression (A.1 + H.1)) =
      fun H => (A.1 + H.1).submatrix Fin.succ Fin.succ by
        funext H
        exact zerothBlockCompression_eq_submatrix_succ _]
    exact continuous_const.add
      (continuous_subtype_val.matrix_submatrix Fin.succ Fin.succ)
  have hmD : Measurable D := by
    unfold D
    exact hcD.measurable.comp (measurable_compressionGUEHermitian (n + 1))
  let Q := fun u => normalizedCompressionRealMatrix n (D u)
  have hmQ : Measurable Q :=
    PSSSNative.BlockBand.PSSS.Measurable.normalizedCompressionRealMatrix hmD
  let E : Set ((ℝ × (Fin (2 * n) → ℝ)) ×
      (CompressionGUECoordinate (n + 1) → ℝ)) :=
    {z | enlargedRealSchurEvent (Q z.2) c b t z.1}
  have hE : MeasurableSet E := by
    unfold E enlargedRealSchurEvent
    let v := fun z : (ℝ × (Fin (2 * n) → ℝ)) ×
        (CompressionGUECoordinate (n + 1) → ℝ) => z.1.2 + b
    let w := fun z : (ℝ × (Fin (2 * n) → ℝ)) ×
        (CompressionGUECoordinate (n + 1) → ℝ) => Q z.2 *ᵥ v z
    have hv : Measurable v := by unfold v; fun_prop
    have hw : Measurable w := by
      rw [measurable_pi_iff]
      intro i
      unfold w Matrix.mulVec dotProduct
      fun_prop
    have hdot : Measurable fun z => dotProduct (v z) (w z) := by
      unfold dotProduct
      fun_prop
    have hnorm : Measurable fun z =>
        ‖(WithLp.toLp 2 (w z) : EuclideanSpace ℝ (Fin (2 * n)))‖ := by
      fun_prop
    change MeasurableSet {z |
      (t * |z.1.1 + c - dotProduct (v z) (w z)|) ^ 2 ≤
        1 + 2 * ‖(WithLp.toLp 2 (w z) :
          EuclideanSpace ℝ (Fin (2 * n)))‖ ^ 2}
    apply measurableSet_le <;> fun_prop
  have hdet := ae_compressionCoordinate_shifted_det_ne_zero A
  have hfiber : ∀ᵐ u ∂ν,
      μ ((fun p => (p, u)) ⁻¹' E) ≤ ENNReal.ofReal (K / t) := by
    filter_upwards [hdet] with u hu
    have hHerm : (D u).IsHermitian := by
      unfold D
      rw [zerothBlockCompression_eq_submatrix_succ]
      exact (A.2.add (compressionGUEHermitian (n + 1) u).2).submatrix Fin.succ
    have hQtail := htail (2 * n) (normalizedCompressionRealMatrix n (D u))
      (normalizedCompressionRealMatrix_isSymm (D u) hHerm)
      (normalizedCompressionRealMatrix_ne_zero (D u) hn hu) c b t ht
    simpa only [E, Set.preimage_ofPred_eq] using hQtail
  exact lintegral_prod_indicator_mul_snd_le_of_fiber
    μ ν E hE W hW (ENNReal.ofReal (K / t)) ENNReal.ofReal_ne_top hfiber

end PSSSNative.BlockBand.PSSS
