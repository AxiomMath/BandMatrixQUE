module
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEOneDimensionalWeightedTail
/-!
# Positive-dimensional weighted canonical fixed-vector tail

For the canonical GUE law in dimension `n + 1`, `n ≥ 1`, the probability that the resolvent
`(A + V)⁻¹` applied to the first coordinate vector has norm `≥ t √(n+1)`, weighted by a measurable
function of the compression `P₀ V P₀`, is at most `K/t` times the expected weight (`t ≥ 1`).
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 1200000
namespace PSSSNative.BlockBand.PSSS
open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

theorem canonicalGUE_fixedVector_inverse_tail_weighted_succ :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (n : ℕ), 0 < n → ∀ (A : HermitianMatrix (Fin (n + 1)))
      (t : ℝ), 1 ≤ t →
      ∀ (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → ℝ≥0∞), Measurable G →
      let P₀ := orthProj (canonicalFirstEuclidean (Nat.succ_pos n))
      let law := canonicalHermitianGUEPushforward (n + 1)
        (canonicalGUEVariance (n + 1)) (canonicalGUEVariance_nonneg (n + 1))
      (∫⁻ V, Set.indicator {V | t * Real.sqrt (n + 1) ≤
          ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ phaseFixedCoordinateVector ⟨0, Nat.succ_pos n⟩) :
            EuclideanSpace ℂ (Fin (n + 1)))‖} (fun _ => (1 : ℝ≥0∞)) V *
          G (P₀ * V.1 * P₀) ∂law) ≤
        ENNReal.ofReal (K / t) * ∫⁻ V, G (P₀ * V.1 * P₀) ∂law := by
  obtain ⟨K, hK, htail⟩ := randomCompression_enlargedSchur_tail_projectedWeight
  refine ⟨K, hK, ?_⟩
  intro n hn A t ht G hG P₀ law
  let coordLaw := hermitianGUECoordinateMeasure (n + 1)
    (canonicalGUEVariance (n + 1)) (canonicalGUEVariance_nonneg (n + 1))
  let μ := (gaussianReal 0 1).prod
    (Measure.pi fun _ : Fin (2 * n) => gaussianReal 0 1)
  let ν := Measure.map (compressionGUECoordinates (n + 1)) coordLaw
  let Φ := fun x : HermitianCoordinateSpace (n + 1) =>
    (splitConcreteFirstColumn n (concreteStandardizedFirstColumn n x),
      compressionGUECoordinates (n + 1) x)
  let c := Real.sqrt (n + 1) * (zerothBlockScalar A.1).re
  let b := Real.sqrt (2 * (n + 1)) •
    reindexedComplexVectorRealification (zerothBlockColumn A.1)
  let D := fun u => zerothBlockCompression
    (A.1 + (compressionGUEHermitian (n + 1) u).1)
  have hcD : Continuous fun H : HermitianMatrix (Fin (n + 1)) =>
      zerothBlockCompression (A.1 + H.1) := by
    rw [show (fun H : HermitianMatrix (Fin (n + 1)) =>
        zerothBlockCompression (A.1 + H.1)) =
      fun H => (A.1 + H.1).submatrix Fin.succ Fin.succ by
        funext H
        exact zerothBlockCompression_eq_submatrix_succ _]
    exact continuous_const.add
      (continuous_subtype_val.matrix_submatrix Fin.succ Fin.succ)
  have hmD : Measurable D := hcD.measurable.comp
    (measurable_compressionGUEHermitian (n + 1))
  let Q := fun u => normalizedCompressionRealMatrix n (D u)
  have hmQ : Measurable Q :=
    PSSSNative.BlockBand.PSSS.Measurable.normalizedCompressionRealMatrix hmD
  let E : Set ((ℝ × (Fin (2 * n) → ℝ)) ×
      (CompressionGUECoordinate (n + 1) → ℝ)) :=
    {z | enlargedRealSchurEvent (Q z.2) c b t z.1}
  have hE : MeasurableSet E := by
    unfold E
    unfold enlargedRealSchurEvent
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
  let B : Set (HermitianMatrix (Fin (n + 1))) :=
    {V | t * Real.sqrt (n + 1) ≤
      ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ
        phaseFixedCoordinateVector ⟨0, Nat.succ_pos n⟩) :
        EuclideanSpace ℂ (Fin (n + 1)))‖}
  have hB : MeasurableSet B := by
    unfold B
    have hm : Measurable fun V : HermitianMatrix (Fin (n + 1)) =>
        (A.1 + V.1)⁻¹ :=
      PSSSNative.BlockBand.Measurable.matrixNonsingInv
        ((continuous_const.add continuous_subtype_val).measurable)
    have hv : Measurable fun V : HermitianMatrix (Fin (n + 1)) =>
        (A.1 + V.1)⁻¹ *ᵥ phaseFixedCoordinateVector 0 := by
      rw [measurable_pi_iff]
      intro i
      unfold Matrix.mulVec dotProduct
      fun_prop
    apply measurableSet_le
    · fun_prop
    · fun_prop
  have htvar : 0 < canonicalGUEVariance (n + 1) := by
    unfold canonicalGUEVariance
    positivity
  have hfull := ae_det_add_hermitianGUEBlock_ne_zero (n + 1)
    (t := canonicalGUEVariance (n + 1)) htvar A.1 A.2
  have hdetm := ae_compressionCoordinate_shifted_det_ne_zero A
  have hS : MeasurableSet {u : CompressionGUECoordinate (n + 1) → ℝ |
      (D u).det ≠ 0} := by
    let T : Set (HermitianMatrix (Fin (n + 1))) :=
      {H | (zerothBlockCompression (A.1 + H.1)).det ≠ 0}
    have hc : Continuous fun H : HermitianMatrix (Fin (n + 1)) =>
        (A.1 + H.1).submatrix Fin.succ Fin.succ :=
      continuous_const.add
        (continuous_subtype_val.matrix_submatrix Fin.succ Fin.succ)
    have hT : MeasurableSet T := by
      unfold T
      simp only [zerothBlockCompression_eq_submatrix_succ]
      exact ((measurableSet_singleton 0).preimage hc.matrix_det.measurable).compl
    exact hT.preimage (measurable_compressionGUEHermitian (n + 1))
  change ∀ᵐ u ∂ν, (D u).det ≠ 0 at hdetm
  rw [ae_map_iff (measurable_compressionGUECoordinates (n + 1)).aemeasurable hS] at hdetm
  have hsub : (hermitianGUEBlock (n + 1)) ⁻¹' B ≤ᵐ[coordLaw] Φ ⁻¹' E := by
    filter_upwards [hfull, hdetm] with x hxfull hxD hxB
    have hdata := canonicalCoordinate_schur_data A x
    have hDH : (zerothBlockCompression
        (A.1 + (hermitianGUEBlock (n + 1) x).1)).det ≠ 0 := by
      rw [← hdata.1]
      exact hxD
    exact canonicalInverseEvent_implies_enlarged A x t (by linarith)
      hDH hxfull hxB
  let W := fun z : (ℝ × (Fin (2 * n) → ℝ)) ×
    (CompressionGUECoordinate (n + 1) → ℝ) =>
  G (P₀ * (compressionGUEHermitian (n + 1) z.2).1 * P₀)
  have hΦ : Measurable Φ := by
    unfold Φ
    exact (((measurePreserving_splitConcreteFirstColumn n).measurable.comp
      (measurable_standardizedFirstColumnOfFirstRow n)).comp
        (measurable_firstRowGUECoordinates (n + 1))).prodMk
      (measurable_compressionGUECoordinates (n + 1))
  have hW : Measurable W := by
    unfold W
    exact (measurable_projectedCompressionWeight (Nat.succ_pos n) G hG).comp measurable_snd
  have hmapΦ : Measure.map Φ coordLaw = μ.prod ν := by
    simpa only [coordLaw, μ, ν, Φ] using
      (map_standardizedFirstColumnPair_compression_eq_prod n)
  have hweight : ∀ x : HermitianCoordinateSpace (n + 1),
      G (P₀ * (hermitianGUEBlock (n + 1) x).1 * P₀) = W (Φ x) := by
    intro x
    unfold W Φ
    rw [orthProj_hermitianGUEBlock_eq_projectedCompression (Nat.succ_pos n)]
  have hsource :
      (∫⁻ x, Set.indicator ((hermitianGUEBlock (n + 1)) ⁻¹' B)
          (fun _ => (1 : ℝ≥0∞)) x *
        G (P₀ * (hermitianGUEBlock (n + 1) x).1 * P₀) ∂coordLaw) ≤
      ∫⁻ z, Set.indicator E (fun _ => (1 : ℝ≥0∞)) z * W z ∂μ.prod ν := by
    exact lintegral_indicator_weight_le_of_map coordLaw (μ.prod ν) Φ hΦ
      ((hermitianGUEBlock (n + 1)) ⁻¹' B) E hE
      (fun x => G (P₀ * (hermitianGUEBlock (n + 1) x).1 * P₀)) W hW
      hweight hmapΦ hsub
  have htailW :
      (∫⁻ z, Set.indicator E (fun _ => (1 : ℝ≥0∞)) z * W z ∂μ.prod ν) ≤
        ENNReal.ofReal (K / t) * ∫⁻ u,
          G (P₀ * (compressionGUEHermitian (n + 1) u).1 * P₀) ∂ν := by
    simpa only [E, Q, W] using htail n hn A c b t ht G hG
  have hmatrix : Measurable fun V : HermitianMatrix (Fin (n + 1)) =>
      P₀ * V.1 * P₀ := by
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hproj : Measurable fun V : HermitianMatrix (Fin (n + 1)) =>
      G (P₀ * V.1 * P₀) := hG.comp hmatrix
  have hunweighted :
      (∫⁻ u, G (P₀ * (compressionGUEHermitian (n + 1) u).1 * P₀) ∂ν) =
        ∫⁻ V, G (P₀ * V.1 * P₀) ∂law := by
    have hcoord : (∫⁻ x, G (P₀ * (hermitianGUEBlock (n + 1) x).1 * P₀) ∂coordLaw) =
        ∫⁻ V, G (P₀ * V.1 * P₀) ∂law := by
      unfold law canonicalHermitianGUEPushforward
      exact (lintegral_map' hproj.aemeasurable
        (measurable_hermitianGUEBlock (n + 1)).aemeasurable).symm
    rw [← hcoord]
    rw [show (∫⁻ u, G (P₀ * (compressionGUEHermitian (n + 1) u).1 * P₀) ∂ν) =
        ∫⁻ z, W z ∂μ.prod ν by
      rw [lintegral_prod_symm' W hW]
      simp only [W]
      let _ : IsProbabilityMeasure μ := by unfold μ; infer_instance
      simp]
    rw [← hmapΦ]
    rw [lintegral_map' hW.aemeasurable hΦ.aemeasurable]
    apply lintegral_congr
    intro x
    exact hweight x |>.symm
  have hleft :
      (∫⁻ V, Set.indicator B (fun _ => (1 : ℝ≥0∞)) V * G (P₀ * V.1 * P₀) ∂law) =
      ∫⁻ x, Set.indicator ((hermitianGUEBlock (n + 1)) ⁻¹' B)
          (fun _ => (1 : ℝ≥0∞)) x *
        G (P₀ * (hermitianGUEBlock (n + 1) x).1 * P₀) ∂coordLaw := by
    unfold law canonicalHermitianGUEPushforward
    exact lintegral_map'
      (((measurable_const.indicator hB).mul hproj).aemeasurable)
      (measurable_hermitianGUEBlock (n + 1)).aemeasurable
  rw [hleft]
  exact hsource.trans (htailW.trans_eq (congrArg (ENNReal.ofReal (K / t) * ·) hunweighted))

end PSSSNative.BlockBand.PSSS
