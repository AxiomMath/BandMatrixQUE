module
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEWeightedUnitaryProjection
/-!
# Weighted canonical GUE inverse tail for arbitrary unit vectors

The weighted inverse tail bound for the canonical GUE law, transported by unitary invariance from
the first coordinate vector to an arbitrary deterministic unit vector.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 800000
namespace PSSSNative.BlockBand.PSSS
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The weighted canonical GUE inverse tail transported from the canonical
coordinate to an arbitrary deterministic unit vector. -/
theorem canonicalGUE_arbitraryUnitVector_inverse_tail_weighted :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (N : ℕ) (_hN : 0 < N), ∀ (A : HermitianMatrix (Fin N))
      (φ : EuclideanSpace ℂ (Fin N)), ‖φ‖ = 1 →
      ∀ (F : (Matrix (Fin N) (Fin N) ℂ) → ℝ≥0∞), Measurable F →
      ∀ (t : ℝ), 1 ≤ t →
      let Pφ := orthProj φ
      let law := canonicalHermitianGUEPushforward N (canonicalGUEVariance N)
        (canonicalGUEVariance_nonneg N)
      (∫⁻ V, Set.indicator {V | t * Real.sqrt N ≤
          ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ WithLp.ofLp φ) :
            EuclideanSpace ℂ (Fin N))‖} (fun _ => (1 : ℝ≥0∞)) V *
          F (Pφ * V.1 * Pφ) ∂law) ≤
        ENNReal.ofReal (C / t) * ∫⁻ V, F (Pφ * V.1 * Pφ) ∂law := by
  obtain ⟨C, hC, htail⟩ := canonicalGUE_fixedVector_inverse_tail_weighted
  refine ⟨C, hC, ?_⟩
  intro N _hN A φ hφ F hF t ht Pφ law
  have hφ' : ‖complexEuclideanVector (WithLp.ofLp φ)‖ = 1 := by
    simpa [complexEuclideanVector] using hφ
  obtain ⟨U, hU, hUφ, hmap, _⟩ :=
    exists_arbitraryUnitVector_GUE_disintegration _hN (WithLp.ofLp φ) hφ'
      (canonicalGUEVariance N) (canonicalGUEVariance_nonneg N)
  have hmaplaw : Measure.map (conjugateHermitian U) law = law := by
    simpa only [law] using hmap
  let A' := conjugateHermitian U A
  let P₀ := orthProj (canonicalFirstEuclidean _hN)
  let G := fun X : Matrix (Fin N) (Fin N) ℂ => F (U * X * Uᴴ)
  let E := {V : HermitianMatrix (Fin N) | t * Real.sqrt N ≤
    ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ WithLp.ofLp φ) :
      EuclideanSpace ℂ (Fin N))‖}
  let E' := {V : HermitianMatrix (Fin N) | t * Real.sqrt N ≤
    ‖(WithLp.toLp 2 ((A'.1 + V.1)⁻¹ *ᵥ
      phaseFixedCoordinateVector ⟨0, _hN⟩) : EuclideanSpace ℂ (Fin N))‖}
  have hpre : (conjugateHermitian U) ⁻¹' E' = E := by
    ext V
    change (t * Real.sqrt N ≤ ‖(WithLp.toLp 2
      (((conjugateHermitian U A).1 + (conjugateHermitian U V).1)⁻¹ *ᵥ
        phaseFixedCoordinateVector ⟨0, _hN⟩) : EuclideanSpace ℂ (Fin N))‖) ↔
      (t * Real.sqrt N ≤ ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ WithLp.ofLp φ) :
        EuclideanSpace ℂ (Fin N))‖)
    rw [conjugateHermitian_add_inv_mulVec_firstCoordinate _hN U hU
      (WithLp.ofLp φ) hUφ A V, norm_conjTranspose_mulVec_of_unitary U hU]
  have hE' : MeasurableSet E' :=
    measurableSet_arbitraryVector_inverse_event A'
      (phaseFixedCoordinateVector ⟨0, _hN⟩) (t * Real.sqrt N)
  have hG : Measurable G := measurable_unitaryConjugatedWeight U F hF
  have hcanon := htail N _hN A' t ht G hG
  have hcompress (V : HermitianMatrix (Fin N)) :
      G (P₀ * (conjugateHermitian U V).1 * P₀) = F (Pφ * V.1 * Pφ) := by
    unfold G P₀ Pφ conjugateHermitian
    exact congrArg F (unitary_mul_canonicalCompression_mul_conjTranspose
      _hN U hU φ hUφ V.1)
  have hmcomp : Measurable fun V : HermitianMatrix (Fin N) => G (P₀ * V.1 * P₀) := by
    apply hG.comp
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  let q := fun V : HermitianMatrix (Fin N) =>
    Set.indicator E' (fun _ => (1 : ℝ≥0∞)) V * G (P₀ * V.1 * P₀)
  have hq : Measurable q := (measurable_const.indicator hE').mul hmcomp
  have hinvq : (∫⁻ V, q (conjugateHermitian U V) ∂law) =
      ∫⁻ V, q V ∂law := by
    calc
      _ = ∫⁻ V, q V ∂Measure.map (conjugateHermitian U) law :=
        (lintegral_map' hq.aemeasurable
          (measurable_conjugateHermitian U).aemeasurable).symm
      _ = _ := by rw [hmaplaw]
  have hinvcomp : (∫⁻ V, G (P₀ * (conjugateHermitian U V).1 * P₀) ∂law) =
      ∫⁻ V, G (P₀ * V.1 * P₀) ∂law := by
    calc
      _ = ∫⁻ V, G (P₀ * V.1 * P₀)
          ∂Measure.map (conjugateHermitian U) law :=
        (lintegral_map' hmcomp.aemeasurable
          (measurable_conjugateHermitian U).aemeasurable).symm
      _ = _ := by rw [hmaplaw]
  have hleft : (∫⁻ V, Set.indicator E (fun _ => (1 : ℝ≥0∞)) V *
      F (Pφ * V.1 * Pφ) ∂law) = ∫⁻ V, q V ∂law := by
    calc
      _ = ∫⁻ V, q (conjugateHermitian U V) ∂law := by
        apply lintegral_congr
        intro V
        unfold q
        rw [hcompress]
        have heq : Set.indicator E' (fun _ => (1 : ℝ≥0∞))
            (conjugateHermitian U V) =
            Set.indicator E (fun _ => (1 : ℝ≥0∞)) V := by
          have hm : (conjugateHermitian U V ∈ E') ↔ V ∈ E :=
            Set.ext_iff.mp hpre V
          by_cases h : V ∈ E
          · simp [Set.indicator, h, hm.mpr h]
          · have hn : conjugateHermitian U V ∉ E' := fun hc => h (hm.mp hc)
            simp [Set.indicator, h, hn]
        exact congrArg (fun z => z * F (Pφ * V.1 * Pφ)) heq.symm
      _ = ∫⁻ V, q V ∂law := hinvq
  have hright : (∫⁻ V, G (P₀ * V.1 * P₀) ∂law) =
      ∫⁻ V, F (Pφ * V.1 * Pφ) ∂law := by
    calc
      _ = ∫⁻ V, G (P₀ * (conjugateHermitian U V).1 * P₀) ∂law :=
        hinvcomp.symm
      _ = _ := lintegral_congr hcompress
  rw [hleft]
  exact hcanon.trans_eq (congrArg (ENNReal.ofReal (C / t) * ·) hright)

end PSSSNative.BlockBand.PSSS
