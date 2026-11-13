module
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUECanonicalWeightedFixedVector
/-!
# Weighted canonical fixed-vector tail in every positive dimension

The weighted inverse tail bound at the first coordinate vector for the canonical GUE law, with one
constant valid in every positive dimension.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace PSSSNative.BlockBand.PSSS
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Weighted canonical-coordinate fixed-vector inverse tail, uniformly in every
positive dimension. -/
theorem canonicalGUE_fixedVector_inverse_tail_weighted :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (N : ℕ) (hN : 0 < N), ∀ (A : HermitianMatrix (Fin N))
      (t : ℝ), 1 ≤ t →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞), Measurable F →
      let P := orthProj (canonicalFirstEuclidean hN)
      let law := canonicalHermitianGUEPushforward N (canonicalGUEVariance N)
        (canonicalGUEVariance_nonneg N)
      (∫⁻ V, Set.indicator {V | t * Real.sqrt N ≤
          ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ phaseFixedCoordinateVector ⟨0, hN⟩) :
            EuclideanSpace ℂ (Fin N))‖} (fun _ => (1 : ℝ≥0∞)) V *
          F (P * V.1 * P) ∂law) ≤
        ENNReal.ofReal (C / t) * ∫⁻ V, F (P * V.1 * P) ∂law := by
  obtain ⟨K, hK, hsucc⟩ := canonicalGUE_fixedVector_inverse_tail_weighted_succ
  refine ⟨K + 2, by linarith, ?_⟩
  intro N hN A t ht F hF P law
  cases N with
  | zero => simp at hN
  | succ n =>
    by_cases hn : n = 0
    · subst n
      have h1 := canonicalGUE_one_fixedVector_inverse_tail_weighted A t ht F
      have hvec : phaseFixedCoordinateVector ⟨0, hN⟩ = canonicalUnitVectorOne := by
        funext i
        fin_cases i
        rfl
      have hcan : canonicalFirstEuclidean hN =
          canonicalFirstEuclidean (by norm_num : 0 < 1) := by
        congr 1
      have hconst : ENNReal.ofReal (2 / t) ≤ ENNReal.ofReal ((K + 2) / t) :=
        ENNReal.ofReal_le_ofReal (by
          have ht0 : 0 < t := by linarith
          apply (div_le_div_iff_of_pos_right ht0).2
          linarith)
      have hmul : ENNReal.ofReal (2 / t) *
          (∫⁻ V, F (P * V.1 * P) ∂law) ≤
          ENNReal.ofReal ((K + 2) / t) *
          (∫⁻ V, F (P * V.1 * P) ∂law) :=
        mul_le_mul_of_nonneg_right hconst bot_le
      dsimp only [P, law] at hmul ⊢
      norm_num at hmul ⊢
      rw [hcan]
      rw [show phaseFixedCoordinateVector (0 : Fin 1) =
          canonicalUnitVectorOne by
        funext i
        fin_cases i
        rfl]
      simpa only [Nat.cast_one, Real.sqrt_one, mul_one] using h1.trans hmul
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hs := hsucc n hnpos A t ht F hF
      have hconst : ENNReal.ofReal (K / t) ≤ ENNReal.ofReal ((K + 2) / t) :=
        ENNReal.ofReal_le_ofReal (by
          have ht0 : 0 < t := by linarith
          apply (div_le_div_iff_of_pos_right ht0).2
          linarith)
      simpa [P, law, Nat.cast_add, Nat.cast_one] using
        hs.trans (mul_le_mul_of_nonneg_right hconst bot_le)

end PSSSNative.BlockBand.PSSS
