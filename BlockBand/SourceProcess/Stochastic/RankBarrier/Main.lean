module
public import BlockBand.SourceProcess.Stochastic.RankBarrier.NearFar
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Gram rank barrier: proof

Proves `GramRankBarrier`. Proof outline (the paper's ambient lift):

1. `e_k(B) = ‖∧^k(PV)‖²/(k!)²`, `e_k(M−B) = ‖∧^k((1−P)V)‖²/(k!)²` (Cauchy–Binet; valid at
   singular matrices);
2. along each noise direction the near rows move by left multiplication and the far rows by
   right multiplication with rank-one coefficients, so every `k`-minor is affine along the noise
   line with slope a combination of `k`-minors;
3. the drift contracts the near minors (`(1 + tα)^k`, `α = −D₀Naux/4 ≤ 0`) and fixes the far ones;
4. hence `𝒢 e_k ≤ C e_k` with `C = |κ| |X|² B²`, where on `‖V‖² ≤ K` (`R = √K`) the slope
   coefficients are bounded by `B_near = k (√D₀/2) ‖P‖ (‖P‖ + R²‖𝖣‖ + 1)` and
   `B_far = k ‖P‖ R |c| (√D₀/2) ‖𝖣‖ R`.

The constant depends on `K, k, D₀, ‖P‖, ‖𝖣‖` and the ambient/column dimensions (allowed by the
statement). Hypotheses used: `0 < D₀` (only `0 ≤ D₀`), `Pᴴ = P`, `P² = P`. The signature
hypothesis on `𝖣`, `Tr P = Naux` and the two-projection constraint are not needed.
-/

namespace BlockBand.SourceProcess.Stochastic.RankBarrierProof
open Matrix Finset BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c]

/-- **The Gram rank barrier holds** (ambient form `GramRankBarrier`). -/
theorem gramRankBarrier_holds (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) :
    GramRankBarrier D0 Naux P D := by
  intro hD0 hP _ k K
  obtain ⟨hPH, hPP, -⟩ := hP
  have hR : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hsw : 0 ≤ Real.sqrt D0 / 2 := by positivity
  refine ⟨(Fintype.card (SourceNoise ι) : ℝ) *
      (Fintype.card ((Fin k → ι) × (Fin k → c)) : ℝ) ^ 2 *
      (((k : ℝ) * (Real.sqrt D0 / 2 * (‖P‖ * defectRadius P D (Real.sqrt K)))) ^ 2 +
        ((k : ℝ) * ((‖P‖ * Real.sqrt K) *
          (Fintype.card c * (Real.sqrt D0 / 2 * (‖D‖ * Real.sqrt K))))) ^ 2),
    fun V _ hK => ?_⟩
  have hVR : ‖V‖ ≤ Real.sqrt K := by
    rw [← Real.sqrt_sq (norm_nonneg V)]; exact Real.sqrt_le_sqrt hK
  have hC0 : 0 ≤ (Fintype.card (SourceNoise ι) : ℝ) *
      (Fintype.card ((Fin k → ι) × (Fin k → c)) : ℝ) ^ 2 := by positivity
  constructor
  · rw [nearMinor_fun k P hPH hPP, nearGram_eq P hPH hPP, principalMinorSum_gram]
    have hw : ∀ a : SourceNoise ι, ∀ l,
        ‖sourceWeight D0 a.2 * (P * gramProjection P V D) l a.1.2‖ ≤
          Real.sqrt D0 / 2 * (‖P‖ * defectRadius P D (Real.sqrt K)) := by
      intro a l
      rw [norm_mul, norm_sourceWeight]
      exact mul_le_mul_of_nonneg_left ((frob_entry_le _ _ _).trans ((frobenius_norm_mul _ _).trans
        (mul_le_mul_of_nonneg_left (gramProjection_norm_le hVR) (norm_nonneg _)))) hsw
    have hg := generator_minorSq_le k P (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) V
      ((k : ℝ) * (Real.sqrt D0 / 2 * (‖P‖ * defectRadius P D (Real.sqrt K))))
      (near_drift_deriv k hD0.le Naux P hPP V)
      (fun a => ⟨_, fun t p => near_lin D0 P D a V t p,
        fun p => norm_rowSlope_le _ _ _ (hw a) p⟩)
    refine hg.trans (mul_le_mul_of_nonneg_right ?_
      (div_nonneg (minorSq_nonneg _ _) (by positivity)))
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) hC0
  · rw [farMinor_fun k P hPH hPP, farGram_eq P hPH hPP, principalMinorSum_gram]
    have hz : ∀ a : SourceNoise ι, ∀ m',
        ‖sourceWeight D0 a.2 * (D * Vᴴ) m' a.1.2‖ ≤ Real.sqrt D0 / 2 * (‖D‖ * Real.sqrt K) := by
      intro a m'
      rw [norm_mul, norm_sourceWeight]
      refine mul_le_mul_of_nonneg_left ((frob_entry_le _ _ _).trans ((frobenius_norm_mul _ _).trans
        ?_)) hsw
      rw [frobenius_norm_conjTranspose]
      exact mul_le_mul_of_nonneg_left hVR (norm_nonneg _)
    have hy : ∀ a : SourceNoise ι, ∀ m, ‖(P * V) a.1.1 m‖ ≤ ‖P‖ * Real.sqrt K := fun a m =>
      (frob_entry_le _ _ _).trans ((frobenius_norm_mul _ _).trans
        (mul_le_mul_of_nonneg_left hVR (norm_nonneg _)))
    have hdrift : ∃ d ≤ (0 : ℝ), HasDerivAt (fun t : ℝ =>
        minorSq k ((1 - P) * (V + t • sourceDrift D0 Naux P V)) / (k.factorial : ℝ) ^ 2) d 0 := by
      refine ⟨0, le_rfl, ?_⟩
      simp_rw [far_drift_line D0 Naux P hPP V]
      exact hasDerivAt_const _ _
    have hg := generator_minorSq_le k (1 - P) (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) V
      ((k : ℝ) * ((‖P‖ * Real.sqrt K) *
        (Fintype.card c * (Real.sqrt D0 / 2 * (‖D‖ * Real.sqrt K))))) hdrift
      (fun a => ⟨_, fun t p => far_lin D0 P hPP D a V t p,
        fun p => norm_colSlope_le _ _ _ (by positivity) (by positivity) (hz a) (hy a) p⟩)
    refine hg.trans (mul_le_mul_of_nonneg_right ?_
      (div_nonneg (minorSq_nonneg _ _) (by positivity)))
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _)) hC0

end BlockBand.SourceProcess.Stochastic.RankBarrierProof
