module
public import BlockBand.SourceProcess.Stochastic.RankBarrier.Main
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The ambient rank barrier with its explicit constant

`RankBarrierProof.gramRankBarrier_holds` proves `GramRankBarrier` with an existential constant.
This file re-runs the same proof (same lemmas of `RankBarrier/`) with the constant exposed as
`ambientBarrierConst D0 P D k K`, and bounds it by `uniformBarrierConst D0 D k K` whenever
`|ι| ≤ 2|c|` and `‖P‖ ≤ √(2|c|)` (`ambientBarrierConst_le`). Hypotheses: `0 ≤ D₀`, `Pᴴ = P`,
`P² = P`, `‖V‖² ≤ K`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix Finset BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra BlockBand.SourceProcess.Stochastic.RankBarrierProof

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c]

/-- The constant of the ambient proof `gramRankBarrier_holds`. -/
def ambientBarrierConst (D0 : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (k : ℕ) (K : ℝ) : ℝ :=
  (Fintype.card (SourceNoise ι) : ℝ) * (Fintype.card ((Fin k → ι) × (Fin k → c)) : ℝ) ^ 2 *
    (((k : ℝ) * (Real.sqrt D0 / 2 * (‖P‖ * defectRadius P D (Real.sqrt K)))) ^ 2 +
      ((k : ℝ) * ((‖P‖ * Real.sqrt K) *
        (Fintype.card c * (Real.sqrt D0 / 2 * (‖D‖ * Real.sqrt K))))) ^ 2)

omit [DecidableEq c] in
/-- The constant obtained for `|ι| ≤ M`, `‖P‖ ≤ √M` with `M = 2|c|`. -/
def uniformBarrierConst (D0 : ℝ) (D : Matrix c c ℂ) (k : ℕ) (K : ℝ) : ℝ :=
  ((2 * Fintype.card c : ℝ) * (2 * Fintype.card c : ℝ) * 2) *
    ((2 * Fintype.card c : ℝ) ^ k * (Fintype.card c : ℝ) ^ k) ^ 2 *
    (((k : ℝ) * (Real.sqrt D0 / 2 * (Real.sqrt (2 * Fintype.card c) *
        (Real.sqrt (2 * Fintype.card c) + Real.sqrt K * ‖D‖ * Real.sqrt K + 1)))) ^ 2 +
      ((k : ℝ) * ((Real.sqrt (2 * Fintype.card c) * Real.sqrt K) *
        (Fintype.card c * (Real.sqrt D0 / 2 * (‖D‖ * Real.sqrt K))))) ^ 2)

omit [DecidableEq ι] [DecidableEq c] in
theorem ambientBarrierConst_le (D0 : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (k : ℕ) (K : ℝ)
    (hι : Fintype.card ι ≤ 2 * Fintype.card c) (hP : ‖P‖ ≤ Real.sqrt (2 * Fintype.card c)) :
    ambientBarrierConst D0 P D k K ≤ uniformBarrierConst D0 D k K := by
  have hι' : (Fintype.card ι : ℝ) ≤ 2 * Fintype.card c := by exact_mod_cast hι
  unfold ambientBarrierConst uniformBarrierConst defectRadius
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
  push_cast
  gcongr

/-- **Ambient rank barrier with explicit constant** (proof of `gramRankBarrier_holds`). -/
theorem gramRankBarrier_explicit {D0 : ℝ} (hD0 : 0 ≤ D0) (Naux : ℕ) {P : Matrix ι ι ℂ}
    (hPH : Pᴴ = P) (hPP : P * P = P) (D : Matrix c c ℂ) (k : ℕ) (K : ℝ) (V : Matrix ι c ℂ)
    (hK : ‖V‖ ^ 2 ≤ K) :
    sdeGenerator (sourceDrift D0 Naux P) (sourceDiffusion D0 P D)
        (fun W => principalMinorSum k (nearGram P W)) V ≤
      ambientBarrierConst D0 P D k K * principalMinorSum k (nearGram P V) ∧
    sdeGenerator (sourceDrift D0 Naux P) (sourceDiffusion D0 P D)
        (fun W => principalMinorSum k (sourceGram W - nearGram P W)) V ≤
      ambientBarrierConst D0 P D k K * principalMinorSum k (sourceGram V - nearGram P V) := by
  have hR : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hsw : 0 ≤ Real.sqrt D0 / 2 := by positivity
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
      (near_drift_deriv k hD0 Naux P hPP V)
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

end BlockBand.SourceProcess.Stochastic.GramUniqueness
