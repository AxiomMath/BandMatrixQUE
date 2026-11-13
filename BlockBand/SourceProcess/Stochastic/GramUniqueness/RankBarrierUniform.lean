module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.BarrierExplicit
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.GramGenerator
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.Reduction
public import BlockBand.SourceProcess.Stochastic.SourceAlgebra.TraceLyapunov
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The uniform Gram rank barrier `GramRankBarrierUniform`

Proof of `GramRankBarrierUniform D0 D`:
the constant `uniformBarrierConst D0 D k K` works for every ambient dimension `n`, rank `Naux`
and near projection `P`. Proof outline:

1. the generator of `W ↦ e_k(B(W))` and of `W ↦ e_k((M−B)(W))` at a
   constrained frame depends only on the Gram pair `(M, B)` of the frame — the `Naux`-terms of
   the drift `-(D₀Naux/4)PV` cancel against the Itô term (Gram drift), and the second-order
   term is fixed by the Gram covariance;
2. every constrained frame has a constrained realization of the same Gram pair
   in `ℂ^m`, `m ≤ 2|c|`, whose near projection `P̃` has `‖P̃‖² = rank ≤ m`;
3. the ambient barrier holds in that realization with the explicit constant
   `ambientBarrierConst ≤ uniformBarrierConst`.

So the answer to "does `sourceDrift` depend on `Naux` in a way that makes the constant
non-uniform?" is no: the `Naux`-dependence is real for each fixed realization (the ambient
constant grows with `|ι|` and `‖P‖ = √Naux`), but it disappears after the exact Gram reduction.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix Finset BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra BlockBand.SourceProcess.Stochastic.RankBarrierProof

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- `e_k` is a polynomial in the matrix entries. -/
theorem contDiff_principalMinorSum_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) {A : E → Matrix c c ℂ} (hA : ∀ i j, ContDiff ℝ 2 fun x => A x i j) :
    ContDiff ℝ 2 fun x => principalMinorSum k (A x) := by
  unfold principalMinorSum
  exact Complex.reCLM.contDiff.comp
    (ContDiff.sum fun s _ => contDiff_det' fun i j => hA _ _)

theorem contDiff_ek_snd (k : ℕ) :
    ContDiff ℝ 2 fun G : Matrix c c ℂ × Matrix c c ℂ => principalMinorSum k G.2 :=
  contDiff_principalMinorSum_comp k fun i j => (contDiff_entry i j).comp contDiff_snd

theorem contDiff_ek_fst_sub_snd (k : ℕ) :
    ContDiff ℝ 2 fun G : Matrix c c ℂ × Matrix c c ℂ => principalMinorSum k (G.1 - G.2) :=
  contDiff_principalMinorSum_comp k fun i j =>
    ((contDiff_entry i j).comp contDiff_fst).sub ((contDiff_entry i j).comp contDiff_snd)

theorem principalMinorSum_near_nonneg {ι : Type*} [Fintype ι] {P : Matrix ι ι ℂ} (hPH : Pᴴ = P)
    (hPP : P * P = P) (k : ℕ) (V : Matrix ι c ℂ) : 0 ≤ principalMinorSum k (nearGram P V) := by
  rw [nearGram_eq P hPH hPP, principalMinorSum_gram]
  exact div_nonneg (minorSq_nonneg _ _) (by positivity)

theorem principalMinorSum_far_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ}
    (hPH : Pᴴ = P) (hPP : P * P = P) (k : ℕ) (V : Matrix ι c ℂ) :
    0 ≤ principalMinorSum k (sourceGram V - nearGram P V) := by
  rw [farGram_eq P hPH hPP, principalMinorSum_gram]
  exact div_nonneg (minorSq_nonneg _ _) (by positivity)

/-- **`GramRankBarrierUniform` holds.** -/
theorem gramRankBarrierUniform_holds (D0 : ℝ) (D : Matrix c c ℂ) :
    GramRankBarrierUniform D0 D := by
  intro hD0 hD k K
  refine ⟨uniformBarrierConst D0 D k K, fun n Naux P V hP hV hK => ?_⟩
  obtain ⟨m, N, Pt, Vt, hm, hNm, hPt, hVt, hG⟩ := exists_small_realization hP hV
  have hKt : ‖Vt‖ ^ 2 ≤ K := by
    have h1 := sourceGram_trace Vt
    rw [show sourceGram Vt = sourceGram V from congrArg Prod.fst hG, sourceGram_trace V] at h1
    rw [← Complex.ofReal_inj.mp h1]
    exact hK
  have hPn : ‖Pt‖ ≤ Real.sqrt (2 * Fintype.card c) := by
    rw [← Real.sqrt_sq (norm_nonneg Pt), frob_sq_nearProjection hPt]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hNm.trans hm)
  have hC := ambientBarrierConst_le D0 Pt D k K (by simpa using hm) hPn
  obtain ⟨hn, hf⟩ := gramRankBarrier_explicit hD0.le N hPt.1 hPt.2.1 D k K Vt hKt
  have hBe : nearGram Pt Vt = nearGram P V := congrArg Prod.snd hG
  have hMe : sourceGram Vt = sourceGram V := congrArg Prod.fst hG
  have e1 : sdeGenerator (sourceDrift D0 Naux P) (sourceDiffusion D0 P D)
      (fun W => principalMinorSum k (nearGram P W)) V =
      sdeGenerator (sourceDrift D0 N Pt) (sourceDiffusion D0 Pt D)
        (fun W => principalMinorSum k (nearGram Pt W)) Vt :=
    gram_generator_congr hD0.le hP hPt hD hV hVt hG.symm (contDiff_ek_snd k)
  have e2 : sdeGenerator (sourceDrift D0 Naux P) (sourceDiffusion D0 P D)
      (fun W => principalMinorSum k (sourceGram W - nearGram P W)) V =
      sdeGenerator (sourceDrift D0 N Pt) (sourceDiffusion D0 Pt D)
        (fun W => principalMinorSum k (sourceGram W - nearGram Pt W)) Vt :=
    gram_generator_congr hD0.le hP hPt hD hV hVt hG.symm (contDiff_ek_fst_sub_snd k)
  constructor
  · rw [e1]
    refine hn.trans ?_
    rw [hBe]
    exact mul_le_mul_of_nonneg_right hC (principalMinorSum_near_nonneg hP.1 hP.2.1 k V)
  · rw [e2]
    refine hf.trans ?_
    rw [hBe, hMe]
    exact mul_le_mul_of_nonneg_right hC (principalMinorSum_far_nonneg hP.1 hP.2.1 k V)

end BlockBand.SourceProcess.Stochastic.GramUniqueness
