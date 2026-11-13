module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.GramRealBridge
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Deterministic bounds for no rank creation

* `norm_toGramReal_le_of_feasible`: at a feasible state, every real Gram coordinate is bounded by
  `Re Tr M` (`|M_ij| ≤ ‖V‖², |B_ij| ≤ ‖PV‖² ≤ ‖V‖²`);
* continuity of `fromGramReal`, `gramRealDrift`, `gramRealCov` (product topology);
* `re_trace_lt_of_lt_stop`, `re_trace_le_of_le_stop`: before the trace stop `σ_K` the trace is
  `< K`, and `≤ K` at times `0 < u ≤ σ_K` on continuous paths.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix MeasureTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra BlockBand.SourceProcess.Stochastic.RankBarrierProof
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

omit [DecidableEq c] in
theorem norm_entry_sourceGram_le {ι : Type*} [Fintype ι] (V : Matrix ι c ℂ) (i j : c) :
    ‖sourceGram V i j‖ ≤ ‖V‖ ^ 2 := by
  refine (frob_entry_le _ i j).trans ((frobenius_norm_mul _ _).trans (le_of_eq ?_))
  rw [frobenius_norm_conjTranspose, sq]

omit [DecidableEq c] in
/-- At a feasible state the real Gram coordinates are bounded by `Re Tr M`. -/
theorem norm_toGramReal_le_of_feasible {D : Matrix c c ℂ} {H : Matrix c c ℂ × Matrix c c ℂ}
    (hH : GramFeasible D H) : ‖toGramReal H‖ ≤ (H.1.trace).re := by
  obtain ⟨n, N, P, V, hP, -, rfl⟩ := exists_realization_of_feasible hH
  rw [re_trace_fst_gramPair]
  have hPV : ‖P * V‖ ^ 2 ≤ ‖V‖ ^ 2 := by
    have h1 := re_trace_fst_gramPair (1 - P) ((1 - P) * V)
    have h2 := re_trace_fst_gramPair P (P * V)
    have h3 := re_trace_fst_gramPair P V
    simp only [gramPair] at h1 h2 h3
    have e : sourceGram V = sourceGram (P * V) + sourceGram ((1 - P) * V) := by
      rw [sourceGram, sourceGram, sourceGram, ← nearGram_eq P hP.1 hP.2.1, ← farGram_eq P hP.1 hP.2.1,
        sourceGram]
      abel
    rw [e, trace_add, Complex.add_re] at h3
    nlinarith [sq_nonneg ‖(1 - P) * V‖]
  have hB : ∀ i j, ‖nearGram P V i j‖ ≤ ‖V‖ ^ 2 := fun i j => by
    rw [nearGram_eq P hP.1 hP.2.1]
    exact (norm_entry_sourceGram_le (P * V) i j).trans hPV
  refine (pi_norm_le_iff_of_nonneg (sq_nonneg _)).2 fun q => ?_
  rw [toGramReal_apply, Real.norm_eq_abs]
  have hz : ‖gramEntry (qi q).1 (gramPair P V)‖ ≤ ‖V‖ ^ 2 := by
    unfold gramEntry gramPair
    split_ifs
    · exact norm_entry_sourceGram_le V _ _
    · exact hB _ _
  refine le_trans ?_ hz
  unfold reIm
  split_ifs
  · exact Complex.abs_re_le_norm _
  · exact Complex.abs_im_le_norm _

theorem continuous_fromGramReal' : Continuous fun y : Fin (gramDim c) → ℝ => fromGramReal y := by
  have : (fun y : Fin (gramDim c) → ℝ => fromGramReal y) =
      fun y => ∑ i, y i • gramFrame ((gramRealEquiv c).symm i) := funext fromGramReal_apply
  rw [this]
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

omit [DecidableEq c] in
theorem continuous_gramDriftG (D0 : ℝ) (D : Matrix c c ℂ) : Continuous (gramDriftG (c := c) D0 D) :=
  continuous_const.prodMk (((continuous_const.mul (continuous_gramScalar D)).neg).smul
    continuous_snd)

theorem continuous_gramRealDrift (D0 : ℝ) (D : Matrix c c ℂ) :
    Continuous (gramRealDrift (c := c) D0 D) :=
  continuous_toGramReal.comp ((continuous_gramDriftG D0 D).comp continuous_fromGramReal')

theorem continuous_gramRealCov (D0 : ℝ) (D : Matrix c c ℂ) :
    Continuous (gramRealCov (c := c) D0 D) := by
  refine continuous_matrix fun i j => ?_
  simp only [gramRealCov, realCovEntry_eq]
  exact ((realCovL _ _).continuous.comp ((continuous_gramCovEntry D0 D _ _).comp
    continuous_fromGramReal')).add ((realCovL' _ _).continuous.comp
    ((continuous_gramCovEntry D0 D _ _).comp continuous_fromGramReal'))

omit [DecidableEq c] in
theorem re_trace_lt_of_lt_stop {Ω : Type*} {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ}
    {K : ℝ} {ω : Ω} {u : ℝ≥0} (h : (u : WithTop ℝ≥0) < gramTraceStop G K ω) :
    ((G u ω).1.trace).re < K := by
  by_contra hc
  push Not at hc
  exact absurd (iInf₂_le u hc) (not_le.mpr h)

omit [DecidableEq c] in
theorem re_trace_le_of_le_stop {Ω : Type*} {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ}
    {K : ℝ} {ω : Ω} (hc : Continuous fun t => G t ω) {u : ℝ≥0} (hu0 : 0 < u)
    (h : (u : WithTop ℝ≥0) ≤ gramTraceStop G K ω) : ((G u ω).1.trace).re ≤ K := by
  have hg : Continuous fun v => ((G v ω).1.trace).re :=
    Complex.continuous_re.comp ((continuous_fst.comp hc).matrix_trace)
  have hS : IsClosed {v : ℝ≥0 | ((G v ω).1.trace).re ≤ K} := isClosed_le hg continuous_const
  have hsub : Iio u ⊆ {v : ℝ≥0 | ((G v ω).1.trace).re ≤ K} := fun v hv =>
    (re_trace_lt_of_lt_stop (lt_of_lt_of_le (WithTop.coe_lt_coe.2 hv) h)).le
  have hu : u ∈ closure (Iio u) := by
    rw [closure_Iio' (a := u) ⟨0, hu0⟩]; exact le_rfl
  exact closure_minimal hsub hS hu

end BlockBand.SourceProcess.Stochastic.GramUniqueness
