module

public import BlockBand.SourceProcess.ModelExist.TransLoc
public import BlockBand.SourceProcess.BornUnique.Pin

/-!
# The trace stop of a born Gram process is a.s. a stopping time

Let `G` be adapted with `G − J` a.s. continuous, where `J = birthSum j β` has `𝓖₀`-measurable
birth times and jumps of nonnegative trace. Then `Re Tr G_t = x_t + Σ_f 1{β_f ≤ t} v_f` with
`x = Re Tr (G − J)` continuous and `v_f ≥ 0`, so `σ_K = inf {t : Re Tr G_t ≥ K}` is the hitting
time of the closed set `{(x, t, b) : x + Σ_f 1{b_f ≤ t} v_f ≥ K}` (upper semicontinuity) by the
continuous adapted process `(x_t, t, β)`; its raw version is a stopping time
(`exists_stop_ae_eq_traceStop`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Finset
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.BornUnique
open scoped NNReal ENNReal

variable {c F : Type*} [Fintype c] [Fintype F]

/-- `x + Σ_f 1{b_f ≤ t} v_f` at `p = (x, t, b)`. -/
def jumpTr (v : F → ℝ) (p : ℝ × ℝ × (F → ℝ)) : ℝ :=
  p.1 + ∑ f, {q : ℝ × ℝ × (F → ℝ) | q.2.2 f ≤ q.2.1}.indicator (fun _ => v f) p

theorem isClosed_jumpTr {v : F → ℝ} (hv : ∀ f, 0 ≤ v f) (K : ℝ) :
    IsClosed (jumpTr v ⁻¹' Ici K) := by
  refine UpperSemicontinuous.isClosed_preimage ?_ K
  refine continuous_fst.upperSemicontinuous.add (upperSemicontinuous_sum fun f _ => ?_)
  exact IsClosed.upperSemicontinuous_indicator
    (isClosed_le ((continuous_apply f).comp (continuous_snd.comp continuous_snd))
      (continuous_fst.comp continuous_snd)) (hv f)

omit [Fintype c] in
theorem re_trace_birthSum [Fintype c] (j : F → Matrix c c ℂ × Matrix c c ℂ) (b : F → ℝ) (t : ℝ) :
    ((birthSum j b t).1.trace).re = ∑ f, if b f ≤ t then ((j f).1.trace).re else 0 := by
  simp only [birthSum, Prod.fst_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  split_ifs <;> simp

/-- The continuous process `(Re Tr (G − J)_t, t, β)`. -/
def zProc {Ω : Type*} (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ)
    (j : F → Matrix c c ℂ × Matrix c c ℂ) (β : F → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    ℝ × ℝ × (F → ℝ) :=
  (((G t ω - birthSum j (fun f => β f ω) t).1.trace).re, (t : ℝ), fun f => β f ω)

theorem mem_jumpTr_iff {Ω : Type*} (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ)
    (j : F → Matrix c c ℂ × Matrix c c ℂ) (β : F → Ω → ℝ) (K : ℝ) (t : ℝ≥0) (ω : Ω) :
    zProc G j β t ω ∈ jumpTr (fun f => ((j f).1.trace).re) ⁻¹' Ici K ↔
      K ≤ ((G t ω).1.trace).re := by
  have e : ((G t ω).1.trace).re = ((G t ω - birthSum j (fun f => β f ω) t).1.trace).re +
      ((birthSum j (fun f => β f ω) t).1.trace).re := by
    simp only [Prod.fst_sub, Matrix.trace_sub, Complex.sub_re]; ring
  rw [e, re_trace_birthSum]
  simp only [Set.mem_preimage, Set.mem_Ici, jumpTr, zProc, Set.indicator, Set.mem_ofPred_eq]

theorem hitTime_zProc {Ω : Type*} (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ)
    (j : F → Matrix c c ℂ × Matrix c c ℂ) (β : F → Ω → ℝ) (K : ℝ) (ω : Ω) :
    hitTime (jumpTr (fun f => ((j f).1.trace).re) ⁻¹' Ici K) (zProc G j β) ω =
      gramTraceStop G K ω := by
  simp only [hitTime, gramTraceStop, mem_jumpTr_iff G j β K]

omit [Fintype c] [Fintype F] in
theorem measurable_vec_of {Ω : Type*} {m : MeasurableSpace Ω} {β : F → Ω → ℝ}
    (h : ∀ f, Measurable[m] (β f)) : Measurable[m] (fun ω => fun f => β f ω) := by
  let _ := m
  exact Measurable.of_eval h

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

omit [Fintype c] in
theorem stronglyMeasurable_birthSum [Fintype c] {j : F → Matrix c c ℂ × Matrix c c ℂ}
    {β : F → Ω → ℝ} (hβ : ∀ f, Measurable[𝓖 0] (β f)) (t : ℝ≥0) :
    StronglyMeasurable[𝓖 0] (fun ω => birthSum j (fun f => β f ω) t) := by
  simp only [birthSum]
  exact Finset.stronglyMeasurable_fun_sum _ fun f _ =>
    StronglyMeasurable.ite (measurableSet_le (hβ f) measurable_const) stronglyMeasurable_const
      stronglyMeasurable_const

/-- **The trace stop of a born process agrees a.s. with a stopping time.** -/
theorem exists_stop_ae_eq_traceStop {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ}
    (hG : ∀ t, StronglyMeasurable[𝓖 t] (G t)) {j : F → Matrix c c ℂ × Matrix c c ℂ}
    (hj : ∀ f, 0 ≤ ((j f).1.trace).re) {β : F → Ω → ℝ} (hβ : ∀ f, Measurable[𝓖 0] (β f))
    (hc : ∀ᵐ ω ∂Q, Continuous fun t => G t ω - birthSum j (fun f => β f ω) t) (K : ℝ) :
    ∃ ρ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 ρ ∧ ∀ᵐ ω ∂Q, ρ ω = gramTraceStop G K ω := by
  have hZ : ∀ t, Measurable[𝓖 t] (zProc G j β t) := fun t => by
    have h1 : StronglyMeasurable[𝓖 t] (fun ω =>
        ((G t ω - birthSum j (fun f => β f ω) t).1.trace).re) :=
      (Complex.continuous_re.comp (continuous_fst.matrix_trace)).comp_stronglyMeasurable
        ((hG t).sub ((stronglyMeasurable_birthSum hβ t).mono (𝓖.mono zero_le)))
    exact h1.measurable.prodMk (measurable_const.prodMk
      (measurable_vec_of fun f => (hβ f).mono (𝓖.mono zero_le) le_rfl))
  refine ⟨rawHit (jumpTr (fun f => ((j f).1.trace).re) ⁻¹' Ici K) (zProc G j β),
    isStoppingTime_rawHit hZ, ?_⟩
  filter_upwards [hc] with ω h
  rw [rawHit_eq_hitTime (Y := zProc G j β) (isClosed_jumpTr hj K), hitTime_zProc]
  exact (Complex.continuous_re.comp ((continuous_fst.comp h).matrix_trace)).prodMk
    (NNReal.continuous_coe.prodMk continuous_const)

end BlockBand.SourceProcess.ModelExist
