module

public import BlockBand.SourceProcess.CapLimit.Embed
public import Mathlib.Probability.Martingale.Basic

/-!
# Born Gram solutions: a column that starts at zero stays zero

Let `G` be a born Gram solution (`IsBornGramSolution`), `y` a column with no birth jump on the
diagonal entry `M_yy`, and `A ∈ 𝓖₀` with `M_yy(0) = 0` a.s. on `A`. Then a.s. on `A`,
`M_yy(t) = 0` for all `t`. Proof: `M_yy` has zero drift, so its stopped compensated coordinate
`M_yy(t∧σ_L) − M_yy(0)` has a martingale modification `N`; `∫_A N_t = ∫_A N_0 = 0` and
`Re N_t = Re M_yy(t∧σ_L) ≥ 0` on `A` (feasibility), so `M_yy(t∧σ_L) = 0` a.s. on `A`. The trace
stops exceed every `t` for large `L` (continuity of `G − J`, bounded jumps), and the continuous
`M_yy = (G − J)_yy` vanishes on a countable dense set of times.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapLimit

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {c : Type*} [Fintype c] [DecidableEq c] {D0 : ℝ} {D : Matrix c c ℂ}
  {J G : ℝ≥0 → Ω → GramState c}

omit [MeasurableSpace Ω] [DecidableEq c] in
/-- With bounded jump traces and continuous `G − J`, the trace stops eventually exceed `t`. -/
theorem exists_le_gramTraceStop_born {ω : Ω} (hc : Continuous fun t => G t ω - J t ω)
    {C : ℝ} (hC : ∀ t, ((J t ω).1.trace).re ≤ C) (t : ℝ≥0) :
    ∃ L : ℕ, (t : WithTop ℝ≥0) ≤ gramTraceStop G L ω := by
  have hcont : Continuous fun s => ((G s ω - J s ω).1.trace).re :=
    Complex.continuous_re.comp ((continuous_fst.comp hc).matrix_trace)
  obtain ⟨R, hR⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_bound_of_continuousOn
    hcont.continuousOn
  obtain ⟨L, hL⟩ := exists_nat_gt (R + C)
  refine ⟨L, le_iInf₂ fun s hs => WithTop.coe_le_coe.2 ?_⟩
  by_contra h
  have h1 := hR s ⟨zero_le, (not_le.1 h).le⟩
  rw [Real.norm_eq_abs] at h1
  have h2 : ((G s ω).1.trace).re = ((G s ω - J s ω).1.trace).re + ((J s ω).1.trace).re := by
    simp [Matrix.trace_sub]
  linarith [le_abs_self ((G s ω - J s ω).1.trace.re), hC s]

omit [MeasurableSpace Ω] in
theorem bornCompensated_diag {y : c} (hJy : ∀ t ω, (J t ω).1 y y = 0) (t : ℝ≥0) (ω : Ω) :
    bornCompensated D0 D G J (0, y, y) t ω = (G t ω).1 y y - (G 0 ω).1 y y := by
  simp [bornCompensated, gramEntry, gramDriftEntry, hJy]

variable [IsFiniteMeasure Q]

/-- **Fixed time and trace level.** -/
theorem ae_stopped_diag_eq_zero (hG : IsBornGramSolution Q 𝓖 D0 D J G) {y : c}
    (hJy : ∀ t ω, (J t ω).1 y y = 0) {A : Set Ω} (hA : MeasurableSet[𝓖 0] A)
    (h0 : ∀ᵐ ω ∂Q, ω ∈ A → (G 0 ω).1 y y = 0) (t : ℝ≥0) (L : ℝ) :
    ∀ᵐ ω ∂Q, ω ∈ A → (stoppedProcess G (gramTraceStop G L) t ω).1 y y = 0 := by
  have hA' : MeasurableSet A := 𝓖.le 0 _ hA
  obtain ⟨N, hN, hNX⟩ := hG.drift L (0, y, y)
  have hst : ∀ u ω, stoppedProcess (bornCompensated D0 D G J (0, y, y)) (gramTraceStop G L) u ω
      = (stoppedProcess G (gramTraceStop G L) u ω).1 y y - (G 0 ω).1 y y := fun u ω => by
    simp only [stoppedProcess, bornCompensated_diag hJy]
  have hN0 : ∫ ω in A, N 0 ω ∂Q = 0 := by
    refine (integral_congr_ae (g := fun _ => (0 : ℂ)) ?_).trans (integral_zero _ _)
    refine ae_restrict_of_ae ?_
    filter_upwards [hNX 0] with ω hω
    rw [hω, hst, stoppedProcess_eq_of_le (by simp)]
    simp
  have hNt : ∫ ω in A, N t ω ∂Q = 0 :=
    (hN.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ t) hA).symm.trans hN0
  -- on `A`, `N t = M_yy(t ∧ σ)`, whose real part is nonnegative
  have heq : ∀ᵐ ω ∂Q, ω ∈ A → N t ω = (stoppedProcess G (gramTraceStop G L) t ω).1 y y := by
    filter_upwards [hNX t, h0] with ω hω h0ω hωA
    rw [hω, hst, h0ω hωA, sub_zero]
  have hpos : ∀ᵐ ω ∂Q, ω ∈ A → 0 ≤ (N t ω).re := by
    filter_upwards [heq, hG.feasible] with ω hω hf hωA
    rw [hω hωA]
    exact re_diag_nonneg (hf _) y
  have hint : Integrable (fun ω => (N t ω).re) Q := (hN.integrable t).re
  have hre : ∫ ω in A, (N t ω).re ∂Q = 0 := by
    have := integral_re (μ := Q.restrict A) (hN.integrable t).integrableOn
    simp only [RCLike.re_to_complex] at this
    rw [this, hNt, Complex.zero_re]
  have hz := (setIntegral_eq_zero_iff_of_nonneg_ae ((ae_restrict_iff' hA').2 hpos)
    hint.integrableOn).1 hre
  filter_upwards [(ae_restrict_iff' hA').1 hz, heq, hG.feasible] with ω hω hω' hf hωA
  have h1 : ((stoppedProcess G (gramTraceStop G L) t ω).1 y y).re ≤ 0 := by
    rw [← hω' hωA, hω hωA]
    simp
  exact (zero_of_re_diag_nonpos (hf _) h1 y).1

/-- **A column that starts at zero stays zero** (a.s. on `A ∈ 𝓖₀`, at all times). -/
theorem ae_diag_eq_zero_on (hG : IsBornGramSolution Q 𝓖 D0 D J G) {y : c}
    (hJy : ∀ t ω, (J t ω).1 y y = 0) (hJb : ∀ ω, ∃ C, ∀ t, ((J t ω).1.trace).re ≤ C)
    {A : Set Ω} (hA : MeasurableSet[𝓖 0] A) (h0 : ∀ᵐ ω ∂Q, ω ∈ A → (G 0 ω).1 y y = 0) :
    ∀ᵐ ω ∂Q, ω ∈ A → ∀ t, (G t ω).1 y y = 0 := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have : Countable S := hSc.to_subtype
  have hall : ∀ᵐ ω ∂Q, ∀ (u : S) (L : ℕ), ω ∈ A →
      (stoppedProcess G (gramTraceStop G L) u ω).1 y y = 0 := by
    rw [ae_all_iff]
    exact fun u => ae_all_iff.2 fun L => ae_stopped_diag_eq_zero hG hJy hA h0 u L
  filter_upwards [hall, hG.continuous] with ω hω hc hωA
  obtain ⟨C, hC⟩ := hJb ω
  have hcont : Continuous fun t => (G t ω - J t ω).1 y y :=
    (continuous_apply_apply y y).comp (continuous_fst.comp hc)
  have hS : ∀ u ∈ S, (G u ω - J u ω).1 y y = 0 := by
    intro u hu
    obtain ⟨L, hL⟩ := exists_le_gramTraceStop_born hc hC u
    have := hω ⟨u, hu⟩ L hωA
    rw [stoppedProcess_eq_of_le hL] at this
    simp [this, hJy]
  intro t
  have hext := Continuous.ext_on hSd hcont continuous_const hS
  have := congrFun hext t
  simpa [hJy] using this

end BlockBand.SourceProcess.CapLimit
