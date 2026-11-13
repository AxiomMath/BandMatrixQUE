module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.FixSymm
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.MultiIsometry
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.HorizonRestrict
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The trace bracket measure of a vector integrator

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖`, finite `ι`,
`h : IsL2IntegratorVec Q 𝓖 N a` (`MultiBracket`), horizon `T`;
`timeProbMeasure T Q = dt|_{(0,T]} ⊗ Q`.

* `bracketMeasure_mono_density`: `α ≤ α'` pointwise implies `ν_T(α) ≤ ν_T(α')`.
* `traceA a = ∑_i a^{ii}` and `barMeasure Q a T = ν_T(traceA a)`, the integrand measure
  `ν̄ = (∑_i a^{ii}) ds ⊗ Q` of the vector integral; `barMeasure_eq_sum`: `ν̄ = ∑_i ν^{ii}`;
  `isFiniteMeasure_bar`; `coord_le_bar`: `ν^{ii} ≤ ν̄`.
* For **symmetric** `a` (`hs`; WLOG by `IsL2IntegratorVec.symmetrize`): `abs_le_trace`
  (`|a^{ij}| ≤ tr a`), the ratio `crossRatio a i j = a^{ij} / tr a` with `|ρ^{ij}| ≤ 1` and
  `tr a · ρ^{ij} = a^{ij}` everywhere, and `integral_bar_crossRatio`: for `F ∈ L¹(ν̄)`,
  `∫ ρ^{ij} F dν̄ = ∫ F a^{ij} d(dt ⊗ Q)` with `F a^{ij} ∈ L¹(dt ⊗ Q)`.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {ι : Type*} [Fintype ι]

/-- **Monotonicity of the bracket measure in the density.** -/
theorem bracketMeasure_mono_density (Q : Measure Ω) (T : ℝ≥0) {α α' : ℝ≥0 → Ω → ℝ}
    (hαα : ∀ t ω, α t ω ≤ α' t ω) : bracketMeasure Q α T ≤ bracketMeasure Q α' T :=
  withDensity_mono (Eventually.of_forall fun _ => ENNReal.ofReal_le_ofReal (hαα _ _))

omit mΩ in
/-- The trace density `∑_i a^{ii}`. -/
def traceA (a : ι → ι → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := ∑ i, a i i t ω

/-- The integrand measure `ν̄ = (tr a) ds ⊗ Q` of the vector integral. -/
def barMeasure (Q : Measure Ω) (a : ι → ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : Measure (ℝ × Ω) :=
  bracketMeasure Q (traceA a) T

omit mΩ in
/-- The cross ratio `a^{ij} / tr a` (`0` where `tr a = 0`). -/
def crossRatio (a : ι → ι → ℝ≥0 → Ω → ℝ) (i j : ι) (t : ℝ≥0) (ω : Ω) : ℝ :=
  a i j t ω / traceA a t ω

namespace IsL2IntegratorVec

variable {N : ι → ℝ≥0 → Ω → ℝ} {a : ι → ι → ℝ≥0 → Ω → ℝ} (h : IsL2IntegratorVec Q 𝓖 N a)
include h

theorem diag_nonneg (i : ι) (t : ℝ≥0) (ω : Ω) : 0 ≤ a i i t ω :=
  psd_diag_nonneg (h.psd t ω) i

theorem trace_nonneg (t : ℝ≥0) (ω : Ω) : 0 ≤ traceA a t ω :=
  Finset.sum_nonneg fun i _ => h.diag_nonneg i t ω

theorem diag_le_trace (i : ι) (t : ℝ≥0) (ω : Ω) : a i i t ω ≤ traceA a t ω :=
  Finset.single_le_sum (f := fun k => a k k t ω) (fun k _ => h.diag_nonneg k t ω)
    (Finset.mem_univ i)

theorem measurable_trace : Measurable fun p : ℝ × Ω => traceA a p.1.toNNReal p.2 := by
  simp only [traceA]
  exact Finset.measurable_sum _ fun i _ => h.measurable i i

theorem coord_le_bar (T : ℝ≥0) (i : ι) : bracketMeasure Q (a i i) T ≤ barMeasure Q a T :=
  bracketMeasure_mono_density Q T (h.diag_le_trace i)

theorem barMeasure_apply (T : ℝ≥0) {s : Set (ℝ × Ω)} (hs : MeasurableSet s) :
    barMeasure Q a T s = ∑ i, bracketMeasure Q (a i i) T s := by
  simp only [barMeasure, bracketMeasure, withDensity_apply _ hs, traceA]
  rw [← lintegral_finsetSum (f := fun i (p : ℝ × Ω) => ENNReal.ofReal (a i i p.1.toNNReal p.2))
    _ fun i _ => ENNReal.measurable_ofReal.comp (h.measurable i i)]
  exact lintegral_congr fun p => ENNReal.ofReal_sum_of_nonneg fun i _ => h.diag_nonneg i _ _

/-- `ν̄ = ∑_i ν^{ii}`. -/
theorem barMeasure_eq_sum (T : ℝ≥0) : barMeasure Q a T = ∑ i, bracketMeasure Q (a i i) T :=
  Measure.ext fun s hs => by rw [h.barMeasure_apply T hs, Measure.coe_finsetSum,
    Finset.sum_apply]

theorem isFiniteMeasure_bar [IsFiniteMeasure Q] (T : ℝ≥0) : IsFiniteMeasure (barMeasure Q a T) :=
  ⟨by
    rw [h.barMeasure_apply T MeasurableSet.univ]
    exact ENNReal.sum_lt_top.2 fun i _ =>
      haveI := (h.coord i).isFiniteMeasure_bracketMeasure T
      measure_lt_top _ _⟩

theorem measurable_crossRatio (i j : ι) :
    Measurable fun p : ℝ × Ω => crossRatio a i j p.1.toNNReal p.2 :=
  (h.measurable i j).div h.measurable_trace

variable (hs : ∀ i j t ω, a i j t ω = a j i t ω)
include hs

theorem abs_le_trace (i j : ι) (t : ℝ≥0) (ω : Ω) : |a i j t ω| ≤ traceA a t ω :=
  abs_le_trace_of_psd_symm (h.psd t ω) (fun i j => hs i j t ω) i j

theorem abs_crossRatio_le (i j : ι) (t : ℝ≥0) (ω : Ω) : |crossRatio a i j t ω| ≤ 1 := by
  rcases (h.trace_nonneg t ω).eq_or_lt with h0 | hpos
  · simp [crossRatio, ← h0]
  · rw [crossRatio, abs_div, abs_of_pos hpos, div_le_one hpos]
    exact h.abs_le_trace hs i j t ω

theorem trace_mul_crossRatio (i j : ι) (t : ℝ≥0) (ω : Ω) :
    traceA a t ω * crossRatio a i j t ω = a i j t ω := by
  rcases (h.trace_nonneg t ω).eq_or_lt with h0 | hpos
  · have := h.abs_le_trace hs i j t ω
    rw [← h0] at this
    have ha : a i j t ω = 0 := abs_nonpos_iff.1 this
    rw [ha, ← h0, zero_mul]
  · rw [crossRatio, mul_div_cancel₀ _ hpos.ne']

/-- **From `ν̄` to `dt ⊗ Q`**: `∫ ρ^{ij} F dν̄ = ∫ F a^{ij} d(dt ⊗ Q)` for `F ∈ L¹(ν̄)`. -/
theorem integral_bar_crossRatio (T : ℝ≥0) (i j : ι) {F : ℝ × Ω → ℝ}
    (hF : Integrable F (barMeasure Q a T)) :
    Integrable (fun p => F p * a i j p.1.toNNReal p.2) (timeProbMeasure T Q) ∧
    ∫ p, crossRatio a i j p.1.toNNReal p.2 * F p ∂barMeasure Q a T =
      ∫ p, F p * a i j p.1.toNNReal p.2 ∂timeProbMeasure T Q := by
  have hm : Measurable fun p : ℝ × Ω => ENNReal.ofReal (traceA a p.1.toNNReal p.2) :=
    ENNReal.measurable_ofReal.comp h.measurable_trace
  have hlt : ∀ᵐ p ∂timeProbMeasure T Q, ENNReal.ofReal (traceA a p.1.toNNReal p.2) < ∞ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hpt (p : ℝ × Ω) : (ENNReal.ofReal (traceA a p.1.toNNReal p.2)).toReal •
      (crossRatio a i j p.1.toNNReal p.2 * F p) = F p * a i j p.1.toNNReal p.2 := by
    rw [ENNReal.toReal_ofReal (h.trace_nonneg _ _), smul_eq_mul, ← mul_assoc,
      h.trace_mul_crossRatio hs, mul_comm]
  have hρF : Integrable (fun p => crossRatio a i j p.1.toNNReal p.2 * F p)
      (barMeasure Q a T) :=
    hF.bdd_mul (c := 1) (h.measurable_crossRatio i j).aestronglyMeasurable
      (Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]; exact h.abs_crossRatio_le hs i j _ _)
  refine ⟨?_, ?_⟩
  · have := (integrable_withDensity_iff_integrable_smul' hm hlt).1 hρF
    simpa only [hpt] using this
  · rw [barMeasure, bracketMeasure, integral_withDensity_eq_integral_toReal_smul hm hlt]
    simp only [hpt]

end IsL2IntegratorVec

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
