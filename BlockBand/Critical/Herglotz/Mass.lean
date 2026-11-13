module

public import BlockBand.Critical.Herglotz.Near

/-!
# Total pole mass `tr Im F(i)` and residue tightness

For an atomic Herglotz function `F`, `poleMass F = Σ_x tr μ({x})/(1 + x²) = tr Im F(i)` controls
every residue. Under the second hypothesis of the Herglotz tail lemma
(`E tr Im F_N(i) → r`), Markov's inequality gives residue tightness:
`P_N(poleMass(F_N) ≥ t) ≤ (r + 1)/t` eventually.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped Matrix NNReal ENNReal ComplexOrder

namespace BlockBand.Critical.Herglotz

open CoareaNative.BlockBand (matrixImaginaryPart)

variable {r : ℕ}

/-- `Σ_x tr μ({x}) / (1 + x²)`, the total pole mass seen from `i`. -/
def poleMass (F : AtomicHerglotz r) : ℝ :=
  ∑ x ∈ F.residue.support, (Matrix.trace (F.residue x)).re / (1 + x ^ 2)

theorem trace_re_nonneg {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.PosSemidef) :
    0 ≤ (Matrix.trace A).re := by
  rw [Matrix.trace, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => re_diag_nonneg hA i

theorem poleMass_nonneg (F : AtomicHerglotz r) : 0 ≤ poleMass F :=
  Finset.sum_nonneg fun x _ => div_nonneg (trace_re_nonneg (F.residue_posSemidef x))
    (by positivity)

theorem le_poleMass_of_mem (F : AtomicHerglotz r) {x : ℝ} (hx : x ∈ F.residue.support) :
    (Matrix.trace (F.residue x)).re / (1 + x ^ 2) ≤ poleMass F :=
  Finset.single_le_sum (f := fun x => (Matrix.trace (F.residue x)).re / (1 + x ^ 2))
    (fun y _ => div_nonneg (trace_re_nonneg (F.residue_posSemidef y)) (by positivity)) hx

/-- Every residue is controlled by the pole mass. -/
theorem matNorm_residue_le (F : AtomicHerglotz r) {x : ℝ} (hx : x ∈ F.residue.support) :
    matNorm (F.residue x) ≤ (r + 1) * (1 + x ^ 2) * poleMass F := by
  have h1 := PosSemidef.matNorm_le_trace (F.residue_posSemidef x)
  have h2 := le_poleMass_of_mem F hx
  have ht := trace_re_nonneg (F.residue_posSemidef x)
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  rw [div_le_iff₀ hpos] at h2
  have hS := poleMass_nonneg F
  calc matNorm (F.residue x) ≤ r * (Matrix.trace (F.residue x)).re := h1
    _ ≤ (r + 1) * (Matrix.trace (F.residue x)).re := by nlinarith
    _ ≤ (r + 1) * (poleMass F * (1 + x ^ 2)) := by gcongr
    _ = (r + 1) * (1 + x ^ 2) * poleMass F := by ring

/-- `poleMass F = tr Im F(i)` (real part of the trace of the matrix imaginary part). -/
theorem poleMass_eq (F : AtomicHerglotz r) :
    poleMass F = ∑ i, (matrixImaginaryPart (F.eval Complex.I) i i).re := by
  rw [AtomicHerglotz.matrixImaginaryPart_eval]
  unfold poleMass Finsupp.sum
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Complex.re_sum,
    Complex.re_ofReal_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum, Matrix.trace, Complex.re_sum, div_eq_inv_mul]
  congr 1
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero, Complex.sub_im,
    Complex.ofReal_im, Complex.I_im, zero_sub, mul_neg, neg_neg, mul_one, one_div]
  congr 1
  ring

theorem measurable_matrixImaginaryPart_apply {Ω : Type*} [MeasurableSpace Ω]
    {A : Ω → Matrix (Fin r) (Fin r) ℂ} (hA : ∀ i j, Measurable fun ω => A ω i j) (i j : Fin r) :
    Measurable fun ω => matrixImaginaryPart (A ω) i j := by
  unfold matrixImaginaryPart
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, smul_eq_mul]
  exact measurable_const.mul ((hA i j).sub (Complex.continuous_conj.measurable.comp (hA j i)))

theorem measurable_eval_at {Ω : Type*} [MeasurableSpace Ω] {F : Ω → AtomicHerglotz r}
    (hmeas : ∀ i j : Fin r, Measurable fun p : Ω × ℂ => (F p.1).eval p.2 i j) (z : ℂ)
    (i j : Fin r) : Measurable fun ω => (F ω).eval z i j :=
  (hmeas i j).comp (measurable_id.prodMk measurable_const)

theorem measurable_poleMass {Ω : Type*} [MeasurableSpace Ω] {F : Ω → AtomicHerglotz r}
    (hmeas : ∀ i j : Fin r, Measurable fun p : Ω × ℂ => (F p.1).eval p.2 i j) :
    Measurable fun ω => poleMass (F ω) := by
  simp_rw [poleMass_eq]
  exact Finset.measurable_sum _ fun i _ => Complex.measurable_re.comp
    (measurable_matrixImaginaryPart_apply (fun i j => measurable_eval_at hmeas _ i j) i i)

section Hyp

variable {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] {P : ∀ N, Measure (Ω N)}
  [∀ N, IsProbabilityMeasure (P N)] {F : ∀ N, Ω N → AtomicHerglotz r} {Ω' : Type*}
  [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))}

/-- Under hypothesis 2 the diagonal of `Im F_N(i)` is eventually integrable and
`E poleMass(F_N)` is eventually the sum of the real parts of the diagonal means. -/
theorem HerglotzTailHypotheses.eventually_integrable_poleMass
    (h : HerglotzTailHypotheses r P F P' Ξ) :
    ∀ᶠ N in atTop, Integrable (fun ω => poleMass (F N ω)) (P N) ∧
      ∫ ω, poleMass (F N ω) ∂P N =
        ∑ i, (∫ ω, matrixImaginaryPart ((F N ω).eval Complex.I) i i ∂P N).re := by
  have hmean : ∀ i : Fin r, Tendsto
      (fun N => ∫ ω, matrixImaginaryPart ((F N ω).eval Complex.I) i i ∂P N) atTop (𝓝 1) := by
    intro i
    have := h.mean 1 one_pos i i
    simpa using this
  have hint : ∀ i : Fin r, ∀ᶠ N in atTop,
      Integrable (fun ω => matrixImaginaryPart ((F N ω).eval Complex.I) i i) (P N) := by
    intro i
    filter_upwards [(hmean i).eventually_ne one_ne_zero] with N hN
    by_contra hni
    exact hN (integral_undef hni)
  filter_upwards [(Filter.eventually_all.2 hint)] with N hN
  have hre : ∀ i, Integrable (fun ω => (matrixImaginaryPart ((F N ω).eval Complex.I) i i).re)
      (P N) := fun i => (hN i).re
  have heq : (fun ω => poleMass (F N ω)) =
      fun ω => ∑ i, (matrixImaginaryPart ((F N ω).eval Complex.I) i i).re :=
    funext fun ω => poleMass_eq _
  refine ⟨?_, ?_⟩
  · rw [heq]; exact integrable_finsetSum _ fun i _ => hre i
  · rw [heq, integral_finsetSum _ fun i _ => hre i]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := integral_re (hN i)
    simpa using this

/-- **Hypothesis 2 at `Y = 1`**: `E poleMass(F_N) = E tr Im F_N(i) → r`. -/
theorem HerglotzTailHypotheses.tendsto_integral_poleMass
    (h : HerglotzTailHypotheses r P F P' Ξ) :
    Tendsto (fun N => ∫ ω, poleMass (F N ω) ∂P N) atTop (𝓝 (r : ℝ)) := by
  have hmean : ∀ i : Fin r, Tendsto
      (fun N => (∫ ω, matrixImaginaryPart ((F N ω).eval Complex.I) i i ∂P N).re) atTop
        (𝓝 1) := by
    intro i
    have h1 := h.mean 1 one_pos i i
    simp only [Complex.ofReal_one, one_mul, Matrix.one_apply_eq] at h1
    have := (Complex.continuous_re.tendsto _).comp h1
    simp only [Complex.one_re] at this
    exact this
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin r)) fun i _ => hmean i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    at hsum
  refine hsum.congr' ?_
  filter_upwards [h.eventually_integrable_poleMass] with N hN
  exact hN.2.symm

/-- **Residue tightness (Markov under hypothesis 2).** For `t > 0`, eventually in `N`,
`P_N(poleMass(F_N) ≥ t) ≤ (r + 1)/t`. -/
theorem HerglotzTailHypotheses.eventually_measure_poleMass_ge_le
    (h : HerglotzTailHypotheses r P F P' Ξ) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ N in atTop, P N {ω | t ≤ poleMass (F N ω)} ≤ ENNReal.ofReal ((r + 1) / t) := by
  filter_upwards [h.eventually_integrable_poleMass,
    h.tendsto_integral_poleMass.eventually (ge_mem_nhds (lt_add_one (r : ℝ)))] with N hN hle
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω => poleMass_nonneg (F N ω)) hN.1 t
  have hreal : (P N).real {ω | t ≤ poleMass (F N ω)} ≤ (r + 1) / t := by
    rw [le_div_iff₀ ht]; linarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top (P N) _)]
  exact ENNReal.ofReal_le_ofReal hreal

end Hyp

end BlockBand.Critical.Herglotz
