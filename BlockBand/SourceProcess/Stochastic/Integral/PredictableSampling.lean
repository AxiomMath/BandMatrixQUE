module
public import BlockBand.SourceProcess.Stochastic.Integral.PredictableRaw
public import BlockBand.SourceProcess.Stochastic.Integral.Dyadic
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Left-endpoint dyadic sampling

On `ℝ × DriverSample S κ` with `ν = timeProbMeasure T (driverLaw μ)` (`dt ⊗ P` on `(0,T]`).
For a family `V : ℝ≥0 → Ω → ℝ` with `V_t` measurable for the augmented `F_t ∨ N`, the
left-endpoint sampling `leftSample n V (s,x) = V_{k 2^{-n}}(x)` for `s ∈ (k 2^{-n}, (k+1) 2^{-n}]`
(and `0` for `s ≤ 0`) is measurable for the augmented predictable σ-algebra
(`stronglyMeasurable_leftSample`).

`aestronglyMeasurable_of_leftLimit`: if for `ν`-a.e. `p = (s,x)` the values `V_{u_n}(x)` converge
to `G p` along every sequence `u_n < s` with `u_n → s`, then `G` is a.e. raw predictable on `ν`.
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open PredictableRectangle

/-- The dyadic left endpoint `(⌈s 2^n⌉ − 1) 2^{-n}` of the dyadic interval containing `s > 0`. -/
def leftPoint (n : ℕ) (s : ℝ) : ℝ≥0 :=
  ((⌈s / (dyadicStep n : ℝ)⌉₊ - 1 : ℕ) : ℝ≥0) * dyadicStep n

theorem dyadicStep_coe_pos (n : ℕ) : 0 < (dyadicStep n : ℝ) :=
  NNReal.coe_pos.2 (dyadicStep_pos n)

/-- For `s > 0`, `s ∈ (k h, (k+1) h]` iff `k = ⌈s/h⌉ − 1` (`h = 2^{-n}`). -/
theorem mem_Ioc_iff_eq_ceil (n k : ℕ) {s : ℝ} (hs : 0 < s) :
    s ∈ Set.Ioc (((k : ℝ≥0) * dyadicStep n : ℝ≥0) : ℝ) ((((k + 1 : ℕ) : ℝ≥0) * dyadicStep n : ℝ≥0) : ℝ) ↔
      k = ⌈s / (dyadicStep n : ℝ)⌉₊ - 1 := by
  have hh := dyadicStep_coe_pos n
  have hc : 0 < ⌈s / (dyadicStep n : ℝ)⌉₊ := Nat.ceil_pos.2 (div_pos hs hh)
  have h1 : k = ⌈s / (dyadicStep n : ℝ)⌉₊ - 1 ↔ ⌈s / (dyadicStep n : ℝ)⌉₊ = k + 1 := by omega
  rw [h1, Nat.ceil_eq_iff (Nat.add_one_ne_zero k), Nat.add_sub_cancel, Set.mem_Ioc,
    lt_div_iff₀ hh, div_le_iff₀ hh]
  push_cast
  rfl

theorem leftPoint_lt (n : ℕ) {s : ℝ} (hs : 0 < s) : (leftPoint n s : ℝ) < s := by
  have h := (mem_Ioc_iff_eq_ceil n _ hs).2 rfl
  exact h.1

theorem le_leftPoint_add (n : ℕ) {s : ℝ} (hs : 0 < s) :
    s ≤ (leftPoint n s : ℝ) + (dyadicStep n : ℝ) := by
  have h := ((mem_Ioc_iff_eq_ceil n _ hs).2 rfl).2
  unfold leftPoint
  push_cast at h ⊢
  linarith

theorem tendsto_leftPoint {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n => (leftPoint n s : ℝ)) atTop (𝓝 s) := by
  have hstep : Tendsto (fun n => (dyadicStep n : ℝ)) atTop (𝓝 0) := by
    have h := NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ≥0))
      (by rw [inv_lt_one₀ two_pos]; exact one_lt_two)
    have h' := (NNReal.continuous_coe.tendsto 0).comp h
    simpa only [dyadicStep, Function.comp_def, NNReal.coe_zero] using h'
  have hlow : Tendsto (fun n => s - (dyadicStep n : ℝ)) atTop (𝓝 s) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hstep
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => by linarith [le_leftPoint_add n hs]) (fun n => (leftPoint_lt n hs).le)

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ]

/-- Left-endpoint dyadic sampling of `V` at mesh `2^{-n}`. -/
def leftSample (n : ℕ) (V : ℝ≥0 → DriverSample S κ → ℝ) (p : ℝ × DriverSample S κ) : ℝ :=
  if 0 < p.1 then V (leftPoint n p.1) p.2 else 0

omit [MeasurableSpace S] [Fintype κ] in
theorem coefficientRectangle_dyadic (n k : ℕ) (V : ℝ≥0 → DriverSample S κ → ℝ)
    (p : ℝ × DriverSample S κ) :
    coefficientRectangle ((k : ℝ≥0) * dyadicStep n) (((k + 1 : ℕ) : ℝ≥0) * dyadicStep n)
      (V ((k : ℝ≥0) * dyadicStep n)) p =
      if 0 < p.1 then (if k = ⌈p.1 / (dyadicStep n : ℝ)⌉₊ - 1 then
        V (leftPoint n p.1) p.2 else 0) else 0 := by
  classical
  unfold coefficientRectangle
  by_cases hp : 0 < p.1
  · rw [ite_eq_left hp]
    by_cases hk : k = ⌈p.1 / (dyadicStep n : ℝ)⌉₊ - 1
    · have hmem := (mem_Ioc_iff_eq_ceil n k hp).2 hk
      rw [Set.indicator_of_mem (Set.mk_mem_prod hmem (Set.mem_univ p.2)), ite_eq_left hk, leftPoint, ← hk]
    · rw [ite_eq_right hk, Set.indicator_of_notMem]
      exact fun h => hk ((mem_Ioc_iff_eq_ceil n k hp).1 (Set.mem_prod.1 h).1)
  · rw [ite_eq_right hp, Set.indicator_of_notMem]
    intro h
    have h1 := (Set.mem_prod.1 h).1.1
    have h2 : (0 : ℝ) ≤ (((k : ℝ≥0) * dyadicStep n : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    exact hp (h2.trans_lt h1)

omit [IsProbabilityMeasure μ] in
/-- The left-endpoint sampling of an augmented-adapted family is augmented predictable. -/
theorem stronglyMeasurable_leftSample (n : ℕ) {V : ℝ≥0 → DriverSample S κ → ℝ}
    (hV : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (V t)) :
    StronglyMeasurable[augPredictable (κ := κ) μ] (leftSample n V) := by
  classical
  let R : ℕ → ℝ × DriverSample S κ → ℝ := fun k =>
    coefficientRectangle ((k : ℝ≥0) * dyadicStep n) (((k + 1 : ℕ) : ℝ≥0) * dyadicStep n)
      (V ((k : ℝ≥0) * dyadicStep n))
  have hR (k : ℕ) : StronglyMeasurable[augPredictable (κ := κ) μ] (R k) :=
    stronglyMeasurable_coefficientRectangle (augmentedContinuousFiltration (κ := κ) μ)
      (hV _).measurable
  have hS (m : ℕ) : StronglyMeasurable[augPredictable (κ := κ) μ] (∑ k ∈ Finset.range m, R k) :=
    Finset.sum_induction _ (fun f => StronglyMeasurable[augPredictable (κ := κ) μ] f)
      (fun _ _ ha hb => ha.add hb) stronglyMeasurable_const (fun k _ => hR k)
  refine @stronglyMeasurable_of_tendsto _ _ _ (augPredictable (κ := κ) μ) _ _ atTop _ _ _ _ hS ?_
  rw [tendsto_pi_nhds]
  intro p
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (⌈p.1 / (dyadicStep n : ℝ)⌉₊ - 1)] with m hm
  rw [Finset.sum_apply]
  simp only [R, coefficientRectangle_dyadic, leftSample]
  by_cases hp : 0 < p.1
  · simp only [ite_eq_left hp]
    rw [Finset.sum_ite_eq' (Finset.range m), ite_eq_left (Finset.mem_range.2 hm)]
  · simp only [ite_eq_right hp, Finset.sum_const_zero]

/-- **Left-limit criterion for raw predictability.** If `V_t` is `F_t ∨ N`-measurable and, for
`ν`-a.e. `p = (s,x)`, `V_{u_n}(x) → G p` along every sequence `u_n < s`, `u_n → s`, then `G` is
a.e. raw predictable for `ν = timeProbMeasure T (driverLaw μ)`. -/
theorem aestronglyMeasurable_of_leftLimit {T : ℝ≥0} {V : ℝ≥0 → DriverSample S κ → ℝ}
    (hV : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (V t))
    {G : ℝ × DriverSample S κ → ℝ}
    (hG : ∀ᵐ p ∂timeProbMeasure T (driverLaw (κ := κ) μ), ∀ u : ℕ → ℝ≥0,
      (∀ n, (u n : ℝ) < p.1) → Tendsto (fun n => (u n : ℝ)) atTop (𝓝 p.1) →
        Tendsto (fun n => V (u n) p.2) atTop (𝓝 (G p))) :
    AEStronglyMeasurable[rawPredictable S κ] G (timeProbMeasure T (driverLaw (κ := κ) μ)) := by
  refine aestronglyMeasurable_sub_of_tendsto_ae (f := fun n => leftSample n V)
    (fun n => aestronglyMeasurable_rawPredictable_of_augmented μ
      (stronglyMeasurable_leftSample μ n hV).aestronglyMeasurable) ?_
  filter_upwards [hG, timeProbMeasure_horizon (κ := κ) μ T] with p hp hpos
  have hs : 0 < p.1 := hpos.1
  have h := hp (fun n => leftPoint n p.1) (fun n => leftPoint_lt n hs) (tendsto_leftPoint hs)
  simpa only [leftSample, ite_eq_left hs] using h

end BlockBand.SourceProcess.Stochastic.Integral
