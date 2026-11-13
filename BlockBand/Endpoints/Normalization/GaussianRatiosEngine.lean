module

public import BlockBand.Endpoints.Normalization.GaussianRatiosDeterminacy

/-!
# Uniform weak comparison from uniform mixed-moment comparison

This is the uniformity argument of the Gaussian-ratios theorem: if a sequence violated the
conclusion, weakly convergent subsequences of both joint vectors would have identical moments, and
factorial moment bounds determine their joint laws. The argument is purely measure-theoretic.

**Statement** (`weak_comparison_of_moments`). Let `ι` be finite and `(μ_a, ν_a)` a family of
pairs of probability measures on `ℝ^ι`, indexed by an arbitrary type with a size `n(a) ∈ ℕ`,
both carried by the closed orthant, with integrable mixed moments. Assume
(i) uniform mixed-moment comparison: for every multi-index `f : Fin r → ι` and `η > 0` there is
`n₀` with `|∫ Π_m x_{f m} dμ_a - ∫ Π_m x_{f m} dν_a| ≤ η` whenever `n(a) ≥ n₀`;
(ii) factorial bounds for the comparison laws: `∫ (Σ_i x_i)^m dν_a ≤ m! R^m` for all `a, m`.
Then for every bounded continuous `h` and `ε > 0` there is `n₀` with
`|∫ h dμ_a - ∫ h dν_a| ≤ ε` whenever `n(a) ≥ n₀`.

Proof: by contradiction; Prokhorov (tightness from first moments); convergence of moments along
the subsequence from second-moment bounds (`tendsto_integral_of_sq_bound`); exponential moments
of the limits (`lintegral_exp_le_of_moments`); `eq_of_mixed_moments`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

variable {ι : Type*} [Fintype ι]

/-!
## Exponential moments from factorial moment bounds
-/

theorem measurable_absSum : Measurable (absSum (ι := ι)) := continuous_absSum.measurable

theorem measurable_ofReal_absSum_pow (m : ℕ) :
    Measurable fun x : ι → ℝ => ENNReal.ofReal (absSum x ^ m) :=
  ENNReal.measurable_ofReal.comp (measurable_absSum.pow_const m)

theorem lintegral_exp_le_of_moments {μ : Measure (ι → ℝ)} {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (h : ∀ m : ℕ, ∫⁻ x, ENNReal.ofReal (absSum x ^ m) ∂μ ≤
      ENNReal.ofReal (C * m.factorial * (R + 1) ^ m)) :
    ∫⁻ x, ENNReal.ofReal (Real.exp ((2 * (R + 1))⁻¹ * absSum x)) ∂μ ≤ ENNReal.ofReal (2 * C) := by
  set s : ℝ := (2 * (R + 1))⁻¹ with hs
  have hs0 : 0 < s := by positivity
  have hser : ∀ x : ι → ℝ, ENNReal.ofReal (Real.exp (s * absSum x)) =
      ∑' m : ℕ, ENNReal.ofReal (s ^ m / m.factorial) * ENNReal.ofReal (absSum x ^ m) := by
    intro x
    have hy : 0 ≤ s * absSum x := mul_nonneg hs0.le (absSum_nonneg x)
    have hsum := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (s * absSum x)
    rw [← Real.exp_eq_exp_ℝ] at hsum
    rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum.summable]
    refine tsum_congr fun m => ?_
    rw [← ENNReal.ofReal_mul (by positivity), mul_pow]
    congr 1; ring
  simp_rw [hser]
  rw [lintegral_tsum (f := fun (m : ℕ) (x : ι → ℝ) =>
    ENNReal.ofReal (s ^ m / m.factorial) * ENNReal.ofReal (absSum x ^ m))
    fun m => ((measurable_ofReal_absSum_pow m).const_mul _).aemeasurable]
  calc ∑' m : ℕ, ∫⁻ x, ENNReal.ofReal (s ^ m / m.factorial) * ENNReal.ofReal (absSum x ^ m) ∂μ
      ≤ ∑' m : ℕ, ENNReal.ofReal C * (2⁻¹ : ℝ≥0∞) ^ m := by
        refine ENNReal.tsum_le_tsum fun m => ?_
        rw [lintegral_const_mul _ (measurable_ofReal_absSum_pow m)]
        refine (mul_le_mul_of_nonneg_left (h m) zero_le).trans (le_of_eq ?_)
        have h2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (2⁻¹) := by
          rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
        rw [← ENNReal.ofReal_mul (by positivity), h2, ← ENNReal.ofReal_pow (by norm_num),
          ← ENNReal.ofReal_mul hC]
        congr 1
        have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
        have hR1 : R + 1 ≠ 0 := by linarith
        have hsR : s * (R + 1) = 2⁻¹ := by rw [hs]; field_simp
        calc s ^ m / m.factorial * (C * m.factorial * (R + 1) ^ m) = C * (s * (R + 1)) ^ m := by
              rw [mul_pow]; field_simp
          _ = C * 2⁻¹ ^ m := by rw [hsR]
    _ = ENNReal.ofReal (2 * C) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two, ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_ofNat, mul_comm]

/-!
## Prokhorov extraction on `ℝ^ι`
-/

/-- A probability measure as a point of `ProbabilityMeasure`. -/
def toPM (ρ : Measure (ι → ℝ)) [h : IsProbabilityMeasure ρ] : ProbabilityMeasure (ι → ℝ) :=
  ⟨ρ, h⟩

omit [Fintype ι] in
@[simp] theorem coe_toPM (ρ : Measure (ι → ℝ)) [IsProbabilityMeasure ρ] :
    ((toPM ρ : ProbabilityMeasure (ι → ℝ)) : Measure (ι → ℝ)) = ρ := rfl

theorem norm_le_absSum (x : ι → ℝ) : ‖x‖ ≤ absSum x := by
  refine (pi_norm_le_iff_of_nonneg (absSum_nonneg x)).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)

theorem exists_tendsto_subseq_of_lintegral_absSum_le (μs : ℕ → Measure (ι → ℝ))
    [∀ j, IsProbabilityMeasure (μs j)] {B : ℝ}
    (hB : ∀ j, ∫⁻ x, ENNReal.ofReal (absSum x) ∂μs j ≤ ENNReal.ofReal B) :
    ∃ μ : ProbabilityMeasure (ι → ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => toPM (μs (φ j))) atTop (𝓝 μ) := by
  let P : ℕ → ProbabilityMeasure (ι → ℝ) := fun j => toPM (μs j)
  have hS : IsTightMeasureSet {((ρ : ProbabilityMeasure (ι → ℝ)) : Measure (ι → ℝ)) |
      ρ ∈ Set.range P} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    by_cases htop : ε = ⊤
    · exact ⟨∅, isCompact_empty, fun _ _ => htop ▸ le_top⟩
    have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    set K : ℝ := max B 0 / ε.toReal + 1 with hK
    have hK0 : 0 < K := by positivity
    refine ⟨Metric.closedBall 0 K, isCompact_closedBall 0 K, ?_⟩
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    have hsub : (Metric.closedBall (0 : ι → ℝ) K)ᶜ ⊆
        {x | ENNReal.ofReal K ≤ ENNReal.ofReal (absSum x)} := by
      intro x hx
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx
      exact ENNReal.ofReal_le_ofReal (hx.le.trans (norm_le_absSum x))
    refine (measure_mono hsub).trans ?_
    refine (meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp measurable_absSum).aemeasurable
      (by simp [hK0]) ENNReal.ofReal_ne_top).trans ?_
    show (∫⁻ x, ENNReal.ofReal (absSum x) ∂μs j) / ENNReal.ofReal K ≤ ε
    refine (ENNReal.div_le_div_right ((hB j).trans (ENNReal.ofReal_le_ofReal (le_max_left B 0)))
      _).trans ?_
    rw [← ENNReal.ofReal_div_of_pos hK0, ← ENNReal.ofReal_toReal htop]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hK0, hK, mul_add, mul_div_assoc', mul_comm ε.toReal (max B 0),
      mul_div_assoc, div_self hεr.ne', mul_one]
    linarith
  obtain ⟨μ, -, φ, hφ, hlim⟩ := (isCompact_closure_of_isTightMeasureSet hS).tendsto_subseq
    (fun j => subset_closure ⟨j, rfl⟩)
  exact ⟨μ, φ, hφ, hlim⟩

/-!
## Integrals of unbounded continuous functions along weakly convergent sequences
-/

/-- Lower semicontinuity of `∫ h` for continuous `h ≥ 0`. -/
theorem lintegral_le_of_tendsto {μs : ℕ → ProbabilityMeasure (ι → ℝ)}
    {μ : ProbabilityMeasure (ι → ℝ)} (hlim : Tendsto μs atTop (𝓝 μ))
    {h : (ι → ℝ) → ℝ} (hc : Continuous h) (h0 : ∀ x, 0 ≤ h x) {C : ℝ}
    (hb : ∀ᶠ j in atTop, ∫⁻ x, ENNReal.ofReal (h x) ∂(μs j : Measure (ι → ℝ)) ≤
      ENNReal.ofReal C) :
    ∫⁻ x, ENNReal.ofReal (h x) ∂(μ : Measure (ι → ℝ)) ≤ ENNReal.ofReal C := by
  set C' := max C 0 with hC'
  have hK : ∀ K : ℕ, ∫⁻ x, ENNReal.ofReal (min (h x) K) ∂(μ : Measure (ι → ℝ)) ≤
      ENNReal.ofReal C := by
    intro K
    let hK : (ι → ℝ) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => min (h x) K) (by fun_prop) K (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (h0 x) (Nat.cast_nonneg K))]
        exact min_le_right _ _)
    have hKx : ∀ x, hK x = min (h x) K := fun x => rfl
    have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) hK
    simp only [hKx] at ht
    have hle : ∀ᶠ j in atTop, ∫ x, min (h x) K ∂(μs j : Measure (ι → ℝ)) ≤ C' := by
      filter_upwards [hb] with j hj
      have hint : Integrable (fun x => min (h x) (K : ℝ)) (μs j : Measure (ι → ℝ)) :=
        hK.integrable _
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x =>
        le_min (h0 x) (Nat.cast_nonneg K)) hint.aestronglyMeasurable]
      refine ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) ?_
      refine le_trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
      exact hj.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have hlimle : ∫ x, min (h x) K ∂(μ : Measure (ι → ℝ)) ≤ C' := le_of_tendsto ht hle
    have hint : Integrable (fun x => min (h x) (K : ℝ)) (μ : Measure (ι → ℝ)) :=
      hK.integrable _
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun x => le_min (h0 x) (Nat.cast_nonneg K))]
    calc ENNReal.ofReal (∫ x, min (h x) K ∂(μ : Measure (ι → ℝ))) ≤ ENNReal.ofReal C' :=
          ENNReal.ofReal_le_ofReal hlimle
      _ = ENNReal.ofReal C := by
          rw [hC']; rcases le_total C 0 with hC | hC
          · rw [max_eq_right hC, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos hC]
          · rw [max_eq_left hC]
  have hsup : ∀ x, ENNReal.ofReal (h x) = ⨆ K : ℕ, ENNReal.ofReal (min (h x) K) := by
    intro x
    refine le_antisymm ?_ (iSup_le fun K => ENNReal.ofReal_le_ofReal (min_le_left _ _))
    obtain ⟨K, hK⟩ := exists_nat_ge (h x)
    exact le_iSup_of_le K (by rw [min_eq_left hK])
  simp_rw [hsup]
  rw [lintegral_iSup (f := fun (K : ℕ) x => ENNReal.ofReal (min (h x) K))
    (fun K => ENNReal.measurable_ofReal.comp (hc.measurable.min measurable_const))
    (fun K L hKL x =>
    ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hKL)))]
  exact iSup_le hK

theorem integrable_sq_of_lintegral {ρ : Measure (ι → ℝ)} [IsProbabilityMeasure ρ]
    {h : (ι → ℝ) → ℝ} (hc : Continuous h) {C : ℝ}
    (hb : ∫⁻ x, ENNReal.ofReal (h x ^ 2) ∂ρ ≤ ENNReal.ofReal C) :
    Integrable (fun x => h x ^ 2) ρ ∧ Integrable h ρ ∧ ∫ x, h x ^ 2 ∂ρ ≤ max C 0 := by
  have h2 : Integrable (fun x => h x ^ 2) ρ := by
    refine ⟨(hc.pow 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg (h x))]
    exact lt_of_le_of_lt hb ENNReal.ofReal_lt_top
  refine ⟨h2, ?_, ?_⟩
  · refine ((integrable_const (1 : ℝ)).add h2).mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Pi.add_apply]
    nlinarith [abs_nonneg (h x), sq_abs (h x), sq_nonneg (|h x| - 1)]
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg (h x))
      h2.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (le_max_right _ _)
      (hb.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))

/-- `|h - clamp_K h| ≤ h²/K`. -/
theorem abs_sub_clamp_le {K y : ℝ} (hK : 0 < K) :
    |y - max (-K) (min K y)| ≤ y ^ 2 / K := by
  rw [le_div_iff₀ hK]
  rcases le_total y (-K) with h1 | h1
  · rw [min_eq_right (by linarith), max_eq_left h1, abs_of_nonpos (by linarith)]
    nlinarith
  · rcases le_total y K with h2 | h2
    · rw [min_eq_right h2, max_eq_right h1, sub_self, abs_zero, zero_mul]; positivity
    · rw [min_eq_left h2, max_eq_right (by linarith), abs_of_nonneg (by linarith)]
      nlinarith

/-- Convergence of `∫ h` for continuous `h` with eventually bounded second moments. -/
theorem tendsto_integral_of_sq_bound {μs : ℕ → ProbabilityMeasure (ι → ℝ)}
    {μ : ProbabilityMeasure (ι → ℝ)} (hlim : Tendsto μs atTop (𝓝 μ))
    {h : (ι → ℝ) → ℝ} (hc : Continuous h) {C : ℝ}
    (hb : ∀ᶠ j in atTop, ∫⁻ x, ENNReal.ofReal (h x ^ 2) ∂(μs j : Measure (ι → ℝ)) ≤
      ENNReal.ofReal C) :
    Integrable h (μ : Measure (ι → ℝ)) ∧
      Tendsto (fun j => ∫ x, h x ∂(μs j : Measure (ι → ℝ))) atTop
        (𝓝 (∫ x, h x ∂(μ : Measure (ι → ℝ)))) := by
  have hbμ := lintegral_le_of_tendsto hlim (hc.pow 2) (fun x => sq_nonneg (h x)) hb
  obtain ⟨h2μ, hiμ, hCμ⟩ := integrable_sq_of_lintegral hc hbμ
  refine ⟨hiμ, ?_⟩
  set C' := max C 0
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K : ℝ := 3 * (C' + 1) / ε with hKdef
  have hK : 0 < K := by positivity
  let hK' : (ι → ℝ) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => max (-K) (min K (h x))) (by fun_prop) K (fun x => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩)
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) hK'
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨j₀, hj₀⟩ := ht (ε / 3) (by positivity)
  obtain ⟨j₁, hj₁⟩ := eventually_atTop.mp hb
  have hCK : C' / K ≤ ε / 3 := by
    rw [hKdef, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [le_max_right C 0]
  have hclose : ∀ (ρ : Measure (ι → ℝ)) [IsProbabilityMeasure ρ],
      Integrable (fun x => h x ^ 2) ρ → Integrable h ρ → ∫ x, h x ^ 2 ∂ρ ≤ C' →
      |∫ x, h x ∂ρ - ∫ x, hK' x ∂ρ| ≤ ε / 3 := by
    intro ρ _ h2 hi hC
    rw [← integral_sub hi (hK'.integrable ρ)]
    refine (abs_integral_le_integral_abs).trans ?_
    refine (integral_mono (hi.sub (hK'.integrable ρ)).abs (h2.div_const K)
      fun x => abs_sub_clamp_le hK).trans ?_
    rw [integral_div]
    exact (div_le_div_of_nonneg_right hC hK.le).trans hCK
  refine ⟨max j₀ j₁, fun j hj => ?_⟩
  obtain ⟨h2j, hij, hCj⟩ := integrable_sq_of_lintegral hc (hj₁ j (le_of_max_le_right hj))
  have e1 := hclose (μs j : Measure (ι → ℝ)) h2j hij hCj
  have e2 := hclose (μ : Measure (ι → ℝ)) h2μ hiμ hCμ
  have e3 := hj₀ j (le_of_max_le_left hj)
  rw [Real.dist_eq] at e3 ⊢
  have : ∫ x, h x ∂(μs j : Measure (ι → ℝ)) - ∫ x, h x ∂(μ : Measure (ι → ℝ)) =
      (∫ x, h x ∂(μs j : Measure (ι → ℝ)) - ∫ x, hK' x ∂(μs j : Measure (ι → ℝ))) +
      (∫ x, hK' x ∂(μs j : Measure (ι → ℝ)) - ∫ x, hK' x ∂(μ : Measure (ι → ℝ))) -
      (∫ x, h x ∂(μ : Measure (ι → ℝ)) - ∫ x, hK' x ∂(μ : Measure (ι → ℝ))) := by ring
  rw [this]
  calc _ ≤ |∫ x, h x ∂(μs j : Measure (ι → ℝ)) - ∫ x, hK' x ∂(μs j : Measure (ι → ℝ))| +
        |∫ x, hK' x ∂(μs j : Measure (ι → ℝ)) - ∫ x, hK' x ∂(μ : Measure (ι → ℝ))| +
        |∫ x, h x ∂(μ : Measure (ι → ℝ)) - ∫ x, hK' x ∂(μ : Measure (ι → ℝ))| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ < ε := by linarith

/-!
## Orthant moments
-/

theorem absSum_pow_eq_sum_monomial {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (m : ℕ) :
    absSum x ^ m = ∑ p : Fin m → ι, monomial p x := by
  have : absSum x = ∑ i, x i := Finset.sum_congr rfl fun i _ => abs_of_nonneg (hx i)
  rw [this, Fintype.sum_pow]; rfl

theorem integrable_absSum_pow_of_monomials {ρ : Measure (ι → ℝ)}
    (hpos : ∀ᵐ x ∂ρ, ∀ i, 0 ≤ x i) (hint : ∀ (r : ℕ) (f : Fin r → ι), Integrable (monomial f) ρ)
    (m : ℕ) : Integrable (fun x => absSum x ^ m) ρ :=
  (integrable_finsetSum _ fun p _ => hint m p).congr
    (hpos.mono fun _ hx => (absSum_pow_eq_sum_monomial hx m).symm)

theorem integral_absSum_pow_eq {ρ : Measure (ι → ℝ)}
    (hpos : ∀ᵐ x ∂ρ, ∀ i, 0 ≤ x i) (hint : ∀ (r : ℕ) (f : Fin r → ι), Integrable (monomial f) ρ)
    (m : ℕ) : ∫ x, absSum x ^ m ∂ρ = ∑ p : Fin m → ι, ∫ x, monomial p x ∂ρ := by
  rw [← integral_finsetSum _ fun p _ => hint m p]
  exact integral_congr_ae (hpos.mono fun x hx => absSum_pow_eq_sum_monomial hx m)

theorem exists_n0_forall {α κ : Type*} [Fintype κ] (n : α → ℕ) {Q : κ → α → Prop}
    (h : ∀ p, ∃ n₀ : ℕ, ∀ a, n₀ ≤ n a → Q p a) :
    ∃ n₀ : ℕ, ∀ a, n₀ ≤ n a → ∀ p, Q p a := by
  classical
  choose f hf using h
  exact ⟨Finset.univ.sup f, fun a ha p => hf p a ((Finset.le_sup (Finset.mem_univ p)).trans ha)⟩

/-- **Uniform weak comparison from uniform mixed-moment comparison** (the uniformity argument of
the Gaussian-ratios theorem and of the two-positive-clocks lemma). -/
theorem weak_comparison_of_moments {α : Type*} (n : α → ℕ) (μ ν : α → Measure (ι → ℝ))
    [∀ a, IsProbabilityMeasure (μ a)] [∀ a, IsProbabilityMeasure (ν a)]
    (hposμ : ∀ a, ∀ᵐ x ∂(μ a), ∀ i, 0 ≤ x i) (hposν : ∀ a, ∀ᵐ x ∂(ν a), ∀ i, 0 ≤ x i)
    (hintμ : ∀ a (r : ℕ) (f : Fin r → ι), Integrable (monomial f) (μ a))
    (hintν : ∀ a (r : ℕ) (f : Fin r → ι), Integrable (monomial f) (ν a))
    (hmom : ∀ (r : ℕ) (f : Fin r → ι) (η : ℝ), 0 < η → ∃ n₀ : ℕ, ∀ a, n₀ ≤ n a →
      |∫ x, monomial f x ∂(μ a) - ∫ x, monomial f x ∂(ν a)| ≤ η)
    (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ a (m : ℕ), ∫ x, absSum x ^ m ∂(ν a) ≤ m.factorial * R ^ m)
    (h : (ι → ℝ) →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ a, n₀ ≤ n a → |∫ x, h x ∂(μ a) - ∫ x, h x ∂(ν a)| ≤ ε := by
  classical
  -- comparison of the powers of `Σ x_i`
  have hpowcmp : ∀ (m : ℕ) (η : ℝ), 0 < η → ∃ n₀ : ℕ, ∀ a, n₀ ≤ n a →
      |∫ x, absSum x ^ m ∂(μ a) - ∫ x, absSum x ^ m ∂(ν a)| ≤ η := by
    intro m η hη
    set c : ℝ := (Fintype.card (Fin m → ι) : ℝ) + 1
    have hc : 0 < c := by positivity
    obtain ⟨n₀, hn₀⟩ := exists_n0_forall n (Q := fun (p : Fin m → ι) a =>
      |∫ x, monomial p x ∂(μ a) - ∫ x, monomial p x ∂(ν a)| ≤ η / c)
      fun p => hmom m p (η / c) (by positivity)
    refine ⟨n₀, fun a ha => ?_⟩
    rw [integral_absSum_pow_eq (hposμ a) (hintμ a), integral_absSum_pow_eq (hposν a) (hintν a),
      ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun p _ => hn₀ a ha p).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_assoc', div_le_iff₀ hc]
    nlinarith
  have hlin : ∀ (ρ : Measure (ι → ℝ)), (∀ᵐ x ∂ρ, ∀ i, 0 ≤ x i) →
      (∀ (r : ℕ) (f : Fin r → ι), Integrable (monomial f) ρ) → ∀ m : ℕ,
      ∫⁻ x, ENNReal.ofReal (absSum x ^ m) ∂ρ = ENNReal.ofReal (∫ x, absSum x ^ m ∂ρ) :=
    fun ρ hp hi m => (ofReal_integral_eq_lintegral_ofReal
      (integrable_absSum_pow_of_monomials hp hi m)
      (Eventually.of_forall fun x => pow_nonneg (absSum_nonneg x) m)).symm
  by_contra hcon
  simp only [not_exists, not_forall, not_le] at hcon
  obtain ⟨n₁, hn₁⟩ := hpowcmp 1 1 one_pos
  choose a ha hgap using fun j : ℕ => hcon (max j n₁)
  have hB1μ : ∀ j, ∫⁻ x, ENNReal.ofReal (absSum x) ∂μ (a j) ≤ ENNReal.ofReal (R + 1) := by
    intro j
    have h1 := hn₁ (a j) (le_trans (le_max_right _ _) (ha j))
    have h2 := hbound (a j) 1
    have h3 := hlin (μ (a j)) (hposμ _) (hintμ _) 1
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul] at h1 h2 h3
    rw [h3]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith [le_abs_self (∫ x, absSum x ∂μ (a j) - ∫ x, absSum x ∂ν (a j))]
  have hBν : ∀ (m : ℕ) b, ∫⁻ x, ENNReal.ofReal (absSum x ^ m) ∂ν b ≤
      ENNReal.ofReal (m.factorial * R ^ m) := fun m b => by
    rw [hlin (ν b) (hposν _) (hintν _) m]; exact ENNReal.ofReal_le_ofReal (hbound b m)
  have hB1ν : ∀ j, ∫⁻ x, ENNReal.ofReal (absSum x) ∂ν (a j) ≤ ENNReal.ofReal R := fun j => by
    have := hBν 1 (a j)
    simpa using this
  obtain ⟨μi, φ₁, hφ₁, hlim₁⟩ :=
    exists_tendsto_subseq_of_lintegral_absSum_le (fun j => μ (a j)) hB1μ
  obtain ⟨νi, φ₂, hφ₂, hlim₂⟩ :=
    exists_tendsto_subseq_of_lintegral_absSum_le (fun j => ν (a (φ₁ j))) fun j => hB1ν _
  set ψ := φ₁ ∘ φ₂ with hψdef
  have hψ : StrictMono ψ := hφ₁.comp hφ₂
  have hμlim : Tendsto (fun j => toPM (μ (a (ψ j)))) atTop (𝓝 μi) :=
    hlim₁.comp hφ₂.tendsto_atTop
  have hνlim : Tendsto (fun j => toPM (ν (a (ψ j)))) atTop (𝓝 νi) := hlim₂
  have hev : ∀ {P : α → Prop}, (∃ n₀ : ℕ, ∀ b, n₀ ≤ n b → P b) →
      ∀ᶠ j in atTop, P (a (ψ j)) := by
    rintro P ⟨n₀, hn₀⟩
    filter_upwards [eventually_ge_atTop n₀] with j hj
    exact hn₀ _ (le_trans (hj.trans (hψ.id_le j)) ((le_max_left _ _).trans (ha _)))
  have hBμ : ∀ m : ℕ, ∀ᶠ j in atTop,
      ∫⁻ x, ENNReal.ofReal (absSum x ^ m) ∂(toPM (μ (a (ψ j))) : Measure (ι → ℝ)) ≤
        ENNReal.ofReal (m.factorial * R ^ m + 1) := by
    intro m
    filter_upwards [hev (hpowcmp m 1 one_pos)] with j hj
    rw [coe_toPM, hlin _ (hposμ _) (hintμ _) m]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith [hbound (a (ψ j)) m, le_abs_self (∫ x, absSum x ^ m ∂μ (a (ψ j)) -
      ∫ x, absSum x ^ m ∂ν (a (ψ j)))]
  have hBν' : ∀ m : ℕ, ∀ᶠ j in atTop,
      ∫⁻ x, ENNReal.ofReal (absSum x ^ m) ∂(toPM (ν (a (ψ j))) : Measure (ι → ℝ)) ≤
        ENNReal.ofReal (m.factorial * R ^ m + 1) := fun m =>
    Eventually.of_forall fun j => by
      rw [coe_toPM]
      exact (hBν m _).trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hsq : ∀ {r : ℕ} (f : Fin r → ι) (x : ι → ℝ), monomial f x ^ 2 ≤ absSum x ^ (2 * r) := by
    intro r f x
    rw [mul_comm, pow_mul, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_monomial_le f x) 2
  have hmon : ∀ (σs : ℕ → ProbabilityMeasure (ι → ℝ)) (σ : ProbabilityMeasure (ι → ℝ)),
      Tendsto σs atTop (𝓝 σ) → (∀ m : ℕ, ∀ᶠ j in atTop,
        ∫⁻ x, ENNReal.ofReal (absSum x ^ m) ∂(σs j : Measure (ι → ℝ)) ≤
          ENNReal.ofReal (m.factorial * R ^ m + 1)) → ∀ (r : ℕ) (f : Fin r → ι),
      Integrable (monomial f) (σ : Measure (ι → ℝ)) ∧
        Tendsto (fun j => ∫ x, monomial f x ∂(σs j : Measure (ι → ℝ))) atTop
          (𝓝 (∫ x, monomial f x ∂(σ : Measure (ι → ℝ)))) := by
    intro σs σ hl hB r f
    refine tendsto_integral_of_sq_bound hl (continuous_monomial f)
      (C := (2 * r).factorial * R ^ (2 * r) + 1) ?_
    filter_upwards [hB (2 * r)] with j hj
    exact (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hsq f x)).trans hj
  have hmomeq : ∀ (r : ℕ) (f : Fin r → ι), ∫ x, monomial f x ∂(μi : Measure (ι → ℝ)) =
      ∫ x, monomial f x ∂(νi : Measure (ι → ℝ)) := by
    intro r f
    have h1 := (hmon _ _ hμlim hBμ r f).2.sub (hmon _ _ hνlim hBν' r f).2
    have h2 : Tendsto (fun j => ∫ x, monomial f x ∂(toPM (μ (a (ψ j))) : Measure (ι → ℝ)) -
        ∫ x, monomial f x ∂(toPM (ν (a (ψ j))) : Measure (ι → ℝ))) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro η hη
      filter_upwards [hev (hmom r f (η / 2) (by positivity))] with j hj
      rw [Real.dist_eq, sub_zero, coe_toPM, coe_toPM]
      linarith
    exact sub_eq_zero.mp (tendsto_nhds_unique h1 h2)
  have hexp : ∀ (σs : ℕ → ProbabilityMeasure (ι → ℝ)) (σ : ProbabilityMeasure (ι → ℝ)),
      Tendsto σs atTop (𝓝 σ) → (∀ m : ℕ, ∀ᶠ j in atTop,
        ∫⁻ x, ENNReal.ofReal (absSum x ^ m) ∂(σs j : Measure (ι → ℝ)) ≤
          ENNReal.ofReal (m.factorial * R ^ m + 1)) →
      Integrable (fun x => Real.exp ((2 * (R + 1))⁻¹ * absSum x)) (σ : Measure (ι → ℝ)) := by
    intro σs σ hl hB
    have hm : ∀ m : ℕ, ∫⁻ x, ENNReal.ofReal (absSum x ^ m) ∂(σ : Measure (ι → ℝ)) ≤
        ENNReal.ofReal (2 * m.factorial * (R + 1) ^ m) := by
      intro m
      refine (lintegral_le_of_tendsto hl (continuous_absSum.pow m)
        (fun x => pow_nonneg (absSum_nonneg x) m) (hB m)).trans (ENNReal.ofReal_le_ofReal ?_)
      have h1 : R ^ m ≤ (R + 1) ^ m := pow_le_pow_left₀ hR (by linarith) m
      have h2 : (1 : ℝ) ≤ (R + 1) ^ m := one_le_pow₀ (by linarith)
      have h3 : (1 : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_pos m
      nlinarith
    have hl' := lintegral_exp_le_of_moments hR (by norm_num : (0 : ℝ) ≤ 2) hm
    refine ⟨(Real.continuous_exp.comp (continuous_const.mul continuous_absSum)).aestronglyMeasurable,
      ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => (Real.exp_pos _).le)]
    exact lt_of_le_of_lt hl' ENNReal.ofReal_lt_top
  have heq : (μi : Measure (ι → ℝ)) = (νi : Measure (ι → ℝ)) :=
    eq_of_mixed_moments (s := (2 * (R + 1))⁻¹) (by positivity) (hexp _ _ hμlim hBμ)
      (hexp _ _ hνlim hBν') hmomeq
  have hhμ := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμlim) h
  have hhν := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hνlim) h
  rw [heq] at hhμ
  have hd := hhμ.sub hhν
  rw [sub_self] at hd
  obtain ⟨j, hj⟩ := (hd.eventually (Metric.ball_mem_nhds 0 hε)).exists
  have hg := hgap (ψ j)
  simp only [Real.dist_eq, sub_zero, coe_toPM] at hj
  linarith

end BlockBand.Endpoints.Normalization
