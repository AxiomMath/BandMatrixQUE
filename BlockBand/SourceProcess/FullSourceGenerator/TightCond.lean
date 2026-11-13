module

public import BlockBand.SourceProcess.FullSourceGenerator.CondTools

/-!
# One step of `tight`: drift, variance and fourth moment from complex error bounds

Abstract (no random-band content); the per-step inputs of the tightness step for the full-source
stops. The summed errors of the
generator identity (`EarlySummed`) are stated for complex conditional expectations of complex
increments; here the increments are real (`ConjWord`: `Re`/`Im` of words are ordinary trace
polynomials) and the bounds are transferred to real conditional expectations.

* `condExp_ofReal`: `E[f|m]` commutes with `ℝ → ℂ` (also for non-integrable `f`).
* `ae_abs_condExp_le`: for `d` vanishing off the `m`-event `A`, and `‖P‖ ≤ C` on `A`:
  `|E[d|m]| ≤ sC + ‖1_A(E[d|m] - sP)‖` a.e. (drift and variance, with `s = W⁻¹`).
* `integral_pow4_le` (the fourth-moment cancellation): for real `Y`
  (`m`-measurable, `|Y| ≤ C_X` on `A`) and `Y'`, if `Σ_{r≤4} C(4,r)(-Y)^{4-r}P_r = 0` pointwise
  (`fourth_cancel` for the generator of `Φ^r`), then
  `E[1_A(Y'-Y)⁴] ≤ Σ_{r≤4} C(4,r) C_X^{4-r} E‖1_A(E[1_A(Y'^r - Y^r)|m] - sP_r)‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MeasureTheory Set Finset

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Conditional expectation commutes with `ℝ → ℂ`. -/
theorem condExp_ofReal (f : Ω → ℝ) :
    (fun ω => ((μ[f | m] ω : ℝ) : ℂ)) =ᵐ[μ] μ[fun ω => (f ω : ℂ) | m] := by
  by_cases hf : Integrable f μ
  · exact Complex.ofRealCLM.comp_condExp_comm hf
  · have hf' : ¬ Integrable (fun ω => (f ω : ℂ)) μ := fun h =>
      hf (by simpa using Complex.reCLM.integrable_comp h)
    rw [condExp_of_not_integrable hf, condExp_of_not_integrable hf']
    exact Filter.Eventually.of_forall fun ω => by simp

/-- `E[d|m]` vanishes off the `m`-event `A` when `d` does. -/
theorem ae_condExp_eq_indicator [IsFiniteMeasure μ] {A : Set Ω} (hA : MeasurableSet[m] A)
    {d : Ω → ℝ} (hdA : ∀ ω, ω ∉ A → d ω = 0) :
    ∀ᵐ ω ∂μ, μ[d | m] ω = A.indicator (μ[d | m]) ω := by
  have hdeq : A.indicator d = d := funext fun ω => by
    by_cases h : ω ∈ A <;> simp [h, hdA]
  by_cases hf : Integrable d μ
  · have := condExp_indicator (μ := μ) hf hA
    rwa [hdeq] at this
  · rw [condExp_of_not_integrable hf]
    exact Filter.Eventually.of_forall fun ω => by simp

/-- **Drift/variance transfer**: `|E[d|m]| ≤ sC + ‖1_A(E[d|m] - sP)‖` a.e. -/
theorem ae_abs_condExp_le [IsFiniteMeasure μ] {A : Set Ω} (hA : MeasurableSet[m] A)
    {d : Ω → ℝ} (hdA : ∀ ω, ω ∉ A → d ω = 0) {P : Ω → ℂ} {s C : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hP : ∀ᵐ ω ∂μ, ω ∈ A → ‖P ω‖ ≤ C) :
    ∀ᵐ ω ∂μ, |μ[d | m] ω| ≤ s * C +
      ‖A.indicator (fun ω => μ[fun ω => (d ω : ℂ) | m] ω - (s : ℂ) * P ω) ω‖ := by
  filter_upwards [ae_condExp_eq_indicator hA hdA, condExp_ofReal (μ := μ) (m := m) d, hP]
    with ω h1 h2 h3
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω]
    have h2' : ((μ[d | m] ω : ℝ) : ℂ) = μ[fun ω => (d ω : ℂ) | m] ω := h2
    have e : |μ[d | m] ω| = ‖μ[fun ω => (d ω : ℂ) | m] ω‖ := by
      rw [← h2', Complex.norm_real, Real.norm_eq_abs]
    rw [e]
    have hsP : ‖(s : ℂ) * P ω‖ ≤ s * C := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
      exact mul_le_mul_of_nonneg_left (h3 hω) hs
    have := norm_sub_norm_le (μ[fun ω => (d ω : ℂ) | m] ω) ((s : ℂ) * P ω)
    linarith
  · rw [h1, Set.indicator_of_notMem hω, abs_zero]
    exact add_nonneg (mul_nonneg hs hC) (norm_nonneg _)

theorem pow_mul_pow_le_add (x y : ℝ) {r : ℕ} (hr : r ≤ 4) :
    |x| ^ (4 - r) * |y| ^ r ≤ x ^ 4 + y ^ 4 := by
  set M := max |x| |y|
  have hx : |x| ≤ M := le_max_left _ _
  have hy : |y| ≤ M := le_max_right _ _
  have h1 : |x| ^ (4 - r) * |y| ^ r ≤ M ^ (4 - r) * M ^ r :=
    mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx _) (pow_le_pow_left₀ (abs_nonneg _) hy _)
      (pow_nonneg (abs_nonneg _) _) (pow_nonneg ((abs_nonneg x).trans hx) _)
  rw [← pow_add, Nat.sub_add_cancel hr] at h1
  have h2 : M ^ 4 ≤ x ^ 4 + y ^ 4 := by
    rcases max_choice |x| |y| with h | h <;> rw [show M = _ from h]
    · rw [Even.pow_abs (by decide)]; nlinarith [Even.pow_nonneg (by decide : Even 4) y]
    · rw [Even.pow_abs (by decide)]; nlinarith [Even.pow_nonneg (by decide : Even 4) x]
  linarith

theorem abs_pow_le_one_add (x : ℝ) {r : ℕ} (hr : r ≤ 4) : |x| ^ r ≤ 1 + x ^ 4 := by
  rcases le_total |x| 1 with h | h
  · have := pow_le_one₀ (abs_nonneg x) h (n := r)
    nlinarith [Even.pow_nonneg (by decide : Even 4) x]
  · have h1 := pow_le_pow_right₀ h hr
    have e : |x| ^ 4 = x ^ 4 := Even.pow_abs (by decide) x
    linarith

/-- **The fourth moment of one step** through the generator of `Φ^r`, `r ≤ 4`. -/
theorem integral_pow4_le (hm : m ≤ m0) [IsProbabilityMeasure μ] {A : Set Ω}
    (hA : MeasurableSet[m] A) {Y Y' : Ω → ℝ} (hY : StronglyMeasurable[m] Y)
    (hY' : AEStronglyMeasurable Y' μ) (hY4 : Integrable (fun ω => Y ω ^ 4) μ)
    (hY'4 : Integrable (fun ω => Y' ω ^ 4) μ) {CX : ℝ} (hCX0 : 0 ≤ CX)
    (hCX : ∀ᵐ ω ∂μ, ω ∈ A → |Y ω| ≤ CX) (s : ℝ) (P : ℕ → Ω → ℂ)
    (hcancel : ∀ ω, ∑ r ∈ range 5,
      ((Nat.choose 4 r : ℕ) : ℂ) * (-(Y ω : ℂ)) ^ (4 - r) * P r ω = 0)
    (hei : ∀ r < 5, Integrable (fun ω => ‖A.indicator (fun ω => μ[fun ω =>
      ((A.indicator (fun ω => Y' ω ^ r - Y ω ^ r) ω : ℝ) : ℂ) | m] ω - (s : ℂ) * P r ω) ω‖) μ) :
    ∫ ω, A.indicator (fun ω => Y' ω - Y ω) ω ^ 4 ∂μ ≤
      ∑ r ∈ range 5, (Nat.choose 4 r : ℝ) * CX ^ (4 - r) * ∫ ω, ‖A.indicator (fun ω => μ[fun ω =>
        ((A.indicator (fun ω => Y' ω ^ r - Y ω ^ r) ω : ℝ) : ℂ) | m] ω - (s : ℂ) * P r ω) ω‖ ∂μ := by
  set Δ : ℕ → Ω → ℝ := fun r => A.indicator fun ω => Y' ω ^ r - Y ω ^ r with hΔ
  set Z : ℕ → Ω → ℝ := fun r => A.indicator fun ω => (-Y ω) ^ (4 - r) with hZ
  set e : ℕ → Ω → ℝ := fun r ω => ‖A.indicator (fun ω => μ[fun ω =>
      ((Δ r ω : ℝ) : ℂ) | m] ω - (s : ℂ) * P r ω) ω‖ with he
  have hAm : MeasurableSet A := hm _ hA
  have hYm : AEStronglyMeasurable Y μ := (hY.mono hm).aestronglyMeasurable
  have hZm : ∀ r, StronglyMeasurable[m] (Z r) := fun r => (hY.neg.pow _).indicator hA
  have hΔm : ∀ r, AEStronglyMeasurable (Δ r) μ := fun r => ((hY'.pow r).sub (hYm.pow r)).indicator hAm
  have hΔi : ∀ r ≤ 4, Integrable (Δ r) μ := fun r hr => by
    refine integrable_of_norm_le (hΔm r) (((integrable_const 2).add hY4).add hY'4)
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hΔ, Pi.add_apply]
    by_cases h : ω ∈ A
    · rw [Set.indicator_of_mem h, Real.norm_eq_abs]
      refine (abs_sub _ _).trans ?_
      rw [abs_pow, abs_pow]
      linarith [abs_pow_le_one_add (Y' ω) hr, abs_pow_le_one_add (Y ω) hr]
    · rw [Set.indicator_of_notMem h, norm_zero]
      linarith [Even.pow_nonneg (by decide : Even 4) (Y ω), Even.pow_nonneg (by decide : Even 4) (Y' ω)]
  have hZΔ : ∀ r ≤ 4, Integrable (fun ω => Z r ω * Δ r ω) μ := fun r hr => by
    refine integrable_of_norm_le (((hZm r).mono hm).aestronglyMeasurable.mul (hΔm r))
      ((hY4.add hY'4).const_mul 3) (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hZ, hΔ, Pi.add_apply]
    by_cases h : ω ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Real.norm_eq_abs, abs_mul]
      refine (mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)).trans ?_
      rw [abs_pow, abs_pow, abs_pow, abs_neg, mul_add]
      have h1 := pow_mul_pow_le_add (Y ω) (Y' ω) hr
      have h2 := pow_mul_pow_le_add (Y ω) (Y ω) hr
      nlinarith [Even.pow_nonneg (by decide : Even 4) (Y ω), Even.pow_nonneg (by decide : Even 4) (Y' ω)]
    · rw [Set.indicator_of_notMem h, zero_mul, norm_zero]
      nlinarith [Even.pow_nonneg (by decide : Even 4) (Y ω), Even.pow_nonneg (by decide : Even 4) (Y' ω)]
  have hrng : ∀ r ∈ range 5, r ≤ 4 := fun r hr => Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  -- the pointwise expansion
  have hexp : ∀ ω, A.indicator (fun ω => Y' ω - Y ω) ω ^ 4 =
      ∑ r ∈ range 5, (Nat.choose 4 r : ℝ) * (Z r ω * Δ r ω) := fun ω => by
    by_cases h : ω ∈ A
    · simp only [hZ, hΔ, Set.indicator_of_mem h, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num [Nat.choose]; ring
    · simp [hZ, hΔ, Set.indicator_of_notMem h]
  have hI1 : ∫ ω, A.indicator (fun ω => Y' ω - Y ω) ω ^ 4 ∂μ =
      ∫ ω, ∑ r ∈ range 5, (Nat.choose 4 r : ℝ) * (Z r ω * μ[Δ r | m] ω) ∂μ := by
    simp_rw [hexp]
    rw [integral_finsetSum _ fun r hr => (hZΔ r (hrng r hr)).const_mul _,
      integral_finsetSum _ fun r hr =>
        (integrable_mul_condExp (hZm r) (hZΔ r (hrng r hr)) (hΔi r (hrng r hr))).const_mul _]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [integral_const_mul, integral_const_mul,
      integral_mul_condExp hm (hZm r) (hZΔ r (hrng r hr)) (hΔi r (hrng r hr))]
  -- the pointwise bound
  have hcomm : ∀ᵐ ω ∂μ, ∀ r, ((μ[Δ r | m] ω : ℝ) : ℂ) = μ[fun ω => ((Δ r ω : ℝ) : ℂ) | m] ω :=
    ae_all_iff.2 fun r => condExp_ofReal (Δ r)
  have hbd : ∀ᵐ ω ∂μ, ‖∑ r ∈ range 5, (Nat.choose 4 r : ℝ) * (Z r ω * μ[Δ r | m] ω)‖ ≤
      ∑ r ∈ range 5, (Nat.choose 4 r : ℝ) * CX ^ (4 - r) * e r ω := by
    filter_upwards [hcomm, hCX] with ω h1 h2
    have hR0 : 0 ≤ ∑ r ∈ range 5, (Nat.choose 4 r : ℝ) * CX ^ (4 - r) * e r ω :=
      Finset.sum_nonneg fun r _ => by positivity
    by_cases h : ω ∈ A
    · have hZr : ∀ r, Z r ω = (-Y ω) ^ (4 - r) := fun r => by simp [hZ, Set.indicator_of_mem h]
      have her : ∀ r, e r ω = ‖μ[fun ω => ((Δ r ω : ℝ) : ℂ) | m] ω - (s : ℂ) * P r ω‖ :=
        fun r => by simp only [he, Set.indicator_of_mem h]
      simp_rw [hZr]
      set L := ∑ r ∈ range 5, (Nat.choose 4 r : ℝ) * ((-Y ω) ^ (4 - r) * μ[Δ r | m] ω)
      have hL : (L : ℂ) = ∑ r ∈ range 5, ((Nat.choose 4 r : ℕ) : ℂ) * (-(Y ω : ℂ)) ^ (4 - r) *
          (μ[fun ω => ((Δ r ω : ℝ) : ℂ) | m] ω - (s : ℂ) * P r ω) := by
        have e0 := hcancel ω
        have : (L : ℂ) = ∑ r ∈ range 5, ((Nat.choose 4 r : ℕ) : ℂ) * (-(Y ω : ℂ)) ^ (4 - r) *
            (μ[fun ω => ((Δ r ω : ℝ) : ℂ) | m] ω - (s : ℂ) * P r ω) + (s : ℂ) *
              ∑ r ∈ range 5, ((Nat.choose 4 r : ℕ) : ℂ) * (-(Y ω : ℂ)) ^ (4 - r) * P r ω := by
          simp only [L, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
            Complex.ofReal_neg, Complex.ofReal_natCast, h1, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun r _ => by ring
        rw [this, e0, mul_zero, add_zero]
      rw [← Complex.norm_real, hL]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => ?_)
      rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Complex.norm_natCast,
        Real.norm_eq_abs, her r]
      gcongr
      exact h2 h
    · simp only [hZ, Set.indicator_of_notMem h, zero_mul, mul_zero, Finset.sum_const_zero,
        norm_zero]
      exact hR0
  have hgi : Integrable (fun ω => ∑ r ∈ range 5, (Nat.choose 4 r : ℝ) * CX ^ (4 - r) * e r ω) μ :=
    integrable_finsetSum _ fun r hr => (hei r (Finset.mem_range.mp hr)).const_mul _
  rw [hI1]
  refine (le_abs_self _).trans ?_
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hgi hbd).trans_eq ?_
  rw [integral_finsetSum _ fun r hr => (hei r (Finset.mem_range.mp hr)).const_mul _]
  exact Finset.sum_congr rfl fun r _ => integral_const_mul _ _

end BlockBand.SourceProcess.FullSourceGenerator
