module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# A discrete Doob decomposition estimate (abstract)

For a real process `X` adapted to an increasing family of sub-σ-algebras `ℱ` on a probability
space, split each increment `X(n+1) - X(n)` into its predictable part `μ[X(n+1) - X(n) | ℱ n]`
and the martingale difference `mart n`. The martingale differences are orthogonal in `L²`, so
over `N` steps starting at `a`:

`μ{t ≤ |X(a+N) - X(a)|} ≤ 4 N v / t² + 2 N c / t`,

when every predictable part has `L¹` norm `≤ c` and every martingale difference has second
moment `≤ v` (`measureReal_abs_sub_ge_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont

open MeasureTheory Finset

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The increment `X(n+1) - X(n)`. -/
def incr (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ := fun ω => X (n + 1) ω - X n ω

/-- The martingale difference `X(n+1) - X(n) - μ[X(n+1) - X(n) | ℱ n]`. -/
def mart (μ : Measure Ω) (ℱ : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => incr X n ω - μ[incr X n | ℱ n] ω

/-- Orthogonality of a martingale difference to an `ℱ`-measurable `L²` function. -/
theorem integral_mul_sub_condExp [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {S D : Ω → ℝ}
    (hS : StronglyMeasurable[m] S) (hS2 : MemLp S 2 μ) (hD2 : MemLp D 2 μ) :
    ∫ ω, S ω * (D ω - μ[D | m] ω) ∂μ = 0 := by
  have hSD : Integrable (S * D) μ := hS2.integrable_mul hD2
  have hC2 : MemLp (μ[D | m]) 2 μ := hD2.condExp (by norm_num)
  have hSC : Integrable (S * μ[D | m]) μ := hS2.integrable_mul hC2
  have hpull := condExp_mul_of_stronglyMeasurable_left hS hSD (hD2.integrable one_le_two)
  have h1 : ∫ ω, S ω * μ[D | m] ω ∂μ = ∫ ω, S ω * D ω ∂μ := by
    calc ∫ ω, S ω * μ[D | m] ω ∂μ = ∫ ω, μ[S * D | m] ω ∂μ :=
          (integral_congr_ae hpull).symm
      _ = ∫ ω, (S * D) ω ∂μ := integral_condExp hm
      _ = ∫ ω, S ω * D ω ∂μ := rfl
  simp only [mul_sub]
  rw [integral_sub (f := fun ω => S ω * D ω) (g := fun ω => S ω * μ[D | m] ω) hSD hSC, h1,
    sub_self]

section Process

variable (ℱ : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ)

theorem memLp_mart {n : ℕ} (h2 : MemLp (incr X n) 2 μ) : MemLp (mart μ ℱ X n) 2 μ :=
  h2.sub (h2.condExp (by norm_num))

theorem stronglyMeasurable_mart (hmono : Monotone ℱ)
    (hX : ∀ n, StronglyMeasurable[ℱ n] (X n)) (n : ℕ) :
    StronglyMeasurable[ℱ (n + 1)] (mart μ ℱ X n) := by
  have hle : ℱ n ≤ ℱ (n + 1) := hmono (Nat.le_succ n)
  have hI : StronglyMeasurable[ℱ (n + 1)] (incr X n) :=
    (hX (n + 1)).sub ((hX n).mono hle)
  exact hI.sub (stronglyMeasurable_condExp.mono hle)

/-- The martingale part over `N` steps from `a`. -/
def martSum (μ : Measure Ω) (a N : ℕ) : Ω → ℝ := fun ω => ∑ i ∈ range N, mart μ ℱ X (a + i) ω

/-- The predictable part over `N` steps from `a`. -/
def driftSum (μ : Measure Ω) (a N : ℕ) : Ω → ℝ :=
  fun ω => ∑ i ∈ range N, μ[incr X (a + i) | ℱ (a + i)] ω

theorem sub_eq_martSum_add_driftSum (a N : ℕ) (ω : Ω) :
    X (a + N) ω - X a ω = martSum ℱ X μ a N ω + driftSum ℱ X μ a N ω := by
  have htel : ∑ i ∈ range N, incr X (a + i) ω = X (a + N) ω - X a ω := by
    simpa [incr, add_assoc] using Finset.sum_range_sub (fun i => X (a + i) ω) N
  rw [← htel, martSum, driftSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mart]

/-- The martingale part: adapted, in `L²`, and its second moment is the sum of the second
moments of the differences (orthogonality). -/
theorem martSum_props [IsProbabilityMeasure μ] (hℱ : ∀ n, ℱ n ≤ m0) (hmono : Monotone ℱ)
    (hX : ∀ n, StronglyMeasurable[ℱ n] (X n)) (a : ℕ) :
    ∀ N : ℕ, (∀ i < N, MemLp (incr X (a + i)) 2 μ) →
      StronglyMeasurable[ℱ (a + N)] (martSum ℱ X μ a N) ∧ MemLp (martSum ℱ X μ a N) 2 μ ∧
        ∫ ω, martSum ℱ X μ a N ω ^ 2 ∂μ =
          ∑ i ∈ range N, ∫ ω, mart μ ℱ X (a + i) ω ^ 2 ∂μ := by
  intro N
  induction N with
  | zero =>
    intro _
    have h0 : martSum ℱ X μ a 0 = fun _ => 0 := by funext ω; simp [martSum]
    rw [h0]
    exact ⟨stronglyMeasurable_const, MemLp.zero', by simp⟩
  | succ N ih =>
    intro h2
    obtain ⟨hSm, hS2, hSq⟩ := ih fun i hi => h2 i (Nat.lt_succ_of_lt hi)
    have hD2 : MemLp (incr X (a + N)) 2 μ := h2 N (Nat.lt_succ_self N)
    have hm2 := memLp_mart (μ := μ) ℱ X hD2
    have hmm : StronglyMeasurable[ℱ (a + (N + 1))] (mart μ ℱ X (a + N)) :=
      stronglyMeasurable_mart ℱ X hmono hX (a + N)
    have hsplit : martSum ℱ X μ a (N + 1) =
        fun ω => martSum ℱ X μ a N ω + mart μ ℱ X (a + N) ω := by
      funext ω; simp [martSum, sum_range_succ]
    refine ⟨?_, ?_, ?_⟩
    · rw [hsplit]
      exact (hSm.mono (hmono (Nat.le_succ _))).add hmm
    · rw [hsplit]; exact hS2.add hm2
    · have horth : ∫ ω, martSum ℱ X μ a N ω * mart μ ℱ X (a + N) ω ∂μ = 0 :=
        integral_mul_sub_condExp (hℱ (a + N)) hSm hS2 hD2
      have hI1 : Integrable (fun ω => martSum ℱ X μ a N ω ^ 2) μ := hS2.integrable_sq
      have hI2 : Integrable (fun ω => 2 * (martSum ℱ X μ a N ω * mart μ ℱ X (a + N) ω)) μ :=
        (hS2.integrable_mul hm2).const_mul 2
      have hI3 : Integrable (fun ω => mart μ ℱ X (a + N) ω ^ 2) μ := hm2.integrable_sq
      rw [hsplit, sum_range_succ, ← hSq]
      have hexp : (fun ω => (martSum ℱ X μ a N ω + mart μ ℱ X (a + N) ω) ^ 2) =
          fun ω => martSum ℱ X μ a N ω ^ 2 +
            2 * (martSum ℱ X μ a N ω * mart μ ℱ X (a + N) ω) + mart μ ℱ X (a + N) ω ^ 2 := by
        funext ω; ring
      rw [hexp, integral_add (f := fun ω => martSum ℱ X μ a N ω ^ 2 +
          2 * (martSum ℱ X μ a N ω * mart μ ℱ X (a + N) ω)) (hI1.add hI2) hI3,
        integral_add (f := fun ω => martSum ℱ X μ a N ω ^ 2) hI1 hI2, integral_const_mul,
        horth, mul_zero, add_zero]

end Process

/-- Chebyshev in `L²`. -/
theorem measureReal_abs_ge_le_sq [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) {t : ℝ}
    (ht : 0 < t) :
    μ.real {ω | t ≤ |f ω|} ≤ (∫ ω, f ω ^ 2 ∂μ) / t ^ 2 := by
  have hsub : {ω | t ≤ |f ω|} ⊆ {ω | t ^ 2 ≤ f ω ^ 2} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have := pow_le_pow_left₀ ht.le hω 2
    rwa [sq_abs] at this
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (Filter.Eventually.of_forall fun ω => sq_nonneg (f ω)) hf.integrable_sq (t ^ 2)
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (by positivity)).trans hM

/-- Markov in `L¹`. -/
theorem measureReal_abs_ge_le_abs [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |f ω|} ≤ (∫ ω, |f ω| ∂μ) / t := by
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (Filter.Eventually.of_forall fun ω => abs_nonneg (f ω)) hf.abs t
  rw [le_div_iff₀ ht, mul_comm]
  exact hM

/-- **The Doob estimate.** Over `N` steps from `a`, with predictable parts of `L¹` norm `≤ c`
and martingale differences of second moment `≤ v`:
`μ{t ≤ |X(a+N) - X(a)|} ≤ 4 N v / t² + 2 N c / t`. -/
theorem measureReal_abs_sub_ge_le [IsProbabilityMeasure μ] (ℱ : ℕ → MeasurableSpace Ω)
    (X : ℕ → Ω → ℝ)
    (hℱ : ∀ n, ℱ n ≤ m0) (hmono : Monotone ℱ) (hX : ∀ n, StronglyMeasurable[ℱ n] (X n))
    (a N : ℕ) {c v t : ℝ} (ht : 0 < t) (h2 : ∀ i < N, MemLp (incr X (a + i)) 2 μ)
    (hdrift : ∀ i < N, ∫ ω, |μ[incr X (a + i) | ℱ (a + i)] ω| ∂μ ≤ c)
    (hvar : ∀ i < N, ∫ ω, mart μ ℱ X (a + i) ω ^ 2 ∂μ ≤ v) :
    μ.real {ω | t ≤ |X (a + N) ω - X a ω|} ≤ 4 * (N * v) / t ^ 2 + 2 * (N * c) / t := by
  obtain ⟨-, hS2, hSq⟩ := martSum_props (μ := μ) ℱ X hℱ hmono hX a N h2
  have hDint : Integrable (driftSum ℱ X μ a N) μ :=
    integrable_finsetSum _ fun i _ => integrable_condExp
  have ht2 : 0 < t / 2 := by positivity
  have hsub : {ω | t ≤ |X (a + N) ω - X a ω|} ⊆
      {ω | t / 2 ≤ |martSum ℱ X μ a N ω|} ∪ {ω | t / 2 ≤ |driftSum ℱ X μ a N ω|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    rw [sub_eq_martSum_add_driftSum (μ := μ)] at hω
    by_contra hcon
    push Not at hcon
    linarith [abs_add_le (martSum ℱ X μ a N ω) (driftSum ℱ X μ a N ω)]
  have hA : μ.real {ω | t / 2 ≤ |martSum ℱ X μ a N ω|} ≤ 4 * (N * v) / t ^ 2 := by
    refine (measureReal_abs_ge_le_sq hS2 ht2).trans ?_
    rw [hSq]
    have hsum : ∑ i ∈ range N, ∫ ω, mart μ ℱ X (a + i) ω ^ 2 ∂μ ≤ N * v := by
      calc ∑ i ∈ range N, ∫ ω, mart μ ℱ X (a + i) ω ^ 2 ∂μ ≤ ∑ _i ∈ range N, v :=
            sum_le_sum fun i hi => hvar i (mem_range.1 hi)
        _ = N * v := by simp
    calc (∑ i ∈ range N, ∫ ω, mart μ ℱ X (a + i) ω ^ 2 ∂μ) / (t / 2) ^ 2
        ≤ (N * v) / (t / 2) ^ 2 := div_le_div_of_nonneg_right hsum (by positivity)
      _ = 4 * (N * v) / t ^ 2 := by field_simp; ring
  have hB : μ.real {ω | t / 2 ≤ |driftSum ℱ X μ a N ω|} ≤ 2 * (N * c) / t := by
    refine (measureReal_abs_ge_le_abs hDint ht2).trans ?_
    have hle : ∫ ω, |driftSum ℱ X μ a N ω| ∂μ ≤ N * c := by
      calc ∫ ω, |driftSum ℱ X μ a N ω| ∂μ
          ≤ ∫ ω, ∑ i ∈ range N, |μ[incr X (a + i) | ℱ (a + i)] ω| ∂μ :=
            integral_mono hDint.abs
              (integrable_finsetSum _ fun i _ => integrable_condExp.abs)
              fun ω => Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i ∈ range N, ∫ ω, |μ[incr X (a + i) | ℱ (a + i)] ω| ∂μ :=
            integral_finsetSum _ fun i _ => integrable_condExp.abs
        _ ≤ ∑ _i ∈ range N, c := sum_le_sum fun i hi => hdrift i (mem_range.1 hi)
        _ = N * c := by simp
    calc (∫ ω, |driftSum ℱ X μ a N ω| ∂μ) / (t / 2) ≤ (N * c) / (t / 2) :=
          div_le_div_of_nonneg_right hle ht2.le
      _ = 2 * (N * c) / t := by field_simp
  calc μ.real {ω | t ≤ |X (a + N) ω - X a ω|}
      ≤ μ.real ({ω | t / 2 ≤ |martSum ℱ X μ a N ω|} ∪
          {ω | t / 2 ≤ |driftSum ℱ X μ a N ω|}) := measureReal_mono hsub
    _ ≤ μ.real {ω | t / 2 ≤ |martSum ℱ X μ a N ω|} +
          μ.real {ω | t / 2 ≤ |driftSum ℱ X μ a N ω|} := measureReal_union_le _ _
    _ ≤ 4 * (N * v) / t ^ 2 + 2 * (N * c) / t := add_le_add hA hB

end BlockBand.SourceProcess.LengthCont
