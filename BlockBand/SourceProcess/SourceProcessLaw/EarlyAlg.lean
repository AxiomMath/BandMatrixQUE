module

public import BlockBand.SourceProcess.SourceProcessLaw.DetBound
public import BlockBand.SourceProcess.SourceProcessLaw.Interface

/-!
# `EarlySources`, pointwise part: truncating tests changes each factor by the early trace

For a test `q` on `[0,T]` and `s > 0`, `Q(q) = Q(q 1_{[s,T]}) + Σ_k e_k Y_{n;k}` with weights
`e_k = (q - q 1_{[s,T]})((k+1)/W)/W² ≥ 0` (`intervalSource_split`). All matrices are positive
semidefinite, so by `abs_re_inv_det_sub_le` and `abs_prod_sub_le` the integrand of
`sourceTransform` changes by at most `Σ_j Σ_a a_{j,a} Σ_k e_{a,k} Re Tr Y_{n;k}`
(`abs_integrand_sub_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourceProcessLaw

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath
open scoped ComplexOrder

theorem abs_prod_sub_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) :
    |∏ i ∈ s, x i - ∏ i ∈ s, y i| ≤ ∑ i ∈ s, |x i - y i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hP : 0 ≤ ∏ i ∈ s, y i := Finset.prod_nonneg fun i _ => (hy i).1
    have hP1 : ∏ i ∈ s, y i ≤ 1 := Finset.prod_le_one₀ (fun i _ => (hy i).1) fun i _ => (hy i).2
    have e : x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i =
        x a * (∏ i ∈ s, x i - ∏ i ∈ s, y i) + (x a - y a) * ∏ i ∈ s, y i := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (hx a).1, abs_of_nonneg hP]
    have h1 : x a * |∏ i ∈ s, x i - ∏ i ∈ s, y i| ≤ |∏ i ∈ s, x i - ∏ i ∈ s, y i| :=
      mul_le_of_le_one_left (abs_nonneg _) (hx a).2
    have h2 : |x a - y a| * ∏ i ∈ s, y i ≤ |x a - y a| :=
      mul_le_of_le_one_right (abs_nonneg _) hP1
    linarith

variable {W : ℕ}

theorem tagProjection_posSemidef (n k : ℕ) : (tagProjection W n k).PosSemidef := by
  rw [tagProjection, posSemidef_diagonal_iff]
  intro x
  split_ifs <;> simp

theorem tagResponse_posSemidef (b E : ℝ) (n k : ℕ) (ω : GrowthPath W) :
    (tagResponse b E W n k ω).PosSemidef :=
  (tagProjection_posSemidef n k).conjTranspose_mul_mul_same _

/-- `Σ_{k<n} w_k Y_{n;k}`. -/
def weightedSource (b E : ℝ) (W n : ℕ) (w : ℕ → ℝ) (ω : GrowthPath W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ∑ k ∈ Finset.range n, ((w k : ℝ) : ℂ) • tagResponse b E W n k ω

theorem weightedSource_posSemidef (b E : ℝ) (n : ℕ) {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k)
    (ω : GrowthPath W) : (weightedSource b E W n w ω).PosSemidef :=
  posSemidef_sum _ fun k _ => (tagResponse_posSemidef b E n k ω).smul
    (by exact_mod_cast hw k)

theorem re_trace_weightedSource (b E : ℝ) (n : ℕ) (w : ℕ → ℝ) (ω : GrowthPath W) :
    (weightedSource b E W n w ω).trace.re =
      ∑ k ∈ Finset.range n, w k * (tagResponse b E W n k ω).trace.re := by
  simp [weightedSource, trace_sum, trace_smul, Complex.re_sum]

/-- The early weights `e_k = (q - q 1_{[s,T]})((k+1)/W)/W²`. -/
def earlyWeight (W : ℕ) (s T : ℝ) (q : ℝ → ℝ) (k : ℕ) : ℝ :=
  (q (((k + 1 : ℕ) : ℝ) / W) - Set.indicator (Set.Icc s T) q (((k + 1 : ℕ) : ℝ) / W)) /
    (W : ℝ) ^ 2

theorem earlyWeight_nonneg {s T : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) (k : ℕ) :
    0 ≤ earlyWeight W s T q k := by
  unfold earlyWeight
  refine div_nonneg ?_ (sq_nonneg _)
  by_cases h : (((k + 1 : ℕ) : ℝ) / W) ∈ Set.Icc s T
  · rw [Set.indicator_of_mem h]; simp
  · rw [Set.indicator_of_notMem h]; simpa using hq _

theorem intervalSource_split (b E : ℝ) (n : ℕ) (s T : ℝ) (q : ℝ → ℝ) (ω : GrowthPath W) :
    intervalSource b E W n q ω =
      intervalSource b E W n (Set.indicator (Set.Icc s T) q) ω +
        weightedSource b E W n (earlyWeight W s T q) ω := by
  simp only [intervalSource, weightedSource, ← Finset.sum_add_distrib, ← add_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  push_cast [earlyWeight]
  ring

theorem intervalSource_posSemidef (b E : ℝ) (n : ℕ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    (ω : GrowthPath W) : (intervalSource b E W n q ω).PosSemidef :=
  posSemidef_sum _ fun k _ => (tagResponse_posSemidef b E n k ω).smul
    (by
      have : 0 ≤ q (((k + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 := div_nonneg (hq _) (sq_nonneg _)
      exact_mod_cast this)

/-- The integrand of `sourceTransform` at length `n`. -/
def srcIntegrand (b E : ℝ) (W n : ℕ) {p J : ℕ} (q : Fin p → ℝ → ℝ) (a : Fin J → Fin p → ℝ)
    (ω : GrowthPath W) : ℝ :=
  ∏ j, (((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
      ∑ i, (a j i : ℂ) • intervalSource b E W n (q i) ω).det⁻¹).re

theorem combo_posSemidef (b E : ℝ) (n : ℕ) {p : ℕ} {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x)
    {c : Fin p → ℝ} (hc : ∀ i, 0 ≤ c i) (ω : GrowthPath W) :
    (∑ i, (c i : ℂ) • intervalSource b E W n (q i) ω).PosSemidef :=
  posSemidef_sum _ fun i _ => (intervalSource_posSemidef b E n (hq i) ω).smul
    (by exact_mod_cast hc i)

theorem srcIntegrand_factor_mem (b E : ℝ) (n : ℕ) {p : ℕ} {q : Fin p → ℝ → ℝ}
    (hq : ∀ i x, 0 ≤ q i x) {c : Fin p → ℝ} (hc : ∀ i, 0 ≤ c i) (ω : GrowthPath W) :
    0 ≤ ((1 + ∑ i, (c i : ℂ) • intervalSource b E W n (q i) ω).det⁻¹).re ∧
      ((1 + ∑ i, (c i : ℂ) • intervalSource b E W n (q i) ω).det⁻¹).re ≤ 1 :=
  let h := re_inv_det_mem (combo_posSemidef b E n hq hc ω)
  ⟨h.1.le, h.2⟩

theorem abs_srcIntegrand_le_one (b E : ℝ) (n : ℕ) {p J : ℕ} {q : Fin p → ℝ → ℝ}
    (hq : ∀ i x, 0 ≤ q i x) {a : Fin J → Fin p → ℝ} (ha : ∀ j i, 0 ≤ a j i) (ω : GrowthPath W) :
    |srcIntegrand b E W n q a ω| ≤ 1 := by
  unfold srcIntegrand
  rw [abs_of_nonneg (Finset.prod_nonneg fun j _ => (srcIntegrand_factor_mem b E n hq (ha j) ω).1)]
  exact Finset.prod_le_one₀ (fun j _ => (srcIntegrand_factor_mem b E n hq (ha j) ω).1)
    fun j _ => (srcIntegrand_factor_mem b E n hq (ha j) ω).2

/-- **Pointwise early-source bound.** -/
theorem abs_integrand_sub_le (b E : ℝ) (n : ℕ) (s T : ℝ) {p J : ℕ} {q : Fin p → ℝ → ℝ}
    (hq : ∀ i x, 0 ≤ q i x) {a : Fin J → Fin p → ℝ} (ha : ∀ j i, 0 ≤ a j i) (ω : GrowthPath W) :
    |srcIntegrand b E W n q a ω -
        srcIntegrand b E W n (fun i => Set.indicator (Set.Icc s T) (q i)) a ω| ≤
      ∑ j, ∑ i, a j i * ∑ k ∈ Finset.range n,
        earlyWeight W s T (q i) k * (tagResponse b E W n k ω).trace.re := by
  have hqs : ∀ i x, 0 ≤ Set.indicator (Set.Icc s T) (q i) x :=
    fun i x => Set.indicator_nonneg (fun y _ => hq i y) x
  refine (abs_prod_sub_le _ _ _ (fun j => srcIntegrand_factor_mem b E n hq (ha j) ω)
    (fun j => srcIntegrand_factor_mem b E n hqs (ha j) ω)).trans
    (Finset.sum_le_sum fun j _ => ?_)
  set A := ∑ i, (a j i : ℂ) • intervalSource b E W n (Set.indicator (Set.Icc s T) (q i)) ω
  set B := ∑ i, (a j i : ℂ) • weightedSource b E W n (earlyWeight W s T (q i)) ω
  have hAB : ∑ i, (a j i : ℂ) • intervalSource b E W n (q i) ω = A + B := by
    simp only [A, B, intervalSource_split b E n s T (q _) ω, smul_add, Finset.sum_add_distrib]
  have hA : A.PosSemidef := combo_posSemidef b E n hqs (ha j) ω
  have hB : B.PosSemidef := posSemidef_sum _ fun i _ =>
    (weightedSource_posSemidef b E n (earlyWeight_nonneg (hq i)) ω).smul
      (by exact_mod_cast ha j i)
  rw [hAB, abs_sub_comm]
  refine (abs_re_inv_det_sub_le hA hB).trans (le_of_eq ?_)
  simp only [B, trace_sum, trace_smul, Complex.re_sum, smul_eq_mul, Complex.re_ofReal_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [re_trace_weightedSource]

end BlockBand.SourceProcess.SourceProcessLaw
