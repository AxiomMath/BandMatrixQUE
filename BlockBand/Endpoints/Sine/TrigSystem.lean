module

public import BlockBand.PointProcess.Specifications
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The circular trigonometric approximant of the sine kernel

Indexing: `n = 0` is the constant, `1 ≤ n ≤ M` is `cos` with frequency `n`,
`M < n ≤ 2M` is `sin` with frequency `n - M` (written as `cos (· - π/2)`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology

/-- The window `[-N/2, N/2)`, `N = 2M + 1`. -/
def cueWindow (M : ℕ) : Set ℝ := Set.Ico (-(2 * M + 1 : ℝ) / 2) ((2 * M + 1 : ℝ) / 2)

/-- Frequency of the `n`-th trigonometric basis function. -/
def cueFreq (M n : ℕ) : ℕ := if n ≤ M then n else n - M

/-- Phase of the `n`-th trigonometric basis function (`0` for `cos`, `π/2` for `sin`). -/
def cuePhase (M n : ℕ) : ℝ := if n ≤ M then 0 else Real.pi / 2

/-- Normalization of the `n`-th trigonometric basis function. -/
def cueCoeff (M n : ℕ) : ℝ :=
  if n = 0 then 1 / Real.sqrt (2 * M + 1) else Real.sqrt (2 / (2 * M + 1))

/-- The `n`-th trigonometric function
`cueCoeff M n * cos (2π (cueFreq M n) x / N - cuePhase M n)`, `N = 2M + 1`. -/
def cueFun (M n : ℕ) (x : ℝ) : ℝ :=
  cueCoeff M n * Real.cos (2 * Real.pi * (cueFreq M n : ℝ) / (2 * M + 1) * x - cuePhase M n)

/-- The real trigonometric basis of the window `cueWindow M`, indexed by `Fin (2M + 1)`. -/
def cueBasis (M : ℕ) (i : Fin (2 * M + 1)) (x : ℝ) : ℝ := cueFun M i x

/-- The circular (CUE-type) projection kernel `∑ i, cueBasis M i x * cueBasis M i y`. -/
def cueKernel (M : ℕ) (x y : ℝ) : ℝ := ∑ i, cueBasis M i x * cueBasis M i y

/-- Explicit form of the constant basis function: `cueBasis M 0 x = 1/√N`. -/
theorem cueBasis_zero (M : ℕ) (x : ℝ) : cueBasis M 0 x = 1 / Real.sqrt (2 * M + 1) := by
  simp [cueBasis, cueFun, cueFreq, cuePhase, cueCoeff]

/-- Explicit form of the cosine basis functions: for `1 ≤ i ≤ M`,
`cueBasis M i x = √(2/N) cos (2π i x / N)`, `N = 2M + 1`. -/
theorem cueBasis_of_le (M : ℕ) (i : Fin (2 * M + 1)) (h0 : 1 ≤ (i : ℕ)) (hM : (i : ℕ) ≤ M)
    (x : ℝ) :
    cueBasis M i x =
      Real.sqrt (2 / (2 * M + 1)) * Real.cos (2 * Real.pi * (i : ℕ) * x / (2 * M + 1)) := by
  have hne : (i : ℕ) ≠ 0 := by omega
  simp only [cueBasis, cueFun, cueFreq, cuePhase, cueCoeff, hM, hne, ite_true, ite_false, sub_zero]
  congr 2
  ring

/-- Explicit form of the sine basis functions: for `M < i`,
`cueBasis M i x = √(2/N) sin (2π (i - M) x / N)`, `N = 2M + 1`. -/
theorem cueBasis_of_lt (M : ℕ) (i : Fin (2 * M + 1)) (hM : M < (i : ℕ)) (x : ℝ) :
    cueBasis M i x = Real.sqrt (2 / (2 * M + 1)) *
      Real.sin (2 * Real.pi * ((i : ℕ) - M : ℕ) * x / (2 * M + 1)) := by
  have hne : (i : ℕ) ≠ 0 := by omega
  have hle : ¬ (i : ℕ) ≤ M := by omega
  simp only [cueBasis, cueFun, cueFreq, cuePhase, cueCoeff, hle, hne, ite_false,
    Real.cos_sub_pi_div_two]
  congr 2
  ring

/-- Each trigonometric function `cueFun M n` is continuous on `ℝ`. -/
theorem continuous_cueFun (M n : ℕ) : Continuous (cueFun M n) := by
  unfold cueFun
  fun_prop

/-- Each basis function `cueBasis M i` is continuous on `ℝ`. -/
theorem continuous_cueBasis (M : ℕ) (i : Fin (2 * M + 1)) : Continuous (cueBasis M i) :=
  continuous_cueFun M i

/-- Each basis function `cueBasis M i` is Borel measurable. -/
theorem measurable_cueBasis (M : ℕ) (i : Fin (2 * M + 1)) : Measurable (cueBasis M i) :=
  (continuous_cueBasis M i).measurable

/-- Uniform bound: `|cueBasis M i x| ≤ 1` for all `M`, `i : Fin (2M + 1)`, `x : ℝ`
(since `1/√N ≤ 1` and `√(2/N) ≤ 1` when `M ≥ 1`). -/
theorem abs_cueBasis_le_one (M : ℕ) (i : Fin (2 * M + 1)) (x : ℝ) : |cueBasis M i x| ≤ 1 := by
  have hN : (1 : ℝ) ≤ 2 * M + 1 := by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hc : 0 ≤ cueCoeff M i ∧ cueCoeff M i ≤ 1 := by
    unfold cueCoeff
    split_ifs with h
    · refine ⟨by positivity, ?_⟩
      rw [div_le_one (by positivity)]
      exact Real.one_le_sqrt.mpr hN
    · refine ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr ?_⟩
      have hM : (1 : ℝ) ≤ M := by
        have : 1 ≤ M := by have := i.isLt; omega
        exact_mod_cast this
      rw [div_le_one (by positivity)]
      linarith
  unfold cueBasis cueFun
  rw [abs_mul, abs_of_nonneg hc.1]
  calc cueCoeff M i * |Real.cos _| ≤ cueCoeff M i * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hc.1
    _ ≤ 1 := by linarith [hc.2]

/-- Lebesgue measure of the window: `volume (cueWindow M) = N = 2M + 1`. -/
theorem volume_cueWindow (M : ℕ) : volume (cueWindow M) = ENNReal.ofReal (2 * M + 1) := by
  rw [cueWindow, Real.volume_Ico]
  congr 1
  ring

/-- Lebesgue measure restricted to the window `cueWindow M` is finite. -/
instance isFiniteMeasure_restrict_cueWindow (M : ℕ) :
    IsFiniteMeasure (volume.restrict (cueWindow M)) := by
  unfold cueWindow
  infer_instance

/-- For `m : ℤ`, `θ : ℝ` and `N = 2M + 1`,
`∫_{[-N/2, N/2)} cos (2π m x / N - θ) dx = N cos θ` if `m = 0`, and `0` otherwise
(Lebesgue measure on the window). -/
theorem integral_cos_cueWindow (M : ℕ) (m : ℤ) (θ : ℝ) :
    ∫ x in cueWindow M, Real.cos (2 * Real.pi * (m : ℝ) / (2 * M + 1) * x - θ) =
      if m = 0 then (2 * M + 1 : ℝ) * Real.cos θ else 0 := by
  have hN : (0 : ℝ) < 2 * M + 1 := by positivity
  have hle : -(2 * M + 1 : ℝ) / 2 ≤ (2 * M + 1 : ℝ) / 2 := by linarith
  rw [cueWindow, integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hle]
  split_ifs with hm
  · subst hm
    simp only [Int.cast_zero, mul_zero, zero_div, zero_mul, zero_sub, Real.cos_neg,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  · set c : ℝ := 2 * Real.pi * (m : ℝ) / (2 * M + 1) with hc
    have hm' : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
    have hc0 : c ≠ 0 := by
      rw [hc]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hm') hN.ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x => Real.sin (c * x - θ) / c)]
    · have h1 : c * ((2 * M + 1 : ℝ) / 2) = m * Real.pi := by
        rw [hc]
        field_simp
      have h2 : c * (-(2 * M + 1 : ℝ) / 2) = -(m * Real.pi) := by
        rw [neg_div, mul_neg, h1]
      simp only [h1, h2]
      rw [Real.sin_sub, Real.sin_sub, Real.sin_neg, Real.cos_neg, Real.sin_int_mul_pi]
      ring
    · intro x _
      have := (((hasDerivAt_id x).const_mul c).sub_const θ).sin.div_const c
      convert this using 1
      · rfl
      · rw [mul_one, mul_div_assoc, div_self hc0, mul_one]
        rfl
    · exact (by fun_prop : Continuous fun x => Real.cos (c * x - θ)).intervalIntegrable _ _

/-- Integrability of `cos (a x - θ)` on the window. -/
theorem integrable_cos_cueWindow (M : ℕ) (a θ : ℝ) :
    Integrable (fun x => Real.cos (a * x - θ)) (volume.restrict (cueWindow M)) :=
  Integrable.of_bound (by fun_prop : Continuous fun x => Real.cos (a * x - θ)).aestronglyMeasurable
    1 (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _)

/-- Gram entries of the trigonometric functions on the window `[-N/2, N/2)`:
`∫ cueFun M n * cueFun M n' = c_n c_{n'} / 2 *
  ([f_n = f_{n'}] N cos (θ_n - θ_{n'}) + [f_n + f_{n'} = 0] N cos (θ_n + θ_{n'}))`
with `c, f, θ` the coefficient, frequency and phase. -/
theorem integral_cueFun_mul (M n n' : ℕ) :
    ∫ x in cueWindow M, cueFun M n x * cueFun M n' x =
      cueCoeff M n * cueCoeff M n' / 2 *
        ((if ((cueFreq M n : ℤ) - cueFreq M n' : ℤ) = 0 then
            (2 * M + 1 : ℝ) * Real.cos (cuePhase M n - cuePhase M n') else 0) +
          (if ((cueFreq M n : ℤ) + cueFreq M n' : ℤ) = 0 then
            (2 * M + 1 : ℝ) * Real.cos (cuePhase M n + cuePhase M n') else 0)) := by
  have key : ∀ a b : ℝ, Real.cos a * Real.cos b = (Real.cos (a - b) + Real.cos (a + b)) / 2 := by
    intro a b
    rw [Real.cos_sub, Real.cos_add]
    ring
  have hpt : ∀ x, cueFun M n x * cueFun M n' x = cueCoeff M n * cueCoeff M n' / 2 *
      (Real.cos (2 * Real.pi * (((cueFreq M n : ℤ) - cueFreq M n' : ℤ) : ℝ) / (2 * M + 1) * x -
          (cuePhase M n - cuePhase M n')) +
        Real.cos (2 * Real.pi * (((cueFreq M n : ℤ) + cueFreq M n' : ℤ) : ℝ) / (2 * M + 1) * x -
          (cuePhase M n + cuePhase M n'))) := by
    intro x
    unfold cueFun
    set a := 2 * Real.pi * (cueFreq M n : ℝ) / (2 * M + 1) * x - cuePhase M n
    set b := 2 * Real.pi * (cueFreq M n' : ℝ) / (2 * M + 1) * x - cuePhase M n'
    have e1 : 2 * Real.pi * (((cueFreq M n : ℤ) - cueFreq M n' : ℤ) : ℝ) / (2 * M + 1) * x -
        (cuePhase M n - cuePhase M n') = a - b := by
      simp only [a, b]
      push_cast
      ring
    have e2 : 2 * Real.pi * (((cueFreq M n : ℤ) + cueFreq M n' : ℤ) : ℝ) / (2 * M + 1) * x -
        (cuePhase M n + cuePhase M n') = a + b := by
      simp only [a, b]
      push_cast
      ring
    rw [e1, e2]
    linear_combination (cueCoeff M n * cueCoeff M n') * key a b
  simp_rw [hpt]
  rw [integral_const_mul, integral_add (integrable_cos_cueWindow _ _ _)
    (integrable_cos_cueWindow _ _ _), integral_cos_cueWindow, integral_cos_cueWindow]

/-- For all `M n : ℕ`, the frequency `cueFreq M n` vanishes iff `n = 0`. -/
theorem cueFreq_eq_zero_iff (M n : ℕ) : cueFreq M n = 0 ↔ n = 0 := by
  unfold cueFreq
  split_ifs with h <;> omega

/-- For all `M n n' : ℕ`, equal frequency and equal phase force `n = n'`. -/
theorem eq_of_cueFreq_eq_of_cuePhase_eq (M n n' : ℕ) (hf : cueFreq M n = cueFreq M n')
    (hp : cuePhase M n = cuePhase M n') : n = n' := by
  have hpi : Real.pi / 2 ≠ 0 := by positivity
  unfold cueFreq at hf
  unfold cuePhase at hp
  split_ifs at hf hp with h1 h2 h2
  · exact hf
  · exact absurd hp.symm hpi
  · exact absurd hp hpi
  · omega

/-- For all `M n n' : ℕ`, distinct phases (one `0`, one `π/2`) give
`cos (cuePhase M n - cuePhase M n') = 0`. -/
theorem cos_cuePhase_sub_of_ne (M n n' : ℕ) (hp : cuePhase M n ≠ cuePhase M n') :
    Real.cos (cuePhase M n - cuePhase M n') = 0 := by
  unfold cuePhase at hp ⊢
  split_ifs at hp ⊢ with h1 h2 h2
  · exact absurd rfl hp
  · simp
  · simp
  · exact absurd rfl hp

/-- **Orthonormality.** For every `M : ℕ` and `i j : Fin (2M + 1)`,
`∫ cueBasis M i a * cueBasis M j a d(volume.restrict (cueWindow M)) = [i = j]`. -/
theorem cueBasis_orthonormal (M : ℕ) (i j : Fin (2 * M + 1)) :
    ∫ a, cueBasis M i a * cueBasis M j a ∂(volume.restrict (cueWindow M)) =
      if i = j then 1 else 0 := by
  have hN : (0 : ℝ) < 2 * M + 1 := by positivity
  unfold cueBasis
  rw [integral_cueFun_mul]
  by_cases hij : i = j
  · subst hij
    simp only [sub_self, ite_true, Real.cos_zero, mul_one]
    by_cases h0 : (i : ℕ) = 0
    · have hf : cueFreq M i = 0 := (cueFreq_eq_zero_iff M i).mpr h0
      have hs : ((cueFreq M i : ℤ) + cueFreq M i : ℤ) = 0 := by rw [hf]; rfl
      have hc : cueCoeff M i = 1 / Real.sqrt (2 * M + 1) := by simp [cueCoeff, h0]
      have hp : cuePhase M i = 0 := by simp [cuePhase, h0]
      rw [ite_eq_left hs, hc, hp, add_zero, Real.cos_zero, mul_one, div_mul_div_comm, one_mul,
        Real.mul_self_sqrt hN.le]
      field_simp
      ring
    · have hf : cueFreq M i ≠ 0 := fun h => h0 ((cueFreq_eq_zero_iff M i).mp h)
      have hs : ¬ ((cueFreq M i : ℤ) + cueFreq M i : ℤ) = 0 := by omega
      simp only [hs, ite_false, add_zero, cueCoeff, h0]
      rw [Real.mul_self_sqrt (by positivity)]
      field_simp
  · simp only [hij, ite_false]
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    have t1 : (if ((cueFreq M i : ℤ) - cueFreq M j : ℤ) = 0 then
        (2 * M + 1 : ℝ) * Real.cos (cuePhase M i - cuePhase M j) else 0) = 0 := by
      split_ifs with h
      · have hf : cueFreq M i = cueFreq M j := by omega
        have hp : cuePhase M i ≠ cuePhase M j := fun hp =>
          hne (eq_of_cueFreq_eq_of_cuePhase_eq M i j hf hp)
        rw [cos_cuePhase_sub_of_ne M i j hp, mul_zero]
      · rfl
    have t2 : (if ((cueFreq M i : ℤ) + cueFreq M j : ℤ) = 0 then
        (2 * M + 1 : ℝ) * Real.cos (cuePhase M i + cuePhase M j) else 0) = 0 := by
      split_ifs with h
      · exfalso
        have hi : cueFreq M i = 0 := by omega
        have hj : cueFreq M j = 0 := by omega
        exact hne (((cueFreq_eq_zero_iff M i).mp hi).trans ((cueFreq_eq_zero_iff M j).mp hj).symm)
      · rfl
    rw [t1, t2, add_zero, mul_zero]

/-- Reindexing `∑_{k ∈ [1, M]} h k = ∑_{k < M} h (k + 1)`. -/
theorem sum_Icc_one_eq_sum_range {R : Type*} [AddCommMonoid R] (h : ℕ → R) (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, h k = ∑ k ∈ Finset.range M, h (k + 1) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- **Dirichlet form of the kernel.** For `M : ℕ`, `N = 2M + 1` and `x y : ℝ`,
`cueKernel M x y = (1/N) * (1 + 2 * ∑_{k=1}^M cos (2π k (x - y) / N))`. -/
theorem cueKernel_eq (M : ℕ) (x y : ℝ) :
    cueKernel M x y = 1 / (2 * M + 1 : ℝ) *
      (1 + 2 * ∑ k ∈ Finset.Icc 1 M, Real.cos (2 * Real.pi * k * (x - y) / (2 * M + 1))) := by
  have hN : (0 : ℝ) < 2 * M + 1 := by positivity
  have hsq : Real.sqrt (2 / (2 * M + 1)) * Real.sqrt (2 / (2 * M + 1)) = 2 / (2 * M + 1) :=
    Real.mul_self_sqrt (by positivity)
  unfold cueKernel cueBasis
  rw [Fin.sum_univ_eq_sum_range (fun n => cueFun M n x * cueFun M n y), Finset.sum_range_succ',
    two_mul, Finset.sum_range_add, sum_Icc_one_eq_sum_range]
  have hA : ∀ k ∈ Finset.range M, cueFun M (k + 1) x * cueFun M (k + 1) y =
      2 / (2 * M + 1) * (Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) / (2 * M + 1) * x) *
        Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) / (2 * M + 1) * y)) := by
    intro k hk
    have hk' : k + 1 ≤ M := Finset.mem_range.mp hk
    simp only [cueFun, cueFreq, cuePhase, cueCoeff, hk', ite_true, Nat.add_one_ne_zero, ite_false,
      sub_zero]
    rw [mul_mul_mul_comm, hsq]
  have hB : ∀ k ∈ Finset.range M, cueFun M (M + k + 1) x * cueFun M (M + k + 1) y =
      2 / (2 * M + 1) * (Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) / (2 * M + 1) * x) *
        Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) / (2 * M + 1) * y)) := by
    intro k _
    have hk' : ¬ M + k + 1 ≤ M := by omega
    have hsub : M + k + 1 - M = k + 1 := by omega
    simp only [cueFun, cueFreq, cuePhase, cueCoeff, hk', ite_false, Nat.add_one_ne_zero, hsub,
      Real.cos_sub_pi_div_two]
    rw [mul_mul_mul_comm, hsq]
  have h0 : cueFun M 0 x * cueFun M 0 y = 1 / (2 * M + 1) := by
    simp only [cueFun, cueFreq, cuePhase, cueCoeff, ite_true, zero_le, Nat.cast_zero, mul_zero,
      zero_div, zero_mul, sub_zero, Real.cos_zero, mul_one]
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hN.le]
  rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hB, h0, ← Finset.sum_add_distrib,
    mul_add, mul_one, add_comm, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show 2 * Real.pi * ((k + 1 : ℕ) : ℝ) * (x - y) / (2 * M + 1) =
      2 * Real.pi * ((k + 1 : ℕ) : ℝ) / (2 * M + 1) * x -
        2 * Real.pi * ((k + 1 : ℕ) : ℝ) / (2 * M + 1) * y by ring, Real.cos_sub]
  field_simp

/-- Diagonal value: `cueKernel M x x = 1` for all `M : ℕ`, `x : ℝ`. -/
theorem cueKernel_self (M : ℕ) (x : ℝ) : cueKernel M x x = 1 := by
  have hN : (0 : ℝ) < 2 * M + 1 := by positivity
  rw [cueKernel_eq]
  simp only [sub_self, mul_zero, zero_div, Real.cos_zero, Finset.sum_const, Nat.card_Icc,
    nsmul_eq_mul, mul_one, Nat.add_sub_cancel]
  field_simp
  ring

/-- The kernel `(x, y) ↦ cueKernel M x y` is jointly continuous on `ℝ × ℝ`. -/
theorem continuous_cueKernel (M : ℕ) : Continuous fun p : ℝ × ℝ => cueKernel M p.1 p.2 := by
  unfold cueKernel
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((continuous_cueBasis M i).comp continuous_fst).mul
    ((continuous_cueBasis M i).comp continuous_snd)

/-- Dirichlet identity: `sin (θ/2) * (1 + 2 ∑_{k=1}^M cos (k θ)) = sin ((2M + 1) θ / 2)`
for all `M : ℕ`, `θ : ℝ`. -/
theorem sin_half_mul_dirichlet (M : ℕ) (θ : ℝ) :
    Real.sin (θ / 2) * (1 + 2 * ∑ k ∈ Finset.Icc 1 M, Real.cos (k * θ)) =
      Real.sin ((2 * M + 1) * θ / 2) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add 2, ← add_assoc, mul_add, ih]
    have h : Real.sin (θ / 2) * (2 * Real.cos (((M + 1 : ℕ) : ℝ) * θ)) =
        Real.sin (((M + 1 : ℕ) : ℝ) * θ + θ / 2) - Real.sin (((M + 1 : ℕ) : ℝ) * θ - θ / 2) := by
      rw [Real.sin_add, Real.sin_sub]
      ring
    rw [h, show ((M + 1 : ℕ) : ℝ) * θ - θ / 2 = (2 * M + 1) * θ / 2 by push_cast; ring,
      show ((M + 1 : ℕ) : ℝ) * θ + θ / 2 = (2 * ((M + 1 : ℕ) : ℝ) + 1) * θ / 2 by push_cast; ring]
    ring

/-- Closed form: `N sin (π (x - y) / N) * cueKernel M x y = sin (π (x - y))`,
`N = 2M + 1`, for all `M : ℕ`, `x y : ℝ`. -/
theorem cueKernel_mul_sin (M : ℕ) (x y : ℝ) :
    (2 * M + 1 : ℝ) * Real.sin (Real.pi * (x - y) / (2 * M + 1)) * cueKernel M x y =
      Real.sin (Real.pi * (x - y)) := by
  have hN : (0 : ℝ) < 2 * M + 1 := by positivity
  set θ : ℝ := 2 * Real.pi * (x - y) / (2 * M + 1) with hθ
  have h := sin_half_mul_dirichlet M θ
  have e1 : θ / 2 = Real.pi * (x - y) / (2 * M + 1) := by rw [hθ]; ring
  have e2 : (2 * M + 1) * θ / 2 = Real.pi * (x - y) := by rw [hθ]; field_simp
  have e3 : ∀ k : ℕ, Real.cos (k * θ) = Real.cos (2 * Real.pi * k * (x - y) / (2 * M + 1)) :=
    fun k => by rw [hθ]; ring_nf
  simp only [e1, e2, e3] at h
  rw [cueKernel_eq, ← h]
  field_simp

/-- **Pointwise convergence to the sine kernel.** For all `x y : ℝ`,
`cueKernel M x y → sineKernel x y = sinc (π (x - y))` as `M → ∞`. -/
theorem tendsto_cueKernel (x y : ℝ) :
    Tendsto (fun M : ℕ => cueKernel M x y) atTop (𝓝 (sineKernel x y)) := by
  by_cases hxy : x = y
  · subst hxy
    simp only [cueKernel_self, sineKernel, sub_self, mul_zero, Real.sinc_zero]
    exact tendsto_const_nhds
  have ht : Real.pi * (x - y) ≠ 0 := mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr hxy)
  set u : ℝ := Real.pi * (x - y) with hu
  have hNtop : Tendsto (fun M : ℕ => (2 * M + 1 : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun M => ?_) tendsto_natCast_atTop_atTop
    linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hv : Tendsto (fun M : ℕ => u / (2 * M + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hNtop
  have hden : Tendsto (fun M : ℕ => u * Real.sinc (u / (2 * M + 1))) atTop (𝓝 u) := by
    have := (Real.continuous_sinc.tendsto 0).comp hv
    rw [Real.sinc_zero] at this
    simpa using this.const_mul u
  have hden_eq : ∀ M : ℕ, u * Real.sinc (u / (2 * M + 1)) =
      (2 * M + 1 : ℝ) * Real.sin (u / (2 * M + 1)) := by
    intro M
    have hN : (0 : ℝ) < 2 * M + 1 := by positivity
    rw [Real.sinc_of_ne_zero (div_ne_zero ht hN.ne')]
    field_simp
  have hlim : Tendsto (fun M : ℕ => Real.sin u / (u * Real.sinc (u / (2 * M + 1)))) atTop
      (𝓝 (Real.sin u / u)) := tendsto_const_nhds.div hden ht
  rw [sineKernel, ← hu, Real.sinc_of_ne_zero ht]
  refine hlim.congr' ?_
  filter_upwards [hden.eventually_ne ht] with M hM
  have hk := cueKernel_mul_sin M x y
  rw [← hu] at hk
  rw [div_eq_iff hM, hden_eq, ← hk]
  ring

end BlockBand.Endpoints
