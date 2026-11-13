module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Real analysis for the conductance moment recursion

Young's inequality with integer powers, the moment expansion of a bounded variable about its mean,
and a logistic comparison for recursive moment bounds.

* `young_pow`: `a^n b ≤ t a^{n+1} + b^{n+1}/t^n` for `a, b ≥ 0`, `t > 0` (integer-power Young).
* `integral_pow_le_of_fluct`: on a probability space, for `0 ≤ Y ≤ M` a.s., `m = E Y` and
  `‖Y - m‖_n ≤ σ`: `E Y^n ≤ m^n + Σ_{k=2}^n C(n,k) m^{n-k} σ^k` (binomial expansion about the
  mean; the linear term vanishes).
* `logistic_bound`: if `x_{r+1} ≤ x_r(1 - cl/W) + (cl^{n+1} + D)/W` for every `l ≥ 0` and
  `1 ≤ r < N`, `x ≥ 0` and `x_1 ≤ K₀(1+W)^n`, then `x_r ≤ K(1 + W/r)^n` for `1 ≤ r ≤ N`, with
  `K = K(n, c, D, K₀)` (the choice `l = (2n/c)(1 + W/r)` linearizes the logistic comparison).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Finset
open scoped ENNReal

/-!
## Young
-/

/-- Young-type bound with integer powers. -/
theorem young_pow (n : ℕ) {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t) :
    a ^ n * b ≤ t * a ^ (n + 1) + b ^ (n + 1) / t ^ n := by
  have h1 : 0 ≤ t * a ^ (n + 1) := by positivity
  have h2 : 0 ≤ b ^ (n + 1) / t ^ n := by positivity
  rcases le_or_gt b (t * a) with h | h
  · have : a ^ n * b ≤ a ^ n * (t * a) := mul_le_mul_of_nonneg_left h (by positivity)
    have e : a ^ n * (t * a) = t * a ^ (n + 1) := by ring
    linarith
  · have hab : a ≤ b / t := by rw [le_div_iff₀ ht]; linarith
    have hp : a ^ n ≤ (b / t) ^ n := pow_le_pow_left₀ ha hab n
    have : a ^ n * b ≤ (b / t) ^ n * b := mul_le_mul_of_nonneg_right hp hb
    have e : (b / t) ^ n * b = b ^ (n + 1) / t ^ n := by rw [div_pow]; ring
    linarith

/-!
## The moment expansion
-/

/-- Moment of a bounded variable around its mean. On a probability space, for
`0 ≤ Y ≤ M`, `m = E Y`, `‖Y - m‖_n ≤ σ`: `E Y^n ≤ m^n + Σ_{k=2}^n C(n,k) m^{n-k} σ^k`. -/
theorem integral_pow_le_of_fluct {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n : ℕ) {Y : Ω → ℝ} (hY : Measurable Y) {M σ : ℝ}
    (hY0 : ∀ᵐ ω ∂μ, 0 ≤ Y ω) (hYM : ∀ᵐ ω ∂μ, Y ω ≤ M) (hσ : 0 ≤ σ)
    (hfl : eLpNorm (fun ω => Y ω - ∫ ω', Y ω' ∂μ) n μ ≤ ENNReal.ofReal σ) :
    ∫ ω, Y ω ^ n ∂μ ≤ (∫ ω, Y ω ∂μ) ^ n +
      ∑ k ∈ Finset.Icc 2 n, (n.choose k : ℝ) * (∫ ω, Y ω ∂μ) ^ (n - k) * σ ^ k := by
  set m := ∫ ω, Y ω ∂μ with hm
  have hm0 : 0 ≤ m := integral_nonneg_of_ae hY0
  set Z : Ω → ℝ := fun ω => Y ω - m with hZ
  have hZm : Measurable Z := hY.sub measurable_const
  have hZb : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ M + m := by
    filter_upwards [hY0, hYM] with ω h0 hM
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> simp only [hZ] <;> linarith
  have hint : ∀ k : ℕ, Integrable (fun ω => Z ω ^ k) μ := fun k =>
    Integrable.of_bound (hZm.pow_const k).aestronglyMeasurable ((M + m) ^ k)
      (hZb.mono fun ω h => by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h k)
  have hYi : Integrable Y μ := by
    refine ((hint 1).add (integrable_const m)).congr (ae_of_all _ fun ω => ?_)
    simp [hZ]
  have hZ1 : ∫ ω, Z ω ∂μ = 0 := by
    simp only [hZ]
    rw [integral_sub hYi (integrable_const m), integral_const, probReal_univ, one_smul, sub_self]
  have hmom : ∀ k : ℕ, 1 ≤ k → k ≤ n → ∫ ω, Z ω ^ k ∂μ ≤ σ ^ k := by
    intro k hk hkn
    have hmem : MemLp Z k μ := MemLp.of_bound hZm.aestronglyMeasurable (M + m) hZb
    have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hle : eLpNorm Z k μ ≤ ENNReal.ofReal σ :=
      (eLpNorm_le_eLpNorm_of_exponent_le (by exact_mod_cast hkn)).trans hfl
    rw [hmem.eLpNorm_eq_integral_rpow_norm hk0 ENNReal.coe_ne_top] at hle
    rw [ENNReal.ofReal_le_ofReal_iff hσ] at hle
    have hkr : ((k : ℝ≥0∞)).toReal = (k : ℝ) := by simp
    rw [hkr] at hle
    set I := ∫ a, ‖Z a‖ ^ (k : ℝ) ∂μ with hI
    have hI0 : 0 ≤ I := integral_nonneg fun _ => by positivity
    have hIk : I ≤ σ ^ k := by
      have h' := pow_le_pow_left₀ (by positivity) hle k
      rwa [← Real.rpow_natCast, ← Real.rpow_mul hI0, inv_mul_cancel₀ (by exact_mod_cast
        (show k ≠ 0 by omega)), Real.rpow_one] at h'
    have hIeq : I = ∫ a, ‖Z a ^ k‖ ∂μ := by
      simp only [hI, Real.rpow_natCast, norm_pow]
    calc ∫ ω, Z ω ^ k ∂μ ≤ ‖∫ ω, Z ω ^ k ∂μ‖ := Real.le_norm_self _
      _ ≤ ∫ a, ‖Z a ^ k‖ ∂μ := norm_integral_le_integral_norm _
      _ = I := hIeq.symm
      _ ≤ σ ^ k := hIk
  have hexp : (fun ω => Y ω ^ n) =
      fun ω => ∑ k ∈ range (n + 1), Z ω ^ k * m ^ (n - k) * (n.choose k : ℝ) := by
    funext ω
    rw [← add_pow]; simp [hZ]
  rw [hexp, integral_finsetSum _ (fun k _ => ((hint k).mul_const _).mul_const _)]
  simp_rw [integral_mul_const]
  rcases n with _ | j
  · simp
  rw [sum_range_succ', sum_range_succ']
  have h0 : ∫ ω, Z ω ^ 0 ∂μ = 1 := by simp
  simp only [zero_add, h0, pow_one, hZ1, Nat.choose_zero_right, Nat.choose_one_right]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    show j + 1 + 1 - 2 = j by omega]
  have hsum : ∑ i ∈ range j, (∫ ω, Z ω ^ (i + 1 + 1) ∂μ) * m ^ (j + 1 - (i + 1 + 1)) *
      ((j + 1).choose (i + 1 + 1) : ℝ) ≤
      ∑ k ∈ range j, ((j + 1).choose (2 + k) : ℝ) * m ^ (j + 1 - (2 + k)) * σ ^ (2 + k) := by
    refine sum_le_sum fun i hi => ?_
    have hi' : i < j := mem_range.mp hi
    rw [show i + 1 + 1 = 2 + i by ring]
    have := hmom (2 + i) (by omega) (by omega)
    have hc : (0 : ℝ) ≤ ((j + 1).choose (2 + i) : ℝ) * m ^ (j + 1 - (2 + i)) := by positivity
    nlinarith
  simp only [zero_mul, add_zero, one_mul, Nat.cast_one, mul_one, Nat.sub_zero]
  linarith

/-!
## The logistic comparison
-/

theorem ma_pow_sub_pow_le (m : ℕ) {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) :
    a ^ (m + 1) - b ^ (m + 1) ≤ (m + 1) * a ^ m * (a - b) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ha : 0 ≤ a := hb.trans hab
    have hpow : b ^ (m + 1) ≤ a ^ (m + 1) := pow_le_pow_left₀ hb hab _
    have hd : 0 ≤ a - b := by linarith
    have e : a ^ (m + 1 + 1) - b ^ (m + 1 + 1) =
        a * (a ^ (m + 1) - b ^ (m + 1)) + b ^ (m + 1) * (a - b) := by ring
    have t1 : a * (a ^ (m + 1) - b ^ (m + 1)) ≤ a * ((m + 1) * a ^ m * (a - b)) :=
      mul_le_mul_of_nonneg_left ih ha
    have t2 : b ^ (m + 1) * (a - b) ≤ a ^ (m + 1) * (a - b) := mul_le_mul_of_nonneg_right hpow hd
    rw [e]
    calc a * (a ^ (m + 1) - b ^ (m + 1)) + b ^ (m + 1) * (a - b)
        ≤ a * ((m + 1) * a ^ m * (a - b)) + a ^ (m + 1) * (a - b) := add_le_add t1 t2
      _ = ((m + 1 : ℕ) + 1 : ℝ) * a ^ (m + 1) * (a - b) := by push_cast; ring

/-- One step of the comparison with `l = (2n/c)v`. -/
theorem ma_step {n : ℕ} (hn : 1 ≤ n) {c D K W v v' x x' : ℝ} (hc : 0 < c) (hD : 0 ≤ D)
    (hW : 1 ≤ W) (hv' : 1 ≤ v') (hv'v : v' ≤ v) (hvW : v ≤ 2 * W) (hvv : v ≤ 2 * v')
    (hdiff : v ^ n - v' ^ n ≤ n * v ^ (n + 1) / W)
    (hK : 2 ^ (n + 1) * c * (2 * n / c) ^ (n + 1) + D ≤ K) (hx : 0 ≤ x)
    (hxK : x ≤ K * v ^ n)
    (hrec : x' ≤ x * (1 - c * ((2 * n / c) * v) / W) +
      (c * ((2 * n / c) * v) ^ (n + 1) + D) / W) :
    x' ≤ K * v' ^ n := by
  have hW0 : 0 < W := by linarith
  have hv1 : 1 ≤ v := hv'.trans hv'v
  have hv0 : 0 ≤ v := by linarith
  set μ := 2 * (n : ℝ) / c with hμ
  set A := c * μ ^ (n + 1) with hA
  have hA0 : 0 ≤ A := by positivity
  set P := v ^ (n + 1) / W with hP
  have hP0 : 0 ≤ P := by positivity
  have hpn : 0 ≤ v' ^ n := by positivity
  have hcμ : c * (μ * v) = 2 * n * v := by rw [hμ]; field_simp
  have hrecA : (c * (μ * v) ^ (n + 1) + D) / W = A * P + D / W := by
    rw [hA, hP, mul_pow]; ring
  have h2 : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
  have hAK : A + D ≤ K := by
    have : A ≤ 2 ^ (n + 1) * c * μ ^ (n + 1) := by
      rw [hA, mul_assoc]; exact le_mul_of_one_le_left (by positivity) h2
    linarith
  have hK0 : 0 ≤ K := by linarith
  rw [hrecA] at hrec
  by_cases hcoef : 0 ≤ 1 - c * (μ * v) / W
  · have t1 : x * (1 - c * (μ * v) / W) ≤ K * v ^ n * (1 - c * (μ * v) / W) :=
      mul_le_mul_of_nonneg_right hxK hcoef
    have e1 : K * v ^ n * (1 - c * (μ * v) / W) = K * v ^ n - 2 * n * K * P := by
      rw [hcμ, hP, pow_succ]; field_simp
    have hvp : 1 ≤ v ^ (n + 1) := one_le_pow₀ hv1
    have tD : D / W ≤ D * P := by
      rw [hP, mul_div_assoc']
      exact div_le_div_of_nonneg_right (le_mul_of_one_le_right hD hvp) hW0.le
    have t3 : (A + D) * P ≤ K * P := mul_le_mul_of_nonneg_right hAK hP0
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have t4 : K * P ≤ n * K * P := by
      have : K ≤ n * K := le_mul_of_one_le_left hK0 hn'
      exact mul_le_mul_of_nonneg_right this hP0
    have t5 : K * (v ^ n - v' ^ n) ≤ K * (n * v ^ (n + 1) / W) := mul_le_mul_of_nonneg_left hdiff hK0
    have e5 : K * (n * v ^ (n + 1) / W) = n * K * P := by rw [hP]; ring
    nlinarith
  · push Not at hcoef
    have t1 : x * (1 - c * (μ * v) / W) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx hcoef.le
    have hvW' : v / W ≤ 2 := by rw [div_le_iff₀ hW0]; linarith
    have hvn : v ^ n ≤ 2 ^ n * v' ^ n := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hv0 hvv n
    have hPb : P ≤ 2 ^ (n + 1) * v' ^ n := by
      have e : P = v ^ n * (v / W) := by rw [hP, pow_succ]; ring
      rw [e]
      calc v ^ n * (v / W) ≤ (2 ^ n * v' ^ n) * 2 :=
            mul_le_mul hvn hvW' (by positivity) (by positivity)
        _ = 2 ^ (n + 1) * v' ^ n := by ring
    have tA : A * P ≤ A * (2 ^ (n + 1) * v' ^ n) := mul_le_mul_of_nonneg_left hPb hA0
    have tD : D / W ≤ D * v' ^ n := by
      calc D / W ≤ D := div_le_self hD hW
        _ ≤ D * v' ^ n := le_mul_of_one_le_right hD (one_le_pow₀ hv')
    have tK : (2 ^ (n + 1) * c * μ ^ (n + 1) + D) * v' ^ n ≤ K * v' ^ n :=
      mul_le_mul_of_nonneg_right hK hpn
    have eA : A * (2 ^ (n + 1) * v' ^ n) = 2 ^ (n + 1) * c * μ ^ (n + 1) * v' ^ n := by
      rw [hA]; ring
    nlinarith

/-- Logistic comparison: the recursion `x_{r+1} ≤ x_r(1 - cl/W) + (cl^{n+1} + D)/W` gives
`x_r ≤ K(1 + W/r)^n`. -/
theorem logistic_bound (n : ℕ) (hn : 1 ≤ n) {c D K₀ : ℝ} (hc : 0 < c) (hD : 0 ≤ D)
    (hK₀ : 0 ≤ K₀) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (W : ℝ), 1 ≤ W → ∀ (x : ℕ → ℝ) (N : ℕ),
      (∀ r, 0 ≤ x r) → x 1 ≤ K₀ * (1 + W) ^ n →
      (∀ r, 1 ≤ r → r < N → ∀ l : ℝ, 0 ≤ l →
        x (r + 1) ≤ x r * (1 - c * l / W) + (c * l ^ (n + 1) + D) / W) →
      ∀ r, 1 ≤ r → r ≤ N → x r ≤ K * (1 + W / r) ^ n := by
  set K := max K₀ (2 ^ (n + 1) * c * (2 * n / c) ^ (n + 1) + D)
  refine ⟨K, le_max_of_le_left hK₀, fun W hW x N hx0 hx1 hrec r hr hrN => ?_⟩
  have hW0 : 0 ≤ W := by linarith
  induction r, hr using Nat.le_induction with
  | base =>
    calc x 1 ≤ K₀ * (1 + W) ^ n := hx1
      _ ≤ K * (1 + W) ^ n := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = K * (1 + W / ((1 : ℕ) : ℝ)) ^ n := by simp
  | succ r hr ih =>
    have ih' := ih (by omega)
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hr0 : (0 : ℝ) < r := by linarith
    have hcast : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    set v := 1 + W / r with hv
    set v' := 1 + W / ((r : ℝ) + 1) with hv'
    have hl : 0 ≤ 2 * (n : ℝ) / c * v := by
      have : 0 ≤ W / r := div_nonneg hW0 hr0.le
      positivity
    refine ma_step hn hc hD hW ?_ ?_ ?_ ?_ ?_ (le_max_right _ _) (hx0 r)
      (ih'.trans (le_of_eq rfl)) (hrec r hr (by omega) _ hl)
    · have : 0 ≤ W / ((r : ℝ) + 1) := div_nonneg hW0 (by linarith)
      linarith
    · have : W / ((r : ℝ) + 1) ≤ W / r := div_le_div_of_nonneg_left hW0 hr0 (by linarith)
      linarith
    · have : W / r ≤ W := div_le_self hW0 hr1
      linarith
    · have : W / r ≤ 2 * (W / ((r : ℝ) + 1)) := by
        rw [mul_div_assoc', div_le_div_iff₀ hr0 (by linarith)]
        nlinarith
      linarith
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hvv' : v' ≤ v := by
        have : W / ((r : ℝ) + 1) ≤ W / r := div_le_div_of_nonneg_left hW0 hr0 (by linarith)
        linarith
      have hv'0 : 0 ≤ v' := by
        have : 0 ≤ W / ((r : ℝ) + 1) := div_nonneg hW0 (by linarith)
        linarith
      have h1 := ma_pow_sub_pow_le m hv'0 hvv'
      have hWpos : 0 < W := by linarith
      have hd : v - v' ≤ v ^ 2 / W := by
        have e : v - v' = W / (r * (r + 1)) := by
          rw [hv, hv']; field_simp; ring
        have e2 : (W / r) ^ 2 / W = W / (r * r) := by field_simp
        have t1 : W / (r * (r + 1)) ≤ W / (r * r) :=
          div_le_div_of_nonneg_left hW0 (by positivity) (by nlinarith)
        have t2 : (W / r) ^ 2 / W ≤ v ^ 2 / W := by
          refine div_le_div_of_nonneg_right ?_ hWpos.le
          have : 0 ≤ W / r := div_nonneg hW0 hr0.le
          rw [hv]; nlinarith
        linarith
      have hvm : 0 ≤ ((m : ℝ) + 1) * v ^ m := by
        have : 0 ≤ v := hv'0.trans hvv'
        positivity
      calc v ^ (m + 1) - v' ^ (m + 1) ≤ (m + 1) * v ^ m * (v - v') := h1
        _ ≤ (m + 1) * v ^ m * (v ^ 2 / W) := mul_le_mul_of_nonneg_left hd hvm
        _ = ((m + 1 : ℕ) : ℝ) * v ^ (m + 1 + 1) / W := by push_cast; ring

end BlockBand.Transmission.SourceMixing
