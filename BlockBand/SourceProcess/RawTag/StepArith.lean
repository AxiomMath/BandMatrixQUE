module

public import BlockBand.SourceProcess.RawTag.StepIneq
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Scalar arithmetic of the one-step recursion

Pointwise inequalities used to turn the one-step bound into `e_{l+1} ≤ e^{α/W}e_l + β/W`:
* `norm_add_pow_le`: `‖u+v‖^N ≤ (1+ε)^{N-1}‖u‖^N + (1+ε⁻¹)^{N-1}‖v‖^N`;
* `step_pointwise_scalar`: `(1 + K/W)‖x+μ‖^{4m} ≤ e^{(K+4m)/W}‖x‖^{4m} + c₃W⁻¹Z^{4m}` when
  `‖μ‖ ≤ C_m Z/W`, `c₃ = (1+K)2^{4m}C_m^{4m}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

/-- Convexity of `t ↦ t^N` with weights `1/(1+ε)`, `ε/(1+ε)`. -/
theorem add_pow_le_weighted {a c ε : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hε : 0 < ε) (N : ℕ) :
    (a + c) ^ N ≤ (1 + ε) ^ (N - 1) * a ^ N + (1 + ε⁻¹) ^ (N - 1) * c ^ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set u := 1 + ε
  set v := 1 + ε⁻¹
  have hu : 0 < u := by positivity
  have hv : 0 < v := by positivity
  have hsum : u⁻¹ + v⁻¹ = 1 := by simp only [u, v]; field_simp; ring
  have hconv := (convexOn_pow (k + 1)).2 (Set.mem_Ici.mpr (by positivity : 0 ≤ a * u))
    (Set.mem_Ici.mpr (by positivity : 0 ≤ c * v)) (inv_nonneg.mpr hu.le) (inv_nonneg.mpr hv.le)
    hsum
  simp only [smul_eq_mul] at hconv
  have e1 : u⁻¹ * (a * u) + v⁻¹ * (c * v) = a + c := by field_simp
  rw [e1] at hconv
  refine hconv.trans (le_of_eq ?_)
  have e2 : ∀ (w y : ℝ), 0 < w → w⁻¹ * (y * w) ^ (k + 1) = w ^ k * y ^ (k + 1) := by
    intro w y hw
    rw [mul_pow, pow_succ w]
    field_simp
  rw [e2 u a hu, e2 v c hv]

theorem norm_add_pow_le (u v : ℂ) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ‖u + v‖ ^ N ≤ (1 + ε) ^ (N - 1) * ‖u‖ ^ N + (1 + ε⁻¹) ^ (N - 1) * ‖v‖ ^ N :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le u v) N).trans
    (add_pow_le_weighted (norm_nonneg _) (norm_nonneg _) hε N)

theorem one_add_le_exp' (x : ℝ) : 1 + x ≤ Real.exp x := by
  have := Real.add_one_le_exp x; linarith

/-- **The pointwise scalar step.** -/
theorem step_pointwise_scalar {x μ : ℂ} {K Cm Z W : ℝ} {m : ℕ} (hm : 1 ≤ m) (hK : 0 ≤ K)
    (hCm : 0 ≤ Cm) (hZ : 0 ≤ Z) (hW : 1 ≤ W) (hμ : ‖μ‖ ≤ Cm * Z / W) :
    (1 + K / W) * (‖x + μ‖ ^ 2) ^ (2 * m) ≤
      Real.exp ((K + 4 * m) / W) * (‖x‖ ^ 2) ^ (2 * m) +
        (1 + K) * 2 ^ (4 * m) * Cm ^ (4 * m) / W * Z ^ (4 * m) := by
  have hW0 : 0 < W := by linarith
  have e2 : ∀ y : ℂ, (‖y‖ ^ 2) ^ (2 * m) = ‖y‖ ^ (4 * m) := fun y => by
    rw [← pow_mul]; ring_nf
  rw [e2, e2]
  set N := 4 * m
  have hN : 1 ≤ N := by omega
  have hc := norm_add_pow_le x μ (inv_pos.mpr hW0) N
  rw [inv_inv] at hc
  have hKW : 0 ≤ K / W := by positivity
  -- first coefficient
  have h1 : (1 + K / W) * (1 + W⁻¹) ^ (N - 1) ≤ Real.exp ((K + 4 * m) / W) := by
    have a1 := one_add_le_exp' (K / W)
    have a2 : (1 + W⁻¹) ^ (N - 1) ≤ Real.exp (W⁻¹) ^ (N - 1) :=
      pow_le_pow_left₀ (by positivity) (one_add_le_exp' _) _
    rw [← Real.exp_nat_mul] at a2
    calc (1 + K / W) * (1 + W⁻¹) ^ (N - 1) ≤ Real.exp (K / W) * Real.exp (↑(N - 1) * W⁻¹) :=
          mul_le_mul a1 a2 (by positivity) (Real.exp_pos _).le
      _ = Real.exp (K / W + ↑(N - 1) * W⁻¹) := (Real.exp_add _ _).symm
      _ ≤ _ := by
          refine Real.exp_le_exp.mpr ?_
          have : ((N - 1 : ℕ) : ℝ) ≤ 4 * m := by
            have : (N - 1 : ℕ) ≤ 4 * m := by omega
            exact_mod_cast this
          rw [add_div, div_eq_mul_inv K, div_eq_mul_inv (4 * (m : ℝ))]
          nlinarith [inv_pos.mpr hW0]
  -- second coefficient
  have h2 : (1 + K / W) * ((1 + W) ^ (N - 1) * ‖μ‖ ^ N) ≤
      (1 + K) * 2 ^ (4 * m) * Cm ^ (4 * m) / W * Z ^ (4 * m) := by
    have b1 : 1 + K / W ≤ 1 + K := by
      have : K / W ≤ K := div_le_self hK hW
      linarith
    have b2 : (1 + W) ^ (N - 1) ≤ (2 * W) ^ (N - 1) := pow_le_pow_left₀ (by positivity)
      (by linarith) _
    have b3 : ‖μ‖ ^ N ≤ (Cm * Z / W) ^ N := pow_le_pow_left₀ (norm_nonneg _) hμ _
    have b4 : (2 * W) ^ (N - 1) * (Cm * Z / W) ^ N = 2 ^ (N - 1) * Cm ^ N / W * Z ^ N := by
      have hWn : W ^ N = W ^ (N - 1) * W := by rw [← pow_succ, Nat.sub_add_cancel hN]
      rw [mul_pow, div_pow, mul_pow, hWn]
      field_simp
    have b5 : (2 : ℝ) ^ (N - 1) ≤ 2 ^ (4 * m) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc (1 + K / W) * ((1 + W) ^ (N - 1) * ‖μ‖ ^ N)
        ≤ (1 + K) * ((2 * W) ^ (N - 1) * (Cm * Z / W) ^ N) := by
          refine mul_le_mul b1 (mul_le_mul b2 b3 (by positivity) (by positivity)) (by positivity)
            (by positivity)
      _ = (1 + K) * (2 ^ (N - 1) * Cm ^ N / W * Z ^ N) := by rw [b4]
      _ ≤ _ := by
          have : 2 ^ (N - 1) * Cm ^ N / W * Z ^ N ≤
              2 ^ (4 * m) * Cm ^ (4 * m) / W * Z ^ (4 * m) := by
            have hpos : 0 ≤ Cm ^ N / W * Z ^ N := by positivity
            calc 2 ^ (N - 1) * Cm ^ N / W * Z ^ N = 2 ^ (N - 1) * (Cm ^ N / W * Z ^ N) := by ring
              _ ≤ 2 ^ (4 * m) * (Cm ^ N / W * Z ^ N) := mul_le_mul_of_nonneg_right b5 hpos
              _ = _ := by ring
          calc (1 + K) * (2 ^ (N - 1) * Cm ^ N / W * Z ^ N)
              ≤ (1 + K) * (2 ^ (4 * m) * Cm ^ (4 * m) / W * Z ^ (4 * m)) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring
  have hx0 : 0 ≤ ‖x‖ ^ N := by positivity
  calc (1 + K / W) * ‖x + μ‖ ^ N
      ≤ (1 + K / W) * ((1 + W⁻¹) ^ (N - 1) * ‖x‖ ^ N + (1 + W) ^ (N - 1) * ‖μ‖ ^ N) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = (1 + K / W) * (1 + W⁻¹) ^ (N - 1) * ‖x‖ ^ N +
        (1 + K / W) * ((1 + W) ^ (N - 1) * ‖μ‖ ^ N) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right h1 hx0) h2

end BlockBand.SourceProcess.RawTag
