module

public import BlockBand.Critical.RelativeVectors.CrossBound

/-!
# The cross window bound in terms of row tails

`crossBoundFun_le`: if every row of `A` has Euclidean norm `≤ 1` and `|c_ij| ≤ c̄` for
`|i - j| ≥ ℓ`, then
`crossBoundFun ≤ B √2 c̄ + Z² c̄ N (√T_m + √T_{m'})`, `T_m = Σ_{j ∉ J} |A_{ι m, j}|²`
(the window part `B (Σ|Θ|² + |ΘΘ|)^{1/2} ≤ √2 B c̄`; the exterior part by Cauchy–Schwarz).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission

variable {N k : ℕ}

/-- Row tail `T = Σ_{j ∉ J} |A_{a j}|²`. -/
def rowTail (A : Matrix (Fin N) (Fin N) ℂ) (J : Finset (Fin N)) (a : Fin N) : ℝ :=
  ∑ j, if j ∈ J then 0 else ‖A a j‖ ^ 2

theorem rowTail_nonneg (A : Matrix (Fin N) (Fin N) ℂ) (J : Finset (Fin N)) (a : Fin N) :
    0 ≤ rowTail A J a :=
  Finset.sum_nonneg fun j _ => by split_ifs <;> positivity

/-- `Σ_j x_j ≤ √N (Σ_j x_j²)^{1/2}` for `x ≥ 0`. -/
theorem sum_le_sqrt_card_mul (x : Fin N → ℝ) :
    ∑ j, x j ≤ Real.sqrt N * Real.sqrt (∑ j, x j ^ 2) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg N)]
  refine Real.le_sqrt_of_sq_le ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ (fun _ => (1 : ℝ)) x
  simpa using h

theorem norm_crossTheta_le_row (ι : Fin k → Fin N) (lam : Fin N → ℝ) (ℓ : ℕ)
    (A : Matrix (Fin N) (Fin N) ℂ) {cbar : ℝ} (hc0 : 0 ≤ cbar)
    (hc : ∀ i j, ℓ ≤ labelDist i j → |dysonCoupling N lam i j| ≤ cbar) (m m' : Fin k)
    (i j : Fin N) :
    ‖crossTheta ι lam ℓ A m m' i j‖ ≤ cbar * (‖A (ι m) i‖ * ‖A (ι m') j‖) := by
  unfold crossTheta
  split_ifs with h
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_right (hc i j h.2) (by positivity)
  · simp only [norm_zero]; positivity

/-- **The cross window bound in terms of row tails.** See the module docstring. -/
theorem crossBoundFun_le (ι : Fin k → Fin N) (lam : Fin N → ℝ) (ℓ : ℕ) (J : Finset (Fin N))
    {B Z : ℝ} (hB : 0 ≤ B) (A : Matrix (Fin N) (Fin N) ℂ) (hrow : ∀ a, ∑ b, ‖A a b‖ ^ 2 ≤ 1)
    {cbar : ℝ} (hc0 : 0 ≤ cbar) (hc : ∀ i j, ℓ ≤ labelDist i j → |dysonCoupling N lam i j| ≤ cbar)
    (m m' : Fin k) :
    crossBoundFun ι lam ℓ J B Z A m m' ≤
      B * (Real.sqrt 2 * cbar) + Z * Z * (cbar * N *
        (Real.sqrt (rowTail A J (ι m)) + Real.sqrt (rowTail A J (ι m')))) := by
  set a : Fin N → ℝ := fun i => ‖A (ι m) i‖
  set b : Fin N → ℝ := fun j => ‖A (ι m') j‖
  have ha2 : ∑ i, a i ^ 2 ≤ 1 := hrow _
  have hb2 : ∑ j, b j ^ 2 ≤ 1 := hrow _
  have hθ := norm_crossTheta_le_row ι lam ℓ A hc0 hc m m'
  -- window part
  have hsq : ∑ i, ∑ j, (‖crossTheta ι lam ℓ A m m' i j‖ ^ 2 +
      ‖crossTheta ι lam ℓ A m m' i j * crossTheta ι lam ℓ A m m' j i‖) ≤ 2 * cbar ^ 2 := by
    have h1 : ∑ i, ∑ j, ‖crossTheta ι lam ℓ A m m' i j‖ ^ 2 ≤ cbar ^ 2 := by
      calc ∑ i, ∑ j, ‖crossTheta ι lam ℓ A m m' i j‖ ^ 2
          ≤ ∑ i, ∑ j, cbar ^ 2 * (a i ^ 2 * b j ^ 2) := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            calc ‖crossTheta ι lam ℓ A m m' i j‖ ^ 2 ≤ (cbar * (a i * b j)) ^ 2 :=
                  pow_le_pow_left₀ (norm_nonneg _) (hθ i j) 2
              _ = _ := by ring
        _ = cbar ^ 2 * ((∑ i, a i ^ 2) * (∑ j, b j ^ 2)) := by
            rw [Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
        _ ≤ cbar ^ 2 * (1 * 1) := by
            gcongr
        _ = cbar ^ 2 := by ring
    have h2 : ∑ i, ∑ j, ‖crossTheta ι lam ℓ A m m' i j * crossTheta ι lam ℓ A m m' j i‖ ≤
        cbar ^ 2 := by
      calc ∑ i, ∑ j, ‖crossTheta ι lam ℓ A m m' i j * crossTheta ι lam ℓ A m m' j i‖
          ≤ ∑ i, ∑ j, cbar ^ 2 * ((a i * b i) * (a j * b j)) := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            rw [norm_mul]
            calc ‖crossTheta ι lam ℓ A m m' i j‖ * ‖crossTheta ι lam ℓ A m m' j i‖
                ≤ (cbar * (a i * b j)) * (cbar * (a j * b i)) :=
                  mul_le_mul (hθ i j) (hθ j i) (norm_nonneg _) (by positivity)
              _ = _ := by ring
        _ = cbar ^ 2 * (∑ i, a i * b i) ^ 2 := by
            rw [sq (∑ i, a i * b i), Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
        _ ≤ cbar ^ 2 * ((∑ i, a i ^ 2) * (∑ i, b i ^ 2)) :=
            mul_le_mul_of_nonneg_left (Finset.sum_mul_sq_le_sq_mul_sq univ a b) (by positivity)
        _ ≤ cbar ^ 2 * (1 * 1) := by
            gcongr
        _ = cbar ^ 2 := by ring
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib, Finset.sum_add_distrib]
    linarith
  have hw : Real.sqrt (∑ i, ∑ j, (‖crossTheta ι lam ℓ A m m' i j‖ ^ 2 +
      ‖crossTheta ι lam ℓ A m m' i j * crossTheta ι lam ℓ A m m' j i‖)) ≤ Real.sqrt 2 * cbar := by
    rw [← Real.sqrt_sq hc0, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  -- exterior part
  have hsa : ∑ i, a i ≤ Real.sqrt N := by
    refine (sum_le_sqrt_card_mul a).trans ?_
    calc Real.sqrt N * Real.sqrt (∑ i, a i ^ 2) ≤ Real.sqrt N * 1 := by
          gcongr; exact Real.sqrt_le_one.mpr ha2
      _ = Real.sqrt N := mul_one _
  have hsb : ∑ j, b j ≤ Real.sqrt N := by
    refine (sum_le_sqrt_card_mul b).trans ?_
    calc Real.sqrt N * Real.sqrt (∑ j, b j ^ 2) ≤ Real.sqrt N * 1 := by
          gcongr; exact Real.sqrt_le_one.mpr hb2
      _ = Real.sqrt N := mul_one _
  have hta : ∑ i, (if i ∈ J then 0 else a i) ≤ Real.sqrt N * Real.sqrt (rowTail A J (ι m)) := by
    refine (sum_le_sqrt_card_mul _).trans (le_of_eq ?_)
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp [a]
  have htb : ∑ j, (if j ∈ J then 0 else b j) ≤ Real.sqrt N * Real.sqrt (rowTail A J (ι m')) := by
    refine (sum_le_sqrt_card_mul _).trans (le_of_eq ?_)
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [b]
  have hext : ∑ i, ∑ j, (if i ∈ J ∧ j ∈ J then 0 else ‖crossTheta ι lam ℓ A m m' i j‖) ≤
      cbar * N * (Real.sqrt (rowTail A J (ι m)) + Real.sqrt (rowTail A J (ι m'))) := by
    have hpt : ∀ i j, (if i ∈ J ∧ j ∈ J then 0 else ‖crossTheta ι lam ℓ A m m' i j‖) ≤
        cbar * ((if i ∈ J then 0 else a i) * b j + a i * (if j ∈ J then 0 else b j)) := by
      intro i j
      have ha0 : 0 ≤ a i := norm_nonneg _
      have hb0 : 0 ≤ b j := norm_nonneg _
      by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
      · simp [hi, hj]
      · simp only [hi, hj, and_false, ite_false, ite_true, zero_mul, zero_add]
        exact hθ i j
      · simp only [hi, hj, false_and, ite_false, ite_true, mul_zero, add_zero]
        exact hθ i j
      · simp only [hi, hj, and_self, ite_false]
        calc ‖crossTheta ι lam ℓ A m m' i j‖ ≤ cbar * (a i * b j) := hθ i j
          _ ≤ cbar * (a i * b j + a i * b j) := by
              gcongr; linarith [mul_nonneg ha0 hb0]
    have hN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
    calc ∑ i, ∑ j, (if i ∈ J ∧ j ∈ J then 0 else ‖crossTheta ι lam ℓ A m m' i j‖)
        ≤ ∑ i, ∑ j, cbar * ((if i ∈ J then 0 else a i) * b j +
            a i * (if j ∈ J then 0 else b j)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
      _ = cbar * ((∑ i, (if i ∈ J then 0 else a i)) * (∑ j, b j) +
            (∑ i, a i) * (∑ j, (if j ∈ J then 0 else b j))) := by
          rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ cbar * ((Real.sqrt N * Real.sqrt (rowTail A J (ι m))) * Real.sqrt N +
            Real.sqrt N * (Real.sqrt N * Real.sqrt (rowTail A J (ι m')))) := by
          have h0a : 0 ≤ ∑ i, (if i ∈ J then 0 else a i) :=
            Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
          have h0b : 0 ≤ ∑ j, b j := Finset.sum_nonneg fun j _ => norm_nonneg _
          gcongr
      _ = cbar * N * (Real.sqrt (rowTail A J (ι m)) + Real.sqrt (rowTail A J (ι m'))) := by
          have e : cbar * ((Real.sqrt N * Real.sqrt (rowTail A J (ι m))) * Real.sqrt N +
              Real.sqrt N * (Real.sqrt N * Real.sqrt (rowTail A J (ι m')))) =
              cbar * (Real.sqrt N * Real.sqrt N) *
                (Real.sqrt (rowTail A J (ι m)) + Real.sqrt (rowTail A J (ι m'))) := by ring
          rw [e, hN]
  unfold crossBoundFun
  have hZZ : 0 ≤ Z * Z := mul_self_nonneg Z
  exact add_le_add (mul_le_mul_of_nonneg_left hw hB) (mul_le_mul_of_nonneg_left hext hZZ)

end BlockBand.Critical.RelativeVectors
