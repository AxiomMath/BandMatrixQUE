module

public import BlockBand.Palm.MomentFlow.LongShortExcess

/-!
# Arithmetic of the `LongShortPropagation` assembly

* `overlapBound_le_poly`: on the fresh class with `q*Γq = 1`,
  `max(1, N‖q‖²) ≤ C_q N^{1 + 2max(A,1)}` (from `nsq_le_of_gamma`).
* `pow_le_poly`, `junk_le`: the `max(1, N‖q‖²)^r N^{-D'}` remainders of the long-jump bound and
  of `M_loc` are `≤ 1`.
* `longShort_counts_le`, `longShort_final_arith`: the union bounds and the Tonelli–Markov bound of the
  assembly give `P(B) ≤ N^{-D}`, `∫ e ≤ N^{-D}`, `e(c₀) ≤ N^{-D}`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm.CoarseRelative

variable {N : ℕ}

theorem overlapBound_le_poly {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N)
    {A c₀ E r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀)
    {q : Fin N → ℂ} (hq : quadForm (freshGamma F c₀ E) q = 1) :
    overlapBound N q ≤
      max 1 (1 / (v₀ * lowConst c₀ s₀ v₀)) * (N : ℝ) ^ (1 + 2 * max A 1) := by
  have h := nsq_le_of_gamma hN hK hC q
  rw [hq, mul_one] at h
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set Cq := max 1 (1 / (v₀ * lowConst c₀ s₀ v₀))
  have hp1 : 1 ≤ (N : ℝ) ^ (1 + 2 * max A 1) :=
    Real.one_le_rpow hN1 (by positivity)
  have e : (N : ℝ) ^ (1 + 2 * max A 1) = N * (N : ℝ) ^ (2 * max A 1) := by
    rw [Real.rpow_add hNp, Real.rpow_one]
  refine max_le (le_trans hp1 (le_mul_of_one_le_left (by linarith) (le_max_left _ _))) ?_
  show (N : ℝ) * nsq q ≤ _
  calc (N : ℝ) * nsq q ≤ N * ((N : ℝ) ^ (2 * max A 1) / (v₀ * lowConst c₀ s₀ v₀)) :=
        mul_le_mul_of_nonneg_left h hNp.le
    _ = (1 / (v₀ * lowConst c₀ s₀ v₀)) * (N : ℝ) ^ (1 + 2 * max A 1) := by rw [e]; ring
    _ ≤ Cq * (N : ℝ) ^ (1 + 2 * max A 1) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

theorem pow_le_poly {x O Cq e : ℝ} {r : ℕ} (hx : 1 ≤ x) (hO0 : 0 ≤ O) (hO : O ≤ Cq * x ^ e)
    (hCqr : Cq ^ r ≤ x) : O ^ r ≤ x ^ (r * e + 1) := by
  have hx0 : 0 < x := by linarith
  calc O ^ r ≤ (Cq * x ^ e) ^ r := pow_le_pow_left₀ hO0 hO r
    _ = Cq ^ r * x ^ (e * r) := by rw [mul_pow, Real.rpow_mul_natCast hx0.le]
    _ ≤ x * x ^ (e * r) := mul_le_mul_of_nonneg_right hCqr (by positivity)
    _ = x ^ (r * e + 1) := by
        rw [Real.rpow_add hx0, Real.rpow_one, mul_comm (r : ℝ) e]; ring

theorem junk_le {x c₂ O Qo D' : ℝ} (hx : 1 ≤ x) (hc₂ : 0 < c₂)
    (hO : O ≤ x ^ Qo) (hD' : Qo + 3 ≤ D') (hc : 1 / c₂ ^ 2 ≤ x) :
    x * (x / c₂ ^ 2) * O * x ^ (-D') ≤ 1 ∧ O * x ^ (-D') ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have h1 : x ^ (-D') ≤ x ^ (-(Qo + 3)) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have h2 : O * x ^ (-D') ≤ x ^ (-(3 : ℝ)) := by
    calc O * x ^ (-D') ≤ x ^ Qo * x ^ (-(Qo + 3)) :=
          mul_le_mul hO h1 (by positivity) (by positivity)
      _ = x ^ (-(3 : ℝ)) := by rw [← Real.rpow_add hx0]; ring_nf
  have h3 : x ^ (-(3 : ℝ)) = (x ^ 3)⁻¹ := by
    rw [Real.rpow_neg hx0.le]; norm_cast
  have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hx
  refine ⟨?_, h2.trans (by rw [h3]; exact inv_le_one_of_one_le₀ hx3)⟩
  calc x * (x / c₂ ^ 2) * O * x ^ (-D') = x * x / c₂ ^ 2 * (O * x ^ (-D')) := by ring
    _ ≤ x * x / c₂ ^ 2 * (x ^ 3)⁻¹ := by
        rw [← h3]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 / c₂ ^ 2 / x := by field_simp
    _ ≤ 1 := by rw [div_le_one hx0]; exact hc

theorem longShort_counts_le {x card O CL ℓ Qo D₁ : ℝ} {r : ℕ} (hx : 4 ≤ x) (hcard0 : 0 ≤ card)
    (hcard : card ≤ x ^ ((r : ℝ) + 1)) (hO0 : 0 ≤ O) (hO : O ≤ x ^ Qo) (hCL : 0 < CL)
    (hCLx : 2 * (r + 1) * r * CL ≤ x) (hℓ : 1 ≤ ℓ) :
    card * (2 * O * (r + 1) * r * (CL * x / ℓ) * x ^ (-D₁)) ≤ x ^ (Qo + r + 3 - D₁) ∧
      card * (2 * O) ≤ x ^ (Qo + r + 2) ∧
      (3 + card) * x ^ (-D₁) ≤ x ^ ((r : ℝ) + 2 - D₁) := by
  have hx0 : 0 < x := by linarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hxℓ : CL * x / ℓ ≤ CL * x := div_le_self (by positivity) hℓ
  have hD : 0 < x ^ (-D₁) := Real.rpow_pos_of_pos hx0 _
  have hK : 2 * O * (r + 1) * r * (CL * x / ℓ) ≤ x * x ^ Qo * x := by
    calc 2 * O * (r + 1) * r * (CL * x / ℓ) ≤ 2 * O * (r + 1) * r * (CL * x) :=
          mul_le_mul_of_nonneg_left hxℓ (by positivity)
      _ = (2 * (r + 1) * r * CL) * O * x := by ring
      _ ≤ x * x ^ Qo * x := by gcongr
  refine ⟨?_, ?_, ?_⟩
  · calc card * (2 * O * (r + 1) * r * (CL * x / ℓ) * x ^ (-D₁))
        ≤ x ^ ((r : ℝ) + 1) * (x * x ^ Qo * x * x ^ (-D₁)) := by
          gcongr
      _ = x ^ (Qo + r + 3 - D₁) := by
          have e1 : x * x ^ Qo * x * x ^ (-D₁) = x ^ (1 + Qo + 1 + -D₁) := by
            rw [Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_one]
          rw [e1, ← Real.rpow_add hx0]; congr 1; ring
  · calc card * (2 * O) ≤ x ^ ((r : ℝ) + 1) * (x * x ^ Qo) := by
          gcongr; linarith
      _ = x ^ (Qo + r + 2) := by
          have e2 : x * x ^ Qo = x ^ (1 + Qo) := by rw [Real.rpow_add hx0, Real.rpow_one]
          rw [e2, ← Real.rpow_add hx0]; congr 1; ring
  · have h1 : 1 ≤ x ^ ((r : ℝ) + 1) := Real.one_le_rpow (by linarith) (by positivity)
    have e : x ^ ((r : ℝ) + 2) = x * x ^ ((r : ℝ) + 1) := by
      rw [show (r : ℝ) + 2 = 1 + ((r : ℝ) + 1) by ring, Real.rpow_add hx0, Real.rpow_one]
    calc (3 + card) * x ^ (-D₁) ≤ x ^ ((r : ℝ) + 2) * x ^ (-D₁) := by
          gcongr; rw [e]; nlinarith
      _ = x ^ ((r : ℝ) + 2 - D₁) := by rw [← Real.rpow_add hx0]; congr 1

/-- **Final arithmetic.** `δ ≤ N^{Q+1-D₁}`, `K_b ≤ N^Q`, `p ≤ N^{r+2-D₁}` with
`D₁ = 2D_p + Q + r + 5` give `τ'(δ + K_b p)/N^{-D_p} + p + N^{-D₁} ≤ N^{-D_p}` and `δ ≤ N^{-D_p}`. -/
theorem longShort_final_arith {x Dp D₁ Q r' δ Kb p τ' : ℝ} (hx : 4 ≤ x) (hDp : 1 ≤ Dp) (hQ : 0 ≤ Q)
    (hr' : 0 ≤ r') (hD₁ : D₁ = 2 * Dp + Q + r' + 5) (hτ1 : τ' ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ x ^ (Q + 1 - D₁)) (hKb0 : 0 ≤ Kb) (hKb : Kb ≤ x ^ Q)
    (hp0 : 0 ≤ p) (hp : p ≤ x ^ (r' + 2 - D₁)) :
    τ' * (δ + Kb * p) / x ^ (-Dp) + p + x ^ (-D₁) ≤ x ^ (-Dp) ∧ δ ≤ x ^ (-Dp) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have mono : ∀ y z : ℝ, y ≤ z → x ^ y ≤ x ^ z := fun y z h =>
    Real.rpow_le_rpow_of_exponent_le hx1 h
  set u := x ^ (-Dp - 3) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hx0 _
  have hδu : δ ≤ x ^ (-2 * Dp - 3) := hδ.trans (mono _ _ (by rw [hD₁]; linarith))
  have hKbp : Kb * p ≤ x ^ (-2 * Dp - 3) := by
    calc Kb * p ≤ x ^ Q * x ^ (r' + 2 - D₁) := mul_le_mul hKb hp hp0 (by positivity)
      _ = x ^ (-2 * Dp - 3) := by rw [← Real.rpow_add hx0, hD₁]; ring_nf
  have hdiv : τ' * (δ + Kb * p) / x ^ (-Dp) ≤ 2 * u := by
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hx0 _)]
    calc τ' * (δ + Kb * p) ≤ 1 * (x ^ (-2 * Dp - 3) + x ^ (-2 * Dp - 3)) :=
          mul_le_mul hτ1 (add_le_add hδu hKbp) (by positivity) zero_le_one
      _ = 2 * u * x ^ (-Dp) := by
          rw [hu, mul_assoc, ← Real.rpow_add hx0]; ring_nf
  have hpu : p ≤ u := hp.trans (mono _ _ (by rw [hD₁]; linarith))
  have hDu : x ^ (-D₁) ≤ u := mono _ _ (by rw [hD₁]; linarith)
  have h4u : 4 * u ≤ x ^ (-Dp) := by
    have e : x ^ (-Dp) = x ^ (3 : ℝ) * u := by rw [hu, ← Real.rpow_add hx0]; ring_nf
    rw [e]
    have : (4 : ℝ) ≤ x ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hx 3
      norm_num at this; linarith
    nlinarith
  refine ⟨by linarith, hδu.trans (mono _ _ (by linarith))⟩

end BlockBand.Palm.MomentFlow
