module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exponent bookkeeping for the physical weighted trace bound

Elementary inequalities in powers of `w = W^{1/100}` for the good and exceptional events.

* `good_arith`: the good-event bound of `good_bound` at these parameters is
  at most `K_A w^{98} + K_B w^{-102} ‖R‖²_HS` (the `W^{19/20+ε}`, `W^{9/10+2ε}`, `W^{1/2+ε}`
  and `dη` terms, then `‖R‖ ≤ (W^{24/25} + W^{-26/25}‖R‖²)/2`).
* `bad_arith`: the trivial bound `(‖G_d‖ + 2s)√(2W)‖R‖ + 2sW + 1` is at most
  `w^{-102}‖R‖² + ‖G_d‖⁴ + 8 w^{602}` (Young twice, in place of Hölder).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.WeightedTrace

theorem rpow_hundredth {W : ℝ} (hW : 0 < W) (x : ℝ) (k : ℤ) (hx : x = k / 100) :
    W ^ x = (W ^ (1 / 100 : ℝ)) ^ k := by
  rw [← Real.rpow_intCast, ← Real.rpow_mul hW.le, hx]; congr 1; ring

theorem zpow_mono_one {w : ℝ} (hw : 1 ≤ w) {m n : ℤ} (h : m ≤ n) : w ^ m ≤ w ^ n :=
  zpow_le_zpow_right₀ hw h

theorem zpow_mul_zpow {w : ℝ} (hw : 1 ≤ w) (m n : ℤ) : w ^ m * w ^ n = w ^ (m + n) :=
  (zpow_add₀ (by positivity) m n).symm

theorem sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- The good-event bound in powers of `w = W^{1/100}`. -/
theorem good_arith {w W η e₁ e₂ e₃ r a₀ ρ Cu A0 CR C0u C₀ s₁ s₂ : ℝ} (hw : 1 ≤ w)
    (hW : W = w ^ (100 : ℤ)) (hη : η = w ^ (-60 : ℤ)) (hs₁ : s₁ = Real.sqrt 2 * w ^ (20 : ℤ))
    (hs₂ : s₂ = Real.sqrt 2 * w ^ (50 : ℤ)) (he₁ : e₁ = CR * w ^ (61 : ℤ))
    (he₂ : e₂ = CR * w ^ (91 : ℤ)) (he₃ : e₃ = CR * w ^ (-99 : ℤ)) (hr : r = C₀ * η + e₃)
    (ha₀ : a₀ ≤ A0 * w ^ (-24 : ℤ)) (ha0 : 0 ≤ a₀) (hρ : 0 ≤ ρ) (hCu : 0 ≤ Cu) (hCR : 0 ≤ CR)
    (hC0u : 0 ≤ C0u) (hC₀ : 0 ≤ C₀) :
    Cu * a₀ * s₁ * ρ + Cu * (2 * W) * η + Cu * (2 * W) * η ^ 2 +
        (η * e₁ + C0u * e₁ + e₂ + 2 * W * (2 * η + 2 * e₃ + 4 * r)) + e₃ * s₂ * ρ ≤
      (4 * Cu + 2 * CR + C0u * CR + 4 + 8 * C₀ + 12 * CR + 2 * Cu * A0 + 2 * CR) * w ^ (98 : ℤ) +
        (2 * Cu * A0 + 2 * CR) * w ^ (-102 : ℤ) * ρ ^ 2 := by
  have hA0 : 0 ≤ A0 := by
    have : 0 ≤ A0 * w ^ (-24 : ℤ) := ha0.trans ha₀
    exact nonneg_of_mul_nonneg_left this (by positivity)
  have h2 := sqrt_two_le_two
  have hs0 := Real.sqrt_nonneg 2
  have p : ∀ k : ℤ, 0 ≤ w ^ k := fun k => by positivity
  have m := fun a b : ℤ => zpow_mul_zpow hw a b
  have le98 : ∀ k : ℤ, k ≤ 98 → w ^ k ≤ w ^ (98 : ℤ) := fun k hk => zpow_mono_one hw hk
  -- the ρ terms: (Cu A0 √2 + CR √2) w^{-4} ρ ≤ (2CuA0 + 2CR)(w^{98} + w^{-102}ρ²)
  have hT1 : Cu * a₀ * s₁ * ρ ≤ 2 * Cu * A0 * (w ^ (-4 : ℤ) * ρ) := by
    rw [hs₁]
    have : a₀ * w ^ (20 : ℤ) ≤ A0 * w ^ (-4 : ℤ) := by
      calc a₀ * w ^ (20 : ℤ) ≤ A0 * w ^ (-24 : ℤ) * w ^ (20 : ℤ) :=
            mul_le_mul_of_nonneg_right ha₀ (p _)
        _ = A0 * w ^ (-4 : ℤ) := by rw [mul_assoc, m]; norm_num
    have h3 : Cu * (a₀ * w ^ (20 : ℤ)) * Real.sqrt 2 * ρ ≤ Cu * (A0 * w ^ (-4 : ℤ)) * 2 * ρ := by
      gcongr
    nlinarith
  have hT5 : e₃ * s₂ * ρ ≤ 2 * CR * (w ^ (-4 : ℤ) * ρ) := by
    rw [he₃, hs₂]
    have e : CR * w ^ (-99 : ℤ) * (Real.sqrt 2 * w ^ (50 : ℤ)) * ρ =
        CR * Real.sqrt 2 * (w ^ (-49 : ℤ) * ρ) := by
      rw [show CR * w ^ (-99 : ℤ) * (Real.sqrt 2 * w ^ (50 : ℤ)) * ρ =
        CR * Real.sqrt 2 * ((w ^ (-99 : ℤ) * w ^ (50 : ℤ)) * ρ) by ring, m]; norm_num
    rw [e]
    have h4 : w ^ (-49 : ℤ) * ρ ≤ w ^ (-4 : ℤ) * ρ :=
      mul_le_mul_of_nonneg_right (zpow_mono_one hw (by norm_num)) hρ
    have h5 : 0 ≤ w ^ (-49 : ℤ) * ρ := mul_nonneg (p _) hρ
    calc CR * Real.sqrt 2 * (w ^ (-49 : ℤ) * ρ) ≤ CR * 2 * (w ^ (-4 : ℤ) * ρ) := by gcongr
      _ = _ := by ring
  have hamgm : w ^ (-4 : ℤ) * ρ ≤ w ^ (98 : ℤ) + w ^ (-102 : ℤ) * ρ ^ 2 := by
    have hsq : 0 ≤ (w ^ (48 : ℤ) - w ^ (-52 : ℤ) * ρ) ^ 2 := sq_nonneg _
    have e1 : w ^ (48 : ℤ) * (w ^ (-52 : ℤ) * ρ) = w ^ (-4 : ℤ) * ρ := by
      rw [← mul_assoc, m]; norm_num
    have e2 : (w ^ (48 : ℤ)) ^ 2 = w ^ (96 : ℤ) := by rw [sq, m]; norm_num
    have e3 : (w ^ (-52 : ℤ) * ρ) ^ 2 = w ^ (-104 : ℤ) * ρ ^ 2 := by
      rw [mul_pow, sq (w ^ (-52 : ℤ)), m]; norm_num
    have h96 : w ^ (96 : ℤ) ≤ w ^ (98 : ℤ) := zpow_mono_one hw (by norm_num)
    have h104 : w ^ (-104 : ℤ) * ρ ^ 2 ≤ w ^ (-102 : ℤ) * ρ ^ 2 :=
      mul_le_mul_of_nonneg_right (zpow_mono_one hw (by norm_num)) (sq_nonneg _)
    have key : (w ^ (48 : ℤ) - w ^ (-52 : ℤ) * ρ) ^ 2 =
        w ^ (96 : ℤ) - 2 * (w ^ (-4 : ℤ) * ρ) + w ^ (-104 : ℤ) * ρ ^ 2 := by
      rw [sub_sq, e2, e3, mul_assoc, e1]
    have n1 : 0 ≤ w ^ (96 : ℤ) := p _
    have n2 : 0 ≤ w ^ (-104 : ℤ) * ρ ^ 2 := mul_nonneg (p _) (sq_nonneg _)
    have n3 : 0 ≤ w ^ (98 : ℤ) := p _
    have n4 : 0 ≤ w ^ (-102 : ℤ) * ρ ^ 2 := mul_nonneg (p _) (sq_nonneg _)
    generalize (w ^ (48 : ℤ) - w ^ (-52 : ℤ) * ρ) ^ 2 = Q at hsq key
    generalize w ^ (-4 : ℤ) * ρ = A at key ⊢
    generalize w ^ (-104 : ℤ) * ρ ^ 2 = C at key h104 n2
    generalize w ^ (-102 : ℤ) * ρ ^ 2 = E at h104 n4 ⊢
    linarith
  -- the constant terms
  have hT2 : Cu * (2 * W) * η ≤ 2 * Cu * w ^ (98 : ℤ) := by
    rw [hW, hη, show Cu * (2 * w ^ (100 : ℤ)) * w ^ (-60 : ℤ) = 2 * Cu * (w ^ (100 : ℤ) *
      w ^ (-60 : ℤ)) by ring, m]
    exact mul_le_mul_of_nonneg_left (le98 _ (by norm_num)) (by positivity)
  have hT3 : Cu * (2 * W) * η ^ 2 ≤ 2 * Cu * w ^ (98 : ℤ) := by
    rw [hW, hη, show Cu * (2 * w ^ (100 : ℤ)) * (w ^ (-60 : ℤ)) ^ 2 = 2 * Cu * (w ^ (100 : ℤ) *
      (w ^ (-60 : ℤ) * w ^ (-60 : ℤ))) by ring, m, m]
    exact mul_le_mul_of_nonneg_left (le98 _ (by norm_num)) (by positivity)
  have hT4 : η * e₁ + C0u * e₁ + e₂ + 2 * W * (2 * η + 2 * e₃ + 4 * r) ≤
      (2 * CR + C0u * CR + 4 + 8 * C₀ + 12 * CR) * w ^ (98 : ℤ) := by
    rw [hr, he₁, he₂, he₃, hW, hη]
    have a1 : w ^ (-60 : ℤ) * (CR * w ^ (61 : ℤ)) ≤ CR * w ^ (98 : ℤ) := by
      rw [show w ^ (-60 : ℤ) * (CR * w ^ (61 : ℤ)) = CR * (w ^ (-60 : ℤ) * w ^ (61 : ℤ)) by ring, m]
      exact mul_le_mul_of_nonneg_left (le98 _ (by norm_num)) hCR
    have a2 : C0u * (CR * w ^ (61 : ℤ)) ≤ C0u * CR * w ^ (98 : ℤ) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left (le98 _ (by norm_num)) (by positivity)
    have a3 : CR * w ^ (91 : ℤ) ≤ CR * w ^ (98 : ℤ) :=
      mul_le_mul_of_nonneg_left (le98 _ (by norm_num)) hCR
    have a4 : 2 * w ^ (100 : ℤ) * (2 * w ^ (-60 : ℤ) + 2 * (CR * w ^ (-99 : ℤ)) +
        4 * (C₀ * w ^ (-60 : ℤ) + CR * w ^ (-99 : ℤ))) =
        (4 + 8 * C₀) * (w ^ (100 : ℤ) * w ^ (-60 : ℤ)) + 12 * CR * (w ^ (100 : ℤ) *
          w ^ (-99 : ℤ)) := by ring
    rw [a4, m, m]
    have b1 : (4 + 8 * C₀) * w ^ ((100 : ℤ) + -60) ≤ (4 + 8 * C₀) * w ^ (98 : ℤ) :=
      mul_le_mul_of_nonneg_left (le98 _ (by norm_num)) (by positivity)
    have b2 : 12 * CR * w ^ ((100 : ℤ) + -99) ≤ 12 * CR * w ^ (98 : ℤ) :=
      mul_le_mul_of_nonneg_left (le98 _ (by norm_num)) (by positivity)
    nlinarith
  have hKB : 0 ≤ 2 * Cu * A0 + 2 * CR := by positivity
  have hfin := mul_le_mul_of_nonneg_left hamgm hKB
  nlinarith

/-- The trivial bound in powers of `w`. -/
theorem bad_arith {w W g s ρ s₂ : ℝ} (hw : 1 ≤ w) (hW : W = w ^ (100 : ℤ))
    (hs₂ : s₂ = Real.sqrt 2 * w ^ (50 : ℤ)) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (g + 2 * s) * s₂ * ρ + s * (2 * W) + 1 ≤
      w ^ (-102 : ℤ) * ρ ^ 2 + g ^ 4 + 8 * w ^ (602 : ℤ) := by
  have m := fun a b : ℤ => zpow_mul_zpow hw a b
  have p : ∀ k : ℤ, 0 < w ^ k := fun k => by positivity
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set b := (g + 2 * s) * Real.sqrt 2 * w ^ (50 : ℤ) with hb
  -- Young: bρ ≤ w^{-102}ρ² + w^{102} b²/4
  have hY : b * ρ ≤ w ^ (-102 : ℤ) * ρ ^ 2 + w ^ (102 : ℤ) * b ^ 2 / 4 := by
    have hsq : 0 ≤ (w ^ (-51 : ℤ) * ρ - w ^ (51 : ℤ) * b / 2) ^ 2 := sq_nonneg _
    have e1 : w ^ (-51 : ℤ) * w ^ (51 : ℤ) = 1 := by rw [m]; norm_num
    have e2 : w ^ (-51 : ℤ) * w ^ (-51 : ℤ) = w ^ (-102 : ℤ) := by rw [m]; norm_num
    have e3 : w ^ (51 : ℤ) * w ^ (51 : ℤ) = w ^ (102 : ℤ) := by rw [m]; norm_num
    have key : (w ^ (-51 : ℤ) * ρ - w ^ (51 : ℤ) * b / 2) ^ 2 =
        (w ^ (-51 : ℤ) * w ^ (-51 : ℤ)) * ρ ^ 2 - (w ^ (-51 : ℤ) * w ^ (51 : ℤ)) * (b * ρ) +
          (w ^ (51 : ℤ) * w ^ (51 : ℤ)) * b ^ 2 / 4 := by ring
    rw [e1, e2, e3] at key
    linarith
  have hb2 : w ^ (102 : ℤ) * b ^ 2 / 4 = (g + 2 * s) ^ 2 * w ^ (202 : ℤ) / 2 := by
    have ew : (w ^ (50 : ℤ)) ^ 2 = w ^ (100 : ℤ) := by rw [sq, m]; norm_num
    rw [hb, mul_pow, mul_pow, h2, ew]
    rw [show w ^ (102 : ℤ) * ((g + 2 * s) ^ 2 * 2 * w ^ (100 : ℤ)) / 4 =
      (g + 2 * s) ^ 2 * (w ^ (102 : ℤ) * w ^ (100 : ℤ)) / 2 by ring, m]
    norm_num
  -- (g + 2s)² ≤ w^{400} + g⁴ w^{-400} + 8
  have hg2 : (g + 2 * s) ^ 2 ≤ w ^ (400 : ℤ) + g ^ 4 * w ^ (-400 : ℤ) + 8 := by
    have hsq : 0 ≤ (w ^ (200 : ℤ) - g ^ 2 * w ^ (-200 : ℤ)) ^ 2 := sq_nonneg _
    have e1 : w ^ (200 : ℤ) * w ^ (-200 : ℤ) = 1 := by rw [m]; norm_num
    have e2 : w ^ (200 : ℤ) * w ^ (200 : ℤ) = w ^ (400 : ℤ) := by rw [m]; norm_num
    have e3 : w ^ (-200 : ℤ) * w ^ (-200 : ℤ) = w ^ (-400 : ℤ) := by rw [m]; norm_num
    have key : (w ^ (200 : ℤ) - g ^ 2 * w ^ (-200 : ℤ)) ^ 2 =
        w ^ (200 : ℤ) * w ^ (200 : ℤ) - 2 * g ^ 2 * (w ^ (200 : ℤ) * w ^ (-200 : ℤ)) +
          g ^ 4 * (w ^ (-200 : ℤ) * w ^ (-200 : ℤ)) := by ring
    rw [e1, e2, e3] at key
    have hs2 : s ^ 2 ≤ 1 := by nlinarith
    have hexp : (g + 2 * s) ^ 2 = 2 * g ^ 2 + 8 * s ^ 2 - (g - 2 * s) ^ 2 := by ring
    nlinarith [sq_nonneg (g - 2 * s)]
  have hmain : (g + 2 * s) ^ 2 * w ^ (202 : ℤ) / 2 ≤ g ^ 4 + 5 * w ^ (602 : ℤ) := by
    have h1 : (g + 2 * s) ^ 2 * w ^ (202 : ℤ) ≤
        (w ^ (400 : ℤ) + g ^ 4 * w ^ (-400 : ℤ) + 8) * w ^ (202 : ℤ) :=
      mul_le_mul_of_nonneg_right hg2 (p _).le
    have e : (w ^ (400 : ℤ) + g ^ 4 * w ^ (-400 : ℤ) + 8) * w ^ (202 : ℤ) =
        w ^ (400 : ℤ) * w ^ (202 : ℤ) + g ^ 4 * (w ^ (-400 : ℤ) * w ^ (202 : ℤ)) +
          8 * w ^ (202 : ℤ) := by ring
    rw [e, m, m] at h1
    have q1 : w ^ ((-400 : ℤ) + 202) ≤ 1 := by
      rw [show (1 : ℝ) = w ^ (0 : ℤ) by simp]; exact zpow_mono_one hw (by norm_num)
    have q2 : w ^ (202 : ℤ) ≤ w ^ (602 : ℤ) := zpow_mono_one hw (by norm_num)
    have q3 : g ^ 4 * w ^ ((-400 : ℤ) + 202) ≤ g ^ 4 :=
      mul_le_of_le_one_right (by positivity) q1
    have : ((400 : ℤ) + 202) = 602 := by norm_num
    rw [this] at h1
    have n1 : 0 ≤ g ^ 4 := by positivity
    have n2 : 0 ≤ w ^ (602 : ℤ) := (p _).le
    linarith
  have hlin : s * (2 * W) + 1 ≤ 3 * w ^ (602 : ℤ) := by
    rw [hW]
    have q1 : w ^ (100 : ℤ) ≤ w ^ (602 : ℤ) := zpow_mono_one hw (by norm_num)
    have q0 : (1 : ℝ) ≤ w ^ (602 : ℤ) := by
      rw [show (1 : ℝ) = w ^ (0 : ℤ) by simp]; exact zpow_mono_one hw (by norm_num)
    nlinarith [p 100]
  have hbρ : (g + 2 * s) * s₂ * ρ = b * ρ := by rw [hs₂, hb]; ring
  rw [hbρ]
  linarith

end BlockBand.DeterminantScore.WeightedTrace
