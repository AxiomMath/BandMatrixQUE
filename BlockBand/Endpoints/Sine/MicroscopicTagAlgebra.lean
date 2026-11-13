module

public import BlockBand.Endpoints.Sine.MicroscopicTagDefs

/-!
# Deterministic estimates for the microscopic tag comparison

These are deterministic statements about real numbers; no law is involved.

* `sum_abs_deletion_le`: the tag deletion identity in the form used: removing coordinates of
  total mass `a` of a nonnegative mass vector and renormalizing the rest moves the normalized
  vector by at most `2a` in `ℓ¹` (equality `2a` when `a < 1`; all degenerate cases, total mass
  `0` or `a = 1`, included, with Lean's `x/0 = 0`).
* `averagedTest_sub_interiorTest_le`: pointwise, for a test `f` that is `L`-Lipschitz and bounded
  by `C`, the averaged test over the `n = r + 3` ring positions (block `0` with mass zero, two
  ports, `r` interior positions) differs from the interior uniform-tag test
  `r⁻¹ Σ_K f(r m_K / m_int)` by at most `2L a_port + (6C + 3L)/n`, `a_port` the normalized port
  mass.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

/-- Tag deletion identity, inequality form. -/
theorem sum_abs_deletion_le {α β : Type*} [Fintype α] [Fintype β] (m : α ⊕ β → ℝ)
    (hm : ∀ y, 0 ≤ m y) :
    (∑ i, |m (Sum.inl i) / (∑ y, m y) - m (Sum.inl i) / (∑ i, m (Sum.inl i))|) +
        ∑ j, |m (Sum.inr j) / (∑ y, m y)| ≤
      2 * ((∑ j, m (Sum.inr j)) / ∑ y, m y) := by
  set T := ∑ y, m y with hT
  set A := ∑ i, m (Sum.inl i) with hA
  set P := ∑ j, m (Sum.inr j) with hP
  have hTAP : T = A + P := by rw [hT, Fintype.sum_sum_type]
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => hm _
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun j _ => hm _
  have hport : ∑ j, |m (Sum.inr j) / T| = P / T := by
    rw [hP, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => abs_of_nonneg (div_nonneg (hm _) (hTAP ▸ by linarith))
  rw [hport]
  rcases eq_or_lt_of_le hA0 with hA' | hA'
  · -- no interior mass: the renormalized vector is zero
    rw [← hA']
    simp only [div_zero, sub_zero]
    have : ∑ i, |m (Sum.inl i) / T| = A / T := by
      rw [hA, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (div_nonneg (hm _) (hTAP ▸ by linarith))
    rw [this, ← hA', zero_div, zero_add]
    have : 0 ≤ P / T := div_nonneg hP0 (by linarith)
    linarith
  · have hTpos : 0 < T := by linarith
    have hint : ∑ i, |m (Sum.inl i) / T - m (Sum.inl i) / A| = P / T := by
      have hterm : ∀ i, |m (Sum.inl i) / T - m (Sum.inl i) / A| =
          m (Sum.inl i) * (1 / A - 1 / T) := by
        intro i
        have hle : m (Sum.inl i) / T ≤ m (Sum.inl i) / A :=
          div_le_div_of_nonneg_left (hm _) hA' (by linarith)
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_mul, ← hA]
      field_simp
      rw [hTAP]; ring
    rw [hint]; ring_nf; exact le_rfl

/-- Ports and the exposed block removed, pointwise. `f` is `L`-Lipschitz and bounded by `C`;
`m ≥ 0` are the masses of the `r` interior positions and the two ports; `n = r + 3`. -/
theorem averagedTest_sub_interiorTest_le {r : ℕ} (hr : 0 < r) (f : ℝ → ℝ) (L C : ℝ)
    (hL : ∀ a b, |f a - f b| ≤ L * |a - b|) (hC : ∀ a, |f a| ≤ C)
    (m : Fin r ⊕ Fin 2 → ℝ) (hm : ∀ y, 0 ≤ m y) :
    |((r + 3 : ℕ) : ℝ)⁻¹ * (f 0 + ∑ y, f (((r + 3 : ℕ) : ℝ) * m y / ∑ y, m y)) -
        (r : ℝ)⁻¹ * ∑ i, f ((r : ℝ) * m (Sum.inl i) / ∑ i, m (Sum.inl i))| ≤
      2 * L * ((∑ j, m (Sum.inr j)) / ∑ y, m y) + (6 * C + 3 * L) / ((r + 3 : ℕ) : ℝ) := by
  set n : ℝ := ((r + 3 : ℕ) : ℝ) with hn
  set T := ∑ y, m y with hT
  set A := ∑ i, m (Sum.inl i) with hA
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hnr : n = r + 3 := by rw [hn]; push_cast; ring
  have hnpos : 0 < n := by rw [hnr]; linarith
  have hL0 : 0 ≤ L := by
    have := hL 1 0
    have h0 : 0 ≤ |f 1 - f 0| := abs_nonneg _
    norm_num at this; linarith
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => hm _
  -- the intermediate test with the ports removed
  set A₁ := n⁻¹ * (f 0 + ((∑ i, f (n * m (Sum.inl i) / A)) + ∑ _j : Fin 2, f 0)) with hA₁
  have hdel := sum_abs_deletion_le m hm
  have step1 : |n⁻¹ * (f 0 + ∑ y, f (n * m y / T)) - A₁| ≤
      2 * L * ((∑ j, m (Sum.inr j)) / T) := by
    rw [hA₁, ← mul_sub, Fintype.sum_sum_type]
    have hsplit : f 0 + ((∑ i, f (n * m (Sum.inl i) / T)) + ∑ j, f (n * m (Sum.inr j) / T)) -
        (f 0 + ((∑ i, f (n * m (Sum.inl i) / A)) + ∑ _j : Fin 2, f 0)) =
        (∑ i, (f (n * m (Sum.inl i) / T) - f (n * m (Sum.inl i) / A))) +
          ∑ j, (f (n * m (Sum.inr j) / T) - f 0) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]; ring
    rw [hsplit, abs_mul, abs_of_pos (inv_pos.2 hnpos)]
    have h1 : |∑ i, (f (n * m (Sum.inl i) / T) - f (n * m (Sum.inl i) / A))| ≤
        ∑ i, L * n * |m (Sum.inl i) / T - m (Sum.inl i) / A| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine (hL _ _).trans (le_of_eq ?_)
      rw [mul_div_assoc, mul_div_assoc, ← mul_sub, abs_mul, abs_of_pos hnpos]; ring
    have h2 : |∑ j, (f (n * m (Sum.inr j) / T) - f 0)| ≤
        ∑ j, L * n * |m (Sum.inr j) / T| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      refine (hL _ _).trans (le_of_eq ?_)
      rw [sub_zero, mul_div_assoc, abs_mul, abs_of_pos hnpos]; ring
    have h3 := (abs_add_le _ _).trans (add_le_add h1 h2)
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add] at h3
    calc n⁻¹ * |(∑ i, (f (n * m (Sum.inl i) / T) - f (n * m (Sum.inl i) / A))) +
          ∑ j, (f (n * m (Sum.inr j) / T) - f 0)|
        ≤ n⁻¹ * (L * n * ((∑ i, |m (Sum.inl i) / T - m (Sum.inl i) / A|) +
            ∑ j, |m (Sum.inr j) / T|)) :=
          mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hnpos.le)
      _ = L * ((∑ i, |m (Sum.inl i) / T - m (Sum.inl i) / A|) + ∑ j, |m (Sum.inr j) / T|) := by
          rw [mul_comm L n, mul_assoc, ← mul_assoc n⁻¹, inv_mul_cancel₀ hnpos.ne', one_mul]
      _ ≤ L * (2 * ((∑ j, m (Sum.inr j)) / T)) := mul_le_mul_of_nonneg_left hdel hL0
      _ = 2 * L * ((∑ j, m (Sum.inr j)) / T) := by ring
  -- from `n` positions to the `r` interior positions
  have hxsum : ∑ i, m (Sum.inl i) / A ≤ 1 := by
    rw [← Finset.sum_div]
    rcases eq_or_lt_of_le hA0 with h | h
    · rw [← hA, ← h, div_zero]; exact zero_le_one
    · rw [← hA, div_self h.ne']
  have hx0 : ∀ i, 0 ≤ m (Sum.inl i) / A := fun i => div_nonneg (hm _) hA0
  have step2 : |A₁ - (r : ℝ)⁻¹ * ∑ i, f ((r : ℝ) * m (Sum.inl i) / A)| ≤
      (6 * C + 3 * L) / n := by
    have hdecomp : A₁ - (r : ℝ)⁻¹ * ∑ i, f ((r : ℝ) * m (Sum.inl i) / A) =
        n⁻¹ * (3 * f 0) + (n⁻¹ * ∑ i, (f (n * m (Sum.inl i) / A) - f (r * m (Sum.inl i) / A)) +
          (n⁻¹ - (r : ℝ)⁻¹) * ∑ i, f ((r : ℝ) * m (Sum.inl i) / A)) := by
      rw [hA₁, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    rw [hdecomp]
    have e1 : |n⁻¹ * (3 * f 0)| ≤ 3 * C / n := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hnpos), abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
      rw [inv_mul_eq_div]
      exact div_le_div_of_nonneg_right (by linarith [hC 0]) hnpos.le
    have e2 : |n⁻¹ * ∑ i, (f (n * m (Sum.inl i) / A) - f (r * m (Sum.inl i) / A))| ≤
        3 * L / n := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hnpos), inv_mul_eq_div]
      refine div_le_div_of_nonneg_right ?_ hnpos.le
      calc |∑ i, (f (n * m (Sum.inl i) / A) - f (r * m (Sum.inl i) / A))|
          ≤ ∑ i, L * (3 * (m (Sum.inl i) / A)) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            refine (hL _ _).trans (le_of_eq ?_)
            rw [mul_div_assoc, mul_div_assoc, ← sub_mul, hnr,
              show ((r : ℝ) + 3 - r) = 3 by ring, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3),
              abs_of_nonneg (hx0 i)]
        _ = 3 * L * ∑ i, m (Sum.inl i) / A := by rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
        _ ≤ 3 * L * 1 := mul_le_mul_of_nonneg_left hxsum (by linarith)
        _ = 3 * L := mul_one _
    have e3 : |(n⁻¹ - (r : ℝ)⁻¹) * ∑ i, f ((r : ℝ) * m (Sum.inl i) / A)| ≤ 3 * C / n := by
      have hsum : |∑ i, f ((r : ℝ) * m (Sum.inl i) / A)| ≤ r * C := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => hC _).trans (le_of_eq ?_)
        simp
      have hd : |n⁻¹ - (r : ℝ)⁻¹| = 3 / (n * r) := by
        rw [hnr]
        have : ((r : ℝ) + 3)⁻¹ - (r : ℝ)⁻¹ = -(3 / ((r + 3) * r)) := by field_simp; ring
        rw [this, abs_neg, abs_of_pos (by positivity)]
      rw [abs_mul, hd]
      calc 3 / (n * r) * |∑ i, f ((r : ℝ) * m (Sum.inl i) / A)| ≤ 3 / (n * r) * (r * C) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 3 * C / n := by field_simp
    have := (abs_add_le _ _).trans (add_le_add e1 ((abs_add_le _ _).trans (add_le_add e2 e3)))
    calc _ ≤ 3 * C / n + (3 * L / n + 3 * C / n) := this
      _ = (6 * C + 3 * L) / n := by ring
  calc _ ≤ |n⁻¹ * (f 0 + ∑ y, f (n * m y / T)) - A₁| +
        |A₁ - (r : ℝ)⁻¹ * ∑ i, f ((r : ℝ) * m (Sum.inl i) / A)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add step1 step2

end BlockBand.Endpoints
