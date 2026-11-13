module

public import BlockBand.LocalWindow.ProofCount

/-!
# Poisson sums, counting from two heights, perturbation

`poissonWeight h x = h²/(x² + h²)` (so `Σ_λ poissonWeight η λ = η Im Tr (A - iη)⁻¹`, the sum in
the local count of the physical local-window lemma). Deterministic; no measure on the matrices (Lebesgue measure on
`(0,1)` is used only for the layer-cake identity of finite sums).

## Main results

* `poissonWeight_le_window_add`, `spectralSum_poisson_le_count_add` (counting from two heights):
  `Σ P_η ≤ N([-Lη, Lη]) + (2/L²) Σ P_{Lη}`; hence a lower bound `Σ P_η ≥ c₀dη` and an upper
  bound `Σ P_{Lη} ≤ C₀dLη` give `N([-Lη,Lη]) ≥ (c₀ - 2C₀/L) dη`.
* `window_le_two_poisson`: `N([-h,h]) ≤ 2 Σ P_h`.
* `sum_le_of_superlevel` (layer cake for finite sums of `[0,1]`-valued terms).
* `card_Ioo_le`: open-interval counts under a perturbation of rank `k` and size `r`.
* `spectralSum_poisson_le` (Poisson sums under perturbation):
  `Σ_A P_η ≤ Σ_{A'} P_η + |ι| r/η + 2k`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofCount

open Matrix Module Finset MeasureTheory
open scoped InnerProductSpace ENNReal

/-- The Poisson weight `P_h(x) = h²/(x² + h²)`. -/
def poissonWeight (h x : ℝ) : ℝ := h ^ 2 / (x ^ 2 + h ^ 2)

theorem poissonWeight_nonneg (h x : ℝ) : 0 ≤ poissonWeight h x :=
  div_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem poissonWeight_le_one {h : ℝ} (hh : 0 < h) (x : ℝ) : poissonWeight h x ≤ 1 := by
  unfold poissonWeight
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg x]

theorem poissonWeight_abs (h x : ℝ) : poissonWeight h |x| = poissonWeight h x := by
  simp [poissonWeight, sq_abs]

/-!
## Counting from two heights
-/

/-- Termwise: `P_η(x) ≤ 1{|x| ≤ Lη} + (2/L²) P_{Lη}(x)` for `η, L > 0`. -/
theorem poissonWeight_le_window_add {η L : ℝ} (hη : 0 < η) (hL : 0 < L) (x : ℝ) :
    poissonWeight η x ≤ (if |x| ≤ L * η then 1 else 0) + 2 / L ^ 2 * poissonWeight (L * η) x := by
  have hP := poissonWeight_nonneg (L * η) x
  split_ifs with hx
  · have := poissonWeight_le_one hη x
    have : 0 ≤ 2 / L ^ 2 * poissonWeight (L * η) x := mul_nonneg (by positivity) hP
    linarith
  · rw [zero_add]
    have hx' : L * η < |x| := lt_of_not_ge hx
    have hx2 : (L * η) ^ 2 ≤ x ^ 2 := by
      rw [← sq_abs x]; exact pow_le_pow_left₀ (by positivity) hx'.le 2
    unfold poissonWeight
    rw [div_le_iff₀ (by positivity)]
    have hden : 0 < x ^ 2 + (L * η) ^ 2 := by positivity
    rw [show 2 / L ^ 2 * ((L * η) ^ 2 / (x ^ 2 + (L * η) ^ 2)) * (x ^ 2 + η ^ 2) =
      2 * η ^ 2 * (x ^ 2 + η ^ 2) / (x ^ 2 + (L * η) ^ 2) by field_simp]
    rw [le_div_iff₀ hden]
    nlinarith [sq_nonneg η, sq_nonneg x, mul_pos hη hη]

/-- **Counting from two heights**: for Hermitian `A` and `η, L > 0`,
`Σ P_η ≤ N_A([-Lη, Lη]) + (2/L²) Σ P_{Lη}`. -/
theorem spectralSum_poisson_le_count_add {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {η L : ℝ} (hη : 0 < η) (hL : 0 < L) :
    BlockBand.Internal.Contracts.Inputs.spectralSum A (poissonWeight η) ≤
      BlockBand.Internal.Contracts.Inputs.spectralSum A
          (fun l => if |l| ≤ L * η then 1 else 0) +
        2 / L ^ 2 * BlockBand.Internal.Contracts.Inputs.spectralSum A (poissonWeight (L * η)) := by
  rw [spectralSum_eq_sum hA, spectralSum_eq_sum hA, spectralSum_eq_sum hA, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => poissonWeight_le_window_add hη hL _

/-- `N_A([-h, h]) ≤ 2 Σ P_h`. -/
theorem window_le_two_poisson {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {h : ℝ} (hh : 0 < h) :
    BlockBand.Internal.Contracts.Inputs.spectralSum A (fun l => if |l| ≤ h then 1 else 0) ≤
      2 * BlockBand.Internal.Contracts.Inputs.spectralSum A (poissonWeight h) := by
  rw [spectralSum_eq_sum hA, spectralSum_eq_sum hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hP := poissonWeight_nonneg h (hA.eigenvalues j)
  split_ifs with hx
  · unfold poissonWeight
    have hx2 : (hA.eigenvalues j) ^ 2 ≤ h ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith
  · linarith

/-!
## Layer cake for finite sums
-/

theorem lintegral_Iio_indicator {v : ℝ} (hv1 : v ≤ 1) :
    ∫⁻ t in Set.Ioo (0 : ℝ) 1, (Set.Iio v).indicator 1 t = ENNReal.ofReal v := by
  rw [lintegral_indicator_one measurableSet_Iio, Measure.restrict_apply measurableSet_Iio]
  have : Set.Iio v ∩ Set.Ioo (0 : ℝ) 1 = Set.Ioo 0 v := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans_le hv1⟩
  rw [this, Real.volume_Ioo, sub_zero]

theorem sum_Iio_indicator {κ : Type} [Fintype κ] (v : κ → ℝ) (t : ℝ) :
    ∑ j, (Set.Iio (v j)).indicator (1 : ℝ → ℝ≥0∞) t =
      ((univ.filter fun j => t < v j).card : ℝ≥0∞) := by
  simp only [Set.indicator_apply, Set.mem_Iio, Pi.one_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Layer cake for finite sums.** If `0 ≤ v_j, u_j ≤ 1` and for every `t ∈ (0,1)`
`#{j : t < v_j} ≤ #{j : t < u_j} + K`, then `Σ v ≤ Σ u + K`. -/
theorem sum_le_of_superlevel {κ : Type} [Fintype κ] (v u : κ → ℝ) (hv0 : ∀ j, 0 ≤ v j)
    (hv1 : ∀ j, v j ≤ 1) (hu0 : ∀ j, 0 ≤ u j) (hu1 : ∀ j, u j ≤ 1) (K : ℕ)
    (h : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (univ.filter fun j => t < v j).card ≤ (univ.filter fun j => t < u j).card + K) :
    ∑ j, v j ≤ ∑ j, u j + K := by
  have hmeas : ∀ (w : κ → ℝ) (j : κ), Measurable ((Set.Iio (w j)).indicator (1 : ℝ → ℝ≥0∞)) :=
    fun w j => measurable_const.indicator measurableSet_Iio
  have hrepr : ∀ w : κ → ℝ, (∀ j, 0 ≤ w j) → (∀ j, w j ≤ 1) →
      ENNReal.ofReal (∑ j, w j) =
        ∫⁻ t in Set.Ioo (0 : ℝ) 1, ∑ j, (Set.Iio (w j)).indicator (1 : ℝ → ℝ≥0∞) t := by
    intro w hw0 hw1
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ => hw0 j,
      lintegral_finsetSum _ fun j _ => hmeas w j]
    exact Finset.sum_congr rfl fun j _ => (lintegral_Iio_indicator (hw1 j)).symm
  have hmain : ENNReal.ofReal (∑ j, v j) ≤ ENNReal.ofReal (∑ j, u j) + K := by
    rw [hrepr v hv0 hv1, hrepr u hu0 hu1]
    calc ∫⁻ t in Set.Ioo (0 : ℝ) 1, ∑ j, (Set.Iio (v j)).indicator (1 : ℝ → ℝ≥0∞) t
        ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, (∑ j, (Set.Iio (u j)).indicator (1 : ℝ → ℝ≥0∞) t + K) := by
          refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
          rw [sum_Iio_indicator, sum_Iio_indicator]
          exact_mod_cast h t ht
      _ = (∫⁻ t in Set.Ioo (0 : ℝ) 1, ∑ j, (Set.Iio (u j)).indicator (1 : ℝ → ℝ≥0∞) t) + K := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, Real.volume_Ioo]
          norm_num
  have hsum : 0 ≤ ∑ j, u j + K := add_nonneg (Finset.sum_nonneg fun j _ => hu0 j) (by positivity)
  have : ENNReal.ofReal (∑ j, u j) + (K : ℝ≥0∞) = ENNReal.ofReal (∑ j, u j + K) := by
    rw [ENNReal.ofReal_add (Finset.sum_nonneg fun j _ => hu0 j) (by positivity),
      ENNReal.ofReal_natCast]
  rw [this] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff hsum).mp hmain

/-!
## Open-interval counts under perturbation
-/

section Open

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A A' : Matrix ι ι ℂ}

theorem card_filter_not_eq (q : ι → Prop) [DecidablePred q] :
    (univ.filter fun j => ¬ q j).card = Fintype.card ι - (univ.filter q).card := by
  have := Finset.card_filter_add_card_filter_not (s := univ) q
  rw [Finset.card_univ] at this
  omega

/-- `#{λ(A) < c} ≤ #{λ(A') < c + r} + k`. -/
theorem card_lt_le (hA : A.IsHermitian) (hA' : A'.IsHermitian) {k : ℕ} {r : ℝ}
    (h : ProofCount.IsPerturbation A A' k r) (c : ℝ) :
    (univ.filter fun j => hA.eigenvalues j < c).card ≤
      (univ.filter fun j => hA'.eigenvalues j < c + r).card + k := by
  have h1 := card_ge_le hA' hA h.symm (c + r)
  rw [show c + r - r = c by ring] at h1
  have e1 : (univ.filter fun j => hA.eigenvalues j < c) =
      (univ.filter fun j => ¬ c ≤ hA.eigenvalues j) := by ext j; simp
  have e2 : (univ.filter fun j => hA'.eigenvalues j < c + r) =
      (univ.filter fun j => ¬ c + r ≤ hA'.eigenvalues j) := by ext j; simp
  rw [e1, e2, card_filter_not_eq, card_filter_not_eq]
  have b1 := Finset.card_le_univ (univ.filter fun j => c ≤ hA.eigenvalues j)
  have b2 := Finset.card_le_univ (univ.filter fun j => c + r ≤ hA'.eigenvalues j)
  omega

/-- `#{λ(A) > c} ≤ #{λ(A') > c - r} + k`. -/
theorem card_gt_le (hA : A.IsHermitian) (hA' : A'.IsHermitian) {k : ℕ} {r : ℝ}
    (h : ProofCount.IsPerturbation A A' k r) (c : ℝ) :
    (univ.filter fun j => c < hA.eigenvalues j).card ≤
      (univ.filter fun j => c - r < hA'.eigenvalues j).card + k := by
  have h1 := card_le_le hA' hA h.symm (c - r)
  rw [show c - r + r = c by ring] at h1
  have e1 : (univ.filter fun j => c < hA.eigenvalues j) =
      (univ.filter fun j => ¬ hA.eigenvalues j ≤ c) := by ext j; simp
  have e2 : (univ.filter fun j => c - r < hA'.eigenvalues j) =
      (univ.filter fun j => ¬ hA'.eigenvalues j ≤ c - r) := by ext j; simp
  rw [e1, e2, card_filter_not_eq, card_filter_not_eq]
  have b1 := Finset.card_le_univ (univ.filter fun j => hA.eigenvalues j ≤ c)
  have b2 := Finset.card_le_univ (univ.filter fun j => hA'.eigenvalues j ≤ c - r)
  omega

/-- **Open-interval counts under perturbation**: `N_A((a,b)) ≤ N_{A'}((a-r, b+r)) + 2k`. -/
theorem card_Ioo_le (hA : A.IsHermitian) (hA' : A'.IsHermitian) {k : ℕ} {r : ℝ}
    (h : ProofCount.IsPerturbation A A' k r) (a b : ℝ) :
    (univ.filter fun j => a < hA.eigenvalues j ∧ hA.eigenvalues j < b).card ≤
      (univ.filter fun j => a - r < hA'.eigenvalues j ∧ hA'.eigenvalues j < b + r).card +
        2 * k := by
  by_cases hab : a < b
  · have h1 := card_lt_le hA hA' h b
    have h2 := card_gt_le hA hA' h a
    have hu : (univ.filter fun j => hA.eigenvalues j < b) ∪
        (univ.filter fun j => a < hA.eigenvalues j) = univ := by
      ext j; simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]
      by_contra hc; push Not at hc; linarith [hc.1, hc.2]
    have hi : (univ.filter fun j => hA.eigenvalues j < b) ∩
        (univ.filter fun j => a < hA.eigenvalues j) =
        (univ.filter fun j => a < hA.eigenvalues j ∧ hA.eigenvalues j < b) := by
      ext j; simp [and_comm]
    have hi' : (univ.filter fun j => hA'.eigenvalues j < b + r) ∩
        (univ.filter fun j => a - r < hA'.eigenvalues j) =
        (univ.filter fun j => a - r < hA'.eigenvalues j ∧ hA'.eigenvalues j < b + r) := by
      ext j; simp [and_comm]
    have e1 := Finset.card_union_add_card_inter (univ.filter fun j => hA.eigenvalues j < b)
      (univ.filter fun j => a < hA.eigenvalues j)
    have e2 := Finset.card_union_add_card_inter (univ.filter fun j => hA'.eigenvalues j < b + r)
      (univ.filter fun j => a - r < hA'.eigenvalues j)
    have e3 := Finset.card_le_univ ((univ.filter fun j => hA'.eigenvalues j < b + r) ∪
      (univ.filter fun j => a - r < hA'.eigenvalues j))
    rw [hu, hi, Finset.card_univ] at e1
    rw [hi'] at e2
    omega
  · have : (univ.filter fun j => a < hA.eigenvalues j ∧ hA.eigenvalues j < b) = ∅ := by
      ext j; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hj; exact hab (hj.1.trans hj.2)
    rw [this, Finset.card_empty]
    exact Nat.zero_le _

end Open

/-!
## Poisson sums under perturbation
-/

/-- Superlevel sets of `P_η`: for `t ∈ (0,1)`, `t < P_η(x) ↔ |x| < η √(1/t - 1)`. -/
theorem lt_poissonWeight_iff {η t : ℝ} (hη : 0 < η) (ht : t ∈ Set.Ioo (0 : ℝ) 1) (x : ℝ) :
    t < poissonWeight η x ↔ |x| < η * Real.sqrt (1 / t - 1) := by
  obtain ⟨ht0, ht1⟩ := ht
  have hρ : 0 ≤ η * Real.sqrt (1 / t - 1) := mul_nonneg hη.le (Real.sqrt_nonneg _)
  have hsq : (η * Real.sqrt (1 / t - 1)) ^ 2 = η ^ 2 * (1 / t - 1) := by
    rw [mul_pow, Real.sq_sqrt]
    rw [sub_nonneg, le_div_iff₀ ht0]; linarith
  rw [show |x| < η * Real.sqrt (1 / t - 1) ↔ |x| ^ 2 < (η * Real.sqrt (1 / t - 1)) ^ 2 from
    (pow_lt_pow_iff_left₀ (abs_nonneg x) hρ two_ne_zero).symm, hsq, sq_abs]
  unfold poissonWeight
  rw [lt_div_iff₀ (by positivity)]
  rw [mul_sub, mul_one_div, mul_one]
  constructor
  · intro h1
    rw [lt_sub_iff_add_lt, lt_div_iff₀ ht0]
    nlinarith
  · intro h1
    rw [lt_sub_iff_add_lt, lt_div_iff₀ ht0] at h1
    nlinarith

/-- `P_η(max(|y| - r, 0)) ≤ P_η(y) + r/η` for `r ≥ 0`. -/
theorem poissonWeight_shift_le {η r : ℝ} (hη : 0 < η) (hr : 0 ≤ r) (y : ℝ) :
    poissonWeight η (max (|y| - r) 0) ≤ poissonWeight η y + r / η := by
  set Y := |y|
  set z := max (|y| - r) 0
  have hz0 : 0 ≤ z := le_max_right _ _
  have hzY : z ≤ Y := max_le (by linarith) (abs_nonneg y)
  have hYz : Y - z ≤ r := by
    have := le_max_left (|y| - r) 0; linarith
  rw [← poissonWeight_abs η y]
  unfold poissonWeight
  have hz' : 0 < z ^ 2 + η ^ 2 := by positivity
  have hY' : 0 < Y ^ 2 + η ^ 2 := by positivity
  rw [div_add_div _ _ hY'.ne' hη.ne', div_le_div_iff₀ hz' (by positivity)]
  have hkey : η ^ 3 * (Y + z) ≤ (z ^ 2 + η ^ 2) * (Y ^ 2 + η ^ 2) := by
    have h1 : η * (Y + z) ≤ Y ^ 2 + z ^ 2 + η ^ 2 := by
      nlinarith [sq_nonneg (Y - η / 2), sq_nonneg (z - η / 2)]
    have h2 : η ^ 2 * (Y ^ 2 + z ^ 2 + η ^ 2) ≤ (z ^ 2 + η ^ 2) * (Y ^ 2 + η ^ 2) := by
      nlinarith [mul_nonneg (sq_nonneg z) (sq_nonneg Y)]
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg η)]
  have hdiff : Y ^ 2 - z ^ 2 ≤ r * (Y + z) := by nlinarith
  have hYz0 : 0 ≤ Y + z := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hdiff (by positivity : (0:ℝ) ≤ η ^ 3),
    mul_le_mul_of_nonneg_left hkey hr]

/-- **Poisson sums under perturbation**: for a perturbation of rank `k` and size `r ≥ 0` and
`η > 0`, `Σ_A P_η ≤ Σ_{A'} P_η + |ι| r/η + 2k`. -/
theorem spectralSum_poisson_le {ι : Type} [Fintype ι] [DecidableEq ι] {A A' : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hA' : A'.IsHermitian) {k : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (h : ProofCount.IsPerturbation A A' k r) {η : ℝ} (hη : 0 < η) :
    BlockBand.Internal.Contracts.Inputs.spectralSum A (poissonWeight η) ≤
      BlockBand.Internal.Contracts.Inputs.spectralSum A' (poissonWeight η) +
        Fintype.card ι * (r / η) + 2 * k := by
  rw [spectralSum_eq_sum hA, spectralSum_eq_sum hA']
  have hlayer := sum_le_of_superlevel (fun j => poissonWeight η (hA.eigenvalues j))
    (fun j => poissonWeight η (max (|hA'.eigenvalues j| - r) 0))
    (fun j => poissonWeight_nonneg _ _) (fun j => poissonWeight_le_one hη _)
    (fun j => poissonWeight_nonneg _ _) (fun j => poissonWeight_le_one hη _) (2 * k)
    (fun t ht => by
      set ρ := η * Real.sqrt (1 / t - 1)
      have hρ : 0 ≤ ρ := mul_nonneg hη.le (Real.sqrt_nonneg _)
      have e1 : (univ.filter fun j => t < poissonWeight η (hA.eigenvalues j)) =
          (univ.filter fun j => -ρ < hA.eigenvalues j ∧ hA.eigenvalues j < ρ) := by
        ext j; simp only [mem_filter, mem_univ, true_and]
        rw [lt_poissonWeight_iff hη ht, abs_lt]
      have e2 : (univ.filter fun j => t < poissonWeight η (max (|hA'.eigenvalues j| - r) 0)) =
          (univ.filter fun j => -ρ - r < hA'.eigenvalues j ∧ hA'.eigenvalues j < ρ + r) := by
        ext j; simp only [mem_filter, mem_univ, true_and]
        rw [lt_poissonWeight_iff hη ht, abs_of_nonneg (le_max_right _ _), max_lt_iff]
        constructor
        · rintro ⟨h1, _⟩
          have := abs_lt.mp (show |hA'.eigenvalues j| < ρ + r by linarith)
          constructor <;> linarith [this.1, this.2]
        · rintro ⟨h1, h2⟩
          have : |hA'.eigenvalues j| < ρ + r := abs_lt.mpr ⟨by linarith, h2⟩
          refine ⟨by linarith, ?_⟩
          rcases eq_or_lt_of_le hρ with h0 | h0
          · exfalso
            have hρ' : ρ = 0 := h0.symm
            have hsq : Real.sqrt (1 / t - 1) = 0 := by
              rcases mul_eq_zero.mp hρ' with h | h
              · exact absurd h hη.ne'
              · exact h
            rw [Real.sqrt_eq_zero'] at hsq
            obtain ⟨ht0, ht1⟩ := ht
            have : 1 < 1 / t := by rw [lt_div_iff₀ ht0]; linarith
            linarith
          · exact h0
      rw [e1, e2]
      exact card_Ioo_le hA hA' h (-ρ) ρ)
  have hshift : ∑ j, poissonWeight η (max (|hA'.eigenvalues j| - r) 0) ≤
      ∑ j, (poissonWeight η (hA'.eigenvalues j) + r / η) :=
    Finset.sum_le_sum fun j _ => poissonWeight_shift_le hη hr _
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hshift
  push_cast at hlayer
  linarith

end BlockBand.LocalWindow.ProofCount
