module

public import Mathlib

/-!
# Integration by parts for a killing factor: the pathwise Riemann sums

The proof of `RatioDualityPrinciple` multiplies the martingale `f(Z_r) − f(Z_0) − ∫_0^r 𝒟f(Z_u) du`
by the killing factor `K_r = exp(−∫_0^r h(t−v)R_v dv)`; Mathlib has no stochastic integration by
parts, so we discretize on the grid `t_j = j r/(n+1)`. This file is the deterministic part. For
real functions `φ, k` continuous on `[0,r]` and bounded `g, k'` with `k(b) − k(a) = ∫_a^b k'`:
* `mul_sub_mul_eq_sum` (telescoping):
  `φ(r)k(r) − φ(0)k(0) = Σ_j [k_j Δφ_j + φ_j Δk_j + Δk_j Δφ_j]`;
* **`tendsto_riemannKill`**: the Riemann sums
  `Σ_j [k_j ∫_{t_j}^{t_{j+1}} g + φ_j Δk_j + Δk_j Δφ_j]` tend to `∫_0^r (k g + φ k')`
  (uniform continuity of `φ, k` on `[0,r]`; no step functions);
* `abs_riemannKill_le`: they are bounded by `4C²r` when `|φ|, |k|, |g|, |k'| ≤ C`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory Filter Topology Set intervalIntegral

/-- The grid `t_j = j r/(n+1)` on `[0, r]`. -/
def killGrid (r : ℝ) (n j : ℕ) : ℝ := j * r / (n + 1)

theorem killGrid_zero (r : ℝ) (n : ℕ) : killGrid r n 0 = 0 := by simp [killGrid]

theorem killGrid_last (r : ℝ) (n : ℕ) : killGrid r n (n + 1) = r := by
  unfold killGrid; push_cast; field_simp

theorem killGrid_succ_sub (r : ℝ) (n j : ℕ) :
    killGrid r n (j + 1) - killGrid r n j = r / (n + 1) := by
  unfold killGrid; push_cast; field_simp; ring

theorem killGrid_mem {r : ℝ} (hr : 0 ≤ r) {n j : ℕ} (hj : j ≤ n + 1) :
    killGrid r n j ∈ Icc 0 r := by
  unfold killGrid
  have hn : (0 : ℝ) < n + 1 := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hn]
  have : (j : ℝ) ≤ n + 1 := by exact_mod_cast hj
  nlinarith

theorem killGrid_le_succ {r : ℝ} (hr : 0 ≤ r) (n j : ℕ) :
    killGrid r n j ≤ killGrid r n (j + 1) := by
  have := killGrid_succ_sub r n j
  have : 0 ≤ r / (n + 1) := by positivity
  linarith

theorem uIcc_killGrid_subset {r : ℝ} (hr : 0 ≤ r) {n j : ℕ} (hj : j < n + 1) :
    uIcc (killGrid r n j) (killGrid r n (j + 1)) ⊆ Icc 0 r := by
  rw [uIcc_of_le (killGrid_le_succ hr n j)]
  exact Icc_subset_Icc (killGrid_mem hr hj.le).1 (killGrid_mem hr (Nat.succ_le_of_lt hj)).2

/-- Telescoping of a product along a sequence. -/
theorem mul_sub_mul_eq_sum (a b : ℕ → ℝ) (n : ℕ) :
    a n * b n - a 0 * b 0 = ∑ j ∈ Finset.range n,
      (b j * (a (j + 1) - a j) + a j * (b (j + 1) - b j) + (b (j + 1) - b j) * (a (j + 1) - a j)) := by
  rw [← Finset.sum_range_sub (fun j => a j * b j) n]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The discretized killed sum. -/
def riemannKill (φ g k : ℝ → ℝ) (r : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (k (killGrid r n j) * (∫ u in killGrid r n j..killGrid r n (j + 1), g u) +
      φ (killGrid r n j) * (k (killGrid r n (j + 1)) - k (killGrid r n j)) +
      (k (killGrid r n (j + 1)) - k (killGrid r n j)) *
        (φ (killGrid r n (j + 1)) - φ (killGrid r n j)))

variable {φ g k k' : ℝ → ℝ} {r C : ℝ}

theorem abs_sub_le_of_deriv (hkd : ∀ a b, 0 ≤ a → a ≤ b → b ≤ r → k b - k a = ∫ u in a..b, k' u)
    (hk'b : ∀ u, |k' u| ≤ C) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ r) :
    |k b - k a| ≤ C * (b - a) := by
  rw [hkd a b ha hab hb]
  have := norm_integral_le_of_norm_le_const (a := a) (b := b) (f := k') fun u _ => hk'b u
  rwa [abs_of_nonneg (sub_nonneg.2 hab)] at this

theorem abs_riemannKill_le (hr : 0 ≤ r) (hφb : ∀ u, |φ u| ≤ C) (hgb : ∀ u, |g u| ≤ C)
    (hkb : ∀ u, |k u| ≤ C) (hk'b : ∀ u, |k' u| ≤ C)
    (hkd : ∀ a b, 0 ≤ a → a ≤ b → b ≤ r → k b - k a = ∫ u in a..b, k' u) (n : ℕ) :
    |riemannKill φ g k r n| ≤ 4 * C ^ 2 * r := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hφb 0)
  unfold riemannKill
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hΔ : ∀ j ∈ Finset.range (n + 1), |k (killGrid r n j) *
      (∫ u in killGrid r n j..killGrid r n (j + 1), g u) +
      φ (killGrid r n j) * (k (killGrid r n (j + 1)) - k (killGrid r n j)) +
      (k (killGrid r n (j + 1)) - k (killGrid r n j)) *
        (φ (killGrid r n (j + 1)) - φ (killGrid r n j))| ≤ 4 * C ^ 2 * (r / (n + 1)) := by
    intro j hj
    have hj' : j < n + 1 := Finset.mem_range.1 hj
    have h0 := (killGrid_mem hr hj'.le).1
    have h1 := (killGrid_mem hr (Nat.succ_le_of_lt hj')).2
    have hle := killGrid_le_succ hr n j
    have hd := killGrid_succ_sub r n j
    have hG : |∫ u in killGrid r n j..killGrid r n (j + 1), g u| ≤ C * (r / (n + 1)) := by
      have := norm_integral_le_of_norm_le_const (a := killGrid r n j) (b := killGrid r n (j + 1))
        (f := g) fun u _ => hgb u
      rwa [abs_of_nonneg (sub_nonneg.2 hle), hd] at this
    have hK : |k (killGrid r n (j + 1)) - k (killGrid r n j)| ≤ C * (r / (n + 1)) := by
      rw [← hd]; exact abs_sub_le_of_deriv hkd hk'b h0 hle h1
    have hP : |φ (killGrid r n (j + 1)) - φ (killGrid r n j)| ≤ 2 * C := by
      have := (abs_sub (φ (killGrid r n (j + 1))) (φ (killGrid r n j))).trans
        (add_le_add (hφb (killGrid r n (j + 1))) (hφb (killGrid r n j)))
      linarith
    have hq : 0 ≤ r / (n + 1) := by positivity
    calc _ ≤ |k (killGrid r n j)| * |∫ u in killGrid r n j..killGrid r n (j + 1), g u| +
          |φ (killGrid r n j)| * |k (killGrid r n (j + 1)) - k (killGrid r n j)| +
          |k (killGrid r n (j + 1)) - k (killGrid r n j)| *
            |φ (killGrid r n (j + 1)) - φ (killGrid r n j)| := by
          rw [← abs_mul, ← abs_mul, ← abs_mul]; exact abs_add_three _ _ _
      _ ≤ C * (C * (r / (n + 1))) + C * (C * (r / (n + 1))) + C * (r / (n + 1)) * (2 * C) := by
          gcongr
          · exact hkb _
          · exact hφb _
      _ = 4 * C ^ 2 * (r / (n + 1)) := by ring
  refine (Finset.sum_le_sum hΔ).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  field_simp

/-- **Pathwise convergence of the killed Riemann sums.** -/
theorem tendsto_riemannKill (hr : 0 ≤ r) (hφ : ContinuousOn φ (Icc 0 r))
    (hk : ContinuousOn k (Icc 0 r)) (hgb : ∀ u, |g u| ≤ C) (hk'b : ∀ u, |k' u| ≤ C)
    (hgi : IntervalIntegrable g volume 0 r) (hk'i : IntervalIntegrable k' volume 0 r)
    (hkd : ∀ a b, 0 ≤ a → a ≤ b → b ≤ r → k b - k a = ∫ u in a..b, k' u) :
    Tendsto (riemannKill φ g k r) atTop (𝓝 (∫ u in (0 : ℝ)..r, (k u * g u + φ u * k' u))) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hgb 0)
  have hφu := (isCompact_Icc.uniformContinuousOn_of_continuous hφ)
  have hku := (isCompact_Icc.uniformContinuousOn_of_continuous hk)
  rw [Metric.uniformContinuousOn_iff_le] at hφu hku
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η := ε / (4 * (C * r + 1)) with hη
  have hηp : 0 < η := by positivity
  obtain ⟨δ₁, hδ₁, h₁⟩ := hφu η hηp
  obtain ⟨δ₂, hδ₂, h₂⟩ := hku η hηp
  obtain ⟨N, hN⟩ := exists_nat_gt (r / min δ₁ δ₂)
  refine ⟨N, fun n hn => ?_⟩
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hstep : r / (n + 1) ≤ min δ₁ δ₂ := by
    rw [div_le_iff₀ hn1]
    have : r / min δ₁ δ₂ < n + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [div_lt_iff₀ (lt_min hδ₁ hδ₂)] at this
    linarith
  -- integrability on each cell
  have hcell : ∀ j < n + 1, IntervalIntegrable (fun u => k u * g u + φ u * k' u) volume
      (killGrid r n j) (killGrid r n (j + 1)) := by
    intro j hj
    have hs := uIcc_killGrid_subset hr hj
    have hsub : uIcc (killGrid r n j) (killGrid r n (j + 1)) ⊆ uIcc 0 r := by
      rwa [uIcc_of_le hr]
    exact ((hgi.mono_set hsub).continuousOn_mul (hk.mono hs)).add
      ((hk'i.mono_set hsub).continuousOn_mul (hφ.mono hs))
  have hI := sum_integral_adjacent_intervals (a := killGrid r n) (n := n + 1) hcell
  rw [killGrid_zero, killGrid_last] at hI
  rw [Real.dist_eq, ← hI, riemannKill, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans_lt ?_
  have hpiece : ∀ j ∈ Finset.range (n + 1),
      |k (killGrid r n j) * (∫ u in killGrid r n j..killGrid r n (j + 1), g u) +
        φ (killGrid r n j) * (k (killGrid r n (j + 1)) - k (killGrid r n j)) +
        (k (killGrid r n (j + 1)) - k (killGrid r n j)) *
          (φ (killGrid r n (j + 1)) - φ (killGrid r n j)) -
        ∫ u in killGrid r n j..killGrid r n (j + 1), (k u * g u + φ u * k' u)| ≤
        3 * (C * η) * (r / (n + 1)) := by
    intro j hj
    have hj' : j < n + 1 := Finset.mem_range.1 hj
    set a := killGrid r n j
    set b := killGrid r n (j + 1)
    have h0 := (killGrid_mem hr hj'.le).1
    have h1 := (killGrid_mem hr (Nat.succ_le_of_lt hj')).2
    have hle : a ≤ b := killGrid_le_succ hr n j
    have hd : b - a = r / (n + 1) := killGrid_succ_sub r n j
    have hs := uIcc_killGrid_subset hr hj'
    have hsub : uIcc a b ⊆ uIcc 0 r := by rwa [uIcc_of_le hr]
    have hamem : a ∈ Icc 0 r := ⟨h0, hle.trans h1⟩
    have hbmem : b ∈ Icc 0 r := ⟨h0.trans hle, h1⟩
    have hgi' := hgi.mono_set hsub
    have hk'i' := hk'i.mono_set hsub
    have hA : IntervalIntegrable (fun u => k a * g u + φ a * k' u) volume a b :=
      (hgi'.const_mul _).add (hk'i'.const_mul _)
    have hB : IntervalIntegrable (fun u => k u * g u + φ u * k' u) volume a b :=
      (hgi'.continuousOn_mul (hk.mono hs)).add (hk'i'.continuousOn_mul (hφ.mono hs))
    have e : k a * (∫ u in a..b, g u) + φ a * (k b - k a) - ∫ u in a..b, (k u * g u + φ u * k' u) =
        ∫ u in a..b, ((k a - k u) * g u + (φ a - φ u) * k' u) := by
      have e1 : ∫ u in a..b, ((k a - k u) * g u + (φ a - φ u) * k' u) =
          (∫ u in a..b, (k a * g u + φ a * k' u)) - ∫ u in a..b, (k u * g u + φ u * k' u) := by
        rw [← integral_sub hA hB]; congr 1; funext u; ring
      rw [e1, integral_add (hgi'.const_mul _) (hk'i'.const_mul _), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, hkd a b h0 hle h1]
    have hint : |∫ u in a..b, ((k a - k u) * g u + (φ a - φ u) * k' u)| ≤
        (2 * (C * η)) * (b - a) := by
      have := norm_integral_le_of_norm_le_const (a := a) (b := b)
        (f := fun u => (k a - k u) * g u + (φ a - φ u) * k' u) (C := 2 * (C * η)) ?_
      · rwa [abs_of_nonneg (sub_nonneg.2 hle)] at this
      intro u hu
      have hu' : u ∈ uIcc a b := uIoc_subset_uIcc hu
      have humem : u ∈ Icc 0 r := hs hu'
      rw [uIcc_of_le hle] at hu'
      have hdist : dist a u ≤ min δ₁ δ₂ := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hu'.1])]
        linarith [hu'.2]
      have hk1 : |k a - k u| ≤ η := by
        have := h₂ a hamem u humem (hdist.trans (min_le_right _ _)); rwa [Real.dist_eq] at this
      have hφ1 : |φ a - φ u| ≤ η := by
        have := h₁ a hamem u humem (hdist.trans (min_le_left _ _)); rwa [Real.dist_eq] at this
      rw [Real.norm_eq_abs]
      calc |(k a - k u) * g u + (φ a - φ u) * k' u|
          ≤ |k a - k u| * |g u| + |φ a - φ u| * |k' u| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ η * C + η * C := by gcongr <;> first | exact hgb u | exact hk'b u
        _ = 2 * (C * η) := by ring
    have hK : |k b - k a| ≤ C * (b - a) := abs_sub_le_of_deriv hkd hk'b h0 hle h1
    have hP : |φ b - φ a| ≤ η := by
      have := h₁ b hbmem a hamem (by
        rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith [min_le_left δ₁ δ₂])
      rwa [Real.dist_eq] at this
    calc |k a * (∫ u in a..b, g u) + φ a * (k b - k a) + (k b - k a) * (φ b - φ a) -
          ∫ u in a..b, (k u * g u + φ u * k' u)|
        = |(∫ u in a..b, ((k a - k u) * g u + (φ a - φ u) * k' u)) +
            (k b - k a) * (φ b - φ a)| := by
          rw [← e]; ring_nf
      _ ≤ (2 * (C * η)) * (b - a) + C * (b - a) * η := by
          refine (abs_add_le _ _).trans (add_le_add hint ?_)
          rw [abs_mul]
          exact mul_le_mul hK hP (abs_nonneg _) (by nlinarith)
      _ = 3 * (C * η) * (r / (n + 1)) := by rw [hd]; ring
  refine (Finset.sum_le_sum hpiece).trans_lt ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have e : ((n + 1 : ℕ) : ℝ) * (3 * (C * η) * (r / (n + 1))) = 3 * (C * r) * η := by
    push_cast; field_simp
  rw [e, hη]
  have hCr : 0 ≤ C * r := mul_nonneg hC hr
  rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
  nlinarith

end BlockBand.Transmission.LawDuality
