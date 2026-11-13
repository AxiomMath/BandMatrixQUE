module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.MP.Telescope
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Discretizing a random time on a grid of `[s, t]`)

Deterministic. For `τ ∈ [0, ∞]`, `s ≤ t` and the grid `t_k = grid s t n k`,
`firstIdx τ s t n` is the first index `k ≤ n + 1` with `τ ≤ t_k` (or `n + 1`); the grid point
`t_{firstIdx}` is the first grid point at or after `τ` (clipped to `[s, t]`). Then:

* `sum_ite_lt_eq`: `Σ_k 1{t_k < τ}(y(t_{k+1}) - y(t_k)) = y(t_{firstIdx}) - y(s)`;
* `tendsto_telescope'`: for continuous `y`, this tends to `y(t ∧ τ) - y(s ∧ τ)`.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem exists_firstIdx (τ : WithTop ℝ≥0) (s t : ℝ≥0) (n : ℕ) :
    ∃ k, ¬ ((grid s t n k : WithTop ℝ≥0) < τ) ∨ k = n + 1 := ⟨n + 1, Or.inr rfl⟩

open Classical in
/-- First grid index at or after `τ`. -/
def firstIdx (τ : WithTop ℝ≥0) (s t : ℝ≥0) (n : ℕ) : ℕ := Nat.find (exists_firstIdx τ s t n)

variable {τ : WithTop ℝ≥0} {s t : ℝ≥0} {n : ℕ}

theorem firstIdx_le : firstIdx τ s t n ≤ n + 1 := by
  classical
  exact Nat.find_min' (exists_firstIdx τ s t n) (Or.inr rfl)

theorem lt_of_lt_firstIdx {k : ℕ} (hk : k < firstIdx τ s t n) :
    (grid s t n k : WithTop ℝ≥0) < τ := by
  classical
  have := Nat.find_min (exists_firstIdx τ s t n) hk
  push Not at this
  exact this.1

theorem not_lt_firstIdx (h : firstIdx τ s t n < n + 1) :
    ¬ ((grid s t n (firstIdx τ s t n) : WithTop ℝ≥0) < τ) := by
  classical
  rcases Nat.find_spec (exists_firstIdx τ s t n) with h1 | h1
  · exact h1
  · exact absurd h1 (Nat.ne_of_lt h)

theorem lt_iff_lt_firstIdx (hst : s ≤ t) {k : ℕ} (hk : k < n + 1) :
    (grid s t n k : WithTop ℝ≥0) < τ ↔ k < firstIdx τ s t n := by
  refine ⟨fun h => ?_, lt_of_lt_firstIdx⟩
  by_contra hkm
  push Not at hkm
  exact not_lt_firstIdx (lt_of_le_of_lt hkm hk)
    (lt_of_le_of_lt (WithTop.coe_le_coe.2 (grid_mono hst n hkm)) h)

theorem sum_ite_lt_eq {E : Type*} [AddCommGroup E] (y : ℝ≥0 → E) (hst : s ≤ t) :
    ∑ k ∈ Finset.range (n + 1),
      (if (grid s t n k : WithTop ℝ≥0) < τ then y (grid s t n (k + 1)) - y (grid s t n k)
        else 0) = y (grid s t n (firstIdx τ s t n)) - y s := by
  classical
  rw [Finset.sum_congr rfl fun k hk => by rw [if_congr (lt_iff_lt_firstIdx hst
    (Finset.mem_range.1 hk)) rfl rfl], ← Finset.sum_filter]
  have : (Finset.range (n + 1)).filter (fun k => k < firstIdx τ s t n) =
      Finset.range (firstIdx τ s t n) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h firstIdx_le, h⟩⟩
  rw [this, Finset.sum_range_sub (fun k => y (grid s t n k)), grid_zero]

/-- The grid point `t_{firstIdx}` approximates `t ∧ τ` when `s < τ`. -/
theorem abs_grid_firstIdx_sub_le (hst : s ≤ t) (hsτ : (s : WithTop ℝ≥0) < τ) :
    |(grid s t n (firstIdx τ s t n) : ℝ) - stopTime τ t| ≤ (t - s : ℝ) / (n + 1) := by
  have hΔ : ∀ k, (grid s t n (k + 1) : ℝ) = grid s t n k + (t - s : ℝ) / (n + 1) := fun k => by
    rw [coe_grid hst, coe_grid hst, rgrid_succ]
  have hst' := stopTime_le τ t
  have hΔ0 : (0 : ℝ) ≤ (t - s : ℝ) / (n + 1) := by
    have : (s : ℝ) ≤ t := by exact_mod_cast hst
    exact div_nonneg (by linarith) (by positivity)
  rcases eq_or_lt_of_le (firstIdx_le (τ := τ) (s := s) (t := t) (n := n)) with he | hlt
  · rw [he, grid_last hst]
    have hP := lt_of_lt_firstIdx (τ := τ) (s := s) (t := t) (n := n) (k := n)
      (by rw [he]; exact Nat.lt_succ_self n)
    have h1 : grid s t n n ≤ stopTime τ t :=
      le_stopTime hP.le (by have := grid_mono hst n (Nat.le_succ n); rwa [grid_last hst] at this)
    have h2 := hΔ n
    rw [grid_last hst] at h2
    have h1' : (grid s t n n : ℝ) ≤ stopTime τ t := by exact_mod_cast h1
    have h3 : (stopTime τ t : ℝ) ≤ t := by exact_mod_cast hst'
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hn := not_lt_firstIdx hlt
    push Not at hn
    have hgt : grid s t n (firstIdx τ s t n) ≤ t := by
      have := grid_mono hst n hlt.le; rwa [grid_last hst] at this
    induction τ with
    | top => exact absurd hn (not_le.2 (WithTop.coe_lt_top _))
    | coe s₀ =>
      have hs : s₀ ≤ grid s t n (firstIdx (s₀ : WithTop ℝ≥0) s t n) := WithTop.coe_le_coe.1 hn
      rw [stopTime_coe, min_eq_right (hs.trans hgt)]
      rcases Nat.eq_zero_or_pos (firstIdx (s₀ : WithTop ℝ≥0) s t n) with hz | hpos
      · rw [hz, grid_zero] at hs
        exact absurd (lt_of_le_of_lt hs (WithTop.coe_lt_coe.1 hsτ)) (lt_irrefl _)
      · obtain ⟨j, hj⟩ : ∃ j, firstIdx (s₀ : WithTop ℝ≥0) s t n = j + 1 :=
          ⟨firstIdx (s₀ : WithTop ℝ≥0) s t n - 1, by omega⟩
        have hPj := lt_of_lt_firstIdx (τ := (s₀ : WithTop ℝ≥0)) (s := s) (t := t) (n := n)
          (k := j) (by omega)
        have hj' : (grid s t n j : ℝ) < s₀ := by exact_mod_cast WithTop.coe_lt_coe.1 hPj
        have h2 := hΔ j
        rw [← hj] at h2
        have hs' : (s₀ : ℝ) ≤ grid s t n (firstIdx (s₀ : WithTop ℝ≥0) s t n) := by
          exact_mod_cast hs
        rw [abs_of_nonneg (by linarith)]
        linarith

/-- **Telescoping limit on `[s, t]`.** -/
theorem tendsto_telescope' {E : Type*} [NormedAddCommGroup E] {y : ℝ≥0 → E}
    (hy : Continuous y) (τ : WithTop ℝ≥0) (hst : s ≤ t) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1),
      (if (grid s t n k : WithTop ℝ≥0) < τ then y (grid s t n (k + 1)) - y (grid s t n k)
        else 0)) atTop (𝓝 (y (stopTime τ t) - y (stopTime τ s))) := by
  simp_rw [sum_ite_lt_eq y hst]
  by_cases hsτ : (s : WithTop ℝ≥0) < τ
  · rw [stopTime_of_lt hsτ]
    have hconv : Tendsto (fun n => grid s t n (firstIdx τ s t n)) atTop (𝓝 (stopTime τ t)) := by
      rw [← NNReal.tendsto_coe]
      refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _)
        (fun n => ?_) (tendsto_mesh (s : ℝ) t))
      rw [Real.norm_eq_abs]; exact abs_grid_firstIdx_sub_le hst hsτ
    exact ((hy.tendsto _).comp hconv).sub_const (y s)
  · push Not at hsτ
    have h0 : ∀ n, firstIdx τ s t n = 0 := fun n => by
      classical
      refine le_antisymm (Nat.find_min' _ (Or.inl ?_)) zero_le
      rw [grid_zero]; exact not_lt.2 hsτ
    simp only [h0, grid_zero, sub_self]
    induction τ with
    | top => exact absurd hsτ (not_le.2 (WithTop.coe_lt_top _))
    | coe s₀ =>
      have hs : s₀ ≤ s := WithTop.coe_le_coe.1 hsτ
      rw [stopTime_coe, stopTime_coe, min_eq_right (hs.trans hst), min_eq_right hs, sub_self]
      exact tendsto_const_nhds

end BlockBand.SourceProcess.Stochastic.Semimartingale
