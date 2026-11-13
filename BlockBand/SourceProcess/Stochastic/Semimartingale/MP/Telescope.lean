module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.MP.Exit
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Telescoping approximation of a stopped path

Deterministic. For a continuous path `y : ℝ≥0 → E` (normed group), any `τ ∈ [0, ∞]` and
`t ≥ 0`, over the grids `t_k = k t/(n + 1)` of `[0, t]`:
`Σ_k 1{t_k < τ} (y(t_{k+1}) - y(t_k)) → y(t ∧ τ) - y(0)`.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem le_stopTime {τ : WithTop ℝ≥0} {t u : ℝ≥0} (hu : (u : WithTop ℝ≥0) ≤ τ) (hut : u ≤ t) :
    u ≤ stopTime τ t := by
  induction τ with
  | top => rw [stopTime_top]; exact hut
  | coe s₀ => rw [stopTime_coe]; exact le_min hut (WithTop.coe_le_coe.1 hu)

theorem tendsto_telescope {E : Type*} [NormedAddCommGroup E] {y : ℝ≥0 → E} (hy : Continuous y)
    (τ : WithTop ℝ≥0) (t : ℝ≥0) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1),
      (if (grid 0 t n k : WithTop ℝ≥0) < τ then y (grid 0 t n (k + 1)) - y (grid 0 t n k)
        else 0)) atTop (𝓝 (y (stopTime τ t) - y 0)) := by
  have h0t : (0 : ℝ≥0) ≤ t := zero_le
  have hex : ∀ n : ℕ, ∃ k, ¬ ((grid 0 t n k : WithTop ℝ≥0) < τ) ∨ k = n + 1 :=
    fun n => ⟨n + 1, Or.inr rfl⟩
  classical
  set m : ℕ → ℕ := fun n => Nat.find (hex n) with hm
  have hm_le : ∀ n, m n ≤ n + 1 := fun n => Nat.find_min' (hex n) (Or.inr rfl)
  have hP_lt : ∀ n k, k < m n → (grid 0 t n k : WithTop ℝ≥0) < τ := fun n k hk => by
    have := Nat.find_min (hex n) hk
    push Not at this
    exact this.1
  have hP_m : ∀ n, m n < n + 1 → ¬ ((grid 0 t n (m n) : WithTop ℝ≥0) < τ) := fun n h => by
    rcases Nat.find_spec (hex n) with h1 | h1
    · exact h1
    · exact absurd h1 (Nat.ne_of_lt h)
  have hiff : ∀ n k, k < n + 1 → ((grid 0 t n k : WithTop ℝ≥0) < τ ↔ k < m n) := by
    intro n k hk
    refine ⟨fun h => ?_, hP_lt n k⟩
    by_contra hkm
    push Not at hkm
    exact hP_m n (lt_of_le_of_lt hkm hk)
      (lt_of_le_of_lt (WithTop.coe_le_coe.2 (grid_mono h0t n hkm)) h)
  have hsum : ∀ n, ∑ k ∈ Finset.range (n + 1),
      (if (grid 0 t n k : WithTop ℝ≥0) < τ then y (grid 0 t n (k + 1)) - y (grid 0 t n k)
        else 0) = y (grid 0 t n (m n)) - y 0 := by
    intro n
    rw [Finset.sum_congr rfl fun k hk => by rw [if_congr (hiff n k (Finset.mem_range.1 hk))
      rfl rfl], ← Finset.sum_filter]
    have : (Finset.range (n + 1)).filter (fun k => k < m n) = Finset.range (m n) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨lt_of_lt_of_le h (hm_le n), h⟩
    rw [this, Finset.sum_range_sub (fun k => y (grid 0 t n k)), grid_zero]
  -- the grid point `t_{m n}` converges to `t ∧ τ`
  have hclose : ∀ n, |(grid 0 t n (m n) : ℝ) - stopTime τ t| ≤ t / (n + 1) := by
    intro n
    have hΔ : ∀ k, (grid 0 t n (k + 1) : ℝ) = grid 0 t n k + t / (n + 1) := fun k => by
      rw [coe_grid h0t, coe_grid h0t, rgrid_succ]; simp
    have hst := stopTime_le τ t
    rcases eq_or_lt_of_le (hm_le n) with he | hlt
    · rw [he, grid_last h0t]
      have hP := hP_lt n n (by rw [he]; exact Nat.lt_succ_self n)
      have h1 : grid 0 t n n ≤ stopTime τ t :=
        le_stopTime hP.le (by have := grid_mono h0t n (Nat.le_succ n); rwa [grid_last h0t] at this)
      have h2 := hΔ n
      rw [grid_last h0t] at h2
      have h1' : (grid 0 t n n : ℝ) ≤ stopTime τ t := by exact_mod_cast h1
      have h3 : (stopTime τ t : ℝ) ≤ t := by exact_mod_cast hst
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hn := hP_m n hlt
      push Not at hn
      have hgt : grid 0 t n (m n) ≤ t := by
        have := grid_mono h0t n hlt.le; rwa [grid_last h0t] at this
      induction τ with
      | top => exact absurd hn (not_le.2 (WithTop.coe_lt_top _))
      | coe s₀ =>
        have hs : s₀ ≤ grid 0 t n (m n) := WithTop.coe_le_coe.1 hn
        rw [stopTime_coe, min_eq_right (hs.trans hgt)]
        rcases Nat.eq_zero_or_pos (m n) with hz | hpos
        · rw [hz, grid_zero] at hs ⊢
          have : s₀ = 0 := le_antisymm hs zero_le
          simp only [this, sub_self, abs_zero, NNReal.coe_zero]
          positivity
        · obtain ⟨j, hj⟩ : ∃ j, m n = j + 1 := ⟨m n - 1, by omega⟩
          have hPj := hP_lt n j (by omega)
          have hj' : (grid 0 t n j : ℝ) < s₀ := by exact_mod_cast WithTop.coe_lt_coe.1 hPj
          have h2 := hΔ j
          rw [← hj] at h2
          have hs' : (s₀ : ℝ) ≤ grid 0 t n (m n) := by exact_mod_cast hs
          rw [abs_of_nonneg (by linarith)]
          linarith
  have hconv : Tendsto (fun n => grid 0 t n (m n)) atTop (𝓝 (stopTime τ t)) := by
    rw [← NNReal.tendsto_coe]
    have hlim : Tendsto (fun n : ℕ => (t : ℝ) / (n + 1)) atTop (𝓝 0) := by
      simpa using tendsto_mesh (0 : ℝ) t
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _)
      (fun n => ?_) hlim)
    rw [Real.norm_eq_abs]; exact hclose n
  have := ((hy.tendsto _).comp hconv).sub_const (y 0)
  exact this.congr fun n => (hsum n).symm

end BlockBand.SourceProcess.Stochastic.Semimartingale
