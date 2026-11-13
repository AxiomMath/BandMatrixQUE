module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Uniform grids stopped at a time `t`

For `0 ≤ t ≤ u` and `K ≥ 1`: grid points `p_k = k u / K` and stopped points `μ_k = min(t, p_k)`, so
`μ_0 = 0` and `μ_K = t`. The cells `(μ_k, μ_{k+1}]`, `k < K`, partition `(0, t]`; a point `x` of the
cell `k` satisfies `p_k < x ≤ p_{k+1} = p_k + u/K` (`mem_cell_bounds`); `cellFun` glues functions
`f_k` on the cells and `sum_integral_cells` adds the cell integrals. At most one cell is partial,
`μ_k < μ_{k+1} < p_{k+1}` (`card_partial_le_one`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.Angular

open MeasureTheory Set

/-- Grid point `p_k = k u / K`. -/
def gridPt (u : ℝ) (K k : ℕ) : ℝ := k * u / K

/-- Stopped grid point `μ_k = min(t, p_k)`. -/
def gridMu (t u : ℝ) (K k : ℕ) : ℝ := min t (gridPt u K k)

variable {t u : ℝ} {K : ℕ}

theorem gridPt_nonneg (hu : 0 ≤ u) (k : ℕ) : 0 ≤ gridPt u K k := by
  unfold gridPt; positivity

theorem gridPt_mono (hu : 0 ≤ u) : Monotone (gridPt u K) := by
  intro j k hjk
  unfold gridPt
  have : (j : ℝ) ≤ k := by exact_mod_cast hjk
  gcongr

@[simp] theorem gridPt_zero : gridPt u K 0 = 0 := by simp [gridPt]

theorem gridPt_self (hK : K ≠ 0) : gridPt u K K = u := by
  unfold gridPt
  have : (K : ℝ) ≠ 0 := by exact_mod_cast hK
  field_simp

theorem gridPt_succ (k : ℕ) : gridPt u K (k + 1) = gridPt u K k + u / K := by
  unfold gridPt; push_cast; ring

theorem gridPt_le (hu : 0 ≤ u) (hK : K ≠ 0) {k : ℕ} (hk : k ≤ K) : gridPt u K k ≤ u := by
  calc gridPt u K k ≤ gridPt u K K := gridPt_mono hu hk
    _ = u := gridPt_self hK

theorem gridMu_mono (hu : 0 ≤ u) : Monotone (gridMu t u K) :=
  fun _ _ h => min_le_min le_rfl (gridPt_mono hu h)

theorem gridMu_zero (ht : 0 ≤ t) : gridMu t u K 0 = 0 := by simp [gridMu, ht]

theorem gridMu_self (hK : K ≠ 0) (htu : t ≤ u) : gridMu t u K K = t := by
  simp [gridMu, gridPt_self hK, htu]

theorem gridMu_le (k : ℕ) : gridMu t u K k ≤ t := min_le_left _ _

theorem gridMu_le_gridPt (k : ℕ) : gridMu t u K k ≤ gridPt u K k := min_le_right _ _

theorem gridMu_nonneg (ht : 0 ≤ t) (hu : 0 ≤ u) (k : ℕ) : 0 ≤ gridMu t u K k :=
  le_min ht (gridPt_nonneg hu k)

/-- A nonempty cell starts at its grid point. -/
theorem gridMu_eq_gridPt_of_lt {k : ℕ} (h : gridMu t u K k < gridMu t u K (k + 1)) :
    gridMu t u K k = gridPt u K k := by
  rcases min_choice t (gridPt u K k) with e | e
  · exfalso
    have : gridMu t u K (k + 1) ≤ gridMu t u K k := by
      rw [show gridMu t u K k = t from e]; exact gridMu_le _
    linarith
  · exact e

/-- The cells cover `(μ_0, μ_m]`. -/
theorem exists_cell_of_mem (hu : 0 ≤ u) (m : ℕ) {x : ℝ}
    (hx : x ∈ Ioc (gridMu t u K 0) (gridMu t u K m)) :
    ∃ k < m, x ∈ Ioc (gridMu t u K k) (gridMu t u K (k + 1)) := by
  induction m with
  | zero => exact absurd hx (by simp)
  | succ m ih =>
    have hU : Ioc (gridMu t u K 0) (gridMu t u K (m + 1)) =
        Ioc (gridMu t u K 0) (gridMu t u K m) ∪ Ioc (gridMu t u K m) (gridMu t u K (m + 1)) :=
      (Ioc_union_Ioc_eq_Ioc (gridMu_mono hu (Nat.zero_le m))
        (gridMu_mono hu (Nat.le_succ m))).symm
    rw [hU] at hx
    rcases hx with hx | hx
    · obtain ⟨k, hk, hxk⟩ := ih hx
      exact ⟨k, Nat.lt_succ_of_lt hk, hxk⟩
    · exact ⟨m, Nat.lt_succ_self m, hx⟩

theorem exists_cell (ht : 0 ≤ t) (htu : t ≤ u) (hK : K ≠ 0) {x : ℝ} (hx : x ∈ Ioc 0 t) :
    ∃ k < K, x ∈ Ioc (gridMu t u K k) (gridMu t u K (k + 1)) := by
  have hu : 0 ≤ u := ht.trans htu
  refine exists_cell_of_mem hu K ?_
  rwa [gridMu_zero ht, gridMu_self hK htu]

theorem cell_unique (hu : 0 ≤ u) {j k : ℕ} {x : ℝ}
    (hj : x ∈ Ioc (gridMu t u K j) (gridMu t u K (j + 1)))
    (hk : x ∈ Ioc (gridMu t u K k) (gridMu t u K (k + 1))) : j = k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := gridMu_mono (t := t) (K := K) hu (show j + 1 ≤ k by omega)
    linarith [hj.2, hk.1]
  · have := gridMu_mono (t := t) (K := K) hu (show k + 1 ≤ j by omega)
    linarith [hj.1, hk.2]

/-- A point of the cell `k` satisfies `p_k < x ≤ p_{k+1} = p_k + u/K`. -/
theorem mem_cell_bounds {k : ℕ} {x : ℝ}
    (hx : x ∈ Ioc (gridMu t u K k) (gridMu t u K (k + 1))) :
    gridPt u K k < x ∧ x ≤ gridPt u K (k + 1) ∧ x ≤ t := by
  have hlt : gridMu t u K k < gridMu t u K (k + 1) := lt_of_lt_of_le hx.1 hx.2
  refine ⟨?_, hx.2.trans (gridMu_le_gridPt _), hx.2.trans (gridMu_le _)⟩
  rw [← gridMu_eq_gridPt_of_lt hlt]; exact hx.1

/-- The glued function: `f_k` on the cell `k`. -/
def cellFun (t u : ℝ) (K : ℕ) (f : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range K, (Ioc (gridMu t u K k) (gridMu t u K (k + 1))).indicator (f k) x

theorem cellFun_eq (hu : 0 ≤ u) (f : ℕ → ℝ → ℝ) {k : ℕ} (hk : k < K) {x : ℝ}
    (hx : x ∈ Ioc (gridMu t u K k) (gridMu t u K (k + 1))) : cellFun t u K f x = f k x := by
  unfold cellFun
  rw [Finset.sum_eq_single k]
  · exact indicator_of_mem hx _
  · intro j _ hjk
    refine indicator_of_notMem (fun hj => hjk ?_) _
    exact cell_unique hu hj hx
  · intro h; exact absurd (Finset.mem_range.2 hk) h

theorem sum_integral_cells (ht : 0 ≤ t) (htu : t ≤ u) (hK : K ≠ 0) (f : ℕ → ℝ → ℝ)
    (hf : ∀ k < K, IntegrableOn (f k) (Ioc (gridMu t u K k) (gridMu t u K (k + 1)))) :
    ∑ k ∈ Finset.range K, ∫ x in Ioc (gridMu t u K k) (gridMu t u K (k + 1)), f k x =
      ∫ x in Ioc 0 t, cellFun t u K f x := by
  have hu : 0 ≤ u := ht.trans htu
  have hcongr : ∀ k < K, ∫ x in Ioc (gridMu t u K k) (gridMu t u K (k + 1)), f k x =
      ∫ x in (gridMu t u K k)..(gridMu t u K (k + 1)), cellFun t u K f x := by
    intro k hk
    rw [intervalIntegral.integral_of_le (gridMu_mono hu (Nat.le_succ k))]
    exact setIntegral_congr_fun measurableSet_Ioc fun x hx => (cellFun_eq hu f hk hx).symm
  rw [Finset.sum_congr rfl fun k hk => hcongr k (Finset.mem_range.1 hk),
    intervalIntegral.sum_integral_adjacent_intervals, gridMu_zero ht, gridMu_self hK htu,
    intervalIntegral.integral_of_le ht]
  intro k hk
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (gridMu_mono hu (Nat.le_succ k))]
  exact (hf k hk).congr_fun (fun x hx => (cellFun_eq hu f hk hx).symm) measurableSet_Ioc

/-- At most one cell is partial. -/
theorem card_partial_le_one (hu : 0 ≤ u) :
    ((Finset.range K).filter (fun k => gridMu t u K k < gridMu t u K (k + 1) ∧
      gridMu t u K (k + 1) < gridPt u K (k + 1))).card ≤ 1 := by
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  simp only [Finset.mem_filter] at ha hb
  have key : ∀ a b, (gridMu t u K a < gridMu t u K (a + 1) ∧
      gridMu t u K (a + 1) < gridPt u K (a + 1)) →
      (gridMu t u K b < gridMu t u K (b + 1)) → ¬ a < b := by
    intro a b ha hb hab
    have e : gridMu t u K (a + 1) = t := by
      rcases min_choice t (gridPt u K (a + 1)) with e | e
      · exact e
      · exact absurd e (ne_of_lt ha.2)
    have h1 := gridMu_mono (t := t) (K := K) hu (show a + 1 ≤ b by omega)
    have h2 := gridMu_le (t := t) (u := u) (K := K) (b + 1)
    linarith
  rcases lt_trichotomy a b with h | h | h
  · exact absurd h (key a b ha.2 hb.2.1)
  · exact h
  · exact absurd h (key b a hb.2 ha.2.1)

end BlockBand.Critical.RelativeVectors.Angular
