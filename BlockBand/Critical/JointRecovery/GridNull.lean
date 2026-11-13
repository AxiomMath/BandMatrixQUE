module

public import BlockBand.Counting.ClosePairGrid

/-!
# A grid argument: quadratic two-point bounds give a null collision set

`measure_iUnion_null_of_grid`: if a monotone family of sets `B x y` has `ν (B x y) ≤ (K(y - x))²`
for `x ≤ y`, and every `bad x` is contained in `B (x - a) (x + a)` for every `a > 0`, then
`ν (⋃ x, bad x) = 0`. Covering each window `[-R, R]` by a grid of mesh `a` gives the bound
`18K²Ra + 36K²a²` (`measure_window_null_of_grid`), which tends to `0` with `a`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.JointRecovery

open MeasureTheory Set Filter
open BlockBand.Counting
open scoped Topology ENNReal

/-- Quantitative grid bound on one window `[-R, R]` with mesh `a > 0`: under the
hypotheses of `measure_iUnion_null_of_grid`, `ν (⋃_{|x| ≤ R} bad x) ≤ 18K²Ra + 36K²a²`. -/
theorem measure_window_null_of_grid {α : Type*} [MeasurableSpace α] (ν : Measure α) (K : ℝ)
    (B : ℝ → ℝ → Set α) (hmono : ∀ x y x' y', x' ≤ x → y ≤ y' → B x y ⊆ B x' y')
    (hB : ∀ x y, x ≤ y → ν (B x y) ≤ ENNReal.ofReal ((K * (y - x)) ^ 2))
    (bad : ℝ → Set α) (hcover : ∀ x a, 0 < a → bad x ⊆ B (x - a) (x + a))
    (R a : ℝ) (hR : 0 ≤ R) (ha : 0 < a) :
    ν (⋃ x ∈ Icc (-R) R, bad x) ≤ ENNReal.ofReal (18 * K ^ 2 * R * a + 36 * K ^ 2 * a ^ 2) := by
  classical
  have hsub : (⋃ x ∈ Icc (-R) R, bad x) ⊆ ⋃ j : Fin (closePairGridSize R a),
      B (closePairGridLo R a j - a / 2) (closePairGridHi R a j + a / 2) := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp hz
    obtain ⟨j, hjlo, hjhi⟩ := exists_closePairGridWindow (x := x) (y := x) hR ha
      (abs_le.mpr ⟨hx.1, hx.2⟩) (by simpa using ha)
    refine mem_iUnion.mpr ⟨j, hmono (x - a / 2) (x + a / 2) _ _ (by linarith) (by linarith)
      (hcover x (a / 2) (half_pos ha) hzx)⟩
  refine (measure_mono hsub).trans ?_
  refine (measure_iUnion_fintype_le ν _).trans ?_
  have hs : (∑ j : Fin (closePairGridSize R a),
        ν (B (closePairGridLo R a j - a / 2) (closePairGridHi R a j + a / 2))) ≤
      ∑ _j : Fin (closePairGridSize R a), ENNReal.ofReal ((K * (3 * a)) ^ 2) := by
    apply Finset.sum_le_sum
    intro j _
    have h := hB (closePairGridLo R a j - a / 2) (closePairGridHi R a j + a / 2)
      (by unfold closePairGridHi; linarith)
    have hlen : (closePairGridHi R a j + a / 2) - (closePairGridLo R a j - a / 2) = 3 * a := by
      unfold closePairGridHi; ring
    rw [hlen] at h
    exact h
  refine hs.trans ?_
  have he : (∑ _j : Fin (closePairGridSize R a), ENNReal.ofReal ((K * (3 * a)) ^ 2)) =
      ENNReal.ofReal ((closePairGridSize R a : ℝ) * (K * (3 * a)) ^ 2) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    simp
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  convert closePairGrid_card_mul_square_le (K := (3 / 2) * K) hR ha using 1 <;> ring

/-- **Grid nullity.** Quadratic interval bounds and local covering give `ν (⋃ x, bad x) = 0`. -/
theorem measure_iUnion_null_of_grid {α : Type*} [MeasurableSpace α] (ν : Measure α) (K : ℝ)
    (B : ℝ → ℝ → Set α) (hmono : ∀ x y x' y', x' ≤ x → y ≤ y' → B x y ⊆ B x' y')
    (hB : ∀ x y, x ≤ y → ν (B x y) ≤ ENNReal.ofReal ((K * (y - x)) ^ 2))
    (bad : ℝ → Set α) (hcover : ∀ x a, 0 < a → bad x ⊆ B (x - a) (x + a)) :
    ν (⋃ x, bad x) = 0 := by
  have hzero (m : ℕ) : ν (⋃ x ∈ Icc (-(m : ℝ)) m, bad x) = 0 := by
    have hscale : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal
        (18 * K ^ 2 * m * ((1 : ℝ) / (n + 1)) + 36 * K ^ 2 * ((1 : ℝ) / (n + 1)) ^ 2))
        atTop (𝓝 0) := by
      have hr : Tendsto (fun n : ℕ =>
          18 * K ^ 2 * m * ((1 : ℝ) / (n + 1)) + 36 * K ^ 2 * ((1 : ℝ) / (n + 1)) ^ 2)
          atTop (𝓝 0) := by
        convert (hscale.const_mul (18 * K ^ 2 * m)).add
          ((hscale.pow 2).const_mul (36 * K ^ 2)) using 1
        simp
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using
        (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hr
    apply le_antisymm _ bot_le
    exact ge_of_tendsto hlim (Eventually.of_forall fun n =>
      measure_window_null_of_grid ν K B hmono hB bad hcover m ((1 : ℝ) / (n + 1))
        (Nat.cast_nonneg _) Nat.one_div_pos_of_nat)
  have hU : (⋃ x, bad x) ⊆ ⋃ m : ℕ, ⋃ x ∈ Icc (-(m : ℝ)) m, bad x := by
    intro z hz
    obtain ⟨x, hx⟩ := mem_iUnion.mp hz
    obtain ⟨m, hm⟩ := exists_nat_ge |x|
    exact mem_iUnion.mpr ⟨m, mem_iUnion₂.mpr ⟨x, abs_le.mp hm, hx⟩⟩
  exact measure_mono_null hU (measure_iUnion_null hzero)

end BlockBand.Critical.JointRecovery
