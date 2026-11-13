module

public import BlockBand.SourceProcess.SourceProcessLaw.EarlyAlg

/-!
# The early weights sum to `O(s/W)`

For a test `q ≤ Q` on `[0,T]`, the weight of each birth index `k < ⌊sW⌋` lost by truncating `q` to
`[s,T]` is at most `Q/W²`, and the others vanish (`earlyWeight_le`); summing gives
`sum_earlyWeight_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourceProcessLaw

theorem earlyWeight_le {W : ℕ} (hW : 0 < W) {s T Q : ℝ} {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    (hQ : ∀ x ∈ Set.Icc 0 T, q x ≤ Q) {k : ℕ} (hk : k < ⌊(W : ℝ) * T⌋₊) :
    earlyWeight W s T q k ≤ if k < ⌊s * W⌋₊ then Q / (W : ℝ) ^ 2 else 0 := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  set x := ((k + 1 : ℕ) : ℝ) / W
  have hx0 : 0 ≤ x := by positivity
  have hxT : x ≤ T := by
    have h1 : ((k + 1 : ℕ) : ℝ) ≤ W * T := by
      have : k + 1 ≤ ⌊(W : ℝ) * T⌋₊ := hk
      exact (Nat.cast_le.2 this).trans (Nat.floor_le (by
        by_contra hneg
        push Not at hneg
        rw [Nat.floor_of_nonpos hneg.le] at hk
        exact Nat.not_lt_zero _ hk))
    rw [div_le_iff₀ hWr]; linarith
  have hind : 0 ≤ Set.indicator (Set.Icc s T) q x := Set.indicator_nonneg (fun y _ => hq0 y) x
  split_ifs with hks
  · unfold earlyWeight
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    linarith [hQ x ⟨hx0, hxT⟩]
  · push Not at hks
    have hsx : s ≤ x := by
      have h1 : s * W < ((k + 1 : ℕ) : ℝ) := by
        have := Nat.lt_floor_add_one (s * W)
        have h2 : (⌊s * W⌋₊ : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hks
        linarith
      rw [le_div_iff₀ hWr]; linarith
    unfold earlyWeight
    rw [Set.indicator_of_mem (show x ∈ Set.Icc s T from ⟨hsx, hxT⟩), sub_self, zero_div]

theorem sum_earlyWeight_le {W : ℕ} (hW : 0 < W) {s T Q : ℝ} (hs : 0 ≤ s) (hQ0 : 0 ≤ Q)
    {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x) (hQ : ∀ x ∈ Set.Icc 0 T, q x ≤ Q) :
    ∑ k ∈ Finset.range ⌊(W : ℝ) * T⌋₊, earlyWeight W s T q k ≤ s * Q / W := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  set m := ⌊s * W⌋₊
  calc ∑ k ∈ Finset.range ⌊(W : ℝ) * T⌋₊, earlyWeight W s T q k
      ≤ ∑ k ∈ Finset.range ⌊(W : ℝ) * T⌋₊, (if k < m then Q / (W : ℝ) ^ 2 else 0) :=
        Finset.sum_le_sum fun k hk => earlyWeight_le hW hq0 hQ (Finset.mem_range.1 hk)
    _ = ((Finset.range ⌊(W : ℝ) * T⌋₊).filter (· < m)).card * (Q / (W : ℝ) ^ 2) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (m : ℝ) * (Q / (W : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have : ((Finset.range ⌊(W : ℝ) * T⌋₊).filter (· < m)).card ≤ (Finset.range m).card :=
          Finset.card_le_card fun k hk => Finset.mem_range.2 (Finset.mem_filter.1 hk).2
        rw [Finset.card_range] at this
        exact_mod_cast this
    _ ≤ (s * W) * (Q / (W : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by positivity)
    _ = s * Q / W := by field_simp

end BlockBand.SourceProcess.SourceProcessLaw
