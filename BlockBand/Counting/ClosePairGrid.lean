module

public import BlockBand.Counting.ClosePairs
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Exact finite close-pair grid

For points restricted to `[-R,R]`, an explicit grid of at most `2R/a + 4` closed windows
of length `2a` covers every ordered pair at distance less than `a`.  Combined with a
`(2 K a)^2` second-factorial window estimate this bounds the expected number of close
pairs by `8 K^2 R a + 16 K^2 a^2`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Counting

open MeasureTheory
open scoped BigOperators

universe u

/-- Ordered distinct pairs of indices whose locations lie in `[-R,R]` and
are at distance strictly less than `a`.  This is the ordered sum in the
close-pair estimate. -/
def closePairIndices {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (R a : ℝ) : Finset (ι × ι) :=
  (orderedDistinctPairs (Finset.univ : Finset ι)).filter fun ij =>
    |u ij.1| ≤ R ∧ |u ij.2| ≤ R ∧ |u ij.1 - u ij.2| < a

/-- Number of cells in the explicit finite grid.  Three padding cells allow
the simple bound `gridSize ≤ 2R/a + 4` without an integrality case split. -/
def closePairGridSize (R a : ℝ) : ℕ :=
  ⌈2 * R / a⌉₊ + 3

/-- Left endpoint of grid window `j`.  Its underlying half-open cell is
`[-R-a+j a, -R+(j)a)`, and the covering window extends one further cell. -/
def closePairGridLo (R a : ℝ) (j : ℕ) : ℝ :=
  -R - a + j * a

/-- Right endpoint of grid window `j`; every grid window has length `2a`. -/
def closePairGridHi (R a : ℝ) (j : ℕ) : ℝ :=
  closePairGridLo R a j + 2 * a

/-- Indices whose point locations lie in the closed length-`2a` window
attached to cell `j`. -/
def closePairGridWindow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (R a : ℝ) (j : ℕ) : Finset ι :=
  Finset.univ.filter fun i =>
    closePairGridLo R a j ≤ u i ∧ u i ≤ closePairGridHi R a j

/-- A scalar pair `x ≤ y` in `[-R,R]` with gap `< a` is contained in one of
the grid's closed length-`2a` windows. -/
theorem exists_closePairGridWindow
    {x y R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a)
    (hxR : |x| ≤ R) (hgap : y - x < a) :
    ∃ j : Fin (closePairGridSize R a),
      closePairGridLo R a j ≤ x ∧ y ≤ closePairGridHi R a j := by
  let t : ℝ := (x + R + a) / a
  have hxlo : -R ≤ x := (abs_le.mp hxR).1
  have hxhi : x ≤ R := (abs_le.mp hxR).2
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (by linarith) ha.le
  let j : ℕ := ⌊t⌋₊
  have hjt : (j : ℝ) ≤ t := by
    exact Nat.floor_le ht0
  have htj : t < (j + 1 : ℕ) := by
    simpa [j] using (Nat.lt_succ_floor t)
  have hq0 : 0 ≤ 2 * R / a := div_nonneg (mul_nonneg (by norm_num) hR) ha.le
  have htq : t ≤ 2 * R / a + 1 := by
    dsimp [t]
    apply (div_le_iff₀ ha).2
    field_simp
    linarith
  have hqceil : 2 * R / a ≤ (⌈2 * R / a⌉₊ : ℕ) := Nat.le_ceil _
  have hjle : j ≤ ⌈2 * R / a⌉₊ + 1 := by
    apply Nat.floor_le_of_le
    have hqceil' : 2 * R / a ≤ (⌈2 * R / a⌉₊ : ℝ) := by
      exact_mod_cast hqceil
    norm_num
    linarith
  have hjlt : j < closePairGridSize R a := by
    dsimp [closePairGridSize]
    omega
  refine ⟨⟨j, hjlt⟩, ?_, ?_⟩
  · change -R - a + (j : ℝ) * a ≤ x
    have hmul := mul_le_mul_of_nonneg_right hjt ha.le
    dsimp [t] at hmul
    rw [div_mul_cancel₀ _ ha.ne'] at hmul
    linarith
  · have hxcell : x < closePairGridLo R a j + a := by
      change x < -R - a + (j : ℝ) * a + a
      have hmul := mul_lt_mul_of_pos_right htj ha
      dsimp [t] at hmul
      rw [div_mul_cancel₀ _ ha.ne'] at hmul
      push_cast at hmul
      linarith
    dsimp [closePairGridHi]
    linarith

/-- Every ordered close pair is covered by the off-diagonal pairs of the
finite grid windows. -/
theorem closePairIndices_subset_grid_biUnion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a) :
    closePairIndices u R a ⊆
      (Finset.univ : Finset (Fin (closePairGridSize R a))).biUnion fun j =>
        orderedDistinctPairs (closePairGridWindow u R a j) := by
  intro ij hij
  simp only [closePairIndices, Finset.mem_filter] at hij
  rcases hij with ⟨hp, hiR, hjR, hgap⟩
  have hne : ij.1 ≠ ij.2 := by
    simpa [orderedDistinctPairs] using hp
  rcases le_total (u ij.1) (u ij.2) with hle | hle
  · obtain ⟨j, hlo, hhi⟩ := exists_closePairGridWindow
      hR ha hiR (by
        rw [abs_lt] at hgap
        linarith [hgap.1])
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩
    simp [orderedDistinctPairs, closePairGridWindow, hne, hlo, hhi,
      hle.trans hhi, hlo.trans hle]
  · obtain ⟨j, hlo, hhi⟩ := exists_closePairGridWindow
      hR ha hjR (by
        rw [abs_lt] at hgap
        exact hgap.2)
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩
    simp [orderedDistinctPairs, closePairGridWindow, hne, hlo, hhi,
      hle.trans hhi, hlo.trans hle]

/-- Deterministic close-pair count bound by second descending factorials of
the length-`2a` grid-window counts. -/
theorem card_closePairIndices_le_grid_descFactorial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a) :
    (closePairIndices u R a).card ≤
      ∑ j : Fin (closePairGridSize R a),
        (closePairGridWindow u R a j).card.descFactorial 2 := by
  simpa using card_pairs_le_sum_descFactorial_of_subset_biUnion
    (closePairIndices u R a)
    (Finset.univ : Finset (Fin (closePairGridSize R a)))
    (fun j : Fin (closePairGridSize R a) => closePairGridWindow u R a j)
    (closePairIndices_subset_grid_biUnion u hR ha)

/-- Every grid window has width exactly `2a`. -/
theorem closePairGridHi_sub_lo (R a : ℝ) (j : ℕ) :
    closePairGridHi R a j - closePairGridLo R a j = 2 * a := by
  simp [closePairGridHi]

/-- The real cardinality of the padded grid is bounded by `2R/a+4`, the count
used in the proof of the close-pair estimate. -/
theorem closePairGridSize_cast_le
    {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a) :
    (closePairGridSize R a : ℝ) ≤ 2 * R / a + 4 := by
  have hq0 : 0 ≤ 2 * R / a :=
    div_nonneg (mul_nonneg (by norm_num) hR) ha.le
  have hc := Nat.ceil_lt_add_one hq0
  dsimp [closePairGridSize]
  norm_num at hc ⊢
  linarith

/-- The deterministic grid cardinality and the uniform length-`2a` window
estimate combine to the right-hand side `8 K^2 R a + 16 K^2 a^2` of the
close-pair estimate.  Here `K` is the rescaled one-point intensity constant;
the statement is uniform in all point configurations. -/
theorem closePairGrid_card_mul_square_le
    {R a K : ℝ} (hR : 0 ≤ R) (ha : 0 < a) :
    (closePairGridSize R a : ℝ) * (2 * K * a) ^ 2 ≤
      8 * K ^ 2 * R * a + 16 * K ^ 2 * a ^ 2 := by
  have hsquare : 0 ≤ (2 * K * a) ^ 2 := sq_nonneg _
  calc
    (closePairGridSize R a : ℝ) * (2 * K * a) ^ 2
        ≤ (2 * R / a + 4) * (2 * K * a) ^ 2 :=
      mul_le_mul_of_nonneg_right (closePairGridSize_cast_le hR ha) hsquare
    _ = 8 * K ^ 2 * R * a + 16 * K ^ 2 * a ^ 2 := by
      field_simp [ha.ne']
      ring

/-- Expectation form of the grid argument.  A uniform
second descending-factorial moment bound `(2 K a)^2` for every closed grid
window implies the close-pair bound `8 K^2 R a + 16 K^2 a^2`.  The locations may be
arbitrary random finite point configurations; measurability and integrability
are explicit hypotheses, and no particular random-matrix law is assumed. -/
theorem integral_closePairIndices_le_manuscript
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (u : Ω → ι → ℝ)
    {R a K : ℝ} (hR : 0 ≤ R) (ha : 0 < a)
    (hpairInt : Integrable
      (fun ω => ((closePairIndices (u ω) R a).card : ℝ)) μ)
    (hwindowInt : ∀ j : Fin (closePairGridSize R a),
      Integrable
        (fun ω =>
          ((closePairGridWindow (u ω) R a j).card.descFactorial 2 : ℝ)) μ)
    (hmoment : ∀ j : Fin (closePairGridSize R a),
      ∫ ω, ((closePairGridWindow (u ω) R a j).card.descFactorial 2 : ℝ) ∂μ
        ≤ (2 * K * a) ^ 2) :
    ∫ ω, ((closePairIndices (u ω) R a).card : ℝ) ∂μ ≤
      8 * K ^ 2 * R * a + 16 * K ^ 2 * a ^ 2 := by
  calc
    (∫ ω, ((closePairIndices (u ω) R a).card : ℝ) ∂μ) ≤
        ∑ _j : Fin (closePairGridSize R a), (2 * K * a) ^ 2 := by
      apply integral_pairCount_le_sum_sq_of_factorialMoments μ
        (Finset.univ : Finset (Fin (closePairGridSize R a)))
        (fun ω => (closePairIndices (u ω) R a).card)
        (fun j ω => (closePairGridWindow (u ω) R a j).card)
        (fun _ => 2 * K * a)
      · exact hpairInt
      · intro j hj
        exact hwindowInt j
      · intro ω
        simpa using card_closePairIndices_le_grid_descFactorial
          (u ω) hR ha
      · intro j hj
        exact hmoment j
    _ = (closePairGridSize R a : ℝ) * (2 * K * a) ^ 2 := by
      simp
    _ ≤ 8 * K ^ 2 * R * a + 16 * K ^ 2 * a ^ 2 :=
      closePairGrid_card_mul_square_le hR ha

end BlockBand.Counting
