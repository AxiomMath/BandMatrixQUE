module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.FourierCriterion
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.SpectralTailAdapter
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.ShiftedHolderProduct

/-!
# Structural consequences of the APSSS dominant-coordinate selection

This module supplies the finite ordered-energy facts used between the APSSS
three-way choice and the analytic tail estimate.  It constructs the canonical
split rank, treats the zero-, one-, and two-coordinate branches separately, and
proves the normalization and exponent bound for the remaining tail.  It makes
no probabilistic or shifted-integral assumption.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

/-- Energy carried by the coordinate whose zero-based index is `k`.  It is
zero when that coordinate does not exist. -/
def coefficientEnergyAt {n : ℕ} (E b : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ j : Fin n, if (j : ℕ) = k then coefficientEnergy E b j else 0

/-- The APSSS split rank, with the source's two successive `1/10` tests. -/
def dominantSplitRank {n : ℕ} (E b : Fin n → ℝ) : ℕ :=
  if coefficientEnergyAt E b 0 ≤ tailEnergy E b 1 / 10 then 0
  else if coefficientEnergyAt E b 1 ≤ tailEnergy E b 2 / 10 then 1 else 2

/-- The canonical split rank is one of `0,1,2`. -/
theorem dominantSplitRank_le_two {n : ℕ} (E b : Fin n → ℝ) :
    dominantSplitRank E b ≤ 2 := by
  unfold dominantSplitRank
  split_ifs <;> omega

/-- Ordered coefficients together with the canonical rank satisfy the
`DominantSelection` predicate. -/
theorem dominantSelection_dominantSplitRank {n : ℕ} (E b : Fin n → ℝ)
    (hord : Antitone (fun j : Fin n => coefficientEnergy E b j)) :
    DominantSelection E b (dominantSplitRank E b) := by
  constructor
  · simpa [coefficientEnergy] using hord
  · simp only [dominantSplitRank, coefficientEnergyAt, tailEnergy,
      coefficientEnergy]
    rfl

/-- If a coordinate with index `k` exists, `coefficientEnergyAt` is exactly
its coefficient energy. -/
theorem coefficientEnergyAt_eq {n : ℕ} (E b : Fin n → ℝ)
    (j : Fin n) (k : ℕ) (hjk : (j : ℕ) = k) :
    coefficientEnergyAt E b k = coefficientEnergy E b j := by
  unfold coefficientEnergyAt
  rw [Finset.sum_eq_single j]
  · simp [hjk]
  · intro i _ hij
    by_cases hik : (i : ℕ) = k
    · exfalso
      apply hij
      apply Fin.ext
      omega
    · simp [hik]
  · simp

/-- The tail beginning at `k` is the `k`th coordinate energy plus the tail
beginning at `k+1`, including when `k` lies beyond the dimension. -/
theorem tailEnergy_eq_coefficientEnergyAt_add_tailEnergy_succ {n : ℕ}
    (E b : Fin n → ℝ) (k : ℕ) :
    tailEnergy E b k = coefficientEnergyAt E b k + tailEnergy E b (k + 1) := by
  unfold tailEnergy coefficientEnergyAt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hlt : k ≤ (j : ℕ)
  · by_cases heq : (j : ℕ) = k
    · simp [heq]
    · have hs : k + 1 ≤ (j : ℕ) := by omega
      simp [hlt, heq, hs]
  · have heq : (j : ℕ) ≠ k := by omega
    have hs : ¬k + 1 ≤ (j : ℕ) := by omega
    simp [hlt, heq, hs]

/-- The strict-index tail notation in the source is the same sum as
`tailEnergy` at the successor rank. -/
theorem sum_coefficientEnergy_gt_eq_tailEnergy_succ {n : ℕ}
    (E b : Fin n → ℝ) (k : ℕ) :
    (∑ j : Fin n, if k < (j : ℕ) then coefficientEnergy E b j else 0) =
      tailEnergy E b (k + 1) := by
  unfold tailEnergy
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : k < (j : ℕ)
  · have hs : k + 1 ≤ (j : ℕ) := by omega
    simp [hj, hs]
  · have hs : ¬k + 1 ≤ (j : ℕ) := by omega
    simp [hj, hs]

/-- Antitonicity makes every tail coefficient no larger than the energy at
its tail's first index. -/
theorem coefficientEnergy_le_coefficientEnergyAt_of_le {n : ℕ}
    (E b : Fin n → ℝ)
    (hord : Antitone (fun j : Fin n => coefficientEnergy E b j))
    (k : ℕ) (j : Fin n) (hkj : k ≤ (j : ℕ)) :
    coefficientEnergy E b j ≤ coefficientEnergyAt E b k := by
  let i : Fin n := ⟨k, lt_of_le_of_lt hkj j.isLt⟩
  rw [coefficientEnergyAt_eq E b i k rfl]
  apply hord
  change k ≤ (j : ℕ)
  exact hkj

/-- A failed APSSS dominance test forces the tested coefficient to be
strictly positive. -/
theorem coefficientEnergyAt_pos_of_not_le_tail {n : ℕ}
    (E b : Fin n → ℝ) (k : ℕ)
    (h : ¬ coefficientEnergyAt E b k ≤ tailEnergy E b (k + 1) / 10) :
    0 < coefficientEnergyAt E b k := by
  have htail := tailEnergy_nonneg E b (k + 1)
  linarith

/-- Every coordinate selected before the canonical split has a
nonzero quadratic coefficient.  This includes the vacuous rank-zero branch
and does not require padding a low-dimensional spectrum. -/
theorem dominantSplitRank_coefficient_ne_zero {n : ℕ} (E b : Fin n → ℝ)
    (j : Fin n) (hj : (j : ℕ) < dominantSplitRank E b) : E j ≠ 0 := by
  unfold dominantSplitRank at hj
  split_ifs at hj with h0 h1
  · omega
  · have hj0 : (j : ℕ) = 0 := by omega
    have hpos := coefficientEnergyAt_pos_of_not_le_tail E b 0 h0
    rw [coefficientEnergyAt_eq E b j 0 hj0] at hpos
    intro hE
    simp [coefficientEnergy, hE] at hpos
  · have hpos0 := coefficientEnergyAt_pos_of_not_le_tail E b 0 h0
    have hpos1 := coefficientEnergyAt_pos_of_not_le_tail E b 1 h1
    have hj01 : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
    rcases hj01 with hj0 | hj1
    · rw [coefficientEnergyAt_eq E b j 0 hj0] at hpos0
      intro hE
      simp [coefficientEnergy, hE] at hpos0
    · rw [coefficientEnergyAt_eq E b j 1 hj1] at hpos1
      intro hE
      simp [coefficientEnergy, hE] at hpos1

/-- APSSS's tail scale `ν`: the nonnegative square root of the selected tail
energy. -/
noncomputable def dominantTailScale {n : ℕ} (E b : Fin n → ℝ) : ℝ :=
  Real.sqrt (tailEnergy E b (dominantSplitRank E b))

/-- Exact `ν²` normalization, valid also for a trivial zero tail. -/
theorem dominantTailScale_sq {n : ℕ} (E b : Fin n → ℝ) :
    dominantTailScale E b ^ 2 = tailEnergy E b (dominantSplitRank E b) := by
  unfold dominantTailScale
  exact Real.sq_sqrt (tailEnergy_nonneg E b _)

/-- In the nontrivial APSSS branch (at least three nonzero coefficients), the
selected tail energy is positive. -/
theorem dominantSplitRank_tailEnergy_pos {n : ℕ} (E b : Fin n → ℝ)
    (hthree : 3 ≤ (Finset.univ.filter fun j : Fin n => E j ≠ 0).card) :
    0 < tailEnergy E b (dominantSplitRank E b) := by
  exact selectionTailEnergy_pos E b (dominantSplitRank E b)
    (dominantSplitRank_le_two E b) hthree

/-- Consequently the normalized tail scale is positive in the nontrivial
branch. -/
theorem dominantTailScale_pos {n : ℕ} (E b : Fin n → ℝ)
    (hthree : 3 ≤ (Finset.univ.filter fun j : Fin n => E j ≠ 0).card) :
    0 < dominantTailScale E b := by
  unfold dominantTailScale
  exact Real.sqrt_pos.2 (dominantSplitRank_tailEnergy_pos E b hthree)

/-- The source's two dominance tests imply the exponent numerator bound for
every selected tail coordinate. -/
theorem dominantSelection_three_sub_mul_coefficientEnergy_le_tailEnergy
    {n : ℕ} (E b : Fin n → ℝ) (r : ℕ)
    (hsel : DominantSelection E b r) (j : Fin n) (hjr : r ≤ (j : ℕ)) :
    ((3 - r : ℕ) : ℝ) * coefficientEnergy E b j ≤ tailEnergy E b r := by
  rcases hsel with ⟨hord, hr⟩
  have hrank : r = dominantSplitRank E b := by
    rw [hr]
    change
      (if coefficientEnergyAt E b 0 ≤
          (∑ j : Fin n, if 0 < (j : ℕ) then coefficientEnergy E b j else 0) / 10
        then 0
        else if coefficientEnergyAt E b 1 ≤
          (∑ j : Fin n, if 1 < (j : ℕ) then coefficientEnergy E b j else 0) / 10
        then 1 else 2) = dominantSplitRank E b
    rw [sum_coefficientEnergy_gt_eq_tailEnergy_succ E b 0,
      sum_coefficientEnergy_gt_eq_tailEnergy_succ E b 1]
    rfl
  rw [hrank] at hjr ⊢
  unfold dominantSplitRank at hjr ⊢
  split_ifs with h0 h1
  ·
    have hc := coefficientEnergy_le_coefficientEnergyAt_of_le E b
      (by simpa [coefficientEnergy] using hord) 0 j (Nat.zero_le _)
    have htail := tailEnergy_nonneg E b 1
    rw [tailEnergy_eq_coefficientEnergyAt_add_tailEnergy_succ E b 0]
    norm_num at *
    nlinarith
  ·
    simp [h0, h1] at hjr
    have hc := coefficientEnergy_le_coefficientEnergyAt_of_le E b
      (by simpa [coefficientEnergy] using hord) 1 j hjr
    have htail := tailEnergy_nonneg E b 2
    rw [tailEnergy_eq_coefficientEnergyAt_add_tailEnergy_succ E b 1]
    norm_num at *
    nlinarith
  · have hsingle := Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun k : Fin n =>
        if 2 ≤ (k : ℕ) then coefficientEnergy E b k else 0)
      (fun k _ => by
        by_cases hk : 2 ≤ (k : ℕ)
        · simp [hk, coefficientEnergy_nonneg E b k]
        · simp [hk])
      (Finset.mem_univ j)
    simp [h0, h1] at hjr
    simpa [hjr, tailEnergy] using hsingle

/-- The exact Hölder-exponent side condition consumed by the shifted tail
product.  It also holds in the trivial-tail case, where real division by zero
totalizes every tail weight to zero. -/
theorem dominantSelection_three_sub_mul_tailHolderWeight_le_one
    {n : ℕ} (E b : Fin n → ℝ) (r : ℕ) (ν : ℝ)
    (hsel : DominantSelection E b r)
    (hν : ν ^ 2 = tailEnergy E b r)
    (j : Fin n) (hjr : r ≤ (j : ℕ)) :
    ((3 - r : ℕ) : ℝ) * tailHolderWeight E b ν j ≤ 1 := by
  have hnum :=
    dominantSelection_three_sub_mul_coefficientEnergy_le_tailEnergy
      E b r hsel j hjr
  rw [← hν] at hnum
  change ((3 - r : ℕ) : ℝ) *
      (coefficientEnergy E b j / ν ^ 2) ≤ 1
  by_cases hν0 : ν = 0
  · simp [hν0]
  · calc
      ((3 - r : ℕ) : ℝ) * (coefficientEnergy E b j / ν ^ 2) =
          (((3 - r : ℕ) : ℝ) * coefficientEnergy E b j) / ν ^ 2 := by
            ring
      _ ≤ 1 := (div_le_one (sq_pos_of_ne_zero hν0)).2 hnum

end PSSSNative.BlockBand.PSSS
