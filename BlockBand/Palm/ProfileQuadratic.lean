module

public import BlockBand.Palm.PositiveHeightProfile
public import Mathlib.Analysis.Complex.Order

/-!
# Relative profile comparison for quadratic forms

The positive-height and zero-height quadratic forms `∑ |q_i|² f(a_i)` in spectral coordinates
are comparable within the factor `1 + h/b`, for every direction `q`; this gives relative error
bounds, fixed-order product bounds and Loewner comparisons after a complex congruence.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm

open Matrix
open scoped ComplexOrder

/-- The zero-height quadratic form in spectral coordinates. -/
def zeroHeightQuadratic {ι : Type*} [Fintype ι]
    (t b : ℝ) (a : ι → ℝ) (q : ι → ℂ) : ℝ :=
  ∑ i, ‖q i‖ ^ 2 * zeroHeightProfileEntry t b (a i)

/-- The positive-height quadratic form in the same coordinates. -/
def positiveHeightQuadratic {ι : Type*} [Fintype ι]
    (t b h : ℝ) (a : ι → ℝ) (q : ι → ℂ) : ℝ :=
  ∑ i, ‖q i‖ ^ 2 * positiveHeightProfileEntry t b h (a i)

/-- A nonzero direction has positive zero-height covariance, with no uniform
lower bound required or concluded. -/
theorem zeroHeightQuadratic_pos
    {ι : Type*} [Fintype ι] {t b : ℝ} (ht : 0 < t) (hb : 0 < b)
    (a : ι → ℝ) {q : ι → ℂ} (hq : q ≠ 0) :
    0 < zeroHeightQuadratic t b a q := by
  classical
  have hentry : ∀ i, 0 < zeroHeightProfileEntry t b (a i) := by
    intro i
    unfold zeroHeightProfileEntry
    positivity
  obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
    by_contra h
    push Not at h
    apply hq
    ext i
    exact h i
  apply Finset.sum_pos' (fun j _ => mul_nonneg (sq_nonneg _) (hentry j).le)
  exact ⟨i, Finset.mem_univ i, mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hi)) (hentry i)⟩

/-- Full directionwise multiplicative profile comparison. It includes the
zero direction and is uniform in all finite spectral coordinates. -/
theorem positiveHeightQuadratic_mem_Icc
    {ι : Type*} [Fintype ι] {t b h : ℝ}
    (ht : 0 < t) (hb : 0 < b) (hh : 0 ≤ h)
    (a : ι → ℝ) (q : ι → ℂ) :
    positiveHeightQuadratic t b h a q ∈ Set.Icc
      ((1 + h / b)⁻¹ * zeroHeightQuadratic t b a q)
      ((1 + h / b) * zeroHeightQuadratic t b a q) := by
  constructor
  · unfold positiveHeightQuadratic zeroHeightQuadratic
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have he := (positiveHeightProfileEntry_mem_Icc ht hb hh (a := a i)).1
    simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left he (sq_nonneg ‖q i‖)
  · unfold positiveHeightQuadratic zeroHeightQuadratic
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have he := (positiveHeightProfileEntry_mem_Icc ht hb hh (a := a i)).2
    simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left he (sq_nonneg ‖q i‖)

/-- Relative error of the full direction quadratic form. No lower bound on
q*Γq appears; mere nonzero direction is sufficient. -/
theorem abs_positiveHeightQuadratic_ratio_sub_one_le
    {ι : Type*} [Fintype ι] {t b h : ℝ}
    (ht : 0 < t) (hb : 0 < b) (hh : 0 ≤ h)
    (a : ι → ℝ) {q : ι → ℂ} (hq : q ≠ 0) :
    |positiveHeightQuadratic t b h a q / zeroHeightQuadratic t b a q - 1| ≤ h / b := by
  have hpos := zeroHeightQuadratic_pos ht hb a hq
  have heps : 0 ≤ h / b := div_nonneg hh hb.le
  have hbounds := positiveHeightQuadratic_mem_Icc ht hb hh a q
  have hlo := (le_div_iff₀ hpos).2 hbounds.1
  have hhi := (div_le_iff₀ hpos).2 hbounds.2
  have hinv : 1 - h / b ≤ (1 + h / b)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by linarith)]
    nlinarith [sq_nonneg (h / b)]
  rw [abs_le]
  constructor <;> linarith

/-- On a regular window `v ≥ c > 0`, the relative error is at most `h/(t c)`, with no
covariance lower bound. -/
theorem abs_positiveHeightQuadratic_ratio_sub_one_le_regular
    {ι : Type*} [Fintype ι] {t v c h : ℝ}
    (ht : 0 < t) (hc : 0 < c) (hcv : c ≤ v) (hh : 0 ≤ h)
    (a : ι → ℝ) {q : ι → ℂ} (hq : q ≠ 0) :
    |positiveHeightQuadratic t (t * v) h a q /
        zeroHeightQuadratic t (t * v) a q - 1| ≤ h / (t * c) := by
  apply (abs_positiveHeightQuadratic_ratio_sub_one_le ht
    (mul_pos ht (hc.trans_le hcv)) hh a hq).trans
  exact div_le_div_of_nonneg_left hh (mul_pos ht hc) (mul_le_mul_of_nonneg_left hcv ht.le)

/-- A product of complete quadratic forms inherits the exact fixed-order
multiplicative comparison, rather than only products of spectral entries. -/
theorem prod_positiveHeightQuadratic_mem_Icc
    {ι α : Type*} [Fintype ι] (s : Finset α)
    {t b h : ℝ} (ht : 0 < t) (hb : 0 < b) (hh : 0 ≤ h)
    (a : ι → ℝ) (q : α → ι → ℂ) :
    ∏ j ∈ s, positiveHeightQuadratic t b h a (q j) ∈ Set.Icc
      ((1 + h / b)⁻¹ ^ s.card * ∏ j ∈ s, zeroHeightQuadratic t b a (q j))
      ((1 + h / b) ^ s.card * ∏ j ∈ s, zeroHeightQuadratic t b a (q j)) := by
  have hz : ∀ j, 0 ≤ zeroHeightQuadratic t b a (q j) := by
    intro j
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (sq_nonneg _) (by unfold zeroHeightProfileEntry; positivity)
  have he : 0 ≤ 1 + h / b := by positivity
  have hp := fun j => positiveHeightQuadratic_mem_Icc ht hb hh a (q j)
  constructor
  · calc
      (1 + h / b)⁻¹ ^ s.card * ∏ j ∈ s, zeroHeightQuadratic t b a (q j) =
          ∏ j ∈ s, ((1 + h / b)⁻¹ * zeroHeightQuadratic t b a (q j)) := by
            simp only [Finset.prod_const, Finset.prod_mul_distrib]
      _ ≤ ∏ j ∈ s, positiveHeightQuadratic t b h a (q j) :=
        Finset.prod_le_prod₀ (fun j _ => mul_nonneg (inv_nonneg.mpr he) (hz j))
          (fun j _ => (hp j).1)
  · calc
      (∏ j ∈ s, positiveHeightQuadratic t b h a (q j)) ≤
          ∏ j ∈ s, ((1 + h / b) * zeroHeightQuadratic t b a (q j)) :=
        Finset.prod_le_prod₀ (fun j _ =>
          (mul_nonneg (inv_nonneg.mpr he) (hz j)).trans (hp j).1)
          (fun j _ => (hp j).2)
      _ = _ := by simp only [Finset.prod_const, Finset.prod_mul_distrib]

/-- Complete complex congruence lower Loewner comparison. Taking U to be
the eigenbasis gives the full covariance matrices' comparison once their
resolvent spectral representations are identified. U need not be unitary. -/
theorem conjugated_positiveHeightProfile_lower
    {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    {t b h : ℝ} (ht : 0 < t) (hb : 0 < b) (hh : 0 ≤ h)
    (a : ι → ℝ) (U : Matrix α ι ℂ) :
    (U * Matrix.diagonal (fun i =>
      (positiveHeightProfileEntry t b h (a i) : ℂ) -
        ((1 + h / b)⁻¹ * zeroHeightProfileEntry t b (a i) : ℝ)) * Uᴴ).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ (positiveHeightProfileEntry t b h (a i) : ℂ) -
    ((1 + h / b)⁻¹ * zeroHeightProfileEntry t b (a i) : ℝ)
  rw [← Complex.ofReal_sub]
  exact Complex.zero_le_real.mpr
    (sub_nonneg.mpr (positiveHeightProfileEntry_mem_Icc ht hb hh (a := a i)).1)

/-- Complete complex congruence upper Loewner comparison, at the same
variance/profile parameters and with arbitrary spectral coordinates. -/
theorem conjugated_positiveHeightProfile_upper
    {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    {t b h : ℝ} (ht : 0 < t) (hb : 0 < b) (hh : 0 ≤ h)
    (a : ι → ℝ) (U : Matrix α ι ℂ) :
    (U * Matrix.diagonal (fun i =>
      ((1 + h / b) * zeroHeightProfileEntry t b (a i) : ℝ) -
        (positiveHeightProfileEntry t b h (a i) : ℂ)) * Uᴴ).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ ((1 + h / b) * zeroHeightProfileEntry t b (a i) : ℝ) -
    (positiveHeightProfileEntry t b h (a i) : ℂ)
  rw [← Complex.ofReal_sub]
  exact Complex.zero_le_real.mpr
    (sub_nonneg.mpr (positiveHeightProfileEntry_mem_Icc ht hb hh (a := a i)).2)

end BlockBand.Palm
