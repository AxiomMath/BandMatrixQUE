module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.Clause1CyclicControl
public import Mathlib

/-!
# Cyclic Green-kernel differences for ER clause (vi)

This module isolates the cancellation which is specific to a nearest-neighbour
cyclic profile.  A naive difference of two Green bounds loses one power of the
square-root height.  Instead, the factor `1-ρ` arising from the difference of
neighbouring two-path numerators cancels the same factor in the recurrence
jump.  The remaining constant depends only on the fixed bond weight `b`.

The finite-cycle wrap denominator is also bounded below at the clause-(vi)
threshold `η ≥ n⁻²`; in particular neither estimate depends on the length or
parity of the cycle.

Source: Erdős–Riabov, *The Zigzag Strategy for Random Band Matrices*,
arXiv:2506.06441v1, Definition 2.4(vi), and the proof of the concrete cyclic
profile in Proposition 2.8(i).  In the block-band paper this is the
identity immediately before the neighbouring-entry/telescoping argument for
(2.26).
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERClause6CyclicDifference

open ERFourierInverse ERFourierAlgebra ERNearestNeighbor ERCyclicDecay ERJumpNormalization ERClause1 ERHerglotz

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- A positive numerical lower bound for the cyclic wrap denominator once
`n √η ≥ 1`. -/
def fixedWrapFloor : ℝ :=
  min (1 - Real.exp (-1)) (1 / 4)

lemma fixedWrapFloor_pos : 0 < fixedWrapFloor := by
  unfold fixedWrapFloor
  apply lt_min
  · rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  · norm_num

/-- The noncritical characteristic factor can equivalently be expressed using
`1+ρ`.  This is the algebra behind the source identity
`(1-q)/sqrt(discriminant) = q/(ab(1+q))`. -/
theorem secondFactor_eq_root_one_add_sq (p : Params) {α ρ : ℂ}
    (hρ0 : ρ ≠ 0)
    (hchar : recurrenceBond p α * ρ ^ 2 -
      recurrenceDiagonal p α * ρ + recurrenceBond p α = 0) :
    1 - α * ((p.c - 2 * p.b : ℝ) : ℂ) =
      α * p.b * (1 + ρ) ^ 2 / ρ := by
  unfold recurrenceBond recurrenceDiagonal at hchar
  field_simp [hρ0]
  push_cast at hchar ⊢
  linear_combination -hchar

/-- Exact cancellation of the neighbouring numerator factor against the
recurrence jump. -/
theorem alpha_mul_one_sub_root_div_jump (p : Params) {α ρ : ℂ}
    (hα0 : α ≠ 0) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1)
    (hplus : 1 + ρ ≠ 0) :
    α * (1 - ρ) / recurrenceJump p α ρ =
      ρ / ((p.b : ℂ) * (1 + ρ)) := by
  have hb0 : (p.b : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt p.b_pos
  unfold recurrenceJump recurrenceBond
  have hinv :
      ρ⁻¹ - ρ = ρ⁻¹ * (1 - ρ) * (1 + ρ) := by
    field_simp [hρ0]
    ring
  rw [hinv]
  field_simp [hα0, hb0, hρ0, hρ1, hplus]

/-- Fixed-bond bound for the cancelled neighbouring Green prefactor.  The
constant involves only `b` and the transverse margin `1-|c-2b|`; it is
independent of the spectral multiplier, cycle length, width, and parity. -/
theorem norm_alpha_mul_one_sub_root_div_jump_le_fixedBond
    (p : Params) {α ρ : ℂ}
    (hα0 : α ≠ 0) (hα : ‖α‖ < 1) (hρ0 : ρ ≠ 0)
    (hρ : ‖ρ‖ < 1)
    (hchar : recurrenceBond p α * ρ ^ 2 -
      recurrenceDiagonal p α * ρ + recurrenceBond p α = 0) :
    ‖α * (1 - ρ) / recurrenceJump p α ρ‖ ≤
      1 / Real.sqrt (p.b * jumpBondMargin p) := by
  have hρ1 : ρ ≠ 1 := by
    intro h
    subst ρ
    norm_num at hρ
  have hplus : 1 + ρ ≠ 0 := by
    intro h
    have hsecond := jumpBondMargin_le_secondFactor p hα
    rw [secondFactor_eq_root_one_add_sq p hρ0 hchar, h] at hsecond
    norm_num at hsecond
    exact (not_lt_of_ge hsecond) (jumpBondMargin_pos p)
  rw [alpha_mul_one_sub_root_div_jump p hα0 hρ0 hρ1 hplus]
  rw [norm_div, norm_mul]
  have hbNorm : ‖(p.b : ℂ)‖ = p.b := by simp [abs_of_pos p.b_pos]
  rw [hbNorm]
  have hsecond := jumpBondMargin_le_secondFactor p hα
  rw [secondFactor_eq_root_one_add_sq p hρ0 hchar, norm_div,
    norm_mul, norm_mul, norm_pow] at hsecond
  rw [show ‖(p.b : ℂ)‖ = p.b by simp [abs_of_pos p.b_pos]] at hsecond
  have hr0 : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  have hb0 : 0 < p.b := p.b_pos
  have hm0 : 0 < jumpBondMargin p := jumpBondMargin_pos p
  have hs0 : 0 < Real.sqrt (p.b * jumpBondMargin p) := by positivity
  have hone : ‖α‖ ≤ 1 := hα.le
  have hplus0 : 0 < ‖1 + ρ‖ := by
    rw [norm_pos_iff]
    intro h
    have heq : ρ = -1 := by linear_combination h
    rw [heq] at hρ
    norm_num at hρ
  have hcore :
      jumpBondMargin p * ‖ρ‖ ≤ p.b * ‖1 + ρ‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hsecond hr0.le
    rw [div_mul_cancel₀ _ (ne_of_gt hr0)] at hmul
    exact hmul.trans (by
      gcongr
      simpa using mul_le_mul_of_nonneg_right hone p.b_pos.le)
  apply (div_le_div_iff₀ (mul_pos hb0 hplus0) hs0).2
  have hsquare :
      (Real.sqrt (p.b * jumpBondMargin p)) ^ 2 =
        p.b * jumpBondMargin p :=
    Real.sq_sqrt (mul_nonneg hb0.le hm0.le)
  have hrle : ‖ρ‖ ≤ 1 := hρ.le
  have htarget :
      (‖ρ‖ * Real.sqrt (p.b * jumpBondMargin p)) ^ 2 ≤
        (p.b * ‖1 + ρ‖) ^ 2 := by
    rw [mul_pow, hsquare, mul_pow]
    have hmul := mul_le_mul_of_nonneg_left hcore
      (mul_nonneg p.b_pos.le (norm_nonneg ρ))
    have hrhs :
        p.b * ‖ρ‖ * (p.b * ‖1 + ρ‖ ^ 2) ≤
          p.b ^ 2 * ‖1 + ρ‖ ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg p.b) (sq_nonneg ‖1 + ρ‖)]
    nlinarith
  simp only [one_mul]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp htarget

/-- Successive two-path numerators have the exact `1-ρ` factor, including
at the wrap edge `d=n-1`. -/
theorem cyclicTwoPathNumerator_succ_sub (p : Params) (ρ : ℂ)
    {d : ℕ} (hd : d < p.n) :
    cyclicTwoPathNumerator p ρ (d + 1) -
        cyclicTwoPathNumerator p ρ d =
      (1 - ρ) * (ρ ^ (p.n - d - 1) - ρ ^ d) := by
  unfold cyclicTwoPathNumerator
  have hdn' : p.n - (d + 1) = p.n - d - 1 := by omega
  have hp : ρ ^ (p.n - d) = ρ ^ (p.n - d - 1) * ρ := by
    have hdn : p.n - d = (p.n - d - 1) + 1 := by omega
    calc
      ρ ^ (p.n - d) = ρ ^ ((p.n - d - 1) + 1) :=
        congrArg (fun k : ℕ => ρ ^ k) hdn
      _ = ρ ^ (p.n - d - 1) * ρ := pow_succ _ _
  nth_rewrite 1 [pow_succ]
  nth_rewrite 1 [hdn']
  nth_rewrite 1 [hp]
  ring

/-- At the clause-(vi) threshold, the exact cyclic wrap denominator is bounded
below by a fixed positive number. -/
theorem fixedWrapFloor_le_contracting_denominator
    (p : Params) {α : ℂ} {η : ℝ}
    (hα0 : α ≠ 0) (hα : ‖α‖ < 1)
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hthreshold : (1 / (p.n : ℝ)) ^ 2 ≤ η)
    (hmargin : η / 4 ≤ 1 - ‖α‖) :
    fixedWrapFloor ≤
      ‖1 - contractingRecurrenceRoot p α ^ p.n‖ := by
  have hrate : Real.sqrt η / 2 ≤ rootGapRate p α :=
    sqrt_height_div_two_le_rootGapRate p hη0 hη1 hmargin
  have hnpos : 0 < (p.n : ℝ) := by exact_mod_cast p.n_pos
  have hs : 1 / (p.n : ℝ) ≤ Real.sqrt η := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 1 / (p.n : ℝ))]
    exact Real.sqrt_le_sqrt hthreshold
  have hquarter : (1 / 4 : ℝ) ≤
      ((p.n : ℝ) * rootGapRate p α) / 2 := by
    have hone : 1 ≤ (p.n : ℝ) * Real.sqrt η := by
      have := mul_le_mul_of_nonneg_left hs hnpos.le
      field_simp at this
      exact this
    have hhalf : (1 / 2 : ℝ) ≤
        (p.n : ℝ) * rootGapRate p α := by
      have := mul_le_mul_of_nonneg_left hrate hnpos.le
      nlinarith
    linarith
  have hwrap := min_rootGap_wrapScale_le_contracting_denominator p hα0 hα
  exact (min_le_min le_rfl hquarter).trans hwrap

/-- A neighbouring entry of the cyclic Green kernel gains exactly the
square-root factor which is absent from a pointwise Green estimate.  Once the
wrap scale is above the clause-(vi) threshold, its constant depends only on
the fixed bond weight.  The two powers are the two oriented paths from the
two neighbouring sites to the source. -/
theorem norm_alpha_mul_fourierGreenKernel_add_one_sub_le
    (p : Params) {α : ℂ} {η : ℝ}
    (hα0 : α ≠ 0) (hα : ‖α‖ < 1)
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hthreshold : (1 / (p.n : ℝ)) ^ 2 ≤ η)
    (hmargin : η / 4 ≤ 1 - ‖α‖)
    (x y : ZMod p.n) :
    let ρ := contractingRecurrenceRoot p α
    let d := orientedBlockDistance p x y
    ‖α * (fourierGreenKernel p α (x + 1) y -
      fourierGreenKernel p α x y)‖ ≤
      (1 / (Real.sqrt (p.b * jumpBondMargin p) * fixedWrapFloor)) *
        (‖ρ‖ ^ (p.n - d - 1) + ‖ρ‖ ^ d) := by
  dsimp only
  let ρ := contractingRecurrenceRoot p α
  let d := orientedBlockDistance p x y
  have hρ0 : ρ ≠ 0 := contractingRecurrenceRoot_ne_zero p hα0
  have hρ : ‖ρ‖ < 1 :=
    norm_contractingRecurrenceRoot_lt_one p hα0 hα
  have hd : d < p.n := ZMod.val_lt (x - y)
  have hadd := orientedBlockDistance_add_one p x y
  have hnum := cyclicTwoPathNumerator_add_mod p ρ hd
  rw [← hadd] at hnum
  have hgreen₁ :=
    fourierGreenKernel_eq_cyclicResolventCandidate p hα0 hα (x + 1) y
  have hgreen₀ :=
    fourierGreenKernel_eq_cyclicResolventCandidate p hα0 hα x y
  rw [hgreen₁, hgreen₀]
  have hwrap0 : 1 - ρ ^ p.n ≠ 0 :=
    one_sub_pow_ne_zero hρ p.n p.n_pos
  have hjump0 : recurrenceJump p α ρ ≠ 0 :=
    recurrenceJump_contracting_ne_zero p hα0 hα
  have hfactor :
      α * (cyclicResolventCandidate p α ρ (x + 1) y -
          cyclicResolventCandidate p α ρ x y) =
        (α * (1 - ρ) / recurrenceJump p α ρ) *
          ((ρ ^ (p.n - d - 1) - ρ ^ d) / (1 - ρ ^ p.n)) := by
    unfold cyclicResolventCandidate cyclicTwoPathKernel
    rw [hnum, show orientedBlockDistance p x y = d by rfl]
    field_simp [hwrap0, hjump0]
    rw [cyclicTwoPathNumerator_succ_sub p ρ hd]
  change ‖α * (cyclicResolventCandidate p α ρ (x + 1) y -
    cyclicResolventCandidate p α ρ x y)‖ ≤
      (1 / (Real.sqrt (p.b * jumpBondMargin p) * fixedWrapFloor)) *
        (‖ρ‖ ^ (p.n - d - 1) + ‖ρ‖ ^ d)
  rw [hfactor, norm_mul]
  have hpref :=
    norm_alpha_mul_one_sub_root_div_jump_le_fixedBond p hα0 hα hρ0 hρ
      (contractingRecurrenceRoot_characteristic p hα0)
  have hwrap :=
    fixedWrapFloor_le_contracting_denominator p hα0 hα hη0 hη1
      hthreshold hmargin
  have hfloor0 : 0 < fixedWrapFloor := fixedWrapFloor_pos
  have hdiff :
      ‖ρ ^ (p.n - d - 1) - ρ ^ d‖ ≤
        ‖ρ‖ ^ (p.n - d - 1) + ‖ρ‖ ^ d := by
    simpa only [norm_pow] using
      norm_sub_le (ρ ^ (p.n - d - 1)) (ρ ^ d)
  calc
    ‖α * (1 - ρ) / recurrenceJump p α ρ‖ *
        ‖(ρ ^ (p.n - d - 1) - ρ ^ d) / (1 - ρ ^ p.n)‖ =
      ‖α * (1 - ρ) / recurrenceJump p α ρ‖ *
        (‖ρ ^ (p.n - d - 1) - ρ ^ d‖ / ‖1 - ρ ^ p.n‖) := by
          congr 1
          rw [norm_div]
    _ ≤
      (1 / Real.sqrt (p.b * jumpBondMargin p)) *
        ((‖ρ‖ ^ (p.n - d - 1) + ‖ρ‖ ^ d) /
          ‖1 - ρ ^ p.n‖) := by gcongr
    _ ≤ (1 / Real.sqrt (p.b * jumpBondMargin p)) *
        ((‖ρ‖ ^ (p.n - d - 1) + ‖ρ‖ ^ d) /
          fixedWrapFloor) := by
      gcongr
    _ = (1 /
        (Real.sqrt (p.b * jumpBondMargin p) * fixedWrapFloor)) *
          (‖ρ‖ ^ (p.n - d - 1) + ‖ρ‖ ^ d) := by
      field_simp [ne_of_gt hfloor0,
        ne_of_gt (Real.sqrt_pos.2
          (mul_pos p.b_pos (jumpBondMargin_pos p)))]

/-- Telescoping on a cyclic group.  This elementary form is used after the
neighbouring Green estimate, before comparing intermediate distances with the
two endpoint distances. -/
theorem norm_sub_le_sum_neighboring (p : Params) (f : ZMod p.n → ℂ)
    (x : ZMod p.n) : ∀ r : ℕ,
    ‖f (x + r) - f x‖ ≤
      ∑ j ∈ Finset.range r, ‖f (x + (j + 1)) - f (x + j)‖ := by
  intro r
  induction r with
  | zero => simp
  | succ r ihr =>
      rw [Finset.sum_range_succ]
      calc
        ‖f (x + (↑(r + 1) : ZMod p.n)) - f x‖ =
            ‖f (x + (r + 1)) - f x‖ := by simp
        _ ≤
            ‖f (x + (r + 1)) - f (x + r)‖ +
              ‖f (x + r) - f x‖ := by
                calc
                  ‖f (x + (r + 1)) - f x‖ =
                      ‖(f (x + (r + 1)) - f (x + r)) +
                        (f (x + r) - f x)‖ := by
                          congr 1
                          ring
                  _ ≤ _ := norm_add_le _ _
        _ ≤ ‖f (x + (r + 1)) - f (x + r)‖ +
              ∑ j ∈ Finset.range r,
                ‖f (x + (j + 1)) - f (x + j)‖ :=
          by simpa [add_comm] using
            add_le_add_right ihr
              ‖f (x + (r + 1)) - f (x + r)‖
        _ = (∑ j ∈ Finset.range r,
              ‖f (x + (j + 1)) - f (x + j)‖) +
              ‖f (x + (r + 1)) - f (x + r)‖ := by ring

end BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERClause6CyclicDifference
