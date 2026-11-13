module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.NearestNeighborResolvent
public import Mathlib

/-!
# Finite cyclic resolvent decay

The two oriented paths on a cycle produce the numerator
`ρ^d + ρ^(n-d)`.  This module records its exact wraparound denominator,
the jump normalization for the nearest-neighbour recurrence, and
dimension/parity-uniform norm estimates.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERCyclicDecay

open ERDiscreteFourier ERFourierInverse ERFourierAlgebra ERCharacterAngle ERNearestNeighbor

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Oriented representative of the block displacement. -/
def orientedBlockDistance (p : Params) (x y : ZMod p.n) : ℕ :=
  (x - y).val

/-- Forward translation increments the oriented representative modulo `n`. -/
theorem orientedBlockDistance_add_one (p : Params) (x y : ZMod p.n) :
    orientedBlockDistance p (x + 1) y =
      (orientedBlockDistance p x y + 1) % p.n := by
  let _ : Fact (1 < p.n) := ⟨lt_of_lt_of_le (by norm_num) p.n_ge_four⟩
  unfold orientedBlockDistance
  rw [show x + 1 - y = (x - y) + 1 by ring, ZMod.val_add,
    ZMod.val_one]

/-- Backward translation decrements the oriented representative modulo `n`. -/
theorem orientedBlockDistance_sub_one (p : Params) (x y : ZMod p.n) :
    orientedBlockDistance p (x - 1) y =
      (orientedBlockDistance p x y + (p.n - 1)) % p.n := by
  let _ : Fact (1 < p.n) := ⟨lt_of_lt_of_le (by norm_num) p.n_ge_four⟩
  unfold orientedBlockDistance
  rw [show x - 1 - y = (x - y) + (-1) by ring, ZMod.val_add,
    ZMod.neg_val]
  simp [ZMod.val_one]

/-- Sum of the two finite cyclic paths with displacement `d`. -/
def cyclicTwoPathNumerator (p : Params) (ρ : ℂ) (d : ℕ) : ℂ :=
  ρ ^ d + ρ ^ (p.n - d)

/-- Wraparound-normalized two-path kernel before the source jump
normalization is applied. -/
def cyclicTwoPathKernel (p : Params) (ρ : ℂ) (x y : ZMod p.n) : ℂ :=
  cyclicTwoPathNumerator p ρ (orientedBlockDistance p x y) /
    (1 - ρ ^ p.n)

/-- The jump coefficient in the inhomogeneous recurrence. -/
def recurrenceJump (p : Params) (α ρ : ℂ) : ℂ :=
  recurrenceBond p α * (ρ⁻¹ - ρ)

/-- The two Laurent modes solve the homogeneous recurrence on the universal
cover.  The finite cyclic formula below is obtained by stitching these modes
at representatives `0` and `n-1`. -/
theorem laurent_twoPath_homogeneous (p : Params) {α ρ : ℂ}
    (hρ0 : ρ ≠ 0)
    (hchar : recurrenceBond p α * ρ ^ 2 -
      recurrenceDiagonal p α * ρ + recurrenceBond p α = 0)
    (N k : ℤ) :
    recurrenceDiagonal p α * (ρ ^ k + ρ ^ (N - k)) -
      recurrenceBond p α *
        ((ρ ^ (k + 1) + ρ ^ (N - (k + 1))) +
          (ρ ^ (k - 1) + ρ ^ (N - (k - 1)))) = 0 := by
  have hrec :
      recurrenceDiagonal p α =
        recurrenceBond p α * (ρ + ρ⁻¹) := by
    apply (mul_right_cancel₀ hρ0)
    field_simp [hρ0]
    linear_combination -hchar
  have hkp : ρ ^ (k + 1) = ρ ^ k * ρ := by
    rw [zpow_add₀ hρ0]
    simp
  have hkm : ρ ^ (k - 1) = ρ ^ k * ρ⁻¹ := by
    rw [show k - 1 = k + (-1) by ring, zpow_add₀ hρ0]
    simp
  have hNkp : ρ ^ (N - (k + 1)) = ρ ^ (N - k) * ρ⁻¹ := by
    rw [show N - (k + 1) = (N - k) + (-1) by ring, zpow_add₀ hρ0]
    simp
  have hNkm : ρ ^ (N - (k - 1)) = ρ ^ (N - k) * ρ := by
    rw [show N - (k - 1) = (N - k) + 1 by ring, zpow_add₀ hρ0]
    simp
  rw [hrec, hkp, hkm, hNkp, hNkm]
  ring

/-- Exact source jump after the two Laurent paths are stitched across the
cyclic boundary.  This is the normalization producing
`(1-ρ^n) * B * (ρ⁻¹-ρ)`. -/
theorem twoPath_source_jump (p : Params) {α ρ : ℂ}
    (hρ0 : ρ ≠ 0)
    (hchar : recurrenceBond p α * ρ ^ 2 -
      recurrenceDiagonal p α * ρ + recurrenceBond p α = 0) :
    recurrenceDiagonal p α * (1 + ρ ^ p.n) -
        recurrenceBond p α *
          (2 * (ρ + ρ ^ (p.n - 1))) =
      (1 - ρ ^ p.n) * recurrenceJump p α ρ := by
  have hrec :
      recurrenceDiagonal p α =
        recurrenceBond p α * (ρ + ρ⁻¹) := by
    apply (mul_right_cancel₀ hρ0)
    field_simp [hρ0]
    linear_combination -hchar
  have hn : p.n = (p.n - 1) + 1 :=
    (Nat.sub_add_cancel (Nat.succ_le_iff.mpr p.n_pos)).symm
  have hpow : ρ ^ p.n = ρ ^ (p.n - 1) * ρ := by
    conv_lhs => rw [hn]
    rw [pow_succ]
  rw [hpow]
  rw [hrec]
  unfold recurrenceJump
  field_simp [hρ0]
  ring

/-- Natural-representative form of the homogeneous recurrence, valid from
`1` through `n-1`; at `d=n-1`, the term `d+1=n` is exactly the wrapped value
at zero. -/
theorem cyclicTwoPathNumerator_homogeneous (p : Params) {α ρ : ℂ}
    (hρ0 : ρ ≠ 0)
    (hchar : recurrenceBond p α * ρ ^ 2 -
      recurrenceDiagonal p α * ρ + recurrenceBond p α = 0)
    {d : ℕ} (hd0 : 1 ≤ d) (hdn : d < p.n) :
    recurrenceDiagonal p α * cyclicTwoPathNumerator p ρ d -
      recurrenceBond p α *
        (cyclicTwoPathNumerator p ρ (d + 1) +
          cyclicTwoPathNumerator p ρ (d - 1)) = 0 := by
  have h := laurent_twoPath_homogeneous p hρ0 hchar (p.n : ℤ) (d : ℤ)
  unfold cyclicTwoPathNumerator
  have hdp : d + 1 ≤ p.n := by omega
  have hdm : d - 1 ≤ p.n := le_trans (Nat.sub_le _ _) hdn.le
  have e0 : (p.n : ℤ) - (d : ℤ) = ((p.n - d : ℕ) : ℤ) := by
    omega
  have em : (d : ℤ) - 1 = ((d - 1 : ℕ) : ℤ) := by omega
  have edp : (d : ℤ) + 1 = ((d + 1 : ℕ) : ℤ) := by omega
  have enm : (p.n : ℤ) - ((d - 1 : ℕ) : ℤ) =
      ((p.n - (d - 1) : ℕ) : ℤ) := by omega
  rw [e0, edp, em, enm] at h
  have ep' : (p.n : ℤ) - ((d + 1 : ℕ) : ℤ) =
      ((p.n - (d + 1) : ℕ) : ℤ) := by omega
  rw [ep'] at h
  rw [zpow_natCast ρ d, zpow_natCast ρ (p.n - d),
    zpow_natCast ρ (d + 1), zpow_natCast ρ (p.n - (d + 1)),
    zpow_natCast ρ (d - 1), zpow_natCast ρ (p.n - (d - 1))] at h
  exact h

/-- Forward wraparound preserves the stitched two-path numerator. -/
theorem cyclicTwoPathNumerator_add_mod (p : Params) (ρ : ℂ)
    {d : ℕ} (hd : d < p.n) :
    cyclicTwoPathNumerator p ρ ((d + 1) % p.n) =
      cyclicTwoPathNumerator p ρ (d + 1) := by
  by_cases hlast : d + 1 = p.n
  · rw [hlast, Nat.mod_self]
    unfold cyclicTwoPathNumerator
    simp [add_comm]
  · have hlt : d + 1 < p.n := by omega
    rw [Nat.mod_eq_of_lt hlt]

/-- Backward wraparound preserves the stitched numerator on nonzero
representatives. -/
theorem cyclicTwoPathNumerator_sub_mod (p : Params) (ρ : ℂ)
    {d : ℕ} (hd0 : 1 ≤ d) (hdn : d < p.n) :
    cyclicTwoPathNumerator p ρ ((d + (p.n - 1)) % p.n) =
      cyclicTwoPathNumerator p ρ (d - 1) := by
  have heq : d + (p.n - 1) = (d - 1) + p.n := by omega
  rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- Explicit cyclic Green candidate, including both the wraparound and jump
normalizations. -/
def cyclicResolventCandidate (p : Params) (α ρ : ℂ)
    (x y : ZMod p.n) : ℂ :=
  cyclicTwoPathKernel p ρ x y / recurrenceJump p α ρ

/-- A strictly contracting root has a nonvanishing wraparound denominator. -/
theorem one_sub_pow_ne_zero {ρ : ℂ} (hρ : ‖ρ‖ < 1) (n : ℕ) (hn : 0 < n) :
    1 - ρ ^ n ≠ 0 := by
  intro h
  have hp : ρ ^ n = 1 := by
    linear_combination -h
  have hnorm := congrArg norm hp
  rw [norm_pow, norm_one] at hnorm
  have hnonneg := norm_nonneg ρ
  have hpowlt : ‖ρ‖ ^ n < 1 := by
    exact pow_lt_one₀ hnonneg hρ hn.ne'
  linarith

/-- The jump coefficient is nonzero for a nonzero open-disk multiplier and
its selected contracting characteristic root. -/
theorem recurrenceJump_contracting_ne_zero (p : Params) {α : ℂ}
    (hα0 : α ≠ 0) (hα : ‖α‖ < 1) :
    recurrenceJump p α (contractingRecurrenceRoot p α) ≠ 0 := by
  have hb : recurrenceBond p α ≠ 0 := by
    unfold recurrenceBond
    exact mul_ne_zero hα0 (by exact_mod_cast ne_of_gt p.b_pos)
  have hρ0 := contractingRecurrenceRoot_ne_zero p hα0
  have hρlt := norm_contractingRecurrenceRoot_lt_one p hα0 hα
  unfold recurrenceJump
  apply mul_ne_zero hb
  intro heq
  have hinv_eq :
      (contractingRecurrenceRoot p α)⁻¹ =
        contractingRecurrenceRoot p α := sub_eq_zero.mp heq
  have hnorm := congrArg norm hinv_eq
  rw [norm_inv] at hnorm
  have hρpos : 0 < ‖contractingRecurrenceRoot p α‖ :=
    norm_pos_iff.mpr hρ0
  have hmul := congrArg
    (fun t : ℝ => t * ‖contractingRecurrenceRoot p α‖) hnorm
  rw [inv_mul_cancel₀ (ne_of_gt hρpos)] at hmul
  nlinarith [sq_nonneg (1 - ‖contractingRecurrenceRoot p α‖)]

/-- The explicitly normalized two-path kernel solves the finite cyclic
inhomogeneous recurrence, including both wraparound sites. -/
theorem cyclicResolventCandidate_physical_right (p : Params) {α : ℂ}
    (hα0 : α ≠ 0) (hα : ‖α‖ < 1) (y : ZMod p.n) :
    physicalStabilityOperator p α
        (fun x => cyclicResolventCandidate p α
          (contractingRecurrenceRoot p α) x y) =
      cyclicDelta y := by
  let ρ := contractingRecurrenceRoot p α
  have hρ0 : ρ ≠ 0 := contractingRecurrenceRoot_ne_zero p hα0
  have hρlt : ‖ρ‖ < 1 :=
    norm_contractingRecurrenceRoot_lt_one p hα0 hα
  have hchar := contractingRecurrenceRoot_characteristic p hα0
  have hwrap : 1 - ρ ^ p.n ≠ 0 :=
    one_sub_pow_ne_zero hρlt p.n p.n_pos
  have hjump : recurrenceJump p α ρ ≠ 0 :=
    recurrenceJump_contracting_ne_zero p hα0 hα
  funext x
  rw [physicalStabilityOperator_stencil]
  change cyclicResolventCandidate p α ρ x y -
      α * ((p.c : ℂ) * cyclicResolventCandidate p α ρ x y +
        p.b * cyclicResolventCandidate p α ρ (x + 1) y +
        p.b * cyclicResolventCandidate p α ρ (x - 1) y) =
    cyclicDelta y x
  have hstencil :
      cyclicResolventCandidate p α ρ x y -
          α * ((p.c : ℂ) * cyclicResolventCandidate p α ρ x y +
            p.b * cyclicResolventCandidate p α ρ (x + 1) y +
            p.b * cyclicResolventCandidate p α ρ (x - 1) y) =
        recurrenceDiagonal p α * cyclicResolventCandidate p α ρ x y -
          recurrenceBond p α *
            (cyclicResolventCandidate p α ρ (x + 1) y +
              cyclicResolventCandidate p α ρ (x - 1) y) := by
    unfold recurrenceDiagonal recurrenceBond
    ring
  rw [hstencil]
  by_cases hxy : x = y
  · subst x
    have hzero : orientedBlockDistance p y y = 0 := by
      simp [orientedBlockDistance]
    have hplus := orientedBlockDistance_add_one p y y
    have hminus := orientedBlockDistance_sub_one p y y
    rw [hzero] at hplus hminus
    have hnmod : (1 % p.n) = 1 := Nat.mod_eq_of_lt
      (lt_of_lt_of_le (by norm_num) p.n_ge_four)
    have hnegmod : ((p.n - 1) % p.n) = p.n - 1 :=
      Nat.mod_eq_of_lt (Nat.sub_lt p.n_pos (by norm_num))
    rw [hnmod] at hplus
    rw [Nat.zero_add, hnegmod] at hminus
    unfold cyclicResolventCandidate cyclicTwoPathKernel
    rw [hzero, hplus, hminus]
    have hsymm :
        cyclicTwoPathNumerator p ρ (p.n - 1) =
          cyclicTwoPathNumerator p ρ 1 := by
      unfold cyclicTwoPathNumerator
      have hnpos := p.n_pos
      have hn : p.n - (p.n - 1) = 1 := by omega
      rw [hn]
      ring
    rw [hsymm]
    rw [cyclicDelta_self]
    field_simp [hwrap, hjump]
    have hj := twoPath_source_jump p hρ0 hchar
    unfold cyclicTwoPathNumerator at *
    linear_combination hj
  · have htne : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hd0 : 1 ≤ orientedBlockDistance p x y :=
      ZMod.val_pos.mpr htne
    have hdn : orientedBlockDistance p x y < p.n :=
      ZMod.val_lt (x - y)
    have hplus := orientedBlockDistance_add_one p x y
    have hminus := orientedBlockDistance_sub_one p x y
    have hp := cyclicTwoPathNumerator_add_mod p ρ hdn
    have hm := cyclicTwoPathNumerator_sub_mod p ρ hd0 hdn
    rw [← hplus] at hp
    rw [← hminus] at hm
    unfold cyclicResolventCandidate cyclicTwoPathKernel
    rw [hp, hm]
    simp only [cyclicDelta_apply, hxy, ite_false]
    field_simp [hwrap, hjump]
    have hh := cyclicTwoPathNumerator_homogeneous p hρ0 hchar hd0 hdn
    linear_combination hh

/-- Exact solution of the finite cyclic recurrence: the Fourier Green kernel
is the two-path formula with wraparound and jump denominators. -/
theorem fourierGreenKernel_eq_cyclicResolventCandidate (p : Params) {α : ℂ}
    (hα0 : α ≠ 0) (hα : ‖α‖ < 1) (x y : ZMod p.n) :
    fourierGreenKernel p α x y =
      cyclicResolventCandidate p α (contractingRecurrenceRoot p α) x y := by
  let f : ZMod p.n → ℂ :=
    fun u => cyclicResolventCandidate p α
      (contractingRecurrenceRoot p α) u y
  have hright : physicalStabilityOperator p α f = cyclicDelta y :=
    cyclicResolventCandidate_physical_right p hα0 hα y
  have hleft :=
    ERCharacterAngle.scalarStabilityInverse_physical_left p hα f
  calc
    fourierGreenKernel p α x y =
        scalarStabilityInverse p α (cyclicDelta y) x :=
      (scalarStabilityInverse_cyclicDelta p α x y).symm
    _ = scalarStabilityInverse p α
          (physicalStabilityOperator p α f) x := by rw [hright]
    _ = f x := congrFun hleft x
    _ = cyclicResolventCandidate p α
          (contractingRecurrenceRoot p α) x y := rfl

/-- Exact two-path numerator bound. -/
theorem norm_cyclicTwoPathNumerator_le (p : Params) (ρ : ℂ) (d : ℕ) :
    ‖cyclicTwoPathNumerator p ρ d‖ ≤
      ‖ρ‖ ^ d + ‖ρ‖ ^ (p.n - d) := by
  unfold cyclicTwoPathNumerator
  simpa only [norm_pow] using norm_add_le (ρ ^ d) (ρ ^ (p.n - d))

/-- The requested finite-cycle two-path estimate with its exact wraparound
denominator. -/
theorem norm_cyclicTwoPathKernel_le (p : Params) {ρ : ℂ}
    (hρ : ‖ρ‖ < 1) (x y : ZMod p.n) :
    ‖cyclicTwoPathKernel p ρ x y‖ ≤
      (‖ρ‖ ^ orientedBlockDistance p x y +
        ‖ρ‖ ^ (p.n - orientedBlockDistance p x y)) /
        ‖1 - ρ ^ p.n‖ := by
  have hden := one_sub_pow_ne_zero hρ p.n p.n_pos
  unfold cyclicTwoPathKernel
  rw [norm_div]
  exact div_le_div_of_nonneg_right
    (norm_cyclicTwoPathNumerator_le p ρ _) (norm_nonneg _)

/-- Full bound for the explicitly normalized cyclic resolvent candidate. -/
theorem norm_cyclicResolventCandidate_le (p : Params) {α ρ : ℂ}
    (hρ : ‖ρ‖ < 1) (x y : ZMod p.n) :
    ‖cyclicResolventCandidate p α ρ x y‖ ≤
      (‖ρ‖ ^ orientedBlockDistance p x y +
        ‖ρ‖ ^ (p.n - orientedBlockDistance p x y)) /
        (‖1 - ρ ^ p.n‖ * ‖recurrenceJump p α ρ‖) := by
  unfold cyclicResolventCandidate
  rw [norm_div]
  have hk := norm_cyclicTwoPathKernel_le p hρ x y
  calc
    ‖cyclicTwoPathKernel p ρ x y‖ / ‖recurrenceJump p α ρ‖ ≤
        ((‖ρ‖ ^ orientedBlockDistance p x y +
          ‖ρ‖ ^ (p.n - orientedBlockDistance p x y)) /
          ‖1 - ρ ^ p.n‖) / ‖recurrenceJump p α ρ‖ :=
      div_le_div_of_nonneg_right hk (norm_nonneg _)
    _ = (‖ρ‖ ^ orientedBlockDistance p x y +
          ‖ρ‖ ^ (p.n - orientedBlockDistance p x y)) /
          (‖1 - ρ ^ p.n‖ * ‖recurrenceJump p α ρ‖) := by
      ring

/-- The unoriented block distance is the minimum of the two cyclic path
lengths arising in the numerator. -/
def cyclicBlockDistance (p : Params) (x y : ZMod p.n) : ℕ :=
  min (orientedBlockDistance p x y)
    (p.n - orientedBlockDistance p x y)

/-- Each two-path power is controlled by the shorter-path exponential, at
the cost of the sharp factor two. -/
theorem twoPathPowers_le_twice_shorter {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {n d : ℕ} :
    r ^ d + r ^ (n - d) ≤ 2 * r ^ min d (n - d) := by
  have hmin₁ : min d (n - d) ≤ d := min_le_left _ _
  have hmin₂ : min d (n - d) ≤ n - d := min_le_right _ _
  have hp₁ := pow_le_pow_of_le_one hr0 hr1 hmin₁
  have hp₂ := pow_le_pow_of_le_one hr0 hr1 hmin₂
  nlinarith

/-- A power of a number in `[0,1]` is bounded by the exponential with rate
equal to its distance from one. -/
theorem pow_le_exp_neg_gap {r : ℝ} (hr0 : 0 ≤ r) (d : ℕ) :
    r ^ d ≤ Real.exp (-(1 - r) * d) := by
  have hbase : r ≤ Real.exp (-(1 - r)) := by
    rw [show -(1 - r) = r - 1 by ring]
    linarith [Real.add_one_le_exp (r - 1)]
  have hp := pow_le_pow_left₀ hr0 hbase d
  rw [← Real.exp_nat_mul] at hp
  simpa [mul_comm] using hp

/-- The wraparound denominator has the dimension-uniform lower bound
`1-‖ρ‖`; in particular no parity-dependent small denominator occurs. -/
theorem one_sub_norm_le_norm_one_sub_pow (p : Params) {ρ : ℂ}
    (hρ : ‖ρ‖ < 1) :
    1 - ‖ρ‖ ≤ ‖1 - ρ ^ p.n‖ := by
  have hpow_le : ‖ρ‖ ^ p.n ≤ ‖ρ‖ := by
    have hn : 1 ≤ p.n := p.n_pos
    simpa using pow_le_pow_of_le_one (norm_nonneg ρ) hρ.le hn
  calc
    1 - ‖ρ‖ ≤ 1 - ‖ρ‖ ^ p.n := by linarith
    _ = ‖(1 : ℂ)‖ - ‖ρ ^ p.n‖ := by simp
    _ ≤ ‖(1 : ℂ) - ρ ^ p.n‖ := norm_sub_norm_le _ _

/-- Explicit two-path bound for the Fourier Green kernel.  The two
denominators are respectively finite-cycle wraparound and the exact
nearest-neighbour source jump. -/
theorem norm_fourierGreenKernel_le_twoPath (p : Params) {α : ℂ}
    (hα0 : α ≠ 0) (hα : ‖α‖ < 1) (x y : ZMod p.n) :
    let ρ := contractingRecurrenceRoot p α
    ‖fourierGreenKernel p α x y‖ ≤
      (‖ρ‖ ^ orientedBlockDistance p x y +
        ‖ρ‖ ^ (p.n - orientedBlockDistance p x y)) /
        (‖1 - ρ ^ p.n‖ * ‖recurrenceJump p α ρ‖) := by
  dsimp only
  rw [fourierGreenKernel_eq_cyclicResolventCandidate p hα0 hα]
  exact norm_cyclicResolventCandidate_le p
    (norm_contractingRecurrenceRoot_lt_one p hα0 hα) x y

/-- Exact tensor/site scaling left for the full-site bridge: after removing
the identity on the within-block mean-zero sector, the block Green correction
is divided by precisely `W`. -/
theorem norm_siteGreenKernel_sub_identity (p : Params) (α : ℂ)
    (x y : Site p.n p.W) :
    ‖siteGreenKernel p α x y - (if x = y then 1 else 0)‖ =
      ‖fourierGreenKernel p α x.1 y.1 -
        (if x.1 = y.1 then 1 else 0)‖ / (p.W : ℝ) := by
  unfold siteGreenKernel
  rw [add_sub_cancel_left, norm_div]
  simp

end BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERCyclicDecay
