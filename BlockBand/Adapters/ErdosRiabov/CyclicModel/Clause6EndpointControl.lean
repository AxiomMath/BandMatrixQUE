module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.Clause6CyclicDifference
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.ScalarProfileControl
public import Mathlib

/-!
# Endpoint control for ER clause (vi)

This module supplies the metric step in the neighbouring-entry/telescoping
argument for the concrete cyclic profile.  Along a directed path of `j`
bonds, cyclic distance from a fixed source can fall by at most `j`.  Hence,
on the short path branch `γ j ≤ 1`, every intermediate exponential is
controlled by the exponential at the initial endpoint with the fixed loss
`exp 1`.  This is the endpoint-distance comparison used in the proof of
Definition 2.4(vi).

Source: Erdős–Riabov, *The Zigzag Strategy for Random Band Matrices*,
arXiv:2506.06441v1, Definition 2.4(vi), and the concrete cyclic-profile proof
in Proposition 2.8(i); equivalently the neighbouring-entry/telescoping
paragraph following (2.26) in the block-band paper.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERClause6EndpointControl

open ERFourierInverse ERFourierAlgebra ERNearestNeighbor ERCyclicDecay ERJumpNormalization ERClause1 ERHerglotz ERScalarProfileControl
open ERClause6CyclicDifference

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Cyclic block distance is symmetric. -/
theorem cyclicBlockDistance_comm (p : Params) (x y : ZMod p.n) :
    cyclicBlockDistance p x y = cyclicBlockDistance p y x := by
  have hneg := cyclicBlockDistance_neg p x y
  have htranslate := cyclicBlockDistance_add_right p (-x) (-y) (x + y)
  simpa [add_comm, add_left_comm, add_assoc] using
    hneg.symm.trans htranslate.symm

/-- Moving one endpoint by one bond changes cyclic distance by at most one. -/
theorem cyclicBlockDistance_le_add_one_left (p : Params)
    (x y : ZMod p.n) :
    cyclicBlockDistance p x y ≤ cyclicBlockDistance p (x + 1) y + 1 := by
  unfold cyclicBlockDistance
  have hd : orientedBlockDistance p x y < p.n := by
    simpa [orientedBlockDistance] using ZMod.val_lt (x - y)
  have hn : 4 ≤ p.n := p.n_ge_four
  rw [orientedBlockDistance_add_one]
  by_cases hwrap : orientedBlockDistance p x y + 1 = p.n
  · rw [hwrap, Nat.mod_self]
    have hback : p.n - orientedBlockDistance p x y = 1 := by omega
    rw [hback, min_eq_right (by omega)]
    simp
  · have hlt : orientedBlockDistance p x y + 1 < p.n := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

/-- A directed path of `j` bonds can decrease distance from a fixed source by
at most `j`.  No parity choice or shortest-path certificate is required. -/
theorem cyclicBlockDistance_endpoint_le_intermediate_add (p : Params)
    (a x : ZMod p.n) : ∀ j : ℕ,
    cyclicBlockDistance p a x ≤
      cyclicBlockDistance p a (x + j) + j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep := cyclicBlockDistance_le_add_one_left p (x + j) a
      rw [cyclicBlockDistance_comm p (x + j) a,
        cyclicBlockDistance_comm p ((x + j) + 1) a] at hstep
      have hadd : (x + (j + 1 : ℕ) : ZMod p.n) = (x + j) + 1 := by
        push_cast
        ring
      rw [hadd]
      omega

/-- Exponential endpoint control along a directed cyclic path.  The hypothesis
`γ j ≤ 1` is exactly the short-path branch in the paper after taking
`γ` to be the square-root spectral height. -/
theorem exp_neg_intermediate_le_exp_one_mul_endpoint
    (p : Params) {γ : ℝ} (hγ : 0 ≤ γ) (a x : ZMod p.n) (j : ℕ)
    (hshort : γ * j ≤ 1) :
    Real.exp (-γ * cyclicBlockDistance p a (x + j)) ≤
      Real.exp 1 * Real.exp (-γ * cyclicBlockDistance p a x) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hdist := cyclicBlockDistance_endpoint_le_intermediate_add p a x j
  have hmul := mul_le_mul_of_nonneg_left
    (show (cyclicBlockDistance p a x : ℝ) ≤
      cyclicBlockDistance p a (x + j) + j by exact_mod_cast hdist) hγ
  nlinarith

/-- Every intermediate exponential on a short directed path is bounded by the
sum of the two endpoint exponentials, with the same fixed loss.  Keeping both
endpoints matches the source formulation and is convenient when the two
orientations of the cyclic Green numerator are combined. -/
theorem exp_neg_intermediate_le_exp_one_mul_endpoint_sum
    (p : Params) {γ : ℝ} (hγ : 0 ≤ γ) (a x : ZMod p.n) {r j : ℕ}
    (hj : j ≤ r) (hshort : γ * r ≤ 1) :
    Real.exp (-γ * cyclicBlockDistance p a (x + j)) ≤
      Real.exp 1 *
        (Real.exp (-γ * cyclicBlockDistance p a x) +
          Real.exp (-γ * cyclicBlockDistance p a (x + r))) := by
  have hjγ : γ * j ≤ 1 :=
    (mul_le_mul_of_nonneg_left (show (j : ℝ) ≤ r by exact_mod_cast hj) hγ).trans
      hshort
  have h := exp_neg_intermediate_le_exp_one_mul_endpoint p hγ a x j hjγ
  calc
    Real.exp (-γ * cyclicBlockDistance p a (x + j)) ≤
        Real.exp 1 * Real.exp (-γ * cyclicBlockDistance p a x) := h
    _ ≤ Real.exp 1 *
        (Real.exp (-γ * cyclicBlockDistance p a x) +
          Real.exp (-γ * cyclicBlockDistance p a (x + r))) := by
      exact mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (Real.exp_pos _).le) (Real.exp_pos _).le

/-- Summed endpoint control for the telescoping path.  This is the precise
finite-cycle estimate needed after applying the neighbouring Green bound:
the cost is the number `r` of crossed bonds, and the only loss is `exp 1`. -/
theorem sum_exp_neg_intermediate_le_card_mul_endpoints
    (p : Params) {γ : ℝ} (hγ : 0 ≤ γ) (a x : ZMod p.n) (r : ℕ)
    (hshort : γ * r ≤ 1) :
    (∑ j ∈ Finset.range r,
      Real.exp (-γ * cyclicBlockDistance p a (x + j))) ≤
      r * (Real.exp 1 *
        (Real.exp (-γ * cyclicBlockDistance p a x) +
          Real.exp (-γ * cyclicBlockDistance p a (x + r)))) := by
  calc
    (∑ j ∈ Finset.range r,
      Real.exp (-γ * cyclicBlockDistance p a (x + j))) ≤
        ∑ _j ∈ Finset.range r,
          Real.exp 1 *
            (Real.exp (-γ * cyclicBlockDistance p a x) +
              Real.exp (-γ * cyclicBlockDistance p a (x + r))) := by
          apply Finset.sum_le_sum
          intro j hj
          exact exp_neg_intermediate_le_exp_one_mul_endpoint_sum p hγ a x
            (Finset.mem_range.mp hj).le hshort
    _ = r * (Real.exp 1 *
        (Real.exp (-γ * cyclicBlockDistance p a x) +
          Real.exp (-γ * cyclicBlockDistance p a (x + r)))) := by simp

/-- The asymmetric exponents produced by a neighbouring cyclic Green
difference are controlled by the ordinary cyclic distance.  The missing bond
in the wrap exponent costs only the fixed factor `exp 1`. -/
theorem neighboring_twoPathPowers_le_exp_cyclic
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {n d : ℕ} (hd : d < n) :
    q ^ (n - d - 1) + q ^ d ≤
      2 * Real.exp 1 * Real.exp (-(1 - q) * min d (n - d)) := by
  let γ := 1 - q
  have hγ0 : 0 ≤ γ := by dsimp [γ]; linarith
  have hγ1 : γ ≤ 1 := by dsimp [γ]; linarith
  have hshort : min d (n - d) ≤ d := min_le_left _ _
  have hwrap : min d (n - d) ≤ n - d := min_le_right _ _
  have hdexp := pow_le_exp_neg_gap hq0 d
  have hwexp := pow_le_exp_neg_gap hq0 (n - d - 1)
  have hde :
      Real.exp (-γ * d) ≤
        Real.exp 1 * Real.exp (-γ * min d (n - d)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hm : ((min d (n - d) : ℕ) : ℝ) ≤ (d : ℝ) :=
      Nat.cast_le.2 hshort
    have := mul_le_mul_of_nonneg_left hm hγ0
    nlinarith
  have hwe :
      Real.exp (-γ * ((n - d - 1 : ℕ) : ℝ)) ≤
        Real.exp 1 * Real.exp (-γ * min d (n - d)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hm : ((min d (n - d) : ℕ) : ℝ) ≤ ((n - d : ℕ) : ℝ) :=
      Nat.cast_le.2 hwrap
    have hsplit : ((n - d : ℕ) : ℝ) =
        ((n - d - 1 : ℕ) : ℝ) + 1 := by
      norm_cast
      omega
    have hmul := mul_le_mul_of_nonneg_left hm hγ0
    have hgoal : γ * ((min d (n - d) : ℕ) : ℝ) ≤
        γ * ((n - d - 1 : ℕ) : ℝ) + 1 := by
      nlinarith
    nlinarith
  dsimp only [γ] at hdexp hwexp hde hwe
  calc
    q ^ (n - d - 1) + q ^ d ≤
        Real.exp (-(1 - q) * ((n - d - 1 : ℕ) : ℝ)) +
          Real.exp (-(1 - q) * (d : ℝ)) := add_le_add hwexp hdexp
    _ ≤ (Real.exp 1 * Real.exp (-(1 - q) *
          ((min d (n - d) : ℕ) : ℝ))) +
        (Real.exp 1 * Real.exp (-(1 - q) *
          ((min d (n - d) : ℕ) : ℝ))) :=
      add_le_add hwe hde
    _ = 2 * Real.exp 1 * Real.exp (-(1 - q) *
        ((min d (n - d) : ℕ) : ℝ)) := by ring

/-- Source-endpoint form of the neighbouring Green estimate.  It combines
the cancellation from `Clause6CyclicDifference` with the preceding
fixed-loss comparison, and already has the square-root rate of the paper. -/
theorem norm_alpha_mul_fourierGreenKernel_add_one_sub_le_endpoint_exp
    (p : Params) {α : ℂ} {η : ℝ}
    (hα0 : α ≠ 0) (hα : ‖α‖ < 1)
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hthreshold : (1 / (p.n : ℝ)) ^ 2 ≤ η)
    (hmargin : η / 4 ≤ 1 - ‖α‖)
    (x y : ZMod p.n) :
    ‖α * (fourierGreenKernel p α (x + 1) y -
      fourierGreenKernel p α x y)‖ ≤
      (2 * Real.exp 1 /
        (Real.sqrt (p.b * jumpBondMargin p) * fixedWrapFloor)) *
        Real.exp (-(Real.sqrt η / 2) * cyclicBlockDistance p x y) := by
  let ρ := contractingRecurrenceRoot p α
  let d := orientedBlockDistance p x y
  have hρ : ‖ρ‖ < 1 :=
    norm_contractingRecurrenceRoot_lt_one p hα0 hα
  have hd : d < p.n := ZMod.val_lt (x - y)
  have hpowers := neighboring_twoPathPowers_le_exp_cyclic
    (q := ‖ρ‖) (n := p.n) (d := d) (norm_nonneg ρ) hρ.le hd
  have hgap : Real.sqrt η / 2 ≤ 1 - ‖ρ‖ := by
    exact (sqrt_height_div_two_le_rootGapRate p hη0 hη1 hmargin).trans
      (min_half_sqrt_radialMargin_le_root_gap p hα0 hα)
  have hexp :
      Real.exp (-(1 - ‖ρ‖) * cyclicBlockDistance p x y) ≤
        Real.exp (-(Real.sqrt η / 2) *
          cyclicBlockDistance p x y) := by
    apply Real.exp_le_exp.mpr
    have hdist : 0 ≤ (cyclicBlockDistance p x y : ℝ) := by positivity
    nlinarith
  have hneighbor :=
    norm_alpha_mul_fourierGreenKernel_add_one_sub_le p hα0 hα hη0 hη1
      hthreshold hmargin x y
  dsimp only at hneighbor
  have hpref0 :
      0 ≤ 1 / (Real.sqrt (p.b * jumpBondMargin p) * fixedWrapFloor) := by
    exact one_div_nonneg.mpr (mul_nonneg (Real.sqrt_nonneg _)
      fixedWrapFloor_pos.le)
  have hpowers' :
      ‖ρ‖ ^ (p.n - d - 1) + ‖ρ‖ ^ d ≤
        2 * Real.exp 1 *
          Real.exp (-(1 - ‖ρ‖) * cyclicBlockDistance p x y) := by
    simpa [d, cyclicBlockDistance] using hpowers
  change ‖α * (fourierGreenKernel p α (x + 1) y -
      fourierGreenKernel p α x y)‖ ≤ _
  calc
    ‖α * (fourierGreenKernel p α (x + 1) y -
        fourierGreenKernel p α x y)‖ ≤
        (1 / (Real.sqrt (p.b * jumpBondMargin p) * fixedWrapFloor)) *
          (‖ρ‖ ^ (p.n - d - 1) + ‖ρ‖ ^ d) := hneighbor
    _ ≤ (1 / (Real.sqrt (p.b * jumpBondMargin p) * fixedWrapFloor)) *
          (2 * Real.exp 1 *
            Real.exp (-(1 - ‖ρ‖) * cyclicBlockDistance p x y)) := by
      exact mul_le_mul_of_nonneg_left hpowers' hpref0
    _ ≤ (1 / (Real.sqrt (p.b * jumpBondMargin p) * fixedWrapFloor)) *
          (2 * Real.exp 1 *
            Real.exp (-(Real.sqrt η / 2) *
              cyclicBlockDistance p x y)) := by
      gcongr
    _ = (2 * Real.exp 1 /
        (Real.sqrt (p.b * jumpBondMargin p) * fixedWrapFloor)) *
          Real.exp (-(Real.sqrt η / 2) *
            cyclicBlockDistance p x y) := by ring

/-- Short-path telescoping for the scalar cyclic Green kernel.  The factor
`r` is the number of crossed block bonds; all intermediate source distances
have been replaced by the two endpoint distances, with a dimension-free
constant. -/
theorem norm_alpha_mul_fourierGreenKernel_path_sub_le_endpoints
    (p : Params) {α : ℂ} {η : ℝ}
    (hα0 : α ≠ 0) (hα : ‖α‖ < 1)
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hthreshold : (1 / (p.n : ℝ)) ^ 2 ≤ η)
    (hmargin : η / 4 ≤ 1 - ‖α‖)
    (x y : ZMod p.n) (r : ℕ)
    (hshort : (Real.sqrt η / 2) * r ≤ 1) :
    ‖α * (fourierGreenKernel p α (x + r) y -
      fourierGreenKernel p α x y)‖ ≤
      (2 * Real.exp 2 /
        (Real.sqrt (p.b * jumpBondMargin p) * fixedWrapFloor)) * r *
        (Real.exp (-(Real.sqrt η / 2) * cyclicBlockDistance p x y) +
          Real.exp (-(Real.sqrt η / 2) *
            cyclicBlockDistance p (x + r) y)) := by
  let γ := Real.sqrt η / 2
  let C := 2 * Real.exp 1 /
    (Real.sqrt (p.b * jumpBondMargin p) * fixedWrapFloor)
  have hγ : 0 ≤ γ := by dsimp [γ]; positivity
  have htel := norm_sub_le_sum_neighboring p
    (fun u => α * fourierGreenKernel p α u y) x r
  have hsum :
      (∑ j ∈ Finset.range r,
        ‖α * fourierGreenKernel p α (x + (j + 1)) y -
          α * fourierGreenKernel p α (x + j) y‖) ≤
        C * ∑ j ∈ Finset.range r,
          Real.exp (-γ * cyclicBlockDistance p y (x + j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hn := norm_alpha_mul_fourierGreenKernel_add_one_sub_le_endpoint_exp
      p hα0 hα hη0 hη1 hthreshold hmargin (x + j) y
    rw [cyclicBlockDistance_comm p (x + j) y] at hn
    change ‖α * fourierGreenKernel p α (x + (j + 1)) y -
        α * fourierGreenKernel p α (x + j) y‖ ≤
      C * Real.exp (-γ * cyclicBlockDistance p y (x + j))
    calc
      ‖α * fourierGreenKernel p α (x + (j + 1)) y -
          α * fourierGreenKernel p α (x + j) y‖ =
          ‖α * (fourierGreenKernel p α ((x + j) + 1) y -
            fourierGreenKernel p α (x + j) y)‖ := by
        rw [mul_sub]
        congr 3
        apply congrArg (fun z : ZMod p.n => fourierGreenKernel p α z y)
        ring
      _ ≤ C * Real.exp (-γ * cyclicBlockDistance p y (x + j)) := by
        simpa [C, γ] using hn
  have hend := sum_exp_neg_intermediate_le_card_mul_endpoints
    p hγ y x r hshort
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
      (mul_nonneg (Real.sqrt_nonneg _) fixedWrapFloor_pos.le)
  calc
    ‖α * (fourierGreenKernel p α (x + r) y -
        fourierGreenKernel p α x y)‖ =
        ‖α * fourierGreenKernel p α (x + r) y -
          α * fourierGreenKernel p α x y‖ := by ring_nf
    _ ≤ ∑ j ∈ Finset.range r,
        ‖α * fourierGreenKernel p α (x + (j + 1)) y -
          α * fourierGreenKernel p α (x + j) y‖ := htel
    _ ≤ C * ∑ j ∈ Finset.range r,
          Real.exp (-γ * cyclicBlockDistance p y (x + j)) := hsum
    _ ≤ C * (r * (Real.exp 1 *
        (Real.exp (-γ * cyclicBlockDistance p y x) +
          Real.exp (-γ * cyclicBlockDistance p y (x + r))))) := by
      exact mul_le_mul_of_nonneg_left hend hC0
    _ = (2 * Real.exp 2 /
        (Real.sqrt (p.b * jumpBondMargin p) * fixedWrapFloor)) * r *
        (Real.exp (-(Real.sqrt η / 2) * cyclicBlockDistance p x y) +
          Real.exp (-(Real.sqrt η / 2) *
            cyclicBlockDistance p (x + r) y)) := by
      rw [cyclicBlockDistance_comm p y x,
        cyclicBlockDistance_comm p y (x + r)]
      dsimp [C, γ]
      have hexp : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      rw [hexp]
      ring

end BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERClause6EndpointControl
