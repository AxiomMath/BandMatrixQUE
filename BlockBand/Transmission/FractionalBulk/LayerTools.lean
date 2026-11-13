module

public import BlockBand.Transmission.FractionalBulk.LayerMoments

/-!
# Bookkeeping for the one-layer expectation

* `integrable_bilinear_of`: entrywise integrable `U` gives integrable `u*Uv`;
* `half_sq_le`: `(Σ a)²/2 ≤ Σ_{i,j : t_i ≤ t_j} a_i a_j` for `a ≥ 0`;
* `integral_shape`: linearity of the integral of `P + c Σ w_i(A_i - 1) - c' Σ_{ij} G_ij`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.FractionalBulk

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionStatements

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

theorem integrable_bilinear_of {n : Type*} [Fintype n] {U : Ω → Matrix n n ℂ}
    (hU : ∀ x y, Integrable (fun ω => U ω x y) ν) (u v : n → ℂ) :
    Integrable (fun ω => bilinear u (U ω) v) ν := by
  simp only [bilinear, dotProduct, mulVec]
  exact integrable_finsetSum _ fun x _ =>
    (integrable_finsetSum _ fun y _ => (hU x y).mul_const _).const_mul _

/-- `(Σ a)²/2 ≤ Σ_{t_i ≤ t_j} a_i a_j` for `a ≥ 0`. -/
theorem half_sq_le {ι : Type*} [Fintype ι] (a t : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i) ^ 2 / 2 ≤ ∑ i, ∑ j, if t i ≤ t j then a i * a j else 0 := by
  set S := ∑ i, ∑ j, if t i ≤ t j then a i * a j else 0
  have hsq : (∑ i, a i) ^ 2 = ∑ i, ∑ j, a i * a j := by
    rw [sq, Finset.sum_mul_sum]
  have hsplit : ∑ i, ∑ j, a i * a j = S + ∑ i, ∑ j, if t i ≤ t j then 0 else a i * a j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  have hle : ∑ i, ∑ j, (if t i ≤ t j then 0 else a i * a j) ≤
      ∑ i, ∑ j, if t j ≤ t i then a i * a j else 0 := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    split_ifs with h1 h2 h2
    · exact mul_nonneg (ha i) (ha j)
    · exact le_rfl
    · exact le_rfl
    · exact absurd (le_of_lt (not_le.mp h1)) h2
  have hswap : ∑ i, ∑ j, (if t j ≤ t i then a i * a j else 0) = S := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  rw [hsq, hsplit]
  linarith

/-- Linearity for the integrated per-sample bound. -/
theorem integral_shape [IsProbabilityMeasure ν] {ι : Type*} [Fintype ι] (P cJ cG : ℝ)
    (w : ι → ℝ) (A : ι → Ω → ℝ) (G : ι → ι → Ω → ℝ) (hA : ∀ i, Integrable (A i) ν)
    (hG : ∀ i j, Integrable (G i j) ν) :
    ∫ y, (P + cJ * ∑ i, w i * (A i y - 1) - cG * ∑ i, ∑ j, G i j y) ∂ν =
      P + cJ * ∑ i, w i * ((∫ y, A i y ∂ν) - 1) - cG * ∑ i, ∑ j, ∫ y, G i j y ∂ν := by
  have h1 : Integrable (fun y => cJ * ∑ i, w i * (A i y - 1)) ν :=
    (integrable_finsetSum _ fun i _ => ((hA i).sub (integrable_const _)).const_mul _).const_mul _
  have h2 : Integrable (fun y => cG * ∑ i, ∑ j, G i j y) ν :=
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hG i j).const_mul _
  have h0 : Integrable (fun y => P + cJ * ∑ i, w i * (A i y - 1)) ν := (integrable_const P).add h1
  have hAi : ∀ i, Integrable (fun y => w i * (A i y - 1)) ν := fun i =>
    ((hA i).sub (integrable_const (1 : ℝ))).const_mul (w i)
  have e1 : ∫ y, ∑ i, w i * (A i y - 1) ∂ν = ∑ i, w i * ((∫ y, A i y ∂ν) - 1) := by
    rw [integral_finsetSum _ fun i _ => hAi i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_sub (hA i) (integrable_const _), integral_const]
    simp
  have e2 : ∫ y, ∑ i, ∑ j, G i j y ∂ν = ∑ i, ∑ j, ∫ y, G i j y ∂ν := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hG i j]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hG i j
  rw [integral_sub h0 h2, integral_add (integrable_const P) h1, integral_const,
    integral_const_mul, integral_const_mul, e1, e2]
  simp

end BlockBand.Transmission.FractionalBulk
