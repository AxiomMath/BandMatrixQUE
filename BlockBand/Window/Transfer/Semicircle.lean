module

public import BlockBand.Internal.Contracts.Layers
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Semicircle distribution function and classical locations

Deterministic facts, no probability law. `F_sc = Layers.semicircleCDF` (lower limit `-2`),
`ρ_sc(x) = √(4 - x²)/(2π)` (`Parameters.semicircleDensity`, zero for `|x| ≥ 2` since `√` of a
nonpositive real is `0`), `e_α = Layers.classicalLocation p α = inf {x | (α+1)/N ≤ F_sc x}`.
Proved here: `0 ≤ ρ_sc ≤ 1/π`, `F_sc` is `1/π`-Lipschitz and monotone, `F_sc(2) = 1`, and
`F_sc(e) = u` for `e = inf {x | u ≤ F_sc x}` and every `0 < u ≤ 1`. New file (no draft source).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Transfer

open MeasureTheory Set
open BlockBand.Internal.Contracts.Layers

theorem semicircleDensity_nonneg (x : ℝ) : 0 ≤ Parameters.semicircleDensity x := by
  unfold Parameters.semicircleDensity
  positivity

theorem semicircleDensity_le (x : ℝ) : Parameters.semicircleDensity x ≤ 1 / Real.pi := by
  unfold Parameters.semicircleDensity
  have h4 : Real.sqrt (4 - x ^ 2) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
  rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
  nlinarith [Real.pi_pos]

theorem continuous_semicircleDensity : Continuous Parameters.semicircleDensity := by
  unfold Parameters.semicircleDensity
  fun_prop

theorem semicircleDensity_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable Parameters.semicircleDensity volume a b :=
  continuous_semicircleDensity.intervalIntegrable a b

/-- `F(x) - F(y) = ∫_y^x ρ_sc`. -/
theorem semicircleCDF_sub (x y : ℝ) :
    semicircleCDF x - semicircleCDF y = ∫ t in y..x, Parameters.semicircleDensity t := by
  unfold semicircleCDF
  exact intervalIntegral.integral_interval_sub_left (semicircleDensity_intervalIntegrable _ _)
    (semicircleDensity_intervalIntegrable _ _)

/-- `F_sc` is `1/π`-Lipschitz (global density bound). -/
theorem abs_semicircleCDF_sub_le (x y : ℝ) :
    |semicircleCDF x - semicircleCDF y| ≤ |x - y| / Real.pi := by
  rw [semicircleCDF_sub]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := y) (b := x) (C := 1 / Real.pi) (f := Parameters.semicircleDensity) (fun t _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (semicircleDensity_nonneg t)]
      exact semicircleDensity_le t)
  rw [Real.norm_eq_abs] at h
  calc _ ≤ 1 / Real.pi * |x - y| := h
    _ = _ := by ring

theorem semicircleCDF_mono {x y : ℝ} (h : y ≤ x) : semicircleCDF y ≤ semicircleCDF x := by
  have hh := semicircleCDF_sub x y
  have h0 : 0 ≤ ∫ t in y..x, Parameters.semicircleDensity t :=
    intervalIntegral.integral_nonneg h fun t _ => semicircleDensity_nonneg t
  linarith

theorem continuous_semicircleCDF : Continuous semicircleCDF := by
  refine Metric.continuous_iff.mpr fun x ε hε => ⟨ε * Real.pi, by positivity, fun y hy => ?_⟩
  rw [Real.dist_eq] at hy ⊢
  calc |semicircleCDF y - semicircleCDF x| ≤ |y - x| / Real.pi := abs_semicircleCDF_sub_le y x
    _ < ε * Real.pi / Real.pi := div_lt_div_of_pos_right hy Real.pi_pos
    _ = ε := by field_simp

theorem semicircleCDF_neg_two : semicircleCDF (-2) = 0 := by
  simp [semicircleCDF]

/-- Total mass: `F_sc(2) = ∫_{-2}^2 √(4-x²)/(2π) dx = 1`. -/
theorem semicircleCDF_two : semicircleCDF 2 = 1 := by
  unfold semicircleCDF Parameters.semicircleDensity
  rw [intervalIntegral.integral_div]
  have hsub : (∫ x in (-2 : ℝ)..2, Real.sqrt (4 - x ^ 2)) =
      2 * ∫ y in (-1 : ℝ)..1, Real.sqrt (4 - (2 * y) ^ 2) := by
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sqrt (4 - x ^ 2))
      (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
    ring
  have hpt : (fun y : ℝ => Real.sqrt (4 - (2 * y) ^ 2)) =
      fun y => 2 * Real.sqrt (1 - y ^ 2) := by
    funext y
    rw [show 4 - (2 * y) ^ 2 = 4 * (1 - y ^ 2) by ring, Real.sqrt_mul (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsub, hpt, intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq]
  field_simp

theorem semicircleCDF_le_one (x : ℝ) : semicircleCDF x ≤ 1 := by
  rcases le_total x 2 with h | h
  · exact (semicircleCDF_mono h).trans_eq semicircleCDF_two
  · have hh := semicircleCDF_sub x 2
    have hz : (∫ t in (2 : ℝ)..x, Parameters.semicircleDensity t) = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards with t ht
      rw [Set.uIoc_of_le h] at ht
      unfold Parameters.semicircleDensity
      rw [Real.sqrt_eq_zero'.mpr (by nlinarith [ht.1]), zero_div]
    rw [semicircleCDF_two] at hh
    linarith

/-- The generalized inverse hits every level: for `0 < u ≤ 1`,
`F_sc (inf {x | u ≤ F_sc x}) = u`. -/
theorem semicircleCDF_sInf (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    semicircleCDF (sInf {x | u ≤ semicircleCDF x}) = u := by
  set S := {x | u ≤ semicircleCDF x}
  have hne : S.Nonempty := ⟨2, by simp [S, semicircleCDF_two, hu1]⟩
  have hbdd : BddBelow S := by
    refine ⟨-2, fun x hx => ?_⟩
    by_contra hlt
    have := semicircleCDF_mono (le_of_lt (lt_of_not_ge hlt))
    rw [semicircleCDF_neg_two] at this
    have hx' : u ≤ semicircleCDF x := hx
    linarith
  have hclosed : IsClosed S := isClosed_le continuous_const continuous_semicircleCDF
  have hmem : sInf S ∈ S := hclosed.csInf_mem hne hbdd
  refine le_antisymm ?_ hmem
  by_contra hgt'
  have hgt := lt_of_not_ge hgt'
  set e := sInf S
  set δ := (semicircleCDF e - u) * Real.pi
  have hδ : 0 < δ := by have := Real.pi_pos; unfold δ; nlinarith
  have hnot : e - δ / 2 ∉ S := fun h => by
    have := csInf_le hbdd h
    linarith
  have hnot' : semicircleCDF (e - δ / 2) < u := lt_of_not_ge hnot
  have hlip := abs_semicircleCDF_sub_le e (e - δ / 2)
  rw [show e - (e - δ / 2) = δ / 2 by ring, abs_of_pos (show (0 : ℝ) < δ / 2 by linarith)] at hlip
  have hd : δ / 2 / Real.pi = (semicircleCDF e - u) / 2 := by
    unfold δ; field_simp
  rw [hd] at hlip
  have := le_abs_self (semicircleCDF e - semicircleCDF (e - δ / 2))
  linarith

/-- `F_sc(e_α) = (α+1)/N` for every physical rank. -/
theorem semicircleCDF_classicalLocation (p : Parameters) (α : Fin p.N) :
    semicircleCDF (classicalLocation p α) = ((α.val + 1 : ℕ) : ℝ) / p.N := by
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  apply semicircleCDF_sInf
  · positivity
  · rw [div_le_one hN]
    exact_mod_cast α.isLt

/-- Classical separation with `β = π`: `π |(α+1) - N F_sc(E)| / N ≤ |e_α - E|`. -/
theorem classicalLocation_separation (p : Parameters) (α : Fin p.N) (E : ℝ) :
    Real.pi * |((α.val : ℝ) + 1) - (p.N : ℝ) * semicircleCDF E| / (p.N : ℝ) ≤
      |classicalLocation p α - E| := by
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hF := semicircleCDF_classicalLocation p α
  have hlip := abs_semicircleCDF_sub_le (classicalLocation p α) E
  rw [hF] at hlip
  have heq : |((α.val : ℝ) + 1) - (p.N : ℝ) * semicircleCDF E| / (p.N : ℝ) =
      |((α.val + 1 : ℕ) : ℝ) / p.N - semicircleCDF E| := by
    rw [← abs_of_pos hN, ← abs_div, abs_of_pos hN]
    congr 1
    push_cast
    field_simp
  rw [mul_div_assoc, heq]
  have := (le_div_iff₀ Real.pi_pos).mp hlip
  linarith

/-- A rank whose level is at least `γ` below `F_sc(E)` has classical location at least
`πγ` below `E`. -/
theorem classicalLocation_le_of_level (p : Parameters) (α : Fin p.N) (E γ : ℝ) (hγ : 0 < γ)
    (hlev : ((α.val + 1 : ℕ) : ℝ) / p.N ≤ semicircleCDF E - γ) :
    classicalLocation p α ≤ E - Real.pi * γ := by
  have hF := semicircleCDF_classicalLocation p α
  have hlt : classicalLocation p α < E := by
    by_contra h
    have := semicircleCDF_mono (le_of_not_gt h)
    linarith
  have hlip := abs_semicircleCDF_sub_le (classicalLocation p α) E
  rw [hF, abs_of_neg (by linarith), abs_of_neg (by linarith), le_div_iff₀ Real.pi_pos] at hlip
  nlinarith [Real.pi_pos]

/-- A rank whose level is at least `γ` above `F_sc(E)` has classical location at least
`πγ` above `E`. -/
theorem le_classicalLocation_of_level (p : Parameters) (α : Fin p.N) (E γ : ℝ) (hγ : 0 < γ)
    (hlev : semicircleCDF E + γ ≤ ((α.val + 1 : ℕ) : ℝ) / p.N) :
    E + Real.pi * γ ≤ classicalLocation p α := by
  have hF := semicircleCDF_classicalLocation p α
  have hlt : E < classicalLocation p α := by
    by_contra h
    have := semicircleCDF_mono (le_of_not_gt h)
    linarith
  have hlip := abs_semicircleCDF_sub_le (classicalLocation p α) E
  rw [hF, abs_of_pos (by linarith), abs_of_pos (by linarith), le_div_iff₀ Real.pi_pos] at hlip
  nlinarith [Real.pi_pos]

end BlockBand.Window.Transfer
