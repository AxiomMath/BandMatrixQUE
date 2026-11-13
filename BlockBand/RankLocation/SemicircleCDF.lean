module

public import BlockBand.Internal.Contracts.Layers

/-!
# The semicircle distribution function, its phase form, and classical locations

Results: the closed form of `F_sc` on `[-2,2]` and its values off `[-2,2]`; `F_sc' = ρ_sc`
on `ℝ`, continuity, monotonicity on `ℝ`, strict monotonicity on `[-2,2]`; the phase identity
`F_sc = ℓ + h/2` (on `[-2,2]`, and in fact on `ℝ`); `F_sc(e_α) = (α.val+1)/N`,
`e_α ∈ [-2,2]`, and `e_α ∈ [-2+ϑ, 2-ϑ]` for every bulk rank `IsBulkRank p ϑ α`, `ϑ > 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.RankLocation

open MeasureTheory Set
open BlockBand.Internal.Contracts.Layers

/-- Explicit antiderivative `(2π)⁻¹ ((x/2)√(4-x²) + 2 arcsin(x/2)) + 1/2` of `ρ_sc`. -/
def semicircleAntideriv (x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ((x / 2) * Real.sqrt (4 - x ^ 2) + 2 * Real.arcsin (x / 2)) + 1 / 2

theorem sqrt_one_sub_half_sq (x : ℝ) :
    Real.sqrt (1 - (x / 2) ^ 2) = Real.sqrt (4 - x ^ 2) / 2 := by
  rw [show 1 - (x / 2) ^ 2 = (4 - x ^ 2) / 2 ^ 2 by ring, Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq (by norm_num)]

theorem hasDerivAt_semicircleAntideriv {x : ℝ} (hx : |x| < 2) :
    HasDerivAt semicircleAntideriv (Parameters.semicircleDensity x) x := by
  have hx' := abs_lt.mp hx
  have h4 : 0 < 4 - x ^ 2 := by nlinarith
  have hs := ((hasDerivAt_pow 2 x).const_sub 4).sqrt h4.ne'
  have ha := (Real.hasDerivAt_arcsin (x := x / 2) (by linarith) (by linarith)).comp x
    ((hasDerivAt_id x).div_const 2)
  have h := (((((hasDerivAt_id x).div_const 2).mul hs).add (ha.const_mul 2)).const_mul
    (1 / (2 * Real.pi))).add_const (1 / 2)
  convert h using 1
  · rfl
  · rw [sqrt_one_sub_half_sq]
    unfold Parameters.semicircleDensity
    have hsp : 0 < Real.sqrt (4 - x ^ 2) := Real.sqrt_pos.mpr h4
    have hsq : Real.sqrt (4 - x ^ 2) ^ 2 = 4 - x ^ 2 := Real.sq_sqrt h4.le
    have hpi : 0 < Real.pi := Real.pi_pos
    simp only [id, Nat.cast_ofNat, show 2 - 1 = 1 from rfl, pow_one]
    field_simp
    linear_combination hsq

theorem continuous_semicircleAntideriv : Continuous semicircleAntideriv := by
  unfold semicircleAntideriv
  have := Real.continuous_arcsin
  fun_prop

theorem semicircleAntideriv_neg_two : semicircleAntideriv (-2) = 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  simp only [semicircleAntideriv, show (-2 : ℝ) / 2 = -1 by norm_num, Real.arcsin_neg_one,
    show 4 - (-2 : ℝ) ^ 2 = 0 by norm_num, Real.sqrt_zero]
  field_simp
  ring

theorem semicircleAntideriv_two : semicircleAntideriv 2 = 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  simp only [semicircleAntideriv, show (2 : ℝ) / 2 = 1 by norm_num, Real.arcsin_one,
    show 4 - (2 : ℝ) ^ 2 = 0 by norm_num, Real.sqrt_zero]
  field_simp
  ring

theorem continuous_semicircleDensity : Continuous Parameters.semicircleDensity := by
  unfold Parameters.semicircleDensity
  fun_prop

theorem semicircleDensity_nonneg (x : ℝ) : 0 ≤ Parameters.semicircleDensity x := by
  unfold Parameters.semicircleDensity
  have := Real.pi_pos
  positivity

theorem semicircleDensity_pos {x : ℝ} (hx : |x| < 2) : 0 < Parameters.semicircleDensity x := by
  unfold Parameters.semicircleDensity
  have := Real.pi_pos
  have hx' := abs_lt.mp hx
  have h4 : 0 < 4 - x ^ 2 := by nlinarith
  have := Real.sqrt_pos.mpr h4
  positivity

theorem semicircleDensity_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : Parameters.semicircleDensity x = 0 := by
  unfold Parameters.semicircleDensity
  have h : 4 - x ^ 2 ≤ 0 := by
    have : (2 : ℝ) ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ (by norm_num) hx 2
    rw [sq_abs] at this
    linarith
  rw [Real.sqrt_eq_zero'.mpr h, zero_div]

theorem semicircleDensity_le (x : ℝ) : Parameters.semicircleDensity x ≤ 1 / Real.pi := by
  unfold Parameters.semicircleDensity
  have hpi := Real.pi_pos
  have h : Real.sqrt (4 - x ^ 2) ≤ 2 := by
    calc Real.sqrt (4 - x ^ 2) ≤ Real.sqrt (2 ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 := Real.sqrt_sq (by norm_num)
  rw [div_le_div_iff₀ (by positivity) hpi]
  nlinarith

/-- **Explicit semicircle distribution function on the support.** With density
`ρ_sc(x) = √(4-x²)/(2π)` (`Parameters.semicircleDensity`, row variance one, support `[-2,2]`),
for `-2 ≤ x ≤ 2`: `F_sc(x) = (2π)⁻¹ ((x/2)√(4-x²) + 2 arcsin(x/2)) + 1/2`. -/
theorem semicircleCDF_eq_antideriv {x : ℝ} (hx : x ∈ Icc (-2 : ℝ) 2) :
    semicircleCDF x = (1 / (2 * Real.pi)) *
      ((x / 2) * Real.sqrt (4 - x ^ 2) + 2 * Real.arcsin (x / 2)) + 1 / 2 := by
  change semicircleCDF x = semicircleAntideriv x
  unfold semicircleCDF
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
    continuous_semicircleAntideriv.continuousOn
    (fun y hy => hasDerivAt_semicircleAntideriv (abs_lt.mpr ⟨hy.1, hy.2.trans_le hx.2⟩))
    (continuous_semicircleDensity.intervalIntegrable _ _), semicircleAntideriv_neg_two, sub_zero]

/-- `F_sc(x) = 0` for `x ≤ -2` (the density `√(4-x²)/(2π)` vanishes off `[-2,2]`). -/
theorem semicircleCDF_of_le_neg_two {x : ℝ} (hx : x ≤ -2) : semicircleCDF x = 0 := by
  unfold semicircleCDF
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun y hy => ?_)]
  · simp
  · rw [uIcc_of_ge hx] at hy
    exact semicircleDensity_eq_zero (by rw [abs_of_neg (by linarith [hy.2])]; linarith [hy.2])

/-- `F_sc(x) = 1` for `x ≥ 2` (total mass one of `√(4-x²)/(2π)`). -/
theorem semicircleCDF_of_two_le {x : ℝ} (hx : 2 ≤ x) : semicircleCDF x = 1 := by
  unfold semicircleCDF
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 2)
    (continuous_semicircleDensity.intervalIntegrable _ _)
    (continuous_semicircleDensity.intervalIntegrable _ _)]
  have h2 : ∫ y in (-2 : ℝ)..2, Parameters.semicircleDensity y = 1 := by
    have := semicircleCDF_eq_antideriv (x := 2) ⟨by norm_num, le_rfl⟩
    unfold semicircleCDF at this
    rw [this]
    exact semicircleAntideriv_two
  rw [h2, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun y hy => ?_)]
  · simp
  · rw [uIcc_of_le hx] at hy
    exact semicircleDensity_eq_zero (by rw [abs_of_pos (by linarith [hy.1])]; linarith [hy.1])

theorem semicircleCDF_neg_two : semicircleCDF (-2) = 0 := semicircleCDF_of_le_neg_two le_rfl

theorem semicircleCDF_two : semicircleCDF 2 = 1 := semicircleCDF_of_two_le le_rfl

/-- **Derivative.** `F_sc' = ρ_sc` at every real `x`, with `ρ_sc(x) = √(4-x²)/(2π)`
(`ρ_sc` is continuous on `ℝ`). -/
theorem hasDerivAt_semicircleCDF (x : ℝ) :
    HasDerivAt semicircleCDF (Parameters.semicircleDensity x) x :=
  (continuous_semicircleDensity.integral_hasStrictDerivAt (-2) x).hasDerivAt

theorem deriv_semicircleCDF (x : ℝ) : deriv semicircleCDF x = Parameters.semicircleDensity x :=
  (hasDerivAt_semicircleCDF x).deriv

theorem differentiable_semicircleCDF : Differentiable ℝ semicircleCDF :=
  fun x => (hasDerivAt_semicircleCDF x).differentiableAt

/-- `F_sc` is continuous on `ℝ`. -/
theorem continuous_semicircleCDF : Continuous semicircleCDF :=
  differentiable_semicircleCDF.continuous

/-- `F_sc` is monotone on `ℝ` (`ρ_sc ≥ 0`). -/
theorem monotone_semicircleCDF : Monotone semicircleCDF :=
  monotone_of_deriv_nonneg differentiable_semicircleCDF
    (fun x => by rw [deriv_semicircleCDF]; exact semicircleDensity_nonneg x)

/-- `F_sc` is strictly monotone on `[-2,2]` (`ρ_sc > 0` on `(-2,2)`). -/
theorem strictMonoOn_semicircleCDF : StrictMonoOn semicircleCDF (Icc (-2 : ℝ) 2) :=
  strictMonoOn_of_deriv_pos (convex_Icc _ _) continuous_semicircleCDF.continuousOn
    (fun x hx => by
      rw [interior_Icc] at hx
      rw [deriv_semicircleCDF]
      exact semicircleDensity_pos (abs_lt.mpr hx))

theorem semicircleCDF_nonneg (x : ℝ) : 0 ≤ semicircleCDF x := by
  rcases le_total x (-2) with h | h
  · rw [semicircleCDF_of_le_neg_two h]
  · rw [← semicircleCDF_neg_two]
    exact monotone_semicircleCDF h

theorem semicircleCDF_le_one (x : ℝ) : semicircleCDF x ≤ 1 := by
  rcases le_total 2 x with h | h
  · rw [semicircleCDF_of_two_le h]
  · rw [← semicircleCDF_two]
    exact monotone_semicircleCDF h

/-!
## The phase identity `F_sc = ℓ + h/2`
-/

theorem normSq_matchedA {E : ℝ} (hE : E ^ 2 ≤ 4) : Complex.normSq (matchedA E) = 1 := by
  have hsq : Real.sqrt (4 - E ^ 2) ^ 2 = 4 - E ^ 2 := Real.sq_sqrt (by linarith)
  simp only [matchedA, Complex.normSq_mk]
  nlinarith

theorem matchedA_inv {E : ℝ} (hE : E ^ 2 ≤ 4) :
    (matchedA E)⁻¹ = ⟨-E / 2, Real.sqrt (4 - E ^ 2) / 2⟩ := by
  apply Complex.ext
  · rw [Complex.inv_re, normSq_matchedA hE, div_one]; rfl
  · rw [Complex.inv_im, normSq_matchedA hE, div_one]
    simp [matchedA]
    ring

/-- `ℓ(E) = 1/2 + π⁻¹ arcsin(E/2)` for `-2 ≤ E ≤ 2` (`ℓ = π⁻¹ Im log a⁻¹`, principal log). -/
theorem phaseEll_eq {E : ℝ} (hE : E ∈ Icc (-2 : ℝ) 2) :
    phaseEll E = 1 / 2 + Real.arcsin (E / 2) / Real.pi := by
  have hE2 : E ^ 2 ≤ 4 := by nlinarith [hE.1, hE.2]
  have hns : Complex.normSq (matchedA E)⁻¹ = 1 := by
    rw [Complex.normSq_inv, normSq_matchedA hE2, inv_one]
  have hnorm : ‖(matchedA E)⁻¹‖ = 1 := by
    have h := Complex.normSq_eq_norm_sq (matchedA E)⁻¹
    rw [hns] at h
    nlinarith [norm_nonneg (matchedA E)⁻¹]
  have hne : (matchedA E)⁻¹ ≠ 0 := by
    intro h
    rw [h, Complex.normSq_zero] at hns
    exact zero_ne_one hns
  have him : 0 ≤ ((matchedA E)⁻¹).im := by
    rw [matchedA_inv hE2]
    exact div_nonneg (Real.sqrt_nonneg _) (by norm_num)
  have hpi := Real.pi_pos
  unfold phaseEll
  rw [Complex.log_im, Complex.arg_of_im_nonneg_of_ne_zero him hne, hnorm, div_one,
    matchedA_inv hE2]
  change Real.arccos (-E / 2) / Real.pi = _
  rw [neg_div, Real.arccos_neg, Real.arccos_eq_pi_div_two_sub_arcsin]
  field_simp
  ring

/-- `h(E) = π⁻¹ Im a² = E √(4-E²) / (2π)`. -/
theorem phaseH_eq (E : ℝ) : phaseH E = E * Real.sqrt (4 - E ^ 2) / (2 * Real.pi) := by
  have hpi := Real.pi_pos
  unfold phaseH
  simp only [matchedA, sq, Complex.mul_im]
  field_simp
  ring

/-- **Phase identity** `F_sc(E) = ℓ(E) + h(E)/2` for `-2 ≤ E ≤ 2`, with `a = (-E - i√(4-E²))/2`
(`matchedA`), `ℓ = π⁻¹ Im log a⁻¹` (principal logarithm, `phaseEll`), `h = π⁻¹ Im a²`
(`phaseH`), `F_sc(E) = ∫_{-2}^E √(4-x²)/(2π) dx`. -/
theorem semicircleCDF_eq_phase {E : ℝ} (hE : E ∈ Icc (-2 : ℝ) 2) :
    semicircleCDF E = phaseEll E + phaseH E / 2 := by
  have hpi := Real.pi_pos
  rw [semicircleCDF_eq_antideriv hE, phaseEll_eq hE, phaseH_eq]
  field_simp
  ring

theorem matchedA_of_four_le_sq {E : ℝ} (hE : 4 ≤ E ^ 2) : matchedA E = ((-E / 2 : ℝ) : ℂ) := by
  have : Real.sqrt (4 - E ^ 2) = 0 := Real.sqrt_eq_zero'.mpr (by linarith)
  apply Complex.ext <;> simp [matchedA, this]

/-- **Phase identity on all of `ℝ`.** Off `[-2,2]`, `a = -E/2` is real, `ℓ ∈ {0,1}`, `h = 0`,
and `F_sc ∈ {0,1}`; so `F_sc(E) = ℓ(E) + h(E)/2` for every real `E`. -/
theorem semicircleCDF_eq_phase_of_real (E : ℝ) :
    semicircleCDF E = phaseEll E + phaseH E / 2 := by
  rcases lt_or_ge E (-2) with h | h
  · have hE : 4 ≤ E ^ 2 := by nlinarith
    rw [semicircleCDF_of_le_neg_two h.le]
    unfold phaseEll phaseH
    rw [matchedA_of_four_le_sq hE, ← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.ofReal_im,
      Complex.log_im, Complex.arg_ofReal_of_nonneg (inv_nonneg.mpr (by linarith))]
    simp
  rcases le_or_gt E 2 with h' | h'
  · exact semicircleCDF_eq_phase ⟨h, h'⟩
  · have hE : 4 ≤ E ^ 2 := by nlinarith
    rw [semicircleCDF_of_two_le h'.le]
    unfold phaseEll phaseH
    rw [matchedA_of_four_le_sq hE, ← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.ofReal_im,
      Complex.log_im, Complex.arg_ofReal_of_neg (inv_lt_zero.mpr (by linarith))]
    have := Real.pi_pos
    field_simp
    simp

/-!
## Classical locations
-/

theorem csInf_semicircleCDF {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    sInf {E : ℝ | t ≤ semicircleCDF E} ∈ Icc (-2 : ℝ) 2 ∧
      semicircleCDF (sInf {E : ℝ | t ≤ semicircleCDF E}) = t := by
  set S := {E : ℝ | t ≤ semicircleCDF E} with hSdef
  have hS2 : (2 : ℝ) ∈ S := by
    show t ≤ semicircleCDF 2
    rw [semicircleCDF_two]; exact ht1
  have hlow : ∀ E ∈ S, -2 < E := by
    intro E hE
    by_contra h
    have := semicircleCDF_of_le_neg_two (not_lt.mp h)
    have hE' : t ≤ semicircleCDF E := hE
    linarith
  have hbdd : BddBelow S := ⟨-2, fun E hE => (hlow E hE).le⟩
  have hclosed : IsClosed S := isClosed_le continuous_const continuous_semicircleCDF
  have hmem : sInf S ∈ S := hclosed.csInf_mem ⟨2, hS2⟩ hbdd
  have he2 : sInf S ≤ 2 := csInf_le hbdd hS2
  have hem2 : -2 ≤ sInf S := le_csInf ⟨2, hS2⟩ (fun E hE => (hlow E hE).le)
  refine ⟨⟨hem2, he2⟩, ?_⟩
  have hmem' : t ≤ semicircleCDF (sInf S) := hmem
  obtain ⟨c, hc, hct⟩ := intermediate_value_Icc hem2 continuous_semicircleCDF.continuousOn
    (show t ∈ Icc (semicircleCDF (-2)) (semicircleCDF (sInf S)) from
      ⟨by rw [semicircleCDF_neg_two]; exact ht0.le, hmem'⟩)
  have hcS : c ∈ S := show t ≤ semicircleCDF c from hct.ge
  have : c = sInf S := le_antisymm hc.2 (csInf_le hbdd hcS)
  rw [← this, hct]

theorem rankFraction_pos (p : Parameters) (α : Fin p.N) :
    0 < ((α.val + 1 : ℕ) : ℝ) / p.N := by
  have := p.N_pos
  positivity

theorem rankFraction_le_one (p : Parameters) (α : Fin p.N) :
    ((α.val + 1 : ℕ) : ℝ) / p.N ≤ 1 := by
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  rw [div_le_one hN]
  exact_mod_cast α.isLt

/-- **Classical location inverts `F_sc`.** `e_α = F_sc⁻¹(α/(nW))` with one-based rank
`α.val + 1` for `α : Fin p.N`, `p.N = nW`, density `√(4-x²)/(2π)` (row variance one).
For every `p` and `α`: `F_sc(e_α) = (α.val+1)/N`. -/
theorem semicircleCDF_classicalLocation (p : Parameters) (α : Fin p.N) :
    semicircleCDF (classicalLocation p α) = ((α.val + 1 : ℕ) : ℝ) / p.N :=
  (csInf_semicircleCDF (rankFraction_pos p α) (rankFraction_le_one p α)).2

/-- `e_α ∈ [-2,2]` for every `p`, `α`. -/
theorem classicalLocation_mem_Icc (p : Parameters) (α : Fin p.N) :
    classicalLocation p α ∈ Icc (-2 : ℝ) 2 :=
  (csInf_semicircleCDF (rankFraction_pos p α) (rankFraction_le_one p α)).1

/-- Edge mass bound `F_sc(-2+κ) ≤ κ/π` for `κ ≥ 0` (from `ρ_sc ≤ 1/π`). -/
theorem semicircleCDF_neg_two_add_le {κ : ℝ} (hκ : 0 ≤ κ) :
    semicircleCDF (-2 + κ) ≤ κ / Real.pi := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -2) (b := -2 + κ) (C := 1 / Real.pi) (f := Parameters.semicircleDensity)
    (fun x _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (semicircleDensity_nonneg x)]
      exact semicircleDensity_le x)
  rw [show -2 + κ - -2 = κ by ring, abs_of_nonneg hκ] at h
  calc semicircleCDF (-2 + κ) ≤ ‖semicircleCDF (-2 + κ)‖ := le_abs_self _
    _ ≤ 1 / Real.pi * κ := h
    _ = κ / Real.pi := by ring

/-- Edge mass bound `1 - κ/π ≤ F_sc(2-κ)` for `κ ≥ 0`. -/
theorem le_semicircleCDF_two_sub {κ : ℝ} (hκ : 0 ≤ κ) :
    1 - κ / Real.pi ≤ semicircleCDF (2 - κ) := by
  have hsplit : semicircleCDF 2 = semicircleCDF (2 - κ) +
      ∫ x in (2 - κ)..2, Parameters.semicircleDensity x := by
    unfold semicircleCDF
    rw [intervalIntegral.integral_add_adjacent_intervals
      (continuous_semicircleDensity.intervalIntegrable _ _)
      (continuous_semicircleDensity.intervalIntegrable _ _)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 2 - κ) (b := 2) (C := 1 / Real.pi) (f := Parameters.semicircleDensity)
    (fun x _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (semicircleDensity_nonneg x)]
      exact semicircleDensity_le x)
  rw [show 2 - (2 - κ) = κ by ring, abs_of_nonneg hκ] at h
  rw [semicircleCDF_two] at hsplit
  have h' := (le_abs_self _).trans h
  have : 1 / Real.pi * κ = κ / Real.pi := by ring
  linarith

/-- **Bulk ranks have bulk classical locations, with explicit `κ(ϑ) = ϑ`.** With
`e_α = F_sc⁻¹(α/(nW))` as in the rank-location theorem; `IsBulkRank p ϑ α` is
`ϑ ≤ (α.val+1)/N ≤ 1-ϑ`, density `√(4-x²)/(2π)` (row variance one). For every `ϑ > 0` (in particular
`0 < ϑ < 1/2`), uniformly in `p` and `α`: `e_α ∈ [-2+ϑ, 2-ϑ] = bulkInterval ϑ`. -/
theorem classicalLocation_mem_bulkInterval {ϑ : ℝ} (hϑ : 0 < ϑ) (p : Parameters)
    (α : Fin p.N) (hα : IsBulkRank p ϑ α) :
    classicalLocation p α ∈ bulkInterval ϑ := by
  have hF := semicircleCDF_classicalLocation p α
  have hpi : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have hlt : ϑ / Real.pi < ϑ := div_lt_self hϑ hpi
  obtain ⟨h1, h2⟩ := hα
  constructor
  · by_contra h
    have hm := monotone_semicircleCDF (not_le.mp h).le
    have := semicircleCDF_neg_two_add_le hϑ.le
    linarith
  · by_contra h
    have hm := monotone_semicircleCDF (not_le.mp h).le
    have := le_semicircleCDF_two_sub hϑ.le
    linarith

/-- Existence form: for `0 < ϑ < 1/2` there is `κ > 0`, independent of `p` and `α`, with
`e_α ∈ [-2+κ, 2-κ]` for every bulk rank. -/
theorem exists_bulkInterval_classicalLocation {ϑ : ℝ} (hϑ : 0 < ϑ) (_hϑ' : ϑ < 1 / 2) :
    ∃ κ > 0, ∀ (p : Parameters) (α : Fin p.N), IsBulkRank p ϑ α →
      classicalLocation p α ∈ Icc (-2 + κ) (2 - κ) :=
  ⟨ϑ, hϑ, fun p α hα => classicalLocation_mem_bulkInterval hϑ p α hα⟩

end BlockBand.RankLocation
