module

public import BlockBand.Critical.GlobalSource.Tightness

/-!
# Global Gaussian source, source replacement: the scalar Taylor step and Lindeberg bookkeeping

* `norm_exp_two_scale_sub_le`: `|e^{i(ta+t²c)} - (1 + ita - t²a²/2 + it²c)| ≤
  t³(4|a|³ + |a||c| + 5c²)` for `0 ≤ t ≤ 1` (the retained `‖C‖²` term is `c²`);
* `enorm_integral_exp_sub_le`: one Lindeberg swap — if the first two Taylor terms have equal
  means (equal mean, covariance and zero pseudo-covariance), the characteristic values differ by
  at most the expected remainder;
* `measurePreserving_update_pi`, `integral_pi_eq_integral_update`,
  `lintegral_pi_eq_lintegral_update`: resampling one coordinate of a product law;
* `norm_sub_le_card_mul_of_insert`: telescoping over the swapped coordinates.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate NNReal ENNReal
open Complex (exp I)

/-!
## Scalar Taylor bounds for `e^{ix}`
-/

theorem norm_exp_mul_I_sub_one_le' (x : ℝ) : ‖exp ((x : ℂ) * I) - 1‖ ≤ |x| := by
  rw [mul_comm]
  simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := x)

/-- Real and imaginary parts of `e^{ix} - 1 - ix + x²/2`. -/
theorem exp_mul_I_taylor_eq (x : ℝ) :
    exp ((x : ℂ) * I) - 1 - (x : ℂ) * I + (x : ℂ) ^ 2 / 2 =
      ((Real.cos x - (1 - x ^ 2 / 2) : ℝ) : ℂ) + ((Real.sin x - x : ℝ) : ℂ) * I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

theorem norm_exp_mul_I_taylor_two_le (x : ℝ) :
    ‖exp ((x : ℂ) * I) - 1 - (x : ℂ) * I + (x : ℂ) ^ 2 / 2‖ ≤ 4 * |x| ^ 3 := by
  rcases le_or_gt |x| 1 with hx | hx
  · rw [exp_mul_I_taylor_eq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := Real.cos_bound hx
    have h2 := Real.sin_bound hx
    have hs : |Real.sin x - x| ≤ |x| ^ 5 / 100 + |x| ^ 3 / 6 := by
      have : Real.sin x - x = (Real.sin x - (x - x ^ 3 / 6)) + (-(x ^ 3 / 6)) := by ring
      rw [this]
      refine (abs_add_le _ _).trans (add_le_add h2 (le_of_eq ?_))
      rw [abs_neg, abs_div, abs_pow]; norm_num
    have ha := abs_nonneg x
    have h4 : |x| ^ 4 ≤ |x| ^ 3 := pow_le_pow_of_le_one ha hx (by norm_num)
    have h5 : |x| ^ 5 ≤ |x| ^ 3 := pow_le_pow_of_le_one ha hx (by norm_num)
    nlinarith
  · have hn : ‖exp ((x : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I x
    have h1 : ‖exp ((x : ℂ) * I) - 1 - (x : ℂ) * I + (x : ℂ) ^ 2 / 2‖ ≤
        1 + 1 + |x| + |x| ^ 2 / 2 := by
      refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
        (add_le_add ((norm_sub_le _ _).trans (by rw [hn, norm_one])) le_rfl)) le_rfl) |>.trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, norm_div,
        norm_pow, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    have h2 : (1 : ℝ) ≤ |x| ^ 3 := one_le_pow₀ hx.le
    have h3 : |x| ≤ |x| ^ 3 := le_self_pow₀ hx.le (by norm_num)
    have h4 : |x| ^ 2 ≤ |x| ^ 3 := pow_le_pow_right₀ hx.le (by norm_num)
    linarith

theorem norm_exp_mul_I_taylor_one_le (x : ℝ) :
    ‖exp ((x : ℂ) * I) - 1 - (x : ℂ) * I‖ ≤ 5 * x ^ 2 := by
  have h := norm_exp_mul_I_taylor_two_le x
  rcases le_or_gt |x| 1 with hx | hx
  · have : exp ((x : ℂ) * I) - 1 - (x : ℂ) * I =
        (exp ((x : ℂ) * I) - 1 - (x : ℂ) * I + (x : ℂ) ^ 2 / 2) - (x : ℂ) ^ 2 / 2 := by ring
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have h3 : |x| ^ 3 ≤ |x| ^ 2 := pow_le_pow_of_le_one (abs_nonneg x) hx (by norm_num)
    have : |x| ^ 2 = x ^ 2 := sq_abs x
    norm_num
    nlinarith
  · have hn : ‖exp ((x : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I x
    have h1 : ‖exp ((x : ℂ) * I) - 1 - (x : ℂ) * I‖ ≤ 1 + 1 + |x| := by
      refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
        (by rw [hn, norm_one])) le_rfl) |>.trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have h2 : (1 : ℝ) ≤ x ^ 2 := by rw [← sq_abs]; exact one_le_pow₀ hx.le
    have h3 : |x| ≤ x ^ 2 := by rw [← sq_abs]; exact le_self_pow₀ hx.le (by norm_num)
    linarith

/-- **The scalar Taylor step** for `e^{i(ta + t²c)}` (`a`, `c` real, `0 ≤ t ≤ 1`). -/
theorem norm_exp_two_scale_sub_le (t a c : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖exp (((t * a + t ^ 2 * c : ℝ) : ℂ) * I) -
        (1 + ((t * a : ℝ) : ℂ) * I - ((t * a : ℝ) : ℂ) ^ 2 / 2 + ((t ^ 2 * c : ℝ) : ℂ) * I)‖ ≤
      t ^ 3 * (4 * |a| ^ 3 + |a| * |c| + 5 * c ^ 2) := by
  set A := exp (((t * a : ℝ) : ℂ) * I)
  set B := exp (((t ^ 2 * c : ℝ) : ℂ) * I)
  have hAB : exp (((t * a + t ^ 2 * c : ℝ) : ℂ) * I) = A * B := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hdec : A * B - (1 + ((t * a : ℝ) : ℂ) * I - ((t * a : ℝ) : ℂ) ^ 2 / 2 +
      ((t ^ 2 * c : ℝ) : ℂ) * I) =
      (A - 1 - ((t * a : ℝ) : ℂ) * I + ((t * a : ℝ) : ℂ) ^ 2 / 2) + (A - 1) * (B - 1) +
        (B - 1 - ((t ^ 2 * c : ℝ) : ℂ) * I) := by ring
  rw [hAB, hdec]
  have h1 := norm_exp_mul_I_taylor_two_le (t * a)
  have h2 := norm_exp_mul_I_sub_one_le' (t * a)
  have h3 := norm_exp_mul_I_sub_one_le' (t ^ 2 * c)
  have h4 := norm_exp_mul_I_taylor_one_le (t ^ 2 * c)
  have hm : ‖(A - 1) * (B - 1)‖ ≤ |t * a| * |t ^ 2 * c| := by
    rw [norm_mul]; exact mul_le_mul h2 h3 (norm_nonneg _) (abs_nonneg _)
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg (pow_nonneg ht0 2)] at *
  have ht4 : t ^ 4 ≤ t ^ 3 := pow_le_pow_of_le_one ht0 ht1 (by norm_num)
  have hc : 0 ≤ c ^ 2 := sq_nonneg c
  have e1 : (t * |a|) ^ 3 = t ^ 3 * |a| ^ 3 := by ring
  have e2 : t * |a| * (t ^ 2 * |c|) = t ^ 3 * (|a| * |c|) := by ring
  have e3 : (t ^ 2 * c) ^ 2 = t ^ 4 * c ^ 2 := by ring
  rw [e1] at h1
  rw [e2] at hm
  rw [e3] at h4
  nlinarith [mul_le_mul_of_nonneg_right ht4 hc]

/-!
## One Lindeberg swap for a characteristic test
-/

/-- **One Lindeberg swap.** Two random scalars `θ_i = θ₀ + tα_i + t²β_i` on one probability space,
whose first two Taylor terms have the same mean (`E α₁ = E α₂`, `E α₁² = E α₂²`, `E β₁ = E β₂`),
have characteristic values at distance at most the third-order remainder. -/
theorem enorm_integral_exp_sub_le {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] (θ₀ t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (α₁ β₁ α₂ β₂ : Y → ℝ)
    (hα₁ : Integrable α₁ μ) (hα₁2 : Integrable (fun y => α₁ y ^ 2) μ) (hβ₁ : Integrable β₁ μ)
    (hα₂ : Integrable α₂ μ) (hα₂2 : Integrable (fun y => α₂ y ^ 2) μ) (hβ₂ : Integrable β₂ μ)
    (hm1 : ∫ y, α₁ y ∂μ = ∫ y, α₂ y ∂μ) (hm2 : ∫ y, α₁ y ^ 2 ∂μ = ∫ y, α₂ y ^ 2 ∂μ)
    (hm3 : ∫ y, β₁ y ∂μ = ∫ y, β₂ y ∂μ) :
    ‖∫ y, exp (((θ₀ + t * α₁ y + t ^ 2 * β₁ y : ℝ) : ℂ) * I) ∂μ -
        ∫ y, exp (((θ₀ + t * α₂ y + t ^ 2 * β₂ y : ℝ) : ℂ) * I) ∂μ‖ₑ ≤
      ∫⁻ y, ENNReal.ofReal (t ^ 3 * (4 * |α₁ y| ^ 3 + |α₁ y| * |β₁ y| + 5 * β₁ y ^ 2)) ∂μ +
        ∫⁻ y, ENNReal.ofReal (t ^ 3 * (4 * |α₂ y| ^ 3 + |α₂ y| * |β₂ y| + 5 * β₂ y ^ 2)) ∂μ := by
  -- the exponential and its second-order polynomial
  let E : (Y → ℝ) → (Y → ℝ) → Y → ℂ := fun α β y =>
    exp (((t * α y + t ^ 2 * β y : ℝ) : ℂ) * I)
  let P : (Y → ℝ) → (Y → ℝ) → Y → ℂ := fun α β y =>
    1 + ((t * α y : ℝ) : ℂ) * I - ((t * α y : ℝ) : ℂ) ^ 2 / 2 + ((t ^ 2 * β y : ℝ) : ℂ) * I
  have hsplit : ∀ (α β : Y → ℝ) (y : Y), exp (((θ₀ + t * α y + t ^ 2 * β y : ℝ) : ℂ) * I) =
      exp ((θ₀ : ℂ) * I) * E α β y := by
    intro α β y
    simp only [E]; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hEint : ∀ (α β : Y → ℝ), Integrable α μ → Integrable β μ → Integrable (E α β) μ := by
    intro α β hα hβ
    have hm : AEStronglyMeasurable (E α β) μ :=
      (Continuous.comp_aestronglyMeasurable (g := fun p : ℝ × ℝ =>
        exp (((t * p.1 + t ^ 2 * p.2 : ℝ) : ℂ) * I)) (by fun_prop)
        (hα.aestronglyMeasurable.prodMk hβ.aestronglyMeasurable))
    exact (integrable_const (1 : ℝ)).mono' hm (ae_of_all _ fun y => by
      simp only [E]; rw [Complex.norm_exp_ofReal_mul_I])
  have hPe : ∀ (α β : Y → ℝ), P α β = fun y => (1 : ℂ) + ((t : ℂ) * I) * (α y : ℂ) -
      ((t : ℂ) ^ 2 / 2) * ((α y ^ 2 : ℝ) : ℂ) + ((t : ℂ) ^ 2 * I) * (β y : ℂ) := by
    intro α β; funext y; simp only [P]; push_cast; ring
  have hPint : ∀ (α β : Y → ℝ), Integrable α μ → Integrable (fun y => α y ^ 2) μ →
      Integrable β μ → Integrable (P α β) μ := by
    intro α β hα hα2 hβ
    rw [hPe]
    exact (((integrable_const _).add (hα.ofReal.const_mul _)).sub
      (hα2.ofReal.const_mul _)).add (hβ.ofReal.const_mul _)
  have hPeq : ∀ (α β : Y → ℝ), Integrable α μ → Integrable (fun y => α y ^ 2) μ →
      Integrable β μ → ∫ y, P α β y ∂μ = 1 + (t : ℂ) * I * ((∫ y, α y ∂μ : ℝ) : ℂ) -
        (t : ℂ) ^ 2 / 2 * ((∫ y, α y ^ 2 ∂μ : ℝ) : ℂ) + (t : ℂ) ^ 2 * I * ((∫ y, β y ∂μ : ℝ) : ℂ) := by
    intro α β hα hα2 hβ
    rw [hPe, integral_add, integral_sub, integral_add, integral_const, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
      integral_complex_ofReal]
    · simp
    · exact integrable_const _
    · exact hα.ofReal.const_mul _
    · exact (integrable_const _).add (hα.ofReal.const_mul _)
    · exact hα2.ofReal.const_mul _
    · exact ((integrable_const _).add (hα.ofReal.const_mul _)).sub (hα2.ofReal.const_mul _)
    · exact hβ.ofReal.const_mul _
  have hP12 : ∫ y, P α₁ β₁ y ∂μ = ∫ y, P α₂ β₂ y ∂μ := by
    rw [hPeq α₁ β₁ hα₁ hα₁2 hβ₁, hPeq α₂ β₂ hα₂ hα₂2 hβ₂, hm1, hm2, hm3]
  simp_rw [hsplit]
  rw [integral_const_mul, integral_const_mul, ← mul_sub, enorm_mul,
    show ‖exp ((θ₀ : ℂ) * I)‖ₑ = 1 by rw [← ofReal_norm, Complex.norm_exp_ofReal_mul_I,
      ENNReal.ofReal_one], one_mul]
  have hdiff : ∫ y, E α₁ β₁ y ∂μ - ∫ y, E α₂ β₂ y ∂μ =
      ∫ y, (E α₁ β₁ y - P α₁ β₁ y) ∂μ - ∫ y, (E α₂ β₂ y - P α₂ β₂ y) ∂μ := by
    rw [integral_sub (hEint _ _ hα₁ hβ₁) (hPint _ _ hα₁ hα₁2 hβ₁),
      integral_sub (hEint _ _ hα₂ hβ₂) (hPint _ _ hα₂ hα₂2 hβ₂), hP12]
    ring
  have hrem : ∀ (α β : Y → ℝ), ‖∫ y, (E α β y - P α β y) ∂μ‖ₑ ≤
      ∫⁻ y, ENNReal.ofReal (t ^ 3 * (4 * |α y| ^ 3 + |α y| * |β y| + 5 * β y ^ 2)) ∂μ := by
    intro α β
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_exp_two_scale_sub_le t (α y) (β y) ht0 ht1)
  rw [hdiff]
  exact (enorm_sub_le).trans (add_le_add (hrem _ _) (hrem _ _))

/-!
## Swapping one coordinate of a product law
-/

/-- Resampling one coordinate of a product of probability laws preserves the product law. -/
theorem measurePreserving_update_pi {ι Y : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Y]
    (μ : ι → Measure Y) [∀ i, IsProbabilityMeasure (μ i)] (j : ι) :
    MeasurePreserving (fun p : (ι → Y) × Y => Function.update p.1 j p.2)
      ((Measure.pi μ).prod (μ j)) (Measure.pi μ) := by
  have hU : Measurable fun p : (ι → Y) × Y => Function.update p.1 j p.2 := measurable_update'
  refine ⟨hU, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hU (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → Y) × Y => Function.update p.1 j p.2) ⁻¹' Set.univ.pi s =
      (Set.univ.pi (Function.update s j Set.univ)) ×ˢ s j := by
    ext ⟨x, y⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, by simpa using h j⟩
      by_cases hij : i = j
      · subst hij; simp
      · simpa [Function.update_of_ne hij] using h i
    · rintro ⟨h1, h2⟩ i
      by_cases hij : i = j
      · subst hij; simpa using h2
      · simpa [Function.update_of_ne hij] using h1 i
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have hfun : (fun i => μ i (Function.update s j Set.univ i)) =
      Function.update (fun i => μ i (s i)) j 1 := by
    funext i
    by_cases hij : i = j
    · subst hij; simp
    · simp [Function.update_of_ne hij]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ j), one_mul,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ j), Finset.sdiff_singleton_eq_erase]

/-- Fubini form of `measurePreserving_update_pi` for integrals. -/
theorem integral_pi_eq_integral_update {ι Y : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Y]
    (μ : ι → Measure Y) [∀ i, IsProbabilityMeasure (μ i)] (j : ι) {f : (ι → Y) → ℂ}
    (hf : Integrable f (Measure.pi μ)) :
    ∫ x, f x ∂Measure.pi μ = ∫ x, ∫ y, f (Function.update x j y) ∂μ j ∂Measure.pi μ := by
  have hU := measurePreserving_update_pi μ j
  have hint : Integrable (fun p : (ι → Y) × Y => f (Function.update p.1 j p.2))
      ((Measure.pi μ).prod (μ j)) := hU.integrable_comp hf.aestronglyMeasurable |>.2 hf
  rw [← integral_prod _ hint]
  conv_lhs => rw [← hU.map_eq]
  exact integral_map hU.measurable.aemeasurable (by rw [hU.map_eq]; exact hf.aestronglyMeasurable)

/-- Fubini form of `measurePreserving_update_pi` for lower integrals. -/
theorem lintegral_pi_eq_lintegral_update {ι Y : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Y] (μ : ι → Measure Y) [∀ i, IsProbabilityMeasure (μ i)] (j : ι)
    {f : (ι → Y) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂Measure.pi μ = ∫⁻ x, ∫⁻ y, f (Function.update x j y) ∂μ j ∂Measure.pi μ := by
  have hU := measurePreserving_update_pi μ j
  rw [← lintegral_prod (fun p : (ι → Y) × Y => f (Function.update p.1 j p.2))
    (hf.comp hU.measurable).aemeasurable]
  conv_lhs => rw [← hU.map_eq]
  exact lintegral_map hf hU.measurable

/-!
## Telescoping over a growing set of swapped coordinates
-/

theorem norm_sub_le_card_mul_of_insert {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset ι → ℂ) (c : ℝ) (h : ∀ S j, j ∉ S → ‖F (insert j S) - F S‖ ≤ c) :
    ‖F Finset.univ - F ∅‖ ≤ Fintype.card ι * c := by
  have key : ∀ S : Finset ι, ‖F S - F ∅‖ ≤ S.card * c := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih =>
      calc ‖F (insert j S) - F ∅‖ ≤ ‖F (insert j S) - F S‖ + ‖F S - F ∅‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ c + S.card * c := add_le_add (h S j hj) ih
        _ = (insert j S).card * c := by rw [Finset.card_insert_of_notMem hj]; push_cast; ring
  simpa using key Finset.univ

end BlockBand.Critical.GlobalSource
