module

public import BlockBand.Endpoints.Sine.MicroscopicTagClock

/-!
# Measurability, bounds and positivity of the two sides of the tag comparison

This file proves the measurability, boundedness and positivity properties of the two sides of the
microscopic tag comparison that are needed to integrate them and to use their positivity and
linearity in the test. The laws are the exact physical law `model.law`, the path law
`probedClockLaw W b` and Lebesgue measure in the microscopic energy `u`.

## Main results

* `pathIntegrand`: the integrand `r⁻¹ Σ_K Φ(Z_{r;K}/M_r)` of `pathTagExpect` (definitionally);
  `tagClock_div_meanClock`: `Z_{r;K}/M_r = r h*Y_{r;K}h / h*Y^{int}h`.
* Joint measurability in `(u, ω, h)` and the bound `‖Φ‖` for the path integrands
  (`measurable_pathIntegrand_of`, `measurable_leadAveragedTest_of`), hence strong measurability
  of `u ↦ E_{path,h}[…](e(u))` (`stronglyMeasurable_pathTagExpect`, …).
* `abs_integral_weight_sub_le`, `abs_integral_sum_test_sub_le`: the positive-functional estimate
  `|T(Φ₁) - T(Φ₂)| ≤ δ T(1) + K T(Φ₃)` whenever `|Φ₁ - Φ₂| ≤ δ + KΦ₃` pointwise, used for both
  `T = physicalTagSide` and `T = pathTagSide` (nonnegative `w`) in `physicalTagSide_abs_sub_le`
  and `pathTagSide_abs_sub_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open scoped ENNReal NNReal BoundedContinuousFunction

theorem continuous_projIci_zero : Continuous (Set.projIci (0 : ℝ)) :=
  continuous_induced_rng.2 (continuous_const.max continuous_id)

theorem norm_test_le (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (z : Set.Ici (0 : ℝ)) : |Φ z| ≤ ‖Φ‖ := by
  rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm z

/-- The integrand `r⁻¹ Σ_K Φ(Z_{r;K}/M_r)` of `pathTagExpect`. -/
def pathIntegrand (b e : ℝ) (W r : ℕ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ)
    (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : ℝ :=
  (r : ℝ)⁻¹ * ∑ K : Fin r, Φ (Set.projIci 0 (tagClock b e W r K x / meanClock b e W r x))

theorem pathTagExpect_eq (b e : ℝ) (W r : ℕ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) :
    pathTagExpect b e W r Φ = ∫ x, pathIntegrand b e W r Φ x ∂probedClockLaw W b := rfl

theorem tagClock_div_meanClock {b e : ℝ} {W r : ℕ} (hW : 0 < W) (K : Fin r)
    (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    tagClock b e W r K x / meanClock b e W r x =
      (r : ℝ) * leadPositionMass b e W r x.1 x.2 (Sum.inl K) / interiorLeadMass b e W r x := by
  have hW' : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have hr : (r : ℝ) ≠ 0 := by
    have : 0 < r := Fin.pos K
    exact_mod_cast this.ne'
  unfold tagClock meanClock
  rcases eq_or_ne (interiorLeadMass b e W r x) 0 with h | h
  · rw [h]; simp
  · field_simp

theorem tagRatio_nonneg {b e : ℝ} {W r : ℕ} (hW : 0 < W) (K : Fin r)
    (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    0 ≤ tagClock b e W r K x / meanClock b e W r x := by
  rw [tagClock_div_meanClock hW]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (leadPositionMass_nonneg _ _ _ _ _))
    (interiorLeadMass_nonneg _ _ _)

/-- The tag ratios average to at most one: `r⁻¹ Σ_K Z_{r;K}/M_r ≤ 1` (`= 1` off the null
event `M_r = 0`). -/
theorem sum_tagRatio_le {b e : ℝ} {W r : ℕ} (hW : 0 < W)
    (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    (r : ℝ)⁻¹ * ∑ K : Fin r, tagClock b e W r K x / meanClock b e W r x ≤ 1 := by
  simp_rw [tagClock_div_meanClock hW]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [← Finset.sum_div, ← Finset.mul_sum]
  rcases eq_or_lt_of_le (interiorLeadMass_nonneg b e (r := r) x) with h | h
  · rw [← h, div_zero, mul_zero]; exact zero_le_one
  · have : ∑ i, leadPositionMass b e W r x.1 x.2 (Sum.inl i) = interiorLeadMass b e W r x := rfl
    rw [this, mul_div_assoc, div_self h.ne', mul_one, inv_mul_cancel₀ hr']

/-!
## Measurability and bounds of the path integrands
-/

theorem measurable_tagRatio_of (b : ℝ) (W r : ℕ) (K : Fin r) {α : Type*} [MeasurableSpace α]
    {e : α → ℝ} {x : α → GrowthPath W × (Fin 2 × Fin W → ℂ)} (he : Measurable e)
    (hx : Measurable x) :
    Measurable (fun a => tagClock b (e a) W r K (x a) / meanClock b (e a) W r (x a)) := by
  unfold tagClock meanClock interiorLeadMass
  exact (measurable_const.mul (measurable_leadPositionMass_of b W r (Sum.inl K) he hx)).div
    (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      measurable_leadPositionMass_of b W r (Sum.inl i) he hx))

theorem measurable_pathIntegrand_of (b : ℝ) (W r : ℕ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) {α : Type*}
    [MeasurableSpace α] {e : α → ℝ} {x : α → GrowthPath W × (Fin 2 × Fin W → ℂ)}
    (he : Measurable e) (hx : Measurable x) :
    Measurable (fun a => pathIntegrand b (e a) W r Φ (x a)) := by
  unfold pathIntegrand
  exact measurable_const.mul (Finset.measurable_sum _ fun K _ =>
    Φ.continuous.measurable.comp (continuous_projIci_zero.measurable.comp
      (measurable_tagRatio_of b W r K he hx)))

theorem measurable_leadAveragedTest_of (b : ℝ) (n W : ℕ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ)
    {α : Type*} [MeasurableSpace α] {e : α → ℝ} {x : α → GrowthPath W × (Fin 2 × Fin W → ℂ)}
    (he : Measurable e) (hx : Measurable x) :
    Measurable (fun a => leadAveragedTest b (e a) n W Φ (x a)) := by
  unfold leadAveragedTest totalLeadMass
  refine measurable_const.mul (measurable_const.add (Finset.measurable_sum _ fun y _ => ?_))
  exact Φ.continuous.measurable.comp (continuous_projIci_zero.measurable.comp
    ((measurable_const.mul (measurable_leadPositionMass_of b W (n - 3) y he hx)).div
      (Finset.measurable_sum _ fun y' _ => measurable_leadPositionMass_of b W (n - 3) y' he hx)))

theorem abs_pathIntegrand_le (b e : ℝ) (W r : ℕ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ)
    (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : |pathIntegrand b e W r Φ x| ≤ ‖Φ‖ := by
  unfold pathIntegrand
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [abs_mul, abs_of_pos (inv_pos.2 hr')]
  calc (r : ℝ)⁻¹ * |∑ K : Fin r, Φ (Set.projIci 0 (tagClock b e W r K x / meanClock b e W r x))|
      ≤ (r : ℝ)⁻¹ * ∑ _K : Fin r, ‖Φ‖ :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun K _ => norm_test_le Φ _)) (by positivity)
    _ = ‖Φ‖ := by simp [field]

theorem abs_leadAveragedTest_le (b e : ℝ) {n : ℕ} (hn : 4 ≤ n) (W : ℕ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ)
    (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : |leadAveragedTest b e n W Φ x| ≤ ‖Φ‖ := by
  unfold leadAveragedTest
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [abs_mul, abs_of_pos (inv_pos.2 hn')]
  have hcard : ((n - 3 : ℕ) : ℝ) + 2 + 1 = n := by
    rw [Nat.cast_sub (by omega : 3 ≤ n)]; push_cast; ring
  calc (n : ℝ)⁻¹ * |Φ (Set.projIci 0 0) + ∑ y : Fin (n - 3) ⊕ Fin 2,
        Φ (Set.projIci 0 ((n : ℝ) * leadPositionMass b e W (n - 3) x.1 x.2 y /
          totalLeadMass b e W (n - 3) x))|
      ≤ (n : ℝ)⁻¹ * (‖Φ‖ + ∑ _y : Fin (n - 3) ⊕ Fin 2, ‖Φ‖) := by
        refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add (norm_test_le Φ _)
          ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ =>
            norm_test_le Φ _)))) (by positivity)
    _ = ‖Φ‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        rw [show (‖Φ‖ + ((n - 3 : ℕ) + 2 : ℝ) * ‖Φ‖) = (((n - 3 : ℕ) : ℝ) + 2 + 1) * ‖Φ‖ by ring,
          hcard]
        field_simp

/-!
## Strong measurability in the microscopic energy
-/

theorem measurable_microEnergy (p : Parameters) (E : ℝ) : Measurable (microEnergy p E) := by
  unfold microEnergy; fun_prop

theorem stronglyMeasurable_pathTagExpect (p : Parameters) (E : ℝ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) :
    StronglyMeasurable (fun u => pathTagExpect p.b (microEnergy p E u) p.W (p.n - 3) Φ) := by
  have := isProbabilityMeasure_probedClockLaw p.W p.b
  have hm := measurable_pathIntegrand_of p.b p.W (p.n - 3) Φ
    (α := ℝ × (GrowthPath p.W × (Fin 2 × Fin p.W → ℂ)))
    ((measurable_microEnergy p E).comp measurable_fst) measurable_snd
  exact hm.stronglyMeasurable.integral_prod_right'

theorem stronglyMeasurable_leadExpect (p : Parameters) (E : ℝ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) :
    StronglyMeasurable (fun u => ∫ x, leadAveragedTest p.b (microEnergy p E u) p.n p.W Φ x
      ∂probedClockLaw p.W p.b) := by
  have := isProbabilityMeasure_probedClockLaw p.W p.b
  have hm := measurable_leadAveragedTest_of p.b p.n p.W Φ
    (α := ℝ × (GrowthPath p.W × (Fin 2 × Fin p.W → ℂ)))
    ((measurable_microEnergy p E).comp measurable_fst) measurable_snd
  exact hm.stronglyMeasurable.integral_prod_right'

theorem abs_pathTagExpect_le (b e : ℝ) (W r : ℕ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) :
    |pathTagExpect b e W r Φ| ≤ ‖Φ‖ := by
  have := isProbabilityMeasure_probedClockLaw W b
  rw [pathTagExpect_eq, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := ‖Φ‖) (Eventually.of_forall fun x => ?_)).trans
    (by simp)
  rw [Real.norm_eq_abs]; exact abs_pathIntegrand_le b e W r Φ x

theorem abs_leadExpect_le (b e : ℝ) {n : ℕ} (hn : 4 ≤ n) (W : ℕ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) :
    |∫ x, leadAveragedTest b e n W Φ x ∂probedClockLaw W b| ≤ ‖Φ‖ := by
  have := isProbabilityMeasure_probedClockLaw W b
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := ‖Φ‖) (Eventually.of_forall fun x => ?_)).trans
    (by simp)
  rw [Real.norm_eq_abs]; exact abs_leadAveragedTest_le b e hn W Φ x

/-!
## A weighted `u`-integral estimate
-/

/-- `|∫ w A₁ - ∫ w A₂| ≤ δ ∫ w A₀ + K ∫ w A₃` for `w ≥ 0` integrable and bounded strongly
measurable `A_i` with `|A₁ - A₂| ≤ δ A₀ + K A₃` pointwise. -/
theorem abs_integral_weight_sub_le {w : ℝ → ℝ} (hw : ∀ u, 0 ≤ w u) (hwi : Integrable w)
    {A₁ A₂ A₀ A₃ : ℝ → ℝ} {C δ K : ℝ}
    (h₁ : StronglyMeasurable A₁) (h₂ : StronglyMeasurable A₂) (h₀ : StronglyMeasurable A₀)
    (h₃ : StronglyMeasurable A₃) (hb₁ : ∀ u, |A₁ u| ≤ C) (hb₂ : ∀ u, |A₂ u| ≤ C)
    (hb₀ : ∀ u, |A₀ u| ≤ C) (hb₃ : ∀ u, |A₃ u| ≤ C)
    (hbd : ∀ u, |A₁ u - A₂ u| ≤ δ * A₀ u + K * A₃ u) :
    |(∫ u, w u * A₁ u) - ∫ u, w u * A₂ u| ≤
      δ * (∫ u, w u * A₀ u) + K * ∫ u, w u * A₃ u := by
  have hi : ∀ {A : ℝ → ℝ}, StronglyMeasurable A → (∀ u, |A u| ≤ C) →
      Integrable (fun u => w u * A u) := fun hA hbA =>
    hwi.mul_bdd hA.aestronglyMeasurable (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]; exact hbA u)
  rw [← integral_sub (hi h₁ hb₁) (hi h₂ hb₂), ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hi h₀ hb₀).const_mul δ) ((hi h₃ hb₃).const_mul K), ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => norm_nonneg _)
    (((hi h₀ hb₀).const_mul δ).add ((hi h₃ hb₃).const_mul K))
    (Eventually.of_forall fun u => ?_))
  simp only [Real.norm_eq_abs]
  rw [← mul_sub, abs_mul, abs_of_nonneg (hw u)]
  calc w u * |A₁ u - A₂ u| ≤ w u * (δ * A₀ u + K * A₃ u) :=
        mul_le_mul_of_nonneg_left (hbd u) (hw u)
    _ = δ * (w u * A₀ u) + K * (w u * A₃ u) := by ring

/-!
## The positive-functional estimate
-/

/-- Generic form: for nonnegative bounded measurable weights `c` and positions `z`,
`T(Φ) = ∫ Σ_i c_i Φ(z_i)` satisfies `|T Φ₁ - T Φ₂| ≤ δ T(1) + K T(Φ₃)` when
`|Φ₁ - Φ₂| ≤ δ + KΦ₃`. -/
theorem abs_integral_sum_test_sub_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (c z : Ω → ι → ℝ) (hc : ∀ ω i, 0 ≤ c ω i)
    (hcm : ∀ i, Measurable fun ω => c ω i) (hzm : ∀ i, Measurable fun ω => z ω i)
    {B : ℝ} (hcb : ∀ ω i, c ω i ≤ B) (Φ₁ Φ₂ Φ₃ : Set.Ici (0 : ℝ) →ᵇ ℝ) {δ K : ℝ}
    (hbd : ∀ y, |Φ₁ y - Φ₂ y| ≤ δ + K * Φ₃ y) :
    |(∫ ω, ∑ i, c ω i * Φ₁ (Set.projIci 0 (z ω i)) ∂μ) -
        ∫ ω, ∑ i, c ω i * Φ₂ (Set.projIci 0 (z ω i)) ∂μ| ≤
      δ * (∫ ω, ∑ i, c ω i ∂μ) + K * ∫ ω, ∑ i, c ω i * Φ₃ (Set.projIci 0 (z ω i)) ∂μ := by
  have hint : ∀ Φ : Set.Ici (0 : ℝ) →ᵇ ℝ,
      Integrable (fun ω => ∑ i, c ω i * Φ (Set.projIci 0 (z ω i))) μ := by
    intro Φ
    refine integrable_finsetSum _ fun i _ => ?_
    refine Integrable.of_bound ((hcm i).mul (Φ.continuous.measurable.comp
      (continuous_projIci_zero.measurable.comp (hzm i)))).aestronglyMeasurable (B * ‖Φ‖)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc ω i)]
    exact mul_le_mul (hcb ω i) (norm_test_le Φ _) (abs_nonneg _) ((hc ω i).trans (hcb ω i))
  have hint0 : Integrable (fun ω => ∑ i, c ω i) μ := by
    refine integrable_finsetSum _ fun i _ => ?_
    refine Integrable.of_bound (hcm i).aestronglyMeasurable B (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hc ω i)]; exact hcb ω i
  rw [← integral_sub (hint Φ₁) (hint Φ₂), ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hint0.const_mul δ) ((hint Φ₃).const_mul K), ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => norm_nonneg _)
    ((hint0.const_mul δ).add ((hint Φ₃).const_mul K)) (Eventually.of_forall fun ω => ?_))
  simp only [Real.norm_eq_abs]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (hc ω i)]
  calc c ω i * |Φ₁ (Set.projIci 0 (z ω i)) - Φ₂ (Set.projIci 0 (z ω i))|
      ≤ c ω i * (δ + K * Φ₃ (Set.projIci 0 (z ω i))) :=
        mul_le_mul_of_nonneg_left (hbd _) (hc ω i)
    _ = δ * c ω i + K * (c ω i * Φ₃ (Set.projIci 0 (z ω i))) := by ring

end BlockBand.Endpoints
