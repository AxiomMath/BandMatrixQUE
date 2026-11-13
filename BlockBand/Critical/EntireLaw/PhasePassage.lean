module

public import BlockBand.Critical.EntireLaw.Statements
public import BlockBand.Critical.EntireLaw.Measurability

/-!
# The entire law: from collar removal to the phase expectations

* measurability of the finite-width ring source matrices (`measurable_ringSourceMatrix`,
  `measurable_omittedRingSourceMatrix`);
* real diagonals for Hermitian `H` (`ringSourceMatrix_diag_im`, `omittedRingSourceMatrix_diag_im`),
  hence `|phase| ≤ 1` and the Lipschitz bound `norm_closedSourcePhase_sub_le`;
* **`tendsto_phase_sub_of_collarSourceRemoval`**: `CollarSourceRemoval` (convergence in
  probability of the collar contribution) implies that the phase expectations with full and with
  collar-omitted probes have the same limit. No other hypothesis is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Filter Topology Matrix
open BlockBand.Critical.Entire
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.CriticalEntire
open scoped ComplexConjugate ENNReal

variable {p : Parameters}

/-!
## 1. Measurability of the finite-width ring source matrices
-/

/-- The probes are coordinatewise multiples of the Gaussians. -/
theorem ringProbeVector_apply (Q : C(Torus, ℝ)) (g : p.Site → ℂ) (x : p.Site) :
    ringProbeVector p Q g x = (((p.W : ℝ)⁻¹ * Real.sqrt (Q (p.ringProfilePoint x.1)) : ℝ) : ℂ) * g x :=
  rfl

theorem omitCollar_ringProbeVector_apply (Q : C(Torus, ℝ)) (g : p.Site → ℂ) (x : p.Site) :
    omitCollar p (ringProbeVector p Q g) x =
      (if IsCollarBlock p x.1 then 0 else
        (((p.W : ℝ)⁻¹ * Real.sqrt (Q (p.ringProfilePoint x.1)) : ℝ) : ℂ)) * g x := by
  unfold omitCollar
  split_ifs <;> simp [ringProbeVector_apply]

/-- A quadratic form `(H, g) ↦ (c ∘ g_a)^* (H - E)⁻¹ (d ∘ g_c)` with coordinatewise weights is
Borel. -/
theorem measurable_weightedQuadratic (E : ℝ) {J : ℕ} (c d : p.Site → ℂ) (a b : Fin J) :
    Measurable (fun x : p.SiteMatrix × (Fin J → p.Site → ℂ) =>
      star (fun z => c z * x.2 a z) ⬝ᵥ ((x.1 - (E : ℂ) • 1)⁻¹ *ᵥ fun z => d z * x.2 b z)) := by
  have hR : Measurable fun x : p.SiteMatrix × (Fin J → p.Site → ℂ) => (x.1 - (E : ℂ) • 1)⁻¹ :=
    BlockBand.Critical.GlobalSource.measurable_matrix_inv.comp
      (((continuous_id.sub continuous_const).measurable :
        Measurable fun H : p.SiteMatrix => H - (E : ℂ) • 1).comp measurable_fst)
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  refine Finset.measurable_sum _ fun z _ => ?_
  refine Measurable.mul ?_ ?_
  · exact (continuous_star : Continuous (star : ℂ → ℂ)).measurable.comp (measurable_const.mul
      ((measurable_pi_apply z).comp ((measurable_pi_apply a).comp measurable_snd)))
  · refine Finset.measurable_sum _ fun w _ => ?_
    exact ((measurable_pi_apply w).comp ((measurable_pi_apply z).comp hR)).mul
      (measurable_const.mul ((measurable_pi_apply w).comp ((measurable_pi_apply b).comp measurable_snd)))

theorem measurable_ringSourceMatrix (E : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) :
    Measurable (fun x : p.SiteMatrix × (Fin J → p.Site → ℂ) => ringSourceMatrix p E Q x.1 x.2) := by
  refine Measurable.of_eval fun a => Measurable.of_eval fun b => ?_
  exact measurable_weightedQuadratic E _ _ a b

theorem measurable_omittedRingSourceMatrix (E : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) :
    Measurable (fun x : p.SiteMatrix × (Fin J → p.Site → ℂ) =>
      omittedRingSourceMatrix p E Q x.1 x.2) := by
  refine Measurable.of_eval fun a => Measurable.of_eval fun b => ?_
  have h : (fun x : p.SiteMatrix × (Fin J → p.Site → ℂ) => omittedRingSourceMatrix p E Q x.1 x.2 a b) =
      fun x => star (fun z => (if IsCollarBlock p z.1 then 0 else
          (((p.W : ℝ)⁻¹ * Real.sqrt (Q a (p.ringProfilePoint z.1)) : ℝ) : ℂ)) * x.2 a z) ⬝ᵥ
        ((x.1 - (E : ℂ) • 1)⁻¹ *ᵥ fun z => (if IsCollarBlock p z.1 then 0 else
          (((p.W : ℝ)⁻¹ * Real.sqrt (Q b (p.ringProfilePoint z.1)) : ℝ) : ℂ)) * x.2 b z) := by
    funext x
    simp only [omittedRingSourceMatrix]
    congr 2
    · funext z; exact omitCollar_ringProbeVector_apply _ _ _
    · funext z; exact omitCollar_ringProbeVector_apply _ _ _
  rw [h]
  exact measurable_weightedQuadratic E _ _ a b

/-!
## 2. Real diagonals and the Lipschitz phase
-/

/-- For Hermitian `R`, `v^* R v` is real. -/
theorem im_star_dotProduct_mulVec_self {ι : Type*} [Fintype ι] {R : Matrix ι ι ℂ}
    (hR : R.IsHermitian) (v : ι → ℂ) : (star v ⬝ᵥ (R *ᵥ v)).im = 0 := by
  have h : star (star v ⬝ᵥ (R *ᵥ v)) = star v ⬝ᵥ (R *ᵥ v) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hij : star (R j i) = R i j := by
      have := congrFun (congrFun hR i) j
      rw [Matrix.conjTranspose_apply] at this
      exact this
    rw [hij]
    ring
  exact Complex.conj_eq_iff_im.mp h

theorem isHermitian_resolvent {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ) :
    ((H - (E : ℂ) • (1 : p.SiteMatrix))⁻¹).IsHermitian := by
  refine (hH.sub ?_).inv
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp

theorem ringSourceMatrix_diag_im {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ) {J : ℕ}
    (Q : Fin J → C(Torus, ℝ)) (g : Fin J → p.Site → ℂ) (a : Fin J) :
    (ringSourceMatrix p E Q H g a a).im = 0 :=
  im_star_dotProduct_mulVec_self (isHermitian_resolvent hH E) _

theorem omittedRingSourceMatrix_diag_im {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ) {J : ℕ}
    (Q : Fin J → C(Torus, ℝ)) (g : Fin J → p.Site → ℂ) (a : Fin J) :
    (omittedRingSourceMatrix p E Q H g a a).im = 0 :=
  im_star_dotProduct_mulVec_self (isHermitian_resolvent hH E) _

/-- The phase is bounded by one on matrices with real diagonal. -/
theorem norm_closedSourcePhase_le {J : ℕ} (σ : Fin J → ℤˣ) {T : Matrix (Fin J) (Fin J) ℂ}
    (hT : ∀ j, (T j j).im = 0) : ‖closedSourcePhase σ T‖ ≤ 1 := by
  unfold closedSourcePhase
  rw [Complex.norm_exp]
  have : (-(Complex.I * ∑ j, (((σ j : ℤ) : ℂ) * T j j))).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, hT]
  rw [this, Real.exp_zero]

/-- Lipschitz bound of the phase on real diagonals: `|e^{-is} - e^{-is'}| ≤ Σ_j |T_jj - T'_jj|`. -/
theorem norm_closedSourcePhase_sub_le {J : ℕ} (σ : Fin J → ℤˣ) {T T' : Matrix (Fin J) (Fin J) ℂ}
    (hT : ∀ j, (T j j).im = 0) (hT' : ∀ j, (T' j j).im = 0) :
    ‖closedSourcePhase σ T - closedSourcePhase σ T'‖ ≤ ∑ j, ‖T j j - T' j j‖ := by
  set s : ℝ := ∑ j, ((σ j : ℤ) : ℝ) * (T j j).re
  set s' : ℝ := ∑ j, ((σ j : ℤ) : ℝ) * (T' j j).re
  have hs : ∑ j, (((σ j : ℤ) : ℂ) * T j j) = (s : ℂ) := by
    push_cast [s]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    exact Complex.ext (by simp) (by simp [hT j])
  have hs' : ∑ j, (((σ j : ℤ) : ℂ) * T' j j) = (s' : ℂ) := by
    push_cast [s']
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    exact Complex.ext (by simp) (by simp [hT' j])
  unfold closedSourcePhase
  rw [hs, hs']
  have hfac : Complex.exp (-(Complex.I * (s : ℂ))) - Complex.exp (-(Complex.I * (s' : ℂ))) =
      Complex.exp (-(Complex.I * (s' : ℂ))) * (Complex.exp (Complex.I * ((s' - s : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [hfac, norm_mul]
  have h1 : ‖Complex.exp (-(Complex.I * (s' : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [h1, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs]
  have hdiff : s' - s = ∑ j, ((σ j : ℤ) : ℝ) * ((T' j j).re - (T j j).re) := by
    simp only [s, s', ← Finset.sum_sub_distrib, mul_sub]
  rw [hdiff]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  have hσ : |((σ j : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (σ j) with h | h <;> simp [h]
  rw [hσ, one_mul, ← Complex.sub_re]
  calc |(T' j j - T j j).re| ≤ ‖T' j j - T j j‖ := Complex.abs_re_le_norm _
    _ = ‖T j j - T' j j‖ := norm_sub_rev _ _

/-!
## 3. Collar removal at the level of the phase expectations
-/

/-- **From `CollarSourceRemoval` (convergence in probability of the collar contribution) to
the phase expectations.** Along every critical sequence and every choice of realizations,
`E exp{-i Σ σ_j (ζ_j^*Rζ_j)} - E exp{-i Σ σ_j (ζ_{o,j}^*Rζ_{o,j})} → 0` (the phases are
`1`-Lipschitz in the real diagonals and bounded by one). -/
theorem tendsto_phase_sub_of_collarSourceRemoval (hO2 : CollarSourceRemoval) {b E : ℝ}
    (hb : 0 < b) (hb' : b < 1 / 2) (hE : -2 < E ∧ E < 2) (τ : PositiveRatio) {J : ℕ}
    {Q : Fin J → C(Torus, ℝ)} (hQ : ∀ a x, 0 ≤ Q a x) (σ : Fin J → ℤˣ)
    (s : CriticalSequence τ.1) (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)) :
    Tendsto (fun j =>
        (∫ x, closedSourcePhase σ (ringSourceMatrix (s.parameters b hb hb' j) E Q x.1 x.2)
          ∂fullRingProbeLaw (R j).model J) -
        ∫ x, closedSourcePhase σ (omittedRingSourceMatrix (s.parameters b hb hb' j) E Q x.1 x.2)
          ∂fullRingProbeLaw (R j).model J) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / (4 * ((J : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  -- the collar entries are small in probability
  have hsmall : ∀ a : Fin J, Tendsto (fun j => (fullRingProbeLaw (R j).model J
      {x | δ < ‖ringSourceMatrix (s.parameters b hb hb' j) E Q x.1 x.2 a a -
        omittedRingSourceMatrix (s.parameters b hb hb' j) E Q x.1 x.2 a a‖}).toReal) atTop (𝓝 0) :=
    fun a => (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (hO2 b E hb hb' hE τ J Q hQ s R a a δ hδpos) |>.congr fun j => rfl
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin J)) fun a _ => hsmall a
  simp only [Finset.sum_const_zero] at hsum
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hsum (ε / 4) (by positivity)
  refine ⟨N, fun j hj => ?_⟩
  set p := s.parameters b hb hb' j
  set μ := fullRingProbeLaw (R j).model J with hμ
  have : IsProbabilityMeasure μ := by
    simp only [hμ, fullRingProbeLaw]; infer_instance
  set Tf := fun x : p.SiteMatrix × (Fin J → p.Site → ℂ) => ringSourceMatrix p E Q x.1 x.2
  set To := fun x : p.SiteMatrix × (Fin J → p.Site → ℂ) => omittedRingSourceMatrix p E Q x.1 x.2
  have hmf : Measurable fun x => closedSourcePhase σ (Tf x) :=
    (measurable_closedSourcePhase σ).comp (measurable_ringSourceMatrix E Q)
  have hmo : Measurable fun x => closedSourcePhase σ (To x) :=
    (measurable_closedSourcePhase σ).comp (measurable_omittedRingSourceMatrix E Q)
  set S : Set (p.SiteMatrix × (Fin J → p.Site → ℂ)) := ⋃ a, {x | δ < ‖Tf x a a - To x a a‖}
  have hSm : MeasurableSet S := MeasurableSet.iUnion fun a =>
    measurableSet_lt measurable_const
      ((((measurable_pi_apply a).comp ((measurable_pi_apply a).comp
        (measurable_ringSourceMatrix E Q))).sub ((measurable_pi_apply a).comp
        ((measurable_pi_apply a).comp (measurable_omittedRingSourceMatrix E Q)))).norm)
  have hHerm : ∀ᵐ x ∂μ, x.1.IsHermitian := by
    have hmp : MeasurePreserving Prod.fst μ (R j).model.law :=
      measurePreserving_fst
    exact hmp.quasiMeasurePreserving.ae (R j).model.isPhysical.1
  -- pointwise bound
  have hpt : ∀ᵐ x ∂μ, ‖closedSourcePhase σ (Tf x) - closedSourcePhase σ (To x)‖ ≤
      (J : ℝ) * δ + 2 * S.indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [hHerm] with x hx
    have hf := ringSourceMatrix_diag_im hx E Q x.2
    have ho := omittedRingSourceMatrix_diag_im hx E Q x.2
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS]
      have hf1 := norm_closedSourcePhase_le σ hf
      have ho1 := norm_closedSourcePhase_le σ ho
      have h2 : ‖closedSourcePhase σ (Tf x) - closedSourcePhase σ (To x)‖ ≤ 2 :=
        (norm_sub_le _ _).trans (by linarith)
      have : 0 ≤ (J : ℝ) * δ := by positivity
      linarith
    · rw [Set.indicator_of_notMem hxS, mul_zero, add_zero]
      refine (norm_closedSourcePhase_sub_le σ hf ho).trans ?_
      have hle : ∀ a, ‖Tf x a a - To x a a‖ ≤ δ := fun a => by
        by_contra h
        exact hxS (Set.mem_iUnion.mpr ⟨a, not_le.mp h⟩)
      calc ∑ a, ‖Tf x a a - To x a a‖ ≤ ∑ _a : Fin J, δ := Finset.sum_le_sum fun a _ => hle a
        _ = (J : ℝ) * δ := by simp
  have hint1 : Integrable (fun x => closedSourcePhase σ (Tf x)) μ := by
    refine (integrable_const (1 : ℝ)).mono' hmf.aestronglyMeasurable ?_
    filter_upwards [hHerm] with x hx
    exact norm_closedSourcePhase_le σ (ringSourceMatrix_diag_im hx E Q x.2)
  have hint2 : Integrable (fun x => closedSourcePhase σ (To x)) μ := by
    refine (integrable_const (1 : ℝ)).mono' hmo.aestronglyMeasurable ?_
    filter_upwards [hHerm] with x hx
    exact norm_closedSourcePhase_le σ (omittedRingSourceMatrix_diag_im hx E Q x.2)
  have hbound : ‖(∫ x, closedSourcePhase σ (Tf x) ∂μ) - ∫ x, closedSourcePhase σ (To x) ∂μ‖ ≤
      (J : ℝ) * δ + 2 * (μ S).toReal := by
    rw [← integral_sub hint1 hint2]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hrhs : ∫ x, ((J : ℝ) * δ + 2 * S.indicator (fun _ => (1 : ℝ)) x) ∂μ =
        (J : ℝ) * δ + 2 * (μ S).toReal := by
      rw [integral_add (integrable_const _) (((integrable_const (1 : ℝ)).indicator hSm).const_mul 2),
        integral_const, integral_const_mul, integral_indicator_const _ hSm]
      simp [measureReal_def]
    rw [← hrhs]
    exact integral_mono_ae (hint1.sub hint2).norm
      ((integrable_const _).add (((integrable_const (1 : ℝ)).indicator hSm).const_mul 2)) hpt
  have hS : (μ S).toReal ≤ ∑ a, (μ {x | δ < ‖Tf x a a - To x a a‖}).toReal := by
    rw [← ENNReal.toReal_sum (fun a _ => measure_ne_top _ _)]
    exact ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun a _ => measure_ne_top _ _)
      (measure_iUnion_fintype_le _ _)
  have hNj := hN j hj
  rw [Real.dist_eq, sub_zero] at hNj
  have hsum_nonneg : 0 ≤ ∑ a, (μ {x | δ < ‖Tf x a a - To x a a‖}).toReal :=
    Finset.sum_nonneg fun a _ => ENNReal.toReal_nonneg
  rw [abs_of_nonneg hsum_nonneg] at hNj
  rw [dist_eq_norm, sub_zero]
  have hJδ : (J : ℝ) * δ ≤ ε / 4 := by
    rw [hδ, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc _ ≤ (J : ℝ) * δ + 2 * (μ S).toReal := hbound
    _ ≤ ε / 4 + 2 * (ε / 4) := by nlinarith [hS, hNj]
    _ < ε := by linarith

end BlockBand.Critical.EntireLaw
