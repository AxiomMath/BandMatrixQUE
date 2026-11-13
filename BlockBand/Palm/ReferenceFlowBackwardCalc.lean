module

public import BlockBand.Palm.ReferenceFlowParamInt

/-!
# Backward equation of the reference flow: general calculus

* `fderiv_fderiv_comp_apply`: the second-order chain rule
  `D²(J ∘ P)(x)[v,w] = D²J(Px)[DP v, DP w] + DJ(Px)[D²P(x)[v,w]]` for `J`, `P` of class `C²`
  at the relevant points.
* `aestronglyMeasurable_clm_of_apply`: a family of continuous linear maps on a
  finite-dimensional space is a.e.-strongly measurable if all its evaluations are.
* `integral_contDiff_two_int`: `C²` of an average with integrable (not necessarily bounded)
  bounds on the first and second derivatives.
* `integral_linear_contDiff`: the case `h ω w = f(A ω w)` with random continuous linear maps
  `A ω`, `‖A ω‖ ≤ M ω`, `M` and `M²` integrable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.ReferenceFlow.Backward

open MeasureTheory Set Filter Topology

section ChainRule

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Second-order chain rule.** -/
theorem fderiv_fderiv_comp_apply {J : F → G} {P : E → F} {x : E}
    (hJ : ContDiffAt ℝ 2 J (P x)) (hP : ContDiffAt ℝ 2 P x) (v w : E) :
    fderiv ℝ (fderiv ℝ (J ∘ P)) x v w =
      fderiv ℝ (fderiv ℝ J) (P x) (fderiv ℝ P x v) (fderiv ℝ P x w) +
        fderiv ℝ J (P x) (fderiv ℝ (fderiv ℝ P) x v w) := by
  have hJ' : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ J (P y) :=
    hP.continuousAt.tendsto.eventually ((hJ.eventually (by simp)).mono fun y hy =>
      hy.differentiableAt (by norm_num))
  have hP' : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ P y :=
    (hP.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have heq : fderiv ℝ (J ∘ P) =ᶠ[𝓝 x] fun y => (fderiv ℝ J (P y)).comp (fderiv ℝ P y) := by
    filter_upwards [hJ', hP'] with y h1 h2
    exact fderiv_comp y h1 h2
  have hd1 : HasFDerivAt (fun y => fderiv ℝ J (P y))
      ((fderiv ℝ (fderiv ℝ J) (P x)).comp (fderiv ℝ P x)) x :=
    (((hJ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt).comp
      x (hP.differentiableAt (by norm_num)).hasFDerivAt
  have hd2 : HasFDerivAt (fderiv ℝ P) (fderiv ℝ (fderiv ℝ P) x) x :=
    ((hP.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  rw [heq.fderiv_eq, (hd1.clm_comp hd2).fderiv]
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  exact add_comm _ _

theorem fderiv_fderiv_clm (L : F →L[ℝ] G) (y : F) : fderiv ℝ (fderiv ℝ L) y = 0 := by
  have : fderiv ℝ L = fun _ => L := funext fun _ => L.fderiv
  rw [this]
  exact fderiv_const_apply L

/-- `D²(L ∘ P) = L ∘ D²P` for a continuous linear `L`. -/
theorem fderiv_fderiv_clm_comp_apply (L : F →L[ℝ] G) {P : E → F} {x : E}
    (hP : ContDiffAt ℝ 2 P x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => L (P y))) x v w = L (fderiv ℝ (fderiv ℝ P) x v w) := by
  have h := fderiv_fderiv_comp_apply (J := L) (P := P) L.contDiff.contDiffAt hP v w
  rw [fderiv_fderiv_clm, L.fderiv] at h
  simpa [Function.comp_def] using h

/-- `D(J ∘ P)(x)[v] = DJ(Px)[DP v]`. -/
theorem fderiv_comp_apply' {J : F → G} {P : E → F} {x : E}
    (hJ : DifferentiableAt ℝ J (P x)) (hP : DifferentiableAt ℝ P x) (v : E) :
    fderiv ℝ (J ∘ P) x v = fderiv ℝ J (P x) (fderiv ℝ P x v) := by
  rw [fderiv_comp x hJ hP]
  rfl

end ChainRule

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A family of continuous linear maps on a finite-dimensional space is a.e.-strongly
measurable if every evaluation is. -/
theorem aestronglyMeasurable_clm_of_apply {F : Ω → E →L[ℝ] Y}
    (h : ∀ u, AEStronglyMeasurable (fun ω => F ω u) P) : AEStronglyMeasurable F P := by
  set b := Module.finBasis ℝ E
  have hF : F = fun ω => ∑ i, ContinuousLinearMap.smulRightL ℝ E Y
      (LinearMap.toContinuousLinearMap (b.coord i)) (F ω (b i)) := by
    funext ω
    ext x
    rw [FunLike.coe_sum, Finset.sum_apply]
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  rw [hF]
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
    (ContinuousLinearMap.continuous _).comp_aestronglyMeasurable (h (b i))

end Measurability

section TwoDerivatives

variable {Ω X : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [IsFiniteMeasure P] in
/-- **`C²` of an average** with integrable bounds on the first and second derivatives. -/
theorem integral_contDiff_two_int {h : Ω → X → ℝ} {B₁ B₂ : Ω → ℝ}
    (hc : ∀ᵐ ω ∂P, ContDiff ℝ 2 (h ω))
    (hb1 : ∀ᵐ ω ∂P, ∀ z, ‖fderiv ℝ (h ω) z‖ ≤ B₁ ω)
    (hb2 : ∀ᵐ ω ∂P, ∀ z, ‖fderiv ℝ (fderiv ℝ (h ω)) z‖ ≤ B₂ ω)
    (hB₁ : Integrable B₁ P) (hB₂ : Integrable B₂ P)
    (hm0 : ∀ z, AEStronglyMeasurable (fun ω => h ω z) P)
    (hi : ∀ z, Integrable (fun ω => h ω z) P)
    (hm1 : ∀ z, AEStronglyMeasurable (fun ω => fderiv ℝ (h ω) z) P)
    (hm2 : ∀ z, AEStronglyMeasurable (fun ω => fderiv ℝ (fderiv ℝ (h ω)) z) P) :
    ContDiff ℝ 2 (fun z => ∫ ω, h ω z ∂P) ∧
      (∀ z, fderiv ℝ (fun z => ∫ ω, h ω z ∂P) z = ∫ ω, fderiv ℝ (h ω) z ∂P) ∧
      (∀ z, fderiv ℝ (fderiv ℝ (fun z => ∫ ω, h ω z ∂P)) z =
        ∫ ω, fderiv ℝ (fderiv ℝ (h ω)) z ∂P) := by
  have hd1 : ∀ᵐ ω ∂P, ∀ z, HasFDerivAt (h ω) (fderiv ℝ (h ω) z) z := by
    filter_upwards [hc] with ω hω z
    exact (hω.differentiable (by norm_num) z).hasFDerivAt
  have hd2 : ∀ᵐ ω ∂P, ∀ z, HasFDerivAt (fderiv ℝ (h ω)) (fderiv ℝ (fderiv ℝ (h ω)) z) z := by
    filter_upwards [hc] with ω hω z
    have h1 : ContDiff ℝ 1 (fderiv ℝ (h ω)) := hω.fderiv_right (by norm_num)
    exact (h1.differentiable (by norm_num) z).hasFDerivAt
  have hi1 : ∀ z, Integrable (fun ω => fderiv ℝ (h ω) z) P := fun z =>
    hB₁.mono' (hm1 z) (by filter_upwards [hb1] with ω hω using hω z)
  have hD1 : ∀ z, HasFDerivAt (fun z => ∫ ω, h ω z ∂P) (∫ ω, fderiv ℝ (h ω) z ∂P) z := fun z =>
    hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := P) (F := fun z ω => h ω z)
      (F' := fun z ω => fderiv ℝ (h ω) z) (x₀ := z) (bound := B₁) (s := univ) Filter.univ_mem
      (Eventually.of_forall fun z => hm0 z) (hi z) (hm1 z)
      (by filter_upwards [hb1] with ω hω x _ using hω x) hB₁
      (by filter_upwards [hd1] with ω hω x _ using hω x)
  have hF1 : fderiv ℝ (fun z => ∫ ω, h ω z ∂P) = fun z => ∫ ω, fderiv ℝ (h ω) z ∂P :=
    funext fun z => (hD1 z).fderiv
  have hD2 : ∀ z, HasFDerivAt (fun z => ∫ ω, fderiv ℝ (h ω) z ∂P)
      (∫ ω, fderiv ℝ (fderiv ℝ (h ω)) z ∂P) z := fun z =>
    hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := P) (F := fun z ω => fderiv ℝ (h ω) z)
      (F' := fun z ω => fderiv ℝ (fderiv ℝ (h ω)) z) (x₀ := z) (bound := B₂) (s := univ)
      Filter.univ_mem (Eventually.of_forall fun z => hm1 z) (hi1 z) (hm2 z)
      (by filter_upwards [hb2] with ω hω x _ using hω x) hB₂
      (by filter_upwards [hd2] with ω hω x _ using hω x)
  have hF2 : fderiv ℝ (fderiv ℝ (fun z => ∫ ω, h ω z ∂P)) =
      fun z => ∫ ω, fderiv ℝ (fderiv ℝ (h ω)) z ∂P := by
    rw [hF1]
    exact funext fun z => (hD2 z).fderiv
  have hcont2 : Continuous fun z => ∫ ω, fderiv ℝ (fderiv ℝ (h ω)) z ∂P := by
    refine continuous_of_dominated (bound := B₂) hm2
      (fun z => by filter_upwards [hb2] with ω hω using hω z) hB₂ ?_
    filter_upwards [hc] with ω hω
    exact (hω.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  refine ⟨?_, fun z => by rw [hF1], fun z => by rw [hF2]⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_fderiv]
  refine ⟨fun z => (hD1 z).differentiableAt, by simp, ?_⟩
  rw [hF1, contDiff_one_iff_fderiv]
  refine ⟨fun z => (hD2 z).differentiableAt, ?_⟩
  have : fderiv ℝ (fun z => ∫ ω, fderiv ℝ (h ω) z ∂P) =
      fun z => ∫ ω, fderiv ℝ (fderiv ℝ (h ω)) z ∂P := funext fun z => (hD2 z).fderiv
  rw [this]
  exact hcont2

/-- **Average of a `C²` test along random linear maps** with integrable bounds. -/
theorem integral_linear_contDiff {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {A : Ω → Y →L[ℝ] X} (hA : AEStronglyMeasurable A P) {M : Ω → ℝ}
    (hAM : ∀ᵐ ω ∂P, ‖A ω‖ ≤ M ω) (hM1 : Integrable M P)
    (hM2 : Integrable (fun ω => M ω * M ω) P) {C : ℝ} {f : X → ℝ} (hf : ContDiff ℝ 2 f)
    (h0 : ∀ z, |f z| ≤ C) (h1 : ∀ z, ‖fderiv ℝ f z‖ ≤ C)
    (h2 : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C) :
    ContDiff ℝ 2 (fun w => ∫ ω, f (A ω w) ∂P) ∧
      (∀ w u, fderiv ℝ (fun w => ∫ ω, f (A ω w) ∂P) w u =
        ∫ ω, fderiv ℝ f (A ω w) (A ω u) ∂P) ∧
      (∀ w u v, fderiv ℝ (fderiv ℝ (fun w => ∫ ω, f (A ω w) ∂P)) w u v =
        ∫ ω, fderiv ℝ (fderiv ℝ f) (A ω w) (A ω u) (A ω v) ∂P) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (h1 0)
  have hfc : Continuous f := hf.continuous
  have hf1c : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hf2c : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hD1 : ∀ ω w, HasFDerivAt (fun w => f (A ω w)) ((fderiv ℝ f (A ω w)).comp (A ω)) w :=
    fun ω w => ((hf.differentiable (by norm_num) _).hasFDerivAt).comp w (A ω).hasFDerivAt
  have hF1 : ∀ ω, fderiv ℝ (fun w => f (A ω w)) = fun w => (fderiv ℝ f (A ω w)).comp (A ω) :=
    fun ω => funext fun w => (hD1 ω w).fderiv
  have hD2 : ∀ ω w, HasFDerivAt (fun w => (fderiv ℝ f (A ω w)).comp (A ω))
      (((ContinuousLinearMap.compL ℝ Y X ℝ).flip (A ω)).comp
        ((fderiv ℝ (fderiv ℝ f) (A ω w)).comp (A ω))) w := by
    intro ω w
    have h1' : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    have hD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (A ω w)) (A ω w) :=
      (h1'.differentiable (by norm_num) _).hasFDerivAt
    exact ((ContinuousLinearMap.compL ℝ Y X ℝ).flip (A ω)).hasFDerivAt.comp w
      (hD.comp w (A ω).hasFDerivAt)
  have hF2 : ∀ ω w, fderiv ℝ (fderiv ℝ (fun w => f (A ω w))) w =
      ((ContinuousLinearMap.compL ℝ Y X ℝ).flip (A ω)).comp
        ((fderiv ℝ (fderiv ℝ f) (A ω w)).comp (A ω)) := fun ω w => by
    rw [hF1 ω, (hD2 ω w).fderiv]
  have hm0 : ∀ w, AEStronglyMeasurable (fun ω => f (A ω w)) P := fun w =>
    (hfc.comp (continuous_id.clm_apply continuous_const)).comp_aestronglyMeasurable hA
  have hm1 : ∀ w, AEStronglyMeasurable (fun ω => fderiv ℝ (fun w => f (A ω w)) w) P := by
    intro w
    simp_rw [hF1]
    exact ((hf1c.comp (continuous_id.clm_apply continuous_const)).clm_comp
      continuous_id).comp_aestronglyMeasurable hA
  have hm2 : ∀ w, AEStronglyMeasurable
      (fun ω => fderiv ℝ (fderiv ℝ (fun w => f (A ω w))) w) P := by
    intro w
    simp_rw [hF2]
    have hpre : Continuous fun B : Y →L[ℝ] X => (ContinuousLinearMap.compL ℝ Y X ℝ).flip B :=
      ((ContinuousLinearMap.compL ℝ Y X ℝ).flip).continuous
    exact (hpre.clm_comp ((hf2c.comp (continuous_id.clm_apply continuous_const)).clm_comp
      continuous_id)).comp_aestronglyMeasurable hA
  have hi : ∀ w, Integrable (fun ω => f (A ω w)) P := fun w =>
    Integrable.of_bound (hm0 w) C (Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using h0 (A ω w))
  have hb1 : ∀ᵐ ω ∂P, ∀ w, ‖fderiv ℝ (fun w => f (A ω w)) w‖ ≤ C * M ω := by
    filter_upwards [hAM] with ω hω w
    rw [hF1]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (h1 _) hω (norm_nonneg _) hC)
  have hb2 : ∀ᵐ ω ∂P, ∀ w, ‖fderiv ℝ (fderiv ℝ (fun w => f (A ω w))) w‖ ≤
      M ω * (C * M ω) := by
    filter_upwards [hAM] with ω hω w
    rw [hF2]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hM0 : 0 ≤ M ω := (norm_nonneg _).trans hω
    refine mul_le_mul ?_ ?_ (norm_nonneg _) hM0
    · refine (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun φ => ?_).trans hω
      simpa [mul_comm] using ContinuousLinearMap.opNorm_comp_le φ (A ω)
    · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (h2 _) hω (norm_nonneg _) hC)
  have hB1 : Integrable (fun ω => C * M ω) P := hM1.const_mul C
  have hB2 : Integrable (fun ω => M ω * (C * M ω)) P :=
    (hM2.const_mul C).congr (Eventually.of_forall fun ω => by ring)
  obtain ⟨hcd, hd1, hd2⟩ := integral_contDiff_two_int (P := P)
    (h := fun ω w => f (A ω w)) (Eventually.of_forall fun ω => hf.comp (A ω).contDiff)
    hb1 hb2 hB1 hB2 hm0 hi hm1 hm2
  have hi1 : ∀ w, Integrable (fun ω => fderiv ℝ (fun w => f (A ω w)) w) P := fun w =>
    hB1.mono' (hm1 w) (by filter_upwards [hb1] with ω hω using hω w)
  have hi2 := fun (w : Y) => Integrable.mono' (β := Y →L[ℝ] Y →L[ℝ] ℝ) hB2 (hm2 w)
    (hb2.mono fun ω hω => hω w)
  refine ⟨hcd, fun w u => ?_, fun w u v => ?_⟩
  · rw [hd1 w, ContinuousLinearMap.integral_apply (hi1 w)]
    simp_rw [hF1]
    rfl
  · rw [hd2 w, ContinuousLinearMap.integral_apply (hi2 w),
      ContinuousLinearMap.integral_apply ((hi2 w).apply_continuousLinearMap u)]
    simp_rw [hF2]
    rfl

end TwoDerivatives

end BlockBand.Palm.ReferenceFlow.Backward
