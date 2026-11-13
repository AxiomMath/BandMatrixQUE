module

public import BlockBand.Palm.ReferenceFlowSpec

/-!
# Differentiating Gaussian and auxiliary averages of `C²` tests

Differentiation under the integral sign for averages of `C²` functions with uniformly bounded
derivatives, in particular for random affine compositions `z ↦ f(A_ω z + b_ω)`.

* `hasFDerivAt_integral_of_bound`: differentiation under the integral with a uniform bound on
  the derivative (finite measure).
* `integral_contDiff_two`: if `h ω` is `C²` with uniformly bounded first and second
  derivatives, then `∫ h ω dP` is `C²`, with `D` and `D²` of the integral the integrals of
  `D h ω` and `D² h ω`.
* `integral_affine_contDiff`: the case `h ω z = f(A_ω z + b_ω)` for a bounded-`C²` test `f` and
  random affine maps with `‖A_ω‖ ≤ M` a.s.: `Dg(z)[u] = E Df(A z + b)[A u]` and
  `D²g(z)[u,v] = E D²f(A z + b)[A u, A v]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.ReferenceFlow

open MeasureTheory Set Filter Topology

section General

variable {Ω X Y : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [CompleteSpace Y]

omit [CompleteSpace Y] in
/-- Differentiation under the integral sign with a uniform derivative bound. -/
theorem hasFDerivAt_integral_of_bound {h : Ω → X → Y} {h' : Ω → X → (X →L[ℝ] Y)} {C : ℝ}
    (hd : ∀ᵐ ω ∂P, ∀ z, HasFDerivAt (h ω) (h' ω z) z)
    (hb : ∀ᵐ ω ∂P, ∀ z, ‖h' ω z‖ ≤ C)
    (hm : ∀ z, AEStronglyMeasurable (fun ω => h ω z) P)
    (hi : ∀ z, Integrable (fun ω => h ω z) P)
    (hm' : ∀ z, AEStronglyMeasurable (fun ω => h' ω z) P) (z : X) :
    HasFDerivAt (fun z => ∫ ω, h ω z ∂P) (∫ ω, h' ω z ∂P) z :=
  hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := P) (F := fun z ω => h ω z)
    (F' := fun z ω => h' ω z) (x₀ := z) (bound := fun _ => C) (s := univ) Filter.univ_mem
    (Eventually.of_forall fun z => hm z) (hi z) (hm' z)
    (by filter_upwards [hb] with ω hω x _ using hω x) (integrable_const C)
    (by filter_upwards [hd] with ω hω x _ using hω x)

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
theorem integrable_of_bound' {g : Ω → Y} (hm : AEStronglyMeasurable g P) {C : ℝ}
    (hb : ∀ᵐ ω ∂P, ‖g ω‖ ≤ C) : Integrable g P :=
  Integrable.of_bound hm C hb

end General

section TwoDerivatives

variable {Ω X : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **`C²` of an average** with uniformly bounded first and second derivatives. -/
theorem integral_contDiff_two {h : Ω → X → ℝ} {C₁ C₂ : ℝ}
    (hc : ∀ᵐ ω ∂P, ContDiff ℝ 2 (h ω))
    (hb1 : ∀ᵐ ω ∂P, ∀ z, ‖fderiv ℝ (h ω) z‖ ≤ C₁)
    (hb2 : ∀ᵐ ω ∂P, ∀ z, ‖fderiv ℝ (fderiv ℝ (h ω)) z‖ ≤ C₂)
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
    integrable_of_bound' (hm1 z) (by filter_upwards [hb1] with ω hω using hω z)
  have hD1 : ∀ z, HasFDerivAt (fun z => ∫ ω, h ω z ∂P) (∫ ω, fderiv ℝ (h ω) z ∂P) z :=
    hasFDerivAt_integral_of_bound hd1 hb1 hm0 hi hm1
  have hF1 : fderiv ℝ (fun z => ∫ ω, h ω z ∂P) = fun z => ∫ ω, fderiv ℝ (h ω) z ∂P :=
    funext fun z => (hD1 z).fderiv
  have hD2 : ∀ z, HasFDerivAt (fun z => ∫ ω, fderiv ℝ (h ω) z ∂P)
      (∫ ω, fderiv ℝ (fderiv ℝ (h ω)) z ∂P) z :=
    hasFDerivAt_integral_of_bound hd2 hb2 hm1 hi1 hm2
  have hF2 : fderiv ℝ (fderiv ℝ (fun z => ∫ ω, h ω z ∂P)) =
      fun z => ∫ ω, fderiv ℝ (fderiv ℝ (h ω)) z ∂P := by
    rw [hF1]
    exact funext fun z => (hD2 z).fderiv
  have hcont2 : Continuous fun z => ∫ ω, fderiv ℝ (fderiv ℝ (h ω)) z ∂P := by
    refine continuous_of_dominated (bound := fun _ => C₂) hm2
      (fun z => by filter_upwards [hb2] with ω hω using hω z) (integrable_const C₂) ?_
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

end TwoDerivatives

section Affine

variable {Ω X : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem hasFDerivAt_comp_affine {f : X → ℝ} (hf : ContDiff ℝ 2 f) (A : X →L[ℝ] X) (b z : X) :
    HasFDerivAt (fun z => f (A z + b)) ((fderiv ℝ f (A z + b)).comp A) z := by
  have hT : HasFDerivAt (fun z => A z + b) A z := (A.hasFDerivAt).add_const b
  exact ((hf.differentiable (by norm_num) _).hasFDerivAt).comp z hT

theorem fderiv_comp_affine {f : X → ℝ} (hf : ContDiff ℝ 2 f) (A : X →L[ℝ] X) (b : X) :
    fderiv ℝ (fun z => f (A z + b)) = fun z => (fderiv ℝ f (A z + b)).comp A :=
  funext fun z => (hasFDerivAt_comp_affine hf A b z).fderiv

/-- Second derivative of `z ↦ f(Az + b)`. -/
theorem hasFDerivAt_fderiv_comp_affine {f : X → ℝ} (hf : ContDiff ℝ 2 f) (A : X →L[ℝ] X)
    (b z : X) :
    HasFDerivAt (fun z => (fderiv ℝ f (A z + b)).comp A)
      (((ContinuousLinearMap.compL ℝ X X ℝ).flip A).comp ((fderiv ℝ (fderiv ℝ f) (A z + b)).comp A))
      z := by
  have hT : HasFDerivAt (fun z => A z + b) A z := (A.hasFDerivAt).add_const b
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (A z + b)) (A z + b) :=
    (h1.differentiable (by norm_num) _).hasFDerivAt
  exact ((ContinuousLinearMap.compL ℝ X X ℝ).flip A).hasFDerivAt.comp z (hD.comp z hT)

theorem fderiv_fderiv_comp_affine_apply {f : X → ℝ} (hf : ContDiff ℝ 2 f) (A : X →L[ℝ] X)
    (b z u v : X) :
    fderiv ℝ (fderiv ℝ (fun z => f (A z + b))) z u v =
      fderiv ℝ (fderiv ℝ f) (A z + b) (A u) (A v) := by
  rw [fderiv_comp_affine hf A b, (hasFDerivAt_fderiv_comp_affine hf A b z).fderiv]
  rfl

theorem contDiff_comp_affine {f : X → ℝ} (hf : ContDiff ℝ 2 f) (A : X →L[ℝ] X) (b : X) :
    ContDiff ℝ 2 (fun z => f (A z + b)) :=
  hf.comp ((A.contDiff).add contDiff_const)

theorem norm_fderiv_comp_affine_le {f : X → ℝ} {C : ℝ}
    (hb : ∀ z, ‖fderiv ℝ f z‖ ≤ C) (A : X →L[ℝ] X) (b z : X) :
    ‖(fderiv ℝ f (A z + b)).comp A‖ ≤ C * ‖A‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))

theorem norm_fderiv_fderiv_comp_affine_le {f : X → ℝ} (hf : ContDiff ℝ 2 f) {C : ℝ}
    (hb : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C) (A : X →L[ℝ] X) (b z : X) :
    ‖fderiv ℝ (fderiv ℝ (fun z => f (A z + b))) z‖ ≤ ‖A‖ * (C * ‖A‖) := by
  rw [fderiv_comp_affine hf A b, (hasFDerivAt_fderiv_comp_affine hf A b z).fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _)
  · refine (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun φ => ?_)
    simpa [mul_comm] using ContinuousLinearMap.opNorm_comp_le φ A
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))

/-- The second-derivative integrand as a continuous function of `(A, b)`. -/
theorem continuous_secondDerivIntegrand {f : X → ℝ} (hf : ContDiff ℝ 2 f) (z : X) :
    Continuous fun q : (X →L[ℝ] X) × X =>
      ((ContinuousLinearMap.compL ℝ X X ℝ).flip q.1).comp
        ((fderiv ℝ (fderiv ℝ f) (q.1 z + q.2)).comp q.1) := by
  have hf2c : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hpre : Continuous fun q : (X →L[ℝ] X) × X => (ContinuousLinearMap.compL ℝ X X ℝ).flip q.1 :=
    ((ContinuousLinearMap.compL ℝ X X ℝ).flip).continuous.comp continuous_fst
  have hin : Continuous fun q : (X →L[ℝ] X) × X =>
      (fderiv ℝ (fderiv ℝ f) (q.1 z + q.2)).comp q.1 :=
    (hf2c.comp ((continuous_fst.clm_apply continuous_const).add continuous_snd)).clm_comp
      continuous_fst
  exact hpre.clm_comp hin

/-- **Average of a `C²` test along random affine maps.** -/
theorem integral_affine_contDiff {A : Ω → X →L[ℝ] X} {b : Ω → X}
    (hA : AEStronglyMeasurable A P) (hbm : AEStronglyMeasurable b P) {M : ℝ}
    (hAM : ∀ᵐ ω ∂P, ‖A ω‖ ≤ M) {C : ℝ} {f : X → ℝ} (hf : ContDiff ℝ 2 f)
    (h0 : ∀ z, |f z| ≤ C) (h1 : ∀ z, ‖fderiv ℝ f z‖ ≤ C)
    (h2 : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C) :
    ContDiff ℝ 2 (fun z => ∫ ω, f (A ω z + b ω) ∂P) ∧
      (∀ z u, fderiv ℝ (fun z => ∫ ω, f (A ω z + b ω) ∂P) z u =
        ∫ ω, fderiv ℝ f (A ω z + b ω) (A ω u) ∂P) ∧
      (∀ z u v, fderiv ℝ (fderiv ℝ (fun z => ∫ ω, f (A ω z + b ω) ∂P)) z u v =
        ∫ ω, fderiv ℝ (fderiv ℝ f) (A ω z + b ω) (A ω u) (A ω v) ∂P) := by
  have hfc : Continuous f := hf.continuous
  have hf1c : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hAb : AEStronglyMeasurable (fun ω => (A ω, b ω)) P := hA.prodMk hbm
  -- measurability of the three integrands
  have hm0 : ∀ z, AEStronglyMeasurable (fun ω => f (A ω z + b ω)) P := fun z =>
    (hfc.comp ((continuous_fst.clm_apply continuous_const).add continuous_snd)).comp_aestronglyMeasurable hAb
  have hm1 : ∀ z, AEStronglyMeasurable (fun ω => fderiv ℝ (fun z => f (A ω z + b ω)) z) P := by
    intro z
    simp_rw [fderiv_comp_affine hf]
    exact ((hf1c.comp ((continuous_fst.clm_apply continuous_const).add continuous_snd)).clm_comp
      continuous_fst).comp_aestronglyMeasurable hAb
  have hm2 : ∀ z, AEStronglyMeasurable
      (fun ω => fderiv ℝ (fderiv ℝ (fun z => f (A ω z + b ω))) z) P := by
    intro z
    have he : ∀ ω, fderiv ℝ (fderiv ℝ (fun z => f (A ω z + b ω))) z =
        ((ContinuousLinearMap.compL ℝ X X ℝ).flip (A ω)).comp
          ((fderiv ℝ (fderiv ℝ f) (A ω z + b ω)).comp (A ω)) := fun ω => by
      rw [fderiv_comp_affine hf, (hasFDerivAt_fderiv_comp_affine hf (A ω) (b ω) z).fderiv]
    have hcm := (continuous_secondDerivIntegrand hf z).comp_aestronglyMeasurable hAb
    exact hcm.congr (Eventually.of_forall fun ω => (he ω).symm)
  have hi : ∀ z, Integrable (fun ω => f (A ω z + b ω)) P := fun z =>
    integrable_of_bound' (hm0 z) (Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using h0 (A ω z + b ω))
  have hb1 : ∀ᵐ ω ∂P, ∀ z, ‖fderiv ℝ (fun z => f (A ω z + b ω)) z‖ ≤ C * M := by
    filter_upwards [hAM] with ω hω z
    rw [fderiv_comp_affine hf]
    exact (norm_fderiv_comp_affine_le h1 (A ω) (b ω) z).trans
      (mul_le_mul_of_nonneg_left hω ((norm_nonneg _).trans (h1 0)))
  have hb2 : ∀ᵐ ω ∂P, ∀ z, ‖fderiv ℝ (fderiv ℝ (fun z => f (A ω z + b ω))) z‖ ≤ M * (C * M) := by
    filter_upwards [hAM] with ω hω z
    have hC : 0 ≤ C := (norm_nonneg _).trans (h1 0)
    refine (norm_fderiv_fderiv_comp_affine_le hf h2 (A ω) (b ω) z).trans ?_
    exact mul_le_mul hω (mul_le_mul_of_nonneg_left hω hC)
      (mul_nonneg hC (norm_nonneg _)) ((norm_nonneg _).trans hω)
  obtain ⟨hcd, hd1, hd2⟩ := integral_contDiff_two (P := P)
    (h := fun ω z => f (A ω z + b ω)) (Eventually.of_forall fun ω => contDiff_comp_affine hf _ _)
    hb1 hb2 hm0 hi hm1 hm2
  refine ⟨hcd, fun z u => ?_, fun z u v => ?_⟩
  · rw [hd1 z, ContinuousLinearMap.integral_apply]
    · simp_rw [fderiv_comp_affine hf]
      rfl
    · exact integrable_of_bound' (hm1 z) (by filter_upwards [hb1] with ω hω using hω z)
  · rw [hd2 z, ContinuousLinearMap.integral_apply, ContinuousLinearMap.integral_apply]
    · simp_rw [fderiv_fderiv_comp_affine_apply hf]
    · exact (integrable_of_bound' (hm2 z) (by filter_upwards [hb2] with ω hω using hω z)).apply_continuousLinearMap u
    · exact integrable_of_bound' (hm2 z) (by filter_upwards [hb2] with ω hω using hω z)

end Affine

end BlockBand.Palm.ReferenceFlow
