module

public import BlockBand.Palm.ReferenceFlowParamInt
public import BlockBand.Palm.ReferenceFlowHeat
public import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Static clauses of the reference backward function

For fixed `s`, the backward function `g_s(z) = E f(K_s z + L_s G)` of the reference flow is `C²`
in `z` with the derivative representations through `K_s`, and it is continuous in `s`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.ReferenceFlow

open MeasureTheory Set Filter Matrix
open BlockBand.SourceProcess.FiniteDriverIntegration

variable {N : ℕ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

/-- The product topology on matrices is second countable (as on `Fin N → Fin N → ℂ`). -/
theorem matrix_secondCountable : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))

/-- The product topology on matrices is metrizable (as on `Fin N → Fin N → ℂ`). -/
theorem matrix_pseudoMetrizable :
    TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin N) (Fin N) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin N → Fin N → ℂ))

attribute [local instance] matrix_secondCountable matrix_pseudoMetrizable

theorem lmul_zero' {p : ℕ} (z : RefState N p) : lmul (0 : Matrix (Fin N) (Fin N) ℂ) z = 0 := by
  funext i α
  simp [lmul]

theorem lmul_one' {p : ℕ} (z : RefState N p) : lmul (1 : Matrix (Fin N) (Fin N) ℂ) z = z := by
  funext i α
  simp [lmul, Matrix.one_apply]

theorem continuous_lmul_joint {p : ℕ} :
    Continuous fun q : Matrix (Fin N) (Fin N) ℂ × RefState N p => lmul q.1 q.2 := by
  refine continuous_pi fun i => continuous_pi fun α => ?_
  simp only [lmul]
  exact continuous_finsetSum _ fun j _ => by fun_prop

theorem norm_lmulL_le {p : ℕ} {K : Matrix (Fin N) (Fin N) ℂ} (hK : ∀ i j, ‖K i j‖ ≤ 1) :
    ‖(lmulL K : RefState N p →L[ℝ] RefState N p)‖ ≤ N := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg N) fun z => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun α => ?_
  simp only [lmulL_apply, lmul]
  calc ‖∑ j, K i j * z j α‖ ≤ ∑ j, ‖K i j * z j α‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin N, ‖z‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hK i j)).trans
          ((norm_le_pi_norm (z j) α).trans (norm_le_pi_norm z j))
    _ = N * ‖z‖ := by simp

/-!
## The backward function: static clauses
-/

section Static

variable {p : ℕ}

/-- The joint law of the auxiliary noise and the Gaussian array. -/
abbrev prodLaw (μ : Measure S) (N p : ℕ) : Measure (DriverSample S (RotIdx N) × RefState N p) :=
  (driverLaw (κ := RotIdx N) μ).prod (matCircularLaw N p)

/-- `K ↦ lmulL K` as a linear map. -/
def lmulLinear (N p : ℕ) :
    Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] (RefState N p →L[ℝ] RefState N p) where
  toFun K := lmulL K
  map_add' K K' := by
    ext z i α
    simp [lmul, add_mul, Finset.sum_add_distrib]
  map_smul' t K := by
    ext z i α
    simp [lmul, Finset.mul_sum, mul_assoc]

theorem continuous_lmulL : Continuous fun K : Matrix (Fin N) (Fin N) ℂ =>
    (lmulL K : RefState N p →L[ℝ] RefState N p) :=
  (lmulLinear N p).continuous_of_finiteDimensional

theorem continuous_affine_joint (z : RefState N p) :
    Continuous fun q : (Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) × RefState N p =>
      lmul q.1.1 z + lmul q.1.2 q.2 :=
  (continuous_lmul_joint.comp (continuous_fst.fst.prodMk continuous_const)).add
    (continuous_lmul_joint.comp (continuous_fst.snd.prodMk continuous_snd))

variable {K L : ℝ → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ}

theorem measurable_triple {s : ℝ} (hK : Measurable (K s)) (hL : Measurable (L s)) :
    Measurable fun ω : DriverSample S (RotIdx N) × RefState N p => ((K s ω.1, L s ω.1), ω.2) :=
  ((hK.comp measurable_fst).prodMk (hL.comp measurable_fst)).prodMk measurable_snd

theorem refSemigroup_eq_prod {s : ℝ} (hK : Measurable (K s)) (hL : Measurable (L s)) {C : ℝ}
    {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f) :
    refSemigroup μ K L f s = fun z =>
      ∫ ω, f (lmulL (K s ω.1) z + lmul (L s ω.1) ω.2) ∂prodLaw μ N p := by
  funext z
  have hm : Measurable fun ω : DriverSample S (RotIdx N) × RefState N p =>
      f (lmulL (K s ω.1) z + lmul (L s ω.1) ω.2) :=
    (hf.contDiff.continuous.comp (continuous_affine_joint z)).measurable.comp
      (measurable_triple hK hL)
  have hi : Integrable (fun ω : DriverSample S (RotIdx N) × RefState N p =>
      f (lmulL (K s ω.1) z + lmul (L s ω.1) ω.2)) (prodLaw μ N p) :=
    Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using hf.bound _)
  rw [refSemigroup, integral_prod _ hi]
  rfl

omit [IsProbabilityMeasure μ] in
theorem ae_prod_of_ae {P : DriverSample S (RotIdx N) → Prop}
    (h : ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, P y) :
    ∀ᵐ ω ∂prodLaw μ N p, P ω.1 :=
  Measure.quasiMeasurePreserving_fst.ae h

set_option maxHeartbeats 1000000 in
/-- `C²` in `z` and the derivative representations of the backward function. -/
theorem refSemigroup_static {s : ℝ} (hK : Measurable (K s)) (hL : Measurable (L s))
    (hKb : ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ i j, ‖K s y i j‖ ≤ 1) {C : ℝ}
    {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f) :
    ContDiff ℝ 2 (refSemigroup μ K L f s) ∧
    (∀ z h, fderiv ℝ (refSemigroup μ K L f s) z h =
      ∫ y, ∫ G, fderiv ℝ f (lmul (K s y) z + lmul (L s y) G) (lmul (K s y) h)
        ∂matCircularLaw N p ∂driverLaw (κ := RotIdx N) μ) ∧
    (∀ z h h', D2 (refSemigroup μ K L f s) z h h' =
      ∫ y, ∫ G, D2 f (lmul (K s y) z + lmul (L s y) G) (lmul (K s y) h) (lmul (K s y) h')
        ∂matCircularLaw N p ∂driverLaw (κ := RotIdx N) μ) := by
  have hA : AEStronglyMeasurable (fun ω : DriverSample S (RotIdx N) × RefState N p =>
      (lmulL (K s ω.1) : RefState N p →L[ℝ] RefState N p)) (prodLaw μ N p) :=
    (continuous_lmulL.comp_aestronglyMeasurable (hK.comp measurable_fst).aestronglyMeasurable)
  have hb : AEStronglyMeasurable (fun ω : DriverSample S (RotIdx N) × RefState N p =>
      lmul (L s ω.1) ω.2) (prodLaw μ N p) :=
    continuous_lmul_joint.comp_aestronglyMeasurable
      ((hL.comp measurable_fst).prodMk measurable_snd).aestronglyMeasurable
  have hAM : ∀ᵐ ω ∂prodLaw μ N p, ‖(lmulL (K s ω.1) : RefState N p →L[ℝ] RefState N p)‖ ≤ N := by
    filter_upwards [ae_prod_of_ae (p := p) hKb] with ω hω
    exact norm_lmulL_le hω
  obtain ⟨hcd, hd1, hd2⟩ := integral_affine_contDiff hA hb hAM hf.contDiff
    hf.bound hf.deriv_bound (norm_fderiv_fderiv_le hf)
  have hC : 0 ≤ C := (abs_nonneg _).trans (hf.bound 0)
  have hf1c : Continuous (fderiv ℝ f) := hf.contDiff.continuous_fderiv (by norm_num)
  have hf2c : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.contDiff.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  rw [refSemigroup_eq_prod hK hL hf]
  refine ⟨hcd, fun z h => ?_, fun z h h' => ?_⟩
  · rw [hd1 z h]
    have hm : Measurable fun ω : DriverSample S (RotIdx N) × RefState N p =>
        fderiv ℝ f (lmulL (K s ω.1) z + lmul (L s ω.1) ω.2) (lmulL (K s ω.1) h) := by
      have hc : Continuous fun q : (Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) ×
          RefState N p => fderiv ℝ f (lmul q.1.1 z + lmul q.1.2 q.2) (lmul q.1.1 h) :=
        (hf1c.comp (continuous_affine_joint z)).clm_apply
          (continuous_lmul_joint.comp (continuous_fst.fst.prodMk continuous_const))
      exact hc.measurable.comp (measurable_triple hK hL)
    have hi : Integrable (fun ω : DriverSample S (RotIdx N) × RefState N p =>
        fderiv ℝ f (lmulL (K s ω.1) z + lmul (L s ω.1) ω.2) (lmulL (K s ω.1) h))
        (prodLaw μ N p) := by
      refine Integrable.of_bound hm.aestronglyMeasurable (C * (N * ‖h‖)) ?_
      filter_upwards [hAM] with ω hω
      refine ((fderiv ℝ f _).le_opNorm _).trans ?_
      refine mul_le_mul (hf.deriv_bound _) ?_ (norm_nonneg _) hC
      exact ((lmulL (K s ω.1)).le_opNorm h).trans (mul_le_mul_of_nonneg_right hω (norm_nonneg _))
    rw [integral_prod _ hi]
    rfl
  · rw [D2, hd2 z h h']
    have hm : Measurable fun ω : DriverSample S (RotIdx N) × RefState N p =>
        fderiv ℝ (fderiv ℝ f) (lmulL (K s ω.1) z + lmul (L s ω.1) ω.2) (lmulL (K s ω.1) h)
          (lmulL (K s ω.1) h') := by
      have hc2 : Continuous fun q : (Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) ×
          RefState N p => fderiv ℝ (fderiv ℝ f) (lmul q.1.1 z + lmul q.1.2 q.2) :=
        hf2c.comp (continuous_affine_joint z)
      have hu : ∀ u : RefState N p, Continuous fun q : (Matrix (Fin N) (Fin N) ℂ ×
          Matrix (Fin N) (Fin N) ℂ) × RefState N p => lmul q.1.1 u := fun u =>
        continuous_lmul_joint.comp (continuous_fst.fst.prodMk continuous_const)
      have hc1 : Continuous fun q : (Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) ×
          RefState N p => fderiv ℝ (fderiv ℝ f) (lmul q.1.1 z + lmul q.1.2 q.2) (lmul q.1.1 h) :=
        hc2.clm_apply (hu h)
      have hc : Continuous fun q : (Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) ×
          RefState N p => fderiv ℝ (fderiv ℝ f) (lmul q.1.1 z + lmul q.1.2 q.2) (lmul q.1.1 h)
            (lmul q.1.1 h') :=
        hc1.clm_apply (hu h')
      have hmc := hc.measurable.comp (measurable_triple hK hL)
      simpa only [lmulL_apply, Function.comp_def] using hmc
    have hi : Integrable (fun ω : DriverSample S (RotIdx N) × RefState N p =>
        fderiv ℝ (fderiv ℝ f) (lmulL (K s ω.1) z + lmul (L s ω.1) ω.2) (lmulL (K s ω.1) h)
          (lmulL (K s ω.1) h')) (prodLaw μ N p) := by
      refine Integrable.of_bound hm.aestronglyMeasurable (C * (N * ‖h‖) * (N * ‖h'‖)) ?_
      filter_upwards [hAM] with ω hω
      have hAh : ‖lmulL (K s ω.1) h‖ ≤ N * ‖h‖ :=
        ((lmulL (K s ω.1)).le_opNorm h).trans (mul_le_mul_of_nonneg_right hω (norm_nonneg _))
      have hAh' : ‖lmulL (K s ω.1) h'‖ ≤ N * ‖h'‖ :=
        ((lmulL (K s ω.1)).le_opNorm h').trans (mul_le_mul_of_nonneg_right hω (norm_nonneg _))
      refine ((fderiv ℝ (fderiv ℝ f) _ _).le_opNorm _).trans ?_
      refine mul_le_mul ?_ hAh' (norm_nonneg _) (by positivity)
      refine ((fderiv ℝ (fderiv ℝ f) _).le_opNorm _).trans ?_
      exact mul_le_mul (norm_fderiv_fderiv_le hf _) hAh (norm_nonneg _) hC
    rw [integral_prod _ hi]
    simp only [D2, lmulL_apply]

/-- Continuity of the backward function in `s`. -/
theorem refSemigroup_continuousOn {a c : ℝ} (hK : ∀ s, Measurable (K s))
    (hL : ∀ s, Measurable (L s))
    (hKc : ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ContinuousOn (fun s => K s y) (Icc a c))
    (hLc : ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ContinuousOn (fun s => L s y) (Icc a c)) {C : ℝ}
    {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f) (z : RefState N p) :
    ContinuousOn (fun s => refSemigroup μ K L f s z) (Icc a c) := by
  have he : (fun s => refSemigroup μ K L f s z) = fun s =>
      ∫ ω, f (lmulL (K s ω.1) z + lmul (L s ω.1) ω.2) ∂prodLaw μ N p :=
    funext fun s => congrFun (refSemigroup_eq_prod (hK s) (hL s) hf) z
  rw [he]
  refine continuousOn_of_dominated (bound := fun _ => C) (fun s _ => ?_)
    (fun s _ => Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hf.bound _)
    (integrable_const C) ?_
  · exact ((hf.contDiff.continuous.comp (continuous_affine_joint z)).measurable.comp
      (measurable_triple (hK s) (hL s))).aestronglyMeasurable
  · filter_upwards [ae_prod_of_ae (p := p) hKc, ae_prod_of_ae (p := p) hLc] with ω h1 h2
    exact (hf.contDiff.continuous.comp (continuous_affine_joint z)).comp_continuousOn
      ((h1.prodMk h2).prodMk continuousOn_const)

end Static

end BlockBand.Palm.ReferenceFlow
