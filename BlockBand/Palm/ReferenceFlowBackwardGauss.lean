module

public import BlockBand.Palm.ReferenceFlowBackwardCalc
public import BlockBand.Palm.ReferenceFlowHeat

/-!
# Backward equation of the reference flow: the Gaussian average in `(m, S)`

For a bounded-`C²` test `f` on `RefState N p` put
`gaussMean f (m, S) = E f(m + S G)`, `G ~ matCircularLaw N p`, a function of the mean
`m ∈ RefState N p` and the matrix `S` (Frobenius norm). Since `(m, S) ↦ m + S G` is linear with
norm `≤ 1 + c ‖G‖` and `G` has finite second moments (`integrable_norm_sq_matCircularLaw`),
`gaussMean f` is globally `C²` with
`D gaussMean(w)[u] = E Df(m + S G)[u.1 + u.2 G]` and
`D² gaussMean(w)[u,v] = E D²f(m + S G)[u.1 + u.2 G, v.1 + v.2 G]` (`gaussMean_derivs`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.ReferenceFlow.Backward

open MeasureTheory Set Filter Matrix BlockBand.Palm.ReferenceFlow
open BlockBand.Internal.Contracts.Inputs

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- The Frobenius uniform structure, preferred over the product instance (they are equal) so
that continuous linear maps out of matrices carry the operator norm. -/
local instance (priority := high) frobUnifG {n : Type*} [Fintype n] :
    UniformSpace (Matrix n n ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := n) (n := n) (α := ℂ)).toUniformSpace

local instance (priority := high) frobTopG {n : Type*} [Fintype n] :
    TopologicalSpace (Matrix n n ℂ) :=
  (frobUnifG (n := n)).toTopologicalSpace

variable {N p : ℕ}

/-!
## Second moments of the circular array
-/

theorem sq_norm_le_sum_sq {ι : Type*} [Fintype ι] (r : ι → ℝ) : ‖r‖ ^ 2 ≤ ∑ k, r k ^ 2 := by
  have h : ‖r‖ ≤ Real.sqrt (∑ k, r k ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun k => ?_
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun k => r k ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ k))
  calc ‖r‖ ^ 2 ≤ Real.sqrt (∑ k, r k ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ k, r k ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem coord_sq_integrable_circGauss (k : CircIdx N p) :
    Integrable (fun r : CircIdx N p → ℝ => r k ^ 2) (circGauss N p) := by
  unfold circGauss gaussianProduct
  have hmp := measurePreserving_eval
    (fun _ : CircIdx N p => ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)) k
  have hid : Integrable (fun x : ℝ => x ^ 2) (ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)) :=
    (ProbabilityTheory.memLp_id_gaussianReal 2).integrable_sq
  exact (hmp.integrable_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 2) _)).mpr hid

theorem integrable_norm_sq_matCircularLaw :
    Integrable (fun G : RefState N p => ‖G‖ ^ 2) (matCircularLaw N p) := by
  rw [integrable_matCircularLaw_iff (by fun_prop)]
  have hsum : Integrable (fun r : CircIdx N p → ℝ =>
      ‖circSample N p‖ ^ 2 * ∑ k, r k ^ 2) (circGauss N p) :=
    (integrable_finsetSum _ fun k _ => coord_sq_integrable_circGauss k).const_mul _
  refine hsum.mono' (by fun_prop) (Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖circSample N p r‖ ^ 2 ≤ (‖circSample N p‖ * ‖r‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) ((circSample N p).le_opNorm r) 2
    _ = ‖circSample N p‖ ^ 2 * ‖r‖ ^ 2 := by ring
    _ ≤ ‖circSample N p‖ ^ 2 * ∑ k, r k ^ 2 :=
        mul_le_mul_of_nonneg_left (sq_norm_le_sum_sq r) (by positivity)

theorem integrable_norm_matCircularLaw :
    Integrable (fun G : RefState N p => ‖G‖) (matCircularLaw N p) := by
  refine ((integrable_const (1 : ℝ)).add integrable_norm_sq_matCircularLaw).mono'
    (by fun_prop) (Eventually.of_forall fun G => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖G‖ - 1), norm_nonneg G]

/-!
## The linear sample map `(m, S) ↦ m + S G`
-/

/-- `S ↦ lmul S G` as a real-linear map. -/
def lmulRightLin (G : RefState N p) : Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] RefState N p where
  toFun S := lmul S G
  map_add' S S' := by
    funext i α
    simp only [lmul, Matrix.add_apply, add_mul, Finset.sum_add_distrib, Pi.add_apply]
  map_smul' t S := by
    funext i α
    simp only [lmul, Matrix.smul_apply, Pi.smul_apply, Complex.real_smul, RingHom.id_apply,
      Finset.mul_sum, mul_assoc]

/-- `G ↦ (S ↦ lmul S G)` as a continuous bilinear map. -/
def lmulRightCLM (N p : ℕ) :
    RefState N p →L[ℝ] (Matrix (Fin N) (Fin N) ℂ →L[ℝ] RefState N p) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun G => LinearMap.toContinuousLinearMap (lmulRightLin G)
      map_add' := fun G G' => by
        ext S : 1
        exact (lmulL S).map_add G G'
      map_smul' := fun t G => by
        ext S : 1
        exact (lmulL S).map_smul t G }

@[simp] theorem lmulRightCLM_apply (G : RefState N p) (S : Matrix (Fin N) (Fin N) ℂ) :
    lmulRightCLM N p G S = lmul S G := rfl

/-- The sample map `(m, S) ↦ m + S G`. -/
def affG (G : RefState N p) : RefState N p × Matrix (Fin N) (Fin N) ℂ →L[ℝ] RefState N p :=
  ContinuousLinearMap.fst ℝ _ _ + (lmulRightCLM N p G).comp (ContinuousLinearMap.snd ℝ _ _)

@[simp] theorem affG_apply (G : RefState N p) (w : RefState N p × Matrix (Fin N) (Fin N) ℂ) :
    affG G w = w.1 + lmul w.2 G := rfl

theorem continuous_affG : Continuous (affG (N := N) (p := p)) :=
  continuous_const.add ((lmulRightCLM N p).continuous.clm_comp continuous_const)

theorem norm_affG_le (G : RefState N p) : ‖affG G‖ ≤ 1 + ‖lmulRightCLM N p‖ * ‖G‖ := by
  refine (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.norm_fst_le _ _ _) ?_)
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc ‖lmulRightCLM N p G‖ * ‖ContinuousLinearMap.snd ℝ (RefState N p)
        (Matrix (Fin N) (Fin N) ℂ)‖ ≤ ‖lmulRightCLM N p G‖ * 1 :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le _ _ _) (norm_nonneg _)
    _ ≤ ‖lmulRightCLM N p‖ * ‖G‖ := by rw [mul_one]; exact (lmulRightCLM N p).le_opNorm G

/-!
## The Gaussian mean `gaussMean f (m, S) = E f(m + S G)`
-/

/-- `gaussMean f (m, S) = E f(m + S G)`. -/
def gaussMean (f : RefState N p → ℝ) (w : RefState N p × Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∫ G, f (w.1 + lmul w.2 G) ∂matCircularLaw N p

/-- **`gaussMean f` is `C²`** with the derivative representations. -/
theorem gaussMean_derivs {C : ℝ} {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f) :
    ContDiff ℝ 2 (gaussMean f) ∧
      (∀ w u, fderiv ℝ (gaussMean f) w u =
        ∫ G, fderiv ℝ f (w.1 + lmul w.2 G) (u.1 + lmul u.2 G) ∂matCircularLaw N p) ∧
      (∀ w u v, fderiv ℝ (fderiv ℝ (gaussMean f)) w u v =
        ∫ G, fderiv ℝ (fderiv ℝ f) (w.1 + lmul w.2 G) (u.1 + lmul u.2 G) (v.1 + lmul v.2 G)
          ∂matCircularLaw N p) := by
  set c := ‖lmulRightCLM N p‖
  have hM1 : Integrable (fun G : RefState N p => 1 + c * ‖G‖) (matCircularLaw N p) :=
    (integrable_const _).add (integrable_norm_matCircularLaw.const_mul c)
  have hM2 : Integrable (fun G : RefState N p => (1 + c * ‖G‖) * (1 + c * ‖G‖))
      (matCircularLaw N p) := by
    have h := ((integrable_const (1 : ℝ)).add
      ((integrable_norm_matCircularLaw (N := N) (p := p)).const_mul (2 * c))).add
      ((integrable_norm_sq_matCircularLaw (N := N) (p := p)).const_mul (c ^ 2))
    refine h.congr (Eventually.of_forall fun G => ?_)
    simp only [Pi.add_apply]
    ring
  have h := integral_linear_contDiff (P := matCircularLaw N p) (A := affG)
    continuous_affG.aestronglyMeasurable (M := fun G => 1 + c * ‖G‖)
    (Eventually.of_forall norm_affG_le) hM1 hM2 hf.contDiff hf.bound hf.deriv_bound
    (norm_fderiv_fderiv_le hf)
  exact h

theorem abs_gaussMean_le {C : ℝ} {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f)
    (w : RefState N p × Matrix (Fin N) (Fin N) ℂ) : |gaussMean f w| ≤ C := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := C) (Eventually.of_forall fun G => ?_)).trans ?_
  · rw [Real.norm_eq_abs]; exact hf.bound _
  · simp

end BlockBand.Palm.ReferenceFlow.Backward
