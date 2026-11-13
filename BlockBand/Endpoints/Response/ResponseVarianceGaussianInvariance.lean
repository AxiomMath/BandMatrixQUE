module

public import BlockBand.Endpoints.Response.ResponseVarianceDefs
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Unitary invariance of the standard circular Gaussian vector

For every finite `ι` and every unitary `U ∈ U(ι)`, the law `circularVectorLaw ι`
(`h_a = r_{a,0} + i r_{a,1}`, `r ~ Π N(0, 1/2)`) is invariant under `h ↦ U h`. Proof: `U`
induces a real linear isometry of `EuclideanSpace ℝ (ι × Fin 2)`; the standard Gaussian there is
isometry invariant (`ProbabilityTheory.stdGaussian_map`, `map_pi_eq_stdGaussian`), and the
variance-`1/2` product law is its image under the scaling `√(1/2)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix WithLp
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal NNReal ComplexConjugate

variable {ι : Type}

/-- Complexification `r ↦ (r_{a,0} + i r_{a,1})_a` (the map defining `circularVectorLaw`). -/
def rvG_cplx (r : ι × Fin 2 → ℝ) : ι → ℂ := fun a => (r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I

/-- Realification `w ↦ (Re w_a, Im w_a)`. -/
def rvG_real (w : ι → ℂ) : ι × Fin 2 → ℝ := fun p => if p.2 = 0 then (w p.1).re else (w p.1).im

theorem rvG_cplx_real (w : ι → ℂ) : rvG_cplx (rvG_real w) = w := by
  funext a
  simp [rvG_cplx, rvG_real]

theorem rvG_real_cplx (r : ι × Fin 2 → ℝ) : rvG_real (rvG_cplx r) = r := by
  funext p
  obtain ⟨a, j⟩ := p
  fin_cases j <;> simp [rvG_cplx, rvG_real]

theorem rvG_continuous_cplx : Continuous (rvG_cplx (ι := ι)) := by
  unfold rvG_cplx
  fun_prop

theorem rvG_continuous_real : Continuous (rvG_real (ι := ι)) := by
  refine continuous_pi fun p => ?_
  unfold rvG_real
  split_ifs
  · exact Complex.continuous_re.comp (continuous_apply _)
  · exact Complex.continuous_im.comp (continuous_apply _)

theorem rvG_sum_sq_real [Fintype ι] (w : ι → ℂ) :
    ∑ p, rvG_real w p ^ 2 = ∑ a, Complex.normSq (w a) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [rvG_real, Fin.sum_univ_two, Complex.normSq_apply, pow_two]

theorem rvG_sum_normSq_unitary [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (v : ι → ℂ) : ∑ a, Complex.normSq ((U *ᵥ v) a) = ∑ a, Complex.normSq (v a) := by
  have key (w : ι → ℂ) : ((∑ a, Complex.normSq (w a) : ℝ) : ℂ) = star w ⬝ᵥ w := by
    simp [dotProduct, Complex.normSq_eq_conj_mul_self]
  apply Complex.ofReal_injective
  rw [key, key, star_mulVec, dotProduct_mulVec, vecMul_vecMul,
    show Uᴴ * U = 1 from (Matrix.mem_unitaryGroup_iff').1 hU, vecMul_one]

/-- The real rotation induced by `U`. -/
def rvG_rot [Fintype ι] (U : Matrix ι ι ℂ) : (ι × Fin 2 → ℝ) →ₗ[ℝ] (ι × Fin 2 → ℝ) where
  toFun r := rvG_real (U *ᵥ rvG_cplx r)
  map_add' r s := by
    have : rvG_cplx (r + s) = rvG_cplx r + rvG_cplx s := by
      funext a; simp [rvG_cplx]; ring
    rw [this, mulVec_add]
    funext p; simp only [rvG_real, Pi.add_apply]; split_ifs <;> simp
  map_smul' t r := by
    have : rvG_cplx (t • r) = (t : ℂ) • rvG_cplx r := by
      funext a; simp [rvG_cplx]; ring
    rw [this, mulVec_smul]
    funext p; simp only [rvG_real, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> simp

theorem rvG_rot_apply [Fintype ι] (U : Matrix ι ι ℂ) (r : ι × Fin 2 → ℝ) :
    rvG_rot U r = rvG_real (U *ᵥ rvG_cplx r) := rfl

theorem rvG_sum_sq_rot [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (r : ι × Fin 2 → ℝ) : ∑ p, rvG_rot U r p ^ 2 = ∑ p, r p ^ 2 := by
  rw [rvG_rot_apply, rvG_sum_sq_real, rvG_sum_normSq_unitary U hU, ← rvG_sum_sq_real,
    rvG_real_cplx]

/-- The rotation as a linear isometry equivalence of `EuclideanSpace ℝ (ι × Fin 2)`. -/
def rvG_rotIso [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    EuclideanSpace ℝ (ι × Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (ι × Fin 2) :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := (WithLp.linearEquiv 2 ℝ (ι × Fin 2 → ℝ)).symm.toLinearMap ∘ₗ rvG_rot U ∘ₗ
        (WithLp.linearEquiv 2 ℝ (ι × Fin 2 → ℝ)).toLinearMap
      norm_map' := fun x => by
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        congr 1
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          Real.norm_eq_abs, sq_abs]
        exact rvG_sum_sq_rot U hU _ }
    rfl

theorem rvG_rotIso_apply [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (x : EuclideanSpace ℝ (ι × Fin 2)) :
    ofLp (rvG_rotIso U hU x) = rvG_rot U (ofLp x) := rfl

/-- The standard product Gaussian on `ι × Fin 2` is invariant under the rotation. -/
theorem rvG_pi_std_map_rot [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 1).map (rvG_rot U) =
      Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 1 := by
  set P := Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 1
  have hP : P = (stdGaussian (EuclideanSpace ℝ (ι × Fin 2))).map ofLp := by
    rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop),
      show (ofLp ∘ toLp 2 : (ι × Fin 2 → ℝ) → _) = id from rfl, Measure.map_id]
  have hfun : (rvG_rot U : (ι × Fin 2 → ℝ) → (ι × Fin 2 → ℝ)) ∘ ofLp =
      ofLp ∘ rvG_rotIso U hU := by
    funext x; rfl
  have hrot_m : Measurable (rvG_rot U : (ι × Fin 2 → ℝ) → (ι × Fin 2 → ℝ)) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  conv_lhs => rw [hP, Measure.map_map hrot_m (by fun_prop), hfun,
    ← Measure.map_map (by fun_prop) (rvG_rotIso U hU).continuous.measurable,
    stdGaussian_map]
  exact hP.symm

/-- `√(1/2)`-scaling of the standard Gaussian. -/
theorem rvG_gaussianReal_half :
    (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt (1 / 2) * x) = gaussianReal 0 (1 / 2 : ℝ≥0) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp [Real.sq_sqrt]

theorem rvG_pi_half_eq_map [Fintype ι] :
    (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)) =
      (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 1).map
        (fun r p => Real.sqrt (1 / 2) * r p) := by
  rw [Measure.pi_map_pi (fun _ => by fun_prop)]
  simp_rw [rvG_gaussianReal_half]

/-- **Unitary invariance of `circularVectorLaw`.** -/
theorem rvG_circularVectorLaw_map_unitary [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (circularVectorLaw ι).map (fun h => U *ᵥ h) = circularVectorLaw ι := by
  have hlaw : circularVectorLaw ι =
      (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)).map rvG_cplx := rfl
  have hrot_m : Measurable (rvG_rot U : (ι × Fin 2 → ℝ) → (ι × Fin 2 → ℝ)) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hsc_m : Measurable (fun (r : ι × Fin 2 → ℝ) (p : ι × Fin 2) => Real.sqrt (1 / 2) * r p) :=
    by fun_prop
  have hU_m : Measurable (fun h : ι → ℂ => U *ᵥ h) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hcomm : (fun h : ι → ℂ => U *ᵥ h) ∘ rvG_cplx ∘
      (fun (r : ι × Fin 2 → ℝ) (p : ι × Fin 2) => Real.sqrt (1 / 2) * r p) =
      (rvG_cplx ∘ (fun (r : ι × Fin 2 → ℝ) (p : ι × Fin 2) => Real.sqrt (1 / 2) * r p)) ∘
        rvG_rot U := by
    funext r
    simp only [Function.comp_apply]
    have hs (s : ι × Fin 2 → ℝ) : rvG_cplx (fun p => Real.sqrt (1 / 2) * s p) =
        ((Real.sqrt (1 / 2) : ℝ) : ℂ) • rvG_cplx s := by
      funext a; simp [rvG_cplx]; ring
    rw [hs, hs, rvG_rot_apply, rvG_cplx_real, mulVec_smul]
  rw [hlaw, rvG_pi_half_eq_map, Measure.map_map rvG_continuous_cplx.measurable hsc_m,
    Measure.map_map hU_m (rvG_continuous_cplx.measurable.comp hsc_m), hcomm,
    ← Measure.map_map (rvG_continuous_cplx.measurable.comp hsc_m) hrot_m, rvG_pi_std_map_rot U hU]

end BlockBand.Endpoints
