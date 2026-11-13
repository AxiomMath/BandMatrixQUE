module

public import BlockBand.SourceProcess.ComplexSourceLaw.Measurability
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Moments.Variance

/-!
# Second moments of the standard circular Gaussian vector

The standard circular Gaussian vector on `ℂ^ι` is the image of the real coordinate law
`Π N(0, 1/2)`, and its coordinates satisfy `E[conj(g_a) g_b] = δ_ab` (`integral_conj_mul`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm
open scoped NNReal ComplexConjugate

variable {ι : Type*} [Fintype ι]

/-- The real coordinate law `Π N(0, 1/2)`. -/
def realCoordLaw (ι : Type*) [Fintype ι] : Measure (ι × Fin 2 → ℝ) :=
  Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (realCoordLaw ι) := by
  unfold realCoordLaw; infer_instance

theorem memLp_coord (c : ι × Fin 2) :
    MemLp (fun r : ι × Fin 2 → ℝ => r c) 2 (realCoordLaw ι) :=
  (memLp_id_gaussianReal 2).comp_measurePreserving (measurePreserving_eval _ c)

theorem integrable_coord_mul (c d : ι × Fin 2) :
    Integrable (fun r : ι × Fin 2 → ℝ => r c * r d) (realCoordLaw ι) :=
  (memLp_coord c).integrable_mul (memLp_coord d)

theorem integral_coord_mul [DecidableEq ι] (c d : ι × Fin 2) :
    ∫ r, r c * r d ∂realCoordLaw ι = if c = d then 1 / 2 else 0 := by
  have hmean : ∀ e : ι × Fin 2, ∫ r, r e ∂realCoordLaw ι = 0 := fun e => by
    have hm := integral_map (μ := realCoordLaw ι) (measurable_pi_apply e).aemeasurable
      (f := fun y : ℝ => y) (by fun_prop)
    rw [realCoordLaw, (measurePreserving_eval _ e).map_eq] at hm
    rw [realCoordLaw, ← hm]
    exact integral_id_gaussianReal
  split_ifs with hcd
  · subst hcd
    have hm := integral_map (μ := realCoordLaw ι) (measurable_pi_apply c).aemeasurable
      (f := fun y : ℝ => y * y) (by fun_prop)
    rw [realCoordLaw, (measurePreserving_eval _ c).map_eq] at hm
    rw [realCoordLaw, ← hm]
    have hv := variance_of_integral_eq_zero (μ := gaussianReal 0 (1 / 2 : ℝ≥0)) aemeasurable_id
      integral_id_gaussianReal
    rw [variance_id_gaussianReal] at hv
    simp only [id, sq] at hv
    rw [← hv]
    norm_num
  · have hind : iIndepFun (fun k (r : ι × Fin 2 → ℝ) => r k) (realCoordLaw ι) :=
      iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
    rw [(hind.indepFun hcd).integral_fun_mul_eq_mul_integral
      (measurable_pi_apply c).aestronglyMeasurable (measurable_pi_apply d).aestronglyMeasurable]
    simp [hmean]

/-- The complex coordinates of the real sample. -/
def circMap (ι : Type*) (r : ι × Fin 2 → ℝ) : ι → ℂ :=
  fun a => (r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I

theorem circularVectorLaw_eq : circularVectorLaw ι = (realCoordLaw ι).map (circMap ι) := rfl

theorem measurable_circMap : Measurable (circMap ι) := measurable_circularMap ι

omit [Fintype ι] in
theorem conj_circMap_mul (r : ι × Fin 2 → ℝ) (a b : ι) :
    conj (circMap ι r a) * circMap ι r b =
      ((r (a, 0) * r (b, 0) + r (a, 1) * r (b, 1) : ℝ) : ℂ) +
        ((r (a, 0) * r (b, 1) - r (a, 1) * r (b, 0) : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [circMap]
  · simp [circMap]; ring

theorem integrable_conj_mul_real (a b : ι) :
    Integrable (fun r => conj (circMap ι r a) * circMap ι r b) (realCoordLaw ι) := by
  simp_rw [conj_circMap_mul]
  refine Integrable.add ?_ (Integrable.mul_const ?_ _)
  · exact (((integrable_coord_mul _ _).add (integrable_coord_mul _ _))).ofReal
  · exact (((integrable_coord_mul _ _).sub (integrable_coord_mul _ _))).ofReal

omit [Fintype ι] in
theorem measurable_conj_mul (a b : ι) : Measurable fun g : ι → ℂ => conj (g a) * g b :=
  (Complex.continuous_conj.measurable.comp (measurable_pi_apply a)).mul (measurable_pi_apply b)

theorem integrable_conj_mul (a b : ι) :
    Integrable (fun g : ι → ℂ => conj (g a) * g b) (circularVectorLaw ι) := by
  rw [circularVectorLaw_eq, integrable_map_measure (measurable_conj_mul a b).aestronglyMeasurable
    measurable_circMap.aemeasurable]
  exact integrable_conj_mul_real a b

/-- **`E[conj(g_a) g_b] = δ_ab`.** -/
theorem integral_conj_mul [DecidableEq ι] (a b : ι) :
    ∫ g, conj (g a) * g b ∂circularVectorLaw ι = if a = b then 1 else 0 := by
  rw [circularVectorLaw_eq, integral_map measurable_circMap.aemeasurable
    (measurable_conj_mul a b).aestronglyMeasurable]
  simp_rw [conj_circMap_mul]
  rw [integral_add (((integrable_coord_mul _ _).add (integrable_coord_mul _ _))).ofReal
      ((((integrable_coord_mul _ _).sub (integrable_coord_mul _ _))).ofReal.mul_const _),
    integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
    integral_add (integrable_coord_mul _ _) (integrable_coord_mul _ _),
    integral_sub (integrable_coord_mul _ _) (integrable_coord_mul _ _)]
  simp only [integral_coord_mul, Prod.mk.injEq, and_true, and_false, ite_false,
    show (0 : Fin 2) ≠ 1 from by decide, show (1 : Fin 2) ≠ 0 from by decide, sub_self]
  split_ifs <;> norm_num

end BlockBand.SourceProcess.ComplexSourceLaw
