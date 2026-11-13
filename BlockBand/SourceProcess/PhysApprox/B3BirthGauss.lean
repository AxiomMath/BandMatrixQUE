module

public import BlockBand.Counting.ComplexGaussianWick
public import BlockBand.SourceProcess.Sampling.Mix
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Gaussian concentration of a circular quadratic form

For the standard circular vector `g ~ CoareaPalm.circularVectorLaw ι` (`E gg* = I`) and a
deterministic complex matrix `A` (no Hermiticity), with `Q_A(g) = Σ A_ab conj(g_a) g_b`
(`Counting.complexQuadraticForm`):
* `coarea_circularVectorLaw_eq`: the law is the image of the product law
  `Counting.circularVectorLaw` under `Counting.circularVector`, so its Wick identities transfer;
* `integral_quad_mul`: `E Q_A Q_B = Tr A Tr B + Tr AB`;
* **`integral_norm_sq_quad_sub`**: `E|Q_A − Tr A|² = Re Tr AAᴴ` (`= ‖A‖²_HS`);
* **`lintegral_quad_sub_le`**: `E|Q_A − Tr A| ≤ (Re Tr AAᴴ)^{1/2}`.
With `A` a `W × W` block and the normalization `W⁻¹`, the error is `W⁻¹‖A‖_HS ≤ W^{-1/2}‖A‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Birth

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open scoped NNReal ENNReal ComplexConjugate

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem measurable_circularVector : Measurable (Counting.circularVector (ι := ι)) := by
  refine measurable_pi_iff.mpr fun i => ?_
  show Measurable fun c : ι → ℝ × ℝ => ((c i).1 : ℂ) + Complex.I * ((c i).2 : ℂ)
  exact (Complex.measurable_ofReal.comp (measurable_fst.comp (measurable_pi_apply i))).add
    (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_snd.comp
      (measurable_pi_apply i))))

/-- The circular law of `CoareaPalm` is the product law `Counting.circularVectorLaw` pushed by
`circularVector`. -/
theorem coarea_circularVectorLaw_eq (ι : Type*) [Fintype ι] :
    circularVectorLaw ι =
      (Counting.circularVectorLaw ι).map Counting.circularVector := by
  have h1 : (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)).map
      (MeasurableEquiv.curry ι (Fin 2) ℝ) =
        Measure.pi fun _ : ι => Measure.pi fun _ : Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0) := by
    have e := Measure.infinitePi_map_curry (fun (_ : ι) (_ : Fin 2) => gaussianReal 0 (1 / 2 : ℝ≥0))
    simpa only [Measure.infinitePi_eq_pi] using e
  have h2 : (Measure.pi fun _ : ι => Measure.pi fun _ : Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)).map
      (fun g a => MeasurableEquiv.finTwoArrow (g a)) = Counting.circularVectorLaw ι :=
    (measurePreserving_pi _ _ fun _ => measurePreserving_finTwoArrow _).map_eq
  have hm1 : Measurable (MeasurableEquiv.curry ι (Fin 2) ℝ) := MeasurableEquiv.measurable _
  have hm2 : Measurable fun (g : ι → Fin 2 → ℝ) a => MeasurableEquiv.finTwoArrow (g a) :=
    (measurePreserving_pi (fun _ : ι => Measure.pi fun _ : Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0))
      _ fun _ => measurePreserving_finTwoArrow _).measurable
  have hm3 : Measurable (Counting.circularVector (ι := ι)) := measurable_circularVector
  rw [circularVectorLaw, ← h2, ← h1, Measure.map_map hm2 hm1, Measure.map_map hm3 (hm2.comp hm1)]
  congr 1
  funext r a
  simp [Counting.circularVector, Counting.circularGaussianCoordinate, MeasurableEquiv.curry,
    MeasurableEquiv.finTwoArrow, MeasurableEquiv.piFinTwo, mul_comm]

theorem measurable_quad (A : Matrix ι ι ℂ) :
    Measurable fun g : ι → ℂ => Counting.complexQuadraticForm A g := by
  unfold Counting.complexQuadraticForm
  exact (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_const.mul ((Complex.continuous_conj.comp (continuous_apply i)).mul
      (continuous_apply j))).measurable

variable [DecidableEq ι]

theorem integrable_quad' (A : Matrix ι ι ℂ) :
    Integrable (fun g => Counting.complexQuadraticForm A g) (circularVectorLaw ι) := by
  rw [coarea_circularVectorLaw_eq,
    integrable_map_measure (measurable_quad A).aestronglyMeasurable
      measurable_circularVector.aemeasurable]
  exact Counting.integrable_actualComplexQuadratic A

theorem integrable_quad_mul (A B : Matrix ι ι ℂ) :
    Integrable (fun g => Counting.complexQuadraticForm A g * Counting.complexQuadraticForm B g)
      (circularVectorLaw ι) := by
  rw [coarea_circularVectorLaw_eq,
    integrable_map_measure (show Measurable fun g => Counting.complexQuadraticForm A g *
      Counting.complexQuadraticForm B g from
        (measurable_quad A).mul (measurable_quad B)).aestronglyMeasurable
      measurable_circularVector.aemeasurable]
  exact Counting.integrable_actualComplexQuadratic_mul A B

/-- `E Q_A = Tr A`. -/
theorem integral_quad' (A : Matrix ι ι ℂ) :
    ∫ g, Counting.complexQuadraticForm A g ∂circularVectorLaw ι = A.trace := by
  rw [coarea_circularVectorLaw_eq, integral_map
    measurable_circularVector.aemeasurable
    (measurable_quad A).aestronglyMeasurable]
  exact Counting.integral_actualComplexQuadratic_eq_trace A

/-- **The circular Wick identity** `E Q_A Q_B = Tr A Tr B + Tr AB`. -/
theorem integral_quad_mul (A B : Matrix ι ι ℂ) :
    ∫ g, Counting.complexQuadraticForm A g * Counting.complexQuadraticForm B g
        ∂circularVectorLaw ι = A.trace * B.trace + (A * B).trace := by
  rw [coarea_circularVectorLaw_eq, integral_map
    measurable_circularVector.aemeasurable
    (show Measurable fun g => Counting.complexQuadraticForm A g *
      Counting.complexQuadraticForm B g from
        (measurable_quad A).mul (measurable_quad B)).aestronglyMeasurable]
  exact Counting.integral_actualComplexQuadratic_mul_eq_trace A B

omit [DecidableEq ι] in
/-- `conj Q_A = Q_{Aᴴ}`. -/
theorem conj_quad (A : Matrix ι ι ℂ) (g : ι → ℂ) :
    conj (Counting.complexQuadraticForm A g) = Counting.complexQuadraticForm Aᴴ g := by
  simp only [Counting.complexQuadraticForm, map_sum, map_mul, Complex.conj_conj,
    conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem norm_sq_eq_re_mul_conj (z : ℂ) : ‖z‖ ^ 2 = (z * conj z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

omit [DecidableEq ι] in
theorem norm_sq_quad_sub_eq (A : Matrix ι ι ℂ) (g : ι → ℂ) :
    ‖Counting.complexQuadraticForm A g - A.trace‖ ^ 2 =
      (Counting.complexQuadraticForm A g * Counting.complexQuadraticForm Aᴴ g -
        conj A.trace * Counting.complexQuadraticForm A g -
          A.trace * Counting.complexQuadraticForm Aᴴ g + A.trace * conj A.trace).re := by
  rw [norm_sq_eq_re_mul_conj, map_sub, conj_quad]
  congr 1
  ring

theorem integrable_quad_expand (A : Matrix ι ι ℂ) :
    Integrable (fun g => Counting.complexQuadraticForm A g * Counting.complexQuadraticForm Aᴴ g -
      conj A.trace * Counting.complexQuadraticForm A g -
        A.trace * Counting.complexQuadraticForm Aᴴ g + A.trace * conj A.trace)
      (circularVectorLaw ι) :=
  (((integrable_quad_mul A Aᴴ).sub ((integrable_quad' A).const_mul _)).sub
    ((integrable_quad' Aᴴ).const_mul _)).add (integrable_const _)

theorem integrable_norm_sq_quad_sub (A : Matrix ι ι ℂ) :
    Integrable (fun g => ‖Counting.complexQuadraticForm A g - A.trace‖ ^ 2)
      (circularVectorLaw ι) := by
  simp_rw [norm_sq_quad_sub_eq]
  exact (integrable_quad_expand A).re

/-- **Variance of a circular quadratic form**: `E|Q_A − Tr A|² = Re Tr AAᴴ`. -/
theorem integral_norm_sq_quad_sub (A : Matrix ι ι ℂ) :
    ∫ g, ‖Counting.complexQuadraticForm A g - A.trace‖ ^ 2 ∂circularVectorLaw ι =
      (A * Aᴴ).trace.re := by
  simp_rw [norm_sq_quad_sub_eq]
  have hre := integral_re (integrable_quad_expand A)
  simp only [RCLike.re_to_complex] at hre
  rw [hre]
  have hI1 := integrable_quad_mul A Aᴴ
  have hI2 := (integrable_quad' A).const_mul (conj A.trace)
  have hI3 := (integrable_quad' Aᴴ).const_mul A.trace
  have hI12 : Integrable (fun x => Counting.complexQuadraticForm A x *
      Counting.complexQuadraticForm Aᴴ x - conj A.trace * Counting.complexQuadraticForm A x)
      (circularVectorLaw ι) := hI1.sub hI2
  have hI123 : Integrable (fun x => Counting.complexQuadraticForm A x *
      Counting.complexQuadraticForm Aᴴ x - conj A.trace * Counting.complexQuadraticForm A x -
        A.trace * Counting.complexQuadraticForm Aᴴ x) (circularVectorLaw ι) := hI12.sub hI3
  rw [integral_add hI123 (integrable_const _), integral_sub hI12 hI3, integral_sub hI1 hI2,
    integral_const_mul, integral_const_mul,
    integral_quad_mul, integral_quad', integral_quad', integral_const]
  have htr : Aᴴ.trace = conj A.trace := by rw [trace_conjTranspose]; rfl
  rw [htr]
  simp only [probReal_univ, one_smul]
  congr 1
  ring

/-- **`L¹` concentration**: `E|Q_A − Tr A| ≤ (Re Tr AAᴴ)^{1/2}`. -/
theorem lintegral_quad_sub_le (A : Matrix ι ι ℂ) :
    ∫⁻ g, ‖Counting.complexQuadraticForm A g - A.trace‖ₑ ∂circularVectorLaw ι ≤
      ENNReal.ofReal (Real.sqrt (A * Aᴴ).trace.re) := by
  set f : (ι → ℂ) → ℝ≥0∞ := fun g => ‖Counting.complexQuadraticForm A g - A.trace‖ₑ with hfdef
  have hf : AEMeasurable f (circularVectorLaw ι) :=
    ((measurable_quad A).sub_const _).enorm.aemeasurable
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (circularVectorLaw ι) Real.HolderConjugate.two_two
    hf (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at hH
  refine hH.trans (le_of_eq ?_)
  have hsq : ∫⁻ g, f g ^ (2 : ℝ) ∂circularVectorLaw ι = ENNReal.ofReal (A * Aᴴ).trace.re := by
    rw [← integral_norm_sq_quad_sub, ofReal_integral_eq_lintegral_ofReal
      (integrable_norm_sq_quad_sub A) (Filter.Eventually.of_forall fun _ => by positivity)]
    refine lintegral_congr fun g => ?_
    simp only [hfdef]
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      Real.rpow_two]
  have h0 : 0 ≤ (A * Aᴴ).trace.re := by
    rw [← integral_norm_sq_quad_sub]; exact integral_nonneg fun _ => by positivity
  rw [hsq, ENNReal.ofReal_rpow_of_nonneg h0 (by norm_num), Real.sqrt_eq_rpow]

end BlockBand.SourceProcess.PhysApprox.B3.Birth
