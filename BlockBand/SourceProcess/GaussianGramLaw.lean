module

public import BlockBand.External.PSSS.NativeLaw
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The circular Gaussian probe and the law of its linear images

The standard circular Gaussian vector on an explicit product space: centred, with covariance the
identity and zero pseudo-covariance; every deterministic linear image `Ag` is Gaussian with
covariance `AAᴴ`, in particular the probe `Vᴴg` has covariance the Gram matrix `VᴴV`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess
open scoped ENNReal NNReal ComplexConjugate BigOperators
open Matrix MeasureTheory ProbabilityTheory

/-- The real component law of a standard circular Gaussian: centered Gaussian
with variance `1/2`. -/
def standardCircularReal : Measure ℝ := gaussianReal 0 (1 / 2 : ℝ≥0)

/-- The explicit product law on real and imaginary components. -/
def standardCircularGaussian : Measure (ℝ × ℝ) :=
  standardCircularReal.prod standardCircularReal

instance : IsProbabilityMeasure standardCircularReal := by
  unfold standardCircularReal
  infer_instance

instance : IsProbabilityMeasure standardCircularGaussian := by
  unfold standardCircularGaussian
  infer_instance

/-- The complex coordinate on the product sample space. -/
def circularGaussianCoordinate (z : ℝ × ℝ) : ℂ := (z.1 : ℂ) + Complex.I * z.2

/-- A centered real Gaussian's second moment is its variance. -/
theorem integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v = (v : ℝ) := by
  rw [← variance_id_gaussianReal (μ := 0) (v := v)]
  rw [variance_eq_integral (by fun_prop)]
  simp [integral_id_gaussianReal]

/-- Each real component of the standard circular law has second moment `1/2`. -/
theorem integral_sq_standardCircularReal :
    ∫ x : ℝ, x ^ 2 ∂standardCircularReal = 1 / 2 := by
  simpa [standardCircularReal] using integral_sq_gaussianReal (1 / 2 : ℝ≥0)

/-- Squaring a real component remains integrable under the standard component law. -/
theorem integrable_sq_standardCircularReal :
    Integrable (fun x : ℝ => x ^ 2) standardCircularReal := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0)) (2 : ℝ≥0)).integrable_norm_pow
    (p := 2) (by norm_num)
  simpa [standardCircularReal, Real.norm_eq_abs, sq_abs] using h

/-- The explicit circular product law has total second moment one. -/
theorem integral_circular_normSq :
    ∫ z : ℝ × ℝ, (z.1 ^ 2 + z.2 ^ 2) ∂standardCircularGaussian = 1 := by
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) standardCircularReal := integrable_const 1
  have hx : Integrable (fun z : ℝ × ℝ => z.1 ^ 2) standardCircularGaussian := by
    simpa [standardCircularGaussian] using integrable_sq_standardCircularReal.smul_prod h1
  have hy : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) standardCircularGaussian := by
    simpa [standardCircularGaussian] using h1.smul_prod integrable_sq_standardCircularReal
  rw [integral_add hx hy]
  unfold standardCircularGaussian
  have ex : (∫ z : ℝ × ℝ, z.1 ^ 2 ∂standardCircularReal.prod standardCircularReal) =
      (∫ x : ℝ, x ^ 2 ∂standardCircularReal) * ∫ _ : ℝ, (1 : ℝ) ∂standardCircularReal := by
    simpa using integral_prod_mul (μ := standardCircularReal) (ν := standardCircularReal)
      (fun x : ℝ => x ^ 2) (fun _ : ℝ => (1 : ℝ))
  have ey : (∫ z : ℝ × ℝ, z.2 ^ 2 ∂standardCircularReal.prod standardCircularReal) =
      (∫ _ : ℝ, (1 : ℝ) ∂standardCircularReal) * ∫ y : ℝ, y ^ 2 ∂standardCircularReal := by
    simpa using integral_prod_mul (μ := standardCircularReal) (ν := standardCircularReal)
      (fun _ : ℝ => (1 : ℝ)) (fun y : ℝ => y ^ 2)
  rw [ex, ey]
  simp [integral_sq_standardCircularReal]
  norm_num

/-- The squared modulus of the explicit circular coordinate is `x²+y²`. -/
theorem conj_mul_circularGaussianCoordinate (z : ℝ × ℝ) :
    conj (circularGaussianCoordinate z) * circularGaussianCoordinate z =
      ((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [circularGaussianCoordinate] <;> norm_cast <;> ring

/-- In complex notation, the explicit standard circular coordinate satisfies
`E[conj Z · Z] = 1`. -/
theorem integral_conj_mul_circularGaussianCoordinate :
    ∫ z : ℝ × ℝ, conj (circularGaussianCoordinate z) * circularGaussianCoordinate z
      ∂standardCircularGaussian = 1 := by
  simp_rw [conj_mul_circularGaussianCoordinate]
  calc
    _ = ((∫ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 ∂standardCircularGaussian : ℝ) : ℂ) :=
      integral_ofReal
    _ = 1 := by rw [integral_circular_normSq]; norm_num

/-- The product probability law of a standard circular Gaussian vector. -/
def standardCircularGaussianVectorLaw (ι : Type*) [Fintype ι] :
    Measure (ι → ℝ × ℝ) :=
  Measure.pi (fun _ : ι => standardCircularGaussian)

instance {ι : Type*} [Fintype ι] :
    IsProbabilityMeasure (standardCircularGaussianVectorLaw ι) := by
  unfold standardCircularGaussianVectorLaw
  infer_instance

/-- The complex random vector carried by the explicit finite product space. -/
def circularGaussianVector {ι : Type*} (ω : ι → ℝ × ℝ) (i : ι) : ℂ :=
  circularGaussianCoordinate (ω i)

/-- Every coordinate of the explicit vector is measurable. -/
theorem measurable_circularGaussianVector {ι : Type*} [Fintype ι] (i : ι) :
    Measurable (fun ω : ι → ℝ × ℝ => circularGaussianVector ω i) := by
  unfold circularGaussianVector circularGaussianCoordinate
  fun_prop

/-- The coordinate family in the explicit product model is mutually independent. -/
theorem iIndepFun_circularGaussianVector {ι : Type*} [Fintype ι] :
    iIndepFun (fun i (ω : ι → ℝ × ℝ) => circularGaussianVector ω i)
      (standardCircularGaussianVectorLaw ι) := by
  unfold standardCircularGaussianVectorLaw circularGaussianVector
  exact iIndepFun_pi (fun _ => (by
    unfold circularGaussianCoordinate
    fun_prop : AEMeasurable circularGaussianCoordinate standardCircularGaussian))

/-- The explicit circular coordinate belongs to `L⁴`. -/
theorem memLp_four_circularGaussianCoordinate :
    MemLp circularGaussianCoordinate 4 standardCircularGaussian := by
  have hr : MemLp id 4 standardCircularReal := by
    simpa [standardCircularReal] using
      memLp_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0)) (4 : ℝ≥0)
  have hx : MemLp (fun z : ℝ × ℝ => (z.1 : ℂ)) 4 standardCircularGaussian := by
    exact (hr.comp_fst standardCircularReal).ofReal
  have hy : MemLp (fun z : ℝ × ℝ => Complex.I * (z.2 : ℂ)) 4
      standardCircularGaussian := by
    exact (hr.comp_snd standardCircularReal).ofReal.const_mul Complex.I
  exact hx.add hy

/-- One coordinate has zero mean. -/
theorem integral_circularGaussianCoordinate :
    ∫ z : ℝ × ℝ, circularGaussianCoordinate z ∂standardCircularGaussian = 0 := by
  have hz := memLp_four_circularGaussianCoordinate.integrable (by norm_num)
  rw [show circularGaussianCoordinate =
      (fun z : ℝ × ℝ => (z.1 : ℂ)) + (fun z => Complex.I * (z.2 : ℂ)) by
        rfl]
  simp only [Pi.add_apply]
  rw [integral_add]
  · unfold standardCircularGaussian
    have ex : (∫ z : ℝ × ℝ, (z.1 : ℂ)
        ∂standardCircularReal.prod standardCircularReal) =
        (∫ x : ℝ, (x : ℂ) ∂standardCircularReal) *
          ∫ _ : ℝ, (1 : ℂ) ∂standardCircularReal := by
      simpa using integral_prod_mul (μ := standardCircularReal) (ν := standardCircularReal)
        (fun x : ℝ => (x : ℂ)) (fun _ : ℝ => (1 : ℂ))
    have ey : (∫ z : ℝ × ℝ, Complex.I * (z.2 : ℂ)
        ∂standardCircularReal.prod standardCircularReal) =
        (∫ _ : ℝ, (1 : ℂ) ∂standardCircularReal) *
          ∫ y : ℝ, Complex.I * (y : ℂ) ∂standardCircularReal := by
      simpa using integral_prod_mul (μ := standardCircularReal) (ν := standardCircularReal)
        (fun _ : ℝ => (1 : ℂ)) (fun y : ℝ => Complex.I * (y : ℂ))
    have hm : (∫ x : ℝ, (x : ℂ) ∂standardCircularReal) = 0 := by
      calc
        _ = ((∫ x : ℝ, x ∂standardCircularReal : ℝ) : ℂ) := integral_ofReal
        _ = 0 := by simp [standardCircularReal, integral_id_gaussianReal]
    rw [ex, ey, integral_const_mul, hm]
    simp
  · have hr : MemLp id 4 standardCircularReal := by
      simpa [standardCircularReal] using
        memLp_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0)) (4 : ℝ≥0)
    exact (hr.comp_fst standardCircularReal).ofReal.integrable (by norm_num)
  · have hr : MemLp id 4 standardCircularReal := by
      simpa [standardCircularReal] using
        memLp_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0)) (4 : ℝ≥0)
    exact ((hr.comp_snd standardCircularReal).ofReal.const_mul Complex.I).integrable (by norm_num)

/-- The conjugate coordinate also has zero mean. -/
theorem integral_conj_circularGaussianCoordinate :
    ∫ z : ℝ × ℝ, conj (circularGaussianCoordinate z) ∂standardCircularGaussian = 0 := by
  have hz := memLp_four_circularGaussianCoordinate.star.integrable (by norm_num)
  rw [show (fun z : ℝ × ℝ => conj (circularGaussianCoordinate z)) =
      (fun z : ℝ × ℝ => (z.1 : ℂ)) + (fun z => -Complex.I * (z.2 : ℂ)) by
        funext z
        simp [circularGaussianCoordinate]]
  change (∫ z : ℝ × ℝ, (z.1 : ℂ) + (-Complex.I * (z.2 : ℂ))
    ∂standardCircularGaussian) = 0
  rw [integral_add]
  · unfold standardCircularGaussian
    have ex : (∫ z : ℝ × ℝ, (z.1 : ℂ)
        ∂standardCircularReal.prod standardCircularReal) =
        (∫ x : ℝ, (x : ℂ) ∂standardCircularReal) *
          ∫ _ : ℝ, (1 : ℂ) ∂standardCircularReal := by
      simpa using integral_prod_mul (μ := standardCircularReal) (ν := standardCircularReal)
        (fun x : ℝ => (x : ℂ)) (fun _ : ℝ => (1 : ℂ))
    have ey : (∫ z : ℝ × ℝ, -Complex.I * (z.2 : ℂ)
        ∂standardCircularReal.prod standardCircularReal) =
        (∫ _ : ℝ, (1 : ℂ) ∂standardCircularReal) *
          ∫ y : ℝ, -Complex.I * (y : ℂ) ∂standardCircularReal := by
      simpa using integral_prod_mul (μ := standardCircularReal) (ν := standardCircularReal)
        (fun _ : ℝ => (1 : ℂ)) (fun y : ℝ => -Complex.I * (y : ℂ))
    have hm : (∫ x : ℝ, (x : ℂ) ∂standardCircularReal) = 0 := by
      calc
        _ = ((∫ x : ℝ, x ∂standardCircularReal : ℝ) : ℂ) := integral_ofReal
        _ = 0 := by simp [standardCircularReal, integral_id_gaussianReal]
    rw [ex, ey, integral_const_mul, hm]
    simp
  · have hr : MemLp id 4 standardCircularReal := by
      simpa [standardCircularReal] using
        memLp_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0)) (4 : ℝ≥0)
    exact (hr.comp_fst standardCircularReal).ofReal.integrable (by norm_num)
  · have hr : MemLp id 4 standardCircularReal := by
      simpa [standardCircularReal] using
        memLp_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0)) (4 : ℝ≥0)
    exact ((hr.comp_snd standardCircularReal).ofReal.const_mul (-Complex.I)).integrable (by norm_num)

/-- The holomorphic second moment of a standard circular coordinate vanishes. -/
theorem integral_circularGaussianCoordinate_sq :
    ∫ z : ℝ × ℝ, circularGaussianCoordinate z ^ 2 ∂standardCircularGaussian = 0 := by
  have hxx : Integrable (fun z : ℝ × ℝ => ((z.1 ^ 2 : ℝ) : ℂ))
      standardCircularGaussian := by
    exact (integrable_sq_standardCircularReal.comp_fst standardCircularReal).ofReal
  have hyy : Integrable (fun z : ℝ × ℝ => ((z.2 ^ 2 : ℝ) : ℂ))
      standardCircularGaussian := by
    exact (integrable_sq_standardCircularReal.comp_snd standardCircularReal).ofReal
  have hr : Integrable (fun x : ℝ => x) standardCircularReal := by
    exact (memLp_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0))
      (2 : ℝ≥0)).integrable (by norm_num)
  have hxy : Integrable (fun z : ℝ × ℝ => ((z.1 * z.2 : ℝ) : ℂ))
      standardCircularGaussian := by
    have hxyR : Integrable (fun z : ℝ × ℝ => z.1 * z.2)
        (standardCircularReal.prod standardCircularReal) := hr.mul_prod (L := ℝ) hr
    exact Integrable.ofReal (𝕜 := ℂ) hxyR
  rw [show (fun z : ℝ × ℝ => circularGaussianCoordinate z ^ 2) =
      (fun z => ((z.1 ^ 2 : ℝ) : ℂ)) - (fun z => ((z.2 ^ 2 : ℝ) : ℂ)) +
        (fun z => (2 * Complex.I) * ((z.1 * z.2 : ℝ) : ℂ)) by
    funext z
    apply Complex.ext
    · simp [circularGaussianCoordinate, pow_two]
    · simp [circularGaussianCoordinate, pow_two]
      ring]
  change (∫ z : ℝ × ℝ,
    (((z.1 ^ 2 : ℝ) : ℂ) - ((z.2 ^ 2 : ℝ) : ℂ)) +
      (2 * Complex.I) * ((z.1 * z.2 : ℝ) : ℂ) ∂standardCircularGaussian) = 0
  rw [integral_add, integral_sub, integral_const_mul]
  · unfold standardCircularGaussian
    have ex : (∫ z : ℝ × ℝ, ((z.1 ^ 2 : ℝ) : ℂ)
        ∂standardCircularReal.prod standardCircularReal) = (1 / 2 : ℂ) := by
      calc
        _ = ((∫ z : ℝ × ℝ, z.1 ^ 2
            ∂standardCircularReal.prod standardCircularReal : ℝ) : ℂ) := integral_ofReal
        _ = (1 / 2 : ℂ) := by
          rw [show (∫ z : ℝ × ℝ, z.1 ^ 2
              ∂standardCircularReal.prod standardCircularReal) =
              (∫ x : ℝ, x ^ 2 ∂standardCircularReal) *
                ∫ _ : ℝ, (1 : ℝ) ∂standardCircularReal by
              simpa using integral_prod_mul (μ := standardCircularReal)
                (ν := standardCircularReal) (fun x : ℝ => x ^ 2) (fun _ : ℝ => (1 : ℝ))]
          simp [integral_sq_standardCircularReal]
    have ey : (∫ z : ℝ × ℝ, ((z.2 ^ 2 : ℝ) : ℂ)
        ∂standardCircularReal.prod standardCircularReal) = (1 / 2 : ℂ) := by
      calc
        _ = ((∫ z : ℝ × ℝ, z.2 ^ 2
            ∂standardCircularReal.prod standardCircularReal : ℝ) : ℂ) := integral_ofReal
        _ = (1 / 2 : ℂ) := by
          rw [show (∫ z : ℝ × ℝ, z.2 ^ 2
              ∂standardCircularReal.prod standardCircularReal) =
              (∫ _ : ℝ, (1 : ℝ) ∂standardCircularReal) *
                ∫ y : ℝ, y ^ 2 ∂standardCircularReal by
              simpa using integral_prod_mul (μ := standardCircularReal)
                (ν := standardCircularReal) (fun _ : ℝ => (1 : ℝ)) (fun y : ℝ => y ^ 2)]
          simp [integral_sq_standardCircularReal]
    have exy : (∫ z : ℝ × ℝ, ((z.1 * z.2 : ℝ) : ℂ)
        ∂standardCircularReal.prod standardCircularReal) = 0 := by
      calc
        _ = ((∫ z : ℝ × ℝ, z.1 * z.2
            ∂standardCircularReal.prod standardCircularReal : ℝ) : ℂ) := integral_ofReal
        _ = 0 := by
          rw [show (∫ z : ℝ × ℝ, z.1 * z.2
              ∂standardCircularReal.prod standardCircularReal) =
              (∫ x : ℝ, x ∂standardCircularReal) *
                ∫ y : ℝ, y ∂standardCircularReal by
              simpa using integral_prod_mul (μ := standardCircularReal)
                (ν := standardCircularReal) (fun x : ℝ => x) (fun y : ℝ => y)]
          simp [standardCircularReal, integral_id_gaussianReal]
    rw [ex, ey, exy]
    norm_num
  all_goals first | exact hxx | exact hyy | exact hxx.sub hyy |
    exact hxy.const_mul (2 * Complex.I)

/-- The antiholomorphic second moment also vanishes. -/
theorem integral_conj_circularGaussianCoordinate_sq :
    ∫ z : ℝ × ℝ, conj (circularGaussianCoordinate z) ^ 2
      ∂standardCircularGaussian = 0 := by
  have hcongr : (fun z : ℝ × ℝ => conj (circularGaussianCoordinate z) ^ 2) =
      fun z => conj (circularGaussianCoordinate z ^ 2) := by
    funext z
    rw [map_pow]
  rw [hcongr]
  change ∫ z : ℝ × ℝ, (starL ℝ) (circularGaussianCoordinate z ^ 2)
      ∂standardCircularGaussian = 0
  have hz2 : Integrable (fun z : ℝ × ℝ => circularGaussianCoordinate z ^ 2)
      standardCircularGaussian := by
    have h2 : MemLp circularGaussianCoordinate 2 standardCircularGaussian :=
      memLp_four_circularGaussianCoordinate.mono_exponent (by norm_num)
    have hm : MemLp (circularGaussianCoordinate * circularGaussianCoordinate) 1
        standardCircularGaussian := h2.mul h2
    exact (hm.integrable (by norm_num)).congr
      (Filter.Eventually.of_forall fun z => by simp only [Pi.mul_apply, pow_two])
  have hs := (starL ℝ).toContinuousLinearMap.integral_comp_comm hz2
  change ∫ z : ℝ × ℝ, (starL ℝ).toContinuousLinearMap
      (circularGaussianCoordinate z ^ 2) ∂standardCircularGaussian = 0
  rw [hs]
  rw [integral_circularGaussianCoordinate_sq]
  simp

/-- Every coordinate of the finite circular vector belongs to `L⁴`. -/
theorem memLp_four_circularGaussianVector {ι : Type*} [Fintype ι] (i : ι) :
    MemLp (fun ω : ι → ℝ × ℝ => circularGaussianVector ω i) 4
      (standardCircularGaussianVectorLaw ι) := by
  have he := measurePreserving_eval (fun _ : ι => standardCircularGaussian) i
  have hmap : MemLp circularGaussianCoordinate 4
      (Measure.map (Function.eval i) (standardCircularGaussianVectorLaw ι)) := by
    rw [show Measure.map (Function.eval i) (standardCircularGaussianVectorLaw ι) =
        standardCircularGaussian by
      exact he.map_eq]
    exact memLp_four_circularGaussianCoordinate
  exact (memLp_map_measure_iff hmap.aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable).mp hmap

/-- The coordinate second contraction is integrable. -/
theorem integrable_circularGaussianVector_second {ι : Type*} [Fintype ι] (i j : ι) :
    Integrable (fun ω : ι → ℝ × ℝ =>
      conj (circularGaussianVector ω i) * circularGaussianVector ω j)
      (standardCircularGaussianVectorLaw ι) := by
  have hi : MemLp (star (fun ω : ι → ℝ × ℝ => circularGaussianVector ω i)) 2
      (standardCircularGaussianVectorLaw ι) := by
    exact ((memLp_four_circularGaussianVector i).mono_exponent (by norm_num)).star
  have hj : MemLp (fun ω : ι → ℝ × ℝ => circularGaussianVector ω j) 2
      (standardCircularGaussianVectorLaw ι) :=
    (memLp_four_circularGaussianVector j).mono_exponent (by norm_num)
  have hm : MemLp
      ((star (fun ω : ι → ℝ × ℝ => circularGaussianVector ω i)) *
        (fun ω => circularGaussianVector ω j)) 1
      (standardCircularGaussianVectorLaw ι) := hi.mul hj
  exact (hm.integrable (by norm_num)).congr
    (Filter.Eventually.of_forall fun _ => by simp [Pi.mul_apply, RCLike.star_def])

/-- A one-coordinate factorization of the second contraction. -/
private def circularWickSecondFactor {ι : Type*} [DecidableEq ι]
    (i j r : ι) (z : ℝ × ℝ) : ℂ :=
  (if i = r then conj (circularGaussianCoordinate z) else 1) *
    (if j = r then circularGaussianCoordinate z else 1)

@[simp] private theorem fintype_prod_ite_eq
    {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (a : ι) (b : ι → M) :
    (∏ x, if a = x then b x else 1) = b a := by
  simp

/-- The explicit product circular law has covariance identity:
`E[conj(gᵢ) gⱼ] = δᵢⱼ`. -/
theorem integral_circularGaussianVector_second
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    ∫ ω : ι → ℝ × ℝ,
      conj (circularGaussianVector ω i) * circularGaussianVector ω j
        ∂standardCircularGaussianVectorLaw ι = if i = j then 1 else 0 := by
  rw [show (fun ω : ι → ℝ × ℝ =>
      conj (circularGaussianVector ω i) * circularGaussianVector ω j) =
      fun ω => ∏ r, circularWickSecondFactor i j r (ω r) by
    funext ω
    simp only [circularWickSecondFactor, Finset.prod_mul_distrib]
    rw [fintype_prod_ite_eq, fintype_prod_ite_eq]
    rfl]
  unfold standardCircularGaussianVectorLaw
  rw [integral_fintype_prod_eq_prod]
  by_cases hij : i = j
  · subst j
    simp
    apply Finset.prod_eq_one
    intro r _
    by_cases hir : i = r
    · subst r
      simpa [circularWickSecondFactor] using
        integral_conj_mul_circularGaussianCoordinate
    · simp [circularWickSecondFactor, hir]
  · simp [hij]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have hji : j ≠ i := Ne.symm hij
    simp [circularWickSecondFactor, hji, integral_conj_circularGaussianCoordinate]

/-- The scalar coordinate is the real-pair reconstruction of `External.PSSS.NativeLaw`. -/
theorem circularGaussianCoordinate_eq_native (z : ℝ × ℝ) :
    circularGaussianCoordinate z =
      BlockBand.External.PSSS.BlockGUE.complexOfUpperRealPair z := by
  simp [circularGaussianCoordinate,
    BlockBand.External.PSSS.BlockGUE.complexOfUpperRealPair, mul_comm]

/-- Circular scalar complex measure, reconstructed from the explicit pair law. -/
def circularComplexMeasure : Measure ℂ :=
  standardCircularGaussian.map circularGaussianCoordinate

/-- Circular real-pair reconstruction is measurable. -/
theorem measurable_circularGaussianCoordinate : Measurable circularGaussianCoordinate := by
  have h : circularGaussianCoordinate =
      BlockBand.External.PSSS.BlockGUE.complexOfUpperRealPair :=
    funext circularGaussianCoordinate_eq_native
  rw [h]
  exact BlockBand.External.PSSS.BlockGUE.measurable_complexOfUpperRealPair

/-- The scalar complex measure is a probability measure. -/
instance circularComplexMeasure_probability : IsProbabilityMeasure circularComplexMeasure := by
  unfold circularComplexMeasure
  infer_instance

/-- The scalar coordinate is Gaussian, from independent real Gaussian marginals and a real-linear
equivalence. -/
theorem hasGaussianLaw_circularGaussianCoordinate :
    HasGaussianLaw circularGaussianCoordinate standardCircularGaussian := by
  let : IsGaussian standardCircularReal := by
    unfold standardCircularReal
    infer_instance
  have hfst : HasGaussianLaw (fun z : ℝ × ℝ => z.1) standardCircularGaussian := by
    exact (measurePreserving_fst (μ := standardCircularReal)
      (ν := standardCircularReal)).hasLaw.hasGaussianLaw
  have hsnd : HasGaussianLaw (fun z : ℝ × ℝ => z.2) standardCircularGaussian := by
    exact (measurePreserving_snd (μ := standardCircularReal)
      (ν := standardCircularReal)).hasLaw.hasGaussianLaw
  have hind : IndepFun (fun z : ℝ × ℝ => z.1) (fun z : ℝ × ℝ => z.2)
      standardCircularGaussian := by
    exact indepFun_prod (μ := standardCircularReal) (ν := standardCircularReal)
      measurable_id measurable_id
  have hpair := IndepFun.hasGaussianLaw hfst hsnd hind
  have hmap := hpair.map_fun Complex.equivRealProdCLM.symm.toContinuousLinearMap
  apply hmap.congr
  exact Filter.Eventually.of_forall fun z => by
    simp [circularGaussianCoordinate, Complex.equivRealProdCLM_symm_apply, mul_comm]

/-- The scalar complex law is Gaussian by its proved pair reconstruction. -/
instance circularComplexMeasure_isGaussian : IsGaussian circularComplexMeasure :=
  hasGaussianLaw_circularGaussianCoordinate.isGaussian_map

/-- Every coordinate has the constructed scalar complex law. -/
theorem hasLaw_circularGaussianVector_coordinate {ι : Type*} [Fintype ι] (i : ι) :
    HasLaw (fun ω : ι → ℝ × ℝ => circularGaussianVector ω i)
      circularComplexMeasure (standardCircularGaussianVectorLaw ι) := by
  exact (hasLaw_map measurable_circularGaussianCoordinate.aemeasurable).fun_comp
    (measurePreserving_eval (fun _ : ι => standardCircularGaussian) i).hasLaw

/-- The finite complex vector measure. -/
def circularComplexVectorMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℂ) :=
  Measure.pi (fun _ : ι => circularComplexMeasure)

instance circularComplexVectorMeasure_probability {ι : Type*} [Fintype ι] :
    IsProbabilityMeasure (circularComplexVectorMeasure ι) := by
  unfold circularComplexVectorMeasure
  infer_instance

/-- The reconstructed vector has the finite independent complex product law. -/
theorem hasLaw_circularGaussianVector {ι : Type*} [Fintype ι] :
    HasLaw (fun ω : ι → ℝ × ℝ => circularGaussianVector ω)
      (circularComplexVectorMeasure ι) (standardCircularGaussianVectorLaw ι) :=
  (iIndepFun_circularGaussianVector (ι := ι)).hasLaw_pi
    hasLaw_circularGaussianVector_coordinate

/-- Scalar Gaussian coordinates and independence construct joint Gaussianity. -/
theorem hasGaussianLaw_circularGaussianVector {ι : Type*} [Fintype ι] :
    HasGaussianLaw (fun ω : ι → ℝ × ℝ => circularGaussianVector ω)
      (standardCircularGaussianVectorLaw ι) := by
  exact iIndepFun.hasGaussianLaw
    (fun i => (hasLaw_circularGaussianVector_coordinate i).hasGaussianLaw)
    iIndepFun_circularGaussianVector

/-- Every finite-coordinate input is Lp for every finite exponent. -/
theorem memLp_circularGaussianVector {ι : Type*} [Fintype ι]
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun ω : ι → ℝ × ℝ => circularGaussianVector ω) p
      (standardCircularGaussianVectorLaw ι) :=
  hasGaussianLaw_circularGaussianVector.memLp hp

/-- Vector coordinate mean, pulled back from the explicit scalar measure. -/
theorem integral_circularGaussianVector_coordinate {ι : Type*} [Fintype ι] (i : ι) :
    ∫ ω : ι → ℝ × ℝ, circularGaussianVector ω i
      ∂standardCircularGaussianVectorLaw ι = 0 := by
  change ∫ ω : ι → ℝ × ℝ, circularGaussianCoordinate (ω i)
    ∂Measure.pi (fun _ : ι => standardCircularGaussian) = 0
  rw [integral_comp_eval measurable_circularGaussianCoordinate.aestronglyMeasurable,
    integral_circularGaussianCoordinate]

/-- Coordinate covariance with the conventional yyᴴ orientation. -/
theorem integral_circularGaussianVector_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) :
    ∫ ω : ι → ℝ × ℝ, circularGaussianVector ω i * conj (circularGaussianVector ω j)
      ∂standardCircularGaussianVectorLaw ι = if i = j then 1 else 0 := by
  simpa only [mul_comm, eq_comm] using integral_circularGaussianVector_second j i

/-- The holomorphic second contraction vanishes, including coincident indices. -/
theorem integral_circularGaussianVector_pseudoCovariance
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    ∫ ω : ι → ℝ × ℝ, circularGaussianVector ω i * circularGaussianVector ω j
      ∂standardCircularGaussianVectorLaw ι = 0 := by
  by_cases hij : i = j
  · subst j
    change ∫ ω : ι → ℝ × ℝ,
      circularGaussianCoordinate (ω i) * circularGaussianCoordinate (ω i)
        ∂Measure.pi (fun _ : ι => standardCircularGaussian) = 0
    simp_rw [← pow_two]
    rw [integral_comp_eval (μ := fun _ : ι => standardCircularGaussian) (i := i)
      (f := fun z : ℝ × ℝ => circularGaussianCoordinate z ^ 2)
      (measurable_circularGaussianCoordinate.pow_const 2).aestronglyMeasurable]
    exact integral_circularGaussianCoordinate_sq
  · have hind := (iIndepFun_circularGaussianVector (ι := ι)).indepFun hij
    rw [hind.integral_fun_mul_eq_mul_integral
      (measurable_circularGaussianVector i).aestronglyMeasurable
      (measurable_circularGaussianVector j).aestronglyMeasurable,
      integral_circularGaussianVector_coordinate i, integral_circularGaussianVector_coordinate j,
      zero_mul]

/-- Real continuous linear realization of a deterministic complex matrix. -/
def gaussianMatrixCLM {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix κ ι ℂ) : (ι → ℂ) →L[ℝ] (κ → ℂ) :=
  (A.mulVecLin.restrictScalars ℝ).toContinuousLinearMap

/-- Probe image on the explicit real-pair product probability space. -/
def linearGaussianImage {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix κ ι ℂ) (ω : ι → ℝ × ℝ) : κ → ℂ :=
  gaussianMatrixCLM A (circularGaussianVector ω)

/-- Image measure is constructed, including for singular and zero matrices. -/
def linearGaussianImageMeasure {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix κ ι ℂ) : Measure (κ → ℂ) :=
  (circularComplexVectorMeasure ι).map (gaussianMatrixCLM A)

instance linearGaussianImageMeasure_probability {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix κ ι ℂ) : IsProbabilityMeasure (linearGaussianImageMeasure A) := by
  unfold linearGaussianImageMeasure
  infer_instance

/-- The product-law image has its constructed image distribution. -/
theorem hasLaw_linearGaussianImage {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix κ ι ℂ) :
    HasLaw (linearGaussianImage A) (linearGaussianImageMeasure A)
      (standardCircularGaussianVectorLaw ι) := by
  exact (hasLaw_map (gaussianMatrixCLM A).measurable.aemeasurable).fun_comp
    hasLaw_circularGaussianVector

/-- Gaussianity follows from the proved joint product law by a linear map. -/
theorem hasGaussianLaw_linearGaussianImage {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix κ ι ℂ) :
    HasGaussianLaw (linearGaussianImage A) (standardCircularGaussianVectorLaw ι) :=
  hasGaussianLaw_circularGaussianVector.map_fun (gaussianMatrixCLM A)

/-- All finite Lp moments of the matrix image exist. -/
theorem memLp_linearGaussianImage {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix κ ι ℂ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (linearGaussianImage A) p (standardCircularGaussianVectorLaw ι) :=
  (hasGaussianLaw_linearGaussianImage A).memLp hp

/-- The image is the advertised matrix-vector product. -/
theorem linearGaussianImage_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix κ ι ℂ) (ω : ι → ℝ × ℝ) :
    linearGaussianImage A ω = A *ᵥ circularGaussianVector ω := rfl

/-- The explicit standard finite circular vector is centered. -/
theorem integral_circularGaussianVector {ι : Type*} [Fintype ι] :
    ∫ ω : ι → ℝ × ℝ, circularGaussianVector ω
      ∂standardCircularGaussianVectorLaw ι = 0 := by
  funext i
  have h := ((LinearMap.proj i : (ι → ℂ) →ₗ[ℝ] ℂ).toContinuousLinearMap).integral_comp_comm
    ((memLp_circularGaussianVector 1 (by norm_num)).integrable le_rfl)
  exact h.symm.trans (integral_circularGaussianVector_coordinate i)

/-- Every deterministic linear image is centered under the constructed probability law. -/
theorem integral_linearGaussianImage {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix κ ι ℂ) :
    ∫ ω : ι → ℝ × ℝ, linearGaussianImage A ω
      ∂standardCircularGaussianVectorLaw ι = 0 := by
  unfold linearGaussianImage
  rw [(gaussianMatrixCLM A).integral_comp_comm
    ((memLp_circularGaussianVector 1 (by norm_num)).integrable le_rfl),
    integral_circularGaussianVector, map_zero]

/-- Every covariance integrand of the standard input is integrable. -/
theorem integrable_circularGaussianVector_covariance {ι : Type*} [Fintype ι] (i j : ι) :
    Integrable (fun ω : ι → ℝ × ℝ =>
      circularGaussianVector ω i * conj (circularGaussianVector ω j))
      (standardCircularGaussianVectorLaw ι) := by
  simpa only [mul_comm] using integrable_circularGaussianVector_second j i

/-- The covariance of a matrix image is `AAᴴ`. -/
theorem integral_linearGaussianImage_covariance {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : Matrix κ ι ℂ) (i j : κ) :
    ∫ ω : ι → ℝ × ℝ, linearGaussianImage A ω i * conj (linearGaussianImage A ω j)
      ∂standardCircularGaussianVectorLaw ι = (A * Aᴴ) i j := by
  have hexpand (ω : ι → ℝ × ℝ) :
      linearGaussianImage A ω i * conj (linearGaussianImage A ω j) =
        ∑ a, ∑ b, (A i a * conj (A j b)) *
          (circularGaussianVector ω a * conj (circularGaussianVector ω b)) := by
    simp only [linearGaussianImage_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
      Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum _]
  · trans ∑ a, ∑ b, (A i a * conj (A j b)) * (if a = b then 1 else 0)
    · apply Finset.sum_congr rfl
      intro a _
      rw [integral_finsetSum _ (fun b _ =>
        (integrable_circularGaussianVector_covariance a b).const_mul _)]
      simp_rw [integral_const_mul, integral_circularGaussianVector_covariance]
    · simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  · intro a _
    exact integrable_finsetSum _ (fun b _ =>
      (integrable_circularGaussianVector_covariance a b).const_mul _)

/-- Holomorphic second integrands are integrable under the circular law. -/
theorem integrable_circularGaussianVector_pseudoCovariance {ι : Type*} [Fintype ι]
    (i j : ι) :
    Integrable (fun ω : ι → ℝ × ℝ => circularGaussianVector ω i * circularGaussianVector ω j)
      (standardCircularGaussianVectorLaw ι) :=
  ((memLp_four_circularGaussianVector i).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).integrable_mul
    ((memLp_four_circularGaussianVector j).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4))

/-- All deterministic complex linear images have zero pseudo covariance. -/
theorem integral_linearGaussianImage_pseudoCovariance {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : Matrix κ ι ℂ) (i j : κ) :
    ∫ ω : ι → ℝ × ℝ, linearGaussianImage A ω i * linearGaussianImage A ω j
      ∂standardCircularGaussianVectorLaw ι = 0 := by
  have hexpand (ω : ι → ℝ × ℝ) :
      linearGaussianImage A ω i * linearGaussianImage A ω j =
        ∑ a, ∑ b, (A i a * A j b) *
          (circularGaussianVector ω a * circularGaussianVector ω b) := by
    simp only [linearGaussianImage_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum _]
  · trans ∑ a, ∑ b, (A i a * A j b) * 0
    · apply Finset.sum_congr rfl
      intro a _
      rw [integral_finsetSum _ (fun b _ =>
        (integrable_circularGaussianVector_pseudoCovariance a b).const_mul _)]
      simp_rw [integral_const_mul, integral_circularGaussianVector_pseudoCovariance]
    · simp
  · intro a _
    exact integrable_finsetSum _ (fun b _ =>
      (integrable_circularGaussianVector_pseudoCovariance a b).const_mul _)

/-- The physical Gram orientation for y=Vᴴg is exactly VᴴV. -/
theorem integral_probeGaussianImage_gram {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (V : Matrix ι κ ℂ) (i j : κ) :
    ∫ ω : ι → ℝ × ℝ, linearGaussianImage Vᴴ ω i * conj (linearGaussianImage Vᴴ ω j)
      ∂standardCircularGaussianVectorLaw ι = (Vᴴ * V) i j := by
  simpa only [Matrix.conjTranspose_conjTranspose] using
    integral_linearGaussianImage_covariance Vᴴ i j

/-- Explicit diagonal square-root source map; zero variances remain allowed. -/
def sourceVarianceMatrix {ι : Type*} [DecidableEq ι] (v : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => (Real.sqrt (v i) : ℂ))

/-- Square-root normalization of the constructed diagonal source map. -/
theorem sourceVarianceMatrix_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) :
    sourceVarianceMatrix v * (sourceVarianceMatrix v)ᴴ = Matrix.diagonal (fun i => (v i : ℂ)) := by
  rw [sourceVarianceMatrix, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  norm_cast
  exact Real.mul_self_sqrt (hv i)

/-- Covariance of an explicitly constructed source with arbitrary nonnegative variances. -/
theorem integral_sourceVarianceImage_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) (i j : ι) :
    ∫ ω : ι → ℝ × ℝ,
      linearGaussianImage (sourceVarianceMatrix v) ω i *
        conj (linearGaussianImage (sourceVarianceMatrix v) ω j)
      ∂standardCircularGaussianVectorLaw ι = Matrix.diagonal (fun k => (v k : ℂ)) i j := by
  rw [integral_linearGaussianImage_covariance, sourceVarianceMatrix_gram v hv]

/-- Conditional fixed-tag scale m/W under the product Gaussian measure. -/
theorem integral_tagSourceImage_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (hm : ∀ i, 0 ≤ m i) (W : ℕ) (hW : 0 < W) (i j : ι) :
    ∫ ω : ι → ℝ × ℝ,
      linearGaussianImage (sourceVarianceMatrix (fun k => m k / W)) ω i *
        conj (linearGaussianImage (sourceVarianceMatrix (fun k => m k / W)) ω j)
      ∂standardCircularGaussianVectorLaw ι =
        Matrix.diagonal (fun k => (m k / W : ℂ)) i j := by
  have hWr : (0 : ℝ) < W := Nat.cast_pos.mpr hW
  simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using
    integral_sourceVarianceImage_covariance (fun k => m k / W)
      (fun k => div_nonneg (hm k) hWr.le) i j

/-- Extended interval Gaussian scale q/W²; this is distinct from the sampled-tag mixture. -/
theorem integral_intervalSourceImage_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (W : ℕ) (i j : ι) :
    ∫ ω : ι → ℝ × ℝ,
      linearGaussianImage (sourceVarianceMatrix (fun k => q k / (W : ℝ)^2)) ω i *
        conj (linearGaussianImage (sourceVarianceMatrix (fun k => q k / (W : ℝ)^2)) ω j)
      ∂standardCircularGaussianVectorLaw ι =
        Matrix.diagonal (fun k => (q k / (W : ℝ)^2 : ℂ)) i j := by
  simpa only [Complex.ofReal_div, Complex.ofReal_pow] using
    integral_sourceVarianceImage_covariance (fun k => q k / (W : ℝ)^2)
      (fun k => div_nonneg (hq k) (sq_nonneg _)) i j

/-- Every image-coordinate covariance integrand is integrable. -/
theorem integrable_linearGaussianImage_covariance {ι κ : Type*}
    [Fintype ι] [Fintype κ] (A : Matrix κ ι ℂ) (i j : κ) :
    Integrable (fun ω : ι → ℝ × ℝ =>
      linearGaussianImage A ω i * conj (linearGaussianImage A ω j))
      (standardCircularGaussianVectorLaw ι) := by
  have hi := ((hasGaussianLaw_linearGaussianImage A).map_fun
    (LinearMap.proj i : (κ → ℂ) →ₗ[ℝ] ℂ).toContinuousLinearMap).memLp
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  have hj := ((hasGaussianLaw_linearGaussianImage A).map_fun
    (LinearMap.proj j : (κ → ℂ) →ₗ[ℝ] ℂ).toContinuousLinearMap).memLp
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  exact (hi.integrable_mul hj.star).congr
    (Filter.Eventually.of_forall fun _ => by rfl)

/-- The expected squared Euclidean length is the trace of the covariance. -/
theorem integral_linearGaussianImage_squaredLength {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : Matrix κ ι ℂ) :
    ∫ ω : ι → ℝ × ℝ,
      (∑ i, linearGaussianImage A ω i * conj (linearGaussianImage A ω i))
      ∂standardCircularGaussianVectorLaw ι = Matrix.trace (A * Aᴴ) := by
  rw [integral_finsetSum _ (fun i _ => integrable_linearGaussianImage_covariance A i i)]
  simp_rw [integral_linearGaussianImage_covariance]
  rfl

end BlockBand.SourceProcess
