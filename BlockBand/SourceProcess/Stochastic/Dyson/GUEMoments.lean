module

public import BlockBand.SourceProcess.Stochastic.Dyson.Coordinates
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Moments.Variance

/-!
# Dyson Brownian motion: first and second moments of the GUE increment law

For `Z ~ gueIncrementLaw N δ` and arbitrary complex matrices `A, B`:
* `E tr(A Z) = 0`, `E[tr(A Z) tr(B Z)] = (δ/N) tr(A B)` (the GUE covariance
  `E[Z_ab Z_cd] = δ δ_ad δ_bc / N` in trace form);
* hence for the orthonormal coordinates `hermCoord`,
  `E hermCoord Z x = 0` and `E[hermCoord Z x · hermCoord Z y] = δ/N · [x = y]`;
* all these coordinates are in every `L^p`, `p < ∞`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal Matrix ComplexConjugate
open BlockBand.Internal.Contracts.Transmission

section Pi

variable {ι : Type*} [Fintype ι] (δ : ℝ≥0)

/-- The product Gaussian measure on the coordinates. -/
abbrev gaussPi (ι : Type*) [Fintype ι] (δ : ℝ≥0) : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => gaussianReal 0 δ

theorem integral_comp_eval_gaussPi (k : ι) (g : ℝ → ℝ) (hg : Measurable g) :
    ∫ r, g (r k) ∂gaussPi ι δ = ∫ x, g x ∂gaussianReal 0 δ := by
  rw [← (measurePreserving_eval (fun _ : ι => gaussianReal 0 δ) k).map_eq,
    integral_map (measurable_pi_apply k).aemeasurable hg.aestronglyMeasurable]

theorem memLp_eval_gaussPi (k : ι) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun r : ι → ℝ => r k) p (gaussPi ι δ) :=
  (memLp_id_gaussianReal' (μ := 0) (v := δ) p hp).comp_measurePreserving
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 δ) k)

theorem integrable_eval_gaussPi (k : ι) : Integrable (fun r : ι → ℝ => r k) (gaussPi ι δ) :=
  (memLp_eval_gaussPi δ k 1 (by simp)).integrable le_rfl

theorem integral_eval_gaussPi (k : ι) : ∫ r, r k ∂gaussPi ι δ = 0 := by
  have := integral_comp_eval_gaussPi δ k id measurable_id
  simp only [id] at this
  rw [this]
  exact integral_id_gaussianReal

theorem integrable_eval_mul_eval_gaussPi (k l : ι) :
    Integrable (fun r : ι → ℝ => r k * r l) (gaussPi ι δ) :=
  (memLp_eval_gaussPi δ k 2 (by simp)).integrable_mul (memLp_eval_gaussPi δ l 2 (by simp))

theorem integral_eval_mul_eval_gaussPi [DecidableEq ι] (k l : ι) :
    ∫ r, r k * r l ∂gaussPi ι δ = if k = l then (δ : ℝ) else 0 := by
  split_ifs with h
  · subst h
    rw [integral_comp_eval_gaussPi δ k (fun x => x * x) (measurable_id.mul measurable_id)]
    have := variance_id_gaussianReal (μ := 0) (v := δ)
    rw [variance_of_integral_eq_zero measurable_id.aemeasurable (by simp)] at this
    simpa [sq] using this
  · have hind : IndepFun (fun r : ι → ℝ => r k) (fun r => r l) (gaussPi ι δ) :=
      (iIndepFun_pi (X := fun _ (x : ℝ) => x) fun _ => measurable_id.aemeasurable).indepFun h
    rw [IndepFun.integral_fun_mul_eq_mul_integral hind (measurable_pi_apply k).aestronglyMeasurable
      (measurable_pi_apply l).aestronglyMeasurable, integral_eval_gaussPi, zero_mul]

/-- Complex linear functional of the coordinates. -/
def linC (w : ι → ℂ) (r : ι → ℝ) : ℂ := ∑ k, w k * (r k : ℂ)

theorem integrable_linC (w : ι → ℂ) : Integrable (linC w) (gaussPi ι δ) :=
  integrable_finsetSum _ fun k _ => (integrable_eval_gaussPi δ k).ofReal.const_mul (w k)

theorem integral_linC (w : ι → ℂ) : ∫ r, linC w r ∂gaussPi ι δ = 0 := by
  unfold linC
  rw [integral_finsetSum (f := fun k (r : ι → ℝ) => w k * (r k : ℂ)) _
    fun k _ => (integrable_eval_gaussPi δ k).ofReal.const_mul (w k)]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_const_mul, integral_complex_ofReal, integral_eval_gaussPi]; simp

theorem integrable_linC_mul (w w' : ι → ℂ) :
    Integrable (fun r => linC w r * linC w' r) (gaussPi ι δ) := by
  unfold linC
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  refine integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => ?_
  have := ((integrable_eval_mul_eval_gaussPi δ k l).ofReal (𝕜 := ℂ)).const_mul (w k * w' l)
  refine this.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [RCLike.ofReal_mul, RCLike.ofReal_eq_complex_ofReal]; ring

theorem integral_linC_mul [DecidableEq ι] (w w' : ι → ℂ) :
    ∫ r, linC w r * linC w' r ∂gaussPi ι δ = (δ : ℂ) * ∑ k, w k * w' k := by
  have e : ∀ r, linC w r * linC w' r =
      ∑ k, ∑ l, (w k * w' l) * ((r k * r l : ℝ) : ℂ) := fun r => by
    unfold linC; simp_rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    push_cast; ring
  simp_rw [e]
  rw [integral_finsetSum (f := fun k (r : ι → ℝ) => ∑ l, (w k * w' l) * ((r k * r l : ℝ) : ℂ))
    _ fun k _ => integrable_finsetSum _ fun l _ =>
      ((integrable_eval_mul_eval_gaussPi δ k l).ofReal).const_mul _]
  simp_rw [fun k => integral_finsetSum
    (f := fun l (r : ι → ℝ) => (w k * w' l) * ((r k * r l : ℝ) : ℂ)) Finset.univ
    fun l (_ : l ∈ Finset.univ) =>
      ((integrable_eval_mul_eval_gaussPi δ k l).ofReal (𝕜 := ℂ)).const_mul (w k * w' l)]
  simp_rw [integral_const_mul, integral_complex_ofReal, integral_eval_mul_eval_gaussPi]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
  simp; ring

end Pi

section GUE

variable {N : ℕ}

/-- The scale `1/(2√N)` of `hermitianOfCoords`. -/
def gueScale (N : ℕ) : ℂ := ((1 / (2 * Real.sqrt N) : ℝ) : ℂ)

theorem gueScale_sq (N : ℕ) : gueScale N * gueScale N = 1 / (4 * N) := by
  unfold gueScale
  rw [← Complex.ofReal_mul]
  have : (1 / (2 * Real.sqrt N)) * (1 / (2 * Real.sqrt N)) = 1 / (4 * (N : ℝ)) := by
    rw [div_mul_div_comm, one_mul, show 2 * Real.sqrt N * (2 * Real.sqrt N) =
      4 * (Real.sqrt N * Real.sqrt N) by ring, Real.mul_self_sqrt (Nat.cast_nonneg N)]
  rw [this]; push_cast; ring

theorem hermitianOfCoords_apply (r : (Fin N × Fin N) × Fin 2 → ℝ) (a b : Fin N) :
    hermitianOfCoords N r a b = gueScale N * (((r ((a, b), 0) : ℂ) + (r ((a, b), 1) : ℂ) *
      Complex.I) + ((r ((b, a), 0) : ℂ) - (r ((b, a), 1) : ℂ) * Complex.I)) := by
  simp [hermitianOfCoords, gueScale, Matrix.add_apply, Matrix.conjTranspose_apply]
  ring

theorem continuous_hermitianOfCoords : Continuous (hermitianOfCoords N) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [hermitianOfCoords_apply]
  fun_prop

theorem measurable_hermitianOfCoords : Measurable (hermitianOfCoords N) :=
  continuous_hermitianOfCoords.measurable

theorem hermitianOfCoords_isHermitian (r : (Fin N × Fin N) × Fin 2 → ℝ) :
    (hermitianOfCoords N r).IsHermitian := by
  ext a b
  simp only [conjTranspose_apply, hermitianOfCoords_apply, RCLike.star_def, map_mul, map_add,
    map_sub, Complex.conj_ofReal, Complex.conj_I, gueScale]
  ring

/-- Weights of `r ↦ tr(A · hermitianOfCoords r)`. -/
def wTr (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : (Fin N × Fin N) × Fin 2) : ℂ :=
  if k.2 = 0 then gueScale N * (A k.1.2 k.1.1 + A k.1.1 k.1.2)
  else gueScale N * Complex.I * (A k.1.2 k.1.1 - A k.1.1 k.1.2)

theorem trace_mul_hermitianOfCoords (A : Matrix (Fin N) (Fin N) ℂ)
    (r : (Fin N × Fin N) × Fin 2 → ℝ) :
    trace (A * hermitianOfCoords N r) = linC (wTr N A) r := by
  simp only [linC, Fintype.sum_prod_type, Fin.sum_univ_two, wTr, trace, diag, mul_apply,
    hermitianOfCoords_apply]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
  have hswap : ∑ a, ∑ b, A a b * (gueScale N * ((r ((b, a), 0) : ℂ) + (r ((b, a), 1) : ℂ) *
      Complex.I)) = ∑ a, ∑ b, A b a * (gueScale N * ((r ((a, b), 0) : ℂ) + (r ((a, b), 1) : ℂ) *
      Complex.I)) := Finset.sum_comm
  have e1 : ∀ a b : Fin N, A a b * (gueScale N * (((r ((b, a), 0) : ℂ) + (r ((b, a), 1) : ℂ) *
      Complex.I) + ((r ((a, b), 0) : ℂ) - (r ((a, b), 1) : ℂ) * Complex.I))) =
      A a b * (gueScale N * ((r ((b, a), 0) : ℂ) + (r ((b, a), 1) : ℂ) * Complex.I)) +
      A a b * (gueScale N * ((r ((a, b), 0) : ℂ) - (r ((a, b), 1) : ℂ) * Complex.I)) :=
    fun a b => by ring
  simp_rw [e1, Finset.sum_add_distrib, hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem sum_wTr_mul_wTr (A B : Matrix (Fin N) (Fin N) ℂ) :
    ∑ k, wTr N A k * wTr N B k = (1 / N : ℂ) * trace (A * B) := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, wTr, Fin.isValue, ↓reduceIte, one_ne_zero]
  have hI := Complex.I_sq
  have hc := gueScale_sq N
  have e : ∀ a b : Fin N, gueScale N * (A b a + A a b) * (gueScale N * (B b a + B a b)) +
      gueScale N * Complex.I * (A b a - A a b) * (gueScale N * Complex.I * (B b a - B a b)) =
      (1 / (4 * N) : ℂ) * (2 * (A a b * B b a) + 2 * (A b a * B a b)) := fun a b => by
    linear_combination ((A b a + A a b) * (B b a + B a b) +
      Complex.I ^ 2 * (A b a - A a b) * (B b a - B a b)) * hc +
      (1 / (4 * N) : ℂ) * (A b a - A a b) * (B b a - B a b) * hI
  simp_rw [e, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : ∑ a, ∑ b, A b a * B a b = trace (A * B) := by
    rw [Finset.sum_comm]; simp [trace, mul_apply]
  have h2 : ∑ a, ∑ b, A a b * B b a = trace (A * B) := by simp [trace, mul_apply]
  rw [h1, h2]
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · field_simp; ring

variable (δ : ℝ≥0)

theorem integral_gue_eq (f : Matrix (Fin N) (Fin N) ℂ → ℂ) (hf : Measurable f) :
    ∫ Z, f Z ∂gueIncrementLaw N δ = ∫ r, f (hermitianOfCoords N r) ∂gaussPi _ δ :=
  integral_map measurable_hermitianOfCoords.aemeasurable hf.aestronglyMeasurable

theorem integral_gue_eq_real (f : Matrix (Fin N) (Fin N) ℂ → ℝ) (hf : Measurable f) :
    ∫ Z, f Z ∂gueIncrementLaw N δ = ∫ r, f (hermitianOfCoords N r) ∂gaussPi _ δ :=
  integral_map measurable_hermitianOfCoords.aemeasurable hf.aestronglyMeasurable

theorem measurable_trace_mul (A : Matrix (Fin N) (Fin N) ℂ) :
    Measurable fun Z : Matrix (Fin N) (Fin N) ℂ => trace (A * Z) := by
  simp only [trace, diag, mul_apply]
  fun_prop

/-- `E tr(A Z) = 0` under the GUE increment law. -/
theorem integral_trace_gue (A : Matrix (Fin N) (Fin N) ℂ) :
    ∫ Z, trace (A * Z) ∂gueIncrementLaw N δ = 0 := by
  rw [integral_gue_eq δ _ (measurable_trace_mul A)]
  simp_rw [trace_mul_hermitianOfCoords]
  exact integral_linC δ _

/-- `E[tr(A Z) tr(B Z)] = (δ/N) tr(A B)` under the GUE increment law. -/
theorem integral_trace_mul_trace_gue (A B : Matrix (Fin N) (Fin N) ℂ) :
    ∫ Z, trace (A * Z) * trace (B * Z) ∂gueIncrementLaw N δ = (δ / N : ℂ) * trace (A * B) := by
  rw [integral_gue_eq δ (fun Z => trace (A * Z) * trace (B * Z))
    ((measurable_trace_mul A).mul (measurable_trace_mul B))]
  simp_rw [trace_mul_hermitianOfCoords]
  rw [integral_linC_mul, sum_wTr_mul_wTr]
  ring

theorem measurable_hermCoord (x : Fin N × Fin N) :
    Measurable fun Z : Matrix (Fin N) (Fin N) ℂ => hermCoord N Z x :=
  Complex.measurable_re.comp (measurable_trace_mul _)

theorem hermCoord_hermitianOfCoords (x : Fin N × Fin N) (r : (Fin N × Fin N) × Fin 2 → ℝ) :
    hermCoord N (hermitianOfCoords N r) x = (linC (wTr N (hermBasis x)) r).re := by
  unfold hermCoord; rw [trace_mul_hermitianOfCoords]

theorem im_linC_wTr_hermBasis (x : Fin N × Fin N) (r : (Fin N × Fin N) × Fin 2 → ℝ) :
    (linC (wTr N (hermBasis x)) r).im = 0 := by
  rw [← trace_mul_hermitianOfCoords]
  exact Complex.conj_eq_iff_im.mp
    (trace_mul_conj_eq (hermBasis_isHermitian x) (hermitianOfCoords_isHermitian r))

theorem hermCoord_mul_hermitianOfCoords (x y : Fin N × Fin N)
    (r : (Fin N × Fin N) × Fin 2 → ℝ) :
    hermCoord N (hermitianOfCoords N r) x * hermCoord N (hermitianOfCoords N r) y =
      (linC (wTr N (hermBasis x)) r * linC (wTr N (hermBasis y)) r).re := by
  rw [hermCoord_hermitianOfCoords, hermCoord_hermitianOfCoords, Complex.mul_re,
    im_linC_wTr_hermBasis, zero_mul, sub_zero]

theorem integrable_hermCoord_gue (x : Fin N × Fin N) :
    Integrable (fun Z => hermCoord N Z x) (gueIncrementLaw N δ) := by
  rw [gueIncrementLaw, integrable_map_measure (measurable_hermCoord x).aestronglyMeasurable
    measurable_hermitianOfCoords.aemeasurable]
  simp only [Function.comp_def, hermCoord_hermitianOfCoords]
  exact (integrable_linC δ _).re

theorem integral_hermCoord_gue (x : Fin N × Fin N) :
    ∫ Z, hermCoord N Z x ∂gueIncrementLaw N δ = 0 := by
  rw [integral_gue_eq_real δ _ (measurable_hermCoord x)]
  simp only [hermCoord_hermitianOfCoords]
  change ∫ r, RCLike.re (linC (wTr N (hermBasis x)) r) ∂gaussPi _ δ = 0
  rw [integral_re (integrable_linC δ _), integral_linC]; rfl

theorem integrable_hermCoord_mul_gue (x y : Fin N × Fin N) :
    Integrable (fun Z => hermCoord N Z x * hermCoord N Z y) (gueIncrementLaw N δ) := by
  have hm : Measurable fun Z => hermCoord N Z x * hermCoord N Z y :=
    (measurable_hermCoord x).mul (measurable_hermCoord y)
  rw [gueIncrementLaw, integrable_map_measure hm.aestronglyMeasurable
    measurable_hermitianOfCoords.aemeasurable]
  simp only [Function.comp_def, hermCoord_mul_hermitianOfCoords]
  exact (integrable_linC_mul δ _ _).re

/-- **GUE covariance in orthonormal coordinates**: `E[y_x y_y] = δ/N · [x = y]`. -/
theorem integral_hermCoord_mul_gue (x y : Fin N × Fin N) :
    ∫ Z, hermCoord N Z x * hermCoord N Z y ∂gueIncrementLaw N δ =
      if x = y then (δ : ℝ) / N else 0 := by
  have hm : Measurable fun Z => hermCoord N Z x * hermCoord N Z y :=
    (measurable_hermCoord x).mul (measurable_hermCoord y)
  rw [integral_gue_eq_real δ _ hm]
  simp only [hermCoord_mul_hermitianOfCoords]
  change ∫ r, RCLike.re (linC (wTr N (hermBasis x)) r * linC (wTr N (hermBasis y)) r)
    ∂gaussPi _ δ = _
  rw [integral_re (integrable_linC_mul δ _ _), integral_linC_mul, sum_wTr_mul_wTr,
    trace_hermBasis_mul_hermBasis]
  split_ifs
  · rw [show (δ : ℂ) * ((1 / N : ℂ) * 1) = (((δ : ℝ) / N : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  · simp

end GUE

end BlockBand.SourceProcess.Stochastic.Dyson
