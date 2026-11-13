module

public import BlockBand.Internal.Contracts.CoareaPalm

/-!
# `GUENormTail`, Gaussian part: Chernoff bound for a fixed bilinear form of `GUE`

* `lintegral_exp_linear`: for the standard Gaussian product `stdGaussPi J` on `J → ℝ` and
  `c : J → ℝ`, `E e^{λ Σ c_j r_j} = e^{λ² Σ c_j² / 2}`.
* `stdGaussPi_tail`: Chernoff, `P(a < Σ c_j r_j) ≤ e^{-a²/(2V)}` when `Σ c_j² ≤ V`, `a ≥ 0`.
* `re_bil_gueSample`: for `G = gueSample t (circularBrownianCoordinates r)` and fixed
  `w, v : ι → ℂ`, `Re(w* G v) = Σ_j gueCoef t w v j · r_j` (an explicit linear form in the
  standard real Gaussian coordinates `r` of `commonCircularIncrementLaw ι 1`).
* `sum_gueCoef_sq_le`: `Σ_j gueCoef_j² ≤ t ‖w‖² ‖v‖²`.
* `gueMeasure_bil_tail`: `GUE_ι(t){G | a < Re(w* G v)} ≤ e^{-a²/(2V)}` whenever
  `t ‖w‖² ‖v‖² ≤ V`, `V > 0`, `a ≥ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.GUENormTail

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal ComplexConjugate
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess

/-- The standard real Gaussian product measure on `J → ℝ`. -/
abbrev stdGaussPi (J : Type*) [Fintype J] : Measure (J → ℝ) :=
  Measure.pi fun _ : J => gaussianReal 0 1

section Chernoff

variable {J : Type*} [Fintype J]

theorem measurable_linear (c : J → ℝ) : Measurable fun r : J → ℝ => ∑ j, c j * r j :=
  Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).const_mul _

/-- Exponential moment of a linear form of a standard Gaussian vector. -/
theorem lintegral_exp_linear (c : J → ℝ) (lam : ℝ) :
    ∫⁻ r, ENNReal.ofReal (Real.exp (lam * ∑ j, c j * r j)) ∂stdGaussPi J =
      ENNReal.ofReal (Real.exp (lam ^ 2 * (∑ j, c j ^ 2) / 2)) := by
  have hprod : ∀ r : J → ℝ,
      Real.exp (lam * ∑ j, c j * r j) = ∏ j, Real.exp ((lam * c j) * r j) := by
    intro r
    rw [Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => by ring_nf
  simp_rw [hprod]
  have hint : Integrable (fun r : J → ℝ => ∏ j, Real.exp ((lam * c j) * r j)) (stdGaussPi J) :=
    Integrable.fintype_prod (f := fun j x => Real.exp ((lam * c j) * x))
      fun j => integrable_exp_mul_gaussianReal _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun r => by positivity)]
  congr 1
  rw [integral_fintype_prod_eq_prod (f := fun j x => Real.exp ((lam * c j) * x))]
  have h1 : ∀ j, ∫ x, Real.exp ((lam * c j) * x) ∂gaussianReal 0 1 =
      Real.exp ((lam * c j) ^ 2 / 2) := by
    intro j
    have := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) (lam * c j)
    simp only [mgf, id] at this
    rw [this]
    congr 1
    push_cast
    ring
  simp_rw [h1, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Chernoff bound** for a linear form of a standard Gaussian vector. -/
theorem stdGaussPi_tail (c : J → ℝ) {a V : ℝ} (ha : 0 ≤ a) (hV : 0 < V)
    (hc : ∑ j, c j ^ 2 ≤ V) :
    stdGaussPi J {r | a < ∑ j, c j * r j} ≤ ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * V)))) := by
  set lam := a / V with hlam_def
  have hlam : 0 ≤ lam := div_nonneg ha hV.le
  have hsub : {r : J → ℝ | a < ∑ j, c j * r j} ⊆
      {r | ENNReal.ofReal (Real.exp (lam * a)) ≤
        ENNReal.ofReal (Real.exp (lam * ∑ j, c j * r j))} := by
    intro r hr
    exact ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_of_lt hr) hlam))
  have hmeas : AEMeasurable
      (fun r : J → ℝ => ENNReal.ofReal (Real.exp (lam * ∑ j, c j * r j))) (stdGaussPi J) :=
    (Real.measurable_exp.comp ((measurable_linear c).const_mul lam)).ennreal_ofReal.aemeasurable
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_lintegral_div hmeas (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top).trans ?_
  rw [lintegral_exp_linear, ← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  calc lam ^ 2 * (∑ j, c j ^ 2) / 2 - lam * a ≤ lam ^ 2 * V / 2 - lam * a := by gcongr
    _ = -(a ^ 2 / (2 * V)) := by
      rw [hlam_def]
      field_simp
      ring

end Chernoff

section Bilinear

variable {ι : Type*} [Fintype ι]

/-- The sesquilinear form `w* G v = Σ_a Σ_b conj(w_a) G_ab v_b`. -/
def bil (w v : ι → ℂ) (G : Matrix ι ι ℂ) : ℂ :=
  ∑ a, ∑ b, G a b * v b * star (w a)

/-- Coefficients of `Re(w* G v)` in the real Gaussian coordinates `r((a,b),k)`. -/
def gueCoef (t : ℝ≥0) (w v : ι → ℂ) (j : (ι × ι) × Fin 2) : ℝ :=
  Real.sqrt ((t : ℝ) / 2) / Real.sqrt 2 *
    (if j.2 = 0 then (conj (w j.1.1) * v j.1.2).re + (conj (w j.1.2) * v j.1.1).re
      else (conj (w j.1.2) * v j.1.1).im - (conj (w j.1.1) * v j.1.2).im)

theorem re_bil_gueSample (t : ℝ≥0) (w v : ι → ℂ) (r : ((ι × ι) × Fin 2) → ℝ) :
    (bil w v (gueSample t (circularBrownianCoordinates r))).re =
      ∑ j, gueCoef t w v j * r j := by
  set X := circularBrownianCoordinates r
  have key : ∀ a b, gueSample t X a b * v b * star (w a) =
      (Real.sqrt ((t : ℝ) / 2) : ℂ) * X (a, b) * v b * star (w a) +
        (Real.sqrt ((t : ℝ) / 2) : ℂ) * conj (X (b, a)) * v b * star (w a) := by
    intro a b
    simp only [gueSample, Matrix.of_apply]
    ring
  have hswap : ∑ a, ∑ b,
      ((Real.sqrt ((t : ℝ) / 2) : ℂ) * conj (X (b, a)) * v b * star (w a)).re =
      ∑ a, ∑ b, ((Real.sqrt ((t : ℝ) / 2) : ℂ) * conj (X (a, b)) * v a * star (w b)).re :=
    Finset.sum_comm
  simp only [bil, key, Complex.re_sum, Complex.add_re, Finset.sum_add_distrib]
  rw [hswap, ← Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fin.sum_univ_two]
  simp only [gueCoef, X, circularBrownianCoordinates, Complex.star_def, Fin.isValue,
    ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, Complex.neg_re, Complex.neg_im,
    Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofReal_re,
    Complex.div_ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, map_div₀,
    map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem sum_gueCoef_sq_le (t : ℝ≥0) (w v : ι → ℂ) :
    ∑ j, gueCoef t w v j ^ 2 ≤
      (t : ℝ) * (∑ a, Complex.normSq (w a)) * (∑ b, Complex.normSq (v b)) := by
  set κ : ℝ := Real.sqrt ((t : ℝ) / 2) / Real.sqrt 2
  have hκ : κ ^ 2 = (t : ℝ) / 4 := by
    rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
    ring
  have hpt : ∀ a b, gueCoef t w v ((a, b), 0) ^ 2 + gueCoef t w v ((a, b), 1) ^ 2 ≤
      (t : ℝ) / 2 * (Complex.normSq (w a) * Complex.normSq (v b) +
        Complex.normSq (w b) * Complex.normSq (v a)) := by
    intro a b
    have hA : Complex.normSq (w a) * Complex.normSq (v b) =
        (conj (w a) * v b).re ^ 2 + (conj (w a) * v b).im ^ 2 := by
      rw [← Complex.normSq_conj (w a), ← map_mul, Complex.normSq_apply]
      ring
    have hB : Complex.normSq (w b) * Complex.normSq (v a) =
        (conj (w b) * v a).re ^ 2 + (conj (w b) * v a).im ^ 2 := by
      rw [← Complex.normSq_conj (w b), ← map_mul, Complex.normSq_apply]
      ring
    rw [hA, hB]
    simp only [gueCoef, Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one]
    set p := (conj (w a) * v b).re
    set p' := (conj (w a) * v b).im
    set q := (conj (w b) * v a).re
    set q' := (conj (w b) * v a).im
    have e : (κ * (p + q)) ^ 2 + (κ * (q' - p')) ^ 2 =
        κ ^ 2 * ((p + q) ^ 2 + (q' - p') ^ 2) := by ring
    rw [e, hκ]
    have ht : (0 : ℝ) ≤ t := t.2
    nlinarith [mul_nonneg ht (sq_nonneg (p - q)), mul_nonneg ht (sq_nonneg (q' + p'))]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  calc ∑ a, ∑ b, ∑ k : Fin 2, gueCoef t w v ((a, b), k) ^ 2
      ≤ ∑ a, ∑ b, (t : ℝ) / 2 * (Complex.normSq (w a) * Complex.normSq (v b) +
          Complex.normSq (w b) * Complex.normSq (v a)) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [Fin.sum_univ_two]
        exact hpt a b
    _ = (t : ℝ) / 2 * (∑ a, ∑ b, Complex.normSq (w a) * Complex.normSq (v b)) +
          (t : ℝ) / 2 * (∑ a, ∑ b, Complex.normSq (w b) * Complex.normSq (v a)) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ = (t : ℝ) * (∑ a, Complex.normSq (w a)) * (∑ b, Complex.normSq (v b)) := by
        have h1 : ∑ a, ∑ b, Complex.normSq (w a) * Complex.normSq (v b) =
            (∑ a, Complex.normSq (w a)) * (∑ b, Complex.normSq (v b)) :=
          (Finset.sum_mul_sum _ _ _ _).symm
        have h2 : ∑ a, ∑ b, Complex.normSq (w b) * Complex.normSq (v a) =
            (∑ a, Complex.normSq (w a)) * (∑ b, Complex.normSq (v b)) := by
          rw [Finset.sum_comm]
          exact (Finset.sum_mul_sum _ _ _ _).symm
        rw [h1, h2]
        ring

omit [Fintype ι] in
theorem continuous_gueSample' (t : ℝ≥0) : Continuous (gueSample (ι := ι) t) := by
  refine continuous_matrix fun a b => ?_
  simp only [gueSample, Matrix.of_apply]
  fun_prop

omit [Fintype ι] in
theorem continuous_circularBrownianCoordinates' :
    Continuous (circularBrownianCoordinates (ι := ι)) := by
  refine continuous_pi fun u => ?_
  simp only [circularBrownianCoordinates]
  fun_prop

theorem continuous_bil (w v : ι → ℂ) : Continuous fun G : Matrix ι ι ℂ => bil w v G := by
  unfold bil
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact ((continuous_id.matrix_elem a b).mul continuous_const).mul continuous_const

/-- **Gaussian tail of a fixed bilinear form of `GUE`.** -/
theorem gueMeasure_bil_tail (t : ℝ≥0) (w v : ι → ℂ) {a V : ℝ} (ha : 0 ≤ a) (hV : 0 < V)
    (hwv : (t : ℝ) * (∑ a, Complex.normSq (w a)) * (∑ b, Complex.normSq (v b)) ≤ V) :
    gueMeasure ι t {G | a < (bil w v G).re} ≤ ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * V)))) := by
  have hE : MeasurableSet {G : Matrix ι ι ℂ | a < (bil w v G).re} :=
    measurableSet_lt measurable_const
      (Complex.measurable_re.comp (continuous_bil w v).measurable)
  unfold gueMeasure commonCircularIncrementLaw
  rw [Measure.map_apply (continuous_gueSample' t).measurable hE,
    Measure.map_apply continuous_circularBrownianCoordinates'.measurable
      ((continuous_gueSample' t).measurable hE)]
  have hset : circularBrownianCoordinates ⁻¹' (gueSample t ⁻¹' {G | a < (bil w v G).re}) =
      {r | a < ∑ j, gueCoef t w v j * r j} := by
    ext r
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, re_bil_gueSample]
  rw [hset]
  exact stdGaussPi_tail _ ha hV ((sum_gueCoef_sq_le t w v).trans hwv)

end Bilinear

end BlockBand.DeterminantScore.GUENormTail
