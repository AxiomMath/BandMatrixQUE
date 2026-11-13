module

public import BlockBand.Layers.ResidualSplitLaw
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Gaussian trace splitting of `GUE_ι(t)`

* `cib_gue_traceless_trace`: the joint law of `(G⁰, Re Tr G / d)`, where
  `G⁰ = tracelessPart G = G - (Tr G / d) I`, is the product of the law of `G⁰` and
  `N(0, t/d)`.
* `cib_gue_indep_traceless_trace`, `cib_gue_trace_hasLaw`: the two corollaries (independence and
  the scalar law `N(0, t/d)`).
* `cib_gueSample_isHermitian`, `cib_gue_ae_isHermitian`: `GUE` samples are Hermitian.

Proof: on the standard real coordinates `r` (i.i.d. `N(0,1)`) the matrix is linear in `r`; the
trace is `√t` times the mean `m(r)` of the diagonal real coordinates, and `G⁰` is the same
linear image of the centred coordinates `r - m(r) e_diag`. The pair `(m, r - m e_diag)` is
jointly Gaussian and uncorrelated, hence independent (Mathlib
`HasGaussianLaw.indepFun_of_covariance_eval`), and `m ~ N(0, 1/d)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.SourceProcess (commonCircularIncrementLaw circularBrownianCoordinates)
open BlockBand.Layers (rslScale rsl_scale_sq rsl_gueSample_re rsl_gueSample_im
  rsl_gueMeasure_eq_map rsl_measurable_gueSample rsl_measurable_cbc)
open scoped ENNReal NNReal ComplexConjugate

/-!
## 1. Standard real coordinates
-/

section Coordinates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard Gaussian law of the real circular coordinates `r : (ι × ι) × Fin 2 → ℝ`. -/
abbrev cibStd (ι : Type*) [Fintype ι] : Measure ((ι × ι) × Fin 2 → ℝ) :=
  Measure.pi fun _ : (ι × ι) × Fin 2 => gaussianReal 0 (1 : ℝ≥0)

omit [DecidableEq ι] in
/-- Mean of the diagonal real coordinates, `m(r) = d⁻¹ Σ_a r((a,a),0)`. -/
def cibMean (r : (ι × ι) × Fin 2 → ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ a, r ((a, a), 0)

/-- Centred coordinates: the diagonal real coordinates minus their mean, others unchanged. -/
def cibCenter (r : (ι × ι) × Fin 2 → ℝ) : (ι × ι) × Fin 2 → ℝ :=
  fun k => r k - if k.1.1 = k.1.2 ∧ k.2 = 0 then cibMean r else 0

omit [DecidableEq ι] in
theorem cib_hasLaw_coord (k : (ι × ι) × Fin 2) :
    HasLaw (fun r : (ι × ι) × Fin 2 → ℝ => r k) (gaussianReal 0 (1 : ℝ≥0)) (cibStd ι) :=
  (measurePreserving_eval (fun _ : (ι × ι) × Fin 2 => gaussianReal 0 (1 : ℝ≥0)) k).hasLaw

omit [DecidableEq ι] in
theorem cib_memLp_coord (k : (ι × ι) × Fin 2) :
    MemLp (fun r : (ι × ι) × Fin 2 → ℝ => r k) 2 (cibStd ι) :=
  (cib_hasLaw_coord k).hasGaussianLaw.memLp_two

omit [DecidableEq ι] in
theorem cib_iIndepFun_coord :
    iIndepFun (fun (k : (ι × ι) × Fin 2) (r : (ι × ι) × Fin 2 → ℝ) => r k) (cibStd ι) :=
  iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem cib_cov_coord (k l : (ι × ι) × Fin 2) :
    cov[fun r : (ι × ι) × Fin 2 → ℝ => r k, fun r => r l; cibStd ι] =
      if k = l then 1 else 0 := by
  by_cases h : k = l
  · subst h
    rw [covariance_self (measurable_pi_apply k).aemeasurable, (cib_hasLaw_coord k).variance_eq,
      variance_id_gaussianReal]
    simp
  · rw [(cib_iIndepFun_coord.indepFun h).covariance_eq_zero (cib_memLp_coord k)
      (cib_memLp_coord l)]
    simp [h]

omit [DecidableEq ι] in
theorem cib_hasGaussianLaw_id :
    HasGaussianLaw (fun r : (ι × ι) × Fin 2 → ℝ => r) (cibStd ι) :=
  iIndepFun.hasGaussianLaw (fun k => (cib_hasLaw_coord k).hasGaussianLaw) cib_iIndepFun_coord

omit [DecidableEq ι] in
/-- `cibMean` as a continuous linear functional. -/
def cibMeanCLM : ((ι × ι) × Fin 2 → ℝ) →L[ℝ] ℝ :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ a, ContinuousLinearMap.proj ((a, a), 0)

omit [DecidableEq ι] in
theorem cibMeanCLM_apply (r : (ι × ι) × Fin 2 → ℝ) : cibMeanCLM r = cibMean r := by
  simp [cibMeanCLM, cibMean]

/-- `cibCenter` as a continuous linear map. -/
def cibCenterCLM : ((ι × ι) × Fin 2 → ℝ) →L[ℝ] ((ι × ι) × Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun k =>
    ContinuousLinearMap.proj k - if k.1.1 = k.1.2 ∧ k.2 = 0 then cibMeanCLM else 0

theorem cibCenterCLM_apply (r : (ι × ι) × Fin 2 → ℝ) : cibCenterCLM r = cibCenter r := by
  funext k
  simp only [cibCenterCLM, cibCenter, ContinuousLinearMap.pi_apply,
    _root_.sub_apply, ContinuousLinearMap.proj_apply]
  split_ifs <;> simp [cibMeanCLM_apply]

/-- Joint map `r ↦ (m(r), r - m(r) e_diag)`, the scalar as a `Unit`-indexed family. -/
def cibJointCLM : ((ι × ι) × Fin 2 → ℝ) →L[ℝ] ((Unit → ℝ) × ((ι × ι) × Fin 2 → ℝ)) :=
  (ContinuousLinearMap.pi fun _ : Unit => cibMeanCLM).prod cibCenterCLM

theorem cib_hasGaussianLaw_joint :
    HasGaussianLaw (fun r : (ι × ι) × Fin 2 → ℝ => ((fun _ : Unit => cibMean r), cibCenter r))
      (cibStd ι) := by
  have h := cib_hasGaussianLaw_id.map_fun (cibJointCLM (ι := ι))
  simpa [cibJointCLM, cibMeanCLM_apply, cibCenterCLM_apply] using h

omit [DecidableEq ι] in
theorem cib_memLp_mean : MemLp (cibMean (ι := ι)) 2 (cibStd ι) := by
  have h := cib_hasGaussianLaw_id.map_fun (cibMeanCLM (ι := ι))
  simp only [cibMeanCLM_apply] at h
  exact h.memLp_two

theorem cib_cov_mean_coord (l : (ι × ι) × Fin 2) :
    cov[cibMean, fun r : (ι × ι) × Fin 2 → ℝ => r l; cibStd ι] =
      if l.1.1 = l.1.2 ∧ l.2 = 0 then (Fintype.card ι : ℝ)⁻¹ else 0 := by
  have hm : (cibMean (ι := ι)) = fun r => (Fintype.card ι : ℝ)⁻¹ * ∑ a, r ((a, a), 0) := rfl
  rw [hm, covariance_const_mul_left, covariance_fun_sum_left
    (X := fun a (r : (ι × ι) × Fin 2 → ℝ) => r ((a, a), 0)) (fun a => cib_memLp_coord _)
    (cib_memLp_coord l)]
  simp only [cib_cov_coord]
  obtain ⟨⟨b, c⟩, j⟩ := l
  by_cases h : b = c ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have h' : ¬(((b, c), j).1.1 = ((b, c), j).1.2 ∧ ((b, c), j).2 = 0) := h
    simp only [h', ite_false]
    rw [Finset.sum_eq_zero, mul_zero]
    intro a _
    have hk : ¬(((a, a), (0 : Fin 2)) = ((b, c), j)) := by
      intro hk
      simp only [Prod.mk.injEq] at hk
      exact h ⟨hk.1.1.symm.trans hk.1.2, hk.2.symm⟩
    simp only [hk, ite_false]

theorem cib_var_mean [Nonempty ι] :
    cov[cibMean, cibMean; cibStd ι] = (Fintype.card ι : ℝ)⁻¹ := by
  change cov[cibMean, fun r => (Fintype.card ι : ℝ)⁻¹ * ∑ a, r ((a, a), 0); cibStd ι] = _
  rw [covariance_const_mul_right, covariance_fun_sum_right
    (X := fun a (r : (ι × ι) × Fin 2 → ℝ) => r ((a, a), 0)) (fun a => cib_memLp_coord _)
    cib_memLp_mean]
  simp only [cib_cov_mean_coord, and_self, ite_true, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have hd : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  field_simp

theorem cib_cov_mean_center (k : (ι × ι) × Fin 2) :
    cov[cibMean, fun r : (ι × ι) × Fin 2 → ℝ => cibCenter r k; cibStd ι] = 0 := by
  by_cases h : k.1.1 = k.1.2 ∧ k.2 = 0
  · have hc : (fun r : (ι × ι) × Fin 2 → ℝ => cibCenter r k) = fun r => r k - cibMean r := by
      funext r
      simp [cibCenter, h]
    rw [hc, covariance_fun_sub_right cib_memLp_mean (cib_memLp_coord k) cib_memLp_mean,
      cib_cov_mean_coord]
    have : Nonempty ι := ⟨k.1.1⟩
    simp only [h, and_self, ite_true]
    rw [cib_var_mean, sub_self]
  · have hc : (fun r : (ι × ι) × Fin 2 → ℝ => cibCenter r k) = fun r => r k := by
      funext r
      simp [cibCenter, h]
    rw [hc, cib_cov_mean_coord]
    simp only [h, ite_false]

/-- Independence of the centred coordinates and the diagonal mean under the standard law. -/
theorem cib_indep_center_mean :
    IndepFun (cibCenter (ι := ι)) cibMean (cibStd ι) := by
  have h := cib_hasGaussianLaw_joint.indepFun_of_covariance_eval
    (X := fun (_ : Unit) (r : (ι × ι) × Fin 2 → ℝ) => cibMean r)
    (Y := fun k (r : (ι × ι) × Fin 2 → ℝ) => cibCenter r k)
    (fun (_ : Unit) k => cib_cov_mean_center k)
  exact (h.comp (measurable_pi_apply ()) measurable_id).symm

omit [DecidableEq ι] in
theorem cib_integral_mean : ∫ r, cibMean r ∂cibStd ι = 0 := by
  simp only [cibMean]
  rw [integral_const_mul, integral_finsetSum _ fun a _ => (cib_memLp_coord _).integrable
    one_le_two]
  simp [(cib_hasLaw_coord _).integral_eq, integral_id_gaussianReal]

/-- The scalar `2 rslScale(t) = √t` multiplying the diagonal mean. -/
def cibTraceScale (t : ℝ≥0) : ℝ := 2 * rslScale t

theorem cib_traceScale_sq (t : ℝ≥0) : cibTraceScale t ^ 2 = (t : ℝ) := by
  rw [cibTraceScale, mul_pow, rsl_scale_sq]
  ring

omit [DecidableEq ι] in
/-- Law of the scaled diagonal mean: `N(0, t/d)`. -/
theorem cib_map_scaled_mean [Nonempty ι] (t : ℝ≥0) :
    (cibStd ι).map (fun r => cibTraceScale t * cibMean r) =
      gaussianReal 0 (t / (Fintype.card ι : ℝ≥0)) := by
  classical
  have hG : HasGaussianLaw (cibMean (ι := ι)) (cibStd ι) := by
    have h := cib_hasGaussianLaw_id.map_fun (cibMeanCLM (ι := ι))
    simpa only [cibMeanCLM_apply] using h
  have hmeas : Measurable (cibMean (ι := ι)) := by
    have : cibMean (ι := ι) = fun r => cibMeanCLM r := funext fun r => (cibMeanCLM_apply r).symm
    rw [this]
    exact (cibMeanCLM (ι := ι)).continuous.measurable
  change (cibStd ι).map ((fun x => cibTraceScale t * x) ∘ cibMean) = _
  rw [← Measure.map_map (measurable_const_mul (cibTraceScale t)) hmeas, hG.map_eq_gaussianReal,
    gaussianReal_map_const_mul, cib_integral_mean, mul_zero, ← covariance_self hmeas.aemeasurable,
    cib_var_mean]
  congr 1
  ext
  simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ (inv_nonneg.mpr (Nat.cast_nonneg _)),
    NNReal.coe_div, NNReal.coe_natCast, cib_traceScale_sq]
  ring

end Coordinates

/-!
## 2. The GUE matrix in standard coordinates
-/

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem cib_trace_gueSample (t : ℝ≥0) (r : (ι × ι) × Fin 2 → ℝ) :
    (gueSample t (circularBrownianCoordinates r)).trace =
      ((cibTraceScale t * ∑ a, r ((a, a), 0) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Matrix.trace, Matrix.diag, Complex.re_sum, rsl_gueSample_re, Complex.ofReal_re,
      Finset.mul_sum, cibTraceScale]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  · simp [Matrix.trace, Matrix.diag, Complex.im_sum, rsl_gueSample_im]

omit [DecidableEq ι] in
theorem cib_traceRe_gueSample (t : ℝ≥0) (r : (ι × ι) × Fin 2 → ℝ) :
    (gueSample t (circularBrownianCoordinates r)).trace.re / (Fintype.card ι : ℝ) =
      cibTraceScale t * cibMean r := by
  rw [cib_trace_gueSample, Complex.ofReal_re, cibMean]
  ring

theorem cib_tracelessPart_gueSample (t : ℝ≥0) (r : (ι × ι) × Fin 2 → ℝ) :
    tracelessPart (gueSample t (circularBrownianCoordinates r)) =
      gueSample t (circularBrownianCoordinates (cibCenter r)) := by
  have hs : ((Fintype.card ι : ℂ))⁻¹ * (gueSample t (circularBrownianCoordinates r)).trace =
      ((cibTraceScale t * cibMean r : ℝ) : ℂ) := by
    rw [cib_trace_gueSample, cibMean]
    push_cast
    ring
  ext a b
  rw [tracelessPart, hs]
  apply Complex.ext
  · rw [rsl_gueSample_re]
    by_cases hab : a = b
    · subst hab
      simp [rsl_gueSample_re, cibCenter, cibTraceScale]
      ring
    · simp [rsl_gueSample_re, hab, cibCenter, Ne.symm hab]
  · rw [rsl_gueSample_im]
    simp [rsl_gueSample_im, Matrix.one_apply, cibCenter]
    split_ifs <;> simp

theorem cib_measurable_tracelessPart : Measurable (tracelessPart (ι := ι)) := by
  have hc : Continuous (tracelessPart (ι := ι)) := by
    unfold tracelessPart
    exact continuous_id.sub ((continuous_const.mul continuous_id.matrix_trace).smul
      continuous_const)
  exact hc.measurable

omit [DecidableEq ι] in
theorem cib_measurable_traceRe :
    Measurable (fun G : Matrix ι ι ℂ => G.trace.re / (Fintype.card ι : ℝ)) := by
  have hc : Continuous (fun G : Matrix ι ι ℂ => G.trace.re / (Fintype.card ι : ℝ)) :=
    (Complex.continuous_re.comp continuous_id.matrix_trace).div_const _
  exact hc.measurable

end Matrix

/-!
## 3. The splitting law
-/

section Split

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The real normalized trace of `GUE_ι(t)` has law `N(0, t/d)`. -/
theorem cib_gue_map_trace [Nonempty ι] (t : ℝ≥0) :
    (gueMeasure ι t).map (fun G => G.trace.re / (Fintype.card ι : ℝ)) =
      gaussianReal 0 (t / (Fintype.card ι : ℝ≥0)) := by
  have hF : Measurable (fun r : (ι × ι) × Fin 2 → ℝ =>
      gueSample t (circularBrownianCoordinates r)) :=
    (rsl_measurable_gueSample t).comp rsl_measurable_cbc
  rw [rsl_gueMeasure_eq_map, Measure.map_map cib_measurable_traceRe hF, ← cib_map_scaled_mean t]
  congr 1
  funext r
  exact cib_traceRe_gueSample t r

/-- **Trace splitting of `GUE_ι(t)`**: the traceless part `G - (d⁻¹ Tr G) I` and the real
normalized trace `Re Tr G / d` are independent, and the latter is `N(0, t/d)`, `d = card ι`. -/
theorem cib_gue_traceless_trace [Nonempty ι] (t : ℝ≥0) :
    (gueMeasure ι t).map (fun G => (tracelessPart G, G.trace.re / (Fintype.card ι : ℝ))) =
      ((gueMeasure ι t).map tracelessPart).prod
        (gaussianReal 0 (t / (Fintype.card ι : ℝ≥0))) := by
  set F : ((ι × ι) × Fin 2 → ℝ) → Matrix ι ι ℂ :=
    fun r => gueSample t (circularBrownianCoordinates r) with hFdef
  have hF : Measurable F := (rsl_measurable_gueSample t).comp rsl_measurable_cbc
  have hc : Measurable (fun x : ℝ => cibTraceScale t * x) := measurable_const_mul _
  have hCen : Measurable (cibCenter (ι := ι)) := by
    have : cibCenter (ι := ι) = fun r => cibCenterCLM r :=
      funext fun r => (cibCenterCLM_apply r).symm
    rw [this]
    exact (cibCenterCLM (ι := ι)).continuous.measurable
  have hMean : Measurable (cibMean (ι := ι)) := by
    have : cibMean (ι := ι) = fun r => cibMeanCLM r := funext fun r => (cibMeanCLM_apply r).symm
    rw [this]
    exact (cibMeanCLM (ι := ι)).continuous.measurable
  have hpair : (fun G : Matrix ι ι ℂ => (tracelessPart G, G.trace.re / (Fintype.card ι : ℝ))) ∘ F =
      Prod.map F (fun x => cibTraceScale t * x) ∘ (fun r => (cibCenter r, cibMean r)) := by
    funext r
    simp only [Function.comp_apply, Prod.map_apply, hFdef, cib_tracelessPart_gueSample,
      cib_traceRe_gueSample]
  have hind := (indepFun_iff_map_prod_eq_prod_map_map hCen.aemeasurable
    hMean.aemeasurable).1 cib_indep_center_mean
  have htp : (gueMeasure ι t).map tracelessPart = ((cibStd ι).map cibCenter).map F := by
    rw [rsl_gueMeasure_eq_map, Measure.map_map cib_measurable_tracelessPart hF,
      Measure.map_map hF hCen]
    congr 1
    funext r
    exact cib_tracelessPart_gueSample t r
  have hgauss : gaussianReal 0 (t / (Fintype.card ι : ℝ≥0)) =
      ((cibStd ι).map cibMean).map (fun x => cibTraceScale t * x) := by
    rw [Measure.map_map hc hMean, ← cib_map_scaled_mean t]
    rfl
  rw [htp, hgauss, Measure.map_prod_map _ _ hF hc, ← hind,
    Measure.map_map (hF.prodMap hc) (hCen.prodMk hMean), ← hpair, rsl_gueMeasure_eq_map,
    Measure.map_map (cib_measurable_tracelessPart.prodMk cib_measurable_traceRe) hF]

/-- Independence of the traceless part and the real normalized trace under `GUE_ι(t)`. -/
theorem cib_gue_indep_traceless_trace [Nonempty ι] (t : ℝ≥0) :
    IndepFun tracelessPart (fun G : Matrix ι ι ℂ => G.trace.re / (Fintype.card ι : ℝ))
      (gueMeasure ι t) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map cib_measurable_tracelessPart.aemeasurable
    cib_measurable_traceRe.aemeasurable, cib_gue_map_trace t]
  exact cib_gue_traceless_trace t

omit [DecidableEq ι] in
/-- The real normalized trace of `GUE_ι(t)` has law `N(0, t/d)`. -/
theorem cib_gue_trace_hasLaw [Nonempty ι] (t : ℝ≥0) :
    HasLaw (fun G : Matrix ι ι ℂ => G.trace.re / (Fintype.card ι : ℝ))
      (gaussianReal 0 (t / (Fintype.card ι : ℝ≥0))) (gueMeasure ι t) :=
  ⟨cib_measurable_traceRe.aemeasurable, cib_gue_map_trace t⟩

end Split

/-!
## 4. Hermitian samples
-/

/-- Every `GUE` sample `√(t/2)(X + Xᴴ)` is Hermitian. -/
theorem cib_gueSample_isHermitian {ι : Type*} (t : ℝ≥0) (X : ι × ι → ℂ) :
    (gueSample t X).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, gueSample, Matrix.of_apply, star_mul', star_add,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  ring

/-- `GUE_ι(t)` is supported on Hermitian matrices. -/
theorem cib_gue_ae_isHermitian {ι : Type*} [Fintype ι] (t : ℝ≥0) :
    ∀ᵐ G ∂gueMeasure ι t, G.IsHermitian := by
  have hS : MeasurableSet {G : Matrix ι ι ℂ | G.IsHermitian} := by
    have hc : Continuous (fun G : Matrix ι ι ℂ => Gᴴ) := continuous_id.matrix_conjTranspose
    exact (isClosed_eq hc continuous_id).measurableSet
  rw [gueMeasure, ae_map_iff (rsl_measurable_gueSample t).aemeasurable hS]
  exact Filter.Eventually.of_forall fun X => cib_gueSample_isHermitian t X

end BlockBand.Center
