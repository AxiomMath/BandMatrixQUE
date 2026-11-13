module

public import BlockBand.Endpoints.Sine.FlowAdmissionShifted
public import BlockBand.Endpoints.Sine.FlowAdmissionGirsanov

/-!
# The scalar shift of a GUE matrix (Gaussian likelihood)

In the shifted Palm step of the proof of the flow-admission lemma, the shift `H ↦ H + aP_S` is a
shift `G ↦ G + aI` of the fresh pair Gaussian `G ~ GUE_𝒩(t)`. This file proves the exact
likelihood of a scalar shift of `CoareaPalm.gueMeasure ι t` (`√(t/2)(X + Xᴴ)`, `X` standard
circular), for every finite index type `ι` and `t > 0`:

`∫ φ(G + cI) dGUE_ι(t) = ∫ ρ_c(G) φ(G) dGUE_ι(t)`, `ρ_c(G) = exp((c Re Tr G - |ι| c²/2)/t)`
(`fap_lintegral_gue_shift`), for every measurable `φ ≥ 0` and real `c`.

Only the `|ι|` real diagonal coordinates move: `G_aa = √t r_{(a,a),0}` with `r` standard real
Gaussian coordinates, and `G + cI` is the sample at `r + (c/√t)1_{diag}`; the coordinate
likelihood is `fa_withDensity_ratio`. No hypothesis.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess
open scoped ENNReal NNReal ComplexConjugate

section GUEShift

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The likelihood `ρ_c(G) = exp((c Re Tr G - |ι| c²/2)/t)` of `G + cI` against `GUE_ι(t)`. -/
def fap_gueDensity (t : ℝ≥0) (c : ℝ) (G : Matrix ι ι ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp ((c * G.trace.re - (Fintype.card ι : ℝ) * c ^ 2 / 2) / t))

omit [DecidableEq ι] in
theorem fap_measurable_gueDensity (t : ℝ≥0) (c : ℝ) :
    Measurable (fap_gueDensity (ι := ι) t c) := by
  unfold fap_gueDensity
  have h : Continuous fun G : Matrix ι ι ℂ => G.trace.re :=
    Complex.continuous_re.comp (continuous_id.matrix_trace)
  exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
    (((measurable_const.mul h.measurable).sub measurable_const).div_const _))

omit [Fintype ι] [DecidableEq ι] in
theorem fap_measurable_circular :
    Measurable (circularBrownianCoordinates (ι := ι)) := by
  refine Measurable.of_eval fun u => ?_
  unfold circularBrownianCoordinates
  exact ((Complex.measurable_ofReal.comp (measurable_pi_apply _)).add
    ((Complex.measurable_ofReal.comp (measurable_pi_apply _)).mul measurable_const)).div_const _

omit [Fintype ι] [DecidableEq ι] in
theorem fap_measurable_gueSample (t : ℝ≥0) : Measurable (gueSample (ι := ι) t) := by
  rw [Matrix.measurable_iff]
  intro a b
  unfold gueSample
  simp only [Matrix.of_apply]
  fun_prop

/-- The coordinate shift `(c/√t) 1_{(a,a),0}`. -/
def fap_coordShift (t : ℝ≥0) (c : ℝ) : ((ι × ι) × Fin 2) → ℝ :=
  fun k => if k.1.1 = k.1.2 ∧ k.2 = 0 then c / Real.sqrt t else 0

/-- The flat GUE sample map `r ↦ √(t/2)(X + Xᴴ)`, `X = (r_0 + i r_1)/√2`. -/
def fap_sample (t : ℝ≥0) (r : ((ι × ι) × Fin 2) → ℝ) : Matrix ι ι ℂ :=
  gueSample t (circularBrownianCoordinates r)

omit [Fintype ι] [DecidableEq ι] in
theorem fap_measurable_sample (t : ℝ≥0) : Measurable (fap_sample (ι := ι) t) :=
  (fap_measurable_gueSample t).comp fap_measurable_circular

theorem fap_sqrt_half_mul (t : ℝ≥0) :
    Real.sqrt ((t : ℝ) / 2) * (2 / Real.sqrt 2) = Real.sqrt t := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

omit [Fintype ι] in
/-- `G(r + m) = G(r) + cI`. -/
theorem fap_sample_shift (t : ℝ≥0) (ht : t ≠ 0) (c : ℝ) (r : ((ι × ι) × Fin 2) → ℝ) :
    fap_sample t (r + fap_coordShift t c) = fap_sample t r + (c : ℂ) • 1 := by
  have hts : Real.sqrt t ≠ 0 := by
    have : (0 : ℝ) < t := lt_of_le_of_ne t.2 (fun h => ht (NNReal.coe_eq_zero.mp h.symm))
    positivity
  have key := fap_sqrt_half_mul t
  ext a b
  simp only [fap_sample, gueSample, circularBrownianCoordinates, fap_coordShift, Matrix.of_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Pi.add_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    simp only [and_true, ite_true, true_and, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.div_re, Complex.conj_re, Complex.I_re, Complex.I_im, Complex.add_im,
        Complex.mul_im, Complex.normSq_ofReal, Complex.conj_im, Complex.div_im]
      have h2 : Real.sqrt 2 ≠ 0 := by positivity
      have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
      linear_combination (-(Real.sqrt t * Real.sqrt 2 * c)) * h22
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.div_re, Complex.conj_re, Complex.I_re, Complex.I_im, Complex.add_im,
        Complex.mul_im, Complex.normSq_ofReal, Complex.conj_im, Complex.div_im]
      ring
  · have hba : ¬ b = a := fun h => hab h.symm
    simp [hab, hba]

omit [DecidableEq ι] in
/-- `Re Tr G(r) = √t Σ_a r_{(a,a),0}`. -/
theorem fap_trace_sample (t : ℝ≥0) (r : ((ι × ι) × Fin 2) → ℝ) :
    (fap_sample t r).trace.re = Real.sqrt t * ∑ a : ι, r ((a, a), 0) := by
  have key := fap_sqrt_half_mul t
  simp only [fap_sample, Matrix.trace, Matrix.diag, gueSample, circularBrownianCoordinates,
    Matrix.of_apply, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.div_re, Complex.conj_re, Complex.I_re, Complex.I_im, Complex.add_im,
    Complex.mul_im, Complex.normSq_ofReal, Complex.conj_im, Complex.div_im]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  linear_combination (-(Real.sqrt t * Real.sqrt 2 * r ((a, a), 0))) * h22

/-- The standard real coordinate law. -/
abbrev fap_coordLaw (ι : Type*) [Fintype ι] : Measure (((ι × ι) × Fin 2) → ℝ) :=
  Measure.pi fun _ : (ι × ι) × Fin 2 => gaussianReal 0 1

/-- The coordinate likelihood `∏_k exp(m_k r_k - m_k²/2)`. -/
def fap_coordDensity (t : ℝ≥0) (c : ℝ) (r : ((ι × ι) × Fin 2) → ℝ) : ℝ≥0∞ :=
  ∏ k, fa_ratio (fap_coordShift t c k) 1 (r k)

theorem fap_measurable_coordDensity (t : ℝ≥0) (c : ℝ) :
    Measurable (fap_coordDensity (ι := ι) t c) := by
  unfold fap_coordDensity
  exact Finset.measurable_prod _ fun k _ =>
    (fa_measurable_ratio _ _).comp (measurable_pi_apply k)

/-- `Law(r + m) = ∏_k ratio_k · Law(r)`. -/
theorem fap_map_coordShift (t : ℝ≥0) (c : ℝ) :
    (fap_coordLaw ι).map (fun r => r + fap_coordShift t c) =
      (fap_coordLaw ι).withDensity (fap_coordDensity t c) := by
  classical
  have hmap : (fun r : ((ι × ι) × Fin 2) → ℝ => r + fap_coordShift t c) =
      fun r k => (fun y : ℝ => y + fap_coordShift t c k) (r k) := by
    funext r k; rfl
  have : ∀ k : (ι × ι) × Fin 2, SigmaFinite ((gaussianReal 0 1).map
      (fun y : ℝ => y + fap_coordShift t c k)) := fun k => by
    rw [gaussianReal_map_add_const]; infer_instance
  rw [hmap, Measure.pi_map_pi (fun k => (measurable_add_const _).aemeasurable)]
  simp_rw [gaussianReal_map_add_const, zero_add]
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator
    (MeasurableSet.univ_pi hs)]
  have hind : (Set.univ.pi s).indicator (fap_coordDensity t c) = fun r =>
      ∏ k, (s k).indicator (fa_ratio (fap_coordShift t c k) 1) (r k) := by
    funext r
    by_cases hr : r ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hr]
      unfold fap_coordDensity
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [Set.indicator_of_mem (hr k (Set.mem_univ k))]
    · rw [Set.indicator_of_notMem hr]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hr
      obtain ⟨k, hk⟩ := hr
      exact (Finset.prod_eq_zero (Finset.mem_univ k) (Set.indicator_of_notMem hk _)).symm
  rw [hind]
  have hmeas : ∀ k, Measurable ((s k).indicator (fa_ratio (fap_coordShift t c k) 1)) :=
    fun k => (fa_measurable_ratio _ _).indicator (hs k)
  refine (lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun k (r : ((ι × ι) × Fin 2) → ℝ) => (s k).indicator
      (fa_ratio (fap_coordShift t c k) 1) (r k))
    (iIndepFun_pi fun k => (hmeas k).aemeasurable)
    (fun k => (hmeas k).comp (measurable_pi_apply k))).trans ?_
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [(measurePreserving_eval (fun _ : (ι × ι) × Fin 2 => gaussianReal 0 1) k).lintegral_comp
      (hmeas k), lintegral_indicator (hs k), ← withDensity_apply _ (hs k),
    fa_withDensity_ratio _ one_ne_zero]

/-- The coordinate likelihood is the matrix likelihood of the sample. -/
theorem fap_coordDensity_eq (t : ℝ≥0) (ht : t ≠ 0) (c : ℝ) (r : ((ι × ι) × Fin 2) → ℝ) :
    fap_coordDensity t c r = fap_gueDensity t c (fap_sample t r) := by
  have htpos : (0 : ℝ) < t := lt_of_le_of_ne t.2 (fun h => ht (NNReal.coe_eq_zero.mp h.symm))
  have hts : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  unfold fap_coordDensity fa_ratio fap_gueDensity
  rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ => (Real.exp_pos _).le), ← Real.exp_sum,
    fap_trace_sample]
  congr 2
  have hsum : ∑ k : (ι × ι) × Fin 2,
      (fap_coordShift t c k * r k - fap_coordShift t c k ^ 2 / 2) / ((1 : ℝ≥0) : ℝ) =
      c / Real.sqrt t * ∑ a : ι, r ((a, a), 0) -
        (Fintype.card ι : ℝ) * (c / Real.sqrt t) ^ 2 / 2 := by
    simp only [NNReal.coe_one, div_one, Fintype.sum_prod_type, Fin.sum_univ_two, fap_coordShift,
      and_true, one_ne_zero, and_false, ite_false, zero_mul, sub_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero]
    have h1 : ∀ a : ι, (∑ b : ι, ((if a = b then c / Real.sqrt t else 0) * r ((a, b), 0) -
        (if a = b then c / Real.sqrt t else 0) ^ 2 / 2)) =
        c / Real.sqrt t * r ((a, a), 0) - (c / Real.sqrt t) ^ 2 / 2 := by
      intro a
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hsum]
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt htpos.le
  field_simp
  rw [hsq]
  ring

/-- **Scalar shift of `GUE_ι(t)`**: `∫ φ(G + cI) dGUE = ∫ ρ_c(G) φ(G) dGUE` for every
measurable `φ ≥ 0`, real `c` and `t > 0`. -/
theorem fap_lintegral_gue_shift (t : ℝ≥0) (ht : t ≠ 0) (c : ℝ) {φ : Matrix ι ι ℂ → ℝ≥0∞}
    (hφ : Measurable φ) :
    ∫⁻ G, φ (G + (c : ℂ) • 1) ∂gueMeasure ι t =
      ∫⁻ G, fap_gueDensity t c G * φ G ∂gueMeasure ι t := by
  have hgue : gueMeasure ι t = (fap_coordLaw ι).map (fap_sample t) := by
    unfold gueMeasure commonCircularIncrementLaw
    rw [Measure.map_map (fap_measurable_gueSample t) fap_measurable_circular]
    rfl
  have hφs : Measurable fun G : Matrix ι ι ℂ => φ (G + (c : ℂ) • 1) :=
    hφ.comp (measurable_id.add_const _)
  have hρφ : Measurable fun G : Matrix ι ι ℂ => fap_gueDensity t c G * φ G :=
    (fap_measurable_gueDensity t c).mul hφ
  rw [hgue, lintegral_map hφs (fap_measurable_sample t), lintegral_map hρφ (fap_measurable_sample t)]
  have h1 : ∀ r, φ (fap_sample t r + (c : ℂ) • 1) = (φ ∘ fap_sample t) (r + fap_coordShift t c) :=
    fun r => by rw [Function.comp_apply, fap_sample_shift t ht c r]
  simp_rw [h1]
  rw [← lintegral_map (hφ.comp (fap_measurable_sample t)) (measurable_add_const _),
    fap_map_coordShift, lintegral_withDensity_eq_lintegral_mul _ (fap_measurable_coordDensity t c)
      (hφ.comp (fap_measurable_sample t))]
  refine lintegral_congr fun r => ?_
  simp only [Pi.mul_apply, Function.comp_apply, fap_coordDensity_eq t ht c r]

end GUEShift

end BlockBand.Endpoints
