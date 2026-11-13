module

public import BlockBand.DeterminantScore.SelectedIBPGradient

/-!
# Deterministic bounds and the fixed-energy tail of `Tr G R_η`

A step towards `SelectedResolvent.SelectedIBPStatement`, following the proof of the physical
real-loop proposition at deterministic exterior data, under the unweighted fresh prior
`G ~ GUE_ι(t)`:

* `integral_trace_mul_res_add`: `E Tr(G R) + t c² = -t E[(Tr R)² - c²]` for every `c ∈ ℂ`
  (centred form of `integral_trace_mul_res`; with `c = d m_E(iη)` and `t = s/d` the right side
  is `-s d⁻¹ E[(Tr R)² - d² m²]`, controlled by the averaged local law).
* `hsNorm_sub_le`, `hsNorm_mul_le`: Hilbert–Schmidt triangle inequality and
  `‖M N‖_HS ≤ c ‖N‖_HS` for `‖M v‖ ≤ c ‖v‖`.
* `hsNorm_gradMat_le`: `‖R - RGR‖_HS ≤ ‖R‖_HS (1 + ‖G‖/|η|)`.
* `eta_mul_hsNorm_res_sq` (Ward identity): `η ‖R‖²_HS = Im Tr R`.
* `measure_norm_lt_le_of_eLpNorm_le`: Markov at a real moment (complex values, outer measure).
* **`traceGRes_tail`**: from `Inputs.GaussianLpGradient`, one absolute `C₀` with
  `P(‖Tr(G R) + t c²‖ > u + t ‖E[(Tr R)² - c²]‖) ≤ (C₀ √p M / u)^p` for every `L^p` bound `M`
  of `√t ‖R - RGR‖_HS`.

The only input is `Inputs.GaussianLpGradient` (hypothesis of `traceGRes_tail` only).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SelectedIBP

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess
open scoped NNReal ComplexConjugate

variable {ι : Type} [Fintype ι] [DecidableEq ι]

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

/-- **Centred form of the IBP identity**: for every `c`,
`E Tr(G R) + t c² = -t E[(Tr R)² - c²]`; with `c = d m_E(iη)` this is the form used in the
proof of the physical real-loop proposition. -/
theorem integral_trace_mul_res_add {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {η : ℝ} (hη : η ≠ 0)
    (t : ℝ≥0) (c : ℂ) :
    (∫ G, (G * res K η G).trace ∂gueMeasure ι t) + (t : ℂ) * c ^ 2 =
      -(t : ℂ) * ∫ G, ((res K η G).trace ^ 2 - c ^ 2) ∂gueMeasure ι t := by
  have hI : Integrable (fun G => (res K η G).trace ^ 2) (gueMeasure ι t) := by
    rw [gueMeasure_eq_map_gueLin]
    have hm : Measurable fun G : Matrix ι ι ℂ => (res K η G).trace ^ 2 := by
      simp only [Matrix.trace, Matrix.diag]
      exact (Finset.measurable_sum _ fun a _ => (measurable_pi_apply a).comp
        ((measurable_pi_apply a).comp (measurable_res K η))).pow_const 2
    refine (integrable_map_measure hm.aestronglyMeasurable
      (continuous_gueLin t).aemeasurable).2 ?_
    have hb : ∀ x : GCoord ι → ℝ, ‖(res K η (gueLin t x)).trace ^ 2‖ ≤
        ((Fintype.card ι : ℝ) * |η|⁻¹) ^ 2 := by
      intro x
      rw [norm_pow]
      have : ‖(res K η (gueLin t x)).trace‖ ≤ (Fintype.card ι : ℝ) * |η|⁻¹ := by
        simp only [Matrix.trace, Matrix.diag]
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_sum fun a _ =>
          norm_res_apply_le (hK.add (isHermitian_gueLin t x)) hη a a).trans (le_of_eq ?_)
        simp
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    exact Integrable.of_bound (hm.comp (continuous_gueLin t).measurable).aestronglyMeasurable _
      (ae_of_all _ hb)
  rw [integral_trace_mul_res hK hη t, integral_sub hI (integrable_const _), integral_const]
  simp only [probReal_univ, one_smul]
  ring

/-- Hilbert–Schmidt norm as a Euclidean norm on `ι × ι`. -/
theorem hsNorm_eq_norm (B : Matrix ι ι ℂ) :
    hsNorm B = ‖(WithLp.toLp 2 (fun q : ι × ι => B q.1 q.2) : EuclideanSpace ℂ (ι × ι))‖ := by
  rw [EuclideanSpace.norm_eq, hsNorm, Fintype.sum_prod_type]

theorem hsNorm_nonneg (B : Matrix ι ι ℂ) : 0 ≤ hsNorm B := Real.sqrt_nonneg _

theorem hsNorm_sub_le (B B' : Matrix ι ι ℂ) : hsNorm (B - B') ≤ hsNorm B + hsNorm B' := by
  simp only [hsNorm_eq_norm]
  have : (WithLp.toLp 2 (fun q : ι × ι => (B - B') q.1 q.2) : EuclideanSpace ℂ (ι × ι)) =
      WithLp.toLp 2 (fun q : ι × ι => B q.1 q.2) - WithLp.toLp 2 (fun q : ι × ι => B' q.1 q.2) := by
    rfl
  rw [this]; exact norm_sub_le _ _

/-- `‖M N‖_HS ≤ c ‖N‖_HS` when `‖M v‖ ≤ c ‖v‖` (column by column). -/
theorem hsNorm_mul_le {M N : Matrix ι ι ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hM : ∀ v, ‖T M v‖ ≤ c * ‖v‖) : hsNorm (M * N) ≤ c * hsNorm N := by
  have key : ∀ b, ∑ a, ‖(M * N) a b‖ ^ 2 ≤ c ^ 2 * ∑ a, ‖N a b‖ ^ 2 := by
    intro b
    set v : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun a => N a b)
    have h1 : ‖T M v‖ ^ 2 = ∑ a, ‖(M * N) a b‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 2
    have h2 : ‖v‖ ^ 2 = ∑ a, ‖N a b‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq]
    rw [← h1, ← h2, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hM v) 2
  have hS : ∑ a, ∑ b, ‖(M * N) a b‖ ^ 2 ≤ c ^ 2 * ∑ a, ∑ b, ‖N a b‖ ^ 2 := by
    rw [Finset.sum_comm, Finset.sum_comm (f := fun a b => ‖N a b‖ ^ 2), Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => key b
  rw [hsNorm, hsNorm, ← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt hS

/-- **Deterministic gradient bound**: if `‖G v‖ ≤ c_G ‖v‖` and `K + G` is
Hermitian, `‖R - RGR‖_HS ≤ ‖R‖_HS (1 + c_G/|η|)`. -/
theorem hsNorm_gradMat_le {K G : Matrix ι ι ℂ} (hKG : (K + G).IsHermitian) {η : ℝ} (hη : η ≠ 0)
    {cG : ℝ} (hcG : 0 ≤ cG) (hG : ∀ v, ‖T G v‖ ≤ cG * ‖v‖) :
    hsNorm (gradMat K η G) ≤ hsNorm (res K η G) * (1 + cG / |η|) := by
  have hR : ∀ v, ‖T (res K η G) v‖ ≤ |η|⁻¹ * ‖v‖ := fun v => by
    have := BlockBand.LocalWindow.ProofCertificate.norm_resolvent_le hKG
      (z := (η : ℂ) * Complex.I) (by rw [im_eta_I]; exact hη) v
    rwa [im_eta_I] at this
  have hη0 : 0 ≤ |η|⁻¹ := inv_nonneg.mpr (abs_nonneg η)
  have h1 : hsNorm (res K η G * G * res K η G) ≤ |η|⁻¹ * (cG * hsNorm (res K η G)) := by
    rw [Matrix.mul_assoc]
    exact (hsNorm_mul_le hη0 hR).trans (mul_le_mul_of_nonneg_left (hsNorm_mul_le hcG hG) hη0)
  refine (hsNorm_sub_le _ _).trans ?_
  have : |η|⁻¹ * (cG * hsNorm (res K η G)) = hsNorm (res K η G) * (cG / |η|) := by
    rw [div_eq_mul_inv]; ring
  rw [mul_add, mul_one, ← this]
  exact add_le_add le_rfl h1

/-- **Ward identity**: `η ‖R‖²_HS = Im Tr R` for `R = (K + G - iη)⁻¹`, `K + G`
Hermitian, `η ≠ 0`. -/
theorem eta_mul_hsNorm_res_sq {K G : Matrix ι ι ℂ} (hKG : (K + G).IsHermitian) {η : ℝ}
    (hη : η ≠ 0) : η * hsNorm (res K η G) ^ 2 = (res K η G).trace.im := by
  set A := K + G - ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) with hA
  set R := res K η G with hRdef
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr (det_res_ne_zero hKG hη)
  have hRA : R * A = 1 := Matrix.nonsing_inv_mul A hu
  have hAR : A * R = 1 := Matrix.mul_nonsing_inv A hu
  have hAh : Aᴴ = K + G - (-((η : ℂ) * Complex.I)) • (1 : Matrix ι ι ℂ) := by
    rw [hA, conjTranspose_sub, hKG.eq, conjTranspose_smul, conjTranspose_one]
    congr 2
    simp [Complex.star_def, Complex.conj_ofReal]
  have h1 : Aᴴ * Rᴴ = 1 := by rw [← conjTranspose_mul, hRA, conjTranspose_one]
  have hdiff : Aᴴ - A = ((2 * η : ℝ) * Complex.I : ℂ) • (1 : Matrix ι ι ℂ) := by
    rw [hAh, hA]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [Matrix.one_apply]; ring
    · simp [hab, Matrix.one_apply]
  have hRR : R - Rᴴ = ((2 * η : ℝ) * Complex.I : ℂ) • (R * Rᴴ) := by
    have : R * (Aᴴ - A) * Rᴴ = R - Rᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h1, Matrix.mul_one, hRA,
        Matrix.one_mul]
    rw [← this, hdiff, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have htr := congrArg Matrix.trace hRR
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_conjTranspose] at htr
  have hS : (R * Rᴴ).trace = ((hsNorm R ^ 2 : ℝ) : ℂ) := by
    rw [hsNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      sq_nonneg _)]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply]
    push_cast
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  rw [hS] at htr
  have him := congrArg Complex.im htr
  simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, smul_eq_mul, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_re] at him
  linarith

/-- **Markov at a real moment** for a complex `f` (outer measure). -/
theorem measure_norm_lt_le_of_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℂ) {q u K : ℝ} (hq : 0 < q) (hu : 0 < u) (hK : 0 ≤ K)
    (h : eLpNorm f (ENNReal.ofReal q) μ ≤ ENNReal.ofReal K) :
    μ {x | u < ‖f x‖} ≤ ENNReal.ofReal ((K / u) ^ q) := by
  have hq0 : ENNReal.ofReal q ≠ 0 := by simp [hq]
  have hM := mul_meas_ge_le_pow_eLpNorm' μ hq0 ENNReal.ofReal_ne_top (f := f)
    (ENNReal.ofReal u)
  rw [ENNReal.toReal_ofReal hq.le] at hM
  have hsub : {x | u < ‖f x‖} ⊆ {x | ENNReal.ofReal u ≤ ‖f x‖ₑ} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hx.le
  have h2 : ENNReal.ofReal u ^ q * μ {x | u < ‖f x‖} ≤ ENNReal.ofReal K ^ q :=
    (mul_le_mul_right (measure_mono hsub) _).trans
      (hM.trans (ENNReal.rpow_le_rpow h hq.le))
  rw [ENNReal.ofReal_rpow_of_nonneg hu.le hq.le, ENNReal.ofReal_rpow_of_nonneg hK hq.le] at h2
  have hup : 0 < u ^ q := Real.rpow_pos_of_pos hu q
  rw [Real.div_rpow hK hu.le, ENNReal.ofReal_div_of_pos hup]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [hup])) (Or.inl ENNReal.ofReal_ne_top),
    mul_comm]
  exact h2

/-- **The fixed-energy `Tr G R` tail** (at deterministic exterior data): from
`Inputs.GaussianLpGradient`, one absolute `C₀ > 0` such that for every `p ≥ 1`, finite
`ι`, Hermitian `K`, `η ≠ 0`, `t`, `c ∈ ℂ`, `u > 0` and every `L^p` bound `M` on the gradient
`√t ‖R - RGR‖_HS` (standard coordinates), under `G ~ GUE_ι(t)`:
`P(‖Tr(G R) + t c²‖ > u + t ‖E[(Tr R)² - c²]‖) ≤ (C₀ √p M / u)^p`. With `c = d m_E(iη)` the
expectation term is the local-law input and `M` is controlled by the Ward identity
`eta_mul_hsNorm_res_sq` and `hsNorm_gradMat_le`. -/
theorem traceGRes_tail (hLp : BlockBand.Internal.Contracts.Inputs.GaussianLpGradient) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ p : ℝ, 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (K : Matrix ι ι ℂ), K.IsHermitian → ∀ η : ℝ, η ≠ 0 → ∀ (t : ℝ≥0) (c : ℂ) (u M : ℝ),
        0 < u → 0 ≤ M →
        eLpNorm (fun x => Real.sqrt t * hsNorm (gradMat K η (gueLin t x)))
            (ENNReal.ofReal p) (stdGauss ι) ≤ ENNReal.ofReal M →
        gueMeasure ι t {G | u + (t : ℝ) *
            ‖∫ G', ((res K η G').trace ^ 2 - c ^ 2) ∂gueMeasure ι t‖ <
              ‖(G * res K η G).trace + (t : ℂ) * c ^ 2‖} ≤
          ENNReal.ofReal ((C₀ * Real.sqrt p * M / u) ^ p) := by
  obtain ⟨C₀, hC₀, hconc⟩ := traceGRes_concentration hLp
  refine ⟨C₀, hC₀, fun p hp ι _ _ K hK η hη t c u M hu hM hgrad => ?_⟩
  have hentry : ∀ a b : ι, Measurable fun G : Matrix ι ι ℂ => res K η G a b := fun a b =>
    (measurable_pi_apply b).comp ((measurable_pi_apply a).comp (measurable_res K η))
  have hmeas1 : Measurable fun G : Matrix ι ι ℂ => (G * res K η G).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ =>
      (show Measurable fun G : Matrix ι ι ℂ => G a b from
        (measurable_pi_apply b).comp (measurable_pi_apply a)).mul (hentry b a)
  set ex := ∫ G', ((res K η G').trace ^ 2 - c ^ 2) ∂gueMeasure ι t
  set EX := ∫ y, traceGRes K η t y ∂stdGauss ι
  have hEX : EX + (t : ℂ) * c ^ 2 = -(t : ℂ) * ex := by
    have h := integral_trace_mul_res_add hK hη t c
    rw [gueMeasure_eq_map_gueLin, integral_map (continuous_gueLin t).aemeasurable
      hmeas1.aestronglyMeasurable] at h
    rw [← gueMeasure_eq_map_gueLin] at h
    exact h
  have hset : MeasurableSet {G : Matrix ι ι ℂ | u + (t : ℝ) * ‖ex‖ <
      ‖(G * res K η G).trace + (t : ℂ) * c ^ 2‖} :=
    measurableSet_lt measurable_const ((hmeas1.add measurable_const).norm)
  rw [gueMeasure_eq_map_gueLin, Measure.map_apply (continuous_gueLin t).measurable hset]
  have hsub : gueLin t ⁻¹' {G : Matrix ι ι ℂ | u + (t : ℝ) * ‖ex‖ <
      ‖(G * res K η G).trace + (t : ℂ) * c ^ 2‖} ⊆
      {x | u < ‖traceGRes K η t x - EX‖} := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hx ⊢
    have h1 : (gueLin t x * res K η (gueLin t x)).trace + (t : ℂ) * c ^ 2 =
        (traceGRes K η t x - EX) + (-(t : ℂ) * ex) := by
      rw [← hEX, traceGRes]; ring
    rw [h1] at hx
    have h2 : ‖-(t : ℂ) * ex‖ = (t : ℝ) * ‖ex‖ := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg t)]
    have := norm_add_le (traceGRes K η t x - EX) (-(t : ℂ) * ex)
    linarith
  refine (measure_mono hsub).trans ?_
  have hK0 : 0 ≤ C₀ * Real.sqrt p * M := by positivity
  refine measure_norm_lt_le_of_eLpNorm_le _ _ (by linarith) hu hK0 ?_
  refine (hconc p hp ι K hK η hη t).trans ?_
  refine (mul_le_mul_right hgrad _).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]

end BlockBand.DeterminantScore.SelectedIBP
