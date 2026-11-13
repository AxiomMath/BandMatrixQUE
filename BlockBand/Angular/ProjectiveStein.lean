module

public import BlockBand.Angular.ConeDivergenceComplex
public import BlockBand.Angular.DegreeZero

/-!
# Projective Stein identities for linear fields

For a complex matrix `B` and a real function `f` on `ℂ^ι`, the field `z ↦ f(z) B z` has
real divergence `Df(z)[Bz] + 2 f(z) Re Tr B` (`realDivergence_smul_mulVec`). With the Gaussian
divergence identity this gives, under the circular Gaussian law,
`E[Df(z)[Bz]] = 2 E[f(z) Re(z*Bz)] - 2 Re Tr B · E[f]` (`integral_fderiv_mulVec`), and, for
`f` invariant under positive scaling (Euler: `Df(z)[z] = 0`),
`E[‖z‖² f] = N E[f]` (`integral_mul_normSq`). These are the integrations by parts on the
sphere used in the angular comparison, with the projective Haar measure obtained from
`integral_projectiveHaar_eq_of_scaleInvariant`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.ProjectiveStein

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.ConeDivergence
open BlockBand.Angular.DegreeZero
open scoped ENNReal NNReal ComplexConjugate

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `z ↦ B z` as a continuous real-linear map. -/
def mulVecCLM (B : Matrix ι ι ℂ) : (ι → ℂ) →L[ℝ] (ι → ℂ) :=
  (LinearMap.toContinuousLinearMap (Matrix.mulVecLin B)).restrictScalars ℝ

theorem mulVecCLM_apply (B : Matrix ι ι ℂ) (z : ι → ℂ) : mulVecCLM B z = B *ᵥ z := rfl

/-- Real-coordinate expansion of a complex vector. -/
theorem vec_eq_sum_coordDir (w : ι → ℂ) :
    w = ∑ a, ((w a).re • (Pi.single a 1 : ι → ℂ) + (w a).im • (Pi.single a Complex.I : ι → ℂ)) := by
  funext b
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
  rw [Finset.sum_eq_single b (fun a _ hab => by simp [Ne.symm hab]) (by simp)]
  simp

/-- The derivative of a real function along a complex vector, in real coordinates. -/
theorem fderiv_apply_eq_sum (L : (ι → ℂ) →L[ℝ] ℝ) (w : ι → ℂ) :
    L w = ∑ a, (L (Pi.single a 1) * (w a).re + L (Pi.single a Complex.I) * (w a).im) := by
  conv_lhs => rw [vec_eq_sum_coordDir w]
  simp [map_sum, map_add, map_smul, smul_eq_mul, mul_comm]

/-- **Divergence of `f · Bz`**: `div(f B·)(z) = Df(z)[Bz] + 2 f(z) Re Tr B`. -/
theorem realDivergence_smul_mulVec (f : (ι → ℂ) → ℝ) (B : Matrix ι ι ℂ) (z : ι → ℂ)
    (hf : DifferentiableAt ℝ f z) :
    realDivergence (fun x => (f x : ℂ) • (B *ᵥ x)) z =
      fderiv ℝ f z (B *ᵥ z) + 2 * f z * (B.trace).re := by
  have h1 : HasFDerivAt (fun x => (f x : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ f z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hf.hasFDerivAt
  have h2 : HasFDerivAt (fun x => B *ᵥ x) (mulVecCLM B) z := (mulVecCLM B).hasFDerivAt
  have hY : HasFDerivAt (fun x => (f x : ℂ) • (B *ᵥ x))
      ((f z : ℂ) • mulVecCLM B + (Complex.ofRealCLM.comp (fderiv ℝ f z)).smulRight (B *ᵥ z)) z :=
    h1.smul h2
  rw [realDivergence, hY.fderiv, fderiv_apply_eq_sum (fderiv ℝ f z) (B *ᵥ z), trace,
    Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, mulVecCLM_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mulVec_single, diag_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- **Euler's identity** for a function invariant under positive scaling. -/
theorem fderiv_apply_self_eq_zero (h : (ι → ℂ) → ℝ) (z : ι → ℂ) (hd : DifferentiableAt ℝ h z)
    (hinv : ∀ r : ℝ, 0 < r → h (r • z) = h z) : fderiv ℝ h z z = 0 := by
  have hline : HasDerivAt (fun t : ℝ => (1 + t) • z) z 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_add 1).smul_const z
    simpa using this
  have hcomp : HasDerivAt (fun t : ℝ => h ((1 + t) • z)) (fderiv ℝ h z z) 0 := by
    have hD : HasFDerivAt h (fderiv ℝ h z) ((1 + (0 : ℝ)) • z) := by simpa using hd.hasFDerivAt
    exact hD.comp_hasDerivAt (0 : ℝ) hline
  have hconst : (fun t : ℝ => h ((1 + t) • z)) =ᶠ[nhds 0] fun _ => h z := by
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with t ht
    exact hinv (1 + t) (by simp at ht; linarith)
  exact (hcomp.congr_of_eventuallyEq hconst.symm).unique (hasDerivAt_const 0 (h z))

theorem norm_mulVecCLM_apply_le (B : Matrix ι ι ℂ) (z : ι → ℂ) :
    ‖B *ᵥ z‖ ≤ ‖mulVecCLM B‖ * ‖z‖ :=
  (mulVecCLM B).le_opNorm z

/-- **Gaussian Stein identity for a linear field.** Under the circular Gaussian law, for a
Borel `f` that is differentiable off the origin with `|f| ≤ M` and `‖Df(z)‖ ‖z‖ ≤ M`:
`E[Df(z)[Bz]] = 2 E[f(z) Re(z*Bz)] - 2 Re Tr B · E[f]`. -/
theorem integral_fderiv_mulVec [Nonempty ι] (f : (ι → ℂ) → ℝ) (B : Matrix ι ι ℂ) (M : ℝ)
    (hfm : Measurable f) (hd : ∀ z, z ≠ 0 → DifferentiableAt ℝ f z) (hb : ∀ z, |f z| ≤ M)
    (hdb : ∀ z, z ≠ 0 → ‖fderiv ℝ f z‖ * ‖z‖ ≤ M) :
    (∫ z, fderiv ℝ f z (B *ᵥ z) ∂circularVectorLaw ι) =
      2 * (∫ z, f z * (∑ a, conj (z a) * (B *ᵥ z) a).re ∂circularVectorLaw ι) -
        2 * (B.trace).re * ∫ z, f z ∂circularVectorLaw ι := by
  set L := mulVecCLM B
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb 0)
  have hYm : Measurable (fun x : ι → ℂ => (f x : ℂ) • (B *ᵥ x)) :=
    (Complex.measurable_ofReal.comp hfm).smul L.continuous.measurable
  have hYd : ∀ z, z ≠ 0 → DifferentiableAt ℝ (fun x : ι → ℂ => (f x : ℂ) • (B *ᵥ x)) z :=
    fun z hz => ((Complex.ofRealCLM.differentiableAt).comp z (hd z hz)).smul
      L.differentiableAt
  have hYg : ∀ z, ‖(f z : ℂ) • (B *ᵥ z)‖ ≤ (M * ‖L‖) * ‖z‖ := by
    intro z
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul (hb z) (norm_mulVecCLM_apply_le B z) (norm_nonneg _) hM
  have hYb : ∀ z, z ≠ 0 →
      ‖fderiv ℝ (fun x : ι → ℂ => (f x : ℂ) • (B *ᵥ x)) z‖ ≤ 2 * M * ‖L‖ := by
    intro z hz
    have h1 : HasFDerivAt (fun x => (f x : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ f z)) z :=
      Complex.ofRealCLM.hasFDerivAt.comp z (hd z hz).hasFDerivAt
    have hY : HasFDerivAt (fun x => (f x : ℂ) • (B *ᵥ x))
        ((f z : ℂ) • L + (Complex.ofRealCLM.comp (fderiv ℝ f z)).smulRight (B *ᵥ z)) z :=
      h1.smul L.hasFDerivAt
    rw [hY.fderiv]
    calc _ ≤ ‖(f z : ℂ) • L‖ + ‖(Complex.ofRealCLM.comp (fderiv ℝ f z)).smulRight (B *ᵥ z)‖ :=
          norm_add_le _ _
      _ ≤ M * ‖L‖ + ‖fderiv ℝ f z‖ * (‖L‖ * ‖z‖) := by
          gcongr
          · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right (hb z) (norm_nonneg _)
          · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
            rw [ContinuousLinearMap.smulRight_apply, norm_smul,
              ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real]
            calc ‖fderiv ℝ f z w‖ * ‖B *ᵥ z‖ ≤ (‖fderiv ℝ f z‖ * ‖w‖) * (‖L‖ * ‖z‖) :=
                  mul_le_mul ((fderiv ℝ f z).le_opNorm w) (norm_mulVecCLM_apply_le B z)
                    (norm_nonneg _) (by positivity)
              _ = ‖fderiv ℝ f z‖ * (‖L‖ * ‖z‖) * ‖w‖ := by ring
      _ ≤ 2 * M * ‖L‖ := by
          have := hdb z hz
          nlinarith [norm_nonneg L]
  have key := integral_realDivergence_eq (fun x : ι → ℂ => (f x : ℂ) • (B *ᵥ x))
    (2 * M * ‖L‖) hYm hYd
    (fun z => (hYg z).trans (mul_le_mul_of_nonneg_right
      (by nlinarith [norm_nonneg L, hM]) (norm_nonneg z))) hYb
  have hprob : IsProbabilityMeasure (circularVectorLaw ι) := by
    rw [circularVectorLaw_eq]; infer_instance
  have hDm : Measurable (fun z : ι → ℂ => fderiv ℝ f z (B *ᵥ z)) := by
    have : (fun z : ι → ℂ => fderiv ℝ f z (B *ᵥ z)) = fun z => ∑ a,
        (fderiv ℝ f z (Pi.single a 1) * ((B *ᵥ z) a).re +
          fderiv ℝ f z (Pi.single a Complex.I) * ((B *ᵥ z) a).im) := by
      funext z; exact fderiv_apply_eq_sum _ _
    rw [this]
    refine Finset.measurable_sum _ fun a _ => ?_
    exact ((measurable_fderiv_apply_const ℝ f _).mul
      (Complex.measurable_re.comp ((measurable_pi_apply a).comp L.continuous.measurable))).add
      ((measurable_fderiv_apply_const ℝ f _).mul
      (Complex.measurable_im.comp ((measurable_pi_apply a).comp L.continuous.measurable)))
  have hDi : Integrable (fun z : ι → ℂ => fderiv ℝ f z (B *ᵥ z)) (circularVectorLaw ι) := by
    refine (integrable_const (M * ‖L‖)).mono' hDm.aestronglyMeasurable ?_
    filter_upwards [ae_circular_ne_zero] with z hz
    rw [Real.norm_eq_abs]
    calc |fderiv ℝ f z (B *ᵥ z)| ≤ ‖fderiv ℝ f z‖ * ‖B *ᵥ z‖ := by
          rw [← Real.norm_eq_abs]; exact (fderiv ℝ f z).le_opNorm _
      _ ≤ ‖fderiv ℝ f z‖ * (‖L‖ * ‖z‖) :=
          mul_le_mul_of_nonneg_left (norm_mulVecCLM_apply_le B z) (norm_nonneg _)
      _ = (‖fderiv ℝ f z‖ * ‖z‖) * ‖L‖ := by ring
      _ ≤ M * ‖L‖ := mul_le_mul_of_nonneg_right (hdb z hz) (norm_nonneg _)
  have hfi : Integrable f (circularVectorLaw ι) :=
    (integrable_const M).mono' hfm.aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hb z)
  have hlhs : (∫ z, realDivergence (fun x : ι → ℂ => (f x : ℂ) • (B *ᵥ x)) z
        ∂circularVectorLaw ι) =
      (∫ z, fderiv ℝ f z (B *ᵥ z) ∂circularVectorLaw ι) +
        2 * (B.trace).re * ∫ z, f z ∂circularVectorLaw ι := by
    rw [← integral_const_mul, ← integral_add hDi (hfi.const_mul _)]
    apply integral_congr_ae
    filter_upwards [ae_circular_ne_zero] with z hz
    rw [realDivergence_smul_mulVec f B z (hd z hz)]
    ring
  have hrhs : ∀ z : ι → ℂ, (∑ a, conj (z a) * ((f z : ℂ) • (B *ᵥ z)) a).re =
      f z * (∑ a, conj (z a) * (B *ᵥ z) a).re := by
    intro z
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (∑ a, conj (z a) * ((f z : ℂ) * (B *ᵥ z) a)) =
        (f z : ℂ) * ∑ a, conj (z a) * (B *ᵥ z) a by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring]
    exact Complex.re_ofReal_mul _ _
  simp_rw [hrhs] at key
  rw [hlhs] at key
  linarith

/-- **Radial identity.** For a Borel `h` invariant under positive scaling, differentiable off
the origin with `|h| ≤ M` and `‖Dh(z)‖ ‖z‖ ≤ M`, `E[h(z) Σ_a |z_a|²] = N E[h]` under the
circular Gaussian law (`N = card ι`). -/
theorem integral_mul_normSq [Nonempty ι] (h : (ι → ℂ) → ℝ) (M : ℝ) (hm : Measurable h)
    (hd : ∀ z, z ≠ 0 → DifferentiableAt ℝ h z) (hb : ∀ z, |h z| ≤ M)
    (hdb : ∀ z, z ≠ 0 → ‖fderiv ℝ h z‖ * ‖z‖ ≤ M)
    (hinv : ∀ z (r : ℝ), 0 < r → h (r • z) = h z) :
    (∫ z, h z * ∑ a, ‖z a‖ ^ 2 ∂circularVectorLaw ι) =
      (Fintype.card ι : ℝ) * ∫ z, h z ∂circularVectorLaw ι := by
  have key := integral_fderiv_mulVec h 1 M hm hd hb hdb
  have h0 : (∫ z, fderiv ℝ h z ((1 : Matrix ι ι ℂ) *ᵥ z) ∂circularVectorLaw ι) = 0 := by
    rw [← integral_zero (ι → ℂ) ℝ]
    apply integral_congr_ae
    filter_upwards [ae_circular_ne_zero] with z hz
    rw [one_mulVec]
    exact fderiv_apply_self_eq_zero h z (hd z hz) (hinv z)
  have hre : ∀ z : ι → ℂ, (∑ a, conj (z a) * ((1 : Matrix ι ι ℂ) *ᵥ z) a).re =
      ∑ a, ‖z a‖ ^ 2 := by
    intro z
    rw [one_mulVec, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.conj_mul']
    norm_cast
  simp_rw [hre] at key
  rw [h0, trace_one] at key
  simp only [Complex.natCast_re] at key
  linarith

/-- `Σ_a |z_a|²`. -/
def normSqSum (z : ι → ℂ) : ℝ := ∑ a, ‖z a‖ ^ 2

/-- The Rayleigh quotient `Re(z* B z)/‖z‖²` (zero at the origin). -/
def quadQuot (B : Matrix ι ι ℂ) (z : ι → ℂ) : ℝ :=
  (∑ a, conj (z a) * (B *ᵥ z) a).re / normSqSum z

theorem normSqSum_pos {z : ι → ℂ} (hz : z ≠ 0) : 0 < normSqSum z := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hz
  exact lt_of_lt_of_le (by positivity : 0 < ‖z k‖ ^ 2)
    (Finset.single_le_sum (f := fun k => ‖z k‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ k))

theorem contDiff_normSqSum : ContDiff ℝ ⊤ (normSqSum (ι := ι)) := by
  unfold normSqSum
  exact ContDiff.sum fun a _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ a)

theorem contDiff_quadForm (B : Matrix ι ι ℂ) :
    ContDiff ℝ ⊤ (fun z : ι → ℂ => (∑ a, conj (z a) * (B *ᵥ z) a).re) := by
  have hB : ContDiff ℝ ⊤ (fun z : ι → ℂ => B *ᵥ z) := (mulVecCLM B).contDiff
  refine Complex.reCLM.contDiff.comp (ContDiff.sum fun a _ => ?_)
  exact ((Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
    (contDiff_apply ℝ ℂ a)).mul ((contDiff_apply ℝ ℂ a).comp hB)

theorem quadQuot_scale (B : Matrix ι ι ℂ) (z : ι → ℂ) {r : ℝ} (hr : 0 < r) :
    quadQuot B (r • z) = quadQuot B z := by
  unfold quadQuot normSqSum
  have h1 : (∑ a, conj ((r • z) a) * (B *ᵥ (r • z)) a).re =
      r ^ 2 * (∑ a, conj (z a) * (B *ᵥ z) a).re := by
    rw [← Complex.re_ofReal_mul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mulVec_smul]
    simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    push_cast; ring
  have h2 : (∑ a, ‖(r • z) a‖ ^ 2) = r ^ 2 * ∑ a, ‖z a‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hr]; ring
  rw [h1, h2]
  by_cases h0 : (∑ a, ‖z a‖ ^ 2) = 0
  · simp [h0]
  · field_simp

theorem contDiffOn_quadQuot (B : Matrix ι ι ℂ) :
    ContDiffOn ℝ 1 (quadQuot B) {z | z ≠ 0} := by
  unfold quadQuot
  exact ((contDiff_quadForm B).contDiffOn.of_le le_top).div
    (contDiff_normSqSum.contDiffOn.of_le le_top) fun z hz => (normSqSum_pos hz).ne'

theorem measurable_quadQuot (B : Matrix ι ι ℂ) : Measurable (quadQuot B) := by
  unfold quadQuot
  exact (contDiff_quadForm B).continuous.measurable.div contDiff_normSqSum.continuous.measurable

theorem complex_smul_eq_real_smul (r : ℝ) (z : ι → ℂ) : (r : ℂ) • z = r • z := by
  funext a; simp [Complex.real_smul]

/-- **Projective Stein identity for a linear field** (sphere integration by parts with the
field `v ↦ Bv`). For a Borel scale-invariant `f`, `C¹` off the origin, under the projective
Haar measure `ν_N` (`N = card ι`):
`ν_N[Df(v)[Bv]] = 2 ν_N[f(v) (N Re(v*Bv) - Re Tr B)]`, with `Re(v*Bv)` written as the
scale-invariant Rayleigh quotient `quadQuot B`. -/
theorem integral_projectiveHaar_fderiv_mulVec [Nonempty ι] (f : (ι → ℂ) → ℝ)
    (hfm : Measurable f) (hinv : IsScaleInvariant f) (hc : ContDiffOn ℝ 1 f {z | z ≠ 0})
    (B : Matrix ι ι ℂ) :
    (∫ z, fderiv ℝ f z (B *ᵥ z) ∂projectiveHaar ι) =
      2 * ∫ z, f z * ((Fintype.card ι : ℝ) * quadQuot B z - (B.trace).re) ∂projectiveHaar ι := by
  have hopen : IsOpen {z : ι → ℂ | z ≠ 0} := isOpen_ne
  have hd : ∀ z : ι → ℂ, z ≠ 0 → DifferentiableAt ℝ f z := fun z hz =>
    (hc.differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds hz)
  obtain ⟨M, hM, hMd⟩ := exists_bound_of_scaleInvariant hinv hc
  -- the product `f · q_B`
  set g : (ι → ℂ) → ℝ := fun z => f z * quadQuot B z with hg
  have hginv : IsScaleInvariant g := fun z r hr => by
    simp only [hg, hinv z r hr, quadQuot_scale B z hr]
  have hgc : ContDiffOn ℝ 1 g {z | z ≠ 0} := hc.mul (contDiffOn_quadQuot B)
  have hgm : Measurable g := hfm.mul (measurable_quadQuot B)
  obtain ⟨Mg, hMg, hMgd⟩ := exists_bound_of_scaleInvariant hginv hgc
  have hgd : ∀ z : ι → ℂ, z ≠ 0 → DifferentiableAt ℝ g z := fun z hz =>
    (hgc.differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds hz)
  have hprob : IsProbabilityMeasure (circularVectorLaw ι) := by
    rw [circularVectorLaw_eq]; infer_instance
  -- measurability of the derivative term
  have hDm : Measurable (fun z : ι → ℂ => fderiv ℝ f z (B *ᵥ z)) := by
    have : (fun z : ι → ℂ => fderiv ℝ f z (B *ᵥ z)) = fun z => ∑ a,
        (fderiv ℝ f z (Pi.single a 1) * ((B *ᵥ z) a).re +
          fderiv ℝ f z (Pi.single a Complex.I) * ((B *ᵥ z) a).im) := by
      funext z; exact fderiv_apply_eq_sum _ _
    rw [this]
    refine Finset.measurable_sum _ fun a _ => ?_
    exact ((measurable_fderiv_apply_const ℝ f _).mul
      (Complex.measurable_re.comp ((measurable_pi_apply a).comp
        (mulVecCLM B).continuous.measurable))).add
      ((measurable_fderiv_apply_const ℝ f _).mul
      (Complex.measurable_im.comp ((measurable_pi_apply a).comp
        (mulVecCLM B).continuous.measurable)))
  have hDinv : ∀ z (r : ℝ), 0 < r →
      fderiv ℝ f ((r : ℂ) • z) (B *ᵥ ((r : ℂ) • z)) = fderiv ℝ f z (B *ᵥ z) := by
    intro z r hr
    rw [complex_smul_eq_real_smul]
    by_cases hz : z = 0
    · simp [hz]
    rw [fderiv_smul_of_scaleInvariant hinv (hd z hz) hr, mulVec_smul]
    simp only [ContinuousLinearMap.map_smul, _root_.smul_apply, smul_eq_mul]
    field_simp
  -- The left side as an integral against the Gaussian law
  rw [integral_projectiveHaar_eq_of_scaleInvariant _ hDm hDinv]
  rw [integral_fderiv_mulVec f B M hfm hd hM hMd]
  -- The radial identity for g
  have hrad := integral_mul_normSq g Mg hgm hgd hMg hMgd hginv
  have hfq : ∀ᵐ z ∂circularVectorLaw ι,
      f z * (∑ a, conj (z a) * (B *ᵥ z) a).re = g z * ∑ a, ‖z a‖ ^ 2 := by
    filter_upwards [ae_circular_ne_zero] with z hz
    have hp := (normSqSum_pos hz).ne'
    simp only [hg, quadQuot]
    unfold normSqSum at hp ⊢
    field_simp
  rw [integral_congr_ae hfq, hrad]
  -- Back to the projective law
  have hRm : Measurable (fun z => f z * ((Fintype.card ι : ℝ) * quadQuot B z - (B.trace).re)) :=
    hfm.mul ((measurable_const.mul (measurable_quadQuot B)).sub measurable_const)
  rw [integral_projectiveHaar_eq_of_scaleInvariant _ hRm (fun z r hr => by
    rw [complex_smul_eq_real_smul, hinv z r hr, quadQuot_scale B z hr])]
  have hfi : Integrable f (circularVectorLaw ι) :=
    (integrable_const M).mono' hfm.aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hM z)
  have hgi : Integrable g (circularVectorLaw ι) :=
    (integrable_const Mg).mono' hgm.aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hMg z)
  have hsplit : (∫ z, f z * ((Fintype.card ι : ℝ) * quadQuot B z - (B.trace).re)
      ∂circularVectorLaw ι) =
      (Fintype.card ι : ℝ) * (∫ z, g z ∂circularVectorLaw ι) -
        (B.trace).re * ∫ z, f z ∂circularVectorLaw ι := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hgi.const_mul _)
      (hfi.const_mul _)]
    exact integral_congr_ae (ae_of_all _ fun z => by simp only [hg]; ring)
  rw [hsplit]
  ring

/-- **Projective Stein identity with a coefficient.** For Borel scale-invariant `c, f`, `C¹`
off the origin: `ν_N[c Df[Bv]] = 2 ν_N[c f (N Re(v*Bv) - Re Tr B)] - ν_N[f Dc[Bv]]`. This
covers every field of the form `Σ (degree-zero coefficient) × (linear field)`. -/
theorem integral_projectiveHaar_coeff_fderiv_mulVec [Nonempty ι] (c f : (ι → ℂ) → ℝ)
    (hcm : Measurable c) (hfm : Measurable f) (hcinv : IsScaleInvariant c)
    (hfinv : IsScaleInvariant f) (hcc : ContDiffOn ℝ 1 c {z | z ≠ 0})
    (hfc : ContDiffOn ℝ 1 f {z | z ≠ 0}) (B : Matrix ι ι ℂ) :
    (∫ z, c z * fderiv ℝ f z (B *ᵥ z) ∂projectiveHaar ι) =
      2 * (∫ z, c z * f z * ((Fintype.card ι : ℝ) * quadQuot B z - (B.trace).re)
        ∂projectiveHaar ι) - ∫ z, f z * fderiv ℝ c z (B *ᵥ z) ∂projectiveHaar ι := by
  have hopen : IsOpen {z : ι → ℂ | z ≠ 0} := isOpen_ne
  have hcf := integral_projectiveHaar_fderiv_mulVec (fun z => c z * f z) (hcm.mul hfm)
    (fun z r hr => by simp only [hcinv z r hr, hfinv z r hr]) (hcc.mul hfc) B
  obtain ⟨Mc, hMc, hMcd⟩ := exists_bound_of_scaleInvariant hcinv hcc
  obtain ⟨Mf, hMf, hMfd⟩ := exists_bound_of_scaleInvariant hfinv hfc
  have hprod : ∀ z : ι → ℂ, z ≠ 0 → fderiv ℝ (fun z => c z * f z) z (B *ᵥ z) =
      c z * fderiv ℝ f z (B *ᵥ z) + f z * fderiv ℝ c z (B *ᵥ z) := by
    intro z hz
    have hdc := (hcc.differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds hz)
    have hdf := (hfc.differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds hz)
    rw [fderiv_fun_mul hdc hdf]
    simp [smul_eq_mul]
  -- integrability on the projective law
  have hprobN : IsProbabilityMeasure (projectiveHaar ι) := by
    unfold projectiveHaar
    have hN : Measurable (fun g : ι → ℂ => ((l2Norm g)⁻¹ : ℂ) • g) :=
      ((Complex.measurable_ofReal.comp measurable_l2Norm).inv).smul measurable_id
    have : IsProbabilityMeasure (circularVectorLaw ι) := by
      rw [circularVectorLaw_eq]; infer_instance
    infer_instance
  have hne : ∀ᵐ z ∂projectiveHaar ι, z ≠ 0 := by
    unfold projectiveHaar
    have hN : Measurable (fun g : ι → ℂ => ((l2Norm g)⁻¹ : ℂ) • g) :=
      ((Complex.measurable_ofReal.comp measurable_l2Norm).inv).smul measurable_id
    have hs : MeasurableSet {g : ι → ℂ | g ≠ 0} := (measurableSet_singleton (0 : ι → ℂ)).compl
    rw [ae_map_iff hN.aemeasurable hs]
    filter_upwards [ae_circular_ne_zero] with g hg
    intro h0
    have := l2Norm_pos hg
    have hc0 : ((l2Norm g)⁻¹ : ℂ) ≠ 0 := by
      simpa using (inv_pos.2 this).ne'
    exact hg ((smul_eq_zero.1 h0).resolve_left hc0)
  have hDm : ∀ h : (ι → ℂ) → ℝ, Measurable (fun z : ι → ℂ => fderiv ℝ h z (B *ᵥ z)) := by
    intro h
    have : (fun z : ι → ℂ => fderiv ℝ h z (B *ᵥ z)) = fun z => ∑ a,
        (fderiv ℝ h z (Pi.single a 1) * ((B *ᵥ z) a).re +
          fderiv ℝ h z (Pi.single a Complex.I) * ((B *ᵥ z) a).im) := by
      funext z; exact fderiv_apply_eq_sum _ _
    rw [this]
    refine Finset.measurable_sum _ fun a _ => ?_
    exact ((measurable_fderiv_apply_const ℝ h _).mul
      (Complex.measurable_re.comp ((measurable_pi_apply a).comp
        (mulVecCLM B).continuous.measurable))).add
      ((measurable_fderiv_apply_const ℝ h _).mul
      (Complex.measurable_im.comp ((measurable_pi_apply a).comp
        (mulVecCLM B).continuous.measurable)))
  have hbd : ∀ (g h : (ι → ℂ) → ℝ) (Mg Mh : ℝ), Measurable g → (∀ z, |g z| ≤ Mg) →
      (∀ z, z ≠ 0 → ‖fderiv ℝ h z‖ * ‖z‖ ≤ Mh) →
      Integrable (fun z => g z * fderiv ℝ h z (B *ᵥ z)) (projectiveHaar ι) := by
    intro g h Mg Mh hg hgb hhb
    refine (integrable_const (Mg * (Mh * ‖mulVecCLM B‖))).mono'
      (hg.mul (hDm h)).aestronglyMeasurable ?_
    filter_upwards [hne] with z hz
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |fderiv ℝ h z (B *ᵥ z)| ≤ Mh * ‖mulVecCLM B‖ := by
      calc |fderiv ℝ h z (B *ᵥ z)| ≤ ‖fderiv ℝ h z‖ * ‖B *ᵥ z‖ := by
            rw [← Real.norm_eq_abs]; exact (fderiv ℝ h z).le_opNorm _
        _ ≤ ‖fderiv ℝ h z‖ * (‖mulVecCLM B‖ * ‖z‖) :=
            mul_le_mul_of_nonneg_left (norm_mulVecCLM_apply_le B z) (norm_nonneg _)
        _ = (‖fderiv ℝ h z‖ * ‖z‖) * ‖mulVecCLM B‖ := by ring
        _ ≤ Mh * ‖mulVecCLM B‖ := mul_le_mul_of_nonneg_right (hhb z hz) (norm_nonneg _)
    exact mul_le_mul (hgb z) h1 (abs_nonneg _) ((abs_nonneg _).trans (hgb 0))
  have hi1 := hbd c f Mc Mf hcm hMc hMfd
  have hi2 := hbd f c Mf Mc hfm hMf hMcd
  have hsplit : (∫ z, fderiv ℝ (fun z => c z * f z) z (B *ᵥ z) ∂projectiveHaar ι) =
      (∫ z, c z * fderiv ℝ f z (B *ᵥ z) ∂projectiveHaar ι) +
        ∫ z, f z * fderiv ℝ c z (B *ᵥ z) ∂projectiveHaar ι := by
    rw [← integral_add hi1 hi2]
    exact integral_congr_ae (by filter_upwards [hne] with z hz; exact hprod z hz)
  rw [hsplit] at hcf
  have hcf' : (∫ z, c z * f z * ((Fintype.card ι : ℝ) * quadQuot B z - (B.trace).re)
      ∂projectiveHaar ι) =
      ∫ z, (fun z => c z * f z) z * ((Fintype.card ι : ℝ) * quadQuot B z - (B.trace).re)
        ∂projectiveHaar ι := rfl
  rw [hcf']
  linarith

/-!
## Integrability helpers on the projective law
-/

theorem isProbabilityMeasure_projectiveHaar : IsProbabilityMeasure (projectiveHaar ι) := by
  unfold projectiveHaar
  have : IsProbabilityMeasure (circularVectorLaw ι) := by
    rw [circularVectorLaw_eq]; infer_instance
  infer_instance

theorem measurable_normalize :
    Measurable (fun g : ι → ℂ => ((l2Norm g)⁻¹ : ℂ) • g) :=
  ((Complex.measurable_ofReal.comp measurable_l2Norm).inv).smul measurable_id

/-- Projective Haar is supported on unit vectors (`Σ_a |v_a|² = 1`), in particular off `0`. -/
theorem ae_projectiveHaar_unit [Nonempty ι] :
    ∀ᵐ v ∂projectiveHaar ι, normSqSum v = 1 := by
  unfold projectiveHaar
  have hs : MeasurableSet {g : ι → ℂ | normSqSum g = 1} :=
    measurableSet_eq_fun contDiff_normSqSum.continuous.measurable measurable_const
  rw [ae_map_iff measurable_normalize.aemeasurable hs]
  filter_upwards [ae_circular_ne_zero] with g hg
  have hl := l2Norm_pos hg
  show normSqSum (((l2Norm g)⁻¹ : ℂ) • g) = 1
  have : l2Norm g ^ 2 = ∑ a, ‖g a‖ ^ 2 := by
    unfold l2Norm; rw [Real.sq_sqrt (Finset.sum_nonneg fun a _ => by positivity)]
  unfold normSqSum
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum, ← this]
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl, inv_pow,
    inv_mul_cancel₀ (by positivity)]

theorem ae_projectiveHaar_ne_zero [Nonempty ι] : ∀ᵐ v ∂projectiveHaar ι, v ≠ 0 := by
  filter_upwards [ae_projectiveHaar_unit] with v hv h0
  rw [h0] at hv; simp [normSqSum] at hv

theorem measurable_fderiv_mulVec (h : (ι → ℂ) → ℝ) (B : Matrix ι ι ℂ) :
    Measurable (fun z : ι → ℂ => fderiv ℝ h z (B *ᵥ z)) := by
  have : (fun z : ι → ℂ => fderiv ℝ h z (B *ᵥ z)) = fun z => ∑ a,
      (fderiv ℝ h z (Pi.single a 1) * ((B *ᵥ z) a).re +
        fderiv ℝ h z (Pi.single a Complex.I) * ((B *ᵥ z) a).im) := by
    funext z; exact fderiv_apply_eq_sum _ _
  rw [this]
  refine Finset.measurable_sum _ fun a _ => ?_
  exact ((measurable_fderiv_apply_const ℝ h _).mul
    (Complex.measurable_re.comp ((measurable_pi_apply a).comp
      (mulVecCLM B).continuous.measurable))).add
    ((measurable_fderiv_apply_const ℝ h _).mul
    (Complex.measurable_im.comp ((measurable_pi_apply a).comp
      (mulVecCLM B).continuous.measurable)))

/-- `Dh(v)[Bv]` is bounded off the origin for scale-invariant `C¹` `h`. -/
theorem exists_bound_fderiv_mulVec {h : (ι → ℂ) → ℝ} (hinv : IsScaleInvariant h)
    (hc : ContDiffOn ℝ 1 h {z | z ≠ 0}) (B : Matrix ι ι ℂ) :
    ∃ M : ℝ, ∀ z, z ≠ 0 → |fderiv ℝ h z (B *ᵥ z)| ≤ M := by
  obtain ⟨M, -, hM⟩ := exists_bound_of_scaleInvariant hinv hc
  refine ⟨M * ‖mulVecCLM B‖, fun z hz => ?_⟩
  calc |fderiv ℝ h z (B *ᵥ z)| ≤ ‖fderiv ℝ h z‖ * ‖B *ᵥ z‖ := by
        rw [← Real.norm_eq_abs]; exact (fderiv ℝ h z).le_opNorm _
    _ ≤ ‖fderiv ℝ h z‖ * (‖mulVecCLM B‖ * ‖z‖) :=
        mul_le_mul_of_nonneg_left (norm_mulVecCLM_apply_le B z) (norm_nonneg _)
    _ = (‖fderiv ℝ h z‖ * ‖z‖) * ‖mulVecCLM B‖ := by ring
    _ ≤ M * ‖mulVecCLM B‖ := mul_le_mul_of_nonneg_right (hM z hz) (norm_nonneg _)

/-- A Borel function bounded off the origin is integrable under projective Haar. -/
theorem integrable_projectiveHaar_of_bound [Nonempty ι] {G : (ι → ℂ) → ℝ} (hG : Measurable G)
    {M : ℝ} (hM : ∀ z, z ≠ 0 → |G z| ≤ M) : Integrable G (projectiveHaar ι) := by
  have := isProbabilityMeasure_projectiveHaar (ι := ι)
  refine (integrable_const M).mono' hG.aestronglyMeasurable ?_
  filter_upwards [ae_projectiveHaar_ne_zero] with z hz
  rw [Real.norm_eq_abs]; exact hM z hz

end BlockBand.Angular.ProjectiveStein
