module

public import BlockBand.Angular.Stein

/-!
# Euclidean bookkeeping for the angular ratio lemma

All norms are Euclidean (`l2Norm`, `normSqSum`), never the sup norm of `ι → ℂ`.
* Cauchy–Schwarz for `Re(x*y)`, the Frobenius bound `‖Mx‖² ≤ ‖M‖_F² ‖x‖²` for rectangular
  complex matrices, and the adjoint rule `Re((Mx)*y) = Re(x*(Mᴴy))`.
* The resolvent bound `(Im z)² ‖(K - z)⁻¹ x‖² ≤ ‖x‖²` for Hermitian `K`.
* The derivative of a Rayleigh quotient at a unit vector in an arbitrary direction.
* The Euclidean gradient `∇f` of the real metric, `Df[w] = Re(w*∇f)`, and `gradNorm f = ‖∇f‖`.
* Integrability under projective Haar of any function continuous off the origin.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.Ratio

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.DegreeZero
open BlockBand.Angular.ProjectiveStein BlockBand.Angular.Reference BlockBand.Angular.Stein
open BlockBand.Angular.Stein.AngularData (reInner quadNum reInner_comm normSqSum_eq_reInner
  reInner_mulVec_herm quadNum_line normSqSum_line fderiv_apply_of_line quadQuot_of_unit)
open scoped ComplexConjugate

section Euclid

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

theorem reInner_eq_dot (x y : n → ℂ) : reInner x y = (star x ⬝ᵥ y).re := rfl

theorem l2Norm_eq (x : n → ℂ) : l2Norm x = Real.sqrt (normSqSum x) := rfl

theorem normSqSum_nonneg (x : n → ℂ) : 0 ≤ normSqSum x :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem l2Norm_nonneg (x : n → ℂ) : 0 ≤ l2Norm x := Real.sqrt_nonneg _

theorem l2Norm_sq (x : n → ℂ) : l2Norm x ^ 2 = normSqSum x := Real.sq_sqrt (normSqSum_nonneg x)

theorem abs_reInner_le (x y : n → ℂ) : |reInner x y| ≤ l2Norm x * l2Norm y := by
  unfold reInner l2Norm
  rw [Complex.re_sum]
  calc |∑ a, (conj (x a) * y a).re| ≤ ∑ a, |(conj (x a) * y a).re| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, ‖x a‖ * ‖y a‖ := Finset.sum_le_sum fun a _ => by
        calc |(conj (x a) * y a).re| ≤ ‖conj (x a) * y a‖ := Complex.abs_re_le_norm _
          _ = ‖x a‖ * ‖y a‖ := by rw [norm_mul, Complex.norm_conj]
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- Squared Frobenius norm `Σ |M_ij|²`. -/
def frob (M : Matrix m n ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖ ^ 2

theorem frob_nonneg (M : Matrix m n ℂ) : 0 ≤ frob M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- `‖Mu‖² ≤ ‖M‖_F² ‖u‖²`. -/
theorem normSqSum_mulVec_le (M : Matrix m n ℂ) (u : n → ℂ) :
    normSqSum (M *ᵥ u) ≤ frob M * normSqSum u := by
  unfold normSqSum frob
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(M *ᵥ u) i‖ ≤ ∑ j, ‖M i j‖ * ‖u j‖ := by
    calc ‖(M *ᵥ u) i‖ = ‖∑ j, M i j * u j‖ := rfl
      _ ≤ ∑ j, ‖M i j * u j‖ := norm_sum_le _ _
      _ = ∑ j, ‖M i j‖ * ‖u j‖ := by simp only [norm_mul]
  calc ‖(M *ᵥ u) i‖ ^ 2 ≤ (∑ j, ‖M i j‖ * ‖u j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ j, ‖M i j‖ ^ 2) * ∑ j, ‖u j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- Adjoint rule `Re((Mx)*y) = Re(x*(Mᴴy))`. -/
theorem reInner_mulVec_left (M : Matrix m n ℂ) (x : n → ℂ) (y : m → ℂ) :
    reInner (M *ᵥ x) y = reInner x (Mᴴ *ᵥ y) := by
  rw [reInner_eq_dot, reInner_eq_dot, star_mulVec, ← dotProduct_mulVec]

theorem reInner_self (x : n → ℂ) : reInner x x = normSqSum x := (normSqSum_eq_reInner x).symm

/-- `Re(v*(MᴴM)v) = ‖Mv‖²`. -/
theorem quadNum_conjTranspose_mul_self (M : Matrix m n ℂ) (x : n → ℂ) :
    quadNum (Mᴴ * M) x = normSqSum (M *ᵥ x) := by
  rw [← reInner_self, reInner_mulVec_left, mulVec_mulVec]; rfl

theorem conjTranspose_mul_self_isHermitian (M : Matrix m n ℂ) : (Mᴴ * M).IsHermitian := by
  unfold IsHermitian; rw [conjTranspose_mul, conjTranspose_conjTranspose]

theorem normSqSum_smul (c : ℂ) (x : n → ℂ) : normSqSum (c • x) = ‖c‖ ^ 2 * normSqSum x := by
  unfold normSqSum; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]

theorem normSqSum_add_le (x y : n → ℂ) :
    normSqSum (x + y) ≤ (l2Norm x + l2Norm y) ^ 2 := by
  have e : normSqSum (x + y) = normSqSum x + 2 * reInner x y + normSqSum y := by
    rw [← reInner_self, ← reInner_self, ← reInner_self]
    unfold reInner
    simp only [Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib, Complex.add_re]
    have hsym : (∑ a, conj (y a) * x a).re = (∑ a, conj (x a) * y a).re := reInner_comm y x
    rw [hsym]; ring
  rw [e]
  have h1 := abs_reInner_le x y
  have hx := l2Norm_sq x; have hy := l2Norm_sq y
  nlinarith [abs_le.1 h1, l2Norm_nonneg x, l2Norm_nonneg y]

/-- Real cross term of a squared norm. -/
theorem normSqSum_sub (x y : n → ℂ) :
    normSqSum (x - y) = normSqSum x - 2 * reInner x y + normSqSum y := by
  rw [← reInner_self, ← reInner_self, ← reInner_self]
  unfold reInner
  simp only [Pi.sub_apply, map_sub, sub_mul, mul_sub, Finset.sum_sub_distrib, Complex.sub_re]
  have hsym : (∑ a, conj (y a) * x a).re = (∑ a, conj (x a) * y a).re := reInner_comm y x
  rw [hsym]; ring

end Euclid

section Resolvent

variable {n : Type} [Fintype n] [DecidableEq n]

/-- **Resolvent bound**: `(Im z)² ‖(K - z)⁻¹ x‖² ≤ ‖x‖²` for Hermitian `K` and `Im z ≠ 0`. -/
theorem resolvent_bound {K : Matrix n n ℂ} (hK : K.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (x : n → ℂ) : z.im ^ 2 * normSqSum (Reference.resolvent K z *ᵥ x) ≤ normSqSum x := by
  set u := Reference.resolvent K z *ᵥ x with hu
  have hx : x = K *ᵥ u - z • u := by
    have h := resolvent_mul hK hz
    calc x = ((K - z • (1 : Matrix n n ℂ)) * Reference.resolvent K z) *ᵥ x := by rw [h, one_mulVec]
      _ = _ := by rw [← mulVec_mulVec, sub_mulVec, smul_mulVec, one_mulVec]
  set w := K *ᵥ u
  have hp : (star u ⬝ᵥ w).im = 0 := hK.im_star_dotProduct_mulVec_self u
  have hcross : reInner w (z • u) = z.re * reInner u w := by
    rw [reInner_eq_dot, reInner_eq_dot, dotProduct_smul, smul_eq_mul, Complex.mul_re]
    have hc : star w ⬝ᵥ u = star (star u ⬝ᵥ w) := by
      simp [dotProduct, star_sum, mul_comm]
    rw [hc, Complex.star_def, Complex.conj_im, hp]; simp
  have hzu : normSqSum (z • u) = Complex.normSq z * normSqSum u := by
    rw [normSqSum_smul, Complex.sq_norm]
  have hcs := abs_reInner_le u w
  have hu2 := l2Norm_sq u; have hw2 := l2Norm_sq w
  have hnorm : normSqSum x = normSqSum w - 2 * (z.re * reInner u w) +
      Complex.normSq z * normSqSum u := by
    rw [hx, normSqSum_sub, hcross, hzu]
  rw [hnorm, Complex.normSq_apply]
  set mm := reInner u w
  have hmm : mm ^ 2 ≤ normSqSum u * normSqSum w := by
    rw [← hu2, ← hw2, ← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hcs 2
  have hn0 := normSqSum_nonneg u
  have hw0 := normSqSum_nonneg w
  rcases hn0.lt_or_eq with hpos | hzero
  · have key : 0 ≤ normSqSum w - 2 * (z.re * mm) + z.re ^ 2 * normSqSum u := by
      by_contra hneg
      push Not at hneg
      have h1 : normSqSum u * (normSqSum w - 2 * (z.re * mm) + z.re ^ 2 * normSqSum u) < 0 :=
        mul_neg_of_pos_of_neg hpos hneg
      nlinarith [sq_nonneg (mm - z.re * normSqSum u)]
    nlinarith
  · have hm0 : mm ^ 2 ≤ 0 := by rw [← hzero] at hmm; simpa using hmm
    have : mm = 0 := by nlinarith [sq_nonneg mm]
    rw [← hzero, this]; nlinarith

end Resolvent

section Sphere

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem ne_zero_of_unit {v : ι → ℂ} (hv : normSqSum v = 1) : v ≠ 0 := by
  intro h0; rw [h0] at hv; simp [normSqSum] at hv

theorem isCompact_unitSphere : IsCompact {v : ι → ℂ | normSqSum v = 1} := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_eq contDiff_normSqSum.continuous continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ι → ℂ)) (r := 1)).subset fun v hv => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
  have h : ‖v a‖ ^ 2 ≤ 1 := by
    rw [← (show normSqSum v = 1 from hv)]
    exact Finset.single_le_sum (f := fun k => ‖v k‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ a)
  nlinarith [norm_nonneg (v a)]

/-- A function continuous off the origin is integrable under projective Haar. -/
theorem integrable_of_continuousOn [Nonempty ι] {G : (ι → ℂ) → ℝ}
    (hG : ContinuousOn G {z | z ≠ 0}) : Integrable G (projectiveHaar ι) := by
  obtain ⟨M, hM⟩ := isCompact_unitSphere.exists_bound_of_continuousOn
    (hG.mono fun v hv => ne_zero_of_unit (ι := ι) hv)
  have := isProbabilityMeasure_projectiveHaar (ι := ι)
  have hae : AEStronglyMeasurable G (projectiveHaar ι) := by
    have h1 := hG.aestronglyMeasurable (μ := projectiveHaar ι) isOpen_ne.measurableSet
    have hr : (projectiveHaar ι).restrict {z : ι → ℂ | z ≠ 0} = projectiveHaar ι :=
      Measure.restrict_eq_self_of_ae_mem ae_projectiveHaar_ne_zero
    rwa [hr] at h1
  refine (integrable_const M).mono' hae ?_
  filter_upwards [ae_projectiveHaar_unit] with v hv using hM v hv

/-- Line derivative of a Rayleigh quotient at a unit vector, arbitrary direction. -/
theorem hasDerivAt_quadQuot_line' (M : Matrix ι ι ℂ) (v w : ι → ℂ) (hv : normSqSum v = 1) :
    HasDerivAt (fun τ : ℝ => quadQuot M (v + τ • w))
      ((reInner w (M *ᵥ v) + reInner v (M *ᵥ w)) - quadNum M v * (2 * reInner w v)) 0 := by
  have hfun : (fun τ : ℝ => quadQuot M (v + τ • w)) = fun τ =>
      (quadNum M v + τ * (reInner w (M *ᵥ v) + reInner v (M *ᵥ w)) + τ ^ 2 * quadNum M w) /
        (1 + τ * (2 * reInner w v) + τ ^ 2 * normSqSum w) := by
    funext τ
    rw [AngularData.quadQuot_eq, quadNum_line, normSqSum_line, hv]
  rw [hfun]
  set p := reInner w (M *ᵥ v) + reInner v (M *ᵥ w)
  have hnum : HasDerivAt (fun τ : ℝ => quadNum M v + τ * p + τ ^ 2 * quadNum M w) p 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const p).const_add (quadNum M v)).fun_add
      ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (quadNum M w))
    simpa using this
  have hden : HasDerivAt (fun τ : ℝ => 1 + τ * (2 * reInner w v) + τ ^ 2 * normSqSum w)
      (2 * reInner w v) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const (2 * reInner w v)).const_add 1).fun_add
      ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (normSqSum w))
    simpa using this
  have := hnum.div hden (by simp)
  convert this using 1
  simp

/-- `DQ_M(v)[w] = 2 Re(w*Mv) - 2 Q_M(v) Re(w*v)` at a unit vector, `M` Hermitian. -/
theorem fderiv_quadQuot_apply {M : Matrix ι ι ℂ} (hM : M.IsHermitian) {v : ι → ℂ}
    (hv : normSqSum v = 1) (w : ι → ℂ) :
    fderiv ℝ (quadQuot M) v w = 2 * reInner w (M *ᵥ v) - 2 * quadQuot M v * reInner w v := by
  have hd : DifferentiableAt ℝ (quadQuot M) v :=
    ((contDiffOn_quadQuot M).differentiableOn one_ne_zero).differentiableAt
      (isOpen_ne.mem_nhds (ne_zero_of_unit hv))
  rw [fderiv_apply_of_line hd (hasDerivAt_quadQuot_line' M v w hv),
    reInner_mulVec_herm hM v w, quadQuot_of_unit hv]
  ring

/-!
## The Euclidean gradient of the real metric
-/

/-- `∇f(v)`, characterized by `Df(v)[w] = Re(w*∇f(v))`. -/
def grad (f : (ι → ℂ) → ℝ) (v : ι → ℂ) : ι → ℂ := fun a =>
  (fderiv ℝ f v (Pi.single a 1) : ℂ) + (fderiv ℝ f v (Pi.single a Complex.I) : ℂ) * Complex.I

/-- `‖∇f(v)‖` (Euclidean). -/
def gradNorm (f : (ι → ℂ) → ℝ) (v : ι → ℂ) : ℝ := l2Norm (grad f v)

theorem fderiv_eq_reInner_grad (f : (ι → ℂ) → ℝ) (v w : ι → ℂ) :
    fderiv ℝ f v w = reInner w (grad f v) := by
  rw [fderiv_apply_eq_sum]
  unfold reInner grad
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

theorem abs_fderiv_le_gradNorm (f : (ι → ℂ) → ℝ) (v w : ι → ℂ) :
    |fderiv ℝ f v w| ≤ l2Norm w * gradNorm f v := by
  rw [fderiv_eq_reInner_grad]; exact abs_reInner_le _ _

theorem gradNorm_nonneg (f : (ι → ℂ) → ℝ) (v : ι → ℂ) : 0 ≤ gradNorm f v := l2Norm_nonneg _

theorem continuous_l2Norm {n : Type} [Fintype n] : Continuous (l2Norm (ι := n)) := by
  unfold l2Norm; fun_prop

theorem continuousOn_fderiv_apply {f : (ι → ℂ) → ℝ} (hf : ContDiffOn ℝ 1 f {z | z ≠ 0})
    {Y : (ι → ℂ) → (ι → ℂ)} (hY : Continuous Y) :
    ContinuousOn (fun v => fderiv ℝ f v (Y v)) {z | z ≠ 0} :=
  (hf.continuousOn_fderiv_of_isOpen isOpen_ne le_rfl).clm_apply hY.continuousOn

theorem continuousOn_gradNorm {f : (ι → ℂ) → ℝ} (hf : ContDiffOn ℝ 1 f {z | z ≠ 0}) :
    ContinuousOn (gradNorm f) {z | z ≠ 0} := by
  have hg : ContinuousOn (grad f) {z | z ≠ 0} := by
    refine continuousOn_pi.2 fun a => ?_
    have h1 := continuousOn_fderiv_apply hf (Y := fun _ => Pi.single a 1) continuous_const
    have h2 := continuousOn_fderiv_apply hf (Y := fun _ => Pi.single a Complex.I)
      continuous_const
    exact (Complex.continuous_ofReal.comp_continuousOn h1).add
      ((Complex.continuous_ofReal.comp_continuousOn h2).mul continuousOn_const)
  exact continuous_l2Norm.comp_continuousOn hg

end Sphere

end BlockBand.Angular.Ratio
