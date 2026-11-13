module

public import BlockBand.Native.PSSS.BlockBand.Analysis.CauchyBoundaryTransform
public import BlockBand.Native.PSSS.BlockBand.Analysis.CauchyResolventBound
public import Mathlib.Analysis.Complex.Harmonic.MeanValue

/-!
# Cauchy–Poisson representation on the upper half-plane

This module proves the noncommuting harmonic-analysis step in the
projected Wegner argument.  For a Hermitian finite matrix `A`, a
positive-semidefinite absorber `Q`, and regulator `η > 0`, it proves that the
standard-Cauchy average of the negative imaginary trace of
`(A + tQ + iηI)⁻¹` equals its upper-half-plane value at `i`, hence the trace of
`(A + i(Q + ηI))⁻¹`.

The proof maps the unit disk to the upper half-plane by the inverse Cayley map,
applies Mathlib's disk mean-value theorem on every smaller concentric circle,
and passes radially to the boundary by dominated convergence.  The domination
is the sharp `card ι / η` estimate from `CauchyResolventBound`; the tangent
boundary change of variables is `CauchyBoundaryTransform`.  No commutativity or
simultaneous diagonalization of `A` and `Q` is assumed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

open Matrix MeasureTheory Set Filter Metric
open scoped ComplexOrder Matrix ENNReal NNReal Topology Interval

namespace PSSSNative.BlockBand

/-- The inverse Cayley map from the unit disk to the upper half-plane. -/
def diskToUpperHalfPlane (w : ℂ) : ℂ :=
  Complex.I * (1 + w) / (1 - w)

@[simp] theorem diskToUpperHalfPlane_zero :
    diskToUpperHalfPlane 0 = Complex.I := by
  simp [diskToUpperHalfPlane]

lemma im_diskToUpperHalfPlane (w : ℂ) (hw : w ≠ 1) :
    (diskToUpperHalfPlane w).im =
      (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
  rw [diskToUpperHalfPlane, Complex.div_im]
  simp only [Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, one_mul,
    Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, zero_add,
    Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
  have hd : (1 - w.re) ^ 2 + (-w.im) ^ 2 ≠ 0 := by
    intro h
    have h1 : 1 - w.re = 0 := by nlinarith [sq_nonneg (1 - w.re), sq_nonneg (-w.im)]
    have h2 : w.im = 0 := by nlinarith [sq_nonneg (1 - w.re), sq_nonneg (-w.im)]
    apply hw
    apply Complex.ext <;> simp_all
    linarith
  field_simp
  simp [Complex.mul_im]
  ring

lemma im_diskToUpperHalfPlane_pos {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (diskToUpperHalfPlane w).im := by
  have hw1 : w ≠ 1 := by
    intro h
    subst w
    simp at hw
  rw [im_diskToUpperHalfPlane w hw1]
  apply div_pos
  · rw [← (Complex.sq_norm w)]
    nlinarith [norm_nonneg w]
  · exact Complex.normSq_pos.mpr (sub_ne_zero.mpr hw1.symm)

lemma diskToUpperHalfPlane_exp_mul_I {φ : ℝ}
    (hφ : φ ∈ Set.Ioo 0 (2 * Real.pi)) :
    diskToUpperHalfPlane (Complex.exp (φ * Complex.I)) =
      (Real.tan (φ / 2 - Real.pi / 2) : ℂ) := by
  have hhalf : φ / 2 ∈ Set.Ioo 0 Real.pi := by
    exact ⟨div_pos hφ.1 (by norm_num), by nlinarith [hφ.2]⟩
  have hsin : Real.sin (φ / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hhalf.1 hhalf.2).ne'
  have hs : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    conv_lhs => rw [show φ = 2 * (φ / 2) by ring]
    exact Real.sin_two_mul (φ / 2)
  have hc : Real.cos φ = 2 * Real.cos (φ / 2) ^ 2 - 1 := by
    conv_lhs => rw [show φ = 2 * (φ / 2) by ring]
    exact Real.cos_two_mul (φ / 2)
  have htan : Real.tan (φ / 2 - Real.pi / 2) =
      -Real.cos (φ / 2) / Real.sin (φ / 2) := by
    rw [Real.tan_eq_sin_div_cos, Real.sin_sub, Real.cos_sub,
      Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  have htrig := Real.sin_sq_add_cos_sq (φ / 2)
  have hone : 1 - Real.cos φ = 2 * Real.sin (φ / 2) ^ 2 := by
    rw [hc]
    nlinarith [htrig]
  have hdeneq : (1 - Real.cos φ) ^ 2 + Real.sin φ ^ 2 =
      4 * Real.sin (φ / 2) ^ 2 := by
    rw [hone, hs]
    ring_nf at htrig ⊢
    linear_combination 4 * Real.sin (φ * (1 / 2)) ^ 2 * htrig
  have hden : (1 - Real.cos φ) ^ 2 + Real.sin φ ^ 2 ≠ 0 := by
    rw [hdeneq]
    positivity
  rw [htan, Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · simp only [diskToUpperHalfPlane, Complex.div_re, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, mul_zero, add_zero, zero_add,
      Complex.normSq_apply]
    norm_num
    rw [show (1 - Real.cos φ) * (1 - Real.cos φ) +
      Real.sin φ * Real.sin φ =
      (1 - Real.cos φ) ^ 2 + Real.sin φ ^ 2 by ring, hdeneq]
    field_simp [hsin]
    rw [hs, hc]
    nlinarith [htrig]
  · simp only [diskToUpperHalfPlane, Complex.div_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, mul_zero, add_zero, zero_add,
      Complex.normSq_apply]
    norm_num
    rw [show (1 - Real.cos φ) * (1 - Real.cos φ) +
      Real.sin φ * Real.sin φ =
      (1 - Real.cos φ) ^ 2 + Real.sin φ ^ 2 by ring, hdeneq]
    field_simp [hsin]
    rw [hs, hc]
    nlinarith [htrig]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem analyticAt_diskToUpperHalfPlane {w : ℂ} (hw : w ≠ 1) :
    AnalyticAt ℂ diskToUpperHalfPlane w := by
  unfold diskToUpperHalfPlane
  fun_prop (discharger := exact sub_ne_zero.mpr hw.symm)

/-- Every concentric circle strictly inside the Cayley disk has the same
average negative-imaginary resolvent trace, namely its value at `i`. -/
theorem circleAverage_neg_im_cauchyResolventTrace_diskToUpperHalfPlane
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η r : ℝ} (hη : 0 < η) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage
        (fun w : ℂ =>
          -(cauchyResolventTrace A Q η (diskToUpperHalfPlane w)).im)
        0 r =
      -(cauchyResolventTrace A Q η Complex.I).im := by
  let g : ℂ → ℝ := fun w =>
    -(cauchyResolventTrace A Q η (diskToUpperHalfPlane w)).im
  have hg : InnerProductSpace.HarmonicOnNhd g (closedBall 0 |r|) := by
    intro w hw
    have hwr : ‖w‖ < 1 := by
      rw [mem_closedBall, dist_zero_right] at hw
      rw [abs_of_nonneg hr0] at hw
      exact lt_of_le_of_lt hw hr1
    have hw1 : w ≠ 1 := by
      intro h
      subst w
      simp at hwr
    have hcayley := analyticAt_diskToUpperHalfPlane hw1
    have htrace := analyticAt_cauchyResolventTrace A Q hA hQ hη
      (im_diskToUpperHalfPlane_pos hwr)
    exact (htrace.comp hcayley).harmonicAt_im.neg
  rw [hg.circleAverage_eq]
  simp [g]

private theorem continuousAt_cauchyResolventTrace_of_im_nonneg
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : 0 ≤ z.im) :
    ContinuousAt (cauchyResolventTrace A Q η) z := by
  have hu : IsUnit (cauchyResolventPencil A Q η z).det :=
    isUnit_det_cauchyResolventPencil A Q hA hQ hη hz
  have hp : ContinuousAt (cauchyResolventPencil A Q η) z := by
    unfold cauchyResolventPencil
    fun_prop
  have hdinv : ContinuousAt Ring.inverse
      (cauchyResolventPencil A Q η z).det := by
    rw [← hu.unit_spec]
    exact (analyticAt_inverse (𝕜 := ℂ) hu.unit).continuousAt
  have hout : ContinuousAt (Inv.inv : Matrix ι ι ℂ → Matrix ι ι ℂ)
      (cauchyResolventPencil A Q η z) :=
    continuousAt_matrix_inv (cauchyResolventPencil A Q η z) hdinv
  have hinv := hout.comp hp
  unfold cauchyResolventTrace
  fun_prop

def radialRadius (n : ℕ) : ℝ := (n : ℝ) / (n + 1)

private lemma radialRadius_nonneg (n : ℕ) : 0 ≤ radialRadius n := by
  unfold radialRadius
  positivity

private lemma radialRadius_lt_one (n : ℕ) : radialRadius n < 1 := by
  unfold radialRadius
  rw [div_lt_one (by positivity)]
  norm_num

private lemma tendsto_radialRadius :
    Tendsto radialRadius atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1)
  exact tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1

private lemma norm_radial_circle_lt_one (n : ℕ) (φ : ℝ) :
    ‖(radialRadius n : ℂ) * Complex.exp (φ * Complex.I)‖ < 1 := by
  rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I,
    mul_one, Real.norm_of_nonneg (radialRadius_nonneg n)]
  exact radialRadius_lt_one n

/-- Radial circle integrals of the Cayley pullback converge to the boundary
integral.  The regulator supplies a uniform `card ι / η` dominator. -/
theorem tendsto_radial_integral_neg_im_cauchyResolventTrace
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) :
    Tendsto
      (fun n : ℕ => ∫ φ in (0 : ℝ)..(2 * Real.pi),
        -(cauchyResolventTrace A Q η
          (diskToUpperHalfPlane
            ((radialRadius n : ℂ) * Complex.exp (φ * Complex.I)))).im)
      atTop
      (𝓝 (∫ φ in (0 : ℝ)..(2 * Real.pi),
        -(cauchyResolventTrace A Q η
          (Real.tan (φ / 2 - Real.pi / 2) : ℂ)).im)) := by
  let F : ℕ → ℝ → ℝ := fun n φ =>
    -(cauchyResolventTrace A Q η
      (diskToUpperHalfPlane
        ((radialRadius n : ℂ) * Complex.exp (φ * Complex.I)))).im
  let f : ℝ → ℝ := fun φ =>
    -(cauchyResolventTrace A Q η
      (Real.tan (φ / 2 - Real.pi / 2) : ℂ)).im
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => (Fintype.card ι : ℝ) / η)
  · filter_upwards with n
    apply Continuous.aestronglyMeasurable
    rw [continuous_iff_continuousAt]
    intro φ
    have hw := norm_radial_circle_lt_one n φ
    have hw1 : (radialRadius n : ℂ) * Complex.exp (φ * Complex.I) ≠ 1 := by
      intro heq
      rw [heq] at hw
      simp at hw
    have htrace := (analyticAt_cauchyResolventTrace A Q hA hQ hη
      (im_diskToUpperHalfPlane_pos hw)).continuousAt
    have hcayley := (analyticAt_diskToUpperHalfPlane hw1).continuousAt
    have houter := htrace.comp hcayley
    have hmul : ContinuousAt (fun z : ℂ => (radialRadius n : ℂ) * z)
        (Complex.exp (φ * Complex.I)) := by fun_prop
    have houtermul := houter.comp hmul
    have hexpcont : ContinuousAt Complex.exp ((φ : ℂ) * Complex.I) :=
      Complex.continuous_exp.continuousAt
    have houterexp := houtermul.comp hexpcont
    have hmulI : ContinuousAt (fun z : ℂ => z * Complex.I) (φ : ℂ) := by
      fun_prop
    have houterlin := houterexp.comp_of_eq hmulI rfl
    have hcoe : ContinuousAt (fun x : ℝ => (x : ℂ)) φ := by fun_prop
    have hcomp := houterlin.comp_of_eq hcoe rfl
    change ContinuousAt (fun x : ℝ => cauchyResolventTrace A Q η
      (diskToUpperHalfPlane
        ((radialRadius n : ℂ) * Complex.exp (x * Complex.I)))) φ at hcomp
    exact (Complex.continuous_im.continuousAt.comp_of_eq hcomp rfl).neg
  · filter_upwards with n
    filter_upwards with φ
    intro _hφ
    have hw := norm_radial_circle_lt_one n φ
    have hz := (im_diskToUpperHalfPlane_pos hw).le
    have hmem := neg_im_cauchyResolventTrace_mem_Icc A Q hA hQ hη hz
    rw [Real.norm_eq_abs, abs_of_nonneg hmem.1]
    exact hmem.2
  · apply intervalIntegrable_const
  · filter_upwards [volume.ae_ne (0 : ℝ),
      volume.ae_ne (2 * Real.pi)] with φ hφ0 hφ2 hφmem
    have hpi : 0 < 2 * Real.pi := by positivity
    have hIoc : φ ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) := by
      simpa [Set.uIoc_of_le hpi.le] using hφmem
    have hφ : φ ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) :=
      ⟨hIoc.1, lt_of_le_of_ne hIoc.2 hφ2⟩
    have hhalf : 0 < φ / 2 := div_pos hφ.1 (by norm_num)
    have hhalfpi : φ / 2 < Real.pi := by nlinarith [hφ.2]
    have hsinpos := Real.sin_pos_of_pos_of_lt_pi hhalf hhalfpi
    have hc : Real.cos φ = 2 * Real.cos (φ / 2) ^ 2 - 1 := by
      conv_lhs => rw [show φ = 2 * (φ / 2) by ring]
      exact Real.cos_two_mul (φ / 2)
    have hone : 1 - Real.cos φ = 2 * Real.sin (φ / 2) ^ 2 := by
      rw [hc]
      nlinarith [Real.sin_sq_add_cos_sq (φ / 2)]
    have hexp : Complex.exp (φ * Complex.I) ≠ 1 := by
      intro he
      rw [Complex.exp_ofReal_mul_I] at he
      have hre := congrArg Complex.re he
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        mul_one, Complex.one_re] at hre
      nlinarith [hone, sq_pos_of_pos hsinpos]
    have hcircle : Tendsto
        (fun n : ℕ => (radialRadius n : ℂ) * Complex.exp (φ * Complex.I))
        atTop (𝓝 (Complex.exp (φ * Complex.I))) := by
      simpa using (Complex.ofRealCLM.continuous.tendsto 1).comp
        tendsto_radialRadius |>.mul_const (Complex.exp (φ * Complex.I))
    have hcayley : Tendsto
        (fun n : ℕ => diskToUpperHalfPlane
          ((radialRadius n : ℂ) * Complex.exp (φ * Complex.I)))
        atTop
        (𝓝 (diskToUpperHalfPlane (Complex.exp (φ * Complex.I)))) :=
      (analyticAt_diskToUpperHalfPlane hexp).continuousAt.tendsto.comp hcircle
    have hcont := continuousAt_cauchyResolventTrace_of_im_nonneg
      A Q hA hQ hη (z := diskToUpperHalfPlane (Complex.exp (φ * Complex.I))) (by
        rw [im_diskToUpperHalfPlane _ hexp, ← Complex.sq_norm]
        simp)
    have ht := hcont.tendsto.comp hcayley
    rw [diskToUpperHalfPlane_exp_mul_I hφ] at ht
    exact (continuous_neg.tendsto _).comp
      ((Complex.continuous_im.tendsto _).comp ht)

/-- **Noncommuting Cauchy–Poisson resolvent identity.**  With the standard
Cauchy weight `standardCauchyWeight`, averaging the regulated boundary resolvent
along the Hermitian pencil `A + tQ` is exactly the resolvent with one added
unit of absorption `Q`.  No simultaneous diagonalization of `A` and `Q` is
used. -/
theorem integral_standardCauchyWeight_mul_neg_im_cauchyResolventTrace_eq_I
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) :
    (∫ t : ℝ, standardCauchyWeight t *
      (-(cauchyResolventTrace A Q η (t : ℂ)).im)) =
      -(cauchyResolventTrace A Q η Complex.I).im := by
  let J : ℕ → ℝ := fun n =>
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
      -(cauchyResolventTrace A Q η
        (diskToUpperHalfPlane
          ((radialRadius n : ℂ) * Complex.exp (φ * Complex.I)))).im
  let L : ℝ :=
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
      -(cauchyResolventTrace A Q η
        (Real.tan (φ / 2 - Real.pi / 2) : ℂ)).im
  have hJ : Tendsto J atTop (𝓝 L) := by
    exact tendsto_radial_integral_neg_im_cauchyResolventTrace A Q hA hQ hη
  have hmean : ∀ n : ℕ,
      (2 * Real.pi)⁻¹ * J n =
        -(cauchyResolventTrace A Q η Complex.I).im := by
    intro n
    have h := circleAverage_neg_im_cauchyResolventTrace_diskToUpperHalfPlane
      A Q hA hQ hη (radialRadius_nonneg n) (radialRadius_lt_one n)
    rw [Real.circleAverage_def] at h
    simpa [J, circleMap_zero, smul_eq_mul] using h
  have hnorm : Tendsto (fun n => (2 * Real.pi)⁻¹ * J n) atTop
      (𝓝 ((2 * Real.pi)⁻¹ * L)) := tendsto_const_nhds.mul hJ
  have hconst : Tendsto (fun _n : ℕ =>
      -(cauchyResolventTrace A Q η Complex.I).im) atTop
      (𝓝 (-(cauchyResolventTrace A Q η Complex.I).im)) :=
    tendsto_const_nhds
  have hangular : (2 * Real.pi)⁻¹ * L =
      -(cauchyResolventTrace A Q η Complex.I).im := by
    exact tendsto_nhds_unique hnorm (hconst.congr' (Eventually.of_forall fun n => (hmean n).symm))
  rw [integral_standardCauchyWeight_mul_eq_circleParam]
  exact hangular

end PSSSNative.BlockBand
