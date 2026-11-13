module
public import BlockBand.Counting.SpectralTranslationL1
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Poisson unsmoothing on the real line

For a continuous function `f` supported in `[-R,R]`, bounded by `M`, with modulus of
continuity `ω` at scale `h ≤ 1`, the `L¹` distance between `f` and its Poisson smoothing
`P_δ * f` is at most `2 (R + 1) ω + 8 R M δ / (π h)`.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory Set

def poissonSmoothTest (δ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t : ℝ, poissonKernel δ t * f (x+t)

theorem integrable_poisson_translationL1 (f : ℝ → ℝ) (hf : Continuous f)
    (R M δ : ℝ) (hR : 0≤R) (hδ : 0<δ)
    (hs : ∀ x, x ∉ Icc (-R) R → f x=0) (hb : ∀ x, |f x|≤M) :
    Integrable (fun t => poissonKernel δ t * spectralTranslationL1 f t) := by
  apply ((integrable_poissonKernel hδ).const_mul (4*R*M)).mono'
    ((integrable_poissonKernel hδ).aestronglyMeasurable.mul
      (measurable_spectralTranslationL1 f hf).aestronglyMeasurable)
  filter_upwards with t
  change ‖poissonKernel δ t * spectralTranslationL1 f t‖ ≤ 4*R*M*poissonKernel δ t
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (poissonKernel_nonneg hδ t)
    (spectralTranslationL1_nonneg f t))]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (spectralTranslationL1_global_le f hf R M hR hs hb t) (poissonKernel_nonneg hδ t)

theorem integral_poisson_translationL1_le (f : ℝ → ℝ) (hf : Continuous f)
    (R M δ h ω : ℝ) (hR : 0≤R) (hM : 0≤M) (hδ : 0<δ)
    (hh : 0<h) (hh1 : h≤1) (hω : 0≤ω)
    (hs : ∀ x, x ∉ Icc (-R) R → f x=0) (hb : ∀ x, |f x|≤M)
    (hmod : ∀ x y, |x-y|≤h → |f x-f y|≤ω) :
    (∫ t : ℝ, poissonKernel δ t * spectralTranslationL1 f t) ≤
      2*(R+1)*ω + 8*R*M*δ/(Real.pi*h) := by
  let A:=2*(R+1)*ω
  let B:=4*R*M
  let tail : Set ℝ := {t | h < |t|}
  have htail : MeasurableSet tail:=measurableSet_lt measurable_const measurable_abs
  have hA : 0≤A := by dsimp[A];positivity
  have hB : 0≤B := by dsimp[B];positivity
  have hp:=integrable_poissonKernel hδ
  have henv : Integrable (fun t=>A*poissonKernel δ t+B*tail.indicator (poissonKernel δ) t):=
    (hp.const_mul A).add ((hp.indicator htail).const_mul B)
  calc
    (∫ t : ℝ, poissonKernel δ t*spectralTranslationL1 f t) ≤
        ∫ t : ℝ, A*poissonKernel δ t+B*tail.indicator (poissonKernel δ) t := by
      apply integral_mono (integrable_poisson_translationL1 f hf R M δ hR hδ hs hb) henv
      intro t
      change poissonKernel δ t*spectralTranslationL1 f t ≤ A*poissonKernel δ t+B*tail.indicator (poissonKernel δ) t
      by_cases ht : h < |t|
      · rw [Set.indicator_of_mem (show t ∈ tail from ht)]
        have he:=spectralTranslationL1_global_le f hf R M hR hs hb t
        have hp0:=poissonKernel_nonneg hδ t
        dsimp[B] at *
        nlinarith
      · rw [Set.indicator_of_notMem (show t ∉ tail from ht)]
        have he:=spectralTranslationL1_near_le f R h ω hR hh1 hs hmod t (le_of_not_gt ht)
        have hp0:=poissonKernel_nonneg hδ t
        dsimp[A] at *
        nlinarith
    _ = A+B*(∫ t : ℝ in tail,poissonKernel δ t) := by
      rw [integral_add (hp.const_mul A) ((hp.indicator htail).const_mul B),
        integral_const_mul,integral_const_mul,integral_poissonKernel hδ,
        integral_indicator htail]
      ring
    _ ≤ A+B*(2*δ/(Real.pi*h)) := by
      gcongr
      exact integral_poissonKernel_tail_le hδ hh
    _ = _ := by dsimp[A,B];ring

theorem continuous_poissonKernel {δ : ℝ} (hδ : 0 < δ) : Continuous (poissonKernel δ) := by
  unfold poissonKernel
  exact continuous_const.div
    (continuous_const.mul ((continuous_id.pow 2).add continuous_const))
    (fun t => by positivity)

theorem integrable_poissonSmoothTest_section (f : ℝ → ℝ) (hf : Continuous f)
    (M δ : ℝ) (hδ : 0 < δ) (hb : ∀ x, |f x| ≤ M) (x : ℝ) :
    Integrable (fun t => poissonKernel δ t * f (x+t)) := by
  apply ((integrable_poissonKernel hδ).const_mul M).mono'
    (((continuous_poissonKernel hδ).mul (hf.comp (continuous_const.add continuous_id))).aestronglyMeasurable)
  filter_upwards with t
  change ‖poissonKernel δ t * f (x+t)‖ ≤ M*poissonKernel δ t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poissonKernel_nonneg hδ t)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb (x+t)) (poissonKernel_nonneg hδ t)

theorem poisson_unsmoothing_difference_eq_integral (f : ℝ → ℝ) (hf : Continuous f)
    (M δ : ℝ) (hδ : 0 < δ) (hb : ∀ x, |f x| ≤ M) (x : ℝ) :
    f x - poissonSmoothTest δ f x =
      ∫ t : ℝ, poissonKernel δ t * (f x - f (x+t)) := by
  simp_rw [mul_sub]
  rw [integral_sub ((integrable_poissonKernel hδ).mul_const (f x))
    (integrable_poissonSmoothTest_section f hf M δ hδ hb x),
    integral_mul_const, integral_poissonKernel hδ, one_mul]
  rfl

theorem integrable_poisson_error_product (f : ℝ → ℝ) (hf : Continuous f)
    (R M δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hs : ∀ x, x ∉ Icc (-R) R → f x=0) (hb : ∀ x, |f x| ≤ M) :
    Integrable (fun z : ℝ×ℝ => poissonKernel δ z.1 * (f z.2 - f (z.2+z.1)))
      (volume.prod volume) := by
  have hm : AEStronglyMeasurable
      (fun z : ℝ×ℝ => poissonKernel δ z.1 * (f z.2 - f (z.2+z.1))) (volume.prod volume) :=
    (((continuous_poissonKernel hδ).comp continuous_fst).mul
      ((hf.comp continuous_snd).sub (hf.comp (continuous_snd.add continuous_fst)))).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards with t
    have hi := integrable_spectralCompactTest f hf R hs
    exact (hi.sub (hi.comp_add_right t)).const_mul _
  · have heq : (fun t : ℝ => ∫ x : ℝ, ‖poissonKernel δ t * (f x-f (x+t))‖) =
        fun t => poissonKernel δ t * spectralTranslationL1 f t := by
      funext t
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poissonKernel_nonneg hδ t),
        ]
      simp_rw [abs_sub_comm (f _) (f (_+t))]
      rw [integral_const_mul]
      rfl
    rw [heq]
    exact integrable_poisson_translationL1 f hf R M δ hR hδ hs hb

theorem integrable_poissonUnsmoothingDifference (f : ℝ → ℝ) (hf : Continuous f)
    (R M δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hs : ∀ x, x ∉ Icc (-R) R → f x=0) (hb : ∀ x, |f x| ≤ M) :
    Integrable (fun x => f x-poissonSmoothTest δ f x) := by
  have hi := (integrable_poisson_error_product f hf R M δ hR hδ hs hb).integral_prod_right
  exact hi.congr (Filter.Eventually.of_forall (fun x =>
    (poisson_unsmoothing_difference_eq_integral f hf M δ hδ hb x).symm))

theorem integral_poissonUnsmoothingDifference_le_translationL1
    (f : ℝ → ℝ) (hf : Continuous f) (R M δ : ℝ)
    (hR : 0 ≤ R) (hδ : 0 < δ)
    (hs : ∀ x, x ∉ Icc (-R) R → f x=0) (hb : ∀ x, |f x| ≤ M) :
    (∫ x : ℝ, |f x-poissonSmoothTest δ f x|) ≤
      ∫ t : ℝ, poissonKernel δ t * spectralTranslationL1 f t := by
  have hi := integrable_poisson_error_product f hf R M δ hR hδ hs hb
  calc
    (∫ x : ℝ, |f x-poissonSmoothTest δ f x|) ≤
        ∫ x : ℝ, ∫ t : ℝ, ‖poissonKernel δ t * (f x-f (x+t))‖ := by
      apply integral_mono (integrable_poissonUnsmoothingDifference f hf R M δ hR hδ hs hb).abs
        hi.norm.integral_prod_right
      intro x
      change |f x-poissonSmoothTest δ f x| ≤ ∫ t : ℝ, ‖poissonKernel δ t*(f x-f (x+t))‖
      rw [poisson_unsmoothing_difference_eq_integral f hf M δ hδ hb x]
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun t : ℝ => poissonKernel δ t*(f x-f (x+t)))
    _ = ∫ t : ℝ, ∫ x : ℝ, ‖poissonKernel δ t * (f x-f (x+t))‖ :=
      (integral_integral_swap hi.norm).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poissonKernel_nonneg hδ t)]
      simp_rw [abs_sub_comm (f _) (f (_+t))]
      rw [integral_const_mul]
      rfl

theorem integral_poissonUnsmoothingDifference_le
    (f : ℝ → ℝ) (hf : Continuous f) (R M δ h ω : ℝ)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hδ : 0 < δ) (hh : 0 < h) (hh1 : h ≤ 1) (hω : 0 ≤ ω)
    (hs : ∀ x, x ∉ Icc (-R) R → f x=0) (hb : ∀ x, |f x| ≤ M)
    (hmod : ∀ x y, |x-y| ≤ h → |f x-f y| ≤ ω) :
    (∫ x : ℝ, |f x-poissonSmoothTest δ f x|) ≤
      2*(R+1)*ω + 8*R*M*δ/(Real.pi*h) :=
  (integral_poissonUnsmoothingDifference_le_translationL1 f hf R M δ hR hδ hs hb).trans
    (integral_poisson_translationL1_le f hf R M δ h ω hR hM hδ hh hh1 hω hs hb hmod)

end BlockBand.Counting
