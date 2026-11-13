module
public import BlockBand.Counting.PoissonSmoothingKernel
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Translation error on the spectral line

For a continuous `f` supported in `[-R,R]` and bounded by `M`, the translation error
`∫ |f (x + t) - f x| dx` is at most `4 R M` for every `t`, and at most `2 (R + 1) ω` for
`|t| ≤ h ≤ 1` when `ω` is a modulus of continuity of `f` at scale `h`.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory Set

def spectralTranslationL1 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, |f (x+t)-f x|

theorem integrable_spectralCompactTest (f : ℝ → ℝ) (hf : Continuous f) (R : ℝ)
    (hs : ∀ x, x ∉ Icc (-R) R → f x=0) : Integrable f := by
  apply (integrableOn_iff_integrable_of_support_subset (s:=Icc (-R) R) ?_).mp
    hf.integrableOn_Icc
  intro x hx
  by_contra h
  exact hx (hs x h)

theorem integrable_spectralTranslationDifference (f : ℝ → ℝ) (hf : Continuous f)
    (R t : ℝ) (hs : ∀ x, x ∉ Icc (-R) R → f x=0) :
    Integrable (fun x => |f (x+t)-f x|) := by
  have hi:=integrable_spectralCompactTest f hf R hs
  exact ((hi.comp_add_right t).sub hi).abs

theorem spectralTranslationL1_nonneg (f : ℝ → ℝ) (t : ℝ) :
    0 ≤ spectralTranslationL1 f t := integral_nonneg (fun _ => abs_nonneg _)

theorem measurable_spectralTranslationL1 (f : ℝ → ℝ) (hf : Continuous f) :
    Measurable (spectralTranslationL1 f) := by
  have hm : StronglyMeasurable (fun z : ℝ×ℝ => |f (z.2+z.1)-f z.2|) :=
    ((hf.comp (continuous_snd.add continuous_fst)).sub (hf.comp continuous_snd)).abs.stronglyMeasurable
  exact hm.integral_prod_right'.measurable

theorem integral_abs_spectralCompactTest_le (f : ℝ → ℝ) (R M : ℝ)
    (hR : 0≤R) (hs : ∀ x, x ∉ Icc (-R) R → f x=0)
    (hbound : ∀ x, |f x|≤M) : (∫ x : ℝ, |f x|)≤2*R*M := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s:=Icc (-R) R) (fun x hx => by rw [hs x hx,abs_zero])]
  have h := norm_setIntegral_le_of_norm_le_const (f:=fun x : ℝ=>|f x|)
    (s:=Icc (-R) R) (μ:=volume) (C:=M) (by simp)
    (fun x _ => by simpa using hbound x)
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _=>abs_nonneg _))] at h
  rw [Real.volume_real_Icc_of_le (by linarith : -R ≤ R)] at h
  nlinarith

theorem spectralTranslationL1_global_le (f : ℝ → ℝ) (hf : Continuous f)
    (R M : ℝ) (hR : 0≤R)
    (hs : ∀ x, x ∉ Icc (-R) R → f x=0) (hbound : ∀ x, |f x|≤M) (t : ℝ) :
    spectralTranslationL1 f t ≤4*R*M := by
  have hi:=integrable_spectralCompactTest f hf R hs
  calc
    spectralTranslationL1 f t ≤∫ x : ℝ, |f (x+t)|+|f x| :=
      integral_mono (integrable_spectralTranslationDifference f hf R t hs)
        ((hi.comp_add_right t).abs.add hi.abs) (fun x=>abs_sub (f (x+t)) (f x))
    _ =2*(∫ x : ℝ, |f x|) := by
      rw [integral_add (hi.comp_add_right t).abs hi.abs,
        integral_add_right_eq_self (fun x : ℝ => |f x|) t]
      ring
    _ ≤4*R*M := by
      have h:=integral_abs_spectralCompactTest_le f R M hR hs hbound
      linarith

theorem spectralTranslationL1_near_le (f : ℝ → ℝ) (R h ω : ℝ)
    (hR : 0≤R) (hh1 : h≤1)
    (hs : ∀ x, x ∉ Icc (-R) R → f x=0)
    (hmod : ∀ x y, |x-y|≤h → |f x-f y|≤ω)
    (t : ℝ) (ht : |t|≤h) : spectralTranslationL1 f t ≤2*(R+1)*ω := by
  have hs' : ∀ x, x ∉ Icc (-R-1) (R+1) → |f (x+t)-f x|=0 := by
    intro x hx
    have ht1:=abs_le.mp (ht.trans hh1)
    have hnotx : x ∉ Icc (-R) R := by
      intro he
      apply hx
      constructor <;> linarith [he.1,he.2]
    have hnotxt : x+t ∉ Icc (-R) R := by
      intro he
      apply hx
      constructor <;> linarith [he.1,he.2,ht1.1,ht1.2]
    rw [hs x hnotx,hs (x+t) hnotxt,sub_self,abs_zero]
  unfold spectralTranslationL1
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hs']
  have hb : ∀ x, |f (x+t)-f x|≤ω := by
    intro x
    apply hmod
    simpa using ht
  have he := norm_setIntegral_le_of_norm_le_const
    (f:=fun x : ℝ=>|f (x+t)-f x|) (s:=Icc (-R-1) (R+1)) (μ:=volume) (C:=ω)
    (by simp) (fun x _ => by simpa using hb x)
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _=>abs_nonneg _))] at he
  rw [Real.volume_real_Icc_of_le (by linarith : -R-1≤R+1)] at he
  nlinarith

end BlockBand.Counting
