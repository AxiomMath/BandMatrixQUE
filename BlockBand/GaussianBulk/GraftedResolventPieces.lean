module
public import BlockBand.GaussianBulk.GraftedResolventPrimitives
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Resolvent integrals on reflected paths and polygonal meshes

Complex conjugation of a path conjugates its resolvent integral, and on segments and
polygonal meshes in the upper half-plane the resolvent form `dz/(z - p)` has an explicit
logarithmic primitive.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open Set MeasureTheory
open scoped unitInterval

/-- Reflection conjugates the resolvent integrand pointwise. -/
theorem graftedResolvent_curveIntegralFun_conj {a b : ℂ} (p : ℝ)
    (γ : Path a b) :
    curveIntegralFun (graftedResolventForm p) (γ.map Complex.continuous_conj) =
      fun s => star (curveIntegralFun (graftedResolventForm p) γ s) := by
  have he : ((γ.map Complex.continuous_conj).extend : ℝ → ℂ) =
      fun s => star (γ.extend s) := rfl
  funext s
  rw [curveIntegralFun_def,he,derivWithin.star,curveIntegralFun_def]
  simp [graftedResolventForm,smul_apply,star_mul,mul_comm]

/-- The reflected path is resolvent-integrable whenever the original path is. -/
theorem graftedResolvent_curveIntegrable_conj {a b : ℂ} (p : ℝ)
    (γ : Path a b) (hγ : CurveIntegrable (graftedResolventForm p) γ) :
    CurveIntegrable (graftedResolventForm p) (γ.map Complex.continuous_conj) := by
  unfold CurveIntegrable at hγ ⊢
  rw [graftedResolvent_curveIntegralFun_conj]
  exact ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp hγ.1,
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hγ.2⟩

/-- The resolvent integral over the reflected path is the conjugate of the original one. -/
theorem graftedResolvent_curveIntegral_conj {a b : ℂ} (p : ℝ) (γ : Path a b) :
    curveIntegral (graftedResolventForm p) (γ.map Complex.continuous_conj) =
      star (curveIntegral (graftedResolventForm p) γ) := by
  rw [curveIntegral_def,graftedResolvent_curveIntegralFun_conj,curveIntegral_def]
  exact intervalIntegral.intervalIntegral_conj

/-- On a segment along which `q(z - p)` stays in the slit plane, the resolvent form is curve
integrable with integral `log(q(b - p)) - log(q(a - p))`. -/
theorem graftedResolvent_segment_log (p : ℝ) (q : ℂ) (hq : q ≠ 0) (a b : ℂ)
    (hslit : ∀ z ∈ range (Path.segment a b), q*(z-(p : ℂ)) ∈ Complex.slitPlane) :
    CurveIntegrable (graftedResolventForm p) (Path.segment a b) ∧
      curveIntegral (graftedResolventForm p) (Path.segment a b) =
        Complex.log (q*(b-(p : ℂ)))-Complex.log (q*(a-(p : ℂ))) := by
  let f : ℝ → ℂ := AffineMap.lineMap a b
  have hf : ContinuousOn f (Icc 0 1) := by dsimp [f];fun_prop
  have hdf (s : ℝ) (_ : s ∈ Icc 0 1) : HasDerivAt f (b-a) s :=
    AffineMap.hasDerivAt_lineMap
  have hs (s : ℝ) (hs : s ∈ Icc 0 1) : q*(f s-(p : ℂ)) ∈ Complex.slitPlane :=
    hslit _ ⟨⟨s,hs⟩,rfl⟩
  have hh := curveIntegral_ofLine_resolvent_log f (fun _ => b-a) p q hq
    hf hdf continuousOn_const hs
  have h0 : a = f 0 := by simp [f]
  have h1 : b = f 1 := by simp [f]
  have he : (Path.ofLine hf rfl rfl).cast h0 h1 = Path.segment a b := by
    ext s
    rfl
  constructor
  · rw [← he]
    exact hh.1.cast h0 h1
  · rw [← he,curveIntegral_cast,hh.2,← h0,← h1]

/-- A segment in the open upper half-plane has the principal-log primitive. -/
theorem graftedResolvent_upper_segment_log (p : ℝ) (a b : ℂ)
    (ha : 0 < a.im) (hb : 0 < b.im) :
    CurveIntegrable (graftedResolventForm p) (Path.segment a b) ∧
      curveIntegral (graftedResolventForm p) (Path.segment a b) =
        Complex.log (b-(p : ℂ))-Complex.log (a-(p : ℂ)) := by
  have hs (z : ℂ) (hz : z ∈ range (Path.segment a b)) :
      (1 : ℂ)*(z-(p : ℂ)) ∈ Complex.slitPlane := by
    obtain ⟨s,rfl⟩ := hz
    apply Complex.mem_slitPlane_iff.mpr
    right
    simp only [one_mul,Complex.sub_im,Complex.ofReal_im,sub_zero,
      Path.segment_apply,AffineMap.lineMap_apply_module,Complex.add_im,
      Complex.smul_im,smul_eq_mul]
    have hn := mul_nonneg (sub_nonneg.mpr s.property.2) ha.le
    by_cases h0 : (s : ℝ) = 0
    · simpa only [h0,sub_zero,one_mul,zero_mul,add_zero] using ha.ne'
    · exact (add_pos_of_nonneg_of_pos hn
        (mul_pos (lt_of_le_of_ne s.property.1 (Ne.symm h0)) hb)).ne'
  simpa only [one_mul] using graftedResolvent_segment_log p 1 one_ne_zero a b hs

/-- The resolvent integral over a polygonal mesh in the upper half-plane telescopes to the
difference of principal logarithms at its endpoints. -/
theorem graftedResolvent_finite_upper_mesh_log (p : ℝ) (v : ℕ → ℂ) (M : ℕ)
    (hv : ∀ j ≤ M, 0 < (v j).im) :
    CurveIntegrable (graftedResolventForm p) (finiteLevelMeshPath v M) ∧
      curveIntegral (graftedResolventForm p) (finiteLevelMeshPath v M) =
        Complex.log (v M-(p : ℂ))-Complex.log (v 0-(p : ℂ)) := by
  induction M with
  | zero => simp [finiteLevelMeshPath]
  | succ M ih =>
    have hm := ih (fun j hj => hv j (by omega))
    have hs := graftedResolvent_upper_segment_log p (v M) (v (M+1))
      (hv M (by omega)) (hv (M+1) le_rfl)
    constructor
    · exact hm.1.trans hs.1
    · change curveIntegral (graftedResolventForm p)
        ((finiteLevelMeshPath v M).trans (Path.segment (v M) (v (M+1)))) = _
      rw [curveIntegral_trans hm.1 hs.1,hm.2,hs.2]
      ring

end BlockBand.GaussianBulk
