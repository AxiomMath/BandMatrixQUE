module
public import BlockBand.GaussianBulk.GraftedResolventPieces

/-!
# The resolvent integral along the central level graph

On a central level graph of positive height, the resolvent form `dz/(z - p)` for real `p` is
curve integrable, with integral the difference of principal logarithms at the endpoints.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open Set MeasureTheory
open scoped unitInterval

/-- If the level height is positive on `[a, b]`, the resolvent form is curve integrable on the
graph arc and its integral is `log(z_b - p) - log(z_a - p)` (principal logarithm). -/
theorem actualLevelGraphPath_resolvent_log {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t a b p : ℝ) (ht : 0 < t) (hab : a ≤ b)
    (hheight : ∀ x ∈ Icc a b, 0 < levelHeight d t x) :
    CurveIntegrable (graftedResolventForm p) (actualLevelGraphPath hN d t a b ht) ∧
      curveIntegral (graftedResolventForm p) (actualLevelGraphPath hN d t a b ht) =
        Complex.log (actualLevelGraphPoint d t b-(p : ℂ))-
          Complex.log (actualLevelGraphPoint d t a-(p : ℂ)) := by
  let f : ℝ → ℂ := fun s => actualLevelGraphPoint d t (AffineMap.lineMap a b s)
  let f' : ℝ → ℂ := fun s => (b-a) •
    deriv (actualLevelGraphPoint d t) (AffineMap.lineMap a b s)
  have hp (s : ℝ) (hs : s ∈ Icc 0 1) : AffineMap.lineMap a b s ∈ Icc a b := by
    have hh : (Path.segment a b) ⟨s,hs⟩ ∈ range (Path.segment a b) := mem_range_self _
    rw [Path.range_segment,segment_eq_Icc hab] at hh
    exact hh
  have hactive (s : ℝ) (hs : s ∈ Icc 0 1) :
      LevelActive d t (AffineMap.lineMap a b s) :=
    (levelHeight_pos_iff hN d t _ ht).mp (hheight _ (hp s hs))
  have hG : Continuous (actualLevelGraphPoint d t) := by
    unfold actualLevelGraphPoint
    exact Complex.continuous_ofReal.add
      ((Complex.continuous_ofReal.comp (levelHeight_continuous hN d t ht)).mul continuous_const)
  have hf : ContinuousOn f (Icc 0 1) := by dsimp [f];fun_prop
  have hdf (s : ℝ) (hs : s ∈ Icc 0 1) : HasDerivAt f (f' s) s := by
    exact ((hasDerivAt_actualLevelGraphPoint hN d t _ ht (hactive s hs)).differentiableAt.hasDerivAt).scomp s AffineMap.hasDerivAt_lineMap
  have hC := (actualLevelGraphPoint_contDiffOn_active hN d t ht).continuousOn_deriv_of_isOpen
    (isOpen_levelActive hN d t ht) (by norm_num)
  have hdf' : ContinuousOn f' (Icc 0 1) :=
    (hC.comp (by fun_prop) hactive).const_smul (b-a)
  have hs (s : ℝ) (hs : s ∈ Icc 0 1) :
      (1 : ℂ)*(f s-(p : ℂ)) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    have hh := (hheight _ (hp s hs)).ne'
    simpa [f,actualLevelGraphPoint] using hh
  have hh := curveIntegral_ofLine_resolvent_log f f' p 1 one_ne_zero hf hdf hdf' hs
  have h0 : actualLevelGraphPoint d t a = f 0 := by simp [f]
  have h1 : actualLevelGraphPoint d t b = f 1 := by simp [f]
  have he : (Path.ofLine hf rfl rfl).cast h0 h1 = actualLevelGraphPath hN d t a b ht := by
    ext s
    rfl
  constructor
  · rw [← he]
    exact hh.1.cast h0 h1
  · rw [← he,curveIntegral_cast,hh.2,← h0,← h1]
    simp only [one_mul]

/-- The same, on an interval within `η²/(4√tmax)` of a saddle of height at least `η`. -/
theorem actualLevelGraphPath_resolvent_log_bulk {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t tmax eta x₀ a b p : ℝ) (ht : 0 < t)
    (htmax : t ≤ tmax) (heta : 0 < eta) (hheight : eta ≤ levelHeight d t x₀)
    (hab : a ≤ b) (hclose : ∀ x ∈ Icc a b, |x-x₀| ≤ eta^2/(4*Real.sqrt tmax)) :
    CurveIntegrable (graftedResolventForm p) (actualLevelGraphPath hN d t a b ht) ∧
      curveIntegral (graftedResolventForm p) (actualLevelGraphPath hN d t a b ht) =
        Complex.log (actualLevelGraphPoint d t b-(p : ℂ))-
          Complex.log (actualLevelGraphPoint d t a-(p : ℂ)) := by
  apply actualLevelGraphPath_resolvent_log hN d t a b p ht hab
  intro x hx
  have hh := levelHeight_neighborhood_lower hN d t tmax eta x₀ x
    ht htmax heta hheight (hclose x hx)
  linarith

end BlockBand.GaussianBulk
