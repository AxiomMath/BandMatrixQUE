module
public import BlockBand.GaussianBulk.GraftedLevelContour
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Regularity of the central level graph

The level height `y(x)` is C¹ on the open set where it is positive, so the central graph
`x ↦ x + i y(x)` is C¹ there, with speed at most `1 + √tmax/η` where `y ≥ η`. Near a saddle
of height at least `η` this gives the arclength bound `(b-a)(1 + 2√tmax/η)`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open Set Filter Topology MeasureTheory

/-- The derivative of the level height is continuous at every active point. -/
theorem levelHeight_deriv_continuousAt {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) (hx : LevelActive d t x) :
    ContinuousAt (deriv (levelHeight d t)) x := by
  have hy := (levelHeight_root hN d t x ht hx).1
  have hY := (levelHeight_continuous hN d t ht).continuousAt (x := x)
  have hpair : ContinuousAt (fun a => (a,levelHeight d t a)) x :=
    continuousAt_id.prodMk hY
  have hA := (levelA1_continuousAt d (x,levelHeight d t x) hy).comp (f := fun a : ℝ => (a,levelHeight d t a)) hpair
  have hB := (levelB_continuousAt d (x,levelHeight d t x) hy).comp (f := fun a : ℝ => (a,levelHeight d t a)) hpair
  have hden : levelHeight d t x*levelB d x (levelHeight d t x) ≠ 0 :=
    mul_ne_zero (ne_of_gt hy) (ne_of_gt (levelB_pos hN d x _ hy))
  have hc := hA.neg.div (hY.mul hB) hden
  apply hc.congr_of_eventuallyEq
  have hactive := (isOpen_levelActive hN d t ht).mem_nhds hx
  filter_upwards [hactive] with a ha
  exact (hasDerivAt_levelHeight hN d t a ht ha).deriv

/-- The level height is C¹ on its open active domain. -/
theorem levelHeight_contDiffOn_active {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t : ℝ) (ht : 0 < t) :
    ContDiffOn ℝ 1 (levelHeight d t) {x | LevelActive d t x} := by
  rw [show (1 : WithTop ℕ∞) = 0+1 by rfl,
    contDiffOn_succ_iff_deriv_of_isOpen (isOpen_levelActive hN d t ht)]
  refine ⟨?_,?_,?_⟩
  · intro x hx
    exact (hasDerivAt_levelHeight hN d t x ht hx).differentiableAt.differentiableWithinAt
  · intro h
    exact (by simp at h)
  · exact contDiffOn_zero.mpr (fun x hx =>
      (levelHeight_deriv_continuousAt hN d t x ht hx).continuousWithinAt)

/-- The central graph `x ↦ x + i y(x)` is C¹ on the open active domain. -/
theorem actualLevelGraphPoint_contDiffOn_active {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t : ℝ) (ht : 0 < t) :
    ContDiffOn ℝ 1 (actualLevelGraphPoint d t) {x | LevelActive d t x} := by
  unfold actualLevelGraphPoint
  exact Complex.ofRealCLM.contDiff.contDiffOn.add
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn
      (levelHeight_contDiffOn_active hN d t ht)).mul contDiffOn_const)

/-- The derivative of the central graph is `1 + i y'(x)`. -/
theorem hasDerivAt_actualLevelGraphPoint {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t x : ℝ) (ht : 0 < t) (hx : LevelActive d t x) :
    HasDerivAt (actualLevelGraphPoint d t)
      (1+((deriv (levelHeight d t) x : ℝ) : ℂ)*Complex.I) x := by
  have hY := (hasDerivAt_levelHeight hN d t x ht hx).differentiableAt.hasDerivAt
  exact (Complex.ofRealCLM.hasDerivAt.add (hY.ofReal_comp.mul_const Complex.I))

/-- The speed of the central graph is at most `1 + √tmax/η` where the level height is at least `η`. -/
theorem actualLevelGraphPoint_speed_le {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t tmax eta x : ℝ) (ht : 0 < t) (htmax : t ≤ tmax)
    (heta : 0 < eta) (hheight : eta ≤ levelHeight d t x) :
    ‖deriv (actualLevelGraphPoint d t) x‖ ≤ 1+Real.sqrt tmax/eta := by
  have hx := (levelHeight_pos_iff hN d t x ht).mp (lt_of_lt_of_le heta hheight)
  rw [(hasDerivAt_actualLevelGraphPoint hN d t x ht hx).deriv]
  have hb := norm_add_le (1 : ℂ) (((deriv (levelHeight d t) x : ℝ) : ℂ)*Complex.I)
  simp only [norm_one,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,
    Real.norm_eq_abs] at hb
  exact le_trans hb (add_le_add_right
    (abs_deriv_levelHeight_uniform hN d t x eta tmax ht htmax heta hheight) 1)

/-- On an interval within `η²/(4√tmax)` of a saddle of height at least `η`, the speed of the
central graph is interval integrable with arclength at most `(b-a)(1 + 2√tmax/η)`. -/
theorem actualLevelGraphPoint_length_bound {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t tmax eta x₀ a b : ℝ) (ht : 0 < t)
    (htmax : t ≤ tmax) (heta : 0 < eta) (hheight : eta ≤ levelHeight d t x₀)
    (hab : a ≤ b)
    (hclose : ∀ x ∈ Icc a b, |x-x₀| ≤ eta^2/(4*Real.sqrt tmax)) :
    IntervalIntegrable (fun x => ‖deriv (actualLevelGraphPoint d t) x‖) volume a b ∧
      (∫ x in a..b, ‖deriv (actualLevelGraphPoint d t) x‖) ≤
        (b-a)*(1+2*Real.sqrt tmax/eta) := by
  have hstrip (x : ℝ) (hx : x ∈ Icc a b) : eta/2 ≤ levelHeight d t x :=
    levelHeight_neighborhood_lower hN d t tmax eta x₀ x ht htmax heta hheight (hclose x hx)
  have hactive : Icc a b ⊆ {x | LevelActive d t x} := by
    intro x hx
    exact (levelHeight_pos_iff hN d t x ht).mp (by linarith [hstrip x hx])
  have hcont : ContinuousOn (deriv (actualLevelGraphPoint d t)) (Icc a b) :=
    ((actualLevelGraphPoint_contDiffOn_active hN d t ht).continuousOn_deriv_of_isOpen
      (isOpen_levelActive hN d t ht) (by norm_num)).mono hactive
  constructor
  · exact hcont.norm.intervalIntegrable_of_Icc hab
  · have hbnd (x : ℝ) (hx : x ∈ Icc a b) :
        ‖deriv (actualLevelGraphPoint d t) x‖ ≤ 1+2*Real.sqrt tmax/eta := by
      have hs := actualLevelGraphPoint_speed_le hN d t tmax (eta/2) x ht htmax
        (by linarith) (hstrip x hx)
      convert hs using 1
      ring
    have hb' := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := 1+2*Real.sqrt tmax/eta)
      (f := fun x => ‖deriv (actualLevelGraphPoint d t) x‖)
      (fun x hx => by
        rw [uIoc_of_le hab] at hx
        simpa only [Real.norm_eq_abs,abs_norm] using hbnd x ⟨le_of_lt hx.1,hx.2⟩)
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] at hb'
    exact le_trans (le_abs_self _) (by simpa only [mul_comm] using hb')

end BlockBand.GaussianBulk
