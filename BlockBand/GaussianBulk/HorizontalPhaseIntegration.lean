module
public import BlockBand.GaussianBulk.LevelHorizontalBarrier
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Integrals of the horizontal phase weight

The modulus of the Johansson integrand along the level graph near the saddle is controlled by
`horizontalPhaseWeight`. Using the horizontal barrier for the level action, its integral over
the core `|a| ≤ r` is `O(n^{-1/2})` and its tail `|a| ≥ R` is exponentially small, uniformly in
`N` and the source `d`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open MeasureTheory Filter Set

/-- The quadratic coefficient `η²/(2 tmax²)` of the horizontal barrier. -/
def horizontalGaussianCoefficient (η tmax : ℝ) : ℝ := η^2/(2*tmax^2)
/-- The local radius `η²/(4√tmax)` of the horizontal barrier. -/
def horizontalGaussianRadius (η tmax : ℝ) : ℝ := η^2/(4*Real.sqrt tmax)
/-- The weight `exp(-n(Λ(x₀+a) - Λ(x₀)) + k|a|)` along the level graph, `Λ` the level action;
`a` is the horizontal offset from `x₀`. -/
def horizontalPhaseWeight {N : ℕ} (d : Fin N → ℝ)
    (E t x₀ n k a : ℝ) : ℝ :=
  Real.exp (-n*(levelAction d E t (x₀+a)-levelAction d E t x₀)+k*|a|)

private theorem integrable_exp_abs (α : ℝ) (hα : 0 < α) :
    Integrable (fun a : ℝ => Real.exp (-α*|a|)) := by
  rw [← integrableOn_univ,← Iic_union_Ioi (a := (0 : ℝ)),integrableOn_union]
  constructor
  · apply (integrableOn_exp_mul_Iic hα 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Iic] with a ha
    rw [abs_of_nonpos ha]
    congr 1
    ring
  · apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos hα) 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    rw [abs_of_pos ha]

private theorem integral_exp_abs (α : ℝ) (hα : 0 < α) :
    (∫ a : ℝ, Real.exp (-α*|a|)) = 2/α := by
  have hf := integrable_exp_abs α hα
  rw [← integral_add_compl measurableSet_Iic hf,compl_Iic]
  have hleft : (∫ a : ℝ in Iic 0, Real.exp (-α*|a|)) = 1/α := by
    calc
      _ = ∫ a : ℝ in Iic 0, Real.exp (α*a) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Iic] with a ha
        rw [abs_of_nonpos ha]
        congr 1
        ring
      _ = _ := by rw [integral_exp_mul_Iic hα];simp
  have hright : (∫ a : ℝ in Ioi 0, Real.exp (-α*|a|)) = 1/α := by
    calc
      _ = ∫ a : ℝ in Ioi 0, Real.exp (-α*a) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
        rw [abs_of_pos ha]
      _ = _ := by rw [integral_exp_mul_Ioi (neg_neg_of_pos hα)];simp
  rw [hleft,hright]
  ring

private theorem min_square_linear_lower (a r : ℝ) :
    r*|a|-r^2/4 ≤ min (a^2) (r*|a|) := by
  apply le_min
  · nlinarith [sq_nonneg (|a|-r/2),sq_abs a]
  · nlinarith [sq_nonneg r]

private theorem linear_abs_quadratic (A k a : ℝ) (hA : 0 < A) :
    k*|a| ≤ (A/2)*a^2+k^2/(2*A) := by
  apply (mul_le_mul_iff_left₀ (show 0 < 2*A by positivity)).mp
  have he : ((A/2)*a^2+k^2/(2*A))*(2*A)= A^2*a^2+k^2 := by
    field_simp [ne_of_gt hA]
  rw [he]
  nlinarith [sq_nonneg (A*|a|-k),sq_abs a]

private theorem horizontalPhaseWeight_measurable {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t x₀ n k : ℝ) (ht : 0 < t) :
    Measurable (horizontalPhaseWeight d E t x₀ n k) := by
  have hA : Continuous (levelAction d E t) :=
    (show Differentiable ℝ (levelAction d E t) from
      fun x => (hasDerivAt_levelAction_global hN d E t x ht).differentiableAt).continuous
  unfold horizontalPhaseWeight
  fun_prop

/-- The horizontal weight is Lebesgue integrable when the Gaussian exponent dominates the linear
growth: `k < n C r` with `C`, `r` the barrier coefficient and radius. -/
theorem integrable_horizontalPhaseWeight {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t x₀ η tmax n k : ℝ) (ht : 0 < t)
    (htmax : t ≤ tmax) (hη : 0 < η) (hheight : η ≤ levelHeight d t x₀)
    (hpsi : levelPsi d t x₀=E) (hn : 0 < n)
    (hscale : k < n*horizontalGaussianCoefficient η tmax*horizontalGaussianRadius η tmax) :
    Integrable (horizontalPhaseWeight d E t x₀ n k) := by
  let C := horizontalGaussianCoefficient η tmax
  let r := horizontalGaussianRadius η tmax
  let α := n*C*r-k
  have hC : 0 < C := by
    have htM : 0 < tmax := lt_of_lt_of_le ht htmax
    dsimp only [C,horizontalGaussianCoefficient]
    positivity
  have hα : 0 < α := sub_pos.mpr hscale
  have hg : Integrable (fun a : ℝ => Real.exp (n*C*r^2/4)*Real.exp (-α*|a|)) :=
    (integrable_exp_abs α hα).const_mul _
  apply hg.mono'
  · exact (horizontalPhaseWeight_measurable hN d E t x₀ n k ht).aestronglyMeasurable
  · filter_upwards with a
    have hb := levelAction_horizontal_barrier hN d E t tmax η x₀ (x₀+a) ht htmax hη hheight hpsi
    simp only [add_sub_cancel_left] at hb
    have hl := mul_le_mul_of_nonneg_left (min_square_linear_lower a r) hC.le
    have hd : C*(r*|a|-r^2/4) ≤ levelAction d E t (x₀+a)-levelAction d E t x₀ :=
      le_trans hl hb
    rw [Real.norm_eq_abs]
    unfold horizontalPhaseWeight
    rw [abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hd hn.le
    dsimp only [α]
    nlinarith

/-- The integral of the horizontal weight over the core `|a| ≤ r` is at most an explicit
constant times `n^{-1/2}`. -/
theorem integral_horizontalPhaseWeight_core_le {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t x₀ η tmax n k : ℝ) (ht : 0 < t)
    (htmax : t ≤ tmax) (hη : 0 < η) (hheight : η ≤ levelHeight d t x₀)
    (hpsi : levelPsi d t x₀=E) (hn : 0 < n) :
    (∫ a in {a : ℝ | |a| ≤ horizontalGaussianRadius η tmax},
      horizontalPhaseWeight d E t x₀ n k a) ≤
      Real.exp (k^2/(2*n*horizontalGaussianCoefficient η tmax))*
        Real.sqrt (Real.pi/(n*horizontalGaussianCoefficient η tmax/2)) := by
  let C := horizontalGaussianCoefficient η tmax
  let r := horizontalGaussianRadius η tmax
  let S : Set ℝ := {a | |a| ≤ r}
  let D := Real.exp (k^2/(2*n*C))
  let g : ℝ → ℝ := fun a => D*Real.exp (-(n*C/2)*a^2)
  have hS : MeasurableSet S := (isClosed_le continuous_abs continuous_const).measurableSet
  have hC : 0 < C := by
    have htM : 0 < tmax := lt_of_lt_of_le ht htmax
    dsimp only [C,horizontalGaussianCoefficient]
    positivity
  have hg : Integrable g :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < n*C/2)).const_mul D
  have hb : ∀ᵐ a ∂volume.restrict S, horizontalPhaseWeight d E t x₀ n k a ≤ g a := by
    filter_upwards [ae_restrict_mem hS] with a ha
    have hx := levelAction_horizontal_barrier hN d E t tmax η x₀ (x₀+a) ht htmax hη hheight hpsi
    simp only [add_sub_cancel_left] at hx
    have hsq : a^2 ≤ r*|a| := by
      have hh := mul_le_mul_of_nonneg_right ha (abs_nonneg a)
      nlinarith [sq_abs a]
    change C*min (a^2) (r*|a|) ≤ levelAction d E t (x₀+a)-levelAction d E t x₀ at hx
    rw [min_eq_left hsq] at hx
    have hmain := mul_le_mul_of_nonneg_left hx hn.le
    have hlin := linear_abs_quadratic (n*C) k a (mul_pos hn hC)
    unfold horizontalPhaseWeight
    dsimp only [g,D]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he : k^2/(2*(n*C))=k^2/(2*n*C) := by ring
    rw [he] at hlin
    nlinarith
  have hf : IntegrableOn (horizontalPhaseWeight d E t x₀ n k) S := by
    apply hg.integrableOn.mono'
    · exact (horizontalPhaseWeight_measurable hN d E t x₀ n k ht).aestronglyMeasurable
    · filter_upwards [hb] with a ha
      rw [Real.norm_eq_abs]
      unfold horizontalPhaseWeight
      rw [abs_of_pos (Real.exp_pos _)]
      exact ha
  have hm := integral_mono_ae hf hg.integrableOn hb
  have hwhole : (∫ a in S, g a) ≤ ∫ a, g a :=
    integral_mono_measure Measure.restrict_le_self
      (by filter_upwards with a; dsimp only [g,D];positivity) hg
  have he : (∫ a, g a)=D*Real.sqrt (Real.pi/(n*C/2)) := by
    rw [show g=(fun a => D*Real.exp (-(n*C/2)*a^2)) from rfl,
      integral_const_mul,integral_gaussian]
  exact le_trans hm (he ▸ hwhole)

/-- The integral of the horizontal weight over the tail `|a| ≥ R ≥ r` is exponentially small,
uniformly in `N` and `d`, when `k < n C r`. -/
theorem integral_horizontalPhaseWeight_tail_le {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t x₀ η tmax n k R : ℝ) (ht : 0 < t)
    (htmax : t ≤ tmax) (hη : 0 < η) (hheight : η ≤ levelHeight d t x₀)
    (hpsi : levelPsi d t x₀=E) (hn : 0 < n)
    (hscale : k < n*horizontalGaussianCoefficient η tmax*horizontalGaussianRadius η tmax)
    (hR : horizontalGaussianRadius η tmax ≤ R) :
    (∫ a in {a : ℝ | R ≤ |a|}, horizontalPhaseWeight d E t x₀ n k a) ≤
      4*Real.exp (-(n*horizontalGaussianCoefficient η tmax*horizontalGaussianRadius η tmax-k)*R/2)/
        (n*horizontalGaussianCoefficient η tmax*horizontalGaussianRadius η tmax-k) := by
  let C := horizontalGaussianCoefficient η tmax
  let r := horizontalGaussianRadius η tmax
  let α := n*C*r-k
  let S : Set ℝ := {a | R ≤ |a|}
  let D := Real.exp (-α*R/2)
  let g : ℝ → ℝ := fun a => D*Real.exp (-(α/2)*|a|)
  have hS : MeasurableSet S := (isClosed_le continuous_const continuous_abs).measurableSet
  have hα : 0 < α := sub_pos.mpr hscale
  have hg : Integrable g := (integrable_exp_abs (α/2) (by positivity)).const_mul D
  have hf := integrable_horizontalPhaseWeight hN d E t x₀ η tmax n k ht htmax hη hheight hpsi hn hscale
  have hb : ∀ᵐ a ∂volume.restrict S, horizontalPhaseWeight d E t x₀ n k a ≤ g a := by
    filter_upwards [ae_restrict_mem hS] with a ha
    have hmin : min (a^2) (r*|a|)=r*|a| := by
      apply min_eq_right
      have hh := mul_le_mul_of_nonneg_right (le_trans hR ha) (abs_nonneg a)
      nlinarith [sq_abs a]
    have hx := levelAction_horizontal_barrier hN d E t tmax η x₀ (x₀+a) ht htmax hη hheight hpsi
    simp only [add_sub_cancel_left] at hx
    change C*min (a^2) (r*|a|) ≤ levelAction d E t (x₀+a)-levelAction d E t x₀ at hx
    rw [hmin] at hx
    have hmain := mul_le_mul_of_nonneg_left hx hn.le
    unfold horizontalPhaseWeight
    dsimp only [g,D]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hcut := mul_le_mul_of_nonneg_left ha (show 0 ≤ α/2 by positivity)
    dsimp only [α] at hcut ⊢
    nlinarith
  have hm := integral_mono_ae hf.integrableOn hg.integrableOn hb
  have hwhole : (∫ a in S, g a) ≤ ∫ a, g a :=
    integral_mono_measure Measure.restrict_le_self
      (by filter_upwards with a; dsimp only [g,D];positivity) hg
  have he : (∫ a, g a)=4*D/α := by
    rw [show g=(fun a => D*Real.exp (-(α/2)*|a|)) from rfl,
      integral_const_mul,integral_exp_abs (α/2) (by positivity)]
    field_simp [ne_of_gt hα]
    ring
  exact le_trans hm (he ▸ hwhole)

/-- Integrability of the horizontal weight at a solution of the finite MDE, with height
`η = tmin · v`. -/
theorem integrable_horizontalPhaseWeight_at_MDE {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t tmin tmax vbulk k : ℝ) (m : ℂ)
    (htmin : 0 < tmin) (ht : tmin ≤ t) (htmax : t ≤ tmax)
    (hv : 0 < vbulk) (hm : vbulk ≤ m.im) (hMDE : FiniteMDE d E t m)
    (hscale : k < (N : ℝ)*horizontalGaussianCoefficient (tmin*vbulk) tmax*
      horizontalGaussianRadius (tmin*vbulk) tmax) :
    Integrable (horizontalPhaseWeight d E t (saddlePoint E t m).re (N : ℝ) k) := by
  have htp := lt_of_lt_of_le htmin ht
  have hmp := lt_of_lt_of_le hv hm
  apply integrable_horizontalPhaseWeight hN d E t (saddlePoint E t m).re (tmin*vbulk) tmax
    (N : ℝ) k htp htmax (mul_pos htmin hv) _
    (levelPsi_at_saddle hN d E t m htp hmp hMDE) (by exact_mod_cast hN) hscale
  rw [levelHeight_at_saddle hN d E t m htp hmp hMDE]
  exact saddlePoint_im_lower E t tmin vbulk m htmin ht hv.le hm

end BlockBand.GaussianBulk
