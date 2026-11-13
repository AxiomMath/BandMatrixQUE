module

public import BlockBand.GaussianBulk.ExternalSineRemainderPhase

/-!
# Exponential smallness away from the central graph

The horizontal barrier for the action holds on the level graph `x ± i y(x)`; the
loop's outer parts are raised meshes, vertical grafts and closing segments, whose points are
`x + iP` with `y(x) ≤ |P| ≤ y(x) + 2√t/N`. `levelAction_sub_verticalRealAction_le` proves that
on such points `Re S` is at most `4/N` below the graph action (raising only lowers the quadratic
term), so the horizontal barrier (`levelAction_horizontal_barrier`) holds there with an
additive loss `4/N` (`verticalRealAction_outer_drop`).

`remainderMajorant_le_outer`: if `r ≤ |Re z - x₀|` (`r = graftedCentralRadius tmax η`) and the
loss is `≤ 4/N`, then `remainderMajorant z ≤ outerDecayConstant`, which is
`e⁴ · verticalMassConstant / r · exp(-(N c r - k) r)`, `c = η²/(2 tmax²)`, `k = |ξ|/(tρ)`,
provided `k ≤ N c r`.

Domain: `N ≥ 1`, `0 < t ≤ tmax`, `ρ > 0`, a positive level root `y₀ ≥ η > 0` at `x₀` with
`levelPsi d t x₀ = E`, arbitrary real `d`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open Set MeasureTheory Filter Topology

/-- Points above the graph by at most `2√t/N` lose at most `4/N` of the graph action. -/
theorem levelAction_sub_verticalRealAction_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x P : ℝ) (ht : 0 < t) (hlo : levelHeight d t x ≤ |P|)
    (hhi : |P| ≤ levelHeight d t x + 2*Real.sqrt t/N) :
    levelAction d E t x - verticalRealAction d E t x P ≤ 4/N := by
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  have hl := (verticalRealAction_raised_graph_loss hN d E t x |P| ht hlo).2
  rw [verticalRealAction_abs] at hl
  have hy := levelHeight_bounds hN d t x ht
  set y := levelHeight d t x
  have hs := Real.sqrt_nonneg t
  have hst : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hP2 : |P|^2 - y^2 ≤ (2*Real.sqrt t/N) * (2*Real.sqrt t + 2*Real.sqrt t/N) := by
    have h1 : 0 ≤ |P| - y := by linarith
    have h2 : |P| - y ≤ 2*Real.sqrt t/N := by linarith
    have h3 : |P| + y ≤ 2*Real.sqrt t + 2*Real.sqrt t/N := by linarith
    have h4 : 0 ≤ |P| + y := by linarith
    have : |P|^2 - y^2 = (|P| - y)*(|P| + y) := by ring
    rw [this]
    exact mul_le_mul h2 h3 h4 (by positivity)
  have hb : (2*Real.sqrt t/N) * (2*Real.sqrt t + 2*Real.sqrt t/N) / (2*t) ≤ 4/N := by
    rw [div_le_div_iff₀ (by positivity) hN0]
    have e : (2*Real.sqrt t/N) * (2*Real.sqrt t + 2*Real.sqrt t/N) * N =
        4*t + 4*t/N := by
      field_simp
      rw [hst]
      ring
    rw [e]
    have : 4*t/N ≤ 4*t := div_le_self (by positivity) hNr
    nlinarith
  calc levelAction d E t x - verticalRealAction d E t x P ≤ (|P|^2 - y^2)/(2*t) := by
        simpa [sq_abs] using hl
    _ ≤ (2*Real.sqrt t/N) * (2*Real.sqrt t + 2*Real.sqrt t/N) / (2*t) :=
        div_le_div_of_nonneg_right hP2 (by positivity)
    _ ≤ 4/N := hb

/-- **Horizontal barrier on raised points, with loss.** For a point
`z = x + iP` with action loss `≤ 4/N` relative to the graph and `r ≤ |x - x₀|`:
`Re S(z) - Re S(z₀) ≥ c r |x - x₀| - 4/N`, `c = η²/(2 tmax²)`. -/
theorem verticalRealAction_outer_drop {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t tmax η x₀ y₀ : ℝ) (ht : 0 < t) (htmax : t ≤ tmax) (hη : 0 < η)
    (hr : PositiveLevelRoot d t x₀ y₀) (hheight : η ≤ y₀) (hpsi : levelPsi d t x₀ = E)
    (z : ℂ) (hzr : graftedCentralRadius tmax η ≤ |z.re - x₀|)
    (hloss : levelAction d E t z.re - verticalRealAction d E t z.re z.im ≤ 4/N) :
    (η^2/(2*tmax^2)) * graftedCentralRadius tmax η * |z.re - x₀| - 4/N ≤
      verticalRealAction d E t z.re z.im - verticalRealAction d E t x₀ y₀ := by
  have hy := levelHeight_eq_of_root hN d t x₀ y₀ ht hr
  have hb := levelAction_horizontal_barrier hN d E t tmax η x₀ z.re ht htmax hη
    (by rw [hy]; exact hheight) hpsi
  have hid : levelAction d E t x₀ = verticalRealAction d E t x₀ y₀ := by
    rw [levelAction_eq_saddlePhase_re, verticalRealAction_eq_saddlePhase_re, hy]
  set r := graftedCentralRadius tmax η
  set a := |z.re - x₀|
  have htm : 0 < tmax := lt_of_lt_of_le ht htmax
  have hr0 : 0 < r := by simp only [r, graftedCentralRadius]; positivity
  have hδ : η^2/(4*Real.sqrt tmax) = 2*r := by simp only [r, graftedCentralRadius]; ring
  rw [hδ] at hb
  have hmin : r * a ≤ min ((z.re - x₀)^2) (2*r*a) := by
    apply le_min
    · rw [← sq_abs]; nlinarith [abs_nonneg (z.re - x₀)]
    · nlinarith [abs_nonneg (z.re - x₀)]
  have hc : 0 ≤ η^2/(2*tmax^2) := by positivity
  have := mul_le_mul_of_nonneg_left hmin hc
  nlinarith

/-- The exponentially small outer bound for the vertical majorant. -/
def outerDecayConstant (N : ℕ) (t tmax η rho xi : ℝ) : ℝ :=
  Real.exp 4 * verticalMassConstant η tmax / graftedCentralRadius tmax η *
    Real.exp (-((N:ℝ)*(η^2/(2*tmax^2))*graftedCentralRadius tmax η - |xi|/(t*rho)) *
      graftedCentralRadius tmax η)

/-- **Outer majorant.** Away from the central strip (`r ≤ |Re z - x₀|`) and with action loss
`≤ 4/N`, `remainderMajorant z ≤ outerDecayConstant N t tmax η ρ ξ`, provided the microscopic
rate `|ξ|/(tρ) ≤ N c r` (`N ≥ 1`). -/
theorem remainderMajorant_le_outer {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t tmax η rho x₀ y₀ xi zeta : ℝ) (ht : 0 < t) (htmax : t ≤ tmax) (hη : 0 < η)
    (hrho : 0 < rho) (hr : PositiveLevelRoot d t x₀ y₀) (hheight : η ≤ y₀)
    (hpsi : levelPsi d t x₀ = E)
    (hscale : |xi|/(t*rho) ≤ (N:ℝ)*(η^2/(2*tmax^2))*graftedCentralRadius tmax η)
    (z : ℂ) (hzr : graftedCentralRadius tmax η ≤ |z.re - x₀|)
    (hloss : levelAction d E t z.re - verticalRealAction d E t z.re z.im ≤ 4/N) :
    remainderMajorant d E t rho x₀ xi zeta z ≤ outerDecayConstant N t tmax η rho xi := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have htm : 0 < tmax := lt_of_lt_of_le ht htmax
  set r := graftedCentralRadius tmax η with hrdef
  have hr0 : 0 < r := by simp only [r, graftedCentralRadius]; positivity
  set k := |xi|/(t*rho)
  set c := η^2/(2*tmax^2)
  set Ez := Real.exp (-(N:ℝ)*(verticalRealAction d E t z.re z.im-verticalRealAction d E t x₀ y₀)+
          xi*(z.re-x₀)/(t*rho)) with hEz
  have hint := (integrable_relativeVerticalExp hN d E t x₀ y₀ η tmax (N:ℝ) ht hr hη hheight
    htmax hN0).norm
  have hmono : remainderMajorant d E t rho x₀ xi zeta z ≤
      ∫ v : ℝ, (Ez / r) * ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) v‖ := by
    unfold remainderMajorant
    refine integral_mono_of_nonneg (Eventually.of_forall fun v => by positivity)
      (hint.const_mul _) (Eventually.of_forall fun v => ?_)
    simp only
    rw [norm_gaugedJohanssonExp_factor hN d E t rho x₀ y₀ v xi zeta ht hrho z]
    have hden : r ≤ ‖((x₀:ℂ)+(v:ℂ)*Complex.I)-z‖ := by
      refine hzr.trans ((abs_sub_comm _ _).le.trans ?_)
      have := Complex.abs_re_le_norm (((x₀:ℂ)+(v:ℂ)*Complex.I)-z)
      simpa using this
    have hnum : 0 ≤ ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) v‖ * Ez := by positivity
    calc ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) v‖ * Ez / ‖((x₀:ℂ)+(v:ℂ)*Complex.I)-z‖
        ≤ ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) v‖ * Ez / r :=
          div_le_div_of_nonneg_left hnum hr0 hden
      _ = Ez / r * ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) v‖ := by ring
  rw [integral_const_mul] at hmono
  have hmass := integral_norm_relativeVerticalExp_le hN d E t x₀ y₀ η tmax (N:ℝ) ht hr hη
    hheight htmax (by exact_mod_cast hN)
  -- the exponential factor
  have hdrop := verticalRealAction_outer_drop hN d E t tmax η x₀ y₀ ht htmax hη hr hheight hpsi
    z hzr hloss
  have hmic : xi*(z.re-x₀)/(t*rho) ≤ k * |z.re - x₀| := by
    calc xi*(z.re-x₀)/(t*rho) ≤ |xi*(z.re-x₀)|/(t*rho) :=
          div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
      _ = k * |z.re - x₀| := by simp only [k]; rw [abs_mul]; ring
  have hEzle : Ez ≤ Real.exp 4 * Real.exp (-((N:ℝ)*c*r - k) * r) := by
    rw [hEz, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : -(N:ℝ)*(verticalRealAction d E t z.re z.im-verticalRealAction d E t x₀ y₀) ≤
        -(N:ℝ)*(c * r * |z.re - x₀| - 4/N) := by
      have := mul_le_mul_of_nonneg_left hdrop hN0.le
      linarith
    have h2 : (N:ℝ)*(4/N) = 4 := by field_simp
    have h3 : -((N:ℝ)*c*r - k) * |z.re - x₀| ≤ -((N:ℝ)*c*r - k) * r := by
      have : 0 ≤ (N:ℝ)*c*r - k := by linarith
      nlinarith
    nlinarith
  have hCv : 0 ≤ verticalMassConstant η tmax := by
    unfold verticalMassConstant; positivity
  calc remainderMajorant d E t rho x₀ xi zeta z
      ≤ Ez / r * ∫ v : ℝ, ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) v‖ := hmono
    _ ≤ (Real.exp 4 * Real.exp (-((N:ℝ)*c*r - k) * r)) / r * verticalMassConstant η tmax :=
        mul_le_mul (div_le_div_of_nonneg_right hEzle hr0.le) hmass
          (integral_nonneg fun _ => norm_nonneg _) (by positivity)
    _ = outerDecayConstant N t tmax η rho xi := by
        unfold outerDecayConstant
        rw [← hrdef]
        ring

end BlockBand.GaussianBulk
