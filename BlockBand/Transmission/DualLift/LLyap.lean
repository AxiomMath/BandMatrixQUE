module

public import BlockBand.Transmission.DualLift.LDiscount
public import BlockBand.Transmission.Dual.ExistsLyapGen

/-!
# The Lyapunov function of the lift: `g = S(1 + log(1+x))`

`liftLyap y = (x + y)(1 + log(1 + x))` in flat coordinates `y = (x, y)`:
* `contDiffOn_liftLyap`: `C²` (indeed `C^∞`) on `flatU` (`x > −1`);
* **`L₁_liftLyap`**: `L₁ g = (D₀/2) S` on `flatU` (that is, `𝒟₁ g = (D₀/2)S`; the
  `log(1+x)` terms cancel because `L₁ S = 0`), hence `L₁_liftLyap_le`: `L₁ g ≤ (D₀/2) g` and
  `0 ≤ g` on `flatStrip` (where `x ≥ 0`), and `S ≤ g` there;
* `liftLyap_ge_of_norm`: on `liftM`, if `‖ξ‖ ≥ n` with `n > max 1 (1/ε)` and `S̃ ≥ ε > 0`,
  then `g(π ξ) ≥ ε log(1 + n²)` (the exit from the `n`-ball away from the corner is an exit to
  `|w|_∞ ≥ n`). No face Lyapunov function is needed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open MeasureTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists

/-- `g(x, y) = (x + y)(1 + log(1 + x))`. -/
def liftLyap (y : Fin 2 → ℝ) : ℝ := (y 0 + y 1) * (1 + Real.log (1 + y 0))

theorem contDiffAt_liftLyap {y : Fin 2 → ℝ} (hy : -1 < y 0) : ContDiffAt ℝ 2 liftLyap y := by
  have c0 : ContDiffAt ℝ 2 (fun y : Fin 2 → ℝ => y 0) y := (contDiff_apply ℝ ℝ 0).contDiffAt
  have c1 : ContDiffAt ℝ 2 (fun y : Fin 2 → ℝ => y 1) y := (contDiff_apply ℝ ℝ 1).contDiffAt
  exact (c0.add c1).mul (contDiffAt_const.add ((contDiffAt_const.add c0).log (by linarith)))

theorem contDiffOn_liftLyap : ContDiffOn ℝ 2 liftLyap flatU := fun _ hy =>
  (contDiffAt_liftLyap hy.2).contDiffWithinAt

theorem measurable_liftLyap : Measurable liftLyap := by
  have c0 : Measurable fun y : Fin 2 → ℝ => y 0 := measurable_pi_apply 0
  have c1 : Measurable fun y : Fin 2 → ℝ => y 1 := measurable_pi_apply 1
  exact (c0.add c1).mul (measurable_const.add (measurable_const.add c0).log)

theorem lineL_first {A c : ℝ} (hc : 0 < 1 + c) :
    deriv (fun r : ℝ => (A + r) * (Real.log (1 + c + r) + 1)) 0 =
      (Real.log (1 + c) + 1) + A * (1 / (1 + c)) := by
  have hl := hasDerivAt_log_shift (c := 1 + c) (r := 0) (by simpa using hc)
  have := ((hasDerivAt_id (0 : ℝ)).const_add A).mul (hl.add_const 1)
  have h' : HasDerivAt (fun r : ℝ => (A + r) * (Real.log (1 + c + r) + 1))
      ((Real.log (1 + c) + 1) + A * (1 / (1 + c))) 0 := by
    convert this using 1
    · funext x; simp
    · simp
  exact h'.deriv

theorem lineL_second {A c : ℝ} (hc : 0 < 1 + c) :
    deriv (deriv fun r : ℝ => (A + r) * (Real.log (1 + c + r) + 1)) 0 =
      2 * (1 / (1 + c)) + A * (-(1 / (1 + c) ^ 2)) := by
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < 1 + c + r := by
    have : Tendsto (fun r : ℝ => 1 + c + r) (𝓝 0) (𝓝 (1 + c)) := by
      simpa using (tendsto_const_nhds (x := 1 + c)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
    exact this.eventually (lt_mem_nhds hc)
  refine deriv_deriv_of_eventually (h1 := fun r => (Real.log (1 + c + r) + 1) +
    (A + r) * (1 / (1 + c + r))) (hev.mono fun r hr => ?_) ?_
  · have hl := hasDerivAt_log_shift (c := 1 + c) (r := r) hr
    have := ((hasDerivAt_id r).const_add A).mul (hl.add_const 1)
    convert this using 1
    · funext x; simp
    · simp
  · have hi := hasDerivAt_inv_shift (c := 1 + c) (r := 0) (by simpa using hc.ne')
    have hl := hasDerivAt_log_shift (c := 1 + c) (r := 0) (by simpa using hc)
    have := (hl.add_const 1).add (((hasDerivAt_id (0 : ℝ)).const_add A).mul hi)
    convert this using 1
    · funext x; simp
    · simp only [add_zero, id_eq]; ring

theorem lineC_first {A d : ℝ} : deriv (fun r : ℝ => (A + r) * d) 0 = d := by
  simp

theorem lineC_second {A d : ℝ} : deriv (deriv fun r : ℝ => (A + r) * d) 0 = 0 := by
  have h : deriv (fun r : ℝ => (A + r) * d) = fun _ => d := funext fun r => by
    simp
  rw [h]; simp

/-- **`L₁ g = (D₀/2) S`** on `flatU`. -/
theorem L₁_liftLyap (D0 : ℝ) {y : Fin 2 → ℝ} (hy : y ∈ flatU) :
    L₁ D0 liftLyap y = D0 / 2 * (y 0 + y 1) := by
  have h1 : 0 < 1 + y 0 := by linarith [hy.2]
  have hS := hy.1
  have hc := contDiffAt_liftLyap hy.2
  have hd := hc.differentiableAt (by norm_num)
  have ex : (fun r : ℝ => liftLyap (y + r • Pi.single 0 1)) = fun r => (y 0 + y 1 + r) *
      (Real.log (1 + y 0 + r) + 1) := by
    funext r
    simp only [liftLyap, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide), mul_one, mul_zero, add_zero]
    ring_nf
  have ey : (fun r : ℝ => liftLyap (y + r • Pi.single 1 1)) = fun r => (y 0 + y 1 + r) *
      (1 + Real.log (1 + y 0)) := by
    funext r
    simp only [liftLyap, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), mul_one, mul_zero, add_zero]
    ring_nf
  rw [L₁_eq, fderiv_eq_deriv_line _ hd, fderiv_eq_deriv_line _ hd,
    fderiv_fderiv_eq_deriv_line _ hc, fderiv_fderiv_eq_deriv_line _ hc, ex, ey,
    lineL_first h1, lineL_second h1, lineC_first, lineC_second,
    flatDrift_one_zero, flatDrift_one_one]
  field_simp
  ring

theorem liftLyap_nonneg {y : Fin 2 → ℝ} (hy : y ∈ flatStrip) : 0 ≤ liftLyap y := by
  have hl : 0 ≤ Real.log (1 + y 0) := Real.log_nonneg (by linarith [hy.1])
  exact mul_nonneg hy.2.2.2.le (by linarith)

theorem le_liftLyap {y : Fin 2 → ℝ} (hy : y ∈ flatStrip) : y 0 + y 1 ≤ liftLyap y := by
  have hl : 0 ≤ Real.log (1 + y 0) := Real.log_nonneg (by linarith [hy.1])
  unfold liftLyap; nlinarith [hy.2.2.2]

theorem L₁_liftLyap_le {D0 : ℝ} (hD0 : 0 ≤ D0) {y : Fin 2 → ℝ} (hy : y ∈ flatStrip) :
    L₁ D0 liftLyap y ≤ D0 / 2 * liftLyap y := by
  have hU : y ∈ flatU := ⟨hy.2.2.2, by linarith [hy.1]⟩
  rw [L₁_liftLyap D0 hU]
  exact mul_le_mul_of_nonneg_left (le_liftLyap hy) (by positivity)

theorem continuousOn_L₁_liftLyap (D0 : ℝ) : ContinuousOn (L₁ D0 liftLyap) flatU := by
  refine ContinuousOn.congr (f := fun y => D0 / 2 * (y 0 + y 1)) (by fun_prop) fun y hy => ?_
  exact L₁_liftLyap D0 hy

/-- **Lower bound at an exit away from the corner.** -/
theorem liftLyap_ge_of_norm {ξ : Fin 6 → ℝ} (h : ξ ∈ liftM) {n ε : ℝ} (hε : 0 < ε)
    (hn1 : 1 < n) (hnε : 1 / ε < n) (hn : n ≤ ‖ξ‖) (hS : ε ≤ lS ξ) :
    ε * Real.log (1 + n * n) ≤ liftLyap (liftProj ξ) := by
  have hn0 : 0 < n := by linarith
  obtain ⟨i, hi⟩ : ∃ i, n ≤ |ξ i| := by
    by_contra hc
    push Not at hc
    have : ‖ξ‖ < n := (pi_norm_lt_iff hn0).2 fun i => by rw [Real.norm_eq_abs]; exact hc i
    linarith
  have hv := h.1
  unfold vSq at hv
  have hS0 := lS_pos h
  have hs := s_eq_inv h
  have hx0 := lx_nonneg ξ
  have hy := ly_mem_of_mem h
  have hmem : liftProj ξ ∈ flatStrip := ⟨hx0, hy.1, hy.2, hS0⟩
  have hge : ∀ j, n ≤ |ξ j| → n * n ≤ ξ j * ξ j := fun j hj => by
    have := mul_le_mul hj hj hn0.le (abs_nonneg _)
    rwa [abs_mul_abs_self] at this
  fin_cases i
  · have hx : n * n ≤ lx ξ := by unfold lx; nlinarith [hge 0 hi, mul_self_nonneg (ξ 1)]
    have hl : Real.log (1 + n * n) ≤ Real.log (1 + lx ξ) :=
      Real.log_le_log (by positivity) (by linarith)
    have hl0 : 0 ≤ Real.log (1 + n * n) := Real.log_nonneg (by nlinarith)
    unfold liftLyap; simp only [liftProj_zero, liftProj_one]; unfold lS at hS
    nlinarith
  · have hx : n * n ≤ lx ξ := by unfold lx; nlinarith [hge 1 hi, mul_self_nonneg (ξ 0)]
    have hl : Real.log (1 + n * n) ≤ Real.log (1 + lx ξ) :=
      Real.log_le_log (by positivity) (by linarith)
    have hl0 : 0 ≤ Real.log (1 + n * n) := Real.log_nonneg (by nlinarith)
    unfold liftLyap; simp only [liftProj_zero, liftProj_one]; unfold lS at hS
    nlinarith
  all_goals first
    | (have h2 := hge _ hi; simp only [Fin.reduceFinMk, Fin.isValue] at h2
       nlinarith [mul_self_nonneg (ξ 2), mul_self_nonneg (ξ 3), mul_self_nonneg (ξ 4)])
    | (exfalso
       have h5 : |ξ 5| ≤ 1 / ε := by
         rw [hs, abs_of_pos (by positivity)]
         exact one_div_le_one_div_of_le hε hS
       simp only [Fin.reduceFinMk, Fin.isValue] at hi
       linarith)

end BlockBand.Transmission.DualLift
