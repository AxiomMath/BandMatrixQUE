module

public import BlockBand.Transmission.DualFeller.F1

/-!
# The absorption Lyapunov function `u = S log(1 + 1/S)`

Deterministic. `absPsi s = s log(1+s) − s log s = s log(1 + 1/s)` and `absLyap = absPsi ∘ S`,
`S = x + y`.
* `L₁_absLyap`: on `flatU`, `L₁ u = −(D₀/2)(1 + x − y)/(1 + S)²`. Indeed `L₁ S = 0`, both
  second derivatives of `u` are `ψ''(S) = −1/(S(1+S)²)`, and the bracket density of `S` is
  `D₀ Q`, `Q = x(1+x) + y(1−y) = S(1 + x − y)`.
* `neg_L₁_absLyap_nonneg`: `−L₁ u ≥ 0` on the strip (`y ≤ 1`), so `u(Y)` is a supermartingale
  everywhere; `le_neg_L₁_absLyap`: `−L₁ u ≥ D₀/9` on the strip where `S < 1/2`;
  `abs_L₁_absLyap_le`: `|L₁ u| ≤ D₀/2` on the strip.
* `absLyap_nonneg`, `absLyap_le_one`: `0 ≤ u ≤ 1` on the strip; `absPsi_small`: `ψ(s) < c`
  for `0 < s < ε₀(c)` (`ψ` extends continuously by `0` at `0`).

Unlike `−S log S`, this function is bounded and has `L₁ u ≤ 0` on the whole strip, so no
stopping at `{S ≥ 1/2}` is needed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualFeller

open MeasureTheory Filter Topology Set Real
open BlockBand.Transmission.DualLift BlockBand.Transmission.Dual
  BlockBand.Transmission.Dual.Exists

/-- `ψ(s) = s log(1+s) − s log s`. -/
def absPsi (s : ℝ) : ℝ := s * Real.log (1 + s) - s * Real.log s

/-- `u = ψ(S)`. -/
def absLyap (y : Fin 2 → ℝ) : ℝ := absPsi (tot y)

/-- `ψ'(s) = log(1+s) − log s − 1/(1+s)`. -/
def absPsi1 (s : ℝ) : ℝ := Real.log (1 + s) - Real.log s - 1 / (1 + s)

theorem hasDerivAt_absPsi {s : ℝ} (hs : 0 < s) : HasDerivAt absPsi (absPsi1 s) s := by
  have h1 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + s)) s := by
    simpa using hasDerivAt_log_shift (c := 1) (r := s) (by linarith)
  have h2 : HasDerivAt (fun s : ℝ => Real.log s) (1 / s) s := by
    simpa [one_div] using Real.hasDerivAt_log hs.ne'
  have := ((hasDerivAt_id s).mul h1).sub ((hasDerivAt_id s).mul h2)
  refine this.congr_deriv ?_
  simp only [absPsi1, id_eq, one_mul]
  field_simp
  ring

theorem hasDerivAt_absPsi1 {s : ℝ} (hs : 0 < s) :
    HasDerivAt absPsi1 (1 / (1 + s) - 1 / s + 1 / (1 + s) ^ 2) s := by
  have h1 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + s)) s := by
    simpa using hasDerivAt_log_shift (c := 1) (r := s) (by linarith)
  have h2 : HasDerivAt (fun s : ℝ => Real.log s) (1 / s) s := by
    simpa [one_div] using Real.hasDerivAt_log hs.ne'
  have h3 := hasDerivAt_inv_shift (c := 1) (r := s) (by linarith)
  exact ((h1.sub h2).sub h3).congr_deriv (by ring)

theorem contDiffAt_absPsi {s : ℝ} (hs : 0 < s) : ContDiffAt ℝ 2 absPsi s := by
  have c1 : ContDiffAt ℝ 2 (fun s : ℝ => Real.log (1 + s)) s :=
    (contDiffAt_const.add contDiffAt_id).log (by simp only [id_eq]; linarith)
  have c2 : ContDiffAt ℝ 2 (fun s : ℝ => Real.log s) s := contDiffAt_id.log hs.ne'
  exact (contDiffAt_id.mul c1).sub (contDiffAt_id.mul c2)

theorem contDiffAt_absLyap {y : Fin 2 → ℝ} (hy : 0 < tot y) : ContDiffAt ℝ 2 absLyap y :=
  (contDiffAt_absPsi hy).comp y (contDiff_tot.contDiffAt.of_le le_top)

theorem contDiffOn_absLyap : ContDiffOn ℝ 2 absLyap flatU := fun _ hy =>
  (contDiffAt_absLyap hy.1).contDiffWithinAt

theorem measurable_absLyap : Measurable absLyap := by
  unfold absLyap absPsi
  have c : Measurable tot := measurable_tot
  exact (c.mul (measurable_const.add c).log).sub (c.mul c.log)

theorem tot_add_single (y : Fin 2 → ℝ) (i : Fin 2) (r : ℝ) :
    tot (y + r • Pi.single i 1) = tot y + r := by
  fin_cases i <;> simp [tot] <;> ring

theorem absLyap_line (y : Fin 2 → ℝ) (i : Fin 2) :
    (fun r : ℝ => absLyap (y + r • Pi.single i 1)) = fun r => absPsi (tot y + r) := by
  funext r; rw [absLyap, tot_add_single]

theorem deriv_line_absPsi {c : ℝ} (hc : 0 < c) :
    deriv (fun r : ℝ => absPsi (c + r)) 0 = absPsi1 c := by
  have := (hasDerivAt_absPsi (by simpa using hc)).comp_const_add c 0
  simpa using this.deriv

theorem deriv2_line_absPsi {c : ℝ} (hc : 0 < c) :
    deriv (deriv fun r : ℝ => absPsi (c + r)) 0 = 1 / (1 + c) - 1 / c + 1 / (1 + c) ^ 2 := by
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < c + r := by
    have : Tendsto (fun r : ℝ => c + r) (𝓝 0) (𝓝 c) := by
      simpa using (tendsto_const_nhds (x := c)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
    exact this.eventually (lt_mem_nhds hc)
  refine deriv_deriv_of_eventually (h1 := fun r => absPsi1 (c + r))
    (hev.mono fun r hr => (hasDerivAt_absPsi hr).comp_const_add c r) ?_
  simpa using (hasDerivAt_absPsi1 (by simpa using hc)).comp_const_add c 0

/-- **`L₁ u = −(D₀/2)(1 + x − y)/(1 + S)²`** on `flatU`. -/
theorem L₁_absLyap (D0 : ℝ) {y : Fin 2 → ℝ} (hy : y ∈ flatU) :
    L₁ D0 absLyap y = -(D0 / 2 * (1 + y 0 - y 1) / (1 + tot y) ^ 2) := by
  have hS : 0 < tot y := hy.1
  have hc := contDiffAt_absLyap hS
  have hd := hc.differentiableAt (by norm_num)
  rw [L₁_eq, fderiv_eq_deriv_line _ hd, fderiv_eq_deriv_line _ hd,
    fderiv_fderiv_eq_deriv_line _ hc, fderiv_fderiv_eq_deriv_line _ hc, absLyap_line,
    absLyap_line, deriv_line_absPsi hS, deriv2_line_absPsi hS, flatDrift_one_zero,
    flatDrift_one_one]
  have hS' : y 0 + y 1 ≠ 0 := hS.ne'
  have h1 : 1 + (y 0 + y 1) ≠ 0 := by unfold tot at hS; linarith
  simp only [tot] at *
  field_simp
  ring

theorem continuousOn_L₁_absLyap (D0 : ℝ) : ContinuousOn (L₁ D0 absLyap) flatU := by
  refine ContinuousOn.congr (f := fun y => -(D0 / 2 * (1 + y 0 - y 1) / (1 + tot y) ^ 2)) ?_
    fun y hy => L₁_absLyap D0 hy
  refine ContinuousOn.neg <| ContinuousOn.div (by fun_prop) (by unfold tot; fun_prop) fun y hy => ?_
  have : 0 < tot y := hy.1
  positivity

theorem neg_L₁_absLyap_nonneg {D0 : ℝ} (hD0 : 0 ≤ D0) {y : Fin 2 → ℝ} (hy : y ∈ flatStrip) :
    0 ≤ -L₁ D0 absLyap y := by
  rw [L₁_absLyap D0 ⟨hy.2.2.2, by linarith [hy.1]⟩]
  have : 0 ≤ 1 + y 0 - y 1 := by linarith [hy.1, hy.2.2.1]
  have h2 : 0 < (1 + tot y) ^ 2 := by have := hy.2.2.2; unfold tot; positivity
  rw [neg_neg]
  exact div_nonneg (mul_nonneg (by linarith) this) h2.le

theorem le_neg_L₁_absLyap {D0 : ℝ} (hD0 : 0 ≤ D0) {y : Fin 2 → ℝ} (hy : y ∈ flatStrip)
    (hS : tot y < 1 / 2) : D0 / 9 ≤ -L₁ D0 absLyap y := by
  rw [L₁_absLyap D0 ⟨hy.2.2.2, by linarith [hy.1]⟩]
  unfold tot at *
  have h0 := hy.1
  have h1 := hy.2.1
  have h2 : 0 < (1 + (y 0 + y 1)) ^ 2 := by have := hy.2.2.2; positivity
  rw [neg_neg, le_div_iff₀ h2]
  have ha : (1 + (y 0 + y 1)) ^ 2 ≤ 9 / 4 := by nlinarith
  have hb : 1 / 2 ≤ 1 + y 0 - y 1 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left ha hD0, mul_le_mul_of_nonneg_left hb hD0]

theorem abs_L₁_absLyap_le {D0 : ℝ} (hD0 : 0 ≤ D0) {y : Fin 2 → ℝ} (hy : y ∈ flatStrip) :
    |L₁ D0 absLyap y| ≤ D0 / 2 := by
  have hn := neg_L₁_absLyap_nonneg hD0 hy
  rw [abs_of_nonpos (by linarith), L₁_absLyap D0 ⟨hy.2.2.2, by linarith [hy.1]⟩]
  unfold tot
  have h0 := hy.1
  have h1 := hy.2.1
  have h2 : 0 < (1 + (y 0 + y 1)) ^ 2 := by have := hy.2.2.2; positivity
  rw [neg_neg, div_le_iff₀ h2]
  have ha : 1 + y 0 - y 1 ≤ (1 + (y 0 + y 1)) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left ha hD0]

theorem absPsi_eq {s : ℝ} (hs : 0 < s) : absPsi s = s * Real.log (1 + 1 / s) := by
  have : 1 + 1 / s = (1 + s) / s := by field_simp; ring
  rw [absPsi, this, Real.log_div (by linarith) hs.ne']
  ring

theorem absPsi_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ absPsi s := by
  rw [absPsi_eq hs]
  exact mul_nonneg hs.le (Real.log_nonneg (by have := one_div_pos.2 hs; linarith))

theorem absPsi_le_one {s : ℝ} (hs : 0 < s) : absPsi s ≤ 1 := by
  rw [absPsi_eq hs]
  have h := Real.log_le_sub_one_of_pos (by have := one_div_pos.2 hs; linarith : 0 < 1 + 1 / s)
  have : s * Real.log (1 + 1 / s) ≤ s * (1 / s) := mul_le_mul_of_nonneg_left (by linarith) hs.le
  rwa [mul_one_div_cancel hs.ne'] at this

/-- `ψ` is small near `0` (it extends continuously by `ψ(0) = 0`). -/
theorem absPsi_small {c : ℝ} (hc : 0 < c) : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ s : ℝ, 0 < s → s < ε₀ →
    absPsi s < c := by
  have h1 : ContinuousAt (fun s : ℝ => s * Real.log (1 + s)) 0 :=
    continuousAt_id.mul ((continuousAt_const.add continuousAt_id).log (by norm_num))
  have h2 : ContinuousAt absPsi 0 := h1.sub Real.continuous_mul_log.continuousAt
  have h0 : absPsi 0 = 0 := by simp [absPsi]
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), absPsi s < c := h2.eventually (gt_mem_nhds (by rw [h0]; exact hc))
  obtain ⟨ε₀, hε₀, hb⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε₀, hε₀, fun s hs hsε => hb ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos hs]
  exact hsε

theorem absLyap_nonneg {y : Fin 2 → ℝ} (hy : y ∈ flatStrip) : 0 ≤ absLyap y :=
  absPsi_nonneg hy.2.2.2

theorem absLyap_le_one {y : Fin 2 → ℝ} (hy : y ∈ flatStrip) : absLyap y ≤ 1 :=
  absPsi_le_one hy.2.2.2

end BlockBand.Transmission.DualFeller
