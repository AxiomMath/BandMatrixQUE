module

public import BlockBand.Transmission.Dual.GPairCoord
public import BlockBand.Transmission.Dual.ExistsLyap
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Negative moments by a parabolic supersolution: the calculus

Level 1, flat coordinates `w = (x, y)`, base generator `L⁰ = L_X + L_Y`
(`flatBaseDrift D₀ 1`, `flatDiff D₀ 1`). With `g(w) = 1 − (1+x)⁻¹ + y = x/(1+x) + y`
(`gapG`), `q ∈ (0, 1)` and `N = 2q/(1−q)`:
`L⁰ e^{−Ng} ≤ (D₀/2) e^{−Ng} [(N² + 2N) g − 2N]` on `x > 0`, `0 < y < 1`. In backward time
`s`, `q = e^{−D₀ s}` solves the Riccati equation `dN/ds = −(D₀/2)(N² + 2N)`, and
`A = (1−q)⁻²` solves `dA/ds = −D₀ N A`. Hence `(1−q)⁻² e^{−N g}` is a space-time
supersolution (exact cancellation, `bracket_eq`). Deterministic.

The test function `negPhi D₀ s₁ T (t, w) = A(t) e^{−N(t) g(w)}` uses the backward time
`κ(t) = s₁ + T − t` for `t ≤ T + s₁/4`, cut off smoothly (`smoothTransition`) so that
`κ ≥ s₁/2 > 0` for all `t ∈ ℝ` (`half_le_kap`): this makes `negPhi` `C²` on `ℝ × {x > 0}`, as
the Itô formula requires. **`itoDrift_negPhi_nonpos`**: its Itô drift along the base
characteristics is `≤ 0` for `t < T + s₁/4`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open Filter Topology Set Real
open BlockBand.Internal.Contracts.Transmission
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists
open scoped NNReal

/-- `g(w) = 1 − (1 + w₀)⁻¹ + w₁`, i.e. `x/(1+x) + y`. -/
def gapG (w : Fin 2 → ℝ) : ℝ := 1 - (1 + w 0)⁻¹ + w 1

theorem measurable_gapG : Measurable gapG := by
  unfold gapG; fun_prop

/-- The open half-space `{w₀ > 0}`. -/
def posU : Set (Fin 2 → ℝ) := {w | 0 < w 0}

theorem isOpen_posU : IsOpen posU := isOpen_lt continuous_const (continuous_apply 0)

theorem contDiffOn_gapG : ContDiffOn ℝ 2 gapG posU := by
  intro w hw
  have h : (1 : ℝ) + w 0 ≠ 0 := by have : 0 < w 0 := hw; linarith
  refine ContDiffAt.contDiffWithinAt ?_
  unfold gapG
  exact (contDiffAt_const.sub ((contDiffAt_const.add
    (contDiff_apply ℝ ℝ (0 : Fin 2)).contDiffAt).inv h)).add
    (contDiff_apply ℝ ℝ (1 : Fin 2)).contDiffAt

theorem gapG_pos {w : Fin 2 → ℝ} (h0 : 0 < w 0) (h1 : 0 < w 1) : 0 < gapG w := by
  unfold gapG
  have : (1 + w 0)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  linarith

/-- `g ≤ x + y`. -/
theorem gapG_le {w : Fin 2 → ℝ} (h0 : 0 < w 0) : gapG w ≤ w 0 + w 1 := by
  unfold gapG
  have h : 1 - (1 + w 0)⁻¹ = w 0 / (1 + w 0) := by field_simp; ring
  have h2 : w 0 / (1 + w 0) ≤ w 0 := div_le_self h0.le (by linarith)
  linarith

/-!
### The cut-off backward time
-/

/-- `κ(t) = s₁ − (t − T)(1 − smoothTransition((t − T − s₁/4)/(s₁/4)))`. -/
def kap (s₁ T t : ℝ) : ℝ := s₁ - (t - T) * (1 - smoothTransition ((t - T - s₁ / 4) / (s₁ / 4)))

theorem contDiff_kap (s₁ T : ℝ) : ContDiff ℝ 2 (kap s₁ T) := by
  unfold kap
  refine contDiff_const.sub ((contDiff_id.sub contDiff_const).mul (contDiff_const.sub ?_))
  exact smoothTransition.contDiff.comp (((contDiff_id.sub contDiff_const).sub
    contDiff_const).div_const _)

theorem kap_eq {s₁ T t : ℝ} (hs : 0 < s₁) (ht : t ≤ T + s₁ / 4) : kap s₁ T t = s₁ - (t - T) := by
  have : (t - T - s₁ / 4) / (s₁ / 4) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  simp [kap, smoothTransition.zero_of_nonpos this]

theorem half_le_kap {s₁ T : ℝ} (hs : 0 < s₁) (t : ℝ) : s₁ / 2 ≤ kap s₁ T t := by
  rcases le_or_gt (t - T) (s₁ / 4) with ha | ha
  · rw [kap_eq hs (by linarith)]; linarith
  rcases le_or_gt (s₁ / 2) (t - T) with ha2 | ha2
  · have : 1 ≤ (t - T - s₁ / 4) / (s₁ / 4) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    simp only [kap, smoothTransition.one_of_one_le this, sub_self, mul_zero, sub_zero]
    linarith
  · have h0 := smoothTransition.nonneg ((t - T - s₁ / 4) / (s₁ / 4))
    have h1 := smoothTransition.le_one ((t - T - s₁ / 4) / (s₁ / 4))
    have : (t - T) * (1 - smoothTransition ((t - T - s₁ / 4) / (s₁ / 4))) ≤ t - T :=
      mul_le_of_le_one_right (by linarith) (by linarith)
    simp only [kap]
    linarith

/-!
### The time profile
-/

variable {D0 s₁ T : ℝ}

/-- `q(t) = e^{−D₀ κ(t)}`. -/
def qf (D0 s₁ T t : ℝ) : ℝ := exp (-(D0 * kap s₁ T t))

/-- `A(t) = (1 − q(t))⁻²`. -/
def Af (D0 s₁ T t : ℝ) : ℝ := ((1 - qf D0 s₁ T t) ^ 2)⁻¹

/-- `N(t) = 2q(t)/(1 − q(t))`. -/
def Nf (D0 s₁ T t : ℝ) : ℝ := 2 * qf D0 s₁ T t / (1 - qf D0 s₁ T t)

/-- **The test function** `(t, w) ↦ A(t) e^{−N(t) g(w)}`. -/
def negPhi (D0 s₁ T : ℝ) (p : ℝ × (Fin 2 → ℝ)) : ℝ :=
  Af D0 s₁ T p.1 * exp (-(Nf D0 s₁ T p.1 * gapG p.2))

theorem qf_pos (t : ℝ) : 0 < qf D0 s₁ T t := exp_pos _

theorem qf_lt_one (hD0 : 0 < D0) (hs : 0 < s₁) (t : ℝ) : qf D0 s₁ T t < 1 := by
  have := half_le_kap (T := T) hs t
  unfold qf
  calc exp (-(D0 * kap s₁ T t)) < exp 0 :=
        exp_lt_exp.2 (neg_lt_zero.2 (mul_pos hD0 (by linarith)))
    _ = 1 := exp_zero

theorem one_sub_qf_ne (hD0 : 0 < D0) (hs : 0 < s₁) (t : ℝ) : 1 - qf D0 s₁ T t ≠ 0 :=
  (sub_pos.2 (qf_lt_one hD0 hs t)).ne'

theorem contDiff_qf (D0 s₁ T : ℝ) : ContDiff ℝ 2 (qf D0 s₁ T) :=
  (contDiff_const.mul (contDiff_kap s₁ T)).neg.exp

theorem contDiff_Af (hD0 : 0 < D0) (hs : 0 < s₁) : ContDiff ℝ 2 (Af D0 s₁ T) :=
  ((contDiff_const.sub (contDiff_qf D0 s₁ T)).pow 2).inv fun t =>
    pow_ne_zero 2 (one_sub_qf_ne hD0 hs t)

theorem contDiff_Nf (hD0 : 0 < D0) (hs : 0 < s₁) : ContDiff ℝ 2 (Nf D0 s₁ T) :=
  (contDiff_const.mul (contDiff_qf D0 s₁ T)).div (contDiff_const.sub (contDiff_qf D0 s₁ T))
    fun t => one_sub_qf_ne hD0 hs t

theorem Af_pos (hD0 : 0 < D0) (hs : 0 < s₁) (t : ℝ) : 0 < Af D0 s₁ T t :=
  inv_pos.2 (pow_pos (sub_pos.2 (qf_lt_one hD0 hs t)) 2)

theorem Nf_nonneg (hD0 : 0 < D0) (hs : 0 < s₁) (t : ℝ) : 0 ≤ Nf D0 s₁ T t :=
  div_nonneg (by have := qf_pos (D0 := D0) (s₁ := s₁) (T := T) t; linarith)
    (sub_pos.2 (qf_lt_one hD0 hs t)).le

theorem measurable_negPhi (hD0 : 0 < D0) (hs : 0 < s₁) : Measurable (negPhi D0 s₁ T) :=
  ((contDiff_Af hD0 hs).continuous.measurable.comp measurable_fst).mul
    ((((contDiff_Nf hD0 hs).continuous.measurable.comp measurable_fst).mul
      (measurable_gapG.comp measurable_snd)).neg.exp)

theorem contDiffOn_negPhi (hD0 : 0 < D0) (hs : 0 < s₁) :
    ContDiffOn ℝ 2 (negPhi D0 s₁ T) (univ ×ˢ posU) :=
  ((contDiff_Af hD0 hs).comp contDiff_fst).contDiffOn.mul
    ((((contDiff_Nf hD0 hs).comp contDiff_fst).contDiffOn.mul
      (contDiffOn_gapG.comp contDiffOn_snd fun _ hp => hp.2)).neg.exp)

theorem negPhi_nonneg (hD0 : 0 < D0) (hs : 0 < s₁) (p : ℝ × (Fin 2 → ℝ)) :
    0 ≤ negPhi D0 s₁ T p :=
  mul_nonneg (Af_pos hD0 hs _).le (exp_pos _).le

theorem negPhi_le (hD0 : 0 < D0) (hs : 0 < s₁) {p : ℝ × (Fin 2 → ℝ)} (hp : 0 ≤ gapG p.2) :
    negPhi D0 s₁ T p ≤ Af D0 s₁ T p.1 := by
  unfold negPhi
  have : exp (-(Nf D0 s₁ T p.1 * gapG p.2)) ≤ 1 :=
    exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (Nf_nonneg hD0 hs _) hp))
  have hA := Af_pos (T := T) hD0 hs p.1
  nlinarith

/-!
### Derivatives
-/

/-- The time derivative of the profile `A(q) e^{−N(q) G}` along `q` with `q' = D₀ q`. -/
theorem hasDerivAt_timeProf {q : ℝ → ℝ} {q' t G : ℝ} (hq : HasDerivAt q q' t) (h1 : q t < 1) :
    HasDerivAt (fun τ => ((1 - q τ) ^ 2)⁻¹ * exp (-(2 * q τ / (1 - q τ) * G)))
      (((1 - q t) ^ 2)⁻¹ * exp (-(2 * q t / (1 - q t) * G)) *
        (2 * q' / (1 - q t) - 2 * q' * G / (1 - q t) ^ 2)) t := by
  have hr : 1 - q t ≠ 0 := (sub_pos.2 h1).ne'
  have hp : HasDerivAt (fun τ => (1 - q τ) ^ 2) (2 * (1 - q t) * (-q')) t := by
    have := (hq.const_sub 1).fun_pow 2
    exact this.congr_deriv (by simp)
  have hA : HasDerivAt (fun τ => ((1 - q τ) ^ 2)⁻¹) (-(2 * (1 - q t) * (-q')) / ((1 - q t) ^ 2) ^ 2)
      t := hp.fun_inv (pow_ne_zero 2 hr)
  have hD : HasDerivAt (fun τ => 2 * q τ / (1 - q τ))
      ((2 * q' * (1 - q t) - 2 * q t * (-q')) / (1 - q t) ^ 2) t :=
    (hq.const_mul 2).fun_div (hq.const_sub 1) hr
  have hN : HasDerivAt (fun τ => exp (-(2 * q τ / (1 - q τ) * G)))
      (exp (-(2 * q t / (1 - q t) * G)) *
        (-((2 * q' * (1 - q t) - 2 * q t * (-q')) / (1 - q t) ^ 2 * G))) t :=
    (hD.mul_const G).neg.exp
  refine (hA.mul hN).congr_deriv ?_
  field_simp
  ring

theorem hasDerivAt_qf (hs : 0 < s₁) {t : ℝ} (ht : t < T + s₁ / 4) :
    HasDerivAt (qf D0 s₁ T) (D0 * qf D0 s₁ T t) t := by
  have hev : (fun τ => exp (-(D0 * (s₁ - (τ - T))))) =ᶠ[𝓝 t] qf D0 s₁ T := by
    filter_upwards [Iio_mem_nhds ht] with τ hτ
    rw [qf, kap_eq hs (le_of_lt hτ)]
  have h : HasDerivAt (fun τ => exp (-(D0 * (s₁ - (τ - T))))) (exp (-(D0 * (s₁ - (t - T)))) * D0)
      t := by
    have := ((((hasDerivAt_id' t).sub_const T).const_sub s₁).const_mul D0).neg.exp
    exact this.congr_deriv (by simp only [Pi.neg_apply]; ring)
  rw [qf, kap_eq hs ht.le, mul_comm]
  exact h.congr_of_eventuallyEq hev.symm

theorem partialTime_eq_deriv {d : ℕ} {φ : ℝ × (Fin d → ℝ) → ℝ} {t : ℝ} {y : Fin d → ℝ}
    (h : DifferentiableAt ℝ φ (t, y)) : partialTime φ (t, y) = deriv (fun τ => φ (τ, y)) t := by
  unfold partialTime
  rw [fderiv_eq_deriv_line _ h]
  have e : (fun r : ℝ => φ ((t, y) + r • ((1 : ℝ), (0 : Fin d → ℝ)))) =
      fun r => (fun τ => φ (τ, y)) (t + r) := by
    funext r; simp
  rw [e]
  exact (deriv_comp_const_add (fun τ => φ (τ, y)) t 0).trans (by rw [add_zero])

theorem line_space {d : ℕ} (φ : ℝ × (Fin d → ℝ) → ℝ) (t : ℝ) (y : Fin d → ℝ) (i : Fin d) :
    (fun r : ℝ => φ ((t, y) + r • ((0 : ℝ), (Pi.single i 1 : Fin d → ℝ)))) =
      fun r => φ (t, y + r • Pi.single i 1) := by
  funext r; simp

/-- The space profile along `x`: first derivative. -/
theorem hasDerivAt_profX (A N a c : ℝ) {r : ℝ} (hr : 0 < 1 + (a + r)) :
    HasDerivAt (fun r : ℝ => A * exp (-(N * (1 - (1 + (a + r))⁻¹ + c))))
      (-(A * N * ((1 + (a + r))⁻¹) ^ 2 * exp (-(N * (1 - (1 + (a + r))⁻¹ + c))))) r := by
  have h1 : HasDerivAt (fun r : ℝ => 1 + (a + r)) 1 r :=
    ((hasDerivAt_id' r).const_add a).const_add 1
  have hi : HasDerivAt (fun r : ℝ => (1 + (a + r))⁻¹) (-1 / (1 + (a + r)) ^ 2) r :=
    h1.fun_inv hr.ne'
  have h := ((((hi.const_sub 1).add_const c).const_mul N).neg.exp).const_mul A
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply]
  field_simp

/-- The space profile along `x`: second derivative at `0`. -/
theorem hasDerivAt_profX' (A N a c : ℝ) (ha : 0 < 1 + a) :
    HasDerivAt (fun r : ℝ => -(A * N * ((1 + (a + r))⁻¹) ^ 2 *
        exp (-(N * (1 - (1 + (a + r))⁻¹ + c)))))
      (A * exp (-(N * (1 - (1 + a)⁻¹ + c))) * (N ^ 2 * ((1 + a)⁻¹) ^ 4 +
        2 * N * ((1 + a)⁻¹) ^ 3)) 0 := by
  have hr : (0 : ℝ) < 1 + (a + 0) := by simpa using ha
  have h1 : HasDerivAt (fun r : ℝ => 1 + (a + r)) 1 0 :=
    ((hasDerivAt_id' 0).const_add a).const_add 1
  have hi : HasDerivAt (fun r : ℝ => (1 + (a + r))⁻¹) (-1 / (1 + (a + 0)) ^ 2) 0 :=
    h1.fun_inv hr.ne'
  have hE := (((hi.const_sub 1).add_const c).const_mul N).neg.exp
  have hp : HasDerivAt (fun r : ℝ => ((1 + (a + r))⁻¹) ^ 2)
      (2 * (1 + (a + 0))⁻¹ * (-1 / (1 + (a + 0)) ^ 2)) 0 := by
    have := hi.fun_pow 2
    exact this.congr_deriv (by simp)
  have h := ((hp.const_mul (A * N)).mul hE).neg
  have e : (fun r : ℝ => -(A * N * ((1 + (a + r))⁻¹) ^ 2 *
      exp (-(N * (1 - (1 + (a + r))⁻¹ + c))))) = fun r => -((A * N) * ((1 + (a + r))⁻¹) ^ 2 *
      exp (-(N * (1 - (1 + (a + r))⁻¹ + c)))) := rfl
  rw [e]
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply, add_zero]
  field_simp
  ring

/-- The space profile along `y`. -/
theorem hasDerivAt_profY (A N G r : ℝ) :
    HasDerivAt (fun r : ℝ => A * exp (-(N * (G + r))))
      (-(N * A * exp (-(N * (G + r))))) r := by
  have h := ((((hasDerivAt_id' r).const_add G).const_mul N).neg.exp).const_mul A
  exact h.congr_deriv (by simp only [Pi.neg_apply]; ring)

theorem hasDerivAt_profY' (A N G : ℝ) :
    HasDerivAt (fun r : ℝ => -(N * A * exp (-(N * (G + r)))))
      (N ^ 2 * A * exp (-(N * G))) 0 := by
  have h := (((((hasDerivAt_id' (0 : ℝ)).const_add G).const_mul N).neg.exp).const_mul
    (N * A)).neg
  exact h.congr_deriv (by simp only [Pi.neg_apply, add_zero]; ring)

/-!
### The drift bracket
-/

/-- **The exact cancellation**: the bracket of the Itô drift is a sum of nonpositive terms. -/
theorem bracket_eq (D0 q x y : ℝ) (hq : q ≠ 1) (hx : 1 + x ≠ 0) :
    2 * (D0 * q) / (1 - q) - 2 * (D0 * q) * (1 - (1 + x)⁻¹ + y) / (1 - q) ^ 2 +
      D0 / 2 * (1 + 2 * x) * (-(2 * q / (1 - q) * ((1 + x)⁻¹) ^ 2)) +
      D0 / 2 * (1 - 2 * y) * (-(2 * q / (1 - q))) +
      1 / 2 * (D0 * (x * (1 + x))) * ((2 * q / (1 - q)) ^ 2 * ((1 + x)⁻¹) ^ 4 +
        2 * (2 * q / (1 - q)) * ((1 + x)⁻¹) ^ 3) +
      1 / 2 * (D0 * (y * (1 - y))) * (2 * q / (1 - q)) ^ 2 =
    -(D0 / 2) * ((2 * q / (1 - q)) * (1 - (1 + x)⁻¹) ^ 2 +
      (2 * q / (1 - q)) ^ 2 * (1 - (1 + x)⁻¹) * (1 - ((1 + x)⁻¹) ^ 2) +
      (2 * q / (1 - q)) ^ 2 * y ^ 2) := by
  have hq' : 1 - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq)
  field_simp
  ring

theorem bracket_nonpos {D0 q x y : ℝ} (hD0 : 0 < D0) (hq0 : 0 < q) (hq1 : q < 1) (hx : 0 < x) :
    2 * (D0 * q) / (1 - q) - 2 * (D0 * q) * (1 - (1 + x)⁻¹ + y) / (1 - q) ^ 2 +
      D0 / 2 * (1 + 2 * x) * (-(2 * q / (1 - q) * ((1 + x)⁻¹) ^ 2)) +
      D0 / 2 * (1 - 2 * y) * (-(2 * q / (1 - q))) +
      1 / 2 * (D0 * (x * (1 + x))) * ((2 * q / (1 - q)) ^ 2 * ((1 + x)⁻¹) ^ 4 +
        2 * (2 * q / (1 - q)) * ((1 + x)⁻¹) ^ 3) +
      1 / 2 * (D0 * (y * (1 - y))) * (2 * q / (1 - q)) ^ 2 ≤ 0 := by
  rw [bracket_eq D0 q x y hq1.ne (by linarith)]
  have hN : 0 ≤ 2 * q / (1 - q) := div_nonneg (by linarith) (by linarith)
  have hu0 : 0 < (1 + x)⁻¹ := inv_pos.2 (by linarith)
  have hu1 : (1 + x)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h1 : 0 ≤ 1 - (1 + x)⁻¹ := by linarith
  have h2 : 0 ≤ 1 - ((1 + x)⁻¹) ^ 2 := by nlinarith
  have : 0 ≤ (2 * q / (1 - q)) * (1 - (1 + x)⁻¹) ^ 2 +
      (2 * q / (1 - q)) ^ 2 * (1 - (1 + x)⁻¹) * (1 - ((1 + x)⁻¹) ^ 2) +
      (2 * q / (1 - q)) ^ 2 * y ^ 2 := by positivity
  nlinarith

/-- **The Itô drift of `negPhi` along the base characteristics is `≤ 0`** before the cut-off. -/
theorem itoDrift_negPhi_nonpos (hD0 : 0 < D0) (hs : 0 < s₁) {t : ℝ≥0}
    (ht : (t : ℝ) < T + s₁ / 4) {y : Fin 2 → ℝ} (hy : 0 < y 0) :
    itoDrift (negPhi D0 s₁ T) y t (flatBaseDrift D0 1 y) (flatDiff D0 1 y) ≤ 0 := by
  have hU : ((t : ℝ), y) ∈ univ ×ˢ posU := ⟨mem_univ _, hy⟩
  have hc : ContDiffAt ℝ 2 (negPhi D0 s₁ T) ((t : ℝ), y) :=
    (contDiffOn_negPhi hD0 hs).contDiffAt ((isOpen_univ.prod isOpen_posU).mem_nhds hU)
  have hd : DifferentiableAt ℝ (negPhi D0 s₁ T) ((t : ℝ), y) := hc.differentiableAt (by norm_num)
  set q := qf D0 s₁ T t with hqdef
  set A := Af D0 s₁ T t
  set N := Nf D0 s₁ T t
  set u := (1 + y 0)⁻¹
  have hq0 : 0 < q := qf_pos _
  have hq1 : q < 1 := qf_lt_one hD0 hs _
  -- time
  have ht' : partialTime (negPhi D0 s₁ T) ((t : ℝ), y) =
      A * exp (-(N * gapG y)) * (2 * (D0 * q) / (1 - q) - 2 * (D0 * q) * gapG y / (1 - q) ^ 2) := by
    rw [partialTime_eq_deriv hd]
    exact (hasDerivAt_timeProf (G := gapG y) (hasDerivAt_qf (D0 := D0) hs ht) hq1).deriv
  -- space, coordinate 0
  have e0 : (fun r : ℝ => negPhi D0 s₁ T ((t : ℝ), y + r • Pi.single 0 1)) =
      fun r => A * exp (-(N * (1 - (1 + (y 0 + r))⁻¹ + y 1))) := by
    funext r; simp [negPhi, gapG, A, N]
  have hr0 : (0 : ℝ) < 1 + (y 0 + 0) := by linarith
  have hs0 : partialSpace (negPhi D0 s₁ T) ((t : ℝ), y) 0 =
      -(A * N * u ^ 2 * exp (-(N * gapG y))) := by
    unfold partialSpace
    rw [fderiv_eq_deriv_line _ hd, line_space, e0, (hasDerivAt_profX A N (y 0) (y 1) hr0).deriv]
    simp [gapG, u]
  have hss0 : partialSpace2 (negPhi D0 s₁ T) ((t : ℝ), y) 0 0 =
      A * exp (-(N * gapG y)) * (N ^ 2 * u ^ 4 + 2 * N * u ^ 3) := by
    unfold partialSpace2
    rw [fderiv_fderiv_eq_deriv_line _ hc, line_space, e0]
    have hev : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < 1 + (y 0 + r) := by
      have hcont : Continuous fun r : ℝ => 1 + (y 0 + r) := by fun_prop
      exact hcont.continuousAt.eventually (lt_mem_nhds hr0)
    rw [deriv_deriv_of_eventually (hev.mono fun r hr => hasDerivAt_profX A N (y 0) (y 1) hr)
      (hasDerivAt_profX' A N (y 0) (y 1) (by linarith))]
    rfl
  -- space, coordinate 1
  have e1 : (fun r : ℝ => negPhi D0 s₁ T ((t : ℝ), y + r • Pi.single 1 1)) =
      fun r => A * exp (-(N * (gapG y + r))) := by
    funext r
    have h0 : (y + r • (Pi.single (1 : Fin 2) (1 : ℝ) : Fin 2 → ℝ)) 0 = y 0 := by simp
    have h1 : (y + r • (Pi.single (1 : Fin 2) (1 : ℝ) : Fin 2 → ℝ)) 1 = y 1 + r := by simp
    simp only [negPhi, gapG, h0, h1]
    rw [← add_assoc]
  have hs1 : partialSpace (negPhi D0 s₁ T) ((t : ℝ), y) 1 = -(N * A * exp (-(N * gapG y))) := by
    unfold partialSpace
    rw [fderiv_eq_deriv_line _ hd, line_space, e1, (hasDerivAt_profY A N (gapG y) 0).deriv,
      add_zero]
  have hss1 : partialSpace2 (negPhi D0 s₁ T) ((t : ℝ), y) 1 1 =
      N ^ 2 * A * exp (-(N * gapG y)) := by
    unfold partialSpace2
    rw [fderiv_fderiv_eq_deriv_line _ hc, line_space, e1,
      deriv_deriv_of_eventually (Eventually.of_forall fun r => hasDerivAt_profY A N (gapG y) r)
        (hasDerivAt_profY' A N (gapG y))]
  -- assemble
  have hE : 0 < A * exp (-(N * gapG y)) := mul_pos (Af_pos hD0 hs _) (exp_pos _)
  have hdiag : ∀ i j : Fin 2, i ≠ j → flatDiff D0 1 y i j = 0 := fun i j hij =>
    Matrix.diagonal_apply_ne _ hij
  have hsum : itoDrift (negPhi D0 s₁ T) y t (flatBaseDrift D0 1 y) (flatDiff D0 1 y) =
      A * exp (-(N * gapG y)) *
        (2 * (D0 * q) / (1 - q) - 2 * (D0 * q) * (1 - (1 + y 0)⁻¹ + y 1) / (1 - q) ^ 2 +
        D0 / 2 * (1 + 2 * y 0) * (-(2 * q / (1 - q) * ((1 + y 0)⁻¹) ^ 2)) +
        D0 / 2 * (1 - 2 * y 1) * (-(2 * q / (1 - q))) +
        1 / 2 * (D0 * (y 0 * (1 + y 0))) * ((2 * q / (1 - q)) ^ 2 * ((1 + y 0)⁻¹) ^ 4 +
          2 * (2 * q / (1 - q)) * ((1 + y 0)⁻¹) ^ 3) +
        1 / 2 * (D0 * (y 1 * (1 - y 1))) * (2 * q / (1 - q)) ^ 2) := by
    have hN : N = 2 * q / (1 - q) := rfl
    unfold itoDrift
    rw [ht', Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
      hs0, hs1, hss0, hss1, hdiag 0 1 (by decide), hdiag 1 0 (by decide), zero_mul, zero_mul,
      add_zero, zero_add, flatBaseDrift_one_zero, flatBaseDrift_one_one]
    have h00 : flatDiff D0 1 y 0 0 = D0 * (y 0 * (1 + y 0)) := by
      rw [flatDiff, Matrix.diagonal_apply_eq]; exact flatDiffDiag_one_zero D0 y
    have h11 : flatDiff D0 1 y 1 1 = D0 * (y 1 * (1 - y 1)) := by
      rw [flatDiff, Matrix.diagonal_apply_eq]; exact flatDiffDiag_one_one D0 y
    rw [h00, h11, ← hN]
    simp only [gapG, u]
    ring
  rw [hsum]
  exact mul_nonpos_of_nonneg_of_nonpos hE.le (bracket_nonpos hD0 hq0 hq1 hy)

end BlockBand.Transmission.Dual.G
