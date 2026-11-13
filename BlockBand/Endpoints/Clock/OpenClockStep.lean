module

public import BlockBand.SourceProcess.CommonMatrixBrownian
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# One lognormal step of the dual geometric Brownian motion

Objects (all on the constructed Wiener space `CanonicalWienerPath`, law `canonicalWienerLaw`,
`canonicalWiener_isBrownian`):
* `OpenClock.incr s v ω = ω(s+v) - ω(s)`, law `N(0, v)` (`hasLaw_incr`);
* `OpenClock.logZ D s v = √D incr - Dv/2`, `OpenClock.lognormal D s v = exp logZ`, with the exact
  moments `E exp(r logZ) = exp(r(r-1)Dv/2)` (`integral_exp_mul_logZ`);
* `OpenClock.lap μ b = ∫ e^{-bx} dμ`, `OpenClock.lap2 μ b = ∫ x² e^{-bx} dμ`.

Main results:
* `abs_integral_exp_lognormal_sub_le`: for `y ≥ 0`, `0 < v`, `10 D v ≤ 1`,
  `|E e^{-y M_v} - e^{-y} - v (D/2) y² e^{-y}| ≤ 24(4D+88D²) v^{3/2} + D² v²`;
* `abs_integral_lap_lognormal_step`: the same bound for
  `|E lap μ (b M_v) - lap μ b - v (D/2) b² lap2 μ b|`, every probability `μ` carried by `[0,∞)`
  and every `b ≥ 0`.

Method: third-order Taylor bound `|e^x-1-x-x²/2| ≤ 4|x|³e^{x⁺}` and the scale-free bound
`|e^{-ym} - (2nd order Taylor at m=1)| ≤ 24|m - m⁻¹|³`; then `E|M-M⁻¹|³` by AM–GM from the exact
lognormal moments `E(M-M⁻¹)² = e^{Dv}-2+e^{3Dv}` and
`E(M-M⁻¹)⁴ = e^{6Dv}-4e^{Dv}+6-4e^{3Dv}+e^{10Dv}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock
namespace OpenClock

open MeasureTheory ProbabilityTheory Real Set
open BlockBand.SourceProcess
open scoped NNReal ENNReal

/-!
## 1. Elementary inequalities
-/

/-- Third-order Taylor bound for `exp` on all of `ℝ`. -/
theorem abs_exp_sub_quad_le (x : ℝ) :
    |exp x - 1 - x - x ^ 2 / 2| ≤ 4 * |x| ^ 3 * exp (max x 0) := by
  have hE : 1 ≤ exp (max x 0) := one_le_exp (le_max_right _ _)
  have hEx : exp x ≤ exp (max x 0) := exp_le_exp.mpr (le_max_left _ _)
  have hax := abs_nonneg x
  rcases le_or_gt (|x|) 1 with hx | hx
  · have h := Real.exp_bound hx (n := 3) (by norm_num)
    have hs : ∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ) = 1 + x + x ^ 2 / 2 := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [hs] at h
    have h' : |exp x - 1 - x - x ^ 2 / 2| ≤ |x| ^ 3 * (2 / 9) := by
      have e : exp x - 1 - x - x ^ 2 / 2 = exp x - (1 + x + x ^ 2 / 2) := by ring
      rw [e]
      refine h.trans (le_of_eq ?_)
      norm_num [Nat.factorial]
    have h3 : 0 ≤ |x| ^ 3 := by positivity
    have : |x| ^ 3 * 1 ≤ |x| ^ 3 * exp (max x 0) := mul_le_mul_of_nonneg_left hE h3
    nlinarith
  · have hx2 : 1 ≤ |x| ^ 2 := by nlinarith
    have h3 : |x| ≤ |x| ^ 3 := by
      calc |x| = |x| * 1 := by ring
        _ ≤ |x| * |x| ^ 2 := mul_le_mul_of_nonneg_left hx2 hax
        _ = |x| ^ 3 := by ring
    have h2 : x ^ 2 ≤ |x| ^ 3 := by
      rw [← sq_abs]
      calc |x| ^ 2 = |x| ^ 2 * 1 := by ring
        _ ≤ |x| ^ 2 * |x| := mul_le_mul_of_nonneg_left hx.le (by positivity)
        _ = |x| ^ 3 := by ring
    have h1 : 1 ≤ |x| ^ 3 := by linarith
    have hp : 0 < exp x := exp_pos x
    have hA : |x| ^ 3 * 1 ≤ |x| ^ 3 * exp (max x 0) := mul_le_mul_of_nonneg_left hE (by positivity)
    have hB : 1 * exp (max x 0) ≤ |x| ^ 3 * exp (max x 0) :=
      mul_le_mul_of_nonneg_right h1 (exp_pos _).le
    rw [abs_le]
    constructor
    · nlinarith [neg_abs_le x, le_abs_self x]
    · nlinarith [neg_abs_le x, le_abs_self x]

/-- `z³ e^{-z} ≤ 6` for `z ≥ 0`. -/
theorem pow_three_mul_exp_neg_le {z : ℝ} (hz : 0 ≤ z) : z ^ 3 * exp (-z) ≤ 6 := by
  have h := pow_div_factorial_le_exp z hz 3
  have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6] at h
  rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos z)]
  linarith

/-- `z² e^{-z} ≤ 2` for `z ≥ 0`. -/
theorem sq_mul_exp_neg_le {z : ℝ} (hz : 0 ≤ z) : z ^ 2 * exp (-z) ≤ 2 := by
  have h := pow_div_factorial_le_exp z hz 2
  have h2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [h2] at h
  rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos z)]
  linarith

/-- The scale-free second-order Taylor bound at `m = 1` for `m ↦ e^{-ym}`, uniformly in
`y ≥ 0`. -/
theorem abs_exp_taylor2_le {y m : ℝ} (hy : 0 ≤ y) (hm : 0 < m) :
    |exp (-(y * m)) - exp (-y) + y * exp (-y) * (m - 1) - y ^ 2 / 2 * exp (-y) * (m - 1) ^ 2|
      ≤ 24 * |m - m⁻¹| ^ 3 := by
  set x := y * (1 - m) with hx
  have hsplit : exp (-(y * m)) = exp (-y) * exp x := by rw [← exp_add]; congr 1; ring
  have hfac : exp (-(y * m)) - exp (-y) + y * exp (-y) * (m - 1) - y ^ 2 / 2 * exp (-y) * (m - 1) ^ 2
      = exp (-y) * (exp x - 1 - x - x ^ 2 / 2) := by rw [hsplit, hx]; ring
  rw [hfac, abs_mul, abs_of_pos (exp_pos _)]
  have hT := abs_exp_sub_quad_le x
  have hyp : 0 ≤ exp (-y) := (exp_pos _).le
  have hstep : exp (-y) * |exp x - 1 - x - x ^ 2 / 2| ≤ 4 * |x| ^ 3 * exp (-y + max x 0) := by
    rw [exp_add]
    calc exp (-y) * |exp x - 1 - x - x ^ 2 / 2| ≤ exp (-y) * (4 * |x| ^ 3 * exp (max x 0)) :=
          mul_le_mul_of_nonneg_left hT hyp
      _ = _ := by ring
  refine hstep.trans ?_
  have hxabs : |x| ^ 3 = y ^ 3 * |m - 1| ^ 3 := by
    rw [hx, abs_mul, abs_of_nonneg hy, mul_pow, abs_sub_comm]
  rw [hxabs]
  rcases le_or_gt 1 m with h1 | h1
  · -- `m ≥ 1`: `x ≤ 0`
    have hx0 : x ≤ 0 := by rw [hx]; nlinarith
    rw [max_eq_right hx0, add_zero]
    have hb := pow_three_mul_exp_neg_le hy
    have hmm : |m - 1| ≤ |m - m⁻¹| := by
      have hi : m⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    have hp : |m - 1| ^ 3 ≤ |m - m⁻¹| ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hmm 3
    have h0 : 0 ≤ |m - 1| ^ 3 := by positivity
    calc 4 * (y ^ 3 * |m - 1| ^ 3) * exp (-y) = 4 * |m - 1| ^ 3 * (y ^ 3 * exp (-y)) := by ring
      _ ≤ 4 * |m - 1| ^ 3 * 6 := mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ 24 * |m - m⁻¹| ^ 3 := by nlinarith
  · -- `m < 1`: `x ≥ 0`
    have hx0 : 0 ≤ x := by rw [hx]; nlinarith
    rw [max_eq_left hx0]
    have he : -y + x = -(y * m) := by rw [hx]; ring
    rw [he]
    have hb := pow_three_mul_exp_neg_le (mul_nonneg hy hm.le)
    have hmm : (1 - m) / m ≤ m⁻¹ - m := by
      rw [div_le_iff₀ hm, sub_mul, inv_mul_cancel₀ hm.ne']
      nlinarith
    have hq0 : 0 ≤ (1 - m) / m := div_nonneg (by linarith) hm.le
    have habs : |m - m⁻¹| = m⁻¹ - m := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have h1m : |m - 1| = 1 - m := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [habs, h1m]
    have hp : ((1 - m) / m) ^ 3 ≤ (m⁻¹ - m) ^ 3 := pow_le_pow_left₀ hq0 hmm 3
    have hm3 : 0 < m ^ 3 := by positivity
    have e : 4 * (y ^ 3 * (1 - m) ^ 3) * exp (-(y * m))
        = 4 * ((1 - m) / m) ^ 3 * ((y * m) ^ 3 * exp (-(y * m))) := by
      field_simp
    rw [e]
    have h0 : 0 ≤ ((1 - m) / m) ^ 3 := by positivity
    calc 4 * ((1 - m) / m) ^ 3 * ((y * m) ^ 3 * exp (-(y * m)))
        ≤ 4 * ((1 - m) / m) ^ 3 * 6 := mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ 24 * (m⁻¹ - m) ^ 3 := by nlinarith

/-- AM–GM: `|x|³ ≤ (s x² + x⁴/s)/2` for `s > 0`. -/
theorem abs_pow_three_le {x s : ℝ} (hs : 0 < s) : |x| ^ 3 ≤ (s * x ^ 2 + x ^ 4 / s) / 2 := by
  set a := |x| with ha
  have ha0 : 0 ≤ a := abs_nonneg x
  have hx2 : x ^ 2 = a ^ 2 := (sq_abs x).symm
  have hx4 : x ^ 4 = a ^ 4 := by rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, hx2]; ring
  rw [hx2, hx4]
  have key : s * a ^ 2 + a ^ 4 / s - 2 * a ^ 3 = a ^ 2 * (s - a) ^ 2 / s := by
    field_simp; ring
  have hnn : 0 ≤ a ^ 2 * (s - a) ^ 2 / s := div_nonneg (by positivity) hs.le
  linarith

/-!
## 2. Lognormal moments on the Wiener space
-/

/-- The Brownian increment `ω(s+v) - ω(s)`. -/
def incr (s v : ℝ≥0) (ω : CanonicalWienerPath) : ℝ := ω (s + v) - ω s

theorem continuous_incr (s v : ℝ≥0) : Continuous (incr s v) := by
  unfold incr
  exact (continuous_eval_const _).sub (continuous_eval_const _)

theorem measurable_incr (s v : ℝ≥0) : Measurable (incr s v) := (continuous_incr s v).measurable

theorem hasLaw_incr (s v : ℝ≥0) : HasLaw (incr s v) (gaussianReal 0 v) canonicalWienerLaw := by
  have h := canonicalWiener_isBrownian.toIsPreBrownianReal.hasLaw_sub (s + v) s
  convert h using 2
  · rfl
  · ext
    simp

theorem integral_exp_mul_incr (s v : ℝ≥0) (t : ℝ) :
    ∫ ω, exp (t * incr s v ω) ∂canonicalWienerLaw = exp (v * t ^ 2 / 2) := by
  have h := mgf_gaussianReal (hasLaw_incr s v) t
  have e : mgf (incr s v) canonicalWienerLaw t = ∫ ω, exp (t * incr s v ω) ∂canonicalWienerLaw :=
    rfl
  rw [← e, h]
  congr 1
  ring

theorem integrable_exp_mul_incr (s v : ℝ≥0) (t : ℝ) :
    Integrable (fun ω => exp (t * incr s v ω)) canonicalWienerLaw := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_exp_mul_incr]
  exact (exp_pos _).ne'

/-- `log M_v = √D (ω(s+v) - ω(s)) - D v/2`. -/
def logZ (D : ℝ) (s v : ℝ≥0) (ω : CanonicalWienerPath) : ℝ :=
  Real.sqrt D * incr s v ω - D * v / 2

/-- The one-step geometric Brownian factor `M_v = exp(√D (ω(s+v) - ω(s)) - D v/2)`. -/
def lognormal (D : ℝ) (s v : ℝ≥0) (ω : CanonicalWienerPath) : ℝ := exp (logZ D s v ω)

theorem continuous_logZ (D : ℝ) (s v : ℝ≥0) : Continuous (logZ D s v) := by
  unfold logZ; exact (continuous_const.mul (continuous_incr s v)).sub continuous_const

theorem measurable_lognormal (D : ℝ) (s v : ℝ≥0) : Measurable (lognormal D s v) :=
  (continuous_exp.comp (continuous_logZ D s v)).measurable

theorem lognormal_pos (D : ℝ) (s v : ℝ≥0) (ω : CanonicalWienerPath) : 0 < lognormal D s v ω :=
  exp_pos _

theorem integrable_exp_mul_logZ (D : ℝ) (s v : ℝ≥0) (r : ℝ) :
    Integrable (fun ω => exp (r * logZ D s v ω)) canonicalWienerLaw := by
  have e : (fun ω => exp (r * logZ D s v ω)) =
      fun ω => exp (-(r * D * v / 2)) * exp ((r * Real.sqrt D) * incr s v ω) := by
    funext ω; rw [← exp_add]; unfold logZ; congr 1; ring
  rw [e]
  exact (integrable_exp_mul_incr s v _).const_mul _

/-- Exact lognormal moments: `E exp(r log M_v) = exp(r(r-1) D v/2)`. -/
theorem integral_exp_mul_logZ {D : ℝ} (hD : 0 ≤ D) (s v : ℝ≥0) (r : ℝ) :
    ∫ ω, exp (r * logZ D s v ω) ∂canonicalWienerLaw = exp (r * (r - 1) * D * v / 2) := by
  have e : (fun ω => exp (r * logZ D s v ω)) =
      fun ω => exp (-(r * D * v / 2)) * exp ((r * Real.sqrt D) * incr s v ω) := by
    funext ω; rw [← exp_add]; unfold logZ; congr 1; ring
  rw [e, integral_const_mul, integral_exp_mul_incr, ← exp_add]
  congr 1
  rw [mul_pow, Real.sq_sqrt hD]
  ring

/-!
## 3. The pointwise step estimate
-/

private theorem exp_small_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |exp x - 1 - x| ≤ x ^ 2 := by
  exact Real.abs_exp_sub_one_sub_id_le (by rw [abs_of_nonneg hx0]; exact hx1)

/-- **One dual step on a pure exponential.** For `y ≥ 0`, `v > 0` with `10 D v ≤ 1`:
`|E e^{-y M_v} - e^{-y} - v (D/2) y² e^{-y}| ≤ 24(4D+88D²) v^{3/2} + D² v²`. -/
theorem abs_integral_exp_lognormal_sub_le {D : ℝ} (hD : 0 ≤ D) (s v : ℝ≥0) (hv : 0 < v)
    (hDv : 10 * D * v ≤ 1) {y : ℝ} (hy : 0 ≤ y) :
    |∫ ω, exp (-(y * lognormal D s v ω)) ∂canonicalWienerLaw - exp (-y)
        - v * (D / 2) * y ^ 2 * exp (-y)|
      ≤ 24 * (4 * D + 88 * D ^ 2) * Real.sqrt v ^ 3 + D ^ 2 * v ^ 2 := by
  set P := canonicalWienerLaw
  set Z := logZ D s v
  set x : ℝ := D * v with hxdef
  have hx0 : 0 ≤ x := mul_nonneg hD v.2
  have hv' : (0 : ℝ) < v := hv
  have hI : ∀ r : ℝ, Integrable (fun ω => exp (r * Z ω)) P := integrable_exp_mul_logZ D s v
  have hE : ∀ r : ℝ, ∫ ω, exp (r * Z ω) ∂P = exp (r * (r - 1) * D * v / 2) :=
    integral_exp_mul_logZ hD s v
  -- notation `M = exp Z`
  have hM : ∀ ω, lognormal D s v ω = exp (1 * Z ω) := fun ω => by rw [one_mul]; rfl
  -- pointwise identities
  have hsq : ∀ ω, (exp (1 * Z ω) - (exp (1 * Z ω))⁻¹) ^ 2
      = exp (2 * Z ω) - 2 + exp ((-2) * Z ω) := by
    intro ω
    have ha : exp (2 * Z ω) = exp (1 * Z ω) * exp (1 * Z ω) := by rw [← exp_add]; ring_nf
    have hb : exp ((-2) * Z ω) = (exp (1 * Z ω))⁻¹ * (exp (1 * Z ω))⁻¹ := by
      rw [← exp_neg, ← exp_add]; ring_nf
    have hab : exp (1 * Z ω) * (exp (1 * Z ω))⁻¹ = 1 := mul_inv_cancel₀ (exp_pos _).ne'
    rw [ha, hb]
    linear_combination (-2) * hab
  have hquart : ∀ ω, (exp (1 * Z ω) - (exp (1 * Z ω))⁻¹) ^ 4
      = exp (4 * Z ω) - 4 * exp (2 * Z ω) + 6 - 4 * exp ((-2) * Z ω) + exp ((-4) * Z ω) := by
    intro ω
    have ha2 : exp (2 * Z ω) = exp (1 * Z ω) ^ 2 := by rw [sq, ← exp_add]; ring_nf
    have ha4 : exp (4 * Z ω) = exp (1 * Z ω) ^ 4 := by
      rw [show exp (1 * Z ω) ^ 4 = exp (1 * Z ω) ^ 2 * exp (1 * Z ω) ^ 2 by ring, ← ha2,
        ← exp_add]; ring_nf
    have hb2 : exp ((-2) * Z ω) = (exp (1 * Z ω))⁻¹ ^ 2 := by
      rw [sq, ← exp_neg, ← exp_add]; ring_nf
    have hb4 : exp ((-4) * Z ω) = (exp (1 * Z ω))⁻¹ ^ 4 := by
      rw [show (exp (1 * Z ω))⁻¹ ^ 4 = (exp (1 * Z ω))⁻¹ ^ 2 * (exp (1 * Z ω))⁻¹ ^ 2 by ring,
        ← hb2, ← exp_add]; ring_nf
    have hab : exp (1 * Z ω) * (exp (1 * Z ω))⁻¹ = 1 := mul_inv_cancel₀ (exp_pos _).ne'
    rw [ha2, ha4, hb2, hb4]
    linear_combination (-4 * exp (1 * Z ω) ^ 2 + 6 * (exp (1 * Z ω) * (exp (1 * Z ω))⁻¹ + 1)
      - 4 * (exp (1 * Z ω))⁻¹ ^ 2) * hab
  -- the moments
  have i2c : Integrable (fun ω => exp (2 * Z ω) - 2) P := (hI 2).sub (integrable_const 2)
  have hm2 : ∫ ω, (exp (1 * Z ω) - (exp (1 * Z ω))⁻¹) ^ 2 ∂P = exp x - 2 + exp (3 * x) := by
    simp_rw [hsq]
    rw [integral_add i2c (hI (-2)), integral_sub (hI 2) (integrable_const 2), hE, hE,
      integral_const, probReal_univ, smul_eq_mul, one_mul, hxdef]
    congr 2 <;> ring_nf
  have j1 : Integrable (fun ω => exp (4 * Z ω) - 4 * exp (2 * Z ω)) P :=
    (hI 4).sub ((hI 2).const_mul 4)
  have j2 : Integrable (fun ω => exp (4 * Z ω) - 4 * exp (2 * Z ω) + 6) P :=
    j1.add (integrable_const 6)
  have j3 : Integrable (fun ω => exp (4 * Z ω) - 4 * exp (2 * Z ω) + 6
      - 4 * exp ((-2) * Z ω)) P := j2.sub ((hI (-2)).const_mul 4)
  have hm4 : ∫ ω, (exp (1 * Z ω) - (exp (1 * Z ω))⁻¹) ^ 4 ∂P
      = exp (6 * x) - 4 * exp x + 6 - 4 * exp (3 * x) + exp (10 * x) := by
    simp_rw [hquart]
    rw [integral_add j3 (hI (-4)), integral_sub j2 ((hI (-2)).const_mul 4),
      integral_add j1 (integrable_const 6), integral_sub (hI 4) ((hI 2).const_mul 4),
      integral_const_mul, integral_const_mul, hE, hE, hE, hE, integral_const, probReal_univ,
      smul_eq_mul, one_mul, hxdef]
    congr 2 <;> ring_nf
  have hm1 : ∫ ω, exp (1 * Z ω) ∂P = 1 := by rw [hE]; simp
  have k1 : Integrable (fun ω => exp (2 * Z ω) - 2 * exp (1 * Z ω)) P :=
    (hI 2).sub ((hI 1).const_mul 2)
  have hsqe : ∀ ω, (exp (1 * Z ω) - 1) ^ 2 = exp (2 * Z ω) - 2 * exp (1 * Z ω) + 1 := by
    intro ω
    have ha : exp (2 * Z ω) = exp (1 * Z ω) * exp (1 * Z ω) := by rw [← exp_add]; ring_nf
    rw [ha]; ring
  have hmsq : ∫ ω, (exp (1 * Z ω) - 1) ^ 2 ∂P = exp x - 1 := by
    simp_rw [hsqe]
    rw [integral_add k1 (integrable_const 1), integral_sub (hI 2) ((hI 1).const_mul 2),
      integral_const_mul, hE, hm1, integral_const, probReal_univ, smul_eq_mul, one_mul, hxdef]
    ring_nf
  -- the Taylor remainder function
  set T : CanonicalWienerPath → ℝ := fun ω =>
    exp (-(y * exp (1 * Z ω))) - exp (-y) + y * exp (-y) * (exp (1 * Z ω) - 1)
      - y ^ 2 / 2 * exp (-y) * (exp (1 * Z ω) - 1) ^ 2 with hT
  have hsqI : Integrable (fun ω => (exp (1 * Z ω) - 1) ^ 2) P := by
    simp_rw [hsqe]; exact k1.add (integrable_const 1)
  have hexpI : Integrable (fun ω => exp (-(y * exp (1 * Z ω)))) P := by
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact (continuous_exp.comp ((continuous_const.mul (continuous_exp.comp
        (continuous_const.mul (continuous_logZ D s v)))).neg)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff, neg_nonpos]
      exact mul_nonneg hy (exp_pos _).le
  have l1 : Integrable (fun ω => exp (-(y * exp (1 * Z ω))) - exp (-y)) P :=
    hexpI.sub (integrable_const _)
  have l2 : Integrable (fun ω => y * exp (-y) * (exp (1 * Z ω) - 1)) P :=
    ((hI 1).sub (integrable_const 1)).const_mul _
  have l3 : Integrable (fun ω => exp (-(y * exp (1 * Z ω))) - exp (-y)
      + y * exp (-y) * (exp (1 * Z ω) - 1)) P := l1.add l2
  have l4 : Integrable (fun ω => y ^ 2 / 2 * exp (-y) * (exp (1 * Z ω) - 1) ^ 2) P :=
    hsqI.const_mul _
  have l5 : Integrable (fun ω => exp (1 * Z ω) - 1) P := (hI 1).sub (integrable_const 1)
  have hTI : Integrable T P := l3.sub l4
  have hintT : ∫ ω, T ω ∂P = ∫ ω, exp (-(y * exp (1 * Z ω))) ∂P - exp (-y)
      - y ^ 2 / 2 * exp (-y) * (exp x - 1) := by
    rw [hT, integral_sub l3 l4, integral_add l1 l2, integral_sub hexpI (integrable_const _),
      integral_const_mul, integral_const_mul, integral_sub (hI 1) (integrable_const 1), hm1,
      hmsq, integral_const, integral_const, probReal_univ, smul_eq_mul, smul_eq_mul, one_mul,
      one_mul]
    ring
  -- bound on `∫ |T|`
  have hTpt : ∀ ω, |T ω| ≤ 24 * |exp (1 * Z ω) - (exp (1 * Z ω))⁻¹| ^ 3 := fun ω =>
    abs_exp_taylor2_le hy (exp_pos _)
  set sv := Real.sqrt v with hsv
  have hsv0 : 0 < sv := Real.sqrt_pos.mpr hv'
  have hsvsq : sv ^ 2 = v := Real.sq_sqrt hv'.le
  have hcube : ∀ ω, 24 * |exp (1 * Z ω) - (exp (1 * Z ω))⁻¹| ^ 3 ≤
      12 * (sv * (exp (1 * Z ω) - (exp (1 * Z ω))⁻¹) ^ 2
        + (exp (1 * Z ω) - (exp (1 * Z ω))⁻¹) ^ 4 / sv) := by
    intro ω
    have := abs_pow_three_le (x := exp (1 * Z ω) - (exp (1 * Z ω))⁻¹) hsv0
    linarith
  have hsqmI : Integrable (fun ω => (exp (1 * Z ω) - (exp (1 * Z ω))⁻¹) ^ 2) P := by
    simp_rw [hsq]; exact i2c.add (hI (-2))
  have hquI : Integrable (fun ω => (exp (1 * Z ω) - (exp (1 * Z ω))⁻¹) ^ 4) P := by
    simp_rw [hquart]; exact j3.add (hI (-4))
  have hboundI : ∫ ω, |T ω| ∂P ≤ 12 * (sv * (exp x - 2 + exp (3 * x))
      + (exp (6 * x) - 4 * exp x + 6 - 4 * exp (3 * x) + exp (10 * x)) / sv) := by
    have hR : Integrable (fun ω => 12 * (sv * (exp (1 * Z ω) - (exp (1 * Z ω))⁻¹) ^ 2
        + (exp (1 * Z ω) - (exp (1 * Z ω))⁻¹) ^ 4 / sv)) P :=
      ((hsqmI.const_mul sv).add (hquI.div_const sv)).const_mul 12
    calc ∫ ω, |T ω| ∂P ≤ ∫ ω, 12 * (sv * (exp (1 * Z ω) - (exp (1 * Z ω))⁻¹) ^ 2
          + (exp (1 * Z ω) - (exp (1 * Z ω))⁻¹) ^ 4 / sv) ∂P :=
          integral_mono hTI.abs hR fun ω => (hTpt ω).trans (hcube ω)
      _ = _ := by
          rw [integral_const_mul, integral_add (hsqmI.const_mul sv) (hquI.div_const sv),
            integral_const_mul, integral_div, hm2, hm4]
  -- elementary exponential bounds for `10 x ≤ 1`
  have hx1 : x ≤ 1 / 10 := by rw [hxdef]; linarith
  have b1 := exp_small_bounds hx0 (by linarith : x ≤ 1)
  have b3 := exp_small_bounds (by linarith : 0 ≤ 3 * x) (by linarith : 3 * x ≤ 1)
  have b6 := exp_small_bounds (by linarith : 0 ≤ 6 * x) (by linarith : 6 * x ≤ 1)
  have b10 := exp_small_bounds (by linarith : 0 ≤ 10 * x) (by linarith : 10 * x ≤ 1)
  rw [abs_le] at b1 b3 b6 b10
  have hm2b : exp x - 2 + exp (3 * x) ≤ 8 * x := by nlinarith
  have hm4b : exp (6 * x) - 4 * exp x + 6 - 4 * exp (3 * x) + exp (10 * x) ≤ 176 * x ^ 2 := by
    nlinarith
  have hfinal : 12 * (sv * (exp x - 2 + exp (3 * x))
      + (exp (6 * x) - 4 * exp x + 6 - 4 * exp (3 * x) + exp (10 * x)) / sv)
      ≤ 24 * (4 * D + 88 * D ^ 2) * sv ^ 3 := by
    have h1 : sv * (exp x - 2 + exp (3 * x)) ≤ sv * (8 * x) :=
      mul_le_mul_of_nonneg_left hm2b hsv0.le
    have h2 : (exp (6 * x) - 4 * exp x + 6 - 4 * exp (3 * x) + exp (10 * x)) / sv
        ≤ 176 * x ^ 2 / sv := div_le_div_of_nonneg_right hm4b hsv0.le
    have h3 : sv * (8 * x) + 176 * x ^ 2 / sv = 2 * (4 * D + 88 * D ^ 2) * sv ^ 3 := by
      rw [hxdef, ← hsvsq]; field_simp; ring
    nlinarith
  -- assemble
  have hmain : ∫ ω, exp (-(y * lognormal D s v ω)) ∂P - exp (-y) - v * (D / 2) * y ^ 2 * exp (-y)
      = ∫ ω, T ω ∂P + y ^ 2 / 2 * exp (-y) * (exp x - 1 - x) := by
    simp_rw [hM]
    rw [hintT, hxdef]; ring
  rw [hmain]
  have hy2 : y ^ 2 / 2 * exp (-y) ≤ 1 := by
    have := sq_mul_exp_neg_le hy; linarith
  have hy20 : 0 ≤ y ^ 2 / 2 * exp (-y) := by positivity
  have hrem : |y ^ 2 / 2 * exp (-y) * (exp x - 1 - x)| ≤ D ^ 2 * v ^ 2 := by
    rw [abs_mul, abs_of_nonneg hy20]
    have hb1 : |exp x - 1 - x| ≤ x ^ 2 := exp_small_bounds hx0 (by linarith)
    calc y ^ 2 / 2 * exp (-y) * |exp x - 1 - x| ≤ 1 * x ^ 2 :=
          mul_le_mul hy2 hb1 (abs_nonneg _) zero_le_one
      _ = D ^ 2 * v ^ 2 := by rw [hxdef]; ring
  calc |∫ ω, T ω ∂P + y ^ 2 / 2 * exp (-y) * (exp x - 1 - x)|
      ≤ |∫ ω, T ω ∂P| + |y ^ 2 / 2 * exp (-y) * (exp x - 1 - x)| := abs_add_le _ _
    _ ≤ ∫ ω, |T ω| ∂P + D ^ 2 * v ^ 2 := add_le_add (abs_integral_le_integral_abs) hrem
    _ ≤ _ := by linarith

/-!
## 4. The step on a Laplace transform
-/

/-- Laplace transform `b ↦ ∫ e^{-bx} dμ`. -/
def lap (μ : Measure ℝ) (b : ℝ) : ℝ := ∫ x, exp (-(b * x)) ∂μ

/-- `∫ x² e^{-bx} dμ`, which is `∂_b² lap μ` for `b > 0` (`deriv_deriv_lap`). -/
def lap2 (μ : Measure ℝ) (b : ℝ) : ℝ := ∫ x, x ^ 2 * exp (-(b * x)) ∂μ

theorem lap_eq_max (μ : Measure ℝ) (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (b : ℝ) :
    lap μ b = ∫ x, exp (-(b * max x 0)) ∂μ := by
  unfold lap
  refine integral_congr_ae (hμ.mono fun x hx => ?_)
  simp only [max_eq_left hx]

theorem lap2_eq_max (μ : Measure ℝ) (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (b : ℝ) :
    lap2 μ b = ∫ x, (max x 0) ^ 2 * exp (-(b * max x 0)) ∂μ := by
  unfold lap2
  refine integral_congr_ae (hμ.mono fun x hx => ?_)
  simp only [max_eq_left hx]

theorem lap_nonneg (μ : Measure ℝ) (b : ℝ) : 0 ≤ lap μ b :=
  integral_nonneg fun _ => (exp_pos _).le

theorem lap_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {b : ℝ}
    (hb : 0 ≤ b) : lap μ b ≤ 1 := by
  rw [lap_eq_max μ hμ]
  have h : ∀ x, exp (-(b * max x 0)) ≤ 1 := fun x => by
    rw [exp_le_one_iff, neg_nonpos]; exact mul_nonneg hb (le_max_right _ _)
  calc ∫ x, exp (-(b * max x 0)) ∂μ ≤ ∫ _x, (1 : ℝ) ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => (exp_pos _).le)
          (integrable_const 1) (Filter.Eventually.of_forall h)
    _ = 1 := by simp

/-- **One dual step on a Laplace transform.** For a probability `μ` carried by `[0,∞)`, `b ≥ 0`,
`v > 0`, `10 D v ≤ 1`:
`|E_ω lap μ (b M_v(ω)) - lap μ b - v (D/2) b² lap2 μ b| ≤ 24(4D+88D²) v^{3/2} + D² v²`. -/
theorem abs_integral_lap_lognormal_step {D : ℝ} (hD : 0 ≤ D) (s v : ℝ≥0) (hv : 0 < v)
    (hDv : 10 * D * v ≤ 1) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    {b : ℝ} (hb : 0 ≤ b) :
    |∫ ω, lap μ (b * lognormal D s v ω) ∂canonicalWienerLaw - lap μ b
        - v * (D / 2) * b ^ 2 * lap2 μ b|
      ≤ 24 * (4 * D + 88 * D ^ 2) * Real.sqrt v ^ 3 + D ^ 2 * v ^ 2 := by
  set P := canonicalWienerLaw
  set C := 24 * (4 * D + 88 * D ^ 2) * Real.sqrt v ^ 3 + D ^ 2 * v ^ 2
  set F : CanonicalWienerPath × ℝ → ℝ := fun p =>
    exp (-((b * max p.2 0) * lognormal D s v p.1)) with hF
  have hFm : Measurable F := by
    refine measurable_exp.comp (Measurable.neg ?_)
    exact (measurable_const.mul (measurable_snd.max measurable_const)).mul
      ((measurable_lognormal D s v).comp measurable_fst)
  have hFb : ∀ p, ‖F p‖ ≤ 1 := fun p => by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff, neg_nonpos]
    exact mul_nonneg (mul_nonneg hb (le_max_right _ _)) (lognormal_pos D s v p.1).le
  have hFI : Integrable F (P.prod μ) :=
    Integrable.of_bound hFm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hFb)
  have hlapω : ∀ ω, lap μ (b * lognormal D s v ω) = ∫ x, F (ω, x) ∂μ := by
    intro ω
    rw [lap_eq_max μ hμ]
    congr 1; funext x; simp only [hF]; congr 1; ring
  have hswap : ∫ ω, lap μ (b * lognormal D s v ω) ∂P = ∫ x, (∫ ω, F (ω, x) ∂P) ∂μ := by
    simp_rw [hlapω]
    exact integral_integral_swap hFI
  -- the three `x`-integrands
  set G : ℝ → ℝ := fun x => ∫ ω, F (ω, x) ∂P with hG
  have hGm : StronglyMeasurable G := hFm.stronglyMeasurable.integral_prod_left'
  have hGb : ∀ x, ‖G x‖ ≤ 1 := fun x => by
    refine (norm_integral_le_of_norm_le_const (C := 1) (Filter.Eventually.of_forall
      fun ω => hFb (ω, x))).trans (le_of_eq ?_)
    simp
  have hGI : Integrable G μ := Integrable.of_bound hGm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall hGb)
  set e1 : ℝ → ℝ := fun x => exp (-(b * max x 0))
  set e2 : ℝ → ℝ := fun x => (max x 0) ^ 2 * exp (-(b * max x 0))
  have he1m : Measurable e1 :=
    measurable_exp.comp ((measurable_const.mul (measurable_id.max measurable_const)).neg)
  have he1I : Integrable e1 μ := by
    refine Integrable.of_bound he1m.aestronglyMeasurable 1 (Filter.Eventually.of_forall
      fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff, neg_nonpos]
    exact mul_nonneg hb (le_max_right _ _)
  -- `b² e2` is bounded by 2
  have hbe2 : ∀ x, ‖b ^ 2 * e2 x‖ ≤ 2 := fun x => by
    have h := sq_mul_exp_neg_le (mul_nonneg hb (le_max_right x 0))
    have e : b ^ 2 * e2 x = (b * max x 0) ^ 2 * exp (-(b * max x 0)) := by
      simp only [e2]; ring
    rw [e, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact h
  have he2I : Integrable (fun x => b ^ 2 * e2 x) μ := by
    refine Integrable.of_bound ?_ 2 (Filter.Eventually.of_forall hbe2)
    exact (measurable_const.mul (((measurable_id.max measurable_const).pow_const 2).mul
      he1m)).aestronglyMeasurable
  have hlap : lap μ b = ∫ x, e1 x ∂μ := lap_eq_max μ hμ b
  have hlap2 : b ^ 2 * lap2 μ b = ∫ x, b ^ 2 * e2 x ∂μ := by
    rw [lap2_eq_max μ hμ b, integral_const_mul]
  have hdiff : ∫ ω, lap μ (b * lognormal D s v ω) ∂P - lap μ b - v * (D / 2) * b ^ 2 * lap2 μ b
      = ∫ x, (G x - e1 x - v * (D / 2) * (b ^ 2 * e2 x)) ∂μ := by
    have m1 : Integrable (fun x => G x - e1 x) μ := hGI.sub he1I
    have m2 : Integrable (fun x => v * (D / 2) * (b ^ 2 * e2 x)) μ := he2I.const_mul _
    rw [hswap, integral_sub m1 m2, integral_sub hGI he1I, integral_const_mul, ← hlap2, hlap]
    ring
  rw [hdiff]
  have hpt : ∀ x, ‖G x - e1 x - v * (D / 2) * (b ^ 2 * e2 x)‖ ≤ C := by
    intro x
    set y := b * max x 0 with hy
    have hy0 : 0 ≤ y := mul_nonneg hb (le_max_right _ _)
    have h := abs_integral_exp_lognormal_sub_le hD s v hv hDv hy0
    have eG : G x = ∫ ω, exp (-(y * lognormal D s v ω)) ∂P := rfl
    have e2' : b ^ 2 * e2 x = y ^ 2 * exp (-y) := by simp only [e2, hy]; ring
    rw [Real.norm_eq_abs, eG, e2']
    have e1' : e1 x = exp (-y) := rfl
    rw [e1']
    convert h using 2
    ring
  refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hpt)).trans ?_
  simp

end OpenClock
end BlockBand.Endpoints.Clock
