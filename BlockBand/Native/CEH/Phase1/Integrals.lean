module

public import Mathlib

/-!
# CEH, Phase 1: elementary integrals along the characteristic and Grönwall

Contents (all on `r ≤ 1`, where `η_r ≥ η > 0`; no order between `u` and `t` is needed for the
identities).
* `∫_u^t a / η_r = log (η_u / η_t)` and `exp (∫_u^t c a / η_r) = (η_u / η_t)^c`.
* `∫_u^t a / η_r^α = (η_t^{1-α} - η_u^{1-α}) / (α - 1) ≤ η_t^{1-α} / (α - 1)` for `α > 1`;
  in particular `∫_u^t a / η_r^3 ≤ 1 / (2 η_t^2)`.
* Integral Grönwall on `[0, T]`: if `X, A, F` are continuous on `[0, T]`, `A ≥ 0` and
  `X t ≤ F t + ∫_0^t A X`, then `X t ≤ F t + ∫_0^t F r A r exp (∫_r^t A) dr`.
  If instead `F` is only monotone, `X t ≤ F t exp (∫_0^t A)`.
* The characteristic corollary: if moreover `F r ≤ K / η_r`, `0 ≤ A r ≤ c a / η_r` on `[0, 1]`,
  `K ≥ 0`, `c ≥ 1`, then
  `X t ≤ (K / η_t) (1 + c (η_0 / η_t)^{c - 1} log (η_0 / η_t))`.

No measure other than Lebesgue measure on `ℝ` appears; everything is deterministic (pathwise).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.Phase1

open Set MeasureTheory intervalIntegral

/-!
## The affine height
-/

/-- The height along the characteristic, `η_r = η + a (1 - r)`. -/
def affineHeight (η a r : ℝ) : ℝ := η + a * (1 - r)

theorem affineHeight_one (η a : ℝ) : affineHeight η a 1 = η := by
  simp [affineHeight]

theorem affineHeight_zero (η a : ℝ) : affineHeight η a 0 = η + a := by
  simp [affineHeight]

theorem continuous_affineHeight (η a : ℝ) : Continuous (affineHeight η a) := by
  unfold affineHeight
  fun_prop

theorem hasDerivAt_affineHeight (η a r : ℝ) : HasDerivAt (affineHeight η a) (-a) r := by
  have h := (((hasDerivAt_id r).const_sub 1).const_mul a).const_add η
  simp only [id, mul_neg, mul_one] at h
  exact h

variable {η a : ℝ}

theorem le_affineHeight (ha : 0 ≤ a) {r : ℝ} (hr : r ≤ 1) : η ≤ affineHeight η a r := by
  unfold affineHeight
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hr)]

theorem affineHeight_pos (hη : 0 < η) (ha : 0 ≤ a) {r : ℝ} (hr : r ≤ 1) :
    0 < affineHeight η a r :=
  hη.trans_le (le_affineHeight ha hr)

/-- `r ↦ η_r` is antitone. -/
theorem affineHeight_antitone (ha : 0 ≤ a) {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
    affineHeight η a r₂ ≤ affineHeight η a r₁ := by
  unfold affineHeight
  nlinarith

private theorem le_one_of_mem_uIcc {u t r : ℝ} (hu : u ≤ 1) (ht : t ≤ 1) (hr : r ∈ uIcc u t) :
    r ≤ 1 :=
  hr.2.trans (max_le hu ht)

/-!
## Elementary integrals
-/

/-- `∫_u^t a / η_r dr = log (η_u / η_t)`. -/
theorem integral_div_affineHeight (hη : 0 < η) (ha : 0 ≤ a) {u t : ℝ} (hu : u ≤ 1)
    (ht : t ≤ 1) :
    ∫ r in u..t, a / affineHeight η a r =
      Real.log (affineHeight η a u / affineHeight η a t) := by
  have hderiv : ∀ r ∈ uIcc u t, HasDerivAt (fun r => -Real.log (affineHeight η a r))
      (a / affineHeight η a r) r := by
    intro r hr
    have hpos := affineHeight_pos hη ha (le_one_of_mem_uIcc hu ht hr)
    have h := ((hasDerivAt_affineHeight η a r).log hpos.ne').neg
    convert h using 1
    ring
  have hint : IntervalIntegrable (fun r => a / affineHeight η a r) volume u t :=
    ContinuousOn.intervalIntegrable (continuousOn_const.div
      (continuous_affineHeight η a).continuousOn fun r hr =>
        (affineHeight_pos hη ha (le_one_of_mem_uIcc hu ht hr)).ne')
  rw [integral_eq_sub_of_hasDerivAt hderiv hint,
    Real.log_div (affineHeight_pos hη ha hu).ne' (affineHeight_pos hη ha ht).ne']
  ring

/-- `exp (∫_u^t c a / η_r dr) = (η_u / η_t)^c`. -/
theorem exp_integral_mul_div_affineHeight (hη : 0 < η) (ha : 0 ≤ a) {u t : ℝ} (hu : u ≤ 1)
    (ht : t ≤ 1) (c : ℝ) :
    Real.exp (∫ r in u..t, c * a / affineHeight η a r) =
      (affineHeight η a u / affineHeight η a t) ^ c := by
  have h : ∫ r in u..t, c * a / affineHeight η a r = c * ∫ r in u..t, a / affineHeight η a r := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext r
    ring
  rw [h, integral_div_affineHeight hη ha hu ht,
    Real.rpow_def_of_pos (div_pos (affineHeight_pos hη ha hu) (affineHeight_pos hη ha ht)),
    mul_comm]

/-- `∫_u^t a / η_r^α dr = (η_t^{1-α} - η_u^{1-α}) / (α - 1)` for `α > 1`. -/
theorem integral_div_affineHeight_rpow (hη : 0 < η) (ha : 0 ≤ a) {u t : ℝ} (hu : u ≤ 1)
    (ht : t ≤ 1) {α : ℝ} (hα : 1 < α) :
    ∫ r in u..t, a / affineHeight η a r ^ α =
      (affineHeight η a t ^ (1 - α) - affineHeight η a u ^ (1 - α)) / (α - 1) := by
  have hα1 : α - 1 ≠ 0 := by linarith
  have hderiv : ∀ r ∈ uIcc u t, HasDerivAt (fun r => affineHeight η a r ^ (1 - α) / (α - 1))
      (a / affineHeight η a r ^ α) r := by
    intro r hr
    have hpos := affineHeight_pos hη ha (le_one_of_mem_uIcc hu ht hr)
    have h := ((hasDerivAt_affineHeight η a r).rpow_const (p := 1 - α)
      (Or.inl hpos.ne')).div_const (α - 1)
    convert h using 1
    rw [show 1 - α - 1 = -α by ring, Real.rpow_neg hpos.le]
    have : 0 < affineHeight η a r ^ α := Real.rpow_pos_of_pos hpos α
    field_simp
    ring
  have hint : IntervalIntegrable (fun r => a / affineHeight η a r ^ α) volume u t := by
    refine ContinuousOn.intervalIntegrable (continuousOn_const.div ?_ fun r hr => ?_)
    · exact (continuous_affineHeight η a).continuousOn.rpow_const fun _ _ => Or.inr (by linarith)
    · exact (Real.rpow_pos_of_pos (affineHeight_pos hη ha (le_one_of_mem_uIcc hu ht hr)) α).ne'
  rw [integral_eq_sub_of_hasDerivAt hderiv hint, sub_div]

/-- `∫_u^t a / η_r^α dr ≤ η_t^{1-α} / (α - 1)` for `α > 1`. -/
theorem integral_div_affineHeight_rpow_le (hη : 0 < η) (ha : 0 ≤ a) {u t : ℝ} (hu : u ≤ 1)
    (ht : t ≤ 1) {α : ℝ} (hα : 1 < α) :
    ∫ r in u..t, a / affineHeight η a r ^ α ≤ affineHeight η a t ^ (1 - α) / (α - 1) := by
  rw [integral_div_affineHeight_rpow hη ha hu ht hα]
  have h0 : 0 ≤ affineHeight η a u ^ (1 - α) :=
    Real.rpow_nonneg (affineHeight_pos hη ha hu).le _
  gcongr
  · linarith

/-- `∫_u^t a / η_r^3 dr = 1 / (2 η_t^2) - 1 / (2 η_u^2)`. -/
theorem integral_div_affineHeight_pow_three (hη : 0 < η) (ha : 0 ≤ a) {u t : ℝ} (hu : u ≤ 1)
    (ht : t ≤ 1) :
    ∫ r in u..t, a / affineHeight η a r ^ 3 =
      1 / (2 * affineHeight η a t ^ 2) - 1 / (2 * affineHeight η a u ^ 2) := by
  have h := integral_div_affineHeight_rpow hη ha hu ht (α := 3) (by norm_num)
  have hu' := affineHeight_pos hη ha hu
  have ht' := affineHeight_pos hη ha ht
  have e3 : ∀ x : ℝ, x ^ (3 : ℝ) = x ^ 3 := fun x => by
    exact_mod_cast Real.rpow_natCast x 3
  have e2 : ∀ x : ℝ, 0 < x → x ^ (1 - 3 : ℝ) = 1 / x ^ 2 := fun x hx => by
    rw [show (1 - 3 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hx.le, Real.rpow_natCast]
    simp
  simp only [e3] at h
  rw [h, e2 _ ht', e2 _ hu']
  norm_num
  ring

/-- `∫_u^t a / η_r^3 dr ≤ 1 / (2 η_t^2)`. -/
theorem integral_div_affineHeight_pow_three_le (hη : 0 < η) (ha : 0 ≤ a) {u t : ℝ}
    (hu : u ≤ 1) (ht : t ≤ 1) :
    ∫ r in u..t, a / affineHeight η a r ^ 3 ≤ 1 / (2 * affineHeight η a t ^ 2) := by
  rw [integral_div_affineHeight_pow_three hη ha hu ht]
  have : 0 ≤ 1 / (2 * affineHeight η a u ^ 2) := by positivity
  linarith

/-!
## Grönwall: continuous core
-/

section GronwallContinuous

variable {X A F : ℝ → ℝ} {T : ℝ}

private theorem hasDerivAt_integral_left (hA : Continuous A) (t r : ℝ) :
    HasDerivAt (fun r => ∫ q in r..t, A q) (-A r) r := by
  have h := ((hA.integral_hasStrictDerivAt t r).hasDerivAt).neg
  have e : (fun r => ∫ q in r..t, A q) = fun r => -∫ q in t..r, A q := by
    funext r
    exact intervalIntegral.integral_symm t r
  rw [e]
  exact h

private theorem continuous_integral_left (hA : Continuous A) (t : ℝ) :
    Continuous fun r => ∫ q in r..t, A q :=
  continuous_iff_continuousAt.2 fun r => (hasDerivAt_integral_left hA t r).continuousAt

private theorem continuous_integral_right (hA : Continuous A) (a : ℝ) :
    Continuous fun t => ∫ q in a..t, A q :=
  continuous_iff_continuousAt.2 fun t =>
    ((hA.integral_hasStrictDerivAt a t).hasDerivAt).continuousAt

/-- `∫_0^t A r exp (∫_r^t A) dr = exp (∫_0^t A) - 1` for continuous `A`. -/
theorem integral_mul_exp_integral (hA : Continuous A) (t : ℝ) :
    ∫ r in (0 : ℝ)..t, A r * Real.exp (∫ q in r..t, A q) =
      Real.exp (∫ r in (0 : ℝ)..t, A r) - 1 := by
  have hderiv : ∀ r ∈ uIcc (0 : ℝ) t,
      HasDerivAt (fun r => -Real.exp (∫ q in r..t, A q))
        (A r * Real.exp (∫ q in r..t, A q)) r := by
    intro r _
    have h := ((hasDerivAt_integral_left hA t r).exp).neg
    convert h using 1
    ring
  have hint : IntervalIntegrable (fun r => A r * Real.exp (∫ q in r..t, A q)) volume 0 t :=
    (hA.mul (continuous_integral_left hA t).rexp).intervalIntegrable 0 t
  rw [integral_eq_sub_of_hasDerivAt hderiv hint, intervalIntegral.integral_same,
    Real.exp_zero]
  ring

private theorem gronwall_core (hX : Continuous X) (hA : Continuous A) (hF : Continuous F)
    (hA0 : ∀ r ∈ Icc 0 T, 0 ≤ A r)
    (hle : ∀ t ∈ Icc 0 T, X t ≤ F t + ∫ r in (0 : ℝ)..t, A r * X r) :
    ∀ t ∈ Icc 0 T, (∫ r in (0 : ℝ)..t, A r * X r) ≤
      ∫ r in (0 : ℝ)..t, F r * A r * Real.exp (∫ q in r..t, A q) := by
  set I : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, A r with hIdef
  set Y : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, A r * X r with hYdef
  set K : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, F r * A r * Real.exp (-I r) with hKdef
  have hI : ∀ t, HasDerivAt I (A t) t := fun t => (hA.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hIc : Continuous I := continuous_integral_right hA 0
  have hY : ∀ t, HasDerivAt Y (A t * X t) t := fun t =>
    ((hA.mul hX).integral_hasStrictDerivAt 0 t).hasDerivAt
  have hK : ∀ t, HasDerivAt K (F t * A t * Real.exp (-I t)) t := fun t =>
    (((hF.mul hA).mul hIc.neg.rexp).integral_hasStrictDerivAt 0 t).hasDerivAt
  set g : ℝ → ℝ := fun t => Y t * Real.exp (-I t) - K t with hgdef
  have hg : ∀ t, HasDerivAt g (A t * X t * Real.exp (-I t) +
      Y t * (Real.exp (-I t) * -A t) - F t * A t * Real.exp (-I t)) t := fun t =>
    ((hY t).mul (hI t).neg.exp).sub (hK t)
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
  have hanti : AntitoneOn g (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hgc.continuousOn
      (fun x _ => (hg x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hg x).deriv]
    have hxle := hle x (Ioo_subset_Icc_self hx)
    have hAx := hA0 x (Ioo_subset_Icc_self hx)
    have he := Real.exp_pos (-I x)
    have e : A x * X x * Real.exp (-I x) + Y x * (Real.exp (-I x) * -A x) -
        F x * A x * Real.exp (-I x) = A x * Real.exp (-I x) * (X x - (F x + Y x)) := by ring
    rw [e]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hAx he.le) (by simp only [hYdef]; linarith)
  intro t ht
  have h0 : g 0 = 0 := by simp [hgdef, hYdef, hKdef]
  have hgt : g t ≤ 0 := h0 ▸ hanti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  have hYt : Y t ≤ K t * Real.exp (I t) := by
    have hE := Real.exp_pos (I t)
    have e : Y t = Y t * Real.exp (-I t) * Real.exp (I t) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    rw [e]
    have : Y t * Real.exp (-I t) ≤ K t := by simp only [hgdef] at hgt; linarith
    exact mul_le_mul_of_nonneg_right this hE.le
  have hKI : K t * Real.exp (I t) =
      ∫ r in (0 : ℝ)..t, F r * A r * Real.exp (∫ q in r..t, A q) := by
    rw [hKdef, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun r _ => ?_
    have hsub := intervalIntegral.integral_interval_sub_left (μ := volume)
      (hA.intervalIntegrable 0 t) (hA.intervalIntegrable 0 r)
    simp only [hIdef]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    linarith
  exact hYt.trans hKI.le

/-- Integral Grönwall for continuous data. -/
theorem gronwall_integral_of_continuous (hX : Continuous X) (hA : Continuous A)
    (hF : Continuous F) (hA0 : ∀ r ∈ Icc 0 T, 0 ≤ A r)
    (hle : ∀ t ∈ Icc 0 T, X t ≤ F t + ∫ r in (0 : ℝ)..t, A r * X r) :
    ∀ t ∈ Icc 0 T, X t ≤ F t + ∫ r in (0 : ℝ)..t, F r * A r * Real.exp (∫ q in r..t, A q) :=
  fun t ht => (hle t ht).trans (by linarith [gronwall_core hX hA hF hA0 hle t ht])

/-- Integral Grönwall with a monotone (not necessarily continuous) forcing, continuous data. -/
theorem gronwall_integral_of_continuous_of_monotoneOn (hX : Continuous X) (hA : Continuous A)
    (hA0 : ∀ r ∈ Icc 0 T, 0 ≤ A r) (hF : MonotoneOn F (Icc 0 T))
    (hle : ∀ t ∈ Icc 0 T, X t ≤ F t + ∫ r in (0 : ℝ)..t, A r * X r) :
    ∀ t ∈ Icc 0 T, X t ≤ F t * Real.exp (∫ r in (0 : ℝ)..t, A r) := by
  intro t ht
  have hle' : ∀ s ∈ Icc 0 t, X s ≤ (fun _ => F t) s + ∫ r in (0 : ℝ)..s, A r * X r := by
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
    have := hF hsT ht hs.2
    have := hle s hsT
    linarith
  have h := gronwall_integral_of_continuous hX hA continuous_const
    (fun r hr => hA0 r ⟨hr.1, hr.2.trans ht.2⟩) hle' t ⟨ht.1, le_rfl⟩
  have e : ∫ r in (0 : ℝ)..t, (fun _ => F t) r * A r * Real.exp (∫ q in r..t, A q) =
      F t * (Real.exp (∫ r in (0 : ℝ)..t, A r) - 1) := by
    rw [← integral_mul_exp_integral hA t, ← intervalIntegral.integral_const_mul]
    congr 1
    funext r
    ring
  rw [e] at h
  linarith

private theorem gronwall_affineHeight_of_continuous {η a K c : ℝ} (hη : 0 < η) (ha : 0 ≤ a)
    (hK : 0 ≤ K) (hc : 1 ≤ c) (hX : Continuous X) (hA : Continuous A)
    (hA0 : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ A r)
    (hAle : ∀ r ∈ Icc (0 : ℝ) 1, A r ≤ c * a / affineHeight η a r)
    (hle : ∀ t ∈ Icc (0 : ℝ) 1,
      X t ≤ K / affineHeight η a t + ∫ r in (0 : ℝ)..t, A r * X r) :
    ∀ t ∈ Icc (0 : ℝ) 1, X t ≤ K / affineHeight η a t *
      (1 + c * (affineHeight η a 0 / affineHeight η a t) ^ (c - 1) *
        Real.log (affineHeight η a 0 / affineHeight η a t)) := by
  set Fe : ℝ → ℝ := fun r => K / affineHeight η a (min r 1) with hFe
  have hFec : Continuous Fe :=
    continuous_const.div ((continuous_affineHeight η a).comp (continuous_id.min continuous_const))
      fun r => (affineHeight_pos hη ha (min_le_right r 1)).ne'
  have hFeq : ∀ r ∈ Icc (0 : ℝ) 1, Fe r = K / affineHeight η a r := fun r hr => by
    simp [hFe, min_eq_left hr.2]
  have hle' : ∀ t ∈ Icc (0 : ℝ) 1, X t ≤ Fe t + ∫ r in (0 : ℝ)..t, A r * X r := fun t ht => by
    rw [hFeq t ht]
    exact hle t ht
  intro t ht
  have h := gronwall_integral_of_continuous hX hA hFec hA0 hle' t ht
  rw [hFeq t ht] at h
  set η0 := affineHeight η a 0 with hη0def
  set ηt := affineHeight η a t with hηtdef
  have hηt : 0 < ηt := affineHeight_pos hη ha ht.2
  have hη0 : 0 < η0 := affineHeight_pos hη ha zero_le_one
  set C := c * K * η0 ^ (c - 1) / ηt ^ c with hCdef
  have hC : 0 ≤ C := by
    have : 0 ≤ c := by linarith
    positivity
  have hpt : ∀ r ∈ Icc (0 : ℝ) t,
      Fe r * A r * Real.exp (∫ q in r..t, A q) ≤ C * (a / affineHeight η a r) := by
    intro r hr
    have hr1 : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1, hr.2.trans ht.2⟩
    have hηr : 0 < affineHeight η a r := affineHeight_pos hη ha hr1.2
    rw [hFeq r hr1]
    have hexp : Real.exp (∫ q in r..t, A q) ≤ (affineHeight η a r / ηt) ^ c := by
      rw [← exp_integral_mul_div_affineHeight hη ha hr1.2 ht.2 c]
      refine Real.exp_le_exp.mpr (intervalIntegral.integral_mono_on hr.2
        (hA.intervalIntegrable _ _) ?_ fun q hq => hAle q ⟨hr.1.trans hq.1, hq.2.trans ht.2⟩)
      exact ContinuousOn.intervalIntegrable (continuousOn_const.div
        (continuous_affineHeight η a).continuousOn fun q hq =>
          (affineHeight_pos hη ha (le_one_of_mem_uIcc hr1.2 ht.2 hq)).ne')
    have hAr := hA0 r hr1
    have hAler := hAle r hr1
    have hKr : 0 ≤ K / affineHeight η a r := div_nonneg hK hηr.le
    have hpow : affineHeight η a r ^ c = affineHeight η a r ^ (c - 1) * affineHeight η a r := by
      rw [← Real.rpow_add_one hηr.ne', sub_add_cancel]
    have hle1 : affineHeight η a r ^ (c - 1) / η0 ^ (c - 1) ≤ 1 :=
      div_le_one_of_le₀ (Real.rpow_le_rpow hηr.le (affineHeight_antitone ha hr.1) (by linarith))
        (by positivity)
    have hCa : 0 ≤ C * (a / affineHeight η a r) := by positivity
    calc K / affineHeight η a r * A r * Real.exp (∫ q in r..t, A q)
        ≤ K / affineHeight η a r * (c * a / affineHeight η a r) *
            (affineHeight η a r / ηt) ^ c := by
          have hE := Real.exp_pos (∫ q in r..t, A q)
          have h1 : K / affineHeight η a r * A r ≤
              K / affineHeight η a r * (c * a / affineHeight η a r) :=
            mul_le_mul_of_nonneg_left hAler hKr
          have h2 : 0 ≤ K / affineHeight η a r * (c * a / affineHeight η a r) := by
            have : 0 ≤ c := by linarith
            positivity
          calc K / affineHeight η a r * A r * Real.exp (∫ q in r..t, A q)
              ≤ K / affineHeight η a r * (c * a / affineHeight η a r) *
                  Real.exp (∫ q in r..t, A q) := mul_le_mul_of_nonneg_right h1 hE.le
            _ ≤ _ := mul_le_mul_of_nonneg_left hexp h2
      _ = C * (a / affineHeight η a r) * (affineHeight η a r ^ (c - 1) / η0 ^ (c - 1)) := by
          rw [Real.div_rpow hηr.le hηt.le, hpow, hCdef]
          have : 0 < η0 ^ (c - 1) := Real.rpow_pos_of_pos hη0 _
          have : 0 < ηt ^ c := Real.rpow_pos_of_pos hηt _
          field_simp
      _ ≤ C * (a / affineHeight η a r) * 1 := mul_le_mul_of_nonneg_left hle1 hCa
      _ = C * (a / affineHeight η a r) := mul_one _
  have hRint : IntervalIntegrable (fun r => C * (a / affineHeight η a r)) volume 0 t :=
    ContinuousOn.intervalIntegrable (continuousOn_const.mul (continuousOn_const.div
      (continuous_affineHeight η a).continuousOn fun q hq =>
        (affineHeight_pos hη ha (le_one_of_mem_uIcc zero_le_one ht.2 hq)).ne'))
  have hbound : ∫ r in (0 : ℝ)..t, Fe r * A r * Real.exp (∫ q in r..t, A q) ≤
      ∫ r in (0 : ℝ)..t, C * (a / affineHeight η a r) :=
    intervalIntegral.integral_mono_on ht.1
      (((hFec.mul hA).mul (continuous_integral_left hA t).rexp).intervalIntegrable _ _) hRint hpt
  rw [intervalIntegral.integral_const_mul, integral_div_affineHeight hη ha zero_le_one ht.2,
    ← hη0def, ← hηtdef] at hbound
  have hfinal : K / ηt + C * Real.log (η0 / ηt) =
      K / ηt * (1 + c * (η0 / ηt) ^ (c - 1) * Real.log (η0 / ηt)) := by
    have hpow : ηt ^ c = ηt ^ (c - 1) * ηt := by
      rw [← Real.rpow_add_one hηt.ne', sub_add_cancel]
    rw [Real.div_rpow hη0.le hηt.le, hCdef, hpow]
    have : 0 < ηt ^ (c - 1) := Real.rpow_pos_of_pos hηt _
    field_simp
  linarith [hfinal]

end GronwallContinuous

/-!
## Grönwall on `[0, T]` with data continuous on `[0, T]`
-/

section Gronwall

variable {X A F : ℝ → ℝ} {T : ℝ}

/-- A function continuous on `[0, T]` agrees there with a continuous function on `ℝ`. -/
theorem exists_continuous_eqOn_Icc {f : ℝ → ℝ} (hT : 0 ≤ T) (hf : ContinuousOn f (Icc 0 T)) :
    ∃ g : ℝ → ℝ, Continuous g ∧ EqOn g f (Icc 0 T) :=
  ⟨fun r => f (projIcc 0 T hT r),
    hf.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun r => (projIcc 0 T hT r).2,
    fun r hr => by simp [projIcc_of_mem hT hr]⟩

private theorem integral_congr_Icc {f g : ℝ → ℝ} {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t)
    (htT : t ≤ T) (h : EqOn f g (Icc 0 T)) :
    ∫ r in u..t, f r = ∫ r in u..t, g r := by
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hut] at hr
  exact h ⟨hu.trans hr.1, hr.2.trans htT⟩

/-- **Integral Grönwall.** If `X, A, F` are continuous on `[0, T]`, `A ≥ 0` there and
`X t ≤ F t + ∫_0^t A X` on `[0, T]`, then on `[0, T]`
`X t ≤ F t + ∫_0^t F r A r exp (∫_r^t A) dr`. -/
theorem gronwall_integral (hX : ContinuousOn X (Icc 0 T)) (hA : ContinuousOn A (Icc 0 T))
    (hF : ContinuousOn F (Icc 0 T)) (hA0 : ∀ r ∈ Icc 0 T, 0 ≤ A r)
    (hle : ∀ t ∈ Icc 0 T, X t ≤ F t + ∫ r in (0 : ℝ)..t, A r * X r) :
    ∀ t ∈ Icc 0 T, X t ≤ F t + ∫ r in (0 : ℝ)..t, F r * A r * Real.exp (∫ q in r..t, A q) := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  obtain ⟨X', hX'c, hX'⟩ := exists_continuous_eqOn_Icc hT hX
  obtain ⟨A', hA'c, hA'⟩ := exists_continuous_eqOn_Icc hT hA
  obtain ⟨F', hF'c, hF'⟩ := exists_continuous_eqOn_Icc hT hF
  have hAX : EqOn (fun r => A' r * X' r) (fun r => A r * X r) (Icc 0 T) := fun r hr => by
    simp only [hA' hr, hX' hr]
  have hle' : ∀ s ∈ Icc 0 T, X' s ≤ F' s + ∫ r in (0 : ℝ)..s, A' r * X' r := fun s hs => by
    rw [hX' hs, hF' hs, integral_congr_Icc le_rfl hs.1 hs.2 hAX]
    exact hle s hs
  have h := gronwall_integral_of_continuous hX'c hA'c hF'c
    (fun r hr => (hA' hr).symm ▸ hA0 r hr) hle' t ht
  rw [hX' ht, hF' ht] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le ht.1] at hr
  have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
  simp only [hF' hrT, hA' hrT, integral_congr_Icc hr.1 hr.2 ht.2 hA']

/-- **Integral Grönwall, monotone forcing.** If `X, A` are continuous on `[0, T]`, `A ≥ 0`,
`F` is monotone on `[0, T]` (no continuity) and `X t ≤ F t + ∫_0^t A X` on `[0, T]`, then
`X t ≤ F t exp (∫_0^t A)` on `[0, T]`. -/
theorem gronwall_integral_of_monotoneOn (hX : ContinuousOn X (Icc 0 T))
    (hA : ContinuousOn A (Icc 0 T)) (hA0 : ∀ r ∈ Icc 0 T, 0 ≤ A r)
    (hF : MonotoneOn F (Icc 0 T))
    (hle : ∀ t ∈ Icc 0 T, X t ≤ F t + ∫ r in (0 : ℝ)..t, A r * X r) :
    ∀ t ∈ Icc 0 T, X t ≤ F t * Real.exp (∫ r in (0 : ℝ)..t, A r) := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  obtain ⟨X', hX'c, hX'⟩ := exists_continuous_eqOn_Icc hT hX
  obtain ⟨A', hA'c, hA'⟩ := exists_continuous_eqOn_Icc hT hA
  have hAX : EqOn (fun r => A' r * X' r) (fun r => A r * X r) (Icc 0 T) := fun r hr => by
    simp only [hA' hr, hX' hr]
  have hle' : ∀ s ∈ Icc 0 T, X' s ≤ F s + ∫ r in (0 : ℝ)..s, A' r * X' r := fun s hs => by
    rw [hX' hs, integral_congr_Icc le_rfl hs.1 hs.2 hAX]
    exact hle s hs
  have h := gronwall_integral_of_continuous_of_monotoneOn hX'c hA'c
    (fun r hr => (hA' hr).symm ▸ hA0 r hr) hF hle' t ht
  rwa [hX' ht, integral_congr_Icc le_rfl ht.1 ht.2 hA'] at h

/-- **Grönwall along the characteristic.** Let `η > 0`, `a ≥ 0`, `η_r = η + a (1 - r)`,
`K ≥ 0`, `c ≥ 1`. Let `X, A` be continuous on `[0, 1]` with `0 ≤ A r ≤ c a / η_r`, and let the
forcing satisfy `F r ≤ K / η_r` (no continuity of `F`). If `X t ≤ F t + ∫_0^t A X` on `[0, 1]`,
then on `[0, 1]`
`X t ≤ (K / η_t) (1 + c (η_0 / η_t)^{c - 1} log (η_0 / η_t))`. -/
theorem gronwall_integral_affineHeight {η a K c : ℝ} (hη : 0 < η) (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hc : 1 ≤ c) (hX : ContinuousOn X (Icc 0 1)) (hA : ContinuousOn A (Icc 0 1))
    (hA0 : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ A r)
    (hAle : ∀ r ∈ Icc (0 : ℝ) 1, A r ≤ c * a / affineHeight η a r)
    (hF : ∀ r ∈ Icc (0 : ℝ) 1, F r ≤ K / affineHeight η a r)
    (hle : ∀ t ∈ Icc (0 : ℝ) 1, X t ≤ F t + ∫ r in (0 : ℝ)..t, A r * X r) :
    ∀ t ∈ Icc (0 : ℝ) 1, X t ≤ K / affineHeight η a t *
      (1 + c * (affineHeight η a 0 / affineHeight η a t) ^ (c - 1) *
        Real.log (affineHeight η a 0 / affineHeight η a t)) := by
  intro t ht
  obtain ⟨X', hX'c, hX'⟩ := exists_continuous_eqOn_Icc zero_le_one hX
  obtain ⟨A', hA'c, hA'⟩ := exists_continuous_eqOn_Icc zero_le_one hA
  have hAX : EqOn (fun r => A' r * X' r) (fun r => A r * X r) (Icc 0 1) := fun r hr => by
    simp only [hA' hr, hX' hr]
  have hle' : ∀ s ∈ Icc (0 : ℝ) 1,
      X' s ≤ K / affineHeight η a s + ∫ r in (0 : ℝ)..s, A' r * X' r := fun s hs => by
    rw [hX' hs, integral_congr_Icc le_rfl hs.1 hs.2 hAX]
    linarith [hle s hs, hF s hs]
  have h := gronwall_affineHeight_of_continuous hη ha hK hc hX'c hA'c
    (fun r hr => (hA' hr).symm ▸ hA0 r hr) (fun r hr => (hA' hr).symm ▸ hAle r hr) hle' t ht
  rwa [hX' ht] at h

/-- The case `c = 1`: `X t ≤ (K / η_t) (1 + log (η_0 / η_t))`. -/
theorem gronwall_integral_affineHeight_one {η a K : ℝ} (hη : 0 < η) (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hX : ContinuousOn X (Icc 0 1)) (hA : ContinuousOn A (Icc 0 1))
    (hA0 : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ A r)
    (hAle : ∀ r ∈ Icc (0 : ℝ) 1, A r ≤ a / affineHeight η a r)
    (hF : ∀ r ∈ Icc (0 : ℝ) 1, F r ≤ K / affineHeight η a r)
    (hle : ∀ t ∈ Icc (0 : ℝ) 1, X t ≤ F t + ∫ r in (0 : ℝ)..t, A r * X r) :
    ∀ t ∈ Icc (0 : ℝ) 1, X t ≤ K / affineHeight η a t *
      (1 + Real.log (affineHeight η a 0 / affineHeight η a t)) := by
  intro t ht
  have h := gronwall_integral_affineHeight hη ha hK le_rfl hX hA hA0
    (fun r hr => by rw [one_mul]; exact hAle r hr) hF hle t ht
  simpa using h

end Gronwall

end BlockBand.Native.CEH.Phase1
