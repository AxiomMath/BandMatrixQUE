module

public import BlockBand.Native.CEH.Phase1.Integrals

/-!
# CEH, zig step: the pathwise bootstrap

Setting. Variance time `t ∈ [0, s]`, height `η_t = η + c (s - t)` (`zigHeight`), with
`η, c > 0` (`c = π ρ` in the application). The paths `X_av`, `X_v` (`v ∈ V`, `V` finite) are
complex, continuous on `[0, s]`, vanish at `0`, and are `M + ∫_0 D` with `D` interval integrable.
The threshold `ZigThreshold` (CEH (6.2)) is `‖X_av‖ ≤ θ / (N η_t)` and
`‖X_v‖ ≤ θ w_v / √(N η_t ρ)`; `ZigThresholdStrict` is its strict version.

Contents.
* `zigHeight` and the integrals `∫_u^t c / η_r = log (η_u / η_t)`,
  `∫_u^t β / η_r² = (β / c) (1 / η_t - 1 / η_u)` (for `u, t ≤ s`).
* `averaged_gronwall`, `linear_gronwall`: Grönwall along the height, from the Phase-1 lemmas
  `gronwall_integral` and `gronwall_integral_of_monotoneOn` (stated on a general `[0, T]`, so no
  rescaling of `[0, 1]` is needed).
* `norm_averaged_le`, `norm_vector_le`: the bounds on an interval `[0, T]` where the threshold
  holds.
* `zig_bootstrap`: the continuity argument. The first time `τ` where the strict threshold fails
  is a minimum of a closed set; on `[0, τ]` the bounds hold and are strictly below the
  thresholds, a contradiction. Conclusion on all of `[0, s]`:
  `‖X_av t‖ ≤ 2 K (1 + log (η_0 / η_t)) / (N η_t)` and `‖X_v t‖ ≤ 4 K w_v / √(N η_t ρ)`.
* `norm_target_le`, `norm_target_le_const`: the target quantities after the bootstrap.

Measure: Lebesgue measure on `ℝ` only.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.Zig

open Set MeasureTheory intervalIntegral
open BlockBand.Native.CEH.Phase1

/-!
## The height in variance time
-/

/-- The height in variance time, `η_t = η + c (s - t)`. -/
def zigHeight (η c s t : ℝ) : ℝ := η + c * (s - t)

variable {η c s : ℝ}

theorem zigHeight_self : zigHeight η c s s = η := by
  simp [zigHeight]

theorem zigHeight_zero : zigHeight η c s 0 = η + c * s := by
  simp [zigHeight]

@[fun_prop]
theorem continuous_zigHeight : Continuous (zigHeight η c s) := by
  unfold zigHeight
  fun_prop

theorem hasDerivAt_zigHeight (t : ℝ) : HasDerivAt (zigHeight η c s) (-c) t := by
  have h := ((hasDerivAt_id t).const_sub s |>.const_mul c).const_add η
  simp only [id, mul_neg, mul_one] at h
  exact h

theorem le_zigHeight (hc : 0 ≤ c) {t : ℝ} (ht : t ≤ s) : η ≤ zigHeight η c s t := by
  unfold zigHeight
  nlinarith [mul_nonneg hc (sub_nonneg.mpr ht)]

theorem zigHeight_pos (hη : 0 < η) (hc : 0 ≤ c) {t : ℝ} (ht : t ≤ s) : 0 < zigHeight η c s t :=
  hη.trans_le (le_zigHeight hc ht)

/-- `t ↦ η_t` is antitone. -/
theorem zigHeight_antitone (hc : 0 ≤ c) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    zigHeight η c s t₂ ≤ zigHeight η c s t₁ := by
  unfold zigHeight
  nlinarith

private theorem le_of_mem_uIcc' {u t r : ℝ} (hu : u ≤ s) (ht : t ≤ s) (hr : r ∈ uIcc u t) :
    r ≤ s :=
  hr.2.trans (max_le hu ht)

private theorem zigHeight_ne_zero_on (hη : 0 < η) (hc : 0 ≤ c) {u t : ℝ} (hu : u ≤ s)
    (ht : t ≤ s) : ∀ r ∈ uIcc u t, zigHeight η c s r ≠ 0 := fun _ hr =>
  (zigHeight_pos hη hc (le_of_mem_uIcc' hu ht hr)).ne'

/-- `∫_u^t c / η_r dr = log (η_u / η_t)`. -/
theorem integral_div_zigHeight (hη : 0 < η) (hc : 0 ≤ c) {u t : ℝ} (hu : u ≤ s) (ht : t ≤ s) :
    ∫ r in u..t, c / zigHeight η c s r = Real.log (zigHeight η c s u / zigHeight η c s t) := by
  have hderiv : ∀ r ∈ uIcc u t, HasDerivAt (fun r => -Real.log (zigHeight η c s r))
      (c / zigHeight η c s r) r := by
    intro r hr
    have h := ((hasDerivAt_zigHeight (η := η) (c := c) (s := s) r).log
      (zigHeight_ne_zero_on hη hc hu ht r hr)).neg
    convert h using 1
    ring
  have hint : IntervalIntegrable (fun r => c / zigHeight η c s r) volume u t :=
    ContinuousOn.intervalIntegrable (continuousOn_const.div
      continuous_zigHeight.continuousOn (zigHeight_ne_zero_on hη hc hu ht))
  rw [integral_eq_sub_of_hasDerivAt hderiv hint,
    Real.log_div (zigHeight_pos hη hc hu).ne' (zigHeight_pos hη hc ht).ne']
  ring

/-- `∫_u^t c / η_r² dr = 1 / η_t - 1 / η_u`. -/
theorem integral_div_zigHeight_sq (hη : 0 < η) (hc : 0 ≤ c) {u t : ℝ} (hu : u ≤ s)
    (ht : t ≤ s) :
    ∫ r in u..t, c / zigHeight η c s r ^ 2 = 1 / zigHeight η c s t - 1 / zigHeight η c s u := by
  have hderiv : ∀ r ∈ uIcc u t, HasDerivAt (fun r => (zigHeight η c s r)⁻¹)
      (c / zigHeight η c s r ^ 2) r := by
    intro r hr
    have h := (hasDerivAt_zigHeight (η := η) (c := c) (s := s) r).inv
      (zigHeight_ne_zero_on hη hc hu ht r hr)
    convert h using 1
    ring
  have hint : IntervalIntegrable (fun r => c / zigHeight η c s r ^ 2) volume u t :=
    ContinuousOn.intervalIntegrable (continuousOn_const.div
      (continuous_zigHeight.continuousOn.pow 2) fun r hr =>
        pow_ne_zero 2 (zigHeight_ne_zero_on hη hc hu ht r hr))
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [one_div, one_div]

/-- `∫_u^t β / η_r² dr = (β / c) (1 / η_t - 1 / η_u)` for `c > 0`. -/
theorem integral_const_div_zigHeight_sq (hη : 0 < η) (hc : 0 < c) (β : ℝ) {u t : ℝ}
    (hu : u ≤ s) (ht : t ≤ s) :
    ∫ r in u..t, β / zigHeight η c s r ^ 2 =
      β / c * (1 / zigHeight η c s t - 1 / zigHeight η c s u) := by
  rw [← integral_div_zigHeight_sq hη hc.le hu ht, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun r _ => ?_
  rw [div_mul_div_comm, mul_comm β c, mul_div_mul_left _ _ hc.ne']

/-!
## Scalar Grönwall bounds along the height
-/

private theorem exp_le_two {x : ℝ} (hx : x ≤ 1 / 2) : Real.exp x ≤ 2 := by
  have h1 : Real.exp (1 / 2) < 1 / (1 - 1 / 2) :=
    Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
  have h2 := Real.exp_le_exp.mpr hx
  norm_num at h1
  linarith

/-- `(β / c) (1 / η_t - 1 / η_u) ≤ 1 / 2` when `2 β ≤ c η`, `u ≤ t ≤ s`. -/
private theorem small_of_two_mul_le (hη : 0 < η) (hc : 0 < c) {β : ℝ} (hβ : 0 ≤ β)
    (hδ : 2 * β ≤ c * η) {u t : ℝ} (hu : u ≤ s) (ht : t ≤ s) :
    β / c * (1 / zigHeight η c s t - 1 / zigHeight η c s u) ≤ 1 / 2 := by
  have hu' := zigHeight_pos hη hc.le hu
  have ht' := le_zigHeight (η := η) hc.le ht
  have h1 : 1 / zigHeight η c s t - 1 / zigHeight η c s u ≤ 1 / η := by
    have : 0 < 1 / zigHeight η c s u := by positivity
    have : 1 / zigHeight η c s t ≤ 1 / η := one_div_le_one_div_of_le hη ht'
    linarith
  calc β / c * (1 / zigHeight η c s t - 1 / zigHeight η c s u) ≤ β / c * (1 / η) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg hβ hc.le)
    _ = β / (c * η) := by field_simp
    _ ≤ 1 / 2 := by
        rw [div_le_iff₀ (mul_pos hc hη)]
        linarith

private theorem continuousOn_coeff (hη : 0 < η) (hc : 0 ≤ c) (β : ℝ) {S : Set ℝ}
    (hS : ∀ r ∈ S, r ≤ s) :
    ContinuousOn (fun r => c / zigHeight η c s r + β / zigHeight η c s r ^ 2) S := by
  have hne : ∀ r ∈ S, zigHeight η c s r ≠ 0 := fun r hr => (zigHeight_pos hη hc (hS r hr)).ne'
  exact (continuousOn_const.div continuous_zigHeight.continuousOn hne).add
    (continuousOn_const.div (continuous_zigHeight.continuousOn.pow 2) fun r hr =>
      pow_ne_zero 2 (hne r hr))

private theorem intervalIntegrable_coeff (hη : 0 < η) (hc : 0 ≤ c) (β : ℝ) {u v : ℝ}
    (hu : u ≤ s) (hv : v ≤ s) :
    IntervalIntegrable (fun r => c / zigHeight η c s r + β / zigHeight η c s r ^ 2) volume u v :=
  (continuousOn_coeff hη hc β fun _ hr => le_of_mem_uIcc' hu hv hr).intervalIntegrable

/-- `∫_u^t (c / η_r + β / η_r²) dr = log (η_u / η_t) + (β / c) (1 / η_t - 1 / η_u)`. -/
theorem integral_coeff (hη : 0 < η) (hc : 0 < c) (β : ℝ) {u t : ℝ} (hu : u ≤ s) (ht : t ≤ s) :
    ∫ r in u..t, (c / zigHeight η c s r + β / zigHeight η c s r ^ 2) =
      Real.log (zigHeight η c s u / zigHeight η c s t) +
        β / c * (1 / zigHeight η c s t - 1 / zigHeight η c s u) := by
  have h1 : IntervalIntegrable (fun r => c / zigHeight η c s r) volume u t :=
    ContinuousOn.intervalIntegrable (continuousOn_const.div
      continuous_zigHeight.continuousOn (zigHeight_ne_zero_on hη hc.le hu ht))
  have h2 : IntervalIntegrable (fun r => β / zigHeight η c s r ^ 2) volume u t :=
    ContinuousOn.intervalIntegrable (continuousOn_const.div
      (continuous_zigHeight.continuousOn.pow 2) fun r hr =>
        pow_ne_zero 2 (zigHeight_ne_zero_on hη hc.le hu ht r hr))
  rw [intervalIntegral.integral_add h1 h2, integral_div_zigHeight hη hc.le hu ht,
    integral_const_div_zigHeight_sq hη hc β hu ht]

/-- **Averaged Grönwall along the height.** Let `η > 0`, `c > 0`, `0 ≤ β` with `2 β ≤ c η`,
`K ≥ 0`, `T ≤ s`. If `X` is continuous on `[0, T]` and, on `[0, T]`,
`X t ≤ K / η_t + ∫_0^t (c / η_r + β / η_r²) X r dr`, then on `[0, T]`
`X t ≤ 2 K (1 + log (η_0 / η_t)) / η_t`. -/
theorem averaged_gronwall {X : ℝ → ℝ} {β K T : ℝ} (hη : 0 < η) (hc : 0 < c) (hβ : 0 ≤ β)
    (hK : 0 ≤ K) (hδ : 2 * β ≤ c * η) (hT : T ≤ s) (hX : ContinuousOn X (Icc 0 T))
    (hle : ∀ t ∈ Icc 0 T, X t ≤ K / zigHeight η c s t +
      ∫ r in (0 : ℝ)..t, (c / zigHeight η c s r + β / zigHeight η c s r ^ 2) * X r) :
    ∀ t ∈ Icc 0 T, X t ≤
      2 * K * (1 + Real.log (zigHeight η c s 0 / zigHeight η c s t)) / zigHeight η c s t := by
  intro t ht
  have hts : t ≤ s := ht.2.trans hT
  have h0s : (0 : ℝ) ≤ s := ht.1.trans hts
  have hpos : ∀ r, r ≤ s → 0 < zigHeight η c s r := fun r hr => zigHeight_pos hη hc.le hr
  have hA := continuousOn_coeff hη hc.le β (S := Icc 0 T) fun r hr => hr.2.trans hT
  have hA0 : ∀ r ∈ Icc (0 : ℝ) T, 0 ≤ c / zigHeight η c s r + β / zigHeight η c s r ^ 2 :=
    fun r hr => by
      have := hpos r (hr.2.trans hT)
      positivity
  have hF : ContinuousOn (fun r => K / zigHeight η c s r) (Icc 0 T) :=
    continuousOn_const.div continuous_zigHeight.continuousOn fun r hr =>
      (hpos r (hr.2.trans hT)).ne'
  have hG := gronwall_integral hX hA hF hA0 hle t ht
  set ht' := zigHeight η c s t with hht'
  have hηt : 0 < ht' := hpos t hts
  -- the integrand, made explicit
  set g : ℝ → ℝ := fun r => K / zigHeight η c s r *
    (c / zigHeight η c s r + β / zigHeight η c s r ^ 2) *
    (zigHeight η c s r / ht' * Real.exp (β / c * (1 / ht' - 1 / zigHeight η c s r))) with hg
  have hcongr : ∫ r in (0 : ℝ)..t, K / zigHeight η c s r *
      (c / zigHeight η c s r + β / zigHeight η c s r ^ 2) *
      Real.exp (∫ q in r..t, (c / zigHeight η c s q + β / zigHeight η c s q ^ 2)) =
      ∫ r in (0 : ℝ)..t, g r := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le ht.1] at hr
    have hrs : r ≤ s := hr.2.trans hts
    simp only [hg]
    rw [integral_coeff hη hc β hrs hts, Real.exp_add,
      Real.exp_log (div_pos (hpos r hrs) hηt)]
  have hgc : ContinuousOn g (uIcc 0 t) := by
    have hne : ∀ r ∈ uIcc (0 : ℝ) t, zigHeight η c s r ≠ 0 :=
      zigHeight_ne_zero_on hη hc.le h0s hts
    simp only [hg]
    exact ((continuousOn_const.div continuous_zigHeight.continuousOn hne).mul
      (continuousOn_coeff hη hc.le β fun _ hr => le_of_mem_uIcc' h0s hts hr)).mul
      ((continuous_zigHeight.continuousOn.div continuousOn_const fun _ _ => hηt.ne').mul
        (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul
          (continuousOn_const.sub (continuousOn_const.div continuous_zigHeight.continuousOn
            hne)))))
  have hpt : ∀ r ∈ Icc (0 : ℝ) t, g r ≤
      2 * K / ht' * (c / zigHeight η c s r + β / zigHeight η c s r ^ 2) := by
    intro r hr
    have hrs : r ≤ s := hr.2.trans hts
    have hηr := hpos r hrs
    have hE := exp_le_two (small_of_two_mul_le hη hc hβ hδ hrs hts)
    have ha : 0 ≤ c / zigHeight η c s r + β / zigHeight η c s r ^ 2 := by positivity
    simp only [hg]
    have e : K / zigHeight η c s r * (c / zigHeight η c s r + β / zigHeight η c s r ^ 2) *
        (zigHeight η c s r / ht' * Real.exp (β / c * (1 / ht' - 1 / zigHeight η c s r))) =
        K / ht' * (c / zigHeight η c s r + β / zigHeight η c s r ^ 2) *
          Real.exp (β / c * (1 / ht' - 1 / zigHeight η c s r)) := by
      field_simp
    rw [e]
    have : 0 ≤ K / ht' * (c / zigHeight η c s r + β / zigHeight η c s r ^ 2) := by positivity
    calc K / ht' * (c / zigHeight η c s r + β / zigHeight η c s r ^ 2) *
          Real.exp (β / c * (1 / ht' - 1 / zigHeight η c s r))
        ≤ K / ht' * (c / zigHeight η c s r + β / zigHeight η c s r ^ 2) * 2 :=
          mul_le_mul_of_nonneg_left hE this
      _ = 2 * K / ht' * (c / zigHeight η c s r + β / zigHeight η c s r ^ 2) := by ring
  have hbound := intervalIntegral.integral_mono_on ht.1 (hgc.intervalIntegrable)
    ((intervalIntegrable_coeff hη hc.le β h0s hts).const_mul (2 * K / ht')) hpt
  rw [intervalIntegral.integral_const_mul, integral_coeff hη hc β h0s hts] at hbound
  have hsm := small_of_two_mul_le hη hc hβ hδ h0s hts
  have hKt : 0 ≤ 2 * K / ht' := by positivity
  have h3 : 2 * K / ht' * (Real.log (zigHeight η c s 0 / ht') +
      β / c * (1 / ht' - 1 / zigHeight η c s 0)) ≤
      2 * K / ht' * (Real.log (zigHeight η c s 0 / ht') + 1 / 2) := by
    gcongr
  rw [hcongr] at hG
  have hfin : K / ht' + 2 * K / ht' * (Real.log (zigHeight η c s 0 / ht') + 1 / 2) =
      2 * K * (1 + Real.log (zigHeight η c s 0 / ht')) / ht' := by
    field_simp
    ring
  linarith

/-- **Linear Grönwall with a small coefficient.** Let `η > 0`, `c > 0`, `0 ≤ β` with
`2 β ≤ c η`, `T ≤ s`. If `X, A` are continuous on `[0, T]`, `0 ≤ A r ≤ β / η_r²`, `F` is monotone
and nonnegative on `[0, T]` and `X t ≤ F t + ∫_0^t A X` on `[0, T]`, then `X t ≤ 2 F t` on
`[0, T]`. -/
theorem linear_gronwall {X A F : ℝ → ℝ} {β T : ℝ} (hη : 0 < η) (hc : 0 < c) (hβ : 0 ≤ β)
    (hδ : 2 * β ≤ c * η) (hT : T ≤ s) (hX : ContinuousOn X (Icc 0 T))
    (hA : ContinuousOn A (Icc 0 T)) (hA0 : ∀ r ∈ Icc 0 T, 0 ≤ A r)
    (hAle : ∀ r ∈ Icc 0 T, A r ≤ β / zigHeight η c s r ^ 2) (hF : MonotoneOn F (Icc 0 T))
    (hF0 : ∀ t ∈ Icc 0 T, 0 ≤ F t)
    (hle : ∀ t ∈ Icc 0 T, X t ≤ F t + ∫ r in (0 : ℝ)..t, A r * X r) :
    ∀ t ∈ Icc 0 T, X t ≤ 2 * F t := by
  intro t ht
  have hts : t ≤ s := ht.2.trans hT
  have h0s : (0 : ℝ) ≤ s := ht.1.trans hts
  have hG := gronwall_integral_of_monotoneOn hX hA hA0 hF hle t ht
  have hAI : IntervalIntegrable A volume 0 t :=
    (hA.mono fun r hr => by
      rw [uIcc_of_le ht.1] at hr
      exact ⟨hr.1, hr.2.trans ht.2⟩).intervalIntegrable
  have hBI : IntervalIntegrable (fun r => β / zigHeight η c s r ^ 2) volume 0 t :=
    ContinuousOn.intervalIntegrable (continuousOn_const.div
      (continuous_zigHeight.continuousOn.pow 2) fun r hr =>
        pow_ne_zero 2 (zigHeight_ne_zero_on hη hc.le h0s hts r hr))
  have hint := intervalIntegral.integral_mono_on ht.1 hAI hBI fun r hr =>
    hAle r ⟨hr.1, hr.2.trans ht.2⟩
  rw [integral_const_div_zigHeight_sq hη hc β h0s hts] at hint
  have hE := exp_le_two (hint.trans (small_of_two_mul_le hη hc hβ hδ h0s hts))
  have := hF0 t ht
  calc X t ≤ F t * Real.exp (∫ r in (0 : ℝ)..t, A r) := hG
    _ ≤ F t * 2 := mul_le_mul_of_nonneg_left hE this
    _ = 2 * F t := mul_comm _ _

/-!
## Pathwise bounds on an interval where the threshold holds
-/

/-- `‖X t‖ ≤ ‖M t‖ + ∫_0^t g` when `X = M + ∫_0 D` and `‖D‖ ≤ g` on `[0, t]`. -/
theorem norm_le_of_decomposition {X M D : ℝ → ℂ} {g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hD : IntervalIntegrable D volume 0 t) (hg : IntervalIntegrable g volume 0 t)
    (hdec : X t = M t + ∫ r in (0 : ℝ)..t, D r) (hDg : ∀ r ∈ Icc 0 t, ‖D r‖ ≤ g r) :
    ‖X t‖ ≤ ‖M t‖ + ∫ r in (0 : ℝ)..t, g r := by
  rw [hdec]
  refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
  exact (intervalIntegral.norm_integral_le_integral_norm ht).trans
    (intervalIntegral.integral_mono_on ht hD.norm hg hDg)

private theorem uIcc_subset_of_mem {t T : ℝ} (ht : t ∈ Icc 0 T) :
    uIcc 0 t ⊆ uIcc 0 T := by
  rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
  exact Icc_subset_Icc_right ht.2

private theorem uIcc_subset_Icc_of_mem {t T : ℝ} (ht : t ∈ Icc 0 T) :
    uIcc 0 t ⊆ Icc 0 T := by
  rw [uIcc_of_le ht.1]
  exact Icc_subset_Icc_right ht.2

/-- **Averaged bound.** On `[0, T]`, `T ≤ s`, let `X = M + ∫_0 D` with `X` continuous,
`‖X r‖ ≤ θ / (N η_r)` (threshold), `‖D r‖ ≤ ‖X r‖ (c + ‖X r‖) / η_r` (drift) and
`‖M t‖ ≤ K / (N η_t)` (martingale). If `2 θ ≤ N c η`, then on `[0, T]`
`‖X t‖ ≤ 2 K (1 + log (η_0 / η_t)) / (N η_t)`. -/
theorem norm_averaged_le {X M D : ℝ → ℂ} {N θ K T : ℝ} (hN : 0 < N) (hη : 0 < η) (hc : 0 < c)
    (hθ : 0 ≤ θ) (hK : 0 ≤ K) (hsmall : 2 * θ ≤ N * c * η) (hT : T ≤ s)
    (hX : ContinuousOn X (Icc 0 T)) (hD : IntervalIntegrable D volume 0 T)
    (hdec : ∀ t ∈ Icc 0 T, X t = M t + ∫ r in (0 : ℝ)..t, D r)
    (hthr : ∀ r ∈ Icc 0 T, ‖X r‖ ≤ θ / (N * zigHeight η c s r))
    (hdrift : ∀ r ∈ Icc 0 T, ‖D r‖ ≤ ‖X r‖ * (c + ‖X r‖) / zigHeight η c s r)
    (hmart : ∀ t ∈ Icc 0 T, ‖M t‖ ≤ K / (N * zigHeight η c s t)) :
    ∀ t ∈ Icc 0 T, ‖X t‖ ≤
      2 * K * (1 + Real.log (zigHeight η c s 0 / zigHeight η c s t)) /
        (N * zigHeight η c s t) := by
  have hpos : ∀ r, r ≤ s → 0 < zigHeight η c s r := fun r hr => zigHeight_pos hη hc.le hr
  have hβ : 0 ≤ θ / N := div_nonneg hθ hN.le
  have hδ : 2 * (θ / N) ≤ c * η := by
    rw [mul_div_assoc', div_le_iff₀ hN]
    linarith
  have hle : ∀ t ∈ Icc 0 T, ‖X t‖ ≤ K / N / zigHeight η c s t +
      ∫ r in (0 : ℝ)..t, (c / zigHeight η c s r + θ / N / zigHeight η c s r ^ 2) * ‖X r‖ := by
    intro t ht
    have hg : IntervalIntegrable (fun r =>
        (c / zigHeight η c s r + θ / N / zigHeight η c s r ^ 2) * ‖X r‖) volume 0 t :=
      (((continuousOn_coeff hη hc.le (θ / N) fun r hr => hr.2.trans hT).mul hX.norm).mono
        (uIcc_subset_Icc_of_mem ht)).intervalIntegrable
    have h := norm_le_of_decomposition ht.1 (hD.mono_set (uIcc_subset_of_mem ht)) hg
      (hdec t ht) fun r hr => by
        have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
        have hηr := hpos r (hrT.2.trans hT)
        calc ‖D r‖ ≤ ‖X r‖ * (c + ‖X r‖) / zigHeight η c s r := hdrift r hrT
          _ ≤ ‖X r‖ * (c + θ / (N * zigHeight η c s r)) / zigHeight η c s r := by
            gcongr
            exact hthr r hrT
          _ = (c / zigHeight η c s r + θ / N / zigHeight η c s r ^ 2) * ‖X r‖ := by
            field_simp
    rw [div_div]
    linarith [hmart t ht]
  intro t ht
  have h := averaged_gronwall hη hc hβ (div_nonneg hK hN.le) hδ hT hX.norm hle t ht
  calc ‖X t‖ ≤ _ := h
    _ = _ := by
      have := hpos t (ht.2.trans hT)
      field_simp

/-- `θ / (N c η_t) ≤ K / √(N η_t ρ)` when `θ² ρ ≤ K² c² N η`. -/
private theorem div_le_div_sqrt {N θ K ρ : ℝ} (hN : 0 < N) (hη : 0 < η) (hc : 0 < c)
    (hθ : 0 ≤ θ) (hK : 0 ≤ K) (hρ : 0 < ρ) (hsmall : θ ^ 2 * ρ ≤ K ^ 2 * c ^ 2 * (N * η))
    {t : ℝ} (ht : t ≤ s) :
    θ / (N * c * zigHeight η c s t) ≤ K / Real.sqrt (N * zigHeight η c s t * ρ) := by
  have hηt := zigHeight_pos hη hc.le ht
  have hle := le_zigHeight (η := η) hc.le ht
  have hS : 0 < Real.sqrt (N * zigHeight η c s t * ρ) := Real.sqrt_pos.mpr (by positivity)
  have hS2 : Real.sqrt (N * zigHeight η c s t * ρ) ^ 2 = N * zigHeight η c s t * ρ :=
    Real.sq_sqrt (by positivity)
  rw [div_le_div_iff₀ (by positivity) hS]
  have h1 : (θ * Real.sqrt (N * zigHeight η c s t * ρ)) ^ 2 ≤
      (K * (N * c * zigHeight η c s t)) ^ 2 := by
    rw [mul_pow, hS2]
    have : θ ^ 2 * ρ ≤ K ^ 2 * c ^ 2 * (N * zigHeight η c s t) :=
      hsmall.trans (by gcongr)
    have hNt : 0 < N * zigHeight η c s t := by positivity
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h1

/-- **Vector bound.** On `[0, T]`, `T ≤ s`, let `X = M + ∫_0 D` with `X` and `Y` continuous,
`‖Y r‖ ≤ θ / (N η_r)` (averaged threshold), `‖D r‖ ≤ ‖Y r‖ (w + ‖X r‖) / η_r` (drift) and
`‖M t‖ ≤ K w / √(N η_t ρ)` (martingale). If `2 θ ≤ N c η` and `θ² ρ ≤ K² c² N η`, then on
`[0, T]` `‖X t‖ ≤ 4 K w / √(N η_t ρ)`. -/
theorem norm_vector_le {X M D Y : ℝ → ℂ} {N θ K ρ w T : ℝ} (hN : 0 < N) (hη : 0 < η)
    (hc : 0 < c) (hθ : 0 ≤ θ) (hK : 0 ≤ K) (hρ : 0 < ρ) (hw : 0 ≤ w)
    (hsmall₂ : 2 * θ ≤ N * c * η) (hsmall₃ : θ ^ 2 * ρ ≤ K ^ 2 * c ^ 2 * (N * η)) (hT : T ≤ s)
    (hX : ContinuousOn X (Icc 0 T)) (hY : ContinuousOn Y (Icc 0 T))
    (hD : IntervalIntegrable D volume 0 T)
    (hdec : ∀ t ∈ Icc 0 T, X t = M t + ∫ r in (0 : ℝ)..t, D r)
    (hthr : ∀ r ∈ Icc 0 T, ‖Y r‖ ≤ θ / (N * zigHeight η c s r))
    (hdrift : ∀ r ∈ Icc 0 T, ‖D r‖ ≤ ‖Y r‖ * (w + ‖X r‖) / zigHeight η c s r)
    (hmart : ∀ t ∈ Icc 0 T, ‖M t‖ ≤ K * w / Real.sqrt (N * zigHeight η c s t * ρ)) :
    ∀ t ∈ Icc 0 T, ‖X t‖ ≤ 4 * K * w / Real.sqrt (N * zigHeight η c s t * ρ) := by
  have hpos : ∀ r, r ≤ s → 0 < zigHeight η c s r := fun r hr => zigHeight_pos hη hc.le hr
  have hne : ∀ r ∈ Icc (0 : ℝ) T, zigHeight η c s r ≠ 0 := fun r hr =>
    (hpos r (hr.2.trans hT)).ne'
  have hβ : 0 ≤ θ / N := div_nonneg hθ hN.le
  have hδ : 2 * (θ / N) ≤ c * η := by
    rw [mul_div_assoc', div_le_iff₀ hN]
    linarith
  set A : ℝ → ℝ := fun r => ‖Y r‖ / zigHeight η c s r with hAdef
  set G : ℝ → ℝ := fun r => w * ‖Y r‖ / zigHeight η c s r with hGdef
  set F : ℝ → ℝ := fun t => K * w / Real.sqrt (N * zigHeight η c s t * ρ) +
    ∫ r in (0 : ℝ)..t, G r with hFdef
  have hA : ContinuousOn A (Icc 0 T) :=
    hY.norm.div continuous_zigHeight.continuousOn hne
  have hGc : ContinuousOn G (Icc 0 T) :=
    (continuousOn_const.mul hY.norm).div continuous_zigHeight.continuousOn hne
  have hA0 : ∀ r ∈ Icc 0 T, 0 ≤ A r := fun r hr => by
    have := hpos r (hr.2.trans hT)
    simp only [hAdef]
    positivity
  have hG0 : ∀ r ∈ Icc 0 T, 0 ≤ G r := fun r hr => by
    have := hpos r (hr.2.trans hT)
    simp only [hGdef]
    positivity
  have hAle : ∀ r ∈ Icc 0 T, A r ≤ θ / N / zigHeight η c s r ^ 2 := fun r hr => by
    have := hpos r (hr.2.trans hT)
    simp only [hAdef]
    calc ‖Y r‖ / zigHeight η c s r ≤ θ / (N * zigHeight η c s r) / zigHeight η c s r := by
          gcongr
          exact hthr r hr
      _ = θ / N / zigHeight η c s r ^ 2 := by field_simp
  have hSmono : ∀ t₁ ∈ Icc (0 : ℝ) T, ∀ t₂ ∈ Icc (0 : ℝ) T, t₁ ≤ t₂ →
      K * w / Real.sqrt (N * zigHeight η c s t₁ * ρ) ≤
        K * w / Real.sqrt (N * zigHeight η c s t₂ * ρ) := by
    intro t₁ _ t₂ ht₂ h12
    have := hpos t₂ (ht₂.2.trans hT)
    refine div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr (by positivity))
      (Real.sqrt_le_sqrt ?_)
    have := zigHeight_antitone (η := η) (s := s) hc.le h12
    gcongr
  have hF : MonotoneOn F (Icc 0 T) := by
    intro t₁ ht₁ t₂ ht₂ h12
    simp only [hFdef]
    refine add_le_add (hSmono t₁ ht₁ t₂ ht₂ h12) ?_
    refine intervalIntegral.integral_mono_interval le_rfl ht₁.1 h12
      (ae_restrict_of_forall_mem measurableSet_Ioc fun r hr =>
        hG0 r ⟨hr.1.le, hr.2.trans ht₂.2⟩)
      (hGc.mono (uIcc_subset_Icc_of_mem ht₂)).intervalIntegrable
  have hF0 : ∀ t ∈ Icc 0 T, 0 ≤ F t := fun t ht => by
    have := hpos t (ht.2.trans hT)
    have hI : 0 ≤ ∫ r in (0 : ℝ)..t, G r :=
      intervalIntegral.integral_nonneg ht.1 fun r hr => hG0 r ⟨hr.1, hr.2.trans ht.2⟩
    simp only [hFdef]
    positivity
  have hle : ∀ t ∈ Icc 0 T, ‖X t‖ ≤ F t + ∫ r in (0 : ℝ)..t, A r * ‖X r‖ := by
    intro t ht
    have hGi : IntervalIntegrable G volume 0 t :=
      (hGc.mono (uIcc_subset_Icc_of_mem ht)).intervalIntegrable
    have hAXi : IntervalIntegrable (fun r => A r * ‖X r‖) volume 0 t :=
      ((hA.mul hX.norm).mono (uIcc_subset_Icc_of_mem ht)).intervalIntegrable
    have h := norm_le_of_decomposition ht.1 (hD.mono_set (uIcc_subset_of_mem ht))
      (hGi.add hAXi) (hdec t ht) fun r hr => by
        have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
        have := hpos r (hrT.2.trans hT)
        refine (hdrift r hrT).trans (le_of_eq ?_)
        simp only [hAdef, hGdef]
        field_simp
    rw [intervalIntegral.integral_add hGi hAXi] at h
    simp only [hFdef]
    linarith [hmart t ht]
  intro t ht
  have hts : t ≤ s := ht.2.trans hT
  have h0s : (0 : ℝ) ≤ s := ht.1.trans hts
  have hηt := hpos t hts
  have h2 := linear_gronwall hη hc hβ hδ hT hX.norm hA hA0 hAle hF hF0 hle t ht
  -- bound the forcing
  have hGI : ∫ r in (0 : ℝ)..t, G r ≤ w * (θ / N) / c *
      (1 / zigHeight η c s t - 1 / zigHeight η c s 0) := by
    rw [← integral_const_div_zigHeight_sq hη hc _ h0s hts]
    refine intervalIntegral.integral_mono_on ht.1
      (hGc.mono (uIcc_subset_Icc_of_mem ht)).intervalIntegrable ?_ fun r hr => ?_
    · exact ContinuousOn.intervalIntegrable (continuousOn_const.div
        (continuous_zigHeight.continuousOn.pow 2) fun r hr =>
          pow_ne_zero 2 (zigHeight_ne_zero_on hη hc.le h0s hts r hr))
    · have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
      have hAr := hAle r hrT
      simp only [hAdef] at hAr
      simp only [hGdef, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hAr hw
  have hG2 : w * (θ / N) / c * (1 / zigHeight η c s t - 1 / zigHeight η c s 0) ≤
      K * w / Real.sqrt (N * zigHeight η c s t * ρ) := by
    have h0 : 0 < 1 / zigHeight η c s 0 := by
      have := hpos 0 h0s
      positivity
    have hk := div_le_div_sqrt hN hη hc hθ hK hρ hsmall₃ hts
    calc w * (θ / N) / c * (1 / zigHeight η c s t - 1 / zigHeight η c s 0)
        ≤ w * (θ / N) / c * (1 / zigHeight η c s t) := by
          have : 0 ≤ w * (θ / N) / c := by positivity
          gcongr
          linarith
      _ = w * (θ / (N * c * zigHeight η c s t)) := by field_simp
      _ ≤ w * (K / Real.sqrt (N * zigHeight η c s t * ρ)) := mul_le_mul_of_nonneg_left hk hw
      _ = K * w / Real.sqrt (N * zigHeight η c s t * ρ) := by ring
  simp only [hFdef] at h2
  calc ‖X t‖ ≤ 2 * (K * w / Real.sqrt (N * zigHeight η c s t * ρ) +
        ∫ r in (0 : ℝ)..t, G r) := h2
    _ ≤ 2 * (K * w / Real.sqrt (N * zigHeight η c s t * ρ) +
        K * w / Real.sqrt (N * zigHeight η c s t * ρ)) := by linarith
    _ = 4 * K * w / Real.sqrt (N * zigHeight η c s t * ρ) := by ring

/-!
## The threshold condition (CEH (6.2))
-/

section Threshold

variable {V : Type*}

/-- The threshold condition at time `t` (non-strict): `‖X_av t‖ ≤ θ / (N η_t)` and
`‖X_v t‖ ≤ θ w_v / √(N η_t ρ)` for all `v`. -/
def ZigThreshold (N η c s ρ θ : ℝ) (w : V → ℝ) (Xav : ℝ → ℂ) (Xv : V → ℝ → ℂ) (t : ℝ) :
    Prop :=
  ‖Xav t‖ ≤ θ / (N * zigHeight η c s t) ∧
    ∀ v, ‖Xv v t‖ ≤ θ * w v / Real.sqrt (N * zigHeight η c s t * ρ)

/-- The strict threshold condition at time `t`. -/
def ZigThresholdStrict (N η c s ρ θ : ℝ) (w : V → ℝ) (Xav : ℝ → ℂ) (Xv : V → ℝ → ℂ)
    (t : ℝ) : Prop :=
  ‖Xav t‖ < θ / (N * zigHeight η c s t) ∧
    ∀ v, ‖Xv v t‖ < θ * w v / Real.sqrt (N * zigHeight η c s t * ρ)

variable {N ρ θ : ℝ} {w : V → ℝ} {Xav : ℝ → ℂ} {Xv : V → ℝ → ℂ}

theorem ZigThresholdStrict.le {t : ℝ} (h : ZigThresholdStrict N η c s ρ θ w Xav Xv t) :
    ZigThreshold N η c s ρ θ w Xav Xv t :=
  ⟨h.1.le, fun v => (h.2 v).le⟩

/-- The gap map: thresholds subtracted from the norms. -/
private def gapMap (N η c s ρ θ : ℝ) (w : V → ℝ) (Xav : ℝ → ℂ) (Xv : V → ℝ → ℂ) (t : ℝ) :
    ℝ × (V → ℝ) :=
  (‖Xav t‖ - θ / (N * zigHeight η c s t),
    fun v => ‖Xv v t‖ - θ * w v / Real.sqrt (N * zigHeight η c s t * ρ))

private theorem continuousOn_gapMap (hN : 0 < N) (hη : 0 < η) (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hXav : ContinuousOn Xav (Icc 0 s)) (hXv : ∀ v, ContinuousOn (Xv v) (Icc 0 s)) :
    ContinuousOn (gapMap N η c s ρ θ w Xav Xv) (Icc 0 s) := by
  have hpos : ∀ r ∈ Icc (0 : ℝ) s, 0 < zigHeight η c s r := fun r hr =>
    zigHeight_pos hη hc hr.2
  refine ContinuousOn.prodMk (hXav.norm.sub (continuousOn_const.div
    (continuousOn_const.mul continuous_zigHeight.continuousOn) fun r hr =>
      (mul_pos hN (hpos r hr)).ne')) (continuousOn_pi.2 fun v => ?_)
  exact (hXv v).norm.sub (continuousOn_const.div
    ((continuousOn_const.mul continuous_zigHeight.continuousOn).mul continuousOn_const).sqrt
      fun r hr => (Real.sqrt_pos.mpr (mul_pos (mul_pos hN (hpos r hr)) hρ)).ne')

private theorem threshold_iff_gapMap {t : ℝ} :
    ZigThreshold N η c s ρ θ w Xav Xv t ↔
      gapMap N η c s ρ θ w Xav Xv t ∈ {p : ℝ × (V → ℝ) | p.1 ≤ 0 ∧ ∀ v, p.2 v ≤ 0} := by
  simp [ZigThreshold, gapMap]

private theorem thresholdStrict_iff_gapMap {t : ℝ} :
    ZigThresholdStrict N η c s ρ θ w Xav Xv t ↔
      gapMap N η c s ρ θ w Xav Xv t ∈ {p : ℝ × (V → ℝ) | p.1 < 0 ∧ ∀ v, p.2 v < 0} := by
  simp [ZigThresholdStrict, gapMap, sub_neg]

private theorem isClosed_threshold (hN : 0 < N) (hη : 0 < η) (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hXav : ContinuousOn Xav (Icc 0 s)) (hXv : ∀ v, ContinuousOn (Xv v) (Icc 0 s)) :
    IsClosed (Icc 0 s ∩ {t | ZigThreshold N η c s ρ θ w Xav Xv t}) := by
  have hcl : IsClosed {p : ℝ × (V → ℝ) | p.1 ≤ 0 ∧ ∀ v, p.2 v ≤ 0} := by
    have e : {p : ℝ × (V → ℝ) | p.1 ≤ 0 ∧ ∀ v, p.2 v ≤ 0} =
        {p : ℝ × (V → ℝ) | p.1 ≤ 0} ∩ ⋂ v, {p : ℝ × (V → ℝ) | p.2 v ≤ 0} := by
      ext p
      simp
    rw [e]
    exact (isClosed_le continuous_fst continuous_const).inter (isClosed_iInter fun v =>
      isClosed_le ((continuous_apply v).comp continuous_snd) continuous_const)
  have h := (continuousOn_gapMap (θ := θ) (w := w) hN hη hc hρ hXav
    hXv).preimage_isClosed_of_isClosed
    isClosed_Icc hcl
  convert h using 1
  ext t
  simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
  rw [threshold_iff_gapMap]
  rfl

private theorem isClosed_not_thresholdStrict [Finite V] (hN : 0 < N) (hη : 0 < η)
    (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hXav : ContinuousOn Xav (Icc 0 s)) (hXv : ∀ v, ContinuousOn (Xv v) (Icc 0 s)) :
    IsClosed (Icc 0 s ∩ {t | ¬ ZigThresholdStrict N η c s ρ θ w Xav Xv t}) := by
  have hop : IsOpen {p : ℝ × (V → ℝ) | p.1 < 0 ∧ ∀ v, p.2 v < 0} := by
    have e : {p : ℝ × (V → ℝ) | p.1 < 0 ∧ ∀ v, p.2 v < 0} =
        {p : ℝ × (V → ℝ) | p.1 < 0} ∩ ⋂ v, {p : ℝ × (V → ℝ) | p.2 v < 0} := by
      ext p
      simp
    rw [e]
    exact (isOpen_lt continuous_fst continuous_const).inter (isOpen_iInter_of_finite fun v =>
      isOpen_lt ((continuous_apply v).comp continuous_snd) continuous_const)
  have h := (continuousOn_gapMap (θ := θ) (w := w) hN hη hc hρ hXav
    hXv).preimage_isClosed_of_isClosed
    isClosed_Icc hop.isClosed_compl
  convert h using 1
  ext t
  simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_compl_iff]
  rw [thresholdStrict_iff_gapMap]
  rfl

end Threshold

/-!
## The bootstrap
-/

/-- **Zig bootstrap (CEH §6.1, (6.2)–(6.3)), pathwise.**

Variance time `t ∈ [0, s]`, height `η_t = η + c (s - t)` (`zigHeight η c s t`), `η, c, ρ, N > 0`,
`K ≥ 0`, finite index set `V`, weights `w_v > 0`. The complex paths `X_av`, `X_v` are continuous
on `[0, s]`, vanish at `0`, and decompose as `X = M + ∫_0 D` with `D` integrable on `[0, s]`.
* Drift: wherever the (non-strict) threshold `ZigThreshold` holds,
  `‖D_av‖ ≤ ‖X_av‖ (c + ‖X_av‖) / η_r` and `‖D_v‖ ≤ ‖X_av‖ (w_v + ‖X_v‖) / η_r`.
* Martingale: at every `t ∈ [0, s]` such that the strict threshold holds on `[0, t)`,
  `‖M_av t‖ ≤ K / (N η_t)` and `‖M_v t‖ ≤ K w_v / √(N η_t ρ)`.
* Smallness: `4 K (1 + log (η_0 / η)) < θ`, `2 θ ≤ N c η` and `θ² ρ ≤ K² c² N η`.

Then on all of `[0, s]` the strict threshold holds, and
`‖X_av t‖ ≤ 2 K (1 + log (η_0 / η_t)) / (N η_t)`, `‖X_v t‖ ≤ 4 K w_v / √(N η_t ρ)`. -/
theorem zig_bootstrap {V : Type*} [Finite V] {N η c s ρ θ K : ℝ} {w : V → ℝ}
    {Xav Mav Dav : ℝ → ℂ} {Xv Mv Dv : V → ℝ → ℂ}
    (hN : 0 < N) (hη : 0 < η) (hc : 0 < c) (hρ : 0 < ρ) (hK : 0 ≤ K) (hw : ∀ v, 0 < w v)
    (hsmall₁ : 4 * K * (1 + Real.log (zigHeight η c s 0 / η)) < θ)
    (hsmall₂ : 2 * θ ≤ N * c * η)
    (hsmall₃ : θ ^ 2 * ρ ≤ K ^ 2 * c ^ 2 * (N * η))
    (hXav : ContinuousOn Xav (Icc 0 s)) (hXv : ∀ v, ContinuousOn (Xv v) (Icc 0 s))
    (hXav0 : Xav 0 = 0) (hXv0 : ∀ v, Xv v 0 = 0)
    (hDav : IntervalIntegrable Dav volume 0 s)
    (hDv : ∀ v, IntervalIntegrable (Dv v) volume 0 s)
    (hdecav : ∀ t ∈ Icc 0 s, Xav t = Mav t + ∫ r in (0 : ℝ)..t, Dav r)
    (hdecv : ∀ v, ∀ t ∈ Icc 0 s, Xv v t = Mv v t + ∫ r in (0 : ℝ)..t, Dv v r)
    (hdriftav : ∀ r ∈ Icc 0 s, ZigThreshold N η c s ρ θ w Xav Xv r →
      ‖Dav r‖ ≤ ‖Xav r‖ * (c + ‖Xav r‖) / zigHeight η c s r)
    (hdriftv : ∀ v, ∀ r ∈ Icc 0 s, ZigThreshold N η c s ρ θ w Xav Xv r →
      ‖Dv v r‖ ≤ ‖Xav r‖ * (w v + ‖Xv v r‖) / zigHeight η c s r)
    (hmartav : ∀ t ∈ Icc 0 s, (∀ r ∈ Ico 0 t, ZigThresholdStrict N η c s ρ θ w Xav Xv r) →
      ‖Mav t‖ ≤ K / (N * zigHeight η c s t))
    (hmartv : ∀ v, ∀ t ∈ Icc 0 s,
      (∀ r ∈ Ico 0 t, ZigThresholdStrict N η c s ρ θ w Xav Xv r) →
      ‖Mv v t‖ ≤ K * w v / Real.sqrt (N * zigHeight η c s t * ρ)) :
    ∀ t ∈ Icc 0 s, ZigThresholdStrict N η c s ρ θ w Xav Xv t ∧
      ‖Xav t‖ ≤ 2 * K * (1 + Real.log (zigHeight η c s 0 / zigHeight η c s t)) /
        (N * zigHeight η c s t) ∧
      ∀ v, ‖Xv v t‖ ≤ 4 * K * w v / Real.sqrt (N * zigHeight η c s t * ρ) := by
  intro t₀ ht₀
  have hs : 0 ≤ s := ht₀.1.trans ht₀.2
  have hpos : ∀ r, r ≤ s → 0 < zigHeight η c s r := fun r hr => zigHeight_pos hη hc.le hr
  have hη0 := hpos 0 hs
  have hL : 0 ≤ Real.log (zigHeight η c s 0 / η) :=
    Real.log_nonneg ((one_le_div hη).2 (le_zigHeight hc.le hs))
  have hθ : 0 < θ := lt_of_le_of_lt (by positivity) hsmall₁
  have hLt : ∀ t ∈ Icc (0 : ℝ) s, Real.log (zigHeight η c s 0 / zigHeight η c s t) ≤
      Real.log (zigHeight η c s 0 / η) := fun t ht =>
    Real.log_le_log (div_pos hη0 (hpos t ht.2))
      (div_le_div_of_nonneg_left hη0.le hη (le_zigHeight hc.le ht.2))
  -- the bounds imply the strict threshold
  have hstrict_of : ∀ t ∈ Icc (0 : ℝ) s,
      ‖Xav t‖ ≤ 2 * K * (1 + Real.log (zigHeight η c s 0 / zigHeight η c s t)) /
        (N * zigHeight η c s t) →
      (∀ v, ‖Xv v t‖ ≤ 4 * K * w v / Real.sqrt (N * zigHeight η c s t * ρ)) →
      ZigThresholdStrict N η c s ρ θ w Xav Xv t := by
    intro t ht hav hv
    have hηt := hpos t ht.2
    refine ⟨hav.trans_lt (div_lt_div_of_pos_right ?_ (by positivity)), fun v =>
      (hv v).trans_lt (div_lt_div_of_pos_right ?_ (Real.sqrt_pos.mpr (by positivity)))⟩
    · have := hLt t ht
      nlinarith
    · have := hw v
      have h4 : 4 * K < θ := by nlinarith
      exact mul_lt_mul_of_pos_right h4 this
  -- the strict threshold holds at time `0`
  have hstrict0 : ZigThresholdStrict N η c s ρ θ w Xav Xv 0 := by
    refine ⟨?_, fun v => ?_⟩
    · rw [hXav0, norm_zero]
      positivity
    · rw [hXv0 v, norm_zero]
      have := hw v
      exact div_pos (mul_pos hθ this) (Real.sqrt_pos.mpr (by positivity))
  -- key step: strict before `T` and non-strict up to `T` give the bounds up to `T`
  have key : ∀ T ∈ Icc (0 : ℝ) s,
      (∀ r ∈ Ico 0 T, ZigThresholdStrict N η c s ρ θ w Xav Xv r) →
      (∀ r ∈ Icc 0 T, ZigThreshold N η c s ρ θ w Xav Xv r) →
      ∀ t ∈ Icc 0 T,
        ‖Xav t‖ ≤ 2 * K * (1 + Real.log (zigHeight η c s 0 / zigHeight η c s t)) /
          (N * zigHeight η c s t) ∧
        ∀ v, ‖Xv v t‖ ≤ 4 * K * w v / Real.sqrt (N * zigHeight η c s t * ρ) := by
    intro T hT hstr hthr t ht
    have hsub : Icc (0 : ℝ) T ⊆ Icc 0 s := Icc_subset_Icc_right hT.2
    have hsubu : uIcc (0 : ℝ) T ⊆ uIcc 0 s := by
      rw [uIcc_of_le hT.1, uIcc_of_le hs]
      exact hsub
    have hmart : ∀ u ∈ Icc (0 : ℝ) T, ∀ r ∈ Ico 0 u, ZigThresholdStrict N η c s ρ θ w Xav Xv r :=
      fun u hu r hr => hstr r ⟨hr.1, hr.2.trans_le hu.2⟩
    have hthrav : ∀ r ∈ Icc (0 : ℝ) T, ‖Xav r‖ ≤ θ / (N * zigHeight η c s r) :=
      fun r hr => (hthr r hr).1
    refine ⟨norm_averaged_le hN hη hc hθ.le hK hsmall₂ hT.2 (hXav.mono hsub)
      (hDav.mono_set hsubu) (fun u hu => hdecav u (hsub hu)) hthrav
      (fun r hr => hdriftav r (hsub hr) (hthr r hr))
      (fun u hu => hmartav u (hsub hu) (hmart u hu)) t ht, fun v => ?_⟩
    exact norm_vector_le hN hη hc hθ.le hK hρ (hw v).le hsmall₂ hsmall₃ hT.2
      ((hXv v).mono hsub) (hXav.mono hsub) ((hDv v).mono_set hsubu)
      (fun u hu => hdecv v u (hsub hu)) hthrav
      (fun r hr => hdriftv v r (hsub hr) (hthr r hr))
      (fun u hu => hmartv v u (hsub hu) (hmart u hu)) t ht
  -- continuity argument: the strict threshold holds on all of `[0, s]`
  have hall : ∀ t ∈ Icc (0 : ℝ) s, ZigThresholdStrict N η c s ρ θ w Xav Xv t := by
    by_contra hne
    push Not at hne
    obtain ⟨t₁, ht₁, hnot⟩ := hne
    set Fs := Icc (0 : ℝ) s ∩ {t | ¬ ZigThresholdStrict N η c s ρ θ w Xav Xv t} with hFs
    have hFcl : IsClosed Fs := isClosed_not_thresholdStrict hN hη hc.le hρ hXav hXv
    have hFne : Fs.Nonempty := ⟨t₁, ht₁, hnot⟩
    have hFbdd : BddBelow Fs := ⟨0, fun x hx => hx.1.1⟩
    have hτ : sInf Fs ∈ Fs := hFcl.csInf_mem hFne hFbdd
    set τ := sInf Fs with hτdef
    have hbelow : ∀ r ∈ Ico 0 τ, ZigThresholdStrict N η c s ρ θ w Xav Xv r := by
      intro r hr
      by_contra hnr
      have hmem : r ∈ Fs := ⟨⟨hr.1, hr.2.le.trans hτ.1.2⟩, hnr⟩
      have := csInf_le hFbdd hmem
      linarith [hr.2]
    have hτpos : 0 < τ := by
      rcases eq_or_lt_of_le hτ.1.1 with h | h
      · exact absurd (h ▸ hstrict0) hτ.2
      · exact h
    have hthrτ : ∀ r ∈ Icc 0 τ, ZigThreshold N η c s ρ θ w Xav Xv r := by
      have hsub : Ico 0 τ ⊆ Icc (0 : ℝ) s ∩ {t | ZigThreshold N η c s ρ θ w Xav Xv t} :=
        fun r hr => ⟨⟨hr.1, hr.2.le.trans hτ.1.2⟩, (hbelow r hr).le⟩
      have hcl := ((isClosed_threshold hN hη hc.le hρ hXav hXv).closure_subset_iff).2 hsub
      rw [closure_Ico hτpos.ne] at hcl
      exact fun r hr => (hcl hr).2
    have hb := key τ hτ.1 hbelow hthrτ τ ⟨hτpos.le, le_rfl⟩
    exact hτ.2 (hstrict_of τ hτ.1 hb.1 hb.2)
  have hb := key s ⟨hs, le_rfl⟩ (fun r hr => hall r ⟨hr.1, hr.2.le⟩)
    (fun r hr => (hall r hr).le) t₀ ht₀
  exact ⟨hall t₀ ht₀, hb.1, hb.2⟩

/-!
## Targets after the bootstrap
-/

/-- **Target, general form.** If `Y t = M_Y t + ∫_0^t D_Y` with `D_Y` integrable on `[0, s]`,
`‖D_Y r‖ ≤ ‖X_av r‖ Λ r / η_r` on `[0, t]` (`X_av`, `Λ` continuous on `[0, s]`) and
`‖M_Y t‖ ≤ K_Y`, then `‖Y t‖ ≤ K_Y + ∫_0^t ‖X_av‖ Λ / η`. -/
theorem norm_target_le {Y MY DY Xav : ℝ → ℂ} {Λ : ℝ → ℝ} {KY t : ℝ} (hη : 0 < η)
    (hc : 0 ≤ c) (ht : t ∈ Icc 0 s) (hXav : ContinuousOn Xav (Icc 0 s))
    (hΛ : ContinuousOn Λ (Icc 0 s)) (hD : IntervalIntegrable DY volume 0 s)
    (hdec : Y t = MY t + ∫ r in (0 : ℝ)..t, DY r)
    (hdrift : ∀ r ∈ Icc 0 t, ‖DY r‖ ≤ ‖Xav r‖ * Λ r / zigHeight η c s r)
    (hmart : ‖MY t‖ ≤ KY) :
    ‖Y t‖ ≤ KY + ∫ r in (0 : ℝ)..t, ‖Xav r‖ * Λ r / zigHeight η c s r := by
  have hg : IntervalIntegrable (fun r => ‖Xav r‖ * Λ r / zigHeight η c s r) volume 0 t :=
    (((hXav.norm.mul hΛ).div continuous_zigHeight.continuousOn fun r hr =>
      (zigHeight_pos hη hc hr.2).ne').mono (uIcc_subset_Icc_of_mem ht)).intervalIntegrable
  have h := norm_le_of_decomposition ht.1 (hD.mono_set (uIcc_subset_of_mem ht)) hg hdec hdrift
  linarith

/-- **Target, constant `Λ`, with the bootstrap bound plugged in.** Let `η, c, N > 0`, `K, Λ ≥ 0`,
`t ∈ [0, s]`. If `Y t = M_Y t + ∫_0^t D_Y` with `D_Y` integrable on `[0, s]`,
`‖X_av r‖ ≤ 2 K (1 + log (η_0 / η_r)) / (N η_r)` (the output of `zig_bootstrap`) and
`‖D_Y r‖ ≤ ‖X_av r‖ Λ / η_r` on `[0, t]`, and `‖M_Y t‖ ≤ K_Y`, then
`‖Y t‖ ≤ K_Y + 2 K Λ (1 + log (η_0 / η)) / (N c η)`. -/
theorem norm_target_le_const {Y MY DY Xav : ℝ → ℂ} {N K Λ KY t : ℝ} (hN : 0 < N)
    (hη : 0 < η) (hc : 0 < c) (hK : 0 ≤ K) (hΛ : 0 ≤ Λ) (ht : t ∈ Icc 0 s)
    (hD : IntervalIntegrable DY volume 0 s)
    (hdec : Y t = MY t + ∫ r in (0 : ℝ)..t, DY r)
    (hXav : ∀ r ∈ Icc 0 t, ‖Xav r‖ ≤
      2 * K * (1 + Real.log (zigHeight η c s 0 / zigHeight η c s r)) / (N * zigHeight η c s r))
    (hdrift : ∀ r ∈ Icc 0 t, ‖DY r‖ ≤ ‖Xav r‖ * Λ / zigHeight η c s r)
    (hmart : ‖MY t‖ ≤ KY) :
    ‖Y t‖ ≤ KY + 2 * K * Λ * (1 + Real.log (zigHeight η c s 0 / η)) / (N * c * η) := by
  have hts : t ≤ s := ht.2
  have hs : 0 ≤ s := ht.1.trans hts
  have hpos : ∀ r, r ≤ s → 0 < zigHeight η c s r := fun r hr => zigHeight_pos hη hc.le hr
  have hη0 := hpos 0 hs
  set L := Real.log (zigHeight η c s 0 / η) with hLdef
  have hL : 0 ≤ L := Real.log_nonneg ((one_le_div hη).2 (le_zigHeight hc.le hs))
  set β := 2 * K * Λ * (1 + L) / N with hβdef
  have hβ : 0 ≤ β := by positivity
  have hg : IntervalIntegrable (fun r => β / zigHeight η c s r ^ 2) volume 0 t :=
    ContinuousOn.intervalIntegrable (continuousOn_const.div
      (continuous_zigHeight.continuousOn.pow 2) fun r hr =>
        pow_ne_zero 2 (zigHeight_ne_zero_on hη hc.le hs hts r hr))
  have h := norm_le_of_decomposition ht.1 (hD.mono_set (uIcc_subset_of_mem ht)) hg hdec
    fun r hr => by
      have hrs : r ≤ s := hr.2.trans hts
      have hηr := hpos r hrs
      have hLr : Real.log (zigHeight η c s 0 / zigHeight η c s r) ≤ L :=
        Real.log_le_log (div_pos hη0 hηr)
          (div_le_div_of_nonneg_left hη0.le hη (le_zigHeight hc.le hrs))
      calc ‖DY r‖ ≤ ‖Xav r‖ * Λ / zigHeight η c s r := hdrift r hr
        _ ≤ 2 * K * (1 + Real.log (zigHeight η c s 0 / zigHeight η c s r)) /
            (N * zigHeight η c s r) * Λ / zigHeight η c s r := by
          gcongr
          exact hXav r hr
        _ ≤ 2 * K * (1 + L) / (N * zigHeight η c s r) * Λ / zigHeight η c s r := by
          gcongr
        _ = β / zigHeight η c s r ^ 2 := by
          simp only [hβdef]
          field_simp
  rw [integral_const_div_zigHeight_sq hη hc β hs hts] at h
  have h2 : β / c * (1 / zigHeight η c s t - 1 / zigHeight η c s 0) ≤ β / c * (1 / η) := by
    have : 0 < 1 / zigHeight η c s 0 := by positivity
    have : 1 / zigHeight η c s t ≤ 1 / η :=
      one_div_le_one_div_of_le hη (le_zigHeight hc.le hts)
    have : 0 ≤ β / c := div_nonneg hβ hc.le
    gcongr
    linarith
  have h3 : β / c * (1 / η) = 2 * K * Λ * (1 + L) / (N * c * η) := by
    simp only [hβdef]
    field_simp
  linarith

end BlockBand.Native.CEH.Zig
