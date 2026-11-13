module

public import BlockBand.Native.CEH.Zig.Bootstrap

/-!
# CEH ETH, two-resolvent zig: Grönwall with a rational coefficient

Grönwall and exact variation-of-constants bounds for linear equations with the rational
coefficient `a(r) = c / (1 - r c)`.

* `duhamel_of_integratingFactor`: the exact (complex) variation of constants. If
  `X t = E t + ∫_0^t b X` on `[0, T]` and `ψ' = -b ψ`, `ψ ≠ 0` on `[0, T]`, then
  `X t = E t + ∫_0^t b r E r (ψ r / ψ t) dr`.
* `duhamel_ratCoeff`: with `b = k a`, `ψ r = (1 - r c)^k`:
  `X t = E t + ∫_0^t k a(r) E(r) ((1 - r c) / (1 - t c))^k dr`. The Duhamel kernel is
  `((1 - r c) / (1 - t c))^k`, with the **earlier** time `r ≤ t` in the numerator.
* `exp_integral_ratCoeff`: `exp (∫_r^t a) = (1 - r c) / (1 - t c)` (complex exponential; no
  branch of the logarithm is needed). So the hypothesis `‖1 - r c‖ / ‖1 - t c‖ ≤ R` is exactly
  `‖exp ∫_r^t a‖ ≤ R`.
* `norm_le_of_duhamel_ratCoeff`: under the kernel bound `‖1 - r c‖ / ‖1 - t c‖ ≤ R`
  (`0 ≤ r ≤ t ≤ T`, a hypothesis), `‖X t‖ ≤ ‖E t‖ + R^k ∫_0^t k ‖a r‖ ‖E r‖ dr`.
* `norm_le_of_duhamel_ratCoeff_A` (`k = 1`, `R = 2`):
  `‖X t‖ ≤ ‖E t‖ + 2 ∫_0^t ‖a r‖ ‖E r‖ dr`;
  `norm_le_of_duhamel_ratCoeff_I` (coefficient `2 a`, `R = 2`, so `R^2 = 4`):
  `‖Y t‖ ≤ ‖E t‖ + 4 ∫_0^t ‖2 a r‖ ‖E r‖ dr`.
* `norm_le_of_duhamel_ratCoeff_const`: with `‖E r‖ ≤ G` on `[0, t]`,
  `‖X t‖ ≤ G (1 + R^k ∫_0^t k ‖a‖)`.

Scope of the ratio hypothesis `‖1 - r c‖ / ‖1 - t c‖ ≤ R` for `r ≤ t`:
* `norm_hybridDen_le_two_mul_mde`, proved in the sibling module of Ward-identity bounds, gives the
  reciprocal ratio,
  `|1 - σ c| ≤ 2 |1 - σ' c|` for `σ' ≤ σ`, i.e. a bound on `ψ t / ψ r`, the inverse of the kernel.
  It does not give `hratio`.
* In the adjoint (critical) constellations (`⟨R₁ A R₂*⟩`, `⟨R₁* A R₂⟩`, `c = ⟨M₁ M₂*⟩`) the kernel
  is of size about `(P_r / P_t)^{k/2}`, `P_r = η_{1,r} η_{2,r}`: CEH's factor
  `√(η_{1,s} η_{2,s} / (η_{1,t} η_{2,t}))` in the display after (7.6). It is not `O(1)` for `t`
  near the target time, so `R = 2` fails there.
* Hence the `R = 2` corollaries apply only where a bounded kernel ratio is separately known (for
  instance non-adjoint constellations in the bulk). The critical case uses the two-height modulus
  Grönwall `gronwall_twoHeight`, with the coefficient bound
  `‖a u‖ ≤ ½ (c₁ / η_{1,u} + c₂ / η_{2,u})` and factor `(P_r / P_t)^{k/2}`.

Why two forms. For complex `c` the modulus Grönwall only gives the factor `exp ∫_r^t |a|`, which
is not controlled by `|exp ∫_r^t a| = |1 - r c| / |1 - t c|` (e.g. `c ∈ iℝ`: the ratio is `≤ 1`
while `∫ |a| > 0`). The ratio enters through the exact Duhamel formula, where the remainder `E`
(martingale and nonlinear drift) is arbitrary. In the critical constellation `c` is close to a
positive real, so `|exp ∫ a| ≈ exp ∫ |a|` and Duhamel gives no gain over the modulus form.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Set MeasureTheory intervalIntegral
open BlockBand.Native.CEH.Phase1

/-- The rational linear coefficient `a(r) = c / (1 - r c)` (`= ⟨M^I_r⟩`). -/
def ratCoeff (c : ℂ) (r : ℝ) : ℂ := c / (1 - r * c)

theorem continuousOn_ratCoeff {c : ℂ} {S : Set ℝ} (hc : ∀ r ∈ S, 1 - (r : ℂ) * c ≠ 0) :
    ContinuousOn (ratCoeff c) S := by
  unfold ratCoeff
  exact continuousOn_const.div (by fun_prop) hc

theorem hasDerivAt_one_sub_mul (c : ℂ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => 1 - (r : ℂ) * c) (-c) r :=
  (((hasDerivAt_id r).ofReal_comp).mul_const c).const_sub 1 |>.congr_deriv (by simp)

/-!
## The modulus Grönwall
-/

/-- **Grönwall with a rational coefficient, modulus form.** Let `k ≥ 0`, `1 - r c ≠ 0` on
`[0, T]`, `x, F` continuous on `[0, T]`, and `x t ≤ F t + ∫_0^t k ‖a r‖ x r dr` on `[0, T]`,
`a = ratCoeff c`. Then on `[0, T]`
`x t ≤ F t + ∫_0^t F r (k ‖a r‖) exp (∫_r^t k ‖a‖) dr`. -/
theorem gronwall_ratCoeff {x F : ℝ → ℝ} {c : ℂ} {k T : ℝ} (hk : 0 ≤ k)
    (hc : ∀ r ∈ Icc 0 T, 1 - (r : ℂ) * c ≠ 0) (hx : ContinuousOn x (Icc 0 T))
    (hF : ContinuousOn F (Icc 0 T))
    (hle : ∀ t ∈ Icc 0 T, x t ≤ F t + ∫ r in (0 : ℝ)..t, k * ‖ratCoeff c r‖ * x r) :
    ∀ t ∈ Icc 0 T, x t ≤ F t + ∫ r in (0 : ℝ)..t,
      F r * (k * ‖ratCoeff c r‖) * Real.exp (∫ q in r..t, k * ‖ratCoeff c q‖) :=
  gronwall_integral hx (continuousOn_const.mul (continuousOn_ratCoeff hc).norm) hF
    (fun r _ => by positivity) hle

/-!
## Exact variation of constants
-/

private theorem exists_continuous_eqOn_Icc' {T : ℝ} (hT : 0 ≤ T) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc 0 T)) : ∃ g : ℝ → ℂ, Continuous g ∧ EqOn g f (Icc 0 T) :=
  ⟨fun r => f (projIcc 0 T hT r),
    hf.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun r => (projIcc 0 T hT r).2,
    fun r hr => by simp [projIcc_of_mem hT hr]⟩

private theorem integral_congr_Icc' {f g : ℝ → ℂ} {T t : ℝ} (ht : t ∈ Icc 0 T)
    (h : EqOn f g (Icc 0 T)) : ∫ r in (0 : ℝ)..t, f r = ∫ r in (0 : ℝ)..t, g r := by
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le ht.1] at hr
  exact h ⟨hr.1, hr.2.trans ht.2⟩

/-- The remainder `E = X - ∫_0 b X` is continuous on `[0, T]`. -/
theorem continuousOn_of_decomposition {X E b : ℝ → ℂ} {T : ℝ}
    (hX : ContinuousOn X (Icc 0 T)) (hb : ContinuousOn b (Icc 0 T))
    (hdec : ∀ t ∈ Icc 0 T, X t = E t + ∫ r in (0 : ℝ)..t, b r * X r) :
    ContinuousOn E (Icc 0 T) := by
  rcases lt_or_ge T 0 with hT | hT
  · rw [Icc_eq_empty (not_le.mpr hT)]
    exact continuousOn_empty _
  obtain ⟨g, hgc, hg⟩ := exists_continuous_eqOn_Icc' hT (hb.mul hX)
  have hI : Continuous fun t => ∫ r in (0 : ℝ)..t, g r :=
    continuous_iff_continuousAt.2 fun t =>
      ((hgc.integral_hasStrictDerivAt 0 t).hasDerivAt).continuousAt
  refine (hX.sub hI.continuousOn).congr fun t ht => ?_
  have h1 : ∫ r in (0 : ℝ)..t, b r * X r = ∫ r in (0 : ℝ)..t, g r :=
    (integral_congr_Icc' ht hg).symm
  simp only [Pi.sub_apply]
  rw [hdec t ht, h1]
  ring

/-- **Variation of constants with an integrating factor.** Let `X, b` be continuous on
`[0, T]`, `ψ` with `ψ' = -b ψ` and `ψ ≠ 0` at every point of `[0, T]`, and
`X t = E t + ∫_0^t b X` on `[0, T]`. Then on `[0, T]`
`X t = E t + ∫_0^t b r E r (ψ r / ψ t) dr`. -/
theorem duhamel_of_integratingFactor {X E b ψ : ℝ → ℂ} {T : ℝ}
    (hX : ContinuousOn X (Icc 0 T)) (hb : ContinuousOn b (Icc 0 T))
    (hψ : ∀ r ∈ Icc 0 T, HasDerivAt ψ (-(b r * ψ r)) r) (hψ0 : ∀ r ∈ Icc 0 T, ψ r ≠ 0)
    (hdec : ∀ t ∈ Icc 0 T, X t = E t + ∫ r in (0 : ℝ)..t, b r * X r) :
    ∀ t ∈ Icc 0 T, X t = E t + ∫ r in (0 : ℝ)..t, b r * E r * (ψ r / ψ t) := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc_right ht.2
  obtain ⟨g, hgc, hg⟩ := exists_continuous_eqOn_Icc' hT (hb.mul hX)
  have hE := continuousOn_of_decomposition hX hb hdec
  have hψc : ContinuousOn ψ (Icc 0 T) := fun r hr =>
    (hψ r hr).continuousAt.continuousWithinAt
  set Y : ℝ → ℂ := fun u => ∫ r in (0 : ℝ)..u, g r with hYdef
  have hY : ∀ u, HasDerivAt Y (g u) u := fun u =>
    (hgc.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hgI : ∀ u ∈ Icc 0 T, ∫ r in (0 : ℝ)..u, b r * X r = Y u := fun u hu =>
    (integral_congr_Icc' hu hg).symm
  have hYX : ∀ u ∈ Icc 0 T, X u = E u + Y u := fun u hu => by
    rw [hdec u hu, hgI u hu]
  have hderiv : ∀ r ∈ uIcc (0 : ℝ) t,
      HasDerivAt (fun u => Y u * ψ u) (b r * E r * ψ r) r := by
    intro r hr
    have hr' := hsub hr
    refine ((hY r).mul (hψ r hr')).congr_deriv ?_
    rw [hg hr', Pi.mul_apply, hYX r hr']
    ring
  have hint : IntervalIntegrable (fun r => b r * E r * ψ r) volume 0 t :=
    (((hb.mul hE).mul hψc).mono hsub).intervalIntegrable
  have h := integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [hYdef, intervalIntegral.integral_same, zero_mul, sub_zero] at h
  have hψt := hψ0 t ht
  rw [hdec t ht, hgI t ht]
  congr 1
  have e : ∫ r in (0 : ℝ)..t, b r * E r * (ψ r / ψ t) =
      (∫ r in (0 : ℝ)..t, b r * E r * ψ r) / ψ t := by
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun r _ => ?_
    ring
  rw [e, h, mul_div_cancel_right₀ _ hψt]

/-- **Variation of constants for `k a(r)`.** If `1 - r c ≠ 0` on `[0, T]`, `X` is continuous on
`[0, T]` and `X t = E t + ∫_0^t k a(r) X r dr` there (`a = ratCoeff c`, `k ∈ ℕ`), then on `[0, T]`
`X t = E t + ∫_0^t k a(r) E r ((1 - r c) / (1 - t c))^k dr`. -/
theorem duhamel_ratCoeff {X E : ℝ → ℂ} {c : ℂ} {T : ℝ} (k : ℕ)
    (hc : ∀ r ∈ Icc 0 T, 1 - (r : ℂ) * c ≠ 0) (hX : ContinuousOn X (Icc 0 T))
    (hdec : ∀ t ∈ Icc 0 T, X t = E t + ∫ r in (0 : ℝ)..t, (k : ℂ) * ratCoeff c r * X r) :
    ∀ t ∈ Icc 0 T, X t = E t + ∫ r in (0 : ℝ)..t,
      (k : ℂ) * ratCoeff c r * E r * ((1 - (r : ℂ) * c) / (1 - (t : ℂ) * c)) ^ k := by
  have hψ : ∀ r ∈ Icc 0 T, HasDerivAt (fun r : ℝ => (1 - (r : ℂ) * c) ^ k)
      (-((k : ℂ) * ratCoeff c r * (1 - (r : ℂ) * c) ^ k)) r := by
    intro r hr
    have h := (hasDerivAt_one_sub_mul c r).pow k
    refine h.congr_deriv ?_
    have hne := hc r hr
    unfold ratCoeff
    rcases k with _ | n
    · simp
    · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp
  intro t ht
  have h := duhamel_of_integratingFactor (b := fun r => (k : ℂ) * ratCoeff c r) hX
    (continuousOn_const.mul (continuousOn_ratCoeff hc)) hψ
    (fun r hr => pow_ne_zero k (hc r hr)) hdec t ht
  rw [h]
  congr 1
  refine intervalIntegral.integral_congr fun r _ => ?_
  simp only [div_pow]

/-- `exp (∫_r^t a) = (1 - r c) / (1 - t c)` (complex exponential) when `1 - q c ≠ 0` for
`q ∈ [r, t]` (in either order). -/
theorem exp_integral_ratCoeff {c : ℂ} {r t : ℝ} (hc : ∀ q ∈ uIcc r t, 1 - (q : ℂ) * c ≠ 0) :
    Complex.exp (∫ q in r..t, ratCoeff c q) = (1 - (r : ℂ) * c) / (1 - (t : ℂ) * c) := by
  set U : Set ℝ := {q | 1 - (q : ℂ) * c ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne_fun (by fun_prop) continuous_const
  have hUc : ContinuousOn (ratCoeff c) U := continuousOn_ratCoeff fun q hq => hq
  have hsub : uIcc r t ⊆ U := fun q hq => hc q hq
  have hI : ∀ u ∈ uIcc r t, HasDerivAt (fun v => ∫ q in r..v, ratCoeff c q) (ratCoeff c u) u := by
    intro u hu
    have hru : uIcc r u ⊆ uIcc r t := uIcc_subset_uIcc_left hu
    exact intervalIntegral.integral_hasDerivAt_right
      ((hUc.mono (hru.trans hsub)).intervalIntegrable)
      (hUc.stronglyMeasurableAtFilter hUo u (hsub hu))
      (hUc.continuousAt (hUo.mem_nhds (hsub hu)))
  have hderiv : ∀ u ∈ uIcc r t, HasDerivAt
      (fun v => Complex.exp (∫ q in r..v, ratCoeff c q) * (1 - (v : ℂ) * c)) 0 u := by
    intro u hu
    refine ((hI u hu).cexp.mul (hasDerivAt_one_sub_mul c u)).congr_deriv ?_
    have key : ratCoeff c u * (1 - (u : ℂ) * c) = c := div_mul_cancel₀ c (hc u hu)
    linear_combination Complex.exp (∫ q in r..u, ratCoeff c q) * key
  have h := integral_eq_sub_of_hasDerivAt hderiv intervalIntegrable_const
  simp only [intervalIntegral.integral_zero, intervalIntegral.integral_same, Complex.exp_zero,
    one_mul] at h
  have ht := hc t right_mem_uIcc
  rw [eq_div_iff ht]
  linear_combination -h

/-!
## Norm bounds under the ratio hypothesis
-/

/-- **Duhamel bound.** Let `1 - r c ≠ 0` on `[0, T]`, with the kernel bound (a hypothesis, not
supplied by `norm_hybridDen_le_two_mul_mde`; see the module header) `‖1 - r c‖ / ‖1 - t c‖ ≤ R` for `0 ≤ r ≤ t ≤ T`
(equivalently `‖exp ∫_r^t a‖ ≤ R`, `exp_integral_ratCoeff`), `X` continuous on `[0, T]` and
`X t = E t + ∫_0^t k a(r) X r dr` there. Then on `[0, T]`,
`‖X t‖ ≤ ‖E t‖ + R^k ∫_0^t k ‖a r‖ ‖E r‖ dr`. -/
theorem norm_le_of_duhamel_ratCoeff {X E : ℝ → ℂ} {c : ℂ} {T R : ℝ} (k : ℕ)
    (hc : ∀ r ∈ Icc 0 T, 1 - (r : ℂ) * c ≠ 0)
    (hratio : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖1 - (r : ℂ) * c‖ / ‖1 - (t : ℂ) * c‖ ≤ R)
    (hX : ContinuousOn X (Icc 0 T))
    (hdec : ∀ t ∈ Icc 0 T, X t = E t + ∫ r in (0 : ℝ)..t, (k : ℂ) * ratCoeff c r * X r) :
    ∀ t ∈ Icc 0 T, ‖X t‖ ≤ ‖E t‖ + R ^ k * ∫ r in (0 : ℝ)..t, k * ‖ratCoeff c r‖ * ‖E r‖ := by
  intro t ht
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc_right ht.2
  have ha := continuousOn_ratCoeff hc
  have hE := continuousOn_of_decomposition hX (continuousOn_const.mul ha) hdec
  rw [duhamel_ratCoeff k hc hX hdec t ht]
  refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
  have hψc : ContinuousOn (fun r : ℝ => ((1 - (r : ℂ) * c) / (1 - (t : ℂ) * c)) ^ k)
      (Icc 0 T) := by fun_prop
  refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on ht.1
    ((((continuousOn_const.mul ha).mul hE).mul hψc).mono hsub).intervalIntegrable.norm
    (((continuousOn_const.mul ((continuousOn_const.mul ha.norm).mul hE.norm)).mono
      hsub).intervalIntegrable) fun r hr => ?_
  have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
  have hq : ‖((1 - (r : ℂ) * c) / (1 - (t : ℂ) * c)) ^ k‖ ≤ R ^ k := by
    rw [norm_pow, norm_div]
    exact pow_le_pow_left₀ (by positivity) (hratio r t hr.1 hr.2 ht.2) k
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast]
  have : 0 ≤ (k : ℝ) * ‖ratCoeff c r‖ * ‖E r‖ := by positivity
  calc (k : ℝ) * ‖ratCoeff c r‖ * ‖E r‖ * ‖((1 - (r : ℂ) * c) / (1 - (t : ℂ) * c)) ^ k‖
      ≤ (k : ℝ) * ‖ratCoeff c r‖ * ‖E r‖ * R ^ k := mul_le_mul_of_nonneg_left hq this
    _ = R ^ k * ((k : ℝ) * ‖ratCoeff c r‖ * ‖E r‖) := by ring

/-- **Coefficient `a`, kernel bound `2` (`k = 1`).** Under the hypothesis
`‖1 - r c‖ / ‖1 - t c‖ ≤ 2` (`0 ≤ r ≤ t ≤ T`; earlier time on top, not supplied by
`norm_hybridDen_le_two_mul_mde`, and false near the target time in the adjoint
constellations, see the module header), if
`X t = E t + ∫_0^t a(r) X r dr` on `[0, T]` with `X` continuous, then
`‖X t‖ ≤ ‖E t‖ + 2 ∫_0^t ‖a r‖ ‖E r‖ dr`. -/
theorem norm_le_of_duhamel_ratCoeff_A {X E : ℝ → ℂ} {c : ℂ} {T : ℝ}
    (hc : ∀ r ∈ Icc 0 T, 1 - (r : ℂ) * c ≠ 0)
    (hratio : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖1 - (r : ℂ) * c‖ / ‖1 - (t : ℂ) * c‖ ≤ 2)
    (hX : ContinuousOn X (Icc 0 T))
    (hdec : ∀ t ∈ Icc 0 T, X t = E t + ∫ r in (0 : ℝ)..t, ratCoeff c r * X r) :
    ∀ t ∈ Icc 0 T, ‖X t‖ ≤ ‖E t‖ + 2 * ∫ r in (0 : ℝ)..t, ‖ratCoeff c r‖ * ‖E r‖ := by
  intro t ht
  have h := norm_le_of_duhamel_ratCoeff 1 hc hratio hX
    (fun u hu => by simpa using hdec u hu) t ht
  simpa using h

/-- **Coefficient `2 a`, kernel bound `2² = 4` (`k = 2`).** Under the hypothesis
`‖1 - r c‖ / ‖1 - t c‖ ≤ 2` (`0 ≤ r ≤ t ≤ T`; earlier time on top, not supplied by
`norm_hybridDen_le_two_mul_mde`, and false near the target time in the adjoint
constellations, see the module header), if
`Y t = E t + ∫_0^t 2 a(r) Y r dr` on `[0, T]` with `Y` continuous, then
`‖Y t‖ ≤ ‖E t‖ + 4 ∫_0^t ‖2 a r‖ ‖E r‖ dr`. -/
theorem norm_le_of_duhamel_ratCoeff_I {Y E : ℝ → ℂ} {c : ℂ} {T : ℝ}
    (hc : ∀ r ∈ Icc 0 T, 1 - (r : ℂ) * c ≠ 0)
    (hratio : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖1 - (r : ℂ) * c‖ / ‖1 - (t : ℂ) * c‖ ≤ 2)
    (hY : ContinuousOn Y (Icc 0 T))
    (hdec : ∀ t ∈ Icc 0 T, Y t = E t + ∫ r in (0 : ℝ)..t, 2 * ratCoeff c r * Y r) :
    ∀ t ∈ Icc 0 T, ‖Y t‖ ≤ ‖E t‖ + 4 * ∫ r in (0 : ℝ)..t, ‖2 * ratCoeff c r‖ * ‖E r‖ := by
  intro t ht
  have h := norm_le_of_duhamel_ratCoeff 2 hc hratio hY
    (fun u hu => by simpa using hdec u hu) t ht
  have e : ∀ r, ‖(2 : ℂ) * ratCoeff c r‖ = 2 * ‖ratCoeff c r‖ := fun r => by
    rw [norm_mul, Complex.norm_two]
  simp only [e]
  norm_num at h
  exact h

/-- **Constant remainder bound.** In the setting of `norm_le_of_duhamel_ratCoeff`, if moreover
`‖E r‖ ≤ G` for `r ∈ [0, t]`, then `‖X t‖ ≤ G (1 + R^k ∫_0^t k ‖a‖)`. -/
theorem norm_le_of_duhamel_ratCoeff_const {X E : ℝ → ℂ} {c : ℂ} {T R G : ℝ} (k : ℕ)
    (hR : 0 ≤ R) (hc : ∀ r ∈ Icc 0 T, 1 - (r : ℂ) * c ≠ 0)
    (hratio : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖1 - (r : ℂ) * c‖ / ‖1 - (t : ℂ) * c‖ ≤ R)
    (hX : ContinuousOn X (Icc 0 T))
    (hdec : ∀ t ∈ Icc 0 T, X t = E t + ∫ r in (0 : ℝ)..t, (k : ℂ) * ratCoeff c r * X r)
    {t : ℝ} (ht : t ∈ Icc 0 T) (hG : ∀ r ∈ Icc 0 t, ‖E r‖ ≤ G) :
    ‖X t‖ ≤ G * (1 + R ^ k * ∫ r in (0 : ℝ)..t, k * ‖ratCoeff c r‖) := by
  have h := norm_le_of_duhamel_ratCoeff k hc hratio hX hdec t ht
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc_right ht.2
  have ha := continuousOn_ratCoeff hc
  have hE := continuousOn_of_decomposition hX (continuousOn_const.mul ha) hdec
  have hI : ∫ r in (0 : ℝ)..t, k * ‖ratCoeff c r‖ * ‖E r‖ ≤
      ∫ r in (0 : ℝ)..t, G * (k * ‖ratCoeff c r‖) := by
    refine intervalIntegral.integral_mono_on ht.1
      ((((continuousOn_const.mul ha.norm).mul hE.norm).mono hsub).intervalIntegrable)
      (((continuousOn_const.mul (continuousOn_const.mul ha.norm)).mono
        hsub).intervalIntegrable) fun r hr => ?_
    have : 0 ≤ (k : ℝ) * ‖ratCoeff c r‖ := by positivity
    rw [mul_comm G]
    exact mul_le_mul_of_nonneg_left (hG r hr) this
  rw [intervalIntegral.integral_const_mul] at hI
  have hRk : 0 ≤ R ^ k := pow_nonneg hR k
  have := hG t ⟨ht.1, le_rfl⟩
  nlinarith [mul_le_mul_of_nonneg_left hI hRk]

end BlockBand.Native.CEH.ETH
