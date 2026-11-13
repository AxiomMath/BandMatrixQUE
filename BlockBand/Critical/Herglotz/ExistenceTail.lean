module

public import BlockBand.Critical.Herglotz.SmoothSharp

/-!
# Existence of `𝖢_r`, part 1: the regularized kernel and the tail-finite configurations

The canonical series is split as
`π⁻¹ Σ_j g_j g_j^*/(x_j - z) = π⁻¹ Σ_j kern(x_j, z) g_j g_j^* + π⁻¹ Σ_j oddTail(x_j) g_j g_j^*`,
with `oddTail(x) = (1 - χ_1(x))/x` (odd, continuous, `= 1/x` for `|x| ≥ 2`, `= 0` for `|x| ≤ 1`)
and `kern(x, z) = (x - z)⁻¹ - oddTail(x) = O(|z| / x²)`. The first sum converges absolutely
for every configuration with `∫ (1 + x²)⁻¹ (1 + Σ_k |g_k|²) dξ < ∞` (`IsTailFinite`), which holds
almost surely for the decorated sine process. This file is deterministic except for the last
section (intensity of non-compactly-supported tests, the tail-finite event and the escaped tail).

Law (last section): `Ξ` decorated sine (`IsDecoratedSineProcess`),
`γ = circularVectorLaw (Fin r)`, Lebesgue measure in the location.

* `tailWeight x = (1 + x²)⁻¹`, `tailWeightMass L = ∫ (1 - χ_L) tailWeight → 0` (`tendsto_tailWeightMass`).
* `oddTail`, `regC ε t = conj t / max(|t|², ε²)` (`= t⁻¹` for `|t| ≥ ε`, `regC 0 = inv`),
  `kernReg ε x z = regC ε (x - z) - oddTail x`, `kern = kernReg 0`.
* `norm_kernReg_le`: `|kernReg ε x z| ≤ kernBound R δ · tailWeight x` whenever `|z| ≤ R`,
  `0 ≤ ε ≤ 1` and either `x = z` or `|x - z| ≥ δ`; `norm_kern_le_of_far` (`|x| > 2R + 2`).
* `IsTailFinite`, `exists_window_null` (no atom at distance in `(0, δ)` from a fixed `z`),
  `integrable_of_le_tailWeight`, `ae_norm_kernReg_le`.
* `measurable_indicator_integral`: measurability of `ω ↦ 1_G(ω) ∫ f dΞ(ω)` for pointwise limits
  of continuous integrands dominated on `G`.
* `lintegral_ofReal_of_decoratedSine'` (intensity, continuous tests `≥ 0`, no support condition),
  `ae_isTailFinite`, `tendsto_measure_tailSum` (escaped tail `→ 0` in probability).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal ComplexConjugate

namespace BlockBand.Critical.Herglotz

open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)

variable {r : ℕ}

/-!
## The weight `(1 + x²)⁻¹` and the escaped tail mass
-/

/-- `tailWeight x = (1 + x²)⁻¹`. -/
def tailWeight (x : ℝ) : ℝ := (1 + x ^ 2)⁻¹

theorem tailWeight_pos (x : ℝ) : 0 < tailWeight x := by unfold tailWeight; positivity

theorem continuous_tailWeight : Continuous tailWeight := by
  unfold tailWeight
  exact (continuous_const.add (continuous_pow 2)).inv₀ fun x =>
    (by positivity : (0 : ℝ) < 1 + x ^ 2).ne'

theorem integrable_tailWeight : Integrable tailWeight := integrable_inv_one_add_sq

/-- `(x²)⁻¹ ≤ 2 (1 + x²)⁻¹` for `|x| ≥ 1`. -/
theorem inv_sq_le_two_mul_tailWeight {x : ℝ} (hx : 1 ≤ |x|) :
    (x ^ 2)⁻¹ ≤ 2 * tailWeight x := by
  have h1 : 1 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  unfold tailWeight
  rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `w₀(x)⁻¹ = 1 + x² ≤ 1 + B²` for `|x| ≤ B`. -/
theorem one_le_mul_tailWeight {x B : ℝ} (hx : |x| ≤ B) :
    1 ≤ (1 + B ^ 2) * tailWeight x := by
  have hB : 0 ≤ B := (abs_nonneg x).trans hx
  have hx2 : x ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  unfold tailWeight
  rw [← div_eq_mul_inv, one_le_div hpos]
  linarith

/-- The escaped tail mass `τ(L) = ∫ (1 - χ_L(x)) (1 + x²)⁻¹ dx`. -/
def tailWeightMass (L : ℝ) : ℝ := ∫ x, (1 - smoothCutoff L x) * tailWeight x

theorem one_sub_smoothCutoff_nonneg (L x : ℝ) : 0 ≤ 1 - smoothCutoff L x :=
  sub_nonneg.2 (smoothCutoff_le_one L x)

theorem one_sub_smoothCutoff_le_one (L x : ℝ) : 1 - smoothCutoff L x ≤ 1 := by
  linarith [smoothCutoff_nonneg L x]

theorem integrable_one_sub_smoothCutoff_mul_tailWeight (L : ℝ) :
    Integrable fun x => (1 - smoothCutoff L x) * tailWeight x :=
  integrable_tailWeight.mono' (((continuous_const.sub (continuous_smoothCutoff L)).mul
    continuous_tailWeight).aestronglyMeasurable) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (one_sub_smoothCutoff_nonneg L x)
        (tailWeight_pos x).le)]
      exact mul_le_of_le_one_left (tailWeight_pos x).le (one_sub_smoothCutoff_le_one L x))

theorem tailWeightMass_nonneg (L : ℝ) : 0 ≤ tailWeightMass L :=
  integral_nonneg fun x => mul_nonneg (one_sub_smoothCutoff_nonneg L x) (tailWeight_pos x).le

/-- `τ(L) → 0` as `L → ∞` (dominated convergence, dominated by `(1 + x²)⁻¹`). -/
theorem tendsto_tailWeightMass : Tendsto tailWeightMass atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (l := atTop)
    (F := fun L x => (1 - smoothCutoff L x) * tailWeight x) (f := fun _ => (0 : ℝ))
    tailWeight
    (Eventually.of_forall fun L => (integrable_one_sub_smoothCutoff_mul_tailWeight L).1)
    (Eventually.of_forall fun L => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (one_sub_smoothCutoff_nonneg L x)
        (tailWeight_pos x).le)]
      exact mul_le_of_le_one_left (tailWeight_pos x).le (one_sub_smoothCutoff_le_one L x))
    integrable_tailWeight
    (Eventually.of_forall fun x => by
      have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_smoothCutoff x)).mul_const
        (tailWeight x)
      simpa using this)
  show Tendsto (fun L => ∫ x, (1 - smoothCutoff L x) * tailWeight x) atTop (𝓝 0)
  simpa using h

/-!
## The odd tail `oddTail x = (1 - χ_1(x)) / x`
-/

/-- `oddTail x = (1 - χ_1(x)) x / max(x², 1)`; it equals `(1 - χ_1(x))/x` (the factor vanishes
for `|x| ≤ 1`). -/
def oddTail (x : ℝ) : ℝ := (1 - smoothCutoff 1 x) * (x / max (x ^ 2) 1)

theorem max_sq_one_pos (x : ℝ) : 0 < max (x ^ 2) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)

theorem continuous_oddTail : Continuous oddTail := by
  unfold oddTail
  exact (continuous_const.sub (continuous_smoothCutoff 1)).mul
    (continuous_id.div ((continuous_pow 2).max continuous_const) fun x => (max_sq_one_pos x).ne')

theorem oddTail_neg (x : ℝ) : oddTail (-x) = -oddTail x := by
  simp only [oddTail, smoothCutoff_neg, neg_sq, neg_div, mul_neg]

theorem oddTail_eq_zero {x : ℝ} (hx : |x| ≤ 1) : oddTail x = 0 := by
  simp [oddTail, smoothCutoff_eq_one hx]

theorem oddTail_eq_inv {x : ℝ} (hx : 2 ≤ |x|) : oddTail x = x⁻¹ := by
  have h0 : smoothCutoff 1 x = 0 := smoothCutoff_eq_zero (by norm_num; linarith)
  have hx1 : 1 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  have hxne : x ≠ 0 := by
    intro h; rw [h, abs_zero] at hx; norm_num at hx
  simp only [oddTail, h0, sub_zero, one_mul, max_eq_left hx1]
  field_simp

theorem abs_div_max_sq_one_le (x : ℝ) : |x / max (x ^ 2) 1| ≤ 1 := by
  rw [abs_div, abs_of_pos (max_sq_one_pos x), div_le_one (max_sq_one_pos x)]
  by_cases h : |x| ≤ 1
  · exact h.trans (le_max_right _ _)
  · replace h := not_le.1 h
    refine le_trans ?_ (le_max_left _ _)
    nlinarith [sq_abs x]

theorem abs_oddTail_le_one (x : ℝ) : |oddTail x| ≤ 1 := by
  unfold oddTail
  rw [abs_mul, abs_of_nonneg (one_sub_smoothCutoff_nonneg 1 x)]
  have h1 := one_sub_smoothCutoff_le_one 1 x
  have h2 := abs_div_max_sq_one_le x
  have h3 := abs_nonneg (x / max (x ^ 2) 1)
  nlinarith

theorem oddTail_sq_le (x : ℝ) : oddTail x ^ 2 ≤ 2 * tailWeight x := by
  by_cases h : |x| ≤ 1
  · rw [oddTail_eq_zero h]
    have := tailWeight_pos x
    norm_num; positivity
  · replace h := not_le.1 h
    have hx1 : 1 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
    have hxne : x ≠ 0 := by
      intro h'; rw [h', abs_zero] at h; norm_num at h
    have hle : oddTail x ^ 2 ≤ (x ^ 2)⁻¹ := by
      unfold oddTail
      rw [max_eq_left hx1, mul_pow]
      have hc : (1 - smoothCutoff 1 x) ^ 2 ≤ 1 := by
        have := one_sub_smoothCutoff_nonneg 1 x
        have := one_sub_smoothCutoff_le_one 1 x
        nlinarith
      have hq : (x / x ^ 2) ^ 2 = (x ^ 2)⁻¹ := by field_simp
      rw [hq]
      exact mul_le_of_le_one_left (by positivity) hc
    exact hle.trans (inv_sq_le_two_mul_tailWeight h.le)

/-!
## The regularized inverse and the kernel
-/

/-- `regC ε t = conj t / max(|t|², ε²)`: continuous for `ε > 0`, `= t⁻¹` for `|t| ≥ ε`, and
`regC ε 0 = 0 = 0⁻¹`. -/
def regC (ε : ℝ) (t : ℂ) : ℂ := conj t / ((max (‖t‖ ^ 2) (ε ^ 2) : ℝ) : ℂ)

theorem regC_eq_inv {ε : ℝ} (hε : 0 ≤ ε) {t : ℂ} (h : ε ≤ ‖t‖) : regC ε t = t⁻¹ := by
  have hm : max (‖t‖ ^ 2) (ε ^ 2) = ‖t‖ ^ 2 :=
    max_eq_left (pow_le_pow_left₀ hε h 2)
  rw [regC, hm, Complex.inv_def, div_eq_mul_inv, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem regC_zero_left (t : ℂ) : regC 0 t = t⁻¹ := regC_eq_inv le_rfl (norm_nonneg t)

theorem regC_zero_right (ε : ℝ) : regC ε 0 = 0 := by simp [regC]

theorem norm_regC_le (ε : ℝ) (t : ℂ) : ‖regC ε t‖ ≤ ‖t‖⁻¹ := by
  by_cases ht : t = 0
  · simp [ht, regC_zero_right]
  have hpos : 0 < ‖t‖ := norm_pos_iff.2 ht
  have hm : ‖t‖ ^ 2 ≤ max (‖t‖ ^ 2) (ε ^ 2) := le_max_left _ _
  have hmpos : 0 < max (‖t‖ ^ 2) (ε ^ 2) := lt_of_lt_of_le (by positivity) hm
  rw [regC, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hmpos, div_le_iff₀ hmpos]
  calc ‖t‖ = ‖t‖⁻¹ * ‖t‖ ^ 2 := by field_simp
    _ ≤ ‖t‖⁻¹ * max (‖t‖ ^ 2) (ε ^ 2) := by gcongr

theorem continuous_regC {ε : ℝ} (hε : 0 < ε) : Continuous (regC ε) := by
  unfold regC
  refine Complex.continuous_conj.div (Complex.continuous_ofReal.comp
    ((continuous_norm.pow 2).max continuous_const)) fun t => ?_
  have : 0 < max (‖t‖ ^ 2) (ε ^ 2) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  exact_mod_cast this.ne'

/-- `regC (1/(n+1)) t → t⁻¹` (eventually equal for `t ≠ 0`; constant `0` for `t = 0`). -/
theorem tendsto_regC (t : ℂ) :
    Tendsto (fun n : ℕ => regC (1 / ((n : ℝ) + 1)) t) atTop (𝓝 t⁻¹) := by
  by_cases ht : t = 0
  · subst ht; simp [regC_zero_right]
  have hpos : 0 < ‖t‖ := norm_pos_iff.2 ht
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hpos
  refine tendsto_const_nhds.congr' ((eventually_ge_atTop N).mono fun n hn => ?_)
  refine (regC_eq_inv (by positivity) ?_).symm
  refine le_trans ?_ hN.le
  gcongr

/-- `kernReg ε x z = regC ε (x - z) - oddTail x`. -/
def kernReg (ε x : ℝ) (z : ℂ) : ℂ := regC ε ((x : ℂ) - z) - (oddTail x : ℂ)

/-- `kern x z = (x - z)⁻¹ - oddTail x` (Lean's `0⁻¹ = 0` at `x = z`). -/
def kern (x : ℝ) (z : ℂ) : ℂ := ((x : ℂ) - z)⁻¹ - (oddTail x : ℂ)

theorem kernReg_zero (x : ℝ) (z : ℂ) : kernReg 0 x z = kern x z := by
  simp [kernReg, kern, regC_zero_left]

theorem continuous_kernReg {ε : ℝ} (hε : 0 < ε) (z : ℂ) : Continuous fun x => kernReg ε x z :=
  ((continuous_regC hε).comp (Complex.continuous_ofReal.sub continuous_const)).sub
    (Complex.continuous_ofReal.comp continuous_oddTail)

theorem tendsto_kernReg (x : ℝ) (z : ℂ) :
    Tendsto (fun n : ℕ => kernReg (1 / ((n : ℝ) + 1)) x z) atTop (𝓝 (kern x z)) :=
  (tendsto_regC _).sub tendsto_const_nhds

/-- `(π (x - z))⁻¹ = π⁻¹ (kern x z + oddTail x)`. -/
theorem inv_pi_mul_sub_eq (x : ℝ) (z : ℂ) :
    ((Real.pi : ℂ) * ((x : ℂ) - z))⁻¹ = (Real.pi : ℂ)⁻¹ * (kern x z + (oddTail x : ℂ)) := by
  rw [kern, sub_add_cancel, mul_inv]

/-- The kernel constant `(δ⁻¹ + 1)(1 + (2R + 2)²) + 4R`. -/
def kernBound (R δ : ℝ) : ℝ := (δ⁻¹ + 1) * (1 + (2 * R + 2) ^ 2) + 4 * R

/-- Far from the window: for `|z| ≤ R`, `|x| > 2R + 2` and `0 ≤ ε ≤ 1`,
`|kernReg ε x z| ≤ 4 R (1 + x²)⁻¹`. -/
theorem norm_kernReg_le_of_far {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {z : ℂ} {R : ℝ}
    (hR : ‖z‖ ≤ R) {x : ℝ} (hx : 2 * R + 2 < |x|) :
    ‖kernReg ε x z‖ ≤ 4 * R * tailWeight x := by
  have hR0 : 0 ≤ R := (norm_nonneg z).trans hR
  have hx2 : 2 ≤ |x| := by linarith
  have hxne : x ≠ 0 := by
    intro h; rw [h, abs_zero] at hx2; norm_num at hx2
  have hxpos : 0 < |x| := abs_pos.2 hxne
  have ht : |x| / 2 ≤ ‖(x : ℂ) - z‖ := by
    have h1 := norm_sub_norm_le (x : ℂ) z
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    linarith
  have htpos : 0 < ‖(x : ℂ) - z‖ := lt_of_lt_of_le (by positivity) ht
  have hreg : regC ε ((x : ℂ) - z) = ((x : ℂ) - z)⁻¹ :=
    regC_eq_inv hε0 (by linarith)
  have htne : (x : ℂ) - z ≠ 0 := norm_pos_iff.1 htpos
  have hxne' : (x : ℂ) ≠ 0 := by exact_mod_cast hxne
  have heq : kernReg ε x z = z / (((x : ℂ) - z) * x) := by
    rw [kernReg, hreg, oddTail_eq_inv hx2]
    push_cast
    field_simp
    ring
  rw [heq, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hden : |x| / 2 * |x| ≤ ‖(x : ℂ) - z‖ * |x| := by gcongr
  have hx2' : (|x| / 2 * |x|) = x ^ 2 / 2 := by rw [mul_comm, ← mul_div_assoc, ← sq, sq_abs]
  rw [hx2'] at hden
  have hsq : 0 < x ^ 2 / 2 := by positivity
  calc ‖z‖ / (‖(x : ℂ) - z‖ * |x|) ≤ R / (x ^ 2 / 2) :=
        div_le_div₀ hR0 hR hsq hden
    _ = 2 * R * (x ^ 2)⁻¹ := by field_simp
    _ ≤ 2 * R * (2 * tailWeight x) := by
        gcongr; exact inv_sq_le_two_mul_tailWeight (by linarith)
    _ = 4 * R * tailWeight x := by ring

/-- **Kernel bound.** For `|z| ≤ R`, `0 < δ`, `0 ≤ ε ≤ 1` and `x` with `x = z` or
`|x - z| ≥ δ`: `|kernReg ε x z| ≤ kernBound R δ · (1 + x²)⁻¹`. -/
theorem norm_kernReg_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {z : ℂ} {R δ : ℝ}
    (hR : ‖z‖ ≤ R) (hδ : 0 < δ) {x : ℝ} (hx : (x : ℂ) = z ∨ δ ≤ ‖(x : ℂ) - z‖) :
    ‖kernReg ε x z‖ ≤ kernBound R δ * tailWeight x := by
  have hR0 : 0 ≤ R := (norm_nonneg z).trans hR
  have hw := tailWeight_pos x
  have hA : 0 ≤ (δ⁻¹ + 1) * (1 + (2 * R + 2) ^ 2) := by positivity
  by_cases hbig : 2 * R + 2 < |x|
  · refine (norm_kernReg_le_of_far hε0 hε1 hR hbig).trans ?_
    unfold kernBound
    nlinarith
  replace hbig := not_lt.1 hbig
  have hreg : ‖regC ε ((x : ℂ) - z)‖ ≤ δ⁻¹ := by
    rcases hx with hx | hx
    · rw [hx, sub_self, regC_zero_right, norm_zero]; positivity
    · exact (norm_regC_le ε _).trans (inv_anti₀ hδ hx)
  have hk : ‖kernReg ε x z‖ ≤ δ⁻¹ + 1 := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith [abs_oddTail_le_one x]
  have h1 := one_le_mul_tailWeight hbig
  unfold kernBound
  have hd : 0 ≤ δ⁻¹ + 1 := by positivity
  calc ‖kernReg ε x z‖ ≤ (δ⁻¹ + 1) * 1 := by rw [mul_one]; exact hk
    _ ≤ (δ⁻¹ + 1) * ((1 + (2 * R + 2) ^ 2) * tailWeight x) := by gcongr
    _ ≤ ((δ⁻¹ + 1) * (1 + (2 * R + 2) ^ 2) + 4 * R) * tailWeight x := by nlinarith

theorem norm_kern_le_of_far {z : ℂ} {R : ℝ} (hR : ‖z‖ ≤ R) {x : ℝ} (hx : 2 * R + 2 < |x|) :
    ‖kern x z‖ ≤ 4 * R * tailWeight x := by
  rw [← kernReg_zero]; exact norm_kernReg_le_of_far le_rfl zero_le_one hR hx

/-- The entry mark `g_i conj(g_j)`. -/
def entryMark (i j : Fin r) (g : Fin r → ℂ) : ℂ := g i * conj (g j)

theorem continuous_entryMark (i j : Fin r) : Continuous (entryMark (r := r) i j) := by
  unfold entryMark; fun_prop

theorem norm_entryMark_le (i j : Fin r) (g : Fin r → ℂ) : ‖entryMark i j g‖ ≤ euclidMark g := by
  rw [entryMark, norm_mul, Complex.norm_conj]; exact norm_mul_norm_le_euclidMark g i j

/-!
## Tail-finite configurations
-/

/-- `ξ` is tail-finite: `∫ (1 + x²)⁻¹ (1 + Σ_k |g_k|²) dξ(x, g) < ∞`. -/
def IsTailFinite (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))) : Prop :=
  ∫⁻ p, ENNReal.ofReal (tailWeight p.1 * (1 + euclidMark p.2)) ∂ξ.measure < ∞

theorem continuous_tailIntegrand :
    Continuous fun p : ℝ × (Fin r → ℂ) => tailWeight p.1 * (1 + euclidMark p.2) :=
  (continuous_tailWeight.comp continuous_fst).mul
    (continuous_const.add (continuous_euclidMark.comp continuous_snd))

theorem measurable_tailIntegrand :
    Measurable fun p : ℝ × (Fin r → ℂ) => tailWeight p.1 * (1 + euclidMark p.2) :=
  continuous_tailIntegrand.measurable

theorem tailIntegrand_nonneg (p : ℝ × (Fin r → ℂ)) : 0 ≤ tailWeight p.1 * (1 + euclidMark p.2) :=
  mul_nonneg (tailWeight_pos _).le (by linarith [euclidMark_nonneg p.2])

theorem IsTailFinite.integrable {ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))} (hξ : IsTailFinite ξ) :
    Integrable (fun p : ℝ × (Fin r → ℂ) => tailWeight p.1 * (1 + euclidMark p.2)) ξ.measure :=
  ⟨measurable_tailIntegrand.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall tailIntegrand_nonneg)).2 hξ⟩

/-- Domination by `c (1 + x²)⁻¹ (1 + Σ|g_k|²)` gives integrability on a tail-finite `ξ`. -/
theorem integrable_of_le_tailWeight {ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))}
    (hξ : IsTailFinite ξ) {f : ℝ × (Fin r → ℂ) → ℂ} (hf : AEStronglyMeasurable f ξ.measure)
    {c : ℝ} (hb : ∀ᵐ p ∂ξ.measure, ‖f p‖ ≤ c * (tailWeight p.1 * (1 + euclidMark p.2))) :
    Integrable f ξ.measure :=
  (hξ.integrable.const_mul c).mono' hf hb

/-- **No atom at distance in `(0, δ)` from `z`.** For a tail-finite `ξ` and any `z ∈ ℂ` there is
`0 < δ ≤ 1` with `ξ{p : 0 < |p.1 - z| < δ} = 0` (continuity from above and integer values). -/
theorem exists_window_null {ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))} (hξ : IsTailFinite ξ)
    (z : ℂ) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ξ.measure {p : ℝ × (Fin r → ℂ) | 0 < ‖(p.1 : ℂ) - z‖ ∧ ‖(p.1 : ℂ) - z‖ < δ} = 0 := by
  set A : ℕ → Set (ℝ × (Fin r → ℂ)) := fun n =>
    {p | 0 < ‖(p.1 : ℂ) - z‖ ∧ ‖(p.1 : ℂ) - z‖ < 1 / ((n : ℝ) + 1)} with hA
  have hcont : Continuous fun p : ℝ × (Fin r → ℂ) => ‖(p.1 : ℂ) - z‖ :=
    (Complex.continuous_ofReal.comp continuous_fst).sub continuous_const |>.norm
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    (measurableSet_lt measurable_const hcont.measurable).inter
      (measurableSet_lt hcont.measurable measurable_const)
  have hanti : Antitone A := by
    intro n m hnm p hp
    refine ⟨hp.1, hp.2.trans_le ?_⟩
    gcongr
  have hinter : (⋂ n, A n) = ∅ := by
    ext p
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    by_contra hcon'
    have hcon : ∀ n, p ∈ A n := fun n => by
      by_contra hn; exact hcon' ⟨n, hn⟩
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (hcon 0).1
    exact lt_irrefl _ (((hcon N).2).trans hN)
  -- finiteness of `ξ(A 0)`
  set c : ℝ := (1 + (‖z‖ + 1) ^ 2)⁻¹ with hc
  have hc0 : 0 < c := by positivity
  have hle : ∀ p, (A 0).indicator (fun _ => ENNReal.ofReal c) p ≤
      ENNReal.ofReal (tailWeight p.1 * (1 + euclidMark p.2)) := by
    intro p
    by_cases hp : p ∈ A 0
    · rw [indicator_of_mem hp]
      refine ENNReal.ofReal_le_ofReal ?_
      have hp1 : |p.1| ≤ ‖z‖ + 1 := by
        have h1 := norm_sub_norm_le (p.1 : ℂ) z
        rw [Complex.norm_real, Real.norm_eq_abs] at h1
        have : ‖(p.1 : ℂ) - z‖ < 1 := by simpa using hp.2
        linarith
      have h2 := one_le_mul_tailWeight hp1
      have h3 : c ≤ tailWeight p.1 := by
        rw [hc, inv_le_iff_one_le_mul₀ (by positivity), mul_comm]; exact h2
      nlinarith [euclidMark_nonneg p.2, tailWeight_pos p.1]
    · rw [indicator_of_notMem hp]; exact zero_le
  have hA0 : ξ.measure (A 0) ≠ ∞ := by
    intro htop
    have h := lintegral_mono (μ := ξ.measure) hle
    rw [lintegral_indicator_const (hAm 0), htop, ENNReal.mul_top (by simpa using hc0)] at h
    exact absurd (lt_of_le_of_lt h hξ) (lt_irrefl _)
  have ht := tendsto_measure_iInter_atTop (μ := ξ.measure) (fun n => (hAm n).nullMeasurableSet)
    hanti ⟨0, hA0⟩
  rw [hinter, measure_empty] at ht
  obtain ⟨n, hn⟩ := ((tendsto_order.1 ht).2 1 one_pos).exists
  have h0 : ξ.measure (A n) = 0 := by
    rcases ξ.integer_valued (A n) (hAm n) with h | ⟨m, hm⟩
    · simp only [Function.comp_apply] at hn; rw [h] at hn; exact absurd hn (by simp)
    · simp only [Function.comp_apply] at hn
      rw [hm] at hn ⊢
      have : m < 1 := by exact_mod_cast hn
      have : m = 0 := by omega
      simp [this]
  refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_, h0⟩
  rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- On a tail-finite `ξ`, for every `z` there is `δ > 0` such that `ξ`-a.e.
`|kernReg ε x z| ≤ kernBound |z| δ · (1 + x²)⁻¹`, uniformly in `0 ≤ ε ≤ 1`. -/
theorem ae_norm_kernReg_le {ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))} (hξ : IsTailFinite ξ)
    (z : ℂ) : ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ᵐ p ∂ξ.measure, ‖kernReg ε p.1 z‖ ≤ kernBound ‖z‖ δ * tailWeight p.1 := by
  obtain ⟨δ, hδ, -, h0⟩ := exists_window_null hξ z
  refine ⟨δ, hδ, fun ε hε0 hε1 => ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with p hp
  refine norm_kernReg_le hε0 hε1 le_rfl hδ ?_
  simp only [not_and_or, not_lt] at hp
  rcases hp with hp | hp
  · left
    have : ‖(p.1 : ℂ) - z‖ = 0 := le_antisymm hp (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  · right; exact hp

/-!
## Measurability of integrals against `Ξ`
-/

/-- The location-and-mark cutoff `χ_n(x) ψ_n(g)`. -/
def boxCutoff (n : ℕ) (p : ℝ × (Fin r → ℂ)) : ℝ := smoothCutoff n p.1 * markCutoff n p.2

theorem continuous_boxCutoff (n : ℕ) : Continuous (boxCutoff (r := r) n) :=
  ((continuous_smoothCutoff _).comp continuous_fst).mul ((continuous_markCutoff n).comp
    continuous_snd)

theorem hasCompactSupport_boxCutoff (n : ℕ) : HasCompactSupport (boxCutoff (r := r) n) := by
  refine HasCompactSupport.intro ((isCompact_closedBall (0 : ℝ) ((n : ℝ) + 1)).prod
    (isCompact_closedBall (0 : Fin r → ℂ) ((n : ℝ) + 1))) fun p hp => ?_
  simp only [mem_prod, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_and_or,
    not_le] at hp
  unfold boxCutoff
  rcases hp with hp | hp
  · rw [smoothCutoff_eq_zero hp.le, zero_mul]
  · rw [markCutoff_eq_zero hp.le, mul_zero]

theorem abs_boxCutoff_le_one (n : ℕ) (p : ℝ × (Fin r → ℂ)) : |boxCutoff n p| ≤ 1 := by
  unfold boxCutoff
  rw [abs_mul, abs_of_nonneg (smoothCutoff_nonneg _ _), abs_of_nonneg (markCutoff_nonneg _ _)]
  have h1 := smoothCutoff_le_one (n : ℝ) p.1
  have h2 := markCutoff_nonneg n p.2
  have h3 := markCutoff_le_one n p.2
  have h4 := smoothCutoff_nonneg (n : ℝ) p.1
  nlinarith

theorem tendsto_boxCutoff (p : ℝ × (Fin r → ℂ)) :
    Tendsto (fun n : ℕ => boxCutoff n p) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max |p.1| ‖p.2‖)
  refine tendsto_const_nhds.congr' ((eventually_ge_atTop N).mono fun n hn => ?_)
  have hn' : max |p.1| ‖p.2‖ ≤ n := hN.trans (by exact_mod_cast hn)
  simp only [boxCutoff]
  rw [smoothCutoff_eq_one ((le_max_left _ _).trans hn'),
    markCutoff_eq_one ((le_max_right _ _).trans hn'), mul_one]

/-- `ω ↦ ∫ H dΞ(ω)` is measurable for continuous compactly supported `H : ℝ × ℂ^r → ℂ`. -/
theorem measurable_integral_of_hasCompactSupport {Ω : Type*} [MeasurableSpace Ω]
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (hΞ : Measurable Ξ)
    {H : ℝ × (Fin r → ℂ) → ℂ} (hH : Continuous H) (hHc : HasCompactSupport H) :
    Measurable fun ω => ∫ p, H p ∂(Ξ ω).measure := by
  set fre : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ :=
    ⟨⟨fun p => (H p).re, Complex.continuous_re.comp hH⟩,
      hHc.comp_left (g := Complex.re) Complex.zero_re⟩
  set fim : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ :=
    ⟨⟨fun p => (H p).im, Complex.continuous_im.comp hH⟩,
      hHc.comp_left (g := Complex.im) Complex.zero_im⟩
  have hre : Measurable fun ω => (Ξ ω).coordinate fre :=
    (BlockBand.Model.Construction.continuous_vaguePointMeasure_coordinate fre).measurable.comp hΞ
  have him : Measurable fun ω => (Ξ ω).coordinate fim :=
    (BlockBand.Model.Construction.continuous_vaguePointMeasure_coordinate fim).measurable.comp hΞ
  have heq : (fun ω => ∫ p, H p ∂(Ξ ω).measure) =
      fun ω => (((Ξ ω).coordinate fre : ℝ) : ℂ) + (((Ξ ω).coordinate fim : ℝ) : ℂ) * Complex.I := by
    funext ω
    rw [← integral_re_add_im (hH.integrable_of_hasCompactSupport hHc)]
    rfl
  rw [heq]
  exact (Complex.measurable_ofReal.comp hre).add
    ((Complex.measurable_ofReal.comp him).mul measurable_const)

/-- **Measurability of `1_G(ω) ∫ f dΞ(ω)`.** If `f` is the pointwise limit of continuous `F n`
and, for every `ω ∈ G`, the `F n` are `Ξ(ω)`-a.e. dominated by one `Ξ(ω)`-integrable function,
then `ω ↦ 1_G(ω) ∫ f dΞ(ω)` is measurable (`G` measurable, `Ξ` measurable). -/
theorem measurable_indicator_integral {Ω : Type*} [MeasurableSpace Ω]
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (hΞ : Measurable Ξ) {G : Set Ω}
    (hG : MeasurableSet G) {F : ℕ → ℝ × (Fin r → ℂ) → ℂ} (hF : ∀ n, Continuous (F n))
    {f : ℝ × (Fin r → ℂ) → ℂ} (hlim : ∀ p, Tendsto (fun n => F n p) atTop (𝓝 (f p)))
    (hdom : ∀ ω ∈ G, ∃ b : ℝ × (Fin r → ℂ) → ℝ, Integrable b (Ξ ω).measure ∧
      ∀ n, ∀ᵐ p ∂(Ξ ω).measure, ‖F n p‖ ≤ b p) :
    Measurable (G.indicator fun ω => ∫ p, f p ∂(Ξ ω).measure) := by
  set H : ℕ → ℝ × (Fin r → ℂ) → ℂ := fun n p => ((boxCutoff n p : ℝ) : ℂ) * F n p with hH
  have hHc (n : ℕ) : Continuous (H n) :=
    (Complex.continuous_ofReal.comp (continuous_boxCutoff n)).mul (hF n)
  have hHs (n : ℕ) : HasCompactSupport (H n) :=
    ((hasCompactSupport_boxCutoff n).comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero).mul_right
  have hHm (n : ℕ) : Measurable (G.indicator fun ω => ∫ p, H n p ∂(Ξ ω).measure) :=
    (measurable_integral_of_hasCompactSupport hΞ (hHc n) (hHs n)).indicator hG
  refine measurable_of_tendsto_metrizable hHm (tendsto_pi_nhds.2 fun ω => ?_)
  by_cases hω : ω ∈ G
  · simp only [indicator_of_mem hω]
    obtain ⟨b, hb, hbF⟩ := hdom ω hω
    refine tendsto_integral_of_dominated_convergence b (fun n => (hHc n).aestronglyMeasurable) hb
      (fun n => (hbF n).mono fun p hp => ?_) (Eventually.of_forall fun p => ?_)
    · rw [hH, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg _) (abs_boxCutoff_le_one n p)).trans hp
    · have := ((Complex.continuous_ofReal.tendsto 1).comp (tendsto_boxCutoff p)).mul (hlim p)
      simpa using this
  · simp only [indicator_of_notMem hω]
    exact tendsto_const_nhds

/-!
## Intensity for continuous tests without support condition
-/

/-- **Intensity for continuous nonnegative tests** (the compactly supported intensity extended by
monotone convergence in the location cutoff `χ_n`). Law: `Ξ` decorated sine
(`IsDecoratedSineProcess`), `γ = circularVectorLaw (Fin r)`. For continuous `f ≥ 0` on
`ℝ × ℂ^r`: `ω ↦ ∫⁻ ofReal f dΞ(ω)` is measurable and
`E ∫⁻ ofReal f dΞ = ∫⁻ x, ∫⁻ g, ofReal f(x, g) dγ dx`. -/
theorem lintegral_ofReal_of_decoratedSine' {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))}
    (h : IsDecoratedSineProcess r P Ξ) {f : ℝ × (Fin r → ℂ) → ℝ} (hf : Continuous f)
    (hf0 : ∀ p, 0 ≤ f p) :
    Measurable (fun ω => ∫⁻ p, ENNReal.ofReal (f p) ∂(Ξ ω).measure) ∧
      ∫⁻ ω, ∫⁻ p, ENNReal.ofReal (f p) ∂(Ξ ω).measure ∂P =
        ∫⁻ x, ∫⁻ g, ENNReal.ofReal (f (x, g)) ∂circularVectorLaw (Fin r) := by
  set γ := circularVectorLaw (Fin r) with hγ
  set fn : ℕ → ℝ × (Fin r → ℂ) → ℝ := fun n p => smoothCutoff n p.1 * f p with hfn
  have hfnc (n : ℕ) : Continuous (fn n) :=
    ((continuous_smoothCutoff _).comp continuous_fst).mul hf
  have hfn0 (n : ℕ) (p : ℝ × (Fin r → ℂ)) : 0 ≤ fn n p :=
    mul_nonneg (smoothCutoff_nonneg _ _) (hf0 p)
  have hfnS (n : ℕ) (x : ℝ) (g : Fin r → ℂ) (hx : x ∉ Metric.closedBall (0 : ℝ) ((n : ℝ) + 1)) :
      fn n (x, g) = 0 := by
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
    simp [hfn, smoothCutoff_eq_zero hx.le]
  have hC (n : ℕ) := lintegral_lintegral_ofReal_of_decoratedSine h (hfnc n) (hfn0 n)
    (isCompact_closedBall _ _) (hfnS n)
  have hmono (p : ℝ × (Fin r → ℂ)) : Monotone fun n : ℕ => ENNReal.ofReal (fn n p) :=
    fun n m hnm => ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (smoothCutoff_mono (by exact_mod_cast hnm) _) (hf0 p))
  have hsup (p : ℝ × (Fin r → ℂ)) : ENNReal.ofReal (f p) = ⨆ n : ℕ, ENNReal.ofReal (fn n p) := by
    refine le_antisymm ?_ (iSup_le fun n => ENNReal.ofReal_le_ofReal
      (mul_le_of_le_one_left (hf0 p) (smoothCutoff_le_one _ _)))
    obtain ⟨N, hN⟩ := exists_nat_ge |p.1|
    refine le_iSup_of_le N (le_of_eq ?_)
    simp [hfn, smoothCutoff_eq_one hN]
  have hfnm (n : ℕ) : Measurable fun p => ENNReal.ofReal (fn n p) :=
    ENNReal.measurable_ofReal.comp (hfnc n).measurable
  have hpath (μ : Measure (ℝ × (Fin r → ℂ))) :
      ∫⁻ p, ENNReal.ofReal (f p) ∂μ = ⨆ n : ℕ, ∫⁻ p, ENNReal.ofReal (fn n p) ∂μ := by
    simp_rw [hsup]
    exact lintegral_iSup hfnm fun n m hnm p => hmono p hnm
  have hpathΩ : (fun ω => ∫⁻ p, ENNReal.ofReal (f p) ∂(Ξ ω).measure) =
      fun ω => ⨆ n : ℕ, ∫⁻ p, ENNReal.ofReal (fn n p) ∂(Ξ ω).measure :=
    funext fun ω => hpath _
  refine ⟨?_, ?_⟩
  · rw [hpathΩ]; exact Measurable.iSup fun n => (hC n).1
  · rw [hpathΩ, lintegral_iSup (fun n => (hC n).1) (fun n m hnm ω =>
      lintegral_mono fun p => hmono p hnm)]
    simp_rw [fun n => (hC n).2]
    have hin (x : ℝ) : ∫⁻ g, ENNReal.ofReal (f (x, g)) ∂γ =
        ⨆ n : ℕ, ∫⁻ g, ENNReal.ofReal (fn n (x, g)) ∂γ := by
      simp_rw [fun g => hsup (x, g)]
      exact lintegral_iSup (fun n => (hfnm n).comp measurable_prodMk_left)
        fun n m hnm g => hmono (x, g) hnm
    simp_rw [hin]
    refine (lintegral_iSup (fun n => (hfnm n).lintegral_prod_right') fun n m hnm x =>
      lintegral_mono fun g => hmono (x, g) hnm).symm

/-- `∫⁻ x, ∫⁻ g, ofReal(a(x) b(g)) dγ dx = (∫⁻ ofReal a) (∫⁻ ofReal b dγ)` for `a ≥ 0`. -/
theorem lintegral_lintegral_ofReal_mul {a : ℝ → ℝ} (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    (b : (Fin r → ℂ) → ℝ) :
    ∫⁻ x, ∫⁻ g, ENNReal.ofReal (a x * b g) ∂circularVectorLaw (Fin r) =
      (∫⁻ x, ENNReal.ofReal (a x)) * ∫⁻ g, ENNReal.ofReal (b g) ∂circularVectorLaw (Fin r) := by
  simp_rw [fun x g => ENNReal.ofReal_mul (q := b g) (ha0 x)]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mul_const _ (ENNReal.measurable_ofReal.comp ha)

theorem lintegral_ofReal_euclidMark :
    ∫⁻ g, ENNReal.ofReal (euclidMark g) ∂circularVectorLaw (Fin r) = ENNReal.ofReal r := by
  rw [← integral_euclidMark (r := r)]
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_of_integrable_sq continuous_euclidMark
    integrable_euclidMark_sq) (Eventually.of_forall euclidMark_nonneg)).symm

/-- The tail-finite event is measurable (law: `IsDecoratedSineProcess`). -/
theorem measurableSet_isTailFinite {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ) :
    MeasurableSet {ω | IsTailFinite (Ξ ω)} :=
  measurableSet_lt (lintegral_ofReal_of_decoratedSine' h continuous_tailIntegrand
    tailIntegrand_nonneg).1 measurable_const

/-- **The decorated sine process is almost surely tail-finite.** Law:
`IsDecoratedSineProcess`; `E ∫ (1 + x²)⁻¹ (1 + Σ_k |g_k|²) dΞ = π (1 + r) < ∞`. -/
theorem ae_isTailFinite {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ) :
    ∀ᵐ ω ∂P, IsTailFinite (Ξ ω) := by
  obtain ⟨hm, hE⟩ := lintegral_ofReal_of_decoratedSine' h continuous_tailIntegrand
    tailIntegrand_nonneg
  refine ae_lt_top hm ?_
  rw [hE]
  dsimp only
  rw [lintegral_lintegral_ofReal_mul continuous_tailWeight.measurable
    (fun x => (tailWeight_pos x).le)]
  refine ENNReal.mul_ne_top (integrable_tailWeight.lintegral_lt_top).ne ?_
  exact ((integrable_const (1 : ℝ)).add (integrable_of_integrable_sq continuous_euclidMark
    integrable_euclidMark_sq)).lintegral_lt_top.ne

/-- The escaped tail `T_L(ω) = ∫ (1 - χ_L(x)) (1 + x²)⁻¹ Σ_k |g_k|² dΞ(ω)` (in `ℝ≥0∞`). -/
def tailSum (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))) (L : ℝ) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal ((1 - smoothCutoff L p.1) * tailWeight p.1 * euclidMark p.2) ∂ξ.measure

theorem continuous_tailSumIntegrand (L : ℝ) : Continuous fun p : ℝ × (Fin r → ℂ) =>
    (1 - smoothCutoff L p.1) * tailWeight p.1 * euclidMark p.2 :=
  (((continuous_const.sub (continuous_smoothCutoff L)).comp continuous_fst).mul
    (continuous_tailWeight.comp continuous_fst)).mul (continuous_euclidMark.comp continuous_snd)

theorem tailSumIntegrand_nonneg (L : ℝ) (p : ℝ × (Fin r → ℂ)) :
    0 ≤ (1 - smoothCutoff L p.1) * tailWeight p.1 * euclidMark p.2 :=
  mul_nonneg (mul_nonneg (one_sub_smoothCutoff_nonneg L _) (tailWeight_pos _).le)
    (euclidMark_nonneg _)

/-- **The escaped tail vanishes in probability.** Law: `IsDecoratedSineProcess`. For every
`ε > 0` (in `ℝ≥0∞`, finite), `P(ε ≤ T_L) ≤ r τ(L) / ε → 0` as `L → ∞` (Markov,
`E T_L = r τ(L)`). -/
theorem tendsto_measure_tailSum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) (hε' : ε ≠ ∞) :
    Tendsto (fun L : ℝ => P {ω | ε ≤ tailSum (Ξ ω) L}) atTop (𝓝 0) := by
  have hbound (L : ℝ) : P {ω | ε ≤ tailSum (Ξ ω) L} ≤
      ENNReal.ofReal (tailWeightMass L) * ENNReal.ofReal r / ε := by
    obtain ⟨hm, hE⟩ := lintegral_ofReal_of_decoratedSine' h (continuous_tailSumIntegrand L)
      (tailSumIntegrand_nonneg L)
    refine (meas_ge_le_lintegral_div hm.aemeasurable hε hε').trans (le_of_eq ?_)
    rw [hE]
    dsimp only
    have ha : Measurable fun x : ℝ => (1 - smoothCutoff L x) * tailWeight x :=
      ((continuous_const.sub (continuous_smoothCutoff L)).mul continuous_tailWeight).measurable
    rw [lintegral_lintegral_ofReal_mul ha (fun x => mul_nonneg
      (one_sub_smoothCutoff_nonneg L x) (tailWeight_pos x).le), lintegral_ofReal_euclidMark,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_one_sub_smoothCutoff_mul_tailWeight L)
        (Eventually.of_forall fun x => mul_nonneg (one_sub_smoothCutoff_nonneg L x)
          (tailWeight_pos x).le)]
    rfl
  have hlim : Tendsto (fun L : ℝ => ENNReal.ofReal (tailWeightMass L) * ENNReal.ofReal r / ε) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun L : ℝ => ENNReal.ofReal (tailWeightMass L)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]; exact (ENNReal.continuous_ofReal.tendsto 0).comp tendsto_tailWeightMass
    have h2 := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal r) h1 (Or.inr ENNReal.ofReal_ne_top)
    rw [zero_mul] at h2
    have h3 := ENNReal.Tendsto.div_const h2 (Or.inr hε)
    rwa [ENNReal.zero_div] at h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    hbound

end BlockBand.Critical.Herglotz
