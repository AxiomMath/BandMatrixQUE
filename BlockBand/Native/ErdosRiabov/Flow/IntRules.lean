module

public import BlockBand.Native.ErdosRiabov.Flow.Scales

/-!
# Integration rules along the VS flow

The integration rules of Erdős–Riabov along the flow. Deterministic; Lebesgue measure on `[0,t]`
(interval integrals `∫ s in 0..t`).

With `η_s = vsHeight z s = η_t + (t-s) Im m` affine and `c_m ≤ Im m ≤ 1`, for
`0 ≤ t ≤ 1`, `γ > 0`:
* `∫_0^t ds/η_s ≤ c_m⁻¹ log((C₀+1)N)` (exact value `(log η_0 - log η_t)/Im m`);
* `∫_0^t η_s^{-(1+γ)} ds ≤ (γ c_m)⁻¹ η_t^{-γ}` (exact value `(η_t^{-γ} - η_0^{-γ})/(γ Im m)`);
* `∫_0^t (ℓ_sη_s)^{-γ} ds/η_s ≤ 2/(γ c_m) (ℓ_tη_t)^{-γ}`, from
  `ℓ_sη_s ≥ (η_s/η_t)^{1/2} ℓ_tη_t` (`Kernel.loc_le_sqrt_ratio_mul`) and the second rule at `γ/2`.
The constants depend only on `c_m` and `γ` (uniform in `N, W, z, t`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Flow

open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open MeasureTheory Set

/-- First rule, exact form: `∫_0^t ds/η_s = (log η_0 - log η_t)/Im m` (`Im z > 0`, `t ≤ 1`). -/
theorem integral_inv_vsHeight {z : ℂ} (hη : 0 < z.im) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ s in (0 : ℝ)..t, (vsHeight z s)⁻¹ =
      (Real.log (vsHeight z 0) - Real.log (vsHeight z t)) / (semicircleM z).im := by
  have hy := semicircleM_im_pos hη
  have hpos : ∀ s ∈ uIcc (0 : ℝ) t, 0 < vsHeight z s := fun s hs => by
    rw [uIcc_of_le ht0] at hs
    exact vsHeight_pos hη (hs.2.trans ht1)
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t,
      HasDerivAt (fun r => -Real.log (vsHeight z r) / (semicircleM z).im)
        ((vsHeight z s)⁻¹) s := by
    intro s hs
    have h := ((hasDerivAt_vsHeight z s).log (hpos s hs).ne').neg.div_const (semicircleM z).im
    convert h using 1
    field_simp
  have hint : IntervalIntegrable (fun s => (vsHeight z s)⁻¹) volume 0 t :=
    ((continuous_vsHeight z).continuousOn.inv₀ fun s hs => (hpos s hs).ne').intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- Second rule, exact form: `∫_0^t η_s^{-(1+γ)} ds = (η_t^{-γ} - η_0^{-γ})/(γ Im m)`. -/
theorem integral_rpow_vsHeight {z : ℂ} (hη : 0 < z.im) {t γ : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hγ : 0 < γ) :
    ∫ s in (0 : ℝ)..t, vsHeight z s ^ (-(1 + γ)) =
      (vsHeight z t ^ (-γ) - vsHeight z 0 ^ (-γ)) / (γ * (semicircleM z).im) := by
  have hy := semicircleM_im_pos hη
  have hpos : ∀ s ∈ uIcc (0 : ℝ) t, 0 < vsHeight z s := fun s hs => by
    rw [uIcc_of_le ht0] at hs
    exact vsHeight_pos hη (hs.2.trans ht1)
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t,
      HasDerivAt (fun r => vsHeight z r ^ (-γ) / (γ * (semicircleM z).im))
        (vsHeight z s ^ (-(1 + γ))) s := by
    intro s hs
    have h := ((hasDerivAt_vsHeight z s).rpow_const (p := -γ)
      (Or.inl (hpos s hs).ne')).div_const (γ * (semicircleM z).im)
    convert h using 1
    rw [show -γ - 1 = -(1 + γ) by ring]
    field_simp
  have hint : IntervalIntegrable (fun s => vsHeight z s ^ (-(1 + γ))) volume 0 t :=
    ((continuous_vsHeight z).continuousOn.rpow_const
      fun s hs => Or.inl (hpos s hs).ne').intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- Second rule: `∫_0^t η_s^{-(1+γ)} ds ≤ (γ c_m)⁻¹ η_t^{-γ}` (`z ∈ 𝒟`, `0 ≤ t ≤ 1`, `γ > 0`). -/
theorem integral_rpow_vsHeight_le {N : ℕ} {δ₀ κ C₀ : ℝ} {z : ℂ} (hN : 0 < N) (hκ : 0 < κ)
    (hC₀ : 0 ≤ C₀) (hz : BulkDomain N δ₀ κ C₀ z) {t γ : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hγ : 0 < γ) :
    ∫ s in (0 : ℝ)..t, vsHeight z s ^ (-(1 + γ)) ≤
      (γ * imLower κ C₀)⁻¹ * vsHeight z t ^ (-γ) := by
  have hη := hz.im_pos hN
  have hy := semicircleM_im_pos hη
  have hcm := semicircleM_im_ge hC₀ hz.1 hη hz.2.2
  have hcm0 := imLower_pos hκ (kappa_le_two_of_bulk hz) hC₀
  rw [integral_rpow_vsHeight hη ht0 ht1 hγ]
  have h0 : 0 ≤ vsHeight z 0 ^ (-γ) := Real.rpow_nonneg (vsHeight_pos hη zero_le_one).le _
  have ht : 0 ≤ vsHeight z t ^ (-γ) := Real.rpow_nonneg (vsHeight_pos hη ht1).le _
  rw [div_le_iff₀ (by positivity), inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have : γ * imLower κ C₀ ≤ γ * (semicircleM z).im := mul_le_mul_of_nonneg_left hcm hγ.le
  nlinarith [mul_le_mul_of_nonneg_left this ht, mul_nonneg h0 (mul_pos hγ hcm0).le]

/-- `ℓ(h')h' ≥ (h'/h)^{1/2} ℓ(h)h`, in the form
`(ℓ(h')h')^{-γ} ≤ (ℓ(h)h)^{-γ} (h/h')^{γ/2}` (`0 < h ≤ h'`, `N, W ≥ 1`, `γ ≥ 0`). -/
theorem loc_mul_rpow_neg_le {N W : ℕ} (hN : 0 < N) (hW : 0 < W) {h h' γ : ℝ} (hh : 0 < h)
    (hhh : h ≤ h') (hγ : 0 ≤ γ) :
    (localizationLength N W h' * h') ^ (-γ) ≤
      (localizationLength N W h * h) ^ (-γ) * (h / h') ^ (γ / 2) := by
  have hh' : 0 < h' := hh.trans_le hhh
  have hℓ := Adapters.ErdosRiabov.loc_pos hN hW hh
  have hr : 0 < Real.sqrt (h' / h) := Real.sqrt_pos.mpr (div_pos hh' hh)
  have hrr : Real.sqrt (h' / h) * Real.sqrt (h' / h) = h' / h :=
    Real.mul_self_sqrt (div_pos hh' hh).le
  have hkey : Real.sqrt (h' / h) * (localizationLength N W h * h) ≤
      localizationLength N W h' * h' := by
    have h1 := loc_le_sqrt_ratio_mul N W hh hhh
    have h2 : Real.sqrt (h' / h) * (localizationLength N W h * h) ≤
        Real.sqrt (h' / h) * (Real.sqrt (h' / h) * localizationLength N W h') * h := by
      have := mul_le_mul_of_nonneg_left h1 hr.le
      nlinarith
    calc Real.sqrt (h' / h) * (localizationLength N W h * h)
        ≤ Real.sqrt (h' / h) * (Real.sqrt (h' / h) * localizationLength N W h') * h := h2
      _ = localizationLength N W h' * h' := by
          rw [← mul_assoc, hrr]
          field_simp
  have hpos : 0 < Real.sqrt (h' / h) * (localizationLength N W h * h) := by positivity
  calc (localizationLength N W h' * h') ^ (-γ)
      ≤ (Real.sqrt (h' / h) * (localizationLength N W h * h)) ^ (-γ) :=
        Real.rpow_le_rpow_of_nonpos hpos hkey (by linarith)
    _ = (localizationLength N W h * h) ^ (-γ) * (h / h') ^ (γ / 2) := by
        rw [Real.mul_rpow hr.le (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_mul
          (div_pos hh' hh).le, show 1 / (2 : ℝ) * -γ = -(γ / 2) by ring,
          Real.rpow_neg (div_pos hh' hh).le, ← Real.inv_rpow (div_pos hh' hh).le, inv_div]
        ring

/-- **Integration rules.** Let `N, W ≥ 1`, `0 ≤ δ₀`, `0 < κ`, `C₀ ≥ 0`,
`z ∈ 𝒟 = BulkDomain N δ₀ κ C₀ z`, `η_s = vsHeight z s`, `ℓ_s = localizationLength N W η_s`,
`c_m = imLower κ C₀`, `0 ≤ t ≤ 1`, `γ > 0`. Then `∫_0^t ds/η_s ≤ c_m⁻¹ log((C₀+1)N)`,
`∫_0^t η_s^{-(1+γ)} ds ≤ (γc_m)⁻¹ η_t^{-γ}` and
`∫_0^t (ℓ_sη_s)^{-γ} η_s⁻¹ ds ≤ 2/(γc_m) (ℓ_tη_t)^{-γ}`. Constants depend only on `c_m, γ`. -/
theorem vsIntRules {N W : ℕ} {δ₀ κ C₀ : ℝ} {z : ℂ} (hN : 0 < N) (hW : 0 < W) (hδ₀ : 0 ≤ δ₀)
    (hκ : 0 < κ) (hC₀ : 0 ≤ C₀) (hz : BulkDomain N δ₀ κ C₀ z) {t γ : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hγ : 0 < γ) :
    ∫ s in (0 : ℝ)..t, (vsHeight z s)⁻¹ ≤ (imLower κ C₀)⁻¹ * Real.log ((C₀ + 1) * N) ∧
      ∫ s in (0 : ℝ)..t, vsHeight z s ^ (-(1 + γ)) ≤
        (γ * imLower κ C₀)⁻¹ * vsHeight z t ^ (-γ) ∧
      ∫ s in (0 : ℝ)..t,
          (localizationLength N W (vsHeight z s) * vsHeight z s) ^ (-γ) * (vsHeight z s)⁻¹ ≤
        2 / (γ * imLower κ C₀) *
          (localizationLength N W (vsHeight z t) * vsHeight z t) ^ (-γ) := by
  have hη := hz.im_pos hN
  have hy := semicircleM_im_pos hη
  obtain ⟨_, _, hcm, _, hbd, _, hC, _, _, hsub, _⟩ := vsFlow_b hN hκ hC₀ hz
  have hcm0 := imLower_pos hκ (kappa_le_two_of_bulk hz) hC₀
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hηt := vsHeight_pos hη ht1
  have hbt := hbd t ht0 ht1
  refine ⟨?_, integral_rpow_vsHeight_le hN hκ hC₀ hz ht0 ht1 hγ, ?_⟩
  · -- first rule
    rw [integral_inv_vsHeight hη ht0 ht1, ← Real.log_div (vsHeight_pos hη zero_le_one).ne'
      hηt.ne']
    have hratio1 : 1 ≤ vsHeight z 0 / vsHeight z t := (one_le_div hηt).mpr hbt.2
    have hlog0 : 0 ≤ Real.log (vsHeight z 0 / vsHeight z t) := Real.log_nonneg hratio1
    have hinvN : (N : ℝ)⁻¹ ≤ vsHeight z t := by
      calc (N : ℝ)⁻¹ = (N : ℝ) ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
        _ ≤ (N : ℝ) ^ (-1 + δ₀) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ ≤ z.im := hz.2.1
        _ ≤ vsHeight z t := hbt.1
    have hratio : vsHeight z 0 / vsHeight z t ≤ (C₀ + 1) * N := by
      rw [div_le_iff₀ hηt]
      calc vsHeight z 0 ≤ C₀ + 1 := hC
        _ = (C₀ + 1) * N * (N : ℝ)⁻¹ := by field_simp
        _ ≤ (C₀ + 1) * N * vsHeight z t :=
            mul_le_mul_of_nonneg_left hinvN (by positivity)
    have hlog : Real.log (vsHeight z 0 / vsHeight z t) ≤ Real.log ((C₀ + 1) * N) :=
      Real.log_le_log (by linarith) hratio
    rw [div_eq_inv_mul]
    calc ((semicircleM z).im)⁻¹ * Real.log (vsHeight z 0 / vsHeight z t)
        ≤ (imLower κ C₀)⁻¹ * Real.log (vsHeight z 0 / vsHeight z t) :=
          mul_le_mul_of_nonneg_right ((inv_le_inv₀ hy hcm0).mpr hcm) hlog0
      _ ≤ (imLower κ C₀)⁻¹ * Real.log ((C₀ + 1) * N) :=
          mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hcm0.le)
  · -- third rule
    set L := localizationLength N W (vsHeight z t) * vsHeight z t with hL
    have hLpos : 0 < L := mul_pos (Adapters.ErdosRiabov.loc_pos hN hW hηt) hηt
    have hRHS : 0 ≤ 2 / (γ * imLower κ C₀) * L ^ (-γ) := by
      have := Real.rpow_nonneg hLpos.le (-γ)
      positivity
    by_cases hint : IntervalIntegrable (fun s =>
        (localizationLength N W (vsHeight z s) * vsHeight z s) ^ (-γ) * (vsHeight z s)⁻¹)
        volume 0 t
    swap
    · rw [intervalIntegral.integral_undef hint]
      exact hRHS
    set C := L ^ (-γ) * vsHeight z t ^ (γ / 2) with hC'
    have hpos : ∀ s ∈ Icc (0 : ℝ) t, 0 < vsHeight z s := fun s hs =>
      vsHeight_pos hη (hs.2.trans ht1)
    have hgint : IntervalIntegrable (fun s => C * vsHeight z s ^ (-(1 + γ / 2))) volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply (continuous_vsHeight z).continuousOn.rpow_const
      intro s hs
      rw [uIcc_of_le ht0] at hs
      exact Or.inl (hpos s hs).ne'
    have hpt : ∀ s ∈ Icc (0 : ℝ) t,
        (localizationLength N W (vsHeight z s) * vsHeight z s) ^ (-γ) * (vsHeight z s)⁻¹ ≤
          C * vsHeight z s ^ (-(1 + γ / 2)) := by
      intro s hs
      have hηs := hpos s hs
      have hts : vsHeight z t ≤ vsHeight z s := by
        rw [← sub_nonneg, hsub]
        exact mul_nonneg (by linarith [hs.2]) hy.le
      have hb := loc_mul_rpow_neg_le hN hW hηt hts hγ.le
      have heq : C * vsHeight z s ^ (-(1 + γ / 2)) =
          L ^ (-γ) * (vsHeight z t / vsHeight z s) ^ (γ / 2) * (vsHeight z s)⁻¹ := by
        rw [hC', Real.div_rpow hηt.le hηs.le, show -(1 + γ / 2) = -(γ / 2) + (-1 : ℝ) by ring,
          Real.rpow_add hηs, Real.rpow_neg_one, Real.rpow_neg hηs.le]
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hb (inv_nonneg.mpr hηs.le)
    calc ∫ s in (0 : ℝ)..t,
          (localizationLength N W (vsHeight z s) * vsHeight z s) ^ (-γ) * (vsHeight z s)⁻¹
        ≤ ∫ s in (0 : ℝ)..t, C * vsHeight z s ^ (-(1 + γ / 2)) :=
          intervalIntegral.integral_mono_on ht0 hint hgint hpt
      _ = C * ∫ s in (0 : ℝ)..t, vsHeight z s ^ (-(1 + γ / 2)) :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ C * ((γ / 2 * imLower κ C₀)⁻¹ * vsHeight z t ^ (-(γ / 2))) := by
          apply mul_le_mul_of_nonneg_left
            (integral_rpow_vsHeight_le hN hκ hC₀ hz ht0 ht1 (by linarith))
          have := Real.rpow_nonneg hLpos.le (-γ)
          have := Real.rpow_nonneg hηt.le (γ / 2)
          positivity
      _ = 2 / (γ * imLower κ C₀) * L ^ (-γ) := by
          rw [hC']
          have hcancel : vsHeight z t ^ (γ / 2) * vsHeight z t ^ (-(γ / 2)) = 1 := by
            rw [← Real.rpow_add hηt]
            simp
          field_simp
          linear_combination hcancel

end BlockBand.Native.ErdosRiabov.Flow
