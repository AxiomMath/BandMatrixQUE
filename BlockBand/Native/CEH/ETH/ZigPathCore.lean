module

public import BlockBand.Native.CEH.ETH.ZigHeightsGronwallTwo
public import BlockBand.Native.CEH.ETH.ZigHeightsBootstrap

/-!
# CEH ETH, two-resolvent zig, path core: integrals, grid and martingale scaling

Setting. Variance time `r ∈ [0, s]`, heights `η_{i,r} = zigHeight η_i c_i s r = η_i + c_i (s - r)`
(`η_i, c_i > 0`), product `P_r = zigHeightProd … r`, rate `c₁/η_{1,r} + c₂/η_{2,r}` (`= -P'/P`).

* `zpc_sqrt_div_sqrt_le` (AM–GM): `√(c₁c₂)/√P_r ≤ (c₁/η_{1,r} + c₂/η_{2,r})/2`.
* `zpc_exists_grid`: the dyadic grid `h_k = H/2^k`, `k ≤ L`, covers `[h, H]` when `H ≤ 2^L h`.
* `zpc_setIntegral_le`: `0 ≤ f ≤ g` on `(0, t]`, `g` continuous, gives
  `∫_{(0,t]} f ≤ ∫_0^t g` (no integrability of `f` needed).
* `zpc_norm_lt_of_parts`: `|Re m| < a` and `|Im m| < a` give `‖m‖ < 2a`.

Data of the path core (shared by all files of the path core):
* `zpc_Geom` (`s, N, η_i, c_i, ρ_i, S`) with `zpc_Geom.Valid`, heights `e₁, e₂`, product `P`,
  units `UX t = √(ρ₁ρ₂) S/√(N P_t)`, `UY t = 1/(N P_t)`, `UZ = ρ₁ρ₂ S²`,
  `ell2 = 1/(c₁η₁) + 1/(c₂η₂)`, `gm = √(c₁η₁ c₂η₂)`, grid `lvl ℓ = P_0/2^ℓ`;
* `zpc_Par` (`lam, θX, θY, θZ, βZ, Tz, Lmax, Cm, Lg`) and the constants `zpc_KX`, `zpc_KY`,
  `zpc_KZ`; the martingale budgets and levels `zpc_bX/aX`, `zpc_bY/aY`, `zpc_bZ/aZ`;
* `zpc_Proc ι κ` (the abstract processes), `zpc_Hyp` (pathwise hypotheses), `zpc_Small`
  (numeric hypotheses). The source of every field is tabulated in `ZigPathCoreClosure`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Set MeasureTheory intervalIntegral
open BlockBand.Native.CEH.Zig

/-!
## Scalar facts
-/

theorem zpc_two_sqrt_mul_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * Real.sqrt (x * y) ≤ x + y := by
  rw [Real.sqrt_mul hx]
  have h := two_mul_le_add_sq (Real.sqrt x) (Real.sqrt y)
  rw [Real.sq_sqrt hx, Real.sq_sqrt hy] at h
  linarith

theorem zpc_norm_lt_of_parts {m : ℂ} {a : ℝ} (h1 : |m.re| < a) (h2 : |m.im| < a) :
    ‖m‖ < 2 * a :=
  calc ‖m‖ ≤ |m.re| + |m.im| := Complex.norm_le_abs_re_add_abs_im _
    _ < a + a := add_lt_add h1 h2
    _ = 2 * a := by ring

/-- **Dyadic grid**.
If `0 < H`, `h ≤ H` and `H ≤ 2^L h`, some `k ≤ L`
has `H / 2^k ≤ h ≤ 2 (H / 2^k)`.
-/
theorem zpc_exists_grid {H h : ℝ} {L : ℕ} (hH : 0 < H) (hh : h ≤ H) (hL : H ≤ 2 ^ L * h) :
    ∃ k ≤ L, H / 2 ^ k ≤ h ∧ h ≤ 2 * (H / 2 ^ k) := by
  have hex : ∃ k, H / 2 ^ k ≤ h := ⟨L, by
    rw [div_le_iff₀ (by positivity)]; linarith⟩
  classical
  set k := Nat.find hex with hk
  have hkspec : H / 2 ^ k ≤ h := Nat.find_spec hex
  have hkL : k ≤ L := Nat.find_min' hex (by rw [div_le_iff₀ (by positivity)]; linarith)
  refine ⟨k, hkL, hkspec, ?_⟩
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0, pow_zero, div_one]; linarith
  · obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hjlt : j < k := by omega
    have hnot : ¬ H / 2 ^ j ≤ h := Nat.find_min hex hjlt
    push Not at hnot
    have : 2 * (H / 2 ^ k) = H / 2 ^ j := by
      rw [hj, pow_succ]; field_simp
    linarith

/-- Set integral over `(0, t]` of a nonnegative function below a continuous one. -/
theorem zpc_setIntegral_le {f g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hf0 : ∀ r ∈ Ioc 0 t, 0 ≤ f r) (hg : ContinuousOn g (Icc 0 t))
    (hfg : ∀ r ∈ Ioc 0 t, f r ≤ g r) :
    ∫ r in Ioc 0 t, f r ≤ ∫ r in (0 : ℝ)..t, g r := by
  rw [intervalIntegral.integral_of_le ht]
  exact integral_mono_of_nonneg ((ae_restrict_mem measurableSet_Ioc).mono hf0)
    ((hg.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    ((ae_restrict_mem measurableSet_Ioc).mono hfg)

/-- `‖∫_0^t f‖ ≤ ∫_0^t g` from a pointwise bound on `[0, t]`, `g` continuous. -/
theorem zpc_norm_integral_le {f : ℝ → ℂ} {g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hg : ContinuousOn g (Icc 0 t)) (hfg : ∀ r ∈ Icc 0 t, ‖f r‖ ≤ g r) :
    ‖∫ r in (0 : ℝ)..t, f r‖ ≤ ∫ r in (0 : ℝ)..t, g r :=
  intervalIntegral.norm_integral_le_of_norm_le ht
    (Filter.Eventually.of_forall fun r hr => hfg r ⟨hr.1.le, hr.2⟩)
    (hg.intervalIntegrable_of_Icc ht)

/-- The real version of `zpc_norm_integral_le`. -/
theorem zpc_abs_integral_le {f g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hg : ContinuousOn g (Icc 0 t)) (hfg : ∀ r ∈ Icc 0 t, |f r| ≤ g r) :
    |∫ r in (0 : ℝ)..t, f r| ≤ ∫ r in (0 : ℝ)..t, g r := by
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) ht
    (Filter.Eventually.of_forall fun r hr =>
      (Real.norm_eq_abs (f r)).trans_le (hfg r ⟨hr.1.le, hr.2⟩))
    (hg.intervalIntegrable_of_Icc ht)
  rwa [Real.norm_eq_abs] at h

/-!
## Two-height integrals on `[0, t]`
-/

section Integrals

variable {η₁ c₁ η₂ c₂ s : ℝ}

/-- **AM–GM** (pointwise): `√(c₁c₂)/√P_r ≤ (c₁/η_{1,r} + c₂/η_{2,r})/2`. -/
theorem zpc_sqrt_div_sqrt_le (hη₁ : 0 < η₁) (hc₁ : 0 < c₁) (hη₂ : 0 < η₂) (hc₂ : 0 < c₂)
    {r : ℝ} (hr : r ≤ s) :
    Real.sqrt (c₁ * c₂) / Real.sqrt (zigHeightProd η₁ c₁ η₂ c₂ s r) ≤
      (c₁ / zigHeight η₁ c₁ s r + c₂ / zigHeight η₂ c₂ s r) / 2 := by
  have h1 := zigHeight_pos hη₁ hc₁.le hr
  have h2 := zigHeight_pos hη₂ hc₂.le hr
  have hP := zigHeightProd_pos hη₁ hc₁.le hη₂ hc₂.le hr
  rw [← Real.sqrt_div' _ hP.le]
  have e : c₁ * c₂ / zigHeightProd η₁ c₁ η₂ c₂ s r =
      (c₁ / zigHeight η₁ c₁ s r) * (c₂ / zigHeight η₂ c₂ s r) := by
    simp only [zigHeightProd]
    field_simp
  rw [e]
  have := zpc_two_sqrt_mul_le (x := c₁ / zigHeight η₁ c₁ s r) (y := c₂ / zigHeight η₂ c₂ s r)
    (by positivity) (by positivity)
  linarith

/-- `√(c₁ η₁ c₂ η₂) ≤ √(c₁ c₂) √P_t` for `t ≤ s` (`η_i ≤ η_{i,t}`). -/
theorem zpc_sqrt_le_sqrt_mul_sqrt (hη₁ : 0 < η₁) (hc₁ : 0 < c₁) (hη₂ : 0 < η₂) (hc₂ : 0 < c₂)
    {t : ℝ} (ht : t ≤ s) :
    Real.sqrt (c₁ * η₁ * (c₂ * η₂)) ≤
      Real.sqrt (c₁ * c₂) * Real.sqrt (zigHeightProd η₁ c₁ η₂ c₂ s t) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  have a1 := le_zigHeight (η := η₁) hc₁.le ht
  have a2 := le_zigHeight (η := η₂) hc₂.le ht
  simp only [zigHeightProd]
  have : c₁ * η₁ * (c₂ * η₂) = c₁ * c₂ * (η₁ * η₂) := by ring
  rw [this]
  have := zigHeight_pos hη₁ hc₁.le ht
  have := zigHeight_pos hη₂ hc₂.le ht
  gcongr

/-- The common AM–GM integration step: if `f ≤ (rate / P^a) / (2√(c₁c₂))` on `[0, t]`, then
`∫_0^t f ≤ 1/(a P_t^a) / (2√(c₁c₂))`. -/
theorem zpc_integral_le_of_amgm (hη₁ : 0 < η₁) (hc₁ : 0 < c₁) (hη₂ : 0 < η₂) (hc₂ : 0 < c₂)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ s) {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 t))
    (hle : ∀ r ∈ Icc 0 t, f r ≤ (c₁ / zigHeight η₁ c₁ s r + c₂ / zigHeight η₂ c₂ s r) /
      zigHeightProd η₁ c₁ η₂ c₂ s r ^ a / (2 * Real.sqrt (c₁ * c₂))) :
    ∫ r in (0 : ℝ)..t, f r ≤
      1 / (a * zigHeightProd η₁ c₁ η₂ c₂ s t ^ a) / (2 * Real.sqrt (c₁ * c₂)) := by
  have h1 : ∀ r ∈ Icc 0 t, 0 < zigHeight η₁ c₁ s r := fun r hr =>
    zigHeight_pos hη₁ hc₁.le (hr.2.trans ht)
  have h2 : ∀ r ∈ Icc 0 t, 0 < zigHeight η₂ c₂ s r := fun r hr =>
    zigHeight_pos hη₂ hc₂.le (hr.2.trans ht)
  have hg : ContinuousOn (fun r => (c₁ / zigHeight η₁ c₁ s r + c₂ / zigHeight η₂ c₂ s r) /
      zigHeightProd η₁ c₁ η₂ c₂ s r ^ a / (2 * Real.sqrt (c₁ * c₂))) (Icc 0 t) := by
    have hsc : 0 < Real.sqrt (c₁ * c₂) := Real.sqrt_pos.2 (by positivity)
    unfold zigHeightProd
    fun_prop (disch := first
      | (intro r hr; have := h1 r hr; have := h2 r hr; positivity)
      | (intro r hr; have := h1 r hr; have := h2 r hr; left; positivity)
      | positivity)
  have hmono := intervalIntegral.integral_mono_on ht0
    (hf.intervalIntegrable_of_Icc (μ := volume) ht0)
    (hg.intervalIntegrable_of_Icc (μ := volume) ht0) hle
  refine hmono.trans ?_
  rw [intervalIntegral.integral_div]
  have hsc : 0 < 2 * Real.sqrt (c₁ * c₂) := by
    have := Real.sqrt_pos.2 (mul_pos hc₁ hc₂); positivity
  exact div_le_div_of_nonneg_right
    (integral_zigHeightProd_rpow_le hη₁ hc₁.le hη₂ hc₂.le (ht0.trans ht) ht ha) hsc.le

/-- `∫_0^t 1/P ≤ 1/(√(c₁c₂) √P_t)`. -/
theorem zpc_integral_inv_P_le (hη₁ : 0 < η₁) (hc₁ : 0 < c₁) (hη₂ : 0 < η₂) (hc₂ : 0 < c₂)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ s) :
    ∫ r in (0 : ℝ)..t, 1 / zigHeightProd η₁ c₁ η₂ c₂ s r ≤
      1 / (Real.sqrt (c₁ * c₂) * Real.sqrt (zigHeightProd η₁ c₁ η₂ c₂ s t)) := by
  have hsc : 0 < Real.sqrt (c₁ * c₂) := Real.sqrt_pos.2 (mul_pos hc₁ hc₂)
  have hP : ∀ r ∈ Icc 0 t, 0 < zigHeightProd η₁ c₁ η₂ c₂ s r := fun r hr =>
    zigHeightProd_pos hη₁ hc₁.le hη₂ hc₂.le (hr.2.trans ht)
  have h := zpc_integral_le_of_amgm hη₁ hc₁ hη₂ hc₂ ht0 ht (a := 1 / 2) (by norm_num)
    (f := fun r => 1 / zigHeightProd η₁ c₁ η₂ c₂ s r)
    (continuousOn_const.div continuous_zigHeightProd.continuousOn fun r hr => (hP r hr).ne')
    (fun r hr => by
      have hPr := hP r hr
      have hQ : 0 < Real.sqrt (zigHeightProd η₁ c₁ η₂ c₂ s r) := Real.sqrt_pos.2 hPr
      have am := zpc_sqrt_div_sqrt_le hη₁ hc₁ hη₂ hc₂ (hr.2.trans ht)
      rw [← Real.sqrt_eq_rpow]
      set Q := Real.sqrt (zigHeightProd η₁ c₁ η₂ c₂ s r) with hQdef
      set A := Real.sqrt (c₁ * c₂)
      set rt := c₁ / zigHeight η₁ c₁ s r + c₂ / zigHeight η₂ c₂ s r
      have eP : zigHeightProd η₁ c₁ η₂ c₂ s r = Q * Q := (Real.mul_self_sqrt hPr.le).symm
      rw [eP]
      calc 1 / (Q * Q) = A / Q / (A * Q) := by field_simp
        _ ≤ rt / 2 / (A * Q) := by gcongr
        _ = rt / Q / (2 * A) := by field_simp)
  refine h.trans (le_of_eq ?_)
  rw [← Real.sqrt_eq_rpow]
  have := Real.sqrt_pos.2 (hP t ⟨ht0, le_rfl⟩)
  field_simp

/-- `∫_0^t 1/(P √P) ≤ 1/(2√(c₁c₂) P_t)`. -/
theorem zpc_integral_inv_P_sqrt_le (hη₁ : 0 < η₁) (hc₁ : 0 < c₁) (hη₂ : 0 < η₂)
    (hc₂ : 0 < c₂) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ s) :
    ∫ r in (0 : ℝ)..t, 1 / (zigHeightProd η₁ c₁ η₂ c₂ s r *
        Real.sqrt (zigHeightProd η₁ c₁ η₂ c₂ s r)) ≤
      1 / (2 * Real.sqrt (c₁ * c₂) * zigHeightProd η₁ c₁ η₂ c₂ s t) := by
  have hsc : 0 < Real.sqrt (c₁ * c₂) := Real.sqrt_pos.2 (mul_pos hc₁ hc₂)
  have hP : ∀ r ∈ Icc 0 t, 0 < zigHeightProd η₁ c₁ η₂ c₂ s r := fun r hr =>
    zigHeightProd_pos hη₁ hc₁.le hη₂ hc₂.le (hr.2.trans ht)
  have hcont : ContinuousOn (fun r => 1 / (zigHeightProd η₁ c₁ η₂ c₂ s r *
      Real.sqrt (zigHeightProd η₁ c₁ η₂ c₂ s r))) (Icc 0 t) :=
    continuousOn_const.div (continuous_zigHeightProd.continuousOn.mul
      continuous_zigHeightProd.continuousOn.sqrt) fun r hr => by
        have := hP r hr; have := Real.sqrt_pos.2 this; positivity
  have h := zpc_integral_le_of_amgm hη₁ hc₁ hη₂ hc₂ ht0 ht (a := 1) one_pos hcont
    (fun r hr => by
      have hPr := hP r hr
      have hQ : 0 < Real.sqrt (zigHeightProd η₁ c₁ η₂ c₂ s r) := Real.sqrt_pos.2 hPr
      have am := zpc_sqrt_div_sqrt_le hη₁ hc₁ hη₂ hc₂ (hr.2.trans ht)
      rw [Real.rpow_one]
      set Q := Real.sqrt (zigHeightProd η₁ c₁ η₂ c₂ s r) with hQdef
      set A := Real.sqrt (c₁ * c₂)
      set rt := c₁ / zigHeight η₁ c₁ s r + c₂ / zigHeight η₂ c₂ s r
      set Pr := zigHeightProd η₁ c₁ η₂ c₂ s r
      calc 1 / (Pr * Q) = A / Q / (A * Pr) := by field_simp
        _ ≤ rt / 2 / (A * Pr) := by gcongr
        _ = rt / Pr / (2 * A) := by field_simp)
  refine h.trans (le_of_eq ?_)
  rw [Real.rpow_one]
  have := hP t ⟨ht0, le_rfl⟩
  field_simp

/-- `∫_0^t 1/P² ≤ 1/(3√(c₁c₂) P_t √P_t)`. -/
theorem zpc_integral_inv_P_sq_le (hη₁ : 0 < η₁) (hc₁ : 0 < c₁) (hη₂ : 0 < η₂) (hc₂ : 0 < c₂)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ s) :
    ∫ r in (0 : ℝ)..t, 1 / zigHeightProd η₁ c₁ η₂ c₂ s r ^ 2 ≤
      1 / (3 * Real.sqrt (c₁ * c₂) * (zigHeightProd η₁ c₁ η₂ c₂ s t *
        Real.sqrt (zigHeightProd η₁ c₁ η₂ c₂ s t))) := by
  have hsc : 0 < Real.sqrt (c₁ * c₂) := Real.sqrt_pos.2 (mul_pos hc₁ hc₂)
  have hP : ∀ r ∈ Icc 0 t, 0 < zigHeightProd η₁ c₁ η₂ c₂ s r := fun r hr =>
    zigHeightProd_pos hη₁ hc₁.le hη₂ hc₂.le (hr.2.trans ht)
  have e32 : ∀ x : ℝ, 0 ≤ x → x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    intro x hx
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hcont : ContinuousOn (fun r => 1 / zigHeightProd η₁ c₁ η₂ c₂ s r ^ 2) (Icc 0 t) :=
    continuousOn_const.div (continuous_zigHeightProd.continuousOn.pow 2) fun r hr => by
      have := hP r hr; positivity
  have h := zpc_integral_le_of_amgm hη₁ hc₁ hη₂ hc₂ ht0 ht (a := 3 / 2) (by norm_num) hcont
    (fun r hr => by
      have hPr := hP r hr
      have hQ : 0 < Real.sqrt (zigHeightProd η₁ c₁ η₂ c₂ s r) := Real.sqrt_pos.2 hPr
      have am := zpc_sqrt_div_sqrt_le hη₁ hc₁ hη₂ hc₂ (hr.2.trans ht)
      rw [e32 _ hPr.le]
      set Q := Real.sqrt (zigHeightProd η₁ c₁ η₂ c₂ s r) with hQdef
      set A := Real.sqrt (c₁ * c₂)
      set rt := c₁ / zigHeight η₁ c₁ s r + c₂ / zigHeight η₂ c₂ s r
      have eP : zigHeightProd η₁ c₁ η₂ c₂ s r = Q * Q := (Real.mul_self_sqrt hPr.le).symm
      rw [eP]
      calc 1 / (Q * Q) ^ 2 = A / Q / (A * (Q * Q * Q)) := by field_simp
        _ ≤ rt / 2 / (A * (Q * Q * Q)) := by gcongr
        _ = rt / (Q * Q * Q) / (2 * A) := by field_simp)
  refine h.trans (le_of_eq ?_)
  have hPt := hP t ⟨ht0, le_rfl⟩
  rw [e32 _ hPt.le]
  have := Real.sqrt_pos.2 hPt
  field_simp

variable {η c η' c' : ℝ}

/-- `∫_0^t c/(η_r² η'_r) ≤ 1/(η_t η'_t)` (any second height `η'`). -/
theorem zpc_integral_sq_mul_le (hη : 0 < η) (hc : 0 < c) (hη' : 0 < η') (hc' : 0 ≤ c')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ s) :
    ∫ r in (0 : ℝ)..t, c / (zigHeight η c s r ^ 2 * zigHeight η' c' s r) ≤
      1 / (zigHeight η c s t * zigHeight η' c' s t) := by
  have h := integral_two_height_rpow_le hη hc.le hη' hc' ht0 ht (α := 2) (β := 1)
    (by norm_num) zero_le_one
  simp only [Real.rpow_one, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_two, one_mul] at h
  exact h

/-- `∫_0^t c/(η_r² √η'_r) ≤ 1/(η_t √η'_t)`. -/
theorem zpc_integral_sq_mul_sqrt_le (hη : 0 < η) (hc : 0 < c) (hη' : 0 < η') (hc' : 0 ≤ c')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ s) :
    ∫ r in (0 : ℝ)..t, c / (zigHeight η c s r ^ 2 * Real.sqrt (zigHeight η' c' s r)) ≤
      1 / (zigHeight η c s t * Real.sqrt (zigHeight η' c' s t)) := by
  have h := integral_two_height_rpow_le hη hc.le hη' hc' ht0 ht (α := 2) (β := 1 / 2)
    (by norm_num) (by norm_num)
  simp only [Real.rpow_one, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_two, one_mul,
    ← Real.sqrt_eq_rpow] at h
  exact h

/-- `∫_0^t c/(η_r³ η'_r²) ≤ 1/(2 η_t² η'_t²)`. -/
theorem zpc_integral_cube_mul_sq_le (hη : 0 < η) (hc : 0 < c) (hη' : 0 < η') (hc' : 0 ≤ c')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ s) :
    ∫ r in (0 : ℝ)..t, c / (zigHeight η c s r ^ 3 * zigHeight η' c' s r ^ 2) ≤
      1 / (2 * zigHeight η c s t ^ 2 * zigHeight η' c' s t ^ 2) := by
  have h := integral_two_height_rpow_le hη hc.le hη' hc' ht0 ht (α := 3) (β := 2)
    (by norm_num) (by norm_num)
  have e3 : ∀ x : ℝ, x ^ (3 : ℝ) = x ^ 3 := fun x => by norm_num
  simp only [e3, show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two] at h
  exact h

/-- `∫_0^t c/η_r² ≤ 1/η_t`. -/
theorem zpc_integral_inv_sq_le (hη : 0 < η) (hc : 0 < c) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ s) :
    ∫ r in (0 : ℝ)..t, c / zigHeight η c s r ^ 2 ≤ 1 / zigHeight η c s t := by
  rw [integral_div_zigHeight_sq hη hc.le (ht0.trans ht) ht]
  have := zigHeight_pos hη hc.le (ht0.trans ht)
  have : 0 < 1 / zigHeight η c s 0 := by positivity
  linarith

end Integrals

/-!
## Sums of integrals
-/

theorem zpc_integral_add2_le {f₁ f₂ : ℝ → ℝ} {a₁ a₂ B₁ B₂ t : ℝ} (ht : 0 ≤ t)
    (h₁ : ContinuousOn f₁ (Icc 0 t)) (h₂ : ContinuousOn f₂ (Icc 0 t)) (ha₁ : 0 ≤ a₁)
    (ha₂ : 0 ≤ a₂) (hB₁ : ∫ r in (0 : ℝ)..t, f₁ r ≤ B₁) (hB₂ : ∫ r in (0 : ℝ)..t, f₂ r ≤ B₂) :
    ∫ r in (0 : ℝ)..t, (a₁ * f₁ r + a₂ * f₂ r) ≤ a₁ * B₁ + a₂ * B₂ := by
  have i₁ := (h₁.intervalIntegrable_of_Icc (μ := volume) ht).const_mul a₁
  have i₂ := (h₂.intervalIntegrable_of_Icc (μ := volume) ht).const_mul a₂
  rw [intervalIntegral.integral_add i₁ i₂, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have := mul_le_mul_of_nonneg_left hB₁ ha₁
  have := mul_le_mul_of_nonneg_left hB₂ ha₂
  linarith

theorem zpc_integral_add3_le {f₁ f₂ f₃ : ℝ → ℝ} {a₁ a₂ a₃ B₁ B₂ B₃ t : ℝ} (ht : 0 ≤ t)
    (h₁ : ContinuousOn f₁ (Icc 0 t)) (h₂ : ContinuousOn f₂ (Icc 0 t))
    (h₃ : ContinuousOn f₃ (Icc 0 t)) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃)
    (hB₁ : ∫ r in (0 : ℝ)..t, f₁ r ≤ B₁) (hB₂ : ∫ r in (0 : ℝ)..t, f₂ r ≤ B₂)
    (hB₃ : ∫ r in (0 : ℝ)..t, f₃ r ≤ B₃) :
    ∫ r in (0 : ℝ)..t, (a₁ * f₁ r + a₂ * f₂ r + a₃ * f₃ r) ≤ a₁ * B₁ + a₂ * B₂ + a₃ * B₃ := by
  have i₁ := (h₁.intervalIntegrable_of_Icc (μ := volume) ht).const_mul a₁
  have i₂ := (h₂.intervalIntegrable_of_Icc (μ := volume) ht).const_mul a₂
  have i₃ := (h₃.intervalIntegrable_of_Icc (μ := volume) ht).const_mul a₃
  rw [intervalIntegral.integral_add (i₁.add i₂) i₃, intervalIntegral.integral_add i₁ i₂,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have := mul_le_mul_of_nonneg_left hB₁ ha₁
  have := mul_le_mul_of_nonneg_left hB₂ ha₂
  have := mul_le_mul_of_nonneg_left hB₃ ha₃
  linarith

theorem zpc_integral_add4_le {f₁ f₂ f₃ f₄ : ℝ → ℝ} {a₁ a₂ a₃ a₄ B₁ B₂ B₃ B₄ t : ℝ}
    (ht : 0 ≤ t) (h₁ : ContinuousOn f₁ (Icc 0 t)) (h₂ : ContinuousOn f₂ (Icc 0 t))
    (h₃ : ContinuousOn f₃ (Icc 0 t)) (h₄ : ContinuousOn f₄ (Icc 0 t)) (ha₁ : 0 ≤ a₁)
    (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (ha₄ : 0 ≤ a₄)
    (hB₁ : ∫ r in (0 : ℝ)..t, f₁ r ≤ B₁) (hB₂ : ∫ r in (0 : ℝ)..t, f₂ r ≤ B₂)
    (hB₃ : ∫ r in (0 : ℝ)..t, f₃ r ≤ B₃) (hB₄ : ∫ r in (0 : ℝ)..t, f₄ r ≤ B₄) :
    ∫ r in (0 : ℝ)..t, (a₁ * f₁ r + a₂ * f₂ r + a₃ * f₃ r + a₄ * f₄ r) ≤
      a₁ * B₁ + a₂ * B₂ + a₃ * B₃ + a₄ * B₄ := by
  have i₁ := (h₁.intervalIntegrable_of_Icc (μ := volume) ht).const_mul a₁
  have i₂ := (h₂.intervalIntegrable_of_Icc (μ := volume) ht).const_mul a₂
  have i₃ := (h₃.intervalIntegrable_of_Icc (μ := volume) ht).const_mul a₃
  have i₄ := (h₄.intervalIntegrable_of_Icc (μ := volume) ht).const_mul a₄
  rw [intervalIntegral.integral_add ((i₁.add i₂).add i₃) i₄,
    intervalIntegral.integral_add (i₁.add i₂) i₃, intervalIntegral.integral_add i₁ i₂,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have := mul_le_mul_of_nonneg_left hB₁ ha₁
  have := mul_le_mul_of_nonneg_left hB₂ ha₂
  have := mul_le_mul_of_nonneg_left hB₃ ha₃
  have := mul_le_mul_of_nonneg_left hB₄ ha₄
  linarith

/-!
## The data of the path core
-/

/-- **Geometry and scales** of the two-resolvent zig at fixed spectral data: target time `s`,
size `N`, heights `η_i` at the target, slopes `c_i` (`= π ρ_i`), densities `ρ_i`, and a constant
control `S` (in the application `S = s₂(s) ≥ s₂(σ)`, since `sTwoAt` is monotone). -/
structure zpc_Geom where
  /-- target variance time -/
  s : ℝ
  /-- matrix size (as a real number) -/
  N : ℝ
  /-- `η₁ = |Im z₁|` -/
  η₁ : ℝ
  /-- `η₂ = |Im z₂|` -/
  η₂ : ℝ
  /-- `c₁ = |Im m₁| = π ρ₁` -/
  c₁ : ℝ
  /-- `c₂ = |Im m₂| = π ρ₂` -/
  c₂ : ℝ
  /-- density at `z₁` -/
  ρ₁ : ℝ
  /-- density at `z₂` -/
  ρ₂ : ℝ
  /-- constant control, `S ≥ s₂(σ)` on `[0, s]` -/
  S : ℝ

namespace zpc_Geom

variable (G : zpc_Geom)

/-- `η_{1,t} = η₁ + c₁ (s - t)`. -/
def e₁ (t : ℝ) : ℝ := zigHeight G.η₁ G.c₁ G.s t

/-- `η_{2,t} = η₂ + c₂ (s - t)`. -/
def e₂ (t : ℝ) : ℝ := zigHeight G.η₂ G.c₂ G.s t

/-- `P_t = η_{1,t} η_{2,t}`. -/
def P (t : ℝ) : ℝ := zigHeightProd G.η₁ G.c₁ G.η₂ G.c₂ G.s t

/-- Unit of `X`: `U_X(t) = √(ρ₁ρ₂) S / √(N P_t)`. -/
def UX (t : ℝ) : ℝ := Real.sqrt (G.ρ₁ * G.ρ₂) * G.S / Real.sqrt (G.N * G.P t)

/-- Unit of `Y`: `U_Y(t) = 1 / (N P_t)`. -/
def UY (t : ℝ) : ℝ := 1 / (G.N * G.P t)

/-- Unit of `Z`: `U_Z = ρ₁ρ₂ S²`. -/
def UZ : ℝ := G.ρ₁ * G.ρ₂ * G.S ^ 2

/-- `ℓ₂ = 1/(c₁η₁) + 1/(c₂η₂)` (`≤ 2N/(π N^{ε_ρ})` on the window). -/
def ell2 : ℝ := 1 / (G.c₁ * G.η₁) + 1 / (G.c₂ * G.η₂)

/-- `gm = √(c₁η₁ · c₂η₂)` (`≥ π N^{ε_ρ}/N` on the window). -/
def gm : ℝ := Real.sqrt (G.c₁ * G.η₁ * (G.c₂ * G.η₂))

/-- The dyadic grid in `P`: `h_ℓ = P_0 / 2^ℓ`. -/
def lvl (ℓ : ℕ) : ℝ := G.P 0 / 2 ^ ℓ

/-- Validity of the geometry. -/
structure Valid : Prop where
  s_nonneg : 0 ≤ G.s
  N_pos : 0 < G.N
  η₁_pos : 0 < G.η₁
  η₂_pos : 0 < G.η₂
  ρ₁_pos : 0 < G.ρ₁
  ρ₂_pos : 0 < G.ρ₂
  S_pos : 0 < G.S
  c₁_eq : G.c₁ = Real.pi * G.ρ₁
  c₂_eq : G.c₂ = Real.pi * G.ρ₂

variable {G}

theorem P_eq (t : ℝ) : G.P t = G.e₁ t * G.e₂ t := rfl

theorem continuousOn_P : ContinuousOn G.P (Icc 0 G.s) :=
  continuous_zigHeightProd.continuousOn

namespace Valid

variable (hG : G.Valid)
include hG

theorem c₁_pos : 0 < G.c₁ := by rw [hG.c₁_eq]; exact mul_pos Real.pi_pos hG.ρ₁_pos

theorem c₂_pos : 0 < G.c₂ := by rw [hG.c₂_eq]; exact mul_pos Real.pi_pos hG.ρ₂_pos

theorem e₁_pos {t : ℝ} (ht : t ≤ G.s) : 0 < G.e₁ t :=
  zigHeight_pos hG.η₁_pos hG.c₁_pos.le ht

theorem e₂_pos {t : ℝ} (ht : t ≤ G.s) : 0 < G.e₂ t :=
  zigHeight_pos hG.η₂_pos hG.c₂_pos.le ht

theorem P_pos {t : ℝ} (ht : t ≤ G.s) : 0 < G.P t :=
  zigHeightProd_pos hG.η₁_pos hG.c₁_pos.le hG.η₂_pos hG.c₂_pos.le ht

theorem P_anti {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) (h₂ : t₂ ≤ G.s) : G.P t₂ ≤ G.P t₁ :=
  zigHeightProd_antitone hG.η₁_pos hG.c₁_pos.le hG.η₂_pos hG.c₂_pos.le h h₂

theorem η₁_le_e₁ {t : ℝ} (ht : t ≤ G.s) : G.η₁ ≤ G.e₁ t := le_zigHeight hG.c₁_pos.le ht

theorem η₂_le_e₂ {t : ℝ} (ht : t ≤ G.s) : G.η₂ ≤ G.e₂ t := le_zigHeight hG.c₂_pos.le ht

theorem UX_pos {t : ℝ} (ht : t ≤ G.s) : 0 < G.UX t := by
  have := hG.P_pos ht
  have := hG.N_pos
  have := hG.ρ₁_pos
  have := hG.ρ₂_pos
  have := hG.S_pos
  unfold UX
  have : 0 < Real.sqrt (G.ρ₁ * G.ρ₂) := Real.sqrt_pos.2 (by positivity)
  have : 0 < Real.sqrt (G.N * G.P t) := Real.sqrt_pos.2 (by positivity)
  positivity

theorem UY_pos {t : ℝ} (ht : t ≤ G.s) : 0 < G.UY t := by
  have := hG.P_pos ht
  have := hG.N_pos
  unfold UY
  positivity

theorem UZ_pos : 0 < G.UZ := by
  have := hG.ρ₁_pos
  have := hG.ρ₂_pos
  have := hG.S_pos
  unfold UZ
  positivity

theorem ell2_pos : 0 < G.ell2 := by
  have := hG.c₁_pos
  have := hG.c₂_pos
  have := hG.η₁_pos
  have := hG.η₂_pos
  unfold ell2
  positivity

theorem gm_pos : 0 < G.gm := by
  have := hG.c₁_pos
  have := hG.c₂_pos
  have := hG.η₁_pos
  have := hG.η₂_pos
  exact Real.sqrt_pos.2 (by positivity)

theorem lvl_pos (ℓ : ℕ) : 0 < G.lvl ℓ := by
  have := hG.P_pos hG.s_nonneg
  unfold lvl
  positivity

/-- `√(c₁c₂) = π √(ρ₁ρ₂)`. -/
theorem sqrt_c₁c₂ : Real.sqrt (G.c₁ * G.c₂) = Real.pi * Real.sqrt (G.ρ₁ * G.ρ₂) := by
  rw [hG.c₁_eq, hG.c₂_eq, show Real.pi * G.ρ₁ * (Real.pi * G.ρ₂) =
    Real.pi ^ 2 * (G.ρ₁ * G.ρ₂) by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq Real.pi_pos.le]

/-- `gm ≤ √(c₁c₂) √P_t`. -/
theorem gm_le {t : ℝ} (ht : t ≤ G.s) :
    G.gm ≤ Real.sqrt (G.c₁ * G.c₂) * Real.sqrt (G.P t) :=
  zpc_sqrt_le_sqrt_mul_sqrt hG.η₁_pos hG.c₁_pos hG.η₂_pos hG.c₂_pos ht

theorem continuousOn_UX : ContinuousOn G.UX (Icc 0 G.s) := by
  have hP : ∀ r ∈ Icc 0 G.s, 0 < G.P r := fun r hr => hG.P_pos hr.2
  have hN := hG.N_pos
  refine continuousOn_const.div ((continuousOn_const.mul continuousOn_P).sqrt) ?_
  intro r hr
  have := hP r hr
  exact (Real.sqrt_pos.2 (by positivity)).ne'

theorem continuousOn_UY : ContinuousOn G.UY (Icc 0 G.s) := by
  have hP : ∀ r ∈ Icc 0 G.s, 0 < G.P r := fun r hr => hG.P_pos hr.2
  have hN := hG.N_pos
  refine continuousOn_const.div (continuousOn_const.mul continuousOn_P) ?_
  intro r hr
  have := hP r hr
  positivity

/-- The grid cell of a time: `h_ℓ ≤ P_t ≤ 2 h_ℓ` for some `ℓ ≤ L`, when `P_0 ≤ 2^L P_s`. -/
theorem exists_cell {L : ℕ} (hL : G.P 0 ≤ 2 ^ L * G.P G.s) {t : ℝ} (ht : t ∈ Icc 0 G.s) :
    ∃ ℓ ≤ L, G.lvl ℓ ≤ G.P t ∧ G.P t ≤ 2 * G.lvl ℓ :=
  zpc_exists_grid (hG.P_pos hG.s_nonneg) (hG.P_anti ht.1 ht.2)
    (hL.trans (mul_le_mul_of_nonneg_left (hG.P_anti ht.2 le_rfl) (by positivity)))

end Valid

end zpc_Geom

/-- **Parameters**: martingale level factor `lam` (`N^{ξ/4}`), thresholds `θX = θY` (`N^{2ξ}`)
and `θZ` (`N^ξ`), endpoint factor `βZ` (`N^{ξ/2}`), tube factor `Tz` (`N^ζ`), log bound `Lmax`
(`≥ log(P_0/P_s)`, `2 log N + C` on the window), the Lemma 5.6 constant `Cm`
(`lemma56Const`), and the
number of grid levels `Lg` (`P_0 ≤ 2^Lg P_s`). -/
structure zpc_Par where
  lam : ℝ
  θX : ℝ
  θY : ℝ
  θZ : ℝ
  βZ : ℝ
  Tz : ℝ
  Lmax : ℝ
  Cm : ℝ
  Lg : ℕ

variable (G : zpc_Geom) (p : zpc_Par)

/-- The `Y` constant `K_Y = 4√3 lam + θY²/(3 N gm) + 3 Tz` (martingale, `Y²`, tube terms). -/
def zpc_KY : ℝ := 4 * Real.sqrt 3 * p.lam + p.θY ^ 2 / (3 * G.N * G.gm) + 3 * p.Tz

/-- The `X` constant: martingale `2 lam √(2 θZ ℓ₂/N)`, `⟨M^A⟩·Y` term `Cm θY/√(N ρ₁ρ₂)`,
`X·Y` term `θX θY/(2 N gm)`, tube terms `Tz √(3θZ/2) (1/√(N c₁η₁) + 1/√(N c₂η₂))`. -/
def zpc_KX : ℝ :=
  2 * p.lam * Real.sqrt (2 * p.θZ * G.ell2 / G.N) +
    p.Cm * p.θY / Real.sqrt (G.N * (G.ρ₁ * G.ρ₂)) + p.θX * p.θY / (2 * G.N * G.gm) +
    p.Tz * Real.sqrt (3 / 2 * p.θZ) *
      (1 / Real.sqrt (G.N * (G.c₁ * G.η₁)) + 1 / Real.sqrt (G.N * (G.c₂ * G.η₂)))

/-- The `Z` constant: initial value `π²`, martingale `lam θZ √(2ℓ₂/N)`, tube terms
`3 Tz θZ ℓ₂/N`, deterministic cross term `8 s Cm² π²`, fluctuating cross term `8 θX²/(N gm)`. -/
def zpc_KZ : ℝ :=
  Real.pi ^ 2 + p.lam * p.θZ * Real.sqrt (2 * G.ell2 / G.N) + 3 * p.Tz * p.θZ * G.ell2 / G.N +
    8 * G.s * p.Cm ^ 2 * Real.pi ^ 2 + 8 * p.θX ^ 2 / (G.N * G.gm)

/-- **Martingale budget of `X`** at grid level `ℓ`: `b = θZ U_Z ℓ₂ / (N² h_ℓ)`. -/
def zpc_bX (ℓ : ℕ) : ℝ := p.θZ * G.UZ * G.ell2 / (G.N ^ 2 * G.lvl ℓ)

/-- **Martingale level of `X`** at grid level `ℓ`: `a = lam √b` (so `a²/(2b) = lam²/2`). -/
def zpc_aX (ℓ : ℕ) : ℝ := p.lam * Real.sqrt (zpc_bX G p ℓ)

/-- **Martingale budget of `Y`** at grid level `ℓ`: `b = 3 / (N² h_ℓ²)`. -/
def zpc_bY (ℓ : ℕ) : ℝ := 3 / (G.N ^ 2 * G.lvl ℓ ^ 2)

/-- **Martingale level of `Y`**: `a = lam √b`. -/
def zpc_aY (ℓ : ℕ) : ℝ := p.lam * Real.sqrt (zpc_bY G ℓ)

/-- **Martingale budget of `Z`** (one level): `b = 2 θZ² U_Z² ℓ₂ / N`. -/
def zpc_bZ : ℝ := 2 * p.θZ ^ 2 * G.UZ ^ 2 * G.ell2 / G.N

/-- **Martingale level of `Z`**: `a = lam √b`. -/
def zpc_aZ : ℝ := p.lam * Real.sqrt (zpc_bZ G p)

/-- **The abstract processes** of one sample path (all functions of the variance time `r`).
`ι` indexes the four constellations of the `A`-chain, `κ` those of the `I`-chain; `yX k` is the
`I`-chain of the constellation of `k`. -/
structure zpc_Proc (ι κ : Type*) where
  /-- `X^{ab} = ⟨R₁^a A R₂^b⟩ - ⟨M^A_{ab,σ}⟩` -/
  X : ι → ℝ → ℂ
  /-- the martingale part of `X` -/
  MX : ι → ℝ → ℂ
  /-- the drift of `X` -/
  DX : ι → ℝ → ℂ
  /-- the linear coefficient `⟨M^I_σ⟩` of the drift of `X` -/
  cfX : ι → ℝ → ℂ
  /-- `⟨M^A_σ⟩` -/
  MA : ι → ℝ → ℂ
  /-- `⟨R₁² A R₂⟩` (constellation of `k`) -/
  QX₁ : ι → ℝ → ℂ
  /-- `⟨R₁ A R₂²⟩` -/
  QX₂ : ι → ℝ → ℂ
  /-- bracket density of `Re` of the martingale part of `X` -/
  brkXre : ι → ℝ → ℝ
  /-- bracket density of `Im` of the martingale part of `X` -/
  brkXim : ι → ℝ → ℝ
  /-- the `I`-chain constellation of `k` -/
  yX : ι → κ
  /-- `Y^{ab} = ⟨R₁^a R₂^b⟩ - ⟨M^I_{ab,σ}⟩` -/
  Y : κ → ℝ → ℂ
  /-- the martingale part of `Y` -/
  MY : κ → ℝ → ℂ
  /-- the drift of `Y` -/
  DY : κ → ℝ → ℂ
  /-- the coefficient `⟨M^I_σ⟩` (the drift is `2 cfY · Y + …`) -/
  cfY : κ → ℝ → ℂ
  /-- `⟨R₁² R₂⟩` -/
  QY₁ : κ → ℝ → ℂ
  /-- `⟨R₁ R₂²⟩` -/
  QY₂ : κ → ℝ → ℂ
  /-- bracket density of `Re` of the martingale part of `Y` -/
  brkYre : κ → ℝ → ℝ
  /-- bracket density of `Im` of the martingale part of `Y` -/
  brkYim : κ → ℝ → ℝ
  /-- `Z = Re⟨Im R₁ A Im R₂ Aᴴ⟩` -/
  Z : ℝ → ℝ
  /-- the martingale part of `Z` (`Z = Z₀ + MZ + ∫ DZ`) -/
  MZ : ℝ → ℝ
  /-- the drift of `Z` -/
  DZ : ℝ → ℝ
  /-- bracket density of `Z` -/
  brkZ : ℝ → ℝ
  /-- `⟨Im R₁ A Im R₂ Aᴴ R₁⟩` -/
  V₁ : ℝ → ℂ
  /-- `⟨Im R₁ A Im R₂ R₂ Aᴴ⟩` (middle form) -/
  V₂ : ℝ → ℂ
  /-- the cross terms of the `Z` drift in CEH (7.2) (`zgl_cross`) -/
  cross : ℝ → ℂ
  /-- tube `W₁ = ⟨R₁⟩ - m₁` -/
  W₁ : ℝ → ℂ
  /-- tube `W₂ = ⟨R₂⟩ - m₂` -/
  W₂ : ℝ → ℂ
  /-- `‖⟨Im R₁⟩‖` -/
  imR₁ : ℝ → ℝ
  /-- `‖⟨Im R₂⟩‖` -/
  imR₂ : ℝ → ℝ
  /-- `‖⟨Im R₁ Im R₂⟩‖` -/
  TI : ℝ → ℝ

/-- **The pathwise hypotheses** of the path core (one sample path on the good event). Each
field names its source in the docstring of `ZigPathCoreClosure`. All bounds are on `[0, s]`. -/
structure zpc_Hyp {ι κ : Type*} (D : zpc_Proc ι κ) : Prop where
  /-- regularity of the processes -/
  contX : ∀ k, ContinuousOn (D.X k) (Icc 0 G.s)
  contY : ∀ j, ContinuousOn (D.Y j) (Icc 0 G.s)
  contZ : ContinuousOn D.Z (Icc 0 G.s)
  contCfX : ∀ k, ContinuousOn (D.cfX k) (Icc 0 G.s)
  contCfY : ∀ j, ContinuousOn (D.cfY j) (Icc 0 G.s)
  intDX : ∀ k, IntervalIntegrable (D.DX k) volume 0 G.s
  intDY : ∀ j, IntervalIntegrable (D.DY j) volume 0 G.s
  intDZ : IntervalIntegrable D.DZ volume 0 G.s
  /-- initial values (`R_{i,0} = M_i`; `Z_0 = chainP ≤ π² ρ₁ρ₂ s₂(0)²`) -/
  X0 : ∀ k, D.X k 0 = 0
  Y0 : ∀ j, D.Y j 0 = 0
  Z0 : |D.Z 0| ≤ Real.pi ^ 2 * G.UZ
  /-- semimartingale decompositions -/
  decX : ∀ k, ∀ t ∈ Icc 0 G.s, D.X k t = D.MX k t + ∫ r in (0 : ℝ)..t, D.DX k r
  decY : ∀ j, ∀ t ∈ Icc 0 G.s, D.Y j t = D.MY j t + ∫ r in (0 : ℝ)..t, D.DY j r
  decZ : ∀ t ∈ Icc 0 G.s, D.Z t = D.Z 0 + D.MZ t + ∫ r in (0 : ℝ)..t, D.DZ r
  /-- linear coefficients -/
  cfX_le : ∀ k, ∀ r ∈ Icc 0 G.s, ‖D.cfX k r‖ ≤ (G.c₁ / G.e₁ r + G.c₂ / G.e₂ r) / 2
  cfY_le : ∀ j, ∀ r ∈ Icc 0 G.s, ‖D.cfY j r‖ ≤ (G.c₁ / G.e₁ r + G.c₂ / G.e₂ r) / 2
  /-- drift identities, as bounds on the remainder after the linear term -/
  driftX : ∀ k, ∀ r ∈ Icc 0 G.s, ‖D.DX k r - D.cfX k r * D.X k r‖ ≤
    ‖D.MA k r‖ * ‖D.Y (D.yX k) r‖ + ‖D.X k r‖ * ‖D.Y (D.yX k) r‖ +
      ‖D.W₁ r‖ * ‖D.QX₁ k r‖ + ‖D.W₂ r‖ * ‖D.QX₂ k r‖
  driftY : ∀ j, ∀ r ∈ Icc 0 G.s, ‖D.DY j r - 2 * D.cfY j r * D.Y j r‖ ≤
    ‖D.Y j r‖ ^ 2 + ‖D.W₁ r‖ * ‖D.QY₁ j r‖ + ‖D.W₂ r‖ * ‖D.QY₂ j r‖
  driftZ : ∀ r ∈ Icc 0 G.s, |D.DZ r| ≤
    (‖D.W₁ r‖ / G.e₁ r + ‖D.W₂ r‖ / G.e₂ r) * |D.Z r| + 2 * ‖D.W₁ r‖ * ‖D.V₁ r‖ +
      2 * ‖D.W₂ r‖ * ‖D.V₂ r‖ + ‖D.cross r‖
  /-- uniform bound `|⟨M^A_σ⟩| ≤ C₅₆ √chainP ≤ C₅₆ π √(ρ₁ρ₂) s₂(σ) ≤ C₅₆ π √(ρ₁ρ₂) S` -/
  MA_le : ∀ k, ∀ r ∈ Icc 0 G.s, ‖D.MA k r‖ ≤ p.Cm * Real.pi * Real.sqrt (G.ρ₁ * G.ρ₂) * G.S
  /-- the cross terms are four products of factors, each a fixed combination (coefficients
  `¼`, `½`) of the four chains `⟨R₁^a A R₂^b⟩ = X^{ab} + ⟨M^A_{ab}⟩` -/
  cross_le : ∀ r ∈ Icc 0 G.s, ∀ x : ℝ, (∀ k, ‖D.X k r‖ + ‖D.MA k r‖ ≤ x) →
    ‖D.cross r‖ ≤ 4 * x ^ 2
  /-- bounds on `⟨R₁² A R₂⟩` and `⟨R₁ A R₂²⟩` by `|Z|` and `|⟨Im Rᵢ⟩|` -/
  QX₁_le : ∀ k, ∀ r ∈ Icc 0 G.s, ‖D.QX₁ k r‖ ≤
    (G.e₁ r)⁻¹ * Real.sqrt (G.e₂ r)⁻¹ * Real.sqrt (D.imR₁ r) * Real.sqrt |D.Z r|
  QX₂_le : ∀ k, ∀ r ∈ Icc 0 G.s, ‖D.QX₂ k r‖ ≤
    (G.e₂ r)⁻¹ * Real.sqrt (G.e₁ r)⁻¹ * Real.sqrt (D.imR₂ r) * Real.sqrt |D.Z r|
  /-- bounds on `⟨R₁² R₂⟩` and `⟨R₁ R₂²⟩` by `|⟨Im Rᵢ⟩|` -/
  QY₁_le : ∀ j, ∀ r ∈ Icc 0 G.s, ‖D.QY₁ j r‖ ≤ D.imR₁ r / (G.e₁ r * G.e₂ r)
  QY₂_le : ∀ j, ∀ r ∈ Icc 0 G.s, ‖D.QY₂ j r‖ ≤ D.imR₂ r / (G.e₁ r * G.e₂ r)
  /-- bounds on `V₁` and its index-2 middle form `V₂` by `|Z|` -/
  V₁_le : ∀ r ∈ Icc 0 G.s, ‖D.V₁ r‖ ≤ |D.Z r| / G.e₁ r
  V₂_le : ∀ r ∈ Icc 0 G.s, ‖D.V₂ r‖ ≤ |D.Z r| / G.e₂ r
  /-- tube (`FlowTube`, exponent `ζ`: `Tz = N^ζ`) -/
  W₁_le : ∀ r ∈ Icc 0 G.s, ‖D.W₁ r‖ ≤ p.Tz / (G.N * G.e₁ r)
  W₂_le : ∀ r ∈ Icc 0 G.s, ‖D.W₂ r‖ ≤ p.Tz / (G.N * G.e₂ r)
  imR₁_le : ∀ r ∈ Icc 0 G.s, D.imR₁ r ≤ 3 / 2 * G.c₁
  imR₂_le : ∀ r ∈ Icc 0 G.s, D.imR₂ r ≤ 3 / 2 * G.c₂
  /-- min form on the tube: `‖⟨Im R₁ Im R₂⟩‖ ≤ (3/2) min (c₁/η₂) (c₂/η₁)` -/
  TI_le₁ : ∀ r ∈ Icc 0 G.s, D.TI r ≤ 3 / 2 * (G.c₁ / G.e₂ r)
  TI_le₂ : ∀ r ∈ Icc 0 G.s, D.TI r ≤ 3 / 2 * (G.c₂ / G.e₁ r)
  /-- brackets of `X` -/
  brkXre_nonneg : ∀ k, ∀ r ∈ Icc 0 G.s, 0 ≤ D.brkXre k r
  brkXre_le : ∀ k, ∀ r ∈ Icc 0 G.s, D.brkXre k r ≤
    2 / G.N ^ 2 * ((G.e₁ r)⁻¹ ^ 3 * (G.e₂ r)⁻¹ + (G.e₁ r)⁻¹ * (G.e₂ r)⁻¹ ^ 3) * |D.Z r|
  brkXim_nonneg : ∀ k, ∀ r ∈ Icc 0 G.s, 0 ≤ D.brkXim k r
  brkXim_le : ∀ k, ∀ r ∈ Icc 0 G.s, D.brkXim k r ≤
    2 / G.N ^ 2 * ((G.e₁ r)⁻¹ ^ 3 * (G.e₂ r)⁻¹ + (G.e₁ r)⁻¹ * (G.e₂ r)⁻¹ ^ 3) * |D.Z r|
  /-- brackets of `Y` -/
  brkYre_nonneg : ∀ j, ∀ r ∈ Icc 0 G.s, 0 ≤ D.brkYre j r
  brkYre_le : ∀ j, ∀ r ∈ Icc 0 G.s, D.brkYre j r ≤
    2 / G.N ^ 2 * ((G.e₁ r)⁻¹ ^ 3 * (G.e₂ r)⁻¹ + (G.e₁ r)⁻¹ * (G.e₂ r)⁻¹ ^ 3) * D.TI r
  brkYim_nonneg : ∀ j, ∀ r ∈ Icc 0 G.s, 0 ≤ D.brkYim j r
  brkYim_le : ∀ j, ∀ r ∈ Icc 0 G.s, D.brkYim j r ≤
    2 / G.N ^ 2 * ((G.e₁ r)⁻¹ ^ 3 * (G.e₂ r)⁻¹ + (G.e₁ r)⁻¹ * (G.e₂ r)⁻¹ ^ 3) * D.TI r
  /-- bracket of `Z` -/
  brkZ_nonneg : ∀ r ∈ Icc 0 G.s, 0 ≤ D.brkZ r
  brkZ_le : ∀ r ∈ Icc 0 G.s, D.brkZ r ≤
    2 / G.N * ((G.e₁ r)⁻¹ ^ 2 + (G.e₂ r)⁻¹ ^ 2) * D.Z r ^ 2
  /-- martingale controls (`MartGood` from `ZigTail`), on the `P`-dyadic grid -/
  martXre : ∀ k, ∀ ℓ ≤ p.Lg, ∀ t ∈ Set.Icc 0 G.s,
    (∫ r in Set.Ioc 0 t, D.brkXre k r) ≤ zpc_bX G p ℓ → |(D.MX k t).re| < zpc_aX G p ℓ
  martXim : ∀ k, ∀ ℓ ≤ p.Lg, ∀ t ∈ Set.Icc 0 G.s,
    (∫ r in Set.Ioc 0 t, D.brkXim k r) ≤ zpc_bX G p ℓ → |(D.MX k t).im| < zpc_aX G p ℓ
  martYre : ∀ j, ∀ ℓ ≤ p.Lg, ∀ t ∈ Set.Icc 0 G.s,
    (∫ r in Set.Ioc 0 t, D.brkYre j r) ≤ zpc_bY G ℓ → |(D.MY j t).re| < zpc_aY G p ℓ
  martYim : ∀ j, ∀ ℓ ≤ p.Lg, ∀ t ∈ Set.Icc 0 G.s,
    (∫ r in Set.Ioc 0 t, D.brkYim j r) ≤ zpc_bY G ℓ → |(D.MY j t).im| < zpc_aY G p ℓ
  martZ : ∀ t ∈ Set.Icc 0 G.s,
    (∫ r in Set.Ioc 0 t, D.brkZ r) ≤ zpc_bZ G p → |D.MZ t| < zpc_aZ G p

/-- **The numeric hypotheses** (the assembly discharges them for `N ≥ N₀`). -/
structure zpc_Small : Prop where
  lam_nonneg : 0 ≤ p.lam
  Tz_nonneg : 0 ≤ p.Tz
  Cm_nonneg : 0 ≤ p.Cm
  θX_pos : 0 < p.θX
  θY_pos : 0 < p.θY
  θZ_pos : 0 < p.θZ
  /-- the grid covers `[P_s, P_0]` -/
  grid : G.P 0 ≤ 2 ^ p.Lg * G.P G.s
  /-- the logarithmic loss of the two-height Grönwall -/
  logP : Real.log (G.P 0 / G.P G.s) ≤ p.Lmax
  /-- closing inequality of `Y` (the binding one: `3 N^ζ (1 + L) < N^{2ξ}`) -/
  closeY : (1 + p.Lmax) * zpc_KY G p < p.θY
  /-- closing inequality of `X` -/
  closeX : (1 + p.Lmax / 2) * zpc_KX G p < p.θX
  /-- closing inequality of `Z` (`π²(1 + 8 s C₅₆²) + o(1) ≤ N^{ξ/2}`) -/
  closeZ : zpc_KZ G p ≤ p.βZ
  /-- `N^{ξ/2} < N^ξ` -/
  βZ_lt : p.βZ < p.θZ

end BlockBand.Native.CEH.ETH
