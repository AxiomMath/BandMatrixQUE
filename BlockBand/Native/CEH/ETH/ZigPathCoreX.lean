module

public import BlockBand.Native.CEH.ETH.ZigPathCore

/-!
# CEH ETH, two-resolvent zig, path core: the `X` step

The improved bound on the fluctuation `X` of the `A`-chain, given the thresholds of `X`, `Y`, `Z`.
Deterministic, on one sample path, with data and hypotheses `zpc_Geom`, `zpc_Par`, `zpc_Proc`,
`zpc_Hyp`, `zpc_Small`; the only measure is Lebesgue measure on `ℝ`.

* `zpc_brkX_integral_le`: if `|Z| ≤ θZ U_Z` on `[0, t]`,
  `∫_{(0,t]} brk_X ≤ θZ U_Z ℓ₂ / (N² P_t)`.
* `zpc_martX_le`: then `‖M_X(t)‖ ≤ 2 lam √(2 θZ ℓ₂/N) U_X(t)` (grid cell, `zpc_bX`, `zpc_aX`).
* `zpc_driftX_le`: if the thresholds of `X`, `Y`, `Z` hold on `[0, T]`, then on `[0, T]`
  `‖∫_0^t (D_X - a X)‖ ≤ (Cm θY/√(Nρ₁ρ₂) + θXθY/(2N gm)
    + Tz √(3θZ/2)(1/√(Nc₁η₁) + 1/√(Nc₂η₂))) U_X(t)`
  (the `⟨M^A⟩·Y`, `X·Y` and the two tube terms `W₁⟨R₁²AR₂⟩`, `W₂⟨R₁AR₂²⟩`).
* `zpc_stepX`: then `‖X_k(t)‖ ≤ (1 + Lmax/2) K_X U_X(t)` on `[0, T]` (two-height Grönwall
  `norm_le_twoHeight_A`, `k = 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Set MeasureTheory intervalIntegral
open BlockBand.Native.CEH.Zig

/-!
## Scalar comparisons
-/

/-- The tube term `W₁⟨R₁²AR₂⟩` (bounded by `QX₁_le`) in integrable form:
`Tz/(N e) · (e⁻¹ √(e')⁻¹ A B) = (Tz A B/(N c)) · (c/(e² √e'))`. -/
theorem zpc_tubeX_eq {Tz N c e e' A B : ℝ} (hN : 0 < N) (hc : 0 < c) (he : 0 < e)
    (he' : 0 < e') :
    Tz / (N * e) * (e⁻¹ * Real.sqrt e'⁻¹ * A * B) =
      Tz * A * B / (N * c) * (c / (e ^ 2 * Real.sqrt e')) := by
  have := Real.sqrt_pos.2 he'
  rw [Real.sqrt_inv]
  field_simp

/-- The same tube term after integration, compared with the unit `U_X`:
`Tz √(3c/2) √(θZ ρρ S²)/(N c) · 1/(e √e') ≤ Tz √(3θZ/2)/√(N c η) · √ρρ S/√(N e e')`
for `η ≤ e`. -/
theorem zpc_tubeX_cmp {Tz θZ N c η e e' rr S : ℝ} (hTz : 0 ≤ Tz) (hθ : 0 ≤ θZ) (hN : 0 < N)
    (hc : 0 < c) (hη : 0 < η) (he' : 0 < e') (hrr : 0 ≤ rr) (hS : 0 ≤ S) (hηe : η ≤ e) :
    Tz * Real.sqrt (3 / 2 * c) * Real.sqrt (θZ * (rr * S ^ 2)) / (N * c) *
        (1 / (e * Real.sqrt e')) ≤
      Tz * Real.sqrt (3 / 2 * θZ) * (1 / Real.sqrt (N * (c * η))) *
        (Real.sqrt rr * S / Real.sqrt (N * (e * e'))) := by
  have he : 0 < e := hη.trans_le hηe
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3 / 2) c, Real.sqrt_mul hθ,
    Real.sqrt_mul hrr, Real.sqrt_sq hS, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3 / 2) θZ,
    Real.sqrt_mul hN.le, Real.sqrt_mul hc.le, Real.sqrt_mul hN.le, Real.sqrt_mul he.le]
  have hsN := Real.mul_self_sqrt hN.le
  have hsc := Real.mul_self_sqrt hc.le
  have hse := Real.mul_self_sqrt he.le
  have hsηe : Real.sqrt η ≤ Real.sqrt e := Real.sqrt_le_sqrt hηe
  have p1 := Real.sqrt_pos.2 hN
  have p2 := Real.sqrt_pos.2 hc
  have p3 := Real.sqrt_pos.2 hη
  have p4 := Real.sqrt_pos.2 he
  have p5 := Real.sqrt_pos.2 he'
  set sN := Real.sqrt N
  set sc := Real.sqrt c
  set sη := Real.sqrt η
  set se := Real.sqrt e
  set se' := Real.sqrt e'
  set K := Tz * Real.sqrt (3 / 2) * Real.sqrt θZ * Real.sqrt rr * S with hK
  have hK0 : 0 ≤ K := by positivity
  rw [← hsN, ← hsc, ← hse]
  calc Tz * (Real.sqrt (3 / 2) * sc) * (Real.sqrt θZ * (Real.sqrt rr * S)) / (sN * sN * (sc * sc)) *
        (1 / (se * se * se'))
      = K * (1 / (sN * sN * sc * (se * se) * se')) := by rw [hK]; field_simp
    _ ≤ K * (1 / (sN * sN * sc * (sη * se) * se')) := by gcongr
    _ = Tz * (Real.sqrt (3 / 2) * Real.sqrt θZ) * (1 / (sN * (sc * sη))) *
        (Real.sqrt rr * S / (sN * (se * se'))) := by rw [hK]; field_simp

variable {ι κ : Type*} {G : zpc_Geom} {p : zpc_Par} {D : zpc_Proc ι κ}

/-!
## The bracket and martingale of `X`
-/

/-- **Bracket of `X`**: if `|Z| ≤ θZ U_Z` on `[0, t]`, then
`∫_{(0,t]} brk ≤ θZ U_Z ℓ₂ / (N² P_t)`. -/
theorem zpc_brkX_integral_le (hG : G.Valid) (hθZ : 0 ≤ p.θZ) {f : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Icc 0 G.s) (hf0 : ∀ r ∈ Icc 0 G.s, 0 ≤ f r)
    (hf : ∀ r ∈ Icc 0 G.s, f r ≤
      2 / G.N ^ 2 * ((G.e₁ r)⁻¹ ^ 3 * (G.e₂ r)⁻¹ + (G.e₁ r)⁻¹ * (G.e₂ r)⁻¹ ^ 3) * |D.Z r|)
    (hZ : ∀ r ∈ Icc 0 t, |D.Z r| ≤ p.θZ * G.UZ) :
    ∫ r in Ioc 0 t, f r ≤ p.θZ * G.UZ * G.ell2 / (G.N ^ 2 * G.P t) := by
  have hN := hG.N_pos
  have hts := ht.2
  have h1 : ∀ r ∈ Icc 0 t, 0 < G.e₁ r := fun r hr => hG.e₁_pos (hr.2.trans hts)
  have h2 : ∀ r ∈ Icc 0 t, 0 < G.e₂ r := fun r hr => hG.e₂_pos (hr.2.trans hts)
  have hc₁ := hG.c₁_pos
  have hc₂ := hG.c₂_pos
  have hUZ := hG.UZ_pos
  set a : ℝ := 2 * (p.θZ * G.UZ) with ha
  have ha0 : 0 ≤ a := by positivity
  have hcont : ContinuousOn (fun r => (1 / G.e₁ r ^ 2 + 1 / G.e₂ r ^ 2) /
      (G.N ^ 2 * G.P r)) (Icc 0 t) := by
    unfold zpc_Geom.e₁ zpc_Geom.e₂ zpc_Geom.P zigHeightProd
    fun_prop (disch := first
      | (intro r hr; have := h1 r hr; have := h2 r hr; unfold zpc_Geom.e₁ zpc_Geom.e₂ at *;
          positivity)
      | positivity)
  have hg : ContinuousOn (fun r => a * ((1 / G.e₁ r ^ 2 + 1 / G.e₂ r ^ 2) /
      (G.N ^ 2 * G.P r))) (Icc 0 t) := continuousOn_const.mul hcont
  refine (zpc_setIntegral_le ht.1 (fun r hr => hf0 r ⟨hr.1.le, hr.2.trans hts⟩)
    hg fun r hr => ?_).trans ?_
  · have hrs : r ∈ Icc 0 G.s := ⟨hr.1.le, hr.2.trans hts⟩
    have he₁ := h1 r ⟨hr.1.le, hr.2⟩
    have he₂ := h2 r ⟨hr.1.le, hr.2⟩
    calc f r ≤ 2 / G.N ^ 2 * ((G.e₁ r)⁻¹ ^ 3 * (G.e₂ r)⁻¹ + (G.e₁ r)⁻¹ * (G.e₂ r)⁻¹ ^ 3) *
          |D.Z r| := hf r hrs
      _ ≤ 2 / G.N ^ 2 * ((G.e₁ r)⁻¹ ^ 3 * (G.e₂ r)⁻¹ + (G.e₁ r)⁻¹ * (G.e₂ r)⁻¹ ^ 3) *
          (p.θZ * G.UZ) := by gcongr; exact hZ r ⟨hr.1.le, hr.2⟩
      _ = a * ((1 / G.e₁ r ^ 2 + 1 / G.e₂ r ^ 2) / (G.N ^ 2 * G.P r)) := by
          rw [ha, zpc_Geom.P_eq]
          field_simp
  · have I := integral_bracket_zigHeightProd_le hG.η₁_pos hc₁ hG.η₂_pos hc₂ hN ht.1 hts
    rw [intervalIntegral.integral_const_mul]
    refine (mul_le_mul_of_nonneg_left I ha0).trans ?_
    have he₁ : G.η₁ ≤ zigHeight G.η₁ G.c₁ G.s t := hG.η₁_le_e₁ hts
    have he₂ : G.η₂ ≤ zigHeight G.η₂ G.c₂ G.s t := hG.η₂_le_e₂ hts
    have hη₁ := hG.η₁_pos
    have hη₂ := hG.η₂_pos
    have hPt := hG.P_pos hts
    have k : 1 / (2 * G.c₁ * zigHeight G.η₁ G.c₁ G.s t) +
        1 / (2 * G.c₂ * zigHeight G.η₂ G.c₂ G.s t) ≤ G.ell2 / 2 := by
      unfold zpc_Geom.ell2
      have a1 : 1 / (2 * G.c₁ * zigHeight G.η₁ G.c₁ G.s t) ≤ 1 / (2 * G.c₁ * G.η₁) := by
        gcongr
      have a2 : 1 / (2 * G.c₂ * zigHeight G.η₂ G.c₂ G.s t) ≤ 1 / (2 * G.c₂ * G.η₂) := by
        gcongr
      have : 1 / (2 * G.c₁ * G.η₁) + 1 / (2 * G.c₂ * G.η₂) =
          (1 / (G.c₁ * G.η₁) + 1 / (G.c₂ * G.η₂)) / 2 := by field_simp
      linarith
    calc a * ((1 / (2 * G.c₁ * zigHeight G.η₁ G.c₁ G.s t) +
          1 / (2 * G.c₂ * zigHeight G.η₂ G.c₂ G.s t)) /
          (G.N ^ 2 * zigHeightProd G.η₁ G.c₁ G.η₂ G.c₂ G.s t))
        ≤ a * (G.ell2 / 2 / (G.N ^ 2 * G.P t)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right k (by positivity)) ha0
      _ = p.θZ * G.UZ * G.ell2 / (G.N ^ 2 * G.P t) := by rw [ha]; field_simp

/-- **Martingale part of `X`**: if `|Z| ≤ θZ U_Z` on `[0, t]`, then
`‖M_X(t)‖ ≤ 2 lam √(2 θZ ℓ₂/N) U_X(t)`. -/
theorem zpc_martX_le (hG : G.Valid) (hS : zpc_Small G p) (h : zpc_Hyp G p D) (k : ι) {t : ℝ}
    (ht : t ∈ Icc 0 G.s) (hZ : ∀ r ∈ Icc 0 t, |D.Z r| ≤ p.θZ * G.UZ) :
    ‖D.MX k t‖ ≤ 2 * p.lam * Real.sqrt (2 * p.θZ * G.ell2 / G.N) * G.UX t := by
  obtain ⟨ℓ, hℓ, hc1, hc2⟩ := hG.exists_cell hS.grid ht
  have hN := hG.N_pos
  have hh := hG.lvl_pos ℓ
  have hPt := hG.P_pos ht.2
  have hθZ := hS.θZ_pos
  have hUZ := hG.UZ_pos
  have hl2 := hG.ell2_pos
  have hb : p.θZ * G.UZ * G.ell2 / (G.N ^ 2 * G.P t) ≤ zpc_bX G p ℓ := by
    unfold zpc_bX
    gcongr
  have hre := h.martXre k ℓ hℓ t ht ((zpc_brkX_integral_le hG hθZ.le ht
    (h.brkXre_nonneg k) (h.brkXre_le k) hZ).trans hb)
  have him := h.martXim k ℓ hℓ t ht ((zpc_brkX_integral_le hG hθZ.le ht
    (h.brkXim_nonneg k) (h.brkXim_le k) hZ).trans hb)
  refine (zpc_norm_lt_of_parts hre him).le.trans ?_
  have hl := hS.lam_nonneg
  unfold zpc_aX
  rw [show 2 * p.lam * Real.sqrt (2 * p.θZ * G.ell2 / G.N) * G.UX t =
    2 * p.lam * (Real.sqrt (2 * p.θZ * G.ell2 / G.N) * G.UX t) by ring, ← mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hUX := hG.UX_pos ht.2
  have hR : 0 ≤ Real.sqrt (2 * p.θZ * G.ell2 / G.N) * G.UX t := by positivity
  rw [← Real.sqrt_sq hR]
  refine Real.sqrt_le_sqrt ?_
  have hρ := mul_pos hG.ρ₁_pos hG.ρ₂_pos
  have hsq : (Real.sqrt (2 * p.θZ * G.ell2 / G.N) * G.UX t) ^ 2 =
      2 * p.θZ * G.ell2 * G.UZ / (G.N ^ 2 * G.P t) := by
    unfold zpc_Geom.UX zpc_Geom.UZ
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hρ.le,
      Real.sq_sqrt (by positivity)]
    field_simp
  rw [hsq]
  unfold zpc_bX
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ p.θZ * G.UZ * G.ell2 * G.N ^ 2 := by positivity
  nlinarith

/-!
## The drift of `X`
-/

/-- **Drift remainder of `X`**: if the thresholds of `X`, `Y`, `Z` hold on `[0, T]`, then on
`[0, T]`, `‖∫_0^t (D_X - a X)‖ ≤ (Cm θY/√(Nρ₁ρ₂) + θXθY/(2N gm)
+ Tz √(3θZ/2)(1/√(Nc₁η₁) + 1/√(Nc₂η₂))) U_X(t)`. -/
theorem zpc_driftX_le (hG : G.Valid) (hS : zpc_Small G p) (h : zpc_Hyp G p D) {T : ℝ}
    (hT : T ∈ Icc 0 G.s) (hX : ∀ r ∈ Icc 0 T, ∀ k, ‖D.X k r‖ ≤ p.θX * G.UX r)
    (hY : ∀ r ∈ Icc 0 T, ∀ j, ‖D.Y j r‖ ≤ p.θY * G.UY r)
    (hZ : ∀ r ∈ Icc 0 T, |D.Z r| ≤ p.θZ * G.UZ) (k : ι) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖∫ r in (0 : ℝ)..t, (D.DX k r - D.cfX k r * D.X k r)‖ ≤
      (p.Cm * p.θY / Real.sqrt (G.N * (G.ρ₁ * G.ρ₂)) + p.θX * p.θY / (2 * G.N * G.gm) +
        p.Tz * Real.sqrt (3 / 2 * p.θZ) *
          (1 / Real.sqrt (G.N * (G.c₁ * G.η₁)) + 1 / Real.sqrt (G.N * (G.c₂ * G.η₂)))) *
        G.UX t := by
  have hN := hG.N_pos
  have hts : t ≤ G.s := ht.2.trans hT.2
  have h1 : ∀ r ∈ Icc 0 t, 0 < G.e₁ r := fun r hr => hG.e₁_pos (hr.2.trans hts)
  have h2 : ∀ r ∈ Icc 0 t, 0 < G.e₂ r := fun r hr => hG.e₂_pos (hr.2.trans hts)
  have hP : ∀ r ∈ Icc 0 t, 0 < G.P r := fun r hr => hG.P_pos (hr.2.trans hts)
  have hc₁ := hG.c₁_pos
  have hc₂ := hG.c₂_pos
  have hTz := hS.Tz_nonneg
  have hCm := hS.Cm_nonneg
  have hθX := hS.θX_pos
  have hθY := hS.θY_pos
  have hθZ := hS.θZ_pos
  have hρ := mul_pos hG.ρ₁_pos hG.ρ₂_pos
  have hS0 := hG.S_pos
  have hUZ := hG.UZ_pos
  set Dm : ℝ := p.Cm * Real.pi * Real.sqrt (G.ρ₁ * G.ρ₂) * G.S with hDm
  have hDm0 : 0 ≤ Dm := by have := Real.pi_pos; positivity
  set a₁ : ℝ := Dm * p.θY / G.N with ha₁
  set a₂ : ℝ := p.θX * p.θY * Real.sqrt (G.ρ₁ * G.ρ₂) * G.S / (G.N * Real.sqrt G.N) with ha₂
  set a₃ : ℝ := p.Tz * Real.sqrt (3 / 2 * G.c₁) * Real.sqrt (p.θZ * G.UZ) / (G.N * G.c₁)
    with ha₃
  set a₄ : ℝ := p.Tz * Real.sqrt (3 / 2 * G.c₂) * Real.sqrt (p.θZ * G.UZ) / (G.N * G.c₂)
    with ha₄
  have hsN := Real.sqrt_pos.2 hN
  have ha₁0 : 0 ≤ a₁ := by positivity
  have ha₂0 : 0 ≤ a₂ := by positivity
  have ha₃0 : 0 ≤ a₃ := by positivity
  have ha₄0 : 0 ≤ a₄ := by positivity
  have hsub : Icc 0 t ⊆ Icc 0 G.s := Icc_subset_Icc le_rfl hts
  have hcont₁ : ContinuousOn (fun r => 1 / G.P r) (Icc 0 t) :=
    continuousOn_const.div (zpc_Geom.continuousOn_P.mono hsub) fun r hr => (hP r hr).ne'
  have hcont₂ : ContinuousOn (fun r => 1 / (G.P r * Real.sqrt (G.P r))) (Icc 0 t) :=
    continuousOn_const.div ((zpc_Geom.continuousOn_P.mono hsub).mul
      (zpc_Geom.continuousOn_P.mono hsub).sqrt) fun r hr => by
        have := hP r hr; have := Real.sqrt_pos.2 this; positivity
  have hcont₃ : ContinuousOn (fun r => G.c₁ / (G.e₁ r ^ 2 * Real.sqrt (G.e₂ r))) (Icc 0 t) := by
    unfold zpc_Geom.e₁ zpc_Geom.e₂
    fun_prop (disch := first
      | (intro r hr; have := h1 r hr; have := h2 r hr; unfold zpc_Geom.e₁ zpc_Geom.e₂ at *;
          have := Real.sqrt_pos.2 (h2 r hr); positivity)
      | positivity)
  have hcont₄ : ContinuousOn (fun r => G.c₂ / (G.e₂ r ^ 2 * Real.sqrt (G.e₁ r))) (Icc 0 t) := by
    unfold zpc_Geom.e₁ zpc_Geom.e₂
    fun_prop (disch := first
      | (intro r hr; have := h1 r hr; have := h2 r hr; unfold zpc_Geom.e₁ zpc_Geom.e₂ at *;
          have := Real.sqrt_pos.2 (h1 r hr); positivity)
      | positivity)
  have hg : ContinuousOn (fun r => a₁ * (1 / G.P r) + a₂ * (1 / (G.P r * Real.sqrt (G.P r))) +
      a₃ * (G.c₁ / (G.e₁ r ^ 2 * Real.sqrt (G.e₂ r))) +
      a₄ * (G.c₂ / (G.e₂ r ^ 2 * Real.sqrt (G.e₁ r)))) (Icc 0 t) :=
    (((continuousOn_const.mul hcont₁).add (continuousOn_const.mul hcont₂)).add
      (continuousOn_const.mul hcont₃)).add (continuousOn_const.mul hcont₄)
  refine (zpc_norm_integral_le ht.1 hg fun r hr => ?_).trans ?_
  · have hrs : r ∈ Icc 0 G.s := ⟨hr.1, hr.2.trans hts⟩
    have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
    have he₁ := h1 r hr
    have he₂ := h2 r hr
    have hPr := hP r hr
    have hZr : Real.sqrt |D.Z r| ≤ Real.sqrt (p.θZ * G.UZ) := Real.sqrt_le_sqrt (hZ r hrT)
    have hQ₁ : ‖D.QX₁ k r‖ ≤ (G.e₁ r)⁻¹ * Real.sqrt (G.e₂ r)⁻¹ *
        Real.sqrt (3 / 2 * G.c₁) * Real.sqrt (p.θZ * G.UZ) := by
      refine (h.QX₁_le k r hrs).trans ?_
      gcongr
      exact h.imR₁_le r hrs
    have hQ₂ : ‖D.QX₂ k r‖ ≤ (G.e₂ r)⁻¹ * Real.sqrt (G.e₁ r)⁻¹ *
        Real.sqrt (3 / 2 * G.c₂) * Real.sqrt (p.θZ * G.UZ) := by
      refine (h.QX₂_le k r hrs).trans ?_
      gcongr
      exact h.imR₂_le r hrs
    calc ‖D.DX k r - D.cfX k r * D.X k r‖
        ≤ ‖D.MA k r‖ * ‖D.Y (D.yX k) r‖ + ‖D.X k r‖ * ‖D.Y (D.yX k) r‖ +
            ‖D.W₁ r‖ * ‖D.QX₁ k r‖ + ‖D.W₂ r‖ * ‖D.QX₂ k r‖ := h.driftX k r hrs
      _ ≤ Dm * (p.θY * G.UY r) + p.θX * G.UX r * (p.θY * G.UY r) +
            p.Tz / (G.N * G.e₁ r) * ((G.e₁ r)⁻¹ * Real.sqrt (G.e₂ r)⁻¹ *
              Real.sqrt (3 / 2 * G.c₁) * Real.sqrt (p.θZ * G.UZ)) +
            p.Tz / (G.N * G.e₂ r) * ((G.e₂ r)⁻¹ * Real.sqrt (G.e₁ r)⁻¹ *
              Real.sqrt (3 / 2 * G.c₂) * Real.sqrt (p.θZ * G.UZ)) := by
          have hY' := hY r hrT (D.yX k)
          have hX' := hX r hrT k
          have hMA := h.MA_le k r hrs
          have hW₁ := h.W₁_le r hrs
          have hW₂ := h.W₂_le r hrs
          have hUX := hG.UX_pos hrs.2
          gcongr
      _ = a₁ * (1 / G.P r) + a₂ * (1 / (G.P r * Real.sqrt (G.P r))) +
            a₃ * (G.c₁ / (G.e₁ r ^ 2 * Real.sqrt (G.e₂ r))) +
            a₄ * (G.c₂ / (G.e₂ r ^ 2 * Real.sqrt (G.e₁ r))) := by
          rw [zpc_tubeX_eq hN hc₁ he₁ he₂, zpc_tubeX_eq hN hc₂ he₂ he₁]
          have e1 : Dm * (p.θY * G.UY r) = a₁ * (1 / G.P r) := by
            rw [ha₁]; unfold zpc_Geom.UY; field_simp
          have e2 : p.θX * G.UX r * (p.θY * G.UY r) =
              a₂ * (1 / (G.P r * Real.sqrt (G.P r))) := by
            rw [ha₂]
            unfold zpc_Geom.UX zpc_Geom.UY
            rw [Real.sqrt_mul hN.le]
            have := Real.sqrt_pos.2 hPr
            field_simp
          rw [e1, e2]
  · have I1 : ∫ r in (0 : ℝ)..t, 1 / G.P r ≤
        1 / (Real.sqrt (G.c₁ * G.c₂) * Real.sqrt (G.P t)) :=
      zpc_integral_inv_P_le hG.η₁_pos hc₁ hG.η₂_pos hc₂ ht.1 hts
    have I2 : ∫ r in (0 : ℝ)..t, 1 / (G.P r * Real.sqrt (G.P r)) ≤
        1 / (2 * Real.sqrt (G.c₁ * G.c₂) * G.P t) :=
      zpc_integral_inv_P_sqrt_le hG.η₁_pos hc₁ hG.η₂_pos hc₂ ht.1 hts
    have I3 := zpc_integral_sq_mul_sqrt_le (s := G.s) hG.η₁_pos hc₁ hG.η₂_pos hc₂.le ht.1 hts
    have I4 := zpc_integral_sq_mul_sqrt_le (s := G.s) hG.η₂_pos hc₂ hG.η₁_pos hc₁.le ht.1 hts
    refine (zpc_integral_add4_le ht.1 hcont₁ hcont₂ hcont₃ hcont₄ ha₁0 ha₂0 ha₃0 ha₄0
      I1 I2 I3 I4).trans ?_
    have hPt := hP t ⟨ht.1, le_rfl⟩
    have he₁ := h1 t ⟨ht.1, le_rfl⟩
    have he₂ := h2 t ⟨ht.1, le_rfl⟩
    have hgm := hG.gm_le hts
    have hgm0 := hG.gm_pos
    have hA : Real.sqrt (G.c₁ * G.c₂) = Real.pi * Real.sqrt (G.ρ₁ * G.ρ₂) := hG.sqrt_c₁c₂
    have hA0 : 0 < Real.sqrt (G.c₁ * G.c₂) := Real.sqrt_pos.2 (by positivity)
    have hQ : 0 < Real.sqrt (G.P t) := Real.sqrt_pos.2 hPt
    have hsρ : 0 < Real.sqrt (G.ρ₁ * G.ρ₂) := Real.sqrt_pos.2 hρ
    -- the `⟨M^A⟩·Y` term
    have k1 : a₁ * (1 / (Real.sqrt (G.c₁ * G.c₂) * Real.sqrt (G.P t))) =
        p.Cm * p.θY / Real.sqrt (G.N * (G.ρ₁ * G.ρ₂)) * G.UX t := by
      rw [ha₁, hDm, hA]
      unfold zpc_Geom.UX
      rw [Real.sqrt_mul hN.le, Real.sqrt_mul hN.le]
      have hsN2 := Real.mul_self_sqrt hN.le
      have := Real.pi_pos
      set sN := Real.sqrt G.N
      rw [← hsN2]
      field_simp
    -- the `X·Y` term
    have k2 : a₂ * (1 / (2 * Real.sqrt (G.c₁ * G.c₂) * G.P t)) ≤
        p.θX * p.θY / (2 * G.N * G.gm) * G.UX t := by
      rw [ha₂]
      unfold zpc_Geom.UX
      rw [Real.sqrt_mul hN.le]
      set Q := Real.sqrt (G.P t) with hQdef
      have eP : G.P t = Q * Q := (Real.mul_self_sqrt hPt.le).symm
      set K := p.θX * p.θY * Real.sqrt (G.ρ₁ * G.ρ₂) * G.S / (2 * G.N * Real.sqrt G.N) with hK
      have hK0 : 0 ≤ K := by positivity
      calc p.θX * p.θY * Real.sqrt (G.ρ₁ * G.ρ₂) * G.S / (G.N * Real.sqrt G.N) *
            (1 / (2 * Real.sqrt (G.c₁ * G.c₂) * G.P t))
          = K * (1 / (Real.sqrt (G.c₁ * G.c₂) * Q * Q)) := by
            rw [hK, eP]; field_simp
        _ ≤ K * (1 / (G.gm * Q)) := by
            gcongr
        _ = p.θX * p.θY / (2 * G.N * G.gm) *
            (Real.sqrt (G.ρ₁ * G.ρ₂) * G.S / (Real.sqrt G.N * Q)) := by
            rw [hK]; field_simp
    -- the tube terms
    have k3 : a₃ * (1 / (zigHeight G.η₁ G.c₁ G.s t * Real.sqrt (zigHeight G.η₂ G.c₂ G.s t))) ≤
        p.Tz * Real.sqrt (3 / 2 * p.θZ) * (1 / Real.sqrt (G.N * (G.c₁ * G.η₁))) * G.UX t := by
      rw [ha₃]
      unfold zpc_Geom.UX
      rw [zpc_Geom.P_eq]
      exact zpc_tubeX_cmp hTz hθZ.le hN hc₁ hG.η₁_pos he₂ hρ.le hS0.le (hG.η₁_le_e₁ hts)
    have k4 : a₄ * (1 / (zigHeight G.η₂ G.c₂ G.s t * Real.sqrt (zigHeight G.η₁ G.c₁ G.s t))) ≤
        p.Tz * Real.sqrt (3 / 2 * p.θZ) * (1 / Real.sqrt (G.N * (G.c₂ * G.η₂))) * G.UX t := by
      rw [ha₄]
      unfold zpc_Geom.UX
      rw [zpc_Geom.P_eq, mul_comm (G.e₁ t)]
      exact zpc_tubeX_cmp hTz hθZ.le hN hc₂ hG.η₂_pos he₁ hρ.le hS0.le (hG.η₂_le_e₂ hts)
    have : (p.Cm * p.θY / Real.sqrt (G.N * (G.ρ₁ * G.ρ₂)) + p.θX * p.θY / (2 * G.N * G.gm) +
        p.Tz * Real.sqrt (3 / 2 * p.θZ) *
          (1 / Real.sqrt (G.N * (G.c₁ * G.η₁)) + 1 / Real.sqrt (G.N * (G.c₂ * G.η₂)))) *
        G.UX t =
        p.Cm * p.θY / Real.sqrt (G.N * (G.ρ₁ * G.ρ₂)) * G.UX t +
          p.θX * p.θY / (2 * G.N * G.gm) * G.UX t +
          p.Tz * Real.sqrt (3 / 2 * p.θZ) * (1 / Real.sqrt (G.N * (G.c₁ * G.η₁))) * G.UX t +
          p.Tz * Real.sqrt (3 / 2 * p.θZ) * (1 / Real.sqrt (G.N * (G.c₂ * G.η₂))) * G.UX t := by
      ring
    rw [this]
    linarith

/-!
## The step
-/

/-- **The `X` step.** If the thresholds of `X`, `Y`, `Z` hold on `[0, T]`, then on `[0, T]`
`‖X_k(t)‖ ≤ (1 + Lmax/2) K_X U_X(t)`. -/
theorem zpc_stepX (hG : G.Valid) (hS : zpc_Small G p) (h : zpc_Hyp G p D) {T : ℝ}
    (hT : T ∈ Icc 0 G.s) (hX : ∀ r ∈ Icc 0 T, ∀ k, ‖D.X k r‖ ≤ p.θX * G.UX r)
    (hY : ∀ r ∈ Icc 0 T, ∀ j, ‖D.Y j r‖ ≤ p.θY * G.UY r)
    (hZ : ∀ r ∈ Icc 0 T, |D.Z r| ≤ p.θZ * G.UZ) (k : ι) :
    ∀ t ∈ Icc 0 T, ‖D.X k t‖ ≤ (1 + p.Lmax / 2) * zpc_KX G p * G.UX t := by
  have hN := hG.N_pos
  have hTs := hT.2
  have hsub : Icc 0 T ⊆ Icc 0 G.s := Icc_subset_Icc le_rfl hTs
  set E : ℝ → ℂ := fun t => D.X k t - ∫ u in (0 : ℝ)..t, D.cfX k u * D.X k u with hE
  have hKX : 0 ≤ zpc_KX G p := by
    have := hS.lam_nonneg
    have := hS.Tz_nonneg
    have := hS.Cm_nonneg
    have := hS.θX_pos
    have := hS.θY_pos
    have := hG.gm_pos
    unfold zpc_KX
    positivity
  have hgr := norm_le_twoHeight_A (E := E)
    (K := zpc_KX G p * (Real.sqrt (G.ρ₁ * G.ρ₂) * G.S)) hG.η₁_pos hG.c₁_pos.le
    hG.η₂_pos hG.c₂_pos.le hN hTs ((h.contX k).mono hsub) ((h.contCfX k).mono hsub)
    (fun t _ => by simp only [hE, sub_add_cancel]) (fun u hu => h.cfX_le k u (hsub hu))
    (fun t ht => by
      have hts : t ∈ Icc 0 G.s := hsub ht
      have hDi : IntervalIntegrable (D.DX k) volume 0 t :=
        (h.intDX k).mono_set (by
          rw [uIcc_of_le hG.s_nonneg, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl hts.2)
      have hci : IntervalIntegrable (fun u => D.cfX k u * D.X k u) volume 0 t :=
        (((h.contCfX k).mono (Icc_subset_Icc le_rfl hts.2)).mul
          ((h.contX k).mono (Icc_subset_Icc le_rfl hts.2))).intervalIntegrable_of_Icc ht.1
      have e : E t = D.MX k t + ∫ r in (0 : ℝ)..t, (D.DX k r - D.cfX k r * D.X k r) := by
        rw [intervalIntegral.integral_sub hDi hci, hE]
        simp only
        rw [h.decX k t hts]
        ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have m := zpc_martX_le hG hS h k hts fun r hr => hZ r ⟨hr.1, hr.2.trans ht.2⟩
      have d := zpc_driftX_le hG hS h hT hX hY hZ k ht
      have : zpc_KX G p * (Real.sqrt (G.ρ₁ * G.ρ₂) * G.S) /
          Real.sqrt (G.N * zigHeightProd G.η₁ G.c₁ G.η₂ G.c₂ G.s t) =
          2 * p.lam * Real.sqrt (2 * p.θZ * G.ell2 / G.N) * G.UX t +
            (p.Cm * p.θY / Real.sqrt (G.N * (G.ρ₁ * G.ρ₂)) +
              p.θX * p.θY / (2 * G.N * G.gm) + p.Tz * Real.sqrt (3 / 2 * p.θZ) *
                (1 / Real.sqrt (G.N * (G.c₁ * G.η₁)) + 1 / Real.sqrt (G.N * (G.c₂ * G.η₂)))) *
              G.UX t := by
        unfold zpc_KX zpc_Geom.UX zpc_Geom.P
        ring
      rw [this]
      exact add_le_add m d)
  intro t ht
  refine (hgr t ht).trans ?_
  have hPt := hG.P_pos (ht.2.trans hTs)
  have hP0 := hG.P_pos hG.s_nonneg
  have hPs := hG.P_pos le_rfl
  have hlog : Real.log (G.P 0 / G.P t) ≤ p.Lmax := by
    refine le_trans ?_ hS.logP
    exact Real.log_le_log (by positivity)
      (div_le_div_of_nonneg_left hP0.le hPs (hG.P_anti (ht.2.trans hTs) le_rfl))
  have hUX := hG.UX_pos (ht.2.trans hTs)
  change zpc_KX G p * (Real.sqrt (G.ρ₁ * G.ρ₂) * G.S) / Real.sqrt (G.N * G.P t) *
    (1 + Real.log (G.P 0 / G.P t) / 2) ≤ _
  rw [show zpc_KX G p * (Real.sqrt (G.ρ₁ * G.ρ₂) * G.S) / Real.sqrt (G.N * G.P t) =
    zpc_KX G p * G.UX t by unfold zpc_Geom.UX; ring,
    show (1 + p.Lmax / 2) * zpc_KX G p * G.UX t =
    zpc_KX G p * G.UX t * (1 + p.Lmax / 2) by ring]
  gcongr

end BlockBand.Native.CEH.ETH
