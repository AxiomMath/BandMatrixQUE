module

public import BlockBand.Native.CEH.ETH.ZigPathCore

/-!
# CEH ETH, two-resolvent zig, path core: the `Z` step

The improved bound on the imaginary chain `Z = Re⟨Im R₁ A Im R₂ Aᴴ⟩`, given the thresholds of `X`
and `Z`. Deterministic, on one sample path, with data and hypotheses `zpc_Geom`, `zpc_Par`,
`zpc_Proc`, `zpc_Hyp`, `zpc_Small`; the only measure is Lebesgue measure on `ℝ`. There is no
Grönwall step for `Z` (no linear term in variance time).

* `zpc_brkZ_integral_le` (from the field `zpc_Hyp.brkZ_le`): if `|Z| ≤ θZ U_Z` on `[0, t]`, `∫_{(0,t]} brk_Z ≤ zpc_bZ`.
* `zpc_martZ_le`: then `|M_Z(t)| ≤ lam θZ √(2ℓ₂/N) U_Z`.
* `zpc_driftZ_le`: if the thresholds of `X` and `Z` hold on `[0, T]`, then on `[0, T]`
  `|∫_0^t D_Z| ≤ (3 Tz θZ ℓ₂/N + 8 s Cm² π² + 8 θX²/(N gm)) U_Z` (tube terms with the fields
  `V₁_le`, `V₂_le` of `zpc_Hyp`; cross terms with `cross_le` and `(a + b)² ≤ 2a² + 2b²`).
* `zpc_stepZ`: then `|Z(t)| ≤ K_Z U_Z ≤ βZ U_Z` on `[0, T]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Set MeasureTheory intervalIntegral
open BlockBand.Native.CEH.Zig

variable {ι κ : Type*} {G : zpc_Geom} {p : zpc_Par} {D : zpc_Proc ι κ}

/-- **Bracket of `Z`**: if `|Z| ≤ θZ U_Z` on `[0, t]`, `∫_{(0,t]} brk_Z ≤ zpc_bZ`. -/
theorem zpc_brkZ_integral_le (hG : G.Valid) {t : ℝ} (ht : t ∈ Icc 0 G.s)
    (h : zpc_Hyp G p D) (hZ : ∀ r ∈ Icc 0 t, |D.Z r| ≤ p.θZ * G.UZ) :
    ∫ r in Ioc 0 t, D.brkZ r ≤ zpc_bZ G p := by
  have hN := hG.N_pos
  have hts := ht.2
  have h1 : ∀ r ∈ Icc 0 t, 0 < G.e₁ r := fun r hr => hG.e₁_pos (hr.2.trans hts)
  have h2 : ∀ r ∈ Icc 0 t, 0 < G.e₂ r := fun r hr => hG.e₂_pos (hr.2.trans hts)
  have hc₁ := hG.c₁_pos
  have hc₂ := hG.c₂_pos
  have hUZ := hG.UZ_pos
  set a₁ : ℝ := 2 * (p.θZ * G.UZ) ^ 2 / (G.N * G.c₁) with ha₁
  set a₂ : ℝ := 2 * (p.θZ * G.UZ) ^ 2 / (G.N * G.c₂) with ha₂
  have ha₁0 : 0 ≤ a₁ := by positivity
  have ha₂0 : 0 ≤ a₂ := by positivity
  have hcont₁ : ContinuousOn (fun r => G.c₁ / G.e₁ r ^ 2) (Icc 0 t) := by
    unfold zpc_Geom.e₁
    fun_prop (disch := first
      | (intro r hr; have := h1 r hr; unfold zpc_Geom.e₁ at *; positivity)
      | positivity)
  have hcont₂ : ContinuousOn (fun r => G.c₂ / G.e₂ r ^ 2) (Icc 0 t) := by
    unfold zpc_Geom.e₂
    fun_prop (disch := first
      | (intro r hr; have := h2 r hr; unfold zpc_Geom.e₂ at *; positivity)
      | positivity)
  have hg : ContinuousOn (fun r => a₁ * (G.c₁ / G.e₁ r ^ 2) + a₂ * (G.c₂ / G.e₂ r ^ 2))
      (Icc 0 t) := (continuousOn_const.mul hcont₁).add (continuousOn_const.mul hcont₂)
  refine (zpc_setIntegral_le ht.1 (fun r hr => h.brkZ_nonneg r ⟨hr.1.le, hr.2.trans hts⟩) hg
    fun r hr => ?_).trans ?_
  · have hrs : r ∈ Icc 0 G.s := ⟨hr.1.le, hr.2.trans hts⟩
    have he₁ := h1 r ⟨hr.1.le, hr.2⟩
    have he₂ := h2 r ⟨hr.1.le, hr.2⟩
    have hZ2 : D.Z r ^ 2 ≤ (p.θZ * G.UZ) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hZ r ⟨hr.1.le, hr.2⟩) 2
    calc D.brkZ r ≤ 2 / G.N * ((G.e₁ r)⁻¹ ^ 2 + (G.e₂ r)⁻¹ ^ 2) * D.Z r ^ 2 := h.brkZ_le r hrs
      _ ≤ 2 / G.N * ((G.e₁ r)⁻¹ ^ 2 + (G.e₂ r)⁻¹ ^ 2) * (p.θZ * G.UZ) ^ 2 := by gcongr
      _ = a₁ * (G.c₁ / G.e₁ r ^ 2) + a₂ * (G.c₂ / G.e₂ r ^ 2) := by
          rw [ha₁, ha₂]
          field_simp
  · have I1 := zpc_integral_inv_sq_le (s := G.s) hG.η₁_pos hc₁ ht.1 hts
    have I2 := zpc_integral_inv_sq_le (s := G.s) hG.η₂_pos hc₂ ht.1 hts
    refine (zpc_integral_add2_le ht.1 hcont₁ hcont₂ ha₁0 ha₂0 I1 I2).trans ?_
    have he₁ : G.η₁ ≤ zigHeight G.η₁ G.c₁ G.s t := hG.η₁_le_e₁ hts
    have he₂ : G.η₂ ≤ zigHeight G.η₂ G.c₂ G.s t := hG.η₂_le_e₂ hts
    have hη₁ := hG.η₁_pos
    have hη₂ := hG.η₂_pos
    have k1 : a₁ * (1 / zigHeight G.η₁ G.c₁ G.s t) ≤ a₁ * (1 / G.η₁) := by gcongr
    have k2 : a₂ * (1 / zigHeight G.η₂ G.c₂ G.s t) ≤ a₂ * (1 / G.η₂) := by gcongr
    have e : a₁ * (1 / G.η₁) + a₂ * (1 / G.η₂) = zpc_bZ G p := by
      rw [ha₁, ha₂]
      unfold zpc_bZ zpc_Geom.ell2
      field_simp
    linarith

/-- **Martingale part of `Z`**: if `|Z| ≤ θZ U_Z` on `[0, t]`,
`|M_Z(t)| ≤ lam θZ √(2ℓ₂/N) U_Z`. -/
theorem zpc_martZ_le (hG : G.Valid) (hS : zpc_Small G p) (h : zpc_Hyp G p D) {t : ℝ}
    (ht : t ∈ Icc 0 G.s) (hZ : ∀ r ∈ Icc 0 t, |D.Z r| ≤ p.θZ * G.UZ) :
    |D.MZ t| ≤ p.lam * p.θZ * Real.sqrt (2 * G.ell2 / G.N) * G.UZ := by
  have hlt := h.martZ t ht (zpc_brkZ_integral_le hG ht h hZ)
  refine hlt.le.trans (le_of_eq ?_)
  have hθZ := hS.θZ_pos
  have hUZ := hG.UZ_pos
  have hN := hG.N_pos
  have hl2 := hG.ell2_pos
  unfold zpc_aZ zpc_bZ
  rw [show 2 * p.θZ ^ 2 * G.UZ ^ 2 * G.ell2 / G.N = (p.θZ * G.UZ) ^ 2 * (2 * G.ell2 / G.N) by
    ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring

/-- **Drift of `Z`**: if the thresholds of `X` and `Z` hold on `[0, T]`, then on `[0, T]`
`|∫_0^t D_Z| ≤ (3 Tz θZ ℓ₂/N + 8 s Cm² π² + 8 θX²/(N gm)) U_Z`. -/
theorem zpc_driftZ_le (hG : G.Valid) (hS : zpc_Small G p) (h : zpc_Hyp G p D) {T : ℝ}
    (hT : T ∈ Icc 0 G.s) (hX : ∀ r ∈ Icc 0 T, ∀ k, ‖D.X k r‖ ≤ p.θX * G.UX r)
    (hZ : ∀ r ∈ Icc 0 T, |D.Z r| ≤ p.θZ * G.UZ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    |∫ r in (0 : ℝ)..t, D.DZ r| ≤
      (3 * p.Tz * p.θZ * G.ell2 / G.N + 8 * G.s * p.Cm ^ 2 * Real.pi ^ 2 +
        8 * p.θX ^ 2 / (G.N * G.gm)) * G.UZ := by
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
  have hθZ := hS.θZ_pos
  have hρ := mul_pos hG.ρ₁_pos hG.ρ₂_pos
  have hS0 := hG.S_pos
  have hUZ := hG.UZ_pos
  have hpi := Real.pi_pos
  set Dm : ℝ := p.Cm * Real.pi * Real.sqrt (G.ρ₁ * G.ρ₂) * G.S with hDm
  have hDm0 : 0 ≤ Dm := by positivity
  set a₁ : ℝ := 3 * p.Tz * p.θZ * G.UZ / (G.N * G.c₁) with ha₁
  set a₂ : ℝ := 3 * p.Tz * p.θZ * G.UZ / (G.N * G.c₂) with ha₂
  set a₃ : ℝ := 8 * p.Cm ^ 2 * Real.pi ^ 2 * G.UZ with ha₃
  set a₄ : ℝ := 8 * p.θX ^ 2 * G.UZ / G.N with ha₄
  have ha₁0 : 0 ≤ a₁ := by positivity
  have ha₂0 : 0 ≤ a₂ := by positivity
  have ha₃0 : 0 ≤ a₃ := by positivity
  have ha₄0 : 0 ≤ a₄ := by positivity
  have hsub : Icc 0 t ⊆ Icc 0 G.s := Icc_subset_Icc le_rfl hts
  have hcont₁ : ContinuousOn (fun r => G.c₁ / G.e₁ r ^ 2) (Icc 0 t) := by
    unfold zpc_Geom.e₁
    fun_prop (disch := first
      | (intro r hr; have := h1 r hr; unfold zpc_Geom.e₁ at *; positivity)
      | positivity)
  have hcont₂ : ContinuousOn (fun r => G.c₂ / G.e₂ r ^ 2) (Icc 0 t) := by
    unfold zpc_Geom.e₂
    fun_prop (disch := first
      | (intro r hr; have := h2 r hr; unfold zpc_Geom.e₂ at *; positivity)
      | positivity)
  have hcont₃ : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc 0 t) := continuousOn_const
  have hcont₄ : ContinuousOn (fun r => 1 / G.P r) (Icc 0 t) :=
    continuousOn_const.div (zpc_Geom.continuousOn_P.mono hsub) fun r hr => (hP r hr).ne'
  have hg : ContinuousOn (fun r => a₁ * (G.c₁ / G.e₁ r ^ 2) + a₂ * (G.c₂ / G.e₂ r ^ 2) +
      a₃ * 1 + a₄ * (1 / G.P r)) (Icc 0 t) :=
    (((continuousOn_const.mul hcont₁).add (continuousOn_const.mul hcont₂)).add
      (continuousOn_const.mul hcont₃)).add (continuousOn_const.mul hcont₄)
  refine (zpc_abs_integral_le ht.1 hg fun r hr => ?_).trans ?_
  · have hrs : r ∈ Icc 0 G.s := ⟨hr.1, hr.2.trans hts⟩
    have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
    have he₁ := h1 r hr
    have he₂ := h2 r hr
    have hPr := hP r hr
    have hZr := hZ r hrT
    have hW₁ := h.W₁_le r hrs
    have hW₂ := h.W₂_le r hrs
    have hV₁ : ‖D.V₁ r‖ ≤ p.θZ * G.UZ / G.e₁ r :=
      (h.V₁_le r hrs).trans (div_le_div_of_nonneg_right hZr he₁.le)
    have hV₂ : ‖D.V₂ r‖ ≤ p.θZ * G.UZ / G.e₂ r :=
      (h.V₂_le r hrs).trans (div_le_div_of_nonneg_right hZr he₂.le)
    have hUX := hG.UX_pos hrs.2
    have hcr : ‖D.cross r‖ ≤ 4 * (p.θX * G.UX r + Dm) ^ 2 :=
      h.cross_le r hrs _ fun k => add_le_add (hX r hrT k) (h.MA_le k r hrs)
    have hsq : 4 * (p.θX * G.UX r + Dm) ^ 2 ≤ a₃ * 1 + a₄ * (1 / G.P r) := by
      have e1 : (p.θX * G.UX r) ^ 2 = p.θX ^ 2 * G.UZ / G.N * (1 / G.P r) := by
        unfold zpc_Geom.UX zpc_Geom.UZ
        rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hρ.le, Real.sq_sqrt (by positivity)]
        field_simp
      have e2 : Dm ^ 2 = p.Cm ^ 2 * Real.pi ^ 2 * G.UZ := by
        rw [hDm]
        unfold zpc_Geom.UZ
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hρ.le]
        ring
      have h4 : 4 * (p.θX * G.UX r + Dm) ^ 2 ≤ 8 * (p.θX * G.UX r) ^ 2 + 8 * Dm ^ 2 := by
        nlinarith [sq_nonneg (p.θX * G.UX r - Dm)]
      rw [e1, e2] at h4
      refine h4.trans (le_of_eq ?_)
      rw [ha₃, ha₄]
      ring
    calc |D.DZ r| ≤ (‖D.W₁ r‖ / G.e₁ r + ‖D.W₂ r‖ / G.e₂ r) * |D.Z r| +
          2 * ‖D.W₁ r‖ * ‖D.V₁ r‖ + 2 * ‖D.W₂ r‖ * ‖D.V₂ r‖ + ‖D.cross r‖ := h.driftZ r hrs
      _ ≤ (p.Tz / (G.N * G.e₁ r) / G.e₁ r + p.Tz / (G.N * G.e₂ r) / G.e₂ r) * (p.θZ * G.UZ) +
          2 * (p.Tz / (G.N * G.e₁ r)) * (p.θZ * G.UZ / G.e₁ r) +
          2 * (p.Tz / (G.N * G.e₂ r)) * (p.θZ * G.UZ / G.e₂ r) +
          4 * (p.θX * G.UX r + Dm) ^ 2 := by gcongr
      _ = a₁ * (G.c₁ / G.e₁ r ^ 2) + a₂ * (G.c₂ / G.e₂ r ^ 2) +
          4 * (p.θX * G.UX r + Dm) ^ 2 := by
          rw [ha₁, ha₂]
          field_simp
          ring
      _ ≤ a₁ * (G.c₁ / G.e₁ r ^ 2) + a₂ * (G.c₂ / G.e₂ r ^ 2) + a₃ * 1 + a₄ * (1 / G.P r) := by
          linarith
  · have I1 := zpc_integral_inv_sq_le (s := G.s) hG.η₁_pos hc₁ ht.1 hts
    have I2 := zpc_integral_inv_sq_le (s := G.s) hG.η₂_pos hc₂ ht.1 hts
    have I3 : ∫ _ in (0 : ℝ)..t, (1 : ℝ) ≤ t := by simp
    have I4 : ∫ r in (0 : ℝ)..t, 1 / G.P r ≤
        1 / (Real.sqrt (G.c₁ * G.c₂) * Real.sqrt (G.P t)) :=
      zpc_integral_inv_P_le hG.η₁_pos hc₁ hG.η₂_pos hc₂ ht.1 hts
    refine (zpc_integral_add4_le ht.1 hcont₁ hcont₂ hcont₃ hcont₄ ha₁0 ha₂0 ha₃0 ha₄0
      I1 I2 I3 I4).trans ?_
    have he₁ : G.η₁ ≤ zigHeight G.η₁ G.c₁ G.s t := hG.η₁_le_e₁ hts
    have he₂ : G.η₂ ≤ zigHeight G.η₂ G.c₂ G.s t := hG.η₂_le_e₂ hts
    have hη₁ := hG.η₁_pos
    have hη₂ := hG.η₂_pos
    have hPt := hP t ⟨ht.1, le_rfl⟩
    have hgm := hG.gm_le hts
    have hgm0 := hG.gm_pos
    have hQ : 0 < Real.sqrt (G.P t) := Real.sqrt_pos.2 hPt
    have k1 : a₁ * (1 / zigHeight G.η₁ G.c₁ G.s t) ≤ a₁ * (1 / G.η₁) := by gcongr
    have k2 : a₂ * (1 / zigHeight G.η₂ G.c₂ G.s t) ≤ a₂ * (1 / G.η₂) := by gcongr
    have k3 : a₃ * t ≤ a₃ * G.s := by gcongr
    have k4 : a₄ * (1 / (Real.sqrt (G.c₁ * G.c₂) * Real.sqrt (G.P t))) ≤ a₄ * (1 / G.gm) := by
      gcongr
    have e : a₁ * (1 / G.η₁) + a₂ * (1 / G.η₂) + a₃ * G.s + a₄ * (1 / G.gm) =
        (3 * p.Tz * p.θZ * G.ell2 / G.N + 8 * G.s * p.Cm ^ 2 * Real.pi ^ 2 +
          8 * p.θX ^ 2 / (G.N * G.gm)) * G.UZ := by
      rw [ha₁, ha₂, ha₃, ha₄]
      unfold zpc_Geom.ell2
      field_simp
    linarith

/-- **The `Z` step.** If the thresholds of `X` and `Z` hold on `[0, T]`, then on `[0, T]`
`|Z(t)| ≤ βZ U_Z`. -/
theorem zpc_stepZ (hG : G.Valid) (hS : zpc_Small G p) (h : zpc_Hyp G p D) {T : ℝ}
    (hT : T ∈ Icc 0 G.s) (hX : ∀ r ∈ Icc 0 T, ∀ k, ‖D.X k r‖ ≤ p.θX * G.UX r)
    (hZ : ∀ r ∈ Icc 0 T, |D.Z r| ≤ p.θZ * G.UZ) :
    ∀ t ∈ Icc 0 T, |D.Z t| ≤ p.βZ * G.UZ := by
  intro t ht
  have hts : t ∈ Icc 0 G.s := ⟨ht.1, ht.2.trans hT.2⟩
  have hUZ := hG.UZ_pos
  have m := zpc_martZ_le hG hS h hts fun r hr => hZ r ⟨hr.1, hr.2.trans ht.2⟩
  have d := zpc_driftZ_le hG hS h hT hX hZ ht
  have z0 := h.Z0
  rw [h.decZ t hts]
  have hK : zpc_KZ G p * G.UZ ≤ p.βZ * G.UZ :=
    mul_le_mul_of_nonneg_right hS.closeZ hUZ.le
  have e : zpc_KZ G p * G.UZ = Real.pi ^ 2 * G.UZ +
      p.lam * p.θZ * Real.sqrt (2 * G.ell2 / G.N) * G.UZ +
      (3 * p.Tz * p.θZ * G.ell2 / G.N + 8 * G.s * p.Cm ^ 2 * Real.pi ^ 2 +
        8 * p.θX ^ 2 / (G.N * G.gm)) * G.UZ := by
    unfold zpc_KZ
    ring
  calc |D.Z 0 + D.MZ t + ∫ r in (0 : ℝ)..t, D.DZ r|
      ≤ |D.Z 0| + |D.MZ t| + |∫ r in (0 : ℝ)..t, D.DZ r| := by
        refine (abs_add_le _ _).trans ?_
        exact add_le_add_left (abs_add_le _ _) _
    _ ≤ p.βZ * G.UZ := by linarith

end BlockBand.Native.CEH.ETH
