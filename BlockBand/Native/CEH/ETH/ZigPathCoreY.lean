module

public import BlockBand.Native.CEH.ETH.ZigPathCore

/-!
# CEH ETH, two-resolvent zig, path core: the `Y` step

The improved bound on the fluctuation `Y` of the `I`-chain, given its own threshold.
Deterministic, on one sample path, with data and hypotheses `zpc_Geom`, `zpc_Par`, `zpc_Proc`,
`zpc_Hyp`, `zpc_Small`; the only measure is Lebesgue measure on `ℝ`.

* `zpc_brkY_integral_le` (min form of `‖⟨Im R₁ Im R₂⟩‖`): `∫_{(0,t]} brk_Y ≤ 3 / (N² P_t²)`.
* `zpc_martY_le`: at every `t ∈ [0, s]`, `‖M_Y(t)‖ ≤ 4√3 lam U_Y(t)` (grid cell
  `h_ℓ ≤ P_t ≤ 2h_ℓ`, budget `zpc_bY ℓ`, level `zpc_aY ℓ`). No threshold is needed: the `Y`
  bracket only uses the tube.
* `zpc_driftY_le`: if `‖Y_j‖ ≤ θY U_Y` on `[0, T]`, then on `[0, T]`
  `‖∫_0^t (D_Y - 2 a Y)‖ ≤ (θY²/(3 N gm) + 3 Tz) U_Y(t)` (`Y²` and tube terms).
* `zpc_stepY`: if `‖Y_j‖ ≤ θY U_Y` on `[0, T]` for all `j`, then on `[0, T]`
  `‖Y_j(t)‖ ≤ (1 + Lmax) K_Y U_Y(t)` (two-height Grönwall `norm_le_twoHeight_I`, `k = 2`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Set MeasureTheory intervalIntegral
open BlockBand.Native.CEH.Zig

variable {ι κ : Type*} {G : zpc_Geom} {p : zpc_Par} {D : zpc_Proc ι κ}

/-- **Bracket of `Y`** (with the min form of `‖⟨Im R₁ Im R₂⟩‖`):
`∫_{(0,t]} brk ≤ 3 / (N² P_t²)`. -/
theorem zpc_brkY_integral_le (hG : G.Valid) {f TI : ℝ → ℝ} {t : ℝ} (ht : t ∈ Icc 0 G.s)
    (hf0 : ∀ r ∈ Icc 0 G.s, 0 ≤ f r)
    (hf : ∀ r ∈ Icc 0 G.s, f r ≤
      2 / G.N ^ 2 * ((G.e₁ r)⁻¹ ^ 3 * (G.e₂ r)⁻¹ + (G.e₁ r)⁻¹ * (G.e₂ r)⁻¹ ^ 3) * TI r)
    (hTI₁ : ∀ r ∈ Icc 0 G.s, TI r ≤ 3 / 2 * (G.c₁ / G.e₂ r))
    (hTI₂ : ∀ r ∈ Icc 0 G.s, TI r ≤ 3 / 2 * (G.c₂ / G.e₁ r)) :
    ∫ r in Ioc 0 t, f r ≤ 3 / (G.N ^ 2 * G.P t ^ 2) := by
  have hN := hG.N_pos
  have hts := ht.2
  have h1 : ∀ r ∈ Icc 0 t, 0 < G.e₁ r := fun r hr => hG.e₁_pos (hr.2.trans hts)
  have h2 : ∀ r ∈ Icc 0 t, 0 < G.e₂ r := fun r hr => hG.e₂_pos (hr.2.trans hts)
  have hc₁ := hG.c₁_pos
  have hc₂ := hG.c₂_pos
  set a : ℝ := 2 / G.N ^ 2 * (3 / 2) with ha
  have ha0 : 0 ≤ a := by positivity
  have hcont₁ : ContinuousOn (fun r => G.c₁ / (G.e₁ r ^ 3 * G.e₂ r ^ 2)) (Icc 0 t) := by
    unfold zpc_Geom.e₁ zpc_Geom.e₂
    fun_prop (disch := first
      | (intro r hr; have := h1 r hr; have := h2 r hr; positivity)
      | positivity)
  have hcont₂ : ContinuousOn (fun r => G.c₂ / (G.e₂ r ^ 3 * G.e₁ r ^ 2)) (Icc 0 t) := by
    unfold zpc_Geom.e₁ zpc_Geom.e₂
    fun_prop (disch := first
      | (intro r hr; have := h1 r hr; have := h2 r hr; positivity)
      | positivity)
  have hg : ContinuousOn (fun r => a * (G.c₁ / (G.e₁ r ^ 3 * G.e₂ r ^ 2)) +
      a * (G.c₂ / (G.e₂ r ^ 3 * G.e₁ r ^ 2))) (Icc 0 t) :=
    (continuousOn_const.mul hcont₁).add (continuousOn_const.mul hcont₂)
  refine (zpc_setIntegral_le ht.1 (fun r hr => hf0 r ⟨hr.1.le, hr.2.trans hts⟩) hg
    fun r hr => ?_).trans ?_
  · have hrs : r ∈ Icc 0 G.s := ⟨hr.1.le, hr.2.trans hts⟩
    have he₁ := h1 r ⟨hr.1.le, hr.2⟩
    have he₂ := h2 r ⟨hr.1.le, hr.2⟩
    calc f r ≤ 2 / G.N ^ 2 * ((G.e₁ r)⁻¹ ^ 3 * (G.e₂ r)⁻¹ + (G.e₁ r)⁻¹ * (G.e₂ r)⁻¹ ^ 3) *
          TI r := hf r hrs
      _ = 2 / G.N ^ 2 * ((G.e₁ r)⁻¹ ^ 3 * (G.e₂ r)⁻¹ * TI r) +
          2 / G.N ^ 2 * ((G.e₁ r)⁻¹ * (G.e₂ r)⁻¹ ^ 3 * TI r) := by ring
      _ ≤ 2 / G.N ^ 2 * ((G.e₁ r)⁻¹ ^ 3 * (G.e₂ r)⁻¹ * (3 / 2 * (G.c₁ / G.e₂ r))) +
          2 / G.N ^ 2 * ((G.e₁ r)⁻¹ * (G.e₂ r)⁻¹ ^ 3 * (3 / 2 * (G.c₂ / G.e₁ r))) := by
          gcongr
          · exact hTI₁ r hrs
          · exact hTI₂ r hrs
      _ = a * (G.c₁ / (G.e₁ r ^ 3 * G.e₂ r ^ 2)) + a * (G.c₂ / (G.e₂ r ^ 3 * G.e₁ r ^ 2)) := by
          rw [ha]
          field_simp
  · have I1 := zpc_integral_cube_mul_sq_le (s := G.s) hG.η₁_pos hc₁ hG.η₂_pos hc₂.le ht.1 hts
    have I2 := zpc_integral_cube_mul_sq_le (s := G.s) hG.η₂_pos hc₂ hG.η₁_pos hc₁.le ht.1 hts
    refine (zpc_integral_add2_le ht.1 hcont₁ hcont₂ ha0 ha0 I1 I2).trans (le_of_eq ?_)
    have := h1 t ⟨ht.1, le_rfl⟩
    have := h2 t ⟨ht.1, le_rfl⟩
    rw [ha, zpc_Geom.P_eq]
    unfold zpc_Geom.e₁ zpc_Geom.e₂
    field_simp
    ring

/-- `√(3/(N² h²)) = √3/(N h)`. -/
theorem zpc_sqrt_three_div {N h : ℝ} (hN : 0 < N) (hh : 0 < h) :
    Real.sqrt (3 / (N ^ 2 * h ^ 2)) = Real.sqrt 3 / (N * h) := by
  rw [show N ^ 2 * h ^ 2 = (N * h) ^ 2 by ring, Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq (by positivity)]

/-- **Martingale part of `Y`**: `‖M_Y(t)‖ ≤ 4√3 lam U_Y(t)` on `[0, s]`. -/
theorem zpc_martY_le (hG : G.Valid) (hS : zpc_Small G p) (h : zpc_Hyp G p D) (j : κ) {t : ℝ}
    (ht : t ∈ Icc 0 G.s) : ‖D.MY j t‖ ≤ 4 * Real.sqrt 3 * p.lam * G.UY t := by
  obtain ⟨ℓ, hℓ, hc1, hc2⟩ := hG.exists_cell hS.grid ht
  have hN := hG.N_pos
  have hh := hG.lvl_pos ℓ
  have hPt := hG.P_pos ht.2
  have hb : 3 / (G.N ^ 2 * G.P t ^ 2) ≤ zpc_bY G ℓ := by
    unfold zpc_bY
    gcongr
  have hre := h.martYre j ℓ hℓ t ht ((zpc_brkY_integral_le hG ht (h.brkYre_nonneg j)
    (h.brkYre_le j) h.TI_le₁ h.TI_le₂).trans hb)
  have him := h.martYim j ℓ hℓ t ht ((zpc_brkY_integral_le hG ht (h.brkYim_nonneg j)
    (h.brkYim_le j) h.TI_le₁ h.TI_le₂).trans hb)
  refine (zpc_norm_lt_of_parts hre him).le.trans ?_
  have hl := hS.lam_nonneg
  unfold zpc_aY zpc_bY zpc_Geom.UY
  rw [zpc_sqrt_three_div hN hh]
  have h3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  rw [show 2 * (p.lam * (Real.sqrt 3 / (G.N * G.lvl ℓ))) =
    (2 * p.lam * Real.sqrt 3) * (1 / (G.N * G.lvl ℓ)) by ring,
    show 4 * Real.sqrt 3 * p.lam * (1 / (G.N * G.P t)) =
    (2 * p.lam * Real.sqrt 3) * (2 / (G.N * G.P t)) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Drift remainder of `Y`**: on `[0, T]` (thresholds `‖Y_j‖ ≤ θY U_Y` there),
`‖∫_0^t (D_Y - 2 a Y)‖ ≤ (θY²/(3 N gm) + 3 Tz) U_Y(t)`. -/
theorem zpc_driftY_le (hG : G.Valid) (hS : zpc_Small G p) (h : zpc_Hyp G p D) {T : ℝ}
    (hT : T ∈ Icc 0 G.s) (hthr : ∀ r ∈ Icc 0 T, ∀ j, ‖D.Y j r‖ ≤ p.θY * G.UY r) (j : κ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖∫ r in (0 : ℝ)..t, (D.DY j r - 2 * D.cfY j r * D.Y j r)‖ ≤
      (p.θY ^ 2 / (3 * G.N * G.gm) + 3 * p.Tz) * G.UY t := by
  have hN := hG.N_pos
  have hts : t ≤ G.s := ht.2.trans hT.2
  have h1 : ∀ r ∈ Icc 0 t, 0 < G.e₁ r := fun r hr => hG.e₁_pos (hr.2.trans hts)
  have h2 : ∀ r ∈ Icc 0 t, 0 < G.e₂ r := fun r hr => hG.e₂_pos (hr.2.trans hts)
  have hP : ∀ r ∈ Icc 0 t, 0 < G.P r := fun r hr => hG.P_pos (hr.2.trans hts)
  have hc₁ := hG.c₁_pos
  have hc₂ := hG.c₂_pos
  have hTz := hS.Tz_nonneg
  set a₁ : ℝ := p.θY ^ 2 / G.N ^ 2 with ha₁
  set a₂ : ℝ := 3 / 2 * p.Tz / G.N with ha₂
  have ha₁0 : 0 ≤ a₁ := by positivity
  have ha₂0 : 0 ≤ a₂ := by positivity
  have hcont₁ : ContinuousOn (fun r => 1 / G.P r ^ 2) (Icc 0 t) :=
    continuousOn_const.div (zpc_Geom.continuousOn_P.mono (Icc_subset_Icc le_rfl hts) |>.pow 2)
      fun r hr => by have := hP r hr; positivity
  have hcont₂ : ContinuousOn (fun r => G.c₁ / (G.e₁ r ^ 2 * G.e₂ r)) (Icc 0 t) := by
    unfold zpc_Geom.e₁ zpc_Geom.e₂
    fun_prop (disch := first
      | (intro r hr; have := h1 r hr; have := h2 r hr; positivity)
      | positivity)
  have hcont₃ : ContinuousOn (fun r => G.c₂ / (G.e₂ r ^ 2 * G.e₁ r)) (Icc 0 t) := by
    unfold zpc_Geom.e₁ zpc_Geom.e₂
    fun_prop (disch := first
      | (intro r hr; have := h1 r hr; have := h2 r hr; positivity)
      | positivity)
  have hg : ContinuousOn (fun r => a₁ * (1 / G.P r ^ 2) + a₂ * (G.c₁ / (G.e₁ r ^ 2 * G.e₂ r)) +
      a₂ * (G.c₂ / (G.e₂ r ^ 2 * G.e₁ r))) (Icc 0 t) :=
    ((continuousOn_const.mul hcont₁).add (continuousOn_const.mul hcont₂)).add
      (continuousOn_const.mul hcont₃)
  refine (zpc_norm_integral_le ht.1 hg fun r hr => ?_).trans ?_
  · have hrs : r ∈ Icc 0 G.s := ⟨hr.1, hr.2.trans hts⟩
    have he₁ := h1 r hr
    have he₂ := h2 r hr
    have hPr := hP r hr
    have hY := hthr r ⟨hr.1, hr.2.trans ht.2⟩ j
    have hW₁ := h.W₁_le r hrs
    have hW₂ := h.W₂_le r hrs
    have hQ₁ : ‖D.QY₁ j r‖ ≤ 3 / 2 * G.c₁ / (G.e₁ r * G.e₂ r) :=
      (h.QY₁_le j r hrs).trans (div_le_div_of_nonneg_right (h.imR₁_le r hrs) (by positivity))
    have hQ₂ : ‖D.QY₂ j r‖ ≤ 3 / 2 * G.c₂ / (G.e₁ r * G.e₂ r) :=
      (h.QY₂_le j r hrs).trans (div_le_div_of_nonneg_right (h.imR₂_le r hrs) (by positivity))
    have hYsq : ‖D.Y j r‖ ^ 2 ≤ (p.θY * G.UY r) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hY 2
    calc ‖D.DY j r - 2 * D.cfY j r * D.Y j r‖
        ≤ ‖D.Y j r‖ ^ 2 + ‖D.W₁ r‖ * ‖D.QY₁ j r‖ + ‖D.W₂ r‖ * ‖D.QY₂ j r‖ := h.driftY j r hrs
      _ ≤ (p.θY * G.UY r) ^ 2 + p.Tz / (G.N * G.e₁ r) * (3 / 2 * G.c₁ / (G.e₁ r * G.e₂ r)) +
          p.Tz / (G.N * G.e₂ r) * (3 / 2 * G.c₂ / (G.e₁ r * G.e₂ r)) := by
          gcongr
      _ = a₁ * (1 / G.P r ^ 2) + a₂ * (G.c₁ / (G.e₁ r ^ 2 * G.e₂ r)) +
          a₂ * (G.c₂ / (G.e₂ r ^ 2 * G.e₁ r)) := by
          rw [ha₁, ha₂]
          unfold zpc_Geom.UY
          rw [zpc_Geom.P_eq]
          field_simp
  · have I1 : ∫ r in (0 : ℝ)..t, 1 / G.P r ^ 2 ≤
        1 / (3 * Real.sqrt (G.c₁ * G.c₂) * (G.P t * Real.sqrt (G.P t))) :=
      zpc_integral_inv_P_sq_le hG.η₁_pos hc₁ hG.η₂_pos hc₂ ht.1 hts
    have I2 := zpc_integral_sq_mul_le (s := G.s) hG.η₁_pos hc₁ hG.η₂_pos hc₂.le ht.1 hts
    have I3 := zpc_integral_sq_mul_le (s := G.s) hG.η₂_pos hc₂ hG.η₁_pos hc₁.le ht.1 hts
    refine (zpc_integral_add3_le ht.1 hcont₁ hcont₂ hcont₃ ha₁0 ha₂0 ha₂0 I1 I2 I3).trans ?_
    have hPt := hP t ⟨ht.1, le_rfl⟩
    have he₁ := h1 t ⟨ht.1, le_rfl⟩
    have he₂ := h2 t ⟨ht.1, le_rfl⟩
    have hgm := hG.gm_le hts
    have hgm0 := hG.gm_pos
    have hA : 0 < Real.sqrt (G.c₁ * G.c₂) := Real.sqrt_pos.2 (by positivity)
    have hQ : 0 < Real.sqrt (G.P t) := Real.sqrt_pos.2 hPt
    -- the `Y²` term
    have k1 : a₁ * (1 / (3 * Real.sqrt (G.c₁ * G.c₂) * (G.P t * Real.sqrt (G.P t)))) ≤
        p.θY ^ 2 / (3 * G.N * G.gm) * G.UY t := by
      rw [ha₁]
      unfold zpc_Geom.UY
      rw [show p.θY ^ 2 / G.N ^ 2 * (1 / (3 * Real.sqrt (G.c₁ * G.c₂) *
          (G.P t * Real.sqrt (G.P t)))) = p.θY ^ 2 / (3 * G.N) * (1 / (G.N * G.P t)) *
          (1 / (Real.sqrt (G.c₁ * G.c₂) * Real.sqrt (G.P t))) by field_simp,
        show p.θY ^ 2 / (3 * G.N * G.gm) * (1 / (G.N * G.P t)) =
          p.θY ^ 2 / (3 * G.N) * (1 / (G.N * G.P t)) * (1 / G.gm) by field_simp]
      gcongr
    -- the tube terms
    have k2 : a₂ * (1 / (zigHeight G.η₁ G.c₁ G.s t * zigHeight G.η₂ G.c₂ G.s t)) +
        a₂ * (1 / (zigHeight G.η₂ G.c₂ G.s t * zigHeight G.η₁ G.c₁ G.s t)) =
        3 * p.Tz * G.UY t := by
      rw [ha₂]
      unfold zpc_Geom.UY
      rw [zpc_Geom.P_eq]
      unfold zpc_Geom.e₁ zpc_Geom.e₂
      unfold zpc_Geom.e₁ at he₁
      unfold zpc_Geom.e₂ at he₂
      field_simp
      ring
    have : (p.θY ^ 2 / (3 * G.N * G.gm) + 3 * p.Tz) * G.UY t =
        p.θY ^ 2 / (3 * G.N * G.gm) * G.UY t + 3 * p.Tz * G.UY t := by ring
    linarith

/-- **The `Y` step.** If `‖Y_j‖ ≤ θY U_Y` on `[0, T]` for all `j`, then on `[0, T]`
`‖Y_j(t)‖ ≤ (1 + Lmax) K_Y U_Y(t)`. -/
theorem zpc_stepY (hG : G.Valid) (hS : zpc_Small G p) (h : zpc_Hyp G p D) {T : ℝ}
    (hT : T ∈ Icc 0 G.s) (hthr : ∀ r ∈ Icc 0 T, ∀ j, ‖D.Y j r‖ ≤ p.θY * G.UY r) (j : κ) :
    ∀ t ∈ Icc 0 T, ‖D.Y j t‖ ≤ (1 + p.Lmax) * zpc_KY G p * G.UY t := by
  have hN := hG.N_pos
  have hTs := hT.2
  have hsub : Icc 0 T ⊆ Icc 0 G.s := Icc_subset_Icc le_rfl hTs
  set E : ℝ → ℂ := fun t => D.Y j t - ∫ u in (0 : ℝ)..t, 2 * D.cfY j u * D.Y j u with hE
  have hKY : 0 ≤ zpc_KY G p := by
    have := hS.lam_nonneg
    have := hS.Tz_nonneg
    have := hG.gm_pos
    unfold zpc_KY
    positivity
  have hgr := norm_le_twoHeight_I (E := E) (K := zpc_KY G p) hG.η₁_pos hG.c₁_pos.le
    hG.η₂_pos hG.c₂_pos.le hN hTs ((h.contY j).mono hsub) ((h.contCfY j).mono hsub)
    (fun t _ => by simp only [hE, sub_add_cancel]) (fun u hu => h.cfY_le j u (hsub hu))
    (fun t ht => by
      have hts : t ∈ Icc 0 G.s := hsub ht
      have hDi : IntervalIntegrable (D.DY j) volume 0 t :=
        (h.intDY j).mono_set (by
          rw [uIcc_of_le hG.s_nonneg, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl hts.2)
      have hci : IntervalIntegrable (fun u => 2 * D.cfY j u * D.Y j u) volume 0 t :=
        ((continuousOn_const.mul ((h.contCfY j).mono (Icc_subset_Icc le_rfl hts.2))).mul
          ((h.contY j).mono (Icc_subset_Icc le_rfl hts.2))).intervalIntegrable_of_Icc ht.1
      have e : E t = D.MY j t + ∫ r in (0 : ℝ)..t, (D.DY j r - 2 * D.cfY j r * D.Y j r) := by
        rw [intervalIntegral.integral_sub hDi hci, hE]
        simp only
        rw [h.decY j t hts]
        ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have m := zpc_martY_le hG hS h j hts
      have d := zpc_driftY_le hG hS h hT hthr j ht
      have : zpc_KY G p / (G.N * G.P t) =
          4 * Real.sqrt 3 * p.lam * G.UY t +
            (p.θY ^ 2 / (3 * G.N * G.gm) + 3 * p.Tz) * G.UY t := by
        unfold zpc_KY zpc_Geom.UY
        ring
      change _ ≤ zpc_KY G p / (G.N * G.P t)
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
  change zpc_KY G p / (G.N * G.P t) * _ ≤ _
  unfold zpc_Geom.UY
  rw [show (1 + p.Lmax) * zpc_KY G p * (1 / (G.N * G.P t)) =
    zpc_KY G p / (G.N * G.P t) * (1 + p.Lmax) by ring]
  gcongr
  exact hlog

end BlockBand.Native.CEH.ETH
