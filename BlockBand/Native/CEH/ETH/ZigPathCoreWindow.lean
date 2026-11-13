module

public import BlockBand.Native.CEH.ETH.ZigPathCoreClosure

/-!
# CEH ETH, two-resolvent zig, path core: window form of the numeric hypotheses

On the spectral window, where `n_e ≤ N ρ_i η_i` (`n_e = N^{ε_ρ}`), the constants of the path core
satisfy

* `K_Y ≤ 4√3 lam + θY²/(3π n_e) + 3 Tz`,
* `K_X ≤ 2 lam √(4θZ/(π n_e)) + Cm θY/√(Nρ₁ρ₂) + θXθY/(2π n_e) + 2 Tz √(3θZ/2)/√(π n_e)`,
* `K_Z ≤ π² + lam θZ √(4/(π n_e)) + 6 Tz θZ/(π n_e) + 8 s Cm² π² + 8 θX²/(π n_e)`.

* `zpc_small_of_ne`: `zpc_Small` from the closing inequalities in this window form.
* `zpc_parRpow`, `zpc_closure_rpow`: the closure with `lam = N^{ξ/4}`, `θX = θY = N^{2ξ}`,
  `θZ = N^ξ`, `βZ = N^{ξ/2}`, `Tz = N^ζ`; conclusion `‖X_k‖ < N^{2ξ} U_X`,
  `‖Y_j‖ < N^{2ξ} U_Y`, `|Z| < N^ξ U_Z` on `[0, s]` and `|Z_s| ≤ N^{ξ/2} ρ₁ρ₂ S²`.
* For the tails: `zpc_bX_pos`, `zpc_bY_pos`, `zpc_bZ_pos` and
  `a²/(2b) = lam²/2` (`zpc_aX_sq_div`, `zpc_aY_sq_div`, `zpc_aZ_sq_div`), with
  `lam²/2 = N^{ξ/2}/2` for `lam = N^{ξ/4}` (`zpc_lam_rpow_sq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Set

variable {G : zpc_Geom}

theorem zpc_N_gm_ge (hG : G.Valid) {ne : ℝ} (hne : 0 < ne) (h₁ : ne ≤ G.N * G.ρ₁ * G.η₁)
    (h₂ : ne ≤ G.N * G.ρ₂ * G.η₂) : Real.pi * ne ≤ G.N * G.gm := by
  have hN := hG.N_pos
  have hρ₁ := hG.ρ₁_pos
  have hρ₂ := hG.ρ₂_pos
  have hη₁ := hG.η₁_pos
  have hη₂ := hG.η₂_pos
  have hpi := Real.pi_pos
  unfold zpc_Geom.gm
  rw [hG.c₁_eq, hG.c₂_eq, show Real.pi * G.ρ₁ * G.η₁ * (Real.pi * G.ρ₂ * G.η₂) =
    (Real.pi * Real.sqrt (G.ρ₁ * G.η₁ * (G.ρ₂ * G.η₂))) ^ 2 by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring, Real.sqrt_sq (by positivity)]
  have hx : ne / G.N ≤ Real.sqrt (G.ρ₁ * G.η₁ * (G.ρ₂ * G.η₂)) := by
    rw [show ne / G.N = Real.sqrt ((ne / G.N) * (ne / G.N)) by
      rw [Real.sqrt_mul_self (by positivity)]]
    refine Real.sqrt_le_sqrt (mul_le_mul ?_ ?_ (by positivity) (by positivity))
    · rw [div_le_iff₀ hN]; linarith
    · rw [div_le_iff₀ hN]; linarith
  have key := mul_le_mul_of_nonneg_left hx (by positivity : (0 : ℝ) ≤ G.N * Real.pi)
  calc Real.pi * ne = G.N * Real.pi * (ne / G.N) := by field_simp
    _ ≤ G.N * Real.pi * Real.sqrt (G.ρ₁ * G.η₁ * (G.ρ₂ * G.η₂)) := key
    _ = _ := by ring

theorem zpc_N_c_η_ge (hG : G.Valid) {ne : ℝ} (h₁ : ne ≤ G.N * G.ρ₁ * G.η₁)
    (h₂ : ne ≤ G.N * G.ρ₂ * G.η₂) :
    Real.pi * ne ≤ G.N * (G.c₁ * G.η₁) ∧ Real.pi * ne ≤ G.N * (G.c₂ * G.η₂) := by
  have hpi := Real.pi_pos
  rw [hG.c₁_eq, hG.c₂_eq]
  constructor <;> nlinarith

theorem zpc_ell2_div_le (hG : G.Valid) {ne : ℝ} (hne : 0 < ne) (h₁ : ne ≤ G.N * G.ρ₁ * G.η₁)
    (h₂ : ne ≤ G.N * G.ρ₂ * G.η₂) : G.ell2 / G.N ≤ 2 / (Real.pi * ne) := by
  have hN := hG.N_pos
  have hpi := Real.pi_pos
  obtain ⟨k₁, k₂⟩ := zpc_N_c_η_ge hG h₁ h₂
  have hq₁ : 0 < G.c₁ * G.η₁ := mul_pos hG.c₁_pos hG.η₁_pos
  have hq₂ : 0 < G.c₂ * G.η₂ := mul_pos hG.c₂_pos hG.η₂_pos
  unfold zpc_Geom.ell2
  have a₁ : 1 / (G.c₁ * G.η₁) / G.N ≤ 1 / (Real.pi * ne) := by
    rw [div_div, one_div_le_one_div (by positivity) (by positivity)]; linarith
  have a₂ : 1 / (G.c₂ * G.η₂) / G.N ≤ 1 / (Real.pi * ne) := by
    rw [div_div, one_div_le_one_div (by positivity) (by positivity)]; linarith
  have e : (1 / (G.c₁ * G.η₁) + 1 / (G.c₂ * G.η₂)) / G.N =
      1 / (G.c₁ * G.η₁) / G.N + 1 / (G.c₂ * G.η₂) / G.N := by ring
  have e' : 2 / (Real.pi * ne) = 1 / (Real.pi * ne) + 1 / (Real.pi * ne) := by ring
  linarith

/-- **`zpc_Small` from the window form** of the closing inequalities (`n_e ≤ N ρ_i η_i`). -/
theorem zpc_small_of_ne {p : zpc_Par} (hG : G.Valid) {ne : ℝ} (hne : 0 < ne)
    (h₁ : ne ≤ G.N * G.ρ₁ * G.η₁) (h₂ : ne ≤ G.N * G.ρ₂ * G.η₂)
    (hlam : 0 ≤ p.lam) (hTz : 0 ≤ p.Tz) (hCm : 0 ≤ p.Cm) (hθX : 0 < p.θX) (hθY : 0 < p.θY)
    (hθZ : 0 < p.θZ) (hgrid : G.P 0 ≤ 2 ^ p.Lg * G.P G.s)
    (hlog : Real.log (G.P 0 / G.P G.s) ≤ p.Lmax)
    (hY : (1 + p.Lmax) * (4 * Real.sqrt 3 * p.lam + p.θY ^ 2 / (3 * (Real.pi * ne)) +
      3 * p.Tz) < p.θY)
    (hX : (1 + p.Lmax / 2) * (2 * p.lam * Real.sqrt (4 * p.θZ / (Real.pi * ne)) +
      p.Cm * p.θY / Real.sqrt (G.N * (G.ρ₁ * G.ρ₂)) + p.θX * p.θY / (2 * (Real.pi * ne)) +
      2 * p.Tz * Real.sqrt (3 / 2 * p.θZ) / Real.sqrt (Real.pi * ne)) < p.θX)
    (hZ : Real.pi ^ 2 + p.lam * p.θZ * Real.sqrt (4 / (Real.pi * ne)) +
      6 * p.Tz * p.θZ / (Real.pi * ne) + 8 * G.s * p.Cm ^ 2 * Real.pi ^ 2 +
      8 * p.θX ^ 2 / (Real.pi * ne) ≤ p.βZ) (hβ : p.βZ < p.θZ) : zpc_Small G p := by
  have hN := hG.N_pos
  have hpi := Real.pi_pos
  have hgm := zpc_N_gm_ge hG hne h₁ h₂
  have hl2 := zpc_ell2_div_le hG hne h₁ h₂
  obtain ⟨k₁, k₂⟩ := zpc_N_c_η_ge hG h₁ h₂
  have hpn : 0 < Real.pi * ne := by positivity
  have hP0 := hG.P_pos hG.s_nonneg
  have hPs := hG.P_pos le_rfl
  have hL : 0 ≤ p.Lmax := by
    refine le_trans (Real.log_nonneg ?_) hlog
    rw [le_div_iff₀ hPs, one_mul]
    exact hG.P_anti hG.s_nonneg le_rfl
  have hgm0 := hG.gm_pos
  have hl20 := hG.ell2_pos
  -- comparison of the constants
  have cY : zpc_KY G p ≤ 4 * Real.sqrt 3 * p.lam + p.θY ^ 2 / (3 * (Real.pi * ne)) +
      3 * p.Tz := by
    unfold zpc_KY
    have : p.θY ^ 2 / (3 * G.N * G.gm) ≤ p.θY ^ 2 / (3 * (Real.pi * ne)) := by
      rw [mul_assoc]; gcongr
    linarith
  have sq1 : Real.sqrt (2 * p.θZ * G.ell2 / G.N) ≤ Real.sqrt (4 * p.θZ / (Real.pi * ne)) := by
    refine Real.sqrt_le_sqrt ?_
    rw [show 2 * p.θZ * G.ell2 / G.N = 2 * p.θZ * (G.ell2 / G.N) by ring,
      show 4 * p.θZ / (Real.pi * ne) = 2 * p.θZ * (2 / (Real.pi * ne)) by ring]
    exact mul_le_mul_of_nonneg_left hl2 (by positivity)
  have sq2 : ∀ q : ℝ, Real.pi * ne ≤ G.N * q →
      1 / Real.sqrt (G.N * q) ≤ 1 / Real.sqrt (Real.pi * ne) := by
    intro q hq
    have : 0 < Real.sqrt (Real.pi * ne) := Real.sqrt_pos.2 hpn
    gcongr
  have cX : zpc_KX G p ≤ 2 * p.lam * Real.sqrt (4 * p.θZ / (Real.pi * ne)) +
      p.Cm * p.θY / Real.sqrt (G.N * (G.ρ₁ * G.ρ₂)) + p.θX * p.θY / (2 * (Real.pi * ne)) +
      2 * p.Tz * Real.sqrt (3 / 2 * p.θZ) / Real.sqrt (Real.pi * ne) := by
    unfold zpc_KX
    have t1 : 2 * p.lam * Real.sqrt (2 * p.θZ * G.ell2 / G.N) ≤
        2 * p.lam * Real.sqrt (4 * p.θZ / (Real.pi * ne)) := by gcongr
    have t2 : p.θX * p.θY / (2 * G.N * G.gm) ≤ p.θX * p.θY / (2 * (Real.pi * ne)) := by
      rw [mul_assoc]; gcongr
    have t3 : p.Tz * Real.sqrt (3 / 2 * p.θZ) *
        (1 / Real.sqrt (G.N * (G.c₁ * G.η₁)) + 1 / Real.sqrt (G.N * (G.c₂ * G.η₂))) ≤
        2 * p.Tz * Real.sqrt (3 / 2 * p.θZ) / Real.sqrt (Real.pi * ne) := by
      have := add_le_add (sq2 _ k₁) (sq2 _ k₂)
      calc p.Tz * Real.sqrt (3 / 2 * p.θZ) *
            (1 / Real.sqrt (G.N * (G.c₁ * G.η₁)) + 1 / Real.sqrt (G.N * (G.c₂ * G.η₂)))
          ≤ p.Tz * Real.sqrt (3 / 2 * p.θZ) *
            (1 / Real.sqrt (Real.pi * ne) + 1 / Real.sqrt (Real.pi * ne)) := by gcongr
        _ = _ := by ring
    linarith
  have cZ : zpc_KZ G p ≤ Real.pi ^ 2 + p.lam * p.θZ * Real.sqrt (4 / (Real.pi * ne)) +
      6 * p.Tz * p.θZ / (Real.pi * ne) + 8 * G.s * p.Cm ^ 2 * Real.pi ^ 2 +
      8 * p.θX ^ 2 / (Real.pi * ne) := by
    unfold zpc_KZ
    have t1 : p.lam * p.θZ * Real.sqrt (2 * G.ell2 / G.N) ≤
        p.lam * p.θZ * Real.sqrt (4 / (Real.pi * ne)) := by
      refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
      rw [show 2 * G.ell2 / G.N = 2 * (G.ell2 / G.N) by ring,
        show 4 / (Real.pi * ne) = 2 * (2 / (Real.pi * ne)) by ring]
      exact mul_le_mul_of_nonneg_left hl2 (by norm_num)
    have t2 : 3 * p.Tz * p.θZ * G.ell2 / G.N ≤ 6 * p.Tz * p.θZ / (Real.pi * ne) := by
      rw [show 3 * p.Tz * p.θZ * G.ell2 / G.N = 3 * p.Tz * p.θZ * (G.ell2 / G.N) by ring,
        show 6 * p.Tz * p.θZ / (Real.pi * ne) = 3 * p.Tz * p.θZ * (2 / (Real.pi * ne)) by ring]
      exact mul_le_mul_of_nonneg_left hl2 (by positivity)
    have t3 : 8 * p.θX ^ 2 / (G.N * G.gm) ≤ 8 * p.θX ^ 2 / (Real.pi * ne) := by gcongr
    linarith
  refine ⟨hlam, hTz, hCm, hθX, hθY, hθZ, hgrid, hlog, ?_, ?_, cZ.trans hZ, hβ⟩
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left cY (by linarith)) hY
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left cX (by linarith)) hX

/-- The parameters of the application: `lam = N^{ξ/4}`, `θX = θY = N^{2ξ}`, `θZ = N^ξ`,
`βZ = N^{ξ/2}`, `Tz = N^ζ`. -/
def zpc_parRpow (N ξ ζ Lmax Cm : ℝ) (Lg : ℕ) : zpc_Par where
  lam := N ^ (ξ / 4)
  θX := N ^ (2 * ξ)
  θY := N ^ (2 * ξ)
  θZ := N ^ ξ
  βZ := N ^ (ξ / 2)
  Tz := N ^ ζ
  Lmax := Lmax
  Cm := Cm
  Lg := Lg

/-- **The closure with `N`-powers.** With
`n_e ≤ N ρ_i η_i` (`n_e = N^{ε_ρ}`) and the window-form closing inequalities, on all of
`[0, s]`: `‖X_k‖ < N^{2ξ} √(ρ₁ρ₂) S/√(N P_t)`, `‖Y_j‖ < N^{2ξ}/(N P_t)`,
`|Z| < N^ξ ρ₁ρ₂ S²`, and `|Z_s| ≤ N^{ξ/2} ρ₁ρ₂ S²`. -/
theorem zpc_closure_rpow {ι κ : Type*} [Finite ι] [Finite κ] {D : zpc_Proc ι κ}
    {ξ ζ ne Lmax Cm : ℝ} {Lg : ℕ} (hG : G.Valid) (hne : 0 < ne)
    (h₁ : ne ≤ G.N * G.ρ₁ * G.η₁) (h₂ : ne ≤ G.N * G.ρ₂ * G.η₂) (hCm : 0 ≤ Cm)
    (hgrid : G.P 0 ≤ 2 ^ Lg * G.P G.s) (hlog : Real.log (G.P 0 / G.P G.s) ≤ Lmax)
    (hY : (1 + Lmax) * (4 * Real.sqrt 3 * G.N ^ (ξ / 4) +
      (G.N ^ (2 * ξ)) ^ 2 / (3 * (Real.pi * ne)) + 3 * G.N ^ ζ) < G.N ^ (2 * ξ))
    (hX : (1 + Lmax / 2) * (2 * G.N ^ (ξ / 4) * Real.sqrt (4 * G.N ^ ξ / (Real.pi * ne)) +
      Cm * G.N ^ (2 * ξ) / Real.sqrt (G.N * (G.ρ₁ * G.ρ₂)) +
      G.N ^ (2 * ξ) * G.N ^ (2 * ξ) / (2 * (Real.pi * ne)) +
      2 * G.N ^ ζ * Real.sqrt (3 / 2 * G.N ^ ξ) / Real.sqrt (Real.pi * ne)) < G.N ^ (2 * ξ))
    (hZ : Real.pi ^ 2 + G.N ^ (ξ / 4) * G.N ^ ξ * Real.sqrt (4 / (Real.pi * ne)) +
      6 * G.N ^ ζ * G.N ^ ξ / (Real.pi * ne) + 8 * G.s * Cm ^ 2 * Real.pi ^ 2 +
      8 * (G.N ^ (2 * ξ)) ^ 2 / (Real.pi * ne) ≤ G.N ^ (ξ / 2))
    (hβ : G.N ^ (ξ / 2) < G.N ^ ξ)
    (h : zpc_Hyp G (zpc_parRpow G.N ξ ζ Lmax Cm Lg) D) :
    (∀ t ∈ Icc 0 G.s,
      (∀ k, ‖D.X k t‖ < G.N ^ (2 * ξ) * G.UX t) ∧ (∀ j, ‖D.Y j t‖ < G.N ^ (2 * ξ) * G.UY t) ∧
      |D.Z t| < G.N ^ ξ * G.UZ) ∧
    |D.Z G.s| ≤ G.N ^ (ξ / 2) * (G.ρ₁ * G.ρ₂ * G.S ^ 2) := by
  have hN := hG.N_pos
  have hS : zpc_Small G (zpc_parRpow G.N ξ ζ Lmax Cm Lg) :=
    zpc_small_of_ne hG hne h₁ h₂ (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hN.le _) hCm
      (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hN _)
      hgrid hlog hY hX hZ hβ
  refine ⟨fun t ht => ?_, zpc_closure_endpoint hG hS h⟩
  obtain ⟨hx, hy, _, hz⟩ := zpc_closure hG hS h t ht
  exact ⟨fun k => (hx k).2, fun j => (hy j).2, hz⟩

/-!
## The martingale parameters (for the tails)
-/

/-- `(lam √b)² / (2b) = lam²/2` for `b > 0`. -/
theorem zpc_level_sq_div {lam b : ℝ} (hb : 0 < b) :
    (lam * Real.sqrt b) ^ 2 / (2 * b) = lam ^ 2 / 2 := by
  rw [mul_pow, Real.sq_sqrt hb.le]
  field_simp

theorem zpc_bX_pos {p : zpc_Par} (hG : G.Valid) (hθZ : 0 < p.θZ) (ℓ : ℕ) :
    0 < zpc_bX G p ℓ := by
  have := hG.UZ_pos
  have := hG.ell2_pos
  have := hG.lvl_pos ℓ
  have := hG.N_pos
  unfold zpc_bX
  positivity

theorem zpc_bY_pos (hG : G.Valid) (ℓ : ℕ) : 0 < zpc_bY G ℓ := by
  have := hG.lvl_pos ℓ
  have := hG.N_pos
  unfold zpc_bY
  positivity

theorem zpc_bZ_pos {p : zpc_Par} (hG : G.Valid) (hθZ : 0 < p.θZ) : 0 < zpc_bZ G p := by
  have := hG.UZ_pos
  have := hG.ell2_pos
  have := hG.N_pos
  unfold zpc_bZ
  positivity

/-- `a_X(ℓ)² / (2 b_X(ℓ)) = lam²/2` (`= N^{ξ/2}/2` for `lam = N^{ξ/4}`). -/
theorem zpc_aX_sq_div {p : zpc_Par} (hG : G.Valid) (hθZ : 0 < p.θZ) (ℓ : ℕ) :
    zpc_aX G p ℓ ^ 2 / (2 * zpc_bX G p ℓ) = p.lam ^ 2 / 2 :=
  zpc_level_sq_div (zpc_bX_pos hG hθZ ℓ)

/-- `a_Y(ℓ)² / (2 b_Y(ℓ)) = lam²/2`. -/
theorem zpc_aY_sq_div {p : zpc_Par} (hG : G.Valid) (ℓ : ℕ) :
    zpc_aY G p ℓ ^ 2 / (2 * zpc_bY G ℓ) = p.lam ^ 2 / 2 :=
  zpc_level_sq_div (zpc_bY_pos hG ℓ)

/-- `a_Z² / (2 b_Z) = lam²/2`. -/
theorem zpc_aZ_sq_div {p : zpc_Par} (hG : G.Valid) (hθZ : 0 < p.θZ) :
    zpc_aZ G p ^ 2 / (2 * zpc_bZ G p) = p.lam ^ 2 / 2 :=
  zpc_level_sq_div (zpc_bZ_pos hG hθZ)

/-- With `lam = N^{ξ/4}`: `lam²/2 = N^{ξ/2}/2`. -/
theorem zpc_lam_rpow_sq (N ξ ζ Lmax Cm : ℝ) (Lg : ℕ) (hN : 0 ≤ N) :
    (zpc_parRpow N ξ ζ Lmax Cm Lg).lam ^ 2 / 2 = N ^ (ξ / 2) / 2 := by
  simp only [zpc_parRpow]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN]
  norm_num
  ring_nf

end BlockBand.Native.CEH.ETH
