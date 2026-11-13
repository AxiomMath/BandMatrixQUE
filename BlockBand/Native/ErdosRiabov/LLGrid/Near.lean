module

public import BlockBand.Native.ErdosRiabov.LLGrid.Tail

/-!
# The (LL) functional between grid points (deterministic)

Grid exponent `C = llCg d = 3 (F + 80)`, `F = Grid.zigF d` (the floor exponent), mesh
`h = N^{-C}` (`VS.meshPow`), modulus level `δ = N^{-C/3}` (`Grid.modulusEvent p C`).
`llCg d ≥ Grid.vsCg d`, so the side conditions of `Grid.zig_conditions` hold for `N ≥ zigN0 d`.

* `absorb_real`: the additive error of `llQ_sub_le` at mesh `h` is at most the floor `φ`;
* **`llQ_le_of_grid`**: for `N ≥ zigN0 d`, times `s ≤ t ≤ s + h`, `t ≤ 1`, Hermitian `H, H'`
  with `|(H - H')_{ab}| ≤ N^{-C/3}`, `G ≥ 0`:
  `llQ_s(H')(y) ≤ G L_s^β s^av_s(y) → llQ_t(H)(y) ≤ (2G + 1) L_t^β s^av_t(y)`
  (`llQ_sub_le`, the floor `Grid.PsiData.normAv_floor`, the ratio `Grid.PsiData.norm_le_mul`,
  `Grid.factor_le_two`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.LLGrid

open Set Function Matrix
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Circ
open scoped NNReal ComplexConjugate

/-- The grid exponent `C = 3 (F + 80)`, `F = zigF d`. -/
def llCg (d : VSData) : ℝ := 3 * (Grid.zigF d + 80)

/-- `F = zigF d = 16 D'' + 10`. -/
theorem zigF_eq (d : VSData) : Grid.zigF d = 16 * d.Dpp + 10 := by
  unfold Grid.zigF vsK
  push_cast
  ring

/-- `C = llCg d > 0`, `C ≥ vsCg d`, `F ≥ 0`, `C - F ≥ F + 37`. -/
theorem llCg_facts (d : VSData) :
    0 < llCg d ∧ Grid.vsCg d ≤ llCg d ∧ 0 ≤ Grid.zigF d ∧
      Grid.zigF d + 33 + 4 ≤ llCg d - Grid.zigF d := by
  have h := Grid.Dpp_nonneg d
  have hF := zigF_eq d
  unfold llCg Grid.vsCg
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Absorption of the additive error** (pure real arithmetic). -/
theorem absorb_real {Nr h r y M eL φ τ : ℝ} (hN2 : 2 ≤ Nr) (hr0 : 0 ≤ r) (hr : r ≤ Nr)
    (hy0 : 0 ≤ y) (hy : y + 1 ≤ Nr) (hM0 : 0 ≤ M) (hM : M ≤ 2 * Nr ^ 27) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ h) (hh : 16 * Nr ^ 33 * h ≤ φ) (heL0 : 0 ≤ eL) (heL : Nr ^ 5 * eL ≤ φ / 2) :
    τ * (2 * (y + 1)) * (r ^ 2 * M) +
      (y + 1) ^ 2 * (2 * Nr * r * (τ * r ^ 2) * M + r ^ 2 * (Nr * eL)) ≤ φ := by
  have hN0 : 0 ≤ Nr := by linarith
  have hN1 : 1 ≤ Nr := by linarith
  have hh0 : 0 ≤ h := hτ0.trans hτ
  have hA : τ * (2 * (y + 1)) * (r ^ 2 * M) ≤ h * (2 * Nr) * (Nr ^ 2 * (2 * Nr ^ 27)) := by
    gcongr
  have hB : (y + 1) ^ 2 * (2 * Nr * r * (τ * r ^ 2) * M) ≤
      Nr ^ 2 * (2 * Nr * Nr * (h * Nr ^ 2) * (2 * Nr ^ 27)) := by
    gcongr
  have hC : (y + 1) ^ 2 * (r ^ 2 * (Nr * eL)) ≤ Nr ^ 2 * (Nr ^ 2 * (Nr * eL)) := by
    gcongr
  have h30 : Nr ^ 30 ≤ Nr ^ 33 := pow_le_pow_right₀ hN1 (by norm_num)
  have e1 : h * (2 * Nr) * (Nr ^ 2 * (2 * Nr ^ 27)) = 4 * h * Nr ^ 30 := by ring
  have e2 : Nr ^ 2 * (2 * Nr * Nr * (h * Nr ^ 2) * (2 * Nr ^ 27)) = 4 * h * Nr ^ 33 := by ring
  have e3 : Nr ^ 2 * (Nr ^ 2 * (Nr * eL)) = Nr ^ 5 * eL := by ring
  have h4 : 4 * h * Nr ^ 30 ≤ 4 * h * Nr ^ 33 := by gcongr
  nlinarith

/-- The crude bound of `𝒳` in powers of `N`: `N c^k + N B^{2(k-1)-1} ≤ 2 N^{27}` for
`c ≤ N`, `B ≤ N²`, `1 ≤ k ≤ 8`. -/
theorem crude_le_pow {Nr c B : ℝ} (hN1 : 1 ≤ Nr) (hc0 : 0 ≤ c) (hc : c ≤ Nr) (hB0 : 0 ≤ B)
    (hB : B ≤ Nr ^ 2) {k : ℕ} (hk : k ≤ 8) :
    Nr * c ^ k + Nr * B ^ (2 * (k - 1) - 1) ≤ 2 * Nr ^ 27 := by
  have hN0 : 0 ≤ Nr := by linarith
  have e1 : c ^ k ≤ Nr ^ 26 :=
    (pow_le_pow_left₀ hc0 hc _).trans (pow_le_pow_right₀ hN1 (by omega))
  have e2 : B ^ (2 * (k - 1) - 1) ≤ Nr ^ 26 := by
    calc B ^ (2 * (k - 1) - 1) ≤ (Nr ^ 2) ^ (2 * (k - 1) - 1) := pow_le_pow_left₀ hB0 hB _
      _ = Nr ^ (2 * (2 * (k - 1) - 1)) := (pow_mul _ _ _).symm
      _ ≤ Nr ^ 26 := pow_le_pow_right₀ hN1 (by omega)
  calc Nr * c ^ k + Nr * B ^ (2 * (k - 1) - 1) ≤ Nr * Nr ^ 26 + Nr * Nr ^ 26 :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hN0) (mul_le_mul_of_nonneg_left e2 hN0)
    _ = 2 * Nr ^ 27 := by ring

/-- `N^5 e ≤ φ/2` from `e ≤ N^{-8} φ`, `N ≥ 2`. -/
theorem pow_five_mul_le {Nr e φ : ℝ} (hN2 : 2 ≤ Nr) (hφ : 0 ≤ φ)
    (he : e ≤ Nr ^ (-(8 : ℝ)) * φ) : Nr ^ 5 * e ≤ φ / 2 := by
  have hNr0 : 0 < Nr := by linarith
  have e0 : Nr ^ 5 * Nr ^ (-(8 : ℝ)) = (Nr ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hNr0,
      show ((5 : ℕ) : ℝ) + -8 = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hNr0.le,
      Real.rpow_natCast]
  have h3 : (2 : ℝ) ≤ Nr ^ 3 :=
    hN2.trans ((pow_one Nr).symm.le.trans (pow_le_pow_right₀ (by linarith) (by norm_num)))
  have h5 : Nr ^ 5 * Nr ^ (-(8 : ℝ)) ≤ 1 / 2 := by
    rw [e0, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h3
  calc Nr ^ 5 * e ≤ Nr ^ 5 * (Nr ^ (-(8 : ℝ)) * φ) :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = (Nr ^ 5 * Nr ^ (-(8 : ℝ))) * φ := by ring
    _ ≤ 1 / 2 * φ := mul_le_mul_of_nonneg_right h5 hφ
    _ = φ / 2 := by ring

/-- `16 N^{33} N^{-C} ≤ φ` from `N^{-F} ≤ φ`, `C - 33 - F ≥ 4`, `N ≥ 2`. -/
theorem mesh_le_floor {Nr C F φ : ℝ} (hN2 : 2 ≤ Nr) (hCF : 4 ≤ C - 33 - F)
    (hφF : Nr ^ (-F) ≤ φ) : 16 * Nr ^ 33 * Nr ^ (-C) ≤ φ := by
  have hNr0 : 0 < Nr := by linarith
  have hN1 : 1 ≤ Nr := by linarith
  have h16 : (16 : ℝ) ≤ Nr ^ (C - 33 - F) := by
    calc (16 : ℝ) = 2 ^ (4 : ℝ) := by norm_num
      _ ≤ Nr ^ (4 : ℝ) := Real.rpow_le_rpow (by norm_num) hN2 (by norm_num)
      _ ≤ Nr ^ (C - 33 - F) := Real.rpow_le_rpow_of_exponent_le hN1 hCF
  have e : Nr ^ (C - 33 - F) * (Nr ^ 33 * Nr ^ (-C)) = Nr ^ (-F) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hNr0, ← Real.rpow_add hNr0]
    congr 1
    push_cast
    ring
  have h0 : 0 ≤ Nr ^ 33 * Nr ^ (-C) := by positivity
  calc 16 * Nr ^ 33 * Nr ^ (-C) = 16 * (Nr ^ 33 * Nr ^ (-C)) := by ring
    _ ≤ Nr ^ (C - 33 - F) * (Nr ^ 33 * Nr ^ (-C)) := mul_le_mul_of_nonneg_right h16 h0
    _ = Nr ^ (-F) := e
    _ ≤ φ := hφF

section Near

variable (d : VSData) {p : BlockBand.Parameters} (P : PsiData (p.n * p.W)) (hPW : P.W = p.W)
  (hPD : P.D = d.D) (hS : StochasticSymm P.S)
  (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z)
  (hN0 : Grid.zigN0 d ≤ ((p.n * p.W : ℕ) : ℝ))

include hz hN0 in

/-- `Im z + 1 ≤ N` for `N ≥ zigN0 d`. -/
theorem im_add_one_le : P.z.im + 1 ≤ ((p.n * p.W : ℕ) : ℝ) := by
  have h1 : P.z.im ≤ d.C0 := (Complex.im_le_norm _).trans hz.2.2
  have h2 : 7 * (d.C0 + 1) ^ 2 + 2 ≤ ((p.n * p.W : ℕ) : ℝ) := by
    refine le_trans ?_ hN0
    unfold Grid.zigN0
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have h3 : 1 ≤ d.C0 := d.C0_ge_one
  nlinarith

include hz hN0 in

/-- The `𝒳`-error at mesh `N^{-C}`, level `N^{-C/3}` (`C = llCg d`): for `|t - s| ≤ N^{-C}`,
`errLip_k(N^{-C/3}, |t - s|, B) ≤ N^{-8} φ` (`B = zigB`, `φ = zigFloor`). -/
theorem errLip_le_floor {n : ℕ} (hn : n + 4 ≤ 8) {τ : ℝ}
    (hτ : τ ≤ ((p.n * p.W : ℕ) : ℝ) ^ (-llCg d)) :
    (Grid.PsiData.errLip P) (n + 2 + 2) (((p.n * p.W : ℕ) : ℝ) ^ (-llCg d / 3)) τ
        (Grid.zigB d (n + 2 + 2) (p.n * p.W)) ≤
      ((p.n * p.W : ℕ) : ℝ) ^ (-(8 : ℝ)) * Grid.zigFloor d P.z (p.n * p.W) := by
  have hNpos : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hzi := hz.im_pos hNpos
  have h17 := Grid.zigN0_ge d
  have hN1 : (1 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := by linarith
  have hNr0 : (0 : ℝ) < ((p.n * p.W : ℕ) : ℝ) := by linarith
  obtain ⟨hB2, -, hBN, hφ, hφF, hzN, -, hNk, -, -⟩ :=
    Grid.zig_conditions d hN0 hz (k := n + 2 + 2) (by omega) (by omega)
  obtain ⟨hC0, -, -, -⟩ := llCg_facts d
  have hφ' : 0 < ((p.n * p.W : ℕ) : ℝ) ^ (-(6 : ℝ)) * Grid.zigFloor d P.z (p.n * p.W) :=
    mul_pos (Real.rpow_pos_of_pos hNr0 _) hφ
  have hφ'F : ((p.n * p.W : ℕ) : ℝ) ^ (-(Grid.zigF d + 6)) ≤
      ((p.n * p.W : ℕ) : ℝ) ^ (-(6 : ℝ)) * Grid.zigFloor d P.z (p.n * p.W) := by
    rw [show -(Grid.zigF d + 6) = -(6 : ℝ) + -Grid.zigF d by ring, Real.rpow_add hNr0]
    exact mul_le_mul_of_nonneg_left hφF (Real.rpow_pos_of_pos hNr0 _).le
  have hk8 : ((n + 2 + 2 : ℕ) : ℝ) ≤ 8 := by exact_mod_cast hn
  have hCg' : ((n + 2 + 2 : ℕ) : ℝ) + 4 + 4 * (((n + 2 + 2 : ℕ) : ℝ) - 1) * 2 +
      (Grid.zigF d + 6) + 3 ≤ llCg d / 3 := by
    unfold llCg
    linarith
  have hB0 : 0 ≤ Grid.zigB d (n + 2 + 2) (p.n * p.W) := by linarith
  have herr := (Grid.PsiData.errLip_div_le_inv P) hN1 hzi hzN hB0 hBN (by norm_num) hφ' hφ'F
    hC0.le (by omega : 1 ≤ n + 2 + 2) hCg' hNk
  have h1 := (Grid.PsiData.errLip_mono P) (n + 2 + 2)
    (δ := ((p.n * p.W : ℕ) : ℝ) ^ (-llCg d / 3)) hτ hB0
  have h2 := (div_le_iff₀ hφ').mp herr
  calc _ ≤ _ := h1
    _ ≤ ((p.n * p.W : ℕ) : ℝ) ^ (-(2 : ℝ)) *
        (((p.n * p.W : ℕ) : ℝ) ^ (-(6 : ℝ)) * Grid.zigFloor d P.z (p.n * p.W)) := h2
    _ = ((p.n * p.W : ℕ) : ℝ) ^ (-(8 : ℝ)) * Grid.zigFloor d P.z (p.n * p.W) := by
        rw [← mul_assoc, ← Real.rpow_add hNr0]
        norm_num

include hPW hPD hz hN0 in

/-- The normalizations at `s ≤ t ≤ s + N^{-C}` (`C = llCg d`):
`L_s^β s^av_s(y) ≤ 2 L_t^β s^av_t(y)`. -/
theorem norm_ratio_le_two {n : ℕ} (hn : n + 4 ≤ 8) {s t : ℝ} (hs1 : s ≤ 1) (ht1 : t ≤ 1)
    (hdt : |t - s| ≤ ((p.n * p.W : ℕ) : ℝ) ^ (-llCg d)) (y : Fin (n + 2 + 2) → Fin (p.n * p.W)) :
    P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s ≤
      2 * (P.lEta t ^ Expo.lossBeta (n + 4) * P.sAv y t) := by
  have hNpos : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hzi := hz.im_pos hNpos
  have hD : 0 ≤ P.D := by rw [hPD]; linarith [d.D_ge_six]
  have h17 := Grid.zigN0_ge d
  have hN1 : (1 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := by linarith
  obtain ⟨-, -, -, -, -, -, -, -, hqE, -⟩ :=
    Grid.zig_conditions d hN0 hz (k := n + 2 + 2) (by omega) (by omega)
  obtain ⟨-, hCv, -, -⟩ := llCg_facts d
  have hβ := Grid.lossBeta_mem (k := n + 2 + 2) hn
  have hsy := P.sAv_pos hNpos hW hzi hs1 y
  have hty := P.sAv_pos hNpos hW hzi ht1 y
  have hrat := (Grid.PsiData.norm_le_mul P) hNpos hW hzi hs1 ht1 hβ.1 hβ.2 hsy.le hty.le
    ((Grid.PsiData.sAv_le_mul P) hNpos hW hzi hD (by omega : 1 ≤ n + 2 + 2) hs1 ht1 y)
  have hq2 : (1 + |s - t| / P.z.im) ^ Grid.normExp (n + 2 + 2) P.D ≤ 2 := by
    refine Grid.factor_le_two (div_nonneg (abs_nonneg _) hzi.le) (Grid.normExp_nonneg _ hD) ?_
    rw [abs_sub_comm, hPD]
    have hhv : ((p.n * p.W : ℕ) : ℝ) ^ (-llCg d) ≤ ((p.n * p.W : ℕ) : ℝ) ^ (-Grid.vsCg d) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    calc |t - s| / P.z.im * Grid.normExp (n + 2 + 2) d.D
        ≤ ((p.n * p.W : ℕ) : ℝ) ^ (-Grid.vsCg d) / P.z.im * Grid.normExp (n + 2 + 2) d.D := by
          gcongr
          · exact Grid.normExp_nonneg _ (by linarith [d.D_ge_six])
          · exact hdt.trans hhv
      _ ≤ 1 / 2 := hqE
  have hLt0 : 0 ≤ P.lEta t ^ Expo.lossBeta (n + 4) * P.sAv y t :=
    mul_nonneg (Real.rpow_nonneg (P.lEta_pos hNpos hW hzi ht1).le _) hty.le
  exact hrat.trans (mul_le_mul_of_nonneg_right hq2 hLt0)

include hPW hPD hz hN0 in

/-- The floor `φ = zigFloor d z N ≤ L_t^β s^av_t(y)` on `[0,1]`. -/
theorem floor_le_norm {n : ℕ} (hn : n + 4 ≤ 8) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (σ : Fin (n + 2 + 2) → Bool) (y : Fin (n + 2 + 2) → Fin (p.n * p.W)) :
    Grid.zigFloor d P.z (p.n * p.W) ≤ P.lEta t ^ Expo.lossBeta (n + 4) * P.sAv y t := by
  have hNpos : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hWN : p.W ≤ p.n * p.W := Nat.le_mul_of_pos_left _ (by have := p.n_ge_four; omega)
  have hD : 0 ≤ P.D := by rw [hPD]; linarith [d.D_ge_six]
  obtain ⟨-, -, -, -, -, -, -, -, -, hNA⟩ :=
    Grid.zig_conditions d hN0 hz (k := n + 2 + 2) (by omega) (by omega)
  have hDpp : (vsK : ℝ) * (2 + P.D) + 1 ≤ (vsK : ℝ) * (2 * d.Dpp + 1) := by
    rw [hPD]; exact floor_exponent_le_of_vsData d
  have hNA' : (1 + Real.sqrt (d.C0 + 1)) ^ ((vsK : ℝ) * (2 + P.D)) ≤
      ((p.n * p.W : ℕ) : ℝ) := by
    rw [hPD]; exact hNA
  exact (Grid.PsiData.normAv_floor P) hNpos p.W_pos hWN d.kappa_pos
    (by linarith [d.C0_ge_one]) hD hz hPW (by omega : 1 ≤ n + 2 + 2) (by unfold vsK; omega)
    hDpp hNA' t ht (σ, y)

include hPW hPD hS hz hN0

/-- **The (LL) functional between grid points** (deterministic). For `N ≥ zigN0 d`, `k = n + 4`,
times `s ≤ t ≤ s + N^{-C}`, `t ≤ 1` (`C = llCg d`), Hermitian `H, H'` with
`|(H - H')_{ab}| ≤ N^{-C/3}`, `G ≥ 0`: if `llQ_s(H')(y) ≤ G L_s^β s^av_s(y)` then
`llQ_t(H)(y) ≤ (2G + 1) L_t^β s^av_t(y)`. -/
theorem llQ_le_of_grid {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool) {s t : ℝ≥0}
    (hst : s ≤ t) (hts : t ≤ s + VS.meshPow ((p.n * p.W : ℕ) : ℝ) (llCg d)) (ht1 : t ≤ 1)
    {H H' : Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ} (hH : H.IsHermitian)
    (hH' : H'.IsHermitian)
    (hδ : ∀ a b, ‖(H - H') a b‖ ≤ ((p.n * p.W : ℕ) : ℝ) ^ (-llCg d / 3)) {G : ℝ} (hG : 0 ≤ G)
    (y : Fin (n + 2 + 2) → Fin (p.n * p.W))
    (hgrid : llQ P σ s H' y ≤ G * (P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s)) :
    llQ P σ t H y ≤ (2 * G + 1) * (P.lEta t ^ Expo.lossBeta (n + 4) * P.sAv y t) := by
  have hNpos : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hzi := hz.im_pos hNpos
  have h17 := Grid.zigN0_ge d
  have hN2 : (2 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := by linarith
  have hNr0 : (0 : ℝ) < ((p.n * p.W : ℕ) : ℝ) := by linarith
  obtain ⟨hB2, hBL, hBN, hφ, hφF, hzN, -, -, -, -⟩ :=
    Grid.zig_conditions d hN0 hz (k := n + 2 + 2) (by omega) (by omega)
  obtain ⟨-, -, hF0, hCF⟩ := llCg_facts d
  have hmesh : (VS.meshPow ((p.n * p.W : ℕ) : ℝ) (llCg d) : ℝ) =
      ((p.n * p.W : ℕ) : ℝ) ^ (-llCg d) := VS.meshPow_coe hNr0.le _
  have hs1 : (s : ℝ) ≤ 1 := by exact_mod_cast hst.trans ht1
  have ht1' : (t : ℝ) ≤ 1 := by exact_mod_cast ht1
  have htI : (t : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨NNReal.coe_nonneg t, ht1'⟩
  have hdt : |(t : ℝ) - s| ≤ ((p.n * p.W : ℕ) : ℝ) ^ (-llCg d) := by
    have h1 : (t : ℝ) ≤ s + ((p.n * p.W : ℕ) : ℝ) ^ (-llCg d) := by
      rw [← hmesh]
      exact_mod_cast hts
    have h2 : (s : ℝ) ≤ t := by exact_mod_cast hst
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hB0 : 0 ≤ Grid.zigB d (n + 2 + 2) (p.n * p.W) := by linarith
  have hBN' : Grid.zigB d (n + 2 + 2) (p.n * p.W) ≤ ((p.n * p.W : ℕ) : ℝ) ^ 2 := by
    rw [← Real.rpow_two]; exact hBN
  have hMb : ∀ y', ‖P.avErr σ y' t H‖ ≤ ((p.n * p.W : ℕ) : ℝ) * (max 1 P.z.im⁻¹) ^ (n + 2 + 2) +
      ((p.n * p.W : ℕ) : ℝ) * Grid.zigB d (n + 2 + 2) (p.n * p.W) ^ (2 * (n + 2 + 2 - 1) - 1) :=
    fun y' => norm_avErr_le P hzi hS σ y' hH hB2 hBL htI
  have hM27 := crude_le_pow (by linarith) (le_trans zero_le_one (le_max_left _ _))
    (max_le (by linarith) hzN) hB0 hBN' (k := n + 2 + 2) hn
  have hsub := llQ_sub_le P hNpos hz hS σ hH hH' hδ hB2 hBL htI ⟨NNReal.coe_nonneg s, hs1⟩ hMb y
  have herr := errLip_le_floor d P hz hN0 hn hdt
  have heL := pow_five_mul_le hN2 hφ.le herr
  have hhφ := mesh_le_floor (C := llCg d) hN2 (by linarith) hφF
  have habs := absorb_real hN2 (inv_nonneg.2 hzi.le) hzN hzi.le (im_add_one_le d P hz hN0)
    ((norm_nonneg _).trans (hMb y)) hM27 (abs_nonneg _) hdt hhφ
    ((Grid.PsiData.errLip_nonneg P) _ (Real.rpow_nonneg hNr0.le _) (abs_nonneg _) hB0) heL
  have hQ : llQ P σ t H y ≤ llQ P σ s H' y + Grid.zigFloor d P.z (p.n * p.W) := by
    have := (abs_le.mp (hsub.trans habs)).2
    linarith
  have hratio := norm_ratio_le_two d P hPW hPD hz hN0 hn hs1 ht1'
    hdt y
  have hfl := floor_le_norm d P hPW hPD hz hN0 hn htI σ y
  calc llQ P σ t H y ≤ llQ P σ s H' y + Grid.zigFloor d P.z (p.n * p.W) := hQ
    _ ≤ G * (2 * (P.lEta t ^ Expo.lossBeta (n + 4) * P.sAv y t)) +
          P.lEta t ^ Expo.lossBeta (n + 4) * P.sAv y t :=
        add_le_add (hgrid.trans (mul_le_mul_of_nonneg_left hratio hG)) hfl
    _ = (2 * G + 1) * (P.lEta t ^ Expo.lossBeta (n + 4) * P.sAv y t) := by ring

end Near

end BlockBand.Native.ErdosRiabov.LLGrid
