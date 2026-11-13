module

public import BlockBand.Native.ErdosRiabov.Grid.PsiRatio

set_option autoImplicit false

/-!
# `Ψ` at nearby times and matrices

A deterministic comparison of the control quantities `Ψ` at two nearby times and matrices.

Setting: `P : PsiData N` with `N, W ≥ 1`, `Im z > 0`, `S` stochastic
symmetric, `D ≥ 0`; `1 ≤ k ≤ 8`; times `s, t ∈ [0,1]`; Hermitian `H, H'` with entries of
`H - H'` of norm `≤ δ`; `q = 1 + |t - s|/Im z`, `E = normExp k D`, `c = max 1 (Im z)⁻¹`, and
`B ≥ 2`, `B ≥ (k - 1)(1 - |m|²)⁻¹` (`m = m(z)`).

* `lossAlpha_mem`, `lossBeta_mem`: `0 ≤ α_k, β_k ≤ 1` for `k ≤ 8`;
* `PsiData.norm_isoErr_sub_le`: `|𝒴_t(H) - 𝒴_s(H')| ≤ errLip = k c^k (Im z)⁻² (N² δ + |t - s|) +
  B^{4(k-1)} |t - s|`; `PsiData.norm_avErr_sub_le`: `|𝒳_t(H) - 𝒳_s(H')| ≤ N · errLip`;
* `ratio_le`: `|e|/n ≤ G |e'|/n' + |e - e'|/n` if `n' ≤ G n`;
* **`PsiData.bigPsiIso_le_of_near`**, **`PsiData.bigPsiAv_le_of_near`**: if every normalization
  at time `t` is `≥ φ > 0`, then `Ψ^{iso}_t(H) ≤ q^E Ψ^{iso}_s(H') + errLip/φ` and
  `Ψ^{av}_t(H) ≤ q^E Ψ^{av}_s(H') + N errLip/φ`.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Grid

open Matrix Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open scoped Matrix.Norms.L2Operator NNReal

variable {N k : ℕ}

/-!
### Loss exponents
-/

theorem lossAlpha_mem {k : ℕ} (hk : k ≤ 8) : 0 ≤ Expo.lossAlpha k ∧ Expo.lossAlpha k ≤ 1 / 2 := by
  unfold Expo.lossAlpha
  split_ifs
  · norm_num
  · refine ⟨by positivity, ?_⟩
    have hk' : (k : ℝ) ≤ 8 := by exact_mod_cast hk
    have h1 : Real.sqrt (2 * (k : ℝ) / 8 - 1) ≤ 1 := by
      rw [Real.sqrt_le_one]
      linarith
    linarith

theorem lossBeta_mem {k : ℕ} (hk : k ≤ 8) : 0 ≤ Expo.lossBeta k ∧ Expo.lossBeta k ≤ 1 := by
  unfold Expo.lossBeta
  split_ifs with h
  · have := lossAlpha_mem (k := k + 1) (by omega)
    exact ⟨this.1, by linarith⟩
  · have := lossAlpha_mem (k := 5) (by norm_num)
    exact ⟨by linarith, by linarith⟩

/-!
### Ratios and maxima
-/

theorem ratio_le {e e' : ℂ} {n n' G : ℝ} (hn : 0 < n) (hn' : 0 < n')
    (h : n' ≤ G * n) : ‖e‖ / n ≤ G * (‖e'‖ / n') + ‖e - e'‖ / n := by
  have h1 : ‖e‖ ≤ ‖e'‖ + ‖e - e'‖ := by
    have := norm_add_le e' (e - e')
    rwa [add_sub_cancel] at this
  have h2 : ‖e'‖ / n ≤ G * (‖e'‖ / n') := by
    rw [div_le_iff₀ hn, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hn']
    nlinarith [norm_nonneg e']
  calc ‖e‖ / n ≤ (‖e'‖ + ‖e - e'‖) / n := by gcongr
    _ = ‖e'‖ / n + ‖e - e'‖ / n := add_div _ _ _
    _ ≤ _ := by linarith

theorem sup_toNNReal_le {ι : Type} [Fintype ι] (f : ι → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, f i ≤ c) : ((Finset.univ.sup fun i => (f i).toNNReal : ℝ≥0) : ℝ) ≤ c := by
  rw [← Real.coe_toNNReal c hc, NNReal.coe_le_coe]
  exact Finset.sup_le fun i _ => Real.toNNReal_le_toNNReal (h i)

namespace PsiData

variable (P : PsiData N)

/-- The Lipschitz constant of the errors `𝒴` (the factor `N` is added for `𝒳`). -/
def errLip (k : ℕ) (δ τ B : ℝ) : ℝ :=
  k * (max 1 P.z.im⁻¹) ^ k * (P.z.im⁻¹ ^ 2 * ((N : ℝ) ^ 2 * δ + τ)) + B ^ (4 * (k - 1)) * τ

theorem errLip_nonneg (k : ℕ) {δ τ B : ℝ} (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hB : 0 ≤ B) :
    0 ≤ (PsiData.errLip P) k δ τ B := by
  unfold PsiData.errLip
  positivity

theorem norm_mChain_sub_le (hz : 0 < P.z.im) (hS : StochasticSymm P.S) (σ : Fin k → Bool)
    (x : Fin k → Fin N) {B : ℝ} (hB2 : 2 ≤ B)
    (hBL : ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B) {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖P.mChain σ x t - P.mChain σ x s‖ ≤ B ^ (4 * (k - 1)) * |t - s| :=
  chainM_lipschitz (mHyp_pat hS hz σ x) hB2 hBL ht hs

theorem norm_gChain_pat_sub_le (hz : 0 < P.z.im) {Bs : Fin k → Matrix (Fin N) (Fin N) ℂ}
    (hBs : ∀ l, ‖Bs l‖ ≤ 1) (σ : Fin k → Bool) {H H' : Matrix (Fin N) (Fin N) ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) {δ : ℝ} (hδ : ∀ a b, ‖(H - H') a b‖ ≤ δ)
    {t s : ℝ} (ht : t ≤ 1) (hs : s ≤ 1) :
    ‖gChain (patZ P.z σ t) Bs H - gChain (patZ P.z σ s) Bs H'‖ ≤
      k * (max 1 P.z.im⁻¹) ^ k * (P.z.im⁻¹ ^ 2 * ((N : ℝ) ^ 2 * δ + |t - s|)) := by
  have hw : ∀ (r : ℝ), r ≤ 1 → ∀ l, P.z.im ≤ |(patZ P.z σ r l).im| := fun r hr l => by
    rw [abs_im_patZ]
    exact (im_le_vsHeight hz hr).trans (le_abs_self _)
  refine (norm_gChain_sub_le Bs hBs hH hH' hz (hw t ht) (hw s hs)
    (fun l => norm_patZ_sub_le hz.ne' σ t s l)).trans ?_
  gcongr
  exact norm_le_card_sq_mul hδ

theorem norm_isoErr_sub_le (hz : 0 < P.z.im) (hS : StochasticSymm P.S) (σ : Fin k → Bool)
    (a b : Fin N) (x : Fin k → Fin N) {H H' : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) {δ : ℝ} (hδ : ∀ a b, ‖(H - H') a b‖ ≤ δ) {B : ℝ} (hB2 : 2 ≤ B)
    (hBL : ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B) {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖P.isoErr σ a b x t H - P.isoErr σ a b x s H'‖ ≤ (PsiData.errLip P) k δ |t - s| B := by
  unfold Psi.PsiData.isoErr errLip
  have hg := (PsiData.norm_gChain_pat_sub_le P) hz (norm_isoSlots_le hS x) σ hH hH' hδ ht.2 hs.2
  have hm := (PsiData.norm_mChain_sub_le P) hz hS σ x hB2 hBL ht hs
  have e : gChain (patZ P.z σ t) (isoSlots P.S x) H a b -
      (if a = b then P.mChain σ x t a else 0) -
      (gChain (patZ P.z σ s) (isoSlots P.S x) H' a b -
        (if a = b then P.mChain σ x s a else 0)) =
      (gChain (patZ P.z σ t) (isoSlots P.S x) H - gChain (patZ P.z σ s) (isoSlots P.S x) H') a b -
        ((if a = b then P.mChain σ x t a else 0) - (if a = b then P.mChain σ x s a else 0)) := by
    rw [Matrix.sub_apply]
    ring
  rw [e]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_entry_le_opNorm _ a b).trans hg) ?_)
  split_ifs
  · rw [← Pi.sub_apply]
    exact (norm_le_pi_norm _ a).trans hm
  · rw [sub_zero, norm_zero]
    positivity

theorem norm_avErr_sub_le (hz : 0 < P.z.im) (hS : StochasticSymm P.S) (σ : Fin k → Bool)
    (x : Fin k → Fin N) {H H' : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) {δ : ℝ} (hδ : ∀ a b, ‖(H - H') a b‖ ≤ δ) {B : ℝ} (hB2 : 2 ≤ B)
    (hBL : ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B) {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖P.avErr σ x t H - P.avErr σ x s H'‖ ≤ N * (PsiData.errLip P) k δ |t - s| B := by
  unfold Psi.PsiData.avErr errLip
  have hg := (PsiData.norm_gChain_pat_sub_le P) hz (norm_avSlots_le hS x) σ hH hH' hδ ht.2 hs.2
  have hm := (PsiData.norm_mChain_sub_le P) hz hS σ x hB2 hBL ht hs
  have e : Matrix.trace (gChain (patZ P.z σ t) (avSlots P.S x) H) -
      ∑ a, P.mChain σ x t a * obsSeq P.S x k a -
      (Matrix.trace (gChain (patZ P.z σ s) (avSlots P.S x) H') -
        ∑ a, P.mChain σ x s a * obsSeq P.S x k a) =
      Matrix.trace (gChain (patZ P.z σ t) (avSlots P.S x) H -
        gChain (patZ P.z σ s) (avSlots P.S x) H') -
        ∑ a, (P.mChain σ x t a - P.mChain σ x s a) * obsSeq P.S x k a := by
    rw [Matrix.trace_sub]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [e]
  have hsum : ‖∑ a, (P.mChain σ x t a - P.mChain σ x s a) * obsSeq P.S x k a‖ ≤
      N * (B ^ (4 * (k - 1)) * |t - s|) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖(P.mChain σ x t a - P.mChain σ x s a) * obsSeq P.S x k a‖
        ≤ ∑ _a : Fin N, B ^ (4 * (k - 1)) * |t - s| := Finset.sum_le_sum fun a _ => by
          rw [norm_mul]
          have h1 : ‖P.mChain σ x t a - P.mChain σ x s a‖ ≤ B ^ (4 * (k - 1)) * |t - s| := by
            rw [← Pi.sub_apply]
            exact (norm_le_pi_norm _ a).trans hm
          have h2 : ‖obsSeq P.S x k a‖ ≤ 1 :=
            (norm_le_pi_norm _ a).trans (norm_obsSeq_le hS x k)
          calc _ ≤ (B ^ (4 * (k - 1)) * |t - s|) * 1 :=
                mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
            _ = _ := mul_one _
      _ = N * (B ^ (4 * (k - 1)) * |t - s|) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine (norm_sub_le _ _).trans ?_
  have ht' := (norm_trace_le _).trans (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg N))
  rw [mul_add]
  exact add_le_add ht' hsum

/-!
### `Ψ` at nearby times
-/

/-- **Two-time comparison of `Ψ^iso`.** -/
theorem bigPsiIso_le_of_near (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im)
    (hS : StochasticSymm P.S) (hD : 0 ≤ P.D) (hk : 1 ≤ k) (hk8 : k ≤ 8)
    {H H' : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian) {δ : ℝ}
    (hδ : ∀ a b, ‖(H - H') a b‖ ≤ δ) {B : ℝ} (hB2 : 2 ≤ B)
    (hBL : ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B) {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) {φ : ℝ} (hφ : 0 < φ)
    (hfl : ∀ i : IsoIdx N k, φ ≤ P.lEta t ^ Expo.lossAlpha k * P.sIso i.2.1 i.2.2.1 i.2.2.2 t) :
    P.bigPsiIso k t H ≤ (1 + |t - s| / P.z.im) ^ normExp k P.D * P.bigPsiIso k s H' +
      (PsiData.errLip P) k δ |t - s| B / φ := by
  set G := (1 + |t - s| / P.z.im) ^ normExp k P.D
  have hq := PsiData.q_ge_one P hz t s
  have hG : 0 ≤ G := Real.rpow_nonneg (by linarith) _
  have hα := lossAlpha_mem hk8
  have hΛ : 0 ≤ (PsiData.errLip P) k δ |t - s| B :=
    (PsiData.errLip_nonneg P) k ((norm_nonneg _).trans (hδ ⟨0, hN⟩ ⟨0, hN⟩)) (abs_nonneg _)
      (by linarith)
  refine sup_toNNReal_le _ (add_nonneg (mul_nonneg hG (P.bigPsiIso_nonneg s H'))
    (div_nonneg hΛ hφ.le)) fun i => ?_
  obtain ⟨σ, a, b, x⟩ := i
  have hnt : 0 < P.lEta t ^ Expo.lossAlpha k * P.sIso a b x t :=
    mul_pos (Real.rpow_pos_of_pos (P.lEta_pos hN hW hz ht.2) _) (P.sIso_pos hN hW hz ht.2 _ _ _)
  have hns : 0 < P.lEta s ^ Expo.lossAlpha k * P.sIso a b x s :=
    mul_pos (Real.rpow_pos_of_pos (P.lEta_pos hN hW hz hs.2) _) (P.sIso_pos hN hW hz hs.2 _ _ _)
  have hcmp : P.lEta s ^ Expo.lossAlpha k * P.sIso a b x s ≤
      G * (P.lEta t ^ Expo.lossAlpha k * P.sIso a b x t) := by
    have h := PsiData.norm_le_mul P hN hW hz hs.2 ht.2 hα.1 (by linarith [hα.2])
      (P.sIso_pos hN hW hz hs.2 a b x).le (P.sIso_pos hN hW hz ht.2 a b x).le
      (PsiData.sIso_le_mul P hN hW hz hD hk hs.2 ht.2 a b x)
    rwa [abs_sub_comm] at h
  have hr := ratio_le (e := P.isoErr σ a b x t H) (e' := P.isoErr σ a b x s H') hnt hns hcmp
  have hE := (PsiData.norm_isoErr_sub_le P) hz hS σ a b x hH hH' hδ hB2 hBL ht hs
  have hfl' := hfl (σ, a, b, x)
  show P.isoRatio (σ, a, b, x) t H ≤ _
  unfold Psi.PsiData.isoRatio
  refine hr.trans (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_left (P.isoRatio_le_bigPsiIso (σ, a, b, x) s H') hG
  · calc ‖P.isoErr σ a b x t H - P.isoErr σ a b x s H'‖ /
          (P.lEta t ^ Expo.lossAlpha k * P.sIso a b x t)
        ≤ (PsiData.errLip P) k δ |t - s| B / (P.lEta t ^ Expo.lossAlpha k * P.sIso a b x t) := by
          gcongr
      _ ≤ (PsiData.errLip P) k δ |t - s| B / φ := div_le_div_of_nonneg_left hΛ hφ hfl'

/-- **Two-time comparison of `Ψ^av`.** -/
theorem bigPsiAv_le_of_near (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im)
    (hS : StochasticSymm P.S) (hD : 0 ≤ P.D) (hk : 1 ≤ k) (hk8 : k ≤ 8)
    {H H' : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian) {δ : ℝ}
    (hδ : ∀ a b, ‖(H - H') a b‖ ≤ δ) {B : ℝ} (hB2 : 2 ≤ B)
    (hBL : ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B) {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) {φ : ℝ} (hφ : 0 < φ)
    (hfl : ∀ i : AvIdx N k, φ ≤ P.lEta t ^ Expo.lossBeta k * P.sAv i.2 t) :
    P.bigPsiAv k t H ≤ (1 + |t - s| / P.z.im) ^ normExp k P.D * P.bigPsiAv k s H' +
      N * (PsiData.errLip P) k δ |t - s| B / φ := by
  set G := (1 + |t - s| / P.z.im) ^ normExp k P.D
  have hq := PsiData.q_ge_one P hz t s
  have hG : 0 ≤ G := Real.rpow_nonneg (by linarith) _
  have hβ := lossBeta_mem hk8
  have hΛ : 0 ≤ (N : ℝ) * (PsiData.errLip P) k δ |t - s| B :=
    mul_nonneg (Nat.cast_nonneg _)
      ((PsiData.errLip_nonneg P) k ((norm_nonneg _).trans (hδ ⟨0, hN⟩ ⟨0, hN⟩)) (abs_nonneg _)
        (by linarith))
  refine sup_toNNReal_le _ (add_nonneg (mul_nonneg hG (P.bigPsiAv_nonneg s H'))
    (div_nonneg hΛ hφ.le)) fun i => ?_
  obtain ⟨σ, x⟩ := i
  have hnt : 0 < P.lEta t ^ Expo.lossBeta k * P.sAv x t :=
    mul_pos (Real.rpow_pos_of_pos (P.lEta_pos hN hW hz ht.2) _) (P.sAv_pos hN hW hz ht.2 _)
  have hns : 0 < P.lEta s ^ Expo.lossBeta k * P.sAv x s :=
    mul_pos (Real.rpow_pos_of_pos (P.lEta_pos hN hW hz hs.2) _) (P.sAv_pos hN hW hz hs.2 _)
  have hcmp : P.lEta s ^ Expo.lossBeta k * P.sAv x s ≤
      G * (P.lEta t ^ Expo.lossBeta k * P.sAv x t) := by
    have h := PsiData.norm_le_mul P hN hW hz hs.2 ht.2 hβ.1 hβ.2
      (P.sAv_pos hN hW hz hs.2 x).le (P.sAv_pos hN hW hz ht.2 x).le
      (PsiData.sAv_le_mul P hN hW hz hD hk hs.2 ht.2 x)
    rwa [abs_sub_comm] at h
  have hr := ratio_le (e := P.avErr σ x t H) (e' := P.avErr σ x s H') hnt hns hcmp
  have hE := (PsiData.norm_avErr_sub_le P) hz hS σ x hH hH' hδ hB2 hBL ht hs
  have hfl' := hfl (σ, x)
  show P.avRatio (σ, x) t H ≤ _
  unfold Psi.PsiData.avRatio
  refine hr.trans (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_left (P.avRatio_le_bigPsiAv (σ, x) s H') hG
  · calc ‖P.avErr σ x t H - P.avErr σ x s H'‖ / (P.lEta t ^ Expo.lossBeta k * P.sAv x t)
        ≤ N * (PsiData.errLip P) k δ |t - s| B / (P.lEta t ^ Expo.lossBeta k * P.sAv x t) := by
          gcongr
      _ ≤ N * (PsiData.errLip P) k δ |t - s| B / φ := div_le_div_of_nonneg_left hΛ hφ hfl'

end PsiData

end BlockBand.Native.ErdosRiabov.Grid
