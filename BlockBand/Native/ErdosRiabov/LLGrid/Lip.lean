module

public import BlockBand.Native.ErdosRiabov.Circ.RemEvent
public import BlockBand.Native.ErdosRiabov.Grid.Zig

/-!
# The (LL) functional at nearby times (deterministic)

Setting: `P : PsiData N`, `N ≥ 1`, `z ∈ 𝒟` (`BulkDomain`), `S` stochastic symmetric,
`T̂_t = vsKernel S m m̄ t` (`m = m(z)`), `r = (Im z)⁻¹`, times in `[0,1]`.

* `kernel_entry_le`, `kernel_rowSum_le`: `|T̂_t(a,b)| ≤ r` and `Σ_b |T̂_t(a,b)| ≤ r`
  (`T̂_t ≥ 0`, row sums `Im m/η_t`, `vsKernel_theta`);
* `kernel_sub_le`: `|T̂_t(a,b) - T̂_s(a,b)| ≤ |t - s| r²` (resolvent identity `vsKernel_sub`);
* `norm_circSlot_le`, `norm_circSlot_sub_le`: one-slot actions, sup bounds;
* `norm_gChain_le`, `norm_avErr_le`: the crude bound `|𝒳_t(x)| ≤ N c^k + N B^{2(k-1)-1}`,
  `c = max 1 r`;
* `llQ`: the (LL) functional `η_s² |T̂^{(k-2)}_s T̂^{(k)}_s[𝒳_s(H)](y)|` (the body of
  `Circ.circLLEvent`); **`llQ_sub_le`**: for Hermitian `H, H'` with entries of `H - H'` at most
  `δ` and `|𝒳_t(H)| ≤ M`:
  `|llQ_t(H) - llQ_s(H')| ≤ 2(Im z + 1)|t - s| r² M +`
  `(Im z + 1)² (2 N r (|t - s| r²) M + r² N errLip(δ, |t - s|))`.
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
open scoped ComplexConjugate Matrix.Norms.L2Operator

variable {N : ℕ}

/-! ### One-slot actions -/

/-- Sup bound for a one-slot action. -/
theorem norm_circSlot_le {k : ℕ} (i : Fin k) (K : Matrix (Fin N) (Fin N) ℂ) {R M : ℝ}
    (hK : ∀ a, ∑ c, ‖K a c‖ ≤ R) (hM0 : 0 ≤ M) (f : CircFun N k) (hf : ∀ x, ‖f x‖ ≤ M)
    (x : Fin k → Fin N) : ‖circSlot i K f x‖ ≤ R * M := by
  rw [circSlot_apply]
  calc ‖∑ c, K (x i) c * f (update x i c)‖ ≤ ∑ c, ‖K (x i) c‖ * M := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)
    _ = (∑ c, ‖K (x i) c‖) * M := by rw [Finset.sum_mul]
    _ ≤ R * M := mul_le_mul_of_nonneg_right (hK _) hM0

/-- Difference of two one-slot actions. -/
theorem norm_circSlot_sub_le {k : ℕ} (i : Fin k) {K K' : Matrix (Fin N) (Fin N) ℂ}
    {ε R M e : ℝ} (hKK : ∀ a c, ‖K a c - K' a c‖ ≤ ε) (hK' : ∀ a, ∑ c, ‖K' a c‖ ≤ R)
    {f g : CircFun N k} (hf : ∀ x, ‖f x‖ ≤ M) (hfg : ∀ x, ‖f x - g x‖ ≤ e) (he : 0 ≤ e)
    (x : Fin k → Fin N) :
    ‖circSlot i K f x - circSlot i K' g x‖ ≤ N * ε * M + R * e := by
  rw [circSlot_apply, circSlot_apply, ← Finset.sum_sub_distrib]
  have hterm : ∀ c, ‖K (x i) c * f (update x i c) - K' (x i) c * g (update x i c)‖ ≤
      ε * M + ‖K' (x i) c‖ * e := by
    intro c
    have e1 : K (x i) c * f (update x i c) - K' (x i) c * g (update x i c) =
        (K (x i) c - K' (x i) c) * f (update x i c) +
          K' (x i) c * (f (update x i c) - g (update x i c)) := by ring
    rw [e1]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul (hKK _ _) (hf _) (norm_nonneg _) ((norm_nonneg _).trans (hKK (x i) c))
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hfg _) (norm_nonneg _)
  calc _ ≤ ∑ c, (ε * M + ‖K' (x i) c‖ * e) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => hterm c)
    _ = N * (ε * M) + (∑ c, ‖K' (x i) c‖) * e := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Finset.sum_mul]
    _ ≤ N * ε * M + R * e := by
        rw [← mul_assoc]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (hK' _) he)

/-! ### The saturated kernel: size and time-Lipschitz bound -/

section Kernel

variable {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S) (hN : 0 < N) {δ₀ κ C₀ : ℝ}
  {z : ℂ} (hz : BulkDomain N δ₀ κ C₀ z)
include hS hN hz

/-- `‖T̂_t(a,b)‖ = Re T̂_t(a,b)` and the row sums `Σ_b ‖T̂_t(a,b)‖ = Im m/η_t`. -/
theorem kernel_rowSum_eq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a : Fin N) :
    ∑ b, ‖vsKernel S (semicircleM z) (conj (semicircleM z)) t a b‖ =
      (semicircleM z).im / vsHeight z t := by
  have hθ := vsKernel_theta hS hN hz ht0 ht1 ht0 ht1
  have hnorm : ∀ b, ‖vsKernel S (semicircleM z) (conj (semicircleM z)) t a b‖ =
      (vsKernel S (semicircleM z) (conj (semicircleM z)) t a b).re := fun b =>
    (Complex.abs_re_eq_norm.mpr (hθ.2.1 a b).1).symm.trans (abs_of_nonneg (hθ.2.1 a b).2)
  have h := congrArg Complex.re (hθ.2.2.1 a)
  rw [Complex.re_sum, Complex.ofReal_re] at h
  simp_rw [hnorm]
  exact h

/-- Row sums of `|T̂_t|` are at most `(Im z)⁻¹`. -/
theorem kernel_rowSum_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a : Fin N) :
    ∑ b, ‖vsKernel S (semicircleM z) (conj (semicircleM z)) t a b‖ ≤ z.im⁻¹ := by
  rw [kernel_rowSum_eq hS hN hz ht0 ht1 a]
  have hzi := hz.im_pos hN
  have hm1 : (semicircleM z).im ≤ 1 :=
    (Complex.im_le_norm _).trans (norm_semicircleM_lt_one hzi.ne').le
  have hη := Grid.im_le_vsHeight hzi ht1
  have hη0 : 0 < vsHeight z t := hzi.trans_le hη
  calc (semicircleM z).im / vsHeight z t ≤ 1 / vsHeight z t :=
        div_le_div_of_nonneg_right hm1 hη0.le
    _ ≤ 1 / z.im := one_div_le_one_div_of_le hzi hη
    _ = z.im⁻¹ := one_div _

/-- Entries of `|T̂_t|` are at most `(Im z)⁻¹`. -/
theorem kernel_entry_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a b : Fin N) :
    ‖vsKernel S (semicircleM z) (conj (semicircleM z)) t a b‖ ≤ z.im⁻¹ :=
  (Finset.single_le_sum (fun c _ => norm_nonneg
    (vsKernel S (semicircleM z) (conj (semicircleM z)) t a c)) (Finset.mem_univ b)).trans
    (kernel_rowSum_le hS hN hz ht0 ht1 a)

/-- **Time-Lipschitz bound of `T̂`**: `|T̂_t(a,b) - T̂_s(a,b)| ≤ |t - s| (Im z)⁻²` (resolvent
identity `T̂_t - T̂_s = (t - s) T̂_t T̂_s`). -/
theorem kernel_sub_le {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (a b : Fin N) :
    ‖vsKernel S (semicircleM z) (conj (semicircleM z)) t a b -
        vsKernel S (semicircleM z) (conj (semicircleM z)) s a b‖ ≤ |t - s| * z.im⁻¹ ^ 2 := by
  have hzi := hz.im_pos hN
  have hm1 : ‖semicircleM z‖ < 1 := norm_semicircleM_lt_one hzi.ne'
  have hmc : ‖conj (semicircleM z)‖ < 1 := by rwa [Complex.norm_conj]
  have hsn := norm_smul_lt_one hm1 hmc hs0 hs1
  have htn := norm_smul_lt_one hm1 hmc ht0 ht1
  rw [← Matrix.sub_apply, vsKernel_sub hS hsn htn, Matrix.smul_apply, smul_eq_mul, norm_mul,
    Matrix.mul_apply, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc ‖∑ c, vsKernel S (semicircleM z) (conj (semicircleM z)) t a c *
        vsKernel S (semicircleM z) (conj (semicircleM z)) s c b‖
      ≤ ∑ c, ‖vsKernel S (semicircleM z) (conj (semicircleM z)) t a c‖ * z.im⁻¹ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (kernel_entry_le hS hN hz hs0 hs1 c b) (norm_nonneg _)
    _ = (∑ c, ‖vsKernel S (semicircleM z) (conj (semicircleM z)) t a c‖) * z.im⁻¹ := by
        rw [Finset.sum_mul]
    _ ≤ z.im⁻¹ * z.im⁻¹ :=
        mul_le_mul_of_nonneg_right (kernel_rowSum_le hS hN hz ht0 ht1 a)
          (inv_nonneg.2 (hz.im_pos hN).le)
    _ = z.im⁻¹ ^ 2 := (sq _).symm

end Kernel

/-! ### A crude bound on `𝒳` -/

/-- `‖G_1 B_1 ⋯ G_k B_k‖ ≤ (max 1 η⁻¹)^k` for `‖B_l‖ ≤ 1`, `|Im w_l| ≥ η`. -/
theorem norm_gChain_le {k : ℕ} {w : Fin k → ℂ} (Bs : Fin k → Matrix (Fin N) (Fin N) ℂ)
    (hBs : ∀ l, ‖Bs l‖ ≤ 1) {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) {η : ℝ}
    (hη : 0 < η) (hw : ∀ l, η ≤ |(w l).im|) : ‖gChain w Bs H‖ ≤ (max 1 η⁻¹) ^ k := by
  unfold gChain Chains.slotProd Chains.slotList
  exact Grid.norm_ofFn_prod_le _ (le_trans zero_le_one (le_max_left _ _)) fun l =>
    (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) (hBs l)).trans
      ((Grid.norm_resolvent_le hH hη (hw l)).trans (le_max_right _ _)))

/-- **Crude bound** `|𝒳_t(x)| ≤ N (max 1 (Im z)⁻¹)^k + N B^{2(k-1)-1}`. -/
theorem norm_avErr_le (P : PsiData N) (hz : 0 < P.z.im) (hS : StochasticSymm P.S) {k : ℕ}
    (σ : Fin k → Bool) (x : Fin k → Fin N) {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    {B : ℝ} (hB2 : 2 ≤ B) (hBL : ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖P.avErr σ x t H‖ ≤ N * (max 1 P.z.im⁻¹) ^ k + N * B ^ (2 * (k - 1) - 1) := by
  unfold Psi.PsiData.avErr
  have hw : ∀ l, P.z.im ≤ |(patZ P.z σ t l).im| := fun l => by
    rw [Grid.abs_im_patZ]
    exact (Grid.im_le_vsHeight hz ht.2).trans (le_abs_self _)
  have hg := norm_gChain_le (avSlots P.S x) (Grid.norm_avSlots_le hS x) hH hz hw
  have hm : ‖P.mChain σ x t‖ ≤ B ^ (2 * (k - 1) - 1) :=
    Grid.chainM_bound (Grid.mHyp_pat hS hz σ x) hB2 hBL ht
  have hsum : ‖∑ a, P.mChain σ x t a * obsSeq P.S x k a‖ ≤ N * B ^ (2 * (k - 1) - 1) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖P.mChain σ x t a * obsSeq P.S x k a‖
        ≤ ∑ _a : Fin N, B ^ (2 * (k - 1) - 1) := Finset.sum_le_sum fun a _ => by
          rw [norm_mul]
          have h1 : ‖P.mChain σ x t a‖ ≤ B ^ (2 * (k - 1) - 1) := (norm_le_pi_norm _ a).trans hm
          have h2 : ‖obsSeq P.S x k a‖ ≤ 1 :=
            (norm_le_pi_norm _ a).trans (Grid.norm_obsSeq_le hS x k)
          calc _ ≤ B ^ (2 * (k - 1) - 1) * 1 :=
                mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
            _ = _ := mul_one _
      _ = N * B ^ (2 * (k - 1) - 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine (norm_sub_le _ _).trans (add_le_add ?_ hsum)
  exact (Grid.norm_trace_le _).trans (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg N))

/-! ### The (LL) functional -/

/-- **The (LL) functional** `η_s² |T̂^{(k-2)}_s T̂^{(k)}_s[𝒳_s(H)](y)|`, `k = n + 4` (the body of
`Circ.circLLEvent`). -/
def llQ (P : PsiData N) {n : ℕ} (σ : Fin (n + 2 + 2) → Bool) (s : ℝ)
    (H : Matrix (Fin N) (Fin N) ℂ) (y : Fin (n + 2 + 2) → Fin N) : ℝ :=
  vsHeight P.z s ^ 2 *
    ‖circSlot ⟨n + 1, by omega⟩ (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
      (circSlot (Fin.last (n + 2 + 1))
        (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
        (fun y => P.avErr σ y s H)) y‖

/-- `η_t ≤ Im z + 1` on `[0,1]`. -/
theorem vsHeight_le_im_add_one {z : ℂ} (hz : 0 < z.im) {t : ℝ} (ht0 : 0 ≤ t) :
    vsHeight z t ≤ z.im + 1 := by
  have hm1 : (semicircleM z).im ≤ 1 :=
    (Complex.im_le_norm _).trans (norm_semicircleM_lt_one hz.ne').le
  have hm0 := semicircleM_im_pos hz
  unfold vsHeight
  nlinarith

/-- **Two-time comparison of the (LL) functional.** For `s, t ∈ [0,1]`, Hermitian `H, H'` with
`|(H - H')_{ab}| ≤ δ`, `|𝒳_t(H)| ≤ M`, `r = (Im z)⁻¹`, `B` as in `Grid.PsiData.norm_avErr_sub_le`:
`|llQ_t(H)(y) - llQ_s(H')(y)| ≤ |t - s| 2(Im z + 1) r² M +`
`(Im z + 1)² (2 N r (|t - s| r²) M + r² (N errLip(δ, |t - s|, B)))`. -/
theorem llQ_sub_le (P : PsiData N) (hN : 0 < N) {δ₀ κ C₀ : ℝ}
    (hz : BulkDomain N δ₀ κ C₀ P.z) (hS : StochasticSymm P.S) {n : ℕ}
    (σ : Fin (n + 2 + 2) → Bool) {H H' : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) {δ : ℝ} (hδ : ∀ a b, ‖(H - H') a b‖ ≤ δ) {B : ℝ} (hB2 : 2 ≤ B)
    (hBL : ((n + 2 + 2 - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B) {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) {M : ℝ}
    (hM : ∀ y, ‖P.avErr σ y t H‖ ≤ M) (y : Fin (n + 2 + 2) → Fin N) :
    |llQ P σ t H y - llQ P σ s H' y| ≤
      |t - s| * (2 * (P.z.im + 1)) * (P.z.im⁻¹ ^ 2 * M) +
        (P.z.im + 1) ^ 2 * (2 * N * P.z.im⁻¹ * (|t - s| * P.z.im⁻¹ ^ 2) * M +
          P.z.im⁻¹ ^ 2 * (N * (Grid.PsiData.errLip P) (n + 2 + 2) δ |t - s| B)) := by
  have hzi := hz.im_pos hN
  set r := P.z.im⁻¹ with hr
  have hr0 : 0 ≤ r := inv_nonneg.2 hzi.le
  set Kt := vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) t
  set Ks := vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s
  set Xt : CircFun N (n + 2 + 2) := fun y => P.avErr σ y t H
  set Xs : CircFun N (n + 2 + 2) := fun y => P.avErr σ y s H'
  set εK := |t - s| * r ^ 2 with hεK
  set eX := (N : ℝ) * (Grid.PsiData.errLip P) (n + 2 + 2) δ |t - s| B with heX
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM fun _ => ⟨0, hN⟩)
  have hεK0 : 0 ≤ εK := by positivity
  have heX0 : 0 ≤ eX := (norm_nonneg _).trans
    ((Grid.PsiData.norm_avErr_sub_le P) hzi hS σ (fun _ => ⟨0, hN⟩) hH hH' hδ hB2 hBL ht hs)
  have hKd : ∀ a c, ‖Kt a c - Ks a c‖ ≤ εK := fun a c =>
    kernel_sub_le hS hN hz hs.1 hs.2 ht.1 ht.2 a c
  have hRt : ∀ a, ∑ c, ‖Kt a c‖ ≤ r := fun a => kernel_rowSum_le hS hN hz ht.1 ht.2 a
  have hRs : ∀ a, ∑ c, ‖Ks a c‖ ≤ r := fun a => kernel_rowSum_le hS hN hz hs.1 hs.2 a
  have hXd : ∀ y, ‖Xt y - Xs y‖ ≤ eX := fun y =>
    (Grid.PsiData.norm_avErr_sub_le P) hzi hS σ y hH hH' hδ hB2 hBL ht hs
  -- the inner action
  have hin : ∀ x, ‖circSlot (Fin.last (n + 2 + 1)) Kt Xt x -
      circSlot (Fin.last (n + 2 + 1)) Ks Xs x‖ ≤ N * εK * M + r * eX := fun x =>
    norm_circSlot_sub_le _ hKd hRs hM hXd heX0 x
  have hin0 : ∀ x, ‖circSlot (Fin.last (n + 2 + 1)) Kt Xt x‖ ≤ r * M := fun x =>
    norm_circSlot_le _ Kt hRt hM0 Xt hM x
  have hout := norm_circSlot_sub_le (⟨n + 1, by omega⟩ : Fin (n + 2 + 2)) hKd hRs hin0 hin
    (by positivity) y
  have hout0 := norm_circSlot_le (⟨n + 1, by omega⟩ : Fin (n + 2 + 2)) Kt hRt (by positivity) _
    hin0 y
  set Ft := circSlot (⟨n + 1, by omega⟩ : Fin (n + 2 + 2)) Kt
    (circSlot (Fin.last (n + 2 + 1)) Kt Xt) y
  set Fs := circSlot (⟨n + 1, by omega⟩ : Fin (n + 2 + 2)) Ks
    (circSlot (Fin.last (n + 2 + 1)) Ks Xs) y
  -- heights
  have hηt0 : 0 ≤ vsHeight P.z t := (vsHeight_pos hzi ht.2).le
  have hηs0 : 0 ≤ vsHeight P.z s := (vsHeight_pos hzi hs.2).le
  have hηt1 := vsHeight_le_im_add_one hzi ht.1
  have hηs1 := vsHeight_le_im_add_one hzi hs.1
  have hm1 : (semicircleM P.z).im ≤ 1 :=
    (Complex.im_le_norm _).trans (norm_semicircleM_lt_one hzi.ne').le
  have hm0 := (semicircleM_im_pos hzi).le
  have hdη : |vsHeight P.z t - vsHeight P.z s| ≤ |t - s| := by
    rw [vsHeight_sub, abs_mul, abs_of_nonneg hm0, abs_sub_comm]
    exact mul_le_of_le_one_right (abs_nonneg _) hm1
  have hdη2 : |vsHeight P.z t ^ 2 - vsHeight P.z s ^ 2| ≤ |t - s| * (2 * (P.z.im + 1)) := by
    rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ vsHeight P.z t + vsHeight P.z s),
      mul_comm]
    exact mul_le_mul hdη (by linarith) (by positivity) (abs_nonneg _)
  have hηs2 : vsHeight P.z s ^ 2 ≤ (P.z.im + 1) ^ 2 := pow_le_pow_left₀ hηs0 hηs1 2
  have hnd := abs_norm_sub_norm_le Ft Fs
  have e : llQ P σ t H y - llQ P σ s H' y =
      (vsHeight P.z t ^ 2 - vsHeight P.z s ^ 2) * ‖Ft‖ + vsHeight P.z s ^ 2 * (‖Ft‖ - ‖Fs‖) := by
    unfold llQ
    ring
  rw [e]
  have hF0 : ‖Ft‖ ≤ r * (r * M) := hout0
  calc |(vsHeight P.z t ^ 2 - vsHeight P.z s ^ 2) * ‖Ft‖ +
        vsHeight P.z s ^ 2 * (‖Ft‖ - ‖Fs‖)|
      ≤ |vsHeight P.z t ^ 2 - vsHeight P.z s ^ 2| * ‖Ft‖ +
          vsHeight P.z s ^ 2 * |‖Ft‖ - ‖Fs‖| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_norm, abs_of_nonneg (by positivity : 0 ≤ vsHeight P.z s ^ 2)]
    _ ≤ (|t - s| * (2 * (P.z.im + 1))) * (r * (r * M)) +
          (P.z.im + 1) ^ 2 * (N * εK * (r * M) + r * (N * εK * M + r * eX)) := by
        refine add_le_add (mul_le_mul hdη2 hF0 (norm_nonneg _) (by positivity))
          (mul_le_mul hηs2 (hnd.trans hout) (abs_nonneg _) (by positivity))
    _ = _ := by ring

end BlockBand.Native.ErdosRiabov.LLGrid
