module

public import BlockBand.Layers.FreshCountVariance

/-!
# The mean-square comparison of the fresh resolvent trace

Proves the input `FcMeanSquare` of `BlockBand.Layers.FreshCount` (`fcMeanSquare_holds`) of
the fresh-count lemma from `ConditionalBlockGUECount` and `GaussianLpGradient`, and assembles the
lemma: `freshCount_holds (hcount) (hgrad) : FreshCountContract`.

Law: `A = gueOfCoords W τ r`, `r` standard Gaussian (transferred from `GUE_W(c/W)` by
`fcd_integral_gue`), `c = 1 - 2b`; `ε = W^{-3/5}`, `y_t = (1-t)γ + ε`, `γ = c(-Im a) = Im z₀`.

* §1 (deterministic, Hermitian `F`): resolvent bounds and identity, normalized trace
  `fcmTr = W⁻¹ Tr`, Jensen, and `Re⟨R²⟩ ≤ -Im⟨R⟩/Im z - 2(Im⟨R⟩)²` (`fcm_re_tr_sq_le`).
* §2: the scalar map `u ↦ ⟨(w_t(u) - F)⁻¹⟩`, `w_t(u) = z₀ + iε + tc(a - u)`; stability
  `|u - a| min(1, 2cα²)/2 ≤ |u - ⟨M_t(u)⟩| + d + ε/γ²` near `a`, uniformly in `t ∈ [0,1]`
  (`fcm_stability`; "`Re(1 - tcW⁻¹Tr R²) ≥ 1 - t + 2tc(Im a)² - Cd`").
* §3: Gaussian integration by parts `E g_t - ⟨M_t(E g_t)⟩ = tc Cov(g_t, ⟨M H_t⁻¹⟩)` (`fcm_sd`),
  bounded by the variance (`fcm_sd_error`); continuity of `t ↦ E g_t` and continuation from
  `t = 0` by the intermediate value theorem (`fcm_mean_bound`):
  `|E g_t - a| ≤ C(d + ε + W⁻² y_t⁻³)` once `W^{-1/5} ≤ ρ₀` and `d ≤ d_*`.
* §4: `fcMeanSquare_holds`: `E|g_t - a|² ≤ 2 Var g_t + 2|E g_t - a|²`; for `W^{-1/5} > ρ₀` the
  bound is trivial (`|g_t| ≤ ε⁻¹ ≤ W`, `y_t ≤ 2`). Constants depend on `b, κ` and the two input
  constants only (uniform in `W ≥ 1`, Hermitian `F` and `E ∈ bulkInterval κ`).

Helper names carry the prefix `fcm`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Complex Filter
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (spectralSum gaussianProduct weightedGradientNorm
  GaussianLpGradient ConditionalBlockGUECount)
open scoped NNReal ENNReal Topology Matrix.Norms.L2Operator

/-!
## 1. Deterministic resolvent facts for Hermitian `F`
-/

section Det

variable {n : Type} [Fintype n] [DecidableEq n]

theorem fcm_res_inv {F : Matrix n n ℂ} (hF : F.IsHermitian) {w : ℂ} (hw : 0 < w.im) :
    IsUnit (w • (1 : Matrix n n ℂ) - F).det ∧ ‖(w • (1 : Matrix n n ℂ) - F)⁻¹‖ ≤ (w.im)⁻¹ := by
  have he : w • (1 : Matrix n n ℂ) - F =
      (((w.re : ℝ) : ℂ) • (1 : Matrix n n ℂ) - F) + (((w.im : ℝ) : ℂ) * I) • 1 := by
    conv_lhs => rw [← Complex.re_add_im w]
    rw [add_smul]
    abel
  rw [he]
  exact fcd_herm_inv ((fcd_isHermitian_real_smul isHermitian_one _).sub hF) hw

/-- The resolvent identity `R₁ - R₂ = (w₂ - w₁) R₁ R₂`. -/
theorem fcm_res_sub {F : Matrix n n ℂ} (hF : F.IsHermitian) {w₁ w₂ : ℂ} (h₁ : 0 < w₁.im)
    (h₂ : 0 < w₂.im) :
    (w₁ • (1 : Matrix n n ℂ) - F)⁻¹ - (w₂ • (1 : Matrix n n ℂ) - F)⁻¹ =
      (w₂ - w₁) • ((w₁ • (1 : Matrix n n ℂ) - F)⁻¹ * (w₂ • (1 : Matrix n n ℂ) - F)⁻¹) := by
  set N₁ := w₁ • (1 : Matrix n n ℂ) - F
  set N₂ := w₂ • (1 : Matrix n n ℂ) - F
  have hu₁ := (fcm_res_inv hF h₁).1
  have hu₂ := (fcm_res_inv hF h₂).1
  calc N₁⁻¹ - N₂⁻¹ = N₁⁻¹ * N₂ * N₂⁻¹ - N₁⁻¹ * N₁ * N₂⁻¹ := by
        rw [Matrix.mul_assoc N₁⁻¹ N₂, mul_nonsing_inv _ hu₂, Matrix.mul_one,
          nonsing_inv_mul _ hu₁, Matrix.one_mul]
    _ = N₁⁻¹ * (N₂ - N₁) * N₂⁻¹ := by rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    _ = (w₂ - w₁) • (N₁⁻¹ * N₂⁻¹) := by
        have : N₂ - N₁ = (w₂ - w₁) • (1 : Matrix n n ℂ) := by
          simp only [N₁, N₂, sub_smul]; abel
        rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- The normalized trace `⟨X⟩ = W⁻¹ Tr X`. -/
def fcmTr (X : Matrix n n ℂ) : ℂ := (Fintype.card n : ℂ)⁻¹ * X.trace

theorem fcm_norm_tr_le (X : Matrix n n ℂ) : ‖fcmTr X‖ ≤ ‖X‖ := by
  unfold fcmTr
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | hpos
  · rw [h0]; simp
  · have hp : (0 : ℝ) < Fintype.card n := by exact_mod_cast hpos
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (Fintype.card n : ℝ)⁻¹ * ‖X.trace‖ ≤ (Fintype.card n : ℝ)⁻¹ * (Fintype.card n * ‖X‖) :=
          mul_le_mul_of_nonneg_left (tfl_trace_le X) (inv_nonneg.mpr hp.le)
      _ = ‖X‖ := by field_simp

omit [DecidableEq n] in
/-- Jensen for a Hermitian matrix: `(Re Tr Q)² ≤ W Re Tr Q²`. -/
theorem fcm_jensen {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) :
    Q.trace.re ^ 2 ≤ Fintype.card n * (Q * Q).trace.re := by
  have h1 : Q.trace.re = ∑ a, (Q a a).re := by rw [trace, Complex.re_sum]; rfl
  have h2 : (Q * Q).trace.re = ∑ a, ∑ b, ‖Q a b‖ ^ 2 := by
    rw [trace, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [diag_apply, mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hba : Q b a = star (Q a b) := by
      have := congrFun (congrFun hQ.eq b) a
      rw [conjTranspose_apply] at this
      exact this.symm
    rw [hba, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  rw [h1, h2]
  calc (∑ a, (Q a a).re) ^ 2 ≤ Fintype.card n * ∑ a, (Q a a).re ^ 2 := by
        have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a => (Q a a).re)
        simpa using this
    _ ≤ Fintype.card n * ∑ a, ∑ b, ‖Q a b‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (Nat.cast_nonneg _)
        calc (Q a a).re ^ 2 ≤ ‖Q a a‖ ^ 2 := by
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
          _ ≤ ∑ b, ‖Q a b‖ ^ 2 :=
              Finset.single_le_sum (f := fun b => ‖Q a b‖ ^ 2) (fun _ _ => sq_nonneg _)
                (Finset.mem_univ a)

/-- **The real part of `⟨R²⟩`**: for `R = (z - F)⁻¹`, `Im z = y > 0`, `m = ⟨R⟩`:
`Re ⟨R²⟩ ≤ -Im m / y - 2 (Im m)²` (normality, the Ward identity and Jensen). -/
theorem fcm_re_tr_sq_le {F : Matrix n n ℂ} (hF : F.IsHermitian) {z : ℂ} (hz : 0 < z.im)
    (hn : 0 < Fintype.card n) :
    (fcmTr ((z • (1 : Matrix n n ℂ) - F)⁻¹ * (z • (1 : Matrix n n ℂ) - F)⁻¹)).re ≤
      -(fcmTr (z • (1 : Matrix n n ℂ) - F)⁻¹).im / z.im -
        2 * (fcmTr (z • (1 : Matrix n n ℂ) - F)⁻¹).im ^ 2 := by
  set R := (z • (1 : Matrix n n ℂ) - F)⁻¹ with hR
  set y := z.im
  set Q := R * Rᴴ with hQ
  have hward := resolvent_sub_conjTranspose F hF z hz
  rw [← hR] at hward
  have hQh : Q.IsHermitian := by
    unfold IsHermitian; rw [hQ, conjTranspose_mul, conjTranspose_conjTranspose]
  -- `Re Tr Q = -Im Tr R / y`
  have hTQ : Q.trace.re = -R.trace.im / y := by
    have h2 := congrArg (fun M => M.trace.im) hward
    simp only [trace_sub, trace_smul, smul_eq_mul, Complex.sub_im, trace_conjTranspose,
      Complex.star_def, Complex.conj_im] at h2
    have e : (-(2 * y : ℂ) * I * Q.trace).im = -(2 * y) * Q.trace.re := by
      simp [Complex.mul_im]
    rw [e] at h2
    field_simp
    linarith
  -- `Re Tr R² = Re Tr Q - 2 y² Re Tr Q²`
  have hsq : (R * R).trace.re = Q.trace.re - 2 * y ^ 2 * (Q * Q).trace.re := by
    have h1 : (R - Rᴴ) * (R - Rᴴ) = ((-(2 * y : ℂ) * I) ^ 2) • (Q * Q) := by
      rw [hward, smul_mul_smul, sq]
    have h2 := congrArg (fun M => M.trace.re) h1
    simp only [Matrix.sub_mul, Matrix.mul_sub, trace_sub, Complex.sub_re, trace_smul,
      smul_eq_mul] at h2
    have e1 : (Rᴴ * Rᴴ).trace.re = (R * R).trace.re := by
      rw [← conjTranspose_mul, trace_conjTranspose, Complex.star_def, Complex.conj_re]
    have e2 : (Rᴴ * R).trace = (R * Rᴴ).trace := trace_mul_comm _ _
    have e3 : ((-(2 * y : ℂ) * I) ^ 2 * (Q * Q).trace).re = -(4 * y ^ 2) * (Q * Q).trace.re := by
      have : (-(2 * y : ℂ) * I) ^ 2 = ((-(4 * y ^ 2) : ℝ) : ℂ) := by
        push_cast; ring_nf; rw [I_sq]; ring
      rw [this, Complex.re_ofReal_mul]
    rw [e1, e2, e3] at h2
    rw [hQ] at h2 ⊢
    linarith
  have hj := fcm_jensen hQh
  have hnp : (0 : ℝ) < Fintype.card n := by exact_mod_cast hn
  have hy := hz
  unfold fcmTr
  have hc : ((Fintype.card n : ℂ))⁻¹ = (((Fintype.card n : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.re_ofReal_mul, Complex.im_ofReal_mul, hsq, hTQ]
  set N : ℝ := (Fintype.card n : ℝ)
  set T := R.trace.im
  have hq2 : (-T / y) ^ 2 / N ≤ (Q * Q).trace.re := by
    rw [div_le_iff₀ hnp, mul_comm]; rw [hTQ] at hj; exact hj
  have hy2 : 0 < y ^ 2 := by positivity
  have h3 : 2 * y ^ 2 * ((-T / y) ^ 2 / N) ≤ 2 * y ^ 2 * (Q * Q).trace.re :=
    mul_le_mul_of_nonneg_left hq2 (by positivity)
  have e : N⁻¹ * (2 * y ^ 2 * ((-T / y) ^ 2 / N)) = 2 * (N⁻¹ * T) ^ 2 := by
    field_simp
  have h4 : N⁻¹ * (2 * y ^ 2 * ((-T / y) ^ 2 / N)) ≤ N⁻¹ * (2 * y ^ 2 * (Q * Q).trace.re) :=
    mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hnp.le)
  rw [e] at h4
  have e2 : N⁻¹ * (-T / y - 2 * y ^ 2 * (Q * Q).trace.re) =
      -(N⁻¹ * T) / y - N⁻¹ * (2 * y ^ 2 * (Q * Q).trace.re) := by ring
  rw [e2]
  linarith

end Det

/-!
## 2. The scalar equation and its stability

`w_t(u) = z₀ + iε + tc(a - u)`, `M_t(u) = (w_t(u) - F)⁻¹`, so that `-E - F - (1-t)ca + iε - tcu =
w_t(u) - F`. The scalar map is `u ↦ ⟨M_t(u)⟩`, and `⟨M_t(a)⟩ = ⟨(z₀ + iε - F)⁻¹⟩` is within
`d + ε/γ²` of `a`. Stability (`fcm_stability`): `(u - a)(1 - tc⟨M_t(u) M_t(a)⟩) =
(u - ⟨M_t(u)⟩) + (⟨M_t(a)⟩ - a)` and `Re(1 - tc⟨M_t(u)M_t(a)⟩) ≥ min(1, 2cα²)/2` near `a`
(`Re(1 - tc⟨R₀²⟩) ≥ 1 - t + 2tcα² - Cd`).
-/

section Scalar

variable (b E : ℝ) {W : ℕ} (F : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ)

/-- `z₀ = -E - ca`. -/
def fcmZ0 : ℂ := -(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * matchedA E

/-- `w_t(u) = z₀ + iε + tc(a - u)`. -/
def fcmW (t : ℝ) (u : ℂ) : ℂ :=
  fcmZ0 b E + (ε : ℂ) * I + ((t * (1 - 2 * b) : ℝ) : ℂ) * (matchedA E - u)

/-- `M_t(u) = (w_t(u) - F)⁻¹`. -/
def fcmM (t : ℝ) (u : ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  (fcmW b E ε t u • (1 : Matrix (Fin W) (Fin W) ℂ) - F)⁻¹

theorem fcmZ0_im : (fcmZ0 b E).im = fcGamma b E := by
  simp only [fcmZ0, fcGamma, Complex.sub_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, zero_mul, add_zero, neg_zero, zero_sub]
  ring

theorem fcmW_im (t : ℝ) (u : ℂ) :
    (fcmW b E ε t u).im = fcGamma b E + ε + t * (1 - 2 * b) * ((matchedA E).im - u.im) := by
  simp only [fcmW, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.sub_im, fcmZ0_im]
  ring

theorem fcmW_self (t : ℝ) : fcmW b E ε t (matchedA E) = fcmZ0 b E + (ε : ℂ) * I := by
  simp [fcmW]

theorem fcm_fcGamma_eq : fcGamma b E = (1 - 2 * b) * -(matchedA E).im := rfl

/-- `Im w_t(u) ≥ γ/2` for `|u - a| ≤ α/2`, `α = -Im a`. -/
theorem fcmW_im_ge {b : ℝ} (hb : b < 1 / 2) {ε : ℝ} (hε : 0 ≤ ε) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {u : ℂ} (hu : ‖u - matchedA E‖ ≤ -(matchedA E).im / 2) :
    fcGamma b E / 2 ≤ (fcmW b E ε t u).im := by
  rw [fcmW_im, fcm_fcGamma_eq]
  have hc : 0 < 1 - 2 * b := by linarith
  have h1 : |u.im - (matchedA E).im| ≤ ‖u - matchedA E‖ := by
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  have h2 : t * (1 - 2 * b) * |u.im - (matchedA E).im| ≤
      (1 - 2 * b) * (-(matchedA E).im / 2) := by
    calc t * (1 - 2 * b) * |u.im - (matchedA E).im| ≤ 1 * (1 - 2 * b) * ‖u - matchedA E‖ := by
          gcongr; exact ht.2
      _ ≤ (1 - 2 * b) * (-(matchedA E).im / 2) := by rw [one_mul]; gcongr
  have h4 : 0 ≤ t * (1 - 2 * b) := mul_nonneg ht.1 hc.le
  have h5 := mul_le_mul_of_nonneg_left (le_abs_self (u.im - (matchedA E).im)) h4
  have e : t * (1 - 2 * b) * ((matchedA E).im - u.im) = -(t * (1 - 2 * b) * (u.im - (matchedA E).im)) := by
    ring
  rw [e]
  have e2 : (1 - 2 * b) * -(matchedA E).im / 2 = (1 - 2 * b) * -(matchedA E).im -
      (1 - 2 * b) * (-(matchedA E).im / 2) := by ring
  rw [e2]
  linarith

theorem fcmTr_sub {n : Type} [Fintype n] (X Y : Matrix n n ℂ) :
    fcmTr (X - Y) = fcmTr X - fcmTr Y := by
  unfold fcmTr; rw [trace_sub]; ring

theorem fcmTr_add {n : Type} [Fintype n] (X Y : Matrix n n ℂ) :
    fcmTr (X + Y) = fcmTr X + fcmTr Y := by
  unfold fcmTr; rw [trace_add]; ring

theorem fcmTr_smul {n : Type} [Fintype n] (k : ℂ) (X : Matrix n n ℂ) :
    fcmTr (k • X) = k * fcmTr X := by
  unfold fcmTr; rw [trace_smul, smul_eq_mul]; ring

/-- The real inequality behind `Re(1 - tc⟨R₀²⟩) ≥ 1 - t + 2tcα² - Cd`. -/
theorem fcm_real_stab {t c α p d : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hc : 0 < c) (hα : 0 < α)
    (hp : |p + α| ≤ d) :
    min 1 (2 * c * α ^ 2) - d * (1 / α + 4 * c * α) ≤
      1 - t * c * (-p / (c * α) - 2 * p ^ 2) := by
  set q := p + α with hq
  have hpq : p = -α + q := by rw [hq]; ring
  have hqd := abs_le.mp hp
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hp
  have hmin : min 1 (2 * c * α ^ 2) ≤ 1 - t + 2 * t * c * α ^ 2 := by
    rcases le_total 1 (2 * c * α ^ 2) with h | h
    · rw [min_eq_left h]; nlinarith [ht.1]
    · rw [min_eq_right h]; nlinarith [ht.2]
  have e1 : t * c * (-p / (c * α)) = t - t * q / α := by
    rw [hpq]; field_simp; ring
  have h2 : t * q / α ≥ -(d / α) := by
    have : -d ≤ t * q := by nlinarith [ht.1, ht.2]
    have h' := div_le_div_of_nonneg_right this hα.le
    rw [neg_div] at h'
    exact h'
  have h3 : 2 * t * c * p ^ 2 ≥ 2 * t * c * α ^ 2 - 4 * c * α * d := by
    rw [hpq]
    have h4 : (-α + q) ^ 2 ≥ α ^ 2 - 2 * α * d := by
      nlinarith [sq_nonneg q, mul_le_mul_of_nonneg_left hqd.2 hα.le]
    have htc : 0 ≤ 2 * t * c := by nlinarith [ht.1]
    have h5 : 2 * t * c * (-α + q) ^ 2 ≥ 2 * t * c * (α ^ 2 - 2 * α * d) :=
      mul_le_mul_of_nonneg_left h4 htc
    have h6 : 2 * t * c * (2 * α * d) ≤ 4 * c * α * d := by
      have : 0 ≤ c * α * d := by positivity
      nlinarith [ht.2]
    nlinarith
  have e2 : 1 - t * c * (-p / (c * α) - 2 * p ^ 2) = 1 - t * c * (-p / (c * α)) + 2 * t * c * p ^ 2 := by
    ring
  rw [e2, e1]
  have e3 : d * (1 / α + 4 * c * α) = d / α + 4 * c * α * d := by field_simp
  rw [e3]
  linarith

/-- **Stability of the scalar equation** near `a`, uniformly in `t ∈ [0,1]`: if `|u - a| ≤ η ≤ α/2`
and `d (1/α + 4cα) + c(3ε + 2cη)/γ³ ≤ min(1, 2cα²)/2`, then
`|u - a| min(1, 2cα²)/2 ≤ |u - ⟨M_t(u)⟩| + d + ε/γ²`, `d = |⟨(z₀ - F)⁻¹⟩ - a|`. -/
theorem fcm_stability {b : ℝ} (hb : b < 1 / 2) {E : ℝ} (hE : |E| < 2) {W : ℕ} (hW : 0 < W)
    {F : Matrix (Fin W) (Fin W) ℂ} (hF : F.IsHermitian) {ε : ℝ} (hε : 0 ≤ ε) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {u : ℂ} {η : ℝ} (hη : η ≤ -(matchedA E).im / 2)
    (hu : ‖u - matchedA E‖ ≤ η)
    (hsmall : ‖fcmTr ((fcmZ0 b E • (1 : Matrix (Fin W) (Fin W) ℂ) - F)⁻¹) - matchedA E‖ *
        (1 / -(matchedA E).im + 4 * (1 - 2 * b) * -(matchedA E).im) +
        (1 - 2 * b) * (3 * ε + 2 * (1 - 2 * b) * η) / fcGamma b E ^ 3 ≤
        min 1 (2 * (1 - 2 * b) * (-(matchedA E).im) ^ 2) / 2) :
    ‖u - matchedA E‖ * (min 1 (2 * (1 - 2 * b) * (-(matchedA E).im) ^ 2) / 2) ≤
      ‖u - fcmTr (fcmM b E F ε t u)‖ +
        ‖fcmTr ((fcmZ0 b E • (1 : Matrix (Fin W) (Fin W) ℂ) - F)⁻¹) - matchedA E‖ +
        ε / fcGamma b E ^ 2 := by
  set a := matchedA E
  set α := -a.im with hαdef
  have hα : 0 < α := by rw [hαdef]; linarith [matchedA_im_neg hE]
  set c := 1 - 2 * b with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  set γ := fcGamma b E with hγdef
  have hγ : γ = c * α := rfl
  have hγ0 : 0 < γ := by rw [hγ]; positivity
  set z₀ := fcmZ0 b E
  have hz₀ : z₀.im = γ := fcmZ0_im b E
  set wu := fcmW b E ε t u
  set wa := fcmW b E ε t a
  have hwu : γ / 2 ≤ wu.im := fcmW_im_ge E hb hε ht (hu.trans hη)
  have hwa : γ ≤ wa.im := by
    rw [fcmW_im, show (matchedA E).im - a.im = 0 from sub_self _, mul_zero, add_zero]
    linarith
  have hwu0 : 0 < wu.im := lt_of_lt_of_le (by positivity) hwu
  have hwa0 : 0 < wa.im := lt_of_lt_of_le hγ0 hwa
  have hz0 : 0 < z₀.im := by rw [hz₀]; exact hγ0
  set Mu := fcmM b E F ε t u
  set Ma := fcmM b E F ε t a
  set R₀ := (z₀ • (1 : Matrix (Fin W) (Fin W) ℂ) - F)⁻¹
  have hMu : ‖Mu‖ ≤ 2 / γ := (fcm_res_inv hF hwu0).2.trans (by
    rw [inv_eq_one_div, div_le_div_iff₀ hwu0 hγ0]; linarith)
  have hMa : ‖Ma‖ ≤ 1 / γ := (fcm_res_inv hF hwa0).2.trans (by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hγ0 hwa)
  have hR₀ : ‖R₀‖ ≤ 1 / γ := (fcm_res_inv hF hz0).2.trans (by rw [hz₀, inv_eq_one_div])
  -- identities
  have hdiff : Mu - Ma = (wa - wu) • (Mu * Ma) := fcm_res_sub hF hwu0 hwa0
  have hwdiff : wa - wu = ((t * c : ℝ) : ℂ) * (u - a) := by
    simp only [wa, wu, fcmW, hcdef]; ring
  have hMuR : Mu - R₀ = (z₀ - wu) • (Mu * R₀) := fcm_res_sub hF hwu0 hz0
  have hMaR : Ma - R₀ = (z₀ - wa) • (Ma * R₀) := fcm_res_sub hF hwa0 hz0
  have hzwu : ‖z₀ - wu‖ ≤ ε + c * ‖u - a‖ := by
    have : z₀ - wu = -((ε : ℂ) * I) + ((t * c : ℝ) : ℂ) * (u - a) := by
      simp only [wu, fcmW, hcdef]; ring
    rw [this]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_neg, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hε]
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg ht.1 hc.le)]
      exact mul_le_mul_of_nonneg_right (by nlinarith [ht.2]) (norm_nonneg _)
  have hzwa : ‖z₀ - wa‖ ≤ ε := by
    have : z₀ - wa = -((ε : ℂ) * I) := by simp only [wa, fcmW]; ring
    rw [this, norm_neg, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hε]
  -- the stability factor
  set X := fcmTr (Mu * Ma)
  set X₀ := fcmTr (R₀ * R₀)
  set Λ : ℂ := 1 - ((t * c : ℝ) : ℂ) * X
  have hkey : (u - a) * Λ = (u - fcmTr Mu) + (fcmTr Ma - a) := by
    have h1 : fcmTr Mu - fcmTr Ma = (wa - wu) * X := by
      rw [← fcmTr_sub, hdiff, fcmTr_smul]
    rw [hwdiff] at h1
    simp only [Λ]
    linear_combination h1
  have hXX : ‖X - X₀‖ ≤ (3 * ε + 2 * c * ‖u - a‖) / γ ^ 3 := by
    rw [← fcmTr_sub]
    refine (fcm_norm_tr_le _).trans ?_
    have e : Mu * Ma - R₀ * R₀ = (Mu - R₀) * Ma + R₀ * (Ma - R₀) := by
      rw [Matrix.sub_mul, Matrix.mul_sub]; abel
    rw [e, hMuR, hMaR]
    have hγ3 : (3 * ε + 2 * c * ‖u - a‖) / γ ^ 3 =
        (ε + c * ‖u - a‖) * (2 / γ) * (1 / γ) * (1 / γ) + 1 / γ * (ε * (1 / γ) * (1 / γ)) := by
      field_simp; ring
    rw [hγ3]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_mul_le _ _).trans (mul_le_mul ?_ hMa (norm_nonneg _) (by positivity))
      rw [norm_smul]
      refine mul_le_mul hzwu ((norm_mul_le _ _).trans (mul_le_mul hMu hR₀ (norm_nonneg _)
        (by positivity))) (norm_nonneg _) (by positivity) |>.trans (le_of_eq (by ring))
    · refine (norm_mul_le _ _).trans (mul_le_mul hR₀ ?_ (norm_nonneg _) (by positivity))
      rw [norm_smul]
      exact mul_le_mul hzwa ((norm_mul_le _ _).trans (mul_le_mul hMa hR₀ (norm_nonneg _)
        (by positivity))) (norm_nonneg _) hε |>.trans (le_of_eq (by ring))
  -- `Re(1 - tc X₀)`
  have hm := fcm_re_tr_sq_le hF hz0 (by rw [Fintype.card_fin]; exact hW)
  rw [hz₀] at hm
  set m := fcmTr R₀
  set d := ‖m - a‖
  have hpd : |m.im + α| ≤ d := by
    rw [hαdef, ← sub_eq_add_neg, ← Complex.sub_im]; exact Complex.abs_im_le_norm _
  have hrs := fcm_real_stab ht hc hα hpd
  have hre0 : min 1 (2 * c * α ^ 2) - d * (1 / α + 4 * c * α) ≤ 1 - t * c * X₀.re := by
    have htc : 0 ≤ t * c := mul_nonneg ht.1 hc.le
    have hm' : X₀.re ≤ -m.im / γ - 2 * m.im ^ 2 := hm
    have h7 := mul_le_mul_of_nonneg_left hm' htc
    refine hrs.trans ?_
    rw [← hγ]
    linarith
  have hreΛ : min 1 (2 * c * α ^ 2) / 2 ≤ Λ.re := by
    have h1 : Λ.re = 1 - t * c * X₀.re - t * c * (X - X₀).re := by
      simp only [Λ, Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul]; ring
    have h2 : t * c * (X - X₀).re ≤ c * ((3 * ε + 2 * c * η) / γ ^ 3) := by
      have h3 : (X - X₀).re ≤ (3 * ε + 2 * c * η) / γ ^ 3 :=
        (Complex.re_le_norm _).trans (hXX.trans (by gcongr))
      have h4 : t * c * (X - X₀).re ≤ t * c * ((3 * ε + 2 * c * η) / γ ^ 3) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg ht.1 hc.le)
      have h5 : 0 ≤ (3 * ε + 2 * c * η) / γ ^ 3 := by
        have : 0 ≤ η := (norm_nonneg _).trans hu
        positivity
      have h6 : t * c * ((3 * ε + 2 * c * η) / γ ^ 3) ≤ c * ((3 * ε + 2 * c * η) / γ ^ 3) := by
        have := mul_le_mul_of_nonneg_right ht.2 (mul_nonneg hc.le h5)
        calc t * c * ((3 * ε + 2 * c * η) / γ ^ 3) = t * (c * ((3 * ε + 2 * c * η) / γ ^ 3)) := by
              ring
          _ ≤ 1 * (c * ((3 * ε + 2 * c * η) / γ ^ 3)) := this
          _ = _ := one_mul _
      linarith
    have e : c * ((3 * ε + 2 * c * η) / γ ^ 3) = c * (3 * ε + 2 * c * η) / γ ^ 3 := by ring
    rw [h1]
    linarith
  -- conclusion
  have hMa' : ‖fcmTr Ma - a‖ ≤ d + ε / γ ^ 2 := by
    have : fcmTr Ma - a = (m - a) + fcmTr (Ma - R₀) := by rw [fcmTr_sub]; ring
    rw [this]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ((fcm_norm_tr_le _).trans ?_))
    rw [hMaR, norm_smul]
    calc ‖z₀ - wa‖ * ‖Ma * R₀‖ ≤ ε * (1 / γ * (1 / γ)) :=
          mul_le_mul hzwa ((norm_mul_le _ _).trans (mul_le_mul hMa hR₀ (norm_nonneg _)
            (by positivity))) (norm_nonneg _) hε
      _ = ε / γ ^ 2 := by field_simp
  have hΛ : Λ.re ≤ ‖Λ‖ := Complex.re_le_norm _
  calc ‖u - a‖ * (min 1 (2 * c * α ^ 2) / 2) ≤ ‖u - a‖ * ‖Λ‖ :=
        mul_le_mul_of_nonneg_left (hreΛ.trans hΛ) (norm_nonneg _)
    _ = ‖(u - fcmTr Mu) + (fcmTr Ma - a)‖ := by rw [← norm_mul, hkey]
    _ ≤ ‖u - fcmTr Mu‖ + (d + ε / γ ^ 2) := (norm_add_le _ _).trans (add_le_add le_rfl hMa')
    _ = _ := by ring

/-- `|⟨(z₀ + iε - F)⁻¹⟩ - a| ≤ d + ε/γ²`. -/
theorem fcm_trMa_le {b : ℝ} (hb : b < 1 / 2) {E : ℝ} (hE : |E| < 2) {W : ℕ}
    {F : Matrix (Fin W) (Fin W) ℂ} (hF : F.IsHermitian) {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    ‖fcmTr (fcmM b E F ε t (matchedA E)) - matchedA E‖ ≤
      ‖fcmTr ((fcmZ0 b E • (1 : Matrix (Fin W) (Fin W) ℂ) - F)⁻¹) - matchedA E‖ +
        ε / fcGamma b E ^ 2 := by
  have hα : 0 < -(matchedA E).im := by linarith [matchedA_im_neg hE]
  have hc : 0 < 1 - 2 * b := by linarith
  have hγ0 : 0 < fcGamma b E := by rw [fcm_fcGamma_eq]; positivity
  set γ := fcGamma b E
  set z₀ := fcmZ0 b E
  have hz₀ : z₀.im = γ := fcmZ0_im b E
  have hz0 : 0 < z₀.im := by rw [hz₀]; exact hγ0
  set wa := fcmW b E ε t (matchedA E)
  have hwa : γ ≤ wa.im := by
    rw [fcmW_im, sub_self, mul_zero, add_zero]; linarith
  have hwa0 : 0 < wa.im := lt_of_lt_of_le hγ0 hwa
  set Ma := fcmM b E F ε t (matchedA E)
  set R₀ := (z₀ • (1 : Matrix (Fin W) (Fin W) ℂ) - F)⁻¹
  have hMa : ‖Ma‖ ≤ 1 / γ := (fcm_res_inv hF hwa0).2.trans (by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hγ0 hwa)
  have hR₀ : ‖R₀‖ ≤ 1 / γ := (fcm_res_inv hF hz0).2.trans (by rw [hz₀, inv_eq_one_div])
  have hMaR : Ma - R₀ = (z₀ - wa) • (Ma * R₀) := fcm_res_sub hF hwa0 hz0
  have hzwa : ‖z₀ - wa‖ ≤ ε := by
    have : z₀ - wa = -((ε : ℂ) * I) := by simp only [wa, fcmW]; ring
    rw [this, norm_neg, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hε]
  have : fcmTr Ma - matchedA E = (fcmTr R₀ - matchedA E) + fcmTr (Ma - R₀) := by
    rw [fcmTr_sub]; ring
  rw [this]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ((fcm_norm_tr_le _).trans ?_))
  rw [hMaR, norm_smul]
  calc ‖z₀ - wa‖ * ‖Ma * R₀‖ ≤ ε * (1 / γ * (1 / γ)) :=
        mul_le_mul hzwa ((norm_mul_le _ _).trans (mul_le_mul hMa hR₀ (norm_nonneg _)
          (by positivity))) (norm_nonneg _) hε
    _ = ε / γ ^ 2 := by field_simp

end Scalar

/-!
## 3. The Schwinger–Dyson comparison of `E g_t` with the scalar equation

Gaussian integration by parts (`core_reg_identity`) gives `D_t E[R] - tτ E[(Tr R) R] = 1`,
`D_t = -E - F - (1-t)ca + iε`. With `u = E g_t` and `M = M_t(u)` (`D_t - tcu = w_t(u) - F`):
`u - ⟨M⟩ = tc (E[g ⟨MR⟩] - E g E⟨MR⟩)` (`fcm_sd`).
-/

section Heat

variable (b E : ℝ) {W : ℕ} (F : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ)

/-- `C₀(t) = -(E + (1-t)c Re a) - F`. -/
def fcmC0 (t : ℝ) : Matrix (Fin W) (Fin W) ℂ :=
  -((E + (1 - t) * (1 - 2 * b) * (matchedA E).re : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) - F

theorem fcm_heatMatrix_eq (t : ℝ) (A : Matrix (Fin W) (Fin W) ℂ) :
    fcHeatMatrix b E F ε t A = fcmC0 b E F t + ((Real.sqrt t : ℝ) : ℂ) • A +
      ((fcHeight' b E ε t : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
  simp only [fcHeatMatrix, fcHeatHerm, fcmC0, neg_smul]
  abel

theorem fcm_isHermitian_C0 {F : Matrix (Fin W) (Fin W) ℂ} (hF : F.IsHermitian) (t : ℝ) :
    (fcmC0 b E F t).IsHermitian := by
  simp only [fcmC0, neg_smul]
  exact (fcd_isHermitian_real_smul isHermitian_one _).neg.sub hF

/-- `D_t = (w_t(u) - F) + tcu`. -/
theorem fcm_D_eq (t : ℝ) (u : ℂ) :
    fcmC0 b E F t + ((fcHeight' b E ε t : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ) =
      (fcmW b E ε t u • (1 : Matrix (Fin W) (Fin W) ℂ) - F) +
        (((t * (1 - 2 * b) : ℝ) : ℂ) * u) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
  have hs : -((E + (1 - t) * (1 - 2 * b) * (matchedA E).re : ℝ) : ℂ) +
      (fcHeight' b E ε t : ℂ) * I = fcmW b E ε t u + ((t * (1 - 2 * b) : ℝ) : ℂ) * u := by
    apply Complex.ext
    · simp [fcmW, fcmZ0, fcHeight', fcGamma]; ring
    · simp [fcmW, fcmZ0, fcHeight', fcGamma]; ring
  calc fcmC0 b E F t + ((fcHeight' b E ε t : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ)
      = (-((E + (1 - t) * (1 - 2 * b) * (matchedA E).re : ℝ) : ℂ) +
          (fcHeight' b E ε t : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ) - F := by
        simp only [fcmC0, add_smul]; abel
    _ = _ := by rw [hs, add_smul]; abel

/-- The CLM `Y ↦ ⟨M Y⟩`. -/
def fcmTrCLM {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    Matrix n n ℂ →L[ℝ] ℂ :=
  ((Fintype.card n : ℂ)⁻¹) • (fcdTr.comp (ContinuousLinearMap.mul ℝ (Matrix n n ℂ) M))

theorem fcmTrCLM_apply {n : Type} [Fintype n] [DecidableEq n] (M Y : Matrix n n ℂ) :
    fcmTrCLM M Y = fcmTr (M * Y) := by
  simp [fcmTrCLM, fcmTr, fcdTr_apply]

theorem fcm_tr_integral {n : Type} [Fintype n] [DecidableEq n] {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (M : Matrix n n ℂ) {f : Ω → Matrix n n ℂ} (hf : Integrable f μ) :
    fcmTr (M * ∫ x, f x ∂μ) = ∫ x, fcmTr (M * f x) ∂μ := by
  rw [← fcmTrCLM_apply, ← (fcmTrCLM M).integral_comp_comm hf]
  simp only [fcmTrCLM_apply]

theorem fcmTr_eq (X : Matrix (Fin W) (Fin W) ℂ) : fcmTr X = (W : ℂ)⁻¹ * X.trace := by
  simp [fcmTr]

/-- **The Schwinger–Dyson comparison.** For `t ∈ [0,1]`, `u = E g_t` and `M = M_t(u)` with
`Im w_t(u) > 0`: `u - ⟨M⟩ = tc (E[g ⟨MR⟩] - u E⟨MR⟩)`. -/
theorem fcm_sd {b : ℝ} (hb : b < 1 / 2) (hW : 0 < W) {F : Matrix (Fin W) (Fin W) ℂ}
    (hF : F.IsHermitian) {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hw : 0 < (fcmW b E ε t (∫ r, fcmTr (fcHeatMatrix b E F ε t
      (gueOfCoords W (fcdTau b W) r))⁻¹ ∂stdGaussCoordLaw (GaussCoord W))).im) :
    let R := fun r => (fcHeatMatrix b E F ε t (gueOfCoords W (fcdTau b W) r))⁻¹
    let u := ∫ r, fcmTr (R r) ∂stdGaussCoordLaw (GaussCoord W)
    let M := fcmM b E F ε t u
    u - fcmTr M = ((t * (1 - 2 * b) : ℝ) : ℂ) *
      ((∫ r, fcmTr (R r) * fcmTr (M * R r) ∂stdGaussCoordLaw (GaussCoord W)) -
        u * ∫ r, fcmTr (M * R r) ∂stdGaussCoordLaw (GaussCoord W)) := by
  intro R u M
  set μ := stdGaussCoordLaw (GaussCoord W)
  set v : GaussCoord W → ℝ≥0 := fun _ => 1 with hv
  have hstd : μ = gaussianProduct v := rfl
  set τ := fcdTau b W
  have hτ : (τ : ℝ) = (1 - 2 * b) / W := fcd_tau_coe hb W
  set y := fcHeight' b E ε t with hydef
  have hγ := fcd_gamma_nonneg hb E
  have hyε : ε ≤ y := by simp only [hydef, fcHeight']; nlinarith [ht.2]
  have hy0 : 0 < y := lt_of_lt_of_le hε hyε
  have hC0 := fcm_isHermitian_C0 b E hF t
  have hreg := fcd_coreReg W τ hC0 (Real.sqrt t)
  have hG : ∀ x, coreG (fcmC0 b E F t) (Real.sqrt t • fcdGue W τ) y x = R x := fun x => by
    rw [fcd_coreG_eq]
    show _ = (fcHeatMatrix b E F ε t (gueOfCoords W τ x))⁻¹
    rw [fcm_heatMatrix_eq]
  have hst : ((Real.sqrt t : ℝ) : ℂ) ^ 2 = (t : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ht.1]
  have hS : ∀ G : Matrix (Fin W) (Fin W) ℂ,
      coreS v (Real.sqrt t • fcdGue W τ) G =
        (((t * τ : ℝ) : ℂ) * G.trace) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
    intro G
    unfold coreS
    simp only [hv, NNReal.coe_one, one_smul, fcd_smul_gue_apply, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    rw [← Finset.smul_sum, fcd_gue_sandwich, smul_smul]
    congr 1
    rw [← sq, hst]
    push_cast
    ring
  have hid := core_reg_identity v hreg hy0
  simp only [hG, hS, Matrix.smul_mul, Matrix.one_mul] at hid
  rw [← hstd] at hid
  -- integrability
  have hHx : ∀ x, (gueOfCoords W τ x).IsHermitian := gueOfCoords_isHermitian W τ
  have hRb : ∀ x, ‖R x‖ ≤ ε⁻¹ := fun x =>
    (fcd_heatMatrix_inv E hb hF hε ht.2 (hHx x)).2
  have hRc : Continuous R :=
    fcd_continuous_inv ((fcd_continuous_heatMatrix b E F ε t).comp (continuous_gueOfCoords W τ))
      fun x => (fcd_heatMatrix_inv E hb hF hε ht.2 (hHx x)).1
  have hRi : Integrable R μ := Integrable.of_bound hRc.aestronglyMeasurable _
    (Filter.Eventually.of_forall hRb)
  have hTRc : Continuous fun x => (((t * τ : ℝ) : ℂ) * (R x).trace) • R x :=
    (continuous_const.mul hRc.matrix_trace).smul hRc
  have hTRi : Integrable (fun x => (((t * τ : ℝ) : ℂ) * (R x).trace) • R x) μ := by
    refine Integrable.of_bound hTRc.aestronglyMeasurable
      (‖((t * τ : ℝ) : ℂ)‖ * (W * ε⁻¹) * ε⁻¹) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_smul, norm_mul]
    have htr : ‖(R x).trace‖ ≤ W * ε⁻¹ := by
      refine (tfl_trace_le _).trans ?_
      rw [Fintype.card_fin]
      exact mul_le_mul_of_nonneg_left (hRb x) (Nat.cast_nonneg _)
    gcongr
    exact hRb x
  -- apply `Y ↦ ⟨M Y⟩`
  have hMN : M * (fcmW b E ε t u • (1 : Matrix (Fin W) (Fin W) ℂ) - F) = 1 :=
    nonsing_inv_mul _ (fcm_res_inv hF hw).1
  have h1 := congrArg (fun Y => fcmTr (M * Y)) hid
  simp only [Matrix.mul_one] at h1
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, fcm_D_eq b E F ε t u, Matrix.mul_add, hMN,
    Matrix.mul_smul, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul,
    fcmTr_sub, fcmTr_add, fcmTr_smul] at h1
  have e1 : fcmTr (∫ x, R x ∂μ) = u := by
    have := fcm_tr_integral (μ := μ) 1 hRi
    simp only [Matrix.one_mul] at this
    exact this
  have e2 : fcmTr (M * ∫ x, R x ∂μ) = ∫ x, fcmTr (M * R x) ∂μ := fcm_tr_integral M hRi
  have hW' : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hW.ne'
  have hpt : ∀ x, fcmTr (M * ((((t * τ : ℝ) : ℂ) * (R x).trace) • R x)) =
      ((t * (1 - 2 * b) : ℝ) : ℂ) * (fcmTr (R x) * fcmTr (M * R x)) := by
    intro x
    rw [Matrix.mul_smul, fcmTr_smul, fcmTr_eq (R x), hτ]
    push_cast
    field_simp
  have e3 : fcmTr (M * ∫ x, (((t * τ : ℝ) : ℂ) * (R x).trace) • R x ∂μ) =
      ((t * (1 - 2 * b) : ℝ) : ℂ) * ∫ x, fcmTr (R x) * fcmTr (M * R x) ∂μ := by
    rw [fcm_tr_integral M hTRi, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [e1, e2, e3] at h1
  linear_combination h1

/-- `L²` bound from an integral bound. -/
theorem fcm_eLpNorm_le_of_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℂ}
    (hf : MemLp f 2 μ) {V : ℝ} (hV : ∫ x, ‖f x‖ ^ 2 ∂μ ≤ V) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt V) := by
  rw [fcm_eLpNorm_two hf]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hV)

/-- **The residual of the scalar equation**: with the variance bound `V ‖K‖²/(W²y³)` for all
deterministic insertions, `|u - ⟨M⟩| ≤ c ‖M‖ V/(W² y³)`. -/
theorem fcm_sd_error {b : ℝ} (hb : b < 1 / 2) (hW : 0 < W) {F : Matrix (Fin W) (Fin W) ℂ}
    (hF : F.IsHermitian) {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {V : ℝ}
    (hV0 : 0 ≤ V)
    (hvar : ∀ K : Matrix (Fin W) (Fin W) ℂ,
      ∫ r, ‖(W : ℂ)⁻¹ * (K * (fcHeatMatrix b E F ε t (gueOfCoords W (fcdTau b W) r))⁻¹).trace -
        ∫ r', (W : ℂ)⁻¹ * (K * (fcHeatMatrix b E F ε t
          (gueOfCoords W (fcdTau b W) r'))⁻¹).trace ∂stdGaussCoordLaw (GaussCoord W)‖ ^ 2
          ∂stdGaussCoordLaw (GaussCoord W) ≤ V * ‖K‖ ^ 2 / ((W : ℝ) ^ 2 * fcHeight' b E ε t ^ 3))
    (hw : 0 < (fcmW b E ε t (∫ r, fcmTr (fcHeatMatrix b E F ε t
      (gueOfCoords W (fcdTau b W) r))⁻¹ ∂stdGaussCoordLaw (GaussCoord W))).im) :
    let u := ∫ r, fcmTr (fcHeatMatrix b E F ε t (gueOfCoords W (fcdTau b W) r))⁻¹
      ∂stdGaussCoordLaw (GaussCoord W)
    ‖u - fcmTr (fcmM b E F ε t u)‖ ≤
      (1 - 2 * b) * ‖fcmM b E F ε t u‖ * (V / ((W : ℝ) ^ 2 * fcHeight' b E ε t ^ 3)) := by
  intro u
  have hsd := fcm_sd E hb hW hF hε ht hw
  simp only at hsd
  rw [hsd]
  set μ := stdGaussCoordLaw (GaussCoord W)
  set τ := fcdTau b W
  set R : (GaussCoord W → ℝ) → Matrix (Fin W) (Fin W) ℂ :=
    fun r => (fcHeatMatrix b E F ε t (gueOfCoords W τ r))⁻¹ with hR
  set M := fcmM b E F ε t u
  set Q := V / ((W : ℝ) ^ 2 * fcHeight' b E ε t ^ 3) with hQ
  have hγ := fcd_gamma_nonneg hb E
  have hy : ε ≤ fcHeight' b E ε t := by unfold fcHeight'; nlinarith [ht.2]
  have hQ0 : 0 ≤ Q := by
    have : 0 < fcHeight' b E ε t := lt_of_lt_of_le hε hy
    positivity
  have hHx : ∀ x, (gueOfCoords W τ x).IsHermitian := gueOfCoords_isHermitian W τ
  have hRb : ∀ x, ‖R x‖ ≤ ε⁻¹ := fun x => (fcd_heatMatrix_inv E hb hF hε ht.2 (hHx x)).2
  have hRc : Continuous R :=
    fcd_continuous_inv ((fcd_continuous_heatMatrix b E F ε t).comp (continuous_gueOfCoords W τ))
      fun x => (fcd_heatMatrix_inv E hb hF hε ht.2 (hHx x)).1
  have hmem : ∀ K : Matrix (Fin W) (Fin W) ℂ, MemLp (fun r => fcmTr (K * R r)) 2 μ := fun K =>
    MemLp.of_bound ((continuous_const.mul ((continuous_const.mul hRc).matrix_trace))
      |>.aestronglyMeasurable) (‖K‖ * ε⁻¹) (Filter.Eventually.of_forall fun x =>
        (fcm_norm_tr_le _).trans ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_left (hRb x) (norm_nonneg _))))
  have hvarK : ∀ K : Matrix (Fin W) (Fin W) ℂ,
      ∫ r, ‖fcmTr (K * R r) - ∫ r', fcmTr (K * R r') ∂μ‖ ^ 2 ∂μ ≤ ‖K‖ ^ 2 * Q := by
    intro K
    have h := hvar K
    simp only [← fcmTr_eq] at h
    calc _ ≤ V * ‖K‖ ^ 2 / ((W : ℝ) ^ 2 * fcHeight' b E ε t ^ 3) := h
      _ = ‖K‖ ^ 2 * Q := by rw [hQ]; ring
  have hmem1 : MemLp (fun r => fcmTr (R r)) 2 μ := by
    have := hmem 1
    simp only [Matrix.one_mul] at this
    exact this
  have hA : eLpNorm (fun r => fcmTr (R r) - ∫ r', fcmTr (R r') ∂μ) 2 μ ≤
      ENNReal.ofReal (Real.sqrt Q) := by
    refine fcm_eLpNorm_le_of_integral (hmem1.sub (memLp_const _)) ?_
    have h := hvarK 1
    simp only [Matrix.one_mul] at h
    refine h.trans ?_
    have h1 : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ^ 2 ≤ 1 := by
      have := lct_norm_one_le (n := Fin W)
      have h0 := norm_nonneg (1 : Matrix (Fin W) (Fin W) ℂ)
      nlinarith
    nlinarith
  have hB : eLpNorm (fun r => fcmTr (M * R r) - ∫ r', fcmTr (M * R r') ∂μ) 2 μ ≤
      ENNReal.ofReal (‖M‖ * Real.sqrt Q) := by
    have := fcm_eLpNorm_le_of_integral ((hmem M).sub (memLp_const _)) (hvarK M)
    rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
  have hcov := core_cov_le (ν := μ) hmem1 (hmem M) (Real.sqrt_nonneg Q)
    (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg Q)) hA hB
  have hc : 0 ≤ t * (1 - 2 * b) := mul_nonneg ht.1 (by linarith)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
  calc t * (1 - 2 * b) * ‖(∫ r, fcmTr (R r) * fcmTr (M * R r) ∂μ) -
        (∫ r, fcmTr (R r) ∂μ) * ∫ r, fcmTr (M * R r) ∂μ‖
      ≤ t * (1 - 2 * b) * (Real.sqrt Q * (‖M‖ * Real.sqrt Q)) :=
        mul_le_mul_of_nonneg_left hcov hc
    _ = t * ((1 - 2 * b) * ‖M‖ * Q) := by
        rw [show Real.sqrt Q * (‖M‖ * Real.sqrt Q) = ‖M‖ * (Real.sqrt Q * Real.sqrt Q) by ring,
          Real.mul_self_sqrt hQ0]; ring
    _ ≤ 1 * ((1 - 2 * b) * ‖M‖ * Q) := by
        gcongr
        · have : 0 < 1 - 2 * b := by linarith
          positivity
        · exact ht.2
    _ = (1 - 2 * b) * ‖M‖ * Q := one_mul _

/-- `t ↦ E g_t` is continuous on `[0,1)`. -/
theorem fcm_gbar_continuousAt {b : ℝ} (hb : b < 1 / 2) {F : Matrix (Fin W) (Fin W) ℂ}
    (hF : F.IsHermitian) {ε : ℝ} (hε : 0 < ε) {t₀ : ℝ} (ht₀ : t₀ < 1) :
    ContinuousAt (fun t => ∫ r, fcmTr (fcHeatMatrix b E F ε t
      (gueOfCoords W (fcdTau b W) r))⁻¹ ∂stdGaussCoordLaw (GaussCoord W)) t₀ := by
  set τ := fcdTau b W
  refine continuousAt_of_dominated (bound := fun _ => ε⁻¹) ?_ ?_ (integrable_const _) ?_
  · refine Filter.Eventually.of_forall fun t => ?_
    unfold fcmTr
    exact (measurable_const.mul ((continuous_id.matrix_trace).measurable.comp
      (fcd_measurable_inv.comp ((fcd_continuous_heatMatrix b E F ε t).comp
        (continuous_gueOfCoords W τ)).measurable))).aestronglyMeasurable
  · filter_upwards [Iio_mem_nhds ht₀] with t ht
    refine Filter.Eventually.of_forall fun r => ?_
    exact (fcm_norm_tr_le _).trans
      (fcd_heatMatrix_inv E hb hF hε (Set.mem_Iio.mp ht).le (gueOfCoords_isHermitian W τ r)).2
  · refine Filter.Eventually.of_forall fun r => ?_
    have hZc : Continuous fun t => fcHeatMatrix b E F ε t (gueOfCoords W τ r) := by
      unfold fcHeatMatrix fcHeatHerm fcHeight'
      fun_prop
    have hinv := fcd_continuousAt_inv hZc.continuousAt
      (fcd_heatMatrix_inv E hb hF hε ht₀.le (gueOfCoords_isHermitian W τ r)).1
    unfold fcmTr
    exact continuousAt_const.mul ((continuous_id.matrix_trace).continuousAt.comp hinv)

/-- At `t = 0` the heat matrix is deterministic: `H_0 = (z₀ + iε) - F`. -/
theorem fcm_heatMatrix_zero (A : Matrix (Fin W) (Fin W) ℂ) (u : ℂ) :
    fcHeatMatrix b E F ε 0 A = fcmW b E ε 0 u • (1 : Matrix (Fin W) (Fin W) ℂ) - F := by
  have hs : -((E + (1 - 0) * (1 - 2 * b) * (matchedA E).re : ℝ) : ℂ) +
      (fcHeight' b E ε 0 : ℂ) * I = fcmW b E ε 0 u := by
    apply Complex.ext
    · simp [fcmW, fcmZ0, fcHeight', fcGamma]; ring
    · simp [fcmW, fcmZ0, fcHeight', fcGamma]
  rw [← hs]
  simp only [fcHeatMatrix, fcHeatHerm, Real.sqrt_zero, Complex.ofReal_zero, zero_smul, zero_sub,
    add_smul, neg_smul]
  abel

/-- **Stability and continuation from `t = 0`**: under the smallness
conditions, for every `t ∈ [0,1)`,
`|E g_t - a| ≤ (2/δ)(c(2/γ)V/(W²y_t³) + d + ε/γ²)`, `δ = min(1, 2cα²)`. -/
theorem fcm_mean_bound {b : ℝ} (hb : b < 1 / 2) {E : ℝ} (hE : |E| < 2) {W : ℕ} (hW : 0 < W)
    {F : Matrix (Fin W) (Fin W) ℂ} (hF : F.IsHermitian) {ε : ℝ} (hε : 0 < ε) {V : ℝ}
    (hV0 : 0 ≤ V)
    (hvar : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ K : Matrix (Fin W) (Fin W) ℂ,
      ∫ r, ‖(W : ℂ)⁻¹ * (K * (fcHeatMatrix b E F ε t (gueOfCoords W (fcdTau b W) r))⁻¹).trace -
        ∫ r', (W : ℂ)⁻¹ * (K * (fcHeatMatrix b E F ε t
          (gueOfCoords W (fcdTau b W) r'))⁻¹).trace ∂stdGaussCoordLaw (GaussCoord W)‖ ^ 2
          ∂stdGaussCoordLaw (GaussCoord W) ≤ V * ‖K‖ ^ 2 / ((W : ℝ) ^ 2 * fcHeight' b E ε t ^ 3))
    {η : ℝ} (hη : η ≤ -(matchedA E).im / 2)
    (hsmall : ‖fcmTr ((fcmZ0 b E • (1 : Matrix (Fin W) (Fin W) ℂ) - F)⁻¹) - matchedA E‖ *
        (1 / -(matchedA E).im + 4 * (1 - 2 * b) * -(matchedA E).im) +
        (1 - 2 * b) * (3 * ε + 2 * (1 - 2 * b) * η) / fcGamma b E ^ 3 ≤
        min 1 (2 * (1 - 2 * b) * (-(matchedA E).im) ^ 2) / 2)
    (hboot : 2 / min 1 (2 * (1 - 2 * b) * (-(matchedA E).im) ^ 2) *
        ((1 - 2 * b) * (2 / fcGamma b E) * (V / ((W : ℝ) ^ 2 * ε ^ 3)) +
          ‖fcmTr ((fcmZ0 b E • (1 : Matrix (Fin W) (Fin W) ℂ) - F)⁻¹) - matchedA E‖ +
          ε / fcGamma b E ^ 2) < η) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖(∫ r, fcmTr (fcHeatMatrix b E F ε t (gueOfCoords W (fcdTau b W) r))⁻¹
          ∂stdGaussCoordLaw (GaussCoord W)) - matchedA E‖ ≤
        2 / min 1 (2 * (1 - 2 * b) * (-(matchedA E).im) ^ 2) *
          ((1 - 2 * b) * (2 / fcGamma b E) * (V / ((W : ℝ) ^ 2 * fcHeight' b E ε t ^ 3)) +
            ‖fcmTr ((fcmZ0 b E • (1 : Matrix (Fin W) (Fin W) ℂ) - F)⁻¹) - matchedA E‖ +
            ε / fcGamma b E ^ 2) := by
  set a := matchedA E
  set α := -a.im with hαdef
  have hα : 0 < α := by rw [hαdef]; linarith [matchedA_im_neg hE]
  set c := 1 - 2 * b with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  set γ := fcGamma b E with hγdef
  have hγ0 : 0 < γ := by rw [hγdef, fcm_fcGamma_eq]; positivity
  set δ := min 1 (2 * c * α ^ 2) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  set d := ‖fcmTr ((fcmZ0 b E • (1 : Matrix (Fin W) (Fin W) ℂ) - F)⁻¹) - a‖
  set gbar : ℝ → ℂ := fun t => ∫ r, fcmTr (fcHeatMatrix b E F ε t
    (gueOfCoords W (fcdTau b W) r))⁻¹ ∂stdGaussCoordLaw (GaussCoord W) with hgbar
  set B : ℝ → ℝ := fun t => 2 / δ * (c * (2 / γ) * (V / ((W : ℝ) ^ 2 * fcHeight' b E ε t ^ 3)) +
    d + ε / γ ^ 2) with hB
  have hγ' := fcd_gamma_nonneg hb E
  have hBle : ∀ t ∈ Set.Icc (0 : ℝ) 1, B t < η := by
    intro t ht
    refine lt_of_le_of_lt ?_ hboot
    have hyε : ε ≤ fcHeight' b E ε t := by unfold fcHeight'; nlinarith [ht.2]
    have hW' : (0 : ℝ) < W := by exact_mod_cast hW
    have h1 : V / ((W : ℝ) ^ 2 * fcHeight' b E ε t ^ 3) ≤ V / ((W : ℝ) ^ 2 * ε ^ 3) := by
      apply div_le_div_of_nonneg_left hV0 (by positivity)
      gcongr
    simp only [hB]
    gcongr
  -- the bootstrap
  have hboot' : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖gbar t - a‖ ≤ η → ‖gbar t - a‖ ≤ B t := by
    intro t ht hgt
    have hu := hgt
    have hst := fcm_stability hb hE hW hF hε.le ht hη hu hsmall
    have hwim : γ / 2 ≤ (fcmW b E ε t (gbar t)).im := fcmW_im_ge E hb hε.le ht (hu.trans hη)
    have hw0 : 0 < (fcmW b E ε t (gbar t)).im := lt_of_lt_of_le (by positivity) hwim
    have herr := fcm_sd_error E hb hW hF hε ht hV0 (hvar t ht) hw0
    simp only at herr
    have hM : ‖fcmM b E F ε t (gbar t)‖ ≤ 2 / γ := (fcm_res_inv hF hw0).2.trans (by
      rw [inv_eq_one_div, div_le_div_iff₀ hw0 hγ0]; linarith)
    have hQ0 : 0 ≤ V / ((W : ℝ) ^ 2 * fcHeight' b E ε t ^ 3) := by
      have : 0 < fcHeight' b E ε t := by unfold fcHeight'; nlinarith [ht.2]
      positivity
    have herr' : ‖gbar t - fcmTr (fcmM b E F ε t (gbar t))‖ ≤
        c * (2 / γ) * (V / ((W : ℝ) ^ 2 * fcHeight' b E ε t ^ 3)) :=
      herr.trans (by gcongr)
    have h2 : ‖gbar t - a‖ * (δ / 2) ≤ c * (2 / γ) * (V / ((W : ℝ) ^ 2 * fcHeight' b E ε t ^ 3)) +
        d + ε / γ ^ 2 := by
      have := hst
      linarith
    simp only [hB]
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ0]
    nlinarith
  -- the a priori bound by continuation
  have hapriori : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖gbar t - a‖ ≤ η := by
    intro t₁ ht₁
    by_contra hcon
    push Not at hcon
    have hcont : ContinuousOn (fun t => ‖gbar t - a‖) (Set.Icc 0 t₁) := by
      intro t ht
      exact ((fcm_gbar_continuousAt E hb hF hε (lt_of_le_of_lt ht.2 ht₁.2)).sub
        continuousAt_const).norm.continuousWithinAt
    have h0 : ‖gbar 0 - a‖ < η := by
      have e0 : gbar 0 = fcmTr (fcmM b E F ε 0 a) := by
        simp only [hgbar, fcm_heatMatrix_zero b E F ε _ a, integral_const, probReal_univ,
          one_smul]
        rfl
      rw [e0]
      refine lt_of_le_of_lt (fcm_trMa_le hb hE hF hε.le 0) (lt_of_le_of_lt ?_ (hBle 0
        ⟨le_rfl, zero_le_one⟩))
      simp only [hB]
      have hQ0 : 0 ≤ c * (2 / γ) * (V / ((W : ℝ) ^ 2 * fcHeight' b E ε 0 ^ 3)) := by
        have : 0 < fcHeight' b E ε 0 := by unfold fcHeight'; nlinarith
        positivity
      have h2 : 1 ≤ 2 / δ := by rw [le_div_iff₀ hδ0]; linarith
      have h3 : 0 ≤ d + ε / γ ^ 2 := by positivity
      nlinarith
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc ht₁.1 hcont ⟨h0.le, hcon.le⟩
    have hs1 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht₁.2.le⟩
    have := hboot' s hs1 hfs.le
    have := hBle s hs1
    simp only at hfs
    linarith
  intro t ht
  exact hboot' t (Set.Ico_subset_Icc_self ht) (hapriori t ht)

end Heat

/-!
## 4. The mean-square bound `FcMeanSquare`
-/

/-- Exponent bookkeeping for `ε = W^{-3/5}`, `ρ = W^{-1/5}`. -/
theorem fcm_rho {W : ℕ} (hW : 0 < W) :
    fcHeight W ≤ (W : ℝ) ^ (-(1 / 5 : ℝ)) ∧ (W : ℝ) ^ (-(1 / 5 : ℝ)) ≤ 1 ∧
      ((W : ℝ) ^ 2 * fcHeight W ^ 3)⁻¹ = (W : ℝ) ^ (-(1 / 5 : ℝ)) ∧ (fcHeight W)⁻¹ ≤ W ∧
      ((W : ℝ) ^ (-(1 / 5 : ℝ))) ^ 5 = (W : ℝ)⁻¹ := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  refine ⟨Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num),
    Real.rpow_le_one_of_one_le_of_nonpos hW1 (by norm_num), ?_, ?_, ?_⟩
  · unfold fcHeight
    rw [← Real.rpow_natCast ((W : ℝ) ^ (-(3 / 5 : ℝ))), ← Real.rpow_mul hW0.le,
      ← Real.rpow_natCast (W : ℝ) 2, ← Real.rpow_add hW0, ← Real.rpow_neg hW0.le]
    norm_num
  · unfold fcHeight
    rw [← Real.rpow_neg hW0.le]
    calc (W : ℝ) ^ (-(-(3 / 5 : ℝ))) ≤ (W : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
      _ = W := Real.rpow_one _
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    norm_num
    exact Real.rpow_neg_one _

theorem fcm_sq_add_le (x y : ℂ) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_add_le x y
  have h0 := norm_nonneg (x + y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

theorem fcm_sq3_le (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]

/-- **Glue**: the mean bound, the variance bound and `|x + y|² ≤ 2|x|² + 2|y|²`. -/
theorem fcm_glue {b : ℝ} (hb : b < 1 / 2) {E : ℝ} (hE : |E| < 2) {W : ℕ} (hW : 0 < W)
    {F : Matrix (Fin W) (Fin W) ℂ} (hF : F.IsHermitian) {ε : ℝ} (hε : 0 < ε) {V : ℝ}
    (hV0 : 0 ≤ V)
    (hvar : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ K : Matrix (Fin W) (Fin W) ℂ,
      ∫ r, ‖(W : ℂ)⁻¹ * (K * (fcHeatMatrix b E F ε t (gueOfCoords W (fcdTau b W) r))⁻¹).trace -
        ∫ r', (W : ℂ)⁻¹ * (K * (fcHeatMatrix b E F ε t
          (gueOfCoords W (fcdTau b W) r'))⁻¹).trace ∂stdGaussCoordLaw (GaussCoord W)‖ ^ 2
          ∂stdGaussCoordLaw (GaussCoord W) ≤ V * ‖K‖ ^ 2 / ((W : ℝ) ^ 2 * fcHeight' b E ε t ^ 3))
    {η : ℝ} (hη : η ≤ -(matchedA E).im / 2)
    (hsmall : ‖fcmTr ((fcmZ0 b E • (1 : Matrix (Fin W) (Fin W) ℂ) - F)⁻¹) - matchedA E‖ *
        (1 / -(matchedA E).im + 4 * (1 - 2 * b) * -(matchedA E).im) +
        (1 - 2 * b) * (3 * ε + 2 * (1 - 2 * b) * η) / fcGamma b E ^ 3 ≤
        min 1 (2 * (1 - 2 * b) * (-(matchedA E).im) ^ 2) / 2)
    (hboot : 2 / min 1 (2 * (1 - 2 * b) * (-(matchedA E).im) ^ 2) *
        ((1 - 2 * b) * (2 / fcGamma b E) * (V / ((W : ℝ) ^ 2 * ε ^ 3)) +
          ‖fcmTr ((fcmZ0 b E • (1 : Matrix (Fin W) (Fin W) ℂ) - F)⁻¹) - matchedA E‖ +
          ε / fcGamma b E ^ 2) < η) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    ∫ r, ‖fcHeatTrace b E F ε t (gueOfCoords W (fcdTau b W) r) - matchedA E‖ ^ 2
        ∂stdGaussCoordLaw (GaussCoord W) ≤
      2 * (V / ((W : ℝ) ^ 2 * fcHeight' b E ε t ^ 3)) +
        2 * (2 / min 1 (2 * (1 - 2 * b) * (-(matchedA E).im) ^ 2) *
          ((1 - 2 * b) * (2 / fcGamma b E) * (V / ((W : ℝ) ^ 2 * fcHeight' b E ε t ^ 3)) +
            ‖fcmTr ((fcmZ0 b E • (1 : Matrix (Fin W) (Fin W) ℂ) - F)⁻¹) - matchedA E‖ +
            ε / fcGamma b E ^ 2)) ^ 2 := by
  have hmb := fcm_mean_bound hb hE hW hF hε hV0 hvar hη hsmall hboot t ht
  set μ := stdGaussCoordLaw (GaussCoord W)
  set τ := fcdTau b W
  set a := matchedA E
  set gbar := ∫ r, fcmTr (fcHeatMatrix b E F ε t (gueOfCoords W τ r))⁻¹ ∂μ with hgbar
  set Bm := 2 / min 1 (2 * (1 - 2 * b) * (-a.im) ^ 2) *
    ((1 - 2 * b) * (2 / fcGamma b E) * (V / ((W : ℝ) ^ 2 * fcHeight' b E ε t ^ 3)) +
      ‖fcmTr ((fcmZ0 b E • (1 : Matrix (Fin W) (Fin W) ℂ) - F)⁻¹) - a‖ + ε / fcGamma b E ^ 2)
  set g : (GaussCoord W → ℝ) → ℂ := fun r => fcHeatTrace b E F ε t (gueOfCoords W τ r) with hg
  have hgg : ∀ r, g r = fcmTr (fcHeatMatrix b E F ε t (gueOfCoords W τ r))⁻¹ := fun r => by
    rw [fcmTr_eq]; rfl
  have hgb : ∀ r, ‖g r‖ ≤ ε⁻¹ := fun r =>
    fcd_heatTrace_le E hb hF hε ht.2.le hW (gueOfCoords_isHermitian W τ r)
  have hgc : Continuous g := by
    have hRc := fcd_continuous_inv ((fcd_continuous_heatMatrix b E F ε t).comp
      (continuous_gueOfCoords W τ)) fun x =>
        (fcd_heatMatrix_inv E hb hF hε ht.2.le (gueOfCoords_isHermitian W τ x)).1
    simp only [hg, fcHeatTrace]
    exact continuous_const.mul hRc.matrix_trace
  have hVar : ∫ r, ‖g r - gbar‖ ^ 2 ∂μ ≤ V / ((W : ℝ) ^ 2 * fcHeight' b E ε t ^ 3) := by
    have h := hvar t (Set.Ico_subset_Icc_self ht) 1
    simp only [Matrix.one_mul, ← fcmTr_eq] at h
    have e : ∫ r, ‖g r - gbar‖ ^ 2 ∂μ = ∫ r, ‖fcmTr (fcHeatMatrix b E F ε t
        (gueOfCoords W τ r))⁻¹ - ∫ r', fcmTr (fcHeatMatrix b E F ε t
          (gueOfCoords W τ r'))⁻¹ ∂μ‖ ^ 2 ∂μ := by
      simp only [hgg, hgbar]
    rw [e]
    refine h.trans ?_
    have h1 : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ^ 2 ≤ 1 := by
      have := lct_norm_one_le (n := Fin W)
      have h0 := norm_nonneg (1 : Matrix (Fin W) (Fin W) ℂ)
      calc ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ h0 this 2
        _ = 1 := one_pow 2
    have hy : 0 < fcHeight' b E ε t := by
      have := fcd_gamma_nonneg hb E
      unfold fcHeight'
      have := mul_nonneg (sub_nonneg.2 ht.2.le) this
      linarith
    have hden : 0 < (W : ℝ) ^ 2 * fcHeight' b E ε t ^ 3 := by
      have : (0 : ℝ) < W := by exact_mod_cast hW
      positivity
    rw [div_le_div_iff_of_pos_right hden]
    calc V * ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ^ 2 ≤ V * 1 := mul_le_mul_of_nonneg_left h1 hV0
      _ = V := mul_one V
  have hsplit : ∀ r, ‖g r - a‖ ^ 2 ≤ 2 * ‖g r - gbar‖ ^ 2 + 2 * ‖gbar - a‖ ^ 2 := fun r => by
    have := fcm_sq_add_le (g r - gbar) (gbar - a)
    rwa [sub_add_sub_cancel] at this
  have hgi : Integrable (fun r => ‖g r - a‖ ^ 2) μ :=
    Integrable.of_bound ((hgc.sub continuous_const).norm.pow 2).aestronglyMeasurable
      ((ε⁻¹ + ‖a‖) ^ 2) (Filter.Eventually.of_forall fun r => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans
          (add_le_add (hgb r) le_rfl)) 2)
  have hgi2 : Integrable (fun r => ‖g r - gbar‖ ^ 2) μ :=
    Integrable.of_bound ((hgc.sub continuous_const).norm.pow 2).aestronglyMeasurable
      ((ε⁻¹ + ‖gbar‖) ^ 2) (Filter.Eventually.of_forall fun r => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans
          (add_le_add (hgb r) le_rfl)) 2)
  have hmb2 : ‖gbar - a‖ ^ 2 ≤ Bm ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hmb 2
  have hI : ∫ r, (2 * ‖g r - gbar‖ ^ 2 + 2 * ‖gbar - a‖ ^ 2) ∂μ =
      2 * ∫ r, ‖g r - gbar‖ ^ 2 ∂μ + 2 * ‖gbar - a‖ ^ 2 := by
    rw [integral_add (hgi2.const_mul 2) (integrable_const (2 * ‖gbar - a‖ ^ 2)),
      integral_const_mul, integral_const, probReal_univ, one_smul]
  have hI2 : Integrable (fun r => 2 * ‖g r - gbar‖ ^ 2 + 2 * ‖gbar - a‖ ^ 2) μ :=
    (hgi2.const_mul 2).add (integrable_const _)
  refine (integral_mono hgi hI2 hsplit).trans ?_
  rw [hI]
  linarith

/-- Real arithmetic: the smallness conditions from the choice of `η, d_*, ρ₀`. -/
theorem fcm_arith_small {c s α γ δ₁ δE Vmax η ρ₀ d ε Q : ℝ} (hc : 0 < c) (hs : 0 < s)
    (hαs : s ≤ α) (hα1 : α ≤ 1) (hγ : γ = c * α) (hδ₁0 : 0 < δ₁) (hδE : δ₁ ≤ δE)
    (hVmax0 : 0 < Vmax) (hη0 : 0 < η) (hηc : η ≤ δ₁ * (c * s) ^ 3 / (16 * c ^ 2))
    (hρ₀a : ρ₀ ≤ δ₁ * (c * s) ^ 3 / (12 * c)) (hρ₀b : ρ₀ ≤ δ₁ * η * (c * s) ^ 2 / 8)
    (hρ₀c : ρ₀ ≤ δ₁ * η * s / (16 * Vmax)) (hd0 : 0 ≤ d) (hda : d ≤ δ₁ / (8 * (1 / s + 4 * c)))
    (hdb : d ≤ δ₁ * η / 16) (hε0 : 0 < ε) (hερ₀ : ε ≤ ρ₀) (hQ0 : 0 ≤ Q) (hQ : Q ≤ Vmax * ρ₀) :
    d * (1 / α + 4 * c * α) + c * (3 * ε + 2 * c * η) / γ ^ 3 ≤ δE / 2 ∧
      2 / δE * (c * (2 / γ) * Q + d + ε / γ ^ 2) < η := by
  have hα0 : 0 < α := lt_of_lt_of_le hs hαs
  have hcs : 0 < c * s := by positivity
  have hγs : c * s ≤ γ := by rw [hγ]; exact mul_le_mul_of_nonneg_left hαs hc.le
  have hγ0 : 0 < γ := lt_of_lt_of_le hcs hγs
  have hρ₀0 : 0 < ρ₀ := lt_of_lt_of_le hε0 hερ₀
  have hγ3 : (c * s) ^ 3 ≤ γ ^ 3 := pow_le_pow_left₀ hcs.le hγs 3
  have hγ2 : (c * s) ^ 2 ≤ γ ^ 2 := pow_le_pow_left₀ hcs.le hγs 2
  have hδE0 : 0 < δE := lt_of_lt_of_le hδ₁0 hδE
  constructor
  · have h1 : 1 / α + 4 * c * α ≤ 1 / s + 4 * c := by
      have := one_div_le_one_div_of_le hs hαs
      have : 4 * c * α ≤ 4 * c := by
        calc 4 * c * α ≤ 4 * c * 1 := mul_le_mul_of_nonneg_left hα1 (by positivity)
          _ = 4 * c := mul_one _
      linarith
    have h2 : d * (1 / α + 4 * c * α) ≤ δ₁ / 8 := by
      calc d * (1 / α + 4 * c * α) ≤ δ₁ / (8 * (1 / s + 4 * c)) * (1 / s + 4 * c) :=
            mul_le_mul hda h1 (by positivity) (by positivity)
        _ = δ₁ / 8 := by field_simp
    have h3 : c * (3 * ε + 2 * c * η) / γ ^ 3 ≤ c * (3 * ρ₀ + 2 * c * η) / (c * s) ^ 3 := by
      gcongr
    have h4 : c * (3 * ρ₀ + 2 * c * η) / (c * s) ^ 3 ≤ 3 * δ₁ / 8 := by
      rw [div_le_iff₀ (by positivity)]
      have e1 : c * (3 * ρ₀) ≤ δ₁ * (c * s) ^ 3 / 4 := by
        have := mul_le_mul_of_nonneg_left hρ₀a (by positivity : (0 : ℝ) ≤ 3 * c)
        have e : 3 * c * (δ₁ * (c * s) ^ 3 / (12 * c)) = δ₁ * (c * s) ^ 3 / 4 := by
          field_simp; ring
        linarith
      have e2 : c * (2 * c * η) ≤ δ₁ * (c * s) ^ 3 / 8 := by
        have := mul_le_mul_of_nonneg_left hηc (by positivity : (0 : ℝ) ≤ 2 * c ^ 2)
        have e : 2 * c ^ 2 * (δ₁ * (c * s) ^ 3 / (16 * c ^ 2)) = δ₁ * (c * s) ^ 3 / 8 := by
          field_simp; ring
        linarith
      have e3 : c * (3 * ρ₀ + 2 * c * η) = c * (3 * ρ₀) + c * (2 * c * η) := by ring
      rw [e3]
      linarith
    linarith
  · have hcγ : c * (2 / γ) = 2 / α := by rw [hγ]; field_simp
    have h2α : 2 / α ≤ 2 / s := div_le_div_of_nonneg_left (by norm_num) hs hαs
    have hεγ : ε / γ ^ 2 ≤ ρ₀ / (c * s) ^ 2 := div_le_div₀ hρ₀0.le hερ₀ (by positivity) hγ2
    have hδ : 2 / δE ≤ 2 / δ₁ := div_le_div_of_nonneg_left (by norm_num) hδ₁0 hδE
    have hin : 0 ≤ c * (2 / γ) * Q + d + ε / γ ^ 2 := by positivity
    have hstep : c * (2 / γ) * Q + d + ε / γ ^ 2 ≤
        2 / s * (Vmax * ρ₀) + δ₁ * η / 16 + ρ₀ / (c * s) ^ 2 := by
      rw [hcγ]
      have := mul_le_mul h2α hQ hQ0 (by positivity)
      linarith
    have e1 : 2 / δ₁ * (2 / s * (Vmax * ρ₀)) ≤ η / 4 := by
      have := mul_le_mul_of_nonneg_left hρ₀c (by positivity : (0 : ℝ) ≤ 4 * Vmax / (δ₁ * s))
      have e : 4 * Vmax / (δ₁ * s) * (δ₁ * η * s / (16 * Vmax)) = η / 4 := by
        field_simp; ring
      have e' : 2 / δ₁ * (2 / s * (Vmax * ρ₀)) = 4 * Vmax / (δ₁ * s) * ρ₀ := by
        field_simp; ring
      linarith
    have e2 : 2 / δ₁ * (ρ₀ / (c * s) ^ 2) ≤ η / 4 := by
      have := mul_le_mul_of_nonneg_left hρ₀b (by positivity : (0 : ℝ) ≤ 2 / (δ₁ * (c * s) ^ 2))
      have e : 2 / (δ₁ * (c * s) ^ 2) * (δ₁ * η * (c * s) ^ 2 / 8) = η / 4 := by
        field_simp; ring
      have e' : 2 / δ₁ * (ρ₀ / (c * s) ^ 2) = 2 / (δ₁ * (c * s) ^ 2) * ρ₀ := by
        field_simp
      linarith
    have e3 : 2 / δ₁ * (δ₁ * η / 16) = η / 8 := by field_simp; ring
    have e4 : 2 / δ₁ * (2 / s * (Vmax * ρ₀) + δ₁ * η / 16 + ρ₀ / (c * s) ^ 2) =
        2 / δ₁ * (2 / s * (Vmax * ρ₀)) + 2 / δ₁ * (δ₁ * η / 16) +
          2 / δ₁ * (ρ₀ / (c * s) ^ 2) := by ring
    calc 2 / δE * (c * (2 / γ) * Q + d + ε / γ ^ 2)
        ≤ 2 / δ₁ * (2 / s * (Vmax * ρ₀) + δ₁ * η / 16 + ρ₀ / (c * s) ^ 2) :=
          mul_le_mul hδ hstep hin (by positivity)
      _ < η := by linarith

/-- Real arithmetic: the final combination of the variance and the mean bound. -/
theorem fcm_arith_final {c s α γ δ₁ δE V Vmax d ε X : ℝ} (hc : 0 < c) (hs : 0 < s)
    (hαs : s ≤ α) (hγ : γ = c * α) (hδ₁0 : 0 < δ₁) (hδE : δ₁ ≤ δE) (hV0 : 0 ≤ V)
    (hVle : V ≤ Vmax) (hd0 : 0 ≤ d) (hε0 : 0 < ε) (hX0 : 0 ≤ X) (hX1 : X ≤ 1) :
    2 * (V * X) + 2 * (2 / δE * (c * (2 / γ) * (V * X) + d + ε / γ ^ 2)) ^ 2 ≤
      (2 * Vmax + 6 * (2 / δ₁) ^ 2 * ((2 * Vmax / s) ^ 2 + 1 + 1 / (c * s) ^ 4)) *
        (d ^ 2 + ε ^ 2 + X) := by
  have hα0 : 0 < α := lt_of_lt_of_le hs hαs
  have hcs : 0 < c * s := by positivity
  have hγs : c * s ≤ γ := by rw [hγ]; exact mul_le_mul_of_nonneg_left hαs hc.le
  have hγ2 : (c * s) ^ 2 ≤ γ ^ 2 := pow_le_pow_left₀ hcs.le hγs 2
  have hγ0 : 0 < γ := lt_of_lt_of_le hcs hγs
  have hδE0 : 0 < δE := lt_of_lt_of_le hδ₁0 hδE
  have hVmax0 : 0 ≤ Vmax := hV0.trans hVle
  set m := 2 / δE * (c * (2 / γ) * (V * X) + d + ε / γ ^ 2)
  have hm0 : 0 ≤ m := by positivity
  have hcγ : c * (2 / γ) = 2 / α := by rw [hγ]; field_simp
  have h2α : 2 / α ≤ 2 / s := div_le_div_of_nonneg_left (by norm_num) hs hαs
  have hδ : 2 / δE ≤ 2 / δ₁ := div_le_div_of_nonneg_left (by norm_num) hδ₁0 hδE
  have hεγ : ε / γ ^ 2 ≤ ε / (c * s) ^ 2 := div_le_div_of_nonneg_left hε0.le (by positivity) hγ2
  have hm : m ≤ 2 / δ₁ * (2 / s * Vmax * X + d + ε / (c * s) ^ 2) := by
    refine mul_le_mul hδ ?_ (by positivity) (by positivity)
    rw [hcγ]
    have := mul_le_mul h2α (mul_le_mul_of_nonneg_right hVle hX0) (by positivity) (by positivity)
    have e : 2 / s * (Vmax * X) = 2 / s * Vmax * X := by ring
    linarith
  have hm2 : m ^ 2 ≤ (2 / δ₁) ^ 2 * (3 * ((2 * Vmax / s) ^ 2 * X + d ^ 2 + ε ^ 2 / (c * s) ^ 4)) := by
    refine (pow_le_pow_left₀ hm0 hm 2).trans ?_
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (fcm_sq3_le _ _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hX2 : X ^ 2 ≤ X := by
      calc X ^ 2 = X * X := sq X
        _ ≤ X * 1 := mul_le_mul_of_nonneg_left hX1 hX0
        _ = X := mul_one X
    have e1 : (2 / s * Vmax * X) ^ 2 = (2 * Vmax / s) ^ 2 * X ^ 2 := by ring
    have e2 : (ε / (c * s) ^ 2) ^ 2 = ε ^ 2 / (c * s) ^ 4 := by ring
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_left hX2 (sq_nonneg (2 * Vmax / s))
    linarith
  have hVX : V * X ≤ Vmax * X := mul_le_mul_of_nonneg_right hVle hX0
  set q := (2 / δ₁) ^ 2
  set A := (2 * Vmax / s) ^ 2
  set B := 1 / (c * s) ^ 4
  have hq : 0 ≤ q := sq_nonneg _
  have hA : 0 ≤ A := sq_nonneg _
  have hB : 0 ≤ B := by positivity
  have hd2 := sq_nonneg d
  have hε2 := sq_nonneg ε
  have e : ε ^ 2 / (c * s) ^ 4 = B * ε ^ 2 := by simp only [B]; ring
  rw [e] at hm2
  have key : (2 * Vmax + 6 * q * (A + 1 + B)) * (d ^ 2 + ε ^ 2 + X) =
      2 * Vmax * X + 6 * q * (A * X + d ^ 2 + B * ε ^ 2) +
        (2 * Vmax * (d ^ 2 + ε ^ 2) + 6 * q * (A * (d ^ 2 + ε ^ 2) + (ε ^ 2 + X) + B * (d ^ 2 + X))) := by
    ring
  rw [key]
  have k1 : 0 ≤ 2 * Vmax * (d ^ 2 + ε ^ 2) + 6 * q * (A * (d ^ 2 + ε ^ 2) + (ε ^ 2 + X) +
      B * (d ^ 2 + X)) := by positivity
  have k2 : 2 * m ^ 2 ≤ 6 * q * (A * X + d ^ 2 + B * ε ^ 2) := by linarith
  linarith

/-- Real arithmetic for small `W`. -/
theorem fcm_arith_smallW {W₀ Wr y X : ℝ} (hW : 0 < Wr) (hWW₀ : Wr ≤ W₀) (hy0 : 0 < y)
    (hy2 : y ≤ 2) (hX : X = (Wr ^ 2)⁻¹ * (y ^ 3)⁻¹) :
    (W₀ + 1) ^ 2 ≤ 8 * W₀ ^ 2 * (W₀ + 1) ^ 2 * X := by
  have hW₀0 : 0 < W₀ := lt_of_lt_of_le hW hWW₀
  have h1 : (W₀ ^ 2)⁻¹ ≤ (Wr ^ 2)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ hW.le hWW₀ 2)
  have h8 : y ^ 3 ≤ 8 := by
    have := pow_le_pow_left₀ hy0.le hy2 3
    norm_num at this
    exact this
  have h2 : (8 : ℝ)⁻¹ ≤ (y ^ 3)⁻¹ := inv_anti₀ (by positivity) h8
  calc (W₀ + 1) ^ 2 = 8 * W₀ ^ 2 * (W₀ + 1) ^ 2 * ((W₀ ^ 2)⁻¹ * (8 : ℝ)⁻¹) := by field_simp
    _ ≤ 8 * W₀ ^ 2 * (W₀ + 1) ^ 2 * X := by rw [hX]; gcongr

/-- **`FcMeanSquare`**: `E|g_t - a|² ≤ C(d² + ε² + W⁻² y_t⁻³)` for `d ≤ d_*`, `ε = W^{-3/5}`,
from `ConditionalBlockGUECount` (the counting bound in the variance estimate) and
`GaussianLpGradient` (Gaussian Poincaré). -/
theorem fcMeanSquare_holds (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient) :
    FcMeanSquare := by
  obtain ⟨Cp, C, hCp, hC, hvar⟩ := fcm_heat_variance hcount hgrad
  intro b hb0 hb κ hκ
  set c := 1 - 2 * b with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  have hc1 : c ≤ 1 := by rw [hcdef]; linarith
  set κ' := min κ 2 with hκ'
  set s := Real.sqrt (4 - (2 - κ') ^ 2) / 2 with hsdef
  have hs : 0 < s := by
    have hk0 : 0 < κ' := lt_min hκ (by norm_num)
    have hk4 : κ' < 4 := (min_le_right _ _).trans_lt (by norm_num)
    have := Real.sqrt_pos.mpr (four_sub_sq_pos hk0 hk4)
    rw [hsdef]; positivity
  set δ₁ := min 1 (2 * c * s ^ 2) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min one_pos (by positivity)
  set Vmax := Cp * (16 * C * Real.sqrt 2 / Real.sqrt c + 1 + 2 / (c * s)) with hVmax
  have hVmax0 : 0 < Vmax := by rw [hVmax]; positivity
  set η := min (s / 2) (δ₁ * (c * s) ^ 3 / (16 * c ^ 2)) with hηdef
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  set dstar := min (δ₁ / (8 * (1 / s + 4 * c))) (δ₁ * η / 16) with hdstar
  have hdstar0 : 0 < dstar := lt_min (by positivity) (by positivity)
  set ρ₀ := min (min (δ₁ * (c * s) ^ 3 / (12 * c)) (δ₁ * η * (c * s) ^ 2 / 8))
    (δ₁ * η * s / (16 * Vmax)) with hρ₀
  have hρ₀0 : 0 < ρ₀ := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  set W₀ := (ρ₀ ^ 5)⁻¹ with hW₀
  set C₁ := 2 * Vmax + 6 * (2 / δ₁) ^ 2 * ((2 * Vmax / s) ^ 2 + 1 + 1 / (c * s) ^ 4) with hC₁
  set C₂ := 8 * W₀ ^ 2 * (W₀ + 1) ^ 2 with hC₂
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  refine ⟨dstar, C₁ + C₂, hdstar0, fun W hW F hF E hE => ?_⟩
  intro a z₀ d hd t ht
  -- facts on `E` and `a`
  have hE2 : |E| < 2 := abs_lt_two_of_mem_bulkInterval hκ hE
  have hE' : E ∈ bulkInterval κ' := by
    have h1 := hE.1; have h2 := hE.2
    have : κ' ≤ κ := min_le_left _ _
    exact ⟨by linarith, by linarith⟩
  have hαs : s ≤ -a.im := by
    have := matchedA_im_le_of_mem_bulkInterval hE'
    rw [hsdef]; linarith
  have hα0 : 0 < -a.im := lt_of_lt_of_le hs hαs
  have hα1 : -a.im ≤ 1 := by
    have h1 : |a.im| ≤ ‖a‖ := Complex.abs_im_le_norm a
    rw [norm_matchedA hE2.le] at h1
    linarith [neg_abs_le a.im, abs_le.mp h1]
  have hγ : fcGamma b E = c * -a.im := rfl
  have hcs : 0 < c * s := by positivity
  have hγs : c * s ≤ fcGamma b E := by rw [hγ]; exact mul_le_mul_of_nonneg_left hαs hc.le
  have hγ0 : 0 < fcGamma b E := lt_of_lt_of_le hcs hγs
  have hγ1 : fcGamma b E ≤ 1 := by
    rw [hγ]; calc c * -a.im ≤ 1 * 1 := mul_le_mul hc1 hα1 hα0.le zero_le_one
      _ = 1 := one_mul 1
  have hδE : δ₁ ≤ min 1 (2 * c * (-a.im) ^ 2) := by
    rw [hδ₁]
    have h1 : s ^ 2 ≤ (-a.im) ^ 2 := pow_le_pow_left₀ hs.le hαs 2
    exact min_le_min le_rfl (mul_le_mul_of_nonneg_left h1 (by positivity))
  set V := Cp * (16 * C * Real.sqrt 2 / Real.sqrt c + 1 + 2 / fcGamma b E) with hVdef
  have hV0 : 0 ≤ V := by rw [hVdef]; positivity
  have hVle : V ≤ Vmax := by
    rw [hVdef, hVmax]
    gcongr
  -- the height `ε = W^{-3/5}` and `ρ = W^{-1/5}`
  have hε0 : 0 < fcHeight W := fcHeight_pos hW
  have hε1 : fcHeight W ≤ 1 := fcHeight_le_one hW
  obtain ⟨hερ, hρ1, hWε, hεW, hρ5⟩ := fcm_rho hW
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hγ' := fcd_gamma_nonneg hb E
  have h1t : 0 ≤ 1 - t := by linarith [ht.2]
  have h1t' : 1 - t ≤ 1 := by linarith [ht.1]
  have hyε : fcHeight W ≤ fcHeight' b E (fcHeight W) t := by
    have := mul_nonneg h1t hγ'
    unfold fcHeight'; linarith
  have hy0 : 0 < fcHeight' b E (fcHeight W) t := lt_of_lt_of_le hε0 hyε
  have hy2 : fcHeight' b E (fcHeight W) t ≤ 2 := by
    have := mul_le_of_le_one_left hγ' h1t'
    unfold fcHeight'; linarith
  set X := ((W : ℝ) ^ 2)⁻¹ * (fcHeight' b E (fcHeight W) t ^ 3)⁻¹ with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hXρ : X ≤ (W : ℝ) ^ (-(1 / 5 : ℝ)) := by
    rw [← hWε, hXdef, ← mul_inv]
    apply inv_anti₀ (by positivity)
    gcongr
  -- transfer to Gaussian coordinates
  have htr : (∫ A, ‖fcHeatTrace b E F (fcHeight W) t A - a‖ ^ 2
      ∂gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) =
      ∫ r, ‖fcHeatTrace b E F (fcHeight W) t (gueOfCoords W (fcdTau b W) r) - a‖ ^ 2
        ∂stdGaussCoordLaw (GaussCoord W) := by
    refine fcd_integral_gue W _ (fun A => ‖fcHeatTrace b E F (fcHeight W) t A - a‖ ^ 2) ?_
    exact (((fcd_measurable_heatTrace b E F (fcHeight W) t (measurable_hermPart W)).sub
      measurable_const).norm.pow_const 2).aestronglyMeasurable
  rw [htr]
  have hRHS0 : 0 ≤ d ^ 2 + fcHeight W ^ 2 + X := by positivity
  have hfinal : C₁ * (d ^ 2 + fcHeight W ^ 2 + X) ≤ (C₁ + C₂) * (d ^ 2 + fcHeight W ^ 2 + X) := by
    have := mul_nonneg hC₂0 hRHS0
    linarith
  by_cases hbig : (W : ℝ) ^ (-(1 / 5 : ℝ)) ≤ ρ₀
  · -- main case
    have hdd : ‖fcmTr ((fcmZ0 b E • (1 : Matrix (Fin W) (Fin W) ℂ) - F)⁻¹) - matchedA E‖ = d := by
      rw [fcmTr_eq]; rfl
    have hvarE := fun t' ht' K => hvar b hb0 hb E hγ0 W hW F hF (fcHeight W) hε0 t' ht' K
    have hη : η ≤ -(matchedA E).im / 2 := (min_le_left _ _).trans (by linarith)
    have hQ : V / ((W : ℝ) ^ 2 * fcHeight W ^ 3) ≤ Vmax * ρ₀ := by
      rw [div_eq_mul_inv, hWε]
      exact mul_le_mul hVle hbig (by positivity) hVmax0.le
    obtain ⟨hsmall, hboot⟩ := fcm_arith_small (γ := fcGamma b E)
      (δE := min 1 (2 * c * (-a.im) ^ 2)) hc hs hαs hα1 hγ hδ₁0 hδE hVmax0 hη0
      (min_le_right _ _) ((min_le_left _ _).trans (min_le_left _ _))
      ((min_le_left _ _).trans (min_le_right _ _)) (min_le_right _ _) (norm_nonneg _)
      (hd.trans (min_le_left _ _)) (hd.trans (min_le_right _ _)) hε0 (hερ.trans hbig)
      (by positivity) hQ
    have hglue := fcm_glue hb hE2 hW hF hε0 hV0 hvarE hη (by rw [hdd]; exact hsmall)
      (by rw [hdd]; exact hboot) ht
    rw [hdd] at hglue
    have hVX : V / ((W : ℝ) ^ 2 * fcHeight' b E (fcHeight W) t ^ 3) = V * X := by
      rw [div_eq_mul_inv, mul_inv]
    rw [hVX] at hglue
    refine hglue.trans (le_trans ?_ hfinal)
    exact fcm_arith_final hc hs hαs hγ hδ₁0 hδE hV0 hVle (norm_nonneg _) hε0 hX0 (hXρ.trans hρ1)
  · -- small `W`
    push Not at hbig
    have hWW₀ : (W : ℝ) ≤ W₀ := by
      have h5 : ρ₀ ^ 5 < ((W : ℝ) ^ (-(1 / 5 : ℝ))) ^ 5 :=
        pow_lt_pow_left₀ hbig hρ₀0.le (by norm_num)
      rw [hρ5] at h5
      rw [hW₀]
      exact ((lt_inv_comm₀ (pow_pos hρ₀0 5) hW').mp h5).le
    have hga : ∀ r, ‖fcHeatTrace b E F (fcHeight W) t (gueOfCoords W (fcdTau b W) r) - a‖ ^ 2 ≤
        (W₀ + 1) ^ 2 := fun r => by
      refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2
      rw [norm_matchedA hE2.le]
      have := fcd_heatTrace_le E hb hF hε0 ht.2.le hW (gueOfCoords_isHermitian W (fcdTau b W) r)
      linarith
    have hL : ∫ r, ‖fcHeatTrace b E F (fcHeight W) t (gueOfCoords W (fcdTau b W) r) - a‖ ^ 2
        ∂stdGaussCoordLaw (GaussCoord W) ≤ (W₀ + 1) ^ 2 := by
      have h0 : ∀ r, 0 ≤ ‖fcHeatTrace b E F (fcHeight W) t (gueOfCoords W (fcdTau b W) r) - a‖ ^ 2 :=
        fun r => sq_nonneg _
      calc _ ≤ ∫ _r, (W₀ + 1) ^ 2 ∂stdGaussCoordLaw (GaussCoord W) :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall h0) (integrable_const _)
              (Filter.Eventually.of_forall hga)
        _ = (W₀ + 1) ^ 2 := by rw [integral_const, probReal_univ, one_smul]
    have hXlow := fcm_arith_smallW hW' hWW₀ hy0 hy2 hXdef
    rw [← hC₂] at hXlow
    calc _ ≤ C₂ * X := hL.trans hXlow
      _ ≤ C₁ * (d ^ 2 + fcHeight W ^ 2 + X) + C₂ * (d ^ 2 + fcHeight W ^ 2) + C₂ * X := by
          have := mul_nonneg hC₁0 hRHS0
          have := mul_nonneg hC₂0 (by positivity : (0 : ℝ) ≤ d ^ 2 + fcHeight W ^ 2)
          linarith
      _ = (C₁ + C₂) * (d ^ 2 + fcHeight W ^ 2 + X) := by ring

/-- **The fresh-count lemma** (`FreshCountContract`), from `ConditionalBlockGUECount` and
`GaussianLpGradient`. -/
theorem freshCount_holds (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient) :
    FreshCountContract :=
  freshCount_holds_of_heat hcount fcHeatDerivative_holds (fcMeanSquare_holds hcount hgrad)

end BlockBand.Layers
