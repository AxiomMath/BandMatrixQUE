module

public import BlockBand.LocalWindow.ProofPartTwoTransfer

/-!
# Stability of the root and of the window centre in `K`

The Dyson root, its resolvent and the window centre are Lipschitz in the deformation `K`. The
argument is the one of `ProofETH.dyson_stability` / `dyson_lipschitz` and
`ProofETH.root_lipschitz`, with two **different** Hermitian deformations `F₁, F₂`: the
stability bound `Re(N - s Tr M₁M₂) ≥ (s/2) N (Im m₁ + Im m₂)²` only uses that each `M_j` is the
root resolvent of its own `F_j`.

## Main results

* `opNorm_smul_one_le`, `norm_trace_mul_mul_le_opNorm` (`|Tr(X D Y)| ≤ ‖D‖ √frob X √frob Y`),
  `s_sqrt_frob_mul_le` (`s √frob M₁ √frob M₂ ≤ N`).
* `dyson_stability_two`, `stability_lower_two`: the stability bound for two deformations.
* `dyson_diff_identity_two`:
  `(m₁ - m₂)(N - s Tr M₁M₂) = (z₁ - z₂) Tr M₁M₂ + Tr(M₁ (F₂ - F₁) M₂)`.
* **`root_lipschitz_two`**: `|m₁ - m₂| ≤ L (|z₁ - z₂| + ‖F₁ - F₂‖)`, `L = rootLip s v₀`.
* **`resolvent_lipschitz_two`**: `‖M₁ - M₂‖ ≤ L' (|z₁ - z₂| + ‖F₁ - F₂‖)`, `L' = resLip s v₀`.
* **`pairCentre_sub_le`**: for pair contractions `J`, real `x, y` and roots of `K₁` at `x`,
  `K₂` at `y` with `Im ≥ v₀`:
  `|pairCentre J K₁ s x - pairCentre J K₂ s y| ≤ (2 L'/v₀)(|x - y| + ‖K₁ - K₂‖)`.
* **`windowCenter_sub_le`**: the same for `windowCenter` (real parts).
* `windowCenter_sub_le_of_rootRectangle`: the same from two root rectangles.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.LawBridge BlockBand.LocalWindow.ProofETH
open scoped Matrix.Norms.L2Operator

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `sqNorm (c • v) = |c|² sqNorm v`. -/
theorem sqNorm_smul (c : ℂ) (v : ι → ℂ) : sqNorm (c • v) = ‖c‖ ^ 2 * sqNorm v := by
  unfold sqNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]

/-- `‖c • 1‖ ≤ |c|` (`L²` operator norm). -/
theorem opNorm_smul_one_le (c : ℂ) : ‖c • (1 : Matrix ι ι ℂ)‖ ≤ ‖c‖ := by
  refine opNorm_le_of_sqNorm (norm_nonneg c) fun v => le_of_eq ?_
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, sqNorm_smul]

/-- `|Tr(X D Y)| ≤ ‖D‖ √frob X √frob Y`. -/
theorem norm_trace_mul_mul_le_opNorm (X D Y : Matrix ι ι ℂ) :
    ‖(X * D * Y).trace‖ ≤ ‖D‖ * (Real.sqrt (frob X) * Real.sqrt (frob Y)) := by
  have h1 := norm_trace_mul_le (X * D) Y
  have h2 : frob (X * D) ≤ ‖D‖ ^ 2 * frob X := frob_mul_right_le (fun v => by
      have := sqNorm_mulVec_le_opNorm Dᴴ v
      rwa [Matrix.l2_opNorm_conjTranspose] at this) X
  have h3 : Real.sqrt (frob (X * D)) ≤ ‖D‖ * Real.sqrt (frob X) := by
    calc Real.sqrt (frob (X * D)) ≤ Real.sqrt (‖D‖ ^ 2 * frob X) := Real.sqrt_le_sqrt h2
      _ = ‖D‖ * Real.sqrt (frob X) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  calc _ ≤ Real.sqrt (frob (X * D)) * Real.sqrt (frob Y) := h1
    _ ≤ (‖D‖ * Real.sqrt (frob X)) * Real.sqrt (frob Y) :=
        mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- `s √frob M₁ √frob M₂ ≤ N` for two root resolvents (of possibly different deformations). -/
theorem s_sqrt_frob_mul_le [Nonempty ι] {F₁ F₂ : Matrix ι ι ℂ} (hF₁ : F₁.IsHermitian)
    (hF₂ : F₂.IsHermitian) {s : ℝ} (hs : 0 < s) {z₁ z₂ m₁ m₂ : ℂ} (hz₁ : 0 ≤ z₁.im)
    (hz₂ : 0 ≤ z₂.im) (h₁ : IsDysonRoot F₁ s z₁ m₁) (h₂ : IsDysonRoot F₂ s z₂ m₂) :
    s * (Real.sqrt (frob (F₁ - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹) *
        Real.sqrt (frob (F₂ - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹)) ≤
      Fintype.card ι := by
  set M₁ := (F₁ - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹
  set M₂ := (F₂ - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹
  have hf₁ := s_frob_le hF₁ hs hz₁ h₁
  have hf₂ := s_frob_le hF₂ hs hz₂ h₂
  have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have e : s * (Real.sqrt (frob M₁) * Real.sqrt (frob M₂)) =
      Real.sqrt (s * frob M₁) * Real.sqrt (s * frob M₂) := by
    rw [Real.sqrt_mul hs.le, Real.sqrt_mul hs.le]
    have := Real.mul_self_sqrt hs.le
    linear_combination (-(Real.sqrt (frob M₁) * Real.sqrt (frob M₂))) * this
  rw [e]
  calc Real.sqrt (s * frob M₁) * Real.sqrt (s * frob M₂)
      ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (Fintype.card ι) :=
        mul_le_mul (Real.sqrt_le_sqrt hf₁) (Real.sqrt_le_sqrt hf₂) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = Fintype.card ι := Real.mul_self_sqrt hN

/-- **Stability of the Dyson equation for two deformations**: for a root `m₁` of `F₁` at `z₁`
and a root `m₂` of `F₂` at `z₂` (`Im z_j ≥ 0`),
`Re (N - s Tr M₁M₂) ≥ (s/2) N (Im m₁ + Im m₂)²` (proof of `dyson_stability`, which uses each
deformation only through its own root). -/
theorem dyson_stability_two [Nonempty ι] {F₁ F₂ : Matrix ι ι ℂ} (hF₁ : F₁.IsHermitian)
    (hF₂ : F₂.IsHermitian) {s : ℝ} (hs : 0 < s) {z₁ z₂ m₁ m₂ : ℂ} (hz₁ : 0 ≤ z₁.im)
    (hz₂ : 0 ≤ z₂.im) (h₁ : IsDysonRoot F₁ s z₁ m₁) (h₂ : IsDysonRoot F₂ s z₂ m₂) :
    s / 2 * Fintype.card ι * (m₁.im + m₂.im) ^ 2 ≤
      Fintype.card ι - s * ((F₁ - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ *
        (F₂ - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹).trace.re := by
  set M₁ := (F₁ - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹
  set M₂ := (F₂ - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹
  set N : ℝ := (Fintype.card ι : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hNc : ((N : ℝ) : ℂ) = (Fintype.card ι : ℂ) := Complex.ofReal_natCast _
  have hNne : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  set Y := M₁ - M₂ᴴ
  have hY : frob Y = frob M₁ + frob M₂ - 2 * (M₁ * M₂).trace.re := by
    have h := trace_mul_conjTranspose Y
    have e : Y * Yᴴ = M₁ * M₁ᴴ - M₁ * M₂ - (M₁ * M₂)ᴴ + M₂ᴴ * M₂ := by
      simp only [Y, conjTranspose_sub, conjTranspose_conjTranspose, conjTranspose_mul,
        Matrix.mul_sub, Matrix.sub_mul]
      abel
    rw [e, trace_add, trace_sub, trace_sub, trace_conjTranspose, trace_mul_comm M₂ᴴ M₂,
      trace_mul_conjTranspose, trace_mul_conjTranspose] at h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.star_def,
      Complex.conj_re] at this
    linarith
  have htrY : Y.trace.im = N * (m₁.im + m₂.im) := by
    have e1 : M₁.trace = N * m₁ := by
      rw [h₁.2, ← mul_assoc, hNc, mul_inv_cancel₀ hNne, one_mul]
    have e2 : M₂.trace = N * m₂ := by
      rw [h₂.2, ← mul_assoc, hNc, mul_inv_cancel₀ hNne, one_mul]
    simp only [Y, trace_sub, trace_conjTranspose, e1, e2, Complex.sub_im, Complex.star_def,
      Complex.conj_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, map_mul, Complex.conj_ofReal]
    ring
  have hYlow : N * (m₁.im + m₂.im) ^ 2 ≤ frob Y := by
    have h1 := norm_trace_sq_le Y
    have h2 : |Y.trace.im| ≤ ‖Y.trace‖ := Complex.abs_im_le_norm _
    have h3 : (Y.trace.im) ^ 2 ≤ ‖Y.trace‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    rw [htrY] at h3
    have : N ^ 2 * (m₁.im + m₂.im) ^ 2 ≤ N * frob Y := by nlinarith
    nlinarith
  have hf₁ := s_frob_le hF₁ hs hz₁ h₁
  have hf₂ := s_frob_le hF₂ hs hz₂ h₂
  nlinarith

/-- `2 s N v₀² ≤ |N - s Tr M₁M₂|` for roots of two deformations with `Im m_j ≥ v₀ ≥ 0`. -/
theorem stability_lower_two [Nonempty ι] {F₁ F₂ : Matrix ι ι ℂ} (hF₁ : F₁.IsHermitian)
    (hF₂ : F₂.IsHermitian) {s : ℝ} (hs : 0 < s) {z₁ z₂ m₁ m₂ : ℂ} (hz₁ : 0 ≤ z₁.im)
    (hz₂ : 0 ≤ z₂.im) (h₁ : IsDysonRoot F₁ s z₁ m₁) (h₂ : IsDysonRoot F₂ s z₂ m₂) {v₀ : ℝ}
    (hv₀ : 0 ≤ v₀) (hv₁ : v₀ ≤ m₁.im) (hv₂ : v₀ ≤ m₂.im) :
    2 * s * Fintype.card ι * v₀ ^ 2 ≤
      ‖(Fintype.card ι : ℂ) - s * ((F₁ - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ *
        (F₂ - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹).trace‖ := by
  have hstab := dyson_stability_two hF₁ hF₂ hs hz₁ hz₂ h₁ h₂
  have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hsq : 4 * v₀ ^ 2 ≤ (m₁.im + m₂.im) ^ 2 := by nlinarith
  have hre : ((Fintype.card ι : ℂ) - s * ((F₁ - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ *
        (F₂ - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹).trace).re =
      Fintype.card ι - s * ((F₁ - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ *
        (F₂ - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹).trace.re := by
    simp [Complex.mul_re]
  refine le_trans ?_ (Complex.re_le_norm _)
  rw [hre]
  have : 2 * s * Fintype.card ι * v₀ ^ 2 ≤ s / 2 * Fintype.card ι * (m₁.im + m₂.im) ^ 2 := by
    have h1 : 0 ≤ s / 2 * Fintype.card ι := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsq h1]
  linarith

/-- The difference identity for roots of two deformations:
`(m₁ - m₂)(N - s Tr M₁M₂) = (z₁ - z₂) Tr M₁M₂ + Tr(M₁ (F₂ - F₁) M₂)`. -/
theorem dyson_diff_identity_two [Nonempty ι] {F₁ F₂ : Matrix ι ι ℂ} (hF₁ : F₁.IsHermitian)
    (hF₂ : F₂.IsHermitian) {s : ℝ} (hs : 0 < s) {z₁ z₂ m₁ m₂ : ℂ} (hz₁ : 0 ≤ z₁.im)
    (hz₂ : 0 ≤ z₂.im) (h₁ : IsDysonRoot F₁ s z₁ m₁) (h₂ : IsDysonRoot F₂ s z₂ m₂) :
    (m₁ - m₂) * ((Fintype.card ι : ℂ) - s * ((F₁ - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ *
        (F₂ - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹).trace) =
      (z₁ - z₂) * ((F₁ - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ *
        (F₂ - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹).trace +
      ((F₁ - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ * (F₂ - F₁) *
        (F₂ - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹).trace := by
  set w₁ := z₁ + (s : ℂ) * m₁ with hw₁def
  set w₂ := z₂ + (s : ℂ) * m₂ with hw₂def
  set M₁ := (F₁ - w₁ • (1 : Matrix ι ι ℂ))⁻¹
  set M₂ := (F₂ - w₂ • (1 : Matrix ι ι ℂ))⁻¹
  have hw₁ := (dysonRoot_w_im_pos hs hz₁ h₁.1).ne'
  have hw₂ := (dysonRoot_w_im_pos hs hz₂ h₂.1).ne'
  have hNne : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hres := ProofETH.inv_sub_inv (det_resolvent_ne_zero hF₁ hw₁) (det_resolvent_ne_zero hF₂ hw₂)
  have hX : F₂ - w₂ • (1 : Matrix ι ι ℂ) - (F₁ - w₁ • (1 : Matrix ι ι ℂ)) =
      (F₂ - F₁) + (w₁ - w₂) • (1 : Matrix ι ι ℂ) := by
    rw [sub_smul]; abel
  rw [hX, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    at hres
  have e := congrArg Matrix.trace hres
  rw [trace_sub, trace_add, trace_smul, smul_eq_mul] at e
  have e1 : M₁.trace = (Fintype.card ι : ℂ) * m₁ := by
    conv_rhs => rw [h₁.2]
    rw [← mul_assoc, mul_inv_cancel₀ hNne, one_mul]
  have e2 : M₂.trace = (Fintype.card ι : ℂ) * m₂ := by
    conv_rhs => rw [h₂.2]
    rw [← mul_assoc, mul_inv_cancel₀ hNne, one_mul]
  rw [e1, e2] at e
  have hw : w₁ - w₂ = (z₁ - z₂) + (s : ℂ) * (m₁ - m₂) := by rw [hw₁def, hw₂def]; ring
  rw [hw] at e
  linear_combination e

/-- **Lipschitz bound of the root in `(z, F)`**: for roots `m₁` of `F₁` at `z₁` and `m₂` of `F₂`
at `z₂` (`Im z_j ≥ 0`, `Im m_j ≥ v₀ > 0`),
`|m₁ - m₂| ≤ rootLip s v₀ (|z₁ - z₂| + ‖F₁ - F₂‖)` (`L²` operator norm). -/
theorem root_lipschitz_two [Nonempty ι] {F₁ F₂ : Matrix ι ι ℂ} (hF₁ : F₁.IsHermitian)
    (hF₂ : F₂.IsHermitian) {s : ℝ} (hs : 0 < s) {z₁ z₂ m₁ m₂ : ℂ} (hz₁ : 0 ≤ z₁.im)
    (hz₂ : 0 ≤ z₂.im) (h₁ : IsDysonRoot F₁ s z₁ m₁) (h₂ : IsDysonRoot F₂ s z₂ m₂) {v₀ : ℝ}
    (hv₀ : 0 < v₀) (hv₁ : v₀ ≤ m₁.im) (hv₂ : v₀ ≤ m₂.im) :
    ‖m₁ - m₂‖ ≤ rootLip s v₀ * (‖z₁ - z₂‖ + ‖F₁ - F₂‖) := by
  set M₁ := (F₁ - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹
  set M₂ := (F₂ - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹
  set N : ℝ := (Fintype.card ι : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hid := dyson_diff_identity_two hF₁ hF₂ hs hz₁ hz₂ h₁ h₂
  have hlow := stability_lower_two hF₁ hF₂ hs hz₁ hz₂ h₁ h₂ hv₀.le hv₁ hv₂
  have hsq := s_sqrt_frob_mul_le hF₁ hF₂ hs hz₁ hz₂ h₁ h₂
  have ht : s * ‖(M₁ * M₂).trace‖ ≤ N :=
    (mul_le_mul_of_nonneg_left (norm_trace_mul_le M₁ M₂) hs.le).trans hsq
  have hD : s * ‖(M₁ * (F₂ - F₁) * M₂).trace‖ ≤ ‖F₁ - F₂‖ * N := by
    have h := norm_trace_mul_mul_le_opNorm M₁ (F₂ - F₁) M₂
    rw [← norm_neg (F₂ - F₁), neg_sub] at h
    calc s * ‖(M₁ * (F₂ - F₁) * M₂).trace‖
        ≤ s * (‖F₁ - F₂‖ * (Real.sqrt (frob M₁) * Real.sqrt (frob M₂))) :=
          mul_le_mul_of_nonneg_left h hs.le
      _ = ‖F₁ - F₂‖ * (s * (Real.sqrt (frob M₁) * Real.sqrt (frob M₂))) := by ring
      _ ≤ ‖F₁ - F₂‖ * N := mul_le_mul_of_nonneg_left hsq (norm_nonneg _)
  have hnorm := congrArg norm hid
  rw [norm_mul] at hnorm
  have hR : ‖(z₁ - z₂) * (M₁ * M₂).trace + (M₁ * (F₂ - F₁) * M₂).trace‖ ≤
      ‖z₁ - z₂‖ * ‖(M₁ * M₂).trace‖ + ‖(M₁ * (F₂ - F₁) * M₂).trace‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
  have hL : ‖m₁ - m₂‖ * (2 * s * N * v₀ ^ 2) ≤
      ‖z₁ - z₂‖ * ‖(M₁ * M₂).trace‖ + ‖(M₁ * (F₂ - F₁) * M₂).trace‖ := by
    calc ‖m₁ - m₂‖ * (2 * s * N * v₀ ^ 2) ≤ ‖m₁ - m₂‖ * ‖(Fintype.card ι : ℂ) - s * (M₁ * M₂).trace‖ :=
          mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
      _ = _ := hnorm
      _ ≤ _ := hR
  have hsL : s * (‖m₁ - m₂‖ * (2 * s * N * v₀ ^ 2)) ≤ (‖z₁ - z₂‖ + ‖F₁ - F₂‖) * N := by
    have := mul_le_mul_of_nonneg_left hL hs.le
    nlinarith [mul_le_mul_of_nonneg_left ht (norm_nonneg (z₁ - z₂)), norm_nonneg (z₁ - z₂)]
  have hpos : 0 < 2 * s ^ 2 * v₀ ^ 2 := by positivity
  have h2 : ‖m₁ - m₂‖ * (2 * s ^ 2 * v₀ ^ 2) ≤ ‖z₁ - z₂‖ + ‖F₁ - F₂‖ := by
    have e : s * (‖m₁ - m₂‖ * (2 * s * N * v₀ ^ 2)) = (‖m₁ - m₂‖ * (2 * s ^ 2 * v₀ ^ 2)) * N := by
      ring
    rw [e] at hsL
    exact le_of_mul_le_mul_right hsL hN
  unfold rootLip
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  exact h2

/-- **Lipschitz bound of the root resolvent in `(z, F)`**:
`‖M₁ - M₂‖ ≤ resLip s v₀ (|z₁ - z₂| + ‖F₁ - F₂‖)`. -/
theorem resolvent_lipschitz_two [Nonempty ι] {F₁ F₂ : Matrix ι ι ℂ} (hF₁ : F₁.IsHermitian)
    (hF₂ : F₂.IsHermitian) {s : ℝ} (hs : 0 < s) {z₁ z₂ m₁ m₂ : ℂ} (hz₁ : 0 ≤ z₁.im)
    (hz₂ : 0 ≤ z₂.im) (h₁ : IsDysonRoot F₁ s z₁ m₁) (h₂ : IsDysonRoot F₂ s z₂ m₂) {v₀ : ℝ}
    (hv₀ : 0 < v₀) (hv₁ : v₀ ≤ m₁.im) (hv₂ : v₀ ≤ m₂.im) :
    ‖(F₁ - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ -
        (F₂ - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹‖ ≤
      resLip s v₀ * (‖z₁ - z₂‖ + ‖F₁ - F₂‖) := by
  set w₁ := z₁ + (s : ℂ) * m₁ with hw₁def
  set w₂ := z₂ + (s : ℂ) * m₂ with hw₂def
  have hw₁ := (dysonRoot_w_im_pos hs hz₁ h₁.1).ne'
  have hw₂ := (dysonRoot_w_im_pos hs hz₂ h₂.1).ne'
  rw [ProofETH.inv_sub_inv (det_resolvent_ne_zero hF₁ hw₁) (det_resolvent_ne_zero hF₂ hw₂)]
  have hM₁ := opNorm_root_resolvent_le hF₁ hs hz₁ hv₀ hv₁
  have hM₂ := opNorm_root_resolvent_le hF₂ hs hz₂ hv₀ hv₂
  have hm := root_lipschitz_two hF₁ hF₂ hs hz₁ hz₂ h₁ h₂ hv₀ hv₁ hv₂
  have hX : F₂ - w₂ • (1 : Matrix ι ι ℂ) - (F₁ - w₁ • (1 : Matrix ι ι ℂ)) =
      (F₂ - F₁) + (w₁ - w₂) • (1 : Matrix ι ι ℂ) := by
    rw [sub_smul]; abel
  have hw : ‖w₁ - w₂‖ ≤ ‖z₁ - z₂‖ + s * (rootLip s v₀ * (‖z₁ - z₂‖ + ‖F₁ - F₂‖)) := by
    have e : w₁ - w₂ = (z₁ - z₂) + (s : ℂ) * (m₁ - m₂) := by rw [hw₁def, hw₂def]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hm hs.le) _
  have hXn : ‖F₂ - w₂ • (1 : Matrix ι ι ℂ) - (F₁ - w₁ • (1 : Matrix ι ι ℂ))‖ ≤
      (1 + s * rootLip s v₀) * (‖z₁ - z₂‖ + ‖F₁ - F₂‖) := by
    rw [hX]
    refine (norm_add_le _ _).trans ?_
    have h1 := opNorm_smul_one_le (ι := ι) (w₁ - w₂)
    rw [← norm_neg (F₂ - F₁), neg_sub]
    have := rootLip_nonneg s v₀
    nlinarith [norm_nonneg (z₁ - z₂), norm_nonneg (F₁ - F₂)]
  have hS0 : 0 ≤ (s * v₀)⁻¹ := inv_nonneg.mpr (mul_pos hs hv₀).le
  have hA0 : 0 ≤ (1 + s * rootLip s v₀) * (‖z₁ - z₂‖ + ‖F₁ - F₂‖) := by
    have := rootLip_nonneg s v₀
    positivity
  unfold resLip
  calc ‖(F₁ - w₁ • (1 : Matrix ι ι ℂ))⁻¹ *
        (F₂ - w₂ • (1 : Matrix ι ι ℂ) - (F₁ - w₁ • (1 : Matrix ι ι ℂ))) *
        (F₂ - w₂ • (1 : Matrix ι ι ℂ))⁻¹‖
      ≤ ‖(F₁ - w₁ • (1 : Matrix ι ι ℂ))⁻¹‖ *
          ‖F₂ - w₂ • (1 : Matrix ι ι ℂ) - (F₁ - w₁ • (1 : Matrix ι ι ℂ))‖ *
          ‖(F₂ - w₂ • (1 : Matrix ι ι ℂ))⁻¹‖ := by
        refine (norm_mul_le _ _).trans ?_
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (s * v₀)⁻¹ * ((1 + s * rootLip s v₀) * (‖z₁ - z₂‖ + ‖F₁ - F₂‖)) * (s * v₀)⁻¹ := by
        refine mul_le_mul (mul_le_mul hM₁ hXn (norm_nonneg _) hS0) hM₂ (norm_nonneg _)
          (mul_nonneg hS0 hA0)
    _ = (1 + s * rootLip s v₀) * ((s * v₀)⁻¹) ^ 2 * (‖z₁ - z₂‖ + ‖F₁ - F₂‖) := by ring

end Generic

variable {p : Parameters} {i : ZMod p.n}

/-- **Stability of the window centre in `(λ, K)`** (grid in the window centre
and in the deformation): for Hermitian pair deformations `K₁, K₂`, real `x, y`, Dyson roots
`m₁` of `K₁` at `x` and `m₂` of `K₂` at `y` with `Im m_j ≥ v₀ > 0` and a pair contraction `J`:
`|pairCentre J K₁ s x - pairCentre J K₂ s y| ≤ (2 resLip(s, v₀)/v₀)(|x - y| + ‖K₁ - K₂‖)`. -/
theorem pairCentre_sub_le {K₁ K₂ J : PairMatrix p i} (hK₁ : K₁.IsHermitian)
    (hK₂ : K₂.IsHermitian) (hJn : ‖J‖ ≤ 1) {s v₀ : ℝ} (hs : 0 < s) (hv₀ : 0 < v₀) {x y : ℝ}
    {m₁ m₂ : ℂ} (hm₁ : IsDysonRoot K₁ s (x : ℂ) m₁) (hm₂ : IsDysonRoot K₂ s (y : ℂ) m₂)
    (hv₁ : v₀ ≤ m₁.im) (hv₂ : v₀ ≤ m₂.im) :
    ‖pairCentre J K₁ s x - pairCentre J K₂ s y‖ ≤
      2 * resLip s v₀ / v₀ * (|x - y| + ‖K₁ - K₂‖) := by
  have : Nonempty (PairSite p i) := ⟨⟨(i, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩
  have hp1 : BlockBand.LocalWindow.pairDyson p i K₁ s x = m₁ :=
    pairDyson_eq_of_isDysonRoot p i hK₁ hs (by simp) hm₁
  have hp2 : BlockBand.LocalWindow.pairDyson p i K₂ s y = m₂ :=
    pairDyson_eq_of_isDysonRoot p i hK₂ hs (by simp) hm₂
  set Rx := (K₁ - ((x : ℂ) + (s : ℂ) * m₁) • (1 : PairMatrix p i))⁻¹ with hRx
  set Ry := (K₂ - ((y : ℂ) + (s : ℂ) * m₂) • (1 : PairMatrix p i))⁻¹ with hRy
  have hgx : BlockBand.LocalWindow.windowGamma p i K₁ s x = (s : ℂ) • (Rx * Rxᴴ) := by
    rw [windowGamma_eq, hp1]
  have hgy : BlockBand.LocalWindow.windowGamma p i K₂ s y = (s : ℂ) • (Ry * Ryᴴ) := by
    rw [windowGamma_eq, hp2]
  set c : ℂ := (((2 * (p.W : ℝ))⁻¹ : ℝ) : ℂ) with hc
  have key : (J * (Rx * Rxᴴ)).trace - (J * (Ry * Ryᴴ)).trace =
      ((Rx - Ry) * Rxᴴ * J).trace + (Ry * (Rx - Ry)ᴴ * J).trace := by
    rw [trace_mul_comm J (Rx * Rxᴴ), trace_mul_comm J (Ry * Ryᴴ), ← trace_sub, ← trace_add]
    congr 1
    rw [conjTranspose_sub]
    noncomm_ring
  have hdiff : pairCentre J K₁ s x - pairCentre J K₂ s y =
      c * (s : ℂ) * (((Rx - Ry) * Rxᴴ * J).trace + (Ry * (Rx - Ry)ᴴ * J).trace) := by
    unfold pairCentre
    rw [hgx, hgy, mul_smul_comm, mul_smul_comm, trace_smul, trace_smul, smul_eq_mul,
      smul_eq_mul, ← hc, mul_assoc, mul_assoc, ← mul_sub, ← mul_sub, key]
    simp only [Matrix.mul_assoc]
  have hJ' : ∀ v : PairSite p i → ℂ, sqNorm (Jᴴ *ᵥ v) ≤ 1 ^ 2 * sqNorm v := fun v =>
    sqNorm_mulVec_le_of_opNorm_le (by rw [Matrix.l2_opNorm_conjTranspose]; exact hJn) v
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * (p.W : ℝ) := by
    rw [BlockBand.Angular.FiberAngular.card_pairSite]; push_cast; ring
  have hW2 : (0 : ℝ) < 2 * (p.W : ℝ) := by have := p.W_pos; positivity
  have hsq : Real.sqrt (Fintype.card (PairSite p i) : ℝ) * Real.sqrt (Fintype.card (PairSite p i))
      = 2 * (p.W : ℝ) := by
    rw [Real.mul_self_sqrt (Nat.cast_nonneg _), hcard]
  have hnx : ‖Rx‖ ≤ (s * v₀)⁻¹ := opNorm_root_resolvent_le hK₁ hs (by simp) hv₀ hv₁
  have hny : ‖Ry‖ ≤ (s * v₀)⁻¹ := opNorm_root_resolvent_le hK₂ hs (by simp) hv₀ hv₂
  set Δ := |x - y| + ‖K₁ - K₂‖ with hΔ
  have hlip : ‖Rx - Ry‖ ≤ resLip s v₀ * Δ := by
    have h := resolvent_lipschitz_two hK₁ hK₂ hs (by simp) (by simp) hm₁ hm₂ hv₀ hv₁ hv₂
    rwa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  set q := Real.sqrt (Fintype.card (PairSite p i) : ℝ)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have ht1 : ‖((Rx - Ry) * Rxᴴ * J).trace‖ ≤ (q * ‖Rx - Ry‖) * (q * ‖Rx‖) :=
    (norm_trace_mul_mul_le hJ' _ _).trans
      (mul_le_mul (sqrt_frob_le _) (sqrt_frob_le _) (Real.sqrt_nonneg _) (by positivity))
  have ht2 : ‖(Ry * (Rx - Ry)ᴴ * J).trace‖ ≤ (q * ‖Ry‖) * (q * ‖Rx - Ry‖) :=
    (norm_trace_mul_mul_le hJ' _ _).trans
      (mul_le_mul (sqrt_frob_le _) (sqrt_frob_le _) (Real.sqrt_nonneg _) (by positivity))
  have hnc : ‖c * (s : ℂ)‖ = (2 * (p.W : ℝ))⁻¹ * s := by
    rw [norm_mul, hc, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hW2), abs_of_pos hs]
  have hL0 : 0 ≤ resLip s v₀ * Δ := (norm_nonneg _).trans hlip
  have hsum : ‖((Rx - Ry) * Rxᴴ * J).trace + (Ry * (Rx - Ry)ᴴ * J).trace‖ ≤
      2 * (p.W : ℝ) * (2 * ((resLip s v₀ * Δ) * (s * v₀)⁻¹)) := by
    refine (norm_add_le _ _).trans ?_
    have e1 : (q * ‖Rx - Ry‖) * (q * ‖Rx‖) = (q * q) * (‖Rx - Ry‖ * ‖Rx‖) := by ring
    have e2 : (q * ‖Ry‖) * (q * ‖Rx - Ry‖) = (q * q) * (‖Rx - Ry‖ * ‖Ry‖) := by ring
    rw [e1, hsq] at ht1
    rw [e2, hsq] at ht2
    have b1 : ‖Rx - Ry‖ * ‖Rx‖ ≤ (resLip s v₀ * Δ) * (s * v₀)⁻¹ :=
      mul_le_mul hlip hnx (norm_nonneg _) hL0
    have b2 : ‖Rx - Ry‖ * ‖Ry‖ ≤ (resLip s v₀ * Δ) * (s * v₀)⁻¹ :=
      mul_le_mul hlip hny (norm_nonneg _) hL0
    nlinarith [mul_le_mul_of_nonneg_left b1 hW2.le, mul_le_mul_of_nonneg_left b2 hW2.le]
  rw [hdiff, norm_mul, hnc]
  calc (2 * (p.W : ℝ))⁻¹ * s *
        ‖((Rx - Ry) * Rxᴴ * J).trace + (Ry * (Rx - Ry)ᴴ * J).trace‖
      ≤ (2 * (p.W : ℝ))⁻¹ * s * (2 * (p.W : ℝ) * (2 * ((resLip s v₀ * Δ) * (s * v₀)⁻¹))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * resLip s v₀ / v₀ * Δ := by
        have hWne : (p.W : ℝ) ≠ 0 := by have := p.W_pos; positivity
        field_simp

/-- **Stability of `j_B` in `(λ, K)`**: `pairCentre_sub_le` for the
real window centre `windowCenter p i J K s λ`. -/
theorem windowCenter_sub_le {K₁ K₂ J : PairMatrix p i} (hK₁ : K₁.IsHermitian)
    (hK₂ : K₂.IsHermitian) (hJn : ‖J‖ ≤ 1) {s v₀ : ℝ} (hs : 0 < s) (hv₀ : 0 < v₀) {x y : ℝ}
    {m₁ m₂ : ℂ} (hm₁ : IsDysonRoot K₁ s (x : ℂ) m₁) (hm₂ : IsDysonRoot K₂ s (y : ℂ) m₂)
    (hv₁ : v₀ ≤ m₁.im) (hv₂ : v₀ ≤ m₂.im) :
    |BlockBand.LocalWindow.windowCenter p i J K₁ s x -
        BlockBand.LocalWindow.windowCenter p i J K₂ s y| ≤
      2 * resLip s v₀ / v₀ * (|x - y| + ‖K₁ - K₂‖) := by
  rw [← re_pairCentre, ← re_pairCentre, ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans
    (pairCentre_sub_le hK₁ hK₂ hJn hs hv₀ hm₁ hm₂ hv₁ hv₂)

/-- `windowCenter_sub_le` from two root rectangles: `K₁` around `E₁` (radius `r₁`) and `K₂`
around `E₂` (radius `r₂`), both with `Im m ≥ v₀`, at `|x - E₁| ≤ r₁`, `|y - E₂| ≤ r₂`. -/
theorem windowCenter_sub_le_of_rootRectangle {K₁ K₂ J : PairMatrix p i} (hK₁ : K₁.IsHermitian)
    (hK₂ : K₂.IsHermitian) (hJn : ‖J‖ ≤ 1) {s v₀ E₁ E₂ r₁ r₂ : ℝ} (hs : 0 < s) (hv₀ : 0 < v₀)
    (hR₁ : PairRootRectangle K₁ s E₁ r₁ v₀) (hR₂ : PairRootRectangle K₂ s E₂ r₂ v₀) {x y : ℝ}
    (hx : |x - E₁| ≤ r₁) (hy : |y - E₂| ≤ r₂) :
    |BlockBand.LocalWindow.windowCenter p i J K₁ s x -
        BlockBand.LocalWindow.windowCenter p i J K₂ s y| ≤
      2 * resLip s v₀ / v₀ * (|x - y| + ‖K₁ - K₂‖) := by
  obtain ⟨m₁, hm₁, hv₁⟩ := hR₁ x hx 0 le_rfl zero_le_one
  obtain ⟨m₂, hm₂, hv₂⟩ := hR₂ y hy 0 le_rfl zero_le_one
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hm₁ hm₂
  exact windowCenter_sub_le hK₁ hK₂ hJn hs hv₀ hm₁ hm₂ hv₁ hv₂

end BlockBand.LocalWindow.ProofPartTwo
