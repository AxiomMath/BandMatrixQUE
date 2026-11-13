module

public import BlockBand.Native.CEH.Phase1.Resolvent

/-!
# CEH ETH: deterministic Ward and reduction inequalities

Core identity (`bw_normalizedTrace_imChain_eq`): with `Y = R₁ᴴ A R₂`,
`T = Im w₁ · Im w₂ · ⟨Y Yᴴ⟩` (Ward `Im R = Im w · R Rᴴ`), so `T` is real, has the sign of
`Im w₁ Im w₂`, and `|T| = η₁ η₂ ⟨Y Yᴴ⟩`.

## Main results

* Positivity: `T` is real, `Im w₁ Im w₂ · T ≥ 0`, and `T ≥ 0` when `Im w₁, Im w₂ > 0`.
* B1: `|⟨R₁² A R₂⟩| ≤ η₁⁻¹ η₂^{-1/2} ⟨|Im R₁|⟩^{1/2} |T|^{1/2}` and
  `|⟨R₁ A R₂²⟩| ≤ η₂⁻¹ η₁^{-1/2} ⟨|Im R₂|⟩^{1/2} |T|^{1/2}` (Cauchy–Schwarz plus Ward; this is
  exactly CEH's power `η₁⁻¹ η₂^{-1/2}`).
* B2: `|⟨R₁² R₂⟩| ≤ |⟨Im R₁⟩| / (η₁ η₂)` and
  `|⟨R₁² R₂⟩| ≤ η₁^{-3/2} η₂^{-1/2} |⟨Im R₁⟩|^{1/2} |⟨Im R₂⟩|^{1/2}`, and the index-swapped
  bounds for `⟨R₁ R₂²⟩`.
* B5: `⟨(Im R₁ A Im R₂ Aᴴ)²⟩` is real and nonnegative and
  `⟨(Im R₁ A Im R₂ Aᴴ)²⟩ ≤ N T²` (from `tr K² ≤ (tr K)²` for `K = Y Yᴴ ⪰ 0`, proved entrywise
  by Cauchy–Schwarz on the rows of `Y`; no sign condition is needed).
* B6: `|⟨Im R₁ A Im R₂ Aᴴ B⟩| ≤ c |T|` for every `B` commuting with `R₁` with
  `‖Bᴴ v‖ ≤ c ‖v‖` (or with `c = ‖B‖`); in particular `|⟨Im R₁ A Im R₂ Aᴴ R₁⟩| ≤ η₁⁻¹ |T|`
  (also for `R₁ᴴ`), and the index-2 analogue `|⟨Im R₂ Aᴴ Im R₁ A R₂⟩| ≤ η₂⁻¹ |T|` (also for
  `R₂ᴴ`, and in the equal middle form `⟨Im R₁ A Im R₂ R₂ Aᴴ⟩`). The index-2 form
  printed in CEH, `⟨Im G₂ A Im G₁ A* G₂⟩ ≤ η₂⁻¹ ⟨Im G₁ A Im G₂ A*⟩`, is false for general `A`
  (it holds with `A ↔ A*`, which is the statement proved here).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Matrix
open BlockBand.Native.CEH.Phase1
open BlockBand.External.CEH (normalizedTrace sourceVectorNorm)
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {N : ℕ}

/-!
## Generic trace facts
-/

/-- `⟨X Xᴴ⟩` is the real number `Re⟨X Xᴴ⟩`. -/
theorem bw_normalizedTrace_mul_conjTranspose_eq_ofReal (X : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (X * Xᴴ) = (((normalizedTrace (X * Xᴴ)).re : ℝ) : ℂ) := by
  rw [normalizedTrace_mul_conjTranspose_self, Complex.ofReal_re]

/-- `Re⟨Xᴴ X⟩ = Re⟨X Xᴴ⟩`. -/
theorem bw_re_normalizedTrace_conjTranspose_mul_self (X : Matrix (Fin N) (Fin N) ℂ) :
    (normalizedTrace (Xᴴ * X)).re = (normalizedTrace (X * Xᴴ)).re := by
  rw [normalizedTrace_mul_comm]

/-- Column bound in normalized form: if `‖C v‖ ≤ c ‖v‖`, then
`Re⟨(C X)ᴴ (C X)⟩ ≤ c² Re⟨Xᴴ X⟩`. -/
theorem bw_re_normalizedTrace_conjTranspose_mul_self_mul_le (C X : Matrix (Fin N) (Fin N) ℂ)
    {c : ℝ} (hC : ∀ v, sourceVectorNorm (C *ᵥ v) ≤ c * sourceVectorNorm v) :
    (normalizedTrace ((C * X)ᴴ * (C * X))).re ≤ c ^ 2 * (normalizedTrace (Xᴴ * X)).re := by
  rw [re_normalizedTrace, re_normalizedTrace]
  have h := re_trace_conjTranspose_mul_self_mul_le C X hC
  have hN : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  calc (N : ℝ)⁻¹ * (((C * X)ᴴ * (C * X)).trace).re
      ≤ (N : ℝ)⁻¹ * (c ^ 2 * ((Xᴴ * X).trace).re) := mul_le_mul_of_nonneg_left h hN
    _ = _ := by ring

/-- Schwarz with an operator bound: if `‖Bᴴ v‖ ≤ c ‖v‖` and `c ≥ 0`, then
`|⟨Y Yᴴ B⟩| ≤ c Re⟨Y Yᴴ⟩`. -/
theorem bw_norm_normalizedTrace_mul_conjTranspose_mul_le (Y B : Matrix (Fin N) (Fin N) ℂ)
    {c : ℝ} (hc : 0 ≤ c) (hB : ∀ v, sourceVectorNorm (Bᴴ *ᵥ v) ≤ c * sourceVectorNorm v) :
    ‖normalizedTrace (Y * Yᴴ * B)‖ ≤ c * (normalizedTrace (Y * Yᴴ)).re := by
  set s := (normalizedTrace (Y * Yᴴ)).re with hs
  have hs0 : 0 ≤ s := normalizedTrace_mul_conjTranspose_self_re_nonneg Y
  rw [Matrix.mul_assoc]
  refine (norm_normalizedTrace_mul_le Y (Yᴴ * B)).trans ?_
  have h2 : (normalizedTrace ((Yᴴ * B)ᴴ * (Yᴴ * B))).re ≤ c ^ 2 * s := by
    have e : (Yᴴ * B)ᴴ * (Yᴴ * B) = (Bᴴ * Y) * (Bᴴ * Y)ᴴ := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [e, ← bw_re_normalizedTrace_conjTranspose_mul_self]
    refine (bw_re_normalizedTrace_conjTranspose_mul_self_mul_le Bᴴ Y hB).trans (le_of_eq ?_)
    rw [bw_re_normalizedTrace_conjTranspose_mul_self]
  calc Real.sqrt s * Real.sqrt (normalizedTrace ((Yᴴ * B)ᴴ * (Yᴴ * B))).re
      ≤ Real.sqrt s * Real.sqrt (c ^ 2 * s) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
    _ = c * s := by
        rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc, ← mul_assoc, mul_comm (Real.sqrt s),
          mul_assoc, Real.mul_self_sqrt hs0]

/-- Entrywise Schwarz for a Gram matrix: `|(Y Yᴴ)_ij| ≤ ‖Y_j‖ ‖Y_i‖` (rows of `Y`). -/
theorem bw_norm_mul_conjTranspose_apply_le (Y : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    ‖(Y * Yᴴ) i j‖ ≤ sourceVectorNorm (Y j) * sourceVectorNorm (Y i) := by
  have e : (Y * Yᴴ) i j = star (Y j) ⬝ᵥ Y i := by
    simp [mul_apply, dotProduct, mul_comm]
  rw [e]
  exact norm_star_dotProduct_le _ _

/-- Trace reduction for `K = Y Yᴴ ⪰ 0`: `∑_ij |K_ij|² ≤ (∑_ij |Y_ij|²)²`, i.e.
`tr K² ≤ (tr K)²`. -/
theorem bw_sum_norm_sq_mul_conjTranspose_le (Y : Matrix (Fin N) (Fin N) ℂ) :
    ∑ i, ∑ j, ‖(Y * Yᴴ) i j‖ ^ 2 ≤ (∑ i, ∑ j, ‖Y i j‖ ^ 2) ^ 2 := by
  have hrow : ∀ i, sourceVectorNorm (Y i) ^ 2 = ∑ k, ‖Y i k‖ ^ 2 := fun i =>
    sourceVectorNorm_sq (Y i)
  calc ∑ i, ∑ j, ‖(Y * Yᴴ) i j‖ ^ 2
      ≤ ∑ i, ∑ j, sourceVectorNorm (Y i) ^ 2 * sourceVectorNorm (Y j) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        have h := pow_le_pow_left₀ (norm_nonneg _) (bw_norm_mul_conjTranspose_apply_le Y i j) 2
        rw [mul_pow, mul_comm] at h
        exact h
    _ = (∑ i, ∑ j, ‖Y i j‖ ^ 2) ^ 2 := by
        rw [sq, Finset.sum_mul_sum]
        simp only [hrow]

/-- Normalized trace reduction: `|⟨(Y Yᴴ)(Y Yᴴ)ᴴ⟩| ≤ N (Re⟨Y Yᴴ⟩)²`. -/
theorem bw_norm_normalizedTrace_gram_sq_le (Y : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace ((Y * Yᴴ) * (Y * Yᴴ)ᴴ)‖ ≤ (N : ℝ) * (normalizedTrace (Y * Yᴴ)).re ^ 2 := by
  rw [normalizedTrace_mul_conjTranspose_self (Y * Yᴴ), normalizedTrace_mul_conjTranspose_self Y,
    Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs]
  set S := ∑ i, ∑ j, ‖Y i j‖ ^ 2
  have hK := bw_sum_norm_sq_mul_conjTranspose_le Y
  have hK0 : 0 ≤ ∑ i, ∑ j, ‖(Y * Yᴴ) i j‖ ^ 2 := by positivity
  rw [abs_of_nonneg (by positivity)]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  · have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    calc (N : ℝ)⁻¹ * ∑ i, ∑ j, ‖(Y * Yᴴ) i j‖ ^ 2 ≤ (N : ℝ)⁻¹ * S ^ 2 :=
          mul_le_mul_of_nonneg_left hK (by positivity)
      _ = (N : ℝ) * ((N : ℝ)⁻¹ * S) ^ 2 := by field_simp

/-!
## Ward factorization of the imaginary chain
-/

/-- The imaginary chain `Im R₁ A Im R₂ Aᴴ` (CEH's `Im G₁ A Im G₂ A*`). -/
def bwImChain (A R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  External.CEH.imaginaryPart R₁ * A * External.CEH.imaginaryPart R₂ * Aᴴ

/-- The Ward mass of the chain: `Re⟨Y Yᴴ⟩` with `Y = R₁ᴴ A R₂`. -/
def bwChainMass (A R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (normalizedTrace ((R₁ᴴ * A * R₂) * (R₁ᴴ * A * R₂)ᴴ)).re

theorem bwChainMass_nonneg (A R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ bwChainMass A R₁ R₂ :=
  normalizedTrace_mul_conjTranspose_self_re_nonneg _

section Resolvents

variable {H : Matrix (Fin N) (Fin N) ℂ} {w₁ w₂ : ℂ}

/-- `Re⟨R Rᴴ⟩ = |⟨Im R⟩| / |Im w|`. -/
theorem bw_re_normalizedTrace_resolvent_mul_conjTranspose (hH : H.IsHermitian)
    {w : ℂ} (hw : w.im ≠ 0) :
    (normalizedTrace (Phase1.resolvent H w * (Phase1.resolvent H w)ᴴ)).re =
      ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w))‖ / |w.im| := by
  have h0 := re_normalizedTrace_imaginaryPart_resolvent_div_nonneg hH hw
  rw [normalizedTrace_resolvent_mul_conjTranspose hH hw, Complex.div_ofReal_re]
  rw [normalizedTrace_imaginaryPart, Complex.ofReal_re] at h0 ⊢
  rw [Complex.norm_real, Real.norm_eq_abs, ← abs_div, abs_of_nonneg h0]

/-- `Re⟨Rᴴ R⟩ = |⟨Im R⟩| / |Im w|`. -/
theorem bw_re_normalizedTrace_conjTranspose_mul_resolvent (hH : H.IsHermitian)
    {w : ℂ} (hw : w.im ≠ 0) :
    (normalizedTrace ((Phase1.resolvent H w)ᴴ * Phase1.resolvent H w)).re =
      ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w))‖ / |w.im| := by
  rw [bw_re_normalizedTrace_conjTranspose_mul_self,
    bw_re_normalizedTrace_resolvent_mul_conjTranspose hH hw]

/-- Ward factorization with a trailing factor `B` commuting with `R₁`:
`⟨Im R₁ A Im R₂ Aᴴ B⟩ = Im w₁ Im w₂ ⟨Y Yᴴ B⟩`, `Y = R₁ᴴ A R₂`. -/
theorem bw_normalizedTrace_imChain_mul_eq (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A B : Matrix (Fin N) (Fin N) ℂ)
    (hB : B * Phase1.resolvent H w₁ = Phase1.resolvent H w₁ * B) :
    normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) * B) =
      ((w₁.im * w₂.im : ℝ) : ℂ) * normalizedTrace
        (((Phase1.resolvent H w₁)ᴴ * A * Phase1.resolvent H w₂) *
          ((Phase1.resolvent H w₁)ᴴ * A * Phase1.resolvent H w₂)ᴴ * B) := by
  set R₁ := Phase1.resolvent H w₁
  set R₂ := Phase1.resolvent H w₂
  rw [bwImChain, imaginaryPart_resolvent hH hw₁, imaginaryPart_resolvent hH hw₂]
  simp only [smul_mul, Matrix.mul_smul, normalizedTrace_smul]
  have e : R₁ * R₁ᴴ * A * (R₂ * R₂ᴴ) * Aᴴ * B = R₁ * (R₁ᴴ * A * R₂ * R₂ᴴ * Aᴴ * B) := by
    simp only [Matrix.mul_assoc]
  have e' : R₁ᴴ * A * R₂ * R₂ᴴ * Aᴴ * B * R₁ = R₁ᴴ * A * R₂ * (R₁ᴴ * A * R₂)ᴴ * B := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, hB]
  rw [e, normalizedTrace_mul_comm, e']
  push_cast
  ring

/-- Ward factorization: `T = ⟨Im R₁ A Im R₂ Aᴴ⟩ = Im w₁ Im w₂ Re⟨Y Yᴴ⟩`, a real number. -/
theorem bw_normalizedTrace_imChain_eq (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂)) =
      ((w₁.im * w₂.im * bwChainMass A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) : ℝ) :
        ℂ) := by
  have h := bw_normalizedTrace_imChain_mul_eq hH hw₁ hw₂ A 1 (by simp)
  simp only [Matrix.mul_one] at h
  rw [h, bw_normalizedTrace_mul_conjTranspose_eq_ofReal, bwChainMass]
  push_cast
  ring

/-!
## Positivity of the imaginary chain
-/

/-- `T` is real. -/
theorem bw_im_normalizedTrace_imChain (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    (normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))).im = 0 := by
  rw [bw_normalizedTrace_imChain_eq hH hw₁ hw₂, Complex.ofReal_im]

/-- `T = Re T` as a complex number. -/
theorem bw_normalizedTrace_imChain_eq_re (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂)) =
      (((normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))).re :
        ℝ) : ℂ) := by
  rw [bw_normalizedTrace_imChain_eq hH hw₁ hw₂, Complex.ofReal_re]

/-- `T` has the sign of `Im w₁ Im w₂`: `Im w₁ Im w₂ · Re T ≥ 0`. -/
theorem bw_mul_re_normalizedTrace_imChain_nonneg (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    0 ≤ w₁.im * w₂.im *
      (normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))).re := by
  rw [bw_normalizedTrace_imChain_eq hH hw₁ hw₂, Complex.ofReal_re, ← mul_assoc]
  exact mul_nonneg (mul_self_nonneg _) (bwChainMass_nonneg _ _ _)

/-- For `Im w₁, Im w₂ > 0`, `Re T ≥ 0` (and `T = Re T` by `bw_normalizedTrace_imChain_eq_re`). -/
theorem bw_re_normalizedTrace_imChain_nonneg (hH : H.IsHermitian) (hw₁ : 0 < w₁.im)
    (hw₂ : 0 < w₂.im) (A : Matrix (Fin N) (Fin N) ℂ) :
    0 ≤ (normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))).re := by
  rw [bw_normalizedTrace_imChain_eq hH hw₁.ne' hw₂.ne', Complex.ofReal_re]
  exact mul_nonneg (mul_pos hw₁ hw₂).le (bwChainMass_nonneg _ _ _)

/-- For `Im w₁, Im w₂ > 0`, `|T| = Re T`. -/
theorem bw_norm_normalizedTrace_imChain_eq_re (hH : H.IsHermitian) (hw₁ : 0 < w₁.im)
    (hw₂ : 0 < w₂.im) (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ =
      (normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))).re := by
  rw [bw_normalizedTrace_imChain_eq_re hH hw₁.ne' hw₂.ne', Complex.norm_real, Complex.ofReal_re,
    Real.norm_eq_abs, abs_of_nonneg (bw_re_normalizedTrace_imChain_nonneg hH hw₁ hw₂ A)]

/-- `|T| = η₁ η₂ Re⟨Y Yᴴ⟩`. -/
theorem bw_norm_normalizedTrace_imChain (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ =
      |w₁.im| * |w₂.im| * bwChainMass A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) := by
  rw [bw_normalizedTrace_imChain_eq hH hw₁ hw₂, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_of_nonneg (bwChainMass_nonneg _ _ _)]

/-- `Re⟨Y Yᴴ⟩ = |T| / (η₁ η₂)`. -/
theorem bwChainMass_eq_norm_div (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    bwChainMass A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) =
      ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ /
        (|w₁.im| * |w₂.im|) := by
  have h1 : 0 < |w₁.im| := abs_pos.mpr hw₁
  have h2 : 0 < |w₂.im| := abs_pos.mpr hw₂
  rw [bw_norm_normalizedTrace_imChain hH hw₁ hw₂]
  field_simp

/-!
## B1: Schwarz bounds for `⟨R₁² A R₂⟩` and `⟨R₁ A R₂²⟩`
-/

/-- `√(a / e₁) √(t / (e₁ e₂)) = e₁⁻¹ √(e₂⁻¹) √a √t`. -/
theorem bw_sqrt_div_mul_sqrt_div {a t e₁ e₂ : ℝ} (h₁ : 0 < e₁) (h₂ : 0 < e₂) :
    Real.sqrt (a / e₁) * Real.sqrt (t / (e₁ * e₂)) =
      e₁⁻¹ * Real.sqrt e₂⁻¹ * Real.sqrt a * Real.sqrt t := by
  have hs₁ := Real.sqrt_pos.mpr h₁
  have hs₂ := Real.sqrt_pos.mpr h₂
  have hm := Real.sq_sqrt h₁.le
  rw [Real.sqrt_div' a h₁.le, Real.sqrt_div' t (mul_pos h₁ h₂).le, Real.sqrt_mul h₁.le,
    Real.sqrt_inv]
  field_simp
  rw [hm]
  ring

/-- `Re⟨(R₁ A R₂)ᴴ (R₁ A R₂)⟩ = Re⟨Y Yᴴ⟩`, `Y = R₁ᴴ A R₂` (normality of `R₁`). -/
theorem bw_re_normalizedTrace_conjTranspose_mul_self_chain (hH : H.IsHermitian)
    (hw₁ : w₁.im ≠ 0) (A R₂ : Matrix (Fin N) (Fin N) ℂ) :
    (normalizedTrace ((Phase1.resolvent H w₁ * A * R₂)ᴴ * (Phase1.resolvent H w₁ * A * R₂))).re =
      bwChainMass A (Phase1.resolvent H w₁) R₂ := by
  set R₁ := Phase1.resolvent H w₁
  have hc : R₁ * R₁ᴴ = R₁ᴴ * R₁ := resolvent_mul_conjTranspose_comm hH hw₁
  have e : (R₁ * A * R₂)ᴴ * (R₁ * A * R₂) = R₂ᴴ * Aᴴ * (R₁ᴴ * R₁) * A * R₂ := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  have e2 : (R₁ᴴ * A * R₂)ᴴ * (R₁ᴴ * A * R₂) = R₂ᴴ * Aᴴ * (R₁ * R₁ᴴ) * A * R₂ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, ← hc, ← e2, bw_re_normalizedTrace_conjTranspose_mul_self]
  rfl

/-- `Re⟨(R₁ A R₂)(R₁ A R₂)ᴴ⟩ = Re⟨Y Yᴴ⟩`, `Y = R₁ᴴ A R₂`. -/
theorem bw_re_normalizedTrace_mul_conjTranspose_self_chain (hH : H.IsHermitian)
    (hw₁ : w₁.im ≠ 0) (A R₂ : Matrix (Fin N) (Fin N) ℂ) :
    (normalizedTrace ((Phase1.resolvent H w₁ * A * R₂) * (Phase1.resolvent H w₁ * A * R₂)ᴴ)).re =
      bwChainMass A (Phase1.resolvent H w₁) R₂ := by
  rw [← bw_re_normalizedTrace_conjTranspose_mul_self,
    bw_re_normalizedTrace_conjTranspose_mul_self_chain hH hw₁]

/-- B1, Schwarz form: `|⟨R₁² A R₂⟩| ≤ √Re⟨R₁ R₁ᴴ⟩ · √Re⟨Y Yᴴ⟩`. Only `Im w₁ ≠ 0` is used. -/
theorem bw_norm_normalizedTrace_resolvent_sq_mul_le_sqrt (hH : H.IsHermitian)
    (hw₁ : w₁.im ≠ 0) (A R₂ : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace (Phase1.resolvent H w₁ * Phase1.resolvent H w₁ * A * R₂)‖ ≤
      Real.sqrt (normalizedTrace (Phase1.resolvent H w₁ * (Phase1.resolvent H w₁)ᴴ)).re *
        Real.sqrt (bwChainMass A (Phase1.resolvent H w₁) R₂) := by
  set R₁ := Phase1.resolvent H w₁
  have e : R₁ * R₁ * A * R₂ = R₁ * (R₁ * A * R₂) := by simp only [Matrix.mul_assoc]
  rw [e, ← bw_re_normalizedTrace_conjTranspose_mul_self_chain hH hw₁ A R₂]
  exact norm_normalizedTrace_mul_le _ _

/-- **B1** (CEH after (7.4)): `|⟨R₁² A R₂⟩| ≤ η₁⁻¹ η₂^{-1/2} |⟨Im R₁⟩|^{1/2} |T|^{1/2}`,
`T = ⟨Im R₁ A Im R₂ Aᴴ⟩`. -/
theorem bw_norm_normalizedTrace_resolvent_sq_mul_resolvent_le (hH : H.IsHermitian)
    (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace (Phase1.resolvent H w₁ * Phase1.resolvent H w₁ * A *
        Phase1.resolvent H w₂)‖ ≤
      |w₁.im|⁻¹ * Real.sqrt |w₂.im|⁻¹ *
        Real.sqrt ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁))‖ *
        Real.sqrt ‖normalizedTrace
          (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ := by
  refine (bw_norm_normalizedTrace_resolvent_sq_mul_le_sqrt hH hw₁ A _).trans (le_of_eq ?_)
  rw [bw_re_normalizedTrace_resolvent_mul_conjTranspose hH hw₁,
    bwChainMass_eq_norm_div hH hw₁ hw₂]
  exact bw_sqrt_div_mul_sqrt_div (abs_pos.mpr hw₁) (abs_pos.mpr hw₂)

/-- B1′, Schwarz form: `|⟨R₁ A R₂²⟩| ≤ √Re⟨Y Yᴴ⟩ · √Re⟨R₂ᴴ R₂⟩`. Only `Im w₁ ≠ 0` is used. -/
theorem bw_norm_normalizedTrace_mul_resolvent_sq_le_sqrt (hH : H.IsHermitian)
    (hw₁ : w₁.im ≠ 0) (A R₂ : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace (Phase1.resolvent H w₁ * A * R₂ * R₂)‖ ≤
      Real.sqrt (bwChainMass A (Phase1.resolvent H w₁) R₂) *
        Real.sqrt (normalizedTrace (R₂ᴴ * R₂)).re := by
  rw [← bw_re_normalizedTrace_mul_conjTranspose_self_chain hH hw₁ A R₂]
  exact norm_normalizedTrace_mul_le _ _

/-- **B1′**: `|⟨R₁ A R₂²⟩| ≤ η₂⁻¹ η₁^{-1/2} |⟨Im R₂⟩|^{1/2} |T|^{1/2}`. -/
theorem bw_norm_normalizedTrace_resolvent_mul_resolvent_sq_le (hH : H.IsHermitian)
    (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace (Phase1.resolvent H w₁ * A * Phase1.resolvent H w₂ *
        Phase1.resolvent H w₂)‖ ≤
      |w₂.im|⁻¹ * Real.sqrt |w₁.im|⁻¹ *
        Real.sqrt ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₂))‖ *
        Real.sqrt ‖normalizedTrace
          (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ := by
  refine (bw_norm_normalizedTrace_mul_resolvent_sq_le_sqrt hH hw₁ A _).trans (le_of_eq ?_)
  rw [bw_re_normalizedTrace_conjTranspose_mul_resolvent hH hw₂,
    bwChainMass_eq_norm_div hH hw₁ hw₂, mul_comm (Real.sqrt _), mul_comm |w₁.im|]
  exact bw_sqrt_div_mul_sqrt_div (abs_pos.mpr hw₂) (abs_pos.mpr hw₁)

/-!
## B2: the `A = 1` chain `⟨R₁² R₂⟩`
-/

/-- **B2a**: `|⟨R₁² R₂⟩| ≤ |⟨Im R₁⟩| / (η₁ η₂)`. -/
theorem bw_norm_normalizedTrace_resolvent_sq_mul_resolvent_le_div (hH : H.IsHermitian)
    (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0) :
    ‖normalizedTrace (Phase1.resolvent H w₁ * Phase1.resolvent H w₁ * Phase1.resolvent H w₂)‖ ≤
      ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁))‖ /
        (|w₁.im| * |w₂.im|) := by
  set R₁ := Phase1.resolvent H w₁
  set R₂ := Phase1.resolvent H w₂
  set a := ‖normalizedTrace (External.CEH.imaginaryPart R₁)‖
  have h₁ : 0 < |w₁.im| := abs_pos.mpr hw₁
  have h₂ : 0 < |w₂.im| := abs_pos.mpr hw₂
  have ha : 0 ≤ a / |w₁.im| := div_nonneg (norm_nonneg _) h₁.le
  have e : R₁ * R₁ * R₂ = R₁ * (R₂ * R₁) := by
    rw [Matrix.mul_assoc, resolvent_commute hH hw₁ hw₂]
  rw [e]
  refine (norm_normalizedTrace_mul_le _ _).trans ?_
  have hcol := bw_re_normalizedTrace_conjTranspose_mul_self_mul_le R₂ R₁
    (sourceVectorNorm_resolvent_mulVec_le hH hw₂)
  rw [bw_re_normalizedTrace_conjTranspose_mul_resolvent hH hw₁] at hcol
  rw [bw_re_normalizedTrace_resolvent_mul_conjTranspose hH hw₁]
  calc Real.sqrt (a / |w₁.im|) *
        Real.sqrt (normalizedTrace ((R₂ * R₁)ᴴ * (R₂ * R₁))).re
      ≤ Real.sqrt (a / |w₁.im|) * Real.sqrt (|w₂.im|⁻¹ ^ 2 * (a / |w₁.im|)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcol) (Real.sqrt_nonneg _)
    _ = a / (|w₁.im| * |w₂.im|) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr h₂.le), mul_left_comm,
          Real.mul_self_sqrt ha]
        field_simp

/-- **B2b**: `|⟨R₁² R₂⟩| ≤ η₁^{-3/2} η₂^{-1/2} |⟨Im R₁⟩|^{1/2} |⟨Im R₂⟩|^{1/2}`, written as
`η₁⁻¹ √(η₁⁻¹ η₂⁻¹) √|⟨Im R₁⟩| √|⟨Im R₂⟩|`. -/
theorem bw_norm_normalizedTrace_resolvent_sq_mul_resolvent_le_sqrt (hH : H.IsHermitian)
    (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0) :
    ‖normalizedTrace (Phase1.resolvent H w₁ * Phase1.resolvent H w₁ * Phase1.resolvent H w₂)‖ ≤
      |w₁.im|⁻¹ * Real.sqrt (|w₁.im|⁻¹ * |w₂.im|⁻¹) *
        Real.sqrt ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁))‖ *
        Real.sqrt ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₂))‖ := by
  set R₁ := Phase1.resolvent H w₁
  set R₂ := Phase1.resolvent H w₂
  set a₁ := ‖normalizedTrace (External.CEH.imaginaryPart R₁)‖
  set a₂ := ‖normalizedTrace (External.CEH.imaginaryPart R₂)‖
  have h₁ : 0 < |w₁.im| := abs_pos.mpr hw₁
  have h₂ : 0 < |w₂.im| := abs_pos.mpr hw₂
  have hB := bw_norm_normalizedTrace_resolvent_sq_mul_le_sqrt hH hw₁ 1 R₂
  rw [Matrix.mul_one, bw_re_normalizedTrace_resolvent_mul_conjTranspose hH hw₁] at hB
  have hm : bwChainMass 1 R₁ R₂ ≤ |w₁.im|⁻¹ ^ 2 * (a₂ / |w₂.im|) := by
    have hcol := bw_re_normalizedTrace_conjTranspose_mul_self_mul_le R₁ᴴ R₂
      (sourceVectorNorm_resolvent_conjTranspose_mulVec_le hH hw₁)
    rw [bw_re_normalizedTrace_conjTranspose_mul_resolvent hH hw₂,
      bw_re_normalizedTrace_conjTranspose_mul_self] at hcol
    rw [bwChainMass, Matrix.mul_one]
    exact hcol
  refine hB.trans ?_
  calc Real.sqrt (a₁ / |w₁.im|) * Real.sqrt (bwChainMass 1 R₁ R₂)
      ≤ Real.sqrt (a₁ / |w₁.im|) * Real.sqrt (|w₁.im|⁻¹ ^ 2 * (a₂ / |w₂.im|)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm) (Real.sqrt_nonneg _)
    _ = _ := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr h₁.le),
          Real.sqrt_div' _ h₁.le, Real.sqrt_div' _ h₂.le, Real.sqrt_mul (inv_nonneg.mpr h₁.le),
          Real.sqrt_inv, Real.sqrt_inv]
        have := Real.sqrt_pos.mpr h₁
        have := Real.sqrt_pos.mpr h₂
        field_simp

/-- **B2a**, index-swapped: `|⟨R₁ R₂²⟩| ≤ |⟨Im R₂⟩| / (η₁ η₂)`. -/
theorem bw_norm_normalizedTrace_resolvent_mul_resolvent_sq_le_div (hH : H.IsHermitian)
    (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0) :
    ‖normalizedTrace (Phase1.resolvent H w₁ * Phase1.resolvent H w₂ * Phase1.resolvent H w₂)‖ ≤
      ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₂))‖ /
        (|w₁.im| * |w₂.im|) := by
  rw [Matrix.mul_assoc, normalizedTrace_mul_comm, mul_comm |w₁.im|]
  exact bw_norm_normalizedTrace_resolvent_sq_mul_resolvent_le_div hH hw₂ hw₁

/-- **B2b**, index-swapped: `|⟨R₁ R₂²⟩| ≤ η₂⁻¹ √(η₂⁻¹ η₁⁻¹) √|⟨Im R₂⟩| √|⟨Im R₁⟩|`. -/
theorem bw_norm_normalizedTrace_resolvent_mul_resolvent_sq_le_sqrt (hH : H.IsHermitian)
    (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0) :
    ‖normalizedTrace (Phase1.resolvent H w₁ * Phase1.resolvent H w₂ * Phase1.resolvent H w₂)‖ ≤
      |w₂.im|⁻¹ * Real.sqrt (|w₂.im|⁻¹ * |w₁.im|⁻¹) *
        Real.sqrt ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₂))‖ *
        Real.sqrt ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁))‖ := by
  rw [Matrix.mul_assoc, normalizedTrace_mul_comm]
  exact bw_norm_normalizedTrace_resolvent_sq_mul_resolvent_le_sqrt hH hw₂ hw₁

/-!
## B5: the reduction inequality
-/

/-- `⟨(Im R₁ A Im R₂ Aᴴ)²⟩ = (Im w₁ Im w₂)² ⟨K Kᴴ⟩`, `K = Y Yᴴ`, `Y = R₁ᴴ A R₂`. -/
theorem bw_normalizedTrace_imChain_sq_eq (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) *
        bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂)) =
      (((w₁.im * w₂.im) ^ 2 : ℝ) : ℂ) * normalizedTrace
        (((Phase1.resolvent H w₁)ᴴ * A * Phase1.resolvent H w₂) *
            ((Phase1.resolvent H w₁)ᴴ * A * Phase1.resolvent H w₂)ᴴ *
          (((Phase1.resolvent H w₁)ᴴ * A * Phase1.resolvent H w₂) *
            ((Phase1.resolvent H w₁)ᴴ * A * Phase1.resolvent H w₂)ᴴ)ᴴ) := by
  set R₁ := Phase1.resolvent H w₁
  set R₂ := Phase1.resolvent H w₂
  rw [bwImChain, imaginaryPart_resolvent hH hw₁, imaginaryPart_resolvent hH hw₂]
  simp only [smul_mul, Matrix.mul_smul, normalizedTrace_smul]
  have e : R₁ * R₁ᴴ * A * (R₂ * R₂ᴴ) * Aᴴ * (R₁ * R₁ᴴ * A * (R₂ * R₂ᴴ) * Aᴴ) =
      R₁ * (R₁ᴴ * A * R₂ * R₂ᴴ * Aᴴ * R₁ * R₁ᴴ * A * R₂ * R₂ᴴ * Aᴴ) := by
    simp only [Matrix.mul_assoc]
  have e' : R₁ᴴ * A * R₂ * R₂ᴴ * Aᴴ * R₁ * R₁ᴴ * A * R₂ * R₂ᴴ * Aᴴ * R₁ =
      R₁ᴴ * A * R₂ * (R₁ᴴ * A * R₂)ᴴ * (R₁ᴴ * A * R₂ * (R₁ᴴ * A * R₂)ᴴ)ᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, normalizedTrace_mul_comm, e']
  push_cast
  ring

/-- `⟨(Im R₁ A Im R₂ Aᴴ)²⟩` is real. -/
theorem bw_normalizedTrace_imChain_sq_eq_re (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) *
        bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂)) =
      (((normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) *
        bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))).re : ℝ) : ℂ) := by
  rw [bw_normalizedTrace_imChain_sq_eq hH hw₁ hw₂, bw_normalizedTrace_mul_conjTranspose_eq_ofReal,
    ← Complex.ofReal_mul, Complex.ofReal_re]

/-- `⟨(Im R₁ A Im R₂ Aᴴ)²⟩ ≥ 0` (any signs of `Im w_i`). -/
theorem bw_re_normalizedTrace_imChain_sq_nonneg (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    0 ≤ (normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) *
        bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))).re := by
  rw [bw_normalizedTrace_imChain_sq_eq hH hw₁ hw₂, bw_normalizedTrace_mul_conjTranspose_eq_ofReal,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (sq_nonneg _) (normalizedTrace_mul_conjTranspose_self_re_nonneg _)

/-- **B5** (reduction inequality before CEH (7.8)):
`|⟨(Im R₁ A Im R₂ Aᴴ)²⟩| ≤ N |⟨Im R₁ A Im R₂ Aᴴ⟩|²`, for any signs of `Im w_i`. -/
theorem bw_norm_normalizedTrace_imChain_sq_le (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) *
        bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ ≤
      (N : ℝ) * ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁)
        (Phase1.resolvent H w₂))‖ ^ 2 := by
  rw [bw_normalizedTrace_imChain_sq_eq hH hw₁ hw₂, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), bw_norm_normalizedTrace_imChain hH hw₁ hw₂]
  have h := bw_norm_normalizedTrace_gram_sq_le
    ((Phase1.resolvent H w₁)ᴴ * A * Phase1.resolvent H w₂)
  rw [← bwChainMass] at h
  calc (w₁.im * w₂.im) ^ 2 * ‖normalizedTrace _‖
      ≤ (w₁.im * w₂.im) ^ 2 *
          ((N : ℝ) * bwChainMass A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) ^ 2) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = _ := by
        rw [mul_pow, ← sq_abs w₁.im, ← sq_abs w₂.im]
        ring

/-- **B5**, real form: `⟨(Im R₁ A Im R₂ Aᴴ)²⟩ ≤ N ⟨Im R₁ A Im R₂ Aᴴ⟩²` (both sides real). -/
theorem bw_re_normalizedTrace_imChain_sq_le (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    (normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) *
        bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))).re ≤
      (N : ℝ) * (normalizedTrace (bwImChain A (Phase1.resolvent H w₁)
        (Phase1.resolvent H w₂))).re ^ 2 := by
  have h := bw_norm_normalizedTrace_imChain_sq_le hH hw₁ hw₂ A
  rw [bw_normalizedTrace_imChain_eq_re hH hw₁ hw₂ A, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] at h
  exact (Complex.re_le_norm _).trans h

/-!
## B6: the sixth and seventh lines of CEH (7.2)
-/

/-- **B6**, general form: if `B` commutes with `R₁` and `‖Bᴴ v‖ ≤ c ‖v‖`, `c ≥ 0`, then
`|⟨Im R₁ A Im R₂ Aᴴ B⟩| ≤ c |⟨Im R₁ A Im R₂ Aᴴ⟩|`. -/
theorem bw_norm_normalizedTrace_imChain_mul_le (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A B : Matrix (Fin N) (Fin N) ℂ)
    (hB : B * Phase1.resolvent H w₁ = Phase1.resolvent H w₁ * B) {c : ℝ} (hc : 0 ≤ c)
    (hBv : ∀ v, sourceVectorNorm (Bᴴ *ᵥ v) ≤ c * sourceVectorNorm v) :
    ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) * B)‖ ≤
      c * ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ := by
  rw [bw_normalizedTrace_imChain_mul_eq hH hw₁ hw₂ A B hB, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, bw_norm_normalizedTrace_imChain hH hw₁ hw₂]
  have h := bw_norm_normalizedTrace_mul_conjTranspose_mul_le
    ((Phase1.resolvent H w₁)ᴴ * A * Phase1.resolvent H w₂) B hc hBv
  rw [← bwChainMass] at h
  calc |w₁.im| * |w₂.im| * ‖normalizedTrace _‖
      ≤ |w₁.im| * |w₂.im| *
          (c * bwChainMass A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- **B6**, operator-norm form: `|⟨Im R₁ A Im R₂ Aᴴ B⟩| ≤ ‖B‖ |⟨Im R₁ A Im R₂ Aᴴ⟩|` for `B`
commuting with `R₁` (`ℓ²` operator norm). -/
theorem bw_norm_normalizedTrace_imChain_mul_le_opNorm (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A B : Matrix (Fin N) (Fin N) ℂ)
    (hB : B * Phase1.resolvent H w₁ = Phase1.resolvent H w₁ * B) :
    ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) * B)‖ ≤
      ‖B‖ * ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ :=
  bw_norm_normalizedTrace_imChain_mul_le hH hw₁ hw₂ A B hB (norm_nonneg _) fun v => by
    simpa [Matrix.l2_opNorm_conjTranspose] using sourceVectorNorm_mulVec_le Bᴴ v

/-- **B6** (CEH (7.2), sixth line): `|⟨Im R₁ A Im R₂ Aᴴ R₁⟩| ≤ η₁⁻¹ |⟨Im R₁ A Im R₂ Aᴴ⟩|`. -/
theorem bw_norm_normalizedTrace_imChain_mul_resolvent_le (hH : H.IsHermitian)
    (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) *
        Phase1.resolvent H w₁)‖ ≤
      |w₁.im|⁻¹ *
        ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ :=
  bw_norm_normalizedTrace_imChain_mul_le hH hw₁ hw₂ A _ rfl (by positivity)
    (sourceVectorNorm_resolvent_conjTranspose_mulVec_le hH hw₁)

/-- **B6**, adjoint: `|⟨Im R₁ A Im R₂ Aᴴ R₁ᴴ⟩| ≤ η₁⁻¹ |⟨Im R₁ A Im R₂ Aᴴ⟩|`. -/
theorem bw_norm_normalizedTrace_imChain_mul_conjTranspose_resolvent_le (hH : H.IsHermitian)
    (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) *
        (Phase1.resolvent H w₁)ᴴ)‖ ≤
      |w₁.im|⁻¹ *
        ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ :=
  bw_norm_normalizedTrace_imChain_mul_le hH hw₁ hw₂ A _
    (resolvent_mul_conjTranspose_comm hH hw₁).symm (by positivity) fun v => by
      rw [conjTranspose_conjTranspose]
      exact sourceVectorNorm_resolvent_mulVec_le hH hw₁ v

/-- Index swap: `⟨Im R₂ Aᴴ Im R₁ A⟩ = ⟨Im R₁ A Im R₂ Aᴴ⟩` (cyclicity; any matrices). -/
theorem bw_normalizedTrace_bwImChain_swap (A R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (bwImChain Aᴴ R₂ R₁) = normalizedTrace (bwImChain A R₁ R₂) := by
  rw [bwImChain, bwImChain, conjTranspose_conjTranspose, Matrix.mul_assoc,
    normalizedTrace_mul_comm, ← Matrix.mul_assoc]

/-- **B6**, index 2 (CEH (7.2), seventh line, with `A ↔ Aᴴ`, see the module note):
`|⟨Im R₂ Aᴴ Im R₁ A R₂⟩| ≤ η₂⁻¹ |⟨Im R₁ A Im R₂ Aᴴ⟩|`. -/
theorem bw_norm_normalizedTrace_imChain_swap_mul_resolvent_le (hH : H.IsHermitian)
    (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₂) * Aᴴ *
        External.CEH.imaginaryPart (Phase1.resolvent H w₁) * A * Phase1.resolvent H w₂)‖ ≤
      |w₂.im|⁻¹ *
        ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ := by
  have h := bw_norm_normalizedTrace_imChain_mul_resolvent_le hH hw₂ hw₁ Aᴴ
  rw [bw_normalizedTrace_bwImChain_swap] at h
  simpa [bwImChain, conjTranspose_conjTranspose] using h

/-- **B6**, index 2, adjoint: `|⟨Im R₂ Aᴴ Im R₁ A R₂ᴴ⟩| ≤ η₂⁻¹ |⟨Im R₁ A Im R₂ Aᴴ⟩|`. -/
theorem bw_norm_normalizedTrace_imChain_swap_mul_conjTranspose_resolvent_le
    (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₂) * Aᴴ *
        External.CEH.imaginaryPart (Phase1.resolvent H w₁) * A * (Phase1.resolvent H w₂)ᴴ)‖ ≤
      |w₂.im|⁻¹ *
        ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ := by
  have h := bw_norm_normalizedTrace_imChain_mul_conjTranspose_resolvent_le hH hw₂ hw₁ Aᴴ
  rw [bw_normalizedTrace_bwImChain_swap] at h
  simpa [bwImChain, conjTranspose_conjTranspose] using h

/-- `Im R · R = R · Im R`. -/
theorem bw_imaginaryPart_resolvent_mul_comm (hH : H.IsHermitian) {w : ℂ} (hw : w.im ≠ 0) :
    External.CEH.imaginaryPart (Phase1.resolvent H w) * Phase1.resolvent H w =
      Phase1.resolvent H w * External.CEH.imaginaryPart (Phase1.resolvent H w) := by
  nth_rewrite 1 [imaginaryPart_resolvent hH hw]
  rw [imaginaryPart_resolvent' hH hw, smul_mul, Matrix.mul_smul]
  simp only [Matrix.mul_assoc]

/-- **B6**, index 2, middle form: `|⟨Im R₁ A Im R₂ R₂ Aᴴ⟩| ≤ η₂⁻¹ |⟨Im R₁ A Im R₂ Aᴴ⟩|`
(`⟨Im R₁ A Im R₂ R₂ Aᴴ⟩ = ⟨Im R₂ Aᴴ Im R₁ A R₂⟩`). -/
theorem bw_norm_normalizedTrace_imChain_mid_resolvent_le (hH : H.IsHermitian)
    (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁) * A *
        External.CEH.imaginaryPart (Phase1.resolvent H w₂) * Phase1.resolvent H w₂ * Aᴴ)‖ ≤
      |w₂.im|⁻¹ *
        ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ := by
  set I₁ := External.CEH.imaginaryPart (Phase1.resolvent H w₁)
  set I₂ := External.CEH.imaginaryPart (Phase1.resolvent H w₂)
  set R₂ := Phase1.resolvent H w₂
  have e : normalizedTrace (I₁ * A * I₂ * R₂ * Aᴴ) =
      normalizedTrace (I₂ * Aᴴ * I₁ * A * R₂) := by
    have e1 : I₁ * A * I₂ * R₂ * Aᴴ = (I₁ * A) * (I₂ * R₂ * Aᴴ) := by
      simp only [Matrix.mul_assoc]
    have e2 : I₂ * R₂ * Aᴴ * (I₁ * A) = R₂ * (I₂ * Aᴴ * I₁ * A) := by
      rw [bw_imaginaryPart_resolvent_mul_comm hH hw₂]
      simp only [Matrix.mul_assoc]
      rfl
    rw [e1, normalizedTrace_mul_comm, e2, normalizedTrace_mul_comm]
  rw [e]
  exact bw_norm_normalizedTrace_imChain_swap_mul_resolvent_le hH hw₁ hw₂ A

end Resolvents

end BlockBand.Native.CEH.ETH
