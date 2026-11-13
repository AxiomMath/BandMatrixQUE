module

public import BlockBand.Native.CEH.ETH.FlowItoZAlg
public import BlockBand.Native.CEH.ETH.BracketsFlow
public import BlockBand.Native.CEH.ETH.DeterministicTransfer

/-!
# CEH ETH: algebraic glue for the zig closure

Trace identities and bounds used to close the zig: the cross terms of the drift (7.2), the
conjugation and swap symmetries of `twoResApprox`, and the index-2 cyclic identity.

**The cross terms of (7.2).** `zgl_cross R₁ R₂ A` is the sum of the four
products of `fz_cehDrift` (CEH (7.2), lines 3–4):
`⟨R₂ᴴAᴴR₁⟩⟨I₁AI₂⟩ + ⟨R₁ᴴAR₂⟩⟨I₂AᴴI₁⟩ + ⟨I₁AR₂⟩⟨I₂AᴴR₁⟩ + ⟨R₂ᴴAᴴI₁⟩⟨R₁ᴴAI₂⟩`, `I_i = Im R_i`
(`zgl_fz_cehDrift_eq`). With the four constellation chains
`x₁₁ = ⟨R₁AR₂⟩, x₁₂ = ⟨R₁AR₂ᴴ⟩, x₂₁ = ⟨R₁ᴴAR₂⟩, x₂₂ = ⟨R₁ᴴAR₂ᴴ⟩`, every one of the eight
factors is a fixed linear combination of the `xₐᵦ` and their conjugates (`zgl_factor_*`; the
reversed chains are `⟨R₂^{(b)}AᴴR₁^{(a)}⟩ = conj x_{āb̄}`), and
* `zgl_cross_eq`: `zgl_cross = conj x₂₁ · T + x₂₁ · conj T + p · conj q + conj p · q` with
  `T = -¼(x₁₁ - x₁₂ - x₂₁ + x₂₂)`, `p = (2i)⁻¹(x₁₁ - x₂₁)`, `q = (2i)⁻¹(x₂₁ - x₂₂)`; hence
  `zgl_cross = 2 Re(conj x₂₁ T) + 2 Re(p conj q)` is real (`zgl_cross_eq_re`);
* `zgl_norm_cross_le`: `|zgl_cross| ≤ (|x₁₁| + |x₁₂| + |x₂₁| + |x₂₂|)²`;
* `zgl_norm_cross_le_split`: for any `μₐᵦ ∈ ℂ` (in the application `μₐᵦ = ⟨M^A_σ⟩` of the
  constellation `(a, b)`, `Xₐᵦ = xₐᵦ - μₐᵦ`),
  `|zgl_cross| ≤ 2 (∑ |xₐᵦ - μₐᵦ|)² + 2 (∑ |μₐᵦ|)²`, and
  `zgl_norm_cross_le_sum_sq`: `|zgl_cross| ≤ 4 ∑ (|xₐᵦ - μₐᵦ| + |μₐᵦ|)²`.

**Conjugate/flip identities for `twoResApprox`.**
`(M^A_σ(M₁, M₂))ᴴ = M^{Aᴴ}_σ(M₂ᴴ, M₁ᴴ)` (`zgl_twoResApprox_conjTranspose`), so
`⟨M^{Aᴴ}_σ(Y, X)⟩ = conj ⟨M^A_σ(Xᴴ, Yᴴ)⟩` and the reversed fluctuation is a conjugated `X`
(`zgl_reversed_sub_eq_conj`); `(M̂_σ(M₁, A, M₂))ᴴ = M̂_σ(M₂, Aᴴ, M₁)`; `⟨M^I_σ⟩` is symmetric;
regularity transfers (`⟨M₂AᴴM₁ᴴ⟩ = conj⟨M₁AM₂ᴴ⟩`); `P = Re⟨Im M₁ A Im M₂ Aᴴ⟩` is unchanged;
and `zgl_lemma56_window_bound_swap` is Lemma 5.6 (bounds 1–4 and `M̂`) for the swapped data
`(z₂, z₁, M₂, M₁, Aᴴ)`, with the same constant and the same `√P`.

**The index-2 cyclic bridge.** For `R₂ = (H - w₂)⁻¹` (`H` Hermitian, `Im w₂ ≠ 0`)
and arbitrary `X, A`: `⟨Im R₂ Aᴴ X A R₂⟩ = ⟨X A Im R₂ R₂ Aᴴ⟩ = ⟨X A R₂ Im R₂ Aᴴ⟩` and the same
with `R₂ᴴ` (`zgl_bridge_index2`, `zgl_bridge_index2_conjTranspose`, `zgl_bridge_fz`); and
`zgl_norm_index_terms_le`: the four `a`-terms of (7.2) are bounded by
`2 (|a₁|/η₁ + |a₂|/η₂) |T|`, `T = ⟨Im R₁ A Im R₂ Aᴴ⟩`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Matrix
open BlockBand.External.CEH (normalizedTrace)
open scoped ComplexConjugate

variable {N : ℕ}

/-!
## Generic trace facts
-/

/-- `⟨Zᴴ Yᴴ Xᴴ⟩ = conj ⟨X Y Z⟩`. -/
theorem zgl_normalizedTrace_rev₃ (X Y Z : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (Zᴴ * Yᴴ * Xᴴ) = conj (normalizedTrace (X * Y * Z)) := by
  rw [← Phase1.normalizedTrace_conjTranspose, conjTranspose_mul, conjTranspose_mul,
    Matrix.mul_assoc]

theorem zgl_norm_two_I_inv : ‖(2 * Complex.I)⁻¹‖ = 1 / 2 := by
  rw [norm_inv, norm_mul, Complex.norm_I]
  norm_num

/-!
## The cross terms of (7.2)
-/

/-- The four cross products of CEH (7.2) (lines 3–4 of `fz_cehDrift`). -/
def zgl_cross (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  normalizedTrace (R₂ᴴ * Aᴴ * R₁) * normalizedTrace (External.CEH.imaginaryPart R₁ * A *
      External.CEH.imaginaryPart R₂) +
    normalizedTrace (R₁ᴴ * A * R₂) * normalizedTrace (External.CEH.imaginaryPart R₂ * Aᴴ *
      External.CEH.imaginaryPart R₁) +
    normalizedTrace (External.CEH.imaginaryPart R₁ * A * R₂) *
      normalizedTrace (External.CEH.imaginaryPart R₂ * Aᴴ * R₁) +
    normalizedTrace (R₂ᴴ * Aᴴ * External.CEH.imaginaryPart R₁) *
      normalizedTrace (R₁ᴴ * A * External.CEH.imaginaryPart R₂)

/-- The CEH (7.2) drift is `coefficient · ⟨Im R₁ A Im R₂ Aᴴ⟩ + zgl_cross + (four a-terms)`. -/
theorem zgl_fz_cehDrift_eq (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) (m₁ m₂ w₁ w₂ : ℂ) :
    fz_cehDrift R₁ R₂ A m₁ m₂ w₁ w₂ =
      (((normalizedTrace R₁ - m₁).im / w₁.im + (normalizedTrace R₂ - m₂).im / w₂.im : ℝ) : ℂ) *
          fz_chain R₁ R₂ A + zgl_cross R₁ R₂ A +
        ((normalizedTrace R₁ - m₁) * normalizedTrace (External.CEH.imaginaryPart R₁ * A *
            External.CEH.imaginaryPart R₂ * Aᴴ * R₁) +
          (normalizedTrace R₂ - m₂) * normalizedTrace (External.CEH.imaginaryPart R₂ * Aᴴ *
            External.CEH.imaginaryPart R₁ * A * R₂) +
          conj (normalizedTrace R₁ - m₁) * normalizedTrace (External.CEH.imaginaryPart R₁ * A *
            External.CEH.imaginaryPart R₂ * Aᴴ * R₁ᴴ) +
          conj (normalizedTrace R₂ - m₂) * normalizedTrace (External.CEH.imaginaryPart R₂ * Aᴴ *
            External.CEH.imaginaryPart R₁ * A * R₂ᴴ)) := by
  unfold fz_cehDrift zgl_cross
  ring

section Factors

variable (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ)

/-- Factor 1: `⟨R₂ᴴAᴴR₁⟩ = conj x₂₁`. -/
theorem zgl_factor_rev_conj : normalizedTrace (R₂ᴴ * Aᴴ * R₁) =
    conj (normalizedTrace (R₁ᴴ * A * R₂)) := by
  rw [← zgl_normalizedTrace_rev₃, conjTranspose_conjTranspose]

/-- Factor 2: `⟨I₁AI₂⟩ = -¼(x₁₁ - x₁₂ - x₂₁ + x₂₂)`. -/
theorem zgl_factor_imIm : normalizedTrace (External.CEH.imaginaryPart R₁ * A *
    External.CEH.imaginaryPart R₂) = -(1 / 4 : ℂ) * (normalizedTrace (R₁ * A * R₂) -
      normalizedTrace (R₁ * A * R₂ᴴ) - normalizedTrace (R₁ᴴ * A * R₂) +
      normalizedTrace (R₁ᴴ * A * R₂ᴴ)) := by
  rw [← fz_two_I_inv_sq]
  simp only [External.CEH.imaginaryPart, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_assoc, Phase1.normalizedTrace_sub, Phase1.normalizedTrace_smul]
  ring

/-- Factor 4: `⟨I₂AᴴI₁⟩ = conj ⟨I₁AI₂⟩`. -/
theorem zgl_factor_imIm_rev : normalizedTrace (External.CEH.imaginaryPart R₂ * Aᴴ *
    External.CEH.imaginaryPart R₁) = conj (normalizedTrace (External.CEH.imaginaryPart R₁ * A *
      External.CEH.imaginaryPart R₂)) := by
  rw [← zgl_normalizedTrace_rev₃, bf_conjTranspose_imaginaryPart,
    bf_conjTranspose_imaginaryPart]

/-- Factor 5: `⟨I₁AR₂⟩ = (2i)⁻¹(x₁₁ - x₂₁)`. -/
theorem zgl_factor_imR : normalizedTrace (External.CEH.imaginaryPart R₁ * A * R₂) =
    (2 * Complex.I)⁻¹ * (normalizedTrace (R₁ * A * R₂) - normalizedTrace (R₁ᴴ * A * R₂)) := by
  simp only [External.CEH.imaginaryPart, Matrix.smul_mul, Matrix.sub_mul,
    Phase1.normalizedTrace_sub, Phase1.normalizedTrace_smul]

/-- Factor 8: `⟨R₁ᴴAI₂⟩ = (2i)⁻¹(x₂₁ - x₂₂)`. -/
theorem zgl_factor_RIm : normalizedTrace (R₁ᴴ * A * External.CEH.imaginaryPart R₂) =
    (2 * Complex.I)⁻¹ * (normalizedTrace (R₁ᴴ * A * R₂) - normalizedTrace (R₁ᴴ * A * R₂ᴴ)) := by
  simp only [External.CEH.imaginaryPart, Matrix.mul_smul, Matrix.mul_sub,
    Phase1.normalizedTrace_sub, Phase1.normalizedTrace_smul]

/-- Factor 6: `⟨I₂AᴴR₁⟩ = conj((2i)⁻¹(x₂₁ - x₂₂))`. -/
theorem zgl_factor_imR_rev : normalizedTrace (External.CEH.imaginaryPart R₂ * Aᴴ * R₁) =
    conj ((2 * Complex.I)⁻¹ * (normalizedTrace (R₁ᴴ * A * R₂) -
      normalizedTrace (R₁ᴴ * A * R₂ᴴ))) := by
  rw [← zgl_factor_RIm, ← zgl_normalizedTrace_rev₃, conjTranspose_conjTranspose,
    bf_conjTranspose_imaginaryPart]

/-- Factor 7: `⟨R₂ᴴAᴴI₁⟩ = conj((2i)⁻¹(x₁₁ - x₂₁))`. -/
theorem zgl_factor_RIm_rev : normalizedTrace (R₂ᴴ * Aᴴ * External.CEH.imaginaryPart R₁) =
    conj ((2 * Complex.I)⁻¹ * (normalizedTrace (R₁ * A * R₂) -
      normalizedTrace (R₁ᴴ * A * R₂))) := by
  rw [← zgl_factor_imR, ← zgl_normalizedTrace_rev₃, bf_conjTranspose_imaginaryPart]

/-- **Cross terms, polarized form**: `zgl_cross = conj x₂₁ T + x₂₁ conj T + p conj q + conj p q`. -/
theorem zgl_cross_eq : zgl_cross R₁ R₂ A =
    conj (normalizedTrace (R₁ᴴ * A * R₂)) * (-(1 / 4 : ℂ) * (normalizedTrace (R₁ * A * R₂) -
        normalizedTrace (R₁ * A * R₂ᴴ) - normalizedTrace (R₁ᴴ * A * R₂) +
        normalizedTrace (R₁ᴴ * A * R₂ᴴ))) +
      normalizedTrace (R₁ᴴ * A * R₂) * conj (-(1 / 4 : ℂ) * (normalizedTrace (R₁ * A * R₂) -
        normalizedTrace (R₁ * A * R₂ᴴ) - normalizedTrace (R₁ᴴ * A * R₂) +
        normalizedTrace (R₁ᴴ * A * R₂ᴴ))) +
      (2 * Complex.I)⁻¹ * (normalizedTrace (R₁ * A * R₂) - normalizedTrace (R₁ᴴ * A * R₂)) *
        conj ((2 * Complex.I)⁻¹ * (normalizedTrace (R₁ᴴ * A * R₂) -
          normalizedTrace (R₁ᴴ * A * R₂ᴴ))) +
      conj ((2 * Complex.I)⁻¹ * (normalizedTrace (R₁ * A * R₂) -
          normalizedTrace (R₁ᴴ * A * R₂))) *
        ((2 * Complex.I)⁻¹ * (normalizedTrace (R₁ᴴ * A * R₂) -
          normalizedTrace (R₁ᴴ * A * R₂ᴴ))) := by
  rw [zgl_cross, zgl_factor_imIm_rev, zgl_factor_rev_conj, zgl_factor_imIm, zgl_factor_imR,
    zgl_factor_imR_rev, zgl_factor_RIm_rev, zgl_factor_RIm]

end Factors

/-- `conj u · v + u · conj v = 2 Re(conj u · v)`. -/
theorem zgl_conj_mul_add (u v : ℂ) : conj u * v + u * conj v = ((2 * (conj u * v).re : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

/-- **Cross terms, real form**: `zgl_cross = 2 Re(conj x₂₁ · T) + 2 Re(p · conj q)` (a real
number). -/
theorem zgl_cross_eq_re (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) : zgl_cross R₁ R₂ A =
    ((2 * (conj (normalizedTrace (R₁ᴴ * A * R₂)) * (-(1 / 4 : ℂ) *
        (normalizedTrace (R₁ * A * R₂) - normalizedTrace (R₁ * A * R₂ᴴ) -
          normalizedTrace (R₁ᴴ * A * R₂) + normalizedTrace (R₁ᴴ * A * R₂ᴴ)))).re +
      2 * ((2 * Complex.I)⁻¹ * (normalizedTrace (R₁ * A * R₂) - normalizedTrace (R₁ᴴ * A * R₂)) *
        conj ((2 * Complex.I)⁻¹ * (normalizedTrace (R₁ᴴ * A * R₂) -
          normalizedTrace (R₁ᴴ * A * R₂ᴴ)))).re : ℝ) : ℂ) := by
  rw [zgl_cross_eq, add_assoc (_ + _), zgl_conj_mul_add]
  set p := (2 * Complex.I)⁻¹ * (normalizedTrace (R₁ * A * R₂) - normalizedTrace (R₁ᴴ * A * R₂))
  set q := (2 * Complex.I)⁻¹ * (normalizedTrace (R₁ᴴ * A * R₂) - normalizedTrace (R₁ᴴ * A * R₂ᴴ))
  have h : p * conj q + conj p * q = ((2 * (p * conj q).re : ℝ) : ℂ) := by
    have := zgl_conj_mul_add q p
    rw [show conj q * p = p * conj q by ring] at this
    rw [← this]; ring
  rw [h]
  push_cast
  ring

/-- Scalar core of the cross bound. -/
theorem zgl_cross_scalar_le {x₁₁ x₁₂ x₂₁ x₂₂ : ℂ} :
    ‖conj x₂₁ * (-(1 / 4 : ℂ) * (x₁₁ - x₁₂ - x₂₁ + x₂₂)) +
        x₂₁ * conj (-(1 / 4 : ℂ) * (x₁₁ - x₁₂ - x₂₁ + x₂₂)) +
        (2 * Complex.I)⁻¹ * (x₁₁ - x₂₁) * conj ((2 * Complex.I)⁻¹ * (x₂₁ - x₂₂)) +
        conj ((2 * Complex.I)⁻¹ * (x₁₁ - x₂₁)) * ((2 * Complex.I)⁻¹ * (x₂₁ - x₂₂))‖ ≤
      (‖x₁₁‖ + ‖x₁₂‖ + ‖x₂₁‖ + ‖x₂₂‖) ^ 2 := by
  set S := ‖x₁₁‖ + ‖x₁₂‖ + ‖x₂₁‖ + ‖x₂₂‖ with hS
  have n1 := norm_nonneg x₁₁
  have n2 := norm_nonneg x₁₂
  have n3 := norm_nonneg x₂₁
  have n4 := norm_nonneg x₂₂
  have hT : ‖-(1 / 4 : ℂ) * (x₁₁ - x₁₂ - x₂₁ + x₂₂)‖ ≤ S / 4 := by
    rw [norm_mul, norm_neg, norm_div, norm_one, Complex.norm_ofNat]
    have : ‖x₁₁ - x₁₂ - x₂₁ + x₂₂‖ ≤ S := by
      refine (norm_add_le _ _).trans ?_
      have h1 := norm_sub_le (x₁₁ - x₁₂) x₂₁
      have h2 := norm_sub_le x₁₁ x₁₂
      linarith
    linarith
  have hp : ‖(2 * Complex.I)⁻¹ * (x₁₁ - x₂₁)‖ ≤ (‖x₁₁‖ + ‖x₂₁‖) / 2 := by
    rw [norm_mul, zgl_norm_two_I_inv]
    have := norm_sub_le x₁₁ x₂₁
    linarith
  have hq : ‖(2 * Complex.I)⁻¹ * (x₂₁ - x₂₂)‖ ≤ (‖x₂₁‖ + ‖x₂₂‖) / 2 := by
    rw [norm_mul, zgl_norm_two_I_inv]
    have := norm_sub_le x₂₁ x₂₂
    linarith
  set T := -(1 / 4 : ℂ) * (x₁₁ - x₁₂ - x₂₁ + x₂₂)
  set p := (2 * Complex.I)⁻¹ * (x₁₁ - x₂₁)
  set q := (2 * Complex.I)⁻¹ * (x₂₁ - x₂₂)
  have hsum : ‖conj x₂₁ * T + x₂₁ * conj T + p * conj q + conj p * q‖ ≤
      2 * (‖x₂₁‖ * ‖T‖) + 2 * (‖p‖ * ‖q‖) := by
    refine norm_add₄_le.trans (le_of_eq ?_)
    simp only [norm_mul, Complex.norm_conj]
    ring
  refine hsum.trans ?_
  have hTn := norm_nonneg T
  have hpn := norm_nonneg p
  have hqn := norm_nonneg q
  have e1 : ‖x₂₁‖ * ‖T‖ ≤ S * (S / 4) := mul_le_mul (by linarith) hT hTn (by positivity)
  have e2 : ‖p‖ * ‖q‖ ≤ (‖x₁₁‖ + ‖x₂₁‖) / 2 * ((‖x₂₁‖ + ‖x₂₂‖) / 2) :=
    mul_le_mul hp hq hqn (by positivity)
  have e3 : (‖x₁₁‖ + ‖x₂₁‖) / 2 * ((‖x₂₁‖ + ‖x₂₂‖) / 2) ≤ S / 2 * (S / 2) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  nlinarith

/-- **Cross terms, bound**: `|zgl_cross| ≤ (|x₁₁| + |x₁₂| + |x₂₁| + |x₂₂|)²`. -/
theorem zgl_norm_cross_le (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) :
    ‖zgl_cross R₁ R₂ A‖ ≤ (‖normalizedTrace (R₁ * A * R₂)‖ + ‖normalizedTrace (R₁ * A * R₂ᴴ)‖ +
      ‖normalizedTrace (R₁ᴴ * A * R₂)‖ + ‖normalizedTrace (R₁ᴴ * A * R₂ᴴ)‖) ^ 2 := by
  rw [zgl_cross_eq]
  exact zgl_cross_scalar_le

/-- `(a+b+c+d)² ≤ 4(a²+b²+c²+d²)`. -/
theorem zgl_sq_sum_four_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

/-- **Cross terms, split bound**: for any `μₐᵦ`, `|zgl_cross| ≤ 2(∑|xₐᵦ - μₐᵦ|)² + 2(∑|μₐᵦ|)²`. -/
theorem zgl_norm_cross_le_split (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) (μ₁₁ μ₁₂ μ₂₁ μ₂₂ : ℂ) :
    ‖zgl_cross R₁ R₂ A‖ ≤
      2 * (‖normalizedTrace (R₁ * A * R₂) - μ₁₁‖ + ‖normalizedTrace (R₁ * A * R₂ᴴ) - μ₁₂‖ +
        ‖normalizedTrace (R₁ᴴ * A * R₂) - μ₂₁‖ + ‖normalizedTrace (R₁ᴴ * A * R₂ᴴ) - μ₂₂‖) ^ 2 +
      2 * (‖μ₁₁‖ + ‖μ₁₂‖ + ‖μ₂₁‖ + ‖μ₂₂‖) ^ 2 := by
  refine (zgl_norm_cross_le R₁ R₂ A).trans ?_
  set D := ‖normalizedTrace (R₁ * A * R₂) - μ₁₁‖ + ‖normalizedTrace (R₁ * A * R₂ᴴ) - μ₁₂‖ +
    ‖normalizedTrace (R₁ᴴ * A * R₂) - μ₂₁‖ + ‖normalizedTrace (R₁ᴴ * A * R₂ᴴ) - μ₂₂‖
  set U := ‖μ₁₁‖ + ‖μ₁₂‖ + ‖μ₂₁‖ + ‖μ₂₂‖
  have h (x μ : ℂ) : ‖x‖ ≤ ‖x - μ‖ + ‖μ‖ := by
    simpa using norm_add_le (x - μ) μ
  have hS : ‖normalizedTrace (R₁ * A * R₂)‖ + ‖normalizedTrace (R₁ * A * R₂ᴴ)‖ +
      ‖normalizedTrace (R₁ᴴ * A * R₂)‖ + ‖normalizedTrace (R₁ᴴ * A * R₂ᴴ)‖ ≤ D + U := by
    linarith [h (normalizedTrace (R₁ * A * R₂)) μ₁₁, h (normalizedTrace (R₁ * A * R₂ᴴ)) μ₁₂,
      h (normalizedTrace (R₁ᴴ * A * R₂)) μ₂₁, h (normalizedTrace (R₁ᴴ * A * R₂ᴴ)) μ₂₂]
  have h0 : 0 ≤ ‖normalizedTrace (R₁ * A * R₂)‖ + ‖normalizedTrace (R₁ * A * R₂ᴴ)‖ +
      ‖normalizedTrace (R₁ᴴ * A * R₂)‖ + ‖normalizedTrace (R₁ᴴ * A * R₂ᴴ)‖ := by positivity
  nlinarith [pow_le_pow_left₀ h0 hS 2, sq_nonneg (D - U)]

/-- **Cross terms, sum-of-squares form**: `|zgl_cross| ≤ 4 ∑ₐᵦ (|xₐᵦ - μₐᵦ| + |μₐᵦ|)²`. -/
theorem zgl_norm_cross_le_sum_sq (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) (μ₁₁ μ₁₂ μ₂₁ μ₂₂ : ℂ) :
    ‖zgl_cross R₁ R₂ A‖ ≤
      4 * ((‖normalizedTrace (R₁ * A * R₂) - μ₁₁‖ + ‖μ₁₁‖) ^ 2 +
        (‖normalizedTrace (R₁ * A * R₂ᴴ) - μ₁₂‖ + ‖μ₁₂‖) ^ 2 +
        (‖normalizedTrace (R₁ᴴ * A * R₂) - μ₂₁‖ + ‖μ₂₁‖) ^ 2 +
        (‖normalizedTrace (R₁ᴴ * A * R₂ᴴ) - μ₂₂‖ + ‖μ₂₂‖) ^ 2) := by
  refine (zgl_norm_cross_le R₁ R₂ A).trans ?_
  have h (x μ : ℂ) : ‖x‖ ≤ ‖x - μ‖ + ‖μ‖ := by
    simpa using norm_add_le (x - μ) μ
  have h0 : 0 ≤ ‖normalizedTrace (R₁ * A * R₂)‖ + ‖normalizedTrace (R₁ * A * R₂ᴴ)‖ +
      ‖normalizedTrace (R₁ᴴ * A * R₂)‖ + ‖normalizedTrace (R₁ᴴ * A * R₂ᴴ)‖ := by positivity
  refine (pow_le_pow_left₀ h0 (add_le_add (add_le_add (add_le_add
    (h (normalizedTrace (R₁ * A * R₂)) μ₁₁) (h (normalizedTrace (R₁ * A * R₂ᴴ)) μ₁₂))
    (h (normalizedTrace (R₁ᴴ * A * R₂)) μ₂₁)) (h (normalizedTrace (R₁ᴴ * A * R₂ᴴ)) μ₂₂))
    2).trans ?_
  exact zgl_sq_sum_four_le _ _ _ _

/-!
## Conjugate/flip identities for `twoResApprox`
-/

section Approx

open CEHNative.BlockBand CEHNative.BlockBand.External.CEH

theorem zgl_NTrace_conjTranspose (X : Matrix (Fin N) (Fin N) ℂ) :
    NTrace Xᴴ = conj (NTrace X) :=
  Phase1.normalizedTrace_conjTranspose X

/-- `⟨Zᴴ Yᴴ Xᴴ⟩ = conj ⟨X Y Z⟩` (trace). -/
theorem zgl_NTrace_rev₃ (X Y Z : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (Zᴴ * Yᴴ * Xᴴ) = conj (NTrace (X * Y * Z)) :=
  zgl_normalizedTrace_rev₃ X Y Z

theorem zgl_NTrace_rev₂ (X Y : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (Yᴴ * Xᴴ) = conj (NTrace (X * Y)) := by
  rw [← conjTranspose_mul]
  exact zgl_NTrace_conjTranspose _

/-- The denominator under adjoint and swap: `1 - σ⟨M₂ᴴM₁ᴴ⟩ = conj(1 - σ⟨M₁M₂⟩)`. -/
theorem zgl_hybridDen_conjTranspose (σ : ℝ) (M₁ M₂ : Matrix (Fin N) (Fin N) ℂ) :
    hybridDen σ M₂ᴴ M₁ᴴ = conj (hybridDen σ M₁ M₂) := by
  rw [hybridDen, hybridDen, zgl_NTrace_rev₂, map_sub, map_one, map_mul, Complex.conj_ofReal]

/-- **Adjoint of `M^A_σ`**: `(M^A_σ(M₁, M₂))ᴴ = M^{Aᴴ}_σ(M₂ᴴ, M₁ᴴ)` (no hypothesis). -/
theorem zgl_twoResApprox_conjTranspose (σ : ℝ) (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    (twoResApprox σ M₁ A M₂)ᴴ = twoResApprox σ M₂ᴴ Aᴴ M₁ᴴ := by
  rw [twoResApprox, twoResApprox, conjTranspose_add, conjTranspose_smul,
    zgl_hybridDen_conjTranspose, zgl_NTrace_rev₃, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_mul, Complex.star_def, map_mul, map_div₀, Complex.conj_ofReal]
  simp only [Matrix.mul_assoc]

/-- **Trace of the adjoint**: `⟨M^{Aᴴ}_σ(M₂ᴴ, M₁ᴴ)⟩ = conj ⟨M^A_σ(M₁, M₂)⟩`. -/
theorem zgl_NTrace_twoResApprox_conjTranspose (σ : ℝ) (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (twoResApprox σ M₂ᴴ Aᴴ M₁ᴴ) = conj (NTrace (twoResApprox σ M₁ A M₂)) := by
  rw [← zgl_twoResApprox_conjTranspose, zgl_NTrace_conjTranspose]

/-- **Trace of the adjoint, swapped order**: `⟨M^{Aᴴ}_σ(Y, X)⟩ = conj ⟨M^A_σ(Xᴴ, Yᴴ)⟩` (any `X`,
`Y`; e.g.
`Y = M₂^{(b)}`, `X = M₁^{(a)}`). -/
theorem zgl_NTrace_twoResApprox_swap (σ : ℝ) (X A Y : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (twoResApprox σ Y Aᴴ X) = conj (NTrace (twoResApprox σ Xᴴ A Yᴴ)) := by
  have h := zgl_NTrace_twoResApprox_conjTranspose σ Xᴴ A Yᴴ
  rwa [conjTranspose_conjTranspose, conjTranspose_conjTranspose] at h

/-- **The reversed fluctuation is a conjugated `X`**: for any matrices,
`⟨P₂ Aᴴ P₁⟩ - ⟨M^{Aᴴ}_σ(Q₂, Q₁)⟩ = conj(⟨P₁ᴴ A P₂ᴴ⟩ - ⟨M^A_σ(Q₁ᴴ, Q₂ᴴ)⟩)`; with
`P_i = R_i^{(∗)}`, `Q_i = M_i^{(∗)}` this is `conj X` of the opposite constellation. -/
theorem zgl_reversed_sub_eq_conj (σ : ℝ) (P₁ P₂ Q₁ Q₂ A : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (P₂ * Aᴴ * P₁) - NTrace (twoResApprox σ Q₂ Aᴴ Q₁) =
      conj (normalizedTrace (P₁ᴴ * A * P₂ᴴ) - NTrace (twoResApprox σ Q₁ᴴ A Q₂ᴴ)) := by
  rw [map_sub, zgl_NTrace_twoResApprox_swap, ← zgl_normalizedTrace_rev₃,
    conjTranspose_conjTranspose, conjTranspose_conjTranspose]

/-- **Adjoint of `M̂_σ`**: `(M̂_σ(M₁, A, M₂))ᴴ = M̂_σ(M₂, Aᴴ, M₁)`. -/
theorem zgl_hatApprox_conjTranspose (σ : ℝ) (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    (hatApprox σ M₁ A M₂)ᴴ = hatApprox σ M₂ Aᴴ M₁ := by
  rw [hatApprox, hatApprox, conjTranspose_smul, conjTranspose_sub, conjTranspose_sub,
    conjTranspose_add, zgl_twoResApprox_conjTranspose, zgl_twoResApprox_conjTranspose,
    zgl_twoResApprox_conjTranspose, zgl_twoResApprox_conjTranspose]
  simp only [conjTranspose_conjTranspose]
  have : star (-(1 / 4 : ℂ)) = -(1 / 4 : ℂ) := by
    rw [Complex.star_def, map_neg, map_div₀, map_one, map_ofNat]
  rw [this]
  congr 1
  abel

/-- `⟨M̂_σ(M₂, Aᴴ, M₁)⟩ = conj ⟨M̂_σ(M₁, A, M₂)⟩`. -/
theorem zgl_NTrace_hatApprox_swap (σ : ℝ) (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (hatApprox σ M₂ Aᴴ M₁) = conj (NTrace (hatApprox σ M₁ A M₂)) := by
  rw [← zgl_hatApprox_conjTranspose, zgl_NTrace_conjTranspose]

/-- **Symmetry of `⟨M^I_σ⟩`**: `⟨M^I_σ(M₂, M₁)⟩ = ⟨M^I_σ(M₁, M₂)⟩` (no hypothesis). -/
theorem zgl_NTrace_twoResApprox_one_comm (σ : ℝ) (M₁ M₂ : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (twoResApprox σ M₂ 1 M₁) = NTrace (twoResApprox σ M₁ 1 M₂) := by
  have h12 := NTrace_twoResApprox_mul σ M₁ 1 M₂ 1
  have h21 := NTrace_twoResApprox_mul σ M₂ 1 M₁ 1
  simp only [Matrix.mul_one] at h12 h21
  have hc : NTrace (M₂ * M₁) = NTrace (M₁ * M₂) := by
    simp only [NTrace, Conventions.normalizedTrace, Matrix.trace_mul_comm M₂ M₁]
  rw [h12, h21, hc, hybridDen_comm]

/-- **Regularity transfer**: `⟨M₂ Aᴴ M₁ᴴ⟩ = conj ⟨M₁ A M₂ᴴ⟩`. -/
theorem zgl_NTrace_reg_swap (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (M₂ * Aᴴ * M₁ᴴ) = conj (NTrace (M₁ * A * M₂ᴴ)) := by
  rw [← zgl_NTrace_rev₃, conjTranspose_conjTranspose]

/-- **Regularity of the adjoint**: if `A` is `(z₁, z₂)`-regular (`⟨M₁AM₂ᴴ⟩ = 0`), then `Aᴴ` is
`(z₂, z₁)`-regular. -/
theorem zgl_reg_swap {M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ} (hreg : NTrace (M₁ * A * M₂ᴴ) = 0) :
    NTrace (M₂ * Aᴴ * M₁ᴴ) = 0 := by
  rw [zgl_NTrace_reg_swap, hreg, map_zero]

/-- **`P` is unchanged**: `⟨Im M₂ Aᴴ Im M₁ (Aᴴ)ᴴ⟩ = ⟨Im M₁ A Im M₂ Aᴴ⟩`. -/
theorem zgl_chain_swap (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (matrixImaginaryPart M₂ * Aᴴ * matrixImaginaryPart M₁ * Aᴴᴴ) =
      NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ) := by
  rw [conjTranspose_conjTranspose]
  simp only [NTrace, Conventions.normalizedTrace]
  rw [show matrixImaginaryPart M₂ * Aᴴ * matrixImaginaryPart M₁ * A =
      (matrixImaginaryPart M₂ * Aᴴ) * (matrixImaginaryPart M₁ * A) by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- **Lemma 5.6 for the swapped data** `(z₂, z₁, M₂, M₁, Aᴴ)`: under the hypotheses of
`lemma56_window_bound_hermitian` for `(z₁, z₂, M₁, M₂, A)`, the bounds hold for the reversed
chains with the same constant `C = lemma56Const s K κ B` and the same
`√P = √Re⟨Im M₁ A Im M₂ Aᴴ⟩`. -/
theorem zgl_lemma56_window_bound_swap (hN : 0 < N) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s σ K κ B : ℝ} (hs : 0 < s) (hκ : 0 < κ) (hσ0 : 0 ≤ σ) (hσs : σ ≤ s)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) {M₁ M₂ : LocalETHMatrix N}
    (h₁ : IsLocalETHMDESolution s F z₁ M₁) (h₂ : IsLocalETHMDESolution s F z₂ M₂)
    (A : LocalETHMatrix N) (hreg : NTrace (M₁ * A * M₂ᴴ) = 0)
    (hκ₁ : κ ≤ (NTrace M₁).im) (hκ₂ : κ ≤ (NTrace M₂).im)
    (hK₁ : (NTrace M₁).im ≤ K) (hK₂ : (NTrace M₂).im ≤ K)
    (hB : ‖(z₁ + (s : ℂ) * NTrace M₁) - conj (z₂ + (s : ℂ) * NTrace M₂)‖ ≤ B) :
    ‖NTrace (twoResApprox σ M₂ Aᴴ M₁)‖ ≤ lemma56Const s K κ B *
        Real.sqrt (NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ)).re ∧
      ‖NTrace (twoResApprox σ M₂ᴴ Aᴴ M₁ᴴ)‖ ≤ lemma56Const s K κ B *
        Real.sqrt (NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ)).re ∧
      NTrace (twoResApprox σ M₂ Aᴴ M₁ᴴ) = 0 ∧
      ‖NTrace (twoResApprox σ M₂ᴴ Aᴴ M₁)‖ ≤ lemma56Const s K κ B *
        Real.sqrt (NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ)).re ∧
      ‖NTrace (hatApprox σ M₂ Aᴴ M₁)‖ ≤ lemma56Const s K κ B *
        Real.sqrt (NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ)).re := by
  have hB' : ‖(z₂ + (s : ℂ) * NTrace M₂) - conj (z₁ + (s : ℂ) * NTrace M₁)‖ ≤ B := by
    refine le_of_eq_of_le ?_ hB
    rw [← Complex.norm_conj, map_sub, Complex.conj_conj, ← norm_neg, neg_sub]
  have h := lemma56_window_bound_hermitian hN hF hs hκ hσ0 hσs hz₂ hz₁ h₂ h₁ Aᴴ
    (zgl_reg_swap hreg) hκ₂ hκ₁ hK₂ hK₁ hB'
  rw [zgl_chain_swap] at h
  exact h

end Approx

/-!
## The index-2 cyclic bridge
-/

section Bridge

variable {H : Matrix (Fin N) (Fin N) ℂ} {w₂ : ℂ}

/-- Cyclic step with a matrix `S` commuting with `Im R₂`: `⟨Im R₂ Aᴴ X A S⟩ = ⟨X A Im R₂ S Aᴴ⟩`
whenever `Im R₂ · S = S · Im R₂` (any matrices). -/
theorem zgl_bridge_comm {I₂ S : Matrix (Fin N) (Fin N) ℂ} (hc : I₂ * S = S * I₂)
    (X A : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (I₂ * Aᴴ * X * A * S) = normalizedTrace (X * A * I₂ * S * Aᴴ) := by
  have e1 : X * A * I₂ * S * Aᴴ = (X * A) * (I₂ * S * Aᴴ) := by simp only [Matrix.mul_assoc]
  have e2 : I₂ * S * Aᴴ * (X * A) = S * (I₂ * Aᴴ * X * A) := by
    rw [hc]; simp only [Matrix.mul_assoc]
  rw [e1, Phase1.normalizedTrace_mul_comm (X * A), e2, Phase1.normalizedTrace_mul_comm]

/-- **Index-2 bridge**: `⟨Im R₂ Aᴴ X A R₂⟩ = ⟨X A Im R₂ R₂ Aᴴ⟩` (the CEH index-2 form equals the
middle form `⟨Im R₁ A Im R₂ R₂ Aᴴ⟩` when `X = Im R₁`), `R₂ = (H - w₂)⁻¹`. -/
theorem zgl_bridge_index2 (hH : H.IsHermitian) (hw₂ : w₂.im ≠ 0)
    (X A : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₂) * Aᴴ * X * A *
        Phase1.resolvent H w₂) =
      normalizedTrace (X * A * External.CEH.imaginaryPart (Phase1.resolvent H w₂) *
        Phase1.resolvent H w₂ * Aᴴ) :=
  zgl_bridge_comm (bw_imaginaryPart_resolvent_mul_comm hH hw₂) X A

/-- **Index-2 bridge**, `R₂ᴴ` analogue: `⟨Im R₂ Aᴴ X A R₂ᴴ⟩ = ⟨X A Im R₂ R₂ᴴ Aᴴ⟩`. -/
theorem zgl_bridge_index2_conjTranspose (hH : H.IsHermitian) (hw₂ : w₂.im ≠ 0)
    (X A : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₂) * Aᴴ * X * A *
        (Phase1.resolvent H w₂)ᴴ) =
      normalizedTrace (X * A * External.CEH.imaginaryPart (Phase1.resolvent H w₂) *
        (Phase1.resolvent H w₂)ᴴ * Aᴴ) :=
  zgl_bridge_comm (fz_conjTranspose_mul_imaginaryPart_comm hH hw₂).symm X A

/-- **Index-2 bridge**, `fz_driftC_eq`'s intermediate form:
`⟨X A R₂ Im R₂ Aᴴ⟩ = ⟨X A Im R₂ R₂ Aᴴ⟩`. -/
theorem zgl_bridge_fz (hH : H.IsHermitian) (hw₂ : w₂.im ≠ 0) (X A : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (X * A * Phase1.resolvent H w₂ *
        External.CEH.imaginaryPart (Phase1.resolvent H w₂) * Aᴴ) =
      normalizedTrace (X * A * External.CEH.imaginaryPart (Phase1.resolvent H w₂) *
        Phase1.resolvent H w₂ * Aᴴ) := by
  rw [Matrix.mul_assoc (X * A), ← bw_imaginaryPart_resolvent_mul_comm hH hw₂, ← Matrix.mul_assoc]

/-- **The four `a`-terms of (7.2)**: for resolvents `R_i = (H - w_i)⁻¹` and any `a₁, a₂`,
`|a₁⟨I₁AI₂AᴴR₁⟩ + a₂⟨I₂AᴴI₁AR₂⟩ + ā₁⟨I₁AI₂AᴴR₁ᴴ⟩ + ā₂⟨I₂AᴴI₁AR₂ᴴ⟩|
  ≤ 2 (|a₁|/η₁ + |a₂|/η₂) |⟨Im R₁ A Im R₂ Aᴴ⟩|`, `η_i = |Im w_i|` (both indices). -/
theorem zgl_norm_index_terms_le (hH : H.IsHermitian) {w₁ : ℂ} (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) (a₁ a₂ : ℂ) :
    ‖a₁ * normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁) * A *
          External.CEH.imaginaryPart (Phase1.resolvent H w₂) * Aᴴ * Phase1.resolvent H w₁) +
        a₂ * normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₂) * Aᴴ *
          External.CEH.imaginaryPart (Phase1.resolvent H w₁) * A * Phase1.resolvent H w₂) +
        conj a₁ * normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁) * A *
          External.CEH.imaginaryPart (Phase1.resolvent H w₂) * Aᴴ * (Phase1.resolvent H w₁)ᴴ) +
        conj a₂ * normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₂) * Aᴴ *
          External.CEH.imaginaryPart (Phase1.resolvent H w₁) * A *
            (Phase1.resolvent H w₂)ᴴ)‖ ≤
      2 * (‖a₁‖ / |w₁.im| + ‖a₂‖ / |w₂.im|) *
        ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ := by
  set T := ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖
  have b1 := bw_norm_normalizedTrace_imChain_mul_resolvent_le hH hw₁ hw₂ A
  have b2 := bw_norm_normalizedTrace_imChain_swap_mul_resolvent_le hH hw₁ hw₂ A
  have b3 := bw_norm_normalizedTrace_imChain_mul_conjTranspose_resolvent_le hH hw₁ hw₂ A
  have b4 := bw_norm_normalizedTrace_imChain_swap_mul_conjTranspose_resolvent_le hH hw₁ hw₂ A
  have n1 := norm_nonneg a₁
  have n2 := norm_nonneg a₂
  refine norm_add₄_le.trans ?_
  simp only [norm_mul, Complex.norm_conj]
  have e : 2 * (‖a₁‖ / |w₁.im| + ‖a₂‖ / |w₂.im|) * T =
      ‖a₁‖ * (|w₁.im|⁻¹ * T) + ‖a₂‖ * (|w₂.im|⁻¹ * T) + ‖a₁‖ * (|w₁.im|⁻¹ * T) +
        ‖a₂‖ * (|w₂.im|⁻¹ * T) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  rw [e]
  exact add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left b1 n1)
    (mul_le_mul_of_nonneg_left b2 n2)) (mul_le_mul_of_nonneg_left b3 n1))
    (mul_le_mul_of_nonneg_left b4 n2)

end Bridge

end BlockBand.Native.CEH.ETH
