module

public import BlockBand.Native.CEH.ETH.BracketsWard
public import BlockBand.Native.CEH.ETH.FlowIto

/-!
# CEH ETH: bracket bounds for the `X` and `Y` chains

Setting (as in `BracketsWard`): one Hermitian `H : Matrix (Fin N) (Fin N) ℂ`, nonreal `w₁, w₂`
(no sign condition), `R_i = Phase1.resolvent H w_i = (H - w_i)⁻¹`, `η_i = |Im w_i|`, an
**arbitrary** matrix `A` (no norm bound is needed in this file), `⟨X⟩ = N⁻¹ tr X`,
`Im X = (2i)⁻¹ (X - Xᴴ)`, `T = ⟨Im R₁ A Im R₂ Aᴴ⟩ = ⟨bwImChain A R₁ R₂⟩` (a real number,
`BracketsWard`), `N` arbitrary.

**Constellations.** The adjoint resolvent is `R_iᴴ = Phase1.resolvent H (w̄_i)`
(`Phase1.resolvent_conjTranspose`), and `Im(R_iᴴ) = -Im R_i` (`bf_imaginaryPart_conjTranspose`).
So every statement below, being for arbitrary nonreal `w_i`, applies unchanged to each of the four
constellations `(w₁^{(∗)}, w₂^{(∗)})`, and `|T|` is the same in all four
(`bf_norm_normalizedTrace_bwImChain_conj_left/right`).

## Main results

* B3 (`X` chain, `B = 1` in the flow-resolvent bracket): with `P = R₁AR₂R₁`, `Q = R₂R₁AR₂`,
  `Re⟨PPᴴ⟩ ≤ η₁⁻³ η₂⁻¹ |T|` and `Re⟨QQᴴ⟩ ≤ η₁⁻¹ η₂⁻³ |T|`; the bracket densities satisfy
  `(1/N) ∑_x (Re or Im (⟨R₁E_xR₁AR₂·1⟩ + ⟨R₁AR₂E_xR₂·1⟩))² ≤ 2N⁻² (η₁⁻³η₂⁻¹ + η₁⁻¹η₂⁻³) |T|`
  (`bf_avgRe2_bracket_X_le`, `bf_avgIm2_bracket_X_le`), stated exactly in the form of
  `isContinuousSemimartingale_avgRe2/avgIm2_flowResolvent` with `B = 1`.
* B4 (`Y` chain, `A = 1`): the same with `A = 1`, `T_I = ⟨Im R₁ Im R₂⟩`
  (`bf_avgRe2_bracket_Y_le`, `bf_avgIm2_bracket_Y_le`); the four-constellation identities
  `⟨Im R₁ A Im R₂ Aᴴ⟩ = -¼ ∑_{a,b} ε_a ε_b ⟨R₁^{(a)} A R₂^{(b)} Aᴴ⟩` and
  `⟨Im R₁ Im R₂⟩ = -¼ ∑_{a,b} ε_a ε_b ⟨R₁^{(a)} R₂^{(b)}⟩` (`ε = +1` for `R`, `-1` for `Rᴴ`);
  and `|⟨Im R₁ Im R₂⟩| ≤ |⟨Im R₁⟩| / η₂`.
* B4′ (middle form): `|⟨Im R₁ A Im R₂ R₂ᴴ Aᴴ⟩| ≤ η₂⁻¹ |T|`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Matrix
open BlockBand.Native.CEH.Phase1
open BlockBand.SourceProcess.Stochastic.Dyson
open BlockBand.External.CEH (normalizedTrace)
open scoped ComplexConjugate

variable {N : ℕ}

/-!
## Imaginary parts and constellations
-/

/-- `⟨-X⟩ = -⟨X⟩`. -/
theorem bf_normalizedTrace_neg (X : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (-X) = -normalizedTrace X := by
  simp [normalizedTrace, trace_neg]

/-- `Im(Xᴴ) = -Im X`. -/
theorem bf_imaginaryPart_conjTranspose (X : Matrix (Fin N) (Fin N) ℂ) :
    External.CEH.imaginaryPart Xᴴ = -External.CEH.imaginaryPart X := by
  rw [External.CEH.imaginaryPart, External.CEH.imaginaryPart, conjTranspose_conjTranspose,
    ← smul_neg, neg_sub]

/-- `Im X` is Hermitian: `(Im X)ᴴ = Im X`. -/
theorem bf_conjTranspose_imaginaryPart (X : Matrix (Fin N) (Fin N) ℂ) :
    (External.CEH.imaginaryPart X)ᴴ = External.CEH.imaginaryPart X := by
  have h : star ((2 * Complex.I)⁻¹) = -(2 * Complex.I)⁻¹ := by
    rw [star_inv₀, star_mul', Complex.star_def, Complex.conj_I, map_ofNat, mul_neg, inv_neg]
  rw [External.CEH.imaginaryPart, conjTranspose_smul, conjTranspose_sub,
    conjTranspose_conjTranspose, h, neg_smul, ← smul_neg, neg_sub]

/-- Left constellation: `bwImChain A R₁ᴴ R₂ = -bwImChain A R₁ R₂`. -/
theorem bf_bwImChain_conjTranspose_left (A R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) :
    bwImChain A R₁ᴴ R₂ = -bwImChain A R₁ R₂ := by
  rw [bwImChain, bwImChain, bf_imaginaryPart_conjTranspose]
  simp only [Matrix.neg_mul]

/-- Right constellation: `bwImChain A R₁ R₂ᴴ = -bwImChain A R₁ R₂`. -/
theorem bf_bwImChain_conjTranspose_right (A R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) :
    bwImChain A R₁ R₂ᴴ = -bwImChain A R₁ R₂ := by
  rw [bwImChain, bwImChain, bf_imaginaryPart_conjTranspose]
  simp only [Matrix.neg_mul, Matrix.mul_neg]

section Resolvents

variable {H : Matrix (Fin N) (Fin N) ℂ} {w₁ w₂ : ℂ}

/-- `|T|` is the same in the constellation `(w̄₁, w₂)`. -/
theorem bf_norm_normalizedTrace_bwImChain_conj_left (hH : H.IsHermitian)
    (A R₂ : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace (bwImChain A (Phase1.resolvent H (conj w₁)) R₂)‖ =
      ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) R₂)‖ := by
  rw [← resolvent_conjTranspose hH, bf_bwImChain_conjTranspose_left, bf_normalizedTrace_neg,
    norm_neg]

/-- `|T|` is the same in the constellation `(w₁, w̄₂)`. -/
theorem bf_norm_normalizedTrace_bwImChain_conj_right (hH : H.IsHermitian)
    (A R₁ : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace (bwImChain A R₁ (Phase1.resolvent H (conj w₂)))‖ =
      ‖normalizedTrace (bwImChain A R₁ (Phase1.resolvent H w₂))‖ := by
  rw [← resolvent_conjTranspose hH, bf_bwImChain_conjTranspose_right, bf_normalizedTrace_neg,
    norm_neg]

/-- The drift coefficient of an adjoint resolvent: `⟨R(w̄)⟩ - m̄ = conj(⟨R(w)⟩ - m)`. -/
theorem bf_normalizedTrace_resolvent_conj_sub (hH : H.IsHermitian) (w m : ℂ) :
    normalizedTrace (Phase1.resolvent H (conj w)) - conj m =
      conj (normalizedTrace (Phase1.resolvent H w) - m) := by
  rw [← resolvent_conjTranspose hH, normalizedTrace_conjTranspose, map_sub]

/-!
## B3: the `X` bracket
-/

/-- **B3**, first half: `Re⟨PPᴴ⟩ ≤ η₁⁻³ η₂⁻¹ |T|` for `P = R₁ A R₂ R₁`. -/
theorem bf_re_normalizedTrace_P_le (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    (normalizedTrace ((Phase1.resolvent H w₁ * A * Phase1.resolvent H w₂ *
        Phase1.resolvent H w₁) * (Phase1.resolvent H w₁ * A * Phase1.resolvent H w₂ *
        Phase1.resolvent H w₁)ᴴ)).re ≤
      |w₁.im|⁻¹ ^ 3 * |w₂.im|⁻¹ *
        ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ := by
  set R₁ := Phase1.resolvent H w₁
  set R₂ := Phase1.resolvent H w₂
  set X := R₁ * A * R₂
  have e : (X * R₁) * (X * R₁)ᴴ = (R₁ᴴ * Xᴴ)ᴴ * (R₁ᴴ * Xᴴ) := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e]
  have h := bw_re_normalizedTrace_conjTranspose_mul_self_mul_le R₁ᴴ Xᴴ
    (sourceVectorNorm_resolvent_conjTranspose_mulVec_le hH hw₁)
  rw [conjTranspose_conjTranspose, bw_re_normalizedTrace_mul_conjTranspose_self_chain hH hw₁,
    bwChainMass_eq_norm_div hH hw₁ hw₂] at h
  refine h.trans (le_of_eq ?_)
  have h₁ : 0 < |w₁.im| := abs_pos.mpr hw₁
  have h₂ : 0 < |w₂.im| := abs_pos.mpr hw₂
  field_simp
  rfl

/-- **B3**, second half: `Re⟨QQᴴ⟩ ≤ η₁⁻¹ η₂⁻³ |T|` for `Q = R₂ R₁ A R₂`. -/
theorem bf_re_normalizedTrace_Q_le (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    (normalizedTrace ((Phase1.resolvent H w₂ * Phase1.resolvent H w₁ * A *
        Phase1.resolvent H w₂) * (Phase1.resolvent H w₂ * Phase1.resolvent H w₁ * A *
        Phase1.resolvent H w₂)ᴴ)).re ≤
      |w₁.im|⁻¹ * |w₂.im|⁻¹ ^ 3 *
        ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ := by
  set R₁ := Phase1.resolvent H w₁
  set R₂ := Phase1.resolvent H w₂
  set X := R₁ * A * R₂
  have e : R₂ * R₁ * A * R₂ = R₂ * X := by simp only [X, Matrix.mul_assoc]
  rw [e, ← bw_re_normalizedTrace_conjTranspose_mul_self]
  have h := bw_re_normalizedTrace_conjTranspose_mul_self_mul_le R₂ X
    (sourceVectorNorm_resolvent_mulVec_le hH hw₂)
  rw [bw_re_normalizedTrace_conjTranspose_mul_self_chain hH hw₁,
    bwChainMass_eq_norm_div hH hw₁ hw₂] at h
  refine h.trans (le_of_eq ?_)
  have h₁ : 0 < |w₁.im| := abs_pos.mpr hw₁
  have h₂ : 0 < |w₂.im| := abs_pos.mpr hw₂
  field_simp
  rfl

/-- The split bracket bound for `B = 1`, combined with B3. -/
theorem bf_split_X_le (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    2 / (N : ℝ) ^ 2 * ((normalizedTrace ((Phase1.resolvent H w₁ * A * Phase1.resolvent H w₂ *
        1 * Phase1.resolvent H w₁) * (Phase1.resolvent H w₁ * A * Phase1.resolvent H w₂ * 1 *
        Phase1.resolvent H w₁)ᴴ)).re +
      (normalizedTrace ((Phase1.resolvent H w₂ * 1 * Phase1.resolvent H w₁ * A *
        Phase1.resolvent H w₂) * (Phase1.resolvent H w₂ * 1 * Phase1.resolvent H w₁ * A *
        Phase1.resolvent H w₂)ᴴ)).re) ≤
      2 / (N : ℝ) ^ 2 * (|w₁.im|⁻¹ ^ 3 * |w₂.im|⁻¹ + |w₁.im|⁻¹ * |w₂.im|⁻¹ ^ 3) *
        ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ := by
  simp only [Matrix.mul_one]
  have hP := bf_re_normalizedTrace_P_le hH hw₁ hw₂ A
  have hQ := bf_re_normalizedTrace_Q_le hH hw₁ hw₂ A
  have hN : (0 : ℝ) ≤ 2 / (N : ℝ) ^ 2 := by positivity
  calc _ ≤ 2 / (N : ℝ) ^ 2 * (|w₁.im|⁻¹ ^ 3 * |w₂.im|⁻¹ *
          ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ +
        |w₁.im|⁻¹ * |w₂.im|⁻¹ ^ 3 *
          ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖) :=
        mul_le_mul_of_nonneg_left (add_le_add hP hQ) hN
    _ = _ := by ring

/-- **B3** (bracket of `X`, real part; CEH display before (7.4)): the bracket density of
`Re⟨R₁ A R₂ · 1⟩` (`isContinuousSemimartingale_avgRe2_flowResolvent` with `B = 1`) is at most
`2N⁻² (η₁⁻³η₂⁻¹ + η₁⁻¹η₂⁻³) |T|`. -/
theorem bf_avgRe2_bracket_X_le (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    1 / (N : ℝ) * ∑ x, (normalizedTrace (Phase1.resolvent H w₁ * hermBasis x *
        Phase1.resolvent H w₁ * A * Phase1.resolvent H w₂ * 1) +
      normalizedTrace (Phase1.resolvent H w₁ * A * Phase1.resolvent H w₂ * hermBasis x *
        Phase1.resolvent H w₂ * 1)).re ^ 2 ≤
      2 / (N : ℝ) ^ 2 * (|w₁.im|⁻¹ ^ 3 * |w₂.im|⁻¹ + |w₁.im|⁻¹ * |w₂.im|⁻¹ ^ 3) *
        ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ :=
  (avgRe2_bracket_le_split A 1 _ _).trans (bf_split_X_le hH hw₁ hw₂ A)

/-- **B3** (bracket of `X`, imaginary part): the bracket density of `Im⟨R₁ A R₂ · 1⟩` is at
most `2N⁻² (η₁⁻³η₂⁻¹ + η₁⁻¹η₂⁻³) |T|`. -/
theorem bf_avgIm2_bracket_X_le (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    1 / (N : ℝ) * ∑ x, (normalizedTrace (Phase1.resolvent H w₁ * hermBasis x *
        Phase1.resolvent H w₁ * A * Phase1.resolvent H w₂ * 1) +
      normalizedTrace (Phase1.resolvent H w₁ * A * Phase1.resolvent H w₂ * hermBasis x *
        Phase1.resolvent H w₂ * 1)).im ^ 2 ≤
      2 / (N : ℝ) ^ 2 * (|w₁.im|⁻¹ ^ 3 * |w₂.im|⁻¹ + |w₁.im|⁻¹ * |w₂.im|⁻¹ ^ 3) *
        ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ :=
  (avgIm2_bracket_le_split A 1 _ _).trans (bf_split_X_le hH hw₁ hw₂ A)

/-!
## B4: the `Y` bracket (`A = 1`)
-/

/-- `bwImChain 1 R₁ R₂ = Im R₁ Im R₂`. -/
theorem bf_bwImChain_one (R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) :
    bwImChain 1 R₁ R₂ = External.CEH.imaginaryPart R₁ * External.CEH.imaginaryPart R₂ := by
  rw [bwImChain, conjTranspose_one, Matrix.mul_one, Matrix.mul_one]

/-- **B4** (bracket of `Y`, real part): the bracket density of `Re⟨R₁ · 1 · R₂ · 1⟩` is at
most `2N⁻² (η₁⁻³η₂⁻¹ + η₁⁻¹η₂⁻³) |⟨Im R₁ Im R₂⟩|`. -/
theorem bf_avgRe2_bracket_Y_le (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0) :
    1 / (N : ℝ) * ∑ x, (normalizedTrace (Phase1.resolvent H w₁ * hermBasis x *
        Phase1.resolvent H w₁ * 1 * Phase1.resolvent H w₂ * 1) +
      normalizedTrace (Phase1.resolvent H w₁ * 1 * Phase1.resolvent H w₂ * hermBasis x *
        Phase1.resolvent H w₂ * 1)).re ^ 2 ≤
      2 / (N : ℝ) ^ 2 * (|w₁.im|⁻¹ ^ 3 * |w₂.im|⁻¹ + |w₁.im|⁻¹ * |w₂.im|⁻¹ ^ 3) *
        ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁) *
          External.CEH.imaginaryPart (Phase1.resolvent H w₂))‖ := by
  rw [← bf_bwImChain_one]
  exact bf_avgRe2_bracket_X_le hH hw₁ hw₂ 1

/-- **B4** (bracket of `Y`, imaginary part). -/
theorem bf_avgIm2_bracket_Y_le (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0) :
    1 / (N : ℝ) * ∑ x, (normalizedTrace (Phase1.resolvent H w₁ * hermBasis x *
        Phase1.resolvent H w₁ * 1 * Phase1.resolvent H w₂ * 1) +
      normalizedTrace (Phase1.resolvent H w₁ * 1 * Phase1.resolvent H w₂ * hermBasis x *
        Phase1.resolvent H w₂ * 1)).im ^ 2 ≤
      2 / (N : ℝ) ^ 2 * (|w₁.im|⁻¹ ^ 3 * |w₂.im|⁻¹ + |w₁.im|⁻¹ * |w₂.im|⁻¹ ^ 3) *
        ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁) *
          External.CEH.imaginaryPart (Phase1.resolvent H w₂))‖ := by
  rw [← bf_bwImChain_one]
  exact bf_avgIm2_bracket_X_le hH hw₁ hw₂ 1

/-- **B4**, trivial bound: `|⟨Im R₁ Im R₂⟩| ≤ |⟨Im R₁⟩| / η₂`. -/
theorem bf_norm_normalizedTrace_imaginaryPart_mul_le (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) :
    ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁) *
        External.CEH.imaginaryPart (Phase1.resolvent H w₂))‖ ≤
      ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁))‖ / |w₂.im| := by
  set R₁ := Phase1.resolvent H w₁
  set R₂ := Phase1.resolvent H w₂
  have h₁ : 0 < |w₁.im| := abs_pos.mpr hw₁
  have h₂ : 0 < |w₂.im| := abs_pos.mpr hw₂
  rw [← bf_bwImChain_one, bw_norm_normalizedTrace_imChain hH hw₁ hw₂]
  have hc : R₁ᴴ * 1 * R₂ = R₂ * R₁ᴴ := by
    rw [Matrix.mul_one, resolvent_conjTranspose hH]
    exact resolvent_commute hH (by simpa using hw₁) hw₂
  have hm : bwChainMass 1 R₁ R₂ ≤
      |w₂.im|⁻¹ ^ 2 * (‖normalizedTrace (External.CEH.imaginaryPart R₁)‖ / |w₁.im|) := by
    rw [bwChainMass, hc, ← bw_re_normalizedTrace_conjTranspose_mul_self]
    have h := bw_re_normalizedTrace_conjTranspose_mul_self_mul_le R₂ R₁ᴴ
      (sourceVectorNorm_resolvent_mulVec_le hH hw₂)
    rw [conjTranspose_conjTranspose, bw_re_normalizedTrace_resolvent_mul_conjTranspose hH hw₁]
      at h
    exact h
  calc |w₁.im| * |w₂.im| * bwChainMass 1 R₁ R₂
      ≤ |w₁.im| * |w₂.im| *
          (|w₂.im|⁻¹ ^ 2 * (‖normalizedTrace (External.CEH.imaginaryPart R₁)‖ / |w₁.im|)) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by field_simp

/-- Four-constellation identity (any matrices):
`⟨Im R₁ A Im R₂ Aᴴ⟩ = -¼ (⟨R₁AR₂Aᴴ⟩ - ⟨R₁AR₂ᴴAᴴ⟩ - ⟨R₁ᴴAR₂Aᴴ⟩ + ⟨R₁ᴴAR₂ᴴAᴴ⟩)`. -/
theorem bf_normalizedTrace_bwImChain_eq_four (A R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (bwImChain A R₁ R₂) =
      -(1 / 4 : ℂ) * (normalizedTrace (R₁ * A * R₂ * Aᴴ) - normalizedTrace (R₁ * A * R₂ᴴ * Aᴴ) -
        normalizedTrace (R₁ᴴ * A * R₂ * Aᴴ) + normalizedTrace (R₁ᴴ * A * R₂ᴴ * Aᴴ)) := by
  have h2 : (2 * Complex.I)⁻¹ = -Complex.I / 2 := by
    rw [mul_inv, Complex.inv_I]
    ring
  rw [bwImChain, External.CEH.imaginaryPart, External.CEH.imaginaryPart, h2]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    normalizedTrace_smul, normalizedTrace_sub]
  linear_combination (1 / 4 : ℂ) * (normalizedTrace (R₁ * A * R₂ * Aᴴ) -
    normalizedTrace (R₁ * A * R₂ᴴ * Aᴴ) - normalizedTrace (R₁ᴴ * A * R₂ * Aᴴ) +
    normalizedTrace (R₁ᴴ * A * R₂ᴴ * Aᴴ)) * Complex.I_sq

/-- Four-constellation identity for resolvents: `T = -¼ ∑_{a,b} ε_a ε_b ⟨R₁^{(a)}AR₂^{(b)}Aᴴ⟩`,
with `R_i^{(∗)} = R(w̄_i)`. -/
theorem bf_normalizedTrace_imChain_eq_four (hH : H.IsHermitian)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂)) =
      -(1 / 4 : ℂ) * (normalizedTrace (Phase1.resolvent H w₁ * A * Phase1.resolvent H w₂ * Aᴴ) -
        normalizedTrace (Phase1.resolvent H w₁ * A * Phase1.resolvent H (conj w₂) * Aᴴ) -
        normalizedTrace (Phase1.resolvent H (conj w₁) * A * Phase1.resolvent H w₂ * Aᴴ) +
        normalizedTrace (Phase1.resolvent H (conj w₁) * A *
          Phase1.resolvent H (conj w₂) * Aᴴ)) := by
  rw [bf_normalizedTrace_bwImChain_eq_four, resolvent_conjTranspose hH,
    resolvent_conjTranspose hH]

/-- **B4**, four-constellation identity for the `A = 1` chain:
`⟨Im R₁ Im R₂⟩ = -¼ (⟨R₁R₂⟩ - ⟨R₁R(w̄₂)⟩ - ⟨R(w̄₁)R₂⟩ + ⟨R(w̄₁)R(w̄₂)⟩)`. -/
theorem bf_normalizedTrace_imaginaryPart_mul_eq_four (hH : H.IsHermitian) :
    normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁) *
        External.CEH.imaginaryPart (Phase1.resolvent H w₂)) =
      -(1 / 4 : ℂ) * (normalizedTrace (Phase1.resolvent H w₁ * Phase1.resolvent H w₂) -
        normalizedTrace (Phase1.resolvent H w₁ * Phase1.resolvent H (conj w₂)) -
        normalizedTrace (Phase1.resolvent H (conj w₁) * Phase1.resolvent H w₂) +
        normalizedTrace (Phase1.resolvent H (conj w₁) * Phase1.resolvent H (conj w₂))) := by
  have h := bf_normalizedTrace_imChain_eq_four (w₁ := w₁) (w₂ := w₂) hH 1
  simpa only [bf_bwImChain_one, Matrix.mul_one, conjTranspose_one] using h

/-!
## B4′: the `R₂ᴴ` middle form
-/

/-- **B4′**: `|⟨Im R₁ A Im R₂ R₂ᴴ Aᴴ⟩| ≤ η₂⁻¹ |T|`. -/
theorem bf_norm_normalizedTrace_imChain_mid_conjTranspose_resolvent_le (hH : H.IsHermitian)
    (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁) * A *
        External.CEH.imaginaryPart (Phase1.resolvent H w₂) * (Phase1.resolvent H w₂)ᴴ * Aᴴ)‖ ≤
      |w₂.im|⁻¹ *
        ‖normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))‖ := by
  have hw₂' : (conj w₂).im ≠ 0 := by simpa using hw₂
  have h := bw_norm_normalizedTrace_imChain_mid_resolvent_le hH hw₁ hw₂' A
  rw [← resolvent_conjTranspose hH, bf_bwImChain_conjTranspose_right, bf_normalizedTrace_neg,
    norm_neg, bf_imaginaryPart_conjTranspose, Complex.conj_im, abs_neg] at h
  simpa only [Matrix.mul_neg, Matrix.neg_mul, bf_normalizedTrace_neg, norm_neg] using h

end Resolvents

end BlockBand.Native.CEH.ETH
