module

public import BlockBand.Native.CEH.ETH.BracketsFlow

/-!
# CEH ETH: the `Z` bracket and the `Z` drift identity

Setting as in `BracketsWard`/`BracketsFlow`: Hermitian `H`, nonreal `w₁, w₂` (no sign condition),
`R_i = Phase1.resolvent H w_i`, `η_i = |Im w_i|`, **arbitrary** `A`, `I_i = Im R_i`,
`X = bwImChain A R₁ R₂ = I₁ A I₂ Aᴴ`, `T = ⟨X⟩` (real), `N` arbitrary.

## Main results

* `bfZDiff_im_eq_zero`: `D(E)` is real for Hermitian `E` (any matrices `R₁, R₂, A`).
* `bfZDiff_eq_normalizedTrace`: `D(E) = ⟨E S⟩` with an explicit `S` (`bfZS`), any `E`.
* **BZ** (`bf_avg_bracket_Z_le`): `(1/N) ∑_x D(E_x)² ≤ 2N⁻² (η₁⁻² + η₂⁻²) Re⟨X X⟩`, and
  (`bf_avg_bracket_Z_le_sq`, with `bw_re_normalizedTrace_imChain_sq_le`) `≤ 2N⁻¹ (η₁⁻² + η₂⁻²) (Re T)²`; also the `|D|²` forms.
  Here `C = 2`.
* **Z drift identity** (`bf_zDrift_four`): for scalars `a₁, a₂` (the coefficients `⟨R_i⟩ - m_i`;
  in the adjoint constellation the coefficient is `conj a_i`,
  `bf_normalizedTrace_resolvent_conj_sub`), the `-¼ ∑ ε_a ε_b` combination of the
  `(⟨R_i⟩ - m_i)`-parts of the flow-resolvent drifts (`B = Aᴴ`) of the four chains
  `⟨R₁^{(a)} A R₂^{(b)} Aᴴ⟩` equals the real number
  `(Im a₁/Im w₁ + Im a₂/Im w₂) T + 2 Re(a₁ ⟨X R₁⟩) + 2 Re(a₂ ⟨I₁ A I₂ R₂ Aᴴ⟩)`.
  The cross terms `⟨R₁AR₂⟩⟨R₂AᴴR₁⟩` of the drift are not treated here.
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
## The directional derivative of `Z`
-/

/-- `ImS(R, E) = (2i)⁻¹ (R E R - Rᴴ E Rᴴ)`. -/
def bfImS (R E : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (2 * Complex.I)⁻¹ • (R * E * R - Rᴴ * E * Rᴴ)

/-- For Hermitian `E`, `ImS(R, E) = Im(R E R)`. -/
theorem bfImS_eq_imaginaryPart (R : Matrix (Fin N) (Fin N) ℂ) {E : Matrix (Fin N) (Fin N) ℂ}
    (hE : E.IsHermitian) : bfImS R E = External.CEH.imaginaryPart (R * E * R) := by
  rw [bfImS, External.CEH.imaginaryPart, conjTranspose_mul, conjTranspose_mul, hE.eq]
  simp only [Matrix.mul_assoc]

/-- `D(E) = ⟨ImS(R₁, E) A Im R₂ Aᴴ⟩ + ⟨Im R₁ A ImS(R₂, E) Aᴴ⟩` (minus the derivative of `Z` in
the direction `E`). -/
def bfZDiff (A R₁ R₂ E : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  normalizedTrace (bfImS R₁ E * A * External.CEH.imaginaryPart R₂ * Aᴴ) +
    normalizedTrace (External.CEH.imaginaryPart R₁ * A * bfImS R₂ E * Aᴴ)

/-- `⟨S Y⟩` is real for `Sᴴ = S`, `Yᴴ = Y`. -/
theorem bf_im_normalizedTrace_mul_herm {S Y : Matrix (Fin N) (Fin N) ℂ} (hS : Sᴴ = S)
    (hY : Yᴴ = Y) : (normalizedTrace (S * Y)).im = 0 := by
  rw [← Complex.conj_eq_iff_im, ← normalizedTrace_conjTranspose, conjTranspose_mul, hS, hY,
    normalizedTrace_mul_comm]

/-- `(A Im R Aᴴ)ᴴ = A Im R Aᴴ`. -/
theorem bf_conjTranspose_sandwich (A R : Matrix (Fin N) (Fin N) ℂ) :
    (A * External.CEH.imaginaryPart R * Aᴴ)ᴴ = A * External.CEH.imaginaryPart R * Aᴴ := by
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    bf_conjTranspose_imaginaryPart, Matrix.mul_assoc]

/-- `D(E)` is real for Hermitian `E` (any `A, R₁, R₂`). -/
theorem bfZDiff_im_eq_zero (A R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) {E : Matrix (Fin N) (Fin N) ℂ}
    (hE : E.IsHermitian) : (bfZDiff A R₁ R₂ E).im = 0 := by
  have hS₁ := bf_conjTranspose_imaginaryPart (R₁ * E * R₁)
  have hS₂ := bf_conjTranspose_imaginaryPart (R₂ * E * R₂)
  rw [← bfImS_eq_imaginaryPart _ hE] at hS₁ hS₂
  have e₁ : bfImS R₁ E * A * External.CEH.imaginaryPart R₂ * Aᴴ =
      bfImS R₁ E * (A * External.CEH.imaginaryPart R₂ * Aᴴ) := by
    simp only [Matrix.mul_assoc]
  have e₂ : normalizedTrace (External.CEH.imaginaryPart R₁ * A * bfImS R₂ E * Aᴴ) =
      normalizedTrace (bfImS R₂ E * (Aᴴ * External.CEH.imaginaryPart R₁ * A)) := by
    rw [show External.CEH.imaginaryPart R₁ * A * bfImS R₂ E * Aᴴ =
      (External.CEH.imaginaryPart R₁ * A) * (bfImS R₂ E * Aᴴ) by simp only [Matrix.mul_assoc],
      normalizedTrace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hY₁ := bf_conjTranspose_sandwich Aᴴ R₁
  rw [conjTranspose_conjTranspose] at hY₁
  rw [bfZDiff, Complex.add_im, e₁, e₂, bf_im_normalizedTrace_mul_herm hS₁
    (bf_conjTranspose_sandwich A R₂), bf_im_normalizedTrace_mul_herm hS₂ hY₁, add_zero]

/-- The matrix `S` with `D(E) = ⟨E S⟩`: with `Y₂ = A Im R₂ Aᴴ`, `Y₁ = Aᴴ Im R₁ A`,
`S = (2i)⁻¹ ((R₁Y₂R₁ - R₁ᴴY₂R₁ᴴ) + (R₂Y₁R₂ - R₂ᴴY₁R₂ᴴ))`. -/
def bfZS (A R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (2 * Complex.I)⁻¹ •
    ((R₁ * (A * External.CEH.imaginaryPart R₂ * Aᴴ) * R₁ -
        R₁ᴴ * (A * External.CEH.imaginaryPart R₂ * Aᴴ) * R₁ᴴ) +
      (R₂ * (Aᴴ * External.CEH.imaginaryPart R₁ * A) * R₂ -
        R₂ᴴ * (Aᴴ * External.CEH.imaginaryPart R₁ * A) * R₂ᴴ))

/-- `⟨R E R' Y⟩ = ⟨E (R' Y R)⟩`. -/
theorem bf_normalizedTrace_cyc_left (R E R' Y : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (R * E * R' * Y) = normalizedTrace (E * (R' * Y * R)) := by
  rw [show R * E * R' * Y = R * (E * R' * Y) by simp only [Matrix.mul_assoc],
    normalizedTrace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- `⟨I A (R E R) Aᴴ⟩ = ⟨E (R (Aᴴ I A) R)⟩`. -/
theorem bf_normalizedTrace_cyc_mid (I A R E : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (I * A * (R * E * R) * Aᴴ) = normalizedTrace (E * (R * (Aᴴ * I * A) * R)) := by
  rw [show I * A * (R * E * R) * Aᴴ = (I * A * R) * (E * R * Aᴴ) by simp only [Matrix.mul_assoc],
    normalizedTrace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- `D(E) = ⟨E S⟩` (any matrices). -/
theorem bfZDiff_eq_normalizedTrace (A R₁ R₂ E : Matrix (Fin N) (Fin N) ℂ) :
    bfZDiff A R₁ R₂ E = normalizedTrace (E * bfZS A R₁ R₂) := by
  set I₁ := External.CEH.imaginaryPart R₁
  set I₂ := External.CEH.imaginaryPart R₂
  have e₁ : normalizedTrace (bfImS R₁ E * A * I₂ * Aᴴ) =
      (2 * Complex.I)⁻¹ * (normalizedTrace (E * (R₁ * (A * I₂ * Aᴴ) * R₁)) -
        normalizedTrace (E * (R₁ᴴ * (A * I₂ * Aᴴ) * R₁ᴴ))) := by
    rw [bfImS, show ((2 * Complex.I)⁻¹ • (R₁ * E * R₁ - R₁ᴴ * E * R₁ᴴ)) * A * I₂ * Aᴴ =
      (2 * Complex.I)⁻¹ • (R₁ * E * R₁ * (A * I₂ * Aᴴ) - R₁ᴴ * E * R₁ᴴ * (A * I₂ * Aᴴ)) by
        simp only [Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_assoc],
      normalizedTrace_smul, normalizedTrace_sub, bf_normalizedTrace_cyc_left,
      bf_normalizedTrace_cyc_left]
  have e₂ : normalizedTrace (I₁ * A * bfImS R₂ E * Aᴴ) =
      (2 * Complex.I)⁻¹ * (normalizedTrace (E * (R₂ * (Aᴴ * I₁ * A) * R₂)) -
        normalizedTrace (E * (R₂ᴴ * (Aᴴ * I₁ * A) * R₂ᴴ))) := by
    rw [bfImS, show I₁ * A * ((2 * Complex.I)⁻¹ • (R₂ * E * R₂ - R₂ᴴ * E * R₂ᴴ)) * Aᴴ =
      (2 * Complex.I)⁻¹ • (I₁ * A * (R₂ * E * R₂) * Aᴴ - I₁ * A * (R₂ᴴ * E * R₂ᴴ) * Aᴴ) by
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub],
      normalizedTrace_smul, normalizedTrace_sub, bf_normalizedTrace_cyc_mid,
      bf_normalizedTrace_cyc_mid]
  rw [bfZDiff, e₁, e₂, bfZS, Matrix.mul_smul, normalizedTrace_smul, Matrix.mul_add,
    Matrix.mul_sub, Matrix.mul_sub, normalizedTrace_add, normalizedTrace_sub, normalizedTrace_sub]
  ring

/-!
## Summation over the Hermitian basis
-/

/-- `(1/N) ∑_x |⟨E_x S⟩|² = N⁻² Re⟨S Sᴴ⟩` (orthonormality of `hermBasis` for `tr(XY)`). -/
theorem bf_avg_normSq_normalizedTrace_hermBasis (S : Matrix (Fin N) (Fin N) ℂ) :
    1 / (N : ℝ) * ∑ x, Complex.normSq (normalizedTrace (hermBasis x * S)) =
      1 / (N : ℝ) ^ 2 * (normalizedTrace (S * Sᴴ)).re := by
  have h : ∀ x, Complex.normSq (normalizedTrace (hermBasis x * S)) =
      1 / (N : ℝ) ^ 2 * Complex.normSq (trace (hermBasis x * S)) := by
    intro x
    rw [normalizedTrace, Complex.normSq_mul, normSq_inv_natCast]
  simp only [h]
  rw [← Finset.mul_sum, Flow.sum_normSq_trace, normalizedTrace_re_mul_conjTranspose]
  ring

/-- `Re⟨(c • M)(c • M)ᴴ⟩ = |c|² Re⟨M Mᴴ⟩`. -/
theorem bf_re_normalizedTrace_smul_mul_conjTranspose (c : ℂ) (M : Matrix (Fin N) (Fin N) ℂ) :
    (normalizedTrace ((c • M) * (c • M)ᴴ)).re =
      Complex.normSq c * (normalizedTrace (M * Mᴴ)).re := by
  rw [normalizedTrace_re_mul_conjTranspose, normalizedTrace_re_mul_conjTranspose,
    Flow.trace_smul_mul_conjTranspose]
  ring

/-- `Re⟨(P - Q)(P - Q)ᴴ⟩ ≤ 2 (Re⟨PPᴴ⟩ + Re⟨QQᴴ⟩)`. -/
theorem bf_normalizedTrace_sub_mul_conjTranspose_le (P Q : Matrix (Fin N) (Fin N) ℂ) :
    (normalizedTrace ((P - Q) * (P - Q)ᴴ)).re ≤
      2 * ((normalizedTrace (P * Pᴴ)).re + (normalizedTrace (Q * Qᴴ)).re) := by
  have h := normalizedTrace_add_mul_conjTranspose_le P (-Q)
  rwa [← sub_eq_add_neg, conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] at h

/-- `Re⟨S Sᴴ⟩ ≤ Re⟨V₁V₁ᴴ⟩ + Re⟨W₁W₁ᴴ⟩ + Re⟨V₂V₂ᴴ⟩ + Re⟨W₂W₂ᴴ⟩` for
`S = (2i)⁻¹ ((V₁ - W₁) + (V₂ - W₂))`. -/
theorem bf_re_normalizedTrace_four_le (V₁ W₁ V₂ W₂ : Matrix (Fin N) (Fin N) ℂ) :
    (normalizedTrace (((2 * Complex.I)⁻¹ • ((V₁ - W₁) + (V₂ - W₂))) *
        ((2 * Complex.I)⁻¹ • ((V₁ - W₁) + (V₂ - W₂)))ᴴ)).re ≤
      (normalizedTrace (V₁ * V₁ᴴ)).re + (normalizedTrace (W₁ * W₁ᴴ)).re +
        (normalizedTrace (V₂ * V₂ᴴ)).re + (normalizedTrace (W₂ * W₂ᴴ)).re := by
  have hc : Complex.normSq (2 * Complex.I)⁻¹ = 1 / 4 := by
    rw [Complex.normSq_inv, Complex.normSq_mul, Complex.normSq_I]
    norm_num
  rw [bf_re_normalizedTrace_smul_mul_conjTranspose, hc]
  have h := normalizedTrace_add_mul_conjTranspose_le (V₁ - W₁) (V₂ - W₂)
  have h₁ := bf_normalizedTrace_sub_mul_conjTranspose_le V₁ W₁
  have h₂ := bf_normalizedTrace_sub_mul_conjTranspose_le V₂ W₂
  linarith

section Resolvents

variable {H : Matrix (Fin N) (Fin N) ℂ} {w₁ w₂ : ℂ}

/-- Ward for the sandwich `V = R Y R`, `Yᴴ = Y`: `⟨V Vᴴ⟩ = (Im w)⁻² ⟨Im R Y Im R Y⟩`. -/
theorem bf_normalizedTrace_sandwich_sq (hH : H.IsHermitian) {w : ℂ} (hw : w.im ≠ 0)
    {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Yᴴ = Y) :
    normalizedTrace ((Phase1.resolvent H w * Y * Phase1.resolvent H w) *
        (Phase1.resolvent H w * Y * Phase1.resolvent H w)ᴴ) =
      (((w.im)⁻¹ ^ 2 : ℝ) : ℂ) * normalizedTrace (External.CEH.imaginaryPart
        (Phase1.resolvent H w) * Y * External.CEH.imaginaryPart (Phase1.resolvent H w) * Y) := by
  set R := Phase1.resolvent H w
  have e : (R * Y * R) * (R * Y * R)ᴴ = (R * Y * (R * Rᴴ) * Y) * Rᴴ := by
    simp only [conjTranspose_mul, hY, Matrix.mul_assoc]
  rw [e, normalizedTrace_mul_comm,
    show Rᴴ * (R * Y * (R * Rᴴ) * Y) = (Rᴴ * R) * Y * (R * Rᴴ) * Y by
      simp only [Matrix.mul_assoc],
    conjTranspose_mul_resolvent hH hw, resolvent_mul_conjTranspose hH hw]
  simp only [Matrix.smul_mul, Matrix.mul_smul, normalizedTrace_smul]
  push_cast
  ring

/-- Ward for the adjoint sandwich `W = Rᴴ Y Rᴴ`, `Yᴴ = Y`: `⟨W Wᴴ⟩ = (Im w)⁻² ⟨Im R Y Im R Y⟩`. -/
theorem bf_normalizedTrace_sandwich_conjTranspose_sq (hH : H.IsHermitian) {w : ℂ}
    (hw : w.im ≠ 0) {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Yᴴ = Y) :
    normalizedTrace (((Phase1.resolvent H w)ᴴ * Y * (Phase1.resolvent H w)ᴴ) *
        ((Phase1.resolvent H w)ᴴ * Y * (Phase1.resolvent H w)ᴴ)ᴴ) =
      (((w.im)⁻¹ ^ 2 : ℝ) : ℂ) * normalizedTrace (External.CEH.imaginaryPart
        (Phase1.resolvent H w) * Y * External.CEH.imaginaryPart (Phase1.resolvent H w) * Y) := by
  set R := Phase1.resolvent H w
  have e : (Rᴴ * Y * Rᴴ) * (Rᴴ * Y * Rᴴ)ᴴ = (Rᴴ * Y * (Rᴴ * R) * Y) * R := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hY, Matrix.mul_assoc]
  rw [e, normalizedTrace_mul_comm,
    show R * (Rᴴ * Y * (Rᴴ * R) * Y) = (R * Rᴴ) * Y * (Rᴴ * R) * Y by
      simp only [Matrix.mul_assoc],
    conjTranspose_mul_resolvent hH hw, resolvent_mul_conjTranspose hH hw]
  simp only [Matrix.smul_mul, Matrix.mul_smul, normalizedTrace_smul]
  push_cast
  ring

/-- `Re⟨S Sᴴ⟩ ≤ 2 (η₁⁻² + η₂⁻²) Re⟨X X⟩` for `S = bfZS A R₁ R₂`, `X = bwImChain A R₁ R₂`. -/
theorem bf_re_normalizedTrace_bfZS_le (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    (normalizedTrace (bfZS A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) *
        (bfZS A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))ᴴ)).re ≤
      2 * (|w₁.im|⁻¹ ^ 2 + |w₂.im|⁻¹ ^ 2) *
        (normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) *
          bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))).re := by
  have hY₂ := bf_conjTranspose_sandwich A (Phase1.resolvent H w₂)
  have hY₁ := bf_conjTranspose_sandwich Aᴴ (Phase1.resolvent H w₁)
  rw [conjTranspose_conjTranspose] at hY₁
  rw [bfZS]
  refine (bf_re_normalizedTrace_four_le _ _ _ _).trans (le_of_eq ?_)
  rw [bf_normalizedTrace_sandwich_sq hH hw₁ hY₂, bf_normalizedTrace_sandwich_sq hH hw₂ hY₁,
    bf_normalizedTrace_sandwich_conjTranspose_sq hH hw₁ hY₂,
    bf_normalizedTrace_sandwich_conjTranspose_sq hH hw₂ hY₁]
  set I₁ := External.CEH.imaginaryPart (Phase1.resolvent H w₁)
  set I₂ := External.CEH.imaginaryPart (Phase1.resolvent H w₂)
  have e₁ : normalizedTrace (I₁ * (A * I₂ * Aᴴ) * I₁ * (A * I₂ * Aᴴ)) =
      normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) *
        bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂)) := by
    simp only [bwImChain, Matrix.mul_assoc]
    rfl
  have e₂ : normalizedTrace (I₂ * (Aᴴ * I₁ * A) * I₂ * (Aᴴ * I₁ * A)) =
      normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) *
        bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂)) := by
    rw [show I₂ * (Aᴴ * I₁ * A) * I₂ * (Aᴴ * I₁ * A) =
      (I₂ * Aᴴ * I₁ * A * I₂ * Aᴴ) * (I₁ * A) by simp only [Matrix.mul_assoc],
      normalizedTrace_mul_comm]
    simp only [bwImChain, Matrix.mul_assoc]
    rfl
  rw [e₁, e₂, Complex.re_ofReal_mul, Complex.re_ofReal_mul, inv_pow, inv_pow, ← sq_abs w₁.im,
    ← sq_abs w₂.im, inv_pow, inv_pow]
  ring

/-- **BZ**, `|D|²` form: `(1/N) ∑_x |D(E_x)|² ≤ 2N⁻² (η₁⁻² + η₂⁻²) Re⟨X X⟩`. -/
theorem bf_avg_normSq_bracket_Z_le (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    1 / (N : ℝ) * ∑ x, Complex.normSq
        (bfZDiff A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) (hermBasis x)) ≤
      2 / (N : ℝ) ^ 2 * (|w₁.im|⁻¹ ^ 2 + |w₂.im|⁻¹ ^ 2) *
        (normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) *
          bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))).re := by
  simp only [bfZDiff_eq_normalizedTrace]
  rw [bf_avg_normSq_normalizedTrace_hermBasis]
  have h := bf_re_normalizedTrace_bfZS_le hH hw₁ hw₂ A
  have hN : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 2 := by positivity
  calc _ ≤ 1 / (N : ℝ) ^ 2 * (2 * (|w₁.im|⁻¹ ^ 2 + |w₂.im|⁻¹ ^ 2) *
        (normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) *
          bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))).re) :=
        mul_le_mul_of_nonneg_left h hN
    _ = _ := by ring

/-- **BZ** (bracket of `Z`): `(1/N) ∑_x D(E_x)² ≤ 2N⁻² (η₁⁻² + η₂⁻²) Re⟨X X⟩`,
`X = Im R₁ A Im R₂ Aᴴ` (`D(E_x)` is real by `bfZDiff_im_eq_zero`). -/
theorem bf_avg_bracket_Z_le (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    1 / (N : ℝ) * ∑ x,
        (bfZDiff A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) (hermBasis x)).re ^ 2 ≤
      2 / (N : ℝ) ^ 2 * (|w₁.im|⁻¹ ^ 2 + |w₂.im|⁻¹ ^ 2) *
        (normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) *
          bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))).re := by
  refine le_trans ?_ (bf_avg_normSq_bracket_Z_le hH hw₁ hw₂ A)
  have hN : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) hN
  rw [sq]
  exact Complex.re_sq_le_normSq _

/-- `2 N⁻² c (N t) = 2 N⁻¹ c t` (also for `N = 0`). -/
theorem bf_two_div_sq_mul_natCast (c t : ℝ) :
    2 / (N : ℝ) ^ 2 * c * ((N : ℝ) * t) = 2 / (N : ℝ) * c * t := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    simp
  · have hN : (N : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    field_simp

/-- **BZ**, final form (with `bw_re_normalizedTrace_imChain_sq_le`): `(1/N) ∑_x D(E_x)² ≤ 2N⁻¹ (η₁⁻² + η₂⁻²) (Re T)²`,
`T = ⟨Im R₁ A Im R₂ Aᴴ⟩`. -/
theorem bf_avg_bracket_Z_le_sq (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    1 / (N : ℝ) * ∑ x,
        (bfZDiff A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) (hermBasis x)).re ^ 2 ≤
      2 / (N : ℝ) * (|w₁.im|⁻¹ ^ 2 + |w₂.im|⁻¹ ^ 2) *
        (normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))).re ^ 2 := by
  refine (bf_avg_bracket_Z_le hH hw₁ hw₂ A).trans ?_
  rw [← bf_two_div_sq_mul_natCast]
  exact mul_le_mul_of_nonneg_left (bw_re_normalizedTrace_imChain_sq_le hH hw₁ hw₂ A)
    (by positivity)

/-- **BZ**, final `|D|²` form: `(1/N) ∑_x |D(E_x)|² ≤ 2N⁻¹ (η₁⁻² + η₂⁻²) (Re T)²`. -/
theorem bf_avg_normSq_bracket_Z_le_sq (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) :
    1 / (N : ℝ) * ∑ x, Complex.normSq
        (bfZDiff A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) (hermBasis x)) ≤
      2 / (N : ℝ) * (|w₁.im|⁻¹ ^ 2 + |w₂.im|⁻¹ ^ 2) *
        (normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))).re ^ 2 := by
  refine (bf_avg_normSq_bracket_Z_le hH hw₁ hw₂ A).trans ?_
  rw [← bf_two_div_sq_mul_natCast]
  exact mul_le_mul_of_nonneg_left (bw_re_normalizedTrace_imChain_sq_le hH hw₁ hw₂ A)
    (by positivity)

/-!
## The `Z` drift identity
-/

theorem bf_two_mul_I_ne_zero : (2 * Complex.I) ≠ 0 :=
  mul_ne_zero two_ne_zero Complex.I_ne_zero

/-- `⟨L R M⟩ - ⟨L Rᴴ M⟩ = 2i ⟨L Im R M⟩` (any matrices). -/
theorem bf_normalizedTrace_sub_conjTranspose (L R M : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (L * R * M) - normalizedTrace (L * Rᴴ * M) =
      2 * Complex.I * normalizedTrace (L * External.CEH.imaginaryPart R * M) := by
  rw [External.CEH.imaginaryPart, Matrix.mul_smul, Matrix.smul_mul, normalizedTrace_smul,
    Matrix.mul_sub, Matrix.sub_mul, normalizedTrace_sub, ← mul_assoc,
    mul_inv_cancel₀ bf_two_mul_I_ne_zero, one_mul]

/-- `R = Rᴴ + 2i Im R` (any matrix). -/
theorem bf_eq_conjTranspose_add_imaginaryPart (R : Matrix (Fin N) (Fin N) ℂ) :
    R = Rᴴ + (2 * Complex.I) • External.CEH.imaginaryPart R := by
  rw [External.CEH.imaginaryPart, smul_smul, mul_inv_cancel₀ bf_two_mul_I_ne_zero, one_smul]
  abel

/-- `R² = (Im w)⁻¹ Im R + 2i Im R · R` (Ward). -/
theorem bf_resolvent_mul_self (hH : H.IsHermitian) {w : ℂ} (hw : w.im ≠ 0) :
    Phase1.resolvent H w * Phase1.resolvent H w =
      (w.im : ℂ)⁻¹ • External.CEH.imaginaryPart (Phase1.resolvent H w) +
        (2 * Complex.I) • (External.CEH.imaginaryPart (Phase1.resolvent H w) *
          Phase1.resolvent H w) := by
  have h := congrArg (· * Phase1.resolvent H w)
    (bf_eq_conjTranspose_add_imaginaryPart (Phase1.resolvent H w))
  rw [h, Matrix.add_mul, conjTranspose_mul_resolvent hH hw, Matrix.smul_mul]

/-- The scalar core of the drift identity. -/
theorem bf_zDrift_scalar (a₁ a₂ p q : ℂ) :
    -(1 / 4 : ℂ) * (a₁ * (2 * Complex.I * p) - conj a₁ * (2 * Complex.I * conj p) +
        a₂ * (2 * Complex.I * q) - conj a₂ * (2 * Complex.I * conj q)) =
      (((a₁ * p).im + (a₂ * q).im : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  · simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]

/-- `conj⟨X Y⟩ = ⟨Xᴴ Y⟩` for `Yᴴ = Y`. -/
theorem bf_conj_normalizedTrace_mul_herm_right (X : Matrix (Fin N) (Fin N) ℂ)
    {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Yᴴ = Y) :
    conj (normalizedTrace (X * Y)) = normalizedTrace (Xᴴ * Y) := by
  rw [← normalizedTrace_conjTranspose, conjTranspose_mul, hY, normalizedTrace_mul_comm]

/-- `conj⟨X Y⟩ = ⟨X Yᴴ⟩` for `Xᴴ = X`. -/
theorem bf_conj_normalizedTrace_mul_herm_left {X : Matrix (Fin N) (Fin N) ℂ} (hX : Xᴴ = X)
    (Y : Matrix (Fin N) (Fin N) ℂ) :
    conj (normalizedTrace (X * Y)) = normalizedTrace (X * Yᴴ) := by
  rw [← normalizedTrace_conjTranspose, conjTranspose_mul, hX, normalizedTrace_mul_comm]

/-- The drift identity for abstract matrices: `R₁, R₂` with `R_i² = u_i Im R_i + 2i Im R_i R_i`,
`Im R₁ R₁ = R₁ Im R₁` and `T = t` real. The adjoints `R_iᴴ` play the adjoint constellations. -/
theorem bf_zDrift_four_aux (A R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) (a₁ a₂ u₁ u₂ : ℂ) (t : ℝ)
    (h₁ : R₁ * R₁ = u₁ • External.CEH.imaginaryPart R₁ +
      (2 * Complex.I) • (External.CEH.imaginaryPart R₁ * R₁))
    (h₂ : R₂ * R₂ = u₂ • External.CEH.imaginaryPart R₂ +
      (2 * Complex.I) • (External.CEH.imaginaryPart R₂ * R₂))
    (hc₁ : External.CEH.imaginaryPart R₁ * R₁ = R₁ * External.CEH.imaginaryPart R₁)
    (hT : normalizedTrace (bwImChain A R₁ R₂) = t) :
    -(1 / 4 : ℂ) *
      ((a₁ * normalizedTrace (R₁ * R₁ * A * R₂ * Aᴴ) +
          a₂ * normalizedTrace (R₁ * A * R₂ * R₂ * Aᴴ)) -
        (a₁ * normalizedTrace (R₁ * R₁ * A * R₂ᴴ * Aᴴ) +
          conj a₂ * normalizedTrace (R₁ * A * R₂ᴴ * R₂ᴴ * Aᴴ)) -
        (conj a₁ * normalizedTrace (R₁ᴴ * R₁ᴴ * A * R₂ * Aᴴ) +
          a₂ * normalizedTrace (R₁ᴴ * A * R₂ * R₂ * Aᴴ)) +
        (conj a₁ * normalizedTrace (R₁ᴴ * R₁ᴴ * A * R₂ᴴ * Aᴴ) +
          conj a₂ * normalizedTrace (R₁ᴴ * A * R₂ᴴ * R₂ᴴ * Aᴴ))) =
      (((a₁ * (u₁ * t + 2 * Complex.I * normalizedTrace (bwImChain A R₁ R₂ * R₁))).im +
        (a₂ * (u₂ * t + 2 * Complex.I * normalizedTrace (External.CEH.imaginaryPart R₁ * A *
          External.CEH.imaginaryPart R₂ * R₂ * Aᴴ))).im : ℝ) : ℂ) := by
  have hp := bf_normalizedTrace_sub_conjTranspose (R₁ * R₁ * A) R₂ Aᴴ
  have hp' := bf_normalizedTrace_sub_conjTranspose (R₁ᴴ * R₁ᴴ * A) R₂ Aᴴ
  have hq : normalizedTrace (R₁ * A * R₂ * R₂ * Aᴴ) - normalizedTrace (R₁ᴴ * A * R₂ * R₂ * Aᴴ) =
      2 * Complex.I * normalizedTrace (External.CEH.imaginaryPart R₁ * A * R₂ * R₂ * Aᴴ) := by
    have h := bf_normalizedTrace_sub_conjTranspose 1 R₁ (A * R₂ * R₂ * Aᴴ)
    simpa only [Matrix.one_mul, Matrix.mul_assoc] using h
  have hq' : normalizedTrace (R₁ * A * R₂ᴴ * R₂ᴴ * Aᴴ) -
      normalizedTrace (R₁ᴴ * A * R₂ᴴ * R₂ᴴ * Aᴴ) =
      2 * Complex.I * normalizedTrace (External.CEH.imaginaryPart R₁ * A * R₂ᴴ * R₂ᴴ * Aᴴ) := by
    have h := bf_normalizedTrace_sub_conjTranspose 1 R₁ (A * R₂ᴴ * R₂ᴴ * Aᴴ)
    simpa only [Matrix.one_mul, Matrix.mul_assoc] using h
  have hpc : normalizedTrace (R₁ᴴ * R₁ᴴ * A * External.CEH.imaginaryPart R₂ * Aᴴ) =
      conj (normalizedTrace (R₁ * R₁ * A * External.CEH.imaginaryPart R₂ * Aᴴ)) := by
    have h := bf_conj_normalizedTrace_mul_herm_right (R₁ * R₁) (bf_conjTranspose_sandwich A R₂)
    rw [conjTranspose_mul] at h
    simp only [Matrix.mul_assoc] at h ⊢
    exact h.symm
  have hqc : normalizedTrace (External.CEH.imaginaryPart R₁ * A * R₂ᴴ * R₂ᴴ * Aᴴ) =
      conj (normalizedTrace (External.CEH.imaginaryPart R₁ * A * R₂ * R₂ * Aᴴ)) := by
    have h := bf_conj_normalizedTrace_mul_herm_left (bf_conjTranspose_imaginaryPart R₁)
      (A * R₂ * R₂ * Aᴴ)
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc] at h ⊢
    exact h.symm
  have hpv : normalizedTrace (R₁ * R₁ * A * External.CEH.imaginaryPart R₂ * Aᴴ) =
      u₁ * t + 2 * Complex.I * normalizedTrace (bwImChain A R₁ R₂ * R₁) := by
    rw [h₁]
    simp only [Matrix.add_mul, Matrix.smul_mul, normalizedTrace_add, normalizedTrace_smul]
    have e₂ : normalizedTrace (External.CEH.imaginaryPart R₁ * R₁ * A *
        External.CEH.imaginaryPart R₂ * Aᴴ) = normalizedTrace (bwImChain A R₁ R₂ * R₁) := by
      rw [hc₁, show R₁ * External.CEH.imaginaryPart R₁ * A * External.CEH.imaginaryPart R₂ * Aᴴ =
        R₁ * bwImChain A R₁ R₂ by simp only [bwImChain, Matrix.mul_assoc],
        normalizedTrace_mul_comm]
    rw [e₂, ← hT]
    rfl
  have hqv : normalizedTrace (External.CEH.imaginaryPart R₁ * A * R₂ * R₂ * Aᴴ) =
      u₂ * t + 2 * Complex.I * normalizedTrace (External.CEH.imaginaryPart R₁ * A *
        External.CEH.imaginaryPart R₂ * R₂ * Aᴴ) := by
    rw [show External.CEH.imaginaryPart R₁ * A * R₂ * R₂ * Aᴴ =
      External.CEH.imaginaryPart R₁ * A * (R₂ * R₂) * Aᴴ by simp only [Matrix.mul_assoc], h₂]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      normalizedTrace_add, normalizedTrace_smul]
    rw [← hT, show External.CEH.imaginaryPart R₁ * A * (External.CEH.imaginaryPart R₂ * R₂) * Aᴴ =
      External.CEH.imaginaryPart R₁ * A * External.CEH.imaginaryPart R₂ * R₂ * Aᴴ by
        simp only [Matrix.mul_assoc]]
    rfl
  have eL : ∀ x₁₁ y₁₁ x₁₂ y₁₂ x₂₁ y₂₁ x₂₂ y₂₂ : ℂ,
      -(1 / 4 : ℂ) * ((a₁ * x₁₁ + a₂ * y₁₁) - (a₁ * x₁₂ + conj a₂ * y₁₂) -
        (conj a₁ * x₂₁ + a₂ * y₂₁) + (conj a₁ * x₂₂ + conj a₂ * y₂₂)) =
      -(1 / 4 : ℂ) * (a₁ * (x₁₁ - x₁₂) - conj a₁ * (x₂₁ - x₂₂) + a₂ * (y₁₁ - y₂₁) -
        conj a₂ * (y₁₂ - y₂₂)) := by
    intros; ring
  rw [eL, hp, hp', hq, hq', hpc, hqc, bf_zDrift_scalar, hpv, hqv]

/-- `Im(a (u⁻¹ t + 2i z)) = (Im a / u) t + 2 Re(a z)` for real `u, t`. -/
theorem bf_im_mul_inv_add (a z : ℂ) (u t : ℝ) :
    (a * ((u : ℂ)⁻¹ * t + 2 * Complex.I * z)).im = a.im / u * t + 2 * (a * z).re := by
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- **Z drift identity**. Let `a₁, a₂ ∈ ℂ` be the drift coefficients `⟨R_i⟩ - m_i` (for the
adjoint resolvent `R(w̄_i)` the coefficient is `conj a_i`, `bf_normalizedTrace_resolvent_conj_sub`).
The combination `-¼ ∑_{a,b} ε_a ε_b` (`T = -¼ ∑ ε_a ε_b ⟨R₁^{(a)}AR₂^{(b)}Aᴴ⟩`,
`bf_normalizedTrace_imChain_eq_four`) of the `(⟨R_i⟩ - m_i)`-parts
`a₁^{(a)} ⟨(R₁^{(a)})² A R₂^{(b)} Aᴴ⟩ + a₂^{(b)} ⟨R₁^{(a)} A (R₂^{(b)})² Aᴴ⟩` of the drifts
(`B = Aᴴ`) equals the real number
`(Im a₁/Im w₁ + Im a₂/Im w₂) T + 2 Re(a₁ ⟨X R₁⟩) + 2 Re(a₂ ⟨Im R₁ A Im R₂ R₂ Aᴴ⟩)`,
`X = Im R₁ A Im R₂ Aᴴ`, `T = ⟨X⟩`. -/
theorem bf_zDrift_four (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0)
    (A : Matrix (Fin N) (Fin N) ℂ) (a₁ a₂ : ℂ) :
    -(1 / 4 : ℂ) *
      ((a₁ * normalizedTrace (Phase1.resolvent H w₁ * Phase1.resolvent H w₁ * A *
            Phase1.resolvent H w₂ * Aᴴ) +
          a₂ * normalizedTrace (Phase1.resolvent H w₁ * A * Phase1.resolvent H w₂ *
            Phase1.resolvent H w₂ * Aᴴ)) -
        (a₁ * normalizedTrace (Phase1.resolvent H w₁ * Phase1.resolvent H w₁ * A *
            Phase1.resolvent H (conj w₂) * Aᴴ) +
          conj a₂ * normalizedTrace (Phase1.resolvent H w₁ * A *
            Phase1.resolvent H (conj w₂) * Phase1.resolvent H (conj w₂) * Aᴴ)) -
        (conj a₁ * normalizedTrace (Phase1.resolvent H (conj w₁) *
            Phase1.resolvent H (conj w₁) * A * Phase1.resolvent H w₂ * Aᴴ) +
          a₂ * normalizedTrace (Phase1.resolvent H (conj w₁) * A * Phase1.resolvent H w₂ *
            Phase1.resolvent H w₂ * Aᴴ)) +
        (conj a₁ * normalizedTrace (Phase1.resolvent H (conj w₁) *
            Phase1.resolvent H (conj w₁) * A * Phase1.resolvent H (conj w₂) * Aᴴ) +
          conj a₂ * normalizedTrace (Phase1.resolvent H (conj w₁) * A *
            Phase1.resolvent H (conj w₂) * Phase1.resolvent H (conj w₂) * Aᴴ))) =
      (((a₁.im / w₁.im + a₂.im / w₂.im) *
          (normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂))).re +
        2 * (a₁ * normalizedTrace (bwImChain A (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) *
          Phase1.resolvent H w₁)).re +
        2 * (a₂ * normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁) * A *
          External.CEH.imaginaryPart (Phase1.resolvent H w₂) * Phase1.resolvent H w₂ * Aᴴ)).re :
          ℝ) : ℂ) := by
  rw [← resolvent_conjTranspose hH w₁, ← resolvent_conjTranspose hH w₂,
    bf_zDrift_four_aux A _ _ a₁ a₂ _ _ _ (bf_resolvent_mul_self hH hw₁)
      (bf_resolvent_mul_self hH hw₂) (bw_imaginaryPart_resolvent_mul_comm hH hw₁)
      (bw_normalizedTrace_imChain_eq_re hH hw₁ hw₂ A),
    bf_im_mul_inv_add, bf_im_mul_inv_add]
  congr 1
  ring

end Resolvents

end BlockBand.Native.CEH.ETH
