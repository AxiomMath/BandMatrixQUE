module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventDeterministicAssembly

/-!
# The fifth bound of CEH Lemma 5.6, deterministically

Cipolloni–Erdős–Henheik, Lemma 5.6, fifth display:

`max_* |⟨M̂_λ(z₁^{(*)}, A, z₂^{(*)}) A^*⟩| ≲ ρ₁ ρ₂ s₂²`,

for `θ(z₁,z₂) = 1` and a `(z₁,z₂)`-regular observable `A = Å`.  The source
(Appendix A.1) states this one follows directly from the definitions (5.12) and (5.10).  This module proves it with the explicit constant `2π²`,
uniformly in `N`, the deformation spectrum, `λ > 0`, the two spectral
parameters and the observable; there is no limit, no random matrix, and no
hypothesis beyond the source's `θ = 1`.

Conventions.  `M₁ = M(z₁⁺)` and `M₂ = M(z₂⁺)` are the upper-half-plane MDE
matrices (the source quantities only involve `zᵢ^±`, so `0 < Im zᵢ` is no
restriction), `ρᵢ = π⁻¹ ⟨Im Mᵢ⟩` with the normalized trace `⟨·⟩`, and
`s₂ = sTwo 1 λ M₁ M₂ A` is Definition 5.1 at `θ = 1`.

The proof uses only: cyclicity of the trace, the regularity identity
`⟨M₁ A M₂^*⟩ = 0`, `M - M^* = 2i Im M`, and commutation of the diagonal MDE
matrices with each other.  The algebraic core is
`⟨M̂ A^*⟩ = ⟨Im M₁ A Im M₂ A^*⟩ - (λ²/2) Re t₊₊`, with `t₊₊` the stable
correction, whose two trace factors are exactly the two factors in the `θ = 1`
term of `s₂²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate

/-!
## Trace algebra
-/

theorem NTrace_mul_comm' {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (X * Y) = NTrace (Y * X) := by
  unfold NTrace Conventions.normalizedTrace
  rw [Matrix.trace_mul_comm]

theorem NTrace_star' {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) :
    NTrace Xᴴ = star (NTrace X) :=
  PencilAdapter.NTrace_conjTranspose X

/-- `M - Mᴴ = 2 i Im M` in the sign convention of `matrixImaginaryPart`. -/
theorem sub_conjTranspose_eq_imaginaryPart {n : Type*}
    (M : Matrix n n ℂ) :
    M - Mᴴ = (2 * Complex.I) • matrixImaginaryPart M := by
  ext i j
  simp only [matrixImaginaryPart, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The fourfold polarization of `Im M₁ A Im M₂`. -/
theorem imaginaryPart_mul_mul_imaginaryPart {n : Type*} [Fintype n] [DecidableEq n]
    (M₁ A M₂ : Matrix n n ℂ) :
    matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ =
      (-(1 / 4 : ℂ)) •
        (M₁ * A * M₂ + M₁ᴴ * A * M₂ᴴ - M₁ * A * M₂ᴴ - M₁ᴴ * A * M₂) := by
  simp only [matrixImaginaryPart, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sub_mul, Matrix.mul_sub]
  have hc : (-Complex.I / 2) * (-Complex.I / 2) = -(1 / 4 : ℂ) := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← smul_sub, smul_smul, hc]
  congr 1
  abel

/-- Under the source regularity identity the `-+` mixed pairing also vanishes. -/
theorem NTrace_adj_mul_mul_adj_eq_zero_of_regular {N : ℕ}
    (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ)
    (hreg : NTrace (M₁ * A * M₂ᴴ) = 0) :
    NTrace (M₁ᴴ * M₂ * Aᴴ) = 0 := by
  have h : (M₁ᴴ * M₂ * Aᴴ) = (A * M₂ᴴ * M₁)ᴴ := by
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hc : NTrace (A * M₂ᴴ * M₁) = NTrace (M₁ * A * M₂ᴴ) := by
    rw [NTrace_mul_comm' (A * M₂ᴴ) M₁, ← Matrix.mul_assoc]
  rw [h, NTrace_star', hc, hreg]
  simp

/-- Regularity converts the stable word into an imaginary-part word. -/
theorem NTrace_word_eq_imaginaryPart_of_regular {N : ℕ}
    (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ)
    (hreg : NTrace (M₁ * A * M₂ᴴ) = 0) :
    NTrace (M₁ * A * M₂) =
      (2 * Complex.I) * NTrace (M₁ * A * matrixImaginaryPart M₂) := by
  have h : M₁ * A * M₂ = M₁ * A * M₂ᴴ + M₁ * A * (M₂ - M₂ᴴ) := by
    noncomm_ring
  rw [h, NTrace_add, hreg, sub_conjTranspose_eq_imaginaryPart, Matrix.mul_smul,
    NTrace_smul, zero_add]

/-- Regularity converts the stable pair-observable trace into an
imaginary-part trace. -/
theorem NTrace_pair_adj_eq_imaginaryPart_of_regular {N : ℕ}
    (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ)
    (hreg : NTrace (M₁ * A * M₂ᴴ) = 0) :
    NTrace (M₁ * M₂ * Aᴴ) =
      (2 * Complex.I) * NTrace (matrixImaginaryPart M₁ * M₂ * Aᴴ) := by
  have h0 := NTrace_adj_mul_mul_adj_eq_zero_of_regular M₁ A M₂ hreg
  have h : M₁ * M₂ * Aᴴ = M₁ᴴ * M₂ * Aᴴ + (M₁ - M₁ᴴ) * M₂ * Aᴴ := by
    noncomm_ring
  rw [h, NTrace_add, h0, sub_conjTranspose_eq_imaginaryPart, Matrix.smul_mul,
    Matrix.smul_mul, NTrace_smul, zero_add]

/-- The stable correction of the `++` constellation, paired with `A^*`. -/
def stableCorrectionPairing {N : ℕ} (lambda : ℂ)
    (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  NTrace (M₁ * A * M₂) /
      stabilityDenominator lambda (NTrace (M₁ * M₂)) * NTrace (M₁ * M₂ * Aᴴ)

/-- Trace of one constellation of the deterministic approximation against `A^*`. -/
theorem NTrace_twoResolventApprox_mul_adj {N : ℕ} (lambda : ℂ)
    (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (twoResolventApprox lambda M₁ A M₂ * Aᴴ) =
      NTrace (M₁ * A * M₂ * Aᴴ) +
        lambda ^ 2 * stableCorrectionPairing lambda M₁ A M₂ := by
  simp only [twoResolventApprox, Matrix.add_mul, Matrix.smul_mul]
  rw [NTrace_add, NTrace_smul]
  simp only [stableCorrectionPairing, NTrace, mul_assoc]

/-- The `--` stable correction is the complex conjugate of the `++` one
(trace cyclicity only). -/
theorem stableCorrectionPairing_adj_adj {N : ℕ} (lambda : ℝ)
    (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    stableCorrectionPairing (lambda : ℂ) M₁ᴴ A M₂ᴴ =
      star (stableCorrectionPairing (lambda : ℂ) M₁ A M₂) := by
  unfold stableCorrectionPairing stabilityDenominator
  have h₁ : NTrace (M₁ᴴ * A * M₂ᴴ) = star (NTrace (M₁ * M₂ * Aᴴ)) := by
    have e : (M₁ * M₂ * Aᴴ)ᴴ = A * M₂ᴴ * M₁ᴴ := by
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← NTrace_star', e, NTrace_mul_comm' (A * M₂ᴴ) M₁ᴴ, ← Matrix.mul_assoc]
  have h₂ : NTrace (M₁ᴴ * M₂ᴴ * Aᴴ) = star (NTrace (M₁ * A * M₂)) := by
    have e : (M₁ * A * M₂)ᴴ = M₂ᴴ * Aᴴ * M₁ᴴ := by
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← NTrace_star', e, NTrace_mul_comm' (M₂ᴴ * Aᴴ) M₁ᴴ, ← Matrix.mul_assoc]
  have h₃ : NTrace (M₁ᴴ * M₂ᴴ) = star (NTrace (M₁ * M₂)) := by
    rw [← NTrace_star', Matrix.conjTranspose_mul, NTrace_mul_comm' M₂ᴴ M₁ᴴ]
  rw [h₁, h₂, h₃]
  simp only [star_mul', star_div₀, star_sub, star_one, star_pow,
    Complex.star_def, Complex.conj_ofReal]
  ring

/-- Exact algebraic form of the fifth Lemma 5.6 quantity for a regular
observable: `⟨M̂ A^*⟩ = ⟨Im M₁ A Im M₂ A^*⟩ - (λ²/4) (t + t̄)`. -/
theorem NTrace_positiveDeterministicApprox_mul_adj_of_regular {N : ℕ}
    (lambda : ℝ) (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ)
    (hreg : NTrace (M₁ * A * M₂ᴴ) = 0) :
    NTrace (positiveDeterministicApprox (lambda : ℂ) M₁ A M₂ * Aᴴ) =
      NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ) -
        ((lambda : ℂ) ^ 2 / 4) *
          (stableCorrectionPairing (lambda : ℂ) M₁ A M₂ +
            star (stableCorrectionPairing (lambda : ℂ) M₁ A M₂)) := by
  have hpm : stableCorrectionPairing (lambda : ℂ) M₁ A M₂ᴴ = 0 := by
    simp [stableCorrectionPairing, hreg]
  have hmp : stableCorrectionPairing (lambda : ℂ) M₁ᴴ A M₂ = 0 := by
    simp [stableCorrectionPairing,
      NTrace_adj_mul_mul_adj_eq_zero_of_regular M₁ A M₂ hreg]
  have hmm := stableCorrectionPairing_adj_adj lambda M₁ A M₂
  have hmain :
      NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ) =
        (-(1 / 4 : ℂ)) *
          (NTrace (M₁ * A * M₂ * Aᴴ) + NTrace (M₁ᴴ * A * M₂ᴴ * Aᴴ) -
            NTrace (M₁ * A * M₂ᴴ * Aᴴ) - NTrace (M₁ᴴ * A * M₂ * Aᴴ)) := by
    rw [imaginaryPart_mul_mul_imaginaryPart, Matrix.smul_mul, NTrace_smul]
    simp only [Matrix.add_mul, Matrix.sub_mul, NTrace_add, NTrace_sub]
  simp only [positiveDeterministicApprox, deterministicConstellation,
    chooseAdjoint, Matrix.smul_mul, Matrix.add_mul, Matrix.sub_mul,
    NTrace_smul, NTrace_add, NTrace_sub, NTrace_twoResolventApprox_mul_adj]
  rw [hmain, hpm, hmp, hmm]
  ring

/-!
## Adjoint constellations of `M̂`
-/

theorem positiveDeterministicApprox_adjoint_left {N : ℕ} (lambda : ℂ)
    (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    positiveDeterministicApprox lambda M₁ᴴ A M₂ =
      -positiveDeterministicApprox lambda M₁ A M₂ := by
  simp only [positiveDeterministicApprox, deterministicConstellation, chooseAdjoint,
    Matrix.conjTranspose_conjTranspose]
  rw [← smul_neg]
  congr 1
  abel

theorem positiveDeterministicApprox_adjoint_right {N : ℕ} (lambda : ℂ)
    (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    positiveDeterministicApprox lambda M₁ A M₂ᴴ =
      -positiveDeterministicApprox lambda M₁ A M₂ := by
  simp only [positiveDeterministicApprox, deterministicConstellation, chooseAdjoint,
    Matrix.conjTranspose_conjTranspose]
  rw [← smul_neg]
  congr 1
  abel

/-- Every adjoint constellation of `M̂` has the same norm-relevant trace
against `A^*` up to sign. -/
theorem norm_NTrace_positiveDeterministicApprox_chooseAdjoint {N : ℕ}
    (lambda : ℂ) (c₁ c₂ : AdjointChoice) (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    ‖NTrace (positiveDeterministicApprox lambda (chooseAdjoint c₁ M₁) A
        (chooseAdjoint c₂ M₂) * Aᴴ)‖ =
      ‖NTrace (positiveDeterministicApprox lambda M₁ A M₂ * Aᴴ)‖ := by
  cases c₁ <;> cases c₂ <;>
    simp [chooseAdjoint, positiveDeterministicApprox_adjoint_left,
      positiveDeterministicApprox_adjoint_right, NTrace,
      Conventions.normalizedTrace, Matrix.trace_neg]

/-- Same statement for the plain trace of `M̂` (fourth bound). -/
theorem norm_NTrace_positiveDeterministicApprox_chooseAdjoint_trace {N : ℕ}
    (lambda : ℂ) (c₁ c₂ : AdjointChoice) (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    ‖NTrace (positiveDeterministicApprox lambda (chooseAdjoint c₁ M₁) A
        (chooseAdjoint c₂ M₂))‖ =
      ‖NTrace (positiveDeterministicApprox lambda M₁ A M₂)‖ := by
  cases c₁ <;> cases c₂ <;>
    simp [chooseAdjoint, positiveDeterministicApprox_adjoint_left,
      positiveDeterministicApprox_adjoint_right, NTrace,
      Conventions.normalizedTrace, Matrix.trace_neg]

/-!
## Diagonal matrices
-/

theorem matrixImaginaryPart_diagonal {N : ℕ} (m : Fin N → ℂ) :
    matrixImaginaryPart (Matrix.diagonal m) =
      Matrix.diagonal (fun i => ((m i).im : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [matrixImaginaryPart, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    ring
  · simp [matrixImaginaryPart, Matrix.diagonal_apply_ne _ hij]

theorem NTrace_diagonal_ofReal {N : ℕ} (r : Fin N → ℝ) :
    NTrace (Matrix.diagonal (fun i => ((r i : ℝ) : ℂ))) =
      (((N : ℝ)⁻¹ * ∑ i, r i : ℝ) : ℂ) := by
  unfold NTrace Conventions.normalizedTrace
  rw [Matrix.trace_diagonal]
  push_cast
  rfl

/-- Weighted Hilbert–Schmidt pairing with two real diagonal weights. -/
theorem NTrace_diagonal_mul_mul_diagonal_mul_adj {N : ℕ}
    (d₁ d₂ : Fin N → ℝ) (A : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (Matrix.diagonal (fun i => ((d₁ i : ℝ) : ℂ)) * A *
        Matrix.diagonal (fun i => ((d₂ i : ℝ) : ℂ)) * Aᴴ) =
      (((N : ℝ)⁻¹ * ∑ i, ∑ j, d₁ i * d₂ j * ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
  have h : Matrix.diagonal (fun i => ((d₁ i : ℝ) : ℂ)) * A *
      Matrix.diagonal (fun i => ((d₂ i : ℝ) : ℂ)) =
      Matrix.of (fun i j => (d₁ i : ℂ) * A i j * (d₂ j : ℂ)) := by
    ext i j
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [h]
  unfold NTrace Conventions.normalizedTrace
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply,
    Matrix.conjTranspose_apply]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show (d₁ i : ℂ) * A i j * (d₂ j : ℂ) * star (A i j) =
      (d₁ i : ℂ) * (d₂ j : ℂ) * (A i j * (starRingEnd ℂ) (A i j)) by
    rw [Complex.star_def]; ring]
  rw [Complex.mul_conj', ← Complex.ofReal_pow]

/-- Diagonal matrices commute. -/
theorem diagonal_mul_comm {N : ℕ} (a b : Fin N → ℂ) :
    Matrix.diagonal a * Matrix.diagonal b = Matrix.diagonal b * Matrix.diagonal a := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  ring

/-!
## The generic diagonal bound
-/

/-- **Fifth bound of CEH Lemma 5.6, diagonal form.**  For diagonal `M₁, M₂`
with positive imaginary parts and an observable with `⟨M₁ A M₂^*⟩ = 0`,
`|⟨M̂(M₁,A,M₂) A^*⟩| ≤ 2 ⟨Im M₁⟩ ⟨Im M₂⟩ s₂²`, where `s₂²` is the
`θ = 1` CEH control `sTwoSq 1`. -/
theorem norm_NTrace_positiveDeterministicApprox_mul_adj_le_diagonal
    {N : ℕ} (hN : 0 < N) (lambda : ℝ) (m n : Fin N → ℂ)
    (hm : ∀ i, 0 < (m i).im) (hn : ∀ i, 0 < (n i).im)
    (A : Matrix (Fin N) (Fin N) ℂ)
    (hreg : NTrace (Matrix.diagonal m * A * (Matrix.diagonal n)ᴴ) = 0) :
    ‖NTrace (positiveDeterministicApprox (lambda : ℂ) (Matrix.diagonal m) A
        (Matrix.diagonal n) * Aᴴ)‖ ≤
      2 * (NTrace (matrixImaginaryPart (Matrix.diagonal m))).re *
        (NTrace (matrixImaginaryPart (Matrix.diagonal n))).re *
        sTwoSq 1 (lambda : ℂ) (Matrix.diagonal m) (Matrix.diagonal n) A := by
  set M₁ := Matrix.diagonal m with hM₁
  set M₂ := Matrix.diagonal n with hM₂
  have hNpos : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hN)
  have hne : (Finset.univ : Finset (Fin N)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩
  set r₁ : ℝ := (N : ℝ)⁻¹ * ∑ i, (m i).im with hr₁def
  set r₂ : ℝ := (N : ℝ)⁻¹ * ∑ i, (n i).im with hr₂def
  have hr₁ : 0 < r₁ := mul_pos hNpos (Finset.sum_pos (fun i _ => hm i) hne)
  have hr₂ : 0 < r₂ := mul_pos hNpos (Finset.sum_pos (fun i _ => hn i) hne)
  have hIm₁ : matrixImaginaryPart M₁ = Matrix.diagonal (fun i => (((m i).im : ℝ) : ℂ)) :=
    matrixImaginaryPart_diagonal m
  have hIm₂ : matrixImaginaryPart M₂ = Matrix.diagonal (fun i => (((n i).im : ℝ) : ℂ)) :=
    matrixImaginaryPart_diagonal n
  have hI₁ : NTrace (matrixImaginaryPart M₁) = (r₁ : ℂ) := by
    rw [hIm₁, NTrace_diagonal_ofReal]
  have hI₂ : NTrace (matrixImaginaryPart M₂) = (r₂ : ℂ) := by
    rw [hIm₂, NTrace_diagonal_ofReal]
  set p : ℝ := (N : ℝ)⁻¹ * ∑ i, ∑ j, (m i).im * (n j).im * ‖A i j‖ ^ 2 with hpdef
  have hp : 0 ≤ p := by
    apply mul_nonneg hNpos.le
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    exact mul_nonneg (mul_nonneg (hm i).le (hn j).le) (sq_nonneg _)
  have hP : NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ) =
      (p : ℂ) := by
    rw [hIm₁, hIm₂, NTrace_diagonal_mul_mul_diagonal_mul_adj]
  -- the CEH control `s₂²`
  set X := NTrace (M₁ * A * matrixImaginaryPart M₂) with hX
  set Y := NTrace (matrixImaginaryPart M₁ * M₂ * Aᴴ) with hY
  set β := stabilityDenominator (lambda : ℂ) (NTrace (M₁ * M₂)) with hβ
  have hΓ₁ : gammaMatrix M₁ = ((r₁ : ℂ))⁻¹ • matrixImaginaryPart M₁ := by
    rw [gammaMatrix, hI₁]
  have hΓ₂ : gammaMatrix M₂ = ((r₂ : ℂ))⁻¹ • matrixImaginaryPart M₂ := by
    rw [gammaMatrix, hI₂]
  have hbase : (NTrace (gammaMatrix M₁ * A * gammaMatrix M₂ * Aᴴ)).re =
      p / (r₁ * r₂) := by
    rw [hΓ₁, hΓ₂]
    simp only [Matrix.smul_mul, Matrix.mul_smul, NTrace_smul]
    rw [hP]
    rw [show ((r₂ : ℂ))⁻¹ * (((r₁ : ℂ))⁻¹ * (p : ℂ)) = ((p / (r₁ * r₂) : ℝ) : ℂ) by
      push_cast; field_simp]
    exact Complex.ofReal_re _
  have hcomm : NTrace (gammaMatrix M₁ * Aᴴ * M₂) = ((r₁ : ℂ))⁻¹ * Y := by
    rw [hΓ₁, Matrix.smul_mul, Matrix.smul_mul, NTrace_smul]
    congr 1
    have hc : M₂ * matrixImaginaryPart M₁ = matrixImaginaryPart M₁ * M₂ := by
      rw [hIm₁, hM₂]
      exact diagonal_mul_comm _ _
    rw [NTrace_mul_comm' (matrixImaginaryPart M₁ * Aᴴ) M₂, ← Matrix.mul_assoc, hc]
  have hXΓ : NTrace (M₁ * A * gammaMatrix M₂) = ((r₂ : ℂ))⁻¹ * X := by
    rw [hΓ₂, Matrix.mul_smul, NTrace_smul]
  have hstable :
      ‖NTrace (M₁ * A * gammaMatrix M₂) * NTrace (gammaMatrix M₁ * Aᴴ * M₂) / β‖ =
        ‖X‖ * ‖Y‖ / ‖β‖ / (r₁ * r₂) := by
    rw [hXΓ, hcomm, norm_div, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hr₁.le,
      Real.norm_of_nonneg hr₂.le]
    field_simp
  have hs : sTwoSq 1 (lambda : ℂ) M₁ M₂ A =
      p / (r₁ * r₂) + lambda ^ 2 * (‖X‖ * ‖Y‖ / ‖β‖ / (r₁ * r₂)) := by
    simp only [sTwoSq]
    rw [hbase, hstable]
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- the algebraic identity
  rw [NTrace_positiveDeterministicApprox_mul_adj_of_regular lambda M₁ A M₂ hreg, hP]
  have ht : stableCorrectionPairing (lambda : ℂ) M₁ A M₂ =
      (2 * Complex.I) * X / β * ((2 * Complex.I) * Y) := by
    unfold stableCorrectionPairing
    rw [NTrace_word_eq_imaginaryPart_of_regular M₁ A M₂ hreg,
      NTrace_pair_adj_eq_imaginaryPart_of_regular M₁ A M₂ hreg]
  have htn : ‖stableCorrectionPairing (lambda : ℂ) M₁ A M₂‖ = 4 * (‖X‖ * ‖Y‖ / ‖β‖) := by
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [ht]
    simp only [norm_mul, norm_div, Complex.norm_I, h2]
    ring
  set t := stableCorrectionPairing (lambda : ℂ) M₁ A M₂
  have hlam : ‖((lambda : ℂ) ^ 2 / 4)‖ = lambda ^ 2 / 4 := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    norm_num
  have hXYβ : 0 ≤ ‖X‖ * ‖Y‖ / ‖β‖ := by positivity
  calc
    ‖(p : ℂ) - (lambda : ℂ) ^ 2 / 4 * (t + star t)‖ ≤
        ‖(p : ℂ)‖ + ‖(lambda : ℂ) ^ 2 / 4 * (t + star t)‖ := norm_sub_le _ _
    _ ≤ p + lambda ^ 2 / 4 * (‖t‖ + ‖t‖) := by
        rw [Complex.norm_real, Real.norm_of_nonneg hp, norm_mul, hlam]
        gcongr
        exact (norm_add_le _ _).trans (by rw [norm_star])
    _ = p + 2 * lambda ^ 2 * (‖X‖ * ‖Y‖ / ‖β‖) := by rw [htn]; ring
    _ ≤ 2 * p + 2 * lambda ^ 2 * (‖X‖ * ‖Y‖ / ‖β‖) := by linarith
    _ = 2 * r₁ * r₂ * sTwoSq 1 (lambda : ℂ) M₁ M₂ A := by
        rw [hs]
        field_simp
    _ = _ := by rw [hI₁, hI₂, Complex.ofReal_re, Complex.ofReal_re]

/-- The `θ = 1` CEH control is nonnegative for diagonal Herglotz data
and a regular observable (a by-product of the diagonal fifth bound). -/
theorem sTwoSq_nonneg_of_diagonal
    {N : ℕ} (hN : 0 < N) (lambda : ℝ) (m n : Fin N → ℂ)
    (hm : ∀ i, 0 < (m i).im) (hn : ∀ i, 0 < (n i).im)
    (A : Matrix (Fin N) (Fin N) ℂ)
    (hreg : NTrace (Matrix.diagonal m * A * (Matrix.diagonal n)ᴴ) = 0) :
    0 ≤ sTwoSq 1 (lambda : ℂ) (Matrix.diagonal m) (Matrix.diagonal n) A := by
  have h := norm_NTrace_positiveDeterministicApprox_mul_adj_le_diagonal hN lambda
    m n hm hn A hreg
  rw [matrixImaginaryPart_diagonal, matrixImaginaryPart_diagonal,
    NTrace_diagonal_ofReal, NTrace_diagonal_ofReal, Complex.ofReal_re,
    Complex.ofReal_re] at h
  have hNpos : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hN)
  have hne : (Finset.univ : Finset (Fin N)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩
  have hr₁ : 0 < (N : ℝ)⁻¹ * ∑ i, (m i).im :=
    mul_pos hNpos (Finset.sum_pos (fun i _ => hm i) hne)
  have hr₂ : 0 < (N : ℝ)⁻¹ * ∑ i, (n i).im :=
    mul_pos hNpos (Finset.sum_pos (fun i _ => hn i) hne)
  have h0 := (norm_nonneg _).trans h
  by_contra hneg
  replace hneg := lt_of_not_ge hneg
  have : 2 * ((N : ℝ)⁻¹ * ∑ i, (m i).im) * ((N : ℝ)⁻¹ * ∑ i, (n i).im) *
      sTwoSq 1 (lambda : ℂ) (Matrix.diagonal m) (Matrix.diagonal n) A < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hneg
  linarith

/-!
## Source-shaped fifth bound on the CEH MDE branch
-/

/-- A `θ = 1` cutoff value forces a nonzero mixed MDE pairing. -/
theorem NTrace_pair_ne_zero_of_regularizationCoefficient_eq_one {N : ℕ}
    (lambda : ℂ) (M₁plus M₂minus : Matrix (Fin N) (Fin N) ℂ)
    (h : regularizationCoefficient lambda M₁plus M₂minus = 1) :
    NTrace (M₁plus * M₂minus) ≠ 0 := by
  intro hzero
  unfold regularizationCoefficient at h
  rw [hzero, mul_zero, Complex.zero_re, zero_sub] at h
  rw [cehTheta_of_neg (by norm_num)] at h
  norm_num at h

/-- **CEH Lemma 5.6, fifth bound** (last line of (5.13)), with explicit constant `2π²`.

Data: `N > 0`, real deformation spectrum `f` (the eigenvalues of `H₀`), `λ > 0`,
spectral parameters `z₁, z₂` with `0 < Im zᵢ` (i.e. `zᵢ = zᵢ⁺`), the
upper-half-plane MDE matrices `Mᵢ = M_λ(zᵢ)` from the unconditional scalar
branch, an arbitrary source matrix `J` and its CEH regularization
`A = Å^{z₁,z₂} = J - ⟨M₁ J M₂^*⟩/⟨M₁ M₂^*⟩` (Definition 5.1 with `θ = 1`).
Hypothesis: the source cutoff `θ(z₁,z₂) = 1`.  Conclusion, for every adjoint
constellation:
`|⟨M̂_λ(z₁^{(*)}, A, z₂^{(*)}) A^*⟩| ≤ 2π² ρ₁ ρ₂ s₂²`, `ρᵢ = π⁻¹ ⟨Im Mᵢ⟩`,
`s₂ = s₂(z₁,z₂;A)`.  All quantifiers are pointwise; there is no limit. -/
theorem lemma56_fifth_bound {N : ℕ} (hN : 0 < N)
    (f : CEHNative.BlockBand.CEH.DeformationSpectrum N)
    (lambda : ℝ) (hlambda : 0 < lambda)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (J : Matrix (Fin N) (Fin N) ℂ) (c₁ c₂ : AdjointChoice) :
    let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
    let M₁ := PencilAdapter.mdeMatrix f lambda z₁
      (CEHNative.BlockBand.CEH.upperBranch hN f hs z₁)
    let M₂ := PencilAdapter.mdeMatrix f lambda z₂
      (CEHNative.BlockBand.CEH.upperBranch hN f hs z₂)
    let A := regularizedObservable 1 M₁ M₂ᴴ J
    let rho₁ := (NTrace (matrixImaginaryPart M₁)).re / Real.pi
    let rho₂ := (NTrace (matrixImaginaryPart M₂)).re / Real.pi
    regularizationCoefficient (lambda : ℂ) M₁ M₂ᴴ = 1 →
    ‖NTrace (positiveDeterministicApprox (lambda : ℂ) (chooseAdjoint c₁ M₁) A
        (chooseAdjoint c₂ M₂) * Aᴴ)‖ ≤
      2 * Real.pi ^ 2 * rho₁ * rho₂ * sTwo 1 (lambda : ℂ) M₁ M₂ A ^ 2 := by
  intro hs M₁ M₂ A rho₁ rho₂ htheta
  set m₁ := CEHNative.BlockBand.CEH.upperBranch hN f hs z₁
  set m₂ := CEHNative.BlockBand.CEH.upperBranch hN f hs z₂
  have hm₁ := CEHNative.BlockBand.CEH.upperBranch_isSolution hN f hs hz₁
  have hm₂ := CEHNative.BlockBand.CEH.upperBranch_isSolution hN f hs hz₂
  have hpos : ∀ {z m : ℂ}, 0 < z.im →
      CEHNative.BlockBand.CEH.IsSolution f (lambda ^ 2) z m →
      ∀ i, 0 < (CEHNative.BlockBand.CEH.entry f (lambda ^ 2) z m i).im := by
    intro z m hz hm i
    apply CEHNative.BlockBand.CEH.entry_im_pos
    unfold CEHNative.BlockBand.CEH.effectiveHeight
    exact add_pos_of_pos_of_nonneg hz (mul_nonneg (sq_nonneg _) hm.2.le)
  have hreg : NTrace (M₁ * A * M₂ᴴ) = 0 :=
    regularizedObservable_trace_zero M₁ M₂ᴴ J
      (NTrace_pair_ne_zero_of_regularizationCoefficient_eq_one _ _ _ htheta)
  have hmain := norm_NTrace_positiveDeterministicApprox_mul_adj_le_diagonal hN lambda
    _ _ (hpos hz₁ hm₁) (hpos hz₂ hm₂) A hreg
  have hnonneg := sTwoSq_nonneg_of_diagonal hN lambda
    _ _ (hpos hz₁ hm₁) (hpos hz₂ hm₂) A hreg
  rw [norm_NTrace_positiveDeterministicApprox_chooseAdjoint]
  change ‖NTrace (positiveDeterministicApprox (lambda : ℂ) M₁ A M₂ * Aᴴ)‖ ≤ _
  have hsq : sTwo 1 (lambda : ℂ) M₁ M₂ A ^ 2 = sTwoSq 1 (lambda : ℂ) M₁ M₂ A :=
    Real.sq_sqrt hnonneg
  rw [hsq]
  refine hmain.trans (le_of_eq ?_)
  simp only [rho₁, rho₂]
  field_simp
  rfl

end CEHNative.BlockBand.External.CEH
