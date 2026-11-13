module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ETHResolventRealization

/-!
# Spectral expansion of the positive two-resolvent observable

This module joins the resolvent realization of the positive spectral kernel with the
finite projector calculation used in the CEH ETH extraction.  It gives the
normalized trace of the two imaginary resolvents of one Hermitian realization as the
positive double spectral sum of squared matrix elements.  No probability estimate or
local law is used.

Source: Cipolloni–Erdős–Henheik, proof of Theorem 2.5 following Theorem 4.2,
with resolvent convention `(A-zI)⁻¹` and normalized trace `N⁻¹ Tr`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix
open scoped BigOperators ComplexConjugate

/-- Exact double spectral expansion for the positive two-resolvent chain. -/
theorem normalizedTrace_matrixImaginaryPart_resolvent_mul
    {N : ℕ} {H : LocalETHMatrix N} {lam : Fin N → ℝ}
    {u : Fin N → Fin N → ℂ}
    (hfamily : IsLocalETHOrthonormalEigenFamily H lam u)
    (x₁ x₂ : ℝ) {eta₁ eta₂ : ℝ} (heta₁ : 0 < eta₁) (heta₂ : 0 < eta₂)
    (A : LocalETHMatrix N) :
    NTrace
        (matrixImaginaryPart
              ((H - ((x₁ : ℂ) + (eta₁ : ℂ) * Complex.I) •
                (1 : LocalETHMatrix N))⁻¹) * A *
          matrixImaginaryPart
              ((H - ((x₂ : ℂ) + (eta₂ : ℂ) * Complex.I) •
                (1 : LocalETHMatrix N))⁻¹) * Aᴴ) =
      ((N : ℂ)⁻¹) * ∑ i : Fin N, ∑ j : Fin N,
        ((cehSpectralWeight (lam i) x₁ eta₁ *
          cehSpectralWeight (lam j) x₂ eta₂ : ℝ) : ℂ) *
          spectralMatrixElement u A i j * star (spectralMatrixElement u A i j) := by
  rw [← spectralImaginaryKernel_eq_matrixImaginaryPart_resolvent
      hfamily x₁ heta₁,
    ← spectralImaginaryKernel_eq_matrixImaginaryPart_resolvent
      hfamily x₂ heta₂]
  exact normalizedTrace_spectralImaginaryKernel_mul lam u x₁ eta₁ x₂ eta₂ A

end CEHNative.BlockBand.External.CEH

namespace CEHNative.BlockBand.External.CEH

open Matrix
open scoped BigOperators ComplexConjugate

/-- Real-valued form of the double spectral expansion. -/
theorem re_normalizedTrace_spectralImaginaryKernel_mul
    {N : ℕ} (lam : Fin N → ℝ) (u : Fin N → Fin N → ℂ)
    (x₁ eta₁ x₂ eta₂ : ℝ) (A : LocalETHMatrix N) :
    (NTrace (spectralImaginaryKernel lam u x₁ eta₁ * A *
        spectralImaginaryKernel lam u x₂ eta₂ * Aᴴ)).re =
      (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
        cehSpectralWeight (lam i) x₁ eta₁ *
          cehSpectralWeight (lam j) x₂ eta₂ *
          ‖spectralMatrixElement u A i j‖ ^ 2 := by
  rw [normalizedTrace_spectralImaginaryKernel_mul]
  have hsum :
      (∑ i : Fin N, ∑ j : Fin N,
        ((cehSpectralWeight (lam i) x₁ eta₁ *
          cehSpectralWeight (lam j) x₂ eta₂ : ℝ) : ℂ) *
          spectralMatrixElement u A i j * star (spectralMatrixElement u A i j)) =
      ((∑ i : Fin N, ∑ j : Fin N,
        cehSpectralWeight (lam i) x₁ eta₁ *
          cehSpectralWeight (lam j) x₂ eta₂ *
          ‖spectralMatrixElement u A i j‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    calc
      ((cehSpectralWeight (lam i) x₁ eta₁ : ℝ) : ℂ) *
            ((cehSpectralWeight (lam j) x₂ eta₂ : ℝ) : ℂ) *
            spectralMatrixElement u A i j * star (spectralMatrixElement u A i j) =
          ((cehSpectralWeight (lam i) x₁ eta₁ : ℝ) : ℂ) *
            ((cehSpectralWeight (lam j) x₂ eta₂ : ℝ) : ℂ) *
            (spectralMatrixElement u A i j * star (spectralMatrixElement u A i j)) := by ring
      _ = ((cehSpectralWeight (lam i) x₁ eta₁ : ℝ) : ℂ) *
            ((cehSpectralWeight (lam j) x₂ eta₂ : ℝ) : ℂ) *
            ((‖spectralMatrixElement u A i j‖ ^ 2 : ℝ) : ℂ) := by
          apply congrArg (fun t : ℂ =>
            ((cehSpectralWeight (lam i) x₁ eta₁ : ℝ) : ℂ) *
              ((cehSpectralWeight (lam j) x₂ eta₂ : ℝ) : ℂ) * t)
          change spectralMatrixElement u A i j *
              conj (spectralMatrixElement u A i j) =
            ((‖spectralMatrixElement u A i j‖ ^ 2 : ℝ) : ℂ)
          calc
            spectralMatrixElement u A i j *
                conj (spectralMatrixElement u A i j) =
                (‖spectralMatrixElement u A i j‖ : ℂ) ^ 2 :=
              Complex.mul_conj' (spectralMatrixElement u A i j)
            _ = ((‖spectralMatrixElement u A i j‖ ^ 2 : ℝ) : ℂ) := by
              norm_cast
      _ = _ := by norm_cast
  rw [hsum]
  change
    (((((N : ℝ) : ℂ)⁻¹) *
      ((∑ i : Fin N, ∑ j : Fin N,
        cehSpectralWeight (lam i) x₁ eta₁ *
          cehSpectralWeight (lam j) x₂ eta₂ *
          ‖spectralMatrixElement u A i j‖ ^ 2 : ℝ) : ℂ)).re) =
      (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
        cehSpectralWeight (lam i) x₁ eta₁ *
          cehSpectralWeight (lam j) x₂ eta₂ *
          ‖spectralMatrixElement u A i j‖ ^ 2
  rw [← Complex.ofReal_inv]
  norm_cast

/-- Every ordered spectral pair contributes at most the full positive
normalized two-resolvent trace. -/
theorem spectralPair_le_re_normalizedTrace_kernel
    {N : ℕ} (hN : 0 < N) (lam : Fin N → ℝ)
    (u : Fin N → Fin N → ℂ) (x₁ x₂ : ℝ)
    {eta₁ eta₂ : ℝ} (heta₁ : 0 ≤ eta₁) (heta₂ : 0 ≤ eta₂)
    (A : LocalETHMatrix N) (i j : Fin N) :
    (N : ℝ)⁻¹ * cehSpectralWeight (lam i) x₁ eta₁ *
          cehSpectralWeight (lam j) x₂ eta₂ *
          ‖spectralMatrixElement u A i j‖ ^ 2 ≤
      (NTrace (spectralImaginaryKernel lam u x₁ eta₁ * A *
        spectralImaginaryKernel lam u x₂ eta₂ * Aᴴ)).re := by
  rw [re_normalizedTrace_spectralImaginaryKernel_mul]
  have hNinv : 0 ≤ (N : ℝ)⁻¹ := by positivity
  rw [show (N : ℝ)⁻¹ * cehSpectralWeight (lam i) x₁ eta₁ *
      cehSpectralWeight (lam j) x₂ eta₂ *
      ‖spectralMatrixElement u A i j‖ ^ 2 =
      (N : ℝ)⁻¹ * (cehSpectralWeight (lam i) x₁ eta₁ *
      cehSpectralWeight (lam j) x₂ eta₂ *
      ‖spectralMatrixElement u A i j‖ ^ 2) by ring]
  apply mul_le_mul_of_nonneg_left _ hNinv
  have hterm_nonneg (a b : Fin N) :
      0 ≤ cehSpectralWeight (lam a) x₁ eta₁ *
          cehSpectralWeight (lam b) x₂ eta₂ *
          ‖spectralMatrixElement u A a b‖ ^ 2 := by
    exact mul_nonneg
      (mul_nonneg (cehSpectralWeight_nonneg _ _ heta₁)
        (cehSpectralWeight_nonneg _ _ heta₂)) (sq_nonneg _)
  calc
    cehSpectralWeight (lam i) x₁ eta₁ *
          cehSpectralWeight (lam j) x₂ eta₂ *
          ‖spectralMatrixElement u A i j‖ ^ 2 ≤
        ∑ b : Fin N,
          cehSpectralWeight (lam i) x₁ eta₁ *
            cehSpectralWeight (lam b) x₂ eta₂ *
            ‖spectralMatrixElement u A i b‖ ^ 2 :=
      Finset.single_le_sum (fun b _ => hterm_nonneg i b) (Finset.mem_univ j)
    _ ≤ ∑ a : Fin N, ∑ b : Fin N,
          cehSpectralWeight (lam a) x₁ eta₁ *
            cehSpectralWeight (lam b) x₂ eta₂ *
            ‖spectralMatrixElement u A a b‖ ^ 2 :=
      Finset.single_le_sum
        (fun a _ => Finset.sum_nonneg fun b _ => hterm_nonneg a b)
        (Finset.mem_univ i)

end CEHNative.BlockBand.External.CEH
