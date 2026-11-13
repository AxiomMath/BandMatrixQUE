module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.Interface
public import BlockBand.Native.CEH.BlockBand.External.CEH.MDEQuantitative
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ETHDeterministicExtraction

/-!
# CEH regularized observable and the published ETH center

This module identifies the scalar removed by CEH's theta-one regularization at
a coincident spectral parameter with the diagonal center in the published ETH
interface.  The proof is the exact matrix Ward identity and trace cyclicity.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix
open CEHNative.BlockBand
open CEHNative.BlockBand.CEH
open scoped ComplexConjugate

/-- For the Hermitian MDE branch in the upper half-plane, the scalar quotient
removed by the theta-one regularized observable is exactly `⟨Γ A⟩`. -/
theorem normalizedTrace_mde_word_div_eq_normalizedTrace_gamma
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im)
    (A : LocalETHMatrix N) :
    NTrace (hermitianMDEBranch hF hs z * A *
        (hermitianMDEBranch hF hs z)ᴴ) /
      NTrace (hermitianMDEBranch hF hs z *
        (hermitianMDEBranch hF hs z)ᴴ) =
      NTrace (localETHGamma (hermitianMDEBranch hF hs z) * A) := by
  let M := hermitianMDEBranch hF hs z
  let m := upperBranch hN (hermitianSpectrum hF) hs z
  let h : ℝ := effectiveHeight s z m
  have hmpos : 0 < m.im :=
    (upperBranch_isSolution hN (hermitianSpectrum hF) hs hz).2
  have hhpos : 0 < h := by
    dsimp [h, m, effectiveHeight]
    positivity
  have hward : localETHImPart M = (h : ℂ) • (star M * M) := by
    simpa [M, m, h] using imPart_hermitianMDEBranch_eq hF hN hs hz
  have htraceWard : ((m.im : ℝ) : ℂ) = (h : ℂ) * NTrace (star M * M) := by
    simpa [M, m, h] using matrix_imaginaryPart_Ward_identity hF hN hs hz
  have hden_ne : NTrace (star M * M) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at htraceWard
    exact hmpos.ne' (Complex.ofReal_injective (by simpa using htraceWard))
  have hcycle_num : NTrace (M * A * star M) = NTrace ((star M * M) * A) := by
    unfold NTrace CEHNative.BlockBand.Conventions.normalizedTrace
    rw [Matrix.trace_mul_cycle]
  have hcycle_den : NTrace (M * star M) = NTrace (star M * M) := by
    unfold NTrace CEHNative.BlockBand.Conventions.normalizedTrace
    rw [Matrix.trace_mul_comm]
  rw [show hermitianMDEBranch hF hs z = M by rfl]
  rw [show (M)ᴴ = star M by rfl, hcycle_num, hcycle_den]
  rw [localETHGamma, normalizedTrace_hermitianMDEBranch hF hN hs hz.ne',
    hermitianMDEMean_of_im_pos hF hN hs hz]
  change NTrace ((star M * M) * A) / NTrace (star M * M) =
    NTrace (((((m.im : ℝ) : ℂ))⁻¹ • localETHImPart M) * A)
  rw [hward]
  rw [Matrix.smul_mul, NTrace_smul]
  have hfactor : (((m.im : ℝ) : ℂ))⁻¹ * (h : ℂ) =
      (NTrace (star M * M))⁻¹ := by
    rw [htraceWard]
    field_simp [show (h : ℂ) ≠ 0 by exact_mod_cast hhpos.ne', hden_ne]
  rw [Matrix.smul_mul, NTrace_smul, ← mul_assoc]
  rw [hfactor]
  field_simp [hden_ne]

/-- At coincident MDE arguments, the interface regularization subtracts
exactly the published diagonal ETH center. -/
theorem regObs_mde_self_eq_sub_center
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im)
    (A : LocalETHMatrix N) :
    regObs (hermitianMDEBranch hF hs z) (hermitianMDEBranch hF hs z) A =
      A - NTrace (localETHGamma (hermitianMDEBranch hF hs z) * A) •
        (1 : LocalETHMatrix N) := by
  unfold regObs
  rw [normalizedTrace_mde_word_div_eq_normalizedTrace_gamma
    hF hN hs hz A]

/-- Matrix elements of the theta-one regularized observable differ from the
original observable only by the removed scalar on the diagonal. -/
theorem spectralMatrixElement_regObs
    {N : ℕ} {H : LocalETHMatrix N} {lam : Fin N → ℝ}
    {u : Fin N → Fin N → ℂ}
    (hfamily : IsLocalETHOrthonormalEigenFamily H lam u)
    (Mi Mj A : LocalETHMatrix N) (i j : Fin N) :
    spectralMatrixElement u (regObs Mi Mj A) i j =
      spectralMatrixElement u A i j -
        (NTrace (Mi * A * Mjᴴ) / NTrace (Mi * Mjᴴ)) *
          (if i = j then 1 else 0) := by
  unfold spectralMatrixElement regObs
  rw [Matrix.vecMul_sub, sub_dotProduct]
  congr 1
  rw [Matrix.vecMul_smul, Matrix.vecMul_one, smul_dotProduct]
  change (NTrace (Mi * A * Mjᴴ) / NTrace (Mi * Mjᴴ)) *
      (star (u i) ⬝ᵥ u j) =
    (NTrace (Mi * A * Mjᴴ) / NTrace (Mi * Mjᴴ)) *
      (if i = j then 1 else 0)
  rw [hfamily.1 i j]

/-- For the canonical Hermitian MDE branch, the norm of the matrix element of
CEH's theta-one regularized observable is exactly the published `localETHError`.
Thus the two-resolvent estimate for `A°` has precisely the deterministic
observable required by the consumer interface. -/
theorem norm_spectralMatrixElement_regObs_mde_eq_localETHError
    {N : ℕ} {F H : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) (etaF : ℝ → ℝ) (ξ : ℝ)
    (hetaF : ∀ x, 0 < etaF x)
    (lam : Fin N → ℝ) (u : Fin N → Fin N → ℂ)
    (hfamily : IsLocalETHOrthonormalEigenFamily H lam u)
    (A : LocalETHMatrix N) (i j : Fin N) :
    let Mf : ℂ → LocalETHMatrix N := hermitianMDEBranch hF hs
    let zi := CEHNative.BlockBand.localETHSpectralPoint
      N etaF ξ (lam i)
    let zj := CEHNative.BlockBand.localETHSpectralPoint
      N etaF ξ (lam j)
    ‖spectralMatrixElement u (regObs (Mf zi) (Mf zj) A) i j‖ =
      CEHNative.BlockBand.localETHError
        Mf etaF ξ A lam u i j := by
  dsimp only
  have hspectral_im (k : Fin N) :
      0 < (CEHNative.BlockBand.localETHSpectralPoint
        N etaF ξ (lam k)).im := by
    simp [CEHNative.BlockBand.localETHSpectralPoint]
    exact mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast hN) ξ)
      (hetaF (lam k))
  by_cases hij : i = j
  · subst j
    rw [spectralMatrixElement_regObs hfamily]
    rw [normalizedTrace_mde_word_div_eq_normalizedTrace_gamma
      hF hN hs (hspectral_im i) A]
    simp [CEHNative.BlockBand.localETHError,
      CEHNative.BlockBand.localETHCenter, spectralMatrixElement,
      Matrix.dotProduct_mulVec]
  · rw [spectralMatrixElement_regObs hfamily]
    simp [hij, CEHNative.BlockBand.localETHError,
      spectralMatrixElement, Matrix.dotProduct_mulVec]

end CEHNative.BlockBand.External.CEH
