module

public import BlockBand.LocalWindow.ProofCertificateRegular

/-!
# The CEH branch is the certificate's Dyson root

A positive root `m` of the scalar self-consistent equation gives a solution of the matrix Dyson
equation, which identifies the CEH branch at the pair, as used in part (i) of the physical
local-window lemma.

## Main results

* `isManuscriptMDE_of_root`: if `Im z > 0`, `Im m > 0` and `m = ⟨(F - z - s m)⁻¹⟩`, then
  `M₀ = (F - z - s m)⁻¹` solves the matrix Dyson equation (`Inputs.IsManuscriptMDE`), with
  `Im M₀ = Im(z + s m) · M₀ M₀*`.
* `branch_eq_of_root`: under `MDEBranchIdentification`, every branch has
  `M.matrix z = M₀` and `⟨M.matrix z⟩ = m`.
* `certificateMatrixTrace_reindex`: the normalized trace resolvent is invariant under
  reindexing (to pass from the pair sites to `Fin (2W)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofCertificate

open Matrix
open BlockBand.Internal.Contracts.Inputs
open BlockBand.External
open scoped ComplexConjugate ComplexOrder

section Branch

variable {N : ℕ}

/-- `Im (F - w)⁻¹ = Im w · (F - w)⁻¹ ((F - w)⁻¹)*` for Hermitian `F` and nonreal `w`. -/
theorem imaginaryPart_resolvent {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {w : ℂ}
    (hw : w.im ≠ 0) :
    CEH.imaginaryPart (F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      (w.im : ℂ) • ((F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *
        ((F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)ᴴ) := by
  set M₀ := (F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹
  have hw' : (conj w).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.mpr hw
  have hu : IsUnit (F - w • (1 : Matrix (Fin N) (Fin N) ℂ)).det :=
    isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero hF hw)
  have hu' : IsUnit (F - conj w • (1 : Matrix (Fin N) (Fin N) ℂ)).det :=
    isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero hF hw')
  have hH : M₀ᴴ = (F - conj w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := by
    rw [conjTranspose_nonsing_inv, conjTranspose_sub, hF.eq, conjTranspose_smul,
      conjTranspose_one, Complex.star_def]
  have e1 : M₀ * (F - conj w • (1 : Matrix (Fin N) (Fin N) ℂ)) * M₀ᴴ = M₀ := by
    rw [hH, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu', Matrix.mul_one]
  have e2 : M₀ * (F - w • (1 : Matrix (Fin N) (Fin N) ℂ)) * M₀ᴴ = M₀ᴴ := by
    rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have hdiff : M₀ - M₀ᴴ = (w - conj w) • (M₀ * M₀ᴴ) := by
    calc M₀ - M₀ᴴ = M₀ * (F - conj w • (1 : Matrix (Fin N) (Fin N) ℂ)) * M₀ᴴ -
          M₀ * (F - w • (1 : Matrix (Fin N) (Fin N) ℂ)) * M₀ᴴ := by rw [e1, e2]
      _ = (w - conj w) • (M₀ * M₀ᴴ) := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_one, sub_smul]
          abel
  unfold CEH.imaginaryPart
  rw [hdiff, smul_smul]
  congr 1
  rw [Complex.sub_conj]
  have : (2 * Complex.I) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  field_simp
  push_cast; ring

/-- **A positive root gives a solution of the matrix Dyson equation**: for Hermitian `F`,
`s > 0`, `Im z > 0`, `Im m > 0` and `m = ⟨(F - z - s m)⁻¹⟩` (`Palm.certificateMatrixTrace`), the
matrix `M₀ = (F - z - s m)⁻¹` satisfies `Inputs.IsManuscriptMDE s F z M₀`. -/
theorem isManuscriptMDE_of_root {s : ℝ} (hs : 0 < s) (F : CEH.SourceHermitian N)
    {z m : ℂ} (hz : 0 < z.im) (hm : 0 < m.im)
    (heq : m = BlockBand.Palm.certificateMatrixTrace F.1 (z + s * m)) :
    CEH.normalizedTrace (F.1 - (z + s * m) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ = m ∧
      IsManuscriptMDE s F z (F.1 - (z + s * m) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := by
  set w := z + s * m
  have hwim : w.im = z.im + s * m.im := by simp [w, Complex.mul_im]
  have hw : 0 < w.im := by rw [hwim]; positivity
  have htr : CEH.normalizedTrace (F.1 - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ = m := by
    rw [heq]
    unfold CEH.normalizedTrace BlockBand.Palm.certificateMatrixTrace
      BlockBand.Palm.certificateMatrixResolvent
    rw [Fintype.card_fin, div_eq_inv_mul]
  refine ⟨htr, ?_, ?_⟩
  · rw [htr]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero F.2 hw.ne'))
  · rw [imaginaryPart_resolvent F.2 hw.ne', smul_smul]
    have hpd : ((F.1 - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *
        ((F.1 - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)ᴴ).PosDef := by
      apply Matrix.PosDef.mul_conjTranspose_self
      have hu : IsUnit (F.1 - w • (1 : Matrix (Fin N) (Fin N) ℂ)).det :=
        isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero F.2 hw.ne')
      exact vecMul_injective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr ((isUnit_nonsing_inv_det_iff).mpr hu))
    have hpos : (0 : ℝ) < z.im * w.im := mul_pos hz hw
    have := hpd.smul hpos
    convert this using 1
    rw [← Complex.ofReal_mul, Complex.coe_smul]

/-- **Branch identification**: under `MDEBranchIdentification`, every branch `M` of `F` at
`λ = √s` agrees at `z` (`Im z > 0`) with `(F - z - s m)⁻¹` for every positive root
`m = ⟨(F - z - s m)⁻¹⟩`; in particular `⟨M.matrix z⟩ = m`. -/
theorem branch_eq_of_root (hMDE : MDEBranchIdentification) (hN : 0 < N) {s : ℝ} (hs : 0 < s)
    (F : CEH.SourceHermitian N) (M : CEH.MDEBranch (Real.sqrt s) F) {z m : ℂ} (hz : 0 < z.im)
    (hm : 0 < m.im) (heq : m = BlockBand.Palm.certificateMatrixTrace F.1 (z + s * m)) :
    M.matrix z = (F.1 - (z + s * m) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ ∧
      CEH.normalizedTrace (M.matrix z) = m := by
  obtain ⟨-, hsol, huniq⟩ := hMDE N hN s hs F
  obtain ⟨htr, hroot⟩ := isManuscriptMDE_of_root hs F hz hm heq
  have h := huniq z hz.ne' _ _ (hsol M z hz.ne') hroot
  exact ⟨h, h ▸ htr⟩

end Branch

section Reindex

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The normalized trace resolvent is invariant under reindexing. -/
theorem certificateMatrixTrace_reindex (e : ι ≃ κ) (F : Matrix ι ι ℂ) (w : ℂ) :
    BlockBand.Palm.certificateMatrixTrace (reindex e e F) w =
      BlockBand.Palm.certificateMatrixTrace F w := by
  unfold BlockBand.Palm.certificateMatrixTrace BlockBand.Palm.certificateMatrixResolvent
  have h1 : reindex e e F - w • (1 : Matrix κ κ ℂ) = reindex e e (F - w • 1) := by
    ext a b
    simp [reindex_apply, Matrix.sub_apply, Matrix.one_apply, e.symm.injective.eq_iff]
  rw [h1, inv_reindex, reindex_apply, Fintype.card_congr e]
  congr 1
  unfold Matrix.trace
  exact e.symm.sum_comp (fun j => (F - w • (1 : Matrix ι ι ℂ))⁻¹ j j)

end Reindex

end BlockBand.LocalWindow.ProofCertificate
