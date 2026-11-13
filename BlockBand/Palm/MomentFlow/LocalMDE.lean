module

public import BlockBand.Palm.MomentFlow.LocalSpectral
public import BlockBand.Internal.Contracts.Inputs

/-!
# The fresh Dyson matrix is the branch of the matrix Dyson equation

*Domain:* `N ≥ 1`, Hermitian `F`, `s > 0`, `Im z > 0`, and a positive Dyson root
(`0 < Im freshDyson F s z`, which holds on the fresh-regularity window by `FreshRegular`).
Deterministic.

* `freshM_isManuscriptMDE`: `freshM F s z` solves `IsManuscriptMDE s F z`
  (`(F - z - s⟨M⟩) M = 1` with `⟨M⟩ = freshDyson F s z`, and `Im z · Im M ≻ 0`, since
  `Im M = (Im z + s Im m) M M*`).
* `mdeBranch_matrix_eq_freshM` (with `MDEBranchIdentification` as a hypothesis): every branch
  `M : CEH.MDEBranch (√s) ⟨F, hF⟩` has `M.matrix z = freshM F s z`, and
  `normalizedTrace (M.matrix z) = freshDyson F s z` (`mdeBranch_trace_eq_freshDyson`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.Palm.CoarseRelative
open scoped ComplexConjugate ComplexOrder

variable {N : ℕ}

theorem freshM_normalizedTrace {F : Matrix (Fin N) (Fin N) ℂ} {s : ℝ} {z : ℂ}
    (hm : 0 < (freshDyson F s z).im) :
    CEH.normalizedTrace (freshM F s z) = freshDyson F s z :=
  (freshDyson_spec_of_im_pos F s z hm).symm

/-- `Im M = (Im w) M M*` for `M = (F - w)⁻¹`, `F` Hermitian. -/
theorem imaginaryPart_resolvent {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {w : ℂ}
    (hw : w.im ≠ 0) :
    CEH.imaginaryPart ((F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) =
      ((w.im : ℝ) : ℂ) • ((F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *
        ((F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)ᴴ) := by
  have hwc : (conj w).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.mpr hw
  unfold CEH.imaginaryPart
  rw [hermitian_resolvent_conjTranspose hF w, hermitian_resolvent_sub hF hw hwc, smul_smul]
  congr 1
  have h2 : (2 * Complex.I) ≠ 0 := by simp
  rw [Complex.sub_conj]
  field_simp
  push_cast; ring

/-- `freshM F s z` solves the matrix Dyson equation `IsManuscriptMDE`. -/
theorem freshM_isManuscriptMDE {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {s : ℝ}
    (hs : 0 < s) {z : ℂ} (hz : 0 < z.im) (hm : 0 < (freshDyson F s z).im) :
    IsManuscriptMDE s ⟨F, hF⟩ z (freshM F s z) := by
  set w : ℂ := z + (s : ℂ) * freshDyson F s z
  have hw : 0 < w.im := add_ofReal_mul_im_pos hs hz.le hm
  have hX : freshM F s z = (F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := rfl
  refine ⟨?_, ?_⟩
  · rw [freshM_normalizedTrace hm]
    exact hermitian_shift_mul_inv hF hw.ne'
  · rw [hX, imaginaryPart_resolvent hF hw.ne', smul_smul]
    have hinj : Function.Injective ((F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).vecMul := by
      intro u v huv
      have hu := congrArg (fun x => x ᵥ* (F - w • (1 : Matrix (Fin N) (Fin N) ℂ))) huv
      simp only [Matrix.vecMul_vecMul, hermitian_shift_inv_mul hF hw.ne',
        Matrix.vecMul_one] at hu
      exact hu
    have hpd := Matrix.PosDef.mul_conjTranspose_self _ hinj
    refine hpd.smul ?_
    rw [← Complex.ofReal_mul]
    exact Complex.zero_lt_real.2 (mul_pos hz hw)

/-- Under `MDEBranchIdentification`, every branch of the matrix Dyson equation is `freshM` at
`z`. -/
theorem mdeBranch_matrix_eq_freshM (hMDE : MDEBranchIdentification) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : 0 < z.im) (hm : 0 < (freshDyson F s z).im)
    (M : CEH.MDEBranch (Real.sqrt s) ⟨F, hF⟩) : M.matrix z = freshM F s z := by
  obtain ⟨-, hsol, huniq⟩ := hMDE N hN s hs ⟨F, hF⟩
  exact huniq z hz.ne' _ _ (hsol M z hz.ne') (freshM_isManuscriptMDE hF hs hz hm)

theorem mdeBranch_trace_eq_freshDyson (hMDE : MDEBranchIdentification) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : 0 < z.im) (hm : 0 < (freshDyson F s z).im)
    (M : CEH.MDEBranch (Real.sqrt s) ⟨F, hF⟩) :
    CEH.normalizedTrace (M.matrix z) = freshDyson F s z := by
  rw [mdeBranch_matrix_eq_freshM hMDE hN hF hs hz hm M, freshM_normalizedTrace hm]

/-- On the fresh-regularity window a branch exists and equals `freshM`. -/
theorem exists_mdeBranch_eq_freshM (hMDE : MDEBranchIdentification) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s) :
    Nonempty (CEH.MDEBranch (Real.sqrt s) ⟨F, hF⟩) :=
  (hMDE N hN s hs ⟨F, hF⟩).1

end BlockBand.Palm.MomentFlow
