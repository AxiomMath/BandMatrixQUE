module

public import BlockBand.Internal.Contracts.CoareaPalm
public import BlockBand.Coarea.ChartLaw
public import BlockBand.Model.Construction.GaussianSimpleSpectrum
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalActualPairGoodEventReadback

/-!
# Almost-sure regularity clause of the coarea theorem

*Statement.* For every admissible `p` and every exact physical model, `model.law`-almost
surely `H` is Hermitian, `H.charpoly` is separable, and for every rank `α` and every adjacent
pair `S = {i, i+1}`, `det(H_R - λ_α(H)) ≠ 0`, where `H_R = exteriorBlock p i H`. Measure:
the exact physical law `model.law` on raw site matrices; exact finite statement at fixed
`n, W, b`, with no norm, limit or uniformity assertion.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.RegularAE

open MeasureTheory Matrix
open BlockBand.Model.Construction BlockBand.Internal.Contracts.CoareaPalm

/-- An eigenvalue of a Hermitian matrix is a root of the determinant `det(H - λ)`. -/
theorem det_sub_physicalOrderedEigenvalue_eq_zero (p : Parameters) (H : p.SiteMatrix)
    (hH : H.IsHermitian) (α : Fin p.N) :
    (H - ((physicalOrderedEigenvalue p H α : ℝ) : ℂ) • (1 : p.SiteMatrix)).det = 0 := by
  classical
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  set r := physicalSpectralRank p α
  refine ⟨BlockBand.Foundations.Spectral.increasingEigenvector hH r, ?_, ?_⟩
  · intro h0
    have h1 := BlockBand.Foundations.Spectral.sum_norm_sq_increasingEigenvector hH r
    rw [h0] at h1
    simp at h1
  · rw [Matrix.sub_mulVec, BlockBand.Foundations.Spectral.mulVec_increasingEigenvector,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    unfold physicalOrderedEigenvalue
    rw [rawIncreasingEigenvalue_eq _ H hH, sub_self]

/-- Deterministic pole exclusion: if the characteristic polynomials of `a • H` and
`a • H_R` are coprime for some scalar `a`, then every eigenvalue `μ` of `H` satisfies
`det(H_R - μ) ≠ 0`. -/
theorem exteriorBlock_det_ne_zero_of_isCoprime (p : Parameters) (i : ZMod p.n)
    (H : p.SiteMatrix) (a μ : ℂ)
    (hμ : (H - μ • (1 : p.SiteMatrix)).det = 0)
    (hcop : IsCoprime (a • H).charpoly (a • exteriorBlock p i H).charpoly) :
    (exteriorBlock p i H - μ • 1).det ≠ 0 := by
  classical
  intro hR
  have key : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ),
      (A - μ • 1).det = 0 → ((a • A).charpoly).IsRoot (a * μ) := by
    intro ι _ _ A hA
    rw [Polynomial.IsRoot, Matrix.eval_charpoly]
    have he : Matrix.scalar ι (a * μ) - a • A = (-a) • (A - μ • 1) := by
      ext x y
      by_cases hxy : x = y
      · subst hxy; simp; ring
      · simp [hxy]
    rw [he, Matrix.det_smul, hA, mul_zero]
  exact CoareaNative.BlockBand.GaussianRing.not_isCoprime_of_isRoot (key H hμ)
    (key (exteriorBlock p i H) hR) hcop

/-- Every cyclic label is the cast of a `Fin n` label. -/
theorem exists_fin_cast (p : Parameters) (i : ZMod p.n) :
    ∃ j : Fin p.toNativeParams.n, (j : ZMod p.toNativeParams.n) = i := by
  have : NeZero p.n := ⟨by have := p.n_ge_four; omega⟩
  refine ⟨⟨i.val, ZMod.val_lt i⟩, ?_⟩
  simp

/-- Transport of the coprimality to the current site matrices: almost surely, for
every `i`, the characteristic polynomials of `c^{-1/2} H` and `c^{-1/2} H_R` are coprime.
-/
theorem ae_isCoprime_charpoly_exteriorBlock (p : Parameters) (model : p.GaussianRingModel) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ i : ZMod p.n,
      IsCoprime ((((Real.sqrt p.c)⁻¹ : ℂ)) • H).charpoly
        ((((Real.sqrt p.c)⁻¹ : ℂ)) • exteriorBlock p i H).charpoly := by
  classical
  let M := model.toNativeLaw
  have hall : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ j : Fin p.toNativeParams.n,
      IsCoprime (M.normalizedPhysicalMatrix H).1.charpoly
        (M.normalizedPhysicalPairExteriorMatrix j H).1.charpoly :=
    ae_all_iff.2 fun j => M.ae_isCoprime_normalizedPhysical_pairExterior_charpoly j
  filter_upwards [hall, model.toNativeLaw_H_ae] with H hcop hHH
  intro i
  obtain ⟨j, rfl⟩ := exists_fin_cast p i
  have h := hcop j
  let e := CoareaNative.BlockBand.GaussianRing.physicalIndexSiteEquiv p.toNativeParams
  let f : CoareaNative.BlockBand.GaussianRing.PhysicalPairExteriorIndex p.toNativeParams j ≃
      ExteriorSite p (j : ZMod p.n) :=
    (CoareaNative.BlockBand.GaussianRing.physicalPairExteriorSiteEquiv p.toNativeParams j).trans
      (Equiv.subtypeEquivRight fun x => by rw [not_or])
  have e1 : (M.normalizedPhysicalMatrix H).1 =
      Matrix.reindex e.symm e.symm ((((Real.sqrt p.c)⁻¹ : ℂ)) • H) := by
    ext x y
    change ((Real.sqrt p.c)⁻¹ : ℂ) * M.H H _ _ = _
    rw [show M.H H = H from hHH]
    rfl
  have e2 : (M.normalizedPhysicalPairExteriorMatrix j H).1 =
      Matrix.reindex f.symm f.symm ((((Real.sqrt p.c)⁻¹ : ℂ)) • exteriorBlock p (j : ZMod p.n) H) := by
    ext x y
    change ((Real.sqrt p.c)⁻¹ : ℂ) * M.H H _ _ = _
    rw [show M.H H = H from hHH]
    rfl
  rw [e1, e2, Matrix.charpoly_reindex, Matrix.charpoly_reindex] at h
  exact h

/-- **`CoareaContract.regular_ae`** (the regularity clause of the coarea theorem): almost surely
`H` is Hermitian with simple spectrum and no eigenvalue of `H` lies in `Spec H_R` for any
adjacent exposed pair. Measure: `model.law`; every admissible `p` and every exact model. -/
theorem coarea_regular_ae : ∀ (p : Parameters) (model : p.GaussianRingModel),
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), H.IsHermitian ∧ H.charpoly.Separable ∧
      ∀ (α : Fin p.N) (i : ZMod p.n),
        (exteriorBlock p i H - ((physicalOrderedEigenvalue p H α : ℝ) : ℂ) • 1).det ≠ 0 := by
  intro p model
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable,
    ae_isCoprime_charpoly_exteriorBlock p model] with H hH hsep hcop
  exact ⟨hH, hsep, fun α i => exteriorBlock_det_ne_zero_of_isCoprime p i H _ _
    (det_sub_physicalOrderedEigenvalue_eq_zero p H hH α) (hcop i)⟩

end BlockBand.Coarea.RegularAE
