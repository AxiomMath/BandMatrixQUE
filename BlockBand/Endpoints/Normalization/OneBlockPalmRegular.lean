module

public import BlockBand.Internal.Contracts.Clocks
public import BlockBand.Coarea.RegularAE

/-!
# One-block Palm identity: almost-sure regularity relative to one block

*Statement* (`oneBlockPalm_regular_ae`). For every admissible `p` and every exact physical
model, `model.law`-almost surely `H` is Hermitian, `H.charpoly` is separable, and for every rank
`α` and every block `k`, `det(H_R - λ_α(H)) ≠ 0` where `H_R = (H_xy)_{x.1 ≠ k, y.1 ≠ k}` is the
off-block principal minor (`oneBlockPalmOffBlock`). Measure: `model.law`; exact finite
statement at fixed `n, W, b`. No physical eigenvalue is lost at a pole.

*Proof.* As in the pair case `RegularAE.coarea_regular_ae`, with the single-block common-spectrum
exclusion `Law.ae_isCoprime_normalizedPhysical_exterior_charpoly` (polynomial nullity with a path
witness) in place of the pair version, and the index bridge `physicalIndexSiteEquiv` restricted to
`x.1 ≠ j`. Hermitian support is the first component of `model.isPhysical`; separability is
`GaussianRingModel.ae_charpoly_separable`; the deterministic pole step is
`RegularAE.det_sub_physicalOrderedEigenvalue_eq_zero` and
`CoareaNative.BlockBand.GaussianRing.not_isCoprime_of_isRoot`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory Matrix
open BlockBand.Model.Construction BlockBand.Internal.Contracts.CoareaPalm
  BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Clocks

/-- The off-block principal minor `H_R = (H_xy)_{x.1 ≠ k, y.1 ≠ k}`. -/
def oneBlockPalmOffBlock (p : Parameters) (k : ZMod p.n) (H : p.SiteMatrix) :
    Matrix (OffBlockSite p k) (OffBlockSite p k) ℂ :=
  fun x y => H x.1 y.1

/-- Deterministic pole exclusion: coprime characteristic polynomials of `a • H` and
`a • H_R` forbid `det(H_R - μ) = 0` at an eigenvalue `μ` of `H`. -/
private theorem offBlock_det_ne_zero_of_isCoprime (p : Parameters) (k : ZMod p.n)
    (H : p.SiteMatrix) (a μ : ℂ)
    (hμ : (H - μ • (1 : p.SiteMatrix)).det = 0)
    (hcop : IsCoprime (a • H).charpoly (a • oneBlockPalmOffBlock p k H).charpoly) :
    (oneBlockPalmOffBlock p k H - μ • 1).det ≠ 0 := by
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
    (key (oneBlockPalmOffBlock p k H) hR) hcop

private theorem fin_cast_ne_iff (p : Parameters) (a j : Fin p.toNativeParams.n) :
    a ≠ j ↔ ((a : ZMod p.n) ≠ (j : ZMod p.n)) := by
  have hn : p.toNativeParams.n = p.n := rfl
  have : NeZero p.n := ⟨by have := p.n_ge_four; omega⟩
  constructor
  · intro h hc
    apply h
    apply Fin.ext
    have h1 := congrArg ZMod.val hc
    have ha : (a : ℕ) < p.n := hn ▸ a.isLt
    have hj : (j : ℕ) < p.n := hn ▸ j.isLt
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hj] at h1
    exact h1
  · intro h hc
    exact h (by rw [hc])

/-- Transport of the single-block coprimality: almost surely, for every `k`, the
characteristic polynomials of `c^{-1/2} H` and `c^{-1/2} H_R` (`R` = all blocks but `k`) are
coprime.
-/
theorem oneBlockPalm_ae_isCoprime_charpoly_offBlock (p : Parameters)
    (model : p.GaussianRingModel) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ k : ZMod p.n,
      IsCoprime ((((Real.sqrt p.c)⁻¹ : ℂ)) • H).charpoly
        ((((Real.sqrt p.c)⁻¹ : ℂ)) • oneBlockPalmOffBlock p k H).charpoly := by
  classical
  let M := model.toNativeLaw
  have hall : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ j : Fin p.toNativeParams.n,
      IsCoprime (M.normalizedPhysicalMatrix H).1.charpoly
        (M.normalizedPhysicalExteriorMatrix j H).1.charpoly :=
    ae_all_iff.2 fun j => M.ae_isCoprime_normalizedPhysical_exterior_charpoly j
  filter_upwards [hall, model.toNativeLaw_H_ae] with H hcop hHH
  intro k
  obtain ⟨j, rfl⟩ := BlockBand.Coarea.RegularAE.exists_fin_cast p k
  have h := hcop j
  let e := CoareaNative.BlockBand.GaussianRing.physicalIndexSiteEquiv p.toNativeParams
  let f : CoareaNative.BlockBand.GaussianRing.PhysicalExteriorIndex p.toNativeParams j ≃
      OffBlockSite p (j : ZMod p.n) :=
    e.subtypeEquiv fun x => fin_cast_ne_iff p x.1 j
  have e1 : (M.normalizedPhysicalMatrix H).1 =
      Matrix.reindex e.symm e.symm ((((Real.sqrt p.c)⁻¹ : ℂ)) • H) := by
    ext x y
    change ((Real.sqrt p.c)⁻¹ : ℂ) * M.H H _ _ = _
    rw [show M.H H = H from hHH]
    rfl
  have e2 : (M.normalizedPhysicalExteriorMatrix j H).1 =
      Matrix.reindex f.symm f.symm
        ((((Real.sqrt p.c)⁻¹ : ℂ)) • oneBlockPalmOffBlock p (j : ZMod p.n) H) := by
    ext x y
    change ((Real.sqrt p.c)⁻¹ : ℂ) * M.H H _ _ = _
    rw [show M.H H = H from hHH]
    rfl
  rw [e1, e2, Matrix.charpoly_reindex, Matrix.charpoly_reindex] at h
  exact h

/-- **Almost-sure one-block regularity** (the one-block analogue of `CoareaContract.regular_ae`,
Claim 3 of the coarea theorem): `model.law`-almost surely `H`
is Hermitian with simple spectrum and no eigenvalue of `H` lies in the spectrum of any
off-block minor `H_R`. Measure: `model.law`; every admissible `p` and every exact model. -/
theorem oneBlockPalm_regular_ae : ∀ (p : Parameters) (model : p.GaussianRingModel),
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), H.IsHermitian ∧ H.charpoly.Separable ∧
      ∀ (α : Fin p.N) (k : ZMod p.n),
        (oneBlockPalmOffBlock p k H -
          ((physicalOrderedEigenvalue p H α : ℝ) : ℂ) • 1).det ≠ 0 := by
  intro p model
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable,
    oneBlockPalm_ae_isCoprime_charpoly_offBlock p model] with H hH hsep hcop
  exact ⟨hH, hsep, fun α k => offBlock_det_ne_zero_of_isCoprime p k H _ _
    (BlockBand.Coarea.RegularAE.det_sub_physicalOrderedEigenvalue_eq_zero p H hH α) (hcop k)⟩

end BlockBand.Endpoints.Normalization
