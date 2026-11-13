module

public import BlockBand.Internal.Contracts.ClocksLeadProfile
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import BlockBand.Endpoints.Normalization.OneBlockPalmSplitting

/-!
# `LeadFieldIdentificationContract`: the deterministic clauses

In the proof of the physical lead-profile theorem, the absorbed-density identity identifies the
resulting Gaussian field; splitting this column into the old path and block `0` gives exactly
`(J𝒢₁₂g, Hg) = (JRLg, Hg)`.

**Statements proved here** (the additive contract `ClocksLeadProfile.LeadFieldIdentificationContract`):
* `leadField_identity` — the clause `identity`, exactly as stated in the contract: on every
  sample where the five matrices `H_path - e`, `A - e - X`, `H_R - e`, `z₀ - Σ`, `z_b - X` are
  invertible (`IsLeadRegular`), for every block vector `g` and ring site `y`,
  `blockLift ω e ((z₀ - Σ)⁻¹ g)(y) = (H g_port)(0, y₂)` at block `k` and
  `= (U L g_port)(leadPos y)` off block `k`, `ω = leadExterior p k x`.
* `leadField_covariance` — the clause `covariance`: `MM* = c|z₀ - Σ|^{-2}` for
  `M = √c (z₀ - Σ)⁻¹` whenever `det(z₀ - Σ) ≠ 0`.
Both are deterministic (no measure).

**Proof of `identity`.** `leadPos` is a bijection `OffBlockSite p k ≃ FullSite W (n-3)`
(injective by the relative block index, equal cardinalities `(n-1)W`). In lead coordinates
`H_R - e = [[P - e, Q], [Qᴴ, A - e]]`, `C = [0; B]`; the block inverse (Schur complement on the
path, `X = Qᴴ(P-e)⁻¹Q`, `S₂ = A - e - X`) gives `(H_R - e)⁻¹C = [-(P-e)⁻¹QS₂⁻¹B; S₂⁻¹B]` and
`Σ = BᴴS₂⁻¹B`. Hence `(z₀ - Σ)⁻¹ = 𝒢₂₂ = H` and `𝒢₁₂ = -S₂⁻¹B𝒢₂₂` (Schur complement of
`𝒢⁻¹ = [[S₂, B], [Bᴴ, z₀]]`), and `U = [-(P-e)⁻¹QK⁻¹; K⁻¹]` (Schur complement of the matched-lead
matrix, `K = z_b - X`), so `UL = UK𝒢₁₂ = [-(P-e)⁻¹Q𝒢₁₂; 𝒢₁₂] = -(H_R - e)⁻¹C(z₀ - Σ)⁻¹`.

**Reduction of `law`.** Every one-block splitting law is the image of the physical law under
`H ↦ (H_R, C)` (`blockSplitting_unique`), so `law` holds as soon as the lead law
`(growthPathLaw ⊗ layerLaw .common).map leadExterior` is itself a one-block splitting law.
`leadFieldIdentification_of_split_regular` assembles the contract from that fact and
`regular_ae`.

The proof uses Mathlib's Schur-complement inverse formula `invOf_fromBlocks₁₁_eq`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open Matrix
open BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Critical BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile
open scoped ComplexConjugate Matrix

namespace LeadProfile

/-- The `(1,2)` and `(2,2)` blocks of the inverse of a block matrix with invertible `A` and
Schur complement `S = D - CA⁻¹B`: `-A⁻¹BS⁻¹` and `S⁻¹`. -/
theorem inv_fromBlocks_toBlocks {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hA : A.det ≠ 0) (hS : (D - C * A⁻¹ * B).det ≠ 0) :
    ((fromBlocks A B C D)⁻¹).toBlocks₁₂ = -(A⁻¹ * B * (D - C * A⁻¹ * B)⁻¹) ∧
      ((fromBlocks A B C D)⁻¹).toBlocks₂₂ = (D - C * A⁻¹ * B)⁻¹ := by
  let iA : Invertible A := invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA)
  have hAi : ⅟A = A⁻¹ := invOf_eq_nonsing_inv A
  let iS : Invertible (D - C * ⅟A * B) := by
    rw [hAi]; exact invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hS)
  let := fromBlocks₁₁Invertible A B C D
  rw [← invOf_eq_nonsing_inv, invOf_fromBlocks₁₁_eq, toBlocks_fromBlocks₁₂,
    toBlocks_fromBlocks₂₂]
  simp only [invOf_eq_nonsing_inv, and_self]

end LeadProfile

section Positions

variable (p : Parameters) (k : ZMod p.n)

theorem leadPos_rel_ne_zero (x : OffBlockSite p k) : (x.1.1 - k).val ≠ 0 := by
  intro h
  rw [ZMod.val_eq_zero, sub_eq_zero] at h
  exact x.2 h

theorem leadPos_rel_lt (x : OffBlockSite p k) : (x.1.1 - k).val < p.n := ZMod.val_lt _

theorem leadPos_injective : Function.Injective (leadPos p k) := by
  intro x y h
  have hx0 := leadPos_rel_ne_zero p k x
  have hy0 := leadPos_rel_ne_zero p k y
  have hxn := leadPos_rel_lt p k x
  have hyn := leadPos_rel_lt p k y
  have h4 := p.n_ge_four
  have key : (x.1.1 - k).val = (y.1.1 - k).val ∧ x.1.2 = y.1.2 := by
    unfold leadPos at h
    simp only at h
    split_ifs at h with h1 h2 h3 h4' h5 h6 h7 h8
    all_goals first
      | (simp only [Sum.inr.injEq, Prod.mk.injEq] at h; exact ⟨by omega, h.2⟩)
      | (simp only [Sum.inl.injEq, Prod.mk.injEq, Fin.mk.injEq] at h; exact ⟨by omega, h.2⟩)
  obtain ⟨hrel, h2⟩ := key
  have h1 : x.1.1 = y.1.1 := by
    have := ZMod.val_injective p.n hrel
    simpa using this
  exact Subtype.ext (Prod.ext h1 h2)

theorem card_offBlockSite_eq :
    Fintype.card (OffBlockSite p k) = Fintype.card (FullSite p.W (p.n - 3)) := by
  classical
  let e : {x : p.Site // x.1 = k} ≃ Fin p.W :=
    { toFun := fun x => x.1.2
      invFun := fun a => ⟨(k, a), rfl⟩
      left_inv := fun x => by obtain ⟨⟨a, b⟩, h⟩ := x; subst h; rfl
      right_inv := fun a => rfl }
  have hblock : Fintype.card {x : p.Site // x.1 = k} = p.W := by
    rw [Fintype.card_congr e, Fintype.card_fin]
  have h4 := p.n_ge_four
  rw [Fintype.card_subtype_compl, hblock]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Parameters.Site, ZMod.card]
  rw [← Nat.add_mul, ← Nat.sub_one_mul]
  congr 1
  omega

/-- `leadPos` as an equivalence `OffBlockSite p k ≃ FullSite W (n-3)`. -/
def leadPosEquiv : OffBlockSite p k ≃ FullSite p.W (p.n - 3) :=
  Equiv.ofBijective (leadPos p k)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨leadPos_injective p k, card_offBlockSite_eq p k⟩)

@[simp] theorem leadPosEquiv_apply (x : OffBlockSite p k) : leadPosEquiv p k x = leadPos p k x :=
  rfl

/-- Block `k` identified with the common port `Fin 1 × Fin W`. -/
def blockPortEquiv : BlockSite p k ≃ Fin 1 × Fin p.W where
  toFun y := ((0 : Fin 1), y.1.2)
  invFun i := ⟨(k, i.2), rfl⟩
  left_inv y := by obtain ⟨⟨a, b⟩, h⟩ := y; subst h; rfl
  right_inv i := Prod.ext (Subsingleton.elim _ _) rfl

theorem blockPortVector_eq (g : BlockSite p k → ℂ) :
    blockPortVector p k g = g ∘ (blockPortEquiv p k).symm := rfl

end Positions

section LeadCoordinates

variable (p : Parameters) (e : ℝ) (x : GrowthPath p.W × LayerSample p.W .common)

/-- `P - e` (the path block). -/
abbrev leadP : Matrix (Fin (p.n - 3) × Fin p.W) (Fin (p.n - 3) × Fin p.W) ℂ :=
  pathMatrix (pathAt p.W (p.n - 3) x.1) - (e : ℂ) • 1

/-- `Q` (the path–port coupling). -/
abbrev leadQ : Matrix (Fin (p.n - 3) × Fin p.W) (Fin 2 × Fin p.W) ℂ :=
  pathPortCoupling (pathAt p.W (p.n - 3) x.1)

/-- `S₂ = A - e - X`. -/
abbrev leadS2 : Matrix (Fin 2 × Fin p.W) (Fin 2 × Fin p.W) ℂ :=
  blockDiag x.2.1 - (e : ℂ) • 1 - leadSchur e p.W (p.n - 3) x.1

/-- `B` (the neighbour–block bonds). -/
abbrev leadB : Matrix (Fin 2 × Fin p.W) (Fin 1 × Fin p.W) ℂ := bondMatrix .common x.2.2

/-- `Σ_lead = Bᴴ S₂⁻¹ B`. -/
abbrev leadSigma : Matrix (Fin 1 × Fin p.W) (Fin 1 × Fin p.W) ℂ :=
  (leadB p x)ᴴ * (leadS2 p e x)⁻¹ * leadB p x

theorem leadSchur_eq : leadSchur e p.W (p.n - 3) x.1 =
    (leadQ p x)ᴴ * (leadP p e x)⁻¹ * leadQ p x := rfl

theorem leadExteriorMatrix_sub :
    leadExteriorMatrix p x.1 x.2 - (e : ℂ) • 1 =
      fromBlocks (leadP p e x) (leadQ p x) (leadQ p x)ᴴ (blockDiag x.2.1 - (e : ℂ) • 1) := by
  unfold leadExteriorMatrix
  ext (i | i) (j | j) <;>
    simp [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply]

theorem leadExteriorCoupling_eq :
    leadExteriorCoupling p x.2 = fromRows 0 (leadB p x) := by
  ext (i | i) j <;> rfl

theorem leadExterior_inv_blocks (h1 : (leadP p e x).det ≠ 0) (h2 : (leadS2 p e x).det ≠ 0) :
    ((leadExteriorMatrix p x.1 x.2 - (e : ℂ) • 1)⁻¹).toBlocks₁₂ =
        -((leadP p e x)⁻¹ * leadQ p x * (leadS2 p e x)⁻¹) ∧
      ((leadExteriorMatrix p x.1 x.2 - (e : ℂ) • 1)⁻¹).toBlocks₂₂ = (leadS2 p e x)⁻¹ := by
  rw [leadExteriorMatrix_sub]
  have hS : blockDiag x.2.1 - (e : ℂ) • 1 - (leadQ p x)ᴴ * (leadP p e x)⁻¹ * leadQ p x =
      leadS2 p e x := rfl
  have := LeadProfile.inv_fromBlocks_toBlocks (leadP p e x) (leadQ p x) (leadQ p x)ᴴ
    (blockDiag x.2.1 - (e : ℂ) • 1) h1 (by rw [hS]; exact h2)
  rw [hS] at this
  exact this

/-- `(H_R - e)⁻¹ C = [-(P-e)⁻¹QS₂⁻¹B; S₂⁻¹B]` in lead coordinates. -/
theorem leadExterior_inv_mul_coupling (h1 : (leadP p e x).det ≠ 0)
    (h2 : (leadS2 p e x).det ≠ 0) :
    (leadExteriorMatrix p x.1 x.2 - (e : ℂ) • 1)⁻¹ * leadExteriorCoupling p x.2 =
      fromRows (-((leadP p e x)⁻¹ * leadQ p x * (leadS2 p e x)⁻¹ * leadB p x))
        ((leadS2 p e x)⁻¹ * leadB p x) := by
  obtain ⟨hb12, hb22⟩ := leadExterior_inv_blocks p e x h1 h2
  rw [leadExteriorCoupling_eq, ← fromBlocks_toBlocks
    ((leadExteriorMatrix p x.1 x.2 - (e : ℂ) • 1)⁻¹), fromBlocks_mul_fromRows, hb12, hb22]
  simp only [Matrix.mul_zero, zero_add, Matrix.neg_mul]

/-- `Cᴴ(H_R - e)⁻¹C = Bᴴ S₂⁻¹ B` in lead coordinates. -/
theorem leadExterior_sigma (h1 : (leadP p e x).det ≠ 0) (h2 : (leadS2 p e x).det ≠ 0) :
    (leadExteriorCoupling p x.2)ᴴ * (leadExteriorMatrix p x.1 x.2 - (e : ℂ) • 1)⁻¹ *
        leadExteriorCoupling p x.2 = leadSigma p e x := by
  rw [Matrix.mul_assoc, leadExterior_inv_mul_coupling p e x h1 h2, leadExteriorCoupling_eq,
    conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]
  simp only [conjTranspose_zero, Matrix.zero_mul, zero_add, leadSigma, Matrix.mul_assoc]

end LeadCoordinates

section Identity

variable (p : Parameters) (k : ZMod p.n) (e : ℝ) (x : GrowthPath p.W × LayerSample p.W .common)

theorem leadExterior_fst :
    (leadExterior p k x).1 =
      (leadExteriorMatrix p x.1 x.2).submatrix (leadPosEquiv p k) (leadPosEquiv p k) := rfl

theorem leadExterior_snd :
    (leadExterior p k x).2 =
      (leadExteriorCoupling p x.2).submatrix (leadPosEquiv p k) (blockPortEquiv p k) := rfl

theorem leadExterior_fst_sub :
    (leadExterior p k x).1 - (e : ℂ) • 1 =
      (leadExteriorMatrix p x.1 x.2 - (e : ℂ) • 1).submatrix (leadPosEquiv p k)
        (leadPosEquiv p k) := by
  rw [leadExterior_fst]
  ext i j
  simp [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, (leadPos_injective p k).eq_iff]

/-- `(H_R - e)⁻¹C` read in lead coordinates. -/
theorem leadExterior_T :
    physicalCoareaT (leadExterior p k x).1 (leadExterior p k x).2 e =
      ((leadExteriorMatrix p x.1 x.2 - (e : ℂ) • 1)⁻¹ * leadExteriorCoupling p x.2).submatrix
        (leadPosEquiv p k) (blockPortEquiv p k) := by
  unfold physicalCoareaT physicalCoareaResolvent
  rw [leadExterior_fst_sub, inv_submatrix_equiv, leadExterior_snd, submatrix_mul_equiv]

/-- `z₀ - Σ` read on the common port. -/
theorem blockShifted_leadExterior (h1 : (leadP p e x).det ≠ 0) (h2 : (leadS2 p e x).det ≠ 0) :
    blockShifted p k (leadExterior p k x) e =
      (commonZ p.b e • (1 : Matrix (Fin 1 × Fin p.W) (Fin 1 × Fin p.W) ℂ) -
        leadSigma p e x).submatrix (blockPortEquiv p k) (blockPortEquiv p k) := by
  unfold blockShifted blockF physicalCoareaF physicalCoareaResolvent
  rw [leadExterior_fst_sub, inv_submatrix_equiv, leadExterior_snd, conjTranspose_submatrix,
    submatrix_mul_equiv, submatrix_mul_equiv, leadExterior_sigma p e x h1 h2]
  ext i j
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, sub_eq_add_neg]

/-- The common-port resolvent blocks: `H = (z₀ - Σ)⁻¹`, `𝒢₁₂ = -S₂⁻¹B(z₀ - Σ)⁻¹`. -/
theorem commonPort_blocks (h2 : (leadS2 p e x).det ≠ 0)
    (h4 : (commonZ p.b e • (1 : Matrix (Fin 1 × Fin p.W) (Fin 1 × Fin p.W) ℂ) -
        leadSigma p e x).det ≠ 0) :
    (commonPortResolvent p.b e (leadSchur e p.W (p.n - 3) x.1) x.2).toBlocks₁₂ =
        -((leadS2 p e x)⁻¹ * leadB p x * (commonZ p.b e • 1 - leadSigma p e x)⁻¹) ∧
      commonPortH p.b e (leadSchur e p.W (p.n - 3) x.1) x.2 =
        (commonZ p.b e • 1 - leadSigma p e x)⁻¹ := by
  unfold commonPortH commonPortResolvent layerResolvent layerMatrix
  exact LeadProfile.inv_fromBlocks_toBlocks _ _ _ _ h2 h4

/-- The matched-lead response: `U = [-(P-e)⁻¹QK⁻¹; K⁻¹]`. -/
theorem leadResponse_eq (h1 : (leadP p e x).det ≠ 0)
    (h5 : (matchedLeadK p.b e (leadSchur e p.W (p.n - 3) x.1)).det ≠ 0) :
    leadResponse p.b e p.W (p.n - 3) x.1 =
      fromRows (-((leadP p e x)⁻¹ * leadQ p x *
          (matchedLeadK p.b e (leadSchur e p.W (p.n - 3) x.1))⁻¹))
        (matchedLeadK p.b e (leadSchur e p.W (p.n - 3) x.1))⁻¹ := by
  obtain ⟨hb12, hb22⟩ := LeadProfile.inv_fromBlocks_toBlocks (leadP p e x) (leadQ p x)
    (leadQ p x)ᴴ (boundaryZ p.b e • 1) h1 h5
  have hfull : fullInverse p.b e p.W (p.n - 3) x.1 =
      (fromBlocks (leadP p e x) (leadQ p x) (leadQ p x)ᴴ (boundaryZ p.b e • 1))⁻¹ := rfl
  have hK : matchedLeadK p.b e (leadSchur e p.W (p.n - 3) x.1) =
      boundaryZ p.b e • 1 - (leadQ p x)ᴴ * (leadP p e x)⁻¹ * leadQ p x := rfl
  rw [hK, ← hb12, ← hb22]
  ext (i | i) j <;> simp [leadResponse, hfull, fromRows, toBlocks₁₂, toBlocks₂₂] <;> rfl

/-- `UL = -[(H_R - e)⁻¹C]_lead (z₀ - Σ)⁻¹`. -/
theorem leadResponse_mul_commonPortL (h1 : (leadP p e x).det ≠ 0)
    (h2 : (leadS2 p e x).det ≠ 0)
    (h4 : (commonZ p.b e • (1 : Matrix (Fin 1 × Fin p.W) (Fin 1 × Fin p.W) ℂ) -
        leadSigma p e x).det ≠ 0)
    (h5 : (matchedLeadK p.b e (leadSchur e p.W (p.n - 3) x.1)).det ≠ 0) :
    leadResponse p.b e p.W (p.n - 3) x.1 *
        commonPortL p.b e (leadSchur e p.W (p.n - 3) x.1) x.2 =
      -(((leadExteriorMatrix p x.1 x.2 - (e : ℂ) • 1)⁻¹ * leadExteriorCoupling p x.2) *
        (commonZ p.b e • 1 - leadSigma p e x)⁻¹) := by
  obtain ⟨h12, -⟩ := commonPort_blocks p e x h2 h4
  have hK : (matchedLeadK p.b e (leadSchur e p.W (p.n - 3) x.1))⁻¹ *
      matchedLeadK p.b e (leadSchur e p.W (p.n - 3) x.1) = 1 :=
    nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h5)
  rw [leadResponse_eq p e x h1 h5, leadExterior_inv_mul_coupling p e x h1 h2, commonPortL,
    h12, fromRows_mul, fromRows_mul, fromRows_neg]
  congr 1
  · simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (matchedLeadK p.b e _)⁻¹, hK, Matrix.one_mul]
  · simp only [Matrix.mul_neg, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (matchedLeadK p.b e _)⁻¹, hK, Matrix.one_mul]

/-- **`LeadFieldIdentificationContract.identity`.** Deterministic; on `IsLeadRegular`. -/
theorem leadField_identity (hreg : IsLeadRegular p k e x) (g : BlockSite p k → ℂ)
    (y : p.Site) :
    blockLift p k (leadExterior p k x) e ((blockShifted p k (leadExterior p k x) e)⁻¹ *ᵥ g) y =
      if hy : y.1 = k then
        (commonPortH p.b e (leadSchur e p.W (p.n - 3) x.1) x.2 *ᵥ blockPortVector p k g)
          ((0 : Fin 1), y.2)
      else ((leadResponse p.b e p.W (p.n - 3) x.1 *
          commonPortL p.b e (leadSchur e p.W (p.n - 3) x.1) x.2) *ᵥ
        blockPortVector p k g) (leadPos p k ⟨y, hy⟩) := by
  obtain ⟨h1, h2, -, h4', h5⟩ := hreg
  have h4 : (commonZ p.b e • (1 : Matrix (Fin 1 × Fin p.W) (Fin 1 × Fin p.W) ℂ) -
      leadSigma p e x).det ≠ 0 := by
    rw [blockShifted_leadExterior p k e x h1 h2, det_submatrix_equiv_self] at h4'
    exact h4'
  have hinv : (blockShifted p k (leadExterior p k x) e)⁻¹ =
      (commonZ p.b e • (1 : Matrix (Fin 1 × Fin p.W) (Fin 1 × Fin p.W) ℂ) -
        leadSigma p e x)⁻¹.submatrix (blockPortEquiv p k) (blockPortEquiv p k) := by
    rw [blockShifted_leadExterior p k e x h1 h2, inv_submatrix_equiv]
  have hv : (blockShifted p k (leadExterior p k x) e)⁻¹ *ᵥ g =
      ((commonZ p.b e • (1 : Matrix (Fin 1 × Fin p.W) (Fin 1 × Fin p.W) ℂ) -
        leadSigma p e x)⁻¹ *ᵥ blockPortVector p k g) ∘ blockPortEquiv p k := by
    rw [hinv, submatrix_mulVec_equiv, blockPortVector_eq]
  obtain ⟨-, hH⟩ := commonPort_blocks p e x h2 h4
  by_cases hy : y.1 = k
  · simp only [blockLift, hy, ↓reduceDIte, hv, Function.comp_apply, hH]
    rfl
  · simp only [blockLift, hy, ↓reduceDIte, hv, leadExterior_T p k e x,
      leadResponse_mul_commonPortL p e x h1 h2 h4 h5]
    rw [submatrix_mulVec_equiv]
    simp only [Function.comp_apply, leadPosEquiv_apply, Matrix.neg_mulVec, Pi.neg_apply,
      ← Matrix.mulVec_mulVec]
    congr 3
    funext i
    simp

/-- **`LeadFieldIdentificationContract.covariance`.** Deterministic:
`MM* = c|z₀ - Σ|^{-2}` for `M = √c (z₀ - Σ)⁻¹`. -/
theorem leadField_covariance (ω : BlockState p k) (hdet : (blockShifted p k ω e).det ≠ 0) :
    blockFieldFactor p k ω e * (blockFieldFactor p k ω e)ᴴ = blockMatchedGamma p k ω e := by
  unfold blockFieldFactor blockMatchedGamma
  have hc : 0 ≤ p.c := by have := p.b_lt_half; unfold Parameters.c; linarith
  set S := blockShifted p k ω e
  have hS : IsUnit S.det := isUnit_iff_ne_zero.mpr hdet
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_inv_rev,
    conjTranspose_nonsing_inv]
  congr 1
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hc]

end Identity

section Law

open MeasureTheory

variable (p : Parameters) (k : ZMod p.n)

/-- `splitMap ∘ assembleBlock = fst`: the exterior is read back from the reassembled matrix. -/
theorem splitMap_assembleBlock (ω : BlockState p k)
    (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) :
    oneBlockPalmSplitMap p k (assembleBlock p k ω G) = ω := by
  obtain ⟨HR, C⟩ := ω
  refine Prod.ext ?_ ?_
  · funext x y
    simp [oneBlockPalmSplitMap, assembleBlock, x.2, y.2]
  · funext x y
    simp [oneBlockPalmSplitMap, assembleBlock, x.2, y.2]

/-- **Uniqueness of the one-block splitting law.** Every `Pω` with `IsBlockSplitting` is the
image of the physical law under `H ↦ (H_R, C)`. -/
theorem blockSplitting_unique (model : p.GaussianRingModel) (Pω : Measure (BlockState p k))
    (h : IsBlockSplitting p k model Pω) : Pω = oneBlockPalmSplitLaw p k model := by
  unfold oneBlockPalmSplitLaw
  rw [← h, Measure.map_map (oneBlockPalm_measurable_splitMap p k)
    (regularEvent_measurable_assembleBlock p k)]
  have hf : (oneBlockPalmSplitMap p k ∘ fun x : BlockState p k ×
      Matrix (BlockSite p k) (BlockSite p k) ℂ => assembleBlock p k x.1 x.2) = Prod.fst := by
    funext x; exact splitMap_assembleBlock p k x.1 x.2
  rw [hf, Measure.map_fst_prod, measure_univ, one_smul]

/-- Two one-block splitting laws coincide. -/
theorem blockSplitting_eq (model : p.GaussianRingModel) (Pω Pω' : Measure (BlockState p k))
    (h : IsBlockSplitting p k model Pω) (h' : IsBlockSplitting p k model Pω') : Pω = Pω' :=
  (blockSplitting_unique p k model Pω h).trans (blockSplitting_unique p k model Pω' h').symm

end Law

/-- **`LeadFieldIdentificationContract`, reduction.** The deterministic clauses `identity` and
`covariance` are proved (`leadField_identity`, `leadField_covariance`); `law` follows from the
uniqueness of the one-block splitting law (`blockSplitting_eq`) once the lead law
`(growthPathLaw ⊗ layerLaw .common).map leadExterior` is shown to be a one-block splitting law
(`hsplit`). The two hypotheses are:
* `hsplit`: `(growthPathLaw W b ⊗ layerLaw W b .common).map (leadExterior p k)` is a one-block
  splitting law of block `k` (a Gaussian characteristic-function identity, finitely many
  coordinates of the infinite product), and
* `hreg`: the clause `regular_ae` (almost-sure invertibility of the five matrices). -/
theorem leadFieldIdentification_of_split_regular
    (hsplit : ∀ (p : Parameters) (model : p.GaussianRingModel) (k : ZMod p.n),
      IsBlockSplitting p k model
        (((growthPathLaw p.W p.b).prod (layerLaw p.W p.b .common)).map (leadExterior p k)))
    (hreg : ∀ (p : Parameters) (k : ZMod p.n) (e : ℝ), -2 < e → e < 2 →
      ∀ᵐ x ∂((growthPathLaw p.W p.b).prod (layerLaw p.W p.b .common)), IsLeadRegular p k e x) :
    LeadFieldIdentificationContract where
  law p model k _ h := blockSplitting_eq p k model _ _ h (hsplit p model k)
  regular_ae := hreg
  identity p k e x h g y := leadField_identity p k e x h g y
  covariance p k ω e h := leadField_covariance p k e ω h

end BlockBand.Endpoints.Normalization
