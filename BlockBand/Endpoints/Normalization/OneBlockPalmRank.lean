module

public import BlockBand.Endpoints.Normalization.OneBlockPalmCoarea
public import BlockBand.Endpoints.Normalization.ExactPalm
public import BlockBand.Coarea.ClockRank

/-!
# One-block Palm identity: reconstruction of the eigenpair on the support

The identity `p_{α0} = (v*Dv)^{-1}`: the one-block analogue of `CoareaContract.reconstructed_rank`
(the reconstruction and index parts of the proof of the coarea theorem) and of the support
computation in the proof of the exact Palm proposition.

**Statement** (`oneBlockPalm_reconstructed_rank`, `oneBlockPalm_reconstruction`). Pointwise and
exact, no measure. For every admissible `p`, block `k`, rank `α`, measurable block frame `U`,
exterior `ω = (H_R, C)`, energy `E`, unit `v`, `G'` with `H = assembleBlock ω G_rec` Hermitian,
`det(H_R - E) ≠ 0`, `det M ≠ 0` and `N_-(M) + N_-(H_R - E) = α`: `λ_α(H) = E`, the selected
eigenvector satisfies `ψψ* = LL*/‖L‖²` with `L = (v, -T(E)v)` (`blockLift`), hence the block
masses are `p_α(H) = blockReconMass ω E v` and `(v*Dv) · p_{αk}(H) = 1`.

**Proof.** As `ClockRank.coarea_reconstructed_rank` with `V = 0` and the decomposition
`k ⊕ R ≃ Site`: frame completeness (`ClockRank.frame_complete`) gives the Schur complement
`A(E) = U_v M U_v*`; Haynsworth inertia (`negativeEigenvalueCount_hermitianSchur`) and the frame
congruence (`ClockRank.negCount_frame`) give `N_-(H - E) = α`; invertibility of `M` and
`H_R - E` makes the kernel of `H - E` the line `ℂ L` (`kernel_frame` below), so `E` is a simple
eigenvalue at rank `α` (`ClockRank.rank_of_simple`), and the measurable selection is a unit
multiple of `L/‖L‖` (`ClockRank.orderedColumnSelection_eq_phase_of_rankSimple`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open Matrix BlockBand.Model.Construction BlockBand.Foundations.Spectral
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea BlockBand.Coarea.ClockRank
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.Layers
open scoped ComplexConjugate

section Block

variable (p : Parameters) (k : ZMod p.n)

private theorem comp_sumEquiv (y : p.Site → ℂ) :
    y ∘ oneBlockPalmSumEquiv p k =
      (fun s : BlockSite p k => y s.1) ⊕ᵥ (fun r : OffBlockSite p k => y r.1) := by
  funext a; cases a <;> rfl

private theorem submatrix_assembleBlock (ω : BlockState p k)
    (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) :
    (assembleBlock p k ω G).submatrix (oneBlockPalmSumEquiv p k) (oneBlockPalmSumEquiv p k) =
      fromBlocks G (ω.2)ᴴ ω.2 ω.1 := by
  ext (a | a) (b | b) <;>
    simp [oneBlockPalmSumEquiv, assembleBlock, a.2, b.2, Matrix.conjTranspose_apply]

private theorem submatrix_assembleBlock_shift (ω : BlockState p k)
    (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) (E : ℝ) :
    (assembleBlock p k ω G - (E : ℂ) • 1).submatrix (oneBlockPalmSumEquiv p k)
        (oneBlockPalmSumEquiv p k) =
      fromBlocks (G - (E : ℂ) • 1) (ω.2)ᴴ ω.2 (ω.1 - (E : ℂ) • 1) := by
  have h : (assembleBlock p k ω G - (E : ℂ) • 1).submatrix (oneBlockPalmSumEquiv p k)
      (oneBlockPalmSumEquiv p k) =
      (assembleBlock p k ω G).submatrix (oneBlockPalmSumEquiv p k) (oneBlockPalmSumEquiv p k) -
        (E : ℂ) • (1 : p.SiteMatrix).submatrix (oneBlockPalmSumEquiv p k)
          (oneBlockPalmSumEquiv p k) := rfl
  rw [h, submatrix_assembleBlock, Matrix.submatrix_one_equiv,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, sub_eq_add_neg, Matrix.fromBlocks_neg,
    Matrix.fromBlocks_add]
  simp [sub_eq_add_neg]

/-- `Σ_x f x = Σ_{s ∈ k} f s + Σ_{r ∉ k} f r`. -/
theorem oneBlockPalm_sum_site_real (f : p.Site → ℝ) :
    ∑ x, f x = ∑ s : BlockSite p k, f s.1 + ∑ r : OffBlockSite p k, f r.1 := by
  rw [← Equiv.sum_comp (oneBlockPalmSumEquiv p k), Fintype.sum_sum_type]
  rfl

/-- `p_{αk}(H) = Σ_{s ∈ k} |ψ_α(s)|²`. -/
theorem oneBlockPalm_blockMass_eq (α : Fin p.N) (H : p.SiteMatrix) :
    physicalOrderedBlockMass p H α k =
      ∑ s : BlockSite p k, ‖physicalOrderedEigenvector p H α s.1‖ ^ 2 := by
  unfold physicalOrderedBlockMass
  rw [← (blockEquiv p k).symm.sum_comp]
  rfl

private theorem shift_mulVec_eq_zero_iff (ω : BlockState p k)
    (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) (E : ℝ) (y : p.Site → ℂ) :
    (assembleBlock p k ω G - (E : ℂ) • 1) *ᵥ y = 0 ↔
      (G - (E : ℂ) • 1) *ᵥ (fun s : BlockSite p k => y s.1) +
          (ω.2)ᴴ *ᵥ (fun r : OffBlockSite p k => y r.1) = 0 ∧
        ω.2 *ᵥ (fun s : BlockSite p k => y s.1) +
          (ω.1 - (E : ℂ) • 1) *ᵥ (fun r : OffBlockSite p k => y r.1) = 0 := by
  rw [← blocks_mulVec_eq_zero, ← comp_sumEquiv, ← submatrix_assembleBlock_shift,
    Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    funext x
    have := congrFun h ((oneBlockPalmSumEquiv p k).symm x)
    simpa using this

private theorem blocks_isHermitian (ω : BlockState p k)
    (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) (E : ℝ)
    (hH : (assembleBlock p k ω G).IsHermitian) :
    (G - (E : ℂ) • 1).IsHermitian ∧ (ω.1 - (E : ℂ) • 1).IsHermitian := by
  have hK := (shift_isHermitian hH E).submatrix (oneBlockPalmSumEquiv p k)
  rw [submatrix_assembleBlock_shift] at hK
  obtain ⟨h11, _, _, h22⟩ := Matrix.isHermitian_fromBlocks_iff.mp hK
  exact ⟨h11, h22⟩

private theorem schurA_eq (ω : BlockState p k) (G : Matrix (BlockSite p k) (BlockSite p k) ℂ)
    (E : ℝ) [Invertible (ω.1 - (E : ℂ) • 1)] :
    G - (E : ℂ) • 1 - (ω.2)ᴴ * ⅟(ω.1 - (E : ℂ) • 1) * (ω.2)ᴴᴴ =
      physicalCoareaA ω.1 ω.2 0 G E := by
  rw [Matrix.invOf_eq_nonsing_inv, conjTranspose_conjTranspose]
  simp only [physicalCoareaA, physicalCoareaF, physicalCoareaResolvent]
  abel

private theorem schurA_isHermitian (ω : BlockState p k)
    (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) (E : ℝ)
    (hH : (assembleBlock p k ω G).IsHermitian) :
    (physicalCoareaA ω.1 ω.2 0 G E).IsHermitian := by
  obtain ⟨h11, h22⟩ := blocks_isHermitian p k ω G E hH
  have h : physicalCoareaA ω.1 ω.2 0 G E =
      G - (E : ℂ) • 1 - (ω.2)ᴴ * (ω.1 - (E : ℂ) • 1)⁻¹ * ω.2 := by
    simp only [physicalCoareaA, physicalCoareaF, physicalCoareaResolvent]
    abel
  rw [h]
  exact h11.sub (Matrix.isHermitian_conjTranspose_mul_mul ω.2 h22.inv)

open CoareaNative.BlockBand (negativeEigenvalueCount) in
private theorem haynsworth (ω : BlockState p k) (G : Matrix (BlockSite p k) (BlockSite p k) ℂ)
    (E : ℝ) (hH : (assembleBlock p k ω G).IsHermitian) (hD : (ω.1 - (E : ℂ) • 1).det ≠ 0) :
    negativeCount (assembleBlock p k ω G - (E : ℂ) • 1) =
      negativeCount (physicalCoareaA ω.1 ω.2 0 G E) + negativeCount (ω.1 - (E : ℂ) • 1) := by
  obtain ⟨h11, h22⟩ := blocks_isHermitian p k ω G E hH
  let _ : Invertible (ω.1 - (E : ℂ) • 1) :=
    Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hD)
  have hS := CoareaNative.BlockBand.negativeEigenvalueCount_hermitianSchur
    (G - (E : ℂ) • 1) (ω.2)ᴴ (ω.1 - (E : ℂ) • 1) h11 h22
  dsimp only at hS
  have hK := shift_isHermitian hH E
  have hK' := hK.submatrix (oneBlockPalmSumEquiv p k)
  rw [negativeCount_eq hK, negativeCount_eq (schurA_isHermitian p k ω G E hH),
    negativeCount_eq h22]
  have hcount : negativeEigenvalueCount hK' = negativeEigenvalueCount hK :=
    negCount_submatrix (oneBlockPalmSumEquiv p k) hK
  refine hcount.symm.trans
    ((negCount_congr hK' _ ((submatrix_assembleBlock_shift p k ω G E).trans
      (by rw [conjTranspose_conjTranspose]))).trans (hS.trans ?_))
  congr 1
  exact negCount_congr _ _ (schurA_eq p k ω G E)

private theorem schurA_eq_transfer (ω : BlockState p k)
    (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) (E : ℝ) :
    physicalCoareaA ω.1 ω.2 0 G E = (G - (E : ℂ) • 1) - (ω.2)ᴴ * physicalCoareaT ω.1 ω.2 E := by
  simp only [physicalCoareaA, physicalCoareaF, physicalCoareaT, Matrix.mul_assoc]
  abel

theorem oneBlockPalm_blockLift_block (ω : BlockState p k) (E : ℝ) (v : BlockSite p k → ℂ) :
    (fun s : BlockSite p k => blockLift p k ω E v s.1) = v := by
  funext s; simp [blockLift, s.2]

theorem oneBlockPalm_blockLift_off (ω : BlockState p k) (E : ℝ) (v : BlockSite p k → ℂ) :
    (fun r : OffBlockSite p k => blockLift p k ω E v r.1) =
      -(physicalCoareaT ω.1 ω.2 E *ᵥ v) := by
  funext r; simp [blockLift, r.2]

private theorem kernel_frame {F : Type*} [Fintype F] [DecidableEq F]
    (ω : BlockState p k) (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) (E : ℝ)
    (v : BlockSite p k → ℂ) (U : Matrix (BlockSite p k) F ℂ) (M : Matrix F F ℂ)
    (hA : physicalCoareaA ω.1 ω.2 0 G E = U * M * Uᴴ) (hUU : Uᴴ * U = 1)
    (hUv : Uᴴ *ᵥ v = 0) (hc : vecMulVec v (star v) + U * Uᴴ = 1)
    (hD : (ω.1 - (E : ℂ) • 1).det ≠ 0) (hM : M.det ≠ 0) :
    (assembleBlock p k ω G - (E : ℂ) • 1) *ᵥ blockLift p k ω E v = 0 ∧
      ∀ y : p.Site → ℂ, (assembleBlock p k ω G - (E : ℂ) • 1) *ᵥ y = 0 →
        y = (star v ⬝ᵥ (fun s : BlockSite p k => y s.1)) • blockLift p k ω E v := by
  constructor
  · rw [shift_mulVec_eq_zero_iff, oneBlockPalm_blockLift_block, oneBlockPalm_blockLift_off]
    constructor
    · rw [Matrix.mulVec_neg, ← sub_eq_add_neg, Matrix.mulVec_mulVec, ← Matrix.sub_mulVec,
        ← schurA_eq_transfer, hA, ← Matrix.mulVec_mulVec, hUv, Matrix.mulVec_zero]
    · have hInv : (ω.1 - (E : ℂ) • 1) * physicalCoareaResolvent ω.1 E = 1 :=
        mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hD)
      rw [Matrix.mulVec_neg, physicalCoareaT, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hInv,
        Matrix.one_mul, add_neg_cancel]
  · intro y hy
    obtain ⟨hPair, hExt⟩ := (shift_mulVec_eq_zero_iff p k ω G E y).mp hy
    set yS : BlockSite p k → ℂ := fun s => y s.1
    set yR : OffBlockSite p k → ℂ := fun r => y r.1
    have hR := physical_exterior_eigenvector_eq_graph ω.1 ω.2 E hD yS yR hExt
    have hPair' : (0 + G - (E : ℂ) • 1) *ᵥ yS + (ω.2)ᴴ *ᵥ yR = 0 := by
      rw [zero_add]; exact hPair
    have hS := physical_schur_eigenvector_equation ω.1 ω.2 0 G E hD yS yR hExt hPair'
    rw [hA] at hS
    have hMU : M *ᵥ (Uᴴ *ᵥ yS) = 0 := by
      have h := congrArg (fun x => Uᴴ *ᵥ x) hS
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h
      rw [Matrix.mulVec_mulVec]
      rwa [show Uᴴ * (U * M * Uᴴ) = (Uᴴ * U) * M * Uᴴ by simp only [Matrix.mul_assoc], hUU,
        Matrix.one_mul] at h
    have hUy : Uᴴ *ᵥ yS = 0 := by
      by_contra h0
      exact hM ((Matrix.exists_mulVec_eq_zero_iff (M := M)).mp ⟨_, h0, hMU⟩)
    obtain ⟨c, hcdef⟩ : ∃ c, c = star v ⬝ᵥ yS := ⟨_, rfl⟩
    rw [← hcdef]
    have hyS : yS = c • v := by
      have h := congrArg (fun X => X *ᵥ yS) hc
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hUy,
        Matrix.mulVec_zero, add_zero, Matrix.vecMulVec_mulVec, ← hcdef] at h
      rw [← h]
      ext s
      simp [mul_comm]
    have hcomp : y ∘ oneBlockPalmSumEquiv p k =
        (c • blockLift p k ω E v) ∘ oneBlockPalmSumEquiv p k := by
      funext a
      cases a with
      | inl s =>
        have := congrFun hyS s
        simpa [oneBlockPalmSumEquiv, blockLift, s.2] using this
      | inr r =>
        have := congrFun hR r
        rw [hyS, Matrix.mulVec_smul] at this
        simpa [oneBlockPalmSumEquiv, blockLift, r.2] using this
    exact (oneBlockPalmSumEquiv p k).surjective.injective_comp_right hcomp

private theorem reconstructed_schur
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (E : ℝ) (v : BlockSite p k → ℂ)
    (G' : Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ)
    (hc : vecMulVec v (star v) + U v * (U v)ᴴ = 1) :
    physicalCoareaA ω.1 ω.2 0 (oneBlockPalmRecon p k U ω E v G') E =
      U v * blockFrameM p k U ω E v G' * (U v)ᴴ := by
  have hc' : vecMulVec v (star v) = 1 - U v * (U v)ᴴ := eq_sub_of_add_eq hc
  simp only [physicalCoareaA, oneBlockPalmRecon, blockFrameM, blockF, hc', Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_sub, Matrix.mul_add,
    Matrix.add_mul]
  abel

private theorem card_frame :
    Fintype.card (BlockSite p k) = Fintype.card (Unit ⊕ BlockFrameIndex p) := by
  rw [regularEvent_card_blockSite, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  have := p.W_pos
  omega

end Block

open CoareaNative.BlockBand (negativeEigenvalueCount) in
/-- **One-block reconstructed rank** (one-block analogue, triage C3, of
`CoareaContract.reconstructed_rank`): on the support of the one-block coarea density the
reassembled matrix has `λ_α = E` and rank-`α` eigenline spanned by `L = blockLift ω E v`.
Pointwise; every admissible `p`, block, rank, frame, exterior, energy, unit `v` and `G'`. -/
theorem oneBlockPalm_reconstructed_rank (p : Parameters) (α : Fin p.N) (k : ZMod p.n)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (ω : BlockState p k) (E : ℝ) (v : BlockSite p k → ℂ)
    (G' : Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ)
    (hH : (assembleBlock p k ω (oneBlockPalmRecon p k U ω E v G')).IsHermitian)
    (hv : l2Norm v = 1) (hD : (ω.1 - (E : ℂ) • 1).det ≠ 0)
    (hM : (blockFrameM p k U ω E v G').det ≠ 0)
    (hcnt : negativeCount (blockFrameM p k U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) =
      α.val) :
    physicalOrderedEigenvalue p (assembleBlock p k ω (oneBlockPalmRecon p k U ω E v G')) α = E ∧
      ∀ x y, physicalOrderedEigenvector p
          (assembleBlock p k ω (oneBlockPalmRecon p k U ω E v G')) α x *
          conj (physicalOrderedEigenvector p
            (assembleBlock p k ω (oneBlockPalmRecon p k U ω E v G')) α y) =
        ((l2Norm (blockLift p k ω E v) ^ 2)⁻¹ : ℂ) *
          (blockLift p k ω E v x * conj (blockLift p k ω E v y)) := by
  set H := assembleBlock p k ω (oneBlockPalmRecon p k U ω E v G')
  set L := blockLift p k ω E v
  set G := oneBlockPalmRecon p k U ω E v G'
  set M := blockFrameM p k U ω E v G'
  obtain ⟨hUU, hUv⟩ := hU.2 v hv
  have hvv := dotProduct_self_of_l2Norm v hv
  have hc := frame_complete (U v) v hUU hUv hvv (card_frame p k)
  have hAeq : physicalCoareaA ω.1 ω.2 0 G E = U v * M * (U v)ᴴ :=
    reconstructed_schur p k U ω E v G' hc
  have hAh := schurA_isHermitian p k ω G E hH
  have hMeq : (U v)ᴴ * physicalCoareaA ω.1 ω.2 0 G E * U v = M := by
    rw [hAeq, show (U v)ᴴ * (U v * M * (U v)ᴴ) * U v = ((U v)ᴴ * U v) * M * ((U v)ᴴ * U v) by
      simp only [Matrix.mul_assoc], hUU, Matrix.one_mul, Matrix.mul_one]
  have hMh : M.IsHermitian := by
    rw [← hMeq]; exact Matrix.isHermitian_conjTranspose_mul_mul (U v) hAh
  have hUMU : (U v * M * (U v)ᴴ).IsHermitian := by rw [← hAeq]; exact hAh
  have hcntA : negativeCount (physicalCoareaA ω.1 ω.2 0 G E) = negativeCount M := by
    rw [negativeCount_eq hAh, negativeCount_eq hMh, negCount_congr hAh hUMU hAeq]
    exact negCount_frame (U v) M hUU hUMU hMh
  have hK := shift_isHermitian hH E
  have hcntK : negativeEigenvalueCount hK = α.val := by
    rw [← negativeCount_eq hK, haynsworth p k ω G E hH hD, hcntA, hcnt]
  have hEC : CoareaNative.BlockBand.eigenCount
      (⟨H, hH⟩ : CoareaNative.BlockBand.HermitianMatrix p.Site) (Set.Iio E) = α.val := by
    rw [← hcntK]
    exact (CoareaNative.BlockBand.negativeEigenvalueCount_sub_real_smul_one_eq_eigenCount_Iio
      ⟨H, hH⟩ E).symm
  obtain ⟨hL0, hker⟩ := kernel_frame p k ω G E v (U v) M hAeq hUU hUv hc hD hM
  have hLne : L ≠ 0 := by
    intro h
    have h1 := oneBlockPalm_blockLift_block p k ω E v
    change (fun s : BlockSite p k => L s.1) = v at h1
    rw [h] at h1
    rw [← h1] at hvv
    simp at hvv
  obtain ⟨j0, hj0⟩ :=
    CoareaNative.BlockBand.exists_orderedEigenvalue_eq_of_shift_mulVec_eq_zero
      (⟨H, hH⟩ : CoareaNative.BlockBand.HermitianMatrix p.Site) hLne hL0
  change increasingEigenvalue hH j0 = E at hj0
  have hmult : ∀ j, increasingEigenvalue hH j = E →
      increasingEigenvector hH j = (star v ⬝ᵥ (fun s : BlockSite p k =>
        increasingEigenvector hH j s.1)) • L := by
    intro j hj
    apply hker
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, mulVec_increasingEigenvector,
      hj, sub_self]
  have hsimple : ∀ j, increasingEigenvalue hH j = E → j = j0 := by
    intro j hj
    by_contra hne
    set cj := star v ⬝ᵥ (fun s : BlockSite p k => increasingEigenvector hH j s.1)
    set ck := star v ⬝ᵥ (fun s : BlockSite p k => increasingEigenvector hH j0 s.1)
    set s := ∑ x, starRingEnd ℂ (L x) * L x
    have horth := increasingEigenvector_orthonormal hH
    have h0 := horth j j0
    have h1 := horth j j
    have h2 := horth j0 j0
    rw [hmult j hj] at h0 h1
    rw [hmult j0 hj0] at h0 h2
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hne, ↓reduceIte] at h0 h1 h2
    have e0 : starRingEnd ℂ cj * ck * s = 0 := by
      rw [← h0, Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    have e1 : starRingEnd ℂ cj * cj * s = 1 := by
      rw [← h1, Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    have e2 : starRingEnd ℂ ck * ck * s = 1 := by
      rw [← h2, Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    have : (1 : ℂ) = 0 := by
      linear_combination (cj * starRingEnd ℂ ck * s) * e0 - (starRingEnd ℂ ck * ck * s) * e1 - e2
    exact one_ne_zero this
  have hrank := rank_of_simple hH E j0 hj0 hsimple
  rw [hEC] at hrank
  set r := physicalSpectralRank p α
  have hr : r = j0 := Fin.ext (by simp [r, physicalSpectralRank, hrank])
  have hEr : physicalOrderedEigenvalue p H α = E := by
    rw [show physicalOrderedEigenvalue p H α = increasingEigenvalue hH r from
      rawIncreasingEigenvalue_eq r H hH, hr, hj0]
  refine ⟨hEr, ?_⟩
  have hsr : RankSimple (⟨H, hH⟩ : HermitianMatrix p.Site) r := by
    intro j hj
    change increasingEigenvalue hH j = increasingEigenvalue hH r at hj
    rw [hr, hj0] at hj
    rw [hr]; exact hsimple j hj
  obtain ⟨z, hz, hsel⟩ := orderedColumnSelection_eq_phase_of_rankSimple r _ hsr
  have hψ : physicalOrderedEigenvector p H α = z • increasingEigenvector hH r :=
    (funext (rawOrderedColumnSelection_eq r H hH)).trans hsel
  set c := star v ⬝ᵥ (fun s : BlockSite p k => increasingEigenvector hH r s.1)
  have hur : increasingEigenvector hH r = c • L := hmult r (by rw [hr, hj0])
  have hnorm := sum_norm_sq_increasingEigenvector hH r
  rw [hur] at hnorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow] at hnorm
  rw [← Finset.mul_sum] at hnorm
  have hL2 : l2Norm L ^ 2 = ∑ x, ‖L x‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun x _ => sq_nonneg _)
  have hzz : z * starRingEnd ℂ z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  have hcc : c * starRingEnd ℂ c = ((l2Norm L ^ 2)⁻¹ : ℝ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hL2, eq_inv_of_mul_eq_one_left hnorm]
  intro x y
  rw [hψ, hur]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  have : z * (c * L x) * (starRingEnd ℂ z * (starRingEnd ℂ c * starRingEnd ℂ (L y))) =
      (z * starRingEnd ℂ z) * (c * starRingEnd ℂ c) * (L x * starRingEnd ℂ (L y)) := by ring
  rw [this, hzz, hcc, one_mul]
  push_cast
  rfl

/-!
## Consequences on the support
-/

section Support

variable (p : Parameters) (k : ZMod p.n)

/-- `v*D(E)v = ‖L_E v‖²` (`D = 1 + T*T`, `L v = (v, -Tv)`), pointwise. -/
theorem oneBlockPalm_clockSpeed_eq_l2Norm_sq (ω : BlockState p k) (E : ℝ)
    (v : BlockSite p k → ℂ) :
    blockClockSpeed p k ω E v = l2Norm (blockLift p k ω E v) ^ 2 := by
  set L := blockLift p k ω E v
  set T := physicalCoareaT ω.1 ω.2 E
  have hL2 : l2Norm L ^ 2 = ∑ x, ‖L x‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun x _ => sq_nonneg _)
  have hpair := oneBlockPalm_blockLift_block p k ω E v
  have hext := oneBlockPalm_blockLift_off p k ω E v
  have hS : ∑ s : BlockSite p k, ‖L s.1‖ ^ 2 = ∑ s, ‖v s‖ ^ 2 :=
    Finset.sum_congr rfl fun s _ => by rw [← congrFun hpair s]
  have hR : ∑ r : OffBlockSite p k, ‖L r.1‖ ^ 2 = ∑ r, ‖(T *ᵥ v) r‖ ^ 2 :=
    Finset.sum_congr rfl fun r _ => by
      rw [show L r.1 = -(T *ᵥ v) r from congrFun hext r, norm_neg]
  rw [hL2, oneBlockPalm_sum_site_real p k, hS, hR, blockClockSpeed, physicalCoareaD, schurClock,
    Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, Complex.add_re,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    re_star_dotProduct_self, re_star_dotProduct_self]

/-- `v*Dv ≥ ‖v‖² = 1` for unit `v`. -/
theorem oneBlockPalm_one_le_clockSpeed (ω : BlockState p k) (E : ℝ) (v : BlockSite p k → ℂ)
    (hv : l2Norm v = 1) : 1 ≤ blockClockSpeed p k ω E v := by
  rw [blockClockSpeed, physicalCoareaD, schurClock,
    Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, Complex.add_re,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    re_star_dotProduct_self, re_star_dotProduct_self, sum_normSq_eq_one v hv]
  have : 0 ≤ ∑ j, ‖(physicalCoareaT ω.1 ω.2 E *ᵥ v) j‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith

theorem oneBlockPalm_clockSpeed_nonneg (ω : BlockState p k) (E : ℝ) (v : BlockSite p k → ℂ) :
    0 ≤ blockClockSpeed p k ω E v := by
  rw [oneBlockPalm_clockSpeed_eq_l2Norm_sq]; exact sq_nonneg _

/-- The reconstructed fresh block is Hermitian (Hermitian `H_R`, Hermitian `G'`). -/
theorem oneBlockPalm_recon_isHermitian
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (h1 : ω.1.IsHermitian) (E : ℝ) (v : BlockSite p k → ℂ)
    (G' : Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ) (hG' : G'.IsHermitian) :
    (oneBlockPalmRecon p k U ω E v G').IsHermitian := by
  have hF := blockF_isHermitian p k ω h1 E
  have hvv : (vecMulVec v (star v)).IsHermitian := by
    ext a b
    simp [vecMulVec, Matrix.conjTranspose_apply, mul_comm]
  have hE : ((E : ℂ) • vecMulVec v (star v)).IsHermitian := by
    rw [IsHermitian, Matrix.conjTranspose_smul, hvv.eq, Complex.star_def, Complex.conj_ofReal]
  unfold oneBlockPalmRecon
  exact (hE.add (Matrix.isHermitian_mul_mul_conjTranspose _
    ((Matrix.isHermitian_conjTranspose_mul_mul _ hF).add hG'))).sub hF

/-- **Reconstruction on the support** (triage C3, `p_{α0} = (v*Dv)⁻¹`): for Hermitian `H_R`,
Hermitian `G'`, unit `v`, `det(H_R - E) ≠ 0`, `det M ≠ 0` and the rank condition, the
reassembled `H = assembleBlock ω G_rec` has `λ_α(H) = E`, block masses `p_α(H) = p(v,E)`
(`blockReconMass`) and `(v*Dv) · p_{αk}(H) = 1`. -/
theorem oneBlockPalm_reconstruction (α : Fin p.N)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (ω : BlockState p k) (h1 : ω.1.IsHermitian) (E : ℝ)
    (v : BlockSite p k → ℂ) (G' : Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ)
    (hG' : G'.IsHermitian) (hv : l2Norm v = 1) (hD : (ω.1 - (E : ℂ) • 1).det ≠ 0)
    (hM : (blockFrameM p k U ω E v G').det ≠ 0)
    (hcnt : negativeCount (blockFrameM p k U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) =
      α.val) :
    physicalOrderedEigenvalue p (assembleBlock p k ω (oneBlockPalmRecon p k U ω E v G')) α = E ∧
      blockMassVector p (assembleBlock p k ω (oneBlockPalmRecon p k U ω E v G')) α =
        blockReconMass p k ω E v ∧
      blockClockSpeed p k ω E v *
        physicalOrderedBlockMass p (assembleBlock p k ω (oneBlockPalmRecon p k U ω E v G')) α k
          = 1 := by
  have hH := oneBlockPalm_assembleBlock_isHermitian p k ω _ h1
    (oneBlockPalm_recon_isHermitian p k U ω h1 E v G' hG')
  obtain ⟨hlam, hproj⟩ := oneBlockPalm_reconstructed_rank p α k U hU ω E v G' hH hv hD hM hcnt
  set L := blockLift p k ω E v
  set H := assembleBlock p k ω (oneBlockPalmRecon p k U ω E v G')
  have hpair := oneBlockPalm_blockLift_block p k ω E v
  have hpt : ∀ x, ‖physicalOrderedEigenvector p H α x‖ ^ 2 = (l2Norm L ^ 2)⁻¹ * ‖L x‖ ^ 2 := by
    intro x
    have h := congrArg Complex.re (hproj x x)
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, Complex.ofReal_re] at h
    rw [h]
    norm_cast
  have hspeed : blockClockSpeed p k ω E v = l2Norm L ^ 2 :=
    oneBlockPalm_clockSpeed_eq_l2Norm_sq p k ω E v
  have hpos : l2Norm L ^ 2 ≠ 0 := by
    rw [← hspeed]; exact (lt_of_lt_of_le one_pos (oneBlockPalm_one_le_clockSpeed p k ω E v hv)).ne'
  refine ⟨hlam, ?_, ?_⟩
  · funext j
    simp only [blockMassVector, physicalOrderedBlockMass, blockReconMass, hpt, hspeed]
    rw [← Finset.mul_sum, inv_mul_eq_div]
  · have hm : physicalOrderedBlockMass p H α k = (l2Norm L ^ 2)⁻¹ := by
      rw [oneBlockPalm_blockMass_eq]
      simp_rw [hpt]
      rw [← Finset.mul_sum]
      have : ∑ s : BlockSite p k, ‖L s.1‖ ^ 2 = 1 := by
        rw [← sum_normSq_eq_one v hv]
        exact Finset.sum_congr rfl fun s _ => by rw [← congrFun hpair s]
      rw [this, mul_one]
    rw [hm, hspeed, mul_inv_cancel₀ hpos]

end Support

end BlockBand.Endpoints.Normalization
