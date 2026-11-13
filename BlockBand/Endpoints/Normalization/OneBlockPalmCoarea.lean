module

public import BlockBand.Internal.Contracts.Clocks
public import BlockBand.Coarea.FixedOmegaRegular
public import BlockBand.Endpoints.Normalization.OneBlockPalmRegular
public import BlockBand.Endpoints.Normalization.OneBlockPalmSplitting
public import BlockBand.Endpoints.Normalization.PalmBridge

/-!
# One-block Palm identity: the fixed-exterior one-block coarea formula

The block `k` is entirely fresh, `GUE_W(c/W)`; `A(e) = G + K(e)`, `K(e) = -e - Σ(e)`, and each
branch `μ_k(e)` has `μ_k' = -v*Dv < 0`, `D = I + T*T`. This is the one-block analogue of the field
`CoareaContract.formula_fixed` (the fixed-`ω` form of the coarea theorem).

**Statement** (`oneBlockPalm_formula_fixed`). For every admissible `p`, exact model, rank `α`,
block `k`, one-block splitting law `Pω` (`IsBlockSplitting`) and measurable block frame `U`
(`IsBlockFrame`): for `Pω`-almost every exterior `ω = (H_R, C)`, simultaneously for every
measurable `g ≥ 0` on block matrices,
`∫ g dGUE_W(c/W) = ∫ dE ∫ dν_W(v) ∫ dGUE_{W-1}(c/W)(G') c_{W,t} 𝓡(E,v,F(E)) (v*D(E)v)
|det M|² 1{N_-(M) + N_-(H_R - E) = α} g(G_rec)` (`oneBlockPalmCoareaFiber`), with
`F(E) = -C*(H_R-E)⁻¹C` (`blockF`), `M = U_v*F(E)U_v + G' - E` (`blockFrameM`) and
`G_rec = E vv* + U_v(U_v*F U_v + G')U_v* - F(E)` (`oneBlockPalmRecon`). Exact identity in
`[0,∞]`; measures `GUE_W(c/W) = gueMeasure (BlockSite p k) (blockTime p)`, Lebesgue `dE`,
`projectiveHaar`, `gueMeasure (BlockFrameIndex p) (blockTime p)`.

**Proof.** The deterministic core is the fixed-`ω` change of variables
`FixedOmega.lintegral_gueMeasure_eq_finFiber` (generic in the exterior dimension, the coupling and
a Hermitian retained potential `V`), applied with `V = 0` after the reindexings
`BlockSite ≃ Fin W` (`blockEquiv`) and `OffBlockSite ≃ Fin dR`. Its good-state hypothesis
(Lebesgue-null complement of the selected-simple good set) follows from the Schur–Haynsworth
lemma `FixedOmega.block_crossing`, which shows that regular reassembled matrices lie in the good
set (`mem_goodSet_of_regular`), and from `GUE`-a.e. regularity for `Pω`-a.e. `ω`
(`oneBlockPalm_regular_ae` transported along the splitting). The argument follows the pair case
`Coarea.FixedOmega.formula_fixed_of_good`, `Coarea.FixedOmega.formula_fixed_of_regularAE`. No
contract is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open Matrix MeasureTheory
open CoareaNative.BlockBand BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw
  BlockBand.Model.Construction BlockBand.Coarea.FixedOmega
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate

section Defs

variable (p : Parameters) (k : ZMod p.n)

/-- The fresh block reconstructed from eigenpair coordinates:
`G_rec = E vv* + U_v (U_v* F(E) U_v + G') U_v* - F(E)`, so `F(E) + G_rec` has eigenpair `(E, v)`. -/
def oneBlockPalmRecon (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (E : ℝ) (v : BlockSite p k → ℂ)
    (G' : Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ) :
    Matrix (BlockSite p k) (BlockSite p k) ℂ :=
  (E : ℂ) • vecMulVec v (star v) + U v * ((U v)ᴴ * blockF p k ω E * U v + G') * (U v)ᴴ -
    blockF p k ω E

/-- The fixed-exterior one-block coarea fiber at rank `α` (crossing speed `v*Dv`), tested
against an observable `g` of the fresh block. -/
def oneBlockPalmCoareaFiber (α : Fin p.N)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (g : Matrix (BlockSite p k) (BlockSite p k) ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ E : ℝ, ∫⁻ v, ∫⁻ G',
    ENNReal.ofReal (coareaConstant p.W (blockTime p) *
        regressionFactor (blockTime p) E v (blockF p k ω E) *
        blockClockSpeed p k ω E v * Complex.normSq (blockFrameM p k U ω E v G').det) *
      (if negativeCount (blockFrameM p k U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val
        then 1 else 0) *
      g (oneBlockPalmRecon p k U ω E v G')
    ∂(gueMeasure (BlockFrameIndex p) (blockTime p)) ∂(projectiveHaar (BlockSite p k)) ∂volume

end Defs

/-!
## Coordinates of the exterior
-/

section ExteriorCoordinates

variable (p : Parameters) (k : ZMod p.n)

/-- Fixed reindexing of the off-block sites. -/
private def offEquiv : OffBlockSite p k ≃ Fin (Fintype.card (OffBlockSite p k)) :=
  Fintype.equivFin _

private def bR (ω : BlockState p k) :
    HermitianCoordinateSpace (Fintype.card (OffBlockSite p k)) :=
  finCoords _ (Matrix.reindex (offEquiv p k) (offEquiv p k) ω.1)

private def bC (ω : BlockState p k) :
    Matrix (Fin (Fintype.card (OffBlockSite p k))) (Fin p.W) ℂ :=
  Matrix.reindex (offEquiv p k) (blockEquiv p k) ω.2

/-- The good-state condition with zero retained potential. -/
private def BlockGood (α : Fin p.N) (ω : BlockState p k) : Prop :=
  volume (physicalSelectedSimpleGoodSet α.val (bR p k ω) (bC p k ω)
    (0 : Matrix (Fin p.W) (Fin p.W) ℂ))ᶜ = 0

private def finFrameB (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ) :
    (Fin p.W → ℂ) → Matrix (Fin p.W) (Fin (p.W - 1)) ℂ :=
  fun w => Matrix.reindex (blockEquiv p k) (Equiv.refl _) (U (w ∘ blockEquiv p k))

private theorem measurable_finFrameB
    {U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ}
    (hU : Measurable U) : Measurable (finFrameB p k U) := by
  have hc : Measurable fun w : Fin p.W → ℂ => w ∘ blockEquiv p k :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  have hr : Measurable (fun M : Matrix (BlockSite p k) (BlockFrameIndex p) ℂ =>
      Matrix.reindex (blockEquiv p k) (Equiv.refl (BlockFrameIndex p)) M) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  exact hr.comp (hU.comp hc)

private theorem finFrameB_isFrameOf
    {U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ}
    (hU : IsBlockFrame p k U) (w : Fin p.W → ℂ) (hw : l2Norm w = 1) :
    IsFrameOf w (finFrameB p k U w) := by
  unfold finFrameB
  have hw' : l2Norm (w ∘ blockEquiv p k) = 1 := by
    have := l2Norm_comp_symm (blockEquiv p k).symm w
    simpa using this.trans hw
  obtain ⟨h1, h2⟩ := hU.2 (w ∘ blockEquiv p k) hw'
  constructor
  · rw [Matrix.conjTranspose_reindex]
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv _ _ _ (blockEquiv p k).symm _]
    simp [h1]
  · funext j
    have := congrFun h2 j
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Function.comp_apply,
      Pi.zero_apply] at this ⊢
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply]
    rw [← this, ← (blockEquiv p k).sum_comp]
    simp

private theorem physicalCoareaF_reindex_zero {α' : Type*} [Fintype α'] [DecidableEq α']
    (eR : OffBlockSite p k ≃ α') (H : Matrix (OffBlockSite p k) (OffBlockSite p k) ℂ)
    (C : Matrix (OffBlockSite p k) (BlockSite p k) ℂ) (E : ℝ) :
    BlockBand.Coarea.physicalCoareaF (Matrix.reindex eR eR H)
        (Matrix.reindex eR (blockEquiv p k) C) (0 : Matrix (Fin p.W) (Fin p.W) ℂ) E =
      Matrix.reindex (blockEquiv p k) (blockEquiv p k)
        (BlockBand.Coarea.physicalCoareaF H C 0 E) := by
  have h0 : Matrix.reindex (blockEquiv p k) (blockEquiv p k)
      (0 : Matrix (BlockSite p k) (BlockSite p k) ℂ) = 0 := by
    ext a b; simp
  rw [← h0]
  exact physicalCoareaF_reindex eR (blockEquiv p k) H C 0 E

/-- **Fixed-exterior one-block coarea at a good exterior.** -/
private theorem formula_fixed_of_good (α : Fin p.N)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (ω : BlockState p k) (hR : ω.1.IsHermitian)
    (hgood : BlockGood p k α ω) (g : Matrix (BlockSite p k) (BlockSite p k) ℂ → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ G, g G ∂gueMeasure (BlockSite p k) (blockTime p) =
      oneBlockPalmCoareaFiber p k α U ω g := by
  set e := blockEquiv p k
  set eR := offEquiv p k
  set t := blockTime p
  have ht : 0 < t := by
    have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
    exact Real.toNNReal_pos.2 (div_pos p.c_pos hW)
  have hd : 1 ≤ p.W := p.W_pos
  have hR' : (Matrix.reindex eR eR ω.1).IsHermitian := hR.submatrix eR.symm
  have hV' : (0 : Matrix (Fin p.W) (Fin p.W) ℂ).IsHermitian := isHermitian_zero
  have hmatR : (hermitianOfFinCoordinates _ (bR p k ω)).1 = Matrix.reindex eR eR ω.1 :=
    hermitianOfFinCoordinates_finCoords hR'
  set g' : Matrix (Fin p.W) (Fin p.W) ℂ → ℝ≥0∞ :=
    fun X => g (Matrix.reindex e.symm e.symm X)
  have hre : Measurable (Matrix.reindex e e : Matrix (BlockSite p k) (BlockSite p k) ℂ → _) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  have hre' : Measurable (Matrix.reindex e.symm e.symm :
      Matrix (Fin p.W) (Fin p.W) ℂ → Matrix (BlockSite p k) (BlockSite p k) ℂ) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  have hg' : Measurable g' := hg.comp hre'
  have hL : ∫⁻ G, g G ∂gueMeasure (BlockSite p k) t = ∫⁻ G, g' G ∂gueMeasure (Fin p.W) t := by
    rw [← gueMeasure_map_reindex e t, lintegral_map hg' hre]
    refine lintegral_congr fun G => ?_
    simp only [g', ← Matrix.reindex_symm, Equiv.symm_apply_apply]
  rw [hL, lintegral_gueMeasure_eq_finFiber hd α.val (bR p k ω) (bC p k ω) hV' ht
    (measurable_finFrameB p k hU.1) (finFrameB_isFrameOf p k hU) hg' hgood]
  unfold finFiber oneBlockPalmCoareaFiber
  refine lintegral_congr fun E => ?_
  have hF : BlockBand.Coarea.physicalCoareaF (hermitianOfFinCoordinates _ (bR p k ω)).1
      (bC p k ω) 0 E = Matrix.reindex e e (blockF p k ω E) := by
    rw [hmatR]; exact physicalCoareaF_reindex_zero p k eR _ _ E
  have hD : BlockBand.Coarea.physicalCoareaD (hermitianOfFinCoordinates _ (bR p k ω)).1
      (bC p k ω) E = Matrix.reindex e e (BlockBand.Coarea.physicalCoareaD ω.1 ω.2 E) := by
    rw [hmatR]; exact physicalCoareaD_reindex eR e _ _ E
  have hnR : negativeCount ((hermitianOfFinCoordinates _ (bR p k ω)).1 - (E : ℂ) • 1) =
      negativeCount (ω.1 - (E : ℂ) • 1) := by
    rw [hmatR]
    have h1 : Matrix.reindex eR eR ω.1 - (E : ℂ) • 1 =
        Matrix.reindex eR eR (ω.1 - (E : ℂ) • 1) := by
      ext a b; simp [Matrix.one_apply]
    rw [h1, negativeCount_reindex eR (M := ω.1 - (E : ℂ) • 1)
      (hR.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E)))]
  simp only [hF, hD, hnR]
  have hmap : (projectiveHaar (BlockSite p k)).map (MeasurableEquiv.arrowCongr' e
      (MeasurableEquiv.refl ℂ)) = projectiveHaar (Fin p.W) := by
    have := BlockBand.Coarea.ProjectiveHaar.projectiveHaar_map_comp_equiv e
    convert this using 2
    funext v
    rfl
  rw [← hmap, MeasureTheory.lintegral_map_equiv]
  refine lintegral_congr fun v => ?_
  refine lintegral_congr fun G' => ?_
  have hv : (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl ℂ)) v = v ∘ e.symm := rfl
  have hfr : finFrameB p k U (v ∘ e.symm) = Matrix.reindex e (Equiv.refl _) (U v) := by
    unfold finFrameB
    congr 2
    funext a
    simp [e]
  rw [hv, hfr, dotProduct_reindex_mulVec, regressionFactor_reindex, fiberIntegrand_reindex]
  rfl

end ExteriorCoordinates

/-!
## Regular reassembled matrices lie in the good set
-/

section Regular

variable (p : Parameters) (k : ZMod p.n)

/-- `k ⊕ R ≃ Site`. -/
def oneBlockPalmSumEquiv : BlockSite p k ⊕ OffBlockSite p k ≃ p.Site :=
  Equiv.sumCompl (fun x : p.Site => x.1 = k)

theorem oneBlockPalm_reindex_assembleBlock (ω : BlockState p k)
    (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) :
    Matrix.reindex (oneBlockPalmSumEquiv p k).symm (oneBlockPalmSumEquiv p k).symm
        (assembleBlock p k ω G) = Matrix.fromBlocks G ω.2ᴴ ω.2 ω.1 := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [oneBlockPalmSumEquiv, assembleBlock, a.2, b.2, Matrix.conjTranspose_apply]

theorem oneBlockPalm_offBlock_assembleBlock (ω : BlockState p k)
    (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) :
    oneBlockPalmOffBlock p k (assembleBlock p k ω G) = ω.1 := by
  ext a b
  simp [oneBlockPalmOffBlock, assembleBlock, a.2, b.2]

theorem oneBlockPalm_block_assembleBlock (ω : BlockState p k)
    (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) :
    (fun a b : BlockSite p k => assembleBlock p k ω G a.1 b.1) = G := by
  funext a b
  simp [assembleBlock, a.2, b.2]

/-- **Regular reassembled matrices lie in the good set** (Schur complement, simple selected root,
Haynsworth rank; `FixedOmega.block_crossing` with `A = G`, `D = H_R`).
-/
private theorem mem_goodSet_of_regular (α : Fin p.N) (ω : BlockState p k)
    (hR : ω.1.IsHermitian) (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) (hG : G.IsHermitian)
    (hH : (assembleBlock p k ω G).IsHermitian) (hsep : (assembleBlock p k ω G).charpoly.Separable)
    (hpole : (oneBlockPalmOffBlock p k (assembleBlock p k ω G) -
      ((physicalOrderedEigenvalue p (assembleBlock p k ω G) α : ℝ) : ℂ) • 1).det ≠ 0) :
    finCoords p.W (Matrix.reindex (blockEquiv p k) (blockEquiv p k) G) ∈
      physicalSelectedSimpleGoodSet α.val (bR p k ω) (bC p k ω)
        (0 : Matrix (Fin p.W) (Fin p.W) ℂ) := by
  set H := assembleBlock p k ω G
  set E := physicalOrderedEigenvalue p H α
  set eqv := oneBlockPalmSumEquiv p k
  set e := blockEquiv p k
  set eR := offEquiv p k
  set r := physicalSpectralRank p α
  set Ah : CoareaNative.BlockBand.HermitianMatrix p.Site := ⟨H, hH⟩
  have hE : E = CoareaNative.BlockBand.orderedEigenvalue Ah r := by
    simp only [E, physicalOrderedEigenvalue]
    rw [rawIncreasingEigenvalue_eq _ H hH]
    rfl
  have hinj := orderedEigenvalue_injective_of_separable' Ah hsep
  set Hb := Matrix.fromBlocks G ω.2ᴴ ω.2 ω.1
  have hblock : Matrix.reindex eqv.symm eqv.symm H = Hb :=
    oneBlockPalm_reindex_assembleBlock p k ω G
  have hdetH : (H - (E : ℂ) • 1).det = 0 :=
    (GaussianRing.det_sub_real_smul_one_eq_zero_iff Ah E).2 ⟨r, hE.symm⟩
  have hdet : (Hb - (E : ℂ) • 1).det = 0 := by
    rw [← hblock, reindex_sub_smul_one, Matrix.det_reindex_self, hdetH]
  set Ab : CoareaNative.BlockBand.HermitianMatrix (BlockSite p k ⊕ OffBlockSite p k) :=
    ⟨Matrix.reindex eqv.symm eqv.symm H, hH.submatrix _⟩
  have hinjb : Function.Injective (CoareaNative.BlockBand.orderedEigenvalue Ab) :=
    (GaussianRing.orderedEigenvalue_injective_reindex_iff eqv.symm Ah).2 hinj
  have hline : ∀ φ ψ : BlockSite p k ⊕ OffBlockSite p k → ℂ, ψ ≠ 0 →
      Hb *ᵥ ψ = (E : ℂ) • ψ → Hb *ᵥ φ = (E : ℂ) • φ → ∃ c : ℂ, φ = c • ψ := by
    intro φ ψ hψ0 hψ hφ
    rw [← hblock] at hψ hφ
    exact GaussianRing.eigenvector_mem_line_of_orderedEigenvalue_injective Ab hinjb hψ0 hψ hφ
  have hcount : negativeCount (Hb - (E : ℂ) • 1) = α.val := by
    rw [← hblock, reindex_sub_smul_one, negativeCount_reindex', hE]
    exact negativeCount_sub_orderedEigenvalue Ah hinj r
  have hdetD : (ω.1 - (E : ℂ) • 1).det ≠ 0 := by
    have := hpole; rwa [oneBlockPalm_offBlock_assembleBlock] at this
  obtain ⟨⟨u, hu0, hSu, hsimp⟩, hrank⟩ :=
    block_crossing hG ω.2 hR E α.val hdetD hdet hline hcount
  set S := G - ω.2ᴴ * (ω.1 - (E : ℂ) • 1)⁻¹ * ω.2
  have hR' : (Matrix.reindex eR eR ω.1).IsHermitian := hR.submatrix eR.symm
  have hmatR : (hermitianOfFinCoordinates _ (bR p k ω)).1 = Matrix.reindex eR eR ω.1 :=
    hermitianOfFinCoordinates_finCoords hR'
  have hGe : (Matrix.reindex e e G).IsHermitian := hG.submatrix e.symm
  set K := finCoords p.W (Matrix.reindex e e G)
  have hmatK : (hermitianOfFinCoordinates _ K).1 = Matrix.reindex e e G :=
    hermitianOfFinCoordinates_finCoords hGe
  have hMglob : physicalGlobalReducedMatrix (bR p k ω) (bC p k ω) 0 K E =
      Matrix.reindex e e S := by
    unfold physicalGlobalReducedMatrix
    have h2 : (0 : Matrix (Fin p.W) (Fin p.W) ℂ) - (bC p k ω)ᴴ *
        CoareaNative.BlockBand.physicalCoareaResolvent
          (hermitianOfFinCoordinates _ (bR p k ω)).1 E * bC p k ω =
        BlockBand.Coarea.physicalCoareaF (hermitianOfFinCoordinates _ (bR p k ω)).1
          (bC p k ω) 0 E := rfl
    rw [hmatK, h2, hmatR]
    rw [show bC p k ω = Matrix.reindex eR e ω.2 from rfl, physicalCoareaF_reindex_zero]
    have h3 : Matrix.reindex e e G + Matrix.reindex e e
        (BlockBand.Coarea.physicalCoareaF ω.1 ω.2 0 E) =
        Matrix.reindex e e (G + BlockBand.Coarea.physicalCoareaF ω.1 ω.2 0 E) := by
      ext a b; simp
    rw [h3]
    congr 1
    simp only [S, BlockBand.Coarea.physicalCoareaF, BlockBand.Coarea.physicalCoareaResolvent]
    abel
  have hSH : S.IsHermitian :=
    hG.sub (isHermitian_conjTranspose_mul_mul ω.2 (shift_isHermitian' hR E).inv)
  refine ⟨E, ?_, u ∘ e.symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    apply hdetD
    have h := (GaussianRing.det_sub_real_smul_one_eq_zero_iff
      (hermitianOfFinCoordinates _ (bR p k ω)) E).2 ⟨s, hs⟩
    rw [hmatR, reindex_sub_smul_one, Matrix.det_reindex_self] at h
    exact h
  · intro h0
    apply hu0
    funext a
    have := congrFun h0 (e a)
    simpa using this
  · rw [hMglob, reindex_mulVec_comp, hSu]
    rfl
  · intro w' hw'
    have hw : S *ᵥ (w' ∘ e) = (E : ℂ) • (w' ∘ e) := by
      rw [hMglob] at hw'
      have h1 : w' = (w' ∘ e) ∘ e.symm := by funext a; simp
      rw [h1, reindex_mulVec_comp] at hw'
      funext a
      have := congrFun hw' (e a)
      simpa using this
    obtain ⟨c, hc⟩ := hsimp _ hw
    refine ⟨c, ?_⟩
    funext a
    have := congrFun hc (e.symm a)
    simpa using this
  · rw [hMglob]; exact hSH.submatrix e.symm
  · rw [shiftedInertia_eq_negativeCount, hmatR, reindex_sub_smul_one, negativeCount_reindex']
    have hMH : (Matrix.reindex e e S).IsHermitian := hSH.submatrix e.symm
    have h1 := negativeEigenvalueCount_sub_real_smul_one_eq_eigenCount_Iio
      (⟨Matrix.reindex e e S, hMH⟩ : CoareaNative.BlockBand.HermitianMatrix (Fin p.W)) E
    simp only at h1
    have h2 : CoareaNative.BlockBand.eigenCount (⟨physicalGlobalReducedMatrix (bR p k ω)
        (bC p k ω) 0 K E, by rw [hMglob]; exact hMH⟩ :
          CoareaNative.BlockBand.HermitianMatrix (Fin p.W)) (Set.Iio E) =
        CoareaNative.BlockBand.eigenCount (⟨Matrix.reindex e e S, hMH⟩ :
          CoareaNative.BlockBand.HermitianMatrix _) (Set.Iio E) := by
      congr 1
      exact Subtype.ext hMglob
    rw [h2, ← h1, negativeEigenvalueCount_eq_negativeCount, reindex_sub_smul_one,
      negativeCount_reindex']
    omega

/-- `GUE`-a.e. regularity of the reassembled matrix gives the good-state condition. -/
private theorem blockGood_of_ae (α : Fin p.N) (ω : BlockState p k) (hR : ω.1.IsHermitian)
    (hae : ∀ᵐ G ∂gueMeasure (BlockSite p k) (blockTime p),
      (assembleBlock p k ω G).IsHermitian ∧ (assembleBlock p k ω G).charpoly.Separable ∧
      (oneBlockPalmOffBlock p k (assembleBlock p k ω G) -
        ((physicalOrderedEigenvalue p (assembleBlock p k ω G) α : ℝ) : ℂ) • 1).det ≠ 0) :
    BlockGood p k α ω := by
  set e := blockEquiv p k
  set t := blockTime p
  have ht : 0 < t := by
    have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
    exact Real.toNNReal_pos.2 (div_pos p.c_pos hW)
  set S := physicalSelectedSimpleGoodSet α.val (bR p k ω) (bC p k ω)
    (0 : Matrix (Fin p.W) (Fin p.W) ℂ)
  have hV' : (0 : Matrix (Fin p.W) (Fin p.W) ℂ).IsHermitian := isHermitian_zero
  have hSm : MeasurableSet S :=
    measurableSet_physicalSelectedSimpleGoodSet α.val _ _ _ hV'
  have hQm : MeasurableSet {X : Matrix (Fin p.W) (Fin p.W) ℂ | finCoords p.W X ∈ S} :=
    (measurable_finCoords _) hSm
  have hre : Measurable (Matrix.reindex e e : Matrix (BlockSite p k) (BlockSite p k) ℂ → _) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  have h1 : ∀ᵐ G ∂gueMeasure (BlockSite p k) t, finCoords p.W (Matrix.reindex e e G) ∈ S := by
    filter_upwards [hae, ae_isHermitian_gueMeasure (ι := BlockSite p k) t] with G hG hGH
    exact mem_goodSet_of_regular p k α ω hR G hGH hG.1 hG.2.1 hG.2.2
  have h2 : ∀ᵐ X ∂gueMeasure (Fin p.W) t, finCoords p.W X ∈ S := by
    rw [← gueMeasure_map_reindex e t]
    exact (ae_map_iff hre.aemeasurable hQm).2 h1
  rw [gueMeasure_eq_map_withDensity p.W ht] at h2
  have h3 := ae_of_ae_map (measurable_hermitianOfFinCoordinates_val p.W).aemeasurable h2
  rw [ae_withDensity_iff (measurable_hermitianGUEDensity_comp_block p.W t)] at h3
  have h4 : ∀ᵐ x ∂(volume : Measure (HermitianCoordinateSpace p.W)), x ∈ S := by
    filter_upwards [h3] with x hx
    have hpos : hermitianGUEDensity p.W t (hermitianGUEBlock p.W x) ≠ 0 := by
      have hZ : 0 < gueNormalizer p.W t := by unfold gueNormalizer; positivity
      rw [hermitianGUEDensity, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have := hx hpos
    rwa [finCoords_hermitianOfFinCoordinates] at this
  exact ae_iff.1 h4

end Regular

/-!
## The fixed-exterior formula for every one-block splitting law
-/

/-- **Fixed-exterior one-block coarea formula** (the one-block analogue of
`CoareaContract.formula_fixed`, the coarea theorem). For every admissible `p`, model,
rank `α`, block `k`, one-block splitting law and measurable frame: for `Pω`-a.e. `ω`,
simultaneously for every measurable `g ≥ 0`,
`∫ g dGUE_W(c/W) = oneBlockPalmCoareaFiber p k α U ω g`. -/
theorem oneBlockPalm_formula_fixed : ∀ (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (k : ZMod p.n) (Pω : Measure (BlockState p k)), IsBlockSplitting p k model Pω →
    ∀ U, IsBlockFrame p k U →
    ∀ᵐ ω ∂Pω, ∀ g : Matrix (BlockSite p k) (BlockSite p k) ℂ → ℝ≥0∞, Measurable g →
      (∫⁻ G, g G ∂(gueMeasure (BlockSite p k) (blockTime p))) =
        oneBlockPalmCoareaFiber p k α U ω g := by
  intro p model α k Pω hsplit U hU
  have : IsProbabilityMeasure (gueMeasure (BlockSite p k) (blockTime p)) :=
    regularEvent_isProbabilityMeasure_gue (BlockSite p k) (blockTime p)
  have h0 := oneBlockPalm_regular_ae p model
  rw [← hsplit] at h0
  have h1 := ae_of_ae_map (regularEvent_measurable_assembleBlock p k).aemeasurable h0
  have h2 := Measure.ae_ae_of_ae_prod h1
  filter_upwards [h2] with ω hω
  have hGH := ae_isHermitian_gueMeasure (ι := BlockSite p k) (blockTime p)
  obtain ⟨G, hG, -⟩ := (hω.and hGH).exists
  have hR : ω.1.IsHermitian := by
    have h := hG.1.submatrix (Subtype.val : OffBlockSite p k → p.Site)
    rw [← oneBlockPalm_offBlock_assembleBlock p k ω G]
    exact h
  have hgood := blockGood_of_ae p k α ω hR (hω.mono fun G hG => ⟨hG.1, hG.2.1, hG.2.2 α k⟩)
  intro g hg
  exact formula_fixed_of_good p k α U hU ω hR hgood g hg

end BlockBand.Endpoints.Normalization
