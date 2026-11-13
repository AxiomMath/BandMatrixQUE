module

public import BlockBand.Coarea.FixedOmegaCover
public import BlockBand.Coarea.ContractClauses

/-!
# Fixed-`ω` coarea: the deterministic eigenpair change of variables

## Main results

* `lintegral_gueMeasure_eq_finFiber` (Fin-indexed form).
* `fiberIntegrand_reindex`, `physicalCoareaF_reindex`, `physicalCoareaD_reindex`: reindexing.
* **`formula_fixed_of_good`**: for every `ω` with `H_R`, `V` Hermitian and
  `FixedOmegaGood p α i ω`, every `s` with `pairTime p s > 0`, every frame `U` with
  `IsPairFrame p i U` and every measurable `g ≥ 0`,
  `∫⁻ G, g G ∂gueMeasure (PairSite p i) (pairTime p s) = coareaFiber p α i s U (clockSpeed p i) ω g`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.FixedOmega

open Matrix MeasureTheory
open CoareaNative.BlockBand BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw
  BlockBand.Model.Construction
open scoped ENNReal NNReal ComplexConjugate

/-!
## The Fin-indexed change of variables
-/

/-- **Fin-indexed fixed-`ω` coarea** (at `ι = Fin d`): under the good-state condition,
`∫ g dGUE_d(t) = finFiber`. -/
theorem lintegral_gueMeasure_eq_finFiber {dR d : ℕ} (hd : 1 ≤ d) (α : ℕ)
    (R : HermitianCoordinateSpace dR) (C : Matrix (Fin dR) (Fin d) ℂ)
    {V : Matrix (Fin d) (Fin d) ℂ} (hV : V.IsHermitian) {t : ℝ≥0} (ht : 0 < t)
    {U : (Fin d → ℂ) → Matrix (Fin d) (Fin (d - 1)) ℂ} (hU : Measurable U)
    (hUf : ∀ v, l2Norm v = 1 → IsFrameOf v (U v))
    {g : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞} (hg : Measurable g)
    (hgood : volume (physicalSelectedSimpleGoodSet α R C V)ᶜ = 0) :
    ∫⁻ G, g G ∂gueMeasure (Fin d) t = finFiber α R C V t U g := by
  rw [lintegral_gueMeasure_eq_decoderChartIntegrand hd α R C hV ht hg hgood,
    lintegral_decoderChartIntegrand_eq_finFiber hd α R C hV ht hU hUf hg]

/-!
## Reindexing
-/

section Reindex

variable {ι ι' κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [Fintype κ] [DecidableEq κ]

theorem physicalCoareaF_reindex {α α' : Type*} [Fintype α] [DecidableEq α] [Fintype α']
    [DecidableEq α'] (eR : α ≃ α') (eS : ι ≃ ι') (H : Matrix α α ℂ) (C : Matrix α ι ℂ)
    (V : Matrix ι ι ℂ) (E : ℝ) :
    BlockBand.Coarea.physicalCoareaF (Matrix.reindex eR eR H) (Matrix.reindex eR eS C)
        (Matrix.reindex eS eS V) E =
      Matrix.reindex eS eS (BlockBand.Coarea.physicalCoareaF H C V E) := by
  unfold BlockBand.Coarea.physicalCoareaF BlockBand.Coarea.physicalCoareaResolvent
  have h1 : Matrix.reindex eR eR H - (E : ℂ) • 1 = Matrix.reindex eR eR (H - (E : ℂ) • 1) := by
    ext a b; simp [Matrix.one_apply]
  rw [h1, Matrix.inv_reindex, Matrix.conjTranspose_reindex]
  ext a b
  simp only [Matrix.reindex_apply, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  congr 1
  rw [← eR.symm.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [← eR.symm.sum_comp]

theorem physicalCoareaD_reindex {α α' : Type*} [Fintype α] [DecidableEq α] [Fintype α']
    [DecidableEq α'] (eR : α ≃ α') (eS : ι ≃ ι') (H : Matrix α α ℂ) (C : Matrix α ι ℂ)
    (E : ℝ) :
    BlockBand.Coarea.physicalCoareaD (Matrix.reindex eR eR H) (Matrix.reindex eR eS C) E =
      Matrix.reindex eS eS (BlockBand.Coarea.physicalCoareaD H C E) := by
  unfold BlockBand.Coarea.physicalCoareaD BlockBand.Coarea.schurClock
    BlockBand.Coarea.physicalCoareaT BlockBand.Coarea.physicalCoareaResolvent
  have h1 : Matrix.reindex eR eR H - (E : ℂ) • 1 = Matrix.reindex eR eR (H - (E : ℂ) • 1) := by
    ext a b; simp [Matrix.one_apply]
  rw [h1, Matrix.inv_reindex]
  ext a b
  simp only [Matrix.reindex_apply, Matrix.add_apply, Matrix.submatrix_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]
  congr 1
  rw [← eR.symm.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  · congr 1
    rw [← eR.symm.sum_comp]
  · rw [← eR.symm.sum_comp]

theorem dotProduct_reindex_mulVec (e : ι ≃ ι') (v : ι → ℂ) (D : Matrix ι ι ℂ) :
    star (v ∘ e.symm) ⬝ᵥ (Matrix.reindex e e D *ᵥ (v ∘ e.symm)) = star v ⬝ᵥ (D *ᵥ v) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.reindex_apply, Matrix.submatrix_apply,
    Pi.star_apply, Function.comp_apply]
  rw [e.symm.sum_comp (fun a => star (v a) * ∑ x, D a (e.symm x) * v (e.symm x))]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  exact e.symm.sum_comp (fun x => D a x * v x)

theorem l2Norm_comp_symm (e : ι ≃ ι') (v : ι → ℂ) : l2Norm (v ∘ e.symm) = l2Norm v :=
  ProjectiveHaar.l2Norm_comp_equiv e v

theorem regressionFactor_reindex (e : ι ≃ ι') (t E : ℝ) (v : ι → ℂ) (F : Matrix ι ι ℂ) :
    regressionFactor t E (v ∘ e.symm) (Matrix.reindex e e F) = regressionFactor t E v F := by
  unfold regressionFactor
  simp only [dotProduct_reindex_mulVec]
  have h : Matrix.reindex e e F *ᵥ (v ∘ e.symm) - (star v ⬝ᵥ (F *ᵥ v)) • (v ∘ e.symm) =
      (F *ᵥ v - (star v ⬝ᵥ (F *ᵥ v)) • v) ∘ e.symm := by
    funext a
    simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
      Function.comp_apply, Pi.sub_apply, Pi.smul_apply]
    congr 1
    exact e.symm.sum_comp (fun x => F (e.symm a) x * v x)
  rw [h, l2Norm_comp_symm]

/-- Reindexing the frame, the deformation, the vector and the observable leaves the
`G'`-integrand unchanged. -/
theorem fiberIntegrand_reindex (e : ι ≃ ι') (U : Matrix ι κ ℂ) (F : Matrix ι ι ℂ) (E : ℝ)
    (v : ι → ℂ) (nR α : ℕ) (K : ℝ) (g : Matrix ι ι ℂ → ℝ≥0∞) (G' : Matrix κ κ ℂ) :
    fiberIntegrand (Matrix.reindex e (Equiv.refl κ) U) (Matrix.reindex e e F) E (v ∘ e.symm) nR α K
        (fun X => g (Matrix.reindex e.symm e.symm X)) G' =
      fiberIntegrand U F E v nR α K g G' := by
  have hA : (Matrix.reindex e (Equiv.refl κ) U)ᴴ * Matrix.reindex e e F *
      Matrix.reindex e (Equiv.refl κ) U = Uᴴ * F * U := by
    rw [Matrix.conjTranspose_reindex]
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv _ _ _ e.symm _, Matrix.submatrix_mul_equiv _ _ _ e.symm _]
    simp
  have hrec : (E : ℂ) • vecMulVec (v ∘ e.symm) (star (v ∘ e.symm)) +
      Matrix.reindex e (Equiv.refl κ) U * (Uᴴ * F * U + G') *
        (Matrix.reindex e (Equiv.refl κ) U)ᴴ - Matrix.reindex e e F =
      Matrix.reindex e e ((E : ℂ) • vecMulVec v (star v) + U * (Uᴴ * F * U + G') * Uᴴ - F) := by
    rw [Matrix.conjTranspose_reindex]
    ext a b
    simp [Matrix.mul_apply, vecMulVec_apply]
  unfold fiberIntegrand
  rw [hA, hrec]
  simp only [← Matrix.reindex_symm, Equiv.symm_apply_apply]

end Reindex

/-!
## The pair setting
-/

section Pair

variable (p : Parameters) (i : ZMod p.n)

/-- Fixed reindexing of the pair sites `S ≃ Fin (2W)`. -/
def pairEquiv : PairSite p i ≃ Fin (2 * p.W) :=
  Fintype.equivOfCardEq ((ContractClauses.card_pairSite p i).trans (Fintype.card_fin _).symm)

/-- Fixed reindexing of the exterior sites. -/
def extEquiv : ExteriorSite p i ≃ Fin (Fintype.card (ExteriorSite p i)) := Fintype.equivFin _

/-- Real coordinates of a matrix (exact on Hermitian matrices). -/
def finCoords (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) : HermitianCoordinateSpace n :=
  coordsOfMatrix A ∘ (hermitianCoordinateEquivFin n).symm

theorem hermitianOfFinCoordinates_finCoords {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) : (hermitianOfFinCoordinates n (finCoords n A)).1 = A := by
  change hermitianMatrixOfCoordinates (coordsOfMatrix A ∘ (hermitianCoordinateEquivFin n).symm ∘
    hermitianCoordinateEquivFin n) = A
  simp only [Equiv.symm_comp_self, Function.comp_id]
  exact hermitianMatrixOfCoordinates_coordsOfMatrix hA

/-- Exterior coordinates of `ω`. -/
def omegaR (ω : SplitState p i) : HermitianCoordinateSpace (Fintype.card (ExteriorSite p i)) :=
  finCoords _ (Matrix.reindex (extEquiv p i) (extEquiv p i) ω.1)

/-- Coupling of `ω`. -/
def omegaC (ω : SplitState p i) :
    Matrix (Fin (Fintype.card (ExteriorSite p i))) (Fin (2 * p.W)) ℂ :=
  Matrix.reindex (extEquiv p i) (pairEquiv p i) ω.2.1

/-- Retained potential of `ω`. -/
def omegaV (ω : SplitState p i) : Matrix (Fin (2 * p.W)) (Fin (2 * p.W)) ℂ :=
  Matrix.reindex (pairEquiv p i) (pairEquiv p i) ω.2.2

/-- **The explicit good-state condition** on `ω` at rank `α`: the selected-simple good set
of `(H_R, C, V)` (fixed reindexings) has Lebesgue-null complement.
-/
def FixedOmegaGood (α : Fin p.N) (ω : SplitState p i) : Prop :=
  volume (physicalSelectedSimpleGoodSet α.val (omegaR p i ω) (omegaC p i ω) (omegaV p i ω))ᶜ = 0

/-- The frame transported to `Fin (2W)`. -/
def finFrame (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) :
    (Fin (2 * p.W) → ℂ) → Matrix (Fin (2 * p.W)) (Fin (2 * p.W - 1)) ℂ :=
  fun w => Matrix.reindex (pairEquiv p i) (Equiv.refl _) (U (w ∘ pairEquiv p i))

theorem measurable_finFrame {U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ}
    (hU : Measurable U) : Measurable (finFrame p i U) := by
  have hc : Measurable fun w : Fin (2 * p.W) → ℂ => w ∘ pairEquiv p i :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  have hr : Measurable (fun M : Matrix (PairSite p i) (FrameIndex p) ℂ =>
      Matrix.reindex (pairEquiv p i) (Equiv.refl (FrameIndex p)) M) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  exact hr.comp (hU.comp hc)

theorem finFrame_isFrameOf {U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ}
    (hU : IsPairFrame p i U) (w : Fin (2 * p.W) → ℂ) (hw : l2Norm w = 1) :
    IsFrameOf w (finFrame p i U w) := by
  unfold finFrame
  have hw' : l2Norm (w ∘ pairEquiv p i) = 1 := by
    have := l2Norm_comp_symm (pairEquiv p i).symm w
    simpa using this.trans hw
  obtain ⟨h1, h2⟩ := hU.2 (w ∘ pairEquiv p i) hw'
  constructor
  · rw [Matrix.conjTranspose_reindex]
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv _ _ _ (pairEquiv p i).symm _]
    simp [h1]
  · funext j
    have := congrFun h2 j
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Function.comp_apply,
      Pi.zero_apply] at this ⊢
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply]
    rw [← this, ← (pairEquiv p i).sum_comp]
    simp

/-- **The fixed-`ω` eigenpair change of variables** (the core of the coarea theorem,
`CoareaContract.formula_fixed` at a fixed good `ω`). -/
theorem formula_fixed_of_good (α : Fin p.N) (s : ℝ) (hs : 0 < pairTime p s)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : IsPairFrame p i U)
    (ω : SplitState p i) (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian)
    (hgood : FixedOmegaGood p i α ω) (g : PairMatrix p i → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ G, g G ∂gueMeasure (PairSite p i) (pairTime p s) =
      coareaFiber p α i s U (clockSpeed p i) ω g := by
  set e := pairEquiv p i
  set eR := extEquiv p i
  set t := pairTime p s
  have hd : 1 ≤ 2 * p.W := by have := p.W_pos; omega
  have hR' : (Matrix.reindex eR eR ω.1).IsHermitian := hR.submatrix eR.symm
  have hV' : (omegaV p i ω).IsHermitian := hV.submatrix e.symm
  have hmatR : (hermitianOfFinCoordinates _ (omegaR p i ω)).1 = Matrix.reindex eR eR ω.1 :=
    hermitianOfFinCoordinates_finCoords hR'
  set g' : Matrix (Fin (2 * p.W)) (Fin (2 * p.W)) ℂ → ℝ≥0∞ :=
    fun X => g (Matrix.reindex e.symm e.symm X)
  have hre : Measurable (Matrix.reindex e e : PairMatrix p i → _) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  have hre' : Measurable (Matrix.reindex e.symm e.symm :
      Matrix (Fin (2 * p.W)) (Fin (2 * p.W)) ℂ → PairMatrix p i) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  have hg' : Measurable g' := hg.comp hre'
  -- the GUE side
  have hL : ∫⁻ G, g G ∂gueMeasure (PairSite p i) t = ∫⁻ G, g' G ∂gueMeasure (Fin (2 * p.W)) t := by
    rw [← gueMeasure_map_reindex e t, lintegral_map hg' hre]
    refine lintegral_congr fun G => ?_
    simp only [g', ← Matrix.reindex_symm, Equiv.symm_apply_apply]
  rw [hL, lintegral_gueMeasure_eq_finFiber hd α.val (omegaR p i ω) (omegaC p i ω) hV' hs
    (measurable_finFrame p i hU.1) (finFrame_isFrameOf p i hU) hg' hgood]
  -- the fiber side
  unfold finFiber coareaFiber
  refine lintegral_congr fun E => ?_
  have hF : BlockBand.Coarea.physicalCoareaF (hermitianOfFinCoordinates _ (omegaR p i ω)).1
      (omegaC p i ω) (omegaV p i ω) E =
      Matrix.reindex e e (BlockBand.Coarea.physicalCoareaF ω.1 ω.2.1 ω.2.2 E) := by
    rw [hmatR]; exact physicalCoareaF_reindex eR e _ _ _ E
  have hD : BlockBand.Coarea.physicalCoareaD (hermitianOfFinCoordinates _ (omegaR p i ω)).1
      (omegaC p i ω) E = Matrix.reindex e e (BlockBand.Coarea.physicalCoareaD ω.1 ω.2.1 E) := by
    rw [hmatR]; exact physicalCoareaD_reindex eR e _ _ E
  have hnR : negativeCount ((hermitianOfFinCoordinates _ (omegaR p i ω)).1 - (E : ℂ) • 1) =
      negativeCount (ω.1 - (E : ℂ) • 1) := by
    rw [hmatR]
    have h1 : Matrix.reindex eR eR ω.1 - (E : ℂ) • 1 = Matrix.reindex eR eR (ω.1 - (E : ℂ) • 1) := by
      ext a b; simp [Matrix.one_apply]
    rw [h1, negativeCount_reindex eR (M := ω.1 - (E : ℂ) • 1)
      (hR.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E)))]
  simp only [hF, hD, hnR]
  have hmap : (projectiveHaar (PairSite p i)).map (MeasurableEquiv.arrowCongr' e
      (MeasurableEquiv.refl ℂ)) = projectiveHaar (Fin (2 * p.W)) := by
    have := ProjectiveHaar.projectiveHaar_map_comp_equiv e
    convert this using 2
    funext v
    rfl
  rw [← hmap, MeasureTheory.lintegral_map_equiv]
  refine lintegral_congr fun v => ?_
  refine lintegral_congr fun G' => ?_
  have hv : (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl ℂ)) v = v ∘ e.symm := rfl
  have hfr : finFrame p i U (v ∘ e.symm) = Matrix.reindex e (Equiv.refl _) (U v) := by
    unfold finFrame
    congr 2
    funext a
    simp [e]
  rw [hv, hfr, dotProduct_reindex_mulVec, regressionFactor_reindex, fiberIntegrand_reindex]
  rfl

end Pair

end BlockBand.Coarea.FixedOmega
