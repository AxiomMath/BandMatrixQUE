module

public import Mathlib
public import BlockBand.Wegner.RingBlockModelRing

/-!
# Direct sums of rings as a `BlockModel`

Proves `RingBlockModels` (`ringBlockModels_holds`): a single ring and a direct sum of rings are
block models with independent blocks.

Generic step (`sumModel`, `sumModel_isIndependent`, `sumModel_presents`): for `r` block models
`M i : BlockModel (n i) W` on independent sample spaces (product measure
`Measure.pi (fun i => (M i).P)`), each with independent `GUE_W(c/W)` blocks independent of its
`(D, Y)`, and each presenting a law `μ i` with `Y = 0`, the block-diagonal direct sum (blocks
ordered by `finSigmaFinEquiv`, deformation `directSumBlockCoords n (D i)`, `Y = 0`) has the same
properties for the same `c` and presents `(Measure.pi μ).map (directSumBlockCoords n)`.
Independence across rings comes from the product measure; independence of all bonds from all
blocks from `hasLaw_pi_prod_split`. Applied to the ring presentations
`ringModel` with common `W`, `b` (so `c = 1 - 2b`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

namespace RingBlock

open MeasureTheory ProbabilityTheory
open BlockBand.External
open BlockBand.Internal.Contracts.Inputs (gueMatrixLaw BlockModel)
open BlockBand.Internal.Contracts.InputsRing
open scoped NNReal ComplexOrder

/-!
## The direct-sum matrix
-/

section DirectSum

variable {r W : ℕ} (n : Fin r → ℕ)

theorem directSum_apply (H : ∀ i, Matrix (Fin (n i) × Fin W) (Fin (n i) × Fin W) ℂ)
    (u v : Σ i, Fin (n i)) (s t : Fin W) :
    directSumBlockCoords n H (finSigmaFinEquiv u, s) (finSigmaFinEquiv v, t) =
      if h : u.1 = v.1 then H u.1 (u.2, s) (Fin.cast (by rw [h]) v.2, t) else 0 := by
  have key : ∀ u' v' : Σ i, Fin (n i), u' = u → v' = v →
      (if h : u'.1 = v'.1 then H u'.1 (u'.2, s) (Fin.cast (by rw [h]) v'.2, t) else 0) =
        if h : u.1 = v.1 then H u.1 (u.2, s) (Fin.cast (by rw [h]) v.2, t) else 0 := by
    rintro _ _ rfl rfl
    rfl
  exact key _ _ (Equiv.symm_apply_apply _ _) (Equiv.symm_apply_apply _ _)

theorem directSum_same (H : ∀ i, Matrix (Fin (n i) × Fin W) (Fin (n i) × Fin W) ℂ)
    (i : Fin r) (a a' : Fin (n i)) (s t : Fin W) :
    directSumBlockCoords n H (finSigmaFinEquiv ⟨i, a⟩, s) (finSigmaFinEquiv ⟨i, a'⟩, t) =
      H i (a, s) (a', t) := by
  rw [directSum_apply]
  simp

theorem directSum_ne (H : ∀ i, Matrix (Fin (n i) × Fin W) (Fin (n i) × Fin W) ℂ)
    {i i' : Fin r} (h : i ≠ i') (a : Fin (n i)) (a' : Fin (n i')) (s t : Fin W) :
    directSumBlockCoords n H (finSigmaFinEquiv ⟨i, a⟩, s) (finSigmaFinEquiv ⟨i', a'⟩, t) = 0 := by
  rw [directSum_apply]
  simp [h]

theorem measurable_directSum :
    Measurable (directSumBlockCoords (W := W) n) := by
  rw [Matrix.measurable_iff]
  intro x y
  by_cases h : (finSigmaFinEquiv.symm x.1).1 = (finSigmaFinEquiv.symm y.1).1
  · simp only [directSumBlockCoords, h, ↓reduceDIte]
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp (measurable_pi_apply _))
  · simp only [directSumBlockCoords, h, ↓reduceDIte]
    exact measurable_const

theorem directSum_isHermitian (H : ∀ i, Matrix (Fin (n i) × Fin W) (Fin (n i) × Fin W) ℂ)
    (hH : ∀ i, (H i).IsHermitian) : (directSumBlockCoords n H).IsHermitian := by
  ext ⟨x1, s⟩ ⟨y1, t⟩
  obtain ⟨⟨i, a⟩, rfl⟩ := finSigmaFinEquiv.surjective x1
  obtain ⟨⟨i', a'⟩, rfl⟩ := finSigmaFinEquiv.surjective y1
  rw [Matrix.conjTranspose_apply]
  by_cases h : i = i'
  · subst h
    rw [directSum_same, directSum_same]
    exact (hH i).apply (a, s) (a', t)
  · rw [directSum_ne n H h, directSum_ne n H (Ne.symm h), star_zero]

theorem diagonalBlocks_directSum (H : ∀ i, Matrix (Fin (n i) × Fin W) (Fin (n i) × Fin W) ℂ)
    (k : Fin (∑ i, n i)) :
    diagonalBlocks (directSumBlockCoords n H) k =
      diagonalBlocks (H (finSigmaFinEquiv.symm k).1) (finSigmaFinEquiv.symm k).2 := by
  obtain ⟨⟨i, a⟩, rfl⟩ := finSigmaFinEquiv.surjective k
  ext s t
  simp only [diagonalBlocks]
  generalize hu : finSigmaFinEquiv.symm (finSigmaFinEquiv (⟨i, a⟩ : Σ i, Fin (n i))) = u
  rw [Equiv.symm_apply_apply] at hu
  subst hu
  exact directSum_same n H i a a s t

theorem offDiagonalBlocks_directSum (H : ∀ i, Matrix (Fin (n i) × Fin W) (Fin (n i) × Fin W) ℂ) :
    offDiagonalBlocks (directSumBlockCoords n H) =
      directSumBlockCoords n (fun i => offDiagonalBlocks (H i)) := by
  ext ⟨x1, s⟩ ⟨y1, t⟩
  obtain ⟨⟨i, a⟩, rfl⟩ := finSigmaFinEquiv.surjective x1
  obtain ⟨⟨i', a'⟩, rfl⟩ := finSigmaFinEquiv.surjective y1
  by_cases h : i = i'
  · subst h
    rw [directSum_same]
    simp only [offDiagonalBlocks, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.inj_iff, heq_eq_eq,
      true_and, directSum_same]
  · rw [directSum_ne n _ h]
    simp [offDiagonalBlocks, directSum_ne n H h]

end DirectSum

/-!
## The direct sum of independent block models
-/

section SumModel

variable {r W : ℕ} {n : Fin r → ℕ} (M : ∀ i, BlockModel (n i) W)

/-- The block-diagonal direct sum of independent block models (product sample space), with
blocks ordered by `finSigmaFinEquiv` and `Y = 0`. -/
def sumModel : BlockModel (∑ i, n i) W where
  Ω := ∀ i, (M i).Ω
  P := Measure.pi fun i => (M i).P
  prob := inferInstance
  A := fun w k => (M (finSigmaFinEquiv.symm k).1).A (w (finSigmaFinEquiv.symm k).1)
    (finSigmaFinEquiv.symm k).2
  D := fun w => directSumBlockCoords n fun i => (M i).D (w i)
  Y := fun _ => 0
  measurable_A := measurable_pi_iff.mpr fun _ =>
    ((measurable_pi_apply _).comp (M _).measurable_A).comp (measurable_pi_apply _)
  measurable_D := (measurable_directSum n).comp
    (measurable_pi_iff.mpr fun i => (M i).measurable_D.comp (measurable_pi_apply i))
  measurable_Y := measurable_const
  hermitian_A := fun _ _ => (M _).hermitian_A _ _
  hermitian_D := fun w => directSum_isHermitian n _ fun i => (M i).hermitian_D (w i)
  posSemidef_Y := fun _ => Matrix.PosSemidef.zero

theorem isProb_map {α β : Type} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → β} (hf : AEMeasurable f μ) :
    IsProbabilityMeasure (μ.map f) :=
  (Measure.isProbabilityMeasure_map_iff hf).mpr inferInstance

theorem isProbabilityMeasure_gueMatrixLaw (S : ℝ≥0) : IsProbabilityMeasure (gueMatrixLaw W S) := by
  rw [gueMatrixLaw_eq_map]
  exact isProb_map measurable_gaussianMatrixRaw.aemeasurable

/-- Independence of the direct sum: blocks independent `GUE_W(c/W)`, bonds independent. -/
theorem sumModel_isIndependent (c : ℝ) (hI : ∀ i, (M i).IsIndependent c) :
    (sumModel M).IsIndependent c := by
  set S := Real.toNNReal (c / W)
  have hG := isProbabilityMeasure_gueMatrixLaw (W := W) S
  refine ⟨fun k => ?_, ?_, ?_⟩
  · exact ((hI _).1 _).fun_comp (measurePreserving_eval (fun i => (M i).P) _).hasLaw
  · have hAi : ∀ i, HasLaw (M i).A (Measure.pi fun _ : Fin (n i) => gueMatrixLaw W S) (M i).P :=
      fun i => (hI i).2.1.hasLaw_pi (fun j => (hI i).1 j)
    have hsf : ∀ i, SigmaFinite (((M i).P).map (M i).A) := fun i => by
      rw [(hAi i).map_eq]
      infer_instance
    have hvec : HasLaw (fun (w : ∀ i, (M i).Ω) i => (M i).A (w i))
        (Measure.pi fun i => Measure.pi fun _ : Fin (n i) => gueMatrixLaw W S)
        (Measure.pi fun i => (M i).P) := by
      refine ⟨(measurable_pi_iff.mpr fun i =>
        (M i).measurable_A.comp (measurable_pi_apply i)).aemeasurable, ?_⟩
      rw [Measure.pi_map_pi (fun i => (M i).measurable_A.aemeasurable)]
      congr 1
      funext i
      exact (hAi i).map_eq
    have hm : Measurable (fun (f : ∀ i, Fin (n i) → Matrix (Fin W) (Fin W) ℂ)
        (σ : Σ i, Fin (n i)) => f σ.1 σ.2) :=
      measurable_pi_iff.mpr fun σ => (measurable_pi_apply σ.2).comp (measurable_pi_apply σ.1)
    have hσ := (hasLaw_map (P := Measure.pi fun i => Measure.pi fun _ : Fin (n i) =>
      gueMatrixLaw W S) hm.aemeasurable).fun_comp hvec
    rw [map_uncurry_pi_pi_dep (fun i (_ : Fin (n i)) => gueMatrixLaw W S)] at hσ
    have hi := SingularLogLaw.iIndepFun_of_hasLaw_pi
      (fun σ : Σ i, Fin (n i) => ((measurable_pi_apply σ.2).comp (M σ.1).measurable_A).comp
        (measurable_pi_apply σ.1)) hσ
    exact hi.precomp finSigmaFinEquiv.symm.injective
  · have hDA : ∀ i, IndepFun (M i).D (M i).A (M i).P := fun i =>
      (hI i).2.2.comp measurable_fst measurable_id
    have hpD : ∀ i, IsProbabilityMeasure (((M i).P).map (M i).D) := fun i =>
      isProb_map (M i).measurable_D.aemeasurable
    have hpA : ∀ i, IsProbabilityMeasure (((M i).P).map (M i).A) := fun i =>
      isProb_map (M i).measurable_A.aemeasurable
    have hpDA : ∀ i, IsProbabilityMeasure (((M i).P).map (fun x => ((M i).D x, (M i).A x))) :=
      fun i => isProb_map ((M i).measurable_D.prodMk (M i).measurable_A).aemeasurable
    have hpair : HasLaw (fun (w : ∀ i, (M i).Ω) i => ((M i).D (w i), (M i).A (w i)))
        (Measure.pi fun i => (((M i).P).map (M i).D).prod (((M i).P).map (M i).A))
        (Measure.pi fun i => (M i).P) := by
      refine ⟨(measurable_pi_iff.mpr fun i => ((M i).measurable_D.prodMk
        (M i).measurable_A).comp (measurable_pi_apply i)).aemeasurable, ?_⟩
      rw [Measure.pi_map_pi (fun i => ((M i).measurable_D.prodMk
        (M i).measurable_A).aemeasurable)]
      congr 1
      funext i
      exact (indepFun_iff_map_prod_eq_prod_map_map (M i).measurable_D.aemeasurable
        (M i).measurable_A.aemeasurable).mp (hDA i)
    have hsplit := (hasLaw_pi_prod_split (fun i => ((M i).P).map (M i).D)
      (fun i => ((M i).P).map (M i).A)).comp hpair
    have hmDv : Measurable (fun (w : ∀ i, (M i).Ω) i => (M i).D (w i)) :=
      measurable_pi_iff.mpr fun i => (M i).measurable_D.comp (measurable_pi_apply i)
    have hmAv : Measurable (fun (w : ∀ i, (M i).Ω) i => (M i).A (w i)) :=
      measurable_pi_iff.mpr fun i => (M i).measurable_A.comp (measurable_pi_apply i)
    have hvec : IndepFun (fun (w : ∀ i, (M i).Ω) i => (M i).D (w i))
        (fun (w : ∀ i, (M i).Ω) i => (M i).A (w i)) (Measure.pi fun i => (M i).P) := by
      rw [indepFun_iff_map_prod_eq_prod_map_map hmDv.aemeasurable hmAv.aemeasurable,
        Measure.pi_map_pi (fun i => (M i).measurable_D.aemeasurable),
        Measure.pi_map_pi (fun i => (M i).measurable_A.aemeasurable)]
      exact hsplit.map_eq
    have hφ : Measurable (fun v : (∀ i, Matrix (Fin (n i) × Fin W) (Fin (n i) × Fin W) ℂ) =>
        (directSumBlockCoords n v,
          (0 : Matrix (Fin (∑ i, n i) × Fin W) (Fin (∑ i, n i) × Fin W) ℂ))) :=
      (measurable_directSum n).prodMk measurable_const
    have hψ : Measurable (fun (v : ∀ i, Fin (n i) → Matrix (Fin W) (Fin W) ℂ)
        (k : Fin (∑ i, n i)) => v (finSigmaFinEquiv.symm k).1 (finSigmaFinEquiv.symm k).2) :=
      measurable_pi_iff.mpr fun k =>
        (measurable_pi_apply _).comp (measurable_pi_apply (finSigmaFinEquiv.symm k).1)
    exact hvec.comp hφ hψ

/-- The direct sum presents the law of the direct sum of the presented matrices. -/
theorem sumModel_presents
    (μ : ∀ i, Measure (Matrix (Fin (n i) × Fin W) (Fin (n i) × Fin W) ℂ))
    (hprob : ∀ i, IsProbabilityMeasure (μ i)) (hP : ∀ i, Presents (M i) (μ i)) :
    Presents (sumModel M) ((Measure.pi μ).map (directSumBlockCoords n)) := by
  apply presents_of_pair _ _ (fun _ => rfl)
  have hdo : ∀ k : ℕ, Measurable (fun X : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ =>
      (diagonalBlocks X, offDiagonalBlocks X)) := fun _ =>
    measurable_diagonalBlocks.prodMk measurable_offDiagonalBlocks
  have hpAD : ∀ i, IsProbabilityMeasure (((M i).P).map (fun x => ((M i).A x, (M i).D x))) :=
    fun i => isProb_map ((M i).measurable_A.prodMk (M i).measurable_D).aemeasurable
  have hpμ : ∀ i, IsProbabilityMeasure ((μ i).map
      (fun X => (diagonalBlocks X, offDiagonalBlocks X))) :=
    fun i => isProb_map (hdo _).aemeasurable
  let Φ : (∀ i, (Fin (n i) → Matrix (Fin W) (Fin W) ℂ) ×
      Matrix (Fin (n i) × Fin W) (Fin (n i) × Fin W) ℂ) →
      (Fin (∑ i, n i) → Matrix (Fin W) (Fin W) ℂ) ×
        Matrix (Fin (∑ i, n i) × Fin W) (Fin (∑ i, n i) × Fin W) ℂ :=
    fun z => (fun k => (z (finSigmaFinEquiv.symm k).1).1 (finSigmaFinEquiv.symm k).2,
      directSumBlockCoords n fun i => (z i).2)
  have hΦ : Measurable Φ :=
    (measurable_pi_iff.mpr fun k => (measurable_pi_apply _).comp
      (measurable_fst.comp (measurable_pi_apply _))).prodMk
      ((measurable_directSum n).comp
        (measurable_pi_iff.mpr fun i => measurable_snd.comp (measurable_pi_apply i)))
  have hmpairs : Measurable (fun (w : ∀ i, (M i).Ω) i => ((M i).A (w i), (M i).D (w i))) :=
    measurable_pi_iff.mpr fun i =>
      ((M i).measurable_A.prodMk (M i).measurable_D).comp (measurable_pi_apply i)
  have hmX : Measurable (fun (X : ∀ i, Matrix (Fin (n i) × Fin W) (Fin (n i) × Fin W) ℂ) i =>
      (diagonalBlocks (X i), offDiagonalBlocks (X i))) :=
    measurable_pi_iff.mpr fun i => (hdo _).comp (measurable_pi_apply i)
  have hpairs : (Measure.pi fun i => (M i).P).map
      (fun (w : ∀ i, (M i).Ω) i => ((M i).A (w i), (M i).D (w i))) =
        Measure.pi fun i => (μ i).map (fun X => (diagonalBlocks X, offDiagonalBlocks X)) := by
    rw [Measure.pi_map_pi (fun i => ((M i).measurable_A.prodMk
      (M i).measurable_D).aemeasurable)]
    congr 1
    funext i
    exact (hP i).2.1
  have hμ : (Measure.pi μ).map
      (fun (X : ∀ i, Matrix (Fin (n i) × Fin W) (Fin (n i) × Fin W) ℂ) i =>
        (diagonalBlocks (X i), offDiagonalBlocks (X i))) =
        Measure.pi fun i => (μ i).map (fun X => (diagonalBlocks X, offDiagonalBlocks X)) :=
    Measure.pi_map_pi (fun _ => (hdo _).aemeasurable)
  calc (sumModel M).P.map (fun w => ((sumModel M).A w, (sumModel M).D w))
      = ((Measure.pi fun i => (M i).P).map
          (fun (w : ∀ i, (M i).Ω) i => ((M i).A (w i), (M i).D (w i)))).map Φ := by
        rw [Measure.map_map hΦ hmpairs]
        rfl
    _ = ((Measure.pi μ).map
          (fun (X : ∀ i, Matrix (Fin (n i) × Fin W) (Fin (n i) × Fin W) ℂ) i =>
            (diagonalBlocks (X i), offDiagonalBlocks (X i)))).map Φ := by
        rw [hpairs, hμ]
    _ = (Measure.pi μ).map ((fun X => (diagonalBlocks X, offDiagonalBlocks X)) ∘
          directSumBlockCoords n) := by
        rw [Measure.map_map hΦ hmX]
        congr 1
        funext X
        refine Prod.ext ?_ ?_
        · funext k
          exact (diagonalBlocks_directSum n X k).symm
        · exact (offDiagonalBlocks_directSum n X).symm
    _ = ((Measure.pi μ).map (directSumBlockCoords n)).map
          (fun X => (diagonalBlocks X, offDiagonalBlocks X)) :=
        (Measure.map_map (hdo _) (measurable_directSum n)).symm

end SumModel

end RingBlock

open MeasureTheory BlockBand.Internal.Contracts.InputsRing in

/-- Law: the product `Measure.pi` of the physical laws of `r` rings
with block numbers `nᵢ ≥ 4`, common width `W ≥ 1` and common bond `b ∈ (0, 1/2)`, any
realizations.
The presentation lives on the product sample space; its `Σᵢ nᵢ` blocks (ordered
by `finSigmaFinEquiv`) are the diagonal blocks of the Hermitian versions of the samples,
independent `GUE_W(c/W)` with `c = 1 - 2b` (Johansson coordinate normalization), the deformation
is the direct sum of the bond parts, independent of all blocks, and `Y = 0`; it presents the law
of `⊕ᵢ Hᵢ` in block coordinates.
Uniform in `r`, `nᵢ`, `W`, `b`.
No cited input.
-/
theorem ringSumAsBlockModel_holds : Internal.Contracts.InputsRing.RingSumAsBlockModel := by
  intro r W n b hn hW hb hb' models
  refine ⟨RingBlock.sumModel (fun i => RingBlock.ringModel _ (models i)), ?_, ?_⟩
  · exact RingBlock.sumModel_isIndependent _ (1 - 2 * b)
      (fun i => RingBlock.ringModel_isIndependent _ (models i))
  · have hμ : (Measure.pi (fun i => ((models i).law :
          Measure (ringParameters (n i) W b (hn i) hW hb hb').SiteMatrix))).map
        (fun H => directSumBlockCoords n
          (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i))) =
        (Measure.pi (fun i => ((models i).law :
          Measure (ringParameters (n i) W b (hn i) hW hb hb').SiteMatrix).map
            (toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb')))).map
          (directSumBlockCoords n) := by
      have hm : Measurable (fun (x : ∀ i, (ringParameters (n i) W b (hn i) hW hb hb').SiteMatrix) i =>
          toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (x i)) :=
        measurable_pi_iff.mpr fun i =>
          (RingBlock.measurable_toBlockCoords _).comp (measurable_pi_apply i)
      rw [← Measure.pi_map_pi (fun i => (RingBlock.measurable_toBlockCoords _).aemeasurable)]
      exact (Measure.map_map (RingBlock.measurable_directSum n) hm).symm
    rw [hμ]
    have hprob : ∀ i, IsProbabilityMeasure (((models i).law :
        Measure (ringParameters (n i) W b (hn i) hW hb hb').SiteMatrix).map
          (toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb'))) := fun i =>
      RingBlock.isProb_map (RingBlock.measurable_toBlockCoords _).aemeasurable
    exact RingBlock.sumModel_presents _ _ hprob (fun i => RingBlock.ringModel_presents _ (models i))

/-- `RingBlockModels`: the physical ring
and every finite direct sum of independent physical rings with common `W`, `b` are presented
as `BlockModel`s with independent `GUE_W(c/W)` diagonal blocks (`c = 1 - 2b`), bonds jointly
independent of the blocks and `Y = 0` (`ringAsBlockModel_holds`, `ringSumAsBlockModel_holds`).
Statement about the Gaussian laws only; no cited input or estimate is used.
-/
theorem ringBlockModels_holds : Internal.Contracts.InputsRing.RingBlockModels :=
  ⟨ringAsBlockModel_holds, ringSumAsBlockModel_holds⟩

end BlockBand.Wegner
