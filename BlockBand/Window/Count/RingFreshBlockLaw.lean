module

public import BlockBand.Window.Count.RingFreshBlock
public import BlockBand.DeterminantScore.Sector.GUELaw

/-!
# Clause (iii) of the fresh-block split: the law of `(Σ̃, Ã)`

Proof. Under `model.law` the real Gaussian coordinates `X = gaussianExtraction H` are independent
(`iIndepFun_gaussianExtraction`) with the variances of the physical model, and
`H = gaussianReconstruction X` a.s. The coordinates of block `k` (`blockCoord`, indexed by
`HermCoord W`) form the product law `hermGaussian W (c/W)`, whose image under `hermOfCoord` is
`gueMeasure (Fin W) (c/W)` (`map_hermOfCoord_hermGaussian`); `Ã = hermOfCoord (X ∘ blockCoord)` a.s.
Every entry of `H_R` and `C = H_{R,k}` is read off the complementary coordinates, so
`Σ̃ = G(X|_{T})` a.s. for a measurable `G`. Disjoint coordinate blocks of an independent family are
independent (`iIndepFun.indepFun_finset`), hence `law(Σ̃, Ã) = law(Σ̃) ⊗ GUE_W(c/W)`:
`freshBlockLawSplit`. With clauses (i) and (ii) (`ringSchurInertia`, `ringBlockTransport`) this
proves `RingFreshBlockSplitAE` (`ringFreshBlockSplitAE`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open Matrix MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.DeterminantScore.Sector (HermCoord hermOfCoord hermGaussian hermVariance
  hermOfCoord_apply continuous_hermOfCoord map_hermOfCoord_hermGaussian)
open scoped ENNReal NNReal

variable (p : BlockBand.Parameters) (k : ZMod p.n)

/-- The Gaussian coordinate of block `k` carrying the Hermitian coordinate `(a, b)`. -/
def blockCoord (c : HermCoord p.W) : p.GaussianCoordinate :=
  if c.1 = c.2 then .inl (k, c.1)
  else if c.1 < c.2 then .inr ((k, c.1), (k, c.2), false)
  else .inr ((k, c.2), (k, c.1), true)

theorem siteIndex_block_lt_iff (a b : Fin p.W) :
    p.siteIndex (k, a) < p.siteIndex (k, b) ↔ a < b := by
  rw [Fin.lt_def]
  simp only [BlockBand.Parameters.siteIndex]
  omega

/-- Left inverse of `blockCoord`. -/
def blockCoordInv : p.GaussianCoordinate → HermCoord p.W
  | .inl x => (x.2, x.2)
  | .inr (x, y, false) => (x.2, y.2)
  | .inr (x, y, true) => (y.2, x.2)

theorem blockCoordInv_blockCoord (c : HermCoord p.W) :
    blockCoordInv p (blockCoord p k c) = c := by
  rcases c with ⟨a, b⟩
  unfold blockCoord
  split_ifs with h1 h2
  · simp only at h1; subst h1; rfl
  · rfl
  · rfl

theorem blockCoord_injective : Function.Injective (blockCoord p k) :=
  Function.LeftInverse.injective (blockCoordInv_blockCoord p k)

/-- `i` belongs to block `k` (both sites in block `k`). -/
def InBlock (i : p.GaussianCoordinate) : Prop :=
  Sum.elim (fun x : p.Site => x.1 = k) (fun t : p.Site × p.Site × Bool => t.1.1 = k ∧ t.2.1.1 = k) i

theorem inBlock_blockCoord (c : HermCoord p.W) : InBlock p k (blockCoord p k c) := by
  unfold blockCoord
  split_ifs <;> simp [InBlock]

/-- The coordinates of block `k`. -/
def blockCoordSet : Finset p.GaussianCoordinate := Finset.univ.image (blockCoord p k)

theorem inBlock_of_mem_blockCoordSet {i : p.GaussianCoordinate} (hi : i ∈ blockCoordSet p k) :
    InBlock p k i := by
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hi
  exact inBlock_blockCoord p k c

theorem mem_blockCoordSet (c : HermCoord p.W) : blockCoord p k c ∈ blockCoordSet p k :=
  Finset.mem_image_of_mem _ (Finset.mem_univ c)

/-- Entries of `gaussianReconstruction` outside the `kk` block only read coordinates outside
block `k`. -/
theorem gaussianReconstruction_apply_congr {Z Z' : p.GaussianCoordinate → ℝ}
    (h : ∀ i, i ∉ blockCoordSet p k → Z i = Z' i) {x y : p.Site} (hxy : x.1 ≠ k ∨ y.1 ≠ k) :
    p.gaussianReconstruction Z x y = p.gaussianReconstruction Z' x y := by
  have hnot : ∀ i, ¬ InBlock p k i → Z i = Z' i := fun i hi =>
    h i fun hm => hi (inBlock_of_mem_blockCoordSet p k hm)
  have hxy' : ¬ (x.1 = k ∧ y.1 = k) := by tauto
  have hyx' : ¬ (y.1 = k ∧ x.1 = k) := by tauto
  unfold BlockBand.Parameters.gaussianReconstruction
  split_ifs with h1 h2
  · subst h1
    rw [hnot (.inl x) (by simp [InBlock]; tauto)]
  · rw [hnot (.inr (x, y, false)) (by simp [InBlock]; tauto),
      hnot (.inr (x, y, true)) (by simp [InBlock]; tauto)]
  · rw [hnot (.inr (y, x, false)) (by simp [InBlock]; tauto),
      hnot (.inr (y, x, true)) (by simp [InBlock]; tauto)]

theorem gaussianCoordinateVariance_blockCoord (c : HermCoord p.W) :
    p.gaussianCoordinateVariance (blockCoord p k c) =
      hermVariance p.W (Real.toNNReal (p.c / p.W)) c := by
  have hcW : 0 ≤ p.c / p.W := div_nonneg p.c_pos.le (Nat.cast_nonneg _)
  rcases c with ⟨a, b⟩
  apply NNReal.coe_injective
  unfold blockCoord hermVariance
  by_cases hab : a = b
  · subst hab
    simp [BlockBand.Parameters.gaussianCoordinateVariance, BlockBand.Parameters.entryVariance,
      Real.coe_toNNReal _ hcW]
    rfl
  · rcases lt_or_gt_of_ne hab with hlt | hgt
    · simp [hab, hlt, BlockBand.Parameters.gaussianCoordinateVariance,
        BlockBand.Parameters.entryVariance, siteIndex_block_lt_iff, Real.coe_toNNReal _ hcW]
      rfl
    · simp [hab, not_lt_of_gt hgt, hgt, BlockBand.Parameters.gaussianCoordinateVariance,
        BlockBand.Parameters.entryVariance, siteIndex_block_lt_iff, Real.coe_toNNReal _ hcW]
      rfl

/-- The fresh-block coordinates of `H`. -/
def blockCoordVector (H : p.SiteMatrix) : HermCoord p.W → ℝ :=
  fun c => p.gaussianExtraction H (blockCoord p k c)

theorem hasLaw_blockCoordVector (model : p.GaussianRingModel) :
    HasLaw (blockCoordVector p k) (hermGaussian p.W (Real.toNNReal (p.c / p.W)))
      (model.law : Measure p.SiteMatrix) := by
  have hind := model.iIndepFun_gaussianExtraction.precomp (blockCoord_injective p k)
  have h := hind.hasLaw_pi (fun c => model.gaussianExtraction_coordinate_hasLaw (blockCoord p k c))
  simp only [gaussianCoordinateVariance_blockCoord] at h
  exact h

theorem ringFreshBlock_eq_hermOfCoord {H : p.SiteMatrix} (hH : H.IsHermitian) :
    ringFreshBlock p k H = hermOfCoord (blockCoordVector p k H) := by
  ext a b
  have hrec := congrFun (congrFun (p.gaussianReconstruction_gaussianExtraction H hH) (k, a)) (k, b)
  simp only [ringFreshBlock, reindex_apply, submatrix_apply, onBlockMatrix, blockFinEquiv,
    Equiv.coe_fn_symm_mk]
  rw [← hrec, hermOfCoord_apply]
  simp only [BlockBand.Parameters.gaussianReconstruction, blockCoordVector, blockCoord,
    siteIndex_block_lt_iff, Prod.mk.injEq, true_and]
  by_cases hab : a = b
  · subst hab; simp
  · rcases lt_or_gt_of_ne hab with hlt | hgt
    · simp [hab, Ne.symm hab, hlt, not_lt_of_gt hlt]; ring
    · have hba : b ≠ a := Ne.symm hab
      simp [hab, hba, hgt, not_lt_of_gt hgt]; ring

/-!
## The complementary coordinates
-/

/-- Extension by zero from the coordinates off block `k`. -/
def extendOff (y : {i // i ∈ (blockCoordSet p k)ᶜ} → ℝ) : p.GaussianCoordinate → ℝ :=
  fun i => if h : i ∈ (blockCoordSet p k)ᶜ then y ⟨i, h⟩ else 0

theorem measurable_extendOff : Measurable (extendOff p k) := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases h : i ∈ (blockCoordSet p k)ᶜ
  · simp only [extendOff, h, dite_true]; exact measurable_pi_apply _
  · simp only [extendOff, h, dite_false]; exact measurable_const

/-- `Σ̃` as a function of the coordinates off block `k`. -/
def schurOfOff (E : ℝ) (y : {i // i ∈ (blockCoordSet p k)ᶜ} → ℝ) :
    Matrix (Fin p.W) (Fin p.W) ℂ :=
  ringSchurSg p k E (p.gaussianReconstruction (extendOff p k y))

theorem measurable_schurOfOff (E : ℝ) : Measurable (schurOfOff p k E) :=
  (measurable_ringSchurSg p k E).comp
    (p.measurable_gaussianReconstruction.comp (measurable_extendOff p k))

theorem ringSchurSg_congr (E : ℝ) {H H' : p.SiteMatrix}
    (h1 : offBlockMatrix p k H = offBlockMatrix p k H')
    (h2 : offOnCoupling p k H = offOnCoupling p k H') :
    ringSchurSg p k E H = ringSchurSg p k E H' := by
  simp only [ringSchurSg, oneBlockComplement_eq, h1, h2]

theorem ringSchurSg_eq_schurOfOff (E : ℝ) {H : p.SiteMatrix} (hH : H.IsHermitian) :
    ringSchurSg p k E H = schurOfOff p k E (fun i => p.gaussianExtraction H i.1) := by
  have hZ : ∀ i, i ∉ blockCoordSet p k →
      extendOff p k (fun i => p.gaussianExtraction H i.1) i = p.gaussianExtraction H i := by
    intro i hi
    have hi' : i ∈ (blockCoordSet p k)ᶜ := Finset.mem_compl.mpr hi
    simp [extendOff, hi']
  have hrec := p.gaussianReconstruction_gaussianExtraction H hH
  unfold schurOfOff
  apply ringSchurSg_congr
  · ext x y
    simp only [offBlockMatrix]
    rw [gaussianReconstruction_apply_congr p k hZ (Or.inl x.2), hrec]
  · ext x y
    simp only [offOnCoupling]
    rw [gaussianReconstruction_apply_congr p k hZ (Or.inl x.2), hrec]

/-!
## The law split
-/

/-- Clause (iii): under the physical law, `law(Σ̃, Ã) = law(Σ̃) ⊗ GUE_W(c/W)`. -/
theorem freshBlockLawSplit : FreshBlockLawSplit := by
  intro p model k E
  set μ := (model.law : Measure p.SiteMatrix)
  set S := blockCoordSet p k
  set T := (blockCoordSet p k)ᶜ
  have hmeasX : ∀ i, Measurable fun H : p.SiteMatrix => p.gaussianExtraction H i :=
    fun i => (measurable_pi_apply i).comp p.measurable_gaussianExtraction
  have hind := model.iIndepFun_gaussianExtraction.indepFun_finset S T
    disjoint_compl_right hmeasX
  let πA : ({i // i ∈ S} → ℝ) → HermCoord p.W → ℝ := fun z c => z ⟨blockCoord p k c,
    mem_blockCoordSet p k c⟩
  have hπA : Measurable πA := measurable_pi_iff.mpr fun c => measurable_pi_apply _
  have hind2 := hind.symm.comp (measurable_schurOfOff p k E)
    (continuous_hermOfCoord.measurable.comp hπA)
  have hSg : ringSchurSg p k E =ᵐ[μ]
      (schurOfOff p k E ∘ fun H (i : {i // i ∈ T}) => p.gaussianExtraction H i.1) := by
    filter_upwards [model.isPhysical.1] with H hH
    exact ringSchurSg_eq_schurOfOff p k E hH
  have hAf : ringFreshBlock p k =ᵐ[μ]
      ((hermOfCoord ∘ πA) ∘ fun H (i : {i // i ∈ S}) => p.gaussianExtraction H i.1) := by
    filter_upwards [model.isPhysical.1] with H hH
    exact ringFreshBlock_eq_hermOfCoord p k hH
  have hmS : Measurable (schurOfOff p k E ∘ fun H (i : {i // i ∈ T}) =>
      p.gaussianExtraction H i.1) :=
    (measurable_schurOfOff p k E).comp (measurable_pi_iff.mpr fun i => hmeasX i.1)
  have hmA : Measurable ((hermOfCoord ∘ πA) ∘ fun H (i : {i // i ∈ S}) =>
      p.gaussianExtraction H i.1) :=
    (continuous_hermOfCoord.measurable.comp hπA).comp (measurable_pi_iff.mpr fun i => hmeasX i.1)
  rw [Measure.map_congr (hSg.prodMk hAf), Measure.map_congr hSg,
    (indepFun_iff_map_prod_eq_prod_map_map hmS.aemeasurable hmA.aemeasurable).mp hind2]
  congr 1
  have hYA : (πA ∘ fun H (i : {i // i ∈ S}) => p.gaussianExtraction H i.1) =
      blockCoordVector p k := rfl
  rw [Function.comp_assoc, ← Measure.map_map continuous_hermOfCoord.measurable
      (hπA.comp (measurable_pi_iff.mpr fun i => hmeasX i.1)), hYA,
    (hasLaw_blockCoordVector p k model).map_eq, map_hermOfCoord_hermGaussian]

/-- The almost-sure fresh-block split holds: clauses (i), (ii) and (iii) all hold. -/
theorem ringFreshBlockSplitAE : RingFreshBlockSplitAE :=
  ringFreshBlockSplitAE_of_lawSplit freshBlockLawSplit

end BlockBand.Window.Count
