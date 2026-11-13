module

public import BlockBand.LocalWindow.LawBridgeStatement
public import BlockBand.LocalWindow.ProofETHWindow

/-!
# The external ETH theorem for the fresh pair block

Conditionally on the exterior data `ω`, the external ETH theorem applied to the fresh `GUE` pair
block, transported from `Fin (2W)` to the pair sites, for part (ii) of the physical local-window
lemma.

## Main results

* `measurableEmbedding_pairSample`: `pairSample p i s` (`W ↦ reindex e⁻¹ e⁻¹ (√s W)`) is a
  measurable embedding for `s > 0`, with range the Hermitian pair matrices;
* `pairEigvec`, `pairEigval`, `isOrthonormalFamily_pairEigvec`, `mulVec_pairEigvec`: the eigenpairs
  of a Hermitian pair matrix read off an eigenpair selection, labelled by `PairSite p i`;
* `gue_not_pairETHGood_le` (**pair ETH**): for a Hermitian pair deformation `K` with
  `s^{-1/2}‖K‖ ≤ C (2W)^A`, `s` in a fixed compact set, any branch `M` of `K` (reindexed)
  with a regular window at `E₀`, any typical spacing and selection, and any Hermitian contraction
  `J` on the pair, the `G`-probability that some pair of eigenvalues of `K + G` in
  `[E₀ - h, E₀ + h]`, `h = (2W)^{-1+β}`, has overlap error above `(2W)^ε (2W)^{-1/2}` is at most
  `(2W)^{-D}`. No measurability of the bad event is needed (the image of an arbitrary set under a
  measurable embedding).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofETH

open MeasureTheory Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.LawBridge
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-!
## Reindexing and the operator norm
-/

section Norm

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem toEuclideanLin_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ κ) :
    Matrix.toEuclideanLin (reindex e e A) v =
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin A ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm v)) := by
  ext k
  simp [mulVec, dotProduct, reindex_apply, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply]

/-- The `L²` operator norm does not increase under reindexing. -/
theorem opNorm_reindex_le (e : ι ≃ κ) (A : Matrix ι ι ℂ) : ‖reindex e e A‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_def, Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  change ‖Matrix.toEuclideanLin (reindex e e A) v‖ ≤ _
  rw [toEuclideanLin_reindex, LinearIsometryEquiv.norm_map]
  calc _ ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖ *
        ‖(LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm v‖ :=
        ContinuousLinearMap.le_opNorm (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) _
    _ = _ := by rw [LinearIsometryEquiv.norm_map]; rfl

/-- The `L²` operator norm is invariant under reindexing. -/
theorem opNorm_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) : ‖reindex e e A‖ = ‖A‖ := by
  refine le_antisymm (opNorm_reindex_le e A) ?_
  have h := opNorm_reindex_le e.symm (reindex e e A)
  rwa [reindex_apply, reindex_apply, submatrix_submatrix, Equiv.self_comp_symm,
    submatrix_id_id] at h

theorem isHermitian_reindex (e : ι ≃ κ) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (reindex e e A).IsHermitian := by
  rw [reindex_apply]; exact hA.submatrix _

theorem measurable_reindex (e : ι ≃ κ) :
    Measurable (fun A : Matrix ι ι ℂ => reindex e e A) := by
  refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
  simp only [reindex_apply, submatrix_apply]
  exact (measurable_pi_apply _).comp (measurable_pi_apply _)

/-- The Hermitian matrices form a measurable set. -/
theorem measurableSet_isHermitian : MeasurableSet {A : Matrix ι ι ℂ | A.IsHermitian} := by
  have e : {A : Matrix ι ι ℂ | A.IsHermitian} =
      ⋂ a : ι, ⋂ b : ι, {A : Matrix ι ι ℂ | star (A b a) = A a b} := by
    ext A
    simp only [mem_iInter]
    constructor
    · intro h a b
      have := congrFun (congrFun h a) b
      simpa [conjTranspose_apply] using this
    · intro h; ext a b; simpa [conjTranspose_apply] using h a b
  rw [e]
  refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => ?_
  have h1 : Measurable fun A : Matrix ι ι ℂ => A b a :=
    (measurable_pi_apply _).comp (measurable_pi_apply _)
  have h2 : Measurable fun A : Matrix ι ι ℂ => A a b :=
    (measurable_pi_apply _).comp (measurable_pi_apply _)
  exact measurableSet_eq_fun (Complex.continuous_conj.measurable.comp h1) h2

end Norm

/-!
## The pair sample is a measurable embedding
-/

section Embedding

variable (p : Parameters) (i : ZMod p.n)

theorem measurable_pairSample_ETH (s : ℝ) : Measurable (pairSample p i s) := by
  have hre : Measurable (reindex (pairEquiv p i).symm (pairEquiv p i).symm :
      Matrix (Fin (2 * p.W)) (Fin (2 * p.W)) ℂ → PairMatrix p i) :=
    measurable_reindex (pairEquiv p i).symm
  exact hre.comp ((continuous_const_smul _).measurable.comp measurable_subtype_coe)

theorem isHermitian_symm_part {ι : Type} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) :
    ((1 / 2 : ℂ) • (G + Gᴴ)).IsHermitian :=
  (isHermitian_add_transpose_self G).smul (by simp [IsSelfAdjoint])

/-- The inverse of `pairSample p i s` on Hermitian pair matrices:
`G ↦ (√s)⁻¹ reindex e e ((G + G*)/2)`. -/
def pairUnsample (s : ℝ) (G : PairMatrix p i) : CEH.SourceHermitian (2 * p.W) :=
  ⟨(((Real.sqrt s)⁻¹ : ℝ) : ℂ) •
      reindex (pairEquiv p i) (pairEquiv p i) ((1 / 2 : ℂ) • (G + Gᴴ)),
    (isHermitian_reindex _ (isHermitian_symm_part G)).smul
      (by simp [IsSelfAdjoint, Complex.conj_ofReal])⟩

theorem measurable_pairUnsample (s : ℝ) : Measurable (pairUnsample p i s) := by
  refine Measurable.subtype_mk ?_
  refine (continuous_const_smul _).measurable.comp ((measurable_reindex _).comp ?_)
  refine (continuous_const_smul _).measurable.comp ?_
  exact measurable_id.add (Continuous.measurable continuous_id.matrix_conjTranspose)

theorem isHermitian_pairSample (s : ℝ) (W : CEH.SourceHermitian (2 * p.W)) :
    (pairSample p i s W).IsHermitian := by
  unfold pairSample
  exact isHermitian_reindex _ (W.2.smul (by simp [IsSelfAdjoint, Complex.conj_ofReal]))

theorem pairSample_pairUnsample {s : ℝ} (hs : 0 < s) {G : PairMatrix p i} (hG : G.IsHermitian) :
    pairSample p i s (pairUnsample p i s G) = G := by
  have hsq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hsym : (1 / 2 : ℂ) • (G + Gᴴ) = G := by
    rw [hG.eq]; rw [← two_smul ℂ G, smul_smul]; norm_num
  unfold pairSample pairUnsample
  simp only
  rw [hsym, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hsq, Complex.ofReal_one, one_smul]
  ext a b
  simp [reindex_apply]

theorem pairUnsample_pairSample {s : ℝ} (hs : 0 < s) (W : CEH.SourceHermitian (2 * p.W)) :
    pairUnsample p i s (pairSample p i s W) = W := by
  have hsq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hG := isHermitian_pairSample p i s W
  apply Subtype.ext
  have hsym : (1 / 2 : ℂ) • (pairSample p i s W + (pairSample p i s W)ᴴ) = pairSample p i s W := by
    rw [hG.eq]; rw [← two_smul ℂ (pairSample p i s W), smul_smul]; norm_num
  unfold pairUnsample
  simp only
  rw [hsym]
  unfold pairSample
  have e1 : reindex (pairEquiv p i) (pairEquiv p i) (reindex (pairEquiv p i).symm
      (pairEquiv p i).symm (((Real.sqrt s : ℝ) : ℂ) • W.1)) = ((Real.sqrt s : ℝ) : ℂ) • W.1 := by
    ext a b; simp [reindex_apply]
  rw [e1, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hsq, Complex.ofReal_one, one_smul]

theorem range_pairSample {s : ℝ} (hs : 0 < s) :
    range (pairSample p i s) = {G : PairMatrix p i | G.IsHermitian} := by
  ext G
  constructor
  · rintro ⟨W, rfl⟩; exact isHermitian_pairSample p i s W
  · intro hG; exact ⟨pairUnsample p i s G, pairSample_pairUnsample p i hs hG⟩

/-- **`pairSample` is a measurable embedding** for `s > 0` (range: the Hermitian matrices). -/
theorem measurableEmbedding_pairSample {s : ℝ} (hs : 0 < s) :
    MeasurableEmbedding (pairSample p i s) := by
  refine MeasurableEmbedding.of_measurable_inverse (measurable_pairSample_ETH p i s) ?_
    (measurable_pairUnsample p i s) (pairUnsample_pairSample p i hs)
  rw [range_pairSample p i hs]
  exact measurableSet_isHermitian

/-- **Images under the pair sample**: for every set `S` of native
samples, `GUE_d(s/d)(pairSample '' S) = gueSourceLaw (2W) S` (no measurability needed).
-/
theorem gueMeasure_image_pairSample (hBridge : PairGUELawBridgeStatement) {s : ℝ} (hs : 0 < s)
    (S : Set (CEH.SourceHermitian (2 * p.W))) :
    gueMeasure (PairSite p i) (pairTime p s) (pairSample p i s '' S) = gueSourceLaw (2 * p.W) S := by
  rw [hBridge p i s hs, (measurableEmbedding_pairSample p i hs).map_apply,
    (measurableEmbedding_pairSample p i hs).injective.preimage_image]

/-- The fresh pair block is almost surely Hermitian (law bridge). -/
theorem gueMeasure_not_isHermitian (hBridge : PairGUELawBridgeStatement) {s : ℝ} (hs : 0 < s) :
    gueMeasure (PairSite p i) (pairTime p s) {G : PairMatrix p i | ¬ G.IsHermitian} = 0 := by
  rw [hBridge p i s hs, (measurableEmbedding_pairSample p i hs).map_apply]
  have : pairSample p i s ⁻¹' {G : PairMatrix p i | ¬ G.IsHermitian} = ∅ := by
    ext W; simp [isHermitian_pairSample]
  rw [this, measure_empty]

end Embedding

/-!
## Pair eigenpairs from a selection
-/

section Eigen

variable {p : Parameters} {i : ZMod p.n}

/-- A Hermitian pair matrix as a CEH Hermitian matrix (`reindex e e`, `e = pairEquiv`). -/
def toSourceHermitian (X : PairMatrix p i) (hX : X.IsHermitian) : CEH.SourceHermitian (2 * p.W) :=
  ⟨reindex (pairEquiv p i) (pairEquiv p i) X, isHermitian_reindex _ hX⟩

/-- The `k`-th selected eigenvector of a Hermitian pair matrix, in pair coordinates and with pair
labels (`k ↦ e k`). -/
def pairEigvec (sel : CEH.EigenpairSelection (2 * p.W)) (X : PairMatrix p i) (hX : X.IsHermitian)
    (k : PairSite p i) : PairSite p i → ℂ :=
  fun x => sel.eigenvector (toSourceHermitian X hX) (pairEquiv p i k) (pairEquiv p i x)

/-- The `k`-th selected eigenvalue of a Hermitian pair matrix (pair labels). -/
def pairEigval (sel : CEH.EigenpairSelection (2 * p.W)) (X : PairMatrix p i) (hX : X.IsHermitian)
    (k : PairSite p i) : ℝ :=
  sel.eigenvalue (toSourceHermitian X hX) (pairEquiv p i k)

theorem star_comp_dotProduct (e : PairSite p i ≃ Fin (2 * p.W)) (u v : Fin (2 * p.W) → ℂ) :
    star (fun x => u (e x)) ⬝ᵥ (fun x => v (e x)) = star u ⬝ᵥ v := by
  unfold dotProduct
  exact e.sum_comp (fun a => star u a * v a)

theorem mulVec_comp (e : PairSite p i ≃ Fin (2 * p.W)) (J : PairMatrix p i)
    (v : Fin (2 * p.W) → ℂ) :
    (J *ᵥ fun x => v (e x)) = fun x => (reindex e e J *ᵥ v) (e x) := by
  ext x
  unfold mulVec dotProduct
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rw [← e.sum_comp (fun b => J x (e.symm b) * v b)]
  simp only [Equiv.symm_apply_apply]

/-- The pair matrix element along transported vectors is the one. -/
theorem pair_matrixElement (e : PairSite p i ≃ Fin (2 * p.W)) (J : PairMatrix p i)
    (u v : Fin (2 * p.W) → ℂ) :
    star (fun x => u (e x)) ⬝ᵥ (J *ᵥ fun x => v (e x)) =
      CEH.sourceMatrixElement (reindex e e J) u v := by
  rw [mulVec_comp, star_comp_dotProduct]; rfl

theorem isOrthonormalFamily_pairEigvec (sel : CEH.EigenpairSelection (2 * p.W))
    (X : PairMatrix p i) (hX : X.IsHermitian) : IsOrthonormalFamily (pairEigvec sel X hX) := by
  intro k l
  unfold pairEigvec
  rw [star_comp_dotProduct (pairEquiv p i), sel.orthonormal]
  by_cases h : k = l
  · simp [h]
  · simp [h, (pairEquiv p i).injective.ne h]

theorem mulVec_pairEigvec (sel : CEH.EigenpairSelection (2 * p.W)) (X : PairMatrix p i)
    (hX : X.IsHermitian) (k : PairSite p i) :
    X *ᵥ pairEigvec sel X hX k = (pairEigval sel X hX k : ℂ) • pairEigvec sel X hX k := by
  unfold pairEigvec pairEigval
  rw [mulVec_comp (pairEquiv p i)]
  have h := sel.eigen_equation (toSourceHermitian X hX) (pairEquiv p i k)
  ext x
  have hx := congrFun h (pairEquiv p i x)
  simp only [Pi.smul_apply] at hx ⊢
  exact hx

end Eigen

/-!
## The pair ETH
-/

section ETH

variable {p : Parameters} {i : ZMod p.n}

/-- The ETH centre `⟨Γ(x + i N^ξ η_f(x)) J⟩` of the external ETH theorem for a pair
observable `J` (reindexed to the sample space). -/
def ethCentre {s : ℝ} {F : CEH.SourceHermitian (2 * p.W)} (M : CEH.MDEBranch (Real.sqrt s) F)
    (spacing : CEH.TypicalSpacing M) (ξ : ℝ) (J : PairMatrix p i) (x : ℝ) : ℂ :=
  CEH.normalizedTrace (CEH.gammaMatrix (M.matrix (CEH.inflatedSpectralPoint spacing ξ x)) *
    reindex (pairEquiv p i) (pairEquiv p i) J)

/-- **The pair ETH conclusion** for `K + G` (transported to the pair): `G` is
Hermitian and for all eigenvalue labels `k, l` of `K + G` whose selected eigenvalues lie in
`[E₀ - h, E₀ + h]`, `h = (2W)^{-1+β}`, the overlap error is at most `(2W)^ε (2W)^{-1/2}`. -/
def PairETHGood {s : ℝ} (K : PairMatrix p i) (hK : K.IsHermitian)
    (M : CEH.MDEBranch (Real.sqrt s) (toSourceHermitian K hK)) (spacing : CEH.TypicalSpacing M)
    (sel : CEH.EigenpairSelection (2 * p.W)) (E₀ β ξ ε : ℝ) (J G : PairMatrix p i) : Prop :=
  ∃ hG : G.IsHermitian, ∀ k l : PairSite p i,
    pairEigval sel (K + G) (hK.add hG) k ∈
        Icc (E₀ - ((2 * p.W : ℕ) : ℝ) ^ (-1 + β)) (E₀ + ((2 * p.W : ℕ) : ℝ) ^ (-1 + β)) →
    pairEigval sel (K + G) (hK.add hG) l ∈
        Icc (E₀ - ((2 * p.W : ℕ) : ℝ) ^ (-1 + β)) (E₀ + ((2 * p.W : ℕ) : ℝ) ^ (-1 + β)) →
    ‖star (pairEigvec sel (K + G) (hK.add hG) k) ⬝ᵥ (J *ᵥ pairEigvec sel (K + G) (hK.add hG) l) -
        (if k = l then ethCentre M spacing ξ J (pairEigval sel (K + G) (hK.add hG) k) else 0)‖ ≤
      ((2 * p.W : ℕ) : ℝ) ^ ε * ((2 * p.W : ℕ) : ℝ) ^ (-(1 : ℝ) / 2)

theorem deformedHermitian_pairUnsample {s : ℝ} (hs : 0 < s) {K G : PairMatrix p i}
    (hK : K.IsHermitian) (hG : G.IsHermitian) :
    CEH.deformedHermitian (Real.sqrt s) (toSourceHermitian K hK) (pairUnsample p i s G) =
      toSourceHermitian (K + G) (hK.add hG) := by
  have hsq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hsym : (1 / 2 : ℂ) • (G + Gᴴ) = G := by
    rw [hG.eq]; rw [← two_smul ℂ G, smul_smul]; norm_num
  apply Subtype.ext
  unfold CEH.deformedHermitian CEH.deformedMatrix toSourceHermitian pairUnsample
  simp only
  rw [hsym, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hsq, Complex.ofReal_one, one_smul]
  ext a b
  simp [reindex_apply]

/-- Off the ETH bad event (`Inputs.ethBadEvent`), the pair conclusion holds. -/
theorem pairETHGood_of_not_mem {s : ℝ} (hs : 0 < s) {K : PairMatrix p i} (hK : K.IsHermitian)
    (M : CEH.MDEBranch (Real.sqrt s) (toSourceHermitian K hK)) (spacing : CEH.TypicalSpacing M)
    (sel : CEH.EigenpairSelection (2 * p.W)) (E₀ β ξ ε : ℝ) (J : PairMatrix p i)
    {G : PairMatrix p i} (hG : G.IsHermitian)
    (hnot : pairUnsample p i s G ∉
      ethBadEvent M spacing sel E₀ β ξ ε (reindex (pairEquiv p i) (pairEquiv p i) J)) :
    PairETHGood K hK M spacing sel E₀ β ξ ε J G := by
  refine ⟨hG, fun k l hk hl => ?_⟩
  by_contra hlt
  push Not at hlt
  apply hnot
  unfold ethBadEvent
  refine ⟨pairEquiv p i k, pairEquiv p i l, ?_⟩
  rw [deformedHermitian_pairUnsample hs hK hG]
  refine ⟨hk, hl, ?_⟩
  have helt := pair_matrixElement (pairEquiv p i) J
    (sel.eigenvector (toSourceHermitian (K + G) (hK.add hG)) (pairEquiv p i k))
    (sel.eigenvector (toSourceHermitian (K + G) (hK.add hG)) (pairEquiv p i l))
  unfold pairEigvec at hlt
  rw [helt] at hlt
  unfold ethCentre pairEigval at hlt
  by_cases hkl : k = l
  · subst hkl; simpa using hlt
  · simpa [hkl, (pairEquiv p i).injective.ne hkl] using hlt

/-- Fixed
`A, C, [sLo, sHi] ⊂ (0, ∞), r, K_reg` first; then `β₀ > 0`; then `0 < ξ < β < β₀`, `ε, D > 0`;
then `N₀`.
Uniformly in `p, i` with `2W ≥ N₀`, `s ∈ [sLo, sHi]`, Hermitian pair deformations
`K` with `s^{-1/2}‖K‖ ≤ C (2W)^A`, branches `M` of `K` (reindexed) with
`RegularWindow M E₀ r K_reg`, typical spacings, eigenpair selections and Hermitian pair
contractions `J`: under `G ~ GUE_{2W}(s/2W)`, the probability that `PairETHGood` fails is at most
`(2W)^{-D}`.
-/
theorem gue_not_pairETHGood_le (hETH : ExternalETH) (hBridge : PairGUELawBridgeStatement)
    (A C sLo sHi r Kr : ℝ) (hsLo : 0 < sLo) (hsHi : sLo ≤ sHi) (hr : 0 < r) (hKr : 0 < Kr) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ξ : ℝ, 0 < ξ → ξ < β → β < β₀ → ∀ ε D : ℝ, 0 < ε → 0 < D →
      ∃ N₀ : ℕ, ∀ (p : Parameters) (i : ZMod p.n), N₀ ≤ 2 * p.W → ∀ s ∈ Icc sLo sHi,
        ∀ (K : PairMatrix p i) (hK : K.IsHermitian),
          (Real.sqrt s)⁻¹ * ‖K‖ ≤ C * ((2 * p.W : ℕ) : ℝ) ^ A →
        ∀ (M : CEH.MDEBranch (Real.sqrt s) (toSourceHermitian K hK)) (E₀ : ℝ),
          RegularWindow M E₀ r Kr →
        ∀ (spacing : CEH.TypicalSpacing M) (sel : CEH.EigenpairSelection (2 * p.W))
          (J : PairMatrix p i), J.IsHermitian → ‖J‖ ≤ 1 →
          gueMeasure (PairSite p i) (pairTime p s)
              {G | ¬ PairETHGood K hK M spacing sel E₀ β ξ ε J G} ≤
            ENNReal.ofReal (((2 * p.W : ℕ) : ℝ) ^ (-D)) := by
  obtain ⟨β₀, hβ₀, h⟩ := hETH A C sLo sHi r Kr hsLo hsHi hr hKr
  refine ⟨β₀, hβ₀, fun β ξ hξ hξβ hβ ε D hε hD => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h β ξ hξ hξβ hβ ε D hε hD
  refine ⟨N₀, fun p i hN s hsI K hK hKn M E₀ hreg spacing sel J hJ hJn => ?_⟩
  have hs : 0 < s := hsLo.trans_le hsI.1
  set J' := reindex (pairEquiv p i) (pairEquiv p i) J
  have hJ' : J'.IsHermitian := isHermitian_reindex _ hJ
  have hJ'n : ‖J'‖ ≤ 1 := (opNorm_reindex_le _ J).trans hJn
  have hKn' : (Real.sqrt s)⁻¹ * ‖(toSourceHermitian K hK).1‖ ≤ C * ((2 * p.W : ℕ) : ℝ) ^ A := by
    unfold toSourceHermitian; simp only; rwa [opNorm_reindex]
  have hbad := hN₀ (2 * p.W) hN s hsI (toSourceHermitian K hK) hKn' M E₀ hreg spacing sel J' hJ'
    hJ'n
  have hsub : {G | ¬ PairETHGood K hK M spacing sel E₀ β ξ ε J G} ⊆
      pairSample p i s '' ethBadEvent M spacing sel E₀ β ξ ε J' ∪
        {G : PairMatrix p i | ¬ G.IsHermitian} := by
    intro G hG
    by_cases hGH : G.IsHermitian
    · left
      refine ⟨pairUnsample p i s G, ?_, pairSample_pairUnsample p i hs hGH⟩
      by_contra hn
      exact hG (pairETHGood_of_not_mem hs hK M spacing sel E₀ β ξ ε J hGH hn)
    · right; exact hGH
  calc gueMeasure (PairSite p i) (pairTime p s) {G | ¬ PairETHGood K hK M spacing sel E₀ β ξ ε J G}
      ≤ gueMeasure (PairSite p i) (pairTime p s)
          (pairSample p i s '' ethBadEvent M spacing sel E₀ β ξ ε J' ∪
            {G : PairMatrix p i | ¬ G.IsHermitian}) := measure_mono hsub
    _ ≤ gueMeasure (PairSite p i) (pairTime p s)
          (pairSample p i s '' ethBadEvent M spacing sel E₀ β ξ ε J') +
        gueMeasure (PairSite p i) (pairTime p s) {G : PairMatrix p i | ¬ G.IsHermitian} :=
        measure_union_le _ _
    _ = gueSourceLaw (2 * p.W) (ethBadEvent M spacing sel E₀ β ξ ε J') := by
        rw [gueMeasure_image_pairSample p i hBridge hs, gueMeasure_not_isHermitian p i hBridge hs,
          add_zero]
    _ ≤ _ := hbad

end ETH

end BlockBand.LocalWindow.ProofETH
