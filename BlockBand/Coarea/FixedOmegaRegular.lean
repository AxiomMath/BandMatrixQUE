module

public import BlockBand.Coarea.FixedOmegaFresh

/-!
# Fixed-`ω` coarea: regular matrices lie in the chart good set

*Domain.* Deterministic part: every split state `ω = (H_R, C, V)` with `H_R`, `V` Hermitian and
every Hermitian `G` such that `H = assemble ω G` is Hermitian with separable characteristic
polynomial and `det(H_R - λ_α(H)) ≠ 0`. Measure part: every splitting law `Pω` of an exact
physical model, `0 < s ≤ min(c,b)`, `t = s/(2W)`.

## Main results

* `block_crossing` (Schur + Haynsworth, generic blocks): for `Hb = [[A, Cᴴ],[C, D]]` Hermitian,
  `E` a simple eigenvalue of `Hb` with `N_-(Hb - E) = α` and `det(D - E) ≠ 0`, the Schur matrix
  `S = A - Cᴴ(D - E)⁻¹C` has a one-dimensional `E`-eigenspace and
  `N_-(S - E) + N_-(D - E) = α`.
* `fixedOmegaGood_of_ae`: `GUE`-a.e. regularity implies `FixedOmegaGood`.
* `formula_fixed_of_regularAE`: the fixed-`ω` coarea formula from almost-sure regularity.
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
## Schur complement and Haynsworth for a block matrix
-/

section Block

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

theorem shift_isHermitian' {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (E : ℝ) : (A - (E : ℂ) • 1).IsHermitian :=
  hA.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))

theorem fromBlocks_sub_smul_one (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) (E : ℝ) :
    Matrix.fromBlocks A B C D - (E : ℂ) • 1 =
      Matrix.fromBlocks (A - (E : ℂ) • 1) B C (D - (E : ℂ) • 1) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply]

/-- **Schur + Haynsworth at a simple eigenvalue** (the rank sector of the coarea theorem). -/
theorem block_crossing {A : Matrix m m ℂ} (hA : A.IsHermitian) (C : Matrix n m ℂ)
    {D : Matrix n n ℂ} (hD : D.IsHermitian) (E : ℝ) (α : ℕ)
    (hdetD : (D - (E : ℂ) • 1).det ≠ 0)
    (hdet : (Matrix.fromBlocks A Cᴴ C D - (E : ℂ) • 1).det = 0)
    (hline : ∀ φ ψ : m ⊕ n → ℂ, ψ ≠ 0 →
      Matrix.fromBlocks A Cᴴ C D *ᵥ ψ = (E : ℂ) • ψ →
      Matrix.fromBlocks A Cᴴ C D *ᵥ φ = (E : ℂ) • φ → ∃ c : ℂ, φ = c • ψ)
    (hcount : negativeCount (Matrix.fromBlocks A Cᴴ C D - (E : ℂ) • 1) = α) :
    let S := A - Cᴴ * (D - (E : ℂ) • 1)⁻¹ * C
    (∃ u : m → ℂ, u ≠ 0 ∧ S *ᵥ u = (E : ℂ) • u ∧
      ∀ w : m → ℂ, S *ᵥ w = (E : ℂ) • w → ∃ c : ℂ, w = c • u) ∧
    negativeCount (S - (E : ℂ) • 1) + negativeCount (D - (E : ℂ) • 1) = α := by
  set DE := D - (E : ℂ) • 1 with hDEdef
  intro S
  set Hb := Matrix.fromBlocks A Cᴴ C D
  have hDEu : IsUnit DE.det := isUnit_iff_ne_zero.mpr hdetD
  have hinv : DE * DE⁻¹ = 1 := Matrix.mul_nonsing_inv DE hDEu
  have hinv' : DE⁻¹ * DE = 1 := Matrix.nonsing_inv_mul DE hDEu
  -- the Schur lift of a vector of the pair block
  have hlift : ∀ w : m → ℂ, S *ᵥ w = (E : ℂ) • w →
      Hb *ᵥ Sum.elim w (-(DE⁻¹ *ᵥ (C *ᵥ w))) = (E : ℂ) • Sum.elim w (-(DE⁻¹ *ᵥ (C *ᵥ w))) := by
    intro w hw
    have hw' : A *ᵥ w - Cᴴ *ᵥ (DE⁻¹ *ᵥ (C *ᵥ w)) = (E : ℂ) • w := by
      rw [← hw]
      simp only [S, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [Matrix.fromBlocks_mulVec]
    funext a
    rcases a with a | a
    · simp only [Sum.elim_inl, Function.comp_def, Sum.elim_inr, Pi.smul_apply]
      have := congrFun hw' a
      simp only [Pi.sub_apply, Pi.smul_apply] at this
      rw [Matrix.mulVec_neg, Pi.add_apply, Pi.neg_apply, ← sub_eq_add_neg]
      exact this
    · simp only [Sum.elim_inl, Function.comp_def, Sum.elim_inr, Pi.smul_apply, Pi.add_apply]
      have h1 : D *ᵥ (-(DE⁻¹ *ᵥ (C *ᵥ w))) =
          -(C *ᵥ w) + (E : ℂ) • (-(DE⁻¹ *ᵥ (C *ᵥ w))) := by
        have hD' : D = DE + (E : ℂ) • 1 := by simp [DE]
        rw [hD', Matrix.add_mulVec, Matrix.mulVec_neg, Matrix.mulVec_mulVec, hinv,
          Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [h1]
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, Function.comp_apply]
      ring
  -- an eigenvector of `Hb`
  obtain ⟨ψ, hψ0, hψ⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hHψ : Hb *ᵥ ψ = (E : ℂ) • ψ := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hψ
    exact hψ
  set u : m → ℂ := ψ ∘ Sum.inl
  have hψ' : Matrix.fromBlocks (A - (E : ℂ) • 1) Cᴴ C DE *ᵥ ψ = 0 := by
    rw [← fromBlocks_sub_smul_one]; exact hψ
  rw [Matrix.fromBlocks_mulVec] at hψ'
  have hS1 : (A - (E : ℂ) • 1) *ᵥ u + Cᴴ *ᵥ (ψ ∘ Sum.inr) = 0 := by
    funext a; have := congrFun hψ' (Sum.inl a); simpa using this
  have hS2 : C *ᵥ u + DE *ᵥ (ψ ∘ Sum.inr) = 0 := by
    funext a; have := congrFun hψ' (Sum.inr a); simpa using this
  have hR : ψ ∘ Sum.inr = -(DE⁻¹ *ᵥ (C *ᵥ u)) := by
    have h := congrArg (fun x => DE⁻¹ *ᵥ x) hS2
    have hcancel : ∀ x : n → ℂ, DE⁻¹ *ᵥ (DE *ᵥ x) = x := fun x => by
      rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
    rw [Matrix.mulVec_add, hcancel, Matrix.mulVec_zero] at h
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h
  have hSu : S *ᵥ u = (E : ℂ) • u := by
    rw [hR, Matrix.mulVec_neg] at hS1
    simp only [S, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have h := hS1
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have : A *ᵥ u - Cᴴ *ᵥ (DE⁻¹ *ᵥ (C *ᵥ u)) = (E : ℂ) • u := by
      rw [← sub_eq_zero, ← h]; abel
    exact this
  have hu0 : u ≠ 0 := by
    intro h0
    apply hψ0
    funext a
    rcases a with a | a
    · exact congrFun h0 a
    · have hR0 : ψ ∘ Sum.inr = 0 := by
        rw [hR, h0, Matrix.mulVec_zero, Matrix.mulVec_zero, neg_zero]
      exact congrFun hR0 a
  refine ⟨⟨u, hu0, hSu, fun w hw => ?_⟩, ?_⟩
  · obtain ⟨c, hc⟩ := hline _ ψ hψ0 hHψ (hlift w hw)
    refine ⟨c, ?_⟩
    funext a
    have := congrFun hc (Sum.inl a)
    simpa [u] using this
  · -- Haynsworth
    have hAE := shift_isHermitian' hA E
    have hDE : DE.IsHermitian := shift_isHermitian' hD E
    let _ : Invertible DE := Matrix.invertibleOfIsUnitDet DE hDEu
    have hsplit := negativeEigenvalueCount_hermitianSchur (A - (E : ℂ) • 1) Cᴴ DE hAE hDE
    simp only at hsplit
    rw [negativeEigenvalueCount_eq_negativeCount, negativeEigenvalueCount_eq_negativeCount,
      negativeEigenvalueCount_eq_negativeCount, Matrix.conjTranspose_conjTranspose,
      Matrix.invOf_eq_nonsing_inv] at hsplit
    have hfull : Matrix.fromBlocks (A - (E : ℂ) • 1) Cᴴ C DE = Hb - (E : ℂ) • 1 :=
      (fromBlocks_sub_smul_one _ _ _ _ E).symm
    have hschur : A - (E : ℂ) • 1 - Cᴴ * DE⁻¹ * C = S - (E : ℂ) • 1 := by
      simp only [S]; abel
    rw [hfull, hschur, hcount] at hsplit
    omega

end Block

/-!
## Simple spectrum facts for a generic index
-/

section Simple

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem orderedEigenvalue_injective_of_separable' (A : CoareaNative.BlockBand.HermitianMatrix ι)
    (hsep : (A : Matrix ι ι ℂ).charpoly.Separable) : Function.Injective (CoareaNative.BlockBand.orderedEigenvalue A) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  rw [← GaussianRing.orderedEigenvalue_injective_reindex_iff e A]
  apply CoareaNative.BlockBand.orderedEigenvalue_injective_of_separable
  change (Matrix.reindex e e A.1).charpoly.Separable
  rw [Matrix.charpoly_reindex]
  exact hsep

theorem negativeCount_sub_orderedEigenvalue (A : CoareaNative.BlockBand.HermitianMatrix ι)
    (hinj : Function.Injective (CoareaNative.BlockBand.orderedEigenvalue A)) (r : Fin (Fintype.card ι)) :
    negativeCount (A.1 - ((CoareaNative.BlockBand.orderedEigenvalue A r : ℝ) : ℂ) • 1) = r.val := by
  rw [← negativeEigenvalueCount_eq_negativeCount (shift_isHermitian' A.2 _)]
  have h := negativeEigenvalueCount_sub_real_smul_one_eq_eigenCount_Iio A (CoareaNative.BlockBand.orderedEigenvalue A r)
  simp only at h
  rw [h, GaussianRing.eigenCount_Iio_orderedEigenvalue_of_injective A hinj r]

theorem reindex_sub_smul_one {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (M : Matrix ι ι ℂ) (E : ℝ) :
    Matrix.reindex e e M - (E : ℂ) • 1 = Matrix.reindex e e (M - (E : ℂ) • 1) := by
  ext a b; simp [Matrix.one_apply]

theorem negativeCount_reindex' {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (M : Matrix ι ι ℂ) : negativeCount (Matrix.reindex e e M) = negativeCount M := by
  by_cases hM : M.IsHermitian
  · exact negativeCount_reindex e hM
  · have hM' : ¬ (Matrix.reindex e e M).IsHermitian := by
      intro h
      apply hM
      have := h.submatrix e
      simpa using this
    unfold negativeCount
    simp [hM, hM']

end Simple

/-!
## The block form of the assembled matrix
-/

section PairBlocks

variable (p : Parameters) (i : ZMod p.n)

/-- `S ⊕ R ≃ Site`. -/
def siteSumEquiv : PairSite p i ⊕ ExteriorSite p i ≃ p.Site :=
  Equiv.sumCompl (fun x : p.Site => x.1 = i ∨ x.1 = i + 1)

theorem reindex_assemble (ω : SplitState p i) (G : PairMatrix p i) :
    Matrix.reindex (siteSumEquiv p i).symm (siteSumEquiv p i).symm (assemble p i ω G) =
      Matrix.fromBlocks (ω.2.2 + G) ω.2.1ᴴ ω.2.1 ω.1 := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [siteSumEquiv, assemble, a.2, b.2, Matrix.conjTranspose_apply]

theorem exteriorBlock_assemble (ω : SplitState p i) (G : PairMatrix p i) :
    exteriorBlock p i (assemble p i ω G) = ω.1 := by
  ext a b
  simp [exteriorBlock, assemble, a.2, b.2]

/-- **Regular assembled matrices lie in the good set** (the third claim of the coarea theorem:
Schur complement, simple selected root, Haynsworth rank). -/
theorem finCoords_mem_goodSet_of_regular (α : Fin p.N) (ω : SplitState p i)
    (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian) (G : PairMatrix p i) (hG : G.IsHermitian)
    (hH : (assemble p i ω G).IsHermitian) (hsep : (assemble p i ω G).charpoly.Separable)
    (hpole : (exteriorBlock p i (assemble p i ω G) -
      ((physicalOrderedEigenvalue p (assemble p i ω G) α : ℝ) : ℂ) • 1).det ≠ 0) :
    finCoords (2 * p.W) (Matrix.reindex (pairEquiv p i) (pairEquiv p i) G) ∈
      physicalSelectedSimpleGoodSet α.val (omegaR p i ω) (omegaC p i ω) (omegaV p i ω) := by
  set H := assemble p i ω G
  set E := physicalOrderedEigenvalue p H α
  set eqv := siteSumEquiv p i
  set e := pairEquiv p i
  set eR := extEquiv p i
  set r := physicalSpectralRank p α
  set Ah : CoareaNative.BlockBand.HermitianMatrix p.Site := ⟨H, hH⟩
  have hE : E = CoareaNative.BlockBand.orderedEigenvalue Ah r := by
    simp only [E, physicalOrderedEigenvalue]
    rw [rawIncreasingEigenvalue_eq _ H hH]
    rfl
  have hinj := orderedEigenvalue_injective_of_separable' Ah hsep
  -- the block matrix
  set Hb := Matrix.fromBlocks (ω.2.2 + G) ω.2.1ᴴ ω.2.1 ω.1
  have hblock : Matrix.reindex eqv.symm eqv.symm H = Hb := reindex_assemble p i ω G
  have hHb : Hb.IsHermitian := by rw [← hblock]; exact hH.submatrix _
  have hAH : (ω.2.2 + G).IsHermitian := hV.add hG
  have hdetH : (H - (E : ℂ) • 1).det = 0 :=
    (GaussianRing.det_sub_real_smul_one_eq_zero_iff Ah E).2 ⟨r, hE.symm⟩
  have hdet : (Hb - (E : ℂ) • 1).det = 0 := by
    rw [← hblock, reindex_sub_smul_one, Matrix.det_reindex_self, hdetH]
  set Ab : CoareaNative.BlockBand.HermitianMatrix (PairSite p i ⊕ ExteriorSite p i) :=
    ⟨Matrix.reindex eqv.symm eqv.symm H, hH.submatrix _⟩
  have hinjb : Function.Injective (CoareaNative.BlockBand.orderedEigenvalue Ab) :=
    (GaussianRing.orderedEigenvalue_injective_reindex_iff eqv.symm Ah).2 hinj
  have hline : ∀ φ ψ : PairSite p i ⊕ ExteriorSite p i → ℂ, ψ ≠ 0 →
      Hb *ᵥ ψ = (E : ℂ) • ψ → Hb *ᵥ φ = (E : ℂ) • φ → ∃ c : ℂ, φ = c • ψ := by
    intro φ ψ hψ0 hψ hφ
    rw [← hblock] at hψ hφ
    exact GaussianRing.eigenvector_mem_line_of_orderedEigenvalue_injective Ab hinjb hψ0 hψ hφ
  have hcount : negativeCount (Hb - (E : ℂ) • 1) = α.val := by
    rw [← hblock, reindex_sub_smul_one, negativeCount_reindex', hE]
    exact negativeCount_sub_orderedEigenvalue Ah hinj r
  have hdetD : (ω.1 - (E : ℂ) • 1).det ≠ 0 := by
    have := hpole; rwa [exteriorBlock_assemble] at this
  obtain ⟨⟨u, hu0, hSu, hsimp⟩, hrank⟩ :=
    block_crossing hAH ω.2.1 hR E α.val hdetD hdet hline hcount
  set S := ω.2.2 + G - ω.2.1ᴴ * (ω.1 - (E : ℂ) • 1)⁻¹ * ω.2.1
  
  have hR' : (Matrix.reindex eR eR ω.1).IsHermitian := hR.submatrix eR.symm
  have hmatR : (hermitianOfFinCoordinates _ (omegaR p i ω)).1 = Matrix.reindex eR eR ω.1 :=
    hermitianOfFinCoordinates_finCoords hR'
  have hGe : (Matrix.reindex e e G).IsHermitian := hG.submatrix e.symm
  set K := finCoords (2 * p.W) (Matrix.reindex e e G)
  have hmatK : (hermitianOfFinCoordinates _ K).1 = Matrix.reindex e e G :=
    hermitianOfFinCoordinates_finCoords hGe
  have hMglob : physicalGlobalReducedMatrix (omegaR p i ω) (omegaC p i ω) (omegaV p i ω) K E =
      Matrix.reindex e e S := by
    unfold physicalGlobalReducedMatrix
    have h2 : omegaV p i ω - (omegaC p i ω)ᴴ *
        CoareaNative.BlockBand.physicalCoareaResolvent
          (hermitianOfFinCoordinates _ (omegaR p i ω)).1 E * omegaC p i ω =
        BlockBand.Coarea.physicalCoareaF (hermitianOfFinCoordinates _ (omegaR p i ω)).1
          (omegaC p i ω) (omegaV p i ω) E := rfl
    rw [hmatK, h2, hmatR]
    rw [show omegaC p i ω = Matrix.reindex eR e ω.2.1 from rfl,
      show omegaV p i ω = Matrix.reindex e e ω.2.2 from rfl, physicalCoareaF_reindex]
    have h3 : Matrix.reindex e e G + Matrix.reindex e e
        (BlockBand.Coarea.physicalCoareaF ω.1 ω.2.1 ω.2.2 E) =
        Matrix.reindex e e (G + BlockBand.Coarea.physicalCoareaF ω.1 ω.2.1 ω.2.2 E) := by
      ext a b; simp
    rw [h3]
    congr 1
    simp only [S, BlockBand.Coarea.physicalCoareaF, BlockBand.Coarea.physicalCoareaResolvent]
    abel
  refine ⟨E, ?_, u ∘ e.symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    apply hdetD
    have h := (GaussianRing.det_sub_real_smul_one_eq_zero_iff
      (hermitianOfFinCoordinates _ (omegaR p i ω)) E).2 ⟨s, hs⟩
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
  · rw [hMglob]; exact (hAH.sub (isHermitian_conjTranspose_mul_mul ω.2.1
      (shift_isHermitian' hR E).inv)).submatrix e.symm
  · rw [shiftedInertia_eq_negativeCount, hmatR, reindex_sub_smul_one, negativeCount_reindex']
    have hMH : (Matrix.reindex e e S).IsHermitian := (hAH.sub (isHermitian_conjTranspose_mul_mul
      ω.2.1 (shift_isHermitian' hR E).inv)).submatrix e.symm
    have h1 := negativeEigenvalueCount_sub_real_smul_one_eq_eigenCount_Iio
      (⟨Matrix.reindex e e S, hMH⟩ : CoareaNative.BlockBand.HermitianMatrix (Fin (2 * p.W))) E
    simp only at h1
    have h2 : CoareaNative.BlockBand.eigenCount (⟨physicalGlobalReducedMatrix (omegaR p i ω) (omegaC p i ω)
        (omegaV p i ω) K E, by rw [hMglob]; exact hMH⟩ : CoareaNative.BlockBand.HermitianMatrix (Fin (2 * p.W)))
          (Set.Iio E) = CoareaNative.BlockBand.eigenCount (⟨Matrix.reindex e e S, hMH⟩ : CoareaNative.BlockBand.HermitianMatrix _) (Set.Iio E) := by
      congr 1
      exact Subtype.ext hMglob
    rw [h2, ← h1, negativeEigenvalueCount_eq_negativeCount, reindex_sub_smul_one,
      negativeCount_reindex']
    omega

end PairBlocks

/-!
## From almost-sure regularity to the good-state condition
-/

section Measure

variable (p : Parameters) (i : ZMod p.n)

theorem finCoords_hermitianOfFinCoordinates (n : ℕ) (x : HermitianCoordinateSpace n) :
    finCoords n (hermitianOfFinCoordinates n x).1 = x := by
  unfold finCoords
  have h : coordsOfMatrix (hermitianOfFinCoordinates n x).1 = x ∘ hermitianCoordinateEquivFin n := by
    rw [coordsOfMatrix_coe]
    exact coordinatesOfHermitian_hermitianOfCoordinates _
  rw [h]
  funext k
  simp

theorem measurable_finCoords (n : ℕ) : Measurable (finCoords n) := by
  refine measurable_pi_iff.2 fun k => ?_
  exact (measurable_pi_apply _).comp (measurable_coordsOfMatrix n)

theorem pairBlock_assemble (ω : SplitState p i) (G : PairMatrix p i) :
    pairBlock p i (assemble p i ω G) = ω.2.2 + G := by
  ext a b
  simp [pairBlock, assemble, a.2, b.2]

/-- `GUE`-a.e. regularity of the assembled matrix gives the good-state condition. -/
theorem fixedOmegaGood_of_ae (α : Fin p.N) (ω : SplitState p i) (hR : ω.1.IsHermitian)
    (hV : ω.2.2.IsHermitian) {t : ℝ≥0} (ht : 0 < t)
    (hae : ∀ᵐ G ∂gueMeasure (PairSite p i) t, (assemble p i ω G).IsHermitian ∧
      (assemble p i ω G).charpoly.Separable ∧
      (exteriorBlock p i (assemble p i ω G) -
        ((physicalOrderedEigenvalue p (assemble p i ω G) α : ℝ) : ℂ) • 1).det ≠ 0) :
    FixedOmegaGood p i α ω := by
  set e := pairEquiv p i
  set S := physicalSelectedSimpleGoodSet α.val (omegaR p i ω) (omegaC p i ω) (omegaV p i ω)
  have hV' : (omegaV p i ω).IsHermitian := hV.submatrix e.symm
  have hSm : MeasurableSet S :=
    measurableSet_physicalSelectedSimpleGoodSet α.val _ _ _ hV'
  have hQm : MeasurableSet {X : Matrix (Fin (2 * p.W)) (Fin (2 * p.W)) ℂ |
      finCoords (2 * p.W) X ∈ S} := (measurable_finCoords _) hSm
  have hre : Measurable (Matrix.reindex e e : PairMatrix p i → _) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  have h1 : ∀ᵐ G ∂gueMeasure (PairSite p i) t, finCoords (2 * p.W) (Matrix.reindex e e G) ∈ S := by
    filter_upwards [hae, ae_isHermitian_gueMeasure (ι := PairSite p i) t] with G hG hGH
    exact finCoords_mem_goodSet_of_regular p i α ω hR hV G hGH hG.1 hG.2.1 hG.2.2
  have h2 : ∀ᵐ X ∂gueMeasure (Fin (2 * p.W)) t, finCoords (2 * p.W) X ∈ S := by
    rw [← gueMeasure_map_reindex e t]
    exact (ae_map_iff hre.aemeasurable hQm).2 h1
  rw [gueMeasure_eq_map_withDensity (2 * p.W) ht] at h2
  have h3 := ae_of_ae_map (measurable_hermitianOfFinCoordinates_val (2 * p.W)).aemeasurable h2
  rw [ae_withDensity_iff (measurable_hermitianGUEDensity_comp_block (2 * p.W) t)] at h3
  have h4 : ∀ᵐ x ∂(volume : Measure (HermitianCoordinateSpace (2 * p.W))), x ∈ S := by
    filter_upwards [h3] with x hx
    have hpos : hermitianGUEDensity (2 * p.W) t (hermitianGUEBlock (2 * p.W) x) ≠ 0 := by
      have hZ : 0 < gueNormalizer (2 * p.W) t := by unfold gueNormalizer; positivity
      rw [hermitianGUEDensity, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have := hx hpos
    rwa [finCoords_hermitianOfFinCoordinates] at this
  exact ae_iff.1 h4

/-- **`CoareaContract.formula_fixed` from `CoareaContract.regular_ae`**: the hypothesis and the
conclusion are the types of these two fields. The regularity clause is proved as
`RegularAE.coarea_regular_ae`; the composition is `coareaContract_holds`. -/
theorem formula_fixed_of_regularAE
    (hreg : ∀ (p : Parameters) (model : p.GaussianRingModel),
      ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), H.IsHermitian ∧ H.charpoly.Separable ∧
        ∀ (α : Fin p.N) (i : ZMod p.n),
          (exteriorBlock p i H - ((physicalOrderedEigenvalue p H α : ℝ) : ℂ) • 1).det ≠ 0) :
    ∀ (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N)
      (i : ZMod p.n) (s : ℝ), 0 < s → s ≤ min p.c p.b →
      ∀ Pω : Measure (SplitState p i), IsPairSplitting p i model s Pω →
      ∀ U, IsPairFrame p i U →
      ∀ᵐ ω ∂Pω, ∀ g : PairMatrix p i → ℝ≥0∞, Measurable g →
        (∫⁻ G, g G ∂(gueMeasure (PairSite p i) (pairTime p s))) =
          coareaFiber p α i s U (clockSpeed p i) ω g := by
  intro p model α i s hs _ Pω hsplit U hU
  have ht : 0 < pairTime p s := by
    unfold pairTime
    have := p.W_pos
    exact Real.toNNReal_pos.2 (div_pos hs (by positivity))
  have h0 := hreg p model
  rw [← hsplit] at h0
  have h1 := ae_of_ae_map (ContractClauses.measurable_assemble p i).aemeasurable h0
  have h2 := Measure.ae_ae_of_ae_prod h1
  filter_upwards [h2] with ω hω
  have hGH := ae_isHermitian_gueMeasure (ι := PairSite p i) (pairTime p s)
  obtain ⟨G, hG, hGh⟩ := (hω.and hGH).exists
  have hR : ω.1.IsHermitian := by
    have h := hG.1.submatrix (Subtype.val : ExteriorSite p i → p.Site)
    rw [← exteriorBlock_assemble p i ω G]
    exact h
  have hV : ω.2.2.IsHermitian := by
    have h := hG.1.submatrix (Subtype.val : PairSite p i → p.Site)
    have h' : (ω.2.2 + G).IsHermitian := by rw [← pairBlock_assemble p i ω G]; exact h
    have := h'.sub hGh
    simpa using this
  have hgood := fixedOmegaGood_of_ae p i α ω hR hV ht
    (hω.mono fun G hG => ⟨hG.1, hG.2.1, hG.2.2 α i⟩)
  intro g hg
  exact formula_fixed_of_good p i α s ht U hU ω hR hV hgood g hg

end Measure

end BlockBand.Coarea.FixedOmega
