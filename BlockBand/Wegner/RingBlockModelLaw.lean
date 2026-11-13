module

public import Mathlib
public import BlockBand.Internal.Contracts.InputsRing
public import BlockBand.Wegner.SingularLogMomentsLaw

/-!
# Generic law lemmas for the ring `BlockModel` presentations

Contents (no estimate and no cited input is used):
* finite-product measure identities: currying a dependent double product
  (`map_uncurry_pi_pi_dep`, `hasLaw_curry`) and splitting a product of pair laws into the
  product of the two product laws (`hasLaw_pi_prod_split`), for arbitrary dependent finite
  families of probability measures;
* `GUE_W(S)` (`gueMatrixLaw`, the concrete Johansson coordinate law) is the image of the
  product of the upper-coordinate laws `SingularLogLaw.coordLaw S` under the Hermitian
  reconstruction (`gueMatrixLaw_eq_map`);
* measurability and hermiticity of the block maps `toBlockCoords`, `diagonalBlocks`,
  `offDiagonalBlocks` of `InputsRing`, and `presents_of_pair`: the `Presents` clause on the
  law of `M.H = D + ⊕ A_j` follows from the joint law of `(A, D)` (since
  `offDiagonalBlocks X + ⊕_j (diagonalBlocks X)_j = X` for every matrix `X`).
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
open scoped NNReal

/-!
## Finite product measures
-/

section PiLemmas

variable {ι : Type} [Fintype ι]

/-- Currying a dependent doubly indexed product of probability measures: under
`Π_i Π_{j ∈ κ i} ν i j` the uncurried family has law `Π_{(i,j)} ν i j`. -/
theorem map_uncurry_pi_pi_dep {κ : ι → Type} [∀ i, Fintype (κ i)] {X : Type}
    [MeasurableSpace X] (ν : ∀ i, κ i → Measure X) [∀ i j, IsProbabilityMeasure (ν i j)] :
    (Measure.pi fun i => Measure.pi (ν i)).map (fun f (σ : Σ i, κ i) => f σ.1 σ.2) =
      Measure.pi fun σ : (Σ i, κ i) => ν σ.1 σ.2 := by
  have hm : Measurable (fun (f : ∀ i, κ i → X) (σ : Σ i, κ i) => f σ.1 σ.2) :=
    measurable_pi_iff.mpr fun σ => (measurable_pi_apply σ.2).comp (measurable_pi_apply σ.1)
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (f : ∀ i, κ i → X) (σ : Σ i, κ i) => f σ.1 σ.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i => Set.univ.pi fun j => s ⟨i, j⟩ := by
    ext f
    simp [Set.mem_pi, Sigma.forall]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_sigma]

/-- Currying a random family indexed by a sigma type whose law is a product. -/
theorem hasLaw_curry {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ι → Type}
    [∀ i, Fintype (κ i)] {X : Type} [MeasurableSpace X] (ν : ∀ i, κ i → Measure X)
    [∀ i j, IsProbabilityMeasure (ν i j)] {Z : Ω → (Σ i, κ i) → X}
    (h : HasLaw Z (Measure.pi fun σ : (Σ i, κ i) => ν σ.1 σ.2) P) :
    HasLaw (fun w i j => Z w ⟨i, j⟩) (Measure.pi fun i => Measure.pi (ν i)) P := by
  let e := MeasurableEquiv.piCurry (fun i (_ : κ i) => X)
  have h1 : MeasurePreserving e.symm (Measure.pi fun i => Measure.pi (ν i))
      (Measure.pi fun σ : (Σ i, κ i) => ν σ.1 σ.2) :=
    ⟨e.symm.measurable, map_uncurry_pi_pi_dep ν⟩
  exact h1.symm.hasLaw.comp h

section SumElim

variable {α β : ι → Type} [mα : ∀ i, MeasurableSpace (α i)] [mβ : ∀ i, MeasurableSpace (β i)]

/-- The measurable structure on the fibres of `Sum.elim α β`. -/
@[instance_reducible]
def sumElimSpace : (t : ι ⊕ ι) → MeasurableSpace (Sum.elim α β t)
  | .inl i => mα i
  | .inr i => mβ i

/-- The family of measures `μ ⊔ ν` on the fibres of `Sum.elim α β`. -/
def sumElimMeasure (μ : ∀ i, Measure (α i)) (ν : ∀ i, Measure (β i)) :
    (t : ι ⊕ ι) → @Measure (Sum.elim α β t) (sumElimSpace t)
  | .inl i => μ i
  | .inr i => ν i

/-- A family of pairs as a family indexed by `ι ⊕ ι`. -/
def sumElimSplit (z : ∀ i, α i × β i) : (t : ι ⊕ ι) → Sum.elim α β t
  | .inl i => (z i).1
  | .inr i => (z i).2

/-- Under `Π_i (μ_i ⊗ ν_i)` the two component families are independent with laws `Π μ`,
`Π ν`. -/
theorem hasLaw_pi_prod_split (μ : ∀ i, Measure (α i)) (ν : ∀ i, Measure (β i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    HasLaw (fun z : (∀ i, α i × β i) => ((fun i => (z i).1), (fun i => (z i).2)))
      ((Measure.pi μ).prod (Measure.pi ν)) (Measure.pi fun i => (μ i).prod (ν i)) := by
  let _ : ∀ t, MeasurableSpace (Sum.elim α β t) := sumElimSpace
  have hsf : ∀ t, SigmaFinite (sumElimMeasure μ ν t) := by
    intro t
    cases t with
    | inl i => exact (inferInstance : SigmaFinite (μ i))
    | inr i => exact (inferInstance : SigmaFinite (ν i))
  have hT : Measurable (sumElimSplit (α := α) (β := β)) := by
    apply measurable_pi_iff.mpr
    intro t
    cases t with
    | inl i => exact measurable_fst.comp (measurable_pi_apply i)
    | inr i => exact measurable_snd.comp (measurable_pi_apply i)
  have h1 : HasLaw (sumElimSplit (α := α) (β := β)) (Measure.pi (sumElimMeasure μ ν))
      (Measure.pi fun i => (μ i).prod (ν i)) := by
    refine ⟨hT.aemeasurable, ?_⟩
    symm
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply hT (MeasurableSet.univ_pi hs)]
    have hpre : sumElimSplit ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i => (@id (Set (α i)) (s (.inl i)) ×ˢ @id (Set (β i)) (s (.inr i))) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_univ_pi, Sum.forall, sumElimSplit]
      exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
    have key : (Measure.pi fun i => (μ i).prod (ν i))
        (Set.univ.pi fun i => (@id (Set (α i)) (s (.inl i)) ×ˢ @id (Set (β i)) (s (.inr i)))) =
          ∏ i, (μ i (@id (Set (α i)) (s (.inl i))) * ν i (@id (Set (β i)) (s (.inr i)))) := by
      rw [Measure.pi_pi]
      simp_rw [Measure.prod_prod]
    rw [hpre, key, Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
    rfl
  exact (measurePreserving_sumPiEquivProdPi (sumElimMeasure μ ν)).hasLaw.comp h1

end SumElim

end PiLemmas

/-!
## `GUE_W(S)` from its upper coordinates
-/

section GUE

variable {W : ℕ}

theorem measurable_gaussianMatrixRaw : Measurable (Johansson.gaussianMatrixRaw (N := W)) :=
  measurable_subtype_coe.comp Johansson.measurable_gaussianMatrix

/-- The Hermitian reconstruction ignores the imaginary part of diagonal coordinates. -/
theorem gaussianMatrixRaw_diagFix (z : Johansson.UpperPair W → ℝ × ℝ) :
    Johansson.gaussianMatrixRaw (fun q => SingularLogLaw.diagFix q (z q)) =
      Johansson.gaussianMatrixRaw z := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [Johansson.gaussianMatrixRaw, SingularLogLaw.diagFix]
  · by_cases hle : a ≤ b
    · simp [Johansson.gaussianMatrixRaw, SingularLogLaw.diagFix, h, hle]
    · simp [Johansson.gaussianMatrixRaw, SingularLogLaw.diagFix, h, hle, Ne.symm h]

/-- `GUE_W(S)` is the reconstruction of independent upper coordinates of laws `coordLaw S`. -/
theorem gueMatrixLaw_eq_map (S : ℝ≥0) :
    gueMatrixLaw W S =
      (Measure.pi (SingularLogLaw.coordLaw (W := W) S)).map Johansson.gaussianMatrixRaw := by
  have : ∀ q : Johansson.UpperPair W, IsProbabilityMeasure (Johansson.upperEntryMeasure S q) :=
    Johansson.upperEntryMeasure_probability S
  have hsf : ∀ q : Johansson.UpperPair W,
      SigmaFinite ((Johansson.upperEntryMeasure S q).map (SingularLogLaw.diagFix q)) :=
    fun q => (inferInstance : SigmaFinite (SingularLogLaw.coordLaw S q))
  have hp : Measure.pi (SingularLogLaw.coordLaw (W := W) S) =
      (Measure.pi (Johansson.upperEntryMeasure S)).map
        (fun x q => SingularLogLaw.diagFix q (x q)) :=
    (Measure.pi_map_pi (fun q => (SingularLogLaw.measurable_diagFix q).aemeasurable)).symm
  have hd : Measurable (fun (x : Johansson.UpperPair W → ℝ × ℝ) q =>
      SingularLogLaw.diagFix q (x q)) :=
    measurable_pi_iff.mpr fun q =>
      (SingularLogLaw.measurable_diagFix q).comp (measurable_pi_apply q)
  rw [hp, Measure.map_map measurable_gaussianMatrixRaw hd, gueMatrixLaw,
    Johansson.coordinateMeasure]
  congr 1
  funext z
  exact (gaussianMatrixRaw_diagFix z).symm

/-- The reconstruction pushes `Π coordLaw S` to `GUE_W(S)`. -/
theorem hasLaw_gaussianMatrixRaw (S : ℝ≥0) :
    HasLaw Johansson.gaussianMatrixRaw (gueMatrixLaw W S)
      (Measure.pi (SingularLogLaw.coordLaw (W := W) S)) :=
  ⟨measurable_gaussianMatrixRaw.aemeasurable, (gueMatrixLaw_eq_map S).symm⟩

end GUE

/-!
## Block maps
-/

section BlockMaps

variable {k W : ℕ}

theorem measurable_diagonalBlocks :
    Measurable (diagonalBlocks (k := k) (W := W)) :=
  measurable_pi_iff.mpr fun j => Matrix.measurable_iff.mpr fun a b =>
    Matrix.measurable_iff.mp measurable_id (j, a) (j, b)

theorem measurable_offDiagonalBlocks :
    Measurable (offDiagonalBlocks (k := k) (W := W)) := by
  rw [Matrix.measurable_iff]
  intro x y
  by_cases h : x.1 = y.1
  · simp only [offDiagonalBlocks, h, ↓reduceIte]
    exact measurable_const
  · simp only [offDiagonalBlocks, h, ↓reduceIte]
    exact Matrix.measurable_iff.mp measurable_id x y

theorem measurable_toBlockCoords (p : Parameters) : Measurable (toBlockCoords p) :=
  Matrix.measurable_iff.mpr fun x y =>
    Matrix.measurable_iff.mp measurable_id ((siteBlockEquiv p).symm x) ((siteBlockEquiv p).symm y)

theorem toBlockCoords_isHermitian (p : Parameters) {H : p.SiteMatrix} (hH : H.IsHermitian) :
    (toBlockCoords p H).IsHermitian :=
  hH.submatrix _

theorem diagonalBlocks_isHermitian {X : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ}
    (hX : X.IsHermitian) (j : Fin k) : (diagonalBlocks X j).IsHermitian :=
  hX.submatrix (fun a => (j, a))

theorem offDiagonalBlocks_isHermitian {X : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ}
    (hX : X.IsHermitian) : (offDiagonalBlocks X).IsHermitian := by
  ext x y
  have hxy := hX.apply x y
  simp only [Matrix.conjTranspose_apply, offDiagonalBlocks]
  by_cases h : x.1 = y.1
  · simp [h]
  · simp [h, Ne.symm h, hxy]

/-- The block-diagonal matrix `⊕_j A_j` of a block family. -/
def blockSumOf (A : Fin k → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ :=
  fun x y => if x.1 = y.1 then A x.1 x.2 y.2 else 0

theorem measurable_blockSumOf : Measurable (blockSumOf (k := k) (W := W)) := by
  rw [Matrix.measurable_iff]
  intro x y
  by_cases h : x.1 = y.1
  · simp only [blockSumOf, h, ↓reduceIte]
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp (measurable_pi_apply _))
  · simp only [blockSumOf, h, ↓reduceIte]
    exact measurable_const

/-- Every matrix is its off-diagonal-block part plus the direct sum of its diagonal blocks. -/
theorem offDiagonal_add_blockSum (X : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) :
    offDiagonalBlocks X + blockSumOf (diagonalBlocks X) = X := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.add_apply, offDiagonalBlocks, blockSumOf, diagonalBlocks]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

/-- The `Presents` clause on the law of `M.H` follows from the joint law of `(A, D)`. -/
theorem presents_of_pair (M : BlockModel k W)
    (μ : Measure (Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ)) (hY : ∀ w, M.Y w = 0)
    (h : M.P.map (fun w => (M.A w, M.D w)) =
      μ.map (fun X => (diagonalBlocks X, offDiagonalBlocks X))) :
    Presents M μ := by
  refine ⟨hY, h, ?_⟩
  have hΨ : Measurable (fun z : (Fin k → Matrix (Fin W) (Fin W) ℂ) ×
      Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ => z.2 + blockSumOf z.1) :=
    Matrix.measurable_iff.mpr fun x y =>
      (Matrix.measurable_iff.mp measurable_snd x y).add
        (Matrix.measurable_iff.mp (measurable_blockSumOf.comp measurable_fst) x y)
  have hAD : Measurable (fun w => (M.A w, M.D w)) := M.measurable_A.prodMk M.measurable_D
  have hdo : Measurable (fun X : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ =>
      (diagonalBlocks X, offDiagonalBlocks X)) :=
    measurable_diagonalBlocks.prodMk measurable_offDiagonalBlocks
  have e1 : M.H = (fun z : (Fin k → Matrix (Fin W) (Fin W) ℂ) ×
      Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ => z.2 + blockSumOf z.1) ∘
        (fun w => (M.A w, M.D w)) := rfl
  rw [e1, ← Measure.map_map hΨ hAD, h, Measure.map_map hΨ hdo]
  have e2 : ((fun z : (Fin k → Matrix (Fin W) (Fin W) ℂ) ×
      Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ => z.2 + blockSumOf z.1) ∘
        fun X => (diagonalBlocks X, offDiagonalBlocks X)) = id := by
    funext X
    exact offDiagonal_add_blockSum X
  rw [e2, Measure.map_id]

end BlockMaps

end RingBlock

end BlockBand.Wegner
