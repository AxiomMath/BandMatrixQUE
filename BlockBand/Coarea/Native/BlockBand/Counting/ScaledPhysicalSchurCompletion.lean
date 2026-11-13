module

public import BlockBand.Coarea.Native.BlockBand.Counting.ScaledPhysicalSchurConstruction
public import BlockBand.Coarea.Native.BlockBand.LinearAlgebra.RegulatedSchurMeasurability

/-!
# Completion of the scaled physical Schur argument

This module constructs the normalized Schur family used in the projected Wegner
argument directly from the Gaussian-ring Hamiltonian.  Exterior coordinate vectors are
first passed through the Hermitian-part projection.  This harmless totalization is
essential: the ambient coordinate space contains vectors with non-real diagonal
coordinates, although the Gaussian samples lie in the Hermitian locus.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder ENNReal NNReal

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- Hermitian totalization of the physical matrix carried by the exterior coordinates,
with the exposed singleton block set equal to zero. -/
def hermitianExteriorMatrix (p : Params) (j : ZMod p.n)
    (ξ : exteriorUpperPairs p j → ℂ) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  matrixHermitianPart
    (physicalMatrixFromExteriorNormalizedBlock p j
      (ξ, (0 : Matrix (BlockGUE.Index (singletonBlockSize p.W))
        (BlockGUE.Index (singletonBlockSize p.W)) ℂ)))

/-- Reconstruction is additive across the exterior/exposed coordinate split. -/
theorem physicalMatrixFromExteriorNormalizedBlock_eq_exterior_add_exposed
    (p : Params) (j : ZMod p.n)
    (ξ : exteriorUpperPairs p j → ℂ)
    (G : Matrix (BlockGUE.Index (singletonBlockSize p.W))
      (BlockGUE.Index (singletonBlockSize p.W)) ℂ) :
    physicalMatrixFromExteriorNormalizedBlock p j (ξ, G) =
      physicalMatrixFromExteriorNormalizedBlock p j
        (ξ, (0 : Matrix (BlockGUE.Index (singletonBlockSize p.W))
          (BlockGUE.Index (singletonBlockSize p.W)) ℂ)) +
      physicalMatrixFromExteriorNormalizedBlock p j
        ((fun _ => 0), G) := by
  classical
  ext a b
  by_cases hab : siteLE p a b
  · simp [physicalMatrixFromExteriorNormalizedBlock, reconstructFromBlockSplit,
      matrixOfUpperCoordinates, hab, mergeUpperCoordinates,
      physicalSingletonUpperCoordinates, normalizedSingletonUpperCoordinates]
    split <;> simp_all
  · simp [physicalMatrixFromExteriorNormalizedBlock, reconstructFromBlockSplit,
      matrixOfUpperCoordinates, hab, mergeUpperCoordinates,
      physicalSingletonUpperCoordinates, normalizedSingletonUpperCoordinates]
    split <;> simp_all

/-- The reconstruction supported on the exposed block is Hermitian whenever the
inserted normalized block is Hermitian. -/
theorem physicalMatrixFromExteriorNormalizedBlock_zero_exterior_isHermitian
    (p : Params) (j : ZMod p.n)
    (G : Matrix (BlockGUE.Index (singletonBlockSize p.W))
      (BlockGUE.Index (singletonBlockSize p.W)) ℂ)
    (hG : G.IsHermitian) :
    (physicalMatrixFromExteriorNormalizedBlock p j ((fun _ => 0), G)).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext a b
  classical
  by_cases hab : siteLE p a b
  · by_cases hba : siteLE p b a
    · have heq : a = b := (p.siteIndexEquiv).injective
          (Fin.ext (Nat.le_antisymm hab hba))
      subst b
      have hGaa := congrFun (congrFun hG ⟨0, a.2⟩) ⟨0, a.2⟩
      simp only [Matrix.conjTranspose_apply] at hGaa
      simp [physicalMatrixFromExteriorNormalizedBlock, reconstructFromBlockSplit,
        matrixOfUpperCoordinates, hab, mergeUpperCoordinates,
        physicalSingletonUpperCoordinates, normalizedSingletonUpperCoordinates]
      split <;> simp_all [map_mul]
    · simp [physicalMatrixFromExteriorNormalizedBlock, reconstructFromBlockSplit,
        matrixOfUpperCoordinates, hab, hba, mergeUpperCoordinates,
        physicalSingletonUpperCoordinates, normalizedSingletonUpperCoordinates]
  · have hba := siteLE_reverse_of_not p a b hab
    simp [physicalMatrixFromExteriorNormalizedBlock, reconstructFromBlockSplit,
      matrixOfUpperCoordinates, hab, hba, mergeUpperCoordinates,
      physicalSingletonUpperCoordinates, normalizedSingletonUpperCoordinates]

/-- The principal block of the exposed-only reconstruction is exactly the physical
coefficient `sqrt p.c` times the normalized matrix. -/
theorem physicalMatrix_zero_exterior_submatrix
    (p : Params) (j : ZMod p.n)
    (G : Matrix (BlockGUE.Index (singletonBlockSize p.W))
      (BlockGUE.Index (singletonBlockSize p.W)) ℂ)
    (hG : G.IsHermitian) :
    (physicalMatrixFromExteriorNormalizedBlock p j ((fun _ => 0), G)).submatrix
        (fun a => singletonPhysicalSplitEquiv p j (Sum.inl a))
        (fun a => singletonPhysicalSplitEquiv p j (Sum.inl a)) =
      ((Real.sqrt p.c : ℝ) : ℂ) • G := by
  ext a b
  change physicalMatrixFromExteriorNormalizedBlock p j ((fun _ => 0), G)
      (j, a.2) (j, b.2) = ((Real.sqrt p.c : ℝ) : ℂ) * G a b
  have hGab := congrFun (congrFun hG a) b
  simp only [Matrix.conjTranspose_apply] at hGab
  have ha : (⟨0, a.2⟩ : BlockGUE.Index (singletonBlockSize p.W)) = a := by
    apply Sigma.ext
    · exact Subsingleton.elim _ _
    · rfl
  have hb : (⟨0, b.2⟩ : BlockGUE.Index (singletonBlockSize p.W)) = b := by
    apply Sigma.ext
    · exact Subsingleton.elim _ _
    · rfl
  classical
  by_cases hab : siteLE p (j, a.2) (j, b.2)
  · let q : UpperPair p := ⟨((j, a.2), (j, b.2)), hab⟩
    have hq : q ∈ diagonalBlockUpperPairs p j :=
      (mem_diagonalBlockUpperPairs_iff p j q).2 ⟨rfl, rfl⟩
    change matrixOfUpperCoordinates p
      (mergeUpperCoordinates p j (physicalSingletonUpperCoordinates p j G)
        (fun _ => 0)) (j, a.2) (j, b.2) = _
    rw [matrixOfUpperCoordinates, dite_eq_left hab,
      mergeUpperCoordinates_of_mem p j _ _ q hq]
    simp [physicalSingletonUpperCoordinates_apply, q, ha, hb]
  · have hba := siteLE_reverse_of_not p (j, a.2) (j, b.2) hab
    let q : UpperPair p := ⟨((j, b.2), (j, a.2)), hba⟩
    have hq : q ∈ diagonalBlockUpperPairs p j :=
      (mem_diagonalBlockUpperPairs_iff p j q).2 ⟨rfl, rfl⟩
    change matrixOfUpperCoordinates p
      (mergeUpperCoordinates p j (physicalSingletonUpperCoordinates p j G)
        (fun _ => 0)) (j, a.2) (j, b.2) = _
    rw [matrixOfUpperCoordinates, dite_eq_right hab,
      mergeUpperCoordinates_of_mem p j _ _ q hq]
    simp [physicalSingletonUpperCoordinates_apply, q, ha, hb, hGab]

/-- The exposed-only reconstruction vanishes unless both indices belong to the
exposed physical block. -/
theorem physicalMatrix_zero_exterior_apply_of_not_both
    (p : Params) (j : ZMod p.n)
    (G : Matrix (BlockGUE.Index (singletonBlockSize p.W))
      (BlockGUE.Index (singletonBlockSize p.W)) ℂ)
    (a b : Site p.n p.W) (h : ¬(a.1 = j ∧ b.1 = j)) :
    physicalMatrixFromExteriorNormalizedBlock p j ((fun _ => 0), G) a b = 0 := by
  classical
  by_cases hab : siteLE p a b
  · let q : UpperPair p := ⟨(a, b), hab⟩
    have hq : q ∉ diagonalBlockUpperPairs p j := by
      intro hmem
      exact h ((mem_diagonalBlockUpperPairs_iff p j q).1 hmem)
    change matrixOfUpperCoordinates p
      (mergeUpperCoordinates p j (physicalSingletonUpperCoordinates p j G)
        (fun _ => 0)) a b = 0
    rw [matrixOfUpperCoordinates, dite_eq_left hab]
    have hmerge : mergeUpperCoordinates p j
        (physicalSingletonUpperCoordinates p j G) (fun _ => 0) q = 0 := by
      rw [mergeUpperCoordinates]
      split <;> simp_all
    exact hmerge
  · have hba := siteLE_reverse_of_not p a b hab
    let q : UpperPair p := ⟨(b, a), hba⟩
    have hq : q ∉ diagonalBlockUpperPairs p j := by
      intro hmem
      have hm := (mem_diagonalBlockUpperPairs_iff p j q).1 hmem
      exact h ⟨hm.2, hm.1⟩
    change matrixOfUpperCoordinates p
      (mergeUpperCoordinates p j (physicalSingletonUpperCoordinates p j G)
        (fun _ => 0)) a b = 0
    rw [matrixOfUpperCoordinates, dite_eq_right hab]
    have hmerge : mergeUpperCoordinates p j
        (physicalSingletonUpperCoordinates p j G) (fun _ => 0) q = 0 := by
      rw [mergeUpperCoordinates]
      split <;> simp_all
    rw [hmerge]
    simp

/-- After normalization and reindexing, an exposed-only Hermitian reconstruction is
exactly the upper-left block, with all other blocks zero. -/
theorem normalized_exposed_reindex_eq_fromBlocks
    (p : Params) (j : ZMod p.n)
    (G : Matrix (BlockGUE.Index (singletonBlockSize p.W))
      (BlockGUE.Index (singletonBlockSize p.W)) ℂ)
    (hG : G.IsHermitian) :
    ((((Real.sqrt p.c)⁻¹ : ℂ) •
      physicalMatrixFromExteriorNormalizedBlock p j ((fun _ => 0), G)).submatrix
        (singletonPhysicalSplitEquiv p j) (singletonPhysicalSplitEquiv p j)) =
      Matrix.fromBlocks G 0 0
        (0 : Matrix (BlockSetSite ({j} : Set (ZMod p.n))ᶜ p.W)
          (BlockSetSite ({j} : Set (ZMod p.n))ᶜ p.W) ℂ) := by
  have hprincipal := physicalMatrix_zero_exterior_submatrix p j G hG
  have hs : Real.sqrt p.c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 p.c_pos)
  ext (a | a) (b | b)
  · change ((Real.sqrt p.c)⁻¹ : ℂ) *
      physicalMatrixFromExteriorNormalizedBlock p j ((fun _ => 0), G)
        (j, a.2) (j, b.2) = G a b
    have hab := congrFun (congrFun hprincipal a) b
    change physicalMatrixFromExteriorNormalizedBlock p j ((fun _ => 0), G)
      (j, a.2) (j, b.2) = ((Real.sqrt p.c : ℝ) : ℂ) * G a b at hab
    rw [hab, ← mul_assoc]
    have hsC : (((Real.sqrt p.c : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hs
    rw [inv_mul_cancel₀ hsC, one_mul]
  · change ((Real.sqrt p.c)⁻¹ : ℂ) *
      physicalMatrixFromExteriorNormalizedBlock p j ((fun _ => 0), G)
        (j, a.2) b.1 = 0
    rw [physicalMatrix_zero_exterior_apply_of_not_both p j G]
    · simp
    · intro h
      exact b.property (by simpa using h.2)
  · change ((Real.sqrt p.c)⁻¹ : ℂ) *
      physicalMatrixFromExteriorNormalizedBlock p j ((fun _ => 0), G)
        a.1 (j, b.2) = 0
    rw [physicalMatrix_zero_exterior_apply_of_not_both p j G]
    · simp
    · intro h
      exact a.property (by simpa using h.1)
  · change ((Real.sqrt p.c)⁻¹ : ℂ) *
      physicalMatrixFromExteriorNormalizedBlock p j ((fun _ => 0), G)
        a.1 b.1 = 0
    rw [physicalMatrix_zero_exterior_apply_of_not_both p j G]
    · simp
    · intro h
      exact a.property (by simpa using h.1)

/-- On a sample, Hermitianizing the exterior reconstruction does not alter it. -/
theorem Law.hermitianExteriorMatrix_coordinates
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    hermitianExteriorMatrix p j (M.exteriorUpperCoordinates j ω) =
      physicalMatrixFromExteriorNormalizedBlock p j
        (M.exteriorUpperCoordinates j ω,
          (0 : Matrix (BlockGUE.Index (singletonBlockSize p.W))
            (BlockGUE.Index (singletonBlockSize p.W)) ℂ)) := by
  let E := physicalMatrixFromExteriorNormalizedBlock p j
    ((fun _ => 0), M.normalizedSingletonBlock j ω)
  have hE : E.IsHermitian :=
    physicalMatrixFromExteriorNormalizedBlock_zero_exterior_isHermitian
      p j _ (M.normalizedSingletonBlock_isHermitian j ω)
  have hsplit := physicalMatrixFromExteriorNormalizedBlock_eq_exterior_add_exposed
    p j (M.exteriorUpperCoordinates j ω) (M.normalizedSingletonBlock j ω)
  have hbase : (physicalMatrixFromExteriorNormalizedBlock p j
      (M.exteriorUpperCoordinates j ω,
        (0 : Matrix (BlockGUE.Index (singletonBlockSize p.W))
          (BlockGUE.Index (singletonBlockSize p.W)) ℂ))).IsHermitian := by
    have hfull : (physicalMatrixFromExteriorNormalizedBlock p j
        (M.exteriorUpperCoordinates j ω, M.normalizedSingletonBlock j ω)).IsHermitian := by
      rw [M.physicalMatrixFromExteriorNormalizedBlock_coordinates j ω]
      exact M.H_hermitian ω
    rw [hsplit] at hfull
    simpa [E] using hfull.sub hE
  unfold hermitianExteriorMatrix matrixHermitianPart
  rw [hbase.eq]
  ext a b
  simp
  ring

/-- The Hermitianized exterior reconstruction is measurable. -/
theorem measurable_hermitianExteriorMatrix (p : Params) (j : ZMod p.n) :
    Measurable (hermitianExteriorMatrix p j) := by
  apply Measurable.matrixHermitianPart
  exact (measurable_physicalMatrixFromExteriorNormalizedBlock p j).comp
    (measurable_id.prodMk measurable_const)

/-- The Hermitianized exterior reconstruction is Hermitian for every ambient
coordinate vector, including vectors outside the support of the physical law. -/
theorem hermitianExteriorMatrix_isHermitian (p : Params) (j : ZMod p.n)
    (ξ : exteriorUpperPairs p j → ℂ) :
    (hermitianExteriorMatrix p j ξ).IsHermitian :=
  matrixHermitianPart_isHermitian _

/-- The coefficient-one normalized pencil with the exposed GUE block removed. -/
def normalizedExteriorPencil (p : Params) (j : ZMod p.n)
    (V Γ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (e η : ℝ)
    (ξ : exteriorUpperPairs p j → ℂ) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  ((Real.sqrt p.c)⁻¹ : ℂ) •
    (hermitianExteriorMatrix p j ξ + V -
      (e : ℂ) • (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) +
      Complex.I • (Γ + η • (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)))

/-- Reindex the normalized exterior pencil into exposed/complement block order. -/
def normalizedExteriorSplitPencil (p : Params) (j : ZMod p.n)
    (V Γ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (e η : ℝ)
    (ξ : exteriorUpperPairs p j → ℂ) :
    Matrix
      (BlockGUE.Index (singletonBlockSize p.W) ⊕
        BlockSetSite ({j} : Set (ZMod p.n))ᶜ p.W)
      (BlockGUE.Index (singletonBlockSize p.W) ⊕
        BlockSetSite ({j} : Set (ZMod p.n))ᶜ p.W) ℂ :=
  (normalizedExteriorPencil p j V Γ e η ξ).submatrix
    (singletonPhysicalSplitEquiv p j) (singletonPhysicalSplitEquiv p j)

/-- The split normalized exterior pencil is measurable. -/
theorem measurable_normalizedExteriorSplitPencil (p : Params) (j : ZMod p.n)
    (V Γ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (e η : ℝ) :
    Measurable (normalizedExteriorSplitPencil p j V Γ e η) := by
  rw [Matrix.measurable_iff]
  intro a b
  change Measurable (fun ξ => normalizedExteriorPencil p j V Γ e η ξ
    (singletonPhysicalSplitEquiv p j a) (singletonPhysicalSplitEquiv p j b))
  unfold normalizedExteriorPencil
  exact measurable_const.mul
    (((((Matrix.measurable_iff.mp (measurable_hermitianExteriorMatrix p j)
      _ _).add measurable_const).sub measurable_const).add measurable_const))

/-- After removing the normalized scalar regulator, the imaginary part of the
normalized exterior pencil is exactly the normalized deterministic absorber. -/
theorem matrixImaginaryPart_normalizedExteriorPencil_sub_regulator
    (p : Params) (j : ZMod p.n)
    (V Γ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hV : V.IsHermitian) (hΓ : Γ.PosSemidef)
    (e η : ℝ) (ξ : exteriorUpperPairs p j → ℂ) :
    matrixImaginaryPart (normalizedExteriorPencil p j V Γ e η ξ) -
        ((η / Real.sqrt p.c : ℝ) : ℂ) •
          (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) =
      ((Real.sqrt p.c)⁻¹ : ℂ) • Γ := by
  let s : ℝ := (Real.sqrt p.c)⁻¹
  let A : Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
    (s : ℂ) • (hermitianExteriorMatrix p j ξ + V -
      (e : ℂ) • (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ))
  let Q : Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
    (s : ℂ) • (Γ + η • (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ))
  have hA : A.IsHermitian := by
    exact (((hermitianExteriorMatrix_isHermitian p j ξ).add hV).sub
      (Matrix.isHermitian_one.smul (RCLike.conj_ofReal e))).smul
        (RCLike.conj_ofReal s)
  have hQ : Q.IsHermitian := by
    exact (hΓ.isHermitian.add
      (Matrix.isHermitian_one.smul (RCLike.conj_ofReal η))).smul
        (RCLike.conj_ofReal s)
  have hpencil : normalizedExteriorPencil p j V Γ e η ξ =
      A + Complex.I • Q := by
    simp only [normalizedExteriorPencil, A, Q, s]
    module
  rw [hpencil, matrixImaginaryPart_add_I_smul A Q hA hQ]
  simp only [Q, s]
  have hs : Real.sqrt p.c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 p.c_pos)
  ext a b
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst b
    simp only [ite_true]
    simp only [Complex.real_smul]
    push_cast
    field_simp [hs]
    ring
  · simp only [hab, ite_false, mul_zero, add_zero, sub_zero, Complex.real_smul]
    push_cast
    rfl

/-- Block family cut out of the normalized exterior pencil. -/
def normalizedExteriorRegulatedFamily
    (p : Params) (j : ZMod p.n)
    (V Γ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hV : V.IsHermitian) (hΓ : Γ.PosSemidef)
    (e η : ℝ) (hη : 0 < η) :
    RegulatedBlockFamily (exteriorUpperPairs p j → ℂ)
      (BlockGUE.Index (singletonBlockSize p.W))
      (BlockSetSite ({j} : Set (ZMod p.n))ᶜ p.W)
      (η / Real.sqrt p.c) := by
  let F := normalizedExteriorSplitPencil p j V Γ e η
  have hF : Measurable F := measurable_normalizedExteriorSplitPencil p j V Γ e η
  refine
    { A := fun ξ => (F ξ).submatrix Sum.inl Sum.inl
      B := fun ξ => (F ξ).submatrix Sum.inl Sum.inr
      C := fun ξ => (F ξ).submatrix Sum.inr Sum.inl
      D := fun ξ => (F ξ).submatrix Sum.inr Sum.inr
      measurable_A := ?_
      measurable_B := ?_
      measurable_C := ?_
      measurable_D := ?_
      eta_pos := div_pos hη (Real.sqrt_pos.2 p.c_pos)
      imaginary_ge := ?_ }
  all_goals try
    · rw [Matrix.measurable_iff]
      intro a b
      exact Matrix.measurable_iff.mp hF _ _
  intro ξ
  have hblocks : Matrix.fromBlocks
      ((F ξ).submatrix Sum.inl Sum.inl)
      ((F ξ).submatrix Sum.inl Sum.inr)
      ((F ξ).submatrix Sum.inr Sum.inl)
      ((F ξ).submatrix Sum.inr Sum.inr) = F ξ := by
    ext (a | a) (b | b) <;> rfl
  rw [hblocks]
  have him0 := matrixImaginaryPart_normalizedExteriorPencil_sub_regulator
    p j V Γ hV hΓ e η ξ
  have him : matrixImaginaryPart (F ξ) -
      ((η / Real.sqrt p.c : ℝ) : ℂ) •
        (1 : Matrix
          (BlockGUE.Index (singletonBlockSize p.W) ⊕
            BlockSetSite ({j} : Set (ZMod p.n))ᶜ p.W)
          (BlockGUE.Index (singletonBlockSize p.W) ⊕
            BlockSetSite ({j} : Set (ZMod p.n))ᶜ p.W) ℂ) =
      (((Real.sqrt p.c)⁻¹ : ℂ) • Γ).submatrix
        (singletonPhysicalSplitEquiv p j) (singletonPhysicalSplitEquiv p j) := by
    ext a b
    have hab := congrFun (congrFun him0
      (singletonPhysicalSplitEquiv p j a))
      (singletonPhysicalSplitEquiv p j b)
    by_cases heq : a = b
    · subst b
      simpa [F, normalizedExteriorSplitPencil, matrixImaginaryPart,
        Complex.real_smul] using hab
    · have heq' : singletonPhysicalSplitEquiv p j a ≠
          singletonPhysicalSplitEquiv p j b :=
        (singletonPhysicalSplitEquiv p j).injective.ne heq
      simpa [F, normalizedExteriorSplitPencil, matrixImaginaryPart,
        heq, heq', Complex.real_smul] using hab
  rw [him]
  apply Matrix.PosSemidef.submatrix
  exact hΓ.smul (by
    exact_mod_cast (inv_nonneg.mpr (Real.sqrt_pos.2 p.c_pos).le))

end GaussianRing
end CoareaNative.BlockBand

namespace CoareaNative.BlockBand

namespace GaussianRing

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder ENNReal NNReal

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- On physical samples the normalized full pencil is the sum of the
coefficient-one exposed block and the Hermitianized exterior pencil. -/
theorem Law.normalized_physicalPencil_eq_exposed_add_exterior
    {p : Params} (M : Law p) (j : ZMod p.n)
    (V Γ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (e η : ℝ) (ω : M.Ω) :
    ((Real.sqrt p.c)⁻¹ : ℂ) •
        (M.H ω + V - (e : ℂ) • (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) +
          Complex.I • (Γ + η • (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ))) =
      ((Real.sqrt p.c)⁻¹ : ℂ) •
          physicalMatrixFromExteriorNormalizedBlock p j
            ((fun _ => 0), M.normalizedSingletonBlock j ω) +
        normalizedExteriorPencil p j V Γ e η
          (M.exteriorUpperCoordinates j ω) := by
  have hsplit := physicalMatrixFromExteriorNormalizedBlock_eq_exterior_add_exposed
    p j (M.exteriorUpperCoordinates j ω) (M.normalizedSingletonBlock j ω)
  rw [M.physicalMatrixFromExteriorNormalizedBlock_coordinates j ω] at hsplit
  unfold normalizedExteriorPencil
  rw [M.hermitianExteriorMatrix_coordinates j ω]
  rw [hsplit]
  module

/-- The normalized pencil, in singleton/complement order, has the exposed
standard GUE matrix added only to the upper-left block of the regulated exterior
family. -/
theorem Law.normalized_physicalSplitPencil_eq_fromBlocks
    {p : Params} (M : Law p) (j : ZMod p.n)
    (V Γ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hV : V.IsHermitian) (hΓ : Γ.PosSemidef)
    (e η : ℝ) (hη : 0 < η) (ω : M.Ω) :
    ((((Real.sqrt p.c)⁻¹ : ℂ) •
        (M.H ω + V -
          (e : ℂ) • (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) +
          Complex.I • (Γ + η •
            (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)))).submatrix
      (singletonPhysicalSplitEquiv p j) (singletonPhysicalSplitEquiv p j)) =
      let F := normalizedExteriorRegulatedFamily p j V Γ hV hΓ e η hη
      Matrix.fromBlocks
        (M.normalizedSingletonBlock j ω + F.A (M.exteriorUpperCoordinates j ω))
        (F.B (M.exteriorUpperCoordinates j ω))
        (F.C (M.exteriorUpperCoordinates j ω))
        (F.D (M.exteriorUpperCoordinates j ω)) := by
  let F := normalizedExteriorRegulatedFamily p j V Γ hV hΓ e η hη
  have hsum := congrArg
    (fun X : Matrix (Site p.n p.W) (Site p.n p.W) ℂ =>
      X.submatrix (singletonPhysicalSplitEquiv p j)
        (singletonPhysicalSplitEquiv p j))
    (M.normalized_physicalPencil_eq_exposed_add_exterior j V Γ e η ω)
  have hexposed := normalized_exposed_reindex_eq_fromBlocks p j
    (M.normalizedSingletonBlock j ω)
    (M.normalizedSingletonBlock_isHermitian j ω)
  have hF : normalizedExteriorSplitPencil p j V Γ e η
      (M.exteriorUpperCoordinates j ω) =
      Matrix.fromBlocks
        (F.A (M.exteriorUpperCoordinates j ω))
        (F.B (M.exteriorUpperCoordinates j ω))
        (F.C (M.exteriorUpperCoordinates j ω))
        (F.D (M.exteriorUpperCoordinates j ω)) := by
    ext (a | a) (b | b) <;> rfl
  change _ = Matrix.fromBlocks
    (M.normalizedSingletonBlock j ω + F.A (M.exteriorUpperCoordinates j ω))
    (F.B (M.exteriorUpperCoordinates j ω))
    (F.C (M.exteriorUpperCoordinates j ω))
    (F.D (M.exteriorUpperCoordinates j ω))
  rw [hsum]
  change
    (((((Real.sqrt p.c)⁻¹ : ℂ) •
      physicalMatrixFromExteriorNormalizedBlock p j
        ((fun _ => 0), M.normalizedSingletonBlock j ω)).submatrix
          (singletonPhysicalSplitEquiv p j) (singletonPhysicalSplitEquiv p j)) +
      normalizedExteriorSplitPencil p j V Γ e η
        (M.exteriorUpperCoordinates j ω)) = _
  rw [hexposed, hF]
  ext (a | a) (b | b) <;> simp

/-- Nonsingular inversion commutes with simultaneous reindexing along an equivalence. -/
theorem nonsing_inv_submatrix_equiv
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (A : Matrix n n ℂ) (hA : IsUnit A.det) :
    (A⁻¹).submatrix e e = (A.submatrix e e)⁻¹ := by
  let B := A.submatrix e e
  have hB : IsUnit B.det := by
    simpa [B] using hA
  have hleft : ((A⁻¹).submatrix e e) * B = 1 := by
    change (Matrix.reindexAlgEquiv ℂ ℂ e.symm) A⁻¹ *
      (Matrix.reindexAlgEquiv ℂ ℂ e.symm) A = 1
    rw [← map_mul, Matrix.nonsing_inv_mul A hA, map_one]
  calc
    (A⁻¹).submatrix e e = ((A⁻¹).submatrix e e) * 1 := by rw [mul_one]
    _ = ((A⁻¹).submatrix e e) * (B * B⁻¹) := by
      rw [Matrix.mul_nonsing_inv B hB]
    _ = (((A⁻¹).submatrix e e) * B) * B⁻¹ := by rw [Matrix.mul_assoc]
    _ = B⁻¹ := by rw [hleft, one_mul]

/-- The paper's block trace is the negative imaginary part of the ordinary trace of
the corresponding principal submatrix. -/
theorem blockNegativeImaginaryTrace_eq_trace_submatrix
    {β ι : Type*} [Fintype ι]
    (R : Matrix (β × ι) (β × ι) ℂ) (j : β) :
    blockNegativeImaginaryTrace R j =
      -(((R.submatrix (fun a : ι => (j, a)) (fun a : ι => (j, a))).trace).im) := by
  simp [blockNegativeImaginaryTrace, Matrix.trace]

/-- The measurable Schur background and absorber extracted from the regulated exterior
family give coefficient-one physical Schur data for the normalized full pencil. -/
def Law.normalizedPhysicalSchurMatrixData
    {p : Params} (M : Law p)
    (V Γ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hV : V.IsHermitian) (hΓ : Γ.PosSemidef)
    (e η : ℝ) (hη : 0 < η) :
    PhysicalSchurMatrixData M
      (fun j ω => blockNegativeImaginaryTrace
        ((((Real.sqrt p.c)⁻¹ : ℂ) •
          (M.H ω + V - (e : ℂ) •
            (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) +
            Complex.I • (Γ + η •
              (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ))))⁻¹) j)
      (η / Real.sqrt p.c) where
  background j ξ := ⟨
    (normalizedExteriorRegulatedFamily p j V Γ hV hΓ e η hη).background ξ,
    (normalizedExteriorRegulatedFamily p j V Γ hV hΓ e η hη).background_isHermitian ξ⟩
  absorber j :=
    (normalizedExteriorRegulatedFamily p j V Γ hV hΓ e η hη).absorber
  absorber_pos j ξ :=
    (normalizedExteriorRegulatedFamily p j V Γ hV hΓ e η hη).absorber_posSemidef ξ
  measurable_schurMatrixTrace j := by
    let F := normalizedExteriorRegulatedFamily p j V Γ hV hΓ e η hη
    have hsum : Measurable (fun z : (exteriorUpperPairs p j → ℂ) ×
        Matrix (BlockGUE.Index (singletonBlockSize p.W))
          (BlockGUE.Index (singletonBlockSize p.W)) ℂ =>
        ((F.background z.1 + z.2) + Complex.I •
          (F.absorber z.1 + (η / Real.sqrt p.c) • (1 : Matrix _ _ ℂ)))) := by
      rw [Matrix.measurable_iff]
      intro a b
      have hbg : Measurable (fun z : (exteriorUpperPairs p j → ℂ) ×
          Matrix (BlockGUE.Index (singletonBlockSize p.W))
            (BlockGUE.Index (singletonBlockSize p.W)) ℂ => F.background z.1 a b) :=
        (Matrix.measurable_iff.mp F.measurable_background a b).comp measurable_fst
      have hG : Measurable (fun z : (exteriorUpperPairs p j → ℂ) ×
          Matrix (BlockGUE.Index (singletonBlockSize p.W))
            (BlockGUE.Index (singletonBlockSize p.W)) ℂ => z.2 a b) :=
        (Matrix.measurable_iff.mp measurable_snd a b)
      have habs : Measurable (fun z : (exteriorUpperPairs p j → ℂ) ×
          Matrix (BlockGUE.Index (singletonBlockSize p.W))
            (BlockGUE.Index (singletonBlockSize p.W)) ℂ => F.absorber z.1 a b) :=
        (Matrix.measurable_iff.mp F.measurable_absorber a b).comp measurable_fst
      exact (hbg.add hG).add
        (measurable_const.mul (habs.add measurable_const))
    have hinv := Measurable.matrixNonsingInv hsum
    exact measurable_neg.comp
      (Complex.measurable_im.comp
        (by
          apply Finset.measurable_sum
          intro i hi
          exact Matrix.measurable_iff.mp hinv i i))
  physical_trace_eq j ω := by
    let F := normalizedExteriorRegulatedFamily p j V Γ hV hΓ e η hη
    let ξ := M.exteriorUpperCoordinates j ω
    let G := M.normalizedSingletonBlock j ω
    let P : Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
      ((Real.sqrt p.c)⁻¹ : ℂ) •
        (M.H ω + V - (e : ℂ) • (1 : Matrix _ _ ℂ) +
          Complex.I • (Γ + η • (1 : Matrix _ _ ℂ)))
    have hsplit := M.normalized_physicalSplitPencil_eq_fromBlocks
      j V Γ hV hΓ e η hη ω
    change blockNegativeImaginaryTrace (P⁻¹) j = _
    rw [blockNegativeImaginaryTrace_eq_trace_submatrix]
    have hG : G.IsHermitian := M.normalizedSingletonBlock_isHermitian j ω
    have hfullunit : IsUnit
        (Matrix.fromBlocks (G + F.A ξ) (F.B ξ) (F.C ξ) (F.D ξ)) := by
      apply isUnit_of_matrixImaginaryPart_posDef
      have him : matrixImaginaryPart
          (Matrix.fromBlocks (G + F.A ξ) (F.B ξ) (F.C ξ) (F.D ξ)) =
          matrixImaginaryPart
            (Matrix.fromBlocks (F.A ξ) (F.B ξ) (F.C ξ) (F.D ξ)) := by
        ext (a | a) (b | b)
        · have hGab := congrFun (congrFun hG a) b
          simp only [Matrix.conjTranspose_apply] at hGab
          simp only [matrixImaginaryPart, Matrix.smul_apply, Matrix.sub_apply,
            Matrix.conjTranspose_apply, Matrix.fromBlocks_apply₁₁,
            Matrix.add_apply]
          have hadd : star (G b a + F.A ξ b a) =
              G a b + star (F.A ξ b a) := by
            change (starRingEnd ℂ) (G b a + F.A ξ b a) =
              G a b + (starRingEnd ℂ) (F.A ξ b a)
            rw [map_add]
            exact congrArg (fun z : ℂ => z + (starRingEnd ℂ) (F.A ξ b a)) hGab
          rw [hadd]
          ring
        · simp [matrixImaginaryPart]
        · simp [matrixImaginaryPart]
        · simp [matrixImaginaryPart]
      rw [him]
      have hreg := F.imaginary_ge ξ
      have heta : (((η / Real.sqrt p.c : ℝ) : ℂ) •
          (1 : Matrix
            (BlockGUE.Index (singletonBlockSize p.W) ⊕
              BlockSetSite ({j} : Set (ZMod p.n))ᶜ p.W)
            (BlockGUE.Index (singletonBlockSize p.W) ⊕
              BlockSetSite ({j} : Set (ZMod p.n))ᶜ p.W) ℂ)).PosDef :=
        Matrix.PosDef.one.smul (by
          exact_mod_cast (div_pos hη (Real.sqrt_pos.2 p.c_pos)))
      have hpos := heta.add_posSemidef hreg
      have heq : (((η / Real.sqrt p.c : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)) +
          (matrixImaginaryPart
            (Matrix.fromBlocks (F.A ξ) (F.B ξ) (F.C ξ) (F.D ξ)) -
              ((η / Real.sqrt p.c : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)) =
          matrixImaginaryPart
            (Matrix.fromBlocks (F.A ξ) (F.B ξ) (F.C ξ) (F.D ξ)) := by
        abel
      rw [heq] at hpos
      exact hpos
    let _ : Invertible (Matrix.fromBlocks (G + F.A ξ) (F.B ξ) (F.C ξ) (F.D ξ)) :=
      Classical.choice hfullunit.nonempty_invertible
    have hPdet : IsUnit P.det := by
      have hdet := ((Matrix.fromBlocks (G + F.A ξ) (F.B ξ) (F.C ξ) (F.D ξ)).isUnit_iff_isUnit_det).mp hfullunit
      rw [← hsplit] at hdet
      simpa [P] using hdet
    have hreindex := nonsing_inv_submatrix_equiv
      (singletonPhysicalSplitEquiv p j) P hPdet
    have htrace :
        ((P⁻¹).submatrix (fun a : Fin p.W => (j, a))
          (fun a : Fin p.W => (j, a))).trace =
        ((P⁻¹).submatrix
          (fun a : BlockGUE.Index (singletonBlockSize p.W) =>
            singletonPhysicalSplitEquiv p j (Sum.inl a))
          (fun a : BlockGUE.Index (singletonBlockSize p.W) =>
            singletonPhysicalSplitEquiv p j (Sum.inl a))).trace := by
      simp only [Matrix.trace]
      symm
      rw [Fintype.sum_sigma, Fin.sum_univ_one]
      rfl
    rw [htrace]
    rw [show (P⁻¹).submatrix
          (fun a => singletonPhysicalSplitEquiv p j (Sum.inl a))
          (fun a => singletonPhysicalSplitEquiv p j (Sum.inl a)) =
        (((P.submatrix (singletonPhysicalSplitEquiv p j)
          (singletonPhysicalSplitEquiv p j))⁻¹).submatrix Sum.inl Sum.inl) by
      rw [← hreindex]
      rfl]
    rw [hsplit]
    let _ : Invertible (F.D ξ) :=
      Classical.choice (F.complement_isUnit ξ).nonempty_invertible
    rw [nonsing_inv_fromBlocks_submatrix₁₁_eq_schurComplement₂₂]
    have hschur : schurComplement₂₂ (G + F.A ξ) (F.B ξ) (F.C ξ) (F.D ξ) =
        G + F.schur ξ := by
      simp [schurComplement₂₂, RegulatedBlockFamily.schur, add_sub_assoc]
    rw [hschur, F.schur_eq_background_add_I_smul ξ]
    change -(((G + (F.background ξ + Complex.I •
      (F.absorber ξ + (η / Real.sqrt p.c) • (1 : Matrix _ _ ℂ))))⁻¹).trace).im = _
    simp only [schurMatrixTrace, F, ξ, G]
    have heq : G + (F.background ξ + Complex.I •
        (F.absorber ξ + (η / Real.sqrt p.c) • (1 : Matrix _ _ ℂ))) =
      (F.background ξ + G) + Complex.I •
        (F.absorber ξ + (η / Real.sqrt p.c) • (1 : Matrix _ _ ℂ)) := by
      module
    rw [heq]

/-- Nonsingular inversion of a nonzero scalar multiple pulls out the reciprocal
scalar, including for singular matrices because Mathlib's nonsingular inverse agrees
with the totalized ring inverse. -/
theorem nonsing_inv_smul_nonzero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (hc : c ≠ 0) (A : Matrix ι ι ℂ) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  rw [Matrix.nonsing_inv_eq_ringInverse, Matrix.nonsing_inv_eq_ringInverse]
  have hunit : IsUnit (c • (1 : Matrix ι ι ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    simp [hc]
  rw [show c • A = (c • (1 : Matrix ι ι ℂ)) * A by
    ext i j
    simp]
  rw [Ring.inverse_mul (Or.inl hunit)]
  have hscalar : Ring.inverse (c • (1 : Matrix ι ι ℂ)) =
      c⁻¹ • (1 : Matrix ι ι ℂ) := by
    have hright : (c • (1 : Matrix ι ι ℂ)) *
        (c⁻¹ • (1 : Matrix ι ι ℂ)) = 1 := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [hc]
      · simp [hij]
    calc
      Ring.inverse (c • (1 : Matrix ι ι ℂ)) =
          Ring.inverse (c • (1 : Matrix ι ι ℂ)) * 1 := by rw [mul_one]
      _ = Ring.inverse (c • (1 : Matrix ι ι ℂ)) *
          ((c • (1 : Matrix ι ι ℂ)) * (c⁻¹ • (1 : Matrix ι ι ℂ))) := by
            rw [hright]
      _ = (Ring.inverse (c • (1 : Matrix ι ι ℂ)) *
          (c • (1 : Matrix ι ι ℂ))) * (c⁻¹ • (1 : Matrix ι ι ℂ)) := by
            rw [Matrix.mul_assoc]
      _ = c⁻¹ • (1 : Matrix ι ι ℂ) := by
            rw [Ring.inverse_mul_cancel _ hunit, one_mul]
  rw [hscalar]
  ext i j
  simp

/-- The deterministic deformation and absorber written in the paper's physical
coordinates. -/
def physicalDeformedAbsorbedResolvent
    {p : Params} (M : Law p)
    (V Γ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (e η : ℝ) (ω : M.Ω) : Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  physicalAbsorbedResolvent (fun ω => M.H ω + V) (fun _ => Γ) e η ω

/-- Scaling the raw physical block trace by `sqrt p.c` gives the block trace of
the coefficient-one normalized pencil. -/
theorem Law.sqrt_mul_physicalTrace_eq_normalizedTrace
    {p : Params} (M : Law p)
    (V Γ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (e η : ℝ) (j : ZMod p.n) (ω : M.Ω) :
    Real.sqrt p.c * blockNegativeImaginaryTrace
      (physicalDeformedAbsorbedResolvent M V Γ e η ω) j =
      blockNegativeImaginaryTrace
        ((((Real.sqrt p.c)⁻¹ : ℂ) •
          (M.H ω + V - (e : ℂ) •
            (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) +
            Complex.I • (Γ + η •
              (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ))))⁻¹) j := by
  let Q : Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
    M.H ω + V - (e : ℂ) • (1 : Matrix _ _ ℂ) +
      Complex.I • (Γ + η • (1 : Matrix _ _ ℂ))
  have hs : Real.sqrt p.c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 p.c_pos)
  have hscale : Q = ((Real.sqrt p.c : ℝ) : ℂ) •
      (((Real.sqrt p.c)⁻¹ : ℂ) • Q) := by
    ext a b
    simp only [Matrix.smul_apply, smul_eq_mul]
    field_simp [hs]
  unfold physicalDeformedAbsorbedResolvent physicalAbsorbedResolvent
  change Real.sqrt p.c * blockNegativeImaginaryTrace (Q⁻¹) j = _
  rw [hscale, nonsing_inv_smul_nonzero _ (by exact_mod_cast hs)]
  unfold blockNegativeImaginaryTrace
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Matrix.smul_apply, smul_eq_mul]
  change Real.sqrt p.c *
      -((((((Real.sqrt p.c)⁻¹ : ℂ) *
        ((((Real.sqrt p.c)⁻¹ : ℂ) • Q)⁻¹ (j, i) (j, i))).im))) =
    -(((((Real.sqrt p.c)⁻¹ : ℂ) • Q)⁻¹ (j, i) (j, i)).im)
  rw [Complex.mul_im]
  simp [Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  field_simp [hs]

/-- The regulated physical pencil canonically constructs the corrected scaled Schur
input; no conditioning or disintegration hypothesis remains. -/
def Law.scaledPhysicalSchurMatrixData
    {p : Params} (M : Law p)
    (V Γ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hV : V.IsHermitian) (hΓ : Γ.PosSemidef)
    (e η : ℝ) (hη : 0 < η) :
    ScaledPhysicalSchurMatrixData M
      (fun j ω => blockNegativeImaginaryTrace
        (physicalDeformedAbsorbedResolvent M V Γ e η ω) j) η where
  normalized := by
    let h := M.normalizedPhysicalSchurMatrixData V Γ hV hΓ e η hη
    exact
      { background := h.background
        absorber := h.absorber
        absorber_pos := h.absorber_pos
        measurable_schurMatrixTrace := h.measurable_schurMatrixTrace
        physical_trace_eq := fun j ω => by
          rw [M.sqrt_mul_physicalTrace_eq_normalizedTrace V Γ e η j ω]
          exact h.physical_trace_eq j ω }

/-- Unconditional regulated projected-Wegner estimate for the physical Gaussian ring,
with the exact diagonal-variance loss `1 / sqrt p.c`. -/
theorem projectedWegner_gaussianRing_physical
    (input : PSSSInput.{0}) {p : Params} (M : Law.{0} p)
    (V Γ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hV : V.IsHermitian) (hΓ : Γ.PosSemidef)
    (e : ℝ) {η : ℝ} (hη : 0 < η) (B : Finset (ZMod p.n)) :
    ∫ ω, ∑ j ∈ B, blockNegativeImaginaryTrace
        (physicalDeformedAbsorbedResolvent M V Γ e η ω) j ∂M.P ≤
      Real.pi * (input.C / Real.sqrt p.c) * (p.W : ℝ) * (B.card : ℝ) := by
  exact projectedWegner_gaussianRing_resolvent_of_scaledSchurMatrixData
    input M e hη (fun ω => M.H ω + V) (fun _ => Γ)
      (M.scaledPhysicalSchurMatrixData V Γ hV hΓ e η hη) B

end GaussianRing
end CoareaNative.BlockBand
