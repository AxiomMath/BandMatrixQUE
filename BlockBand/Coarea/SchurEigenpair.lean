module

public import BlockBand.Coarea.SchurReconstruction

/-!
# Retained mass and unit pair direction in deterministic coarea

For an eigenvector of `H`, the retained mass on the exposed pair is the squared norm of its pair
restriction; it is positive when the restriction is nonzero, and the normalized restriction is a
unit pair direction. These give the structural identities of an eigenpair in the deterministic
clause of the coarea theorem.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section
namespace BlockBand.Coarea

open Matrix

/-- Retained `L²` mass, with no division by the pair dimension. -/
def retainedMass {m : Type*} [Fintype m] (ψS : m → ℂ) : ℝ :=
  ∑ i, Complex.normSq (ψS i)

/-- The retained coordinate sum is the exact Euclidean squared norm. -/
theorem retainedMass_eq_norm_sq {m : Type*} [Fintype m] (ψS : m → ℂ) :
    retainedMass ψS = ‖WithLp.toLp 2 ψS‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [retainedMass, Complex.normSq_eq_norm_sq]

/-- Every nonzero retained vector has strictly positive retained `L²` mass. -/
theorem retainedMass_pos_of_ne_zero {m : Type*} [Fintype m]
    (ψS : m → ℂ) (hS : ψS ≠ 0) : 0 < retainedMass ψS := by
  have hNZ : WithLp.toLp 2 ψS ≠ 0 := by
    intro h
    apply hS
    funext i
    have h' := congrArg (fun x : EuclideanSpace ℂ m => x i) h
    simpa using h'
  rw [retainedMass_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr hNZ)

/-- A unit full eigenvector cannot have zero retained vector at a nonpole. -/
theorem physical_retained_vector_ne_zero
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (H_R : Matrix n n ℂ) (C : Matrix n m ℂ) (E : ℝ)
    (hE : (H_R - (E : ℂ) • 1).det ≠ 0) (ψS : m → ℂ) (ψR : n → ℂ)
    (hExterior : C *ᵥ ψS + (H_R - (E : ℂ) • 1) *ᵥ ψR = 0)
    (hUnit : ‖WithLp.toLp 2 (ψS ⊕ᵥ ψR)‖ = 1) : ψS ≠ 0 := by
  intro hS
  have hR := physical_exterior_eigenvector_eq_graph H_R C E hE ψS ψR hExterior
  rw [hS, Matrix.mulVec_zero, neg_zero] at hR
  have hZero : (ψS ⊕ᵥ ψR) = 0 := by
    ext i
    cases i <;> simp [hS, hR]
  rw [hZero] at hUnit
  simp at hUnit

/-- Pair direction chosen exactly as `v = psiS/sqrt(mass)`. -/
def physicalRetainedDirection {m : Type*} [Fintype m] (ψS : m → ℂ) : m → ℂ :=
  ((Real.sqrt (retainedMass ψS))⁻¹ : ℂ) • ψS

/-- The retained mass makes the chosen pair direction a unit `L²` vector. -/
theorem norm_physicalRetainedDirection {m : Type*} [Fintype m]
    (ψS : m → ℂ) (hS : ψS ≠ 0) :
    ‖WithLp.toLp 2 (physicalRetainedDirection ψS)‖ = 1 := by
  have hnorm : 0 < ‖WithLp.toLp 2 ψS‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 ψS)), ← retainedMass_eq_norm_sq]
    exact Real.sqrt_pos.mpr (retainedMass_pos_of_ne_zero ψS hS)
  rw [physicalRetainedDirection, retainedMass_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg _), WithLp.toLp_smul, norm_smul,
    norm_inv, Complex.norm_real, Real.norm_of_nonneg hnorm.le,
    inv_mul_cancel₀ hnorm.ne']

/-- The deterministic first clause of the coarea theorem, with the retained mass, its
positivity and the unit pair direction. The probability law and the ordered-rank selection are
not part of this statement. -/
theorem physical_eigenpair_structural_identities
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (H_R : Matrix n n ℂ) (C : Matrix n m ℂ) (V G : Matrix m m ℂ) (E : ℝ)
    (hE : (H_R - (E : ℂ) • 1).det ≠ 0) (ψS : m → ℂ) (ψR : n → ℂ)
    (hExterior : C *ᵥ ψS + (H_R - (E : ℂ) • 1) *ᵥ ψR = 0)
    (hPair : (V + G - (E : ℂ) • 1) *ᵥ ψS + Cᴴ *ᵥ ψR = 0)
    (hUnit : ‖WithLp.toLp 2 (ψS ⊕ᵥ ψR)‖ = 1) :
    let mass := retainedMass ψS
    let v := physicalRetainedDirection ψS
    0 < mass ∧ ‖WithLp.toLp 2 v‖ = 1 ∧
      physicalCoareaA H_R C V G E *ᵥ v = 0 ∧
      star v ⬝ᵥ (physicalCoareaD H_R C E *ᵥ v) = ((mass⁻¹ : ℝ) : ℂ) ∧
      (ψS ⊕ᵥ ψR) =
        ((‖WithLp.toLp 2 (schurGraph (physicalCoareaT H_R C E) v)‖⁻¹ : ℝ) : ℂ) •
          schurGraph (physicalCoareaT H_R C E) v := by
  have hS := physical_retained_vector_ne_zero H_R C E hE ψS ψR hExterior hUnit
  have hMass := retainedMass_pos_of_ne_zero ψS hS
  have hUnit' : star (ψS ⊕ᵥ ψR) ⬝ᵥ (ψS ⊕ᵥ ψR) = 1 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 (ψS ⊕ᵥ ψR))
    rw [EuclideanSpace.inner_eq_star_dotProduct, hUnit, dotProduct_comm] at h
    simpa using h
  have hStruct := physical_normalized_eigenvector_reconstruction
    H_R C V G E hE ψS ψR hExterior hPair (retainedMass ψS) hMass hUnit'
  exact ⟨hMass, norm_physicalRetainedDirection ψS hS, hStruct⟩

end BlockBand.Coarea
