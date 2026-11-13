module

public import BlockBand.Coarea.SchurDerivative

/-!
# Deterministic physical eigenvector reconstruction

An eigenvector of `H` with `det(H_R - λ) ≠ 0` is the Schur graph `(v, -Tv)` of its pair
restriction `v`, which solves the Schur eigenvector equation; for a normalized eigenvector the
inverse pair mass is the clock quadratic form `vᴴ (I + TᴴT) v`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section
namespace BlockBand.Coarea

open Matrix
open scoped ComplexOrder

/-- Schur graph vector, with the paper's negative exterior sign. -/
def schurGraph {m n : Type*} [Fintype m] [Fintype n] (T : Matrix n m ℂ)
    (v : m → ℂ) : m ⊕ n → ℂ := v ⊕ᵥ (-(T *ᵥ v))

/-- The Schur clock is positive semidefinite. -/
theorem schurClock_posSemidef
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) :
    (schurClock T).PosSemidef := by
  unfold schurClock
  exact Matrix.PosSemidef.one.add (Matrix.posSemidef_conjTranspose_mul_self T)

/-- The identity contribution makes the Schur clock strictly positive. -/
theorem schurClock_posDef
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) :
    (schurClock T).PosDef := by
  unfold schurClock
  exact Matrix.PosDef.one.add_posSemidef
    (Matrix.posSemidef_conjTranspose_mul_self T)

/-- In particular, the Schur clock is invertible. -/
theorem schurClock_isUnit
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) :
    IsUnit (schurClock T) :=
  (schurClock_posDef T).isUnit

/-- The clock quadratic form is exactly the squared mass of the reconstructed
Schur-graph vector.  This is the deterministic identity behind
the clock reconstruction identity. -/
theorem dotProduct_schurReconstruction_eq_schurClock
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) (v : m → ℂ) :
    star (v ⊕ᵥ (-(T *ᵥ v))) ⬝ᵥ (v ⊕ᵥ (-(T *ᵥ v))) =
      star v ⬝ᵥ (schurClock T *ᵥ v) := by
  rw [show star (v ⊕ᵥ (-(T *ᵥ v))) =
      (star v ⊕ᵥ star (-(T *ᵥ v))) by
    ext i
    cases i <;> rfl]
  rw [sumElim_dotProduct_sumElim]
  simp [schurClock, Matrix.add_mulVec, Matrix.mulVec_mulVec,
    Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]

/-- Every nonzero pair direction has a strictly positive clock. -/
theorem schurClock_quadratic_pos
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) {v : m → ℂ} (hv : v ≠ 0) :
    0 < star v ⬝ᵥ (schurClock T *ᵥ v) :=
  (schurClock_posDef T).dotProduct_mulVec_pos hv

/-- Consequently, the reconstructed Schur-graph vector of a nonzero pair
direction has strictly positive squared mass. -/
theorem dotProduct_schurReconstruction_pos
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) {v : m → ℂ} (hv : v ≠ 0) :
    0 < star (v ⊕ᵥ (-(T *ᵥ v))) ⬝ᵥ (v ⊕ᵥ (-(T *ᵥ v))) := by
  rw [dotProduct_schurReconstruction_eq_schurClock]
  exact schurClock_quadratic_pos T hv

/-- A normalized reconstruction `ψ = √mass (v,-Tv)` has
`mass⁻¹ = vᴴ (I+TᴴT) v` (the clock reconstruction identity of the coarea theorem).
All quantities are finite-dimensional and exact; there is no limiting or
probabilistic hypothesis. -/
theorem schurClock_eq_inv_mass_of_normalized
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) (v : m → ℂ) (mass : ℝ) (hmass : 0 < mass)
    (hnormalized :
      star ((Real.sqrt mass : ℂ) • (v ⊕ᵥ (-(T *ᵥ v)))) ⬝ᵥ
          ((Real.sqrt mass : ℂ) • (v ⊕ᵥ (-(T *ᵥ v)))) = 1) :
    star v ⬝ᵥ (schurClock T *ᵥ v) = ((mass⁻¹ : ℝ) : ℂ) := by
  have hsqrt : (Real.sqrt mass : ℂ) * (Real.sqrt mass : ℂ) = (mass : ℂ) := by
    norm_cast
    simpa [pow_two] using Real.sq_sqrt hmass.le
  have hscale :
      star ((Real.sqrt mass : ℂ) • (v ⊕ᵥ (-(T *ᵥ v)))) ⬝ᵥ
          ((Real.sqrt mass : ℂ) • (v ⊕ᵥ (-(T *ᵥ v)))) =
        (mass : ℂ) *
          (star (v ⊕ᵥ (-(T *ᵥ v))) ⬝ᵥ (v ⊕ᵥ (-(T *ᵥ v)))) := by
    rw [StarModule.star_smul, dotProduct_smul, smul_dotProduct]
    have hstar : star (Real.sqrt mass : ℂ) = (Real.sqrt mass : ℂ) := by simp
    rw [hstar]
    simp only [smul_eq_mul]
    rw [← mul_assoc, hsqrt]
  rw [hscale, dotProduct_schurReconstruction_eq_schurClock] at hnormalized
  have hm0 : (mass : ℂ) ≠ 0 := by exact_mod_cast hmass.ne'
  apply (mul_left_cancel₀ hm0)
  rw [hnormalized]
  norm_num [hmass.ne']

/-- Eliminating the exterior block gives the negative transfer graph. -/
theorem physical_exterior_eigenvector_eq_graph
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (H_R : Matrix n n ℂ) (C : Matrix n m ℂ) (E : ℝ)
    (hE : (H_R - (E : ℂ) • 1).det ≠ 0) (ψS : m → ℂ) (ψR : n → ℂ)
    (hExterior : C *ᵥ ψS + (H_R - (E : ℂ) • 1) *ᵥ ψR = 0) :
    ψR = -(physicalCoareaT H_R C E *ᵥ ψS) := by
  have hInv : physicalCoareaResolvent H_R E * (H_R - (E : ℂ) • 1) = 1 :=
    nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hE)
  have h := congrArg (fun x => physicalCoareaResolvent H_R E *ᵥ x) hExterior
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, hInv,
    Matrix.one_mulVec, Matrix.mulVec_zero] at h
  exact eq_neg_of_add_eq_zero_right h

/-- Both full block eigenvector equations imply the exact Schur null equation. -/
theorem physical_schur_eigenvector_equation
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (H_R : Matrix n n ℂ) (C : Matrix n m ℂ) (V G : Matrix m m ℂ) (E : ℝ)
    (hE : (H_R - (E : ℂ) • 1).det ≠ 0) (ψS : m → ℂ) (ψR : n → ℂ)
    (hExterior : C *ᵥ ψS + (H_R - (E : ℂ) • 1) *ᵥ ψR = 0)
    (hPair : (V + G - (E : ℂ) • 1) *ᵥ ψS + Cᴴ *ᵥ ψR = 0) :
    physicalCoareaA H_R C V G E *ᵥ ψS = 0 := by
  have hR := physical_exterior_eigenvector_eq_graph H_R C E hE ψS ψR hExterior
  have hA : physicalCoareaA H_R C V G E =
      (V + G - (E : ℂ) • 1) - Cᴴ * physicalCoareaT H_R C E := by
    simp only [physicalCoareaA, physicalCoareaF, physicalCoareaT, Matrix.mul_assoc]
    abel
  rw [hR, Matrix.mulVec_neg] at hPair
  rw [hA, Matrix.sub_mulVec]
  simpa only [sub_eq_add_neg, Matrix.mulVec_mulVec] using hPair

/-- A positive mass scale in a normalized Schur graph gives the exact
Euclidean normalization formula `psi = L / ||L||`. -/
theorem schurGraph_normalization_of_unit
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) (v : m → ℂ) (mass : ℝ) (hmass : 0 < mass)
    (hnormalized : star ((Real.sqrt mass : ℂ) • schurGraph T v) ⬝ᵥ
      ((Real.sqrt mass : ℂ) • schurGraph T v) = 1) :
    (Real.sqrt mass : ℂ) • schurGraph T v =
      ((‖WithLp.toLp 2 (schurGraph T v)‖⁻¹ : ℝ) : ℂ) • schurGraph T v := by
  have hClock := schurClock_eq_inv_mass_of_normalized T v mass hmass hnormalized
  have hNorm : ‖WithLp.toLp 2 (schurGraph T v)‖ ^ 2 = mass⁻¹ := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct]
    change (schurGraph T v ⬝ᵥ star (schurGraph T v)).re = mass⁻¹
    rw [dotProduct_comm]
    rw [schurGraph, dotProduct_schurReconstruction_eq_schurClock, hClock,
      Complex.ofReal_re]
  have hNorm' := congrArg Real.sqrt hNorm
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_inv] at hNorm'
  rw [hNorm', inv_inv]

/-- The three deterministic structural clauses of the prescribed-rank coarea
formula, derived from the block equations and unit full-vector norm.
`v` is explicitly `psiS/sqrt(mass)`.
When `mass` is the retained `L²` mass,
this is exactly the paper's normalized pair direction.
-/
theorem physical_normalized_eigenvector_reconstruction
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (H_R : Matrix n n ℂ) (C : Matrix n m ℂ) (V G : Matrix m m ℂ) (E : ℝ)
    (hE : (H_R - (E : ℂ) • 1).det ≠ 0) (ψS : m → ℂ) (ψR : n → ℂ)
    (hExterior : C *ᵥ ψS + (H_R - (E : ℂ) • 1) *ᵥ ψR = 0)
    (hPair : (V + G - (E : ℂ) • 1) *ᵥ ψS + Cᴴ *ᵥ ψR = 0)
    (mass : ℝ) (hmass : 0 < mass)
    (hUnit : star (ψS ⊕ᵥ ψR) ⬝ᵥ (ψS ⊕ᵥ ψR) = 1) :
    let v := ((Real.sqrt mass)⁻¹ : ℂ) • ψS
    physicalCoareaA H_R C V G E *ᵥ v = 0 ∧
      star v ⬝ᵥ (physicalCoareaD H_R C E *ᵥ v) = ((mass⁻¹ : ℝ) : ℂ) ∧
      (ψS ⊕ᵥ ψR) =
        ((‖WithLp.toLp 2 (schurGraph (physicalCoareaT H_R C E) v)‖⁻¹ : ℝ) : ℂ) •
          schurGraph (physicalCoareaT H_R C E) v := by
  dsimp only
  let v : m → ℂ := ((Real.sqrt mass)⁻¹ : ℂ) • ψS
  have hsqrt : Real.sqrt mass ≠ 0 := (Real.sqrt_pos.mpr hmass).ne'
  have hS : (Real.sqrt mass : ℂ) • v = ψS := by
    simp [v, smul_smul, hsqrt]
  have hR := physical_exterior_eigenvector_eq_graph H_R C E hE ψS ψR hExterior
  have hGraph : (ψS ⊕ᵥ ψR) =
      (Real.sqrt mass : ℂ) • schurGraph (physicalCoareaT H_R C E) v := by
    rw [hR, ← hS]
    ext i
    cases i <;> simp [schurGraph, Matrix.mulVec_smul]
  have hNormalized : star ((Real.sqrt mass : ℂ) •
      schurGraph (physicalCoareaT H_R C E) v) ⬝ᵥ
        ((Real.sqrt mass : ℂ) • schurGraph (physicalCoareaT H_R C E) v) = 1 := by
    rw [← hGraph]
    exact hUnit
  refine ⟨?_, ?_, ?_⟩
  · change physicalCoareaA H_R C V G E *ᵥ v = 0
    change physicalCoareaA H_R C V G E *ᵥ (((Real.sqrt mass)⁻¹ : ℂ) • ψS) = 0
    rw [Matrix.mulVec_smul,
      physical_schur_eigenvector_equation H_R C V G E hE ψS ψR hExterior hPair,
      smul_zero]
  · exact schurClock_eq_inv_mass_of_normalized
      (physicalCoareaT H_R C E) v mass hmass hNormalized
  · rw [hGraph]
    exact schurGraph_normalization_of_unit
      (physicalCoareaT H_R C E) v mass hmass hNormalized

end BlockBand.Coarea
