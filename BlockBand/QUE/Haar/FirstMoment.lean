module

public import BlockBand.QUE.Haar.CompactUnitary
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# First complex Haar coordinate moment from group invariance

Under the Haar probability measure on `U(A)`, every squared entry has mean `1/W`, and every
coordinate of a Haar-rotated fixed vector `v` has expected mass `‖v‖²/W`
(`integral_mulVec_mass`), by translation invariance under permutation matrices.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE.Haar

open MeasureTheory Matrix
open scoped BigOperators Classical

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- A permutation matrix, as an element of the complex unitary group. -/
def permutationUnitary (e : Equiv.Perm A) : Matrix.unitaryGroup A ℂ :=
  ⟨e.permMatrix ℂ, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp⟩

/-- Left multiplication by a permutation relabels row coordinates exactly. -/
theorem permutationUnitary_mul_apply (e : Equiv.Perm A)
    (U : Matrix.unitaryGroup A ℂ) (c a : A) :
    (permutationUnitary e * U) c a = U (e c) a := by
  change (e.permMatrix ℂ * (U : Matrix A A ℂ)) c a = _
  change (e.permMatrix ℂ *ᵥ fun d => U d a) c = _
  rw [Matrix.permMatrix_mulVec]
  rfl

/-- All Haar squared-entry observables are integrable. -/
theorem integrable_entry_mass (c a : A) :
    Integrable (fun U : Matrix.unitaryGroup A ℂ => ‖U c a‖ ^ 2)
      unitaryProbability := by
  apply Continuous.integrable_of_hasCompactSupport
    ((continuous_subtype_val.matrix_elem c a).norm.pow 2)
  exact HasCompactSupport.of_compactSpace _

/-- Coordinate permutation symmetry is proved by Haar translation. -/
theorem integral_entry_mass_eq (c d a : A) :
    (∫ U : Matrix.unitaryGroup A ℂ, ‖U c a‖ ^ 2 ∂unitaryProbability) =
      ∫ U : Matrix.unitaryGroup A ℂ, ‖U d a‖ ^ 2 ∂unitaryProbability := by
  have h := integral_unitary_translate
    (fun U : Matrix.unitaryGroup A ℂ => ‖U c a‖ ^ 2)
    (permutationUnitary (Equiv.swap c d))
  simpa only [permutationUnitary_mul_apply, Equiv.swap_apply_left] using h.symm

/-- The complex Haar first mass moment is exactly `1/W`, for every positive
width including width one. The denominator is the complex coordinate count. -/
theorem integral_entry_mass (c a : A) :
    (∫ U : Matrix.unitaryGroup A ℂ, ‖U c a‖ ^ 2 ∂unitaryProbability) =
      1 / (Fintype.card A : ℝ) := by
  have hpos : 0 < (Fintype.card A : ℝ) := by
    have : Nonempty A := ⟨c⟩
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  have hsum : (Fintype.card A : ℝ) *
      (∫ U : Matrix.unitaryGroup A ℂ, ‖U c a‖ ^ 2 ∂unitaryProbability) = 1 := by
    calc
      _ = ∑ d : A, ∫ U : Matrix.unitaryGroup A ℂ,
          ‖U d a‖ ^ 2 ∂unitaryProbability := by
        simp_rw [← integral_entry_mass_eq c _ a]
        simp
      _ = ∫ U : Matrix.unitaryGroup A ℂ,
          (∑ d : A, ‖U d a‖ ^ 2) ∂unitaryProbability := by
        rw [integral_finsetSum _ (fun d _ => integrable_entry_mass d a)]
      _ = 1 := by simp_rw [unitary_column_mass]; simp
  apply (eq_div_iff hpos.ne').2
  simpa [mul_comm] using hsum

/-- A unitary rotation preserves the total mass of every deterministic complex
vector, including the zero vector. -/
theorem unitary_mulVec_mass (U : Matrix.unitaryGroup A ℂ) (v : A → ℂ) :
    (∑ c : A, ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 2) =
      ∑ c : A, ‖v c‖ ^ 2 := by
  have hinner : star ((U : Matrix A A ℂ) *ᵥ v) ⬝ᵥ
      ((U : Matrix A A ℂ) *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      ← Matrix.star_eq_conjTranspose, Matrix.UnitaryGroup.star_mul_self, Matrix.vecMul_one]
  have h := congrArg Complex.re hinner
  simpa [dotProduct, Complex.mul_re, Complex.normSq_apply, Complex.sq_norm,
    mul_comm, ← pow_two] using h

/-- Squared masses of arbitrary deterministically rotated vectors are
integrable on the compact Haar probability space. -/
theorem integrable_mulVec_mass (v : A → ℂ) (c : A) :
    Integrable (fun U : Matrix.unitaryGroup A ℂ =>
      ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 2) unitaryProbability := by
  apply Continuous.integrable_of_hasCompactSupport
    (((continuous_apply c).comp
      (continuous_subtype_val.matrix_mulVec continuous_const)).norm.pow 2)
  exact HasCompactSupport.of_compactSpace _

/-- All coordinates of a Haar-rotated fixed vector have the same expected
mass, by permutation translation of the constructed Haar law. -/
theorem integral_mulVec_mass_eq (v : A → ℂ) (c d : A) :
    (∫ U : Matrix.unitaryGroup A ℂ,
      ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 2 ∂unitaryProbability) =
    ∫ U : Matrix.unitaryGroup A ℂ,
      ‖((U : Matrix A A ℂ) *ᵥ v) d‖ ^ 2 ∂unitaryProbability := by
  have h := integral_unitary_translate
    (fun U : Matrix.unitaryGroup A ℂ =>
      ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 2)
    (permutationUnitary (Equiv.swap c d))
  have hrot (U : Matrix.unitaryGroup A ℂ) :
      (((permutationUnitary (Equiv.swap c d) * U : Matrix.unitaryGroup A ℂ) :
        Matrix A A ℂ) *ᵥ v) c = ((U : Matrix A A ℂ) *ᵥ v) d := by
    change (((Equiv.swap c d).permMatrix ℂ * (U : Matrix A A ℂ)) *ᵥ v) c = _
    rw [← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec]
    simp
  simpa only [hrot] using h.symm

/-- First moment for every fixed complex vector: the total block mass divided by the complex
width (including the zero vector). -/
theorem integral_mulVec_mass (v : A → ℂ) (c : A) :
    (∫ U : Matrix.unitaryGroup A ℂ,
      ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 2 ∂unitaryProbability) =
      (∑ d : A, ‖v d‖ ^ 2) / (Fintype.card A : ℝ) := by
  have : Nonempty A := ⟨c⟩
  have hpos : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  apply (eq_div_iff hpos.ne').2
  calc
    _ = ∑ d : A, ∫ U : Matrix.unitaryGroup A ℂ,
        ‖((U : Matrix A A ℂ) *ᵥ v) d‖ ^ 2 ∂unitaryProbability := by
      simp_rw [← integral_mulVec_mass_eq v c _]
      simp [mul_comm]
    _ = ∫ U : Matrix.unitaryGroup A ℂ,
        (∑ d : A, ‖((U : Matrix A A ℂ) *ᵥ v) d‖ ^ 2) ∂unitaryProbability := by
      rw [integral_finsetSum _ (fun d _ => integrable_mulVec_mass v d)]
    _ = _ := by simp_rw [unitary_mulVec_mass]; simp

end BlockBand.QUE.Haar
