module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPReplicatedFrechet
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Ward-gradient bounds for the replicated resolvent trace

Coordinate Parseval identities for the GUE directions and Ward contractions bound the gradient of
the normalized one-resolvent trace; with the Gaussian Poincaré inequality this bounds the
variances of its real and imaginary parts.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
@[expose] public section
noncomputable section

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal ComplexOrder Matrix.Norms.L2Operator

namespace CEHNative.BlockBand.External.CEH
namespace ReplicatedGUEEuclidean

open PencilAdapter

def rawHermitianDirection (n : ℕ) (c : HermitianCoordinate n) :
    Matrix (Fin n) (Fin n) ℂ :=
  hermitianMatrixOfCoordinates (Pi.single c 1)

lemma rawHermitianDirection_diagonal (n : ℕ) (i a b : Fin n) :
    rawHermitianDirection n (.inl i) a b = if a = i ∧ b = i then 1 else 0 := by
  simp only [rawHermitianDirection, hermitianMatrixOfCoordinates,
    hermitianUpperEntry, Pi.single_apply]
  split_ifs <;> aesop

lemma trace_mul_rawHermitianDirection_diagonal (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (A * rawHermitianDirection n (.inl i)).trace = A i i := by
  classical
  rw [Matrix.trace, Finset.sum_eq_single i]
  · change (A * rawHermitianDirection n (.inl i)) i i = A i i
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [rawHermitianDirection_diagonal]
    · intro b hb hbi
      simp [rawHermitianDirection_diagonal, hbi]
    · simp
  · intro b hb hbi
    change (A * rawHermitianDirection n (.inl i)) b b = 0
    rw [Matrix.mul_apply]
    simp [rawHermitianDirection_diagonal, hbi]
  · simp

lemma rawHermitianDirection_realUpper {n : ℕ} (ij : StrictUpperIndex n)
    (a b : Fin n) :
    rawHermitianDirection n (.inr (.inl ij)) a b =
      if a = ij.1.1 ∧ b = ij.1.2 then 1
      else if a = ij.1.2 ∧ b = ij.1.1 then 1 else 0 := by
  by_cases hab : a = b
  · subst b
    simp [rawHermitianDirection, hermitianMatrixOfCoordinates,
      hermitianUpperEntry, Pi.single_apply, ij.property.ne]
    by_cases h₁ : a = ij.1.1 ∧ a = ij.1.2
    · rcases h₁ with ⟨h₁, h₂⟩
      subst a
      omega
    · by_cases h₂ : a = ij.1.2 ∧ a = ij.1.1
      · rcases h₂ with ⟨h₂, h₁⟩
        subst a
        omega
      · simp [h₁, h₂]
  · by_cases hlt : a < b
    · simp [rawHermitianDirection, hermitianMatrixOfCoordinates,
        hermitianUpperEntry, Pi.single_apply, hab, hlt, Subtype.ext_iff]
      split_ifs <;> simp_all [Prod.ext_iff] <;> omega
    · have hba : b < a := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hab)
      simp [rawHermitianDirection, hermitianMatrixOfCoordinates,
        hermitianUpperEntry, Pi.single_apply, hab, hlt, hba, Subtype.ext_iff]
      have hf : ¬(a = ij.1.1 ∧ b = ij.1.2) := by
        intro h
        rcases h with ⟨rfl, rfl⟩
        omega
      have hr : ((b, a) = ij.1) ↔ (a = ij.1.2 ∧ b = ij.1.1) := by
        simp [Prod.ext_iff, and_comm]
      simp [hf, hr]

lemma rawHermitianDirection_imagUpper {n : ℕ} (ij : StrictUpperIndex n)
    (a b : Fin n) :
    rawHermitianDirection n (.inr (.inr ij)) a b =
      if a = ij.1.1 ∧ b = ij.1.2 then Complex.I
      else if a = ij.1.2 ∧ b = ij.1.1 then -Complex.I else 0 := by
  by_cases hab : a = b
  · subst b
    simp [rawHermitianDirection, hermitianMatrixOfCoordinates,
      hermitianUpperEntry, Pi.single_apply, ij.property.ne]
    by_cases h₁ : a = ij.1.1 ∧ a = ij.1.2
    · rcases h₁ with ⟨h₁, h₂⟩
      subst a
      omega
    · by_cases h₂ : a = ij.1.2 ∧ a = ij.1.1
      · rcases h₂ with ⟨h₂, h₁⟩
        subst a
        omega
      · simp [h₁, h₂]
  · by_cases hlt : a < b
    · simp [rawHermitianDirection, hermitianMatrixOfCoordinates,
        hermitianUpperEntry, Pi.single_apply, hab, hlt, Subtype.ext_iff]
      split_ifs <;> simp_all [Prod.ext_iff] <;> omega
    · have hba : b < a := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hab)
      simp [rawHermitianDirection, hermitianMatrixOfCoordinates,
        hermitianUpperEntry, Pi.single_apply, hab, hlt, hba, Subtype.ext_iff]
      have hf : ¬(a = ij.1.1 ∧ b = ij.1.2) := by
        intro h
        rcases h with ⟨rfl, rfl⟩
        omega
      have hr : ((b, a) = ij.1) ↔ (a = ij.1.2 ∧ b = ij.1.1) := by
        simp [Prod.ext_iff, and_comm]
      simp [hf, hr]

lemma mul_rawHermitianDirection_realUpper_diag {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (ij : StrictUpperIndex n) (r : Fin n) :
    (A * rawHermitianDirection n (.inr (.inl ij))) r r =
      if r = ij.1.1 then A ij.1.1 ij.1.2
      else if r = ij.1.2 then A ij.1.2 ij.1.1 else 0 := by
  classical
  rw [Matrix.mul_apply]
  simp only [rawHermitianDirection_realUpper, mul_ite, mul_one, mul_zero]
  by_cases hr₁ : r = ij.1.1
  · subst r
    rw [Finset.sum_eq_single ij.1.2]
    · simp [ij.property.ne]
    · intro q hq hne
      simp [hne, ij.property.ne]
    · simp
  · by_cases hr₂ : r = ij.1.2
    · subst r
      rw [Finset.sum_eq_single ij.1.1]
      · simp [ij.property.ne, ij.property.ne.symm]
      · intro q hq hne
        simp [hne, ij.property.ne, ij.property.ne.symm]
      · simp
    · simp [hr₁, hr₂]

lemma mul_rawHermitianDirection_imagUpper_diag {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (ij : StrictUpperIndex n) (r : Fin n) :
    (A * rawHermitianDirection n (.inr (.inr ij))) r r =
      if r = ij.1.1 then -(Complex.I * A ij.1.1 ij.1.2)
      else if r = ij.1.2 then Complex.I * A ij.1.2 ij.1.1 else 0 := by
  classical
  rw [Matrix.mul_apply]
  simp only [rawHermitianDirection_imagUpper, mul_ite, mul_zero]
  by_cases hr₁ : r = ij.1.1
  · subst r
    rw [Finset.sum_eq_single ij.1.2]
    · simp [ij.property.ne]
      ring
    · intro q hq hne
      simp [hne, ij.property.ne]
    · simp
  · by_cases hr₂ : r = ij.1.2
    · subst r
      rw [Finset.sum_eq_single ij.1.1]
      · simp [ij.property.ne, ij.property.ne.symm]
        ring
      · intro q hq hne
        simp [hne, ij.property.ne, ij.property.ne.symm]
      · simp
    · simp [hr₁, hr₂]

lemma trace_mul_rawHermitianDirection_realUpper {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (ij : StrictUpperIndex n) :
    (A * rawHermitianDirection n (.inr (.inl ij))).trace =
      A ij.1.1 ij.1.2 + A ij.1.2 ij.1.1 := by
  classical
  rw [Matrix.trace]
  change (∑ r, (A * rawHermitianDirection n (.inr (.inl ij))) r r) = _
  simp_rw [mul_rawHermitianDirection_realUpper_diag]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ ij.1.1)]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem
    (show ij.1.2 ∈ (Finset.univ : Finset (Fin n)) \ {ij.1.1} by
      simp [ij.property.ne.symm])]
  have hz : (∑ x ∈ ((Finset.univ : Finset (Fin n)) \ {ij.1.1}) \ {ij.1.2},
      if x = ij.1.1 then A ij.1.1 ij.1.2
      else if x = ij.1.2 then A ij.1.2 ij.1.1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hr₁ : r ≠ ij.1.1 := by
      exact fun h => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hr).1).2 (by simpa [h])
    have hr₂ : r ≠ ij.1.2 := by
      exact fun h => (Finset.mem_sdiff.mp hr).2 (by simpa [h])
    simp [hr₁, hr₂]
  rw [hz]
  simp [ij.property.ne, ij.property.ne.symm]

lemma trace_mul_rawHermitianDirection_imagUpper {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (ij : StrictUpperIndex n) :
    (A * rawHermitianDirection n (.inr (.inr ij))).trace =
      Complex.I * (A ij.1.2 ij.1.1 - A ij.1.1 ij.1.2) := by
  classical
  rw [Matrix.trace]
  change (∑ r, (A * rawHermitianDirection n (.inr (.inr ij))) r r) = _
  simp_rw [mul_rawHermitianDirection_imagUpper_diag]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ ij.1.1)]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem
    (show ij.1.2 ∈ (Finset.univ : Finset (Fin n)) \ {ij.1.1} by
      simp [ij.property.ne.symm])]
  have hz : (∑ x ∈ ((Finset.univ : Finset (Fin n)) \ {ij.1.1}) \ {ij.1.2},
      if x = ij.1.1 then -(Complex.I * A ij.1.1 ij.1.2)
      else if x = ij.1.2 then Complex.I * A ij.1.2 ij.1.1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hr₁ : r ≠ ij.1.1 := by
      exact fun h => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hr).1).2 (by simpa [h])
    have hr₂ : r ≠ ij.1.2 := by
      exact fun h => (Finset.mem_sdiff.mp hr).2 (by simpa [h])
    simp [hr₁, hr₂]
  rw [hz]
  simp [ij.property.ne, ij.property.ne.symm]
  ring

/-- For one strict upper-triangular pair, the real and imaginary GUE directions
satisfy the exact two-coordinate Parseval identity.  The normalization here is
that of `gueCoordinateDirection`: neither off-diagonal direction carries a
factor `1 / √2`. -/
lemma trace_rawHermitianDirection_upper_parseval {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (ij : StrictUpperIndex n) :
    ‖(A * rawHermitianDirection n (.inr (.inl ij))).trace‖ ^ 2 +
        ‖(A * rawHermitianDirection n (.inr (.inr ij))).trace‖ ^ 2 =
      2 * (‖A ij.1.1 ij.1.2‖ ^ 2 + ‖A ij.1.2 ij.1.1‖ ^ 2) := by
  rw [trace_mul_rawHermitianDirection_realUpper,
    trace_mul_rawHermitianDirection_imagUpper, norm_mul]
  norm_num [Complex.norm_I]
  have h := parallelogram_law_with_norm ℂ
    (A ij.1.1 ij.1.2) (A ij.1.2 ij.1.1)
  rw [norm_sub_rev] at h
  nlinarith

/-- Exact coordinate Parseval identity for the diagonal, real-upper and
imaginary-upper coordinates of an arbitrary complex matrix. -/
lemma sum_trace_rawHermitianDirection_sq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ c : HermitianCoordinate n,
        ‖(A * rawHermitianDirection n c).trace‖ ^ 2) =
      (∑ i : Fin n, ‖A i i‖ ^ 2) +
        2 * ∑ ij : StrictUpperIndex n,
          (‖A ij.1.1 ij.1.2‖ ^ 2 + ‖A ij.1.2 ij.1.1‖ ^ 2) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp_rw [trace_mul_rawHermitianDirection_diagonal]
  rw [← Finset.sum_add_distrib]
  simp_rw [trace_rawHermitianDirection_upper_parseval]
  rw [Finset.mul_sum]

/-- The matrix entry paired with a diagonal, real-upper, or imaginary-upper
Hermitian coordinate.  The two copies of `StrictUpperIndex` select opposite
orientations of the same strict pair. -/
def matrixEntryOfHermitianCoordinate {n : ℕ} :
    HermitianCoordinate n → Fin n × Fin n
  | .inl i => (i, i)
  | .inr (.inl ij) => ij.1
  | .inr (.inr ij) => (ij.1.2, ij.1.1)

lemma matrixEntryOfHermitianCoordinate_injective {n : ℕ} :
    Function.Injective (@matrixEntryOfHermitianCoordinate n) := by
  intro c₁ c₂ h
  rcases c₁ with i | c₁
  · rcases c₂ with j | c₂
    · simpa [matrixEntryOfHermitianCoordinate] using congrArg Prod.fst h
    · rcases c₂ with kl | kl
      · have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        simp only [matrixEntryOfHermitianCoordinate] at h₁ h₂
        have hkl := kl.property
        omega
      · have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        simp only [matrixEntryOfHermitianCoordinate] at h₁ h₂
        have hkl := kl.property
        omega
  · rcases c₁ with ij | ij
    · rcases c₂ with j | c₂
      · have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        simp only [matrixEntryOfHermitianCoordinate] at h₁ h₂
        have hij := ij.property
        omega
      · rcases c₂ with kl | kl
        · congr 2
          exact Subtype.ext h
        · have h₁ := congrArg Prod.fst h
          have h₂ := congrArg Prod.snd h
          simp only [matrixEntryOfHermitianCoordinate] at h₁ h₂
          have hij := ij.property
          have hkl := kl.property
          omega
    · rcases c₂ with j | c₂
      · have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        simp only [matrixEntryOfHermitianCoordinate] at h₁ h₂
        have hij := ij.property
        omega
      · rcases c₂ with kl | kl
        · have h₁ := congrArg Prod.fst h
          have h₂ := congrArg Prod.snd h
          simp only [matrixEntryOfHermitianCoordinate] at h₁ h₂
          have hij := ij.property
          have hkl := kl.property
          omega
        · congr 2
          apply Subtype.ext
          apply Prod.ext
          · simpa [matrixEntryOfHermitianCoordinate] using congrArg Prod.snd h
          · simpa [matrixEntryOfHermitianCoordinate] using congrArg Prod.fst h

lemma sum_matrixEntryOfHermitianCoordinate_sq_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ c : HermitianCoordinate n,
        ‖A (matrixEntryOfHermitianCoordinate c).1
          (matrixEntryOfHermitianCoordinate c).2‖ ^ 2) ≤
      ∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2 := by
  let f : (Fin n × Fin n) → ℝ := fun p => ‖A p.1 p.2‖ ^ 2
  have h := tsum_comp_le_tsum_of_inj
    (f := f) (Summable.of_finite) (fun _ => sq_nonneg _)
    matrixEntryOfHermitianCoordinate_injective
  simpa [f, tsum_fintype, Function.comp_def, Fintype.sum_prod_type] using h

/-- The exact coordinate computation implies the sharp factor-two comparison
with the entrywise Hilbert–Schmidt square mass. -/
lemma sum_trace_rawHermitianDirection_sq_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ c : HermitianCoordinate n,
        ‖(A * rawHermitianDirection n c).trace‖ ^ 2) ≤
      2 * ∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2 := by
  rw [sum_trace_rawHermitianDirection_sq]
  have hentry := sum_matrixEntryOfHermitianCoordinate_sq_le A
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hentry
  simp only [matrixEntryOfHermitianCoordinate] at hentry
  rw [Finset.sum_add_distrib]
  have hdiag : 0 ≤ ∑ i : Fin n, ‖A i i‖ ^ 2 := by positivity
  nlinarith

/-- The finite-ordinal GUE direction is exactly the raw Hermitian coordinate
direction transported along the coordinate equivalence. -/
lemma gueCoordinateDirection_eq_rawHermitianDirection (n : ℕ)
    (k : Fin (Fintype.card (HermitianCoordinate n))) :
    gueCoordinateDirection n k =
      rawHermitianDirection n ((hermitianCoordinateEquivFin n).symm k) := by
  unfold gueCoordinateDirection hermitianGUEBlock hermitianOfFinCoordinates
    hermitianOfCoordinates rawHermitianDirection
  rw [show Pi.single k (1 : ℝ) ∘ hermitianCoordinateEquivFin n =
      Pi.single ((hermitianCoordinateEquivFin n).symm k) 1 by
    simpa using piSingle_hermitianCoordinateEquivFin_comp n
      ((hermitianCoordinateEquivFin n).symm k)]

/-- Sharp factor-two Parseval bound in the finite-ordinal GUE chart. -/
theorem sum_trace_gueCoordinateDirection_sq_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ k : Fin (Fintype.card (HermitianCoordinate n)),
        ‖(A * gueCoordinateDirection n k).trace‖ ^ 2) ≤
      2 * ∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2 := by
  rw [← (hermitianCoordinateEquivFin n).sum_comp]
  simpa [gueCoordinateDirection_eq_rawHermitianDirection] using
    sum_trace_rawHermitianDirection_sq_le A

/-- The squared mass in one matrix row is controlled by the squared `ℓ²`
operator norm. -/
lemma matrix_row_norm_sq_le_l2_opNorm_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i : ι) :
    ∑ j, ‖A i j‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  let e : EuclideanSpace ℂ ι := WithLp.toLp 2 (Pi.single i 1)
  let v : EuclideanSpace ℂ ι :=
    (EuclideanSpace.equiv ι ℂ).symm ((A.conjTranspose).mulVec e.ofLp)
  have h := Matrix.l2_opNorm_mulVec A.conjTranspose e
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  have hv : ‖v‖ ≤ ‖A‖ := by
    simpa [v, Matrix.l2_opNorm_conjTranspose, he] using h
  have hsq := mul_self_le_mul_self (norm_nonneg v) hv
  rw [← sq, ← sq] at hsq
  simpa [v, e, EuclideanSpace.norm_sq_eq, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply] using hsq

/-- Entrywise Hilbert–Schmidt square mass is at most dimension times the
squared `ℓ²` operator norm. -/
lemma sum_matrix_entry_norm_sq_le_card_mul_l2_opNorm_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    (∑ i, ∑ j, ‖A i j‖ ^ 2) ≤
      (Fintype.card ι : ℝ) * ‖A‖ ^ 2 := by
  calc
    (∑ i, ∑ j, ‖A i j‖ ^ 2) ≤ ∑ _i : ι, ‖A‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => matrix_row_norm_sq_le_l2_opNorm_sq A i
    _ = (Fintype.card ι : ℝ) * ‖A‖ ^ 2 := by simp

/-- Squaring a matrix costs the fourth power of its operator norm in
entrywise Hilbert–Schmidt square mass. -/
lemma sum_matrix_sq_entry_norm_sq_le_card_mul_l2_opNorm_four
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    (∑ i, ∑ j, ‖(A * A) i j‖ ^ 2) ≤
      (Fintype.card ι : ℝ) * ‖A‖ ^ 4 := by
  calc
    (∑ i, ∑ j, ‖(A * A) i j‖ ^ 2) ≤
        (Fintype.card ι : ℝ) * ‖A * A‖ ^ 2 :=
      sum_matrix_entry_norm_sq_le_card_mul_l2_opNorm_sq (A * A)
    _ ≤ (Fintype.card ι : ℝ) * ‖A‖ ^ 4 := by
      gcongr
      calc
        ‖A * A‖ ^ 2 ≤ (‖A‖ * ‖A‖) ^ 2 := by
          gcongr
          exact norm_mul_le A A
        _ = ‖A‖ ^ 4 := by ring

/-- The nonreal resolvent bound in the matrix `ℓ²` operator norm. -/
lemma norm_hermitian_resolvent_l2_opNorm_le {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖(H - z • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹‖ ≤ |z.im|⁻¹ := by
  have hzero : (0 : Matrix (Fin n) (Fin n) ℂ).PosSemidef :=
    ⟨Matrix.isHermitian_zero, by intro u; simp⟩
  by_cases hzpos : 0 < z.im
  · let A := H - (z.re : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
    have hA : A.IsHermitian :=
      hH.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal z.re))
    have hshape :
        cauchyResolventPencil A 0 z.im 0 =
          (H - z • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hH.eq]
      ext p q
      by_cases hpq : p = q
      · subst q
        simp [A, cauchyResolventPencil, Complex.ext_iff]
      · simp [A, cauchyResolventPencil, hpq]
    have hb := norm_cauchyResolventPencil_nonsing_inv_le
      A 0 hA hzero hzpos (show 0 ≤ (0 : ℂ).im by simp)
    rw [hshape] at hb
    rw [← Matrix.conjTranspose_nonsing_inv,
      Matrix.l2_opNorm_conjTranspose] at hb
    simpa [abs_of_pos hzpos] using hb
  · have hzneg : z.im < 0 := lt_of_le_of_ne (le_of_not_gt hzpos) hz
    let A := H - (z.re : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
    have hA : A.IsHermitian :=
      hH.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal z.re))
    have hshape :
        cauchyResolventPencil A 0 (-z.im) 0 =
          H - z • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      ext p q
      by_cases hpq : p = q
      · subst q
        simp [A, cauchyResolventPencil, Complex.ext_iff]
        ring
      · simp [A, cauchyResolventPencil, hpq]
    have hb := norm_cauchyResolventPencil_nonsing_inv_le
      A 0 hA hzero (neg_pos.mpr hzneg)
      (show 0 ≤ (0 : ℂ).im by simp)
    rw [hshape] at hb
    simpa [abs_of_neg hzneg] using hb

/-- Ward/Hilbert–Schmidt contraction for the square of a Hermitian
resolvent. -/
theorem sum_hermitian_resolvent_sq_entry_norm_sq_le {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    (∑ i : Fin n, ∑ j : Fin n,
        ‖(((H - z • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹) *
          ((H - z • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹)) i j‖ ^ 2) ≤
      (n : ℝ) * |z.im|⁻¹ ^ 4 := by
  let G := (H - z • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹
  have hG := norm_hermitian_resolvent_l2_opNorm_le H hH hz
  calc
    (∑ i : Fin n, ∑ j : Fin n, ‖(G * G) i j‖ ^ 2) ≤
        (n : ℝ) * ‖G‖ ^ 4 := by
      simpa using sum_matrix_sq_entry_norm_sq_le_card_mul_l2_opNorm_four G
    _ ≤ (n : ℝ) * |z.im|⁻¹ ^ 4 := by
      gcongr

/-- The sharp coordinate Ward contraction: the sum of squared coordinate
traces of `G²` is bounded by `2 n |Im z|⁻⁴`. -/
theorem sum_trace_resolvent_sq_gueCoordinateDirection_le {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    let G := (H - z • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹
    (∑ k : Fin (Fintype.card (HermitianCoordinate n)),
        ‖((G * G) * gueCoordinateDirection n k).trace‖ ^ 2) ≤
      2 * (n : ℝ) * |z.im|⁻¹ ^ 4 := by
  dsimp only
  let G := (H - z • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹
  calc
    (∑ k : Fin (Fintype.card (HermitianCoordinate n)),
        ‖((G * G) * gueCoordinateDirection n k).trace‖ ^ 2) ≤
      2 * ∑ i : Fin n, ∑ j : Fin n, ‖(G * G) i j‖ ^ 2 :=
        sum_trace_gueCoordinateDirection_sq_le (G * G)
    _ ≤ 2 * ((n : ℝ) * |z.im|⁻¹ ^ 4) := by
      gcongr
      simpa [G] using sum_hermitian_resolvent_sq_entry_norm_sq_le H hH hz
    _ = 2 * (n : ℝ) * |z.im|⁻¹ ^ 4 := by ring

/-- Cyclicity places the coordinate direction between the two resolvents,
which is the form occurring in the Fréchet derivative. -/
theorem sum_trace_resolvent_gueCoordinateDirection_resolvent_le {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    let G := (H - z • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹
    (∑ k : Fin (Fintype.card (HermitianCoordinate n)),
        ‖(G * gueCoordinateDirection n k * G).trace‖ ^ 2) ≤
      2 * (n : ℝ) * |z.im|⁻¹ ^ 4 := by
  dsimp only
  let G := (H - z • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹
  change (∑ k, ‖(G * gueCoordinateDirection n k * G).trace‖ ^ 2) ≤ _
  rw [show (∑ k, ‖(G * gueCoordinateDirection n k * G).trace‖ ^ 2) =
      ∑ k, ‖((G * G) * gueCoordinateDirection n k).trace‖ ^ 2 by
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.trace_mul_cycle]]
  exact sum_trace_resolvent_sq_gueCoordinateDirection_le H hH hz

/-- Coordinate evaluation of the Fréchet derivative, rewritten using the one
common global resolvent rather than a coordinate-dependent affine pencil. -/
lemma fderiv_oneResolventTrace_apply_single_global
    {N d : ℕ} (f : Spectrum N) (lambda : ℝ) {z : ℂ}
    (hz : z.im ≠ 0)
    (k : Fin (Fintype.card (HermitianCoordinate (N * d))))
    (x : CoordinateEuclideanSpace N d) :
    let y := (coordinatesEquiv N d).symm x
    let G := scaledFullGUEResolvent
      (deformationMatrix (replicatedSpectrum d f)) lambda z y
    fderiv ℝ (oneResolventTrace d f lambda z) x
        (EuclideanSpace.single k 1) =
      -((((N * d : ℕ) : ℂ)⁻¹ * (lambda : ℂ)) *
        (G * gueCoordinateDirection (N * d) k * G).trace) := by
  dsimp only
  let y := (coordinatesEquiv N d).symm x
  rw [fderiv_oneResolventTrace_apply_single f lambda hz k x]
  dsimp only
  rw [← scaledReplicatedResolvent_update_eq_coordinateResolvent
    f lambda z k y (x k)]
  have hyk : Function.update y k (x k) = y := by
    apply Function.update_eq_self
  rw [hyk]
  let G := scaledFullGUEResolvent
    (deformationMatrix (replicatedSpectrum d f)) lambda z y
  let D := gueCoordinateDirection (N * d) k
  change (((N * d : ℕ) : ℂ)⁻¹ *
      ∑ i, -(G * ((lambda : ℂ) • D) * G) i i) =
    -(((((N * d : ℕ) : ℂ)⁻¹ * (lambda : ℂ)) *
      (G * D * G).trace))
  have hmat : G * ((lambda : ℂ) • D) * G =
      (lambda : ℂ) • (G * D * G) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hmat]
  unfold Matrix.trace
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.diag_apply]
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

/-- Sharp square-sum bound for all Euclidean coordinate evaluations of the
complex resolvent-trace derivative. -/
theorem sum_norm_fderiv_oneResolventTrace_apply_single_sq_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (x : CoordinateEuclideanSpace N d) :
    (∑ k : Fin (Fintype.card (HermitianCoordinate (N * d))),
      ‖fderiv ℝ (oneResolventTrace d f lambda z) x
        (EuclideanSpace.single k 1)‖ ^ 2) ≤
      2 * lambda ^ 2 * (((N * d : ℕ) : ℝ)⁻¹) * |z.im|⁻¹ ^ 4 := by
  let y := (coordinatesEquiv N d).symm x
  let H := deformedMatrix (replicatedSpectrum d f) lambda
    (hermitianGUEBlock (N * d) y).1
  let G := scaledFullGUEResolvent
    (deformationMatrix (replicatedSpectrum d f)) lambda z y
  have hH : H.IsHermitian := deformedMatrix_isHermitian _ _ _
    (hermitianGUEBlock_isHermitian (N * d) y)
  have hG : G = (H - z • (1 : Matrix (Fin (N * d)) (Fin (N * d)) ℂ))⁻¹ := by
    rfl
  have hward :=
    sum_trace_resolvent_gueCoordinateDirection_resolvent_le H hH hz
  rw [← hG] at hward
  simp_rw [fderiv_oneResolventTrace_apply_single_global f lambda hz]
  simp only [norm_neg, norm_mul, norm_inv, norm_natCast, Nat.cast_mul,
    Nat.cast_ofNat, Complex.norm_real, Real.norm_eq_abs]
  change (∑ k, ((((N : ℝ) * (d : ℝ))⁻¹ * |lambda|) *
      ‖(G * gueCoordinateDirection (N * d) k * G).trace‖) ^ 2) ≤ _
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  calc
    (((N : ℝ) * (d : ℝ))⁻¹) ^ 2 * |lambda| ^ 2 *
        (∑ k, ‖(G * gueCoordinateDirection (N * d) k * G).trace‖ ^ 2) ≤
      (((N : ℝ) * (d : ℝ))⁻¹) ^ 2 * |lambda| ^ 2 *
        (2 * ((N : ℝ) * (d : ℝ)) * |z.im|⁻¹ ^ 4) := by
          gcongr
          simpa only [Nat.cast_mul] using hward
    _ = 2 * lambda ^ 2 * (((N : ℝ) * (d : ℝ))⁻¹) * |z.im|⁻¹ ^ 4 := by
      rw [sq_abs]
      field_simp

/-- Sharp squared operator-norm bound for the real component of the global
Fréchet derivative. -/
theorem norm_fderiv_oneResolventTrace_re_sq_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (x : CoordinateEuclideanSpace N d) :
    ‖fderiv ℝ (fun y => (oneResolventTrace d f lambda z y).re) x‖ ^ 2 ≤
      2 * lambda ^ 2 * (((N * d : ℕ) : ℝ)⁻¹) * |z.im|⁻¹ ^ 4 := by
  let L := fderiv ℝ (fun y => (oneResolventTrace d f lambda z y).re) x
  rw [OrthonormalBasis.norm_dual (EuclideanSpace.basisFun _ ℝ) L]
  calc
    (∑ k, L ((EuclideanSpace.basisFun _ ℝ) k) ^ 2) ≤
        ∑ k, ‖fderiv ℝ (oneResolventTrace d f lambda z) x
          (EuclideanSpace.single k 1)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      have heval : L ((EuclideanSpace.basisFun _ ℝ) k) =
          (fderiv ℝ (oneResolventTrace d f lambda z) x
            (EuclideanSpace.single k 1)).re := by
        simp [L, fderiv_oneResolventTrace_re f lambda hz]
      rw [heval]
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2
        (Complex.abs_re_le_norm _)
    _ ≤ 2 * lambda ^ 2 * (((N * d : ℕ) : ℝ)⁻¹) * |z.im|⁻¹ ^ 4 :=
      sum_norm_fderiv_oneResolventTrace_apply_single_sq_le hN hd f lambda hz x

/-- Sharp squared operator-norm bound for the imaginary component of the
global Fréchet derivative. -/
theorem norm_fderiv_oneResolventTrace_im_sq_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (x : CoordinateEuclideanSpace N d) :
    ‖fderiv ℝ (fun y => (oneResolventTrace d f lambda z y).im) x‖ ^ 2 ≤
      2 * lambda ^ 2 * (((N * d : ℕ) : ℝ)⁻¹) * |z.im|⁻¹ ^ 4 := by
  let L := fderiv ℝ (fun y => (oneResolventTrace d f lambda z y).im) x
  rw [OrthonormalBasis.norm_dual (EuclideanSpace.basisFun _ ℝ) L]
  calc
    (∑ k, L ((EuclideanSpace.basisFun _ ℝ) k) ^ 2) ≤
        ∑ k, ‖fderiv ℝ (oneResolventTrace d f lambda z) x
          (EuclideanSpace.single k 1)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      have heval : L ((EuclideanSpace.basisFun _ ℝ) k) =
          (fderiv ℝ (oneResolventTrace d f lambda z) x
            (EuclideanSpace.single k 1)).im := by
        simp [L, fderiv_oneResolventTrace_im f lambda hz]
      rw [heval]
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2
        (Complex.abs_im_le_norm _)
    _ ≤ 2 * lambda ^ 2 * (((N * d : ℕ) : ℝ)⁻¹) * |z.im|⁻¹ ^ 4 :=
      sum_norm_fderiv_oneResolventTrace_apply_single_sq_le hN hd f lambda hz x

/-- Concrete Gaussian Poincaré bound for the real part of the normalized
one-resolvent trace, with the sharp Ward-gradient constant. -/
theorem variance_oneResolventTrace_re_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Var[(fun x : CoordinateEuclideanSpace N d =>
        (oneResolventTrace d f lambda z x).re); measure N d] ≤
      (Real.pi ^ 2 / 4) * lambda ^ 2 *
        (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4 := by
  let C : ℝ := 2 * lambda ^ 2 * (((N * d : ℕ) : ℝ)⁻¹) * |z.im|⁻¹ ^ 4
  have hC : 0 ≤ C := by positivity
  have h := variance_measure_le_of_fderiv_bound hN hd
    (contDiff_oneResolventTrace_re f lambda hz)
    (Real.sqrt_nonneg C)
    (fun x => Real.le_sqrt_of_sq_le
      (norm_fderiv_oneResolventTrace_re_sq_le hN hd f lambda hz x))
  rw [Real.sq_sqrt hC] at h
  calc
    Var[(fun x : CoordinateEuclideanSpace N d =>
        (oneResolventTrace d f lambda z x).re); measure N d] ≤
      (Real.pi ^ 2 / 8) * (1 / (((N * d : ℕ) : ℝ))) * C := h
    _ = (Real.pi ^ 2 / 4) * lambda ^ 2 *
        (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4 := by
      dsimp [C]
      rw [one_div]
      ring

/-- Concrete Gaussian Poincaré bound for the imaginary part of the normalized
one-resolvent trace, with the sharp Ward-gradient constant. -/
theorem variance_oneResolventTrace_im_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Var[(fun x : CoordinateEuclideanSpace N d =>
        (oneResolventTrace d f lambda z x).im); measure N d] ≤
      (Real.pi ^ 2 / 4) * lambda ^ 2 *
        (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4 := by
  let C : ℝ := 2 * lambda ^ 2 * (((N * d : ℕ) : ℝ)⁻¹) * |z.im|⁻¹ ^ 4
  have hC : 0 ≤ C := by positivity
  have h := variance_measure_le_of_fderiv_bound hN hd
    (contDiff_oneResolventTrace_im f lambda hz)
    (Real.sqrt_nonneg C)
    (fun x => Real.le_sqrt_of_sq_le
      (norm_fderiv_oneResolventTrace_im_sq_le hN hd f lambda hz x))
  rw [Real.sq_sqrt hC] at h
  calc
    Var[(fun x : CoordinateEuclideanSpace N d =>
        (oneResolventTrace d f lambda z x).im); measure N d] ≤
      (Real.pi ^ 2 / 8) * (1 / (((N * d : ℕ) : ℝ))) * C := h
    _ = (Real.pi ^ 2 / 4) * lambda ^ 2 *
        (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4 := by
      dsimp [C]
      rw [one_div]
      ring

end ReplicatedGUEEuclidean
end CEHNative.BlockBand.External.CEH
