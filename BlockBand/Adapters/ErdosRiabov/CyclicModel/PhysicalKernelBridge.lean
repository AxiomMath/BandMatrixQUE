module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.CyclicGreenSummation
public import Mathlib

/-!
# Entrywise ER kernel bridge and flattened-distance comparison

This module identifies the paper's matrices `Θ` and `Ξ` with the physical
site Green correction, including the exact full-site identity subtraction.
It then compares block cyclic distance with the row-major site distance used
in Erdős–Riabov's weighted clauses.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERPhysicalBridge

open scoped BigOperators
open ERProfile ERDiscreteFourier ERFourierInverse ERFourierAlgebra ERCharacterAngle ERNearestNeighbor ERCyclicDecay ERJumpNormalization ERCyclicSummation ERHerglotz

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Full-site stability as a matrix. -/
def siteStabilityMatrix (p : Params) (α : ℂ) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  1 - α • erComplexVarianceProfile p

/-- Full-site Green kernel as a matrix. -/
def siteGreenMatrix (p : Params) (α : ℂ) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  fun x y => siteGreenKernel p α x y

/-- Matrix multiplication by the stability matrix is the physical stability
operator used in the tensor inverse proof. -/
theorem siteStabilityMatrix_mulVec (p : Params) (α : ℂ)
    (f : Site p.n p.W → ℂ) :
    (siteStabilityMatrix p α).mulVec f =
      sitePhysicalStabilityOperator p α f := by
  funext x
  simp only [siteStabilityMatrix, sitePhysicalStabilityOperator,
    erComplexVarianceProfile, ERProfile.siteCovariance, Matrix.mulVec,
    dotProduct, Matrix.sub_apply, Matrix.smul_apply, sub_mul,
    Finset.sum_sub_distrib, Finset.mul_sum]
  rw [show (∑ i, (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) x i * f i) =
      f x by simp [Matrix.one_apply]]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The physical Green matrix is a right matrix inverse. -/
theorem siteStabilityMatrix_mul_siteGreenMatrix (p : Params) {α : ℂ}
    (hα : ‖α‖ < 1) :
    siteStabilityMatrix p α * siteGreenMatrix p α = 1 := by
  ext x y
  have h := congrFun (siteGreenKernel_physical_right p hα y) x
  rw [← siteStabilityMatrix_mulVec] at h
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, siteGreenMatrix,
    Matrix.one_apply] using h

/-- Consequently Mathlib's nonsingular matrix inverse is exactly the physical
Green matrix, with no change of normalization. -/
theorem siteStabilityMatrix_inv_eq_siteGreenMatrix (p : Params) {α : ℂ}
    (hα : ‖α‖ < 1) :
    (siteStabilityMatrix p α)⁻¹ = siteGreenMatrix p α :=
  Matrix.inv_eq_right_inv (siteStabilityMatrix_mul_siteGreenMatrix p hα)

/-- Algebraic resolvent correction identity `A(I-A)⁻¹=(I-A)⁻¹-I` for the
physical site covariance. -/
theorem covariance_mul_inverse_eq_green_sub_one (p : Params) {α : ℂ}
    (hα : ‖α‖ < 1) :
    (α • erComplexVarianceProfile p) *
        (1 - α • erComplexVarianceProfile p)⁻¹ =
      siteGreenMatrix p α - 1 := by
  have hinv : (1 - α • erComplexVarianceProfile p)⁻¹ =
      siteGreenMatrix p α := by
    exact siteStabilityMatrix_inv_eq_siteGreenMatrix p hα
  rw [hinv]
  have hright := siteStabilityMatrix_mul_siteGreenMatrix p hα
  unfold siteStabilityMatrix at hright
  rw [sub_mul, one_mul] at hright
  apply eq_sub_iff_add_eq.mpr
  simpa [add_comm] using (sub_eq_iff_eq_add.mp hright).symm

/-- Exact entrywise physical-kernel bridge for corrected `Θ`. -/
theorem erTheta_apply_eq_siteGreenKernel_sub_identity (p : Params)
    {z₁ z₂ : ℂ} (h₁ : z₁.im ≠ 0) (h₂ : z₂.im ≠ 0)
    (x y : Site p.n p.W) :
    erTheta p z₁ z₂ x y =
      siteGreenKernel p
        (erSemicircleStieltjes z₁ *
          starRingEnd ℂ (erSemicircleStieltjes z₂)) x y -
        (if x = y then 1 else 0) := by
  let α := erSemicircleStieltjes z₁ *
    starRingEnd ℂ (erSemicircleStieltjes z₂)
  have hα : ‖α‖ < 1 := norm_thetaMultiplier_lt_one
    (norm_erSemicircleStieltjes_lt_one h₁)
    (norm_erSemicircleStieltjes_lt_one h₂)
  have hmat := covariance_mul_inverse_eq_green_sub_one p hα
  have happ := congrFun (congrFun hmat x) y
  simpa [erTheta, α, siteGreenMatrix, Matrix.one_apply] using happ

/-- Exact entrywise physical-kernel bridge for `Ξ`. -/
theorem erXi_apply_eq_siteGreenKernel_sub_identity (p : Params)
    {z₁ z₂ : ℂ} (h₁ : z₁.im ≠ 0) (h₂ : z₂.im ≠ 0)
    (x y : Site p.n p.W) :
    erXi p z₁ z₂ x y =
      siteGreenKernel p
        (erSemicircleStieltjes z₁ * erSemicircleStieltjes z₂) x y -
        (if x = y then 1 else 0) := by
  let α := erSemicircleStieltjes z₁ * erSemicircleStieltjes z₂
  have hα : ‖α‖ < 1 := by
    rw [norm_mul]
    have h₁' := norm_erSemicircleStieltjes_lt_one h₁
    have h₂' := norm_erSemicircleStieltjes_lt_one h₂
    nlinarith [norm_nonneg (erSemicircleStieltjes z₁),
      norm_nonneg (erSemicircleStieltjes z₂)]
  have hmat := covariance_mul_inverse_eq_green_sub_one p hα
  have happ := congrFun (congrFun hmat x) y
  simpa [erXi, α, siteGreenMatrix, Matrix.one_apply] using happ

/-- Absolute distance between the canonical block representatives. -/
def blockRepresentativeDistance (p : Params) (x y : ZMod p.n) : ℕ :=
  max x.val y.val - min x.val y.val

/-- The two-path block distance is the circular distance between canonical
block representatives.  This formulation is convenient for comparison with
the row-major physical site numbering. -/
theorem cyclicBlockDistance_eq_min_representative (p : Params)
    (x y : ZMod p.n) :
    cyclicBlockDistance p x y =
      min (blockRepresentativeDistance p x y)
        (p.n - blockRepresentativeDistance p x y) := by
  unfold cyclicBlockDistance
  by_cases h : y.val ≤ x.val
  · rw [show orientedBlockDistance p x y = x.val - y.val by
      exact ZMod.val_sub h]
    simp [blockRepresentativeDistance, h]
  · have hxy : x.val < y.val := Nat.lt_of_not_ge h
    have hsub : (y - x).val = y.val - x.val :=
      ZMod.val_sub hxy.le
    have hne : y - x ≠ 0 := by
      rw [sub_ne_zero]
      intro hyx
      exact hxy.ne (congrArg ZMod.val hyx.symm)
    let _ : NeZero (y - x) := ⟨hne⟩
    have hneg : (x - y).val = p.n - (y.val - x.val) := by
      rw [show x - y = -(y - x) by abel,
        ZMod.val_neg_of_ne_zero (y - x), hsub]
    rw [show orientedBlockDistance p x y =
        p.n - (y.val - x.val) by exact hneg]
    have hd : y.val - x.val ≤ p.n := by
      exact (Nat.sub_le _ _).trans (ZMod.val_le y)
    simp [blockRepresentativeDistance, hxy.le,
      Nat.sub_sub_self hd, min_comm]

/-- Row-major flattening distorts the block cyclic distance by at most one
block.  The additive `W` is precisely the allowance for the two within-block
coordinates; the statement is uniform in the parity of the block cycle. -/
theorem width_mul_cyclicBlockDistance_le_siteDistance_add_width
    (p : Params) (x y : Site p.n p.W) :
    p.W * cyclicBlockDistance p x.1 y.1 ≤
      erSiteDistance p x y + p.W := by
  rw [cyclicBlockDistance_eq_min_representative]
  simp only [erSiteDistance,
    Conventions.ModelParameters.siteIndexEquiv_apply_val]
  let a := x.1.val
  let b := y.1.val
  let u := x.2.val
  let v := y.2.val
  have ha : a < p.n := ZMod.val_lt x.1
  have hb : b < p.n := ZMod.val_lt y.1
  have hu : u < p.W := x.2.isLt
  have hv : v < p.W := y.2.isLt
  change p.W *
      min (max a b - min a b) (p.n - (max a b - min a b)) ≤
    min (max (u + p.W * a) (v + p.W * b) -
          min (u + p.W * a) (v + p.W * b))
        (p.L - (max (u + p.W * a) (v + p.W * b) -
          min (u + p.W * a) (v + p.W * b))) + p.W
  rw [mul_min]
  unfold Conventions.ModelParameters.L Conventions.dimension
  by_cases hab : b ≤ a
  · simp only [max_eq_left hab, min_eq_right hab]
    simp only [Nat.mul_sub_left_distrib, Nat.mul_comm p.W p.n]
    by_cases hij : v + p.W * b ≤ u + p.W * a
    · simp only [max_eq_left hij, min_eq_right hij]
      omega
    · have hji : u + p.W * a ≤ v + p.W * b := Nat.le_of_not_ge hij
      simp only [max_eq_right hji, min_eq_left hji]
      omega
  · have hab' : a ≤ b := Nat.le_of_not_ge hab
    simp only [max_eq_right hab', min_eq_left hab']
    simp only [Nat.mul_sub_left_distrib, Nat.mul_comm p.W p.n]
    by_cases hij : v + p.W * b ≤ u + p.W * a
    · simp only [max_eq_left hij, min_eq_right hij]
      omega
    · have hji : u + p.W * a ≤ v + p.W * b := Nat.le_of_not_ge hij
      simp only [max_eq_right hji, min_eq_left hji]
      omega

/-- The converse row-major comparison.  Together with the preceding theorem,
this says that flattening changes `W` times the cyclic block distance by at
most one block width. -/
theorem siteDistance_le_width_mul_cyclicBlockDistance_add_width
    (p : Params) (x y : Site p.n p.W) :
    erSiteDistance p x y ≤
      p.W * cyclicBlockDistance p x.1 y.1 + p.W := by
  rw [cyclicBlockDistance_eq_min_representative]
  simp only [erSiteDistance,
    Conventions.ModelParameters.siteIndexEquiv_apply_val]
  let a := x.1.val
  let b := y.1.val
  let u := x.2.val
  let v := y.2.val
  have ha : a < p.n := ZMod.val_lt x.1
  have hb : b < p.n := ZMod.val_lt y.1
  have hu : u < p.W := x.2.isLt
  have hv : v < p.W := y.2.isLt
  change min (max (u + p.W * a) (v + p.W * b) -
          min (u + p.W * a) (v + p.W * b))
        (p.L - (max (u + p.W * a) (v + p.W * b) -
          min (u + p.W * a) (v + p.W * b))) ≤
    p.W * min (max a b - min a b)
      (p.n - (max a b - min a b)) + p.W
  rw [mul_min]
  unfold Conventions.ModelParameters.L Conventions.dimension
  by_cases hab : b ≤ a
  · simp only [max_eq_left hab, min_eq_right hab]
    simp only [Nat.mul_sub_left_distrib, Nat.mul_comm p.W p.n]
    by_cases hij : v + p.W * b ≤ u + p.W * a
    · simp only [max_eq_left hij, min_eq_right hij]
      omega
    · have hji : u + p.W * a ≤ v + p.W * b := Nat.le_of_not_ge hij
      simp only [max_eq_right hji, min_eq_left hji]
      have heq : a = b := by
        by_contra hne
        have hba : b < a := lt_of_le_of_ne hab (Ne.symm hne)
        have hgap : p.W * b + p.W ≤ p.W * a := by
          rw [← Nat.mul_succ]
          exact Nat.mul_le_mul_left p.W (Nat.succ_le_of_lt hba)
        omega
      have habval : a = y.1.val := by simpa [b] using heq
      have hmulEq : p.W * a = p.W * y.1.val :=
        congrArg (p.W * ·) habval
      subst b
      apply min_le_of_left_le
      omega
  · have hab' : a ≤ b := Nat.le_of_not_ge hab
    simp only [max_eq_right hab', min_eq_left hab']
    simp only [Nat.mul_sub_left_distrib, Nat.mul_comm p.W p.n]
    by_cases hij : v + p.W * b ≤ u + p.W * a
    · simp only [max_eq_left hij, min_eq_right hij]
      have heq : a = b := by
        by_contra hne
        have hablt : a < b := lt_of_le_of_ne hab' hne
        have hgap : p.W * a + p.W ≤ p.W * b := by
          rw [← Nat.mul_succ]
          exact Nat.mul_le_mul_left p.W (Nat.succ_le_of_lt hablt)
        omega
      subst b
      apply min_le_of_left_le
      omega
    · have hji : u + p.W * a ≤ v + p.W * b := Nat.le_of_not_ge hij
      simp only [max_eq_right hji, min_eq_left hji]
      omega

end BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERPhysicalBridge
