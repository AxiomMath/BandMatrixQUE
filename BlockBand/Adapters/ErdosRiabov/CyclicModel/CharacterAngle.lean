module
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.GreenConvolution
public import Mathlib

/-!
# Character angles and the Fourier diagonalization of the stability operator

The cyclic character cosine is the cosine of the principal angle, so the covariance eigenvalue
is the cyclic symbol at that angle. The DFT diagonalizes the cyclic covariance and the stability
operator `I - αC` on every input; the Fourier Green convolution is a two-sided inverse for
`‖α‖ < 1`, and its tensorization with the identity on the within-block mean-zero sector is a
right inverse of the full-site stability operator.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERCharacterAngle

open scoped BigOperators
open ERProfile ERProfileAnalytic ERDiscreteFourier ERFourierInverse ERFourierAlgebra ERGreenConvolution

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The character cosine at the canonical nonnegative representative. -/
theorem characterCosine_eq_cos_rawAngle (p : Params) (r : ZMod p.n) :
    characterCosine p r =
      Real.cos (2 * Real.pi * (r.val : ℝ) / (p.n : ℝ)) := by
  unfold characterCosine
  have hr : ((r.val : ℤ) : ZMod p.n) = r := by
    norm_num [ZMod.natCast_zmod_val]
  conv_lhs => rw [← hr]
  rw [ZMod.stdAddChar_coe]
  rw [show
      (2 * (Real.pi : ℂ) * Complex.I * (r.val : ℤ) / (p.n : ℕ)) =
        ((2 * Real.pi * (r.val : ℝ) / (p.n : ℝ) : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  exact Complex.exp_ofReal_mul_I_re _

/-- Folding the canonical representative around the half-ring does not change its
cosine.  This covers the even antipode and the terminal modes of an odd ring with the
same formula. -/
theorem cos_rawAngle_eq_cos_principalAngle (p : Params) (r : ZMod p.n) :
    Real.cos (2 * Real.pi * (r.val : ℝ) / (p.n : ℝ)) =
      Real.cos (principalAngle p r) := by
  have hn : 0 < (p.n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 4) p.n_ge_four
  by_cases h : r.val ≤ p.n - r.val
  · rw [principalAngle, principalFrequency, min_eq_left h]
  · rw [principalAngle, principalFrequency, min_eq_right (Nat.le_of_not_ge h)]
    rw [← Real.cos_two_pi_sub
      (2 * Real.pi * (r.val : ℝ) / (p.n : ℝ))]
    congr 1
    have hr : r.val ≤ p.n := Nat.le_of_lt r.val_lt
    rw [Nat.cast_sub hr]
    field_simp

/-- The real part of the standard cyclic character is the cosine of the unoriented
principal angle. -/
theorem characterCosine_eq_cos_principalAngle (p : Params) (r : ZMod p.n) :
    characterCosine p r = Real.cos (principalAngle p r) := by
  rw [characterCosine_eq_cos_rawAngle, cos_rawAngle_eq_cos_principalAngle]

/-- The covariance eigenvalue is the analytic cyclic symbol evaluated at the
principal discrete angle. -/
theorem covarianceEigenvalue_eq_cyclicSymbol_principalAngle
    (p : Params) (r : ZMod p.n) :
    covarianceEigenvalue p r =
      (cyclicSymbol p.b (principalAngle p r) : ℝ) := by
  rw [covarianceEigenvalue_eq_cyclicSymbolCos,
    characterCosine_eq_cos_principalAngle]
  rfl

/-- The DFT of a forward translate acquires the positive standard character. -/
theorem cyclicDFT_add_one (p : Params) (f : ZMod p.n → ℂ) (r : ZMod p.n) :
    cyclicDFT p (fun x => f (x + 1)) r =
      ZMod.stdAddChar r * cyclicDFT p f r := by
  rw [cyclicDFT_apply, cyclicDFT_apply]
  calc
    ∑ x, ZMod.stdAddChar (-(x * r)) * f (x + 1) =
        ∑ x, ZMod.stdAddChar r *
          (ZMod.stdAddChar (-((x + 1) * r)) * f (x + 1)) := by
      apply Fintype.sum_congr
      intro x
      have harg : r + -((x + 1) * r) = -(x * r) := by simp [add_mul]
      rw [← mul_assoc, ← AddChar.map_add_eq_mul, harg]
    _ = ZMod.stdAddChar r *
        ∑ x, ZMod.stdAddChar (-((x + 1) * r)) * f (x + 1) := by
      rw [Finset.mul_sum]
    _ = ZMod.stdAddChar r *
        ∑ x, ZMod.stdAddChar (-(x * r)) * f x := by
      congr 1
      exact Equiv.sum_comp (Equiv.addRight (1 : ZMod p.n))
        (fun x : ZMod p.n => ZMod.stdAddChar (-(x * r)) * f x)

/-- The DFT of a backward translate acquires the negative standard character. -/
theorem cyclicDFT_sub_one (p : Params) (f : ZMod p.n → ℂ) (r : ZMod p.n) :
    cyclicDFT p (fun x => f (x - 1)) r =
      ZMod.stdAddChar (-r) * cyclicDFT p f r := by
  rw [cyclicDFT_apply, cyclicDFT_apply]
  calc
    ∑ x, ZMod.stdAddChar (-(x * r)) * f (x - 1) =
        ∑ x, ZMod.stdAddChar (-r) *
          (ZMod.stdAddChar (-((x - 1) * r)) * f (x - 1)) := by
      apply Fintype.sum_congr
      intro x
      have harg : -r + -((x - 1) * r) = -(x * r) := by ring
      rw [← mul_assoc, ← AddChar.map_add_eq_mul, harg]
    _ = ZMod.stdAddChar (-r) *
        ∑ x, ZMod.stdAddChar (-((x - 1) * r)) * f (x - 1) := by
      rw [Finset.mul_sum]
    _ = ZMod.stdAddChar (-r) *
        ∑ x, ZMod.stdAddChar (-(x * r)) * f x := by
      congr 1
      simpa [sub_eq_add_neg] using
        (Equiv.sum_comp (Equiv.addRight (-1 : ZMod p.n))
          (fun x : ZMod p.n => ZMod.stdAddChar (-(x * r)) * f x))

/-- Arbitrary-function diagonalization of the real-space cyclic covariance.  Unlike
the mode eigenvector statement, this identifies the DFT of the matrix
multiplication on every input. -/
theorem cyclicDFT_covariance_mulVec (p : Params) (f : ZMod p.n → ℂ)
    (r : ZMod p.n) :
    cyclicDFT p ((complexCyclicCovariance p).mulVec f) r =
      covarianceEigenvalue p r * cyclicDFT p f r := by
  rw [show (complexCyclicCovariance p).mulVec f =
      (p.c : ℂ) • f +
        (p.b : ℂ) • (fun x => f (x + 1)) +
        (p.b : ℂ) • (fun x => f (x - 1)) by
    funext x
    simp [complexCyclicCovariance, Matrix.mulVec, dotProduct,
      Finset.sum_add_distrib, add_mul]]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [cyclicDFT_add_one, cyclicDFT_sub_one]
  unfold covarianceEigenvalue
  ring

/-- The physical scalar stability operator `I-αC`. -/
def physicalStabilityOperator (p : Params) (α : ℂ) (f : ZMod p.n → ℂ) :
    ZMod p.n → ℂ :=
  (1 - α • complexCyclicCovariance p).mulVec f

/-- Arbitrary-function DFT diagonalization of the physical stability matrix. -/
theorem cyclicDFT_physicalStabilityOperator (p : Params) (α : ℂ)
    (f : ZMod p.n → ℂ) (r : ZMod p.n) :
    cyclicDFT p (physicalStabilityOperator p α f) r =
      stabilityMultiplier p α r * cyclicDFT p f r := by
  rw [physicalStabilityOperator, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec]
  change cyclicDFT p (f - α • (complexCyclicCovariance p).mulVec f) r = _
  simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [cyclicDFT_covariance_mulVec]
  unfold stabilityMultiplier
  ring

/-- The Fourier-coordinate stability operator is exactly the real-space matrix
operator, rather than merely an abstract diagonal multiplier. -/
theorem fourierStabilityOperator_eq_physical (p : Params) (α : ℂ)
    (f : ZMod p.n → ℂ) :
    fourierStabilityOperator p α f = physicalStabilityOperator p α f := by
  apply (cyclicDFT p).injective
  ext r
  rw [cyclicDFT_physicalStabilityOperator]
  simp [fourierStabilityOperator]

/-- The explicitly normalized Fourier Green convolution is a left inverse of the
real-space stability matrix on `‖α‖ < 1`. -/
theorem scalarStabilityInverse_physical_left (p : Params) {α : ℂ}
    (hα : ‖α‖ < 1) (f : ZMod p.n → ℂ) :
    scalarStabilityInverse p α (physicalStabilityOperator p α f) = f := by
  rw [← fourierStabilityOperator_eq_physical]
  exact scalarStabilityInverse_left p hα f

/-- The explicitly normalized Fourier Green convolution is also a right inverse of
the real-space stability matrix on `‖α‖ < 1`. -/
theorem scalarStabilityInverse_physical_right (p : Params) {α : ℂ}
    (hα : ‖α‖ < 1) (f : ZMod p.n → ℂ) :
    physicalStabilityOperator p α (scalarStabilityInverse p α f) = f := by
  rw [← fourierStabilityOperator_eq_physical]
  exact scalarStabilityInverse_right p hα f

/-- Complexification does not alter any scalar covariance entry. -/
theorem complexCyclicCovariance_apply (p : Params) (k l : ZMod p.n) :
    complexCyclicCovariance p k l = (cyclicCovariance p k l : ℂ) := by
  unfold complexCyclicCovariance cyclicCovariance blockWeight
  split_ifs <;> norm_cast

/-- Erdős–Riabov Proposition 2.8(ii), in operator form for an arbitrary complex site vector:
the full covariance first takes block averages and then applies the scalar cyclic
covariance. -/
theorem siteCovariance_dotProduct_eq_blockAverage (p : Params)
    (f : Site p.n p.W → ℂ) (x : Site p.n p.W) :
    dotProduct (fun y => (siteCovariance p x y : ℂ)) f =
      (complexCyclicCovariance p).mulVec (blockAverage p f) x.1 := by
  have hW : (p.W : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt p.W_pos
  simp only [dotProduct, Matrix.mulVec, blockAverage]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k hk
  rw [complexCyclicCovariance_apply]
  simp_rw [siteCovariance_apply]
  push_cast
  rw [← Finset.mul_sum]
  field_simp

/-- Averaging a block-constant site vector returns its block value. -/
@[simp] theorem blockAverage_blockConstant (p : Params) (g : ZMod p.n → ℂ)
    (k : ZMod p.n) :
    blockAverage p (fun x => g x.1) k = g k := by
  have hW : (p.W : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt p.W_pos
  simp [blockAverage]
  field_simp

/-- Averaging the canonical within-block remainder gives zero. -/
@[simp] theorem blockAverage_blockMeanZero (p : Params)
    (f : Site p.n p.W → ℂ) (k : ZMod p.n) :
    blockAverage p (blockMeanZeroPart p f) k = 0 := by
  unfold blockAverage
  rw [sum_blockMeanZeroPart p f k]
  simp

/-- Full-site physical stability operator. -/
def sitePhysicalStabilityOperator (p : Params) (α : ℂ)
    (f : Site p.n p.W → ℂ) : Site p.n p.W → ℂ :=
  fun x => f x - α * dotProduct (fun y => (siteCovariance p x y : ℂ)) f

/-- The full-site stability operator splits into scalar block stability and the
identity on the within-block mean-zero sector. -/
theorem sitePhysicalStabilityOperator_decomposition (p : Params) (α : ℂ)
    (f : Site p.n p.W → ℂ) (x : Site p.n p.W) :
    sitePhysicalStabilityOperator p α f x =
      physicalStabilityOperator p α (blockAverage p f) x.1 +
        blockMeanZeroPart p f x := by
  rw [sitePhysicalStabilityOperator,
    siteCovariance_dotProduct_eq_blockAverage]
  rw [physicalStabilityOperator, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec]
  change f x - α * (complexCyclicCovariance p).mulVec (blockAverage p f) x.1 =
    (blockAverage p f x.1 -
      α * (complexCyclicCovariance p).mulVec (blockAverage p f) x.1) +
      blockMeanZeroPart p f x
  rw [← block_decomposition p f x]
  simp only [blockConstantPart]
  ring

/-- Tensorized inverse: apply the scalar Green inverse to block averages and retain
the mean-zero sector, on which stability is the identity. -/
def siteStabilityInverse (p : Params) (α : ℂ)
    (f : Site p.n p.W → ℂ) : Site p.n p.W → ℂ :=
  fun x => scalarStabilityInverse p α (blockAverage p f) x.1 +
    blockMeanZeroPart p f x

/-- The block average of the tensorized inverse is the scalar inverse. -/
theorem blockAverage_siteStabilityInverse (p : Params) (α : ℂ)
    (f : Site p.n p.W → ℂ) (k : ZMod p.n) :
    blockAverage p (siteStabilityInverse p α f) k =
      scalarStabilityInverse p α (blockAverage p f) k := by
  have hW : (p.W : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt p.W_pos
  unfold blockAverage siteStabilityInverse
  simp_rw [Finset.sum_add_distrib, sum_blockMeanZeroPart]
  simp
  field_simp
  congr 2
  funext j
  rw [blockAverage, div_eq_mul_inv]
  ring

/-- The tensorized inverse likewise preserves the within-block mean-zero component. -/
theorem blockMeanZeroPart_siteStabilityInverse (p : Params) (α : ℂ)
    (f : Site p.n p.W → ℂ) (x : Site p.n p.W) :
    blockMeanZeroPart p (siteStabilityInverse p α f) x =
      blockMeanZeroPart p f x := by
  rw [blockMeanZeroPart, blockConstantPart,
    blockAverage_siteStabilityInverse, siteStabilityInverse]
  ring

/-- The tensorized Fourier-Green operator is a right inverse of the full-site
stability matrix. -/
theorem siteStabilityInverse_physical_right (p : Params) {α : ℂ}
    (hα : ‖α‖ < 1) (f : Site p.n p.W → ℂ) :
    sitePhysicalStabilityOperator p α (siteStabilityInverse p α f) = f := by
  have havg :
      blockAverage p (siteStabilityInverse p α f) =
        scalarStabilityInverse p α (blockAverage p f) := by
    funext k
    exact blockAverage_siteStabilityInverse p α f k
  funext x
  rw [sitePhysicalStabilityOperator_decomposition,
    havg,
    blockMeanZeroPart_siteStabilityInverse,
    scalarStabilityInverse_physical_right p hα]
  exact block_decomposition p f x

end BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERCharacterAngle
