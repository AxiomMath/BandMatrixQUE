module

public import BlockBand.QUE.Haar.BlockMoments
public import BlockBand.QUE.HaarMomentReduction
public import BlockBand.QUE.FiniteTestBounds

/-!
# The site bridge under independent Haar rotations

For a fixed vector with blocks rotated by independent Haar unitaries, the variance of a site test
splits into the block-constant statistic and the within-block residual, with full factor
`1/(W+1)` (`rotated_site_bridge`, `rotated_site_le_block_add_width`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE.Haar

open Matrix MeasureTheory
open scoped BigOperators Classical
open BlockBand.Foundations.FiniteBlock

variable {B A : Type*} [Fintype B] [Fintype A] [DecidableEq A] [Nonempty A]

/-- Constant part of the site fluctuation after block rotation. -/
def blockFluctuation (v : B → A → ℂ) (baseline : ℝ) (w : B × A → ℝ) : ℝ :=
  ∑ b : B, average w b * (blockMass v b - (Fintype.card A : ℝ) * baseline)

omit [Nonempty A] in
/-- Block-constant statistics are deterministic under the rotations. -/
theorem fluctuation_constant_rotated (v : B → A → ℂ) (baseline : ℝ)
    (w : B × A → ℝ) (U : B → Matrix.unitaryGroup A ℂ) :
    fluctuation (rotatedMass v) baseline (constantPart w) U =
      blockFluctuation v baseline w := by
  unfold fluctuation blockFluctuation
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  simp only [constantPart, ← Finset.mul_sum, Finset.sum_sub_distrib,
    sum_rotatedMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [Nonempty A] in
/-- All squared site fluctuations are integrable under product Haar. -/
theorem integrable_rotated_fluctuation (v : B → A → ℂ) (baseline : ℝ) (w : B × A → ℝ) :
    Integrable (fun U => |fluctuation (rotatedMass v) baseline w U| ^ 2) blockProbability := by
  have hc : Continuous (fun U : B → Matrix.unitaryGroup A ℂ =>
      fluctuation (rotatedMass v) baseline w U) := by
    unfold fluctuation
    exact continuous_finsetSum _ (fun x _ =>
      continuous_const.mul ((continuous_rotatedMass v x).sub continuous_const))
  exact (hc.abs.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Coordinate covariance base dictated by independent Haar rotations. -/
def blockPairBase (v : B → A → ℂ) (b d : B) : ℝ :=
  if b = d then blockMass v b ^ 2 /
    ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) + 1))
  else (blockMass v b / (Fintype.card A : ℝ)) * (blockMass v d / (Fintype.card A : ℝ))

/-- Same-block diagonal excess dictated by the proved complex moments. -/
def blockDiagonalExcess (v : B → A → ℂ) (b : B) : ℝ :=
  blockMass v b ^ 2 / ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) + 1))

omit [Nonempty A] in
/-- Full coordinate second moments are constructed, including distinct-block
factorization and the within-block diagonal correction. -/
theorem integral_rotatedMass_pair (v : B → A → ℂ) (x y : B × A) :
    (∫ U, rotatedMass v U x * rotatedMass v U y ∂blockProbability) =
      blockPairBase v x.1 y.1 + if x = y then blockDiagonalExcess v x.1 else 0 := by
  rcases x with ⟨b, a⟩
  rcases y with ⟨d, c⟩
  by_cases hbd : b = d
  · subst d
    simpa [blockPairBase, blockDiagonalExcess] using integral_rotatedMass_same v b a c
  · have hxy : (b, a) ≠ (d, c) := by
      intro h
      exact hbd (congrArg Prod.fst h)
    simpa [blockPairBase, hbd, hxy] using integral_rotatedMass_distinct v b d hbd a c

/-- The mixed constant/centred statistic cancels under the Haar law, by the first moments and the
preserved block masses. -/
theorem rotated_statistic_decomposition (v : B → A → ℂ) (baseline : ℝ) (w : B × A → ℝ) :
    quadraticStatistic blockProbability (rotatedMass v) baseline w =
      quadraticStatistic blockProbability (rotatedMass v) baseline (constantPart w) +
      quadraticStatistic blockProbability (rotatedMass v) baseline (centeredPart w) := by
  apply statistic_decomposition blockProbability (rotatedMass v) baseline w
    (fun b => blockFluctuation v baseline w * (blockMass v b / (Fintype.card A : ℝ)))
    (integrable_rotated_fluctuation v baseline (constantPart w))
    (integrable_rotated_fluctuation v baseline (centeredPart w))
  · intro x
    simp_rw [fluctuation_constant_rotated]
    exact (integrable_rotatedMass v x).const_mul _
  · intro b a
    simp_rw [fluctuation_constant_rotated]
    rw [integral_const_mul, integral_rotatedMass]

/-- The complex Haar site bridge for a fixed vector, with the full variance and the mixed
cancellation (an inner-integration identity). -/
theorem rotated_site_bridge (v : B → A → ℂ) (baseline : ℝ) (w : B × A → ℝ) :
    quadraticStatistic blockProbability (rotatedMass v) baseline w =
      |blockFluctuation v baseline w| ^ 2 +
        ∑ b : B, blockDiagonalExcess v b * ∑ a : A, centeredPart w (b, a) ^ 2 := by
  rw [rotated_statistic_decomposition]
  have hconstant : quadraticStatistic blockProbability (rotatedMass v) baseline (constantPart w) =
      |blockFluctuation v baseline w| ^ 2 := by
    unfold quadraticStatistic
    simp_rw [fluctuation_constant_rotated]
    simp
  rw [hconstant]
  congr 1
  exact residual_statistic_of_second_moments blockProbability (rotatedMass v) baseline w
    (blockPairBase v) (blockDiagonalExcess v) (integrable_rotatedMass_product v)
    (by
      intro x y
      by_cases hxy : x = y
      · simpa only [ite_eq_left hxy] using integral_rotatedMass_pair v x y
      · simpa only [ite_eq_right hxy] using integral_rotatedMass_pair v x y)

/-- The inner Haar bridge in the block-average variance normalization, with the full factor
`1/(W+1)`. -/
theorem rotated_site_bridge_average (v : B → A → ℂ) (baseline : ℝ) (w : B × A → ℝ) :
    quadraticStatistic blockProbability (rotatedMass v) baseline w =
      |blockFluctuation v baseline w| ^ 2 +
        (1 / ((Fintype.card A : ℝ) + 1)) *
          ∑ b : B, blockMass v b ^ 2 *
            ((∑ a : A, w (b, a) ^ 2) / (Fintype.card A : ℝ) - average w b ^ 2) := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A).ne'
  rw [rotated_site_bridge]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [sum_centered_sq]
  unfold blockDiagonalExcess
  field_simp

/-- Finite test bound under the independent complex Haar law, with coefficient `1/(W+1)`, for
every normalized fixed vector and every positive width. -/
theorem rotated_site_le_block_add_width (v : B → A → ℂ) (baseline : ℝ)
    (hsum : ∑ b : B, blockMass v b = 1) (w : B × A → ℝ) (hw : ∀ x, |w x| ≤ 1) :
    quadraticStatistic blockProbability (rotatedMass v) baseline w ≤
      |blockFluctuation v baseline w| ^ 2 + 1 / ((Fintype.card A : ℝ) + 1) := by
  rw [rotated_site_bridge]
  apply add_le_add_right
  exact haar_weighted_residual_le (blockMass v)
    (fun b => Finset.sum_nonneg (fun a _ => sq_nonneg ‖v b a‖)) hsum w hw

end BlockBand.QUE.Haar
