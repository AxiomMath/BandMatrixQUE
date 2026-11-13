module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedWeightedCell
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.SingleBlockDOSLimit
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.UniformVectorOperatorCorollary

/-!
# Source-correct deterministic cells for the fixed-target Minami reduction

These lemmas are deliberately independent of every moving-predecessor module.
They concern only the auxiliary half-open cell in `Ioo (-xi) xi`; the
multiplicative weight is an arbitrary nonnegative scalar, so the later
specialization can retain the full-public fixed-`Icc a b` predecessor.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 700000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- Width of one of the `2^M` equal auxiliary cells in `(-xi,xi)`. -/
def correctedMinamiCellWidth (xi : ℝ) (M : ℕ) : ℝ :=
  2 * xi / (2 ^ M : ℝ)

/-- Midpoint of the `n`th corrected auxiliary cell. -/
def correctedMinamiCellMidpoint (xi : ℝ) (M : ℕ) (n : Fin (2 ^ M)) : ℝ :=
  -xi + n * correctedMinamiCellWidth xi M +
    correctedMinamiCellWidth xi M / 2

/-- An eigenvalue in an auxiliary cell is at distance at most half the width
from the cell midpoint. -/
theorem corrected_abs_orderedEigenvalue_sub_cellMidpoint_le_half {N m : ℕ}
    (H : HermitianMatrix (Fin N)) (a w : ℝ) (_hw : 0 < w) (n : Fin m)
    {i : Fin (Fintype.card (Fin N))}
    (hi : orderedEigenvalue H i ∈
      Set.Ico (a + n * w) (a + (n + 1) * w)) :
    |orderedEigenvalue H i - (a + n * w + w / 2)| ≤ w / 2 := by
  rw [abs_le]
  constructor <;> linarith [hi.1, hi.2]

/-- Occupancy of a positive-width auxiliary cell forces the inverse at its
midpoint to have operator norm at least `2 / w`. -/
theorem corrected_two_div_width_le_l2_opNorm_of_gridCellOccupied {N m : ℕ}
    (H : HermitianMatrix (Fin N)) (a w : ℝ) (hw : 0 < w) (n : Fin m)
    (hocc : gridCellOccupied H a w n)
    (hunit : IsUnit
      (H.1 - ((a + n * w + w / 2 : ℝ) : ℂ) •
        (1 : Matrix (Fin N) (Fin N) ℂ))) :
    2 / w ≤
      ‖(H.1 - ((a + n * w + w / 2 : ℝ) : ℂ) •
        (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹‖ := by
  rcases hocc with ⟨i, hi⟩
  let c : ℝ := a + n * w + w / 2
  have hgap : orderedEigenvalue H i ≠ c := by
    have hdet :
        (H.1 - (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).det ≠ 0 := by
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hunit
      exact hunit
    have hzero := eigenCount_singleton_eq_zero_of_det_energyShift_ne_zero H c hdet
    exact (eigenCount_singleton_eq_zero_iff H c).1 hzero i
  have hpos : 0 < |orderedEigenvalue H i - c| :=
    abs_pos.mpr (sub_ne_zero.mpr hgap)
  have hhalf : |orderedEigenvalue H i - c| ≤ w / 2 := by
    exact corrected_abs_orderedEigenvalue_sub_cellMidpoint_le_half H a w hw n hi
  have hinv := inv_gap_le_l2_opNorm H i c hunit
  have hanti : (w / 2)⁻¹ ≤ |orderedEigenvalue H i - c|⁻¹ :=
    inv_anti₀ hpos hhalf
  calc
    2 / w = (w / 2)⁻¹ := by field_simp
    _ ≤ |orderedEigenvalue H i - c|⁻¹ := hanti
    _ ≤ _ := hinv

/-- The auxiliary occupied-cell/large-direction implication, with the same
arbitrary nonnegative weight on both sides. -/
theorem corrected_indicator_cell_largeImage_mul_weight_le_inverseVector
    {N m : ℕ} (hN : 0 < N) (H : HermitianMatrix (Fin N))
    (a w : ℝ) (hw : 0 < w) (n : Fin m)
    (v : EuclideanSpace ℂ (Fin N)) (W : ℝ≥0∞)
    (hunit : IsUnit
      (H.1 - ((a + n * w + w / 2 : ℝ) : ℂ) •
        (1 : Matrix (Fin N) (Fin N) ℂ))) :
    Set.indicator {_u : Unit | gridCellOccupied H a w n} (fun _ => (1 : ℝ≥0∞)) () *
        Set.indicator
          {v : EuclideanSpace ℂ (Fin N) |
            ‖(H.1 - ((a + n * w + w / 2 : ℝ) : ℂ) •
                (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹‖ /
                (10 * Real.sqrt N) ≤
              ‖(WithLp.toLp 2
                ((H.1 - ((a + n * w + w / 2 : ℝ) : ℂ) •
                  (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ WithLp.ofLp v) :
                  EuclideanSpace ℂ (Fin N))‖}
          (fun _ => (1 : ℝ≥0∞)) v * W ≤
      Set.indicator
        {v : EuclideanSpace ℂ (Fin N) |
          1 / (5 * Real.sqrt N * w) ≤
            ‖(WithLp.toLp 2
              ((H.1 - ((a + n * w + w / 2 : ℝ) : ℂ) •
                (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ WithLp.ofLp v) :
                EuclideanSpace ℂ (Fin N))‖}
        (fun _ => (1 : ℝ≥0∞)) v * W := by
  let Q : Matrix (Fin N) (Fin N) ℂ :=
    (H.1 - ((a + n * w + w / 2 : ℝ) : ℂ) •
      (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹
  change
    Set.indicator {_u : Unit | gridCellOccupied H a w n}
        (fun _ => (1 : ℝ≥0∞)) () *
      Set.indicator
        {v : EuclideanSpace ℂ (Fin N) |
          ‖Q‖ / (10 * Real.sqrt N) ≤
            ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp v) :
              EuclideanSpace ℂ (Fin N))‖}
        (fun _ => (1 : ℝ≥0∞)) v * W ≤
      Set.indicator
        {v : EuclideanSpace ℂ (Fin N) |
          1 / (5 * Real.sqrt N * w) ≤
            ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp v) :
              EuclideanSpace ℂ (Fin N))‖}
        (fun _ => (1 : ℝ≥0∞)) v * W
  by_cases hocc : gridCellOccupied H a w n
  · by_cases hlarge : ‖Q‖ / (10 * Real.sqrt N) ≤
        ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp v) :
          EuclideanSpace ℂ (Fin N))‖
    · have hsqrt : 0 < Real.sqrt (N : ℝ) :=
        Real.sqrt_pos.2 (by exact_mod_cast hN)
      have hop := corrected_two_div_width_le_l2_opNorm_of_gridCellOccupied
        H a w hw n hocc hunit
      have hvec : 1 / (5 * Real.sqrt N * w) ≤
          ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp v) :
            EuclideanSpace ℂ (Fin N))‖ := by
        calc
          1 / (5 * Real.sqrt N * w) = (2 / w) / (10 * Real.sqrt N) := by
            field_simp [ne_of_gt hw, ne_of_gt hsqrt]
            norm_num
          _ ≤ ‖Q‖ / (10 * Real.sqrt N) := by
            simpa only [Q] using
              (div_le_div_of_nonneg_right hop (by positivity :
                0 ≤ 10 * Real.sqrt (N : ℝ)))
          _ ≤ _ := hlarge
      have hocc' : () ∈ {_u : Unit | gridCellOccupied H a w n} := hocc
      have hlarge' : v ∈ {v : EuclideanSpace ℂ (Fin N) |
          ‖Q‖ / (10 * Real.sqrt N) ≤
            ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp v) :
              EuclideanSpace ℂ (Fin N))‖} := hlarge
      have hvec' : v ∈ {v : EuclideanSpace ℂ (Fin N) |
          1 / (5 * Real.sqrt N * w) ≤
            ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp v) :
              EuclideanSpace ℂ (Fin N))‖} := hvec
      rw [Set.indicator_of_mem hocc', Set.indicator_of_mem hlarge',
        Set.indicator_of_mem hvec']
      simp
    · simp [Set.indicator, hocc, hlarge]
  · simp [Set.indicator, hocc]

/-- Exact arithmetic normalization for the symmetric auxiliary mesh. -/
theorem corrected_card_mul_minamiCellWidth (xi : ℝ) (M : ℕ) :
    ((2 ^ M : ℕ) : ℝ) * correctedMinamiCellWidth xi M = 2 * xi := by
  simp only [correctedMinamiCellWidth, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

end PSSSNative.BlockBand.PSSS
