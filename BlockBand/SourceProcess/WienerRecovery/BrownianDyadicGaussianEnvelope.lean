module

public import BlockBand.SourceProcess.WienerRecovery.BrownianDyadicChainingClosure
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Concrete Gaussian envelope for Brownian dyadic levels

This module chooses an explicit summable modulus on every positive compact horizon
and proves that the corresponding dyadic bad-level probabilities have a geometric
envelope.  Combining this calculation with the Borel–Cantelli layer gives an
almost-sure eventual dyadic modulus without an abstract probability-bound hypothesis.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery.CEH

open scoped ENNReal NNReal Topology
open Filter MeasureTheory ProbabilityTheory

namespace BrownianDyadicGaussianEnvelope

open BrownianDyadicChainingClosure
open BrownianKolmogorovChentsovClosure
open ScalarWienerMeasureConstruction

/-- A summable dyadic modulus on `[0,T]`.  The factor `(3/4)^n` is slower than
the Brownian standard-deviation scale `2^{-n/2}`; the extra linear factor makes
the Gaussian exponent dominate a geometric series uniformly at every level. -/
def compactDyadicModulus (T : NNReal) (n : ℕ) : ℝ :=
  8 * ((T : ℝ) + 1) * (n + 1) * (3 / 4 : ℝ) ^ n

/-- The chosen compact dyadic modulus is nonnegative. -/
theorem compactDyadicModulus_nonneg (T : NNReal) (n : ℕ) :
    0 ≤ compactDyadicModulus T n := by
  unfold compactDyadicModulus
  positivity

/-- The chosen compact dyadic modulus is summable. -/
theorem summable_compactDyadicModulus (T : NNReal) :
    Summable (compactDyadicModulus T) := by
  have hr : ‖(3 / 4 : ℝ)‖ < 1 := by norm_num
  have hn : Summable (fun n : ℕ => (n : ℝ) * (3 / 4 : ℝ) ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable
  have hg : Summable (fun n : ℕ => (3 / 4 : ℝ) ^ n) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hsum := hn.add hg
  have hmul := hsum.mul_left (8 * ((T : ℝ) + 1))
  convert hmul using 1
  funext n
  simp only [compactDyadicModulus]
  ring

/-- Every edge of the level-`n` partition of `[0,T]` has length `T / 2^n`. -/
theorem nndist_dyadicLeft_dyadicRight
    (T : NNReal) (n : ℕ) (k : Fin (2 ^ n)) :
    (nndist (dyadicLeft T n k).1 (dyadicRight T n k).1 : ℝ) =
      (T : ℝ) / (2 : ℝ) ^ n := by
  rw [coe_nndist, Real.dist_eq]
  change |T.1 * (k.1 : NNReal).1 / ((2 ^ n : ℕ) : NNReal).1 -
      T.1 * (((k.1 + 1 : ℕ) : NNReal).1) / ((2 ^ n : ℕ) : NNReal).1| = _
  have hk0 : (k.1 : NNReal).1 = (k.1 : ℝ) := by norm_cast
  have hk1 : (((k.1 + 1 : ℕ) : NNReal).1) = (k.1 : ℝ) + 1 := by norm_cast
  have hp : (((2 ^ n : ℕ) : NNReal).1) = (2 : ℝ) ^ n := by norm_cast
  rw [hk0, hk1, hp]
  rw [abs_of_nonpos]
  · field_simp
    ring_nf
    rfl
  · have hp' : 0 < (2 : ℝ) ^ n := by positivity
    rw [← sub_div]
    apply div_nonpos_of_nonpos_of_nonneg
    · calc
        (T : ℝ) * (k.1 : ℝ) - (T : ℝ) * ((k.1 : ℝ) + 1) = -(T : ℝ) := by ring
        _ ≤ 0 := neg_nonpos.mpr T.coe_nonneg
    · positivity

/-- With the chosen modulus, each dyadic-edge Gaussian exponent is at most
`-(n+1)`.  The generous constant makes the estimate uniform in
the positive horizon `T`. -/
theorem dyadicGaussianExponent_le
    (T : NNReal) (hT : 0 < T) (n : ℕ) (k : Fin (2 ^ n)) :
    -(compactDyadicModulus T n) ^ 2 /
        (2 * (nndist (dyadicLeft T n k).1
          (dyadicRight T n k).1 : ℝ)) ≤ -(n + 1 : ℕ) := by
  rw [nndist_dyadicLeft_dyadicRight]
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hp : 0 < (2 : ℝ) ^ n := by positivity
  have hratio : 1 ≤ (9 / 8 : ℝ) ^ n := by
    exact one_le_pow₀ (by norm_num)
  have hpow : ((3 / 4 : ℝ) ^ n) ^ 2 * (2 : ℝ) ^ n =
      (9 / 8 : ℝ) ^ n := by
    calc
      ((3 / 4 : ℝ) ^ n) ^ 2 * (2 : ℝ) ^ n =
          ((3 / 4 : ℝ) ^ 2) ^ n * (2 : ℝ) ^ n := by
            rw [← pow_mul, ← pow_mul]
            congr 2
            omega
      _ = ((3 / 4 : ℝ) ^ 2 * 2) ^ n := by rw [mul_pow]
      _ = (9 / 8 : ℝ) ^ n := by norm_num
  have hscale :
      2 * (T : ℝ) * (n + 1 : ℕ) / (2 : ℝ) ^ n ≤
        (compactDyadicModulus T n) ^ 2 := by
    rw [div_le_iff₀ hp]
    unfold compactDyadicModulus
    push_cast
    have hTscale : (T : ℝ) ≤ ((T : ℝ) + 1) ^ 2 := by
      nlinarith [T.coe_nonneg]
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by norm_num
    calc
      2 * (T : ℝ) * (n + 1 : ℝ) ≤
          64 * ((T : ℝ) + 1) ^ 2 * (n + 1 : ℝ) := by
            gcongr
            nlinarith
      _ ≤ 64 * ((T : ℝ) + 1) ^ 2 * (n + 1 : ℝ) ^ 2 := by
            gcongr
            nlinarith
      _ ≤ 64 * ((T : ℝ) + 1) ^ 2 * (n + 1 : ℝ) ^ 2 *
          (9 / 8 : ℝ) ^ n := by
            exact le_mul_of_one_le_right (by positivity) hratio
      _ = (8 * ((T : ℝ) + 1) * (n + 1 : ℝ) *
          (3 / 4 : ℝ) ^ n) ^ 2 * (2 : ℝ) ^ n := by
            rw [← hpow]
            ring
  have hden : 0 < 2 * ((T : ℝ) / (2 : ℝ) ^ n) := by positivity
  rw [div_le_iff₀ hden]
  calc
    -(compactDyadicModulus T n) ^ 2 ≤
        -(2 * (T : ℝ) * (n + 1 : ℕ) / (2 : ℝ) ^ n) := neg_le_neg hscale
    _ = -(n + 1 : ℕ) * (2 * ((T : ℝ) / (2 : ℝ) ^ n)) := by ring

/-- The concrete geometric ratio left after summing the Gaussian estimate over
the `2^n` dyadic edges. -/
def gaussianDyadicRatio : ℝ := 2 * Real.exp (-1)

/-- The concrete dyadic ratio is positive. -/
theorem gaussianDyadicRatio_pos : 0 < gaussianDyadicRatio := by
  unfold gaussianDyadicRatio
  positivity

/-- The concrete dyadic ratio is strictly smaller than one. -/
theorem gaussianDyadicRatio_lt_one : gaussianDyadicRatio < 1 := by
  have he : (2 : ℝ) < Real.exp 1 := by
    convert Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0) using 1; norm_num
  unfold gaussianDyadicRatio
  rw [Real.exp_neg]
  exact (div_lt_one (by positivity)).2 he

/-- The explicit finite-level Gaussian union estimate is bounded by the
concrete geometric sequence `gaussianDyadicRatio^(n+1)`. -/
theorem measureReal_dyadicBadLevel_compactDyadicModulus_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (T : NNReal) (hT : 0 < T) (n : ℕ) :
    P.real (dyadicBadLevel B T (compactDyadicModulus T) n) ≤
      gaussianDyadicRatio ^ (n + 1) := by
  calc
    P.real (dyadicBadLevel B T (compactDyadicModulus T) n) ≤
        ∑ k : Fin (2 ^ n), 2 * Real.exp
          (-(compactDyadicModulus T n) ^ 2 /
            (2 * (nndist (dyadicLeft T n k).1
              (dyadicRight T n k).1 : ℝ))) :=
      measureReal_dyadicBadLevel_le hB T (compactDyadicModulus T)
        (compactDyadicModulus_nonneg T) n
    _ ≤ ∑ _k : Fin (2 ^ n), 2 * Real.exp (-(n + 1 : ℕ)) := by
      gcongr with k
      exact dyadicGaussianExponent_le T hT n k
    _ = gaussianDyadicRatio ^ (n + 1) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hexp : Real.exp (-(n + 1 : ℕ)) =
          Real.exp (-1) ^ (n + 1) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [hexp]
      unfold gaussianDyadicRatio
      push_cast
      calc
        (2 : ℝ) ^ n * (2 * Real.exp (-1) ^ (n + 1)) =
            (2 : ℝ) ^ (n + 1) * Real.exp (-1) ^ (n + 1) := by
              rw [pow_succ]
              ring
        _ = (2 * Real.exp (-1)) ^ (n + 1) := by rw [mul_pow]

/-- The same concrete ratio in `ENNReal`, for use by Borel–Cantelli. -/
def gaussianDyadicRatioENNReal : ENNReal :=
  ENNReal.ofReal gaussianDyadicRatio

/-- The `ENNReal` dyadic ratio is strictly below one. -/
theorem gaussianDyadicRatioENNReal_lt_one :
    gaussianDyadicRatioENNReal < 1 := by
  exact ENNReal.ofReal_lt_one.2 gaussianDyadicRatio_lt_one

/-- Convert the explicit real-valued Gaussian level estimate to the geometric
`ENNReal` envelope used by Borel–Cantelli. -/
theorem measure_dyadicBadLevel_compactDyadicModulus_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (T : NNReal) (hT : 0 < T) (n : ℕ) :
    P (dyadicBadLevel B T (compactDyadicModulus T) n) ≤
      gaussianDyadicRatioENNReal * gaussianDyadicRatioENNReal ^ n := by
  have hr := measureReal_dyadicBadLevel_compactDyadicModulus_le hB T hT n
  calc
    P (dyadicBadLevel B T (compactDyadicModulus T) n) =
        ENNReal.ofReal
          (P.real (dyadicBadLevel B T (compactDyadicModulus T) n)) := by
            symm
            exact ofReal_measureReal
    _ ≤ ENNReal.ofReal (gaussianDyadicRatio ^ (n + 1)) :=
      ENNReal.ofReal_le_ofReal hr
    _ = gaussianDyadicRatioENNReal * gaussianDyadicRatioENNReal ^ n := by
      rw [ENNReal.ofReal_pow gaussianDyadicRatio_pos.le]
      unfold gaussianDyadicRatioENNReal
      rw [pow_succ']

/-- For the canonical raw Brownian coordinate process, the explicit Gaussian
calculation and first Borel–Cantelli give the eventual uniform dyadic modulus
on every positive compact horizon.  No abstract level-envelope hypothesis is
left in this statement. -/
theorem ae_eventually_rawCoordinate_dyadic_modulus
    (hcont : BrownianCylinderContinuityAtEmpty)
    (T : NNReal) (hT : 0 < T) :
    ∀ᵐ ω ∂(brownianRawMeasure hcont), ∀ᶠ n in atTop,
      ∀ k : Fin (2 ^ n),
        |rawCoordinateProcess (dyadicLeft T n k) ω -
            rawCoordinateProcess (dyadicRight T n k) ω| <
          compactDyadicModulus T n := by
  let _ := isProbabilityMeasure_brownianRawMeasure hcont
  apply ae_eventually_dyadic_modulus_of_geometric_bound
    rawCoordinateProcess T (compactDyadicModulus T)
    (C := gaussianDyadicRatioENNReal) (q := gaussianDyadicRatioENNReal)
    (by simp [gaussianDyadicRatioENNReal])
    gaussianDyadicRatioENNReal_lt_one
  intro n
  exact measure_dyadicBadLevel_compactDyadicModulus_le
    (isPreBrownianReal_rawCoordinateProcess hcont) T hT n

end BrownianDyadicGaussianEnvelope

end BlockBand.SourceProcess.WienerRecovery.CEH
