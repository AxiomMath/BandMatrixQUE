module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.WeightedSquaresAnalytic
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.WeightedSquaresEnvelope
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.ShiftedHolderIntegrals
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# APSSS Fourier criterion and contour estimate

The contour-shift estimate for the Fourier integral of the characteristic function of weighted
Gaussian squares (APSSS (6.12)–(6.22)): the inner Fourier contour is moved by `δ = 1/(10ν²)`,
the vertical edges vanish, and the positive regularizer is removed by dominated convergence
(`liminf_fourier_le_shifted`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

/-- APSSS's dominant-coordinate ordering (the energies `E_j²(1 + b_j²)` are antitone) and
the three-case choice `r ∈ {0, 1, 2}` of the number of exceptional coordinates, in zero-based
indexing. -/
def DominantSelection {n : ℕ} (E b : Fin n → ℝ) (r : ℕ) : Prop :=
  Antitone (fun j : Fin n => E j ^ 2 * (1 + b j ^ 2)) ∧
    r =
      (if (∑ j : Fin n,
          if (j : ℕ) = 0 then E j ^ 2 * (1 + b j ^ 2) else 0) ≤
          (∑ j : Fin n,
            if 0 < (j : ℕ) then E j ^ 2 * (1 + b j ^ 2) else 0) / 10
        then 0
        else if (∑ j : Fin n,
          if (j : ℕ) = 1 then E j ^ 2 * (1 + b j ^ 2) else 0) ≤
          (∑ j : Fin n,
            if 1 < (j : ℕ) then E j ^ 2 * (1 + b j ^ 2) else 0) / 10
        then 1 else 2)

/-- The APSSS contour displacement `δ = 1/(10ν²)`, where `ν²` is the
coefficient energy after the dominant coordinates. -/
noncomputable def selectionDelta {n : ℕ} (E b : Fin n → ℝ) (r : ℕ) : ℝ :=
  1 / (10 * ∑ j : Fin n,
    if r ≤ (j : ℕ) then E j ^ 2 * (1 + b j ^ 2) else 0)

/-- Three nonzero coefficients cannot all occur before one of the indices
`r = 0,1,2`; hence at least one coefficient remains in the tail. -/
theorem exists_nonzero_tail_coordinate {n : ℕ} (E : Fin n → ℝ) (r : ℕ)
    (hr : r ≤ 2)
    (hthree : 3 ≤ (Finset.univ.filter fun j : Fin n => E j ≠ 0).card) :
    ∃ j : Fin n, r ≤ (j : ℕ) ∧ E j ≠ 0 := by
  let S := Finset.univ.filter fun j : Fin n => E j ≠ 0
  change 3 ≤ S.card at hthree
  by_contra hex
  have hall : ∀ j : Fin n, E j ≠ 0 → (j : ℕ) < r := by
    intro j hj
    exact Nat.lt_of_not_ge fun hjr => hex ⟨j, hjr, hj⟩
  have hcard : S.card ≤ (Finset.range r).card := by
    apply Finset.card_le_card_of_injOn (fun j : Fin n => (j : ℕ))
    · intro j hj
      change (j : ℕ) ∈ Finset.range r
      rw [Finset.mem_range]
      exact hall j (by simpa [S] using hj)
    · intro i hi j hj hij
      exact Fin.ext hij
  simp only [Finset.card_range] at hcard
  omega

/-- If `r ≤ 2` and at least three coefficients `E j` are nonzero, the tail energy
`Σ_{j ≥ r} E_j²(1 + b_j²)` is strictly positive. -/
theorem selectionTailEnergy_pos {n : ℕ} (E b : Fin n → ℝ) (r : ℕ)
    (hr : r ≤ 2)
    (hthree : 3 ≤ (Finset.univ.filter fun j : Fin n => E j ≠ 0).card) :
    0 < ∑ j : Fin n,
      if r ≤ (j : ℕ) then E j ^ 2 * (1 + b j ^ 2) else 0 := by
  apply Finset.sum_pos'
  · intro j _
    split_ifs <;> positivity
  · obtain ⟨j, hjr, hjE⟩ := exists_nonzero_tail_coordinate E r hr hthree
    refine ⟨j, Finset.mem_univ _, ?_⟩
    rw [ite_eq_left hjr]
    positivity

/-- Under the same hypotheses the contour displacement `selectionDelta E b r` is positive. -/
theorem selectionDelta_pos {n : ℕ} (E b : Fin n → ℝ) (r : ℕ)
    (hr : r ≤ 2)
    (hthree : 3 ≤ (Finset.univ.filter fun j : Fin n => E j ≠ 0).card) :
    0 < selectionDelta E b r := by
  unfold selectionDelta
  have := selectionTailEnergy_pos E b r hr hthree
  positivity

/-- The displacement `δ = selectionDelta E b r` stays inside every Gaussian continuation
half-plane of a tail coordinate: `2 δ E_j² < 1` for `j ≥ r`. -/
theorem selectionDelta_coefficient_lt {n : ℕ} (E b : Fin n → ℝ) (r : ℕ)
    (hr : r ≤ 2)
    (hthree : 3 ≤ (Finset.univ.filter fun j : Fin n => E j ≠ 0).card)
    (j : Fin n) (hjr : r ≤ (j : ℕ)) :
    2 * selectionDelta E b r * E j ^ 2 < 1 := by
  let ν2 : ℝ := ∑ k : Fin n,
    if r ≤ (k : ℕ) then E k ^ 2 * (1 + b k ^ 2) else 0
  have hν : 0 < ν2 := by
    exact selectionTailEnergy_pos E b r hr hthree
  have hterm : E j ^ 2 * (1 + b j ^ 2) ≤ ν2 := by
    dsimp [ν2]
    have h := Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun k : Fin n =>
        if r ≤ (k : ℕ) then E k ^ 2 * (1 + b k ^ 2) else 0)
      (fun k _ => by split_ifs <;> positivity) (Finset.mem_univ j)
    simpa [hjr] using h
  have hE : E j ^ 2 ≤ E j ^ 2 * (1 + b j ^ 2) := by
    nlinarith [sq_nonneg (E j), sq_nonneg (b j)]
  rw [selectionDelta]
  change 2 * (1 / (10 * ν2)) * E j ^ 2 < 1
  rw [one_div, ← div_eq_mul_inv, div_mul_eq_mul_div]
  apply (div_lt_iff₀ (by positivity : 0 < 10 * ν2)).2
  nlinarith

/-- The three-coordinate hypothesis in particular makes every permitted
dominant index a valid index of the ambient vector. -/
theorem dominantIndex_le_dimension {n : ℕ} (E : Fin n → ℝ) (r : ℕ)
    (hr : r ≤ 2)
    (hthree : 3 ≤ (Finset.univ.filter fun j : Fin n => E j ≠ 0).card) :
    r ≤ n := by
  have hc :
      (Finset.univ.filter fun j : Fin n => E j ≠ 0).card ≤ n := by
    calc
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = n := Finset.card_fin n
  omega

/-- Square-root normalization of the tail energy used by the product-envelope
and sharp scalar estimates. -/
theorem sqrt_selectionTailEnergy_sq {n : ℕ} (E b : Fin n → ℝ) (r : ℕ) :
    Real.sqrt (∑ j : Fin n,
      if r ≤ (j : ℕ) then E j ^ 2 * (1 + b j ^ 2) else 0) ^ 2 =
      ∑ j : Fin n,
        if r ≤ (j : ℕ) then E j ^ 2 * (1 + b j ^ 2) else 0 := by
  rw [Real.sq_sqrt]
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> positivity

/-- The principal-branch continuation of the joint characteristic function used
in APSSS (6.12)--(6.16). -/
def weightedSquaresCharFun {n : ℕ} (E b : Fin n → ℝ) (r : ℕ)
    (ξ η : ℂ) (a : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * η * (a : ℂ))) *
    ∏ j : Fin n,
      ((1 - 2 * Complex.I *
          (if (j : ℕ) < r then η * (E j : ℂ)
            else ξ * (E j : ℂ) ^ 2 + η * (E j : ℂ))) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (Complex.I *
          (if (j : ℕ) < r then η * (E j : ℂ)
            else ξ * (E j : ℂ) ^ 2 + η * (E j : ℂ)) /
          (1 - 2 * Complex.I *
            (if (j : ℕ) < r then η * (E j : ℂ)
              else ξ * (E j : ℂ) ^ 2 + η * (E j : ℂ))) * (b j : ℂ) ^ 2))

/-- The closed form `weightedSquaresCharFun` is the phase `exp(-iηa)` times the finite product
of the one-dimensional Gaussian-square transforms. -/
theorem weightedSquaresCharFun_eq_product {n : ℕ} (E b : Fin n → ℝ)
    (r : ℕ) (ξ η : ℂ) (a : ℝ) :
    weightedSquaresCharFun E b r ξ η a =
      Complex.exp (-(I * η * (a : ℂ))) *
        ∏ j, gaussianSquareTransform (weightedSquareFrequency E r ξ η j) (b j) := by
  unfold weightedSquaresCharFun gaussianSquareTransform gaussianSquareDenominator
  congr 1

/-- The finite-product envelope on the shifted contour `ξ - iδ`, `δ = selectionDelta E b r`:
at most `e` times the product of `dominantDecayFactor` over the dominant coordinates and
`tailDecayFactor` over the tail coordinates. -/
theorem norm_weightedSquaresCharFun_selection_le {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (hr : r ≤ 2)
    (hthree : 3 ≤ (Finset.univ.filter fun j : Fin n => E j ≠ 0).card)
    (ξ η a : ℝ) :
    ‖weightedSquaresCharFun E b r
      ((ξ : ℂ) - selectionDelta E b r * I) (η : ℂ) a‖ ≤
      Real.exp 1 * ∏ j : Fin n, if (j : ℕ) < r then
        dominantDecayFactor (E j) (b j) η
      else tailDecayFactor (E j) (b j) ξ η := by
  let ν : ℝ := Real.sqrt (∑ j : Fin n,
    if r ≤ (j : ℕ) then E j ^ 2 * (1 + b j ^ 2) else 0)
  have hνpos : 0 < ν := by
    dsimp [ν]
    exact Real.sqrt_pos.2 (selectionTailEnergy_pos E b r hr hthree)
  have hνsq : ν ^ 2 = ∑ j : Fin n,
      if r ≤ (j : ℕ) then E j ^ 2 * (1 + b j ^ 2) else 0 := by
    exact sqrt_selectionTailEnergy_sq E b r
  have hδ : selectionDelta E b r = 1 / (10 * ν ^ 2) := by
    unfold selectionDelta
    rw [hνsq]
  rw [weightedSquaresCharFun_eq_product, norm_mul]
  have hphase :
      ‖Complex.exp (-(I * (η : ℂ) * (a : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  rw [hphase, one_mul]
  have henv := charfun_weightedSquares_envelope E b r
    (dominantIndex_le_dimension E r hr hthree) ν (selectionDelta E b r)
    hνsq hνpos hδ ξ η
  rw [show (∏ j : Fin n, gaussianSquareTransform
      (weightedSquareFrequency E r
        ((ξ : ℂ) - selectionDelta E b r * I) (η : ℂ) j) (b j)) =
      ∏ j : Fin n, if (j : ℕ) < r then
        gaussianSquareTransform ((η * E j : ℝ) : ℂ) (b j)
      else gaussianSquareTransform
        (shiftedSquareFrequency (tailAffineFrequency (E j) ξ η)
          (selectionDelta E b r * E j ^ 2)) (b j) by
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : (j : ℕ) < r
    · rw [ite_eq_left hj,
        weightedSquareFrequency_shift_eq_dominant E r ξ η
          (selectionDelta E b r) j hj]
    · rw [ite_eq_right hj,
        weightedSquareFrequency_shift_eq E r ξ η
          (selectionDelta E b r) j (Nat.le_of_not_gt hj)]]
  exact henv

/-- Pointwise holomorphy in the contour variable throughout the common
continuation half-plane. -/
theorem analyticAt_weightedSquaresCharFun {n : ℕ} (E b : Fin n → ℝ)
    (r : ℕ) (η : ℂ) (a : ℝ) {ξ : ℂ}
    (hhalf : ∀ j, 0 <
      (gaussianSquareDenominator (weightedSquareFrequency E r ξ η j)).re) :
    AnalyticAt ℂ (fun z => weightedSquaresCharFun E b r z η a) ξ := by
  rw [show (fun z => weightedSquaresCharFun E b r z η a) =
      (fun z => Complex.exp (-(I * η * (a : ℂ))) *
        ∏ j, gaussianSquareTransform (weightedSquareFrequency E r z η j) (b j)) by
    funext z
    exact weightedSquaresCharFun_eq_product E b r z η a]
  apply analyticAt_const.mul
  apply analyticAt_gaussianSquareTransform_prod
  · intro j
    unfold weightedSquareFrequency
    split_ifs <;> fun_prop
  · exact hhalf

/-- Real part of every Gaussian-square denominator as the contour variable
moves off the real axis. -/
theorem weightedSquareDenominator_re_contour {n : ℕ} (E : Fin n → ℝ)
    (r : ℕ) (ξ : ℂ) (η : ℝ) (j : Fin n) :
    (gaussianSquareDenominator
      (weightedSquareFrequency E r ξ (η : ℂ) j)).re =
      if (j : ℕ) < r then 1 else 1 + 2 * ξ.im * E j ^ 2 := by
  unfold gaussianSquareDenominator weightedSquareFrequency
  by_cases hj : (j : ℕ) < r
  · simp [hj, Complex.mul_re]
  · simp [hj, Complex.mul_re, pow_two]
    ring

/-- The coefficient condition `2δEⱼ² < 1` keeps every denominator in the open
right half-plane throughout the closed strip `-δ ≤ Im ξ ≤ 0`. -/
theorem weightedSquareDenominator_re_pos_of_mem_strip {n : ℕ}
    (E : Fin n → ℝ) (r : ℕ) {δ : ℝ}
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) → 2 * δ * E j ^ 2 < 1)
    (ξ : ℂ) (hξlo : -δ ≤ ξ.im) (η : ℝ) (j : Fin n) :
    0 < (gaussianSquareDenominator
      (weightedSquareFrequency E r ξ (η : ℂ) j)).re := by
  rw [weightedSquareDenominator_re_contour]
  by_cases hj : (j : ℕ) < r
  · simp [hj]
  · rw [ite_eq_right hj]
    have hcoef := hδE j (Nat.le_of_not_gt hj)
    have hsq : 0 ≤ E j ^ 2 := sq_nonneg _
    nlinarith

/-- If `2 δ E_j² < 1` for every tail coordinate, the characteristic continuation is
holomorphic at every `ξ` with `Im ξ ≥ -δ`. -/
theorem analyticAt_weightedSquaresCharFun_of_mem_strip {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {δ : ℝ}
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) → 2 * δ * E j ^ 2 < 1)
    (η : ℝ) (a : ℝ) (ξ : ℂ) (hξlo : -δ ≤ ξ.im) :
    AnalyticAt ℂ (fun z => weightedSquaresCharFun E b r z (η : ℂ) a) ξ := by
  apply analyticAt_weightedSquaresCharFun
  intro j
  exact weightedSquareDenominator_re_pos_of_mem_strip E r hδE ξ hξlo η j

/-- The complex contour integrand before taking the horizontal limit. -/
def weightedSquaresContourIntegrand {n : ℕ} (E b : Fin n → ℝ) (r : ℕ)
    (ε δ' : ℝ) (η : ℝ) (a : ℝ) (z : ℂ) : ℂ :=
  weightedSquaresCharFun E b r z (η : ℂ) a /
    ((((η ^ 2 * ε ^ 2 + δ' : ℝ) : ℂ) + z * I) ^
      (((3 / 2 + δ' : ℝ) : ℂ)))

/-- The APSSS contour integrand is holomorphic throughout the deformation strip
when the positive regularizer `δ'` is present. -/
theorem analyticAt_weightedSquaresContourIntegrand {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {ε δ δ' : ℝ}
    (hδ' : 0 < δ')
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) → 2 * δ * E j ^ 2 < 1)
    (η a : ℝ) (z : ℂ) (hzlo : -δ ≤ z.im) (hzhi : z.im ≤ 0) :
    AnalyticAt ℂ (weightedSquaresContourIntegrand E b r ε δ' η a) z := by
  have hchar :=
    analyticAt_weightedSquaresCharFun_of_mem_strip E b r hδE η a z hzlo
  have hbase : AnalyticAt ℂ
      (fun q : ℂ => (((η ^ 2 * ε ^ 2 + δ' : ℝ) : ℂ) + q * I)) z := by
    fun_prop
  have hre : 0 <
      ((((η ^ 2 * ε ^ 2 + δ' : ℝ) : ℂ) + z * I)).re := by
    rw [add_re, ofReal_re, mul_re]
    simp only [I_re, I_im, mul_zero, mul_one]
    have : 0 ≤ η ^ 2 * ε ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  have hslit :
      (((η ^ 2 * ε ^ 2 + δ' : ℝ) : ℂ) + z * I) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl hre)
  have hexp : AnalyticAt ℂ
      (fun _ : ℂ => (((3 / 2 + δ' : ℝ) : ℂ))) z := analyticAt_const
  have hpow : AnalyticAt ℂ
      (fun q : ℂ => (((η ^ 2 * ε ^ 2 + δ' : ℝ) : ℂ) + q * I) ^
        (((3 / 2 + δ' : ℝ) : ℂ))) z :=
    AnalyticAt.cpow hbase hexp hslit
  have hne :
      (((η ^ 2 * ε ^ 2 + δ' : ℝ) : ℂ) + z * I) ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
  unfold weightedSquaresContourIntegrand
  have hquot := hchar.div hpow (Complex.cpow_ne_zero_iff.mpr (Or.inl hne))
  rw [show
      (fun q => weightedSquaresCharFun E b r q (η : ℂ) a) /
          (fun q => (((η ^ 2 * ε ^ 2 + δ' : ℝ) : ℂ) + q * I) ^
            (((3 / 2 + δ' : ℝ) : ℂ))) =
        (fun q => weightedSquaresCharFun E b r q (η : ℂ) a /
          ((((η ^ 2 * ε ^ 2 + δ' : ℝ) : ℂ) + q * I) ^
            (((3 / 2 + δ' : ℝ) : ℂ)))) by rfl] at hquot
  exact hquot

/-- Exact finite APSSS rectangle deformation, with both vertical edges retained.
This is the specialization of Cauchy–Goursat to the characteristic
product and complex-power denominator. -/
theorem weightedSquaresContour_finite_shift {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {ε δ δ' : ℝ}
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) → 2 * δ * E j ^ 2 < 1)
    (η a R : ℝ) :
    (∫ x : ℝ in -R..R,
        weightedSquaresContourIntegrand E b r ε δ' η a (x : ℂ)) =
      (∫ x : ℝ in -R..R,
        weightedSquaresContourIntegrand E b r ε δ' η a
          ((x : ℂ) - δ * I)) +
      I * (∫ y : ℝ in -δ..0,
        weightedSquaresContourIntegrand E b r ε δ' η a
          ((R : ℂ) + y * I)) -
      I * (∫ y : ℝ in -δ..0,
        weightedSquaresContourIntegrand E b r ε δ' η a
          ((-R : ℂ) + y * I)) := by
  apply integral_real_segment_eq_shifted_add_vertical
  intro z hz
  have hzlo : -δ ≤ z.im := by
    simpa [hδ.le] using hz.2.1
  have hzhi : z.im ≤ 0 := by
    simpa [hδ.le] using hz.2.2
  exact (analyticAt_weightedSquaresContourIntegrand E b r hδ' hδE
    η a z hzlo hzhi).differentiableAt.differentiableWithinAt

/-- Uniform positive lower bound for the `j`th Gaussian denominator throughout
the closed contour strip. -/
def stripCoordinateLower {n : ℕ} (E : Fin n → ℝ) (r : ℕ)
    (δ : ℝ) (j : Fin n) : ℝ :=
  if (j : ℕ) < r then 1 else 1 - 2 * δ * E j ^ 2

/-- Explicit finite bound for the characteristic numerator on the whole strip. -/
def stripNumeratorBound {n : ℕ} (E b : Fin n → ℝ) (r : ℕ)
    (δ : ℝ) : ℝ :=
  ∏ j : Fin n,
    (stripCoordinateLower E r δ j) ^ (-(1 / 2 : ℝ)) *
      Real.exp ((((stripCoordinateLower E r δ j)⁻¹ + 1) / 2) * b j ^ 2)

theorem stripCoordinateLower_pos {n : ℕ} (E : Fin n → ℝ) (r : ℕ)
    {δ : ℝ}
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) → 2 * δ * E j ^ 2 < 1)
    (j : Fin n) : 0 < stripCoordinateLower E r δ j := by
  unfold stripCoordinateLower
  by_cases hj : (j : ℕ) < r
  · simp [hj]
  · rw [ite_eq_right hj]
    linarith [hδE j (Nat.le_of_not_gt hj)]

/-- The continued weighted-square characteristic numerator is uniformly bounded
on the compact vertical strip, independently of its real coordinate. -/
theorem norm_weightedSquaresCharFun_le_stripNumeratorBound {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {δ : ℝ}
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) → 2 * δ * E j ^ 2 < 1)
    (η a : ℝ) (z : ℂ) (hzlo : -δ ≤ z.im) :
    ‖weightedSquaresCharFun E b r z (η : ℂ) a‖ ≤
      stripNumeratorBound E b r δ := by
  rw [weightedSquaresCharFun_eq_product, norm_mul, norm_prod]
  have hphase :
      ‖Complex.exp (-(I * (η : ℂ) * (a : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  rw [hphase, one_mul]
  unfold stripNumeratorBound
  apply Finset.prod_le_prod₀
  · intro j _
    exact norm_nonneg _
  · intro j _
    apply norm_gaussianSquareTransform_le_of_re_ge
      (b j) (stripCoordinateLower E r δ j)
    · exact stripCoordinateLower_pos E r hδE j
    · rw [weightedSquareDenominator_re_contour]
      unfold stripCoordinateLower
      by_cases hj : (j : ℕ) < r
      · simp [hj]
      · rw [ite_eq_right hj, ite_eq_right hj]
        nlinarith [sq_nonneg (E j)]

/-- Quantitative decay of the complete contour integrand on either vertical
edge.  The characteristic numerator uses the preceding uniform strip bound,
while the complex-power denominator contributes `|R|^(-3/2-δ')`. -/
theorem norm_weightedSquaresContourIntegrand_vertical_le {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {ε δ δ' : ℝ}
    (hδ' : 0 < δ')
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) → 2 * δ * E j ^ 2 < 1)
    (η a R y : ℝ) (hR : R ≠ 0) (hylo : -δ ≤ y) :
    ‖weightedSquaresContourIntegrand E b r ε δ' η a
        ((R : ℂ) + y * I)‖ ≤
      stripNumeratorBound E b r δ *
        |R| ^ (-(3 / 2 + δ') : ℝ) := by
  let q : ℂ := ((R : ℂ) + y * I)
  let d : ℂ := ((η ^ 2 * ε ^ 2 + δ' : ℝ) : ℂ) + q * I
  have hnum :
      ‖weightedSquaresCharFun E b r q (η : ℂ) a‖ ≤
        stripNumeratorBound E b r δ := by
    apply norm_weightedSquaresCharFun_le_stripNumeratorBound E b r hδE
    simpa [q, Complex.mul_im]
  have hdim : d.im = R := by
    dsimp [d, q]
    simp [Complex.mul_im]
  have hbase : |R| ≤ ‖d‖ := by
    rw [← hdim]
    exact Complex.abs_im_le_norm d
  have hRpos : 0 < |R| := abs_pos.mpr hR
  have hpow :
      ‖d‖ ^ (-(3 / 2 + δ') : ℝ) ≤
        |R| ^ (-(3 / 2 + δ') : ℝ) := by
    apply Real.rpow_le_rpow_of_nonpos hRpos hbase
    linarith
  unfold weightedSquaresContourIntegrand
  rw [norm_div]
  change
    ‖weightedSquaresCharFun E b r q (η : ℂ) a‖ /
        ‖d ^ (((3 / 2 + δ' : ℝ) : ℂ))‖ ≤ _
  rw [Complex.norm_cpow_real]
  rw [div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg d)]
  have hBnonneg : 0 ≤ stripNumeratorBound E b r δ := by
    unfold stripNumeratorBound
    apply Finset.prod_nonneg
    intro j _
    have hc := stripCoordinateLower_pos E r hδE j
    positivity
  exact mul_le_mul hnum hpow (Real.rpow_nonneg (norm_nonneg d) _)
    hBnonneg

/-- The integral over either finite vertical edge inherits the pointwise
power decay.  This estimate is uniform in the height along the deformation
strip. -/
theorem norm_weightedSquaresContourIntegrand_vertical_integral_le {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {ε δ δ' : ℝ}
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) → 2 * δ * E j ^ 2 < 1)
    (η a R : ℝ) (hR : R ≠ 0) :
    ‖∫ y : ℝ in -δ..0,
        weightedSquaresContourIntegrand E b r ε δ' η a
          ((R : ℂ) + y * I)‖ ≤
      (stripNumeratorBound E b r δ *
        |R| ^ (-(3 / 2 + δ') : ℝ)) * δ := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun y : ℝ =>
      weightedSquaresContourIntegrand E b r ε δ' η a
        ((R : ℂ) + y * I))
    (C := stripNumeratorBound E b r δ *
      |R| ^ (-(3 / 2 + δ') : ℝ)) (a := -δ) (b := 0) (by
      intro y hy
      apply norm_weightedSquaresContourIntegrand_vertical_le
        E b r hδ' hδE η a R y hR
      have hy' : y ∈ Set.Ioc (-δ) 0 := by
        simpa [Set.uIoc, hδ.le] using hy
      exact hy'.1.le)
  simpa [abs_of_pos hδ] using hbound

/-- Each vertical edge in the APSSS rectangle disappears when its real
coordinate tends to positive infinity.  The sign parameter simultaneously
covers the right (`s = 1`) and left (`s = -1`) edges. -/
theorem tendsto_weightedSquaresContourIntegrand_vertical_integral_zero {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {ε δ δ' : ℝ}
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) → 2 * δ * E j ^ 2 < 1)
    (η a : ℝ) {s : ℝ} (hs : |s| = 1) :
    Tendsto
      (fun R : ℝ => ∫ y : ℝ in -δ..0,
        weightedSquaresContourIntegrand E b r ε δ' η a
          (((s * R : ℝ) : ℂ) + y * I))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm'
    (a := fun R : ℝ =>
      (stripNumeratorBound E b r δ *
        |s * R| ^ (-(3 / 2 + δ') : ℝ)) * δ)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    apply norm_weightedSquaresContourIntegrand_vertical_integral_le
      E b r hδ hδ' hδE η a (s * R)
    exact mul_ne_zero
      (by
        intro hs0
        rw [hs0, abs_zero] at hs
        norm_num at hs)
      (ne_of_gt hR)
  · have hp : 0 < 3 / 2 + δ' := by linarith
    have ht :
        Tendsto (fun R : ℝ => R ^ (-(3 / 2 + δ') : ℝ))
          atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop hp
    have habs :
        (fun R : ℝ => |s * R| ^ (-(3 / 2 + δ') : ℝ)) =ᶠ[atTop]
          (fun R : ℝ => R ^ (-(3 / 2 + δ') : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      rw [abs_mul, hs, one_mul, abs_of_pos hR]
    have ht' :
        Tendsto (fun R : ℝ => |s * R| ^ (-(3 / 2 + δ') : ℝ))
          atTop (𝓝 0) :=
      ht.congr' habs.symm
    simpa only [mul_zero, zero_mul] using
      (ht'.const_mul (stripNumeratorBound E b r δ)).mul_const δ

/-- After the rectangle width tends to infinity, the two horizontal truncated
integrals differ by a quantity tending to zero.  This is the `R → ∞` passage
in the APSSS contour deformation, proved directly from the finite rectangle
identity and the two vertical-edge estimates. -/
theorem tendsto_weightedSquaresContour_horizontal_difference_zero {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {ε δ δ' : ℝ}
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) → 2 * δ * E j ^ 2 < 1)
    (η a : ℝ) :
    Tendsto
      (fun R : ℝ =>
        (∫ x : ℝ in -R..R,
          weightedSquaresContourIntegrand E b r ε δ' η a (x : ℂ)) -
        (∫ x : ℝ in -R..R,
          weightedSquaresContourIntegrand E b r ε δ' η a
            ((x : ℂ) - δ * I)))
      atTop (𝓝 0) := by
  have hright :=
    tendsto_weightedSquaresContourIntegrand_vertical_integral_zero
      E b r (ε := ε) hδ hδ' hδE η a (s := 1) (by norm_num)
  have hleft :=
    tendsto_weightedSquaresContourIntegrand_vertical_integral_zero
      E b r (ε := ε) hδ hδ' hδE η a (s := -1) (by norm_num)
  have hedges :
      Tendsto
        (fun R : ℝ =>
          I * (∫ y : ℝ in -δ..0,
            weightedSquaresContourIntegrand E b r ε δ' η a
              ((R : ℂ) + y * I)) -
          I * (∫ y : ℝ in -δ..0,
            weightedSquaresContourIntegrand E b r ε δ' η a
              ((-R : ℂ) + y * I)))
        atTop (𝓝 0) := by
    have hright' :
        Tendsto
          (fun R : ℝ => ∫ y : ℝ in -δ..0,
            weightedSquaresContourIntegrand E b r ε δ' η a
              ((R : ℂ) + y * I))
          atTop (𝓝 0) := by
      simpa using hright
    have hleft' :
        Tendsto
          (fun R : ℝ => ∫ y : ℝ in -δ..0,
            weightedSquaresContourIntegrand E b r ε δ' η a
              ((-R : ℂ) + y * I))
          atTop (𝓝 0) := by
      simpa using hleft
    simpa only [mul_zero, sub_zero] using
      (hright'.const_mul I).sub (hleft'.const_mul I)
  apply hedges.congr'
  filter_upwards with R
  rw [weightedSquaresContour_finite_shift E b r hδ hδ' hδE η a R]
  ring

/-- Every positive horizontal contour displacement gives an integrable power
kernel on the whole real line. -/
theorem integrable_shiftedPowerKernel {δ p : ℝ} (hδ : 0 < δ)
    (hp : 1 / 2 < p) :
    Integrable (fun x : ℝ => (x ^ 2 + δ ^ 2) ^ (-p)) := by
  let c : ℝ := min 1 (δ ^ 2)
  have hc : 0 < c := lt_min zero_lt_one (sq_pos_of_pos hδ)
  have hbase : Integrable (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-p)) := by
    have h := integrable_rpow_neg_one_add_norm_sq (μ := volume)
      (E := ℝ) (r := 2 * p) (by
        rw [show (Module.finrank ℝ ℝ : ℝ) = 1 by norm_num]
        linarith)
    simpa [show -(2 * p) / 2 = -p by ring] using h
  apply (hbase.const_mul (c ^ (-p))).mono'
  · exact (((continuous_id.pow 2).add_const (δ ^ 2)).rpow continuous_const
      (fun x => Or.inl (ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg x)
        (sq_pos_of_pos hδ))))).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    have hc1 : c ≤ 1 := min_le_left _ _
    have hcδ : c ≤ δ ^ 2 := min_le_right _ _
    have hmul : c * (1 + ‖x‖ ^ 2) ≤ x ^ 2 + δ ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
      nlinarith [sq_nonneg x]
    rw [← Real.mul_rpow hc.le (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hmul (by linarith)

/-- On the shifted horizontal line, the positive real part of the complex
power base supplies an integrable whole-line majorant. -/
theorem norm_weightedSquaresContourIntegrand_shifted_le {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {ε δ δ' : ℝ}
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) → 2 * δ * E j ^ 2 < 1)
    (η a x : ℝ) :
    ‖weightedSquaresContourIntegrand E b r ε δ' η a
        ((x : ℂ) - δ * I)‖ ≤
      stripNumeratorBound E b r δ *
        (x ^ 2 + δ ^ 2) ^ (-(3 / 4 + δ' / 2) : ℝ) := by
  let q : ℂ := (x : ℂ) - δ * I
  let d : ℂ := ((η ^ 2 * ε ^ 2 + δ' : ℝ) : ℂ) + q * I
  have hnum :
      ‖weightedSquaresCharFun E b r q (η : ℂ) a‖ ≤
        stripNumeratorBound E b r δ := by
    apply norm_weightedSquaresCharFun_le_stripNumeratorBound E b r hδE
    simp [q, Complex.mul_im]
  have hdre : d.re = η ^ 2 * ε ^ 2 + δ' + δ := by
    dsimp [d, q]
    simp [Complex.mul_re]
  have hdim : d.im = x := by
    dsimp [d, q]
    simp [Complex.mul_im]
  have hnormsq : x ^ 2 + δ ^ 2 ≤ ‖d‖ ^ 2 := by
    rw [show ‖d‖ ^ 2 = d.re ^ 2 + d.im ^ 2 by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring, hdre, hdim]
    have hη : 0 ≤ η ^ 2 * ε ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith
  have hleft : 0 < Real.sqrt (x ^ 2 + δ ^ 2) := by positivity
  have hnorm : Real.sqrt (x ^ 2 + δ ^ 2) ≤ ‖d‖ := by
    rw [Real.sqrt_le_iff]
    exact ⟨norm_nonneg _, hnormsq⟩
  have hpow :
      ‖d‖ ^ (-(3 / 2 + δ') : ℝ) ≤
        (x ^ 2 + δ ^ 2) ^ (-(3 / 4 + δ' / 2) : ℝ) := by
    calc
      ‖d‖ ^ (-(3 / 2 + δ') : ℝ) ≤
          (Real.sqrt (x ^ 2 + δ ^ 2)) ^ (-(3 / 2 + δ') : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hleft hnorm (by linarith)
      _ = (x ^ 2 + δ ^ 2) ^ (-(3 / 4 + δ' / 2) : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        rw [← Real.rpow_mul (by positivity)]
        congr 1
        ring
  unfold weightedSquaresContourIntegrand
  rw [norm_div]
  change ‖weightedSquaresCharFun E b r q (η : ℂ) a‖ /
      ‖d ^ (((3 / 2 + δ' : ℝ) : ℂ))‖ ≤ _
  rw [Complex.norm_cpow_real, div_eq_mul_inv,
    ← Real.rpow_neg (norm_nonneg d)]
  exact mul_le_mul hnum hpow (Real.rpow_nonneg (norm_nonneg d) _)
    (by
      unfold stripNumeratorBound
      apply Finset.prod_nonneg
      intro j _
      have hj := stripCoordinateLower_pos E r hδE j
      positivity)

/-- The shifted contour integrand is Bochner-integrable on the whole real
line for every positive regularizer. -/
theorem integrable_weightedSquaresContourIntegrand_shifted {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {ε δ δ' : ℝ}
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) → 2 * δ * E j ^ 2 < 1)
    (η a : ℝ) :
    Integrable (fun x : ℝ =>
      weightedSquaresContourIntegrand E b r ε δ' η a
        ((x : ℂ) - δ * I)) := by
  have hk := integrable_shiftedPowerKernel hδ
    (p := 3 / 4 + δ' / 2) (by linarith)
  apply (hk.const_mul (stripNumeratorBound E b r δ)).mono'
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro x
    have hzlo : -δ ≤ (((x : ℂ) - δ * I)).im := by
      simp [Complex.mul_im]
    have hzhi : (((x : ℂ) - δ * I)).im ≤ 0 := by
      simp [Complex.mul_im, hδ.le]
    have hc : ContinuousAt (fun y : ℝ => (y : ℂ) - δ * I) x := by fun_prop
    have ha := (analyticAt_weightedSquaresContourIntegrand E b r (ε := ε) hδ' hδE η a
      ((x : ℂ) - δ * I) hzlo hzhi).continuousAt
    change ContinuousAt
      (weightedSquaresContourIntegrand E b r ε δ' η a ∘
        fun y : ℝ => (y : ℂ) - δ * I) x
    exact ha.comp (f := fun y : ℝ => (y : ℂ) - δ * I) hc
  · exact .of_forall fun x =>
      norm_weightedSquaresContourIntegrand_shifted_le E b r hδ hδ' hδE η a x

/-- The original horizontal contour is likewise integrable: the positive
regularizer itself separates the complex-power base from zero. -/
theorem integrable_weightedSquaresContourIntegrand_real {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {ε δ δ' : ℝ}
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) → 2 * δ * E j ^ 2 < 1)
    (η a : ℝ) :
    Integrable (fun x : ℝ =>
      weightedSquaresContourIntegrand E b r ε δ' η a (x : ℂ)) := by
  have hk := integrable_shiftedPowerKernel hδ'
    (p := 3 / 4 + δ' / 2) (by linarith)
  apply (hk.const_mul (stripNumeratorBound E b r δ)).mono'
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro x
    have hzlo : -δ ≤ ((x : ℂ)).im := by simp [hδ.le]
    have hzhi : ((x : ℂ)).im ≤ 0 := by simp
    have hc : ContinuousAt (fun y : ℝ => (y : ℂ)) x := by fun_prop
    have ha := (analyticAt_weightedSquaresContourIntegrand E b r (ε := ε)
      hδ' hδE η a (x : ℂ) hzlo hzhi).continuousAt
    change ContinuousAt
      (weightedSquaresContourIntegrand E b r ε δ' η a ∘
        fun y : ℝ => (y : ℂ)) x
    exact ha.comp (f := fun y : ℝ => (y : ℂ)) hc
  · refine .of_forall fun x => ?_
    let q : ℂ := (x : ℂ)
    let d : ℂ := ((η ^ 2 * ε ^ 2 + δ' : ℝ) : ℂ) + q * I
    have hnum : ‖weightedSquaresCharFun E b r q (η : ℂ) a‖ ≤
        stripNumeratorBound E b r δ := by
      apply norm_weightedSquaresCharFun_le_stripNumeratorBound E b r hδE
      simp [q, hδ.le]
    have hdre : d.re = η ^ 2 * ε ^ 2 + δ' := by
      dsimp [d, q]
      simp [Complex.mul_re]
    have hdim : d.im = x := by
      dsimp [d, q]
      simp [Complex.mul_im]
    have hnormsq : x ^ 2 + δ' ^ 2 ≤ ‖d‖ ^ 2 := by
      rw [show ‖d‖ ^ 2 = d.re ^ 2 + d.im ^ 2 by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring, hdre, hdim]
      have hη : 0 ≤ η ^ 2 * ε ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      nlinarith
    have hleft : 0 < Real.sqrt (x ^ 2 + δ' ^ 2) := by positivity
    have hnorm : Real.sqrt (x ^ 2 + δ' ^ 2) ≤ ‖d‖ := by
      rw [Real.sqrt_le_iff]
      exact ⟨norm_nonneg _, hnormsq⟩
    have hpow : ‖d‖ ^ (-(3 / 2 + δ') : ℝ) ≤
        (x ^ 2 + δ' ^ 2) ^ (-(3 / 4 + δ' / 2) : ℝ) := by
      calc
        ‖d‖ ^ (-(3 / 2 + δ') : ℝ) ≤
            (Real.sqrt (x ^ 2 + δ' ^ 2)) ^ (-(3 / 2 + δ') : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hleft hnorm (by linarith)
        _ = (x ^ 2 + δ' ^ 2) ^ (-(3 / 4 + δ' / 2) : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
          congr 1
          ring
    unfold weightedSquaresContourIntegrand
    rw [norm_div]
    change ‖weightedSquaresCharFun E b r q (η : ℂ) a‖ /
        ‖d ^ (((3 / 2 + δ' : ℝ) : ℂ))‖ ≤ _
    rw [Complex.norm_cpow_real, div_eq_mul_inv,
      ← Real.rpow_neg (norm_nonneg d)]
    exact mul_le_mul hnum hpow (Real.rpow_nonneg (norm_nonneg d) _)
      (by
        unfold stripNumeratorBound
        apply Finset.prod_nonneg
        intro j _
        have hj := stripCoordinateLower_pos E r hδE j
        positivity)

/-- Symmetric truncations of an integrable whole-line function converge to its
whole-line Bochner integral. -/
theorem tendsto_intervalIntegral_neg_self_atTop {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F)
    (hf : Integrable f) :
    Tendsto (fun R : ℝ => ∫ x : ℝ in -R..R, f x) atTop
      (𝓝 (∫ x : ℝ, f x)) := by
  have ht : Tendsto
      (fun R : ℝ => ∫ x : ℝ, (Set.Ioc (-R) R).indicator f x)
      atTop (𝓝 (∫ x : ℝ, f x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
    · exact .of_forall fun R =>
        hf.1.indicator measurableSet_Ioc
    · exact .of_forall fun R => .of_forall fun x => by
        by_cases hx : x ∈ Set.Ioc (-R) R
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator, hx]
    · exact hf.norm
    · exact .of_forall fun x => by
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eventually_gt_atTop |x|] with R hR
        have hxR : x ≤ R := (le_abs_self x).trans hR.le
        have hRx : -R < x := by
          have := (neg_le_abs x)
          linarith
        have hxmem : x ∈ Set.Ioc (-R) R := ⟨hRx, hxR⟩
        rw [Set.indicator_of_mem hxmem]
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  rw [intervalIntegral.integral_of_le (by linarith),
    integral_indicator measurableSet_Ioc]

/-- Passing the finite rectangle identity to the whole line gives the exact
horizontal contour shift for every positive regularizer. -/
theorem weightedSquaresContour_integral_eq_shifted {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {ε δ δ' : ℝ}
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) → 2 * δ * E j ^ 2 < 1)
    (η a : ℝ) :
    (∫ x : ℝ, weightedSquaresContourIntegrand E b r ε δ' η a (x : ℂ)) =
      ∫ x : ℝ, weightedSquaresContourIntegrand E b r ε δ' η a
        ((x : ℂ) - δ * I) := by
  have hreal := tendsto_intervalIntegral_neg_self_atTop
    (fun x : ℝ => weightedSquaresContourIntegrand E b r ε δ' η a (x : ℂ))
    (integrable_weightedSquaresContourIntegrand_real E b r hδ hδ' hδE η a)
  have hshift := tendsto_intervalIntegral_neg_self_atTop
    (fun x : ℝ => weightedSquaresContourIntegrand E b r ε δ' η a
      ((x : ℂ) - δ * I))
    (integrable_weightedSquaresContourIntegrand_shifted E b r hδ hδ' hδE η a)
  have hdiff := tendsto_weightedSquaresContour_horizontal_difference_zero
    E b r (ε := ε) hδ hδ' hδE η a
  have hlim := hreal.sub hshift
  have hzero :
      (∫ x : ℝ, weightedSquaresContourIntegrand E b r ε δ' η a (x : ℂ)) -
        (∫ x : ℝ, weightedSquaresContourIntegrand E b r ε δ' η a
          ((x : ℂ) - δ * I)) = 0 :=
    tendsto_nhds_unique hlim hdiff
  exact sub_eq_zero.mp hzero

/-- The shifted Fourier integrand after the positive regularizer has been
removed. -/
def weightedSquaresContourLimitIntegrand {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (ε δ η a x : ℝ) : ℂ :=
  weightedSquaresCharFun E b r ((x : ℂ) - δ * I) (η : ℂ) a /
    ((((η ^ 2 * ε ^ 2 : ℝ) : ℂ) +
      ((x : ℂ) - δ * I) * I) ^ ((3 / 2 : ℝ) : ℂ))

/-- Pointwise continuity of the shifted integrand at `δ' = 0`. -/
theorem tendsto_weightedSquaresContourIntegrand_shifted_zero {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (ε : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (η a x : ℝ) :
    Tendsto (fun δ' : ℝ =>
      weightedSquaresContourIntegrand E b r ε δ' η a
        ((x : ℂ) - δ * I)) (𝓝 0)
      (𝓝 (weightedSquaresContourLimitIntegrand E b r ε δ η a x)) := by
  let q : ℂ := (x : ℂ) - δ * I
  let base : ℝ → ℂ := fun t =>
    ((η ^ 2 * ε ^ 2 + t : ℝ) : ℂ) + q * I
  let exponent : ℝ → ℂ := fun t => ((3 / 2 + t : ℝ) : ℂ)
  have hbase : ContinuousAt base 0 := by
    dsimp [base]
    fun_prop
  have hexponent : ContinuousAt exponent 0 := by
    dsimp [exponent]
    fun_prop
  have hre : 0 < (base 0).re := by
    dsimp [base, q]
    simp [Complex.mul_re]
    have hη : 0 ≤ η ^ 2 * ε ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  have hslit : base 0 ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl hre)
  have hpow : Tendsto (fun t => (base t) ^ (exponent t)) (𝓝 0)
      (𝓝 ((base 0) ^ (exponent 0))) :=
    (hbase.cpow hexponent hslit).tendsto
  have hpow0 : (base 0) ^ (exponent 0) ≠ 0 := by
    apply Complex.cpow_ne_zero_iff.mpr
    left
    intro hb
    rw [hb] at hre
    simp at hre
  have hnum : Tendsto (fun _ : ℝ =>
      weightedSquaresCharFun E b r q (η : ℂ) a) (𝓝 0)
      (𝓝 (weightedSquaresCharFun E b r q (η : ℂ) a)) := tendsto_const_nhds
  have hdiv := hnum.div hpow hpow0
  unfold weightedSquaresContourIntegrand weightedSquaresContourLimitIntegrand
  dsimp [base, exponent, q] at hdiv ⊢
  convert hdiv using 1
  all_goals push_cast
  all_goals norm_num

/-- A single integrable majorant works for all sufficiently small positive
regularizers on the shifted horizontal contour. -/
theorem norm_weightedSquaresContourIntegrand_shifted_le_dominator {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {ε δ δ' : ℝ}
    (hδ : 0 < δ) (hδ' : 0 < δ') (hδ'le : δ' ≤ 1 / 2)
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) → 2 * δ * E j ^ 2 < 1)
    (η a x : ℝ) :
    ‖weightedSquaresContourIntegrand E b r ε δ' η a
        ((x : ℂ) - δ * I)‖ ≤
      stripNumeratorBound E b r δ *
        ((x ^ 2 + δ ^ 2) ^ (-(3 / 4 : ℝ)) +
          (x ^ 2 + δ ^ 2) ^ (-(1 : ℝ))) := by
  have hmain := norm_weightedSquaresContourIntegrand_shifted_le
    E b r (ε := ε) hδ hδ' hδE η a x
  apply hmain.trans
  have hpow : (x ^ 2 + δ ^ 2) ^ (-(3 / 4 + δ' / 2) : ℝ) ≤
      (x ^ 2 + δ ^ 2) ^ (-(3 / 4 : ℝ)) +
        (x ^ 2 + δ ^ 2) ^ (-(1 : ℝ)) := by
    let s : ℝ := x ^ 2 + δ ^ 2
    have hs : 0 < s := by positivity
    rcases lt_or_ge s 1 with hs1 | hs1
    · calc
        s ^ (-(3 / 4 + δ' / 2) : ℝ) ≤ s ^ (-(1 : ℝ)) := by
          rw [Real.rpow_le_rpow_left_iff_of_base_lt_one hs hs1]
          linarith
        _ ≤ s ^ (-(3 / 4 : ℝ)) + s ^ (-(1 : ℝ)) :=
          le_add_of_nonneg_left (Real.rpow_nonneg hs.le _)
    · calc
        s ^ (-(3 / 4 + δ' / 2) : ℝ) ≤ s ^ (-(3 / 4 : ℝ)) := by
          exact Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
        _ ≤ s ^ (-(3 / 4 : ℝ)) + s ^ (-(1 : ℝ)) :=
          le_add_of_nonneg_right (Real.rpow_nonneg hs.le _)
  have hB : 0 ≤ stripNumeratorBound E b r δ := by
    unfold stripNumeratorBound
    apply Finset.prod_nonneg
    intro j _
    have hj := stripCoordinateLower_pos E r hδE j
    positivity
  exact mul_le_mul_of_nonneg_left hpow hB

/-- Integrability of the uniform small-regularizer majorant. -/
theorem integrable_weightedSquaresContour_dominator {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x : ℝ => stripNumeratorBound E b r δ *
      ((x ^ 2 + δ ^ 2) ^ (-(3 / 4 : ℝ)) +
        (x ^ 2 + δ ^ 2) ^ (-(1 : ℝ)))) := by
  exact ((integrable_shiftedPowerKernel hδ (p := (3 / 4 : ℝ)) (by norm_num)).add
    (integrable_shiftedPowerKernel hδ (p := (1 : ℝ)) (by norm_num))).const_mul _

/-- Dominated convergence through the inner shifted Fourier integral. -/
theorem tendsto_integral_weightedSquaresContourIntegrand_shifted_zero {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {ε δ : ℝ}
    (hδ : 0 < δ)
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) → 2 * δ * E j ^ 2 < 1)
    (η a : ℝ) :
    Tendsto (fun δ' : ℝ => ∫ x : ℝ,
      weightedSquaresContourIntegrand E b r ε δ' η a
        ((x : ℂ) - δ * I)) (𝓝[>] 0)
      (𝓝 (∫ x : ℝ,
        weightedSquaresContourLimitIntegrand E b r ε δ η a x)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x : ℝ => stripNumeratorBound E b r δ *
      ((x ^ 2 + δ ^ 2) ^ (-(3 / 4 : ℝ)) +
        (x ^ 2 + δ ^ 2) ^ (-(1 : ℝ))))
  · filter_upwards [self_mem_nhdsWithin] with δ' hδ'
    exact (integrable_weightedSquaresContourIntegrand_shifted E b r hδ
      hδ' hδE η a).1
  · have hsmall : ∀ᶠ δ' : ℝ in 𝓝[>] 0, δ' ≤ 1 / 2 :=
      nhdsWithin_le_nhds
        (Iic_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
    filter_upwards [self_mem_nhdsWithin, hsmall] with δ' hδ' hδ'le
    exact .of_forall fun x =>
      norm_weightedSquaresContourIntegrand_shifted_le_dominator E b r
        hδ hδ' hδ'le hδE η a x
  · exact integrable_weightedSquaresContour_dominator E b r hδ
  · exact .of_forall fun x =>
      (tendsto_weightedSquaresContourIntegrand_shifted_zero
        E b r ε hδ η a x).mono_left nhdsWithin_le_nhds

/-- Exact normalization of the limiting complex-power denominator, followed by
its lower bound from the contour displacement. -/
theorem enorm_weightedSquaresContourLimitIntegrand_le {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (ε : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (η a x : ℝ) :
    ‖weightedSquaresContourLimitIntegrand E b r ε δ η a x‖ₑ ≤
      ‖weightedSquaresCharFun E b r ((x : ℂ) - δ * I) (η : ℂ) a‖ₑ /
        ENNReal.ofReal ((x ^ 2 + δ ^ 2) ^ ((3 : ℝ) / 4)) := by
  let q : ℂ := (x : ℂ) - δ * I
  let d : ℂ := (((η ^ 2 * ε ^ 2 : ℝ) : ℂ) + q * I)
  have hdre : d.re = η ^ 2 * ε ^ 2 + δ := by
    dsimp [d, q]
    simp [Complex.mul_re]
  have hdim : d.im = x := by
    dsimp [d, q]
    simp [Complex.mul_im]
  have hnormsq : x ^ 2 + δ ^ 2 ≤ ‖d‖ ^ 2 := by
    rw [show ‖d‖ ^ 2 = d.re ^ 2 + d.im ^ 2 by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring, hdre, hdim]
    have hη : 0 ≤ η ^ 2 * ε ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith
  have hs : 0 < x ^ 2 + δ ^ 2 := by positivity
  have hsqrt : Real.sqrt (x ^ 2 + δ ^ 2) ≤ ‖d‖ := by
    rw [Real.sqrt_le_iff]
    exact ⟨norm_nonneg _, hnormsq⟩
  have hden : 0 < (x ^ 2 + δ ^ 2) ^ ((3 : ℝ) / 4) :=
    Real.rpow_pos_of_pos hs _
  have hpow : ‖d‖ ^ (-(3 / 2 : ℝ)) ≤
      ((x ^ 2 + δ ^ 2) ^ ((3 : ℝ) / 4))⁻¹ := by
    calc
      ‖d‖ ^ (-(3 / 2 : ℝ)) ≤
          (Real.sqrt (x ^ 2 + δ ^ 2)) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.2 hs) hsqrt (by norm_num)
      _ = ((x ^ 2 + δ ^ 2) ^ ((3 : ℝ) / 4))⁻¹ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le, ← Real.rpow_neg hs.le]
        congr 1
        ring
  have hreal :
      ‖weightedSquaresContourLimitIntegrand E b r ε δ η a x‖ ≤
        ‖weightedSquaresCharFun E b r q (η : ℂ) a‖ /
          ((x ^ 2 + δ ^ 2) ^ ((3 : ℝ) / 4)) := by
    unfold weightedSquaresContourLimitIntegrand
    change ‖weightedSquaresCharFun E b r q (η : ℂ) a /
      d ^ ((3 / 2 : ℝ) : ℂ)‖ ≤ _
    rw [norm_div, Complex.norm_cpow_real, div_eq_mul_inv,
      ← Real.rpow_neg (norm_nonneg d)]
    exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
  have hen := ENNReal.ofReal_le_ofReal hreal
  rw [ofReal_norm, ENNReal.ofReal_div_of_pos hden,
    ofReal_norm] at hen
  simpa [q] using hen

/-- The small-regularizer dominator retaining the characteristic
numerator, needed for the outer `η` dominated-convergence step. -/
theorem norm_weightedSquaresContourIntegrand_shifted_le_numerator_dominator {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {ε δ δ' : ℝ}
    (hδ : 0 < δ) (hδ' : 0 < δ') (hδ'le : δ' ≤ 1 / 2)
    (η a x : ℝ) :
    ‖weightedSquaresContourIntegrand E b r ε δ' η a
        ((x : ℂ) - δ * I)‖ ≤
      ‖weightedSquaresCharFun E b r ((x : ℂ) - δ * I) (η : ℂ) a‖ *
        ((x ^ 2 + δ ^ 2) ^ (-(3 / 4 : ℝ)) +
          (x ^ 2 + δ ^ 2) ^ (-(1 : ℝ))) := by
  let q : ℂ := (x : ℂ) - δ * I
  let d : ℂ := ((η ^ 2 * ε ^ 2 + δ' : ℝ) : ℂ) + q * I
  have hdre : d.re = η ^ 2 * ε ^ 2 + δ' + δ := by
    dsimp [d, q]
    simp [Complex.mul_re]
  have hdim : d.im = x := by
    dsimp [d, q]
    simp [Complex.mul_im]
  have hnormsq : x ^ 2 + δ ^ 2 ≤ ‖d‖ ^ 2 := by
    rw [show ‖d‖ ^ 2 = d.re ^ 2 + d.im ^ 2 by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring, hdre, hdim]
    have hη : 0 ≤ η ^ 2 * ε ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith
  have hs : 0 < x ^ 2 + δ ^ 2 := by positivity
  have hnorm : Real.sqrt (x ^ 2 + δ ^ 2) ≤ ‖d‖ := by
    rw [Real.sqrt_le_iff]
    exact ⟨norm_nonneg _, hnormsq⟩
  have hpow : ‖d‖ ^ (-(3 / 2 + δ') : ℝ) ≤
      (x ^ 2 + δ ^ 2) ^ (-(3 / 4 + δ' / 2) : ℝ) := by
    calc
      ‖d‖ ^ (-(3 / 2 + δ') : ℝ) ≤
          (Real.sqrt (x ^ 2 + δ ^ 2)) ^ (-(3 / 2 + δ') : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.2 hs) hnorm (by linarith)
      _ = (x ^ 2 + δ ^ 2) ^ (-(3 / 4 + δ' / 2) : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le]
        congr 1
        ring
  have hexp : (x ^ 2 + δ ^ 2) ^ (-(3 / 4 + δ' / 2) : ℝ) ≤
      (x ^ 2 + δ ^ 2) ^ (-(3 / 4 : ℝ)) +
        (x ^ 2 + δ ^ 2) ^ (-(1 : ℝ)) := by
    rcases lt_or_ge (x ^ 2 + δ ^ 2) 1 with hs1 | hs1
    · calc
        (x ^ 2 + δ ^ 2) ^ (-(3 / 4 + δ' / 2) : ℝ) ≤
            (x ^ 2 + δ ^ 2) ^ (-(1 : ℝ)) := by
          rw [Real.rpow_le_rpow_left_iff_of_base_lt_one hs hs1]
          linarith
        _ ≤ _ := le_add_of_nonneg_left (Real.rpow_nonneg hs.le _)
    · calc
        (x ^ 2 + δ ^ 2) ^ (-(3 / 4 + δ' / 2) : ℝ) ≤
            (x ^ 2 + δ ^ 2) ^ (-(3 / 4 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
        _ ≤ _ := le_add_of_nonneg_right (Real.rpow_nonneg hs.le _)
  unfold weightedSquaresContourIntegrand
  rw [norm_div]
  change ‖weightedSquaresCharFun E b r q (η : ℂ) a‖ /
      ‖d ^ (((3 / 2 + δ' : ℝ) : ℂ))‖ ≤ _
  rw [Complex.norm_cpow_real, div_eq_mul_inv,
    ← Real.rpow_neg (norm_nonneg d)]
  exact mul_le_mul_of_nonneg_left (hpow.trans hexp) (norm_nonneg _)

/-- The power `-1` part of the local dominator is absorbed by the target
`-3/4` kernel because the contour displacement is positive. -/
theorem shiftedPower_one_le_delta_mul_three_quarters {δ x : ℝ}
    (hδ : 0 < δ) :
    (x ^ 2 + δ ^ 2) ^ (-(1 : ℝ)) ≤
      δ⁻¹ ^ (1 / 2 : ℝ) *
        (x ^ 2 + δ ^ 2) ^ (-(3 / 4 : ℝ)) := by
  have hs : 0 < x ^ 2 + δ ^ 2 := by positivity
  have hδsq : δ ^ 2 ≤ x ^ 2 + δ ^ 2 := by nlinarith [sq_nonneg x]
  have hquarter : (x ^ 2 + δ ^ 2) ^ (-(1 / 4 : ℝ)) ≤
      (δ ^ 2) ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hδ) hδsq (by norm_num)
  rw [show (-(1 : ℝ)) = -(1 / 4 : ℝ) + -(3 / 4 : ℝ) by ring,
    Real.rpow_add hs]
  have heq : (δ ^ 2) ^ (-(1 / 4 : ℝ)) = δ⁻¹ ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le,
      Real.inv_rpow hδ.le, ← Real.rpow_neg hδ.le]
    congr 1
    ring
  exact mul_le_mul_of_nonneg_right (hquarter.trans_eq heq)
    (Real.rpow_nonneg hs.le _)

/-- The nonnegative target density in the outer Fourier variable. -/
def shiftedFourierMajorant {n : ℕ} (E b : Fin n → ℝ) (r : ℕ)
    (δ η a : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ,
    ‖weightedSquaresCharFun E b r ((x : ℂ) - δ * I) (η : ℂ) a‖ₑ /
      ENNReal.ofReal ((x ^ 2 + δ ^ 2) ^ ((3 : ℝ) / 4))

/-- The norm of the regularized inner integral is dominated, uniformly near
zero, by a fixed multiple of the target density. -/
theorem enorm_integral_weightedSquaresContourIntegrand_shifted_le {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {ε δ δ' : ℝ}
    (hδ : 0 < δ) (hδ' : 0 < δ') (hδ'le : δ' ≤ 1 / 2)
    (η a : ℝ) :
    ‖∫ x : ℝ, weightedSquaresContourIntegrand E b r ε δ' η a
        ((x : ℂ) - δ * I)‖ₑ ≤
      ENNReal.ofReal (1 + δ⁻¹ ^ (1 / 2 : ℝ)) *
        shiftedFourierMajorant E b r δ η a := by
  apply (enorm_integral_le_lintegral_enorm _).trans
  rw [shiftedFourierMajorant, ← lintegral_const_mul' _ _ (by finiteness)]
  apply lintegral_mono
  intro x
  have hs : 0 < x ^ 2 + δ ^ 2 := by positivity
  have hden : 0 < (x ^ 2 + δ ^ 2) ^ ((3 : ℝ) / 4) :=
    Real.rpow_pos_of_pos hs _
  have h0 := norm_weightedSquaresContourIntegrand_shifted_le_numerator_dominator
    E b r (ε := ε) hδ hδ' hδ'le η a x
  have h1 := shiftedPower_one_le_delta_mul_three_quarters (x := x) hδ
  have hreal :
      ‖weightedSquaresContourIntegrand E b r ε δ' η a
          ((x : ℂ) - δ * I)‖ ≤
        (1 + δ⁻¹ ^ (1 / 2 : ℝ)) *
          (‖weightedSquaresCharFun E b r ((x : ℂ) - δ * I) (η : ℂ) a‖ /
            ((x ^ 2 + δ ^ 2) ^ ((3 : ℝ) / 4))) := by
    calc
      _ ≤ ‖weightedSquaresCharFun E b r ((x : ℂ) - δ * I) (η : ℂ) a‖ *
          ((x ^ 2 + δ ^ 2) ^ (-(3 / 4 : ℝ)) +
            (x ^ 2 + δ ^ 2) ^ (-(1 : ℝ))) := h0
      _ ≤ ‖weightedSquaresCharFun E b r ((x : ℂ) - δ * I) (η : ℂ) a‖ *
          ((x ^ 2 + δ ^ 2) ^ (-(3 / 4 : ℝ)) +
            δ⁻¹ ^ (1 / 2 : ℝ) *
              (x ^ 2 + δ ^ 2) ^ (-(3 / 4 : ℝ))) := by
        gcongr
      _ = (1 + δ⁻¹ ^ (1 / 2 : ℝ)) *
          (‖weightedSquaresCharFun E b r ((x : ℂ) - δ * I) (η : ℂ) a‖ /
            ((x ^ 2 + δ ^ 2) ^ ((3 : ℝ) / 4))) := by
        rw [div_eq_mul_inv, Real.rpow_neg hs.le]
        ring
  have hen := ENNReal.ofReal_le_ofReal hreal
  rw [ofReal_norm, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_div_of_pos hden, ofReal_norm] at hen
  exact hen

/-- The limiting inner integral is bounded by the target density with constant
one. -/
theorem enorm_integral_weightedSquaresContourLimitIntegrand_le {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (ε : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (η a : ℝ) :
    ‖∫ x : ℝ, weightedSquaresContourLimitIntegrand E b r ε δ η a x‖ₑ ≤
      shiftedFourierMajorant E b r δ η a := by
  apply (enorm_integral_le_lintegral_enorm _).trans
  unfold shiftedFourierMajorant
  exact lintegral_mono fun x =>
    enorm_weightedSquaresContourLimitIntegrand_le E b r ε hδ η a x

/-- Measurability in the outer Fourier variable of the regularized inner
integral. -/
theorem measurable_enorm_integral_weightedSquaresContourIntegrand_shifted {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (ε δ δ' a : ℝ) :
    Measurable (fun η : ℝ =>
      ‖∫ x : ℝ, weightedSquaresContourIntegrand E b r ε δ' η a
        ((x : ℂ) - δ * I)‖ₑ) := by
  apply StronglyMeasurable.enorm
  apply StronglyMeasurable.integral_prod_right
  unfold weightedSquaresContourIntegrand weightedSquaresCharFun
  fun_prop

/-- Dominated convergence through the outer Fourier integral, conditional only
on finiteness of the sharp shifted Fourier majorant. -/
theorem tendsto_lintegral_enorm_inner_shifted_zero {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {ε δ : ℝ}
    (hδ : 0 < δ)
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) → 2 * δ * E j ^ 2 < 1)
    (a : ℝ)
    (hfin : (∫⁻ η : ℝ, shiftedFourierMajorant E b r δ η a) ≠ ∞) :
    Tendsto
      (fun δ' : ℝ => ∫⁻ η : ℝ,
        ‖∫ x : ℝ, weightedSquaresContourIntegrand E b r ε δ' η a
          ((x : ℂ) - δ * I)‖ₑ)
      (𝓝[>] 0)
      (𝓝 (∫⁻ η : ℝ,
        ‖∫ x : ℝ,
          weightedSquaresContourLimitIntegrand E b r ε δ η a x‖ₑ)) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (1 + δ⁻¹ ^ (1 / 2 : ℝ))
  apply tendsto_lintegral_filter_of_dominated_convergence
    (fun η : ℝ => C * shiftedFourierMajorant E b r δ η a)
  · exact .of_forall fun δ' =>
      measurable_enorm_integral_weightedSquaresContourIntegrand_shifted
        E b r ε δ δ' a
  · have hsmall : ∀ᶠ δ' : ℝ in 𝓝[>] 0, δ' ≤ 1 / 2 :=
      nhdsWithin_le_nhds
        (Iic_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
    filter_upwards [self_mem_nhdsWithin, hsmall] with δ' hδ' hδ'le
    exact .of_forall fun η =>
      enorm_integral_weightedSquaresContourIntegrand_shifted_le
        E b r hδ hδ' hδ'le η a
  · rw [lintegral_const_mul' _ _ (by simp [C])]
    exact ENNReal.mul_ne_top (by simp [C]) hfin
  · exact .of_forall fun η =>
      continuous_enorm.continuousAt.tendsto.comp
        (tendsto_integral_weightedSquaresContourIntegrand_shifted_zero
          E b r hδ hδE η a)

/-- The same outer dominated-convergence statement on the original horizontal
line, using the exact positive-regularizer contour shift. -/
theorem tendsto_lintegral_enorm_inner_real_zero {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) {ε δ : ℝ}
    (hδ : 0 < δ)
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) → 2 * δ * E j ^ 2 < 1)
    (a : ℝ)
    (hfin : (∫⁻ η : ℝ, shiftedFourierMajorant E b r δ η a) ≠ ∞) :
    Tendsto
      (fun δ' : ℝ => ∫⁻ η : ℝ,
        ‖∫ x : ℝ,
          weightedSquaresContourIntegrand E b r ε δ' η a (x : ℂ)‖ₑ)
      (𝓝[>] 0)
      (𝓝 (∫⁻ η : ℝ,
        ‖∫ x : ℝ,
          weightedSquaresContourLimitIntegrand E b r ε δ η a x‖ₑ)) := by
  apply (tendsto_lintegral_enorm_inner_shifted_zero
    E b r hδ hδE a hfin).congr'
  filter_upwards [self_mem_nhdsWithin] with δ' hδ'
  apply lintegral_congr
  intro η
  rw [weightedSquaresContour_integral_eq_shifted
    E b r hδ hδ' hδE η a]

/-- APSSS (6.18)--(6.22), with the positive denominator regularizer removed
after shifting the inner Fourier contour.  The `r ≤ 2` and three-coordinate
hypotheses record the sharp APSSS regime; the limiting argument itself also
covers the case in which the displayed nonnegative majorant is infinite. -/
theorem liminf_fourier_le_shifted {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (hr : r ≤ 2)
    (hthree : 3 ≤ (Finset.univ.filter fun j : Fin n => E j ≠ 0).card)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hδE : ∀ j : Fin n, r ≤ (j : ℕ) →
      2 * δ * E j ^ 2 < 1)
    (a : ℝ) :
    Filter.liminf
      (fun δ' : ℝ => ∫⁻ η : ℝ,
        ‖∫ ξ : ℝ,
          weightedSquaresCharFun E b r ξ (η : ℂ) a /
            ((((η ^ 2 * ε ^ 2 + δ' : ℝ) : ℂ) +
              (ξ : ℂ) * Complex.I) ^
              (((3 / 2 + δ' : ℝ)) : ℂ))‖ₑ)
      (nhdsWithin 0 (Set.Ioi 0))
      ≤
    ∫⁻ η : ℝ, ∫⁻ ξ : ℝ,
      ‖weightedSquaresCharFun E b r
        ((ξ : ℂ) - δ * Complex.I) (η : ℂ) a‖ₑ /
      ENNReal.ofReal
        ((ξ ^ 2 + δ ^ 2) ^ ((3 : ℝ) / 4)) := by
  have _hr := hr
  have _hthree := hthree
  have _hε := hε
  change Filter.liminf
      (fun δ' : ℝ => ∫⁻ η : ℝ,
        ‖∫ ξ : ℝ,
          weightedSquaresContourIntegrand E b r ε δ' η a (ξ : ℂ)‖ₑ)
      (𝓝[>] 0) ≤
    ∫⁻ η : ℝ, shiftedFourierMajorant E b r δ η a
  by_cases hfin :
      (∫⁻ η : ℝ, shiftedFourierMajorant E b r δ η a) = ∞
  · rw [hfin]
    exact le_top
  · rw [(tendsto_lintegral_enorm_inner_real_zero
      E b r hδ hδE a hfin).liminf_eq]
    exact lintegral_mono fun η =>
      enorm_integral_weightedSquaresContourLimitIntegrand_le
        E b r ε hδ η a

end PSSSNative.BlockBand.PSSS
