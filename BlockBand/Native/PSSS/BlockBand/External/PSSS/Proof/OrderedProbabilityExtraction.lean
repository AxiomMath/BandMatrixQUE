module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.OrderedFourierTail
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.RatioTailFourier
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.QuadraticRatioDominant

/-!
# Ordered probability extraction for diagonal Gaussian quadratic ratios

This module turns the ordered Fourier estimate of APSSS
(Aizenman–Peled–Schenker–Shamis–Sodin) into a probability bound
for the product-Gaussian weighted-square law.  It keeps the low-active-
coordinate cases separate: Fourier inversion is used only when at least three
coefficients are active, where the selected tail energy is almost surely
positive.  The remaining spectral/orthogonal transport from a general
symmetric quadratic form is not part of this module.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

/-- The absolute constant delivered by Fourier extraction for the ordered
selected tail.  The second factor is exactly the contour/Hölder constant. -/
def orderedTailProbabilityConstant : ℝ≥0∞ :=
  ENNReal.ofReal (3 * Real.exp (1 / 4) / (4 * Real.pi)) *
    (ENNReal.ofReal (Real.exp 1) * shiftedIntegralAbsoluteConstant)

/-- The final diagonal constant: the deterministic two-coordinate part plus
the ordered Fourier tail. -/
def orderedQuadraticRatioProbabilityConstant : ℝ≥0∞ :=
  ENNReal.ofReal 24 + orderedTailProbabilityConstant

/-- A nonzero coefficient in the selected tail makes its random square energy
strictly positive almost surely under the product standard-Gaussian law. -/
theorem ae_tailQuadraticRatioEnergy_pos_of_exists {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (j : Fin n)
    (hjr : r ≤ (j : ℕ)) (hEj : E j ≠ 0) :
    ∀ᵐ g ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1),
      0 < tailQuadraticRatioEnergy E b r g := by
  let _ : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
  filter_upwards [Measure.ae_eval_ne
    (fun _ : Fin n => gaussianReal 0 1) j (-b j)] with g hg
  unfold tailQuadraticRatioEnergy
  have hterm : 0 < E j ^ 2 * (g j + b j) ^ 2 := by
    have hgj : g j + b j ≠ 0 := by
      exact fun hz => hg ((add_eq_zero_iff_eq_neg).mp hz)
    exact mul_pos (sq_pos_of_ne_zero hEj) (sq_pos_of_ne_zero hgj)
  have hmem : j ∈ Finset.univ.filter (fun k : Fin n => r ≤ (k : ℕ)) := by
    simp [hjr]
  have hle : E j ^ 2 * (g j + b j) ^ 2 ≤
      ∑ k : Fin n, if r ≤ (k : ℕ) then E k ^ 2 * (g k + b k) ^ 2 else 0 := by
    rw [← Finset.sum_filter]
    apply Finset.single_le_sum
      (f := fun k : Fin n => E k ^ 2 * (g k + b k) ^ 2)
      (s := Finset.univ.filter (fun k : Fin n => r ≤ (k : ℕ)))
    · intro k _
      exact mul_nonneg (sq_nonneg (E k)) (sq_nonneg (g k + b k))
    · exact hmem
  exact hterm.trans_le hle

/-- In the three-active-coordinate regime, the canonical rank-`≤2` selection
has a nonzero coefficient left in its tail. -/
theorem exists_nonzero_canonical_tail {n : ℕ} (E b : Fin n → ℝ)
    (hthree : 3 ≤ (Finset.univ.filter fun j : Fin n => E j ≠ 0).card) :
    ∃ j : Fin n, dominantSplitRank E b ≤ (j : ℕ) ∧ E j ≠ 0 := by
  by_contra h
  push Not at h
  have hsub : Finset.univ.filter (fun j : Fin n => E j ≠ 0) ⊆
      Finset.univ.filter (fun j : Fin n => (j : ℕ) < dominantSplitRank E b) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact Nat.lt_of_not_ge fun hge => hj (h j hge)
  have hc := Finset.card_le_card hsub
  rw [Fin.card_filter_val_lt] at hc
  have hr := dominantSplitRank_le_two E b
  omega

/-- The canonical selected tail energy is almost surely positive exactly in
the regime where the Fourier argument is invoked. -/
theorem ae_canonical_tailQuadraticRatioEnergy_pos {n : ℕ}
    (E b : Fin n → ℝ)
    (hthree : 3 ≤ (Finset.univ.filter fun j : Fin n => E j ≠ 0).card) :
    ∀ᵐ g ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1),
      0 < tailQuadraticRatioEnergy E b (dominantSplitRank E b) g := by
  obtain ⟨j, hjr, hEj⟩ := exists_nonzero_canonical_tail E b hthree
  exact ae_tailQuadraticRatioEnergy_pos_of_exists E b _ j hjr hEj

/-- Probability bound for the canonical ordered tail event in the
product-Gaussian weighted-square law.  Its constant is uniform in dimension,
shifts, coefficients, and the center `a`. -/
theorem measure_ordered_tailMultiplicativeEvent_le {n : ℕ}
    (E b : Fin n → ℝ)
    (hord : Antitone (fun j : Fin n => coefficientEnergy E b j))
    (hthree : 3 ≤ (Finset.univ.filter fun j : Fin n => E j ≠ 0).card)
    (j₀ j₁ : Fin n) (hj₀ : (j₀ : ℕ) = 0) (hj₁ : (j₁ : ℕ) = 1)
    (a t : ℝ) (ht : 1 ≤ t) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (tailMultiplicativeEvent E b (dominantSplitRank E b) a (t / 3)) ≤
    orderedTailProbabilityConstant / ENNReal.ofReal t := by
  let P := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let X := tailQuadraticRatioEnergy E b (dominantSplitRank E b)
  let Y := quadraticRatioValue E b
  have hε : 0 < 3 / t := by positivity
  have hratio := ratio_tail_le_fourier P X Y
    (by unfold X tailQuadraticRatioEnergy; fun_prop)
    (by unfold Y quadraticRatioValue; fun_prop)
    (ae_canonical_tailQuadraticRatioEnergy_pos E b hthree) hε a
  have hevent : tailMultiplicativeEvent E b (dominantSplitRank E b) a (t / 3) =
      {g | |Y g - a| ≤ (3 / t) * Real.sqrt (X g)} := by
    ext g
    unfold tailMultiplicativeEvent X Y
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h
    · calc
        |quadraticRatioValue E b g - a| ≤
            Real.sqrt (tailQuadraticRatioEnergy E b
              (dominantSplitRank E b) g) / (t / 3) :=
          (le_div_iff₀ (by positivity : 0 < t / 3)).2 (by
            simpa [mul_comm] using h)
        _ = (3 / t) * Real.sqrt (tailQuadraticRatioEnergy E b
              (dominantSplitRank E b) g) := by field_simp
    · have h' : |quadraticRatioValue E b g - a| ≤
          Real.sqrt (tailQuadraticRatioEnergy E b
            (dominantSplitRank E b) g) / (t / 3) := by
        convert h using 1; field_simp
      have hh := (le_div_iff₀ (by positivity : 0 < t / 3)).1 h'
      simpa [mul_comm] using hh
  rw [hevent]
  refine hratio.trans ?_
  have hlim := ordered_liminf_fourier_le_absolute E b hord hthree
    j₀ j₁ hj₀ hj₁ hε a
  calc
    ENNReal.ofReal (Real.exp (1 / 4) * (3 / t) / (4 * Real.pi)) *
        Filter.liminf (fun δ : ℝ => ∫⁻ η : ℝ,
          ‖∫ ξ : ℝ,
            (∫ g, Complex.exp (Complex.I *
              ((ξ : ℂ) * X g + (η : ℂ) * Y g)) ∂P) /
              (((η ^ 2 * (3 / t) ^ 2 + δ : ℝ) : ℂ) +
                (ξ : ℂ) * Complex.I) ^ (((3 / 2 + δ : ℝ)) : ℂ)‖ₑ)
          (nhdsWithin 0 (Set.Ioi 0))
      = ENNReal.ofReal (Real.exp (1 / 4) * (3 / t) / (4 * Real.pi)) *
        Filter.liminf (fun δ : ℝ => ∫⁻ η : ℝ,
          ‖∫ ξ : ℝ,
            weightedSquaresCharFun E b (dominantSplitRank E b)
              (ξ : ℂ) (η : ℂ) a /
              (((η ^ 2 * (3 / t) ^ 2 + δ : ℝ) : ℂ) +
                (ξ : ℂ) * Complex.I) ^ (((3 / 2 + δ : ℝ)) : ℂ)‖ₑ)
          (nhdsWithin 0 (Set.Ioi 0)) := by
          congr 2
          funext δ
          congr 1
          funext η
          have hphase : ‖Complex.exp
              (-(Complex.I * (η : ℂ) * (a : ℂ)))‖ₑ = 1 := by
            rw [← ofReal_norm]
            simp [Complex.norm_exp, Complex.mul_re]
          have hint : (∫ ξ : ℝ,
                weightedSquaresCharFun E b (dominantSplitRank E b)
                  (ξ : ℂ) (η : ℂ) a /
                  (((η ^ 2 * (3 / t) ^ 2 + δ : ℝ) : ℂ) +
                    (ξ : ℂ) * Complex.I) ^ (((3 / 2 + δ : ℝ)) : ℂ)) =
              Complex.exp (-(Complex.I * (η : ℂ) * (a : ℂ))) *
                ∫ ξ : ℝ,
                  quadraticRatioCharacteristic E b (dominantSplitRank E b) ξ η /
                    (((η ^ 2 * (3 / t) ^ 2 + δ : ℝ) : ℂ) +
                      (ξ : ℂ) * Complex.I) ^ (((3 / 2 + δ : ℝ)) : ℂ) := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with ξ
            rw [weightedSquaresCharFun_eq_phase_mul_quadraticRatioCharacteristic]
            ring
          rw [hint, enorm_mul, hphase, one_mul]
          rfl
    _ ≤ ENNReal.ofReal (Real.exp (1 / 4) * (3 / t) / (4 * Real.pi)) *
        (ENNReal.ofReal (Real.exp 1) * shiftedIntegralAbsoluteConstant) := by
          gcongr
    _ = orderedTailProbabilityConstant / ENNReal.ofReal t := by
      unfold orderedTailProbabilityConstant
      have hcoef : ENNReal.ofReal
          (Real.exp (1 / 4) * (3 / t) / (4 * Real.pi)) =
          ENNReal.ofReal (3 * Real.exp (1 / 4) / (4 * Real.pi)) /
            ENNReal.ofReal t := by
        rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < t)]
        congr 1
        field_simp
      rw [hcoef]
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Under decreasing coefficient energies, every active coefficient occurs
strictly before the cardinality of the active support. -/
theorem active_index_lt_card_of_ordered {n : ℕ} (E b : Fin n → ℝ)
    (hord : Antitone (fun j : Fin n => coefficientEnergy E b j))
    (j : Fin n) (hEj : E j ≠ 0) :
    (j : ℕ) < (Finset.univ.filter fun k : Fin n => E k ≠ 0).card := by
  let A := Finset.univ.filter fun k : Fin n => E k ≠ 0
  let I := Finset.univ.filter fun k : Fin n => (k : ℕ) < (j : ℕ) + 1
  have hsub : I ⊆ A := by
    intro i hi
    simp only [I, A, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hij : i ≤ j := by exact Fin.mk_le_mk.mpr (by omega)
    have hjpos : 0 < coefficientEnergy E b j := by
      unfold coefficientEnergy
      exact mul_pos (sq_pos_of_ne_zero hEj) (by positivity)
    have hipos := hjpos.trans_le (hord hij)
    intro hEi
    simp [coefficientEnergy, hEi] at hipos
  have hc := Finset.card_le_card hsub
  have hI : I.card = (j : ℕ) + 1 := by
    simpa [I, Nat.min_eq_right (Nat.succ_le_iff.mpr j.isLt)] using
      (Fin.card_filter_val_lt (n := n) (m := (j : ℕ) + 1))
  rw [hI] at hc
  exact Nat.lt_of_succ_le hc

/-- Ordered activity has no holes: the active coefficients are exactly the
initial segment whose length is their cardinality. -/
theorem ordered_active_support_eq_initial {n : ℕ} (E b : Fin n → ℝ)
    (hord : Antitone (fun j : Fin n => coefficientEnergy E b j)) :
    (Finset.univ.filter fun j : Fin n => E j ≠ 0) =
      Finset.univ.filter (fun j : Fin n =>
        (j : ℕ) < (Finset.univ.filter fun k : Fin n => E k ≠ 0).card) := by
  let A := Finset.univ.filter fun j : Fin n => E j ≠ 0
  let I := Finset.univ.filter fun j : Fin n => (j : ℕ) < A.card
  have hsub : A ⊆ I := by
    intro j hj
    simp only [A, I, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact active_index_lt_card_of_ordered E b hord j hj
  have hcardI : I.card = A.card := by
    have hle : A.card ≤ n := by simpa using Finset.card_le_univ A
    simp [I, Fin.card_filter_val_lt, Nat.min_eq_right hle]
  have hcard : I.card ≤ A.card := hcardI.le
  exact Finset.eq_of_subset_of_card_le hsub hcard

/-- In the one- or two-active-coordinate regime the canonical support
truncation at its cardinality has identically zero tail energy. -/
theorem tailQuadraticRatioEnergy_activeCard_eq_zero {n : ℕ}
    (E b g : Fin n → ℝ)
    (hord : Antitone (fun j : Fin n => coefficientEnergy E b j)) :
    tailQuadraticRatioEnergy E b
      (Finset.univ.filter fun j : Fin n => E j ≠ 0).card g = 0 := by
  have hs := ordered_active_support_eq_initial E b hord
  unfold tailQuadraticRatioEnergy
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : (Finset.univ.filter fun k : Fin n => E k ≠ 0).card ≤ (j : ℕ)
  · have hEj : E j = 0 := by
      by_contra hn
      have hm : j ∈ Finset.univ.filter (fun k : Fin n => E k ≠ 0) := by simp [hn]
      rw [hs] at hm
      exact (Nat.not_lt_of_ge hj) (by simpa using hm)
    simp [hj, hEj]
  · simp [hj]

/-- When one or two ordered coefficients are active, the Fourier tail is
unnecessary: the full event is already covered by the dominant
coordinates. -/
theorem measure_ordered_weightedSquares_lowActive_le {m : ℕ}
    (E b : Fin (m + 1) → ℝ)
    (hord : Antitone (fun j : Fin (m + 1) => coefficientEnergy E b j))
    (hpos : 0 < (Finset.univ.filter fun j : Fin (m + 1) => E j ≠ 0).card)
    (hlt : (Finset.univ.filter fun j : Fin (m + 1) => E j ≠ 0).card < 3)
    (a t : ℝ) (ht : 1 ≤ t) :
    (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
      ((weightedSquaresRandomVector E b 0 a) ⁻¹'
        multiplicativeRatioPairEvent t) ≤ ENNReal.ofReal (24 / t) := by
  let r := (Finset.univ.filter fun j : Fin (m + 1) => E j ≠ 0).card
  have hr : r ≤ 2 := by omega
  have hE : ∀ j : Fin (m + 1), (j : ℕ) < r → E j ≠ 0 := by
    intro j hj
    have hs := ordered_active_support_eq_initial E b hord
    have hm : j ∈ Finset.univ.filter (fun k : Fin (m + 1) =>
        (k : ℕ) < (Finset.univ.filter fun k : Fin (m + 1) => E k ≠ 0).card) := by
      simpa [r] using hj
    rw [← hs] at hm
    simpa using hm
  have htail : tailMultiplicativeEvent E b r a (t / 3) ⊆
      dominantCoordinatesEvent E b r a (t / 3) := by
    intro g hg
    have hzero := tailQuadraticRatioEnergy_activeCard_eq_zero E b g hord
    have hYa : quadraticRatioValue E b g - a = 0 := by
      unfold tailMultiplicativeEvent at hg
      simp only [Set.mem_ofPred_eq] at hg
      change t / 3 * |quadraticRatioValue E b g - a| ≤
        Real.sqrt (tailQuadraticRatioEnergy E b r g) at hg
      rw [show tailQuadraticRatioEnergy E b r g = 0 by simpa [r] using hzero] at hg
      simp only [Real.sqrt_zero] at hg
      have ht3 : 0 < t / 3 := by positivity
      exact abs_eq_zero.mp (by nlinarith [abs_nonneg (quadraticRatioValue E b g - a)])
    have hrpos : 0 < r := hpos
    let j₀ : Fin (m + 1) := 0
    apply Set.mem_iUnion₂.mpr
    refine ⟨j₀, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hrpos
    · unfold dominantCoordinateEvent
      simp only [Set.mem_ofPred_eq, hYa, abs_zero, mul_zero]
      positivity
  calc
    (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
        ((weightedSquaresRandomVector E b 0 a) ⁻¹'
          multiplicativeRatioPairEvent t) ≤
      (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
        (dominantCoordinatesEvent E b r a (t / 3)) := by
          apply measure_mono
          exact (weightedSquares_multiplicativeEvent_subset_dominant_union_tail
            E b r a t hr (by positivity)).trans (Set.union_subset le_rfl htail)
    _ ≤ ENNReal.ofReal (8 / (t / 3)) :=
      measure_dominantCoordinatesEvent_le E b r a (t / 3) hr hE (by positivity)
    _ = ENNReal.ofReal (24 / t) := by
      congr 1
      field_simp
      norm_num

/-- Final ordered diagonal APSSS probability estimate.  At least one active
coefficient is necessary (the all-zero form with `a = 0` has probability one
for every `t`).  The proof uses direct one-dimensional small-ball estimates
for one or two active coefficients, and the weighted-square
characteristic law plus Fourier extraction when at least three are active.
The conclusion is uniform in dimension, coefficients, shifts, and `a`. -/
theorem measure_ordered_weightedSquares_multiplicativeEvent_le {m : ℕ}
    (E b : Fin (m + 1) → ℝ)
    (hord : Antitone (fun j : Fin (m + 1) => coefficientEnergy E b j))
    (hactive : 0 < (Finset.univ.filter fun j : Fin (m + 1) => E j ≠ 0).card)
    (a t : ℝ) (ht : 1 ≤ t) :
    (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
      ((weightedSquaresRandomVector E b 0 a) ⁻¹'
        multiplicativeRatioPairEvent t) ≤
      orderedQuadraticRatioProbabilityConstant / ENNReal.ofReal t := by
  by_cases hthree : 3 ≤
      (Finset.univ.filter fun j : Fin (m + 1) => E j ≠ 0).card
  · let r := dominantSplitRank E b
    have hr : r ≤ 2 := dominantSplitRank_le_two E b
    have hE : ∀ j : Fin (m + 1), (j : ℕ) < r → E j ≠ 0 := by
      simpa [r] using dominantSplitRank_coefficient_ne_zero E b
    have hn : 2 < m + 1 := by
      have hc : (Finset.univ.filter fun j : Fin (m + 1) => E j ≠ 0).card ≤
          m + 1 := by
        simpa using (Finset.card_le_univ
          (Finset.univ.filter fun j : Fin (m + 1) => E j ≠ 0))
      omega
    let j₀ : Fin (m + 1) := ⟨0, by omega⟩
    let j₁ : Fin (m + 1) := ⟨1, by omega⟩
    have hmain := measure_weightedSquares_multiplicativeEvent_le_dominant_add_tail
      E b r a t hr hE ht
    have htail := measure_ordered_tailMultiplicativeEvent_le E b hord hthree
      j₀ j₁ rfl rfl a t ht
    calc
      (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
          ((weightedSquaresRandomVector E b 0 a) ⁻¹'
            multiplicativeRatioPairEvent t) ≤
        ENNReal.ofReal (24 / t) +
          (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
            (tailMultiplicativeEvent E b r a (t / 3)) := hmain
      _ ≤ ENNReal.ofReal 24 / ENNReal.ofReal t +
          orderedTailProbabilityConstant / ENNReal.ofReal t := by
            gcongr
            rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < t)]
      _ = orderedQuadraticRatioProbabilityConstant / ENNReal.ofReal t := by
            unfold orderedQuadraticRatioProbabilityConstant
            rw [ENNReal.add_div]
  · have hlt : (Finset.univ.filter fun j : Fin (m + 1) => E j ≠ 0).card < 3 := by
      omega
    have hlo := measure_ordered_weightedSquares_lowActive_le E b hord hactive hlt a t ht
    calc
      (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
          ((weightedSquaresRandomVector E b 0 a) ⁻¹'
            multiplicativeRatioPairEvent t) ≤ ENNReal.ofReal (24 / t) := hlo
      _ = ENNReal.ofReal 24 / ENNReal.ofReal t := by
        rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < t)]
      _ ≤ orderedQuadraticRatioProbabilityConstant / ENNReal.ofReal t := by
        unfold orderedQuadraticRatioProbabilityConstant
        gcongr
        exact le_add_right le_rfl

end PSSSNative.BlockBand.PSSS
