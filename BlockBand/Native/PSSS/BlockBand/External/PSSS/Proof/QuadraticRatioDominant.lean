module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.SpectralTailAdapter
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Dominant-coordinate reduction for the APSSS quadratic ratio

APSSS refers to Aizenman–Peled–Schenker–Shamis–Sodin.

This module proves the uniform rank-one small-ball estimate used for the at
most two dominant coordinates, including empty and one-coordinate cases.  It
then combines those events with the ordered spectral tail event.  The final
reduction takes only the still-missing numeric Fourier-tail inequality as an
explicit premise.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal InnerProductSpace Matrix

/-- The scalar quadratic strip occurring after conditioning on every Gaussian
coordinate except one. -/
def quadraticStrip (c ε : ℝ) : Set ℝ :=
  {x | |x ^ 2 - c| ≤ ε * |x|}

/-- A quadratic strip of nonnegative width lies in two intervals, each of
radius `ε`, about the two possible square roots. -/
theorem quadraticStrip_subset_two_intervals {c ε : ℝ} (hε : 0 ≤ ε) :
    quadraticStrip c ε ⊆
      Set.Icc (Real.sqrt (max c 0) - ε) (Real.sqrt (max c 0) + ε) ∪
      Set.Icc (-Real.sqrt (max c 0) - ε) (-Real.sqrt (max c 0) + ε) := by
  intro x hx
  change |x ^ 2 - c| ≤ ε * |x| at hx
  have habs : 0 ≤ |x| := abs_nonneg x
  have hs : 0 ≤ Real.sqrt (max c 0) := Real.sqrt_nonneg _
  have hs_sq : (Real.sqrt (max c 0)) ^ 2 = max c 0 := by
    rw [Real.sq_sqrt]
    exact le_max_right _ _
  have hnear : |x| ≤ Real.sqrt (max c 0) + ε ∧
      Real.sqrt (max c 0) - ε ≤ |x| := by
    by_cases hc : 0 ≤ c
    · rw [max_eq_left hc] at hs_sq ⊢
      have hlo : -(ε * |x|) ≤ x ^ 2 - c := (neg_le_of_abs_le hx)
      have hhi : x ^ 2 - c ≤ ε * |x| := (le_of_abs_le hx)
      have hsc : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
      constructor
      · by_contra h
        have hy : Real.sqrt c + ε < |x| := lt_of_not_ge h
        have hsum : 0 < |x| + Real.sqrt c := by nlinarith
        have hprod : ε * |x| <
            (|x| - Real.sqrt c) * (|x| + Real.sqrt c) := by
          calc
            ε * |x| ≤ ε * (|x| + Real.sqrt c) := by
              exact mul_le_mul_of_nonneg_left (by linarith) hε
            _ < (|x| - Real.sqrt c) *
                (|x| + Real.sqrt c) := by
              gcongr
              linarith
        nlinarith [sq_abs x]
      · by_contra h
        have hy : |x| < Real.sqrt c - ε := lt_of_not_ge h
        have hsum : 0 < Real.sqrt c + |x| := by nlinarith
        have hprod : ε * |x| <
            (Real.sqrt c - |x|) * (Real.sqrt c + |x|) := by
          calc
            ε * |x| ≤ ε * (Real.sqrt c + |x|) := by
              exact mul_le_mul_of_nonneg_left (by linarith) hε
            _ < (Real.sqrt c - |x|) *
                (Real.sqrt c + |x|) := by
              gcongr
              linarith
        nlinarith [sq_abs x]
    · rw [max_eq_right (le_of_not_ge hc)] at hs_sq ⊢
      simp only [Real.sqrt_zero, zero_add, zero_sub]
      have hhi : x ^ 2 - c ≤ ε * |x| := le_of_abs_le hx
      constructor
      · by_contra h
        have hy : ε < |x| := lt_of_not_ge h
        have hxne : x ≠ 0 := by
          intro hx0
          subst x
          simp at hy
          linarith
        have hprod : ε * |x| < |x| ^ 2 := by
          simpa [pow_two] using
            (mul_lt_mul_of_pos_right hy (abs_pos.mpr hxne))
        nlinarith [sq_abs x]
      · linarith
  rcases le_total 0 x with hx0 | hx0
  · left
    simp only [mem_Icc]
    rw [abs_of_nonneg hx0] at hnear
    exact ⟨hnear.2, hnear.1⟩
  · right
    simp only [mem_Icc]
    rw [abs_of_nonpos hx0] at hnear
    constructor <;> linarith

/-- The Lebesgue measure of a quadratic strip is at most `4ε`. -/
theorem volume_quadraticStrip_le {c ε : ℝ} (hε : 0 ≤ ε) :
    volume (quadraticStrip c ε) ≤ ENNReal.ofReal (4 * ε) := by
  calc
    volume (quadraticStrip c ε) ≤
        volume (Set.Icc (Real.sqrt (max c 0) - ε)
          (Real.sqrt (max c 0) + ε) ∪
        Set.Icc (-Real.sqrt (max c 0) - ε)
          (-Real.sqrt (max c 0) + ε)) :=
      measure_mono (quadraticStrip_subset_two_intervals hε)
    _ ≤ volume (Set.Icc (Real.sqrt (max c 0) - ε)
          (Real.sqrt (max c 0) + ε)) +
        volume (Set.Icc (-Real.sqrt (max c 0) - ε)
          (-Real.sqrt (max c 0) + ε)) := measure_union_le _ _
    _ = ENNReal.ofReal (4 * ε) := by
      rw [Real.volume_Icc, Real.volume_Icc]
      rw [show Real.sqrt (max c 0) + ε -
          (Real.sqrt (max c 0) - ε) = 2 * ε by ring]
      rw [show -Real.sqrt (max c 0) + ε -
          (-Real.sqrt (max c 0) - ε) = 2 * ε by ring]
      rw [← ENNReal.ofReal_add
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε)]
      congr 1
      ring

/-- The standard real Gaussian density is bounded by one. -/
theorem gaussianPDFReal_zero_one_le_one (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ 1 := by
  rw [gaussianPDFReal_def]
  have hexp : Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ≥0))) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    norm_num
    nlinarith [sq_nonneg x]
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (1 : ℝ≥0)) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have hpi : 1 ≤ Real.pi :=
      le_trans (by norm_num : (1 : ℝ) ≤ 3) Real.pi_gt_three.le
    norm_num at hpi ⊢
    linarith
  calc
    (Real.sqrt (2 * Real.pi * (1 : ℝ≥0)))⁻¹ *
        Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ≥0))) ≤
      (Real.sqrt (2 * Real.pi * (1 : ℝ≥0)))⁻¹ * 1 := by
        gcongr
    _ ≤ 1 := by
      simpa using inv_le_one_of_one_le₀ hsqrt

/-- Any Borel set under a standard real Gaussian has probability at most its
Lebesgue measure. -/
theorem gaussianReal_zero_one_le_volume (s : Set ℝ) :
    gaussianReal 0 1 s ≤ volume s := by
  rw [gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0) s]
  calc
    ENNReal.ofReal (∫ x in s, gaussianPDFReal 0 1 x) ≤
        (volume.restrict s) Set.univ := by
      apply integral_le_measure
      · intro x _
        exact gaussianPDFReal_zero_one_le_one x
      · intro x hx
        simp at hx
    _ = volume s := by simp

/-- Uniform shifted scalar quadratic-strip bound.  The constant four is
absolute and independent of the shift and of the center of the quadratic
strip. -/
theorem gaussianReal_shifted_quadraticStrip_le (b c ε : ℝ) (hε : 0 ≤ ε) :
    gaussianReal 0 1 {g | g + b ∈ quadraticStrip c ε} ≤
      ENNReal.ofReal (4 * ε) := by
  let s := quadraticStrip c ε
  have hset :
      {g : ℝ | g + b ∈ quadraticStrip c ε} =
        (fun g : ℝ => b + g) ⁻¹' s := by
    ext g
    simp [s, add_comm]
  calc
    gaussianReal 0 1 {g | g + b ∈ quadraticStrip c ε} ≤
        volume {g | g + b ∈ quadraticStrip c ε} :=
      gaussianReal_zero_one_le_volume _
    _ = volume s := by
      rw [hset]
      exact measure_preimage_vadd volume b s
    _ ≤ ENNReal.ofReal (4 * ε) := volume_quadraticStrip_le hε

/-- Fubini bound used after separating one Gaussian coordinate: a uniform
bound on all one-dimensional fibers bounds the whole product event. -/
theorem prod_measure_le_of_fiber_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    [IsProbabilityMeasure ν] {s : Set (α × β)} (hs : MeasurableSet s)
    (C : ℝ≥0∞)
    (hfiber : ∀ y, μ ((fun x => (x, y)) ⁻¹' s) ≤ C) :
    μ.prod ν s ≤ C := by
  rw [Measure.prod_apply_symm hs]
  calc
    (∫⁻ y, μ ((fun x => (x, y)) ⁻¹' s) ∂ν) ≤
        ∫⁻ _y, C ∂ν := lintegral_mono hfiber
    _ = C := by simp

/-- The contribution of one nonzero diagonal coefficient, after all other
coordinates are fixed, is contained in a translated quadratic strip of width
`τ⁻¹`. -/
theorem scalar_dominant_event_subset_quadraticStrip
    {E b d a τ : ℝ} (hE : E ≠ 0) (hτ : 0 < τ) :
    {x | τ * |E * (x + b) ^ 2 + d - a| ≤ |E| * |x + b|} ⊆
      {x | x + b ∈ quadraticStrip ((a - d) / E) τ⁻¹} := by
  intro x hx
  change τ * |E * (x + b) ^ 2 + d - a| ≤ |E| * |x + b| at hx
  change |(x + b) ^ 2 - (a - d) / E| ≤ τ⁻¹ * |x + b|
  have hid :
      E * ((x + b) ^ 2 - (a - d) / E) =
        E * (x + b) ^ 2 + d - a := by
    field_simp
    ring
  rw [← hid, abs_mul] at hx
  have hEpos : 0 < |E| := abs_pos.mpr hE
  have hcancel :
      τ * |(x + b) ^ 2 - (a - d) / E| ≤ |x + b| := by
    have hx' : |E| * (τ * |(x + b) ^ 2 - (a - d) / E|) ≤
        |E| * |x + b| := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hx
    exact (mul_le_mul_iff_of_pos_left hEpos).mp hx'
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hτ).2
  simpa [mul_comm] using hcancel

/-- Scalar conditional small-ball estimate for a single nonzero diagonal
coefficient. -/
theorem gaussianReal_scalar_dominant_event_le
    {E b d a τ : ℝ} (hE : E ≠ 0) (hτ : 0 < τ) :
    gaussianReal 0 1
        {x | τ * |E * (x + b) ^ 2 + d - a| ≤ |E| * |x + b|} ≤
      ENNReal.ofReal (4 / τ) := by
  calc
    gaussianReal 0 1
        {x | τ * |E * (x + b) ^ 2 + d - a| ≤ |E| * |x + b|} ≤
      gaussianReal 0 1
        {x | x + b ∈ quadraticStrip ((a - d) / E) τ⁻¹} :=
      measure_mono (scalar_dominant_event_subset_quadraticStrip hE hτ)
    _ ≤ ENNReal.ofReal (4 * τ⁻¹) :=
      gaussianReal_shifted_quadraticStrip_le _ _ _
        (inv_nonneg.mpr hτ.le)
    _ = ENNReal.ofReal (4 / τ) := by rw [div_eq_mul_inv]

/-- Event where one diagonal coordinate alone dominates the shifted
quadratic denominator. -/
def dominantCoordinateEvent {n : ℕ} (E b : Fin n → ℝ)
    (j : Fin n) (a τ : ℝ) : Set (Fin n → ℝ) :=
  {g | τ * |quadraticRatioValue E b g - a| ≤
    |E j| * |g j + b j|}

/-- Every dominant-coordinate event is measurable. -/
theorem measurableSet_dominantCoordinateEvent {n : ℕ}
    (E b : Fin n → ℝ) (j : Fin n) (a τ : ℝ) :
    MeasurableSet (dominantCoordinateEvent E b j a τ) := by
  unfold dominantCoordinateEvent quadraticRatioValue
  measurability

/-- Uniform product-Gaussian bound for one nonzero dominant coordinate. -/
theorem measure_dominantCoordinateEvent_le {m : ℕ}
    (E b : Fin (m + 1) → ℝ) (j : Fin (m + 1)) (a τ : ℝ)
    (hE : E j ≠ 0) (hτ : 0 < τ) :
    (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
        (dominantCoordinateEvent E b j a τ) ≤
      ENNReal.ofReal (4 / τ) := by
  let e :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j
  let ν : Measure (Fin m → ℝ) :=
    Measure.pi (fun _ : Fin m => gaussianReal 0 1)
  let s : Set (ℝ × (Fin m → ℝ)) :=
    e.symm ⁻¹' dominantCoordinateEvent E b j a τ
  have hs : MeasurableSet s :=
    e.symm.measurable
      (measurableSet_dominantCoordinateEvent E b j a τ)
  have hmp :=
    measurePreserving_piFinSuccAbove
      (fun _ : Fin (m + 1) => gaussianReal 0 1) j
  have hevent :
      (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
          (dominantCoordinateEvent E b j a τ) =
        (gaussianReal 0 1).prod ν s := by
    have hpre := hmp.measure_preimage hs.nullMeasurableSet
    simpa [s, ν, e] using hpre
  rw [hevent]
  apply prod_measure_le_of_fiber_le _ _ hs
  intro y
  let d : ℝ :=
    ∑ k : Fin m, E (j.succAbove k) *
      (y k + b (j.succAbove k)) ^ 2
  have hfiber :
      (fun x : ℝ => (x, y)) ⁻¹' s =
        {x | τ * |E j * (x + b j) ^ 2 + d - a| ≤
          |E j| * |x + b j|} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    unfold s dominantCoordinateEvent quadraticRatioValue
    change τ * |(∑ k, E k * (e.symm (x, y) k + b k) ^ 2) - a| ≤
        |E j| * |e.symm (x, y) j + b j| ↔
      τ * |E j * (x + b j) ^ 2 + d - a| ≤
        |E j| * |x + b j|
    rw [j.sum_univ_succAbove]
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, d]
  rw [hfiber]
  exact gaussianReal_scalar_dominant_event_le hE hτ

/-- Union of the first `r` ordered dominant-coordinate events.  It is empty
when `r = 0`, consists of one event when `r = 1`, and of at most two events
under the APSSS hypothesis `r ≤ 2`. -/
def dominantCoordinatesEvent {n : ℕ} (E b : Fin n → ℝ)
    (r : ℕ) (a τ : ℝ) : Set (Fin n → ℝ) :=
  ⋃ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < r),
    dominantCoordinateEvent E b j a τ

/-- The first `r ≤ 2` nonzero diagonal coordinates contribute at most
`8/τ` under the product standard-Gaussian law.  The proof is a finite
union bound and therefore also handles ranks zero and one without padding
them by fictitious coordinates. -/
theorem measure_dominantCoordinatesEvent_le {m : ℕ}
    (E b : Fin (m + 1) → ℝ) (r : ℕ) (a τ : ℝ)
    (hr : r ≤ 2) (hE : ∀ j : Fin (m + 1), (j : ℕ) < r → E j ≠ 0)
    (hτ : 0 < τ) :
    (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
        (dominantCoordinatesEvent E b r a τ) ≤
      ENNReal.ofReal (8 / τ) := by
  let I := Finset.univ.filter (fun j : Fin (m + 1) => (j : ℕ) < r)
  calc
    (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
        (dominantCoordinatesEvent E b r a τ) ≤
      ∑ j ∈ I,
        (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
          (dominantCoordinateEvent E b j a τ) := by
      exact measure_biUnion_finset_le I (dominantCoordinateEvent E b · a τ)
    _ ≤ ∑ _j ∈ I, ENNReal.ofReal (4 / τ) := by
      gcongr with j hj
      exact measure_dominantCoordinateEvent_le E b j a τ
        (hE j (Finset.mem_filter.mp hj).2) hτ
    _ ≤ 2 * ENNReal.ofReal (4 / τ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      gcongr
      have hcard :
          I.card = min (m + 1) r := by
        simpa [I] using
          (Fin.card_filter_val_lt (n := m + 1) (m := r))
      rw [hcard]
      exact_mod_cast (min_le_right (m + 1) r |>.trans hr)
    _ = ENNReal.ofReal (8 / τ) := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring

/-- Multiplicative event for the ordered tail numerator. -/
def tailMultiplicativeEvent {n : ℕ} (E b : Fin n → ℝ)
    (r : ℕ) (a τ : ℝ) : Set (Fin n → ℝ) :=
  {g | τ * |quadraticRatioValue E b g - a| ≤
    Real.sqrt (tailQuadraticRatioEnergy E b r g)}

/-- Deterministic APSSS three-way split.  With at most two dominant
coordinates, the full multiplicative event forces either one dominant
coordinate event or the tail event, all at threshold `t/3`.  For ranks zero
and one the unused slots simply disappear from the finite union. -/
theorem weightedSquares_multiplicativeEvent_subset_dominant_union_tail
    {n : ℕ} (E b : Fin n → ℝ) (r : ℕ) (a t : ℝ)
    (hr : r ≤ 2) (ht : 0 ≤ t) :
    (weightedSquaresRandomVector E b 0 a) ⁻¹'
        multiplicativeRatioPairEvent t ⊆
      dominantCoordinatesEvent E b r a (t / 3) ∪
        tailMultiplicativeEvent E b r a (t / 3) := by
  intro g hg
  have hfull :
      t * |quadraticRatioValue E b g - a| ≤
        Real.sqrt (quadraticRatioEnergy E b g) := by
    simpa [weightedSquaresRandomVector, multiplicativeRatioPairEvent,
      tailQuadraticRatioEnergy_zero] using hg
  have hsplit :=
    sqrt_quadraticRatioEnergy_le_dominant_add_tail E b g r
  let z : ℝ := (t / 3) * |quadraticRatioValue E b g - a|
  let I := Finset.univ.filter (fun j : Fin n => (j : ℕ) < r)
  have hz : 0 ≤ z := by
    dsimp [z]
    positivity
  by_contra hmem
  simp only [Set.mem_union, not_or] at hmem
  have htail :
      Real.sqrt (tailQuadraticRatioEnergy E b r g) < z := by
    have hn := hmem.2
    unfold tailMultiplicativeEvent at hn
    simp only [Set.mem_ofPred_eq, not_le] at hn
    exact hn
  have hcoord : ∀ j ∈ I, |E j| * |g j + b j| ≤ z := by
    intro j hj
    have hn := hmem.1
    unfold dominantCoordinatesEvent at hn
    have hnot :
        g ∉ dominantCoordinateEvent E b j a (t / 3) := by
      intro hgj
      apply hn
      exact Set.mem_iUnion₂.mpr ⟨j, hj, hgj⟩
    unfold dominantCoordinateEvent at hnot
    simp only [Set.mem_ofPred_eq, not_le] at hnot
    exact hnot.le
  have hcard : I.card ≤ 2 := by
    have heq : I.card = min n r := by
      simpa [I] using (Fin.card_filter_val_lt (n := n) (m := r))
    omega
  have hdominant :
      (∑ j : Fin n, if (j : ℕ) < r then
        |E j| * |g j + b j| else 0) ≤ 2 * z := by
    rw [← Finset.sum_filter]
    change (∑ j ∈ I, |E j| * |g j + b j|) ≤ 2 * z
    calc
      (∑ j ∈ I, |E j| * |g j + b j|) ≤ ∑ _j ∈ I, z := by
        gcongr with j hj
        exact hcoord j hj
      _ = I.card * z := by simp
      _ ≤ 2 * z := by
        gcongr
        exact_mod_cast hcard
  have hcontra :
      (∑ j : Fin n, if (j : ℕ) < r then
        |E j| * |g j + b j| else 0) +
          Real.sqrt (tailQuadraticRatioEnergy E b r g) <
        t * |quadraticRatioValue E b g - a| := by
    dsimp [z] at htail hdominant ⊢
    nlinarith [abs_nonneg (quadraticRatioValue E b g - a)]
  exact (not_lt_of_ge (le_trans hfull hsplit)) hcontra

/-- Probability form of the dominant/tail reduction.  The absolute dominant
constant is `24`: two scalar strips, each bounded by `4/(t/3)`.  No estimate
on the tail event is used here. -/
theorem measure_weightedSquares_multiplicativeEvent_le_dominant_add_tail
    {m : ℕ} (E b : Fin (m + 1) → ℝ) (r : ℕ) (a t : ℝ)
    (hr : r ≤ 2) (hE : ∀ j : Fin (m + 1), (j : ℕ) < r → E j ≠ 0)
    (ht : 1 ≤ t) :
    (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
        ((weightedSquaresRandomVector E b 0 a) ⁻¹'
          multiplicativeRatioPairEvent t) ≤
      ENNReal.ofReal (24 / t) +
        (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
          (tailMultiplicativeEvent E b r a (t / 3)) := by
  calc
    (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
        ((weightedSquaresRandomVector E b 0 a) ⁻¹'
          multiplicativeRatioPairEvent t) ≤
      (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
          (dominantCoordinatesEvent E b r a (t / 3) ∪
            tailMultiplicativeEvent E b r a (t / 3)) :=
      measure_mono
        (weightedSquares_multiplicativeEvent_subset_dominant_union_tail
          E b r a t hr (by positivity))
    _ ≤
      (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
          (dominantCoordinatesEvent E b r a (t / 3)) +
        (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
          (tailMultiplicativeEvent E b r a (t / 3)) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (24 / t) +
        (Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))
          (tailMultiplicativeEvent E b r a (t / 3)) := by
      gcongr
      convert measure_dominantCoordinatesEvent_le E b r a (t / 3)
        hr hE (by positivity) using 1
      congr 1
      field_simp
      ring

end PSSSNative.BlockBand.PSSS
