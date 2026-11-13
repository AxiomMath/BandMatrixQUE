module

public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# A `1/4`-net of the complex unit ball

* `card_le_of_separated`: in a real `d`-dimensional normed space, a `1/4`-separated finite subset
  of the closed unit ball has at most `9^d` points (volume comparison of disjoint `1/8`-balls
  inside the `9/8`-ball, `Measure.addHaar_ball_of_pos`).
* `exists_quarter_net`: `EuclideanSpace ℂ (Fin n)` (real dimension `2n`) has a `1/4`-net of its
  closed unit ball inside the ball with at most `9^{2n}` points (maximal separated set).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open MeasureTheory Metric Set Module
open scoped ENNReal NNReal

section
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]

theorem card_le_of_separated (C : Finset X) (hC : ∀ c ∈ C, ‖c‖ ≤ 1)
    (hsep : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → 1 / 4 < dist c c') :
    C.card ≤ 9 ^ finrank ℝ X := by
  let μ : Measure X := Measure.addHaar
  set d := finrank ℝ X
  have hdisj : (C : Set X).PairwiseDisjoint fun c => ball c (1 / 8 : ℝ) := by
    intro c hc c' hc' hne
    refine Set.disjoint_left.mpr fun z hz hz' => ?_
    have h1 := hsep c hc c' hc' hne
    have h2 := dist_triangle_right c c' z
    rw [mem_ball] at hz hz'
    rw [dist_comm c z, dist_comm c' z] at h2
    linarith
  have hsub : (⋃ c ∈ C, ball c (1 / 8 : ℝ)) ⊆ ball (0 : X) (9 / 8) := by
    intro z hz
    simp only [mem_iUnion] at hz
    obtain ⟨c, hc, hz⟩ := hz
    rw [mem_ball, dist_zero_right]
    rw [mem_ball, dist_eq_norm] at hz
    have := norm_le_norm_add_norm_sub' z c
    have := hC c hc
    rw [norm_sub_rev] at hz
    linarith [norm_sub_rev z c]
  have hmeas := measure_biUnion_finset (μ := μ) hdisj (fun c _ => measurableSet_ball)
  have key : ((C.card : ℝ≥0∞) * ENNReal.ofReal ((1 / 8 : ℝ) ^ d)) * μ (ball 0 1) ≤
      ENNReal.ofReal ((9 / 8 : ℝ) ^ d) * μ (ball 0 1) := by
    calc ((C.card : ℝ≥0∞) * ENNReal.ofReal ((1 / 8 : ℝ) ^ d)) * μ (ball 0 1)
        = ∑ c ∈ C, μ (ball c (1 / 8 : ℝ)) := by
          rw [Finset.sum_congr rfl fun c _ => Measure.addHaar_ball_of_pos μ c (by norm_num : (0 : ℝ) < 1 / 8),
            Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ = μ (⋃ c ∈ C, ball c (1 / 8 : ℝ)) := hmeas.symm
      _ ≤ μ (ball 0 (9 / 8)) := measure_mono hsub
      _ = _ := Measure.addHaar_ball_of_pos μ 0 (by norm_num)
  have h0 : μ (ball (0 : X) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have htop : μ (ball (0 : X) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have key2 := (ENNReal.mul_le_mul_iff_left h0 htop).mp key
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at key2
  have h8 : (0 : ℝ) < (1 / 8 : ℝ) ^ d := by positivity
  have h98 : (9 / 8 : ℝ) ^ d = 9 ^ d * (1 / 8) ^ d := by rw [← mul_pow]; norm_num
  rw [h98] at key2
  have : (C.card : ℝ) ≤ 9 ^ d := le_of_mul_le_mul_right key2 h8
  exact_mod_cast this
end

theorem finrank_euclidean_complex (n : ℕ) : finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2 * n := by
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin]

theorem packingNumber_le (n : ℕ) :
    packingNumber (1 / 4 : ℝ≥0) (closedBall (0 : EuclideanSpace ℂ (Fin n)) 1) ≤ 9 ^ (2 * n) := by
  have hfin : ∀ C : Finset (EuclideanSpace ℂ (Fin n)),
      (↑C : Set (EuclideanSpace ℂ (Fin n))) ⊆ closedBall 0 1 →
      IsSeparated ((1 / 4 : ℝ≥0) : ℝ≥0∞) (↑C : Set (EuclideanSpace ℂ (Fin n))) →
      C.card ≤ 9 ^ (2 * n) := by
    intro C hCA hsep
    let _ : MeasurableSpace (EuclideanSpace ℂ (Fin n)) := borel _
    have _ : BorelSpace (EuclideanSpace ℂ (Fin n)) := ⟨rfl⟩
    rw [← finrank_euclidean_complex]
    refine card_le_of_separated C (fun c hc => by simpa using hCA hc) fun c hc c' hc' hne => ?_
    have : ((1 / 4 : ℝ≥0) : ℝ≥0∞) < edist c c' := hsep hc hc' hne
    rw [edist_dist] at this
    have h := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mp
      (by simpa using this : ENNReal.ofReal (1 / 4) < ENNReal.ofReal (dist c c'))
    exact h
  unfold packingNumber
  refine iSup₂_le fun C hCA => iSup_le fun hsep => ?_
  by_cases hC : C.Finite
  · rw [← hC.coe_toFinset, Set.encard_coe_eq_coe_finsetCard]
    have := hfin hC.toFinset (by simpa using hCA) (by simpa using hsep)
    exact_mod_cast this
  · exfalso
    obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hC (9 ^ (2 * n) + 1)
    have := hfin t (ht.trans hCA) (hsep.mono ht)
    omega

theorem exists_quarter_net (n : ℕ) : ∃ N : Finset (EuclideanSpace ℂ (Fin n)),
    N.card ≤ 9 ^ (2 * n) ∧ (∀ u ∈ N, ‖u‖ ≤ 1) ∧ ∀ x : EuclideanSpace ℂ (Fin n), ‖x‖ ≤ 1 →
      ∃ u ∈ N, ‖x - u‖ ≤ 1 / 4 := by
  set A := closedBall (0 : EuclideanSpace ℂ (Fin n)) 1
  have hP := packingNumber_le n
  have hne : packingNumber (1 / 4 : ℝ≥0) A ≠ ⊤ := ne_top_of_le_ne_top (by simp) hP
  set S := maximalSeparatedSet (1 / 4 : ℝ≥0) A
  have hS : S.encard ≤ 9 ^ (2 * n) := by rw [encard_maximalSeparatedSet hne]; exact hP
  have hSf : S.Finite := Set.finite_of_encard_le_coe hS
  refine ⟨hSf.toFinset, ?_, ?_, ?_⟩
  · rw [hSf.encard_eq_coe_toFinset_card] at hS
    exact_mod_cast hS
  · intro u hu
    have := maximalSeparatedSet_subset (hSf.mem_toFinset.mp hu)
    simpa [A] using this
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := isCover_maximalSeparatedSet hne (show x ∈ A by simpa [A] using hx)
    refine ⟨y, hSf.mem_toFinset.mpr hy, ?_⟩
    have hxy' : edist x y ≤ ((1 / 4 : ℝ≥0) : ℝ≥0∞) := hxy
    rw [edist_dist] at hxy'
    have := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp
      (by simpa using hxy' : ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal (1 / 4))
    rwa [dist_eq_norm] at this

end BlockBand.Transmission.PassiveLayer
