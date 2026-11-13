module

public import BlockBand.SourceProcess.BornRestart.PathComp

/-!
# Bounds for stopped compensated coordinates along born paths

* `norm_le_of_le_stop`: a continuous path bounded strictly before `τ > 0` is bounded up to `τ`.
* `exists_pComp_bound`, `exists_pBr_bound`: while the continuous part `g - J` stays in the ball
  of radius `R` (real coordinates), `pComp` is `O(1 + r)` and `pBr` is `O((1 + r)²)`, with
  constants depending only on `D₀, 𝖣, j, R` and the coordinates.
* `exists_pComp_stop_bound`, `exists_pBr_stop_bound`: the same at `stopTime θ r` when the ball
  bound holds strictly before `θ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornRestart

open MeasureTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.BornUnique
open scoped NNReal

/-- A continuous path bounded strictly before `τ > 0` is bounded up to `τ`. -/
theorem norm_le_of_le_stop {E : Type*} [SeminormedAddCommGroup E] {y : ℝ≥0 → E}
    (hy : Continuous y) {τ : WithTop ℝ≥0} {R : ℝ}
    (h : ∀ s : ℝ≥0, (s : WithTop ℝ≥0) < τ → ‖y s‖ ≤ R) (hτ : 0 < τ) {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) ≤ τ) : ‖y s‖ ≤ R := by
  rcases hs.lt_or_eq with h1 | h1
  · exact h s h1
  have hs0 : 0 < s := by
    rw [← h1] at hτ
    exact WithTop.coe_pos.1 hτ
  have : (𝓝[<] s).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hs0⟩
  have ht : Tendsto (fun x => ‖y x‖) (𝓝[<] s) (𝓝 ‖y s‖) :=
    ((hy.tendsto s).norm).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto ht ?_
  filter_upwards [(self_mem_nhdsWithin : Iio s ∈ 𝓝[<] s)] with s' hs'
  exact h s' (by rw [← h1]; exact WithTop.coe_lt_coe.2 hs')

variable {c F : Type} [Fintype c] [DecidableEq c] [Fintype F] {D0 : ℝ} {D : Matrix c c ℂ}
  {j : F → GramState c}

/-- Integrals along a path in a ball are `O(r)`. -/
theorem exists_pInt_bound {φ : GramState c → ℂ} (hφ : Continuous φ) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (g : ℝ≥0 → GramState c) (b : F → ℝ) (r₁ : ℝ≥0),
      (∀ s ≤ r₁, ‖toGramReal (g s - birthSum j b (s : ℝ))‖ ≤ R) →
      ∀ r ≤ r₁, ‖∫ s in Ioc (0 : ℝ) r, φ (g s.toNNReal)‖ ≤ C * r₁ := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_continuous hφ (R + jumpBound j)
  refine ⟨C, hC0, fun g b r₁ hR r hr => ?_⟩
  refine (norm_setIntegral_le_of_norm_le_const (C := C) (by simp) fun s hs => ?_).trans ?_
  · refine hC _ (norm_toGramReal_path_le (hR _ ?_))
    have := Real.toNNReal_le_toNNReal hs.2
    rw [Real.toNNReal_coe] at this
    exact this.trans hr
  · rw [Real.volume_real_Ioc_of_le (NNReal.coe_nonneg r), sub_zero]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hr) hC0

/-- **Bound for the compensated coordinates in a ball.** -/
theorem exists_pComp_bound (e : Fin 2 × c × c) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (g : ℝ≥0 → GramState c) (b : F → ℝ) (r₁ : ℝ≥0),
      (∀ s ≤ r₁, ‖toGramReal (g s - birthSum j b (s : ℝ))‖ ≤ R) →
      ∀ r ≤ r₁, ‖pComp D0 D j g b e r‖ ≤ C * (1 + r₁) := by
  obtain ⟨Ce, hCe0, hCe⟩ := exists_bound_of_continuous (continuous_gramEntry (c := c) e) R
  obtain ⟨Cd, hCd0, hCd⟩ := exists_pInt_bound (j := j) (continuous_gramDriftEntry D0 D e) R
  refine ⟨2 * Ce + Cd, by positivity, fun g b r₁ hR r hr => ?_⟩
  have h1 := hCe _ (hR r hr)
  have h2 := hCe _ (hR 0 zero_le)
  have h3 := hCd g b r₁ hR r hr
  unfold pComp
  have hr₁ : (0 : ℝ) ≤ r₁ := r₁.coe_nonneg
  calc _ ≤ ‖gramEntry e (g r - birthSum j b (r : ℝ))‖ +
        ‖gramEntry e (g 0 - birthSum j b ((0 : ℝ≥0) : ℝ))‖ +
        ‖∫ s in Ioc (0 : ℝ) r, gramDriftEntry D0 D e (g s.toNNReal)‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ Ce + Ce + Cd * r₁ := by gcongr
    _ ≤ (2 * Ce + Cd) * (1 + r₁) := by nlinarith

/-- **Bound for the compensated products in a ball.** -/
theorem exists_pBr_bound (e e' : Fin 2 × c × c) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (g : ℝ≥0 → GramState c) (b : F → ℝ) (r₁ : ℝ≥0),
      (∀ s ≤ r₁, ‖toGramReal (g s - birthSum j b (s : ℝ))‖ ≤ R) →
      ∀ r ≤ r₁, ‖pBr D0 D j g b e e' r‖ ≤ C * (1 + r₁) ^ 2 := by
  obtain ⟨C1, hC10, hC1⟩ := exists_pComp_bound (D0 := D0) (D := D) (j := j) e R
  obtain ⟨C2, hC20, hC2⟩ := exists_pComp_bound (D0 := D0) (D := D) (j := j) e' R
  obtain ⟨C3, hC30, hC3⟩ := exists_pInt_bound (j := j) (continuous_gramCovEntry D0 D e e') R
  refine ⟨C1 * C2 + C3, by positivity, fun g b r₁ hR r hr => ?_⟩
  have h1 := hC1 g b r₁ hR r hr
  have h2 := hC2 g b r₁ hR r hr
  have h3 := hC3 g b r₁ hR r hr
  have hr₁ : (0 : ℝ) ≤ r₁ := r₁.coe_nonneg
  unfold pBr
  calc _ ≤ ‖pComp D0 D j g b e r‖ * ‖pComp D0 D j g b e' r‖ +
        ‖∫ s in Ioc (0 : ℝ) r, gramCovEntry D0 D e e' (g s.toNNReal)‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_mul_le _ _) _)
    _ ≤ C1 * (1 + r₁) * (C2 * (1 + r₁)) + C3 * r₁ := by gcongr
    _ ≤ (C1 * C2 + C3) * (1 + r₁) ^ 2 := by
      nlinarith [mul_nonneg hC10 hC20, mul_nonneg hC30 hr₁, mul_nonneg hC30 (sq_nonneg (r₁ : ℝ))]

/-- **Stopped bound for the compensated coordinates.** -/
theorem exists_pComp_stop_bound (e : Fin 2 × c × c) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (g : ℝ≥0 → GramState c) (b : F → ℝ) (θ : WithTop ℝ≥0) (r : ℝ≥0),
      Continuous (fun t => g t - birthSum j b (t : ℝ)) →
      (∀ s : ℝ≥0, (s : WithTop ℝ≥0) < θ → ‖toGramReal (g s - birthSum j b (s : ℝ))‖ ≤ R) →
      ‖pComp D0 D j g b e (stopTime θ r)‖ ≤ C * (1 + r) := by
  obtain ⟨C, hC0, hC⟩ := exists_pComp_bound (D0 := D0) (D := D) (j := j) e R
  refine ⟨C, hC0, fun g b θ r hc hθ => ?_⟩
  rcases eq_zero_or_pos θ with h0 | h0
  · rw [h0, stopTime_zero', pComp_zero, norm_zero]
    have : (0 : ℝ) ≤ r := r.coe_nonneg
    positivity
  refine (hC g b (stopTime θ r) (fun s hs => ?_) _ le_rfl).trans ?_
  · exact norm_le_of_le_stop (continuous_toGramReal.comp hc) hθ h0
      ((WithTop.coe_le_coe.2 hs).trans (stopTime_le_self θ r))
  · exact mul_le_mul_of_nonneg_left (by gcongr; exact_mod_cast stopTime_le θ r) hC0

/-- **Stopped bound for the compensated products.** -/
theorem exists_pBr_stop_bound (e e' : Fin 2 × c × c) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (g : ℝ≥0 → GramState c) (b : F → ℝ) (θ : WithTop ℝ≥0) (r : ℝ≥0),
      Continuous (fun t => g t - birthSum j b (t : ℝ)) →
      (∀ s : ℝ≥0, (s : WithTop ℝ≥0) < θ → ‖toGramReal (g s - birthSum j b (s : ℝ))‖ ≤ R) →
      ‖pBr D0 D j g b e e' (stopTime θ r)‖ ≤ C * (1 + r) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_pBr_bound (D0 := D0) (D := D) (j := j) e e' R
  refine ⟨C, hC0, fun g b θ r hc hθ => ?_⟩
  rcases eq_zero_or_pos θ with h0 | h0
  · rw [h0, stopTime_zero', pBr_zero, norm_zero]
    positivity
  refine (hC g b (stopTime θ r) (fun s hs => ?_) _ le_rfl).trans ?_
  · exact norm_le_of_le_stop (continuous_toGramReal.comp hc) hθ h0
      ((WithTop.coe_le_coe.2 hs).trans (stopTime_le_self θ r))
  · exact mul_le_mul_of_nonneg_left (by gcongr; exact_mod_cast stopTime_le θ r) hC0

end BlockBand.SourceProcess.BornRestart
