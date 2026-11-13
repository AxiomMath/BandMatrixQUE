module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalSum

/-!
# Accounting of the summed errors

Measure: an arbitrary probability space (the closed law in applications).
* `lint_rest_le`: `∫⁻ 1_A Φ (C (η³ + η⁴) + K) ≤ 4 Φ C N² Σ_c ∫⁻ 1_A |δ_c|³ + 8 Φ C N³ Σ_c
  ∫⁻ 1_A |δ_c|⁴ + Φ (C (4d³ + 8d⁴) + K)` for `η = Σ_c |δ_c| + d`;
* `lint_crude_le`: `∫⁻ 1_A Φ (ε + K₀ (2 Σ_c |Δ_c| + D) + L) ≤ Φ (ε + K₀ D + L) + 2 Φ K₀ Σ_c
  ∫⁻ 1_A |Δ_c|`;
* `sum_drift_le`, `sum_bracket_le`, `sum_birth_le`, `sum_lind_le`, `sum_cube_le`: partial sums of
  the step errors are bounded by the summed errors.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedLimit
open BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass
open scoped NNReal ENNReal

variable {K np : ℕ}

/-!
## Real inequalities
-/

theorem add_pow3_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by
  nlinarith [sq_nonneg (x - y), mul_nonneg hx hy, mul_nonneg (mul_nonneg hx hy) (add_nonneg hx hy)]

theorem add_pow4_le (x y : ℝ) : (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x + y),
    mul_nonneg (sq_nonneg (x - y)) (sq_nonneg (x + y))]

theorem sum_pow_le_card {ι : Type*} [Fintype ι] {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (n : ℕ) :
    (∑ i, x i) ^ (n + 1) ≤ (Fintype.card ι : ℝ) ^ n * ∑ i, x i ^ (n + 1) := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.1 h0
    simp
  · have h := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset ι)) (fun i _ => hx i) n
    rw [Finset.card_univ, div_le_iff₀ (by positivity)] at h
    linarith

section Lint

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {A A' : Set Ω}

omit [IsProbabilityMeasure μ] in
theorem aem_ind (hA' : MeasurableSet A') (hAA : A =ᵐ[μ] A') {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    AEMeasurable (A.indicator f) μ :=
  (hf.indicator hA').aemeasurable.congr (indicator_ae_eq_of_ae_eq_set hAA).symm

theorem lint_ind_const_le (c : ℝ≥0∞) : ∫⁻ y, A.indicator (fun _ => c) y ∂μ ≤ c :=
  (lintegral_indicator_const_le A c).trans (by
    calc c * μ A ≤ c * 1 := by gcongr; exact prob_le_one
      _ = c := mul_one c)

omit [IsProbabilityMeasure μ] in
theorem lint_ind_add (hA' : MeasurableSet A') (hAA : A =ᵐ[μ] A') {f g : Ω → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ y, A.indicator (fun y => f y + g y) y ∂μ =
      ∫⁻ y, A.indicator f y ∂μ + ∫⁻ y, A.indicator g y ∂μ := by
  have e : A.indicator (fun y => f y + g y) = fun y => A.indicator f y + A.indicator g y := by
    funext y; by_cases h : y ∈ A <;> simp [h]
  rw [e, lintegral_add_left' (aem_ind hA' hAA hf)]

omit [IsProbabilityMeasure μ] in
theorem lint_ind_const_mul (c : ℝ≥0∞) (hc : c ≠ ⊤) (f : Ω → ℝ≥0∞) :
    ∫⁻ y, A.indicator (fun y => c * f y) y ∂μ = c * ∫⁻ y, A.indicator f y ∂μ := by
  have e : A.indicator (fun y => c * f y) = fun y => c * A.indicator f y := by
    funext y; by_cases h : y ∈ A <;> simp [h]
  rw [e, lintegral_const_mul' c _ hc]

omit [IsProbabilityMeasure μ] in
theorem lint_ind_sum (hA' : MeasurableSet A') (hAA : A =ᵐ[μ] A') {ι : Type*} [Fintype ι]
    {f : ι → Ω → ℝ≥0∞} (hf : ∀ c, Measurable (f c)) :
    ∫⁻ y, A.indicator (fun y => ∑ c, f c y) y ∂μ = ∑ c, ∫⁻ y, A.indicator (f c) y ∂μ := by
  have e : A.indicator (fun y => ∑ c, f c y) = fun y => ∑ c, A.indicator (f c) y := by
    funext y; by_cases h : y ∈ A <;> simp [h]
  rw [e, lintegral_finsetSum' _ fun c _ => aem_ind hA' hAA (hf c)]

/-- **The rest of the generic steps, integrated.** -/
theorem lint_rest_le (hA' : MeasurableSet A') (hAA : A =ᵐ[μ] A') {ι : Type*} [Fintype ι]
    {δ : ι → Ω → ℂ} (hδ : ∀ c, Measurable (δ c)) {Φ C d Kc : ℝ} (hΦ : 0 ≤ Φ) (hC : 0 ≤ C)
    (hd : 0 ≤ d) (hK : 0 ≤ Kc) :
    ∫⁻ y, A.indicator (fun y => ENNReal.ofReal (Φ * (C * ((∑ c, ‖δ c y‖ + d) ^ 3 +
        (∑ c, ‖δ c y‖ + d) ^ 4) + Kc))) y ∂μ ≤
      ENNReal.ofReal (4 * Φ * C * (Fintype.card ι : ℝ) ^ 2) *
          ∑ c, ∫⁻ y, A.indicator (fun y => ‖δ c y‖ₑ ^ 3) y ∂μ +
        ENNReal.ofReal (8 * Φ * C * (Fintype.card ι : ℝ) ^ 3) *
          ∑ c, ∫⁻ y, A.indicator (fun y => ‖δ c y‖ₑ ^ 4) y ∂μ +
        ENNReal.ofReal (Φ * (C * (4 * d ^ 3 + 8 * d ^ 4) + Kc)) := by
  set N : ℝ := ((Fintype.card ι : ℕ) : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hpt : ∀ y, ENNReal.ofReal (Φ * (C * ((∑ c, ‖δ c y‖ + d) ^ 3 +
        (∑ c, ‖δ c y‖ + d) ^ 4) + Kc)) ≤
      (ENNReal.ofReal (4 * Φ * C * N ^ 2) * ∑ c, ‖δ c y‖ₑ ^ 3 +
        ENNReal.ofReal (8 * Φ * C * N ^ 3) * ∑ c, ‖δ c y‖ₑ ^ 4) +
        ENNReal.ofReal (Φ * (C * (4 * d ^ 3 + 8 * d ^ 4) + Kc)) := fun y => by
    set S := ∑ c, ‖δ c y‖
    have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have h3 := add_pow3_le hS hd
    have h4 := add_pow4_le S d
    have hS3 := sum_pow_le_card (fun c => norm_nonneg (δ c y)) 2
    have hS4 := sum_pow_le_card (fun c => norm_nonneg (δ c y)) 3
    have e3 : ∑ c, ‖δ c y‖ₑ ^ 3 = ENNReal.ofReal (∑ c, ‖δ c y‖ ^ 3) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun c _ => by positivity]
      exact Finset.sum_congr rfl fun c _ => by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    have e4 : ∑ c, ‖δ c y‖ₑ ^ 4 = ENNReal.ofReal (∑ c, ‖δ c y‖ ^ 4) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun c _ => by positivity]
      exact Finset.sum_congr rfl fun c _ => by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    have hs3 : 0 ≤ ∑ c, ‖δ c y‖ ^ 3 := Finset.sum_nonneg fun _ _ => by positivity
    have hs4 : 0 ≤ ∑ c, ‖δ c y‖ ^ 4 := Finset.sum_nonneg fun _ _ => by positivity
    rw [e3, e4, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hA3 : (S + d) ^ 3 ≤ 4 * (N ^ 2 * ∑ c, ‖δ c y‖ ^ 3) + 4 * d ^ 3 := by
      calc (S + d) ^ 3 ≤ 4 * (S ^ 3 + d ^ 3) := h3
        _ ≤ 4 * (N ^ 2 * ∑ c, ‖δ c y‖ ^ (2 + 1) + d ^ 3) := by gcongr
        _ = _ := by ring
    have hA4 : (S + d) ^ 4 ≤ 8 * (N ^ 3 * ∑ c, ‖δ c y‖ ^ 4) + 8 * d ^ 4 := by
      calc (S + d) ^ 4 ≤ 8 * (S ^ 4 + d ^ 4) := h4
        _ ≤ 8 * (N ^ 3 * ∑ c, ‖δ c y‖ ^ (3 + 1) + d ^ 4) := by gcongr
        _ = _ := by ring
    have : C * ((S + d) ^ 3 + (S + d) ^ 4) ≤
        C * ((4 * (N ^ 2 * ∑ c, ‖δ c y‖ ^ 3) + 4 * d ^ 3) +
          (8 * (N ^ 3 * ∑ c, ‖δ c y‖ ^ 4) + 8 * d ^ 4)) := by gcongr
    nlinarith [mul_le_mul_of_nonneg_left this hΦ]
  have hmono : ∫⁻ y, A.indicator (fun y => ENNReal.ofReal (Φ * (C * ((∑ c, ‖δ c y‖ + d) ^ 3 +
        (∑ c, ‖δ c y‖ + d) ^ 4) + Kc))) y ∂μ ≤
      ∫⁻ y, A.indicator (fun y => (ENNReal.ofReal (4 * Φ * C * N ^ 2) * ∑ c, ‖δ c y‖ₑ ^ 3 +
        ENNReal.ofReal (8 * Φ * C * N ^ 3) * ∑ c, ‖δ c y‖ₑ ^ 4) +
        ENNReal.ofReal (Φ * (C * (4 * d ^ 3 + 8 * d ^ 4) + Kc))) y ∂μ :=
    lintegral_mono fun y => by
      by_cases h : y ∈ A
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; exact hpt y
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
  refine hmono.trans ?_
  have hm3 : ∀ c, Measurable fun y => ‖δ c y‖ₑ ^ 3 := fun c => (hδ c).enorm.pow_const 3
  have hm4 : ∀ c, Measurable fun y => ‖δ c y‖ₑ ^ 4 := fun c => (hδ c).enorm.pow_const 4
  have hs3 : Measurable fun y => ∑ c, ‖δ c y‖ₑ ^ 3 := Finset.measurable_sum _ fun c _ => hm3 c
  have hs4 : Measurable fun y => ∑ c, ‖δ c y‖ₑ ^ 4 := Finset.measurable_sum _ fun c _ => hm4 c
  have hf1 : Measurable fun y => ENNReal.ofReal (4 * Φ * C * N ^ 2) * ∑ c, ‖δ c y‖ₑ ^ 3 +
      ENNReal.ofReal (8 * Φ * C * N ^ 3) * ∑ c, ‖δ c y‖ₑ ^ 4 :=
    (hs3.const_mul _).add (hs4.const_mul _)
  rw [lint_ind_add hA' hAA hf1, lint_ind_add hA' hAA (hs3.const_mul _),
    lint_ind_const_mul _ ENNReal.ofReal_ne_top, lint_ind_const_mul _ ENNReal.ofReal_ne_top,
    lint_ind_sum hA' hAA hm3, lint_ind_sum hA' hAA hm4]
  exact add_le_add le_rfl (lint_ind_const_le _)

/-- **The special cells, integrated.** -/
theorem lint_crude_le (hA' : MeasurableSet A') (hAA : A =ᵐ[μ] A') {ι : Type*} [Fintype ι]
    {Δ : ι → Ω → ℂ} (hΔ : ∀ c, Measurable (Δ c)) {Φ ε K₀ D L : ℝ} (hΦ : 0 ≤ Φ) (hε : 0 ≤ ε)
    (hK : 0 ≤ K₀) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    ∫⁻ y, A.indicator (fun y => ENNReal.ofReal (Φ * (ε + K₀ * (2 * ∑ c, ‖Δ c y‖ + D) + L))) y ∂μ ≤
      ENNReal.ofReal (Φ * (ε + K₀ * D + L)) +
        ENNReal.ofReal (2 * Φ * K₀) * ∑ c, ∫⁻ y, A.indicator (fun y => ‖Δ c y‖ₑ) y ∂μ := by
  have hpt : ∀ y, ENNReal.ofReal (Φ * (ε + K₀ * (2 * ∑ c, ‖Δ c y‖ + D) + L)) =
      ENNReal.ofReal (2 * Φ * K₀) * ∑ c, ‖Δ c y‖ₑ + ENNReal.ofReal (Φ * (ε + K₀ * D + L)) :=
    fun y => by
    have hs : 0 ≤ ∑ c, ‖Δ c y‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have e : ∑ c, ‖Δ c y‖ₑ = ENNReal.ofReal (∑ c, ‖Δ c y‖) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun c _ => norm_nonneg _]
      exact Finset.sum_congr rfl fun c _ => (ofReal_norm _).symm
    rw [e, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by positivity)]
    congr 1; ring
  simp only [hpt]
  have hm : ∀ c, Measurable fun y => ‖Δ c y‖ₑ := fun c => (hΔ c).enorm
  have hs : Measurable fun y => ∑ c, ‖Δ c y‖ₑ := Finset.measurable_sum _ fun c _ => hm c
  have hf1 : Measurable fun y => ENNReal.ofReal (2 * Φ * K₀) * ∑ c, ‖Δ c y‖ₑ := hs.const_mul _
  rw [lint_ind_add hA' hAA hf1, lint_ind_const_mul _ ENNReal.ofReal_ne_top, lint_ind_sum hA' hAA hm,
    add_comm]
  exact add_le_add (lint_ind_const_le _) le_rfl

end Lint

/-!
## Partial sums of the step errors
-/

section Partial

variable {b E s h : ℝ} {τ m : Fin np → ℝ} {W : ℕ} {T R : ℝ}
  {V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}

theorem sum_drift_le {G : Finset ℕ} (hG : G ⊆ nbSteps s T τ W) (c c' : CIdx K np) :
    ∑ j ∈ G, ∫⁻ y, ‖(b3Alive b E s h τ m R W j V).indicator (fun y =>
        (closedLaw b W np)[(b3Alive b E s h τ m R W j V).indicator (b3dX b E s h τ m W j V c) |
          b3Sigma W j np] y - (W : ℂ)⁻¹ * cDrift b E c (b3ClosedGramAt b E s h τ m W j V y)) y‖ₑ
        ∂closedLaw b W np ≤ b3SummedErr b E s T h τ m R W V c c' := by
  unfold b3SummedErr
  exact (Finset.sum_le_sum_of_subset hG).trans (le_add_right (le_add_right le_rfl))

theorem sum_bracket_le {G : Finset ℕ} (hG : G ⊆ nbSteps s T τ W) (c c' : CIdx K np) :
    ∑ j ∈ G, ∫⁻ y, ‖(b3Alive b E s h τ m R W j V).indicator (fun y =>
        (closedLaw b W np)[(b3Alive b E s h τ m R W j V).indicator (fun y =>
          b3dX b E s h τ m W j V c y * b3dX b E s h τ m W j V c' y) | b3Sigma W j np] y -
        (W : ℂ)⁻¹ * cCov b E c c' (b3ClosedGramAt b E s h τ m W j V y)) y‖ₑ
        ∂closedLaw b W np ≤ b3SummedErr b E s T h τ m R W V c c' := by
  unfold b3SummedErr
  exact (Finset.sum_le_sum_of_subset hG).trans (le_add_right (le_add_left le_rfl))

theorem sum_birth_le {G : Finset ℕ}
    (hG : G ⊆ (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter (fun j => IsBirthStep τ W j))
    (c c' : CIdx K np) :
    ∑ j ∈ G, ∫⁻ y, ‖(b3Alive b E s h τ m R W j V).indicator (fun y =>
        b3dX b E s h τ m W j V c y - cEntry c (b3BirthAt b τ m W j) (b3KBirthAt E τ m W j)) y‖ₑ
        ∂closedLaw b W np ≤ b3SummedErr b E s T h τ m R W V c c' := by
  unfold b3SummedErr
  exact (Finset.sum_le_sum_of_subset hG).trans (le_add_left le_rfl)

theorem sum_lind_le {G : Finset ℕ} (hG : G ⊆ nbSteps s T τ W) (c : CIdx K np) :
    ∑ j ∈ G, ∫⁻ y, (b3Alive b E s h τ m R W j V).indicator
        (fun y => ‖b3dX b E s h τ m W j V c y‖ₑ ^ 4) y ∂closedLaw b W np ≤
      b3LindebergErr b E s T h τ m R W V c :=
  Finset.sum_le_sum_of_subset hG

theorem sum_cube_le {G : Finset ℕ} (hG : G ⊆ nbSteps s T τ W) (c : GIdx K np) :
    ∑ j ∈ G, ∫⁻ y, (b3Alive b E s h τ m R W j V).indicator
        (fun y => ‖b3dX b E s h τ m W j V (Sum.inl c) y‖ₑ ^ 3) y ∂closedLaw b W np ≤
      ∑ j ∈ nbSteps s T τ W, ∫⁻ y, (b3Alive b E s h τ m R W j V).indicator
        (fun y => ‖b3dX b E s h τ m W j V (Sum.inl c) y‖ₑ ^ 3) y ∂closedLaw b W np :=
  Finset.sum_le_sum_of_subset hG

end Partial

/-!
## Abstract summation
-/

theorem sum_generic_le {ι : Type*} [Fintype ι] (G : Finset ℕ) (Y : ℕ → ℝ≥0∞)
    (e1 : ℕ → ι → ℝ≥0∞) (e2 : ℕ → ι → ι → ℝ≥0∞) (l3 l4 : ℕ → ι → ℝ≥0∞)
    (E1 : ι → ℝ≥0∞) (E2 : ι → ι → ℝ≥0∞) (C3 C4 : ι → ℝ≥0∞) (κa κ3 κ4 k : ℝ≥0∞)
    (hY : ∀ j ∈ G, Y j ≤ κa * (∑ c, e1 j c + ∑ c, ∑ c', e2 j c c') +
      (κ3 * ∑ c, l3 j c + κ4 * ∑ c, l4 j c + k))
    (h1 : ∀ c, ∑ j ∈ G, e1 j c ≤ E1 c) (h2 : ∀ c c', ∑ j ∈ G, e2 j c c' ≤ E2 c c')
    (h3 : ∀ c, ∑ j ∈ G, l3 j c ≤ C3 c) (h4 : ∀ c, ∑ j ∈ G, l4 j c ≤ C4 c) :
    ∑ j ∈ G, Y j ≤ κa * (∑ c, E1 c + ∑ c, ∑ c', E2 c c') +
      (κ3 * ∑ c, C3 c + κ4 * ∑ c, C4 c + G.card * k) := by
  refine (Finset.sum_le_sum hY).trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_comm (s := G) (t := Finset.univ) (f := fun j c => e1 j c),
    Finset.sum_comm (s := G) (t := Finset.univ) (f := fun j c => l3 j c),
    Finset.sum_comm (s := G) (t := Finset.univ) (f := fun j c => l4 j c),
    Finset.sum_comm (s := G) (t := Finset.univ) (f := fun j c => ∑ c', e2 j c c')]
  have h2' : ∀ c, ∑ j ∈ G, ∑ c', e2 j c c' ≤ ∑ c', E2 c c' := fun c => by
    rw [Finset.sum_comm]; exact Finset.sum_le_sum fun c' _ => h2 c c'
  gcongr with c _ c _ c _ c _
  · exact h1 c
  · exact h2' c
  · exact h3 c
  · exact h4 c

theorem sum_special_le {ι : Type*} [Fintype ι] (S : Finset ℕ) (Y : ℕ → ℝ≥0∞)
    (d : ℕ → ι → ℝ≥0∞) (f0 : ι → ℝ≥0∞) (g : ℕ → ι → ℝ≥0∞) (Bs : Finset ℕ) (p : ℕ)
    (Eb : ι → ℝ≥0∞) (κ k : ℝ≥0∞) (hY : ∀ j ∈ S, Y j ≤ k + κ * ∑ c, d j c)
    (hd : ∀ j ∈ S, ∀ c, d j c ≤ (if j = p then f0 c else 0) + (if j ∈ Bs then g j c else 0))
    (hb : ∀ c, ∑ j ∈ Bs, g j c ≤ Eb c) :
    ∑ j ∈ S, Y j ≤ S.card * k + κ * ∑ c, (f0 c + Eb c) := by
  classical
  refine (Finset.sum_le_sum hY).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  gcongr
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun c _ => ?_
  refine (Finset.sum_le_sum fun j hj => hd j hj c).trans ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · rw [Finset.sum_ite_eq']
    split_ifs <;> simp
  · rw [← Finset.sum_filter]
    refine le_trans ?_ (hb c)
    exact Finset.sum_le_sum_of_subset (fun j hj => (Finset.mem_filter.1 hj).2)

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
