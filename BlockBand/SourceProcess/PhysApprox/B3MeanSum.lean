module

public import BlockBand.SourceProcess.PhysApprox.B3GenMem
public import BlockBand.SourceProcess.PhysApprox.B3MartUnc

/-!
# The summed `𝒦` means from the `L⁴` mean shape

The mean shape in `L⁴`: at every non-birth step, a.e. `|e_i| ≤ C(δ_i + W⁻¹)` with
`∫δ_i⁴ ≤ C/W⁴` (estimates `KStopMeanForm4`, closed stopped steps, and `KUncMeanForm4`, unclosed
steps). Proved here:

* `lintegral_sum_pow_four_le_of_dom` (generic): `∫(Σ_{i∈S}|e_i|)⁴ ≤ |S|⁴ · 8c⁴(K + w⁴)` from
  `|e_i| ≤ c(δ_i + w)`, `∫δ_i⁴ ≤ K` (power mean; no measurability of `δ_i` needed);
* **`kStopMeanSum_of_form4 : KStopMeanForm4 → KStopMeanSum`** (`|S| ≤ ⌊WT⌋ ≤ W max T 0`, so the
  sum is `≤ 8C⁴(max T 0)⁴(C + 1)`, uniform in `W`);
* **`genKMeanForm_of_form4 : KStopMeanForm4 → GenKMeanForm`** (`δ' = δ + W⁻¹`,
  `∫δ² ≤ W²∫δ⁴ + W⁻²`);
* `kUncMeanSum_of_form4 : KUncMeanForm4 → KUncMeanSum` (unclosed estimate, same proof).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ClosedPath
open scoped NNReal ENNReal

/-!
## Generic estimates
-/

section Generic

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- `x² ≤ a²x⁴ + b²` when `1 ≤ ab`. -/
theorem mean_sq_le_four {x a c : ℝ≥0∞} (hac : 1 ≤ a * c) : x ^ 2 ≤ a ^ 2 * x ^ 4 + c ^ 2 := by
  rcases le_total x c with h | h
  · exact (pow_le_pow_left₀ zero_le h 2).trans le_add_self
  · have h1 : 1 ≤ a * x := hac.trans (mul_le_mul_right h a)
    calc x ^ 2 = x ^ 2 * 1 := (mul_one _).symm
      _ ≤ x ^ 2 * (a * x) ^ 2 := by gcongr; exact one_le_pow₀ h1
      _ = a ^ 2 * x ^ 4 := by ring
      _ ≤ a ^ 2 * x ^ 4 + c ^ 2 := le_self_add

/-- One step: `∫|e|⁴ ≤ 8c⁴(K + w⁴)` from `|e| ≤ c(δ + w)` a.e. and `∫δ⁴ ≤ K`. -/
theorem lintegral_pow_four_le_of_dom [IsProbabilityMeasure μ] (e : α → ℂ) (δ : α → ℝ≥0∞)
    {c K w : ℝ≥0∞} (hc : c ≠ ∞) (hδ : ∫⁻ y, δ y ^ 4 ∂μ ≤ K)
    (hdom : ∀ᵐ y ∂μ, ‖e y‖ₑ ≤ c * (δ y + w)) :
    ∫⁻ y, ‖e y‖ₑ ^ 4 ∂μ ≤ 8 * c ^ 4 * (K + w ^ 4) := by
  have hc8 : 8 * c ^ 4 ≠ ∞ := ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hc)
  calc ∫⁻ y, ‖e y‖ₑ ^ 4 ∂μ ≤ ∫⁻ y, (8 * c ^ 4 * δ y ^ 4 + 8 * c ^ 4 * w ^ 4) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hdom] with y hy
        calc ‖e y‖ₑ ^ 4 ≤ (c * (δ y + w)) ^ 4 := pow_le_pow_left₀ zero_le hy 4
          _ = c ^ 4 * (δ y + w) ^ 4 := mul_pow _ _ _
          _ ≤ c ^ 4 * (8 * (δ y ^ 4 + w ^ 4)) := by gcongr; exact add_pow_four_le _ _
          _ = 8 * c ^ 4 * δ y ^ 4 + 8 * c ^ 4 * w ^ 4 := by ring
    _ = 8 * c ^ 4 * ∫⁻ y, δ y ^ 4 ∂μ + 8 * c ^ 4 * w ^ 4 := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ hc8, lintegral_const,
          measure_univ, mul_one]
    _ ≤ 8 * c ^ 4 * K + 8 * c ^ 4 * w ^ 4 := by gcongr
    _ = 8 * c ^ 4 * (K + w ^ 4) := by ring

/-- Power mean over a finite set of steps: `∫(Σ_{i∈S}|e_i|)⁴ ≤ |S|⁴ B` from `∫|e_i|⁴ ≤ B`. -/
theorem lintegral_sum_pow_four_le (S : Finset ℕ) (e : ℕ → α → ℂ)
    (he : ∀ i ∈ S, AEMeasurable (e i) μ) {B : ℝ≥0∞}
    (hB : ∀ i ∈ S, ∫⁻ y, ‖e i y‖ₑ ^ 4 ∂μ ≤ B) :
    ∫⁻ y, (∑ i ∈ S, ‖e i y‖ₑ) ^ 4 ∂μ ≤ (S.card : ℝ≥0∞) ^ 4 * B := by
  calc ∫⁻ y, (∑ i ∈ S, ‖e i y‖ₑ) ^ 4 ∂μ ≤
        ∫⁻ y, (S.card : ℝ≥0∞) ^ 3 * ∑ i ∈ S, ‖e i y‖ₑ ^ 4 ∂μ :=
        lintegral_mono fun y => sum_pow_four_le S _
    _ = (S.card : ℝ≥0∞) ^ 3 * ∑ i ∈ S, ∫⁻ y, ‖e i y‖ₑ ^ 4 ∂μ := by
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)),
          lintegral_finsetSum' S fun i hi => (he i hi).enorm.pow_const 4]
    _ ≤ (S.card : ℝ≥0∞) ^ 3 * ∑ _i ∈ S, B := by
        gcongr with i hi
        exact hB i hi
    _ = (S.card : ℝ≥0∞) ^ 4 * B := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **The summed means from the `L⁴` mean shape** (generic). -/
theorem lintegral_sum_pow_four_le_of_dom [IsProbabilityMeasure μ] (S : Finset ℕ) (e : ℕ → α → ℂ)
    (he : ∀ i ∈ S, AEMeasurable (e i) μ) {c K w : ℝ≥0∞} (hc : c ≠ ∞)
    (hdom : ∀ i ∈ S, ∃ δ : α → ℝ≥0∞, ∫⁻ y, δ y ^ 4 ∂μ ≤ K ∧
      ∀ᵐ y ∂μ, ‖e i y‖ₑ ≤ c * (δ y + w)) :
    ∫⁻ y, (∑ i ∈ S, ‖e i y‖ₑ) ^ 4 ∂μ ≤ (S.card : ℝ≥0∞) ^ 4 * (8 * c ^ 4 * (K + w ^ 4)) := by
  refine lintegral_sum_pow_four_le S e he fun i hi => ?_
  obtain ⟨δ, hδ, hd⟩ := hdom i hi
  exact lintegral_pow_four_le_of_dom (e i) δ hc hδ hd

end Generic

/-!
## The step count and the constant
-/

/-- `#(non-birth steps) ≤ ⌊WT⌋ ≤ W max T 0`. -/
theorem card_genNoBirthSteps_le (s T : ℝ) {np : ℕ} (τ : Fin np → ℝ) (W : ℕ) :
    ((genNoBirthSteps s T τ W).card : ℝ≥0∞) ≤ (W : ℝ≥0∞) * ENNReal.ofReal (max T 0) := by
  have h1 : (genNoBirthSteps s T τ W).card ≤ ⌊(W : ℝ) * T⌋₊ :=
    (Finset.card_filter_le _ _).trans ((Nat.card_Ico _ _).le.trans (Nat.sub_le _ _))
  have h2 : (⌊(W : ℝ) * T⌋₊ : ℝ) ≤ (W : ℝ) * max T 0 :=
    calc (⌊(W : ℝ) * T⌋₊ : ℝ) ≤ (⌊(W : ℝ) * max T 0⌋₊ : ℝ) := by
          exact_mod_cast Nat.floor_le_floor
            (mul_le_mul_of_nonneg_left (le_max_left T 0) (Nat.cast_nonneg W))
      _ ≤ (W : ℝ) * max T 0 := Nat.floor_le (by positivity)
  calc ((genNoBirthSteps s T τ W).card : ℝ≥0∞) ≤ (⌊(W : ℝ) * T⌋₊ : ℝ≥0∞) := by
        exact_mod_cast h1
    _ = ENNReal.ofReal (⌊(W : ℝ) * T⌋₊ : ℝ) := (ENNReal.ofReal_natCast _).symm
    _ ≤ ENNReal.ofReal ((W : ℝ) * max T 0) := ENNReal.ofReal_le_ofReal h2
    _ = (W : ℝ≥0∞) * ENNReal.ofReal (max T 0) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- `W⁴(C/W⁴ + W⁻⁴) = C + 1`. -/
theorem mean_pow_four_scale {W : ℕ} (hW : 1 ≤ W) {C : ℝ} (hC : 0 ≤ C) :
    (W : ℝ≥0∞) ^ 4 * (ENNReal.ofReal (C / (W : ℝ) ^ 4) + ENNReal.ofReal (1 / (W : ℝ)) ^ 4) =
      ENNReal.ofReal (C + 1) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _),
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- The final constant: `|S| ≤ W max T 0` gives `|S|⁴ · 8C⁴(C/W⁴ + W⁻⁴) ≤ 8C⁴(max T 0)⁴(C+1)`. -/
theorem mean_sum_const_le {W : ℕ} (hW : 1 ≤ W) {C T : ℝ} (hC : 0 ≤ C) {n : ℝ≥0∞}
    (hn : n ≤ (W : ℝ≥0∞) * ENNReal.ofReal (max T 0)) :
    n ^ 4 * (8 * ENNReal.ofReal C ^ 4 *
        (ENNReal.ofReal (C / (W : ℝ) ^ 4) + ENNReal.ofReal (1 / (W : ℝ)) ^ 4)) ≤
      ENNReal.ofReal (8 * C ^ 4 * max T 0 ^ 4 * (C + 1)) := by
  calc n ^ 4 * (8 * ENNReal.ofReal C ^ 4 *
        (ENNReal.ofReal (C / (W : ℝ) ^ 4) + ENNReal.ofReal (1 / (W : ℝ)) ^ 4)) ≤
        ((W : ℝ≥0∞) * ENNReal.ofReal (max T 0)) ^ 4 * (8 * ENNReal.ofReal C ^ 4 *
          (ENNReal.ofReal (C / (W : ℝ) ^ 4) + ENNReal.ofReal (1 / (W : ℝ)) ^ 4)) := by gcongr
    _ = 8 * ENNReal.ofReal C ^ 4 * ENNReal.ofReal (max T 0) ^ 4 * ((W : ℝ≥0∞) ^ 4 *
          (ENNReal.ofReal (C / (W : ℝ) ^ 4) + ENNReal.ofReal (1 / (W : ℝ)) ^ 4)) := by ring
    _ = 8 * ENNReal.ofReal C ^ 4 * ENNReal.ofReal (max T 0) ^ 4 * ENNReal.ofReal (C + 1) := by
        rw [mean_pow_four_scale hW hC]
    _ = ENNReal.ofReal (8 * C ^ 4 * max T 0 ^ 4 * (C + 1)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hC,
          ENNReal.ofReal_pow (le_max_right T 0), ENNReal.ofReal_ofNat]

/-!
## The estimates in `L⁴` mean shape
-/

/-- **`KStopMeanForm4`: the mean shape of the closed stopped `𝒦` step in `L⁴`** (with at `p = 4`): at
every non-birth step, a.e. `|E[Z_i | b3Sigma i]| ≤ C(δ_i + W⁻¹)` with `∫δ_i⁴ ≤ C/W⁴`. Reduced to the
closed exact update and the closed jet in `kStopMeanForm4_of_closed`. -/
def KStopMeanForm4 : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ i ∈ genNoBirthSteps s T τ W, ∀ ij : Fin np × Fin np,
      ∃ δ : ProbedPath W np × ℝ → ℝ≥0∞,
        ∫⁻ y, δ y ^ 4 ∂closedLaw b W np ≤ ENNReal.ofReal (C / (W : ℝ) ^ 4) ∧
        ∀ᵐ y ∂closedLaw b W np, ‖kStopMean b E s h τ m R W i (Vs W) ij y‖ₑ ≤
          ENNReal.ofReal C * (δ y + ENNReal.ofReal (1 / (W : ℝ)))

/-- **`KUncMeanForm4`**: the same shape for the unclosed steps
(mean `C(δ₀ + W⁻¹)`, here with unbounded frames absorbed into `δ_i`). -/
def KUncMeanForm4 : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T → ∀ s : ℝ,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ W in atTop, ∀ i ∈ genNoBirthSteps s T τ W, ∀ ij : Fin np × Fin np,
      ∃ δ : ProbedPath W np × ℝ → ℝ≥0∞,
        ∫⁻ y, δ y ^ 4 ∂closedLaw b W np ≤ ENNReal.ofReal (C / (W : ℝ) ^ 4) ∧
        ∀ᵐ y ∂closedLaw b W np, ‖kUncMean b E τ m W i ij y‖ₑ ≤
          ENNReal.ofReal C * (δ y + ENNReal.ofReal (1 / (W : ℝ)))

/-!
## The reductions
-/

/-- **`KStopMeanSum` from the `L⁴` mean shape** ("Minkowski for the summed
means"; here the power mean). -/
theorem kStopMeanSum_of_form4 (hT : KStopMeanForm4) : KStopMeanSum := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C, hC, hev⟩ := hT b E np τ m T s h K Vs hF R
  refine ⟨8 * C ^ 4 * max T 0 ^ 4 * (C + 1), ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with W hW hW1 ij
  refine (lintegral_sum_pow_four_le_of_dom (genNoBirthSteps s T τ W)
    (fun i => kStopMean b E s h τ m R W i (Vs W) ij)
    (fun i _ => (measurable_kStopMean b E s h τ m R W i (Vs W) ij).aemeasurable)
    ENNReal.ofReal_ne_top fun i hi => hW i hi ij).trans ?_
  exact mean_sum_const_le hW1 hC (card_genNoBirthSteps_le s T τ W)

/-- **`KUncMeanSum` from its `L⁴` mean shape.** -/
theorem kUncMeanSum_of_form4 (hT : KUncMeanForm4) : KUncMeanSum := by
  intro b E np τ m T hD s
  obtain ⟨C, hC, hev⟩ := hT b E np τ m T hD s
  refine ⟨8 * C ^ 4 * max T 0 ^ 4 * (C + 1), ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with W hW hW1 ij
  refine (lintegral_sum_pow_four_le_of_dom (genNoBirthSteps s T τ W)
    (fun i => kUncMean b E τ m W i ij)
    (fun i _ => (measurable_kUncMean b E τ m W i ij).aemeasurable)
    ENNReal.ofReal_ne_top fun i hi => hW i hi ij).trans ?_
  exact mean_sum_const_le hW1 hC (card_genNoBirthSteps_le s T τ W)

/-- The stopped `𝒦` increment `b3dX` is `kStopStep`. -/
theorem indicator_b3dX_inr_eq (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij : Fin np × Fin np) :
    (b3Alive b E s h τ m R W j Vs).indicator (b3dX b E s h τ m W j Vs (Sum.inr ij : CIdx K np)) =
      kStopStep b E s h τ m R W j Vs ij := by
  funext y
  rfl

/-- `∫(δ + w)² ≤ 3((C + 2)/W²)` from `∫δ⁴ ≤ C/W⁴`, `w = W⁻¹`. -/
theorem lintegral_add_sq_le_of_four {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {W : ℕ} (hW : 1 ≤ W) {C : ℝ} (hC : 0 ≤ C) (δ : α → ℝ≥0∞)
    (hδ : ∫⁻ y, δ y ^ 4 ∂μ ≤ ENNReal.ofReal (C / (W : ℝ) ^ 4)) :
    ∫⁻ y, (δ y + ENNReal.ofReal (1 / (W : ℝ))) ^ 2 ∂μ ≤
      ENNReal.ofReal (3 * (C + 2) / (W : ℝ) ^ 2) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set a : ℝ≥0∞ := ENNReal.ofReal W
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (W : ℝ))
  have hac : 1 ≤ a * c := by
    rw [← ENNReal.ofReal_mul hW0.le, mul_one_div_cancel hW0.ne', ENNReal.ofReal_one]
  have ha2 : a ^ 2 ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have h2 : ∫⁻ y, δ y ^ 2 ∂μ ≤ a ^ 2 * ENNReal.ofReal (C / (W : ℝ) ^ 4) + c ^ 2 := by
    calc ∫⁻ y, δ y ^ 2 ∂μ ≤ ∫⁻ y, (a ^ 2 * δ y ^ 4 + c ^ 2) ∂μ :=
          lintegral_mono fun y => mean_sq_le_four hac
      _ = a ^ 2 * ∫⁻ y, δ y ^ 4 ∂μ + c ^ 2 := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ha2,
            lintegral_const, measure_univ, mul_one]
      _ ≤ a ^ 2 * ENNReal.ofReal (C / (W : ℝ) ^ 4) + c ^ 2 := by gcongr
  calc ∫⁻ y, (δ y + c) ^ 2 ∂μ ≤ ∫⁻ y, (3 * δ y ^ 2 + 3 * c ^ 2) ∂μ := by
        refine lintegral_mono fun y => ?_
        calc (δ y + c) ^ 2 ≤ 3 * (δ y ^ 2 + c ^ 2) := genMem_add_sq_le _ _
          _ = 3 * δ y ^ 2 + 3 * c ^ 2 := by ring
    _ = 3 * ∫⁻ y, δ y ^ 2 ∂μ + 3 * c ^ 2 := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num),
          lintegral_const, measure_univ, mul_one]
    _ ≤ 3 * (a ^ 2 * ENNReal.ofReal (C / (W : ℝ) ^ 4) + c ^ 2) + 3 * c ^ 2 := by gcongr
    _ = ENNReal.ofReal (3 * (C + 2) / (W : ℝ) ^ 2) := by
        simp only [a, c]
        rw [← ENNReal.ofReal_pow (Nat.cast_nonneg _), ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity), ← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
        congr 1
        field_simp
        ring

/-- **`GenKMeanForm` from the `L⁴` mean shape** (`δ' = δ + W⁻¹`; Jensen in the form
`δ² ≤ W²δ⁴ + W⁻²`). -/
theorem genKMeanForm_of_form4 (hT : KStopMeanForm4) : GenKMeanForm := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C, hC, hev⟩ := hT b E np τ m T s h K Vs hF R
  refine ⟨max C (3 * (C + 2)), le_max_of_le_left hC, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with W hW hW1 j hj ij
  obtain ⟨δ, hδ, hdom⟩ := hW j hj ij
  refine ⟨fun y => δ y + ENNReal.ofReal (1 / (W : ℝ)), ?_, ?_⟩
  · refine (lintegral_add_sq_le_of_four hW1 hC δ hδ).trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
  · filter_upwards [hdom] with y hy
    rw [indicator_b3dX_inr_eq]
    refine hy.trans ?_
    calc ENNReal.ofReal C * (δ y + ENNReal.ofReal (1 / (W : ℝ))) ≤
          ENNReal.ofReal (max C (3 * (C + 2))) * (δ y + ENNReal.ofReal (1 / (W : ℝ))) := by
          gcongr; exact le_max_left _ _
      _ ≤ ENNReal.ofReal (max C (3 * (C + 2))) *
          ((δ y + ENNReal.ofReal (1 / (W : ℝ))) + ENNReal.ofReal (1 / (W : ℝ) ^ 2)) :=
          mul_le_mul_right le_self_add _

end BlockBand.SourceProcess.PhysApprox.B3
