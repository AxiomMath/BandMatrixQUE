module

public import BlockBand.SourceProcess.FullSourceGenerator.GenTools

/-!
# The tested increment at fixed `W`, abstractly

Abstract (no random-band content): a filtration `G`,
an adapted complex sequence `X_j`, predictable drifts `g_j` with weight `s` (`= W⁻¹`), events
`A_j ∈ G_j` (`{j < σ_K}`), the stopped increments `D_j = 1_{A_j}(X_{j+1} - X_j)` and the drift
errors `e_j = 1_{A_j}(E[D_j|G_j] - s g_j)` (`driftErr`). For a `G_{j₀}`-measurable test `ξ`
bounded by `B_K` on `A_{j₀}` and a bad event `Bc` off which every `A_j`, `j₀ ≤ j < j₁`, holds:

**`norm_integral_tested_le`**: for all `λ, κ > 0`,
`‖E[ξ(X_{j₁} - X_{j₀} - Σ s g_j)]‖ ≤ B_K Σ E|e_j| + λ(E|M|² + E|mart|²) + μ(Bc)/(4λκ) +
κE|ξ|⁴/(4λ)`, `mart = Σ(D_j - E[D_j|G_j])`; and `lintegral_sq_mart_D_le`:
`E|mart|² ≤ 4ΣE|D_j|²`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MeasureTheory Finset
open scoped ENNReal

/-- Young: `i x (a + b) ≤ λ(a² + b²) + i/(4λκ) + κx⁴/(4λ)` for `i ∈ {0,1}`. -/
theorem young_tested {i x a b lam kap : ℝ} (hi : i = 0 ∨ i = 1) (_hx : 0 ≤ x) (_ha : 0 ≤ a)
    (_hb : 0 ≤ b) (hl : 0 < lam) (hk : 0 < kap) :
    i * (x * (a + b)) ≤ lam * (a ^ 2 + b ^ 2) + i / (4 * lam * kap) + kap / (4 * lam) * x ^ 4 := by
  have h1 : x * (a + b) ≤ lam / 2 * (a + b) ^ 2 + x ^ 2 / (2 * lam) := by
    have h0 : 0 ≤ (lam * (a + b) - x) ^ 2 / (2 * lam) := by positivity
    have e : lam / 2 * (a + b) ^ 2 + x ^ 2 / (2 * lam) - x * (a + b) =
        (lam * (a + b) - x) ^ 2 / (2 * lam) := by field_simp; ring
    linarith
  have h2 : x ^ 2 ≤ 1 / (2 * kap) + kap / 2 * x ^ 4 := by
    have h0 : 0 ≤ (kap * x ^ 2 - 1) ^ 2 / (2 * kap) := by positivity
    have e : 1 / (2 * kap) + kap / 2 * x ^ 4 - x ^ 2 = (kap * x ^ 2 - 1) ^ 2 / (2 * kap) := by
      field_simp; ring
    linarith
  have h3 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  rcases hi with rfl | rfl
  · simp only [zero_mul, zero_div, add_zero]; positivity
  · simp only [one_mul]
    calc x * (a + b) ≤ lam / 2 * (a + b) ^ 2 + x ^ 2 / (2 * lam) := h1
      _ ≤ lam / 2 * (2 * (a ^ 2 + b ^ 2)) + (1 / (2 * kap) + kap / 2 * x ^ 4) / (2 * lam) := by
          gcongr
      _ = _ := by field_simp; ring

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  (G : ℕ → MeasurableSpace Ω) (X g : ℕ → Ω → ℂ) (A : ℕ → Set Ω) (s : ℂ)

/-- The stopped increment `1_{A_j}(X_{j+1} - X_j)`. -/
def stopInc (j : ℕ) : Ω → ℂ := (A j).indicator fun ω => X (j + 1) ω - X j ω

/-- The drift error `1_{A_j}(E[D_j|G_j] - s g_j)`. -/
def stopErr {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) (G : ℕ → MeasurableSpace Ω)
    (X g : ℕ → Ω → ℂ) (A : ℕ → Set Ω) (s : ℂ) (j : ℕ) : Ω → ℂ :=
  (A j).indicator fun ω => μ[stopInc X A j | G j] ω - s * g j ω

theorem sum_Ico_telescope_C (j₀ j₁ : ℕ) (h : j₀ ≤ j₁) (ω : Ω) :
    ∑ j ∈ Ico j₀ j₁, (X (j + 1) ω - X j ω) = X j₁ ω - X j₀ ω := by
  induction j₁, h using Nat.le_induction with
  | base => simp
  | succ n hn ih => rw [Finset.sum_Ico_succ_top hn, ih]; ring

variable (hG : Monotone G) (hle : ∀ j, G j ≤ m0) (hXm : ∀ j, StronglyMeasurable[G j] (X j))
  (hX2 : ∀ j, MemLp (X j) 2 μ) (hA : ∀ j, MeasurableSet[G j] (A j))

include hG hle hXm hX2 hA in
theorem stopInc_meas (j : ℕ) : StronglyMeasurable[G (j + 1)] (stopInc X A j) :=
  ((hXm (j + 1)).sub ((hXm j).mono (hG (Nat.le_succ j)))).indicator
    (hG (Nat.le_succ j) _ (hA j))

include hG hle hXm hX2 hA in
theorem stopInc_memLp (j : ℕ) : MemLp (stopInc X A j) 2 μ :=
  ((hX2 (j + 1)).sub (hX2 j)).indicator (hle j _ (hA j)).nullMeasurableSet

include hG hle hXm hX2 hA in
/-- `E|Σ(D_j - E[D_j|G_j])|² ≤ 4ΣE|D_j|²`. -/
theorem lintegral_sq_mart_D_le (a n : ℕ) :
    ∫⁻ ω, ‖∑ j ∈ Ico a n, (stopInc X A j ω - μ[stopInc X A j | G j] ω)‖ₑ ^ 2 ∂μ ≤
      4 * ∑ j ∈ Ico a n, ∫⁻ ω, ‖stopInc X A j ω‖ₑ ^ 2 ∂μ :=
  lintegral_sq_mart_le G hG hle _ (stopInc_meas G X A hG hle hXm hX2 hA)
    (stopInc_memLp G X A hG hle hXm hX2 hA) a n

include hG hle hXm hX2 hA in
/-- **The tested increment at fixed `W`.** -/
theorem norm_integral_tested_le (hgm : ∀ j, StronglyMeasurable[G j] (g j))
    (hg2 : ∀ j, MemLp (g j) 2 μ) {j₀ j₁ : ℕ} (hj : j₀ ≤ j₁)
    (hAj₀ : ∀ j ∈ Ico j₀ j₁, A j ⊆ A j₀) {Bc : Set Ω} (hBc : MeasurableSet Bc)
    (hB : ∀ ω, ω ∉ Bc → ∀ j ∈ Ico j₀ j₁, ω ∈ A j) {ξ : Ω → ℂ}
    (hξm : StronglyMeasurable[G j₀] ξ) (hξ2 : MemLp ξ 2 μ) {BK : ℝ} (hBK : 0 ≤ BK)
    (hξK : ∀ᵐ ω ∂μ, ω ∈ A j₀ → ‖ξ ω‖ ≤ BK) {lam kap : ℝ} (hl : 0 < lam) (hk : 0 < kap) :
    ‖∫ ω, ξ ω * (X j₁ ω - X j₀ ω - ∑ j ∈ Ico j₀ j₁, s * g j ω) ∂μ‖ₑ ≤
      ENNReal.ofReal BK * ∑ j ∈ Ico j₀ j₁, ∫⁻ ω, ‖stopErr μ G X g A s j ω‖ₑ ∂μ +
      ENNReal.ofReal lam * (∫⁻ ω, ‖X j₁ ω - X j₀ ω - ∑ j ∈ Ico j₀ j₁, s * g j ω‖ₑ ^ 2 ∂μ +
        ∫⁻ ω, ‖∑ j ∈ Ico j₀ j₁, (stopInc X A j ω - μ[stopInc X A j | G j] ω)‖ₑ ^ 2 ∂μ) +
      ENNReal.ofReal (1 / (4 * lam * kap)) * μ Bc +
      ENNReal.ofReal (kap / (4 * lam)) * ∫⁻ ω, ‖ξ ω‖ₑ ^ 4 ∂μ := by
  set D := stopInc X A
  set e := stopErr μ G X g A s
  set M : Ω → ℂ := fun ω => X j₁ ω - X j₀ ω - ∑ j ∈ Ico j₀ j₁, s * g j ω
  set mart : Ω → ℂ := fun ω => ∑ j ∈ Ico j₀ j₁, (D j ω - μ[D j | G j] ω)
  have hD2 := stopInc_memLp G X A hG hle hXm hX2 hA
  have hc2 : ∀ j, MemLp (μ[D j | G j]) 2 μ := fun j => (hD2 j).condExp one_le_two
  have hM2 : MemLp M 2 μ := ((hX2 j₁).sub (hX2 j₀)).sub
    (memLp_finsetSum _ fun j _ => (hg2 j).const_mul s)
  have hmart2 : MemLp mart 2 μ := memLp_finsetSum _ fun j _ => (hD2 j).sub (hc2 j)
  -- the martingale part is orthogonal to `ξ`
  have horth : ∫ ω, ξ ω * mart ω ∂μ = 0 := by
    simp only [mart, Finset.mul_sum]
    rw [integral_finsetSum (f := fun j ω => ξ ω * (D j ω - μ[D j | G j] ω)) _
      fun j _ => integrable_mul_of_memLp hξ2 ((hD2 j).sub (hc2 j))]
    refine Finset.sum_eq_zero fun j hj => ?_
    exact integral_mul_sub_condExp_C (hle j)
      ((hξm.mono (hG (Finset.mem_Ico.mp hj).1)).aestronglyMeasurable)
      (integrable_mul_of_memLp hξ2 (hD2 j)) (memLp_one_iff_integrable.mp
        ((hD2 j).mono_exponent one_le_two))
  have hsplit : ∫ ω, ξ ω * M ω ∂μ = ∫ ω, ξ ω * (M ω - mart ω) ∂μ := by
    have h := integral_sub (integrable_mul_of_memLp hξ2 hM2) (integrable_mul_of_memLp hξ2 hmart2)
    simp only [← mul_sub] at h
    rw [h, horth, sub_zero]
  -- pointwise bound
  have hpt : ∀ ω, ‖ξ ω * (M ω - mart ω)‖ ≤ ‖ξ ω‖ * ∑ j ∈ Ico j₀ j₁, ‖e j ω‖ +
      Bc.indicator (fun _ => (1 : ℝ)) ω * (‖ξ ω‖ * (‖M ω‖ + ‖mart ω‖)) := by
    intro ω
    rw [norm_mul]
    by_cases hω : ω ∈ Bc
    · rw [Set.indicator_of_mem hω, one_mul]
      have : ‖M ω - mart ω‖ ≤ ‖M ω‖ + ‖mart ω‖ := norm_sub_le _ _
      nlinarith [norm_nonneg (ξ ω), Finset.sum_nonneg fun j (_ : j ∈ Ico j₀ j₁) =>
        norm_nonneg (e j ω)]
    · rw [Set.indicator_of_notMem hω, zero_mul, add_zero]
      have hAll := hB ω hω
      have heq : M ω - mart ω = ∑ j ∈ Ico j₀ j₁, e j ω := by
        simp only [M, mart, e, stopErr, D, stopInc]
        rw [← sum_Ico_telescope_C X j₀ j₁ hj ω, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j hjm => ?_
        rw [Set.indicator_of_mem (hAll j hjm), Set.indicator_of_mem (hAll j hjm)]
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
  have hpe : ∀ᵐ ω ∂μ, ‖ξ ω‖ * ∑ j ∈ Ico j₀ j₁, ‖e j ω‖ ≤ BK * ∑ j ∈ Ico j₀ j₁, ‖e j ω‖ := by
    filter_upwards [hξK] with ω hω
    by_cases h0 : ω ∈ A j₀
    · exact mul_le_mul_of_nonneg_right (hω h0) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    · have : ∑ j ∈ Ico j₀ j₁, ‖e j ω‖ = 0 := Finset.sum_eq_zero fun j hjm => by
        simp only [e, stopErr]
        rw [Set.indicator_of_notMem (fun h => h0 (hAj₀ j hjm h)), norm_zero]
      rw [this, mul_zero, mul_zero]
  have hyo : ∀ ω, Bc.indicator (fun _ => (1 : ℝ)) ω * (‖ξ ω‖ * (‖M ω‖ + ‖mart ω‖)) ≤
      lam * (‖M ω‖ ^ 2 + ‖mart ω‖ ^ 2) + Bc.indicator (fun _ => (1 : ℝ)) ω / (4 * lam * kap) +
        kap / (4 * lam) * ‖ξ ω‖ ^ 4 := by
    intro ω
    refine young_tested ?_ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hl hk
    by_cases hω : ω ∈ Bc
    · right; exact Set.indicator_of_mem hω _
    · left; exact Set.indicator_of_notMem hω _
  -- integrate
  have hm0 : ∀ j, StronglyMeasurable[m0] (X j) := fun j => (hXm j).mono (hle j)
  have hem : ∀ j, Measurable fun ω => ‖e j ω‖ₑ := fun j =>
    (((stronglyMeasurable_condExp.sub ((hgm j).const_mul s)).indicator (hA j)).mono
      (hle j)).measurable.enorm
  have hMm : Measurable fun ω => ‖M ω‖ₑ := (((hm0 j₁).sub (hm0 j₀)).sub
    (Finset.stronglyMeasurable_fun_sum _ fun j _ =>
      ((hgm j).mono (hle j)).const_mul s)).measurable.enorm
  have hmm : Measurable fun ω => ‖mart ω‖ₑ := (Finset.stronglyMeasurable_fun_sum _ fun j _ =>
    ((stopInc_meas G X A hG hle hXm hX2 hA j).mono (hle (j + 1))).sub
      (stronglyMeasurable_condExp.mono (hle j))).measurable.enorm
  have hξe : Measurable fun ω => ‖ξ ω‖ₑ := (hξm.mono (hle j₀)).measurable.enorm
  have hIm : Measurable (Bc.indicator fun _ => (1 : ℝ≥0∞)) := measurable_const.indicator hBc
  have hfin : ∀ᵐ ω ∂μ, ‖ξ ω * (M ω - mart ω)‖ₑ ≤
      ENNReal.ofReal BK * ∑ j ∈ Ico j₀ j₁, ‖e j ω‖ₑ +
      ENNReal.ofReal lam * (‖M ω‖ₑ ^ 2 + ‖mart ω‖ₑ ^ 2) +
      ENNReal.ofReal (1 / (4 * lam * kap)) * Bc.indicator (fun _ => (1 : ℝ≥0∞)) ω +
      ENNReal.ofReal (kap / (4 * lam)) * ‖ξ ω‖ₑ ^ 4 := by
    filter_upwards [hpe] with ω hω
    have hi : ENNReal.ofReal (Bc.indicator (fun _ => (1 : ℝ)) ω) =
        Bc.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
      by_cases h : ω ∈ Bc <;> simp [h]
    have hi0 : 0 ≤ Bc.indicator (fun _ => (1 : ℝ)) ω := Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    have hr : ‖ξ ω * (M ω - mart ω)‖ ≤ BK * ∑ j ∈ Ico j₀ j₁, ‖e j ω‖ +
        lam * (‖M ω‖ ^ 2 + ‖mart ω‖ ^ 2) + 1 / (4 * lam * kap) * Bc.indicator (fun _ => (1 : ℝ)) ω +
        kap / (4 * lam) * ‖ξ ω‖ ^ 4 := by
      have := hyo ω
      have := hpt ω
      rw [div_eq_mul_one_div (Bc.indicator (fun _ => (1 : ℝ)) ω), mul_comm
        (Bc.indicator (fun _ => (1 : ℝ)) ω)] at *
      linarith
    rw [← ofReal_norm]
    refine (ENNReal.ofReal_le_ofReal hr).trans (le_of_eq ?_)
    have hs0 : 0 ≤ ∑ j ∈ Ico j₀ j₁, ‖e j ω‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity)
      (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul hBK, ENNReal.ofReal_mul hl.le, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _,
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
      ofReal_norm, ofReal_norm, hi]
    simp only [ofReal_norm]
  rw [hsplit]
  refine (enorm_integral_le_lintegral_enorm _).trans ((lintegral_mono_ae hfin).trans (le_of_eq ?_))
  rw [lintegral_add_right' _ ((hξe.pow_const 4).const_mul _).aemeasurable,
    lintegral_add_right' _ (hIm.const_mul _).aemeasurable,
    lintegral_add_left ((Finset.measurable_fun_sum _ fun j _ => hem j).const_mul _),
    lintegral_const_mul _ (Finset.measurable_fun_sum _ fun j _ => hem j),
    lintegral_finsetSum _ fun j _ => hem j,
    lintegral_const_mul (f := fun ω => ‖M ω‖ₑ ^ 2 + ‖mart ω‖ₑ ^ 2) _
      ((hMm.pow_const 2).add (hmm.pow_const 2)),
    lintegral_add_left (hMm.pow_const 2), lintegral_const_mul _ hIm, lintegral_indicator_const hBc, one_mul,
    lintegral_const_mul _ (hξe.pow_const 4)]

end BlockBand.SourceProcess.FullSourceGenerator
