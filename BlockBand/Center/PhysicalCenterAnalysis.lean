module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Generic analysis for the physical center

* `pc_indepFun_prodMk_left`: if `V ⊥ (A, B)` and `A ⊥ B` then `(V, A) ⊥ B` (law-level proof via
  `Measure.prodAssoc_prod`);
* `pc_terminal_energy_le` (**elementary random-energy bound**, expectation case): for a jointly
  measurable `D : Ω × ℝ → ℝ`, a measurable terminal energy `Λ`, `‖Λ - e₀‖_{L⁴} ≤ M` and
  `sup_E ‖D(·,E)‖_{L²} ≤ K`, one has `|E ∫_{e₀}^{Λ} D(E) dE| ≤ 2π M K`. Proof: Tonelli,
  Cauchy–Schwarz at each deterministic energy, Markov (`P(|Λ-e₀| ≥ |E-e₀|) ≤ M⁴/|E-e₀|⁴`), and
  `∫ 2M²/(M²+t²) dt = 2πM`. This is the expectation case `p = 1`, `q = 4 > 2` of the
  random-energy lemma; no `p < 1` is used.
* `pc_lintegral_pow_le_of_eLpNorm`, `pc_sq_integral_le`, `pc_lintegral_mul_sq_le`: conversions
  between `eLpNorm` bounds, lower integrals and real second moments, and the Hölder step
  `‖fg‖₂ ≤ ‖f‖₄ ‖g‖₄`.
* `pc_geom_sum_le`: `Σ_{g ∈ ℤ/n} (ρ^{min((g-e).val,(e-g).val)})² ≤ 2/(1-ρ²)` ("at most two edges
  occur at each positive cyclic distance").
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Interval

/-!
## 1. Independence
-/

/-- If `V ⊥ (A, B)` and `A ⊥ B`, then `(V, A) ⊥ B`. -/
theorem pc_indepFun_prodMk_left {Ω α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {V : Ω → α} {A : Ω → β} {B : Ω → γ} (hV : Measurable V) (hA : Measurable A)
    (hB : Measurable B) (h1 : IndepFun V (fun ω => (A ω, B ω)) μ) (h2 : IndepFun A B μ) :
    IndepFun (fun ω => (V ω, A ω)) B μ := by
  have hVA : IndepFun V A μ := h1.comp measurable_id measurable_fst
  rw [indepFun_iff_map_prod_eq_prod_map_map (hV.prodMk hA).aemeasurable hB.aemeasurable]
  rw [indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable (hA.prodMk hB).aemeasurable] at h1
  rw [indepFun_iff_map_prod_eq_prod_map_map hA.aemeasurable hB.aemeasurable] at h2
  rw [indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hA.aemeasurable] at hVA
  rw [hVA]
  have hfun : (fun ω => ((V ω, A ω), B ω)) =
      (MeasurableEquiv.prodAssoc.symm : α × β × γ ≃ᵐ (α × β) × γ) ∘
        (fun ω => (V ω, (A ω, B ω))) := by
    funext ω; rfl
  rw [hfun, ← Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
    (hV.prodMk (hA.prodMk hB)), h1, h2, ← Measure.prodAssoc_prod,
    Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      MeasurableEquiv.prodAssoc.measurable]
  simp

/-!
## 2. `eLpNorm`, lower integrals and second moments
-/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- An `L^r` bound `‖f‖_r ≤ c` (`r ∈ ℕ`, `r ≥ 1`, `c ≥ 0`) bounds `∫⁻ ‖f‖ₑ^r` by `c^r`. -/
theorem pc_lintegral_pow_le_of_eLpNorm {F : Type*} [NormedAddCommGroup F] {f : Ω → F}
    (hf : AEStronglyMeasurable f μ) {r : ℕ} (hr : 0 < r) {c : ℝ} (hc : 0 ≤ c)
    (h : eLpNorm f (ENNReal.ofReal (r : ℝ)) μ ≤ ENNReal.ofReal c) :
    ∫⁻ x, ‖f x‖ₑ ^ r ∂μ ≤ ENNReal.ofReal (c ^ r) := by
  have hr0 : ENNReal.ofReal (r : ℝ) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact_mod_cast hr
  have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) hr0 ENNReal.ofReal_ne_top hf
  rw [ENNReal.toReal_ofReal (by positivity)] at heq
  have hrr : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hpow : ∫⁻ x, ‖f x‖ₑ ^ r ∂μ = eLpNorm f (ENNReal.ofReal (r : ℝ)) μ ^ r := by
    rw [heq, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hrr,
      ENNReal.rpow_one]
    exact lintegral_congr fun x => (ENNReal.rpow_natCast _ _).symm
  rw [hpow, ENNReal.ofReal_pow hc]
  exact pow_le_pow_left₀ zero_le h r

/-- Real second moment from a lower-integral bound: integrability of `f²` and `∫ f² ≤ V`. -/
theorem pc_sq_integral_le {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {V : ℝ}
    (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal V) :
    Integrable (fun x => f x ^ 2) μ ∧ (∫ x, f x ^ 2 ∂μ) ≤ max V 0 := by
  have henorm : ∀ x, ‖f x ^ 2‖ₑ = ‖f x‖ₑ ^ 2 := fun x => by rw [enorm_pow]
  have hfin : ∫⁻ x, ‖f x ^ 2‖ₑ ∂μ < ⊤ := by
    simp_rw [henorm]; exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hint : Integrable (fun x => f x ^ 2) μ := ⟨hf.pow 2, hfin⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg (f x))
    (hf.pow 2).aemeasurable.aestronglyMeasurable]
  have hle : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ ≤ ENNReal.ofReal V := by
    refine le_trans (le_of_eq ?_) h
    refine lintegral_congr fun x => ?_
    rw [← henorm, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ).toReal ≤ (ENNReal.ofReal V).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = max V 0 := ENNReal.toReal_ofReal'

/-- A real second moment gives the lower-integral bound. -/
theorem pc_lintegral_sq_le_of_integral {f : Ω → ℝ} (hint : Integrable (fun x => f x ^ 2) μ)
    {V : ℝ} (h : (∫ x, f x ^ 2 ∂μ) ≤ V) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal V := by
  have : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => sq_nonneg (f x))]
    refine lintegral_congr fun x => ?_
    rw [← enorm_pow, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [this]
  exact ENNReal.ofReal_le_ofReal h

theorem pc_rpow_four_half (a : ℝ) : (a ^ 4) ^ (1 / 2 : ℝ) = a ^ 2 := by
  rw [show a ^ 4 = (a ^ 2) ^ (2 : ℝ) by rw [Real.rpow_two]; ring, ← Real.rpow_mul (by positivity)]
  norm_num

/-- Hölder: `∫⁻ ‖fg‖ₑ² ≤ (ab)²` from `∫⁻ ‖f‖ₑ⁴ ≤ a⁴`, `∫⁻ ‖g‖ₑ⁴ ≤ b⁴`. -/
theorem pc_lintegral_mul_sq_le {f g : Ω → ℝ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {a b : ℝ}
    (hf4 : ∫⁻ x, ‖f x‖ₑ ^ 4 ∂μ ≤ ENNReal.ofReal (a ^ 4))
    (hg4 : ∫⁻ x, ‖g x‖ₑ ^ 4 ∂μ ≤ ENNReal.ofReal (b ^ 4)) :
    ∫⁻ x, ‖f x * g x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal ((a * b) ^ 2) := by
  have hF : AEMeasurable (fun x => ‖f x‖ₑ ^ 2) μ := hf.enorm.pow_const 2
  have hG : AEMeasurable (fun x => ‖g x‖ₑ ^ 2) μ := hg.enorm.pow_const 2
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hF hG
  have hpow : ∀ (u : ℝ≥0∞), (u ^ 2) ^ (2 : ℝ) = u ^ 4 := fun u => by
    rw [ENNReal.rpow_two]; ring
  simp only [hpow] at hCS
  have h1 : (∫⁻ x, ‖f x‖ₑ ^ 4 ∂μ) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (a ^ 2) := by
    calc _ ≤ (ENNReal.ofReal (a ^ 4)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hf4 (by norm_num)
      _ = ENNReal.ofReal (a ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), pc_rpow_four_half a]
  have h2 : (∫⁻ x, ‖g x‖ₑ ^ 4 ∂μ) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (b ^ 2) := by
    calc _ ≤ (ENNReal.ofReal (b ^ 4)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hg4 (by norm_num)
      _ = ENNReal.ofReal (b ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), pc_rpow_four_half b]
  calc ∫⁻ x, ‖f x * g x‖ₑ ^ 2 ∂μ = ∫⁻ x, ((fun x => ‖f x‖ₑ ^ 2) * fun x => ‖g x‖ₑ ^ 2) x ∂μ := by
        refine lintegral_congr fun x => ?_
        simp only [Pi.mul_apply, enorm_mul, mul_pow]
    _ ≤ _ := hCS
    _ ≤ ENNReal.ofReal (a ^ 2) * ENNReal.ofReal (b ^ 2) := mul_le_mul' h1 h2
    _ = ENNReal.ofReal ((a * b) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf

end Moments

/-!
## 3. The elementary random-energy bound (expectation case)
-/

section Energy

/-- `∫ 2M²/(M² + t²) dt = 2πM`. -/
theorem pc_integral_cauchy {M : ℝ} (hM : 0 < M) :
    Integrable (fun t : ℝ => 2 * (1 + (t / M) ^ 2)⁻¹) ∧
      (∫ t : ℝ, 2 * (1 + (t / M) ^ 2)⁻¹) = 2 * Real.pi * M := by
  have hi : Integrable (fun t : ℝ => (1 + (t / M) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq).comp_div hM.ne'
  refine ⟨hi.const_mul 2, ?_⟩
  rw [integral_const_mul, Measure.integral_comp_div (fun u : ℝ => (1 + u ^ 2)⁻¹) M,
    integral_univ_inv_one_add_sq, abs_of_pos hM, smul_eq_mul]
  ring

theorem pc_cauchy_eq {M t : ℝ} (hM : 0 < M) :
    2 * (1 + (t / M) ^ 2)⁻¹ = 2 * M ^ 2 / (M ^ 2 + t ^ 2) := by
  field_simp

/-- **Elementary random-energy bound** (expectation case of the random-energy lemma, `q = 4`):
`|E ∫_{e₀}^{Λ} D(E) dE| ≤ 2π M K` for any probability law, jointly measurable `D`, measurable
`Λ` (arbitrarily dependent), `‖Λ - e₀‖₄ ≤ M` and `‖D(·, E)‖₂ ≤ K` at every deterministic `E`. -/
theorem pc_terminal_energy_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (D : Ω × ℝ → ℝ) (hD : Measurable D) (Λ : Ω → ℝ)
    (hΛ : Measurable Λ) (e₀ M K : ℝ) (hM : 0 < M) (hK : 0 ≤ K)
    (hterm : ∫⁻ x, ‖Λ x - e₀‖ₑ ^ 4 ∂μ ≤ ENNReal.ofReal (M ^ 4))
    (hDk : ∀ E, ∫⁻ x, ‖D (x, E)‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (K ^ 2)) :
    |∫ x, (∫ E in e₀..Λ x, D (x, E)) ∂μ| ≤ 2 * Real.pi * M * K := by
  -- the region `{(x, E) : E ∈ Ι e₀ (Λ x)}`
  set S : Set (Ω × ℝ) := {z | min e₀ (Λ z.1) < z.2 ∧ z.2 ≤ max e₀ (Λ z.1)} with hSdef
  have hS : MeasurableSet S := by
    have hm1 : Measurable fun z : Ω × ℝ => min e₀ (Λ z.1) :=
      measurable_const.min (hΛ.comp measurable_fst)
    have hm2 : Measurable fun z : Ω × ℝ => max e₀ (Λ z.1) :=
      measurable_const.max (hΛ.comp measurable_fst)
    exact (measurableSet_lt hm1 measurable_snd).inter (measurableSet_le measurable_snd hm2)
  set f : Ω × ℝ → ℝ≥0∞ := S.indicator (fun z => ‖D z‖ₑ) with hfdef
  have hf : Measurable f := hD.enorm.indicator hS
  -- pointwise: the norm of the oriented integral is bounded by the lower integral over `Ι`
  have hpt : ∀ x, ENNReal.ofReal ‖∫ E in e₀..Λ x, D (x, E)‖ ≤ ∫⁻ E, f (x, E) := by
    intro x
    have hmeasE : Measurable fun E => D (x, E) := hD.comp (measurable_const.prodMk measurable_id)
    calc ENNReal.ofReal ‖∫ E in e₀..Λ x, D (x, E)‖
        ≤ ENNReal.ofReal (∫ E in Ι e₀ (Λ x), ‖D (x, E)‖) :=
          ENNReal.ofReal_le_ofReal (intervalIntegral.norm_integral_le_integral_norm_uIoc)
      _ ≤ ∫⁻ E in Ι e₀ (Λ x), ‖D (x, E)‖ₑ := by
          rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            hmeasE.norm.aestronglyMeasurable]
          refine ENNReal.ofReal_toReal_le.trans (le_of_eq ?_)
          exact lintegral_congr fun E => ofReal_norm _
      _ = ∫⁻ E, f (x, E) := by
          rw [← lintegral_indicator measurableSet_uIoc]
          refine lintegral_congr fun E => ?_
          simp only [hfdef, Set.indicator, hSdef, Set.mem_ofPred_eq, Set.uIoc, Set.mem_Ioc]
          congr 1
  -- Cauchy–Schwarz and Markov at each energy
  have hCauchy : ∀ E, ∫⁻ x, f (x, E) ∂μ ≤
      ENNReal.ofReal K * ENNReal.ofReal (2 * M ^ 2 / (M ^ 2 + (E - e₀) ^ 2)) := by
    intro E
    set A : Set Ω := {x | min e₀ (Λ x) < E ∧ E ≤ max e₀ (Λ x)} with hAdef
    have hA : MeasurableSet A :=
      (measurableSet_lt (measurable_const.min hΛ) measurable_const).inter
        (measurableSet_le measurable_const (measurable_const.max hΛ))
    have hfx : (fun x => f (x, E)) = (fun x => ‖D (x, E)‖ₑ) * A.indicator 1 := by
      funext x
      simp only [hfdef, Set.indicator, hSdef, hAdef, Set.mem_ofPred_eq, Pi.mul_apply, Pi.one_apply]
      split_ifs <;> simp
    have hmeasE : Measurable fun x => D (x, E) := hD.comp (measurable_id.prodMk measurable_const)
    have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
      hmeasE.enorm.aemeasurable ((measurable_one.indicator hA).aemeasurable)
    rw [← hfx] at hCS
    have hI : ∫⁻ x, (A.indicator (1 : Ω → ℝ≥0∞) x) ^ (2 : ℝ) ∂μ = μ A := by
      have : (fun x => (A.indicator (1 : Ω → ℝ≥0∞) x) ^ (2 : ℝ)) = A.indicator 1 := by
        funext x
        by_cases hx : x ∈ A <;> simp [Set.indicator, hx]
      rw [this, lintegral_indicator_one hA]
    rw [hI] at hCS
    have hD2 : (∫⁻ x, ‖D (x, E)‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal K := by
      have h := hDk E
      simp only [← ENNReal.rpow_two] at h
      calc _ ≤ (ENNReal.ofReal (K ^ 2)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
        _ = ENNReal.ofReal K := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            show K ^ 2 = K ^ (2 : ℝ) by rw [Real.rpow_two], ← Real.rpow_mul hK]
          norm_num
    -- the measure of `A`
    set y : ℝ := 2 * M ^ 2 / (M ^ 2 + (E - e₀) ^ 2) with hydef
    have hy0 : 0 ≤ y := by positivity
    have hAmeas : μ A ≤ ENNReal.ofReal (y ^ 2) := by
      by_cases ht : (E - e₀) ^ 2 ≤ M ^ 2
      · have hy1 : 1 ≤ y := by
          rw [hydef, le_div_iff₀ (by positivity)]; linarith
        calc μ A ≤ 1 := prob_le_one
          _ ≤ ENNReal.ofReal (y ^ 2) := by
            rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (one_le_pow₀ hy1)
      · replace ht := lt_of_not_ge ht
        set t : ℝ := |E - e₀| with htdef
        have ht2 : t ^ 2 = (E - e₀) ^ 2 := sq_abs _
        have htpos : 0 < t := by
          rw [htdef, abs_pos]; intro h0; rw [h0] at ht; nlinarith [sq_nonneg M]
        have hsub : A ⊆ {x | ENNReal.ofReal (t ^ 4) ≤ ‖Λ x - e₀‖ₑ ^ 4} := by
          intro x hx
          simp only [hAdef, Set.mem_ofPred_eq] at hx
          simp only [Set.mem_ofPred_eq]
          have hle : t ≤ |Λ x - e₀| := by
            rw [htdef]
            rcases le_total e₀ (Λ x) with h | h
            · rw [min_eq_left h, max_eq_right h] at hx
              rw [abs_of_pos (by linarith [hx.1]), abs_of_nonneg (by linarith)]; linarith [hx.2]
            · rw [min_eq_right h, max_eq_left h] at hx
              rw [abs_of_nonpos (by linarith [hx.2]), abs_of_nonpos (by linarith)]
              linarith [hx.1]
          rw [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ htpos.le hle 4)
        have hΛm : Measurable fun x => ‖Λ x - e₀‖ₑ ^ 4 :=
          ((hΛ.sub (measurable_const (a := e₀))).enorm.pow_const 4)
        have hmk := mul_meas_ge_le_lintegral₀ hΛm.aemeasurable (ENNReal.ofReal (t ^ 4)) (μ := μ)
        have ht4 : 0 < t ^ 4 := by positivity
        have hmA : μ A ≤ ENNReal.ofReal (M ^ 4) / ENNReal.ofReal (t ^ 4) := by
          rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using ht4)) (Or.inl ENNReal.ofReal_ne_top),
            mul_comm]
          have hmono : ENNReal.ofReal (t ^ 4) * μ A ≤
              ENNReal.ofReal (t ^ 4) * μ {x | ENNReal.ofReal (t ^ 4) ≤ ‖Λ x - e₀‖ₑ ^ 4} := by
            gcongr
          exact (hmono.trans hmk).trans hterm
        refine hmA.trans ?_
        rw [← ENNReal.ofReal_div_of_pos ht4]
        refine ENNReal.ofReal_le_ofReal ?_
        have hyge : M ^ 2 / t ^ 2 ≤ y := by
          have hEpos : 0 < (E - e₀) ^ 2 := by nlinarith [sq_nonneg M]
          rw [hydef, ht2, div_le_div_iff₀ hEpos (by positivity)]
          nlinarith [sq_nonneg M, sq_nonneg (E - e₀)]
        calc M ^ 4 / t ^ 4 = (M ^ 2 / t ^ 2) ^ 2 := by ring
          _ ≤ y ^ 2 := pow_le_pow_left₀ (by positivity) hyge 2
    have hAy : μ A ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal y := by
      calc _ ≤ (ENNReal.ofReal (y ^ 2)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hAmeas (by norm_num)
        _ = ENNReal.ofReal y := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            show y ^ 2 = y ^ (2 : ℝ) by rw [Real.rpow_two], ← Real.rpow_mul hy0]
          norm_num
    exact hCS.trans (mul_le_mul' hD2 hAy)
  -- integrate in energy
  obtain ⟨hint, hval⟩ := pc_integral_cauchy hM
  have hEint : ∫⁻ E, ENNReal.ofReal (2 * M ^ 2 / (M ^ 2 + (E - e₀) ^ 2)) =
      ENNReal.ofReal (2 * Real.pi * M) := by
    have h1 : (fun E : ℝ => ENNReal.ofReal (2 * M ^ 2 / (M ^ 2 + (E - e₀) ^ 2))) =
        fun E => (fun t : ℝ => ENNReal.ofReal (2 * (1 + (t / M) ^ 2)⁻¹)) (E + -e₀) := by
      funext E; dsimp only; rw [pc_cauchy_eq hM, sub_eq_add_neg]
    rw [h1, lintegral_add_right_eq_self (fun t : ℝ => ENNReal.ofReal (2 * (1 + (t / M) ^ 2)⁻¹)),
      ← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun t => by positivity), hval]
  have htotal : ∫⁻ x, ENNReal.ofReal ‖∫ E in e₀..Λ x, D (x, E)‖ ∂μ ≤
      ENNReal.ofReal (2 * Real.pi * M * K) := by
    calc ∫⁻ x, ENNReal.ofReal ‖∫ E in e₀..Λ x, D (x, E)‖ ∂μ ≤ ∫⁻ x, (∫⁻ E, f (x, E)) ∂μ :=
          lintegral_mono hpt
      _ = ∫⁻ E, ∫⁻ x, f (x, E) ∂μ :=
          lintegral_lintegral_swap (f := fun x E => f (x, E)) (by
            change AEMeasurable f _; exact hf.aemeasurable)
      _ ≤ ∫⁻ E, ENNReal.ofReal K * ENNReal.ofReal (2 * M ^ 2 / (M ^ 2 + (E - e₀) ^ 2)) :=
          lintegral_mono hCauchy
      _ = ENNReal.ofReal K * ENNReal.ofReal (2 * Real.pi * M) := by
          rw [lintegral_const_mul _ (by fun_prop), hEint]
      _ = ENNReal.ofReal (2 * Real.pi * M * K) := by
          rw [← ENNReal.ofReal_mul hK]; ring_nf
  calc |∫ x, (∫ E in e₀..Λ x, D (x, E)) ∂μ| = ‖∫ x, (∫ E in e₀..Λ x, D (x, E)) ∂μ‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ (∫⁻ x, ENNReal.ofReal ‖∫ E in e₀..Λ x, D (x, E)‖ ∂μ).toReal :=
        norm_integral_le_lintegral_norm _
    _ ≤ (ENNReal.ofReal (2 * Real.pi * M * K)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top htotal
    _ = 2 * Real.pi * M * K := ENNReal.toReal_ofReal (by positivity)

end Energy

/-!
## 4. The cyclic geometric row sum
-/

/-- `Σ_{g ∈ ℤ/n} (ρ^{min((g-e).val, (e-g).val)})² ≤ 2/(1-ρ²)`. -/
theorem pc_geom_sum_le (n : ℕ) [NeZero n] (e : ZMod n) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    ∑ g : ZMod n, (ρ ^ min (g - e).val (e - g).val) ^ 2 ≤ 2 / (1 - ρ ^ 2) := by
  set r : ℝ := ρ ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr]; nlinarith
  have hpt : ∀ g : ZMod n, (ρ ^ min (g - e).val (e - g).val) ^ 2 ≤
      r ^ (g - e).val + r ^ (e - g).val := by
    intro g
    rw [← pow_mul, mul_comm, pow_mul]
    rcases le_total (g - e).val (e - g).val with h | h
    · rw [min_eq_left h]; linarith [pow_nonneg hr0 (e - g).val]
    · rw [min_eq_right h]; linarith [pow_nonneg hr0 (g - e).val]
  have hsum : ∀ φ : ZMod n → ZMod n, Function.Injective φ →
      ∑ g : ZMod n, r ^ (φ g).val ≤ 1 / (1 - r) := by
    intro φ hφ
    have hinj : Set.InjOn (fun g : ZMod n => (φ g).val) (Finset.univ : Finset (ZMod n)) :=
      fun a _ b _ hab => hφ (ZMod.val_injective n hab)
    rw [← Finset.sum_image (f := fun j : ℕ => r ^ j) hinj, one_div,
      ← tsum_geometric_of_lt_one hr0 hr1]
    exact Summable.sum_le_tsum _ (fun j _ => pow_nonneg hr0 j) (summable_geometric_of_lt_one hr0 hr1)
  have h1' := hsum (fun g => g - e) (sub_left_injective)
  have h2' := hsum (fun g => e - g) (sub_right_injective)
  calc ∑ g : ZMod n, (ρ ^ min (g - e).val (e - g).val) ^ 2
      ≤ ∑ g : ZMod n, (r ^ (g - e).val + r ^ (e - g).val) := Finset.sum_le_sum fun g _ => hpt g
    _ = ∑ g : ZMod n, r ^ (g - e).val + ∑ g : ZMod n, r ^ (e - g).val := Finset.sum_add_distrib
    _ ≤ 1 / (1 - r) + 1 / (1 - r) := add_le_add h1' h2'
    _ = 2 / (1 - ρ ^ 2) := by rw [hr]; ring

end BlockBand.Center
