module

public import BlockBand.Critical.EntireLaw.CollarGaussian

/-!
# The entire law: the finite-width collar bound

`measure_collarDiff_le`: for every finite realization, real `E`, nonnegative profiles, entries
`(a, c)`, `ε, η > 0` and `K`, with `δ = 2^{-(K+1)}`, `t = ε²/4`, `L_K = 1 + 2(C/√c)(K+1)`:
`P(|(ζ^*Rζ - ζ_o^*Rζ_o)_{ac}| > ε) ≤ (C/√c) N 2δ
  + W⁻²‖Q_a‖ (3 N L_K/n)/η + W⁻²‖Q_c‖ N L_K/(t/η) + W⁻²‖Q_c‖ (3 N L_K/n)/η + W⁻²‖Q_a‖ N L_K/(t/η)`.
Proof: off `{H not Hermitian} ∪ {an eigenvalue within δ of E}`, Cauchy–Schwarz
(`norm_sq_dotProduct_inv_le`) bounds each collar term by a product of two `|R|`-forms; Markov on
each form with the expectations of `CollarGaussian`/`CollarCount` (collar forms carry `3/n`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal

variable {p : Parameters}

/-!
## 1. Probe coefficients
-/

/-- Coefficient of the probe `ζ = W⁻¹ Q^{1/2} g` at the site `y`. -/
def probeCoeff (p : Parameters) (Q : C(Torus, ℝ)) (y : p.Site) : ℂ :=
  (((p.W : ℝ)⁻¹ * Real.sqrt (Q (p.ringProfilePoint y.1)) : ℝ) : ℂ)

theorem ringProbeVector_eq (Q : C(Torus, ℝ)) (g : p.Site → ℂ) :
    ringProbeVector p Q g = fun y => probeCoeff p Q y * g y := rfl

theorem omitCollar_ringProbeVector_eq (Q : C(Torus, ℝ)) (g : p.Site → ℂ) :
    omitCollar p (ringProbeVector p Q g) =
      fun y => (if IsCollarBlock p y.1 then 0 else probeCoeff p Q y) * g y := by
  funext y
  unfold omitCollar
  split_ifs <;> simp [ringProbeVector_eq]

theorem collarPart_ringProbeVector_eq (Q : C(Torus, ℝ)) (g : p.Site → ℂ) :
    collarPart p (ringProbeVector p Q g) =
      fun y => (if IsCollarBlock p y.1 then probeCoeff p Q y else 0) * g y := by
  funext y
  unfold collarPart
  split_ifs <;> simp [ringProbeVector_eq]

theorem norm_sq_probeCoeff_le {Q : C(Torus, ℝ)} (hQ : ∀ x, 0 ≤ Q x) (y : p.Site) :
    ‖probeCoeff p Q y‖ ^ 2 ≤ ((p.W : ℝ) ^ 2)⁻¹ * ‖Q‖ := by
  unfold probeCoeff
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (hQ _), inv_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact (le_abs_self _).trans (Q.norm_coe_le_norm _)

/-!
## 2. Expected masses of `|R|`
-/

theorem integrable_totalAbsMass (model : p.GaussianRingModel) (E : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (totalAbsMass p E δ) (model.law : Measure p.SiteMatrix) := by
  refine Integrable.of_bound (measurable_totalAbsMass E δ).aestronglyMeasurable
    (p.N * δ⁻¹) (Filter.Eventually.of_forall fun H => ?_)
  rw [Real.norm_of_nonneg (totalAbsMass_nonneg E δ H)]
  exact totalAbsMass_le E hδ H

/-- The constant `L_K = 1 + 2 (C/√c)(K+1)` of the dyadic trace bound. -/
def traceConst (p : Parameters) (source : BlockBand.External.PSSS.SourceContract.{0}) (K : ℕ) :
    ℝ :=
  1 + 2 * (source.C / Real.sqrt p.c) * (K + 1)

theorem traceConst_nonneg (source : BlockBand.External.PSSS.SourceContract.{0}) (K : ℕ) :
    0 ≤ traceConst p source K := by
  have := source.C_pos
  unfold traceConst
  positivity

theorem lintegral_totalAbsMass_le (model : p.GaussianRingModel)
    (source : BlockBand.External.PSSS.SourceContract.{0}) (E : ℝ) (K : ℕ) :
    ∫⁻ H, ENNReal.ofReal (totalAbsMass p E ((1 / 2 : ℝ) ^ (K + 1)) H)
        ∂(model.law : Measure p.SiteMatrix) ≤
      ENNReal.ofReal (p.N * traceConst p source K) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_totalAbsMass model E (by positivity))
    (Filter.Eventually.of_forall fun H => totalAbsMass_nonneg E _ H)]
  exact ENNReal.ofReal_le_ofReal (integral_totalAbsMass_le model source E K)

theorem lintegral_collarAbsMass_le' (model : p.GaussianRingModel)
    (source : BlockBand.External.PSSS.SourceContract.{0}) (E : ℝ) (K : ℕ) :
    ∫⁻ H, ENNReal.ofReal (collarAbsMass p E ((1 / 2 : ℝ) ^ (K + 1)) H)
        ∂(model.law : Measure p.SiteMatrix) ≤
      ENNReal.ofReal (3 * (p.N * traceConst p source K) / p.n) := by
  have h := (lintegral_collarAbsMass_le model E ((1 / 2 : ℝ) ^ (K + 1))).trans
    (mul_le_mul_right (lintegral_totalAbsMass_le model source E K) 3)
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  rw [ENNReal.ofReal_div_of_pos hn, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hn.ne'))
    (Or.inl ENNReal.ofReal_ne_top), mul_comm, ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_natCast]
  simpa using h

/-!
## 3. The finite-width bound
-/

/-- Markov for an `|R|`-form. -/
theorem measure_le_absForm_le (model : p.GaussianRingModel) (E δ : ℝ) {J : ℕ} (a : Fin J)
    (d : p.Site → ℂ) {t m : ℝ} (ht : 0 < t)
    (hm : ∫⁻ x, ENNReal.ofReal (absForm E δ x.1 (fun y => d y * x.2 a y))
      ∂fullRingProbeLaw model J ≤ ENNReal.ofReal m) :
    fullRingProbeLaw model J
        {x | ENNReal.ofReal t ≤ ENNReal.ofReal (absForm E δ x.1 (fun y => d y * x.2 a y))} ≤
      ENNReal.ofReal (m / t) := by
  have hmeas : Measurable fun x : p.SiteMatrix × (Fin J → p.Site → ℂ) =>
      ENNReal.ofReal (absForm E δ x.1 (fun y => d y * x.2 a y)) :=
    ENNReal.measurable_ofReal.comp (measurable_absForm_scaled E δ measurable_fst
      ((measurable_pi_apply a).comp measurable_snd) d)
  refine (meas_ge_le_lintegral_div hmeas.aemeasurable (by simpa using ht)
    ENNReal.ofReal_ne_top).trans ?_
  rw [ENNReal.ofReal_div_of_pos ht]
  exact ENNReal.div_le_div_right hm _

/-- Expected `|R|`-form of a probe restricted to the collar: `≤ W⁻²‖Q‖ (3/n) N L_K`. -/
theorem lintegral_collarProbe_le (model : p.GaussianRingModel)
    (source : BlockBand.External.PSSS.SourceContract.{0}) (E : ℝ) (K : ℕ) {J : ℕ} (a : Fin J)
    {Q : C(Torus, ℝ)} (hQ : ∀ x, 0 ≤ Q x) :
    ∫⁻ x, ENNReal.ofReal (absForm E ((1 / 2 : ℝ) ^ (K + 1)) x.1
        (fun y => (if IsCollarBlock p y.1 then probeCoeff p Q y else 0) * x.2 a y))
        ∂fullRingProbeLaw model J ≤
      ENNReal.ofReal (((p.W : ℝ) ^ 2)⁻¹ * ‖Q‖ * (3 * (p.N * traceConst p source K) / p.n)) := by
  have hκ : 0 ≤ ((p.W : ℝ) ^ 2)⁻¹ * ‖Q‖ := by positivity
  refine (lintegral_probeForm_le model E _ a _ (fun y => IsCollarBlock p y.1) hκ
    (fun y => ?_)).trans ?_
  · split_ifs
    · exact norm_sq_probeCoeff_le hQ y
    · simp
  · rw [ENNReal.ofReal_mul hκ]
    exact mul_le_mul_right (lintegral_collarAbsMass_le' model source E K) _

/-- Expected `|R|`-form of a masked probe (full or collar-omitted): `≤ W⁻²‖Q‖ N L_K`. -/
theorem lintegral_maskedProbe_le (model : p.GaussianRingModel)
    (source : BlockBand.External.PSSS.SourceContract.{0}) (E : ℝ) (K : ℕ) {J : ℕ} (a : Fin J)
    {Q : C(Torus, ℝ)} (hQ : ∀ x, 0 ≤ Q x) (d : p.Site → ℂ)
    (hd : ∀ y, d y = probeCoeff p Q y ∨ d y = 0) :
    ∫⁻ x, ENNReal.ofReal (absForm E ((1 / 2 : ℝ) ^ (K + 1)) x.1 (fun y => d y * x.2 a y))
        ∂fullRingProbeLaw model J ≤
      ENNReal.ofReal (((p.W : ℝ) ^ 2)⁻¹ * ‖Q‖ * (p.N * traceConst p source K)) := by
  have hκ : 0 ≤ ((p.W : ℝ) ^ 2)⁻¹ * ‖Q‖ := by positivity
  refine (lintegral_probeForm_le model E _ a _ (fun _ => True) hκ (fun y => ?_)).trans ?_
  · simp only [ite_true]
    rcases hd y with h | h
    · rw [h]; exact norm_sq_probeCoeff_le hQ y
    · rw [h, norm_zero]; simpa using hκ
  · rw [ENNReal.ofReal_mul hκ]
    refine mul_le_mul_right (le_of_eq_of_le ?_ (lintegral_totalAbsMass_le model source E K)) _
    simp [totalAbsMass]

/-- Two nonnegative factors below `η` and `t/η` have product `< t`. -/
theorem mul_lt_of_lt_of_lt_div {x y η t : ℝ} (hx0 : 0 ≤ x) (hη : 0 < η) (ht : 0 < t)
    (hx : x < η) (hy : y < t / η) : x * y < t := by
  calc x * y ≤ x * (t / η) := mul_le_mul_of_nonneg_left hy.le hx0
    _ < η * (t / η) := mul_lt_mul_of_pos_right hx (by positivity)
    _ = t := by field_simp

/-- `z ≥ 0`, `z² < ε²/4`, `ε > 0` give `z < ε/2`. -/
theorem lt_half_of_sq_lt {z ε : ℝ} (hz : 0 ≤ z) (hε : 0 < ε) (h : z ^ 2 < ε ^ 2 / 4) :
    z < ε / 2 := by
  nlinarith

/-- **Finite-width collar bound** (with `δ = 2^{-(K+1)}` in place of `ε/Λ`):
for every realization, `E`, nonnegative profiles, `ε, η > 0`, `K`,
`P(|(ζ^*Rζ - ζ_o^*Rζ_o)_{ac}| > ε) ≤ (C/√c) N 2δ + W⁻²(‖Q_a‖+‖Q_c‖)[(3/n) N L_K/η + N L_K η/t]`,
`t = ε²/4`. -/
theorem measure_collarDiff_le (model : p.GaussianRingModel)
    (source : BlockBand.External.PSSS.SourceContract.{0}) (E : ℝ) {J : ℕ}
    (Q : Fin J → C(Torus, ℝ)) (hQ : ∀ a x, 0 ≤ Q a x) (a c : Fin J) {ε η : ℝ} (hε : 0 < ε)
    (hη : 0 < η) (K : ℕ) :
    fullRingProbeLaw model J {x | ε < ‖ringSourceMatrix p E Q x.1 x.2 a c -
        omittedRingSourceMatrix p E Q x.1 x.2 a c‖} ≤
      ENNReal.ofReal (source.C / Real.sqrt p.c * p.N * (2 * (1 / 2 : ℝ) ^ (K + 1))) +
      ENNReal.ofReal (((p.W : ℝ) ^ 2)⁻¹ * ‖Q a‖ * (3 * (p.N * traceConst p source K) / p.n) / η) +
      ENNReal.ofReal (((p.W : ℝ) ^ 2)⁻¹ * ‖Q c‖ * (p.N * traceConst p source K) /
        (ε ^ 2 / 4 / η)) +
      ENNReal.ofReal (((p.W : ℝ) ^ 2)⁻¹ * ‖Q c‖ * (3 * (p.N * traceConst p source K) / p.n) / η) +
      ENNReal.ofReal (((p.W : ℝ) ^ 2)⁻¹ * ‖Q a‖ * (p.N * traceConst p source K) /
        (ε ^ 2 / 4 / η)) := by
  set δ : ℝ := (1 / 2 : ℝ) ^ (K + 1)
  have hδ : 0 < δ := by positivity
  set t : ℝ := ε ^ 2 / 4
  have ht : 0 < t := by positivity
  have htη : 0 < t / η := by positivity
  set μ := fullRingProbeLaw model J
  -- coefficient functions
  set dc : Fin J → p.Site → ℂ := fun b y =>
    if IsCollarBlock p y.1 then probeCoeff p (Q b) y else 0
  set dO : Fin J → p.Site → ℂ := fun b y =>
    if IsCollarBlock p y.1 then 0 else probeCoeff p (Q b) y
  set df : Fin J → p.Site → ℂ := fun b y => probeCoeff p (Q b) y
  set A : (Fin J → p.Site → ℂ) → Fin J → p.SiteMatrix × (Fin J → p.Site → ℂ) → ℝ :=
    fun d b x => absForm E δ x.1 (fun y => d b y * x.2 b y)
  set cnt : p.SiteMatrix → ℕ := fun H =>
    BlockBand.Counting.physicalSpectralSetCount p (zeroHermitian p) (Icc (E - δ) (E + δ)) H
  set S0 := {x : p.SiteMatrix × (Fin J → p.Site → ℂ) | ¬ x.1.IsHermitian}
  set S1 := {x : p.SiteMatrix × (Fin J → p.Site → ℂ) | 1 ≤ cnt x.1}
  set S2 := {x | ENNReal.ofReal η ≤ ENNReal.ofReal (A dc a x)}
  set S3 := {x | ENNReal.ofReal (t / η) ≤ ENNReal.ofReal (A df c x)}
  set S4 := {x | ENNReal.ofReal η ≤ ENNReal.ofReal (A dc c x)}
  set S5 := {x | ENNReal.ofReal (t / η) ≤ ENNReal.ofReal (A dO a x)}
  have hsub : {x : p.SiteMatrix × (Fin J → p.Site → ℂ) | ε < ‖ringSourceMatrix p E Q x.1 x.2 a c -
      omittedRingSourceMatrix p E Q x.1 x.2 a c‖} ⊆ S0 ∪ S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 := by
    intro x hx
    by_contra hcon
    simp only [S0, S1, S2, S3, S4, S5, mem_union, mem_ofPred_eq, not_or, not_le, not_not] at hcon
    obtain ⟨⟨⟨⟨⟨hH, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hcon
    rw [ENNReal.ofReal_lt_ofReal_iff hη] at h2 h4
    rw [ENNReal.ofReal_lt_ofReal_iff htη] at h3 h5
    have hcnt : cnt x.1 = 0 := by omega
    have hgap := gap_of_count_eq_zero hH hcnt
    have hD := ringSource_sub_omitted_eq E Q x.1 x.2 a c
    rw [collarPart_ringProbeVector_eq, omitCollar_ringProbeVector_eq,
      collarPart_ringProbeVector_eq, ringProbeVector_eq] at hD
    have e1 := norm_sq_dotProduct_inv_le hH hδ.le hgap
      (fun y => dc a y * x.2 a y) (fun y => df c y * x.2 c y)
    have e2 := norm_sq_dotProduct_inv_le hH hδ.le hgap
      (fun y => dO a y * x.2 a y) (fun y => dc c y * x.2 c y)
    change _ ≤ A dc a x * A df c x at e1
    change _ ≤ A dO a x * A dc c x at e2
    have hA : ∀ d b, 0 ≤ A d b x := fun d b => absForm_nonneg E δ x.1 _
    have t1 := lt_half_of_sq_lt (norm_nonneg _) hε (e1.trans_lt
      (mul_lt_of_lt_of_lt_div (hA _ _) hη ht h2 h3))
    have t2 := lt_half_of_sq_lt (norm_nonneg _) hε (e2.trans_lt (by
      rw [mul_comm]; exact mul_lt_of_lt_of_lt_div (hA _ _) hη ht h4 h5))
    have hle := norm_add_le (star (fun y => dc a y * x.2 a y) ⬝ᵥ
      ((x.1 - (E : ℂ) • 1)⁻¹ *ᵥ fun y => df c y * x.2 c y))
      (star (fun y => dO a y * x.2 a y) ⬝ᵥ ((x.1 - (E : ℂ) • 1)⁻¹ *ᵥ fun y => dc c y * x.2 c y))
    change ε < ‖ringSourceMatrix p E Q x.1 x.2 a c - omittedRingSourceMatrix p E Q x.1 x.2 a c‖ at hx
    rw [hD] at hx
    linarith
  -- measures of the bad sets
  have m0 : μ S0 = 0 := by
    have h := (model.isPhysical.1 : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), H.IsHermitian)
    exact ae_iff.mp (Measure.quasiMeasurePreserving_fst.ae h)
  have m1 : μ S1 ≤ ENNReal.ofReal (source.C / Real.sqrt p.c * p.N * (2 * δ)) := by
    have hS1 : S1 = {H | 1 ≤ cnt H} ×ˢ univ := by ext x; simp [S1]
    rw [hS1]
    simp only [μ, fullRingProbeLaw]
    rw [Measure.prod_prod, measure_univ, mul_one]
    exact measure_count_pos_le model source E hδ.le
  have m2 := measure_le_absForm_le model E δ a (dc a) hη
    (lintegral_collarProbe_le model source E K a (hQ a))
  have m3 := measure_le_absForm_le model E δ c (df c) htη
    (lintegral_maskedProbe_le model source E K c (hQ c) (df c) fun y => Or.inl rfl)
  have m4 := measure_le_absForm_le model E δ c (dc c) hη
    (lintegral_collarProbe_le model source E K c (hQ c))
  have m5 := measure_le_absForm_le model E δ a (dO a) htη
    (lintegral_maskedProbe_le model source E K a (hQ a) (dO a) fun y => by
      simp only [dO]; split_ifs <;> simp)
  calc μ {x | ε < ‖ringSourceMatrix p E Q x.1 x.2 a c - omittedRingSourceMatrix p E Q x.1 x.2 a c‖}
      ≤ μ (S0 ∪ S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5) := measure_mono hsub
    _ ≤ μ (S0 ∪ S1 ∪ S2 ∪ S3 ∪ S4) + μ S5 := measure_union_le _ _
    _ ≤ μ (S0 ∪ S1 ∪ S2 ∪ S3) + μ S4 + μ S5 := by gcongr; exact measure_union_le _ _
    _ ≤ μ (S0 ∪ S1 ∪ S2) + μ S3 + μ S4 + μ S5 := by gcongr; exact measure_union_le _ _
    _ ≤ μ (S0 ∪ S1) + μ S2 + μ S3 + μ S4 + μ S5 := by gcongr; exact measure_union_le _ _
    _ ≤ μ S0 + μ S1 + μ S2 + μ S3 + μ S4 + μ S5 := by gcongr; exact measure_union_le _ _
    _ ≤ _ := by
        rw [m0, zero_add]
        gcongr

end BlockBand.Critical.EntireLaw
