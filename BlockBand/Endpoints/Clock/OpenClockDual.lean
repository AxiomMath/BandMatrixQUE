module

public import BlockBand.Endpoints.Clock.OpenClockStep

/-!
# The discrete dual (stopped Feynman–Kac) comparison at fixed width

## The dual chain

On the constructed Wiener space, sample `e_i = ω(i h)` (`sampleW`, `h ∈ ℝ≥0`) and put
* `dualB e i = a exp(√D (e_i - e_0) - D i h/2)` (the dual geometric Brownian motion started at
  `a`; `dualB_succ`: `b_{k+1} = b_k M_h` with the one-step factor of `OpenClockStep`);
* `dualAlive e k = ∏_{i ≤ k} 1_{[K⁻¹,K]}(b_i)` (alive up to `k`; killing at the first exit,
  which is the discrete form of the paper's stop at `[K⁻¹, K]`);
* `dualKill e k = exp(-c h Σ_{i<k} q(t - i h) b_i)` (a left Riemann sum of the paper's killing
  `a d ∫ q(t-s) M_s ds`).

## Results

* `integral_indep_eq`: for independent `X, Y` and bounded measurable `F`,
  `E F(X,Y) = E_ω E_ω' F(X ω, Y ω')`;
* `dual_step_bound` (one step, Markov property `IsPreBrownianReal.indepFun_shift`): if
  `|lap μ₁ b - e^{-c h q_k b} E lap μ₀ (b M_h)| ≤ ε` on `[K⁻¹, K]` then the dual terms
  `u_k = E[A_k κ_k lap μ₁ (b_k)]`, `E[A_{k+1} κ_{k+1} lap μ₀ (b_{k+1})]` differ by at most
  `ε + E A_k - E A_{k+1}`;
* `dual_compare` (telescoping over `k < N`): for laws `μs 0, …, μs N` carried by `[0,∞)`,
  `|lap (μs 0) a - E κ_N| ≤ Σ_{k<N} ε_k + 2(1 - E A_N) + η` where `η` bounds
  `|lap (μs N) - 1|` on `[K⁻¹, K]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock
namespace OpenClock

open MeasureTheory ProbabilityTheory Real Set
open BlockBand.SourceProcess
open scoped NNReal ENNReal

/-!
## 1. Independence and iterated integrals
-/

/-- For independent `X, Y` and a bounded measurable `F`, `E F(X,Y) = E_ω E_ω' F(X ω, Y ω')`. -/
theorem integral_indep_eq {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → α} {Y : Ω → β}
    (hX : Measurable X) (hY : Measurable Y) (h : IndepFun X Y P) {F : α × β → ℝ}
    (hF : Measurable F) {C : ℝ} (hC : ∀ z, |F z| ≤ C) :
    ∫ ω, F (X ω, Y ω) ∂P = ∫ ω, (∫ ω', F (X ω, Y ω') ∂P) ∂P := by
  have hmap : P.map (fun ω => (X ω, Y ω)) = (P.map X).prod (P.map Y) :=
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 h
  have hFI : Integrable F ((P.map X).prod (P.map Y)) :=
    Integrable.of_bound hF.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hC z)
  have h1 : ∫ ω, F (X ω, Y ω) ∂P = ∫ z, F z ∂((P.map X).prod (P.map Y)) := by
    rw [← hmap, integral_map (hX.prodMk hY).aemeasurable hF.aestronglyMeasurable]
  rw [h1, integral_prod F hFI]
  have hinner : ∀ x, ∫ y, F (x, y) ∂(P.map Y) = ∫ ω', F (x, Y ω') ∂P := fun x =>
    integral_map hY.aemeasurable (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  simp_rw [hinner]
  have hm : StronglyMeasurable (fun x => ∫ ω', F (x, Y ω') ∂P) := by
    have : StronglyMeasurable (Function.uncurry fun x ω' => F (x, Y ω')) :=
      (hF.comp (measurable_fst.prodMk (hY.comp measurable_snd))).stronglyMeasurable
    exact this.integral_prod_right'
  exact integral_map hX.aemeasurable hm.aestronglyMeasurable

/-- Bounded measurable functions are integrable for a probability measure. -/
theorem integrable_of_abs_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f) (C : ℝ) (h : ∀ ω, |f ω| ≤ C) :
    Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact h ω)

/-!
## 2. Laplace transforms: measurability and bounds
-/

theorem measurable_lap (μ : Measure ℝ) [SFinite μ] : Measurable (lap μ) := by
  have : StronglyMeasurable (Function.uncurry fun (b x : ℝ) => exp (-(b * x))) :=
    (continuous_exp.comp (continuous_fst.mul continuous_snd).neg).measurable.stronglyMeasurable
  exact this.integral_prod_right'.measurable

theorem abs_lap_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {b : ℝ}
    (hb : 0 ≤ b) : |lap μ b| ≤ 1 := by
  rw [abs_of_nonneg (lap_nonneg μ b)]; exact lap_le_one μ hμ hb

/-- `0 ≤ b² ∫ x² e^{-bx} dμ ≤ 2` for `b ≥ 0`. -/
theorem sq_mul_lap2_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {b : ℝ}
    (hb : 0 ≤ b) : 0 ≤ b ^ 2 * lap2 μ b ∧ b ^ 2 * lap2 μ b ≤ 2 := by
  rw [lap2_eq_max μ hμ b, ← integral_const_mul]
  have hpt : ∀ x, b ^ 2 * ((max x 0) ^ 2 * exp (-(b * max x 0)))
      = (b * max x 0) ^ 2 * exp (-(b * max x 0)) := fun x => by ring
  simp_rw [hpt]
  constructor
  · exact integral_nonneg fun x => by positivity
  · have hb2 : ∀ x, (b * max x 0) ^ 2 * exp (-(b * max x 0)) ≤ 2 := fun x =>
      sq_mul_exp_neg_le (mul_nonneg hb (le_max_right _ _))
    calc ∫ x, (b * max x 0) ^ 2 * exp (-(b * max x 0)) ∂μ ≤ ∫ _x, (2 : ℝ) ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
            (integrable_const 2) (Filter.Eventually.of_forall hb2)
      _ = 2 := by simp

/-- Laplace transforms of laws on `[0,∞)` are antitone on `[0,∞)`. -/
theorem lap_antitone (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {b b' : ℝ}
    (hb : 0 ≤ b) (hbb : b ≤ b') : lap μ b' ≤ lap μ b := by
  rw [lap_eq_max μ hμ, lap_eq_max μ hμ]
  have hb' : 0 ≤ b' := hb.trans hbb
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => (exp_pos _).le) ?_
    (Filter.Eventually.of_forall fun x => ?_)
  · refine integrable_of_abs_le ?_ 1 fun x => ?_
    · exact measurable_exp.comp ((measurable_const.mul (measurable_id.max measurable_const)).neg)
    · rw [abs_of_pos (exp_pos _), exp_le_one_iff, neg_nonpos]
      exact mul_nonneg hb (le_max_right _ _)
  · exact exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hbb (le_max_right _ _)))

/-!
## 3. The dual chain
-/

/-- Samples `e_i = ω(i h)` of the Wiener path on the grid of mesh `h`. -/
def sampleW (hh : ℝ≥0) (ω : CanonicalWienerPath) (i : ℕ) : ℝ := ω ((i : ℝ≥0) * hh)

/-- The dual geometric Brownian motion on the grid, started at `a`. -/
def dualB (D a : ℝ) (hh : ℝ≥0) (e : ℕ → ℝ) (i : ℕ) : ℝ :=
  a * exp (Real.sqrt D * (e i - e 0) - D * ((i : ℝ) * hh) / 2)

/-- `∏_{i ≤ k} 1_{[K⁻¹,K]}(b_i)`: the dual has not left `[K⁻¹, K]` up to step `k`. -/
def dualAlive (D a K : ℝ) (hh : ℝ≥0) (e : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range (k + 1), (Icc K⁻¹ K).indicator (fun _ => (1 : ℝ)) (dualB D a hh e i)

/-- Discrete killing `exp(-c h Σ_{i<k} q(t - i h) b_i)`. -/
def dualKill (D a c : ℝ) (q : ℝ → ℝ) (t : ℝ) (hh : ℝ≥0) (e : ℕ → ℝ) (k : ℕ) : ℝ :=
  exp (-(c * hh * ∑ i ∈ Finset.range k, q (t - i * hh) * dualB D a hh e i))

section Dual

variable {D a K c : ℝ} {q : ℝ → ℝ} {t : ℝ} {hh : ℝ≥0}

theorem dualB_pos (ha : 0 < a) (e : ℕ → ℝ) (i : ℕ) : 0 < dualB D a hh e i :=
  mul_pos ha (exp_pos _)

theorem dualB_zero (e : ℕ → ℝ) : dualB D a hh e 0 = a := by
  simp [dualB]

theorem indicator_mem (K b : ℝ) :
    0 ≤ (Icc K⁻¹ K).indicator (fun _ => (1 : ℝ)) b ∧
      (Icc K⁻¹ K).indicator (fun _ => (1 : ℝ)) b ≤ 1 := by
  by_cases h : b ∈ Icc K⁻¹ K
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

theorem dualAlive_mem (e : ℕ → ℝ) (k : ℕ) :
    0 ≤ dualAlive D a K hh e k ∧ dualAlive D a K hh e k ≤ 1 := by
  unfold dualAlive
  exact ⟨Finset.prod_nonneg fun i _ => (indicator_mem K _).1,
    Finset.prod_le_one₀ (fun i _ => (indicator_mem K _).1) fun i _ => (indicator_mem K _).2⟩

theorem dualAlive_succ (e : ℕ → ℝ) (k : ℕ) :
    dualAlive D a K hh e (k + 1) =
      dualAlive D a K hh e k * (Icc K⁻¹ K).indicator (fun _ => (1 : ℝ)) (dualB D a hh e (k + 1)) := by
  unfold dualAlive; rw [Finset.prod_range_succ]

theorem mem_of_dualAlive_ne_zero {e : ℕ → ℝ} {k : ℕ} (h : dualAlive D a K hh e k ≠ 0) :
    dualB D a hh e k ∈ Icc K⁻¹ K := by
  by_contra hk
  apply h
  unfold dualAlive
  exact Finset.prod_eq_zero (Finset.self_mem_range_succ k) (Set.indicator_of_notMem hk _)

theorem dualKill_mem (ha : 0 < a) (hc : 0 ≤ c) (hq : ∀ x, 0 ≤ q x) (e : ℕ → ℝ) (k : ℕ) :
    0 < dualKill D a c q t hh e k ∧ dualKill D a c q t hh e k ≤ 1 := by
  refine ⟨exp_pos _, ?_⟩
  unfold dualKill
  rw [exp_le_one_iff, neg_nonpos]
  refine mul_nonneg (mul_nonneg hc hh.2) (Finset.sum_nonneg fun i _ => ?_)
  exact mul_nonneg (hq _) (dualB_pos ha e i).le

theorem dualKill_zero (e : ℕ → ℝ) : dualKill D a c q t hh e 0 = 1 := by
  simp [dualKill]

theorem dualKill_succ (e : ℕ → ℝ) (k : ℕ) :
    dualKill D a c q t hh e (k + 1) =
      dualKill D a c q t hh e k * exp (-(c * hh * q (t - k * hh) * dualB D a hh e k)) := by
  unfold dualKill
  rw [← exp_add, Finset.sum_range_succ]
  congr 1; ring

theorem dualB_congr {e e' : ℕ → ℝ} {k : ℕ} (h : ∀ i ≤ k, e i = e' i) {i : ℕ} (hi : i ≤ k) :
    dualB D a hh e i = dualB D a hh e' i := by
  unfold dualB; rw [h i hi, h 0 (Nat.zero_le _)]

theorem dualAlive_congr {e e' : ℕ → ℝ} {k : ℕ} (h : ∀ i ≤ k, e i = e' i) :
    dualAlive D a K hh e k = dualAlive D a K hh e' k := by
  unfold dualAlive
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [dualB_congr h (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

theorem dualKill_congr {e e' : ℕ → ℝ} {k : ℕ} (h : ∀ i ≤ k, e i = e' i) :
    dualKill D a c q t hh e k = dualKill D a c q t hh e' k := by
  unfold dualKill
  congr 3
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [dualB_congr h (Finset.mem_range.mp hi).le]

theorem measurable_dualB (i : ℕ) : Measurable (fun e : ℕ → ℝ => dualB D a hh e i) := by
  unfold dualB
  refine measurable_const.mul (measurable_exp.comp ?_)
  exact (measurable_const.mul ((measurable_pi_apply i).sub (measurable_pi_apply 0))).sub
    measurable_const

theorem measurable_dualAlive (k : ℕ) : Measurable (fun e : ℕ → ℝ => dualAlive D a K hh e k) := by
  unfold dualAlive
  refine Finset.measurable_prod _ fun i _ => ?_
  exact (measurable_const.indicator measurableSet_Icc).comp (measurable_dualB i)

theorem measurable_dualKill (k : ℕ) :
    Measurable (fun e : ℕ → ℝ => dualKill D a c q t hh e k) := by
  unfold dualKill
  refine measurable_exp.comp (Measurable.neg (measurable_const.mul ?_))
  exact Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_dualB i)

theorem measurable_sampleW (hh : ℝ≥0) : Measurable (sampleW hh) :=
  Measurable.of_eval fun i => (continuous_eval_const ((i : ℝ≥0) * hh)).measurable

/-- `b_{k+1} = b_k M_h`, with `M_h` the one-step lognormal factor started at time `k h`. -/
theorem dualB_succ (ω : CanonicalWienerPath) (k : ℕ) :
    dualB D a hh (sampleW hh ω) (k + 1) =
      dualB D a hh (sampleW hh ω) k * lognormal D ((k : ℝ≥0) * hh) hh ω := by
  unfold dualB lognormal logZ incr sampleW
  have ht : ((k + 1 : ℕ) : ℝ≥0) * hh = (k : ℝ≥0) * hh + hh := by push_cast; ring
  rw [ht, mul_assoc, ← exp_add]
  congr 2
  push_cast
  ring

end Dual

/-!
## 4. One step of the dual comparison
-/

section Step

variable {D a K c : ℝ} {q : ℝ → ℝ} {t : ℝ} {hh : ℝ≥0}

/-- Past samples read off the restriction of the path to `[0, k h]`. -/
def pastSample (hh : ℝ≥0) (k : ℕ) (x : Iic ((k : ℝ≥0) * hh) → ℝ) (i : ℕ) : ℝ :=
  if h : (i : ℝ≥0) * hh ≤ (k : ℝ≥0) * hh then x ⟨(i : ℝ≥0) * hh, h⟩ else 0

theorem measurable_pastSample (hh : ℝ≥0) (k : ℕ) : Measurable (pastSample hh k) := by
  refine Measurable.of_eval fun i => ?_
  unfold pastSample
  by_cases h : (i : ℝ≥0) * hh ≤ (k : ℝ≥0) * hh
  · simp only [h, ↓reduceDIte]; exact measurable_pi_apply _
  · simp only [h, ↓reduceDIte]; exact measurable_const

theorem pastSample_eq (hh : ℝ≥0) (k : ℕ) (ω : CanonicalWienerPath) {i : ℕ} (hi : i ≤ k) :
    pastSample hh k (fun s : Iic ((k : ℝ≥0) * hh) => ω s) i = sampleW hh ω i := by
  have h : (i : ℝ≥0) * hh ≤ (k : ℝ≥0) * hh := mul_le_mul_of_nonneg_right (by exact_mod_cast hi)
    hh.2
  simp [pastSample, h, sampleW]

/-- **One dual step.** If `|lap μ₁ b - e^{-c h q(t - k h) b} E lap μ₀ (b M_h)| ≤ ε` for all
`b ∈ [K⁻¹, K]`, then
`|E[A_k κ_k lap μ₁(b_k)] - E[A_{k+1} κ_{k+1} lap μ₀(b_{k+1})]| ≤ ε + E A_k - E A_{k+1}`. -/
theorem dual_step_bound (ha : 0 < a) (hc : 0 ≤ c) (hq : ∀ x, 0 ≤ q x) (k : ℕ)
    (μ₀ μ₁ : Measure ℝ) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (hμ₀ : ∀ᵐ x ∂μ₀, 0 ≤ x) (hμ₁ : ∀ᵐ x ∂μ₁, 0 ≤ x) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ b ∈ Icc K⁻¹ K, |lap μ₁ b - exp (-(c * hh * q (t - k * hh) * b)) *
        ∫ ω, lap μ₀ (b * lognormal D ((k : ℝ≥0) * hh) hh ω) ∂canonicalWienerLaw| ≤ ε) :
    |∫ ω, dualAlive D a K hh (sampleW hh ω) k * dualKill D a c q t hh (sampleW hh ω) k *
          lap μ₁ (dualB D a hh (sampleW hh ω) k) ∂canonicalWienerLaw -
        ∫ ω, dualAlive D a K hh (sampleW hh ω) (k + 1) *
          dualKill D a c q t hh (sampleW hh ω) (k + 1) *
          lap μ₀ (dualB D a hh (sampleW hh ω) (k + 1)) ∂canonicalWienerLaw|
      ≤ ε + (∫ ω, dualAlive D a K hh (sampleW hh ω) k ∂canonicalWienerLaw -
        ∫ ω, dualAlive D a K hh (sampleW hh ω) (k + 1) ∂canonicalWienerLaw) := by
  set P := canonicalWienerLaw
  set S := sampleW hh
  have hS := measurable_sampleW hh
  set A : CanonicalWienerPath → ℝ := fun ω => dualAlive D a K hh (S ω) k with hA
  set A' : CanonicalWienerPath → ℝ := fun ω => dualAlive D a K hh (S ω) (k + 1) with hA'
  set κ : CanonicalWienerPath → ℝ := fun ω => dualKill D a c q t hh (S ω) k with hκ
  set κ' : CanonicalWienerPath → ℝ := fun ω => dualKill D a c q t hh (S ω) (k + 1) with hκ'
  set B : CanonicalWienerPath → ℝ := fun ω => dualB D a hh (S ω) k with hB
  set B' : CanonicalWienerPath → ℝ := fun ω => dualB D a hh (S ω) (k + 1) with hB'
  set L : CanonicalWienerPath → ℝ := fun ω => lognormal D ((k : ℝ≥0) * hh) hh ω with hL
  set z : ℝ := c * hh * q (t - k * hh) with hz
  set H : ℝ → ℝ := fun b => exp (-(z * b)) * ∫ ω, lap μ₀ (b * L ω) ∂P with hH
  set ind' : CanonicalWienerPath → ℝ :=
    fun ω => (Icc K⁻¹ K).indicator (fun _ => (1 : ℝ)) (B' ω) with hind'
  -- measurability
  have mA : Measurable A := (measurable_dualAlive k).comp hS
  have mA' : Measurable A' := (measurable_dualAlive (k + 1)).comp hS
  have mκ : Measurable κ := (measurable_dualKill k).comp hS
  have mκ' : Measurable κ' := (measurable_dualKill (k + 1)).comp hS
  have mB : Measurable B := (measurable_dualB k).comp hS
  have mB' : Measurable B' := (measurable_dualB (k + 1)).comp hS
  have mL : Measurable L := measurable_lognormal D _ hh
  have mlap₀ := measurable_lap μ₀
  have mlap₁ := measurable_lap μ₁
  -- bounds
  have bA : ∀ ω, 0 ≤ A ω ∧ A ω ≤ 1 := fun ω => dualAlive_mem _ _
  have bA' : ∀ ω, 0 ≤ A' ω ∧ A' ω ≤ 1 := fun ω => dualAlive_mem _ _
  have bκ : ∀ ω, 0 < κ ω ∧ κ ω ≤ 1 := fun ω => dualKill_mem ha hc hq _ _
  have bκ' : ∀ ω, 0 < κ' ω ∧ κ' ω ≤ 1 := fun ω => dualKill_mem ha hc hq _ _
  have pB : ∀ ω, 0 < B ω := fun ω => dualB_pos ha _ _
  have pB' : ∀ ω, 0 < B' ω := fun ω => dualB_pos ha _ _
  have hz0 : 0 ≤ z := mul_nonneg (mul_nonneg hc hh.2) (hq _)
  have blap₀ : ∀ {b : ℝ}, 0 ≤ b → |lap μ₀ b| ≤ 1 := fun hb => abs_lap_le_one μ₀ hμ₀ hb
  have blap₁ : ∀ {b : ℝ}, 0 ≤ b → |lap μ₁ b| ≤ 1 := fun hb => abs_lap_le_one μ₁ hμ₁ hb
  -- structural identities
  have hB'eq : ∀ ω, B' ω = B ω * L ω := fun ω => dualB_succ ω k
  have hκ'eq : ∀ ω, κ' ω = κ ω * exp (-(z * B ω)) := fun ω => by
    simp only [hκ', hκ, hB, hz]; rw [dualKill_succ]
  have hA'eq : ∀ ω, A' ω = A ω * ind' ω := fun ω => dualAlive_succ _ _
  -- the independence step
  have hindep : ∫ ω, A ω * κ ω * (exp (-(z * B ω)) * lap μ₀ (B ω * L ω)) ∂P =
      ∫ ω, A ω * κ ω * H (B ω) ∂P := by
    set t₀ : ℝ≥0 := (k : ℝ≥0) * hh
    set X : CanonicalWienerPath → (Iic t₀ → ℝ) := fun ω s => ω s with hX
    set Y : CanonicalWienerPath → (ℝ≥0 → ℝ) := fun ω s => ω (t₀ + s) - ω t₀ with hY
    have hXY : IndepFun X Y P :=
      (canonicalWiener_isBrownian.toIsPreBrownianReal.indepFun_shift t₀).symm
    have mX : Measurable X :=
      Measurable.of_eval fun s => (continuous_eval_const (s : ℝ≥0)).measurable
    have mY : Measurable Y := Measurable.of_eval fun s =>
      ((continuous_eval_const (t₀ + s)).sub (continuous_eval_const t₀)).measurable
    set ps := pastSample hh k
    have mps := measurable_pastSample hh k
    set Gb : ℝ → ℝ → ℝ := fun b y =>
      exp (-(z * max b 0)) * lap μ₀ (max b 0 * exp (Real.sqrt D * y - D * hh / 2)) with hGb
    set F : (Iic t₀ → ℝ) × (ℝ≥0 → ℝ) → ℝ := fun p =>
      dualAlive D a K hh (ps p.1) k * dualKill D a c q t hh (ps p.1) k *
        Gb (dualB D a hh (ps p.1) k) (p.2 hh) with hF
    have mF : Measurable F := by
      refine (((measurable_dualAlive k).comp (mps.comp measurable_fst)).mul
        ((measurable_dualKill k).comp (mps.comp measurable_fst))).mul ?_
      refine (measurable_exp.comp (measurable_const.mul
        (((measurable_dualB k).comp (mps.comp measurable_fst)).max measurable_const)).neg).mul ?_
      refine mlap₀.comp ?_
      exact (((measurable_dualB k).comp (mps.comp measurable_fst)).max measurable_const).mul
        (measurable_exp.comp ((measurable_const.mul
          ((measurable_pi_apply hh).comp measurable_snd)).sub measurable_const))
    have bF : ∀ p, |F p| ≤ 1 := by
      intro p
      simp only [hF, hGb]
      have h1 := dualAlive_mem (D := D) (a := a) (K := K) (hh := hh) (ps p.1) k
      have h2 := dualKill_mem (D := D) (t := t) (hh := hh) ha hc hq (ps p.1) k
      have h3 : 0 < exp (-(z * max (dualB D a hh (ps p.1) k) 0)) ∧
          exp (-(z * max (dualB D a hh (ps p.1) k) 0)) ≤ 1 :=
        ⟨exp_pos _, exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hz0 (le_max_right _ _)))⟩
      have h4 := blap₀ (mul_nonneg (le_max_right (dualB D a hh (ps p.1) k) 0)
        (exp_pos (Real.sqrt D * p.2 hh - D * hh / 2)).le)
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h1.1, abs_of_pos h2.1, abs_of_pos h3.1]
      have := mul_le_mul h3.2 h4 (abs_nonneg _) zero_le_one
      have := mul_le_mul h2.2 this (by positivity) zero_le_one
      have := mul_le_mul h1.2 this (mul_nonneg h2.1.le (by positivity)) zero_le_one
      simpa only [one_mul, mul_assoc] using this
    have hagree : ∀ ω, ∀ i ≤ k, ps (X ω) i = S ω i := fun ω i hi => pastSample_eq hh k ω hi
    have hFω : ∀ ω ω', F (X ω, Y ω') =
        A ω * κ ω * (exp (-(z * B ω)) * lap μ₀ (B ω * L ω')) := by
      intro ω ω'
      simp only [hF, hGb]
      rw [dualAlive_congr (hagree ω), dualKill_congr (hagree ω),
        dualB_congr (hagree ω) le_rfl, max_eq_left (pB ω).le]
      rfl
    have h := integral_indep_eq mX mY hXY mF bF
    simp_rw [hFω] at h
    rw [h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hH]
    rw [integral_const_mul, integral_const_mul]
  -- integrability
  have iA : Integrable A P := integrable_of_abs_le mA 1 fun ω => by
    rw [abs_of_nonneg (bA ω).1]; exact (bA ω).2
  have iA' : Integrable A' P := integrable_of_abs_le mA' 1 fun ω => by
    rw [abs_of_nonneg (bA' ω).1]; exact (bA' ω).2
  have mH : Measurable H := by
    refine (measurable_exp.comp (measurable_const.mul measurable_id).neg).mul ?_
    have : StronglyMeasurable (Function.uncurry fun (b : ℝ) (ω : CanonicalWienerPath) =>
        lap μ₀ (b * L ω)) :=
      (mlap₀.comp (measurable_fst.mul (mL.comp measurable_snd))).stronglyMeasurable
    exact this.integral_prod_right'.measurable
  have bH : ∀ {b : ℝ}, 0 ≤ b → |H b| ≤ 1 := by
    intro b hb
    simp only [hH]
    rw [abs_mul, abs_of_pos (exp_pos _)]
    have h1 : exp (-(z * b)) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hz0 hb))
    have h2 : |∫ ω, lap μ₀ (b * L ω) ∂P| ≤ 1 := by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ ω, |lap μ₀ (b * L ω)| ∂P ≤ ∫ _ω, (1 : ℝ) ∂P :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
              (integrable_const 1) (Filter.Eventually.of_forall fun ω =>
                blap₀ (mul_nonneg hb (lognormal_pos D _ hh ω).le))
        _ = 1 := by simp
    nlinarith [abs_nonneg (∫ ω, lap μ₀ (b * L ω) ∂P), exp_pos (-(z * b))]
  have i1 : Integrable (fun ω => A ω * κ ω * lap μ₁ (B ω)) P := by
    refine integrable_of_abs_le ((mA.mul mκ).mul (mlap₁.comp mB)) 1 fun ω => ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (bA ω).1, abs_of_pos (bκ ω).1]
    have := mul_le_mul (bκ ω).2 (blap₁ (pB ω).le) (abs_nonneg _) zero_le_one
    have := mul_le_mul (bA ω).2 this (mul_nonneg (bκ ω).1.le (abs_nonneg _)) zero_le_one
    simpa only [one_mul, mul_assoc] using this
  have i2 : Integrable (fun ω => A ω * κ ω * H (B ω)) P := by
    refine integrable_of_abs_le ((mA.mul mκ).mul (mH.comp mB)) 1 fun ω => ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (bA ω).1, abs_of_pos (bκ ω).1]
    have := mul_le_mul (bκ ω).2 (bH (pB ω).le) (abs_nonneg _) zero_le_one
    have := mul_le_mul (bA ω).2 this (mul_nonneg (bκ ω).1.le (abs_nonneg _)) zero_le_one
    simpa only [one_mul, mul_assoc] using this
  have i3 : Integrable (fun ω => A ω * κ ω * (exp (-(z * B ω)) * lap μ₀ (B ω * L ω))) P := by
    refine integrable_of_abs_le ((mA.mul mκ).mul ((measurable_exp.comp
      (measurable_const.mul mB).neg).mul (mlap₀.comp (mB.mul mL)))) 1 fun ω => ?_
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (bA ω).1, abs_of_pos (bκ ω).1,
      abs_of_pos (exp_pos _)]
    have he : exp (-(z * B ω)) ≤ 1 :=
      exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hz0 (pB ω).le))
    have := mul_le_mul he (blap₀ (mul_nonneg (pB ω).le (lognormal_pos D ((k : ℝ≥0) * hh) hh ω).le))
      (abs_nonneg _) zero_le_one
    have := mul_le_mul (bκ ω).2 this (by positivity) zero_le_one
    have := mul_le_mul (bA ω).2 this (mul_nonneg (bκ ω).1.le (by positivity)) zero_le_one
    simpa only [one_mul, mul_assoc] using this
  have i4 : Integrable (fun ω => (A ω - A' ω) * κ' ω * lap μ₀ (B' ω)) P := by
    refine integrable_of_abs_le (((mA.sub mA').mul mκ').mul (mlap₀.comp mB')) 1 fun ω => ?_
    have hd : 0 ≤ A ω - A' ω ∧ A ω - A' ω ≤ 1 := by
      rw [hA'eq]
      have := indicator_mem K (B' ω)
      constructor <;> nlinarith [bA ω]
    rw [abs_mul, abs_mul, abs_of_nonneg hd.1, abs_of_pos (bκ' ω).1]
    have := mul_le_mul (bκ' ω).2 (blap₀ (pB' ω).le) (abs_nonneg _) zero_le_one
    have := mul_le_mul hd.2 this (mul_nonneg (bκ' ω).1.le (abs_nonneg _)) zero_le_one
    simpa only [one_mul, mul_assoc] using this
  -- decomposition of the second dual term
  have hsecond : (fun ω => A' ω * κ' ω * lap μ₀ (B' ω)) =
      fun ω => A ω * κ ω * (exp (-(z * B ω)) * lap μ₀ (B ω * L ω)) -
        (A ω - A' ω) * κ' ω * lap μ₀ (B' ω) := by
    funext ω
    rw [hκ'eq, ← hB'eq]
    ring
  change |∫ ω, A ω * κ ω * lap μ₁ (B ω) ∂P - ∫ ω, A' ω * κ' ω * lap μ₀ (B' ω) ∂P|
    ≤ ε + (∫ ω, A ω ∂P - ∫ ω, A' ω ∂P)
  rw [hsecond, integral_sub i3 i4, hindep, ← integral_sub iA iA']
  have hdiff : ∫ ω, A ω * κ ω * lap μ₁ (B ω) ∂P -
      (∫ ω, A ω * κ ω * H (B ω) ∂P - ∫ ω, (A ω - A' ω) * κ' ω * lap μ₀ (B' ω) ∂P)
      = ∫ ω, A ω * κ ω * (lap μ₁ (B ω) - H (B ω)) ∂P +
        ∫ ω, (A ω - A' ω) * κ' ω * lap μ₀ (B' ω) ∂P := by
    rw [show ∀ x y w : ℝ, x - (y - w) = (x - y) + w from fun x y w => by ring,
      ← integral_sub i1 i2]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    ring
  rw [hdiff]
  -- pointwise bounds
  have ip1 : Integrable (fun ω => A ω * κ ω * (lap μ₁ (B ω) - H (B ω))) P := by
    have := i1.sub i2
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply]; ring
  have hpt1 : ∀ ω, |A ω * κ ω * (lap μ₁ (B ω) - H (B ω))| ≤ ε * A ω := by
    intro ω
    rcases eq_or_ne (A ω) 0 with h0 | h0
    · rw [h0]; simp
    · have hmem := mem_of_dualAlive_ne_zero h0
      have hb := hε (B ω) hmem
      have hlapB : lap μ₁ (B ω) - H (B ω) = lap μ₁ (B ω) - exp (-(c * hh * q (t - k * hh) *
          B ω)) * ∫ ω', lap μ₀ (B ω * lognormal D ((k : ℝ≥0) * hh) hh ω') ∂P := rfl
      rw [abs_mul, abs_mul, abs_of_nonneg (bA ω).1, abs_of_pos (bκ ω).1, hlapB]
      calc A ω * κ ω * |_| ≤ A ω * 1 * ε :=
            mul_le_mul (mul_le_mul_of_nonneg_left (bκ ω).2 (bA ω).1) hb (abs_nonneg _)
              (by nlinarith [bA ω])
        _ = ε * A ω := by ring
  have hpt2 : ∀ ω, |(A ω - A' ω) * κ' ω * lap μ₀ (B' ω)| ≤ A ω - A' ω := by
    intro ω
    have hd : 0 ≤ A ω - A' ω := by
      rw [hA'eq]; have := indicator_mem K (B' ω); nlinarith [bA ω]
    rw [abs_mul, abs_mul, abs_of_nonneg hd, abs_of_pos (bκ' ω).1]
    have := mul_le_mul (bκ' ω).2 (blap₀ (pB' ω).le) (abs_nonneg _) zero_le_one
    calc (A ω - A' ω) * κ' ω * |lap μ₀ (B' ω)| = (A ω - A' ω) * (κ' ω * |lap μ₀ (B' ω)|) := by
          ring
      _ ≤ (A ω - A' ω) * 1 := mul_le_mul_of_nonneg_left (by simpa using this) hd
      _ = A ω - A' ω := mul_one _
  have iY : Integrable (fun ω => A ω - A' ω) P := iA.sub iA'
  have hEA : ∫ ω, A ω ∂P ≤ 1 := by
    calc ∫ ω, A ω ∂P ≤ ∫ _ω, (1 : ℝ) ∂P :=
          integral_mono iA (integrable_const 1) fun ω => (bA ω).2
      _ = 1 := by simp
  calc |∫ ω, A ω * κ ω * (lap μ₁ (B ω) - H (B ω)) ∂P +
        ∫ ω, (A ω - A' ω) * κ' ω * lap μ₀ (B' ω) ∂P|
      ≤ |∫ ω, A ω * κ ω * (lap μ₁ (B ω) - H (B ω)) ∂P| +
        |∫ ω, (A ω - A' ω) * κ' ω * lap μ₀ (B' ω) ∂P| := abs_add_le _ _
    _ ≤ ∫ ω, |A ω * κ ω * (lap μ₁ (B ω) - H (B ω))| ∂P +
        ∫ ω, |(A ω - A' ω) * κ' ω * lap μ₀ (B' ω)| ∂P :=
        add_le_add abs_integral_le_integral_abs abs_integral_le_integral_abs
    _ ≤ ∫ ω, ε * A ω ∂P + ∫ ω, (A ω - A' ω) ∂P :=
        add_le_add (integral_mono ip1.abs (iA.const_mul ε) hpt1)
          (integral_mono i4.abs iY hpt2)
    _ = ε * ∫ ω, A ω ∂P + ∫ ω, (A ω - A' ω) ∂P := by rw [integral_const_mul]
    _ ≤ ε + ∫ ω, (A ω - A' ω) ∂P := by nlinarith

/-- **Telescoped dual comparison at fixed width.** Let `μs 0, …, μs N` be probability laws on
`[0,∞)` (in the application `μs k` is the law at original step `n - k`, so `μs 0` is the final
time and `μs N` the entrance time). If each dual step is `ε_k`-consistent on `[K⁻¹, K]`
(hypothesis of `dual_step_bound`) and `|lap (μs N) - 1| ≤ η` on `[K⁻¹, K]`, then for
`a ∈ [K⁻¹, K]`:
`|lap (μs 0) a - E κ_N| ≤ Σ_{k<N} ε_k + 2 (1 - E A_N) + η`. -/
theorem dual_compare (ha : 0 < a) (hc : 0 ≤ c) (hq : ∀ x, 0 ≤ q x) (haK : a ∈ Icc K⁻¹ K)
    (N : ℕ) (μs : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (μs k)]
    (hμs : ∀ k, ∀ᵐ x ∂μs k, 0 ≤ x) (ε : ℕ → ℝ) (hε0 : ∀ k, 0 ≤ ε k)
    (hε : ∀ k < N, ∀ b ∈ Icc K⁻¹ K, |lap (μs k) b - exp (-(c * hh * q (t - k * hh) * b)) *
        ∫ ω, lap (μs (k + 1)) (b * lognormal D ((k : ℝ≥0) * hh) hh ω) ∂canonicalWienerLaw| ≤ ε k)
    {η : ℝ} (hη : ∀ b ∈ Icc K⁻¹ K, |lap (μs N) b - 1| ≤ η) :
    |lap (μs 0) a - ∫ ω, dualKill D a c q t hh (sampleW hh ω) N ∂canonicalWienerLaw|
      ≤ ∑ k ∈ Finset.range N, ε k +
        2 * (1 - ∫ ω, dualAlive D a K hh (sampleW hh ω) N ∂canonicalWienerLaw) + η := by
  set P := canonicalWienerLaw
  set S := sampleW hh
  have hS := measurable_sampleW hh
  set u : ℕ → ℝ := fun k => ∫ ω, dualAlive D a K hh (S ω) k * dualKill D a c q t hh (S ω) k *
    lap (μs k) (dualB D a hh (S ω) k) ∂P with hu
  set α : ℕ → ℝ := fun k => ∫ ω, dualAlive D a K hh (S ω) k ∂P with hα
  have hstep : ∀ k < N, |u k - u (k + 1)| ≤ ε k + (α k - α (k + 1)) := fun k hk =>
    dual_step_bound ha hc hq k (μs (k + 1)) (μs k) (hμs (k + 1)) (hμs k) (hε0 k) (hε k hk)
  have hind1 : (Icc K⁻¹ K).indicator (fun _ => (1 : ℝ)) a = 1 := Set.indicator_of_mem haK _
  have hA0 : ∀ e : ℕ → ℝ, dualAlive D a K hh e 0 = 1 := fun e => by
    simp [dualAlive, dualB_zero, hind1]
  have hu0 : u 0 = lap (μs 0) a := by
    simp only [hu, hA0, dualKill_zero, dualB_zero, one_mul]
    simp
  have hα0 : α 0 = 1 := by simp only [hα, hA0]; simp
  have htel : |u 0 - u N| ≤ ∑ k ∈ Finset.range N, ε k + (α 0 - α N) := by
    have e1 : u 0 - u N = ∑ k ∈ Finset.range N, (u k - u (k + 1)) :=
      (Finset.sum_range_sub' u N).symm
    have e2 : α 0 - α N = ∑ k ∈ Finset.range N, (α k - α (k + 1)) :=
      (Finset.sum_range_sub' α N).symm
    rw [e1, e2, ← Finset.sum_add_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    exact hstep k (Finset.mem_range.mp hk)
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη a haK)
  -- the entrance term
  have mA := (measurable_dualAlive (D := D) (a := a) (K := K) (hh := hh) N).comp hS
  have mκ := (measurable_dualKill (D := D) (a := a) (c := c) (q := q) (t := t) (hh := hh) N).comp hS
  have mB := (measurable_dualB (D := D) (a := a) (hh := hh) N).comp hS
  have mlap := measurable_lap (μs N)
  have bA : ∀ ω, 0 ≤ dualAlive D a K hh (S ω) N ∧ dualAlive D a K hh (S ω) N ≤ 1 :=
    fun ω => dualAlive_mem _ _
  have bκ : ∀ ω, 0 < dualKill D a c q t hh (S ω) N ∧ dualKill D a c q t hh (S ω) N ≤ 1 :=
    fun ω => dualKill_mem ha hc hq _ _
  have blap : ∀ ω, |lap (μs N) (dualB D a hh (S ω) N)| ≤ 1 := fun ω =>
    abs_lap_le_one _ (hμs N) (dualB_pos ha _ _).le
  have iT : Integrable (fun ω => dualAlive D a K hh (S ω) N * dualKill D a c q t hh (S ω) N *
      lap (μs N) (dualB D a hh (S ω) N)) P := by
    refine integrable_of_abs_le ((mA.mul mκ).mul (mlap.comp mB)) 1 fun ω => ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (bA ω).1, abs_of_pos (bκ ω).1]
    have := mul_le_mul (bκ ω).2 (blap ω) (abs_nonneg _) zero_le_one
    have := mul_le_mul (bA ω).2 this (mul_nonneg (bκ ω).1.le (abs_nonneg _)) zero_le_one
    simpa only [one_mul, mul_assoc] using this
  have iκ : Integrable (fun ω => dualKill D a c q t hh (S ω) N) P :=
    integrable_of_abs_le mκ 1 fun ω => by rw [abs_of_pos (bκ ω).1]; exact (bκ ω).2
  have iA : Integrable (fun ω => dualAlive D a K hh (S ω) N) P :=
    integrable_of_abs_le mA 1 fun ω => by rw [abs_of_nonneg (bA ω).1]; exact (bA ω).2
  have hent : |u N - ∫ ω, dualKill D a c q t hh (S ω) N ∂P| ≤ η + (1 - α N) := by
    have hpt : ∀ ω, |dualAlive D a K hh (S ω) N * dualKill D a c q t hh (S ω) N *
        lap (μs N) (dualB D a hh (S ω) N) - dualKill D a c q t hh (S ω) N|
        ≤ η + (1 - dualAlive D a K hh (S ω) N) := by
      intro ω
      set A := dualAlive D a K hh (S ω) N
      set κ := dualKill D a c q t hh (S ω) N
      set l := lap (μs N) (dualB D a hh (S ω) N)
      have e : A * κ * l - κ = A * κ * (l - 1) - (1 - A) * κ := by ring
      rw [e]
      have h1 : |A * κ * (l - 1)| ≤ η := by
        rcases eq_or_ne A 0 with h0 | h0
        · rw [h0]; simpa using hη0
        · have hb := hη _ (mem_of_dualAlive_ne_zero h0)
          rw [abs_mul, abs_mul, abs_of_nonneg (bA ω).1, abs_of_pos (bκ ω).1]
          have := mul_le_mul (bκ ω).2 hb (abs_nonneg _) zero_le_one
          have := mul_le_mul (bA ω).2 this (mul_nonneg (bκ ω).1.le (abs_nonneg _)) zero_le_one
          linarith
      have h2 : |(1 - A) * κ| ≤ 1 - A := by
        rw [abs_mul, abs_of_nonneg (by linarith [bA ω]), abs_of_pos (bκ ω).1]
        nlinarith [bA ω, bκ ω]
      exact (abs_sub _ _).trans (add_le_add h1 h2)
    have e : u N - ∫ ω, dualKill D a c q t hh (S ω) N ∂P =
        ∫ ω, (dualAlive D a K hh (S ω) N * dualKill D a c q t hh (S ω) N *
          lap (μs N) (dualB D a hh (S ω) N) - dualKill D a c q t hh (S ω) N) ∂P :=
      (integral_sub iT iκ).symm
    rw [e]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |dualAlive D a K hh (S ω) N * dualKill D a c q t hh (S ω) N *
          lap (μs N) (dualB D a hh (S ω) N) - dualKill D a c q t hh (S ω) N| ∂P
        ≤ ∫ ω, (η + (1 - dualAlive D a K hh (S ω) N)) ∂P :=
          integral_mono (iT.sub iκ).abs ((integrable_const η).add
            ((integrable_const 1).sub iA)) hpt
      _ = η + (1 - α N) := by
          have i1A : Integrable (fun ω => 1 - dualAlive D a K hh (S ω) N) P :=
            (integrable_const 1).sub iA
          rw [integral_add (integrable_const η) i1A, integral_sub (integrable_const 1) iA]
          simp [hα]
  rw [← hu0]
  calc |u 0 - ∫ ω, dualKill D a c q t hh (S ω) N ∂P|
      ≤ |u 0 - u N| + |u N - ∫ ω, dualKill D a c q t hh (S ω) N ∂P| := abs_sub_le _ _ _
    _ ≤ (∑ k ∈ Finset.range N, ε k + (α 0 - α N)) + (η + (1 - α N)) := add_le_add htel hent
    _ = _ := by rw [hα0]; ring

end Step

end OpenClock
end BlockBand.Endpoints.Clock
