module

public import BlockBand.Internal.Contracts.Endpoints

/-!
# Uniform moments of an edge clock after a bounded injection interval

This file proves the edge-clock moment bounds `edgeClockMoments` and `edgeClockMoments_limsup`
from `EdgeClockMomentsContract`.

* Source class: every nonnegative test `q ≤ M` vanishing off the injection interval
  `[t₁, t₁+R]`, `R ≤ R₀` (`IsBoundedInjection`; no continuity is needed). The interval
  source `Q(q) = Σ_k q((k+1)/W) Y_{j;k}/W²` is Loewner monotone in `q ≥ 0` because every
  `Y_{j;k} = 𝒰*P_k𝒰` is positive semidefinite, so `0 ≤ Tr Q(q) ≤ M Tr Q(1_{[t₁,t₁+R]})`
  (`trace_intervalSource_le`).
* All fixed trace moments `E γ^p`, every real `p > 0`: for `p ≥ 1` from the `L^p` bound of the
  contract, for `0 < p < 1` from `x^p ≤ 1 + x` and the `p = 1` bound (probability law).
* Both clocks: the full clock trace `γ = Tr Q` and the near-near clock trace `Tr A`,
  `A = nearClock`, since `0 ≤ Tr A ≤ Tr Q` (`A` is a principal block of the positive semidefinite
  `Q`).

Law: the unabsorbed two-input path `growthPathLaw W b` with matched leads, fixed `0 < b < 1/2`,
bulk energy `-2 < E < 2`. The clock of a test supported in `[t₁, t₁+R]` is zero before its
injection. Expectations of the nonnegative moments are lower Lebesgue integrals, so no
integrability hypothesis is needed.

Quantifiers (`edgeClockMoments`): `b, E, R₀ > 0, p > 0`, then `C = C_{p,R₀}`; then the total
length `T` and `W₀ = W₀(T)`; for `W ≥ W₀`, every preceding length `t₁ ≥ 0`, injection length
`0 ≤ R ≤ R₀`, bound `M`, test `q`, and every path length `j ≤ (t₁+R+R₀)W` (injection plus
propagation by at most `R₀`) with `t₁+R+R₀ ≤ T`: `E (Tr Q_j)^p ≤ M^p C` and
`E (Tr A_j)^p ≤ M^p C`. `C` is chosen before `T` and `t₁`: it is independent of the
length of the preceding path. The critical-limsup form (`edgeClockMoments_limsup`):
`C` first; then at fixed `t₁, R, M, q` and every sequence of lengths `j(W) ≤ (t₁+R+R₀)W`,
`limsup_W E (Tr Q_{j(W)})^p ≤ M^p C` (in `ℝ≥0∞`), and the same for `Tr A`.

No hypothesis besides `EdgeClockMomentsContract` is used; `TagBirthValueContract` is not needed,
since the statement concerns interval sources normalized by `W²`, not tags.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Filter
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Endpoints

/-!
## Vocabulary
-/

/-- The source class of the edge-clock moment lemma: a nonnegative test bounded by `M` and
vanishing off the injection interval `[t₁, t₁+R]` (sources on physical blocks, normalized by
`W²` through `intervalSource`). -/
def IsBoundedInjection (t₁ R M : ℝ) (q : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ q x) ∧ (∀ x, q x ≤ M) ∧ ∀ x, x ∉ Set.Icc t₁ (t₁ + R) → q x = 0

/-- `E γ^p` of the full clock `γ = Tr Q(q)` of the path of length `j`. -/
def edgeClockMoment (b E p : ℝ) (W j : ℕ) (q : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((intervalSource b E W j q ω).trace.re ^ p) ∂growthPathLaw W b

/-- `E (Tr A)^p` of the near-near clock block `A = nearClock` of the path of length `j`. -/
def edgeNearClockMoment (b E p : ℝ) (W j : ℕ) (q : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((nearClock b E W j q ω).trace.re ^ p) ∂growthPathLaw W b

/-!
## Deterministic Loewner comparison
-/

theorem tagResponse_posSemidef (b E : ℝ) (W n k : ℕ) (ω : GrowthPath W) :
    (tagResponse b E W n k ω).PosSemidef := by
  unfold tagResponse
  apply PosSemidef.conjTranspose_mul_mul_same
  unfold tagProjection
  rw [posSemidef_diagonal_iff]
  intro x
  split_ifs <;> simp

theorem intervalSource_posSemidef (b E : ℝ) (W n : ℕ) (q : ℝ → ℝ) (hq : ∀ x, 0 ≤ q x)
    (ω : GrowthPath W) : (intervalSource b E W n q ω).PosSemidef := by
  unfold intervalSource
  refine posSemidef_sum _ fun k _ => ?_
  have hc : (0 : ℂ) ≤ (((q (((k + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 : ℝ)) : ℂ) := by
    rw [Complex.zero_le_real]
    exact div_nonneg (hq _) (sq_nonneg _)
  exact (tagResponse_posSemidef b E W n k ω).smul hc

/-- `Tr Q(q) = Σ_k (q_k/W²) Re Tr Y_{n;k}` as a real number (the imaginary part vanishes). -/
theorem trace_intervalSource (b E : ℝ) (W n : ℕ) (q : ℝ → ℝ) (ω : GrowthPath W) :
    (intervalSource b E W n q ω).trace = ((∑ k ∈ Finset.range n,
      q (((k + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 * (tagResponse b E W n k ω).trace.re : ℝ) : ℂ) := by
  unfold intervalSource
  rw [trace_sum]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [trace_smul, smul_eq_mul]
  have h := (Complex.nonneg_iff.mp (tagResponse_posSemidef b E W n k ω).trace_nonneg).2
  congr 1
  apply Complex.ext <;> simp [← h]

/-- Loewner comparison of the clock traces: `0 ≤ q ≤ M 1_{[t₁,t₁+R]}` gives
`Tr Q(q) ≤ M Tr Q(1_{[t₁,t₁+R]})`. -/
theorem trace_intervalSource_le (b E : ℝ) (W n : ℕ) {t₁ R M : ℝ} {q : ℝ → ℝ}
    (hq : IsBoundedInjection t₁ R M q) (ω : GrowthPath W) :
    (intervalSource b E W n q ω).trace.re ≤
      M * (intervalSource b E W n ((Set.Icc t₁ (t₁ + R)).indicator fun _ => (1 : ℝ)) ω).trace.re := by
  rw [trace_intervalSource, trace_intervalSource, Complex.ofReal_re, Complex.ofReal_re,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hY : 0 ≤ (tagResponse b E W n k ω).trace.re :=
    (Complex.nonneg_iff.mp (tagResponse_posSemidef b E W n k ω).trace_nonneg).1
  set x : ℝ := ((k + 1 : ℕ) : ℝ) / W
  have hqx : q x ≤ M * (Set.Icc t₁ (t₁ + R)).indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ Set.Icc t₁ (t₁ + R)
    · rw [Set.indicator_of_mem hx, mul_one]; exact hq.2.1 x
    · rw [Set.indicator_of_notMem hx, mul_zero, hq.2.2 x hx]
  calc q x / (W : ℝ) ^ 2 * (tagResponse b E W n k ω).trace.re
      ≤ M * (Set.Icc t₁ (t₁ + R)).indicator (fun _ => (1 : ℝ)) x / (W : ℝ) ^ 2 *
          (tagResponse b E W n k ω).trace.re := by gcongr
    _ = _ := by ring

theorem trace_intervalSource_re_nonneg (b E : ℝ) (W n : ℕ) (q : ℝ → ℝ) (hq : ∀ x, 0 ≤ q x)
    (ω : GrowthPath W) : 0 ≤ (intervalSource b E W n q ω).trace.re :=
  (Complex.nonneg_iff.mp (intervalSource_posSemidef b E W n q hq ω).trace_nonneg).1

/-- The near-near clock block is dominated by the full clock: `0 ≤ Tr A ≤ Tr Q`. -/
theorem trace_nearClock_le (b E : ℝ) (W n : ℕ) (q : ℝ → ℝ) (hq : ∀ x, 0 ≤ q x)
    (ω : GrowthPath W) :
    0 ≤ (nearClock b E W n q ω).trace.re ∧
      (nearClock b E W n q ω).trace.re ≤ (intervalSource b E W n q ω).trace.re := by
  have hP := intervalSource_posSemidef b E W n q hq ω
  set Q := intervalSource b E W n q ω
  have hdiag : ∀ x, 0 ≤ (Q x x).re := fun x =>
    (Complex.nonneg_iff.mp (hP.diag_nonneg (i := x))).1
  have hA : (nearClock b E W n q ω).trace.re = ∑ a : Fin W, (Q (0, a) (0, a)).re := by
    simp [nearClock, portBlock, trace, Q]
  have hQ : Q.trace.re = ∑ x : Fin 2 × Fin W, (Q x x).re := by simp [trace]
  rw [hA, hQ, Fintype.sum_prod_type, Fin.sum_univ_two]
  refine ⟨Finset.sum_nonneg fun a _ => hdiag _, ?_⟩
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun a _ => hdiag _)

/-!
## Moments from the contract
-/

theorem isProbabilityMeasure_gueMeasure (ι : Type*) [Fintype ι] (t : NNReal) :
    IsProbabilityMeasure (BlockBand.Internal.Contracts.CoareaPalm.gueMeasure ι t) := by
  unfold BlockBand.Internal.Contracts.CoareaPalm.gueMeasure
    BlockBand.SourceProcess.commonCircularIncrementLaw
  infer_instance

theorem isProbabilityMeasure_ginibreMeasure (ι κ : Type*) [Fintype ι] [Fintype κ] (t : NNReal) :
    IsProbabilityMeasure (BlockBand.Internal.Contracts.Layers.ginibreMeasure ι κ t) := by
  unfold BlockBand.Internal.Contracts.Layers.ginibreMeasure
  infer_instance

theorem isProbabilityMeasure_growthPathLaw (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (growthPathLaw W b) := by
  have h1 : ∀ _ : ℕ, IsProbabilityMeasure (BlockBand.Internal.Contracts.CoareaPalm.gueMeasure
      (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) := fun _ => isProbabilityMeasure_gueMeasure _ _
  have h2 : ∀ _ : ℕ, IsProbabilityMeasure (BlockBand.Internal.Contracts.Layers.ginibreMeasure
      (Fin W) (Fin W) (Real.toNNReal (b / W))) := fun _ => isProbabilityMeasure_ginibreMeasure _ _ _
  unfold growthPathLaw
  infer_instance

/-- The indicator clock moments for `p ≥ 1`, from the contract's `L^p` bound. -/
theorem indicator_moment_le_of_eLpNorm {W : ℕ} {b : ℝ} {f : GrowthPath W → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) {p C : ℝ} (hp : 1 ≤ p)
    (h : eLpNorm (fun ω => (f ω : ℂ)) (ENNReal.ofReal p) (growthPathLaw W b) ≤ ENNReal.ofReal C) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂growthPathLaw W b ≤ ENNReal.ofReal (C ^ p) := by
  have hp0 : 0 < p := by linarith
  have hfin : eLpNorm (fun ω => (f ω : ℂ)) (ENNReal.ofReal p) (growthPathLaw W b) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hmeas := aestronglyMeasurable_of_eLpNorm_ne_top hfin
  have hne0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 ENNReal.ofReal_ne_top hmeas,
    ENNReal.toReal_ofReal hp0.le] at h
  have hint : ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂growthPathLaw W b =
      ∫⁻ ω, ‖(f ω : ℂ)‖ₑ ^ p ∂growthPathLaw W b := by
    refine lintegral_congr fun ω => ?_
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hf0 ω),
      ENNReal.ofReal_rpow_of_nonneg (hf0 ω) hp0.le]
  rw [hint]
  have h2 := ENNReal.rpow_le_rpow h hp0.le
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one] at h2
  by_cases hC : 0 ≤ C
  · rwa [ENNReal.ofReal_rpow_of_nonneg hC hp0.le] at h2
  · rw [ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp hC)), ENNReal.zero_rpow_of_pos hp0] at h2
    exact h2.trans bot_le

/-- Moments of order `0 < p ≤ 1` from the first moment: `x^p ≤ 1 + x` on a probability space. -/
theorem moment_le_one_add {W : ℕ} {b : ℝ} {f : GrowthPath W → ℝ} (hf0 : ∀ ω, 0 ≤ f ω)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂growthPathLaw W b ≤
      1 + ∫⁻ ω, ENNReal.ofReal (f ω ^ (1 : ℝ)) ∂growthPathLaw W b := by
  have := isProbabilityMeasure_growthPathLaw W b
  calc ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂growthPathLaw W b
      ≤ ∫⁻ ω, (1 + ENNReal.ofReal (f ω ^ (1 : ℝ))) ∂growthPathLaw W b := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (Real.rpow_nonneg (hf0 ω) _)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.rpow_one]
        rcases le_total (f ω) 1 with h | h
        · have := Real.rpow_le_one (hf0 ω) h hp0.le
          linarith [hf0 ω]
        · have := Real.rpow_le_rpow_of_exponent_le h hp1
          rw [Real.rpow_one] at this
          linarith
    _ = 1 + ∫⁻ ω, ENNReal.ofReal (f ω ^ (1 : ℝ)) ∂growthPathLaw W b := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

/-!
## The edge-clock moment lemma
-/

/-- Law:
`growthPathLaw W b`, fixed
`0 < b < 1/2`, bulk `E`.
For `R₀ > 0` and every fixed moment order `p > 0` there is
`C = C_{p,R₀}`, chosen before the total length `T` and the preceding length `t₁` (constants
independent of the length of the preceding path); then `W₀ = W₀(T)`; for `W ≥ W₀`,
every clock injected during `[t₁, t₁+R]`, `R ≤ R₀`, by a nonnegative test `q ≤ M`
(`IsBoundedInjection`), and every length `j ≤ (t₁+R+R₀)W` (injection, then propagation for
at most another `R₀`):
`E (Tr Q_j)^p ≤ M^p C` and `E (Tr A_j)^p ≤ M^p C`, `A = nearClock`.
-/
theorem edgeClockMoments (hECM : EdgeClockMomentsContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ R₀ p : ℝ, 0 < R₀ → 0 < p →
      ∃ C : ℝ, ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ (t₁ R M : ℝ) (q : ℝ → ℝ),
        0 ≤ t₁ → 0 ≤ R → R ≤ R₀ → t₁ + R + R₀ ≤ T → IsBoundedInjection t₁ R M q →
        ∀ j : ℕ, (j : ℝ) ≤ (t₁ + R + R₀) * W →
          edgeClockMoment b E p W j q ≤ ENNReal.ofReal (M ^ p * C) ∧
            edgeNearClockMoment b E p W j q ≤ ENNReal.ofReal (M ^ p * C) := by
  intro b hb hb' E hE hE' R₀ p hR₀ hp
  -- the contract at exponent `max p 1`
  obtain ⟨C₁, hC₁⟩ := hECM b hb hb' E hE hE' R₀ (max p 1) hR₀ (le_max_right _ _)
  -- the indicator moment bound `Cind` at exponent `p`
  let Cind : ℝ := if 1 ≤ p then max C₁ 0 ^ p else 1 + max C₁ 0
  refine ⟨Cind, fun T => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hC₁ T
  refine ⟨W₀, fun W hW t₁ R M q ht₁ hR hRR₀ hT hq j hj => ?_⟩
  set ind : ℝ → ℝ := (Set.Icc t₁ (t₁ + R)).indicator fun _ => (1 : ℝ)
  have hind0 : ∀ x, 0 ≤ ind x := fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hM : 0 ≤ M := (hq.1 0).trans (hq.2.1 0)
  set g : GrowthPath W → ℝ := fun ω => (intervalSource b E W j ind ω).trace.re
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => trace_intervalSource_re_nonneg b E W j ind hind0 ω
  have hgc : (fun ω => (intervalSource b E W j ind ω).trace) = fun ω => ((g ω : ℝ) : ℂ) := by
    funext ω
    simp only [g]
    rw [trace_intervalSource b E W j ind ω, Complex.ofReal_re]
  have hcon := hW₀ W hW t₁ R ht₁ hR hRR₀ hT j hj
  rw [hgc] at hcon
  -- indicator moment at `p`
  have hindmom : ∫⁻ ω, ENNReal.ofReal (g ω ^ p) ∂growthPathLaw W b ≤ ENNReal.ofReal Cind := by
    have hcon' : eLpNorm (fun ω => ((g ω : ℝ) : ℂ)) (ENNReal.ofReal (max p 1))
        (growthPathLaw W b) ≤ ENNReal.ofReal (max C₁ 0) :=
      hcon.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    by_cases hp1 : 1 ≤ p
    · have hmx : max p 1 = p := max_eq_left hp1
      rw [hmx] at hcon'
      simpa [Cind, hp1] using indicator_moment_le_of_eLpNorm hg0 hp1 hcon'
    · have hmx : max p 1 = 1 := max_eq_right (le_of_lt (not_le.mp hp1))
      rw [hmx] at hcon'
      have h1 := indicator_moment_le_of_eLpNorm hg0 le_rfl hcon'
      rw [Real.rpow_one] at h1
      refine (moment_le_one_add hg0 hp (le_of_lt (not_le.mp hp1))).trans ?_
      simp only [Cind, hp1, ite_false]
      rw [ENNReal.ofReal_add zero_le_one (le_max_right _ _), ENNReal.ofReal_one]
      gcongr
  -- pointwise comparison of the moments
  have hscale : ∫⁻ ω, ENNReal.ofReal ((M * g ω) ^ p) ∂growthPathLaw W b ≤
      ENNReal.ofReal (M ^ p * Cind) := by
    calc ∫⁻ ω, ENNReal.ofReal ((M * g ω) ^ p) ∂growthPathLaw W b
        = ∫⁻ ω, ENNReal.ofReal (M ^ p) * ENNReal.ofReal (g ω ^ p) ∂growthPathLaw W b := by
          refine lintegral_congr fun ω => ?_
          rw [Real.mul_rpow hM (hg0 ω), ENNReal.ofReal_mul (Real.rpow_nonneg hM _)]
      _ = ENNReal.ofReal (M ^ p) * ∫⁻ ω, ENNReal.ofReal (g ω ^ p) ∂growthPathLaw W b :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (M ^ p) * ENNReal.ofReal Cind := by gcongr
      _ = ENNReal.ofReal (M ^ p * Cind) := (ENNReal.ofReal_mul (Real.rpow_nonneg hM _)).symm
  have hQle : ∀ ω, 0 ≤ (intervalSource b E W j q ω).trace.re ∧
      (intervalSource b E W j q ω).trace.re ≤ M * g ω := fun ω =>
    ⟨trace_intervalSource_re_nonneg b E W j q hq.1 ω, trace_intervalSource_le b E W j hq ω⟩
  constructor
  · refine le_trans (lintegral_mono fun ω => ?_) hscale
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (hQle ω).1 (hQle ω).2 hp.le)
  · refine le_trans (lintegral_mono fun ω => ?_) hscale
    have hA := trace_nearClock_le b E W j q hq.1 ω
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hA.1 (hA.2.trans (hQle ω).2) hp.le)

/-- The edge-clock moment lemma, critical-limsup form. For `R₀ > 0` and `p > 0` there is
`C = C_{p,R₀}`, chosen before the source and the preceding length `t₁`, such that for every
clock injected during `[t₁, t₁+R]` (`0 ≤ t₁`, `0 ≤ R ≤ R₀`, test `q ≤ M`) and every sequence
of path lengths `j(W) ≤ (t₁+R+R₀)W`: `limsup_W E (Tr Q_{j(W)})^p ≤ M^p C` and
`limsup_W E (Tr A_{j(W)})^p ≤ M^p C` (`W → ∞` at fixed `t₁, R, M, q`; limsup in `ℝ≥0∞`). -/
theorem edgeClockMoments_limsup (hECM : EdgeClockMomentsContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ R₀ p : ℝ, 0 < R₀ → 0 < p →
      ∃ C : ℝ, ∀ (t₁ R M : ℝ) (q : ℝ → ℝ), 0 ≤ t₁ → 0 ≤ R → R ≤ R₀ →
        IsBoundedInjection t₁ R M q → ∀ jW : ℕ → ℕ, (∀ W, (jW W : ℝ) ≤ (t₁ + R + R₀) * W) →
          limsup (fun W => edgeClockMoment b E p W (jW W) q) atTop ≤
              ENNReal.ofReal (M ^ p * C) ∧
            limsup (fun W => edgeNearClockMoment b E p W (jW W) q) atTop ≤
              ENNReal.ofReal (M ^ p * C) := by
  intro b hb hb' E hE hE' R₀ p hR₀ hp
  obtain ⟨C, hC⟩ := edgeClockMoments hECM b hb hb' E hE hE' R₀ p hR₀ hp
  refine ⟨C, fun t₁ R M q ht₁ hR hRR₀ hq jW hjW => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hC (t₁ + R + R₀)
  have hev : ∀ᶠ W in atTop, edgeClockMoment b E p W (jW W) q ≤ ENNReal.ofReal (M ^ p * C) ∧
      edgeNearClockMoment b E p W (jW W) q ≤ ENNReal.ofReal (M ^ p * C) :=
    eventually_atTop.2 ⟨W₀, fun W hW => hW₀ W hW t₁ R M q ht₁ hR hRR₀ le_rfl hq (jW W) (hjW W)⟩
  exact ⟨limsup_le_of_le (by isBoundedDefault) (hev.mono fun _ h => h.1),
    limsup_le_of_le (by isBoundedDefault) (hev.mono fun _ h => h.2)⟩

end BlockBand.Endpoints
