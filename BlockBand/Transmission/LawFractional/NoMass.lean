module

public import BlockBand.Transmission.LawFractional.Main
public import BlockBand.Transmission.LawDuality.PowerLimit

/-!
# `noMassAtZero`: the homogeneous limit has no trace mass at zero

The paper uses `Σ_{t_i ≤ ε} t_i^q ≤ ε^{q-p}P_p` for `p < q ≤ 1`, first with `q = 1` to exclude
mass at zero. Here `p = 1/2`, `q = 1`.

* `bump ε`: `s ↦ max(0, 1 - s/ε²)` on `[0,1]` (`= 1` at `0`, `= 0` on `[ε², 1]`);
* `integral_bump_le`: for `0 ⪯ T`,
  `∫ bump_ε d(traceMeasure T) = Σ_i t_i bump_ε(t_i) ≤ ε Tr T^{1/2}`;
* `real_singleton_le`: `ν{0} ≤ ∫ bump_ε dν` for every finite measure `ν` on `[0,1]`;

Proof. Let `(P, μ)` satisfy `IsTransmissionLimit b E 0 P μ` and `t > 0`. The one-time `fdd`
clause with the bounded continuous test `ν ↦ clip(∫ bump_ε dν)` (`clip = max 0 (min · 1)`)
gives `E clip(∫ bump_ε dμ(t)) ≤ limsup_W ε E Tr T_{⌊Wt⌋}^{1/2} ≤ εC(1 + t⁻¹)`. Then
`clip(ν{0}) ≤ inf_n clip(∫ bump_{1/(n+1)} dν)`, whose expectation is `0`.
Measurability: `ν ↦ ∫ g dν` is Giry-measurable (`measurable_integral_continuous`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFractional

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.FractionalBulk BlockBand.Transmission.LawDuality
open scoped ENNReal ComplexOrder BoundedContinuousFunction

/-- `s ↦ max(0, 1 - s/ε²)` on `[0,1]`. -/
def bump (ε : ℝ) : C(unitInterval, ℝ) :=
  ⟨fun s => max 0 (1 - (s : ℝ) / ε ^ 2),
    continuous_const.max (continuous_const.sub (continuous_subtype_val.div_const _))⟩

theorem bump_apply (ε : ℝ) (s : unitInterval) : bump ε s = max 0 (1 - (s : ℝ) / ε ^ 2) := rfl

theorem bump_nonneg (ε : ℝ) (s : unitInterval) : 0 ≤ bump ε s := le_max_left _ _

/-- Pointwise: `x bump_ε(x) ≤ ε x^{1/2}` for `x ≥ 0`, `0 < ε ≤ 1`. -/
theorem bump_point {ε x : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hx : 0 ≤ x) :
    x * bump ε (toUnit x) ≤ ε * x ^ (1 / 2 : ℝ) := by
  rw [bump_apply, toUnit, Set.coe_projIcc, ← Real.sqrt_eq_rpow]
  have hs := Real.sqrt_nonneg x
  by_cases hxe : ε ^ 2 ≤ x
  · have hm : ε ^ 2 ≤ max 0 (min 1 x) := by
      refine le_max_of_le_right (le_min ?_ hxe)
      nlinarith
    have h0 : 1 - max 0 (min 1 x) / ε ^ 2 ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ (by positivity)]; linarith
    rw [max_eq_left h0, mul_zero]
    positivity
  · push Not at hxe
    have hb : max 0 (1 - max 0 (min 1 x) / ε ^ 2) ≤ 1 := by
      refine max_le zero_le_one ?_
      have : 0 ≤ max 0 (min 1 x) / ε ^ 2 := by positivity
      linarith
    have hsq : Real.sqrt x ≤ ε := by
      rw [show ε = Real.sqrt (ε ^ 2) from (Real.sqrt_sq hε.le).symm]
      exact Real.sqrt_le_sqrt hxe.le
    have hxx : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx).symm
    calc x * max 0 (1 - max 0 (min 1 x) / ε ^ 2) ≤ x * 1 := mul_le_mul_of_nonneg_left hb hx
      _ = Real.sqrt x * Real.sqrt x := by rw [mul_one]; exact hxx
      _ ≤ ε * Real.sqrt x := mul_le_mul_of_nonneg_right hsq hs

/-- `∫ bump_ε d(traceMeasure T) ≤ ε Tr T^{1/2}` for `T ⪰ 0`. -/
theorem integral_bump_le {n : Type*} [Fintype n] [DecidableEq n] {T : Matrix n n ℂ}
    (h0 : T.PosSemidef) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ s, bump ε s ∂(traceMeasure T : Measure unitInterval) ≤ ε * fracTrace (1 / 2) T := by
  rw [integral_traceMeasure h0.1 (bump ε).continuous, fracTrace_eq_sum_eigenvalues_psd h0,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Real.coe_toNNReal _ (h0.eigenvalues_nonneg i)]
  exact bump_point hε hε1 (h0.eigenvalues_nonneg i)

/-- `ν{0} ≤ ∫ bump_ε dν`. -/
theorem real_singleton_le (ν : FiniteMeasure unitInterval) (ε : ℝ) :
    (ν : Measure unitInterval).real {0} ≤ ∫ s, bump ε s ∂(ν : Measure unitInterval) := by
  rw [← integral_indicator_one (measurableSet_singleton 0)]
  refine integral_mono ((integrable_const (1 : ℝ)).indicator (measurableSet_singleton 0))
    ((BoundedContinuousFunction.mkOfCompact (bump ε)).integrable _) fun s => ?_
  by_cases hs : s = 0
  · subst hs
    simp [bump_apply]
  · rw [Set.indicator_of_notMem (by simpa using hs)]
    exact bump_nonneg ε s

/-- `clip x = max 0 (min x 1)`. -/
def clip (x : ℝ) : ℝ := max 0 (min x 1)

theorem clip_mem (x : ℝ) : 0 ≤ clip x ∧ clip x ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem continuous_clip : Continuous clip :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clip_mono {x y : ℝ} (h : x ≤ y) : clip x ≤ clip y :=
  max_le_max le_rfl (min_le_min_right _ h)

/-- The bounded continuous test `ν ↦ clip(∫ bump_ε d(ν 0))` on `Fin 1 → 𝓜_f[0,1]`. -/
def bumpTest (ε : ℝ) : BoundedContinuousFunction (Fin 1 → FiniteMeasure unitInterval) ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun ν => clip (∫ s, bump ε s ∂(ν 0 : Measure unitInterval)),
      continuous_clip.comp ((FiniteMeasure.continuous_integral_boundedContinuousFunction
        (BoundedContinuousFunction.mkOfCompact (bump ε))).comp (continuous_apply 0))⟩ 1
    (fun x y => by
      simp only [ContinuousMap.coe_mk]
      obtain ⟨a0, a1⟩ := clip_mem (∫ s, bump ε s ∂(x 0 : Measure unitInterval))
      obtain ⟨b0, b1⟩ := clip_mem (∫ s, bump ε s ∂(y 0 : Measure unitInterval))
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith)

theorem bumpTest_apply (ε : ℝ) (ν : Fin 1 → FiniteMeasure unitInterval) :
    bumpTest ε ν = clip (∫ s, bump ε s ∂(ν 0 : Measure unitInterval)) := rfl

/-- **One-time bound at the limit**: `E clip(∫ bump_ε dμ(t)) ≤ ε max(C, 0)` whenever
`limsup_W E Tr T_{⌊Wt⌋}^{1/2} ≤ C`. -/
theorem limit_bump_le {b E : ℝ} (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (hμ : IsTransmissionLimit b E (fun _ => 0) P μ) {t : ℝ} (ht : 0 < t) {C : ℝ}
    (hC : limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
        (fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω))
        ∂growthPathLaw W b) atTop ≤ ENNReal.ofReal C)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ ω, clip (∫ s, bump ε s ∂(μ t ω : Measure unitInterval)) ∂P ≤ ε * max C 0 := by
  have hlim := hμ.fdd 1 (fun _ => t) (fun _ => ht) (bumpTest ε)
  simp only [bumpTest_apply] at hlim
  have hW : ∀ W : ℕ, ENNReal.ofReal (∫ ω, clip (∫ s, bump ε s
        ∂(transmissionProcess b E (fun _ => 0) W t ω : Measure unitInterval)) ∂growthPathLaw W b) ≤
      ENNReal.ofReal ε * ∫⁻ ω, ENNReal.ofReal
        (fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω))
        ∂growthPathLaw W b := by
    intro W
    have hint := integrable_pathFrac (W := W) (p := 1 / 2) (by norm_num) (by norm_num) hb h1 h2
      ⌊(W : ℝ) * t⌋₊
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun ω => fracTrace_nonneg' _ _), ← ENNReal.ofReal_mul hε.le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun ω => (clip_mem _).1)
      (hint.const_mul ε) ?_
    filter_upwards [SourceMixing.mm_ae_passive (W := W) (b := b) (by linarith) h1 h2 ⌊(W : ℝ) * t⌋₊]
      with ω hω
    have hT := Generator.passiveTransmission_posSemidef (by linarith : b < 1) h1 h2 hω
    have hb' := integral_bump_le hT hε hε1
    have hP0 : 0 ≤ ε * fracTrace (1 / 2) (passiveTransmission b E (pathX b E W ⌊(W : ℝ) * t⌋₊ ω)) :=
      mul_nonneg hε.le (fracTrace_nonneg' _ _)
    exact (max_le_max le_rfl (min_le_left _ _)).trans (max_le hP0 hb')
  have hlimE := (ENNReal.continuous_ofReal.tendsto _).comp hlim
  have hkey : ENNReal.ofReal (∫ ω, clip (∫ s, bump ε s ∂(μ t ω : Measure unitInterval)) ∂P) ≤
      ENNReal.ofReal ε * ENNReal.ofReal C := by
    rw [← hlimE.limsup_eq]
    calc limsup _ atTop ≤ limsup (fun W : ℕ => ENNReal.ofReal ε * ∫⁻ ω, ENNReal.ofReal
          (fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω))
          ∂growthPathLaw W b) atTop := limsup_le_limsup (Eventually.of_forall hW)
      _ = ENNReal.ofReal ε * limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
          (fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω))
          ∂growthPathLaw W b) atTop := ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ε * ENNReal.ofReal C := mul_le_mul_right hC _
  rw [← ENNReal.ofReal_mul hε.le] at hkey
  have hkey' := hkey.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (le_max_left C 0) hε.le))
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hε.le (le_max_right _ _))).1 hkey'

/-- **The field `TransmissionLawContract.noMassAtZero` from the `fractional`
field type.**
-/
theorem noMassAtZero_of_fractional
    (hF : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
      ∀ p : ℝ, 0 < p → p < 1 → ∃ C : ℝ, ∀ t : ℝ, 0 < t →
        limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
            (fracTrace p (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω))
            ∂growthPathLaw W b) atTop ≤ ENNReal.ofReal (C * (1 + t⁻¹))) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
      ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
        ∀ t : ℝ, 0 < t → ∀ᵐ ω ∂P, (μ t ω : Measure unitInterval) {0} = 0 := by
  intro b hb0 hb E h1 h2 Ω _ P μ hμ t ht
  obtain ⟨C, hC⟩ := hF b hb0 hb E h1 h2 (1 / 2) (by norm_num) (by norm_num)
  have hCt := hC t ht
  set C' := max (C * (1 + t⁻¹)) 0
  have hprob := hμ.prob
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n ∧ ε n ≤ 1 := fun n => by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  set h : ℕ → Ω → ℝ := fun n ω => clip (∫ s, bump (ε n) s ∂(μ t ω : Measure unitInterval))
  have hm : ∀ n, Measurable (h n) := fun n =>
    continuous_clip.measurable.comp
      ((measurable_integral_continuous (bump (ε n))).comp (hμ.measurable t ht))
  set g : Ω → ℝ≥0∞ := fun ω => ⨅ n, ENNReal.ofReal (h n ω)
  have hgm : Measurable g := Measurable.iInf fun n => ENNReal.measurable_ofReal.comp (hm n)
  have hgle : ∀ n, ∫⁻ ω, g ω ∂P ≤ ENNReal.ofReal (ε n * C') := by
    intro n
    have hint : Integrable (h n) P := Integrable.of_bound (hm n).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (clip_mem _).1]; exact (clip_mem _).2)
    refine (lintegral_mono fun ω => iInf_le _ n).trans ?_
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun ω => (clip_mem _).1)]
    exact ENNReal.ofReal_le_ofReal (limit_bump_le hb h1 h2 hμ ht hCt (hε n).1 (hε n).2)
  have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (ε n * C')) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const C')
    simpa [ε, one_div] using this
  have hg0 : ∫⁻ ω, g ω ∂P = 0 := le_antisymm (ge_of_tendsto' htend hgle) bot_le
  have hae := (lintegral_eq_zero_iff hgm).1 hg0
  filter_upwards [hae] with ω hω
  have hle : ENNReal.ofReal (clip ((μ t ω : Measure unitInterval).real {0})) ≤ g ω :=
    le_iInf fun n => ENNReal.ofReal_le_ofReal (clip_mono (real_singleton_le _ _))
  rw [hω, Pi.zero_apply, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hle
  have hr : (μ t ω : Measure unitInterval).real {0} = 0 := by
    by_contra hne
    have hpos : 0 < (μ t ω : Measure unitInterval).real {0} :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
    have : 0 < clip ((μ t ω : Measure unitInterval).real {0}) :=
      lt_max_of_lt_right (lt_min hpos one_pos)
    linarith
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hr

/-- **The field `TransmissionLawContract.noMassAtZero` from the input hypotheses.** -/
theorem noMassAtZero_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
      ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
        ∀ t : ℝ, 0 < t → ∀ᵐ ω ∂P, (μ t ω : Measure unitInterval) {0} = 0 :=
  noMassAtZero_of_fractional (fractional_holds hMT hGA hLp hP)

end BlockBand.Transmission.LawFractional
