module

public import BlockBand.Native.CEH.ETH.FlowItoZ
public import BlockBand.Native.CEH.LocalLaw.Tail

/-!
# CEH ETH: exponential-tail controls for the two-resolvent chains

Freedman-type exponential tails for the martingale parts of the two-resolvent chains along the
flow, and the pathwise controls that hold off the tail events.

* `ztl_measure_event_le`: if `(ztl_stop f s, ztl_gate g s, ztl_gateM h s)` is a continuous
  semimartingale, `Q(event) ≤ 2 exp(-a²/(2b))` (`measure_abs_compensated_ge_le`), `a, b > 0`.
* `ztl_smCompensated_eq`, `ztl_bracket_eq`: identification of `smCompensated` with `ztl_mart`
  and of the bracket integral with `∫_{(0,t]} h(r⁺)`, for `t ∈ [0, s]` (no integrability needed:
  both sides are Lebesgue set integrals over `(0, t]`).
* `ztl_control_of_not_mem`: off the event, the control
  `∀ t ∈ Set.Icc 0 (s:ℝ), (∫ r in Set.Ioc 0 t, brk r) ≤ b → |m t| < a`.

**Instances.** `X`: the chain `Re tr(K R₁ A R₂)`
(`isContinuousSemimartingale_reTr_flowResolvent2`), with explicit path functions `ztl_mX`
(value minus initial value minus `∫_{(0,t]}` of the drift
`Re tr(K flowDrift2 R₁ R₂ A m₁ m₂)`) and `ztl_brkX` (bracket density
`(1/N) Σ_x (Re tr(K(R₁E_xR₁AR₂ + R₁AR₂E_xR₂)))²`); `Z`: the imaginary chain
`Re⟨Im R₁ A Im R₂ Aᴴ⟩` (`isContinuousSemimartingale_imChain_flowResolvent`) with `ztl_mZ`
(drift: the `-¼` four-constellation combination) and `ztl_brkZ` (`(1/N) Σ_x (Re fz_D(E_x))²`).
For each: semimartingale identification, tail bound, `smCompensated`/bracket identification and
the control off the event.

Measure: `Q` (probability) for the tail bounds; Lebesgue measure on `ℝ` in the path functions.
The controls are pathwise (no stopping time, no measurability of any bad set).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.SourceProcess.Stochastic.Dyson BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization BlockBand.Native.CEH.Flow
open BlockBand.Native.CEH.Martingale BlockBand.Native.CEH.LocalLaw
open BlockBand.External.CEH (normalizedTrace)
open scoped NNReal ENNReal ComplexConjugate

variable {Ω : Type} {N : ℕ}

/-!
### Generic layer
-/

section Generic

/-- The value process stopped at `s`: `t ↦ f(t ∧ s)` in `ℝ¹`. -/
def ztl_stop (f : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) : ℝ≥0 → Ω → Fin 1 → ℝ :=
  fun t ω _ => f (min t s) ω

/-- The drift gated at `s`: `t ↦ 1_{t ≤ s} g(t)` in `ℝ¹`. -/
def ztl_gate (g : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) : ℝ≥0 → Ω → Fin 1 → ℝ :=
  fun t ω _ => if t ≤ s then g t ω else 0

/-- The bracket density gated at `s`: `t ↦ 1_{t ≤ s} h(t)` as a `1 × 1` matrix. -/
def ztl_gateM (h : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ :=
  fun t ω => Matrix.of fun _ _ => if t ≤ s then h t ω else 0

/-- The compensated path `t ↦ f(t⁺) - f(0) - ∫_{(0,t]} g(r⁺)`. -/
def ztl_mart (f g : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  f t.toNNReal ω - f (0 : ℝ).toNNReal ω - ∫ r in Ioc 0 t, g r.toNNReal ω

/-- The exponential-tail event: `∃ t ≤ s, a ≤ |smCompensated t|` with bracket integral `≤ b`. -/
def ztl_event (f g h : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (a b : ℝ) : Set Ω :=
  {ω | ∃ t ≤ s, a ≤ |smCompensated (ztl_stop f s) (ztl_gate g s) 0 t ω| ∧
    ∫ r in Ioc 0 (t : ℝ), ztl_gateM h s r.toNNReal ω 0 0 ≤ b}

/-- For `t ≥ 0`, the drift integral of `ztl_mart` is the interval integral `∫_0^t`. -/
theorem ztl_mart_eq_intervalIntegral (f g : ℝ≥0 → Ω → ℝ) (ω : Ω) {t : ℝ} (ht : 0 ≤ t) :
    ztl_mart f g ω t =
      f t.toNNReal ω - f (0 : ℝ).toNNReal ω - ∫ r in (0 : ℝ)..t, g r.toNNReal ω := by
  rw [ztl_mart, intervalIntegral.integral_of_le ht]

/-- **Identification of the compensated coordinate** with `ztl_mart`, on `[0, s]`. -/
theorem ztl_smCompensated_eq (f g : ℝ≥0 → Ω → ℝ) {s : ℝ≥0} (ω : Ω) {t : ℝ}
    (ht : t ∈ Icc 0 (s : ℝ)) :
    smCompensated (ztl_stop f s) (ztl_gate g s) 0 t.toNNReal ω = ztl_mart f g ω t := by
  have hts := toNNReal_le_of_mem ht
  have eβ : ∫ r in Ioc 0 t, ztl_gate g s r.toNNReal ω 0 = ∫ r in Ioc 0 t, g r.toNNReal ω := by
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    have hr' : r.toNNReal ≤ s := toNNReal_le_of_mem ⟨hr.1.le, hr.2.trans ht.2⟩
    simp only [ztl_gate, hr', ↓reduceIte]
  unfold smCompensated ztl_mart
  rw [Real.coe_toNNReal _ ht.1, eβ]
  simp only [ztl_stop, min_eq_left hts, min_eq_left (zero_le : (0 : ℝ≥0) ≤ s),
    Real.toNNReal_zero]

/-- **Identification of the bracket integral**, on `[0, s]`. -/
theorem ztl_bracket_eq (h : ℝ≥0 → Ω → ℝ) {s : ℝ≥0} (ω : Ω) {t : ℝ} (ht : t ∈ Icc 0 (s : ℝ)) :
    ∫ r in Ioc 0 ((t.toNNReal : ℝ≥0) : ℝ), ztl_gateM h s r.toNNReal ω 0 0 =
      ∫ r in Ioc 0 t, h r.toNNReal ω := by
  rw [Real.coe_toNNReal _ ht.1]
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  have hr' : r.toNNReal ≤ s := toNNReal_le_of_mem ⟨hr.1.le, hr.2.trans ht.2⟩
  simp only [ztl_gateM, Matrix.of_apply, hr', ↓reduceIte]

/-- **Off the tail event, the control holds.** -/
theorem ztl_control_of_not_mem {f g h : ℝ≥0 → Ω → ℝ} {s : ℝ≥0} {a b : ℝ} {ω : Ω}
    (hω : ω ∉ ztl_event f g h s a b) :
    ∀ t ∈ Set.Icc 0 (s : ℝ), (∫ r in Set.Ioc 0 t, h r.toNNReal ω) ≤ b →
      |ztl_mart f g ω t| < a := by
  intro t ht hb
  by_contra hlt
  push Not at hlt
  exact hω ⟨t.toNNReal, toNNReal_le_of_mem ht,
    by rw [ztl_smCompensated_eq f g ω ht]; exact hlt, by rw [ztl_bracket_eq h ω ht]; exact hb⟩

variable [MeasurableSpace Ω] {Q : Measure Ω}

/-- **Union bound** for a finite family with a common per-event bound `2 exp(-q)`. -/
theorem ztl_measure_iUnion_le {ι : Type} [Fintype ι] (E : ι → Set Ω) {q : ℝ}
    (hE : ∀ j, Q (E j) ≤ ENNReal.ofReal (2 * Real.exp (-q))) :
    Q (⋃ j, E j) ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * (2 * Real.exp (-q))) := by
  calc Q (⋃ j, E j) ≤ ∑ j, Q (E j) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : ι, ENNReal.ofReal (2 * Real.exp (-q)) := Finset.sum_le_sum fun j _ => hE j
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

/-- **Union bound, violation form.** If every `ω ∈ S` violates one of the controls `C j`, and
each `C j` holds off an event `E j` of measure `≤ 2 exp(-q)`, then `Q S ≤ #ι · 2 exp(-q)`.
No measurability of `S` is needed. -/
theorem ztl_measure_le_of_violates {ι : Type} [Fintype ι] (E : ι → Set Ω) (C : ι → Ω → Prop)
    {q : ℝ} (hE : ∀ j, Q (E j) ≤ ENNReal.ofReal (2 * Real.exp (-q)))
    (hC : ∀ j ω, ω ∉ E j → C j ω) (S : Set Ω) (hS : ∀ ω ∈ S, ∃ j, ¬ C j ω) :
    Q S ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * (2 * Real.exp (-q))) := by
  refine (measure_mono fun ω hω => ?_).trans (ztl_measure_iUnion_le E hE)
  obtain ⟨j, hj⟩ := hS ω hω
  exact mem_iUnion.2 ⟨j, by_contra fun hω' => hj (hC j ω hω')⟩

variable [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- **Exponential tail** of the generic event, `a, b > 0`. -/
theorem ztl_measure_event_le {f g h : ℝ≥0 → Ω → ℝ} {s : ℝ≥0}
    (hY : IsContinuousSemimartingale (d := 1) Q 𝓖 (ztl_stop f s) (ztl_gate g s) (ztl_gateM h s))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Q (ztl_event f g h s a b) ≤ ENNReal.ofReal (2 * Real.exp (-(a ^ 2) / (2 * b))) :=
  measure_abs_compensated_ge_le hY s ha hb

/-- **Exponential tail**, `q`-form: `Q(event) ≤ 2 exp(-q)` when `q ≤ a²/(2b)`. -/
theorem ztl_measure_event_le_exp {f g h : ℝ≥0 → Ω → ℝ} {s : ℝ≥0}
    (hY : IsContinuousSemimartingale (d := 1) Q 𝓖 (ztl_stop f s) (ztl_gate g s) (ztl_gateM h s))
    {a b q : ℝ} (ha : 0 < a) (hb : 0 < b) (hq : q ≤ a ^ 2 / (2 * b)) :
    Q (ztl_event f g h s a b) ≤ ENNReal.ofReal (2 * Real.exp (-q)) := by
  refine (ztl_measure_event_le hY ha hb).trans (ENNReal.ofReal_le_ofReal ?_)
  gcongr
  rw [neg_div]
  linarith

end Generic

/-!
### The two-resolvent chain `X = Re tr(K R₁ A R₂)`
-/

section ChainX

/-- The value `Re tr(K R_{1,σ} A R_{2,σ})`. -/
def ztl_valX (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ≥0) (K A : Matrix (Fin N) (Fin N) ℂ) : ℝ≥0 → Ω → ℝ :=
  fun σ ω => reTr K (flowResolvent F G z₁ m₁ s σ ω * A * flowResolvent F G z₂ m₂ s σ ω)

/-- The drift `Re tr(K flowDrift2 R_{1,σ} R_{2,σ} A m₁ m₂)`. -/
def ztl_drfX (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ≥0) (K A : Matrix (Fin N) (Fin N) ℂ) : ℝ≥0 → Ω → ℝ :=
  fun σ ω => reTr K (flowDrift2 (flowResolvent F G z₁ m₁ s σ ω)
    (flowResolvent F G z₂ m₂ s σ ω) A m₁ m₂)

/-- The bracket density `(1/N) Σ_x (Re tr(K(R₁E_xR₁AR₂ + R₁AR₂E_xR₂)))²`. -/
def ztl_bdX (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ≥0) (K A : Matrix (Fin N) (Fin N) ℂ) : ℝ≥0 → Ω → ℝ :=
  fun σ ω => 1 / (N : ℝ) * ∑ x, reTr K (flowResolvent F G z₁ m₁ s σ ω * hermBasis x *
    flowResolvent F G z₁ m₁ s σ ω * A * flowResolvent F G z₂ m₂ s σ ω +
    flowResolvent F G z₁ m₁ s σ ω * A * flowResolvent F G z₂ m₂ s σ ω * hermBasis x *
    flowResolvent F G z₂ m₂ s σ ω) ^ 2

/-- **The path function `m`** of `X`: `Re tr(K R₁(t) A R₂(t)) - Re tr(K R₁(0) A R₂(0)) -
∫_{(0,t]} Re tr(K flowDrift2 R₁(r) R₂(r) A m₁ m₂) dr`, with `R_i(t) = pathR … ω t`. -/
def ztl_mX (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ≥0) (K A : Matrix (Fin N) (Fin N) ℂ) (ω : Ω) (t : ℝ) : ℝ :=
  reTr K (pathR F G z₁ m₁ s ω t * A * pathR F G z₂ m₂ s ω t) -
    reTr K (pathR F G z₁ m₁ s ω 0 * A * pathR F G z₂ m₂ s ω 0) -
    ∫ r in Ioc 0 t, reTr K (flowDrift2 (pathR F G z₁ m₁ s ω r) (pathR F G z₂ m₂ s ω r) A m₁ m₂)

/-- **The path function `brk`** of `X`: the bracket density
`(1/N) Σ_x (Re tr(K(R₁(t)E_xR₁(t)AR₂(t) + R₁(t)AR₂(t)E_xR₂(t))))²`. -/
def ztl_brkX (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ≥0) (K A : Matrix (Fin N) (Fin N) ℂ) (ω : Ω) (t : ℝ) : ℝ :=
  1 / (N : ℝ) * ∑ x, reTr K (pathR F G z₁ m₁ s ω t * hermBasis x * pathR F G z₁ m₁ s ω t * A *
    pathR F G z₂ m₂ s ω t + pathR F G z₁ m₁ s ω t * A * pathR F G z₂ m₂ s ω t * hermBasis x *
    pathR F G z₂ m₂ s ω t) ^ 2

/-- The exponential-tail event of `X`. -/
def ztl_eventX (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ≥0) (K A : Matrix (Fin N) (Fin N) ℂ) (a b : ℝ) : Set Ω :=
  ztl_event (ztl_valX F G z₁ m₁ z₂ m₂ s K A) (ztl_drfX F G z₁ m₁ z₂ m₂ s K A)
    (ztl_bdX F G z₁ m₁ z₂ m₂ s K A) s a b

variable {F : Matrix (Fin N) (Fin N) ℂ} {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}
  {z₁ m₁ z₂ m₂ : ℂ} {s : ℝ≥0} {K A : Matrix (Fin N) (Fin N) ℂ}

theorem ztl_mX_eq (ω : Ω) (t : ℝ) :
    ztl_mX F G z₁ m₁ z₂ m₂ s K A ω t =
      ztl_mart (ztl_valX F G z₁ m₁ z₂ m₂ s K A) (ztl_drfX F G z₁ m₁ z₂ m₂ s K A) ω t := rfl

theorem ztl_brkX_eq (ω : Ω) (t : ℝ) :
    ztl_brkX F G z₁ m₁ z₂ m₂ s K A ω t = ztl_bdX F G z₁ m₁ z₂ m₂ s K A t.toNNReal ω := rfl

/-- `smCompensated` of the process is `ztl_mX`, on `[0, s]`. -/
theorem ztl_smCompensated_X (ω : Ω) {t : ℝ} (ht : t ∈ Icc 0 (s : ℝ)) :
    smCompensated (ztl_stop (ztl_valX F G z₁ m₁ z₂ m₂ s K A) s)
      (ztl_gate (ztl_drfX F G z₁ m₁ z₂ m₂ s K A) s) 0 t.toNNReal ω =
      ztl_mX F G z₁ m₁ z₂ m₂ s K A ω t :=
  ztl_smCompensated_eq _ _ ω ht

/-- The bracket integral of the process is `∫_{(0,t]} ztl_brkX`, on `[0, s]`. -/
theorem ztl_bracket_X (ω : Ω) {t : ℝ} (ht : t ∈ Icc 0 (s : ℝ)) :
    ∫ r in Ioc 0 ((t.toNNReal : ℝ≥0) : ℝ),
        ztl_gateM (ztl_bdX F G z₁ m₁ z₂ m₂ s K A) s r.toNNReal ω 0 0 =
      ∫ r in Ioc 0 t, ztl_brkX F G z₁ m₁ z₂ m₂ s K A ω r :=
  ztl_bracket_eq _ ω ht

/-- **Control of `X` off its tail event**, in the shared shape. -/
theorem ztl_controlX {a b : ℝ} {ω : Ω} (hω : ω ∉ ztl_eventX F G z₁ m₁ z₂ m₂ s K A a b) :
    ∀ t ∈ Set.Icc 0 (s : ℝ), (∫ r in Set.Ioc 0 t, ztl_brkX F G z₁ m₁ z₂ m₂ s K A ω r) ≤ b →
      |ztl_mX F G z₁ m₁ z₂ m₂ s K A ω t| < a :=
  ztl_control_of_not_mem hω

variable [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- The semimartingale theorem, in the stopped/gated form. -/
theorem ztl_semimartingaleX (hG : IsHermitianBrownian Q 𝓖 N G) (hF : F.IsHermitian)
    (hz₁ : z₁.im ≠ 0) (hm₁ : 0 ≤ z₁.im * m₁.im) (hz₂ : z₂.im ≠ 0) (hm₂ : 0 ≤ z₂.im * m₂.im)
    (s : ℝ≥0) (K A : Matrix (Fin N) (Fin N) ℂ) :
    IsContinuousSemimartingale (d := 1) Q 𝓖 (ztl_stop (ztl_valX F G z₁ m₁ z₂ m₂ s K A) s)
      (ztl_gate (ztl_drfX F G z₁ m₁ z₂ m₂ s K A) s)
      (ztl_gateM (ztl_bdX F G z₁ m₁ z₂ m₂ s K A) s) :=
  isContinuousSemimartingale_reTr_flowResolvent2 hG hF hz₁ hm₁ hz₂ hm₂ s K A

/-- **Exponential tail of `X`**: `Q(ztl_eventX … a b) ≤ 2 exp(-a²/(2b))`. -/
theorem ztl_measure_eventX_le (hG : IsHermitianBrownian Q 𝓖 N G) (hF : F.IsHermitian)
    (hz₁ : z₁.im ≠ 0) (hm₁ : 0 ≤ z₁.im * m₁.im) (hz₂ : z₂.im ≠ 0) (hm₂ : 0 ≤ z₂.im * m₂.im)
    (s : ℝ≥0) (K A : Matrix (Fin N) (Fin N) ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Q (ztl_eventX F G z₁ m₁ z₂ m₂ s K A a b) ≤
      ENNReal.ofReal (2 * Real.exp (-(a ^ 2) / (2 * b))) :=
  ztl_measure_event_le (ztl_semimartingaleX hG hF hz₁ hm₁ hz₂ hm₂ s K A) ha hb

end ChainX

/-!
### The imaginary chain `Z = Re⟨Im R₁ A Im R₂ Aᴴ⟩`
-/

section ChainZ

/-- The value `Re⟨Im R_{1,σ} A Im R_{2,σ} Aᴴ⟩`. -/
def ztl_valZ (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ≥0) (A : Matrix (Fin N) (Fin N) ℂ) : ℝ≥0 → Ω → ℝ :=
  fun σ ω => (normalizedTrace (External.CEH.imaginaryPart (flowResolvent F G z₁ m₁ s σ ω) * A *
    External.CEH.imaginaryPart (flowResolvent F G z₂ m₂ s σ ω) * Aᴴ)).re

/-- The drift of `Z`: `-¼` times the four-constellation combination of the flow Itô formula
drifts, `K = N⁻¹Aᴴ`. -/
def ztl_drfZ (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ≥0) (A : Matrix (Fin N) (Fin N) ℂ) : ℝ≥0 → Ω → ℝ :=
  fun σ ω => -(1 / 4) *
    (reTr ((N : ℂ)⁻¹ • Aᴴ) (flowDrift2 (flowResolvent F G z₁ m₁ s σ ω)
        (flowResolvent F G z₂ m₂ s σ ω) A m₁ m₂) -
      reTr ((N : ℂ)⁻¹ • Aᴴ) (flowDrift2 (flowResolvent F G z₁ m₁ s σ ω)
        (flowResolvent F G z₂ m₂ s σ ω)ᴴ A m₁ (conj m₂)) -
      reTr ((N : ℂ)⁻¹ • Aᴴ) (flowDrift2 (flowResolvent F G z₁ m₁ s σ ω)ᴴ
        (flowResolvent F G z₂ m₂ s σ ω) A (conj m₁) m₂) +
      reTr ((N : ℂ)⁻¹ • Aᴴ) (flowDrift2 (flowResolvent F G z₁ m₁ s σ ω)ᴴ
        (flowResolvent F G z₂ m₂ s σ ω)ᴴ A (conj m₁) (conj m₂)))

/-- The bracket density of `Z`, `(1/N) Σ_x (Re fz_D R₁ R₂ A E_x)²`. -/
def ztl_bdZ (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ≥0) (A : Matrix (Fin N) (Fin N) ℂ) : ℝ≥0 → Ω → ℝ :=
  fun σ ω => 1 / (N : ℝ) * ∑ x, (fz_D (flowResolvent F G z₁ m₁ s σ ω)
    (flowResolvent F G z₂ m₂ s σ ω) A (hermBasis x)).re ^ 2

/-- **The path function `m`** of `Z`: `Z(t) - Z(0) - ∫_{(0,t]}` of its drift, along
`R_i(t) = pathR … ω t`. -/
def ztl_mZ (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ≥0) (A : Matrix (Fin N) (Fin N) ℂ) (ω : Ω) (t : ℝ) : ℝ :=
  (normalizedTrace (External.CEH.imaginaryPart (pathR F G z₁ m₁ s ω t) * A *
      External.CEH.imaginaryPart (pathR F G z₂ m₂ s ω t) * Aᴴ)).re -
    (normalizedTrace (External.CEH.imaginaryPart (pathR F G z₁ m₁ s ω 0) * A *
      External.CEH.imaginaryPart (pathR F G z₂ m₂ s ω 0) * Aᴴ)).re -
    ∫ r in Ioc 0 t, -(1 / 4) *
      (reTr ((N : ℂ)⁻¹ • Aᴴ) (flowDrift2 (pathR F G z₁ m₁ s ω r)
          (pathR F G z₂ m₂ s ω r) A m₁ m₂) -
        reTr ((N : ℂ)⁻¹ • Aᴴ) (flowDrift2 (pathR F G z₁ m₁ s ω r)
          (pathR F G z₂ m₂ s ω r)ᴴ A m₁ (conj m₂)) -
        reTr ((N : ℂ)⁻¹ • Aᴴ) (flowDrift2 (pathR F G z₁ m₁ s ω r)ᴴ
          (pathR F G z₂ m₂ s ω r) A (conj m₁) m₂) +
        reTr ((N : ℂ)⁻¹ • Aᴴ) (flowDrift2 (pathR F G z₁ m₁ s ω r)ᴴ
          (pathR F G z₂ m₂ s ω r)ᴴ A (conj m₁) (conj m₂)))

/-- **The path function `brk`** of `Z`: `(1/N) Σ_x (Re fz_D R₁(t) R₂(t) A E_x)²`. -/
def ztl_brkZ (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ≥0) (A : Matrix (Fin N) (Fin N) ℂ) (ω : Ω) (t : ℝ) : ℝ :=
  1 / (N : ℝ) * ∑ x, (fz_D (pathR F G z₁ m₁ s ω t) (pathR F G z₂ m₂ s ω t) A
    (hermBasis x)).re ^ 2

/-- The exponential-tail event of `Z`. -/
def ztl_eventZ (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ≥0) (A : Matrix (Fin N) (Fin N) ℂ) (a b : ℝ) : Set Ω :=
  ztl_event (ztl_valZ F G z₁ m₁ z₂ m₂ s A) (ztl_drfZ F G z₁ m₁ z₂ m₂ s A)
    (ztl_bdZ F G z₁ m₁ z₂ m₂ s A) s a b

variable {F : Matrix (Fin N) (Fin N) ℂ} {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}
  {z₁ m₁ z₂ m₂ : ℂ} {s : ℝ≥0} {A : Matrix (Fin N) (Fin N) ℂ}

theorem ztl_mZ_eq (ω : Ω) (t : ℝ) :
    ztl_mZ F G z₁ m₁ z₂ m₂ s A ω t =
      ztl_mart (ztl_valZ F G z₁ m₁ z₂ m₂ s A) (ztl_drfZ F G z₁ m₁ z₂ m₂ s A) ω t := rfl

theorem ztl_brkZ_eq (ω : Ω) (t : ℝ) :
    ztl_brkZ F G z₁ m₁ z₂ m₂ s A ω t = ztl_bdZ F G z₁ m₁ z₂ m₂ s A t.toNNReal ω := rfl

/-- `smCompensated` of the process `Z` is `ztl_mZ`, on `[0, s]`. -/
theorem ztl_smCompensated_Z (ω : Ω) {t : ℝ} (ht : t ∈ Icc 0 (s : ℝ)) :
    smCompensated (ztl_stop (ztl_valZ F G z₁ m₁ z₂ m₂ s A) s)
      (ztl_gate (ztl_drfZ F G z₁ m₁ z₂ m₂ s A) s) 0 t.toNNReal ω =
      ztl_mZ F G z₁ m₁ z₂ m₂ s A ω t :=
  ztl_smCompensated_eq _ _ ω ht

/-- The bracket integral of the process `Z` is `∫_{(0,t]} ztl_brkZ`, on `[0, s]`. -/
theorem ztl_bracket_Z (ω : Ω) {t : ℝ} (ht : t ∈ Icc 0 (s : ℝ)) :
    ∫ r in Ioc 0 ((t.toNNReal : ℝ≥0) : ℝ),
        ztl_gateM (ztl_bdZ F G z₁ m₁ z₂ m₂ s A) s r.toNNReal ω 0 0 =
      ∫ r in Ioc 0 t, ztl_brkZ F G z₁ m₁ z₂ m₂ s A ω r :=
  ztl_bracket_eq _ ω ht

/-- **Control of `Z` off its tail event**, in the shared shape. -/
theorem ztl_controlZ {a b : ℝ} {ω : Ω} (hω : ω ∉ ztl_eventZ F G z₁ m₁ z₂ m₂ s A a b) :
    ∀ t ∈ Set.Icc 0 (s : ℝ), (∫ r in Set.Ioc 0 t, ztl_brkZ F G z₁ m₁ z₂ m₂ s A ω r) ≤ b →
      |ztl_mZ F G z₁ m₁ z₂ m₂ s A ω t| < a :=
  ztl_control_of_not_mem hω

variable [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- The semimartingale theorem for `Z`, in the stopped/gated form. -/
theorem ztl_semimartingaleZ (hG : IsHermitianBrownian Q 𝓖 N G) (hF : F.IsHermitian)
    (hz₁ : z₁.im ≠ 0) (hm₁ : 0 ≤ z₁.im * m₁.im) (hz₂ : z₂.im ≠ 0) (hm₂ : 0 ≤ z₂.im * m₂.im)
    (s : ℝ≥0) (A : Matrix (Fin N) (Fin N) ℂ) :
    IsContinuousSemimartingale (d := 1) Q 𝓖 (ztl_stop (ztl_valZ F G z₁ m₁ z₂ m₂ s A) s)
      (ztl_gate (ztl_drfZ F G z₁ m₁ z₂ m₂ s A) s)
      (ztl_gateM (ztl_bdZ F G z₁ m₁ z₂ m₂ s A) s) :=
  isContinuousSemimartingale_imChain_flowResolvent hG hF hz₁ hm₁ hz₂ hm₂ s A

/-- **Exponential tail of `Z`**: `Q(ztl_eventZ … a b) ≤ 2 exp(-a²/(2b))`. -/
theorem ztl_measure_eventZ_le (hG : IsHermitianBrownian Q 𝓖 N G) (hF : F.IsHermitian)
    (hz₁ : z₁.im ≠ 0) (hm₁ : 0 ≤ z₁.im * m₁.im) (hz₂ : z₂.im ≠ 0) (hm₂ : 0 ≤ z₂.im * m₂.im)
    (s : ℝ≥0) (A : Matrix (Fin N) (Fin N) ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Q (ztl_eventZ F G z₁ m₁ z₂ m₂ s A a b) ≤
      ENNReal.ofReal (2 * Real.exp (-(a ^ 2) / (2 * b))) :=
  ztl_measure_event_le (ztl_semimartingaleZ hG hF hz₁ hm₁ hz₂ hm₂ s A) ha hb

end ChainZ

end BlockBand.Native.CEH.ETH
