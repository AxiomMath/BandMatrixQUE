module

public import BlockBand.Diffusion.Process.KolmogorovExtension
public import BlockBand.Diffusion.Process.KolmogorovChentsov
public import BlockBand.Diffusion.Process.TransitionFdd
public import Mathlib.Data.Fin.VecNotation

/-!
# Bridge processes with continuous paths from transition densities

**Input.**  A complete separable metric state space `α` (Borel), a σ-finite reference measure
`ν` on `α`, a transition density `q : ℝ → α → α → ℝ≥0∞` (jointly measurable in the two space
variables for each time, Chapman–Kolmogorov for positive times, **no** Markov property needed),
a start `z`, an endpoint `e`, a duration `t > 0` with `0 < q t z e < ∞`, and Chentsov-type moment
bounds `BridgeMomentBound` on the bridge fdd measures (two-point bounds for interior times,
one-point bounds to the fixed endpoints, exponents `p > 0`, `γ > 1`).

**Output** (`isBridgeProcess_bridgeProcess`, `exists_isBridgeProcess`).  On
`Ω = (Ioo 0 t → α)` with the Kolmogorov extension `bridgeRawMeasure` of the bridge family,
the process `bridgeProcess` satisfies `IsBridgeProcess`: a probability measure, every `Z s`
measurable, **every** path continuous on `ℝ` (in particular on `[0, t]`), `Z 0 = z` and
`Z t = e` almost surely, and for all `0 < t₁ < ⋯ < t_k < t` and measurable `F ≥ 0`,
`∫⁻ F(Z_{t₁},…,Z_{t_k}) dP = ∫⁻ F(zs) · bridgeFddDensity q z e t ts zs d(ν ⊗ ⋯ ⊗ ν)`.
This is the generic form of `IsBaseBridge` (there `α = ℝ × ℝ`, `ν = volume`,
`q = ENNReal.ofReal ∘ p`, `e = (0,0)`).

**Moment bounds at the endpoints.**  Convergence in probability `Z_s → z`
(`s → 0`) and `Z_s → e` (`s → t`) alone does **not** give almost-sure continuity of the paths at
the endpoints; we therefore require the Chentsov moment bound up to the endpoints
(`BridgeMomentBound.start`, `.finish`), which implies these convergences in probability.
`BridgeMomentBound.ends` (`d(z,e)^p ≤ M t^γ`) only fixes the constant `M`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- **A bridge process** from `z` to `e` of length `t` for the kernel `q` with reference measure
`ν` (generic form of `IsBaseBridge`). -/
structure IsBridgeProcess {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace α]
    (P : Measure Ω) (ν : Measure α) (q : ℝ → α → α → ℝ≥0∞) (z e : α) (t : ℝ)
    (Z : ℝ → Ω → α) : Prop where
  prob : IsProbabilityMeasure P
  meas : ∀ s, Measurable (Z s)
  paths : ∀ᵐ ω ∂P, ContinuousOn (fun s => Z s ω) (Icc 0 t) ∧ Z 0 ω = z ∧ Z t ω = e
  fdd : ∀ (k : ℕ) (ts : Fin k → ℝ), StrictMono ts → (∀ i, 0 < ts i ∧ ts i < t) →
    ∀ F : (Fin k → α) → ℝ≥0∞, Measurable F →
      ∫⁻ ω, F (fun i => Z (ts i) ω) ∂P =
        ∫⁻ zs, F zs * bridgeFddDensity q z e t ts zs ∂(Measure.pi fun _ : Fin k => ν)

/-- Chentsov-type moment bounds for the bridge fdd measures, including the fixed endpoints. -/
structure BridgeMomentBound [PseudoEMetricSpace α] (ν : Measure α) (q : ℝ → α → α → ℝ≥0∞)
    (z e : α) (t p γ M : ℝ) : Prop where
  interior : ∀ r s : ℝ, 0 < r → r < s → s < t →
    ∫⁻ zs, edist (zs 0) (zs 1) ^ p ∂(bridgeFddMeasure ν q z e t ![r, s]) ≤
      ENNReal.ofReal (M * (s - r) ^ γ)
  start : ∀ s : ℝ, 0 < s → s < t →
    ∫⁻ zs, edist z (zs 0) ^ p ∂(bridgeFddMeasure ν q z e t ![s]) ≤ ENNReal.ofReal (M * s ^ γ)
  finish : ∀ s : ℝ, 0 < s → s < t →
    ∫⁻ zs, edist (zs 0) e ^ p ∂(bridgeFddMeasure ν q z e t ![s]) ≤
      ENNReal.ofReal (M * (t - s) ^ γ)
  ends : edist z e ^ p ≤ ENNReal.ofReal (M * t ^ γ)

/-- The raw bridge process on `Ioo 0 t → α`: coordinates in the interior, `z` at times `≤ 0`,
`e` at times `≥ t`. -/
def bridgeRawProcess (z e : α) (t : ℝ) (s : ℝ) (ω : Ioo (0 : ℝ) t → α) : α :=
  if h : s ∈ Ioo 0 t then ω ⟨s, h⟩ else if s ≤ 0 then z else e

omit [MeasurableSpace α] in
theorem bridgeRawProcess_of_mem (z e : α) {t s : ℝ} (h : s ∈ Ioo 0 t) (ω : Ioo (0 : ℝ) t → α) :
    bridgeRawProcess z e t s ω = ω ⟨s, h⟩ := by
  simp [bridgeRawProcess, h]

omit [MeasurableSpace α] in
theorem bridgeRawProcess_zero (z e : α) (t : ℝ) (ω : Ioo (0 : ℝ) t → α) :
    bridgeRawProcess z e t 0 ω = z := by
  simp [bridgeRawProcess]

omit [MeasurableSpace α] in
theorem bridgeRawProcess_self (z e : α) {t : ℝ} (ht : 0 < t) (ω : Ioo (0 : ℝ) t → α) :
    bridgeRawProcess z e t t ω = e := by
  simp [bridgeRawProcess, not_le.2 ht]

theorem measurable_bridgeRawProcess (z e : α) (t s : ℝ) :
    Measurable (bridgeRawProcess z e t s) := by
  by_cases h : s ∈ Ioo 0 t
  · have : bridgeRawProcess z e t s = fun ω => ω ⟨s, h⟩ :=
      funext fun ω => bridgeRawProcess_of_mem z e h ω
    rw [this]
    exact measurable_pi_apply _
  · have : bridgeRawProcess z e t s = fun _ => if s ≤ 0 then z else e :=
      funext fun ω => by simp [bridgeRawProcess, h]
    rw [this]
    exact measurable_const

variable [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α] [BorelSpace α]
  {ν : Measure α} [SigmaFinite ν] {q : ℝ → α → α → ℝ≥0∞}

/-- The Kolmogorov extension of the bridge family on `Ioo 0 t → α`. -/
def bridgeRawMeasure (ν : Measure α) [SigmaFinite ν] (q : ℝ → α → α → ℝ≥0∞)
    (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2) (hCK : ChapmanKolmogorov ν q)
    (z e : α) {t : ℝ} (h0 : q t z e ≠ 0) (htop : q t z e ≠ ∞) : Measure (Ioo (0 : ℝ) t → α) :=
  haveI : ∀ J, IsProbabilityMeasure (bridgeFamily ν q z e t J) := fun J =>
    isProbabilityMeasure_bridgeFamily hq hCK z e h0 htop J
  kolmogorovExtension (X := fun _ : Ioo (0 : ℝ) t => α) (bridgeFamily ν q z e t)
    (isProjectiveMeasureFamily_bridgeFamily hq hCK z e t)

section RawMeasure

variable (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2) (hCK : ChapmanKolmogorov ν q)
  (z e : α) {t : ℝ} (h0 : q t z e ≠ 0) (htop : q t z e ≠ ∞)

theorem isProjectiveLimit_bridgeRawMeasure :
    IsProjectiveLimit (α := fun _ : Ioo (0 : ℝ) t => α) (bridgeRawMeasure ν q hq hCK z e h0 htop)
      (bridgeFamily ν q z e t) :=
  haveI : ∀ J, IsProbabilityMeasure (bridgeFamily ν q z e t J) := fun J =>
    isProbabilityMeasure_bridgeFamily hq hCK z e h0 htop J
  isProjectiveLimit_kolmogorovExtension _ _

theorem isProbabilityMeasure_bridgeRawMeasure :
    IsProbabilityMeasure (bridgeRawMeasure ν q hq hCK z e h0 htop) :=
  haveI : ∀ J, IsProbabilityMeasure (bridgeFamily ν q z e t J) := fun J =>
    isProbabilityMeasure_bridgeFamily hq hCK z e h0 htop J
  (isProjectiveLimit_bridgeRawMeasure hq hCK z e h0 htop).isProbabilityMeasure

/-- Integrals of functions of finitely many interior coordinates under the raw bridge measure
are bridge fdd integrals. -/
theorem lintegral_eval_bridgeRawMeasure {m : ℕ} (u : Fin m → Ioo (0 : ℝ) t) (hu : StrictMono u)
    (G : (Fin m → α) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ ω, G (fun i => ω (u i)) ∂(bridgeRawMeasure ν q hq hCK z e h0 htop) =
      ∫⁻ zs, G zs ∂(bridgeFddMeasure ν q z e t fun i => (u i : ℝ)) := by
  rw [← map_eval_of_isProjectiveLimit_bridgeFamily hq hCK z e t
    (isProjectiveLimit_bridgeRawMeasure hq hCK z e h0 htop) u hu,
    lintegral_map hG (Measurable.of_eval fun _ => measurable_pi_apply _)]

end RawMeasure

/-!
### The bridge process
-/

section Process

variable (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2) (hCK : ChapmanKolmogorov ν q)
  {z e : α} {t : ℝ} (h0 : q t z e ≠ 0) (htop : q t z e ≠ ∞)

theorem strictMono_vecCons_one {β : Type*} [Preorder β] (x : β) :
    StrictMono (![x] : Fin 1 → β) := by
  intro a b hab
  exact absurd hab (by simp [Subsingleton.elim a b])

/-- The bridge moment bounds give the Chentsov bound for the raw bridge process on `[0, t]`. -/
theorem chentsovBound_bridgeRawProcess (ht : 0 < t) {p γ M : ℝ} (hp : 0 < p)
    (hB : BridgeMomentBound ν q z e t p γ M) :
    KolmogorovChentsov.ChentsovBound (bridgeRawMeasure ν q hq hCK z e h0 htop)
      (bridgeRawProcess z e t) t p γ M := by
  have hP := isProbabilityMeasure_bridgeRawMeasure hq hCK z e h0 htop
  have key : ∀ a b, a ∈ Icc 0 t → b ∈ Icc 0 t → a < b →
      ∫⁻ ω, edist (bridgeRawProcess z e t a ω) (bridgeRawProcess z e t b ω) ^ p
        ∂(bridgeRawMeasure ν q hq hCK z e h0 htop) ≤ ENNReal.ofReal (M * |a - b| ^ γ) := by
    intro a b ha hb hab
    rw [abs_sub_comm, abs_of_pos (sub_pos.2 hab)]
    rcases eq_or_lt_of_le ha.1 with ha0 | ha0 <;> rcases eq_or_lt_of_le hb.2 with hbt | hbt
    · subst a b
      simp only [bridgeRawProcess_zero, bridgeRawProcess_self z e ht, lintegral_const,
        measure_univ, mul_one, sub_zero]
      exact hB.ends
    · subst a
      have hbI : b ∈ Ioo 0 t := ⟨hab, hbt⟩
      have h1 := lintegral_eval_bridgeRawMeasure hq hCK z e h0 htop ![⟨b, hbI⟩]
        (strictMono_vecCons_one _) (fun zs => edist z (zs 0) ^ p)
        (((measurable_const.edist (measurable_pi_apply 0))).pow_const p)
      have hts : (fun i => ((![⟨b, hbI⟩] : Fin 1 → Ioo (0 : ℝ) t) i : ℝ)) = ![b] := by
        funext i
        fin_cases i
        rfl
      rw [hts] at h1
      simp only [bridgeRawProcess_zero, bridgeRawProcess_of_mem z e hbI, sub_zero]
      simp only [Matrix.cons_val_zero] at h1
      rw [h1]
      exact hB.start b hbI.1 hbI.2
    · subst b
      have haI : a ∈ Ioo 0 t := ⟨ha0, hab⟩
      have h1 := lintegral_eval_bridgeRawMeasure hq hCK z e h0 htop ![⟨a, haI⟩]
        (strictMono_vecCons_one _) (fun zs => edist (zs 0) e ^ p)
        ((((measurable_pi_apply 0).edist measurable_const)).pow_const p)
      have hts : (fun i => ((![⟨a, haI⟩] : Fin 1 → Ioo (0 : ℝ) t) i : ℝ)) = ![a] := by
        funext i
        fin_cases i
        rfl
      rw [hts] at h1
      simp only [bridgeRawProcess_self z e ht, bridgeRawProcess_of_mem z e haI]
      simp only [Matrix.cons_val_zero] at h1
      rw [h1]
      exact hB.finish a haI.1 haI.2
    · have haI : a ∈ Ioo 0 t := ⟨ha0, hab.trans hbt⟩
      have hbI : b ∈ Ioo 0 t := ⟨ha0.trans hab, hbt⟩
      have hu : StrictMono (![⟨a, haI⟩, ⟨b, hbI⟩] : Fin 2 → Ioo (0 : ℝ) t) := by
        refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
        fin_cases i
        exact Subtype.mk_lt_mk.2 hab
      have h1 := lintegral_eval_bridgeRawMeasure hq hCK z e h0 htop _ hu
        (fun zs => edist (zs 0) (zs 1) ^ p)
        ((((measurable_pi_apply 0).edist (measurable_pi_apply 1))).pow_const p)
      have hts : (fun i => ((![⟨a, haI⟩, ⟨b, hbI⟩] : Fin 2 → Ioo (0 : ℝ) t) i : ℝ)) =
          ![a, b] := by
        funext i
        fin_cases i <;> rfl
      rw [hts] at h1
      simp only [bridgeRawProcess_of_mem z e haI, bridgeRawProcess_of_mem z e hbI]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1
      rw [h1]
      exact hB.interior a b haI.1 hab hbI.2
  intro a ha b hb
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact key a b ha hb hab
  · simp [ENNReal.zero_rpow_of_pos hp]
  · have := key b a hb ha hab
    simpa only [edist_comm, abs_sub_comm] using this

/-- **The bridge process**: the Kolmogorov–Chentsov modification of the raw bridge process. -/
def bridgeProcess (z e : α) (t p γ : ℝ) : ℝ → (Ioo (0 : ℝ) t → α) → α :=
  KolmogorovChentsov.modification (bridgeRawProcess z e t) t p γ

/-- **Bridge process theorem.**  Under Chapman–Kolmogorov, `0 < q t z e < ∞` and the bridge
moment bounds, `bridgeProcess` under `bridgeRawMeasure` is a bridge process from `z` to `e` of
length `t`: continuous paths, fixed endpoints a.s., bridge fdd at all interior times. -/
theorem isBridgeProcess_bridgeProcess (ht : 0 < t) {p γ M : ℝ} (hp : 0 < p) (hγ : 1 < γ)
    (hM : 0 ≤ M) (hB : BridgeMomentBound ν q z e t p γ M) :
    IsBridgeProcess (bridgeRawMeasure ν q hq hCK z e h0 htop) ν q z e t
      (bridgeProcess z e t p γ) := by
  have hX := measurable_bridgeRawProcess z e t
  have hmom := chentsovBound_bridgeRawProcess hq hCK h0 htop ht hp hB
  refine ⟨isProbabilityMeasure_bridgeRawMeasure hq hCK z e h0 htop,
    fun s => KolmogorovChentsov.measurable_modification hX ht hp hγ s, ?_, ?_⟩
  · filter_upwards [KolmogorovChentsov.modification_ae_eq hX hM hp hγ ht hmom
      (s := 0) ⟨le_rfl, ht.le⟩, KolmogorovChentsov.modification_ae_eq hX hM hp hγ ht hmom
      (s := t) ⟨ht.le, le_rfl⟩] with ω hω0 hωt
    refine ⟨(KolmogorovChentsov.continuous_modification ht hp hγ ω).continuousOn, ?_, ?_⟩
    · simp only [bridgeProcess, hω0, bridgeRawProcess_zero]
    · simp only [bridgeProcess, hωt, bridgeRawProcess_self z e ht]
  · intro k ts hts hbd F hF
    have hall : ∀ᵐ ω ∂(bridgeRawMeasure ν q hq hCK z e h0 htop), ∀ i,
        bridgeProcess z e t p γ (ts i) ω = bridgeRawProcess z e t (ts i) ω :=
      ae_all_iff.2 fun i => KolmogorovChentsov.modification_ae_eq hX hM hp hγ ht hmom
        ⟨(hbd i).1.le, (hbd i).2.le⟩
    have hae : ∀ᵐ ω ∂(bridgeRawMeasure ν q hq hCK z e h0 htop),
        F (fun i => bridgeProcess z e t p γ (ts i) ω) = F (fun i => ω ⟨ts i, hbd i⟩) := by
      filter_upwards [hall] with ω hω
      congr 1
      funext i
      rw [hω i, bridgeRawProcess_of_mem z e (hbd i)]
    rw [lintegral_congr_ae hae, lintegral_eval_bridgeRawMeasure hq hCK z e h0 htop
      (fun i => ⟨ts i, hbd i⟩) (fun a b h => hts h) F hF, bridgeFddMeasure,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_bridgeFddDensity hq z e t _) hF]
    refine lintegral_congr fun zs => ?_
    simp only [Pi.mul_apply]
    exact mul_comm _ _

include hq hCK h0 htop in
/-- **Existence of the bridge process** on the canonical space `Ioo 0 t → α`. -/
theorem exists_isBridgeProcess (ht : 0 < t) {p γ M : ℝ} (hp : 0 < p) (hγ : 1 < γ)
    (hM : 0 ≤ M) (hB : BridgeMomentBound ν q z e t p γ M) :
    ∃ (P : Measure (Ioo (0 : ℝ) t → α)) (Z : ℝ → (Ioo (0 : ℝ) t → α) → α),
      IsBridgeProcess P ν q z e t Z ∧ ∀ ω, Continuous fun s => Z s ω :=
  ⟨_, _, isBridgeProcess_bridgeProcess hq hCK h0 htop ht hp hγ hM hB,
    KolmogorovChentsov.continuous_modification ht hp hγ⟩

end Process

end BlockBand.Diffusion
