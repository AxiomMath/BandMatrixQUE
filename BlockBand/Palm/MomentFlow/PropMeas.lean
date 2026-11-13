module

public import BlockBand.Palm.MomentFlow.Steps2TailEq
public import BlockBand.Palm.MomentFlow.BridgeLaw
public import BlockBand.Palm.MomentFlow.Steps2Short
public import BlockBand.Palm.RelativeLocalizationAdapted

/-!
# Tonelli–Markov in time, and measurable backward short-flow rows

* `tonelli_markov` (generic): a process `X(v, ω)` on `[a,b]`, continuous in `v` for every sample,
  `m`-measurable in `ω` for every `v`, `0 ≤ X ≤ K`, with `μ{δ < X(v)} ≤ p` for every `v`, has
  `μ{t < ∫_a^b X(v) dv} ≤ (b-a)(δ + Kp)/t`, and this set is `m`-measurable.
* `truncBackward F a ℓ g s u r ξ v ω`: the time reversal of the adapted Picard solution
  (`adaptedMass`) of the backward short moment flow on the enumerated `r`-sector (`cfgMat`), with
  rates truncated at gap `g` (`cfgRate`) and eigenvalues held constant outside `[s,u]` (`clampT`).
  - `measurable_truncBackward`: each coordinate at each fixed time is
    `pathSigma F a a c`-measurable (`a ≤ s ≤ u ≤ c`);
  - `continuous_truncBackward`: continuous in time for every sample;
  - `truncBackward_isBackward`: on samples whose gaps on `[s,u]` are all `≥ g > 0`, it is an
    `IsBackwardMomentFlow` of the **exact** short rates `shortFlowRate F a ω ℓ` with terminal
    datum `δ_ξ`.
  Joint measurability in `(v, ω)` follows (`measurable_uncurry_of_continuous_of_measurable`) and
  is used inside `tonelli_markov`.
* `exists_forward`: forward moment-flow solutions exist for rates continuous on `[v,u]`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory intervalIntegral
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm.RelativeLocalization
open scoped NNReal

/-- `ω ↦ ∫_a^b g(r, ω) dr` is measurable for `g` continuous in `r`, measurable in `ω`. -/
theorem measurable_intervalIntegral_real {β : Type*} [MeasurableSpace β] (g : ℝ → β → ℝ)
    (hc : ∀ ω, Continuous fun r => g r ω) (hm : ∀ r, Measurable (g r)) (a b : ℝ) :
    Measurable fun ω => ∫ r in a..b, g r ω := by
  have hu : Measurable (Function.uncurry g) := measurable_uncurry_of_continuous_of_measurable hc hm
  have hsw : StronglyMeasurable (Function.uncurry fun (ω : β) (r : ℝ) => g r ω) :=
    (hu.comp measurable_swap).stronglyMeasurable
  have h1 := hsw.integral_prod_right (ν := volume.restrict (Set.Ioc a b))
  have h2 := hsw.integral_prod_right (ν := volume.restrict (Set.Ioc b a))
  have : (fun ω => ∫ r in a..b, g r ω) =
      fun ω => (∫ r in Set.Ioc a b, g r ω) - ∫ r in Set.Ioc b a, g r ω := by
    funext ω; rfl
  rw [this]
  exact h1.measurable.sub h2.measurable

/-- **Tonelli–Markov in time.** -/
theorem tonelli_markov {Ω : Type*} (m : MeasurableSpace Ω) {m0 : MeasurableSpace Ω}
    (hm : m ≤ m0) (μ : Measure Ω) [IsProbabilityMeasure μ] {a b : ℝ} (hab : a ≤ b)
    {X : ℝ → Ω → ℝ} (hXm : ∀ v ∈ Icc a b, Measurable[m] (X v))
    (hXc : ∀ ω, ContinuousOn (fun v => X v ω) (Icc a b))
    {K δ p t : ℝ} (hX0 : ∀ v ∈ Icc a b, ∀ ω, 0 ≤ X v ω)
    (hXK : ∀ v ∈ Icc a b, ∀ ω, X v ω ≤ K) (hK : 0 ≤ K)
    (hδ : 0 ≤ δ) (hp : 0 ≤ p) (ht : 0 < t)
    (hbad : ∀ v ∈ Icc a b, μ {ω | δ < X v ω} ≤ ENNReal.ofReal p) :
    MeasurableSet[m] {ω | t < ∫ v in a..b, X v ω} ∧
      μ {ω | t < ∫ v in a..b, X v ω} ≤ ENNReal.ofReal ((b - a) * (δ + K * p) / t) := by
  set π : ℝ → ℝ := fun v => max a (min v b) with hπ
  have hπc : Continuous π := by fun_prop
  have hπm : ∀ v, π v ∈ Icc a b := fun v => ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hπid : ∀ v ∈ Icc a b, π v = v := fun v hv => by
    simp only [hπ]; rw [min_eq_left hv.2, max_eq_right hv.1]
  set Y : ℝ → Ω → ℝ := fun v ω => X (π v) ω with hY
  have hYc : ∀ ω, Continuous fun v => Y v ω := fun ω =>
    (hXc ω).comp_continuous hπc hπm
  have hYm : ∀ v, Measurable[m] (Y v) := fun v => hXm _ (hπm v)
  have hYm0 : ∀ v, Measurable[m0] (Y v) := fun v => (hYm v).mono hm le_rfl
  have hI : ∀ ω, ∫ v in a..b, X v ω = ∫ v in a..b, Y v ω := fun ω => by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le hab] at hv
    simp only [hY, hπid v hv]
  simp_rw [hI]
  have hmeas : Measurable[m] fun ω => ∫ v in a..b, Y v ω :=
    @measurable_intervalIntegral_real Ω m Y hYc hYm a b
  have hmeas0 : Measurable[m0] fun ω => ∫ v in a..b, Y v ω :=
    @measurable_intervalIntegral_real Ω m0 Y hYc hYm0 a b
  refine ⟨measurableSet_lt measurable_const hmeas, ?_⟩
  have hY0 : ∀ v ω, 0 ≤ Y v ω := fun v ω => hX0 _ (hπm v) ω
  -- pointwise expectation bound
  have hexp : ∀ v ∈ Ioc a b, ∫⁻ ω, ENNReal.ofReal (Y v ω) ∂μ ≤ ENNReal.ofReal (δ + K * p) := by
    intro v hv
    have hvI : v ∈ Icc a b := Ioc_subset_Icc_self hv
    have hpt : ∀ ω, ENNReal.ofReal (Y v ω) ≤ ENNReal.ofReal δ +
        ENNReal.ofReal K * {ω | δ < Y v ω}.indicator 1 ω := by
      intro ω
      by_cases h : δ < Y v ω
      · have hmem : ω ∈ {ω | δ < Y v ω} := h
        rw [indicator_of_mem hmem, Pi.one_apply, mul_one]
        exact (ENNReal.ofReal_le_ofReal (hXK _ (hπm v) ω)).trans le_add_self
      · push Not at h
        exact (ENNReal.ofReal_le_ofReal h).trans le_self_add
    have hS : MeasurableSet[m0] {ω | δ < Y v ω} := measurableSet_lt measurable_const (hYm0 v)
    calc ∫⁻ ω, ENNReal.ofReal (Y v ω) ∂μ
        ≤ ∫⁻ ω, (ENNReal.ofReal δ + ENNReal.ofReal K * {ω | δ < Y v ω}.indicator 1 ω) ∂μ :=
          lintegral_mono hpt
      _ = ENNReal.ofReal δ + ENNReal.ofReal K * μ {ω | δ < Y v ω} := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul _ (measurable_one.indicator hS), lintegral_indicator_one hS]
      _ ≤ ENNReal.ofReal δ + ENNReal.ofReal K * ENNReal.ofReal p := by
          gcongr
          have : {ω | δ < Y v ω} = {ω | δ < X v ω} := by
            ext ω; simp only [hY, hπid v hvI, mem_ofPred_eq]
          rw [this]; exact hbad v hvI
      _ = ENNReal.ofReal (δ + K * p) := by
          rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_add hδ (mul_nonneg hK hp)]
  -- Tonelli
  have hjoint : Measurable (Function.uncurry fun (ω : Ω) (v : ℝ) =>
      ENNReal.ofReal (Y v ω)) := by
    have hu : Measurable (Function.uncurry Y) :=
      @measurable_uncurry_of_continuous_of_measurable Ω ℝ ℝ _ _ _ _ _ _ _ _ _ m0 Y hYc hYm0
    exact ENNReal.measurable_ofReal.comp (hu.comp measurable_swap)
  have hlin : ∫⁻ ω, ENNReal.ofReal (∫ v in a..b, Y v ω) ∂μ ≤
      ENNReal.ofReal ((b - a) * (δ + K * p)) := by
    have hrep : ∀ ω, ENNReal.ofReal (∫ v in a..b, Y v ω) =
        ∫⁻ v in Ioc a b, ENNReal.ofReal (Y v ω) := by
      intro ω
      rw [intervalIntegral.integral_of_le hab]
      refine ofReal_integral_eq_lintegral_ofReal ?_ (Filter.Eventually.of_forall fun v => hY0 v ω)
      exact ((hYc ω).integrableOn_Icc (μ := volume)).mono_set Ioc_subset_Icc_self
    simp_rw [hrep]
    rw [lintegral_lintegral_swap hjoint.aemeasurable]
    calc ∫⁻ v in Ioc a b, ∫⁻ ω, ENNReal.ofReal (Y v ω) ∂μ
        ≤ ∫⁻ _v in Ioc a b, ENNReal.ofReal (δ + K * p) :=
          setLIntegral_mono measurable_const fun v hv => hexp v hv
      _ = ENNReal.ofReal ((b - a) * (δ + K * p)) := by
          rw [setLIntegral_const, Real.volume_Ioc, mul_comm,
            ← ENNReal.ofReal_mul (by linarith)]
  have hsub : {ω | t < ∫ v in a..b, Y v ω} ⊆
      {ω | ENNReal.ofReal t ≤ ENNReal.ofReal (∫ v in a..b, Y v ω)} :=
    fun ω hω => ENNReal.ofReal_le_ofReal (le_of_lt hω)
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp hmeas0).aemeasurable
    (by simpa using ht) ENNReal.ofReal_ne_top).trans ?_
  rw [ENNReal.ofReal_div_of_pos ht]
  exact ENNReal.div_le_div_right hlin _

variable {N : ℕ}

/-- Clamp of a time to `[s, u]`. -/
def clampT (s u x : ℝ) : ℝ := max s (min x u)

theorem continuous_clampT (s u : ℝ) : Continuous (clampT s u) := by
  unfold clampT; fun_prop

theorem clampT_mem {s u : ℝ} (hsu : s ≤ u) (x : ℝ) : clampT s u x ∈ Icc s u :=
  ⟨le_max_left _ _, max_le hsu (min_le_right _ _)⟩

theorem clampT_of_mem {s u x : ℝ} (hx : x ∈ Icc s u) : clampT s u x = x := by
  unfold clampT; rw [min_eq_left hx.2, max_eq_right hx.1]

/-- Eigenvalue vector at the clamped time. -/
def clampEig (F : Matrix (Fin N) (Fin N) ℂ) (a s u : ℝ) (ω : FlowSample N) (x : ℝ) :
    Fin N → ℝ := fun k => flowEigenvalue F a ω (clampT s u x) k

/-- Coefficient field (forward time `t = u - v`) of the truncated backward short flow. -/
def backCoeff (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ℓ : ℕ) (g s u : ℝ) (r : ℕ) :
    ℝ≥0 → FlowSample N → Fin (sectorCard N r) → Fin (sectorCard N r) → ℝ :=
  fun t ω => cfgMat (cfgRate N (clampEig F a s u ω (u - t)) ℓ g) r

/-- Terminal datum `δ_ξ` on the enumerated sector. -/
def backDatum (r : ℕ) (ξ : Occ N) : FlowSample N → Fin (sectorCard N r) → ℝ :=
  fun _ p => deltaCfg ξ (sectorEnum N r p)

/-- **The measurable backward short-flow row** (truncation level `g`): time reversal of the
adapted Picard solution `adaptedMass`. -/
def truncBackward (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ℓ : ℕ) (g s u : ℝ) (r : ℕ)
    (ξ : Occ N) (v : ℝ) (ω : FlowSample N) : Occ N → ℝ :=
  cfgExt r (adaptedMass (backCoeff F a ℓ g s u r) (backDatum r ξ) ((u - v).toNNReal : ℝ) ω)

theorem continuous_cfgExt_apply (r : ℕ) (ζ : Occ N) :
    Continuous fun V : Fin (sectorCard N r) → ℝ => cfgExt r V ζ := by
  unfold cfgExt
  refine continuous_finsetSum _ fun q _ => ?_
  split_ifs
  · exact continuous_apply q
  · exact continuous_const

theorem continuous_backCoeff {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    (a : ℝ) (ℓ : ℕ) {g : ℝ} (hg : 0 < g) (s u : ℝ) (r : ℕ) (ω : FlowSample N) :
    Continuous fun t => backCoeff F a ℓ g s u r t ω := by
  have h1 : Continuous fun t : ℝ≥0 => clampEig F a s u ω (u - t) :=
    continuous_pi fun k => (continuous_flowEigenvalue hF a ω k).comp
      ((continuous_clampT s u).comp (continuous_const.sub NNReal.continuous_coe))
  exact continuous_cfgMat_comp ((continuous_cfgRate hN ℓ hg).comp h1) r

theorem measurable_backCoeff (F : Matrix (Fin N) (Fin N) ℂ) (hN : 0 < N) {a c : ℝ} (ℓ : ℕ)
    {g : ℝ} (hg : 0 < g) {s u : ℝ} (has : a ≤ s) (hsu : s ≤ u) (huc : u ≤ c) (r : ℕ)
    (t : ℝ≥0) : Measurable[pathSigma F a a c] (backCoeff F a ℓ g s u r t) := by
  have hcont : Continuous fun lam : Fin N → ℝ => cfgMat (cfgRate N lam ℓ g) r :=
    continuous_cfgMat_comp (continuous_cfgRate hN ℓ hg) r
  have hlam : Measurable[pathSigma F a a c] fun ω => clampEig F a s u ω (u - t) := by
    refine @Measurable.of_eval _ _ _ (pathSigma F a a c) _ _ fun k => ?_
    have hm := clampT_mem hsu (u - t)
    exact measurable_flowEigenvalue_pathSigma F a a c ⟨has.trans hm.1, hm.2.trans huc⟩ k
  exact hcont.measurable.comp hlam

/-- `𝓛`-measurability of each coordinate of the backward row at a fixed time. -/
theorem measurable_truncBackward {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (hN : 0 < N) {a c : ℝ} (ℓ : ℕ) {g : ℝ} (hg : 0 < g) {s u : ℝ} (has : a ≤ s) (hsu : s ≤ u)
    (huc : u ≤ c) (r : ℕ) (ξ : Occ N) (v : ℝ) (ζ : Occ N) :
    Measurable[pathSigma F a a c] fun ω => truncBackward F a ℓ g s u r ξ v ω ζ := by
  have h := adaptedMass_measurable (Filtration.const ℝ≥0 (pathSigma F a a c)
      (pathSigma_le F a a c)) (Lc := backCoeff F a ℓ g s u r)
    (fun t => measurable_backCoeff F hN ℓ hg has hsu huc r t)
    (fun ω => continuous_backCoeff hF hN a ℓ hg s u r ω) (v₀ := backDatum r ξ)
    (by exact measurable_const) (u - v).toNNReal
  exact (continuous_cfgExt_apply r ζ).measurable.comp h

theorem continuous_truncBackward {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (hN : 0 < N) (a : ℝ) (ℓ : ℕ) {g : ℝ} (hg : 0 < g) (s u : ℝ) (r : ℕ) (ξ : Occ N)
    (ω : FlowSample N) (ζ : Occ N) :
    Continuous fun v => truncBackward F a ℓ g s u r ξ v ω ζ := by
  have h := adaptedMass_continuous (fun ω => continuous_backCoeff hF hN a ℓ hg s u r ω)
    (backDatum r ξ) ω
  exact (continuous_cfgExt_apply r ζ).comp (h.comp
    (continuous_real_toNNReal.comp (continuous_const.sub continuous_id)))

/-- Exact (untruncated) short rates in the `cfgRate` form. -/
theorem cfgRate_zero_eq_short (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N)
    (ℓ : ℕ) (x : ℝ) :
    cfgRate N (fun k => flowEigenvalue F a ω x k) ℓ 0 = shortFlowRate F a ω ℓ x := by
  funext i j
  by_cases hij : i = j
  · subst hij
    simp [cfgRate, shortFlowRate, maskRate, flowRate]
  · by_cases hd : labelDist i j < ℓ
    · rw [cfgRate_zero_apply _ ℓ hij hd]
      simp [shortFlowRate, maskRate, hd, pairRate, flowRate]
    · simp [cfgRate, shortFlowRate, maskRate, hd]

/-- On a path whose gaps on `[s,u]` are all `≥ g > 0`, the truncated row is a backward solution
of the exact short flow with terminal datum `δ_ξ`. -/
theorem truncBackward_isBackward {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (hN : 0 < N) (a : ℝ) (ℓ : ℕ) {g : ℝ} (hg : 0 < g) {s u : ℝ} (hsu : s ≤ u) (r : ℕ)
    (ξ : Occ N) (ω : FlowSample N)
    (hgap : ∀ x ∈ Icc s u, ∀ k m : Fin N, k ≠ m →
      g ≤ |flowEigenvalue F a ω x k - flowEigenvalue F a ω x m|) :
    IsBackwardMomentFlow (shortFlowRate F a ω ℓ) r s u
        (fun v => truncBackward F a ℓ g s u r ξ v ω) ∧
      ∀ ζ ∈ sector N r, truncBackward F a ℓ g s u r ξ u ω ζ = deltaCfg ξ ζ := by
  set Lc := backCoeff F a ℓ g s u r
  have hLc := fun ω => continuous_backCoeff hF hN a ℓ hg s u r ω
  obtain ⟨h0, -, hd⟩ := adaptedMass_solution hLc (backDatum r ξ) ω (sub_nonneg.2 hsu)
  have hrate : ∀ x ∈ Icc s u, cfgRate N (clampEig F a s u ω x) ℓ g = shortFlowRate F a ω ℓ x := by
    intro x hx
    have e : clampEig F a s u ω x = fun k => flowEigenvalue F a ω x k := by
      funext k; simp [clampEig, clampT_of_mem hx]
    rw [e, cfgRate_eq_zero_gap hg.le (hgap x hx), cfgRate_zero_eq_short]
  refine ⟨fun ζ hζ => ⟨?_, fun v hv => ?_⟩, fun ζ hζ => ?_⟩
  · exact (continuous_truncBackward hF hN a ℓ hg s u r ξ ω ζ).continuousOn
  · set V : ℝ → Fin (sectorCard N r) → ℝ := fun t => adaptedMass Lc (backDatum r ξ) t ω
    have hev : (fun v' => V (u - v') (sectorIndex hζ)) =ᶠ[nhds v]
        fun v' => truncBackward F a ℓ g s u r ξ v' ω ζ := by
      filter_upwards [Iio_mem_nhds hv.2] with v' hv'
      simp only [truncBackward, cfgExt_of_mem _ hζ, V]
      rw [Real.coe_toNNReal _ (by linarith [mem_Iio.1 hv'])]
    have ht : u - v ∈ Ioo (0 : ℝ) (u - s) := ⟨by linarith [hv.2], by linarith [hv.1]⟩
    have h1 := hasDerivAt_pi.1 (hd (u - v) ht) (sectorIndex hζ)
    have hρ : HasDerivAt (fun v' : ℝ => u - v') (-1) v := by
      simpa using (hasDerivAt_id v).const_sub u
    have h2 := (h1.scomp v hρ).congr_of_eventuallyEq hev.symm
    have hvI : v ∈ Icc s u := Ioo_subset_Icc_self hv
    have hcoef : realCoeff Lc ω (u - v) = cfgMat (shortFlowRate F a ω ℓ v) r := by
      simp only [realCoeff, Lc, backCoeff]
      rw [Real.coe_toNNReal _ ht.1.le, show u - (u - v) = v by ring, hrate v hvI]
    have e := cfgMat_act (shortFlowRate F a ω ℓ v) r
      (fun ζ' => truncBackward F a ℓ g s u r ξ v ω ζ') (sectorIndex hζ)
    rw [sectorEnum_index hζ] at e
    have hval : ∀ q, truncBackward F a ℓ g s u r ξ v ω (sectorEnum N r q) = V (u - v) q := by
      intro q
      simp only [truncBackward, cfgExt_enum, V]
      rw [Real.coe_toNNReal _ ht.1.le]
    simp only [hval] at e
    rw [hcoef, e] at h2
    convert h2 using 1
    simp
  · simp only [truncBackward, sub_self, Real.toNNReal_zero, NNReal.coe_zero, cfgExt_of_mem _ hζ]
    have h0' : adaptedMass Lc (backDatum r ξ) 0 ω = backDatum r ξ ω := h0
    rw [h0']
    simp only [backDatum, sectorEnum_index hζ]

/-- **Forward solutions exist** for rates continuous on `[v,u]` (time reversal of
`exists_backward`). -/
theorem exists_forward {c : ℝ → Fin N → Fin N → ℝ} {v u : ℝ} (hvu : v ≤ u)
    (hc : ContinuousOn c (Icc v u)) (r : ℕ) (f : Occ N → ℝ) :
    ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution c r v u Φ ∧ ∀ ζ ∈ sector N r, Φ v ζ = f ζ := by
  have hmaps : MapsTo (fun t : ℝ => v + u - t) (Icc v u) (Icc v u) := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hc' : ContinuousOn (fun t => c (v + u - t)) (Icc v u) :=
    hc.comp (by fun_prop : Continuous fun t : ℝ => v + u - t).continuousOn hmaps
  obtain ⟨w, hw, hwu⟩ := exists_backward hvu hc' r f
  have hrev := hw.reverse
  have e : (fun t => (fun t => c (v + u - t)) (v + u - t)) = c := by
    funext t; simp only [show v + u - (v + u - t) = t by ring]
  rw [e] at hrev
  refine ⟨_, hrev, fun ζ hζ => ?_⟩
  simp only [show v + u - v = u by ring]
  exact hwu ζ hζ

end BlockBand.Palm.MomentFlow
