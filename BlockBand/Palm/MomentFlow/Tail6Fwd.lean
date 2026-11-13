module

public import BlockBand.Palm.MomentFlow.Tail6

/-!
# Measurable forward short flows and Tonelli on the excess

* `truncForward F a ℓ g s u r Φ₀ v ω`: the forward short moment flow on the enumerated
  `r`-sector from a random datum `Φ₀(ω, ·)` at time `s` (`adaptedMass` on
  `cfgMat` with rates truncated at `g`, eigenvalues clamped to `[s,u]`).
  - `measurable_truncForward`: `pathSigma F a a c`-measurable at each time if `Φ₀` is;
  - `continuous_truncForward`: continuous in time for every sample;
  - `truncForward_isSolution`: on samples with all gaps `≥ g` on `[s,u]`, an
    `IsMomentFlowSolution` of the exact short rates with initial value `Φ₀(ω)`.
  With `Φ₀ = Av F_r(s)` this is the flattened flow `g_u`.
* **`tonelli_excess`**: `tonelli_markov` applied to the excess `(X - d)_+` over a deterministic
  continuous bound `d`, on an `m`-measurable set `Gc` where `X` is continuous and `≤ K`: one
  `m`-measurable `B`, `μ(B) ≤ (b-a)(δ+Kp)/t`, and `∫_a^b X ≤ ∫_a^b d + t` on `Gc \ B`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory intervalIntegral
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm.RelativeLocalization
open scoped NNReal

variable {N : ℕ}

/-- Coefficient field (forward time `t = v - s`) of the truncated forward short flow. -/
def fwdCoeff (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ℓ : ℕ) (g s u : ℝ) (r : ℕ) :
    ℝ≥0 → FlowSample N → Fin (sectorCard N r) → Fin (sectorCard N r) → ℝ :=
  fun t ω => cfgMat (cfgRate N (clampEig F a s u ω (s + t)) ℓ g) r

/-- Initial datum `Φ₀(ω, ·)` on the enumerated sector. -/
def fwdDatum (r : ℕ) (Φ₀ : FlowSample N → Occ N → ℝ) : FlowSample N → Fin (sectorCard N r) → ℝ :=
  fun ω p => Φ₀ ω (sectorEnum N r p)

/-- **The measurable forward short flow** from a random initial datum `Φ₀` at time `s`
(truncation level `g`). -/
def truncForward (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ℓ : ℕ) (g s u : ℝ) (r : ℕ)
    (Φ₀ : FlowSample N → Occ N → ℝ) (v : ℝ) (ω : FlowSample N) : Occ N → ℝ :=
  cfgExt r (adaptedMass (fwdCoeff F a ℓ g s u r) (fwdDatum r Φ₀) ((v - s).toNNReal : ℝ) ω)

theorem continuous_fwdCoeff {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    (a : ℝ) (ℓ : ℕ) {g : ℝ} (hg : 0 < g) (s u : ℝ) (r : ℕ) (ω : FlowSample N) :
    Continuous fun t => fwdCoeff F a ℓ g s u r t ω := by
  have h1 : Continuous fun t : ℝ≥0 => clampEig F a s u ω (s + t) :=
    continuous_pi fun k => (continuous_flowEigenvalue hF a ω k).comp
      ((continuous_clampT s u).comp (continuous_const.add NNReal.continuous_coe))
  exact continuous_cfgMat_comp ((continuous_cfgRate hN ℓ hg).comp h1) r

theorem measurable_fwdCoeff (F : Matrix (Fin N) (Fin N) ℂ) (hN : 0 < N) {a c : ℝ} (ℓ : ℕ)
    {g : ℝ} (hg : 0 < g) {s u : ℝ} (has : a ≤ s) (hsu : s ≤ u) (huc : u ≤ c) (r : ℕ)
    (t : ℝ≥0) : Measurable[pathSigma F a a c] (fwdCoeff F a ℓ g s u r t) := by
  have hcont : Continuous fun lam : Fin N → ℝ => cfgMat (cfgRate N lam ℓ g) r :=
    continuous_cfgMat_comp (continuous_cfgRate hN ℓ hg) r
  have hlam : Measurable[pathSigma F a a c] fun ω => clampEig F a s u ω (s + t) := by
    refine @Measurable.of_eval _ _ _ (pathSigma F a a c) _ _ fun k => ?_
    have hm := clampT_mem hsu (s + t)
    exact measurable_flowEigenvalue_pathSigma F a a c ⟨has.trans hm.1, hm.2.trans huc⟩ k
  exact hcont.measurable.comp hlam

/-- `𝓛`-measurability of the forward flow at each time, for an `𝓛`-measurable datum. -/
theorem measurable_truncForward {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (hN : 0 < N) {a c : ℝ} (ℓ : ℕ) {g : ℝ} (hg : 0 < g) {s u : ℝ} (has : a ≤ s) (hsu : s ≤ u)
    (huc : u ≤ c) (r : ℕ) {Φ₀ : FlowSample N → Occ N → ℝ}
    (hΦ₀ : ∀ ζ, Measurable[pathSigma F a a c] fun ω => Φ₀ ω ζ) (v : ℝ) (ζ : Occ N) :
    Measurable[pathSigma F a a c] fun ω => truncForward F a ℓ g s u r Φ₀ v ω ζ := by
  have hd : Measurable[pathSigma F a a c] (fwdDatum r Φ₀) :=
    @measurable_pi_iff _ _ _ (pathSigma F a a c) _ _ |>.mpr fun p => hΦ₀ _
  have h := adaptedMass_measurable (Filtration.const ℝ≥0 (pathSigma F a a c)
      (pathSigma_le F a a c)) (Lc := fwdCoeff F a ℓ g s u r)
    (fun t => measurable_fwdCoeff F hN ℓ hg has hsu huc r t)
    (fun ω => continuous_fwdCoeff hF hN a ℓ hg s u r ω) (v₀ := fwdDatum r Φ₀) hd
    (v - s).toNNReal
  exact (continuous_cfgExt_apply r ζ).measurable.comp h

theorem continuous_truncForward {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (hN : 0 < N) (a : ℝ) (ℓ : ℕ) {g : ℝ} (hg : 0 < g) (s u : ℝ) (r : ℕ)
    (Φ₀ : FlowSample N → Occ N → ℝ) (ω : FlowSample N) (ζ : Occ N) :
    Continuous fun v => truncForward F a ℓ g s u r Φ₀ v ω ζ := by
  have h := adaptedMass_continuous (fun ω => continuous_fwdCoeff hF hN a ℓ hg s u r ω)
    (fwdDatum r Φ₀) ω
  exact (continuous_cfgExt_apply r ζ).comp (h.comp
    (continuous_real_toNNReal.comp (continuous_id.sub continuous_const)))

/-- On samples with all gaps `≥ g > 0` on `[s,u]`, `truncForward` solves the **exact** short
moment flow on `[s,u]` with initial datum `Φ₀(ω)`. -/
theorem truncForward_isSolution {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (hN : 0 < N) (a : ℝ) (ℓ : ℕ) {g : ℝ} (hg : 0 < g) {s u : ℝ} (hsu : s ≤ u) (r : ℕ)
    (Φ₀ : FlowSample N → Occ N → ℝ) (ω : FlowSample N)
    (hgap : ∀ x ∈ Icc s u, ∀ k m : Fin N, k ≠ m →
      g ≤ |flowEigenvalue F a ω x k - flowEigenvalue F a ω x m|) :
    IsMomentFlowSolution (shortFlowRate F a ω ℓ) r s u
        (fun v => truncForward F a ℓ g s u r Φ₀ v ω) ∧
      ∀ ζ ∈ sector N r, truncForward F a ℓ g s u r Φ₀ s ω ζ = Φ₀ ω ζ := by
  set Lc := fwdCoeff F a ℓ g s u r
  have hLc := fun ω => continuous_fwdCoeff hF hN a ℓ hg s u r ω
  obtain ⟨h0, -, hd⟩ := adaptedMass_solution hLc (fwdDatum r Φ₀) ω (sub_nonneg.2 hsu)
  have hrate : ∀ x ∈ Icc s u, cfgRate N (clampEig F a s u ω x) ℓ g = shortFlowRate F a ω ℓ x := by
    intro x hx
    have e : clampEig F a s u ω x = fun k => flowEigenvalue F a ω x k := by
      funext k; simp [clampEig, clampT_of_mem hx]
    rw [e, cfgRate_eq_zero_gap hg.le (hgap x hx), cfgRate_zero_eq_short]
  refine ⟨fun ζ hζ => ⟨?_, fun v hv => ?_⟩, fun ζ hζ => ?_⟩
  · exact (continuous_truncForward hF hN a ℓ hg s u r Φ₀ ω ζ).continuousOn
  · set V : ℝ → Fin (sectorCard N r) → ℝ := fun t => adaptedMass Lc (fwdDatum r Φ₀) t ω
    have hev : (fun v' => V (v' - s) (sectorIndex hζ)) =ᶠ[nhds v]
        fun v' => truncForward F a ℓ g s u r Φ₀ v' ω ζ := by
      filter_upwards [Ioi_mem_nhds hv.1] with v' hv'
      simp only [truncForward, cfgExt_of_mem _ hζ, V]
      rw [Real.coe_toNNReal _ (by linarith [mem_Ioi.1 hv'])]
    have ht : v - s ∈ Ioo (0 : ℝ) (u - s) := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have h1 := hasDerivAt_pi.1 (hd (v - s) ht) (sectorIndex hζ)
    have hρ : HasDerivAt (fun v' : ℝ => v' - s) 1 v := by
      simpa using (hasDerivAt_id v).sub_const s
    have h2 := (h1.scomp v hρ).congr_of_eventuallyEq hev.symm
    have hvI : v ∈ Icc s u := Ioo_subset_Icc_self hv
    have hcoef : realCoeff Lc ω (v - s) = cfgMat (shortFlowRate F a ω ℓ v) r := by
      simp only [realCoeff, Lc, fwdCoeff]
      rw [Real.coe_toNNReal _ ht.1.le, show s + (v - s) = v by ring, hrate v hvI]
    have e := cfgMat_act (shortFlowRate F a ω ℓ v) r
      (fun ζ' => truncForward F a ℓ g s u r Φ₀ v ω ζ') (sectorIndex hζ)
    rw [sectorEnum_index hζ] at e
    have hval : ∀ q, truncForward F a ℓ g s u r Φ₀ v ω (sectorEnum N r q) = V (v - s) q := by
      intro q
      simp only [truncForward, cfgExt_enum, V]
      rw [Real.coe_toNNReal _ ht.1.le]
    simp only [hval] at e
    rw [hcoef, e] at h2
    convert h2 using 1
    simp
  · simp only [truncForward, sub_self, Real.toNNReal_zero, NNReal.coe_zero, cfgExt_of_mem _ hζ]
    have h0' : adaptedMass Lc (fwdDatum r Φ₀) 0 ω = fwdDatum r Φ₀ ω := h0
    rw [h0']
    simp only [fwdDatum, sectorEnum_index hζ]

/-- **Tonelli–Markov on the excess over a deterministic bound.** `X ≤ K` and
continuous in time on an `m`-measurable set `Gc`; deterministic continuous `d ≥ 0`; per-time
`μ{ω ∈ Gc, d(v) + δ < X(v)} ≤ p`. Then one `m`-measurable `B`, `μ(B) ≤ (b-a)(δ + Kp)/t`, with
`∫_a^b X ≤ ∫_a^b d + t` on `Gc \ B`. -/
theorem tonelli_excess {Ω : Type*} (m : MeasurableSpace Ω) {m0 : MeasurableSpace Ω}
    (hm : m ≤ m0) (μ : Measure Ω) [IsProbabilityMeasure μ] {a b : ℝ} (hab : a ≤ b)
    {X : ℝ → Ω → ℝ} {Gc : Set Ω} (hGc : MeasurableSet[m] Gc)
    (hXm : ∀ v ∈ Icc a b, Measurable[m] (X v))
    (hXc : ∀ ω ∈ Gc, ContinuousOn (fun v => X v ω) (Icc a b))
    {K δ p t : ℝ} {d : ℝ → ℝ} (hdc : ContinuousOn d (Icc a b)) (hd0 : ∀ v ∈ Icc a b, 0 ≤ d v)
    (hXK : ∀ ω ∈ Gc, ∀ v ∈ Icc a b, X v ω ≤ K)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hp : 0 ≤ p) (ht : 0 < t)
    (hbad : ∀ v ∈ Icc a b, μ {ω | ω ∈ Gc ∧ d v + δ < X v ω} ≤ ENNReal.ofReal p) :
    ∃ B : Set Ω, MeasurableSet[m] B ∧ μ B ≤ ENNReal.ofReal ((b - a) * (δ + K * p) / t) ∧
      ∀ ω ∈ Gc, ω ∉ B → (∫ v in a..b, X v ω) ≤ (∫ v in a..b, d v) + t := by
  classical
  set Y : ℝ → Ω → ℝ := fun v ω => Gc.indicator (fun ω => max 0 (X v ω - d v)) ω with hY
  have hYm : ∀ v ∈ Icc a b, Measurable[m] (Y v) := fun v hv =>
    ((measurable_const.max ((hXm v hv).sub_const (d v)))).indicator hGc
  have hYc : ∀ ω, ContinuousOn (fun v => Y v ω) (Icc a b) := by
    intro ω
    by_cases hω : ω ∈ Gc
    · simp only [hY, indicator_of_mem hω]
      exact (continuous_max.comp_continuousOn (continuousOn_const.prodMk ((hXc ω hω).sub hdc)) :)
    · simp only [hY, indicator_of_notMem hω]; exact continuousOn_const
  have hY0 : ∀ v ∈ Icc a b, ∀ ω, 0 ≤ Y v ω := fun v _ ω => by
    simp only [hY]; by_cases hω : ω ∈ Gc
    · rw [indicator_of_mem hω]; exact le_max_left _ _
    · rw [indicator_of_notMem hω]
  have hYK : ∀ v ∈ Icc a b, ∀ ω, Y v ω ≤ K := fun v hv ω => by
    simp only [hY]; by_cases hω : ω ∈ Gc
    · rw [indicator_of_mem hω]
      exact max_le hK (by linarith [hXK ω hω v hv, hd0 v hv])
    · rw [indicator_of_notMem hω]; exact hK
  have hYbad : ∀ v ∈ Icc a b, μ {ω | δ < Y v ω} ≤ ENNReal.ofReal p := by
    intro v hv
    refine (measure_mono fun ω hω => ?_).trans (hbad v hv)
    have hω' : δ < Y v ω := hω
    by_cases hG : ω ∈ Gc
    · simp only [hY, indicator_of_mem hG] at hω'
      refine ⟨hG, ?_⟩
      rcases le_total (X v ω - d v) 0 with h | h
      · rw [max_eq_left h] at hω'; linarith
      · rw [max_eq_right h] at hω'; linarith
    · simp only [hY, indicator_of_notMem hG] at hω'; linarith
  obtain ⟨hBm, hBμ⟩ := tonelli_markov m hm μ hab hYm hYc hY0 hYK hK hδ hp ht hYbad
  refine ⟨_, hBm, hBμ, fun ω hω hωB => ?_⟩
  have hle : (∫ v in a..b, Y v ω) ≤ t := not_lt.1 hωB
  have hXi : IntervalIntegrable (fun v => X v ω) volume a b :=
    (hXc ω hω).intervalIntegrable_of_Icc hab
  have hdi : IntervalIntegrable d volume a b := hdc.intervalIntegrable_of_Icc hab
  have hYi : IntervalIntegrable (fun v => Y v ω) volume a b :=
    (hYc ω).intervalIntegrable_of_Icc hab
  have hmono : (∫ v in a..b, X v ω) ≤ ∫ v in a..b, (d v + Y v ω) :=
    intervalIntegral.integral_mono_on hab hXi (hdi.add hYi) fun v hv => by
      simp only [hY, indicator_of_mem hω]
      linarith [le_max_right 0 (X v ω - d v)]
  rw [intervalIntegral.integral_add hdi hYi] at hmono
  linarith

end BlockBand.Palm.MomentFlow
