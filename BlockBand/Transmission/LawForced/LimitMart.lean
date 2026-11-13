module

public import BlockBand.Transmission.LawForced.LimitDrift
public import BlockBand.Transmission.LawForced.LimitFubini
public import BlockBand.Transmission.LawDuality.Refined

/-!
# Prop 3 `SubLimitRatioMartingale` from the finite-`W` forced expansion

**`isRatioMartingale_of hRD`**: every subsequential limit `(P, μ)` (any admissible `κ`, every
chamber point `z`, all `x`, including `x ≥ 1`) has martingale increments
`F_z(μ_t) − F_z(μ_s) − ∫_s^t ratioDrift(u, z, μ_u) du`. **`subLimitRatioMartingale_of hRD :
SubLimitRatioMartingale`**.

Route, for a past test `Ψ = Φ(μ(u_l))_l`, `u_l ≤ s`, and `W_n = φ n`:
* finite `W`: `|E_n[ψ_n(F(μ^{⌊W_nt⌋}) − F(μ^{⌊W_ns⌋}) − Σ_r ratioDriftAt_r/W_n)]| ≤
  ‖Φ‖ Σ_r E|ratioDriftError_r| → 0` (`abs_integral_ratio_drift_le`, `RatioDriftSummable` at
  `ε = s`, `T = t`; `ψ_n = testAt` is `𝓕_{⌊W_ns⌋}`-measurable);
* the drift sums converge to `∫_s^t E[Ψ ratioDrift(v, z, μ_v)] dv` (`tendsto_drift_sum`);
* Fubini on the limit (`limit_fubini_bdd`).
No moment bound is used: at a fixed chamber point the drift is bounded uniformly in `ν`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.LawDuality
open scoped NNReal ENNReal BoundedContinuousFunction

theorem integral_sub3 {α : Type*} [MeasurableSpace α] {ρ : Measure α} {f g k : α → ℝ}
    (hf : Integrable f ρ) (hg : Integrable g ρ) (hk : Integrable k ρ) :
    ∫ x, (f x - g x - k x) ∂ρ = ∫ x, f x ∂ρ - ∫ x, g x ∂ρ - ∫ x, k x ∂ρ := by
  have h1 : Integrable (fun x => f x - g x) ρ := hf.sub hg
  rw [integral_sub h1 hk, integral_sub hf hg]

theorem integral_mul_sub3 {α : Type*} [MeasurableSpace α] {ρ : Measure α} {ψ f g k : α → ℝ}
    (hf : Integrable (fun x => ψ x * f x) ρ) (hg : Integrable (fun x => ψ x * g x) ρ)
    (hk : Integrable (fun x => ψ x * k x) ρ) :
    ∫ x, ψ x * (f x - g x - k x) ∂ρ =
      ∫ x, ψ x * f x ∂ρ - ∫ x, ψ x * g x ∂ρ - ∫ x, ψ x * k x ∂ρ := by
  rw [← integral_sub3 hf hg hk]
  exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)

/-- The finite-`W` tested identity split into its three terms. -/
theorem finite_split {b E : ℝ} {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) (hb1 : b < 1)
    (hE1 : -2 < E) (hE2 : E < 2) {p : ℕ} {z : DualCoord p} (hz : z ∈ dualChamber p) {W m : ℕ}
    (uu : Fin m → ℝ) (Φ : BoundedContinuousFunction (Fin m → FiniteMeasure unitInterval) ℝ)
    (s t : ℝ) :
    ∫ ω, testAt b E κ W uu Φ ω * (ratioAt b E κ W ⌊(W : ℝ) * t⌋₊ z ω -
        ratioAt b E κ W ⌊(W : ℝ) * s⌋₊ z ω -
        ∑ r ∈ Finset.Ico ⌊(W : ℝ) * s⌋₊ ⌊(W : ℝ) * t⌋₊, ratioDriftAt b E κ W r z ω / (W : ℝ))
        ∂growthPathLaw W b =
      ∫ ω, testAt b E κ W uu Φ ω *
          transmissionRatio z.1 z.2 (transmissionProcess b E κ W t ω) ∂growthPathLaw W b -
        ∫ ω, testAt b E κ W uu Φ ω *
          transmissionRatio z.1 z.2 (transmissionProcess b E κ W s ω) ∂growthPathLaw W b -
        ∫ ω, testAt b E κ W uu Φ ω *
          ∑ r ∈ Finset.Ico ⌊(W : ℝ) * s⌋₊ ⌊(W : ℝ) * t⌋₊, ratioDriftAt b E κ W r z ω / (W : ℝ)
          ∂growthPathLaw W b := by
  have hψm : Measurable (testAt b E κ W uu Φ) :=
    Φ.continuous.measurable.comp (measurable_pi_iff.mpr fun l => measurable_stateAt' b E κ _)
  have hψb : ∀ᵐ ω ∂growthPathLaw W b, ‖testAt b E κ W uu Φ ω‖ ≤ ‖Φ‖ :=
    Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact abs_testAt_le b E κ uu Φ ω
  have i1 := (integrable_ratioAt hκ hb1 hE1 hE2 hz (W := W) ⌊(W : ℝ) * t⌋₊).bdd_mul
    hψm.aestronglyMeasurable hψb
  have i2 := (integrable_ratioAt hκ hb1 hE1 hE2 hz (W := W) ⌊(W : ℝ) * s⌋₊).bdd_mul
    hψm.aestronglyMeasurable hψb
  have i3 := (integrable_finsetSum (Finset.Ico ⌊(W : ℝ) * s⌋₊ ⌊(W : ℝ) * t⌋₊) fun r _ =>
    integrable_ratioDriftAt hκ hb1 hE1 hE2 hz (W := W) r).bdd_mul
      hψm.aestronglyMeasurable hψb
  exact integral_mul_sub3 i1 i2 i3

theorem continuousAt_drift_pair (D0 E : ℝ) {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) {p : ℕ}
    {z : DualCoord p} (hz : z ∈ dualChamber p) (u : ℝ) (ν : FiniteMeasure unitInterval) :
    ContinuousAt (fun q : ℝ × FiniteMeasure unitInterval => ratioDrift D0 E κ q.1 z q.2)
      (u, ν) := by
  have hm : Continuous fun q : ℝ × FiniteMeasure unitInterval =>
      ((q.1, (z, q.2)) : ℝ × (DualCoord p × FiniteMeasure unitInterval)) :=
    continuous_fst.prodMk (continuous_const.prodMk continuous_snd)
  have hc := continuousAt_ratioDrift D0 E hκ.1 u hz ν
  have h2 : ContinuousAt ((fun q : ℝ × (DualCoord p × FiniteMeasure unitInterval) =>
      ratioDrift D0 E κ q.1 q.2.1 q.2.2) ∘ fun q : ℝ × FiniteMeasure unitInterval =>
        ((q.1, (z, q.2)) : ℝ × (DualCoord p × FiniteMeasure unitInterval))) (u, ν) :=
    ContinuousAt.comp_of_eq hc hm.continuousAt rfl
  exact h2

/-- **Every subsequential limit is a ratio martingale** (from `RatioDriftSummable`). -/
theorem isRatioMartingale_of (hRD : RatioDriftSummable) {b E : ℝ} {κ : ℝ → ℝ} {φ : ℕ → ℕ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hκ : IsAbsorptionProfile κ)
    (hφ : Tendsto φ atTop atTop) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : ℝ → Ω → FiniteMeasure unitInterval} (h : IsTransmissionSubLimit b E κ φ P μ) :
    IsRatioMartingale (transportD0 b E) E κ P μ := by
  have := h.prob
  have hb1 : b < 1 := by linarith
  intro p z hz s t hs ht hst
  have hs0 : 0 < s := hs
  set D0 := transportD0 b E
  obtain ⟨C, -, hC⟩ := exists_bound_drift D0 E hκ hz
  have hG := continuousAt_drift_pair D0 E hκ hz
  have hFub := fun {ψ : Ω → ℝ} (hψ : Measurable ψ) {B : ℝ} (hB : ∀ ω, |ψ ω| ≤ B) =>
    limit_fubini_bdd (G := fun u ν => ratioDrift D0 E κ u z ν) h.measurable h.continuous hG
      hC hs0 hst hψ hB
  have hFm : ∀ v, 0 < v → Measurable fun ω => transmissionRatio z.1 z.2 (μ v ω) := fun v hv =>
    (continuous_ratio_nu hz).measurable.comp (h.measurable v hv)
  have hFb : ∀ v ω, |transmissionRatio z.1 z.2 (μ v ω)| ≤ 1 := fun v ω => by
    have h' := transmissionRatio_mem_vec (IsRatioParameter.isRatioRange hz) (μ v ω)
    rw [abs_of_pos h'.1]; exact h'.2
  have hFi : ∀ v, 0 < v → Integrable (fun ω => transmissionRatio z.1 z.2 (μ v ω)) P :=
    fun v hv => Integrable.of_bound (C := 1) (hFm v hv).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hFb v ω)
  have hI := (hFub (ψ := fun _ => (1 : ℝ)) measurable_const (B := 1) fun _ => by simp).1
  refine ⟨((hFi t ht).sub (hFi s hs)).sub hI, ?_⟩
  intro m i uu huu Φ
  simp only [smul_eq_mul]
  set Ψ : Ω → ℝ := fun ω => Φ fun l => μ (uu l) ω
  have hΨm : Measurable Ψ :=
    Φ.continuous.measurable.comp (measurable_pi_iff.mpr fun l => h.measurable _ (huu l).1)
  have hΨb : ∀ ω, |Ψ ω| ≤ ‖Φ‖ := fun ω => by
    rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _
  have hΨb' : ∀ᵐ ω ∂P, ‖Ψ ω‖ ≤ ‖Φ‖ := Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hΨb ω
  obtain ⟨-, hswap, -⟩ := hFub hΨm hΨb
  have hu : ∀ l, 0 < uu l := fun l => (huu l).1
  -- the limit of the finite-`W` identity
  set L := ∫ v in s..t, ∫ ω, Φ (fun l => μ (uu l) ω) * ratioDrift D0 E κ v z (μ v ω) ∂P
  have hY := (tendsto_test_mul hκ.2.1 hb1 hE1 hE2 h hu Φ ht (ratioBCF' hz)).sub
    (tendsto_test_mul hκ.2.1 hb1 hE1 hE2 h hu Φ hs (ratioBCF' hz))
  simp only [ratioBCF'_apply] at hY
  have hZ := tendsto_drift_sum hκ hb1 hE1 hE2 hz Φ hφ h hu hs0 hst
  have hX := hY.sub hZ
  have hX0 : Tendsto (fun n => ∫ ω, testAt b E κ (φ n) uu Φ ω *
      (ratioAt b E κ (φ n) ⌊((φ n : ℕ) : ℝ) * t⌋₊ z ω -
        ratioAt b E κ (φ n) ⌊((φ n : ℕ) : ℝ) * s⌋₊ z ω -
        ∑ r ∈ Finset.Ico ⌊((φ n : ℕ) : ℝ) * s⌋₊ ⌊((φ n : ℕ) : ℝ) * t⌋₊,
          ratioDriftAt b E κ (φ n) r z ω / (φ n : ℝ)) ∂growthPathLaw (φ n) b) atTop (𝓝 0) := by
    have hsum := ((hRD b hb0 hb E hE1 hE2 κ hκ p z hz s t hs0 hst).comp hφ).const_mul ‖Φ‖
    rw [mul_zero] at hsum
    refine squeeze_zero_norm (fun n => ?_) hsum
    rw [Real.norm_eq_abs]
    exact abs_integral_ratio_drift_le hκ hb1 hE1 hE2 hz
      (measurable_testAt b E κ (fun l => ⟨(huu l).1.le, (huu l).2⟩) Φ)
      (abs_testAt_le b E κ uu Φ) _
      (Nat.floor_mono (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg _)))
  have hXe := fun n => finite_split hκ hb1 hE1 hE2 hz (W := φ n) uu Φ s t
  simp only [hXe] at hX0
  have huniq := tendsto_nhds_unique hX hX0
  -- conclude
  have i1 := (hFi t ht).bdd_mul hΨm.aestronglyMeasurable hΨb'
  have i2 := (hFi s hs).bdd_mul hΨm.aestronglyMeasurable hΨb'
  have i3 := hI.bdd_mul hΨm.aestronglyMeasurable hΨb'
  change ∫ ω, Ψ ω * (transmissionRatio z.1 z.2 (μ t ω) - transmissionRatio z.1 z.2 (μ s ω) -
    ∫ u in s..t, ratioDrift D0 E κ u z (μ u ω)) ∂P = 0
  rw [integral_mul_sub3 i1 i2 i3, hswap]
  linarith

/-- **Prop 3 from the finite-`W` forced ratio expansion.** -/
theorem subLimitRatioMartingale_of (hRD : RatioDriftSummable) : SubLimitRatioMartingale :=
  fun _ hb0 hb _ hE1 hE2 _ hκ _ hφ _ _ _ _ h => isRatioMartingale_of hRD hb0 hb hE1 hE2 hκ hφ h

end BlockBand.Transmission.LawForced
