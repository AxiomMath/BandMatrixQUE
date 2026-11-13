module

public import BlockBand.Endpoints.Transmission.AlongRatioLimit
public import BlockBand.Transmission.LawForced.LimitMart

/-!
# Every sub-limit along a moving energy is a ratio martingale at the base energy

`isRatioMartingale_along`: for `0 < b < 1/2`, `-2 < E < 2`, an admissible `κ`, a moving
energy `e` (`IsMovingEnergy E Ce e`) and `φ → ∞`, every `(P, μ)` with
`IsTransmissionSubLimitAlong b e κ φ P μ` satisfies
`IsRatioMartingale (transportD0 b E) E κ P μ` (drift at the base energy `E`).

The proof follows `LawForced.isRatioMartingale_of`, with the width-`W` process at `E_n = e W_n`:
* at finite `W`, `abs_integral_ratio_drift_le` and `finite_split` at `E := E_n` (eventually in
  `(-2, 2)`), with the summed error tending to `0` by `tendsto_ratioDriftError_along`;
* the `F` terms by `tendsto_test_mul_along`;
* the drift sums by `tendsto_drift_sum_along` (limit drift at `D₀(E)`, `E`);
* Fubini on the limit (`limit_fubini_bdd`).

The hypotheses are `MatchedTracesContract`, `GaussianAbsorptionContract`, `GaussianLpGradient` and
`GaussianPoincare`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Transmission

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.LawDuality BlockBand.Transmission.LawForced
open scoped NNReal ENNReal BoundedContinuousFunction

/-- **Every sub-limit along a moving energy is a ratio martingale at the base energy.** -/
theorem isRatioMartingale_along (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    {b E Ce : ℝ} {e : ℕ → ℝ} {κ : ℝ → ℝ} {φ : ℕ → ℕ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (he : IsMovingEnergy E Ce e) (hκ : IsAbsorptionProfile κ)
    (hφ : Tendsto φ atTop atTop) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : ℝ → Ω → FiniteMeasure unitInterval} (h : IsTransmissionSubLimitAlong b e κ φ P μ) :
    IsRatioMartingale (transportD0 b E) E κ P μ := by
  have := h.prob
  have hb1 : b < 1 := by linarith
  have hEn := eventually_energy_along hE1 hE2 he hφ
  have hEn' : ∀ᶠ n in atTop, -2 < e (φ n) ∧ e (φ n) < 2 := hEn.mono fun n hn => ⟨hn.1, hn.2.1⟩
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
  have hY := (tendsto_test_mul_along hκ.2.1 hb1 hEn' h hu Φ ht (ratioBCF' hz)).sub
    (tendsto_test_mul_along hκ.2.1 hb1 hEn' h hu Φ hs (ratioBCF' hz))
  simp only [ratioBCF'_apply] at hY
  have hZ := tendsto_drift_sum_along he hκ hb1 hE1 hE2 hz Φ hφ h hu hs0 hst
  have hX := hY.sub hZ
  have hX0 : Tendsto (fun n => ∫ ω, testAt b (e (φ n)) κ (φ n) uu Φ ω *
      (ratioAt b (e (φ n)) κ (φ n) ⌊((φ n : ℕ) : ℝ) * t⌋₊ z ω -
        ratioAt b (e (φ n)) κ (φ n) ⌊((φ n : ℕ) : ℝ) * s⌋₊ z ω -
        ∑ r ∈ Finset.Ico ⌊((φ n : ℕ) : ℝ) * s⌋₊ ⌊((φ n : ℕ) : ℝ) * t⌋₊,
          ratioDriftAt b (e (φ n)) κ (φ n) r z ω / (φ n : ℝ)) ∂growthPathLaw (φ n) b) atTop
      (𝓝 0) := by
    have hsum := ((tendsto_ratioDriftError_along hMT hGA hLp hP hb0 hb hE1 hE2 he hκ hz hs0
      hst).comp hφ).const_mul ‖Φ‖
    rw [mul_zero] at hsum
    refine squeeze_zero_norm' ?_ hsum
    filter_upwards [hEn'] with n hn
    rw [Real.norm_eq_abs]
    exact abs_integral_ratio_drift_le hκ hb1 hn.1 hn.2 hz
      (measurable_testAt b (e (φ n)) κ (fun l => ⟨(huu l).1.le, (huu l).2⟩) Φ)
      (abs_testAt_le b (e (φ n)) κ uu Φ) _
      (Nat.floor_mono (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg _)))
  have hX1 := hX0.congr' (by
    filter_upwards [hEn'] with n hn
    exact finite_split hκ hb1 hn.1 hn.2 hz (W := φ n) uu Φ s t)
  have huniq := tendsto_nhds_unique hX hX1
  -- conclude
  have i1 := (hFi t ht).bdd_mul hΨm.aestronglyMeasurable hΨb'
  have i2 := (hFi s hs).bdd_mul hΨm.aestronglyMeasurable hΨb'
  have i3 := hI.bdd_mul hΨm.aestronglyMeasurable hΨb'
  change ∫ ω, Ψ ω * (transmissionRatio z.1 z.2 (μ t ω) - transmissionRatio z.1 z.2 (μ s ω) -
    ∫ u in s..t, ratioDrift D0 E κ u z (μ u ω)) ∂P = 0
  rw [integral_mul_sub3 i1 i2 i3, hswap]
  linarith

end BlockBand.Endpoints.Transmission
