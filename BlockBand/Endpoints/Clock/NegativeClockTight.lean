module

public import BlockBand.Endpoints.Clock.SmallBall
public import BlockBand.Internal.Contracts.TransmissionUniform

/-!
# The negative-clock theorem, tightness clause

We prove the `tight` field of `Clocks.NegativeClockContract` from the `clock` field of
`TransmissionUniform.FullSourceMomentsEnergyUniformContract` at `p = 1`.

Proof. Fix `b ∈ (0,1/2)`, `E ∈ (-2,2)`, `τ > 0` and a `ClockSequence τ E`. With
`κI = (2 - |E|)/2`, eventually `E_j ∈ bulkInterval κI`; the contract is applied with base energy
`E_j` itself and `E' = E_j` (window constant `C_e = 0`) and total length `T = τ + 1`
(eventually `n_j ≤ (τ+1)W_j`). Gaussian conditioning (`integral_quadForm_circular`):
`E_h[h*Yh] = Re Tr Y`, so `E T_W ≤ W⁻¹ E|W⁻¹ Tr Y| ≤ C(n+1)/W ≤ C(τ+2)` eventually; Markov
gives the uniform tail bound eventually, and each of the finitely many earlier laws is a
probability measure on `ℝ`, hence has small tails.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal Matrix

namespace NegativeClockTight

/-- A single finite measure on `ℝ` has small tails. -/
theorem exists_tail_le (ν : Measure ℝ) [IsFiniteMeasure ν] {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ν {x | R < |x|} ≤ ENNReal.ofReal ε := by
  have hmeas : ∀ n : ℕ, NullMeasurableSet {x : ℝ | (n : ℝ) < |x|} ν := fun n =>
    (measurableSet_lt measurable_const measurable_abs).nullMeasurableSet
  have hanti : Antitone (fun n : ℕ => {x : ℝ | (n : ℝ) < |x|}) := by
    intro m n hmn x hx
    have hx' : (n : ℝ) < |x| := hx
    exact (lt_of_le_of_lt (by exact_mod_cast hmn) hx' : (m : ℝ) < |x|)
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ n : ℕ, {x : ℝ | (n : ℝ) < |x|}) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_lt]
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    exact ⟨n, hn⟩
  rw [hempty, measure_empty] at hlim
  have hev := (ENNReal.tendsto_nhds_zero.mp hlim) (ENNReal.ofReal ε)
    (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨n, hn⟩

/-- Finitely many finite measures on `ℝ` have uniformly small tails. -/
theorem exists_tail_le_of_lt (ν : ℕ → Measure ℝ) [∀ j, IsFiniteMeasure (ν j)] {ε : ℝ}
    (hε : 0 < ε) (J : ℕ) : ∃ R : ℝ, ∀ j < J, ν j {x | R < |x|} ≤ ENNReal.ofReal ε := by
  induction J with
  | zero => exact ⟨0, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ J ih =>
    obtain ⟨R₁, hR₁⟩ := ih
    obtain ⟨R₂, hR₂⟩ := exists_tail_le (ν J) hε
    refine ⟨max R₁ R₂, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact (measure_mono fun x (hx : max R₁ R₂ < |x|) =>
        (lt_of_le_of_lt (le_max_left _ _) hx : R₁ < |x|)).trans (hR₁ j hj)
    · exact (measure_mono fun x (hx : max R₁ R₂ < |x|) =>
        (lt_of_le_of_lt (le_max_right _ _) hx : R₂ < |x|)).trans hR₂

/-- Gaussian conditioning for the probe: `∫⁻ ofReal T_W = ∫⁻_ω ofReal(W⁻² Re Tr Y)`. -/
theorem lintegral_scaledClock (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ) :
    ∫⁻ x, ENNReal.ofReal (scaledClock b s j x) ∂probedClockLaw (s.W j) b =
      ∫⁻ ω, ENNReal.ofReal
        ((fullClock b (s.energy j) (s.W j) (s.n j) ω).trace.re / (s.W j : ℝ) ^ 2)
        ∂growthPathLaw (s.W j) b := by
  unfold probedClockLaw
  rw [lintegral_prod (fun x => ENNReal.ofReal (scaledClock b s j x))
    (ENNReal.measurable_ofReal.comp (measurable_scaledClock b s j)).aemeasurable]
  refine lintegral_congr fun ω => ?_
  have hnn : ∀ h, 0 ≤ scaledClock b s j (ω, h) := fun h => by
    rw [scaledClock_apply]
    exact div_nonneg (fullClock_quadForm_nonneg _ _ _ _ _ _) (by positivity)
  have hint : Integrable (fun h => scaledClock b s j (ω, h))
      (circularVectorLaw (Fin 2 × Fin (s.W j))) := by
    simp_rw [scaledClock_apply]
    exact (integrable_quadForm_circular _).div_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)]
  congr 1
  simp_rw [scaledClock_apply]
  rw [integral_div, integral_quadForm_circular]

/-- `ofReal(W⁻² Re Tr Y) ≤ ofReal(W⁻¹) ‖W⁻¹ Tr Y‖ₑ` for `W > 0`. -/
theorem ofReal_trace_le {ι : Type*} [Fintype ι] (Y : Matrix ι ι ℂ) {W : ℕ} (hW : 0 < W) :
    ENNReal.ofReal (Y.trace.re / (W : ℝ) ^ 2) ≤
      ENNReal.ofReal (1 / (W : ℝ)) * ‖(W : ℂ)⁻¹ * Y.trace‖ₑ := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h1 : Y.trace.re ≤ ‖Y.trace‖ := Complex.re_le_norm _
  have e : Y.trace.re / (W : ℝ) ^ 2 = 1 / (W : ℝ) * ((W : ℝ)⁻¹ * Y.trace.re) := by
    field_simp
  rw [e]
  gcongr

end NegativeClockTight

open NegativeClockTight in

/-- **, tightness**.
For
`b ∈ (0,1/2)`, `E ∈ (-2,2)`, `τ > 0` and every clock sequence `s` (`n_j/W_j → τ`, `W_j → ∞`,
energies `E_j → E`), the laws of `T_W = W⁻² h*Yh` (`h ~ CN(0, I_{2W})` independent of the
path) are tight in the sense of `IsTightSeq` (a bound for every `j`).
Consumes
`FullSourceMomentsEnergyUniformContract.clock` at `p = 1`.
-/
theorem negativeClock_tight
    (hFSM : BlockBand.Internal.Contracts.TransmissionUniform.FullSourceMomentsEnergyUniformContract)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {E : ℝ} (hE0 : -2 < E) (hE1 : E < 2) {τ : ℝ}
    (hτ : 0 < τ) (s : ClockSequence τ E) :
    IsTightSeq (fun j => clockLaw (s.W j) b (scaledClock b s j)) := by
  intro ε hε
  set κI : ℝ := (2 - |E|) / 2 with hκI
  have hEabs : |E| < 2 := abs_lt.mpr ⟨hE0, hE1⟩
  have hκ : 0 < κI := by rw [hκI]; linarith
  obtain ⟨C, W₀, hC⟩ := hFSM.clock b hb0 hb1 κI 0 (τ + 1) 1 hκ le_rfl
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  -- eventual conditions
  have hEin : ∀ᶠ j in atTop, s.energy j ∈ bulkInterval κI := by
    refine s.energy_tendsto.eventually (Icc_mem_nhds ?_ ?_)
    · have := neg_abs_le E; rw [hκI]; linarith
    · have := le_abs_self E; rw [hκI]; linarith
  have hWge : ∀ᶠ j in atTop, W₀ ≤ s.W j := s.width_tendsto.eventually_ge_atTop W₀
  have hratio : ∀ᶠ j in atTop, (s.n j : ℝ) / s.W j < τ + 1 :=
    s.ratio_tendsto.eventually_lt_const (by linarith)
  set M : ℝ := C' * (τ + 2) with hM
  have hM0 : 0 ≤ M := by positivity
  set R₁ : ℝ := M / ε + 1 with hR₁
  have hR₁0 : 0 < R₁ := by positivity
  have hmain : ∀ᶠ j in atTop,
      clockLaw (s.W j) b (scaledClock b s j) {x | R₁ < |x|} ≤ ENNReal.ofReal ε := by
    filter_upwards [hEin, hWge, hratio] with j hEj hWj hrj
    have hWpos := s.W_pos j
    have hW' : (0 : ℝ) < s.W j := by exact_mod_cast hWpos
    have hW1 : (1 : ℝ) ≤ s.W j := by exact_mod_cast hWpos
    have hnle : (s.n j : ℝ) ≤ (τ + 1) * s.W j := by
      have := (div_lt_iff₀ hW').mp hrj; linarith
    have hnear : IsNearEnergy 0 (s.W j) (s.energy j) (s.energy j) := by
      unfold IsNearEnergy; simp
    have hL1 := hC (s.W j) hWj (s.energy j) hEj (s.energy j) hnear (s.n j) hnle
    rw [ENNReal.ofReal_one] at hL1
    have hmeasf : AEStronglyMeasurable (fun ω => ((s.W j : ℂ))⁻¹ *
        ((boundaryToInterior b (s.energy j) (s.W j) (s.n j) ω)ᴴ *
          boundaryToInterior b (s.energy j) (s.W j) (s.n j) ω).trace)
        (growthPathLaw (s.W j) b) := by
      have h := measurable_fullClock b (s.energy j) (s.W j) (s.n j)
      have ht : Continuous (fun Y : Matrix (Fin 2 × Fin (s.W j)) (Fin 2 × Fin (s.W j)) ℂ =>
          ((s.W j : ℂ))⁻¹ * Y.trace) := continuous_const.mul continuous_id.matrix_trace
      exact (ht.measurable.comp h).aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm hmeasf] at hL1
    -- expectation bound
    have hexp : ∫⁻ x, ENNReal.ofReal (scaledClock b s j x) ∂probedClockLaw (s.W j) b ≤
        ENNReal.ofReal M := by
      rw [lintegral_scaledClock]
      calc ∫⁻ ω, ENNReal.ofReal
            ((fullClock b (s.energy j) (s.W j) (s.n j) ω).trace.re / (s.W j : ℝ) ^ 2)
            ∂growthPathLaw (s.W j) b
          ≤ ∫⁻ ω, ENNReal.ofReal (1 / (s.W j : ℝ)) * ‖((s.W j : ℂ))⁻¹ *
              ((boundaryToInterior b (s.energy j) (s.W j) (s.n j) ω)ᴴ *
                boundaryToInterior b (s.energy j) (s.W j) (s.n j) ω).trace‖ₑ
              ∂growthPathLaw (s.W j) b :=
            lintegral_mono fun ω => ofReal_trace_le _ hWpos
        _ = ENNReal.ofReal (1 / (s.W j : ℝ)) * ∫⁻ ω, ‖((s.W j : ℂ))⁻¹ *
              ((boundaryToInterior b (s.energy j) (s.W j) (s.n j) ω)ᴴ *
                boundaryToInterior b (s.energy j) (s.W j) (s.n j) ω).trace‖ₑ
              ∂growthPathLaw (s.W j) b :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (1 / (s.W j : ℝ)) * ENNReal.ofReal (C * ((s.n j : ℝ) + 1)) := by
            gcongr
        _ ≤ ENNReal.ofReal (1 / (s.W j : ℝ)) * ENNReal.ofReal (C' * ((s.n j : ℝ) + 1)) := by
            gcongr
            exact le_max_left _ _
        _ = ENNReal.ofReal (C' * (((s.n j : ℝ) + 1) / s.W j)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
        _ ≤ ENNReal.ofReal M := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [hM]
            refine mul_le_mul_of_nonneg_left ?_ hC'0
            rw [div_le_iff₀ hW']
            nlinarith
    -- Markov
    have hSm : MeasurableSet {x : ℝ | R₁ < |x|} := measurableSet_lt measurable_const measurable_abs
    unfold clockLaw
    rw [Measure.map_apply (measurable_scaledClock b s j) hSm]
    have hmark := mul_meas_ge_le_lintegral₀ (μ := probedClockLaw (s.W j) b)
      (f := fun x => ENNReal.ofReal (scaledClock b s j x))
      (ENNReal.measurable_ofReal.comp (measurable_scaledClock b s j)).aemeasurable
      (ENNReal.ofReal R₁)
    have hsub : scaledClock b s j ⁻¹' {x | R₁ < |x|} ⊆
        {x | ENNReal.ofReal R₁ ≤ ENNReal.ofReal (scaledClock b s j x)} := by
      intro x hx
      have hx' : R₁ < |scaledClock b s j x| := hx
      have hnn : 0 ≤ scaledClock b s j x := by
        rw [scaledClock_apply]
        exact div_nonneg (fullClock_quadForm_nonneg _ _ _ _ _ _) (by positivity)
      rw [abs_of_nonneg hnn] at hx'
      exact ENNReal.ofReal_le_ofReal hx'.le
    have h1 : ENNReal.ofReal R₁ * probedClockLaw (s.W j) b (scaledClock b s j ⁻¹' {x | R₁ < |x|})
        ≤ ENNReal.ofReal R₁ * ENNReal.ofReal ε := by
      calc _ ≤ ENNReal.ofReal R₁ * probedClockLaw (s.W j) b
              {x | ENNReal.ofReal R₁ ≤ ENNReal.ofReal (scaledClock b s j x)} := by
            gcongr
        _ ≤ _ := hmark
        _ ≤ ENNReal.ofReal M := hexp
        _ ≤ ENNReal.ofReal (R₁ * ε) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [hR₁, add_mul, div_mul_cancel₀ _ hε.ne']
            linarith
        _ = ENNReal.ofReal R₁ * ENNReal.ofReal ε := ENNReal.ofReal_mul hR₁0.le
    exact (ENNReal.mul_le_mul_iff_right (by simpa using hR₁0) ENNReal.ofReal_ne_top).mp h1
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hmain
  obtain ⟨R₂, hR₂⟩ := exists_tail_le_of_lt (fun j => clockLaw (s.W j) b (scaledClock b s j)) hε J
  refine ⟨max R₁ R₂, fun j => ?_⟩
  rcases lt_or_ge j J with hj | hj
  · exact (measure_mono fun x (hx : max R₁ R₂ < |x|) =>
      (lt_of_le_of_lt (le_max_right _ _) hx : R₂ < |x|)).trans (hR₂ j hj)
  · exact (measure_mono fun x (hx : max R₁ R₂ < |x|) =>
      (lt_of_le_of_lt (le_max_left _ _) hx : R₁ < |x|)).trans (hJ j hj)

end BlockBand.Endpoints.Clock
