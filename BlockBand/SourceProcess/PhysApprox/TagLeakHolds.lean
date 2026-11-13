module

public import BlockBand.SourceProcess.PhysApprox.TagLeakBound
public import BlockBand.SourceProcess.PhysApprox.Assembly
public import BlockBand.SourceProcess.SmallLeak.HoldsOfContracts

/-!
# The input leakage `TagChannelLeakage` from the contract hypotheses

This file proves `TargetTL`. Measure `growthPathLaw W b`; domain `0 < b < 1/2`, `-2 < E < 2`,
`0 < s < τ < T`; the tag is born at `k = ⌊Wτ⌋`, read at `n_T = ⌊WT⌋`, the omitted far inputs are
chosen at `n_s = ⌊Ws⌋` with cutoff `h`. Uniformity: `∀ᶠ h ∈ 𝓝[>] 0, ∀ᶠ W`.

The flux estimates are source-free and are used as they are (`omittedFluxStart_holds`,
`omittedFluxGrowth_holds`). The leak recursion is the one-step leakage recursion applied at each
width to the spike `tagTest W k` (`tag_leak_bound_at`), which is the tag `W⁻¹Y_{n;k}`. Its inputs
are as in `leakRecursion_holds`, except that the trace exit uses the tag sup moments
`TagSupBulk` at `p = 2` (instead of the interval-source sup moments), the start term is `0` (the
tag is born after `n_s`) and the birth weight is `≤ 1/W` (one birth of weight `1/W` instead of
`≤ W` births of weight `Q/W²`). The sum over `≤ TW` steps of the per-step bound `P` still closes
with `E δ₀ ≤ C/W` (`‖δ₀‖₄ ≤ C_δ/W`, `DeltaZeroLengthUniform`):
`(n_T − n_s)P ≤ C₁K(√x + x)`, `C₁ = T(a₁(C_δ + 1) + a₂(C_δ² + 1) + B/(4η²))`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.FullSourceStops BlockBand.SourceProcess.FullSource
open BlockBand.Transmission.PathScalar BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.TagBirth BlockBand.SourceProcess.RawTag
open BlockBand.Transmission.LengthUniform BlockBand.SourceProcess.SmallLeak
open scoped ENNReal Matrix.Norms.L2Operator ComplexOrder

/-- The arithmetic of the summed step bound: `W P ≤ K C (√x + x)` for `K ≥ 1`. -/
theorem tag_step_arith {K a1 a2 a3 Cδ x w : ℝ} (hK : 1 ≤ K) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (ha3 : 0 ≤ a3) (hCδ : 0 ≤ Cδ) (hx0 : 0 ≤ x) (hw : 1 ≤ w) :
    w * (K * a1 * (Cδ / w * Real.sqrt x + Real.sqrt x * w⁻¹) +
      K * a2 * ((Cδ / w) ^ 2 * Real.sqrt (w * x) + x * w⁻¹) + w⁻¹ * a3 * x) ≤
      K * (a1 * (Cδ + 1) + a2 * (Cδ ^ 2 + 1) + a3) * (Real.sqrt x + x) := by
  have hw0 : 0 < w := by linarith
  have hsx := Real.sqrt_nonneg x
  have hWx : Real.sqrt (w * x) ≤ w * Real.sqrt x := by
    rw [Real.sqrt_mul hw0.le]
    refine mul_le_mul_of_nonneg_right ?_ hsx
    calc Real.sqrt w ≤ Real.sqrt (w ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = w := Real.sqrt_sq hw0.le
  have t1 : Real.sqrt (w * x) / w ≤ Real.sqrt x := by
    rw [div_le_iff₀ hw0]; linarith only [hWx, mul_comm w (Real.sqrt x)]
  have e : w * (K * a1 * (Cδ / w * Real.sqrt x + Real.sqrt x * w⁻¹) +
      K * a2 * ((Cδ / w) ^ 2 * Real.sqrt (w * x) + x * w⁻¹) + w⁻¹ * a3 * x) =
      K * a1 * (Cδ + 1) * Real.sqrt x + K * a2 * (Cδ ^ 2 * (Real.sqrt (w * x) / w) + x) +
        a3 * x := by
    field_simp
  rw [e]
  have hK0 : 0 ≤ K := by linarith
  have hKa2 : 0 ≤ K * a2 := mul_nonneg hK0 ha2
  have T1 : 0 ≤ K * a1 * (Cδ + 1) * x :=
    mul_nonneg (mul_nonneg (mul_nonneg hK0 ha1) (add_nonneg hCδ zero_le_one)) hx0
  have T2 : 0 ≤ K * a2 * Cδ ^ 2 * (Real.sqrt x - Real.sqrt (w * x) / w) :=
    mul_nonneg (mul_nonneg hKa2 (sq_nonneg _)) (sub_nonneg.mpr t1)
  have T3 : 0 ≤ K * a2 * Cδ ^ 2 * x := mul_nonneg (mul_nonneg hKa2 (sq_nonneg _)) hx0
  have T4 : 0 ≤ K * a2 * Real.sqrt x := mul_nonneg hKa2 hsx
  have T5 : 0 ≤ K * a3 * Real.sqrt x := mul_nonneg (mul_nonneg hK0 ha3) hsx
  have T6 : 0 ≤ K * a3 * x - a3 * x := by
    have := mul_le_mul_of_nonneg_right hK (mul_nonneg ha3 hx0)
    linarith only [this]
  have key : K * (a1 * (Cδ + 1) + a2 * (Cδ ^ 2 + 1) + a3) * (Real.sqrt x + x) -
      (K * a1 * (Cδ + 1) * Real.sqrt x + K * a2 * (Cδ ^ 2 * (Real.sqrt (w * x) / w) + x) +
        a3 * x) = K * a1 * (Cδ + 1) * x + K * a2 * Cδ ^ 2 * (Real.sqrt x -
          Real.sqrt (w * x) / w) + K * a2 * Real.sqrt x + K * a2 * Cδ ^ 2 * x +
        K * a3 * Real.sqrt x + (K * a3 * x - a3 * x) := by ring
  linarith only [key, T1, T2, T3, T4, T5, T6]

/-- **`TagChannelLeakage`** (the small-channel leakage for one normalized tag) from the five
contract hypotheses. -/
theorem tagChannelLeakage_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hSR : ScalarRecursionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    TagChannelLeakage := by
  intro b hb0 hb E hE1 hE2 s τ T hs hsτ hτT ε hε
  have hsT : s < T := hsτ.trans hτT
  obtain ⟨hκ, hEκ⟩ := mem_bulkInterval_self hE1 hE2
  set κ := min (E + 2) (2 - E)
  obtain ⟨CS, hCS⟩ := omittedFluxStart_holds hMT hGA hLp hP b hb0 hb E hE1 hE2 s hs
  obtain ⟨CG, hCG⟩ := omittedFluxGrowth_holds hGA hLp hSR b hb0 hb E hE1 hE2 s T hs hsT
  obtain ⟨Ca, C₂, Cn, CN₂, CN, Cf₀, Cm₀, ρ, d₀, WL, -, -, -, -, -, -, -, -, -, hL⟩ :=
    tagLayerBounds_of (fullSourceEstimates_holds hGA hLp)
      (passiveMeanStep_holds (passiveBounds_holds hGA hLp)) (passiveFluctuationStep_holds hGA hLp)
      hb0 hb hκ (n := 2) le_rfl
  obtain ⟨Cm, Cf, W₂, hCm, hCf, hΔb⟩ := delta_fresh_bounds hGA hLp b hb0 hb κ hκ 2 (by norm_num)
  obtain ⟨CD, W₃, hCD, hΔ2⟩ := delta_moments hGA b hb0 hb κ hκ 2 (by norm_num)
  obtain ⟨Cδ, hCδ, hδT⟩ := deltaZeroLengthUniform_holds hMT hGA hLp b hb0 hb κ 4 hκ (by norm_num)
  obtain ⟨W₅, hW₅⟩ := hδT T
  obtain ⟨Csup, W₆, hsup⟩ := tagSupBulk_holds hGA hLp hSR b hb0 hb κ T 2 hκ two_pos
  have hη : 0 < etaZ b E := boundaryZ_im_pos (by linarith) hE1 hE2
  set η := etaZ b E
  set B := (1 + CD / η) ^ 2
  have hB0 : 0 ≤ B := sq_nonneg _
  set a1 := Cm / η
  set a2 := (Cm ^ 2 + Cf ^ 2) / η ^ 2
  set a3 := B / (4 * η ^ 2)
  set C₁ := T * (a1 * (Cδ + 1) + a2 * (Cδ ^ 2 + 1) + a3)
  set Csup' := max Csup 0
  set K := max 1 (2 * Csup' / ε)
  have hT0 : 0 < T := hs.trans hsT
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := by linarith
  have hCK : Csup' / K ≤ ε / 2 := by
    rw [div_le_iff₀ hK0]
    have : 2 * Csup' / ε ≤ K := le_max_right _ _
    rw [div_le_iff₀ hε] at this
    linarith
  filter_upwards [eventually_small_bound CG CS (max C₁ 0 * K) (half_pos hε)]
    with h ⟨h0, h1, hsmall⟩
  filter_upwards [hCS h h0 h1, hCG h h0 h1 h h0, eventually_ge_atTop (max (max (max WL W₂)
    (max W₃ W₅)) (max W₆ (max (⌈1 / (T - τ)⌉₊ + 1) (⌈2 / s⌉₊ + 1))))] with W hSW hGW hW
  have hWL : WL ≤ W := le_trans (by simp) hW
  have hW2 : W₂ ≤ W := le_trans (by simp) hW
  have hW3 : W₃ ≤ W := le_trans (by simp) hW
  have hW5 : W₅ ≤ W := le_trans (by simp) hW
  have hW6 : W₆ ≤ W := le_trans (by simp) hW
  have hW8 : ⌈1 / (T - τ)⌉₊ + 1 ≤ W := le_trans (by simp) hW
  have hW9 : ⌈2 / s⌉₊ + 1 ≤ W := le_trans (by simp) hW
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hWs : 2 ≤ (W : ℝ) * s := by
    have : 2 / s ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈2 / s⌉₊ ≤ W))
    rw [div_le_iff₀ hs] at this; linarith
  have hWτ : (W : ℝ) * τ + 1 ≤ W * T := by
    have hTτ : 0 < T - τ := by linarith
    have : 1 / (T - τ) ≤ W :=
      (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈1 / (T - τ)⌉₊ ≤ W))
    rw [div_le_iff₀ hTτ, mul_sub] at this; linarith
  set ns := ⌊(W : ℝ) * s⌋₊
  set nT := ⌊(W : ℝ) * T⌋₊
  set k := ⌊(W : ℝ) * τ⌋₊
  have hns : (W : ℝ) * s - 1 < ns := Nat.sub_one_lt_floor _
  have hn1 : 1 ≤ ns := Nat.le_floor (by push_cast; linarith)
  have hnT : ns ≤ nT := Nat.floor_le_floor (mul_le_mul_of_nonneg_left hsT.le hW0.le)
  have hnk : ns ≤ k := Nat.floor_le_floor (mul_le_mul_of_nonneg_left hsτ.le hW0.le)
  have hkT : k < nT := by
    have hk : (k : ℝ) ≤ W * τ := Nat.floor_le (mul_nonneg hW0.le (hs.trans hsτ).le)
    have : k + 1 ≤ nT := Nat.le_floor (by push_cast; linarith)
    omega
  have hnTW : (nT : ℝ) ≤ T * W := by
    have := Nat.floor_le (mul_nonneg hW0.le hT0.le); linarith [mul_comm (W : ℝ) T]
  -- the flux bound `x(h)` along `[n_s, n_T]` (`smallChannelLeakage_of`)
  set x := fluxBound CG CS h
  have hx0 : 0 ≤ x := by unfold x fluxBound; positivity
  have hI0 : 0 ≤ ∫ ω, omittedFlux b E h s W ns ω ∂growthPathLaw W b :=
    integral_nonneg fun ω => omittedFlux_nonneg b E h s W _ ω
  have hflux : ∀ j : ℕ, ns ≤ j → j ≤ nT →
      ∫ ω, omittedFlux b E h s W j ω ∂growthPathLaw W b ≤ x := by
    intro j hj1 hj2
    refine (hGW j hj1 hj2).trans ?_
    have h1 : CG * ∫ ω, omittedFlux b E h s W ns ω ∂growthPathLaw W b ≤
        max CG 0 * (max CS 0 * h) := by
      refine (mul_le_mul_of_nonneg_right (le_max_left CG 0) hI0).trans
        (mul_le_mul_of_nonneg_left (hSW.trans ?_) (le_max_right _ _))
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) h0.le
    simp only [x, fluxBound]; linarith
  -- the inputs at `W` (`leakRecursion_holds`)
  have hΔb' := fun X hX => hΔb W hW2 E hEκ X hX
  have hN : ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      Integrable (fun f => ‖freshTransport b E XX f‖ ^ 2) (freshLaw W b) := fun XX hXX => by
    have hm : Measurable fun f => ‖freshTransport b E XX f‖ :=
      (measurable_freshTransport_comp b E (XX := fun _ => XX) measurable_const measurable_id).norm
    have hb2 := (hL W hWL E hEκ).N₂ XX hXX
    have hmom : MomBd (freshLaw W b) (fun f => ‖freshTransport b E XX f‖) 2 (max CN₂ 0) :=
      ⟨hm.aestronglyMeasurable, by
        rw [show ENNReal.ofReal 2 = 2 by norm_num]
        exact hb2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
    exact (ProjSeparator.sq_moment_of_momBd (le_max_right _ _) hmom).1
  have hBb : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      Integrable (fun f => (1 + ‖freshDelta b E X f‖ / η) ^ 2) (freshLaw W b) ∧
        ∫ f, (1 + ‖freshDelta b E X f‖ / η) ^ 2 ∂freshLaw W b ≤ B := fun X hX =>
    delta_sq hCD hη (fun f => norm_nonneg _) (by exact_mod_cast hΔ2 W hW3 E hEκ X hX)
  have hδ : ∀ j, ns ≤ j → j < nT →
      MomBd (growthPathLaw W b) (pathDelta b E W j) ((4 : ℕ) : ℝ) (Cδ / W) := by
    intro j hj1 hj2
    have hm : Measurable (pathDelta b E W j) := by
      have e : pathDelta b E W j = fun ω => jetDistance0 b E (nearSchur (boundaryZ b E)
          (pastXX E W j (pastCoords W j ω))) := funext (pathDelta_eq_past b E j)
      rw [e]
      exact (measurable_jetDistance0 b E).comp (measurable_nearSchur_comp (boundaryZ b E)
        ((measurable_pastXX E j).comp (measurable_pastCoords W j)))
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    have hjT : (j : ℝ) ≤ T * W := by
      have : (j : ℝ) ≤ nT := by exact_mod_cast hj2.le
      linarith
    have := hW₅ W hW5 E hEκ j (by omega) hjT
    have h4 : ENNReal.ofReal ((4 : ℕ) : ℝ) = ENNReal.ofReal 4 := by norm_num
    rw [h4]; exact this
  -- the trace exit: the tag sup moments at `p = 2`
  set M : GrowthPath W → ℝ≥0∞ := fun ω => ⨆ (j : ℕ) (_ : (j : ℝ) ≤ T * W),
    ENNReal.ofReal ((W : ℝ)⁻¹ * (tagResponse b E W j k ω).trace.re)
  have hM : ∀ ω i, ns ≤ i → i ≤ nT →
      ENNReal.ofReal (intervalSource b E W i (tagTest W k) ω).trace.re ≤ M ω := by
    intro ω i _ h2
    rw [re_trace_intervalSource_tagTest b E hW1 k i ω]
    split_ifs
    · have hi2 : (i : ℝ) ≤ T * W := by
        have : (i : ℝ) ≤ nT := by exact_mod_cast h2
        linarith
      exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : (j : ℝ) ≤ T * W) =>
        ENNReal.ofReal ((W : ℝ)⁻¹ * (tagResponse b E W j k ω).trace.re)) i hi2 le_rfl
    · rw [ENNReal.ofReal_zero]; exact zero_le
  have hMs : ∫⁻ ω, M ω ^ 2 ∂growthPathLaw W b ≤ ENNReal.ofReal Csup' := by
    have := hsup W hW6 E hEκ k
    simp only [ENNReal.rpow_two] at this
    exact this.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  -- the start: the tag is born after `n_s`
  have hstart : ∀ ω, omittedLeak b E h s (tagTest W k) W ns ω = 0 := by
    intro ω
    rw [omittedLeak, intervalSource_tagTest b E hW1 k ns ω, ite_eq_right (show ¬ k < ns by omega),
      Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]
  have main := tag_leak_bound_at (h := h) (fun y => tagTest_nonneg W k y) hb0 hb hE1 hE2 hW1
    hn1 hnT (K := K) (Cm := Cm) (Cf := Cf) (B := B) (c := (W : ℝ)⁻¹) (D := Cδ / W) (x := x)
    (Csup := Csup') hK0 hCm hCf (by positivity) (birthWeight_tagTest_le hW1 k)
    (by positivity) (le_max_right _ _) hΔb' hN hBb hδ hflux M hM hMs hstart
  -- the arithmetic
  set n := nT - ns
  have hn : (n : ℝ) ≤ T * W := by
    have : (n : ℝ) ≤ nT := by exact_mod_cast Nat.sub_le nT ns
    linarith
  have ha1 : 0 ≤ a1 := by positivity
  have ha2 : 0 ≤ a2 := by positivity
  have ha3 : 0 ≤ a3 := by positivity
  set P := K * (Cm / η) * (Cδ / W * Real.sqrt x + Real.sqrt x * (W : ℝ)⁻¹) +
    K * ((Cm ^ 2 + Cf ^ 2) / η ^ 2) * ((Cδ / W) ^ 2 * Real.sqrt (W * x) + x * (W : ℝ)⁻¹) +
    (W : ℝ)⁻¹ * B * x / (4 * η ^ 2) with hPdef
  have hP' : P = K * a1 * (Cδ / W * Real.sqrt x + Real.sqrt x * (W : ℝ)⁻¹) +
      K * a2 * ((Cδ / W) ^ 2 * Real.sqrt (W * x) + x * (W : ℝ)⁻¹) + (W : ℝ)⁻¹ * a3 * x := by
    rw [hPdef]; simp only [a1, a2, a3]; ring
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hWP := tag_step_arith (K := K) (a1 := a1) (a2 := a2) (a3 := a3) (Cδ := Cδ) (x := x)
    (w := W) hK1 ha1 ha2 ha3 hCδ hx0 (by exact_mod_cast hW1)
  rw [← hP'] at hWP
  have hnP : (n : ℝ) * P ≤ max C₁ 0 * K * (Real.sqrt x + x) := by
    calc (n : ℝ) * P ≤ T * W * P := mul_le_mul_of_nonneg_right hn hP0
      _ = T * (W * P) := by ring
      _ ≤ T * (K * (a1 * (Cδ + 1) + a2 * (Cδ ^ 2 + 1) + a3) * (Real.sqrt x + x)) :=
          mul_le_mul_of_nonneg_left hWP hT0.le
      _ = C₁ * K * (Real.sqrt x + x) := by simp only [C₁]; ring
      _ ≤ max C₁ 0 * K * (Real.sqrt x + x) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hK0.le)
            (by positivity)
  have hfin : (n : ℝ) * P + Csup' / K ≤ ε := by linarith only [hnP, hsmall, hCK]
  calc ∫⁻ ω, ENNReal.ofReal ((farEmbed (omittedProj b E h W ns ω) *
          tagResponse b E W nT k ω).trace.re / W) ∂growthPathLaw W b
        = ∫⁻ ω, ENNReal.ofReal (omittedLeak b E h s (tagTest W k) W nT ω)
          ∂growthPathLaw W b := by
        refine lintegral_congr fun ω => ?_
        rw [omittedLeak_tagTest hW1 hkT ω]
    _ ≤ ENNReal.ofReal ((n : ℝ) * P + Csup' / K) := main
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hfin

/-- **`TargetTL`.** -/
theorem targetTL_holds : TargetTL :=
  fun hMT hGA hSR hLp hP => tagChannelLeakage_holds hMT hGA hSR hLp hP

end BlockBand.SourceProcess.PhysApprox
