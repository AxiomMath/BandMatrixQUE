module

public import BlockBand.SourceProcess.SmallLeak.LeakBound
public import BlockBand.SourceProcess.SmallLeak.GrowthHolds
public import BlockBand.SourceProcess.FullSourceStops.TagSup
public import BlockBand.SourceProcess.ProjSeparator.FarHolds
public import BlockBand.Transmission.LengthUniform.DeltaZero

/-!
# The summed leakage recursion

This file proves `LeakRecursion` from the matched-traces, Gaussian layer and scalar recursion
hypotheses.

`leak_bound_at` with: `‖δ_j‖₄ ≤ C_δ/W` (`DeltaZeroLengthUniform`), the source sup moments
(`supMoments_of`, `p = 2`), the tag moments (`TagSupBulk`, `p = 1`) and the one-layer bounds.
The step sum is `≤ TW·P ≤ C₁K(√x + x)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.FullSourceStops BlockBand.SourceProcess.FullSource
open BlockBand.Transmission.PathScalar BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.TagBirth BlockBand.SourceProcess.RawTag
open BlockBand.Transmission.LengthUniform
open scoped ENNReal Matrix.Norms.L2Operator ComplexOrder

variable {W : ℕ}

/-- `E(1 + ‖Δ‖/η)² ≤ (1 + C/η)²` from `‖Δ‖ ∈ L²`. -/
theorem delta_sq {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {Δ : Ω → ℝ} {C η : ℝ} (hC : 0 ≤ C) (hη : 0 < η) (hΔ0 : ∀ ω, 0 ≤ Δ ω)
    (h : MomBd ν Δ ((2 : ℕ) : ℝ) C) :
    Integrable (fun ω => (1 + Δ ω / η) ^ 2) ν ∧ ∫ ω, (1 + Δ ω / η) ^ 2 ∂ν ≤ (1 + C / η) ^ 2 := by
  have h1 : MomBd ν (fun _ => (1 : ℝ)) ((2 : ℕ) : ℝ) 1 := by
    simpa using MomBd.const (μ := ν) (1 : ℝ) ((2 : ℕ) : ℝ) (by norm_num)
  have h3 := h1.add (by norm_num) (h.const_mul (inv_nonneg.mpr hη.le)) (by norm_num) (by positivity)
  obtain ⟨hi, hb⟩ := integral_abs_pow_le (ν := ν) (n := 2) (by norm_num) (by positivity) h3
  have e : ∀ ω, |1 + η⁻¹ * Δ ω| ^ 2 = (1 + Δ ω / η) ^ 2 := fun ω => by
    rw [abs_of_nonneg (by have := hΔ0 ω; positivity), div_eq_inv_mul]
  simp only [e] at hi hb
  exact ⟨hi, hb.trans (le_of_eq (by rw [div_eq_inv_mul]))⟩

/-- **`LeakRecursion`** from the input hypotheses. -/
theorem leakRecursion_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) : LeakRecursion := by
  intro b hb0 hb E hE1 hE2 s T hs hsT q hq
  obtain ⟨hκ, hEκ⟩ := mem_bulkInterval_self hE1 hE2
  set κ := min (E + 2) (2 - E)
  obtain ⟨Q, hQ0, hQb⟩ := intervalTest_bounded hq
  obtain ⟨Ca, C₂, Cn, CN₂, CN, Cf₀, Cm₀, ρ, d₀, WL, -, -, -, -, -, -, -, -, -, hL⟩ :=
    tagLayerBounds_of (fullSourceEstimates_holds hGA hLp)
      (passiveMeanStep_holds (passiveBounds_holds hGA hLp)) (passiveFluctuationStep_holds hGA hLp)
      hb0 hb hκ (n := 2) le_rfl
  obtain ⟨Cm, Cf, W₂, hCm, hCf, hΔb⟩ := delta_fresh_bounds hGA hLp b hb0 hb κ hκ 2 (by norm_num)
  obtain ⟨CD, W₃, hCD, hΔ2⟩ := delta_moments hGA b hb0 hb κ hκ 2 (by norm_num)
  obtain ⟨Cδ, hCδ, hδT⟩ := deltaZeroLengthUniform_holds hMT hGA hLp b hb0 hb κ 4 hκ (by norm_num)
  obtain ⟨W₅, hW₅⟩ := hδT T
  obtain ⟨Csup, W₆, hsup⟩ := supMoments_of (tagSupBulk_holds hGA hLp hSR) b hb0 hb κ hκ 0 1
    (fun _ => q) (fun _ => ⟨s, T, hq⟩) (s / 2) T 2 (by positivity) (by linarith) (by norm_num)
  obtain ⟨Ctag, W₇, htag⟩ := tagSupBulk_holds hGA hLp hSR b hb0 hb κ T 1 hκ one_pos
  have hη : 0 < etaZ b E := boundaryZ_im_pos (by linarith) hE1 hE2
  set η := etaZ b E
  set B := (1 + CD / η) ^ 2
  set a1 := Cm / η
  set a2 := (Cm ^ 2 + Cf ^ 2) / η ^ 2
  set a3 := Q * B / (4 * η ^ 2)
  set C₁ := T * (a1 * (Cδ + 1) + a2 * (Cδ ^ 2 + 1) + a3)
  set Csup' := max Csup 0
  set Ctag' := max Ctag 0
  have hT0 : 0 < T := hs.trans hsT
  refine ⟨max C₁ Csup', fun K hK h h0 h1 η' hη' => ?_⟩
  filter_upwards [eventually_ge_atTop (max (max (max WL W₂) (max W₃ W₅)) (max (max W₆ W₇)
    (max (⌈Q * Ctag' / η'⌉₊ + 1) (⌈2 / s⌉₊ + 1))))] with W hW x hx0 hx
  have hWL : WL ≤ W := le_trans (by simp) hW
  have hW2 : W₂ ≤ W := le_trans (by simp) hW
  have hW3 : W₃ ≤ W := le_trans (by simp) hW
  have hW5 : W₅ ≤ W := le_trans (by simp) hW
  have hW6 : W₆ ≤ W := le_trans (by simp) hW
  have hW7 : W₇ ≤ W := le_trans (by simp) hW
  have hW8 : ⌈Q * Ctag' / η'⌉₊ + 1 ≤ W := le_trans (by simp) hW
  have hW9 : ⌈2 / s⌉₊ + 1 ≤ W := le_trans (by simp) hW
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hWs : 2 ≤ (W : ℝ) * s := by
    have : 2 / s ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈2 / s⌉₊ ≤ W))
    rw [div_le_iff₀ hs] at this; linarith
  set ns := ⌊(W : ℝ) * s⌋₊
  set nT := ⌊(W : ℝ) * T⌋₊
  have hns : (W : ℝ) * s - 1 < ns := Nat.sub_one_lt_floor _
  have hn1 : 1 ≤ ns := Nat.le_floor (by push_cast; linarith)
  have hnT : ns ≤ nT := Nat.floor_le_floor (mul_le_mul_of_nonneg_left hsT.le hW0.le)
  have hnTW : (nT : ℝ) ≤ T * W := by
    have := Nat.floor_le (mul_nonneg hW0.le hT0.le); linarith [mul_comm (W : ℝ) T]
  -- the inputs at `W`
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
  set k0 : Fin 0 → ℕ := fun i => i.elim0
  set q' : Fin 1 → ℝ → ℝ := fun _ => q
  set M : GrowthPath W → ℝ≥0∞ := fun ω => ⨆ (j : ℕ) (_ : s / 2 * W ≤ j ∧ (j : ℝ) ≤ T * W),
    ‖sourceTrace b E k0 q' W j ω (Sum.inr 0)‖ₑ
  have hM : ∀ ω i, ns ≤ i → i ≤ nT →
      ENNReal.ofReal (intervalSource b E W i q ω).trace.re ≤ M ω := by
    intro ω i h1 h2
    have hi1 : s / 2 * W ≤ i := by
      have : (ns : ℝ) ≤ i := by exact_mod_cast h1
      nlinarith
    have hi2 : (i : ℝ) ≤ T * W := by
      have : (i : ℝ) ≤ nT := by exact_mod_cast h2
      linarith
    refine le_trans ?_ (le_iSup₂_of_le (f := fun (j : ℕ) (_ : s / 2 * W ≤ j ∧ (j : ℝ) ≤ T * W) =>
      ‖sourceTrace b E k0 q' W j ω (Sum.inr 0)‖ₑ) i ⟨hi1, hi2⟩ le_rfl)
    show ENNReal.ofReal (intervalSource b E W i q ω).trace.re ≤
      ‖(intervalSource b E W i q ω).trace.re‖ₑ
    rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hMs : ∫⁻ ω, M ω ^ 2 ∂growthPathLaw W b ≤ ENNReal.ofReal Csup' := by
    have := hsup W hW6 E hEκ k0 (Sum.inr 0)
    simp only [ENNReal.rpow_two] at this
    exact this.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have htag' : ∫⁻ ω, ENNReal.ofReal ((W : ℝ)⁻¹ * (tagResponse b E W ns (ns - 1) ω).trace.re)
      ∂growthPathLaw W b ≤ ENNReal.ofReal Ctag' := by
    have := htag W hW7 E hEκ (ns - 1)
    simp only [ENNReal.rpow_one] at this
    refine le_trans (lintegral_mono fun ω => ?_) (this.trans (ENNReal.ofReal_le_ofReal
      (le_max_left _ _)))
    have hns' : (ns : ℝ) ≤ T * W := (by exact_mod_cast hnT : (ns : ℝ) ≤ nT).trans hnTW
    exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : (j : ℝ) ≤ T * W) =>
      ENNReal.ofReal ((W : ℝ)⁻¹ * (tagResponse b E W j (ns - 1) ω).trace.re)) ns hns' le_rfl
  have hK0 : 0 < K := by linarith
  have main := leak_bound_at (h := h) hq hb0 hb hE1 hE2 hW1 hn1 hnT (K := K) (Cm := Cm) (Cf := Cf)
    (B := B) (Q := Q) (D := Cδ / W) (x := x) (Ctag := Ctag') (Csup := Csup') hK0 hCm hCf
    (by positivity) hQ0 (fun y => (hQb y).2) (by positivity) (le_max_right _ _) (le_max_right _ _)
    hΔb' hN hBb hδ hx M hM hMs htag'
  -- the arithmetic
  set n := nT - ns
  have hn : (n : ℝ) ≤ T * W := by
    have : (n : ℝ) ≤ nT := by exact_mod_cast Nat.sub_le nT ns
    linarith
  have hsx := Real.sqrt_nonneg x
  have hWx : Real.sqrt (W * x) ≤ W * Real.sqrt x := by
    rw [Real.sqrt_mul hW0.le]
    refine mul_le_mul_of_nonneg_right ?_ hsx
    have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    calc Real.sqrt W ≤ Real.sqrt (W ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = W := Real.sqrt_sq hW0.le
  generalize hPdef : K * (Cm / η) * (Cδ / W * Real.sqrt x + Real.sqrt x * (W : ℝ)⁻¹) +
    K * ((Cm ^ 2 + Cf ^ 2) / η ^ 2) * ((Cδ / W) ^ 2 * Real.sqrt (W * x) + x * (W : ℝ)⁻¹) +
    Q / (W : ℝ) ^ 2 * B * x / (4 * η ^ 2) = P at main
  have ha1 : 0 ≤ a1 := by positivity
  have ha2 : 0 ≤ a2 := by positivity
  have ha3 : 0 ≤ a3 := by positivity
  have hP0 : 0 ≤ P := by
    rw [← hPdef]
    have hWi : 0 ≤ (W : ℝ)⁻¹ := inv_nonneg.mpr hW0.le
    have hD0 : 0 ≤ Cδ / W := div_nonneg hCδ hW0.le
    have hB0 : 0 ≤ B := sq_nonneg _
    refine add_nonneg (add_nonneg (mul_nonneg (mul_nonneg hK0.le ha1) (add_nonneg
      (mul_nonneg hD0 hsx) (mul_nonneg hsx hWi))) (mul_nonneg (mul_nonneg hK0.le ha2) (add_nonneg
        (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)) (mul_nonneg hx0 hWi)))) ?_
    exact div_nonneg (mul_nonneg (mul_nonneg (div_nonneg hQ0 (sq_nonneg _)) hB0) hx0)
      (by positivity)
  have hWP : (W : ℝ) * P ≤ K * (a1 * (Cδ + 1) + a2 * (Cδ ^ 2 + 1) + a3) * (Real.sqrt x + x) := by
    have e : (W : ℝ) * P = K * a1 * (Cδ + 1) * Real.sqrt x +
        K * a2 * (Cδ ^ 2 * (Real.sqrt (W * x) / W) + x) + a3 * x / W := by
      rw [← hPdef]; simp only [a1, a2, a3]; field_simp
    rw [e]
    have t1 : Real.sqrt (W * x) / W ≤ Real.sqrt x := by
      rw [div_le_iff₀ hW0]; linarith only [hWx, mul_comm (W : ℝ) (Real.sqrt x)]
    have hKa2 : 0 ≤ K * a2 := mul_nonneg hK0.le ha2
    have T2 : 0 ≤ K * a2 * Cδ ^ 2 * (Real.sqrt x - Real.sqrt (W * x) / W) :=
      mul_nonneg (mul_nonneg hKa2 (sq_nonneg _)) (sub_nonneg.mpr t1)
    have T6 : 0 ≤ K * a3 * x - a3 * x / W := by
      have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
      have h1 : a3 * x / W ≤ a3 * x := div_le_self (mul_nonneg ha3 hx0) hW1'
      have h2 : a3 * x ≤ K * a3 * x := by
        have := mul_le_mul_of_nonneg_right hK (mul_nonneg ha3 hx0)
        linarith only [this]
      linarith only [h1, h2]
    have T1 : 0 ≤ K * a1 * (Cδ + 1) * x :=
      mul_nonneg (mul_nonneg (mul_nonneg hK0.le ha1) (add_nonneg hCδ zero_le_one)) hx0
    have T3 : 0 ≤ K * a2 * Cδ ^ 2 * x := mul_nonneg (mul_nonneg hKa2 (sq_nonneg _)) hx0
    have T4 : 0 ≤ K * a2 * Real.sqrt x := mul_nonneg hKa2 hsx
    have T5 : 0 ≤ K * a3 * Real.sqrt x := mul_nonneg (mul_nonneg hK0.le ha3) hsx
    have key : K * (a1 * (Cδ + 1) + a2 * (Cδ ^ 2 + 1) + a3) * (Real.sqrt x + x) -
        (K * a1 * (Cδ + 1) * Real.sqrt x + K * a2 * (Cδ ^ 2 * (Real.sqrt (W * x) / W) + x) +
          a3 * x / W) = K * a1 * (Cδ + 1) * x + K * a2 * Cδ ^ 2 * (Real.sqrt x -
            Real.sqrt (W * x) / W) + K * a2 * Real.sqrt x + K * a2 * Cδ ^ 2 * x +
          K * a3 * Real.sqrt x + (K * a3 * x - a3 * x / W) := by ring
    linarith only [key, T1, T2, T3, T4, T5, T6]
  have hnP : (n : ℝ) * P ≤ C₁ * K * (Real.sqrt x + x) := by
    calc (n : ℝ) * P ≤ T * W * P := mul_le_mul_of_nonneg_right hn hP0
      _ = T * (W * P) := by ring
      _ ≤ T * (K * (a1 * (Cδ + 1) + a2 * (Cδ ^ 2 + 1) + a3) * (Real.sqrt x + x)) :=
          mul_le_mul_of_nonneg_left hWP hT0.le
      _ = C₁ * K * (Real.sqrt x + x) := by simp only [C₁]; ring
  have hstart : Q / W * Ctag' ≤ η' := by
    have : Q * Ctag' / η' < W := by
      have := Nat.lt_of_ceil_lt (show ⌈Q * Ctag' / η'⌉₊ < W by omega)
      exact this
    rw [div_lt_iff₀ hη'] at this
    rw [div_mul_eq_mul_div, div_le_iff₀ hW0]; linarith only [this]
  have hC1 : C₁ * K * (Real.sqrt x + x) ≤ max C₁ Csup' * K * (Real.sqrt x + x) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hK0.le)
      (by positivity)
  have hC2 : Csup' / K ≤ max C₁ Csup' / K :=
    div_le_div_of_nonneg_right (le_max_right _ _) hK0.le
  have hmain : ∫ ω, omittedLeak b E h s q W nT ω ∂growthPathLaw W b ≤
      Q / W * Ctag' + (n : ℝ) * P + Csup' / K := main
  linarith only [hmain, hnP, hstart, hC1, hC2]

end BlockBand.SourceProcess.SmallLeak
