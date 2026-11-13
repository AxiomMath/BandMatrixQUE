module

public import BlockBand.SourceProcess.FullSourceStops.CurrentStep
public import BlockBand.SourceProcess.FullSourceStops.FractionalUniform
public import BlockBand.SourceProcess.FullSourceStops.TagSup

/-!
# The current tail at one width and one energy

* `current_tail_at` (one width, one energy): with `j₀ = k+1`, `N ≤ RW`,
  `P{∃ j ∈ [j₀, N], Tr|J_j| > K} ≤ P(G_Nᶜ) + (2e^{α₁R}(1 + K_w d)/K) E Tr T_{j₀}^{1/2}`
  (the maximal inequality `ville` for the stopped carrier weights at the level `K/W`, the
  Loewner comparison `Tr|J_j| ≤ Re Tr H_j` and `Re Tr H_{j₀} = 2 Tr T_{j₀}^{1/2}`).

Proved from it in the sibling module:
* `current_tail_bound`: the same, uniformly on `bulkInterval κI`, at `j₀ = ⌊Wε⌋`, `N = ⌊TW⌋`,
  with the exit probability below any `η > 0` for large `W` (SUPX);
* `CurrentNuclearTailFixed`, `currentNuclearTailFixed_of`: the fixed-`E` form, from a fixed-`E`
  fractional bound.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer BlockBand.SourceProcess.FullSource
open scoped ENNReal Matrix.Norms.L2Operator ComplexOrder

variable {W : ℕ}

theorem fracTrace_nonneg {n : Type*} [Fintype n] [DecidableEq n] (p : ℝ) (T : Matrix n n ℂ) :
    0 ≤ fracTrace p T :=
  Multiset.sum_nonneg fun _ h => by
    obtain ⟨z, -, rfl⟩ := Multiset.mem_map.mp h
    exact Real.rpow_nonneg (le_max_right _ _) _

/-- **The current tail at one width and one energy.** -/
theorem current_tail_at {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) {Ca C₂ Cn CN₂ CN Cf Cm Kw ρ d₀ d : ℝ}
    (hL : TagLayerBounds b E W 2 Ca C₂ Cn CN₂ CN Cf Cm ρ d₀)
    (hCa : 0 ≤ Ca) (hC₂ : 0 ≤ C₂) (hCN : 0 ≤ CN) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cm)
    (hKw : 0 ≤ Kw) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hKL : Ca ≤ Kw * (1 - ρ) / 2)
    (hd1 : d ≤ 1) (hρLd : ρ * Ca * d ≤ (1 - ρ) / 2) (hdd₀ : d ≤ d₀) (hd0 : 0 ≤ d)
    (k N : ℕ) {R : ℝ} (hNR : (N : ℝ) ≤ R * W) {K : ℝ} (hK : 0 < K) :
    growthPathLaw W b {ω | ∃ j : ℕ, k + 1 ≤ j ∧ j ≤ N ∧ K < nuclearNorm (pathCurrent b E W j ω)} ≤
      growthPathLaw W b (stopEv b E W k d N)ᶜ +
        ENNReal.ofReal (2 * Real.exp (alphaOne Kw Cm Ca Cf CN * R) * (1 + Kw * d) / K) *
          ∫⁻ ω, ENNReal.ofReal (fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W (k + 1) ω))
            ∂growthPathLaw W b := by
  set μ := growthPathLaw W b
  set α := alphaOne Kw Cm Ca Cf CN
  have hα : 0 ≤ α := alphaOne_nonneg hKw hCm hCa hCN
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set Y := curStopped b E W k Kw d
  set lam : ℝ≥0∞ := ENNReal.ofReal (K / W)
  set c : ℝ≥0∞ := ENNReal.ofReal (1 + α / W)
  set N' := N - (k + 1)
  set I := ∫⁻ ω, ENNReal.ofReal (fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W (k + 1) ω)) ∂μ
  set q : ℝ := (1 + Kw * d) * ((W : ℝ)⁻¹ * 2)
  have hq : 0 ≤ q := by positivity
  have hc : 1 ≤ c := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (by positivity))
  have hcN : c ^ N' ≤ ENNReal.ofReal (Real.exp (α * R)) := by
    rw [← ENNReal.ofReal_pow (by positivity)]
    refine ENNReal.ofReal_le_ofReal (one_add_pow_le_exp hα N' hW0 ?_)
    have : (N' : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N (k + 1)
    linarith
  -- the first moment at the base length
  have hY0 : ∫⁻ ω, Y 0 ω ∂μ ≤ ENNReal.ofReal q * I := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_trace_carrier_zero hb hE1 hE2 hW k] with ω hω
    simp only [Y, curStopped, Nat.add_zero]
    by_cases hG : ω ∈ stopEv b E W k d (k + 1)
    · rw [Set.indicator_of_mem hG, curWeight, Nat.add_zero, hω, ← ENNReal.ofReal_mul hq]
      have hδ : pathDelta b E W (k + 1) ω ≤ d := hG (k + 1) le_rfl le_rfl
      have hδ0 : 0 ≤ pathDelta b E W (k + 1) ω := norm_nonneg _
      have hx := fracTrace_nonneg (1 / 2) (pathTransmission b E (fun _ => 0) W (k + 1) ω)
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : 1 + Kw * pathDelta b E W (k + 1) ω ≤ 1 + Kw * d := by nlinarith
      have h2 : 0 ≤ (W : ℝ)⁻¹ * (2 * fracTrace (1 / 2)
          (pathTransmission b E (fun _ => 0) W (k + 1) ω)) := by positivity
      calc (1 + Kw * pathDelta b E W (k + 1) ω) * ((W : ℝ)⁻¹ * (2 * fracTrace (1 / 2)
            (pathTransmission b E (fun _ => 0) W (k + 1) ω)))
          ≤ (1 + Kw * d) * ((W : ℝ)⁻¹ * (2 * fracTrace (1 / 2)
            (pathTransmission b E (fun _ => 0) W (k + 1) ω))) :=
            mul_le_mul_of_nonneg_right h1 h2
        _ = q * fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W (k + 1) ω) := by
            simp only [q]; ring
    · rw [Set.indicator_of_notMem hG]; exact bot_le
  -- the maximal inequality
  have hV := ville μ (measurable_curStopped b E k Kw d) lam c hc
    (curStopped_step hb hE1 hE2 hW hL hCa hC₂ hCN hCf hCm hKw hρ0 hρ1 hKL hd1 hρLd hdd₀ lam) N'
  have hlam0 : lam ≠ 0 := by
    simp only [lam, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hnoHit : μ (noHit Y lam N')ᶜ ≤
      ENNReal.ofReal (2 * Real.exp (α * R) * (1 + Kw * d) / K) * I := by
    have h1 : μ (noHit Y lam N')ᶜ = lam⁻¹ * (lam * μ (noHit Y lam N')ᶜ) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hlam0 ENNReal.ofReal_ne_top, one_mul]
    rw [h1]
    calc lam⁻¹ * (lam * μ (noHit Y lam N')ᶜ)
        ≤ lam⁻¹ * (ENNReal.ofReal (Real.exp (α * R)) * (ENNReal.ofReal q * I)) := by
          exact mul_le_mul' le_rfl (hV.trans (mul_le_mul' hcN hY0))
      _ = ENNReal.ofReal (2 * Real.exp (α * R) * (1 + Kw * d) / K) * I := by
          have hl : lam⁻¹ = ENNReal.ofReal (K / W)⁻¹ := (ENNReal.ofReal_inv_of_pos (by positivity)).symm
          rw [hl, ← mul_assoc, ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          simp only [q]; field_simp
  -- the set inclusion
  set bad : Set (GrowthPath W) := {ω | ¬ ∀ i,
    (carrier b E W k i ω - pathCurrent b E W (k + 1 + i) ω).PosSemidef ∧
      (carrier b E W k i ω + pathCurrent b E W (k + 1 + i) ω).PosSemidef}
  have hbad : μ bad = 0 := by
    have := ae_carrier_sandwich hb0 hb hE1 hE2 hW k
    rwa [ae_iff] at this
  have hsub : {ω | ∃ j : ℕ, k + 1 ≤ j ∧ j ≤ N ∧ K < nuclearNorm (pathCurrent b E W j ω)} ⊆
      (stopEv b E W k d N)ᶜ ∪ ((noHit Y lam N')ᶜ ∪ bad) := by
    rintro ω ⟨j, hkj, hjN, hJ⟩
    by_cases hG : ω ∈ stopEv b E W k d N
    · right
      by_cases hS : ω ∈ bad
      · exact Or.inr hS
      · left
        have hS' : ∀ i, (carrier b E W k i ω - pathCurrent b E W (k + 1 + i) ω).PosSemidef ∧
            (carrier b E W k i ω + pathCurrent b E W (k + 1 + i) ω).PosSemidef := by
          by_contra h; exact hS h
        obtain ⟨i, rfl⟩ : ∃ i, j = k + 1 + i := ⟨j - (k + 1), by omega⟩
        rw [compl_noHit]
        refine ⟨i, by omega, ?_⟩
        have hmem : ω ∈ stopEv b E W k d (k + 1 + i) := fun l h1 h2 => hG l h1 (by omega)
        simp only [Y, curStopped]
        rw [Set.indicator_of_mem hmem, curWeight]
        have hle := nuclearNorm_le_of_loewner (pathCurrent_isHermitian b E _ ω) (hS' i).1 (hS' i).2
        have hδ : 0 ≤ pathDelta b E W (k + 1 + i) ω := norm_nonneg _
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : K / W ≤ (W : ℝ)⁻¹ * (carrier b E W k i ω).trace.re := by
          rw [div_eq_inv_mul]; exact mul_le_mul_of_nonneg_left (hJ.le.trans hle) (by positivity)
        have h2 : 0 ≤ (W : ℝ)⁻¹ * (carrier b E W k i ω).trace.re := (by positivity : 0 ≤ K / W).trans h1
        nlinarith [mul_nonneg (mul_nonneg hKw hδ) h2]
    · exact Or.inl hG
  calc μ {ω | ∃ j : ℕ, k + 1 ≤ j ∧ j ≤ N ∧ K < nuclearNorm (pathCurrent b E W j ω)}
      ≤ μ (stopEv b E W k d N)ᶜ + (μ (noHit Y lam N')ᶜ + μ bad) :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add_right
          (measure_union_le _ _) _))
    _ ≤ μ (stopEv b E W k d N)ᶜ + ENNReal.ofReal (2 * Real.exp (α * R) * (1 + Kw * d) / K) * I := by
        rw [hbad, add_zero]; gcongr

end BlockBand.SourceProcess.FullSourceStops
