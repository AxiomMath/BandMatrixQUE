module

public import BlockBand.SourceProcess.FullSourceStops.CurrentTail
public import BlockBand.SourceProcess.FullSourceStops.Main

/-!
# The current tail (energy-uniform and fixed-`E`) from fractional transmission bounds

* `current_tail_bound`: on `bulkInterval κI`, at `j₀ = ⌊Wε⌋`, `N = ⌊TW⌋`, for `W` large,
  `P{sup_{εW ≤ j ≤ TW} Tr|J_j| > K} ≤ η + (A/K) E Tr T_{j₀}^{1/2}` with `A` independent of
  `K, η, W, E` (layer bounds and SUPX uniform on the bulk set);
* `currentNuclearTail_of`: the statement `CurrentNuclearTail` (defined in the sibling interface
  module) from `GaussianAbsorptionContract`,
  `ScalarRecursionContract`, `GaussianLpGradient` and the hypothesis
  `FractionalTransmissionUniform`;
* `FractionalTransmissionFixed`, `CurrentNuclearTailFixed`: the fixed-`E` forms;
  `fractionalTransmissionFixed_of_law`: the `TransmissionLawContract.fractional` field
  (`p = 1/2`, `t = ε`) **implies** `FractionalTransmissionFixed`;
  `currentNuclearTailFixed_of`: `CurrentNuclearTailFixed` from the same inputs and
  `FractionalTransmissionFixed`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.PathScalar BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.FullSource
open scoped ENNReal

/-- **The current tail, uniformly on a bulk set, at one large width.** -/
theorem current_tail_bound (hFS : FullSourceEstimates) (hMS : PassiveMeanStep)
    (hFl : PassiveFluctuationStep) (hSX : SuperexpExit) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κI : ℝ} (hκ : 0 < κI) {ε T : ℝ} (hε : 0 < ε) (hεT : ε < T) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ η : ℝ, 0 < η → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ K : ℝ, 0 < K →
        growthPathLaw W b {ω | ∃ j : ℕ, ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧
            K < nuclearNorm (pathCurrent b E W j ω)} ≤
          ENNReal.ofReal η + ENNReal.ofReal (A / K) *
            ∫⁻ ω, ENNReal.ofReal (fracTrace (1 / 2)
              (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * ε⌋₊ ω)) ∂growthPathLaw W b := by
  obtain ⟨Ca, C₂, Cn, CN₂, CN, Cf, Cm, ρ, d₀, WL, hCa, hC₂, hCn, hCN, hCf, hCm, hρ0, hρ1, hd₀,
    hL⟩ := tagLayerBounds_of hFS hMS hFl hb0 hb hκ (n := 2) le_rfl
  set Kw := 2 * Ca / (1 - ρ)
  have hKw : 0 ≤ Kw := div_nonneg (by linarith) (by linarith)
  have hKL : Ca ≤ Kw * (1 - ρ) / 2 := by
    simp only [Kw]; rw [div_mul_cancel₀ _ (by linarith : (1 - ρ) ≠ 0)]; linarith
  set d := min (min d₀ 1) ((1 - ρ) / (2 * (ρ * Ca + 1)))
  have hden : 0 < 2 * (ρ * Ca + 1) := by nlinarith [mul_nonneg hρ0 hCa]
  have hd0 : 0 < d := lt_min (lt_min hd₀ one_pos) (div_pos (by linarith) hden)
  have hd1 : d ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hdd₀ : d ≤ d₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hρLd : ρ * Ca * d ≤ (1 - ρ) / 2 := by
    have h1 : d ≤ (1 - ρ) / (2 * (ρ * Ca + 1)) := min_le_right _ _
    have h2 : ρ * Ca * d ≤ ρ * Ca * ((1 - ρ) / (2 * (ρ * Ca + 1))) :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hρ0 hCa)
    have h3 : ρ * Ca * ((1 - ρ) / (2 * (ρ * Ca + 1))) ≤ (1 - ρ) / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ hden (by norm_num)]
      nlinarith [mul_nonneg hρ0 hCa]
    linarith
  set α := alphaOne Kw Cm Ca Cf CN
  refine ⟨2 * Real.exp (α * T) * (1 + Kw * d), by positivity, fun η hη => ?_⟩
  obtain ⟨c, Ws, hc, hSup⟩ := hSX b hb0 hb κI T hκ d hd0
  obtain ⟨W₃, hW₃⟩ := superexp_absorbs (A := 1) (B := 1 / η) (c := c) (T := T) (R := 0)
    le_rfl (by positivity) hc
  refine ⟨max (max WL Ws) (max W₃ (max ⌈1 / ε⌉₊ 1)), fun W hW E hE K hK => ?_⟩
  have hWL : WL ≤ W := le_trans (by simp) hW
  have hWs : Ws ≤ W := le_trans (by simp) hW
  have hW3 : W₃ ≤ W := le_trans (by simp) hW
  have hWε : ⌈1 / ε⌉₊ ≤ W := le_trans (by simp) hW
  have hW1 : 1 ≤ W := le_trans (by simp) hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  obtain ⟨hE1, hE2⟩ := bulk_bounds hκ hE
  have hj0 : 1 ≤ ⌊(W : ℝ) * ε⌋₊ := by
    refine Nat.le_floor ?_
    have : 1 / ε ≤ W := Nat.ceil_le.mp hWε
    rw [div_le_iff₀ hε] at this
    push_cast; linarith
  set k := ⌊(W : ℝ) * ε⌋₊ - 1
  have hk : k + 1 = ⌊(W : ℝ) * ε⌋₊ := by omega
  set N := ⌊T * W⌋₊
  have hNR : (N : ℝ) ≤ T * W := Nat.floor_le (by nlinarith)
  have hsub : {ω | ∃ j : ℕ, ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧
      K < nuclearNorm (pathCurrent b E W j ω)} ⊆
      {ω | ∃ j : ℕ, ⌊(W : ℝ) * ε⌋₊ ≤ j ∧ j ≤ N ∧ K < nuclearNorm (pathCurrent b E W j ω)} := by
    rintro ω ⟨j, h1, h2, h3⟩
    refine ⟨j, ?_, Nat.le_floor h2, h3⟩
    have : (⌊(W : ℝ) * ε⌋₊ : ℝ) ≤ j :=
      (Nat.floor_le (by positivity)).trans (by linarith [mul_comm (W : ℝ) ε])
    exact_mod_cast this
  have h := current_tail_at hb0 hb hE1 hE2 hW1 (hL W hWL E hE) hCa hC₂ hCN hCf hCm hKw hρ0 hρ1
    hKL hd1 hρLd hdd₀ hd0.le k N hNR hK
  rw [hk] at h
  have hP : growthPathLaw W b (stopEv b E W k d N)ᶜ ≤ ENNReal.ofReal η := by
    refine (measure_mono (stopEv_compl_subset b E k d T hNR)).trans
      ((hSup W hWs E hE).trans (ENNReal.ofReal_le_ofReal ?_))
    have h3 := hW₃ W hW3 0 (by simp)
    rw [pow_zero, one_mul] at h3
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 1 / η)).mpr h3
    rwa [one_div_one_div] at this
  exact (measure_mono hsub).trans (h.trans (add_le_add_left hP _))

/-- **`CurrentNuclearTail`** from the input hypotheses and `FractionalTransmissionUniform`. -/
theorem currentNuclearTail_of (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hFr : FractionalTransmissionUniform) : CurrentNuclearTail := by
  intro b hb0 hb κI hκ ε T hε hεT
  have hFS := fullSourceEstimates_holds hGA hLp
  obtain ⟨A, hA, hbd⟩ := current_tail_bound hFS (passiveMeanStep_holds (passiveBounds_holds hGA hLp))
    (passiveFluctuationStep_holds hGA hLp) (superexpExit_of hSR) hb0 hb hκ hε hεT
  obtain ⟨C₀, hC₀⟩ := hFr b hb0 hb κI hκ ε hε
  refine ⟨A * max C₀ 0, fun K hK => ?_⟩
  set g : ℕ → ℝ≥0∞ := fun W => ⨆ (E : ℝ) (_ : E ∈ bulkInterval κI),
    ∫⁻ ω, ENNReal.ofReal (fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * ε⌋₊ ω))
      ∂growthPathLaw W b
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  have hη' : (0 : ℝ) < η := by exact_mod_cast hη
  obtain ⟨W₀, hW₀⟩ := hbd η hη'
  have hev : ∀ᶠ W : ℕ in atTop, (⨆ (E : ℝ) (_ : E ∈ bulkInterval κI),
      growthPathLaw W b {ω | ∃ j : ℕ, ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧
        K < nuclearNorm (pathCurrent b E W j ω)}) ≤
      ENNReal.ofReal η + ENNReal.ofReal (A / K) * g W := by
    filter_upwards [eventually_ge_atTop W₀] with W hW
    refine iSup₂_le fun E hE => (hW₀ W hW E hE K hK).trans ?_
    gcongr
    exact le_iSup₂_of_le (f := fun (E : ℝ) (_ : E ∈ bulkInterval κI) =>
      ∫⁻ ω, ENNReal.ofReal (fracTrace (1 / 2)
        (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * ε⌋₊ ω)) ∂growthPathLaw W b) E hE le_rfl
  calc _ ≤ limsup (fun W => ENNReal.ofReal η + ENNReal.ofReal (A / K) * g W) atTop :=
        limsup_le_limsup hev
    _ = ENNReal.ofReal η + ENNReal.ofReal (A / K) * limsup g atTop := by
        rw [limsup_const_add atTop _ _ (by isBoundedDefault) (by isBoundedDefault),
          ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal η + ENNReal.ofReal (A / K) * ENNReal.ofReal (max C₀ 0) := by
        gcongr; exact hC₀.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    _ = ENNReal.ofReal (A * max C₀ 0 / K) + η := by
        rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal, add_comm]
        congr 2; ring

/-- The fixed-`E` fractional bound at `p = 1/2`: `limsup_W E Tr T_{⌊Wε⌋}^{1/2} ≤ C`. -/
def FractionalTransmissionFixed : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
    limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
        (fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * ε⌋₊ ω))
        ∂growthPathLaw W b) atTop ≤ ENNReal.ofReal C

/-- The `TransmissionLawContract.fractional` field (`p = 1/2`, `t = ε`) gives the
fixed-`E` fractional bound. -/
theorem fractionalTransmissionFixed_of_law (hTL : TransmissionLawContract) :
    FractionalTransmissionFixed := by
  intro b hb0 hb E h1 h2 ε hε
  obtain ⟨C, hC⟩ := hTL.fractional b hb0 hb E h1 h2 (1 / 2) (by norm_num) (by norm_num)
  exact ⟨C * (1 + ε⁻¹), hC ε hε⟩

/-- The fixed-`E` tail of the current's nuclear norm. -/
def CurrentNuclearTailFixed : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ ε T : ℝ, 0 < ε → ε < T →
    ∃ C : ℝ, ∀ K : ℝ, 0 < K →
      limsup (fun W : ℕ => growthPathLaw W b {ω | ∃ j : ℕ, ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧
          K < nuclearNorm (pathCurrent b E W j ω)}) atTop ≤ ENNReal.ofReal (C / K)

/-- **`CurrentNuclearTailFixed`** from the input hypotheses and `FractionalTransmissionFixed`. -/
theorem currentNuclearTailFixed_of (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hFr : FractionalTransmissionFixed) :
    CurrentNuclearTailFixed := by
  intro b hb0 hb E h1 h2 ε T hε hεT
  obtain ⟨hκ, hE⟩ := mem_bulk_self h1 h2
  have hFS := fullSourceEstimates_holds hGA hLp
  obtain ⟨A, hA, hbd⟩ := current_tail_bound hFS (passiveMeanStep_holds (passiveBounds_holds hGA hLp))
    (passiveFluctuationStep_holds hGA hLp) (superexpExit_of hSR) hb0 hb hκ hε hεT
  obtain ⟨C₀, hC₀⟩ := hFr b hb0 hb E h1 h2 ε hε
  refine ⟨A * max C₀ 0, fun K hK => ?_⟩
  set g : ℕ → ℝ≥0∞ := fun W => ∫⁻ ω, ENNReal.ofReal
    (fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * ε⌋₊ ω)) ∂growthPathLaw W b
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  have hη' : (0 : ℝ) < η := by exact_mod_cast hη
  obtain ⟨W₀, hW₀⟩ := hbd η hη'
  have hev : ∀ᶠ W : ℕ in atTop, growthPathLaw W b {ω | ∃ j : ℕ, ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧
      K < nuclearNorm (pathCurrent b E W j ω)} ≤ ENNReal.ofReal η + ENNReal.ofReal (A / K) * g W := by
    filter_upwards [eventually_ge_atTop W₀] with W hW
    exact hW₀ W hW E hE K hK
  calc _ ≤ limsup (fun W => ENNReal.ofReal η + ENNReal.ofReal (A / K) * g W) atTop :=
        limsup_le_limsup hev
    _ = ENNReal.ofReal η + ENNReal.ofReal (A / K) * limsup g atTop := by
        rw [limsup_const_add atTop _ _ (by isBoundedDefault) (by isBoundedDefault),
          ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal η + ENNReal.ofReal (A / K) * ENNReal.ofReal (max C₀ 0) := by
        gcongr; exact hC₀.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    _ = ENNReal.ofReal (A * max C₀ 0 / K) + η := by
        rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal, add_comm]
        congr 2; ring

end BlockBand.SourceProcess.FullSourceStops
