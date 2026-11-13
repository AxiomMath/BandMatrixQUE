module

public import BlockBand.SourceProcess.PhysApprox.B3JetClosing

/-!
# The closed jet at one moment order `p`

**Moment order.** In `closedJetLp_of` the jet in `L^p`
uses the closed start in `L^p` and in `L^{p+2}` (Markov at `p + 2` for the start exit), hence
`FarFracTraceMoments` at `p` and at `p + 2`. Here the start exit uses Markov at `p` only (one
term, `μ(δ₀(X_cl,n_s) > d₀/2) ≤ (2S_p/(d₀W))^p`; the `p + 2` stays only on the fresh errors,
which come from the contract hypotheses). So **the jet in `L^p` needs the fractional moments at the
same `p` only** (with `α < 1/p`):

* `FarFracTraceMomentsAt p`, `ClosedJetShiftStartLpAt p`, `ClosedJetStartLpAt p`: the estimates at
  one order;
* `closedJetShiftStartLpAt_of_frac`, `closedJetStartLpAt_of_shift`, **`closedJetLpAt_of`**;
* **`closedJetLpAt_b3ClosedX`**: `MatchedTracesContract`, `GaussianAbsorptionContract`,
  `GaussianLpGradient`, `ClosedShiftDiscTrace` and `FarFracTraceMomentsAt p` give
  `‖δ₀(b3ClosedX_j)‖_p ≤ C/W` at every `n_s ≤ j < ⌊WT⌋`;
* **`closedJetL4Fam_b3ClosedX_of_fracAt`**: `ClosedJetL4Fam b3ClosedX` from
  `FarFracTraceMomentsAt 4` (that is, `α < 1/4`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet

open MeasureTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.LengthUniform BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.Closing
open scoped ENNReal ComplexOrder

/-- `FarFracTraceMoments` at one order `p`. -/
def FarFracTraceMomentsAt (p : ℝ) : Prop :=
  ∀ b E : ℝ, 0 < b → b < 1 / 2 → -2 < E → E < 2 → ∀ s : ℝ, 0 < s →
    ∃ α : ℝ, 0 < α ∧ α * p < 1 ∧ ∃ C : ℝ, ∀ᶠ W in atTop,
      ∫⁻ ω, ENNReal.ofReal (farFracTrace b E α W (closeLen s W) ω ^ p) ∂growthPathLaw W b ≤
        ENNReal.ofReal C

theorem farFracTraceMomentsAt_of (hB : FarFracTraceMoments) {p : ℝ} (hp : 1 ≤ p) :
    FarFracTraceMomentsAt p := fun b E h0 h1 h2 h3 s hs => hB b E h0 h1 h2 h3 s hs p hp

/-- `ClosedJetShiftStartLp` at one order `p`. -/
def ClosedJetShiftStartLpAt (p : ℝ) (Xcl : ClosedInputFam) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∃ C : ℝ, ∀ᶠ W in atTop,
      eLpNorm (fun y => jetShift b E (Xcl b E s h τ m W (closeLen s W) y) (closeLen s W) y)
        (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- `ClosedJetStartLp` at one order `p`. -/
def ClosedJetStartLpAt (p : ℝ) (Xcl : ClosedInputFam) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∃ C : ℝ, ∀ᶠ W in atTop,
      eLpNorm (fun y => jetDistance0 b E (Xcl b E s h τ m W (closeLen s W) y))
        (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

theorem closedJetShiftStartLpAt_of_frac (hA : ClosedShiftDiscTrace) {p : ℝ} (hp : 1 ≤ p)
    (hB : FarFracTraceMomentsAt p) : ClosedJetShiftStartLpAt p b3ClosedX := by
  intro b E np τ m T s h K Vs hF
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, hs, -, hh0, hh1, -⟩ := id hF
  obtain ⟨α, hα0, hαp, CF, hCF⟩ := hB b E hb0 hb hE1 hE2 s hs
  have hp0 : 0 < p := by linarith
  have hα1 : α ≤ 1 := by nlinarith
  have hβ0 : 0 ≤ α * p := by positivity
  set Lθ := ∫⁻ θ, ENNReal.ofReal (‖1 - phase θ‖ ^ (-(α * p))) ∂phaseLaw with hLθ
  have hLθ' : Lθ < ∞ := lintegral_phase_rpow_lt_top hβ0 hαp
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval (min (2 + E) (2 - E)) :=
    ⟨by have := min_le_left (2 + E) (2 - E); linarith,
      by have := min_le_right (2 + E) (2 - E); linarith⟩
  have hη : 0 < etaZ b E := lt_of_lt_of_le (etaLow_pos (by linarith : b < 1) hκ)
    (etaLow_le (by linarith : b < 1) hκ hEb)
  set kc := kernelConst h α
  have hkc : 0 ≤ kc := by unfold kc kernelConst; positivity
  set A0 := 2 / etaZ b E * kc
  have hA00 : 0 ≤ A0 := by positivity
  set X := max CF 0 * Lθ.toReal
  have hX0 : 0 ≤ X := mul_nonneg (le_max_right _ _) ENNReal.toReal_nonneg
  refine ⟨A0 * X ^ p⁻¹, ?_⟩
  filter_upwards [hA b E np τ m T s h K Vs hF, hCF, eventually_ge_atTop 1] with W hWA hWF hW1
  have hx0 : (0 : ℝ) < W := by exact_mod_cast hW1
  set n := closeLen s W
  set μ := closedLaw b W np
  set Δ : ProbedPath W np × ℝ → ℝ := fun y => jetShift b E (b3ClosedX b E s h τ m W n y) n y
  have hΔm : Measurable Δ := measurable_jetShift_b3ClosedX b E s h τ m n
  have hΔ0 : ∀ y, 0 ≤ Δ y := fun y => norm_nonneg _
  set F : GrowthPath W → ℝ := fun ω => farFracTrace b E α W n ω
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => Finset.sum_nonneg fun k _ => by positivity
  set A := A0 / W
  have hA0 : 0 ≤ A := by positivity
  -- the pointwise bound, a.e.
  have hph : ∀ᵐ y ∂μ, y.2 ∈ Ioo 0 (2 * Real.pi) := by
    rw [ae_iff]
    have : {y : ProbedPath W np × ℝ | ¬ y.2 ∈ Ioo 0 (2 * Real.pi)} =
        Set.univ ×ˢ {θ | ¬ θ ∈ Ioo 0 (2 * Real.pi)} := by ext y; simp
    rw [this, Measure.prod_prod, ← ae_iff.1 ae_phaseLaw_mem_Ioo, mul_comm]
    simp
  have hpt : ∀ᵐ y ∂μ, Δ y ≤ A * (‖1 - phase y.2‖ ^ (-α) * F y.1.1) := by
    filter_upwards [hWA, hph] with y hy hθ
    have hy' := hy (boundaryZ b E) (by rw [sub_self, norm_zero]; positivity)
    rw [← jetShift_eq_nearTraceAt] at hy'
    refine hy'.trans ?_
    have hS := sum_shiftKernel_le hh0 hh1 hα0 hα1 (norm_phase y.2) (phase_ne_one hθ)
      (farEig b E W n y.1.1)
    have hw : 0 ≤ ‖1 - phase y.2‖ ^ (-α) := Real.rpow_nonneg (norm_nonneg _) _
    calc 2 / (etaZ b E * W) * ∑ k, shiftKernel h (farEig b E W n y.1.1 k) (phase y.2)
        ≤ 2 / (etaZ b E * W) * (kc * ‖1 - phase y.2‖ ^ (-α) * F y.1.1) := by
          gcongr; exact hS
      _ = A * (‖1 - phase y.2‖ ^ (-α) * F y.1.1) := by
          simp only [A, A0]; field_simp
  -- the `p`-th moment
  have hpow : ∀ᵐ y ∂μ, ‖Δ y‖ₑ ^ p ≤ ENNReal.ofReal (A ^ p) *
      (ENNReal.ofReal (F y.1.1 ^ p) * ENNReal.ofReal (‖1 - phase y.2‖ ^ (-(α * p)))) := by
    filter_upwards [hpt] with y hy
    rw [Real.enorm_eq_ofReal (hΔ0 y), ENNReal.ofReal_rpow_of_nonneg (hΔ0 y) hp0.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (hF0 _) p),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hA0 p)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hw : 0 ≤ ‖1 - phase y.2‖ ^ (-α) := Real.rpow_nonneg (norm_nonneg _) _
    calc Δ y ^ p ≤ (A * (‖1 - phase y.2‖ ^ (-α) * F y.1.1)) ^ p :=
          Real.rpow_le_rpow (hΔ0 y) hy hp0.le
      _ = A ^ p * (F y.1.1 ^ p * ‖1 - phase y.2‖ ^ (-(α * p))) := by
          rw [Real.mul_rpow hA0 (mul_nonneg hw (hF0 _)), Real.mul_rpow hw (hF0 _),
            ← Real.rpow_mul (norm_nonneg _), neg_mul]
          ring
  have hint : ∫⁻ y, ‖Δ y‖ₑ ^ p ∂μ ≤ ENNReal.ofReal (A ^ p) * (ENNReal.ofReal (max CF 0) * Lθ) := by
    refine (lintegral_mono_ae hpow).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    refine (lintegral_closedLaw_mul_le b W np (fun ω => ENNReal.ofReal (F ω ^ p))
      (fun θ => ENNReal.ofReal (‖1 - phase θ‖ ^ (-(α * p)))) (fun _ => ENNReal.ofReal_ne_top)
      hLθ'.ne).trans ?_
    gcongr
    exact hWF.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hLθeq : Lθ = ENNReal.ofReal Lθ.toReal := (ENNReal.ofReal_toReal hLθ'.ne).symm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top
    hΔm.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
  calc (∫⁻ y, ‖Δ y‖ₑ ^ p ∂μ) ^ (1 / p)
      ≤ (ENNReal.ofReal (A ^ p) * (ENNReal.ofReal (max CF 0) * Lθ)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hint (by positivity)
    _ = ENNReal.ofReal (A * X ^ p⁻¹) := by
        rw [hLθeq, ← ENNReal.ofReal_mul (le_max_right _ _), ← ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hA0,
          mul_one_div_cancel hp0.ne', Real.rpow_one, one_div]
    _ = ENNReal.ofReal (A0 * X ^ p⁻¹ / W) := by
        congr 1; simp only [A]; ring

theorem closedJetStartLpAt_of_shift (hδ : DeltaZeroLengthUniform) {Xcl : ClosedInputFam}
    {p : ℝ} (hp : 1 ≤ p)
    (hXm : ∀ (b E s h : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (W j : ℕ),
      Measurable (Xcl b E s h τ m W j))
    (hSh : ClosedJetShiftStartLpAt p Xcl) : ClosedJetStartLpAt p Xcl := by
  intro b E np τ m T s h K Vs hF
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, hs, -, -, -, -⟩ := id hF
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval (min (2 + E) (2 - E)) :=
    ⟨by have := min_le_left (2 + E) (2 - E); linarith,
      by have := min_le_right (2 + E) (2 - E); linarith⟩
  obtain ⟨Cδ, hCδ, hδT⟩ := hδ b hb0 hb _ p hκ hp
  obtain ⟨W₀, hW₀⟩ := hδT s
  obtain ⟨C₁, hC₁⟩ := hSh b E np τ m T s h K Vs hF
  refine ⟨Cδ + max C₁ 0, ?_⟩
  filter_upwards [hC₁, eventually_ge_atTop (max W₀ (max 1 ⌈s⁻¹⌉₊))] with W hW hWb
  simp only [max_le_iff] at hWb
  obtain ⟨hW0, hW1, hWs⟩ := hWb
  have hx1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hx0 : (0 : ℝ) < W := by linarith
  set r := closeLen s W with hr
  have hr1 : 1 ≤ r := by
    rw [hr, closeLen, Nat.one_le_floor_iff]
    have h1 := (Nat.le_ceil s⁻¹).trans (by exact_mod_cast hWs : (⌈s⁻¹⌉₊ : ℝ) ≤ W)
    rw [inv_le_iff_one_le_mul₀ hs] at h1
    linarith
  have hrT : (r : ℝ) ≤ s * W := by
    rw [hr, closeLen, mul_comm]; exact Nat.floor_le (by positivity)
  have hopen := hW₀ W hW0 E hEb r hr1 hrT
  rw [← eLpNorm_open_closedLaw b E W np r] at hopen
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hpt : ∀ y : ProbedPath W np × ℝ, ‖jetDistance0 b E (Xcl b E s h τ m W r y)‖ ≤
      ‖jetDistance0 b E (pathX b E W r y.1.1) + jetShift b E (Xcl b E s h τ m W r y) r y‖ := by
    intro y
    have htri := norm_sub_le_norm_sub_add_norm_sub
      ((W : ℂ)⁻¹ * (passiveResolvent b E (Xcl b E s h τ m W r y)).trace)
      ((W : ℂ)⁻¹ * (passiveResolvent b E (pathX b E W r y.1.1)).trace) (matchedA E)
    have h0 : 0 ≤ jetDistance0 b E (Xcl b E s h τ m W r y) := norm_nonneg _
    have h0' : 0 ≤ jetDistance0 b E (pathX b E W r y.1.1) := norm_nonneg _
    have h0'' : 0 ≤ jetShift b E (Xcl b E s h τ m W r y) r y := norm_nonneg _
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (by positivity)]
    unfold jetDistance0 jetShift
    linarith
  have hmX : AEStronglyMeasurable (fun y => jetDistance0 b E (Xcl b E s h τ m W r y))
      (closedLaw b W np) :=
    ((measurable_jetDistance0 b E).comp (hXm b E s h np τ m W r)).aestronglyMeasurable
  calc eLpNorm (fun y => jetDistance0 b E (Xcl b E s h τ m W r y)) (ENNReal.ofReal p)
        (closedLaw b W np)
      ≤ eLpNorm ((fun y : ProbedPath W np × ℝ => jetDistance0 b E (pathX b E W r y.1.1)) +
          fun y => jetShift b E (Xcl b E s h τ m W r y) r y) (ENNReal.ofReal p)
            (closedLaw b W np) :=
        eLpNorm_mono hmX hpt
    _ ≤ ENNReal.ofReal (Cδ / W) + ENNReal.ofReal (max C₁ 0 / W) :=
        (eLpNorm_add_le hp1).trans (add_le_add hopen (hW.trans (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (le_max_left _ _) hx0.le))))
    _ = ENNReal.ofReal ((Cδ + max C₁ 0) / W) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_div]

theorem closedJetLpAt_of (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {Xcl : ClosedInputFam} (hReg : ClosedInputRegular Xcl) (hRec : ClosedInputRecursion Xcl)
    {p : ℝ} (hp : 1 ≤ p) (hStart : ClosedJetStartLpAt p Xcl) :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ W in atTop,
        ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          eLpNorm (fun y => jetDistance0 b E (Xcl b E s h τ m W j y)) (ENNReal.ofReal p)
            (closedLaw b W np) ≤ ENNReal.ofReal (C / W) := by
  intro b E np τ m T s h K Vs hF
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, -, -, -, -, -⟩ := id hF
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval (min (2 + E) (2 - E)) :=
    ⟨by have := min_le_left (2 + E) (2 - E); linarith,
      by have := min_le_right (2 + E) (2 - E); linarith⟩
  obtain ⟨d₀, ρ, Cm, Wm, hd₀, hρ0, hρ1, hCm, hmean⟩ :=
    passiveMeanStep_holds (passiveBounds_holds hGA hLp) b hb0 hb _ hκ
  obtain ⟨Cp, Wp, hCp, hflp⟩ := passiveFluctuationStep_holds hGA hLp b hb0 hb _ hκ p hp
  obtain ⟨Cq, Wq, hCq, hflq⟩ :=
    passiveFluctuationStep_holds hGA hLp b hb0 hb _ hκ (p + 2) (by linarith)
  obtain ⟨S1, hS1⟩ := hStart b E np τ m T s h K Vs hF
  have h1ρ : 0 < 1 - ρ := by linarith
  set t := (1 - ρ) * d₀ / 2 with ht
  have ht0 : 0 < t := by positivity
  set M := (etaZ b E)⁻¹ + 1 with hM
  have hM0 : 0 ≤ M := by
    have := (etaLow_pos (by linarith : b < 1) hκ).le.trans
      (etaLow_le (by linarith : b < 1) hκ hEb)
    positivity
  set S1' := max S1 0
  have hS1'0 : 0 ≤ S1' := le_max_right _ _
  set A := (d₀ / 2)⁻¹ ^ p * S1' ^ p with hA
  set B := t⁻¹ ^ (p + 2) * Cq ^ (p + 2) with hB
  have hA0 : 0 ≤ A := mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (le_max_right _ _) _)
  have hB0 : 0 ≤ B := mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hCq _)
  set Kb := A + max T 0 * B with hKb
  have hKb0 : 0 ≤ Kb := by have := le_max_right T 0; positivity
  have hp0 : (0 : ℝ) < p := by linarith
  refine ⟨S1' + (Cm + Cp) / (1 - ρ) + Kb ^ p⁻¹ * M, by positivity, ?_⟩
  filter_upwards [hReg b E np τ m T s h K Vs hF, hRec b E np τ m T s h K Vs hF, hS1,
    eventually_ge_atTop (max (max Wm (max Wp Wq))
      (max 1 ⌈Cm / ((1 - ρ) * d₀ / 2)⌉₊))]
    with W hWreg hWrec hWS1 hWbig j hj
  simp only [max_le_iff] at hWbig
  obtain ⟨⟨hWm, hWp, hWq⟩, hW1, hWC⟩ := hWbig
  have hx : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hx0 : (0 : ℝ) < W := by linarith
  obtain ⟨hjs, hjT⟩ := Finset.mem_Ico.1 hj
  set j₀ := closeLen s W with hj₀
  have hWd : Cm / (W : ℝ) ^ 2 ≤ (1 - ρ) * d₀ / 2 := by
    have hud : 0 < (1 - ρ) * d₀ / 2 := by positivity
    have h1 := (Nat.le_ceil (Cm / ((1 - ρ) * d₀ / 2))).trans
      (by exact_mod_cast hWC : (⌈Cm / ((1 - ρ) * d₀ / 2)⌉₊ : ℝ) ≤ W)
    rw [div_le_iff₀ hud] at h1
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hS1' : eLpNorm (fun y => jetDistance0 b E (Xcl b E s h τ m W j₀ y)) (ENNReal.ofReal p)
      (closedLaw b W np) ≤ ENNReal.ofReal (S1' / W) :=
    hWS1.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hx0.le))
  have key := eLpNorm_jet_le (np := np) hb0 hb hE1 hE2 hp hd₀ hρ0 hρ1 hCm hCp hCq
    (by positivity : 0 ≤ S1' / W) hWd (fun X hX hd => hmean W hWm E hEb X hX hd)
    (fun X hX => hflp W hWp E hEb X hX) (fun X hX => hflq W hWq E hEb X hX)
    (fun j => Xcl b E s h τ m W j) hjs
    (fun j' h1 h2 => (hWreg j' (Finset.mem_Ico.2 ⟨h1, lt_of_le_of_lt h2 hjT⟩)).1)
    (fun j' h1 h2 => (hWreg j' (Finset.mem_Ico.2 ⟨h1, lt_of_le_of_lt h2 hjT⟩)).2.1)
    (fun j' h1 h2 => (hWreg j' (Finset.mem_Ico.2 ⟨h1, lt_of_le_of_lt h2 hjT⟩)).2.2)
    (fun j' h1 h2 => hWrec j' h1 (by omega)) hS1'
  have hm1 := markov_ofReal (closedLaw b W np) (fun y => norm_nonneg _)
    hp0 (by positivity : (0 : ℝ) < d₀ / 2)
    (by positivity : (0 : ℝ) ≤ S1' / W) hS1'
  have hWi : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  have hdiv : ∀ (y q : ℝ), 0 ≤ y → (y / W) ^ q = y ^ q * (W : ℝ)⁻¹ ^ q :=
    fun y q hy => by rw [div_eq_mul_inv, Real.mul_rpow hy hWi]
  have hnT : ((j - j₀ : ℕ) : ℝ) ≤ T * W := by
    have hT1 : 0 < ⌊(W : ℝ) * T⌋₊ := lt_of_le_of_lt (Nat.zero_le _) hjT
    have hWT : 0 ≤ (W : ℝ) * T := le_trans zero_le_one (Nat.floor_pos.1 hT1)
    have h1 : ((j - j₀ : ℕ) : ℝ) ≤ j := by exact_mod_cast Nat.sub_le j j₀
    have h2 : (j : ℝ) ≤ ⌊(W : ℝ) * T⌋₊ := by exact_mod_cast hjT.le
    have h3 := Nat.floor_le hWT
    linarith
  have hbadR : (d₀ / 2)⁻¹ ^ p * (S1' / W) ^ p +
      ((j - j₀ : ℕ) : ℝ) * (t⁻¹ ^ (p + 2) * (Cq / W) ^ (p + 2)) ≤ Kb * (W : ℝ)⁻¹ ^ p := by
    have hx1 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
    have hxi0 : 0 < (W : ℝ)⁻¹ := by positivity
    have h2 := bad_arith (A := 0) (B := B) (T := T) (p := p + 1) (r := j - j₀) le_rfl hB0 hx hnT
    rw [show p + 1 + 1 = p + 2 by ring] at h2
    have h3 : (W : ℝ)⁻¹ ^ (p + 1) ≤ (W : ℝ)⁻¹ ^ p :=
      Real.rpow_le_rpow_of_exponent_ge hxi0 hx1 (by linarith)
    rw [hdiv S1' p (le_max_right _ _), hdiv Cq (p + 2) hCq]
    have e1 : (d₀ / 2)⁻¹ ^ p * (S1' ^ p * (W : ℝ)⁻¹ ^ p) = A * (W : ℝ)⁻¹ ^ p := by
      simp only [hA]; ring
    have e2 : ((j - j₀ : ℕ) : ℝ) * (t⁻¹ ^ (p + 2) * (Cq ^ (p + 2) * (W : ℝ)⁻¹ ^ (p + 2))) =
        ((j - j₀ : ℕ) : ℝ) * (B * (W : ℝ)⁻¹ ^ (p + 2)) := by
      simp only [hB]; ring
    rw [e1, e2, hKb, add_mul]
    have hTB : 0 ≤ max T 0 * B := by have := le_max_right T 0; positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 hTB]
  have hpow : (closedLaw b W np {y | d₀ / 2 < jetDistance0 b E (Xcl b E s h τ m W j₀ y)} +
      ENNReal.ofReal (((j - j₀ : ℕ) : ℝ) *
        (((1 - ρ) * d₀ / 2)⁻¹ ^ (p + 2) * (Cq / W) ^ (p + 2)))) ^
        (ENNReal.ofReal p).toReal⁻¹ ≤ ENNReal.ofReal (Kb ^ p⁻¹ * (W : ℝ)⁻¹) := by
    rw [ENNReal.toReal_ofReal hp0.le]
    have hsum : closedLaw b W np {y | d₀ / 2 < jetDistance0 b E (Xcl b E s h τ m W j₀ y)} +
        ENNReal.ofReal (((j - j₀ : ℕ) : ℝ) *
          (((1 - ρ) * d₀ / 2)⁻¹ ^ (p + 2) * (Cq / W) ^ (p + 2))) ≤
        ENNReal.ofReal (Kb * (W : ℝ)⁻¹ ^ p) := by
      refine (add_le_add hm1 le_rfl).trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal hbadR
    refine (ENNReal.rpow_le_rpow hsum (inv_nonneg.2 hp0.le)).trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (inv_nonneg.2 hp0.le),
      Real.mul_rpow hKb0 (by positivity), Real.rpow_rpow_inv hWi hp0.ne']
  refine key.trans ?_
  calc ENNReal.ofReal (S1' / W + (Cm / (W : ℝ) ^ 2 + Cp / W) / (1 - ρ)) +
        (closedLaw b W np {y | d₀ / 2 < jetDistance0 b E (Xcl b E s h τ m W j₀ y)} +
          ENNReal.ofReal (((j - j₀ : ℕ) : ℝ) *
            (((1 - ρ) * d₀ / 2)⁻¹ ^ (p + 2) * (Cq / W) ^ (p + 2)))) ^
          (ENNReal.ofReal p).toReal⁻¹ * ENNReal.ofReal M
      ≤ ENNReal.ofReal (S1' / W + (Cm / (W : ℝ) ^ 2 + Cp / W) / (1 - ρ)) +
          ENNReal.ofReal (Kb ^ p⁻¹ * (W : ℝ)⁻¹) * ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal (S1' / W + (Cm / (W : ℝ) ^ 2 + Cp / W) / (1 - ρ) +
          Kb ^ p⁻¹ * (W : ℝ)⁻¹ * M) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
    _ ≤ ENNReal.ofReal ((S1' + (Cm + Cp) / (1 - ρ) + Kb ^ p⁻¹ * M) / W) :=
        ENNReal.ofReal_le_ofReal (absorbed_final_arith hx hCm hρ1)

/-- **The closed jet in `L^p` at `b3ClosedX` from the fractional moments at the same `p`.** -/
theorem closedJetLpAt_b3ClosedX (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hA : ClosedShiftDiscTrace) {p : ℝ} (hp : 1 ≤ p)
    (hB : FarFracTraceMomentsAt p) :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ W in atTop,
        ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          eLpNorm (fun y => jetDistance0 b E (b3ClosedX b E s h τ m W j y)) (ENNReal.ofReal p)
            (closedLaw b W np) ≤ ENNReal.ofReal (C / W) :=
  closedJetLpAt_of hGA hLp (closedInputRegular_b3ClosedX closedInputPassive_b3ClosedX)
    closedInputRecursion_b3ClosedX hp
    (closedJetStartLpAt_of_shift (deltaZeroLengthUniform_holds hMT hGA hLp) hp
      (fun b E s h _ τ m _ j => measurable_b3ClosedX b E s h τ m j)
      (closedJetShiftStartLpAt_of_frac hA hp hB))

/-- **`ClosedJetL4Fam b3ClosedX` from the fractional moments at `p = 4` only.** -/
theorem closedJetL4Fam_b3ClosedX_of_fracAt (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hA : ClosedShiftDiscTrace)
    (hB : FarFracTraceMomentsAt 4) : ClosedJetL4Fam b3ClosedX := by
  intro b E np τ m T s h K Vs hF
  obtain ⟨C, hC0, hC⟩ := closedJetLpAt_b3ClosedX hMT hGA hLp hA (by norm_num) hB
    b E np τ m T s h K Vs hF
  refine ⟨C ^ 4, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with W hW hW1 j hj _
  have hx0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hm : Measurable fun y => jetDistance0 b E (b3ClosedX b E s h τ m W j y) :=
    (measurable_jetDistance0 b E).comp (measurable_b3ClosedX b E s h τ m j)
  refine (lintegral_ofReal_pow_four_le _ (fun y => norm_nonneg _) hm (by positivity)
    (hW j hj)).trans (le_of_eq ?_)
  rw [div_pow]

end BlockBand.SourceProcess.PhysApprox.B3.Jet
