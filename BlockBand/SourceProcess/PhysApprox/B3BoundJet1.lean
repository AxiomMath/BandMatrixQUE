module

public import BlockBand.SourceProcess.PhysApprox.B3BoundJet
public import BlockBand.SourceProcess.PhysApprox.B3JetNbhd

/-!
# The closed `δ₁` jet at bounded moment order

* `ClosedJetShiftNbhdLpLe P`, `ClosedJet1ShiftLpLe P`, `ClosedJet1StartLe P`: the original
  `ClosedJetShiftNbhdLp`, `ClosedJet1ShiftLp`, `ClosedJet1Start` with `p ≤ P`;
* `Jet.closedShiftDisc_dominatedAt`, `Jet.closedJetShiftNbhdLpLe_of_frac`: the shift from
  `FarFracTraceMomentsAt p` at the same `p`;
* `closedJet1ShiftLpLe_of_nbhd` (Cauchy), `closedJet1StartLe_of_shift`, `closedJet1LpLe_of`;
* **`closedJet1LpLe_of_frac`**: `MatchedTracesContract`, `GaussianAbsorptionContract`,
  `GaussianLpGradient`, `ClosedShiftDiscTrace` and the fractional moments at every
  `1 ≤ p ≤ P` give `ClosedJet1LpLe P`;
* **`closedJet1LpLe_of_frac4`**, **`closedJetsLe_of_frac4`**: from `FarFracTraceMoments4`,
  `ClosedJet1LpLe 4` (and `ClosedJet0LpLe 4`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet1

open MeasureTheory Filter Topology Matrix Metric
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PathJet BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.Transmission.LengthUniform
open scoped ENNReal ComplexOrder

/-!
## Bounded restatements of the shift and restart estimates
-/

/-- **`ClosedJetShiftNbhdLp` at the orders `1 ≤ p ≤ P`.** -/
def ClosedJetShiftNbhdLpLe (P : ℝ) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ p : ℝ, 1 ≤ p → p ≤ P → ∃ r C : ℝ, 0 < r ∧
      ∀ᶠ W in atTop, ∀ w ∈ closedBall (boundaryZ b E) r,
        eLpNorm (fun y => ‖stieltjes (b3ClosedX b E s h τ m W (closeLen s W) y) w -
            stieltjes (pathX b E W (closeLen s W) y.1.1) w‖) (ENNReal.ofReal p)
          (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- **`ClosedJet1ShiftLp` at the orders `1 ≤ p ≤ P`.** -/
def ClosedJet1ShiftLpLe (P : ℝ) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → p ≤ P → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, closeLen s W < ⌊(W : ℝ) * T⌋₊ →
      eLpNorm ((b3Alive b E s h τ m R W (closeLen s W) (Vs W)).indicator
          (fun y => jet1Shift b E (b3ClosedX b E s h τ m W (closeLen s W) y) (closeLen s W) y))
          (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- **`ClosedJet1Start` at the orders `1 ≤ p ≤ P`.** -/
def ClosedJet1StartLe (P : ℝ) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → p ≤ P → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, closeLen s W < ⌊(W : ℝ) * T⌋₊ →
      eLpNorm ((b3Alive b E s h τ m R W (closeLen s W) (Vs W)).indicator
          (fun y => jetDistance1 b E (b3Jet b E) (b3ClosedX b E s h τ m W (closeLen s W) y)))
          (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

theorem closedJetShiftNbhdLpLe_of (h : ClosedJetShiftNbhdLp) (P : ℝ) : ClosedJetShiftNbhdLpLe P :=
  fun b E np τ m T s h' K Vs hF p hp _ => h b E np τ m T s h' K Vs hF p hp

theorem closedJet1ShiftLpLe_of (h : ClosedJet1ShiftLp) (P : ℝ) : ClosedJet1ShiftLpLe P :=
  fun b E np τ m T s h' K Vs hF R p hp _ => h b E np τ m T s h' K Vs hF R p hp

theorem closedJet1StartLe_of (h : ClosedJet1Start) (P : ℝ) : ClosedJet1StartLe P :=
  fun b E np τ m T s h' K Vs hF R p hp _ => h b E np τ m T s h' K Vs hF R p hp

end BlockBand.SourceProcess.PhysApprox.B3.Jet1

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet

open MeasureTheory Filter Topology Matrix Set Metric
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.LengthUniform BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.PhysApprox.B3.Jet1
open scoped ENNReal ComplexOrder

/-!
## The shift from the fractional moments at the same order
-/

/-- **The disc-uniform closing shift is dominated in `L^p`, from the fractional moments at the
same `p`** (adapted from `closedShiftDisc_dominated`; only the order changes): there is `B`
with, a.e., `|W⁻¹Tr(w - X_cl)⁻¹ - W⁻¹Tr(w - X_open)⁻¹| ≤ B` on
`|w - z_∂| ≤ η/2` and `E B^p ≤ (C/W)^p`. -/
theorem closedShiftDisc_dominatedAt (hA : ClosedShiftDiscTrace) {p : ℝ} (hp : 1 ≤ p)
    (hB : FarFracTraceMomentsAt p) :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ W in atTop,
        ∃ B : ProbedPath W np × ℝ → ℝ, (∀ y, 0 ≤ B y) ∧
          (∀ᵐ y ∂closedLaw b W np, ∀ w : ℂ, ‖w - boundaryZ b E‖ ≤ etaZ b E / 2 →
            ‖nearTraceAt W w (b3ClosedX b E s h τ m W (closeLen s W) y) -
              nearTraceAt W w (pathX b E W (closeLen s W) y.1.1)‖ ≤ B y) ∧
          ∫⁻ y, ENNReal.ofReal (B y ^ p) ∂closedLaw b W np ≤ ENNReal.ofReal ((C / W) ^ p) := by
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
  refine ⟨A0 * X ^ p⁻¹, by positivity, ?_⟩
  filter_upwards [hA b E np τ m T s h K Vs hF, hCF, eventually_ge_atTop 1] with W hWA hWF hW1
  have hx0 : (0 : ℝ) < W := by exact_mod_cast hW1
  set n := closeLen s W
  set μ := closedLaw b W np
  set A := A0 / W
  have hA0 : 0 ≤ A := by positivity
  set F : GrowthPath W → ℝ := fun ω => farFracTrace b E α W n ω
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => Finset.sum_nonneg fun k _ => by positivity
  set B : ProbedPath W np × ℝ → ℝ := fun y =>
    2 / (etaZ b E * W) * ∑ k, shiftKernel h (farEig b E W n y.1.1 k) (phase y.2)
  have hker0 : ∀ t z, 0 ≤ shiftKernel h t z := fun t z => by
    unfold shiftKernel; split_ifs <;> positivity
  have hB0 : ∀ y, 0 ≤ B y := fun y =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => hker0 _ _)
  refine ⟨B, hB0, hWA, ?_⟩
  have hph : ∀ᵐ y ∂μ, y.2 ∈ Ioo 0 (2 * Real.pi) := by
    rw [ae_iff]
    have : {y : ProbedPath W np × ℝ | ¬ y.2 ∈ Ioo 0 (2 * Real.pi)} =
        Set.univ ×ˢ {θ | ¬ θ ∈ Ioo 0 (2 * Real.pi)} := by ext y; simp
    rw [this, Measure.prod_prod, ← ae_iff.1 ae_phaseLaw_mem_Ioo, mul_comm]
    simp
  have hpt : ∀ᵐ y ∂μ, B y ^ p ≤ A ^ p * (F y.1.1 ^ p * ‖1 - phase y.2‖ ^ (-(α * p))) := by
    filter_upwards [hph] with y hθ
    have hS := sum_shiftKernel_le hh0 hh1 hα0 hα1 (norm_phase y.2) (phase_ne_one hθ)
      (farEig b E W n y.1.1)
    have hw : 0 ≤ ‖1 - phase y.2‖ ^ (-α) := Real.rpow_nonneg (norm_nonneg _) _
    have hBle : B y ≤ A * (‖1 - phase y.2‖ ^ (-α) * F y.1.1) := by
      calc B y ≤ 2 / (etaZ b E * W) * (kc * ‖1 - phase y.2‖ ^ (-α) * F y.1.1) := by
            simp only [B]; gcongr; exact hS
        _ = A * (‖1 - phase y.2‖ ^ (-α) * F y.1.1) := by
            simp only [A, A0]; field_simp
    calc B y ^ p ≤ (A * (‖1 - phase y.2‖ ^ (-α) * F y.1.1)) ^ p :=
          Real.rpow_le_rpow (hB0 y) hBle hp0.le
      _ = A ^ p * (F y.1.1 ^ p * ‖1 - phase y.2‖ ^ (-(α * p))) := by
          rw [Real.mul_rpow hA0 (mul_nonneg hw (hF0 _)), Real.mul_rpow hw (hF0 _),
            ← Real.rpow_mul (norm_nonneg _), neg_mul]
          ring
  have hint : ∫⁻ y, ENNReal.ofReal (B y ^ p) ∂μ ≤
      ENNReal.ofReal (A ^ p) * (ENNReal.ofReal (max CF 0) * Lθ) := by
    refine (lintegral_mono_ae (hpt.mono fun y hy => (ENNReal.ofReal_le_ofReal hy).trans
      (le_of_eq (by rw [ENNReal.ofReal_mul (Real.rpow_nonneg hA0 p),
        ENNReal.ofReal_mul (Real.rpow_nonneg (hF0 _) p)]))
      )).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    refine (lintegral_closedLaw_mul_le b W np (fun ω => ENNReal.ofReal (F ω ^ p))
      (fun θ => ENNReal.ofReal (‖1 - phase θ‖ ^ (-(α * p)))) (fun _ => ENNReal.ofReal_ne_top)
      hLθ'.ne).trans ?_
    gcongr
    exact hWF.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  refine hint.trans (le_of_eq ?_)
  rw [(ENNReal.ofReal_toReal hLθ'.ne).symm, ← ENNReal.ofReal_mul (le_max_right _ _),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_div_right_comm, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hX0,
    inv_mul_cancel₀ hp0.ne', Real.rpow_one]

/-- **`ClosedJetShiftNbhdLpLe P`** from the cavity-kernel bound on the boundary disc and the
fractional transmission moments at the orders `1 ≤ p ≤ P`, with radius `η/2` (adapted from
`closedJetShiftNbhdLp_of_frac`). -/
theorem closedJetShiftNbhdLpLe_of_frac (hA : ClosedShiftDiscTrace) {P : ℝ}
    (hB : ∀ p : ℝ, 1 ≤ p → p ≤ P → FarFracTraceMomentsAt p) : ClosedJetShiftNbhdLpLe P := by
  intro b E np τ m T s h K Vs hF p hp hpP
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, -⟩ := id hF
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval (min (2 + E) (2 - E)) :=
    ⟨by have := min_le_left (2 + E) (2 - E); linarith,
      by have := min_le_right (2 + E) (2 - E); linarith⟩
  have hη : 0 < etaZ b E := lt_of_lt_of_le (etaLow_pos (by linarith : b < 1) hκ)
    (etaLow_le (by linarith : b < 1) hκ hEb)
  obtain ⟨C, hC0, hC⟩ := closedShiftDisc_dominatedAt hA hp (hB p hp hpP) b E np τ m T s h K Vs hF
  have hp0 : 0 < p := by linarith
  refine ⟨etaZ b E / 2, C, by positivity, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with W hW hW1 w hw
  obtain ⟨B, hB0, hdom, hint⟩ := hW
  have hx0 : (0 : ℝ) < W := by exact_mod_cast hW1
  set n := closeLen s W
  set f : ProbedPath W np × ℝ → ℝ := fun y =>
    ‖stieltjes (b3ClosedX b E s h τ m W n y) w - stieltjes (pathX b E W n y.1.1) w‖ with hfdef
  have hfm : Measurable f :=
    ((measurable_stieltjes_joint.comp ((measurable_b3ClosedX b E s h τ m n).prodMk
      measurable_const)).sub (measurable_stieltjes_joint.comp
        (((measurable_pathX b E n).comp (measurable_fst.comp measurable_fst)).prodMk
          measurable_const))).norm
  have hw' : ‖w - boundaryZ b E‖ ≤ etaZ b E / 2 := by
    rwa [mem_closedBall, dist_eq_norm] at hw
  have hle : ∀ᵐ y ∂closedLaw b W np, ‖f y‖ₑ ^ p ≤ ENNReal.ofReal (B y ^ p) := by
    filter_upwards [hdom] with y hy
    have h1 : f y ≤ B y := hy w hw'
    rw [Real.enorm_eq_ofReal (norm_nonneg _), ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
      hp0.le]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) h1 hp0.le)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top
    hfm.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
  calc (∫⁻ y, ‖f y‖ₑ ^ p ∂closedLaw b W np) ^ (1 / p)
      ≤ (ENNReal.ofReal ((C / W) ^ p)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow ((lintegral_mono_ae hle).trans hint) (by positivity)
    _ = ENNReal.ofReal (C / W) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), one_div,
          Real.rpow_rpow_inv (by positivity) hp0.ne']

end BlockBand.SourceProcess.PhysApprox.B3.Jet

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet1

open MeasureTheory Filter Topology Matrix Metric
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PathJet BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.Transmission.LengthUniform
open scoped ENNReal ComplexOrder

/-!
## The `δ₁` shift, restart and recursion at bounded order
-/

/-- **`ClosedJet1ShiftLpLe P` from the common estimate at the same orders**
and the passivity of `b3ClosedX` (`ClosedInputPassive b3ClosedX`): Cauchy on
`|w - z_∂| = ρ`, `ρ = min(r, Im z_∂/2)`,
then Jensen and Tonelli (adapted from `closedJet1ShiftLp_of_nbhd`). -/
theorem closedJet1ShiftLpLe_of_nbhd {P : ℝ}
    (hP : ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ᶠ W in atTop,
        ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          ∀ᵐ y ∂closedLaw b W np, (passiveY (b3ClosedX b E s h τ m W j y)).PosSemidef)
    (hN : ClosedJetShiftNbhdLpLe P) : ClosedJet1ShiftLpLe P := by
  intro b E np τ m T s h K Vs hFD R p hp hpP
  obtain ⟨⟨-, hb, hE1, hE2, -, -, -, -⟩, -, -, -, -, -⟩ := id hFD
  have hb1 : b < 1 := by linarith
  obtain ⟨r, C, hr, hev⟩ := hN b E np τ m T s h K Vs hFD p hp hpP
  have hzim : 0 < (boundaryZ b E).im := BlockBand.Transmission.Bridge.boundaryZ_im_pos hb1 hE1 hE2
  obtain ⟨ρ, hρ0, hρr, hρz⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ρ < (boundaryZ b E).im :=
    ⟨min r ((boundaryZ b E).im / 2), lt_min hr (by positivity), min_le_left _ _,
      (min_le_right _ _).trans_lt (by linarith)⟩
  have hρi : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ0.le
  refine ⟨ρ⁻¹ * max C 0, by positivity, ?_⟩
  filter_upwards [hev, hP b E np τ m T s h K Vs hFD, hFD.2.2.2.2.2] with W hW hWP hVW hlt
  have hV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hAm : NullMeasurableSet (b3Alive b E s h τ m R W (closeLen s W) (Vs W))
      (closedLaw b W np) :=
    nullMeasurableSet_b3Alive hb1 hE1 hE2 s h τ m R W (closeLen s W) hV
  have hpc : ∀ᵐ y ∂closedLaw b W np,
      (passiveY (b3ClosedX b E s h τ m W (closeLen s W) y)).PosSemidef :=
    hWP _ (Finset.mem_Ico.2 ⟨le_rfl, hlt⟩)
  have hpo : ∀ᵐ y ∂closedLaw b W np, (passiveY (pathX b E W (closeLen s W) y.1.1)).PosSemidef := by
    have h0 : ∀ᵐ ω ∂growthPathLaw W b, (passiveY (pathX b E W (closeLen s W) ω)).PosSemidef := by
      filter_upwards [ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) hb1 hE1 hE2]
        with ω hP'
      exact pathNearSchur_passive hP' _
    rw [← closedLaw_map_path b W np] at h0
    exact ae_of_ae_map (measurable_fst.comp measurable_fst).aemeasurable h0
  have hGm : Measurable (Function.uncurry fun (y : ProbedPath W np × ℝ) (θ : ℝ) =>
      ‖stieltjes (b3ClosedX b E s h τ m W (closeLen s W) y) (circleMap (boundaryZ b E) ρ θ) -
        stieltjes (pathX b E W (closeLen s W) y.1.1) (circleMap (boundaryZ b E) ρ θ)‖) := by
    have hc : Measurable fun q : (ProbedPath W np × ℝ) × ℝ => circleMap (boundaryZ b E) ρ q.2 :=
      (continuous_circleMap _ ρ).measurable.comp measurable_snd
    have h1 := measurable_stieltjes_joint.comp
      (((measurable_b3ClosedX b E s h τ m (closeLen s W)).comp measurable_fst).prodMk hc)
    have h2 := measurable_stieltjes_joint.comp
      ((((measurable_pathX b E (closeLen s W)).comp (measurable_fst.comp measurable_fst)).comp
        measurable_fst).prodMk hc)
    exact (h1.sub h2).norm
  have hθ : ∀ θ : ℝ, eLpNorm (fun y : ProbedPath W np × ℝ =>
      ‖stieltjes (b3ClosedX b E s h τ m W (closeLen s W) y) (circleMap (boundaryZ b E) ρ θ) -
        stieltjes (pathX b E W (closeLen s W) y.1.1) (circleMap (boundaryZ b E) ρ θ)‖)
      (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (max C 0 / W) := fun θ =>
    (hW _ (by
      rw [mem_closedBall, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
        abs_of_pos hρ0]
      exact hρr)).trans (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)))
  have hB := eLpNorm_integral_le_of_forall (closedLaw b W np) phaseLaw hGm hp hθ
  have hf₀ : Measurable fun y : ProbedPath W np × ℝ =>
      ‖-crossTr (b3ClosedX b E s h τ m W (closeLen s W) y) (boundaryZ b E) (boundaryZ b E) -
        -crossTr (pathX b E W (closeLen s W) y.1.1) (boundaryZ b E) (boundaryZ b E)‖ :=
    (((measurable_crossTr_mat _).comp (measurable_b3ClosedX b E s h τ m (closeLen s W))).neg.sub
      ((measurable_crossTr_mat _).comp ((measurable_pathX b E (closeLen s W)).comp
        (measurable_fst.comp measurable_fst))).neg).norm
  have hae : ∀ᵐ y ∂closedLaw b W np,
      jet1Shift b E (b3ClosedX b E s h τ m W (closeLen s W) y) (closeLen s W) y =
        ‖-crossTr (b3ClosedX b E s h τ m W (closeLen s W) y) (boundaryZ b E) (boundaryZ b E) -
          -crossTr (pathX b E W (closeLen s W) y.1.1) (boundaryZ b E) (boundaryZ b E)‖ := by
    filter_upwards [hpc, hpo] with y h1 h2
    rw [jet1Shift, jet1D_eq_deriv, jet1D_eq_deriv, deriv_stieltjes h1 hzim,
      deriv_stieltjes h2 hzim]
  have hm : AEStronglyMeasurable ((b3Alive b E s h τ m R W (closeLen s W) (Vs W)).indicator
      fun y => jet1Shift b E (b3ClosedX b E s h τ m W (closeLen s W) y) (closeLen s W) y)
      (closedLaw b W np) := by
    refine (hf₀.aestronglyMeasurable.indicator₀ hAm).congr ?_
    filter_upwards [hae] with y hy
    by_cases hyA : y ∈ b3Alive b E s h τ m R W (closeLen s W) (Vs W)
    · rw [Set.indicator_of_mem hyA, Set.indicator_of_mem hyA, hy]
    · rw [Set.indicator_of_notMem hyA, Set.indicator_of_notMem hyA]
  have hpt : ∀ᵐ y ∂closedLaw b W np,
      ‖(b3Alive b E s h τ m R W (closeLen s W) (Vs W)).indicator
        (fun y => jet1Shift b E (b3ClosedX b E s h τ m W (closeLen s W) y) (closeLen s W) y) y‖ ≤
      ‖ρ⁻¹ * ∫ θ, ‖stieltjes (b3ClosedX b E s h τ m W (closeLen s W) y)
          (circleMap (boundaryZ b E) ρ θ) -
        stieltjes (pathX b E W (closeLen s W) y.1.1) (circleMap (boundaryZ b E) ρ θ)‖
          ∂phaseLaw‖ := by
    filter_upwards [hpc, hpo] with y h1 h2
    have hk := norm_jet1D_sub_le hb1 hE1 hE2 h1 h2 hρ0 hρz
    have hI0 : 0 ≤ ρ⁻¹ * ∫ θ, ‖stieltjes (b3ClosedX b E s h τ m W (closeLen s W) y)
          (circleMap (boundaryZ b E) ρ θ) -
        stieltjes (pathX b E W (closeLen s W) y.1.1) (circleMap (boundaryZ b E) ρ θ)‖
          ∂phaseLaw :=
      mul_nonneg hρi (integral_nonneg fun θ => norm_nonneg _)
    rw [Real.norm_of_nonneg hI0]
    by_cases hyA : y ∈ b3Alive b E s h τ m R W (closeLen s W) (Vs W)
    · have hj0 : 0 ≤ jet1Shift b E (b3ClosedX b E s h τ m W (closeLen s W) y) (closeLen s W) y :=
        norm_nonneg _
      rw [Set.indicator_of_mem hyA, Real.norm_of_nonneg hj0]
      exact hk
    · rw [Set.indicator_of_notMem hyA, norm_zero]
      exact hI0
  refine (eLpNorm_mono_ae hm hpt).trans ?_
  have hsm := eLpNorm_const_smul ρ⁻¹ (fun y : ProbedPath W np × ℝ => ∫ θ,
      ‖stieltjes (b3ClosedX b E s h τ m W (closeLen s W) y) (circleMap (boundaryZ b E) ρ θ) -
        stieltjes (pathX b E W (closeLen s W) y.1.1) (circleMap (boundaryZ b E) ρ θ)‖
          ∂phaseLaw) (ENNReal.ofReal p) (closedLaw b W np)
  rw [Real.enorm_of_nonneg hρi] at hsm
  refine (le_of_eq hsm).trans ?_
  calc ENNReal.ofReal ρ⁻¹ * eLpNorm (fun y : ProbedPath W np × ℝ => ∫ θ,
      ‖stieltjes (b3ClosedX b E s h τ m W (closeLen s W) y) (circleMap (boundaryZ b E) ρ θ) -
        stieltjes (pathX b E W (closeLen s W) y.1.1) (circleMap (boundaryZ b E) ρ θ)‖
          ∂phaseLaw) (ENNReal.ofReal p) (closedLaw b W np)
      ≤ ENNReal.ofReal ρ⁻¹ * ENNReal.ofReal (max C 0 / W) := by gcongr
    _ = ENNReal.ofReal (ρ⁻¹ * max C 0 / W) := by
        rw [← ENNReal.ofReal_mul hρi, mul_div_assoc]

/-- **`ClosedJet1StartLe P` from the open jet and the closing shift at the same orders**
(adapted from `closedJet1Start_of_shift`). -/
theorem closedJet1StartLe_of_shift {P : ℝ} (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ᶠ W in atTop,
        ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          ∀ᵐ y ∂closedLaw b W np, (passiveY (b3ClosedX b E s h τ m W j y)).PosSemidef)
    (hSh : ClosedJet1ShiftLpLe P) : ClosedJet1StartLe P := by
  intro b E np τ m T s h K Vs hFD R p hp hpP
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, hs, -, -, -, -⟩ := id hFD
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval (min (2 + E) (2 - E)) :=
    ⟨by have := min_le_left (2 + E) (2 - E); linarith,
      by have := min_le_right (2 + E) (2 - E); linarith⟩
  have hjs := b3Jet_spec hb0 hb hE1 hE2
  obtain ⟨Co, hCo⟩ := lengthUniform_jet_holds hMT hGA hLp b hb0 hb _ (s / 2) p hκ
    (by positivity) hp
  obtain ⟨W₀, hW₀⟩ := hCo s
  obtain ⟨Cs, hCs, hevs⟩ := hSh b E np τ m T s h K Vs hFD R p hp hpP
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  refine ⟨Cs + max Co 0, by positivity, ?_⟩
  filter_upwards [hevs, hP b E np τ m T s h K Vs hFD, hFD.2.2.2.2.2,
    eventually_ge_atTop (max W₀ (max 1 ⌈2 / s⌉₊))] with W hWs hWP hVW hWb hlt
  have hWs := hWs hlt
  have hV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hfm : AEStronglyMeasurable ((b3Alive b E s h τ m R W (closeLen s W) (Vs W)).indicator
      fun y => jetDistance1 b E (b3Jet b E) (b3ClosedX b E s h τ m W (closeLen s W) y))
      (closedLaw b W np) :=
    (((measurable_jet1V b E (b3Jet b E)).comp (measurable_b3ClosedX b E s h τ m
      (closeLen s W))).aestronglyMeasurable.indicator₀ (nullMeasurableSet_b3Alive
        (by linarith) hE1 hE2 s h τ m R W (closeLen s W) hV)).congr
      (indicator_jetDistance1_ae_eq (by linarith) hE1 hE2 _ _ _
        (hWP _ (Finset.mem_Ico.2 ⟨le_rfl, hlt⟩))).symm
  simp only [max_le_iff] at hWb
  obtain ⟨hW0, hW1, hW2⟩ := hWb
  have hx0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  set r := closeLen s W with hr
  have hWs2 : 2 ≤ (W : ℝ) * s := by
    have h1 := (Nat.le_ceil (2 / s)).trans (by exact_mod_cast hW2 : (⌈2 / s⌉₊ : ℝ) ≤ W)
    rw [div_le_iff₀ hs] at h1
    linarith
  have hrlo : s / 2 * W ≤ r := by
    have := Nat.lt_floor_add_one ((W : ℝ) * s)
    rw [hr]
    nlinarith
  have hrhi : (r : ℝ) ≤ s * W := by
    rw [hr, mul_comm]; exact Nat.floor_le (by positivity)
  have hopen := hW₀ W hW0 E hEb (b3Jet b E) hjs r hrlo hrhi
  have hopen1 : eLpNorm (fun ω => jetDistance1 b E (b3Jet b E) (pathX b E W r ω))
      (ENNReal.ofReal p) (growthPathLaw W b) ≤ ENNReal.ofReal (max Co 0 / W) :=
    (le_add_self.trans hopen).trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) hx0.le))
  -- the open jet under the closed law
  have hae : (fun ω => jetDistance1 b E (b3Jet b E) (pathX b E W r ω)) =ᵐ[growthPathLaw W b]
      pathJetV b E (b3Jet b E) W r := pathJet1_ae_eq (by linarith) hE1 hE2 _ r
  have hgm : AEStronglyMeasurable (fun ω => jetDistance1 b E (b3Jet b E) (pathX b E W r ω))
      (growthPathLaw W b) :=
    (measurable_pathJetV b E (b3Jet b E) r).aestronglyMeasurable.congr hae.symm
  have hg : eLpNorm (fun y : ProbedPath W np × ℝ =>
      jetDistance1 b E (b3Jet b E) (pathX b E W r y.1.1)) (ENNReal.ofReal p)
      (closedLaw b W np) ≤ ENNReal.ofReal (max Co 0 / W) := by
    have hm : AEMeasurable (fun y : ProbedPath W np × ℝ => y.1.1) (closedLaw b W np) :=
      (measurable_fst.comp measurable_fst).aemeasurable
    rw [← closedLaw_map_path b W np] at hgm
    have := eLpNorm_map_measure hgm hm (p := ENNReal.ofReal p)
    rw [closedLaw_map_path b W np] at this
    rw [show (fun y : ProbedPath W np × ℝ => jetDistance1 b E (b3Jet b E) (pathX b E W r y.1.1)) =
      (fun ω => jetDistance1 b E (b3Jet b E) (pathX b E W r ω)) ∘ fun y => y.1.1 from rfl,
      ← this]
    exact hopen1
  -- the pointwise triangle inequality
  set A := b3Alive b E s h τ m R W r (Vs W)
  have hpt : ∀ y, ‖A.indicator (fun y => jetDistance1 b E (b3Jet b E)
      (b3ClosedX b E s h τ m W r y)) y‖ ≤
      ‖(A.indicator (fun y => jet1Shift b E (b3ClosedX b E s h τ m W r y) r y) +
        fun y : ProbedPath W np × ℝ => jetDistance1 b E (b3Jet b E) (pathX b E W r y.1.1)) y‖ :=
      by
    intro y
    have hn1 : 0 ≤ jetDistance1 b E (b3Jet b E) (pathX b E W r y.1.1) := norm_nonneg _
    by_cases hy : y ∈ A
    · have ha : 0 ≤ jetDistance1 b E (b3Jet b E) (b3ClosedX b E s h τ m W r y) := norm_nonneg _
      have hb' : 0 ≤ jet1Shift b E (b3ClosedX b E s h τ m W r y) r y := norm_nonneg _
      rw [Set.indicator_of_mem hy, Pi.add_apply, Set.indicator_of_mem hy,
        Real.norm_of_nonneg ha, Real.norm_of_nonneg (add_nonneg hb' hn1)]
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    · rw [Set.indicator_of_notMem hy, Pi.add_apply, Set.indicator_of_notMem hy, zero_add,
        norm_zero]
      exact norm_nonneg _
  refine (eLpNorm_mono hfm hpt).trans ((eLpNorm_add_le hp1).trans ?_)
  refine (add_le_add hWs hg).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_div]

/-- **`ClosedJet1LpLe P`** (adapted from `closedJet1Lp_of`)
from the contract hypotheses, the passivity (`hP`) and the one-port
recursion (`hRec`) of `b3ClosedX` (`ClosedInputPassive b3ClosedX` and
`ClosedInputRecursion b3ClosedX`), the closed `δ₀` at all steps and the closed `δ₁` at the
restart, all at the orders `1 ≤ p ≤ P`. -/
theorem closedJet1LpLe_of {P : ℝ} (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ᶠ W in atTop,
        ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          ∀ᵐ y ∂closedLaw b W np, (passiveY (b3ClosedX b E s h τ m W j y)).PosSemidef)
    (hRec : ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ᶠ W in atTop,
        ∀ j : ℕ, closeLen s W ≤ j → j + 1 < ⌊(W : ℝ) * T⌋₊ →
          ∀ᵐ y ∂closedLaw b W np, b3ClosedX b E s h τ m W (j + 1) y =
            freshSchur E (b3ClosedX b E s h τ m W j y) (freshSample W j y.1.1))
    (h0 : ClosedJet0LpStepsLe P) (hS : ClosedJet1StartLe P) : ClosedJet1LpLe P := by
  intro b E np τ m T s h K Vs hFD R p hp hpP
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, -, -, -, -, -⟩ := id hFD
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval (min (2 + E) (2 - E)) :=
    ⟨by have := min_le_left (2 + E) (2 - E); linarith,
      by have := min_le_right (2 + E) (2 - E); linarith⟩
  set κ := min (2 + E) (2 - E) with hκdef
  have hjs := b3Jet_spec hb0 hb hE1 hE2
  obtain ⟨d₀, ρ₁, C₂, Cm, Wm, hd₀, hρ₁0, hρ₁1, hC₂, hCm, hmean⟩ :=
    passiveJetMeanStep_holds (BlockBand.Transmission.PassiveLayer.passiveBounds_holds hGA hLp) b
      hb0 hb κ hκ
  obtain ⟨Cf, Wf, hCf, hfl⟩ := passiveJetFluctuationStep_holds hGA hLp b hb0 hb κ hκ p hp
  obtain ⟨C₀, hC₀, hev0⟩ := h0 b E np τ m T s h K Vs hFD R p hp hpP
  obtain ⟨C₁, hC₁, hev1⟩ := hS b E np τ m T s h K Vs hFD R p hp hpP
  have hM0 : 0 ≤ jetM b κ := by
    unfold jetM; have := etaLow_pos (by linarith : b < 1) hκ; positivity
  refine ⟨(C₁ + ((C₂ + jetM b κ / d₀) * C₀ + Cm + Cf) / (1 - ρ₁)), ?_, ?_⟩
  · have : 0 < 1 - ρ₁ := by linarith
    positivity
  filter_upwards [hev0, hev1, hP b E np τ m T s h K Vs hFD, hRec b E np τ m T s h K Vs hFD,
    hFD.2.2.2.2.2, eventually_ge_atTop (max (max Wm Wf) 1)] with W hW0 hW1 hWP hWR hVW hWb j hj
  simp only [max_le_iff] at hWb
  obtain ⟨⟨hWm, hWf⟩, hW1'⟩ := hWb
  obtain ⟨hjs', hjT⟩ := Finset.mem_Ico.1 (Finset.mem_filter.1 hj).1
  have hV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hXp : ∀ j', closeLen s W ≤ j' → j' ≤ j →
      ∀ᵐ y ∂closedLaw b W np, (passiveY (b3ClosedX b E s h τ m W j' y)).PosSemidef :=
    fun j' h1 h2 => hWP j' (Finset.mem_Ico.2 ⟨h1, lt_of_le_of_lt h2 hjT⟩)
  have hstart : eLpNorm ((b3Alive b E s h τ m R W (closeLen s W) (Vs W)).indicator fun y =>
      jet1V b E (b3Jet b E) (b3ClosedX b E s h τ m W (closeLen s W) y)) (ENNReal.ofReal p)
        (closedLaw b W np) ≤ ENNReal.ofReal (C₁ / W) :=
    (eLpNorm_congr_ae (indicator_jetDistance1_ae_eq (μ := closedLaw b W np) (by linarith) hE1
      hE2 (b3Jet b E) (b3ClosedX b E s h τ m W (closeLen s W))
      (b3Alive b E s h τ m R W (closeLen s W) (Vs W)) (hXp _ le_rfl hjs'))).symm.trans_le
      (hW1 (lt_of_le_of_lt hjs' hjT))
  have key := eLpNorm_closedJet1_le hb0 hb hκ hEb hjs hd₀ hρ₁0 hρ₁1 hC₂ hCm hCf hC₀ hC₁ hp hW1'
    (hmean W hWm E hEb (b3Jet b E) hjs)
    (fun X' hX' => jetFun_fluct hb0 hb hκ hfl hWf hEb X' hX')
    (fun j' => b3ClosedX b E s h τ m W j') (fun j' => b3Alive b E s h τ m R W j' (Vs W))
    (fun j' => genMem_b3Alive_succ_subset b E s h τ m R W j' (Vs W))
    (fun j' => nullMeasurableSet_b3Alive (by linarith) hE1 hE2 s h τ m R W j' hV) hjs'
    (fun j' => measurable_b3ClosedX b E s h τ m j')
    (fun j' h1 _ y => b3ClosedX_b3Ext h1 le_rfl y) hXp
    (fun j' h1 h2 => hWR j' h1 (by omega))
    (fun j' h1 h2 => hW0 j' (Finset.mem_Ico.2 ⟨h1, by omega⟩)) hstart
  exact (eLpNorm_congr_ae (indicator_jetDistance1_ae_eq (μ := closedLaw b W np) (by linarith)
    hE1 hE2 (b3Jet b E) (b3ClosedX b E s h τ m W j) (b3Alive b E s h τ m R W j (Vs W))
    (hXp _ hjs' le_rfl))).trans_le key

/-!
## Assembly
-/

/-- **`ClosedJet1LpLe P`** from the contract hypotheses, the cavity-kernel bound and the
fractional moments at every order `1 ≤ p ≤ P` (passivity and recursion of `b3ClosedX` are
proved). -/
theorem closedJet1LpLe_of_frac (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hA : Jet.ClosedShiftDiscTrace) {P : ℝ}
    (hB : ∀ p : ℝ, 1 ≤ p → p ≤ P → Jet.FarFracTraceMomentsAt p) : ClosedJet1LpLe P :=
  closedJet1LpLe_of hGA hLp Jet.closedInputPassive_b3ClosedX Jet.closedInputRecursion_b3ClosedX
    (closedJet0LpStepsLe_of_famLe (closedJet0FamLe_of_fracAt hMT hGA hLp hA hB))
    (closedJet1StartLe_of_shift hMT hGA hLp Jet.closedInputPassive_b3ClosedX
      (closedJet1ShiftLpLe_of_nbhd Jet.closedInputPassive_b3ClosedX
        (Jet.closedJetShiftNbhdLpLe_of_frac hA hB)))

/-- **`ClosedJet1LpLe 4` from `FarFracTraceMoments4`.** -/
theorem closedJet1LpLe_of_frac4 (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hA : Jet.ClosedShiftDiscTrace) (hB : FarFracTraceMoments4) :
    ClosedJet1LpLe 4 :=
  closedJet1LpLe_of_frac hMT hGA hLp hA fun _ hp hp4 => farFracTraceMomentsAt_of_four hB hp hp4

/-- **Both closed jets at the orders `1 ≤ p ≤ 4` from `FarFracTraceMoments4`.** -/
theorem closedJetsLe_of_frac4 (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hA : Jet.ClosedShiftDiscTrace) (hB : FarFracTraceMoments4) :
    ClosedJet0LpLe 4 ∧ ClosedJet1LpLe 4 :=
  ⟨closedJet0LpLe_of_frac4 hMT hGA hLp hA hB, closedJet1LpLe_of_frac4 hMT hGA hLp hA hB⟩

end BlockBand.SourceProcess.PhysApprox.B3.Jet1
