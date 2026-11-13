module

public import BlockBand.Transmission.LawDecay.MassDecay
public import BlockBand.Transmission.LawFractional.DecayMoving

/-!
# The `expDecay` fields from the transmission inputs

* **`expDecay_moving_holds hMT hGA hLp hP`**: `TransmissionLawEnergyUniformContract.expDecay`
  (moving energies, constants before `C_e, e`).
* **`expDecay_holds hMT hGA hLp hP`**: `TransmissionLawContract.expDecay` (the case `e ≡ E`).

The proof is `expDecay_moving_of` with its limit-side input replaced by the finite-`W` bound
`mass_decay`: eventually `E g_{⌊Wt⌋} ≤ (C + 1)e^{-ct}`. It also uses the interpolation
`E Tr T^q ≤ (E g)^θ(E Tr T^{q/2})^{1-θ}` (`integral_interp`) and the fractional bound
`fractional_bulk`. No limit object is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDecay

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.FractionalBulk BlockBand.Transmission.LawFractional
open scoped ENNReal

/-- **`TransmissionLawEnergyUniformContract.expDecay`, from the input hypotheses.** -/
theorem expDecay_moving_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ q : ℝ, 0 < q → q < 1 → ∃ C c : ℝ, 0 < c ∧ ∀ (Ce : ℝ) (e : ℕ → ℝ), IsMovingEnergy E Ce e →
      ∀ t : ℝ, 2 ≤ t →
        limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
            (fracTrace q (pathTransmission b (e W) (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω))
            ∂growthPathLaw W b) atTop ≤ ENNReal.ofReal (C * Real.exp (-(c * t))) := by
  intro b hb0 hb E h1 h2 q hq0 hq1
  obtain ⟨C, c, hc, hM⟩ := mass_decay hMT hGA hLp hP hb0 hb h1 h2
  set κI := min (E + 2) (2 - E)
  have hκ : 0 < κI := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval κI :=
    ⟨by have := min_le_left (E + 2) (2 - E); linarith,
      by have := min_le_right (E + 2) (2 - E); linarith⟩
  obtain ⟨Cp, hCp0, hCp⟩ := fractional_bulk hMT hGA hLp hP b hb0 hb (κI / 2) (by positivity)
    (q / 2) (by positivity) (by linarith)
  obtain ⟨hθ0, hθ1⟩ := interpExp_mem hq0 hq1
  set θ := interpExp q
  set C' := max C 0 + 1
  have hC' : 0 < C' := by positivity
  refine ⟨C' ^ θ * (3 * (Cp + 1)) ^ (1 - θ), c * θ, by positivity, fun Ce e he t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  set A := C' * Real.exp (-(c * t))
  set B := (Cp + 1) * (1 + t⁻¹)
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  have hev1 : ∀ᶠ W : ℕ in atTop,
      ∫ ω, pathConductance b (e W) W ⌊(W : ℝ) * t⌋₊ ω ∂growthPathLaw W b ≤ A := by
    filter_upwards [hM Ce e he t ht (Real.exp (-(c * t))) (Real.exp_pos _)] with W hW
    refine hW.trans ?_
    have : C * Real.exp (-(c * t)) ≤ max C 0 * Real.exp (-(c * t)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    simp only [A, C']; linarith
  set W₁ := EnergyUniform.windowWidth κI Ce
  have heb : ∀ W, W₁ ≤ W → e W ∈ bulkInterval (κI / 2) := fun W hW =>
    EnergyUniform.window_mem_bulkInterval hκ hW hEb
      (he W (lt_of_lt_of_le (Nat.succ_pos _) hW))
  obtain ⟨W₀, hW₀⟩ := hCp t ht0
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hev1, eventually_ge_atTop (max W₀ W₁)] with W hW1 hW2
  have hWb := heb W (le_of_max_le_right hW2)
  have h1' : -2 < e W := by have := hWb.1; linarith
  have h2' : e W < 2 := by have := hWb.2; linarith
  have hPp := hW₀ W (le_of_max_le_left hW2) (e W) hWb
  have hip := integrable_pathFrac (W := W) (p := q / 2) (by positivity) (by linarith) hb h1' h2'
    ⌊(W : ℝ) * t⌋₊
  rw [← ofReal_integral_eq_lintegral_ofReal hip
    (Eventually.of_forall fun ω => fracTrace_nonneg' _ _)] at hPp
  have hPB : ∫ ω, fracTrace (q / 2) (pathTransmission b (e W) (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω)
      ∂growthPathLaw W b ≤ B := by
    have h := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hPp
    have : Cp * (1 + t⁻¹) ≤ B := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hI := integral_interp (W := W) hb h1' h2' hq0 hq1 hA hB _ hW1 hPB
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_pathFrac (W := W) hq0 hq1 hb h1' h2' ⌊(W : ℝ) * t⌋₊)
    (Eventually.of_forall fun ω => fracTrace_nonneg' _ _)]
  refine ENNReal.ofReal_le_ofReal (hI.trans ?_)
  have hAθ : A ^ θ = C' ^ θ * Real.exp (-(c * θ * t)) := by
    rw [Real.mul_rpow hC'.le (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2; ring
  have hB3 : B ≤ 3 * (Cp + 1) := by
    have : t⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ ht0 (by norm_num)]; linarith
    have hCp1 : 0 ≤ Cp + 1 := by linarith
    simp only [B]; nlinarith
  have hBθ : B ^ (1 - θ) ≤ (3 * (Cp + 1)) ^ (1 - θ) :=
    Real.rpow_le_rpow hB.le hB3 (by linarith)
  rw [hAθ]
  have h0 : 0 ≤ C' ^ θ * Real.exp (-(c * θ * t)) := by positivity
  calc C' ^ θ * Real.exp (-(c * θ * t)) * B ^ (1 - θ) ≤
      C' ^ θ * Real.exp (-(c * θ * t)) * (3 * (Cp + 1)) ^ (1 - θ) :=
        mul_le_mul_of_nonneg_left hBθ h0
    _ = C' ^ θ * (3 * (Cp + 1)) ^ (1 - θ) * Real.exp (-(c * θ * t)) := by ring

/-- **`TransmissionLawContract.expDecay`, from the input hypotheses** (`e ≡ E`). -/
theorem expDecay_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ q : ℝ, 0 < q → q < 1 → ∃ C c : ℝ, 0 < c ∧ ∀ t : ℝ, 2 ≤ t →
      limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
          (fracTrace q (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω))
          ∂growthPathLaw W b) atTop ≤ ENNReal.ofReal (C * Real.exp (-(c * t))) := by
  intro b hb0 hb E h1 h2 q hq0 hq1
  obtain ⟨C, c, hc, h⟩ := expDecay_moving_holds hMT hGA hLp hP b hb0 hb E h1 h2 q hq0 hq1
  exact ⟨C, c, hc, h 0 (fun _ => E) (LawFractional.isMovingEnergy_const E)⟩

end BlockBand.Transmission.LawDecay
