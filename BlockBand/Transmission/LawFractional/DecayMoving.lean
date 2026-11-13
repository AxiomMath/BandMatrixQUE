module

public import BlockBand.Transmission.LawFractional.Decay

/-!
# `expDecay` along moving energies (`TransmissionLawEnergyUniformContract.expDecay`)

* `HomogeneousLimitAlongExists`: the `κ ≡ 0` case of the energy-uniform `law` field. It asks for
  one `(P, μ)` that is the limit along every moving energy `|e_W - E| ≤ C_e W⁻²`
  (`homogeneousLimitAlongExists_of_law`).
* **`expDecay_moving_of hMT hGA hLp hP hEx hDec`**: the energy-uniform `expDecay` field. The
  proof is that of `expDecay_of`, with two changes: `fractional_bulk` is used at the halved
  margin, and `mass_tendsto` is used along `e` from `W ≥ windowWidth` on
  (`EnergyUniform.window_mem_bulkInterval`). The constants come before `C_e` and `e`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFractional

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.FractionalBulk
open scoped ENNReal

/-- **One homogeneous limit along every moving energy** (the `κ ≡ 0` case of the energy-uniform
`law` field). -/
def HomogeneousLimitAlongExists : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval),
      ∀ (Ce : ℝ) (e : ℕ → ℝ), IsMovingEnergy E Ce e → IsTransmissionLimitAlong b e (fun _ => 0) P μ

theorem isMovingEnergy_const (E : ℝ) : IsMovingEnergy E 0 (fun _ => E) := fun W _ => by
  simp [IsNearEnergy]

theorem isTransmissionLimit_of_along {b E : ℝ} {κ : ℝ → ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (h : ∀ (Ce : ℝ) (e : ℕ → ℝ), IsMovingEnergy E Ce e → IsTransmissionLimitAlong b e κ P μ) :
    IsTransmissionLimit b E κ P μ :=
  have h0 := h 0 (fun _ => E) (isMovingEnergy_const E)
  ⟨h0.prob, h0.measurable, h0.continuous, h0.fdd, h0.modulus⟩

/-- The energy-uniform `law` field type gives `HomogeneousLimitAlongExists`. -/
theorem homogeneousLimitAlongExists_of_law
    (hL : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
      ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
          (μ : ℝ → Ω → FiniteMeasure unitInterval),
          (∀ (Ce : ℝ) (e : ℕ → ℝ), IsMovingEnergy E Ce e → IsTransmissionLimitAlong b e κ P μ) ∧
          ∀ t : ℝ, 0 < t → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
            HasDualDeletionProcess (transportD0 b E) x y ∧
            DualLawValue E κ t (transportD0 b E) x y (∫ ω, transmissionRatio x y (μ t ω) ∂P)) :
    HomogeneousLimitAlongExists := fun b hb0 hb E h1 h2 => by
  obtain ⟨Ω, m, P, μ, h, -⟩ := hL b hb0 hb E h1 h2 _ isAbsorptionProfile_zero
  exact ⟨Ω, m, P, μ, h⟩

/-- **The field `TransmissionLawEnergyUniformContract.expDecay`** (moving energies). -/
theorem expDecay_moving_of (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hEx : HomogeneousLimitAlongExists)
    (hDec : LimitMassDecay) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ q : ℝ, 0 < q → q < 1 → ∃ C c : ℝ, 0 < c ∧ ∀ (Ce : ℝ) (e : ℕ → ℝ), IsMovingEnergy E Ce e →
      ∀ t : ℝ, 2 ≤ t →
        limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
            (fracTrace q (pathTransmission b (e W) (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω))
            ∂growthPathLaw W b) atTop ≤ ENNReal.ofReal (C * Real.exp (-(c * t))) := by
  intro b hb0 hb E h1 h2 q hq0 hq1
  obtain ⟨Ω, mΩ, P, μ, hμA⟩ := hEx b hb0 hb E h1 h2
  have hμ := isTransmissionLimit_of_along hμA
  obtain ⟨C, c, hc, hC⟩ := hDec b hb0 hb E h1 h2 Ω mΩ P μ hμ
  have hprob := hμ.prob
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
  have hlimb : ∫ ω, massFn (μ t ω) ∂P < A := by
    have h := limit_mass_le (hμ.measurable t ht0) (hC t ht)
    have hmax : max (C * Real.exp (-(c * t))) 0 ≤ max C 0 * Real.exp (-(c * t)) :=
      max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
        (by positivity)
    have : max C 0 * Real.exp (-(c * t)) < A := by
      simp only [A, C']
      nlinarith [Real.exp_pos (-(c * t))]
    linarith
  set W₁ := EnergyUniform.windowWidth κI Ce
  have heb : ∀ W, W₁ ≤ W → e W ∈ bulkInterval (κI / 2) := fun W hW =>
    EnergyUniform.window_mem_bulkInterval hκ hW hEb
      (he W (lt_of_lt_of_le (Nat.succ_pos _) hW))
  have hT := mass_tendsto hMT hGA hLp hb0 hb (by positivity : 0 < κI / 2) heb
    (hμ.measurable t ht0) ht0 (fun Φ => (hμA Ce e he).fdd 1 (fun _ => t) (fun _ => ht0) Φ)
  have hev1 := hT.eventually (eventually_le_nhds hlimb)
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

end BlockBand.Transmission.LawFractional
