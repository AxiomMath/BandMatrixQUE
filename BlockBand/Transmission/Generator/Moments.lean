module

public import BlockBand.Transmission.Generator.Basic
public import BlockBand.Transmission.EnergyUniform.Window
public import BlockBand.Transmission.LengthUniform.ConductanceUniform
public import BlockBand.Transmission.SourceMixing.Holds

/-!
# Power-sum moments along a moving energy; `conductanceMoments` and one-time tightness

* `pathPower_moment_along`: from `TransmissionLengthUniformContract.conductance` (bulk-uniform,
  `C = C_{p,ε}` before `T`), along `e W → E`: for `W ≥ W₀(T)`, `t ∈ [ε, T]`, `k ≥ 1`,
  `E|Tr T^k_{⌊Wt⌋}|^p ≤ C` (via `0 ≤ P_k ≤ g`).
* `conductanceMoments_holds`: the field `conductanceMoments` is
  `PassiveSourceMixingContract.finiteConductance`.
* `tightOne_along`: the one-time clause of `tight` along `e` (Markov).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal

/-- The field `conductanceMoments` (`ConductanceMomentBound`), at finite `W`, from
`SourceMixing.passiveSourceMixing_holds`. -/
theorem conductanceMoments_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) : ConductanceMomentBound :=
  (SourceMixing.passiveSourceMixing_holds hMT hGA hLp).finiteConductance

/-- The bulk margin of a fixed bulk energy. -/
theorem mem_bulk_min {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    0 < min (2 + E) (2 - E) ∧ E ∈ bulkInterval (min (2 + E) (2 - E)) := by
  refine ⟨lt_min (by linarith) (by linarith), ?_, ?_⟩
  · have := min_le_left (2 + E) (2 - E); linarith
  · have := min_le_right (2 + E) (2 - E); linarith

/-- Along a moving energy, `e W` is a bulk energy for `W ≥ windowWidth`. -/
theorem along_mem_bulk {E Ce : ℝ} {e : ℕ → ℝ} (hE1 : -2 < E) (hE2 : E < 2)
    (he : IsMovingEnergy E Ce e) {W : ℕ}
    (hW : EnergyUniform.windowWidth (min (2 + E) (2 - E)) Ce ≤ W) :
    e W ∈ bulkInterval (min (2 + E) (2 - E) / 2) := by
  obtain ⟨hκ, hEκ⟩ := mem_bulk_min hE1 hE2
  have hW0 : 0 < W := lt_of_lt_of_le (Nat.succ_pos _) hW
  exact EnergyUniform.window_mem_bulkInterval hκ hW hEκ (he W hW0)

theorem bulk_bounds' {κ E : ℝ} (hκ : 0 < κ) (h : E ∈ bulkInterval κ) : -2 < E ∧ E < 2 :=
  ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **Moments of the power sums along a moving energy**, uniformly on `t ∈ [ε, T]`, `k ≥ 1`;
`C` before `T`. -/
theorem pathPower_moment_along (hLU : TransmissionLengthUniformContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ}
    (he : IsMovingEnergy E Ce e) {ε p : ℝ} (hε : 0 < ε) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ t : ℝ, ε ≤ t → t ≤ T →
      ∀ k : ℕ, 1 ≤ k →
        ∫⁻ ω, ‖pathPower b (e W) W k ⌊(W : ℝ) * t⌋₊ ω‖ₑ ^ p ∂growthPathLaw W b ≤
          ENNReal.ofReal C := by
  obtain ⟨hκ, -⟩ := mem_bulk_min hE1 hE2
  set κI := min (2 + E) (2 - E)
  obtain ⟨C, hC⟩ := hLU.conductance b hb0 hb (κI / 2) (ε / 2) p (by positivity) (by positivity) hp
  refine ⟨max C 0, le_max_right _ _, fun T => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hC T
  refine ⟨max W₀ (max (EnergyUniform.windowWidth κI Ce) ⌈2 / ε⌉₊), fun W hW t hεt htT k hk => ?_⟩
  have hW1 : W₀ ≤ W := le_trans (le_max_left _ _) hW
  have hW2 : EnergyUniform.windowWidth κI Ce ≤ W :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW3 : ⌈2 / ε⌉₊ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hmem := along_mem_bulk hE1 hE2 he hW2
  obtain ⟨he1, he2⟩ := bulk_bounds' (by positivity) hmem
  have hWε : 2 / ε ≤ (W : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hW3)
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have hr1 : ε / 2 * W ≤ (⌊(W : ℝ) * t⌋₊ : ℝ) := by
    have h1 := Nat.lt_floor_add_one ((W : ℝ) * t)
    have h2 : 2 ≤ ε * W := by rw [div_le_iff₀ hε] at hWε; linarith
    nlinarith
  have hr2 : (⌊(W : ℝ) * t⌋₊ : ℝ) ≤ T * W := by
    have h1 := Nat.floor_le (mul_nonneg hW0 (by linarith : (0 : ℝ) ≤ t))
    nlinarith
  have hg := hW₀ W hW1 (e W) hmem _ hr1 hr2
  refine le_trans (lintegral_mono_ae ?_) (hg.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  filter_upwards [pathPower_mem (W := W) (by linarith : b < 1) he1 he2] with ω hω
  obtain ⟨h0, h1, -⟩ := hω k ⌊(W : ℝ) * t⌋₊ hk
  refine ENNReal.rpow_le_rpow ?_ (by linarith)
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_of_nonneg h0,
    abs_of_nonneg (h0.trans h1)]
  exact ENNReal.ofReal_le_ofReal h1

/-- Markov from a first-moment bound. -/
theorem meas_lt_abs_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : Measurable X) {C θ : ℝ} (hC : 0 ≤ C) (hθ : 0 < θ)
    (h : ∫⁻ ω, ‖X ω‖ₑ ^ (1 : ℝ) ∂μ ≤ ENNReal.ofReal C) :
    μ {ω | C / θ + 1 < |X ω|} ≤ ENNReal.ofReal θ := by
  have hM : 0 < C / θ + 1 := by positivity
  simp only [ENNReal.rpow_one] at h
  have hsub : {ω | C / θ + 1 < |X ω|} ⊆ {ω | ENNReal.ofReal (C / θ + 1) ≤ ‖X ω‖ₑ} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Real.enorm_eq_ofReal_abs] at hω ⊢
    exact ENNReal.ofReal_le_ofReal hω.le
  refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div hX.enorm.aemeasurable
    (by simpa using hM) ENNReal.ofReal_ne_top).trans ?_)
  refine (ENNReal.div_le_div_right h _).trans ?_
  rw [← ENNReal.ofReal_div_of_pos hM]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ hM]
  have : C = θ * (C / θ) := by field_simp
  nlinarith

/-- **The one-time clause of `tight`, along a moving energy.** -/
theorem tightOne_along (hLU : TransmissionLengthUniformContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ}
    (he : IsMovingEnergy E Ce e) {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ θ : ℝ, 0 < θ → ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      growthPathLaw W b {ω | M < |pathPower b (e W) W k ⌊(W : ℝ) * ε⌋₊ ω|} ≤
        ENNReal.ofReal θ := by
  intro θ hθ
  obtain ⟨C, hC0, hC⟩ := pathPower_moment_along hLU hb0 hb hE1 hE2 he hε le_rfl
  obtain ⟨W₀, hW₀⟩ := hC ε
  exact ⟨C / θ + 1, W₀, fun W hW =>
    meas_lt_abs_le (measurable_pathPower _ _ _ _) hC0 hθ (hW₀ W hW ε le_rfl le_rfl k hk)⟩

end BlockBand.Transmission.Generator
