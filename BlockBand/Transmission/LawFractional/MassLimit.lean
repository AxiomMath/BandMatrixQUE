module

public import BlockBand.Transmission.LawFractional.Interp
public import BlockBand.Transmission.LawDuality.BorelGiry
public import BlockBand.Transmission.LawDuality.PowerLimit
public import BlockBand.Transmission.LawDuality.TightAbsorbed
public import BlockBand.Transmission.Generator.Weak
public import BlockBand.Transmission.LengthUniform.ConductanceUniform

/-!
# Finite-`W` mean conductance converges to the limit mass (one time)

Unabsorbed path `growthPathLaw W b`, energies `e W` (eventually in a fixed `bulkInterval κ`;
`e ≡ E` is the fixed-energy case).

**`mass_tendsto hMT hGA hLp`**: assume the one-time laws of `μ_W(t)` at energy `e W` converge
weakly to the law of `Y` (the one-time `fdd` clause of `IsTransmissionLimit` or
`IsTransmissionLimitAlong`). Then `E g_{⌊Wt⌋} → E Y[0,1]`.

Proof. Use `Generator.tendsto_integral_of_sq_bound` with `G = massFn` (`ν ↦ ∫ s⁰ dν`).
It needs a uniform `L²` bound. That bound is `E g_r² ≤ C` on `r ≥ (t/2)W`, from
`TransmissionLengthUniformContract.conductance` (`LengthUniform.lengthUniform_conductance_holds`).
The identity `massFn μ_W(t) = g_{⌊Wt⌋}` holds a.s. (`ae_integral_pow_transmissionProcess`,
`j = 0`). The `W`-indexed processes are replaced by measurable versions
(`aemeasurable_transmissionProcess`), and the index is shifted past the bulk threshold.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFractional

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open scoped ENNReal

/-- The mass `ν ↦ ∫ s⁰ dν`. -/
def massFn (ν : FiniteMeasure unitInterval) : ℝ := ∫ s, (s : ℝ) ^ 0 ∂(ν : Measure unitInterval)

theorem continuous_massFn : Continuous massFn :=
  FiniteMeasure.continuous_integral_boundedContinuousFunction (LawDuality.powBCF 0)

theorem measurable_massFn : Measurable massFn :=
  LawDuality.measurable_integral_continuous (LawDuality.powBCF 0).toContinuousMap

theorem massFn_nonneg (ν : FiniteMeasure unitInterval) : 0 ≤ massFn ν :=
  integral_nonneg fun s => pow_nonneg s.2.1 0

/-- a.s. `massFn μ_W(t) = g_{⌊Wt⌋}`. -/
theorem ae_massFn_eq {W : ℕ} {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) (t : ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, massFn (transmissionProcess b E (fun _ => 0) W t ω) =
      pathConductance b E W ⌊(W : ℝ) * t⌋₊ ω := by
  filter_upwards [LawDuality.ae_integral_pow_transmissionProcess (W := W) (κ := fun _ => 0)
    (fun _ => le_rfl) hb h1 h2] with ω hω
  rw [massFn, hω 0 t, zero_add, pow_one]
  rfl

/-- **Mean conductance converges to the limit mass.** -/
theorem mass_tendsto (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    {e : ℕ → ℝ} {W₁ : ℕ} (he : ∀ W, W₁ ≤ W → e W ∈ bulkInterval κ) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → FiniteMeasure unitInterval} (hY : Measurable Y) {t : ℝ} (ht : 0 < t)
    (hconv : ∀ Φ : BoundedContinuousFunction (Fin 1 → FiniteMeasure unitInterval) ℝ,
      Tendsto (fun W : ℕ => ∫ ω, Φ (fun _ => transmissionProcess b (e W) (fun _ => 0) W t ω)
        ∂growthPathLaw W b) atTop (𝓝 (∫ ω, Φ (fun _ => Y ω) ∂P))) :
    Tendsto (fun W : ℕ => ∫ ω, pathConductance b (e W) W ⌊(W : ℝ) * t⌋₊ ω ∂growthPathLaw W b)
      atTop (𝓝 (∫ ω, massFn (Y ω) ∂P)) := by
  rw [← Filter.tendsto_add_atTop_iff_nat W₁]
  have hE : ∀ n : ℕ, -2 < e (n + W₁) ∧ e (n + W₁) < 2 := fun n => by
    have h := he (n + W₁) (Nat.le_add_left _ _)
    exact ⟨by have := h.1; linarith, by have := h.2; linarith⟩
  have hae : ∀ n : ℕ, AEMeasurable (transmissionProcess b (e (n + W₁)) (fun _ => 0) (n + W₁) t)
      (growthPathLaw (n + W₁) b) := fun n =>
    LawDuality.aemeasurable_transmissionProcess (fun _ => le_rfl) (by linarith) (hE n).1
      (hE n).2 t
  set X : ∀ n : ℕ, GrowthPath (n + W₁) → FiniteMeasure unitInterval := fun n => (hae n).mk
  have hXm : ∀ n, Measurable (X n) := fun n => (hae n).measurable_mk
  have hXe : ∀ n, transmissionProcess b (e (n + W₁)) (fun _ => 0) (n + W₁) t =ᵐ[growthPathLaw (n + W₁) b]
      X n := fun n => (hae n).ae_eq_mk
  -- weak convergence of the one-time laws, for the versions
  have hconv' : ∀ Φ : BoundedContinuousFunction (FiniteMeasure unitInterval) ℝ,
      Tendsto (fun n => ∫ ω, Φ (X n ω) ∂growthPathLaw (n + W₁) b) atTop
        (𝓝 (∫ ω, Φ (Y ω) ∂P)) := by
    intro Φ
    have h := (hconv (Φ.compContinuous ⟨fun ν => ν 0, continuous_apply 0⟩)).comp
      (tendsto_add_atTop_nat W₁)
    refine h.congr fun n => integral_congr_ae ?_
    filter_upwards [hXe n] with ω hω
    simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
    rw [hω]
  -- the identity with the conductance
  have hid : ∀ n, (fun ω => massFn (X n ω)) =ᵐ[growthPathLaw (n + W₁) b]
      fun ω => pathConductance b (e (n + W₁)) (n + W₁) ⌊((n + W₁ : ℕ) : ℝ) * t⌋₊ ω := fun n => by
    filter_upwards [hXe n, ae_massFn_eq (W := n + W₁) (b := b) (by linarith) (hE n).1 (hE n).2 t]
      with ω hω h'
    rw [← hω, h']
  -- the uniform `L²` bound
  obtain ⟨Cg, hCg⟩ := LengthUniform.lengthUniform_conductance_holds hMT hGA hLp b hb0 hb κ
    (t / 2) 2 hκ (by positivity) (by norm_num)
  obtain ⟨W₀, hW₀⟩ := hCg t
  have hC : ∀ᶠ n in atTop, ∫⁻ ω, ‖massFn (X n ω)‖ₑ ^ 2 ∂growthPathLaw (n + W₁) b ≤
      ENNReal.ofReal Cg := by
    filter_upwards [eventually_ge_atTop (max W₀ ⌈2 / t⌉₊)] with n hn
    simp only [max_le_iff] at hn
    set W := n + W₁
    have hWW₀ : W₀ ≤ W := le_trans hn.1 (Nat.le_add_right _ _)
    have hcW : ⌈2 / t⌉₊ ≤ W := le_trans hn.2 (Nat.le_add_right _ _)
    have hW2 : 2 / t ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hcW)
    have hWt : 2 ≤ (W : ℝ) * t := by rwa [div_le_iff₀ ht] at hW2
    have hfl : t / 2 * W ≤ (⌊(W : ℝ) * t⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one ((W : ℝ) * t); nlinarith
    have hfl' : (⌊(W : ℝ) * t⌋₊ : ℝ) ≤ t * W := by
      rw [mul_comm t]; exact Nat.floor_le (by positivity)
    have h := hW₀ W hWW₀ (e W) (he W (Nat.le_add_left _ _)) _ hfl hfl'
    refine le_trans (le_of_eq ?_) h
    refine lintegral_congr_ae ?_
    filter_upwards [hid n] with ω hω
    rw [hω, ← ENNReal.rpow_natCast, Nat.cast_ofNat]
  have hT := (Generator.tendsto_integral_of_sq_bound hXm hY hconv' continuous_massFn hC).2
  refine hT.congr fun n => integral_congr_ae (hid n)

end BlockBand.Transmission.LawFractional
