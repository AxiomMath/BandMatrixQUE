module

public import BlockBand.Transmission.Absorbed.Conductance
public import BlockBand.Transmission.LawDuality.TightAbsorbed

/-!
# The one-time clause of `AbsorbedPowerTight`

Part (a) of `LawDuality.AbsorbedPowerTight`, the tightness of the absorbed path.

`PowerTightAt b E κ` is a conjunction under `∀ k ε T` of a one-time clause and a modulus
clause. It is split here exactly (`powerTightAt_iff`) into
* `OneTimeTightAt b E κ`: one-time tightness of `Re Tr (T^κ_{⌊Wε⌋})^k`;
* `PowerModulusAt b E κ`: the `[ε,T]` sup-modulus (part (b), not addressed here; see
  `absorbedPowerModulus_holds`).

**`oneTimeTightAt_holds`**: `OneTimeTightAt b E κ` for every admissible profile `κ` (including
`κ ≡ 0`), `0 < b < 1/2`, `-2 < E < 2`, from the contract hypotheses `MatchedTracesContract`,
`GaussianAbsorptionContract` and `GaussianLpGradient`. Proof: `0 ⪯ T^κ ⪯ I` a.s. gives
`|Re Tr (T^κ)^k| ≤ g^κ` (`Generator.trace_pow_mem`); at `r = ⌊Wε⌋ ∈ [εW/2, εW]` (`W ≥ 2/ε`),
`absorbedConductance_bulk` at `p = 1` gives `E g^κ_r ≤ C`; Markov with `M = C₊/θ + 1`.

**`absorbedPowerTight_of_modulus`**: `AbsorbedPowerModulus → AbsorbedPowerTight` (from the same
hypotheses), i.e. `AbsorbedPowerTight` is reduced to its part (b).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.LawDuality
open scoped NNReal ENNReal ComplexOrder

/-- **The one-time clause of `PowerTightAt b E κ`** (its first conjunct). -/
def OneTimeTightAt (b E : ℝ) (κ : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ ε T : ℝ, 0 < ε → ε < T →
    ∀ θ : ℝ, 0 < θ → ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      growthPathLaw W b {ω | M < |absorbedPowerTrace b E κ W k ε ω|} ≤ ENNReal.ofReal θ

/-- **The modulus clause of `PowerTightAt b E κ`** (its second conjunct). -/
def PowerModulusAt (b E : ℝ) (κ : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ ε T : ℝ, 0 < ε → ε < T →
    ∀ η θ : ℝ, 0 < η → 0 < θ → ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      growthPathLaw W b {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
        η < |absorbedPowerTrace b E κ W k t ω - absorbedPowerTrace b E κ W k t' ω|} ≤
        ENNReal.ofReal θ

/-- `PowerTightAt` is exactly the conjunction of its two clauses. -/
theorem powerTightAt_iff {b E : ℝ} {κ : ℝ → ℝ} :
    PowerTightAt b E κ ↔ OneTimeTightAt b E κ ∧ PowerModulusAt b E κ :=
  ⟨fun h => ⟨fun k hk ε T hε hT => (h k hk ε T hε hT).1,
      fun k hk ε T hε hT => (h k hk ε T hε hT).2⟩,
    fun h k hk ε T hε hT => ⟨h.1 k hk ε T hε hT, h.2 k hk ε T hε hT⟩⟩

/-- **Part (b) of `AbsorbedPowerTight`**: the modulus clause for every admissible
`κ ≠ 0`. -/
def AbsorbedPowerModulus : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    κ ≠ (fun _ => 0) → PowerModulusAt b E κ

variable {W : ℕ}

/-- `|Re Tr (T^κ_r)^k| ≤ g^κ_r` almost surely, `k ≥ 1`. -/
theorem ae_abs_powerTrace_le {b E : ℝ} {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) (hb : b < 1)
    (h1 : -2 < E) (h2 : E < 2) {k : ℕ} (hk : 1 ≤ k) (t : ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, |absorbedPowerTrace b E κ W k t ω| ≤
      absorbedConductance b E κ W ⌊(W : ℝ) * t⌋₊ ω := by
  filter_upwards [Bridge.ae_passiveSample W hκ hb h1 h2] with ω hω
  obtain ⟨ha, hb'⟩ := Generator.trace_pow_mem (Bridge.pathTransmission_posSemidef hω _)
    (Bridge.one_sub_pathTransmission_posSemidef b E κ W _ ω) k hk
  rw [absorbedPowerTrace, abs_of_nonneg ha]
  exact hb'

/-- **The one-time clause for every admissible profile** (part (a) of `AbsorbedPowerTight`,
and also `κ ≡ 0`). -/
theorem oneTimeTightAt_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {E : ℝ} (h1 : -2 < E)
    (h2 : E < 2) {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) : OneTimeTightAt b E κ := by
  intro k hk ε T hε _ θ hθ
  obtain ⟨K, hK⟩ := hκ.2.2
  have hκK : ∀ s, 0 ≤ κ s ∧ κ s ≤ max K 0 := fun s => ⟨hκ.2.1 s, (hK s).trans (le_max_left _ _)⟩
  have hκI : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hE := PassiveLayer.mem_bulkInterval_min E
  obtain ⟨C, hC⟩ := absorbedConductance_bulk hMT hGA hLp b hb0 hb _ (ε / 2) 1 (max K 0) hκI
    (by positivity) le_rfl (le_max_right _ _)
  obtain ⟨W₀, hW₀⟩ := hC ε
  set M := max C 0 / θ + 1 with hM
  have hM0 : 0 < M := by positivity
  refine ⟨M, max W₀ ⌈2 / ε⌉₊, fun W hW => ?_⟩
  have hWa : W₀ ≤ W := le_of_max_le_left hW
  have hWε : 2 / ε ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hW)
  have hWε' : 2 ≤ (W : ℝ) * ε := by rwa [div_le_iff₀ hε] at hWε
  set r := ⌊(W : ℝ) * ε⌋₊
  have hr1 : (W : ℝ) * ε - 1 < r := Nat.sub_one_lt_floor _
  have hr2 : (r : ℝ) ≤ W * ε := Nat.floor_le (by positivity)
  have hεr : ε / 2 * W ≤ r := by linarith
  have hrT : (r : ℝ) ≤ ε * W := by linarith
  have hmom := hW₀ W hWa E hE κ hκK r hεr hrT
  set g := absorbedConductance b E κ W r
  have hg : Measurable g := measurable_absorbedConductance b E κ r
  have hsub : {ω | M < |absorbedPowerTrace b E κ W k ε ω|} ≤ᵐ[growthPathLaw W b]
      {ω | ENNReal.ofReal M ≤ ‖g ω‖ₑ} := by
    filter_upwards [ae_abs_powerTrace_le (W := W) hκ.2.1 (by linarith) h1 h2 hk ε] with ω hω hlt
    change M < |absorbedPowerTrace b E κ W k ε ω| at hlt
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hlt.le.trans (hω.trans (le_abs_self _)))
  have hmark := meas_ge_le_lintegral_div (μ := growthPathLaw W b)
    hg.enorm.aemeasurable (ε := ENNReal.ofReal M) (by simpa using hM0) ENNReal.ofReal_ne_top
  have hint : ∫⁻ ω, ‖g ω‖ₑ ∂growthPathLaw W b ≤ ENNReal.ofReal (max C 0) := by
    have := hmom
    simp only [ENNReal.rpow_one] at this
    exact this.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  calc growthPathLaw W b {ω | M < |absorbedPowerTrace b E κ W k ε ω|}
      ≤ growthPathLaw W b {ω | ENNReal.ofReal M ≤ ‖g ω‖ₑ} := measure_mono_ae hsub
    _ ≤ (∫⁻ ω, ‖g ω‖ₑ ∂growthPathLaw W b) / ENNReal.ofReal M := hmark
    _ ≤ ENNReal.ofReal (max C 0) / ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal (max C 0 / M) := (ENNReal.ofReal_div_of_pos hM0).symm
    _ ≤ ENNReal.ofReal θ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hM0, hM, mul_add, mul_one, mul_div_cancel₀ _ hθ.ne']
        linarith

/-- **`AbsorbedPowerTight` from its part (b)**: with the one-time clause proved
(`oneTimeTightAt_holds`), `AbsorbedPowerTight` reduces to the absorbed sup-modulus. -/
theorem absorbedPowerTight_of_modulus (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hMod : AbsorbedPowerModulus) : AbsorbedPowerTight :=
  fun b hb hb2 E hE1 hE2 κ hκ h0 => powerTightAt_iff.2
    ⟨oneTimeTightAt_holds hMT hGA hLp hb hb2 hE1 hE2 hκ, hMod b hb hb2 E hE1 hE2 κ hκ h0⟩

end BlockBand.Transmission.Absorbed
