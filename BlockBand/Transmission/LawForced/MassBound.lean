module

public import BlockBand.Transmission.LawDuality.Refined
public import BlockBand.Transmission.LawDuality.TightAbsorbed
public import BlockBand.Transmission.Absorbed.Conductance
public import BlockBand.Transmission.Generator.Weak
public import BlockBand.Transmission.Generator.LimitBasic

/-!
# `SubLimitMassBound` for every profile

Every subsequential limit has locally bounded mean mass (bounded by `(x₁+y₁)E g`), for every
admissible profile `κ` (the case `κ ≡ 0` is `hasLocalMassBound_zero`).

The proof: `Absorbed.absorbedConductance_bulk` (from the contract hypotheses `hMT hGA hLp`)
gives, at `p = 2`, a bound `E (g^κ_r)² ≤ C` uniform on `(ε/2)W ≤ r ≤ TW` and over the bulk. The
mass of `μ_W(t)` is `g^κ_{⌊Wt⌋}` a.s. (`mass_transmissionProcess`), and the mass is weakly
continuous, so `tendsto_integral_of_sq_bound` (one-time fdd, `G = mass`) carries the
second-moment bound to the limit; `‖m‖ₑ ≤ 1 + ‖m‖ₑ²` gives the first moment.

* `massOne` (the mass as a one-time test), `massOne_eq_real`, `measure_univ_eq_enorm`;
* **`hasLocalMassBound_of_baseContracts`**: one subsequential limit;
* **`subLimitMassBound_holds hMT hGA hLp : SubLimitMassBound`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Absorbed
open scoped NNReal ENNReal BoundedContinuousFunction

/-- The state space of one-time tests. -/
abbrev St1 := Fin 1 → FiniteMeasure unitInterval

/-- `x ↦ mass (x 0)`. -/
def massOne (x : St1) : ℝ := ((x 0).mass : ℝ)

theorem continuous_massOne : Continuous massOne :=
  NNReal.continuous_coe.comp (FiniteMeasure.continuous_mass.comp (continuous_apply 0))

theorem massOne_eq_real (ν : FiniteMeasure unitInterval) :
    massOne (fun _ => ν) = (ν : Measure unitInterval).real univ := by
  rw [massOne, Measure.real, ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal]

theorem measure_univ_eq_enorm (ν : FiniteMeasure unitInterval) :
    (ν : Measure unitInterval) univ = ‖massOne (fun _ => ν)‖ₑ := by
  rw [massOne_eq_real, Real.enorm_eq_ofReal measureReal_nonneg, Measure.real,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **Locally bounded mean mass of one subsequential limit, every profile.** -/
theorem hasLocalMassBound_of_baseContracts (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {b E : ℝ} {κ : ℝ → ℝ}
    {φ : ℕ → ℕ} (hb : 0 < b) (hb2 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hκ : IsAbsorptionProfile κ) (hφ : Tendsto φ atTop atTop) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (h : IsTransmissionSubLimit b E κ φ P μ) : HasLocalMassBound P μ := by
  have := h.prob
  obtain ⟨hκI, hEI⟩ := mem_bulkInterval_half hE1 hE2
  obtain ⟨-, hκ0, K, hK⟩ := hκ
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have hκK : ∀ s, 0 ≤ κ s ∧ κ s ≤ max K 0 := fun s => ⟨hκ0 s, (hK s).trans (le_max_left _ _)⟩
  intro ε T hε
  obtain ⟨C, hC⟩ := absorbedConductance_bulk hMT hGA hLp b hb hb2 _ (ε / 2) 2 (max K 0) hκI
    (by positivity) (by norm_num) hK0
  obtain ⟨W₀, hW₀⟩ := hC T
  refine ⟨1 + max C 0, fun t ht => ?_⟩
  have ht0 : 0 < t := hε.trans_le ht.1
  -- measurable versions of the finite-`W` one-time states
  have hae : ∀ n, AEMeasurable (fun ω => (fun _ : Fin 1 => transmissionProcess b E κ (φ n) t ω))
      (growthPathLaw (φ n) b) := fun n =>
    AEMeasurable.of_eval fun _ =>
      aemeasurable_transmissionProcess hκ0 (by linarith) hE1 hE2 t
  set X : ∀ n, GrowthPath (φ n) → St1 := fun n => (hae n).mk _
  have hX : ∀ n, Measurable (X n) := fun n => (hae n).measurable_mk
  have hXe : ∀ n, ∀ᵐ ω ∂growthPathLaw (φ n) b,
      (fun _ : Fin 1 => transmissionProcess b E κ (φ n) t ω) = X n ω := fun n =>
    (hae n).ae_eq_mk
  have hY : Measurable fun ω => (fun _ : Fin 1 => μ t ω) :=
    measurable_pi_iff.mpr fun _ => h.measurable t ht0
  have hconv : ∀ Φ : BoundedContinuousFunction St1 ℝ,
      Tendsto (fun n => ∫ ω, Φ (X n ω) ∂growthPathLaw (φ n) b) atTop
        (𝓝 (∫ ω, Φ ((fun ω => (fun _ : Fin 1 => μ t ω)) ω) ∂P)) := by
    intro Φ
    have hf := h.fdd 1 (fun _ => t) (fun _ => ht0) Φ
    refine hf.congr fun n => integral_congr_ae ?_
    filter_upwards [hXe n] with ω hω
    rw [← hω]
  -- the finite-`W` second moments, eventually in `n`
  have hev : ∀ᶠ n in atTop, W₀ ≤ φ n ∧ 4 / ε ≤ (φ n : ℝ) := by
    have h1 := hφ.eventually_ge_atTop W₀
    have h2 := (tendsto_natCast_atTop_atTop.comp hφ).eventually_ge_atTop (4 / ε)
    filter_upwards [h1, h2] with n hn1 hn2 using ⟨hn1, hn2⟩
  have hCn : ∀ᶠ n in atTop, ∫⁻ ω, ‖massOne (X n ω)‖ₑ ^ 2 ∂growthPathLaw (φ n) b ≤
      ENNReal.ofReal C := by
    filter_upwards [hev] with n ⟨hn1, hn2⟩
    set Wn := φ n
    have hWpos : (0 : ℝ) < Wn := lt_of_lt_of_le (by positivity) hn2
    set r := ⌊(Wn : ℝ) * t⌋₊
    have hWt : 0 ≤ (Wn : ℝ) * t := by positivity
    have hr1 : (ε / 2) * Wn ≤ r := by
      have hfl := Nat.lt_floor_add_one ((Wn : ℝ) * t)
      have h4 : 4 ≤ ε * Wn := by rw [div_le_iff₀ hε] at hn2; linarith
      have : ε * Wn ≤ t * Wn := mul_le_mul_of_nonneg_right ht.1 hWpos.le
      nlinarith
    have hr2 : (r : ℝ) ≤ T * Wn := by
      have := Nat.floor_le hWt
      have : (Wn : ℝ) * t ≤ Wn * T := mul_le_mul_of_nonneg_left ht.2 hWpos.le
      nlinarith
    have hb' := hW₀ Wn hn1 E hEI κ hκK r hr1 hr2
    refine le_trans (le_of_eq ?_) hb'
    have hm := mass_transmissionProcess (W := Wn) hκ0 (by linarith : b < 1) hE1 hE2
    refine lintegral_congr_ae ?_
    filter_upwards [hXe n, hm] with ω hω hmω
    rw [← hω, massOne_eq_real, hmω t, ENNReal.rpow_two]
    rfl
  have hlim := (Generator.tendsto_integral_of_sq_bound (μ := fun n => growthPathLaw (φ n) b)
    hX hY hconv continuous_massOne hCn).1
  calc ∫⁻ ω, (μ t ω : Measure unitInterval) univ ∂P
      = ∫⁻ ω, ‖massOne ((fun ω => (fun _ : Fin 1 => μ t ω)) ω)‖ₑ ∂P :=
        lintegral_congr fun ω => measure_univ_eq_enorm (μ t ω)
    _ ≤ ∫⁻ ω, (1 + ‖massOne ((fun ω => (fun _ : Fin 1 => μ t ω)) ω)‖ₑ ^ 2) ∂P :=
        lintegral_mono fun ω => Generator.enorm_le_one_add_sq _
    _ = 1 + ∫⁻ ω, ‖massOne ((fun ω => (fun _ : Fin 1 => μ t ω)) ω)‖ₑ ^ 2 ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ 1 + ENNReal.ofReal C := add_le_add le_rfl hlim
    _ = ENNReal.ofReal (1 + max C 0) := by
        rw [ENNReal.ofReal_add zero_le_one (le_max_right _ _), ENNReal.ofReal_one,
          Generator.ofReal_max_zero]

/-- **`SubLimitMassBound`, every profile**: every subsequential limit has locally bounded mean mass. -/
theorem subLimitMassBound_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) : SubLimitMassBound :=
  fun _ hb hb2 _ hE1 hE2 _ hκ _ hφ _ _ _ _ h =>
    hasLocalMassBound_of_baseContracts hMT hGA hLp hb hb2 hE1 hE2 hκ hφ h

end BlockBand.Transmission.LawForced
