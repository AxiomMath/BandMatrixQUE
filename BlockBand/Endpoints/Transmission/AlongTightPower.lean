module

public import BlockBand.Endpoints.Transmission.AlongTightLayer

/-!
# Absorbed power-sum tightness along moving energies

Part of the transmission law theorem (tightness along the absorbed path), along moving
energies.

* `PowerTightAlong b e κ`: `LawDuality.PowerTightAt b E κ` with the width-`W` absorbed path at
  energy `e W`. At `e = fun _ => E` it is `PowerTightAt b E κ` (`powerTightAlong_const_iff`).
* `oneTimeTightAlong_holds`: the one-time clause (`oneTimeTightAt_holds`, with the bulk window
  `e W ∈ bulkInterval (min (2+E) (2-E) / 2)` for `W ≥ windowWidth`).
* `powerModulusAlong_absorbed_holds`: the `[ε,T]` sup-modulus (`absorbedPowerModulus_holds`,
  with the bulk-uniform layer bounds of `AlongTightLayer`).
* **`powerTightAlong_holds hMT hGA hLp`**: `PowerTightAlong b e κ` for `0 < b < 1/2`,
  `-2 < E < 2`, every admissible `κ` (including `0`) and every moving energy `e` around `E`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Transmission

open MeasureTheory Filter Finset Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.Generator BlockBand.Transmission.Absorbed
open BlockBand.Transmission.LawDuality
open scoped ENNReal NNReal ComplexOrder

/-- **The `tight` clause along the energies `e W`**: `PowerTightAt` with the width-`W` absorbed
path at energy `e W`. -/
def PowerTightAlong (b : ℝ) (e : ℕ → ℝ) (κ : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ ε T : ℝ, 0 < ε → ε < T →
    (∀ θ : ℝ, 0 < θ → ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      growthPathLaw W b {ω | M < |absorbedPowerTrace b (e W) κ W k ε ω|} ≤ ENNReal.ofReal θ) ∧
    (∀ η θ : ℝ, 0 < η → 0 < θ → ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      growthPathLaw W b {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
        η < |absorbedPowerTrace b (e W) κ W k t ω - absorbedPowerTrace b (e W) κ W k t' ω|} ≤
        ENNReal.ofReal θ)

/-- At constant energy, `PowerTightAlong` is `PowerTightAt`. -/
theorem powerTightAlong_const_iff {b E : ℝ} {κ : ℝ → ℝ} :
    PowerTightAlong b (fun _ => E) κ ↔ PowerTightAt b E κ :=
  Iff.rfl

/-- **The one-time clause of `PowerTightAlong`**, every admissible profile. -/
theorem oneTimeTightAlong_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E)
    (hE2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e) {κ : ℝ → ℝ}
    (hκ : IsAbsorptionProfile κ) :
    ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∀ θ : ℝ, 0 < θ → ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      growthPathLaw W b {ω | M < |absorbedPowerTrace b (e W) κ W k ε ω|} ≤ ENNReal.ofReal θ := by
  intro k hk ε hε θ hθ
  obtain ⟨K, hK⟩ := hκ.2.2
  have hκK : ∀ s, 0 ≤ κ s ∧ κ s ≤ max K 0 := fun s => ⟨hκ.2.1 s, (hK s).trans (le_max_left _ _)⟩
  obtain ⟨hκ0, -⟩ := mem_bulk_min hE1 hE2
  have hκI : 0 < min (2 + E) (2 - E) / 2 := by positivity
  obtain ⟨C, hC⟩ := absorbedConductance_bulk hMT hGA hLp b hb0 hb _ (ε / 2) 1 (max K 0) hκI
    (by positivity) le_rfl (le_max_right _ _)
  obtain ⟨W₀, hW₀⟩ := hC ε
  set M := max C 0 / θ + 1 with hM
  have hM0 : 0 < M := by positivity
  refine ⟨M, max (max W₀ ⌈2 / ε⌉₊) (EnergyUniform.windowWidth (min (2 + E) (2 - E)) Ce),
    fun W hW => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWa, hWc⟩, hWw⟩ := hW
  have hmem := along_mem_bulk hE1 hE2 he hWw
  obtain ⟨h1, h2⟩ := bulk_bounds' hκI hmem
  have hWε : 2 / ε ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWc)
  have hWε' : 2 ≤ (W : ℝ) * ε := by rwa [div_le_iff₀ hε] at hWε
  set r := ⌊(W : ℝ) * ε⌋₊
  have hr1 : (W : ℝ) * ε - 1 < r := Nat.sub_one_lt_floor _
  have hr2 : (r : ℝ) ≤ W * ε := Nat.floor_le (by positivity)
  have hεr : ε / 2 * W ≤ r := by linarith
  have hrT : (r : ℝ) ≤ ε * W := by linarith
  have hmom := hW₀ W hWa (e W) hmem κ hκK r hεr hrT
  set g := absorbedConductance b (e W) κ W r
  have hg : Measurable g := measurable_absorbedConductance b (e W) κ r
  have hsub : {ω | M < |absorbedPowerTrace b (e W) κ W k ε ω|} ≤ᵐ[growthPathLaw W b]
      {ω | ENNReal.ofReal M ≤ ‖g ω‖ₑ} := by
    filter_upwards [ae_abs_powerTrace_le (W := W) hκ.2.1 (by linarith) h1 h2 hk ε] with ω hω hlt
    change M < |absorbedPowerTrace b (e W) κ W k ε ω| at hlt
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hlt.le.trans (hω.trans (le_abs_self _)))
  have hmark := meas_ge_le_lintegral_div (μ := growthPathLaw W b)
    hg.enorm.aemeasurable (ε := ENNReal.ofReal M) (by simpa using hM0) ENNReal.ofReal_ne_top
  have hint : ∫⁻ ω, ‖g ω‖ₑ ∂growthPathLaw W b ≤ ENNReal.ofReal (max C 0) := by
    have := hmom
    simp only [ENNReal.rpow_one] at this
    exact this.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  calc growthPathLaw W b {ω | M < |absorbedPowerTrace b (e W) κ W k ε ω|}
      ≤ growthPathLaw W b {ω | ENNReal.ofReal M ≤ ‖g ω‖ₑ} := measure_mono_ae hsub
    _ ≤ (∫⁻ ω, ‖g ω‖ₑ ∂growthPathLaw W b) / ENNReal.ofReal M := hmark
    _ ≤ ENNReal.ofReal (max C 0) / ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal (max C 0 / M) := (ENNReal.ofReal_div_of_pos hM0).symm
    _ ≤ ENNReal.ofReal θ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hM0, hM, mul_add, mul_one, mul_div_cancel₀ _ hθ.ne']
        linarith

/-- **The modulus clause of `PowerTightAlong`**, every admissible profile
(`absorbedPowerModulus_holds` along the energies `e W`). -/
theorem powerModulusAlong_absorbed_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ}
    (he : IsMovingEnergy E Ce e) {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) :
    ∀ k : ℕ, 1 ≤ k → ∀ ε T : ℝ, 0 < ε → ε < T →
    ∀ η θ : ℝ, 0 < η → 0 < θ → ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      growthPathLaw W b {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
        η < |absorbedPowerTrace b (e W) κ W k t ω - absorbedPowerTrace b (e W) κ W k t' ω|} ≤
        ENNReal.ofReal θ := by
  intro k hk ε T hε hεT η θ hη hθ
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨K0, hK0⟩ := hκ.2.2
  set K := max K0 0
  have hK : 0 ≤ K := le_max_right _ _
  have hκK : ∀ s, 0 ≤ κ s ∧ κ s ≤ K := fun s => ⟨hκ.2.1 s, (hK0 s).trans (le_max_left _ _)⟩
  have hT0 : 0 < T := by linarith
  obtain ⟨hκ0, -⟩ := mem_bulk_min hE1 hE2
  have hκI : 0 < min (2 + E) (2 - E) / 2 := by positivity
  obtain ⟨K4, W4, hK4, h4L⟩ := shiftFour_layer_bulk hGA hLp hb0 hb hκI hK j
  obtain ⟨Kd, Wd, hKd, hdL⟩ := shiftDrift_layer_bulk hGA hLp hb0 hb hκI hK j
  obtain ⟨M, WM, hM, hMom⟩ := absorbed_modY_moment_bulk hMT hGA hLp hb0 hb hκI hK
    (ε := ε / 2) (by positivity) (ε + T + 1)
  obtain ⟨Q, hQ, hQdef⟩ : ∃ Q : ℝ, 0 ≤ Q ∧ Q = 8 * (T + 1) * (320 * 1296 * (K4 * M) / η ^ 4 +
      9 * Kd ^ 2 * M / η ^ 2) := ⟨_, by positivity, rfl⟩
  obtain ⟨δ, hδ, hδ4, hδQ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ δ * Q ≤ θ / 2 := by
    refine ⟨min (1 / 4) (θ / (2 * (Q + 1))), lt_min (by norm_num) (by positivity),
      min_le_left _ _, ?_⟩
    have h1 : min (1 / 4) (θ / (2 * (Q + 1))) ≤ θ / (2 * (Q + 1)) := min_le_right _ _
    have h3 : θ / (2 * (Q + 1)) * Q ≤ θ / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  refine ⟨δ, hδ, max (max (max W4 Wd) (max WM ⌈2 / ε + 1 / δ⌉₊))
    (EnergyUniform.windowWidth (min (2 + E) (2 - E)) Ce), fun W hW => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW4, hWd⟩, hWM, hWc⟩, hWw⟩ := hW
  have hmem := along_mem_bulk hE1 hE2 he hWw
  obtain ⟨he1, he2⟩ := bulk_bounds' hκI hmem
  have hWr : 2 / ε + 1 / δ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWc)
  have hεd : 0 < 2 / ε := by positivity
  have hδd : 0 < 1 / δ := by positivity
  have hWpos : (0 : ℝ) < W := by linarith
  have hW1 : 1 ≤ W := by
    have : (0 : ℝ) < W := hWpos
    exact_mod_cast this
  have hWε : 2 ≤ ε * W := by
    have : 2 / ε ≤ W := by linarith
    rw [div_le_iff₀ hε] at this; linarith
  have hWδ : 1 ≤ δ * W := by
    have : 1 / δ ≤ W := by linarith
    rw [div_le_iff₀ hδ] at this; linarith
  have hrange := modulus_range hε hT0.le hδ.le hδ4 hWε hWδ
  have ha : 1 ≤ modA ε W := (hrange 0 (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))).1
  have hεj : ∀ i, 0 ≤ layerAbsorption W κ (i + 1) 0 ∧
      layerAbsorption W κ (i + 1) 0 ≤ K / (W : ℝ) ^ 2 := fun i =>
    ⟨div_nonneg (hκK _).1 (sq_nonneg _), div_le_div_of_nonneg_right (hκK _).2 (sq_nonneg _)⟩
  have H4 : ∀ u < (modNb T δ W + 1) * modL δ W, ∫ ω, modInc (absPower b (e W) κ W (j + 1))
      (modA ε W + u) ω ^ 4 ∂growthPathLaw W b ≤ K4 * M / (W : ℝ) ^ 2 := fun u hu => by
    obtain ⟨r1, r2, r3, -⟩ := hrange u hu
    obtain ⟨iY, mY⟩ := hMom W hWM (e W) hmem κ hκK _ r2 r3
    have hGm : Measurable fun X : Matrix (Fin W) (Fin W) ℂ =>
        K4 * (modY b (e W) X ^ 12 / (W : ℝ) ^ 2) :=
      (((measurable_modY b (e W)).pow_const 12).div_const _).const_mul _
    refine (integral_absInc_pow_four_le hb0 hb he1 he2 hW1 hκ.2.1 (by omega : 1 ≤ j + 1) r1 hGm
      ((iY.div_const _).const_mul _) fun X hX =>
        h4L W hW4 (e W) hmem X hX _ (hεj _).1 (hεj _).2).trans ?_
    rw [integral_const_mul, integral_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right mY (sq_nonneg _)) hK4
  have Hd : ∀ i, 1 ≤ i → ∀ᵐ ω ∂growthPathLaw W b,
      |((growthPathLaw W b)[modInc (absPower b (e W) κ W (j + 1)) i | growthFiltration W i]) ω| ≤
        Kd * (modY b (e W) (pathNearSchur b (e W) κ W i ω) ^ 3 / W) := fun i hi =>
    ae_abs_condExp_absInc_le hb0 hb he1 he2 hW1 hκ.2.1 (by omega : 1 ≤ j + 1) hi fun X hX =>
      hdL W hWd (e W) hmem X hX _ (hεj _).1 (hεj _).2
  have HY : ∀ u < (modNb T δ W + 1) * modL δ W, ∫ ω, modY b (e W) (pathNearSchur b (e W) κ W
      (modA ε W + u) ω) ^ 6 ∂growthPathLaw W b ≤ M := fun u hu => by
    obtain ⟨-, r2, r3, -⟩ := hrange u hu
    obtain ⟨iY, mY⟩ := hMom W hWM (e W) hmem κ hκK _ r2 r3
    have hb6 : ∀ᵐ ω ∂growthPathLaw W b,
        modY b (e W) (pathNearSchur b (e W) κ W (modA ε W + u) ω) ^ 6 ≤
          modY b (e W) (pathNearSchur b (e W) κ W (modA ε W + u) ω) ^ 12 := by
      filter_upwards [ae_passiveSample W hκ.2.1 (by linarith : b < 1) he1 he2] with ω hP
      have h1' := (modY_ge hb0 hb he1 he2 (pathNearSchur_passive hP (modA ε W + u))).1
      exact pow_le_pow_right₀ h1' (by norm_num)
    have i6 : Integrable (fun ω => modY b (e W) (pathNearSchur b (e W) κ W (modA ε W + u) ω) ^ 6)
        (growthPathLaw W b) := by
      refine Integrable.mono' iY ((((measurable_modY b (e W)).comp
        (measurable_pathNearSchur' b (e W) κ _)).pow_const 6).aestronglyMeasurable) ?_
      filter_upwards [hb6] with ω h
      rw [Real.norm_of_nonneg (by positivity)]; exact h
    exact (integral_mono_ae i6 iY hb6).trans mY
  refine (absModulus_fixedW hb0 hb he1 he2 hκ.2.1 (by omega : 1 ≤ j + 1) hε.le hη hKd ha H4 Hd
    HY).trans (ENNReal.ofReal_le_ofReal ?_)
  refine (modulus_real_le (Nat.cast_nonneg _) hWpos hT0.le hδ.le hδ4 (by positivity)
    hM hη (modNb_mul_le hT0.le) (modL_le hδ.le hWδ)).trans ?_
  rw [← hQdef]; linarith

/-- **`PowerTightAlong b e κ`** from `hMT, hGA, hLp`: every admissible profile (including
`κ ≡ 0`), every moving energy `e` around a bulk `E`. -/
theorem powerTightAlong_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E)
    (hE2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e) {κ : ℝ → ℝ}
    (hκ : IsAbsorptionProfile κ) : PowerTightAlong b e κ :=
  fun k hk ε T hε hεT =>
    ⟨oneTimeTightAlong_holds hMT hGA hLp hb0 hb hE1 hE2 he hκ k hk ε hε,
      powerModulusAlong_absorbed_holds hMT hGA hLp hb0 hb hE1 hE2 he hκ k hk ε T hε hεT⟩

end BlockBand.Endpoints.Transmission
