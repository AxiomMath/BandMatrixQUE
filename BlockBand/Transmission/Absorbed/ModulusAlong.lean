module

public import BlockBand.Transmission.Absorbed.ModulusMoment
public import BlockBand.Transmission.Generator.ModAlong

/-!
# `AbsorbedPowerModulus` and `AbsorbedPowerTight`

The modulus part (b) of `LawDuality.AbsorbedPowerTight`, the tightness of the absorbed path.

* `absModulus_fixedW`: `meas_modBad_le` for `X_r = absPower b E κ W k r` with
  `G_u = c·Y'(X_u)³/W` and `e_u = 𝟙_{u=0}E[Δ_0 ∣ 𝓕_0]` (so `Σ_{u ≥ a}‖e_u‖₁ = 0`, `a ≥ 1`);
* **`absorbedPowerModulus_holds hMT hGA hLp : AbsorbedPowerModulus`**;
* **`absorbedPowerTight_holds hMT hGA hLp : LawDuality.AbsorbedPowerTight`**
  (`absorbedPowerTight_of_modulus`).

Inputs at fixed `b, E`, uniform over `0 ≤ κ ≤ K` and `u` in the block range
`[εW/2, (ε+T+1)W]`: `E Δ⁴ ≤ K₄M/W²` (`shiftFour_layer` + `integral_absInc_pow_four_le`),
`|E[Δ ∣ 𝓕]| ≤ K_d Y'³/W` (`shiftDrift_layer` + `ae_abs_condExp_absInc_le`),
`E Y'⁶ ≤ E Y'¹² ≤ M` (`absorbed_modY_moment`). The floor bookkeeping and the real arithmetic are
`modulus_subset`, `modulus_range`, `modulus_real_le`, `modL_le`, `modNb_mul_le`.
Neither continuity of `κ` nor `κ ≠ 0` is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open MeasureTheory Filter Finset Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.Generator
open scoped ENNReal NNReal ComplexOrder

variable {W : ℕ}

/-- `0 ≤ Y'(X) ≤ (W+1)(W(η⁻¹+1)+1)` at a passive input. -/
theorem modY_bound {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef) :
    0 ≤ modY b E X ∧ modY b E X ≤ ((W : ℝ) + 1) * (W * ((etaZ b E)⁻¹ + 1) + 1) := by
  obtain ⟨a0, a1⟩ := trace_pow_le_card (b := b) (by linarith) h1 h2 hX (le_refl 1)
  simp only [pow_one] at a0 a1
  have hd := jetDistance0_le_bound hb0 hb h1 h2 hX
  have hd0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hA : 0 ≤ (W : ℝ) * jetDistance0 b E X + 1 := by positivity
  refine ⟨mul_nonneg (by linarith) hA, mul_le_mul (by linarith) (by nlinarith) hA (by positivity)⟩

/-- **The absorbed modulus at one width.** -/
theorem absModulus_fixedW {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) {k : ℕ} (hk : 1 ≤ k) {ε T δ η K₄ c MY : ℝ}
    (hε : 0 ≤ ε) (hη : 0 < η) (hc : 0 ≤ c) (ha : 1 ≤ modA ε W)
    (h4 : ∀ u < (modNb T δ W + 1) * modL δ W,
      ∫ ω, modInc (absPower b E κ W k) (modA ε W + u) ω ^ 4 ∂growthPathLaw W b ≤
        K₄ / (W : ℝ) ^ 2)
    (hd : ∀ j, 1 ≤ j → ∀ᵐ ω ∂growthPathLaw W b,
      |((growthPathLaw W b)[modInc (absPower b E κ W k) j | growthFiltration W j]) ω| ≤
        c * (modY b E (pathNearSchur b E κ W j ω) ^ 3 / W))
    (hY : ∀ u < (modNb T δ W + 1) * modL δ W,
      ∫ ω, modY b E (pathNearSchur b E κ W (modA ε W + u) ω) ^ 6 ∂growthPathLaw W b ≤ MY) :
    growthPathLaw W b {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
        η < |LawDuality.absorbedPowerTrace b E κ W k t ω -
          LawDuality.absorbedPowerTrace b E κ W k t' ω|} ≤
      ENNReal.ofReal (modNb T δ W * (320 * (2 * modL δ W : ℝ) ^ 2 * (K₄ / (W : ℝ) ^ 2) /
          (η / 6) ^ 4 + (2 * modL δ W : ℝ) ^ 2 * ((c / W) ^ 2 * MY) / (η / 3) ^ 2)) := by
  set μ := growthPathLaw W b
  set X : ℕ → GrowthPath W → ℝ := absPower b E κ W k
  set ℱ := growthFiltration W
  have hX : ∀ r, StronglyMeasurable[ℱ r] (X r) := fun r => stronglyMeasurable_absPower b E κ k r
  have hB : ∀ r, ∀ᵐ ω ∂μ, |X r ω| ≤ W := fun r => ae_abs_absPower_le hκ (by linarith) h1 h2 hk r
  set G : ℕ → GrowthPath W → ℝ := fun u ω => c * (modY b E (pathNearSchur b E κ W u ω) ^ 3 / W)
  set e : ℕ → GrowthPath W → ℝ := fun u => if u = 0 then μ[modInc X 0 | ℱ 0] else 0
  have hYm : ∀ u, Measurable fun ω => modY b E (pathNearSchur b E κ W u ω) := fun u =>
    (measurable_modY b E).comp (measurable_pathNearSchur' b E κ u)
  have hYb : ∀ u, ∀ᵐ ω ∂μ, 0 ≤ modY b E (pathNearSchur b E κ W u ω) ∧
      modY b E (pathNearSchur b E κ W u ω) ≤ ((W : ℝ) + 1) * (W * ((etaZ b E)⁻¹ + 1) + 1) :=
    fun u => by
      filter_upwards [ae_passiveSample W hκ (by linarith : b < 1) h1 h2] with ω hP
      exact modY_bound hb0 hb h1 h2 (pathNearSchur_passive hP u)
  have hG2 : ∀ u, Integrable (fun ω => G u ω ^ 2) μ := fun u => by
    refine Integrable.of_bound ((((hYm u).pow_const 3).div_const _).const_mul c |>.pow_const
      2).aestronglyMeasurable ((c * ((((W : ℝ) + 1) * (W * ((etaZ b E)⁻¹ + 1) + 1)) ^ 3 / W)) ^ 2)
      ?_
    filter_upwards [hYb u] with ω h
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    refine pow_le_pow_left₀ (mul_nonneg hc (div_nonneg (pow_nonneg h.1 3) (Nat.cast_nonneg _)))
      ?_ 2
    refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)) hc
    exact pow_le_pow_left₀ h.1 h.2 3
  have he : ∀ u, AEStronglyMeasurable (e u) μ := fun u => by
    by_cases hu : u = 0
    · simp only [e, hu, ite_true]
      exact (stronglyMeasurable_condExp.mono (ℱ.le 0)).aestronglyMeasurable
    · simp only [e, hu, ite_false]; exact aestronglyMeasurable_const
  have hd' : ∀ u, ∀ᵐ ω ∂μ, |(μ[modInc X u | ℱ u]) ω| ≤ G u ω + |e u ω| := fun u => by
    by_cases hu : u = 0
    · subst hu
      filter_upwards [hYb 0] with ω h
      simp only [e, ite_true]
      have : 0 ≤ G 0 ω := mul_nonneg hc (div_nonneg (pow_nonneg h.1 3) (Nat.cast_nonneg _))
      linarith
    · filter_upwards [hd u (by omega)] with ω h
      simp only [e, hu, ite_false, Pi.zero_apply, abs_zero, add_zero]
      exact h
  have hL : 0 < modL δ W := Nat.succ_pos _
  have hGM : ∀ u < (modNb T δ W + 1) * modL δ W,
      ∫ ω, G (modA ε W + u) ω ^ 2 ∂μ ≤ (c / W) ^ 2 * MY := fun u hu => by
    have e2 : (fun ω => G (modA ε W + u) ω ^ 2) = fun ω =>
        (c / W) ^ 2 * modY b E (pathNearSchur b E κ W (modA ε W + u) ω) ^ 6 := by
      funext ω; simp only [G]; ring
    rw [e2, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hY u hu) (sq_nonneg _)
  have hmain := meas_modBad_le ℱ hX hB G e hG2 he hd' hL hη h4 hGM
  have hzero : ∑ u ∈ range ((modNb T δ W + 1) * modL δ W), eLpNorm (e (modA ε W + u)) 1 μ = 0 :=
    Finset.sum_eq_zero fun u _ => by
      have : modA ε W + u ≠ 0 := by omega
      simp only [e, this, ite_false, eLpNorm_zero]
  rw [hzero, ENNReal.zero_div, add_zero] at hmain
  exact (measure_mono (modulus_subset X hε)).trans hmain

/-- **`AbsorbedPowerModulus`** from the contract hypotheses. -/
theorem absorbedPowerModulus_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) : AbsorbedPowerModulus := by
  intro b hb0 hb E hE1 hE2 κ hκ _ k hk ε T hε hεT η θ hη hθ
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨K0, hK0⟩ := hκ.2.2
  set K := max K0 0
  have hK : 0 ≤ K := le_max_right _ _
  have hκK : ∀ s, 0 ≤ κ s ∧ κ s ≤ K := fun s => ⟨hκ.2.1 s, (hK0 s).trans (le_max_left _ _)⟩
  have hT0 : 0 < T := by linarith
  obtain ⟨K4, W4, hK4, h4L⟩ := shiftFour_layer hb0 hb hE1 hE2 hGA hLp hK j
  obtain ⟨Kd, Wd, hKd, hdL⟩ := shiftDrift_layer hb0 hb hE1 hE2 hGA hLp hK j
  obtain ⟨M, WM, hM, hMom⟩ := absorbed_modY_moment hMT hGA hLp hb0 hb hE1 hE2 hK
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
  refine ⟨δ, hδ, max (max W4 Wd) (max WM ⌈2 / ε + 1 / δ⌉₊), fun W hW => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW4, hWd⟩, hWM, hWc⟩ := hW
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
  have H4 : ∀ u < (modNb T δ W + 1) * modL δ W, ∫ ω, modInc (absPower b E κ W (j + 1))
      (modA ε W + u) ω ^ 4 ∂growthPathLaw W b ≤ K4 * M / (W : ℝ) ^ 2 := fun u hu => by
    obtain ⟨r1, r2, r3, -⟩ := hrange u hu
    obtain ⟨iY, mY⟩ := hMom W hWM κ hκK _ r2 r3
    have hGm : Measurable fun X : Matrix (Fin W) (Fin W) ℂ => K4 * (modY b E X ^ 12 / (W : ℝ) ^ 2) :=
      (((measurable_modY b E).pow_const 12).div_const _).const_mul _
    refine (integral_absInc_pow_four_le hb0 hb hE1 hE2 hW1 hκ.2.1 (by omega : 1 ≤ j + 1) r1 hGm
      ((iY.div_const _).const_mul _) fun X hX =>
        h4L W hW4 X hX _ (hεj _).1 (hεj _).2).trans ?_
    rw [integral_const_mul, integral_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right mY (sq_nonneg _)) hK4
  have Hd : ∀ i, 1 ≤ i → ∀ᵐ ω ∂growthPathLaw W b,
      |((growthPathLaw W b)[modInc (absPower b E κ W (j + 1)) i | growthFiltration W i]) ω| ≤
        Kd * (modY b E (pathNearSchur b E κ W i ω) ^ 3 / W) := fun i hi =>
    ae_abs_condExp_absInc_le hb0 hb hE1 hE2 hW1 hκ.2.1 (by omega : 1 ≤ j + 1) hi fun X hX =>
      hdL W hWd X hX _ (hεj _).1 (hεj _).2
  have HY : ∀ u < (modNb T δ W + 1) * modL δ W, ∫ ω, modY b E (pathNearSchur b E κ W
      (modA ε W + u) ω) ^ 6 ∂growthPathLaw W b ≤ M := fun u hu => by
    obtain ⟨-, r2, r3, -⟩ := hrange u hu
    obtain ⟨iY, mY⟩ := hMom W hWM κ hκK _ r2 r3
    have hb6 : ∀ᵐ ω ∂growthPathLaw W b, modY b E (pathNearSchur b E κ W (modA ε W + u) ω) ^ 6 ≤
        modY b E (pathNearSchur b E κ W (modA ε W + u) ω) ^ 12 := by
      filter_upwards [ae_passiveSample W hκ.2.1 (by linarith : b < 1) hE1 hE2] with ω hP
      have h1' := (modY_ge hb0 hb hE1 hE2 (pathNearSchur_passive hP (modA ε W + u))).1
      exact pow_le_pow_right₀ h1' (by norm_num)
    have i6 : Integrable (fun ω => modY b E (pathNearSchur b E κ W (modA ε W + u) ω) ^ 6)
        (growthPathLaw W b) := by
      refine Integrable.mono' iY ((((measurable_modY b E).comp
        (measurable_pathNearSchur' b E κ _)).pow_const 6).aestronglyMeasurable) ?_
      filter_upwards [hb6] with ω h
      rw [Real.norm_of_nonneg (by positivity)]; exact h
    exact (integral_mono_ae i6 iY hb6).trans mY
  refine (absModulus_fixedW hb0 hb hE1 hE2 hκ.2.1 (by omega : 1 ≤ j + 1) hε.le hη hKd ha H4 Hd
    HY).trans (ENNReal.ofReal_le_ofReal ?_)
  refine (modulus_real_le (Nat.cast_nonneg _) hWpos hT0.le hδ.le hδ4 (by positivity)
    hM hη (modNb_mul_le hT0.le) (modL_le hδ.le hWδ)).trans ?_
  rw [← hQdef]; linarith

/-- **`AbsorbedPowerTight`** from the contract hypotheses: the one-time clause
(`oneTimeTightAt_holds`) and the modulus (`absorbedPowerModulus_holds`). -/
theorem absorbedPowerTight_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    LawDuality.AbsorbedPowerTight :=
  absorbedPowerTight_of_modulus hMT hGA hLp (absorbedPowerModulus_holds hMT hGA hLp)

end BlockBand.Transmission.Absorbed
