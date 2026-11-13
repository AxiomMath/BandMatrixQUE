module

public import BlockBand.Transmission.PathScalar.AbsorbedStart
public import BlockBand.Transmission.PathScalar.MeanStepLimit
public import BlockBand.Transmission.PassiveLayer.FlucMain
public import BlockBand.Transmission.PassiveLayer.TMMain

/-!
# Length-uniform `δ₀` moments

`DeltaZeroLengthUniform`: `b, κ, p` first; then `C`; then `T`; then `W₀`; for `W ≥ W₀`,
`E ∈ bulkInterval κ` and `1 ≤ r ≤ TW`, `‖δ_{0,r}‖_{L^p(growthPathLaw W b)} ≤ C/W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LengthUniform

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PathScalar
open scoped ENNReal NNReal Matrix ComplexOrder

/-- **Length-uniform `δ₀` moments**: the constant `C` is chosen before the total length `T`. -/
def DeltaZeroLengthUniform : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ p : ℝ, 0 < κ → 1 ≤ p →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ r : ℕ,
      1 ≤ r → (r : ℝ) ≤ T * W →
        eLpNorm (fun ω => jetDistance0 b E (pathX b E W r ω)) (ENNReal.ofReal p)
          (growthPathLaw W b) ≤ ENNReal.ofReal (C / W)

/-- The exit arithmetic at `q = p + 2`: `(A + rB) W^{-(p+2)} ≤ W^{-p}` for `r ≤ TW` and
`W ≥ A + T₊B`, `W ≥ 1`. -/
theorem bad_arith_uniform {A B T p : ℝ} {r : ℕ} {x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 1 ≤ x)
    (hr : (r : ℝ) ≤ T * x) (hxA : A + max T 0 * B ≤ x) :
    A * x⁻¹ ^ (p + 2) + r * (B * x⁻¹ ^ (p + 2)) ≤ x⁻¹ ^ p := by
  have hx0 : 0 < x := by linarith
  have h := bad_arith (A := A) (B := B) (T := T) (p := p + 1) (r := r) hA hB hx hr
  rw [show p + 1 + 1 = p + 2 by ring] at h
  refine h.trans ?_
  have hi : x⁻¹ ^ (p + 1) = x⁻¹ ^ p * x⁻¹ := by
    rw [Real.rpow_add (inv_pos.2 hx0), Real.rpow_one]
  have hxp : 0 ≤ x⁻¹ ^ p := Real.rpow_nonneg (inv_nonneg.2 hx0.le) _
  have hAB : (A + max T 0 * B) * x⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hx0]; exact hxA
  rw [hi]
  calc (A + max T 0 * B) * (x⁻¹ ^ p * x⁻¹) = x⁻¹ ^ p * ((A + max T 0 * B) * x⁻¹) := by ring
    _ ≤ x⁻¹ ^ p * 1 := mul_le_mul_of_nonneg_left hAB hxp
    _ = x⁻¹ ^ p := mul_one _

/-- **Length-uniform `δ₀` moments from the one-step inputs**: the passive mean and fluctuation
steps and the start bound give length-uniform `δ₀` moments. -/
theorem deltaZeroLengthUniform_of_steps (hMean : PassiveMeanStep) (hFl : PassiveFluctuationStep)
    (hStart : AbsorbedStartBound) : DeltaZeroLengthUniform := by
  intro b hb hb' κ' p hκ' hp
  obtain ⟨d₀, ρ, Cm, Wm, hd₀, hρ0, hρ1, hCm, hmean⟩ := hMean b hb hb' κ' hκ'
  obtain ⟨Cp, Wp, hCp, hflp⟩ := hFl b hb hb' κ' hκ' p hp
  obtain ⟨Cq, Wq, hCq, hflq⟩ := hFl b hb hb' κ' hκ' (p + 2) (by linarith)
  obtain ⟨S1, Ws1, hS1, hst1⟩ := hStart b hb hb' κ' 0 p hκ' le_rfl hp
  obtain ⟨S2, Ws2, hS2, hst2⟩ := hStart b hb hb' κ' 0 (p + 2) hκ' le_rfl (by linarith)
  have hηl := etaLow_pos (by linarith : b < 1) hκ'
  have h1ρ : 0 < 1 - ρ := by linarith
  set ηl := etaLow b κ' with hηl_def
  set c₀ := Cm with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  set d := d₀ / 2 with hd
  set t := (1 - ρ) * d / 2 with ht
  have hd0 : 0 < d := by positivity
  have ht0 : 0 < t := by positivity
  set A := (d / 2)⁻¹ ^ (p + 2) * S2 ^ (p + 2) with hA
  set B := t⁻¹ ^ (p + 2) * Cq ^ (p + 2) with hB
  have hA0 : 0 ≤ A := mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hS2 _)
  have hB0 : 0 ≤ B := mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hCq _)
  set M := ηl⁻¹ + 1 with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨S1 + (c₀ + Cp) / (1 - ρ) + 1 * M, by positivity, fun T => ?_⟩
  refine ⟨max (max (max Wm Wp) (max Wq (max Ws1 Ws2)))
      (max 1 (max ⌈A + max T 0 * B⌉₊ ⌈c₀ / ((1 - ρ) * d / 2)⌉₊)), ?_⟩
  intro W hW E hE r hr hrT
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWm, hWp⟩, hWq, hWs1, hWs2⟩, hW1, hWA', hWc'⟩ := hW
  have hW0 : 0 < W := by omega
  have hx : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hx0 : (0 : ℝ) < W := by linarith
  have hWA : A + max T 0 * B ≤ W :=
    (Nat.le_ceil _).trans (by exact_mod_cast hWA')
  have hWK : 0 / (ηl ^ 2 * (W : ℝ) ^ 2) ≤ d₀ / 2 := by rw [zero_div]; positivity
  have hcW : c₀ / (W : ℝ) ^ 2 ≤ (1 - ρ) * d / 2 := by
    have hc := Nat.le_ceil (c₀ / ((1 - ρ) * d / 2))
    have hc' : ((⌈c₀ / ((1 - ρ) * d / 2)⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast hWc'
    have hWW : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
    have h1 : c₀ / ((1 - ρ) * d / 2) ≤ (W : ℝ) ^ 2 := by linarith
    rw [div_le_iff₀ (by positivity)] at h1
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨h1, h2⟩ := bulk_bounds hκ' hE
  set κ : ℝ → ℝ := fun _ => 0 with hκ
  have hκ0 : ∀ s, 0 ≤ κ s := fun _ => le_rfl
  have hκK : ∀ s, 0 ≤ κ s ∧ κ s ≤ 0 := fun _ => ⟨le_rfl, le_rfl⟩
  have hκm : ∀ (m : ℕ) (i : Fin m), layerAbsorption W κ m i ≤ 0 / (W : ℝ) ^ 2 :=
    fun m i => by simp [layerAbsorption, hκ]
  -- the zero-profile object is `δ₀` by definition
  change eLpNorm (absorbedDelta b E κ W r) (ENNReal.ofReal p) (growthPathLaw W b) ≤ _
  have hstep := ae_absorbed_step hb hb' hκ' hρ0 hρ1 le_rfl hmean hWm hW1 hWK hE hκ0 hκm
  have hstep' : ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j → j < r →
      absorbedDelta b E κ W j ω ≤ d → absorbedDelta b E κ W (j + 1) ω ≤
        ρ * absorbedDelta b E κ W j ω + c₀ / (W : ℝ) ^ 2 + stepFluct b E κ W (j + 1 - 1) ω :=
    hstep.mono fun ω h j hj _ hdj => by simpa using h j hj hdj
  have hξ : ∀ j, 2 ≤ j → j ≤ r → eLpNorm (stepFluct b E κ W (j - 1)) (ENNReal.ofReal p)
      (growthPathLaw W b) ≤ ENNReal.ofReal (Cp / W) := fun j _ _ =>
    eLpNorm_stepFluct_le (by linarith) h1 h2 (by linarith) hκ0 (j - 1)
      fun X hX => hflp W hWp E hE X hX
  have key := eLpNorm_delta_le (δ := fun j => absorbedDelta b E κ W j)
    (ξ := fun j => stepFluct b E κ W (j - 1)) (d := d) (t := t) (ρ := ρ) (c := c₀ / (W : ℝ) ^ 2)
    (n := r) (growthPathLaw W b) hp hρ0 hρ1 hd0 (by positivity) (by linarith) (by positivity)
    (by positivity) (fun j ω => absorbedDelta_nonneg b E κ j ω)
    (fun j ω => stepFluct_nonneg b E κ (j - 1) ω) (fun j => measurable_absorbedDelta b E κ j)
    (fun j => measurable_stepFluct b E κ (j - 1)) hstep' (hst1 W hWs1 E hE κ hκK) hξ hr le_rfl
    (ae_absorbed_bound hb hb' hκ' hE hκ0 r)
  have hbad := measure_bad_le (δ := fun j => absorbedDelta b E κ W j)
    (ξ := fun j => stepFluct b E κ W (j - 1)) (d := d) (t := t) (growthPathLaw W b) r
  have hm1 : growthPathLaw W b {ω | d / 2 < absorbedDelta b E κ W 1 ω} ≤
      ENNReal.ofReal ((d / 2)⁻¹ ^ (p + 2) * (S2 / W) ^ (p + 2)) :=
    markov_ofReal _ (absorbedDelta_nonneg b E κ 1) (by linarith) (by positivity) (by positivity)
      (hst2 W hWs2 E hE κ hκK)
  have hm2 : ∀ j ∈ Finset.Icc 2 r, growthPathLaw W b {ω | t < stepFluct b E κ W (j - 1) ω} ≤
      ENNReal.ofReal (t⁻¹ ^ (p + 2) * (Cq / W) ^ (p + 2)) := fun j _ =>
    markov_ofReal _ (stepFluct_nonneg b E κ (j - 1)) (by linarith) ht0 (by positivity)
      (eLpNorm_stepFluct_le (by linarith) h1 h2 (by linarith) hκ0 (j - 1)
        fun X hX => hflq W hWq E hE X hX)
  have hc2 : 0 ≤ t⁻¹ ^ (p + 2) * (Cq / W) ^ (p + 2) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  have hsum : ∑ j ∈ Finset.Icc 2 r, growthPathLaw W b {ω | t < stepFluct b E κ W (j - 1) ω} ≤
      ENNReal.ofReal (r * (t⁻¹ ^ (p + 2) * (Cq / W) ^ (p + 2))) := by
    refine (Finset.sum_le_sum hm2).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hc2)
    rw [Nat.card_Icc]; exact_mod_cast (by omega : r + 1 - 2 ≤ r)
  have hWi : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  have hdiv : ∀ y : ℝ, 0 ≤ y → (y / W) ^ (p + 2) = y ^ (p + 2) * (W : ℝ)⁻¹ ^ (p + 2) :=
    fun y hy => by rw [div_eq_mul_inv, Real.mul_rpow hy hWi]
  have hXbad : growthPathLaw W b (goodEvent (fun j => absorbedDelta b E κ W j)
      (fun j => stepFluct b E κ W (j - 1)) d t r)ᶜ ≤ ENNReal.ofReal ((W : ℝ)⁻¹ ^ p) := by
    refine hbad.trans ((add_le_add hm1 hsum).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := bad_arith_uniform (A := A) (B := B) (T := T) (p := p) (r := r) hA0 hB0 hx hrT hWA
    rw [hdiv S2 hS2, hdiv Cq hCq]
    calc (d / 2)⁻¹ ^ (p + 2) * (S2 ^ (p + 2) * (W : ℝ)⁻¹ ^ (p + 2)) +
          r * (t⁻¹ ^ (p + 2) * (Cq ^ (p + 2) * (W : ℝ)⁻¹ ^ (p + 2)))
        = A * (W : ℝ)⁻¹ ^ (p + 2) + r * (B * (W : ℝ)⁻¹ ^ (p + 2)) := by
          simp only [hA, hB]; ring
      _ ≤ _ := this
  have hp0 : (0 : ℝ) < p := by linarith
  have hpow : growthPathLaw W b (goodEvent (fun j => absorbedDelta b E κ W j)
      (fun j => stepFluct b E κ W (j - 1)) d t r)ᶜ ^ (ENNReal.ofReal p).toReal⁻¹ ≤
        ENNReal.ofReal (1 * (W : ℝ)⁻¹) := by
    rw [ENNReal.toReal_ofReal hp0.le, one_mul]
    refine (ENNReal.rpow_le_rpow hXbad (inv_nonneg.2 hp0.le)).trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (inv_nonneg.2 hp0.le),
      Real.rpow_rpow_inv hWi hp0.ne']
  refine key.trans ?_
  calc ENNReal.ofReal (S1 / W + (c₀ / (W : ℝ) ^ 2 + Cp / W) / (1 - ρ)) +
        growthPathLaw W b (goodEvent (fun j => absorbedDelta b E κ W j)
          (fun j => stepFluct b E κ W (j - 1)) d t r)ᶜ ^ (ENNReal.ofReal p).toReal⁻¹ *
            ENNReal.ofReal M
      ≤ ENNReal.ofReal (S1 / W + (c₀ / (W : ℝ) ^ 2 + Cp / W) / (1 - ρ)) +
          ENNReal.ofReal (1 * (W : ℝ)⁻¹) * ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal (S1 / W + (c₀ / (W : ℝ) ^ 2 + Cp / W) / (1 - ρ) +
          1 * (W : ℝ)⁻¹ * M) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
    _ ≤ ENNReal.ofReal ((S1 + (c₀ + Cp) / (1 - ρ) + 1 * M) / W) :=
        ENNReal.ofReal_le_ofReal (absorbed_final_arith hx hc₀0 hρ1)

/-- **`DeltaZeroLengthUniform` from the input hypotheses** `MatchedTracesContract`,
`GaussianAbsorptionContract` and `GaussianLpGradient`. -/
theorem deltaZeroLengthUniform_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) : DeltaZeroLengthUniform :=
  deltaZeroLengthUniform_of_steps
    (passiveMeanStep_holds (PassiveLayer.passiveBounds_holds hGA hLp))
    (PassiveLayer.passiveFluctuationStep_holds hGA hLp)
    (absorbedStartBound_holds hMT (PassiveLayer.passiveBounds_holds hGA hLp))

end BlockBand.Transmission.LengthUniform
