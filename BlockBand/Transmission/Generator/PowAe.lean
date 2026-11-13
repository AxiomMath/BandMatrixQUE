module

public import BlockBand.Transmission.Generator.PowBound

/-!
# The `k = j + 2` drift error: almost-sure bound along the path

**`driftError_pow_le hGA hLp hP`**: `b, κ, j` first; then `K ≥ 0, W₀`; for `W ≥ W₀`, path energy
`E' ∈ bulkInterval κ`, stationary jet `s` at `E'`, base energy `E` and `r ≥ 1`, a.s.
`|driftError b E E' W (j+2) r| ≤ K(g+1)⁵(a+1)²(t+1)²(d+1)/√W³ + |D₀(E) - D₀(E')|k²(g+1)²/√W²`
(`g, a, t, d` = `pathG, pathA, pathT, pathD`). From `driftError_pow_ae`, `layer_bulk`,
`layerErr_le_prod`, `layerTau_eq` and `transmissionDrift_sub_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PathScalar BlockBand.Transmission.SourceMixing
open scoped ENNReal ComplexOrder

variable {W : ℕ}

/-- `τ ≤ 4(g+1)(|Tr Qf| + hs(Q,f))`. -/
theorem layerTau_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hg : 0 ≤ (passiveTransmission b E X).trace.re) :
    layerTau b E X ≤ 4 * ((passiveTransmission b E X).trace.re + 1) *
      (‖(passiveQ b E X * passiveF b E X).trace‖ +
        hsSandwich (passiveQ b E X) (passiveF b E X)) := by
  have hη0 := (PassiveCovariance.etaZ_pos b E hb h1 h2).le
  have hη1 := etaZ_le_one hb0 hb h1 h2
  rw [layerTau_eq hη0]
  set g := (passiveTransmission b E X).trace.re
  set A := ‖(passiveQ b E X * passiveF b E X).trace‖
  set H := hsSandwich (passiveQ b E X) (passiveF b E X)
  have hA : 0 ≤ A := norm_nonneg _
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hsg : Real.sqrt g ≤ g + 1 := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have h3 : A + Real.sqrt g * H ≤ (g + 1) * (A + H) := by nlinarith
  calc 4 * etaZ b E * (A + Real.sqrt g * H) ≤ 4 * 1 * (A + Real.sqrt g * H) := by gcongr
    _ ≤ 4 * ((g + 1) * (A + H)) := by linarith
    _ = _ := by ring

/-- The layer term against the normalised product, at a deterministic passive `X`. -/
theorem layer_prod_le {KL : ℝ} (hKL : 0 ≤ KL) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (hW1 : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : (passiveY X).PosSemidef) (s : ℂ) {I : ℝ}
    (hI : |I| ≤ KL * layerErr (passiveTransmission b E X).trace.re
      (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) (jetDistance1 b E s X) (layerTau b E X)
      (Real.sqrt W)) :
    |I| ≤ 23 * KL * (((passiveTransmission b E X).trace.re + 1) ^ 5 *
      (W * jetDistance0 b E X + 1) ^ 2 *
      (Real.sqrt W * (‖(passiveQ b E X * passiveF b E X).trace‖ +
        hsSandwich (passiveQ b E X) (passiveF b E X)) + 1) ^ 2 *
      (W * jetDistance1 b E s X + 1)) / Real.sqrt W ^ 3 := by
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  have hs2 : Real.sqrt W ^ 2 = W := Real.sq_sqrt hWpos.le
  have hs1 : 1 ≤ Real.sqrt W := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hWr
  have hs0 : 0 < Real.sqrt W := by linarith
  have hT := passiveTransmission_posSemidef (b := b) (by linarith) h1 h2 hX
  have hg : 0 ≤ (passiveTransmission b E X).trace.re := (mm_trace_posSemidef hT).1
  have hle := layerErr_le_prod (g := (passiveTransmission b E X).trace.re)
    (δ := jetDistance0 b E X) (d := jetDistance1 b E s X) (τ := layerTau b E X)
    (s := Real.sqrt W) (a := W * jetDistance0 b E X)
    (t := Real.sqrt W * (‖(passiveQ b E X * passiveF b E X).trace‖ +
        hsSandwich (passiveQ b E X) (passiveF b E X)))
    (dd := W * jetDistance1 b E s X) hg (mul_nonneg hWpos.le (norm_nonneg _))
    (mul_nonneg hs0.le (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)))
    (mul_nonneg hWpos.le (norm_nonneg _)) hs1
    (by rw [hs2]; field_simp) (by rw [hs2]; field_simp)
    (by
      refine (layerTau_le hb0 (by linarith) h1 h2 hg).trans (le_of_eq ?_)
      field_simp)
    (by unfold layerTau hsSandwich; positivity)
  rw [hs2] at hle
  refine hI.trans ?_
  refine (mul_le_mul_of_nonneg_left hle hKL).trans (le_of_eq ?_)
  ring

/-- **The `k = j + 2` drift error, a.s. bound along the path.** -/
theorem driftError_pow_le (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) (j : ℕ) :
    ∃ (K : ℝ) (W₀ : ℕ), 0 ≤ K ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E' ∈ bulkInterval κ,
      ∀ s : ℂ, IsStationaryJet b E' s → ∀ E : ℝ, ∀ r : ℕ, 1 ≤ r →
      ∀ᵐ ω ∂growthPathLaw W b, |driftError b E E' W (j + 2) r ω| ≤
        K * ((pathG b E' W r ω + 1) ^ 5 * (pathA b E' W r ω + 1) ^ 2 *
          (pathT b E' W r ω + 1) ^ 2 * (pathD b E' s W r ω + 1)) / Real.sqrt W ^ 3 +
        |transportD0 b E - transportD0 b E'| * ((j + 2 : ℕ) : ℝ) ^ 2 *
          (pathG b E' W r ω + 1) ^ 2 / Real.sqrt W ^ 2 := by
  obtain ⟨KL, WL, hKL, hL⟩ := layer_bulk hGA hLp hP hb0 hb hκ j
  refine ⟨23 * KL, max WL 1, by positivity, fun W hW E' hE' s hs E r hr => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨hWL, hW1⟩ := hW
  have h1 : -2 < E' := by have := hE'.1; linarith
  have h2 : E' < 2 := by have := hE'.2; linarith
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  have hs2 : Real.sqrt W ^ 2 = W := Real.sq_sqrt hWpos.le
  filter_upwards [driftError_pow_ae (E := E) hb0 hb h1 h2 hW1 (k := j + 2) (by omega) hr,
    mm_ae_passive (W := W) (b := b) (by linarith) h1 h2 r] with ω e hX
  rw [e]
  have hA := layer_prod_le hKL hb0 hb h1 h2 hW1 hX s (hL W hWL E' hE' s hs _ hX)
  have hT := passiveTransmission_posSemidef (b := b) (by linarith) h1 h2 hX
  have hT1 := one_sub_passiveTransmission_posSemidef b E' (pathX b E' W r ω)
  have hg : 0 ≤ pathG b E' W r ω := (mm_trace_posSemidef hT).1
  have hP : ∀ m, 1 ≤ m → 0 ≤ ((passiveTransmission b E' (pathX b E' W r ω)) ^ m).trace.re ∧
      ((passiveTransmission b E' (pathX b E' W r ω)) ^ m).trace.re ≤
        ((passiveTransmission b E' (pathX b E' W r ω)) ^ 1).trace.re := fun m hm => by
    rw [pow_one]; exact trace_pow_mem hT hT1 m hm
  have hD := transmissionDrift_sub_le (k := j + 2) (by omega) hP (transportD0 b E')
    (transportD0 b E)
  rw [pow_one] at hD
  have hg2 : pathG b E' W r ω ^ 2 ≤ (pathG b E' W r ω + 1) ^ 2 :=
    pow_le_pow_left₀ hg (by linarith) 2
  have hB : |(transmissionDrift (transportD0 b E') (j + 2)
        (fun m => ((passiveTransmission b E' (pathX b E' W r ω)) ^ m).trace.re) -
      transmissionDrift (transportD0 b E) (j + 2)
        (fun m => ((passiveTransmission b E' (pathX b E' W r ω)) ^ m).trace.re)) / W| ≤
      |transportD0 b E - transportD0 b E'| * ((j + 2 : ℕ) : ℝ) ^ 2 *
        (pathG b E' W r ω + 1) ^ 2 / Real.sqrt W ^ 2 := by
    rw [abs_div, abs_of_pos hWpos, hs2, abs_sub_comm (transportD0 b E)]
    refine div_le_div_of_nonneg_right ?_ hWpos.le
    refine hD.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg2 (by positivity))
      (abs_nonneg _)
  refine (abs_add_le _ _).trans (add_le_add ?_ hB)
  exact hA

end BlockBand.Transmission.Generator
