module

public import BlockBand.Critical.GlobalSource.ReplacementEndpoints

/-!
# Global Gaussian source: proof of the source replacement estimate

* `sourceReplacement_holds : ComplexSourceLawContract → SourceReplacementStatement`, from the
  fields `rawTagMoments` (`p = 4`, two independent tags; `p = 2`, one tag) and
  `extendedSourceMoments` (`p = 2`, through `exists_lintegral_sourceMoment2_le`). Constants:
  `C = 16 J stepConst J C₄ C₂ Ce (|T||qmax|)`, `W₀ = max 1 (max W₄ (max W₂ We))`. The case `L = 0`
  is handled separately (`charFun_sub_eq_zero_of_length_zero`).
* `globalGaussianSource_holds_of_sourceLimit : ComplexSourceLawContract →
  ComplexSourceLimitAlongSequences → GlobalGaussianSourceStatement`.

Proof map (the `Replacement…` modules, in import order):
`ReplacementGaussian` (circular Gaussian identities, Gaussian stability) →
`ReplacementTaylor` (scalar Taylor step, one Lindeberg swap, product-law bookkeeping) →
`ReplacementHybrid` (slots, exact covariance, matched moments, hybrid phase `θ₀ + tα + t²β`) →
`ReplacementSwap` (one swap of the hybrid) → `ReplacementMoments` (conditional Gaussian moment
bounds for a fixed matrix) → `ReplacementPath` (path averages from `rawTagMoments`) →
`ReplacementLindeberg` (`J·M` swaps telescope to `O(M^{-1/2})`) → `ReplacementEndpoints`
(all-Gaussian hybrid = `profileProbeLaw`, all-tag hybrid = `discreteSampledLaw`) → this file.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)
open BlockBand.Internal.Contracts.CriticalEntire (tagGroup)
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers (bulkInterval)
open scoped ComplexConjugate NNReal ENNReal Matrix RealInnerProductSpace
open Complex (exp I)

/-- Masses of profiles `0 ≤ r ≤ qmax` on paths of length `L ≤ TW` are at most `|T||qmax|`. -/
theorem profileMass_le {W L : ℕ} (hW : 0 < W) {T qmax : ℝ} (hL : (L : ℝ) ≤ T * W)
    {r : Fin L → ℝ} (hr : ∀ k, 0 ≤ r k ∧ r k ≤ qmax) : profileMass W L r ≤ |T| * |qmax| := by
  unfold profileMass
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hs : ∑ k, r k ≤ L * |qmax| := by
    calc ∑ k, r k ≤ ∑ _k : Fin L, |qmax| :=
          Finset.sum_le_sum fun k _ => (hr k).2.trans (le_abs_self _)
      _ = L * |qmax| := by simp
  have hLW : (L : ℝ) / W ≤ |T| := by
    rw [div_le_iff₀ hW']; exact hL.trans (mul_le_mul_of_nonneg_right (le_abs_self T) hW'.le)
  calc (W : ℝ)⁻¹ * ∑ k, r k ≤ (W : ℝ)⁻¹ * (L * |qmax|) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (L / W) * |qmax| := by ring
    _ ≤ |T| * |qmax| := mul_le_mul_of_nonneg_right hLW (abs_nonneg _)

/-- With no remaining blocks both probe matrices vanish. -/
theorem charFun_sub_eq_zero_of_length_zero (b E : ℝ) (W J M : ℕ) (r : Fin J → Fin 0 → ℝ)
    (hr : ∀ a k, 0 ≤ r a k) (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) :
    charFun ((profileProbeLaw W 0 J b).map
        (fun x => matrixCoord J (profileProbeMatrix b E W 0 r x))) u -
      charFun ((discreteSampledLaw W 0 J M b r).map
        (fun y => matrixCoord J (discreteSampledMatrix b E W 0 r y))) u = 0 := by
  have hP : IsProbabilityMeasure (growthPathLaw W b) := by unfold growthPathLaw; infer_instance
  have hblk : ∀ s : Fin (J * M), IsProbabilityMeasure (discreteBlockLaw W 0 (r (tagGroup s))) :=
    fun s => isProbabilityMeasure_discreteBlockLaw (hr _)
  have h1 : (fun x => matrixCoord J (profileProbeMatrix b E W 0 r x)) =
      fun _ => matrixCoord J 0 := by
    funext x
    have : profileProbeMatrix b E W 0 r x = 0 := by
      funext a c; simp [profileProbeMatrix, dotProduct]
    rw [this]
  have h2 : (fun y => matrixCoord J (discreteSampledMatrix b E W 0 r (M := M) y)) =
      fun _ => matrixCoord J 0 := by
    funext y
    have : discreteSampledMatrix b E W 0 r (M := M) y = 0 := by
      funext a c; simp [discreteSampledMatrix, blockSampledMatrix, dotProduct]
    rw [this]
  rw [h1, h2, Measure.map_const, Measure.map_const]
  unfold profileProbeLaw discreteSampledLaw
  simp [measure_univ]

/-- **The source replacement estimate** for characteristic tests (`SourceReplacementStatement`),
from `ComplexSourceLawContract` (fields `rawTagMoments` at `p = 4` and `p = 2`, and
`extendedSourceMoments` at `p = 2`). -/
theorem sourceReplacement_holds (hCS : ComplexSourceLawContract) : SourceReplacementStatement := by
  intro b hb hb' κI hκI T qmax J
  obtain ⟨C₄, W₄, h4⟩ := hCS.rawTagMoments b hb hb' κI hκI T 4 (by norm_num)
  obtain ⟨C₂, W₂, h2⟩ := hCS.rawTagMoments b hb hb' κI hκI T 2 (by norm_num)
  obtain ⟨Ce, We, he⟩ := exists_lintegral_sourceMoment2_le hCS hb hb' hκI T qmax
  refine ⟨16 * J * stepConst J C₄ C₂ Ce (|T| * |qmax|), max 1 (max W₄ (max W₂ We)),
    fun W hW E hE L hL r hrq M hM u => ?_⟩
  have hW1 : 1 ≤ W := le_trans (le_max_left _ _) hW
  have hW4 : W₄ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hW
  have hWe : We ≤ W := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hW
  have hr : ∀ a k, 0 ≤ r a k := fun a k => (hrq a k).1
  have hM' : 0 < M := hM
  have hC : 0 ≤ 16 * (J : ℝ) * stepConst J C₄ C₂ Ce (|T| * |qmax|) := by
    have := stepConst_nonneg J C₄ C₂ Ce (|T| * |qmax|); positivity
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · subst hL0
    rw [charFun_sub_eq_zero_of_length_zero b E W J M r hr u, norm_zero]
    positivity
  have hraw4 : RawTagFour b E W L C₄ := fun k k' m₁ m₂ h₁ h₂ =>
    (h4 W hW4 E hE L hL k k' m₁ m₂ h₁ h₂).1
  have hraw2 : RawTagTwo b E W L C₂ := fun k m hm => (h2 W hW2 E hE L hL k k m m hm hm).2
  have hext : ∀ a, ∫⁻ ω, ENNReal.ofReal (sourceMoment2 b E W L (r a) ω) ∂growthPathLaw W b ≤
      ENNReal.ofReal Ce := fun a => he W hWe E hE L hL (r a) (hrq a)
  have hμ : ∀ a, profileMass W L (r a) ≤ |T| * |qmax| := fun a =>
    profileMass_le (by omega) hL (hrq a)
  rw [← hybridChar_empty b E hr hM' u, ← hybridChar_univ b E hr hLpos u, norm_sub_rev]
  refine (norm_hybridChar_univ_sub_empty_le hraw4 hraw2 hr hμ hext hM' u).trans ?_
  have hu : (1 + 2 * ‖u‖) ^ 3 ≤ 8 * (1 + ‖u‖) ^ 3 := by
    have h0 : 0 ≤ 1 + 2 * ‖u‖ := by positivity
    have h1 : 1 + 2 * ‖u‖ ≤ 2 * (1 + ‖u‖) := by linarith
    calc (1 + 2 * ‖u‖) ^ 3 ≤ (2 * (1 + ‖u‖)) ^ 3 := pow_le_pow_left₀ h0 h1 3
      _ = 8 * (1 + ‖u‖) ^ 3 := by ring
  have hs := stepConst_nonneg J C₄ C₂ Ce (|T| * |qmax|)
  have hsq : 0 < Real.sqrt M := Real.sqrt_pos.2 (by exact_mod_cast hM')
  rw [div_le_div_iff_of_pos_right hsq]
  calc 2 * (J : ℝ) * (1 + 2 * ‖u‖) ^ 3 * stepConst J C₄ C₂ Ce (|T| * |qmax|)
      ≤ 2 * (J : ℝ) * (8 * (1 + ‖u‖) ^ 3) * stepConst J C₄ C₂ Ce (|T| * |qmax|) := by gcongr
    _ = _ := by ring

/-- **The global Gaussian source statement** (`GlobalGaussianSourceStatement`) from
`ComplexSourceLawContract` and `ComplexSourceLimitAlongSequences`; the replacement estimate is
`sourceReplacement_holds`. -/
theorem globalGaussianSource_holds_of_sourceLimit (hCS : ComplexSourceLawContract)
    (hA : ComplexSourceLimitAlongSequences) : GlobalGaussianSourceStatement :=
  globalGaussianSource_holds_of_replacement hCS hA (sourceReplacement_holds hCS)

end BlockBand.Critical.GlobalSource
