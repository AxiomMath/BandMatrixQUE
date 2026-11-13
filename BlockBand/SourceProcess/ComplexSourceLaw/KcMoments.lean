module

public import BlockBand.SourceProcess.ComplexSourceLaw.Marginal

/-!
# Moments of the entries of `𝒦` from the raw tag bound

`lintegral_kc_le`: under the raw tag bounds at the path length (`RawTagBoundAt`), the entries of
the complex source matrix satisfy `E|𝒦ᵢⱼ|^p ≤ C(mᵢmⱼ)^{p/2}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws

variable {W : ℕ}

/-- The raw tag bounds at fixed `(W, E, n)`, constant `C` (the body of `RawTagMoments`). -/
def RawTagBoundAt (b E : ℝ) (W n : ℕ) (p C : ℝ) : Prop :=
  ∀ (j k : Fin n) (mj mk : ℝ), 0 ≤ mj → 0 ≤ mk →
    (∫⁻ x, ENNReal.ofReal (‖star (tagVector W n j mj x.2.1) ⬝ᵥ
        ((fullInverse b E W n x.1).toBlocks₁₁ *ᵥ tagVector W n k mk x.2.2)‖ ^ p)
      ∂(growthPathLaw W b).prod
        ((circularVectorLaw (Fin W)).prod (circularVectorLaw (Fin W))) ≤
      ENNReal.ofReal (C * (mj * mk) ^ (p / 2))) ∧
    ∫⁻ x, ENNReal.ofReal (‖star (tagVector W n j mj x.2) ⬝ᵥ
        ((fullInverse b E W n x.1).toBlocks₁₁ *ᵥ tagVector W n j mj x.2)‖ ^ p)
      ∂(growthPathLaw W b).prod (circularVectorLaw (Fin W)) ≤
      ENNReal.ofReal (C * (mj * mj) ^ (p / 2))

theorem tagForm_zero_left {n : ℕ} (G : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ)
    (v : Fin n × Fin W → ℂ) : tagForm G 0 v = 0 := by simp [tagForm]

theorem tagForm_zero_right {n : ℕ} (G : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ)
    (u : Fin n × Fin W → ℂ) : tagForm G u 0 = 0 := by simp [tagForm]

/-- **`E|𝒦ᵢⱼ|^p ≤ C(mᵢmⱼ)^{p/2}`** from the raw tag bounds at the path length. -/
theorem lintegral_kc_le (b E : ℝ) {np : ℕ} (n : ℕ) (τ m : Fin np → ℝ) (hm : ∀ j, 0 ≤ m j)
    {p C : ℝ} (hp : 0 < p) (hraw : RawTagBoundAt b E W n p C) (i j : Fin np) :
    ∫⁻ x, ENNReal.ofReal (‖complexSourceK b E W n τ m x i j‖ ^ p) ∂probedPathLaw W np b ≤
      ENNReal.ofReal (C * (m i * m j) ^ (p / 2)) := by
  simp_rw [complexSourceK_apply]
  by_cases hi : ⌊(W : ℝ) * τ i⌋₊ < n
  swap
  · simp_rw [probeColumn_eq_zero n τ m _ i hi, tagForm_zero_left, norm_zero,
      Real.zero_rpow hp.ne', ENNReal.ofReal_zero, lintegral_zero]
    exact zero_le
  by_cases hj : ⌊(W : ℝ) * τ j⌋₊ < n
  swap
  · simp_rw [probeColumn_eq_zero n τ m _ j hj, tagForm_zero_right, norm_zero,
      Real.zero_rpow hp.ne', ENNReal.ofReal_zero, lintegral_zero]
    exact zero_le
  simp_rw [probeColumn_eq_tagVector n τ m _ i hi, probeColumn_eq_tagVector n τ m _ j hj]
  set ki : Fin n := ⟨n - 1 - ⌊(W : ℝ) * τ i⌋₊, by omega⟩
  set kj : Fin n := ⟨n - 1 - ⌊(W : ℝ) * τ j⌋₊, by omega⟩
  have hG := measurable_interior (W := W) b E n
  have hF : ∀ (u v : (Fin W → ℂ) × (Fin W → ℂ) → Fin W → ℂ), Measurable u → Measurable v →
      Measurable fun y : GrowthPath W × ((Fin W → ℂ) × (Fin W → ℂ)) => ENNReal.ofReal
        (‖tagForm (fullInverse b E W n y.1).toBlocks₁₁ (tagVector W n ki (m i) (u y.2))
          (tagVector W n kj (m j) (v y.2))‖ ^ p) := fun u v hu hv =>
    ENNReal.measurable_ofReal.comp ((measurable_tagForm (hG.comp measurable_fst)
      ((measurable_tagVector n ki (m i)).comp (hu.comp measurable_snd))
      ((measurable_tagVector n kj (m j)).comp (hv.comp measurable_snd))).norm.pow_const p)
  have : IsProbabilityMeasure (growthPathLaw W b) :=
    Transmission.Bridge.isProbabilityMeasure_growthPathLaw W b
  by_cases hij : i = j
  · subst hij
    have hmap : (probedPathLaw W np b).map (Prod.map id (fun g : Fin np → Fin W → ℂ => g i)) =
        (growthPathLaw W b).prod (circularVectorLaw (Fin W)) := by
      rw [probedPathLaw, ← Measure.map_prod_map _ _ measurable_id (measurable_pi_apply i),
        Measure.map_id, (measurePreserving_eval (fun _ : Fin np => circularVectorLaw (Fin W))
          i).map_eq]
    have hFm : Measurable fun y : GrowthPath W × (Fin W → ℂ) => ENNReal.ofReal
        (‖tagForm (fullInverse b E W n y.1).toBlocks₁₁ (tagVector W n ki (m i) y.2)
          (tagVector W n ki (m i) y.2)‖ ^ p) :=
      ENNReal.measurable_ofReal.comp ((measurable_tagForm (hG.comp measurable_fst)
        ((measurable_tagVector n ki (m i)).comp measurable_snd)
        ((measurable_tagVector n ki (m i)).comp measurable_snd)).norm.pow_const p)
    have e := lintegral_map (μ := probedPathLaw W np b) hFm
      ((measurable_id (α := GrowthPath W)).prodMap
      (measurable_pi_apply (X := fun _ : Fin np => Fin W → ℂ) i))
    rw [hmap] at e
    exact e.symm.trans_le (hraw ki ki (m i) (m i) (hm i) (hm i)).2
  · have hmap : (probedPathLaw W np b).map
        (Prod.map id (fun g : Fin np → Fin W → ℂ => (g i, g j))) =
        (growthPathLaw W b).prod
          ((circularVectorLaw (Fin W)).prod (circularVectorLaw (Fin W))) := by
      rw [probedPathLaw, ← Measure.map_prod_map _ _ measurable_id
        ((measurable_pi_apply i).prodMk (measurable_pi_apply j)), Measure.map_id,
        pi_map_pair _ hij]
    have e := lintegral_map (μ := probedPathLaw W np b)
      (hF Prod.fst Prod.snd measurable_fst measurable_snd)
      ((measurable_id (α := GrowthPath W)).prodMap
        ((measurable_pi_apply (X := fun _ : Fin np => Fin W → ℂ) i).prodMk
          (measurable_pi_apply (X := fun _ : Fin np => Fin W → ℂ) j)))
    rw [hmap] at e
    exact e.symm.trans_le (hraw ki kj (m i) (m j) (hm i) (hm j)).1

end BlockBand.SourceProcess.ComplexSourceLaw
