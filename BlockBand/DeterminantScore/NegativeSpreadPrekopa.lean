module

public import BlockBand.DeterminantScore.NegativeSpreadConcave
public import BlockBand.External.Prekopa.SourceStatement

/-!
# Log-concave tails of `U^{-1/2}`

Prékopa's theorem applied to the convex hypograph of `f = U^{-1/2}` makes `P(f ≥ r)` log-concave
for `r ≥ 0`. It is used (`BlockBand.External.Prekopa.SourceContract`, Prékopa 1973, Theorem 6)
with `n = 1`, the joint density `F(s, λ) = 1{λ ∈ chamber, s₀ ≤ f(λ)} e^{-𝒰(λ)}` (`𝒰` from the
`density` clause of `IndexedSpectralConvexityStatement`, extended by `0` off the chamber for
measurability) and `A = univ`. Joint log-concavity on the whole space uses convexity of the
chamber and of `𝒰` (from the spectral curvature identity) and concavity of `f`
(`spreadF_concave`). The completed Lebesgue marginal is identified with `P(f(λ) ≥ s₀)` under the
sector law (`lintegral_completion_eq`, `lintegral_sectorLaw_comp`).

`tail_rpow_le`: `P(f ≥ r)^θ ≤ P(f ≥ θr)`, `0 < θ < 1` (log-concavity between `r` and `0`,
`P(f ≥ 0) = 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.NegativeSpread

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open scoped ENNReal NNReal ContDiff

variable {m : ℕ} {t : ℝ≥0} {K : Matrix (Fin m) (Fin m) ℂ} {ℓ : ℕ}

theorem lintegral_completion_eq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {g : α → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y : NullMeasurableSpace α μ, g y ∂μ.completion = ∫⁻ y, g y ∂μ := by
  let ι : NullMeasurableSpace α μ → α := fun y => y
  have hid : Measurable ι := fun s hs =>
    (MeasurableSet.nullMeasurableSet (μ := μ) hs : NullMeasurableSet s μ)
  have hmap : @Measure.map (NullMeasurableSpace α μ) α _ _ ι μ.completion = μ := by
    ext s hs
    rw [Measure.map_apply hid hs]
    rfl
  conv_rhs => rw [← hmap]
  rw [lintegral_map hg hid]

theorem lintegral_sectorLaw_comp (hK : K.IsHermitian) (hZ : 0 < (sectorMass m t K ℓ).re)
    {𝒰 : (Fin m → ℝ) → ℝ}
    (hdens : ∀ g : (Fin m → ℝ) → ℝ≥0∞, Measurable g →
      (∫⁻ x, ENNReal.ofReal (sectorDetSq K ℓ x).re * g (orderedEigs K x) ∂hermGaussian m t) =
        ENNReal.ofReal (sectorMass m t K ℓ).re *
          ∫⁻ lam in chamber m ℓ, ENNReal.ofReal (Real.exp (-𝒰 lam)) * g lam)
    {g : (Fin m → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g (orderedEigs K x) ∂sectorLaw m t K ℓ =
      ∫⁻ lam in chamber m ℓ, ENNReal.ofReal (Real.exp (-𝒰 lam)) * g lam := by
  rw [lintegral_sectorLaw hK hZ (g := fun x => g (orderedEigs K x))
    (hg.comp (measurable_orderedEigs K)), hdens g hg, ← mul_assoc,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hZ).ne' ENNReal.ofReal_ne_top, one_mul]

/-- **Log-concave tails**: with `f = U^{-1/2}`, `r ↦ P(f ≥ r)` is log-concave; with `P(f ≥ 0) = 1`
this gives `P(f ≥ r)^θ ≤ P(f ≥ θr)` for `0 < θ < 1`. -/
theorem tail_rpow_le (hP : BlockBand.External.Prekopa.SourceContract)
    (hconv : IndexedSpectralConvexityStatement) (hm : 0 < m) (ht : 0 < t)
    (hK : K.IsHermitian) (hZ : 0 < (sectorMass m t K ℓ).re) (r : ℝ) {θ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ < 1) :
    sectorLaw m t K ℓ {x | r ≤ spreadF (orderedEigs K x)} ^ θ ≤
      sectorLaw m t K ℓ {x | θ * r ≤ spreadF (orderedEigs K x)} := by
  classical
  have hprob := isProbabilityMeasure_sectorLaw hK hZ
  have ht' : (0 : ℝ) < t := NNReal.coe_pos.2 ht
  obtain ⟨𝒰, h2, hdens, hH⟩ := hconv.density m t K ℓ ht hK hZ
  set ch := chamber m ℓ
  set 𝒰' : (Fin m → ℝ) → ℝ := ch.piecewise 𝒰 0 with h𝒰'def
  have h𝒰'm : Measurable 𝒰' :=
    ContinuousOn.measurable_piecewise h2.continuousOn continuousOn_const measurableSet_chamber
  have h𝒰'eq : ∀ y ∈ ch, 𝒰' y = 𝒰 y := fun y hy => Set.piecewise_eq_of_mem _ _ _ hy
  have hconvU : ConvexOn ℝ ch 𝒰 :=
    convexOn_of_iteratedFDeriv_two_nonneg (convex_chamber ℓ) (isOpen_chamber ℓ) h2
      fun p hp v => (curvatureForm_nonneg ht' p v).trans (hH p hp v)
  set F : (Fin 1 → ℝ) × (Fin m → ℝ) → ℝ≥0 := fun z =>
    if z.2 ∈ ch ∧ z.1 0 ≤ spreadF z.2 then Real.toNNReal (Real.exp (-𝒰' z.2)) else 0 with hFdef
  have hFcoe : ∀ z, (F z : ℝ≥0∞) =
      if z.2 ∈ ch ∧ z.1 0 ≤ spreadF z.2 then ENNReal.ofReal (Real.exp (-𝒰' z.2)) else 0 := by
    intro z
    simp only [hFdef]
    split_ifs <;> rfl
  have hF : BlockBand.External.Prekopa.JointLogConcave 1 m F := by
    intro z w a ha ha1
    have hb : 0 < 1 - a := by linarith
    simp only [hFcoe]
    by_cases hz : z.2 ∈ ch ∧ z.1 0 ≤ spreadF z.2
    · by_cases hw : w.2 ∈ ch ∧ w.1 0 ≤ spreadF w.2
      · have hc2 : (a • z + (1 - a) • w).2 = a • z.2 + (1 - a) • w.2 := rfl
        have hc1 : (a • z + (1 - a) • w).1 0 = a * z.1 0 + (1 - a) * w.1 0 := rfl
        have hcch : a • z.2 + (1 - a) • w.2 ∈ ch :=
          convex_chamber ℓ hz.1 hw.1 ha.le hb.le (by ring)
        have hcf : (a • z + (1 - a) • w).1 0 ≤ spreadF (a • z + (1 - a) • w).2 := by
          rw [hc1, hc2]
          have := spreadF_concave hm hz.1 hw.1 ha ha1
          have h1 := mul_le_mul_of_nonneg_left hz.2 ha.le
          have h2 := mul_le_mul_of_nonneg_left hw.2 hb.le
          linarith
        rw [ite_eq_left hz, ite_eq_left hw, ite_eq_left ⟨hc2 ▸ hcch, hcf⟩,
          ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le ha.le,
          ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hb.le,
          ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp, hc2,
          h𝒰'eq _ hz.1, h𝒰'eq _ hw.1, h𝒰'eq _ hcch]
        have := hconvU.2 hz.1 hw.1 ha.le hb.le (by ring)
        simp only [smul_eq_mul] at this
        linarith
      · rw [ite_eq_right hw, ENNReal.zero_rpow_of_pos hb, mul_zero]
        exact bot_le
    · rw [ite_eq_right hz, ENNReal.zero_rpow_of_pos ha, zero_mul]
      exact bot_le
  have hLC := hP.theorem6 1 m F Set.univ hF convex_univ
  have hmarg : ∀ s : Fin 1 → ℝ, BlockBand.External.Prekopa.marginal F Set.univ s =
      sectorLaw m t K ℓ {x | s 0 ≤ spreadF (orderedEigs K x)} := by
    intro s
    have hmeas : Measurable fun y : Fin m → ℝ => (F (s, y) : ℝ≥0∞) := by
      simp only [hFcoe]
      exact Measurable.ite (measurableSet_chamber.inter
        (measurableSet_le measurable_const measurable_spreadF))
        (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp h𝒰'm.neg)) measurable_const
    set G : (Fin m → ℝ) → ℝ≥0∞ := {y | s 0 ≤ spreadF y}.indicator 1 with hGdef
    have hGm : Measurable G :=
      measurable_one.indicator (measurableSet_le measurable_const measurable_spreadF)
    have hpt : ∀ y, (F (s, y) : ℝ≥0∞) =
        ch.indicator (fun y => ENNReal.ofReal (Real.exp (-𝒰 y)) * G y) y := by
      intro y
      rw [hFcoe]
      by_cases hy : y ∈ ch
      · rw [Set.indicator_of_mem hy]
        by_cases hs : s 0 ≤ spreadF y
        · rw [ite_eq_left ⟨hy, hs⟩, h𝒰'eq y hy, hGdef, Set.indicator_of_mem (show y ∈ {y | s 0 ≤ spreadF y} from hs),
            Pi.one_apply, mul_one]
        · rw [ite_eq_right (fun h => hs h.2), hGdef,
            Set.indicator_of_notMem (show y ∉ {y | s 0 ≤ spreadF y} from hs), mul_zero]
      · rw [Set.indicator_of_notMem hy, ite_eq_right (fun h => hy h.1)]
    have hm1 : BlockBand.External.Prekopa.marginal F Set.univ s =
        ∫⁻ y : NullMeasurableSpace (Fin m → ℝ) (volume : Measure (Fin m → ℝ)),
          (F (s, y) : ℝ≥0∞) ∂(volume : Measure (Fin m → ℝ)).completion := by
      unfold BlockBand.External.Prekopa.marginal
      exact lintegral_congr fun y => ite_eq_left (Set.mem_univ _)
    rw [hm1, lintegral_completion_eq volume hmeas, lintegral_congr hpt,
      lintegral_indicator measurableSet_chamber,
      ← lintegral_sectorLaw_comp hK hZ hdens hGm,
      ← lintegral_indicator_one (measurableSet_le (f := fun _ => s 0)
        (g := fun x => spreadF (orderedEigs K x)) measurable_const
        (measurable_spreadF.comp (measurable_orderedEigs K)))]
    rfl
  have h := hLC (fun _ => r) (fun _ => 0) θ hθ hθ1
  rw [hmarg, hmarg, hmarg] at h
  have h0 : {x | (fun _ : Fin 1 => (0 : ℝ)) 0 ≤ spreadF (orderedEigs K x)} = Set.univ :=
    Set.eq_univ_of_forall fun x => spreadF_nonneg _
  rw [h0, measure_univ, ENNReal.one_rpow, mul_one] at h
  convert h using 3
  simp

end BlockBand.DeterminantScore.NegativeSpread
