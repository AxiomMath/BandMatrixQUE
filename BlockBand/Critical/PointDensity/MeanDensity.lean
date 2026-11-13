module

public import BlockBand.Coarea.FreshPalmDensity
public import BlockBand.Internal.Contracts.Critical

/-!
# Point density: the canonical continuous mean density

The mean eigenvalue measure of `F + G`, `G ~ gueMeasure (Fin N) (c/N)` (`GUE_N(c/N)`), has an
explicit continuous, positive and bounded Lebesgue density, for every `N ≥ 1`, Hermitian `F` and
`c > 0` (exact identities, no limit). The proof uses the scalar split `G = G⁰ + ζ I`,
`G⁰ ~ freshTracelessLaw N c`, `ζ ~ N(0, c/N²)` independent (`scalarShiftLaw_fin_eq_gueMeasure`).

* `map_freshEigenvalue_eq_withDensity`: `Law(λ_ℓ(F + G))` has the Lebesgue density
  `rankDensity F c ℓ E = E_{G⁰} φ_{√c/N}(E - λ_ℓ(F + G⁰))` (the scalar Palm side with
  observable `1`).
* `freshMeanEigenvalueMeasure_eq_withDensity`: the normalized mean eigenvalue measure
  `N⁻¹ Σ_ℓ Law(λ_ℓ(F + G))` is `volume.withDensity (meanDensity F c)`.
* `continuous_meanDensity`, `meanDensity_pos`, `meanDensity_le`: the density is continuous,
  strictly positive and bounded by `densityBound c N = (2π c/N²)^{-1/2} = N/√(2πc)`,
  uniformly in `F`.
* `apply_eq_meanDensityReal`: **every** continuous `ρ` with
  `freshMeanEigenvalueMeasure N c F = volume.withDensity (ofReal ∘ ρ)` equals
  `meanDensityReal F c = (meanDensity F c ·).toReal` everywhere (two continuous densities of the
  same measure agree everywhere).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.PointDensity

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Critical
  BlockBand.Coarea.FreshPalm BlockBand.Coarea.GUELaw BlockBand.Coarea.PoleExclusion
  BlockBand.Coarea.FixedOmega
open scoped ENNReal NNReal

variable {N : ℕ}

/-- Lebesgue density of `Law(λ_ℓ(F + G))`, `G ~ GUE_N(c/N)`:
`E_{G⁰}[φ_{√c/N}(E - λ_ℓ(F + G⁰))]` (the scalar Palm side of the fresh Palm formula with the
observable `1`). -/
def rankDensity (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (ℓ : Fin N) (E : ℝ) : ℝ≥0∞ :=
  palmSide F c ℓ (fun _ => 1) E

/-- The uniform Gaussian prefactor `(2π c/N²)^{-1/2}` (`= N/√(2πc)` for `c > 0`, `N ≥ 1`). -/
def densityBound (c : ℝ) (N : ℕ) : ℝ :=
  (Real.sqrt (2 * Real.pi * BlockBand.Palm.scalarVariance (Real.toNNReal c) N))⁻¹

/-- The normalized mean density `N⁻¹ Σ_ℓ rankDensity F c ℓ`. -/
def meanDensity (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (E : ℝ) : ℝ≥0∞ :=
  (N : ℝ≥0∞)⁻¹ * ∑ ℓ : Fin N, rankDensity F c ℓ E

theorem continuous_rankDensity (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (ℓ : Fin N) :
    Continuous (rankDensity F c ℓ) :=
  continuous_palmSide F c ℓ measurable_const ENNReal.one_ne_top (fun _ => le_rfl)

theorem measurable_rankDensity (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (ℓ : Fin N) :
    Measurable (rankDensity F c ℓ) :=
  (continuous_rankDensity F c ℓ).measurable

theorem rankDensity_le (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (ℓ : Fin N) (E : ℝ) :
    rankDensity F c ℓ E ≤ ENNReal.ofReal (densityBound c N) := by
  unfold rankDensity palmSide
  calc ∫⁻ A0, ENNReal.ofReal (palmWeight F c E ℓ A0) * 1 ∂freshTracelessLaw N c
      ≤ ∫⁻ _A0, ENNReal.ofReal (densityBound c N) ∂freshTracelessLaw N c := by
        refine lintegral_mono fun A0 => ?_
        rw [mul_one]
        exact ENNReal.ofReal_le_ofReal (BlockBand.Palm.scalarWeight_le_prefactor _ _ _ _)
    _ = ENNReal.ofReal (densityBound c N) := by rw [lintegral_const, measure_univ, mul_one]

theorem rankDensity_pos (hN : 0 < N) (F : Matrix (Fin N) (Fin N) ℂ) {c : ℝ} (hc : 0 < c)
    (ℓ : Fin N) (E : ℝ) : 0 < rankDensity F c ℓ E := by
  unfold rankDensity palmSide
  have hσ : BlockBand.Palm.scalarVariance (Real.toNNReal c) N ≠ 0 :=
    BlockBand.Palm.scalarVariance_ne_zero (Real.toNNReal_pos.2 hc).ne' hN.ne'
  have hm : Measurable fun A0 : Matrix (Fin N) (Fin N) ℂ =>
      ENNReal.ofReal (palmWeight F c E ℓ A0) * 1 :=
    (ENNReal.measurable_ofReal.comp (measurable_palmWeight F c E ℓ)).mul measurable_const
  rw [pos_iff_ne_zero, Ne, lintegral_eq_zero_iff hm]
  intro h
  have : (ae (freshTracelessLaw N c)).NeBot :=
    ae_neBot.2 (IsProbabilityMeasure.ne_zero _)
  obtain ⟨A0, hA0⟩ := h.exists
  have hpos : 0 < ENNReal.ofReal (palmWeight F c E ℓ A0) * 1 := by
    rw [mul_one, ENNReal.ofReal_pos]
    unfold palmWeight BlockBand.Palm.scalarWeight
    exact gaussianPDFReal_pos _ _ _ hσ
  have hA0' : ENNReal.ofReal (palmWeight F c E ℓ A0) * 1 = 0 := hA0
  rw [hA0'] at hpos
  exact lt_irrefl _ hpos

/-- **Law of one rank.** For `N ≥ 1`, Hermitian `F`, `c > 0`:
`Law(λ_ℓ(F + G)) = volume.withDensity (rankDensity F c ℓ)`, `G ~ GUE_N(c/N)`. -/
theorem map_freshEigenvalue_eq_withDensity (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {c : ℝ} (hc : 0 < c) (ℓ : Fin N) :
    (gueMeasure (Fin N) (Real.toNNReal (c / N))).map (fun G => freshEigenvalue (F + G) ℓ) =
      volume.withDensity (rankDensity F c ℓ) := by
  have hmeas : Measurable fun G : Matrix (Fin N) (Fin N) ℂ => freshEigenvalue (F + G) ℓ :=
    (measurable_freshEigenvalue ℓ).comp (measurable_matrix_add measurable_const measurable_id)
  refine Measure.ext_of_lintegral _ fun h hh => ?_
  rw [lintegral_map hh hmeas,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_rankDensity F c ℓ) hh]
  set t : ℝ≥0 := Real.toNNReal (c / N)
  set c' : ℝ≥0 := Real.toNNReal c
  set σ : ℝ≥0 := BlockBand.Palm.scalarVariance c' N
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc' : c' ≠ 0 := (Real.toNNReal_pos.2 hc).ne'
  have hσ : (σ : ℝ) = (t : ℝ) / N := by
    rw [BlockBand.Palm.coe_scalarVariance, Real.coe_toNNReal _ hc.le,
      Real.coe_toNNReal _ (div_pos hc hNr).le]
    field_simp
  set μ0 := freshTracelessLaw N c
  have hμ0 : μ0 = (gueMeasure (Fin N) t).map tracelessPart := rfl
  set ν : Matrix (Fin N) (Fin N) ℂ → ℝ := fun A0 => freshEigenvalue (F + A0) ℓ
  have hν : Measurable ν := hmeas
  set Φ : Matrix (Fin N) (Fin N) ℂ × ℝ → ℝ≥0∞ := fun p => h p.2
  have hΦ : Measurable Φ := hh.comp measurable_snd
  rw [← scalarShiftLaw_fin_eq_gueMeasure hN t σ hσ]
  unfold scalarShiftLaw
  rw [lintegral_map (f := fun G => h (freshEigenvalue (F + G) ℓ)) (hh.comp hmeas)
    measurable_scalarAdd, ← hμ0]
  have hcongr : (fun y : Matrix (Fin N) (Fin N) ℂ × ℝ =>
      h (freshEigenvalue (F + (y.1 + (y.2 : ℂ) • 1)) ℓ)) =ᵐ[μ0.prod
        (gaussianReal 0 σ)] fun y => Φ (y.1, ν y.1 + y.2) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ0)
      (ν := gaussianReal 0 σ)).ae (ae_freshTracelessLaw hN c)] with y hy
    simp only [Φ, ν]
    rw [← add_assoc, freshEigenvalue_add_smul_one (hF.add hy.1)]
  rw [lintegral_congr_ae hcongr,
    BlockBand.Palm.lintegral_dependentScalarShift_eq_kernel μ0 hc' hN.ne' hν hΦ]
  refine lintegral_congr fun E => ?_
  have hfP : Measurable fun A0 : Matrix (Fin N) (Fin N) ℂ =>
      ENNReal.ofReal (palmWeight F c E ℓ A0) * 1 :=
    (ENNReal.measurable_ofReal.comp (measurable_palmWeight F c E ℓ)).mul measurable_const
  show _ = (∫⁻ A0, ENNReal.ofReal (palmWeight F c E ℓ A0) * 1 ∂freshTracelessLaw N c) * h E
  rw [← lintegral_mul_const _ hfP]
  refine lintegral_congr fun A0 => ?_
  simp only [Φ, ν, BlockBand.Palm.scalarWeightENN_eq_ofReal]
  unfold palmWeight
  ring

theorem measurable_meanDensity (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) :
    Measurable (meanDensity F c) :=
  measurable_const.mul (Finset.measurable_sum _ fun ℓ _ => measurable_rankDensity F c ℓ)

/-- **The mean measure has the canonical density.** For `N ≥ 1`, Hermitian `F`, `c > 0`:
`freshMeanEigenvalueMeasure N c F = volume.withDensity (meanDensity F c)`. -/
theorem freshMeanEigenvalueMeasure_eq_withDensity (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {c : ℝ} (hc : 0 < c) :
    freshMeanEigenvalueMeasure N c F = volume.withDensity (meanDensity F c) := by
  unfold freshMeanEigenvalueMeasure
  simp_rw [map_freshEigenvalue_eq_withDensity hN hF hc]
  refine Measure.ext_of_lintegral _ fun h hh => ?_
  rw [lintegral_smul_measure, lintegral_finsetSum_measure,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_meanDensity F c) hh]
  simp_rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_rankDensity F c _) hh]
  have hsplit : (fun y => (meanDensity F c * h) y) =
      fun y => (N : ℝ≥0∞)⁻¹ * ∑ ℓ : Fin N, (rankDensity F c ℓ * h) y := by
    funext y
    simp only [Pi.mul_apply, meanDensity, Finset.sum_mul, mul_assoc]
  rw [hsplit, lintegral_const_mul _ (Finset.measurable_sum _ fun ℓ _ =>
      (measurable_rankDensity F c ℓ).mul hh),
    lintegral_finsetSum _ fun ℓ _ => (measurable_rankDensity F c ℓ).mul hh, smul_eq_mul]

theorem continuous_meanDensity (hN : 0 < N) (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) :
    Continuous (meanDensity F c) :=
  (ENNReal.continuous_const_mul (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 hN.ne'))).comp
    (continuous_finsetSum _ fun ℓ _ => continuous_rankDensity F c ℓ)

theorem meanDensity_le (hN : 0 < N) (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (E : ℝ) :
    meanDensity F c E ≤ ENNReal.ofReal (densityBound c N) := by
  unfold meanDensity
  have h0 : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hsum : ∑ ℓ : Fin N, rankDensity F c ℓ E ≤
      (N : ℝ≥0∞) * ENNReal.ofReal (densityBound c N) := by
    calc ∑ ℓ : Fin N, rankDensity F c ℓ E ≤ ∑ _ℓ : Fin N, ENNReal.ofReal (densityBound c N) :=
          Finset.sum_le_sum fun ℓ _ => rankDensity_le F c ℓ E
      _ = (N : ℝ≥0∞) * ENNReal.ofReal (densityBound c N) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc (N : ℝ≥0∞)⁻¹ * ∑ ℓ : Fin N, rankDensity F c ℓ E
      ≤ (N : ℝ≥0∞)⁻¹ * ((N : ℝ≥0∞) * ENNReal.ofReal (densityBound c N)) := by gcongr
    _ = ENNReal.ofReal (densityBound c N) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top N), one_mul]

theorem meanDensity_ne_top (hN : 0 < N) (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (E : ℝ) :
    meanDensity F c E ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (meanDensity_le hN F c E)

theorem meanDensity_pos (hN : 0 < N) (F : Matrix (Fin N) (Fin N) ℂ) {c : ℝ} (hc : 0 < c)
    (E : ℝ) : 0 < meanDensity F c E := by
  unfold meanDensity
  refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top N)) ?_
  have h1 : rankDensity F c ⟨0, hN⟩ E ≤ ∑ ℓ : Fin N, rankDensity F c ℓ E :=
    Finset.single_le_sum (f := fun ℓ => rankDensity F c ℓ E) (fun _ _ => zero_le)
      (Finset.mem_univ _)
  exact (lt_of_lt_of_le (rankDensity_pos hN F hc _ E) h1).ne'

/-- Real version of the canonical density: continuous, `= meanDensity` after `ofReal`. -/
def meanDensityReal (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (E : ℝ) : ℝ :=
  (meanDensity F c E).toReal

theorem continuous_meanDensityReal (hN : 0 < N) (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) :
    Continuous (meanDensityReal F c) :=
  ENNReal.continuousOn_toReal.comp_continuous (continuous_meanDensity hN F c)
    (fun E => meanDensity_ne_top hN F c E)

theorem ofReal_meanDensityReal (hN : 0 < N) (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (E : ℝ) :
    ENNReal.ofReal (meanDensityReal F c E) = meanDensity F c E :=
  ENNReal.ofReal_toReal (meanDensity_ne_top hN F c E)

/-- Two continuous Lebesgue densities of the same measure on `ℝ` coincide everywhere. -/
theorem eq_of_withDensity_eq_of_continuous {f g : ℝ → ℝ≥0∞} (hf : Continuous f)
    (hg : Continuous g) (h : volume.withDensity f = volume.withDensity g) : f = g :=
  (Continuous.ae_eq_iff_eq volume hf hg).1
    ((withDensity_eq_iff_of_sigmaFinite hf.measurable.aemeasurable
      hg.measurable.aemeasurable).1 h)

/-- **Every continuous density is the canonical one.** For `N ≥ 1`, Hermitian `F`, `c > 0`
and every continuous `ρ` with `freshMeanEigenvalueMeasure N c F = volume.withDensity
(ofReal ∘ ρ)`: `ρ E = meanDensityReal F c E` for every `E` (both are positive). -/
theorem apply_eq_meanDensityReal (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {c : ℝ} (hc : 0 < c) {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hμ : freshMeanEigenvalueMeasure N c F =
      volume.withDensity (fun y => ENNReal.ofReal (ρ y))) (E : ℝ) :
    ρ E = meanDensityReal F c E := by
  have h := eq_of_withDensity_eq_of_continuous (ENNReal.continuous_ofReal.comp hρ)
    (continuous_meanDensity hN F c)
    (hμ.symm.trans (freshMeanEigenvalueMeasure_eq_withDensity hN hF hc))
  have hE : ENNReal.ofReal (ρ E) = meanDensity F c E := congrFun h E
  have hpos : 0 < ρ E := by
    have := meanDensity_pos hN F hc E
    rw [← hE, ENNReal.ofReal_pos] at this
    exact this
  unfold meanDensityReal
  rw [← hE, ENNReal.toReal_ofReal hpos.le]

theorem meanDensityReal_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (E : ℝ) :
    0 ≤ meanDensityReal F c E :=
  ENNReal.toReal_nonneg

theorem meanDensityReal_le (hN : 0 < N) (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (E : ℝ) :
    meanDensityReal F c E ≤ densityBound c N := by
  have h0 : 0 ≤ densityBound c N := inv_nonneg.2 (Real.sqrt_nonneg _)
  unfold meanDensityReal
  exact (ENNReal.toReal_le_toReal (meanDensity_ne_top hN F c E) ENNReal.ofReal_ne_top).2
    (meanDensity_le hN F c E) |>.trans_eq (ENNReal.toReal_ofReal h0)

end BlockBand.Critical.PointDensity
