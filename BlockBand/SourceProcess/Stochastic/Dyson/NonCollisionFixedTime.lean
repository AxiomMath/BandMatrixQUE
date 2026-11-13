module

public import BlockBand.SourceProcess.Stochastic.Dyson.NonCollisionDisc

/-!
# Non-collision at a fixed time

* `gueIncrementLaw_not_simple`: for Hermitian `F₀` and `δ > 0`,
  `GUE(δ){K | F₀ + K has a repeated eigenvalue} = 0` (the bad set is contained in the zero set of
  the nonzero polynomial `discPoly N F₀`, null for the product Gaussian measure);
* `simple_fixedTime`: if `G` is a Hermitian Brownian motion for `𝓖` and `F` is `𝓖_0`-measurable
  Hermitian, then for every fixed `t > 0`, a.s. `F + G_t` has simple spectrum (independence of
  `F` and `G_t - G_0`, Fubini).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal
open BlockBand.Internal.Contracts.Transmission

attribute [local instance] secondCountableTopology_matrix

variable {N : ℕ}

theorem measurableSet_not_simple_add (F₀ : Matrix (Fin N) (Fin N) ℂ) :
    MeasurableSet {K : Matrix (Fin N) (Fin N) ℂ | ¬ HasSimpleSpectrum N (F₀ + K)} :=
  ((isOpen_hasSimpleSpectrum (N := N)).preimage
    (continuous_const.add continuous_id)).measurableSet.compl

/-- The GUE increment law does not charge the non-simple set translated by a Hermitian `F₀`. -/
theorem gueIncrementLaw_not_simple {F₀ : Matrix (Fin N) (Fin N) ℂ} (hF₀ : F₀.IsHermitian)
    {δ : ℝ≥0} (hδ : δ ≠ 0) :
    gueIncrementLaw N δ {K | ¬ HasSimpleSpectrum N (F₀ + K)} = 0 := by
  rw [gueIncrementLaw, Measure.map_apply measurable_hermitianOfCoords
    (measurableSet_not_simple_add F₀)]
  have := nullSingletonClass_gaussianReal (μ := 0) hδ
  refine measure_mono_null (fun r hr => ?_) (pi_evalZero_eq_zero (discPoly_ne_zero hF₀))
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hr ⊢
  rw [evalR_discPoly]
  exact traceDisc_eq_zero_of_not_simple (hF₀.add (hermitianOfCoords_isHermitian r)) hr

theorem measurableSet_isHermitian :
    MeasurableSet {K : Matrix (Fin N) (Fin N) ℂ | K.IsHermitian} :=
  (isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id).measurableSet

/-- **Fixed-time simple spectrum.** -/
theorem simple_fixedTime {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}
    (hG : IsHermitianBrownian Q 𝓖 N G) (hF : Measurable[𝓖 0] F) (hFh : ∀ ω, (F ω).IsHermitian)
    {t : ℝ≥0} (ht : 0 < t) : ∀ᵐ ω ∂Q, HasSimpleSpectrum N (F ω + G t ω) := by
  set X : Ω → Matrix (Fin N) (Fin N) ℂ := fun ω => G t ω - G 0 ω with hXdef
  have hXG : ∀ ω, X ω = G t ω := fun ω => by simp [X, hG.zero ω]
  have hFm : Measurable F := hF.mono (𝓖.le 0) le_rfl
  have hXm : Measurable X := ((hG.adapted t).mono (𝓖.le t) le_rfl).sub
    ((hG.adapted 0).mono (𝓖.le 0) le_rfl)
  have hind : IndepFun X F Q := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (hG.indep 0 t zero_le) (MeasurableSpace.comap_le_iff_le_map.mpr hF)
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hFm.aemeasurable).mp hind
  have hlaw : Q.map X = gueIncrementLaw N t := by
    simpa using (hG.law 0 t zero_le).map_eq
  set S : Set (Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) :=
    {p | ¬ HasSimpleSpectrum N (p.2 + p.1)}
  have hS : MeasurableSet S :=
    ((isOpen_hasSimpleSpectrum (N := N)).preimage
      (continuous_snd.add continuous_fst)).measurableSet.compl
  rw [ae_iff]
  have hset : {ω | ¬ HasSimpleSpectrum N (F ω + G t ω)} = (fun ω => (X ω, F ω)) ⁻¹' S := by
    ext ω; simp [S, hXG]
  rw [hset, ← Measure.map_apply (hXm.prodMk hFm) hS, hmap, Measure.prod_apply_symm hS, hlaw]
  have hH : ∀ᵐ y ∂(Q.map F), y.IsHermitian :=
    (ae_map_iff hFm.aemeasurable measurableSet_isHermitian).mpr (Filter.Eventually.of_forall hFh)
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hH] with y hy
  exact gueIncrementLaw_not_simple hy ht.ne'

end BlockBand.SourceProcess.Stochastic.Dyson
