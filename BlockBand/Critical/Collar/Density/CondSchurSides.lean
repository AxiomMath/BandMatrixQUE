module

public import BlockBand.Critical.Collar.Density.CondSchurCollarMeas

/-!
# Conditional Schur identity: Sides

Part of the proof of the conditional Schur identity in the collar density lemma: the top
density, averaged first over `G`, is exactly `TΣ_F(0)T*`.

The two sides of the identity as iterated integrals over `(A, B)` and the traceless middle
block: `ofReal_quadForm_collarTopProjector_eq`, `lintegral_gue_port_traceless`,
`lintegral_condCollarDensity_eq`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix MeasureTheory Filter Topology ProbabilityTheory
open BlockBand.Foundations.Spectral BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Coarea.GUELaw BlockBand.Coarea.PoleExclusion
open scoped ComplexConjugate ComplexOrder ENNReal NNReal

variable {W : ℕ}

attribute [local instance] matrix_secondCountableTopology_gen

/-!
## The top side
-/

theorem norm_cfc_indicator_apply_le {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (I : Set ℝ) (a c : ι) :
    ‖cfc (I.indicator (1 : ℝ → ℝ)) H a c‖ ≤ Fintype.card ι * 1 := by
  rw [cfc_eq_specSum hH]
  refine norm_specSum_apply_le hH (fun l => ?_) a c
  rw [Complex.norm_real]
  by_cases hl : l ∈ I
  · simp [Set.indicator_of_mem hl]
  · simp [Set.indicator_of_notMem hl]

theorem ofReal_quadForm_collarTopProjector_eq {b : ℝ} (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (a₁ a₂ : ℝ)
    (u : Fin 2 × Fin W → ℂ) :
    ENNReal.ofReal (quadForm (collarTopProjector W b e X (Set.Icc a₁ a₂)) u) =
      ∫⁻ ω₁, ∫⁻ G, csTopRaw e X a₁ a₂ u (ω₁, G)
        ∂gueMeasure (PortSite W .common) (Real.toNNReal ((1 - 2 * b) / W)) ∂layerLaw W b .common := by
  have hH := ae_collarMatrix_isHermitian (W := W) b e hX
  set f₁ := (Set.Icc a₁ a₂).indicator (1 : ℝ → ℝ)
  have hf₁ : Measurable f₁ := measurable_const.indicator measurableSet_Icc
  have hent : ∀ i j, Integrable (fun ω => (cfc f₁ (collarMatrix e X ω)).toBlocks₁₁ i j)
      (collarLaw W b) := by
    intro i j
    refine Integrable.of_bound (aestronglyMeasurable_cfc_apply (measurable_collarMatrix e X)
      (hH.mono fun _ h => h.1) hf₁ (Sum.inl i) (Sum.inl j))
      (Fintype.card (LayerSite W .common) * 1) ?_
    filter_upwards [hH] with ω hω
    exact norm_cfc_indicator_apply_le hω.1 _ _ _
  have hq := integral_quadForm hent u
  have hqi : Integrable (fun ω => quadForm ((cfc f₁ (collarMatrix e X ω)).toBlocks₁₁) u)
      (collarLaw W b) := (integrable_star_dotProduct_mulVec hent u).re
  have hnn : ∀ᵐ ω ∂collarLaw W b, 0 ≤ quadForm ((cfc f₁ (collarMatrix e X ω)).toBlocks₁₁) u := by
    filter_upwards [hH] with ω hω
    rw [quadForm_cfc_toBlocks11 hω.1]
    refine Finset.sum_nonneg fun r _ => mul_nonneg ?_ (sq_nonneg _)
    by_cases hl : increasingEigenvalue hω.1 r ∈ Set.Icc a₁ a₂
    · simp [f₁, Set.indicator_of_mem hl]
    · simp [f₁, Set.indicator_of_notMem hl]
  have hdef : collarTopProjector W b e X (Set.Icc a₁ a₂) =
      matrixExpect (collarLaw W b) fun ω => (cfc f₁ (collarMatrix e X ω)).toBlocks₁₁ := rfl
  rw [hdef, ← hq, ofReal_integral_eq_lintegral_ofReal hqi hnn]
  have hae : (fun ω => ENNReal.ofReal (quadForm ((cfc f₁ (collarMatrix e X ω)).toBlocks₁₁) u)) =ᵐ[collarLaw W b]
      csTopRaw e X a₁ a₂ u := by
    filter_upwards [hH] with ω hω
    rw [csTopRaw, rawCfc_eq_cfc hω.1]
  rw [lintegral_congr_ae hae, collarLaw,
    lintegral_prod _ (measurable_csTopRaw e X a₁ a₂ u).aemeasurable]

theorem lintegral_gue_port_traceless (c : ℝ)
    {K : Matrix (PortSite W .common) (PortSite W .common) ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ G, K (tracelessPart G) ∂gueMeasure (PortSite W .common) (Real.toNNReal (c / W)) =
      ∫⁻ A0, K (A0.submatrix (portEquiv W) (portEquiv W)) ∂freshTracelessLaw W c := by
  have hR : Measurable (Matrix.reindex (portEquiv W).symm (portEquiv W).symm :
      Matrix (Fin W) (Fin W) ℂ → Matrix (PortSite W .common) (PortSite W .common) ℂ) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  rw [← gueMeasure_map_reindex (portEquiv W).symm (Real.toNNReal (c / W)),
    lintegral_map (f := fun G => K (tracelessPart G)) (hK.comp measurable_tracelessPart) hR,
    freshTracelessLaw, lintegral_map (f := fun A : Matrix (Fin W) (Fin W) ℂ =>
      K (A.submatrix (portEquiv W) (portEquiv W))) (hK.comp hR) measurable_tracelessPart]
  refine lintegral_congr fun G => ?_
  rw [tracelessPart_reindex]
  rfl

theorem scalarVariance_eq_div_card {b : ℝ} (hb : b < 1 / 2) (hW : 0 < W) :
    ((BlockBand.Palm.scalarVariance (Real.toNNReal (1 - 2 * b)) W : ℝ≥0) : ℝ) =
      (Real.toNNReal ((1 - 2 * b) / W) : ℝ) / Fintype.card (PortSite W .common) := by
  have hc : 0 < 1 - 2 * b := by linarith
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  rw [BlockBand.Palm.coe_scalarVariance, Real.coe_toNNReal _ hc.le,
    Real.coe_toNNReal _ (div_pos hc hWr).le, card_portSite_common]
  field_simp

/-!
## The conditional side
-/

theorem lintegral_condCollarDensity_eq (hW : 0 < W) {b : ℝ} (hb : b < 1 / 2) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (a₁ a₂ : ℝ)
    (u : Fin 2 × Fin W → ℂ) :
    ∫⁻ x in Set.Icc a₁ a₂, ∫⁻ ω₁, ENNReal.ofReal (quadForm (condCollarDensity b (e + x) X ω₁) u)
        ∂layerLaw W b .common =
      ∫⁻ ω₁, (∫⁻ A0, (∫⁻ x in Set.Icc a₁ a₂,
        csPsi (BlockBand.Palm.scalarVariance (Real.toNNReal (1 - 2 * b)) W) e X u ((x, ω₁), A0))
          ∂freshTracelessLaw W (1 - 2 * b)) ∂layerLaw W b .common := by
  have := BlockBand.Layers.bond_isProbabilityMeasure_layerLaw W b .common
  set σ := BlockBand.Palm.scalarVariance (Real.toNNReal (1 - 2 * b)) W
  have hc : 0 < 1 - 2 * b := by linarith
  have h1 : ∀ x : ℝ, ∫⁻ ω₁, ENNReal.ofReal (quadForm (condCollarDensity b (e + x) X ω₁) u)
      ∂layerLaw W b .common = ∫⁻ ω₁, ∫⁻ A0, csPsi σ e X u ((x, ω₁), A0)
        ∂freshTracelessLaw W (1 - 2 * b) ∂layerLaw W b .common := by
    intro x
    refine lintegral_congr_ae ?_
    filter_upwards [BlockBand.Layers.lct_ae_blocks_isHermitian W b .common] with ω₁ hA
    rw [quadForm_condCollarDensity_eq, ofReal_quadForm_sigma_eq_lintegral_rawCfc hW
      (collarFW_isHermitian (e + x) hX hA) hc]
    rfl
  simp_rw [h1]
  have hm := (measurable_csPsi σ e X u).lintegral_prod_right'
    (ν := freshTracelessLaw W (1 - 2 * b))
  rw [lintegral_lintegral_swap (μ := volume.restrict (Set.Icc a₁ a₂))
    (ν := layerLaw W b .common)
    (f := fun x ω₁ => ∫⁻ A0, csPsi σ e X u ((x, ω₁), A0) ∂freshTracelessLaw W (1 - 2 * b))
    hm.aemeasurable]
  refine lintegral_congr fun ω₁ => ?_
  have hm2 : Measurable fun q : ℝ × Matrix (Fin W) (Fin W) ℂ => csPsi σ e X u ((q.1, ω₁), q.2) :=
    (measurable_csPsi σ e X u).comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  exact lintegral_lintegral_swap hm2.aemeasurable

end BlockBand.Critical.Collar.Density
