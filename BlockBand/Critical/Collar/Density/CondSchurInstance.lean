module

public import BlockBand.Critical.Collar.Density.CondSchurSides

/-!
# Conditional Schur identity for one collar instance

`collarConditionalDensity_eq_of_ae_generic` proves the conditional Schur identity for one collar
instance (fixed `W`, `b < 1/2`, real `e`, Hermitian `X`, interval `[a₁, a₂]`), assuming that the
pair `(D, B)` is almost surely generic: no eigenvector of `D = A - e - X` lies in `ker B*`.
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

/-- **The conditional Schur identity for one collar instance**, from almost-sure genericity of
`(D, B)` (no eigenvector of `D = A - e - X` in `ker B*`). -/
theorem collarConditionalDensity_eq_of_ae_generic (hW : 0 < W) {b : ℝ} (hb : b < 1 / 2)
    (e : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) {a₁ a₂ : ℝ}
    (ha : a₁ ≤ a₂) (u : Fin 2 × Fin W → ℂ)
    (hgen : ∀ᵐ ω₁ ∂layerLaw W b .common,
      CsGeneric (collarTopBlock e X ω₁) (bondMatrix .common ω₁.2)) :
    ENNReal.ofReal (quadForm (collarTopProjector W b e X (Set.Icc a₁ a₂)) u) =
      ∫⁻ x in Set.Icc a₁ a₂, ∫⁻ ω, ENNReal.ofReal (quadForm (condCollarDensity b (e + x) X ω) u)
        ∂layerLaw W b .common := by
  set σ := BlockBand.Palm.scalarVariance (Real.toNNReal (1 - 2 * b)) W
  have hc : 0 < 1 - 2 * b := by linarith
  have hσ : σ ≠ 0 := BlockBand.Palm.scalarVariance_ne_zero
    (Real.toNNReal_pos.2 hc).ne' hW.ne'
  have hcard : 0 < Fintype.card (PortSite W .common) := by rw [card_portSite_common]; exact hW
  rw [ofReal_quadForm_collarTopProjector_eq e hX a₁ a₂ u,
    lintegral_condCollarDensity_eq hW hb e hX a₁ a₂ u]
  refine lintegral_congr_ae ?_
  filter_upwards [hgen, BlockBand.Layers.lct_ae_blocks_isHermitian W b .common] with ω₁ hg hA
  set D := collarTopBlock e X ω₁
  set Bm := bondMatrix .common ω₁.2
  have hD : D.IsHermitian := collarTopBlock_isHermitian e hX hA
  have hmeas1 : Measurable fun G => csTopRaw e X a₁ a₂ u (ω₁, G) :=
    (measurable_csTopRaw e X a₁ a₂ u).comp measurable_prodMk_left
  rw [lintegral_gue_scalarSplit (PortSite W .common) hcard _ σ
    (scalarVariance_eq_div_card hb hW) hmeas1]
  have hK : Measurable fun G0 : Matrix (PortSite W .common) (PortSite W .common) ℂ =>
      ∫⁻ ζ, csTopRaw e X a₁ a₂ u (ω₁, G0 + (ζ : ℂ) • 1) ∂gaussianReal 0 σ := by
    have h2 : Measurable fun q : Matrix (PortSite W .common) (PortSite W .common) ℂ × ℝ =>
        csTopRaw e X a₁ a₂ u (ω₁, q.1 + (q.2 : ℂ) • 1) :=
      hmeas1.comp measurable_scalarAdd
    exact h2.lintegral_prod_right'
  rw [lintegral_gue_port_traceless (1 - 2 * b) hK]
  refine lintegral_congr_ae ?_
  filter_upwards [BlockBand.Coarea.FreshPalm.ae_freshTracelessLaw hW (1 - 2 * b)] with A0 hA0
  set G0 := A0.submatrix (portEquiv W) (portEquiv W)
  have hG : (G0 - (e : ℂ) • (1 : Matrix (PortSite W .common) (PortSite W .common) ℂ)).IsHermitian :=
    (hA0.1.submatrix _).sub (isHermitian_one.smul (Complex.conj_ofReal e))
  have hL : ∀ ζ : ℝ, csTopRaw e X a₁ a₂ u (ω₁, G0 + (ζ : ℂ) • 1) =
      ENNReal.ofReal (csTop D Bm (G0 - (e : ℂ) • 1) a₁ a₂ u ζ) := by
    intro ζ
    rw [csTopRaw, collarMatrix_eq_csPencil, rawCfc_eq_cfc (csPencil_isHermitian hD hG ζ)]
    rfl
  simp_rw [hL]
  rw [lintegral_gaussian_csTop hD hG hg u hσ ha]
  refine lintegral_congr fun x => ?_
  have hF : (collarFW (e + x) X ω₁ + A0).IsHermitian :=
    (collarFW_isHermitian (e + x) hX hA).add hA0.1
  rw [csPsi, rawCfc_eq_cfc hF, quadForm_cfc_collarFW_eq e x ω₁ hD hA0.1]

end BlockBand.Critical.Collar.Density
