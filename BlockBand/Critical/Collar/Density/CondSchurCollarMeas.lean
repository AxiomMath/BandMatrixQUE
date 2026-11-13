module

public import BlockBand.Critical.Collar.Density.CondSchurCollar
public import BlockBand.Critical.Collar.Density.CondSchurGeneric

/-!
# Conditional Schur identity: measurability

Measurability, on the layer sample, of the Schur complement `F_{e+x}`, of the vector `T_{e+x}*u`
and of the integrands defined through the raw functional calculus, as needed to apply Fubini in
the conditional Schur identity for the collar.
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

/-!
## Measurability on the layer sample
-/

attribute [local instance] matrix_secondCountableTopology_gen

theorem continuous_collarTopBlock_energy (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Continuous fun p : ℝ × LayerSample W .common => collarTopBlock (e + p.1) X p.2 := by
  unfold collarTopBlock
  refine ((continuous_blockDiag_gen.comp (continuous_fst.comp continuous_snd)).sub ?_).sub
    continuous_const
  exact (Complex.continuous_ofReal.comp (continuous_const.add continuous_fst)).smul
    continuous_const

theorem measurable_inv_collarTopBlock_energy (e : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable fun p : ℝ × LayerSample W .common => (collarTopBlock (e + p.1) X p.2)⁻¹ := by
  have h := measurable_matrix_inv_cs.comp (continuous_collarTopBlock_energy e X).measurable
  exact h

theorem measurable_collarFW_energy (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable fun p : ℝ × LayerSample W .common => collarFW (e + p.1) X p.2 := by
  have hB : Continuous fun p : ℝ × LayerSample W .common => bondMatrix .common p.2.2 :=
    continuous_bondMatrix_gen.comp (continuous_snd.comp continuous_snd)
  have hc : Continuous fun q : (ℝ × Matrix (Fin 2 × Fin W) (Fin 1 × Fin W) ℂ) ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
      (-(((e + q.1.1 : ℝ) : ℂ) • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)) -
        q.1.2ᴴ * q.2 * q.1.2).submatrix (portEquiv W).symm (portEquiv W).symm := by
    refine Continuous.matrix_submatrix ?_ _ _
    refine (((Complex.continuous_ofReal.comp (continuous_const.add
      (continuous_fst.comp continuous_fst))).smul continuous_const).neg).sub ?_
    exact ((continuous_snd.comp continuous_fst).matrix_conjTranspose.matrix_mul
      continuous_snd).matrix_mul (continuous_snd.comp continuous_fst)
  have h := hc.measurable.comp (((measurable_fst.prodMk hB.measurable)).prodMk
    (measurable_inv_collarTopBlock_energy e X))
  exact h

theorem measurable_collarTW_conj_mulVec (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (u : Fin 2 × Fin W → ℂ) :
    Measurable fun p : ℝ × LayerSample W .common => (collarTW (e + p.1) X p.2)ᴴ *ᵥ u := by
  have hB : Continuous fun p : ℝ × LayerSample W .common => bondMatrix .common p.2.2 :=
    continuous_bondMatrix_gen.comp (continuous_snd.comp continuous_snd)
  have hc : Continuous fun q : Matrix (Fin 2 × Fin W) (Fin 1 × Fin W) ℂ ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
      ((-(q.2 * q.1)).submatrix id (portEquiv W).symm)ᴴ *ᵥ u := by
    refine Continuous.matrix_mulVec ?_ continuous_const
    exact ((continuous_snd.matrix_mul continuous_fst).neg.matrix_submatrix _ _).matrix_conjTranspose
  have h := hc.measurable.comp (hB.measurable.prodMk (measurable_inv_collarTopBlock_energy e X))
  exact h

/-- The measurable integrand `Ψ(x, ω₁, A⁰) = y'* φ(-(F_x + A⁰)) y'` (raw functional calculus). -/
def csPsi (σ : ℝ≥0) (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (u : Fin 2 × Fin W → ℂ) (q : (ℝ × LayerSample W .common) × Matrix (Fin W) (Fin W) ℂ) :
    ℝ≥0∞ :=
  ENNReal.ofReal (quadForm (rawCfc (fun l => gaussianPDFReal 0 σ (-l))
    (collarFW (e + q.1.1) X q.1.2 + q.2)) ((collarTW (e + q.1.1) X q.1.2)ᴴ *ᵥ u))

theorem measurable_csPsi (σ : ℝ≥0) (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (u : Fin 2 × Fin W → ℂ) : Measurable (csPsi σ e X u) := by
  have hM : Measurable fun q : (ℝ × LayerSample W .common) × Matrix (Fin W) (Fin W) ℂ =>
      collarFW (e + q.1.1) X q.1.2 + q.2 :=
    ((measurable_collarFW_energy e X).comp measurable_fst).add measurable_snd
  have hf : Measurable fun l : ℝ => gaussianPDFReal 0 σ (-l) :=
    (measurable_gaussianPDFReal 0 σ).comp measurable_neg
  have hR : Measurable fun q : (ℝ × LayerSample W .common) × Matrix (Fin W) (Fin W) ℂ =>
      rawCfc (fun l => gaussianPDFReal 0 σ (-l)) (collarFW (e + q.1.1) X q.1.2 + q.2) :=
    measurable_matrix_of_entries fun i j => measurable_rawCfc_apply hM hf i j
  have hV : Measurable fun q : (ℝ × LayerSample W .common) × Matrix (Fin W) (Fin W) ℂ =>
      (collarTW (e + q.1.1) X q.1.2)ᴴ *ᵥ u :=
    (measurable_collarTW_conj_mulVec e X u).comp measurable_fst
  have h := ENNReal.measurable_ofReal.comp
    ((continuous_quadForm_pair (ι := Fin W)).measurable.comp (hR.prodMk hV))
  exact h

/-- The measurable top integrand `ω ↦ u*[1_I(ℋ_X)]₁₁u` (raw functional calculus). -/
def csTopRaw (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (a₁ a₂ : ℝ)
    (u : Fin 2 × Fin W → ℂ) (ω : CollarSample W) : ℝ≥0∞ :=
  ENNReal.ofReal (quadForm ((rawCfc ((Set.Icc a₁ a₂).indicator (1 : ℝ → ℝ))
    (collarMatrix e X ω)).toBlocks₁₁) u)

theorem measurable_csTopRaw (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (a₁ a₂ : ℝ) (u : Fin 2 × Fin W → ℂ) : Measurable (csTopRaw e X a₁ a₂ u) := by
  have hR : Measurable fun ω : CollarSample W => rawCfc ((Set.Icc a₁ a₂).indicator (1 : ℝ → ℝ))
      (collarMatrix e X ω) :=
    measurable_matrix_of_entries fun i j => measurable_rawCfc_apply (measurable_collarMatrix e X)
      (measurable_const.indicator measurableSet_Icc) i j
  have h := ENNReal.measurable_ofReal.comp
    ((continuous_quadForm_toBlocks11 (m := Fin 2 × Fin W) (n := PortSite W .common) u).measurable.comp hR)
  exact h

end BlockBand.Critical.Collar.Density
