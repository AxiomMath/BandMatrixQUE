module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCanonicalSelectedFormula

/-!
# Parameter assembly for the PSSS first Minami reduction

After conditioning on the exterior sample of one block, the energy integral of the weighted
regulated selected trace equals an iterated `(e, t, ξ)` integral of the auxiliary selected-block
eigenvalue count. The identity holds pointwise in the exterior and selected samples and is then
summed over the blocks.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- The auxiliary count integrand for one canonical selected block. -/
def canonicalSelectedAuxiliaryCountIntegrand
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (Gj : BlockProductDisintegration.SelectedSample dims j)
    (e : ℝ) {eta : ℝ} (heta : 0 < eta)
    (w : ℝ≥0∞) (t xi : ℝ) : ℝ≥0∞ :=
  w *
    ((eigenCount
        (addHermitian
          (publicGUERealBackground
            (publicFrozenCanonicalHermitian A₀ j Gext e eta)
            (canonicalFrozenAbsorber
              (frozenSelectedA A₀ j Gext) (frozenSelectedB A₀ j Gext)
              (frozenSelectedC A₀ j Gext) (frozenSelectedD A₀ j Gext)
              e eta)
            (publicFrozenCanonicalAbsorber_posSemidef
              A₀ j Gext e heta) t)
          (Gj ⟨j, by simp⟩))
        (Ioo (-xi) xi) : ℝ≥0∞) *
      ENNReal.ofReal (poissonRadialWeight eta xi))

/-- Exact pointwise first-reduction equality in named-integrand form. -/
theorem weighted_selectedTrace_eq_auxiliaryCountAverage
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (Gj : BlockProductDisintegration.SelectedSample dims j)
    (e : ℝ) {eta : ℝ} (heta : 0 < eta)
    (w : ℝ≥0∞) (hw : w ≠ ⊤) :
    w * publicBlockRegulatedSelectedTrace A₀ j e eta
      ((BlockProductDisintegration.split dims j).symm (Gext, Gj)) =
      ∫⁻ t : ℝ, ENNReal.ofReal (standardCauchyWeight t) *
        (∫⁻ xi : ℝ in Ioi 0,
          canonicalSelectedAuxiliaryCountIntegrand
            A₀ j Gext Gj e heta w t xi) := by
  exact publicBlockRegulatedSelectedTrace_weighted_count_formula
    A₀ j Gext Gj e heta w hw

/-- **Energy-parameter first reduction.**  The normalized regulated selected trace integrated
over a half-open energy interval `Ioc a b` equals its canonical `(e, t, ξ)` auxiliary-count
integral.  The finite weight `w e` may depend on the exterior sample, the selected sample and
the energy. -/
theorem energyLIntegral_weighted_selectedTrace_eq_auxiliaryCount
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (Gj : BlockProductDisintegration.SelectedSample dims j)
    {a b eta : ℝ} (heta : 0 < eta)
    (w : ℝ → ℝ≥0∞) (hw : ∀ e, w e ≠ ⊤) :
    (∫⁻ e : ℝ in Ioc a b,
      (ENNReal.ofReal (1 / Real.pi) * w e) *
        publicBlockRegulatedSelectedTrace A₀ j e eta
          ((BlockProductDisintegration.split dims j).symm (Gext, Gj))) =
      ∫⁻ e : ℝ in Ioc a b, ∫⁻ t : ℝ,
        ENNReal.ofReal (standardCauchyWeight t) *
          (∫⁻ xi : ℝ in Ioi 0,
            canonicalSelectedAuxiliaryCountIntegrand
              A₀ j Gext Gj e heta
              (ENNReal.ofReal (1 / Real.pi) * w e) t xi) := by
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro e he
  exact weighted_selectedTrace_eq_auxiliaryCountAverage
    A₀ j Gext Gj e heta (ENNReal.ofReal (1 / Real.pi) * w e)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hw e))

/-- The first-reduction identity integrated over the exterior and selected samples of the product
disintegration. No Tonelli exchange is used: the same sample-dependent finite weight occurs on
both sides, pointwise before the three parameter integrations. -/
theorem iterated_weighted_selectedTrace_eq_auxiliaryCount
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {a b eta : ℝ} (heta : 0 < eta)
    (w : BlockProductDisintegration.ExteriorSample dims j →
      BlockProductDisintegration.SelectedSample dims j → ℝ → ℝ≥0∞)
    (hw : ∀ Gext Gj e, w Gext Gj e ≠ ⊤) :
    (∫⁻ (Gext : BlockProductDisintegration.ExteriorSample dims j),
      (∫⁻ (Gj : BlockProductDisintegration.SelectedSample dims j),
        (∫⁻ e : ℝ in Ioc a b,
          (ENNReal.ofReal (1 / Real.pi) * w Gext Gj e) *
            publicBlockRegulatedSelectedTrace A₀ j e eta
              ((BlockProductDisintegration.split dims j).symm (Gext, Gj)))
        ∂BlockProductDisintegration.selectedMeasure dims hd j)
      ∂BlockProductDisintegration.exteriorMeasure dims hd j) =
    ∫⁻ (Gext : BlockProductDisintegration.ExteriorSample dims j),
      (∫⁻ (Gj : BlockProductDisintegration.SelectedSample dims j),
        (∫⁻ e : ℝ in Ioc a b, ∫⁻ t : ℝ,
          ENNReal.ofReal (standardCauchyWeight t) *
            (∫⁻ xi : ℝ in Ioi 0,
              canonicalSelectedAuxiliaryCountIntegrand
                A₀ j Gext Gj e heta
                (ENNReal.ofReal (1 / Real.pi) * w Gext Gj e) t xi))
        ∂BlockProductDisintegration.selectedMeasure dims hd j)
      ∂BlockProductDisintegration.exteriorMeasure dims hd j := by
  apply lintegral_congr
  intro Gext
  apply lintegral_congr
  intro Gj
  exact energyLIntegral_weighted_selectedTrace_eq_auxiliaryCount
    A₀ j Gext Gj heta (w Gext Gj) (hw Gext Gj)

/-- Sum over blocks of the selected first-reduction identities. Each block keeps its own pointwise
finite weight. -/
theorem sum_iterated_weighted_selectedTrace_eq_auxiliaryCount
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {a b eta : ℝ} (heta : 0 < eta)
    (w : ∀ j : Fin k,
      BlockProductDisintegration.ExteriorSample dims j →
      BlockProductDisintegration.SelectedSample dims j → ℝ → ℝ≥0∞)
    (hw : ∀ j Gext Gj e, w j Gext Gj e ≠ ⊤) :
    (∑ j : Fin k,
      ∫⁻ (Gext : BlockProductDisintegration.ExteriorSample dims j),
        (∫⁻ (Gj : BlockProductDisintegration.SelectedSample dims j),
          (∫⁻ e : ℝ in Ioc a b,
            (ENNReal.ofReal (1 / Real.pi) * w j Gext Gj e) *
              publicBlockRegulatedSelectedTrace A₀ j e eta
                ((BlockProductDisintegration.split dims j).symm (Gext, Gj)))
          ∂BlockProductDisintegration.selectedMeasure dims hd j)
        ∂BlockProductDisintegration.exteriorMeasure dims hd j) =
    ∑ j : Fin k,
      ∫⁻ (Gext : BlockProductDisintegration.ExteriorSample dims j),
        (∫⁻ (Gj : BlockProductDisintegration.SelectedSample dims j),
          (∫⁻ e : ℝ in Ioc a b, ∫⁻ t : ℝ,
            ENNReal.ofReal (standardCauchyWeight t) *
              (∫⁻ xi : ℝ in Ioi 0,
                canonicalSelectedAuxiliaryCountIntegrand
                  A₀ j Gext Gj e heta
                  (ENNReal.ofReal (1 / Real.pi) * w j Gext Gj e) t xi))
          ∂BlockProductDisintegration.selectedMeasure dims hd j)
        ∂BlockProductDisintegration.exteriorMeasure dims hd j := by
  apply Finset.sum_congr rfl
  intro j hj
  exact iterated_weighted_selectedTrace_eq_auxiliaryCount
    dims hd A₀ j heta (w j) (hw j)

end PSSSNative.BlockBand.PSSS
