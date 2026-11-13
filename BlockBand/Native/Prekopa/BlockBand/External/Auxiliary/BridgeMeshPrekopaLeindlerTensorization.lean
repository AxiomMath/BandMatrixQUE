module

public import BlockBand.Native.Prekopa.BlockBand.External.Auxiliary.BridgeMeshPrekopaLeindlerProof
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Tensorization of Prékopa–Leindler on finite bridge meshes

This module proves the product step for the three-function Prékopa–Leindler
inequality.  It uses only Tonelli/Fubini and Prékopa–Leindler on the two factors;
no marginal-convexity assumption occurs.

The scalar one-dimensional inequality is a hypothesis here (it is proved as
`scalarPrekopaLeindler`).  From it, the induction below gives every finite scalar product, including
both zero-dimensional cases, and hence every nested `r × m` bridge-mesh volume.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PrekopaNative.BlockBand

open MeasureTheory Set
open scoped ENNReal

/-- The three-function Prékopa–Leindler property for a measure on a real module. -/
def MeasurePrekopaLeindler
    (E : Type*) [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    (μ : Measure E) : Prop :=
  ∀ (f g h : E → ℝ≥0∞),
    Measurable f → Measurable g → Measurable h →
    ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
      (∀ x y, f x ^ a * g y ^ b ≤ h (a • x + b • y)) →
      (∫⁻ x, f x ∂μ) ^ a * (∫⁻ y, g y ∂μ) ^ b ≤ ∫⁻ z, h z ∂μ

/-- Prékopa–Leindler tensorizes across a product of `s`-finite measures.  The proof
first applies the second-factor inequality to every pair of outer coordinates, then
applies the first-factor inequality to the resulting measurable marginal functions.
Tonelli identifies all three iterated integrals with the product-measure integrals. -/
theorem measurePrekopaLeindler_prod
    {E F : Type*}
    [MeasurableSpace E] [MeasurableSpace F]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (μ : Measure E) (ν : Measure F) [SFinite μ] [SFinite ν]
    (hμ : MeasurePrekopaLeindler E μ)
    (hν : MeasurePrekopaLeindler F ν) :
    MeasurePrekopaLeindler (E × F) (μ.prod ν) := by
  intro f g h hf hg hh a b ha hb hab hpw
  let Fm : E → ℝ≥0∞ := fun x => ∫⁻ y, f (x, y) ∂ν
  let Gm : E → ℝ≥0∞ := fun x => ∫⁻ y, g (x, y) ∂ν
  let Hm : E → ℝ≥0∞ := fun x => ∫⁻ y, h (x, y) ∂ν
  have hFm : Measurable Fm := hf.lintegral_prod_right'
  have hGm : Measurable Gm := hg.lintegral_prod_right'
  have hHm : Measurable Hm := hh.lintegral_prod_right'
  have hpoint : ∀ x y, Fm x ^ a * Gm y ^ b ≤ Hm (a • x + b • y) := by
    intro x y
    have hfx : Measurable (fun z : F => f (x, z)) :=
      hf.comp (measurable_const.prodMk measurable_id)
    have hgy : Measurable (fun z : F => g (y, z)) :=
      hg.comp (measurable_const.prodMk measurable_id)
    have hhxy : Measurable (fun z : F => h (a • x + b • y, z)) :=
      hh.comp (measurable_const.prodMk measurable_id)
    apply hν (fun z => f (x, z)) (fun z => g (y, z))
      (fun z => h (a • x + b • y, z)) hfx hgy hhxy a b ha hb hab
    intro u v
    simpa [Prod.smul_mk, Prod.fst_add, Prod.snd_add] using hpw (x, u) (y, v)
  have hout := hμ Fm Gm Hm hFm hGm hHm a b ha hb hab hpoint
  rw [lintegral_prod f hf.aemeasurable, lintegral_prod g hg.aemeasurable,
    lintegral_prod h hh.aemeasurable]
  exact hout

/-- The scalar input is precisely the measure-level property for Lebesgue measure. -/
theorem measurePrekopaLeindler_real
    (hscalar : ScalarPrekopaLeindler) :
    MeasurePrekopaLeindler ℝ volume := hscalar

/-- Transport of Prékopa–Leindler along a measure-preserving measurable equivalence
which respects the real-module operations. -/
theorem MeasurePrekopaLeindler.map_measurableEquiv
    {E F : Type*}
    [MeasurableSpace E] [MeasurableSpace F]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {μ : Measure E} {ν : Measure F}
    (hE : MeasurePrekopaLeindler E μ)
    (e : E ≃ᵐ F) (he : MeasurePreserving e μ ν)
    (hadd : ∀ x y, e (x + y) = e x + e y)
    (hsmul : ∀ (c : ℝ) x, e (c • x) = c • e x) :
    MeasurePrekopaLeindler F ν := by
  intro f g h hf hg hh a b ha hb hab hpw
  have hi := hE (f ∘ e) (g ∘ e) (h ∘ e)
    (hf.comp e.measurable) (hg.comp e.measurable) (hh.comp e.measurable)
    a b ha hb hab
  have hpull : ∀ x y,
      (f ∘ e) x ^ a * (g ∘ e) y ^ b ≤ (h ∘ e) (a • x + b • y) := by
    intro x y
    simpa [Function.comp_apply, hadd, hsmul] using hpw (e x) (e y)
  specialize hi hpull
  simpa [he.lintegral_comp hf, he.lintegral_comp hg, he.lintegral_comp hh] using hi

/-- Prékopa–Leindler on the empty product.  The product measure and the underlying
space both have exactly one point, so this is the zero-dimensional base of the
induction; no positive dimension is assumed. -/
theorem measurePrekopaLeindler_pi_fin_zero
    {E : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    (μ : Measure E) :
    MeasurePrekopaLeindler (Fin 0 → E) (Measure.pi fun _ : Fin 0 => μ) := by
  intro f g h hf hg hh a b ha hb hab hpw
  let z : Fin 0 → E := fun i => Fin.elim0 i
  have hu : ∀ u : Fin 0 → E, u = z := fun u => Subsingleton.elim _ _
  have hz : a • z + b • z = z := Subsingleton.elim _ _
  simpa [hu, hz] using hpw z z

/-- Induction/tensorization from one factor to every finite homogeneous product.
At the successor step `piFinSuccAbove` splits off one coordinate; its mathlib theorem
identifies the finite product measure exactly with the corresponding product measure. -/
theorem measurePrekopaLeindler_pi_fin
    {E : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    (μ : Measure E) [SigmaFinite μ]
    (hμ : MeasurePrekopaLeindler E μ) :
    ∀ n : ℕ, MeasurePrekopaLeindler (Fin n → E) (Measure.pi fun _ : Fin n => μ) := by
  intro n
  induction n with
  | zero => exact measurePrekopaLeindler_pi_fin_zero μ
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0
      have hprod : MeasurePrekopaLeindler (E × (Fin n → E))
          (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
        measurePrekopaLeindler_prod μ (Measure.pi fun _ : Fin n => μ) hμ ih
      apply hprod.map_measurableEquiv e.symm
        (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
      · intro x y
        apply e.injective
        ext <;> rfl
      · intro c x
        apply e.injective
        ext <;> rfl

/-- The scalar statement tensorizes to every finite Cartesian power of Lebesgue
measure.  Scalar Prékopa–Leindler itself is a hypothesis here. -/
theorem measurePrekopaLeindler_euclidean_pi
    (hscalar : ScalarPrekopaLeindler) (n : ℕ) :
    MeasurePrekopaLeindler (Fin n → ℝ)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) :=
  measurePrekopaLeindler_pi_fin volume (measurePrekopaLeindler_real hscalar) n

end PrekopaNative.BlockBand
