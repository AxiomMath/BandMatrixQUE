module

public import BlockBand.Critical.Entire.RandomEntire
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Compact-open continuity of source-coordinate derivative evaluation

Locally uniform convergence of entire functions in finitely many complex variables
implies convergence of every fixed coordinate partial derivative at every fixed source
point.  The proof restricts to the affine complex line in the chosen coordinate and
uses Mathlib's one-variable Cauchy-integral theorem
`TendstoLocallyUniformlyOn.deriv`.  No Montel, Hurwitz, or stochastic compactness
statement is assumed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.JointRecovery

open Filter MeasureTheory Set Topology
open BlockBand.Critical.Entire BlockBand.Critical.Entire.EntireFunction
open scoped Topology

namespace EntireFunction

variable {m : ℕ}

/-- The affine complex line through `z` in coordinate direction `a`. -/
def coordinateLine (a : Fin m) (z : Fin m → ℂ) (w : ℂ) : Fin m → ℂ :=
  w • Pi.single a 1 + z

/-- The coordinate line is continuous. -/
theorem continuous_coordinateLine (a : Fin m) (z : Fin m → ℂ) :
    Continuous (coordinateLine a z) := by
  unfold coordinateLine
  fun_prop

/-- Restriction of an entire function to a coordinate line is entire. -/
theorem differentiable_coordinateSlice (a : Fin m) (z : Fin m → ℂ)
    (F : EntireFunction m) :
    Differentiable ℂ (fun w => F (coordinateLine a z w)) := by
  exact F.differentiable.comp
    ((differentiable_id.smul_const (Pi.single a 1)).add_const z)

/-- The derivative of the coordinate slice at zero is the corresponding Fréchet
partial derivative at the base point. -/
theorem deriv_coordinateSlice_zero (a : Fin m) (z : Fin m → ℂ)
    (F : EntireFunction m) :
    deriv (fun w => F (coordinateLine a z w)) 0 = partialDerivValue a F z := by
  let e : Fin m → ℂ := Pi.single a 1
  have hline : HasDerivAt (fun w : ℂ => w • e + z) e 0 := by
    simpa using ((hasDerivAt_id (x := (0 : ℂ))).smul_const e).add_const z
  have hcomp := F.differentiable.differentiableAt.hasFDerivAt.comp 0 hline.hasFDerivAt
  change deriv ((fun x => F x) ∘ fun w : ℂ => w • e + z) 0 =
    partialDerivValue a F z
  rw [hcomp.hasDerivAt.deriv]
  simp [partialDerivValue, e]

/-- Locally uniform convergence of entire functions implies convergence of a fixed
source-coordinate partial derivative at a fixed source point.  The index is an
arbitrary filter, not only a sequence. -/
theorem partialDerivValue_tendsto
    {ι : Type*} {l : Filter ι} {F : ι → EntireFunction m} {G : EntireFunction m}
    (hFG : Tendsto F l (𝓝 G)) (a : Fin m) (z : Fin m → ℂ) :
    Tendsto (fun i => partialDerivValue a (F i) z) l
      (𝓝 (partialDerivValue a G z)) := by
  have hlocal : TendstoLocallyUniformly (fun i => ⇑(F i)) ⇑G l :=
    tendsto_iff_tendstoLocallyUniformly.mp hFG
  have hslice : TendstoLocallyUniformly
      (fun i w => F i (coordinateLine a z w))
      (fun w => G (coordinateLine a z w)) l := by
    change TendstoLocallyUniformly
      (fun i => (fun x => F i x) ∘ coordinateLine a z)
      ((fun x => G x) ∘ coordinateLine a z) l
    exact hlocal.comp (coordinateLine a z) (continuous_coordinateLine a z)
  have hderiv : TendstoLocallyUniformlyOn
      (deriv ∘ fun i w => F i (coordinateLine a z w))
      (deriv fun w => G (coordinateLine a z w)) l Set.univ :=
    (tendstoLocallyUniformlyOn_univ.mpr hslice).deriv
      (Eventually.of_forall fun i =>
        (differentiable_coordinateSlice a z (F i)).differentiableOn)
      isOpen_univ
  have hpoint := hderiv.tendsto_at (mem_univ (0 : ℂ))
  simpa only [Function.comp_apply, deriv_coordinateSlice_zero] using hpoint

/-- Partial-derivative evaluation at a fixed coordinate and source point is continuous
for the compact-open topology on `EntireFunction`. -/
theorem continuous_partialDerivValue_const (a : Fin m) (z : Fin m → ℂ) :
    Continuous fun F : EntireFunction m => partialDerivValue a F z := by
  rw [continuous_iff_continuousAt]
  intro F
  rw [continuousAt_def]
  exact partialDerivValue_tendsto (tendsto_id : Tendsto id (𝓝 F) (𝓝 F)) a z

/-- The already available measurability theorem follows in particular from continuity. -/
theorem measurable_partialDerivValue_const_of_continuous (a : Fin m)
    (z : Fin m → ℂ) :
    Measurable fun F : EntireFunction m => partialDerivValue a F z :=
  (continuous_partialDerivValue_const a z).measurable

/-- Weak convergence of entire-function laws passes to one fixed coordinate derivative. -/
theorem tendsto_map_partialDerivValue
    {ι : Type*} {l : Filter ι} {μ : ι → RandomEntire m} {ν : RandomEntire m}
    (hμ : Tendsto μ l (𝓝 ν)) (a : Fin m) (z : Fin m → ℂ) :
    Tendsto (fun i => (μ i).map (fun F => partialDerivValue a F z)) l
      (𝓝 (ν.map fun F => partialDerivValue a F z)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hμ
    (continuous_partialDerivValue_const a z)

/-- A finite vector of coordinate partial derivatives, allowing a different deterministic
source point for each output coordinate. -/
def partialDerivVector {p : ℕ} (a : Fin p → Fin m)
    (z : Fin p → Fin m → ℂ) (F : EntireFunction m) : Fin p → ℂ :=
  fun j => partialDerivValue (a j) F (z j)

/-- Every finite derivative-vector observable is continuous. -/
theorem continuous_partialDerivVector {p : ℕ} (a : Fin p → Fin m)
    (z : Fin p → Fin m → ℂ) :
    Continuous (partialDerivVector a z : EntireFunction m → Fin p → ℂ) := by
  exact continuous_pi fun j => continuous_partialDerivValue_const (a j) (z j)

/-- Hence finite derivative-vector observables are Borel measurable. -/
theorem measurable_partialDerivVector {p : ℕ} (a : Fin p → Fin m)
    (z : Fin p → Fin m → ℂ) :
    Measurable (partialDerivVector a z : EntireFunction m → Fin p → ℂ) :=
  (continuous_partialDerivVector a z).measurable

/-- Weak convergence of entire-function laws passes to every finite vector of fixed
source-coordinate derivatives by the continuous mapping theorem. -/
theorem tendsto_map_partialDerivVector
    {ι : Type*} {l : Filter ι} {μ : ι → RandomEntire m} {ν : RandomEntire m}
    (hμ : Tendsto μ l (𝓝 ν)) {p : ℕ} (a : Fin p → Fin m)
    (z : Fin p → Fin m → ℂ) :
    Tendsto (fun i => (μ i).map (partialDerivVector a z)) l
      (𝓝 (ν.map (partialDerivVector a z))) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hμ
    (continuous_partialDerivVector a z)

end EntireFunction

end BlockBand.Critical.JointRecovery
