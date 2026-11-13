module

public import Mathlib

/-!
# Random entire functions

`EntireFunction m` is the space of entire functions of `m` complex variables with the
compact-open (locally uniform) topology and its Borel σ-algebra, and `RandomEntire m` is the
space of probability laws on it. The file proves continuity and measurability of evaluation and of
holomorphic partial derivatives, a measurability criterion through point evaluations, and the
measurability of normalized finite random determinants (`DeterministicEntireNormalizer`).
-/

@[expose] public section

open Filter Topology MeasureTheory
open scoped ENNReal

namespace BlockBand.Critical.Entire

/-- Entire functions of `m` complex variables, equipped below with the subspace of the
compact-open topology on continuous maps.  This is the locally-uniform state space for the
normalized random determinants and their limiting laws; it does not assert any stochastic
convergence. -/
def EntireFunction (m : ℕ) : Type :=
  {F : C(Fin m → ℂ, ℂ) // Differentiable ℂ ⇑F}

namespace EntireFunction

variable {m : ℕ}

instance instFunLike : FunLike (EntireFunction m) (Fin m → ℂ) ℂ where
  coe F := ⇑F.1
  coe_injective _ _ h := Subtype.ext (DFunLike.coe_injective h)

/-- The compact-open topology, inherited from continuous maps.  Mathlib's topology on
`C(X,Y)` is uniform convergence on compact subsets when `Y` is a uniform space. -/
noncomputable instance instTopologicalSpace : TopologicalSpace (EntireFunction m) :=
  instTopologicalSpaceSubtype

/-- Random entire functions use the Borel σ-algebra of the compact-open topology. -/
noncomputable instance instMeasurableSpace : MeasurableSpace (EntireFunction m) :=
  Subtype.instMeasurableSpace

instance instOpensMeasurableSpace : OpensMeasurableSpace (EntireFunction m) := ⟨by
  apply MeasurableSpace.generateFrom_le
  intro s hs
  rcases isOpen_induced_iff.mp hs with ⟨t, ht, hts⟩
  rw [← hts]
  exact measurable_subtype_coe ht.measurableSet⟩

instance instBorelSpace : BorelSpace (EntireFunction m) where
  measurable_eq := le_antisymm (by
    intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    exact continuous_subtype_val.borel_measurable ht) OpensMeasurableSpace.borel_le

instance instT2Space : T2Space (EntireFunction m) :=
  (Topology.IsEmbedding.subtypeVal :
    Topology.IsEmbedding (Subtype.val : EntireFunction m → C(Fin m → ℂ, ℂ))).t2Space

instance instSecondCountableTopology : SecondCountableTopology (EntireFunction m) :=
  (Topology.IsEmbedding.subtypeVal :
    Topology.IsEmbedding (Subtype.val : EntireFunction m → C(Fin m → ℂ, ℂ))).isInducing.secondCountableTopology

/-- Forget holomorphy and retain the underlying continuous map. -/
def toContinuousMap (F : EntireFunction m) : C(Fin m → ℂ, ℂ) := F.1

/-- Bundle an everywhere complex-differentiable function as an entire function. -/
def ofDifferentiable (F : (Fin m → ℂ) → ℂ) (hF : Differentiable ℂ F) : EntireFunction m :=
  ⟨⟨F, hF.continuous⟩, hF⟩

@[simp] theorem coe_ofDifferentiable (F : (Fin m → ℂ) → ℂ) (hF : Differentiable ℂ F) :
    ⇑(ofDifferentiable F hF) = F := rfl

@[simp] theorem coe_toContinuousMap (F : EntireFunction m) : ⇑(toContinuousMap F) = ⇑F := rfl

/-- Every bundled entire function is complex differentiable on all of `ℂ^m`. -/
theorem differentiable (F : EntireFunction m) : Differentiable ℂ ⇑F := F.2

@[ext] theorem ext {F G : EntireFunction m} (h : ∀ z, F z = G z) : F = G :=
  DFunLike.ext F G h

/-- The inclusion into continuous maps is a topological embedding. -/
theorem isEmbedding_toContinuousMap :
    Topology.IsEmbedding (toContinuousMap : EntireFunction m → C(Fin m → ℂ, ℂ)) :=
  Topology.IsEmbedding.subtypeVal

/-- Convergence in the state space is precisely locally uniform convergence on `ℂ^m`. -/
theorem tendsto_iff_tendstoLocallyUniformly {ι : Type*} {l : Filter ι}
    {F : ι → EntireFunction m} {G : EntireFunction m} :
    Tendsto F l (𝓝 G) ↔ TendstoLocallyUniformly (fun i => ⇑(F i)) ⇑G l := by
  rw [isEmbedding_toContinuousMap.tendsto_nhds_iff]
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly

/-- Joint evaluation is continuous for the compact-open topology. -/
theorem continuous_eval :
    Continuous fun p : EntireFunction m × (Fin m → ℂ) => p.1 p.2 :=
  (ContinuousEval.continuous_eval :
      Continuous fun p : C(Fin m → ℂ, ℂ) × (Fin m → ℂ) => p.1 p.2).comp
    (isEmbedding_toContinuousMap.continuous.prodMap continuous_id)

/-- Evaluation at a deterministic source point is continuous. -/
theorem continuous_eval_const (z : Fin m → ℂ) :
    Continuous fun F : EntireFunction m => F z :=
  continuous_eval.comp (continuous_id.prodMk continuous_const)

/-- Evaluation at a deterministic source point is Borel measurable. -/
theorem measurable_eval_const (z : Fin m → ℂ) :
    Measurable fun F : EntireFunction m => F z :=
  (continuous_eval_const z).measurable

/-- Joint evaluation is Borel measurable. -/
theorem measurable_eval :
    Measurable fun p : EntireFunction m × (Fin m → ℂ) => p.1 p.2 :=
  continuous_eval.measurable

/-- Measurability into the compact-open entire-function state is equivalent to
measurability of all point evaluations.  This is the practical constructor for finite
random determinants. -/
theorem measurable_iff_eval {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → EntireFunction m} :
    Measurable X ↔ ∀ z : Fin m → ℂ, Measurable fun ω => X ω z := by
  constructor
  · intro h z
    exact (measurable_eval_const z).comp h
  · intro h
    exact (ContinuousMap.measurable_iff_eval.mpr h).subtype_mk

/-- Bundle a pointwise measurable family of entire functions as a measurable random
element of the compact-open state space. -/
theorem measurable_ofDifferentiable {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → (Fin m → ℂ) → ℂ} (hf : ∀ ω, Differentiable ℂ (f ω))
    (hmeas : ∀ z : Fin m → ℂ, Measurable fun ω => f ω z) :
    Measurable fun ω => ofDifferentiable (f ω) (hf ω) :=
  measurable_iff_eval.mpr hmeas

/-- The holomorphic partial derivative in coordinate `a`. -/
noncomputable def partialDerivValue (a : Fin m) (F : EntireFunction m)
    (z : Fin m → ℂ) : ℂ :=
  fderiv ℂ (⇑F) z (Pi.single a 1)

/-- A pointwise identity relating `partialDerivValue` to the Fréchet derivative. -/
@[simp] theorem partialDerivValue_eq (a : Fin m) (F : EntireFunction m)
    (z : Fin m → ℂ) :
    partialDerivValue a F z = fderiv ℂ (⇑F) z (Pi.single a 1) := rfl

/-- Partial-derivative evaluation is jointly Borel measurable in the entire function
and the source point.  This uses Mathlib's parameter-dependent measurability theorem for
Fréchet derivatives, applied to the jointly continuous compact-open evaluation map. -/
theorem measurable_partialDerivValue (a : Fin m) :
    Measurable fun p : EntireFunction m × (Fin m → ℂ) =>
      partialDerivValue a p.1 p.2 := by
  exact measurable_fderiv_apply_const_with_param ℂ continuous_eval (Pi.single a 1)

/-- A holomorphic partial derivative at a deterministic source point is Borel measurable
as a function of the entire function. -/
theorem measurable_partialDerivValue_const (a : Fin m) (z : Fin m → ℂ) :
    Measurable fun F : EntireFunction m => partialDerivValue a F z :=
  (measurable_partialDerivValue a).comp (measurable_id.prodMk measurable_const)

/-- Partial-derivative evaluation of a measurable random entire function is measurable. -/
theorem measurable_partialDerivValue_comp {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → EntireFunction m} (hX : Measurable X)
    (a : Fin m) (z : Fin m → ℂ) :
    Measurable fun ω => partialDerivValue a (X ω) z :=
  (measurable_partialDerivValue_const a z).comp hX

/-- Evaluation of a measurable random entire function at a deterministic source point. -/
theorem measurable_eval_comp {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → EntireFunction m} (hX : Measurable X) (z : Fin m → ℂ) :
    Measurable fun ω => X ω z :=
  (measurable_eval_const z).comp hX

end EntireFunction

/-- The law of a random entire function in the compact-open Borel state space. -/
abbrev RandomEntire (m : ℕ) : Type := ProbabilityMeasure (EntireFunction m)

namespace RandomEntire

variable {m : ℕ}

/-- The law of a measurable random entire element.  The measurability witness is kept in
the interface even though `ProbabilityMeasure.map` is totalized on nonmeasurable maps. -/
noncomputable def lawOf {Ω : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    (X : Ω → EntireFunction m) (_hX : Measurable X) : RandomEntire m :=
  μ.map X

end RandomEntire

/-- A deterministic, nonzero denominator together with an entire numerator.  This is
exactly the normalization of the random determinants: proving that a concrete
matrix determinant supplies these fields is a finite-dimensional task, not a stochastic
convergence assertion. -/
structure DeterministicEntireNormalizer (m : ℕ) where
  numerator : (Fin m → ℂ) → ℂ
  numerator_entire : Differentiable ℂ numerator
  denominator : ℂ
  denominator_ne_zero : denominator ≠ 0

namespace DeterministicEntireNormalizer

variable {m : ℕ}

/-- The normalized entire function `numerator / denominator`. -/
noncomputable def normalized (N : DeterministicEntireNormalizer m) : EntireFunction m :=
  EntireFunction.ofDifferentiable
    (fun z => N.denominator⁻¹ * N.numerator z)
    (differentiable_const N.denominator⁻¹ |>.mul N.numerator_entire)

@[simp] theorem normalized_apply (N : DeterministicEntireNormalizer m) (z : Fin m → ℂ) :
    N.normalized z = N.denominator⁻¹ * N.numerator z := rfl

/-- If the numerator at a base source equals the denominator, normalization fixes that
source at one (in the paper the base source is `0`, so `D_W(0)=1`). -/
theorem normalized_eq_one_of_numerator_eq (N : DeterministicEntireNormalizer m)
    {z : Fin m → ℂ} (hz : N.numerator z = N.denominator) :
    N.normalized z = 1 := by
  rw [normalized_apply, hz, inv_mul_cancel₀ N.denominator_ne_zero]

/-- Measurability of a finite random normalized determinant reduces to measurable
numerator evaluations; the deterministic normalizer introduces no extra randomness. -/
theorem measurable_normalized_eval {Ω : Type*} [MeasurableSpace Ω]
    (denominator : ℂ) (hdenominator : denominator ≠ 0)
    (numerator : Ω → (Fin m → ℂ) → ℂ)
    (hentire : ∀ ω, Differentiable ℂ (numerator ω))
    (hmeas : ∀ z, Measurable fun ω => numerator ω z)
    (z : Fin m → ℂ) :
    Measurable fun ω =>
      (DeterministicEntireNormalizer.normalized
        { numerator := numerator ω
          numerator_entire := hentire ω
          denominator := denominator
          denominator_ne_zero := hdenominator }) z := by
  rw [show (fun ω =>
      (DeterministicEntireNormalizer.normalized
        { numerator := numerator ω
          numerator_entire := hentire ω
          denominator := denominator
          denominator_ne_zero := hdenominator }) z) =
      (fun ω => denominator⁻¹ * numerator ω z) by funext ω; rfl]
  exact measurable_const.mul (hmeas z)

/-- The whole normalized finite determinant is a measurable random element of the
compact-open state space, not merely a collection of measurable evaluations. -/
theorem measurable_normalized {Ω : Type*} [MeasurableSpace Ω]
    (denominator : ℂ) (hdenominator : denominator ≠ 0)
    (numerator : Ω → (Fin m → ℂ) → ℂ)
    (hentire : ∀ ω, Differentiable ℂ (numerator ω))
    (hmeas : ∀ z, Measurable fun ω => numerator ω z) :
    Measurable fun ω =>
      DeterministicEntireNormalizer.normalized
        { numerator := numerator ω
          numerator_entire := hentire ω
          denominator := denominator
          denominator_ne_zero := hdenominator } := by
  apply EntireFunction.measurable_iff_eval.mpr
  intro z
  exact measurable_normalized_eval denominator hdenominator numerator hentire hmeas z

end DeterministicEntireNormalizer

end BlockBand.Critical.Entire
