module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.SChainLocalLaw
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.GaussianPoincareIntermediate
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean real coordinates of the exact Gaussian ring (ER Proposition 5.4 input)

The global law of Erdős–Riabov, *The Zigzag Strategy for Random Band Matrices*,
arXiv:2506.06441v1, Proposition 5.4 (proved in their Section 7), is a statement about
smooth functions of the Gaussian matrix `H` at macroscopic spectral heights.  To use
the finite-dimensional Gaussian Poincaré inequality we realize `H` as a linear image
of a Gaussian vector in a real Hilbert space.

* `GlobalCoord p = UpperPair p × Fin 2`: the real (`0`) and imaginary (`1`) part of
  every upper-triangular entry `H_q`, `q = (a, b)`, `a ≤ b` in the source order.
* `CoordSpace p = EuclideanSpace ℝ (GlobalCoord p)`.
* `coordVector M ω`: the coordinates of the sample `M.H ω`.
* `coordMatrix x`: Hermitian reconstruction (diagonal coordinates are projected to
  their real part, the diagonal imaginary coordinate is ignored), so that
  `coordMatrix (coordVector M ω) = M.H ω` for every sample.

Nothing probabilistic is assumed here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERSChainGlobal

open MeasureTheory ProbabilityTheory
open ERProfile ERConcrete ERGaussianPoincareIntermediate ERProductCoordinateAnalysis

/-- `p.n ≠ 0` as an instance (scoped to this development). -/
scoped instance instNeZeroGlobal (p : Params) : NeZero p.n := p.nNeZero
/-- Upper pairs are finite (scoped to this development). -/
scoped instance instFiniteUpperPairGlobal (p : Params) : Finite (UpperPair p) :=
  Finite.of_injective Subtype.val Subtype.val_injective
/-- The finite enumeration of upper pairs used throughout this development. -/
scoped instance instFintypeUpperPairGlobal (p : Params) : Fintype (UpperPair p) :=
  Fintype.ofFinite _
/-- Classical decidable equality of upper pairs (scoped to this development). -/
scoped instance instDecidableEqUpperPairGlobal (p : Params) : DecidableEq (UpperPair p) :=
  Classical.decEq _

/-- Real coordinate labels: an upper pair and a component (`0` real, `1` imaginary). -/
abbrev GlobalCoord (p : Params) : Type := UpperPair p × Fin 2

/-- The Euclidean space of all real upper coordinates. -/
abbrev CoordSpace (p : Params) : Type := EuclideanSpace ℝ (GlobalCoord p)

/-- The complex upper entries encoded by a real coordinate vector. -/
def coordEntries {p : Params} (x : CoordSpace p) (q : UpperPair p) : ℂ :=
  (x (q, 0) : ℂ) + Complex.I * (x (q, 1) : ℂ)

/-- Hermitian reconstruction of a matrix from a real coordinate vector. -/
def coordMatrix {p : Params} (x : CoordSpace p) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  matrixOfUpperCoordinates (coordEntries x)

/-- The reconstruction is Hermitian for every coordinate vector. -/
theorem coordMatrix_isHermitian {p : Params} (x : CoordSpace p) :
    (coordMatrix x).IsHermitian :=
  matrixOfUpperCoordinates_isHermitian _

/-- The real coordinate function extracted from complex upper entries. -/
def entriesToRaw {p : Params} (u : UpperPair p → ℂ) : GlobalCoord p → ℝ :=
  fun k => if k.2 = 0 then (u k.1).re else (u k.1).im

/-- The real-linear coordinate extraction into the plain function space. -/
def entriesToRawLinear (p : Params) : (UpperPair p → ℂ) →ₗ[ℝ] (GlobalCoord p → ℝ) where
  toFun := entriesToRaw
  map_add' u v := by
    funext k
    by_cases hk : k.2 = 0 <;> simp [entriesToRaw, hk]
  map_smul' c u := by
    funext k
    by_cases hk : k.2 = 0 <;> simp [entriesToRaw, hk]

/-- The continuous real-linear map from complex upper entries to Euclidean
coordinates. -/
def entriesToCoord (p : Params) : (UpperPair p → ℂ) →L[ℝ] CoordSpace p :=
  (EuclideanSpace.equiv (GlobalCoord p) ℝ).symm.toContinuousLinearMap.comp
    (LinearMap.toContinuousLinearMap (entriesToRawLinear p))

@[simp] theorem entriesToCoord_apply {p : Params} (u : UpperPair p → ℂ)
    (k : GlobalCoord p) :
    entriesToCoord p u k = if k.2 = 0 then (u k.1).re else (u k.1).im := rfl

/-- The real coordinate vector of a sample. -/
def coordVector {p : Params} (M : Law p) (ω : M.Ω) : CoordSpace p :=
  entriesToCoord p (fun q => upperEntryFamily M q ω)

@[simp] theorem coordVector_apply {p : Params} (M : Law p) (ω : M.Ω)
    (k : GlobalCoord p) :
    coordVector M ω k =
      if k.2 = 0 then (M.H ω k.1.1.1 k.1.1.2).re else (M.H ω k.1.1.1 k.1.1.2).im := rfl

theorem coordEntries_coordVector {p : Params} (M : Law p) (ω : M.Ω) :
    coordEntries (coordVector M ω) = fun q => upperEntryFamily M q ω := by
  funext q
  apply Complex.ext <;> simp [coordEntries, coordVector, upperEntryFamily]

/-- Exact pointwise reconstruction of the sample from its coordinates. -/
theorem coordMatrix_coordVector {p : Params} (M : Law p) (ω : M.Ω) :
    coordMatrix (coordVector M ω) = M.H ω := by
  rw [coordMatrix, coordEntries_coordVector]
  exact Law.matrixOfUpperCoordinates_actual M ω

/-- The coordinate vector is measurable. -/
theorem measurable_coordVector {p : Params} (M : Law p) :
    Measurable (coordVector M) :=
  (entriesToCoord p).continuous.measurable.comp
    (measurable_pi_iff.mpr fun q => measurable_upperEntryFamily M q)

/-- The law of the coordinate vector on the Euclidean space. -/
def coordMeasure {p : Params} (M : Law p) : Measure (CoordSpace p) :=
  M.P.map (coordVector M)

instance coordMeasure.instIsProbabilityMeasure {p : Params} (M : Law p) :
    IsProbabilityMeasure (coordMeasure M) :=
  ⟨by simp [coordMeasure, Measure.map_apply (measurable_coordVector M) MeasurableSet.univ]⟩

/-- The coordinate law is Gaussian: it is a continuous linear image of the jointly
Gaussian upper-entry vector. -/
instance coordMeasure.instIsGaussian {p : Params} (M : Law p) :
    IsGaussian (coordMeasure M) :=
  ((Law.hasGaussianLaw_upperCoordinateVector M).map (entriesToCoord p)).isGaussian_map

end ERSChainGlobal
end GaussianRing
end ERNative.BlockBand
