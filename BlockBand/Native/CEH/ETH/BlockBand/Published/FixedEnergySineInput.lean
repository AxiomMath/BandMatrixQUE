module

public import BlockBand.Native.CEH.ETH.BlockBand.Coarea.PhysicalHermitianGaussianSplit
public import BlockBand.Native.CEH.ETH.BlockBand.Published.SineProcess
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import BlockBand.Native.CEH.ETH.BlockBand.Spectral.PhysicalUnfolding

/-!
# Conditional fixed-energy sine-universality interface

This module states, as an explicit conditional input, the external fixed-energy sine-kernel
theorem (fixed-variance complex Gaussian bulk statistics).

The source ensemble is not an arbitrary probability measure: it is constructed
below as `F + G`, where the real diagonal coordinates of `G` have variance
`t / N` and the real and imaginary strict-upper coordinates have variance
`t / (2N)`.  Thus it is exactly `F + sqrt(t) G_N` for normalized complex GUE
`G_N`; no unnamed law or existence theorem is hidden in the interface.

At energy `E`, an MDE solution `m` supplies the source density
`rho = Im(m) / pi`.  The real scalar conjugation of the finite kernel cancels in its determinant, so the
interface states the gauge-invariant factorial correlations directly.  Physical
correlation densities are unfolded with the
Jacobian `(N rho)^{-k}` and evaluated at `E + x_i/(N rho)`.  The input records
both the uniform `O(N^{-1/2})` convergence of every fixed correlation and weak
convergence of the resulting `RationalWindowPointState` law to an explicitly
supplied `SineProcessInput`.  All existence needed at the conditional boundary
(the limiting sine law, physical correlation densities, their factorial-law
identity, and measurability of the finite point-state map) is carried by
structure fields rather than asserted by an axiom or an unconditional theorem.

Quantifier order follows the paper: the polynomial deformation exponent,
compact variance interval, positive MDE lower bound, compact energy interval,
correlation order, and compact unfolded window are fixed before the constants
and cutoff.  The deformation, variance, energy, and MDE solution may then vary
with `N`; no limiting empirical measure of `F` and no dimension-independent
operator-norm bound are assumed.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open Filter MeasureTheory
open scoped ENNReal NNReal Topology Matrix.Norms.L2Operator

/-- The scalar Dyson equation used in the external sine-kernel theorem:
`m = <(F - (E + t m)I)⁻¹>`, with the positive-imaginary branch selected.
The normalization of `normalizedTrace` is `N⁻¹ Tr`. -/
def IsFixedEnergyMDESolution {N : ℕ} (t E : ℝ)
    (F : HermitianMatrix (Fin N)) (m : ℂ) : Prop :=
  m = Conventions.normalizedTrace
      (F.1 - ((E : ℂ) + (t : ℂ) * m) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ ∧
    0 < m.im

/-- The free-convolution density in the normalization. -/
def fixedEnergyDensity (m : ℂ) : ℝ :=
  m.im / Real.pi

/-- A regular fixed-energy deformation in the precise fixed-variance regime of
the external sine-kernel theorem.  The operator norm may grow like `N^A`; `E` is only
required to remain in the fixed compact interval `[-energyRadius,energyRadius]`.
The lower bound is on `Im m`, exactly as printed, so the density lower bound is
`vStar / pi`. -/
def FixedEnergyRegularDeformation (N : ℕ)
    (A tLo tHi vStar energyRadius : ℝ)
    (F : HermitianMatrix (Fin N)) (t E : ℝ) (m : ℂ) : Prop :=
  1 ≤ N ∧
    0 ≤ A ∧
    0 < tLo ∧ tLo ≤ t ∧ t ≤ tHi ∧
    0 < vStar ∧ vStar ≤ m.im ∧
    0 ≤ energyRadius ∧ |E| ≤ energyRadius ∧
    ‖F.1‖ ≤ Real.rpow (N : ℝ) A ∧
    IsFixedEnergyMDESolution t E F m

/-- The exact normalized complex-GUE deformation map.  The coordinate law used
below has diagonal variance `t/N` and strict-upper component variance
`t/(2N)`, hence this is `F + sqrt(t) G_N`. -/
def fixedEnergyDeformedGUEMap (N : ℕ) (F : HermitianMatrix (Fin N))
    (x : HermitianCoordinateSpace N) : HermitianMatrix (Fin N) :=
  hermitianMatrixAdd F (hermitianGUEBlock N x)

/-- The exact deformed normalized-GUE probability law at variance parameter
`t`.  Unlike an abstract law parameter, this definition exposes the source
existence and normalization used by the external theorem. -/
def fixedEnergyDeformedGUELaw (N : ℕ) (F : HermitianMatrix (Fin N))
    (t : ℝ) : ProbabilityMeasure (HermitianMatrix (Fin N)) :=
  let variance : ℝ := max 0 (t / (N : ℝ))
  let hvariance : 0 ≤ variance := le_max_left 0 (t / (N : ℝ))
  let source : ProbabilityMeasure (HermitianCoordinateSpace N) :=
    ⟨hermitianGUECoordinateMeasure N variance hvariance, inferInstance⟩
  source.map (fixedEnergyDeformedGUEMap N F)

/-- The fixed-energy unfolding used by the external theorem, with the local
MDE density rather than the semicircle density of the ring endpoint. -/
def fixedEnergyUnfoldedEigenvalue (N : ℕ) (E rho : ℝ)
    (H : HermitianMatrix (Fin N)) (a : Fin N) : ℝ :=
  (N : ℝ) * rho *
    (orderedEigenvalue H (Fin.cast (Fintype.card_fin N).symm a) - E)

/-- Compatibility with the unfolding: when the local density is
specialized to the semicircle density, the fixed-energy coordinate
is exactly `unfoldedEigenvalue`. -/
theorem fixedEnergyUnfoldedEigenvalue_eq_unfoldedEigenvalue
    (p : Params) (E : ℝ) (H : HermitianMatrix (Fin p.L)) (a : Fin p.L) :
    fixedEnergyUnfoldedEigenvalue p.L E (Conventions.semicircleDensity E) H a =
      unfoldedEigenvalue p E H a := by
  rfl

/-- The complete finite unfolded spectrum, with the trivial mark used
by `RationalWindowPointState`. -/
def fixedEnergyUnfoldedConfiguration (N : ℕ) (E rho : ℝ)
    (H : HermitianMatrix (Fin N)) : FiniteMarkedConfiguration N Unit :=
  fun a => (fixedEnergyUnfoldedEigenvalue N E rho H a, ())

/-- Embed the finite unfolded spectrum into the common rational-window state
space used by the weak-convergence statements. -/
def fixedEnergyRationalWindowPointState (N : ℕ) (E rho : ℝ)
    (H : HermitianMatrix (Fin N)) : RationalWindowPointState :=
  finiteMarkedRationalWindowPointState
    (fixedEnergyUnfoldedConfiguration N E rho H)

/-- The finite deformed-GUE point-state law.  Its codomain is the same
`ProbabilityMeasure RationalWindowPointState` used by the tightness
and weak-convergence theorems. -/
def fixedEnergyPointLaw (N : ℕ) (F : HermitianMatrix (Fin N))
    (t E rho : ℝ) : ProbabilityMeasure RationalWindowPointState :=
  (fixedEnergyDeformedGUELaw N F t).map
    (fixedEnergyRationalWindowPointState N E rho)

/-- A physical `k`-point density unfolded at `E` with the exact Jacobian
`(N rho)^{-k}`.  The inverse affine map is
`x_i |-> E + x_i/(N rho)`; there is no additional `pi` because
`rho = Im(m)/pi`. -/
def fixedEnergyUnfoldedCorrelation (N : ℕ) (E rho : ℝ)
    (physicalCorrelation : (k : ℕ) → (Fin k → ℝ) → ℝ)
    (k : ℕ) (x : Fin k → ℝ) : ℝ :=
  ((N : ℝ) * rho) ^ (-k : ℤ) *
    physicalCorrelation k (fun i => E + x i / ((N : ℝ) * rho))

/-- Explicit conditional input for the external sine-kernel theorem.

The `physicalCorrelation` field is data because correlation densities are not determined by
an arbitrary point-process law in Mathlib. The `factorialLaw` field ties it to the deformed-GUE
eigenvalue law after
unfolding, including ordered distinct tuples and the full Jacobian.  The two
asymptotic fields then record respectively the source theorem's uniform
correlation estimate and its local-point-process consequence. -/
structure FixedEnergySineInput where
  /-- Explicit existence of the limiting, intensity-one sine law. -/
  sine : SineProcessInput
  /-- Physical factorial-correlation densities of the deformed GUE law. -/
  physicalCorrelation :
    (N : ℕ) → HermitianMatrix (Fin N) → ℝ →
      (k : ℕ) → (Fin k → ℝ) → ℝ
  /-- Measurability needed to push the canonical finite matrix law into the
  common rational-window point-state space. -/
  stateMeasurable :
    ∀ (N : ℕ) (E rho : ℝ),
      Measurable (fixedEnergyRationalWindowPointState N E rho)
  /-- Exact factorial-density identity after unfolding.  This fixes the
  correlation convention, ordered-tuple normalization, and Jacobian before
  any limit is taken. -/
  factorialLaw :
    ∀ (N : ℕ) (F : HermitianMatrix (Fin N)) (t : ℝ)
      (E rho : ℝ) (_hrho : 0 < rho)
      (k n : ℕ) (B : Set (Fin k → ℝ)),
      MeasurableSet B →
      B ⊆ Set.pi Set.univ
        (fun _ : Fin k => Set.Ioo (-(n : ℝ)) (n : ℝ)) →
      ∫⁻ ξ, localFactorialMass k n ξ B
          ∂fixedEnergyPointLaw N F t E rho =
        ∫⁻ x in B,
          ENNReal.ofReal
            (fixedEnergyUnfoldedCorrelation N E rho
              (physicalCorrelation N F t) k x) ∂volume
  /-- Uniform fixed-order correlation convergence with the `O(N^{-1/2})` rate.  Constants are chosen after all fixed regularity and
  compactness parameters, and before `N,F,t,E,m,x`. -/
  correlationBound :
    ∀ (A tLo tHi vStar energyRadius : ℝ) (k : ℕ) (R : ℝ),
      0 ≤ A → 0 < tLo → tLo ≤ tHi → 0 < vStar →
      0 ≤ energyRadius → 0 ≤ R →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
        ∀ (N : ℕ), N₀ ≤ N →
        ∀ (F : HermitianMatrix (Fin N)) (t E : ℝ) (m : ℂ),
          FixedEnergyRegularDeformation N A tLo tHi vStar energyRadius
            F t E m →
          ∀ x : Fin k → ℝ, (∀ i, |x i| ≤ R) →
            |fixedEnergyUnfoldedCorrelation N E (fixedEnergyDensity m)
                (physicalCorrelation N F t) k x - sineCorrelation k x| ≤
              C / Real.sqrt N
  /-- Weak convergence of the local point process, in the common
  rational-window state.  The sequential formulation is the exact uniform
  reading: every sequence of admissible deformations with `N -> infinity`
  has the same supplied sine-law limit. -/
  pointProcess :
    ∀ [OpensMeasurableSpace RationalWindowPointState],
    ∀ (A tLo tHi vStar energyRadius : ℝ),
      0 ≤ A → 0 < tLo → tLo ≤ tHi → 0 < vStar →
      0 ≤ energyRadius →
      ∀ (N : ℕ → ℕ) (F : ∀ j, HermitianMatrix (Fin (N j)))
        (t E : ℕ → ℝ) (m : ℕ → ℂ),
        Tendsto N atTop atTop →
        (∀ j, FixedEnergyRegularDeformation (N j)
          A tLo tHi vStar energyRadius (F j) (t j) (E j) (m j)) →
        Tendsto
          (fun j => fixedEnergyPointLaw (N j) (F j) (t j) (E j)
            (fixedEnergyDensity (m j)))
          atTop (𝓝 (sineProcess sine))

/-- The external sine-kernel theorem, correlation-function form.  This theorem
only exposes the corresponding field of an explicit input; it does not construct that input. -/
theorem fixedEnergySineUniversality_correlation
    (input : FixedEnergySineInput)
    (A tLo tHi vStar energyRadius : ℝ) (k : ℕ) (R : ℝ)
    (hA : 0 ≤ A) (htLo : 0 < tLo) (ht : tLo ≤ tHi)
    (hv : 0 < vStar) (hE : 0 ≤ energyRadius) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ (N : ℕ), N₀ ≤ N →
      ∀ (F : HermitianMatrix (Fin N)) (t E : ℝ) (m : ℂ),
        FixedEnergyRegularDeformation N A tLo tHi vStar energyRadius
          F t E m →
        ∀ x : Fin k → ℝ, (∀ i, |x i| ≤ R) →
          |fixedEnergyUnfoldedCorrelation N E (fixedEnergyDensity m)
              (input.physicalCorrelation N F t) k x - sineCorrelation k x| ≤
            C / Real.sqrt N :=
  input.correlationBound A tLo tHi vStar energyRadius k R
    hA htLo ht hv hE hR

/-- The external sine-kernel theorem, local-point-process form.  Fixed regularity
parameters precede the varying admissible sequence, so this is the uniform
fixed-energy statement rather than a pointwise convergence claim. -/
theorem fixedEnergySineUniversality_pointProcess
    [OpensMeasurableSpace RationalWindowPointState]
    (input : FixedEnergySineInput)
    (A tLo tHi vStar energyRadius : ℝ)
    (hA : 0 ≤ A) (htLo : 0 < tLo) (ht : tLo ≤ tHi)
    (hv : 0 < vStar) (hE : 0 ≤ energyRadius)
    (N : ℕ → ℕ) (F : ∀ j, HermitianMatrix (Fin (N j)))
    (t E : ℕ → ℝ) (m : ℕ → ℂ)
    (hN : Tendsto N atTop atTop)
    (hregular : ∀ j, FixedEnergyRegularDeformation (N j)
      A tLo tHi vStar energyRadius (F j) (t j) (E j) (m j)) :
    Tendsto
      (fun j => fixedEnergyPointLaw (N j) (F j) (t j) (E j)
        (fixedEnergyDensity (m j)))
      atTop (𝓝 (sineProcess input.sine)) :=
  input.pointProcess A tLo tHi vStar energyRadius
    hA htLo ht hv hE N F t E m hN hregular

end CEHNative.BlockBand
