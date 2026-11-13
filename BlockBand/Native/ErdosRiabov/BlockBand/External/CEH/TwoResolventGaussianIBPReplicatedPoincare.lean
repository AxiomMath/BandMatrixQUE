module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.CEH.GUEStationarity
public import BlockBand.Native.ErdosRiabov.BlockBand.Model.GaussianRing
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Complex.Basic
public import BlockBand.Model.Construction.OrderedEigenvalues
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.FieldTheory.Separable
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.Sequences
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.Topology.Instances.Nat
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import BlockBand.Native.ErdosRiabov.BlockBand.Basic.Parameters
public import Mathlib.Probability.Independence.InfinitePi
public import BlockBand.Native.ErdosRiabov.BlockBand.External.CEH.TwoResolventPencilAdapter
public import BlockBand.Native.ErdosRiabov.BlockBand.Probability.GaussianIntegrationByParts
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import BlockBand.Native.ErdosRiabov.BlockBand.Analysis.CauchyResolventBound
public import Mathlib.MeasureTheory.Integral.Pi
public import BlockBand.Native.ErdosRiabov.BlockBand.External.CEH.MDE
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.Spaces.CompactConvergenceCLM
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Moments.CovarianceBilin
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Gaussian Poincaré input for replicated CEH resolvents

This module proves, without axioms, a finite-dimensional Gaussian variance
bound by the independent-copy rotation argument.  The proof is measure-level:
rotation invariance is derived from the centered Gaussian law, and the
fundamental theorem of calculus and Cauchy–Schwarz control the increment.
It is then available for the concrete finite coordinate product law used by
the replicated GUE construction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
@[expose] public section
noncomputable section

open scoped BigOperators ENNReal NNReal ProbabilityTheory RealInnerProductSpace Topology
open MeasureTheory Filter Real

namespace ERNative.BlockBand.External.CEH
namespace FiniteGaussianPoincare

open scoped Interval
open ProbabilityTheory

open scoped Interval

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  {μ : Measure H} [IsGaussian μ]

/-- The `t`-dependent affine Gaussian mixture `√t • x + √(1-t) • y`. -/
noncomputable def gaussMix (t : ℝ) (p : H × H) : H :=
  Real.sqrt t • p.1 + Real.sqrt (1 - t) • p.2

/-!
We also use the orthogonal companion
`(x,y) ↦ (√(1-t) • x - √t • y)`.

For `t ∈ [0,1]`, the map `(x,y) ↦ (gaussMix t (x,y), gaussMixOrtho t (x,y))` is an involution.
-/

/-- The orthogonal companion of `gaussMix`: `√(1-t) • x - √t • y`. -/
noncomputable def gaussMixOrtho (t : ℝ) (p : H × H) : H :=
  Real.sqrt (1 - t) • p.1 - Real.sqrt t • p.2

/-!
### Continuous linear maps packaging
-/

/-- `gaussMix` as a continuous linear map in the pair variable. -/
noncomputable def gaussMixCLM (t : ℝ) : (H × H) →L[ℝ] H :=
  (Real.sqrt t) • ContinuousLinearMap.fst ℝ H H
    + (Real.sqrt (1 - t)) • ContinuousLinearMap.snd ℝ H H

@[simp] lemma gaussMixCLM_apply (t : ℝ) (p : H × H) :
    gaussMixCLM (H := H) t p = gaussMix (H := H) t p := by
  rfl

/-- `gaussMixOrtho` as a continuous linear map in the pair variable. -/
noncomputable def gaussMixOrthoCLM (t : ℝ) : (H × H) →L[ℝ] H :=
  (Real.sqrt (1 - t)) • ContinuousLinearMap.fst ℝ H H
    - (Real.sqrt t) • ContinuousLinearMap.snd ℝ H H

@[simp] lemma gaussMixOrthoCLM_apply (t : ℝ) (p : H × H) :
    gaussMixOrthoCLM (H := H) t p = gaussMixOrtho (H := H) t p := by
  rfl

/-- The orthogonal mixing map `(x,y) ↦ (gaussMix t (x,y), gaussMixOrtho t (x,y))`. -/
noncomputable def gaussMixMap (t : ℝ) : (H × H) →L[ℝ] (H × H) :=
  (gaussMixCLM (H := H) t).prod (gaussMixOrthoCLM (H := H) t)

@[simp] lemma gaussMixMap_apply (t : ℝ) (p : H × H) :
    gaussMixMap (H := H) t p = (gaussMix (H := H) t p, gaussMixOrtho (H := H) t p) := by
  rfl

@[simp] lemma gaussMix_zero (p : H × H) : gaussMix (H := H) 0 p = p.2 := by
  simp [gaussMix]

@[simp] lemma gaussMix_one (p : H × H) : gaussMix (H := H) 1 p = p.1 := by
  simp [gaussMix]

@[simp] lemma gaussMixOrtho_zero (p : H × H) : gaussMixOrtho (H := H) 0 p = p.1 := by
  simp [gaussMixOrtho]

@[simp] lemma gaussMixOrtho_one (p : H × H) : gaussMixOrtho (H := H) 1 p = -p.2 := by
  simp [gaussMixOrtho]

/-!
### A smoother (cos/sin) Gaussian mixing map

The `sqrt`-parameterization `gaussMix` is convenient for some algebraic identities, but for the
Poincaré/variance argument we prefer the rotation-parameterization
`(x,y) ↦ (cos θ • x + sin θ • y, -sin θ • x + cos θ • y)`, since it has a clean derivative in `θ`.
-/

/-- The `θ`-dependent Gaussian rotation mix `cos θ • x + sin θ • y`. -/
noncomputable def gaussRot (θ : ℝ) (p : H × H) : H :=
  Real.cos θ • p.1 + Real.sin θ • p.2

/-- The orthogonal companion of `gaussRot`: `-sin θ • x + cos θ • y`. -/
noncomputable def gaussRotOrtho (θ : ℝ) (p : H × H) : H :=
  -Real.sin θ • p.1 + Real.cos θ • p.2

/-!
### Continuous linear maps
-/

/-- `gaussRot` as a continuous linear map in the pair variable. -/
noncomputable def gaussRotCLM (θ : ℝ) : (H × H) →L[ℝ] H :=
  (Real.cos θ) • ContinuousLinearMap.fst ℝ H H
    + (Real.sin θ) • ContinuousLinearMap.snd ℝ H H

@[simp] lemma gaussRotCLM_apply (θ : ℝ) (p : H × H) :
    gaussRotCLM (H := H) θ p = gaussRot (H := H) θ p := by
  rfl

/-- `gaussRotOrtho` as a continuous linear map in the pair variable. -/
noncomputable def gaussRotOrthoCLM (θ : ℝ) : (H × H) →L[ℝ] H :=
  (-Real.sin θ) • ContinuousLinearMap.fst ℝ H H
    + (Real.cos θ) • ContinuousLinearMap.snd ℝ H H

@[simp] lemma gaussRotOrthoCLM_apply (θ : ℝ) (p : H × H) :
    gaussRotOrthoCLM (H := H) θ p = gaussRotOrtho (H := H) θ p := by
  rfl

/-- The rotation mixing map `(x,y) ↦ (gaussRot θ (x,y), gaussRotOrtho θ (x,y))`. -/
noncomputable def gaussRotMap (θ : ℝ) : (H × H) →L[ℝ] (H × H) :=
  (gaussRotCLM (H := H) θ).prod (gaussRotOrthoCLM (H := H) θ)

@[simp] lemma gaussRotMap_apply (θ : ℝ) (p : H × H) :
    gaussRotMap (H := H) θ p = (gaussRot (H := H) θ p, gaussRotOrtho (H := H) θ p) := by
  rfl

private lemma variance_gaussRot_components (θ : ℝ) (L₁ L₂ : StrongDual ℝ H) :
    Var[(Real.cos θ) • L₁ + (Real.sin θ) • L₂; μ]
      + Var[(-Real.sin θ) • L₁ + (Real.cos θ) • L₂; μ]
      = Var[L₁; μ] + Var[L₂; μ] := by
  have hL₁ : MemLp L₁ 2 μ := IsGaussian.memLp_dual μ L₁ 2 (by simp)
  have hL₂ : MemLp L₂ 2 μ := IsGaussian.memLp_dual μ L₂ 2 (by simp)
  have hVar₁ :
      Var[(Real.cos θ) • L₁ + (Real.sin θ) • L₂; μ]
        = Var[(Real.cos θ) • L₁; μ]
          + 2 * cov[(Real.cos θ) • L₁, (Real.sin θ) • L₂; μ]
          + Var[(Real.sin θ) • L₂; μ] :=
    (variance_add (μ := μ) (hL₁.const_smul (Real.cos θ)) (hL₂.const_smul (Real.sin θ)))
  have hVar₂ :
      Var[(-Real.sin θ) • L₁ + (Real.cos θ) • L₂; μ]
        = Var[(-Real.sin θ) • L₁; μ]
          + 2 * cov[(-Real.sin θ) • L₁, (Real.cos θ) • L₂; μ]
          + Var[(Real.cos θ) • L₂; μ] :=
    (variance_add (μ := μ) (hL₁.const_smul (-Real.sin θ)) (hL₂.const_smul (Real.cos θ)))
  have hcos2sin2 : (Real.cos θ) ^ 2 + (Real.sin θ) ^ 2 = 1 := by
    simp
  have hv (c : ℝ) (L : StrongDual ℝ H) :
      Var[(c • L : StrongDual ℝ H); μ] = c ^ 2 * Var[L; μ] := by
    convert variance_smul c (L : H → ℝ) μ using 1
  have hc₁ :
      cov[(Real.cos θ • L₁ : StrongDual ℝ H),
        (Real.sin θ) • (L₂ : H → ℝ); μ] =
        Real.cos θ * Real.sin θ * cov[L₁, L₂; μ] := by
    change cov[(Real.cos θ) • (L₁ : H → ℝ),
      (Real.sin θ) • (L₂ : H → ℝ); μ] = _
    rw [covariance_smul_left, covariance_smul_right]
    ring
  have hc₂ :
      cov[(-Real.sin θ • L₁ : StrongDual ℝ H),
        (Real.cos θ) • (L₂ : H → ℝ); μ] =
        (-Real.sin θ) * Real.cos θ * cov[L₁, L₂; μ] := by
    change cov[(-Real.sin θ) • (L₁ : H → ℝ),
      (Real.cos θ) • (L₂ : H → ℝ); μ] = _
    rw [covariance_smul_left, covariance_smul_right]
    ring
  calc
    Var[(Real.cos θ) • L₁ + (Real.sin θ) • L₂; μ]
        + Var[(-Real.sin θ) • L₁ + (Real.cos θ) • L₂; μ]
        = (Real.cos θ) ^ 2 * Var[L₁; μ]
            + (Real.sin θ) ^ 2 * Var[L₁; μ]
            + (Real.sin θ) ^ 2 * Var[L₂; μ]
            + (Real.cos θ) ^ 2 * Var[L₂; μ] := by
          rw [hVar₁, hVar₂]
          rw [hv, hv, hv, hv, hc₁, hc₂]
          ring
    _ = ((Real.cos θ) ^ 2 + (Real.sin θ) ^ 2) * Var[L₁; μ]
          + ((Real.cos θ) ^ 2 + (Real.sin θ) ^ 2) * Var[L₂; μ] := by
          ring
    _ = Var[L₁; μ] + Var[L₂; μ] := by
          simp [hcos2sin2]

/-- The rotation map preserves the product Gaussian law (centered case). -/
lemma map_gaussRotMap_prod (hmean0 : (∫ x : H, x ∂μ) = 0) (θ : ℝ) :
    (μ.prod μ).map (gaussRotMap (H := H) θ) = μ.prod μ := by
  let P : Measure (H × H) := μ.prod μ
  let Q : Measure (H × H) := P.map (gaussRotMap (H := H) θ)
  haveI : IsGaussian P := by infer_instance
  haveI : IsGaussian Q := by infer_instance
  have hPmean : P[id] = (0 : H × H) := by
    have hInt : Integrable (id : (H × H) → (H × H)) P := IsGaussian.integrable_id (μ := P)
    have hfst :
        (∫ x : H × H, x ∂P).1 = 0 := by
      have hproj :
          (∫ x : H × H, x ∂P).1 = ∫ x : H × H, x.1 ∂P := by
        simpa using
          (ContinuousLinearMap.integral_comp_comm (ContinuousLinearMap.fst ℝ H H) hInt).symm
      have : (∫ x : H × H, x.1 ∂P) = 0 := by
        calc
          (∫ x : H × H, x.1 ∂P)
              = μ.real Set.univ • ∫ x : H, x ∂μ := by
                  simpa [P] using (integral_fun_fst (μ := μ) (ν := μ) (f := (id : H → H)))
          _ = 0 := by simp [probReal_univ, hmean0]
      simpa [hproj] using this
    have hsnd :
        (∫ x : H × H, x ∂P).2 = 0 := by
      have hproj :
          (∫ x : H × H, x ∂P).2 = ∫ x : H × H, x.2 ∂P := by
        simpa using
          (ContinuousLinearMap.integral_comp_comm (ContinuousLinearMap.snd ℝ H H) hInt).symm
      have : (∫ x : H × H, x.2 ∂P) = 0 := by
        calc
          (∫ x : H × H, x.2 ∂P)
              = μ.real Set.univ • ∫ x : H, x ∂μ := by
                  simpa [P] using (integral_fun_snd (μ := μ) (ν := μ) (f := (id : H → H)))
          _ = 0 := by simp [probReal_univ, hmean0]
      simpa [hproj] using this
    ext
    · simpa using hfst
    · simpa using hsnd
  have hQmean : Q[id] = (0 : H × H) := by
    have hInt : Integrable (id : (H × H) → (H × H)) P := IsGaussian.integrable_id (μ := P)
    have hMap : AEMeasurable (gaussRotMap (H := H) θ) P := by fun_prop
    have hId : AEStronglyMeasurable (id : (H × H) → (H × H)) Q := by
      simpa [Q] using (aestronglyMeasurable_id : AEStronglyMeasurable (id : (H × H) → (H × H)) Q)
    have :
        (∫ x : H × H, x ∂Q) = ∫ x : H × H, gaussRotMap (H := H) θ x ∂P := by
      simpa [Q] using (integral_map (μ := P) (φ := gaussRotMap (H := H) θ) (f := (id : (H × H) → (H × H)))
        hMap hId)
    have hZero : (∫ x : H × H, gaussRotMap (H := H) θ x ∂P) = 0 := by
      have hPmean_int : (∫ x : H × H, x ∂P) = (0 : H × H) := by
        simpa using (hPmean : P[id] = (0 : H × H))
      have h :=
        (ContinuousLinearMap.integral_comp_comm (gaussRotMap (H := H) θ) hInt)
      change (∫ x : H × H, gaussRotMap (H := H) θ x ∂P) = (0, 0)
      simpa [hPmean_int, gaussRotMap_apply, gaussRot, gaussRotOrtho] using h
    simpa [this, hZero]
  have hm : P[id] = Q[id] := by
    calc
      P[id] = (0 : H × H) := hPmean
      _ = Q[id] := hQmean.symm
  have hLpP : MemLp (id : (H × H) → (H × H)) 2 P := IsGaussian.memLp_two_id (μ := P)
  have hLpQ : MemLp (id : (H × H) → (H × H)) 2 Q := IsGaussian.memLp_two_id (μ := Q)
  have hv : covarianceBilinDual P = covarianceBilinDual Q := by
    apply (ContinuousLinearMap.toBilinForm_inj (covarianceBilinDual P) (covarianceBilinDual Q)).1
    refine LinearMap.BilinForm.ext_of_isSymm
      (isPosSemidef_covarianceBilinDual.isSymm) (isPosSemidef_covarianceBilinDual.isSymm) ?_
    intro L
    have hdiag :
        covarianceBilinDual P L L = covarianceBilinDual Q L L := by
      simp [covarianceBilinDual_self_eq_variance, hLpP, hLpQ]
      have hVar : Var[L; Q] = Var[L; P] := by
        have hLQ : AEMeasurable (L : (H × H) → ℝ) Q := by fun_prop
        have hMap : AEMeasurable (gaussRotMap (H := H) θ) P := by fun_prop
        have hVar_map :
            Var[(L : (H × H) → ℝ); Q] = Var[(L : (H × H) → ℝ) ∘ gaussRotMap (H := H) θ; P] := by
          simpa [Q] using (variance_map (μ := P) (X := (L : (H × H) → ℝ))
            (Y := gaussRotMap (H := H) θ) hLQ hMap)
        have hId : MemLp (id : H → H) 2 μ := IsGaussian.memLp_two_id (μ := μ)
        have hVarP : Var[L; P] = Var[L.comp (.inl ℝ H H); μ] + Var[L.comp (.inr ℝ H H); μ] := by
          simpa [P] using (variance_dual_prod (E := H) (F := H) (μ := μ) (ν := μ) (L := L) hId hId)
        have hVarRot :
            Var[(L : (H × H) → ℝ) ∘ gaussRotMap (H := H) θ; P]
              = Var[(L.comp (gaussRotMap (H := H) θ)).comp (.inl ℝ H H); μ]
                + Var[(L.comp (gaussRotMap (H := H) θ)).comp (.inr ℝ H H); μ] := by
          change Var[(L.comp (gaussRotMap (H := H) θ) : (H × H) → ℝ); P] = _
          simpa [P] using
            (variance_dual_prod (E := H) (F := H) (μ := μ) (ν := μ)
              (L := (L.comp (gaussRotMap (H := H) θ))) hId hId)
        set L₁ : StrongDual ℝ H := L.comp (.inl ℝ H H)
        set L₂ : StrongDual ℝ H := L.comp (.inr ℝ H H)
        have hInl :
            (L.comp (gaussRotMap (H := H) θ)).comp (.inl ℝ H H)
              = (Real.cos (-θ)) • L₁ + (Real.sin (-θ)) • L₂ := by
          ext x
          have hdecomp :
              L (Real.cos θ • x, -(Real.sin θ • x))
                = L₁ (Real.cos θ • x) + L₂ (-(Real.sin θ • x)) := by
            simpa [L₁, L₂] using
              (ContinuousLinearMap.comp_inl_add_comp_inr (L := L) (v := (Real.cos θ • x, -(Real.sin θ • x)))).symm
          have hL0 : L (0, -(Real.sin θ • x)) = -(Real.sin θ * L (0, x)) := by
            calc
              L (0, -(Real.sin θ • x)) = L₂ (-(Real.sin θ • x)) := by simp [L₂]
              _ = -(L₂ (Real.sin θ • x)) := by simp
              _ = -(Real.sin θ * L₂ x) := by simp [map_smul, smul_eq_mul]
              _ = -(Real.sin θ * L (0, x)) := by simp [L₂]
          simp [L₁, L₂, gaussRotMap_apply, gaussRot, gaussRotOrtho,
            ContinuousLinearMap.comp_apply, Real.cos_neg, Real.sin_neg, hdecomp, hL0,
            add_comm, smul_eq_mul]
        have hInr :
            (L.comp (gaussRotMap (H := H) θ)).comp (.inr ℝ H H)
              = (-Real.sin (-θ)) • L₁ + (Real.cos (-θ)) • L₂ := by
          ext x
          have hdecomp :
              L (Real.sin θ • x, Real.cos θ • x)
                = L₁ (Real.sin θ • x) + L₂ (Real.cos θ • x) := by
            simpa [L₁, L₂] using
              (ContinuousLinearMap.comp_inl_add_comp_inr (L := L) (v := (Real.sin θ • x, Real.cos θ • x))).symm
          simp [L₁, L₂, gaussRotMap_apply, gaussRot, gaussRotOrtho, ContinuousLinearMap.comp_apply,
            Real.cos_neg, Real.sin_neg, hdecomp, add_comm, smul_eq_mul]
        have hRotate :
            Var[(Real.cos (-θ)) • L₁ + (Real.sin (-θ)) • L₂; μ]
              + Var[(-Real.sin (-θ)) • L₁ + (Real.cos (-θ)) • L₂; μ]
              = Var[L₁; μ] + Var[L₂; μ] :=
          variance_gaussRot_components (μ := μ) (H := H) (-θ) L₁ L₂
        have : Var[(L : (H × H) → ℝ) ∘ gaussRotMap (H := H) θ; P] = Var[L; P] := by
          rw [hVarRot, hVarP]
          simpa [hInl, hInr, L₁, L₂] using hRotate
        exact (hVar_map.trans this).trans rfl
      simp [hVar]
    simpa using hdiag
  simpa [P, Q] using (ProbabilityTheory.IsGaussian.ext_covarianceBilinDual (μ := P) (ν := Q) hm hv).symm

/-!
### Main variance bound will go here.
-/

section PoincareAux

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable {ν : Measure F} [IsGaussian ν]

/-- A (centered) Gaussian second-moment bound for continuous linear functionals.

This is the `L²` input used in the Poincaré/variance argument: under `∫ x, x ∂ν = 0`,
the second moment of any `L : StrongDual ℝ F` is controlled by `‖covarianceOperator ν‖ * ‖L‖²`. -/
lemma integral_sq_dual_le_opNorm_covarianceOperator (hmean0 : (∫ x : F, x ∂ν) = 0)
    (L : StrongDual ℝ F) :
    (∫ x : F, (L x) ^ 2 ∂ν) ≤ ‖covarianceOperator ν‖ * ‖L‖ ^ 2 := by
  let h : F := (InnerProductSpace.toDual ℝ F).symm L
  have hL : ∀ x : F, L x = ⟪h, x⟫ := by
    intro x
    simp [h]
  have hInt : Integrable (id : F → F) ν := IsGaussian.integrable_id (μ := ν)
  have hmeanL : ν[L] = 0 := by
    have : ν[L] = L (∫ x : F, x ∂ν) := by
      simpa using (L.integral_comp_comm hInt)
    simpa [hmean0] using this
  have hLp2 : MemLp (id : F → F) 2 ν := IsGaussian.memLp_two_id (μ := ν)
  have hEq : (∫ x : F, (L x) ^ 2 ∂ν) = ⟪covarianceOperator ν h, h⟫ := by
    calc
      (∫ x : F, (L x) ^ 2 ∂ν) = ∫ x : F, ⟪h, x⟫ ^ 2 ∂ν := by
        simp [hL]
      _ = ⟪covarianceOperator ν h, h⟫ := by
        have : ⟪covarianceOperator ν h, h⟫ = ∫ x : F, ⟪h, x⟫ ^ 2 ∂ν := by
          simpa [pow_two] using (covarianceOperator_inner (μ := ν) hLp2 h h)
        simp [this]
  calc
    (∫ x : F, (L x) ^ 2 ∂ν) = ⟪covarianceOperator ν h, h⟫ := hEq
    _ ≤ ‖covarianceOperator ν h‖ * ‖h‖ := real_inner_le_norm _ _
    _ ≤ (‖covarianceOperator ν‖ * ‖h‖) * ‖h‖ := by
          gcongr
          exact (covarianceOperator ν).le_opNorm h
    _ = ‖covarianceOperator ν‖ * ‖h‖ ^ 2 := by ring
    _ = ‖covarianceOperator ν‖ * ‖L‖ ^ 2 := by
          simp [h]

end PoincareAux

/-!
### Gaussian variance bound (bounded derivative form)
-/

section PoincareBound

open scoped Interval

variable (hmean0 : (∫ x : H, x ∂μ) = 0)

private lemma hasDerivAt_gaussRot (θ : ℝ) (p : H × H) :
    HasDerivAt (fun t : ℝ => gaussRot (H := H) t p) (gaussRotOrtho (H := H) θ p) θ := by
  convert ((Real.hasDerivAt_cos θ).smul_const p.1).add
      ((Real.hasDerivAt_sin θ).smul_const p.2) using 1
  · funext t
    rfl
  · simp [gaussRotOrtho, sub_eq_add_neg, add_comm]

private lemma hasDerivAt_comp_gaussRot {f : H → ℝ} (hf : ContDiff ℝ 1 f) (θ : ℝ) (p : H × H) :
    HasDerivAt (fun t : ℝ => f (gaussRot (H := H) t p))
      ((fderiv ℝ f (gaussRot (H := H) θ p)) (gaussRotOrtho (H := H) θ p)) θ := by
  have hf' : DifferentiableAt ℝ f (gaussRot (H := H) θ p) :=
    (hf.differentiable (by simp)).differentiableAt
  have hF : HasFDerivAt f (fderiv ℝ f (gaussRot (H := H) θ p)) (gaussRot (H := H) θ p) :=
    hf'.hasFDerivAt
  convert (hF.comp_hasDerivAt θ
    (hasDerivAt_gaussRot (H := H) θ p)) using 1 <;> rfl

/-!
We will need a simple Cauchy–Schwarz estimate for interval integrals:
\[
  \Bigl(\int_a^b g(t)\,dt\Bigr)^2 \le (b-a)\int_a^b g(t)^2\,dt.
\]

We prove this via Hölder on the restricted Lebesgue measure on `Ioc a b`.
-/
private lemma sq_intervalIntegral_le_sub_mul_integral_sq {a b : ℝ} (hab : a ≤ b)
    {g : ℝ → ℝ} (hg : MemLp g 2 (volume.restrict (Set.Ioc a b))) :
    (∫ t in a..b, g t) ^ 2 ≤ (b - a) * ∫ t in a..b, (g t) ^ 2 := by
  have hI : (∫ t in a..b, g t) = ∫ t in Set.Ioc a b, g t ∂volume := by
    simp [intervalIntegral.integral_of_le hab]
  have hI2 : (∫ t in a..b, (g t) ^ 2) = ∫ t in Set.Ioc a b, (g t) ^ 2 ∂volume := by
    simp [intervalIntegral.integral_of_le hab]
  have hvol : (volume (Set.Ioc a b)) < ∞ := by
    simp [volume_Ioc]
  haveI : Fact ((volume : Measure ℝ) (Set.Ioc a b) < ∞) := ⟨hvol⟩
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) := by infer_instance
  have h1 :
      |∫ t in Set.Ioc a b, g t ∂volume| ≤ ∫ t in Set.Ioc a b, |g t| ∂volume := by
    simpa using
      (abs_integral_le_integral_abs (μ := volume.restrict (Set.Ioc a b)) (f := g))
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) (volume.restrict (Set.Ioc a b)) := by
    simpa using hg
  have hconst :
      MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) (volume.restrict (Set.Ioc a b)) := by
    simpa using
      (memLp_const (μ := volume.restrict (Set.Ioc a b)) (p := ENNReal.ofReal (2 : ℝ)) (c := (1 : ℝ)))
  have habs :
      MemLp (fun t : ℝ => |g t|) (ENNReal.ofReal (2 : ℝ)) (volume.restrict (Set.Ioc a b)) := by
    exact hg'.abs
  have h2 :
      (∫ t in Set.Ioc a b, |g t| ∂volume)
        ≤ (∫ t in Set.Ioc a b, (1 : ℝ) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))
            * (∫ t in Set.Ioc a b, |g t| ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) := by
    simpa [Real.norm_eq_abs, abs_abs, mul_comm, mul_left_comm, mul_assoc, one_mul] using
      (integral_mul_norm_le_Lp_mul_Lq (μ := volume.restrict (Set.Ioc a b))
        (p := (2 : ℝ)) (q := (2 : ℝ))
        (hpq := by
          simpa using (Real.HolderConjugate.two_two : (2 : ℝ).HolderConjugate (2 : ℝ)))
        hconst habs)
  have hlen : (∫ t in Set.Ioc a b, (1 : ℝ) ^ (2 : ℝ) ∂volume) = (b - a) := by
    simp [hab]
  have hsq :
      (∫ t in Set.Ioc a b, |g t| ^ (2 : ℝ) ∂volume) = ∫ t in Set.Ioc a b, (g t) ^ 2 ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards with t
    simp
  have hset :
      |∫ t in Set.Ioc a b, g t ∂volume| ^ 2
        ≤ (b - a) * ∫ t in Set.Ioc a b, (g t) ^ 2 ∂volume := by
    have h12 :
        |∫ t in Set.Ioc a b, g t ∂volume|
          ≤ (∫ t in Set.Ioc a b, (1 : ℝ) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))
              * (∫ t in Set.Ioc a b, |g t| ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) := by
      exact le_trans h1 h2
    have hsq' :
        |∫ t in Set.Ioc a b, g t ∂volume| ^ 2
          ≤ ((∫ t in Set.Ioc a b, (1 : ℝ) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))
              * (∫ t in Set.Ioc a b, |g t| ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))) ^ 2 := by
      simpa [pow_two] using (mul_self_le_mul_self (abs_nonneg _) h12)
    have hA0 : 0 ≤ ∫ t in Set.Ioc a b, (1 : ℝ) ^ (2 : ℝ) ∂volume := by
      refine integral_nonneg (fun _ => ?_)
      simp
    have hB0 : 0 ≤ ∫ t in Set.Ioc a b, |g t| ^ (2 : ℝ) ∂volume := by
      refine integral_nonneg (fun t => ?_)
      exact Real.rpow_nonneg (abs_nonneg (g t)) _
    have hsquare :
        ((∫ t in Set.Ioc a b, (1 : ℝ) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))
            * (∫ t in Set.Ioc a b, |g t| ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))) ^ 2
          = (∫ t in Set.Ioc a b, (1 : ℝ) ^ (2 : ℝ) ∂volume)
              * (∫ t in Set.Ioc a b, |g t| ^ (2 : ℝ) ∂volume) := by
      rw [(Real.sqrt_eq_rpow _).symm, (Real.sqrt_eq_rpow _).symm]
      calc
        ((Real.sqrt (∫ t in Set.Ioc a b, (1 : ℝ) ^ (2 : ℝ) ∂volume)
              * Real.sqrt (∫ t in Set.Ioc a b, |g t| ^ (2 : ℝ) ∂volume)) ^ 2)
            =
            (Real.sqrt (∫ t in Set.Ioc a b, (1 : ℝ) ^ (2 : ℝ) ∂volume)) ^ 2
              * (Real.sqrt (∫ t in Set.Ioc a b, |g t| ^ (2 : ℝ) ∂volume)) ^ 2 := by
              simpa using
                (mul_pow
                  (Real.sqrt (∫ t in Set.Ioc a b, (1 : ℝ) ^ (2 : ℝ) ∂volume))
                  (Real.sqrt (∫ t in Set.Ioc a b, |g t| ^ (2 : ℝ) ∂volume)) 2)
        _ = (∫ t in Set.Ioc a b, (1 : ℝ) ^ (2 : ℝ) ∂volume)
              * (∫ t in Set.Ioc a b, |g t| ^ (2 : ℝ) ∂volume) := by
              have hsqrtA :
                  (Real.sqrt (∫ t in Set.Ioc a b, (1 : ℝ) ^ (2 : ℝ) ∂volume)) ^ 2
                    = ∫ t in Set.Ioc a b, (1 : ℝ) ^ (2 : ℝ) ∂volume :=
                Real.sq_sqrt hA0
              have hsqrtB :
                  (Real.sqrt (∫ t in Set.Ioc a b, |g t| ^ (2 : ℝ) ∂volume)) ^ 2
                    = ∫ t in Set.Ioc a b, |g t| ^ (2 : ℝ) ∂volume :=
                Real.sq_sqrt hB0
              rw [hsqrtA, hsqrtB]
    refine le_trans hsq' ?_
    rw [hsquare, hlen, hsq]
  have hset' :
      (∫ t in Set.Ioc a b, g t ∂volume) ^ 2
        ≤ (b - a) * ∫ t in Set.Ioc a b, (g t) ^ 2 ∂volume := by
    simpa [sq_abs] using hset
  simpa [hI, hI2] using hset'

/-- **Gaussian variance bound (Poincaré-type, bounded derivative form).**

For a centered Gaussian measure `μ` on a real Hilbert space `H`, any `C¹` functional `f` with a
uniform derivative bound `‖fderiv f x‖ ≤ K` satisfies
`Var[f; μ] ≤ (π^2 / 8) * ‖covarianceOperator μ‖ * K^2`.

The constant `π^2 / 8` comes from the rotation smart path on `[0, π/2]` together with a
Cauchy–Schwarz estimate for interval integrals. -/
theorem variance_le_pi_sq_div_eight_mul_opNorm_covarianceOperator_mul_bound_sq
    (hmean0 : (∫ x : H, x ∂μ) = 0) {f : H → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ} (hK : 0 ≤ K)
    (hderiv : ∀ x, ‖fderiv ℝ f x‖ ≤ K) :
    Var[f; μ] ≤ (Real.pi ^ 2 / 8) * ‖covarianceOperator μ‖ * K ^ 2 := by
  classical
  by_cases hfLp : MemLp f 2 μ
  · let b : ℝ := Real.pi / 2
    have hb0 : (0 : ℝ) ≤ b := by
      simpa [b] using (Real.pi_div_two_pos.le)
    let P : Measure (H × H) := μ.prod μ
    have hVar :
        Var[f; μ] = (1 / (2 : ℝ)) * ∫ p : H × H, (f p.1 - f p.2) ^ 2 ∂P := by
      have hVarDiff :
          Var[(fun p : H × H => f p.1 - f p.2); P] = 2 * Var[f; μ] := by
        have h :=
          (variance_add_prod (μ := μ) (ν := μ) (X := f) (Y := fun x : H => -f x) hfLp hfLp.neg)
        simpa [P, sub_eq_add_neg, variance_fun_neg, two_mul, add_assoc, add_comm, add_left_comm] using h
      have hMean0 : P[fun p : H × H => f p.1 - f p.2] = 0 := by
        have hfInt : Integrable f μ := hfLp.integrable (by simp)
        have hfInt_fst : Integrable (fun p : H × H => f p.1) P := (hfInt.comp_fst μ)
        have hfInt_snd : Integrable (fun p : H × H => f p.2) P := (hfInt.comp_snd μ)
        calc
          P[fun p : H × H => f p.1 - f p.2]
              = ∫ p : H × H, (f p.1 - f p.2) ∂P := rfl
          _ = (∫ p : H × H, f p.1 ∂P) - ∫ p : H × H, f p.2 ∂P := by
                simpa using (integral_sub hfInt_fst hfInt_snd)
          _ = (∫ x : H, f x ∂μ) - ∫ x : H, f x ∂μ := by
                simp [P, integral_fun_fst, integral_fun_snd, probReal_univ]
          _ = 0 := by ring
      have hMeasDiff : AEMeasurable (fun p : H × H => f p.1 - f p.2) P := by
        have hf_meas : Measurable f := hf.continuous.measurable
        exact (hf_meas.comp measurable_fst).aemeasurable.sub (hf_meas.comp measurable_snd).aemeasurable
      have hVarDiffInt :
          Var[(fun p : H × H => f p.1 - f p.2); P]
            = ∫ p : H × H, (f p.1 - f p.2) ^ 2 ∂P := by
        simpa [P] using (variance_of_integral_eq_zero (μ := P) hMeasDiff hMean0)
      have hInt :
          ∫ p : H × H, (f p.1 - f p.2) ^ 2 ∂P = 2 * Var[f; μ] := by
        calc
          ∫ p : H × H, (f p.1 - f p.2) ^ 2 ∂P
              = Var[(fun p : H × H => f p.1 - f p.2); P] := by simp [hVarDiffInt]
          _ = 2 * Var[f; μ] := hVarDiff
      calc
        Var[f; μ] = (1 / (2 : ℝ)) * (2 * Var[f; μ]) := by ring
        _ = (1 / (2 : ℝ)) * ∫ p : H × H, (f p.1 - f p.2) ^ 2 ∂P := by
              rw [← hInt]
    let d : ℝ → H × H → ℝ := fun θ p =>
      (fderiv ℝ f (gaussRot (H := H) θ p)) (gaussRotOrtho (H := H) θ p)
    have hOrtho_le (θ : ℝ) (p : H × H) :
        ‖gaussRotOrtho (H := H) θ p‖ ≤ ‖p.1‖ + ‖p.2‖ := by
      have h1 :
          ‖-Real.sin θ • p.1‖ ≤ ‖p.1‖ := by
        have : |Real.sin θ| * ‖p.1‖ ≤ ‖p.1‖ := by
          have := mul_le_mul_of_nonneg_right (abs_sin_le_one θ) (norm_nonneg p.1)
          simpa [one_mul] using this
        simpa [gaussRotOrtho, norm_smul, abs_neg] using this
      have h2 :
          ‖Real.cos θ • p.2‖ ≤ ‖p.2‖ := by
        have : |Real.cos θ| * ‖p.2‖ ≤ ‖p.2‖ := by
          have := mul_le_mul_of_nonneg_right (abs_cos_le_one θ) (norm_nonneg p.2)
          simpa [one_mul] using this
        simpa [norm_smul] using this
      calc
        ‖gaussRotOrtho (H := H) θ p‖
            = ‖-Real.sin θ • p.1 + Real.cos θ • p.2‖ := by simp [gaussRotOrtho]
        _ ≤ ‖-Real.sin θ • p.1‖ + ‖Real.cos θ • p.2‖ := norm_add_le _ _
        _ ≤ ‖p.1‖ + ‖p.2‖ := add_le_add h1 h2
    have hdiff_sq (p : H × H) :
        (f p.1 - f p.2) ^ 2 ≤ b * ∫ θ in 0..b, (d θ p) ^ 2 := by
      have hFTC :
          ∫ θ in 0..b, d θ p = f p.2 - f p.1 := by
        have hgauss : Continuous (fun θ : ℝ => gaussRot (H := H) θ p) := by
          simpa [gaussRot] using (by fun_prop : Continuous fun θ : ℝ =>
            Real.cos θ • p.1 + Real.sin θ • p.2)
        have hcont :
            ContinuousOn (fun θ : ℝ => f (gaussRot (H := H) θ p)) (Set.Icc 0 b) := by
          change ContinuousOn
            (f ∘ fun θ : ℝ => gaussRot (H := H) θ p) (Set.Icc 0 b)
          exact (hf.continuous.comp hgauss).continuousOn
        have hder :
            ∀ θ ∈ Set.Ioo 0 b,
              HasDerivAt (fun t : ℝ => f (gaussRot (H := H) t p)) (d θ p) θ := by
          intro θ _hθ
          simpa [d] using (hasDerivAt_comp_gaussRot (H := H) (f := f) hf θ p)
        have hDf :
            Continuous fun q : H × H => (fderiv ℝ f q.1 : H → ℝ) q.2 :=
          hf.continuous_fderiv_apply (by simp)
        have hpair : Continuous fun θ : ℝ =>
            (gaussRot (H := H) θ p, gaussRotOrtho (H := H) θ p) := by
          simpa [gaussRot, gaussRotOrtho] using (by fun_prop : Continuous fun θ : ℝ =>
            (Real.cos θ • p.1 + Real.sin θ • p.2, -Real.sin θ • p.1 + Real.cos θ • p.2))
        have hcontd : Continuous (fun θ : ℝ => d θ p) := by
          change Continuous ((fun q : H × H =>
            (fderiv ℝ f q.1 : H → ℝ) q.2) ∘ fun θ : ℝ =>
              (gaussRot (H := H) θ p, gaussRotOrtho (H := H) θ p))
          exact hDf.comp hpair
        have hint : IntervalIntegrable (fun θ : ℝ => d θ p) (volume : Measure ℝ) 0 b :=
          hcontd.intervalIntegrable (μ := (volume : Measure ℝ)) 0 b
        have h :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (0 : ℝ)) (b := b)
            hb0 hcont hder hint
        simpa [b, gaussRot, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two] using h
      have hvol : (volume (Set.Ioc (0 : ℝ) b)) < ∞ := by
        simpa [volume_Ioc] using (ENNReal.ofReal_lt_top (b - (0 : ℝ)))
      haveI : Fact ((volume : Measure ℝ) (Set.Ioc (0 : ℝ) b) < ∞) := ⟨hvol⟩
      haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) b)) := by infer_instance
      have hmeas : AEStronglyMeasurable (fun θ : ℝ => d θ p) (volume.restrict (Set.Ioc (0 : ℝ) b)) := by
        have hDf :
            Continuous fun q : H × H => (fderiv ℝ f q.1 : H → ℝ) q.2 :=
          hf.continuous_fderiv_apply (by simp)
        have hpair : Continuous fun θ : ℝ =>
            (gaussRot (H := H) θ p, gaussRotOrtho (H := H) θ p) := by
          simpa [gaussRot, gaussRotOrtho] using (by fun_prop : Continuous fun θ : ℝ =>
            (Real.cos θ • p.1 + Real.sin θ • p.2, -Real.sin θ • p.1 + Real.cos θ • p.2))
        have hcontd : Continuous (fun θ : ℝ => d θ p) := by
          change Continuous ((fun q : H × H =>
            (fderiv ℝ f q.1 : H → ℝ) q.2) ∘ fun θ : ℝ =>
              (gaussRot (H := H) θ p, gaussRotOrtho (H := H) θ p))
          exact hDf.comp hpair
        exact hcontd.aestronglyMeasurable
      have hbound :
          ∀ᵐ θ ∂(volume.restrict (Set.Ioc (0 : ℝ) b)), ‖d θ p‖ ≤ K * (‖p.1‖ + ‖p.2‖) := by
        refine Filter.Eventually.of_forall (fun θ => ?_)
        have hL :
            ‖d θ p‖ ≤ ‖fderiv ℝ f (gaussRot (H := H) θ p)‖ * ‖gaussRotOrtho (H := H) θ p‖ := by
          simpa [d] using
            (ContinuousLinearMap.le_opNorm (fderiv ℝ f (gaussRot (H := H) θ p))
              (gaussRotOrtho (H := H) θ p))
        have hL' : ‖fderiv ℝ f (gaussRot (H := H) θ p)‖ ≤ K :=
          hderiv (gaussRot (H := H) θ p)
        have : ‖d θ p‖ ≤ K * (‖p.1‖ + ‖p.2‖) := by
          calc
            ‖d θ p‖ ≤ ‖fderiv ℝ f (gaussRot (H := H) θ p)‖ * ‖gaussRotOrtho (H := H) θ p‖ := hL
            _ ≤ K * ‖gaussRotOrtho (H := H) θ p‖ := by
                  gcongr
            _ ≤ K * (‖p.1‖ + ‖p.2‖) := by
                  gcongr
                  exact hOrtho_le θ p
        simpa using this
      have hMemLp :
          MemLp (fun θ : ℝ => d θ p) 2 (volume.restrict (Set.Ioc (0 : ℝ) b)) :=
        MemLp.of_bound hmeas (C := K * (‖p.1‖ + ‖p.2‖)) hbound
      have hCS :=
        sq_intervalIntegral_le_sub_mul_integral_sq (a := (0 : ℝ)) (b := b) hb0 (g := fun θ => d θ p) hMemLp
      have :
          (f p.2 - f p.1) ^ 2 ≤ b * ∫ θ in 0..b, (d θ p) ^ 2 := by
        simpa [hFTC] using hCS
      calc
        (f p.1 - f p.2) ^ 2 = (f p.2 - f p.1) ^ 2 := by ring
        _ ≤ b * ∫ θ in 0..b, (d θ p) ^ 2 := this
    have hvol_u : (volume (Set.uIoc (0 : ℝ) b)) < ∞ := by simp [volume_uIoc]
    haveI : Fact ((volume : Measure ℝ) (Set.uIoc (0 : ℝ) b) < ∞) := ⟨hvol_u⟩
    haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) b)) := by infer_instance
    have hIdLp2 : MemLp (id : H → H) 2 μ := IsGaussian.memLp_two_id (μ := μ)
    have hNormLp2 : MemLp (fun x : H => ‖x‖) 2 μ := hIdLp2.norm
    have hNorm_fst : MemLp (fun p : H × H => ‖p.1‖) 2 P := hNormLp2.comp_fst μ
    have hNorm_snd : MemLp (fun p : H × H => ‖p.2‖) 2 P := hNormLp2.comp_snd μ
    have hSum : MemLp (fun p : H × H => ‖p.1‖ + ‖p.2‖) 2 P := hNorm_fst.add hNorm_snd
    have hSumSq : Integrable (fun p : H × H => (‖p.1‖ + ‖p.2‖) ^ 2) P :=
      hSum.integrable_sq
    have hG0 : Integrable (fun p : H × H => (K * (‖p.1‖ + ‖p.2‖)) ^ 2) P := by
      have h' : Integrable (fun p : H × H => (K ^ 2) * (‖p.1‖ + ‖p.2‖) ^ 2) P :=
        hSumSq.const_mul (K ^ 2)
      have :
          (fun p : H × H => (K * (‖p.1‖ + ‖p.2‖)) ^ 2)
            = fun p : H × H => (K ^ 2) * (‖p.1‖ + ‖p.2‖) ^ 2 := by
        funext p
        ring
      simpa [this] using h'
    have hG :
        Integrable (fun z : ℝ × (H × H) => (K * (‖z.2.1‖ + ‖z.2.2‖)) ^ 2)
          ((volume.restrict (Set.uIoc (0 : ℝ) b)).prod P) := by
      simpa [P] using (hG0.comp_snd (μ := volume.restrict (Set.uIoc (0 : ℝ) b)))
    have hInt_uncurry :
        Integrable (Function.uncurry (fun θ : ℝ => fun p : H × H => (d θ p) ^ 2))
          ((volume.restrict (Set.uIoc (0 : ℝ) b)).prod P) := by
      have hDf :
          Continuous fun q : H × H => (fderiv ℝ f q.1 : H → ℝ) q.2 :=
        hf.continuous_fderiv_apply (by simp)
      have hpair : Continuous fun z : ℝ × (H × H) =>
          (gaussRot (H := H) z.1 z.2, gaussRotOrtho (H := H) z.1 z.2) := by
        simpa [gaussRot, gaussRotOrtho] using (by fun_prop : Continuous fun z : ℝ × (H × H) =>
          (Real.cos z.1 • z.2.1 + Real.sin z.1 • z.2.2,
            -Real.sin z.1 • z.2.1 + Real.cos z.1 • z.2.2))
      have hcont_d : Continuous (fun z : ℝ × (H × H) => d z.1 z.2) := by
        change Continuous ((fun q : H × H =>
          (fderiv ℝ f q.1 : H → ℝ) q.2) ∘ fun z : ℝ × (H × H) =>
            (gaussRot (H := H) z.1 z.2, gaussRotOrtho (H := H) z.1 z.2))
        exact hDf.comp hpair
      have hmeas :
          AEStronglyMeasurable
            (Function.uncurry (fun θ : ℝ => fun p : H × H => (d θ p) ^ 2))
            ((volume.restrict (Set.uIoc (0 : ℝ) b)).prod P) := by
        have : Continuous
            (Function.uncurry (fun θ : ℝ => fun p : H × H => (d θ p) ^ 2)) := by
          change Continuous (fun z : ℝ × (H × H) => (d z.1 z.2) ^ 2)
          exact hcont_d.pow 2
        exact this.aestronglyMeasurable
      have hdom :
          ∀ᵐ z ∂((volume.restrict (Set.uIoc (0 : ℝ) b)).prod P),
            ‖Function.uncurry (fun θ : ℝ => fun p : H × H => (d θ p) ^ 2) z‖
              ≤ (K * (‖z.2.1‖ + ‖z.2.2‖)) ^ 2 := by
        refine Filter.Eventually.of_forall (fun z => ?_)
        rcases z with ⟨θ, p⟩
        have hθ :
            ‖d θ p‖ ≤ K * (‖p.1‖ + ‖p.2‖) := by
          have hL :
              ‖d θ p‖ ≤ ‖fderiv ℝ f (gaussRot (H := H) θ p)‖ * ‖gaussRotOrtho (H := H) θ p‖ := by
            simpa [d] using
              (ContinuousLinearMap.le_opNorm (fderiv ℝ f (gaussRot (H := H) θ p))
                (gaussRotOrtho (H := H) θ p))
          have hL' : ‖fderiv ℝ f (gaussRot (H := H) θ p)‖ ≤ K :=
            hderiv (gaussRot (H := H) θ p)
          calc
            ‖d θ p‖ ≤ ‖fderiv ℝ f (gaussRot (H := H) θ p)‖ * ‖gaussRotOrtho (H := H) θ p‖ := hL
            _ ≤ K * ‖gaussRotOrtho (H := H) θ p‖ := by
                  gcongr
            _ ≤ K * (‖p.1‖ + ‖p.2‖) := by
                  gcongr
                  exact hOrtho_le θ p
        have hθ' : |d θ p| ≤ K * (‖p.1‖ + ‖p.2‖) := by
          simpa [Real.norm_eq_abs] using hθ
        have hsq : (d θ p) ^ 2 ≤ (K * (‖p.1‖ + ‖p.2‖)) ^ 2 := by
          have : |d θ p| ^ 2 ≤ (K * (‖p.1‖ + ‖p.2‖)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hθ' 2
          simpa [sq_abs] using this
        have hnonneg : 0 ≤ (d θ p) ^ 2 := sq_nonneg _
        simpa [Function.uncurry, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hsq
      exact Integrable.mono' hG hmeas hdom
    have hSwap :
        (∫ p : H × H, (∫ θ in (0 : ℝ)..b, (d θ p) ^ 2) ∂P)
          = ∫ θ in (0 : ℝ)..b, ∫ p : H × H, (d θ p) ^ 2 ∂P := by
      simpa [Function.uncurry] using
        (intervalIntegral_integral_swap (a := (0 : ℝ)) (b := b)
            (μ := P) (f := fun θ (p : H × H) => (d θ p) ^ 2) hInt_uncurry).symm
    have hInv (θ : ℝ) :
        (∫ p : H × H, (d θ p) ^ 2 ∂P)
          = ∫ p : H × H, ((fderiv ℝ f p.1) p.2) ^ 2 ∂P := by
      have hmap : (P.map (gaussRotMap (H := H) θ)) = P := by
        simpa [P] using (map_gaussRotMap_prod (μ := μ) (H := H) hmean0 θ)
      have hMeas : AEMeasurable (gaussRotMap (H := H) θ) P := by fun_prop
      let g : (H × H) → ℝ := fun p => ((fderiv ℝ f p.1) p.2) ^ 2
      have hg_str : AEStronglyMeasurable g (P.map (gaussRotMap (H := H) θ)) := by
        have hcont : Continuous fun q : H × H => (fderiv ℝ f q.1 : H → ℝ) q.2 :=
          hf.continuous_fderiv_apply (by simp)
        have : Continuous g := by
          change Continuous (fun p : H × H =>
            ((fderiv ℝ f p.1) p.2) ^ 2)
          exact hcont.pow 2
        exact this.aestronglyMeasurable
      have hIntMap :
          ∫ p : H × H, g p ∂P.map (gaussRotMap (H := H) θ)
            = ∫ p : H × H, g (gaussRotMap (H := H) θ p) ∂P :=
        integral_map (μ := P) (φ := gaussRotMap (H := H) θ) (f := g) hMeas hg_str
      have : ∫ p : H × H, g (gaussRotMap (H := H) θ p) ∂P = ∫ p : H × H, g p ∂P := by
        simpa [hmap] using hIntMap.symm
      simpa [g, d, gaussRotMap_apply] using this
    have hInt_rhs :
        Integrable (fun p : H × H => b * (∫ θ in (0 : ℝ)..b, (d θ p) ^ 2)) P := by
      have hab : (0 : ℝ) ≤ b := hb0
      have h_int' :
          Integrable (fun z : ℝ × (H × H) => (d z.1 z.2) ^ 2)
            ((volume.restrict (Set.Ioc (0 : ℝ) b)).prod P) := by
        rw [← Set.uIoc_of_le hab]
        exact hInt_uncurry
      have h_inner :
          Integrable (fun p : H × H => ∫ θ : ℝ, (d θ p) ^ 2 ∂(volume.restrict (Set.Ioc (0 : ℝ) b))) P :=
        h_int'.integral_prod_right
      have h_inner' :
          Integrable (fun p : H × H => ∫ θ in (0 : ℝ)..b, (d θ p) ^ 2) P := by
        simpa [intervalIntegral.integral_of_le hab] using h_inner
      exact Integrable.const_mul h_inner' b
    have hInt_diff :
        ∫ p : H × H, (f p.1 - f p.2) ^ 2 ∂P
          ≤ ∫ p : H × H, b * (∫ θ in (0 : ℝ)..b, (d θ p) ^ 2) ∂P := by
      have hnonneg : 0 ≤ᵐ[P] fun p : H × H => (f p.1 - f p.2) ^ 2 :=
        Filter.Eventually.of_forall (fun _ => sq_nonneg _)
      have hAE :
          (fun p : H × H => (f p.1 - f p.2) ^ 2)
            ≤ᵐ[P] fun p : H × H => b * (∫ θ in (0 : ℝ)..b, (d θ p) ^ 2) :=
        ae_of_all _ hdiff_sq
      exact integral_mono_of_nonneg (μ := P) hnonneg hInt_rhs hAE
    have hInt_J :
        (∫ p : H × H, (∫ θ in (0 : ℝ)..b, (d θ p) ^ 2) ∂P)
          = b * ∫ p : H × H, ((fderiv ℝ f p.1) p.2) ^ 2 ∂P := by
      calc
        (∫ p : H × H, (∫ θ in (0 : ℝ)..b, (d θ p) ^ 2) ∂P)
            = ∫ θ in (0 : ℝ)..b, ∫ p : H × H, (d θ p) ^ 2 ∂P := hSwap
        _ = ∫ θ in (0 : ℝ)..b, ∫ p : H × H, ((fderiv ℝ f p.1) p.2) ^ 2 ∂P := by
              refine intervalIntegral.integral_congr (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := b) ?_
              intro θ _hθ
              simpa using (hInv θ)
        _ = b * ∫ p : H × H, ((fderiv ℝ f p.1) p.2) ^ 2 ∂P := by
              simp [intervalIntegral.integral_const, hb0, sub_eq_add_neg, add_comm, add_left_comm,
                add_assoc, mul_assoc]
    have hInt_diff' :
        ∫ p : H × H, (f p.1 - f p.2) ^ 2 ∂P
          ≤ (Real.pi ^ 2 / 4) * ∫ p : H × H, ((fderiv ℝ f p.1) p.2) ^ 2 ∂P := by
      have := hInt_diff
      have hPull :
          (∫ p : H × H, b * (∫ θ in (0 : ℝ)..b, (d θ p) ^ 2) ∂P)
            = b * (∫ p : H × H, (∫ θ in (0 : ℝ)..b, (d θ p) ^ 2) ∂P) := by
        simpa using (integral_const_mul (μ := P) b (fun p : H × H => ∫ θ in (0 : ℝ)..b, (d θ p) ^ 2))
      have hb2 : b * b = Real.pi ^ 2 / 4 := by
        simp [b, pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        norm_num
      calc
        ∫ p : H × H, (f p.1 - f p.2) ^ 2 ∂P
            ≤ b * (∫ p : H × H, (∫ θ in (0 : ℝ)..b, (d θ p) ^ 2) ∂P) := by
                simpa [hPull] using this
        _ = b * (b * ∫ p : H × H, ((fderiv ℝ f p.1) p.2) ^ 2 ∂P) := by
              simp [hInt_J]
        _ = (Real.pi ^ 2 / 4) * ∫ p : H × H, ((fderiv ℝ f p.1) p.2) ^ 2 ∂P := by
              calc
                b * (b * ∫ p : H × H, ((fderiv ℝ f p.1) p.2) ^ 2 ∂P)
                    = (b * b) * ∫ p : H × H, ((fderiv ℝ f p.1) p.2) ^ 2 ∂P := by ring
                _ = (Real.pi ^ 2 / 4) * ∫ p : H × H, ((fderiv ℝ f p.1) p.2) ^ 2 ∂P := by
                      simp [hb2]
    have hC :
        (∫ p : H × H, ((fderiv ℝ f p.1) p.2) ^ 2 ∂P) ≤ ‖covarianceOperator μ‖ * K ^ 2 := by
      let φ : H × H → ℝ := fun p => ((fderiv ℝ f p.1) p.2) ^ 2
      have hφ_int : Integrable φ P := by
        have hNorm_snd' : MemLp (fun p : H × H => ‖p.2‖) 2 P := hNorm_snd
        have hInt_snd_sq : Integrable (fun p : H × H => (‖p.2‖) ^ 2) P :=
          hNorm_snd'.integrable_sq
        have hdom :
            ∀ᵐ p ∂P, ‖φ p‖ ≤ (K ^ 2) * (‖p.2‖) ^ 2 := by
          refine Filter.Eventually.of_forall (fun p => ?_)
          have hL :
              ‖(fderiv ℝ f p.1) p.2‖ ≤ ‖fderiv ℝ f p.1‖ * ‖p.2‖ := by
            simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ f p.1) p.2)
          have hL' : ‖fderiv ℝ f p.1‖ ≤ K := hderiv p.1
          have h' : ‖(fderiv ℝ f p.1) p.2‖ ≤ K * ‖p.2‖ := by
            calc
              ‖(fderiv ℝ f p.1) p.2‖ ≤ ‖fderiv ℝ f p.1‖ * ‖p.2‖ := hL
              _ ≤ K * ‖p.2‖ := by gcongr
          have : (‖(fderiv ℝ f p.1) p.2‖) ^ 2 ≤ (K * ‖p.2‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h' 2
          have : ‖φ p‖ ≤ (K ^ 2) * (‖p.2‖) ^ 2 := by
            simpa [φ, Real.norm_eq_abs, pow_two, mul_assoc, mul_left_comm, mul_comm] using this
          exact this
        have hmeasφ : AEStronglyMeasurable φ P := by
          have hcont : Continuous fun q : H × H => (fderiv ℝ f q.1 : H → ℝ) q.2 :=
            hf.continuous_fderiv_apply (by simp)
          have : Continuous φ := by
            change Continuous (fun p : H × H =>
              ((fderiv ℝ f p.1) p.2) ^ 2)
            exact hcont.pow 2
          exact this.aestronglyMeasurable
        have hboundInt : Integrable (fun p : H × H => (K ^ 2) * (‖p.2‖) ^ 2) P :=
          hInt_snd_sq.const_mul (K ^ 2)
        exact Integrable.mono' hboundInt hmeasφ hdom
      have hFub :
          (∫ p : H × H, φ p ∂P)
            = ∫ x : H, ∫ y : H, ((fderiv ℝ f x) y) ^ 2 ∂μ ∂μ := by
        simpa [P, φ] using (integral_prod (μ := μ) (ν := μ) (f := φ) hφ_int)
      have hInner (x : H) :
          (∫ y : H, ((fderiv ℝ f x) y) ^ 2 ∂μ) ≤ ‖covarianceOperator μ‖ * ‖fderiv ℝ f x‖ ^ 2 := by
        simpa using
          (integral_sq_dual_le_opNorm_covarianceOperator (ν := μ) (hmean0 := hmean0)
            (L := (fderiv ℝ f x)))
      have hInner' (x : H) :
          (∫ y : H, ((fderiv ℝ f x) y) ^ 2 ∂μ) ≤ ‖covarianceOperator μ‖ * K ^ 2 := by
        have hx : ‖fderiv ℝ f x‖ ^ 2 ≤ K ^ 2 := by
          have hx' : ‖fderiv ℝ f x‖ ≤ K := hderiv x
          exact pow_le_pow_left₀ (norm_nonneg _) hx' 2
        exact (hInner x).trans (by gcongr)
      have hnonneg :
          0 ≤ᵐ[μ] fun x : H => ∫ y : H, ((fderiv ℝ f x) y) ^ 2 ∂μ := by
        refine Filter.Eventually.of_forall (fun x => ?_)
        exact integral_nonneg (fun _ => sq_nonneg _)
      have hIntConst : Integrable (fun _x : H => ‖covarianceOperator μ‖ * K ^ 2) μ := by
        simpa using integrable_const (‖covarianceOperator μ‖ * K ^ 2)
      have hAE :
          (fun x : H => ∫ y : H, ((fderiv ℝ f x) y) ^ 2 ∂μ)
            ≤ᵐ[μ] fun _x : H => ‖covarianceOperator μ‖ * K ^ 2 :=
        Filter.Eventually.of_forall hInner'
      have hInt_le :
          (∫ x : H, ∫ y : H, ((fderiv ℝ f x) y) ^ 2 ∂μ ∂μ)
            ≤ ∫ _x : H, ‖covarianceOperator μ‖ * K ^ 2 ∂μ :=
        integral_mono_of_nonneg (μ := μ) hnonneg hIntConst hAE
      calc
        (∫ p : H × H, ((fderiv ℝ f p.1) p.2) ^ 2 ∂P)
            = ∫ x : H, ∫ y : H, ((fderiv ℝ f x) y) ^ 2 ∂μ ∂μ := by
                simpa [φ] using hFub
        _ ≤ ∫ _x : H, ‖covarianceOperator μ‖ * K ^ 2 ∂μ := hInt_le
        _ = ‖covarianceOperator μ‖ * K ^ 2 := by
              simp [probReal_univ]
    have hInt_final :
        ∫ p : H × H, (f p.1 - f p.2) ^ 2 ∂P
          ≤ (Real.pi ^ 2 / 4) * (‖covarianceOperator μ‖ * K ^ 2) := by
      exact (le_trans hInt_diff' (by gcongr))
    have : Var[f; μ] ≤ (Real.pi ^ 2 / 8) * ‖covarianceOperator μ‖ * K ^ 2 := by
      rw [hVar]
      have hhalf : (0 : ℝ) ≤ (1 / (2 : ℝ)) := by positivity
      have hscaled :
          (1 / (2 : ℝ)) * (∫ p : H × H, (f p.1 - f p.2) ^ 2 ∂P)
            ≤ (1 / (2 : ℝ)) * ((Real.pi ^ 2 / 4) * (‖covarianceOperator μ‖ * K ^ 2)) :=
        mul_le_mul_of_nonneg_left hInt_final hhalf
      calc
        (1 / (2 : ℝ)) * (∫ p : H × H, (f p.1 - f p.2) ^ 2 ∂P)
            ≤ (1 / (2 : ℝ)) * ((Real.pi ^ 2 / 4) * (‖covarianceOperator μ‖ * K ^ 2)) := hscaled
        _ = (Real.pi ^ 2 / 8) * ‖covarianceOperator μ‖ * K ^ 2 := by ring
    exact this
  · have hf_meas : AEStronglyMeasurable f μ := hf.continuous.aestronglyMeasurable
    have hVar0 : Var[f; μ] = 0 :=
      variance_of_not_memLp (μ := μ) hf_meas hfLp
    have hRHS : 0 ≤ (Real.pi ^ 2 / 8) * ‖covarianceOperator μ‖ * K ^ 2 := by
      have hpi : 0 ≤ (Real.pi ^ 2 / 8 : ℝ) := by
        have : 0 ≤ (Real.pi ^ 2 : ℝ) := by exact pow_two_nonneg _
        nlinarith
      have hpiSigma : 0 ≤ (Real.pi ^ 2 / 8) * ‖covarianceOperator μ‖ :=
        mul_nonneg hpi (norm_nonneg (covarianceOperator μ))
      exact mul_nonneg hpiSigma (sq_nonneg K)
    simpa [hVar0] using hRHS

end PoincareBound

/-!
### The concrete replicated full-GUE product law
-/

/-!
The raw coordinate space is deliberately a finite function space with its
sup norm, rather than `EuclideanSpace`.  The concrete law is now proved
Gaussian and centered above.  Applying the Hilbert-space inequality requires
an explicit measurable linear transport to `EuclideanSpace` and a diagonal
covariance-operator computation; those are not hidden here as assumptions.
-/

end FiniteGaussianPoincare
end ERNative.BlockBand.External.CEH
