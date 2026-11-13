module

public import BlockBand.Native.PSSS.BlockBand.Coarea.PhysicalHermitianGaussianSplit
public import BlockBand.Native.PSSS.BlockBand.LinearAlgebra.Schur
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Analysis.Calculus.DerivativeTest
public import BlockBand.Native.PSSS.BlockBand.Spectral.Measurable.OrderedSpectrum
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.InnerProductSpace.Positive
public import BlockBand.Native.PSSS.BlockBand.Probability.GaussianNormalization
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import BlockBand.Native.PSSS.BlockBand.Coarea.GaussianRegression
public import BlockBand.Native.PSSS.BlockBand.Coarea.LagrangeProjectorCorrectness
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Finset.Max
public import BlockBand.Native.PSSS.BlockBand.Coarea.SelectedCoordinateEigenpairChart
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Affine
public import BlockBand.Native.PSSS.BlockBand.Coarea.NonlinearEigenpairSmoothDerivative
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.MeasureTheory.Function.Jacobian
public import BlockBand.Native.PSSS.BlockBand.Coarea.CoareaGoodSet
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import BlockBand.Native.PSSS.BlockBand.Counting.PhysicalMultiBlockCountConstruction
public import Mathlib.Probability.IdentDistribIndep
public import BlockBand.Native.PSSS.BlockBand.Analysis.ProjectedWegnerSchur
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Probability.IdentDistrib
public import BlockBand.Native.PSSS.BlockBand.Basic.Indices
public import BlockBand.Native.PSSS.BlockBand.Spectral.Ordered
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw
public import BlockBand.Native.PSSS.BlockBand.LinearAlgebra.RegulatedSchurMeasurability
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Interface
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Topology.Instances.Rat
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import BlockBand.Native.PSSS.BlockBand.Counting.PhysicalSchurMatrixConstruction
public import Mathlib.Data.Matrix.Composition
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import BlockBand.Native.PSSS.BlockBand.Analysis.HermitianPoissonTrace
public import BlockBand.Native.PSSS.BlockBand.Spectral.Measurable.Counts
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Lebesgue density of the fresh finite-product GUE block

The fresh GUE block of `PhysicalHermitianGaussianSplit` is the product of
diagonal `N(0,t)` and strict-upper real/imaginary `N(0,t/2)` coordinate laws.
For positive `t` this module identifies that product measure with Lebesgue
measure on the real coordinate space weighted by the GUE matrix density
`Z_d(t)⁻¹ exp (-Tr(G²)/(2t))`, `Z_d(t) = gueNormalizer d t`.

The proof is the coordinatewise Gaussian density, the product of densities on a
finite product (proved here by induction on the number of coordinates), the
exact Hilbert–Schmidt coordinate identity
`Tr(G²) = ∑ᵢ xᵢᵢ² + 2 ∑_{i<j} (Re² + Im²)`, and the factorization of
`gueNormalizer`.  This proves `FreshGUECoordinateDensityIdentification` of
`PhysicalConditionalCoareaManuscript` for `0 < t` (it is false at `t = 0` for
`d > 0`), and rewrites the fresh-GUE side of that module's bridge, after
residual translation, as an explicit Lebesgue integral over the coordinates of
the total exposed block.

It then computes the coarea chart weight exactly
(`physicalSchurOuterWeight_eq_matrixForm`): it is
`c_{d,t} exp(-‖M - F(E)‖²/(2t)) ⟨v, 𝒟(E) v⟩`, centred at the energy-dependent
Schur compression `F(E)`.  For the uncoupled readback (`C = 0`, `V` the
residual) it equals `κ_d(t) = c_{d,t} Z_d(t)` times the fresh GUE density, and
`κ_2(1) ≠ 1`, so the identification `weight = density` is false.  The
joined equality "fresh GUE side = chart sum" is proved with the
factor `κ_d(t)` on the decoded union, and on the whole space conditionally on a
named a.e.-cover hypothesis.  All statements are at fixed finite `d`; no limit
or uniformity is asserted.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section
namespace PSSSNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal MatrixOrder

/-!
### Products of densities on finite products
-/

/-- Tonelli for a finite product of one-variable functions over a finite
product of σ-finite measures on `ℝ`. -/
theorem lintegral_pi_fin_prod_eq_prod :
    ∀ (n : ℕ) (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
      (f : Fin n → ℝ → ℝ≥0∞), (∀ i, Measurable (f i)) →
      ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i
  | 0, μ, _, f, _ => by
      simp
  | n + 1, μ, _, f, hf => by
      have hmp := (measurePreserving_piFinSuccAbove μ 0).symm
      rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
      simp_rw [Fin.prod_univ_succ]
      have hcomp : ∀ p : ℝ × (Fin n → ℝ),
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p 0 = p.1 ∧
          ∀ j : Fin n,
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p j.succ =
              p.2 j := by
        intro p
        simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.cons_succ]
      simp_rw [fun p => (hcomp p).1, fun p j => (hcomp p).2 j]
      simp only [Fin.succAbove_zero]
      have hg : Measurable (fun y : Fin n → ℝ => ∏ j, f j.succ (y j)) :=
        Finset.measurable_prod _ fun j _ => (hf j.succ).comp (measurable_pi_apply j)
      rw [lintegral_prod_mul (f := f 0) (g := fun y : Fin n → ℝ => ∏ j, f j.succ (y j))
          (hf 0).aemeasurable hg.aemeasurable,
        lintegral_pi_fin_prod_eq_prod n (fun j => μ j.succ) (fun j => f j.succ)
          (fun j => hf j.succ)]

/-- A finite product of densities against σ-finite measures on `ℝ` is the
product measure with the product density. -/
theorem pi_fin_withDensity_eq {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    lintegral_pi_fin_prod_eq_prod n _ f hf]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i)]

/-!
### The Hilbert–Schmidt coordinate identity
-/

/-- A double sum over `Fin d × Fin d` splits into the diagonal, the strict
upper triangle and the strict lower triangle (indexed by its transpose). -/
theorem sum_fin_pairs_eq_diag_add_upper_add_lower {d : ℕ}
    (g : Fin d → Fin d → ℝ) :
    ∑ i, ∑ j, g i j =
      ∑ i, g i i + ∑ ij : StrictUpperIndex d, g ij.1.1 ij.1.2 +
        ∑ ij : StrictUpperIndex d, g ij.1.2 ij.1.1 := by
  rw [← Fintype.sum_prod_type' (f := g)]
  have hsplit : ∀ p : Fin d × Fin d, g p.1 p.2 =
      ((if p.1 = p.2 then g p.1 p.2 else 0) +
        (if p.1 < p.2 then g p.1 p.2 else 0)) +
        (if p.2 < p.1 then g p.1 p.2 else 0) := by
    intro p
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [h, h.ne, not_lt_of_gt h]
    · simp [h]
    · simp [h, h.ne', not_lt_of_gt h]
  rw [Finset.sum_congr rfl fun p _ => hsplit p, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hupper : ∀ h : Fin d × Fin d → ℝ,
      (∑ p : Fin d × Fin d, if p.1 < p.2 then h p else 0) =
        ∑ ij : StrictUpperIndex d, h ij.1 := by
    intro h
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun p => by simp) h
  congr 1
  · congr 1
    · rw [Fintype.sum_prod_type' (f := fun i j => if i = j then g i j else 0)]
      simp
    · exact hupper fun p => g p.1 p.2
  · rw [← (Equiv.prodComm (Fin d) (Fin d)).sum_comp]
    exact hupper fun p => g p.2 p.1

/-- The number of strict-upper positions satisfies `2 · #{i<j} = d (d - 1)`. -/
theorem two_mul_card_strictUpperIndex (d : ℕ) :
    2 * (Fintype.card (StrictUpperIndex d) : ℝ) = (d : ℝ) * ((d : ℝ) - 1) := by
  have h := sum_fin_pairs_eq_diag_add_upper_add_lower (d := d) (fun _ _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at h
  linarith

/-- Exact Hilbert–Schmidt identity in Hermitian coordinates:
`Tr(G²) = ∑ᵢ xᵢᵢ² + 2 ∑_{i<j} ((Re Gᵢⱼ)² + (Im Gᵢⱼ)²)`. -/
theorem hilbertSchmidtNormSq_hermitianMatrixOfCoordinates {d : ℕ}
    (y : HermitianCoordinate d → ℝ) :
    hilbertSchmidtNormSq (hermitianMatrixOfCoordinates y) =
      ∑ i, y (.inl i) ^ 2 +
        2 * ∑ ij : StrictUpperIndex d,
          (y (.inr (.inl ij)) ^ 2 + y (.inr (.inr ij)) ^ 2) := by
  unfold hilbertSchmidtNormSq
  rw [sum_fin_pairs_eq_diag_add_upper_add_lower]
  have hdiag : ∀ i, Complex.normSq (hermitianMatrixOfCoordinates y i i) =
      y (.inl i) ^ 2 := by
    intro i
    simp [hermitianMatrixOfCoordinates, Complex.normSq_ofReal, sq]
  have hup : ∀ ij : StrictUpperIndex d,
      Complex.normSq (hermitianMatrixOfCoordinates y ij.1.1 ij.1.2) =
        y (.inr (.inl ij)) ^ 2 + y (.inr (.inr ij)) ^ 2 := by
    intro ij
    simp [hermitianMatrixOfCoordinates, ij.2.ne, ij.2, hermitianUpperEntry,
      Complex.normSq_add_mul_I]
  have hlow : ∀ ij : StrictUpperIndex d,
      Complex.normSq (hermitianMatrixOfCoordinates y ij.1.2 ij.1.1) =
        y (.inr (.inl ij)) ^ 2 + y (.inr (.inr ij)) ^ 2 := by
    intro ij
    simp [hermitianMatrixOfCoordinates, ij.2.ne', not_lt_of_gt ij.2,
      hermitianUpperEntry, Complex.normSq_apply]
    ring
  simp only [hdiag, hup, hlow]
  ring

/-!
### Identification of the fresh GUE coordinate law
-/

/-- The real variance of a fresh coordinate after reindexing through the
canonical coordinate equivalence. -/
theorem hermitianGUEFinCoordinateVariance_equivFin_inl (d : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (i : Fin d) :
    ((hermitianGUEFinCoordinateVariance d t ht
      (hermitianCoordinateEquivFin d (.inl i)) : ℝ≥0) : ℝ) = t := by
  simp only [hermitianGUEFinCoordinateVariance, Equiv.symm_apply_apply]
  rfl

/-- Strict-upper real coordinates carry variance `t/2`. -/
theorem hermitianGUEFinCoordinateVariance_equivFin_inr (d : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (c : StrictUpperIndex d ⊕ StrictUpperIndex d) :
    ((hermitianGUEFinCoordinateVariance d t ht
      (hermitianCoordinateEquivFin d (.inr c)) : ℝ≥0) : ℝ) = t / 2 := by
  simp only [hermitianGUEFinCoordinateVariance, Equiv.symm_apply_apply]
  rfl

/-- Pointwise: the product of the coordinate Gaussian densities is the
GUE matrix density `Z_d(t)⁻¹ exp (-Tr(G²)/(2t))` of the
reconstructed block.  Positive variance `0 < t`; fixed finite `d`. -/
theorem prod_gaussianPDF_eq_hermitianGUEDensity (d : ℕ) {t : ℝ} (ht : 0 < t)
    (x : HermitianCoordinateSpace d) :
    ∏ k, gaussianPDF 0 (hermitianGUEFinCoordinateVariance d t ht.le k) (x k) =
      hermitianGUEDensity d t (hermitianGUEBlock d x) := by
  simp only [gaussianPDF]
  rw [← ENNReal.ofReal_prod_of_nonneg fun k _ => gaussianPDFReal_nonneg _ _ _]
  unfold hermitianGUEDensity
  congr 1
  rw [← (hermitianCoordinateEquivFin d).prod_comp, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [gaussianPDFReal_def, sub_zero,
    hermitianGUEFinCoordinateVariance_equivFin_inl,
    hermitianGUEFinCoordinateVariance_equivFin_inr]
  change _ = Real.exp (-hilbertSchmidtNormSq
      (hermitianMatrixOfCoordinates (x ∘ hermitianCoordinateEquivFin d)) / (2 * t)) /
        gueNormalizer d t
  rw [hilbertSchmidtNormSq_hermitianMatrixOfCoordinates]
  simp only [Function.comp_apply, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]
  have hS := two_mul_card_strictUpperIndex d
  set S := Fintype.card (StrictUpperIndex d)
  have hb : Real.sqrt (2 * Real.pi * (t / 2)) ^ 2 = Real.pi * t := by
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hZ : gueNormalizer d t =
      Real.sqrt (2 * Real.pi * t) ^ d * Real.sqrt (2 * Real.pi * (t / 2)) ^ (2 * S) := by
    unfold gueNormalizer
    rw [pow_mul, hb, ← Real.rpow_natCast (Real.pi * t), ← hS,
      Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 2
    · ring
    · ring
  rw [hZ]
  have ha : 0 < Real.sqrt (2 * Real.pi * t) := by positivity
  have hb0 : 0 < Real.sqrt (2 * Real.pi * (t / 2)) := by positivity
  have hexp : ∀ (A B C : ℝ), Real.exp (-A / (2 * t)) * Real.exp (-B / (2 * (t / 2))) *
      Real.exp (-C / (2 * (t / 2))) = Real.exp (-(A + 2 * (B + C)) / (2 * t)) := by
    intro A B C
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  simp only [← Finset.sum_div, Finset.sum_neg_distrib, Finset.sum_add_distrib]
  rw [← hexp]
  ring

/-- Every fresh coordinate variance is nonzero for positive `t`. -/
theorem hermitianGUEFinCoordinateVariance_ne_zero (d : ℕ) {t : ℝ} (ht : 0 < t)
    (k : Fin (Fintype.card (HermitianCoordinate d))) :
    hermitianGUEFinCoordinateVariance d t ht.le k ≠ 0 := by
  rw [ne_eq, ← NNReal.coe_eq_zero, ← Equiv.apply_symm_apply (hermitianCoordinateEquivFin d) k]
  rcases (hermitianCoordinateEquivFin d).symm k with i | c
  · rw [hermitianGUEFinCoordinateVariance_equivFin_inl]
    exact ht.ne'
  · rw [hermitianGUEFinCoordinateVariance_equivFin_inr]
    positivity

/-- Measurability of the GUE matrix density in the fresh real coordinates. -/
theorem measurable_hermitianGUEDensity_comp_block (d : ℕ) (t : ℝ) :
    Measurable (fun x : HermitianCoordinateSpace d =>
      hermitianGUEDensity d t (hermitianGUEBlock d x)) := by
  have hG : Measurable fun x : HermitianCoordinateSpace d => (hermitianGUEBlock d x).1 :=
    measurable_subtype_coe.comp (measurable_hermitianGUEBlock d)
  have hHS : Measurable fun x : HermitianCoordinateSpace d =>
      hilbertSchmidtNormSq (hermitianGUEBlock d x).1 := by
    unfold hilbertSchmidtNormSq
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact Complex.continuous_normSq.measurable.comp hG.eval_matrix
  unfold hermitianGUEDensity
  exact ENNReal.measurable_ofReal.comp
    ((Real.measurable_exp.comp (hHS.neg.div_const _)).div_const _)

/-- **Fresh GUE coordinate density identification** (with the normalization
`gueNormalizer`).

For every finite `d` and every positive variance `t`, the product of the
diagonal `N(0,t)` and strict-upper real/imaginary `N(0,t/2)` coordinate laws
equals Lebesgue measure on `Fin (#coordinates) → ℝ` with density
`Z_d(t)⁻¹ exp (-Tr(G²)/(2t))` of the reconstructed block `G`,
`Z_d(t) = gueNormalizer d t`.  The hypothesis `0 < t` is necessary: see
`hermitianGUECoordinateMeasure_ne_withDensity_zero`. -/
theorem hermitianGUECoordinateMeasure_eq_withDensity (d : ℕ) {t : ℝ} (ht : 0 < t) :
    hermitianGUECoordinateMeasure d t ht.le =
      volume.withDensity (fun x =>
        hermitianGUEDensity d t (hermitianGUEBlock d x)) := by
  have hv := hermitianGUEFinCoordinateVariance_ne_zero d ht
  have hfun : (fun k => gaussianReal 0 (hermitianGUEFinCoordinateVariance d t ht.le k)) =
      fun k => volume.withDensity
        (gaussianPDF 0 (hermitianGUEFinCoordinateVariance d t ht.le k)) :=
    funext fun k => gaussianReal_of_var_ne_zero 0 (hv k)
  have : ∀ k, SigmaFinite (volume.withDensity
      (gaussianPDF 0 (hermitianGUEFinCoordinateVariance d t ht.le k))) := fun k => by
    rw [← gaussianReal_of_var_ne_zero 0 (hv k)]
    infer_instance
  unfold hermitianGUECoordinateMeasure
  rw [hfun, pi_fin_withDensity_eq (fun _ => volume) _
    (fun k => measurable_gaussianPDF 0 _), ← volume_pi]
  congr 1
  funext x
  exact prod_gaussianPDF_eq_hermitianGUEDensity d ht x

/-- The identification fails at `t = 0` for every nonempty block: the product
of the degenerate laws `N(0,0)` is a probability measure, whereas Lean's
`gueNormalizer d 0 = 0` makes the displayed density identically `0`. -/
theorem hermitianGUECoordinateMeasure_ne_withDensity_zero {d : ℕ} (hd : 0 < d) :
    hermitianGUECoordinateMeasure d 0 le_rfl ≠
      volume.withDensity (fun x =>
        hermitianGUEDensity d 0 (hermitianGUEBlock d x)) := by
  intro h
  have hZ : gueNormalizer d 0 = 0 := by
    unfold gueNormalizer
    rw [mul_zero, Real.zero_rpow (by positivity), zero_mul]
  have hdens : (fun x : HermitianCoordinateSpace d =>
      hermitianGUEDensity d 0 (hermitianGUEBlock d x)) = 0 := by
    funext x
    simp [hermitianGUEDensity, hZ]
  have h1 := measure_univ (μ := hermitianGUECoordinateMeasure d 0 le_rfl)
  rw [h, hdens, withDensity_zero] at h1
  simp at h1

/-!
### The named representation gap of `PhysicalConditionalCoareaManuscript`
-/

/-!
### Exact form of the coarea chart weight
-/

/-- Hilbert–Schmidt norm as a trace. -/
theorem hilbertSchmidtNormSq_eq_re_trace {m : Type*} [Fintype m]
    (A : Matrix m m ℂ) :
    hilbertSchmidtNormSq A = ((Aᴴ * A).trace).re := by
  unfold hilbertSchmidtNormSq
  rw [Matrix.trace, Complex.re_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  ring

/-- Unitary conjugation preserves the Hilbert–Schmidt norm. -/
theorem hilbertSchmidtNormSq_unitary_conj {m : Type*} [Fintype m] [DecidableEq m]
    (U A : Matrix m m ℂ) (hU : Uᴴ * U = 1) :
    hilbertSchmidtNormSq (U * A * Uᴴ) = hilbertSchmidtNormSq A := by
  rw [hilbertSchmidtNormSq_eq_re_trace, hilbertSchmidtNormSq_eq_re_trace]
  congr 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  calc (U * (Aᴴ * Uᴴ) * (U * A * Uᴴ)).trace
      = (U * (Aᴴ * (Uᴴ * U) * A) * Uᴴ).trace := by simp only [Matrix.mul_assoc]
    _ = ((Aᴴ * A) * (Uᴴ * U)).trace := by
        rw [hU, Matrix.mul_one, Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hU,
          Matrix.one_mul, Matrix.mul_one]
    _ = (Aᴴ * A).trace := by rw [hU, Matrix.mul_one]

/-!
### The joined lintegral equality
-/

end PSSSNative.BlockBand
