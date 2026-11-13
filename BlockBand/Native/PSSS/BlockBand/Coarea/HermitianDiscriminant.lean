module

public import BlockBand.Native.PSSS.BlockBand.LinearAlgebra.Schur
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import BlockBand.Native.PSSS.BlockBand.Spectral.Measurable.OrderedSpectrum
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Nullity of polynomial discriminant loci

The repeated-spectrum locus is algebraic: it is cut out by the discriminant of
the characteristic polynomial.  The measure-theoretic input missing from the
global eigenpair-coarea assembly is therefore that a nonzero multivariate
polynomial has a Lebesgue-null zero locus.  This module proves that statement
unconditionally over real coordinate space, by induction and Fubini.

The result is stated for real multivariate polynomials.  This is the
measure-theoretic theorem needed after the real diagonal and real/imaginary
upper-triangular coordinates of a complex Hermitian matrix have been expanded.
No probabilistic or absolute-continuity assumption is used.

Mathlib defines `Matrix.discr`, but currently has no naturality theorem showing
that it is the evaluation of the generic-entry `MvPolynomial`, and it has no
linear coordinate equivalence for the real space of complex Hermitian matrices.
Those two algebraic coordinate constructions remain before the result below can
be specialized to the `HermitianMatrix` subtype itself.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PSSSNative.BlockBand

open MeasureTheory MvPolynomial Set

/-- The zero locus of a nonzero real polynomial in `n` real variables
has Lebesgue measure zero.

The proof slices in the first coordinate.  Away from the null zero set of the
leading coefficient, each one-dimensional slice is the finite root set of a
nonzero univariate polynomial; Fubini then gives the result. -/
theorem volume_mvPolynomial_zeroSet (n : ℕ) :
    ∀ (p : MvPolynomial (Fin n) ℝ), p ≠ 0 →
      volume {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0 := by
  induction n with
  | zero =>
      intro p hp
      have hc : p.coeff 0 ≠ 0 := by
        intro h
        apply hp
        rw [eq_C_of_isEmpty p, h, map_zero]
      have hempty : {x : Fin 0 → ℝ | MvPolynomial.eval x p = 0} = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro x hx
        apply hc
        change MvPolynomial.eval x p = 0 at hx
        rw [eq_C_of_isEmpty p, eval_C] at hx
        exact hx
      rw [hempty, measure_empty]
  | succ n ih =>
      intro p hp
      let q : Polynomial (MvPolynomial (Fin n) ℝ) := finSuccEquiv ℝ n p
      have hq : q ≠ 0 := by
        dsimp [q]
        exact (finSuccEquiv ℝ n).injective.ne hp
      let c : MvPolynomial (Fin n) ℝ := q.leadingCoeff
      have hc : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
      have hcnull : volume {s : Fin n → ℝ | MvPolynomial.eval s c = 0} = 0 := ih c hc
      let swapCoords : (Fin (n + 1) → ℝ) → (Fin n → ℝ) × ℝ :=
        fun x => (Fin.tail x, x 0)
      have hswap : MeasurePreserving swapCoords volume (volume.prod volume) := by
        let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
        have he : MeasurePreserving e volume (volume.prod volume) :=
          volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
        have hprod : MeasurePreserving
            (Prod.swap : ℝ × (Fin n → ℝ) → (Fin n → ℝ) × ℝ)
            (volume.prod volume) (volume.prod volume) :=
          Measure.measurePreserving_swap
        have hfun : swapCoords = Prod.swap ∘ e := by
          funext x
          have hex : e x = (x 0, Fin.tail x) := by
            simp only [e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_zero]
            rfl
          simp [swapCoords, Function.comp_apply, hex]
        rw [hfun]
        exact hprod.comp he
      let zeroSet : Set ((Fin n → ℝ) × ℝ) :=
        {z | MvPolynomial.eval (Fin.cons z.2 z.1) p = 0}
      have hcons : Measurable
          (fun z : (Fin n → ℝ) × ℝ => (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ)) := by
        rw [measurable_pi_iff]
        intro i
        refine Fin.cases ?_ ?_ i
        · simpa using measurable_snd
        · intro j
          change Measurable (fun x : (Fin n → ℝ) × ℝ => x.1 j)
          fun_prop
      have hzeroSet : MeasurableSet zeroSet := by
        have hmeas : Measurable (fun z : (Fin n → ℝ) × ℝ =>
            MvPolynomial.eval (Fin.cons z.2 z.1) p) :=
          (MvPolynomial.continuous_eval p).measurable.comp hcons
        exact hmeas (measurableSet_singleton 0)
      have hpreimage :
          {x : Fin (n + 1) → ℝ | MvPolynomial.eval x p = 0} =
            swapCoords ⁻¹' zeroSet := by
        ext x
        simp only [swapCoords, zeroSet, mem_ofPred_eq, mem_preimage]
        rw [Fin.cons_self_tail]
      rw [hpreimage, hswap.measure_preimage hzeroSet.nullMeasurableSet,
        Measure.measure_prod_null hzeroSet]
      have hslices :
          {s : Fin n → ℝ | volume (Prod.mk s ⁻¹' zeroSet) ≠ 0} ⊆
            {s : Fin n → ℝ | MvPolynomial.eval s c = 0} := by
        intro s hs
        simp only [mem_ofPred_eq] at hs ⊢
        by_contra hcs
        apply hs
        have hmap : Polynomial.map (MvPolynomial.eval s) q ≠ 0 := by
          intro hz
          apply hcs
          have hcoeff :
              (Polynomial.map (MvPolynomial.eval s) q).coeff q.natDegree =
                MvPolynomial.eval s c := by
            rw [Polynomial.coeff_map]
            rfl
          rw [hz] at hcoeff
          simpa using hcoeff.symm
        have hslice : Prod.mk s ⁻¹' zeroSet =
            {y : ℝ | (Polynomial.map (MvPolynomial.eval s) q).IsRoot y} := by
          ext y
          simp only [zeroSet, mem_preimage, mem_ofPred_eq, Polynomial.IsRoot.def]
          rw [MvPolynomial.eval_eq_eval_mv_eval' s y p]
        rw [hslice]
        exact (Polynomial.finite_setOfPred_isRoot hmap).measure_zero _
      have hbad :
          volume {s : Fin n → ℝ | volume (Prod.mk s ⁻¹' zeroSet) ≠ 0} = 0 :=
        measure_mono_null hslices hcnull
      have hae : ∀ᵐ s ∂(volume : Measure (Fin n → ℝ)),
          volume (Prod.mk s ⁻¹' zeroSet) = 0 := by
        rw [ae_iff]
        simpa using hbad
      filter_upwards [hae] with s hs
      simpa using hs

/-- The simple locus cut out by a coordinate polynomial.  For a Hermitian
coordinate chart, the intended polynomial is the characteristic discriminant. -/
def polynomialSimpleLocus (n : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    Set (Fin n → ℝ) :=
  {x | MvPolynomial.eval x p ≠ 0}

/-- A nonzero discriminant polynomial gives exactly the full-measure hypothesis
`EigenpairCoareaAtlas.discriminant_null` when the ambient Hermitian space is
presented in real coordinates. -/
theorem volume_polynomialSimpleLocus_compl
    (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    volume (polynomialSimpleLocus n p)ᶜ = 0 := by
  rw [show (polynomialSimpleLocus n p)ᶜ =
      {x : Fin n → ℝ | MvPolynomial.eval x p = 0} by
    ext x
    simp [polynomialSimpleLocus]]
  exact volume_mvPolynomial_zeroSet n p hp

end PSSSNative.BlockBand
