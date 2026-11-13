module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.Basic

/-!
# Zero sets of nonzero polynomials are null for products of atomless measures

The fixed-time step of the non-collision clause of `DysonBrownianMotion`: the non-simple
Hermitian matrices form the zero set of a polynomial in the real coordinates.

`pi_evalZero_eq_zero`: if `ν` is a σ-finite atomless measure on `ℝ`, `ι` is finite and
`p : MvPolynomial ι ℂ` is nonzero, then `{x : ι → ℝ | p(x) = 0}` is null for the product
measure `ν^ι`. Proof by induction on the number of variables (`finSuccEquiv`), Fubini
(`Measure.prod_apply_symm`) and finiteness of the roots of a nonzero one-variable polynomial.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory MvPolynomial

/-- Evaluation of a complex polynomial at a real point. -/
abbrev evalR {ι : Type*} (x : ι → ℝ) (p : MvPolynomial ι ℂ) : ℂ :=
  eval (fun i => (x i : ℂ)) p

theorem continuous_evalR {ι : Type*} (p : MvPolynomial ι ℂ) :
    Continuous fun x : ι → ℝ => evalR x p :=
  (MvPolynomial.continuous_eval p).comp (continuous_pi fun i =>
    Complex.continuous_ofReal.comp (continuous_apply i))

theorem measurableSet_evalR_eq_zero {ι : Type*} [Countable ι] (p : MvPolynomial ι ℂ) :
    MeasurableSet {x : ι → ℝ | evalR x p = 0} :=
  (isClosed_eq (continuous_evalR p) continuous_const).measurableSet

/-- One variable: a nonzero complex polynomial has finitely many real roots. -/
theorem measure_polyRoots_eq_zero {ν : Measure ℝ} [NullSingletonClass ν] {r : Polynomial ℂ} (hr : r ≠ 0) :
    ν {a : ℝ | Polynomial.eval (a : ℂ) r = 0} = 0 := by
  refine measure_mono_null (t := (fun a : ℝ => (a : ℂ)) ⁻¹' (r.roots.toFinset : Set ℂ))
    (fun a ha => ?_) ?_
  · simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_roots hr).2 ha
  · exact ((r.roots.toFinset.finite_toSet).preimage
      (Complex.ofReal_injective.injOn)).measure_zero ν

theorem pi_evalZero_fin (ν : Measure ℝ) [SigmaFinite ν] [NullSingletonClass ν] : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℂ), p ≠ 0 →
    Measure.pi (fun _ : Fin n => ν) {x | evalR x p = 0} = 0
  | 0, p, hp => by
    have : {x : Fin 0 → ℝ | evalR x p = 0} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      apply hp
      rw [MvPolynomial.eq_C_of_isEmpty p] at h ⊢
      simp only [eval_C] at h
      rw [h, map_zero]
    rw [this, measure_empty]
  | n + 1, p, hp => by
    set q := finSuccEquiv ℂ n p with hqdef
    have hq : q ≠ 0 := fun h => hp ((finSuccEquiv ℂ n).injective (h.trans (map_zero _).symm))
    set c := q.leadingCoeff
    have hc : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
    have hgood : ∀ᵐ t ∂(Measure.pi fun _ : Fin n => ν), evalR t c ≠ 0 := by
      rw [ae_iff]; simpa using pi_evalZero_fin ν n c hc
    have hslice : ∀ t : Fin n → ℝ, evalR t c ≠ 0 →
        ν {a : ℝ | evalR (Fin.cons a t : Fin (n + 1) → ℝ) p = 0} = 0 := by
      intro t ht
      set r := Polynomial.map (eval fun i => (t i : ℂ)) q
      have hr : r ≠ 0 := by
        intro h0
        apply ht
        have := congrArg (fun r => r.coeff q.natDegree) h0
        simp only [r, Polynomial.coeff_map, Polynomial.coeff_zero] at this
        exact this
      refine (measure_mono_null (fun a ha => ?_) (measure_polyRoots_eq_zero (ν := ν) hr) :)
      simp only [Set.mem_ofPred_eq] at ha ⊢
      have e : (fun i => ((Fin.cons a t : Fin (n + 1) → ℝ) i : ℂ)) =
          Fin.cons (a : ℂ) (fun i => (t i : ℂ)) := by
        ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      rw [evalR, e, eval_eq_eval_mv_eval'] at ha
      exact ha
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    set S := {x : Fin (n + 1) → ℝ | evalR x p = 0}
    have hS : MeasurableSet S := measurableSet_evalR_eq_zero p
    have hSe : S = e ⁻¹' (e.symm ⁻¹' S) := by
      ext x; simp
    rw [hSe, hmp.measure_preimage_equiv, Measure.prod_apply_symm (e.symm.measurable hS)]
    refine (lintegral_congr_ae ?_).trans (lintegral_zero)
    filter_upwards [hgood] with t ht
    refine (le_antisymm (le_of_eq_of_le ?_ (hslice t ht).le) zero_le).trans rfl
    congr 1
    ext a
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, S, Set.mem_preimage,
      Set.mem_ofPred_eq]
    show evalR (Fin.insertNth 0 a t) p = 0 ↔ _
    rw [Fin.insertNth_zero']

/-- **Zero sets of nonzero polynomials are `ν^ι`-null.** -/
theorem pi_evalZero_eq_zero {ν : Measure ℝ} [SigmaFinite ν] [NullSingletonClass ν] {ι : Type*} [Fintype ι] {p : MvPolynomial ι ℂ} (hp : p ≠ 0) :
    Measure.pi (fun _ : ι => ν) {x | evalR x p = 0} = 0 := by
  set eι := Fintype.equivFin ι
  have hmp := measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card ι) => ν) eι
  set e := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => ℝ) eι
  have hp' : rename eι p ≠ 0 := fun h =>
    hp (rename_injective _ eι.injective (h.trans (map_zero _).symm))
  have hS : {x : ι → ℝ | evalR x p = 0} = e ⁻¹' {y | evalR y (rename eι p) = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, evalR, eval_rename]
    have hfx : ((fun i => ((e x) i : ℂ)) ∘ eι) = fun i => (x i : ℂ) := by
      ext i; simp [e, MeasurableEquiv.coe_piCongrLeft]
    rw [hfx]
  rw [hS, hmp.measure_preimage_equiv]
  exact pi_evalZero_fin ν _ _ hp'

end BlockBand.SourceProcess.Stochastic.Dyson
