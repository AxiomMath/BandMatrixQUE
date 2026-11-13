module

public import BlockBand.Model.Construction.GaussianCompatibility

/-!
# Null zero sets of polynomials

The zero set of a nonzero real polynomial in finitely many real variables is Lebesgue-null, with
the real- and imaginary-part polynomials of a complex polynomial and absolute continuity of
finite products; these are used for almost-sure simplicity of the sparse Gaussian spectrum.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Parameters
open MeasureTheory MvPolynomial Set
open scoped NNReal

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

/-- Take the real part of every coefficient of a complex multivariate
polynomial, without changing its monomials. -/
def mvPolynomialRealPart {σ : Type*} (p : MvPolynomial σ ℂ) :
    MvPolynomial σ ℝ :=
  p.coeff.sum fun m z => MvPolynomial.monomial m z.re

/-- Take the imaginary part of every coefficient of a complex multivariate
polynomial, without changing its monomials. -/
def mvPolynomialImagPart {σ : Type*} (p : MvPolynomial σ ℂ) :
    MvPolynomial σ ℝ :=
  p.coeff.sum fun m z => MvPolynomial.monomial m z.im

/-- Coefficientwise real-part extraction commutes with evaluation at real
variable values. -/
theorem eval_mvPolynomialRealPart {σ : Type*} (p : MvPolynomial σ ℂ)
    (x : σ → ℝ) :
    MvPolynomial.eval x (mvPolynomialRealPart p) =
      (MvPolynomial.eval (fun i => (x i : ℂ)) p).re := by
  classical
  have hprod (m : σ →₀ ℕ) :
      (∏ i ∈ m.support, (x i : ℂ) ^ m i) =
        ((∏ i ∈ m.support, x i ^ m i : ℝ) : ℂ) := by
    norm_cast
  rw [mvPolynomialRealPart, MvPolynomial.sum_def,
    MvPolynomial.eval_sum, MvPolynomial.eval_eq]
  rw [← Complex.reCLM_apply, map_sum]
  simp only [Complex.reCLM_apply]
  apply Finset.sum_congr rfl
  intro m hm
  have hre : (∏ i ∈ m.support, (x i : ℂ) ^ m i).re =
      ∏ i ∈ m.support, x i ^ m i := by
    calc
      _ = (((∏ i ∈ m.support, x i ^ m i : ℝ) : ℂ)).re :=
        congrArg Complex.re (hprod m)
      _ = _ := rfl
  have him : (∏ i ∈ m.support, (x i : ℂ) ^ m i).im = 0 := by
    calc
      _ = (((∏ i ∈ m.support, x i ^ m i : ℝ) : ℂ)).im :=
        congrArg Complex.im (hprod m)
      _ = _ := rfl
  by_cases hz : (p.coeff m).re = 0 <;>
    simp [MvPolynomial.eval_monomial, Finsupp.prod, hz, hre, him]

/-- Coefficientwise imaginary-part extraction commutes with evaluation at real
variable values. -/
theorem eval_mvPolynomialImagPart {σ : Type*} (p : MvPolynomial σ ℂ)
    (x : σ → ℝ) :
    MvPolynomial.eval x (mvPolynomialImagPart p) =
      (MvPolynomial.eval (fun i => (x i : ℂ)) p).im := by
  classical
  have hprod (m : σ →₀ ℕ) :
      (∏ i ∈ m.support, (x i : ℂ) ^ m i) =
        ((∏ i ∈ m.support, x i ^ m i : ℝ) : ℂ) := by
    norm_cast
  rw [mvPolynomialImagPart, MvPolynomial.sum_def,
    MvPolynomial.eval_sum, MvPolynomial.eval_eq]
  rw [← Complex.imCLM_apply, map_sum]
  simp only [Complex.imCLM_apply]
  apply Finset.sum_congr rfl
  intro m hm
  have hre : (∏ i ∈ m.support, (x i : ℂ) ^ m i).re =
      ∏ i ∈ m.support, x i ^ m i := by
    calc
      _ = (((∏ i ∈ m.support, x i ^ m i : ℝ) : ℂ)).re :=
        congrArg Complex.re (hprod m)
      _ = _ := rfl
  have him : (∏ i ∈ m.support, (x i : ℂ) ^ m i).im = 0 := by
    calc
      _ = (((∏ i ∈ m.support, x i ^ m i : ℝ) : ℂ)).im :=
        congrArg Complex.im (hprod m)
      _ = _ := rfl
  by_cases hz : (p.coeff m).im = 0 <;>
    simp [MvPolynomial.eval_monomial, Finsupp.prod, hz, hre, him]

/-- Finite products of absolutely continuous factors are absolutely continuous
w.r.t. Lebesgue measure on `σ → ℝ`. -/
theorem pi_absolutelyContinuous_volume {σ : Type*} [Fintype σ]
    (μ : σ → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (h : ∀ i, μ i ≪ (volume : Measure ℝ)) :
    Measure.pi μ ≪ (volume : Measure (σ → ℝ)) := by
  let P : ∀ (α : Type _) [Fintype α], Prop := fun α _ =>
    ∀ (μ ν : α → Measure ℝ) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)],
      (∀ i, μ i ≪ ν i) → Measure.pi μ ≪ Measure.pi ν
  have key : P σ := by
    refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ σ
    · intro α β _ e hα μ ν _ _ hμν
      let _ : Fintype α := Fintype.ofEquiv β e.symm
      have hm := (measurePreserving_piCongrLeft μ e).map_eq
      have hn := (measurePreserving_piCongrLeft ν e).map_eq
      rw [← hm, ← hn]
      exact (hα (fun a => μ (e a)) (fun a => ν (e a)) (fun a => hμν (e a))).map
        (MeasurableEquiv.piCongrLeft (fun _ => ℝ) e).measurable
    · intro μ ν _ _ _
      rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
    · intro α _ hα μ ν _ _ hμν
      rw [← Measure.pi_map_piOptionEquivProd μ, ← Measure.pi_map_piOptionEquivProd ν]
      exact ((hα (fun i => μ (some i)) (fun i => ν (some i)) (fun i => hμν (some i))).prod
        (hμν none)).map (MeasurableEquiv.piOptionEquivProd (fun _ => ℝ)).symm.measurable
  rw [volume_pi]
  exact key μ (fun _ => volume) h

/-- The zero set of a nonzero real polynomial in finitely many variables indexed by any
fintype is Lebesgue-null. -/
theorem volume_mvPolynomial_zeroSet_fintype {σ : Type*} [Fintype σ]
    (Q : MvPolynomial σ ℝ) (hQ : Q ≠ 0) :
    volume {x : σ → ℝ | MvPolynomial.eval x Q = 0} = 0 := by
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let Q' : MvPolynomial (Fin (Fintype.card σ)) ℝ := MvPolynomial.rename e Q
  have hQ' : Q' ≠ 0 := by
    intro h0
    apply hQ
    apply MvPolynomial.rename_injective e e.injective
    simpa [Q'] using h0
  have hnull := volume_mvPolynomial_zeroSet _ Q' hQ'
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card σ) => ℝ) e
  have hpre : {x : σ → ℝ | MvPolynomial.eval x Q = 0} =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card σ) => ℝ) e) ⁻¹'
        {y | MvPolynomial.eval y Q' = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Q', MvPolynomial.eval_rename]
    have : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card σ) => ℝ) e) x) ∘ e = x := by
      funext a
      exact Equiv.piCongrLeft_apply_apply (fun _ : Fin (Fintype.card σ) => ℝ) e x a
    rw [this]
  rw [hpre]
  exact hmp.quasiMeasurePreserving.preimage_null hnull

/-- The real norm-square polynomial of a complex polynomial in real variables. -/
def mvPolynomialNormSq {σ : Type*} (F : MvPolynomial σ ℂ) : MvPolynomial σ ℝ :=
  mvPolynomialRealPart F ^ 2 + mvPolynomialImagPart F ^ 2

theorem eval_mvPolynomialNormSq {σ : Type*} (F : MvPolynomial σ ℂ) (x : σ → ℝ) :
    MvPolynomial.eval x (mvPolynomialNormSq F) =
      Complex.normSq (MvPolynomial.eval (fun i => (x i : ℂ)) F) := by
  rw [mvPolynomialNormSq, map_add, map_pow, map_pow,
    eval_mvPolynomialRealPart, eval_mvPolynomialImagPart]
  simp [Complex.normSq, pow_two]

end BlockBand.Parameters
