module

public import BlockBand.SourceProcess.ModelExist.Select

/-!
# Measurability of the perpendicular selection

The candidate vectors of the perpendicular selection depend continuously or measurably on the Gram
pair and the earlier vectors, so the selection `perpSel` is measurable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open Matrix Finset MeasureTheory
open scoped ComplexOrder

variable {c' : Type*} [Fintype c'] [DecidableEq c'] {n : ℕ} (cur : c' → Prop) [DecidablePred cur]

omit [DecidableEq c'] in
theorem secMat : SecondCountableTopology (Matrix c' c' ℂ) :=
  inferInstanceAs (SecondCountableTopology (c' → c' → ℂ))

attribute [local instance] secMat

omit [DecidableEq c'] [DecidablePred cur] in
theorem continuous_selG :
    Continuous fun z : (Matrix c' c' ℂ × Matrix c' c' ℂ) × (Fin n → c' → ℂ) =>
      selG cur z.1 z.2 := by
  refine continuous_pi fun r => ?_
  rcases r with x | k | l
  · exact (continuous_apply x).comp ((continuous_fst.comp continuous_fst).sub
      (continuous_snd.comp continuous_fst))
  · exact (continuous_apply k.1).comp (continuous_fst.comp continuous_fst)
  · simp only [selG]
    exact Continuous.matrix_vecMul ((continuous_apply l).comp continuous_snd).star
      (continuous_fst.comp continuous_fst)

theorem measurable_candQ (k : c') :
    Measurable fun z : (Matrix c' c' ℂ × Matrix c' c' ℂ) × (Fin n → c' → ℂ) =>
      candQ cur z.1 z.2 k := by
  have h1 : Measurable fun z : (Matrix c' c' ℂ × Matrix c' c' ℂ) × (Fin n → c' → ℂ) =>
      specProj (selG cur z.1 z.2) :=
    measurable_specProj.comp (continuous_selG cur).measurable
  exact (continuous_id.matrix_mulVec continuous_const).measurable.comp h1

theorem measurable_candR (k : c') :
    Measurable fun z : (Matrix c' c' ℂ × Matrix c' c' ℂ) × (Fin n → c' → ℂ) =>
      candR cur z.1 z.2 k := by
  have hq := measurable_candQ cur k (n := n)
  have hM : Measurable fun z : (Matrix c' c' ℂ × Matrix c' c' ℂ) × (Fin n → c' → ℂ) => z.1.1 :=
    measurable_fst.comp measurable_fst
  have h : Measurable fun z : (Matrix c' c' ℂ × Matrix c' c' ℂ) × (Fin n → c' → ℂ) =>
      star (candQ cur z.1 z.2 k) ⬝ᵥ (z.1.1 *ᵥ candQ cur z.1 z.2 k) := by
    have hc : Continuous fun p : (c' → ℂ) × Matrix c' c' ℂ => star p.1 ⬝ᵥ (p.2 *ᵥ p.1) :=
      Continuous.dotProduct continuous_fst.star (continuous_snd.matrix_mulVec continuous_fst)
    exact hc.measurable.comp (hq.prodMk hM)
  exact Complex.measurable_re.comp h

theorem measurableSet_isFirst (j : Fin (Fintype.card c')) :
    MeasurableSet {z : (Matrix c' c' ℂ × Matrix c' c' ℂ) × (Fin n → c' → ℂ) |
      IsFirst cur z.1 z.2 j} := by
  simp only [IsFirst, Set.ofPred_and]
  refine (measurableSet_lt measurable_const (measurable_candR cur _)).inter ?_
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun j' => MeasurableSet.iInter fun _ => ?_
  exact (measurableSet_lt measurable_const (measurable_candR cur _)).compl

/-- **The selection is measurable.** -/
theorem measurable_perpSel : Measurable (perpSel cur (n := n)) := by
  have hz : Measurable fun z : (Matrix c' c' ℂ × Matrix c' c' ℂ) × (Fin n → c' → ℂ) × ℝ =>
      (z.1, z.2.1) := measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hv : Measurable fun z : (Matrix c' c' ℂ × Matrix c' c' ℂ) × (Fin n → c' → ℂ) × ℝ =>
      z.2.2 := measurable_snd.comp measurable_snd
  refine measurable_pi_iff.2 fun x => ?_
  simp only [perpSel, Finset.sum_apply]
  refine Finset.measurable_fun_sum _ fun j _ => ?_
  have hset := (measurableSet_isFirst cur (n := n) j).preimage hz
  have hr := (measurable_candR cur ((Fintype.equivFin c').symm j)).comp hz
  have hq := (measurable_pi_apply x).comp
    ((measurable_candQ cur ((Fintype.equivFin c').symm j)).comp hz)
  have hf : Measurable fun z : (Matrix c' c' ℂ × Matrix c' c' ℂ) × (Fin n → c' → ℂ) × ℝ =>
      ((Real.sqrt (z.2.2 / candR cur z.1 z.2.1 ((Fintype.equivFin c').symm j)) : ℝ) : ℂ) *
        candQ cur z.1 z.2.1 ((Fintype.equivFin c').symm j) x :=
    (Complex.measurable_ofReal.comp (hv.div hr).sqrt).mul hq
  classical
  have hite := @Measurable.piecewise _ _ _ _ _ _ _ (fun _ => Classical.propDecidable _) hset hf
    (measurable_const (a := (0 : ℂ)))
  convert hite using 1
  funext z
  simp only [Set.piecewise, Set.mem_preimage, Set.mem_ofPred_eq]
  split_ifs <;> simp

end BlockBand.SourceProcess.ModelExist
