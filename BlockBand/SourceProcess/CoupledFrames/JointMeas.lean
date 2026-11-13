module

public import BlockBand.SourceProcess.CoupledFrames.JointExist
public import BlockBand.SourceProcess.ModelExist.SelectMeas

/-!
# The two-frame selection is measurable

The auxiliary maps `jointG` and `jointQ` are continuous, so the two-frame
selection `jointSel` is measurable (`measurable_jointSel`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open Matrix Finset MeasureTheory
open scoped ComplexOrder

variable {c' : Type*} [Fintype c'] [DecidableEq c'] {n : ℕ} (cur : c' → Prop) [DecidablePred cur]

theorem continuous_jointG :
    Continuous fun z : (Matrix (c' ⊕ c') (c' ⊕ c') ℂ × Matrix (c' ⊕ c') (c' ⊕ c') ℂ) ×
      (Fin n → c' ⊕ c' → ℂ) => jointG cur z.1 z.2 := by
  have hM : Continuous fun z : (Matrix (c' ⊕ c') (c' ⊕ c') ℂ × Matrix (c' ⊕ c') (c' ⊕ c') ℂ) ×
      (Fin n → c' ⊕ c' → ℂ) => z.1.1 := continuous_fst.comp continuous_fst
  have hB : Continuous fun z : (Matrix (c' ⊕ c') (c' ⊕ c') ℂ × Matrix (c' ⊕ c') (c' ⊕ c') ℂ) ×
      (Fin n → c' ⊕ c' → ℂ) => z.1.2 := continuous_snd.comp continuous_fst
  refine continuous_pi fun r => ?_
  rcases r with z | z | z | ⟨l, j⟩
  · exact (continuous_apply z).comp (hM.matrix_mul continuous_const)
  · exact (continuous_apply z).comp ((hM.sub hB).matrix_mul continuous_const)
  · exact (continuous_apply z).comp ((continuous_const.matrix_mul hM).matrix_mul continuous_const)
  · simp only [jointG]
    exact Continuous.matrix_vecMul
      (continuous_const.matrix_mulVec ((continuous_apply l).comp continuous_snd)).star
      (hM.matrix_mul continuous_const)

theorem continuous_jointQ :
    Continuous fun H : Matrix (c' ⊕ c') (c' ⊕ c') ℂ × Matrix (c' ⊕ c') (c' ⊕ c') ℂ => jointQ H :=
  (continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const

/-- **The two-frame selection is measurable.** -/
theorem measurable_jointSel : Measurable (jointSel n cur) := by
  have : SecondCountableTopology (Matrix (c' ⊕ c') (c' ⊕ c') ℂ) := ModelExist.secMat
  refine measurable_genSel _ _ _ ((continuous_jointG cur).measurable.comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
    ((continuous_jointQ).measurable.comp measurable_fst) (measurable_snd.comp measurable_snd)

end BlockBand.SourceProcess.CoupledFrames
