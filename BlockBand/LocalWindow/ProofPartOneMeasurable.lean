module

public import BlockBand.LocalWindow.ProofTruncation
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Measurability of the truncated deformation

The truncated resolvent `g_ε(H - E)` and the truncated deformation `F̂(E)` are Borel measurable
functions of the matrix data, for `ε > 0`.

## Main results

* `continuous_truncInv`: for `ε > 0`, `g_ε(x) = x/ε²` (`|x| ≤ ε`), `x⁻¹` (`|x| > ε`) is
  continuous on `ℝ` (both pieces equal `±1/ε` at `|x| = ε`).
* `truncResolvent_eq_cfc'`: `truncResolvent ε H E = cfc (g_ε(· - E)) H` for every `H`.
* **`measurable_truncResolvent`**, **`measurable_truncF`**: for `ε > 0` and fixed `E`,
  `H ↦ g_ε(H - E)` (zero off the Hermitian set) and `(H_R, C, V) ↦ F̂(E)` are Borel measurable
  (continuity of the continuous functional calculus on the closed Hermitian set,
  `Continuous.cfc_of_mem_nhdsSet`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofCount

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- `g_ε` is continuous for `ε > 0`. -/
theorem continuous_truncInv {ε : ℝ} (hε : 0 < ε) : Continuous (truncInv ε) := by
  unfold truncInv
  refine continuous_if_le continuous_abs continuous_const (by fun_prop) ?_ ?_
  · exact continuousOn_inv₀.mono fun x hx => by
      have : ε ≤ |x| := hx
      exact abs_pos.mp (hε.trans_le this)
  · intro x hx
    rcases abs_eq hε.le |>.mp hx with h | h <;> subst h <;> field_simp

/-- On Hermitian `H`, `g_ε(H - E)` is the continuous functional calculus. -/
theorem truncResolvent_eq_cfc {H : Matrix α α ℂ} (hH : H.IsHermitian) (ε E : ℝ) :
    truncResolvent ε H E = cfc (fun x => truncInv ε (x - E)) H := by
  rw [hH.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, truncResolvent,
    dite_eq_left_of_eq_true (eq_true hH)]
  rfl

/-- `H ↦ g_ε(H - E)` is continuous on the Hermitian matrices (`ε > 0`). -/
theorem continuous_truncResolvent_herm {ε : ℝ} (hε : 0 < ε) (E : ℝ) :
    Continuous (fun H : {H : Matrix α α ℂ // H.IsHermitian} =>
      cfc (fun x => truncInv ε (x - E)) H.1) := by
  refine Continuous.cfc_of_mem_nhdsSet (s := Set.univ) _ (by simp) continuous_subtype_val
    (fun H => H.2.isSelfAdjoint) ?_
  exact ((continuous_truncInv hε).comp (continuous_id.sub continuous_const)).continuousOn

/-- `truncResolvent ε H E = cfc (g_ε(· - E)) H` for every `H` (both sides vanish off the
Hermitian set). -/
theorem truncResolvent_eq_cfc' (ε : ℝ) (H : Matrix α α ℂ) (E : ℝ) :
    truncResolvent ε H E = cfc (fun x => truncInv ε (x - E)) H := by
  by_cases hH : H.IsHermitian
  · exact truncResolvent_eq_cfc hH ε E
  · simp only [truncResolvent, hH, ↓reduceDIte]
    exact (cfc_apply_of_not_predicate _ (fun h => hH h)).symm

/-- **`H ↦ g_ε(H - E)` is Borel measurable** (`ε > 0`). -/
theorem measurable_truncResolvent {ε : ℝ} (hε : 0 < ε) (E : ℝ) :
    Measurable (fun H : Matrix α α ℂ => truncResolvent ε H E) := by
  simp_rw [truncResolvent_eq_cfc']
  have hS : MeasurableSet {H : Matrix α α ℂ | H.IsHermitian} :=
    (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
  refine measurable_of_restrict_of_restrict_compl hS
    (continuous_truncResolvent_herm hε E).measurable ?_
  have : (({H : Matrix α α ℂ | H.IsHermitian}ᶜ).domRestrict
      fun H => cfc (fun x => truncInv ε (x - E)) H) = fun _ => 0 := by
    funext H
    exact cfc_apply_of_not_predicate _ (fun h => H.2 h)
  rw [this]
  exact measurable_const

/-- Entrywise measurability of a matrix product of measurable matrix-valued maps. -/
theorem measurable_matrix_mul' {X : Type*} [MeasurableSpace X] {γ : Type} [Fintype γ]
    {f : X → Matrix β γ ℂ} {g : X → Matrix γ α ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => f x * g x) := by
  refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
  simp only [mul_apply]
  refine Finset.measurable_sum _ fun k _ => ?_
  exact ((measurable_pi_apply k).comp ((measurable_pi_apply a).comp hf)).mul
    ((measurable_pi_apply b).comp ((measurable_pi_apply k).comp hg))

/-- **`(H_R, C, V) ↦ F̂(E) = V - C* g_ε(H_R - E) C` is Borel measurable** (`ε > 0`, fixed `E`). -/
theorem measurable_truncF {ε : ℝ} (hε : 0 < ε) (E : ℝ) :
    Measurable (fun om : Matrix α α ℂ × Matrix α β ℂ × Matrix β β ℂ =>
      truncF ε om.1 om.2.1 om.2.2 E) := by
  unfold truncF
  have h1 : Measurable (fun om : Matrix α α ℂ × Matrix α β ℂ × Matrix β β ℂ =>
      truncResolvent ε om.1 E) := (measurable_truncResolvent hε E).comp measurable_fst
  have hC : Measurable (fun om : Matrix α α ℂ × Matrix α β ℂ × Matrix β β ℂ => om.2.1) :=
    measurable_fst.comp measurable_snd
  have hCh : Measurable (fun om : Matrix α α ℂ × Matrix α β ℂ × Matrix β β ℂ => om.2.1ᴴ) := by
    refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
    simp only [conjTranspose_apply]
    exact Complex.continuous_conj.measurable.comp
      ((measurable_pi_apply a).comp ((measurable_pi_apply b).comp hC))
  exact (measurable_snd.comp measurable_snd).sub
    (measurable_matrix_mul' (measurable_matrix_mul' hCh h1) hC)

end BlockBand.LocalWindow.ProofCount
