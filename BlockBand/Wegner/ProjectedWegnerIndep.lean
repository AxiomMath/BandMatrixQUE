module

public import Mathlib
public import BlockBand.Internal.Contracts.Inputs

/-!
# Fully independent block models have fresh blocks

In a block model with mutually independent `GUE_W(c/W)` blocks independent of `(D, Y)`
(`Internal.Contracts.Inputs.BlockModel.IsIndependent c`), each block `A_j` is independent of
`(D, Y, A_{-j})`. Law: the model probability `M.P`; no norm or other hypothesis.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

open MeasureTheory ProbabilityTheory

/-- Exchange lemma for independence. On a probability space `μ`, for measurable `U`, `V`, `Z`
with values in arbitrary measurable spaces: if `U` is independent of the pair `(V, Z)` and `V`
is independent of `Z`, then `V` is independent of the pair `(U, Z)`. Proof via laws: the law
of `(U, (V, Z))` is `μ_U ⊗ (μ_V ⊗ μ_Z)`, and the law of `(V, (U, Z))` is its image under the
measure-preserving reassociation `(u, (v, z)) ↦ (v, (u, z))`. Used for the single-block
reduction of the projected Wegner estimate. -/
theorem indepFun_prodMk_of_indepFun_prodMk {Ω α β γ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {U : Ω → α} {V : Ω → β} {Z : Ω → γ}
    (hU : Measurable U) (hV : Measurable V) (hZ : Measurable Z)
    (h1 : IndepFun U (fun w => (V w, Z w)) μ) (h2 : IndepFun V Z μ) :
    IndepFun V (fun w => (U w, Z w)) μ := by
  have hVZ : Measurable (fun w => (V w, Z w)) := hV.prodMk hZ
  have hUZ : Measurable (fun w => (U w, Z w)) := hU.prodMk hZ
  rw [indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hVZ.aemeasurable] at h1
  rw [indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hZ.aemeasurable] at h2
  rw [indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hUZ.aemeasurable]
  rw [h2] at h1
  -- the law of `(U, Z)`
  have hlawUZ : μ.map (fun w => (U w, Z w)) = (μ.map U).prod (μ.map Z) := by
    have hm : Measurable (fun p : α × β × γ => (p.1, p.2.2)) := by fun_prop
    have : (fun w => (U w, Z w)) = (fun p : α × β × γ => (p.1, p.2.2)) ∘
        (fun w => (U w, V w, Z w)) := rfl
    rw [this, ← Measure.map_map hm (hU.prodMk hVZ), h1]
    have : (fun p : α × β × γ => (p.1, p.2.2)) = Prod.map id Prod.snd := rfl
    rw [this, ← Measure.map_prod_map _ _ measurable_id measurable_snd, Measure.map_id,
      Measure.map_snd_prod, measure_univ, one_smul]
  rw [hlawUZ]
  -- the reassociation `(u, (v, z)) ↦ (v, (u, z))`
  let σ : α × β × γ → β × α × γ := fun p => (p.2.1, p.1, p.2.2)
  have hσ : Measurable σ := by fun_prop
  have hmp : MeasurePreserving σ ((μ.map U).prod ((μ.map V).prod (μ.map Z)))
      ((μ.map V).prod ((μ.map U).prod (μ.map Z))) := by
    have e1 := (measurePreserving_prodAssoc (μ.map U) (μ.map V) (μ.map Z)).symm
    have e2 := ((Measure.measurePreserving_swap (μ := μ.map U) (ν := μ.map V)).prod
      (MeasurePreserving.id (μ.map Z)))
    have e3 := measurePreserving_prodAssoc (μ.map V) (μ.map U) (μ.map Z)
    exact (e3.comp e2).comp e1
  have : (fun w => (V w, U w, Z w)) = σ ∘ (fun w => (U w, V w, Z w)) := rfl
  rw [this, ← Measure.map_map hσ (hU.prodMk hVZ), h1, hmp.map_eq]

/-- Single-block reduction of the projected Wegner estimate (for a single block `j` it suffices
that `D` and `Y` are independent of `A_j`), law side. Let `M` be a block model
(`Internal.Contracts.Inputs.BlockModel k W`, law `M.P`) satisfying `M.IsIndependent c`: each
`A_j ~ GUE_W(c/W)` (`gueMatrixLaw W (c/W).toNNReal`), the blocks are mutually independent, and
`(D, Y)` is independent of the whole block family. Then for every `j : Fin k`,
`M.IsFreshBlock c j`: `A_j ~ GUE_W(c/W)` and `A_j` is independent of `(D, Y, A_{-j})` with
`A_{-j}` the family with block `j` set to `0`. Uniform in `k`, `W`, `c` (no sign condition). -/
theorem isFreshBlock_of_isIndependent {k W : ℕ} (M : Internal.Contracts.Inputs.BlockModel k W)
    (c : ℝ) (h : M.IsIndependent c) (j : Fin k) : M.IsFreshBlock c j := by
  obtain ⟨hlaw, hiInd, hInd⟩ := h
  refine ⟨hlaw j, ?_⟩
  classical
  set β := Matrix (Fin W) (Fin W) ℂ
  have hAi : ∀ i, Measurable (fun w => M.A w i) := fun i =>
    (measurable_pi_apply i).comp M.measurable_A
  let Zf : (Fin k → β) → (Fin k → β) := fun a i => if i = j then 0 else a i
  have hZf : Measurable Zf := by
    refine measurable_pi_iff.mpr fun i => ?_
    by_cases hij : i = j
    · simp [Zf, hij]
    · simp only [Zf, hij, ↓reduceIte]
      fun_prop
  let Z : M.Ω → Fin k → β := fun w => Zf (M.A w)
  have hZ : Measurable Z := hZf.comp M.measurable_A
  -- `(D, Y)` is independent of `(A_j, A_{-j})`
  have h1 : IndepFun (fun w => (M.D w, M.Y w)) (fun w => (M.A w j, Z w)) M.P := by
    have hφ : Measurable (fun a : Fin k → β => (a j, Zf a)) :=
      (measurable_pi_apply j).prodMk hZf
    exact hInd.comp measurable_id hφ
  -- `A_j` is independent of `A_{-j}`
  have h2 : IndepFun (fun w => M.A w j) Z M.P := by
    have hST : Disjoint ({j} : Finset (Fin k)) {j}ᶜ := disjoint_compl_right
    have h0 := hiInd.indepFun_finset {j} {j}ᶜ hST hAi
    let ψ1 : (({j} : Finset (Fin k)) → β) → β := fun x => x ⟨j, Finset.mem_singleton_self j⟩
    let ψ2 : (({j}ᶜ : Finset (Fin k)) → β) → (Fin k → β) := fun x i =>
      if hi : i = j then 0 else x ⟨i, by simpa using hi⟩
    have hψ1 : Measurable ψ1 := measurable_pi_apply _
    have hψ2 : Measurable ψ2 := by
      refine measurable_pi_iff.mpr fun i => ?_
      by_cases hij : i = j
      · simp [ψ2, hij]
      · simp only [ψ2, hij]
        fun_prop
    have h3 := h0.comp hψ1 hψ2
    have hZeq : Z = ψ2 ∘ (fun w (i : ({j}ᶜ : Finset (Fin k))) => M.A w i) := by
      funext w i
      by_cases hij : i = j <;> simp [Z, Zf, ψ2, hij]
    rw [hZeq]
    exact h3
  have h4 := indepFun_prodMk_of_indepFun_prodMk (M.measurable_D.prodMk M.measurable_Y)
    (hAi j) hZ h1 h2
  have hre : Measurable (fun p : (Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ ×
      Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) × (Fin k → β) => (p.1.1, p.1.2, p.2)) := by
    fun_prop
  exact h4.comp measurable_id hre

end BlockBand.Wegner
