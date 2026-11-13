module

public import BlockBand.Transmission.Bridge.GueNull

/-!
# The unabsorbed path pencil `H_j - E` is almost surely invertible (`b < 1/2`)

Along the near-end filtration and the passive update.

Induction on the length along the near-end growth: newest block first,
`H_{j+1} - E = [[A_j - E, C_nᴴ],[C_n, H_j - E]]` (`pathMatrix_succ_submatrix`), so when
`H_j - E` is invertible `det(H_{j+1} - E) = det(H_j - E) · det(A_j + C_j)` with
`C_j = -E - C_nᴴ(H_j - E)⁻¹C_n` a function of the past (`det_pathPencil_succ`). The fresh block
`A_j ~ GUE_W(((1-2b)/W)₊)` is independent of the past (`growthPathLaw_map_past_fresh`), so
Fubini and `ae_det_gue_add_ne_zero` give the step.

Main results, for `b < 1/2` and `W ≥ 1` (no lower bound on `b` is needed here):
`ae_isUnit_pathPencil_growth` (every `j`, under `growthPathLaw`) and
`ae_isUnit_pathPencil_pathLaw` (under `pathLaw W r b`, every `r`). For `b ≥ 1/2` the
GUE factor is `δ₀` and the statement is not claimed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Bridge

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix

variable {W : ℕ}

theorem measurable_pathMatrix (r : ℕ) : Measurable fun p : PathSample W r => pathMatrix p := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [pathMatrix]
  split_ifs
  · exact Matrix.measurable_apply.comp ((measurable_pi_apply _).comp measurable_fst)
  · exact Matrix.measurable_apply.comp ((measurable_pi_apply _).comp
      (measurable_fst.comp measurable_snd))
  · exact Complex.continuous_conj.measurable.comp (Matrix.measurable_apply.comp
      ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)))
  · exact measurable_const

theorem measurable_pathPortCoupling (r : ℕ) :
    Measurable fun p : PathSample W r => pathPortCoupling p := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [pathPortCoupling]
  split_ifs
  · exact Matrix.measurable_apply.comp ((measurable_pi_apply _).comp
      (measurable_snd.comp measurable_snd))
  · exact measurable_const

theorem measurable_pathOfPast (r : ℕ) : Measurable (pathOfPast W r) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact Measurable.of_eval fun i => (measurable_pi_apply _).comp measurable_fst
  · exact Measurable.of_eval fun i =>
      measurable_matrix_conjTranspose' ((measurable_pi_apply _).comp measurable_snd)
  · refine Measurable.of_eval fun j => ?_
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact (measurable_pi_apply _).comp measurable_snd
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact (measurable_pi_apply _).comp measurable_snd

/-- The unabsorbed pencil as a function of the past coordinates. -/
def pastPencil (E : ℝ) (W j : ℕ)
    (p : (Fin j → Matrix (Fin W) (Fin W) ℂ) × (Fin (j + 1) → Matrix (Fin W) (Fin W) ℂ)) :
    Matrix (Fin j × Fin W) (Fin j × Fin W) ℂ :=
  pathMatrix (pathOfPast W j p) - (E : ℂ) • 1

/-- The Schur shift `C_j = -E - C_nᴴ(H_j - E)⁻¹C_n` as a function of the past coordinates. -/
def pastShift (E : ℝ) (W j : ℕ)
    (p : (Fin j → Matrix (Fin W) (Fin W) ℂ) × (Fin (j + 1) → Matrix (Fin W) (Fin W) ℂ)) :
    Matrix (Fin W) (Fin W) ℂ :=
  let Cn : Matrix (Fin j × Fin W) (Fin W) ℂ := fun a y => pathPortCoupling (pathOfPast W j p) a (0, y)
  (-((E : ℂ) • 1) - Cnᴴ * (pastPencil E W j p)⁻¹ * Cn)

theorem measurable_pastPencil (E : ℝ) (j : ℕ) : Measurable (pastPencil E W j) := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [pastPencil, Matrix.sub_apply]
  exact ((measurable_pathMatrix j).comp (measurable_pathOfPast j)).eval_matrix.sub measurable_const

theorem measurable_pastShift (E : ℝ) (j : ℕ) : Measurable (pastShift E W j) := by
  have hCn : Measurable fun p : (Fin j → Matrix (Fin W) (Fin W) ℂ) ×
      (Fin (j + 1) → Matrix (Fin W) (Fin W) ℂ) =>
      (fun a y => pathPortCoupling (pathOfPast W j p) a (0, y) :
        Matrix (Fin j × Fin W) (Fin W) ℂ) :=
    Measurable.of_eval_matrix _ fun x y =>
      ((measurable_pathPortCoupling j).comp (measurable_pathOfPast j)).eval_matrix
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [pastShift, Matrix.sub_apply]
  exact measurable_const.sub (measurable_matrix_mul' (measurable_matrix_mul'
    (measurable_matrix_conjTranspose' hCn) (measurable_matrix_inv.comp
      (measurable_pastPencil E j))) hCn).eval_matrix

theorem pathPencil_eq_past (E : ℝ) (j : ℕ) (ω : GrowthPath W) :
    pathMatrix (pathAt W j ω) - (E : ℂ) • 1 = pastPencil E W j (pastCoords W j ω) := by
  rw [pastPencil, pathAt_eq_pathOfPast]; rfl

/-- **Schur step**: `det(H_{j+1} - E) = det(H_j - E) · det(A_j + C_j)` when `H_j - E` is
invertible. -/
theorem det_pathPencil_succ (E : ℝ) (j : ℕ) (ω : GrowthPath W)
    (hD : IsUnit (pathMatrix (pathAt W j ω) - (E : ℂ) • 1)) :
    (pathMatrix (pathAt W (j + 1) ω) - (E : ℂ) • 1).det =
      (pathMatrix (pathAt W j ω) - (E : ℂ) • 1).det *
        ((freshSample W j ω).1 0 + pastShift E W j (pastCoords W j ω)).det := by
  let : Invertible (pathMatrix (pathAt W j ω) - (E : ℂ) • 1) := hD.invertible
  rw [← Matrix.det_submatrix_equiv_self (headEquiv j W), pathMatrix_succ_submatrix,
    Matrix.det_fromBlocks₂₂, invOf_eq_nonsing_inv]
  congr 2
  rw [pastShift, ← pathPencil_eq_past]
  simp only [freshSample, pathAt_eq_pathOfPast, Function.comp]
  abel

theorem freshLaw_map_block (W : ℕ) (b : ℝ) :
    (freshLaw W b).map (fun f => f.1 0) = gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W)) := by
  rw [show (fun f : LayerSample W .oneBlockOnePort => f.1 0) = (fun v => v 0) ∘ Prod.fst from rfl,
    ← Measure.map_map (measurable_pi_apply 0) measurable_fst, freshLaw, layerLaw,
    Measure.map_fst_prod, measure_univ, one_smul]
  exact (measurePreserving_eval _ 0).map_eq

/-- The pencil `H_j - E` is singular only on a null set, for every length `j`. -/
theorem growth_det_pathPencil_null {b : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) :
    ∀ j : ℕ, growthPathLaw W b {ω | (pathMatrix (pathAt W j ω) - (E : ℂ) • 1).det = 0} = 0
  | 0 => by simp [Matrix.det_isEmpty]
  | j + 1 => by
    set T : Set (((Fin j → Matrix (Fin W) (Fin W) ℂ) × (Fin (j + 1) → Matrix (Fin W) (Fin W) ℂ)) ×
        LayerSample W .oneBlockOnePort) :=
      {q | (pastPencil E W j q.1).det ≠ 0 ∧ (q.2.1 0 + pastShift E W j q.1).det = 0}
    have hT : MeasurableSet T := by
      refine ((measurableSet_singleton 0).compl.preimage
        (measurable_det.comp ((measurable_pastPencil E j).comp measurable_fst))).inter
        ((measurableSet_singleton 0).preimage (measurable_det.comp ?_))
      refine Measurable.of_eval_matrix _ fun x y => ?_
      simp only [Matrix.add_apply]
      exact (Matrix.measurable_apply.comp ((measurable_pi_apply 0).comp
        (measurable_fst.comp measurable_snd))).add
        ((measurable_pastShift E j).comp measurable_fst).eval_matrix
    have hsub : {ω | (pathMatrix (pathAt W (j + 1) ω) - (E : ℂ) • 1).det = 0} ⊆
        {ω | (pathMatrix (pathAt W j ω) - (E : ℂ) • 1).det = 0} ∪
          (fun ω => (pastCoords W j ω, freshSample W j ω)) ⁻¹' T := by
      intro ω hω
      by_cases h : (pathMatrix (pathAt W j ω) - (E : ℂ) • 1).det = 0
      · exact Or.inl h
      · right
        have hD : IsUnit (pathMatrix (pathAt W j ω) - (E : ℂ) • 1) :=
          (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)
        simp only [Set.mem_ofPred_eq, det_pathPencil_succ E j ω hD, mul_eq_zero] at hω
        refine ⟨by rwa [← pathPencil_eq_past], hω.resolve_left h⟩
    refine measure_mono_null hsub (measure_union_null (growth_det_pathPencil_null hb hW E j) ?_)
    rw [← Measure.map_apply ((measurable_pastCoords W j).prodMk (measurable_freshSample W j)) hT,
      growthPathLaw_map_past_fresh, Measure.measure_prod_null hT]
    refine Filter.Eventually.of_forall fun p => ?_
    have hA := ae_det_gue_add_ne_zero W (gueVariance_ne_zero hb hW) (pastShift E W j p)
    rw [ae_iff, ← freshLaw_map_block W b, Measure.map_apply (by
      exact (measurable_pi_apply 0).comp measurable_fst)] at hA
    · simp only [Pi.zero_apply]
      refine measure_mono_null (fun f hf => ?_) hA
      simpa [T] using hf.2
    · exact (measurableSet_singleton 0).compl.compl.preimage (measurable_det.comp
        (Measurable.of_eval_matrix _ fun x y => Matrix.measurable_apply.add measurable_const))

/-- **Near-end growth**: for `b < 1/2`, `W ≥ 1`, almost surely the unabsorbed pencil
`H_j - E` is invertible for every length `j`. -/
theorem ae_isUnit_pathPencil_growth {b : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, IsUnit (pathMatrix (pathAt W j ω) - (E : ℂ) • 1) := by
  rw [ae_all_iff]
  intro j
  rw [ae_iff]
  simpa [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] using
    growth_det_pathPencil_null hb hW E j

/-- **The path law**: for `b < 1/2`, `W ≥ 1` and every `r`, `H_path - E` is
`pathLaw W r b`-almost surely invertible. -/
theorem ae_isUnit_pathPencil_pathLaw {b : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) (r : ℕ) :
    ∀ᵐ ω ∂pathLaw W r b, IsUnit (pathMatrix ω - (E : ℂ) • 1) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact Filter.Eventually.of_forall fun ω => by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_isEmpty]; exact isUnit_one
  have hset : MeasurableSet {ω : PathSample W r | IsUnit (pathMatrix ω - (E : ℂ) • 1)} := by
    have : {ω : PathSample W r | IsUnit (pathMatrix ω - (E : ℂ) • 1)} =
        (fun ω => (pathMatrix ω - (E : ℂ) • 1).det) ⁻¹' {0}ᶜ := by
      ext ω; simp [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    rw [this]
    refine (measurableSet_singleton 0).compl.preimage (measurable_det.comp ?_)
    exact Measurable.of_eval_matrix _ fun x y =>
      (measurable_pathMatrix r).eval_matrix.sub measurable_const
  have hpath : Measurable (pathAt W r) := by
    rw [pathAt_eq_pathOfPast]; exact (measurable_pathOfPast r).comp (measurable_pastCoords W r)
  rw [← growthPathLaw_map_pathAt W b hr, ae_map_iff hpath.aemeasurable hset]
  exact (ae_isUnit_pathPencil_growth hb hW E).mono fun ω h => h r

end BlockBand.Transmission.Bridge
