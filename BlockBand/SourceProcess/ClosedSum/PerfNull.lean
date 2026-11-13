module

public import BlockBand.SourceProcess.ClosedSum.PerfStep
public import BlockBand.Transmission.Bridge.PencilAE

/-!
# The modified pencil is almost surely invertible, for all lead constants

**`ae_isUnit_modPencil`** (`b < 1/2`, `W ≥ 1`, every `E ∈ ℝ`, `u, v ∈ ℂ`): almost surely, for
every length `n`, `modPencil E u v (pathAt W n ω)` is invertible.

Induction along the near-end growth, as in
`growth_det_pathPencil_null`, but the shift of the fresh block may also depend on the
fresh near bond `B_{j+1}`: conditionally on the past and on `B_{j+1}`, the fresh GUE block
`A_j` is independent, so `det(A_j + C) ≠ 0` a.s. (`ae_det_gue_add_ne_zero` and Tonelli,
`Measure.prod_apply_symm`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSum

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge
open scoped ENNReal NNReal

variable {W : ℕ}

abbrev PastC (W j : ℕ) :=
  (Fin j → Matrix (Fin W) (Fin W) ℂ) × (Fin (j + 1) → Matrix (Fin W) (Fin W) ℂ)

theorem measurable_colOf {α : Type*} [MeasurableSpace α] {r : ℕ}
    {f : α → Matrix (Fin r × Fin W) (Fin 2 × Fin W) ℂ} (hf : Measurable f) (i : Fin 2) :
    Measurable fun a => colOf (f a) i :=
  Measurable.of_eval_matrix _ fun _ _ => hf.eval_matrix

theorem measurable_modPencil (E : ℝ) (u v : ℂ) (r : ℕ) :
    Measurable fun p : PathSample W r => modPencil E u v p := by
  have hC := measurable_pathPortCoupling (W := W) r
  have hL : Measurable fun p : PathSample W r => portLoad u v p := by
    refine Measurable.of_eval_matrix _ fun x y => ?_
    simp only [portLoad, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact (measurable_const.mul (measurable_matrix_mul' (measurable_colOf hC 0)
      (measurable_matrix_conjTranspose' (measurable_colOf hC 0))).eval_matrix).add
      (measurable_const.mul (measurable_matrix_mul' (measurable_colOf hC 1)
      (measurable_matrix_conjTranspose' (measurable_colOf hC 1))).eval_matrix)
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [modPencil, Matrix.sub_apply]
  exact ((measurable_pathMatrix r).eval_matrix.sub measurable_const).sub hL.eval_matrix

/-- The shift of the fresh block, as a function of the past and of the fresh near bond. -/
def pastShiftMod (E : ℝ) (u v : ℂ) (j : ℕ) (p : PastC W j) (B : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  -((E : ℂ) • 1) - (u • (B * Bᴴ) + if j = 0 then v • (p.2 0 * (p.2 0)ᴴ) else 0) -
    (colOf (pathPortCoupling (pathOfPast W j p)) 0)ᴴ *
      (modPencil E 0 v (pathOfPast W j p))⁻¹ * colOf (pathPortCoupling (pathOfPast W j p)) 0

theorem measurable_pastShiftMod (E : ℝ) (u v : ℂ) (j : ℕ) :
    Measurable fun q : PastC W j × Matrix (Fin W) (Fin W) ℂ => pastShiftMod E u v j q.1 q.2 := by
  have hP : Measurable fun q : PastC W j × Matrix (Fin W) (Fin W) ℂ => pathOfPast W j q.1 :=
    (measurable_pathOfPast (W := W) j).comp measurable_fst
  have hC := measurable_colOf ((measurable_pathPortCoupling j).comp hP) 0
  have hK := measurable_matrix_inv.comp ((measurable_modPencil E 0 v j).comp hP)
  have hB0 : Measurable fun q : PastC W j × Matrix (Fin W) (Fin W) ℂ => q.1.2 0 :=
    (measurable_pi_apply 0).comp (measurable_snd.comp measurable_fst)
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [pastShiftMod, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine (measurable_const.sub (measurable_const.mul (measurable_matrix_mul' measurable_snd
    (measurable_matrix_conjTranspose' measurable_snd)).eval_matrix |>.add ?_)).sub
    (measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' hC) hK)
      hC).eval_matrix
  split_ifs
  · exact measurable_const.mul (measurable_matrix_mul' hB0
      (measurable_matrix_conjTranspose' hB0)).eval_matrix
  · exact measurable_const

theorem det_modPencil_succ_past (E : ℝ) (u v : ℂ) (j : ℕ) (ω : GrowthPath W)
    (hK : IsUnit (modPencil E 0 v (pathAt W j ω))) :
    (modPencil E u v (pathAt W (j + 1) ω)).det = (modPencil E 0 v (pathAt W j ω)).det *
      ((freshSample W j ω).1 0 + pastShiftMod E u v j (pastCoords W j ω)
        ((freshSample W j ω).2 0 0)).det := by
  rw [det_modPencil_succ E u v j ω hK]
  congr 2
  simp only [pastShiftMod, headLoad, freshSample, pastCoords, Fin.val_zero]
  change _ = ω.1 j + (_ - _ - (nearCol W j ω)ᴴ * _ * nearCol W j ω)
  abel

theorem measurableSet_fresh_det {α : Type*} [MeasurableSpace α]
    {c : α × Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ} (hc : Measurable c) :
    MeasurableSet {q : α × LayerSample W .oneBlockOnePort | (q.2.1 0 + c (q.1, q.2.2 0 0)).det = 0} := by
  refine (measurableSet_singleton 0).preimage (measurable_det.comp ?_)
  have hB : Measurable fun q : α × LayerSample W .oneBlockOnePort => q.2.2 0 0 :=
    (measurable_pi_apply 0).comp ((measurable_pi_apply 0).comp (measurable_snd.comp measurable_snd))
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [Matrix.add_apply]
  exact (Matrix.measurable_apply.comp ((measurable_pi_apply 0).comp
    (measurable_fst.comp measurable_snd))).add (hc.comp (measurable_fst.prodMk hB)).eval_matrix

/-- **Tonelli over the fresh layer**: the fresh GUE block plus any measurable function of the past
and of the fresh near bond is a.s. invertible. -/
theorem fresh_det_null {b : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] {c : α × Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ}
    (hc : Measurable c) :
    (μ.prod (freshLaw W b)) {q | (q.2.1 0 + c (q.1, q.2.2 0 0)).det = 0} = 0 := by
  have hs := measurableSet_fresh_det (W := W) hc
  rw [Measure.measure_prod_null hs]
  refine Filter.Eventually.of_forall fun p => ?_
  have hs' := measurable_prodMk_left (x := p) hs
  set gue := gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))
  change (freshLaw W b) (Prod.mk p ⁻¹' _) = 0
  rw [show freshLaw W b = (Measure.pi fun _ : Fin 1 => gue).prod
      (Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin 1 =>
        ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) from rfl,
    Measure.prod_apply_symm hs']
  refine (lintegral_congr fun y => ?_).trans lintegral_zero
  set S := {M : Matrix (Fin W) (Fin W) ℂ | (M + c (p, y 0 0)).det = 0}
  have hS : MeasurableSet S := (measurableSet_singleton 0).preimage (measurable_det.comp
    (Measurable.of_eval_matrix _ fun x y => Matrix.measurable_apply.add measurable_const))
  have hpre : (fun x => (x, y)) ⁻¹' (Prod.mk p ⁻¹' {q : α × LayerSample W .oneBlockOnePort |
      (q.2.1 0 + c (q.1, q.2.2 0 0)).det = 0}) = (fun A : Fin 1 → Matrix (Fin W) (Fin W) ℂ => A 0) ⁻¹' S :=
    rfl
  rw [hpre, ← Measure.map_apply (measurable_pi_apply 0) hS, (measurePreserving_eval _ 0).map_eq]
  have hA := ae_det_gue_add_ne_zero W (gueVariance_ne_zero hb hW) (c (p, y 0 0))
  rw [ae_iff] at hA
  simpa [S] using hA

/-- One growth step of the null set. -/
theorem growth_modPencil_step {b : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) (u v : ℂ) (j : ℕ)
    (hP : growthPathLaw W b {ω | (modPencil E 0 v (pathAt W j ω)).det = 0} = 0) :
    growthPathLaw W b {ω | (modPencil E u v (pathAt W (j + 1) ω)).det = 0} = 0 := by
  have hc := measurable_pastShiftMod (W := W) E u v j
  set T := {q : PastC W j × LayerSample W .oneBlockOnePort |
    (q.2.1 0 + pastShiftMod E u v j q.1 (q.2.2 0 0)).det = 0}
  have hT : MeasurableSet T := measurableSet_fresh_det hc
  have hsub : {ω | (modPencil E u v (pathAt W (j + 1) ω)).det = 0} ⊆
      {ω | (modPencil E 0 v (pathAt W j ω)).det = 0} ∪
        (fun ω => (pastCoords W j ω, freshSample W j ω)) ⁻¹' T := by
    intro ω hω
    by_cases h : (modPencil E 0 v (pathAt W j ω)).det = 0
    · exact Or.inl h
    · right
      have hK : IsUnit (modPencil E 0 v (pathAt W j ω)) :=
        (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)
      simp only [Set.mem_ofPred_eq, det_modPencil_succ_past E u v j ω hK, mul_eq_zero] at hω
      exact hω.resolve_left h
  refine measure_mono_null hsub (measure_union_null hP ?_)
  rw [← Measure.map_apply ((measurable_pastCoords W j).prodMk (measurable_freshSample W j)) hT,
    growthPathLaw_map_past_fresh]
  exact fresh_det_null hb hW (pastLaw W j b) hc

theorem growth_modPencil_null {b : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) (v : ℂ) :
    ∀ j, growthPathLaw W b {ω | (modPencil E 0 v (pathAt W j ω)).det = 0} = 0
  | 0 => by simp [Matrix.det_isEmpty]
  | j + 1 => growth_modPencil_step hb hW E 0 v j (growth_modPencil_null hb hW E v j)

/-- **The modified pencil is a.s. invertible at every length**, for all lead constants `u, v`. -/
theorem ae_isUnit_modPencil {b : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) (u v : ℂ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ n, IsUnit (modPencil E u v (pathAt W n ω)) := by
  rw [ae_all_iff]
  intro n
  rw [ae_iff]
  rcases n with _ | j
  · have h0 : ∀ ω, IsUnit (modPencil E u v (pathAt W 0 ω)) := fun ω => by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_isEmpty]; exact isUnit_one
    rw [show {ω | ¬IsUnit (modPencil E u v (pathAt W 0 ω))} = ∅ from
      Set.eq_empty_of_forall_notMem fun ω h => h (h0 ω), measure_empty]
  · simpa [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] using
      growth_modPencil_step hb hW E u v j (growth_modPencil_null hb hW E v j)

end BlockBand.SourceProcess.ClosedSum
