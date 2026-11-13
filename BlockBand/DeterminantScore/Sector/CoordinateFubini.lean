module

public import BlockBand.DeterminantScore.Sector.Statement
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini along one real coordinate of a finite product measure

A product measure on `σ → ℝ` splits as the product of the measure of one coordinate `c` and the
product over the others (`coordSplit`); hence integrals are iterated along `c`
(`integral_eq_iterated`) and almost every coordinate line of an integrable function is integrable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.Sector

open MeasureTheory

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Insert the coordinate `c = s` into a vector of the complementary coordinates. -/
def insertCoord (c : σ) (s : ℝ) (y : {j // ¬ j = c} → ℝ) : σ → ℝ :=
  fun j => if h : j = c then s else y ⟨j, h⟩

omit [Fintype σ] in
theorem insertCoord_self (c : σ) (s : ℝ) (y : {j // ¬ j = c} → ℝ) :
    insertCoord c s y c = s := by
  simp [insertCoord]

omit [Fintype σ] in
theorem insertCoord_eq_update (c : σ) (s : ℝ) (y : {j // ¬ j = c} → ℝ) :
    insertCoord c s y = Function.update (insertCoord c 0 y) c s := by
  funext j
  by_cases h : j = c
  · subst h; simp [insertCoord]
  · simp [insertCoord, h]

/-- The singleton subtype `{j // j = c}`. -/
abbrev uniqueEqCoord (c : σ) : Unique {j // j = c} where
  default := ⟨c, rfl⟩
  uniq d := Subtype.ext d.2

/-- The split `x ↦ (x c, (x j)_{j ≠ c})`. -/
def coordSplit (c : σ) : (σ → ℝ) ≃ᵐ ℝ × ({j // ¬ j = c} → ℝ) :=
  letI := uniqueEqCoord c
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : σ => ℝ) (fun j => j = c)).trans
    ((MeasurableEquiv.piUnique (fun _ : {j // j = c} => ℝ)).prodCongr (MeasurableEquiv.refl _))

omit [Fintype σ] in
theorem coordSplit_symm_apply (c : σ) (q : ℝ × ({j // ¬ j = c} → ℝ)) :
    (coordSplit c).symm q = insertCoord c q.1 q.2 := by
  let _ := uniqueEqCoord c
  have hdefault : ((default : {j // j = c}) : σ) = c := (default : {j // j = c}).2
  apply (coordSplit c).injective
  simp only [MeasurableEquiv.apply_symm_apply]
  apply Prod.ext
  · simp [coordSplit, insertCoord, MeasurableEquiv.prodCongr, hdefault]
  · funext d
    simp [coordSplit, insertCoord, MeasurableEquiv.prodCongr, d.2]

theorem measurePreserving_coordSplit (ν : σ → Measure ℝ) [∀ i, SigmaFinite (ν i)] (c : σ) :
    MeasurePreserving (coordSplit c) (Measure.pi ν)
      ((ν c).prod (Measure.pi fun j : {j // ¬ j = c} => ν j)) := by
  let _ := uniqueEqCoord c
  let _ : Fintype {j // j = c} := Subtype.fintype (fun j => j = c)
  have hpred := measurePreserving_piEquivPiSubtypeProd ν (fun j => j = c)
  have hsel := measurePreserving_piUnique (fun d : {j // j = c} => ν d)
  have hcomp : MeasurePreserving
      (MeasurableEquiv.refl ({j // ¬ j = c} → ℝ))
      (Measure.pi fun j : {j // ¬ j = c} => ν j) (Measure.pi fun j : {j // ¬ j = c} => ν j) :=
    MeasurePreserving.id _
  exact (hsel.prod hcomp).comp hpred

variable (ν : σ → Measure ℝ) [∀ i, SigmaFinite (ν i)]

theorem integrable_insertCoord_iff (c : σ) {E : Type*} [NormedAddCommGroup E]
    (F : (σ → ℝ) → E) :
    Integrable (fun q : ℝ × ({j // ¬ j = c} → ℝ) => F (insertCoord c q.1 q.2))
        ((ν c).prod (Measure.pi fun j : {j // ¬ j = c} => ν j)) ↔
      Integrable F (Measure.pi ν) := by
  have h := (measurePreserving_coordSplit ν c).symm
  have hiff := h.integrable_comp_emb (coordSplit c).symm.measurableEmbedding (g := F)
  rw [← hiff]
  apply integrable_congr
  filter_upwards with q
  simp [coordSplit_symm_apply]

/-- Fubini along the coordinate `c`. -/
theorem integral_eq_iterated (c : σ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (σ → ℝ) → E) (hF : Integrable F (Measure.pi ν)) :
    (∫ x, F x ∂Measure.pi ν) =
      ∫ y, ∫ s, F (insertCoord c s y) ∂ν c ∂Measure.pi fun j : {j // ¬ j = c} => ν j := by
  have h := (measurePreserving_coordSplit ν c).integral_comp'
    (fun q => F ((coordSplit c).symm q))
  simp only [MeasurableEquiv.symm_apply_apply] at h
  rw [h]
  simp_rw [coordSplit_symm_apply]
  exact integral_prod_symm _ ((integrable_insertCoord_iff ν c F).2 hF)

/-- Almost every coordinate line of an integrable function is integrable. -/
theorem ae_integrable_line (c : σ) {E : Type*} [NormedAddCommGroup E]
    (F : (σ → ℝ) → E) (hF : Integrable F (Measure.pi ν)) :
    ∀ᵐ y ∂Measure.pi (fun j : {j // ¬ j = c} => ν j),
      Integrable (fun s => F (insertCoord c s y)) (ν c) :=
  ((integrable_insertCoord_iff ν c F).2 hF).prod_left_ae

end BlockBand.DeterminantScore.Sector
