module

public import BlockBand.SourceProcess.ModelExist.TransLoc

/-!
# Weighted increments after stopping times: complex `LocMart`s and their products

For a finite family `A_x` of processes, a stopping time `σ` and `𝓕_σ`-measurable weights `w_x`,
`tRep σ w A = Σ_x w_x (A_x − A_x^σ)`.
* `cLocMart_tRep`: if every `A_x` is a `CLocMart` with drift `0`, so is `tRep σ w A`;
* `cLocMart_tRep_mul`: if moreover `A_x B_y` has drift `Γ_xy`, then
  `tRep σ₁ w₁ A · tRep σ₂ w₂ B` has drift `Σ 1{σ₁ ∨ σ₂ < s} w₁_x w₂_y Γ_xy(s)`
  (`CLocMart.pair`, then the `𝓕_{σ₁ ∨ σ₂}`-measurable weight, `CLocMart.weight`);
* `star_tRep`: `conj(tRep σ w A) = tRep σ (conj w) (conj A)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexConstruct

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped NNReal ENNReal Topology
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale BlockBand.SourceProcess.ModelExist

variable {Ω : Type*} {ι' ι'' : Type*} [Fintype ι'] [Fintype ι'']

/-- `Σ_x w_x (A_x − A_x^σ)`. -/
def tRep (σ : Ω → WithTop ℝ≥0) (w : ι' → Ω → ℂ) (A : ι' → ℝ≥0 → Ω → ℂ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  ∑ x, w x ω * (A x t ω - stoppedProcess (A x) σ t ω)

theorem tRep_zero (σ : Ω → WithTop ℝ≥0) (w : ι' → Ω → ℂ) (A : ι' → ℝ≥0 → Ω → ℂ) (ω : Ω) :
    tRep σ w A 0 ω = 0 := by
  have h0 : ∀ r : WithTop ℝ≥0, stopTime r 0 = 0 := fun r => le_antisymm (stopTime_le _ 0) zero_le
  simp [tRep, stoppedProcess_eq_stopTime, h0]

theorem star_tRep (σ : Ω → WithTop ℝ≥0) (w : ι' → Ω → ℂ) (A : ι' → ℝ≥0 → Ω → ℂ) (t : ℝ≥0)
    (ω : Ω) : star (tRep σ w A t ω) =
      tRep σ (fun x ω => star (w x ω)) (fun x t ω => star (A x t ω)) t ω := by
  simp only [tRep, star_sum, star_mul', star_sub, stoppedProcess_eq_stopTime]

variable [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- **Weighted increments of drift-free complex `LocMart`s are drift-free.** -/
theorem cLocMart_tRep {A : ι' → ℝ≥0 → Ω → ℂ} (hA : ∀ x, CLocMart Q 𝓖 (A x) (fun _ _ => 0))
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓖 σ) {w : ι' → Ω → ℂ}
    (hw : ∀ x, StronglyMeasurable[hσ.measurableSpace] (w x)) :
    CLocMart Q 𝓖 (tRep σ w A) (fun _ _ => 0) := by
  have h2 := CLocMart.sum univ fun x _ => (hA x).shift hσ (hw x)
  convert h2 using 1
  · rfl
  · funext s ω
    simp only [mul_zero, ite_self, Finset.sum_const_zero]

/-- **Products of weighted increments.** -/
theorem cLocMart_tRep_mul {A : ι' → ℝ≥0 → Ω → ℂ} {B : ι'' → ℝ≥0 → Ω → ℂ}
    {Γ : ι' → ι'' → ℝ≥0 → Ω → ℂ} (hA : ∀ x, CLocMart Q 𝓖 (A x) (fun _ _ => 0))
    (hB : ∀ y, CLocMart Q 𝓖 (B y) (fun _ _ => 0))
    (hAB : ∀ x y, CLocMart Q 𝓖 (fun t ω => A x t ω * B y t ω) (Γ x y))
    {σ₁ σ₂ : Ω → WithTop ℝ≥0} (hσ₁ : IsStoppingTime 𝓖 σ₁) (hσ₂ : IsStoppingTime 𝓖 σ₂)
    {w₁ : ι' → Ω → ℂ} {w₂ : ι'' → Ω → ℂ}
    (hw₁ : ∀ x, StronglyMeasurable[hσ₁.measurableSpace] (w₁ x))
    (hw₂ : ∀ y, StronglyMeasurable[hσ₂.measurableSpace] (w₂ y)) :
    CLocMart Q 𝓖 (fun t ω => tRep σ₁ w₁ A t ω * tRep σ₂ w₂ B t ω)
      (fun s ω => ∑ x, ∑ y, if max (σ₁ ω) (σ₂ ω) < (s : WithTop ℝ≥0) then
        w₁ x ω * w₂ y ω * Γ x y s ω else 0) := by
  have hρ := hσ₁.max hσ₂
  have h := fun x y => by
    have hw : StronglyMeasurable[hρ.measurableSpace] (fun ω => w₁ x ω * w₂ y ω) :=
      ((hw₁ x).mono (hσ₁.measurableSpace_mono hρ fun ω => le_max_left _ _)).mul
      ((hw₂ y).mono (hσ₂.measurableSpace_mono hρ fun ω => le_max_right _ _))
    exact ((hA x).pair (hB y) (hAB x y) hσ₁ hσ₂).weight hρ (stopped_pair_zero _ _ _ _) hw
  have h2 := CLocMart.sum univ fun x _ => CLocMart.sum univ fun y _ => h x y
  convert h2 using 1
  · funext t ω
    simp only [tRep, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  · funext s ω
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> rfl

end BlockBand.SourceProcess.ComplexConstruct
