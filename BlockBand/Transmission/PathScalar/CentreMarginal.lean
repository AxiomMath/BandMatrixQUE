module

public import BlockBand.Transmission.PathScalar.CentreLaw

/-!
# Centre growth: proof of `CentreGrowthMarginal` and the unconditional superexponential bound

This proves the hypothesis `CentreGrowthMarginal`, along the two-ended recursion of the
centre-grown path.

`assemble L : GrowthSample W r₀ L → PathSample W (r₀ + 2L)` assembles the centre-grown path
(`assemble (L+1) ω = newPath (assemble L (trunc ω)) (last layer)`). Then, for `r₀ ≥ 1`:
* `assemble_law`: `assemble L` maps `growthLaw W r₀ L b` to `pathLaw W (r₀+2L) b`
  (induction with `newPath_law` and `trunc_last_law`);
* `ae_grownSchur_eq`: for `b < 1/2`, `W ≥ 1`, almost surely
  `grownSchur E ω L = pathSchur E (assemble L ω)` (induction with `pathSchur_newPath`; the inner
  pencils are a.s. invertible by `ae_isUnit_pathPencil_pathLaw`);
* `centreGrowthMarginal_holds`: `CentreGrowthMarginal b E` for `b < 1/2`;

* `passiveInitialScalar_superexp_of_scalarRecursion`: the superexponential bound from
  `ScalarRecursionContract` alone.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge
open scoped ENNReal NNReal Matrix

variable {W : ℕ}

/-- The sample with the last layer removed, and the last layer. -/
def truncLast {r₀ L : ℕ} (ω : GrowthSample W r₀ (L + 1)) :
    GrowthSample W r₀ L × LayerSample W .separate :=
  ((ω.1, Fin.init ω.2), ω.2 (Fin.last L))

/-- The centre-grown path assembled as a path sample of length `r₀ + 2L`. -/
def assemble {r₀ : ℕ} : (L : ℕ) → GrowthSample W r₀ L → PathSample W (r₀ + 2 * L)
  | 0, ω => ω.1
  | L + 1, ω => newPath (assemble L (truncLast ω).1) (truncLast ω).2

/-- The `Bridge` instance, restated at the shape `.separate` (instance search does not unify the
generic statement with the reduced measurable-space instance of `LayerSample W .separate`). -/
instance isProbabilityMeasure_layerLaw_separate (b : ℝ) :
    IsProbabilityMeasure (layerLaw W b .separate) :=
  isProbabilityMeasure_layerLaw W b _

instance isProbabilityMeasure_growthLaw (b : ℝ) (r₀ L : ℕ) :
    IsProbabilityMeasure (growthLaw W r₀ L b) := by
  unfold growthLaw; infer_instance

theorem trunc_last_law (b : ℝ) (r₀ L : ℕ) :
    MeasurePreserving (truncLast (W := W) (r₀ := r₀) (L := L)) (growthLaw W r₀ (L + 1) b)
      ((growthLaw W r₀ L b).prod (layerLaw W b .separate)) := by
  have h1 := (MeasurePreserving.id (pathLaw W r₀ b)).prod
    (measurePreserving_piFinSuccAbove (fun _ : Fin (L + 1) => layerLaw W b .separate) (Fin.last L))
  have h2 := (MeasurePreserving.id (pathLaw W r₀ b)).prod
    (Measure.measurePreserving_swap (μ := layerLaw W b .separate)
      (ν := Measure.pi fun _ : Fin L => layerLaw W b .separate))
  have h3 := (measurePreserving_prodAssoc (pathLaw W r₀ b)
    (Measure.pi fun _ : Fin L => layerLaw W b .separate) (layerLaw W b .separate)).symm
  have h := (h3.comp h2).comp h1
  have hfun : truncLast (W := W) (r₀ := r₀) (L := L) = fun ω =>
      ((ω.1, fun j : Fin L => ω.2 ((Fin.last L).succAbove j)), ω.2 (Fin.last L)) := by
    funext ω
    simp only [truncLast, Fin.succAbove_last]
    rfl
  rw [hfun]
  exact h

theorem assemble_law (b : ℝ) {r₀ : ℕ} (hr₀ : 1 ≤ r₀) :
    ∀ L : ℕ, MeasurePreserving (assemble (W := W) (r₀ := r₀) L) (growthLaw W r₀ L b)
      (pathLaw W (r₀ + 2 * L) b)
  | 0 => measurePreserving_fst (μ := pathLaw W r₀ b)
      (ν := Measure.pi fun _ : Fin 0 => layerLaw W b .separate)
  | L + 1 => by
    have h := ((newPath_law (W := W) b (r := r₀ + 2 * L) (by omega)).comp
      ((assemble_law b hr₀ L).prod (MeasurePreserving.id (layerLaw W b .separate)))).comp
      (trunc_last_law b r₀ L)
    exact h

/-- The truncation `ω ↦ ω` without its last layer preserves the growth laws. -/
theorem trunc_law (b : ℝ) (r₀ L : ℕ) :
    MeasurePreserving (fun ω : GrowthSample W r₀ (L + 1) => (truncLast ω).1)
      (growthLaw W r₀ (L + 1) b) (growthLaw W r₀ L b) :=
  (measurePreserving_fst (μ := growthLaw W r₀ L b) (ν := layerLaw W b .separate)).comp
    (trunc_last_law b r₀ L)

theorem grownSchur_truncLast (E : ℝ) {r₀ L : ℕ} (ω : GrowthSample W r₀ (L + 1)) :
    ∀ k ≤ L, grownSchur E ω k = grownSchur E (truncLast ω).1 k
  | 0, _ => rfl
  | k + 1, hk => by
    have h1 : k < L + 1 := by omega
    have h2 : k < L := by omega
    simp only [grownSchur, h1, h2, dite_true]
    rw [grownSchur_truncLast E ω k (by omega)]
    rfl

theorem grownSchur_succ_last (E : ℝ) {r₀ L : ℕ} (ω : GrowthSample W r₀ (L + 1)) :
    grownSchur E ω (L + 1) =
      layerSchur .separate E (grownSchur E (truncLast ω).1 L) (truncLast ω).2 := by
  have h1 : L < L + 1 := by omega
  simp only [grownSchur, h1, dite_true]
  rw [grownSchur_truncLast E ω L le_rfl]
  rfl

/-- **The centre-grown Schur matrix is the path Schur matrix** almost surely (`b < 1/2`,
`W ≥ 1`, `r₀ ≥ 1`). -/
theorem ae_grownSchur_eq {b : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) {r₀ : ℕ} (hr₀ : 1 ≤ r₀) :
    ∀ L : ℕ, ∀ᵐ ω ∂growthLaw W r₀ L b, grownSchur E ω L = pathSchur E (assemble L ω)
  | 0 => Filter.Eventually.of_forall fun _ => rfl
  | L + 1 => by
    have hT := trunc_law (W := W) b r₀ L
    have hIH : ∀ᵐ ω ∂growthLaw W r₀ (L + 1) b,
        grownSchur E (truncLast ω).1 L = pathSchur E (assemble L (truncLast ω).1) := by
      have := ae_grownSchur_eq hb hW E hr₀ L
      rw [← hT.map_eq] at this
      exact ae_of_ae_map hT.measurable.aemeasurable this
    have hU : ∀ᵐ ω ∂growthLaw W r₀ (L + 1) b,
        IsUnit (pathMatrix (assemble L (truncLast ω).1) - (E : ℂ) • 1) := by
      have hA := (assemble_law (W := W) b hr₀ L).comp hT
      have := ae_isUnit_pathPencil_pathLaw (W := W) hb hW E (r₀ + 2 * L)
      rw [← hA.map_eq] at this
      exact ae_of_ae_map hA.measurable.aemeasurable this
    filter_upwards [hIH, hU] with ω h1 h2
    rw [grownSchur_succ_last, h1]
    exact (pathSchur_newPath E (by omega) _ _ h2).symm

/-- **`CentreGrowthMarginal` holds** for `b < 1/2` (every `E`). -/
theorem centreGrowthMarginal_holds {b : ℝ} (hb : b < 1 / 2) (E : ℝ) : CentreGrowthMarginal b E := by
  intro W hW r₀ hr₀ L
  have hr : 1 ≤ r₀ := by rcases hr₀ with rfl | rfl <;> omega
  rw [Measure.map_congr (ae_grownSchur_eq hb hW E hr L), ← (assemble_law b hr L).map_eq,
    Measure.map_map (measurable_pathSchur E _) (assemble_law b hr L).measurable]
  rfl

/-- **The superexponential bound, unconditional on the centre-growth identity**: from
`ScalarRecursionContract` alone, `P(∃ r ≤ TW, δ_{0,r} > d) ≤ ⌊TW⌋₊ exp(-cW log W)`. -/
theorem passiveInitialScalar_superexp_of_scalarRecursion (hSR : ScalarRecursionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
      ∀ d : ℝ, 0 < d → ∃ (c : ℝ) (W₀ : ℕ), 0 < c ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
        growthPathLaw W b {ω | ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ T * W ∧
          d < jetDistance0 b E (pathX b E W r ω)} ≤
          ENNReal.ofReal ((⌊T * W⌋₊ : ℝ) * Real.exp (-(c * W * Real.log W))) :=
  fun b hb hb' κ T hκ =>
    passiveInitialScalar_superexp hSR b hb hb' κ T hκ fun E _ => centreGrowthMarginal_holds hb' E

end BlockBand.Transmission.PathScalar
