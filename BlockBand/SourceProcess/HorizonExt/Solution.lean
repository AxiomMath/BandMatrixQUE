module

public import BlockBand.SourceProcess.HorizonExt.GlueBr

/-!
# The glued process is a global Gram martingale-problem solution

**`isGramMartingaleSolution_glue`**: let `G` be a horizon solution on `(Ω, 𝓖, Q)` up to `r`, and
`Y` a global solution on `(Ω × W, 𝓕, Q ⊗ ν)` with `fst⁻¹ m ≤ 𝓕₀` and `Y₀ = G_r ∘ fst` a.s.
Then `glueProc r G Y` is an `IsGramMartingaleSolution` for `glueFil 𝓖 𝓕 r`. Its laws at the
times `t ≤ r` are those of `G` (`map_glueProc_of_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.HorizonExt

open MeasureTheory ProbabilityTheory Filter Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.BornStopped
open scoped NNReal

variable {c : Type} [Fintype c] [DecidableEq c]
variable {Ω W : Type} {m : MeasurableSpace Ω} [MeasurableSpace W] {Q : Measure Ω}
  {ν : Measure W} [IsProbabilityMeasure Q] [IsProbabilityMeasure ν]
variable {𝓖 : Filtration ℝ≥0 m} {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × W))}
  {D0 : ℝ} {D : Matrix c c ℂ} {r : ℝ≥0}
  {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} {Y : ℝ≥0 → Ω × W → Matrix c c ℂ × Matrix c c ℂ}

omit [Fintype c] [DecidableEq c] [MeasurableSpace W] in
theorem glueProc_of_le {t : ℝ≥0} (ht : t ≤ r) :
    glueProc (W := W) r G Y t = fun x => G t x.1 :=
  funext fun _ => glue_of_le ht

omit [Fintype c] [DecidableEq c] [MeasurableSpace W] in
theorem glueProc_of_lt {t : ℝ≥0} (ht : r < t) :
    glueProc (W := W) r G Y t = Y (t - r) :=
  funext fun _ => glue_of_lt ht

/-- **The glued process solves the Gram martingale problem.** -/
theorem isGramMartingaleSolution_glue (h𝓕 : m.comap Prod.fst ≤ 𝓕 0)
    (hG : IsGramHorizonSolution Q 𝓖 D0 D r G)
    (hY : IsGramMartingaleSolution (Q.prod ν) 𝓕 D0 D Y)
    (h0 : ∀ᵐ x ∂(Q.prod ν), Y 0 x = G r x.1) :
    IsGramMartingaleSolution (Q.prod ν) (glueFil 𝓖 𝓕 h𝓕 r) D0 D (glueProc r G Y) := by
  refine ⟨fun t => ?_, ?_, ?_, glue_drift h𝓕 hG hY h0, glue_bracket h𝓕 hG hY h0⟩
  · by_cases ht : t ≤ r
    · rw [glueProc_of_le ht]
      exact ((hG.adapted t).comp_measurable (comap_measurable Prod.fst)).mono
        (comap_le_glueFil t)
    · rw [glueProc_of_lt (not_le.1 ht), glueFil_of_le (not_le.1 ht).le]
      exact hY.adapted (t - r)
  · filter_upwards [ae_good hG hY h0] with x hx
    exact continuous_glue hx.1 hx.2.2.1 hx.2.2.2.2
  · filter_upwards [ae_good hG hY h0] with x hx t
    by_cases ht : t ≤ r
    · simp only [glueProc, glue_of_le ht]
      exact hx.2.1 t ht
    · simp only [glueProc, glue_of_lt (not_le.1 ht)]
      exact hx.2.2.2.1 _

omit [DecidableEq c] [IsProbabilityMeasure Q] in
/-- **Laws of the glued process up to `r`.** -/
theorem map_glueProc_of_le (hG : ∀ t, StronglyMeasurable[𝓖 t] (G t)) {t : ℝ≥0} (ht : t ≤ r) :
    (Q.prod ν).map (glueProc r G Y t) = Q.map (G t) := by
  have hm := SourceProcessLaw.measurable_of_stronglyMeasurable_gram (𝓖.le t) (hG t)
  rw [glueProc_of_le ht, show (fun x : Ω × W => G t x.1) = G t ∘ Prod.fst from rfl,
    ← Measure.map_map hm measurable_fst, (measurePreserving_fst (μ := Q) (ν := ν)).map_eq]

end BlockBand.SourceProcess.HorizonExt
