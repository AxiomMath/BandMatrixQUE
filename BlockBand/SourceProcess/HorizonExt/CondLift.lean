module

public import BlockBand.SourceProcess.BornStopped.Piece

/-!
# Martingales on a product space, and gluing at a deterministic time

On `Ω × W` with `Q ⊗ ν` (`ν` a probability measure):
* `condExp_comp_fst`: `E[f ∘ fst | fst⁻¹ 𝓜] = E[f | 𝓜] ∘ fst`.
* `glueFil 𝓖 𝓕 r`: the filtration `fst⁻¹ 𝓖_t` for `t < r` and `𝓕_{t - r}` for `t ≥ r`; it is a
  filtration when `fst⁻¹ m ≤ 𝓕₀`.
* `martingale_lift_min`: a `𝓖`-martingale `N` gives the `glueFil`-martingale `N(t ∧ r) ∘ fst`.
* `martingale_shift`: an `𝓕`-martingale `Y` with `Y₀ = 0` a.s. gives the `glueFil`-martingale
  `1{r ≤ t} Y(t - r)` (tower property at `r`, `fst⁻¹ 𝓖_s ≤ 𝓕₀`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.HorizonExt

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

variable {Ω W : Type*} {m : MeasurableSpace Ω} [MeasurableSpace W] {Q : Measure Ω}
  {ν : Measure W} [IsProbabilityMeasure Q] [IsProbabilityMeasure ν]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem setIntegral_fst (S : Set Ω) (g : Ω → E) :
    ∫ x in Prod.fst ⁻¹' S, g x.1 ∂(Q.prod ν) = ∫ y in S, g y ∂Q := by
  rw [← Set.prod_univ, ← Measure.prod_restrict, Measure.restrict_univ, integral_fun_fst,
    probReal_univ, one_smul]

theorem condExp_comp_fst (𝓖 : Filtration ℝ≥0 m) (s : ℝ≥0) {f : Ω → E} (hf : Integrable f Q) :
    (Q.prod ν)[fun x => f x.1 | (𝓖 s).comap Prod.fst] =ᵐ[Q.prod ν] fun x => (Q[f | 𝓖 s]) x.1 := by
  have hmp : MeasurePreserving Prod.fst (Q.prod ν) Q := measurePreserving_fst
  have hle : (𝓖 s).comap Prod.fst ≤ (Prod.instMeasurableSpace : MeasurableSpace (Ω × W)) :=
    (MeasurableSpace.comap_mono (𝓖.le s)).trans measurable_fst.comap_le
  have hmeas : Measurable[(𝓖 s).comap Prod.fst, 𝓖 s] (Prod.fst : Ω × W → Ω) :=
    comap_measurable _
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle (hmp.integrable_comp_of_integrable hf)
    (fun s _ _ => (hmp.integrable_comp_of_integrable integrable_condExp).integrableOn) ?_
    (stronglyMeasurable_condExp.comp_measurable hmeas).aestronglyMeasurable).symm
  rintro _ ⟨S, hS, rfl⟩ -
  show ∫ x in _, (Q[f | 𝓖 s]) x.1 ∂(Q.prod ν) = ∫ x in _, f x.1 ∂(Q.prod ν)
  rw [setIntegral_fst, setIntegral_fst, setIntegral_condExp (𝓖.le s) hf hS]

/-- The glued filtration: `fst⁻¹ 𝓖_t` before `r`, `𝓕_{t-r}` from `r` on. -/
def glueFil (𝓖 : Filtration ℝ≥0 m) (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × W)))
    (h : m.comap Prod.fst ≤ 𝓕 0) (r : ℝ≥0) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × W)) where
  seq t := if t < r then (𝓖 t).comap Prod.fst else 𝓕 (t - r)
  mono' s t hst := by
    by_cases ht : t < r
    · have hs : s < r := lt_of_le_of_lt hst ht
      simp only [hs, ht, ↓reduceIte]
      exact MeasurableSpace.comap_mono (𝓖.mono hst)
    · by_cases hs : s < r
      · simp only [hs, ht, ↓reduceIte, ↓reduceIte]
        exact (MeasurableSpace.comap_mono (𝓖.le s)).trans (h.trans (𝓕.mono zero_le))
      · simp only [hs, ht, ↓reduceIte]
        exact 𝓕.mono (tsub_le_tsub_right hst r)
  le' t := by
    split_ifs
    · exact (MeasurableSpace.comap_mono (𝓖.le t)).trans measurable_fst.comap_le
    · exact 𝓕.le _

variable {𝓖 : Filtration ℝ≥0 m} {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × W))}
  {h : m.comap Prod.fst ≤ 𝓕 0} {r : ℝ≥0}

theorem glueFil_of_lt {t : ℝ≥0} (ht : t < r) : glueFil 𝓖 𝓕 h r t = (𝓖 t).comap Prod.fst := by
  simp only [glueFil, ht, ↓reduceIte]

theorem glueFil_of_le {t : ℝ≥0} (ht : r ≤ t) : glueFil 𝓖 𝓕 h r t = 𝓕 (t - r) := by
  simp only [glueFil, not_lt.2 ht, ↓reduceIte]

theorem comap_le_glueFil (t : ℝ≥0) : (𝓖 t).comap Prod.fst ≤ glueFil 𝓖 𝓕 h r t := by
  by_cases ht : t < r
  · rw [glueFil_of_lt ht]
  · rw [glueFil_of_le (not_lt.1 ht)]
    exact (MeasurableSpace.comap_mono (𝓖.le t)).trans (h.trans (𝓕.mono zero_le))

/-- **Lift of a martingale stopped at the deterministic time `r`.** -/
theorem martingale_lift_min {N : ℝ≥0 → Ω → E} (hN : Martingale N 𝓖 Q) :
    Martingale (fun t (x : Ω × W) => N (min t r) x.1) (glueFil 𝓖 𝓕 h r) (Q.prod ν) := by
  have hNr := BornStopped.martingale_min hN r
  have hmp : MeasurePreserving Prod.fst (Q.prod ν) Q := measurePreserving_fst
  have had : ∀ t, StronglyMeasurable[glueFil 𝓖 𝓕 h r t] fun x : Ω × W => N (min t r) x.1 :=
    fun t => ((hNr.1 t).comp_measurable (comap_measurable Prod.fst)).mono (comap_le_glueFil t)
  refine ⟨had, fun s t hst => ?_⟩
  by_cases hs : s < r
  · rw [glueFil_of_lt hs]
    refine (condExp_comp_fst 𝓖 s (hNr.integrable t)).trans ?_
    exact hmp.quasiMeasurePreserving.ae_eq_comp (hNr.2 s t hst)
  · have h1 : min t r = r := min_eq_right ((not_lt.1 hs).trans hst)
    have h2 : min s r = r := min_eq_right (not_lt.1 hs)
    have hint : Integrable (fun x : Ω × W => N (min t r) x.1) (Q.prod ν) :=
      hmp.integrable_comp_of_integrable (hNr.integrable t)
    show (Q.prod ν)[fun x => N (min t r) x.1 | _] =ᵐ[_] fun x => N (min s r) x.1
    have e : (fun x : Ω × W => N (min t r) x.1) = fun x => N (min s r) x.1 := by rw [h1, h2]
    rw [e] at hint ⊢
    exact Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable ((glueFil 𝓖 𝓕 h r).le s)
      (had s) hint)

/-- **A martingale started at `r`.** -/
theorem martingale_shift {Y : ℝ≥0 → Ω × W → E} (hY : Martingale Y 𝓕 (Q.prod ν))
    (hY0 : Y 0 =ᵐ[Q.prod ν] 0) :
    Martingale (fun t => if r ≤ t then Y (t - r) else 0) (glueFil 𝓖 𝓕 h r) (Q.prod ν) := by
  refine ⟨fun t => ?_, fun s t hst => ?_⟩
  · by_cases ht : r ≤ t
    · simp only [ht, ↓reduceIte]
      rw [glueFil_of_le ht]
      exact hY.1 (t - r)
    · simp only [ht, ↓reduceIte]
      exact stronglyMeasurable_zero
  by_cases ht : r ≤ t
  · simp only [ht, ↓reduceIte]
    by_cases hs : r ≤ s
    · simp only [hs, ↓reduceIte]
      rw [glueFil_of_le hs]
      exact hY.2 (s - r) (t - r) (tsub_le_tsub_right hst r)
    · simp only [hs, ↓reduceIte]
      have hs' : s < r := not_le.1 hs
      have hle : glueFil 𝓖 𝓕 h r s ≤ 𝓕 0 := by
        rw [glueFil_of_lt hs']
        exact (MeasurableSpace.comap_mono (𝓖.le s)).trans h
      refine (condExp_condExp_of_le hle (𝓕.le 0)).symm.trans ?_
      refine (condExp_congr_ae ((hY.2 0 (t - r) zero_le).trans hY0)).trans ?_
      rw [condExp_zero]
  · have hs : ¬ r ≤ s := fun hs => ht (hs.trans hst)
    simp only [ht, hs, ↓reduceIte, condExp_zero]
    rfl

end BlockBand.SourceProcess.HorizonExt
