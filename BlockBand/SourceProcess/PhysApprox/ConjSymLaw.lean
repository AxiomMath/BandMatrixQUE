module

public import BlockBand.Transmission.Bridge.Marginal

/-!
# The growth path law is invariant under entrywise conjugation

Used for the output leakage from the input leakage (`TargetT4`).

* `matConj M = M.map conj` (entrywise complex conjugation).
* `ginibreMeasure_map_matConj`: `Gin(t)` is invariant under `matConj` (the imaginary parts are
  centred Gaussians, invariant under `x ↦ -x`).
* `gueMeasure_map_matConj`: `GUE(t)` is invariant under `matConj`
  (`conj ∘ gueSample = gueSample ∘ conj`, and the circular entries are conjugation invariant).
* `conjPath`: entrywise conjugation of every block and bond of the growth sample;
  `measurePreserving_conjPath` and `lintegral_conjPath`: `growthPathLaw W b` is invariant.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Bridge
open scoped ENNReal NNReal ComplexConjugate

/-- Entrywise complex conjugation of a matrix. -/
def matConj {ι κ : Type*} (M : Matrix ι κ ℂ) : Matrix ι κ ℂ := M.map (starRingEnd ℂ)

theorem matConj_apply {ι κ : Type*} (M : Matrix ι κ ℂ) (i : ι) (j : κ) :
    matConj M i j = conj (M i j) := rfl

theorem matConj_matConj {ι κ : Type*} (M : Matrix ι κ ℂ) : matConj (matConj M) = M := by
  ext i j
  simp [matConj_apply]

theorem measurable_matConj {ι κ : Type*} :
    Measurable (matConj : Matrix ι κ ℂ → Matrix ι κ ℂ) := by
  apply Measurable.of_eval_matrix
  intro x y
  simp only [matConj, Matrix.map_apply]
  exact Complex.continuous_conj.measurable.comp Matrix.measurable_apply

/-- Negate the imaginary coordinate (index `1 : Fin 2`). -/
def negIm {α : Type*} (f : α → Fin 2) (p : α) (x : ℝ) : ℝ := if f p = 0 then x else -x

theorem measurable_negIm {α : Type*} (f : α → Fin 2) (p : α) : Measurable (negIm f p) := by
  unfold negIm
  by_cases h : f p = 0
  · simp only [h, ite_true]; exact measurable_id
  · simp only [h, ite_false]; exact measurable_neg

theorem gaussianReal_map_negIm {α : Type*} (f : α → Fin 2) (p : α) (v : ℝ≥0) :
    (gaussianReal 0 v).map (negIm f p) = gaussianReal 0 v := by
  unfold negIm
  by_cases h : f p = 0
  · simp only [h, ite_true]; exact Measure.map_id
  · simp only [h, ite_false]; rw [gaussianReal_map_neg, neg_zero]

theorem pi_map_negIm {α : Type*} [Fintype α] (f : α → Fin 2) (v : ℝ≥0) :
    (Measure.pi fun _ : α => gaussianReal 0 v).map (fun r p => negIm f p (r p)) =
      Measure.pi fun _ : α => gaussianReal 0 v := by
  rw [Measure.pi_map_pi (fun p => (measurable_negIm f p).aemeasurable)]
  simp only [gaussianReal_map_negIm]

theorem measurable_negIm_pi {α : Type*} [Fintype α] (f : α → Fin 2) :
    Measurable fun (r : α → ℝ) (p : α) => negIm f p (r p) :=
  Measurable.of_eval fun p => (measurable_negIm f p).comp (measurable_pi_apply p)

/-- **`Gin(t)` is invariant under entrywise conjugation.** -/
theorem ginibreMeasure_map_matConj (ι κ : Type*) [Fintype ι] [Fintype κ] (t : ℝ≥0) :
    (ginibreMeasure ι κ t).map matConj = ginibreMeasure ι κ t := by
  have hconj : matConj ∘ ginibreSample ι κ =
      ginibreSample ι κ ∘ (fun r p => negIm (fun p : ι × κ × Fin 2 => p.2.2) p (r p)) := by
    funext r
    ext x y
    have h1 : (1 : Fin 2) ≠ 0 := by decide
    simp [matConj, ginibreSample, negIm, h1]
  rw [ginibreMeasure_eq, Measure.map_map measurable_matConj (measurable_ginibreSample ι κ), hconj,
    ← Measure.map_map (measurable_ginibreSample ι κ) (measurable_negIm_pi _), pi_map_negIm]

/-- Entrywise conjugation of a flat complex vector. -/
def vecConj {α : Type*} (X : α → ℂ) : α → ℂ := fun u => conj (X u)

theorem measurable_vecConj {α : Type*} : Measurable (vecConj : (α → ℂ) → α → ℂ) :=
  Measurable.of_eval fun u => Complex.continuous_conj.measurable.comp (measurable_pi_apply u)

/-- The circular increment law is invariant under entrywise conjugation. -/
theorem commonCircularIncrementLaw_map_vecConj (ι : Type*) [Fintype ι] (δ : ℝ≥0) :
    (BlockBand.SourceProcess.commonCircularIncrementLaw ι δ).map vecConj =
      BlockBand.SourceProcess.commonCircularIncrementLaw ι δ := by
  have hconj : vecConj ∘ BlockBand.SourceProcess.circularBrownianCoordinates (ι := ι) =
      BlockBand.SourceProcess.circularBrownianCoordinates ∘
        (fun r p => negIm (fun p : (ι × ι) × Fin 2 => p.2) p (r p)) := by
    funext r
    ext u
    have h1 : (1 : Fin 2) ≠ 0 := by decide
    simp [vecConj, BlockBand.SourceProcess.circularBrownianCoordinates, negIm, h1]
  unfold BlockBand.SourceProcess.commonCircularIncrementLaw
  rw [Measure.map_map measurable_vecConj measurable_circularBrownianCoordinates, hconj,
    ← Measure.map_map measurable_circularBrownianCoordinates (measurable_negIm_pi _),
    pi_map_negIm]

/-- **`GUE(t)` is invariant under entrywise conjugation.** -/
theorem gueMeasure_map_matConj (ι : Type*) [Fintype ι] (t : ℝ≥0) :
    (gueMeasure ι t).map matConj = gueMeasure ι t := by
  have hconj : matConj ∘ gueSample (ι := ι) t = gueSample t ∘ vecConj := by
    funext X
    ext a c
    simp [matConj, gueSample, vecConj]
  rw [gueMeasure, Measure.map_map measurable_matConj (measurable_gueSample t), hconj,
    ← Measure.map_map (measurable_gueSample t) measurable_vecConj,
    commonCircularIncrementLaw_map_vecConj]

variable {W : ℕ}

/-- Entrywise conjugation of every GUE block and every Ginibre bond of the growth sample. -/
def conjPath (ω : GrowthPath W) : GrowthPath W :=
  (fun k => matConj (ω.1 k), fun k => matConj (ω.2 k))

theorem conjPath_involutive : Function.Involutive (conjPath (W := W)) := by
  intro ω
  simp only [conjPath, matConj_matConj]

theorem measurable_conjPath : Measurable (conjPath (W := W)) := by
  unfold conjPath
  refine Measurable.prodMk ?_ ?_
  · exact Measurable.of_eval fun k =>
      measurable_matConj.comp ((measurable_pi_apply k).comp measurable_fst)
  · exact Measurable.of_eval fun k =>
      measurable_matConj.comp ((measurable_pi_apply k).comp measurable_snd)

/-- `conjPath` as a measurable involution. -/
def conjPathEquiv (W : ℕ) : GrowthPath W ≃ᵐ GrowthPath W :=
  MeasurableEquiv.ofInvolutive conjPath conjPath_involutive measurable_conjPath

/-- **The growth path law is invariant under entrywise conjugation.** -/
theorem growthPathLaw_map_conjPath (b : ℝ) :
    (growthPathLaw W b).map conjPath = growthPathLaw W b := by
  have hc : (conjPath : GrowthPath W → GrowthPath W) =
      Prod.map (fun (a : ℕ → Matrix (Fin W) (Fin W) ℂ) k => matConj (a k))
        (fun (a : ℕ → Matrix (Fin W) (Fin W) ℂ) k => matConj (a k)) := rfl
  have hm : Measurable fun (a : ℕ → Matrix (Fin W) (Fin W) ℂ) k => matConj (a k) :=
    Measurable.of_eval fun k => measurable_matConj.comp (measurable_pi_apply k)
  rw [hc, growthPathLaw, ← Measure.map_prod_map _ _ hm hm,
    Measure.infinitePi_map_pi (fun _ : ℕ => gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W)))
      (fun _ => measurable_matConj),
    Measure.infinitePi_map_pi
      (fun _ : ℕ => ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)))
      (fun _ => measurable_matConj)]
  simp only [gueMeasure_map_matConj, ginibreMeasure_map_matConj]

theorem measurePreserving_conjPath (b : ℝ) :
    MeasurePreserving (conjPath (W := W)) (growthPathLaw W b) (growthPathLaw W b) :=
  ⟨measurable_conjPath, growthPathLaw_map_conjPath b⟩

/-- `∫⁻ F(ω̄) = ∫⁻ F(ω)` under the growth path law (no measurability of `F` needed). -/
theorem lintegral_conjPath (b : ℝ) (F : GrowthPath W → ℝ≥0∞) :
    ∫⁻ ω, F (conjPath ω) ∂growthPathLaw W b = ∫⁻ ω, F ω ∂growthPathLaw W b :=
  (measurePreserving_conjPath b).lintegral_comp_emb (conjPathEquiv W).measurableEmbedding F

end BlockBand.SourceProcess.PhysApprox
