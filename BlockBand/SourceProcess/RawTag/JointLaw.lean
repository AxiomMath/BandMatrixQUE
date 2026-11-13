module

public import BlockBand.SourceProcess.RawTag.Defs

/-!
# The joint law of the past, the tag Gaussians and the fresh layer

Bookkeeping for the conditional (Fubini) form of the raw-moment transport. The sample space is
`GrowthPath W × Γ`, where `Γ` carries the tag Gaussians, with law `growthPathLaw W b ⊗ ν`. At
step `l → l+1`:
* every length-`l` object is unchanged when the growth sample is replaced by
  `extendPast (pastCoords W l ω)` (`fullInverse_extendPast`, `pathX_extendPast`);
* `((pastCoords W l ω, γ), freshSample W l ω)` has law `(pastLaw ⊗ ν) ⊗ freshLaw`
  (`map_past_tag_fresh`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped Matrix ENNReal

variable {W : ℕ}

theorem measurable_extendPast (j : ℕ) : Measurable (extendPast (W := W) (j := j)) := by
  refine Measurable.prodMk (measurable_pi_iff.mpr fun k => ?_) (measurable_pi_iff.mpr fun k => ?_)
  · by_cases h : k < j
    · simp only [h, ↓reduceDIte]
      exact (measurable_pi_apply _).comp measurable_fst
    · simp only [h, ↓reduceDIte]; exact measurable_const
  · by_cases h : k < j + 1
    · simp only [h, ↓reduceDIte]
      exact (measurable_pi_apply _).comp measurable_snd
    · simp only [h, ↓reduceDIte]; exact measurable_const

/-- The past extended by zeros. -/
abbrev pastExt (W l : ℕ) (ω : GrowthPath W) : GrowthPath W := extendPast (pastCoords W l ω)

theorem pathAt_extendPast (l : ℕ) (ω : GrowthPath W) :
    pathAt W l (pastExt W l ω) = pathAt W l ω := by
  rw [pathAt_eq_pathOfPast, Function.comp_apply, pastCoords_extendPast]
  rfl

theorem fullInverse_extendPast (b E : ℝ) (l : ℕ) (ω : GrowthPath W) :
    fullInverse b E W l (pastExt W l ω) = fullInverse b E W l ω := by
  rw [fullInverse, fullPathMatrix, pathAt_extendPast]; rfl

theorem pathX_extendPast (b E : ℝ) (l : ℕ) (ω : GrowthPath W) :
    pathX b E W l (pastExt W l ω) = pathX b E W l ω := by
  rw [pathX_eq, pathX_eq, pathAt_extendPast]

theorem rawForm_extendPast (b E : ℝ) (l β₁ β₂ : ℕ) (ω : GrowthPath W) (g h : Fin W → ℂ) :
    rawForm b E W l β₁ β₂ (pastExt W l ω) g h = rawForm b E W l β₁ β₂ ω g h := by
  rw [rawForm, rawForm, fullInverse_extendPast]

theorem frame_extendPast (b E : ℝ) (l β : ℕ) (ω : GrowthPath W) (g : Fin W → ℂ) :
    frame b E W l β (pastExt W l ω) g = frame b E W l β ω g := by
  rw [frame, frame, boundaryToInterior, boundaryToInterior, fullInverse_extendPast]

theorem scatteringMatrix_extendPast (b E : ℝ) (l : ℕ) (ω : GrowthPath W) :
    scatteringMatrix b E W l (pastExt W l ω) = scatteringMatrix b E W l ω := by
  rw [scatteringMatrix, scatteringMatrix, boundaryResolvent, boundaryResolvent,
    fullInverse_extendPast]

theorem nearL_extendPast (b E : ℝ) (l β : ℕ) (ω : GrowthPath W) (g : Fin W → ℂ) :
    nearL b E W l β (pastExt W l ω) g = nearL b E W l β ω g := by
  rw [nearL, nearL, frame_extendPast]

theorem nearR_extendPast (b E : ℝ) (l β : ℕ) (ω : GrowthPath W) (g : Fin W → ℂ) :
    nearR b E W l β (pastExt W l ω) g = nearR b E W l β ω g := by
  rw [nearR, nearR, frame_extendPast, scatteringMatrix_extendPast]

/-! ## Measurability -/

theorem measurable_unitTag (l β : ℕ) : Measurable fun g : Fin W → ℂ => unitTag W l β g := by
  refine Measurable.of_eval fun y => ?_
  simp only [unitTag]
  split_ifs
  · exact measurable_const.mul (measurable_pi_apply _)
  · exact measurable_const

theorem measurable_rawForm {α : Type*} [MeasurableSpace α] (b E : ℝ) (l β₁ β₂ : ℕ)
    {ω : α → GrowthPath W} {g h : α → Fin W → ℂ} (hω : Measurable ω) (hg : Measurable g)
    (hh : Measurable h) : Measurable fun a => rawForm b E W l β₁ β₂ (ω a) (g a) (h a) := by
  have hG : Measurable fun a => (fullInverse b E W l (ω a)).toBlocks₁₁ :=
    Measurable.of_eval_matrix _ fun _ _ =>
      ((BlockBand.SourceProcess.FullSourceStops.measurable_fullInverse b E l).comp hω).eval_matrix
  have hu := (measurable_unitTag (W := W) l β₁).comp hg
  have hv := (measurable_unitTag (W := W) l β₂).comp hh
  simp only [rawForm, dotProduct, mulVec, Pi.star_apply]
  exact Finset.measurable_sum _ fun y _ =>
    (Complex.continuous_conj.measurable.comp ((measurable_pi_apply y).comp hu)).mul
      (Finset.measurable_sum _ fun z _ => hG.eval_matrix.mul ((measurable_pi_apply z).comp hv))

theorem measurable_mulVec' {α m n : Type*} [MeasurableSpace α] [Fintype n]
    {A : α → Matrix m n ℂ} {v : α → n → ℂ} (hA : Measurable A) (hv : Measurable v) :
    Measurable fun a => A a *ᵥ v a := by
  refine Measurable.of_eval fun i => ?_
  simp only [mulVec, dotProduct]
  exact Finset.measurable_sum _ fun j _ => hA.eval_matrix.mul ((measurable_pi_apply j).comp hv)

theorem measurable_frame {α : Type*} [MeasurableSpace α] (b E : ℝ) (l β : ℕ)
    {ω : α → GrowthPath W} {g : α → Fin W → ℂ} (hω : Measurable ω) (hg : Measurable g) :
    Measurable fun a => frame b E W l β (ω a) (g a) := by
  have hU : Measurable fun a => (boundaryToInterior b E W l (ω a))ᴴ :=
    Measurable.of_eval_matrix _ fun _ _ => (Complex.continuous_conj.measurable.comp
      ((BlockBand.SourceProcess.FullSourceStops.measurable_fullInverse b E l).comp hω).eval_matrix)
  exact measurable_mulVec' hU ((measurable_unitTag l β).comp hg)

theorem measurable_nearL {α : Type*} [MeasurableSpace α] (b E : ℝ) (l β : ℕ)
    {ω : α → GrowthPath W} {g : α → Fin W → ℂ} (hω : Measurable ω) (hg : Measurable g) :
    Measurable fun a => nearL b E W l β (ω a) (g a) :=
  measurable_mulVec' measurable_const (measurable_frame b E l β hω hg)

theorem measurable_nearR {α : Type*} [MeasurableSpace α] (b E : ℝ) (l β : ℕ)
    {ω : α → GrowthPath W} {g : α → Fin W → ℂ} (hω : Measurable ω) (hg : Measurable g) :
    Measurable fun a => nearR b E W l β (ω a) (g a) :=
  measurable_mulVec' measurable_const (measurable_mulVec'
    ((BlockBand.SourceProcess.FullSourceStops.measurable_scatteringMatrix b E l).comp hω)
    (measurable_frame b E l β hω hg))

/-! ## The joint law -/

theorem map_past_tag_fresh (W l : ℕ) (b : ℝ) {Γ : Type*} [MeasurableSpace Γ] (ν : Measure Γ)
    [IsProbabilityMeasure ν] :
    ((growthPathLaw W b).prod ν).map (fun w => ((pastCoords W l w.1, w.2), freshSample W l w.1)) =
      ((pastLaw W l b).prod ν).prod (freshLaw W b) := by
  have := isProbabilityMeasure_growthPathLaw W b
  have hPF : Measurable fun ω : GrowthPath W => (pastCoords W l ω, freshSample W l ω) :=
    (measurable_pastCoords W l).prodMk (measurable_freshSample W l)
  have h1 : ((pastLaw W l b).prod (freshLaw W b)).prod ν =
      ((growthPathLaw W b).prod ν).map (Prod.map (fun ω => (pastCoords W l ω,
        freshSample W l ω)) id) := by
    rw [← growthPathLaw_map_past_fresh, ← Measure.map_prod_map _ _ hPF measurable_id,
      Measure.map_id]
  have hsh : MeasurePreserving (fun z : (PastSample W l × LayerSample W .oneBlockOnePort) × Γ =>
      ((z.1.1, z.2), z.1.2)) (((pastLaw W l b).prod (freshLaw W b)).prod ν)
      (((pastLaw W l b).prod ν).prod (freshLaw W b)) := by
    have h1 := measurePreserving_prodAssoc (pastLaw W l b) (freshLaw W b) ν
    have h2 := (MeasurePreserving.id (pastLaw W l b)).prod
      (Measure.measurePreserving_swap (μ := freshLaw W b) (ν := ν))
    have h3 := (measurePreserving_prodAssoc (pastLaw W l b) ν (freshLaw W b)).symm
    have := h3.comp (h2.comp h1)
    convert this using 1
    funext z; rfl
  rw [← hsh.map_eq, h1, Measure.map_map hsh.measurable (hPF.prodMap measurable_id)]
  rfl

end BlockBand.SourceProcess.RawTag
