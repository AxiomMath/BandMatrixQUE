module

public import BlockBand.Transmission.DualEntrance.LiftEntrance
public import BlockBand.Transmission.Dual.Normalize
public import BlockBand.Transmission.DualFeller.Interface

/-!
# The lift from a random interior start is an `IsDualFrom` realization

Setting: the driver space `LΩ S` with law `LP μ` (any `S : Type`, any probability `μ`)
and augmented filtration `L𝓖 μ`; `D₀ > 0`; an admissible random start `ξ` (`IsLiftStart`)
whose projection is in the open chamber `𝒞₁` at every `ω`; **any** lifted family `F`.

* **`LiftFamily.exists_isDualFrom`**: the lifted realization `(F.N₂, F.X₂, F.Y₂)`, modified on a
  measurable null set to the constant path at the fixed interior point `(1, 1/2)`, is an
  `IsDualFrom (LP μ) (L𝓖 μ) D₀ 1` realization, a.s. equal to `(F.N₂, F.X₂, F.Y₂)` at all times.
  It is stated for every `F` (not just some realization) because start continuity compares
  `liftZbar F` for different families.
* `zbarOf`, `LiftFamily.zbarOf_dualState₂`: the read-out `Z̄ = (X_t 0, Y_t 0)` of the
  truncated state is `liftZbar F` at every `ω`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists BlockBand.Transmission.DualLift
open scoped NNReal ENNReal

/-- The read-out `Z̄ = (x₀, y₀)` of a dual state. -/
def zbarOf (s : DualState) : Fin 2 → ℝ := ![s.2.1 0, s.2.2 0]

theorem measurable_zbarOf : Measurable zbarOf := by
  have h0 : Measurable fun s : DualState => s.2.1 0 :=
    (measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)
  have h1 : Measurable fun s : DualState => s.2.2 0 :=
    (measurable_pi_apply 0).comp (measurable_snd.comp measurable_snd)
  refine measurable_pi_iff.2 fun i => ?_
  fin_cases i
  · simpa [zbarOf] using h0
  · simpa [zbarOf] using h1

theorem isRatioParameter_ref : IsRatioParameter ![(1 : ℝ)] ![1 / 2] :=
  ⟨Subsingleton.strictMono _, Subsingleton.strictMono _, fun i => by
    rw [Fin.fin_one_eq_zero i]; norm_num, fun i => by rw [Fin.fin_one_eq_zero i]; norm_num⟩

namespace LiftFamily

variable {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : LΩ S → Fin 6 → ℝ} (F : DualLift.LiftFamily μ D0 ξ)

/-- The read-out of the lifted truncated state is `liftZbar F` (at every `ω`). -/
theorem zbarOf_dualState₂ (t : ℝ≥0) (ω : LΩ S) :
    zbarOf (dualState F.N₂ F.X₂ F.Y₂ ω t) = DualFeller.liftZbar F t ω := by
  have h1 := F.N₂_le_one t ω
  unfold zbarOf DualFeller.liftZbar
  by_cases h : F.N₂ t ω = 1
  · funext i; fin_cases i <;> simp [dualState, truncCoord, h, DualLift.LiftFamily.X₂,
      DualLift.LiftFamily.Y₂]
  · have h0 : F.N₂ t ω = 0 := by omega
    funext i; fin_cases i <;> simp [dualState, truncCoord, h0]

open scoped Classical in
/-- **The lift from a random interior start, normalized, is `IsDualFrom` at level one.** -/
theorem exists_isDualFrom (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ)
    (hin : ∀ ω, liftProj (ξ ω) ∈ flatChamber 1) :
    ∃ (N' : ℝ≥0 → LΩ S → ℕ) (X' Y' : ℝ≥0 → LΩ S → ℕ → ℝ),
      IsDualFrom (LP μ) (L𝓖 μ) D0 1 N' X' Y' ∧
      ∀ᵐ ω ∂LP μ, ∀ t, N' t ω = F.N₂ t ω ∧ X' t ω = F.X₂ t ω ∧ Y' t ω = F.Y₂ t ω := by
  set Good : Set (LΩ S) := {ω | ω ∈ F.good₂ ∧ F.EntrGood ω} with hGood
  have hae : ∀ᵐ ω ∂LP μ, ω ∈ Good := by
    filter_upwards [F.ae_good₂ hD0 hξ, DualEntrance.liftEntrance_holds hD0 S μ ξ hξ F]
      with ω h1 h2 using ⟨h1, h2⟩
  set B := toMeasurable (LP μ) Goodᶜ with hBdef
  have hBm : MeasurableSet B := measurableSet_toMeasurable _ _
  have hB0 : LP μ B = 0 := by rw [hBdef, measure_toMeasurable]; exact ae_iff.1 hae
  have hgood : ∀ ω, ω ∉ B → ω ∈ Good := fun ω hω => by
    by_contra hc; exact hω (subset_toMeasurable _ _ hc)
  have hBaug : ∀ t, MeasurableSet[L𝓖 μ t] B := fun t => by
    have := measurableSet_aug_of_full μ hBm.compl (by rw [compl_compl]; exact hB0) t
    simpa using this.compl
  have hnotB : ∀ᵐ ω ∂LP μ, ω ∉ B := measure_eq_zero_iff_ae_notMem.1 hB0
  have href := isRatioParameter_ref
  refine ⟨modN B 1 F.N₂, modX B ![(1 : ℝ)] F.X₂, modX B ![1 / 2] F.Y₂, ?_, ?_⟩
  · refine
      { prob := inferInstance
        adapted := fun t => ?_
        start := Eventually.of_forall fun ω => ?_
        bound := fun ω => ?_
        paths := fun ω => ?_
        martingale := fun q hq hq1 f hf hfc hfs => ?_ }
    · obtain ⟨hN, hX, hY⟩ := F.adapted₂ hD0 hξ t
      exact ⟨Measurable.ite (hBaug t) measurable_const hN,
        Measurable.ite (hBaug t) (measurable_const (a := extendFin ![(1 : ℝ)])) hX,
        Measurable.ite (hBaug t) (measurable_const (a := extendFin ![(1 / 2 : ℝ)])) hY⟩
    · by_cases hω : ω ∈ B
      · simp [modN, hω]
      · simp [modN, hω, F.N₂_zero]
    · by_cases hω : ω ∈ B
      · simp [modN, hω]
      · simp [modN, hω, F.N₂_zero]
    · by_cases hω : ω ∈ B
      · simpa [modN, modX, hω] using isDeletionPath_const href
      · have hg := hgood ω hω
        simpa [modN, modX, hω] using F.isDeletionPath_N₂ hξ hg.1 hg.2 (hin ω)
    · obtain rfl : q = 1 := le_antisymm hq1 hq
      have hM := F.martingale_dualMartingale₂ hD0 hξ hf hfc hfs
      set c : ℝ≥0 → ℝ := fun t => dualMartingale D0 1 f (fun _ (_ : Unit) => 1)
        (fun _ _ => extendFin ![(1 : ℝ)]) (fun _ _ => extendFin ![(1 / 2 : ℝ)]) t ()
      have hrep : ∀ t, dualMartingale D0 1 f (modN B 1 F.N₂) (modX B ![(1 : ℝ)] F.X₂)
          (modX B ![1 / 2] F.Y₂) t =
          fun ω => if ω ∈ B then c t else dualMartingale D0 1 f F.N₂ F.X₂ F.Y₂ t ω := fun t => by
        funext ω
        by_cases hω : ω ∈ B
        · simp only [hω, ↓reduceIte]
          exact dualMartingale_congr D0 1 f (fun s => by simp [modN, hω])
            (fun s => by simp [modX, hω]) (fun s => by simp [modX, hω]) t
        · simp only [hω, ↓reduceIte]
          exact dualMartingale_congr D0 1 f (fun s => by simp [modN, hω])
            (fun s => by simp [modX, hω]) (fun s => by simp [modX, hω]) t
      refine martingale_of_ae_eq hM (fun t => ?_) (fun t => ?_)
      · rw [hrep t]
        exact StronglyMeasurable.ite (hBaug t) stronglyMeasurable_const (hM.1 t)
      · rw [hrep t]
        filter_upwards [hnotB] with ω hω
        simp [hω]
  · filter_upwards [hnotB] with ω hω t
    simp [modN, modX, hω]

end LiftFamily

end BlockBand.Transmission.DualBoundary
