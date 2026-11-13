module

public import BlockBand.Transmission.DualLift.LPath

/-!
# The realization of the lift

`good₂ ⊆ good` is a measurable set of full measure on which the corner limit (`IsConv`) also
holds. The realization `(N₂, X₂, Y₂)` is the glued process on `good₂` and the constant start
`(1, π ξ)` off `good₂`. Facts: adapted at every `ω` (`measurable_N₂`, `measurable_Z₂`),
`N₂ 0 = 1`, `Z₂ 0 = π ξ` everywhere; a boundary deletion path on `good₂ ∩ EntrGood`
(`isBoundaryDeletionPath_N₂`), a deletion path there if moreover `π ξ ∈ 𝒞₁`
(`isDeletionPath_N₂`); `dualMartingale` in closed form (`dualMartingale_eq₂`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists
open scoped NNReal ENNReal

variable {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : LΩ S → Fin 6 → ℝ}

namespace LiftFamily

variable (F : LiftFamily μ D0 ξ)

/-- Good paths on which the corner limit holds. -/
def good₂ : Set (LΩ S) := (toMeasurable (LP μ) {ω | ¬(ω ∈ F.good ∧ F.IsConv ω)})ᶜ

theorem measurableSet_good₂ : MeasurableSet F.good₂ := (measurableSet_toMeasurable _ _).compl

theorem measure_good₂_compl (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) : LP μ F.good₂ᶜ = 0 := by
  rw [good₂, compl_compl, measure_toMeasurable]; exact ae_iff.1 (F.ae_good_conv hD0 hξ)

theorem good₂_spec {ω : LΩ S} (hω : ω ∈ F.good₂) : ω ∈ F.good ∧ F.IsConv ω := by
  by_contra h; exact hω (subset_toMeasurable _ _ h)

theorem ae_good₂ (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) : ∀ᵐ ω ∂LP μ, ω ∈ F.good₂ := by
  rw [ae_iff]; exact F.measure_good₂_compl hD0 hξ

theorem measurableSet_good₂_aug (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (t : ℝ≥0) :
    MeasurableSet[L𝓖 μ t] F.good₂ :=
  measurableSet_aug_of_full μ F.measurableSet_good₂ (F.measure_good₂_compl hD0 hξ) t

open scoped Classical in
/-- The level of the realization. -/
def N₂ (t : ℝ≥0) (ω : LΩ S) : ℕ := if ω ∈ F.good₂ then F.Nd t ω else 1

open scoped Classical in
/-- The flat coordinates of the realization. -/
def Z₂ (t : ℝ≥0) (ω : LΩ S) : Fin 2 → ℝ := if ω ∈ F.good₂ then F.Zd t ω else liftProj (ξ ω)

/-- The `x`-sequence. -/
def X₂ (t : ℝ≥0) (ω : LΩ S) : ℕ → ℝ := fun _ => F.Z₂ t ω 0

/-- The `y`-sequence. -/
def Y₂ (t : ℝ≥0) (ω : LΩ S) : ℕ → ℝ := fun _ => F.Z₂ t ω 1

theorem N₂_le_one (t : ℝ≥0) (ω : LΩ S) : F.N₂ t ω ≤ 1 := by
  unfold N₂; split_ifs
  · exact F.Nd_le_one t ω
  · exact le_rfl

theorem N₂_zero (ω : LΩ S) : F.N₂ 0 ω = 1 := by unfold N₂; split_ifs <;> simp [F.Nd_zero]

theorem Z₂_zero (ω : LΩ S) : F.Z₂ 0 ω = liftProj (ξ ω) := by
  unfold Z₂; split_ifs <;> simp [F.Zd_zero]

theorem dualCoordOf_2 (t : ℝ≥0) (ω : LΩ S) :
    dualCoordOf 1 (F.X₂ t ω) (F.Y₂ t ω) = ofFlat 1 (F.Z₂ t ω) := by
  ext i
  · simp [dualCoordOf, X₂, Fin.fin_one_eq_zero i]; rfl
  · simp [dualCoordOf, Y₂, Fin.fin_one_eq_zero i]; rfl

theorem measurable_N₂ (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (t : ℝ≥0) :
    Measurable[L𝓖 μ t] (F.N₂ t) :=
  Measurable.ite (F.measurableSet_good₂_aug hD0 hξ t) (F.measurable_Nd hD0 hξ t) measurable_const

omit [IsProbabilityMeasure μ] in
theorem measurable_start (hξ : IsLiftStart μ ξ) (t : ℝ≥0) :
    Measurable[L𝓖 μ t] fun ω => liftProj (ξ ω) :=
  contDiff_liftProj.continuous.measurable.comp ((hξ.meas.mono ((L𝓖 μ).mono
    (zero_le : (0 : ℝ≥0) ≤ t))).measurable)

theorem measurable_Z₂ (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (t : ℝ≥0) :
    Measurable[L𝓖 μ t] (F.Z₂ t) :=
  Measurable.ite (F.measurableSet_good₂_aug hD0 hξ t) (F.measurable_Zd hD0 hξ t)
    (measurable_start hξ t)

theorem adapted₂ (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (t : ℝ≥0) :
    Measurable[L𝓖 μ t] (F.N₂ t) ∧ Measurable[L𝓖 μ t] (F.X₂ t) ∧ Measurable[L𝓖 μ t] (F.Y₂ t) :=
  ⟨F.measurable_N₂ hD0 hξ t,
    (continuous_pi fun _ => continuous_apply 0).measurable.comp (F.measurable_Z₂ hD0 hξ t),
    (continuous_pi fun _ => continuous_apply 1).measurable.comp (F.measurable_Z₂ hD0 hξ t)⟩

theorem paths_eq {ω : LΩ S} (hω : ω ∈ F.good₂) :
    ((fun t => F.N₂ t ω) = fun t => F.Nd t ω) ∧ ((fun t => F.X₂ t ω) = fun t => F.Xd t ω) ∧
      ((fun t => F.Y₂ t ω) = fun t => F.Yd t ω) := by
  have hZ : ∀ t, F.Z₂ t ω = F.Zd t ω := fun t => by simp only [Z₂, hω, ite_true]
  refine ⟨funext fun t => by simp [N₂, hω], funext fun t => ?_, funext fun t => ?_⟩
  · show (fun _ => F.Z₂ t ω 0) = fun _ => F.Zd t ω 0
    rw [hZ]
  · show (fun _ => F.Z₂ t ω 1) = fun _ => F.Zd t ω 1
    rw [hZ]

theorem isBoundaryDeletionPath_N₂ (hξ : IsLiftStart μ ξ) {ω : LΩ S} (hω : ω ∈ F.good₂)
    (hE : F.EntrGood ω) :
    IsBoundaryDeletionPath (fun t => F.N₂ t ω) (fun t => F.X₂ t ω) (fun t => F.Y₂ t ω) := by
  obtain ⟨h1, h2, h3⟩ := F.paths_eq hω
  rw [h1, h2, h3]
  exact F.isBoundaryDeletionPath_of_good hξ (F.good₂_spec hω).1 (F.good₂_spec hω).2 hE

theorem isDeletionPath_N₂ (hξ : IsLiftStart μ ξ) {ω : LΩ S} (hω : ω ∈ F.good₂)
    (hE : F.EntrGood ω) (h0 : liftProj (ξ ω) ∈ flatChamber 1) :
    IsDeletionPath (fun t => F.N₂ t ω) (fun t => F.X₂ t ω) (fun t => F.Y₂ t ω) := by
  obtain ⟨h1, h2, h3⟩ := F.paths_eq hω
  rw [h1, h2, h3]
  exact F.isDeletionPath_of_good hξ (F.good₂_spec hω).1 (F.good₂_spec hω).2 hE h0

/-- The flat test function. -/
def liftFc (f : DualCoord 1 → ℝ) : (Fin 2 → ℝ) → ℝ := fun w => f (ofFlat 1 w)

/-- The flat generator of the test. -/
def liftLc (f : DualCoord 1 → ℝ) (D0 : ℝ) : (Fin 2 → ℝ) → ℝ :=
  fun w => dualGenerator D0 f (ofFlat 1 w)

/-- The `dualMartingale` of the realization in closed form. -/
theorem dualMartingale_eq₂ (f : DualCoord 1 → ℝ) (t : ℝ≥0) (ω : LΩ S) :
    dualMartingale D0 1 f F.N₂ F.X₂ F.Y₂ t ω =
      (if F.N₂ t ω = 1 then liftFc f (F.Z₂ t ω) else 0) - liftFc f (liftProj (ξ ω)) -
        ∫ u in Ioc (0 : ℝ) t, (if F.N₂ u.toNNReal ω = 1 then
          liftLc f D0 (F.Z₂ u.toNNReal ω) else 0) := by
  have hex : ∃ u ≤ t, F.N₂ u ω ≤ 1 := ⟨0, zero_le, F.N₂_le_one 0 ω⟩
  have hent : dualEntrance F.N₂ 1 ω = 0 := by
    have : {s | F.N₂ s ω ≤ 1} = univ := eq_univ_of_forall fun s => F.N₂_le_one s ω
    simp only [dualEntrance, this, csInf_univ]; rfl
  simp only [dualMartingale, dualEntranceValue, hex, ite_true, hent, dualLift, F.dualCoordOf_2,
    F.N₂_zero, F.Z₂_zero, liftFc, liftLc]

end LiftFamily

end BlockBand.Transmission.DualLift
