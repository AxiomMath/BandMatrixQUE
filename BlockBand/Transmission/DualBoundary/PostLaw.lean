module

public import BlockBand.Transmission.DualBoundary.Markov
public import BlockBand.Transmission.DualBoundary.LiftFrom
public import BlockBand.Transmission.Dual.Unique

/-!
# The post-`s` law of a boundary realization is a lift law

Setting: a one-pair boundary realization `h` on `(Ω, P, 𝓖)` (`Ω : Type`), a deterministic
`s > 0` with `P(postSet) ≠ 0` (`postSet = {good, N_s = 1}`), and on a driver space
`LΩ S` an admissible start `ξ` with `π ξ ∈ 𝒞₁` everywhere whose projection has the law of
`Z̄_s = (X_s 0, Y_s 0)` under `P[|postSet]`. Then for **every** lifted family `F` from `ξ`:

**`map_zbar_post_eq_lift`**: the law of the post-`s` read-out path `u ↦ Z̄_{s+u}` (as
`zbarOf` of the truncated post state) under `P[|postSet]` is the law of `u ↦ liftZbar F u`.

Proof: the Markov property `markov_at` and `LiftFamily.exists_isDualFrom` give two
`IsDualFrom` realizations at level one with the same initial law; `Dual.dualUniqueAt`
(`DualUniqueAt D₀ 1`) identifies the laws of their truncated states; push forward by the
measurable read-out.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists BlockBand.Transmission.DualLift
open BlockBand.SourceProcess.Stochastic
open scoped NNReal ENNReal

/-- The level-one initial state with coordinates `z`. -/
def startState (z : Fin 2 → ℝ) : DualState :=
  (1, truncCoord 1 (fun _ => z 0), truncCoord 1 (fun _ => z 1))

theorem measurable_startState : Measurable startState := by
  refine measurable_const.prodMk (Measurable.prodMk ?_ ?_) <;>
  · refine measurable_pi_iff.2 fun i => ?_
    unfold truncCoord
    split_ifs
    · exact measurable_pi_apply _
    · exact measurable_const

/-- The read-out of a path of states. -/
def zbarPath (γ : ℝ≥0 → DualState) : ℝ≥0 → Fin 2 → ℝ := fun u => zbarOf (γ u)

theorem measurable_zbarPath : Measurable zbarPath :=
  measurable_pi_iff.2 fun u => measurable_zbarOf.comp (measurable_pi_apply u)

/-- **The post-`s` read-out law is the lift read-out law.** -/
theorem map_zbar_post_eq_lift {D0 : ℝ} (hD0 : 0 < D0) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {x y : ℝ}
    {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) {s : ℝ≥0} (hs : 0 < s)
    (hA0 : P (postSet P N X Y s) ≠ 0)
    {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
    {ξ : LΩ S → Fin 6 → ℝ} (hξ : IsLiftStart μ ξ) (hin : ∀ ω, liftProj (ξ ω) ∈ flatChamber 1)
    (hlaw : (LP μ).map (fun ω => liftProj (ξ ω)) =
      (P[|postSet P N X Y s]).map (fun ω => ![X s ω 0, Y s ω 0]))
    (F : DualLift.LiftFamily μ D0 ξ) :
    (P[|postSet P N X Y s]).map (fun ω => zbarPath
        (dualState (postN P N X Y s) (postC P N X Y s X) (postC P N X Y s Y) ω)) =
      (LP μ).map (fun ω u => DualFeller.liftZbar F u ω) := by
  have := h.prob
  set A := postSet P N X Y s with hAdef
  have hA := measurableSet_postSet_aug h s
  have hAm : MeasurableSet A := (augmentedFiltration 𝓖 P).le s _ hA
  have hpost := markov_at h hs hA subset_rfl hA0
  obtain ⟨N', X', Y', hL, hae⟩ := LiftFamily.exists_isDualFrom F hD0 hξ hin
  have hW : Measurable fun ω => ![X s ω 0, Y s ω 0] := by
    have hX := ((h.adapted s).2.1.mono (𝓖.le s) le_rfl)
    have hY := ((h.adapted s).2.2.mono (𝓖.le s) le_rfl)
    have hX0 : Measurable fun ω => X s ω 0 := (measurable_pi_apply 0).comp hX
    have hY0 : Measurable fun ω => Y s ω 0 := (measurable_pi_apply 0).comp hY
    refine measurable_pi_iff.2 fun i => ?_
    fin_cases i
    · exact hX0
    · exact hY0
  have hZ : Measurable fun ω => liftProj (ξ ω) :=
    contDiff_liftProj.continuous.measurable.comp (hξ.meas.mono ((L𝓖 μ).le 0)).measurable
  have h0post : (fun ω => dualState (postN P N X Y s) (postC P N X Y s X) (postC P N X Y s Y) ω 0)
      =ᵐ[P[|A]] startState ∘ fun ω => ![X s ω 0, Y s ω 0] := by
    filter_upwards [ae_cond_mem hAm] with ω hω
    have hω' : ω ∈ postSet P N X Y s := hω
    simp only [dualState, postN, postC, hω', ite_true, add_zero, hω'.2, Function.comp,
      startState]
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> funext i <;> by_cases hi : i = 0 <;>
      simp [truncCoord, hi]
  have h0lift : (fun ω => dualState N' X' Y' ω 0) =ᵐ[LP μ]
      startState ∘ fun ω => liftProj (ξ ω) := by
    filter_upwards [hae] with ω hω
    obtain ⟨h1, h2, h3⟩ := hω 0
    simp only [dualState, h1, h2, h3, F.N₂_zero, Function.comp, startState]
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> funext i <;>
      simp [truncCoord, DualLift.LiftFamily.X₂, DualLift.LiftFamily.Y₂, F.Z₂_zero]
  have hstart : (P[|A]).map
      (fun ω => dualState (postN P N X Y s) (postC P N X Y s X) (postC P N X Y s Y) ω 0) =
      (LP μ).map (fun ω => dualState N' X' Y' ω 0) := by
    rw [Measure.map_congr h0post, Measure.map_congr h0lift,
      ← Measure.map_map measurable_startState hW, ← Measure.map_map measurable_startState hZ,
      hlaw]
  have hU := dualUniqueAt hD0 1 Ω (P[|A]) (shiftAug 𝓖 P s) _ _ _ (LΩ S) (LP μ) (L𝓖 μ)
    N' X' Y' hpost hL hstart
  have e1 : (fun ω => zbarPath
      (dualState (postN P N X Y s) (postC P N X Y s X) (postC P N X Y s Y) ω)) =
      zbarPath ∘ dualState (postN P N X Y s) (postC P N X Y s X) (postC P N X Y s Y) := rfl
  rw [e1, ← Measure.map_map measurable_zbarPath hpost.measurable_dualState, hU,
    Measure.map_map measurable_zbarPath hL.measurable_dualState]
  refine Measure.map_congr ?_
  filter_upwards [hae] with ω hω
  funext u
  obtain ⟨h1, h2, h3⟩ := hω u
  simp only [Function.comp, zbarPath]
  rw [← LiftFamily.zbarOf_dualState₂ F u ω]
  simp [dualState, h1, h2, h3]

end BlockBand.Transmission.DualBoundary
