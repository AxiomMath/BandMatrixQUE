module

public import BlockBand.Transmission.Dual.ExistsCoord
public import BlockBand.SourceProcess.Stochastic.SDE.ExportStop
public import BlockBand.SourceProcess.Stochastic.ItoNative.Formula
public import BlockBand.SourceProcess.Stochastic.Bridges.NativeIto

/-!
# `exists_` at `p = 1`: the exit-time solutions in flat coordinates

Probability space: the driver space `Ω₁ = DriverSample Unit (Fin 2)` (a `Type`), law
`P₁ = driverLaw (dirac ())` (two independent Brownian motions), augmented filtration `𝓖₁`.
For `D₀ > 0` and a start `z ∈ 𝒞₁`, a `SolFamily D₀ z` is a family of strong exit-time
solutions `X n` of radius `n` of the `(u, v)`-SDE (`uvDrift`, `uvDiff`) from `fromFlat z`.
Its flat images `Yf n = toFlat ∘ X n`:
* stay in the compact `toFlat '' closedBall 0 (max n ‖fromFlat z‖) ⊆ 𝒞₁` (`Yf_mem_K`);
* start at `z` at every `ω` and are continuous at every `ω`;
* are continuous semimartingales for `𝓖₁` with the flat dual characteristics switched off
  after the exit time `e n` (`isCSM_Yf`; the Itô formula with `toFlat_drift`,
  `toFlat_cov`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.Exists

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal

/-- The driver space with one dummy old state and two Brownian coordinates. -/
abbrev Ω₁ : Type := DriverSample Unit (Fin 2)

/-- The dummy old-state law. -/
abbrev μ₁ : Measure Unit := Measure.dirac ()

/-- The driver law. -/
abbrev P₁ : Measure Ω₁ := driverLaw (κ := Fin 2) μ₁

/-- The augmented driver filtration. -/
abbrev 𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁) := driverAugmented (κ := Fin 2) μ₁

instance : IsProbabilityMeasure P₁ := by
  unfold P₁ driverLaw; infer_instance

/-- A family of strong exit-time solutions of radii `n ∈ ℕ` of the `(u, v)`-SDE. -/
structure SolFamily (D0 : ℝ) (z : Fin 2 → ℝ) where
  X : ℕ → ℝ≥0 → Ω₁ → Fin 2 → ℝ
  strong : ∀ n : ℕ, IsStrongExitSolution μ₁ (uvDrift D0) (uvDiff D0) (fun _ => fromFlat z) n (X n)

theorem nonempty_solFamily {D0 : ℝ} (hD0 : 0 < D0) (z : Fin 2 → ℝ) :
    Nonempty (SolFamily D0 z) := by
  have h : ∀ n : ℕ, ∃ X, IsStrongExitSolution μ₁ (uvDrift D0) (uvDiff D0)
      (fun _ => fromFlat z) n X := fun n =>
    exists_solutionUntil_exitTime_strong (locallyLipschitz_uvDrift D0)
      (locallyLipschitz_uvDiff hD0) stronglyMeasurable_const n
  choose X hX using h
  exact ⟨⟨X, hX⟩⟩

variable {D0 : ℝ} {z : Fin 2 → ℝ}

/-- The radius bounding the `n`-th solution. -/
def rad (z : Fin 2 → ℝ) (n : ℕ) : ℝ := max n ‖fromFlat z‖

/-- The compact set of the chamber containing the `n`-th flat path. -/
def Kset (z : Fin 2 → ℝ) (n : ℕ) : Set (Fin 2 → ℝ) := toFlat '' Metric.closedBall 0 (rad z n)

theorem isCompact_Kset (z : Fin 2 → ℝ) (n : ℕ) : IsCompact (Kset z n) :=
  (isCompact_closedBall _ _).image contDiff_toFlat.continuous

theorem Kset_subset (z : Fin 2 → ℝ) (n : ℕ) : Kset z n ⊆ flatChamber 1 := by
  rintro _ ⟨w, -, rfl⟩; exact toFlat_mem w

namespace SolFamily

variable (F : SolFamily D0 z)

/-- The exit time of the `n`-th solution from the sup-norm ball of radius `n`. -/
def e (n : ℕ) : Ω₁ → WithTop ℝ≥0 := exitTime (F.X n) n

/-- The flat image of the `n`-th solution. -/
def Yf (n : ℕ) (t : ℝ≥0) (ω : Ω₁) : Fin 2 → ℝ := toFlat (F.X n t ω)

theorem isStoppingTime_e (n : ℕ) : IsStoppingTime 𝓖₁ (F.e n) := (F.strong n).stopping

theorem continuous_X (n : ℕ) (ω : Ω₁) : Continuous fun t => F.X n t ω := (F.strong n).continuous ω

theorem continuous_Yf (n : ℕ) (ω : Ω₁) : Continuous fun t => F.Yf n t ω :=
  contDiff_toFlat.continuous.comp (F.continuous_X n ω)

theorem X_zero (n : ℕ) (ω : Ω₁) : F.X n 0 ω = fromFlat z := (F.strong n).init ω

theorem Yf_zero (hz : z ∈ flatChamber 1) (n : ℕ) (ω : Ω₁) : F.Yf n 0 ω = z := by
  have h0 : 0 < z 0 := hz.2.2.1 0
  have h1 := hz.2.2.2 0
  rw [Yf, X_zero]
  exact toFlat_fromFlat h0 h1.1 h1.2

theorem X_stopped (n : ℕ) (t : ℝ≥0) (ω : Ω₁) :
    F.X n t ω = stoppedProcess (F.X n) (F.e n) t ω := ((F.strong n).stopped t ω).symm

theorem X_eq_of_e_le (n : ℕ) {t m : ℝ≥0} {ω : Ω₁} (hm : F.e n ω = m) (hmt : m ≤ t) :
    F.X n t ω = F.X n m ω := by
  rw [F.X_stopped n t ω, stoppedProcess_eq_of_ge (by rw [hm]; exact WithTop.coe_le_coe.2 hmt), hm]
  rfl

theorem norm_X_le (n : ℕ) (t : ℝ≥0) (ω : Ω₁) : ‖F.X n t ω‖ ≤ rad z n := by
  have key : ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ F.e n ω → ‖F.X n s ω‖ ≤ rad z n := by
    intro s hs
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h | h
    · rw [← h, X_zero]; exact le_max_right _ _
    · exact (norm_le_of_le_exitTimeOf (F.continuous_X n ω) h hs).trans (le_max_left _ _)
  by_cases ht : (t : WithTop ℝ≥0) ≤ F.e n ω
  · exact key t ht
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt (not_le.1 ht))
    have hmt : m ≤ t := by
      have := (not_le.1 ht).le; rw [← hm] at this; exact WithTop.coe_le_coe.1 this
    rw [F.X_eq_of_e_le n hm.symm hmt]
    exact key m (by rw [← hm])

theorem Yf_mem_K (n : ℕ) (t : ℝ≥0) (ω : Ω₁) : F.Yf n t ω ∈ Kset z n :=
  ⟨F.X n t ω, mem_closedBall_zero_iff.2 (F.norm_X_le n t ω), rfl⟩

theorem Yf_mem (n : ℕ) (t : ℝ≥0) (ω : Ω₁) : F.Yf n t ω ∈ flatChamber 1 := toFlat_mem _

/-- Radius consistency, almost surely for all pairs `n ≤ m`. -/
theorem ae_consistent (hD0 : 0 < D0) : ∀ᵐ ω ∂P₁, ∀ n m : ℕ, n ≤ m → F.e n ω ≤ F.e m ω ∧
    ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ F.e n ω → F.X n t ω = F.X m t ω := by
  rw [ae_all_iff]; intro n
  rw [ae_all_iff]; intro m
  by_cases hnm : n ≤ m
  · filter_upwards [(F.strong n).ae_consistent (locallyLipschitz_uvDrift D0)
      (locallyLipschitz_uvDiff hD0) (Nat.cast_le.2 hnm) (F.strong m)] with ω hω _
    exact ⟨hω.2.1, hω.2.2⟩
  · exact Eventually.of_forall fun ω h => absurd h hnm

/-- **The flat paths are continuous semimartingales** with the dual characteristics switched
off after the exit time. -/
theorem isCSM_Yf (hD0 : 0 < D0) (n : ℕ) :
    IsContinuousSemimartingale P₁ 𝓖₁ (F.Yf n)
      (fun t ω => switchOff (F.e n) (fun t ω => flatDrift D0 1 (F.Yf n t ω)) t ω)
      (fun t ω => switchOff (F.e n) (fun t ω => flatDiff D0 1 (F.Yf n t ω)) t ω) := by
  have hφ : ContDiff ℝ 2 fun p : ℝ × (Fin 2 → ℝ) => toFlat p.2 :=
    (contDiff_toFlat.of_le (by simp)).comp contDiff_snd
  have hX := (F.strong n).sol.1
  have hY := ItoNative.itoFormulaFor_native (κ := Fin 2) (μ := μ₁) (E := Fin 2 → ℝ) (F := Fin 2 → ℝ)
    _ _ _ hX _ hφ
  have H := hY.isContinuousSemimartingale
  have hd : ∀ w : Fin 2 → ℝ, DifferentiableAt ℝ toFlat w := fun w =>
    contDiff_toFlat.differentiable (by simp) w
  have hc : ∀ w : Fin 2 → ℝ, ContDiffAt ℝ 2 toFlat w := fun w =>
    (contDiff_toFlat.of_le (by simp)).contDiffAt
  have e1 : (fun (t : ℝ≥0) (ω : Ω₁) => timeDeriv (fun p : ℝ × (Fin 2 → ℝ) => toFlat p.2) ((t : ℝ), F.X n t ω) +
      spaceDeriv (fun p : ℝ × (Fin 2 → ℝ) => toFlat p.2) ((t : ℝ), F.X n t ω)
        (switchOff (exitTime (F.X n) n) (fun t ω => uvDrift D0 (F.X n t ω)) t ω) +
      (1 / 2 : ℝ) • ∑ a, spaceDeriv2 (fun p : ℝ × (Fin 2 → ℝ) => toFlat p.2) ((t : ℝ), F.X n t ω)
        (switchOff (exitTime (F.X n) n) (fun t ω => uvDiff D0 a (F.X n t ω)) t ω)
        (switchOff (exitTime (F.X n) n) (fun t ω => uvDiff D0 a (F.X n t ω)) t ω)) =
      fun t ω => switchOff (F.e n) (fun t ω => flatDrift D0 1 (F.Yf n t ω)) t ω := by
    funext t ω
    simp only [timeDeriv, spaceDeriv, spaceDeriv2, fderiv_comp_snd_time (hd _),
      fderiv_comp_snd_apply (hd _), fderiv_fderiv_comp_snd_apply (hc _), zero_add]
    unfold switchOff SolFamily.e SolFamily.Yf
    split_ifs with h
    · exact toFlat_drift hD0 _
    · simp
  have e2 : (fun (t : ℝ≥0) (ω : Ω₁) => Matrix.of fun i j => ∑ a,
      spaceDeriv (fun p : ℝ × (Fin 2 → ℝ) => toFlat p.2) ((t : ℝ), F.X n t ω)
        (switchOff (exitTime (F.X n) n) (fun t ω => uvDiff D0 a (F.X n t ω)) t ω) i *
      spaceDeriv (fun p : ℝ × (Fin 2 → ℝ) => toFlat p.2) ((t : ℝ), F.X n t ω)
        (switchOff (exitTime (F.X n) n) (fun t ω => uvDiff D0 a (F.X n t ω)) t ω) j) =
      fun t ω => switchOff (F.e n) (fun t ω => flatDiff D0 1 (F.Yf n t ω)) t ω := by
    funext t ω
    simp only [spaceDeriv, fderiv_comp_snd_apply (hd _)]
    unfold switchOff SolFamily.e SolFamily.Yf
    split_ifs with h
    · exact toFlat_cov hD0 _
    · ext i j; simp
  rw [e1, e2] at H
  exact H

end SolFamily

end BlockBand.Transmission.Dual.Exists
