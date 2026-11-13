module

public import BlockBand.Transmission.DualLift.Sphere
public import BlockBand.Transmission.Dual.ExistsSDE

/-!
# The lifted exit-time solutions from a random start

Probability space: the driver space `Ω = DriverSample S (Fin 5)` for any `S : Type` and
any probability `μ` on `S` (`S = Unit`, `μ = δ_()` for deterministic starts), law
`driverLaw μ`, augmented filtration `driverAugmented μ`. Start: a random point
`ξ : Ω → ℝ⁶`, measurable for the augmented time-zero σ-algebra, lying in `liftM` at every `ω`
(local well-posedness accepts random starts; the section `liftSection` produces such starts).

A `LiftFamily μ D₀ ξ` is a family of strong exit-time solutions `X n` of radius `n` of the
lifted SDE (`liftDrift`, `liftSigma`, no cutoff). Facts:
* every path is continuous, starts at `ξ`, and is stopped at its exit time `e n`;
* `ae_mem_liftM`: a.s. every `X n` stays in `liftM` for all times;
* `ae_consistent`: a.s. the radii are consistent (pathwise uniqueness);
* **`isCSM_proj`**: the projected path `π(X n)` is a continuous semimartingale for the
  augmented filtration with characteristics `vecGen π` and `Σ_a (Dπ σ_a)(Dπ σ_a)ᵀ` evaluated
  along `X n`, switched off after `e n` (Itô formula).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Transmission.Dual.Exists
open scoped NNReal

variable {S : Type} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

/-- The driver space. -/
abbrev LΩ (S : Type) [MeasurableSpace S] : Type := DriverSample S (Fin 5)

/-- The driver law. -/
abbrev LP : Measure (LΩ S) := driverLaw (κ := Fin 5) μ

/-- The augmented driver filtration. -/
abbrev L𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (LΩ S)) :=
  driverAugmented (κ := Fin 5) μ

instance : IsProbabilityMeasure (LP μ) := by
  unfold LP driverLaw; infer_instance

/-- An admissible random start: augmented-`𝓕₀`-measurable with values in `liftM`. -/
structure IsLiftStart (ξ : LΩ S → Fin 6 → ℝ) : Prop where
  meas : StronglyMeasurable[L𝓖 μ 0] ξ
  mem : ∀ ω, ξ ω ∈ liftM

/-- A family of strong exit-time solutions of radii `n ∈ ℕ` of the lifted SDE. -/
structure LiftFamily (D0 : ℝ) (ξ : LΩ S → Fin 6 → ℝ) where
  X : ℕ → ℝ≥0 → LΩ S → Fin 6 → ℝ
  strong : ∀ n : ℕ, IsStrongExitSolution μ (liftDrift D0) (liftSigma D0) ξ n (X n)

variable {μ}

theorem nonempty_liftFamily {D0 : ℝ} (hD0 : 0 < D0) {ξ : LΩ S → Fin 6 → ℝ}
    (hξ : IsLiftStart μ ξ) : Nonempty (LiftFamily μ D0 ξ) := by
  have h : ∀ n : ℕ, ∃ X, IsStrongExitSolution μ (liftDrift D0) (liftSigma D0) ξ n X := fun n =>
    exists_solutionUntil_exitTime_strong (locallyLipschitz_liftDrift D0)
      (locallyLipschitz_liftSigma hD0) hξ.meas n
  choose X hX using h
  exact ⟨⟨X, hX⟩⟩

variable {D0 : ℝ} {ξ : LΩ S → Fin 6 → ℝ}

namespace LiftFamily

variable (F : LiftFamily μ D0 ξ)

/-- The exit time of the `n`-th solution from the sup-norm ball of radius `n`. -/
def e (n : ℕ) : LΩ S → WithTop ℝ≥0 := exitTime (F.X n) n

/-- The projected (flat) path, without modification. -/
def Zp (n : ℕ) (t : ℝ≥0) (ω : LΩ S) : Fin 2 → ℝ := liftProj (F.X n t ω)

theorem isStoppingTime_e (n : ℕ) : IsStoppingTime (L𝓖 μ) (F.e n) := (F.strong n).stopping

theorem continuous_X (n : ℕ) (ω : LΩ S) : Continuous fun t => F.X n t ω :=
  (F.strong n).continuous ω

theorem continuous_Zp (n : ℕ) (ω : LΩ S) : Continuous fun t => F.Zp n t ω :=
  contDiff_liftProj.continuous.comp (F.continuous_X n ω)

theorem X_zero (n : ℕ) (ω : LΩ S) : F.X n 0 ω = ξ ω := (F.strong n).init ω

theorem X_stopped (n : ℕ) (t : ℝ≥0) (ω : LΩ S) :
    F.X n t ω = stoppedProcess (F.X n) (F.e n) t ω := ((F.strong n).stopped t ω).symm

theorem X_eq_of_e_le (n : ℕ) {t m : ℝ≥0} {ω : LΩ S} (hm : F.e n ω = m) (hmt : m ≤ t) :
    F.X n t ω = F.X n m ω := by
  rw [F.X_stopped n t ω, stoppedProcess_eq_of_ge (by rw [hm]; exact WithTop.coe_le_coe.2 hmt), hm]
  rfl

/-- Paths stay in the ball of radius `max n ‖ξ‖`. -/
theorem norm_X_le (n : ℕ) (t : ℝ≥0) (ω : LΩ S) : ‖F.X n t ω‖ ≤ max (n : ℝ) ‖ξ ω‖ := by
  have key : ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ F.e n ω → ‖F.X n s ω‖ ≤ max (n : ℝ) ‖ξ ω‖ := by
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

/-- **Invariance of `liftM` along the family.** -/
theorem ae_mem_liftM (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) :
    ∀ᵐ ω ∂LP μ, ∀ n : ℕ, ∀ t, F.X n t ω ∈ liftM := by
  rw [ae_all_iff]
  intro n
  exact ae_forall_mem_liftM hD0 hξ.meas (Eventually.of_forall hξ.mem) (F.strong n)

/-- Radius consistency, almost surely for all pairs `n ≤ m`. -/
theorem ae_consistent (hD0 : 0 < D0) : ∀ᵐ ω ∂LP μ, ∀ n m : ℕ, n ≤ m → F.e n ω ≤ F.e m ω ∧
    ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ F.e n ω → F.X n t ω = F.X m t ω := by
  rw [ae_all_iff]; intro n
  rw [ae_all_iff]; intro m
  by_cases hnm : n ≤ m
  · filter_upwards [(F.strong n).ae_consistent (locallyLipschitz_liftDrift D0)
      (locallyLipschitz_liftSigma hD0) (Nat.cast_le.2 hnm) (F.strong m)] with ω hω _
    exact ⟨hω.2.1, hω.2.2⟩
  · exact Eventually.of_forall fun ω h => absurd h hnm

/-- The lifted covariance of `π`. -/
def liftCov (D0 : ℝ) (ξ : Fin 6 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => ∑ a, fderiv ℝ liftProj ξ (liftSigma D0 a ξ) i *
    fderiv ℝ liftProj ξ (liftSigma D0 a ξ) j

/-- **The projected paths are continuous semimartingales** (lifted characteristics, switched
off after the exit time). -/
theorem isCSM_proj (n : ℕ) :
    IsContinuousSemimartingale (LP μ) (L𝓖 μ) (F.Zp n)
      (fun t ω => switchOff (F.e n) (fun t ω =>
        SourceSDE.vecGen (liftDrift D0) (liftSigma D0) liftProj (F.X n t ω)) t ω)
      (fun t ω => switchOff (F.e n) (fun t ω => liftCov D0 (F.X n t ω)) t ω) := by
  have hφ : ContDiff ℝ 2 fun p : ℝ × (Fin 6 → ℝ) => liftProj p.2 :=
    (contDiff_liftProj.of_le (by simp)).comp contDiff_snd
  have hX := (F.strong n).sol.1
  have hY := ItoNative.itoFormulaFor_native (κ := Fin 5) (μ := μ) (E := Fin 6 → ℝ)
    (F := Fin 2 → ℝ) _ _ _ hX _ hφ
  have H := hY.isContinuousSemimartingale
  have hd : ∀ w : Fin 6 → ℝ, DifferentiableAt ℝ liftProj w := fun w =>
    contDiff_liftProj.differentiable (by simp) w
  have hc : ∀ w : Fin 6 → ℝ, ContDiffAt ℝ 2 liftProj w := fun w =>
    (contDiff_liftProj.of_le (by simp)).contDiffAt
  have e1 : (fun (t : ℝ≥0) (ω : LΩ S) =>
      timeDeriv (fun p : ℝ × (Fin 6 → ℝ) => liftProj p.2) ((t : ℝ), F.X n t ω) +
      spaceDeriv (fun p : ℝ × (Fin 6 → ℝ) => liftProj p.2) ((t : ℝ), F.X n t ω)
        (switchOff (exitTime (F.X n) n) (fun t ω => liftDrift D0 (F.X n t ω)) t ω) +
      (1 / 2 : ℝ) • ∑ a, spaceDeriv2 (fun p : ℝ × (Fin 6 → ℝ) => liftProj p.2)
        ((t : ℝ), F.X n t ω)
        (switchOff (exitTime (F.X n) n) (fun t ω => liftSigma D0 a (F.X n t ω)) t ω)
        (switchOff (exitTime (F.X n) n) (fun t ω => liftSigma D0 a (F.X n t ω)) t ω)) =
      fun t ω => switchOff (F.e n) (fun t ω =>
        SourceSDE.vecGen (liftDrift D0) (liftSigma D0) liftProj (F.X n t ω)) t ω := by
    funext t ω
    simp only [timeDeriv, spaceDeriv, spaceDeriv2, fderiv_comp_snd_time (hd _),
      fderiv_comp_snd_apply (hd _), fderiv_fderiv_comp_snd_apply (hc _), zero_add]
    unfold switchOff LiftFamily.e
    split_ifs with h
    · rfl
    · simp
  have e2 : (fun (t : ℝ≥0) (ω : LΩ S) => Matrix.of fun i j => ∑ a,
      spaceDeriv (fun p : ℝ × (Fin 6 → ℝ) => liftProj p.2) ((t : ℝ), F.X n t ω)
        (switchOff (exitTime (F.X n) n) (fun t ω => liftSigma D0 a (F.X n t ω)) t ω) i *
      spaceDeriv (fun p : ℝ × (Fin 6 → ℝ) => liftProj p.2) ((t : ℝ), F.X n t ω)
        (switchOff (exitTime (F.X n) n) (fun t ω => liftSigma D0 a (F.X n t ω)) t ω) j) =
      fun t ω => switchOff (F.e n) (fun t ω => liftCov D0 (F.X n t ω)) t ω := by
    funext t ω
    simp only [spaceDeriv, fderiv_comp_snd_apply (hd _)]
    unfold switchOff LiftFamily.e
    split_ifs with h
    · rfl
    · ext i j; simp
  rw [e1, e2] at H
  exact H

end LiftFamily

end BlockBand.Transmission.DualLift
