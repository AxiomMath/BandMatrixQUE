module

public import BlockBand.Transmission.Dual.GChartQ
public import BlockBand.Transmission.Dual.GChart
public import BlockBand.Transmission.Dual.GBridge
public import BlockBand.Transmission.Dual.ExistsSDE
public import BlockBand.Transmission.Dual.UniqueLevel

/-!
# The level-`q` dual up to exhaustion: exit-time solutions in the global chart

Driver space `Ω_q = DriverSample Unit (Fin (q+q))` (law `P_q`, augmented filtration `𝓖_q`). In
the chart `chartQ q` the flat dual `(flatDrift, flatDiff)` has the `C^∞` coefficients
`b1Drift = chartDrift`, `b1Sigma = chartSigma` (with `σ_a = flatSigma a`). For `z ∈ 𝒞_q`, a
`B1Family D₀ q z` is a family of strong exit-time solutions `X n` of radius `n` from
`chartQInv z`; its flat paths `Yf n = chartQ ∘ X n`:
* start at `z` and are continuous at every `ω`, and stay in the chamber;
* are continuous semimartingales with the flat dual characteristics switched off after the exit
  time `e n` (`isCSM_Yf`: Itô, `chart_drift_eq`, `chart_sigma_eq`, `flatSigma_cov`);
* solve the flat dual martingale problem in `chartQ '' ball 0 n` (`isMPSolutionOn_Yf`, via
  `isMPSolutionOn_of_agree`), hence in every interior domain `W` of the chamber for `n`
  large (`exists_isMPSolutionOn_Yf`): the comparison solution of the local Doob identity
  `lemma1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.Transmission.Dual.Exists
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {q : ℕ} {D0 : ℝ}

/-- The driver space of level `q`. -/
abbrev Ωq (q : ℕ) : Type := DriverSample Unit (Fin (q + q))

/-- Its law. -/
abbrev Pq (q : ℕ) : Measure (Ωq q) := driverLaw (κ := Fin (q + q)) μ₁

/-- Its augmented filtration. -/
abbrev 𝓖q (q : ℕ) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ωq q)) :=
  driverAugmented (κ := Fin (q + q)) μ₁

instance (q : ℕ) : IsProbabilityMeasure (Pq q) := by unfold Pq driverLaw; infer_instance

/-- The chart drift of the dual. -/
def b1Drift (D0 : ℝ) (q : ℕ) : (Fin (q + q) → ℝ) → Fin (q + q) → ℝ :=
  chartDrift (chartQ q) (flatDrift D0 q) (flatSigma D0 q)

/-- The chart noise of the dual. -/
def b1Sigma (D0 : ℝ) (q : ℕ) (a : Fin (q + q)) : (Fin (q + q) → ℝ) → Fin (q + q) → ℝ :=
  chartSigma (chartQ q) (flatSigma D0 q) a

theorem hinv_chartQ (w : Fin (q + q) → ℝ) : ∃ e : (Fin (q + q) → ℝ) ≃L[ℝ] (Fin (q + q) → ℝ),
    (e : (Fin (q + q) → ℝ) →L[ℝ] (Fin (q + q) → ℝ)) = fderiv ℝ (chartQ q) w :=
  exists_equiv_fderiv_of_leftInverse (contDiff_chartQ.differentiable (by simp) w)
    (differentiableAt_chartQInv (chartQ_mem w)) chartQInv_chartQ

theorem contDiffOn_flatDrift_top (D0 : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (flatDrift D0 q) (flatChamber q) := fun _ hw =>
  (contDiffAt_flatDrift D0 hw).contDiffWithinAt

theorem locallyLipschitz_b1Drift (hD0 : 0 < D0) : LocallyLipschitz (b1Drift D0 q) :=
  locallyLipschitz_chartDrift contDiff_chartQ hinv_chartQ (contDiffOn_flatDrift_top D0)
    (contDiffOn_flatSigma hD0) chartQ_mem

theorem locallyLipschitz_b1Sigma (hD0 : 0 < D0) (a : Fin (q + q)) :
    LocallyLipschitz (b1Sigma D0 q a) :=
  locallyLipschitz_chartSigma contDiff_chartQ hinv_chartQ (contDiffOn_flatSigma hD0) chartQ_mem a

/-- A family of strong exit-time solutions of radii `n` of the chart SDE. -/
structure B1Family (D0 : ℝ) (q : ℕ) (z : Fin (q + q) → ℝ) where
  X : ℕ → ℝ≥0 → Ωq q → Fin (q + q) → ℝ
  strong : ∀ n : ℕ, IsStrongExitSolution μ₁ (b1Drift D0 q) (b1Sigma D0 q)
    (fun _ => chartQInv q z) n (X n)

theorem nonempty_b1Family (hD0 : 0 < D0) (z : Fin (q + q) → ℝ) : Nonempty (B1Family D0 q z) := by
  have h : ∀ n : ℕ, ∃ X, IsStrongExitSolution μ₁ (b1Drift D0 q) (b1Sigma D0 q)
      (fun _ => chartQInv q z) n X := fun n =>
    exists_solutionUntil_exitTime_strong (locallyLipschitz_b1Drift hD0)
      (locallyLipschitz_b1Sigma hD0) stronglyMeasurable_const n
  choose X hX using h
  exact ⟨⟨X, hX⟩⟩

namespace B1Family

variable {z : Fin (q + q) → ℝ} (F : B1Family D0 q z)

/-- The exit time of the `n`-th solution from the ball of radius `n`. -/
def e (n : ℕ) : Ωq q → WithTop ℝ≥0 := exitTime (F.X n) n

/-- The flat image of the `n`-th solution. -/
def Yf (n : ℕ) (t : ℝ≥0) (ω : Ωq q) : Fin (q + q) → ℝ := chartQ q (F.X n t ω)

theorem continuous_Yf (n : ℕ) (ω : Ωq q) : Continuous fun t => F.Yf n t ω :=
  contDiff_chartQ.continuous.comp ((F.strong n).continuous ω)

theorem Yf_zero (hz : z ∈ flatChamber q) (n : ℕ) (ω : Ωq q) : F.Yf n 0 ω = z := by
  rw [Yf, (F.strong n).init ω]; exact chartQ_chartQInv hz

theorem Yf_mem (n : ℕ) (t : ℝ≥0) (ω : Ωq q) : F.Yf n t ω ∈ flatChamber q := chartQ_mem _

theorem stronglyMeasurable_Yf (n : ℕ) (t : ℝ≥0) : StronglyMeasurable[𝓖q q t] (F.Yf n t) :=
  contDiff_chartQ.continuous.comp_stronglyMeasurable ((F.strong n).sol.1.adapted t)

/-- Radius consistency, almost surely for all pairs `n ≤ m`. -/
theorem ae_consistent (hD0 : 0 < D0) : ∀ᵐ ω ∂Pq q, ∀ n m : ℕ, n ≤ m → F.e n ω ≤ F.e m ω ∧
    ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ F.e n ω → F.X n t ω = F.X m t ω := by
  rw [ae_all_iff]; intro n
  rw [ae_all_iff]; intro m
  by_cases hnm : n ≤ m
  · filter_upwards [(F.strong n).ae_consistent (locallyLipschitz_b1Drift hD0)
      (locallyLipschitz_b1Sigma hD0) (Nat.cast_le.2 hnm) (F.strong m)] with ω hω _
    exact ⟨hω.2.1, hω.2.2⟩
  · exact Eventually.of_forall fun ω h => absurd h hnm

/-- **The flat paths are continuous semimartingales** with the dual characteristics switched
off after the exit time. -/
theorem isCSM_Yf (hD0 : 0 < D0) (n : ℕ) :
    IsContinuousSemimartingale (Pq q) (𝓖q q) (F.Yf n)
      (fun t ω => switchOff (F.e n) (fun t ω => flatDrift D0 q (F.Yf n t ω)) t ω)
      (fun t ω => switchOff (F.e n) (fun t ω => flatDiff D0 q (F.Yf n t ω)) t ω) := by
  have hφ : ContDiff ℝ 2 fun p : ℝ × (Fin (q + q) → ℝ) => chartQ q p.2 :=
    (contDiff_chartQ.of_le (by simp)).comp contDiff_snd
  have hX := (F.strong n).sol.1
  have hY := ItoNative.itoFormulaFor_native (κ := Fin (q + q)) (μ := μ₁)
    (E := Fin (q + q) → ℝ) (F := Fin (q + q) → ℝ) _ _ _ hX _ hφ
  have H := hY.isContinuousSemimartingale
  have hd : ∀ w : Fin (q + q) → ℝ, DifferentiableAt ℝ (chartQ q) w := fun w =>
    contDiff_chartQ.differentiable (by simp) w
  have hc : ∀ w : Fin (q + q) → ℝ, ContDiffAt ℝ 2 (chartQ q) w := fun w =>
    (contDiff_chartQ.of_le (by simp)).contDiffAt
  have e1 : (fun (t : ℝ≥0) (ω : Ωq q) =>
      timeDeriv (fun p : ℝ × (Fin (q + q) → ℝ) => chartQ q p.2) ((t : ℝ), F.X n t ω) +
      spaceDeriv (fun p : ℝ × (Fin (q + q) → ℝ) => chartQ q p.2) ((t : ℝ), F.X n t ω)
        (switchOff (exitTime (F.X n) n) (fun t ω => b1Drift D0 q (F.X n t ω)) t ω) +
      (1 / 2 : ℝ) • ∑ a, spaceDeriv2 (fun p : ℝ × (Fin (q + q) → ℝ) => chartQ q p.2)
        ((t : ℝ), F.X n t ω)
        (switchOff (exitTime (F.X n) n) (fun t ω => b1Sigma D0 q a (F.X n t ω)) t ω)
        (switchOff (exitTime (F.X n) n) (fun t ω => b1Sigma D0 q a (F.X n t ω)) t ω)) =
      fun t ω => switchOff (F.e n) (fun t ω => flatDrift D0 q (F.Yf n t ω)) t ω := by
    funext t ω
    simp only [timeDeriv, spaceDeriv, spaceDeriv2, fderiv_comp_snd_time (hd _),
      fderiv_comp_snd_apply (hd _), fderiv_fderiv_comp_snd_apply (hc _), zero_add]
    unfold switchOff B1Family.e B1Family.Yf
    split_ifs with h
    · exact chart_drift_eq _ _ (hinv_chartQ _)
    · simp
  have e2 : (fun (t : ℝ≥0) (ω : Ωq q) => Matrix.of fun i j => ∑ a,
      spaceDeriv (fun p : ℝ × (Fin (q + q) → ℝ) => chartQ q p.2) ((t : ℝ), F.X n t ω)
        (switchOff (exitTime (F.X n) n) (fun t ω => b1Sigma D0 q a (F.X n t ω)) t ω) i *
      spaceDeriv (fun p : ℝ × (Fin (q + q) → ℝ) => chartQ q p.2) ((t : ℝ), F.X n t ω)
        (switchOff (exitTime (F.X n) n) (fun t ω => b1Sigma D0 q a (F.X n t ω)) t ω) j) =
      fun t ω => switchOff (F.e n) (fun t ω => flatDiff D0 q (F.Yf n t ω)) t ω := by
    funext t ω
    simp only [spaceDeriv, fderiv_comp_snd_apply (hd _)]
    unfold switchOff B1Family.e B1Family.Yf
    split_ifs with h
    · simp only [b1Sigma, chart_sigma_eq _ (hinv_chartQ _)]
      exact flatSigma_cov hD0 (chartQ_mem _)
    · ext i j; simp
  rw [e1, e2] at H
  exact H

theorem exitTimeFrom_le_e {n : ℕ} {W : Set (Fin (q + q) → ℝ)}
    (hW : W ⊆ chartQ q '' Metric.ball 0 n) (ω : Ωq q) :
    exitTimeFrom W (F.Yf n) ω ≤ F.e n ω := by
  refine le_iInf₂ fun t ht => iInf₂_le t fun hmem => ?_
  obtain ⟨w, hw, he⟩ := hW hmem
  have := chartQ_injective he
  rw [this, Metric.mem_ball, dist_zero_right] at hw
  exact absurd ht (not_le.2 hw)

/-- **The flat paths solve the dual martingale problem** in `chartQ '' ball 0 n`. -/
theorem isMPSolutionOn_Yf (hD0 : 0 < D0) (n : ℕ) :
    IsMPSolutionOn (Pq q) (𝓖q q) (flatDrift D0 q) (flatDiff D0 q)
      (chartQ q '' Metric.ball 0 n) (F.Yf n) := by
  have hsub : chartQ q '' Metric.ball 0 n ⊆ flatChamber q := by
    rintro _ ⟨w, -, rfl⟩; exact chartQ_mem w
  refine isMPSolutionOn_of_agree ((continuousOn_flatDrift D0).mono hsub)
    (contDiff_flatDiff D0).continuous.continuousOn (F.isCSM_Yf hD0 n) fun W hW ω s hs => ?_
  have hle : (s : WithTop ℝ≥0) ≤ F.e n ω :=
    hs.trans (F.exitTimeFrom_le_e (subset_closure.trans hW.2.2) ω)
  simp only [switchOff, B1Family.e] at hle ⊢
  exact ⟨ite_eq_left hle, ite_eq_left hle⟩

/-- **The comparison solution of the local Doob identity**: for every interior domain `W` of the
chamber, some `Yf n` solves the flat dual problem in `W`. -/
theorem exists_isMPSolutionOn_Yf (hD0 : 0 < D0) {W : Set (Fin (q + q) → ℝ)}
    (hW : IsInteriorDomain W (flatChamber q)) : ∃ n : ℕ,
    IsMPSolutionOn (Pq q) (𝓖q q) (flatDrift D0 q) (flatDiff D0 q) W (F.Yf n) := by
  obtain ⟨n, hn⟩ := exists_ball_superset hW.2.1 hW.2.2
  exact ⟨n, isMPSolutionOn_mono (F.isMPSolutionOn_Yf hD0 n) (subset_closure.trans hn)⟩

end B1Family

end BlockBand.Transmission.Dual.G
