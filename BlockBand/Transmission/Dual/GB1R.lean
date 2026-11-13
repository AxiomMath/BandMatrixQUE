module

public import BlockBand.Transmission.Dual.GDomPath
public import BlockBand.Transmission.Dual.GSeqQ

/-!
# The level-`q` dual up to exhaustion, from a random start

* `B1R D₀ q μ ξ`: strong exit-time solutions of radii `n` of the chart SDE from the
  `𝓖₀`-measurable start `chartQInv ∘ ξ`; `nonempty_b1R` (local well-posedness accepts a
  `𝓖₀`-measurable start, `measurable_start`);
* `Yf`, `e`, `isCSM_Yf`, `isMPSolutionOn_Yf`, `ae_consistent`, as for a deterministic start;
* `cpath`, `stopSeq`, `IsConsAt`, `isStopSeq_stopSeq`, `isNested_stopSeq`, `stopSeq_zero`.
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

variable {q : ℕ} {D0 : ℝ} {t₀ : ℝ≥0}
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

/-- The driver space of level `q` over the old state `S`. -/
abbrev ΩR (S : Type*) (q : ℕ) : Type _ := DriverSample S (Fin (q + q))

/-- Its law. -/
abbrev PR (q : ℕ) : Measure (ΩR S q) := driverLaw (κ := Fin (q + q)) μ

/-- Its augmented filtration. -/
abbrev 𝓖R (q : ℕ) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ΩR S q)) :=
  driverAugmented (κ := Fin (q + q)) μ

theorem measurable_prevVal {m : ℕ} (k : Fin m) : Measurable fun s : Fin m → ℝ => prevVal s k := by
  unfold prevVal; split_ifs
  · exact measurable_const
  · exact measurable_pi_apply _

theorem measurable_logGap {m : ℕ} : Measurable (logGap (q := m)) :=
  measurable_pi_iff.2 fun k => ((measurable_pi_apply k).sub (measurable_prevVal k)).log

theorem measurable_chartQInv : Measurable (chartQInv q) := by
  have h1 : Measurable fun z : Fin (q + q) → ℝ => logGap (ofFlat q z).1 :=
    measurable_logGap.comp (ofFlat q).continuous.measurable.fst
  have h2 : Measurable fun z : Fin (q + q) → ℝ => logGap fun j => yInv ((ofFlat q z).2 j) := by
    refine measurable_logGap.comp (measurable_pi_iff.2 fun j => ?_)
    exact ((measurable_const.sub ((measurable_pi_apply j).comp
      (ofFlat q).continuous.measurable.snd)).log).neg
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [chartQInv, Fin.append_left]; exact (measurable_pi_apply j).comp h1
  · simp only [chartQInv, Fin.append_right]; exact (measurable_pi_apply j).comp h2

omit [IsProbabilityMeasure μ] in
/-- A function of the old state is `𝓖R 0`-measurable. -/
theorem measurable_fst_zero {E : Type*} [MeasurableSpace E] {g : S → E} (hg : Measurable g) :
    Measurable[𝓖R μ q 0] fun x : ΩR S q => g x.1 := by
  have h : Measurable[BlockBand.SourceProcess.commonWienerFiltration S (Fin (q + q)) 0] fun x : ΩR S q => x.1 :=
    (comap_measurable (m := inferInstance)
      (fun x : ΩR S q => (x.1, BlockBand.SourceProcess.commonWienerPast 0 x.2))).fst
  exact (hg.comp h).mono (le_augmentedFiltration _ _ 0) le_rfl

variable {μ}

/-- A family of strong exit-time solutions of radii `n` of the chart SDE from `chartQInv ∘ ξ`. -/
structure B1R (D0 : ℝ) (q : ℕ) (μ : Measure S) [IsProbabilityMeasure μ]
    (ξ : S → Fin (q + q) → ℝ) where
  X : ℕ → ℝ≥0 → ΩR S q → Fin (q + q) → ℝ
  strong : ∀ n : ℕ, IsStrongExitSolution μ (b1Drift D0 q) (b1Sigma D0 q)
    (fun x => chartQInv q (ξ x.1)) n (X n)

theorem nonempty_b1R (hD0 : 0 < D0) {ξ : S → Fin (q + q) → ℝ} (hξ : Measurable ξ) :
    Nonempty (B1R D0 q μ ξ) := by
  have hs : StronglyMeasurable[𝓖R μ q 0] fun x : ΩR S q => chartQInv q (ξ x.1) :=
    (measurable_fst_zero μ (measurable_chartQInv.comp hξ)).stronglyMeasurable
  have h : ∀ n : ℕ, ∃ X, IsStrongExitSolution μ (b1Drift D0 q) (b1Sigma D0 q)
      (fun x => chartQInv q (ξ x.1)) n X := fun n =>
    exists_solutionUntil_exitTime_strong (locallyLipschitz_b1Drift hD0)
      (locallyLipschitz_b1Sigma hD0) hs n
  choose X hX using h
  exact ⟨⟨X, hX⟩⟩

namespace B1R

variable {ξ : S → Fin (q + q) → ℝ} (F : B1R D0 q μ ξ)

/-- The exit time of the `n`-th solution from the ball of radius `n`. -/
def e (n : ℕ) : ΩR S q → WithTop ℝ≥0 := exitTime (F.X n) n

/-- The flat image of the `n`-th solution. -/
def Yf (n : ℕ) (t : ℝ≥0) (ω : ΩR S q) : Fin (q + q) → ℝ := chartQ q (F.X n t ω)

theorem continuous_Yf (n : ℕ) (ω : ΩR S q) : Continuous fun t => F.Yf n t ω :=
  contDiff_chartQ.continuous.comp ((F.strong n).continuous ω)

theorem Yf_zero (hξc : ∀ s, ξ s ∈ flatChamber q) (n : ℕ) (ω : ΩR S q) : F.Yf n 0 ω = ξ ω.1 := by
  rw [Yf, (F.strong n).init ω]; exact chartQ_chartQInv (hξc _)

theorem Yf_mem (n : ℕ) (t : ℝ≥0) (ω : ΩR S q) : F.Yf n t ω ∈ flatChamber q := chartQ_mem _

theorem stronglyMeasurable_Yf (n : ℕ) (t : ℝ≥0) : StronglyMeasurable[𝓖R μ q t] (F.Yf n t) :=
  contDiff_chartQ.continuous.comp_stronglyMeasurable ((F.strong n).sol.1.adapted t)

theorem isStoppingTime_e (n : ℕ) : IsStoppingTime (𝓖R μ q) (F.e n) := (F.strong n).stopping

/-- Radius consistency, almost surely for all pairs `n ≤ m`. -/
theorem ae_consistent (hD0 : 0 < D0) : ∀ᵐ ω ∂PR μ q, ∀ n m : ℕ, n ≤ m → F.e n ω ≤ F.e m ω ∧
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
    IsContinuousSemimartingale (PR μ q) (𝓖R μ q) (F.Yf n)
      (fun t ω => switchOff (F.e n) (fun t ω => flatDrift D0 q (F.Yf n t ω)) t ω)
      (fun t ω => switchOff (F.e n) (fun t ω => flatDiff D0 q (F.Yf n t ω)) t ω) := by
  have hφ : ContDiff ℝ 2 fun p : ℝ × (Fin (q + q) → ℝ) => chartQ q p.2 :=
    (contDiff_chartQ.of_le (by simp)).comp contDiff_snd
  have hX := (F.strong n).sol.1
  have hY := ItoNative.itoFormulaFor_native (κ := Fin (q + q)) (μ := μ)
    (E := Fin (q + q) → ℝ) (F := Fin (q + q) → ℝ) _ _ _ hX _ hφ
  have H := hY.isContinuousSemimartingale
  have hd : ∀ w : Fin (q + q) → ℝ, DifferentiableAt ℝ (chartQ q) w := fun w =>
    contDiff_chartQ.differentiable (by simp) w
  have hc : ∀ w : Fin (q + q) → ℝ, ContDiffAt ℝ 2 (chartQ q) w := fun w =>
    (contDiff_chartQ.of_le (by simp)).contDiffAt
  have e1 : (fun (t : ℝ≥0) (ω : ΩR S q) =>
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
    unfold switchOff B1R.e B1R.Yf
    split_ifs with h
    · exact chart_drift_eq _ _ (hinv_chartQ _)
    · simp
  have e2 : (fun (t : ℝ≥0) (ω : ΩR S q) => Matrix.of fun i j => ∑ a,
      spaceDeriv (fun p : ℝ × (Fin (q + q) → ℝ) => chartQ q p.2) ((t : ℝ), F.X n t ω)
        (switchOff (exitTime (F.X n) n) (fun t ω => b1Sigma D0 q a (F.X n t ω)) t ω) i *
      spaceDeriv (fun p : ℝ × (Fin (q + q) → ℝ) => chartQ q p.2) ((t : ℝ), F.X n t ω)
        (switchOff (exitTime (F.X n) n) (fun t ω => b1Sigma D0 q a (F.X n t ω)) t ω) j) =
      fun t ω => switchOff (F.e n) (fun t ω => flatDiff D0 q (F.Yf n t ω)) t ω := by
    funext t ω
    simp only [spaceDeriv, fderiv_comp_snd_apply (hd _)]
    unfold switchOff B1R.e B1R.Yf
    split_ifs with h
    · simp only [b1Sigma, chart_sigma_eq _ (hinv_chartQ _)]
      exact flatSigma_cov hD0 (chartQ_mem _)
    · ext i j; simp
  rw [e1, e2] at H
  exact H

theorem exitTimeFrom_le_e {n : ℕ} {W : Set (Fin (q + q) → ℝ)}
    (hW : W ⊆ chartQ q '' Metric.ball 0 n) (ω : ΩR S q) :
    exitTimeFrom W (F.Yf n) ω ≤ F.e n ω := by
  refine le_iInf₂ fun t ht => iInf₂_le t fun hmem => ?_
  obtain ⟨w, hw, he⟩ := hW hmem
  have := chartQ_injective he
  rw [this, Metric.mem_ball, dist_zero_right] at hw
  exact absurd ht (not_le.2 hw)

/-- **The flat paths solve the dual martingale problem** in `chartQ '' ball 0 n`. -/
theorem isMPSolutionOn_Yf (hD0 : 0 < D0) (n : ℕ) :
    IsMPSolutionOn (PR μ q) (𝓖R μ q) (flatDrift D0 q) (flatDiff D0 q)
      (chartQ q '' Metric.ball 0 n) (F.Yf n) := by
  have hsub : chartQ q '' Metric.ball 0 n ⊆ flatChamber q := by
    rintro _ ⟨w, -, rfl⟩; exact chartQ_mem w
  refine isMPSolutionOn_of_agree ((continuousOn_flatDrift D0).mono hsub)
    (contDiff_flatDiff D0).continuous.continuousOn (F.isCSM_Yf hD0 n) fun W hW ω s hs => ?_
  have hle : (s : WithTop ℝ≥0) ≤ F.e n ω :=
    hs.trans (F.exitTimeFrom_le_e (subset_closure.trans hW.2.2) ω)
  simp only [switchOff, B1R.e] at hle ⊢
  exact ⟨ite_eq_left hle, ite_eq_left hle⟩

/-- The `m`-th flat path as a continuous path. -/
def cpath (m : ℕ) (ω : ΩR S q) : CPath (q + q) := ⟨fun t => F.Yf m t ω, F.continuous_Yf m ω⟩

theorem measurable_Yf' (m : ℕ) (t : ℝ≥0) : Measurable (F.Yf m t) :=
  (F.stronglyMeasurable_Yf m t).measurable.mono ((𝓖R μ q).le t) le_rfl

theorem measurable_cpath (m : ℕ) : Measurable (F.cpath m) :=
  Measurable.subtype_mk (measurable_pi_iff.2 fun t => F.measurable_Yf' m t)

/-- The stop sequence with radii `r`. -/
def stopSeq (W : ℕ → Set (Fin (q + q) → ℝ)) (t₀ : ℝ≥0) (r : ℕ → ℕ) (ω : ΩR S q) :
    ℕ → CPath (q + q) := fun n => pstop (W n) t₀ (F.cpath (r n) ω)

theorem measurable_stopSeq {W : ℕ → Set (Fin (q + q) → ℝ)} (hW : ∀ n, IsOpen (W n))
    (r : ℕ → ℕ) : Measurable (F.stopSeq W t₀ r) :=
  measurable_pi_iff.2 fun n => (measurable_pstop (hW n) t₀).comp (F.measurable_cpath _)

/-- Radius consistency at a fixed `ω`. -/
def IsConsAt (ω : ΩR S q) : Prop :=
  ∀ n m : ℕ, n ≤ m → F.e n ω ≤ F.e m ω ∧
    ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ F.e n ω → F.X n t ω = F.X m t ω

theorem ae_isConsAt (hD0 : 0 < D0) : ∀ᵐ ω ∂PR μ q, F.IsConsAt ω := F.ae_consistent hD0

theorem Yf_eq_of_le {ω : ΩR S q} (hc : F.IsConsAt ω) {m m' : ℕ} (h : m ≤ m') {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ F.e m ω) : F.Yf m' t ω = F.Yf m t ω := by
  simp only [Yf]; rw [(hc m m' h).2 t ht]

theorem pexit_cpath_le {m : ℕ} {W : Set (Fin (q + q) → ℝ)}
    (hW : W ⊆ chartQ q '' Metric.ball 0 m) (ω : ΩR S q) : pexit W (F.cpath m ω) ≤ F.e m ω :=
  F.exitTimeFrom_le_e hW ω

/-- **The stop sequence of a random-start family is a stop sequence** (monotone large
radii). -/
theorem isStopSeq_stopSeq (hD0 : 0 < D0) {W : ℕ → Set (Fin (q + q) → ℝ)}
    (hW : ∀ n, IsOpen (W n)) (hmono : Monotone W) {r : ℕ → ℕ} (hr : Monotone r)
    (hball : ∀ n, W n ⊆ chartQ q '' Metric.ball 0 (r n)) :
    IsStopSeq (PR μ q) W t₀ (F.stopSeq W t₀ r) := by
  intro k n hkn
  filter_upwards [F.ae_isConsAt hD0] with ω hc
  show pstop (W k) t₀ (F.cpath (r k) ω) = pstop (W k) t₀ (pstop (W n) t₀ (F.cpath (r n) ω))
  rw [pstop_pstop (hW k) (hmono hkn)]
  refine (pstop_congr (hW k) t₀ fun u hu => ?_).symm
  exact F.Yf_eq_of_le hc (hr hkn)
    ((hu.trans (min_le_left _ _)).trans (F.pexit_cpath_le (hball k) ω))

theorem isNested_stopSeq {W : ℕ → Set (Fin (q + q) → ℝ)} (hW : ∀ n, IsOpen (W n))
    (hmono : Monotone W) {r : ℕ → ℕ} (hr : Monotone r)
    (hball : ∀ n, W n ⊆ chartQ q '' Metric.ball 0 (r n)) {ω : ΩR S q} (hc : F.IsConsAt ω) :
    IsNested W t₀ (F.stopSeq W t₀ r ω) := by
  intro k n hkn
  show pstop (W k) t₀ (F.cpath (r k) ω) = pstop (W k) t₀ (pstop (W n) t₀ (F.cpath (r n) ω))
  rw [pstop_pstop (hW k) (hmono hkn)]
  refine (pstop_congr (hW k) t₀ fun u hu => ?_).symm
  exact F.Yf_eq_of_le hc (hr hkn)
    ((hu.trans (min_le_left _ _)).trans (F.pexit_cpath_le (hball k) ω))

theorem stopSeq_zero (hξc : ∀ s, ξ s ∈ flatChamber q) (W : ℕ → Set (Fin (q + q) → ℝ))
    (r : ℕ → ℕ) (ω : ΩR S q) : (F.stopSeq W t₀ r ω 0).1 0 = ξ ω.1 := by
  rw [stopSeq, pstop_apply_zero]; exact F.Yf_zero hξc _ ω

end B1R

end BlockBand.Transmission.Dual.G
