module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Main
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Itô formula for martingale-problem solutions in every universe

`MartingaleProblemItoU.{u} d` is the body of `MartingaleProblemIto d` with the sample space in
`Type u` instead of `Type`; the original statement is its universe-0 instance
(`martingaleProblemItoU_zero_iff`, `Iff.rfl`). It is proved by the unchanged proof of
`Semimartingale.martingaleProblemIto_holds` (all its lemmas are universe-polymorphic), as for
`SemimartingaleItoFormulaU`.

Why not `ULift`: `ULift.{v} Ω : Type (max u v)` only raises the universe, so it cannot bring a
sample space `Ω : Type u` (as in `GramMartingaleProblemUniqueness`, or the driver
space `DriverSample S κ` with `S : Type*`) down to `Type`; and a transfer to a canonical path
space fails for the product σ-algebra on `ℝ≥0 → ℝ^d` (the set of continuous paths contains no
non-empty measurable set, so `∀ᵐ` path continuity is not inherited by the law).
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

universe u

/-- The body of `MartingaleProblemIto` with `Ω : Type u`. -/
def MartingaleProblemItoU (d : ℕ) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (b : (Fin d → ℝ) → Fin d → ℝ) (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (U : Set (Fin d → ℝ)), IsOpen U → ContinuousOn b U → ContinuousOn a U →
  ∀ Y : ℝ≥0 → Ω → Fin d → ℝ, IsMPSolutionOn Q 𝓖 b a U Y →
  ∀ φ : (Fin d → ℝ) → ℝ, ContDiffOn ℝ 2 φ U →
  ∀ W, IsInteriorDomain W U →
    ∃ Mφ : ℝ≥0 → Ω → ℝ, Martingale Mφ 𝓖 Q ∧ ∀ t,
      Mφ t =ᵐ[Q] stoppedProcess (fun t ω => φ (Y t ω) - φ (Y 0 ω) -
        ∫ s in Ioc (0 : ℝ) t, mpGenerator b a φ (Y s.toNNReal ω)) (exitTimeFrom W Y) t

/-- `MartingaleProblemIto` is the universe-0 instance. -/
theorem martingaleProblemItoU_zero_iff (d : ℕ) :
    MartingaleProblemItoU.{0} d ↔ MartingaleProblemIto d := Iff.rfl

/-- **The Itô formula for martingale-problem solutions in every universe** (the proof of
`martingaleProblemIto_holds`, in an arbitrary universe). -/
theorem martingaleProblemItoU_holds (d : ℕ) : MartingaleProblemItoU.{u} d := by
  intro Ω _ Q _ 𝓖 b a U hU hb ha Y hY φ hφ W hW
  obtain ⟨hWo, hWc, hWU⟩ := hW
  set τ := exitTimeFrom W Y with hτ
  have hX0 : ∀ t ω, Y 0 ω ∉ W → stoppedProcess (fun t ω => φ (Y t ω) - φ (Y 0 ω) -
      ∫ s in Ioc (0 : ℝ) t, mpGenerator b a φ (Y s.toNNReal ω)) τ t ω = 0 := by
    intro t ω h
    rw [stoppedProcess_eq_stopTime, hτ, exitTimeFrom_eq_zero h, stopTime_of_eq_zero]
    simp
  rcases W.eq_empty_or_nonempty with hWe | ⟨y₀, hy₀⟩
  · refine ⟨fun _ _ => 0, martingale_const 𝓖 Q 0, fun t => ae_of_all _ fun ω => ?_⟩
    exact (hX0 t ω (by rw [hWe]; exact notMem_empty _)).symm
  classical
  -- data
  set G : Set Ω := {ω | Y 0 ω ∈ W} with hGdef
  have hG : MeasurableSet[𝓖 0] G := (hY.adapted 0).measurable hWo.measurableSet
  set K := closure W
  have hKU : K ⊆ U := hWU
  set Zs : ℝ≥0 → Ω → Fin d → ℝ := fun t ω => Y (stopTime (τ ω) t) ω with hZs
  set Z : ℝ≥0 → Ω → Fin d → ℝ := fun t ω => if Y 0 ω ∈ W then Zs t ω else y₀ with hZ
  set β : ℝ≥0 → Ω → Fin d → ℝ := fun t ω => if Y 0 ω ∈ W then W.indicator b (Z t ω) else 0
  set a' : (Fin d → ℝ) → Fin d → Fin d → ℝ := fun z i j => a z i j with ha'
  set α : ℝ≥0 → Ω → Fin d → Fin d → ℝ := fun t ω =>
    if Y 0 ω ∈ W then W.indicator a' (Z t ω) else 0
  have hWd : IsInteriorDomain W U := ⟨hWo, hWc, hWU⟩
  choose Nd hNd hNdeq using hY.drift W hWd
  choose Nb hNb hNbeq using hY.bracket W hWd
  set N : Fin d → ℝ≥0 → Ω → ℝ := fun i t => G.indicator (Nd i t)
  set B : Fin d → Fin d → ℝ≥0 → Ω → ℝ := fun i j t => G.indicator (Nb i j t)
  -- bounds on the coefficients
  obtain ⟨Cb, hCb⟩ := hWc.exists_bound_of_continuousOn (f := b) (hb.mono hKU)
  have hent : ∀ i j, ContinuousOn (fun z => a z i j) U := fun i j => by
    have : Continuous fun M : Matrix (Fin d) (Fin d) ℝ => M i j :=
      (continuous_apply j).comp (continuous_apply i)
    exact this.comp_continuousOn ha
  have hCa : ∀ i j, ∃ C, ∀ z ∈ K, ‖a z i j‖ ≤ C := fun i j =>
    hWc.exists_bound_of_continuousOn (f := fun z => a z i j) ((hent i j).mono hKU)
  choose Ca hCa using hCa
  set Cα : ℝ := ∑ i, ∑ j, |Ca i j|
  have hZ0 : ∀ ω, Y 0 ω ∈ W → Z 0 ω = Y 0 ω := fun ω h => by
    simp only [hZ, h, ↓reduceIte, hZs, stopTime_zero]
  -- the time change on good paths
  have tc : ∀ ω, Continuous (fun t => Y t ω) → Y 0 ω ∈ W → ∀ (g : (Fin d → ℝ) → ℝ) t,
      ∫ v in Ioc (0 : ℝ) (stopTime (τ ω) t), g (Y v.toNNReal ω) =
        ∫ v in Ioc (0 : ℝ) t, W.indicator g (Z v.toNNReal ω) := by
    intro ω hω h0 g t
    simp only [hZ, h0, ↓reduceIte, hZs]
    exact setIntegral_stop_eq hWo hω g t
  have H : SchemeHyp Q 𝓖 K Z β α N B Cb Cα := by
    refine ⟨hWc, ?_, ?_, fun t => ?_, fun t ω i => ?_, fun t ω i j => ?_, ?_, ?_,
      fun i => martingale_indicator_zero (hNd i) hG, fun i t => ?_,
      fun i j => martingale_indicator_zero (hNb i j) hG, fun i j t => ?_⟩
    · filter_upwards [hY.continuous] with ω hω t
      by_cases h0 : Y 0 ω ∈ W
      · simp only [hZ, h0, ↓reduceIte, hZs]; exact stop_mem_closure hWo hω h0 t
      · simp only [hZ, h0, ↓reduceIte]; exact subset_closure hy₀
    · filter_upwards [hY.continuous] with ω hω
      by_cases h0 : Y 0 ω ∈ W
      · simp only [hZ, h0, ↓reduceIte, hZs]; exact hω.comp (continuous_stopTime _)
      · simp only [hZ, h0, ↓reduceIte]; exact continuous_const
    · have hs := aesm_stoppedProcess_exit (𝓖 := 𝓖) (Q := Q) hY.adapted hY.continuous hWo t
      refine ⟨G.piecewise (hs.mk _) (fun _ => y₀), (hs.stronglyMeasurable_mk).piecewise
        (𝓖.mono (zero_le : (0 : ℝ≥0) ≤ t) G hG) stronglyMeasurable_const, ?_⟩
      filter_upwards [hs.ae_eq_mk] with ω hω
      by_cases h0 : Y 0 ω ∈ W
      · have hω0 : ω ∈ G := h0
        simp only [Set.piecewise, hω0, ↓reduceIte, hZ, h0]
        exact hω
      · have hω0 : ω ∉ G := h0
        simp only [Set.piecewise, hω0, ↓reduceIte, hZ, h0]
    · simp only [β]
      split_ifs with h0
      · rw [indicator_apply_pi]
        by_cases hz : Z t ω ∈ W
        · rw [Set.indicator_of_mem hz]
          exact (le_of_eq (Real.norm_eq_abs _).symm).trans ((norm_le_pi_norm _ i).trans
            (hCb _ (subset_closure hz)))
        · rw [Set.indicator_of_notMem hz, abs_zero]
          exact (norm_nonneg _).trans (hCb y₀ (subset_closure hy₀))
      · simp only [Pi.zero_apply, abs_zero]
        exact (norm_nonneg _).trans (hCb y₀ (subset_closure hy₀))
    · have hCα0 : 0 ≤ Cα := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hle : ∀ z ∈ K, |a z i j| ≤ Cα := fun z hz => by
        refine ((le_of_eq (Real.norm_eq_abs _).symm).trans ((hCa i j z hz).trans
          (le_abs_self _))).trans ?_
        refine (Finset.single_le_sum (f := fun j => |Ca i j|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ j)).trans ?_
        exact Finset.single_le_sum (f := fun i => ∑ j, |Ca i j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
      simp only [α]
      split_ifs with h0
      · rw [indicator_apply_pi2]
        by_cases hz : Z t ω ∈ W
        · rw [Set.indicator_of_mem hz]; exact hle _ (subset_closure hz)
        · rw [Set.indicator_of_notMem hz, abs_zero]; exact hCα0
      · simp only [Pi.zero_apply, abs_zero]; exact hCα0
    · filter_upwards [hY.continuous] with ω hω i
      simp only [β]
      split_ifs with h0
      · have hp : Continuous fun u : ℝ => Z u.toNNReal ω := by
          simp only [hZ, h0, ↓reduceIte, hZs]
          exact (hω.comp (continuous_stopTime _)).comp continuous_real_toNNReal
        simp_rw [indicator_apply_pi]
        exact ((measurable_indicator_coord hWo (subset_closure.trans hWU) hb i).comp
          hp.measurable).aestronglyMeasurable
      · exact aestronglyMeasurable_const
    · filter_upwards [hY.continuous] with ω hω i j
      simp only [α]
      split_ifs with h0
      · have hp : Continuous fun u : ℝ => Z u.toNNReal ω := by
          simp only [hZ, h0, ↓reduceIte, hZs]
          exact (hω.comp (continuous_stopTime _)).comp continuous_real_toNNReal
        simp_rw [indicator_apply_pi2]
        have hm : Measurable (W.indicator fun z => a' z i j) := by
          classical
          have : W.indicator (fun z => a' z i j) = W.piecewise (fun z => a z i j) (fun _ => 0) := by
            funext z; by_cases h : z ∈ W <;> simp [h, a']
          rw [this]
          exact ((hent i j).mono (subset_closure.trans hWU)).measurable_piecewise
            continuousOn_const hWo.measurableSet
        exact (hm.comp hp.measurable).aestronglyMeasurable
      · exact aestronglyMeasurable_const
    · filter_upwards [hNdeq i t, hY.continuous] with ω h1 hω
      by_cases h0 : Y 0 ω ∈ W
      · have hω0 : ω ∈ G := h0
        simp only [N, Set.indicator_of_mem hω0, h1, stoppedProcess_eq_stopTime, mpCompensated,
          drI]
        rw [tc ω hω h0 (fun z => b z i) t, hZ0 ω h0]
        have : ∀ v : ℝ, β v.toNNReal ω i = W.indicator (fun z => b z i) (Z v.toNNReal ω) :=
          fun v => by simp only [β, h0, ↓reduceIte, indicator_apply_pi]
        simp only [this, hZ, h0, ↓reduceIte, hZs]
        rfl
      · have hω0 : ω ∉ G := h0
        simp [N, Set.indicator_of_notMem hω0, hZ, h0, drI, β]
    · filter_upwards [hNbeq i j t, hNdeq i t, hNdeq j t, hY.continuous] with ω h1 h2 h3 hω
      by_cases h0 : Y 0 ω ∈ W
      · have hω0 : ω ∈ G := h0
        simp only [B, N, Set.indicator_of_mem hω0, h1, h2, h3, stoppedProcess_eq_stopTime, difJ]
        rw [tc ω hω h0 (fun z => a z i j) t]
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioc fun v _ => ?_
        simp only [α, h0, ↓reduceIte]
        by_cases hz : Z v.toNNReal ω ∈ W <;> simp [hz, a']
      · have hω0 : ω ∉ G := h0
        simp [B, N, Set.indicator_of_notMem hω0, difJ, α, h0]
  -- apply the Taylor scheme
  obtain ⟨M, hM, hMeq⟩ := H.exists_martingale_schemeProc hU hKU hφ
  refine ⟨M, hM, fun t => ?_⟩
  filter_upwards [hMeq t, hY.continuous] with ω h1 hω
  rw [h1]
  by_cases h0 : Y 0 ω ∈ W
  · rw [stoppedProcess_eq_stopTime, tc ω hω h0 (mpGenerator b a φ) t]
    simp only [schemeProc, hZ0 ω h0]
    congr 1
    · simp only [hZ, h0, ↓reduceIte, hZs]
    · refine setIntegral_congr_fun measurableSet_Ioc fun v _ => ?_
      simp only [schemeGen, β, α, h0, ↓reduceIte]
      by_cases hz : Z v.toNNReal ω ∈ W
      · simp only [Set.indicator_of_mem hz, mpGenerator]
        rfl
      · simp [Set.indicator_of_notMem hz]
  · rw [hX0 t ω h0]
    simp [schemeProc, hZ, h0, schemeGen, β, α]

end BlockBand.SourceProcess.Stochastic.GramUniqueness
