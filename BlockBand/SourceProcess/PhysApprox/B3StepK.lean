module

public import BlockBand.SourceProcess.PhysApprox.B3StepFresh
public import BlockBand.SourceProcess.PhysApprox.B3MartMax

/-!
# `KCorrStepFourAt` reduced to the closed exact update and a closed jet

* **`ClosedPastFreshLaw`** (a hypothesis): the joint law of (past at `i`, probes, phase) and the
  fresh layer under `closedLaw`. It is the statement of `closedLaw_map_past_fresh` with `b3Past`
  and `probePhaseLaw` unfolded.
* **`ClosedKStepForm Xcl`** (the closed exact update for a closed input family `Xcl`), stated as a
  hypothesis: on the domain, at every step, `Xcl` is Borel, past-determined and a.e. passive, and
  every entry with two old tags has stopped step `u*Δ(Xcl, F_j)v` a.e. with past-determined
  frames of norm `≤ C_f`.
* **`ClosedJetHalf Xcl`**, stated as a hypothesis: `E δ₀(Xcl_j)⁴ ≤ C/W²` (`L⁴` size `W^{-1/2}`)
  at the steps after the first birth. Weaker than the `C/W` jet.
* **`kStopStepFourAt_of_closed`**: `ClosedPastFreshLaw + ClosedKStepForm Xcl + ClosedJetHalf Xcl`
  and the contract hypotheses give `KStopStepFourAt`; entries with an unborn tag vanish
  (`kStopStep_eq_zero_of_unborn`). Hence **`kCorrStepFourAt_of_closed`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.ComplexSourceLaw
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W np K : ℕ}

/-!
## The per-step stopped closed `𝒦` bound and its equivalence with `KCorrStepFourAt`
-/

/-- **`KStopStepFourAt`**: at every step `n_s ≤ j < ⌊WT⌋` and every entry with no tag born at
`j`, the stopped closed `𝒦` step has `E[1_{A_j}|Δ𝒦_cl|⁴] ≤ C/W²`, uniformly. -/
def KStopStepFourAt : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, ∀ᶠ W in atTop,
      ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, ∀ ij : Fin np × Fin np,
        ¬ IsNewCoord τ W j (Sum.inr ij : CIdx K np) →
          ∫⁻ y, ‖kStopStep b E s h τ m R W j (Vs W) ij y‖ₑ ^ 4 ∂closedLaw b W np ≤
            ENNReal.ofReal (C / (W : ℝ) ^ 2)

/-- `KCorrStepFourAt ⇒ KStopStepFourAt` (`lintegral_kStopStep_at`). -/
theorem kStopStepFourAt_of_corrAt (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) (hC : KCorrStepFourAt) :
    KStopStepFourAt := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C, -, hC'⟩ := lintegral_kStopStep_at hGA hLp hSR hMT hC b E np τ m T s h K Vs hF R
  exact ⟨C, hC'⟩

/-- **`KStopStepFourAt ⇒ KCorrStepFourAt`** given the input hypotheses: the closing-correction step
is the unclosed step minus the closed step.
-/
theorem kCorrStepFourAt_of_stopAt (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) (hS : KStopStepFourAt) :
    KCorrStepFourAt := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C₁, W₁, hC₁, hU⟩ := lintegral_kUnclosedStep_le hGA hLp hSR hMT hF.1
  obtain ⟨C₂, h₂⟩ := hS b E np τ m T s h K Vs hF R
  refine ⟨8 * (C₁ + max C₂ 0), ?_⟩
  filter_upwards [h₂, eventually_ge_atTop W₁] with W hW2 hW j hj ij hnew
  have hn₁ : ⌊(W : ℝ) * τ ij.1⌋₊ ≠ j := fun h' =>
    hnew (show IsNewCoord τ W j (Sum.inr ij : CIdx K np) from Or.inl h')
  have hn₂ : ⌊(W : ℝ) * τ ij.2⌋₊ ≠ j := fun h' =>
    hnew (show IsNewCoord τ W j (Sum.inr ij : CIdx K np) from Or.inr h')
  refine (lintegral_kStopStep_le b E s h τ m R W j (Vs W) ij).2.trans ?_
  calc 8 * (∫⁻ y, ‖complexSourceK b E W (j + 1) τ m y.1 ij.1 ij.2 -
          complexSourceK b E W j τ m y.1 ij.1 ij.2‖ₑ ^ 4 ∂closedLaw b W np +
        ∫⁻ y, ‖kStopStep b E s h τ m R W j (Vs W) ij y‖ₑ ^ 4 ∂closedLaw b W np)
      ≤ 8 * (ENNReal.ofReal (C₁ / (W : ℝ) ^ 2) + ENNReal.ofReal (max C₂ 0 / (W : ℝ) ^ 2)) := by
        gcongr
        · exact hU W hW j (succ_le_mul_of_lt_floor (Finset.mem_Ico.1 hj).2) ij hn₁ hn₂
        · exact (hW2 j hj ij hnew).trans (ENNReal.ofReal_le_ofReal
            (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)))
    _ = ENNReal.ofReal (8 * (C₁ + max C₂ 0) / (W : ℝ) ^ 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← add_div,
          show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
          mul_div_assoc]

/-!
## The joint law and the closed estimates
-/

/-- **`ClosedPastFreshLaw`** (the statement of `closedLaw_map_past_fresh`, with `b3Past` and
`probePhaseLaw` unfolded): under `closedLaw`, `((pastCoords W i, probes, θ), freshSample W i)` has
law `(pastLaw ⊗ probes ⊗ phase) ⊗ freshLaw`. -/
def ClosedPastFreshLaw : Prop :=
  ∀ (b : ℝ) (W np i : ℕ),
    (closedLaw b W np).map (fun y : ProbedPath W np × ℝ =>
        ((pastCoords W i y.1.1, (y.1.2, y.2)), freshSample W i y.1.1)) =
      ((pastLaw W i b).prod
        ((Measure.pi fun _ : Fin np => circularVectorLaw (Fin W)).prod phaseLaw)).prod
        (freshLaw W b)

/-- A closed input family: for the parameters and the step `j`, the passive one-port input of
the closed path at length `j` (the true one is the near-end Schur complement of the far-closed
path). -/
abbrev ClosedInputFam : Type :=
  (b E s h : ℝ) → {np : ℕ} → (τ m : Fin np → ℝ) → (W j : ℕ) → ProbedPath W np × ℝ →
    Matrix (Fin W) (Fin W) ℂ

/-- **`ClosedKStepForm Xcl`: the closed exact update** (for the far-closed path). On the domain,
for every trace level `R` there is a frame bound `C_f` such that eventually, at every step
`n_s ≤ j < ⌊WT⌋`: `Xcl_j` is Borel, unchanged by `b3Ext W j` and a.e. passive; and every entry
`ik` with both tags old has, a.e., `1_{A_j}(Δ𝒦_cl)_{ik} = u*Δ(Xcl_j, F_j)v` for Borel,
`b3Ext W j`-invariant `u, v` of norm `≤ C_f` (on `A_j`: `u = ι*V_cl e_i`, `v = ι*𝕊_cl V_cl e_k`,
`‖u‖², ‖v‖² ≤ R`). -/
def ClosedKStepForm (Xcl : ClosedInputFam) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ Cf : ℝ, ∀ᶠ W in atTop,
      ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
        Measurable (Xcl b E s h τ m W j) ∧
        (∀ y, Xcl b E s h τ m W j (b3Ext W j y) = Xcl b E s h τ m W j y) ∧
        (∀ᵐ y ∂closedLaw b W np, (passiveY (Xcl b E s h τ m W j y)).PosSemidef) ∧
        ∀ ij : Fin np × Fin np, ⌊(W : ℝ) * τ ij.1⌋₊ < j → ⌊(W : ℝ) * τ ij.2⌋₊ < j →
          ∃ u v : ProbedPath W np × ℝ → Fin W → ℂ, Measurable u ∧ Measurable v ∧
            (∀ y, u (b3Ext W j y) = u y) ∧ (∀ y, v (b3Ext W j y) = v y) ∧
            (∀ y, vecNorm (u y) ≤ Cf) ∧ (∀ y, vecNorm (v y) ≤ Cf) ∧
            ∀ᵐ y ∂closedLaw b W np, kStopStep b E s h τ m R W j (Vs W) ij y =
              bilinear (u y) (freshDelta b E (Xcl b E s h τ m W j y) (freshSample W j y.1.1))
                (v y)

/-- **`ClosedJetHalf Xcl`: the closed jet at the `W^{-1/2}` scale** (the jets are stationary at
the `W⁻¹` scale; only `W^{-1/2}` in `L⁴` is asked): at every step `n_s ≤ j < ⌊WT⌋` after the first
birth, `E δ₀(Xcl_j)⁴ ≤ C/W²`. -/
def ClosedJetHalf (Xcl : ClosedInputFam) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∃ Cδ : ℝ, ∀ᶠ W in atTop,
      ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, (∃ i, ⌊(W : ℝ) * τ i⌋₊ < j) →
        ∫⁻ y, ENNReal.ofReal (jetDistance0 b E (Xcl b E s h τ m W j y) ^ 4)
          ∂closedLaw b W np ≤ ENNReal.ofReal (Cδ / (W : ℝ) ^ 2)

/-!
## One closed fresh step
-/

theorem step_continuous_passiveY : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => passiveY M := by
  have h : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => M - Mᴴ :=
    continuous_id.sub continuous_id.matrix_conjTranspose
  unfold passiveY BlockBand.Transmission.matrixImaginaryPart
  exact (h.const_smul (-Complex.I / 2 : ℂ)).neg

theorem step_measurableSet_passive :
    MeasurableSet {M : Matrix (Fin W) (Fin W) ℂ | (passiveY M).PosSemidef} :=
  step_continuous_passiveY.measurable Matrix.posSemidef_is_closed.measurableSet

/-- **The fourth moment of one closed fresh step** (from the contract hypotheses and
`ClosedPastFreshLaw`): for Borel `b3Ext W j`-invariant frames bounded by `C_f` and an a.e. passive
invariant input `X`, `E|u*Δ(X, F_j)v|⁴ ≤ E[C C_f⁸(δ₀(X) + W^{-1/2})⁴]` under `closedLaw`. -/
theorem lintegral_closed_bilinear_four_le (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hL : ClosedPastFreshLaw) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ (np j : ℕ)
      (u v : ProbedPath W np × ℝ → Fin W → ℂ) (X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ)
      (Cf : ℝ), Measurable u → Measurable v → Measurable X → 0 ≤ Cf →
      (∀ y, u (b3Ext W j y) = u y) → (∀ y, v (b3Ext W j y) = v y) →
      (∀ y, X (b3Ext W j y) = X y) → (∀ y, vecNorm (u y) ≤ Cf) → (∀ y, vecNorm (v y) ≤ Cf) →
      (∀ᵐ y ∂closedLaw b W np, (passiveY (X y)).PosSemidef) →
        ∫⁻ y, ‖bilinear (u y) (freshDelta b E (X y) (freshSample W j y.1.1)) (v y)‖ₑ ^ 4
            ∂closedLaw b W np ≤
          ∫⁻ y, ENNReal.ofReal (C * Cf ^ 8 *
            (jetDistance0 b E (X y) + (Real.sqrt W)⁻¹) ^ 4) ∂closedLaw b W np := by
  obtain ⟨C, W₀, hC, H⟩ := StepFresh.lintegral_bilinear_freshDelta_four_le hGA hLp hb0 hb hE1 hE2
  refine ⟨C, W₀, hC, fun W hW np j u v X Cf hu hv hX hCf hu' hv' hX' hub hvb hpas => ?_⟩
  set μ := closedLaw b W np
  set μP := (pastLaw W j b).prod
    ((Measure.pi fun _ : Fin np => circularVectorLaw (Fin W)).prod phaseLaw)
  set π : ProbedPath W np × ℝ → PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) :=
    fun y => (pastCoords W j y.1.1, (y.1.2, y.2))
  set r : PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) → ProbedPath W np × ℝ :=
    fun p => ((extPast W j p.1, p.2.1), p.2.2)
  have hπ : Measurable π := measurable_b3Sigma_map W j np
  have hr : Measurable r :=
    (((measurable_extPast j).comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)
  set φ : ProbedPath W np × ℝ → LayerSample W .oneBlockOnePort := fun y => freshSample W j y.1.1
  have hφ : Measurable φ := (measurable_freshSample W j).comp (measurable_fst.comp measurable_fst)
  have hmap : μ.map (fun y => (π y, φ y)) = μP.prod (freshLaw W b) := hL b W np j
  have hmapπ : μ.map π = μP := by
    have h := congrArg (fun m => m.map Prod.fst) hmap
    rw [Measure.map_map measurable_fst (hπ.prodMk hφ), Measure.map_fst_prod, measure_univ,
      one_smul] at h
    exact h
  have hrπ : ∀ y, r (π y) = b3Ext W j y := fun y => rfl
  have hpasP : ∀ᵐ p ∂μP, (passiveY (X (r p))).PosSemidef := by
    have hset : MeasurableSet {p | (passiveY (X (r p))).PosSemidef} :=
      (hX.comp hr) step_measurableSet_passive
    rw [← hmapπ, ae_map_iff hπ.aemeasurable hset]
    filter_upwards [hpas] with y hy
    rw [hrπ, hX']
    exact hy
  have hH := H W hW μ μP hπ hφ hmap (u ∘ r) (v ∘ r) (X ∘ r) Cf (hu.comp hr) (hv.comp hr)
    (hX.comp hr) hCf (fun p => hub _) (fun p => hvb _) hpasP
  have hg : Measurable fun p => ENNReal.ofReal (C * Cf ^ 8 *
      (jetDistance0 b E ((X ∘ r) p) + (Real.sqrt W)⁻¹) ^ 4) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((((measurable_jetDistance0 (W := W) b E).comp (hX.comp hr)).add measurable_const).pow_const
        4))
  calc ∫⁻ y, ‖bilinear (u y) (freshDelta b E (X y) (freshSample W j y.1.1)) (v y)‖ₑ ^ 4 ∂μ
      = ∫⁻ y, ‖bilinear ((u ∘ r) (π y)) (freshDelta b E ((X ∘ r) (π y)) (φ y))
          ((v ∘ r) (π y))‖ₑ ^ 4 ∂μ := by
        refine lintegral_congr fun y => ?_
        simp only [Function.comp_apply, hrπ, hu', hv', hX', φ]
    _ ≤ _ := hH
    _ = ∫⁻ y, ENNReal.ofReal (C * Cf ^ 8 *
          (jetDistance0 b E (X y) + (Real.sqrt W)⁻¹) ^ 4) ∂μ := by
        rw [← hmapπ, lintegral_map hg hπ]
        refine lintegral_congr fun y => ?_
        simp only [Function.comp_apply, hrπ, hX']

/-!
## Unborn entries
-/

/-- An entry with a tag unborn at length `j + 1` has a zero stopped step. -/
theorem kStopStep_eq_zero_of_unborn (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij : Fin np × Fin np)
    (hij : j + 1 ≤ ⌊(W : ℝ) * τ ij.1⌋₊ ∨ j + 1 ≤ ⌊(W : ℝ) * τ ij.2⌋₊)
    (y : ProbedPath W np × ℝ) : kStopStep b E s h τ m R W j Vs ij y = 0 := by
  have h0 : (fun y => b3ClosedKAt b E s h τ m W (j + 1) y ij.1 ij.2 -
      b3ClosedKAt b E s h τ m W j y ij.1 ij.2) = 0 := by
    funext y
    rcases hij with h1 | h2
    · rw [Birth.b3ClosedKAt_unborn_row h1 y ij.2,
        Birth.b3ClosedKAt_unborn_row (by omega : j ≤ ⌊(W : ℝ) * τ ij.1⌋₊) y ij.2, sub_self]
      rfl
    · rw [Birth.b3ClosedKAt_unborn_col h2 y ij.1,
        Birth.b3ClosedKAt_unborn_col (by omega : j ≤ ⌊(W : ℝ) * τ ij.2⌋₊) y ij.1, sub_self]
      rfl
  unfold kStopStep
  rw [h0, Set.indicator_zero']
  rfl

/-!
## The reduction
-/

/-- **`KStopStepFourAt` from the closed exact update, the closed jet and the contract
hypotheses.** -/
theorem kStopStepFourAt_of_closed (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hL : ClosedPastFreshLaw) {Xcl : ClosedInputFam} (hF : ClosedKStepForm Xcl)
    (hJ : ClosedJetHalf Xcl) : KStopStepFourAt := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨hb0, hb1, hE1, hE2, -⟩ := hD.1
  obtain ⟨C, W₀, hC, H⟩ := lintegral_closed_bilinear_four_le hGA hLp hL hb0 hb1 hE1 hE2
  obtain ⟨Cf, hFW⟩ := hF b E np τ m T s h K Vs hD R
  obtain ⟨Cδ, hJW⟩ := hJ b E np τ m T s h K Vs hD
  refine ⟨8 * C * max Cf 0 ^ 8 * (max Cδ 0 + 1), ?_⟩
  filter_upwards [hFW, hJW, eventually_ge_atTop (max W₀ 1)] with W hFj hJj hW j hj ij hnew
  have hW₀ : W₀ ≤ W := le_trans (le_max_left _ _) hW
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  obtain ⟨hXm, hXi, hXp, hform⟩ := hFj j hj
  have hn₁ : ⌊(W : ℝ) * τ ij.1⌋₊ ≠ j := fun h' =>
    hnew (show IsNewCoord τ W j (Sum.inr ij : CIdx K np) from Or.inl h')
  have hn₂ : ⌊(W : ℝ) * τ ij.2⌋₊ ≠ j := fun h' =>
    hnew (show IsNewCoord τ W j (Sum.inr ij : CIdx K np) from Or.inr h')
  by_cases h1 : ⌊(W : ℝ) * τ ij.1⌋₊ < j
  · by_cases h2 : ⌊(W : ℝ) * τ ij.2⌋₊ < j
    · obtain ⟨u, v, hu, hv, hu', hv', hub, hvb, hae⟩ := hform ij h1 h2
      rw [lintegral_congr_ae (hae.mono fun y hy => by rw [hy])]
      refine (H W hW₀ np j u v (Xcl b E s h τ m W j) (max Cf 0) hu hv hXm (le_max_right _ _)
        hu' hv' hXi (fun y => (hub y).trans (le_max_left _ _))
        (fun y => (hvb y).trans (le_max_left _ _)) hXp).trans ?_
      exact StepFresh.lintegral_jetWeight_le (closedLaw b W np) hW1 hC
        (fun y => jetDistance0 b E (Xcl b E s h τ m W j y)) (fun y => norm_nonneg _)
        (hJj j hj ⟨ij.1, h1⟩)
    · have h0 := kStopStep_eq_zero_of_unborn b E s h τ m R W j (Vs W) ij (Or.inr (by omega))
      simp only [h0, enorm_zero]
      norm_num
  · have h0 := kStopStep_eq_zero_of_unborn b E s h τ m R W j (Vs W) ij (Or.inl (by omega))
    simp only [h0, enorm_zero]
    norm_num

/-- **`KCorrStepFourAt` from the closed exact update, the closed jet and the contract
hypotheses.** -/
theorem kCorrStepFourAt_of_closed (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) (hL : ClosedPastFreshLaw)
    {Xcl : ClosedInputFam} (hF : ClosedKStepForm Xcl) (hJ : ClosedJetHalf Xcl) :
    KCorrStepFourAt :=
  kCorrStepFourAt_of_stopAt hGA hLp hSR hMT (kStopStepFourAt_of_closed hGA hLp hL hF hJ)

end BlockBand.SourceProcess.PhysApprox.B3
