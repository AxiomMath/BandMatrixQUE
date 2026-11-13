module

public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormBound
public import BlockBand.SourceProcess.PhysApprox.B3MeanClosed
public import BlockBand.SourceProcess.PhysApprox.B3StepK
public import BlockBand.SourceProcess.PhysApprox.B3CurMain

/-!
# The closed step forms `ClosedStepForm` and `ClosedKStepForm b3ClosedX`

* `ae_closedPath_good`, `ae_closedPhase_good`: the a.s. invertibilities;
* `ae_passive_b3ClosedX`: `X_cl` is a.s. passive at every length;
* **`closedStep_core`**: at a step `n_s ≤ i`, `i ≥ 1`, with two old tags, the stopped closed
  step is `u*Δ(X_cl, F_i)v` a.e. with Borel, past-determined frames of norm `≤ √R`;
* **`closedStepForm_holds`**: the first half of `ClosedKMeanInput` (`ClosedStepForm` with
  `X = b3ClosedX`, `C_f = √R`), eventually in `W`, at every non-birth step with live entry;
* **`closedKStepForm_holds : ClosedKStepForm b3ClosedX`**;
* **`ClosedJetL4Pin`** (the second half, for the same `b3ClosedX`, stated as a hypothesis)
  and **`closedKMeanInput_of_jet : ClosedJetL4Pin → ClosedKMeanInput`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.PhysApprox.ClosedForm
open scoped ComplexOrder

variable {W np K : ℕ}

/-!
## Almost-sure invertibility
-/

theorem measurable_det_comp {α n : Type*} [MeasurableSpace α] [Fintype n] [DecidableEq n]
    {f : α → Matrix n n ℂ} (hf : Measurable f) : Measurable fun a => (f a).det :=
  (continuous_id.matrix_det).measurable.comp hf

/-- The path-level a.s. facts under `closedLaw`. -/
theorem ae_closedPath_good {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) :
    ∀ᵐ y ∂closedLaw b W np, (∀ k, (y.1.1.1 k).IsHermitian) ∧
      (∀ n, IsUnit (pathMatrix (pathAt W n y.1.1) - (E : ℂ) • 1)) ∧ (∀ k, IsUnit (y.1.1.2 k)) ∧
      ∀ n, scatteringMatrix b E W n y.1.1 * (scatteringMatrix b E W n y.1.1)ᴴ = 1 := by
  have hq : Measure.QuasiMeasurePreserving (fun y : ProbedPath W np × ℝ => y.1.1)
      (closedLaw b W np) (growthPathLaw W b) :=
    (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)).comp
      (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw W np b))
  have h0 : ∀ᵐ ω ∂growthPathLaw W b, (∀ k, (ω.1 k).IsHermitian) ∧
      (∀ n, IsUnit (pathMatrix (pathAt W n ω) - (E : ℂ) • 1)) ∧ (∀ k, IsUnit (ω.2 k)) ∧
      ∀ n, scatteringMatrix b E W n ω * (scatteringMatrix b E W n ω)ᴴ = 1 := by
    filter_upwards [ae_growth_isHermitian W b, ae_isUnit_pathPencil_growth hb hW E,
      ae_isUnit_growth_bond hb0 hW, ae_scattering_unitary hb hE1 hE2 hW] with ω h1 h2 h3 h4
    exact ⟨h1, h2, h3, fun n => (h4 n).1⟩
  exact hq.ae h0

/-- The unclosed near resolvent `R₀` at length `j`. -/
def closedR0 (b E h s : ℝ) (W j : ℕ) (ω : GrowthPath W) : Matrix (Fin W) (Fin W) ℂ :=
  nearSel W * boundaryResolvent b E W j ω *
    (1 - farEmbed (omittedProj b E h W (closeLen s W) ω)) * (nearSel W)ᴴ

theorem measurable_closingDen (b E s h : ℝ) (n : ℕ) :
    Measurable fun y : ProbedPath W np × ℝ => 1 - phase y.2 • closingN
      (scatteringMatrix b E W n y.1.1) (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
      (farEmbed (closingPairing b E h W (closeLen s W) y.1.1)) := by
  have hω : Measurable fun y : ProbedPath W np × ℝ => y.1.1 := measurable_fst.comp measurable_fst
  have hS := (measurable_scatteringMatrix b E n).comp hω
  have hA := measurable_farEmbed ((measurable_omittedProj b E h (closeLen s W)).comp hω)
  have hP := measurable_farEmbed ((measurable_closingPairing b E h (closeLen s W)).comp hω)
  exact measurable_matrix_sub measurable_const (measurable_matrix_cmul
    (measurable_phase.comp measurable_snd) (measurable_matrix_mul' (measurable_matrix_mul' hP hS)
      hA))

/-- The phase-level a.s. invertibilities under `closedLaw`, at the step `j → j + 1`. -/
theorem ae_closedPhase_good (b E s h : ℝ) (j : ℕ) :
    ∀ᵐ y ∂closedLaw b W np,
      (1 - phase y.2 • closingN (scatteringMatrix b E W j y.1.1)
        (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
        (farEmbed (closingPairing b E h W (closeLen s W) y.1.1))).det ≠ 0 ∧
      (1 - phase y.2 • closingN (scatteringMatrix b E W (j + 1) y.1.1)
        (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
        (farEmbed (closingPairing b E h W (closeLen s W) y.1.1))).det ≠ 0 ∧
      (1 - (phase y.2 * (star (boundaryZ b E) / boundaryZ b E)) •
        farEmbed (closingPairing b E h W (closeLen s W) y.1.1)).det ≠ 0 ∧
      ((closedR0 b E h s W j y.1.1).det = 0 ∨
        (closedNearR b E s h W j y.1.1 (phase y.2)).det ≠ 0) := by
  have hω : Measurable fun y : ProbedPath W np × ℝ => y.1.1 := measurable_fst.comp measurable_fst
  have m1 := measurable_det_comp (measurable_closingDen (W := W) (np := np) b E s h j)
  have m2 := measurable_det_comp (measurable_closingDen (W := W) (np := np) b E s h (j + 1))
  have m3 : Measurable fun y : ProbedPath W np × ℝ =>
      (1 - (phase y.2 * (star (boundaryZ b E) / boundaryZ b E)) •
        farEmbed (closingPairing b E h W (closeLen s W) y.1.1)).det :=
    measurable_det_comp (measurable_matrix_sub measurable_const (measurable_matrix_cmul
      ((measurable_phase.comp measurable_snd).mul measurable_const)
      (measurable_farEmbed ((measurable_closingPairing b E h (closeLen s W)).comp hω))))
  have m4 : Measurable fun y : ProbedPath W np × ℝ => (closedR0 b E h s W j y.1.1).det :=
    measurable_det_comp (measurable_matrix_mul' (measurable_matrix_mul'
      (measurable_matrix_mul' measurable_const (measurable_boundaryResolvent_comp b E j hω))
      (measurable_matrix_sub measurable_const
        (measurable_farEmbed ((measurable_omittedProj b E h (closeLen s W)).comp hω))))
      measurable_const)
  have m5 := measurable_det_comp (measurable_closedNearR (W := W) (np := np) b E s h j)
  have hs := (m1 (measurableSet_singleton 0).compl).inter
    ((m2 (measurableSet_singleton 0).compl).inter ((m3 (measurableSet_singleton 0).compl).inter
      ((m4 (measurableSet_singleton 0)).union (m5 (measurableSet_singleton 0).compl))))
  refine (Measure.ae_prod_mem_iff_ae_ae_mem hs).2 (Eventually.of_forall fun x => ?_)
  have hcorner : ∀ᵐ θ ∂phaseLaw, (closedR0 b E h s W j x.1).det = 0 ∨
      (closedNearR b E s h W j x.1 (phase θ)).det ≠ 0 := by
    by_cases hR0 : IsUnit (closedR0 b E h s W j x.1).det
    · filter_upwards [ae_isUnit_corner (closedR0 b E h s W j x.1)
        (nearSel W * boundaryResolvent b E W j x.1)
        (closingN (scatteringMatrix b E W j x.1)
          (farEmbed (omittedProj b E h W (closeLen s W) x.1))
          (farEmbed (closingPairing b E h W (closeLen s W) x.1)))
        (closingT (scatteringMatrix b E W j x.1)
          (farEmbed (omittedProj b E h W (closeLen s W) x.1))
          (farEmbed (closingPairing b E h W (closeLen s W) x.1)) * (nearSel W)ᴴ) hR0] with θ hθ
      right
      rw [closedNearR_eq_corner]
      exact hθ.ne_zero
    · exact Eventually.of_forall fun _ => Or.inl (not_not.1 (mt isUnit_iff_ne_zero.2 hR0))
  filter_upwards [ae_isUnit_one_sub_smul 1 (closingN (scatteringMatrix b E W j x.1)
      (farEmbed (omittedProj b E h W (closeLen s W) x.1))
      (farEmbed (closingPairing b E h W (closeLen s W) x.1))),
    ae_isUnit_one_sub_smul 1 (closingN (scatteringMatrix b E W (j + 1) x.1)
      (farEmbed (omittedProj b E h W (closeLen s W) x.1))
      (farEmbed (closingPairing b E h W (closeLen s W) x.1))),
    ae_isUnit_one_sub_smul (star (boundaryZ b E) / boundaryZ b E)
      (farEmbed (closingPairing b E h W (closeLen s W) x.1)), hcorner] with θ h1 h2 h3 h4
  rw [mul_one] at h1 h2
  exact ⟨h1.ne_zero, h2.ne_zero, h3.ne_zero, h4⟩

/-- **`X_cl` is a.s. passive** at every length. -/
theorem ae_passive_b3ClosedX {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (s h : ℝ) (hh : h ^ 2 < 1) (τ m : Fin np → ℝ) (hW : 1 ≤ W) (j : ℕ) :
    ∀ᵐ y ∂closedLaw b W np, (passiveY (b3ClosedX b E s h τ m W j y)).PosSemidef := by
  have hη := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  filter_upwards [ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW,
    ae_closedPhase_good (W := W) (np := np) b E s h j] with y hP hQ
  obtain ⟨hA, hF, -, hS⟩ := hP
  obtain ⟨h1, -, -, h4⟩ := hQ
  have hR := h4.resolve_left (isUnit_closedR0 b E h s j y.1.1 hA hη (hF j)).ne_zero
  exact passive_closedNearX b E s h hh j y.1.1 y.2 hη (hS j) (isUnit_iff_ne_zero.2 h1)
    (isUnit_iff_ne_zero.2 hR)

/-!
## The clipped frames
-/

/-- `w` if `‖w‖ ≤ C`, else `0`. -/
def clipVec (C : ℝ) (w : Fin W → ℂ) : Fin W → ℂ := if vecNorm w ≤ C then w else 0

theorem measurable_vecNorm : Measurable fun w : Fin W → ℂ => vecNorm w :=
  (Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
    (continuous_norm.comp (continuous_apply i)).pow 2)).measurable

theorem measurable_clipVec_comp {α : Type*} [MeasurableSpace α] (C : ℝ) {f : α → Fin W → ℂ}
    (hf : Measurable f) : Measurable fun a => clipVec C (f a) :=
  Measurable.ite (measurableSet_le (measurable_vecNorm.comp hf) measurable_const) hf
    measurable_const

theorem vecNorm_clipVec_le {C : ℝ} (hC : 0 ≤ C) (w : Fin W → ℂ) : vecNorm (clipVec C w) ≤ C := by
  unfold clipVec
  split_ifs with hw
  · exact hw
  · simpa [vecNorm] using hC

/-!
## The closed exact update with bounded frames
-/

/-- **The closed exact update with bounded past-determined frames** at a step `n_s ≤ i`,
`i ≥ 1`, for two old tags. -/
theorem closedStep_core {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (s h : ℝ) (hh : h ^ 2 < 1) (τ m : Fin np → ℝ) (hW : 1 ≤ W)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hVm : Measurable Vs)
    (hVinv : ∀ j, closeLen s W ≤ j → ∀ ω, Vs (extPast W j (pastCoords W j ω)) = Vs ω)
    (R : ℝ) {i : ℕ} (hi : 1 ≤ i) (hsi : closeLen s W ≤ i) (ij : Fin np × Fin np)
    (h1 : ⌊(W : ℝ) * τ ij.1⌋₊ < i) (h2 : ⌊(W : ℝ) * τ ij.2⌋₊ < i) :
    ∃ u v : ProbedPath W np × ℝ → Fin W → ℂ, Measurable u ∧ Measurable v ∧
      (∀ y, u (b3Ext W i y) = u y) ∧ (∀ y, v (b3Ext W i y) = v y) ∧
      (∀ y, vecNorm (u y) ≤ Real.sqrt R) ∧ (∀ y, vecNorm (v y) ≤ Real.sqrt R) ∧
      kStopStep b E s h τ m R W i Vs ij =ᵐ[closedLaw b W np] fun y =>
        bilinear (u y) (freshDelta b E (b3ClosedX b E s h τ m W i y) (freshSample W i y.1.1))
          (v y) := by
  have hη := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  set Al := b3AliveM (np := np) b E s h τ m R W i Vs with hAl
  have hAlm : MeasurableSet Al := measurableSet_b3AliveM b E s h τ m R W i hVm
  have hAlinv : ∀ y, b3Ext W i y ∈ Al ↔ y ∈ Al :=
    mem_b3AliveM_b3Ext b E s h τ m R hsi le_rfl (hVinv i hsi)
  refine ⟨fun y => clipVec (Real.sqrt R) (Al.indicator (closedNearU b E s h τ m W i ij.1) y),
    fun y => clipVec (Real.sqrt R) (Al.indicator (closedNearV b E s h τ m W i ij.2) y),
    measurable_clipVec_comp _ ((measurable_closedNearU b E s h τ m i ij.1).indicator hAlm),
    measurable_clipVec_comp _ ((measurable_closedNearV b E s h τ m i ij.2).indicator hAlm),
    fun y => ?_, fun y => ?_, fun y => vecNorm_clipVec_le (Real.sqrt_nonneg _) _,
    fun y => vecNorm_clipVec_le (Real.sqrt_nonneg _) _, ?_⟩
  · by_cases hy : y ∈ Al
    · simp only [Set.indicator_of_mem hy, Set.indicator_of_mem ((hAlinv y).2 hy),
        closedNearU_b3Ext hsi le_rfl]
    · simp only [Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (fun h' => hy ((hAlinv y).1 h'))]
  · by_cases hy : y ∈ Al
    · simp only [Set.indicator_of_mem hy, Set.indicator_of_mem ((hAlinv y).2 hy),
        closedNearV_b3Ext hsi le_rfl]
    · simp only [Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (fun h' => hy ((hAlinv y).1 h'))]
  filter_upwards [kStopStep_ae_eq (by linarith) hE1 hE2 s h τ m R W i Vs ij,
    ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW,
    ae_closedPhase_good (W := W) (np := np) b E s h i] with y hZ hP hQ
  obtain ⟨hA, hF, hB, hS⟩ := hP
  obtain ⟨hU, hU', hY, h4⟩ := hQ
  have hR := h4.resolve_left (isUnit_closedR0 b E h s i y.1.1 hA hη (hF i)).ne_zero
  have hX := passive_closedNearX b E s h hh i y.1.1 y.2 hη (hS i) (isUnit_iff_ne_zero.2 hU)
    (isUnit_iff_ne_zero.2 hR)
  rw [hZ, kStopStepM]
  by_cases hy : y ∈ Al
  · have htr : ((b3ClosedGramAt b E s h τ m W i Vs y).1.trace).re < R := hy.2 i hsi le_rfl
    have hu := norm_closedNearU_le b E s h τ m i Vs ij.1 y htr
    have hv := norm_closedNearV_le b E s h hh τ m i Vs ij.2 y (hS i) (isUnit_iff_ne_zero.2 hU) htr
    rw [← hAl, Set.indicator_of_mem hy, Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    simp only [clipVec, hu, hv, ↓reduceIte]
    exact closedK_step b E s h τ m hi y hA hη (hF i) (hF (i + 1)) (hB (i + 1))
      (isUnit_iff_ne_zero.2 hU) (isUnit_iff_ne_zero.2 hU') (isUnit_iff_ne_zero.2 hY)
      (isUnit_iff_ne_zero.2 hR) hX h1 h2
  · rw [← hAl, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
    simp [clipVec, bilinear, vecNorm]

/-!
## The targets
-/

theorem lt_of_noBirth {s T : ℝ} {τ : Fin np → ℝ} {i : ℕ} (hi : i ∈ genNoBirthSteps s T τ W)
    (k : Fin np) (hk : ⌊(W : ℝ) * τ k⌋₊ < i + 1) : ⌊(W : ℝ) * τ k⌋₊ < i := by
  have hnb := (Finset.mem_filter.1 hi).2
  have hne : ⌊(W : ℝ) * τ k⌋₊ ≠ i := fun h' => hnb ⟨k, h'⟩
  omega

/-- **`ClosedStepForm` holds** for the closed input `b3ClosedX` with `C_f = √R`: the first half
of `ClosedKMeanInput`. -/
theorem closedStepForm_holds :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∀ᶠ W in atTop,
        ∀ ij : Fin np × Fin np, ∀ i ∈ genNoBirthSteps s T τ W,
          ⌊(W : ℝ) * τ ij.1⌋₊ < i + 1 → ⌊(W : ℝ) * τ ij.2⌋₊ < i + 1 →
          ∃ u v : ProbedPath W np × ℝ → Fin W → ℂ,
            ClosedStepForm b E s h τ m R W i (Vs W) ij (Real.sqrt R) u v
              (b3ClosedX b E s h τ m W i) := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hF.1
  have hh : h ^ 2 < 1 := by nlinarith [hF.2.2.2.1, hF.2.2.2.2.1]
  filter_upwards [hF.2.2.2.2.2, eventually_ge_atTop 1, B3Cur.eventually_one_le_closeLen hF.2.1]
    with W hVW hW hs1 ij i hi hk1 hk2
  have hVs : Measurable[growthSigma W (closeLen s W)] (Vs W) := hVW.1
  have hmV : Measurable (Vs W) :=
    hVs.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hVinv : ∀ j, closeLen s W ≤ j → ∀ ω, Vs W (extPast W j (pastCoords W j ω)) = Vs W ω :=
    fun j hj ω => growth_fun_extPast hj hVs ω
  have hsi : closeLen s W ≤ i := (Finset.mem_Ico.1 (Finset.mem_filter.1 hi).1).1
  obtain ⟨u, v, hu, hv, hu', hv', hub, hvb, hEq⟩ := closedStep_core hb0 hb hE1 hE2 s h hh τ m hW
    hmV hVinv R (hs1.trans hsi) hsi ij (lt_of_noBirth hi _ hk1) (lt_of_noBirth hi _ hk2)
  exact ⟨u, v, hu, hv, measurable_b3ClosedX b E s h τ m i, hu', hv',
    fun y => b3ClosedX_b3Ext hsi le_rfl y, hub, hvb,
    ae_passive_b3ClosedX hb0 hb hE1 hE2 s h hh τ m hW i, hEq⟩

/-- **`ClosedKStepForm b3ClosedX` holds.** -/
theorem closedKStepForm_holds : ClosedKStepForm b3ClosedX := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hF.1
  have hh : h ^ 2 < 1 := by nlinarith [hF.2.2.2.1, hF.2.2.2.2.1]
  refine ⟨Real.sqrt R, ?_⟩
  filter_upwards [hF.2.2.2.2.2, eventually_ge_atTop 1, B3Cur.eventually_one_le_closeLen hF.2.1]
    with W hVW hW hs1 j hj
  have hVs : Measurable[growthSigma W (closeLen s W)] (Vs W) := hVW.1
  have hmV : Measurable (Vs W) :=
    hVs.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hVinv : ∀ j, closeLen s W ≤ j → ∀ ω, Vs W (extPast W j (pastCoords W j ω)) = Vs W ω :=
    fun j hj ω => growth_fun_extPast hj hVs ω
  have hsj : closeLen s W ≤ j := (Finset.mem_Ico.1 hj).1
  refine ⟨measurable_b3ClosedX b E s h τ m j, fun y => b3ClosedX_b3Ext hsj le_rfl y,
    ae_passive_b3ClosedX hb0 hb hE1 hE2 s h hh τ m hW j, fun ij hk1 hk2 => ?_⟩
  obtain ⟨u, v, hu, hv, hu', hv', hub, hvb, hEq⟩ := closedStep_core hb0 hb hE1 hE2 s h hh τ m hW
    hmV hVinv R (hs1.trans hsj) hsj ij hk1 hk2
  exact ⟨u, v, hu, hv, hu', hv', hub, hvb, hEq⟩

/-- **`ClosedJetL4Pin`** (`ClosedJetL4` for the closed input `b3ClosedX`): eventually,
at every non-birth step with a born tag, `∫δ₀(X_cl)⁴ ≤ C_j/W⁴`. -/
def ClosedJetL4Pin : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∃ Cj : ℝ, ∀ᶠ W in atTop,
      ∀ i ∈ genNoBirthSteps s T τ W, (∃ k, ⌊(W : ℝ) * τ k⌋₊ < i + 1) →
        ClosedJetL4 b E W np Cj (b3ClosedX b E s h τ m W i)

/-- **`ClosedKMeanInput` from the closed jet of `b3ClosedX`**: the exact-update half is
`closedStepForm_holds`. -/
theorem closedKMeanInput_of_jet (hJ : ClosedJetL4Pin) : ClosedKMeanInput := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨Cj, hCj⟩ := hJ b E np τ m T s h K Vs hF
  refine ⟨Real.sqrt R, Cj, ?_⟩
  filter_upwards [closedStepForm_holds b E np τ m T s h K Vs hF R, hCj] with W hS hJW ij i hi
    hk1 hk2
  obtain ⟨u, v, huv⟩ := hS ij i hi hk1 hk2
  exact ⟨u, v, b3ClosedX b E s h τ m W i, huv, hJW i hi ⟨ij.1, hk1⟩⟩

end BlockBand.SourceProcess.PhysApprox.B3

