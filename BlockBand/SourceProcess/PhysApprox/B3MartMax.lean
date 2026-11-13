module

public import BlockBand.SourceProcess.PhysApprox.B3MartGen
public import BlockBand.SourceProcess.PhysApprox.B3MomMax
public import BlockBand.SourceProcess.ClosedSumProof.Events

/-!
# The maximal martingale bound `TargetMartMax`

* `b3Filt`: the closed filtration `j ↦ b3Sigma W j` (monotone, `b3Sigma_mono`);
* adaptedness (as in `ClosedSumProof`, for the probed closed process):
  every closed object at length `k ≤ j` with `n_s ≤ k` is unchanged when the path is replaced by
  its past at length `j` (`b3ClosedKAt_b3Ext`, `b3ClosedGramAt_b3Ext`, `mem_b3AliveM_b3Ext`), so
  the Borel stopped step `kStopStepM` (`b3AliveM` for `b3Alive`) is `b3Sigma (i + 1)`-measurable
  (`measurable_kStopStepM_past`) and a.e. equal to `kStopStep` (`kStopStep_ae_eq`);
* **`targetMartMax_holds : TargetMartMax`**, from the generic Doob + crude Burkholder bound
  `lintegral_runMax_martSum_le`:
  `E max_{n ≤ N}|Σ d|⁴ ≤ 4096 (N + 1) Σ_{non-birth} E|Z_i|⁴`, `N = ⌊WT⌋ ≤ W·max T 0`, so
  `(N + 1)/W ≤ max T 0 + 1` and the `W ·` normalisation of `KStopStepFour` cancels exactly:
  constant `4096 (max T 0 + 1) max C 0`, uniform in `W`. No factor of `N` is lost.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.FullSourceStops BlockBand.SourceProcess.FullSource
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal

variable {W np K : ℕ}

/-!
## The closed filtration
-/

theorem b3Sigma_mono {i j : ℕ} (hij : i ≤ j) : b3Sigma W i np ≤ b3Sigma W j np := by
  have e : (fun y : ProbedPath W np × ℝ => (pastCoords W i y.1.1, y.1.2, y.2)) =
      (fun x => (restrictPast hij x.1, x.2)) ∘
        (fun y : ProbedPath W np × ℝ => (pastCoords W j y.1.1, y.1.2, y.2)) := rfl
  show MeasurableSpace.comap _ _ ≤ MeasurableSpace.comap _ _
  rw [e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono
    (((measurable_restrictPast hij).comp measurable_fst).prodMk measurable_snd).comap_le

theorem b3Sigma_le (j : ℕ) :
    b3Sigma W j np ≤ (inferInstance : MeasurableSpace (ProbedPath W np × ℝ)) :=
  (measurable_b3Sigma_map W j np).comap_le

/-- **The closed filtration** `j ↦ b3Sigma W j` (path up to `j`, probes, phase). -/
def b3Filt (W np : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (ProbedPath W np × ℝ)) where
  seq j := b3Sigma W j np
  mono' _ _ h := b3Sigma_mono h
  le' j := b3Sigma_le j

theorem b3Filt_apply (j : ℕ) : b3Filt W np j = b3Sigma W j np := rfl

/-!
## Functions of the past
-/

/-- The sample with the path replaced by its past at length `j` (extended by zeros). -/
def b3Ext (W j : ℕ) (y : ProbedPath W np × ℝ) : ProbedPath W np × ℝ :=
  ((extPast W j (pastCoords W j y.1.1), y.1.2), y.2)

/-- A Borel function unchanged by `b3Ext W j` is `b3Sigma W j`-measurable. -/
theorem measurable_b3Sigma_of_inv {β : Type*} [MeasurableSpace β] {j : ℕ}
    {f : ProbedPath W np × ℝ → β} (hf : Measurable f) (hinv : ∀ y, f (b3Ext W j y) = f y) :
    Measurable[b3Sigma W j np] f := by
  have hg : Measurable[b3Sigma W j np] fun y : ProbedPath W np × ℝ =>
      (pastCoords W j y.1.1, y.1.2, y.2) := comap_measurable _
  have hψ : Measurable fun x : Transmission.PathScalar.PastSample W j ×
      (Fin np → Fin W → ℂ) × ℝ =>
      (((extPast W j x.1, x.2.1), x.2.2) : ProbedPath W np × ℝ) :=
    (((measurable_extPast j).comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)
  have e : f = f ∘ ((fun x : Transmission.PathScalar.PastSample W j ×
      (Fin np → Fin W → ℂ) × ℝ =>
      (((extPast W j x.1, x.2.1), x.2.2) : ProbedPath W np × ℝ)) ∘
        fun y : ProbedPath W np × ℝ => (pastCoords W j y.1.1, y.1.2, y.2)) :=
    funext fun y => (hinv y).symm
  rw [e]
  exact hf.comp (hψ.comp hg)

/-- Membership in a `growthSigma W n`-event is unchanged by `extPast W j`, `n ≤ j`. -/
theorem mem_growth_extPast_iff {n j : ℕ} (hnj : n ≤ j) {A : Set (GrowthPath W)}
    (hA : MeasurableSet[growthSigma W n] A) (ω : GrowthPath W) :
    extPast W j (pastCoords W j ω) ∈ A ↔ ω ∈ A := by
  obtain ⟨T, -, rfl⟩ := hA
  show pastCoords W n (extPast W j (pastCoords W j ω)) ∈ T ↔ pastCoords W n ω ∈ T
  rw [ClosedSumProof.pastCoords_extPast_le hnj]

/-- A `growthSigma W n`-measurable function is unchanged by `extPast W j`, `n ≤ j`. -/
theorem growth_fun_extPast {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
    {n j : ℕ} (hnj : n ≤ j) {f : GrowthPath W → β} (hf : Measurable[growthSigma W n] f)
    (ω : GrowthPath W) : f (extPast W j (pastCoords W j ω)) = f ω :=
  (mem_growth_extPast_iff hnj (hf (measurableSet_singleton (f ω))) ω).2 rfl

theorem fullInverse_b3Ext {k j : ℕ} (hkj : k ≤ j) (b E : ℝ) (ω : GrowthPath W) :
    fullInverse b E W k (extPast W j (pastCoords W j ω)) = fullInverse b E W k ω := by
  simp only [fullInverse, fullPathMatrix, ContractingWords.pathAt_extPast_le hkj]

/-- **The closed `𝒦` at length `n_s ≤ k ≤ j` is a function of the past at `j`.** -/
theorem b3ClosedKAt_b3Ext (b E s h : ℝ) (τ m : Fin np → ℝ) {k j : ℕ} (hck : closeLen s W ≤ k)
    (hkj : k ≤ j) (y : ProbedPath W np × ℝ) :
    b3ClosedKAt b E s h τ m W k (b3Ext W j y) = b3ClosedKAt b E s h τ m W k y := by
  have hS := ClosedSumProof.scatteringMatrix_extPast hkj b E y.1.1
  have hS' := ClosedSumProof.scatteringMatrix_extPast (hck.trans hkj) b E y.1.1
  have hR : farReflection b E W (closeLen s W) (extPast W j (pastCoords W j y.1.1)) =
      farReflection b E W (closeLen s W) y.1.1 := by simp only [farReflection, hS']
  have hF := fullInverse_b3Ext hkj b E y.1.1
  simp only [b3Ext, b3ClosedKAt, complexSourceK, probeFrame, boundaryToInterior, omittedProj,
    closingPairing, farTransmission, hR, hS, hF]

/-- **The closed Gram state at length `n_s ≤ k ≤ j` is a function of the past at `j`**, for a
frame unchanged by `extPast W j`. -/
theorem b3ClosedGramAt_b3Ext (b E s h : ℝ) (τ m : Fin np → ℝ) {k j : ℕ}
    (hck : closeLen s W ≤ k) (hkj : k ≤ j)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : ∀ ω, Vs (extPast W j (pastCoords W j ω)) = Vs ω) (y : ProbedPath W np × ℝ) :
    b3ClosedGramAt b E s h τ m W k Vs (b3Ext W j y) = b3ClosedGramAt b E s h τ m W k Vs y := by
  have hS := ClosedSumProof.scatteringMatrix_extPast hkj b E y.1.1
  have hS' := ClosedSumProof.scatteringMatrix_extPast (hck.trans hkj) b E y.1.1
  have hR : farReflection b E W (closeLen s W) (extPast W j (pastCoords W j y.1.1)) =
      farReflection b E W (closeLen s W) y.1.1 := by simp only [farReflection, hS']
  have hF := fullInverse_b3Ext hkj b E y.1.1
  have hP := ClosedSumProof.stepProd_extPast (j := j) b E (closeLen s W) y.1.1
    (k - closeLen s W) (by omega)
  simp only [b3Ext, b3ClosedGramAt, b3ClosedFrameAt, b3OpenFrameAt, physClosingMapAt, probeFrame,
    boundaryToInterior, omittedProj, closingPairing, farTransmission, hR, hS, hF, hP, hV]

/-- Membership in the Borel alive set at `i ≤ j` is unchanged by `b3Ext W j`, `n_s ≤ j`. -/
theorem mem_b3AliveM_b3Ext (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) {i j : ℕ}
    (hcj : closeLen s W ≤ j) (hij : i ≤ j)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : ∀ ω, Vs (extPast W j (pastCoords W j ω)) = Vs ω) (y : ProbedPath W np × ℝ) :
    b3Ext W j y ∈ b3AliveM b E s h τ m R W i Vs ↔ y ∈ b3AliveM b E s h τ m R W i Vs := by
  have hcap := mem_growth_extPast_iff hcj (ClosedSumProof.measurableSet_capM b E s h K W) y.1.1
  have htr : ∀ k, closeLen s W ≤ k → k ≤ i →
      b3ClosedGramAt b E s h τ m W k Vs (b3Ext W j y) = b3ClosedGramAt b E s h τ m W k Vs y :=
    fun k hk1 hk2 => b3ClosedGramAt_b3Ext b E s h τ m hk1 (hk2.trans hij) hV y
  simp only [b3AliveM, b3TraceOK, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hcap.1 h1, fun k hk1 hk2 => by rw [← htr k hk1 hk2]; exact h2 k hk1 hk2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hcap.2 h1, fun k hk1 hk2 => by rw [htr k hk1 hk2]; exact h2 k hk1 hk2⟩

/-!
## The Borel stopped step
-/

/-- The stopped step with the Borel alive set `b3AliveM` in place of `b3Alive`. -/
def kStopStepM (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W i : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij : Fin np × Fin np) :
    ProbedPath W np × ℝ → ℂ :=
  (b3AliveM b E s h τ m R W i Vs).indicator (fun y =>
    b3ClosedKAt b E s h τ m W (i + 1) y ij.1 ij.2 - b3ClosedKAt b E s h τ m W i y ij.1 ij.2)

theorem kStopStep_ae_eq {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (s h : ℝ)
    (τ m : Fin np → ℝ) (R : ℝ) (W i : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij : Fin np × Fin np) :
    kStopStep b E s h τ m R W i Vs ij =ᵐ[closedLaw b W np] kStopStepM b E s h τ m R W i Vs ij :=
  indicator_ae_eq_of_ae_eq_set (b3Alive_ae_eq hb hE1 hE2 s h τ m R W i Vs)

/-- **Adaptedness**: the Borel stopped step `Z_i` is `b3Sigma (i + 1)`-measurable. -/
theorem measurable_kStopStepM_past (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) {i : ℕ}
    (hci : closeLen s W ≤ i) {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVm : Measurable Vs) (hV : ∀ ω, Vs (extPast W (i + 1) (pastCoords W (i + 1) ω)) = Vs ω)
    (ij : Fin np × Fin np) :
    Measurable[b3Sigma W (i + 1) np] (kStopStepM b E s h τ m R W i Vs ij) := by
  have hf : Measurable fun y : ProbedPath W np × ℝ =>
      b3ClosedKAt b E s h τ m W (i + 1) y ij.1 ij.2 - b3ClosedKAt b E s h τ m W i y ij.1 ij.2 :=
    (measurable_b3ClosedKAt b E s h τ m W (i + 1)).eval_matrix.sub
      (measurable_b3ClosedKAt b E s h τ m W i).eval_matrix
  refine measurable_b3Sigma_of_inv (hf.indicator (measurableSet_b3AliveM b E s h τ m R W i hVm))
    fun y => ?_
  have hmem := mem_b3AliveM_b3Ext b E s h τ m R (j := i + 1) (by omega) (Nat.le_succ i) hV y
  have e1 := b3ClosedKAt_b3Ext b E s h τ m (k := i + 1) (by omega) le_rfl y
  have e2 := b3ClosedKAt_b3Ext b E s h τ m (k := i) hci (Nat.le_succ i) y
  by_cases hy : y ∈ b3AliveM b E s h τ m R W i Vs
  · rw [kStopStepM, Set.indicator_of_mem (hmem.2 hy), Set.indicator_of_mem hy, e1, e2]
  · rw [kStopStepM, Set.indicator_of_notMem (fun h => hy (hmem.1 h)), Set.indicator_of_notMem hy]

theorem memLp_four_of_lintegral {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {f : Ω → ℂ} (hf : AEStronglyMeasurable f μ) (h : ∫⁻ ω, ‖f ω‖ₑ ^ 4 ∂μ ≠ ⊤) :
    MemLp f 4 μ := by
  rw [← mart_eLpNorm_pow_four hf] at h
  exact memLp_iff.2 (lt_top_iff_ne_top.2 fun h' => h (by rw [h']; simp))

/-- The non-birth steps below `n ≤ N`, as a filter of `range n`. -/
theorem filter_Ico_eq_range_filter {a n N : ℕ} (p : ℕ → Prop) [DecidablePred p] (hn : n ≤ N) :
    (Finset.Ico a n).filter p = (Finset.range n).filter (· ∈ (Finset.Ico a N).filter p) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h2, ⟨h1, by omega⟩, h3⟩
  · rintro ⟨h2, ⟨h1, -⟩, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

/-- `⌊WT⌋ + 1 ≤ W(max T 0 + 1)` for `W ≥ 1`. -/
theorem floor_add_one_le_mul {W : ℕ} (hW1 : 1 ≤ W) (T : ℝ) :
    ((⌊(W : ℝ) * T⌋₊ : ℝ≥0∞) + 1) ≤ ((W : ℕ) : ℝ≥0∞) * ENNReal.ofReal (max T 0 + 1) := by
  have hr : (⌊(W : ℝ) * T⌋₊ : ℝ) + 1 ≤ (W : ℝ) * (max T 0 + 1) := by
    have h1 : (⌊(W : ℝ) * T⌋₊ : ℝ) ≤ (W : ℝ) * max T 0 :=
      calc (⌊(W : ℝ) * T⌋₊ : ℝ) ≤ (⌊(W : ℝ) * max T 0⌋₊ : ℝ) := by
            exact_mod_cast Nat.floor_le_floor
              (mul_le_mul_of_nonneg_left (le_max_left T 0) (Nat.cast_nonneg W))
        _ ≤ (W : ℝ) * max T 0 := Nat.floor_le (by positivity)
    have h2 : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    nlinarith
  calc ((⌊(W : ℝ) * T⌋₊ : ℝ≥0∞) + 1) = ENNReal.ofReal ((⌊(W : ℝ) * T⌋₊ : ℝ) + 1) := by
        rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
          ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal ((W : ℝ) * (max T 0 + 1)) := ENNReal.ofReal_le_ofReal hr
    _ = ((W : ℕ) : ℝ≥0∞) * ENNReal.ofReal (max T 0 + 1) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-!
## `TargetMartMax`
-/

/-- **`TargetMartMax` holds**: Doob's `L⁴` maximal inequality and the crude Burkholder bound
(`lintegral_runMax_martSum_le`) give `KStopMartMax` from the per-step estimate `KStopStepFour`, with
constant `4096 (max T 0 + 1) max C 0` (`⌊WT⌋ + 1 ≤ W(max T 0 + 1)`). -/
theorem targetMartMax_holds : TargetMartMax := by
  intro hP b E np τ m T s h K Vs hF R
  obtain ⟨C, hC⟩ := hP b E np τ m T s h K Vs hF R
  refine ⟨4096 * (max T 0 + 1) * max C 0, ?_⟩
  have hb1 : b < 1 := by linarith [hF.1.2.1]
  have hE1 := hF.1.2.2.1
  have hE2 := hF.1.2.2.2.1
  filter_upwards [hC, hF.2.2.2.2.2, eventually_ge_atTop 1] with W hW hVW hW1 ij
  have hVs : Measurable[growthSigma W (closeLen s W)] (Vs W) := hVW.1
  have hmV : Measurable (Vs W) :=
    hVs.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hVinv : ∀ j, closeLen s W ≤ j → ∀ ω, Vs W (extPast W j (pastCoords W j ω)) = Vs W ω :=
    fun j hj ω => growth_fun_extPast hj hVs ω
  set N := ⌊(W : ℝ) * T⌋₊ with hN
  set S := (Finset.Ico (closeLen s W) N).filter (fun i => ¬ IsBirthStep τ W i) with hS
  set μ := closedLaw b W np with hμ
  set Z : ℕ → ProbedPath W np × ℝ → ℂ := fun i => kStopStepM b E s h τ m R W i (Vs W) ij
    with hZ
  have hZae : ∀ i, kStopStep b E s h τ m R W i (Vs W) ij =ᵐ[μ] Z i := fun i =>
    kStopStep_ae_eq hb1 hE1 hE2 s h τ m R W i (Vs W) ij
  have hSc : ∀ i ∈ S, closeLen s W ≤ i := fun i hi =>
    (Finset.mem_Ico.1 (Finset.mem_filter.1 hi).1).1
  have hZm : ∀ i ∈ S, StronglyMeasurable[b3Filt W np (i + 1)] (Z i) := fun i hi =>
    (measurable_kStopStepM_past b E s h τ m R (hSc i hi) hmV
      (hVinv (i + 1) (by have := hSc i hi; omega)) ij).stronglyMeasurable
  have hsum_eq : ∀ i, ∫⁻ y, ‖Z i y‖ₑ ^ 4 ∂μ =
      ∫⁻ y, ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ∂μ := fun i =>
    lintegral_congr_ae ((hZae i).mono fun y hy => by simp only [hy])
  have hW' := hW ij
  have hfin : ∀ i ∈ S, ∫⁻ y, ‖Z i y‖ₑ ^ 4 ∂μ ≠ ⊤ := by
    intro i hi
    rw [hsum_eq]
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans ?_ hW')
    calc ∫⁻ y, ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ∂μ
        ≤ ∑ i ∈ S, ∫⁻ y, ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ∂μ :=
          Finset.single_le_sum (f := fun i => ∫⁻ y,
            ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ∂μ) (fun _ _ => zero_le) hi
      _ ≤ ((W : ℕ) : ℝ≥0∞) * ∑ i ∈ S,
            ∫⁻ y, ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ∂μ :=
          le_mul_of_one_le_left zero_le (by exact_mod_cast hW1)
  have hZ4 : ∀ i ∈ S, MemLp (Z i) 4 μ := fun i hi =>
    memLp_four_of_lintegral (((hZm i hi).mono ((b3Filt W np).le (i + 1))).aestronglyMeasurable)
      (hfin i hi)
  have key := lintegral_runMax_martSum_le (μ := μ) (ℱ := b3Filt W np) hZm hZ4 N
  have hae : ∀ᵐ y ∂μ, ∀ i, kStopMart b E s h τ m R W i (Vs W) ij y =
      Z i y - μ[Z i | b3Filt W np i] y := by
    rw [ae_all_iff]
    intro i
    have h1 : kStopMean b E s h τ m R W i (Vs W) ij =ᵐ[μ] μ[Z i | b3Filt W np i] :=
      condExp_congr_ae (hZae i)
    filter_upwards [hZae i, h1] with y e1 e2
    rw [kStopMart, e1, e2]
  have hpt : ∀ᵐ y ∂μ, (⨆ n ∈ Finset.Icc (closeLen s W) N,
      ‖∑ i ∈ (Finset.Ico (closeLen s W) n).filter (fun i => ¬ IsBirthStep τ W i),
        kStopMart b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4) ≤
      ‖(Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖martSum (b3Filt W np) μ S Z k y‖)‖ₑ ^ 4 := by
    filter_upwards [hae] with y hy
    refine iSup₂_le fun n hn => ?_
    obtain ⟨-, hn2⟩ := Finset.mem_Icc.1 hn
    have hset : (Finset.Ico (closeLen s W) n).filter (fun i => ¬ IsBirthStep τ W i) =
        (Finset.range n).filter (· ∈ S) := filter_Ico_eq_range_filter _ hn2
    have hsum : ∑ i ∈ (Finset.Ico (closeLen s W) n).filter (fun i => ¬ IsBirthStep τ W i),
        kStopMart b E s h τ m R W i (Vs W) ij y = martSum (b3Filt W np) μ S Z n y := by
      rw [hset, martSum, Finset.sum_apply]
      exact Finset.sum_congr rfl fun i _ => hy i
    rw [hsum]
    have hle : ‖martSum (b3Filt W np) μ S Z n y‖ ≤
        (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖martSum (b3Filt W np) μ S Z k y‖) :=
      Finset.le_sup' (fun k => ‖martSum (b3Filt W np) μ S Z k y‖)
        (Finset.mem_range.2 (by omega))
    refine pow_le_pow_left₀ zero_le ?_ 4
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hle.trans (Real.le_norm_self _))
  have hfilt : (Finset.range N).filter (· ∈ S) = S :=
    (filter_Ico_eq_range_filter (a := closeLen s W) _ le_rfl).symm
  have hNW := floor_add_one_le_mul hW1 T
  set sig4 := ∑ i ∈ S, ∫⁻ y, ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ∂μ with hsig4
  calc ∫⁻ y, (⨆ n ∈ Finset.Icc (closeLen s W) N,
          ‖∑ i ∈ (Finset.Ico (closeLen s W) n).filter (fun i => ¬ IsBirthStep τ W i),
            kStopMart b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4) ∂μ
      ≤ ∫⁻ y, ‖(Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖martSum (b3Filt W np) μ S Z k y‖)‖ₑ ^ 4 ∂μ := lintegral_mono_ae hpt
    _ ≤ 4096 * ((N : ℝ≥0∞) + 1) * ∑ i ∈ (Finset.range N).filter (· ∈ S),
          ∫⁻ y, ‖Z i y‖ₑ ^ 4 ∂μ := key
    _ = 4096 * ((N : ℝ≥0∞) + 1) * sig4 := by
        rw [hfilt, hsig4]
        exact congrArg _ (Finset.sum_congr rfl fun i _ => hsum_eq i)
    _ ≤ 4096 * (((W : ℕ) : ℝ≥0∞) * ENNReal.ofReal (max T 0 + 1)) * sig4 := by gcongr
    _ = 4096 * ENNReal.ofReal (max T 0 + 1) * (((W : ℕ) : ℝ≥0∞) * sig4) := by ring
    _ ≤ 4096 * ENNReal.ofReal (max T 0 + 1) * ENNReal.ofReal (max C 0) := by
        gcongr
        exact hW'.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    _ = ENNReal.ofReal (4096 * (max T 0 + 1) * max C 0) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_ofNat]

end BlockBand.SourceProcess.PhysApprox.B3
