module

public import BlockBand.SourceProcess.PhysApprox.B3MomTight
public import BlockBand.SourceProcess.PhysApprox.B3GenDoob
public import BlockBand.SourceProcess.ClosedSumProof.Events
public import BlockBand.SourceProcess.ClosedSumProof.ClosedStep

/-!
# Adaptedness of the closed complex process

The complex copy of the adaptedness and event-measurability lemmas of `ClosedSumProof`, for the
closed law `closedLaw b W np` and the filtration `b3Sigma W j np` (path up
to `j`, probe Gaussians, phase). For an admissible frame (`growthSigma W n_s`-measurable) and
`n_s ≤ i ≤ j`:
* `b3Sigma_mono`: the filtration is monotone;
* **`measurable_b3X_past`**: every coordinate `b3X … i … c` (Gram and `𝒦`) is
  `b3Sigma W j`-measurable;
* **`measurableSet_b3AliveM_past`**: the Borel alive set `b3AliveM … i` is a `b3Sigma W j`-event.

Method: `rho W j` replaces the path by its past at length `j` (`extPast`); every object
above is invariant under `rho W j`, and a measurable `rho W j`-invariant function is
`b3Sigma W j`-measurable. The lemmas `scatteringMatrix_extPast`, `stepProd_extPast`,
`pastCoords_extPast_le` and `measurableSet_capM` are used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Modul

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.FullSourceStops BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.FullSource BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.PathScalar

variable {W np K : ℕ}

/-!
## The past replacement
-/

/-- Replace the path by its past at length `j` (extended by zero). -/
def rho (W j np : ℕ) (y : ProbedPath W np × ℝ) : ProbedPath W np × ℝ :=
  ((extPast W j (pastCoords W j y.1.1), y.1.2), y.2)

theorem measurable_rho (j : ℕ) : Measurable[b3Sigma W j np] (rho W j np) := by
  have hg : Measurable fun x : PastSample W j × (Fin np → Fin W → ℂ) × ℝ =>
      (((extPast W j x.1, x.2.1), x.2.2) : ProbedPath W np × ℝ) :=
    (((measurable_extPast j).comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)
  exact hg.comp (comap_measurable _)

/-- A measurable `rho W j`-invariant function is `b3Sigma W j`-measurable. -/
theorem measurable_of_rho {β : Type*} [MeasurableSpace β] {j : ℕ}
    {f : ProbedPath W np × ℝ → β} (hf : Measurable f) (hρ : ∀ y, f (rho W j np y) = f y) :
    Measurable[b3Sigma W j np] f := by
  have h := hf.comp (measurable_rho (W := W) (np := np) j)
  rwa [show f ∘ rho W j np = f from funext hρ] at h

/-- A measurable `rho W j`-invariant set is a `b3Sigma W j`-event. -/
theorem measurableSet_of_rho {j : ℕ} {S : Set (ProbedPath W np × ℝ)} (hS : MeasurableSet S)
    (hρ : ∀ y, rho W j np y ∈ S ↔ y ∈ S) : MeasurableSet[b3Sigma W j np] S := by
  have h := measurable_rho (W := W) (np := np) j hS
  rwa [show rho W j np ⁻¹' S = S from Set.ext hρ] at h

/-- The filtration is monotone. -/
theorem b3Sigma_mono {i j : ℕ} (hij : i ≤ j) : b3Sigma W i np ≤ b3Sigma W j np := by
  refine Measurable.comap_le ?_
  have e : (fun y : ProbedPath W np × ℝ => (pastCoords W i y.1.1, y.1.2, y.2)) =
      (fun x => (restrictPast hij x.1, x.2)) ∘
        (fun y : ProbedPath W np × ℝ => (pastCoords W j y.1.1, y.1.2, y.2)) := rfl
  rw [e]
  exact (((measurable_restrictPast hij).comp measurable_fst).prodMk measurable_snd).comp
    (comap_measurable _)

/-!
## Functions of the past at an earlier length
-/

theorem mem_iff_of_growth {n j : ℕ} (hnj : n ≤ j) {S : Set (GrowthPath W)}
    (hS : MeasurableSet[growthSigma W n] S) (ω : GrowthPath W) :
    extPast W j (pastCoords W j ω) ∈ S ↔ ω ∈ S := by
  obtain ⟨S', -, rfl⟩ := hS
  show pastCoords W n (extPast W j (pastCoords W j ω)) ∈ S' ↔ pastCoords W n ω ∈ S'
  rw [ClosedSumProof.pastCoords_extPast_le hnj ω]

theorem eq_of_growth {n j : ℕ} (hnj : n ≤ j)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : Measurable[growthSigma W n] Vs) (ω : GrowthPath W) :
    Vs (extPast W j (pastCoords W j ω)) = Vs ω := by
  ext a k
  have hm : MeasurableSet[growthSigma W n] {ω' | Vs ω' a k = Vs ω a k} :=
    (@Measurable.eval_matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ _ (GrowthPath W)
      (growthSigma W n) a k Vs hV) (measurableSet_singleton _)
  exact (mem_iff_of_growth hnj hm ω).2 rfl

variable (b E : ℝ)

theorem fullInverse_extPast {i j : ℕ} (hij : i ≤ j) (ω : GrowthPath W) :
    fullInverse b E W i (extPast W j (pastCoords W j ω)) = fullInverse b E W i ω := by
  simp only [fullInverse, fullPathMatrix, ContractingWords.pathAt_extPast_le hij]

theorem boundaryToInterior_extPast {i j : ℕ} (hij : i ≤ j) (ω : GrowthPath W) :
    boundaryToInterior b E W i (extPast W j (pastCoords W j ω)) = boundaryToInterior b E W i ω := by
  simp only [boundaryToInterior, fullInverse_extPast b E hij]

theorem farReflection_extPast {i j : ℕ} (hij : i ≤ j) (ω : GrowthPath W) :
    farReflection b E W i (extPast W j (pastCoords W j ω)) = farReflection b E W i ω := by
  simp only [farReflection, ClosedSumProof.scatteringMatrix_extPast hij]

theorem omittedProj_extPast (h : ℝ) {i j : ℕ} (hij : i ≤ j) (ω : GrowthPath W) :
    omittedProj b E h W i (extPast W j (pastCoords W j ω)) = omittedProj b E h W i ω := by
  simp only [omittedProj, farTransmission, farReflection_extPast b E hij]

theorem closingPairing_extPast (h : ℝ) {i j : ℕ} (hij : i ≤ j) (ω : GrowthPath W) :
    closingPairing b E h W i (extPast W j (pastCoords W j ω)) = closingPairing b E h W i ω := by
  simp only [closingPairing, farTransmission, farReflection_extPast b E hij]

variable {b E} (s h : ℝ) (τ m : Fin np → ℝ)

theorem physClosingMapAt_extPast {i j : ℕ} (hs : closeLen s W ≤ i) (hij : i ≤ j)
    (ω : GrowthPath W) (z : ℂ) :
    physClosingMapAt b E s h W i (extPast W j (pastCoords W j ω)) z =
      physClosingMapAt b E s h W i ω z := by
  simp only [physClosingMapAt, ClosedSumProof.scatteringMatrix_extPast hij,
    omittedProj_extPast b E h (hs.trans hij), closingPairing_extPast b E h (hs.trans hij)]

/-!
## Invariance of the closed process
-/

theorem b3ClosedGramAt_rho {i j : ℕ} (hs : closeLen s W ≤ i) (hij : i ≤ j)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : Measurable[growthSigma W (closeLen s W)] Vs) (y : ProbedPath W np × ℝ) :
    b3ClosedGramAt b E s h τ m W i Vs (rho W j np y) = b3ClosedGramAt b E s h τ m W i Vs y := by
  simp only [b3ClosedGramAt, b3ClosedFrameAt, b3OpenFrameAt, probeFrame, rho,
    physClosingMapAt_extPast s h hs hij, boundaryToInterior_extPast b E hij,
    eq_of_growth (hs.trans hij) hV,
    ClosedSumProof.stepProd_extPast b E (closeLen s W) _ (i - closeLen s W)
      (by omega : closeLen s W + (i - closeLen s W) ≤ j)]

theorem b3ClosedKAt_rho {i j : ℕ} (hs : closeLen s W ≤ i) (hij : i ≤ j)
    (y : ProbedPath W np × ℝ) :
    b3ClosedKAt b E s h τ m W i (rho W j np y) = b3ClosedKAt b E s h τ m W i y := by
  simp only [b3ClosedKAt, complexSourceK, probeFrame, rho, fullInverse_extPast b E hij,
    boundaryToInterior_extPast b E hij, ClosedSumProof.scatteringMatrix_extPast hij,
    omittedProj_extPast b E h (hs.trans hij), closingPairing_extPast b E h (hs.trans hij)]

theorem b3X_rho {i j : ℕ} (hs : closeLen s W ≤ i) (hij : i ≤ j)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : Measurable[growthSigma W (closeLen s W)] Vs) (c : CIdx K np)
    (y : ProbedPath W np × ℝ) :
    b3X b E s h τ m W i Vs c (rho W j np y) = b3X b E s h τ m W i Vs c y := by
  simp only [b3X, b3ClosedGramAt_rho s h τ m hs hij hV, b3ClosedKAt_rho s h τ m hs hij]

/-!
## Measurability
-/

theorem measurable_cEntry_comp {α : Type*} [MeasurableSpace α] (c : CIdx K np)
    {G : α → GramState (SrcCol K (Fin np))} {Kc : α → Matrix (Fin np) (Fin np) ℂ}
    (hG : Measurable G) (hK : Measurable Kc) : Measurable fun a => cEntry c (G a) (Kc a) := by
  cases c with
  | inl e => exact (ClosedSumProof.measurable_gramEntry e).comp hG
  | inr ij => exact hK.eval_matrix

theorem measurable_b3X {i : ℕ} {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : Measurable Vs) (c : CIdx K np) : Measurable (b3X b E s h τ m W i Vs c) :=
  measurable_cEntry_comp c (measurable_b3ClosedGramAt b E s h τ m W i hV)
    (measurable_b3ClosedKAt b E s h τ m W i)

/-- **Adaptedness of the closed complex process.** -/
theorem measurable_b3X_past {i j : ℕ} (hs : closeLen s W ≤ i) (hij : i ≤ j)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : Measurable[growthSigma W (closeLen s W)] Vs) (c : CIdx K np) :
    Measurable[b3Sigma W j np] (b3X b E s h τ m W i Vs c) :=
  measurable_of_rho (measurable_b3X s h τ m
    (hV.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl) c)
    (b3X_rho s h τ m hs hij hV c)

/-- **The Borel alive set at `i` is a `b3Sigma W j`-event** (`n_s ≤ j`, `i ≤ j`). -/
theorem measurableSet_b3AliveM_past (R : ℝ) {i j : ℕ} (hs : closeLen s W ≤ j) (hij : i ≤ j)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : Measurable[growthSigma W (closeLen s W)] Vs) :
    MeasurableSet[b3Sigma W j np] (b3AliveM b E s h τ m R W i Vs) := by
  refine measurableSet_of_rho (measurableSet_b3AliveM b E s h τ m R W i
    (hV.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl)) fun y => ?_
  have hcap := mem_iff_of_growth hs (ClosedSumProof.measurableSet_capM b E s h K W) y.1.1
  simp only [b3AliveM, b3TraceOK, Set.mem_inter_iff, Set.mem_ofPred_eq]
  refine and_congr ?_ (forall_congr' fun i' => imp_congr_right fun h1 => imp_congr_right
    fun h2 => ?_)
  · exact hcap
  · rw [b3ClosedGramAt_rho s h τ m h1 (h2.trans hij) hV]

end BlockBand.SourceProcess.PhysApprox.B3.Modul
