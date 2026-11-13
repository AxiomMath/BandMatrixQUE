module

public import BlockBand.SourceProcess.ClosedSum.Main
public import BlockBand.SourceProcess.ClosingAux.Meas
public import BlockBand.SourceProcess.Sampling.Fubini
public import BlockBand.SourceProcess.ContractingWords.Alive

/-!
# Adaptedness of the closed Gram process (`ClosedSummed`/`ClosedTight` support)

For a frame `Vs` measurable for `growthSigma W n_s` and a length `j ≥ n_s`, the closed Gram state
`closedGramAt … j Vs` is measurable for the closed filtration `closedSigma W j p M` (path up to
`j`, samples, phase): **`measurable_closedGramAt_past`**. The filtration is monotone
(`closedSigma_mono`) and below the product σ-algebra (`closedSigma_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSumProof

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedSum
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.FullSourceStops
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.FullSource BlockBand.SourceProcess.Sampling
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers

variable {W p K M : ℕ}

/-- The closed Gram state with the time-`s` frame given as a value `V`. -/
def closedGramVal (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (W j : ℕ)
    (V : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ω : GrowthPath W)
    (km : (Fin p × Fin M → ℕ) × (Fin p × Fin M → Fin W → ℂ)) (θ : ℝ) :
    GramState (SrcCol K (Fin p × Fin M)) :=
  gramPair (nearPortProj W) ((physClosingMapAt b E s h W j ω (phase θ))ᴴ *
    openFrameAt b E s T q W j (fun _ => V) (ω, km))

theorem closedGramAt_eq_val (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (y : SampledPath W p M × ℝ) :
    closedGramAt b E s T h q W j Vs y = closedGramVal b E s T h q W j (Vs y.1.1) y.1.1 y.1.2 y.2 :=
  rfl

theorem measurable_stepProd_transportN (b E : ℝ) (j₀ : ℕ) :
    ∀ m : ℕ, Measurable fun ω : GrowthPath W => stepProd (fun i => transportN b E W i ω) j₀ m
  | 0 => measurable_const
  | m + 1 => measurable_matrix_mul' (measurable_stepProd_transportN b E j₀ m)
      (measurable_transportN b E (j₀ + m))

theorem measurable_boundaryToInterior (b E : ℝ) (n : ℕ) :
    Measurable (boundaryToInterior b E W n) :=
  Measurable.of_eval_matrix _ fun _ _ => (measurable_fullInverse b E n).eval_matrix

/-- **Joint measurability** of `closedGramVal` in the frame value, path, samples and phase. -/
theorem measurable_closedGramVal (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (W j : ℕ) :
    Measurable fun x : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ × GrowthPath W ×
        ((Fin p × Fin M → ℕ) × (Fin p × Fin M → Fin W → ℂ)) × ℝ =>
      closedGramVal b E s T h q W j x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  have hω : Measurable fun x : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ × GrowthPath W ×
      ((Fin p × Fin M → ℕ) × (Fin p × Fin M → Fin W → ℂ)) × ℝ => x.2.1 :=
    measurable_fst.comp measurable_snd
  have hC := measurable_closingMap ((measurable_scatteringMatrix b E j).comp hω)
    (measurable_farEmbed ((measurable_omittedProj b E h (closeLen s W)).comp hω))
    (measurable_farEmbed ((measurable_closingPairing b E h (closeLen s W)).comp hω))
    (measurable_phase.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hU := (measurable_boundaryToInterior b E j).comp hω
  have hX : Measurable fun x : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ × GrowthPath W ×
      ((Fin p × Fin M → ℕ) × (Fin p × Fin M → Fin W → ℂ)) × ℝ =>
      openFrameAt b E s T q W j (fun _ => x.1) (x.2.1, x.2.2.1) := by
    refine Measurable.of_eval_matrix _ fun z col => ?_
    rcases col with k | il
    · simp only [openFrameAt, of_apply, Sum.elim_inl]
      exact (measurable_matrix_mul' (measurable_matrix_conjTranspose'
        ((measurable_stepProd_transportN b E _ _).comp hω)) measurable_fst).eval_matrix
    · simp only [openFrameAt, of_apply, Sum.elim_inr]
      have hg : Measurable fun x : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ × GrowthPath W ×
          ((Fin p × Fin M → ℕ) × (Fin p × Fin M → Fin W → ℂ)) × ℝ =>
          (x.2.2.1.1 il, x.2.2.1.2 il) :=
        ((measurable_pi_apply il).comp (measurable_fst.comp (measurable_fst.comp
          (measurable_snd.comp measurable_snd)))).prodMk ((measurable_pi_apply il).comp
          (measurable_snd.comp (measurable_fst.comp (measurable_snd.comp measurable_snd))))
      have ht := (measurable_tagVector_pair W j).comp hg
      refine measurable_const.mul ?_
      simp only [mulVec, dotProduct, conjTranspose_apply, Complex.star_def]
      exact Finset.measurable_sum _ fun z' _ =>
        (Complex.continuous_conj.measurable.comp hU.eval_matrix).mul ht.eval
  have hF := measurable_matrix_mul' (measurable_matrix_conjTranspose' hC) hX
  unfold closedGramVal gramPair sourceGram nearGram
  exact (measurable_matrix_mul' (measurable_matrix_conjTranspose' hF) hF).prodMk
    (measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' hF)
      measurable_const) hF)

theorem pastCoords_extPast_le {i j : ℕ} (hij : i ≤ j) (ω : GrowthPath W) :
    pastCoords W i (extPast W j (pastCoords W j ω)) = pastCoords W i ω := by
  rw [pastCoords_restrict hij, pastCoords_extPast, ← pastCoords_restrict hij]

theorem scatteringMatrix_extPast {i j : ℕ} (hij : i ≤ j) (b E : ℝ) (ω : GrowthPath W) :
    scatteringMatrix b E W i (extPast W j (pastCoords W j ω)) = scatteringMatrix b E W i ω := by
  simp only [scatteringMatrix, boundaryResolvent, fullInverse, fullPathMatrix,
    ContractingWords.pathAt_extPast_le hij]

theorem transportN_extPast (b E : ℝ) {i j : ℕ} (hij : i < j) (ω : GrowthPath W) :
    transportN b E W i (extPast W j (pastCoords W j ω)) = transportN b E W i ω := by
  have h1 := ContractingWords.pathAt_extPast_le (W := W) (i := i) (j := j) hij.le ω
  have h2 : freshSample W i (extPast W j (pastCoords W j ω)) = freshSample W i ω := by
    simp [freshSample, extPast, pastCoords, hij]
  show freshTransport b E (pathSchur E (pathAt W i _)) (freshSample W i _) = _
  rw [h1, h2]

theorem stepProd_extPast (b E : ℝ) (j₀ : ℕ) {j : ℕ} (ω : GrowthPath W) (m : ℕ)
    (hm : j₀ + m ≤ j) :
    stepProd (fun i => transportN b E W i (extPast W j (pastCoords W j ω))) j₀ m =
      stepProd (fun i => transportN b E W i ω) j₀ m := by
  induction m with
  | zero => simp only [stepProd]
  | succ m ih => rw [stepProd, stepProd, ih (by omega), transportN_extPast b E (by omega) ω]

/-- **The closed Gram state at length `j ≥ n_s` depends on the path only through its past.** -/
theorem closedGramVal_extPast (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) {j : ℕ}
    (hj : closeLen s W ≤ j) (V : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ω : GrowthPath W)
    (km : (Fin p × Fin M → ℕ) × (Fin p × Fin M → Fin W → ℂ)) (θ : ℝ) :
    closedGramVal b E s T h q W j V (extPast W j (pastCoords W j ω)) km θ =
      closedGramVal b E s T h q W j V ω km θ := by
  have hS := scatteringMatrix_extPast (i := j) (j := j) le_rfl b E ω
  have hS' := scatteringMatrix_extPast hj b E ω
  have hR : farReflection b E W (closeLen s W) (extPast W j (pastCoords W j ω)) =
      farReflection b E W (closeLen s W) ω := by simp only [farReflection, hS']
  have hU : boundaryToInterior b E W j (extPast W j (pastCoords W j ω)) =
      boundaryToInterior b E W j ω := by
    simp only [boundaryToInterior, fullInverse, fullPathMatrix,
      ContractingWords.pathAt_extPast_le le_rfl]
  have hP := stepProd_extPast (j := j) b E (closeLen s W) ω (j - closeLen s W) (by omega)
  simp only [closedGramVal, physClosingMapAt, omittedProj, closingPairing, farTransmission, hR, hS,
    openFrameAt, hU, hP]

/-- The closed filtration is monotone. -/
theorem closedSigma_mono {i j : ℕ} (hij : i ≤ j) : closedSigma W i p M ≤ closedSigma W j p M := by
  have e : (fun y : SampledPath W p M × ℝ => (pastCoords W i y.1.1, y.1.2, y.2)) =
      (fun x => (restrictPast hij x.1, x.2)) ∘
        (fun y : SampledPath W p M × ℝ => (pastCoords W j y.1.1, y.1.2, y.2)) := rfl
  unfold closedSigma
  rw [e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono
    (((measurable_restrictPast hij).comp measurable_fst).prodMk measurable_snd).comap_le

/-- The closed filtration lies below the product σ-algebra. -/
theorem closedSigma_le (j : ℕ) :
    closedSigma W j p M ≤ (inferInstance : MeasurableSpace (SampledPath W p M × ℝ)) :=
  (((measurable_pastCoords W j).comp (measurable_fst.comp measurable_fst)).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).comap_le

/-- The generator of `closedSigma W j` is `closedSigma W j`-measurable. -/
theorem measurable_closedGen (j : ℕ) :
    Measurable[closedSigma W j p M] fun y : SampledPath W p M × ℝ =>
      (pastCoords W j y.1.1, y.1.2, y.2) :=
  comap_measurable _

/-- A `growthSigma W i`-measurable function of the path, `i ≤ j`, is `closedSigma W j`-measurable. -/
theorem measurable_closed_of_growth {β : Type*} [MeasurableSpace β] {i j : ℕ} (hij : i ≤ j)
    {f : GrowthPath W → β} (hf : Measurable[growthSigma W i] f) :
    Measurable[closedSigma W j p M] fun y : SampledPath W p M × ℝ => f y.1.1 := by
  have hpc : Measurable[closedSigma W j p M, growthSigma W i] fun y : SampledPath W p M × ℝ =>
      y.1.1 := by
    intro S hS
    obtain ⟨T, hT, rfl⟩ := hS
    exact ((measurable_restrictPast hij).comp (measurable_fst.comp (measurable_closedGen j))) hT
  exact hf.comp hpc

/-- **Adaptedness of the closed Gram process.** -/
theorem measurable_closedGramAt_past (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) {j : ℕ}
    (hj : closeLen s W ≤ j) {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : Measurable[growthSigma W (closeLen s W)] Vs) :
    Measurable[closedSigma W j p M] (closedGramAt b E s T h q W j Vs) := by
  have e : closedGramAt b E s T h q W j Vs = fun y : SampledPath W p M × ℝ =>
      closedGramVal b E s T h q W j (Vs y.1.1) (extPast W j (pastCoords W j y.1.1)) y.1.2 y.2 := by
    funext y; exact (closedGramVal_extPast b E s T h q hj _ _ _ _).symm
  rw [e]
  have hg := measurable_closedGen (W := W) (p := p) (M := M) j
  have h1 : Measurable[closedSigma W j p M] fun y : SampledPath W p M × ℝ => Vs y.1.1 :=
    measurable_closed_of_growth hj hVs
  have h2 : Measurable[closedSigma W j p M] fun y : SampledPath W p M × ℝ =>
      extPast W j (pastCoords W j y.1.1) := (measurable_extPast j).comp (measurable_fst.comp hg)
  have h3 : Measurable[closedSigma W j p M] fun y : SampledPath W p M × ℝ => y.1.2 :=
    (measurable_fst.comp measurable_snd).comp hg
  have h4 : Measurable[closedSigma W j p M] fun y : SampledPath W p M × ℝ => y.2 :=
    (measurable_snd.comp measurable_snd).comp hg
  have h5 : Measurable[closedSigma W j p M] fun y : SampledPath W p M × ℝ =>
      (Vs y.1.1, extPast W j (pastCoords W j y.1.1), y.1.2, y.2) :=
    h1.prodMk (h2.prodMk (h3.prodMk h4))
  have h6 := (measurable_closedGramVal (K := K) (M := M) b E s T h q W j).comp h5
  exact h6

end BlockBand.SourceProcess.ClosedSumProof
