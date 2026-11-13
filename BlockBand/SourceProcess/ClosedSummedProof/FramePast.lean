module

public import BlockBand.SourceProcess.ClosedSummedProof.FreshCondE

/-!
# The closed frame is a measurable function of the closed past

* `frameVal`, `framePast j x`: the closed frame `C_j(z)ᴴX_j` read from the closed past
  `x = (pastCoords j, samples, phase)` (the path is completed by `extPast`);
* **`closedFrameAt_eq_framePast`**: for `j ≥ n_s` and a `growthSigma W n_s`-measurable `Vs`,
  `closedFrameAt j Vs y = framePast j (cpast j y)`; **`measurable_framePast`**;
* `sigVals`, `srcSignature_eq`: `𝖣 = diag(±1, 0)` as a real diagonal with entries in `[-1,1]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSummedProof

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedSum
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.FullSourceStops
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.FullSource BlockBand.SourceProcess.Sampling
open BlockBand.SourceProcess.ClosedSumProof

variable {W p K M : ℕ}

/-- The closed frame with the time-`s` frame given as a value `V`. -/
def frameVal (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (W j : ℕ)
    (V : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ω : GrowthPath W)
    (km : SampCoords W p M) (θ : ℝ) : Matrix (Fin 2 × Fin W) (SrcCol K (Fin p × Fin M)) ℂ :=
  (physClosingMapAt b E s h W j ω (phase θ))ᴴ * openFrameAt b E s T q W j (fun _ => V) (ω, km)

theorem measurable_frameVal (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (W j : ℕ) :
    Measurable fun x : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ × GrowthPath W ×
        SampCoords W p M × ℝ => frameVal b E s T h q W j x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  have hω : Measurable fun x : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ × GrowthPath W ×
      SampCoords W p M × ℝ => x.2.1 := measurable_fst.comp measurable_snd
  have hC := measurable_closingMap ((measurable_scatteringMatrix b E j).comp hω)
    (measurable_farEmbed ((measurable_omittedProj b E h (closeLen s W)).comp hω))
    (measurable_farEmbed ((measurable_closingPairing b E h (closeLen s W)).comp hω))
    (measurable_phase.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hU := (measurable_boundaryToInterior b E j).comp hω
  have hX : Measurable fun x : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ × GrowthPath W ×
      SampCoords W p M × ℝ => openFrameAt b E s T q W j (fun _ => x.1) (x.2.1, x.2.2.1) := by
    refine Measurable.of_eval_matrix _ fun z col => ?_
    rcases col with k | il
    · simp only [openFrameAt, of_apply, Sum.elim_inl]
      exact (measurable_matrix_mul' (measurable_matrix_conjTranspose'
        ((measurable_stepProd_transportN b E _ _).comp hω)) measurable_fst).eval_matrix
    · simp only [openFrameAt, of_apply, Sum.elim_inr]
      have hg : Measurable fun x : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ × GrowthPath W ×
          SampCoords W p M × ℝ => (x.2.2.1.1 il, x.2.2.1.2 il) :=
        ((measurable_pi_apply il).comp (measurable_fst.comp (measurable_fst.comp
          (measurable_snd.comp measurable_snd)))).prodMk ((measurable_pi_apply il).comp
          (measurable_snd.comp (measurable_fst.comp (measurable_snd.comp measurable_snd))))
      have ht := (measurable_tagVector_pair W j).comp hg
      refine measurable_const.mul ?_
      simp only [mulVec, dotProduct, conjTranspose_apply, Complex.star_def]
      exact Finset.measurable_sum _ fun z' _ =>
        (Complex.continuous_conj.measurable.comp hU.eval_matrix).mul ht.eval
  exact measurable_matrix_mul' (measurable_matrix_conjTranspose' hC) hX

/-- **The closed frame at `j ≥ n_s` depends on the path only through its past.** -/
theorem frameVal_extPast (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) {j : ℕ}
    (hj : closeLen s W ≤ j) (V : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ω : GrowthPath W)
    (km : SampCoords W p M) (θ : ℝ) :
    frameVal b E s T h q W j V (extPast W j (pastCoords W j ω)) km θ =
      frameVal b E s T h q W j V ω km θ := by
  have hS := scatteringMatrix_extPast (i := j) (j := j) le_rfl b E ω
  have hS' := scatteringMatrix_extPast hj b E ω
  have hR : farReflection b E W (closeLen s W) (extPast W j (pastCoords W j ω)) =
      farReflection b E W (closeLen s W) ω := by simp only [farReflection, hS']
  have hU : boundaryToInterior b E W j (extPast W j (pastCoords W j ω)) =
      boundaryToInterior b E W j ω := by
    simp only [boundaryToInterior, fullInverse, fullPathMatrix,
      ContractingWords.pathAt_extPast_le le_rfl]
  have hP := stepProd_extPast (j := j) b E (closeLen s W) ω (j - closeLen s W) (by omega)
  simp only [frameVal, physClosingMapAt, omittedProj, closingPairing, farTransmission, hR, hS,
    openFrameAt, hU, hP]

/-- A function measurable for a comap is constant on the fibres. -/
theorem eq_of_measurable_comap {α β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass β] {g : α → γ} {f : α → β}
    (hf : Measurable[MeasurableSpace.comap g inferInstance] f) {a a' : α} (h : g a = g a') :
    f a = f a' := by
  obtain ⟨S, -, hS⟩ := hf (measurableSet_singleton (f a))
  have ha : a ∈ g ⁻¹' S := by rw [hS]; rfl
  have ha' : a' ∈ g ⁻¹' S := by simpa [Set.mem_preimage, ← h] using ha
  rw [hS] at ha'
  exact ha'.symm

/-- The closed frame as a function of the closed past. -/
def framePast (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (x : ClosedPast W j p M) :
    Matrix (Fin 2 × Fin W) (SrcCol K (Fin p × Fin M)) ℂ :=
  frameVal b E s T h q W j (Vs (extPast W j x.1)) (extPast W j x.1) x.2.1 x.2.2

theorem closedFrameAt_eq_framePast (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) {j : ℕ}
    (hj : closeLen s W ≤ j) {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : Measurable[growthSigma W (closeLen s W)] Vs) (y : SampledPath W p M × ℝ) :
    closedFrameAt b E s T h q W j Vs y = framePast b E s T h q W j Vs (cpast j y) := by
  have hV : Vs (extPast W j (pastCoords W j y.1.1)) = Vs y.1.1 :=
    eq_of_measurable_comap hVs (pastCoords_extPast_le hj y.1.1)
  simp only [framePast, cpast, hV, frameVal_extPast b E s T h q hj]
  rfl

theorem measurable_framePast (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (W j : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : Measurable[growthSigma W (closeLen s W)] Vs) :
    Measurable (framePast b E s T h q W j Vs (p := p) (M := M)) := by
  have hle : growthSigma W (closeLen s W) ≤ (inferInstance : MeasurableSpace (GrowthPath W)) :=
    (measurable_pastCoords W _).comap_le
  have hV : Measurable Vs := fun S hS => hle _ (hVs hS)
  have he : Measurable fun x : ClosedPast W j p M => extPast W j x.1 :=
    (measurable_extPast j).comp measurable_fst
  have hg : Measurable fun x : ClosedPast W j p M =>
      (Vs (extPast W j x.1), extPast W j x.1, x.2.1, x.2.2) :=
    (hV.comp he).prodMk (he.prodMk
      ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)))
  have hf := (measurable_frameVal b E s T h q W j (p := p) (M := M) (K := K)).comp hg
  exact hf

/-- The signature values `±1` on current columns, `0` on probes. -/
def sigVals (K : ℕ) (π : Type) : SrcCol K π → ℝ
  | Sum.inl (_, σ) => if σ = 0 then 1 else -1
  | Sum.inr _ => 0

theorem abs_sigVals_le (K : ℕ) (π : Type) (x : SrcCol K π) : |sigVals K π x| ≤ 1 := by
  rcases x with ⟨_, σ⟩ | _
  · simp only [sigVals]; split_ifs <;> simp
  · simp [sigVals]

theorem srcSignature_eq (K : ℕ) (π : Type) [DecidableEq π] :
    srcSignature K π = sigD (sigVals K π) := by
  ext x y
  rcases x with ⟨k, σ⟩ | x <;> simp only [srcSignature, sigD, diagonal_apply] <;> split_ifs <;>
    simp_all [sigVals]

end BlockBand.SourceProcess.ClosedSummedProof
