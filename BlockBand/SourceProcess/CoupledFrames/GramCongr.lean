module

public import BlockBand.Internal.Contracts.TransmissionLaws
public import BlockBand.SourceProcess.ModelExist.TransAlg

/-!
# Born Gram solutions under indistinguishable changes

* `isBornGramSolution_congr`: an adapted process indistinguishable from a born Gram solution is
  one (every other clause is pathwise or almost sure).
* `gramPair_mul`: `gramPair P (Y L) = congrGram L (gramPair P Y)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped NNReal ENNReal
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.ModelExist

variable {Ω c : Type*} [MeasurableSpace Ω] [Fintype c] [DecidableEq c] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {D : Matrix c c ℂ}
  {J G G' : ℝ≥0 → Ω → GramState c}

omit [MeasurableSpace Ω] in
theorem bornCompensated_congr {ω : Ω} (h : ∀ t, G' t ω = G t ω) (e : Fin 2 × c × c) (t : ℝ≥0) :
    bornCompensated D0 D G' J e t ω = bornCompensated D0 D G J e t ω := by
  simp only [bornCompensated, h]

omit [MeasurableSpace Ω] [DecidableEq c] in
theorem gramTraceStop_congr {ω : Ω} (h : ∀ t, G' t ω = G t ω) (K : ℝ) :
    gramTraceStop G' K ω = gramTraceStop G K ω := by
  simp only [gramTraceStop, h]

/-- **Born Gram solutions under indistinguishable changes.** -/
theorem isBornGramSolution_congr
    (hG : IsBornGramSolution Q 𝓖 D0 D J G) (ha : ∀ t, StronglyMeasurable[𝓖 t] (G' t))
    (heq : ∀ᵐ ω ∂Q, ∀ t, G' t ω = G t ω) : IsBornGramSolution Q 𝓖 D0 D J G' := by
  refine ⟨ha, hG.jump, ?_, ?_, fun K e => ?_, fun K e e' => ?_⟩
  · filter_upwards [hG.continuous, heq] with ω h1 h2
    simpa only [h2] using h1
  · filter_upwards [hG.feasible, heq] with ω h1 h2 t
    rw [h2]; exact h1 t
  · obtain ⟨N, hN, hNe⟩ := hG.drift K e
    refine ⟨N, hN, fun t => ?_⟩
    filter_upwards [hNe t, heq] with ω h1 h2
    rw [h1, stoppedProcess, stoppedProcess, gramTraceStop_congr h2, bornCompensated_congr h2]
  · obtain ⟨N, hN, hNe⟩ := hG.bracket K e e'
    refine ⟨N, hN, fun t => ?_⟩
    filter_upwards [hNe t, heq] with ω h1 h2
    rw [h1, stoppedProcess, stoppedProcess, gramTraceStop_congr h2]
    simp only [bornCompensated_congr h2, h2]

omit [MeasurableSpace Ω] [Fintype c] [DecidableEq c] in
theorem gramPair_mul {ι c' : Type*} [Fintype ι] [Fintype c'] (P : Matrix ι ι ℂ)
    (Y : Matrix ι c' ℂ) (L : Matrix c' c ℂ) : gramPair P (Y * L) = congrGram L (gramPair P Y) := by
  simp only [gramPair, sourceGram, nearGram, congrGram, conjTranspose_mul, Matrix.mul_assoc]

end BlockBand.SourceProcess.CoupledFrames
