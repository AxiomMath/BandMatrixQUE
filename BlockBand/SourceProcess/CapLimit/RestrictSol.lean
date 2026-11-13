module

public import BlockBand.SourceProcess.CapLimit.ZeroCol
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankCorOn

/-!
# Restricting a born Gram solution on an `𝓖₀`-event

`isBornGramSolution_restrict`: let `G` be a born Gram solution for the signature `D`, `r` an
injective column map such that `D` does not couple the range of `r` with its complement, and
`A ∈ 𝓖₀` with `Q A ≠ 0` such that a.s. on `A` the state vanishes outside the range of `r` at all
times. Then the restriction is a born Gram solution under `Q[|A]` for `D.submatrix r r`, with the
restricted jumps. The martingales are those of the full solution (`martingale_cond`); the
compensated processes and trace stops agree pathwise on `A`.

In particular, the restriction to the first `K` columns is a cap-`K` model for the conditioned
entrance: the drift and covariance entries and `g` do not see zero columns, and feasibility
restricts.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapLimit

open MeasureTheory ProbabilityTheory Function
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal ENNReal

variable {Ω : Type*} {c₁ c₂ : Type*} [Fintype c₁] [DecidableEq c₁] [Fintype c₂]
  [DecidableEq c₂] {r : c₁ → c₂} {D0 : ℝ} {D : Matrix c₂ c₂ ℂ} {J G : ℝ≥0 → Ω → GramState c₂}

/-- The restricted process. -/
def pRestrict (r : c₁ → c₂) (G : ℝ≥0 → Ω → GramState c₂) : ℝ≥0 → Ω → GramState c₁ :=
  fun t ω => gRestrict r (G t ω)

omit [DecidableEq c₁] [DecidableEq c₂] in
theorem gramTraceStop_pRestrict (hr : Injective r) {ω : Ω} (hZ : ∀ t, GSupp r (G t ω))
    (L : ℝ) : gramTraceStop (pRestrict r G) L ω = gramTraceStop G L ω := by
  unfold gramTraceStop pRestrict
  simp only [trace_gRestrict hr (hZ _).1]

theorem bornCompensated_pRestrict (hr : Injective r) (hD : Sep r D) {ω : Ω}
    (hZ : ∀ t, GSupp r (G t ω)) (e : Fin 2 × c₁ × c₁) (t : ℝ≥0) :
    bornCompensated D0 (D.submatrix r r) (pRestrict r G) (pRestrict r J) e t ω =
      bornCompensated D0 D G J (eMap r e) t ω := by
  unfold bornCompensated pRestrict
  simp only [← gRestrict_sub, gramEntry_gRestrict, gramDriftEntry_gRestrict hr D0 hD (hZ _).1]

theorem stopped_compensated_pRestrict (hr : Injective r) (hD : Sep r D) {ω : Ω}
    (hZ : ∀ t, GSupp r (G t ω)) (L : ℝ) (e : Fin 2 × c₁ × c₁) (t : ℝ≥0) :
    stoppedProcess (bornCompensated D0 (D.submatrix r r) (pRestrict r G) (pRestrict r J) e)
        (gramTraceStop (pRestrict r G) L) t ω =
      stoppedProcess (bornCompensated D0 D G J (eMap r e)) (gramTraceStop G L) t ω := by
  simp only [stoppedProcess, gramTraceStop_pRestrict hr hZ, bornCompensated_pRestrict hr hD hZ]

theorem stopped_bracket_pRestrict (hr : Injective r) (hD : Sep r D) {ω : Ω}
    (hZ : ∀ t, GSupp r (G t ω)) (L : ℝ) (e e' : Fin 2 × c₁ × c₁) (t : ℝ≥0) :
    stoppedProcess (fun t ω =>
        bornCompensated D0 (D.submatrix r r) (pRestrict r G) (pRestrict r J) e t ω *
        bornCompensated D0 (D.submatrix r r) (pRestrict r G) (pRestrict r J) e' t ω -
        ∫ s in Set.Ioc (0 : ℝ) t, gramCovEntry D0 (D.submatrix r r) e e'
          (pRestrict r G s.toNNReal ω))
        (gramTraceStop (pRestrict r G) L) t ω =
      stoppedProcess (fun t ω => bornCompensated D0 D G J (eMap r e) t ω *
        bornCompensated D0 D G J (eMap r e') t ω -
        ∫ s in Set.Ioc (0 : ℝ) t, gramCovEntry D0 D (eMap r e) (eMap r e') (G s.toNNReal ω))
        (gramTraceStop G L) t ω := by
  simp only [stoppedProcess, gramTraceStop_pRestrict hr hZ, bornCompensated_pRestrict hr hD hZ,
    pRestrict, gramCovEntry_gRestrict hr D0 hD (hZ _)]

variable [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- **The restriction of a born solution on `A` is a born solution under `Q[|A]`.** -/
theorem isBornGramSolution_restrict (hr : Injective r) (hD : Sep r D)
    (hG : IsBornGramSolution Q 𝓖 D0 D J G) {A : Set Ω} (hA : MeasurableSet[𝓖 0] A)
    (hA0 : Q A ≠ 0) (hZ : ∀ᵐ ω ∂Q, ω ∈ A → ∀ t, GSupp r (G t ω)) :
    IsBornGramSolution (Q[|A]) 𝓖 D0 (D.submatrix r r) (pRestrict r J) (pRestrict r G) where
  adapted t := continuous_gRestrict.comp_stronglyMeasurable (hG.adapted t)
  jump t := continuous_gRestrict.comp_stronglyMeasurable (hG.jump t)
  continuous := ae_cond_of_ae (hG.continuous.mono fun ω hω =>
    continuous_gRestrict.comp hω) A
  feasible := by
    refine ae_cond_of_ae_on (𝓖.le 0 _ hA) ?_
    filter_upwards [hG.feasible, hZ] with ω hf hz hωA t
    exact gramFeasible_gRestrict hr (hf t) (hz hωA t).1
  drift L e := by
    obtain ⟨N, hN, hNX⟩ := hG.drift L (eMap r e)
    refine ⟨N, martingale_cond hN hA hA0, fun t => ae_cond_of_ae_on (𝓖.le 0 _ hA) ?_⟩
    filter_upwards [hNX t, hZ] with ω hω hz hωA
    rw [hω, stopped_compensated_pRestrict hr hD (hz hωA)]
  bracket L e e' := by
    obtain ⟨N, hN, hNX⟩ := hG.bracket L (eMap r e) (eMap r e')
    refine ⟨N, martingale_cond hN hA hA0, fun t => ae_cond_of_ae_on (𝓖.le 0 _ hA) ?_⟩
    filter_upwards [hNX t, hZ] with ω hω hz hωA
    rw [hω, stopped_bracket_pRestrict hr hD (hz hωA)]

end BlockBand.SourceProcess.CapLimit
