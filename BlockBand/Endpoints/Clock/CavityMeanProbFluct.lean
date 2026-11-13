module

public import BlockBand.Endpoints.Clock.CavityMeanProbMean

/-!
# The cavity-mean lemma (iii): the conditional fluctuation `‖h₊ - E(h₊|X)‖_{p|X} ≤ C√p/W`

Almost surely `h₊(z') = W⁻¹ Tr(Q 𝒢)` with `Q` the port projection, `‖Q‖ ≤ 1`
(`ae_cavityHplus_eq_portBlockTrace`, `lct_port_eq_trace`); this is the single-resolvent trace with
one bounded insertion covered by the `fluctuation` field of `TraceMatrixContract`, applied to the
one-block, one-port shape. The constants `a₀, C` depend only on `b, η₀, M`; they are uniform in
`W ≥ 1`, Hermitian `X`, real `e`, `Im z' ≥ η₀`, `|z'| ≤ M` and `2 ≤ p ≤ a₀ W`. The norm is `L^p`
over `layerLaw W b .oneBlockOnePort` (conditional on `X`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Layers CavityMeanProb
open scoped Matrix.Norms.L2Operator ENNReal

/-- **Part (iii) of the cavity-mean lemma**, from `TraceMatrixContract.fluctuation`. For
`0 < b < 1/2`, `η₀ > 0`, `M` there are `a₀ > 0` and `C` such that for every `W ≥ 1`, Hermitian
`X`, real `e`, `Im z' ≥ η₀`, `|z'| ≤ M` and `2 ≤ p ≤ a₀ W`:
`‖h₊(z') - E(h₊(z')|X)‖_{L^p(layerLaw W b.oneBlockOnePort)} ≤ C √p / W`.
-/
theorem cavityMean_fluctuation (htm : TraceMatrixContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {η₀ M : ℝ} (hη : 0 < η₀) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧ ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      ∀ (e : ℝ) (z' : ℂ), η₀ ≤ z'.im → ‖z'‖ ≤ M →
      ∀ p : ℝ, 2 ≤ p → p ≤ a₀ * W →
        eLpNorm (fun ω => cavityHplus e X z' ω -
            ∫ ω', cavityHplus e X z' ω' ∂layerLaw W b .oneBlockOnePort)
          (ENNReal.ofReal p) (layerLaw W b .oneBlockOnePort) ≤
          ENNReal.ofReal (C * Real.sqrt p / W) := by
  obtain ⟨ε₃, C, hε₃, hfl⟩ := htm.fluctuation b hb0 hb1 η₀ M hη 1
  refine ⟨ε₃, C, hε₃, fun W hW X hX e z' hz hzM p hp hpW => ?_⟩
  have h := hfl W hW .oneBlockOnePort (cavityLift X) (cavityLift_isHermitian hX) e z' hz hzM
    (meqPortProj 0) (meq_norm_portProj_le 0) p hp hpW
  dsimp only at h
  have hae : (fun ω => cavityHplus e X z' ω) =ᵐ[layerLaw W b .oneBlockOnePort]
      (fun ω => (W : ℂ)⁻¹ * (meqPortProj 0 *
        layerResolvent .oneBlockOnePort e z' (cavityLift X) ω).trace) := by
    filter_upwards [ae_cavityHplus_eq_portBlockTrace hb1 e X z'] with ω hω
    rw [hω, lct_port_eq_trace]
  have hint := integral_congr_ae hae
  refine le_of_eq_of_le (eLpNorm_congr_ae ?_) h
  filter_upwards [hae] with ω hω
  rw [hω, hint]

/-- Part (iii) from `ConditionalBlockGUECount` and `GaussianLpGradient` (through
`traceMatrix_holds`). -/
theorem cavityMean_fluctuation_of_inputs (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : Internal.Contracts.Inputs.GaussianLpGradient) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {η₀ M : ℝ} (hη : 0 < η₀) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧ ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      ∀ (e : ℝ) (z' : ℂ), η₀ ≤ z'.im → ‖z'‖ ≤ M →
      ∀ p : ℝ, 2 ≤ p → p ≤ a₀ * W →
        eLpNorm (fun ω => cavityHplus e X z' ω -
            ∫ ω', cavityHplus e X z' ω' ∂layerLaw W b .oneBlockOnePort)
          (ENNReal.ofReal p) (layerLaw W b .oneBlockOnePort) ≤
          ENNReal.ofReal (C * Real.sqrt p / W) :=
  cavityMean_fluctuation (traceMatrix_holds hcount hgrad) hb0 hb1 hη

end BlockBand.Endpoints.Clock
