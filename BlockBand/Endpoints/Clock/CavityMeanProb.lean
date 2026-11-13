module

public import BlockBand.Endpoints.Clock.CavityMeanProbDeriv

/-!
# The cavity-mean lemma: the one-ended conditional mean

`CavityMeanStatement` is the cavity-mean lemma:
* (i) for `Im z' ≥ η₀`, `|z'| ≤ M`, the cavity equations (`v = f(-e - cv - bu)`,
  `u = (z' - bv)⁻¹`) have a unique solution with negative imaginary parts
  (`IsCavityMatrixSolution`), namely `(cavityV X b e z', cavityU X b e z')`;
* (ii) `|E(h₊(z') | X) - u| ≤ C W⁻²`;
* (iii) `‖h₊(z') - E(h₊(z') | X)‖_{p|X} ≤ C √p / W` for `2 ≤ p ≤ a₀ W`;
* (iv) for each fixed `k`, the same two bounds for `∂^k_{z'} h₊` and `∂^k u` (`e` fixed), with
  constants `a₀(k), C(k)`, at every point of the domain (each is interior to the domain with
  parameters `η₀/2, M + η₀/2`).

Constants depend only on `b, η₀, M` (and `k`); they are uniform in `W ≥ 1`, `X`, `e`, `z'`.
Part (ii) is in `CavityMeanProbMean`, (iii) in `CavityMeanProbFluct`, the analyticity of `u` in
`CavityMeanProbAnalytic` and (iv) in `CavityMeanProbDeriv`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal

/-- **the cavity-mean lemma**, full statement; see the module docstring. -/
def CavityMeanStatement : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ η₀ M : ℝ, 0 < η₀ →
    (∃ a₀ C : ℝ, 0 < a₀ ∧ 0 < C ∧ ∀ (W : ℕ), 0 < W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian → ∀ (e : ℝ) (z' : ℂ), η₀ ≤ z'.im → ‖z'‖ ≤ M →
        (∃! vu : ℂ × ℂ, IsCavityMatrixSolution X b (1 - 2 * b) e z' vu.1 vu.2) ∧
        IsCavityMatrixSolution X b (1 - 2 * b) e z' (cavityV X b e z') (cavityU X b e z') ∧
        ‖(∫ ω, cavityHplus e X z' ω ∂layerLaw W b .oneBlockOnePort) - cavityU X b e z'‖ ≤
          C / (W : ℝ) ^ 2 ∧
        ∀ p : ℝ, 2 ≤ p → p ≤ a₀ * W →
          eLpNorm (fun ω => cavityHplus e X z' ω -
              ∫ ω', cavityHplus e X z' ω' ∂layerLaw W b .oneBlockOnePort)
            (ENNReal.ofReal p) (layerLaw W b .oneBlockOnePort) ≤
            ENNReal.ofReal (C * Real.sqrt p / W)) ∧
    ∀ k : ℕ, ∃ a₀ C : ℝ, 0 < a₀ ∧ ∀ (W : ℕ), 0 < W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian → ∀ (e : ℝ) (z' : ℂ), η₀ ≤ z'.im → ‖z'‖ ≤ M →
        ‖(∫ ω, iteratedDeriv k (fun ζ => cavityHplus e X ζ ω) z' ∂layerLaw W b .oneBlockOnePort) -
            iteratedDeriv k (cavityU X b e) z'‖ ≤ C / (W : ℝ) ^ 2 ∧
        ∀ p : ℝ, 2 ≤ p → p ≤ a₀ * W →
          eLpNorm (fun ω => iteratedDeriv k (fun ζ => cavityHplus e X ζ ω) z' -
              ∫ ω', iteratedDeriv k (fun ζ => cavityHplus e X ζ ω') z'
                ∂layerLaw W b .oneBlockOnePort)
            (ENNReal.ofReal p) (layerLaw W b .oneBlockOnePort) ≤
            ENNReal.ofReal (C * Real.sqrt p / W)

/-- **The cavity-mean lemma** (`CavityMeanStatement`), from `GaussianAbsorptionContract` and
`TraceMatrixContract` (field `fluctuation`).
-/
theorem cavityMean_of (habs : GaussianAbsorptionContract) (htm : TraceMatrixContract) :
    CavityMeanStatement := by
  intro b hb0 hb1 η₀ M hη
  refine ⟨?_, fun k => cavityMean_deriv habs htm hb0 hb1 hη k⟩
  obtain ⟨C₂, hC₂, hmean⟩ := cavityMean_condMean habs hb0 hb1 (M := M) hη
  obtain ⟨a₀, C₃, ha₀, hfl⟩ := cavityMean_fluctuation htm hb0 hb1 (M := M) hη
  refine ⟨a₀, C₂ + max C₃ 0, ha₀, by positivity, ?_⟩
  intro W hW X hX e z' hz hzM
  have hz0 : 0 < z'.im := hη.trans_le hz
  have hc : 0 < 1 - 2 * b := by linarith
  have hsol := cavitySol_spec hW hX hb0 hb1 e hz0
  refine ⟨?_, hsol, ?_, ?_⟩
  · obtain ⟨vu, h, huniq⟩ := cavityMatrix_existsUnique (e := e) hW hX hb0 hc hz0
    refine ⟨vu, h, fun vu' h' => ?_⟩
    obtain ⟨h1, h2⟩ := huniq vu'.1 vu'.2 h'
    exact Prod.ext h1 h2
  · refine (hmean W hW X hX e z' _ _ hz hzM hsol).trans ?_
    have hWr : (0 : ℝ) < W := by exact_mod_cast hW
    rw [div_le_div_iff_of_pos_right (by positivity)]
    linarith [le_max_right C₃ 0]
  · intro p hp hpW
    refine (hfl W hW X hX e z' hz hzM p hp hpW).trans (ENNReal.ofReal_le_ofReal ?_)
    have hWr : (0 : ℝ) < W := by exact_mod_cast hW
    have : 0 ≤ Real.sqrt p / W := by positivity
    rw [mul_div_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_right ?_ this
    linarith [le_max_left C₃ 0]

/-- **The cavity-mean lemma** from `ConditionalBlockGUECount` and `GaussianLpGradient`, through
`gaussianAbsorption_holds` and `traceMatrix_holds`. -/
theorem cavityMean_of_inputs (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : Internal.Contracts.Inputs.GaussianLpGradient) : CavityMeanStatement :=
  cavityMean_of (BlockBand.Layers.gaussianAbsorption_holds hcount)
    (BlockBand.Layers.traceMatrix_holds hcount hgrad)

end BlockBand.Endpoints.Clock
