module

public import BlockBand.SourceProcess.HorizonExt.Realize
public import BlockBand.SourceProcess.SourceProcessLaw.ModelValue
public import BlockBand.SourceProcess.Stochastic.RankBarrier.GramMinors
public import Mathlib.Analysis.Matrix.PosDef

/-!
# The square-root realization of a feasible Gram state

In `ℂ^c ⊕ ℂ^c` with the near projection `P0 = diag(1, 0)` (rank `|c|`), put
`sqrtFrame G = [B^{1/2}; (M - B)^{1/2}]`, the square roots taken by the spectral calculus
`GramChart.fcM` of the Hermitian part. For a feasible `G` the blocks `B` and `M - B` are positive
semidefinite, so `gramPair P0 (sqrtFrame G) = G` (`gramPair_sqrtFrame`) and the frame satisfies
the two-projection constraint (`twoProjection_sqrtFrame`). The map is
measurable (`measurable_sqrtFrame`): `fcM √·` is the pointwise limit of the Lipschitz maps
`fcM (√ max · (n+1)⁻¹)` (`GramChart.lipschitzWith_fcM`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.HorizonExt

open Matrix MeasureTheory Filter Topology BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open BlockBand.SourceProcess.Stochastic.RankBarrierProof
open scoped ComplexOrder

variable {c : Type} [Fintype c] [DecidableEq c]

/-- The square-root frame `[B^{1/2}; (M - B)^{1/2}]`. -/
def sqrtFrame (G : Matrix c c ℂ × Matrix c c ℂ) : Matrix (c ⊕ c) c ℂ :=
  fromRows (fcM Real.sqrt G.2) (fcM Real.sqrt (G.1 - G.2))

theorem fcM_sqrt_sq {A : Matrix c c ℂ} (hA : A.PosSemidef) :
    (fcM Real.sqrt A)ᴴ * fcM Real.sqrt A = A := by
  have hH : Aᴴ = A := hA.1
  have hA' : (hermPart A).PosSemidef := by rw [hermPart_of_herm hH]; exact hA
  rw [fcM_conjTranspose, fcM_mul_self fun i => Real.mul_self_sqrt (hA'.eigenvalues_nonneg i),
    hermPart_of_herm hH]

omit [DecidableEq c] in
theorem posSemidef_of_feasible {D : Matrix c c ℂ} {G : Matrix c c ℂ × Matrix c c ℂ}
    (hG : GramFeasible D G) : G.2.PosSemidef ∧ (G.1 - G.2).PosSemidef := by
  obtain ⟨n, P, V, hPH, hPP, -, rfl⟩ := hG
  refine ⟨?_, ?_⟩
  · simp only [gramPair]
    rw [nearGram_eq P hPH hPP]
    exact posSemidef_conjTranspose_mul_self _
  · simp only [gramPair]
    rw [farGram_eq P hPH hPP]
    exact posSemidef_conjTranspose_mul_self _

/-- **The square-root frame realizes every feasible state.** -/
theorem gramPair_sqrtFrame {D : Matrix c c ℂ} {G : Matrix c c ℂ × Matrix c c ℂ}
    (hG : GramFeasible D G) : gramPair P0 (sqrtFrame G) = G := by
  obtain ⟨h1, h2⟩ := posSemidef_of_feasible hG
  simp only [gramPair, sqrtFrame, sourceGram_fromRows, nearGram_fromRows, fcM_sqrt_sq h1,
    fcM_sqrt_sq h2, add_sub_cancel]

theorem isNearProjection_P0 : IsNearProjection (P0 (c := c)) (Fintype.card c) :=
  ⟨P0_herm, P0_idem, by simp [P0, trace, Fintype.sum_sum_type]⟩

theorem twoProjection_sqrtFrame {D : Matrix c c ℂ} (hD : IsSignature D)
    {G : Matrix c c ℂ × Matrix c c ℂ} (hG : GramFeasible D G) :
    TwoProjection P0 D (sqrtFrame G) :=
  twoProjection_of_feasible P0_herm P0_idem hD (by rwa [gramPair_sqrtFrame hG])

theorem tendsto_sqrt_max (x : ℝ) :
    Tendsto (fun n : ℕ => Real.sqrt (max x (1 / ((n : ℝ) + 1)))) atTop (𝓝 (Real.sqrt x)) := by
  have e : Real.sqrt x = Real.sqrt (max x 0) := by
    rcases le_total 0 x with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, Real.sqrt_zero, Real.sqrt_eq_zero_of_nonpos h]
  rw [e]
  exact ((Real.continuous_sqrt.comp (continuous_const.max continuous_id)).tendsto 0).comp
    tendsto_one_div_add_atTop_nhds_zero_nat

theorem tendsto_fcM_sqrt (A : Matrix c c ℂ) :
    Tendsto (fun n : ℕ => fcM (fun x => Real.sqrt (max x (1 / ((n : ℝ) + 1)))) A) atTop
      (𝓝 (fcM Real.sqrt A)) := by
  have hΦ : Continuous fun d : c → ℂ => eU A * diagonal d * star (eU A) :=
    (continuous_const.matrix_mul (continuous_id.matrix_diagonal)).matrix_mul continuous_const
  have hd : Tendsto (fun n : ℕ => fun i => ((Real.sqrt (max (eL A i) (1 / ((n : ℝ) + 1))) : ℝ) : ℂ))
      atTop (𝓝 fun i => ((Real.sqrt (eL A i) : ℝ) : ℂ)) :=
    tendsto_pi_nhds.2 fun i => (Complex.continuous_ofReal.tendsto _).comp (tendsto_sqrt_max _)
  exact (hΦ.tendsto _).comp hd

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace in
theorem continuous_fcM_sqrt_max (n : ℕ) :
    Continuous (fcM (n := c) fun x => Real.sqrt (max x (1 / ((n : ℝ) + 1)))) :=
  (lipschitzWith_fcM (lipschitzWith_sqrt_max (δ := 1 / ((n : ℝ) + 1)) (by positivity))).continuous

theorem measurable_fcM_sqrt : Measurable (fcM (n := c) Real.sqrt) := by
  have : BorelSpace (Matrix c c ℂ) := inferInstanceAs (BorelSpace (c → c → ℂ))
  have : TopologicalSpace.PseudoMetrizableSpace (Matrix c c ℂ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (c → c → ℂ))
  exact measurable_of_tendsto_metrizable (fun n => (continuous_fcM_sqrt_max n).measurable)
    (tendsto_pi_nhds.2 tendsto_fcM_sqrt)

theorem measurable_sqrtFrame : Measurable (sqrtFrame (c := c)) := by
  have : BorelSpace (Matrix c c ℂ) := inferInstanceAs (BorelSpace (c → c → ℂ))
  have : SecondCountableTopology (Matrix c c ℂ) :=
    inferInstanceAs (SecondCountableTopology (c → c → ℂ))
  have h2 : Measurable fun G : Matrix c c ℂ × Matrix c c ℂ => fcM Real.sqrt G.2 :=
    measurable_fcM_sqrt.comp measurable_snd
  have h3 : Measurable fun G : Matrix c c ℂ × Matrix c c ℂ => fcM Real.sqrt (G.1 - G.2) :=
    measurable_fcM_sqrt.comp (measurable_fst.sub measurable_snd)
  refine Measurable.of_eval fun i => ?_
  rcases i with i | i
  · exact Measurable.of_eval fun j => (measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp h2)
  · exact Measurable.of_eval fun j => (measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp h3)

end BlockBand.SourceProcess.HorizonExt
