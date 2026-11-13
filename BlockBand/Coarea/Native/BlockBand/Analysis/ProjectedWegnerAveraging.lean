module

public import BlockBand.Coarea.Native.BlockBand.Analysis.ProjectedWegnerSchur
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Arbitrary-absorber one-block projected-Wegner averaging

This module performs the Tonelli/Fubini step after the deterministic Schur
bridge.  The standard-Cauchy parameter and the exposed GUE randomness are
handled jointly.  The conclusion is the sharp conditioned one-block estimate
`π C dim` for every deterministic positive-semidefinite absorber.

No physical conditional-distribution or block-exterior assembly is asserted:
`M`, `A₀`, and `Q` are explicit parameters throughout.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Filter Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder ENNReal NNReal Topology

universe u

/-- The arbitrary-absorber negative imaginary trace of one exposed GUE block. -/
def BlockGUE.absorbedTrace
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (Q : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)
    (η : ℝ) (ω : M.Ω) : ℝ :=
  -((((BlockGUE.deformed M A₀ ω : Matrix _ _ ℂ) +
    Complex.I • (Q + η • (1 : Matrix _ _ ℂ)))⁻¹).trace).im

/-- Joint real integrand in the Cauchy parameter and exposed GUE randomness. -/
def BlockGUE.weightedPoissonBackgroundIntegrand
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (Q : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)
    (hQ : Q.PosSemidef) (η : ℝ) (p : ℝ × M.Ω) : ℝ :=
  standardCauchyWeight p.1 *
    BlockGUE.poissonEigenvalueSum M
      (BlockGUE.realBackground A₀ Q hQ p.1) 0 η p.2

private theorem measurable_realBackground_deformed_prod
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (Q : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)
    (hQ : Q.PosSemidef) :
    Measurable (fun p : ℝ × M.Ω =>
      BlockGUE.deformed M (BlockGUE.realBackground A₀ Q hQ p.1) p.2) := by
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro i j
  change Measurable (fun p : ℝ × M.Ω =>
    (A₀.1 i j + (p.1 : ℂ) * Q i j) + M.G p.2 i j)
  have ht : Measurable (fun p : ℝ × M.Ω => (p.1 : ℂ) * Q i j) :=
    (Complex.measurable_ofReal.comp measurable_fst).mul measurable_const
  exact (measurable_const.add ht).add
    ((M.measurable_entry i j).comp measurable_snd)

/-- Joint measurability of the nonnegative Cauchy/Poisson integrand. -/
theorem measurable_weightedPoissonBackgroundIntegrand
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (Q : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)
    (hQ : Q.PosSemidef) (η : ℝ) :
    Measurable (BlockGUE.weightedPoissonBackgroundIntegrand M A₀ Q hQ η) := by
  unfold BlockGUE.weightedPoissonBackgroundIntegrand
  apply (show Measurable (fun p : ℝ × M.Ω => standardCauchyWeight p.1) by
    unfold standardCauchyWeight
    fun_prop).mul
  unfold BlockGUE.poissonEigenvalueSum
  apply Finset.measurable_sum
  intro i hi
  unfold centeredPoissonKernel
  have heig : Measurable (fun p : ℝ × M.Ω =>
      orderedEigenvalue
        (BlockGUE.deformed M
          (BlockGUE.realBackground A₀ Q hQ p.1) p.2) i) :=
    (measurable_orderedEigenvalue i).comp
      (measurable_realBackground_deformed_prod hd M A₀ Q hQ)
  fun_prop

/-- The joint Cauchy/Poisson integrand is pointwise nonnegative. -/
theorem weightedPoissonBackgroundIntegrand_nonneg
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (Q : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)
    (hQ : Q.PosSemidef) {η : ℝ} (hη : 0 < η)
    (p : ℝ × M.Ω) :
    0 ≤ BlockGUE.weightedPoissonBackgroundIntegrand M A₀ Q hQ η p := by
  unfold BlockGUE.weightedPoissonBackgroundIntegrand
  apply mul_nonneg
  · unfold standardCauchyWeight
    positivity
  · unfold BlockGUE.poissonEigenvalueSum
    exact Finset.sum_nonneg fun i _hi => centeredPoissonKernel_nonneg hη

/-- The joint Cauchy-parameter/exposed-randomness integrand is
Bochner integrable.  The proof uses the sharp uniform PSSS bound on every
fixed real background and domination by the integrable standard-Cauchy
density. -/
theorem integrable_weightedPoissonBackgroundIntegrand
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (Q : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)
    (hQ : Q.PosSemidef) {η : ℝ} (hη : 0 < η) :
    Integrable (BlockGUE.weightedPoissonBackgroundIntegrand M A₀ Q hQ η)
      (volume.prod M.P) := by
  let K : ℝ :=
    Real.pi * input.C * (Fintype.card (BlockGUE.Index d) : ℝ)
  have hK : 0 ≤ K :=
    mul_nonneg (mul_nonneg Real.pi_nonneg input.C_nonneg)
      (Nat.cast_nonneg _)
  have hmeas :=
    measurable_weightedPoissonBackgroundIntegrand hd M A₀ Q hQ η
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  constructor
  · filter_upwards with t
    exact
      (psss_weighted_realBackground_poisson_integrable_and_integral_le
        input hd M A₀ Q hQ t hη).1
  · have hw : Integrable standardCauchyWeight := by
      unfold standardCauchyWeight
      convert integrable_inv_one_add_sq.const_mul Real.pi⁻¹ using 1
      funext t
      field_simp [Real.pi_ne_zero]
    apply (hw.const_mul K).mono'
      hmeas.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards with t
    have hslice :=
      (psss_weighted_realBackground_poisson_integrable_and_integral_le
        input hd M A₀ Q hQ t hη).2
    have hint : 0 ≤ ∫ ω, BlockGUE.weightedPoissonBackgroundIntegrand
        M A₀ Q hQ η (t, ω) ∂M.P :=
      integral_nonneg fun ω =>
        weightedPoissonBackgroundIntegrand_nonneg
          hd M A₀ Q hQ hη (t, ω)
    rw [show (∫ ω, ‖BlockGUE.weightedPoissonBackgroundIntegrand
        M A₀ Q hQ η (t, ω)‖ ∂M.P) =
        ∫ ω, BlockGUE.weightedPoissonBackgroundIntegrand
          M A₀ Q hQ η (t, ω) ∂M.P by
      apply integral_congr_ae
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg
        (weightedPoissonBackgroundIntegrand_nonneg
          hd M A₀ Q hQ hη (t, ω))]]
    rw [Real.norm_eq_abs, abs_of_nonneg hint]
    simpa only [BlockGUE.weightedPoissonBackgroundIntegrand, K, mul_comm] using hslice

/-- Pointwise Poisson representation of the arbitrary-absorber trace, in the
joint-integrand normalization used for Fubini. -/
theorem absorbedTrace_eq_integral_weightedPoissonBackgroundIntegrand
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (Q : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)
    (hQ : Q.PosSemidef) {η : ℝ} (hη : 0 < η) (ω : M.Ω) :
    BlockGUE.absorbedTrace M A₀ Q η ω =
      ∫ t, BlockGUE.weightedPoissonBackgroundIntegrand
        M A₀ Q hQ η (t, ω) := by
  simpa [BlockGUE.absorbedTrace,
    BlockGUE.weightedPoissonBackgroundIntegrand] using
    blockGUE_absorbedTrace_eq_integral_poissonEigenvalueSum
      hd M A₀ Q hQ hη ω

/-- Fubini exchanges the exposed GUE expectation and standard-Cauchy
averaging.  Product integrability is supplied by the uniform PSSS slice
estimate rather than assumed. -/
theorem integral_absorbedTrace_eq_integral_integral_weightedPoissonBackground
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (Q : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)
    (hQ : Q.PosSemidef) {η : ℝ} (hη : 0 < η) :
    ∫ ω, BlockGUE.absorbedTrace M A₀ Q η ω ∂M.P =
      ∫ t, ∫ ω, BlockGUE.weightedPoissonBackgroundIntegrand
        M A₀ Q hQ η (t, ω) ∂M.P := by
  rw [show (∫ ω, BlockGUE.absorbedTrace M A₀ Q η ω ∂M.P) =
      ∫ ω, ∫ t, BlockGUE.weightedPoissonBackgroundIntegrand
        M A₀ Q hQ η (t, ω) ∂volume ∂M.P by
    apply integral_congr_ae
    filter_upwards with ω
    exact absorbedTrace_eq_integral_weightedPoissonBackgroundIntegrand
      hd M A₀ Q hQ hη ω]
  have hprod :=
    integrable_weightedPoissonBackgroundIntegrand
      input hd M A₀ Q hQ hη
  change Integrable (Function.uncurry (fun t ω =>
    BlockGUE.weightedPoissonBackgroundIntegrand
      M A₀ Q hQ η (t, ω))) (volume.prod M.P) at hprod
  exact (integral_integral_swap hprod).symm

/-- The conditioned arbitrary-positive-absorber one-block trace is integrable,
and its expectation obeys the exact PSSS normalization `π C dim`. -/
theorem blockGUE_absorbedTrace_integrable_and_integral_le
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (Q : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)
    (hQ : Q.PosSemidef) {η : ℝ} (hη : 0 < η) :
    Integrable (BlockGUE.absorbedTrace M A₀ Q η) M.P ∧
      ∫ ω, BlockGUE.absorbedTrace M A₀ Q η ω ∂M.P ≤
        Real.pi * input.C *
          (Fintype.card (BlockGUE.Index d) : ℝ) := by
  let F := BlockGUE.weightedPoissonBackgroundIntegrand M A₀ Q hQ η
  let K : ℝ :=
    Real.pi * input.C * (Fintype.card (BlockGUE.Index d) : ℝ)
  have hprod : Integrable F (volume.prod M.P) :=
    integrable_weightedPoissonBackgroundIntegrand
      input hd M A₀ Q hQ hη
  have habs : Integrable (BlockGUE.absorbedTrace M A₀ Q η) M.P := by
    apply hprod.integral_prod_right.congr
    filter_upwards with ω
    exact (absorbedTrace_eq_integral_weightedPoissonBackgroundIntegrand
      hd M A₀ Q hQ hη ω).symm
  refine ⟨habs, ?_⟩
  have hw : Integrable standardCauchyWeight := by
    unfold standardCauchyWeight
    convert integrable_inv_one_add_sq.const_mul Real.pi⁻¹ using 1
    funext t
    field_simp [Real.pi_ne_zero]
  have hinner : Integrable (fun t => ∫ ω, F (t, ω) ∂M.P) :=
    hprod.integral_prod_left
  have hpoint : ∀ t, (∫ ω, F (t, ω) ∂M.P) ≤
      standardCauchyWeight t * K := by
    intro t
    simpa only [F, BlockGUE.weightedPoissonBackgroundIntegrand, K] using
      (psss_weighted_realBackground_poisson_integrable_and_integral_le
        input hd M A₀ Q hQ t hη).2
  calc
    ∫ ω, BlockGUE.absorbedTrace M A₀ Q η ω ∂M.P =
        ∫ t, ∫ ω, F (t, ω) ∂M.P := by
          exact integral_absorbedTrace_eq_integral_integral_weightedPoissonBackground
            input hd M A₀ Q hQ hη
    _ ≤ ∫ t, standardCauchyWeight t * K :=
      integral_mono hinner (hw.mul_const K) hpoint
    _ = K := by
      rw [integral_mul_const, integral_standardCauchyWeight, one_mul]
    _ = Real.pi * input.C *
        (Fintype.card (BlockGUE.Index d) : ℝ) := rfl

/-- A `SingleBlockAveraging` value for one exposed GUE block with an
arbitrary deterministic positive-semidefinite absorber.  This is the analytic
one-block result only; no physical conditional law is asserted here. -/
theorem psss_absorbed_singleBlockAveraging
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (Q : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)
    (hQ : Q.PosSemidef) {η : ℝ} (hη : 0 < η) :
    SingleBlockAveraging M.P
      (fun (_j : Fin 1) => BlockGUE.absorbedTrace M A₀ Q η)
      input.C (Fintype.card (BlockGUE.Index d) : ℝ) where
  integrable _j :=
    (blockGUE_absorbedTrace_integrable_and_integral_le
      input hd M A₀ Q hQ hη).1
  nonneg _j := Filter.Eventually.of_forall fun ω => by
    exact blockGUE_absorbedTrace_nonneg hd M A₀ Q hQ hη ω
  oneBlock _j :=
    (blockGUE_absorbedTrace_integrable_and_integral_le
      input hd M A₀ Q hQ hη).2

end CoareaNative.BlockBand
