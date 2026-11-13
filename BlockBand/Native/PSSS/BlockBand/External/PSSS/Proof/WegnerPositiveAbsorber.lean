module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WegnerSchurPerron
public import BlockBand.Native.PSSS.BlockBand.Analysis.HermitianPoissonTrace

/-!
# Positive-absorber averaging for a conditioned public GUE block

For a Hermitian background `A`, a positive semidefinite absorber `Q` and `η > 0`, the negative
imaginary trace of `(A + V + i(Q + η))⁻¹` is a Cauchy average over `t` of Poisson sums for the
Hermitian matrices `A + tQ + V`. With the single-block density of states, its expectation under
`GUE_N(1/N)` is at most `π C N`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- A real Cauchy background obtained by adding `tQ` to a Hermitian matrix. -/
def publicGUERealBackground {N : ℕ} (A : HermitianMatrix (Fin N))
    (Q : Matrix (Fin N) (Fin N) ℂ) (hQ : Q.PosSemidef) (t : ℝ) :
    HermitianMatrix (Fin N) :=
  ⟨A.1 + (t : ℂ) • Q,
    A.2.add (hQ.isHermitian.smul
      (isSelfAdjoint_iff.mpr (Complex.conj_ofReal t)))⟩

/-- Negative imaginary trace of the public GUE resolvent with a deterministic
positive absorber. -/
def publicGUEAbsorbedTrace {N : ℕ} (A V : HermitianMatrix (Fin N))
    (Q : Matrix (Fin N) (Fin N) ℂ) (eta : ℝ) : ℝ :=
  -((((A.1 + V.1) + Complex.I •
    (Q + eta • (1 : Matrix (Fin N) (Fin N) ℂ)))⁻¹).trace).im

/-- Pointwise noncommuting Cauchy representation of the absorbed trace.
Every real Cauchy slice is the ordinary ordered Poisson sum for the Hermitian
background `A + tQ`; no simultaneous diagonalization of `A` and `Q` is used. -/
theorem publicGUEAbsorbedTrace_eq_integral_orderedPoisson {N : ℕ}
    (A V : HermitianMatrix (Fin N))
    (Q : Matrix (Fin N) (Fin N) ℂ) (hQ : Q.PosSemidef)
    {eta : ℝ} (heta : 0 < eta) :
    publicGUEAbsorbedTrace A V Q eta =
      ∫ t : ℝ, standardCauchyWeight t *
        (∑ i : Fin (Fintype.card (Fin N)),
          centeredPoissonKernel 0 eta
            (orderedEigenvalue
              (addHermitian (publicGUERealBackground A Q hQ t) V) i)) := by
  unfold publicGUEAbsorbedTrace
  rw [← integral_standardCauchyWeight_mul_neg_im_real_background_resolvent
    (A.1 + V.1) Q (A.2.add V.2) hQ heta]
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  have hs := neg_im_trace_nonsing_inv_sub_smul_one_add_I_eq_ordered_poisson
    (addHermitian (publicGUERealBackground A Q hQ t) V) 0 heta
  simpa [publicGUERealBackground, addHermitian, centeredPoissonKernel,
    add_assoc, add_left_comm, add_comm] using hs

/-- **Positive-absorber estimate.** The `GUE_N(1/N)` expectation of the absorbed resolvent trace
is at most `π C N`,
uniformly in the deterministic Hermitian background, the positive-semidefinite
absorber, and the positive regulator. -/
theorem lintegral_publicGUE_absorbedTrace_le_of_singleBlockDOS {C : ℝ}
    (hC : 1 ≤ C) (h : SingleBlockDOS C) {N : ℕ} (hN : 0 < N)
    (A : HermitianMatrix (Fin N))
    (Q : Matrix (Fin N) (Fin N) ℂ) (hQ : Q.PosSemidef)
    {eta : ℝ} (heta : 0 < eta) :
    (∫⁻ V, ENNReal.ofReal (publicGUEAbsorbedTrace A V Q eta)
      ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
        Measure (HermitianMatrix (Fin N)))) ≤
      ENNReal.ofReal (Real.pi * C * N) := by
  let μ : Measure (HermitianMatrix (Fin N)) :=
    PSSSNative.BlockBand.GUE N (1 / (N : ℝ))
  let F : ℝ → HermitianMatrix (Fin N) → ℝ := fun t V =>
    standardCauchyWeight t *
      (∑ i : Fin (Fintype.card (Fin N)),
        centeredPoissonKernel 0 eta
          (orderedEigenvalue
            (addHermitian (publicGUERealBackground A Q hQ t) V) i))
  have hF_nonneg (t : ℝ) (V : HermitianMatrix (Fin N)) : 0 ≤ F t V := by
    apply mul_nonneg
    · unfold standardCauchyWeight
      positivity
    · exact Finset.sum_nonneg fun i _ => centeredPoissonKernel_nonneg heta
  have hwmeas : Measurable standardCauchyWeight := by
    unfold standardCauchyWeight
    fun_prop (discharger := intro t; positivity)
  have hF_meas : Measurable (Function.uncurry F) := by
    apply (hwmeas.comp measurable_fst).mul
    apply Finset.measurable_sum
    intro i _hi
    apply (show Measurable (centeredPoissonKernel 0 eta) by
      unfold centeredPoissonKernel
      fun_prop).comp
    apply (measurable_orderedEigenvalue i).comp
    apply Measurable.subtype_mk
    rw [Matrix.measurable_iff]
    intro x y
    simp only [publicGUERealBackground,
      Subtype.coe_mk, Matrix.add_apply, Matrix.smul_apply]
    exact (measurable_const.add
      ((Complex.continuous_ofReal.measurable.comp measurable_fst).mul
        measurable_const)).add
      ((BlockGUE.measurable_hermitianMatrix_entry x y).comp measurable_snd)
  have hrepr (V : HermitianMatrix (Fin N)) :
      publicGUEAbsorbedTrace A V Q eta = ∫ t, F t V := by
    exact publicGUEAbsorbedTrace_eq_integral_orderedPoisson A V Q hQ heta
  have hint (V : HermitianMatrix (Fin N)) :
      Integrable (fun t => F t V) volume := by
    apply (integrable_standardCauchyWeight_mul_neg_im_cauchyResolventTrace
      (A.1 + V.1) Q (A.2.add V.2) hQ heta).congr
    filter_upwards [] with t
    have hs := neg_im_trace_nonsing_inv_sub_smul_one_add_I_eq_ordered_poisson
      (addHermitian (publicGUERealBackground A Q hQ t) V) 0 heta
    simp only [F]
    congr 1
    simpa [publicGUERealBackground, addHermitian, centeredPoissonKernel,
      cauchyResolventTrace, cauchyResolventPencil, add_assoc, add_left_comm,
      add_comm] using hs
  calc
    (∫⁻ V, ENNReal.ofReal (publicGUEAbsorbedTrace A V Q eta) ∂μ) =
        ∫⁻ V, (∫⁻ t, ENNReal.ofReal (F t V) ∂volume) ∂μ := by
      apply lintegral_congr
      intro V
      rw [hrepr V, ofReal_integral_eq_lintegral_ofReal (hint V)]
      filter_upwards with t
      exact hF_nonneg t V
    _ = ∫⁻ t, (∫⁻ V, ENNReal.ofReal (F t V) ∂μ) ∂volume := by
      have hm : Measurable (Function.uncurry fun V t =>
          ENNReal.ofReal (F t V)) :=
        ENNReal.measurable_ofReal.comp
          (hF_meas.comp measurable_swap)
      exact lintegral_lintegral_swap
        (μ := μ) (ν := volume) hm.aemeasurable
    _ ≤ ∫⁻ t, ENNReal.ofReal (standardCauchyWeight t) *
        ENNReal.ofReal (Real.pi * C * N) ∂volume := by
      apply lintegral_mono
      intro t
      have hs := lintegral_publicGUE_orderedPoisson_le_of_singleBlockDOS
        hC h hN (publicGUERealBackground A Q hQ t) 0 heta
      change (∫⁻ V, ENNReal.ofReal (F t V) ∂μ) ≤ _
      simp_rw [show ∀ V, ENNReal.ofReal (F t V) =
          ENNReal.ofReal (standardCauchyWeight t) *
            ENNReal.ofReal (∑ i : Fin (Fintype.card (Fin N)),
              centeredPoissonKernel 0 eta
                (orderedEigenvalue
                  (addHermitian (publicGUERealBackground A Q hQ t) V) i)) by
        intro V
        rw [← ENNReal.ofReal_mul]
        unfold standardCauchyWeight
        positivity]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
    _ = ENNReal.ofReal (Real.pi * C * N) := by
      rw [show (fun t => ENNReal.ofReal (standardCauchyWeight t) *
          ENNReal.ofReal (Real.pi * C * N)) =
          (fun t => ENNReal.ofReal (Real.pi * C * N) *
            ENNReal.ofReal (standardCauchyWeight t)) by
        funext t
        ac_rfl]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · rw [integral_standardCauchyWeight]
        simp
      · unfold standardCauchyWeight
        convert integrable_inv_one_add_sq.const_mul Real.pi⁻¹ using 1
        funext t
        field_simp [Real.pi_ne_zero]
      · filter_upwards with t
        unfold standardCauchyWeight
        positivity

end PSSSNative.BlockBand.PSSS
