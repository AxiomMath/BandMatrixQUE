module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiRadialCountIdentity
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WegnerPositiveAbsorber

/-!
# Exact absorbed selected-block count formula

This module combines the noncommuting Cauchy representation with the
deterministic radial count identity.  The result is the pointwise
`(t, ξ)`-parameter formula needed in the first Minami reduction, before any
selected-block expectation or compression factorial weight is introduced.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- **PSSS regulated selected-block count formula.**  The absorbed trace of a
fixed selected Hermitian block is exactly the standard-Cauchy average of the
radial multiplicity count for the Hermitian slice `A + V + tQ`.  This is an
identity in `ℝ≥0∞`, so a nonnegative compression factorial weight may be
multiplied through it pointwise.  The normalizations are
`1/(π(1+t²))` and `2ηξ/(ξ²+η²)²`. -/
theorem publicGUEAbsorbedTrace_eq_lintegral_eigenCount_Ioo {N : ℕ}
    (A V : HermitianMatrix (Fin N))
    (Q : Matrix (Fin N) (Fin N) ℂ) (hQ : Q.PosSemidef)
    {eta : ℝ} (heta : 0 < eta) :
    ENNReal.ofReal (publicGUEAbsorbedTrace A V Q eta) =
      ∫⁻ t : ℝ,
        ENNReal.ofReal (standardCauchyWeight t) *
          (∫⁻ xi : ℝ in Ioi 0,
            (eigenCount
                (addHermitian (publicGUERealBackground A Q hQ t) V)
                (Ioo (-xi) xi) : ℝ≥0∞) *
              ENNReal.ofReal (poissonRadialWeight eta xi)) := by
  let F : ℝ → ℝ := fun t =>
    standardCauchyWeight t *
      (-(((((addHermitian (publicGUERealBackground A Q hQ t) V :
          HermitianMatrix (Fin N)) : Matrix (Fin N) (Fin N) ℂ) +
        Complex.I • (eta • (1 : Matrix (Fin N) (Fin N) ℂ)))⁻¹).trace).im)
  have hrepr : publicGUEAbsorbedTrace A V Q eta = ∫ t, F t := by
    rw [publicGUEAbsorbedTrace_eq_integral_orderedPoisson A V Q hQ heta]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [F]
    congr 1
    symm
    have hs :=
      neg_im_trace_nonsing_inv_sub_smul_one_add_I_eq_ordered_poisson
        (addHermitian (publicGUERealBackground A Q hQ t) V) 0 heta
    simpa [centeredPoissonKernel] using hs
  have hint : Integrable F := by
    apply (integrable_standardCauchyWeight_mul_neg_im_cauchyResolventTrace
      (A.1 + V.1) Q (A.2.add V.2) hQ heta).congr
    filter_upwards [] with t
    dsimp only [F]
    congr 2
    simp [addHermitian, publicGUERealBackground, cauchyResolventTrace,
      cauchyResolventPencil, add_assoc, add_left_comm, add_comm]
  have hnonneg (t : ℝ) : 0 ≤ F t := by
    dsimp only [F]
    apply mul_nonneg
    · unfold standardCauchyWeight
      positivity
    · have h := neg_im_trace_nonsing_inv_sub_smul_one_add_I_eq_ordered_poisson
        (addHermitian (publicGUERealBackground A Q hQ t) V) 0 heta
      have h' :
          -(((((addHermitian (publicGUERealBackground A Q hQ t) V :
              HermitianMatrix (Fin N)) : Matrix (Fin N) (Fin N) ℂ) +
            Complex.I •
              (eta • (1 : Matrix (Fin N) (Fin N) ℂ)))⁻¹).trace).im =
            ∑ i : Fin (Fintype.card (Fin N)),
              eta / ((orderedEigenvalue
                (addHermitian (publicGUERealBackground A Q hQ t) V) i) ^ 2 +
                  eta ^ 2) := by
        simpa using h
      rw [h']
      exact Finset.sum_nonneg fun i _ => by positivity
  rw [hrepr, ofReal_integral_eq_lintegral_ofReal hint]
  · apply lintegral_congr
    intro t
    rw [show ENNReal.ofReal (F t) =
        ENNReal.ofReal (standardCauchyWeight t) *
          ENNReal.ofReal
            (-(((((addHermitian (publicGUERealBackground A Q hQ t) V :
                HermitianMatrix (Fin N)) : Matrix (Fin N) (Fin N) ℂ) +
              Complex.I • (eta • (1 : Matrix (Fin N) (Fin N) ℂ)))⁻¹).trace).im) by
      dsimp only [F]
      rw [ENNReal.ofReal_mul]
      unfold standardCauchyWeight
      positivity]
    rw [negImTrace_eq_lintegral_eigenCount_Ioo
      (addHermitian (publicGUERealBackground A Q hQ t) V) heta]
  · filter_upwards with t
    exact hnonneg t

/-- Weighted pointwise form of the regulated selected-block count formula.
The finite weight is moved all the way to the auxiliary eigenvalue count,
which is the form used by rank-one compression and the
factorial-count induction. -/
theorem mul_publicGUEAbsorbedTrace_eq_lintegral_eigenCount_Ioo {N : ℕ}
    (A V : HermitianMatrix (Fin N))
    (Q : Matrix (Fin N) (Fin N) ℂ) (hQ : Q.PosSemidef)
    {eta : ℝ} (heta : 0 < eta) (w : ℝ≥0∞) (hw : w ≠ ⊤) :
    w * ENNReal.ofReal (publicGUEAbsorbedTrace A V Q eta) =
      ∫⁻ t : ℝ,
        ENNReal.ofReal (standardCauchyWeight t) *
          (∫⁻ xi : ℝ in Ioi 0,
            w *
              ((eigenCount
                  (addHermitian (publicGUERealBackground A Q hQ t) V)
                  (Ioo (-xi) xi) : ℝ≥0∞) *
                ENNReal.ofReal (poissonRadialWeight eta xi))) := by
  rw [publicGUEAbsorbedTrace_eq_lintegral_eigenCount_Ioo A V Q hQ heta]
  rw [← lintegral_const_mul' _ _ hw]
  apply lintegral_congr
  intro t
  rw [← mul_assoc, mul_comm w (ENNReal.ofReal (standardCauchyWeight t)),
    mul_assoc]
  congr 1
  rw [← lintegral_const_mul' _ _ hw]

end PSSSNative.BlockBand.PSSS
