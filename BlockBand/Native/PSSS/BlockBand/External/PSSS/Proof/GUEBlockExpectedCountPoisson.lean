module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEBlockPoissonRepresentation
public import BlockBand.Native.PSSS.BlockBand.Analysis.ProjectedWegnerSchur

/-!
# Endpoint inversion and canonical-block expected-count assembly

This module proves the endpoint-sensitive finite-dimensional
Perron–Stieltjes inversion, packages the projected Schur resolvent as an
explicit Hermitian background with a positive negative absorber, and gives
the finite Tonelli decomposition and unconditional dimension bound for a
deformed normalized canonical GUE block.  The final bound is intentionally
not advertised as a Wegner estimate: an interval-length estimate requires an
additional uniform positive-height truncation argument from the fixed-vector
inverse tail.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ComplexOrder ENNReal NNReal Topology

/-- Exact interval mass of one Poisson kernel, with the orientation used by
`H - x I + iη I`. -/
theorem integral_poissonKernel_shift (a b lam eta : ℝ) :
    (∫ x : ℝ in a..b, eta / ((lam - x) ^ 2 + eta ^ 2)) =
      Real.arctan ((lam - a) / eta) - Real.arctan ((lam - b) / eta) := by
  rw [show (fun x : ℝ => eta / ((lam - x) ^ 2 + eta ^ 2)) =
      (fun x : ℝ => eta / (eta ^ 2 + (lam - x) ^ 2)) by
        funext x
        rw [add_comm]]
  rw [intervalIntegral.integral_comp_sub_left
    (fun y : ℝ => eta / (eta ^ 2 + y ^ 2)) lam]
  simpa [add_comm] using
    (integral_div_sq_add_sq (a := lam - b) (b := lam - a) (c := eta))

lemma tendsto_arctan_pos_div_nhdsGT_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun eta : ℝ => Real.arctan (c / eta)) (𝓝[>] 0)
      (𝓝 (Real.pi / 2)) := by
  apply tendsto_nhds_of_tendsto_nhdsWithin
  apply Real.tendsto_arctan_atTop.comp
  have h := tendsto_inv_nhdsGT_zero.const_mul_atTop hc
  change Tendsto (fun eta : ℝ => c * eta⁻¹) (𝓝[>] 0) atTop
  exact h

lemma tendsto_arctan_neg_div_nhdsGT_zero {c : ℝ} (hc : c < 0) :
    Tendsto (fun eta : ℝ => Real.arctan (c / eta)) (𝓝[>] 0)
      (𝓝 (-(Real.pi / 2))) := by
  apply tendsto_nhds_of_tendsto_nhdsWithin
  apply Real.tendsto_arctan_atBot.comp
  change Tendsto (fun eta : ℝ => c * eta⁻¹) (𝓝[>] 0) atBot
  exact tendsto_const_nhds.neg_mul_atTop hc tendsto_inv_nhdsGT_zero

/-- Endpoint-sensitive scalar Perron–Stieltjes inversion.  The endpoint
exclusions are essential: a Poisson kernel has half mass at an endpoint. -/
theorem tendsto_normalized_integral_poissonKernel_shift
    {a b lam : ℝ} (hab : a < b) (ha : lam ≠ a) (hb : lam ≠ b) :
    Tendsto (fun eta : ℝ =>
      (1 / Real.pi) *
        (∫ x : ℝ in a..b, eta / ((lam - x) ^ 2 + eta ^ 2)))
      (𝓝[>] 0) (𝓝 (if lam ∈ Set.Icc a b then 1 else 0)) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [show (fun eta : ℝ => (1 / Real.pi) *
        (∫ x : ℝ in a..b, eta / ((lam - x) ^ 2 + eta ^ 2))) =
      (fun eta : ℝ => (1 / Real.pi) *
        (Real.arctan ((lam - a) / eta) -
          Real.arctan ((lam - b) / eta))) by
    funext eta
    rw [integral_poissonKernel_shift]]
  rcases lt_trichotomy lam a with hla | hla | hal
  · have h₁ := tendsto_arctan_neg_div_nhdsGT_zero (sub_neg.mpr hla)
    have h₂ := tendsto_arctan_neg_div_nhdsGT_zero
      (sub_neg.mpr (lt_trans hla hab))
    have h := (h₁.sub h₂).const_mul (1 / Real.pi)
    simpa [Set.mem_Icc, not_le.mpr hla] using h
  · exact (ha hla).elim
  · rcases lt_trichotomy lam b with hlb | hlb | hbl
    · have h₁ := tendsto_arctan_pos_div_nhdsGT_zero (sub_pos.mpr hal)
      have h₂ := tendsto_arctan_neg_div_nhdsGT_zero (sub_neg.mpr hlb)
      have h := (h₁.sub h₂).const_mul (1 / Real.pi)
      have hmem : lam ∈ Set.Icc a b := ⟨hal.le, hlb.le⟩
      simpa [hmem, hpi] using h
    · exact (hb hlb).elim
    · have h₁ := tendsto_arctan_pos_div_nhdsGT_zero
        (sub_pos.mpr (lt_trans hab hbl))
      have h₂ := tendsto_arctan_pos_div_nhdsGT_zero (sub_pos.mpr hbl)
      have h := (h₁.sub h₂).const_mul (1 / Real.pi)
      simpa [Set.mem_Icc, not_le.mpr hbl] using h

/-- Hermitian part of a complex square matrix. -/
def matrixHermitianPart {n : Type*} (M : Matrix n n ℂ) : Matrix n n ℂ :=
  (1 / 2 : ℂ) • (M + Mᴴ)

lemma matrixHermitianPart_isHermitian {n : Type*} (M : Matrix n n ℂ) :
    (matrixHermitianPart M).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [matrixHermitianPart]
  ring

lemma matrix_eq_hermitianPart_add_I_imaginaryPart {n : Type*}
    (M : Matrix n n ℂ) :
    M = matrixHermitianPart M + Complex.I • matrixImaginaryPart M := by
  ext i j
  simp [matrixHermitianPart, matrixImaginaryPart]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Finite-dimensional Perron–Stieltjes inversion with both endpoint atoms
excluded.  The limit is taken through positive heights and counts algebraic
multiplicity in the closed interval. -/
theorem tendsto_integral_neg_im_trace_resolvent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : HermitianMatrix ι) {a b : ℝ} (hab : a < b)
    (ha : eigenCount H {a} = 0) (hb : eigenCount H {b} = 0) :
    Tendsto (fun eta : ℝ =>
      (1 / Real.pi) * ∫ x : ℝ in a..b,
        -(((((H : Matrix ι ι ℂ) -
          (x : ℂ) • (1 : Matrix ι ι ℂ) +
          Complex.I • (eta • (1 : Matrix ι ι ℂ)))⁻¹).trace).im))
      (𝓝[>] 0) (𝓝 (eigenCount H (Set.Icc a b) : ℝ)) := by
  classical
  have ha' := (eigenCount_singleton_eq_zero_iff H a).mp ha
  have hb' := (eigenCount_singleton_eq_zero_iff H b).mp hb
  have hsum := tendsto_finsetSum Finset.univ (fun j _hj =>
    tendsto_normalized_integral_poissonKernel_shift hab (ha' j) (hb' j))
  have hlim : Tendsto (fun eta : ℝ => ∑ j : Fin (Fintype.card ι),
      (1 / Real.pi) * ∫ x : ℝ in a..b,
        eta / ((orderedEigenvalue H j - x) ^ 2 + eta ^ 2))
      (𝓝[>] 0) (𝓝 (eigenCount H (Set.Icc a b) : ℝ)) := by
    convert hsum using 1
    rw [eigenCount_def]
    simp only [Set.mem_Icc, Finset.sum_boole]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with eta heta
  have heta' : 0 < eta := heta
  have hpoint : (fun x : ℝ =>
      -(((((H : Matrix ι ι ℂ) -
        (x : ℂ) • (1 : Matrix ι ι ℂ) +
        Complex.I • (eta • (1 : Matrix ι ι ℂ)))⁻¹).trace).im)) =
      (fun x : ℝ => ∑ j : Fin (Fintype.card ι),
        eta / ((orderedEigenvalue H j - x) ^ 2 + eta ^ 2)) := by
    funext x
    exact neg_im_trace_nonsing_inv_sub_smul_one_add_I_eq_ordered_poisson
      H x heta'
  rw [hpoint]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
  · intro j _hj
    exact (continuous_const.div (by fun_prop) (fun x => by positivity)).intervalIntegrable _ _

/-- Deterministic deformation of a Hermitian sample. -/
def addHermitian {N : ℕ} (A V : HermitianMatrix (Fin N)) :
    HermitianMatrix (Fin N) := ⟨A.1 + V.1, A.2.add V.2⟩

lemma measurable_addHermitian {N : ℕ} (A : HermitianMatrix (Fin N)) :
    Measurable (addHermitian A) := by
  apply Measurable.subtype_mk
  exact (continuous_const.add continuous_subtype_val).measurable

end PSSSNative.BlockBand.PSSS
