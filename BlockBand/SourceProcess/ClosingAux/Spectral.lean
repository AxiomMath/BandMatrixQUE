module

public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# No unimodular-or-larger eigenvalue implies `N^n → 0` (Gelfand's formula)

`tendsto_pow_of_eigen`: for a complex square matrix `N`, if every eigenvector equation
`N v = k v` with `1 ≤ ‖k‖` forces `v = 0`, then `N^n → 0` (entrywise topology). Proof: the
spectrum of `N` lies in the open unit disc, so its spectral radius is `< 1` (the spectrum is
compact); Gelfand's formula `‖N^n‖^{1/n} → ρ(N)` for the `L²` operator norm gives
`‖N^n‖ ≤ c^n` eventually, `c < 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosingAux

open Matrix Filter Topology
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_eigen_of_mem_spectrum {N : Matrix ι ι ℂ} {k : ℂ} (hk : k ∈ spectrum ℂ N) :
    ∃ v : ι → ℂ, v ≠ 0 ∧ N *ᵥ v = k • v := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hk
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hk
  refine ⟨v, hv, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec] at h0
  exact (sub_eq_zero.1 h0).symm

open scoped Matrix.Norms.L2Operator in
/-- The same, stated with the `L²` operator-norm instances in scope. -/
theorem tendsto_pow_of_eigen_l2 {N : Matrix ι ι ℂ}
    (hN : ∀ (k : ℂ) (v : ι → ℂ), N *ᵥ v = k • v → 1 ≤ ‖k‖ → v = 0) :
    Tendsto (fun n : ℕ => N ^ n) atTop (𝓝 0) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact tendsto_const_nhds.congr fun n => Subsingleton.elim _ _
  have hlt : ∀ k ∈ spectrum ℂ N, ‖k‖₊ < (1 : ℝ≥0) := by
    intro k hk
    obtain ⟨v, hv, hkv⟩ := exists_eigen_of_mem_spectrum hk
    by_contra h
    exact hv (hN k v hkv (by exact_mod_cast not_lt.1 h))
  have hρ : spectralRadius ℂ N < (1 : ℝ≥0) :=
    spectrum.spectralRadius_lt_of_forall_lt_of_nonempty (spectrum.nonempty N) hlt
  obtain ⟨c, hρc, hc1⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hρ
  have hc1' : (c : ℝ) < 1 := by exact_mod_cast (ENNReal.coe_lt_coe.1 hc1)
  have hG := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius N
  have hev : ∀ᶠ n : ℕ in atTop, ‖N ^ n‖ ≤ (c : ℝ) ^ n := by
    filter_upwards [hG.eventually (gt_mem_nhds hρc), eventually_ge_atTop 1] with n hn hn1
    have h1 : ‖N ^ n‖ ^ (1 / n : ℝ) < c := by
      rwa [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) ENNReal.coe_ne_top,
        ENNReal.coe_toReal] at hn
    have hn0 : n ≠ 0 := by omega
    have e : (‖N ^ n‖ ^ (1 / n : ℝ)) ^ n = ‖N ^ n‖ := by
      rw [one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hn0]
    rw [← e]
    exact pow_le_pow_left₀ (by positivity) h1.le n
  have hc : Tendsto (fun n : ℕ => (c : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one c.coe_nonneg hc1'
  exact tendsto_zero_iff_norm_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) hev hc)

/-- **Eigenvalues in the open unit disc give `N^n → 0`** (the default entrywise topology). -/
theorem tendsto_pow_of_eigen {N : Matrix ι ι ℂ}
    (hN : ∀ (k : ℂ) (v : ι → ℂ), N *ᵥ v = k • v → 1 ≤ ‖k‖ → v = 0) :
    Tendsto (fun n : ℕ => N ^ n) atTop (𝓝 0) :=
  tendsto_pow_of_eigen_l2 hN

end BlockBand.SourceProcess.ClosingAux
