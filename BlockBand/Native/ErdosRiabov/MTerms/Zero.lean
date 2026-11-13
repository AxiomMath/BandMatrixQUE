module

public import BlockBand.Native.ErdosRiabov.MTerms.Basic

/-!
# Deterministic `M`-terms: the `σ = 0` value

Proves `Split.ZeroStatement`:
at `σ = 0`, `M_{[1,k]} = (∏_{i=1}^k m_i) ∏_{p=1}^{k-1} A_p`.

Setting: any `n`, any real matrix `S` (no `ProfileHyp` needed), any `m : ℕ → ℂ` and
`A : ℕ → Fin n → ℂ` (no bound on `‖m i‖` needed).

Main declarations: `stabOp_zero` (`(1 - 0·a S)⁻¹ = 1`), `chainTilde_zero`
(`M̃_{[j,k]} = ∏_{p=j}^{k-1} A_p` at `σ = 0`, all `j, k`), `zero_holds : ZeroStatement`.

Inputs: Mathlib; `BlockBand.Native.ErdosRiabov.Split.MTermsStatement`;
`BlockBand.Native.ErdosRiabov.MTerms.Basic` (`chainTilde_of_lt`, `chainTilde_of_le`,
`chainM_eq_smul`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MTerms

open BlockBand.Native.ErdosRiabov.Split Matrix Finset

variable {n : ℕ}

/-- At `σ = 0` the stability operator is the identity (no hypotheses). -/
theorem stabOp_zero (S : Matrix (Fin n) (Fin n) ℝ) (a : ℂ) : stabOp 0 S a = 1 := by
  unfold stabOp
  rw [Complex.ofReal_zero, zero_mul, zero_smul, sub_zero, inv_one]

/-- At `σ = 0`, `M̃_{[j,k]} = ∏_{p=j}^{k-1} A_p` for all `j, k` (no hypotheses). -/
theorem chainTilde_zero (S : Matrix (Fin n) (Fin n) ℝ) (m : ℕ → ℂ) (A : ℕ → Fin n → ℂ)
    (j k : ℕ) : chainTilde 0 S m A j k = ∏ p ∈ Finset.Ico j k, A p := by
  induction hd : k - j using Nat.strong_induction_on generalizing j with
  | _ d ih =>
  rcases lt_or_ge j k with h | h
  · rw [chainTilde_of_lt h, stabOp_zero, one_mulVec,
      Finset.sum_eq_zero (fun i _ => by rw [Complex.ofReal_zero, zero_mul, zero_mul, zero_smul]),
      add_zero, ih (k - (j + 1)) (by omega) (j + 1) rfl, Finset.prod_eq_prod_Ico_succ_bot h]
  · rw [chainTilde_of_le h, Finset.Ico_eq_empty (by omega), Finset.prod_empty]
    rfl

/-- At `σ = 0`, `M_{[1,k]} = (∏_{i=1}^k m_i) ∏_{p=1}^{k-1} A_p`. -/
theorem zero_holds : ZeroStatement := by
  intro n S m A k _
  rw [chainM_eq_smul, chainTilde_zero]

end BlockBand.Native.ErdosRiabov.MTerms
