module

public import BlockBand.Native.ErdosRiabov.MTerms.Basic

/-!
# Deterministic `M`-terms: explicit short chains

Proves `Split.ExplicitShortStatement`, the explicit forms of the short `M`-terms (as in
Erdős–Riabov, with `S → σ S`): `M_{[1,1]} = m_1`, `M_{[1,2]} = m_1 m_2 K_{12} A_1`, and for
`A_1 = S^{x_1}`, `A_2 = S^{x_2}`,
`(M_{[1,3]})_a = m_1 m_2 m_3 ∑_b (K_{13})_{ab} (K_{12} S)_{b x_1} (K_{23} S)_{b x_2}`, where
`K_{ij} = (1 - σ m_i m_j S)⁻¹`.

Setting: `n : ℕ`, profile `S` with `ProfileHyp S`, `σ ∈ [0,1]`, `m : ℕ → ℂ` with `‖m i‖ < 1`.

Main declarations: `mulVec_rowObs` (`(K S^x)_b = (K S)_{b x}`, by symmetry of `S`),
`chainTilde_one_three` (`M̃_{[1,3]} = K_{13}[(K_{12} A_1)(K_{23} A_2)]`),
`explicitShort_holds : ExplicitShortStatement`.

Proof: `chainM_self`; `chainTilde_one_step` (`M̃_{[j,j+1]} = K_{j,j+1} A_j`); for
`k = 3`, `chainTilde_recursion2` (the second form of the recursion) with the empty sum over
`Ioo 2 3`, i.e.
`M̃_{[1,3]} = K_{13}[(A_1 + σ m_1 m_2 S K_{12} A_1)(K_{23} A_2)] = K_{13}[(K_{12} A_1)(K_{23} A_2)]`.

Inputs: Mathlib; `BlockBand.Native.ErdosRiabov.Split.MTermsStatement`;
`BlockBand.Native.ErdosRiabov.MTerms.Basic`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MTerms

open BlockBand.Native.ErdosRiabov.Split Matrix Finset

variable {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}

/-- `(K S^x)_b = (K S)_{b x}` for symmetric `S` and any matrix `K`. -/
theorem mulVec_rowObs (hS : ProfileHyp S) (K : Matrix (Fin n) (Fin n) ℂ) (x : Fin n) :
    K *ᵥ rowObs S x = fun b => (K * profileC S) b x := by
  funext b
  simp only [mulVec, dotProduct, mul_apply, rowObs, profileC_apply, hS.symm x]

/-- `M̃_{[1,3]} = K_{13}[(K_{12} A_1)(K_{23} A_2)]`. -/
theorem chainTilde_one_three (hS : ProfileHyp S) {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    {m : ℕ → ℂ} (hm : ∀ i, ‖m i‖ < 1) (A : ℕ → Fin n → ℂ) :
    chainTilde σ S m A 1 3 =
      stabOp σ S (m 1 * m 3) *ᵥ
        ((stabOp σ S (m 1 * m 2) *ᵥ A 1) * (stabOp σ S (m 2 * m 3) *ᵥ A 2)) := by
  have h12 : chainTilde σ S m A 1 2 = stabOp σ S (m 1 * m 2) *ᵥ A 1 := chainTilde_one_step 1
  have h23 : chainTilde σ S m A 2 3 = stabOp σ S (m 2 * m 3) *ᵥ A 2 := chainTilde_one_step 2
  rw [chainTilde_recursion2 hS hσ hm (by norm_num : 1 + 2 ≤ 3),
    Finset.sum_eq_zero (fun i hi => by rw [Finset.mem_Ioo] at hi; omega), add_zero,
    show (1 + 1 : ℕ) = 2 from rfl, h12, h23]

/-- The explicit forms of `M_{[1,1]}`, `M_{[1,2]}` and, for `A_j = S^{x_j}`,
`M_{[1,3]}`. -/
theorem explicitShort_holds : ExplicitShortStatement := by
  intro n S hS σ hσ m hm
  have hI2 : Finset.Icc 1 2 = {1, 2} := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hI3 : Finset.Icc 1 3 = {1, 2, 3} := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  refine ⟨fun A => chainM_self 1, fun A => ?_, fun x₁ x₂ a => ?_⟩
  · have h12 : chainTilde σ S m A 1 2 = stabOp σ S (m 1 * m 2) *ᵥ A 1 := chainTilde_one_step 1
    rw [chainM_eq_smul, h12, hI2, Finset.prod_pair (by norm_num)]
  · rw [chainM_eq_smul, chainTilde_one_three hS hσ hm, hI3,
      Finset.prod_insert (by norm_num), Finset.prod_pair (by norm_num), ite_eq_left rfl,
      ite_eq_right (by norm_num : (2 : ℕ) ≠ 1), mulVec_rowObs hS, mulVec_rowObs hS]
    simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Pi.mul_apply, mul_assoc]

end BlockBand.Native.ErdosRiabov.MTerms
