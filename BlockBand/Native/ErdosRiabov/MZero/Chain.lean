module

public import BlockBand.Native.ErdosRiabov.Psi.Defs

/-!
# The `M`-terms at `t = 0`

Computed directly from the recursion `Split.chainTilde_eq` at profile scale `σ = 0`.
Deterministic; no measure.

* `mzero_stabOp_zero`: `(1 - 0·a S)⁻¹ = 1`;
* `mzero_chainTilde_zero`, `mzero_chainM_zero`: `M̃^{(0)}_{[j,l]} = ∏_{p=j}^{l-1} A_p` and
  `M^{(0)}_{[j,l]} = (∏_{i=j}^l m_i) ∏_{p=j}^{l-1} A_p` (all `j, l`; diagonals);
* `mzero_mChain_zero`: the pattern `M`-term at `t = 0`,
  `(M^{(0)}_{[1,k]}(x'))_{aa} = (∏_{i=1}^k m_i) ∏_{p=1}^{k-1} (S^{x_{p-1}})_{aa}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MZero

open BlockBand.Native.ErdosRiabov.Psi

variable {n : ℕ}

/-- At profile scale `0` the stability operator is the identity. -/
theorem mzero_stabOp_zero (S : Matrix (Fin n) (Fin n) ℝ) (a : ℂ) : Split.stabOp 0 S a = 1 := by
  simp [Split.stabOp]

/-- `M̃^{(0)}_{[j,l]} = ∏_{p=j}^{l-1} A_p` (by induction on `l - j`). -/
theorem mzero_chainTilde_zero (S : Matrix (Fin n) (Fin n) ℝ) (m : ℕ → ℂ) (A : ℕ → Fin n → ℂ) :
    ∀ e j l, l - j = e → Split.chainTilde 0 S m A j l = ∏ p ∈ Finset.Ico j l, A p := by
  intro e
  induction e with
  | zero =>
    intro j l h
    rw [Split.chainTilde_eq, ite_eq_right (by omega), Finset.Ico_eq_empty_of_le (by omega),
      Finset.prod_empty]
    rfl
  | succ e ih =>
    intro j l h
    rw [Split.chainTilde_eq, ite_eq_left (by omega), mzero_stabOp_zero, Matrix.one_mulVec,
      Finset.prod_eq_prod_Ico_succ_bot (by omega), ih (j + 1) l (by omega)]
    simp

/-- **The `M`-chain at `t = 0`**: `M^{(0)}_{[j,l]} = (∏_{i=j}^l m_i) ∏_{p=j}^{l-1} A_p`. -/
theorem mzero_chainM_zero (S : Matrix (Fin n) (Fin n) ℝ) (m : ℕ → ℂ) (A : ℕ → Fin n → ℂ)
    (j l : ℕ) :
    Split.chainM 0 S m A j l = (∏ i ∈ Finset.Icc j l, m i) • ∏ p ∈ Finset.Ico j l, A p := by
  rw [Split.chainM, mzero_chainTilde_zero S m A (l - j) j l rfl]

/-- The pattern `M`-term at `t = 0`:
`(M^{(0)}_{[1,k]}(x'))_{aa} = (∏_{i=1}^k m_i) ∏_{p=1}^{k-1} (A_p)_{aa}`, `A_p = S^{x_{p-1}}`. -/
theorem mzero_mChain_zero (P : PsiData n) {k : ℕ} (σ : Fin k → Bool) (x : Fin k → Fin n)
    (a : Fin n) :
    P.mChain σ x 0 a =
      (∏ i ∈ Finset.Icc 1 k, patM P.z σ i) * ∏ p ∈ Finset.Ico 1 k, obsSeq P.S x p a := by
  unfold PsiData.mChain
  rw [mzero_chainM_zero, Pi.smul_apply, smul_eq_mul, Finset.prod_apply]

end BlockBand.Native.ErdosRiabov.MZero
