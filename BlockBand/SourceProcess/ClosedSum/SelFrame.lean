module

public import BlockBand.SourceProcess.ClosedSum.ClosedGram
public import BlockBand.SourceProcess.EigenSel.Interface

/-!
# The time-`s` frame from a measurable eigen-selection

Deterministic algebra on a scattering matrix `S` of the two-port space and a selection `V` with
the property of `EigenSel.MeasurableEigenSelection` (orthonormal, `A·V = V·diag(eigenvalues₀)`)
for `A = T_far(S) = 1 - S_ffᴴS_ff`. The far vectors are the columns of `V(T_far)` instead of
Mathlib's `eigenvectorBasis` (`physFarVec`):

* `selVec`, `selT` (the Rayleigh quotient, `= eigenvalues₀`, `selT_eq`), `selFw`, `selF`,
  `selFrame` (current block of `curFrame` built from these);
* `selVec_eigen`, `selVec_orthonormal`, `selT_eq`, `selFw_conj_mul_self`, `farT_mul_selFw`: the
  selected vectors are orthonormal eigenvectors of `T_far`, and the corresponding identities for
  the masked block `selFw`.

Proved from these in the sibling module `SelGram`:
* **`gramPair_selFrame`** (`SSᴴ = 1`, retained `t_k < 1`): `gramPair P (selFrame) = curGramOf
  (initialGram K (Fin 0) t h)`;
* **`sub_mul_selFrame`**: `(P' - P) V_{(k,σ)} = λ_σ(t_k) V_{(k,σ)}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSum

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit

variable {W K : ℕ}

/-- The selection property for one Hermitian matrix. -/
def IsEigenSel (V : (Fin W → Fin W → ℂ) → Fin W → Fin (Fintype.card (Fin W)) → ℂ) : Prop :=
  ∀ (A : Matrix (Fin W) (Fin W) ℂ) (hA : A.IsHermitian),
    (Matrix.of (V A))ᴴ * Matrix.of (V A) = 1 ∧
      A * Matrix.of (V A) = Matrix.of (V A) * diagonal (fun k => ((hA.eigenvalues₀ k : ℝ) : ℂ))

/-- `T_far(S) = 1 - S_ffᴴ S_ff`. -/
def farT (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  1 - (portBlock S 1 1)ᴴ * portBlock S 1 1

theorem farT_isHermitian (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : (farT S).IsHermitian :=
  isHermitian_one.sub (isHermitian_conjTranspose_mul_self _)

variable (V : (Fin W → Fin W → ℂ) → Fin W → Fin (Fintype.card (Fin W)) → ℂ)

/-- The `k`-th selected far vector (`0` for `k ≥ W`). -/
def selVec (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (k : ℕ) : Fin W → ℂ :=
  if hk : k < Fintype.card (Fin W) then fun a => V (farT S) a ⟨k, hk⟩ else 0

/-- The Rayleigh quotient `t_k = ⟨v_k, T v_k⟩`. -/
def selT (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (k : ℕ) : ℝ :=
  (star (selVec V S k) ⬝ᵥ (farT S *ᵥ selVec V S k)).re

/-- The masked selected far frame. -/
def selFw (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (h : ℝ) (K : ℕ) :
    Matrix (Fin W) (Fin K) ℂ :=
  Matrix.of fun a k => if h ^ 2 < selT V S k.val then selVec V S k.val a else 0

/-- **The time-`s` frame from the selection**: the current block of `Φ V₀`. -/
def selFrame (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (h : ℝ) (K : ℕ) :
    Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ :=
  curBlock (curFrame (nearPortProj W) (Sᴴ * nearPortProj W * S) (farInj W * selFw V S h K) (Fin 0)
    (selT V S) h)

variable {V} (hV : IsEigenSel V) (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
include hV

theorem selVec_eigen {k : ℕ} (hk : k < Fintype.card (Fin W)) :
    farT S *ᵥ selVec V S k =
      (((farT_isHermitian S).eigenvalues₀ ⟨k, hk⟩ : ℝ) : ℂ) • selVec V S k := by
  have e := (hV (farT S) (farT_isHermitian S)).2
  funext a
  have := congrFun (congrFun e a) ⟨k, hk⟩
  rw [mul_diagonal, mul_apply] at this
  simp only [of_apply] at this
  simp only [selVec, hk, ↓reduceDIte, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [this, mul_comm]

theorem selVec_orthonormal {k l : ℕ} (hk : k < Fintype.card (Fin W))
    (hl : l < Fintype.card (Fin W)) :
    star (selVec V S k) ⬝ᵥ selVec V S l = if k = l then 1 else 0 := by
  have := congrFun (congrFun (hV (farT S) (farT_isHermitian S)).1 ⟨k, hk⟩) ⟨l, hl⟩
  simp only [mul_apply, conjTranspose_apply, of_apply, one_apply, Fin.mk.injEq] at this
  simp only [selVec, hk, hl, ↓reduceDIte, dotProduct, Pi.star_apply]
  rw [← this]

theorem selT_eq {k : ℕ} (hk : k < Fintype.card (Fin W)) :
    selT V S k = (farT_isHermitian S).eigenvalues₀ ⟨k, hk⟩ := by
  rw [selT, selVec_eigen hV S hk, dotProduct_smul, selVec_orthonormal hV S hk hk]
  simp

omit hV in
theorem selT_ge {k : ℕ} (hk : ¬ k < Fintype.card (Fin W)) : selT V S k = 0 := by
  simp only [selT, selVec, hk, ↓reduceDIte]
  simp

omit hV in
theorem retained_lt_card' {h : ℝ} {k : ℕ} (hk : h ^ 2 < selT V S k) :
    k < Fintype.card (Fin W) := by
  by_contra hc
  rw [selT_ge S hc] at hk
  nlinarith [sq_nonneg h]

theorem selFw_conj_mul_self (h : ℝ) :
    (selFw V S h K)ᴴ * selFw V S h K = maskDiag K (selT V S) h := by
  ext k l
  simp only [mul_apply, conjTranspose_apply, selFw, of_apply, maskDiag, diagonal_apply,
    retainMask]
  by_cases hk : h ^ 2 < selT V S k.val <;> by_cases hl : h ^ 2 < selT V S l.val
  · have e := selVec_orthonormal hV S (retained_lt_card' S hk) (retained_lt_card' S hl)
    simp only [hk, hl, ↓reduceIte, dotProduct, Pi.star_apply] at e ⊢
    rw [e]
    by_cases hkl : k = l
    · simp [hkl]
    · have : k.val ≠ l.val := fun h' => hkl (Fin.ext h')
      simp [hkl, this]
  · have hkl : k ≠ l := fun e => hl (e ▸ hk)
    simp [hk, hl, hkl]
  · have hkl : k ≠ l := fun e => hk (e ▸ hl)
    simp [hk, hl, hkl]
  · simp [hk, hl]

theorem farT_mul_selFw (h : ℝ) :
    farT S * selFw V S h K = selFw V S h K * tDiag K (selT V S) := by
  ext a k
  rw [mul_apply, mul_apply, Finset.sum_eq_single k (fun j _ hj => by simp [tDiag, hj]) (by simp)]
  simp only [selFw, of_apply, tDiag, diagonal_apply_eq]
  split_ifs with hk
  · have e := congrFun (selVec_eigen hV S (retained_lt_card' S hk)) a
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
    rw [e, selT_eq hV S (retained_lt_card' S hk), mul_comm]
  · simp

end BlockBand.SourceProcess.ClosedSum
