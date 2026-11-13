module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

/-!
# Statements of the `M`-term algebra at profile `σ S`

The definition of the deterministic `M`-terms and the statements of their explicit short forms,
cyclicity, Ward identity, derivative and value at `σ = 0`. These are the variance-scaling forms
of the corresponding definitions and lemmas of Erdős–Riabov (arXiv 2506.06441v1; the derivative
without the Ornstein–Uhlenbeck term `k/2 · M`), at the profile `σ S` instead of `S`.

Conventions (1-based, as in ER): a chain of length `k` has spectral data `m 1, …, m k` (the
values `m(z_j)`; here arbitrary complex numbers with `‖m j‖ < 1`) and diagonal observables
`A 1, …, A (k-1)`, each a vector `Fin n → ℂ` (the diagonal of the matrix). `chainTilde σ S m A j k`
is `M̃_{[j,k]}` and `chainM σ S m A j k = (∏_{i=j}^k m i) • M̃_{[j,k]}` is `M_{[j,k]}`; both are
diagonal and are represented by their diagonal. The self-energy of a diagonal matrix with diagonal
`v` is the diagonal matrix with diagonal `S *ᵥ v`. The parameter `z_{j,σ}` is
`zParam σ (m j) = -1/m j - σ m j`.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Split

open Matrix Finset
open scoped BigOperators

variable {n : ℕ}

/-- Standing hypotheses on the profile: nonnegative, symmetric, row sums `1`. -/
structure ProfileHyp (S : Matrix (Fin n) (Fin n) ℝ) : Prop where
  nonneg : ∀ a b, 0 ≤ S a b
  symm : ∀ a b, S a b = S b a
  rowSum : ∀ a, ∑ b, S a b = 1

/-- The complexified profile. -/
def profileC (S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  S.map (fun x : ℝ => (x : ℂ))

/-- The stability operator `(1 - σ a S)⁻¹` (matrix inverse; junk value if singular). -/
def stabOp (σ : ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (a : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 - ((σ : ℂ) * a) • profileC S)⁻¹

/-- The diagonal of `S[diag v]`. -/
def selfEnergy (S : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℂ) : Fin n → ℂ :=
  profileC S *ᵥ v

/-- The diagonal observable `S^x = diag (S_{x a})_a`. -/
def rowObs (S : Matrix (Fin n) (Fin n) ℝ) (x : Fin n) : Fin n → ℂ :=
  fun a => (S x a : ℂ)

/-- `M̃_{[j,k]}` at profile `σ S` (the Erdős–Riabov recursion with `S → σ S`);
`M̃_{[j,j]} = 1`. -/
def chainTilde (σ : ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (m : ℕ → ℂ) (A : ℕ → Fin n → ℂ)
    (j k : ℕ) : Fin n → ℂ :=
  if _h : j < k then
    stabOp σ S (m j * m k) *ᵥ
      (A j * chainTilde σ S m A (j + 1) k +
        ∑ i ∈ (Finset.Ioo j k).attach,
          ((σ : ℂ) * m j * m i) •
            (selfEnergy S (chainTilde σ S m A j i) * chainTilde σ S m A i k))
  else fun _ => 1
termination_by k - j
decreasing_by
  all_goals first
    | omega
    | (have := Finset.mem_Ioo.mp i.2; omega)

/-- `M_{[j,k]} = (∏_{i=j}^k m i) • M̃_{[j,k]}`. -/
def chainM (σ : ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (m : ℕ → ℂ) (A : ℕ → Fin n → ℂ)
    (j k : ℕ) : Fin n → ℂ :=
  (∏ i ∈ Finset.Icc j k, m i) • chainTilde σ S m A j k

/-- `z_{j,σ} = -1/m_j - σ m_j`. -/
def zParam (σ : ℝ) (a : ℂ) : ℂ := -1 / a - (σ : ℂ) * a

/-- Cyclic rotation of a chain of length `k`: position `1` takes entry `k`, position `p ≥ 2`
takes entry `p - 1`. -/
def rotateChain {α : Type*} (k : ℕ) (f : ℕ → α) : ℕ → α :=
  fun p => if p = 1 then f k else f (p - 1)

/-- Remove entry `p` and shift the later entries down by one. -/
def dropAt {α : Type*} (p : ℕ) (f : ℕ → α) : ℕ → α :=
  fun i => if i < p then f i else f (i + 1)

/-- Spectral data of the glued chain `(z_1, …, z_i, z_j, …, z_k)` -/
def glueChain (i j : ℕ) (m : ℕ → ℂ) : ℕ → ℂ :=
  fun p => if p ≤ i then m p else m (p + j - i - 1)

/-- Observables of the glued chain `(A_1, …, A_{i-1}, B, A_j, …, A_{k-1})`. -/
def glueObs (i j : ℕ) (B : Fin n → ℂ) (A : ℕ → Fin n → ℂ) : ℕ → Fin n → ℂ :=
  fun p => if p < i then A p else if p = i then B else A (p + j - i - 1)

/-- Unfolding of the recursion with a plain finset sum. -/
theorem chainTilde_eq (σ : ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (m : ℕ → ℂ)
    (A : ℕ → Fin n → ℂ) (j k : ℕ) :
    chainTilde σ S m A j k =
      if j < k then
        stabOp σ S (m j * m k) *ᵥ
          (A j * chainTilde σ S m A (j + 1) k +
            ∑ i ∈ Finset.Ioo j k,
              ((σ : ℂ) * m j * m i) •
                (selfEnergy S (chainTilde σ S m A j i) * chainTilde σ S m A i k))
      else fun _ => 1 := by
  rw [chainTilde]
  split_ifs
  · rw [Finset.sum_attach (Finset.Ioo j k)
      (fun i => ((σ : ℂ) * m j * m i) •
        (selfEnergy S (chainTilde σ S m A j i) * chainTilde σ S m A i k))]
  · rfl

/-- Explicit short terms: `M_{[1,1]} = m_1`, `M_{[1,2]} = m_1 m_2 (1 - σ m_1 m_2 S)⁻¹ A_1`,
and for `A_j = S^{x_j}`:
`(M_{[1,3]})_a = m_1 m_2 m_3 ∑_b (K_{13})_{ab} (K_{12} S)_{b x_1} (K_{23} S)_{b x_2}`,
`K_{ij} = (1 - σ m_i m_j S)⁻¹`. -/
def ExplicitShortStatement : Prop :=
  ∀ (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ), ProfileHyp S →
  ∀ σ : ℝ, σ ∈ Set.Icc (0 : ℝ) 1 → ∀ m : ℕ → ℂ, (∀ i, ‖m i‖ < 1) →
    (∀ A : ℕ → Fin n → ℂ, chainM σ S m A 1 1 = fun _ => m 1) ∧
    (∀ A : ℕ → Fin n → ℂ,
      chainM σ S m A 1 2 = (m 1 * m 2) • (stabOp σ S (m 1 * m 2) *ᵥ A 1)) ∧
    (∀ x₁ x₂ : Fin n, ∀ a : Fin n,
      chainM σ S m (fun p => if p = 1 then rowObs S x₁ else rowObs S x₂) 1 3 a =
        m 1 * m 2 * m 3 * ∑ b, stabOp σ S (m 1 * m 3) a b *
          (stabOp σ S (m 1 * m 2) * profileC S) b x₁ *
          (stabOp σ S (m 2 * m 3) * profileC S) b x₂)

/-- Cyclicity at profile `σ S`, `k ≥ 2`:
`Tr[M̃(z_1, A_1, …, A_{k-1}, z_k) A_k] = Tr[A_{k-1} M̃(z_k, A_k, z_1, A_1, …, A_{k-2}, z_{k-1})]`.
-/
def CyclicStatement : Prop :=
  ∀ (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ), ProfileHyp S →
  ∀ σ : ℝ, σ ∈ Set.Icc (0 : ℝ) 1 → ∀ m : ℕ → ℂ, (∀ i, ‖m i‖ < 1) →
  ∀ (A : ℕ → Fin n → ℂ) (k : ℕ), 2 ≤ k →
    ∑ a, chainTilde σ S m A 1 k a * A k a =
      ∑ a, A (k - 1) a * chainTilde σ S (rotateChain k m) (rotateChain k A) 1 k a

/-- Divided-difference (Ward) identity at profile `σ S`: if `A_j = I`,
`1 ≤ j < k` and `m_j ≠ m_{j+1}`, then `M_{[1,k]}` equals
`(z_{j,σ} - z_{j+1,σ})⁻¹ (M(chain without z_{j+1}) - M(chain without z_j))`, where both shorter
chains drop the observable `A_j`. -/
def WardStatement : Prop :=
  ∀ (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ), ProfileHyp S →
  ∀ σ : ℝ, σ ∈ Set.Icc (0 : ℝ) 1 → ∀ m : ℕ → ℂ, (∀ i, ‖m i‖ < 1) → (∀ i, m i ≠ 0) →
  ∀ (A : ℕ → Fin n → ℂ) (k j : ℕ), 2 ≤ k → 1 ≤ j → j < k → A j = (fun _ => 1) →
    m j ≠ m (j + 1) →
    chainM σ S m A 1 k =
      (zParam σ (m j) - zParam σ (m (j + 1)))⁻¹ •
        (chainM σ S (dropAt (j + 1) m) (dropAt j A) 1 (k - 1) -
          chainM σ S (dropAt j m) (dropAt j A) 1 (k - 1))

/-- Derivative in the profile scale `σ` at fixed `m` (without the term `k/2 · M`; the
variance-scaling flow keeps `m` fixed):
`d/dσ M_{[1,k]} = ∑_{1 ≤ i < j ≤ k} ∑_q (M_{[i,j]})_{qq} M^{(q)}_{[1,i],[j,k]}`, where
`M^{(q)}_{[1,i],[j,k]} = M(z_1, A_1, …, z_i, S^q, z_j, A_j, …, z_k)` has length `k - j + i + 1`. -/
def DerivStatement : Prop :=
  ∀ (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ), ProfileHyp S →
  ∀ σ : ℝ, σ ∈ Set.Icc (0 : ℝ) 1 → ∀ m : ℕ → ℂ, (∀ i, ‖m i‖ < 1) →
  ∀ (A : ℕ → Fin n → ℂ) (k : ℕ), 1 ≤ k → ∀ a : Fin n,
    HasDerivAt (fun s : ℝ => chainM s S m A 1 k a)
      (∑ i ∈ Finset.Icc 1 k, ∑ j ∈ Finset.Ioc i k, ∑ q : Fin n,
        chainM σ S m A i j q *
          chainM σ S (glueChain i j m) (glueObs i j (rowObs S q) A) 1 (k - j + i + 1) a) σ

/-- At `σ = 0`:
`M_{[1,k]} = (∏_{i=1}^k m_i) ∏_{p=1}^{k-1} A_p` for `k ≥ 1`. -/
def ZeroStatement : Prop :=
  ∀ (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (m : ℕ → ℂ) (A : ℕ → Fin n → ℂ) (k : ℕ), 1 ≤ k →
    chainM 0 S m A 1 k = (∏ i ∈ Finset.Icc 1 k, m i) • ∏ p ∈ Finset.Ico 1 k, A p

/-- The `M`-term algebra at profile `σ S`: the five statements above. It is proved as
`MTerms.mTermAlgebra_holds`.
-/
def MTermAlgebra : Prop :=
  ExplicitShortStatement ∧ CyclicStatement ∧ WardStatement ∧ DerivStatement ∧ ZeroStatement

end BlockBand.Native.ErdosRiabov.Split
