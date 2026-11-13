module

public import BlockBand.SourceProcess.FullSourceGenerator.MatchingCore

/-!
# Contraction and expansion identities for the word generator

Deterministic; letters `A`, separators `B` with `B I = 1`, `P = B P` idempotent (`OrdTable`), current
`J`, `P' = P + J`.

**The rule as a tensor.** `ruleTensor D P P' a b c d = D(P_{ad}P'_{cb} + P'_{ad}P_{cb})` is the
main part `(D₀/2W)(P⊗P' + P'⊗P)` of the covariance `E[𝓔_{ab}𝓔_{cd}]` of the full-source
covariance lemma at basis vectors (`ruleTensor_eq_crossedTensor`). Contracting the
two noise slots of `Tr(M X N Y)` against it gives `pairContraction` (`pairContraction_eq_tensor`),
and contracting `Tr(MX)Tr(NY)` gives `crossContraction` (`crossContraction_eq_tensor`); these are
the two lines of the word covariance formula.

**Expansion.** Replacing the separators at the marked positions `i < j` of a word by
`B_iXB_i` and `B_jYB_j` (the rule `B_e ↦ B_e + P^e d𝓑 P^e`) gives exactly `Tr(M_{ij}XN_{ij}Y)`
(`pair_expansion`), and one replacement gives `Tr(M_iX)` (`single_expansion`), with
`M_{ij} = B_j·(A_{j+1}B_{j+1}⋯A_iB_i)`, `N_{ij} = B_i·(A_{i+1}B_{i+1}⋯A_jB_j)` and
`M_i = B_i·(A_{i+1}B_{i+1}⋯A_iB_i)` (cyclic segments).

In the sibling module, these identities give the matching of `pairTerm`, `crossTerm`, `wordDrift` and `wordCov` with the
contractions (`pairTerm_eval`, `crossTerm_eval`, `wordDrift_eval`, `wordCov_eval`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open Matrix MvPolynomial
open BlockBand.Internal.Contracts.TransmissionStatements

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {nT nI : ℕ}

/-!
### The rule as a contraction
-/

/-- `E Tr(M d𝓑 N d𝓑) = D[Tr(MP)Tr(NP') + Tr(MP')Tr(NP)]` (first line of the word covariance). -/
def pairContraction (D : ℂ) (P P' M N : Matrix ι ι ℂ) : ℂ :=
  D * ((M * P).trace * (N * P').trace + (M * P').trace * (N * P).trace)

/-- `E Tr(M d𝓑) Tr(N d𝓑) = D[Tr(MPNP') + Tr(MP'NP)]` (second line of the word covariance). -/
def crossContraction (D : ℂ) (P P' M N : Matrix ι ι ℂ) : ℂ :=
  D * ((M * P * N * P').trace + (M * P' * N * P).trace)

/-- The rule tensor `κ_{abcd} = D(P_{ad}P'_{cb} + P'_{ad}P_{cb})`, i.e. `E[d𝓑_{ab} d𝓑_{cd}]`. -/
def ruleTensor (D : ℂ) (P P' : Matrix ι ι ℂ) (a b c d : ι) : ℂ :=
  D * (P a d * P' c b + P' a d * P c b)

/-- At basis vectors the rule tensor is `D(P⊗P' + P'⊗P)` in the crossed-tensor convention of the
full-source covariance lemma (`crossedTensor v₁ v₂ v₃ v₄ A B = (v₁*Av₄)(v₃*Bv₂)`). -/
theorem ruleTensor_eq_crossedTensor (D : ℂ) (P P' : Matrix ι ι ℂ) (a b c d : ι) :
    ruleTensor D P P' a b c d = D * (crossedTensor (Pi.single a 1) (Pi.single b 1)
      (Pi.single c 1) (Pi.single d 1) P P' + crossedTensor (Pi.single a 1) (Pi.single b 1)
        (Pi.single c 1) (Pi.single d 1) P' P) := by
  simp [ruleTensor, crossedTensor, bilinear, Matrix.mulVec_single, dotProduct, Pi.single_apply]

omit [DecidableEq ι] in
/-- Contracting `X_{ab}Y_{cd}` in `Tr(MXNY) = Σ M_{da}X_{ab}N_{bc}Y_{cd}` against the rule. -/
theorem pairContraction_eq_tensor (D : ℂ) (P P' M N : Matrix ι ι ℂ) :
    ∑ b, ∑ c, ∑ d, ∑ a, M d a * N b c * ruleTensor D P P' a b c d =
      pairContraction D P P' M N := by
  simp only [pairContraction, ruleTensor, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  congr 1 <;>
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [DecidableEq ι] in
/-- Contracting `X_{ab}Y_{cd}` in `Tr(MX)Tr(NY) = Σ M_{ba}X_{ab}N_{dc}Y_{cd}` against the rule. -/
theorem crossContraction_eq_tensor (D : ℂ) (P P' M N : Matrix ι ι ℂ) :
    ∑ b, ∑ c, ∑ d, ∑ a, M b a * N d c * ruleTensor D P P' a b c d =
      crossContraction D P P' M N := by
  simp only [crossContraction, ruleTensor, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  congr 1 <;>
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-!
### The expansion at marked separators
-/

section Expansion

variable (A : TraceLetter nT nI → Matrix ι ι ℂ) (B : Separator → Matrix ι ι ℂ)
  (L Mid R : TraceWord nT nI) (x y : TraceLetter nT nI × Separator)

/-- Two marked separators: `Tr(⋯A_i(B_iXB_i)⋯A_j(B_jYB_j)⋯) = Tr(M X N Y)`. -/
theorem pair_expansion (X Y : Matrix ι ι ℂ) :
    (segProd A B L * (A x.1 * (B x.2 * X * B x.2)) * segProd A B Mid *
        (A y.1 * (B y.2 * Y * B y.2)) * segProd A B R).trace =
      (B y.2 * segProd A B (R ++ L ++ [x]) * X * (B x.2 * segProd A B (Mid ++ [y])) *
        Y).trace := by
  simp only [segProd_append, segProd_singleton, Matrix.mul_assoc]
  iterate 3 (conv_lhs => rw [Matrix.trace_mul_comm]); simp only [Matrix.mul_assoc]
  iterate 5 (conv_rhs => rw [Matrix.trace_mul_comm]); simp only [Matrix.mul_assoc]

/-- One marked separator: `Tr(⋯A_i(B_iXB_i)⋯) = Tr(M X)`. -/
theorem single_expansion (X : Matrix ι ι ℂ) :
    (segProd A B L * (A x.1 * (B x.2 * X * B x.2)) * segProd A B R).trace =
      (B x.2 * segProd A B (R ++ L ++ [x]) * X).trace := by
  simp only [segProd_append, segProd_singleton, Matrix.mul_assoc]
  iterate 3 (conv_lhs => rw [Matrix.trace_mul_comm]); simp only [Matrix.mul_assoc]
  iterate 5 (conv_rhs => rw [Matrix.trace_mul_comm]); simp only [Matrix.mul_assoc]

end Expansion

end BlockBand.SourceProcess.FullSourceGenerator
