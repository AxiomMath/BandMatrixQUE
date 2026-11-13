module

public import BlockBand.Critical.Collar.Density.CondSchurPencil
public import BlockBand.Layers.ScalarRecursion

/-!
# Conditional Schur identity: Gram

Part of the proof of the conditional Schur identity in the collar density lemma: the top
density, averaged first over `G`, is exactly `TΣ_F(0)T*`.

The genericity Gram matrix `Γ(D, B) = BB* + D BB* D` (`det Γ ≠ 0 ⇒ CsGeneric`) and the
null-set lemma for determinants of polynomial matrices in Gaussian coordinates.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix MeasureTheory Filter ProbabilityTheory
open BlockBand.Internal.Contracts.Layers
open scoped ComplexConjugate ComplexOrder ENNReal NNReal

/-!
## The genericity Gram determinant
-/

/-- `Γ(D, B) = BB* + D BB* D`; `det Γ ≠ 0` forces genericity. -/
def csGram {m n : Type} [Fintype m] [Fintype n] (D : Matrix m m ℂ) (B : Matrix m n ℂ) :
    Matrix m m ℂ :=
  B * Bᴴ + D * (B * Bᴴ) * D

theorem csGeneric_of_det_csGram_ne_zero {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    {D : Matrix m m ℂ} {B : Matrix m n ℂ} (h : (csGram D B).det ≠ 0) : CsGeneric D B := by
  intro x v hv hBv
  by_contra hne
  apply h
  refine exists_mulVec_eq_zero_iff.1 ⟨v, hne, ?_⟩
  unfold csGram
  have h1 : (B * Bᴴ) *ᵥ v = 0 := by rw [← mulVec_mulVec, hBv, mulVec_zero]
  rw [add_mulVec, h1, zero_add, ← mulVec_mulVec, hv, mulVec_smul, ← mulVec_mulVec, h1,
    mulVec_zero, smul_zero]

/-- A polynomial matrix whose determinant is nonzero at one point has an almost surely nonzero
determinant under any law absolutely continuous with respect to Lebesgue measure. -/
theorem measure_det_eq_zero_of_poly {σ ι : Type} [Fintype σ] [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι (MvPolynomial σ ℂ)) (M : (σ → ℝ) → Matrix ι ι ℂ)
    (hM : ∀ x, P.map (MvPolynomial.eval fun i => (x i : ℂ)) = M x) (x₀ : σ → ℝ)
    (hx₀ : (M x₀).det ≠ 0) {μ : Measure (σ → ℝ)} (hμ : μ ≪ volume) :
    μ {x | (M x).det = 0} = 0 := by
  set Q := BlockBand.Parameters.mvPolynomialNormSq P.det
  have hQx : ∀ x, MvPolynomial.eval x Q = Complex.normSq (M x).det := by
    intro x
    rw [BlockBand.Parameters.eval_mvPolynomialNormSq, RingHom.map_det, RingHom.mapMatrix_apply,
      hM]
  have hQ : Q ≠ 0 := by
    intro h0
    have h := hQx x₀
    rw [h0, map_zero] at h
    exact hx₀ (Complex.normSq_eq_zero.mp h.symm)
  have hset : {x | (M x).det = 0} = {x : σ → ℝ | MvPolynomial.eval x Q = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, hQx, Complex.normSq_eq_zero]
  rw [hset]
  exact hμ (BlockBand.Parameters.volume_mvPolynomial_zeroSet_fintype Q hQ)

end BlockBand.Critical.Collar.Density
