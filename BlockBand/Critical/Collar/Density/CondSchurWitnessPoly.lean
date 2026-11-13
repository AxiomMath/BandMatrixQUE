module

public import BlockBand.Critical.Collar.Density.CondSchurGram
public import BlockBand.Critical.Collar.Density.CondSchurAnalysis

/-!
# Conditional Schur identity: WitnessPoly

Part of the proof of the conditional Schur identity in the collar density lemma: the top
density, averaged first over `G`, is exactly `TΣ_F(0)T*`.

Polynomial matrices of `B`, `B*` and `D = A - e - X` in the Gaussian coordinates of the
common-port layer, and the witness coordinates.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix MeasureTheory Filter ProbabilityTheory
open BlockBand.Internal.Contracts.Layers
open scoped ComplexConjugate ComplexOrder ENNReal NNReal

variable {W : ℕ}

/-!
## Polynomial matrices in the Gaussian coordinates
-/

/-- Bond coordinates of the common-port layer. -/
abbrev BondCoord (W : ℕ) := Fin 2 × (Fin 1 × (Fin W × Fin W × Fin 2))

/-- `B` as a polynomial matrix in the bond coordinates. -/
def bondPoly (W : ℕ) : Matrix (Fin 2 × Fin W) (Fin 1 × Fin W) (MvPolynomial (BondCoord W) ℂ) :=
  Matrix.of fun p q => MvPolynomial.X (p.1, q.1, p.2, q.2, 0) +
    MvPolynomial.X (p.1, q.1, p.2, q.2, 1) * MvPolynomial.C Complex.I

/-- `B*` as a polynomial matrix in the bond coordinates. -/
def bondPolyH (W : ℕ) : Matrix (Fin 1 × Fin W) (Fin 2 × Fin W) (MvPolynomial (BondCoord W) ℂ) :=
  Matrix.of fun q p => MvPolynomial.X (p.1, q.1, p.2, q.2, 0) -
    MvPolynomial.X (p.1, q.1, p.2, q.2, 1) * MvPolynomial.C Complex.I

theorem bondPoly_map_eval (r : BondCoord W → ℝ) :
    (bondPoly W).map (MvPolynomial.eval fun i => (r i : ℂ)) =
      bondMatrix .common (BlockBand.Layers.bondAssemble r) := by
  ext p q
  simp [bondPoly, bondMatrix, LayerShape.incident, BlockBand.Layers.bondAssemble,
    BlockBand.Layers.ginibreAssemble]

theorem bondPolyH_map_eval (r : BondCoord W → ℝ) :
    (bondPolyH W).map (MvPolynomial.eval fun i => (r i : ℂ)) =
      (bondMatrix .common (BlockBand.Layers.bondAssemble r))ᴴ := by
  ext q p
  simp [bondPolyH, bondMatrix, LayerShape.incident, BlockBand.Layers.bondAssemble,
    BlockBand.Layers.ginibreAssemble, Complex.conj_ofReal]
  ring

theorem srecTopPoly_map_eval (t : ℝ≥0) (N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (x : Fin 2 × BlockBand.Layers.GaussCoord W → ℝ) :
    (BlockBand.Layers.srecTopPoly W 2 t N).map (MvPolynomial.eval fun i => (x i : ℂ)) =
      BlockBand.Internal.Contracts.Layers.blockDiag
        (BlockBand.Layers.pgBlocksOfCoords W 2 t x) + N := by
  ext p q
  simp only [Matrix.map_apply, BlockBand.Layers.srecTopPoly, map_add, MvPolynomial.eval_C,
    Matrix.add_apply, BlockBand.Internal.Contracts.Layers.blockDiag]
  split_ifs with h
  · rw [BlockBand.Layers.eval_pgGuePoly]
  · simp

theorem csGram_map {σ m n : Type} [Fintype m] [Fintype n] (f : MvPolynomial σ ℂ →+* ℂ)
    (P : Matrix m m (MvPolynomial σ ℂ)) (Q : Matrix m n (MvPolynomial σ ℂ))
    (R : Matrix n m (MvPolynomial σ ℂ)) :
    (Q * R + P * (Q * R) * P).map f = Q.map f * R.map f + P.map f * (Q.map f * R.map f) * P.map f := by
  rw [Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
    Matrix.map_mul]

/-!
## The witness
-/

/-- Witness bonds `B₁ = B₂ = I`. -/
def bondWitness (W : ℕ) : BondCoord W → ℝ :=
  fun i => if i.2.2.1 = i.2.2.2.1 ∧ i.2.2.2.2 = 0 then 1 else 0

theorem bondMatrix_bondWitness_apply (p : Fin 2 × Fin W) (q : Fin 1 × Fin W) :
    bondMatrix .common (BlockBand.Layers.bondAssemble (bondWitness W)) p q =
      if p.2 = q.2 then 1 else 0 := by
  simp only [bondMatrix, LayerShape.incident, ite_true, BlockBand.Layers.bondAssemble,
    BlockBand.Layers.ginibreAssemble, bondWitness, Matrix.of_apply]
  split_ifs <;> simp_all

/-- The witness end blocks `A₁ = λ I`, `A₂ = 0` in GUE coordinates. -/
def blockWitness (W : ℕ) (s : ℝ) : Fin 2 × BlockBand.Layers.GaussCoord W → ℝ :=
  fun i => if i.2.1.1 = i.2.1.2 ∧ i.2.2 = 0 then (if i.1 = 0 then s else 0) else 0

theorem pgBlocksOfCoords_blockWitness (t : ℝ≥0) (s : ℝ) (k : Fin 2) :
    BlockBand.Layers.pgBlocksOfCoords W 2 t (blockWitness W s) k =
      ((Real.sqrt ((t : ℝ) / 2) : ℂ) * (2 / (Real.sqrt 2 : ℂ)) * (if k = 0 then s else 0)) • 1 := by
  have h : BlockBand.Layers.pgBlocksOfCoords W 2 t (blockWitness W s) k =
      BlockBand.Layers.pgBlocksOfCoords W 2 t
        (BlockBand.Layers.pgWitness W 2 (if k = 0 then s else 0)) k := by
    simp only [BlockBand.Layers.pgBlocksOfCoords]
    congr 1
  rw [h, BlockBand.Layers.pgBlocksOfCoords_witness]

end BlockBand.Critical.Collar.Density
