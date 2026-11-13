module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.PublicScalarPolynomialNullity
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFullCompressionFatou

/-!
# Public-coordinate polynomial for full ambient compression endpoints

This module constructs the polynomial matrix obtained from all independent
public block coordinates simultaneously.  Its adjugate quadratic form in an
ambient direction is the determinant polynomial of the codimension-one
compression at a fixed endpoint; no selected-block conditioning is used.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory MvPolynomial

/-- Universal block-diagonal public noise over the flattened scalar labels. -/
def publicUniversalNoise {k : ℕ} (d : Fin k → ℕ) :
    Matrix (BlockGUE.Index d) (BlockGUE.Index d)
      (MvPolynomial (BlockGUE.PublicScalarIndex d) ℂ) := fun x y =>
  if h : x.1 = y.1 then
    MvPolynomial.rename (fun c : HermitianCoordinate (d x.1) =>
      (⟨x.1, c⟩ : BlockGUE.PublicScalarIndex d))
      (universalHermitianMatrix (d x.1) x.2 (h ▸ y.2))
  else 0

/-- Evaluating the universal public noise gives the reconstructed
block-diagonal public sample. -/
theorem map_eval_publicUniversalNoise {k : ℕ} (d : Fin k → ℕ)
    (x : BlockGUE.PublicScalarSample d) :
    (publicUniversalNoise d).map (MvPolynomial.eval fun c => (x c : ℂ)) =
      (BlockGUE.publicBlockDiagonal (BlockGUE.publicBlocksFromScalars x)).1 := by
  ext p q
  by_cases h : p.1 = q.1
  · rcases p with ⟨j, p⟩
    rcases q with ⟨l, q⟩
    simp only at h
    subst l
    simp only [publicUniversalNoise, ↓reduceDIte, Matrix.map_apply,
      MvPolynomial.eval_rename]
    have hev := congrFun (congrFun
      (eval_universalHermitianMatrix (fun c =>
        BlockGUE.publicBlockCoordinates x j
          (hermitianCoordinateEquivFin (d j) c))) p) q
    simpa [BlockGUE.publicBlockDiagonal, BlockGUE.publicBlockDiagonalRaw,
      BlockGUE.publicBlocksFromScalars, BlockGUE.publicBlockCoordinates,
      hermitianGUEBlock, hermitianOfFinCoordinates, hermitianOfCoordinates,
      Function.comp_def] using hev
  · simp [publicUniversalNoise, BlockGUE.publicBlockDiagonal,
      BlockGUE.publicBlockDiagonalRaw, h]

/-- Universal fixed-endpoint deformation matrix. -/
def publicUniversalEndpointMatrix {k : ℕ} {d : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index d)) (e : ℝ) :
    Matrix (BlockGUE.Index d) (BlockGUE.Index d)
      (MvPolynomial (BlockGUE.PublicScalarIndex d) ℂ) :=
  (A₀.1 - (e : ℂ) • (1 : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)).map
      MvPolynomial.C + publicUniversalNoise d

/-- Adjugate quadratic polynomial detecting ambient-compression
endpoint eigenvalues. -/
def publicAmbientCompressionEndpointPolynomial {k : ℕ} {d : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (u : EuclideanSpace ℂ (BlockGUE.Index d)) (e : ℝ) :
    MvPolynomial (BlockGUE.PublicScalarIndex d) ℂ :=
  ∑ i, ∑ j, MvPolynomial.C (star (WithLp.ofLp u i)) *
    (publicUniversalEndpointMatrix A₀ e).adjugate i j *
      MvPolynomial.C (WithLp.ofLp u j)

/-- Evaluation is the adjugate quadratic form of the full public
deformation shifted by the fixed endpoint. -/
theorem eval_publicAmbientCompressionEndpointPolynomial
    {k : ℕ} {d : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (u : EuclideanSpace ℂ (BlockGUE.Index d)) (e : ℝ)
    (x : BlockGUE.PublicScalarSample d) :
    MvPolynomial.eval (fun c => (x c : ℂ))
        (publicAmbientCompressionEndpointPolynomial A₀ u e) =
      star (WithLp.ofLp u) ⬝ᵥ
        (((publicBlockDeformation A₀ (BlockGUE.publicBlocksFromScalars x)).1 -
          (e : ℂ) • (1 : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)).adjugate *ᵥ
            WithLp.ofLp u) := by
  let ev : MvPolynomial (BlockGUE.PublicScalarIndex d) ℂ →+* ℂ :=
    MvPolynomial.eval fun c => (x c : ℂ)
  have hmat : (publicUniversalEndpointMatrix A₀ e).map ev =
      (publicBlockDeformation A₀ (BlockGUE.publicBlocksFromScalars x)).1 -
        (e : ℂ) • (1 : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ) := by
    have hn := map_eval_publicUniversalNoise d x
    simp only [publicUniversalEndpointMatrix, publicBlockDeformation]
    ext i j
    have hnij := congrFun (congrFun hn i) j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply]
    change ev (MvPolynomial.C (A₀.1 i j -
        (e : ℂ) • (1 : Matrix _ _ ℂ) i j) +
        publicUniversalNoise d i j) =
      A₀.1 i j + (BlockGUE.publicBlockDiagonal
        (BlockGUE.publicBlocksFromScalars x)).1 i j -
        (e : ℂ) • (1 : Matrix _ _ ℂ) i j
    rw [map_add, MvPolynomial.eval_C]
    change _ + (publicUniversalNoise d).map ev i j = _
    rw [hnij]
    abel
  have hadj := RingHom.map_adjugate ev (publicUniversalEndpointMatrix A₀ e)
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at hadj
  rw [hmat] at hadj
  rw [publicAmbientCompressionEndpointPolynomial, map_sum]
  simp only [map_sum, map_mul, MvPolynomial.eval_C, dotProduct, mulVec,
    Pi.star_apply, Finset.mul_sum, ← hadj, Matrix.map_apply]
  simp [ev, mul_assoc]

end PSSSNative.BlockBand.PSSS
