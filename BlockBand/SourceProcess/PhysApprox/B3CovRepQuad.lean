module

public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormJoint
public import BlockBand.SourceProcess.FullSource.WardIdentity
public import BlockBand.SourceProcess.FullSource.DeltaReduction
public import BlockBand.Transmission.PassiveLayer.PoissonLayer
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# The quadratic remainder of `U - 1` (exact form)

At a passive input `X` with `R = (z - X)⁻¹`, `Y = -Im X`, `F₁ = passiveF X = R - c₀`, and for
one fresh layer with `A` Hermitian and `B` invertible (almost surely, `PassiveLayer.ae_good`):

* **`freshQuad_eq`**: `freshQuad X = U - 1 - (ΔF₁ + (ΔF₁)*)` equals
  `-ΔQ(ΔQ)*` for every `Q` with `ηQQ* = RYR*`, i.e. `freshQuad = -ΔMΔ*`, `M = RYR*/η`
  (FullSource's `ward_algebra`, the one-port Ward identity, with `Q` a square root of `M`);
* `exists_mul_conjTranspose_eq`: every positive semidefinite matrix is `SSᴴ` (spectral theorem);
* `bilinear_mul_conjTranspose`: `x*(AAᴴ)y = Σ_k (x*a_k)·conj(y*a_k)` over the columns `a_k`;
* `trace_resolvent_sandwich`: `Tr(RYR*) = Tr(R*YR)`, so `Re Tr M = q/η = g/(4η²)`
  (`passiveMass q`, conductance `g = 4ηq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open scoped ComplexOrder

variable {W : ℕ}

/-- Every positive semidefinite complex matrix is `S Sᴴ`. -/
theorem exists_mul_conjTranspose_eq {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hM : M.PosSemidef) : ∃ S : Matrix n n ℂ, S * Sᴴ = M := by
  set hA := hM.1
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ)
  refine ⟨U * diagonal (fun i => ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ)), ?_⟩
  conv_rhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, conjTranspose_mul, diagonal_conjTranspose]
  have hd : diagonal (fun i => ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ)) *
      diagonal (star fun i => ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ)) =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, Function.comp_apply]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hM.eigenvalues_nonneg i)]
    rfl
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _) (diagonal _), hd, star_eq_conjTranspose,
    ← Matrix.mul_assoc]

/-- `x*(AAᴴ)y = Σ_k (x*a_k)·conj(y*a_k)`. -/
theorem bilinear_mul_conjTranspose {n : Type*} [Fintype n] (A : Matrix n n ℂ) (x y : n → ℂ) :
    bilinear x (A * Aᴴ) y =
      ∑ k, (star x ⬝ᵥ fun i => A i k) * star (star y ⬝ᵥ fun i => A i k) := by
  rw [bilinear, ← mulVec_mulVec, dotProduct_mulVec]
  unfold dotProduct
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  show ∑ j, (Aᴴ) k j * y j = _
  simp only [conjTranspose_apply, Pi.star_apply, star_sum, star_mul', star_star]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The columns of `ΔQ` are `Δq_k`. -/
theorem col_mul (A Q : Matrix (Fin W) (Fin W) ℂ) (k : Fin W) :
    (fun i => (A * Q) i k) = A *ᵥ fun i => Q i k := by
  funext i; simp [Matrix.mul_apply, mulVec, dotProduct]

/-- **The quadratic remainder is `-ΔQ(ΔQ)ᴴ`** for `ηQQᴴ = RYRᴴ`. -/
theorem freshQuad_eq (b E : ℝ) {X : Matrix (Fin W) (Fin W) ℂ} (hη : 0 < etaZ b E)
    (hY : (passiveY X).PosSemidef) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) (Q : Matrix (Fin W) (Fin W) ℂ)
    (hQ : passiveResolvent b E X * passiveY X * (passiveResolvent b E X)ᴴ =
      ((etaZ b E : ℝ) : ℂ) • (Q * Qᴴ)) :
    ClosedForm.freshQuad b E X ω = -(freshDelta b E X ω * Q * (freshDelta b E X ω * Q)ᴴ) := by
  set z := boundaryZ b E
  have hz : 0 < z.im := hη
  have hK : IsUnit (z • (1 : Matrix (Fin W) (Fin W) ℂ) - X) := by
    apply BlockBand.Transmission.isUnit_of_matrixImaginaryPart_posDef
    rw [BlockBand.Transmission.PassiveCovariance.matrixImaginaryPart_nearPencil]
    exact Matrix.PosDef.posSemidef_add hY (Matrix.PosDef.one.smul hη)
  have hw : freshL b E X ω * (freshL b E X ω)ᴴ +
      freshDelta b E X ω * Q * (freshDelta b E X ω * Q)ᴴ - 1 =
      freshDelta b E X ω * passiveF b E X + (passiveF b E X)ᴴ * (freshDelta b E X ω)ᴴ := by
    rw [FullSource.freshL_eq_lAt, FullSource.freshDelta_eq]
    exact FullSource.ward_algebra (BlockBand.Transmission.PassiveLayer.g11 E z X ω)
      (BlockBand.Transmission.PassiveLayer.g12 E z X ω) (z • 1 - X) (passiveY X)
      (passiveResolvent b E X) Q hη.ne' (FullSource.im_g11 E hz hY hA hB)
      (FullSource.pencil_sub_conj z X)
      (Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hK)) hQ
  unfold ClosedForm.freshQuad freshU
  rw [conjTranspose_mul]
  rw [← sub_eq_zero]
  have e : freshL b E X ω * (freshL b E X ω)ᴴ - 1 -
      (freshDelta b E X ω * passiveF b E X + (passiveF b E X)ᴴ * (freshDelta b E X ω)ᴴ) -
      -(freshDelta b E X ω * Q * (freshDelta b E X ω * Q)ᴴ) =
      (freshL b E X ω * (freshL b E X ω)ᴴ +
        freshDelta b E X ω * Q * (freshDelta b E X ω * Q)ᴴ - 1) -
      (freshDelta b E X ω * passiveF b E X + (passiveF b E X)ᴴ * (freshDelta b E X ω)ᴴ) := by
    abel
  rw [e, hw, sub_self]

/-- **`Tr(RYRᴴ) = Tr(RᴴYR)`** for `R = (z - X)⁻¹`, `Y = -Im X`. -/
theorem trace_resolvent_sandwich (b E : ℝ) {X : Matrix (Fin W) (Fin W) ℂ} (hη : 0 < etaZ b E)
    (hY : (passiveY X).PosSemidef) :
    (passiveResolvent b E X * passiveY X * (passiveResolvent b E X)ᴴ).trace =
      (passiveQ b E X).trace := by
  set z := boundaryZ b E
  set K := z • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  set R := passiveResolvent b E X
  set Y := passiveY X
  have hK : IsUnit K := by
    apply BlockBand.Transmission.isUnit_of_matrixImaginaryPart_posDef
    rw [BlockBand.Transmission.PassiveCovariance.matrixImaginaryPart_nearPencil]
    exact Matrix.PosDef.posSemidef_add hY (Matrix.PosDef.one.smul hη)
  have hRK : R * K = 1 := Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hK)
  have hKR : K * R = 1 := Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hK)
  have hpen : K - Kᴴ = (2 * Complex.I) • (((etaZ b E : ℝ) : ℂ) • 1 + Y) :=
    FullSource.pencil_sub_conj z X
  have h1 := FullSource.inv_sub_conj R K hRK
  have h2 := FullSource.inv_sub_conj Rᴴ Kᴴ (by rw [← conjTranspose_mul, hKR, conjTranspose_one])
  rw [conjTranspose_conjTranspose, conjTranspose_conjTranspose] at h2
  have hpen' : Kᴴ - K = -((2 * Complex.I) • (((etaZ b E : ℝ) : ℂ) • 1 + Y)) := by
    rw [← hpen]; abel
  rw [hpen'] at h1
  rw [hpen] at h2
  have t1 := congrArg Matrix.trace h1
  have t2 := congrArg Matrix.trace h2
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_one, trace_sub, trace_neg, trace_smul, trace_add,
    smul_eq_mul] at t1 t2
  have hc : (2 * Complex.I) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  have htr : (R * Rᴴ).trace = (Rᴴ * R).trace := trace_mul_comm _ _
  have key : (2 * Complex.I) * ((Rᴴ * Y * R).trace - (R * Y * Rᴴ).trace) = 0 := by
    rw [htr] at t1
    linear_combination -(t1 + t2)
  have := (mul_eq_zero.mp key).resolve_left hc
  simp only [passiveQ]
  rw [sub_eq_zero] at this
  exact this.symm

end BlockBand.SourceProcess.PhysApprox.B3
