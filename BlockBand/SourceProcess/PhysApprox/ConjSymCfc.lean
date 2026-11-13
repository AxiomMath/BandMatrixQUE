module

public import BlockBand.SourceProcess.PhysApprox.ConjSymPath
public import BlockBand.SourceProcess.Closing.PhysHardy
public import Mathlib.LinearAlgebra.Lagrange

/-!
# The omitted projection at the conjugated path

Used for the output leakage from the input leakage (`TargetT4`).

* `cfc_matConj`: `cfc f (conj X) = conj (cfc f X)` for Hermitian `X` and real `f` (entrywise
  conjugation is a continuous real star-algebra homomorphism, `StarAlgHom.map_cfc`).
* `cfc_omitIndicator_eq`: `1_{≤h²}(1 - SSᴴ) = Πᴴ Π` with `Π = g(1 - SᴴS)Sᴴ` (polynomial
  interpolation of `g²` on both spectra and `S(1 - SᴴS) = (1 - SSᴴ)S`), for `h² < 1`.
* `omittedProj_conjPath`: `A_-(ω̄) = conj(ΠᴴΠ)` for Hermitian blocks.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Closing
open scoped ComplexConjugate

/-- Entrywise conjugation as a real star-algebra homomorphism. -/
def conjStarAlgHom (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℂ →⋆ₐ[ℝ] Matrix ι ι ℂ where
  toFun := matConj
  map_one' := matConj_one
  map_mul' := matConj_mul
  map_zero' := by
    ext i j
    simp [matConj_apply]
  map_add' := fun M N => by
    ext i j
    simp [matConj_apply]
  commutes' := fun r => by
    ext i j
    simp only [matConj_apply, Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp
  map_star' := fun M => by
    ext i j
    simp [matConj_apply, Matrix.star_apply]

theorem conjStarAlgHom_apply (ι : Type*) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    conjStarAlgHom ι M = matConj M := rfl

variable {W : ℕ}

/-- `cfc f (conj X) = conj (cfc f X)` for Hermitian `X`. -/
theorem cfc_matConj (f : ℝ → ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (hX : X.IsHermitian) :
    cfc f (matConj X) = matConj (cfc f X) := by
  have hc : Continuous (conjStarAlgHom (Fin W)) := by
    change Continuous fun M : Matrix (Fin W) (Fin W) ℂ => M.map (starRingEnd ℂ)
    exact continuous_id.matrix_map Complex.continuous_conj
  have hXc : IsSelfAdjoint (conjStarAlgHom (Fin W) X) := hX.isSelfAdjoint.map _
  have h := StarAlgHom.map_cfc (conjStarAlgHom (Fin W)) f X (continuousOn_spectrum f X) hc
    hX.isSelfAdjoint hXc
  rw [conjStarAlgHom_apply, conjStarAlgHom_apply] at h
  exact h.symm

/-- If `SX = YS` then `S p(X) = p(Y) S` for every real polynomial `p`. -/
theorem mul_aeval_of_semiconj {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S X Y : Matrix ι ι ℂ} (h : S * X = Y * S) (p : Polynomial ℝ) :
    S * Polynomial.aeval X p = Polynomial.aeval Y p * S := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, Matrix.mul_add, Matrix.add_mul, hp, hq]
  | monomial n a =>
    have hn : S * X ^ n = Y ^ n * S := (SemiconjBy.pow_right h n).eq
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← mul_assoc, ← Algebra.commutes,
      mul_assoc, hn, ← mul_assoc]

/-- **`1_{≤h²}(1 - SSᴴ) = ΠᴴΠ`**, `Π = g(1 - SᴴS)Sᴴ`, `g = pairWeight h`, for `h² < 1`. -/
theorem cfc_omitIndicator_eq (h : ℝ) (hh : h ^ 2 < 1) (S : Matrix (Fin W) (Fin W) ℂ) :
    cfc (omitIndicator h) (1 - S * Sᴴ) =
      (cfc (pairWeight h) (1 - Sᴴ * S) * Sᴴ)ᴴ * (cfc (pairWeight h) (1 - Sᴴ * S) * Sᴴ) := by
  classical
  have hT : IsSelfAdjoint (1 - Sᴴ * S) :=
    (isHermitian_one.sub (isHermitian_conjTranspose_mul_self S)).isSelfAdjoint
  have hT' : IsSelfAdjoint (1 - S * Sᴴ) :=
    (isHermitian_one.sub (isHermitian_mul_conjTranspose_self S)).isSelfAdjoint
  have hfin : (spectrum ℝ (1 - Sᴴ * S) ∪ spectrum ℝ (1 - S * Sᴴ)).Finite :=
    (show (spectrum ℝ (1 - Sᴴ * S)).Finite from Matrix.finite_real_spectrum).union
      (show (spectrum ℝ (1 - S * Sᴴ)).Finite from Matrix.finite_real_spectrum)
  set g2 : ℝ → ℝ := fun t => pairWeight h t * pairWeight h t with hg2
  set p : Polynomial ℝ := Lagrange.interpolate hfin.toFinset id g2
  have hnode : ∀ t ∈ spectrum ℝ (1 - Sᴴ * S) ∪ spectrum ℝ (1 - S * Sᴴ), p.eval t = g2 t :=
    fun t ht => Lagrange.eval_interpolate_at_node g2 (Set.injOn_id _) (hfin.mem_toFinset.2 ht)
  have h1 : cfc (pairWeight h) (1 - Sᴴ * S) * cfc (pairWeight h) (1 - Sᴴ * S) =
      Polynomial.aeval (1 - Sᴴ * S) p := by
    rw [← cfc_mul (pairWeight h) (pairWeight h) (1 - Sᴴ * S) (continuousOn_spectrum _ _)
      (continuousOn_spectrum _ _), ← cfc_polynomial p (1 - Sᴴ * S) hT]
    exact cfc_congr fun t ht => (hnode t (Or.inl ht)).symm
  have hsemi : S * (1 - Sᴴ * S) = (1 - S * Sᴴ) * S := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  have h2 := mul_aeval_of_semiconj hsemi p
  have h3 : cfc (omitIndicator h) (1 - S * Sᴴ) =
      Polynomial.aeval (1 - S * Sᴴ) p * (S * Sᴴ) := by
    rw [cfc_congr (g := fun t => (p * (1 - Polynomial.X)).eval t), cfc_polynomial _ _ hT',
      map_mul, map_sub, map_one, Polynomial.aeval_X, sub_sub_cancel]
    intro t ht
    have hw := pairWeight_mul h hh t
    beta_reduce at hw
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
      hnode t (Or.inr ht), hg2]
    linear_combination -hw
  rw [conjTranspose_mul, conjTranspose_conjTranspose, cfc_conjTranspose, h3]
  have e : S * cfc (pairWeight h) (1 - Sᴴ * S) * (cfc (pairWeight h) (1 - Sᴴ * S) * Sᴴ) =
      S * (cfc (pairWeight h) (1 - Sᴴ * S) * cfc (pairWeight h) (1 - Sᴴ * S)) * Sᴴ := by
    simp only [Matrix.mul_assoc]
  rw [e, h1, h2, Matrix.mul_assoc]

/-- **`A_-(ω̄) = conj(ΠᴴΠ)`** for Hermitian blocks and `h² < 1`. -/
theorem omittedProj_conjPath (b E h : ℝ) (hh : h ^ 2 < 1) (n : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    omittedProj b E h W n (conjPath ω) =
      matConj ((closingPairing b E h W n ω)ᴴ * closingPairing b E h W n ω) := by
  have hX : (1 - farReflection b E W n ω * (farReflection b E W n ω)ᴴ).IsHermitian :=
    isHermitian_one.sub (isHermitian_mul_conjTranspose_self _)
  rw [omittedProj, farTransmission_conjPath b E n ω hA, cfc_matConj _ _ hX,
    cfc_omitIndicator_eq h hh, closingPairing, farTransmission]

end BlockBand.SourceProcess.PhysApprox
