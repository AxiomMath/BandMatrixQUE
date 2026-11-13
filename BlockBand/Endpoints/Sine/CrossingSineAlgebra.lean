module

public import BlockBand.Internal.Contracts.Layers
public import BlockBand.Model.Construction.OrderedSpectrum
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Crossing parameters of the scalar pair flow: exact Schur algebra

Main identity (`crossingSum_eq`, `t_j = -𝒩ρ μ_j`): if `H` is Hermitian and the exterior minor
`H_RR - E` is invertible, then with the Schur complement
`G + K(E) = H_SS - E - H_SR (H_RR - E)⁻¹ H_RS` (`pairSchur`) and its eigenvalues `μ_k`,
`Σ_j f(t_j) = Σ_k f(-𝒩ρ μ_k)`. Also: `pairSchur` of a split sample `assemble ω G` is
`G + pairResidual ω E` (`pairSchur_assemble`); eigenvalue sums are invariant under reindexing to
the ordered spectrum of `Fin N` (`sum_orderedEigenvalue_reindex`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix Polynomial
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers

section Pair

variable (p : Parameters) (i : ZMod p.n)

/-- The unfolding scale `𝒩ρ(E)`, `𝒩 = 2W`, `ρ = semicircleDensity`. -/
def crossingScale (E : ℝ) : ℝ := 2 * (p.W : ℝ) * Parameters.semicircleDensity E

/-- The scalar pair flow `H(t) = H + t/(𝒩ρ) P_S`. -/
def pairFlow (H : p.SiteMatrix) (E t : ℝ) : p.SiteMatrix :=
  H + ((t / crossingScale p E : ℝ) : ℂ) • pairProjector p i

/-- The crossing polynomial `det(H - E + X/(𝒩ρ) P_S) ∈ ℂ[X]`; its value at `t` is
`det(H(t) - E)` (`crossingPoly_eval`). -/
def crossingPoly (H : p.SiteMatrix) (E : ℝ) : ℂ[X] :=
  ((C : ℂ →+* ℂ[X]).mapMatrix (H - (E : ℂ) • 1) +
    (X : ℂ[X]) • (C : ℂ →+* ℂ[X]).mapMatrix
      ((((crossingScale p E)⁻¹ : ℝ) : ℂ) • pairProjector p i)).det

/-- The linear statistic `Σ_j f(t_j)` of the crossing process `𝒞_W = Σ_j δ_{t_j}`: the sum of
`f` over the real roots `t_j` of `crossingPoly` (with multiplicity). -/
def crossingSum (f : ℝ → ℝ) (H : p.SiteMatrix) (E : ℝ) : ℝ :=
  (((crossingPoly p i H E).roots.filter fun z => z.im = 0).map fun z => f z.re).sum

/-- The block `H_SR` (pair rows, exterior columns). -/
def pairExteriorBlock (H : p.SiteMatrix) : Matrix (PairSite p i) (ExteriorSite p i) ℂ :=
  fun x y => H x.1 y.1

/-- The Schur complement `H_SS - E - H_SR (H_RR - E)⁻¹ H_RS` on the pair. -/
def pairSchur (H : p.SiteMatrix) (E : ℝ) : PairMatrix p i :=
  pairBlock p i H - (E : ℂ) • 1 -
    pairExteriorBlock p i H * (exteriorBlock p i H - (E : ℂ) • 1)⁻¹ * couplingBlock p i H

theorem crossingPoly_eval (H : p.SiteMatrix) (E t : ℝ) :
    (crossingPoly p i H E).eval (t : ℂ) = (pairFlow p i H E t - (E : ℂ) • 1).det := by
  unfold crossingPoly
  rw [← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext x y
  simp only [RingHom.mapMatrix_apply, map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, coe_evalRingHom, eval_add, eval_mul, eval_C, eval_X, pairFlow, smul_eq_mul]
  push_cast
  ring

/-- Site splitting `S ⊕ R ≃ Site`. -/
abbrev pairSplit : PairSite p i ⊕ ExteriorSite p i ≃ p.Site :=
  Equiv.sumCompl fun x : p.Site => x.1 = i ∨ x.1 = i + 1

theorem isHermitian_real_smul_one {n : Type*} [Fintype n] [DecidableEq n] (E : ℝ) :
    ((E : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := by
  ext a b
  by_cases h : a = b
  · subst h; simp
  · simp [one_apply, h, Ne.symm h]

theorem pairSchur_isHermitian (H : p.SiteMatrix) (hH : H.IsHermitian) (E : ℝ) :
    (pairSchur p i H E).IsHermitian := by
  have hSR : pairExteriorBlock p i H = (couplingBlock p i H)ᴴ := by
    ext a b
    simp only [pairExteriorBlock, couplingBlock, conjTranspose_apply]
    rw [← hH.apply]
  have hR : (exteriorBlock p i H - (E : ℂ) • 1).IsHermitian := by
    refine IsHermitian.sub ?_ ?_
    · ext a b; simp only [exteriorBlock, conjTranspose_apply]; exact hH.apply _ _
    · exact (isHermitian_real_smul_one E)
  have hP : (pairBlock p i H).IsHermitian := by
    ext a b; simp only [pairBlock, conjTranspose_apply]; exact hH.apply _ _
  unfold pairSchur
  rw [hSR]
  refine (hP.sub (isHermitian_real_smul_one E)).sub ?_
  exact isHermitian_conjTranspose_mul_mul _ hR.inv

/-- `det(S + u) = Π_k (u + μ_k)` for Hermitian `S` with eigenvalues `μ_k`. -/
theorem det_add_smul_one_eq_prod {n : Type*} [Fintype n] [DecidableEq n] {S : Matrix n n ℂ}
    (hS : S.IsHermitian) (u : ℂ) :
    (S + u • 1).det = ∏ k, (u + (hS.eigenvalues k : ℂ)) := by
  have h := eval_charpoly S (-u)
  rw [hS.charpoly_eq, eval_prod] at h
  simp only [eval_sub, eval_X, eval_C] at h
  have h2 : (scalar n (-u) - S) = -(S + u • 1) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [Matrix.diagonal]; ring
    · simp [Matrix.diagonal, hab]
  rw [h2, det_neg] at h
  have h4 : ∏ k, (-u - (hS.eigenvalues k : ℂ)) = (-1) ^ Fintype.card n * (S + u • 1).det := h
  have h3 : ∏ k, (u + (hS.eigenvalues k : ℂ)) =
      (-1) ^ Fintype.card n * ∏ k, (-u - (hS.eigenvalues k : ℂ)) := by
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => by ring
  rw [h3, h4, ← mul_assoc, ← mul_pow]
  norm_num

/-- The pair crossing locations `t_j = -𝒩ρ μ_j`: for Hermitian `H` with invertible exterior
minor `H_RR - E` and `𝒩ρ ≠ 0`, the crossing polynomial factors as
`det(H_RR - E) (𝒩ρ)^{-2W'} Π_k (X + 𝒩ρ μ_k)`, `μ_k` the eigenvalues of `pairSchur`. -/
theorem crossingPoly_eq (H : p.SiteMatrix) (hH : H.IsHermitian) (E : ℝ)
    (hdet : (exteriorBlock p i H - (E : ℂ) • 1).det ≠ 0) (hsc : crossingScale p E ≠ 0) :
    crossingPoly p i H E =
      C ((exteriorBlock p i H - (E : ℂ) • 1).det *
          (((crossingScale p E)⁻¹ : ℝ) : ℂ) ^ Fintype.card (PairSite p i)) *
        ∏ k, (X - C ((-(crossingScale p E * (pairSchur_isHermitian p i H hH E).eigenvalues k) :
          ℝ) : ℂ)) := by
  apply Polynomial.funext
  intro z
  set hS := pairSchur_isHermitian p i H hH E
  set c : ℂ := (((crossingScale p E)⁻¹ : ℝ) : ℂ)
  have hc : c * ((crossingScale p E : ℝ) : ℂ) = 1 := by
    simp only [c]; rw [← Complex.ofReal_mul, inv_mul_cancel₀ hsc, Complex.ofReal_one]
  -- evaluation of the defining determinant at a complex point
  have hev : (crossingPoly p i H E).eval z =
      ((H - (E : ℂ) • 1) + (z * c) • pairProjector p i).det := by
    unfold crossingPoly
    rw [← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext x y
    simp only [RingHom.mapMatrix_apply, map_apply, Matrix.add_apply, Matrix.smul_apply,
      coe_evalRingHom, eval_add, eval_mul, eval_C, eval_X, smul_eq_mul, c]
    push_cast
    ring
  rw [hev]
  -- the Schur identity holds at complex parameters by the same block computation
  have hschur : ((H - (E : ℂ) • 1) + (z * c) • pairProjector p i).det =
      (exteriorBlock p i H - (E : ℂ) • 1).det * (pairSchur p i H E + (z * c) • 1).det := by
    classical
    set M := (H - (E : ℂ) • 1) + (z * c) • pairProjector p i
    have hM : M.det = (M.submatrix (pairSplit p i) (pairSplit p i)).det :=
      (det_submatrix_equiv_self (pairSplit p i) M).symm
    rw [hM, ← fromBlocks_toBlocks (M.submatrix (pairSplit p i) (pairSplit p i))]
    set D := (M.submatrix (pairSplit p i) (pairSplit p i)).toBlocks₂₂
    have hD : D = exteriorBlock p i H - (E : ℂ) • 1 := by
      ext x y
      have hx := x.2
      simp only [D, M, toBlocks₂₂, submatrix_apply, of_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.add_apply, pairProjector, exteriorBlock, Equiv.sumCompl_apply_inr]
      by_cases hxy : x = y
      · subst hxy; simp [hx]
      · have : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
        simp [one_apply, this, hxy]
    have hDu : IsUnit D.det := by rw [hD]; exact isUnit_iff_ne_zero.mpr hdet
    let _ := invertibleOfIsUnitDet D hDu
    rw [det_fromBlocks₂₂, invOf_eq_nonsing_inv, hD]
    congr 2
    have hA : ∀ a b : PairSite p i, (M.submatrix (pairSplit p i) (pairSplit p i)).toBlocks₁₁ a b =
        pairBlock p i H a b - (E : ℂ) * (1 : PairMatrix p i) a b +
          (z * c) * (1 : PairMatrix p i) a b := by
      intro a b
      have ha := a.2
      simp only [M, toBlocks₁₁, submatrix_apply, of_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.add_apply, pairProjector, pairBlock, Equiv.sumCompl_apply_inl, smul_eq_mul]
      by_cases hab : a = b
      · subst hab; simp [ha]
      · have : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
        simp [one_apply, this, hab]
    have hB : (M.submatrix (pairSplit p i) (pairSplit p i)).toBlocks₁₂ =
        pairExteriorBlock p i H := by
      ext a b
      have hne : a.1 ≠ b.1 := fun h => b.2 (h ▸ a.2)
      simp [M, toBlocks₁₂, pairProjector, pairExteriorBlock, one_apply, hne]
    have hC : (M.submatrix (pairSplit p i) (pairSplit p i)).toBlocks₂₁ = couplingBlock p i H := by
      ext a b
      have hne : a.1 ≠ b.1 := fun h => a.2 (h ▸ b.2)
      simp [M, toBlocks₂₁, pairProjector, couplingBlock, one_apply, hne]
    rw [hB, hC]
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply, hA, pairSchur, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hschur, det_add_smul_one_eq_prod hS, eval_mul, eval_C, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [mul_assoc]
  congr 1
  rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  push_cast
  have : c * ((crossingScale p E : ℝ) : ℂ) * (hS.eigenvalues k : ℂ) = (hS.eigenvalues k : ℂ) := by
    rw [hc, one_mul]
  linear_combination -this

/-- The crossing statistic in terms of the Schur eigenvalues: `Σ_j f(t_j) = Σ_k f(-𝒩ρ μ_k)`. -/
theorem crossingSum_eq (f : ℝ → ℝ) (H : p.SiteMatrix) (hH : H.IsHermitian) (E : ℝ)
    (hdet : (exteriorBlock p i H - (E : ℂ) • 1).det ≠ 0) (hsc : crossingScale p E ≠ 0) :
    crossingSum p i f H E =
      ∑ k, f (-(crossingScale p E * (pairSchur_isHermitian p i H hH E).eigenvalues k)) := by
  unfold crossingSum
  rw [crossingPoly_eq p i H hH E hdet hsc, roots_C_mul]
  · set g : PairSite p i → ℂ :=
      fun k => ((-(crossingScale p E * (pairSchur_isHermitian p i H hH E).eigenvalues k) : ℝ) : ℂ)
    have hprod : ∏ k, (X - C (g k)) = ((Finset.univ.val.map g).map fun a => X - C a).prod := by
      rw [Multiset.map_map, Finset.prod_eq_multiset_prod]; rfl
    rw [hprod, roots_multiset_prod_X_sub_C, Multiset.filter_eq_self.mpr, Multiset.map_map]
    · simp only [Function.comp_def, g, Complex.ofReal_re]
      rfl
    · intro z hz
      obtain ⟨k, _, rfl⟩ := Multiset.mem_map.mp hz
      simp [g]
  · refine mul_ne_zero hdet (pow_ne_zero _ ?_)
    exact_mod_cast inv_ne_zero hsc

end Pair

/-!
## Split samples
-/

section Split

variable (p : Parameters) (i : ZMod p.n)

theorem exteriorBlock_assemble (ω : SplitState p i) (G : PairMatrix p i) :
    exteriorBlock p i (assemble p i ω G) = ω.1 := by
  ext a b; simp [exteriorBlock, assemble, a.2, b.2]

theorem pairSchur_assemble (ω : SplitState p i) (G : PairMatrix p i) (E : ℝ) :
    pairSchur p i (assemble p i ω G) E = G + pairResidual p i ω E := by
  have h1 : pairBlock p i (assemble p i ω G) = ω.2.2 + G := by
    ext a b; simp [pairBlock, assemble, a.2, b.2]
  have h2 : pairExteriorBlock p i (assemble p i ω G) = (ω.2.1)ᴴ := by
    ext a b; simp [pairExteriorBlock, assemble, a.2, b.2, conjTranspose_apply]
  have h3 : couplingBlock p i (assemble p i ω G) = ω.2.1 := by
    ext a b; simp [couplingBlock, assemble, a.2, b.2]
  rw [pairSchur, h1, h2, h3, exteriorBlock_assemble, pairResidual,
    BlockBand.Coarea.physicalCoareaF, BlockBand.Coarea.physicalCoareaResolvent]
  abel

end Split

/-!
## Eigenvalue sums and reindexing
-/

/-- `Σ_k φ(μ_k) = Σ_{z ∈ roots charpoly} φ(Re z)` for Hermitian matrices. -/
theorem sum_eigenvalues_eq_roots {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (φ : ℝ → ℝ) :
    ∑ k, φ (hA.eigenvalues k) = (A.charpoly.roots.map fun z => φ z.re).sum := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  simp only [Function.comp_def]
  rfl

/-- The ordered spectrum of a reindexed Hermitian matrix carries the same eigenvalue sums. -/
theorem sum_orderedEigenvalue_reindex {n : Type*} [Fintype n] [DecidableEq n] {N : ℕ}
    (e : n ≃ Fin N) {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : (reindex e e A).IsHermitian) (φ : ℝ → ℝ) :
    ∑ k : Fin (Fintype.card (Fin N)),
        φ (BlockBand.Model.Construction.orderedEigenvalue ⟨reindex e e A, hB⟩ k) =
      ∑ k, φ (hA.eigenvalues k) := by
  rw [sum_eigenvalues_eq_roots hA, ← charpoly_reindex e A, hB.roots_charpoly_eq_eigenvalues₀,
    Multiset.map_map]
  simp only [BlockBand.Model.Construction.orderedEigenvalue,
    BlockBand.Foundations.Spectral.increasingEigenvalue]
  rw [← Finset.sum_eq_multiset_sum]
  · exact Fintype.sum_equiv Fin.revPerm _ _ (fun k => by simp)

end BlockBand.Endpoints
