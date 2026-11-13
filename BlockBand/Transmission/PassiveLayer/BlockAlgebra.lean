module

public import BlockBand.Transmission.PassiveCovariance.ResolventBound

/-!
# Deterministic block-matrix tools for the passive layer

* `vecNorm_add`, `vecNorm_comp_le`, `vecNorm_sumElim`: elementary Euclidean-norm facts.
* `vecNorm_mulVec_le'`, `opNorm_le_of_vec'`: rectangular versions of the `PassiveCovariance`
  lemmas.
* `norm_submatrix_le`: a submatrix along injective index maps has no larger norm.
* `norm_fromBlocks_le`: `‖[[a,b],[c,d]]‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖`.
* `isUnit_and_norm_inv_le_of_coercive`: `δ‖x‖² ≤ Im x*Sx` for all `x` gives `S` invertible,
  `‖S⁻¹‖ ≤ δ⁻¹`.
* `fromBlocks_mul_schurInv`: Schur inversion of `[[P, B], [B*, wI]]` through
  `S = P - w⁻¹BB*`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator ComplexOrder

section
variable {m : Type*} [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
theorem vecNorm_add (x y : m → ℂ) : vecNorm (x + y) ≤ vecNorm x + vecNorm y := by
  rw [vecNorm_eq, vecNorm_eq, vecNorm_eq, WithLp.toLp_add]; exact norm_add_le _ _

omit [DecidableEq m] in
theorem vecNorm_sq_eq (x : m → ℂ) : vecNorm x ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

omit [DecidableEq m] in
theorem vecNorm_le_of_sq {x : m → ℂ} {c : ℝ} (hc : 0 ≤ c) (h : ∑ i, ‖x i‖ ^ 2 ≤ c ^ 2) :
    vecNorm x ≤ c := by
  rw [← Real.sqrt_sq hc]; exact Real.sqrt_le_sqrt h

theorem vecNorm_comp_le {n : Type*} [Fintype n] [DecidableEq n] (x : m → ℂ) {f : n → m}
    (hf : Function.Injective f) : vecNorm (x ∘ f) ≤ vecNorm x := by
  refine vecNorm_le_of_sq (vecNorm_nonneg _) ?_
  rw [vecNorm_sq_eq]
  calc ∑ i, ‖(x ∘ f) i‖ ^ 2 = ∑ i ∈ Finset.univ.image f, ‖x i‖ ^ 2 := by
        rw [Finset.sum_image fun a _ b _ h => hf h]; rfl
    _ ≤ ∑ i, ‖x i‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity

omit [DecidableEq m] in
theorem vecNorm_sumElim {n : Type*} [Fintype n] [DecidableEq n] (x : m → ℂ) (y : n → ℂ) :
    vecNorm (Sum.elim x y) ≤ vecNorm x + vecNorm y := by
  refine vecNorm_le_of_sq (by have := vecNorm_nonneg x; have := vecNorm_nonneg y; positivity) ?_
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← vecNorm_sq_eq, ← vecNorm_sq_eq]
  nlinarith [vecNorm_nonneg x, vecNorm_nonneg y]

end

section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
theorem vecNorm_mulVec_le' (A : Matrix m n ℂ) (v : n → ℂ) :
    vecNorm (A *ᵥ v) ≤ ‖A‖ * vecNorm v := by
  have := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 v)
  rw [vecNorm_eq, vecNorm_eq]; exact this

omit [DecidableEq m] in
theorem opNorm_le_of_vec' (A : Matrix m n ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : n → ℂ, vecNorm (A *ᵥ x) ≤ C * vecNorm x) : ‖A‖ ≤ C := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  have := h x.ofLp
  rw [vecNorm_eq, vecNorm_eq] at this
  exact this

/-- Submatrices along injective maps do not increase the operator norm. -/
theorem norm_submatrix_le {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq m'] [DecidableEq n'] (A : Matrix m n ℂ)
    {f : m' → m} {g : n' → n} (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖A.submatrix f g‖ ≤ ‖A‖ := by
  refine opNorm_le_of_vec' _ (norm_nonneg _) fun u => ?_
  set ũ : n → ℂ := Function.extend g u 0
  have hu : vecNorm ũ = vecNorm u := by
    rw [vecNorm, vecNorm]
    congr 1
    calc ∑ i, ‖ũ i‖ ^ 2 = ∑ i ∈ Finset.univ.image g, ‖ũ i‖ ^ 2 := by
          refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
          have : ¬ ∃ a, g a = i := fun ⟨a, ha⟩ => hi (Finset.mem_image.mpr ⟨a, by simp, ha⟩)
          simp [ũ, Function.extend_apply' _ _ _ this]
      _ = ∑ a, ‖u a‖ ^ 2 := by
          rw [Finset.sum_image fun a _ b _ h => hg h]
          simp [ũ, hg.extend_apply]
  have hmv : A.submatrix f g *ᵥ u = (A *ᵥ ũ) ∘ f := by
    ext i
    simp only [mulVec, dotProduct, submatrix_apply, Function.comp_apply]
    calc ∑ j, A (f i) (g j) * u j = ∑ j ∈ Finset.univ.image g, A (f i) j * ũ j := by
          rw [Finset.sum_image fun a _ b _ h => hg h]; simp [ũ, hg.extend_apply]
      _ = ∑ j, A (f i) j * ũ j := by
          refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
          have : ¬ ∃ a, g a = j := fun ⟨a, ha⟩ => hj (Finset.mem_image.mpr ⟨a, by simp, ha⟩)
          simp [ũ, Function.extend_apply' _ _ _ this]
  rw [hmv, ← hu]
  exact (vecNorm_comp_le _ hf).trans (vecNorm_mulVec_le' A ũ)

end

section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The operator norm of a block matrix is at most the sum of its block norms. -/
theorem norm_fromBlocks_le (a : Matrix m m ℂ) (b : Matrix m n ℂ) (c : Matrix n m ℂ)
    (d : Matrix n n ℂ) :
    ‖fromBlocks a b c d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  refine opNorm_le_of_vec' _ (by positivity) fun x => ?_
  rw [fromBlocks_mulVec]
  have h1 := vecNorm_comp_le x Sum.inl_injective
  have h2 := vecNorm_comp_le x Sum.inr_injective
  refine (vecNorm_sumElim _ _).trans ?_
  have ha := vecNorm_mulVec_le' a (x ∘ Sum.inl)
  have hb := vecNorm_mulVec_le' b (x ∘ Sum.inr)
  have hc := vecNorm_mulVec_le' c (x ∘ Sum.inl)
  have hd := vecNorm_mulVec_le' d (x ∘ Sum.inr)
  have e1 := vecNorm_add (a *ᵥ (x ∘ Sum.inl)) (b *ᵥ (x ∘ Sum.inr))
  have e2 := vecNorm_add (c *ᵥ (x ∘ Sum.inl)) (d *ᵥ (x ∘ Sum.inr))
  have := norm_nonneg a; have := norm_nonneg b; have := norm_nonneg c; have := norm_nonneg d
  nlinarith [vecNorm_nonneg (x ∘ Sum.inl), vecNorm_nonneg (x ∘ Sum.inr)]

end

section
variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Coercivity of the imaginary part gives invertibility and `‖S⁻¹‖ ≤ δ⁻¹`. -/
theorem isUnit_and_norm_inv_le_of_coercive {S : Matrix m m ℂ} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x : m → ℂ, δ * vecNorm x ^ 2 ≤ (star x ⬝ᵥ (S *ᵥ x)).im) :
    IsUnit S ∧ ‖S⁻¹‖ ≤ δ⁻¹ := by
  have hlow : ∀ x : m → ℂ, δ * vecNorm x ≤ vecNorm (S *ᵥ x) := by
    intro x
    have h1 := h x
    have h2 : (star x ⬝ᵥ (S *ᵥ x)).im ≤ vecNorm x * vecNorm (S *ᵥ x) :=
      (Complex.im_le_norm _).trans (norm_star_dotProduct_le _ _)
    rcases (vecNorm_nonneg x).eq_or_lt with hx | hx
    · rw [← hx, mul_zero]; exact vecNorm_nonneg _
    · nlinarith
  have hinj : Function.Injective (S *ᵥ ·) := by
    intro x y hxy
    have := hlow (x - y)
    simp only at hxy
    rw [mulVec_sub, hxy, sub_self] at this
    have h0 : vecNorm (0 : m → ℂ) = 0 := by simp [vecNorm]
    rw [h0] at this
    have : vecNorm (x - y) = 0 := le_antisymm (by nlinarith [vecNorm_nonneg (x - y)])
      (vecNorm_nonneg _)
    rw [vecNorm_eq, norm_eq_zero] at this
    have := congrArg WithLp.ofLp this
    simpa [sub_eq_zero] using this
  have hS : IsUnit S := mulVec_injective_iff_isUnit.mp hinj
  refine ⟨hS, opNorm_le_of_vec _ (inv_nonneg.mpr hδ.le) fun y => ?_⟩
  have := hlow (S⁻¹ *ᵥ y)
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det S).mp hS), one_mulVec] at this
  rw [inv_mul_eq_div, le_div_iff₀ hδ]; linarith

/-- Schur inversion of `[[P, B], [B*, wI]]` through `S = P - w⁻¹BB*`. -/
theorem fromBlocks_mul_schurInv (P Bm : Matrix m m ℂ) {w : ℂ} (hw : w ≠ 0)
    (hS : IsUnit (P - w⁻¹ • (Bm * Bmᴴ))) :
    fromBlocks P Bm Bmᴴ (w • 1) *
      fromBlocks (P - w⁻¹ • (Bm * Bmᴴ))⁻¹ (-w⁻¹ • ((P - w⁻¹ • (Bm * Bmᴴ))⁻¹ * Bm))
        (-w⁻¹ • (Bmᴴ * (P - w⁻¹ • (Bm * Bmᴴ))⁻¹))
        (w⁻¹ • 1 + (w⁻¹ ^ 2) • (Bmᴴ * (P - w⁻¹ • (Bm * Bmᴴ))⁻¹ * Bm)) = 1 := by
  set S := P - w⁻¹ • (Bm * Bmᴴ) with hSdef
  have hSS : S * S⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det S).mp hS)
  have hPS : P * S⁻¹ = 1 + w⁻¹ • (Bm * (Bmᴴ * S⁻¹)) := by
    have hP : P = S + w⁻¹ • (Bm * Bmᴴ) := by rw [hSdef]; abel
    rw [hP, add_mul, hSS, smul_mul_assoc, mul_assoc]
  have hw' : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
  rw [fromBlocks_multiply, ← fromBlocks_one]
  congr 1
  · rw [hPS, mul_smul_comm]; module
  · rw [mul_smul_comm, ← mul_assoc, hPS]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc]
    module
  · rw [smul_mul_assoc, one_mul, smul_smul]
    linear_combination (norm := module) -(hw' • (Bmᴴ * S⁻¹))
  · rw [mul_smul_comm, smul_mul_assoc, one_mul, smul_add, smul_smul, smul_smul]
    simp only [mul_assoc]
    linear_combination (norm := module) hw' • (1 : Matrix m m ℂ) +
      hw' • (w⁻¹ • (Bmᴴ * (S⁻¹ * Bm)))
end

end BlockBand.Transmission.PassiveLayer
