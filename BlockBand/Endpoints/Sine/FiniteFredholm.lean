module

public import BlockBand.Endpoints.Sine.FredholmDefs
public import BlockBand.Endpoints.Sine.Andreief
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Finite projection kernels: exact Fredholm expansion

Route: with `G p q = ∫ ψ p ψ q φ dν`, the `k`-th Fredholm integral equals
`∑ i : Fin k → ι, det (G.submatrix i i) = k! ∑_{|S| = k} det G_S`; the
principal-minor expansion of `det (1 - G)` and the Andréief identity close the
argument.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weighted Gram matrix `G p q = ∫ ψ p a * ψ q a * φ a dν`. -/
def weightedGram (ν : Measure ℝ) (ψ : ι → ℝ → ℝ) (φ : ℝ → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun p q => ∫ a, ψ p a * ψ q a * φ a ∂ν

omit [Fintype ι] in
/-- A map `i : Fin k → ι` whose image is a finset `s` of cardinality `k`
factors as `Subtype.val ∘ e` for a bijection `e : Fin k ≃ s`. -/
theorem exists_equiv_of_image_eq {k : ℕ} (i : Fin k → ι) (s : Finset ι)
    (hs : Finset.univ.image i = s) (hcard : s.card = k) :
    ∃ e : Fin k ≃ s, ∀ a, (e a : ι) = i a := by
  have hmem : ∀ a, i a ∈ s := fun a => hs ▸ Finset.mem_image_of_mem i (Finset.mem_univ a)
  have hinj : Function.Injective i := by
    have h : (Finset.univ.image i).card = (Finset.univ : Finset (Fin k)).card := by
      rw [hs, hcard, Finset.card_univ, Fintype.card_fin]
    rw [Finset.card_image_iff, Finset.coe_univ] at h
    exact Set.injOn_univ.mp h
  refine ⟨Equiv.ofBijective (fun a => ⟨i a, hmem a⟩) ⟨fun a b hab => hinj ?_, ?_⟩, fun a => rfl⟩
  · exact congrArg Subtype.val hab
  · rintro ⟨x, hx⟩
    rw [← hs, Finset.mem_image] at hx
    obtain ⟨a, -, rfl⟩ := hx
    exact ⟨a, rfl⟩

/-- Over any commutative ring `R`, for `A : Matrix ι ι R` and `k : ℕ`,
`∑ i : Fin k → ι, det (A.submatrix i i) = k! * ∑_{s ⊆ ι, |s| = k} det A_s`
(non-injective `i` have a repeated row; the injective `i` with image `s` are
the `k!` bijections `Fin k ≃ s`). -/
theorem sum_det_submatrix_eq_factorial_mul_sum_minors {R : Type*} [CommRing R]
    (A : Matrix ι ι R) (k : ℕ) :
    ∑ i : Fin k → ι, (A.submatrix i i).det =
      (k.factorial : R) * ∑ s ∈ (Finset.univ : Finset ι).powersetCard k,
        (A.submatrix (Subtype.val : s → ι) Subtype.val).det := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun i : Fin k → ι => Finset.univ.image i), Finset.mul_sum]
  rw [← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset ι).powersetCard k))]
  · refine Finset.sum_congr rfl fun s hs => ?_
    have hcard : s.card = k := (Finset.mem_powersetCard.mp hs).2
    have hval : ∀ i ∈ Finset.univ.filter (fun i : Fin k → ι => Finset.univ.image i = s),
        (A.submatrix i i).det = (A.submatrix (Subtype.val : s → ι) Subtype.val).det := by
      intro i hi
      obtain ⟨e, he⟩ := exists_equiv_of_image_eq i s (Finset.mem_filter.mp hi).2 hcard
      have hsub : A.submatrix i i = (A.submatrix (Subtype.val : s → ι) Subtype.val).submatrix e e := by
        ext a b
        simp [he]
      rw [hsub, det_submatrix_equiv_self]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have e0 : Fin k ≃ s := Fintype.equivOfCardEq (by simp [hcard])
    have hc : (Finset.univ : Finset (Fin k ≃ s)).card =
        (Finset.univ.filter (fun i : Fin k → ι => Finset.univ.image i = s)).card := by
      refine Finset.card_bij (fun e _ => fun a => (e a : ι)) ?_ ?_ ?_
      · intro e _
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        ext x
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨a, rfl⟩
          exact (e a).2
        · intro hx
          obtain ⟨a, ha⟩ := e.surjective ⟨x, hx⟩
          exact ⟨a, by rw [ha]⟩
      · intro e₁ _ e₂ _ h
        exact Equiv.ext fun a => Subtype.ext (congrFun h a)
      · intro i hi
        obtain ⟨e, he⟩ := exists_equiv_of_image_eq i s (Finset.mem_filter.mp hi).2 hcard
        exact ⟨e, Finset.mem_univ _, funext he⟩
    rw [← hc, Finset.card_univ, Fintype.card_equiv e0, Fintype.card_fin]
  · intro s _ hs
    refine Finset.sum_eq_zero fun i hi => ?_
    have himg : Finset.univ.image i = s := (Finset.mem_filter.mp hi).2
    have hninj : ¬ Function.Injective i := by
      intro hinj
      apply hs
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    simp only [Function.Injective, not_forall] at hninj
    obtain ⟨a, b, hab, hne⟩ := hninj
    refine det_zero_of_row_eq hne ?_
    funext c
    simp [hab]

/-- Principal-minor expansion of `det (1 - A)` over a commutative ring `R`:
`det (1 - A) = ∑_{k ≤ card ι} (-1)^k ∑_{s ⊆ ι, |s| = k} det A_s`. Obtained by
evaluating `det (1 + X • A)` at `X = -1` with
`Matrix.coeff_det_one_add_X_smul_eq_sum_minors`. -/
theorem det_one_sub_eq_sum_minors {R : Type*} [CommRing R] (A : Matrix ι ι R) :
    (1 - A).det = ∑ k ∈ Finset.range (Fintype.card ι + 1), (-1 : R) ^ k *
      ∑ s ∈ (Finset.univ : Finset ι).powersetCard k,
        (A.submatrix (Subtype.val : s → ι) Subtype.val).det := by
  set p : Polynomial R := (1 + (Polynomial.X : Polynomial R) • A.map Polynomial.C).det with hp
  have hcoeff := coeff_det_one_add_X_smul_eq_sum_minors A
  have heval : p.eval (-1) = (1 - A).det := by
    rw [hp, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [sub_eq_add_neg]
    · simp [Matrix.one_apply_ne hij]
  have hdeg : p.natDegree < Fintype.card ι + 1 := by
    refine Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_)
    rw [hp, hcoeff, Finset.powersetCard_eq_empty.mpr (by simpa using hN), Finset.sum_empty]
  rw [← heval, Polynomial.eval_eq_sum_range' hdeg]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hp, hcoeff, mul_comm]

omit [DecidableEq ι] in
/-- Pointwise expansion of a finite-rank Fredholm integrand: if
`K x y = ∑ i, ψ i x * ψ i y` for all `x y`, then for every `k : ℕ` and
`y : Fin k → ℝ`,
`det [K (y a) (y b)] * ∏ a, φ (y a) =
  ∑ σ, ∑ i : Fin k → ι, sign σ * ∏ a, ψ (i a) (y a) * ψ (i (σ⁻¹ a)) (y a) * φ (y a)`. -/
theorem det_kernel_mul_prod_eq_sum (ψ : ι → ℝ → ℝ) (K : ℝ → ℝ → ℝ)
    (hK : ∀ x y, K x y = ∑ i, ψ i x * ψ i y) (φ : ℝ → ℝ) {k : ℕ} (y : Fin k → ℝ) :
    Matrix.det (fun a b : Fin k => K (y a) (y b)) * ∏ a, φ (y a) =
      ∑ σ : Equiv.Perm (Fin k), ∑ i : Fin k → ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ a, (ψ (i a) (y a) * ψ (i (σ⁻¹ a)) (y a) * φ (y a)) := by
  change Matrix.det (Matrix.of fun a b : Fin k => K (y a) (y b)) * _ = _
  rw [← det_transpose, det_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hentry : ∀ a, (Matrix.of fun a b : Fin k => K (y a) (y b))ᵀ (σ a) a =
      ∑ p, ψ p (y a) * ψ p (y (σ a)) := fun a => by
    simp [Matrix.transpose_apply, hK]
  simp only [hentry, Fintype.prod_sum, Units.smul_def, zsmul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hre : ∏ a, ψ (i a) (y (σ a)) = ∏ a, ψ (i (σ⁻¹ a)) (y a) := by
    rw [← Equiv.prod_comp σ (fun a => ψ (i (σ⁻¹ a)) (y a))]
    simp
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, hre]
  ring

omit [DecidableEq ι] in
/-- The `k`-th Fredholm integral of a finite-rank kernel. Let `ν` be a finite
measure on `ℝ`, `ψ : ι → ℝ → ℝ` measurable with `|ψ i a| ≤ C`,
`K x y = ∑ i, ψ i x * ψ i y`, and `φ` measurable with `|φ a| ≤ D`. Then for
every `k : ℕ`, `fredholmIntegral K ν φ k = ∑ i : Fin k → ι, det (G.submatrix i i)`
with `G = weightedGram ν ψ φ`. -/
theorem fredholmIntegral_eq_sum_det_submatrix (ν : Measure ℝ) [IsFiniteMeasure ν]
    (ψ : ι → ℝ → ℝ) (hψ : ∀ i, Measurable (ψ i)) (hψb : ∃ C, ∀ i a, |ψ i a| ≤ C)
    (K : ℝ → ℝ → ℝ) (hK : ∀ x y, K x y = ∑ i, ψ i x * ψ i y)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hφb : ∃ C, ∀ a, |φ a| ≤ C) (k : ℕ) :
    fredholmIntegral K ν φ k =
      ∑ i : Fin k → ι, ((weightedGram ν ψ φ).submatrix i i).det := by
  obtain ⟨C, hC⟩ := hψb
  obtain ⟨D, hD⟩ := hφb
  have hint : ∀ (σ : Equiv.Perm (Fin k)) (i : Fin k → ι), Integrable
      (fun y : Fin k → ℝ => ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ a, (ψ (i a) (y a) * ψ (i (σ⁻¹ a)) (y a) * φ (y a))) (Measure.pi fun _ => ν) := by
    intro σ i
    refine Integrable.const_mul (Integrable.fintype_prod (𝕜 := ℝ) (μ := fun _ => ν)
      (f := fun a t => ψ (i a) t * ψ (i (σ⁻¹ a)) t * φ t) fun a => ?_) _
    refine integrable_of_measurable_of_abs_le (((hψ _).mul (hψ _)).mul hφ) (C * C * D)
      fun t => ?_
    rw [abs_mul, abs_mul]
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (i a) t)
    exact mul_le_mul (mul_le_mul (hC _ _) (hC _ _) (abs_nonneg _) hC0) (hD t) (abs_nonneg _)
      (mul_nonneg hC0 hC0)
  have hI : ∀ (σ : Equiv.Perm (Fin k)) (i : Fin k → ι),
      ∫ y : Fin k → ℝ, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ a, (ψ (i a) (y a) * ψ (i (σ⁻¹ a)) (y a) * φ (y a)) ∂Measure.pi (fun _ => ν) =
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ a, weightedGram ν ψ φ (i a) (i (σ⁻¹ a)) := by
    intro σ i
    rw [integral_const_mul,
      integral_fintype_prod_eq_prod (fun a t => ψ (i a) t * ψ (i (σ⁻¹ a)) t * φ t)]
    simp [weightedGram]
  unfold fredholmIntegral
  simp_rw [det_kernel_mul_prod_eq_sum ψ K hK φ]
  rw [integral_finsetSum _ fun σ _ => integrable_finsetSum _ fun i _ => hint σ i]
  simp_rw [integral_finsetSum _ fun i _ => hint _ i, hI]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin k))), ← det_transpose, det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [Units.smul_def, Equiv.Perm.sign_inv]

/-- The signed Fredholm terms of a finite-rank kernel are signed sums of
principal minors: under the hypotheses of
`fredholmIntegral_eq_sum_det_submatrix`, for every `k : ℕ`,
`fredholmTerm K ν φ k = (-1)^k * ∑_{s ⊆ ι, |s| = k} det G_s`,
`G = weightedGram ν ψ φ`. -/
theorem fredholmTerm_eq_sum_minors (ν : Measure ℝ) [IsFiniteMeasure ν]
    (ψ : ι → ℝ → ℝ) (hψ : ∀ i, Measurable (ψ i)) (hψb : ∃ C, ∀ i a, |ψ i a| ≤ C)
    (K : ℝ → ℝ → ℝ) (hK : ∀ x y, K x y = ∑ i, ψ i x * ψ i y)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hφb : ∃ C, ∀ a, |φ a| ≤ C) (k : ℕ) :
    fredholmTerm K ν φ k = (-1 : ℝ) ^ k * ∑ s ∈ (Finset.univ : Finset ι).powersetCard k,
      ((weightedGram ν ψ φ).submatrix (Subtype.val : s → ι) Subtype.val).det := by
  unfold fredholmTerm
  rw [fredholmIntegral_eq_sum_det_submatrix ν ψ hψ hψb K hK φ hφ hφb k,
    sum_det_submatrix_eq_factorial_mul_sum_minors]
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp

/-- Vanishing of high Fredholm terms of a finite-rank kernel: under the
hypotheses of `fredholmIntegral_eq_sum_det_submatrix` (finite `ν`, bounded
measurable `ψ` and `φ`, `K x y = ∑ i, ψ i x * ψ i y`; no orthonormality is
needed), `fredholmTerm K ν φ k = 0` for every `k > card ι`. -/
theorem fredholmTerm_eq_zero_of_card_lt (ν : Measure ℝ) [IsFiniteMeasure ν]
    (ψ : ι → ℝ → ℝ) (hψ : ∀ i, Measurable (ψ i)) (hψb : ∃ C, ∀ i a, |ψ i a| ≤ C)
    (K : ℝ → ℝ → ℝ) (hK : ∀ x y, K x y = ∑ i, ψ i x * ψ i y)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hφb : ∃ C, ∀ a, |φ a| ≤ C) {k : ℕ}
    (hk : Fintype.card ι < k) : fredholmTerm K ν φ k = 0 := by
  rw [fredholmTerm_eq_sum_minors ν ψ hψ hψb K hK φ hφ hφb k,
    Finset.powersetCard_eq_empty.mpr (by simpa using hk), Finset.sum_empty, mul_zero]

/-- The Fredholm series of a finite-rank kernel sums to `det (1 - G)`: under
the hypotheses of `fredholmIntegral_eq_sum_det_submatrix` (no orthonormality
needed), `HasSum (fredholmTerm K ν φ) (det (1 - weightedGram ν ψ φ))`. -/
theorem hasSum_fredholmTerm_det_one_sub (ν : Measure ℝ) [IsFiniteMeasure ν]
    (ψ : ι → ℝ → ℝ) (hψ : ∀ i, Measurable (ψ i)) (hψb : ∃ C, ∀ i a, |ψ i a| ≤ C)
    (K : ℝ → ℝ → ℝ) (hK : ∀ x y, K x y = ∑ i, ψ i x * ψ i y)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hφb : ∃ C, ∀ a, |φ a| ≤ C) :
    HasSum (fun k => fredholmTerm K ν φ k) (1 - weightedGram ν ψ φ).det := by
  rw [det_one_sub_eq_sum_minors]
  have h := hasSum_sum_of_ne_finset_zero (f := fun k => fredholmTerm K ν φ k)
    (s := Finset.range (Fintype.card ι + 1)) (L := SummationFilter.unconditional ℕ)
    fun k hk => fredholmTerm_eq_zero_of_card_lt ν ψ hψ hψb K hK φ hφ hφb
      (by simpa [Nat.lt_succ_iff] using hk)
  convert h using 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fredholmTerm_eq_sum_minors ν ψ hψ hψb K hK φ hφ hφb k]

/-- Andréief form of `det (1 - G)` for an orthonormal family. Let `ν` be a
finite measure on `ℝ`, `ψ : ι → ℝ → ℝ` bounded measurable with
`∫ ψ i * ψ j dν = [i = j]`, and `φ` bounded measurable. Then
`det (1 - weightedGram ν ψ φ) =
  (card ι)!⁻¹ * ∫ det [ψ i (x j)]² ∏ j (1 - φ (x j)) dν^ι`. -/
theorem det_one_sub_weightedGram_eq_integral (ν : Measure ℝ) [IsFiniteMeasure ν]
    (ψ : ι → ℝ → ℝ) (hψ : ∀ i, Measurable (ψ i)) (hψb : ∃ C, ∀ i a, |ψ i a| ≤ C)
    (hON : ∀ i j, ∫ a, ψ i a * ψ j a ∂ν = if i = j then 1 else 0)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hφb : ∃ C, ∀ a, |φ a| ≤ C) :
    (1 - weightedGram ν ψ φ).det =
      ((Fintype.card ι).factorial : ℝ)⁻¹ * ∫ x : ι → ℝ,
        (Matrix.of fun i j => ψ i (x j)).det ^ 2 * ∏ j, (1 - φ (x j))
        ∂Measure.pi (fun _ => ν) := by
  obtain ⟨C, hC⟩ := hψb
  obtain ⟨D, hD⟩ := hφb
  set g : ι → ℝ → ℝ := fun i a => (1 - φ a) * ψ i a with hg
  have hgm : ∀ i, Measurable (g i) := fun i => (measurable_const.sub hφ).mul (hψ i)
  have hgb : ∃ C', ∀ i a, |g i a| ≤ C' := by
    refine ⟨(1 + |D|) * C, fun i a => ?_⟩
    rw [hg, abs_mul]
    have h1 : |1 - φ a| ≤ 1 + |D| := by
      calc |1 - φ a| ≤ |(1 : ℝ)| + |φ a| := abs_sub _ _
        _ ≤ 1 + |D| := by rw [abs_one]; linarith [hD a, le_abs_self D]
    exact mul_le_mul h1 (hC i a) (abs_nonneg _) (by positivity)
  have hpt : ∀ x : ι → ℝ, (Matrix.of fun i j => ψ i (x j)).det ^ 2 * ∏ j, (1 - φ (x j)) =
      (Matrix.of fun i j => ψ i (x j)).det * (Matrix.of fun i j => g i (x j)).det := by
    intro x
    have : (Matrix.of fun i j => g i (x j)) =
        Matrix.of fun i j => (1 - φ (x j)) * (Matrix.of fun i j => ψ i (x j)) i j := by
      ext i j
      simp [hg]
    rw [this, det_mul_row]
    ring
  simp_rw [hpt]
  rw [andreief ν ψ g hψ hgm ⟨C, hC⟩ hgb]
  have hent : (Matrix.of fun i j => ∫ a, ψ i a * g j a ∂ν) = 1 - weightedGram ν ψ φ := by
    ext i j
    have hi1 : Integrable (fun a => ψ i a * ψ j a) ν :=
      integrable_of_measurable_of_abs_le ((hψ i).mul (hψ j)) (C * C) fun a => by
        rw [abs_mul]
        exact mul_le_mul (hC _ _) (hC _ _) (abs_nonneg _) ((abs_nonneg _).trans (hC i a))
    have hi2 : Integrable (fun a => ψ i a * ψ j a * φ a) ν :=
      integrable_of_measurable_of_abs_le (((hψ i).mul (hψ j)).mul hφ) (C * C * D) fun a => by
        have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC i a)
        rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul (hC _ _) (hC _ _) (abs_nonneg _) hC0) (hD a)
          (abs_nonneg _) (mul_nonneg hC0 hC0)
    have : (fun a => ψ i a * g j a) = fun a => ψ i a * ψ j a - ψ i a * ψ j a * φ a := by
      funext a
      simp only [hg]
      ring
    rw [of_apply, this, integral_sub hi1 hi2, hON, Matrix.sub_apply, weightedGram, of_apply,
      Matrix.one_apply]
  rw [hent, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
    one_mul]

/-- **Finite projection identity, vanishing terms.** Let `ν` be a finite
measure on `ℝ`, `ψ : ι → ℝ → ℝ` measurable and bounded, `K x y = ∑ i, ψ i x * ψ i y`,
and `φ : ℝ → ℝ` measurable and bounded. Then `fredholmTerm K ν φ k = 0` whenever
`card ι < k`. (Orthonormality is not needed; this is
`fredholmTerm_eq_zero_of_card_lt`, restated with the orthonormality hypothesis
of the projection setting.) -/
theorem finiteProjection_fredholmTerm_eq_zero (ν : Measure ℝ) [IsFiniteMeasure ν]
    (ψ : ι → ℝ → ℝ) (hψ : ∀ i, Measurable (ψ i)) (hψb : ∃ C, ∀ i a, |ψ i a| ≤ C)
    (_hON : ∀ i j, ∫ a, ψ i a * ψ j a ∂ν = if i = j then 1 else 0)
    (K : ℝ → ℝ → ℝ) (hK : ∀ x y, K x y = ∑ i, ψ i x * ψ i y)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hφb : ∃ C, ∀ a, |φ a| ≤ C) {k : ℕ}
    (hk : Fintype.card ι < k) : fredholmTerm K ν φ k = 0 :=
  fredholmTerm_eq_zero_of_card_lt ν ψ hψ hψb K hK φ hφ hφb hk

/-- **Finite projection identity.** Let `ν` be a finite measure on `ℝ`,
`ψ : ι → ℝ → ℝ` measurable and uniformly bounded with
`∫ ψ i a * ψ j a dν = [i = j]`, `K x y = ∑ i, ψ i x * ψ i y`, and `φ : ℝ → ℝ`
measurable and bounded. Then the Fredholm terms of `(K, ν, φ)` sum to
`(card ι)!⁻¹ * ∫ det [ψ i (x j)]² ∏ j (1 - φ (x j)) dν^ι`
(integral over `x : ι → ℝ` against `Measure.pi (fun _ => ν)`). -/
theorem finiteProjection_hasSum_fredholmTerm (ν : Measure ℝ) [IsFiniteMeasure ν]
    (ψ : ι → ℝ → ℝ) (hψ : ∀ i, Measurable (ψ i)) (hψb : ∃ C, ∀ i a, |ψ i a| ≤ C)
    (hON : ∀ i j, ∫ a, ψ i a * ψ j a ∂ν = if i = j then 1 else 0)
    (K : ℝ → ℝ → ℝ) (hK : ∀ x y, K x y = ∑ i, ψ i x * ψ i y)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hφb : ∃ C, ∀ a, |φ a| ≤ C) :
    HasSum (fun k => fredholmTerm K ν φ k)
      (((Fintype.card ι).factorial : ℝ)⁻¹ * ∫ x : ι → ℝ,
        (Matrix.of fun i j => ψ i (x j)).det ^ 2 * ∏ j, (1 - φ (x j))
        ∂Measure.pi (fun _ => ν)) := by
  rw [← det_one_sub_weightedGram_eq_integral ν ψ hψ hψb hON φ hφ hφb]
  exact hasSum_fredholmTerm_det_one_sub ν ψ hψ hψb K hK φ hφ hφb

/-- **Finite projection identity, series form.** Under the hypotheses of
`finiteProjection_hasSum_fredholmTerm`,
`fredholmSeries K ν φ = (card ι)!⁻¹ * ∫ det [ψ i (x j)]² ∏ j (1 - φ (x j)) dν^ι`. -/
theorem finiteProjection_fredholmSeries_eq (ν : Measure ℝ) [IsFiniteMeasure ν]
    (ψ : ι → ℝ → ℝ) (hψ : ∀ i, Measurable (ψ i)) (hψb : ∃ C, ∀ i a, |ψ i a| ≤ C)
    (hON : ∀ i j, ∫ a, ψ i a * ψ j a ∂ν = if i = j then 1 else 0)
    (K : ℝ → ℝ → ℝ) (hK : ∀ x y, K x y = ∑ i, ψ i x * ψ i y)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hφb : ∃ C, ∀ a, |φ a| ≤ C) :
    fredholmSeries K ν φ =
      ((Fintype.card ι).factorial : ℝ)⁻¹ * ∫ x : ι → ℝ,
        (Matrix.of fun i j => ψ i (x j)).det ^ 2 * ∏ j, (1 - φ (x j))
        ∂Measure.pi (fun _ => ν) :=
  (finiteProjection_hasSum_fredholmTerm ν ψ hψ hψb hON K hK φ hφ hφb).tsum_eq

end BlockBand.Endpoints
