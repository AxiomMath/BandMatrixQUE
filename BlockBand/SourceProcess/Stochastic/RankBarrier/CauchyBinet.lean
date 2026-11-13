module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Fintype.Perm
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Cauchy–Binet over index functions

The proof of the finite Gram law uses `e_k(U*U) = ‖∧^k U‖²_HS`, by
Cauchy–Binet. We use minors indexed by *functions* `f : n → m` (not subsets), which avoids
orderings: for `A : n × m`, `B : m × n`,

  `|Perm n| · det (A B) = ∑_{f : n → m} det (A_{·,f}) det (B_{f,·})`   (`cauchyBinet`),

and the counting identity `∑_{g : Fin k → c} det A_{g,g} = k! ∑_{|s| = k} det A_{s,s}`
(`sum_det_submatrix_self`). Pure algebra over a commutative ring; no norm or measure.
-/

namespace BlockBand.SourceProcess.Stochastic.RankBarrierProof
open Matrix Equiv Finset

variable {R : Type*} [CommRing R]
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

/-- Expansion of `det (A B)` over index functions (one Leibniz expansion). -/
theorem det_mul_eq_sum_fun (A : Matrix n m R) (B : Matrix m n R) :
    det (A * B) = ∑ f : n → m, det (A.submatrix id f) * ∏ i, B (f i) i := by
  calc det (A * B) = ∑ f : n → m, ∑ σ : Perm n, ((Perm.sign σ : ℤ) : R) * ∏ i, A (σ i) (f i) * B (f i) i := by
        simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ]
        rw [Finset.sum_comm]
    _ = ∑ f : n → m, det (A.submatrix id f) * ∏ i, B (f i) i := by
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [det_apply', Finset.sum_mul]
        refine Finset.sum_congr rfl fun σ _ => ?_
        simp only [submatrix_apply, id, prod_mul_distrib, mul_assoc]

/-- **Cauchy–Binet over index functions.** -/
theorem cauchyBinet (A : Matrix n m R) (B : Matrix m n R) :
    (Fintype.card (Perm n) : R) * det (A * B) =
      ∑ f : n → m, det (A.submatrix id f) * det (B.submatrix f id) := by
  have hπ : ∀ π : Perm n, ∑ f : n → m, ((Perm.sign π : ℤ) : R) * det (A.submatrix id f) * ∏ i, B (f (π i)) i =
      det (A * B) := by
    intro π
    rw [det_mul_eq_sum_fun, ← (Equiv.arrowCongr π (Equiv.refl m)).sum_comp]
    refine Finset.sum_congr rfl fun f _ => ?_
    have h1 : A.submatrix id ((Equiv.arrowCongr π (Equiv.refl m)) f) =
        (A.submatrix id f).submatrix id π.symm := rfl
    have h2 : ∀ i, (Equiv.arrowCongr π (Equiv.refl m)) f (π i) = f i := by
      intro i; simp [Equiv.arrowCongr_apply]
    rw [h1, det_permute', Perm.sign_symm]
    simp only [h2]
    have hs : ((Perm.sign π : ℤ) : R) * ((Perm.sign π : ℤ) : R) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    calc ((Perm.sign π : ℤ) : R) * (((Perm.sign π : ℤ) : R) * det (A.submatrix id f)) * ∏ i, B (f i) i
        = (((Perm.sign π : ℤ) : R) * ((Perm.sign π : ℤ) : R)) * det (A.submatrix id f) * ∏ i, B (f i) i := by ring
      _ = _ := by rw [hs, one_mul]
  calc (Fintype.card (Perm n) : R) * det (A * B) = ∑ _π : Perm n, det (A * B) := by
        simp [Finset.card_univ]
    _ = ∑ π : Perm n, ∑ f : n → m, ((Perm.sign π : ℤ) : R) * det (A.submatrix id f) * ∏ i, B (f (π i)) i :=
        Finset.sum_congr rfl fun π _ => (hπ π).symm
    _ = ∑ f : n → m, det (A.submatrix id f) * det (B.submatrix f id) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [det_apply' (B.submatrix f id), Finset.mul_sum]
        refine Finset.sum_congr rfl fun π _ => ?_
        simp only [submatrix_apply, id]
        ring

/-- The principal submatrix on a finset `s`, indexed by the subtype. -/
abbrev principalSub {c : Type*} (A : Matrix c c R) (s : Finset c) : Matrix s s R :=
  A.submatrix (fun i : s => (i : c)) (fun i : s => (i : c))

/-- Sum over the fibre of `g ↦ image g` above a `k`-set `s`: `k!` copies of `det A_{s,s}`. -/
theorem sum_fiber_det_submatrix {c : Type*} [Fintype c] [DecidableEq c] (A : Matrix c c R)
    (k : ℕ) (s : Finset c) (hs : s.card = k) :
    ∑ g : Fin k → c with Finset.univ.image g = s, det (A.submatrix g g) =
      (k.factorial : R) * det (principalSub A s) := by
  have hcard : Fintype.card (Fin k ≃ s) = k.factorial := by
    have e : Fin k ≃ s := Fintype.equivOfCardEq (by simp [hs])
    rw [Fintype.card_equiv e, Fintype.card_fin]
  symm
  calc (k.factorial : R) * det (principalSub A s)
      = ∑ e : Fin k ≃ s, det (principalSub A s) := by simp [Finset.card_univ, hcard]
    _ = ∑ e : Fin k ≃ s, det (A.submatrix (fun i => (e i : c)) (fun i => (e i : c))) :=
        Finset.sum_congr rfl fun e _ => (det_submatrix_equiv_self e (principalSub A s)).symm
    _ = _ := by
      refine Finset.sum_bij (fun e _ => fun i => (e i : c)) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro e _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        ext x
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, rfl⟩; exact (e i).2
        · intro hx; exact ⟨e.symm ⟨x, hx⟩, by simp⟩
      · intro e₁ _ e₂ _ h
        ext i
        exact congrFun h i
      · intro g hg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
        have hinj : Function.Injective g := by
          have h1 : (Finset.univ.image g).card = (Finset.univ : Finset (Fin k)).card := by
            rw [hg, hs, Finset.card_univ, Fintype.card_fin]
          have := Finset.card_image_iff.mp h1
          intro a b hab
          exact this (Finset.mem_coe.2 (Finset.mem_univ a))
            (Finset.mem_coe.2 (Finset.mem_univ b)) hab
        have hmem : ∀ i, g i ∈ s := fun i => hg ▸ Finset.mem_image_of_mem g (Finset.mem_univ i)
        let g' : Fin k → s := fun i => ⟨g i, hmem i⟩
        have hbij : Function.Bijective g' := by
          rw [Fintype.bijective_iff_injective_and_card]
          refine ⟨fun a b hab => hinj (congrArg Subtype.val hab), ?_⟩
          simp [hs]
        exact ⟨Equiv.ofBijective g' hbij, Finset.mem_univ _, rfl⟩

/-- **Counting identity**: `∑_{g : Fin k → c} det A_{g,g} = k! · ∑_{|s|=k} det A_{s,s}`. -/
theorem sum_det_submatrix_self {c : Type*} [Fintype c] [DecidableEq c] (A : Matrix c c R)
    (k : ℕ) :
    ∑ g : Fin k → c, det (A.submatrix g g) =
      (k.factorial : R) * ∑ s ∈ (Finset.univ : Finset c).powersetCard k, det (principalSub A s) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun g : Fin k → c => Finset.univ.image g), Finset.mul_sum]
  rw [← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset c).powersetCard k))
    (f := fun s => ∑ g : Fin k → c with Finset.univ.image g = s, det (A.submatrix g g)) ?_]
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mem_powersetCard] at hs
    exact sum_fiber_det_submatrix A k s hs.2
  · intro s _ hs
    rw [Finset.mem_powersetCard, not_and] at hs
    have hsk : s.card ≠ k := hs (Finset.subset_univ _)
    refine Finset.sum_eq_zero fun g hg => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    have hni : ¬ Function.Injective g := by
      intro hinj
      apply hsk
      rw [← hg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, g i = g j ∧ i ≠ j := by
      by_contra h
      push Not at h
      exact hni fun i j hij => h i j hij
    exact det_zero_of_row_eq hne (by ext l; simp [hij])

end BlockBand.SourceProcess.Stochastic.RankBarrierProof
