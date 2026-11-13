module
public import BlockBand.Foundations.Spectral.OrderedEigenpairs

/-!
# Positive scaling of ordered Hermitian eigenvalues

For a Hermitian matrix `A` and `s > 0`, the characteristic roots of `s A` are `s` times
those of `A`, and every increasingly ordered eigenvalue of `s A` is `s` times the
corresponding eigenvalue of `A`.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open Matrix Polynomial Unitary
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Matrix ι ι ℂ}

theorem charpoly_positiveScale (hA : A.IsHermitian) (s : ℝ) :
    ((s : ℂ) • A).charpoly =
      ∏ i, (X - C ((s * hA.eigenvalues i : ℝ) : ℂ)) := by
  have hd : (s : ℂ) • A =
      conjStarAlgAut ℂ _ hA.eigenvectorUnitary
        (diagonal (fun i => ((s * hA.eigenvalues i : ℝ) : ℂ))) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [← map_smul]
    congr 1
    ext i j
    simp [diagonal_apply, Function.comp_def, mul_ite]
  rw [hd, conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc]
  simp [charpoly_diagonal]

theorem roots_positiveScale (hA : A.IsHermitian) (s : ℝ) :
    ((s : ℂ) • A).charpoly.roots =
      Multiset.map (fun i => ((s * hA.eigenvalues i : ℝ) : ℂ)) Finset.univ.val := by
  rw [charpoly_positiveScale hA s, Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero _)

theorem eigenvaluesOrdered_positiveScale (hA : A.IsHermitian) (s : ℝ) (hs : 0 < s)
    (hS : ((s : ℂ) • A).IsHermitian) :
    hS.eigenvalues₀ = fun i => s * hA.eigenvalues₀ i := by
  have hr : (((s : ℂ) • A).charpoly.roots.map (RCLike.re : ℂ → ℝ)) =
      Multiset.map (fun i => s * hA.eigenvalues₀ i) Finset.univ.val := by
    rw [roots_positiveScale hA s, Multiset.map_map]
    simp only [Function.comp_def]
    change Multiset.map (fun i : ι => s * hA.eigenvalues₀
      ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm i))
        Finset.univ.val = _
    change Multiset.map ((fun i => s * hA.eigenvalues₀ i) ∘
      (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm)
        Finset.univ.val = _
    rw [← Multiset.map_map]
    congr 1
    exact Multiset.map_univ_val_equiv _
  apply List.ofFn_inj.mp
  rw [← hS.sort_roots_charpoly_eq_eigenvalues₀, hr]
  simp only [Fin.univ_val_map, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  apply Antitone.sortedGE_ofFn
  intro i j hij
  exact mul_le_mul_of_nonneg_left (hA.eigenvalues₀_antitone hij) hs.le

theorem increasingEigenvalue_positiveScale (hA : A.IsHermitian) (s : ℝ) (hs : 0 < s)
    (hS : ((s : ℂ) • A).IsHermitian) (i : Fin (Fintype.card ι)) :
    BlockBand.Foundations.Spectral.increasingEigenvalue hS i =
      s * BlockBand.Foundations.Spectral.increasingEigenvalue hA i := by
  exact congrFun (eigenvaluesOrdered_positiveScale hA s hs hS) i.rev

end BlockBand.Counting
