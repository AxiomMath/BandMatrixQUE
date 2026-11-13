module

public import BlockBand.Transmission.Bridge.NullDet

/-!
# Null determinant set of a random diagonal perturbation

For an atomless law `μ` on `ℝ`, a fixed complex matrix `C` and `d ~ μ^{⊗n}`, the determinant
`det(diag d + C)` vanishes only on a null set. The proof expands the determinant as an affine
function of `d₀` and inducts on the size.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Bridge

open MeasureTheory Matrix
open scoped Matrix

/-- `det(diag d + C) = d₀ · det(diag(d ∘ succ) + C₊₊) + det(diag(d with d₀ = 0) + C)`. -/
theorem det_diagonal_add_affine (n : ℕ) (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (d : Fin (n + 1) → ℝ) :
    (diagonal (fun x => (d x : ℂ)) + C).det =
      (d 0 : ℂ) * (diagonal (fun x : Fin n => (d x.succ : ℂ)) + C.submatrix Fin.succ Fin.succ).det +
        (diagonal (fun x => (Function.update d 0 0 x : ℂ)) + C).det := by
  have hminor : ∀ j : Fin (n + 1),
      (diagonal (fun x => (d x : ℂ)) + C).submatrix Fin.succ j.succAbove =
      (diagonal (fun x => (Function.update d 0 0 x : ℂ)) + C).submatrix Fin.succ j.succAbove := by
    intro j; ext i l
    simp [Matrix.diagonal_apply]
  have hcof : (diagonal (fun x => (d x : ℂ)) + C).submatrix Fin.succ Fin.succ =
      diagonal (fun x : Fin n => (d x.succ : ℂ)) + C.submatrix Fin.succ Fin.succ := by
    ext i l; simp [Matrix.diagonal_apply]
  have hcof' : (diagonal (fun x => (Function.update d 0 0 x : ℂ)) + C).submatrix Fin.succ Fin.succ =
      diagonal (fun x : Fin n => (d x.succ : ℂ)) + C.submatrix Fin.succ Fin.succ := by
    ext i l; simp [Matrix.diagonal_apply]
  rw [Matrix.det_succ_row_zero, Matrix.det_succ_row_zero (diagonal _ + C), Fin.sum_univ_succ,
    Fin.sum_univ_succ]
  simp only [Fin.succAbove_zero]
  rw [hcof, hcof']
  simp_rw [hminor]
  have h0 : ∀ x : Fin n, ((0 : Fin (n + 1)) = x.succ) = False :=
    fun x => propext ⟨fun h => Fin.succ_ne_zero x h.symm, False.elim⟩
  simp [h0]
  ring

/-- **`det(diag d + C)` vanishes on a null set** of `d ~ μ^{⊗n}`, for every fixed `C`. -/
theorem pi_det_diagonal_add_null (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} = 0) :
    ∀ (n : ℕ) (C : Matrix (Fin n) (Fin n) ℂ), (Measure.pi fun _ : Fin n => μ)
      {d | (diagonal (fun x => (d x : ℂ)) + C).det = 0} = 0
  | 0, C => by simp [Matrix.det_fin_zero]
  | n + 1, C => by
    set c : (Fin (n + 1) → ℝ) → ℂ :=
      fun d => (diagonal (fun x : Fin n => (d x.succ : ℂ)) + C.submatrix Fin.succ Fin.succ).det
    set g : (Fin (n + 1) → ℝ) → ℂ :=
      fun d => (diagonal (fun x => (Function.update d 0 0 x : ℂ)) + C).det
    have hdiag : ∀ {m : ℕ} (D : Matrix (Fin m) (Fin m) ℂ),
        Measurable fun d : Fin m → ℝ => (diagonal (fun x => (d x : ℂ)) + D).det := by
      intro m D
      refine measurable_det.comp (Measurable.of_eval_matrix _ fun x y => ?_)
      simp only [Matrix.add_apply, Matrix.diagonal_apply]
      split_ifs
      · exact (Complex.measurable_ofReal.comp (measurable_pi_apply x)).add measurable_const
      · exact measurable_const
    have hR : Measurable fun (d : Fin (n + 1) → ℝ) (x : Fin n) => d x.succ :=
      Measurable.of_eval fun _ => measurable_pi_apply _
    have hc : Measurable c := (hdiag _).comp hR
    have hU : Measurable fun d : Fin (n + 1) → ℝ => Function.update d 0 0 :=
      (measurable_update_coord 0).comp (measurable_id.prodMk measurable_const)
    have hg : Measurable g := (hdiag C).comp hU
    have hsub : {d : Fin (n + 1) → ℝ | (diagonal (fun x => (d x : ℂ)) + C).det = 0} ⊆
        {d | c d = 0} ∪ {d | c d ≠ 0 ∧ (d 0 : ℂ) * c d + g d = 0} := by
      intro d hd
      by_cases h : c d = 0
      · exact Or.inl h
      · exact Or.inr ⟨h, by rw [← det_diagonal_add_affine]; exact hd⟩
    refine measure_mono_null hsub (measure_union_null ?_ ?_)
    · have hmap := infinitePi_map_reindex μ (Fin.succ : Fin n → Fin (n + 1)) (Fin.succ_injective n)
      rw [Measure.infinitePi_eq_pi] at hmap
      have hmeas : MeasurableSet {d : Fin n → ℝ |
          (diagonal (fun x => (d x : ℂ)) + C.submatrix Fin.succ Fin.succ).det = 0} :=
        (measurableSet_singleton (0 : ℂ)).preimage (hdiag (C.submatrix Fin.succ Fin.succ))
      have := pi_det_diagonal_add_null μ hμ n (C.submatrix Fin.succ Fin.succ)
      rw [← hmap, Measure.map_apply hR hmeas] at this
      exact this
    · refine null_affine_coord μ hμ 0 c g hc hg (fun d t => ?_) (fun d t => ?_)
      · simp only [c]
        congr 3
      · simp only [g, Function.update_idem]

end BlockBand.Transmission.Bridge
