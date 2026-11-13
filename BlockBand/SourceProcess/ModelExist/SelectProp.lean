module

public import BlockBand.SourceProcess.ModelExist.SelectMeas

/-!
# The perpendicular selection meets its specification

`perpSel_spec`: the perpendicular selection returns a vector meeting its specification, so
`PerpSelection` holds for every finite column type (`perpSelection_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open Matrix Finset MeasureTheory
open scoped ComplexOrder

variable {c' : Type*} [Fintype c'] [DecidableEq c'] {n : ℕ} (cur : c' → Prop) [DecidablePred cur]

theorem candQ_lin (H : Matrix c' c' ℂ × Matrix c' c' ℂ) (prev : Fin n → c' → ℂ) (k : c') :
    SelLin cur H prev (candQ cur H prev k) := by
  refine (selG_mulVec_eq_zero cur).1 ?_
  rw [candQ, mulVec_mulVec, mul_specProj, zero_mulVec]

omit [DecidableEq c'] [DecidablePred cur] in
theorem selLin_smul {H : Matrix c' c' ℂ × Matrix c' c' ℂ} {prev : Fin n → c' → ℂ} {a : c' → ℂ}
    (h : SelLin cur H prev a) (z : ℂ) : SelLin cur H prev (z • a) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [mulVec_smul, h1, smul_zero], fun k hk => ?_, fun l => ?_⟩
  · rw [mulVec_smul, Pi.smul_apply, h2 k hk, smul_zero]
  · rw [mulVec_smul, dotProduct_smul, h3 l, smul_zero]

theorem exists_candR_pos {H : Matrix c' c' ℂ × Matrix c' c' ℂ} {prev : Fin n → c' → ℂ}
    (hM : H.1.PosSemidef) (hE : SelExists cur H prev) : ∃ k, 0 < candR cur H prev k := by
  obtain ⟨w, hwlin, hMw⟩ := hE
  have hPw := specProj_mulVec_of (selG cur H prev) ((selG_mulVec_eq_zero cur).2 hwlin)
  by_contra hall
  push Not at hall
  have hMq : ∀ k, H.1 *ᵥ candQ cur H prev k = 0 := fun k => by
    have h0 := hM.dotProduct_mulVec_nonneg (candQ cur H prev k)
    have hz : star (candQ cur H prev k) ⬝ᵥ (H.1 *ᵥ candQ cur H prev k) = 0 := by
      obtain ⟨hre, him⟩ := Complex.le_def.1 h0
      apply Complex.ext
      · exact le_antisymm (hall k) hre
      · exact him.symm
    exact (hM.dotProduct_mulVec_zero_iff).1 hz
  have hMP : H.1 * specProj (selG cur H prev) = 0 := by
    ext i k
    have := congrFun (hMq k) i
    rw [candQ, mulVec_mulVec] at this
    simpa [mulVec, dotProduct, Pi.single_apply] using this
  apply hMw
  rw [← hPw, mulVec_mulVec, hMP, zero_mulVec]

theorem perpSel_spec (H : Matrix c' c' ℂ × Matrix c' c' ℂ) (prev : Fin n → c' → ℂ) (v : ℝ)
    (hv : 0 ≤ v) (hM : H.1.PosSemidef) (hE : SelExists cur H prev) :
    SelSpec cur H prev v (perpSel cur (H, prev, v)) := by
  set e := Fintype.equivFin c'
  obtain ⟨k0, hk0⟩ := exists_candR_pos cur hM hE
  set S := univ.filter fun j : Fin (Fintype.card c') => 0 < candR cur H prev (e.symm j)
  have hS : S.Nonempty := ⟨e k0, by simp [S, hk0]⟩
  set j0 := S.min' hS
  have hj0 : IsFirst cur H prev j0 := by
    refine ⟨(Finset.mem_filter.1 (S.min'_mem hS)).2, fun j' hj' hpos => ?_⟩
    have hmem : j' ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hpos⟩
    exact absurd (S.min'_le j' hmem) (not_le.2 hj')
  have huniq : ∀ j, IsFirst cur H prev j → j = j0 := fun j hj => by
    rcases lt_trichotomy j j0 with h | h | h
    · exact absurd hj.1 (hj0.2 j h)
    · exact h
    · exact absurd hj0.1 (hj.2 j0 h)
  have hsel : perpSel cur (H, prev, v) =
      ((Real.sqrt (v / candR cur H prev (e.symm j0)) : ℝ) : ℂ) • candQ cur H prev (e.symm j0) := by
    unfold perpSel
    rw [Finset.sum_eq_single j0 (fun j _ hj => ite_eq_right (fun h => hj (huniq j h))) (by simp),
      ite_eq_left hj0]
  rw [hsel]
  refine ⟨selLin_smul cur (candQ_lin cur H prev _) _, ?_⟩
  set q := candQ cur H prev (e.symm j0)
  have hr : 0 < candR cur H prev (e.symm j0) := hj0.1
  have hreal : star q ⬝ᵥ (H.1 *ᵥ q) = ((candR cur H prev (e.symm j0) : ℝ) : ℂ) := by
    obtain ⟨-, him⟩ := Complex.le_def.1 (hM.dotProduct_mulVec_nonneg q)
    apply Complex.ext
    · rfl
    · simpa using him.symm
  rw [mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, hreal]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (div_nonneg hv hr.le),
    ← Complex.ofReal_mul, div_mul_cancel₀ v hr.ne']

/-- **`PerpSelection` holds for every finite column type.** -/
theorem perpSelection_holds : PerpSelection c' n cur :=
  ⟨perpSel cur, measurable_perpSel cur, fun H prev v hv hM _ hE => perpSel_spec cur H prev v hv hM hE⟩

end BlockBand.SourceProcess.ModelExist
