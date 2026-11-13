module

public import BlockBand.SourceProcess.CapLimit.Restrict

/-!
# Feasibility: zero columns and restriction

* `re_diag_nonneg`: `Re M_yy ≥ 0`;
* `zero_of_re_diag_nonpos`: if `Re M_yy ≤ 0` then column `y` of `V` vanishes, so every entry of
  `M` and `B` in row or column `y` vanishes;
* `gramFeasible_gRestrict`: if `M` vanishes outside the range of `r` and the signature does not
  couple the range with its complement, the restricted state is feasible for the restricted
  signature.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapLimit

open Matrix Function
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic

variable {c₁ c₂ : Type*} {r : c₁ → c₂}

theorem re_star_mul_self (z : ℂ) : (star z * z).re = Complex.normSq z := by
  simp [Complex.mul_re, Complex.normSq_apply]

theorem re_sourceGram_diag {n : Type*} [Fintype n] (V : Matrix n c₂ ℂ) (y : c₂) :
    (sourceGram V y y).re = ∑ x, Complex.normSq (V x y) := by
  simp only [sourceGram, mul_apply, conjTranspose_apply, Complex.re_sum, re_star_mul_self]

theorem re_diag_nonneg [Fintype c₂] {D : Matrix c₂ c₂ ℂ}
    {G : Matrix c₂ c₂ ℂ × Matrix c₂ c₂ ℂ} (hG : GramFeasible D G) (y : c₂) :
    0 ≤ (G.1 y y).re := by
  obtain ⟨n, P, V, -, -, -, rfl⟩ := hG
  rw [show (gramPair P V).1 = sourceGram V from rfl, re_sourceGram_diag]
  exact Finset.sum_nonneg fun x _ => Complex.normSq_nonneg _

theorem zero_of_re_diag_nonpos [Fintype c₂] {D : Matrix c₂ c₂ ℂ}
    {G : Matrix c₂ c₂ ℂ × Matrix c₂ c₂ ℂ} (hG : GramFeasible D G) {y : c₂}
    (hy : (G.1 y y).re ≤ 0) :
    ∀ z, G.1 y z = 0 ∧ G.1 z y = 0 ∧ G.2 y z = 0 ∧ G.2 z y = 0 := by
  obtain ⟨n, P, V, -, -, -, rfl⟩ := hG
  rw [show (gramPair P V).1 = sourceGram V from rfl, re_sourceGram_diag] at hy
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => Complex.normSq_nonneg (V x y)).1
    (le_antisymm hy (Finset.sum_nonneg fun x _ => Complex.normSq_nonneg _))
  have hV : ∀ x, V x y = 0 := fun x => Complex.normSq_eq_zero.1 (h0 x (Finset.mem_univ _))
  intro z
  simp only [gramPair, sourceGram, nearGram, mul_apply, conjTranspose_apply, hV, star_zero,
    zero_mul, mul_zero, Finset.sum_const_zero, and_self]

/-- A feasible state whose diagonal vanishes outside the range of `r` vanishes there. -/
theorem gsupp_of_feasible [Fintype c₂] {D : Matrix c₂ c₂ ℂ}
    {G : Matrix c₂ c₂ ℂ × Matrix c₂ c₂ ℂ} (hG : GramFeasible D G)
    (h : ∀ y, y ∉ Set.range r → (G.1 y y).re ≤ 0) : GSupp r G :=
  ⟨fun y hy z => ⟨(zero_of_re_diag_nonpos hG (h y hy) z).1,
      (zero_of_re_diag_nonpos hG (h y hy) z).2.1⟩,
    fun y hy z => ⟨(zero_of_re_diag_nonpos hG (h y hy) z).2.2.1,
      (zero_of_re_diag_nonpos hG (h y hy) z).2.2.2⟩⟩

theorem mul_mul_conjTranspose_submatrix [Fintype c₁] [Fintype c₂] {n : Type*} [Fintype n]
    (hr : Injective r) {V : Matrix n c₂ ℂ} (hV : ∀ x z, z ∉ Set.range r → V x z = 0)
    (D : Matrix c₂ c₂ ℂ) :
    V * D * Vᴴ = V.submatrix id r * D.submatrix r r * (V.submatrix id r)ᴴ := by
  ext i j
  simp only [mul_apply, submatrix_apply, conjTranspose_apply, id]
  rw [sum_range_of_zero hr (fun z hz => by rw [hV j z hz, star_zero, mul_zero])]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sum_range_of_zero hr (fun w hw => by rw [hV i w hw, zero_mul])]

/-- **Feasibility restricts.** -/
theorem gramFeasible_gRestrict [Fintype c₁] [Fintype c₂] (hr : Injective r)
    {D : Matrix c₂ c₂ ℂ} {G : Matrix c₂ c₂ ℂ × Matrix c₂ c₂ ℂ} (hG : GramFeasible D G)
    (hS : Supp r G.1) : GramFeasible (D.submatrix r r) (gRestrict r G) := by
  obtain ⟨n, P, V, hP1, hP2, hTP, rfl⟩ := hG
  have hV : ∀ x z, z ∉ Set.range r → V x z = 0 := by
    intro x z hz
    have h := (hS z hz z).1
    have hre : (sourceGram V z z).re ≤ 0 := by
      rw [show sourceGram V z z = (gramPair P V).1 z z from rfl, h, Complex.zero_re]
    rw [re_sourceGram_diag] at hre
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => Complex.normSq_nonneg (V x z)).1
      (le_antisymm hre (Finset.sum_nonneg fun x _ => Complex.normSq_nonneg _))
    exact Complex.normSq_eq_zero.1 (h0 x (Finset.mem_univ _))
  have hproj : gramProjection P V D = gramProjection P (V.submatrix id r) (D.submatrix r r) := by
    unfold gramProjection
    rw [mul_mul_conjTranspose_submatrix hr hV]
  refine ⟨n, P, V.submatrix id r, hP1, hP2, ?_, rfl⟩
  unfold TwoProjection at hTP ⊢
  rw [← hproj]
  exact hTP

end BlockBand.SourceProcess.CapLimit
