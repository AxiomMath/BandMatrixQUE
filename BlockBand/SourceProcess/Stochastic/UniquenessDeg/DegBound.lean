module
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.DegAlg
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Pointwise bounds for the degenerate Gronwall estimates

At a point where the joint density is `zDens s` (`s = c.σ(Y_r)`) and the regularized driver
integrand is `hval s ε`, with Euler coefficients `Γ = c.σ(E_j)`:
* **`quad_sum_vsY_le`** (Euler driven by the regularized driver versus the solution):
  `∑_i qZ(Γ hval − e_i) ≤ 2 ‖Γ - s‖² + 2 ‖s‖² frob(tikX s ε - pinvX s)`.
* **`quad_sum_vsX_le`** (two Euler schemes with two regularizations):
  `∑_i qZ(Γ hval_ε − Γ' hval_ε') ≤ 2 ‖Γ - Γ'‖² + 2 ‖Γ'‖² frob(tikX s ε - tikX s ε')`;
  `quad_sum_off` (outside the stochastic interval): `∑_i qZ((Γ - Γ') offval) = ‖Γ - Γ'‖²`.
* `frob_tikX_sub_pinvX_le`: `frob(tikX - pinvX) ≤ 4d`.
-/

namespace BlockBand.SourceProcess.Stochastic.UniquenessDeg
open Matrix Filter Topology
open BlockBand.SourceProcess.Stochastic.Representation

variable {d : ℕ}

/-- Sum of squared entries of a square array. -/
def sq2 (Γ : Fin d → Fin d → ℝ) : ℝ := ∑ i, ∑ k, Γ i k ^ 2

theorem sq2_nonneg (Γ : Fin d → Fin d → ℝ) : 0 ≤ sq2 Γ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem frob_orth_eq {κ : Type*} [Fintype κ] {X : Fin d → κ → ℝ}
    (hX : ∀ k l, ∑ c, X k c * X l c = if k = l then 1 else 0) : frob X = d := by
  unfold frob
  simp_rw [sq]
  simp [hX]

theorem frob_tikX_sub_pinvX_le (s : Matrix (Fin d) (Fin d) ℝ) {ε : ℝ} (hε : 0 < ε) :
    frob (fun k c => tikX s ε k c + -pinvX s k c) ≤ 4 * d := by
  refine (frob_add_le _ _).trans ?_
  have h1 := frob_orth_eq (tikX_orth s hε)
  have h2 : frob (fun k c => -pinvX s k c) = d := by
    rw [← frob_orth_eq (pinvX_orth s)]; simp [frob]
  rw [h1, h2]; ring_nf; rfl

theorem frob_neg {κ : Type*} [Fintype κ] (A : Fin d → κ → ℝ) :
    frob (fun k c => -A k c) = frob A := by simp [frob]

theorem frob_tikX_sub_le (s : Matrix (Fin d) (Fin d) ℝ) (ε ε' : ℝ) :
    frob (fun k c => tikX s ε k c + -tikX s ε' k c) ≤
      2 * frob (fun k c => tikX s ε k c + -pinvX s k c) +
        2 * frob (fun k c => tikX s ε' k c + -pinvX s k c) := by
  have e : (fun k c => tikX s ε k c + -tikX s ε' k c) = fun k c =>
      (tikX s ε k c + -pinvX s k c) + -(tikX s ε' k c + -pinvX s k c) := by
    funext k c; ring
  rw [e]
  refine (frob_add_le _ _).trans ?_
  rw [frob_neg]

/-- The row integrand of the comparison with the solution. -/
def gY (s Γ : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) (i : Fin d) (c : Fin d ⊕ Fin (d + d)) : ℝ :=
  ∑ k, Γ i k * hval s ε k c - (if c = Sum.inl i then 1 else 0)

theorem quad_gY (s Γ : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) (i : Fin d) :
    ∑ c, ∑ c', gY s Γ ε i c * gY s Γ ε i c' * zDens s c c' =
      ∑ c, (∑ k, (Γ i k - s i k) * tikX s ε k c + ∑ k, s i k * (tikX s ε k c + -pinvX s k c)) ^ 2 := by
  rw [quad_zDens, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun m _ => ?_
    have e1 : ∑ j, gY s Γ ε i (Sum.inl j) * s j m = ∑ k, Γ i k * tikX s ε k (Sum.inl m) - s i m := by
      have := congrFun (contract_hval s ε Γ i) (Sum.inl m)
      simp only [Sum.elim_inl] at this
      rw [this]
      simp [gY, sub_mul, Finset.sum_sub_distrib, ite_mul]
    rw [e1, ← mul_pinvX_inl s i m]
    congr 1
    simp only [sub_mul, mul_add, mul_neg, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_neg_distrib]
    ring
  · refine Finset.sum_congr rfl fun l _ => ?_
    have e2 : gY s Γ ε i (Sum.inr l) = ∑ k, Γ i k * tikX s ε k (Sum.inr l) := by
      simp [gY, tikX, hval]
    rw [e2]
    have h0 := mul_pinvX_inr s i l
    congr 1
    simp only [sub_mul, mul_add, mul_neg, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, h0]
    ring

/-- **The comparison with the solution.** -/
theorem quad_sum_vsY_le (s Γ : Matrix (Fin d) (Fin d) ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∑ i, ∑ c, ∑ c', gY s Γ ε i c * gY s Γ ε i c' * zDens s c c' ≤
      2 * sq2 (fun i k => Γ i k - s i k) +
        2 * (sq2 s * frob (fun k c => tikX s ε k c + -pinvX s k c)) := by
  simp_rw [quad_gY]
  have h := frob_add_le (mulF (fun i k => Γ i k - s i k) (tikX s ε))
    (mulF s (fun k c => tikX s ε k c + -pinvX s k c))
  rw [frob_mulF_orth _ (tikX_orth s hε)] at h
  have h2 := frob_mulF_le s (fun k c => tikX s ε k c + -pinvX s k c)
  calc _ = frob (fun i c => mulF (fun i k => Γ i k - s i k) (tikX s ε) i c +
        mulF s (fun k c => tikX s ε k c + -pinvX s k c) i c) := rfl
    _ ≤ _ := h
    _ ≤ _ := by unfold sq2; gcongr

/-- The row integrand of the comparison of two Euler schemes. -/
def gX (s Γ Γ' : Matrix (Fin d) (Fin d) ℝ) (ε ε' : ℝ) (i : Fin d)
    (c : Fin d ⊕ Fin (d + d)) : ℝ :=
  ∑ k, Γ i k * hval s ε k c - ∑ k, Γ' i k * hval s ε' k c

theorem quad_gX (s Γ Γ' : Matrix (Fin d) (Fin d) ℝ) (ε ε' : ℝ) (i : Fin d) :
    ∑ c, ∑ c', gX s Γ Γ' ε ε' i c * gX s Γ Γ' ε ε' i c' * zDens s c c' =
      ∑ c, (∑ k, (Γ i k - Γ' i k) * tikX s ε k c +
        ∑ k, Γ' i k * (tikX s ε k c + -tikX s ε' k c)) ^ 2 := by
  rw [quad_zDens, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun m _ => ?_
    have h1 := congrFun (contract_hval s ε Γ i) (Sum.inl m)
    have h2 := congrFun (contract_hval s ε' Γ' i) (Sum.inl m)
    simp only [Sum.elim_inl] at h1 h2
    have e1 : ∑ j, gX s Γ Γ' ε ε' i (Sum.inl j) * s j m =
        ∑ k, Γ i k * tikX s ε k (Sum.inl m) - ∑ k, Γ' i k * tikX s ε' k (Sum.inl m) := by
      rw [h1, h2]
      simp only [gX, sub_mul, Finset.sum_sub_distrib]
    rw [e1]
    congr 1
    simp only [sub_mul, mul_add, mul_neg, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_neg_distrib]
    ring
  · refine Finset.sum_congr rfl fun l _ => ?_
    have e2 : gX s Γ Γ' ε ε' i (Sum.inr l) =
        ∑ k, Γ i k * tikX s ε k (Sum.inr l) - ∑ k, Γ' i k * tikX s ε' k (Sum.inr l) := by
      simp [gX, tikX, hval]
    rw [e2]
    congr 1
    simp only [sub_mul, mul_add, mul_neg, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_neg_distrib]
    ring

/-- **The comparison of two Euler schemes.** -/
theorem quad_sum_vsX_le (s Γ Γ' : Matrix (Fin d) (Fin d) ℝ) {ε ε' : ℝ} (hε : 0 < ε) :
    ∑ i, ∑ c, ∑ c', gX s Γ Γ' ε ε' i c * gX s Γ Γ' ε ε' i c' * zDens s c c' ≤
      2 * sq2 (fun i k => Γ i k - Γ' i k) +
        2 * (sq2 Γ' * frob (fun k c => tikX s ε k c + -tikX s ε' k c)) := by
  simp_rw [quad_gX]
  have h := frob_add_le (mulF (fun i k => Γ i k - Γ' i k) (tikX s ε))
    (mulF Γ' (fun k c => tikX s ε k c + -tikX s ε' k c))
  rw [frob_mulF_orth _ (tikX_orth s hε)] at h
  have h2 := frob_mulF_le Γ' (fun k c => tikX s ε k c + -tikX s ε' k c)
  calc _ = frob (fun i c => mulF (fun i k => Γ i k - Γ' i k) (tikX s ε) i c +
        mulF Γ' (fun k c => tikX s ε k c + -tikX s ε' k c) i c) := rfl
    _ ≤ _ := h
    _ ≤ _ := by unfold sq2; gcongr

theorem sum_offval (u : Fin d → ℝ) (l : Fin (d + d)) :
    ∑ k, u k * offval k (Sum.inr l) = Fin.addCases (fun k' => u k') (fun _ => 0) l := by
  revert l
  refine Fin.addCases (fun k' => ?_) (fun x => ?_)
  · simp [offval, Fin.castAdd_inj]
  · rw [Fin.addCases_right]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : x.addNat d ≠ Fin.castAdd d k := fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_addNat, Fin.val_castAdd] at this
      omega
    simp [offval, this]

/-- Outside the stochastic interval. -/
theorem quad_sum_off (Γ Γ' : Matrix (Fin d) (Fin d) ℝ) :
    ∑ i, ∑ c, ∑ c', (∑ k, Γ i k * offval k c - ∑ k, Γ' i k * offval k c) *
      (∑ k, Γ i k * offval k c' - ∑ k, Γ' i k * offval k c') * zDens 0 c c' =
        sq2 (fun i k => Γ i k - Γ' i k) := by
  unfold sq2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [quad_zDens]
  have e : ∀ l, (∑ k, Γ i k * offval k (Sum.inr l) - ∑ k, Γ' i k * offval k (Sum.inr l)) =
      ∑ k, (Γ i k - Γ' i k) * offval k (Sum.inr l) := fun l => by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
  simp only [Matrix.zero_apply, mul_zero, Finset.sum_const_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_add]
  simp_rw [e, sum_offval]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  simp

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
