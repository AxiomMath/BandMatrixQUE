module
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.TikhonovAlg
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Quadratic forms of the joint integrator

* `frob A = ∑_{i,c} A_{ic}²`, `mulF Γ X = Γ X` (plain functions);
  `frob_add_le`, `frob_mulF_orth` (`‖ΓX‖ = ‖Γ‖` for orthonormal rows), `frob_mulF_le`.
* `zDens s`: the density `diag(s sᵀ, I_{2d})` of the joint integrator `(M, B')` at a point;
  **`quad_zDens`**: `uᵀ zDens(s) u = ∑_m (∑_i u_i s_{im})² + ∑_l u_l²`.
* `hval s ε`, `offval`: the regularized driver integrand at a point inside / outside the
  stochastic interval; **`contract_hval`**: contracting `hval` with `zDens s` gives `tikX`.
-/

namespace BlockBand.SourceProcess.Stochastic.UniquenessDeg
open Matrix Filter Topology
open BlockBand.SourceProcess.Stochastic.Representation

variable {d : ℕ} {κ : Type*} [Fintype κ]

/-- Sum of squares of a `Fin d × κ` array. -/
def frob (A : Fin d → κ → ℝ) : ℝ := ∑ i, ∑ c, A i c ^ 2

/-- The product `Γ X`. -/
def mulF (Γ : Fin d → Fin d → ℝ) (X : Fin d → κ → ℝ) : Fin d → κ → ℝ :=
  fun i c => ∑ k, Γ i k * X k c

theorem frob_nonneg (A : Fin d → κ → ℝ) : 0 ≤ frob A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem frob_add_le (A B : Fin d → κ → ℝ) :
    frob (fun i c => A i c + B i c) ≤ 2 * frob A + 2 * frob B := by
  unfold frob
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun c _ => by nlinarith [sq_nonneg (A i c - B i c)]

theorem frob_mulF_orth (Γ : Fin d → Fin d → ℝ) {X : Fin d → κ → ℝ}
    (hX : ∀ k l, ∑ c, X k c * X l c = if k = l then 1 else 0) :
    frob (mulF Γ X) = ∑ i, ∑ k, Γ i k ^ 2 := by
  unfold frob mulF
  refine Finset.sum_congr rfl fun i _ => ?_
  calc ∑ c, (∑ k, Γ i k * X k c) ^ 2 = ∑ k, ∑ l, Γ i k * Γ i l * ∑ c, X k c * X l c := by
        simp only [sq, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun c _ => by ring
    _ = ∑ k, Γ i k ^ 2 := by
        simp only [hX, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
          ite_true, sq]

theorem frob_mulF_le (Γ : Fin d → Fin d → ℝ) (X : Fin d → κ → ℝ) :
    frob (mulF Γ X) ≤ (∑ i, ∑ k, Γ i k ^ 2) * frob X := by
  unfold frob mulF
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ c, (∑ k, Γ i k * X k c) ^ 2 ≤ ∑ c, (∑ k, Γ i k ^ 2) * ∑ k, X k c ^ 2 :=
        Finset.sum_le_sum fun c _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ k, Γ i k ^ 2) * ∑ k, ∑ c, X k c ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]

/-- The joint density `diag(s sᵀ, I)` at a point. -/
def zDens (s : Matrix (Fin d) (Fin d) ℝ) : Fin d ⊕ Fin (d + d) → Fin d ⊕ Fin (d + d) → ℝ :=
  fun c c' => Sum.elim (fun i => Sum.elim (fun j => (s * sᵀ) i j) (fun _ => 0))
    (fun l => Sum.elim (fun _ => 0) (fun l' => if l = l' then 1 else 0)) c c'

/-- **The joint quadratic form.** -/
theorem quad_zDens (s : Matrix (Fin d) (Fin d) ℝ) (u : Fin d ⊕ Fin (d + d) → ℝ) :
    ∑ c, ∑ c', u c * u c' * zDens s c c' =
      ∑ m, (∑ i, u (Sum.inl i) * s i m) ^ 2 + ∑ l, u (Sum.inr l) ^ 2 := by
  simp only [Fintype.sum_sum_type, zDens, Sum.elim_inl, Sum.elim_inr, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  congr 1
  · have e1 : ∀ m, (∑ i, u (Sum.inl i) * s i m) ^ 2 =
        ∑ i, ∑ j, u (Sum.inl i) * s i m * (u (Sum.inl j) * s j m) := fun m => by
      rw [sq, Finset.sum_mul_sum]
    have key : ∀ i j, u (Sum.inl i) * u (Sum.inl j) * (s * sᵀ) i j =
        ∑ m, u (Sum.inl i) * s i m * (u (Sum.inl j) * s j m) := fun i j => by
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Matrix.transpose_apply]; ring
    simp only [e1, key]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  · exact Finset.sum_congr rfl fun l _ => by ring

/-- The driver integrand inside the stochastic interval: `[P_ε | √(2ε) P_ε | ε G⁻¹]`. -/
def hval (s : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) (k : Fin d) : Fin d ⊕ Fin (d + d) → ℝ :=
  Sum.elim (fun i => tikhonov s ε k i)
    (fun l => Fin.addCases (fun l₁ => Real.sqrt (2 * ε) * tikhonov s ε k l₁)
      (fun l₂ => ε * (gramReg s ε)⁻¹ k l₂) l)

/-- The driver integrand outside the stochastic interval: `e_k` in the first noise block. -/
def offval (k : Fin d) : Fin d ⊕ Fin (d + d) → ℝ :=
  Sum.elim (fun _ => 0) (fun l => if l = Fin.castAdd d k then 1 else 0)

/-- `hval` contracted with `s` on the first block is `tikX`. -/
theorem contract_hval (s : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) (Γ : Fin d → Fin d → ℝ)
    (i : Fin d) : (fun c => ∑ k, Γ i k * tikX s ε k c) =
      fun c => Sum.elim (fun m => ∑ j, (∑ k, Γ i k * hval s ε k (Sum.inl j)) * s j m)
        (fun l => ∑ k, Γ i k * hval s ε k (Sum.inr l)) c := by
  funext c
  rcases c with m | l
  · simp only [tikX, hval, Sum.elim_inl, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  · rfl

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
