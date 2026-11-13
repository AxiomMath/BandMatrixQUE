module

public import BlockBand.Endpoints.Poisson.PhaseFractionalCore
public import BlockBand.Endpoints.Poisson.UnitaryLogSpectral
public import BlockBand.Endpoints.Response.FractionalTrace

/-!
# Deterministic parts of the real log-determinant comparison

Matrix and scalar facts used in the proof of the unitary log-comparison lemma (Steps 1–4 of
that proof).

* `abs_log_norm_le` (the two-sided logarithm bound): `|log|z|| ≤ p⁻¹(|z-1|^p + |z⁻¹-1|^p)`.
* `diagConj T Q d = T diag(d) Q*`: the interpolating unitaries `V^{(k)} = V₀ Q diag(d_k) Q*`
  (Step 1); `rankOneTwist_eq_diagConj` identifies a rank-one twist along an
  eigenvector `w_j = Q e_j` with a diagonal update.
* `norm_blockTrace_diagConj_sub_le`, `conductance_diagConj_le` (Step 2): with
  `c = d - 1`, the normalized block traces of the port compression change by at most
  `W⁻¹ Σ_i |c_i|`, and the conductance by at most `2 Σ_i |c_i|` (the trace-norm bound
  `‖V^{(k)} - V₀‖₁ ≤ Σ_i |c_i|` used entrywise).
* `fracTrace_diagConj_sub`: `Tr |V₁ - V₀|^p = Σ_j |ζ_j - 1|^p`.
* `abs_log_det_twist_le` (Steps 3–4 for one phase, the one-phase ratio): for a contraction `U`,
  `|log|det(I - tÛV')| - log|det(I - tÛV)|| ≤ 3p⁻¹|ζ-1|^p(|q|^p + |q'|^p)`,
  `V' = V(I + (ζ-1)ww*)`, `q, q'` the quadratic forms of the two endpoints.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints.PhaseFractional

open Matrix
open BlockBand.Internal.Contracts.Critical BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath
open scoped ComplexOrder ComplexConjugate

/-!
## The two-sided logarithm bound
-/

theorem log_one_add_le_rpow {x p : ℝ} (hx : 0 ≤ x) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Real.log (1 + x) ≤ x ^ p / p := by
  have h1 : Real.log ((1 + x) ^ p) ≤ (1 + x) ^ p - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos (by linarith) _)
  rw [Real.log_rpow (by linarith)] at h1
  have h2 := Real.rpow_add_le_add_rpow zero_le_one hx hp0.le hp1
  rw [Real.one_rpow] at h2
  rw [le_div_iff₀ hp0]
  nlinarith

theorem log_norm_le_rpow {z : ℂ} (hz : 1 ≤ ‖z‖) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Real.log ‖z‖ ≤ ‖z - 1‖ ^ p / p := by
  have h1 : ‖z‖ ≤ 1 + ‖z - 1‖ := by
    have := norm_add_le (z - 1) 1
    simp at this; linarith
  calc Real.log ‖z‖ ≤ Real.log (1 + ‖z - 1‖) := Real.log_le_log (by linarith) h1
    _ ≤ _ := log_one_add_le_rpow (norm_nonneg _) hp0 hp1

/-- **Two-sided logarithm bound**: `|log|z|| ≤ p⁻¹(|z-1|^p + |z⁻¹-1|^p)`. -/
theorem abs_log_norm_le {z : ℂ} (hz : z ≠ 0) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    |Real.log ‖z‖| ≤ (‖z - 1‖ ^ p + ‖z⁻¹ - 1‖ ^ p) / p := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h0 : 0 ≤ ‖z - 1‖ ^ p / p := div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hp0.le
  have h0' : 0 ≤ ‖z⁻¹ - 1‖ ^ p / p := div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hp0.le
  rw [add_div]
  rcases le_total 1 ‖z‖ with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    linarith [log_norm_le_rpow h hp0 hp1]
  · have hinv : 1 ≤ ‖z⁻¹‖ := by rw [norm_inv]; exact one_le_inv₀ hn |>.mpr h
    have := log_norm_le_rpow hinv hp0 hp1
    rw [norm_inv, Real.log_inv] at this
    rw [abs_of_nonpos (Real.log_nonpos hn.le h)]
    linarith

/-!
## Products bounded by sums of squares
-/

theorem norm_sum_mul_conj_le {κ : Type*} [Fintype κ] (S : Finset κ) (f g : κ → ℂ) :
    ‖∑ x ∈ S, f x * conj (g x)‖ ≤ (∑ x, ‖f x‖ ^ 2 + ∑ x, ‖g x‖ ^ 2) / 2 := by
  calc ‖∑ x ∈ S, f x * conj (g x)‖ ≤ ∑ x ∈ S, ‖f x‖ * ‖g x‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        congr 1; ext x; rw [norm_mul, Complex.norm_conj]
    _ ≤ ∑ x, ‖f x‖ * ‖g x‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun x _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    _ ≤ ∑ x, (‖f x‖ ^ 2 + ‖g x‖ ^ 2) / 2 :=
        Finset.sum_le_sum fun x _ => by nlinarith [sq_nonneg (‖f x‖ - ‖g x‖)]
    _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]

theorem quadNorm_eq_sum {κ : Type*} [Fintype κ] (x : κ → ℂ) :
    quadNorm x = ∑ i, ‖x i‖ ^ 2 := by
  rw [quadNorm, dotProduct]
  simp only [Pi.star_apply, Complex.re_sum]
  congr 1; ext i
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

/-- Columns of a matrix `T` with `T*T = I` are unit vectors. -/
theorem sum_norm_col_sq {κ : Type*} [Fintype κ] [DecidableEq κ] {T : Matrix κ κ ℂ}
    (hT : Tᴴ * T = 1) (i : κ) : ∑ x, ‖T x i‖ ^ 2 = 1 := by
  have h := congrFun (congrFun hT i) i
  rw [mul_apply, one_apply_eq] at h
  have h2 := congrArg Complex.re h
  simp only [conjTranspose_apply, Complex.re_sum, Complex.one_re] at h2
  rw [← h2]
  congr 1; ext x
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

/-!
## Diagonal conjugations `T diag(d) Q*`
-/

section DiagConj

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `T diag(d) Q*`; with `T = V₀ Q` this is `V₀ Q diag(d) Q*`. -/
def diagConj (T Q : Matrix ι ι ℂ) (d : ι → ℂ) : Matrix ι ι ℂ := T * diagonal d * Qᴴ

theorem diagConj_apply (T Q : Matrix ι ι ℂ) (d : ι → ℂ) (x y : ι) :
    diagConj T Q d x y = ∑ i, T x i * d i * conj (Q y i) := by
  rw [diagConj, mul_apply]
  congr 1; ext i
  rw [mul_diagonal, conjTranspose_apply, Complex.star_def]

theorem diagConj_sub (T Q : Matrix ι ι ℂ) (d d' : ι → ℂ) :
    diagConj T Q d - diagConj T Q d' = diagConj T Q (d - d') := by
  rw [diagConj, diagConj, diagConj, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  rfl

theorem diagConj_mul {T Q : Matrix ι ι ℂ} (hQ : Qᴴ * Q = 1) (d u : ι → ℂ) :
    diagConj T Q d * diagConj Q Q u = diagConj T Q (d * u) := by
  rw [diagConj, diagConj, diagConj]
  rw [show T * diagonal d * Qᴴ * (Q * diagonal u * Qᴴ) =
    T * diagonal d * (Qᴴ * Q) * diagonal u * Qᴴ by simp only [Matrix.mul_assoc], hQ,
    Matrix.mul_one, Matrix.mul_assoc T, diagonal_mul_diagonal]
  rfl

theorem diagConj_unitary {T Q : Matrix ι ι ℂ} (hT : Tᴴ * T = 1) (hQ' : Q * Qᴴ = 1)
    {d : ι → ℂ} (hd : ∀ i, ‖d i‖ = 1) : (diagConj T Q d)ᴴ * diagConj T Q d = 1 := by
  have hdd : diagonal (star d) * diagonal d = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hd i]
    simp
  rw [diagConj]
  calc (T * diagonal d * Qᴴ)ᴴ * (T * diagonal d * Qᴴ)
      = Q * (diagonal (star d) * (Tᴴ * T) * diagonal d) * Qᴴ := by
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
          Matrix.mul_assoc]
    _ = 1 := by rw [hT, Matrix.mul_one, hdd, Matrix.mul_one, hQ']

theorem rankOneTwist_eq_diagConj {Q : Matrix ι ι ℂ} (hQ' : Q * Qᴴ = 1) (j : ι) (ω : ℂ) :
    rankOneTwist (fun x => Q x j) ω = diagConj Q Q (Function.update 1 j ω) := by
  ext x y
  rw [diagConj_apply]
  have hupd : ∀ i, Function.update (1 : ι → ℂ) j ω i = 1 + if i = j then ω - 1 else 0 := by
    intro i
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have h1 : ∑ i, Q x i * conj (Q y i) = (1 : Matrix ι ι ℂ) x y := by
    rw [← hQ', mul_apply]
    simp [conjTranspose_apply]
  simp only [hupd, mul_add, add_mul, mul_one, Finset.sum_add_distrib, h1]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]
  simp [rankOneTwist, vecMulVec_apply]
  ring

theorem toBlocks₁₁_sub {α β : Type*} (A B : Matrix (α ⊕ β) (α ⊕ β) ℂ) :
    (A - B).toBlocks₁₁ = A.toBlocks₁₁ - B.toBlocks₁₁ := by
  ext x y; rfl

end DiagConj

/-!
## Perturbation of the port compression (Step 2)
-/

section Perturbation

variable {W : ℕ} {β : Type*} [Fintype β] [DecidableEq β]

omit [DecidableEq β] in
theorem sum_inl_le_sum {f : (Fin 2 × Fin W) ⊕ β → ℝ} (hf : ∀ x, 0 ≤ f x) (j : Fin 2) :
    ∑ a : Fin W, f (Sum.inl (j, a)) ≤ ∑ x, f x := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  have h1 : ∑ a : Fin W, f (Sum.inl (j, a)) ≤ ∑ j' : Fin 2, ∑ a : Fin W, f (Sum.inl (j', a)) :=
    Finset.single_le_sum (f := fun j' => ∑ a : Fin W, f (Sum.inl (j', a)))
      (fun j' _ => Finset.sum_nonneg fun a _ => hf _) (Finset.mem_univ j)
  have h2 : 0 ≤ ∑ b : β, f (Sum.inr b) := Finset.sum_nonneg fun b _ => hf _
  linarith

omit [DecidableEq β] in
theorem sum_inl_all_le_sum {f : (Fin 2 × Fin W) ⊕ β → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ y : Fin 2 × Fin W, f (Sum.inl y) ≤ ∑ x, f x := by
  rw [Fintype.sum_sum_type]
  have h2 : 0 ≤ ∑ b : β, f (Sum.inr b) := Finset.sum_nonneg fun b _ => hf _
  linarith

/-- Normalized block traces of the port compression (Step 2). -/
theorem norm_blockTrace_diagConj_sub_le {T Q : Matrix ((Fin 2 × Fin W) ⊕ β)
    ((Fin 2 × Fin W) ⊕ β) ℂ} (hT : Tᴴ * T = 1) (hQ : Qᴴ * Q = 1)
    (d : (Fin 2 × Fin W) ⊕ β → ℂ) (j : Fin 2) :
    ‖blockTrace ((diagConj T Q d).toBlocks₁₁ - (diagConj T Q 1).toBlocks₁₁) j‖ ≤
      (W : ℝ)⁻¹ * ∑ i, ‖d i - 1‖ := by
  rw [← toBlocks₁₁_sub, diagConj_sub]
  unfold blockTrace
  simp only [toBlocks₁₁, Matrix.of_apply, diagConj_apply]
  rw [Finset.sum_comm, norm_mul, norm_inv, Complex.norm_natCast]
  gcongr
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hfac : ∑ a : Fin W, T (Sum.inl (j, a)) i * (d - 1) i * conj (Q (Sum.inl (j, a)) i) =
      (d i - 1) * ∑ a : Fin W, T (Sum.inl (j, a)) i * conj (Q (Sum.inl (j, a)) i) := by
    rw [Finset.mul_sum]; congr 1; ext a; rw [Pi.sub_apply, Pi.one_apply]; ring
  rw [hfac, norm_mul]
  have hb := norm_sum_mul_conj_le Finset.univ (fun a : Fin W => T (Sum.inl (j, a)) i)
    (fun a : Fin W => Q (Sum.inl (j, a)) i)
  have h1 := sum_inl_le_sum (f := fun x => ‖T x i‖ ^ 2) (fun x => sq_nonneg _) j
  have h2 := sum_inl_le_sum (f := fun x => ‖Q x i‖ ^ 2) (fun x => sq_nonneg _) j
  rw [sum_norm_col_sq hT i] at h1
  rw [sum_norm_col_sq hQ i] at h2
  have : ‖∑ a : Fin W, T (Sum.inl (j, a)) i * conj (Q (Sum.inl (j, a)) i)‖ ≤ 1 := by
    linarith
  calc ‖d i - 1‖ * ‖∑ a : Fin W, T (Sum.inl (j, a)) i * conj (Q (Sum.inl (j, a)) i)‖
      ≤ ‖d i - 1‖ * 1 := by gcongr
    _ = ‖d i - 1‖ := mul_one _

theorem trace_conjTranspose_mul_re_eq {κ : Type*} [Fintype κ] (r : Matrix κ κ ℂ) :
    (rᴴ * r).trace.re = ∑ x, ∑ y, ‖r y x‖ ^ 2 := by
  rw [trace, Complex.re_sum]
  congr 1; ext x
  rw [diag_apply, mul_apply, Complex.re_sum]
  congr 1; ext y
  rw [conjTranspose_apply, Complex.star_def, ← Complex.normSq_eq_norm_sq, mul_comm,
    Complex.mul_conj]
  simp

theorem sum_comm₃ {κ ι' : Type*} [Fintype κ] [Fintype ι'] (F : κ → κ → ι' → ℂ) :
    ∑ x, ∑ y, ∑ i, F x y i = ∑ i, ∑ y, ∑ x, F x y i := by
  calc ∑ x, ∑ y, ∑ i, F x y i = ∑ y, ∑ x, ∑ i, F x y i := Finset.sum_comm
    _ = ∑ y, ∑ i, ∑ x, F x y i := Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ i, ∑ y, ∑ x, F x y i := Finset.sum_comm

/-- Conductance of the port compression (Step 2): `g ≤ g₀ + 2 Σ_i |c_i|`. -/
theorem conductance_diagConj_le {T Q : Matrix ((Fin 2 × Fin W) ⊕ β) ((Fin 2 × Fin W) ⊕ β) ℂ}
    (hT : Tᴴ * T = 1) (hQ : Qᴴ * Q = 1) (hr₀ : IsContraction (diagConj T Q 1).toBlocks₁₁)
    (d : (Fin 2 × Fin W) ⊕ β → ℂ) :
    conductance (diagConj T Q d).toBlocks₁₁ ≤
      conductance (diagConj T Q 1).toBlocks₁₁ + 2 * ∑ i, ‖d i - 1‖ := by
  set r₀ := (diagConj T Q 1).toBlocks₁₁ with hr₀def
  set Δ := (diagConj T Q (d - 1)).toBlocks₁₁ with hΔ
  have hr : (diagConj T Q d).toBlocks₁₁ = r₀ + Δ := by
    rw [hΔ, ← diagConj_sub, toBlocks₁₁_sub, hr₀def]; abel
  rw [hr, conductance_eq, conductance_eq]
  have hΔe : ∀ y x, Δ y x = ∑ i, T (Sum.inl y) i * (d i - 1) * conj (Q (Sum.inl x) i) := by
    intro y x
    rw [hΔ]
    simp only [toBlocks₁₁, Matrix.of_apply, diagConj_apply, Pi.sub_apply, Pi.one_apply]
  -- the cross term
  set g : (Fin 2 × Fin W) ⊕ β → Fin 2 × Fin W → ℂ := fun i => r₀ *ᵥ (fun x => Q (Sum.inl x) i)
    with hg
  have hcross : ∑ x, ∑ y, r₀ y x * conj (Δ y x) =
      ∑ i, conj (d i - 1) * ∑ y, g i y * conj (T (Sum.inl y) i) := by
    have h1 : ∑ x, ∑ y, r₀ y x * conj (Δ y x) = ∑ x, ∑ y, ∑ i,
        r₀ y x * (conj (T (Sum.inl y) i) * conj (d i - 1) * Q (Sum.inl x) i) := by
      congr 1; ext x; congr 1; ext y
      rw [hΔe, map_sum, Finset.mul_sum]
      congr 1; ext i
      rw [map_mul, map_mul, Complex.conj_conj]
    rw [h1, sum_comm₃]
    congr 1; ext i
    rw [Finset.mul_sum]
    congr 1; ext y
    rw [hg]
    simp only [mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    congr 1; ext x
    ring
  have hbound : ‖∑ x, ∑ y, r₀ y x * conj (Δ y x)‖ ≤ ∑ i, ‖d i - 1‖ := by
    rw [hcross]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_conj]
    have hb := norm_sum_mul_conj_le Finset.univ (g i) (fun y => T (Sum.inl y) i)
    have h1 := sum_inl_all_le_sum (f := fun x => ‖T x i‖ ^ 2) (fun x => sq_nonneg _)
    rw [sum_norm_col_sq hT i] at h1
    have h2 : ∑ y, ‖g i y‖ ^ 2 ≤ 1 := by
      rw [← quadNorm_eq_sum]
      refine (hr₀ _).trans ?_
      rw [quadNorm_eq_sum]
      have := sum_inl_all_le_sum (f := fun x => ‖Q x i‖ ^ 2) (fun x => sq_nonneg _)
      rw [sum_norm_col_sq hQ i] at this
      exact this
    have : ‖∑ y, g i y * conj (T (Sum.inl y) i)‖ ≤ 1 := by linarith
    calc ‖d i - 1‖ * ‖∑ y, g i y * conj (T (Sum.inl y) i)‖ ≤ ‖d i - 1‖ * 1 := by gcongr
      _ = ‖d i - 1‖ := mul_one _
  -- the trace of `r*r`
  have hsq : ∀ x y, ‖r₀ y x‖ ^ 2 + 2 * (r₀ y x * conj (Δ y x)).re ≤ ‖(r₀ + Δ) y x‖ ^ 2 := by
    intro x y
    rw [Matrix.add_apply, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_add]
    linarith [Complex.normSq_nonneg (Δ y x)]
  have htr : (r₀ᴴ * r₀).trace.re + 2 * (∑ x, ∑ y, r₀ y x * conj (Δ y x)).re ≤
      ((r₀ + Δ)ᴴ * (r₀ + Δ)).trace.re := by
    rw [trace_conjTranspose_mul_re_eq, trace_conjTranspose_mul_re_eq, Complex.re_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun y _ => hsq x y
  have hre : -(∑ i, ‖d i - 1‖) ≤ (∑ x, ∑ y, r₀ y x * conj (Δ y x)).re := by
    have := Complex.abs_re_le_norm (∑ x, ∑ y, r₀ y x * conj (Δ y x))
    have := neg_abs_le (∑ x, ∑ y, r₀ y x * conj (Δ y x)).re
    linarith
  linarith

end Perturbation

/-!
## `σ = Σ_j |ζ_j - 1|^p`
-/

section Sigma

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fracTrace_diagonal (p : ℝ) (d : ι → ℂ) :
    fracTrace p (diagonal d) = ∑ i, (max (d i).re 0) ^ p := by
  unfold fracTrace
  rw [charpoly_diagonal, Finset.prod_eq_multiset_prod,
    show (Finset.univ.val.map fun i => Polynomial.X - Polynomial.C (d i)) =
      (Finset.univ.val.map d).map (fun a => Polynomial.X - Polynomial.C a) by
      rw [Multiset.map_map]; rfl,
    Polynomial.roots_multiset_prod_X_sub_C, Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

/-- **`σ` through the phases**: `Tr |T diag(ζ) Q* - T Q*|^p = Σ_j |ζ_j - 1|^p` for `T*T = I`,
`Q` unitary (here `Tr|A|^p = fracTrace (p/2) (A*A)`). -/
theorem fracTrace_diagConj_sub {T Q : Matrix ι ι ℂ} (hT : Tᴴ * T = 1)
    (hQ' : Q * Qᴴ = 1) (ζ : ι → ℂ) (p : ℝ) :
    fracTrace (p / 2) ((diagConj T Q ζ - diagConj T Q 1)ᴴ * (diagConj T Q ζ - diagConj T Q 1)) =
      ∑ i, ‖ζ i - 1‖ ^ p := by
  rw [diagConj_sub, diagConj]
  have h1 : (T * diagonal (ζ - 1) * Qᴴ)ᴴ * (T * diagonal (ζ - 1) * Qᴴ) =
      Q * diagonal (star (ζ - 1) * (ζ - 1)) * star Q := by
    rw [star_eq_conjTranspose]
    calc (T * diagonal (ζ - 1) * Qᴴ)ᴴ * (T * diagonal (ζ - 1) * Qᴴ)
        = Q * (diagonal (star (ζ - 1)) * (Tᴴ * T) * diagonal (ζ - 1)) * Qᴴ := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
            Matrix.mul_assoc]
      _ = _ := by rw [hT, Matrix.mul_one, diagonal_mul_diagonal]; rfl
  have hU : Q ∈ unitaryGroup ι ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose]; exact hQ'
  rw [h1, BlockBand.Endpoints.fracTrace_unitary_conj _ _ hU, fracTrace_diagonal]
  congr 1; ext i
  have : (((star (ζ - 1) * (ζ - 1)) i)).re = ‖ζ i - 1‖ ^ 2 := by
    simp only [Pi.mul_apply, Pi.star_apply, Pi.sub_apply, Pi.one_apply, Complex.star_def]
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  rw [this, max_eq_left (sq_nonneg _), ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1; push_cast; ring

end Sigma

/-!
## One phase step (Steps 3–4, the one-phase ratio and the two-sided logarithm bound)
-/

section OneStep

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem norm_sub_one_rpow_le {q : ℂ} (hq : 1 / 2 < q.re) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ‖q - 1‖ ^ p ≤ 3 * ‖q‖ ^ p := by
  have h1 : 1 / 2 < ‖q‖ := hq.trans_le (Complex.re_le_norm q)
  have h2 : ‖q - 1‖ ≤ 3 * ‖q‖ := by
    have := norm_sub_le q 1
    rw [norm_one] at this; linarith
  calc ‖q - 1‖ ^ p ≤ (3 * ‖q‖) ^ p := Real.rpow_le_rpow (norm_nonneg _) h2 hp0.le
    _ = 3 ^ p * ‖q‖ ^ p := Real.mul_rpow (by norm_num) (norm_nonneg _)
    _ ≤ 3 * ‖q‖ ^ p := by
        gcongr
        calc (3 : ℝ) ^ p ≤ 3 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1
          _ = 3 := Real.rpow_one 3

/-- **One phase step**: for a contraction `U`, unitary `V`, unit `w`, `|ζ| = 1`,
`0 ≤ t < 1`, `V' = V(I + (ζ - 1)ww*)`:
`|log|det(I - tÛV')| - log|det(I - tÛV)|| ≤ 3p⁻¹|ζ - 1|^p (|q|^p + |q'|^p)`,
`q = w*(I - tÛV)⁻¹w`, `q' = w*(I - tÛV')⁻¹w`. -/
theorem abs_log_det_twist_le {U : Matrix α α ℂ} (hU : IsContraction U)
    {V : Matrix (α ⊕ β) (α ⊕ β) ℂ} (hV : Vᴴ * V = 1) {w : α ⊕ β → ℂ} (hw : star w ⬝ᵥ w = 1)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) :
    |Real.log ‖(1 - (t : ℂ) • (collarHat U * (V * rankOneTwist w ζ))).det‖ -
        Real.log ‖(1 - (t : ℂ) • (collarHat U * V)).det‖| ≤
      3 / p * ‖ζ - 1‖ ^ p * (‖fullQuad t U V w‖ ^ p +
        ‖fullQuad t U (V * rankOneTwist w ζ) w‖ ^ p) := by
  have hV' : (V * rankOneTwist w ζ)ᴴ * (V * rankOneTwist w ζ) = 1 := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul,
      rankOneTwist_unitary hw hζ]
  set X := (t : ℂ) • (collarHat (β := β) U * V) with hXdef
  set X' := (t : ℂ) • (collarHat (β := β) U * (V * rankOneTwist w ζ)) with hX'def
  have hXX : X' = X * rankOneTwist w ζ := by
    rw [hX'def, hXdef, smul_mul_assoc, Matrix.mul_assoc]
  have hζc : ‖conj ζ‖ = 1 := by rw [Complex.norm_conj, hζ]
  have hXX' : X = X' * rankOneTwist w (conj ζ) := by
    rw [hXX, Matrix.mul_assoc, rankOneTwist_mul w hw]
    have : ζ * conj ζ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]; simp
    rw [this, rankOneTwist_one, Matrix.mul_one]
  have hc : IsContraction (collarHat (β := β) U * V) :=
    (isContraction_fromBlocks_zero hU).mul (isContraction_of_unitary hV)
  have hc' : IsContraction (collarHat (β := β) U * (V * rankOneTwist w ζ)) :=
    (isContraction_fromBlocks_zero hU).mul (isContraction_of_unitary hV')
  have hX := (hc.smul_strict ht0 ht1).isUnit_det
  have hX' := (hc'.smul_strict ht0 ht1).isUnit_det
  rw [← hXdef] at hX
  rw [← hX'def] at hX'
  set q := fullQuad t U V w with hq
  set q' := fullQuad t U (V * rankOneTwist w ζ) w with hq'
  have hqX : resolventQuad X w = q := rfl
  have hqX' : resolventQuad X' w = q' := rfl
  have hd1 := det_twist_eq hX hw ζ
  rw [← hXX, hqX] at hd1
  have hd2 := det_twist_eq hX' hw (conj ζ)
  rw [← hXX', hqX'] at hd2
  set z := 1 - (ζ - 1) * (q - 1) with hz
  set z' := 1 - (conj ζ - 1) * (q' - 1) with hz'
  have hD := hX.ne_zero
  have hD' := hX'.ne_zero
  have hzz : z * z' = 1 := by
    have : (1 - X).det = (1 - X).det * (z * z') := by
      conv_lhs => rw [hd2, hd1]
      ring
    have := mul_left_cancel₀ hD (this.symm.trans (mul_one _).symm)
    exact this
  have hz0 : z ≠ 0 := left_ne_zero_of_mul_eq_one hzz
  have hzinv : z⁻¹ = z' := (eq_inv_of_mul_eq_one_right hzz).symm
  have hlog : Real.log ‖(1 - X').det‖ - Real.log ‖(1 - X).det‖ = Real.log ‖z‖ := by
    rw [hd1, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hD) (norm_ne_zero_iff.mpr hz0)]
    ring
  rw [hlog]
  refine (abs_log_norm_le hz0 hp0 hp1).trans ?_
  have hq12 := (fullQuad_pointwise hU hV hw ht0 ht1).1
  have hq12' := (fullQuad_pointwise hU hV' hw ht0 ht1).1
  rw [← hq] at hq12
  rw [← hq'] at hq12'
  have e1 : ‖z - 1‖ ^ p = ‖ζ - 1‖ ^ p * ‖q - 1‖ ^ p := by
    rw [hz, show 1 - (ζ - 1) * (q - 1) - 1 = -((ζ - 1) * (q - 1)) by ring, norm_neg, norm_mul,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  have e2 : ‖z⁻¹ - 1‖ ^ p = ‖ζ - 1‖ ^ p * ‖q' - 1‖ ^ p := by
    rw [hzinv, hz', show 1 - (conj ζ - 1) * (q' - 1) - 1 = -((conj ζ - 1) * (q' - 1)) by ring,
      norm_neg, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    congr 2
    rw [show conj ζ - 1 = conj (ζ - 1) by simp, Complex.norm_conj]
  rw [e1, e2]
  have b1 := norm_sub_one_rpow_le hq12 hp0 hp1
  have b2 := norm_sub_one_rpow_le hq12' hp0 hp1
  have hζp : 0 ≤ ‖ζ - 1‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
  rw [div_le_iff₀ hp0]
  have : 3 / p * ‖ζ - 1‖ ^ p * (‖q‖ ^ p + ‖q'‖ ^ p) * p =
      3 * ‖ζ - 1‖ ^ p * (‖q‖ ^ p + ‖q'‖ ^ p) := by field_simp
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left b1 hζp, mul_le_mul_of_nonneg_left b2 hζp]

end OneStep

end BlockBand.Endpoints.PhaseFractional
