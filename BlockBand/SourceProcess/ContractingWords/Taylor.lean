module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Complex.Basic

/-!
# Second-order Taylor expansion of a complex polynomial with a cubic remainder

Deterministic algebra for the contracting-words expansion and the product rule of the word
generator: apply the product rule to a trace polynomial, keep first drift terms and pairs of
differential terms.

For a finite set `S` of variables, a polynomial `Φ` and increments `h` vanishing off `S`:
`Φ(x+h) = Φ(x) + d1 + ½d2 + rem`, `d1 = Σ_{v∈S} ∂_vΦ(x)h_v`,
`d2 = Σ_{w∈S}Σ_{v∈S} ∂_v∂_wΦ(x)h_wh_v` (the order of `wordGenerator`). **`taylor_bound`**: there
are `C, N` such that whenever `|x_w|, |h_w| ≤ M` (`M ≥ 1`) for every `w`,
`|Φ(x)| ≤ CM^N`, `|d1| ≤ CM^Nη`, `|d2| ≤ CM^Nη²`, `|rem| ≤ CM^Nη³`, `η = Σ_{w∈S}|h_w|`
(induction on `Φ`: constants, sums, `p·X_n`). Also `eval_congr_vars`, `vars_pderiv_subset`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MvPolynomial

variable {σ : Type*} [DecidableEq σ]

/-- `Σ_{v∈S} ∂_vΦ(x) h_v`. -/
def tay1 (S : Finset σ) (Φ : MvPolynomial σ ℂ) (x h : σ → ℂ) : ℂ :=
  ∑ v ∈ S, eval x (pderiv v Φ) * h v

/-- `Σ_{w∈S}Σ_{v∈S} ∂_v∂_wΦ(x) h_w h_v`. -/
def tay2 (S : Finset σ) (Φ : MvPolynomial σ ℂ) (x h : σ → ℂ) : ℂ :=
  ∑ w ∈ S, ∑ v ∈ S, eval x (pderiv v (pderiv w Φ)) * (h w * h v)

/-- The cubic remainder `Φ(x+h) - Φ(x) - d1 - ½d2`. -/
def tayR (S : Finset σ) (Φ : MvPolynomial σ ℂ) (x h : σ → ℂ) : ℂ :=
  eval (x + h) Φ - eval x Φ - tay1 S Φ x h - (1 / 2 : ℂ) * tay2 S Φ x h

theorem sum_single_mul (S : Finset σ) (n : σ) (c : ℂ) (h : σ → ℂ) (hS : ∀ w ∉ S, h w = 0) :
    ∑ v ∈ S, (if v = n then c else 0) * h v = c * h n := by
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', ite_eq_left_iff]
  intro hn; rw [hS n hn, mul_zero]

theorem eval_pderiv_mulX (x : σ → ℂ) (p : MvPolynomial σ ℂ) (n v : σ) :
    eval x (pderiv v (p * X n)) = eval x (pderiv v p) * x n + if v = n then eval x p else 0 := by
  rw [pderiv_mul, pderiv_X, Pi.single_apply, map_add, map_mul, map_mul, eval_X]
  by_cases h : n = v
  · subst h; simp
  · simp [h, Ne.symm h]

theorem pderiv_pderiv_mulX (p : MvPolynomial σ ℂ) (n w v : σ) :
    pderiv v (pderiv w (p * X n)) = pderiv v (pderiv w p) * X n +
      (if v = n then pderiv w p else 0) + (if w = n then pderiv v p else 0) := by
  rw [pderiv_mul, pderiv_X, Pi.single_apply, map_add, pderiv_mul, pderiv_X, Pi.single_apply]
  by_cases h1 : n = v <;> by_cases h2 : n = w
  · subst h1; subst h2; simp
  · subst h1; simp [Ne.symm h2, h2]
  · subst h2; simp [Ne.symm h1, h1]
  · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem tay1_mulX (S : Finset σ) (p : MvPolynomial σ ℂ) (n : σ) (x h : σ → ℂ)
    (hS : ∀ w ∉ S, h w = 0) :
    tay1 S (p * X n) x h = tay1 S p x h * x n + eval x p * h n := by
  simp only [tay1, eval_pderiv_mulX, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [sum_single_mul S n _ h hS]
  congr 1
  exact Finset.sum_congr rfl fun v _ => by ring

theorem tay2_mulX (S : Finset σ) (p : MvPolynomial σ ℂ) (n : σ) (x h : σ → ℂ)
    (hS : ∀ w ∉ S, h w = 0) :
    tay2 S (p * X n) x h = tay2 S p x h * x n + 2 * (tay1 S p x h * h n) := by
  have e : ∀ w v, eval x (pderiv v (pderiv w (p * X n))) * (h w * h v) =
      eval x (pderiv v (pderiv w p)) * (h w * h v) * x n +
        (if v = n then eval x (pderiv w p) * h w else 0) * h v +
        (if w = n then eval x (pderiv v p) * h v else 0) * h w := by
    intro w v
    rw [pderiv_pderiv_mulX, map_add, map_add, map_mul, eval_X]
    split_ifs <;> (try simp only [map_zero, zero_mul, add_zero]) <;> ring
  simp only [tay2, e, Finset.sum_add_distrib, Finset.sum_mul]
  have h1 : ∑ w ∈ S, ∑ v ∈ S, (if v = n then eval x (pderiv w p) * h w else 0) * h v =
      tay1 S p x h * h n := by
    simp only [tay1, Finset.sum_mul]
    exact Finset.sum_congr rfl fun w _ => sum_single_mul S n _ h hS
  have h2 : ∑ w ∈ S, ∑ v ∈ S, (if w = n then eval x (pderiv v p) * h v else 0) * h w =
      tay1 S p x h * h n := by
    rw [Finset.sum_comm]
    simp only [tay1, Finset.sum_mul]
    exact Finset.sum_congr rfl fun v _ => sum_single_mul S n _ h hS
  rw [h1, h2]; ring

theorem tayR_mulX (S : Finset σ) (p : MvPolynomial σ ℂ) (n : σ) (x h : σ → ℂ)
    (hS : ∀ w ∉ S, h w = 0) :
    tayR S (p * X n) x h = tayR S p x h * (x n + h n) + (1 / 2 : ℂ) * tay2 S p x h * h n := by
  have hp : eval (x + h) p = eval x p + tay1 S p x h + (1 / 2 : ℂ) * tay2 S p x h +
      tayR S p x h := by simp only [tayR]; ring
  simp only [tayR] at hp ⊢
  rw [tay1_mulX S p n x h hS, tay2_mulX S p n x h hS, map_mul, map_mul, eval_X, eval_X, hp,
    Pi.add_apply]
  ring

/-- The four bounds of the induction. -/
def TayBound (S : Finset σ) (Φ : MvPolynomial σ ℂ) (C : ℝ) (N : ℕ) : Prop :=
  ∀ M : ℝ, 1 ≤ M → ∀ x h : σ → ℂ, (∀ w, ‖x w‖ ≤ M) → (∀ w, ‖h w‖ ≤ M) → (∀ w ∉ S, h w = 0) →
    ‖eval x Φ‖ ≤ C * M ^ N ∧ ‖tay1 S Φ x h‖ ≤ C * M ^ N * ∑ w ∈ S, ‖h w‖ ∧
    ‖tay2 S Φ x h‖ ≤ C * M ^ N * (∑ w ∈ S, ‖h w‖) ^ 2 ∧
    ‖tayR S Φ x h‖ ≤ C * M ^ N * (∑ w ∈ S, ‖h w‖) ^ 3

omit [DecidableEq σ] in
theorem tayBound_C (S : Finset σ) (a : ℂ) : TayBound S (C a) ‖a‖ 0 := by
  intro M _ x h _ _ _
  have h1 : tay1 S (C a) x h = 0 := by simp [tay1]
  have h2 : tay2 S (C a) x h = 0 := by simp [tay2]
  have hR : tayR S (C a) x h = 0 := by simp [tayR, h1, h2]
  have hη : 0 ≤ ∑ w ∈ S, ‖h w‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [h1, h2, hR, norm_zero, eval_C, pow_zero, mul_one]
  exact ⟨le_rfl, by positivity, by positivity, by positivity⟩

omit [DecidableEq σ] in
theorem tayBound_mono {S : Finset σ} {Φ : MvPolynomial σ ℂ} {C C' : ℝ} {N N' : ℕ}
    (h : TayBound S Φ C N) (hC0 : 0 ≤ C) (hC : C ≤ C') (hN : N ≤ N') : TayBound S Φ C' N' := by
  intro M hM x k hx hk hS
  have hMN : M ^ N ≤ M ^ N' := pow_le_pow_right₀ hM hN
  have hK : C * M ^ N ≤ C' * M ^ N' :=
    mul_le_mul hC hMN (by positivity) (hC0.trans hC)
  have hη : 0 ≤ ∑ w ∈ S, ‖k w‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨h1, h2, h3, h4⟩ := h M hM x k hx hk hS
  exact ⟨h1.trans hK, h2.trans (mul_le_mul_of_nonneg_right hK hη),
    h3.trans (mul_le_mul_of_nonneg_right hK (by positivity)),
    h4.trans (mul_le_mul_of_nonneg_right hK (by positivity))⟩

omit [DecidableEq σ] in
theorem tay_add (S : Finset σ) (p q : MvPolynomial σ ℂ) (x h : σ → ℂ) :
    tay1 S (p + q) x h = tay1 S p x h + tay1 S q x h ∧
      tay2 S (p + q) x h = tay2 S p x h + tay2 S q x h ∧
      tayR S (p + q) x h = tayR S p x h + tayR S q x h := by
  have h1 : tay1 S (p + q) x h = tay1 S p x h + tay1 S q x h := by
    simp only [tay1, map_add, add_mul, Finset.sum_add_distrib]
  have h2 : tay2 S (p + q) x h = tay2 S p x h + tay2 S q x h := by
    simp only [tay2, map_add, add_mul, Finset.sum_add_distrib]
  refine ⟨h1, h2, ?_⟩
  simp only [tayR, h1, h2, map_add]; ring

omit [DecidableEq σ] in
theorem tayBound_add {S : Finset σ} {p q : MvPolynomial σ ℂ} {C₁ C₂ : ℝ} {N₁ N₂ : ℕ}
    (h₁ : TayBound S p C₁ N₁) (h₂ : TayBound S q C₂ N₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    TayBound S (p + q) (C₁ + C₂) (max N₁ N₂) := by
  have g₁ := tayBound_mono h₁ hC₁ le_rfl (le_max_left N₁ N₂)
  have g₂ := tayBound_mono h₂ hC₂ le_rfl (le_max_right N₁ N₂)
  intro M hM x k hx hk hS
  obtain ⟨a1, a2, a3, a4⟩ := g₁ M hM x k hx hk hS
  obtain ⟨b1, b2, b3, b4⟩ := g₂ M hM x k hx hk hS
  obtain ⟨e1, e2, e3⟩ := tay_add S p q x k
  rw [e1, e2, e3, map_add]
  refine ⟨(norm_add_le _ _).trans ?_, (norm_add_le _ _).trans ?_, (norm_add_le _ _).trans ?_,
    (norm_add_le _ _).trans ?_⟩ <;> linarith

theorem norm_le_eta {S : Finset σ} {h : σ → ℂ} (hS : ∀ w ∉ S, h w = 0) (n : σ) :
    ‖h n‖ ≤ ∑ w ∈ S, ‖h w‖ := by
  by_cases hn : n ∈ S
  · exact Finset.single_le_sum (f := fun w => ‖h w‖) (fun _ _ => norm_nonneg _) hn
  · rw [hS n hn, norm_zero]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem tayBound_mulX {S : Finset σ} {p : MvPolynomial σ ℂ} {C : ℝ} {N : ℕ}
    (h : TayBound S p C N) (hC : 0 ≤ C) (n : σ) : TayBound S (p * X n) (3 * C) (N + 1) := by
  intro M hM x k hx hk hS
  obtain ⟨a1, a2, a3, a4⟩ := h M hM x k hx hk hS
  set η := ∑ w ∈ S, ‖k w‖
  have hη : 0 ≤ η := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hkn : ‖k n‖ ≤ η := norm_le_eta hS n
  have hkM := hk n
  have hxn := hx n
  set P := C * M ^ N
  have hP : 0 ≤ P := by positivity
  have hPM : 3 * C * M ^ (N + 1) = 3 * (P * M) := by simp only [P]; rw [pow_succ]; ring
  rw [tay1_mulX S p n x k hS, tay2_mulX S p n x k hS, tayR_mulX S p n x k hS, map_mul, eval_X,
    hPM]
  have n1 := norm_nonneg (eval x p)
  have n2 := norm_nonneg (tay1 S p x k)
  have n3 := norm_nonneg (tay2 S p x k)
  have n4 := norm_nonneg (tayR S p x k)
  have hM0 : (0 : ℝ) ≤ M := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [norm_mul]
    nlinarith [mul_le_mul a1 hxn (norm_nonneg _) hP]
  · refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have q1 := mul_le_mul a2 hxn (norm_nonneg _) (by positivity)
    have q2 := mul_le_mul a1 hkn (norm_nonneg _) hP
    nlinarith [mul_nonneg hP hη, mul_nonneg (mul_nonneg hP hη) hM0]
  · refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
    have q1 := mul_le_mul a3 hxn (norm_nonneg _) (by positivity)
    have q2 := mul_le_mul a2 hkn (norm_nonneg _) (by positivity)
    nlinarith [mul_nonneg hP (sq_nonneg η), mul_nonneg (mul_nonneg hP (sq_nonneg η)) hM0]
  · refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul]
    have hxk : ‖x n + k n‖ ≤ 2 * M := (norm_add_le _ _).trans (by linarith)
    have q1 := mul_le_mul a4 hxk (norm_nonneg _) (by positivity)
    have q2 := mul_le_mul a3 hkn (norm_nonneg _) (by positivity)
    have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h12]
    have e3 : P * η ^ 2 * η = P * η ^ 3 := by ring
    nlinarith [mul_nonneg hP (pow_nonneg hη 3), mul_nonneg (mul_nonneg hP (pow_nonneg hη 3)) hM0]

/-- **Second-order Taylor expansion with cubic remainder** (every complex polynomial). -/
theorem taylor_bound (S : Finset σ) (Φ : MvPolynomial σ ℂ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ TayBound S Φ C N := by
  induction Φ using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, 0, norm_nonneg _, tayBound_C S a⟩
  | add p q hp hq =>
    obtain ⟨C₁, N₁, hC₁, h₁⟩ := hp
    obtain ⟨C₂, N₂, hC₂, h₂⟩ := hq
    exact ⟨C₁ + C₂, max N₁ N₂, by positivity, tayBound_add h₁ h₂ hC₁ hC₂⟩
  | mul_X p n hp =>
    obtain ⟨C, N, hC, h⟩ := hp
    exact ⟨3 * C, N + 1, by positivity, tayBound_mulX h hC n⟩

omit [DecidableEq σ] in
/-- Evaluation depends only on the variables. -/
theorem eval_congr_vars {Φ : MvPolynomial σ ℂ} {x y : σ → ℂ} (h : ∀ w ∈ Φ.vars, x w = y w) :
    eval x Φ = eval y Φ := by
  refine eval₂_congr _ x y fun {i} {c} hi hc => h i ?_
  exact (mem_vars_iff_mem_support i).mpr ⟨c, Finsupp.mem_support_iff.mpr hc, hi⟩

omit [DecidableEq σ] in
theorem vars_pderiv_subset (Φ : MvPolynomial σ ℂ) (v : σ) : (pderiv v Φ).vars ⊆ Φ.vars := by
  intro i hi
  obtain ⟨d, hd, hid⟩ := (mem_vars_iff_mem_support i).mp hi
  rw [mem_support_iff, coeff_pderiv] at hd
  refine (mem_vars_iff_mem_support i).mpr ⟨d + Finsupp.single v 1, ?_, ?_⟩
  · rw [mem_support_iff]; intro h0; exact hd (by rw [h0, zero_mul])
  · rw [Finsupp.mem_support_iff] at hid ⊢
    simp only [Finsupp.coe_add, Pi.add_apply]; omega

end BlockBand.SourceProcess.ContractingWords
