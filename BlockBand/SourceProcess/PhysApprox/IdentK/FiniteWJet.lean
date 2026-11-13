module

public import BlockBand.SourceProcess.PhysApprox.IdentK.Statements
public import BlockBand.Transmission.LawDecay.Taylor

/-!
# Second-order jets of one discrete step

A step of a quantity is described relative to a vector `β : I → ℂ` of basic increments
(`I` finite). A **jet** `x = (v, l, q)` is a value `v`, a linear form `l` and a quadratic form
`q`; it describes `v'` (the value after the step) when
`‖v' − v − lin l β − quad q β‖ ≤ C ‖β‖₁³` (`IsJet C x v' β`, all components bounded by `C`).

* `IsJet.mul`: products of jets (the discrete product rule), constant `10 C₁ C₂`, for
  `‖β‖₁ ≤ 1`.
* `gen d B x = lin l d + Σ q_{ii'} B_{ii'}`: the generator of a jet, for a drift vector `d` and a
  bracket matrix `B`; `gen_mul`, `gen_chain` (Itô's product and chain rules).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW

open Finset

/-!
## Linear and quadratic forms
-/

section Forms

variable {I : Type*} [Fintype I]

/-- The linear form `Σ_i l_i β_i`. -/
def lin (l β : I → ℂ) : ℂ := ∑ i, l i * β i

/-- The quadratic form `Σ_{i,i'} q_{ii'} β_i β_{i'}`. -/
def quad (q : I → I → ℂ) (β : I → ℂ) : ℂ := ∑ i, ∑ i', q i i' * (β i * β i')

/-- The `ℓ¹` norm `Σ_i ‖β_i‖`. -/
def nrm (β : I → ℂ) : ℝ := ∑ i, ‖β i‖

/-- The bracket `Σ_{i,i'} l_i m_{i'} B_{ii'}`. -/
def br (B : I → I → ℂ) (l m : I → ℂ) : ℂ := ∑ i, ∑ i', l i * m i' * B i i'

theorem nrm_nonneg (β : I → ℂ) : 0 ≤ nrm β := sum_nonneg fun _ _ => norm_nonneg _

theorem norm_le_nrm (β : I → ℂ) (i : I) : ‖β i‖ ≤ nrm β :=
  single_le_sum (f := fun i => ‖β i‖) (fun _ _ => norm_nonneg _) (mem_univ i)

theorem norm_lin_le {l : I → ℂ} {C : ℝ} (hl : ∀ i, ‖l i‖ ≤ C) (β : I → ℂ) :
    ‖lin l β‖ ≤ C * nrm β := by
  unfold lin nrm
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hl i) (norm_nonneg _)

theorem norm_quad_le {q : I → I → ℂ} {C : ℝ} (hq : ∀ i i', ‖q i i'‖ ≤ C) (β : I → ℂ) :
    ‖quad q β‖ ≤ C * nrm β ^ 2 := by
  unfold quad nrm
  rw [sq, sum_mul_sum, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i' _ => ?_)
  rw [norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right (hq i i') (mul_nonneg (norm_nonneg (β i)) (norm_nonneg (β i')))

theorem lin_add (l m β : I → ℂ) : lin (fun i => l i + m i) β = lin l β + lin m β := by
  simp only [lin, add_mul, sum_add_distrib]

theorem lin_smul (c : ℂ) (l β : I → ℂ) : lin (fun i => c * l i) β = c * lin l β := by
  simp only [lin, mul_sum, mul_assoc]

theorem quad_add (q r : I → I → ℂ) (β : I → ℂ) :
    quad (fun i i' => q i i' + r i i') β = quad q β + quad r β := by
  simp only [quad, add_mul, sum_add_distrib]

theorem quad_smul (c : ℂ) (q : I → I → ℂ) (β : I → ℂ) :
    quad (fun i i' => c * q i i') β = c * quad q β := by
  simp only [quad, mul_sum, mul_assoc]

theorem quad_tens (l m β : I → ℂ) : quad (fun i i' => l i * m i') β = lin l β * lin m β := by
  simp only [quad, lin, sum_mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun i' _ => by ring

end Forms

/-!
## Jets
-/

/-- A second-order jet: value, linear form, quadratic form. -/
structure Jet (I : Type*) where
  v : ℂ
  l : I → ℂ
  q : I → I → ℂ

section Jets

variable {I : Type*} [Fintype I]

/-- The product of two jets (discrete product rule). -/
def Jet.mul (x y : Jet I) : Jet I :=
  ⟨x.v * y.v, fun i => x.v * y.l i + y.v * x.l i,
    fun i i' => x.v * y.q i i' + y.v * x.q i i' + x.l i * y.l i'⟩

/-- A constant jet. -/
def Jet.const (c : ℂ) : Jet I := ⟨c, fun _ => 0, fun _ _ => 0⟩

/-- The chain rule jet of `f ∘ x` for a real-valued `x` with value `x0`. -/
def Jet.chain (f f1 f2 : ℝ → ℝ) (x0 : ℝ) (x : Jet I) : Jet I :=
  ⟨(f x0 : ℂ), fun i => (f1 x0 : ℂ) * x.l i,
    fun i i' => (f1 x0 : ℂ) * x.q i i' + ((f2 x0 / 2 : ℝ) : ℂ) * (x.l i * x.l i')⟩

/-- **`x` describes the step `v → v'` of size `β`** with constant `C`. -/
def IsJet (C : ℝ) (x : Jet I) (v' : ℂ) (β : I → ℂ) : Prop :=
  ‖x.v‖ ≤ C ∧ (∀ i, ‖x.l i‖ ≤ C) ∧ (∀ i i', ‖x.q i i'‖ ≤ C) ∧
    ‖v' - x.v - lin x.l β - quad x.q β‖ ≤ C * nrm β ^ 3

theorem IsJet.nonneg {C : ℝ} {x : Jet I} {v' : ℂ} {β : I → ℂ} (h : IsJet C x v' β) : 0 ≤ C :=
  (norm_nonneg _).trans h.1

theorem IsJet.mono {C C' : ℝ} {x : Jet I} {v' : ℂ} {β : I → ℂ} (h : IsJet C x v' β)
    (hC : C ≤ C') : IsJet C' x v' β :=
  ⟨h.1.trans hC, fun i => (h.2.1 i).trans hC, fun i i' => (h.2.2.1 i i').trans hC,
    h.2.2.2.trans (mul_le_mul_of_nonneg_right hC (pow_nonneg (nrm_nonneg β) 3))⟩

theorem isJet_exact {C : ℝ} {x : Jet I} {v' : ℂ} {β : I → ℂ} (hv : ‖x.v‖ ≤ C)
    (hl : ∀ i, ‖x.l i‖ ≤ C) (hq : ∀ i i', ‖x.q i i'‖ ≤ C)
    (he : v' = x.v + lin x.l β + quad x.q β) : IsJet C x v' β := by
  refine ⟨hv, hl, hq, ?_⟩
  rw [he, show x.v + lin x.l β + quad x.q β - x.v - lin x.l β - quad x.q β = 0 by ring,
    norm_zero]
  exact mul_nonneg ((norm_nonneg _).trans hv) (pow_nonneg (nrm_nonneg β) 3)

theorem isJet_const {c : ℂ} {C : ℝ} (hc : ‖c‖ ≤ C) (β : I → ℂ) :
    IsJet C (Jet.const c : Jet I) c β := by
  have hC : 0 ≤ C := (norm_nonneg _).trans hc
  refine isJet_exact hc (fun _ => by simpa [Jet.const] using hC)
    (fun _ _ => by simpa [Jet.const] using hC) ?_
  simp [Jet.const, lin, quad]

/-- An elementary bound: a product of two terms of orders `p` and `q`. -/
theorem norm_mul_le_pow {a b : ℂ} {A B N : ℝ} {p q : ℕ} (ha : ‖a‖ ≤ A * N ^ p)
    (hb : ‖b‖ ≤ B * N ^ q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hN0 : 0 ≤ N) (hN : N ≤ 1)
    (hpq : 3 ≤ p + q) : ‖a * b‖ ≤ A * B * N ^ 3 := by
  rw [norm_mul]
  have h1 : ‖a‖ * ‖b‖ ≤ A * N ^ p * (B * N ^ q) :=
    mul_le_mul ha hb (norm_nonneg _) (mul_nonneg hA (pow_nonneg hN0 _))
  have h2 : N ^ (p + q) ≤ N ^ 3 := pow_le_pow_of_le_one hN0 hN hpq
  calc ‖a‖ * ‖b‖ ≤ A * N ^ p * (B * N ^ q) := h1
    _ = A * B * N ^ (p + q) := by rw [pow_add]; ring
    _ ≤ A * B * N ^ 3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hA hB)

/-- **Product rule for jets.** -/
theorem IsJet.mul {C1 C2 : ℝ} {x y : Jet I} {v' w' : ℂ} {β : I → ℂ} (hx : IsJet C1 x v' β)
    (hy : IsJet C2 y w' β) (hN : nrm β ≤ 1) : IsJet (10 * C1 * C2) (x.mul y) (v' * w') β := by
  obtain ⟨hx0, hxl, hxq, hxr⟩ := hx
  obtain ⟨hy0, hyl, hyq, hyr⟩ := hy
  have hC1 : 0 ≤ C1 := (norm_nonneg _).trans hx0
  have hC2 : 0 ≤ C2 := (norm_nonneg _).trans hy0
  have hP : 0 ≤ C1 * C2 := mul_nonneg hC1 hC2
  have hN0 : 0 ≤ nrm β := nrm_nonneg β
  refine ⟨?_, fun i => ?_, fun i i' => ?_, ?_⟩
  · simp only [Jet.mul, norm_mul]
    have := mul_le_mul hx0 hy0 (norm_nonneg _) hC1
    linarith
  · simp only [Jet.mul]
    have h1 := mul_le_mul hx0 (hyl i) (norm_nonneg _) hC1
    have h2 := mul_le_mul hy0 (hxl i) (norm_nonneg _) hC2
    calc ‖x.v * y.l i + y.v * x.l i‖ ≤ ‖x.v‖ * ‖y.l i‖ + ‖y.v‖ * ‖x.l i‖ := by
          rw [← norm_mul, ← norm_mul]; exact norm_add_le _ _
      _ ≤ 10 * C1 * C2 := by nlinarith
  · simp only [Jet.mul]
    have h1 := mul_le_mul hx0 (hyq i i') (norm_nonneg _) hC1
    have h2 := mul_le_mul hy0 (hxq i i') (norm_nonneg _) hC2
    have h3 := mul_le_mul (hxl i) (hyl i') (norm_nonneg _) hC1
    calc ‖x.v * y.q i i' + y.v * x.q i i' + x.l i * y.l i'‖
        ≤ ‖x.v‖ * ‖y.q i i'‖ + ‖y.v‖ * ‖x.q i i'‖ + ‖x.l i‖ * ‖y.l i'‖ := by
          rw [← norm_mul, ← norm_mul, ← norm_mul]; exact norm_add₃_le
      _ ≤ 10 * C1 * C2 := by nlinarith
  · set N := nrm β with hNdef
    set L1 := lin x.l β
    set Q1 := quad x.q β
    set L2 := lin y.l β
    set Q2 := quad y.q β
    obtain ⟨r1, hr1d⟩ : ∃ r1, v' = x.v + L1 + Q1 + r1 := ⟨v' - x.v - L1 - Q1, by ring⟩
    obtain ⟨r2, hr2d⟩ : ∃ r2, w' = y.v + L2 + Q2 + r2 := ⟨w' - y.v - L2 - Q2, by ring⟩
    have hr1 : ‖r1‖ ≤ C1 * N ^ 3 := by
      have := hxr; rwa [hr1d, show x.v + L1 + Q1 + r1 - x.v - L1 - Q1 = r1 by ring] at this
    have hr2 : ‖r2‖ ≤ C2 * N ^ 3 := by
      have := hyr; rwa [hr2d, show y.v + L2 + Q2 + r2 - y.v - L2 - Q2 = r2 by ring] at this
    have hL1 : ‖L1‖ ≤ C1 * N ^ 1 := by rw [pow_one]; exact norm_lin_le hxl β
    have hL2 : ‖L2‖ ≤ C2 * N ^ 1 := by rw [pow_one]; exact norm_lin_le hyl β
    have hQ1 : ‖Q1‖ ≤ C1 * N ^ 2 := norm_quad_le hxq β
    have hQ2 : ‖Q2‖ ≤ C2 * N ^ 2 := norm_quad_le hyq β
    have hv1 : ‖x.v‖ ≤ C1 * N ^ 0 := by rw [pow_zero, mul_one]; exact hx0
    have hv2 : ‖y.v‖ ≤ C2 * N ^ 0 := by rw [pow_zero, mul_one]; exact hy0
    have hlin : lin (x.mul y).l β = x.v * L2 + y.v * L1 := by
      simp only [Jet.mul]; rw [lin_add, lin_smul, lin_smul]
    have hquad : quad (x.mul y).q β = x.v * Q2 + y.v * Q1 + L1 * L2 := by
      simp only [Jet.mul]; rw [quad_add, quad_add, quad_smul, quad_smul, quad_tens]
    have he : v' * w' - (x.mul y).v - lin (x.mul y).l β - quad (x.mul y).q β =
        x.v * r2 + L1 * Q2 + L1 * r2 + Q1 * L2 + Q1 * Q2 + Q1 * r2 + r1 * y.v + r1 * L2 +
          r1 * Q2 + r1 * r2 := by
      rw [hlin, hquad, hr1d, hr2d]; simp only [Jet.mul]; ring
    rw [he]
    have k := fun {a b : ℂ} {A B : ℝ} {p q : ℕ} (ha : ‖a‖ ≤ A * N ^ p) (hb : ‖b‖ ≤ B * N ^ q)
      (hA : 0 ≤ A) (hB : 0 ≤ B) (hpq : 3 ≤ p + q) =>
      norm_mul_le_pow ha hb hA hB hN0 hN hpq
    calc _ ≤ C1 * C2 * N ^ 3 + C1 * C2 * N ^ 3 + C1 * C2 * N ^ 3 + C1 * C2 * N ^ 3 +
          C1 * C2 * N ^ 3 + C1 * C2 * N ^ 3 + C1 * C2 * N ^ 3 + C1 * C2 * N ^ 3 +
          C1 * C2 * N ^ 3 + C1 * C2 * N ^ 3 := by
          refine norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le
            (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le
            (norm_add_le_of_le ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
          · exact k hv1 hr2 hC1 hC2 (by norm_num)
          · exact k hL1 hQ2 hC1 hC2 (by norm_num)
          · exact k hL1 hr2 hC1 hC2 (by norm_num)
          · exact k hQ1 hL2 hC1 hC2 (by norm_num)
          · exact k hQ1 hQ2 hC1 hC2 (by norm_num)
          · exact k hQ1 hr2 hC1 hC2 (by norm_num)
          · exact k hr1 hv2 hC1 hC2 (by norm_num)
          · exact k hr1 hL2 hC1 hC2 (by norm_num)
          · exact k hr1 hQ2 hC1 hC2 (by norm_num)
          · exact k hr1 hr2 hC1 hC2 (by norm_num)
      _ = 10 * C1 * C2 * N ^ 3 := by ring

/-!
## One-dimensional Taylor expansion of order two
-/

/-- **Second-order Taylor with a third-derivative bound**, two-sided. -/
theorem abs_taylor3_le {f f1 f2 f3 : ℝ → ℝ} {M : ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x) (hf2 : ∀ x, HasDerivAt f2 (f3 x) x)
    (hM : ∀ x, |f3 x| ≤ M) (x h : ℝ) :
    |f (x + h) - f x - f1 x * h - f2 x * h ^ 2 / 2| ≤ M * |h| ^ 3 / 6 := by
  have hin : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => x + θ * h) h θ := fun θ => by
    simpa using ((hasDerivAt_id θ).mul_const h).const_add x
  have up : ∀ g g1 g2 g3 : ℝ → ℝ, (∀ x, HasDerivAt g (g1 x) x) →
      (∀ x, HasDerivAt g1 (g2 x) x) → (∀ x, HasDerivAt g2 (g3 x) x) → (∀ x, |g3 x| ≤ M) →
      g (x + h) ≤ g x + g1 x * h + g2 x * h ^ 2 / 2 + M * |h| ^ 3 / 6 := by
    intro g g1 g2 g3 hg hg1 hg2 hg3
    have := BlockBand.Transmission.LawDecay.taylor2_upper (f := fun θ => g (x + θ * h))
      (f₁ := fun θ => g1 (x + θ * h) * h) (f₂ := fun θ => g2 (x + θ * h) * h ^ 2)
      (f₃ := fun θ => g3 (x + θ * h) * h ^ 3) (M := M * |h| ^ 3)
      (fun θ _ => (hg _).comp θ (hin θ))
      (fun θ _ => (((hg1 _).comp θ (hin θ)).mul_const h).congr_deriv (by ring))
      (fun θ _ => (((hg2 _).comp θ (hin θ)).mul_const (h ^ 2)).congr_deriv (by ring))
      (fun θ _ => by
        have h1 := le_abs_self (g3 (x + θ * h) * h ^ 3)
        rw [abs_mul, abs_pow] at h1
        exact h1.trans (mul_le_mul_of_nonneg_right (hg3 _) (pow_nonneg (abs_nonneg h) 3)))
    simp only [zero_mul, add_zero, one_mul] at this
    linarith
  have h1 := up f f1 f2 f3 hf hf1 hf2 hM
  have h2 := up (fun y => -f y) (fun y => -f1 y) (fun y => -f2 y) (fun y => -f3 y)
    (fun y => (hf y).neg) (fun y => (hf1 y).neg) (fun y => (hf2 y).neg)
    (fun y => by rw [abs_neg]; exact hM y)
  rw [abs_le]
  constructor <;> nlinarith

/-- **Chain rule for jets**: `f ∘ x` for a real `x` with an exact jet. -/
theorem isJet_chain {f f1 f2 f3 : ℝ → ℝ} {M : ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x) (hf2 : ∀ x, HasDerivAt f2 (f3 x) x)
    (hM : ∀ x, |f x| ≤ M ∧ |f1 x| ≤ M ∧ |f2 x| ≤ M ∧ |f3 x| ≤ M) {x : Jet I} {x0 x' : ℝ}
    {β : I → ℂ} {C : ℝ} (hC : 0 ≤ C) (hl : ∀ i, ‖x.l i‖ ≤ C) (hq : ∀ i i', ‖x.q i i'‖ ≤ C)
    (hx : ((x' - x0 : ℝ) : ℂ) = lin x.l β + quad x.q β) (hN : nrm β ≤ 1) :
    IsJet (4 * M * (1 + C) ^ 3) (Jet.chain f f1 f2 x0 x) (f x' : ℂ) β := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0).1
  have hN0 : 0 ≤ nrm β := nrm_nonneg β
  have hC3 : C ≤ (1 + C) ^ 3 := by nlinarith [sq_nonneg C]
  have hC2 : C ^ 2 ≤ (1 + C) ^ 3 := by nlinarith [sq_nonneg C]
  have hC1 : (1 : ℝ) ≤ (1 + C) ^ 3 := one_le_pow₀ (by linarith)
  have hC33 : C ^ 3 ≤ (1 + C) ^ 3 := pow_le_pow_left₀ hC (by linarith) 3
  refine ⟨?_, fun i => ?_, fun i i' => ?_, ?_⟩
  · simp only [Jet.chain, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [(hM x0).1]
  · simp only [Jet.chain, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have := mul_le_mul (hM x0).2.1 (hl i) (norm_nonneg _) hM0
    nlinarith
  · simp only [Jet.chain]
    have h1 := mul_le_mul (hM x0).2.1 (hq i i') (norm_nonneg _) hM0
    have h3 := mul_le_mul (hl i) (hl i') (norm_nonneg _) hC
    have h2 : |f2 x0 / 2| ≤ M / 2 := by rw [abs_div, abs_two]; linarith [(hM x0).2.2.1]
    calc ‖(f1 x0 : ℂ) * x.q i i' + ((f2 x0 / 2 : ℝ) : ℂ) * (x.l i * x.l i')‖
        ≤ |f1 x0| * ‖x.q i i'‖ + |f2 x0 / 2| * (‖x.l i‖ * ‖x.l i'‖) := by
          refine (norm_add_le _ _).trans ?_
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, le_refl]
      _ ≤ M * C + M / 2 * (C * C) :=
          add_le_add h1 (mul_le_mul h2 h3 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (by linarith))
      _ ≤ 4 * M * (1 + C) ^ 3 := by nlinarith
  · set N := nrm β
    set L := lin x.l β
    set Q := quad x.q β
    have hT := abs_taylor3_le hf hf1 hf2 (fun y => (hM y).2.2.2) x0 (x' - x0)
    rw [add_sub_cancel] at hT
    set h := x' - x0
    have hL : ‖L‖ ≤ C * N := norm_lin_le hl β
    have hQ : ‖Q‖ ≤ C * N ^ 2 := norm_quad_le hq β
    have hN2 : N ^ 2 ≤ N := by nlinarith
    have hhn : |h| ≤ 2 * C * N := by
      have e1 : ‖((h : ℝ) : ℂ)‖ ≤ ‖L‖ + ‖Q‖ := by rw [hx]; exact norm_add_le _ _
      rw [Complex.norm_real, Real.norm_eq_abs] at e1
      nlinarith
    have hlin : lin (Jet.chain f f1 f2 x0 x).l β = (f1 x0 : ℂ) * L := by
      simp only [Jet.chain]; rw [lin_smul]
    have hquad : quad (Jet.chain f f1 f2 x0 x).q β =
        (f1 x0 : ℂ) * Q + ((f2 x0 / 2 : ℝ) : ℂ) * (L * L) := by
      simp only [Jet.chain]; rw [quad_add, quad_smul, quad_smul, quad_tens]
    have hLe : L = (h : ℂ) - Q := by rw [hx]; ring
    have he : (f x' : ℂ) - (Jet.chain f f1 f2 x0 x).v - lin (Jet.chain f f1 f2 x0 x).l β -
        quad (Jet.chain f f1 f2 x0 x).q β =
        ((f x' - f x0 - f1 x0 * h - f2 x0 * h ^ 2 / 2 : ℝ) : ℂ) +
          ((f2 x0 / 2 : ℝ) : ℂ) * (2 * L * Q + Q * Q) := by
      rw [hlin, hquad]; simp only [Jet.chain]; rw [hLe]; push_cast; ring
    rw [he]
    have h2 : |f2 x0 / 2| ≤ M / 2 := by rw [abs_div, abs_two]; linarith [(hM x0).2.2.1]
    have hLQ : ‖2 * L * Q + Q * Q‖ ≤ 3 * C ^ 2 * N ^ 3 := by
      have e1 : ‖2 * L * Q‖ ≤ 2 * (C * N) * (C * N ^ 2) := by
        rw [norm_mul, norm_mul, Complex.norm_two]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hL (by norm_num)) hQ (norm_nonneg _)
          (by nlinarith [norm_nonneg L])
      have e2 : ‖Q * Q‖ ≤ (C * N ^ 2) * (C * N ^ 2) := by
        rw [norm_mul]; exact mul_le_mul hQ hQ (norm_nonneg _) ((norm_nonneg _).trans hQ)
      have e3 : N ^ 4 ≤ N ^ 3 := pow_le_pow_of_le_one hN0 hN (by norm_num)
      refine (norm_add_le _ _).trans ?_
      nlinarith [sq_nonneg C, mul_nonneg (sq_nonneg C) (pow_nonneg hN0 3)]
    have hh3 : |h| ^ 3 ≤ (2 * C * N) ^ 3 := pow_le_pow_left₀ (abs_nonneg h) hhn 3
    calc _ ≤ |f x' - f x0 - f1 x0 * h - f2 x0 * h ^ 2 / 2| +
          |f2 x0 / 2| * ‖2 * L * Q + Q * Q‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real,
            Real.norm_eq_abs]
      _ ≤ M * (2 * C * N) ^ 3 / 6 + M / 2 * (3 * C ^ 2 * N ^ 3) := by
          refine add_le_add (hT.trans ?_) (mul_le_mul h2 hLQ (norm_nonneg _) (by linarith))
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh3 hM0) (by norm_num)
      _ ≤ 4 * M * (1 + C) ^ 3 * N ^ 3 := by
          have hN3 : 0 ≤ N ^ 3 := pow_nonneg hN0 3
          have := mul_le_mul_of_nonneg_left hC33 (mul_nonneg hM0 hN3)
          have := mul_le_mul_of_nonneg_left hC2 (mul_nonneg hM0 hN3)
          nlinarith

/-!
## Generators
-/

/-- **The generator of a jet** for the drift vector `d` and the bracket matrix `B`. -/
def gen (d : I → ℂ) (B : I → I → ℂ) (x : Jet I) : ℂ :=
  lin x.l d + ∑ i, ∑ i', x.q i i' * B i i'

theorem gen_mul (d : I → ℂ) (B : I → I → ℂ) (x y : Jet I) :
    gen d B (x.mul y) = x.v * gen d B y + y.v * gen d B x + br B x.l y.l := by
  simp only [gen, Jet.mul, br, lin, add_mul, sum_add_distrib, mul_add, mul_sum, mul_assoc]
  ring

theorem gen_chain (d : I → ℂ) (B : I → I → ℂ) (f f1 f2 : ℝ → ℝ) (x0 : ℝ) (x : Jet I) :
    gen d B (Jet.chain f f1 f2 x0 x) =
      (f1 x0 : ℂ) * gen d B x + ((f2 x0 / 2 : ℝ) : ℂ) * br B x.l x.l := by
  simp only [gen, Jet.chain, br, lin, add_mul, sum_add_distrib, mul_add, mul_sum, mul_assoc]
  ring

theorem gen_const (d : I → ℂ) (B : I → I → ℂ) (c : ℂ) : gen d B (Jet.const c : Jet I) = 0 := by
  simp [gen, Jet.const, lin]

end Jets

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW
