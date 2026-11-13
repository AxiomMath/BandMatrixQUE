module

public import Mathlib

/-!
# A measurable skipping Gram–Schmidt process

For a sequence `c : ℕ → (Fin N → ℂ)` of coordinate vectors, `gramSchmidt c k` is the explicit
recursion
`u_k := c_k - ∑_{l<k} ⟨w_l, c_k⟩ w_l`, `w_k := ‖u_k‖⁻¹ • u_k`,
with the inner product `⟨x, y⟩ = star x ⬝ᵥ y` (conjugate-linear in the first slot) and the
Euclidean norm. The convention `0⁻¹ = 0` gives `w_k = 0` exactly when `u_k = 0`, so no case split
appears in the definition. Everything here is deterministic and holds for every finite `N` and
every input sequence; there is no measure, norm constant, or limit.

## Main results

* the nonzero outputs are orthonormal and pairwise orthogonal to all other outputs;
* every output lies in any submodule containing all inputs;
* every input `c_k` is a linear combination of the outputs `w_l`, `l ≤ k`;
* if the inputs depend measurably on a parameter, so do the outputs (Borel, entrywise);
* the counting facts used to select the `t`-th nonzero output.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH

open Matrix

namespace Eigenpairs

variable {N : ℕ}

/-- Unnormalized Euclidean `ℓ²` norm of a coordinate vector. -/
def vecNorm (u : Fin N → ℂ) : ℝ :=
  Real.sqrt (∑ x, ‖u x‖ ^ 2)

/-- The explicit skipping Gram–Schmidt recursion (`0⁻¹ = 0` normalizes a zero residual to `0`). -/
def gramSchmidt (c : ℕ → Fin N → ℂ) : ℕ → Fin N → ℂ
  | k =>
    ((vecNorm (c k - ∑ l : Fin k, (star (gramSchmidt c l) ⬝ᵥ c k) • gramSchmidt c l) : ℂ)⁻¹) •
      (c k - ∑ l : Fin k, (star (gramSchmidt c l) ⬝ᵥ c k) • gramSchmidt c l)
termination_by k => k
decreasing_by all_goals exact l.isLt

/-- The Gram–Schmidt residual `u_k`. -/
def gsResidual (c : ℕ → Fin N → ℂ) (k : ℕ) : Fin N → ℂ :=
  c k - ∑ l : Fin k, (star (gramSchmidt c l) ⬝ᵥ c k) • gramSchmidt c l

theorem gramSchmidt_eq (c : ℕ → Fin N → ℂ) (k : ℕ) :
    gramSchmidt c k = ((vecNorm (gsResidual c k) : ℂ)⁻¹) • gsResidual c k := by
  rw [gramSchmidt]
  rfl

theorem star_dotProduct_self_eq (u : Fin N → ℂ) :
    star u ⬝ᵥ u = ((vecNorm u : ℂ)) ^ 2 := by
  have h0 : 0 ≤ ∑ x, ‖u x‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [vecNorm, ← Complex.ofReal_pow, Real.sq_sqrt h0]
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_sum,
    Complex.ofReal_pow]

theorem vecNorm_eq_zero_iff (u : Fin N → ℂ) : vecNorm u = 0 ↔ u = 0 := by
  have h0 : ∀ x ∈ (Finset.univ : Finset (Fin N)), 0 ≤ ‖u x‖ ^ 2 := fun _ _ => sq_nonneg _
  constructor
  · intro h
    rw [vecNorm, Real.sqrt_eq_zero (Finset.sum_nonneg h0), Finset.sum_eq_zero_iff_of_nonneg h0] at h
    funext x
    simpa using h x (Finset.mem_univ x)
  · rintro rfl
    simp [vecNorm]

theorem star_dotProduct_conj (a b : Fin N → ℂ) : star b ⬝ᵥ a = star (star a ⬝ᵥ b) := by
  rw [← star_dotProduct_star, star_star, dotProduct_comm]

/-- `‖u_k‖ • w_k = u_k`. -/
theorem vecNorm_smul_gramSchmidt (c : ℕ → Fin N → ℂ) (k : ℕ) :
    ((vecNorm (gsResidual c k) : ℂ)) • gramSchmidt c k = gsResidual c k := by
  rw [gramSchmidt_eq, smul_smul]
  by_cases h : gsResidual c k = 0
  · rw [h, smul_zero]
  · have hn : ((vecNorm (gsResidual c k) : ℂ)) ≠ 0 := by
      exact_mod_cast (vecNorm_eq_zero_iff _).not.mpr h
    rw [mul_inv_cancel₀ hn, one_smul]

theorem gramSchmidt_eq_zero_iff (c : ℕ → Fin N → ℂ) (k : ℕ) :
    gramSchmidt c k = 0 ↔ gsResidual c k = 0 := by
  constructor
  · intro h
    rw [← vecNorm_smul_gramSchmidt, h, smul_zero]
  · intro h
    rw [gramSchmidt_eq, h, smul_zero]

/-- Each nonzero output has unit norm. -/
theorem star_gramSchmidt_self (c : ℕ → Fin N → ℂ) (k : ℕ) (hk : gramSchmidt c k ≠ 0) :
    star (gramSchmidt c k) ⬝ᵥ gramSchmidt c k = 1 := by
  have hu : gsResidual c k ≠ 0 := (gramSchmidt_eq_zero_iff c k).not.mp hk
  have hn : ((vecNorm (gsResidual c k) : ℂ)) ≠ 0 := by
    exact_mod_cast (vecNorm_eq_zero_iff _).not.mpr hu
  rw [gramSchmidt_eq, star_smul, smul_dotProduct, dotProduct_smul, star_dotProduct_self_eq]
  have hs : star ((vecNorm (gsResidual c k) : ℂ)⁻¹) = ((vecNorm (gsResidual c k) : ℂ)⁻¹) := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [hs, smul_eq_mul, smul_eq_mul]
  field_simp

/-- A zero-or-unit output: `(1 - ⟨w,w⟩) ⟨w, x⟩ = 0`. -/
theorem star_gramSchmidt_dot_sub (c : ℕ → Fin N → ℂ) (l : ℕ) (x : Fin N → ℂ) :
    (star (gramSchmidt c l) ⬝ᵥ x) * (star (gramSchmidt c l) ⬝ᵥ gramSchmidt c l) =
      star (gramSchmidt c l) ⬝ᵥ x := by
  by_cases h : gramSchmidt c l = 0
  · simp [h]
  · rw [star_gramSchmidt_self c l h, mul_one]

/-- Earlier outputs are orthogonal to later ones. -/
theorem star_gramSchmidt_dot_of_lt (c : ℕ → Fin N → ℂ) :
    ∀ k l, l < k → star (gramSchmidt c l) ⬝ᵥ gramSchmidt c k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro l hl
    have hpair : ∀ j : Fin k, j.val ≠ l →
        star (gramSchmidt c l) ⬝ᵥ gramSchmidt c j = 0 := by
      intro j hj
      rcases lt_or_gt_of_ne hj with hjl | hjl
      · rw [star_dotProduct_conj, ih l hl j hjl, star_zero]
      · exact ih j j.isLt l hjl
    have hres : star (gramSchmidt c l) ⬝ᵥ gsResidual c k = 0 := by
      rw [gsResidual, dotProduct_sub, dotProduct_sum]
      simp only [dotProduct_smul, smul_eq_mul]
      rw [Finset.sum_eq_single (⟨l, hl⟩ : Fin k)]
      · rw [star_gramSchmidt_dot_sub, sub_self]
      · intro j _ hj
        rw [hpair j (fun h => hj (Fin.ext h)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [gramSchmidt_eq c k, dotProduct_smul, hres, smul_zero]

/-- Distinct outputs are orthogonal. -/
theorem star_gramSchmidt_dot_of_ne (c : ℕ → Fin N → ℂ) (k l : ℕ) (h : k ≠ l) :
    star (gramSchmidt c k) ⬝ᵥ gramSchmidt c l = 0 := by
  rcases lt_or_gt_of_ne h with hkl | hkl
  · exact star_gramSchmidt_dot_of_lt c l k hkl
  · rw [star_dotProduct_conj, star_gramSchmidt_dot_of_lt c k l hkl, star_zero]

/-- Every output lies in any submodule containing all inputs. -/
theorem gramSchmidt_mem (c : ℕ → Fin N → ℂ) (E : Submodule ℂ (Fin N → ℂ))
    (hc : ∀ k, c k ∈ E) : ∀ k, gramSchmidt c k ∈ E := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [gramSchmidt_eq]
    refine E.smul_mem _ (E.sub_mem (hc k) (E.sum_mem fun l _ => E.smul_mem _ (ih l l.isLt)))

/-- Each input is a combination of the outputs up to its own index. -/
theorem input_eq_sum (c : ℕ → Fin N → ℂ) (k : ℕ) :
    c k = ((vecNorm (gsResidual c k) : ℂ)) • gramSchmidt c k +
      ∑ l : Fin k, (star (gramSchmidt c l) ⬝ᵥ c k) • gramSchmidt c l := by
  rw [vecNorm_smul_gramSchmidt, gsResidual, sub_add_cancel]

/-- Each input lies in any submodule containing all outputs. -/
theorem input_mem (c : ℕ → Fin N → ℂ) (E : Submodule ℂ (Fin N → ℂ)) (k : ℕ)
    (hw : ∀ l ≤ k, gramSchmidt c l ∈ E) : c k ∈ E := by
  rw [input_eq_sum c k]
  exact E.add_mem (E.smul_mem _ (hw k le_rfl))
    (E.sum_mem fun l _ => E.smul_mem _ (hw l l.isLt.le))

/-!
### Measurability
-/

theorem measurable_star_dotProduct {α : Type*} [MeasurableSpace α] {f g : α → Fin N → ℂ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => star (f a) ⬝ᵥ g a) := by
  simp only [dotProduct, Pi.star_apply]
  exact Finset.measurable_sum _ fun x _ =>
    (continuous_star.measurable.comp (measurable_pi_apply x |>.comp hf)).mul
      (measurable_pi_apply x |>.comp hg)

theorem measurable_vecNorm {α : Type*} [MeasurableSpace α] {f : α → Fin N → ℂ}
    (hf : Measurable f) : Measurable (fun a => vecNorm (f a)) := by
  simp only [vecNorm]
  exact (Finset.measurable_sum _ fun x _ => ((measurable_pi_apply x).comp hf).norm.pow_const 2).sqrt

/-- Measurable inputs give measurable outputs. -/
theorem measurable_gramSchmidt {α : Type*} [MeasurableSpace α] (c : α → ℕ → Fin N → ℂ)
    (hc : ∀ k, Measurable (fun a => c a k)) :
    ∀ k, Measurable (fun a => gramSchmidt (c a) k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hr : Measurable (fun a => gsResidual (c a) k) := by
      simp only [gsResidual]
      refine measurable_pi_iff.mpr fun y => ?_
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact ((measurable_pi_apply y).comp (hc k)).sub
        (Finset.measurable_sum _ fun l _ =>
          (measurable_star_dotProduct (ih l l.isLt) (hc k)).mul
            ((measurable_pi_apply y).comp (ih l l.isLt)))
    simp only [gramSchmidt_eq]
    refine measurable_pi_iff.mpr fun y => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (Complex.measurable_ofReal.comp (measurable_vecNorm hr)).inv.mul
      ((measurable_pi_apply y).comp hr)

/-!
### Counting nonzero outputs
-/

open Classical in
/-- The indices `l < k` satisfying `p` (classical decidability). -/
def belowSet (p : ℕ → Prop) (k : ℕ) : Finset ℕ :=
  (Finset.range k).filter p

theorem mem_belowSet (p : ℕ → Prop) (k l : ℕ) : l ∈ belowSet p k ↔ l < k ∧ p l := by
  simp [belowSet]

/-- Number of indices `l < k` satisfying `p`. -/
def countBelow (p : ℕ → Prop) (k : ℕ) : ℕ :=
  (belowSet p k).card

open Classical in
theorem countBelow_eq_sum (p : ℕ → Prop) (k : ℕ) :
    countBelow p k = ∑ l ∈ Finset.range k, if p l then 1 else 0 := by
  rw [countBelow, belowSet, Finset.card_filter]

theorem countBelow_succ (p : ℕ → Prop) (k : ℕ) :
    countBelow p (k + 1) = countBelow p k + (open Classical in if p k then 1 else 0) := by
  classical
  simp only [countBelow, belowSet, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rw [add_zero]

theorem countBelow_mono (p : ℕ → Prop) {k k' : ℕ} (h : k ≤ k') :
    countBelow p k ≤ countBelow p k' := by
  classical
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

theorem countBelow_lt_of_lt (p : ℕ → Prop) {k k' : ℕ} (hp : p k) (h : k < k') :
    countBelow p k < countBelow p k' := by
  have h1 := countBelow_succ p k
  simp only [hp, ite_true] at h1
  have h2 := countBelow_mono p (show k + 1 ≤ k' from h)
  omega

theorem exists_countBelow_eq (p : ℕ → Prop) :
    ∀ n t, t < countBelow p n → ∃ k < n, p k ∧ countBelow p k = t := by
  intro n
  induction n with
  | zero => intro t ht; simp [countBelow, belowSet] at ht
  | succ n ih =>
    intro t ht
    rw [countBelow_succ] at ht
    by_cases htn : t < countBelow p n
    · obtain ⟨k, hk, hpk, hck⟩ := ih t htn
      exact ⟨k, Nat.lt_succ_of_lt hk, hpk, hck⟩
    · by_cases hpn : p n
      · simp only [hpn, ite_true] at ht
        exact ⟨n, Nat.lt_succ_self n, hpn, by omega⟩
      · simp only [hpn, ite_false] at ht
        omega

end Eigenpairs

end BlockBand.Native.CEH
