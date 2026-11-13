module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Summation by parts with a monotone weight

`abel_antitone`: for a finite family of distinct points `λ_i`, a weight `g` that is nonnegative and
nonincreasing on `[m₀, ∞)` with `m₀ ≤ λ_i`, and reals `X_i` all of whose prefix sums
`Σ_{λ_i ≤ u} X_i` are at most `M` in absolute value, `|Σ_i g(λ_i) X_i| ≤ M g(m₀)`. Applied to the
interval sums of `z_i z_i^* - Γ_i`, one summation by parts over the whole side replaces a dyadic
decomposition and gives the bound `N^{1-α+ε} · max_i c_ij`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Finset

theorem abel_antitone_aux {ι : Type*} [DecidableEq ι] (lam : ι → ℝ) (g : ℝ → ℝ) (m₀ : ℝ)
    (hg : ∀ u v, m₀ ≤ u → u ≤ v → g v ≤ g u) (X : ι → ℝ) {M : ℝ} (hM : 0 ≤ M) :
    ∀ R : Finset ι, Set.InjOn lam R → (∀ i ∈ R, m₀ ≤ lam i) →
      (∀ u, |∑ i ∈ R.filter (fun i => lam i ≤ u), X i| ≤ M) →
      ∀ c, (∀ i ∈ R, lam i ≤ c) → m₀ ≤ c →
        |∑ i ∈ R, (g (lam i) - g c) * X i| ≤ M * (g m₀ - g c) := by
  intro R
  induction R using Finset.induction_on_max_value (f := lam) with
  | empty =>
    intro _ _ _ c _ hc
    simp only [sum_empty, abs_zero]
    exact mul_nonneg hM (sub_nonneg.2 (hg _ _ le_rfl hc))
  | insert a s has hmax ih =>
    intro hinj hm₀ hpre c hc hm₀c
    have hlt : ∀ x ∈ s, lam x < lam a := by
      intro x hx
      refine lt_of_le_of_ne (hmax x hx) fun h => ?_
      have := hinj (mem_insert_of_mem hx) (mem_insert_self a s) h
      exact has (this ▸ hx)
    have hinj' : Set.InjOn lam s := hinj.mono (by intro x hx; exact mem_insert_of_mem hx)
    have hm₀' : ∀ i ∈ s, m₀ ≤ lam i := fun i hi => hm₀ i (mem_insert_of_mem hi)
    have hma : m₀ ≤ lam a := hm₀ a (mem_insert_self a s)
    have hpre' : ∀ u, |∑ i ∈ s.filter (fun i => lam i ≤ u), X i| ≤ M := by
      intro u
      rcases lt_or_ge u (lam a) with hu | hu
      · have e : (insert a s).filter (fun i => lam i ≤ u) = s.filter (fun i => lam i ≤ u) := by
          simp only [filter_insert, not_le.2 hu, ↓reduceIte]
        rw [← e]; exact hpre u
      · have e1 : s.filter (fun i => lam i ≤ u) = s :=
          filter_true_of_mem fun i hi => (hlt i hi).le.trans hu
        rw [e1]
        rcases s.eq_empty_or_nonempty with hs | hs
        · rw [hs, sum_empty, abs_zero]; exact hM
        · obtain ⟨b, hb, hbmax⟩ := s.exists_max_image lam hs
          have e2 : (insert a s).filter (fun i => lam i ≤ lam b) = s := by
            ext i
            simp only [mem_filter, mem_insert]
            constructor
            · rintro ⟨rfl | hi, hle⟩
              · exact absurd hle (not_le.2 (hlt b hb))
              · exact hi
            · intro hi; exact ⟨Or.inr hi, hbmax i hi⟩
          rw [← e2]; exact hpre (lam b)
    have hih := ih hinj' hm₀' hpre' (lam a) (fun i hi => (hlt i hi).le) hma
    have hall : (insert a s).filter (fun i => lam i ≤ c) = insert a s :=
      filter_true_of_mem hc
    have hS := hpre c
    rw [hall] at hS
    have e : ∑ i ∈ insert a s, (g (lam i) - g c) * X i =
        ∑ i ∈ s, (g (lam i) - g (lam a)) * X i + (g (lam a) - g c) * ∑ i ∈ insert a s, X i := by
      rw [sum_insert has, sum_insert has, mul_add, Finset.mul_sum]
      have : ∑ i ∈ s, (g (lam i) - g c) * X i =
          ∑ i ∈ s, (g (lam i) - g (lam a)) * X i + ∑ i ∈ s, (g (lam a) - g c) * X i := by
        rw [← sum_add_distrib]; exact sum_congr rfl fun i _ => by ring
      rw [this]; ring
    rw [e]
    have hgac : 0 ≤ g (lam a) - g c := sub_nonneg.2 (hg _ _ hma (hc a (mem_insert_self a s)))
    calc |∑ i ∈ s, (g (lam i) - g (lam a)) * X i + (g (lam a) - g c) * ∑ i ∈ insert a s, X i|
        ≤ |∑ i ∈ s, (g (lam i) - g (lam a)) * X i| +
            |(g (lam a) - g c) * ∑ i ∈ insert a s, X i| := abs_add_le _ _
      _ ≤ M * (g m₀ - g (lam a)) + (g (lam a) - g c) * M := by
          refine add_le_add hih ?_
          rw [abs_mul, abs_of_nonneg hgac]
          exact mul_le_mul_of_nonneg_left hS hgac
      _ = M * (g m₀ - g c) := by ring

/-- **Summation by parts with a nonincreasing nonnegative weight.** -/
theorem abel_antitone {ι : Type*} [DecidableEq ι] (R : Finset ι) (lam : ι → ℝ)
    (hinj : Set.InjOn lam R) (g : ℝ → ℝ) (m₀ : ℝ) (hm₀ : ∀ i ∈ R, m₀ ≤ lam i)
    (hg : ∀ u v, m₀ ≤ u → u ≤ v → g v ≤ g u) (hg0 : ∀ u, m₀ ≤ u → 0 ≤ g u) (X : ι → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hpre : ∀ u, |∑ i ∈ R.filter (fun i => lam i ≤ u), X i| ≤ M) :
    |∑ i ∈ R, g (lam i) * X i| ≤ M * g m₀ := by
  rcases R.eq_empty_or_nonempty with hR | hR
  · rw [hR, sum_empty, abs_zero]; exact mul_nonneg hM (hg0 m₀ le_rfl)
  obtain ⟨b, hb, hbmax⟩ := R.exists_max_image lam hR
  have hmb : m₀ ≤ lam b := hm₀ b hb
  have h := abel_antitone_aux lam g m₀ hg X hM R hinj hm₀ hpre (lam b) hbmax hmb
  have hall : R.filter (fun i => lam i ≤ lam b) = R := filter_true_of_mem hbmax
  have hS := hpre (lam b)
  rw [hall] at hS
  have e : ∑ i ∈ R, g (lam i) * X i =
      ∑ i ∈ R, (g (lam i) - g (lam b)) * X i + g (lam b) * ∑ i ∈ R, X i := by
    rw [Finset.mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun i _ => by ring
  rw [e]
  have hgb := hg0 (lam b) hmb
  calc |∑ i ∈ R, (g (lam i) - g (lam b)) * X i + g (lam b) * ∑ i ∈ R, X i|
      ≤ M * (g m₀ - g (lam b)) + g (lam b) * M := by
        refine (abs_add_le _ _).trans (add_le_add h ?_)
        rw [abs_mul, abs_of_nonneg hgb]
        exact mul_le_mul_of_nonneg_left hS hgb
    _ = M * g m₀ := by ring

end BlockBand.Critical.RelativeVectors
