module

public import BlockBand.Palm.MomentFlow.MultiPerm
public import BlockBand.Palm.MomentFlow.MultiFlow

/-!
# The pairwise symmetrization for the matching weight

* `quad_eq` (**pairwise symmetrization**). For `p ≠ q` and `y_p = i ≠ j = y_q`, put
  `G_{pq}(y) = 1[y_q ≠ y_p] c_{y_p y_q} (pW(y^{p→y_q}) - pW(y))`. Then
  `G_{pq}(y) + G_{qp}(y) + G_{pq}(y∘(p q)) + G_{qp}(y∘(p q)) = 2 c_ij (a_j - a_i)(b_j - b_i) R`,
  `a = φ(· - c_p)`, `b = φ(· - c_q)`, `R` the product of the other factors.
* `sum_G_le`: summed over the labellings of `ζ` and over `(p,q)`, the `ζ_j` part of the generator
  is `≤ r² A² K² Σ_y pW(y)/(2N)` (second order; uses `pair_fg_le`).
* These give, in the sibling module `MultiPermPoint`, the drift inequality for `permW`
  (`perm_point_drift_le`, `perm_drift_le`) with rate `κ_r = r κ₁ + r² A²(K²+1)/(2N)`, the same
  rate as for the single-centre weight.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization

variable {N r : ℕ}

/-- The `ζ_j` part of the generator attached to the ordered pair of positions `(p, q)`. -/
def pairG (cr : Fin N → Fin N → ℝ) (φ : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) (p q : Fin r)
    (y : Fin r → Fin N) : ℝ :=
  if y q ≠ y p then cr (y p) (y q) * (pW φ lam c (Function.update y p (y q)) - pW φ lam c y)
  else 0

theorem swap_apply_left' (y : Fin r → Fin N) (p q : Fin r) : (y ∘ Equiv.swap p q) p = y q := by
  simp

theorem swap_apply_right' (y : Fin r → Fin N) (p q : Fin r) : (y ∘ Equiv.swap p q) q = y p := by
  simp

theorem swap_apply_ne' (y : Fin r → Fin N) {p q m : Fin r} (hp : m ≠ p) (hq : m ≠ q) :
    (y ∘ Equiv.swap p q) m = y m := by
  simp [Equiv.swap_apply_of_ne_of_ne hp hq]

/-- **The pairwise symmetrization.** -/
theorem quad_eq {cr : Fin N → Fin N → ℝ} (hcr : ∀ i j, cr i j = cr j i) (φ : ℝ → ℝ)
    (lam : Fin N → ℝ) (c : Fin r → ℝ) {p q : Fin r} (hpq : p ≠ q) (y : Fin r → Fin N)
    (hy : y p ≠ y q) :
    pairG cr φ lam c p q y + pairG cr φ lam c q p y + pairG cr φ lam c p q (y ∘ Equiv.swap p q) +
        pairG cr φ lam c q p (y ∘ Equiv.swap p q) =
      2 * cr (y p) (y q) * ((φ (lam (y q) - c p) - φ (lam (y p) - c p)) *
        (φ (lam (y q) - c q) - φ (lam (y p) - c q))) * pWxx φ lam c y p q := by
  set z := y ∘ Equiv.swap p q with hz
  have hzp : z p = y q := swap_apply_left' y p q
  have hzq : z q = y p := swap_apply_right' y p q
  have hzm : ∀ m, m ≠ p → m ≠ q → z m = y m := fun m h1 h2 => swap_apply_ne' y h1 h2
  have hqp : q ≠ p := Ne.symm hpq
  -- the six tuples, through their values at `p, q`
  have e1 := pW_eq_mul_mul φ lam c y hpq
  have e2 := pW_eq_mul_mul φ lam c (Function.update y p (y q)) hpq
  have e3 := pW_eq_mul_mul φ lam c (Function.update y q (y p)) hpq
  have e4 := pW_eq_mul_mul φ lam c z hpq
  have e5 := pW_eq_mul_mul φ lam c (Function.update z p (z q)) hpq
  have e6 := pW_eq_mul_mul φ lam c (Function.update z q (z p)) hpq
  have r2 : pWxx φ lam c (Function.update y p (y q)) p q = pWxx φ lam c y p q :=
    pWxx_congr φ lam c fun m h1 _ => Function.update_of_ne h1 _ _
  have r3 : pWxx φ lam c (Function.update y q (y p)) p q = pWxx φ lam c y p q :=
    pWxx_congr φ lam c fun m _ h2 => Function.update_of_ne h2 _ _
  have r4 : pWxx φ lam c z p q = pWxx φ lam c y p q := pWxx_congr φ lam c hzm
  have r5 : pWxx φ lam c (Function.update z p (z q)) p q = pWxx φ lam c y p q :=
    pWxx_congr φ lam c fun m h1 h2 => by rw [Function.update_of_ne h1, hzm m h1 h2]
  have r6 : pWxx φ lam c (Function.update z q (z p)) p q = pWxx φ lam c y p q :=
    pWxx_congr φ lam c fun m h1 h2 => by rw [Function.update_of_ne h2, hzm m h1 h2]
  simp only [Function.update_self, Function.update_of_ne hpq, Function.update_of_ne hqp]
    at e2 e3 e5 e6
  rw [r2] at e2; rw [r3] at e3; rw [r4] at e4; rw [r5] at e5; rw [r6] at e6
  simp only [hzp, hzq] at e4 e5 e6
  have hy' : y q ≠ y p := Ne.symm hy
  unfold pairG
  rw [hzp, hzq, ite_eq_left hy', ite_eq_left hy, ite_eq_left hy, ite_eq_left hy', e1, e2, e3,
    e4, e5, e6, hcr (y q) (y p)]
  ring

theorem pairG_self (cr : Fin N → Fin N → ℝ) (φ : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ)
    (p : Fin r) (y : Fin r → Fin N) : pairG cr φ lam c p p y = 0 := by
  simp [pairG]

/-- Precomposition with a transposition permutes the labellings of `ζ`. -/
theorem sum_labs_swap (ζ : Occ N) (p q : Fin r) (g : (Fin r → Fin N) → ℝ) :
    ∑ y ∈ labs r ζ, g (y ∘ Equiv.swap p q) = ∑ y ∈ labs r ζ, g y := by
  refine Finset.sum_nbij' (fun y => y ∘ Equiv.swap p q) (fun y => y ∘ Equiv.swap p q) ?_ ?_ ?_ ?_
    ?_
  · intro y hy; rw [mem_labs] at hy ⊢; rw [occOf_comp_swap, hy]
  · intro y hy; rw [mem_labs] at hy ⊢; rw [occOf_comp_swap, hy]
  · intro y _; funext m; simp
  · intro y _; funext m; simp
  · intro y _; rfl

/-- **The `ζ_j` part is of second order**, summed over labellings and pairs of positions. -/
theorem sum_G_le (lam : Fin N → ℝ) (ℓ : ℕ) (c : Fin r → ℝ) {φ φ1 : ℝ → ℝ}
    (hφ : ∀ z, HasDerivAt φ (φ1 z) z) {A K G : ℝ} (hφ0 : ∀ z, 0 ≤ φ z)
    (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ K * φ x)
    (hshort : ∀ m k l, l ≠ k → labelDist k l < ℓ →
      |lam l - lam k| ≤ G ∨ (φ1 (lam k - c m) = 0 ∧ φ (lam l - c m) = φ (lam k - c m)))
    (ζ : Occ N) :
    ∑ y ∈ labs r ζ, ∑ p, ∑ q, pairG (cfgRate N lam ℓ 0) φ lam c p q y ≤
      (r : ℝ) ^ 2 * (A ^ 2 * K ^ 2) / (2 * N) * ∑ y ∈ labs r ζ, pW φ lam c y := by
  set cr := cfgRate N lam ℓ 0 with hcrdef
  have hcr : ∀ i j, cr i j = cr j i := cfgRate_symm lam ℓ 0
  set S := ∑ p, ∑ q, ∑ y ∈ labs r ζ, pairG cr φ lam c p q y with hS
  have hS' : ∑ y ∈ labs r ζ, ∑ p, ∑ q, pairG cr φ lam c p q y = S := by
    rw [hS, Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_comm
  have h1 : ∑ p, ∑ q, ∑ y ∈ labs r ζ, pairG cr φ lam c q p y = S := by
    rw [hS]; exact Finset.sum_comm
  have h2 : ∑ p, ∑ q, ∑ y ∈ labs r ζ, pairG cr φ lam c p q (y ∘ Equiv.swap p q) = S :=
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      sum_labs_swap ζ p q (pairG cr φ lam c p q)
  have h3 : ∑ p, ∑ q, ∑ y ∈ labs r ζ, pairG cr φ lam c q p (y ∘ Equiv.swap p q) = S := by
    rw [← h1]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      sum_labs_swap ζ p q (pairG cr φ lam c q p)
  have hquad : ∀ p q y, pairG cr φ lam c p q y + pairG cr φ lam c q p y +
      pairG cr φ lam c p q (y ∘ Equiv.swap p q) + pairG cr φ lam c q p (y ∘ Equiv.swap p q) ≤
      2 * (A ^ 2 * K ^ 2) / N * pW φ lam c y := by
    intro p q y
    have hR0 : 0 ≤ 2 * (A ^ 2 * K ^ 2) / N * pW φ lam c y := by
      have := pW_nonneg hφ0 lam c y; positivity
    by_cases hpq : p = q
    · subst hpq; simp only [pairG_self, add_zero]; exact hR0
    by_cases hy : y p = y q
    · have z0 : ∀ (a b : Fin r) (w : Fin r → Fin N), w b = w a → pairG cr φ lam c a b w = 0 :=
        fun a b w h => by simp [pairG, h]
      have ha : (y ∘ Equiv.swap p q) q = (y ∘ Equiv.swap p q) p := by
        rw [swap_apply_left', swap_apply_right']; exact hy
      have hb : (y ∘ Equiv.swap p q) p = (y ∘ Equiv.swap p q) q := ha.symm
      rw [z0 p q y hy.symm, z0 q p y hy, z0 p q _ ha, z0 q p _ hb]
      simp only [add_zero]; exact hR0
    rw [quad_eq hcr φ lam c hpq y hy]
    have hfp : ∀ z, HasDerivAt (fun t => φ (t - c p)) (φ1 (z - c p)) z :=
      fun z => HasDerivAt.comp_sub_const z (c p) (hφ (z - c p))
    have hfq : ∀ z, HasDerivAt (fun t => φ (t - c q)) (φ1 (z - c q)) z :=
      fun z => HasDerivAt.comp_sub_const z (c q) (hφ (z - c q))
    have hpair := pair_fg_le lam ℓ hfp hfq (fun z => hφ0 _) (fun z => hφ0 _) hA0 hK0
      (fun z => hA _) (fun z => hA _)
      (fun x z h => hcomp (x - c p) (z - c p) (by rw [sub_sub_sub_cancel_right]; exact h))
      (fun x z h => hcomp (x - c q) (z - c q) (by rw [sub_sub_sub_cancel_right]; exact h))
      (i := y p) (j := y q) (fun hd hne => by
        rcases hshort p (y p) (y q) (Ne.symm hne) hd with h | h
        · exact Or.inl h
        · exact Or.inr h.2)
    have hxx := pWxx_nonneg hφ0 lam c y p q
    rw [pW_eq_mul_mul φ lam c y hpq]
    calc 2 * cr (y p) (y q) * ((φ (lam (y q) - c p) - φ (lam (y p) - c p)) *
          (φ (lam (y q) - c q) - φ (lam (y p) - c q))) * pWxx φ lam c y p q
        = 2 * (cr (y p) (y q) * ((φ (lam (y q) - c p) - φ (lam (y p) - c p)) *
          (φ (lam (y q) - c q) - φ (lam (y p) - c q)))) * pWxx φ lam c y p q := by ring
      _ ≤ 2 * (A ^ 2 * K ^ 2 * (φ (lam (y p) - c p) * φ (lam (y q) - c q)) / N) *
          pWxx φ lam c y p q := by gcongr
      _ = _ := by ring
  have h4 : 4 * S ≤ ∑ p : Fin r, ∑ q : Fin r, ∑ y ∈ labs r ζ,
      2 * (A ^ 2 * K ^ 2) / N * pW φ lam c y := by
    have : 4 * S = ∑ p, ∑ q, ∑ y ∈ labs r ζ, (pairG cr φ lam c p q y + pairG cr φ lam c q p y +
        pairG cr φ lam c p q (y ∘ Equiv.swap p q) +
        pairG cr φ lam c q p (y ∘ Equiv.swap p q)) := by
      simp only [Finset.sum_add_distrib]
      rw [h1, h2, h3]; ring
    rw [this]
    exact Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ =>
      Finset.sum_le_sum fun y _ => hquad p q y
  rw [hS']
  have hsum : ∑ p : Fin r, ∑ q : Fin r, ∑ y ∈ labs r ζ, 2 * (A ^ 2 * K ^ 2) / N * pW φ lam c y =
      (r : ℝ) ^ 2 * (2 * (A ^ 2 * K ^ 2) / N) * ∑ y ∈ labs r ζ, pW φ lam c y := by
    simp only [← Finset.mul_sum, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsum] at h4
  have : (r : ℝ) ^ 2 * (A ^ 2 * K ^ 2) / (2 * N) * ∑ y ∈ labs r ζ, pW φ lam c y =
      ((r : ℝ) ^ 2 * (2 * (A ^ 2 * K ^ 2) / N) * ∑ y ∈ labs r ζ, pW φ lam c y) / 4 := by ring
  rw [this]; linarith

/-!
### The one-particle bracket for a shifted weight
-/

theorem shift_bracket_le (lam : Fin N → ℝ) (ℓ : ℕ) (cm : ℝ)
    {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z)
    {A B K G c₁ : ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A)
    (hB : ∀ z, |φ2 z| ≤ B * φ z) (hB0 : 0 ≤ B) (hK0 : 0 ≤ K)
    (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ K * φ x) (hc₁ : 0 < c₁) (k : Fin N)
    (hshort : ∀ l, l ≠ k → labelDist k l < ℓ →
      |lam l - lam k| ≤ G ∨ (φ1 (lam k - cm) = 0 ∧ φ (lam l - cm) = φ (lam k - cm)))
    (hlong : ∀ l, l ≠ k → ℓ ≤ labelDist k l → c₁ * labelDist k l / N ≤ |lam k - lam l|) :
    (∑ j ∈ univ.erase k, cfgRate N lam ℓ 0 k j * (φ (lam j - cm) - φ (lam k - cm))) +
        (φ1 (lam k - cm) * dysonDrift N lam k + φ2 (lam k - cm) / (2 * N)) ≤
      (2 * ℓ * B * K / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)) * φ (lam k - cm) := by
  set lam' : Fin N → ℝ := fun l => lam l - cm with hlam'
  have h := label_drift_le lam' ℓ hφ hφ1 hφ0 hA hA0 hB hB0 hK0 hcomp hc₁ k
    (fun l hl hd => by
      rcases hshort l hl hd with h | h
      · left; simpa only [hlam', sub_sub_sub_cancel_right] using h
      · exact Or.inr h)
    (fun l hl hd => by simpa only [hlam', sub_sub_sub_cancel_right] using hlong l hl hd)
  have hpr : ∀ l, pairRate N lam' k l = pairRate N lam k l := fun l => by
    simp only [pairRate, hlam', sub_sub_sub_cancel_right]
  have hdd : dysonDrift N lam' k = dysonDrift N lam k := mf_dysonDrift_sub_const lam cm k
  rw [sum_cfgRate_eq lam ℓ (fun t => φ (t - cm)) k]
  simp only [hpr, hdd] at h
  exact h

end BlockBand.Palm.MomentFlow
