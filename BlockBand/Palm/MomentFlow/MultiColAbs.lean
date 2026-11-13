module

public import BlockBand.Palm.MomentFlow.MultiPermPoint

/-!
# Column form: two-sided drift bounds for the matching weight

Deterministic. The column form uses the reciprocal `1/permW` of the matching
weight; its drift needs a **lower** bound on the drift of `permW`, which the absolute-value
versions below provide (same constants as the upper bounds of `label_drift_le`,
`pair_fg_le`, `sum_G_le`, `perm_point_drift_le`).

* `abs_short_term_le`, `label_bracket_abs`: `|one-particle bracket| ≤ κ₁ φ`;
* `pair_fg_abs`, `sum_G_abs`: the `ζ_j` part is `≤ r² A² K² Σ pW/(2N)` in absolute value;
* proved in the sibling module `MultiColAbsPoint` from these: `perm_point_drift_abs`,
  `|𝓢W + Σ_i (D_i ∂_iW + ∂²_iW/(2N))| ≤ κ_r W` for `W = permW`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization

variable {N r : ℕ}

theorem abs_short_term_le {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z)
    (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z) (hN : 0 < N) {x y M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ Set.uIcc x y, |φ2 z| ≤ M) :
    |((N : ℝ) * (x - y) ^ 2)⁻¹ * (φ y - φ x) + φ1 x * ((1 / (N : ℝ)) * (1 / (x - y)))| ≤
      M / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hxy : x = y
  · subst hxy; simp; positivity
  · have hd : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hd2 : 0 < (x - y) ^ 2 := by positivity
    have ht := abs_taylor2_le hφ hφ1 hM
    have heq : ((N : ℝ) * (x - y) ^ 2)⁻¹ * (φ y - φ x) + φ1 x * ((1 / (N : ℝ)) * (1 / (x - y))) =
        (φ y - φ x - φ1 x * (y - x)) / ((N : ℝ) * (x - y) ^ 2) := by
      field_simp; ring
    rw [heq, abs_div, abs_of_pos (mul_pos hNr hd2), div_le_div_iff₀ (mul_pos hNr hd2) hNr]
    have : (y - x) ^ 2 = (x - y) ^ 2 := by ring
    rw [this] at ht
    calc |φ y - φ x - φ1 x * (y - x)| * N ≤ M * (x - y) ^ 2 * N :=
          mul_le_mul_of_nonneg_right ht hNr.le
      _ = M * (N * (x - y) ^ 2) := by ring

/-- **Two-sided one-particle bracket**: `|Σ_short c(φ_l - φ_k) + φ'_k D_k + φ''_k/(2N)| ≤ κ₁ φ_k`. -/
theorem label_bracket_abs (lam : Fin N → ℝ) (ℓ : ℕ)
    {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z)
    {A B K G c₁ : ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A)
    (hB : ∀ z, |φ2 z| ≤ B * φ z) (hB0 : 0 ≤ B) (hK0 : 0 ≤ K)
    (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ K * φ x) (hc₁ : 0 < c₁) (k : Fin N)
    (hshort : ∀ l, l ≠ k → labelDist k l < ℓ →
      |lam l - lam k| ≤ G ∨ (φ1 (lam k) = 0 ∧ φ (lam l) = φ (lam k)))
    (hlong : ∀ l, l ≠ k → ℓ ≤ labelDist k l → c₁ * labelDist k l / N ≤ |lam k - lam l|) :
    |(∑ l, if l ≠ k ∧ labelDist k l < ℓ then
          pairRate N lam k l * (φ (lam l) - φ (lam k)) else 0) +
        (φ1 (lam k) * dysonDrift N lam k + φ2 (lam k) / (2 * N))| ≤
      (2 * ℓ * B * K / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)) * φ (lam k) := by
  classical
  have hN : 0 < N := Fin.pos k
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hφk := hφ0 (lam k)
  rw [dysonDrift_split lam ℓ k, mul_add, Finset.mul_sum, Finset.mul_sum]
  have hS : |(∑ l, if l ≠ k ∧ labelDist k l < ℓ then
        pairRate N lam k l * (φ (lam l) - φ (lam k)) else 0) +
      ∑ l, φ1 (lam k) * (if l ≠ k ∧ labelDist k l < ℓ then
        (1 / (N : ℝ)) * (1 / (lam k - lam l)) else 0)| ≤
      2 * ℓ * B * K / N * φ (lam k) := by
    rw [← Finset.sum_add_distrib]
    have hpt : ∀ l, |((if l ≠ k ∧ labelDist k l < ℓ then
          pairRate N lam k l * (φ (lam l) - φ (lam k)) else 0) +
        φ1 (lam k) * (if l ≠ k ∧ labelDist k l < ℓ then
          (1 / (N : ℝ)) * (1 / (lam k - lam l)) else 0))| ≤
        if l ≠ k ∧ labelDist k l < ℓ then B * K * φ (lam k) / N else 0 := by
      intro l
      by_cases hl : l ≠ k ∧ labelDist k l < ℓ
      · rw [ite_eq_left hl, ite_eq_left hl, ite_eq_left hl]
        rcases hshort l hl.1 hl.2 with hc | hf
        · have := abs_short_term_le (N := N) hφ hφ1 hN (x := lam k) (y := lam l)
            (M := B * K * φ (lam k)) (by positivity) ?_
          · simpa only [pairRate, mul_div_assoc] using this
          intro z hz
          refine (hB z).trans ?_
          have hz' : |z - lam k| ≤ G := by
            refine le_trans ?_ hc
            rw [Set.mem_uIcc] at hz
            rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
            · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
          have := hcomp (lam k) z hz'
          calc B * φ z ≤ B * (K * φ (lam k)) := mul_le_mul_of_nonneg_left this hB0
            _ = B * K * φ (lam k) := by ring
        · rw [show pairRate N lam k l = ((N : ℝ) * (lam k - lam l) ^ 2)⁻¹ from rfl,
            short_term_flat hf.1 hf.2, abs_zero]
          positivity
      · simp [hl]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun l _ => hpt l).trans ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc := card_short_le k ℓ
    have : 0 ≤ B * K * φ (lam k) / N := by positivity
    calc _ ≤ (2 * ℓ) * (B * K * φ (lam k) / N) := mul_le_mul_of_nonneg_right hc this
      _ = _ := by ring
  have hL : |∑ l, φ1 (lam k) * (if l ≠ k ∧ ℓ ≤ labelDist k l then
        (1 / (N : ℝ)) * (1 / (lam k - lam l)) else 0)| ≤
      2 * A * (1 + Real.log N) / c₁ * φ (lam k) := by
    have hpt : ∀ l, |φ1 (lam k) * (if l ≠ k ∧ ℓ ≤ labelDist k l then
          (1 / (N : ℝ)) * (1 / (lam k - lam l)) else 0)| ≤
        if l ≠ k then A * φ (lam k) / c₁ * ((labelDist k l : ℝ))⁻¹ else 0 := by
      intro l
      by_cases hl : l ≠ k ∧ ℓ ≤ labelDist k l
      · rw [ite_eq_left hl, ite_eq_left hl.1]
        have hd := hlong l hl.1 hl.2
        have hdp : (0 : ℝ) < labelDist k l := by exact_mod_cast labelDist_pos hl.1
        have hgap : 0 < |lam k - lam l| := lt_of_lt_of_le (by positivity) hd
        calc |φ1 (lam k) * ((1 / (N : ℝ)) * (1 / (lam k - lam l)))|
            = |φ1 (lam k)| * ((1 / (N : ℝ)) * (1 / |lam k - lam l|)) := by
              rw [abs_mul, abs_mul, abs_div, abs_div, abs_one, abs_of_pos hNr]
          _ ≤ (A * φ (lam k)) * ((1 / (N : ℝ)) * (N / (c₁ * labelDist k l))) := by
              refine mul_le_mul (hA _) ?_ (by positivity) (by positivity)
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              rw [div_le_div_iff₀ hgap (by positivity)]
              rw [div_le_iff₀ hNr] at hd
              linarith
          _ = A * φ (lam k) / c₁ * ((labelDist k l : ℝ))⁻¹ := by field_simp
      · rw [ite_eq_right hl, mul_zero, abs_zero]
        split_ifs
        · positivity
        · exact le_rfl
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun l _ => hpt l).trans ?_)
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    have := sum_inv_labelDist_le k
    calc A * φ (lam k) / c₁ * ∑ l ∈ Finset.univ.filter (fun l : Fin N => l ≠ k),
          ((labelDist k l : ℝ))⁻¹ ≤ A * φ (lam k) / c₁ * (2 * (1 + Real.log N)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have hI : |φ2 (lam k) / (2 * N)| ≤ B / (2 * N) * φ (lam k) := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * N), div_mul_eq_mul_div,
      div_le_div_iff_of_pos_right (by positivity)]
    linarith [hB (lam k)]
  calc _ = |((∑ l, if l ≠ k ∧ labelDist k l < ℓ then
          pairRate N lam k l * (φ (lam l) - φ (lam k)) else 0) +
        ∑ l, φ1 (lam k) * (if l ≠ k ∧ labelDist k l < ℓ then
          (1 / (N : ℝ)) * (1 / (lam k - lam l)) else 0)) +
        (∑ l, φ1 (lam k) * (if l ≠ k ∧ ℓ ≤ labelDist k l then
          (1 / (N : ℝ)) * (1 / (lam k - lam l)) else 0)) + φ2 (lam k) / (2 * N)| := by
        congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * ℓ * B * K / N * φ (lam k) + 2 * A * (1 + Real.log N) / c₁ * φ (lam k) +
        B / (2 * N) * φ (lam k) := add_le_add (add_le_add hS hL) hI
    _ = _ := by ring

/-- **Two-sided pair bound**: `|c_ij (f_j - f_i)(g_j - g_i)| ≤ A² K² f_i g_j / N`. -/
theorem pair_fg_abs (lam : Fin N → ℝ) (ℓ : ℕ) {f f1 g g1 : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt f (f1 z) z) (hg : ∀ z, HasDerivAt g (g1 z) z) {A K G : ℝ}
    (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z) (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hAf : ∀ z, |f1 z| ≤ A * f z) (hAg : ∀ z, |g1 z| ≤ A * g z)
    (hcf : ∀ x z, |z - x| ≤ G → f z ≤ K * f x) (hcg : ∀ x z, |z - x| ≤ G → g z ≤ K * g x)
    {i j : Fin N}
    (hshort : labelDist i j < ℓ → i ≠ j → |lam j - lam i| ≤ G ∨ f (lam j) = f (lam i)) :
    |cfgRate N lam ℓ 0 i j * ((f (lam j) - f (lam i)) * (g (lam j) - g (lam i)))| ≤
      A ^ 2 * K ^ 2 * (f (lam i) * g (lam j)) / N := by
  have hR : 0 ≤ A ^ 2 * K ^ 2 * (f (lam i) * g (lam j)) / N := by
    have := hf0 (lam i); have := hg0 (lam j); positivity
  by_cases hs : i ≠ j ∧ labelDist i j < ℓ
  · rw [cfgRate_zero_apply lam ℓ hs.1 hs.2]
    rcases hshort hs.2 hs.1 with hc | hfl
    · by_cases hij : lam i = lam j
      · have h0 : f (lam j) - f (lam i) = 0 := by rw [hij, sub_self]
        rw [h0, zero_mul, mul_zero, abs_zero]; exact hR
      obtain ⟨z₁, hz1, -, hz⟩ := exists_mvt_between hf (lam i) (lam j)
      obtain ⟨z₂, -, hz2, hz'⟩ := exists_mvt_between hg (lam i) (lam j)
      rw [hz, hz']
      have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have h1 : |f1 z₁| ≤ A * K * f (lam i) := by
        have := hcf (lam i) z₁ (hz1.trans hc)
        calc |f1 z₁| ≤ A * f z₁ := hAf z₁
          _ ≤ A * (K * f (lam i)) := mul_le_mul_of_nonneg_left this hA0
          _ = A * K * f (lam i) := by ring
      have h2 : |g1 z₂| ≤ A * K * g (lam j) := by
        have := hcg (lam j) z₂ (hz2.trans hc)
        calc |g1 z₂| ≤ A * g z₂ := hAg z₂
          _ ≤ A * (K * g (lam j)) := mul_le_mul_of_nonneg_left this hA0
          _ = A * K * g (lam j) := by ring
      have hprod : |f1 z₁ * g1 z₂| ≤ A ^ 2 * K ^ 2 * (f (lam i) * g (lam j)) := by
        have := mul_le_mul h1 h2 (abs_nonneg _) (by have := hf0 (lam i); positivity)
        rw [← abs_mul] at this
        calc |f1 z₁ * g1 z₂| ≤ A * K * f (lam i) * (A * K * g (lam j)) := this
          _ = _ := by ring
      have heq : pairRate N lam i j * (f1 z₁ * (lam j - lam i) * (g1 z₂ * (lam j - lam i))) =
          f1 z₁ * g1 z₂ / N := by
        unfold pairRate
        rcases eq_or_ne (N : ℝ) 0 with hN | hN
        · rw [hN]; simp
        · have hd : (lam i - lam j) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hij)
          have : (lam j - lam i) * (lam j - lam i) = (lam i - lam j) ^ 2 := by ring
          calc ((N : ℝ) * (lam i - lam j) ^ 2)⁻¹ *
                (f1 z₁ * (lam j - lam i) * (g1 z₂ * (lam j - lam i)))
              = ((N : ℝ) * (lam i - lam j) ^ 2)⁻¹ * (f1 z₁ * g1 z₂) *
                  ((lam j - lam i) * (lam j - lam i)) := by ring
            _ = _ := by rw [this]; field_simp
      rw [heq, abs_div, abs_of_nonneg hNr]
      exact div_le_div_of_nonneg_right hprod hNr
    · rw [hfl, sub_self, zero_mul, mul_zero, abs_zero]; exact hR
  · have : cfgRate N lam ℓ 0 i j = 0 := by unfold cfgRate; rw [ite_eq_right hs]
    rw [this, zero_mul, abs_zero]; exact hR

/-- **The `ζ_j` part, two-sided.** -/
theorem sum_G_abs (lam : Fin N → ℝ) (ℓ : ℕ) (c : Fin r → ℝ) {φ φ1 : ℝ → ℝ}
    (hφ : ∀ z, HasDerivAt φ (φ1 z) z) {A K G : ℝ} (hφ0 : ∀ z, 0 ≤ φ z)
    (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ K * φ x)
    (hshort : ∀ m k l, l ≠ k → labelDist k l < ℓ →
      |lam l - lam k| ≤ G ∨ (φ1 (lam k - c m) = 0 ∧ φ (lam l - c m) = φ (lam k - c m)))
    (ζ : Occ N) :
    |∑ y ∈ labs r ζ, ∑ p, ∑ q, pairG (cfgRate N lam ℓ 0) φ lam c p q y| ≤
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
  have hquad : ∀ p q y, |pairG cr φ lam c p q y + pairG cr φ lam c q p y +
      pairG cr φ lam c p q (y ∘ Equiv.swap p q) + pairG cr φ lam c q p (y ∘ Equiv.swap p q)| ≤
      2 * (A ^ 2 * K ^ 2) / N * pW φ lam c y := by
    intro p q y
    have hR0 : 0 ≤ 2 * (A ^ 2 * K ^ 2) / N * pW φ lam c y := by
      have := pW_nonneg hφ0 lam c y; positivity
    by_cases hpq : p = q
    · subst hpq; simp only [pairG_self, add_zero, abs_zero]; exact hR0
    by_cases hy : y p = y q
    · have z0 : ∀ (a b : Fin r) (w : Fin r → Fin N), w b = w a → pairG cr φ lam c a b w = 0 :=
        fun a b w h => by simp [pairG, h]
      have ha : (y ∘ Equiv.swap p q) q = (y ∘ Equiv.swap p q) p := by
        rw [swap_apply_left', swap_apply_right']; exact hy
      have hb : (y ∘ Equiv.swap p q) p = (y ∘ Equiv.swap p q) q := ha.symm
      rw [z0 p q y hy.symm, z0 q p y hy, z0 p q _ ha, z0 q p _ hb]
      simp only [add_zero, abs_zero]; exact hR0
    rw [quad_eq hcr φ lam c hpq y hy]
    have hfp : ∀ z, HasDerivAt (fun t => φ (t - c p)) (φ1 (z - c p)) z :=
      fun z => HasDerivAt.comp_sub_const z (c p) (hφ (z - c p))
    have hfq : ∀ z, HasDerivAt (fun t => φ (t - c q)) (φ1 (z - c q)) z :=
      fun z => HasDerivAt.comp_sub_const z (c q) (hφ (z - c q))
    have hpair := pair_fg_abs lam ℓ hfp hfq (fun z => hφ0 _) (fun z => hφ0 _) hA0 hK0
      (fun z => hA _) (fun z => hA _)
      (fun x z h => hcomp (x - c p) (z - c p) (by rw [sub_sub_sub_cancel_right]; exact h))
      (fun x z h => hcomp (x - c q) (z - c q) (by rw [sub_sub_sub_cancel_right]; exact h))
      (i := y p) (j := y q) (fun hd hne => by
        rcases hshort p (y p) (y q) (Ne.symm hne) hd with h | h
        · exact Or.inl h
        · exact Or.inr h.2)
    have hxx := pWxx_nonneg hφ0 lam c y p q
    rw [pW_eq_mul_mul φ lam c y hpq]
    calc |2 * cr (y p) (y q) * ((φ (lam (y q) - c p) - φ (lam (y p) - c p)) *
          (φ (lam (y q) - c q) - φ (lam (y p) - c q))) * pWxx φ lam c y p q|
        = 2 * |cr (y p) (y q) * ((φ (lam (y q) - c p) - φ (lam (y p) - c p)) *
          (φ (lam (y q) - c q) - φ (lam (y p) - c q)))| * pWxx φ lam c y p q := by
          rw [show 2 * cr (y p) (y q) * ((φ (lam (y q) - c p) - φ (lam (y p) - c p)) *
            (φ (lam (y q) - c q) - φ (lam (y p) - c q))) * pWxx φ lam c y p q =
            2 * (cr (y p) (y q) * ((φ (lam (y q) - c p) - φ (lam (y p) - c p)) *
            (φ (lam (y q) - c q) - φ (lam (y p) - c q)))) * pWxx φ lam c y p q by ring,
            abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg hxx]
      _ ≤ 2 * (A ^ 2 * K ^ 2 * (φ (lam (y p) - c p) * φ (lam (y q) - c q)) / N) *
          pWxx φ lam c y p q := by gcongr
      _ = _ := by ring
  have h4 : 4 * |S| ≤ ∑ p : Fin r, ∑ q : Fin r, ∑ y ∈ labs r ζ,
      2 * (A ^ 2 * K ^ 2) / N * pW φ lam c y := by
    have : 4 * S = ∑ p, ∑ q, ∑ y ∈ labs r ζ, (pairG cr φ lam c p q y + pairG cr φ lam c q p y +
        pairG cr φ lam c p q (y ∘ Equiv.swap p q) +
        pairG cr φ lam c q p (y ∘ Equiv.swap p q)) := by
      simp only [Finset.sum_add_distrib]
      rw [h1, h2, h3]; ring
    have h4' : |4 * S| ≤ ∑ p : Fin r, ∑ q : Fin r, ∑ y ∈ labs r ζ,
        2 * (A ^ 2 * K ^ 2) / N * pW φ lam c y := by
      rw [this]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => hquad p q y)))
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)] at h4'
    exact h4'
  rw [hS']
  have hsum : ∑ p : Fin r, ∑ q : Fin r, ∑ y ∈ labs r ζ, 2 * (A ^ 2 * K ^ 2) / N * pW φ lam c y =
      (r : ℝ) ^ 2 * (2 * (A ^ 2 * K ^ 2) / N) * ∑ y ∈ labs r ζ, pW φ lam c y := by
    simp only [← Finset.mul_sum, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsum] at h4
  have : (r : ℝ) ^ 2 * (A ^ 2 * K ^ 2) / (2 * N) * ∑ y ∈ labs r ζ, pW φ lam c y =
      ((r : ℝ) ^ 2 * (2 * (A ^ 2 * K ^ 2) / N) * ∑ y ∈ labs r ζ, pW φ lam c y) / 4 := by ring
  rw [this]; linarith

end BlockBand.Palm.MomentFlow
