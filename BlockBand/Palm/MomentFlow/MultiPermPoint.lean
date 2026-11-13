module

public import BlockBand.Palm.MomentFlow.MultiPermDrift

/-!
# the drift inequality for the matching weight

`𝓢 W(ζ) + Σ_i (D_i ∂_iW(ζ) + ∂²_iW(ζ)/(2N)) ≤ (r κ₁ + r² A²(K²+1)/(2N)) W(ζ)`

for `W = permW φ λ c`, `∂_iW = ζ! Σ_{y ⊢ ζ} permD1 y i`, `∂²_iW = ζ! Σ_{y ⊢ ζ} permD2 y i`
(`perm_point_drift_le`), and the summed form against `v ≥ 0` on the sector (`perm_drift_le`).
The proof splits `jumpCoeff = ζ_i + ζ_i ζ_j`: the `ζ_i` part is, particle by particle, the
one-particle bracket of `label_drift_le` for the shifted weight `φ(· - c_p)`
(`shift_bracket_le`); the `ζ_iζ_j` part is `sum_G_le` (the pairwise symmetrization `quad_eq`);
the Itô cross terms of two particles on one label are of second order.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization

variable {N r : ℕ}

/-- `Σ_{j ≠ y_p} c ζ_j Δ_j` is the pair sum `Σ_q pairG p q y`. -/
theorem sum_occ_eq_pairG (cr : Fin N → Fin N → ℝ) (φ : ℝ → ℝ) (lam : Fin N → ℝ)
    (c : Fin r → ℝ) (y : Fin r → Fin N) (p : Fin r) :
    ∑ j ∈ univ.erase (y p), cr (y p) j * (occOf y j : ℝ) *
        (pW φ lam c (Function.update y p j) - pW φ lam c y) =
      ∑ q, pairG cr φ lam c p q y := by
  classical
  have hocc : ∀ j, (occOf y j : ℝ) = ∑ q, if y q = j then (1 : ℝ) else 0 := by
    intro j; rw [occOf_eq_sum]; push_cast; rfl
  simp only [hocc, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  rw [Finset.sum_ite_eq]
  unfold pairG
  by_cases hq : y q = y p
  · rw [ite_eq_right (by simp [hq]), ite_eq_right (by simp [hq])]
  · rw [ite_eq_left (by simp [hq]), ite_eq_left hq]

/-- **Drift inequality for the matching weight, pointwise in `ζ`.** -/
theorem perm_point_drift_le (lam : Fin N → ℝ) (ℓ : ℕ) (c : Fin r → ℝ)
    {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z)
    {A B K G c₁ : ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A)
    (hB : ∀ z, |φ2 z| ≤ B * φ z) (hB0 : 0 ≤ B) (hK0 : 0 ≤ K)
    (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ K * φ x) (hc₁ : 0 < c₁)
    (hshort : ∀ m k l, l ≠ k → labelDist k l < ℓ →
      |lam l - lam k| ≤ G ∨ (φ1 (lam k - c m) = 0 ∧ φ (lam l - c m) = φ (lam k - c m)))
    (hlong : ∀ k l, l ≠ k → ℓ ≤ labelDist k l → c₁ * labelDist k l / N ≤ |lam k - lam l|)
    (ζ : Occ N) :
    momentGenerator (cfgRate N lam ℓ 0) (permW φ lam c) ζ +
        ∑ i, (dysonDrift N lam i * (cfgFact ζ * ∑ y ∈ labs r ζ, permD1 φ φ1 lam c y i) +
          cfgFact ζ * ∑ y ∈ labs r ζ, permD2 φ φ1 φ2 lam c y i / (2 * N)) ≤
      (r * (2 * ℓ * B * K / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)) +
          r ^ 2 * (A ^ 2 * (K ^ 2 + 1)) / (2 * N)) * permW φ lam c ζ := by
  classical
  set cr := cfgRate N lam ℓ 0 with hcrdef
  set κ₁ := 2 * ℓ * B * K / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N) with hκ₁
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set br : (Fin r → Fin N) → Fin r → ℝ := fun y p =>
    (∑ j ∈ univ.erase (y p), cr (y p) j * (pW φ lam c (Function.update y p j) - pW φ lam c y)) +
      dysonDrift N lam (y p) * φ1 (lam (y p) - c p) * pWx φ lam c y p +
      φ2 (lam (y p) - c p) * pWx φ lam c y p / (2 * N) with hbr
  set P3 : (Fin r → Fin N) → ℝ := fun y => ∑ p, φ1 (lam (y p) - c p) *
    ∑ q ∈ univ.erase p, (if y q = y p then φ1 (lam (y p) - c q) * pWxx φ lam c y p q
      else 0) with hP3
  set τ : (Fin r → Fin N) → ℝ := fun y =>
    (∑ p, ∑ j ∈ univ.erase (y p), cr (y p) j * (1 + (occOf y j : ℝ)) *
        (pW φ lam c (Function.update y p j) - pW φ lam c y)) +
      ∑ i, (dysonDrift N lam i * permD1 φ φ1 lam c y i + permD2 φ φ1 φ2 lam c y i / (2 * N))
    with hτ
  -- the left side is `ζ! Σ_y τ y`
  have hL : momentGenerator cr (permW φ lam c) ζ +
      ∑ i, (dysonDrift N lam i * (cfgFact ζ * ∑ y ∈ labs r ζ, permD1 φ φ1 lam c y i) +
        cfgFact ζ * ∑ y ∈ labs r ζ, permD2 φ φ1 φ2 lam c y i / (2 * N)) =
      cfgFact ζ * ∑ y ∈ labs r ζ, τ y := by
    rw [momentGenerator_permW]
    have e : ∑ i, (dysonDrift N lam i * (cfgFact ζ * ∑ y ∈ labs r ζ, permD1 φ φ1 lam c y i) +
        cfgFact ζ * ∑ y ∈ labs r ζ, permD2 φ φ1 φ2 lam c y i / (2 * N)) =
        cfgFact ζ * ∑ y ∈ labs r ζ, ∑ i, (dysonDrift N lam i * permD1 φ φ1 lam c y i +
          permD2 φ φ1 φ2 lam c y i / (2 * N)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => by ring
    rw [e, ← mul_add, ← Finset.sum_add_distrib]
  -- decomposition of `τ`
  have hsplit : ∀ y, τ y = ∑ p, br y p + ∑ p, ∑ q, pairG cr φ lam c p q y + P3 y / (2 * N) := by
    intro y
    have hB1 : ∀ p, ∑ j ∈ univ.erase (y p), cr (y p) j * (1 + (occOf y j : ℝ)) *
        (pW φ lam c (Function.update y p j) - pW φ lam c y) =
        (∑ j ∈ univ.erase (y p), cr (y p) j *
          (pW φ lam c (Function.update y p j) - pW φ lam c y)) +
          ∑ q, pairG cr φ lam c p q y := by
      intro p
      rw [← sum_occ_eq_pairG, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [hτ, hbr, hP3]
    rw [Finset.sum_congr rfl fun p _ => hB1 p, Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_dyson_permD1, ← Finset.sum_div, sum_permD2]
    simp only [Finset.sum_add_distrib, add_div, Finset.sum_div]
    ring
  -- bounds
  have hbr_le : ∀ y p, br y p ≤ κ₁ * pW φ lam c y := by
    intro y p
    have hb := shift_bracket_le lam ℓ (c p) hφ hφ1 hφ0 hA hA0 hB hB0 hK0 hcomp hc₁ (y p)
      (hshort p (y p)) (hlong (y p))
    have hx := pWx_nonneg hφ0 lam c y p
    have e1 : ∑ j ∈ univ.erase (y p), cr (y p) j *
        (pW φ lam c (Function.update y p j) - pW φ lam c y) =
        pWx φ lam c y p * ∑ j ∈ univ.erase (y p), cr (y p) j *
          (φ (lam j - c p) - φ (lam (y p) - c p)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pW_update, pW_eq_mul φ lam c y p]; ring
    have e2 : br y p = pWx φ lam c y p * ((∑ j ∈ univ.erase (y p), cr (y p) j *
        (φ (lam j - c p) - φ (lam (y p) - c p))) +
        (φ1 (lam (y p) - c p) * dysonDrift N lam (y p) + φ2 (lam (y p) - c p) / (2 * N))) := by
      simp only [hbr]; rw [e1]; ring
    rw [e2, pW_eq_mul φ lam c y p]
    calc _ ≤ pWx φ lam c y p * (κ₁ * φ (lam (y p) - c p)) := mul_le_mul_of_nonneg_left hb hx
      _ = _ := by ring
  have hP3_le : ∀ y, P3 y ≤ (r : ℝ) ^ 2 * A ^ 2 * pW φ lam c y := by
    intro y
    have hpw := pW_nonneg hφ0 lam c y
    have hterm : ∀ p, φ1 (lam (y p) - c p) * ∑ q ∈ univ.erase p,
        (if y q = y p then φ1 (lam (y p) - c q) * pWxx φ lam c y p q else 0) ≤
        ∑ _q ∈ univ.erase p, A ^ 2 * pW φ lam c y := by
      intro p
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q hq => ?_
      have hqp : q ≠ p := (mem_erase.1 hq).1
      by_cases hyq : y q = y p
      · rw [ite_eq_left hyq, pW_eq_mul_mul φ lam c y (Ne.symm hqp), hyq]
        have hxx := pWxx_nonneg hφ0 lam c y p q
        have h1 := hA (lam (y p) - c p)
        have h2 := hA (lam (y p) - c q)
        have hAp : 0 ≤ A * φ (lam (y p) - c p) := mul_nonneg hA0 (hφ0 _)
        have hab : φ1 (lam (y p) - c p) * φ1 (lam (y p) - c q) ≤
            A * φ (lam (y p) - c p) * (A * φ (lam (y p) - c q)) := by
          calc _ ≤ |φ1 (lam (y p) - c p) * φ1 (lam (y p) - c q)| := le_abs_self _
            _ = |φ1 (lam (y p) - c p)| * |φ1 (lam (y p) - c q)| := abs_mul _ _
            _ ≤ _ := mul_le_mul h1 h2 (abs_nonneg _) hAp
        calc φ1 (lam (y p) - c p) * (φ1 (lam (y p) - c q) * pWxx φ lam c y p q)
            = (φ1 (lam (y p) - c p) * φ1 (lam (y p) - c q)) * pWxx φ lam c y p q := by ring
          _ ≤ (A * φ (lam (y p) - c p) * (A * φ (lam (y p) - c q))) * pWxx φ lam c y p q :=
              mul_le_mul_of_nonneg_right hab hxx
          _ = _ := by ring
      · rw [ite_eq_right hyq, mul_zero]; positivity
    calc P3 y ≤ ∑ p : Fin r, ∑ _q ∈ univ.erase p, A ^ 2 * pW φ lam c y :=
          Finset.sum_le_sum fun p _ => hterm p
      _ ≤ ∑ _p : Fin r, ∑ _q : Fin r, A ^ 2 * pW φ lam c y :=
          Finset.sum_le_sum fun p _ => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) fun _ _ _ => by positivity
      _ = _ := by simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hG := sum_G_le lam ℓ c hφ hφ0 hA hA0 hK0 hcomp hshort ζ
  have hsum : ∑ y ∈ labs r ζ, τ y ≤
      (r * κ₁ + r ^ 2 * (A ^ 2 * (K ^ 2 + 1)) / (2 * N)) * ∑ y ∈ labs r ζ, pW φ lam c y := by
    simp only [hsplit, Finset.sum_add_distrib]
    have h1 : ∑ y ∈ labs r ζ, ∑ p, br y p ≤ ∑ y ∈ labs r ζ, r * κ₁ * pW φ lam c y :=
      Finset.sum_le_sum fun y _ => by
        calc ∑ p, br y p ≤ ∑ _p : Fin r, κ₁ * pW φ lam c y :=
              Finset.sum_le_sum fun p _ => hbr_le y p
          _ = _ := by simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul];
                      ring
    have h3 : ∑ y ∈ labs r ζ, P3 y / (2 * N) ≤
        ∑ y ∈ labs r ζ, (r : ℝ) ^ 2 * A ^ 2 * pW φ lam c y / (2 * N) :=
      Finset.sum_le_sum fun y _ => div_le_div_of_nonneg_right (hP3_le y) (by positivity)
    have e1 : ∑ y ∈ labs r ζ, r * κ₁ * pW φ lam c y = r * κ₁ * ∑ y ∈ labs r ζ, pW φ lam c y := by
      rw [Finset.mul_sum]
    have e3 : ∑ y ∈ labs r ζ, (r : ℝ) ^ 2 * A ^ 2 * pW φ lam c y / (2 * N) =
        (r : ℝ) ^ 2 * A ^ 2 / (2 * N) * ∑ y ∈ labs r ζ, pW φ lam c y := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    rw [e1] at h1; rw [e3] at h3
    have : (r * κ₁ + r ^ 2 * (A ^ 2 * (K ^ 2 + 1)) / (2 * N)) * ∑ y ∈ labs r ζ, pW φ lam c y =
        r * κ₁ * ∑ y ∈ labs r ζ, pW φ lam c y +
        (r : ℝ) ^ 2 * (A ^ 2 * K ^ 2) / (2 * N) * ∑ y ∈ labs r ζ, pW φ lam c y +
        (r : ℝ) ^ 2 * A ^ 2 / (2 * N) * ∑ y ∈ labs r ζ, pW φ lam c y := by ring
    rw [this]
    linarith
  rw [hL]
  calc cfgFact ζ * ∑ y ∈ labs r ζ, τ y ≤ cfgFact ζ *
        ((r * κ₁ + r ^ 2 * (A ^ 2 * (K ^ 2 + 1)) / (2 * N)) * ∑ y ∈ labs r ζ, pW φ lam c y) :=
        mul_le_mul_of_nonneg_left hsum (cfgFact_pos ζ).le
    _ = _ := by unfold permW; ring

/-- **Drift inequality for the matching weight, summed against `v ≥ 0` on the sector.** -/
theorem perm_drift_le (lam : Fin N → ℝ) (ℓ : ℕ) (c : Fin r → ℝ)
    {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z)
    {A B K G c₁ : ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A)
    (hB : ∀ z, |φ2 z| ≤ B * φ z) (hB0 : 0 ≤ B) (hK0 : 0 ≤ K)
    (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ K * φ x) (hc₁ : 0 < c₁)
    (hshort : ∀ m k l, l ≠ k → labelDist k l < ℓ →
      |lam l - lam k| ≤ G ∨ (φ1 (lam k - c m) = 0 ∧ φ (lam l - c m) = φ (lam k - c m)))
    (hlong : ∀ k l, l ≠ k → ℓ ≤ labelDist k l → c₁ * labelDist k l / N ≤ |lam k - lam l|)
    (v : Occ N → ℝ) (hv : ∀ ξ ∈ sector N r, 0 ≤ v ξ) :
    ∑ ξ ∈ sector N r, permW φ lam c ξ * momentGenerator (cfgRate N lam ℓ 0) v ξ +
        ∑ ξ ∈ sector N r, v ξ *
          ∑ i, (dysonDrift N lam i * (cfgFact ξ * ∑ y ∈ labs r ξ, permD1 φ φ1 lam c y i) +
            cfgFact ξ * ∑ y ∈ labs r ξ, permD2 φ φ1 φ2 lam c y i / (2 * N)) ≤
      (r * (2 * ℓ * B * K / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)) +
          r ^ 2 * (A ^ 2 * (K ^ 2 + 1)) / (2 * N)) *
        ∑ ξ ∈ sector N r, permW φ lam c ξ * v ξ := by
  rw [sum_mul_momentGenerator_symm (cfgRate_symm lam ℓ 0) r v (permW φ lam c),
    ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun ξ hξ => ?_
  rw [← mul_add]
  calc _ ≤ v ξ * ((r * (2 * ℓ * B * K / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)) +
          r ^ 2 * (A ^ 2 * (K ^ 2 + 1)) / (2 * N)) * permW φ lam c ξ) :=
        mul_le_mul_of_nonneg_left
          (perm_point_drift_le lam ℓ c hφ hφ1 hφ0 hA hA0 hB hB0 hK0 hcomp hc₁ hshort hlong ξ)
          (hv ξ hξ)
    _ = _ := by ring

end BlockBand.Palm.MomentFlow
