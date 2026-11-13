module

public import BlockBand.Palm.MomentFlow.MultiColAbs

/-!
# Column form: the two-sided drift bound for the matching weight

Deterministic. `perm_point_drift_abs`: under the hypotheses of `perm_point_drift_le`,
`|𝓢W(ζ) + Σ_i (D_i ∂_iW(ζ) + ∂²_iW(ζ)/(2N))| ≤ κ_r W(ζ)` for the matching weight `W = permW`,
with `κ_r = r(2ℓBK/N + 2A(1 + log N)/c₁ + B/(2N)) + r²A²(K² + 1)/(2N)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization

variable {N r : ℕ}

/-- **Two-sided drift bound for the matching weight, pointwise in `ζ`.** -/
theorem perm_point_drift_abs (lam : Fin N → ℝ) (ℓ : ℕ) (c : Fin r → ℝ)
    {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z)
    {A B K G c₁ : ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A)
    (hB : ∀ z, |φ2 z| ≤ B * φ z) (hB0 : 0 ≤ B) (hK0 : 0 ≤ K)
    (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ K * φ x) (hc₁ : 0 < c₁)
    (hshort : ∀ m k l, l ≠ k → labelDist k l < ℓ →
      |lam l - lam k| ≤ G ∨ (φ1 (lam k - c m) = 0 ∧ φ (lam l - c m) = φ (lam k - c m)))
    (hlong : ∀ k l, l ≠ k → ℓ ≤ labelDist k l → c₁ * labelDist k l / N ≤ |lam k - lam l|)
    (ζ : Occ N) :
    |momentGenerator (cfgRate N lam ℓ 0) (permW φ lam c) ζ +
        ∑ i, (dysonDrift N lam i * (cfgFact ζ * ∑ y ∈ labs r ζ, permD1 φ φ1 lam c y i) +
          cfgFact ζ * ∑ y ∈ labs r ζ, permD2 φ φ1 φ2 lam c y i / (2 * N))| ≤
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
  have hbr_le : ∀ y p, |br y p| ≤ κ₁ * pW φ lam c y := by
    intro y p
    have hb0 := label_bracket_abs (fun l => lam l - c p) ℓ hφ hφ1 hφ0 hA hA0 hB hB0 hK0 hcomp hc₁
      (y p) (fun l hl hd => by
        rcases hshort p (y p) l hl hd with h | h
        · left; simpa only [sub_sub_sub_cancel_right] using h
        · exact Or.inr h)
      (fun l hl hd => by simpa only [sub_sub_sub_cancel_right] using hlong (y p) l hl hd)
    have hpr : ∀ l, pairRate N (fun l => lam l - c p) (y p) l = pairRate N lam (y p) l :=
      fun l => by simp only [pairRate, sub_sub_sub_cancel_right]
    have hdd : dysonDrift N (fun l => lam l - c p) (y p) = dysonDrift N lam (y p) :=
      mf_dysonDrift_sub_const lam (c p) (y p)
    simp only [hpr, hdd] at hb0
    have hb : |(∑ j ∈ univ.erase (y p), cr (y p) j * (φ (lam j - c p) - φ (lam (y p) - c p))) +
        (φ1 (lam (y p) - c p) * dysonDrift N lam (y p) + φ2 (lam (y p) - c p) / (2 * N))| ≤
        κ₁ * φ (lam (y p) - c p) := by
      rw [hcrdef, sum_cfgRate_eq lam ℓ (fun t => φ (t - c p)) (y p)]
      exact hb0
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
    rw [e2, pW_eq_mul φ lam c y p, abs_mul, abs_of_nonneg hx]
    calc _ ≤ pWx φ lam c y p * (κ₁ * φ (lam (y p) - c p)) := mul_le_mul_of_nonneg_left hb hx
      _ = _ := by ring
  have hP3_le : ∀ y, |P3 y| ≤ (r : ℝ) ^ 2 * A ^ 2 * pW φ lam c y := by
    intro y
    have hpw := pW_nonneg hφ0 lam c y
    have hterm : ∀ p, |φ1 (lam (y p) - c p) * ∑ q ∈ univ.erase p,
        (if y q = y p then φ1 (lam (y p) - c q) * pWxx φ lam c y p q else 0)| ≤
        ∑ _q ∈ univ.erase p, A ^ 2 * pW φ lam c y := by
      intro p
      rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q hq => ?_)
      have hqp : q ≠ p := (mem_erase.1 hq).1
      by_cases hyq : y q = y p
      · rw [ite_eq_left hyq, pW_eq_mul_mul φ lam c y (Ne.symm hqp), hyq]
        have hxx := pWxx_nonneg hφ0 lam c y p q
        have h1 := hA (lam (y p) - c p)
        have h2 := hA (lam (y p) - c q)
        have hAp : 0 ≤ A * φ (lam (y p) - c p) := mul_nonneg hA0 (hφ0 _)
        have hab : |φ1 (lam (y p) - c p) * φ1 (lam (y p) - c q)| ≤
            A * φ (lam (y p) - c p) * (A * φ (lam (y p) - c q)) := by
          calc _ = |φ1 (lam (y p) - c p)| * |φ1 (lam (y p) - c q)| := abs_mul _ _
            _ ≤ _ := mul_le_mul h1 h2 (abs_nonneg _) hAp
        calc |φ1 (lam (y p) - c p) * (φ1 (lam (y p) - c q) * pWxx φ lam c y p q)|
            = |φ1 (lam (y p) - c p) * φ1 (lam (y p) - c q)| * pWxx φ lam c y p q := by
              rw [← mul_assoc, abs_mul, abs_of_nonneg hxx]
          _ ≤ (A * φ (lam (y p) - c p) * (A * φ (lam (y p) - c q))) * pWxx φ lam c y p q :=
              mul_le_mul_of_nonneg_right hab hxx
          _ = _ := by ring
      · rw [ite_eq_right hyq, mul_zero, abs_zero]; positivity
    calc |P3 y| ≤ ∑ p : Fin r, ∑ _q ∈ univ.erase p, A ^ 2 * pW φ lam c y :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => hterm p)
      _ ≤ ∑ _p : Fin r, ∑ _q : Fin r, A ^ 2 * pW φ lam c y :=
          Finset.sum_le_sum fun p _ => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) fun _ _ _ => by positivity
      _ = _ := by simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hG := sum_G_abs lam ℓ c hφ hφ0 hA hA0 hK0 hcomp hshort ζ
  have hsum : |∑ y ∈ labs r ζ, τ y| ≤
      (r * κ₁ + r ^ 2 * (A ^ 2 * (K ^ 2 + 1)) / (2 * N)) * ∑ y ∈ labs r ζ, pW φ lam c y := by
    simp only [hsplit, Finset.sum_add_distrib]
    have h1 : |∑ y ∈ labs r ζ, ∑ p, br y p| ≤ ∑ y ∈ labs r ζ, r * κ₁ * pW φ lam c y :=
      (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum fun y _ => by
        calc |∑ p, br y p| ≤ ∑ _p : Fin r, κ₁ * pW φ lam c y :=
              (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => hbr_le y p)
          _ = _ := by simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul];
                      ring
    have h3 : |∑ y ∈ labs r ζ, P3 y / (2 * N)| ≤
        ∑ y ∈ labs r ζ, (r : ℝ) ^ 2 * A ^ 2 * pW φ lam c y / (2 * N) :=
      (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum fun y _ => by
        rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * N)]
        exact div_le_div_of_nonneg_right (hP3_le y) (by positivity)
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
    have habs := abs_add_three (∑ y ∈ labs r ζ, ∑ p, br y p)
      (∑ y ∈ labs r ζ, ∑ p, ∑ q, pairG cr φ lam c p q y) (∑ y ∈ labs r ζ, P3 y / (2 * N))
    linarith
  rw [hL, abs_mul, abs_of_pos (cfgFact_pos ζ)]
  calc cfgFact ζ * |∑ y ∈ labs r ζ, τ y| ≤ cfgFact ζ *
        ((r * κ₁ + r ^ 2 * (A ^ 2 * (K ^ 2 + 1)) / (2 * N)) * ∑ y ∈ labs r ζ, pW φ lam c y) :=
        mul_le_mul_of_nonneg_left hsum (cfgFact_pos ζ).le
    _ = _ := by unfold permW; ring

end BlockBand.Palm.MomentFlow
