module

public import BlockBand.Palm.MomentFlow.PropLongShortArith

/-!
# Arithmetic of the `Flattening` assembly

* `flat_arith`: union and Tonelli–Markov bounds, `P(B) ≤ N^{-D}`, `e(c₀) ≤ N^{-D}`, `∫ e ≤ N^{-D}`.
* `flat_main_le`: the commutator main term `(b+1)(2/(K_w w)) r N^ε ℓ ≤ C₂ N^{(4r+2)ε} ℓ/w`, and
  the rough bound `b ≤ C₂ N^{(4r+2)ε}`.
* `flat_energy_alg`: `M t + X t ≤ (1 + X/K_w)(M + K_w) t`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

theorem flat_arith {x Ob1 Qo r' cp cs cP Dq D D₁ Q τ' y : ℝ} (hx : 4 ≤ x) (hOb1 : 1 ≤ Ob1)
    (hObx : Ob1 ≤ x ^ Qo) (hr' : 1 ≤ r') (hy0 : 0 ≤ y) (hy : y ≤ x ^ r')
    (hcp0 : 0 ≤ cp) (hcp : cp ≤ x ^ (r' + 1)) (hcs0 : 0 ≤ cs) (hcs : cs ≤ x ^ (r' + 1))
    (hcP0 : 0 ≤ cP) (hcP : cP ≤ x ^ (r' + 1)) (hQ : Q = 2 * r' + Qo + 1) (hQo : 0 ≤ Qo)
    (hD₁ : D₁ = 2 * Dq + Q + r' + 5) (hDq : 1 ≤ Dq) (hDD : D ≤ Dq - 1) (hτ1 : τ' ≤ 1) :
    τ' * (cp * ((Ob1 + 1) * (y * x ^ (-D₁))) + cp * (2 * Ob1) * ((3 + cs + cP) * x ^ (-D₁))) /
        x ^ (-Dq) + (3 + cs + cP) * x ^ (-D₁) + x ^ (-D₁) + x ^ (-D₁) + x ^ (-D₁) ≤ x ^ (-D) ∧
      cp * ((Ob1 + 1) * (y * x ^ (-D₁))) ≤ x ^ (-D) ∧ x ^ (-Dq) ≤ x ^ (-D) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have mono : ∀ a b : ℝ, a ≤ b → x ^ a ≤ x ^ b := fun a b h =>
    Real.rpow_le_rpow_of_exponent_le hx1 h
  have hx₁0 : 0 < x ^ (-D₁) := Real.rpow_pos_of_pos hx0 _
  have hxQo1 : 1 ≤ x ^ Qo := Real.one_le_rpow hx1 hQo
  have hOb2 : Ob1 + 1 ≤ x ^ (Qo + 1) := by
    rw [Real.rpow_add hx0, Real.rpow_one]; nlinarith
  have h2Ob : 2 * Ob1 ≤ x ^ (Qo + 1) := by
    rw [Real.rpow_add hx0, Real.rpow_one]; nlinarith
  have hδ : cp * ((Ob1 + 1) * (y * x ^ (-D₁))) ≤ x ^ (Q + 1 - D₁) := by
    calc cp * ((Ob1 + 1) * (y * x ^ (-D₁)))
        ≤ x ^ (r' + 1) * (x ^ (Qo + 1) * (x ^ r' * x ^ (-D₁))) := by gcongr
      _ = x ^ (Q + 1 - D₁) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0, hQ]; ring_nf
  have hKb : cp * (2 * Ob1) ≤ x ^ Q := by
    calc cp * (2 * Ob1) ≤ x ^ (r' + 1) * x ^ (Qo + 1) := by gcongr
      _ = x ^ (r' + Qo + 2) := by rw [← Real.rpow_add hx0]; ring_nf
      _ ≤ x ^ Q := mono _ _ (by rw [hQ]; linarith)
  have hp : (3 + cs + cP) * x ^ (-D₁) ≤ x ^ (r' + 2 - D₁) := by
    have h4 : 4 ≤ x ^ (r' + 1) := hx.trans (by
      calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ ≤ x ^ (r' + 1) := mono _ _ (by linarith))
    have h3 : 3 + cs + cP ≤ x ^ (r' + 2) := by
      have e : x ^ (r' + 2) = x ^ (r' + 1) * x := by
        rw [show r' + 2 = (r' + 1) + 1 by ring, Real.rpow_add hx0, Real.rpow_one]
      rw [e]
      have := mul_le_mul_of_nonneg_left hx (by linarith : (0 : ℝ) ≤ x ^ (r' + 1))
      linarith
    calc (3 + cs + cP) * x ^ (-D₁) ≤ x ^ (r' + 2) * x ^ (-D₁) :=
          mul_le_mul_of_nonneg_right h3 hx₁0.le
      _ = x ^ (r' + 2 - D₁) := by rw [← Real.rpow_add hx0]; ring_nf
  obtain ⟨hfin, hδD⟩ := longShort_final_arith (τ' := τ') hx hDq (by rw [hQ]; linarith) (by linarith)
    hD₁ hτ1 (by positivity) hδ (by positivity) hKb (by positivity) hp
  have hx₁q : x ^ (-D₁) ≤ x ^ (-Dq) := mono _ _ (by rw [hD₁, hQ]; linarith)
  have hDDq : x ^ (-Dq) ≤ x ^ (-D) := mono _ _ (by linarith)
  have h3 : 3 * x ^ (-Dq) ≤ x ^ (-D) := by
    have e : x ^ (-(Dq - 1)) = x ^ (-Dq) * x := by
      rw [show -(Dq - 1) = -Dq + 1 by ring, Real.rpow_add hx0, Real.rpow_one]
    have h1 : x ^ (-(Dq - 1)) ≤ x ^ (-D) := mono _ _ (by linarith)
    have h2 : 3 * x ^ (-Dq) ≤ x ^ (-Dq) * x := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_pos_of_pos hx0 _).le
    linarith
  exact ⟨by linarith, hδD.trans hDDq, hDDq⟩

theorem flat_main_le {x ε b K₀ Kw w ℓ C₂ : ℝ} {r : ℕ} (hx : 1 ≤ x) (hε : 0 < ε)
    (hbK : b + 1 ≤ K₀ * x ^ (4 * r * ε)) (hK₀N : K₀ ≤ x ^ ε) (hK₀N' : 2 * r / Kw * K₀ ≤ x ^ ε)
    (hKw : 0 < Kw) (hw : 0 < w) (hℓ : 0 ≤ ℓ) (hC₂ : 1 ≤ C₂) :
    (b + 1) * (2 / (Kw * w) * (r * (x ^ ε * ℓ))) ≤ C₂ * x ^ ((4 * r + 2) * ε) * (ℓ / w) ∧
      b ≤ C₂ * x ^ ((4 * r + 2) * ε) := by
  have hx0 : 0 < x := by linarith
  have hP : 0 ≤ x ^ (4 * r * ε) := Real.rpow_nonneg hx0.le _
  have hE : 0 ≤ x ^ ε := Real.rpow_nonneg hx0.le _
  have hlw : 0 ≤ ℓ / w := div_nonneg hℓ hw.le
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have e2 : x ^ ((4 * r + 2) * ε) = x ^ ε * x ^ (4 * r * ε) * x ^ ε := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; ring_nf
  have hN' : 0 ≤ x ^ ((4 * r + 2) * ε) := Real.rpow_nonneg hx0.le _
  have hx1e : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
  constructor
  · have e1 : 2 / (Kw * w) * (r * (x ^ ε * ℓ)) = (2 * r / Kw) * x ^ ε * (ℓ / w) := by
      field_simp
    rw [e1]
    calc (b + 1) * ((2 * r / Kw) * x ^ ε * (ℓ / w))
        ≤ (K₀ * x ^ (4 * r * ε)) * ((2 * r / Kw) * x ^ ε * (ℓ / w)) :=
          mul_le_mul_of_nonneg_right hbK (by positivity)
      _ = (2 * r / Kw * K₀) * (x ^ (4 * r * ε) * x ^ ε * (ℓ / w)) := by ring
      _ ≤ x ^ ε * (x ^ (4 * r * ε) * x ^ ε * (ℓ / w)) :=
          mul_le_mul_of_nonneg_right hK₀N' (by positivity)
      _ = x ^ ((4 * r + 2) * ε) * (ℓ / w) := by rw [e2]; ring
      _ ≤ C₂ * x ^ ((4 * r + 2) * ε) * (ℓ / w) := by
          rw [mul_assoc C₂]; exact le_mul_of_one_le_left (mul_nonneg hN' hlw) hC₂
  · calc b ≤ K₀ * x ^ (4 * r * ε) := by linarith
      _ ≤ x ^ ε * x ^ (4 * r * ε) := mul_le_mul_of_nonneg_right hK₀N hP
      _ ≤ x ^ ε * x ^ (4 * r * ε) * x ^ ε := le_mul_of_one_le_right (by positivity) hx1e
      _ = x ^ ((4 * r + 2) * ε) := e2.symm
      _ ≤ C₂ * x ^ ((4 * r + 2) * ε) := le_mul_of_one_le_left hN' hC₂

theorem flat_energy_alg {M Kw ce t : ℝ} (hM : 0 ≤ M) (hKw : 0 < Kw) (hce : 0 < ce) (ht : 0 < t) :
    M * t + (3 + 10 * Kw / ce) * t ≤ (1 + (3 + 10 * Kw / ce) / Kw) * (M + Kw) * t := by
  have hX : 0 ≤ (3 + 10 * Kw / ce) / Kw * M := by positivity
  have e : (1 + (3 + 10 * Kw / ce) / Kw) * (M + Kw) =
      M + Kw + (3 + 10 * Kw / ce) / Kw * M + (3 + 10 * Kw / ce) := by
    field_simp; ring
  have : M + (3 + 10 * Kw / ce) ≤ (1 + (3 + 10 * Kw / ce) / Kw) * (M + Kw) := by
    rw [e]; linarith
  nlinarith

end BlockBand.Palm.MomentFlow
