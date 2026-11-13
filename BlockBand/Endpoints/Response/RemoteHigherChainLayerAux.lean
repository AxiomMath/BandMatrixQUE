module

public import BlockBand.Endpoints.Response.RemoteHigherChainFluct

/-!
# Real algebra of the higher one-layer clock step

* `rhc_rpow_le_one_add_sq`: `x^e ≤ 1 + x²` for `0 ≤ e ≤ 2`.
* `rhc_forcing_young`: the forcing of the higher logistic inequality,
  `H^{r-1} g^{2(1-p)}γ^p ≤ ε H^{r+1}/γ^p + ε^{-(r-1)/2} g^{(r+1)(1-p)}γ^{pr}`.
* `rhc_layer_real`: the real bookkeeping of the higher one-layer inequality.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

/-- `x^e ≤ 1 + x²` for `x ≥ 0` and `0 ≤ e ≤ 2`. -/
theorem rhc_rpow_le_one_add_sq {x e : ℝ} (hx : 0 ≤ x) (he0 : 0 ≤ e) (he : e ≤ 2) :
    x ^ e ≤ 1 + x ^ 2 := by
  rcases le_total x 1 with h | h
  · have := Real.rpow_le_one hx h he0
    nlinarith [sq_nonneg x]
  · have : x ^ e ≤ x ^ ((2 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le h (by norm_num; linarith)
    rw [Real.rpow_natCast] at this
    linarith

/-- The forcing exponents: for `H, γ > 0`, `r ≥ 1`, `ε > 0`,
`H^{r-1} (g^{2(1-p)} γ^p) ≤ ε H^{r+1}/γ^p + ε^{-(r-1)/2} g^{(r+1)(1-p)} γ^{pr}` (`g ≥ 0`). -/
theorem rhc_forcing_young {H γ g p r ε : ℝ} (hH : 0 < H) (hγ : 0 < γ) (hg : 0 ≤ g) (hr : 1 ≤ r)
    (hε : 0 < ε) :
    H ^ (r - 1) * (g ^ (2 * (1 - p)) * γ ^ p) ≤
      ε * (H ^ (r + 1) / γ ^ p) + ε ^ (-((r - 1) / 2)) * (g ^ ((r + 1) * (1 - p)) * γ ^ (p * r)) := by
  set G := g ^ (1 - p) * γ ^ p with hG
  have hG0 : 0 ≤ G := by positivity
  have hγp : 0 < γ ^ p := Real.rpow_pos_of_pos hγ _
  have hy := rhc_young hr hH.le hG0 hε
  have e1 : g ^ (2 * (1 - p)) * γ ^ p = G ^ 2 / γ ^ p := by
    have hg2 : (g ^ (1 - p)) ^ 2 = g ^ (2 * (1 - p)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hg]; ring_nf
    rw [hG, mul_pow, hg2]; field_simp
  have e2 : g ^ ((r + 1) * (1 - p)) * γ ^ (p * r) = G ^ (r + 1) / γ ^ p := by
    rw [hG, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hg, ← Real.rpow_mul hγ.le,
      mul_div_assoc, ← Real.rpow_sub hγ]
    congr 2 <;> ring
  rw [e1, e2]
  have : H ^ (r - 1) * (G ^ 2 / γ ^ p) = (H ^ (r - 1) * G ^ 2) / γ ^ p := by ring
  rw [this, div_le_iff₀ hγp]
  have e3 : (ε * (H ^ (r + 1) / γ ^ p) + ε ^ (-((r - 1) / 2)) * (G ^ (r + 1) / γ ^ p)) * γ ^ p =
      ε * H ^ (r + 1) + ε ^ (-((r - 1) / 2)) * G ^ (r + 1) := by
    field_simp
  rw [e3]; exact hy

/-- Real bookkeeping of the higher one-layer step. From the integrated pointwise power
inequality `I_r + κ(a - I₁) ≤ a^r + T₂ + T_q`, the integrated `r = 1` logistic
`I₁ + c_L u Q₁ ≤ a + C_L u F₁`, and the bounds on `κQ₁`, `κF₁`, `T₂`, `T_q`, `a^r`:
`I_r + (t c_L/2) u Q_r ≤ (1 + C'δ + C'u) H^r + C' u F_r`, `C' = K₀ + K₂ + K_q + C_L M' ε'`. -/
theorem rhc_layer_real {Ir I1 a κ ar T2 Tq u Hr Q1 Qr F1 Fr δ cL CL M' ε ε' K0 K2 Kq t : ℝ}
    (hR1 : Ir + κ * (a - I1) ≤ ar + T2 + Tq) (hR2 : I1 + cL * u * Q1 ≤ a + CL * u * F1)
    (hκ : 0 ≤ κ) (hκQ : t * Qr ≤ κ * Q1) (hκF : κ * F1 ≤ M' * (ε * Qr + ε' * Fr))
    (hε : CL * M' * ε ≤ t * cL / 2) (hT2 : T2 ≤ K2 * u * Hr) (hTq : Tq ≤ Kq * u * Hr)
    (har : ar ≤ (1 + K0 * δ + K0 * u) * Hr) (hu : 0 ≤ u) (hCL : 0 ≤ CL) (hcL : 0 ≤ cL)
    (hQr : 0 ≤ Qr) (hFr : 0 ≤ Fr) (hHr : 0 ≤ Hr) (hδ : 0 ≤ δ) (hK0 : 0 ≤ K0) (hK2 : 0 ≤ K2)
    (hKq : 0 ≤ Kq) (hM' : 0 ≤ M') (hε' : 0 ≤ ε') :
    Ir + t * cL / 2 * u * Qr ≤
      (1 + (K0 + K2 + Kq + CL * M' * ε') * δ + (K0 + K2 + Kq + CL * M' * ε') * u) * Hr +
        (K0 + K2 + Kq + CL * M' * ε') * u * Fr := by
  have h1 : κ * (cL * u * Q1 - CL * u * F1) ≤ κ * (a - I1) :=
    mul_le_mul_of_nonneg_left (by linarith) hκ
  have h2 : cL * u * (t * Qr) ≤ cL * u * (κ * Q1) :=
    mul_le_mul_of_nonneg_left hκQ (by positivity)
  have h3 : CL * u * (κ * F1) ≤ CL * u * (M' * (ε * Qr + ε' * Fr)) :=
    mul_le_mul_of_nonneg_left hκF (by positivity)
  have h4 : u * Qr * (CL * M' * ε) ≤ u * Qr * (t * cL / 2) :=
    mul_le_mul_of_nonneg_left hε (by positivity)
  have hX : 0 ≤ CL * M' * ε' * u * Fr := by positivity
  have hY : 0 ≤ (K2 + Kq + CL * M' * ε') * δ * Hr := by positivity
  have hZ : 0 ≤ (K0 + K2 + Kq) * u * Fr := by positivity
  have hW : 0 ≤ CL * M' * ε' * u * Hr := by positivity
  linarith

end BlockBand.Endpoints
