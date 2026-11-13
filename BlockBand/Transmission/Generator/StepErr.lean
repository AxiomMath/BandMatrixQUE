module

public import BlockBand.Transmission.Generator.StepInputs

/-!
# Scalar bookkeeping of the `k ≥ 2` one-layer drift error

* `step_combine`: the five pieces (quadratic, main/`f`, zeroth order, weighted mean, scalar)
  combine to `|E Tr T₊^k - P_k - A_k/W|`;
* `layerErr`: `(g+1)³(W^{-3/2} + eτ + e² + (e + δ₁)/W + τ²/W)`;
* `le_layerErr`: each summand of `layerErr`, times `g^a` with `a ≤ 3`, is dominated by
  `layerErr`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

/-- **Combination of the five pieces.** -/
theorem step_combine {I Z0 Qs F P A c Wr G k E1 E2 E3 E4 E5 Dk : ℝ} (j : ℕ)
    (hQ : |I - Z0 - Qs| ≤ E1) (hM : Qs = c ^ j * (A + Dk * P) / Wr + F) (hF : |F| ≤ E2)
    (hZ : |Z0 - c ^ (j + 2) * P - k * c ^ (j + 1) * (G - c * P)| ≤ E3)
    (hG : |G - c * P| ≤ E4) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hk : 0 ≤ k)
    (hS : |c ^ (j + 2) * P + c ^ j * (A + Dk * P) / Wr - P - A / Wr| ≤ E5) :
    |I - P - A / Wr| ≤ E1 + E2 + E3 + k * E4 + E5 := by
  have hcj : c ^ (j + 1) ≤ 1 := pow_le_one₀ hc0 hc1
  have h4 : |k * c ^ (j + 1) * (G - c * P)| ≤ k * E4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hk, abs_of_nonneg (pow_nonneg hc0 _)]
    calc k * c ^ (j + 1) * |G - c * P| ≤ k * 1 * E4 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hcj hk) hG (abs_nonneg _) (by positivity)
      _ = k * E4 := by ring
  have e : I - P - A / Wr = (I - Z0 - Qs) + F + (Z0 - c ^ (j + 2) * P - k * c ^ (j + 1) *
      (G - c * P)) + k * c ^ (j + 1) * (G - c * P) +
      (c ^ (j + 2) * P + c ^ j * (A + Dk * P) / Wr - P - A / Wr) := by rw [hM]; ring
  rw [e]
  have := abs_add_le (I - Z0 - Qs) F
  have := abs_add_le ((I - Z0 - Qs) + F) (Z0 - c ^ (j + 2) * P - k * c ^ (j + 1) * (G - c * P))
  have := abs_add_le ((I - Z0 - Qs) + F + (Z0 - c ^ (j + 2) * P - k * c ^ (j + 1) *
    (G - c * P))) (k * c ^ (j + 1) * (G - c * P))
  have := abs_add_le ((I - Z0 - Qs) + F + (Z0 - c ^ (j + 2) * P - k * c ^ (j + 1) *
    (G - c * P)) + k * c ^ (j + 1) * (G - c * P))
    (c ^ (j + 2) * P + c ^ j * (A + Dk * P) / Wr - P - A / Wr)
  linarith

/-- The one-layer error `(g+1)³(s⁻³ + eτ + e² + (e + δ₁)/s² + τ²/s²)`, `s = √W`. -/
def layerErr (g e d τ s : ℝ) : ℝ :=
  (g + 1) ^ 3 * (s⁻¹ ^ 3 + e * τ + e ^ 2 + (e + d) / s ^ 2 + τ ^ 2 / s ^ 2)

theorem layerErr_nonneg {g e d τ s : ℝ} (hg : 0 ≤ g) (he : 0 ≤ e) (hd : 0 ≤ d) (hτ : 0 ≤ τ)
    (hs : 0 < s) : 0 ≤ layerErr g e d τ s := by
  unfold layerErr; positivity

/-- Each summand of `layerErr`, times `g^a` with `a ≤ 3`, is dominated by `layerErr`. -/
theorem le_layerErr {g e d τ s : ℝ} (hg : 0 ≤ g) (he : 0 ≤ e) (hd : 0 ≤ d) (hτ : 0 ≤ τ)
    (hs : 0 < s) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ s⁻¹ ^ 3 ∨ x ≤ e * τ ∨ x ≤ e ^ 2 ∨ x ≤ (e + d) / s ^ 2 ∨ x ≤ τ ^ 2 / s ^ 2)
    {a : ℕ} (ha : a ≤ 3) : g ^ a * x ≤ layerErr g e d τ s := by
  have hg1 : g ^ a ≤ (g + 1) ^ 3 := (pow_le_pow_left₀ hg (by linarith) a).trans
    (pow_le_pow_right₀ (by linarith) ha)
  have hsum : x ≤ s⁻¹ ^ 3 + e * τ + e ^ 2 + (e + d) / s ^ 2 + τ ^ 2 / s ^ 2 := by
    have a1 : 0 ≤ s⁻¹ ^ 3 := by positivity
    have a2 : 0 ≤ e * τ := by positivity
    have a3 : 0 ≤ e ^ 2 := by positivity
    have a4 : 0 ≤ (e + d) / s ^ 2 := by positivity
    have a5 : 0 ≤ τ ^ 2 / s ^ 2 := by positivity
    rcases hx with h | h | h | h | h <;> linarith
  exact mul_le_mul hg1 hsum hx0 (by positivity)

end BlockBand.Transmission.Generator
