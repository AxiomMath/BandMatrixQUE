module

public import BlockBand.Transmission.Generator.LayerBulk
public import BlockBand.Transmission.Generator.PowCond

/-!
# The `k = j + 2` drift error along the path: an almost-sure bound

Along the path at energy `E'` (length `r ≥ 1`, stationary jet `s`), with the normalised
variables `g = Tr T_r`, `a = Wδ₀`, `d = Wδ₁`, `t = √W(|Tr(Q_rf_r)| + hs(Q_r,f_r))`
(`pathG`, `pathA`, `pathD`, `pathT`):
* `layerTau_eq`: `τ = 4η(|Tr Qf| + √g·hs(Q,f))` (`T = 4ηQ`);
* `layerErr_le_prod`: `layerErr g e δ₁ τ √W ≤ 23(g+1)⁵(a+1)²(t+1)²(d+1)/W^{3/2}`;
* **`driftError_pow_le hGA hLp hP`**: a.s.
  `|driftError b E E' W (j+2) r| ≤ K(g+1)⁵(a+1)²(t+1)²(d+1)/√W³ + |D₀(E) - D₀(E')|k²(g+1)²/√W²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PathScalar BlockBand.Transmission.SourceMixing
open scoped ENNReal ComplexOrder

variable {W : ℕ}

/-- `τ = 4η(|Tr Qf| + √g·hs(Q,f))`. -/
theorem layerTau_eq {b E : ℝ} (hη : 0 ≤ etaZ b E) (X : Matrix (Fin W) (Fin W) ℂ) :
    layerTau b E X = 4 * etaZ b E * (‖(passiveQ b E X * passiveF b E X).trace‖ +
      Real.sqrt (passiveTransmission b E X).trace.re *
        hsSandwich (passiveQ b E X) (passiveF b E X)) := by
  set c : ℝ := 4 * etaZ b E
  have hc : 0 ≤ c := by positivity
  have h1 : (passiveTransmission b E X * passiveF b E X).trace =
      (c : ℂ) * (passiveQ b E X * passiveF b E X).trace := by
    rw [passiveTransmission, Matrix.smul_mul, trace_smul, smul_eq_mul]
  have h2 : hsSandwich (passiveTransmission b E X) (passiveF b E X) =
      c * hsSandwich (passiveQ b E X) (passiveF b E X) := by
    unfold hsSandwich
    have e : passiveTransmission b E X * passiveF b E X * passiveTransmission b E X *
        (passiveF b E X)ᴴ = ((c * c : ℝ) : ℂ) • (passiveQ b E X * passiveF b E X *
          passiveQ b E X * (passiveF b E X)ᴴ) := by
      simp only [passiveTransmission, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1; simp only [c]; push_cast; ring
    rw [e, trace_smul, smul_eq_mul, Complex.re_ofReal_mul, Real.sqrt_mul (by positivity),
      Real.sqrt_mul_self hc]
  rw [layerTau, h1, h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
  ring

/-- **`layerErr` against the normalised product.** -/
theorem layerErr_le_prod {g δ d τ s a t dd : ℝ} (hg : 0 ≤ g) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hdd : 0 ≤ dd) (hs : 1 ≤ s) (hδ : δ = a / s ^ 2) (hd : d = dd / s ^ 2)
    (hτ : τ ≤ 4 * (g + 1) * t / s) (hτ0 : 0 ≤ τ) :
    layerErr g (δ + (s ^ 2)⁻¹ ^ 2) d τ s ≤
      23 * ((g + 1) ^ 5 * (a + 1) ^ 2 * (t + 1) ^ 2 * (dd + 1)) / s ^ 3 := by
  have hs0 : 0 < s := by linarith
  set G := (g + 1) ^ 2
  set A2 := (a + 1) ^ 2
  set T2 := (t + 1) ^ 2
  set D1 := dd + 1
  have hG : 1 ≤ G := one_le_pow₀ (by linarith)
  have hA2 : 1 ≤ A2 := one_le_pow₀ (by linarith)
  have hT2 : 1 ≤ T2 := one_le_pow₀ (by linarith)
  have hD1 : 1 ≤ D1 := by simp only [D1]; linarith
  set X := G * A2 * T2 * D1
  have hX1 : 1 ≤ X := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hG hA2) hT2) hD1
  have hx_le : ∀ x : ℝ, 1 ≤ x → x ≤ x ^ 2 := fun x hx => by nlinarith
  have hAX : A2 ≤ X := by
    calc A2 = 1 * A2 * 1 * 1 := by ring
      _ ≤ X := by simp only [X]; gcongr
  have hagt : (a + 1) * (g + 1) * t ≤ X := by
    have h1 : a + 1 ≤ A2 := hx_le _ (by linarith)
    have h2 : g + 1 ≤ G := hx_le _ (by linarith)
    have h3 : t ≤ T2 := (show t ≤ t + 1 by linarith).trans (hx_le _ (by linarith))
    calc (a + 1) * (g + 1) * t ≤ A2 * G * T2 :=
          mul_le_mul (mul_le_mul h1 h2 (by linarith) (by positivity)) h3 ht (by positivity)
      _ = G * A2 * T2 * 1 := by ring
      _ ≤ X := mul_le_mul_of_nonneg_left hD1 (by positivity)
  have had : (a + 1) * (dd + 1) ≤ X := by
    have h1 : a + 1 ≤ A2 := hx_le _ (by linarith)
    calc (a + 1) * (dd + 1) ≤ 1 * A2 * 1 * D1 := by
          rw [show 1 * A2 * 1 * D1 = A2 * D1 by ring]
          exact mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ X := by simp only [X]; gcongr
  have hgt : G * t ^ 2 ≤ X := by
    have h3 : t ^ 2 ≤ T2 := pow_le_pow_left₀ ht (by linarith) 2
    calc G * t ^ 2 ≤ G * 1 * T2 * 1 := by rw [mul_one, mul_one]; gcongr
      _ ≤ X := by simp only [X]; gcongr
  have hs3 : 0 < s ^ 3 := by positivity
  have h43 : ∀ x : ℝ, 0 ≤ x → x / s ^ 4 ≤ x / s ^ 3 := fun x hx =>
    div_le_div_of_nonneg_left hx hs3 (pow_le_pow_right₀ hs (by norm_num))
  set e := δ + (s ^ 2)⁻¹ ^ 2
  have he : e ≤ (a + 1) / s ^ 2 := by
    have : (s ^ 2)⁻¹ ^ 2 ≤ 1 / s ^ 2 := by
      rw [← one_div, div_pow, one_pow]
      exact div_le_div_of_nonneg_left zero_le_one (by positivity)
        (by nlinarith [one_le_pow₀ hs (n := 2)])
    simp only [e, hδ]; rw [add_div]; linarith
  have he0 : 0 ≤ e := by simp only [e, hδ]; positivity
  -- the five summands
  have b1 : s⁻¹ ^ 3 ≤ X / s ^ 3 := by
    rw [inv_pow, ← one_div]; exact div_le_div_of_nonneg_right hX1 hs3.le
  have b2 : e * τ ≤ 4 * X / s ^ 3 := by
    calc e * τ ≤ (a + 1) / s ^ 2 * (4 * (g + 1) * t / s) := mul_le_mul he hτ hτ0 (by positivity)
      _ = 4 * ((a + 1) * (g + 1) * t) / s ^ 3 := by field_simp; try ring
      _ ≤ 4 * X / s ^ 3 := by gcongr
  have b3 : e ^ 2 ≤ X / s ^ 3 := by
    calc e ^ 2 ≤ ((a + 1) / s ^ 2) ^ 2 := pow_le_pow_left₀ he0 he 2
      _ = A2 / s ^ 4 := by simp only [A2]; field_simp; try ring
      _ ≤ A2 / s ^ 3 := h43 _ (by positivity)
      _ ≤ X / s ^ 3 := by gcongr
  have b4 : (e + d) / s ^ 2 ≤ X / s ^ 3 := by
    calc (e + d) / s ^ 2 ≤ ((a + 1) / s ^ 2 + dd / s ^ 2) / s ^ 2 := by rw [hd]; gcongr
      _ = (a + 1 + dd) / s ^ 4 := by field_simp; try ring
      _ ≤ (a + 1 + dd) / s ^ 3 := h43 _ (by positivity)
      _ ≤ X / s ^ 3 := by
          gcongr; nlinarith [mul_nonneg ha hdd]
  have b5 : τ ^ 2 / s ^ 2 ≤ 16 * X / s ^ 3 := by
    calc τ ^ 2 / s ^ 2 ≤ (4 * (g + 1) * t / s) ^ 2 / s ^ 2 := by
          gcongr
      _ = 16 * (G * t ^ 2) / s ^ 4 := by simp only [G]; field_simp; try ring
      _ ≤ 16 * (G * t ^ 2) / s ^ 3 := h43 _ (by positivity)
      _ ≤ 16 * X / s ^ 3 := by gcongr
  have hsum : s⁻¹ ^ 3 + e * τ + e ^ 2 + (e + d) / s ^ 2 + τ ^ 2 / s ^ 2 ≤ 23 * X / s ^ 3 := by
    have : 23 * X / s ^ 3 = X / s ^ 3 + 4 * X / s ^ 3 + X / s ^ 3 + X / s ^ 3 + 16 * X / s ^ 3 := by
      ring
    linarith
  unfold layerErr
  calc (g + 1) ^ 3 * (s⁻¹ ^ 3 + e * τ + e ^ 2 + (e + d) / s ^ 2 + τ ^ 2 / s ^ 2) ≤
      (g + 1) ^ 3 * (23 * X / s ^ 3) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by simp only [X, G, A2, T2, D1]; ring

/-- `g_r = Tr T_r`. -/
def pathG (b E : ℝ) (W r : ℕ) (ω : GrowthPath W) : ℝ :=
  (passiveTransmission b E (pathX b E W r ω)).trace.re

/-- `a_r = Wδ₀(X_r)`. -/
def pathA (b E : ℝ) (W r : ℕ) (ω : GrowthPath W) : ℝ := W * jetDistance0 b E (pathX b E W r ω)

/-- `d_r = Wδ₁(X_r)` at the jet `s`. -/
def pathD (b E : ℝ) (s : ℂ) (W r : ℕ) (ω : GrowthPath W) : ℝ :=
  W * jetDistance1 b E s (pathX b E W r ω)

/-- `t_r = √W(|Tr(Q_rf_r)| + hs(Q_r, f_r))`. -/
def pathT (b E : ℝ) (W r : ℕ) (ω : GrowthPath W) : ℝ :=
  Real.sqrt W * (‖(passiveQ b E (pathX b E W r ω) * passiveF b E (pathX b E W r ω)).trace‖ +
    hsSandwich (passiveQ b E (pathX b E W r ω)) (passiveF b E (pathX b E W r ω)))

end BlockBand.Transmission.Generator
