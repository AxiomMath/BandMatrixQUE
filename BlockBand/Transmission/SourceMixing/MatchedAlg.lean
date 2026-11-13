module

public import BlockBand.Transmission.SourceMixing.MatchedBasic

/-!
# Scalar perturbation algebra for the matched values (deterministic part)

Exact identities at the matched values and linear stability of the scalar equations around them.

* `rhoStar_identity`: at the matched values,
  `k·θ_*·jetB + ba(1 - bθ_*s)d_* = b·c₀(1 - θ_*)`, `k = c + b²` (uses only
  `θ_*(1 + k₋s) = ba²`, `c₀(ā - a) = d_*`, `aā = 1`, `kd_* = 1 - b`);
* `s1_close`, `theta_close`, `rho_close`, `T_close`: linear stability of the three scalar equations
  (`s₁(1 - k_hA) = bh`, `θ(1 - k_v⟨M²⟩) = bv²`, `ρ₁(1 - k_hA) = T`) around the matched point, with
  explicit constants and without dividing by a small quantity (only by `b` and `|1 + k₋s| > b`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped ComplexConjugate

/-- `k = c + b²` as a complex number. -/
abbrev kStarC (b : ℝ) : ℂ := ((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2

theorem kStar_mul_dStar {b : ℝ} (hb : b < 1 / 2) : kStarC b * (dStar b : ℂ) = 1 - b := by
  have h : (1 - b : ℂ) ≠ 0 := by
    have : (1 - b : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  unfold kStarC dStar; push_cast; field_simp; ring

theorem one_add_b_dStar {b : ℝ} (hb : b < 1 / 2) : 1 + (b : ℂ) * (dStar b : ℂ) = dStar b := by
  have h : (1 - b : ℂ) ≠ 0 := by
    have : (1 - b : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  unfold dStar; push_cast; field_simp; ring

/-- The exact matched identity `ρ₁* = c₀(1 - θ_*)`. -/
theorem rhoStar_identity {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (s θ : ℂ)
    (hθ : θ * (1 + kMinus b E * s) = (b : ℂ) * matchedA E ^ 2) :
    kStarC b * (θ * 1 * jetB b E s) +
        (b : ℂ) * matchedA E * (1 + (b : ℂ) * (-(θ * s))) * (dStar b : ℂ) =
      (b : ℂ) * (cZero b E * (1 - θ)) := by
  have had : matchedA E * (dStar b : ℂ) = cZero b E * (1 - matchedA E ^ 2) := by
    have h := cZero_mul_conj_sub hb0 hb h1 h2
    have hc : matchedA E * conj (matchedA E) = 1 := matchedA_mul_conj E h1 h2
    linear_combination (-matchedA E) * h + cZero b E * hc
  have hkd := kStar_mul_dStar hb
  unfold jetB
  unfold kMinus at hθ
  linear_combination cZero b E * hθ + ((b : ℂ) * (1 - (b : ℂ) * θ * s)) * had +
    (cZero b E * θ) * hkd

/-- `s₁ - 1` from `s₁(1 - k_hA) ≈ bh`. -/
theorem s1_close {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {s₁ h A : ℂ} {e K B Cs : ℝ}
    (he : 0 ≤ e) (hK : 0 ≤ K) (hB : ‖A‖ ≤ B) (hs : ‖s₁‖ ≤ Cs)
    (hh : ‖h - 1‖ ≤ K * e) (hAd : ‖A - dStar b‖ ≤ K * e)
    (h3 : ‖s₁ * (1 - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * h) * A) - (b : ℂ) * h‖ ≤ K * e) :
    ‖(((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * h) * A - kStarC b * (dStar b : ℂ)‖ ≤
        (b ^ 2 * K * B + K) * e ∧
      ‖s₁ - 1‖ ≤ (Cs * (b ^ 2 * K * B + K) + K + b * K) / b * e := by
  have hkd := kStar_mul_dStar hb
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hk1 : ‖kStarC b‖ ≤ 1 := by
    unfold kStarC
    rw [show ((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 = (((1 - b) ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith
  have hx : ‖(((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * h) * A - kStarC b * (dStar b : ℂ)‖ ≤
      (b ^ 2 * K * B + K) * e := by
    have e' : (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * h) * A - kStarC b * (dStar b : ℂ) =
        (b : ℂ) ^ 2 * ((h - 1) * A) + kStarC b * (A - dStar b) := by unfold kStarC; ring
    rw [e']
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow, nb, norm_mul]
    have hA0 : 0 ≤ B := (norm_nonneg _).trans hB
    calc b ^ 2 * (‖h - 1‖ * ‖A‖) + ‖kStarC b‖ * ‖A - dStar b‖ ≤
        b ^ 2 * (K * e * B) + 1 * (K * e) := by gcongr
      _ = _ := by ring
  refine ⟨hx, ?_⟩
  have e' : (b : ℂ) * (s₁ - 1) = s₁ * (kStarC b * (dStar b : ℂ) -
      (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * h) * A) * (-1) +
      (s₁ * (1 - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * h) * A) - (b : ℂ) * h) +
      (b : ℂ) * (h - 1) := by
    linear_combination s₁ * hkd
  have hn' : ‖(b : ℂ) * (s₁ - 1)‖ ≤ Cs * ((b ^ 2 * K * B + K) * e) + K * e + b * (K * e) := by
    rw [e']
    refine (norm_add₃_le).trans (add_le_add_three ?_ h3 ?_)
    · rw [norm_mul, norm_mul, norm_neg, norm_one, mul_one, norm_sub_rev]
      exact mul_le_mul hs hx (norm_nonneg _) ((norm_nonneg _).trans hs)
    · rw [norm_mul, nb]; exact mul_le_mul_of_nonneg_left hh hb0.le
  have hn : b * ‖s₁ - 1‖ ≤ Cs * ((b ^ 2 * K * B + K) * e) + K * e + b * (K * e) := by
    rw [norm_mul, nb] at hn'; exact hn'
  rw [div_mul_eq_mul_div, le_div_iff₀ hb0]
  linarith

/-- `θ - θ_*` from `θ(1 - k_v⟨M²⟩) ≈ bv²`. -/
theorem theta_close {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {θ θs v m2 s : ℂ} {e K B Ct D : ℝ}
    (he : 0 ≤ e) (hK : 0 ≤ K) (hv : ‖v‖ ≤ B) (hθ : ‖θ‖ ≤ Ct) (hsD : ‖s‖ ≤ D)
    (ha : ‖matchedA E‖ = 1) (hden : b < ‖1 + kMinus b E * s‖)
    (hθs : θs * (1 + kMinus b E * s) = (b : ℂ) * matchedA E ^ 2)
    (hm2 : ‖m2 + s‖ ≤ K * e) (hva : ‖v - matchedA E‖ ≤ K * e)
    (h3 : ‖θ * (1 - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * v ^ 2) * m2) - (b : ℂ) * v ^ 2‖ ≤
      K * e) :
    ‖θ - θs‖ ≤ (Ct * ((1 + b ^ 2 * B ^ 2) * K + b ^ 2 * ((B + 1) * K) * D) + K +
      b * ((B + 1) * K)) / b * e := by
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hB : 0 ≤ B := (norm_nonneg _).trans hv
  have hv2 : ‖v ^ 2 - matchedA E ^ 2‖ ≤ (B + 1) * K * e := by
    rw [show v ^ 2 - matchedA E ^ 2 = (v + matchedA E) * (v - matchedA E) by ring, norm_mul]
    calc ‖v + matchedA E‖ * ‖v - matchedA E‖ ≤ (B + 1) * (K * e) :=
          mul_le_mul ((norm_add_le _ _).trans (by rw [ha]; linarith)) hva (norm_nonneg _)
            (by linarith)
      _ = _ := by ring
  have hkv : ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * v ^ 2‖ ≤ 1 + b ^ 2 * B ^ 2 := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
    · rw [norm_mul, norm_pow, norm_pow, nb]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv 2) (by positivity)
  have e' : (1 + kMinus b E * s) * (θ - θs) =
      θ * ((((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * v ^ 2) * (m2 + s) -
        (b : ℂ) ^ 2 * (v ^ 2 - matchedA E ^ 2) * s) +
      (θ * (1 - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * v ^ 2) * m2) - (b : ℂ) * v ^ 2) +
      (b : ℂ) * (v ^ 2 - matchedA E ^ 2) := by
    unfold kMinus at hθs ⊢
    linear_combination (-1 : ℂ) * hθs
  have hn : b * ‖θ - θs‖ ≤ Ct * ((1 + b ^ 2 * B ^ 2) * (K * e) + b ^ 2 * ((B + 1) * K * e) * D) +
      K * e + b * ((B + 1) * K * e) := by
    have hle : b * ‖θ - θs‖ ≤ ‖1 + kMinus b E * s‖ * ‖θ - θs‖ :=
      mul_le_mul_of_nonneg_right hden.le (norm_nonneg _)
    refine hle.trans ?_
    rw [← norm_mul, e']
    refine (norm_add₃_le).trans (add_le_add_three ?_ h3 ?_)
    · rw [norm_mul]
      refine mul_le_mul hθ ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) (norm_nonneg _)
        ((norm_nonneg _).trans hθ)
      · rw [norm_mul]; exact mul_le_mul hkv hm2 (norm_nonneg _) (by positivity)
      · rw [norm_mul, norm_mul, norm_pow, nb]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hv2 (by positivity)) hsD (norm_nonneg _)
          (by positivity)
    · rw [norm_mul, nb]; exact mul_le_mul_of_nonneg_left hv2 hb0.le
  rw [div_mul_eq_mul_div, le_div_iff₀ hb0]
  nlinarith

/-- `ρ₁ - ρ_*` from `ρ₁(1 - k_hA) ≈ T` and `T ≈ T_* = bρ_*`. -/
theorem rho_close {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {ρ T Ts ρs x : ℂ} {e K Kx KT Cr : ℝ}
    (hTs : Ts = (b : ℂ) * ρs) (hρ : ‖ρ‖ ≤ Cr) (hx : ‖x - kStarC b * (dStar b : ℂ)‖ ≤ Kx * e)
    (h3 : ‖ρ * (1 - x) - T‖ ≤ K * e) (hT : ‖T - Ts‖ ≤ KT * e) :
    ‖ρ - ρs‖ ≤ (Cr * Kx + K + KT) / b * e := by
  have hkd := kStar_mul_dStar hb
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have e' : (b : ℂ) * (ρ - ρs) = ρ * (x - kStarC b * (dStar b : ℂ)) + (ρ * (1 - x) - T) +
      (T - Ts) := by linear_combination ρ * hkd + hTs
  have hn : ‖(b : ℂ) * (ρ - ρs)‖ ≤ Cr * (Kx * e) + K * e + KT * e := by
    rw [e']
    refine (norm_add₃_le).trans (add_le_add_three ?_ h3 hT)
    rw [norm_mul]; exact mul_le_mul hρ hx (norm_nonneg _) ((norm_nonneg _).trans hρ)
  rw [norm_mul, nb] at hn
  rw [div_mul_eq_mul_div, le_div_iff₀ hb0]
  linarith

/-- The telescoping bound `|T - T_*| ≤ K_T e`. -/
theorem T_close {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {kh θ θs s₁ B jB v a τ t₂ d s : ℂ}
    {e K Kθ Ks Kτ Kt Ct Cs CB Ct2 D : ℝ}
    (hkh : ‖kh - kStarC b‖ ≤ b ^ 2 * K * e) (hθ : ‖θ‖ ≤ Ct) (hs₁ : ‖s₁‖ ≤ Cs) (hB : ‖B‖ ≤ CB)
    (hθs : ‖θs‖ ≤ 1) (hBj : ‖B - jB‖ ≤ K * e) (hva : ‖v - a‖ ≤ K * e) (hτ : ‖τ‖ ≤ Ct)
    (ht₂ : ‖t₂‖ ≤ Ct2) (ha : ‖a‖ = 1) (hτs : ‖τ + θs * s‖ ≤ Kτ * e) (hsD : ‖s‖ ≤ D)
    (htd : ‖t₂ - d‖ ≤ Kt * e) (hθθ : ‖θ - θs‖ ≤ Kθ * e) (hs1 : ‖s₁ - 1‖ ≤ Ks * e) :
    ‖(kh * (θ * s₁ * B) + (b : ℂ) * v * (1 + (b : ℂ) * τ) * t₂) -
        (kStarC b * (θs * 1 * jB) + (b : ℂ) * a * (1 + (b : ℂ) * (-(θs * s))) * d)‖ ≤
      (b ^ 2 * K * (Ct * Cs * CB) + Kθ * Cs * CB + Ks * CB + K + b * K * (1 + b * Ct) * Ct2 +
        b * b * Kτ * Ct2 + b * (1 + b * D) * Kt) * e := by
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hk1 : ‖kStarC b‖ ≤ 1 := by
    unfold kStarC
    rw [show ((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 = (((1 - b) ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith
  have hCt : 0 ≤ Ct := (norm_nonneg _).trans hθ
  have hCs : 0 ≤ Cs := (norm_nonneg _).trans hs₁
  have hCB : 0 ≤ CB := (norm_nonneg _).trans hB
  have hCt2 : 0 ≤ Ct2 := (norm_nonneg _).trans ht₂
  have hD : 0 ≤ D := (norm_nonneg _).trans hsD
  have n1 : 0 ≤ b ^ 2 * K * e := (norm_nonneg _).trans hkh
  have n2 : 0 ≤ Kθ * e := (norm_nonneg _).trans hθθ
  have n3 : 0 ≤ Ks * e := (norm_nonneg _).trans hs1
  have n4 : 0 ≤ K * e := (norm_nonneg _).trans hBj
  have n5 : 0 ≤ Kτ * e := (norm_nonneg _).trans hτs
  have n6 : 0 ≤ Kt * e := (norm_nonneg _).trans htd
  have e' : (kh * (θ * s₁ * B) + (b : ℂ) * v * (1 + (b : ℂ) * τ) * t₂) -
      (kStarC b * (θs * 1 * jB) + (b : ℂ) * a * (1 + (b : ℂ) * (-(θs * s))) * d) =
      (kh - kStarC b) * (θ * s₁ * B) + kStarC b * ((θ - θs) * s₁ * B) +
        kStarC b * (θs * (s₁ - 1) * B) + kStarC b * (θs * (B - jB)) +
        (b : ℂ) * (v - a) * (1 + (b : ℂ) * τ) * t₂ + (b : ℂ) * a * ((b : ℂ) * (τ + θs * s)) * t₂ +
        (b : ℂ) * a * (1 - (b : ℂ) * (θs * s)) * (t₂ - d) := by ring
  rw [e']
  have h1τ : ‖1 + (b : ℂ) * τ‖ ≤ 1 + b * Ct := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul, nb]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hτ hb0.le)
  have h1s : ‖1 - (b : ℂ) * (θs * s)‖ ≤ 1 + b * D := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, nb, norm_mul]
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hb0.le)
    calc ‖θs‖ * ‖s‖ ≤ 1 * D := mul_le_mul hθs hsD (norm_nonneg _) zero_le_one
      _ = D := one_mul D
  have t1 : ‖(kh - kStarC b) * (θ * s₁ * B)‖ ≤ b ^ 2 * K * (Ct * Cs * CB) * e := by
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖kh - kStarC b‖ * (‖θ‖ * ‖s₁‖ * ‖B‖) ≤ b ^ 2 * K * e * (Ct * Cs * CB) := by gcongr
      _ = _ := by ring
  have t2 : ‖kStarC b * ((θ - θs) * s₁ * B)‖ ≤ Kθ * Cs * CB * e := by
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖kStarC b‖ * (‖θ - θs‖ * ‖s₁‖ * ‖B‖) ≤ 1 * (Kθ * e * Cs * CB) := by gcongr
      _ = _ := by ring
  have t3 : ‖kStarC b * (θs * (s₁ - 1) * B)‖ ≤ Ks * CB * e := by
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖kStarC b‖ * (‖θs‖ * ‖s₁ - 1‖ * ‖B‖) ≤ 1 * (1 * (Ks * e) * CB) := by gcongr
      _ = _ := by ring
  have t4 : ‖kStarC b * (θs * (B - jB))‖ ≤ K * e := by
    rw [norm_mul, norm_mul]
    calc ‖kStarC b‖ * (‖θs‖ * ‖B - jB‖) ≤ 1 * (1 * (K * e)) := by gcongr
      _ = _ := by ring
  have t5 : ‖(b : ℂ) * (v - a) * (1 + (b : ℂ) * τ) * t₂‖ ≤ b * K * (1 + b * Ct) * Ct2 * e := by
    rw [norm_mul, norm_mul, norm_mul, nb]
    calc b * ‖v - a‖ * ‖1 + (b : ℂ) * τ‖ * ‖t₂‖ ≤ b * (K * e) * (1 + b * Ct) * Ct2 := by gcongr
      _ = _ := by ring
  have t6 : ‖(b : ℂ) * a * ((b : ℂ) * (τ + θs * s)) * t₂‖ ≤ b * b * Kτ * Ct2 * e := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, nb, ha]
    calc b * 1 * (b * ‖τ + θs * s‖) * ‖t₂‖ ≤ b * 1 * (b * (Kτ * e)) * Ct2 := by gcongr
      _ = _ := by ring
  have t7 : ‖(b : ℂ) * a * (1 - (b : ℂ) * (θs * s)) * (t₂ - d)‖ ≤ b * (1 + b * D) * Kt * e := by
    rw [norm_mul, norm_mul, norm_mul, nb, ha]
    calc b * 1 * ‖1 - (b : ℂ) * (θs * s)‖ * ‖t₂ - d‖ ≤ b * 1 * (1 + b * D) * (Kt * e) := by
          gcongr
      _ = _ := by ring
  calc _ ≤ ‖(kh - kStarC b) * (θ * s₁ * B)‖ + ‖kStarC b * ((θ - θs) * s₁ * B)‖ +
        ‖kStarC b * (θs * (s₁ - 1) * B)‖ + ‖kStarC b * (θs * (B - jB))‖ +
        ‖(b : ℂ) * (v - a) * (1 + (b : ℂ) * τ) * t₂‖ +
        ‖(b : ℂ) * a * ((b : ℂ) * (τ + θs * s)) * t₂‖ +
        ‖(b : ℂ) * a * (1 - (b : ℂ) * (θs * s)) * (t₂ - d)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_add_le _ _
    _ ≤ _ := by linarith [t1, t2, t3, t4, t5, t6, t7]

end BlockBand.Transmission.SourceMixing
