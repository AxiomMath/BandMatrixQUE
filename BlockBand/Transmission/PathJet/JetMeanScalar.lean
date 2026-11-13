module

public import BlockBand.Transmission.PathJet.JetMeanAlg

/-!
# The jet mean step: scalar bookkeeping

`jet_mean_scalar`: deterministic complex-number statement. Given the exact differentiated mean
identities (`jet_identity`), the stationarity of `s`, the bulk margin `‖k₋‖d_* ≤ 1 - b - g`,
and smallness `Λ ≤ Λ₀` of a size parameter `Λ` with
`‖u - a‖ ≤ A₁Λ`, `‖r₁‖, ‖r₁'‖, ‖r₂'‖ ≤ Λ`, `δ₀ ≤ Λ`, `‖φ - t‖ ≤ K_φ‖ζ - z‖`,
`‖t‖ ≤ d_* + δ₀/η` and `‖u'‖ ≤ M_u`, it gives
`‖u' - s‖ ≤ ρ_J‖t - s‖ + K Λ` with `ρ_J = rhoJ b g < 1` and `K = jetK b g η K_φ A₁ M_u`.
Here `t` is the old jet at `z` (so `‖t - s‖ = δ₁`) and `φ` the old jet at `ζ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathJet

/-- `A₄ = K_φ (2(A₁+1)/b + A₁)`, the constant of `‖φ - t‖ ≤ A₄Λ`. -/
def jetA4 (b Kφ A₁ : ℝ) : ℝ := Kφ * (2 * (A₁ + 1) / b + A₁)

/-- The smallness threshold `Λ₀`. -/
def jetLam0 (b g η Kφ A₁ : ℝ) : ℝ :=
  min (1 / (2 * A₁ + 2)) (g / (2 * (1 / η + jetA4 b Kφ A₁ + 9 * A₁ + 1)))

/-- The constant `K` of the jet mean step. -/
def jetKc (b Kφ A₁ Mu : ℝ) : ℝ := jetA4 b Kφ A₁ + (9 + 4 * Mu + 30 * A₁) / b

theorem jetLam0_pos {b g η Kφ A₁ : ℝ} (hb : 0 < b) (hg : 0 < g) (hη : 0 < η) (hK : 0 ≤ Kφ)
    (hA : 0 ≤ A₁) : 0 < jetLam0 b g η Kφ A₁ := by
  have : 0 ≤ jetA4 b Kφ A₁ := by unfold jetA4; positivity
  unfold jetLam0; exact lt_min (by positivity) (by positivity)

theorem jet_final {s t φ u' : ℂ} {b g A₄ Λ Mu A₁ e1 e2 e3 : ℝ} (hb0 : 0 < b) (hg : 0 < g)
    (hA₄ : 0 ≤ A₄) (hΛ0 : 0 ≤ Λ)
    (hcon : ‖u' - s‖ ≤ rhoJ b g * ‖φ - s‖ + (e1 + e2 * e3) / (b + g / 2))
    (he : ‖φ - t‖ ≤ A₄ * Λ) (hε : e1 ≤ (9 + 4 * Mu) * Λ) (hK1 : e3 ≤ 10)
    (hua : e2 ≤ 3 * (A₁ * Λ)) (he3 : 0 ≤ e3) (hA₁ : 0 ≤ A₁) (hMu : 0 ≤ Mu) :
    ‖u' - s‖ ≤ rhoJ b g * ‖t - s‖ + (A₄ + (9 + 4 * Mu + 30 * A₁) / b) * Λ := by
  have hρ0 := rhoJ_nonneg hb0 hg
  have hρ1 := rhoJ_lt_one hb0 hg
  have hL : 0 < b + g / 2 := by positivity
  have hφs : ‖φ - s‖ ≤ ‖t - s‖ + A₄ * Λ := by
    have := norm_add_le (t - s) (φ - t)
    rw [show t - s + (φ - t) = φ - s by ring] at this; linarith
  have hnum : e1 + e2 * e3 ≤ (9 + 4 * Mu + 30 * A₁) * Λ := by
    have : e2 * e3 ≤ 3 * (A₁ * Λ) * 10 := mul_le_mul hua hK1 he3 (by positivity)
    linarith
  have hfrac : (e1 + e2 * e3) / (b + g / 2) ≤ (9 + 4 * Mu + 30 * A₁) / b * Λ := by
    rw [div_mul_eq_mul_div]
    calc (e1 + e2 * e3) / (b + g / 2) ≤ (9 + 4 * Mu + 30 * A₁) * Λ / (b + g / 2) :=
          div_le_div_of_nonneg_right hnum hL.le
      _ ≤ (9 + 4 * Mu + 30 * A₁) * Λ / b :=
          div_le_div_of_nonneg_left (by positivity) hb0 (by linarith)
  have h1 : rhoJ b g * ‖φ - s‖ ≤ rhoJ b g * ‖t - s‖ + A₄ * Λ := by
    have := mul_le_mul_of_nonneg_left hφs hρ0
    have : rhoJ b g * (A₄ * Λ) ≤ A₄ * Λ := mul_le_of_le_one_left (by positivity) hρ1.le
    linarith [mul_add (rhoJ b g) ‖t - s‖ (A₄ * Λ)]
  linarith [add_mul A₄ ((9 + 4 * Mu + 30 * A₁) / b) Λ]

theorem jet_err_u {a u v D z r₁ : ℂ} {b A₁ Λ : ℝ} (hb0 : 0 < b) (ha : ‖a‖ = 1)
    (hz : z = a⁻¹ + (b : ℂ) * a) (hDdef : D = z - (b : ℂ) * v) (hD : u * D = 1 + r₁)
    (hx : ‖u - a‖ ≤ A₁ * Λ) (hr₁ : ‖r₁‖ ≤ Λ) (hsm : A₁ * Λ ≤ 1 / 2) :
    1 / 2 ≤ ‖u‖ ∧ ‖u‖ ≤ 3 / 2 ∧ ‖v - a‖ ≤ 2 * (A₁ + 1) / b * Λ ∧
      ‖u ^ 2 - a ^ 2‖ ≤ 3 * (A₁ * Λ) := by
  have hx' : ‖u - a‖ ≤ 1 / 2 := hx.trans hsm
  have hu1 : 1 / 2 ≤ ‖u‖ := by
    have := norm_sub_norm_le a u; rw [ha, norm_sub_rev] at this; linarith
  have hu2 : ‖u‖ ≤ 3 / 2 := by
    have := norm_add_le a (u - a)
    rw [add_sub_cancel, ha] at this; linarith
  have hva : (b : ℂ) * u * a * (v - a) = (u - a) - a * r₁ := by
    have ha0 : a ≠ 0 := fun h => by rw [h, norm_zero] at ha; exact zero_ne_one ha
    rw [hDdef, hz] at hD
    field_simp at hD
    linear_combination (-1 : ℂ) * hD
  refine ⟨hu1, hu2, ?_, ?_⟩
  · have h := congrArg norm hva
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le, ha,
      mul_one] at h
    have hr : ‖(u - a) - a * r₁‖ ≤ A₁ * Λ + Λ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, ha, one_mul]; linarith
    have hbu : b / 2 * ‖v - a‖ ≤ b * ‖u‖ * ‖v - a‖ := by
      have : b / 2 ≤ b * ‖u‖ := by nlinarith
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    rw [div_mul_eq_mul_div, le_div_iff₀ hb0]
    linarith
  · have e : u ^ 2 - a ^ 2 = (u - a) * (u + a) := by ring
    rw [e, norm_mul]
    have h3 : ‖u + a‖ ≤ 3 := (norm_add_le _ _).trans (by rw [ha]; linarith)
    calc ‖u - a‖ * ‖u + a‖ ≤ (A₁ * Λ) * 3 := mul_le_mul hx h3 (norm_nonneg _) ((norm_nonneg _).trans hx)
      _ = 3 * (A₁ * Λ) := by ring

theorem jet_err_phi {a u v z ζ φ t : ℂ} {b Kφ A₁ Λ dS δ₀ η : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hKφ : 0 ≤ Kφ) (hη : 0 < η)
    (hζz : ζ - z = -(((1 - 2 * b : ℝ) : ℂ) * (v - a) + (b : ℂ) * (u - a)))
    (hx : ‖u - a‖ ≤ A₁ * Λ) (hy : ‖v - a‖ ≤ 2 * (A₁ + 1) / b * Λ)
    (hφt : ‖φ - t‖ ≤ Kφ * ‖ζ - z‖) (ht : ‖t‖ ≤ dS + δ₀ / η) (hδ : δ₀ ≤ Λ) :
    ‖φ - t‖ ≤ jetA4 b Kφ A₁ * Λ ∧ ‖φ‖ ≤ dS + Λ / η + jetA4 b Kφ A₁ * Λ := by
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  have hq : ‖ζ - z‖ ≤ (2 * (A₁ + 1) / b + A₁) * Λ := by
    rw [hζz, norm_neg]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hc0,
      Real.norm_of_nonneg hb0.le]
    have h1' : (1 - 2 * b) * ‖v - a‖ ≤ 2 * (A₁ + 1) / b * Λ :=
      (mul_le_of_le_one_left (norm_nonneg _) (by linarith)).trans hy
    have h2' : b * ‖u - a‖ ≤ A₁ * Λ :=
      (mul_le_of_le_one_left (norm_nonneg _) (by linarith)).trans hx
    linarith
  have he : ‖φ - t‖ ≤ jetA4 b Kφ A₁ * Λ := by
    refine hφt.trans ?_
    simp only [jetA4]
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hq hKφ
  refine ⟨he, ?_⟩
  have : ‖φ‖ ≤ ‖t‖ + ‖φ - t‖ := by
    have := norm_add_le t (φ - t); rwa [add_sub_cancel] at this
  have hδη : δ₀ / η ≤ Λ / η := div_le_div_of_nonneg_right hδ hη.le
  linarith

theorem jet_den {a s k u φ : ℂ} {b g dS P Q : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hk : k = ((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * a ^ 2) (hsd : ‖s‖ ≤ dS)
    (hkd : ‖k‖ * dS ≤ 1 - b - g) (hk1 : ‖k‖ ≤ 1) (hφ : ‖φ‖ ≤ dS + P) (hφ3 : ‖φ‖ ≤ 3)
    (hP : 0 ≤ P) (hua : ‖u ^ 2 - a ^ 2‖ ≤ Q) (hPQ : P + 3 * Q ≤ g / 2) :
    b + g ≤ ‖1 + k * s‖ ∧ b + g / 2 ≤ ‖1 + (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * u ^ 2) * φ‖ := by
  refine ⟨?_, ?_⟩
  · have h := norm_sub_norm_le (1 : ℂ) (-(k * s))
    rw [sub_neg_eq_add, norm_one, norm_neg, norm_mul] at h
    have : ‖k‖ * ‖s‖ ≤ ‖k‖ * dS := mul_le_mul_of_nonneg_left hsd (norm_nonneg _)
    linarith
  · have e : 1 + (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * u ^ 2) * φ =
        (1 + k * φ) + (b : ℂ) ^ 2 * (u ^ 2 - a ^ 2) * φ := by rw [hk]; ring
    rw [e]
    have hQ : 0 ≤ Q := (norm_nonneg _).trans hua
    have h3 : ‖(b : ℂ) ^ 2 * (u ^ 2 - a ^ 2) * φ‖ ≤ 3 * Q := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hb0.le]
      have hb2 : b ^ 2 ≤ 1 := by nlinarith
      have := mul_le_mul (mul_le_mul hb2 hua (norm_nonneg _) zero_le_one) hφ3 (norm_nonneg _)
        (by positivity : (0 : ℝ) ≤ 1 * Q)
      linarith
    have h4 : 1 - ‖k‖ * ‖φ‖ ≤ ‖1 + k * φ‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (-(k * φ))
      rw [sub_neg_eq_add, norm_one, norm_neg, norm_mul] at h; linarith
    have h5 : ‖k‖ * ‖φ‖ ≤ (1 - b - g) + P := by
      have h := mul_le_mul_of_nonneg_left hφ (norm_nonneg k)
      have : ‖k‖ * P ≤ P := mul_le_of_le_one_left hP hk1
      linarith [mul_add ‖k‖ dS P]
    have h6 := norm_sub_norm_le (1 + k * φ) (-((b : ℂ) ^ 2 * (u ^ 2 - a ^ 2) * φ))
    rw [sub_neg_eq_add, norm_neg] at h6
    linarith

theorem jet_eps {s u u' φ r₁ r₁' r₂' : ℂ} {b Mu Λ dS : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hu2 : ‖u‖ ≤ 3 / 2) (hφ3 : ‖φ‖ ≤ 3) (hsd : ‖s‖ ≤ dS) (hdS : dS ≤ 2) (hMu : 0 ≤ Mu)
    (hu' : ‖u'‖ ≤ Mu) (hr₁ : ‖r₁‖ ≤ Λ) (hr₁' : ‖r₁'‖ ≤ Λ) (hr₂' : ‖r₂'‖ ≤ Λ) (hΛ0 : 0 ≤ Λ) :
    ‖r₁' * u * (1 + ((1 - 2 * b : ℝ) : ℂ) * φ) - u' * r₁ * (1 + ((1 - 2 * b : ℝ) : ℂ) * φ) +
        (b : ℂ) * u ^ 2 * r₂'‖ ≤ (9 + 4 * Mu) * Λ ∧
      ‖s * (b : ℂ) ^ 2 * φ + 1 + ((1 - 2 * b : ℝ) : ℂ) * φ‖ ≤ 10 := by
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  have hcφ : ‖1 + ((1 - 2 * b : ℝ) : ℂ) * φ‖ ≤ 4 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0]
    have : (1 - 2 * b) * ‖φ‖ ≤ 1 * 3 := mul_le_mul (by linarith) hφ3 (norm_nonneg _) zero_le_one
    linarith
  refine ⟨?_, ?_⟩
  · set w := 1 + ((1 - 2 * b : ℝ) : ℂ) * φ
    have e1 : ‖r₁' * u * w‖ ≤ Λ * (3 / 2) * 4 :=
      (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
        (mul_le_mul hr₁' hu2 (norm_nonneg _) hΛ0)) hcφ (norm_nonneg _) (by positivity))
    have e2 : ‖u' * r₁ * w‖ ≤ Mu * Λ * 4 :=
      (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
        (mul_le_mul hu' hr₁ (norm_nonneg _) hMu)) hcφ (norm_nonneg _) (by positivity))
    have hbu : ‖(b : ℂ) * u ^ 2‖ ≤ 1 * (3 / 2) ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hb0.le]
      exact mul_le_mul (by linarith) (pow_le_pow_left₀ (norm_nonneg _) hu2 2) (by positivity)
        zero_le_one
    have e3 : ‖(b : ℂ) * u ^ 2 * r₂'‖ ≤ 1 * (3 / 2) ^ 2 * Λ :=
      (norm_mul_le _ _).trans (mul_le_mul hbu hr₂' (norm_nonneg _) (by positivity))
    have := norm_add_le (r₁' * u * w - u' * r₁ * w) ((b : ℂ) * u ^ 2 * r₂')
    have := norm_sub_le (r₁' * u * w) (u' * r₁ * w)
    linarith
  · have hb2 : b ^ 2 ≤ 1 := by nlinarith
    have t1 : ‖s * (b : ℂ) ^ 2 * φ‖ ≤ 6 := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hb0.le]
      have := mul_le_mul (mul_le_mul (hsd.trans hdS) hb2 (by positivity) (by norm_num)) hφ3
        (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2 * 1)
      linarith
    have t3 : ‖((1 - 2 * b : ℝ) : ℂ) * φ‖ ≤ 3 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0]
      have := mul_le_mul (by linarith : 1 - 2 * b ≤ 1) hφ3 (norm_nonneg _) zero_le_one
      linarith
    have := norm_add_le (s * (b : ℂ) ^ 2 * φ + 1) (((1 - 2 * b : ℝ) : ℂ) * φ)
    have := norm_add_le (s * (b : ℂ) ^ 2 * φ) 1
    rw [norm_one] at this
    linarith

theorem jet_mean_scalar {a s k u v u' v' D φ t r₁ r₁' r₂' z ζ : ℂ} {b g η Kφ A₁ Mu dS δ₀ Λ : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (hg : 0 < g) (hη : 0 < η) (hKφ : 0 ≤ Kφ) (hA₁ : 0 ≤ A₁)
    (hMu : 0 ≤ Mu) (ha : ‖a‖ = 1) (hk : k = ((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * a ^ 2)
    (hs : k * s ^ 2 + (1 + ((1 - 2 * b : ℝ) : ℂ) * a ^ 2) * s + a ^ 2 = 0) (hsd : ‖s‖ ≤ dS)
    (hkd : ‖k‖ * dS ≤ 1 - b - g) (hdS : dS ≤ 2) (hk1 : ‖k‖ ≤ 1)
    (hz : z = a⁻¹ + (b : ℂ) * a) (hDdef : D = z - (b : ℂ) * v)
    (hζz : ζ - z = -(((1 - 2 * b : ℝ) : ℂ) * (v - a) + (b : ℂ) * (u - a)))
    (hD : u * D = 1 + r₁) (h1 : r₁' = u' * D + u - (b : ℂ) * u * v')
    (h2 : r₂' = v' * (1 + ((1 - 2 * b : ℝ) : ℂ) * φ) + (b : ℂ) * φ * u')
    (hx : ‖u - a‖ ≤ A₁ * Λ) (hr₁ : ‖r₁‖ ≤ Λ) (hr₁' : ‖r₁'‖ ≤ Λ) (hr₂' : ‖r₂'‖ ≤ Λ)
    (hδ0 : 0 ≤ δ₀) (hδ : δ₀ ≤ Λ) (hφt : ‖φ - t‖ ≤ Kφ * ‖ζ - z‖) (ht : ‖t‖ ≤ dS + δ₀ / η)
    (hu' : ‖u'‖ ≤ Mu) (hΛ : Λ ≤ jetLam0 b g η Kφ A₁) :
    ‖u' - s‖ ≤ rhoJ b g * ‖t - s‖ + jetKc b Kφ A₁ Mu * Λ := by
  have hΛ0 : 0 ≤ Λ := hδ0.trans hδ
  have hA₄ : 0 ≤ jetA4 b Kφ A₁ := by simp only [jetA4]; positivity
  have hΛ1 : Λ ≤ 1 / (2 * A₁ + 2) := hΛ.trans (min_le_left _ _)
  have hΛ2 : Λ ≤ g / (2 * (1 / η + (jetA4 b Kφ A₁) + 9 * A₁ + 1)) := hΛ.trans (min_le_right _ _)
  have hS : Λ / η + (jetA4 b Kφ A₁) * Λ + 9 * (3 * (A₁ * Λ)) / 3 ≤ g / 2 := by
    rw [le_div_iff₀ (by positivity)] at hΛ2
    have e : Λ / η + (jetA4 b Kφ A₁) * Λ + 9 * (3 * (A₁ * Λ)) / 3 = Λ * (1 / η + (jetA4 b Kφ A₁) + 9 * A₁) := by ring
    rw [e]; nlinarith
  have hsm : A₁ * Λ ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hΛ1
    nlinarith
  obtain ⟨hu1, hu2, hy, hua⟩ := jet_err_u hb0 ha hz hDdef hD hx hr₁ hsm
  obtain ⟨he, hφ⟩ := jet_err_phi hb0 hb hKφ hη hζz hx hy hφt ht hδ
  have hP : 0 ≤ Λ / η + (jetA4 b Kφ A₁) * Λ := by positivity
  have hg1 : g ≤ 1 := by
    have := mul_nonneg (norm_nonneg k) ((norm_nonneg s).trans hsd); linarith
  have hφ3 : ‖φ‖ ≤ 3 := by
    have : 0 ≤ 9 * (3 * (A₁ * Λ)) / 3 := by positivity
    have : φ = φ := rfl
    linarith [hφ, hS]
  have hφ' : ‖φ‖ ≤ dS + (Λ / η + (jetA4 b Kφ A₁) * Λ) := by linarith
  obtain ⟨hks, hDen⟩ := jet_den hb0 hb hk hsd hkd hk1 hφ' hφ3 hP hua (by linarith)
  have hid := jet_identity (a := a) (s := s) (k := k) (c := ((1 - 2 * b : ℝ) : ℂ)) (b := (b : ℂ))
    (u := u) (u' := u') (v' := v') (D := D) (φ := φ) (r₁ := r₁) (r₁' := r₁') (r₂' := r₂') hk hs hD
    h1 h2
  have hcon := jet_contraction (br := b) hb0 hg
    (by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]) ha hk hs hks hDen hid
  obtain ⟨hε, hK1⟩ := jet_eps (s := s) hb0 hb hu2 hφ3 hsd hdS hMu hu' hr₁ hr₁' hr₂' hΛ0
  exact jet_final hb0 hg hA₄ hΛ0 hcon he hε hK1 hua (norm_nonneg _) hA₁ hMu
