module

public import BlockBand.Transmission.Generator.StepErr

/-!
# Scalar bookkeeping: `layer_point`'s right side is `O(layerErr)`

With `W = s²`, `s ≥ 1`, `e = δ + W⁻²`, `q ≤ c_q g`, `0 ≤ D ≤ C_D`, `σ₁, σ₂ ≤ C_σ/W`,
`U_a ≤ C_u(e + q/W)` and `ε ≤ C_ε(W⁻² + W⁻¹(δ + d + q/W))`, each of the seven terms of
`layer_point`'s bound is `≤ const·layerErr g e d τ s` (`layer_rhs_le`). Every term is
`const·g^a·x` with `a ≤ 3` and `x` one summand of `layerErr` (`le_layerErr`), using
`W⁻² ≤ s⁻³` and `q g^a ≤ c_q g^{a+1}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

section Atoms

variable {g e d τ s : ℝ} (hg : 0 ≤ g) (he : 0 ≤ e) (hd : 0 ≤ d) (hτ : 0 ≤ τ) (hs : 1 ≤ s)
include hg he hd hτ hs

theorem at_s3 {a : ℕ} (ha : a ≤ 3) : g ^ a * s⁻¹ ^ 3 ≤ layerErr g e d τ s :=
  le_layerErr hg he hd hτ (by linarith) (by positivity) (Or.inl le_rfl) ha

theorem at_W2 {a : ℕ} (ha : a ≤ 3) : g ^ a * ((s ^ 2)⁻¹ ^ 2) ≤ layerErr g e d τ s := by
  have hs0 : 0 < s := by linarith
  have h : (s ^ 2)⁻¹ ^ 2 ≤ s⁻¹ ^ 3 := by
    rw [← inv_pow, ← pow_mul]
    exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hs) (by norm_num)
  exact le_layerErr hg he hd hτ hs0 (by positivity) (Or.inl h) ha

theorem at_eW {a : ℕ} (ha : a ≤ 3) : g ^ a * (e / s ^ 2) ≤ layerErr g e d τ s := by
  have hs0 : 0 < s := by linarith
  exact le_layerErr hg he hd hτ hs0 (by positivity) (Or.inr (Or.inr (Or.inr (Or.inl
    (div_le_div_of_nonneg_right (by linarith) (by positivity)))))) ha

theorem at_dW {a : ℕ} (ha : a ≤ 3) : g ^ a * (d / s ^ 2) ≤ layerErr g e d τ s := by
  have hs0 : 0 < s := by linarith
  exact le_layerErr hg he hd hτ hs0 (by positivity) (Or.inr (Or.inr (Or.inr (Or.inl
    (div_le_div_of_nonneg_right (by linarith) (by positivity)))))) ha

theorem at_eτ {a : ℕ} (ha : a ≤ 3) : g ^ a * (e * τ) ≤ layerErr g e d τ s :=
  le_layerErr hg he hd hτ (by linarith) (by positivity) (Or.inr (Or.inl le_rfl)) ha

theorem at_e2 {a : ℕ} (ha : a ≤ 3) : g ^ a * e ^ 2 ≤ layerErr g e d τ s :=
  le_layerErr hg he hd hτ (by linarith) (by positivity) (Or.inr (Or.inr (Or.inl le_rfl))) ha

theorem at_τ2 {a : ℕ} (ha : a ≤ 3) : g ^ a * (τ ^ 2 / s ^ 2) ≤ layerErr g e d τ s :=
  le_layerErr hg he hd hτ (by linarith) (by positivity)
    (Or.inr (Or.inr (Or.inr (Or.inr le_rfl)))) ha

end Atoms

section Terms

variable {g δ d τ s q cq : ℝ}

/-- `q·g²/W² ≤ c_q·L`. -/
theorem t_qg2 (hg : 0 ≤ g) (hδ : 0 ≤ δ) (hd : 0 ≤ d) (hτ : 0 ≤ τ)
    (hs : 1 ≤ s) (_hq0 : 0 ≤ q) (hq : q ≤ cq * g) (hcq : 0 ≤ cq) :
    q * (g ^ 2 / s ^ 2) / s ^ 2 ≤ cq * layerErr g (δ + (s ^ 2)⁻¹ ^ 2) d τ s := by
  have he : 0 ≤ δ + (s ^ 2)⁻¹ ^ 2 := by positivity
  have a2 := at_W2 hg he hd hτ hs (a := 3) (by norm_num)
  have e1 : q * (g ^ 2 / s ^ 2) / s ^ 2 = q * (g ^ 2 * (s ^ 2)⁻¹ ^ 2) := by ring
  have e2 : cq * (g ^ 3 * (s ^ 2)⁻¹ ^ 2) = (cq * g) * (g ^ 2 * (s ^ 2)⁻¹ ^ 2) := by ring
  rw [e1]
  calc q * (g ^ 2 * (s ^ 2)⁻¹ ^ 2) ≤ (cq * g) * (g ^ 2 * (s ^ 2)⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_right hq (by positivity)
    _ = cq * (g ^ 3 * (s ^ 2)⁻¹ ^ 2) := e2.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left a2 hcq

/-- `U_a·g²/W ≤ C_u(1 + c_q)·L`. -/
theorem t_Ua (hg : 0 ≤ g) (hδ : 0 ≤ δ) (hd : 0 ≤ d) (hτ : 0 ≤ τ)
    (hs : 1 ≤ s) (hq0 : 0 ≤ q) (hq : q ≤ cq * g) (hcq : 0 ≤ cq)
    {Ua Cu : ℝ} (hCu : 0 ≤ Cu) (hUa : Ua ≤ Cu * (δ + (s ^ 2)⁻¹ ^ 2 + q / s ^ 2)) :
    Ua * (g ^ 2 / s ^ 2) ≤ Cu * (1 + cq) * layerErr g (δ + (s ^ 2)⁻¹ ^ 2) d τ s := by
  have he : 0 ≤ δ + (s ^ 2)⁻¹ ^ 2 := by positivity
  have a1 := at_eW hg he hd hτ hs (a := 2) (by norm_num)
  have a3 := t_qg2 hg hδ hd hτ hs hq0 hq hcq
  calc Ua * (g ^ 2 / s ^ 2) ≤ Cu * (δ + (s ^ 2)⁻¹ ^ 2 + q / s ^ 2) * (g ^ 2 / s ^ 2) :=
        mul_le_mul_of_nonneg_right hUa (by positivity)
    _ = Cu * (g ^ 2 * ((δ + (s ^ 2)⁻¹ ^ 2) / s ^ 2) + q * (g ^ 2 / s ^ 2) / s ^ 2) := by ring
    _ ≤ Cu * (layerErr g (δ + (s ^ 2)⁻¹ ^ 2) d τ s +
          cq * layerErr g (δ + (s ^ 2)⁻¹ ^ 2) d τ s) :=
        mul_le_mul_of_nonneg_left (add_le_add a1 a3) hCu
    _ = _ := by ring

/-- `U_a²·g ≤ 2C_u²(1 + c_q²)·L`. -/
theorem t_Ua2 (hg : 0 ≤ g) (hδ : 0 ≤ δ) (hd : 0 ≤ d) (hτ : 0 ≤ τ)
    (hs : 1 ≤ s) (hq0 : 0 ≤ q) (hq : q ≤ cq * g) (_hcq : 0 ≤ cq)
    {Ua Cu : ℝ} (hUa0 : 0 ≤ Ua) (hUa : Ua ≤ Cu * (δ + (s ^ 2)⁻¹ ^ 2 + q / s ^ 2)) :
    Ua ^ 2 * g ≤ 2 * Cu ^ 2 * (1 + cq ^ 2) * layerErr g (δ + (s ^ 2)⁻¹ ^ 2) d τ s := by
  set e := δ + (s ^ 2)⁻¹ ^ 2
  set L := layerErr g e d τ s
  have he : 0 ≤ e := by positivity
  have a1 : g ^ 1 * e ^ 2 ≤ L := at_e2 hg he hd hτ hs (a := 1) (by norm_num)
  have a2 : g ^ 3 * (s ^ 2)⁻¹ ^ 2 ≤ L := at_W2 hg he hd hτ hs (a := 3) (by norm_num)
  have hU2 : Ua ^ 2 ≤ (Cu * (e + q / s ^ 2)) ^ 2 := pow_le_pow_left₀ hUa0 hUa 2
  have h2 : (Cu * (e + q / s ^ 2)) ^ 2 ≤ 2 * Cu ^ 2 * (e ^ 2 + (q / s ^ 2) ^ 2) := by
    have h := mul_nonneg (sq_nonneg Cu) (sq_nonneg (e - q / s ^ 2))
    nlinarith
  have h3 : (q / s ^ 2) ^ 2 * g ≤ cq ^ 2 * (g ^ 3 * (s ^ 2)⁻¹ ^ 2) := by
    have e1 : (q / s ^ 2) ^ 2 * g = q ^ 2 * (g * (s ^ 2)⁻¹ ^ 2) := by ring
    have e2 : cq ^ 2 * (g ^ 3 * (s ^ 2)⁻¹ ^ 2) = (cq * g) ^ 2 * (g * (s ^ 2)⁻¹ ^ 2) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq 2) (by positivity)
  have hL0 : 0 ≤ L := layerErr_nonneg hg he hd hτ (by linarith)
  rw [pow_one] at a1
  calc Ua ^ 2 * g ≤ 2 * Cu ^ 2 * (e ^ 2 + (q / s ^ 2) ^ 2) * g :=
        mul_le_mul_of_nonneg_right (hU2.trans h2) hg
    _ = 2 * Cu ^ 2 * (g * e ^ 2 + (q / s ^ 2) ^ 2 * g) := by ring
    _ ≤ 2 * Cu ^ 2 * (L + cq ^ 2 * L) := mul_le_mul_of_nonneg_left (add_le_add a1
          (h3.trans (mul_le_mul_of_nonneg_left a2 (sq_nonneg _)))) (by positivity)
    _ = _ := by ring

/-- `ε·g² ≤ C_ε(3 + c_q)·L`. -/
theorem t_eps (hg : 0 ≤ g) (hδ : 0 ≤ δ) (hd : 0 ≤ d) (hτ : 0 ≤ τ)
    (hs : 1 ≤ s) (hq0 : 0 ≤ q) (hq : q ≤ cq * g) (hcq : 0 ≤ cq)
    {ε Cε : ℝ} (hCε : 0 ≤ Cε)
    (hε : ε ≤ Cε * ((s ^ 2)⁻¹ ^ 2 + (s ^ 2)⁻¹ * (δ + d + q / s ^ 2))) :
    ε * g ^ 2 ≤ Cε * (3 + cq) * layerErr g (δ + (s ^ 2)⁻¹ ^ 2) d τ s := by
  set e := δ + (s ^ 2)⁻¹ ^ 2
  set L := layerErr g e d τ s
  have he : 0 ≤ e := by positivity
  have a1 : g ^ 2 * (s ^ 2)⁻¹ ^ 2 ≤ L := at_W2 hg he hd hτ hs (by norm_num)
  have a2 : g ^ 2 * (e / s ^ 2) ≤ L := at_eW hg he hd hτ hs (by norm_num)
  have a3 : g ^ 2 * (d / s ^ 2) ≤ L := at_dW hg he hd hτ hs (by norm_num)
  have a4 := t_qg2 hg hδ hd hτ hs hq0 hq hcq
  have hδe : g ^ 2 * (δ / s ^ 2) ≤ g ^ 2 * (e / s ^ 2) := by
    gcongr; simp only [e]; linarith [sq_nonneg (s ^ 2)⁻¹]
  calc ε * g ^ 2 ≤ Cε * ((s ^ 2)⁻¹ ^ 2 + (s ^ 2)⁻¹ * (δ + d + q / s ^ 2)) * g ^ 2 :=
        mul_le_mul_of_nonneg_right hε (sq_nonneg _)
    _ = Cε * (g ^ 2 * (s ^ 2)⁻¹ ^ 2 + g ^ 2 * (δ / s ^ 2) + g ^ 2 * (d / s ^ 2) +
          q * (g ^ 2 / s ^ 2) / s ^ 2) := by ring
    _ ≤ Cε * (L + L + L + cq * L) := by
        gcongr
        · exact hδe.trans a2
    _ = _ := by ring

/-- `(σ₁ + σ₂)·τ² ≤ 2C_σ·L` for `σᵢ ≤ C_σ/W`. -/
theorem t_tau (hg : 0 ≤ g) (hδ : 0 ≤ δ) (hd : 0 ≤ d) (hτ : 0 ≤ τ)
    (hs : 1 ≤ s) (_hq0 : 0 ≤ q) (_hq : q ≤ cq * g) (_hcq : 0 ≤ cq)
    {σ1 σ2 Cσ : ℝ} (hCσ : 0 ≤ Cσ) (h1 : σ1 ≤ Cσ / s ^ 2) (h2 : σ2 ≤ Cσ / s ^ 2) :
    (σ1 + σ2) * τ ^ 2 ≤ 2 * Cσ * layerErr g (δ + (s ^ 2)⁻¹ ^ 2) d τ s := by
  have he : 0 ≤ δ + (s ^ 2)⁻¹ ^ 2 := by positivity
  have a : g ^ 0 * (τ ^ 2 / s ^ 2) ≤ layerErr g (δ + (s ^ 2)⁻¹ ^ 2) d τ s :=
    at_τ2 hg he hd hτ hs (by norm_num)
  rw [pow_zero, one_mul] at a
  calc (σ1 + σ2) * τ ^ 2 ≤ (Cσ / s ^ 2 + Cσ / s ^ 2) * τ ^ 2 :=
        mul_le_mul_of_nonneg_right (add_le_add h1 h2) (sq_nonneg _)
    _ = 2 * Cσ * (τ ^ 2 / s ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left a (by linarith)

/-- The weighted-mean term: `C_m(eτ + e²g + eqg/W + W⁻²g) ≤ C_m(3 + c_q)·L`. -/
theorem t_wm (hg : 0 ≤ g) (hδ : 0 ≤ δ) (hd : 0 ≤ d) (hτ : 0 ≤ τ)
    (hs : 1 ≤ s) (_hq0 : 0 ≤ q) (hq : q ≤ cq * g) (hcq : 0 ≤ cq)
    {Cm : ℝ} (hCm : 0 ≤ Cm) :
    Cm * ((δ + (s ^ 2)⁻¹ ^ 2) * τ + (δ + (s ^ 2)⁻¹ ^ 2) ^ 2 * g +
      (δ + (s ^ 2)⁻¹ ^ 2) * q * g / s ^ 2 + (s ^ 2)⁻¹ ^ 2 * g) ≤
      Cm * (3 + cq) * layerErr g (δ + (s ^ 2)⁻¹ ^ 2) d τ s := by
  set e := δ + (s ^ 2)⁻¹ ^ 2
  set L := layerErr g e d τ s
  have he : 0 ≤ e := by positivity
  have a1 : g ^ 0 * (e * τ) ≤ L := at_eτ hg he hd hτ hs (by norm_num)
  have a2 : g ^ 1 * e ^ 2 ≤ L := at_e2 hg he hd hτ hs (by norm_num)
  have a3 : g ^ 2 * (e / s ^ 2) ≤ L := at_eW hg he hd hτ hs (by norm_num)
  have a4 : g ^ 1 * (s ^ 2)⁻¹ ^ 2 ≤ L := at_W2 hg he hd hτ hs (by norm_num)
  rw [pow_zero, one_mul] at a1
  rw [pow_one] at a2 a4
  have h3 : e * q * g / s ^ 2 ≤ cq * L := by
    have e1 : e * q * g / s ^ 2 = q * (g * (e / s ^ 2)) := by ring
    have e2 : cq * (g ^ 2 * (e / s ^ 2)) = (cq * g) * (g * (e / s ^ 2)) := by ring
    rw [e1]
    calc q * (g * (e / s ^ 2)) ≤ (cq * g) * (g * (e / s ^ 2)) :=
          mul_le_mul_of_nonneg_right hq (by positivity)
      _ = cq * (g ^ 2 * (e / s ^ 2)) := e2.symm
      _ ≤ cq * L := mul_le_mul_of_nonneg_left a3 hcq
  calc Cm * (e * τ + e ^ 2 * g + e * q * g / s ^ 2 + (s ^ 2)⁻¹ ^ 2 * g) ≤
      Cm * (L + L + cq * L + L) := by
        gcongr
        · linarith
        · linarith
    _ = _ := by ring

end Terms

/-- The scalar term `k²y²g + j·y·D₀k²g²/W`, `y = D₀g/(2W)`, `0 ≤ D₀ ≤ C_D`. -/
theorem t_scal {g δ d τ s D CD : ℝ} (hg : 0 ≤ g) (hδ : 0 ≤ δ) (hd : 0 ≤ d) (hτ : 0 ≤ τ)
    (hs : 1 ≤ s) (hD : 0 ≤ D) (hDC : D ≤ CD) (j : ℕ) :
    ((j + 2 : ℕ) : ℝ) ^ 2 * (D * g / (2 * s ^ 2)) ^ 2 * g +
        j * (D * g / (2 * s ^ 2)) * (D * ((j + 2 : ℕ) : ℝ) ^ 2 * g ^ 2) / s ^ 2 ≤
      ((j + 2 : ℕ) : ℝ) ^ 2 * CD ^ 2 * (1 + j) * layerErr g (δ + (s ^ 2)⁻¹ ^ 2) d τ s := by
  have he : 0 ≤ δ + (s ^ 2)⁻¹ ^ 2 := by positivity
  have a : g ^ 3 * (s ^ 2)⁻¹ ^ 2 ≤ layerErr g (δ + (s ^ 2)⁻¹ ^ 2) d τ s :=
    at_W2 hg he hd hτ hs (by norm_num)
  have hs0 : 0 < s := by linarith
  set n : ℝ := ((j + 2 : ℕ) : ℝ)
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hD2 : D ^ 2 ≤ CD ^ 2 := pow_le_pow_left₀ hD hDC 2
  have e1 : n ^ 2 * (D * g / (2 * s ^ 2)) ^ 2 * g +
      j * (D * g / (2 * s ^ 2)) * (D * n ^ 2 * g ^ 2) / s ^ 2 =
      n ^ 2 * (1 / 4 + j / 2) * D ^ 2 * (g ^ 3 * (s ^ 2)⁻¹ ^ 2) := by
    field_simp; ring
  rw [e1]
  have hn : 0 ≤ n := Nat.cast_nonneg _
  calc n ^ 2 * (1 / 4 + j / 2) * D ^ 2 * (g ^ 3 * (s ^ 2)⁻¹ ^ 2) ≤
      n ^ 2 * (1 + j) * CD ^ 2 * (g ^ 3 * (s ^ 2)⁻¹ ^ 2) := by
        gcongr
        · linarith
        · linarith
    _ ≤ n ^ 2 * (1 + j) * CD ^ 2 * layerErr g (δ + (s ^ 2)⁻¹ ^ 2) d τ s :=
        mul_le_mul_of_nonneg_left a (by positivity)
    _ = _ := by ring

/-- The constant of `layer_rhs_le`. -/
def layerK (j : ℕ) (cq CD Cb Cu Cm Cε Cσ : ℝ) : ℝ :=
  ((j + 2 : ℕ) : ℝ) ^ 3 * (3 * 2) ^ (2 * (j + 2)) * Cb ^ 3 +
    ((j + 2 : ℕ) : ℝ) ^ 2 * (3 * (j + 1 : ℕ) * 2 ^ (3 * (j + 1))) * Cb ^ 2 * (Cu * (1 + cq)) +
    ((j + 1 : ℕ) : ℝ) ^ 2 * (Cε * (3 + cq)) + ((j + 1 : ℕ) : ℝ) ^ 2 * (2 * Cσ) +
    ((j + 2 : ℕ) : ℝ) * (3 * 2) ^ (2 * (j + 2)) * (2 * Cu ^ 2 * (1 + cq ^ 2)) +
    ((j + 2 : ℕ) : ℝ) * (Cm * (3 + cq)) + ((j + 2 : ℕ) : ℝ) ^ 2 * CD ^ 2 * (1 + j)

theorem layerK_nonneg (j : ℕ) {cq CD Cb Cu Cm Cε Cσ : ℝ} (hcq : 0 ≤ cq) (hCb : 0 ≤ Cb)
    (hCu : 0 ≤ Cu) (hCm : 0 ≤ Cm) (hCε : 0 ≤ Cε) (hCσ : 0 ≤ Cσ) :
    0 ≤ layerK j cq CD Cb Cu Cm Cε Cσ := by
  unfold layerK; positivity

/-- **`layer_point`'s right side is `≤ layerK·layerErr`** (generic reals, `W = s²`). -/
theorem layer_rhs_le {g δ d τ q cq D CD Cb Cu Cm Cε Cσ Ua ε σ1 σ2 W s : ℝ} (j : ℕ)
    (hg : 0 ≤ g) (hδ : 0 ≤ δ) (hd : 0 ≤ d) (hτ : 0 ≤ τ) (hs : 1 ≤ s) (hsW : s ^ 2 = W)
    (hq0 : 0 ≤ q) (hq : q ≤ cq * g) (hcq : 0 ≤ cq) (hD : 0 ≤ D) (hDC : D ≤ CD)
    (hCb : 0 ≤ Cb) (hCu : 0 ≤ Cu) (hCm : 0 ≤ Cm) (hCε : 0 ≤ Cε) (hCσ : 0 ≤ Cσ)
    (hUa0 : 0 ≤ Ua) (hUa : Ua ≤ Cu * (δ + W⁻¹ ^ 2 + q / W))
    (hε : ε ≤ Cε * (W⁻¹ ^ 2 + W⁻¹ * (δ + d + q / W)))
    (h1 : σ1 ≤ Cσ / W) (h2 : σ2 ≤ Cσ / W) :
    (((j + 1 + 1 : ℕ) : ℝ) ^ 3 * (3 * 2) ^ (2 * (j + 1 + 1)) * (Cb / s * g) ^ 3 +
        ((j + 1 + 1 : ℕ) : ℝ) * (((j + 1 + 1 : ℕ) : ℝ) * (3 * (j + 1 : ℕ) * 2 ^ (3 * (j + 1)) *
          Ua)) * (Cb / s * g) ^ 2 +
        ε * (((j + 1 : ℕ) : ℝ) ^ 2 * g ^ 2)) +
      (σ1 + σ2) * ((j + 1 : ℕ) : ℝ) ^ 2 * τ ^ 2 +
      ((j + 1 + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (j + 1 + 1)) * (Ua ^ 2 * g) +
      ((j + 2 : ℕ) : ℝ) * (Cm * ((δ + W⁻¹ ^ 2) * τ + (δ + W⁻¹ ^ 2) ^ 2 * g +
        (δ + W⁻¹ ^ 2) * q * g / W + W⁻¹ ^ 2 * g)) +
      (((j + 2 : ℕ) : ℝ) ^ 2 * (D * g / (2 * W)) ^ 2 * g +
        j * (D * g / (2 * W)) * (D * ((j + 2 : ℕ) : ℝ) ^ 2 * g ^ 2) / W) ≤
      layerK j cq CD Cb Cu Cm Cε Cσ * layerErr g (δ + W⁻¹ ^ 2) d τ s := by
  subst hsW
  rw [show j + 1 + 1 = j + 2 from rfl]
  set n : ℝ := ((j + 2 : ℕ) : ℝ)
  set m : ℝ := ((j + 1 : ℕ) : ℝ)
  set L := layerErr g (δ + (s ^ 2)⁻¹ ^ 2) d τ s
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have he : 0 ≤ δ + (s ^ 2)⁻¹ ^ 2 := by positivity
  set c : ℝ := 3 * (j + 1 : ℕ) * 2 ^ (3 * (j + 1))
  have hc : 0 ≤ c := by positivity
  have T1 : n ^ 3 * (3 * 2) ^ (2 * (j + 2)) * (Cb / s * g) ^ 3 ≤
      n ^ 3 * (3 * 2) ^ (2 * (j + 2)) * Cb ^ 3 * L := by
    have a := at_s3 hg he hd hτ hs (a := 3) (by norm_num)
    have e : (Cb / s * g) ^ 3 = Cb ^ 3 * (g ^ 3 * s⁻¹ ^ 3) := by ring
    rw [e, show n ^ 3 * (3 * 2) ^ (2 * (j + 2)) * Cb ^ 3 * L =
      n ^ 3 * (3 * 2) ^ (2 * (j + 2)) * (Cb ^ 3 * L) by ring]
    gcongr
  have T2 : n * (n * (c * Ua)) * (Cb / s * g) ^ 2 ≤ n ^ 2 * c * Cb ^ 2 * (Cu * (1 + cq)) * L := by
    have a := t_Ua hg hδ hd hτ hs hq0 hq hcq hCu hUa
    have e : n * (n * (c * Ua)) * (Cb / s * g) ^ 2 =
        n ^ 2 * c * Cb ^ 2 * (Ua * (g ^ 2 / s ^ 2)) := by
      ring
    rw [e, mul_assoc (n ^ 2 * c * Cb ^ 2)]
    gcongr
  have T3 : ε * (m ^ 2 * g ^ 2) ≤ m ^ 2 * (Cε * (3 + cq)) * L := by
    have a := t_eps hg hδ hd hτ hs hq0 hq hcq hCε hε
    rw [show ε * (m ^ 2 * g ^ 2) = m ^ 2 * (ε * g ^ 2) by ring, mul_assoc (m ^ 2)]
    gcongr
  have T4 : (σ1 + σ2) * m ^ 2 * τ ^ 2 ≤ m ^ 2 * (2 * Cσ) * L := by
    have a := t_tau hg hδ hd hτ hs hq0 hq hcq hCσ h1 h2
    rw [show (σ1 + σ2) * m ^ 2 * τ ^ 2 = m ^ 2 * ((σ1 + σ2) * τ ^ 2) by ring, mul_assoc (m ^ 2)]
    gcongr
  have T5 : n * (3 * 2) ^ (2 * (j + 2)) * (Ua ^ 2 * g) ≤
      n * (3 * 2) ^ (2 * (j + 2)) * (2 * Cu ^ 2 * (1 + cq ^ 2)) * L := by
    have a := t_Ua2 hg hδ hd hτ hs hq0 hq hcq hUa0 hUa
    rw [mul_assoc (n * (3 * 2) ^ (2 * (j + 2)))]
    gcongr
  have T6 : n * (Cm * ((δ + (s ^ 2)⁻¹ ^ 2) * τ + (δ + (s ^ 2)⁻¹ ^ 2) ^ 2 * g +
      (δ + (s ^ 2)⁻¹ ^ 2) * q * g / s ^ 2 + (s ^ 2)⁻¹ ^ 2 * g)) ≤ n * (Cm * (3 + cq)) * L := by
    have a := t_wm hg hδ hd hτ hs hq0 hq hcq hCm
    rw [mul_assoc n]
    gcongr
  have T7 : n ^ 2 * (D * g / (2 * s ^ 2)) ^ 2 * g +
      j * (D * g / (2 * s ^ 2)) * (D * n ^ 2 * g ^ 2) / s ^ 2 ≤ n ^ 2 * CD ^ 2 * (1 + j) * L :=
    t_scal hg hδ hd hτ hs hD hDC j
  have hK : layerK j cq CD Cb Cu Cm Cε Cσ * L = n ^ 3 * (3 * 2) ^ (2 * (j + 2)) * Cb ^ 3 * L +
      n ^ 2 * c * Cb ^ 2 * (Cu * (1 + cq)) * L + m ^ 2 * (Cε * (3 + cq)) * L +
      m ^ 2 * (2 * Cσ) * L + n * (3 * 2) ^ (2 * (j + 2)) * (2 * Cu ^ 2 * (1 + cq ^ 2)) * L +
      n * (Cm * (3 + cq)) * L + n ^ 2 * CD ^ 2 * (1 + j) * L := by
    simp only [layerK, n, m, c]; ring
  rw [hK]
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add T1 T2) T3) T4) T5)
    T6) T7

end BlockBand.Transmission.Generator
