module

public import BlockBand.LocalWindow.ProofPartTwoLargeCentrePoint
public import BlockBand.LocalWindow.ProofPartTwoFinalGrid

/-!
# The error budget of the large-`ρ` branch

Real arithmetic for the assembly of the large-`ρ` branch (`partTwoLargeRho_holds`) of part (ii)
of the physical local-window lemma.

## Main results

* `natCast_two_mul_sub_one`, `compressVar_bounds` (`s/2 ≤ s' ≤ s`), `compressRadius_bounds`
  (`1/(2W) ≤ h ≤ W^{-1+β}`), `resLip_anti` (the resolvent Lipschitz constant decreases in `s`).
* **`nS_mul_compressTol_le`**: `(C_c(2W)^β + 1) · 2N^{ε'}N^{-1/2} ≤ 4(2C_c + 1)W^{β+ε'-1/2}`,
  `N = 2W - 1`.
* **`largeRho_budget_le`**: the bound of `largeRho_point_le` is at most
  `n_S tol + 2Lh + (14 + 5/(sv₀²))X` once every small term is at most `X ≤ 1`.
* `largeRho_Q_le`, `largeRho_P_le`, `largeRhoZ`, **`largeRho_rho_conds`**: if
  `|ρ| ≥ Z Kb⁴` (`Kb ≥ W ≥ 1` the block-form constant, `X² W = 1`), every condition of
  `largeRho_point_le` on `|ρ|` and every small term is satisfied.
* **`largeRho_final_le`**: the budget is at most `C W^{-1/2+ε}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open BlockBand.LocalWindow.ProofETH

section Scales

variable {p : Parameters}

/-- `2W - 1` as a real number. -/
theorem natCast_two_mul_sub_one (p : Parameters) :
    ((2 * p.W - 1 : ℕ) : ℝ) = 2 * (p.W : ℝ) - 1 := by
  have h : 1 ≤ 2 * p.W := by have := p.W_pos; omega
  rw [Nat.cast_sub h]; push_cast; ring

/-- The compressed variance `s' = s(1 - 1/(2W))` lies in `[s/2, s]`. -/
theorem compressVar_bounds {s : ℝ} (hs : 0 ≤ s) :
    s / 2 ≤ compressVar p s ∧ compressVar p s ≤ s := by
  unfold compressVar
  have hW : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have h1 : 1 / (2 * (p.W : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h2 : 0 ≤ 1 / (2 * (p.W : ℝ)) := by positivity
  constructor <;> nlinarith

/-- The compressed window radius `h = (2W - 1)^{-1+β}` satisfies `1/(2W) ≤ h ≤ W^{-1+β}`. -/
theorem compressRadius_bounds {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    1 / (2 * (p.W : ℝ)) ≤ compressRadius p β ∧ compressRadius p β ≤ (p.W : ℝ) ^ (-1 + β) := by
  unfold compressRadius
  rw [natCast_two_mul_sub_one]
  have hW : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hN : (1 : ℝ) ≤ 2 * p.W - 1 := by linarith
  constructor
  · have h1 : (2 * (p.W : ℝ) - 1) ^ (-1 : ℝ) ≤ (2 * (p.W : ℝ) - 1) ^ (-1 + β) :=
      Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    rw [Real.rpow_neg_one] at h1
    refine le_trans ?_ h1
    rw [one_div]; exact inv_anti₀ (by linarith) (by linarith)
  · exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)

/-- The resolvent Lipschitz constant `resLip s v₀` decreases in `s > 0`. -/
theorem resLip_anti {s₁ s₂ v₀ : ℝ} (hs₁ : 0 < s₁) (h : s₁ ≤ s₂) (hv : 0 < v₀) :
    resLip s₂ v₀ ≤ resLip s₁ v₀ := by
  have hs₂ : 0 < s₂ := hs₁.trans_le h
  have e : ∀ s : ℝ, 0 < s → resLip s v₀ = (1 + (2 * s * v₀ ^ 2)⁻¹) * ((s * v₀)⁻¹) ^ 2 := by
    intro s hs
    unfold resLip rootLip
    have : s * (2 * s ^ 2 * v₀ ^ 2)⁻¹ = (2 * s * v₀ ^ 2)⁻¹ := by
      field_simp
    rw [this]
  rw [e s₂ hs₂, e s₁ hs₁]
  have h1 : (2 * s₂ * v₀ ^ 2)⁻¹ ≤ (2 * s₁ * v₀ ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (by gcongr)
  have h2 : (s₂ * v₀)⁻¹ ≤ (s₁ * v₀)⁻¹ := inv_anti₀ (by positivity) (by gcongr)
  have h3 : ((s₂ * v₀)⁻¹) ^ 2 ≤ ((s₁ * v₀)⁻¹) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  exact mul_le_mul (by linarith) h3 (by positivity) (by positivity)

/-- **The count times the compressed ETH tolerance**:
`(C_c(2W)^β + 1) · 2N^{ε'}N^{-1/2} ≤ 4(2C_c + 1)W^{β+ε'-1/2}`, `N = 2W - 1`. -/
theorem nS_mul_compressTol_le {Cc β ε' : ℝ} (hCc : 0 ≤ Cc) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hε0 : 0 ≤ ε') (hε1 : ε' ≤ 1) :
    (Cc * ((2 * p.W : ℕ) : ℝ) ^ β + 1) * compressTol p ε' ≤
      4 * (2 * Cc + 1) * (p.W : ℝ) ^ (β + ε' - 1 / 2) := by
  unfold compressTol
  rw [natCast_two_mul_sub_one]
  set W : ℝ := (p.W : ℝ) with hWdef
  have hW : (1 : ℝ) ≤ W := by rw [hWdef]; exact_mod_cast p.W_pos
  have hW0 : 0 < W := by linarith
  have hd : ((2 * p.W : ℕ) : ℝ) = 2 * W := by rw [hWdef]; push_cast; ring
  rw [hd]
  have h2 : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (2 * W) ^ x ≤ 2 * W ^ x := by
    intro x hx0 hx1
    rw [Real.mul_rpow (by norm_num) hW0.le]
    have : (2 : ℝ) ^ x ≤ 2 := by
      calc (2 : ℝ) ^ x ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hx1
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hW0.le _)
  have hNW : W ≤ 2 * W - 1 := by linarith
  have hN2 : 2 * W - 1 ≤ 2 * W := by linarith
  have hN0 : 0 < 2 * W - 1 := by linarith
  have a1 : (2 * W - 1) ^ ε' ≤ 2 * W ^ ε' :=
    (Real.rpow_le_rpow hN0.le hN2 hε0).trans (h2 ε' hε0 hε1)
  have a2 : (2 * W - 1) ^ (-(1 : ℝ) / 2) ≤ W ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hW0 hNW (by norm_num)
  have a3 : Cc * (2 * W) ^ β + 1 ≤ (2 * Cc + 1) * W ^ β := by
    have h1 : 1 ≤ W ^ β := Real.one_le_rpow hW hβ0
    have := mul_le_mul_of_nonneg_left (h2 β hβ0 hβ1) hCc
    nlinarith
  have hWb : 0 ≤ W ^ β := Real.rpow_nonneg hW0.le _
  have hWe : 0 ≤ W ^ ε' := Real.rpow_nonneg hW0.le _
  have hWh : 0 ≤ W ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hW0.le _
  have a4 : 2 * ((2 * W - 1) ^ ε' * (2 * W - 1) ^ (-(1 : ℝ) / 2)) ≤
      2 * ((2 * W ^ ε') * W ^ (-(1 : ℝ) / 2)) := by
    have := mul_le_mul a1 a2 (Real.rpow_nonneg hN0.le _) (by positivity)
    linarith
  have hpos : 0 ≤ Cc * (2 * W) ^ β + 1 := by
    have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * W) β
    positivity
  calc (Cc * (2 * W) ^ β + 1) * (2 * ((2 * W - 1) ^ ε' * (2 * W - 1) ^ (-(1 : ℝ) / 2)))
      ≤ ((2 * Cc + 1) * W ^ β) * (2 * ((2 * W ^ ε') * W ^ (-(1 : ℝ) / 2))) :=
        mul_le_mul a3 a4 (by positivity) (by positivity)
    _ = 4 * (2 * Cc + 1) * (W ^ β * W ^ ε' * W ^ (-(1 : ℝ) / 2)) := by ring
    _ = 4 * (2 * Cc + 1) * W ^ (β + ε' - 1 / 2) := by
        rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; ring_nf

end Scales

/-!
## The error budget at one exact eigenvector
-/

/-- **The error budget** of `largeRho_point_le`: if the operator error `r_g`, the block-form terms
`4K²/|ρ|` (relative to `h/4`), `q = 2K/|ρ|`, the observable change `δ_J` and the centre error are
all at most `X ≤ 1`, the bound is at most `n_S tol + 2Lh + (14 + 5/(sv₀²))X`. -/
theorem largeRho_budget_le {nS tol L h rg K ρa δJ s' v₀ s cce X : ℝ} (hX0 : 0 ≤ X) (hX1 : X ≤ 1)
    (hh : 0 < h) (hL : 0 ≤ L) (hrg0 : 0 ≤ rg) (hrg : rg ≤ X * h / 4) (hK0 : 0 ≤ K)
    (hρ : 0 < ρa) (hKK : 4 * K ^ 2 / ρa ≤ X * h / 4) (hq : 2 * K / ρa ≤ X) (hδ0 : 0 ≤ δJ)
    (hδ : δJ ≤ X) (hcce : cce ≤ X) (hs : 0 < s) (hv : 0 < v₀) (hs' : s / 2 ≤ s') :
    nS * tol + (L * (3 * h / 2 + rg) + δJ / (s' * v₀ ^ 2) + cce) +
        2 * ((rg + 4 * K ^ 2 / ρa) / (h / 2)) +
        (1 + 1 / (s * v₀ ^ 2)) * ((rg + 4 * K ^ 2 / ρa) / (h / 2)) ^ 2 +
        2 * K / ρa * (2 + 2 * K / ρa) + 2 * (2 * K / ρa) * (1 / (s * v₀ ^ 2)) +
        (δJ + 4 * (2 * K / ρa)) ≤
      nS * tol + 2 * L * h + (14 + 5 / (s * v₀ ^ 2)) * X := by
  set c := 1 / (s * v₀ ^ 2) with hc
  have hc0 : 0 < c := by positivity
  set τ := (rg + 4 * K ^ 2 / ρa) / (h / 2) with hτ
  have hKK0 : 0 ≤ 4 * K ^ 2 / ρa := by positivity
  have hτ0 : 0 ≤ τ := by positivity
  have hτX : τ ≤ X := by
    rw [hτ, div_le_iff₀ (by positivity)]; linarith
  have hτ2 : τ ^ 2 ≤ X := by nlinarith
  set q := 2 * K / ρa with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hqq : q * (2 + q) ≤ 3 * X := by nlinarith
  have hLh : L * (3 * h / 2 + rg) ≤ 2 * L * h := by
    have : rg ≤ h / 2 := by nlinarith
    nlinarith
  have hδs : δJ / (s' * v₀ ^ 2) ≤ 2 * c * X := by
    have hsv : s * v₀ ^ 2 / 2 ≤ s' * v₀ ^ 2 := by nlinarith [sq_nonneg v₀]
    have h1 : δJ / (s' * v₀ ^ 2) ≤ δJ / (s * v₀ ^ 2 / 2) :=
      div_le_div_of_nonneg_left hδ0 (by positivity) hsv
    have h2 : δJ / (s * v₀ ^ 2 / 2) = 2 * c * δJ := by rw [hc]; field_simp
    rw [h2] at h1
    nlinarith
  have hcτ : (1 + c) * τ ^ 2 ≤ (1 + c) * X := mul_le_mul_of_nonneg_left hτ2 (by positivity)
  have hqc : 2 * q * c ≤ 2 * c * X := by nlinarith
  have e5 : (5 : ℝ) / (s * v₀ ^ 2) = 5 * c := by rw [hc]; ring
  rw [e5]
  nlinarith

/-- The centre-error denominator: for `s' ≥ s/2`, `nM ≤ K_b`, `K_b ≥ 1`, `|x| ≤ 1` and
`2(1 + 1/v₀) ≤ |ρ|`, `(1 + nM/(s'v₀))³/(|ρ| - (|x| + 1/v₀)) ≤ 2(1 + 2/(sv₀))³K_b³/|ρ|`. -/
theorem largeRho_Q_le {s s' v₀ nM Kb ρa x : ℝ} (hs : 0 < s) (hs' : s / 2 ≤ s') (hv : 0 < v₀)
    (hnM0 : 0 ≤ nM) (hnM : nM ≤ Kb) (hKb : 1 ≤ Kb) (hx : |x| ≤ 1)
    (hρ : 2 * (1 + 1 / v₀) ≤ ρa) :
    (1 + nM / (s' * v₀)) ^ 3 / (ρa - (|x| + 1 / v₀)) ≤
      2 * ((1 + 2 / (s * v₀)) ^ 3 * Kb ^ 3) / ρa := by
  have hs'0 : 0 < s' := by linarith
  have hv1 : 0 < 1 / v₀ := by positivity
  have hρ0 : 0 < ρa := by linarith
  have hden : ρa / 2 ≤ ρa - (|x| + 1 / v₀) := by linarith
  have hnum1 : nM / (s' * v₀) ≤ 2 * Kb / (s * v₀) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : nM * (s * v₀) ≤ Kb * (s * v₀) := mul_le_mul_of_nonneg_right hnM (by positivity)
    have h2 : Kb * (s * v₀) ≤ 2 * Kb * (s' * v₀) := by
      have := mul_le_mul_of_nonneg_left (show s ≤ 2 * s' by linarith)
        (by positivity : (0 : ℝ) ≤ Kb * v₀)
      linarith
    linarith
  have hnum2 : 1 + 2 * Kb / (s * v₀) ≤ (1 + 2 / (s * v₀)) * Kb := by
    have : 2 * Kb / (s * v₀) = 2 / (s * v₀) * Kb := by ring
    rw [this]; nlinarith
  have hnum : (1 + nM / (s' * v₀)) ^ 3 ≤ (1 + 2 / (s * v₀)) ^ 3 * Kb ^ 3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 3
  calc (1 + nM / (s' * v₀)) ^ 3 / (ρa - (|x| + 1 / v₀))
      ≤ (1 + 2 / (s * v₀)) ^ 3 * Kb ^ 3 / (ρa / 2) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 2 * ((1 + 2 / (s * v₀)) ^ 3 * Kb ^ 3) / ρa := by field_simp

/-- The prefactor of the centre error: for `s/2 ≤ s'`,
`2s/(s'v₀) · (1 + 4/(v₀²(s'v₀)²)) ≤ (4/v₀)(1 + 16/(s²v₀⁴))`. -/
theorem largeRho_P_le {s s' v₀ : ℝ} (hs : 0 < s) (hs' : s / 2 ≤ s') (hv : 0 < v₀) :
    2 * s / (s' * v₀) * (1 + 4 / (v₀ ^ 2 * (s' * v₀) ^ 2)) ≤
      4 / v₀ * (1 + 16 / (s ^ 2 * v₀ ^ 4)) := by
  have hs'0 : 0 < s' := by linarith
  have h1 : 2 * s / (s' * v₀) ≤ 4 / v₀ := by
    rw [div_le_div_iff₀ (by positivity) hv]; nlinarith
  have h2 : 4 / (v₀ ^ 2 * (s' * v₀) ^ 2) ≤ 16 / (s ^ 2 * v₀ ^ 4) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : s ^ 2 ≤ 4 * s' ^ 2 := by nlinarith
    have h4 : 0 ≤ v₀ ^ 4 := by positivity
    have e : 16 * (v₀ ^ 2 * (s' * v₀) ^ 2) = 4 * (4 * s' ^ 2) * v₀ ^ 4 := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_right h3 h4
    nlinarith
  exact mul_le_mul h1 (by linarith) (by positivity) (by positivity)

/-- The constant `Z` of the large-`ρ` threshold `|ρ| ≥ Z K_b⁴`. -/
def largeRhoZ (s v₀ K₀ : ℝ) : ℝ :=
  2 * (4 / v₀ * (1 + 16 / (s ^ 2 * v₀ ^ 4))) * (2 * (1 + 2 / (s * v₀)) ^ 3) +
    8 * (1 + 2 / (s * v₀)) ^ 3 / v₀ + 8 * (1 + 2 / (s * v₀)) ^ 3 / (s * v₀ ^ 3) +
    4 * (3 * K₀ + 4) + 2 * (1 + 1 / v₀) + 40

/-- **The conditions on `|ρ|`** (taking `H` large makes both errors
`O(W^{-10})`): if `|ρ| ≥ Z K_b⁴` with `1 ≤ W ≤ K_b`, `X > 0`, `X²W = 1`, `nM ≤ K_b`,
`s/2 ≤ s'` and `|x| ≤ 1`, then `4K_b, 6K_b ≤ |ρ|`, `|x| + 1/v₀ < |ρ|`, the two smallness
conditions of `pairCentre_compress_close`, the centre error is at most `X`, `2K_b/|ρ| ≤ X`,
`4K_b²/|ρ| ≤ X(1/(2W))/4` and `√(2W)(3K₀K_b² + 4K_b)/|ρ| ≤ X/2`. -/
theorem largeRho_rho_conds {W X Kb ρa s s' v₀ nM x K₀ : ℝ} (hW : 1 ≤ W) (hWK : W ≤ Kb)
    (hX0 : 0 < X) (hXW : X ^ 2 * W = 1) (hs : 0 < s) (hs' : s / 2 ≤ s') (hv : 0 < v₀)
    (hnM0 : 0 ≤ nM) (hnM : nM ≤ Kb) (hx : |x| ≤ 1) (hK₀ : 0 ≤ K₀)
    (hρ : largeRhoZ s v₀ K₀ * Kb ^ 4 ≤ ρa) :
    4 * Kb ≤ ρa ∧ 6 * Kb ≤ ρa ∧ |x| + 1 / v₀ < ρa ∧
      4 * ((1 + nM / (s' * v₀)) ^ 3 / (ρa - (|x| + 1 / v₀))) ≤ v₀ ∧
      2 * ((1 + nM / (s' * v₀)) ^ 3 / (ρa - (|x| + 1 / v₀))) ≤ s' * v₀ ^ 3 ∧
      2 * s / (s' * v₀) * (1 + 4 / (v₀ ^ 2 * (s' * v₀) ^ 2)) *
          ((1 + nM / (s' * v₀)) ^ 3 / (ρa - (|x| + 1 / v₀))) ≤ X ∧
      2 * Kb / ρa ≤ X ∧ 4 * Kb ^ 2 / ρa ≤ X * (1 / (2 * W)) / 4 ∧
      Real.sqrt (2 * W) * ((3 * K₀ * Kb ^ 2 + 4 * Kb) / ρa) ≤ X / 2 := by
  have hKb : 1 ≤ Kb := hW.trans hWK
  have hW0 : 0 < W := by linarith
  have hKb0 : 0 < Kb := by linarith
  have hv1 : 0 < 1 / v₀ := by positivity
  have hsv2 : 0 < 2 / (s * v₀) := by positivity
  set Y₀ := (1 + 2 / (s * v₀)) ^ 3 with hY₀
  set P := 4 / v₀ * (1 + 16 / (s ^ 2 * v₀ ^ 4)) with hP
  have hY₀0 : 1 ≤ Y₀ := one_le_pow₀ (by linarith)
  have hP0 : 0 ≤ P := by positivity
  have t1 : 0 ≤ 2 * P * (2 * Y₀) := by positivity
  have t2 : 0 ≤ 8 * Y₀ / v₀ := by positivity
  have t3 : 0 ≤ 8 * Y₀ / (s * v₀ ^ 3) := by positivity
  have t4 : 0 ≤ 4 * (3 * K₀ + 4) := by positivity
  have t5 : 0 ≤ 2 * (1 + 1 / v₀) := by positivity
  have hZe : largeRhoZ s v₀ K₀ = 2 * P * (2 * Y₀) + 8 * Y₀ / v₀ + 8 * Y₀ / (s * v₀ ^ 3) +
      4 * (3 * K₀ + 4) + 2 * (1 + 1 / v₀) + 40 := rfl
  set Z := largeRhoZ s v₀ K₀ with hZ
  have hZ1 : 2 * P * (2 * Y₀) ≤ Z := by rw [hZe]; linarith
  have hZ2 : 8 * Y₀ / v₀ ≤ Z := by rw [hZe]; linarith
  have hZ3 : 8 * Y₀ / (s * v₀ ^ 3) ≤ Z := by rw [hZe]; linarith
  have hZ4 : 4 * (3 * K₀ + 4) ≤ Z := by rw [hZe]; linarith
  have hZ5 : 2 * (1 + 1 / v₀) ≤ Z := by rw [hZe]; linarith
  have hZ0 : 40 ≤ Z := by rw [hZe]; linarith
  have hK4 : 1 ≤ Kb ^ 4 := one_le_pow₀ hKb
  have hK34 : Kb ^ 3 ≤ Kb ^ 4 := pow_le_pow_right₀ hKb (by norm_num)
  have hK13 : Kb ≤ Kb ^ 3 := by
    calc Kb = Kb ^ 1 := (pow_one Kb).symm
      _ ≤ Kb ^ 3 := pow_le_pow_right₀ hKb (by norm_num)
  have hK23 : Kb ^ 2 ≤ Kb ^ 3 := pow_le_pow_right₀ hKb (by norm_num)
  have hZK : Z ≤ Z * Kb ^ 4 := le_mul_of_one_le_right (by linarith) hK4
  have hρZ : Z ≤ ρa := hZK.trans hρ
  have hρ0 : 0 < ρa := by linarith
  -- `X K_b ≥ 1`
  have hX2 : X ^ 2 ≤ 1 := by
    have := le_mul_of_one_le_right (sq_nonneg X) hW
    linarith
  have hX1 : X ≤ 1 := (pow_le_one_iff_of_nonneg hX0.le two_ne_zero).mp hX2
  have hXX : X ^ 2 ≤ X := by rw [sq]; exact mul_le_of_le_one_left hX0.le hX1
  have hXW1 : 1 ≤ X * W := by
    have := mul_le_mul_of_nonneg_right hXX hW0.le
    linarith
  have hXK : 1 ≤ X * Kb := hXW1.trans (mul_le_mul_of_nonneg_left hWK hX0.le)
  have hZK3 : 0 ≤ Z * Kb ^ 3 := by positivity
  have hXρ : Z * Kb ^ 3 ≤ X * ρa := by
    have h1 : Z * Kb ^ 3 ≤ Z * Kb ^ 3 * (X * Kb) := le_mul_of_one_le_right hZK3 hXK
    have h2 : Z * Kb ^ 3 * (X * Kb) = X * (Z * Kb ^ 4) := by ring
    have h3 : X * (Z * Kb ^ 4) ≤ X * ρa := mul_le_mul_of_nonneg_left hρ hX0.le
    linarith
  have hρ2 : 2 * (1 + 1 / v₀) ≤ ρa := by linarith
  have hQ := largeRho_Q_le hs hs' hv hnM0 hnM hKb hx hρ2
  set Q := (1 + nM / (s' * v₀)) ^ 3 / (ρa - (|x| + 1 / v₀)) with hQdef
  have hQ' : Q ≤ 2 * (Y₀ * Kb ^ 3) / ρa := hQ
  have hY3 : 0 ≤ Y₀ * Kb ^ 3 := by positivity
  have hxv : |x| + 1 / v₀ ≤ 1 + 1 / v₀ := by linarith
  have hKρ : Kb ^ 4 * 40 ≤ ρa := by
    have := mul_le_mul_of_nonneg_left hZ0 (by positivity : (0 : ℝ) ≤ Kb ^ 4)
    linarith [mul_comm Z (Kb ^ 4)]
  have hKb4 : Kb ≤ Kb ^ 4 := hK13.trans hK34
  refine ⟨by linarith, by linarith, by linarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `4Q ≤ v₀`
    have h2 : 8 * Y₀ / v₀ * Kb ^ 4 ≤ ρa :=
      (mul_le_mul_of_nonneg_right hZ2 (by positivity)).trans hρ
    have e : 8 * Y₀ / v₀ * Kb ^ 4 = (8 * Y₀ * Kb ^ 4) / v₀ := by ring
    rw [e, div_le_iff₀ hv] at h2
    have h4 : 8 * (Y₀ * Kb ^ 3) ≤ 8 * Y₀ * Kb ^ 4 := by
      have := mul_le_mul_of_nonneg_left hK34 (by positivity : (0 : ℝ) ≤ 8 * Y₀)
      linarith
    have h1 : 8 * (Y₀ * Kb ^ 3) ≤ v₀ * ρa := by linarith [mul_comm ρa v₀]
    have h3 : 2 * (Y₀ * Kb ^ 3) / ρa ≤ v₀ / 4 := by
      rw [div_le_iff₀ hρ0]; linarith
    linarith
  · -- `2Q ≤ s'v₀³`
    have h2 : 8 * Y₀ / (s * v₀ ^ 3) * Kb ^ 4 ≤ ρa :=
      (mul_le_mul_of_nonneg_right hZ3 (by positivity)).trans hρ
    have e : 8 * Y₀ / (s * v₀ ^ 3) * Kb ^ 4 = (8 * Y₀ * Kb ^ 4) / (s * v₀ ^ 3) := by ring
    rw [e, div_le_iff₀ (by positivity)] at h2
    have h4 : 8 * (Y₀ * Kb ^ 3) ≤ 8 * Y₀ * Kb ^ 4 := by
      have := mul_le_mul_of_nonneg_left hK34 (by positivity : (0 : ℝ) ≤ 8 * Y₀)
      linarith
    have h1 : 8 * (Y₀ * Kb ^ 3) ≤ s * v₀ ^ 3 * ρa := by linarith [mul_comm ρa (s * v₀ ^ 3)]
    have h3 : 2 * (Y₀ * Kb ^ 3) / ρa ≤ s * v₀ ^ 3 / 4 := by
      rw [div_le_iff₀ hρ0]; linarith
    have h5 : s * v₀ ^ 3 / 2 ≤ s' * v₀ ^ 3 := by
      have := mul_le_mul_of_nonneg_right hs' (by positivity : (0 : ℝ) ≤ v₀ ^ 3)
      linarith
    linarith
  · -- the centre error
    have hPl := largeRho_P_le hs hs' hv
    have hden : 0 < ρa - (|x| + 1 / v₀) := by linarith
    have hs'0 : 0 < s' := by linarith
    have hnv : 0 ≤ nM / (s' * v₀) := div_nonneg hnM0 (by positivity)
    have hQ0 : 0 ≤ Q := div_nonneg (pow_nonneg (by linarith) 3) hden.le
    have h1 : 2 * s / (s' * v₀) * (1 + 4 / (v₀ ^ 2 * (s' * v₀) ^ 2)) * Q ≤
        P * (2 * (Y₀ * Kb ^ 3) / ρa) := mul_le_mul hPl hQ' hQ0 hP0
    have h2 : P * (2 * (Y₀ * Kb ^ 3) / ρa) ≤ X := by
      rw [show P * (2 * (Y₀ * Kb ^ 3) / ρa) = (2 * P * Y₀ * Kb ^ 3) / ρa by ring,
        div_le_iff₀ hρ0]
      have h3 : 2 * P * Y₀ * Kb ^ 3 ≤ Z * Kb ^ 3 := by
        have := mul_le_mul_of_nonneg_right hZ1 (by positivity : (0 : ℝ) ≤ Kb ^ 3)
        have e2 : 2 * P * (2 * Y₀) * Kb ^ 3 = 2 * (2 * P * Y₀ * Kb ^ 3) := by ring
        have h4 : 0 ≤ 2 * P * Y₀ * Kb ^ 3 := by positivity
        linarith
      linarith
    linarith
  · rw [div_le_iff₀ hρ0]
    have : 2 * Kb ≤ Z * Kb ^ 3 := by
      have := mul_le_mul_of_nonneg_right hZ0 (by positivity : (0 : ℝ) ≤ Kb ^ 3)
      linarith
    linarith
  · rw [div_le_iff₀ hρ0]
    have e : X * (1 / (2 * W)) / 4 * ρa = X * ρa / (8 * W) := by field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have h1 : W * Kb ^ 2 ≤ Kb ^ 3 := by
      have := mul_le_mul_of_nonneg_right hWK (by positivity : (0 : ℝ) ≤ Kb ^ 2)
      linarith [show Kb * Kb ^ 2 = Kb ^ 3 by ring]
    have h2 : 32 * Kb ^ 3 ≤ Z * Kb ^ 3 := by
      have := mul_le_mul_of_nonneg_right hZ0 (by positivity : (0 : ℝ) ≤ Kb ^ 3)
      linarith
    have e2 : 4 * Kb ^ 2 * (8 * W) = 32 * (W * Kb ^ 2) := by ring
    linarith
  · have hsq : Real.sqrt (2 * W) ≤ 2 * W :=
      Real.sqrt_le_iff.mpr ⟨by positivity, by
        rw [sq]; exact le_mul_of_one_le_left (by positivity) (by linarith)⟩
    have h0 : 0 ≤ (3 * K₀ * Kb ^ 2 + 4 * Kb) / ρa := by positivity
    refine (mul_le_mul_of_nonneg_right hsq h0).trans ?_
    rw [mul_div_assoc', div_le_iff₀ hρ0]
    have a1 : W * Kb ^ 2 ≤ Kb ^ 3 := by
      have := mul_le_mul_of_nonneg_right hWK (by positivity : (0 : ℝ) ≤ Kb ^ 2)
      linarith [show Kb * Kb ^ 2 = Kb ^ 3 by ring]
    have a2 : W * Kb ≤ Kb ^ 3 := by
      have := mul_le_mul_of_nonneg_right hWK hKb0.le
      linarith [show Kb * Kb = Kb ^ 2 by ring]
    have a3 : 2 * W * (3 * K₀ * Kb ^ 2 + 4 * Kb) ≤ 2 * (3 * K₀ + 4) * Kb ^ 3 := by
      have b1 := mul_le_mul_of_nonneg_left a1 (by positivity : (0 : ℝ) ≤ 6 * K₀)
      have b2 := mul_le_mul_of_nonneg_left a2 (by norm_num : (0 : ℝ) ≤ 8)
      have e3 : 2 * W * (3 * K₀ * Kb ^ 2 + 4 * Kb) = 6 * K₀ * (W * Kb ^ 2) + 8 * (W * Kb) := by
        ring
      have e4 : 2 * (3 * K₀ + 4) * Kb ^ 3 = 6 * K₀ * Kb ^ 3 + 8 * Kb ^ 3 := by ring
      linarith
    have a4 : 4 * (3 * K₀ + 4) * Kb ^ 3 ≤ Z * Kb ^ 3 :=
      mul_le_mul_of_nonneg_right hZ4 (by positivity)
    have a5 : 0 ≤ (3 * K₀ + 4) * Kb ^ 3 := by positivity
    linarith

/-- **The final power of `W`**: with `X = W^{-1/2}`, `h ≤ W^{-1+β}`, `β ≤ 1/2`,
`β + ε' ≤ ε`, `0 ≤ L ≤ L̄`: `n_S tol + 2Lh + (14 + 5c)X ≤ (4(2C_c + 1) + 2L̄ + 14 + 5c)W^{-1/2+ε}`. -/
theorem largeRho_final_le {W h nStol L Lb c Cc β ε' ε : ℝ} (hW : 1 ≤ W) (hh0 : 0 ≤ h)
    (hh : h ≤ W ^ (-1 + β)) (hβ : β ≤ 1 / 2)
    (hn : nStol ≤ 4 * (2 * Cc + 1) * W ^ (β + ε' - 1 / 2)) (hβε : β + ε' ≤ ε) (hε : 0 ≤ ε)
    (hL0 : 0 ≤ L) (hL : L ≤ Lb) (hc : 0 ≤ c) (hCc : 0 ≤ Cc) :
    nStol + 2 * L * h + (14 + 5 * c) * W ^ (-(1 / 2) : ℝ) ≤
      (4 * (2 * Cc + 1) + 2 * Lb + 14 + 5 * c) * W ^ (-(1 / 2) + ε) := by
  have hW0 : 0 < W := by linarith
  set Y := W ^ (-(1 / 2) + ε) with hY
  have hY0 : 0 ≤ Y := Real.rpow_nonneg hW0.le _
  have a1 : W ^ (β + ε' - 1 / 2) ≤ Y := Real.rpow_le_rpow_of_exponent_le hW (by linarith)
  have a2 : W ^ (-1 + β) ≤ Y := Real.rpow_le_rpow_of_exponent_le hW (by linarith)
  have a3 : W ^ (-(1 / 2) : ℝ) ≤ Y := Real.rpow_le_rpow_of_exponent_le hW (by linarith)
  have b1 : nStol ≤ 4 * (2 * Cc + 1) * Y :=
    hn.trans (mul_le_mul_of_nonneg_left a1 (by positivity))
  have b2 : 2 * L * h ≤ 2 * Lb * Y := by
    have := mul_le_mul hL (hh.trans a2) hh0 (hL0.trans hL)
    nlinarith
  have b3 : (14 + 5 * c) * W ^ (-(1 / 2) : ℝ) ≤ (14 + 5 * c) * Y :=
    mul_le_mul_of_nonneg_left a3 (by positivity)
  nlinarith

/-!
## Powers of `W`
-/

/-- `(W^{-1/2})² W = 1`. -/
theorem rpow_neg_half_sq_mul {W : ℝ} (hW : 0 < W) : (W ^ (-(1 / 2) : ℝ)) ^ 2 * W = 1 := by
  have e : (W ^ (-(1 / 2) : ℝ)) ^ 2 = W⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le, ← Real.rpow_neg_one]; norm_num
  rw [e, inv_mul_cancel₀ hW.ne']

/-- **The regular-part scale** (`K = CW^{A₀}`): with `‖V‖ ≤ c + C_G`,
`‖C‖ ≤ c ≤ TW²`, `|x| ≤ 2`, `‖V‖ + ‖C‖²/W^{-(A₀+1)} + |x| ≤ (T + C_G + T² + 2)W^{A₀+5}`. -/
theorem regScale_le {W c CG T A₀ nV nC x : ℝ} (hW : 1 ≤ W) (hT : 0 ≤ T)
    (hc : c ≤ T * W ^ 2) (hCG : 0 ≤ CG) (hA₀ : 0 ≤ A₀) (hV : nV ≤ c + CG) (hC0 : 0 ≤ nC)
    (hC : nC ≤ c) (hx : |x| ≤ 2) :
    nV + nC ^ 2 / W ^ (-(A₀ + 1)) + |x| ≤ (T + CG + T ^ 2 + 2) * W ^ (A₀ + 5) := by
  have hW0 : 0 < W := by linarith
  set Y := W ^ (A₀ + 5) with hY
  have hY1 : 1 ≤ Y := Real.one_le_rpow hW (by linarith)
  have hW2 : W ^ 2 ≤ Y := by
    rw [hY, ← Real.rpow_natCast W 2]
    exact Real.rpow_le_rpow_of_exponent_le hW (by push_cast; linarith)
  have h1 : nC ^ 2 / W ^ (-(A₀ + 1)) ≤ T ^ 2 * Y := by
    rw [Real.rpow_neg hW0.le, div_inv_eq_mul]
    have e : Y = W ^ 4 * W ^ (A₀ + 1) := by
      rw [hY, ← Real.rpow_natCast W 4, ← Real.rpow_add hW0]; congr 1; push_cast; ring
    have h2 : nC ^ 2 ≤ (T * W ^ 2) ^ 2 := pow_le_pow_left₀ hC0 (hC.trans hc) 2
    rw [e]
    have h3 : 0 ≤ W ^ (A₀ + 1) := Real.rpow_nonneg hW0.le _
    calc nC ^ 2 * W ^ (A₀ + 1) ≤ (T * W ^ 2) ^ 2 * W ^ (A₀ + 1) :=
          mul_le_mul_of_nonneg_right h2 h3
      _ = T ^ 2 * (W ^ 4 * W ^ (A₀ + 1)) := by ring
  have h4 : c ≤ T * Y := hc.trans (mul_le_mul_of_nonneg_left hW2 hT)
  have h5 : CG ≤ CG * Y := le_mul_of_one_le_right hCG hY1
  have h6 : |x| ≤ 2 * Y := by linarith
  have e7 : (T + CG + T ^ 2 + 2) * Y = T * Y + CG * Y + T ^ 2 * Y + 2 * Y := by ring
  linarith

/-- **The large-`ρ` threshold**: from `|ρ| > W^{4(A₀+5)+1} - ‖C*φ‖²/W^{-A₀}`,
`‖C*φ‖² ≤ c² ≤ T²W⁴` and `Z_k κ₁⁴ + T² ≤ W`: `|ρ| ≥ Z_k (κ₁ W^{A₀+5})⁴`. -/
theorem rho_lower {W c T A₀ Zk κ₁ sq ρa : ℝ} (hW : 1 ≤ W) (hc0 : 0 ≤ c)
    (hc : c ≤ T * W ^ 2) (hA₀ : 0 ≤ A₀) (hsq : sq ≤ c ^ 2)
    (hWZ : Zk * κ₁ ^ 4 + T ^ 2 ≤ W)
    (hρ : W ^ (4 * (A₀ + 5) + 1) - sq / W ^ (-A₀) < ρa) :
    Zk * (κ₁ * W ^ (A₀ + 5)) ^ 4 ≤ ρa := by
  have hW0 : 0 < W := by linarith
  set Y := W ^ (4 * (A₀ + 5)) with hY
  have hY0 : 0 ≤ Y := Real.rpow_nonneg hW0.le _
  have e1 : W ^ (4 * (A₀ + 5) + 1) = W * Y := by
    rw [Real.rpow_add hW0, Real.rpow_one, mul_comm]
  have e2 : (W ^ (A₀ + 5)) ^ 4 = Y := by
    rw [hY, ← Real.rpow_natCast (W ^ (A₀ + 5)) 4, ← Real.rpow_mul hW0.le]; congr 1; push_cast
    ring
  have h1 : sq / W ^ (-A₀) ≤ T ^ 2 * Y := by
    rw [Real.rpow_neg hW0.le, div_inv_eq_mul]
    have h2 : c ^ 2 ≤ (T * W ^ 2) ^ 2 := pow_le_pow_left₀ hc0 hc 2
    have h3 : W ^ 4 * W ^ A₀ ≤ Y := by
      rw [hY, ← Real.rpow_natCast W 4, ← Real.rpow_add hW0]
      exact Real.rpow_le_rpow_of_exponent_le hW (by push_cast; linarith)
    have h4 : 0 ≤ W ^ A₀ := Real.rpow_nonneg hW0.le _
    calc sq * W ^ A₀ ≤ (T * W ^ 2) ^ 2 * W ^ A₀ :=
          mul_le_mul_of_nonneg_right (hsq.trans h2) h4
      _ = T ^ 2 * (W ^ 4 * W ^ A₀) := by ring
      _ ≤ T ^ 2 * Y := mul_le_mul_of_nonneg_left h3 (sq_nonneg T)
  rw [mul_pow, e2]
  rw [e1] at hρ
  have h5 : (Zk * κ₁ ^ 4 + T ^ 2) * Y ≤ W * Y := mul_le_mul_of_nonneg_right hWZ hY0
  have e3 : Zk * (κ₁ ^ 4 * Y) = (Zk * κ₁ ^ 4 + T ^ 2) * Y - T ^ 2 * Y := by ring
  linarith

/-- With `8W^{-1/2} ≤ 1`: `W^{-2} ≤ W^{-1/2} (1/(2W))/4`. -/
theorem rpow_neg_two_le {W : ℝ} (hW : 1 ≤ W) (h8 : 8 * W ^ (-(1 / 2) : ℝ) ≤ 1) :
    W ^ (-2 : ℝ) ≤ W ^ (-(1 / 2) : ℝ) * (1 / (2 * W)) / 4 := by
  have hW0 : 0 < W := by linarith
  have e : W ^ (-2 : ℝ) = W ^ (-(1 / 2) : ℝ) * W ^ (-(1 / 2) : ℝ) * W⁻¹ := by
    rw [← Real.rpow_add hW0, ← Real.rpow_neg_one, ← Real.rpow_add hW0]; norm_num
  rw [e]
  have hX0 : 0 ≤ W ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hW0.le _
  have hWi : 0 < W⁻¹ := inv_pos.mpr hW0
  have e2 : W ^ (-(1 / 2) : ℝ) * (1 / (2 * W)) / 4 = W ^ (-(1 / 2) : ℝ) * (1 / 8) * W⁻¹ := by
    field_simp; ring
  rw [e2]
  have h1 : W ^ (-(1 / 2) : ℝ) ≤ 1 / 8 := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hX0
  exact mul_le_mul_of_nonneg_right h2 hWi.le

/-- The class (b) operator-error term: `√N K_q r_g ≤ W^{-1/2}/2` for `N ≤ 2W`, `r_g ≤ W^{-2}`
and `4K_q W^{-1} ≤ 1`. -/
theorem sqrt_mul_rg_le {W N Kq rg : ℝ} (hW : 1 ≤ W) (hN : N ≤ 2 * W) (hKq : 0 ≤ Kq)
    (hrg0 : 0 ≤ rg) (hrg : rg ≤ W ^ (-2 : ℝ)) (hK : 4 * Kq * W ^ (-1 : ℝ) ≤ 1) :
    Real.sqrt N * Kq * rg ≤ W ^ (-(1 / 2) : ℝ) / 2 := by
  have hW0 : 0 < W := by linarith
  have h1 : Real.sqrt N ≤ 2 * W ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt N ≤ Real.sqrt (4 * W) := Real.sqrt_le_sqrt (by linarith)
      _ = 2 * Real.sqrt W := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have e : W ^ (1 / 2 : ℝ) * W ^ (-2 : ℝ) = W ^ (-1 : ℝ) * W ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; norm_num
  have hX := Real.rpow_nonneg hW0.le (-(1 / 2) : ℝ)
  have hWm := Real.rpow_nonneg hW0.le (-1 : ℝ)
  calc Real.sqrt N * Kq * rg ≤ (2 * W ^ (1 / 2 : ℝ)) * Kq * W ^ (-2 : ℝ) := by
        have := mul_le_mul_of_nonneg_right h1 hKq
        exact mul_le_mul this hrg hrg0 (by positivity)
    _ = 2 * Kq * (W ^ (-1 : ℝ) * W ^ (-(1 / 2) : ℝ)) := by rw [← e]; ring
    _ ≤ W ^ (-(1 / 2) : ℝ) / 2 := by
        have h2 := mul_le_mul_of_nonneg_right hK hX
        have e2 : 2 * Kq * (W ^ (-1 : ℝ) * W ^ (-(1 / 2) : ℝ)) =
            4 * Kq * W ^ (-1 : ℝ) * W ^ (-(1 / 2) : ℝ) / 2 := by ring
        rw [e2]; linarith

/-- The window-centre grid `intervalGrid δ (h/2)` has at most `6W` points (`δ ≤ 1/2`,
`h ≥ 1/(2W)`). -/
theorem centreGrid_card_le {W δ h : ℝ} (hW : 1 ≤ W) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hh : 1 / (2 * W) ≤ h) : ((intervalGrid δ (h / 2)).card : ℝ) ≤ 6 * W := by
  have hW0 : 0 < W := by linarith
  have hh0 : 0 < h := lt_of_lt_of_le (by positivity) hh
  refine (intervalGrid_card_le hδ0 (by positivity)).trans ?_
  have h1 : 1 ≤ 2 * W * h := by
    rw [div_le_iff₀ (by positivity)] at hh; linarith
  have h2 : 2 * δ / (h / 2) ≤ 4 * W := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end BlockBand.LocalWindow.ProofPartTwo
