module

public import BlockBand.Adapters.ErdosRiabov.PolynomialControl
public import BlockBand.Adapters.ErdosRiabov.DecayKernel

/-!
# Clauses (ii) and (iii) of Erdős–Riabov admissibility for the polynomial control

For the polynomial control `Υ_η(x,y) = (ℓη)⁻¹ (1 + d(x,y)/ℓ)^{-D}` on the cyclic ring, this
file proves the pointwise maximum, row-sum, polynomial floor and delocalized bounds of
clause (ii) of Erdős–Riabov Definition 2.4, and the monotonicity in `η` of clause (iii).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov

open BlockBand.External
open scoped BigOperators

/-- The polynomial control written with the decay kernel `F`. -/
theorem polynomialControl_eq {N W : ℕ} (hN : 0 < N) (hW : 0 < W) (D : ℝ) {η : ℝ} (hη : 0 < η)
    (x y : Fin N) :
    Internal.Contracts.Inputs.polynomialControl N W D η x y =
      (ErdosRiabov.localizationLength N W η * η)⁻¹ *
        decayF D (ErdosRiabov.localizationLength N W η)
          (ErdosRiabov.cyclicDistance N x y) := by
  unfold Internal.Contracts.Inputs.polynomialControl
  rw [decayF_eq_rpow_neg (loc_pos hN hW hη) (Nat.cast_nonneg _)]

theorem polynomialControl_pos {N W : ℕ} (hN : 0 < N) (hW : 0 < W) (D : ℝ) {η : ℝ} (hη : 0 < η)
    (x y : Fin N) : 0 < Internal.Contracts.Inputs.polynomialControl N W D η x y := by
  rw [polynomialControl_eq hN hW D hη]
  have := loc_pos hN hW hη
  exact mul_pos (inv_pos.2 (by positivity)) (decayF_pos this (Nat.cast_nonneg _))

theorem polynomialControl_symm (N W : ℕ) (D η : ℝ) (x y : Fin N) :
    Internal.Contracts.Inputs.polynomialControl N W D η x y =
      Internal.Contracts.Inputs.polynomialControl N W D η y x := by
  unfold Internal.Contracts.Inputs.polynomialControl
  rw [ErdosRiabov.cyclicDistance_comm]

/-- Clause (ii), pointwise maximum. -/
theorem polynomialControl_le_max {N W : ℕ} (hN : 0 < N) (hW : 0 < W) {D : ℝ} (hD : 0 ≤ D)
    {η : ℝ} (hη : 0 < η) (x y : Fin N) :
    Internal.Contracts.Inputs.polynomialControl N W D η x y ≤
      (ErdosRiabov.localizationLength N W η * η)⁻¹ := by
  rw [polynomialControl_eq hN hW D hη]
  have hl := loc_pos hN hW hη
  have : 0 < (ErdosRiabov.localizationLength N W η * η)⁻¹ := by positivity
  calc _ ≤ (ErdosRiabov.localizationLength N W η * η)⁻¹ * 1 := by
        gcongr; exact decayF_le_one hD hl (Nat.cast_nonneg _)
    _ = _ := mul_one _

/-- Clause (ii), row sum (the row-sum bound with exponent `σ = D ≥ 2`). -/
theorem polynomialControl_rowSum_le {N W : ℕ} (hN : 0 < N) (hW : 0 < W) {D : ℝ} (hD : 2 ≤ D)
    {C₀ η : ℝ} (hC₀ : 1 ≤ C₀) (hη : 0 < η) (hηC : η ≤ C₀) (x : Fin N) :
    ∑ a, Internal.Contracts.Inputs.polynomialControl N W D η x a ≤
      2 * (Real.sqrt C₀ + 1) / η := by
  set l := ErdosRiabov.localizationLength N W η with hl_def
  have hl : 0 < l := loc_pos hN hW hη
  have hlow : 1 / Real.sqrt C₀ ≤ l := inv_sqrt_le_loc hN hW hC₀ hη hηC
  have hsC : 0 < Real.sqrt C₀ := Real.sqrt_pos.2 (by linarith)
  have h1 : 1 ≤ Real.sqrt C₀ * l := by
    rw [div_le_iff₀ hsC] at hlow; linarith
  calc ∑ a, Internal.Contracts.Inputs.polynomialControl N W D η x a
        = (l * η)⁻¹ * ∑ a, decayF D l (ErdosRiabov.cyclicDistance N x a) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => polynomialControl_eq hN hW D hη x a
    _ ≤ (l * η)⁻¹ * ∑ a : Fin N, ((1 + (ErdosRiabov.cyclicDistance N x a : ℝ) / l) ^ 2)⁻¹ := by
          gcongr with a
          exact decayF_le_inv_sq hD hl (Nat.cast_nonneg _)
    _ ≤ (l * η)⁻¹ * (2 * (1 + l)) := by gcongr; exact sum_inv_sq_le l hl x
    _ ≤ (l * η)⁻¹ * (2 * ((Real.sqrt C₀ + 1) * l)) := by gcongr; nlinarith
    _ = 2 * (Real.sqrt C₀ + 1) / η := by field_simp

/-- `t ≤ 4^t` for `t ≥ 0`. -/
theorem le_four_rpow {t : ℝ} (ht : 0 ≤ t) : t ≤ (4 : ℝ) ^ t := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have hlog : 1 < Real.log 4 := by
    have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have := Real.add_one_le_exp (Real.log 4 * t)
  nlinarith

/-- The floor exponent of clause (ii), `D' = (1 + 2C₀)(D + 1)/2`. -/
def floorExponent (C₀ D : ℝ) : ℝ := (1 + 2 * C₀) * (D + 1) / 2

theorem floorExponent_pos {C₀ D : ℝ} (hC₀ : 1 ≤ C₀) (hD : 0 ≤ D) : 0 < floorExponent C₀ D := by
  unfold floorExponent; nlinarith

/-- Clause (ii), polynomial floor: `N^{-2D'} ≤ Υ_η(x,y)` for every `D'' ≥ D'`, `N ≥ 4`. -/
theorem rpow_floor_le_polynomialControl {N W : ℕ} (hN : 4 ≤ N) (hW : 0 < W) {D : ℝ}
    (hD : 0 ≤ D) {C₀ η : ℝ} (hC₀ : 1 ≤ C₀) (hη : 0 < η) (hηC : η ≤ C₀) {D'' : ℝ}
    (hD'' : floorExponent C₀ D ≤ D'') (x y : Fin N) :
    Real.rpow (N : ℝ) (-2 * D'') ≤ Internal.Contracts.Inputs.polynomialControl N W D η x y := by
  have hN0 : 0 < N := by omega
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  set l := ErdosRiabov.localizationLength N W η
  have hl : 0 < l := loc_pos hN0 hW hη
  have hlow : 1 / Real.sqrt C₀ ≤ l := inv_sqrt_le_loc hN0 hW hC₀ hη hηC
  have hsC : 0 < Real.sqrt C₀ := Real.sqrt_pos.2 (by linarith)
  have hsCle : Real.sqrt C₀ ≤ C₀ := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  set d : ℝ := (ErdosRiabov.cyclicDistance N x y : ℝ)
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hdN : d ≤ N := by
    have := two_mul_cyclicDistance_le N x y
    have : (ErdosRiabov.cyclicDistance N x y : ℝ) ≤ N := by exact_mod_cast (by omega)
    exact this
  -- `ℓη ≤ N C₀` and `1 + d/ℓ ≤ 2 N C₀`
  have hlη : l * η ≤ N * C₀ := mul_le_mul (loc_le_N N W η) hηC hη.le (by linarith)
  have hbase : 1 + d / l ≤ 2 * N * C₀ := by
    have : d / l ≤ d * Real.sqrt C₀ := by
      rw [div_le_iff₀ hl]
      rw [div_le_iff₀ hsC] at hlow
      nlinarith
    nlinarith
  set M : ℝ := 2 * N * C₀
  have hM1 : 1 ≤ M := by nlinarith
  -- Υ ≥ (M^(D+1))⁻¹
  have hY : (M ^ (D + 1))⁻¹ ≤ Internal.Contracts.Inputs.polynomialControl N W D η x y := by
    rw [polynomialControl_eq hN0 hW D hη]
    unfold decayF
    have hb : 1 ≤ 1 + d / l := one_le_base hl hd0
    rw [Real.rpow_add (by linarith), Real.rpow_one, ← mul_inv]
    apply inv_anti₀ (by positivity)
    rw [mul_comm (M ^ D) M]
    apply mul_le_mul (by nlinarith) (Real.rpow_le_rpow (by linarith) hbase hD) (by positivity)
      (by positivity)
  -- `M ≤ N^(1 + 2C₀)` since `2C₀ ≤ 4^(2C₀) ≤ N^(2C₀)`
  have hMN : M ≤ (N : ℝ) ^ (1 + 2 * C₀) := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
    have h4 : (4 : ℝ) ^ (2 * C₀) ≤ (N : ℝ) ^ (2 * C₀) :=
      Real.rpow_le_rpow (by norm_num) hNr (by linarith)
    have := le_four_rpow (show (0 : ℝ) ≤ 2 * C₀ by linarith)
    show 2 * N * C₀ ≤ _
    nlinarith
  have hpow : M ^ (D + 1) ≤ (N : ℝ) ^ (2 * floorExponent C₀ D) := by
    calc M ^ (D + 1) ≤ ((N : ℝ) ^ (1 + 2 * C₀)) ^ (D + 1) :=
          Real.rpow_le_rpow (by linarith) hMN (by linarith)
      _ = (N : ℝ) ^ (2 * floorExponent C₀ D) := by
          rw [← Real.rpow_mul (by linarith)]; unfold floorExponent; ring_nf
  calc Real.rpow (N : ℝ) (-2 * D'') ≤ (N : ℝ) ^ (-(2 * floorExponent C₀ D)) := by
        show (N : ℝ) ^ (-2 * D'') ≤ _
        exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    _ = ((N : ℝ) ^ (2 * floorExponent C₀ D))⁻¹ := Real.rpow_neg (by linarith) _
    _ ≤ (M ^ (D + 1))⁻¹ := inv_anti₀ (by positivity) hpow
    _ ≤ _ := hY

/-- Clause (ii), delocalized two-sided comparison: if `η ≤ (W/N)²` then
`(3/2)^{-D} (Nη)⁻¹ ≤ Υ_η ≤ (Nη)⁻¹`. -/
theorem polynomialControl_deloc {N W : ℕ} (hN : 0 < N) (hW : 0 < W) {D : ℝ} (hD : 0 ≤ D)
    {η : ℝ} (hη : 0 < η) (hsmall : η ≤ ((W : ℝ) / (N : ℝ)) ^ 2) (x y : Fin N) :
    ((3 / 2 : ℝ) ^ D)⁻¹ * (1 / ((N : ℝ) * η)) ≤
        Internal.Contracts.Inputs.polynomialControl N W D η x y ∧
      Internal.Contracts.Inputs.polynomialControl N W D η x y ≤ 1 / ((N : ℝ) * η) := by
  have hl := loc_eq_N hN hη hsmall
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [polynomialControl_eq hN hW D hη, hl]
  have hd0 : (0 : ℝ) ≤ ErdosRiabov.cyclicDistance N x y := Nat.cast_nonneg _
  have hdN : 2 * (ErdosRiabov.cyclicDistance N x y : ℝ) ≤ N := by
    exact_mod_cast two_mul_cyclicDistance_le N x y
  constructor
  · rw [mul_comm, one_div]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    unfold decayF
    apply inv_anti₀ (Real.rpow_pos_of_pos (by linarith [one_le_base hNr hd0]) _)
    apply Real.rpow_le_rpow (by linarith [one_le_base hNr hd0]) _ hD
    have : (ErdosRiabov.cyclicDistance N x y : ℝ) / N ≤ 1 / 2 := by
      rw [div_le_iff₀ hNr]; linarith
    linarith
  · rw [one_div]
    calc _ ≤ ((N : ℝ) * η)⁻¹ * 1 := by
          gcongr; exact decayF_le_one hD hNr hd0
      _ = _ := mul_one _

/-- Clause (iii): `Υ_{η₂} ≤ Υ_{η₁}` for `0 < η₁ ≤ η₂` (ER (2.22) with constant one). -/
theorem polynomialControl_anti {N W : ℕ} (hN : 0 < N) (hW : 0 < W) {D : ℝ} (hD : 0 ≤ D)
    {η₁ η₂ : ℝ} (h₁ : 0 < η₁) (h : η₁ ≤ η₂) (x y : Fin N) :
    Internal.Contracts.Inputs.polynomialControl N W D η₂ x y ≤
      Internal.Contracts.Inputs.polynomialControl N W D η₁ x y := by
  have h₂ : 0 < η₂ := h₁.trans_le h
  rw [polynomialControl_eq hN hW D h₁, polynomialControl_eq hN hW D h₂]
  have hl₁ := loc_pos hN hW h₁
  have hl₂ := loc_pos hN hW h₂
  apply mul_le_mul (inv_anti₀ (by positivity) (loc_mul_mono N W h₁ h))
    (decayF_mono_scale hD hl₂ (loc_antitone N W h₁ h) (Nat.cast_nonneg _))
    (decayF_pos hl₂ (Nat.cast_nonneg _)).le (by positivity)

end BlockBand.Adapters.ErdosRiabov
