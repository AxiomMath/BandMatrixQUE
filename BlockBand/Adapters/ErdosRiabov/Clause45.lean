module

public import BlockBand.Adapters.ErdosRiabov.Clause23
public import BlockBand.Adapters.ErdosRiabov.Convolution

/-!
# Clauses (iv), (v) for the polynomial control

The Erdős–Riabov estimates (2.23)–(2.25) for the control
`Υ_η(x,y) = (ℓη)⁻¹(1 + d(x,y)/ℓ)^{-D}`, without a `log N` loss. Deterministic, on the native
cycle `Fin N`, `1 ≤ W ≤ N`. Heights `0 < η₁ ≤ η₂ ≤ C₀`, `C₀ ≥ 1`, `D ≥ 6`. With
`l = ℓ(η₂) ≤ L₀ = ℓ(η₁)`, `s = D/2`, `c = √C₀`:
* (2.23) pointwise product, constant one (estimate (P));
* (2.24) square-root convolution with constant `K_C = 2(c+1)(2^s + 4^s)` (estimate (C));
* (2.25) weighted convolution, both choices `ηᵢ ∈ {η₁, η₂}`, constant
  `K_W = 2(c+1)(2^s c + 4^s)` (estimate (W); the choice `ηᵢ = η₂` reduces to `ηᵢ = η₁`
  because `F_l ≤ F_{L₀}`).
Uniform in `N, W, η₁, η₂, x, y`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov

open BlockBand.External
open scoped BigOperators

/-- Amplitude identity `√((lη)⁻¹ v⁻¹) l = η⁻¹ √(lη v⁻¹)`. -/
theorem sqrt_amp_identity {l η v : ℝ} (hl : 0 < l) (hη : 0 < η) (hv : 0 < v) :
    Real.sqrt ((l * η)⁻¹ * v⁻¹) * l = 1 / η * Real.sqrt (l * η * v⁻¹) := by
  calc Real.sqrt ((l * η)⁻¹ * v⁻¹) * l = Real.sqrt ((l * η)⁻¹ * v⁻¹) * Real.sqrt (l ^ 2) := by
        rw [Real.sqrt_sq hl.le]
    _ = Real.sqrt ((l * η)⁻¹ * v⁻¹ * l ^ 2) := (Real.sqrt_mul (by positivity) _).symm
    _ = Real.sqrt ((1 / η) ^ 2 * (l * η * v⁻¹)) := by congr 1; field_simp
    _ = Real.sqrt ((1 / η) ^ 2) * Real.sqrt (l * η * v⁻¹) := Real.sqrt_mul (by positivity) _
    _ = 1 / η * Real.sqrt (l * η * v⁻¹) := by rw [Real.sqrt_sq (by positivity)]

/-- `√(Υ_{η}(x,a) Υ_{η'}(a,y)) = √((ℓη)⁻¹(ℓ'η')⁻¹) F_ℓ(d(x,a)) F_{ℓ'}(d(a,y))`, `s = D/2`. -/
theorem sqrt_control_mul {N W : ℕ} (hN : 0 < N) (hW : 0 < W) (D : ℝ) {η η' : ℝ} (hη : 0 < η)
    (hη' : 0 < η') (x a y : Fin N) :
    Real.sqrt (Internal.Contracts.Inputs.polynomialControl N W D η x a *
        Internal.Contracts.Inputs.polynomialControl N W D η' a y) =
      Real.sqrt ((ErdosRiabov.localizationLength N W η * η)⁻¹ *
          (ErdosRiabov.localizationLength N W η' * η')⁻¹) *
        (decayF (D / 2) (ErdosRiabov.localizationLength N W η)
            (ErdosRiabov.cyclicDistance N x a) *
          decayF (D / 2) (ErdosRiabov.localizationLength N W η')
            (ErdosRiabov.cyclicDistance N a y)) := by
  have hl := loc_pos hN hW hη
  have hl' := loc_pos hN hW hη'
  rw [polynomialControl_eq hN hW D hη, polynomialControl_eq hN hW D hη',
    decayF_sq hl (Nat.cast_nonneg _), decayF_sq hl' (Nat.cast_nonneg _)]
  have h1 := decayF_pos (s := D / 2) hl (Nat.cast_nonneg (ErdosRiabov.cyclicDistance N x a))
  have h2 := decayF_pos (s := D / 2) hl' (Nat.cast_nonneg (ErdosRiabov.cyclicDistance N a y))
  rw [show (ErdosRiabov.localizationLength N W η * η)⁻¹ *
        decayF (D / 2) (ErdosRiabov.localizationLength N W η)
          (ErdosRiabov.cyclicDistance N x a) ^ 2 *
      ((ErdosRiabov.localizationLength N W η' * η')⁻¹ *
        decayF (D / 2) (ErdosRiabov.localizationLength N W η')
          (ErdosRiabov.cyclicDistance N a y) ^ 2) =
      ((ErdosRiabov.localizationLength N W η * η)⁻¹ *
        (ErdosRiabov.localizationLength N W η' * η')⁻¹) *
      (decayF (D / 2) (ErdosRiabov.localizationLength N W η)
          (ErdosRiabov.cyclicDistance N x a) *
        decayF (D / 2) (ErdosRiabov.localizationLength N W η')
          (ErdosRiabov.cyclicDistance N a y)) ^ 2 by ring]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- `√(u Υ_η(x,y)) = √(u (ℓη)⁻¹) F_ℓ(d(x,y))` for `u ≥ 0`. -/
theorem sqrt_mul_control {N W : ℕ} (hN : 0 < N) (hW : 0 < W) (D : ℝ) {η u : ℝ} (hη : 0 < η)
    (hu : 0 ≤ u) (x y : Fin N) :
    Real.sqrt (u * Internal.Contracts.Inputs.polynomialControl N W D η x y) =
      Real.sqrt (u * (ErdosRiabov.localizationLength N W η * η)⁻¹) *
        decayF (D / 2) (ErdosRiabov.localizationLength N W η)
          (ErdosRiabov.cyclicDistance N x y) := by
  have hl := loc_pos hN hW hη
  rw [polynomialControl_eq hN hW D hη, decayF_sq hl (Nat.cast_nonneg _), ← mul_assoc,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (decayF_pos hl (Nat.cast_nonneg _)).le]

/-- Clause (iv), pointwise (ER (2.23), estimate (P)). -/
theorem clause4_pointwise {N W : ℕ} (hN : 0 < N) (hW : 0 < W) {D : ℝ} (hD : 0 ≤ D)
    {η₁ η₂ : ℝ} (h₁ : 0 < η₁) (h : η₁ ≤ η₂) (x y a : Fin N) :
    Internal.Contracts.Inputs.polynomialControl N W D η₂ x a *
        Internal.Contracts.Inputs.polynomialControl N W D η₁ a y ≤
      (ErdosRiabov.localizationLength N W η₂ * η₂)⁻¹ *
        Internal.Contracts.Inputs.polynomialControl N W D η₁ x y := by
  have h₂ : 0 < η₂ := h₁.trans_le h
  have hl₁ := loc_pos hN hW h₁
  have hl₂ := loc_pos hN hW h₂
  rw [polynomialControl_eq hN hW D h₁, polynomialControl_eq hN hW D h₂,
    polynomialControl_eq hN hW D h₁]
  have hP := decayF_mul_le hD hl₂ (loc_antitone N W h₁ h)
    (Nat.cast_nonneg (ErdosRiabov.cyclicDistance N x a))
    (Nat.cast_nonneg (ErdosRiabov.cyclicDistance N a y))
  have htri : (ErdosRiabov.cyclicDistance N x y : ℝ) ≤
      ErdosRiabov.cyclicDistance N x a + ErdosRiabov.cyclicDistance N a y := by
    exact_mod_cast cyclicDistance_triangle N x a y
  have hA := decayF_anti hD hl₁ (Nat.cast_nonneg _) htri
  have : 0 < (ErdosRiabov.localizationLength N W η₂ * η₂)⁻¹ := by positivity
  have : 0 < (ErdosRiabov.localizationLength N W η₁ * η₁)⁻¹ := by positivity
  calc (ErdosRiabov.localizationLength N W η₂ * η₂)⁻¹ *
        decayF D (ErdosRiabov.localizationLength N W η₂) (ErdosRiabov.cyclicDistance N x a) *
      ((ErdosRiabov.localizationLength N W η₁ * η₁)⁻¹ *
        decayF D (ErdosRiabov.localizationLength N W η₁) (ErdosRiabov.cyclicDistance N a y))
      = (ErdosRiabov.localizationLength N W η₂ * η₂)⁻¹ *
        ((ErdosRiabov.localizationLength N W η₁ * η₁)⁻¹ *
          (decayF D (ErdosRiabov.localizationLength N W η₂) (ErdosRiabov.cyclicDistance N x a) *
            decayF D (ErdosRiabov.localizationLength N W η₁)
              (ErdosRiabov.cyclicDistance N a y))) := by ring
    _ ≤ (ErdosRiabov.localizationLength N W η₂ * η₂)⁻¹ *
        ((ErdosRiabov.localizationLength N W η₁ * η₁)⁻¹ *
          decayF D (ErdosRiabov.localizationLength N W η₁)
            (ErdosRiabov.cyclicDistance N x y)) := by
        gcongr
        exact hP.trans hA

/-- The constant `K_C` of (C). -/
def constC (C₀ D : ℝ) : ℝ := 2 * (Real.sqrt C₀ + 1) * (2 ^ (D / 2) + 4 ^ (D / 2))

/-- The constant `K_W` of (W). -/
def constW (C₀ D : ℝ) : ℝ :=
  2 * (Real.sqrt C₀ + 1) * (2 ^ (D / 2) * Real.sqrt C₀ + 4 ^ (D / 2))

/-- Clause (iv), square-root convolution (ER (2.24), estimate (C)). -/
theorem clause4_sqrt {N W : ℕ} (hN : 0 < N) (hW : 0 < W) {D : ℝ} (hD : 6 ≤ D) {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) {η₁ η₂ : ℝ} (h₁ : 0 < η₁) (h : η₁ ≤ η₂) (h₂C : η₂ ≤ C₀) (x y : Fin N) :
    ∑ a, Real.sqrt (Internal.Contracts.Inputs.polynomialControl N W D η₂ x a *
        Internal.Contracts.Inputs.polynomialControl N W D η₁ a y) ≤
      constC C₀ D / η₂ * Real.sqrt (ErdosRiabov.localizationLength N W η₂ * η₂ *
        Internal.Contracts.Inputs.polynomialControl N W D η₁ x y) := by
  have h₂ : 0 < η₂ := h₁.trans_le h
  set l := ErdosRiabov.localizationLength N W η₂
  set L₀ := ErdosRiabov.localizationLength N W η₁
  have hl : 0 < l := loc_pos hN hW h₂
  have hL₀ : 0 < L₀ := loc_pos hN hW h₁
  have hlL : l ≤ L₀ := loc_antitone N W h₁ h
  have hsC : 0 < Real.sqrt C₀ := Real.sqrt_pos.2 (by linarith)
  have hc : 1 ≤ Real.sqrt C₀ * l := by
    have := inv_sqrt_le_loc hN hW hC₀ h₂ h₂C
    rw [div_le_iff₀ hsC] at this; linarith
  have hconv := convolution_C (N := N) (s := D / 2) (by linarith) hl hlL hc x y
  have hamp := sqrt_amp_identity hl h₂ (mul_pos hL₀ h₁)
  set F := decayF (D / 2) L₀ (ErdosRiabov.cyclicDistance N x y)
  have hF : 0 < F := decayF_pos hL₀ (Nat.cast_nonneg _)
  rw [sqrt_mul_control hN hW D h₁ (by positivity)]
  calc ∑ a, Real.sqrt (Internal.Contracts.Inputs.polynomialControl N W D η₂ x a *
        Internal.Contracts.Inputs.polynomialControl N W D η₁ a y)
      = Real.sqrt ((l * η₂)⁻¹ * (L₀ * η₁)⁻¹) * ∑ a : Fin N,
          decayF (D / 2) l (ErdosRiabov.cyclicDistance N x a) *
            decayF (D / 2) L₀ (ErdosRiabov.cyclicDistance N a y) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => sqrt_control_mul hN hW D h₂ h₁ x a y
    _ ≤ Real.sqrt ((l * η₂)⁻¹ * (L₀ * η₁)⁻¹) * (constC C₀ D * l * F) := by
        gcongr; exact hconv
    _ = constC C₀ D * (Real.sqrt ((l * η₂)⁻¹ * (L₀ * η₁)⁻¹) * l) * F := by ring
    _ = constC C₀ D / η₂ * (Real.sqrt (l * η₂ * (L₀ * η₁)⁻¹) * F) := by
        rw [hamp]; ring

/-- The weight of ER (2.25). -/
theorem weight_bounds {N W : ℕ} (hN : 0 < N) (hW : 0 < W) (hWN : W ≤ N) {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) {η₁ η₂ : ℝ} (h₁ : 0 < η₁) (h : η₁ ≤ η₂) (h₂C : η₂ ≤ C₀) (x a : Fin N) :
    let L₀ := ErdosRiabov.localizationLength N W η₁
    let l := ErdosRiabov.localizationLength N W η₂
    let w := min ((ErdosRiabov.cyclicDistance N a x : ℝ) + W) L₀ / L₀
    0 ≤ w ∧ w ≤ 1 ∧
      w ≤ Real.sqrt C₀ * (l / L₀) * (1 + (ErdosRiabov.cyclicDistance N x a : ℝ) / l) := by
  intro L₀ l w
  have h₂ : 0 < η₂ := h₁.trans_le h
  have hl : 0 < l := loc_pos hN hW h₂
  have hL₀ : 0 < L₀ := loc_pos hN hW h₁
  have hd0 : (0 : ℝ) ≤ ErdosRiabov.cyclicDistance N a x := Nat.cast_nonneg _
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have h1C : 1 ≤ Real.sqrt C₀ := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hC₀
  have hWl : (W : ℝ) ≤ Real.sqrt C₀ * l := W_le_sqrt_mul_loc hWN hC₀ h₂ h₂C
  refine ⟨div_nonneg (le_min (by positivity) hL₀.le) hL₀.le,
    (div_le_one hL₀).2 (min_le_right _ _), ?_⟩
  rw [ErdosRiabov.cyclicDistance_comm N x a]
  calc w ≤ ((ErdosRiabov.cyclicDistance N a x : ℝ) + W) / L₀ :=
        div_le_div_of_nonneg_right (min_le_left _ _) hL₀.le
    _ ≤ Real.sqrt C₀ * (l + ErdosRiabov.cyclicDistance N a x) / L₀ := by
        apply div_le_div_of_nonneg_right _ hL₀.le
        nlinarith
    _ = Real.sqrt C₀ * (l / L₀) * (1 + (ErdosRiabov.cyclicDistance N a x : ℝ) / l) := by
        field_simp

/-- Clause (v), weighted convolution (ER (2.25), estimate (W)), for both `ηᵢ ∈ {η₁, η₂}`. -/
theorem clause5_bound {N W : ℕ} (hN : 0 < N) (hW : 0 < W) (hWN : W ≤ N) {D : ℝ} (hD : 6 ≤ D)
    {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {η₁ η₂ : ℝ} (h₁ : 0 < η₁) (h : η₁ ≤ η₂) (h₂C : η₂ ≤ C₀)
    (ηi : ℝ) (hi : ηi = η₁ ∨ ηi = η₂) (x y : Fin N) :
    (∑ a, (min ((ErdosRiabov.cyclicDistance N a x : ℝ) + W)
          (ErdosRiabov.localizationLength N W η₁) / ErdosRiabov.localizationLength N W η₁) *
        Real.sqrt (Internal.Contracts.Inputs.polynomialControl N W D η₂ x a *
          Internal.Contracts.Inputs.polynomialControl N W D ηi a y)) ≤
      constW C₀ D / η₂ *
        (ErdosRiabov.localizationLength N W η₂ / ErdosRiabov.localizationLength N W η₁) *
        Real.sqrt ((ErdosRiabov.localizationLength N W η₂ * η₂) /
          (ErdosRiabov.localizationLength N W ηi * ηi)) *
        Real.sqrt (ErdosRiabov.localizationLength N W η₁ * η₁ *
          Internal.Contracts.Inputs.polynomialControl N W D η₁ x y) := by
  have h₂ : 0 < η₂ := h₁.trans_le h
  have hi0 : 0 < ηi := by rcases hi with hi | hi <;> rw [hi] <;> assumption
  set l := ErdosRiabov.localizationLength N W η₂
  set L₀ := ErdosRiabov.localizationLength N W η₁
  set hh := ErdosRiabov.localizationLength N W ηi
  have hl : 0 < l := loc_pos hN hW h₂
  have hL₀ : 0 < L₀ := loc_pos hN hW h₁
  have hh0 : 0 < hh := loc_pos hN hW hi0
  have hlL : l ≤ L₀ := loc_antitone N W h₁ h
  have hhL : hh ≤ L₀ := by
    rcases hi with hi | hi
    · simp only [hh, L₀, hi, le_rfl]
    · simp only [hh, hi]; exact hlL
  have hsC : 0 < Real.sqrt C₀ := Real.sqrt_pos.2 (by linarith)
  have h1C : 1 ≤ Real.sqrt C₀ := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hC₀
  have hc : 1 ≤ Real.sqrt C₀ * l := by
    have := inv_sqrt_le_loc hN hW hC₀ h₂ h₂C
    rw [div_le_iff₀ hsC] at this; linarith
  set w : Fin N → ℝ := fun a =>
    min ((ErdosRiabov.cyclicDistance N a x : ℝ) + W) L₀ / L₀ with hw_def
  have hwb := fun a => weight_bounds hN hW hWN hC₀ h₁ h h₂C x a
  have hconv := convolution_W (N := N) (s := D / 2) (by linarith) hl hlL h1C hc x y w
    (fun a => (hwb a).1) (fun a => (hwb a).2.1) (fun a => (hwb a).2.2)
  have hamp := sqrt_amp_identity hl h₂ (mul_pos hh0 hi0)
  set F := decayF (D / 2) L₀ (ErdosRiabov.cyclicDistance N x y)
  have hF : 0 < F := decayF_pos hL₀ (Nat.cast_nonneg _)
  have hlast : Real.sqrt (L₀ * η₁ *
      Internal.Contracts.Inputs.polynomialControl N W D η₁ x y) = F := by
    rw [sqrt_mul_control hN hW D h₁ (by positivity), mul_inv_cancel₀ (by positivity),
      Real.sqrt_one, one_mul]
  rw [hlast]
  calc (∑ a, w a * Real.sqrt (Internal.Contracts.Inputs.polynomialControl N W D η₂ x a *
          Internal.Contracts.Inputs.polynomialControl N W D ηi a y))
      = Real.sqrt ((l * η₂)⁻¹ * (hh * ηi)⁻¹) * ∑ a : Fin N, w a *
          decayF (D / 2) l (ErdosRiabov.cyclicDistance N x a) *
            decayF (D / 2) hh (ErdosRiabov.cyclicDistance N a y) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [sqrt_control_mul hN hW D h₂ hi0 x a y]; ring
    _ ≤ Real.sqrt ((l * η₂)⁻¹ * (hh * ηi)⁻¹) * ∑ a : Fin N, w a *
          decayF (D / 2) l (ErdosRiabov.cyclicDistance N x a) *
            decayF (D / 2) L₀ (ErdosRiabov.cyclicDistance N a y) := by
        gcongr with a
        · have := (hwb a).1
          have := decayF_pos (s := D / 2) hl (Nat.cast_nonneg (ErdosRiabov.cyclicDistance N x a))
          positivity
        · exact decayF_mono_scale (by linarith) hh0 hhL (Nat.cast_nonneg _)
    _ ≤ Real.sqrt ((l * η₂)⁻¹ * (hh * ηi)⁻¹) * (constW C₀ D * (l ^ 2 / L₀) * F) := by
        gcongr; exact hconv
    _ = constW C₀ D * (l / L₀) * (Real.sqrt ((l * η₂)⁻¹ * (hh * ηi)⁻¹) * l) * F := by
        field_simp
    _ = constW C₀ D / η₂ * (l / L₀) * Real.sqrt ((l * η₂) / (hh * ηi)) * F := by
        rw [hamp, div_eq_mul_inv (l * η₂)]; ring

end BlockBand.Adapters.ErdosRiabov
