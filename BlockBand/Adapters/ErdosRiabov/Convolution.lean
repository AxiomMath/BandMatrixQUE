module

public import BlockBand.Adapters.ErdosRiabov.PolynomialControl
public import BlockBand.Adapters.ErdosRiabov.DecayKernel

/-!
# Convolution estimates (C) and (W) on the `N`-cycle

Deterministic convolution bounds without a `log N` loss; sums over the cycle `Fin N` with
the periodic distance `d`. Scales `0 < l ≤ L₀` with `1 ≤ c l` (in the application `c = √C₀`),
exponent `s ≥ 3` (in the application `s = D/2`, `D ≥ 6`), `δ = d(x,y)`, and
`F_l(t) = (1 + t/l)^{-s}`. With `K_R = 2(c+1)`:
* (C) `Σ_a F_l(d(x,a)) F_{L₀}(d(a,y)) ≤ K_R (2^s + 4^s) l F_{L₀}(δ)`;
* (W) `Σ_a w(a) F_l(d(x,a)) F_{L₀}(d(a,y)) ≤ K_R (2^s c + 4^s) (l²/L₀) F_{L₀}(δ)` for any
  weight `0 ≤ w ≤ min 1 (c (l/L₀)(1 + d(x,a)/l))`.
Proof: if `δ ≤ L₀` then `F_{L₀}(δ) ≥ 2^{-s}` and (R) suffices; if
`δ > L₀` split pointwise on `d(a,y) ≥ δ/2`, using `F_{L₀}(δ/2) ≤ 2^s F_{L₀}(δ)` on one side
and `F_l(δ/2) ≤ (4l/L₀)^s F_{L₀}(δ)` with (R) at scale `L₀` on the other. Uniform in `N`,
`x`, `y`, `l`, `L₀`. No contract is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov

open BlockBand.External
open scoped BigOperators

/-- (R) at a scale `L ≥ 1/c`: `Σ_a (1 + d(x,a)/L)^{-2} ≤ 2(c+1) L`. -/
theorem sum_inv_sq_le_scale {N : ℕ} {c L : ℝ} (hL : 0 < L) (hc : 1 ≤ c * L) (x : Fin N) :
    ∑ a : Fin N, ((1 + (ErdosRiabov.cyclicDistance N x a : ℝ) / L) ^ 2)⁻¹ ≤
      2 * (c + 1) * L := by
  refine (sum_inv_sq_le L hL x).trans ?_
  nlinarith

/-- (R) for the kernel `F`, `s ≥ 2`. -/
theorem sum_decayF_le {N : ℕ} {s c L : ℝ} (hs : 2 ≤ s) (hL : 0 < L) (hc : 1 ≤ c * L)
    (x : Fin N) :
    ∑ a : Fin N, decayF s L (ErdosRiabov.cyclicDistance N x a) ≤ 2 * (c + 1) * L :=
  (Finset.sum_le_sum fun _ _ => decayF_le_inv_sq hs hL (Nat.cast_nonneg _)).trans
    (sum_inv_sq_le_scale hL hc x)

/-- (R) with the distance in the other order. -/
theorem sum_decayF_le' {N : ℕ} {s c L : ℝ} (hs : 2 ≤ s) (hL : 0 < L) (hc : 1 ≤ c * L)
    (y : Fin N) :
    ∑ a : Fin N, decayF s L (ErdosRiabov.cyclicDistance N a y) ≤ 2 * (c + 1) * L := by
  simp_rw [ErdosRiabov.cyclicDistance_comm N _ y]
  exact sum_decayF_le hs hL hc y

/-- The pointwise split behind the case `δ > L₀`. -/
theorem split_pointwise {N : ℕ} {s l L₀ : ℝ} (hs : 0 ≤ s) (hl : 0 < l) (hlL : l ≤ L₀)
    (x y a : Fin N) (hδ : L₀ < (ErdosRiabov.cyclicDistance N x y : ℝ)) (w : ℝ) (hw0 : 0 ≤ w)
    (hw1 : w ≤ 1) :
    w * decayF s l (ErdosRiabov.cyclicDistance N x a) *
        decayF s L₀ (ErdosRiabov.cyclicDistance N a y) ≤
      2 ^ s * decayF s L₀ (ErdosRiabov.cyclicDistance N x y) *
          (w * decayF s l (ErdosRiabov.cyclicDistance N x a)) +
        (4 * l / L₀) ^ s * decayF s L₀ (ErdosRiabov.cyclicDistance N x y) *
          decayF s L₀ (ErdosRiabov.cyclicDistance N a y) := by
  have hL₀ : 0 < L₀ := hl.trans_le hlL
  set δ : ℝ := (ErdosRiabov.cyclicDistance N x y : ℝ)
  set u : ℝ := (ErdosRiabov.cyclicDistance N x a : ℝ)
  set v : ℝ := (ErdosRiabov.cyclicDistance N a y : ℝ)
  have hu : 0 ≤ u := Nat.cast_nonneg _
  have hv : 0 ≤ v := Nat.cast_nonneg _
  have hδ0 : 0 ≤ δ := Nat.cast_nonneg _
  have htri : δ ≤ u + v := by
    simp only [δ, u, v]; exact_mod_cast cyclicDistance_triangle N x a y
  have hFl := decayF_pos (s := s) hl hu
  have hFL := decayF_pos (s := s) hL₀ hv
  have hFδ := decayF_pos (s := s) hL₀ hδ0
  have hA : 0 ≤ 2 ^ s * decayF s L₀ δ * (w * decayF s l u) := by positivity
  have hB : 0 ≤ (4 * l / L₀) ^ s * decayF s L₀ δ * decayF s L₀ v := by positivity
  rcases le_or_gt (δ / 2) v with h | h
  · have : decayF s L₀ v ≤ 2 ^ s * decayF s L₀ δ :=
      (decayF_anti hs hL₀ (by linarith) h).trans (decayF_half_le hs hL₀ hδ0)
    calc w * decayF s l u * decayF s L₀ v ≤ w * decayF s l u * (2 ^ s * decayF s L₀ δ) := by
          gcongr
      _ = 2 ^ s * decayF s L₀ δ * (w * decayF s l u) := by ring
      _ ≤ _ := le_add_of_nonneg_right hB
  · have hu2 : δ / 2 ≤ u := by linarith
    have : decayF s l u ≤ (4 * l / L₀) ^ s * decayF s L₀ δ :=
      (decayF_anti hs hl (by linarith) hu2).trans (decayF_transfer hs hl hlL hδ)
    calc w * decayF s l u * decayF s L₀ v ≤ 1 * ((4 * l / L₀) ^ s * decayF s L₀ δ) *
          decayF s L₀ v := by gcongr
      _ = (4 * l / L₀) ^ s * decayF s L₀ δ * decayF s L₀ v := by ring
      _ ≤ _ := le_add_of_nonneg_left hA

/-- `(4l/L₀)^s L₀ ≤ 4^s l²/L₀` for `s ≥ 2`, and `≤ 4^s l` for `s ≥ 1`. -/
theorem transfer_factor_le {s l L₀ : ℝ} (hs : 2 ≤ s) (hl : 0 < l) (hlL : l ≤ L₀) :
    (4 * l / L₀) ^ s * L₀ ≤ 4 ^ s * (l ^ 2 / L₀) ∧ (4 * l / L₀) ^ s * L₀ ≤ 4 ^ s * l := by
  have hL₀ : 0 < L₀ := hl.trans_le hlL
  have hr0 : 0 < l / L₀ := div_pos hl hL₀
  have hr1 : l / L₀ ≤ 1 := (div_le_one hL₀).2 hlL
  have e : (4 * l / L₀) ^ s = 4 ^ s * (l / L₀) ^ s := by
    rw [mul_div_assoc, Real.mul_rpow (by norm_num) hr0.le]
  have h2 : (l / L₀) ^ s ≤ (l / L₀) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hs
  have h1 : (l / L₀) ^ s ≤ (l / L₀) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
  rw [Real.rpow_two] at h2
  rw [Real.rpow_one] at h1
  have h4 : (0 : ℝ) < 4 ^ s := by positivity
  rw [e]
  constructor
  · calc 4 ^ s * (l / L₀) ^ s * L₀ ≤ 4 ^ s * (l / L₀) ^ 2 * L₀ := by gcongr
      _ = 4 ^ s * (l ^ 2 / L₀) := by field_simp
  · calc 4 ^ s * (l / L₀) ^ s * L₀ ≤ 4 ^ s * (l / L₀) * L₀ := by gcongr
      _ = 4 ^ s * l := by field_simp

/-- Estimate (C). -/
theorem convolution_C {N : ℕ} {s c l L₀ : ℝ} (hs : 3 ≤ s) (hl : 0 < l) (hlL : l ≤ L₀)
    (hc : 1 ≤ c * l) (x y : Fin N) :
    ∑ a : Fin N, decayF s l (ErdosRiabov.cyclicDistance N x a) *
        decayF s L₀ (ErdosRiabov.cyclicDistance N a y) ≤
      2 * (c + 1) * (2 ^ s + 4 ^ s) * l * decayF s L₀ (ErdosRiabov.cyclicDistance N x y) := by
  have hs0 : 0 ≤ s := by linarith
  have hL₀ : 0 < L₀ := hl.trans_le hlL
  have hc0 : 0 ≤ c := by nlinarith
  have hcL : 1 ≤ c * L₀ := by nlinarith
  set δ : ℝ := (ErdosRiabov.cyclicDistance N x y : ℝ)
  have hδ0 : 0 ≤ δ := Nat.cast_nonneg _
  have hFδ := decayF_pos (s := s) hL₀ hδ0
  have hR := sum_decayF_le (s := s) (by linarith) hl hc x
  have h2s : (0 : ℝ) < 2 ^ s := by positivity
  have h4s : (0 : ℝ) < 4 ^ s := by positivity
  rcases le_or_gt δ L₀ with hδ | hδ
  · have h1 := one_le_two_rpow_mul_decayF hs0 hL₀ hδ0 hδ
    calc ∑ a : Fin N, decayF s l (ErdosRiabov.cyclicDistance N x a) *
          decayF s L₀ (ErdosRiabov.cyclicDistance N a y)
          ≤ ∑ a : Fin N, decayF s l (ErdosRiabov.cyclicDistance N x a) := by
            apply Finset.sum_le_sum; intro a _
            have := decayF_pos (s := s) hl (Nat.cast_nonneg (ErdosRiabov.cyclicDistance N x a))
            calc _ ≤ decayF s l (ErdosRiabov.cyclicDistance N x a) * 1 := by
                  gcongr; exact decayF_le_one hs0 hL₀ (Nat.cast_nonneg _)
              _ = _ := mul_one _
      _ ≤ 2 * (c + 1) * l := hR
      _ ≤ 2 * (c + 1) * l * (2 ^ s * decayF s L₀ δ) := by
            have : 0 ≤ 2 * (c + 1) * l := by positivity
            nlinarith
      _ ≤ _ := by
            have : 0 ≤ 2 * (c + 1) * l * decayF s L₀ δ := by positivity
            nlinarith
  · have hpt := fun a : Fin N => split_pointwise hs0 hl hlL x y a hδ 1 zero_le_one le_rfl
    have hR' := sum_decayF_le' (s := s) (by linarith) hL₀ hcL y
    have hT := (transfer_factor_le (s := s) (by linarith) hl hlL).2
    calc ∑ a : Fin N, decayF s l (ErdosRiabov.cyclicDistance N x a) *
          decayF s L₀ (ErdosRiabov.cyclicDistance N a y)
          = ∑ a : Fin N, 1 * decayF s l (ErdosRiabov.cyclicDistance N x a) *
              decayF s L₀ (ErdosRiabov.cyclicDistance N a y) := by simp
      _ ≤ ∑ a : Fin N, (2 ^ s * decayF s L₀ δ *
            (1 * decayF s l (ErdosRiabov.cyclicDistance N x a)) +
            (4 * l / L₀) ^ s * decayF s L₀ δ *
              decayF s L₀ (ErdosRiabov.cyclicDistance N a y)) :=
            Finset.sum_le_sum fun a _ => hpt a
      _ = 2 ^ s * decayF s L₀ δ * ∑ a : Fin N, decayF s l (ErdosRiabov.cyclicDistance N x a) +
            (4 * l / L₀) ^ s * decayF s L₀ δ *
              ∑ a : Fin N, decayF s L₀ (ErdosRiabov.cyclicDistance N a y) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]; simp
      _ ≤ 2 ^ s * decayF s L₀ δ * (2 * (c + 1) * l) +
            (4 * l / L₀) ^ s * decayF s L₀ δ * (2 * (c + 1) * L₀) := by
            have : 0 ≤ (4 * l / L₀) ^ s := by positivity
            gcongr
      _ = 2 * (c + 1) * decayF s L₀ δ * (2 ^ s * l + (4 * l / L₀) ^ s * L₀) := by ring
      _ ≤ 2 * (c + 1) * decayF s L₀ δ * (2 ^ s * l + 4 ^ s * l) := by gcongr
      _ = _ := by ring

/-- Estimate (W), for the weight bounds `0 ≤ w ≤ 1` and `w ≤ c (l/L₀)(1 + d(x,a)/l)`. -/
theorem convolution_W {N : ℕ} {s c l L₀ : ℝ} (hs : 3 ≤ s) (hl : 0 < l) (hlL : l ≤ L₀)
    (hc1 : 1 ≤ c) (hc : 1 ≤ c * l) (x y : Fin N) (w : Fin N → ℝ) (hw0 : ∀ a, 0 ≤ w a)
    (hw1 : ∀ a, w a ≤ 1)
    (hw : ∀ a, w a ≤ c * (l / L₀) * (1 + (ErdosRiabov.cyclicDistance N x a : ℝ) / l)) :
    ∑ a : Fin N, w a * decayF s l (ErdosRiabov.cyclicDistance N x a) *
        decayF s L₀ (ErdosRiabov.cyclicDistance N a y) ≤
      2 * (c + 1) * (2 ^ s * c + 4 ^ s) * (l ^ 2 / L₀) *
        decayF s L₀ (ErdosRiabov.cyclicDistance N x y) := by
  have hs0 : 0 ≤ s := by linarith
  have hL₀ : 0 < L₀ := hl.trans_le hlL
  have hc0 : 0 ≤ c := by linarith
  have hcL : 1 ≤ c * L₀ := by nlinarith
  set δ : ℝ := (ErdosRiabov.cyclicDistance N x y : ℝ)
  have hδ0 : 0 ≤ δ := Nat.cast_nonneg _
  have hFδ := decayF_pos (s := s) hL₀ hδ0
  have h2s : (0 : ℝ) < 2 ^ s := by positivity
  have h4s : (0 : ℝ) < 4 ^ s := by positivity
  -- weighted (R): `Σ_a w F_l ≤ 2(c+1) c l²/L₀`
  have hWR : ∑ a : Fin N, w a * decayF s l (ErdosRiabov.cyclicDistance N x a) ≤
      2 * (c + 1) * c * (l ^ 2 / L₀) := by
    calc ∑ a : Fin N, w a * decayF s l (ErdosRiabov.cyclicDistance N x a)
        ≤ ∑ a : Fin N, c * (l / L₀) *
            ((1 + (ErdosRiabov.cyclicDistance N x a : ℝ) / l) ^ 2)⁻¹ := by
          apply Finset.sum_le_sum; intro a _
          have hF := decayF_pos (s := s) hl (Nat.cast_nonneg (ErdosRiabov.cyclicDistance N x a))
          calc w a * decayF s l (ErdosRiabov.cyclicDistance N x a)
              ≤ c * (l / L₀) * (1 + (ErdosRiabov.cyclicDistance N x a : ℝ) / l) *
                  decayF s l (ErdosRiabov.cyclicDistance N x a) := by gcongr; exact hw a
            _ = c * (l / L₀) * ((1 + (ErdosRiabov.cyclicDistance N x a : ℝ) / l) *
                  decayF s l (ErdosRiabov.cyclicDistance N x a)) := by ring
            _ ≤ _ := by
                gcongr; exact base_mul_decayF_le_inv_sq hs hl (Nat.cast_nonneg _)
      _ = c * (l / L₀) * ∑ a : Fin N,
            ((1 + (ErdosRiabov.cyclicDistance N x a : ℝ) / l) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ c * (l / L₀) * (2 * (c + 1) * l) := by
          gcongr; exact sum_inv_sq_le_scale hl hc x
      _ = 2 * (c + 1) * c * (l ^ 2 / L₀) := by ring
  rcases le_or_gt δ L₀ with hδ | hδ
  · have h1 := one_le_two_rpow_mul_decayF hs0 hL₀ hδ0 hδ
    calc ∑ a : Fin N, w a * decayF s l (ErdosRiabov.cyclicDistance N x a) *
          decayF s L₀ (ErdosRiabov.cyclicDistance N a y)
          ≤ ∑ a : Fin N, w a * decayF s l (ErdosRiabov.cyclicDistance N x a) := by
            apply Finset.sum_le_sum; intro a _
            have := decayF_pos (s := s) hl (Nat.cast_nonneg (ErdosRiabov.cyclicDistance N x a))
            have := hw0 a
            calc _ ≤ w a * decayF s l (ErdosRiabov.cyclicDistance N x a) * 1 := by
                  gcongr; exact decayF_le_one hs0 hL₀ (Nat.cast_nonneg _)
              _ = _ := mul_one _
      _ ≤ 2 * (c + 1) * c * (l ^ 2 / L₀) := hWR
      _ ≤ 2 * (c + 1) * c * (l ^ 2 / L₀) * (2 ^ s * decayF s L₀ δ) := by
            have : 0 ≤ 2 * (c + 1) * c * (l ^ 2 / L₀) := by positivity
            nlinarith
      _ ≤ _ := by
            have : 0 ≤ 2 * (c + 1) * (l ^ 2 / L₀) * decayF s L₀ δ := by positivity
            have : 0 ≤ 2 * (c + 1) * (l ^ 2 / L₀) * decayF s L₀ δ * 4 ^ s := by positivity
            nlinarith
  · have hpt := fun a : Fin N => split_pointwise hs0 hl hlL x y a hδ (w a) (hw0 a) (hw1 a)
    have hR' := sum_decayF_le' (s := s) (by linarith) hL₀ hcL y
    have hT := (transfer_factor_le (s := s) (by linarith) hl hlL).1
    calc ∑ a : Fin N, w a * decayF s l (ErdosRiabov.cyclicDistance N x a) *
          decayF s L₀ (ErdosRiabov.cyclicDistance N a y)
          ≤ ∑ a : Fin N, (2 ^ s * decayF s L₀ δ *
            (w a * decayF s l (ErdosRiabov.cyclicDistance N x a)) +
            (4 * l / L₀) ^ s * decayF s L₀ δ *
              decayF s L₀ (ErdosRiabov.cyclicDistance N a y)) :=
            Finset.sum_le_sum fun a _ => hpt a
      _ = 2 ^ s * decayF s L₀ δ *
              ∑ a : Fin N, w a * decayF s l (ErdosRiabov.cyclicDistance N x a) +
            (4 * l / L₀) ^ s * decayF s L₀ δ *
              ∑ a : Fin N, decayF s L₀ (ErdosRiabov.cyclicDistance N a y) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 ^ s * decayF s L₀ δ * (2 * (c + 1) * c * (l ^ 2 / L₀)) +
            (4 * l / L₀) ^ s * decayF s L₀ δ * (2 * (c + 1) * L₀) := by
            have : 0 ≤ (4 * l / L₀) ^ s := by positivity
            gcongr
      _ = 2 * (c + 1) * decayF s L₀ δ *
            (2 ^ s * c * (l ^ 2 / L₀) + (4 * l / L₀) ^ s * L₀) := by ring
      _ ≤ 2 * (c + 1) * decayF s L₀ δ * (2 ^ s * c * (l ^ 2 / L₀) + 4 ^ s * (l ^ 2 / L₀)) := by
            gcongr
      _ = _ := by ring

end BlockBand.Adapters.ErdosRiabov
