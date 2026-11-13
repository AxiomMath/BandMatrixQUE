module

public import BlockBand.Palm.MomentFlow.EventControl
public import BlockBand.Palm.GoodEventBrownian
public import BlockBand.Palm.MomentFlow.BridgeVersion

/-!
# Deterministic ingredients of the time mesh

* `resolvent_quad_im_compare`: `Im q*(H - z)⁻¹q ≤ Im q*(H' - z)⁻¹q + ‖H - H'‖ ‖q‖²/(Im z)²`
  (operator norm `opB` of `BlockBand.Palm.GoodEvent`).
* `im_resolvent_le_on_good`: on the good event of the external local law at `(σ, z)`,
  `Im q*G q ≤ (1 + N^δ/√(πv₀Nη)) K q*Γq` (`Γ(z) ≍ Γ` and `isotropicControl_freshM_le`).
* `nsq_le_of_gamma`: `‖q‖² ≤ N^{2max(A,1)} q*Γq/(v₀ lowConst)` (the directional lower bound,
  inverted).
* `dyadic_cell`: every `u ∈ [0,T]` lies in some level-`m` dyadic cell `[kT/2^m, (k+1)T/2^m]`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.Palm BlockBand.Palm.CoarseRelative BlockBand.Palm.GoodEvent
open scoped ComplexConjugate

variable {N : ℕ}

theorem norm_dotProduct_le_l2 (u v : Fin N → ℂ) : ‖star u ⬝ᵥ v‖ ≤ l2Norm u * l2Norm v := by
  have h := norm_dotProduct_sq_le u v
  rw [← Real.sqrt_le_sqrt_iff (by positivity), Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_mul (Finset.sum_nonneg fun _ _ => by positivity)] at h
  exact h

theorem l2Norm_resolvent_le {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) {w : ℂ}
    (hw : w.im ≠ 0) (y : Fin N → ℂ) :
    l2Norm ((H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ y) ≤ l2Norm y / |w.im| := by
  have h := hermitian_resolvent_nsq_le hH hw y
  rw [l2Norm_eq_sqrt_nsq, l2Norm_eq_sqrt_nsq]
  calc Real.sqrt (nsq ((H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ y))
      ≤ Real.sqrt ((w.im ^ 2)⁻¹ * nsq y) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (nsq y) / |w.im| := by
        rw [Real.sqrt_mul (inv_nonneg.2 (sq_nonneg _)), Real.sqrt_inv, Real.sqrt_sq_eq_abs]
        ring

/-- Resolvent comparison in operator norm. -/
theorem resolvent_quad_im_compare {H H' : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) {z : ℂ} (hz : 0 < z.im) (q : Fin N → ℂ) :
    (star q ⬝ᵥ ((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im ≤
      (star q ⬝ᵥ ((H' - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im +
        opB (H - H') * nsq q / z.im ^ 2 := by
  set X := H - z • (1 : Matrix (Fin N) (Fin N) ℂ)
  set X' := H' - z • (1 : Matrix (Fin N) (Fin N) ℂ)
  have hu := hermitian_shift_det_isUnit hH hz.ne'
  have hu' := hermitian_shift_det_isUnit hH' hz.ne'
  have hid : X⁻¹ - X'⁻¹ = X⁻¹ * (H' - H) * X'⁻¹ := by
    have e : H' - H = X' - X := by simp only [X, X']; abel
    rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu', Matrix.mul_one]
  have hsplit : star q ⬝ᵥ (X⁻¹ *ᵥ q) = star q ⬝ᵥ (X'⁻¹ *ᵥ q) +
      star q ⬝ᵥ ((X⁻¹ * (H' - H) * X'⁻¹) *ᵥ q) := by
    rw [← hid, Matrix.sub_mulVec, dotProduct_sub]; ring
  -- `q* X⁻¹ D X'⁻¹ q = (X⁻¹ᴴ q)* D (X'⁻¹ q)`
  have hX : star q ⬝ᵥ ((X⁻¹ * (H' - H) * X'⁻¹) *ᵥ q) =
      star ((X⁻¹)ᴴ *ᵥ q) ⬝ᵥ ((H' - H) *ᵥ (X'⁻¹ *ᵥ q)) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hXc : (X⁻¹)ᴴ = (H - (conj z) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ :=
    hermitian_resolvent_conjTranspose hH z
  have hzc : (conj z).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.2 hz.ne'
  have hb1 : l2Norm ((X⁻¹)ᴴ *ᵥ q) ≤ l2Norm q / z.im := by
    rw [hXc]
    have := l2Norm_resolvent_le hH hzc q
    rwa [Complex.conj_im, abs_neg, abs_of_pos hz] at this
  have hb2 : l2Norm (X'⁻¹ *ᵥ q) ≤ l2Norm q / z.im := by
    have := l2Norm_resolvent_le hH' hz.ne' q
    rwa [abs_of_pos hz] at this
  have hD : l2Norm ((H' - H) *ᵥ (X'⁻¹ *ᵥ q)) ≤ opB (H - H') * (l2Norm q / z.im) := by
    have := l2Norm_mulVec_le (H' - H) (X'⁻¹ *ᵥ q)
    rw [show H' - H = -(H - H') by abel, opB_neg] at this
    rw [show H' - H = -(H - H') by abel]
    exact this.trans (mul_le_mul_of_nonneg_left hb2 (opB_nonneg _))
  have hnorm : ‖star q ⬝ᵥ ((X⁻¹ * (H' - H) * X'⁻¹) *ᵥ q)‖ ≤
      opB (H - H') * nsq q / z.im ^ 2 := by
    rw [hX]
    refine (norm_dotProduct_le_l2 _ _).trans ?_
    have hq0 : 0 ≤ l2Norm q := Real.sqrt_nonneg _
    have hnn : 0 ≤ nsq q := Finset.sum_nonneg fun _ _ => by positivity
    have hl2 : l2Norm q * l2Norm q = nsq q := by
      rw [l2Norm_eq_sqrt_nsq]; exact Real.mul_self_sqrt hnn
    calc l2Norm ((X⁻¹)ᴴ *ᵥ q) * l2Norm ((H' - H) *ᵥ (X'⁻¹ *ᵥ q))
        ≤ (l2Norm q / z.im) * (opB (H - H') * (l2Norm q / z.im)) :=
          mul_le_mul hb1 hD (Real.sqrt_nonneg _) (by positivity)
      _ = opB (H - H') * nsq q / z.im ^ 2 := by rw [← hl2]; field_simp
  rw [hsplit, Complex.add_im]
  linarith [Complex.im_le_norm (star q ⬝ᵥ ((X⁻¹ * (H' - H) * X'⁻¹) *ᵥ q))]

/-- On the CEH good event, `Im q*Gq ≤ (1 + N^δ/√(πv₀Nη)) K q*Γq`. -/
theorem im_resolvent_le_on_good {F : Matrix (Fin N) (Fin N) ℂ} {A c₀ E r₀ s₀ v₀ σ : ℝ}
    (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀)
    (hσ : σ ∈ Icc (c₀ - s₀) c₀) {x η : ℝ} (hx : |x - E| ≤ r₀) (hη : 0 < η) (hη1 : η ≤ 1)
    (hN : 0 < N) (q : Fin N → ℂ) {δ : ℝ} {H : Matrix (Fin N) (Fin N) ℂ}
    (hgood : ‖star q ⬝ᵥ (((H - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
      freshM F σ ⟨x, η⟩) *ᵥ q)‖ ≤ (N : ℝ) ^ δ * CEH.isotropicControl (freshM F σ ⟨x, η⟩) ⟨x, η⟩ q q) :
    (star q ⬝ᵥ ((H - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im ≤
      (1 + (N : ℝ) ^ δ / Real.sqrt (Real.pi * v₀ * N * η)) *
        (gammaCompConst c₀ r₀ s₀ v₀ * quadForm (freshGamma F c₀ E) q) := by
  have hzr : |(⟨x, η⟩ : ℂ).re - E| ≤ r₀ := hx
  have h2 := im_quad_le ((H - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)
    (freshM F σ ⟨x, η⟩) q
  have hctrl := isotropicControl_freshM_le hK hC hσ hzr hη hη1 hN q
  have hgam := quad_im_le_gamma hN hK hC hσ hzr hη.le hη1 q
  set a := (star q ⬝ᵥ (freshM F σ ⟨x, η⟩ *ᵥ q)).im
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hNδ : 0 ≤ (N : ℝ) ^ δ := Real.rpow_nonneg hNp.le _
  have hv0 := hK.2.2.2.2.2
  have hsq : 0 < Real.sqrt (Real.pi * v₀ * N * η) := by positivity
  have hfac : 0 ≤ 1 + (N : ℝ) ^ δ / Real.sqrt (Real.pi * v₀ * N * η) := by positivity
  have : (N : ℝ) ^ δ * CEH.isotropicControl (freshM F σ ⟨x, η⟩) ⟨x, η⟩ q q ≤
      (N : ℝ) ^ δ * (a / Real.sqrt (Real.pi * v₀ * N * η)) :=
    mul_le_mul_of_nonneg_left hctrl hNδ
  have e : a * (1 + (N : ℝ) ^ δ / Real.sqrt (Real.pi * v₀ * N * η)) =
      a + (N : ℝ) ^ δ * (a / Real.sqrt (Real.pi * v₀ * N * η)) := by ring
  calc _ ≤ a * (1 + (N : ℝ) ^ δ / Real.sqrt (Real.pi * v₀ * N * η)) := by rw [e]; linarith
    _ ≤ (gammaCompConst c₀ r₀ s₀ v₀ * quadForm (freshGamma F c₀ E) q) *
          (1 + (N : ℝ) ^ δ / Real.sqrt (Real.pi * v₀ * N * η)) :=
        mul_le_mul_of_nonneg_right hgam hfac
    _ = _ := by ring

/-- `‖q‖² ≤ N^{2max(A,1)} q*Γq/(v₀ lowConst)`. -/
theorem nsq_le_of_gamma {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N)
    {A c₀ E r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀)
    (q : Fin N → ℂ) :
    nsq q ≤ (N : ℝ) ^ (2 * max A 1) * quadForm (freshGamma F c₀ E) q /
      (v₀ * lowConst c₀ s₀ v₀) := by
  have h := freshGamma_quad_lower hN hK hC q
  have hv0 := hK.2.2.2.2.2
  have hl : 0 < lowConst c₀ s₀ v₀ := by
    unfold lowConst
    have : 0 < c₀ - s₀ := by linarith [hK.2.2.2.2.1, hK.1]
    positivity
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 0 < (N : ℝ) ^ (2 * max A 1) := Real.rpow_pos_of_pos hNp _
  have hinv : (N : ℝ) ^ (-(2 * max A 1)) * (N : ℝ) ^ (2 * max A 1) = 1 := by
    rw [← Real.rpow_add hNp]; simp
  rw [le_div_iff₀ (by positivity)]
  calc nsq q * (v₀ * lowConst c₀ s₀ v₀)
      = (v₀ * lowConst c₀ s₀ v₀ * (N : ℝ) ^ (-(2 * max A 1)) * nsq q) *
          (N : ℝ) ^ (2 * max A 1) := by
        rw [show v₀ * lowConst c₀ s₀ v₀ * (N : ℝ) ^ (-(2 * max A 1)) * nsq q *
          (N : ℝ) ^ (2 * max A 1) = v₀ * lowConst c₀ s₀ v₀ * nsq q *
          ((N : ℝ) ^ (-(2 * max A 1)) * (N : ℝ) ^ (2 * max A 1)) by ring, hinv]; ring
    _ ≤ quadForm (freshGamma F c₀ E) q * (N : ℝ) ^ (2 * max A 1) :=
        mul_le_mul_of_nonneg_right h hp.le
    _ = _ := by ring

/-- Level-`m` dyadic cells cover `[0, T]`. -/
theorem dyadic_cell {T : ℝ} (hT : 0 < T) (m : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (huT : u ≤ T) :
    ∃ k : ℕ, k < 2 ^ m ∧ (k : ℝ) * T / 2 ^ m ≤ u ∧ u ≤ ((k : ℝ) + 1) * T / 2 ^ m := by
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  set t := u * 2 ^ m / T
  have ht0 : 0 ≤ t := by positivity
  have htm : t ≤ 2 ^ m := by
    simp only [t]; rw [div_le_iff₀ hT]; nlinarith
  by_cases hfull : ⌊t⌋₊ < 2 ^ m
  · refine ⟨⌊t⌋₊, hfull, ?_, ?_⟩
    · have := Nat.floor_le ht0
      rw [div_le_iff₀ h2]; simp only [t] at this
      rw [le_div_iff₀ hT] at this; linarith
    · have := Nat.lt_floor_add_one t
      rw [le_div_iff₀ h2]; simp only [t] at this
      rw [div_lt_iff₀ hT] at this; linarith
  · refine ⟨2 ^ m - 1, Nat.sub_lt (by positivity) one_pos, ?_, ?_⟩
    · have hle : (2 : ℝ) ^ m ≤ ⌊t⌋₊ := by exact_mod_cast not_lt.1 hfull
      have := Nat.floor_le ht0
      have hcast : ((2 ^ m - 1 : ℕ) : ℝ) = (2 : ℝ) ^ m - 1 := by
        rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_two, Nat.cast_one]
      rw [hcast, div_le_iff₀ h2]
      have : t = 2 ^ m := le_antisymm htm (hle.trans this)
      simp only [t] at this
      rw [div_eq_iff hT.ne'] at this
      nlinarith
    · have hcast : ((2 ^ m - 1 : ℕ) : ℝ) = (2 : ℝ) ^ m - 1 := by
        rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_two, Nat.cast_one]
      rw [hcast, sub_add_cancel]
      have e : (2 : ℝ) ^ m * T / 2 ^ m = T := by field_simp
      rw [e]; exact huT

end BlockBand.Palm.MomentFlow
