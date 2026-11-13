module

public import BlockBand.Native.CEH.LocalLaw.Setup

/-!
# CEH local law, assembly: the MDE solution and the CEH controls

Deterministic facts about a solution `M` of the MDE of the paper `(F - (z + s⟨M⟩)) M = 1`,
`Im z · Im M ≻ 0` (`IsManuscriptMDE s F z M`), `s ≥ 0`, `Im z ≠ 0`, `N > 0`; `m = ⟨M⟩`,
`c = |Im m| = π ρ`, `η = |Im z|`, `w_v = |Im v* M v|`.

* `w_v > 0` for `v ≠ 0`; `Re v* Γ v = w_v / c`; `Re ⟨Γ B Bᴴ⟩ = W_B / c` with
  `W_B = N⁻¹ ∑_j w_{B e_j}`; `W_B > 0` for `B ≠ 0`.
* `isotropicControl_eq`: `isotropicControl M z x y = √(ρ/(Nη)) √(w_x w_y) / c` (`x, y ≠ 0`);
  `averagedControl_eq`: `averagedControl M B z = √(W_B / c) / (N η)` (`B ≠ 0`).
* `density_sq_mul_le`: `c² s ≤ 1` (Ward identity for `M` and `|⟨M⟩|² ≤ ⟨M Mᴴ⟩`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.LocalLaw

open Matrix Set
open BlockBand.External.CEH BlockBand.Native.CEH.Phase1
open BlockBand.Internal.Contracts.Inputs

variable {N : ℕ} {s : ℝ} {F : SourceHermitian N} {z : ℂ} {Mz : Matrix (Fin N) (Fin N) ℂ}

/-- `a / b = |a| / |b|` when `a b ≥ 0`. -/
theorem div_eq_abs_div_abs {a b : ℝ} (h : 0 ≤ a * b) : a / b = |a| / |b| := by
  rw [← abs_div, abs_of_nonneg (div_nonneg_iff.2 (mul_nonneg_iff.1 h))]

theorem mde_spectral_im_ne (hMDE : IsManuscriptMDE s F z Mz) (hz : z.im ≠ 0) (hs : 0 ≤ s) :
    (z + (s : ℂ) * normalizedTrace Mz).im ≠ 0 :=
  mde_im_spectral_ne hMDE hz hs

/-- `w_v > 0` for `v ≠ 0`. -/
theorem mde_weight_pos (hMDE : IsManuscriptMDE s F z Mz) (hz : z.im ≠ 0) (hs : 0 ≤ s)
    {v : Fin N → ℂ} (hv : v ≠ 0) : 0 < |(sourceMatrixElement Mz v v).im| := by
  have h := abs_im_sourceMatrixElement_resolvent_pos F.2 (mde_spectral_im_ne hMDE hz hs) hv
  rwa [← mde_eq_resolvent hMDE] at h

/-- `Im (v* M v) · Im m ≥ 0`. -/
theorem mde_im_quad_mul_nonneg (hMDE : IsManuscriptMDE s F z Mz) (hz : z.im ≠ 0) (hs : 0 ≤ s)
    (v : Fin N → ℂ) : 0 ≤ (sourceMatrixElement Mz v v).im * (normalizedTrace Mz).im := by
  have h := im_sourceMatrixElement_resolvent F.2 (mde_spectral_im_ne hMDE hz hs) v
  rw [← mde_eq_resolvent hMDE, im_add_ofReal_mul] at h
  rw [h]
  have h1 := mde_im_mul_im_nonneg hMDE
  have h2 : 0 ≤ (z.im + s * (normalizedTrace Mz).im) * (normalizedTrace Mz).im := by
    nlinarith [sq_nonneg (normalizedTrace Mz).im]
  have h3 := sq_nonneg (sourceVectorNorm (Mz *ᵥ v))
  calc (0 : ℝ) ≤ sourceVectorNorm (Mz *ᵥ v) ^ 2 *
        ((z.im + s * (normalizedTrace Mz).im) * (normalizedTrace Mz).im) := mul_nonneg h3 h2
    _ = _ := by ring

/-- `Re v* Γ v = w_v / c`. -/
theorem re_sourceMatrixElement_gamma (hMDE : IsManuscriptMDE s F z Mz) (hz : z.im ≠ 0)
    (hs : 0 ≤ s) (v : Fin N → ℂ) :
    (sourceMatrixElement (gammaMatrix Mz) v v).re =
      |(sourceMatrixElement Mz v v).im| / |(normalizedTrace Mz).im| := by
  rw [gammaMatrix_eq, sourceMatrixElement_smul, ← Complex.ofReal_inv, Complex.re_ofReal_mul,
    re_sourceMatrixElement_imaginaryPart, inv_mul_eq_div]
  exact div_eq_abs_div_abs (mde_im_quad_mul_nonneg hMDE hz hs v)

/-- `Re ⟨Γ B Bᴴ⟩ = W_B / c`. -/
theorem re_normalizedTrace_gamma_mul (hMDE : IsManuscriptMDE s F z Mz) (hz : z.im ≠ 0)
    (hs : 0 ≤ s) (B : Matrix (Fin N) (Fin N) ℂ) :
    (normalizedTrace (gammaMatrix Mz * B * Bᴴ)).re =
      (N : ℝ)⁻¹ * (∑ j, |(sourceMatrixElement Mz (col B j) (col B j)).im|) /
        |(normalizedTrace Mz).im| := by
  rw [gammaMatrix_eq, Matrix.smul_mul, Matrix.smul_mul, normalizedTrace_smul,
    normalizedTrace_mul_mul_conjTranspose, ← Complex.ofReal_inv, Complex.re_ofReal_mul,
    ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum]
  simp only [re_sourceMatrixElement_imaginaryPart]
  rw [mul_div_assoc, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← div_eq_abs_div_abs (mde_im_quad_mul_nonneg hMDE hz hs (col B j))]
  ring

/-- `W_B > 0` for `B ≠ 0`. -/
theorem mde_weight_sum_pos (hMDE : IsManuscriptMDE s F z Mz) (hz : z.im ≠ 0) (hs : 0 ≤ s)
    (hN : 0 < N) {B : Matrix (Fin N) (Fin N) ℂ} (hB : B ≠ 0) :
    0 < (N : ℝ)⁻¹ * ∑ j, |(sourceMatrixElement Mz (col B j) (col B j)).im| := by
  have hex : ∃ j, col B j ≠ 0 := by
    by_contra h
    push Not at h
    apply hB
    ext i j
    have := congrFun (h j) i
    simpa [col] using this
  obtain ⟨j, hj⟩ := hex
  have hpos := mde_weight_pos hMDE hz hs hj
  have hle : |(sourceMatrixElement Mz (col B j) (col B j)).im| ≤
      ∑ j, |(sourceMatrixElement Mz (col B j) (col B j)).im| :=
    Finset.single_le_sum (f := fun j => |(sourceMatrixElement Mz (col B j) (col B j)).im|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 hN)
  exact mul_pos this (hpos.trans_le hle)

/-- `Re ⟨B Bᴴ⟩ > 0` for `B ≠ 0`. -/
theorem re_normalizedTrace_mul_conjTranspose_pos (hN : 0 < N) {B : Matrix (Fin N) (Fin N) ℂ}
    (hB : B ≠ 0) : 0 < (normalizedTrace (B * Bᴴ)).re := by
  rw [normalizedTrace_mul_conjTranspose_self, Complex.ofReal_re]
  have hex : ∃ i j, B i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hB (Matrix.ext fun i j => h i j)
  obtain ⟨i, j, hij⟩ := hex
  have h1 : 0 < ‖B i j‖ ^ 2 := by positivity
  have h2 : ‖B i j‖ ^ 2 ≤ ∑ j, ‖B i j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖B i j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h3 : ∑ j, ‖B i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖B i j‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ∑ j, ‖B i j‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact mul_pos (inv_pos.2 (Nat.cast_pos.2 hN)) (h1.trans_le (h2.trans h3))

/-- **Isotropic control** for `x, y ≠ 0`: `√(ρ/(Nη)) √(w_x w_y) / c`. -/
theorem isotropicControl_eq (hMDE : IsManuscriptMDE s F z Mz) (hz : z.im ≠ 0) (hs : 0 ≤ s)
    (hN : 0 < N) {x y : Fin N → ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    isotropicControl Mz z x y =
      Real.sqrt (sourceDensity Mz / ((N : ℝ) * |z.im|)) *
        Real.sqrt (|(sourceMatrixElement Mz x x).im| * |(sourceMatrixElement Mz y y).im|) /
        |(normalizedTrace Mz).im| := by
  have hc : 0 < |(normalizedTrace Mz).im| := abs_pos.2 fun h0 => by
    have := mde_im_mul_im_pos hN hMDE
    rw [h0, mul_zero] at this
    exact lt_irrefl _ this
  have hnx : 0 < sourceVectorNorm x :=
    lt_of_le_of_ne (sourceVectorNorm_nonneg x) fun h => hx ((sourceVectorNorm_eq_zero_iff x).1 h.symm)
  have hny : 0 < sourceVectorNorm y :=
    lt_of_le_of_ne (sourceVectorNorm_nonneg y) fun h => hy ((sourceVectorNorm_eq_zero_iff y).1 h.symm)
  unfold isotropicControl
  rw [re_sourceMatrixElement_gamma hMDE hz hs, re_sourceMatrixElement_gamma hMDE hz hs]
  set c := |(normalizedTrace Mz).im|
  set wx := |(sourceMatrixElement Mz x x).im|
  set wy := |(sourceMatrixElement Mz y y).im|
  have hw : 0 ≤ wx * wy := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have e : wx / c * (wy / c) / (sourceVectorNorm x ^ 2 * sourceVectorNorm y ^ 2) =
      (wx * wy) / (c * sourceVectorNorm x * sourceVectorNorm y) ^ 2 := by
    field_simp
  rw [e, Real.sqrt_div hw, Real.sqrt_sq (by positivity)]
  field_simp

/-- **Averaged control** for `B ≠ 0`: `√(W_B / c) / (N η)`. -/
theorem averagedControl_eq (hMDE : IsManuscriptMDE s F z Mz) (hz : z.im ≠ 0) (hs : 0 ≤ s)
    (hN : 0 < N) {B : Matrix (Fin N) (Fin N) ℂ} (hB : B ≠ 0) :
    averagedControl Mz B z =
      Real.sqrt ((N : ℝ)⁻¹ * (∑ j, |(sourceMatrixElement Mz (col B j) (col B j)).im|) /
        |(normalizedTrace Mz).im|) / ((N : ℝ) * |z.im|) := by
  have ha := re_normalizedTrace_mul_conjTranspose_pos hN hB
  unfold averagedControl normalizedHilbertSchmidt
  rw [re_normalizedTrace_gamma_mul hMDE hz hs]
  set a := (normalizedTrace (B * Bᴴ)).re
  set X := (N : ℝ)⁻¹ * (∑ j, |(sourceMatrixElement Mz (col B j) (col B j)).im|) /
    |(normalizedTrace Mz).im|
  have : Real.sqrt a * Real.sqrt (X / a) = Real.sqrt X := by
    rw [← Real.sqrt_mul ha.le, mul_div_cancel₀ _ ha.ne']
  rw [div_mul_eq_mul_div, this]

/-- **Density bound** `c² s ≤ 1`, i.e. `ρ ≤ 1/(π √s)`. -/
theorem density_sq_mul_le (hMDE : IsManuscriptMDE s F z Mz) (hz : z.im ≠ 0) (hs : 0 ≤ s)
    (hN : 0 < N) : |(normalizedTrace Mz).im| ^ 2 * s ≤ 1 := by
  set w := z + (s : ℂ) * normalizedTrace Mz with hwdef
  have hw := mde_spectral_im_ne hMDE hz hs
  have hres := mde_eq_resolvent hMDE
  have hc : 0 < |(normalizedTrace Mz).im| := abs_pos.2 fun h0 => by
    have := mde_im_mul_im_pos hN hMDE
    rw [h0, mul_zero] at this
    exact lt_irrefl _ this
  -- Ward: `⟨M Mᴴ⟩ = Im m / Im w`
  have hward := normalizedTrace_resolvent_mul_conjTranspose_eq_real F.2 hw
  rw [← hres] at hward
  -- Cauchy–Schwarz: `|m| ≤ √⟨M Mᴴ⟩`
  have hcs := norm_normalizedTrace_mul_le Mz 1
  rw [Matrix.mul_one, conjTranspose_one, Matrix.mul_one] at hcs
  have h1 : normalizedTrace (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    rw [normalizedTrace, trace_one, Fintype.card_fin]
    field_simp [Nat.cast_ne_zero.2 hN.ne']
  rw [h1, Complex.one_re, Real.sqrt_one, mul_one, hward, Complex.ofReal_re] at hcs
  have hmw : 0 ≤ (normalizedTrace Mz).im * w.im := by
    rw [hwdef, im_add_ofReal_mul]
    nlinarith [mde_im_mul_im_nonneg hMDE, mul_nonneg hs (sq_nonneg (normalizedTrace Mz).im)]
  have hq : 0 ≤ (normalizedTrace Mz).im / w.im := div_nonneg_iff.2 (mul_nonneg_iff.1 hmw)
  have hsq : |(normalizedTrace Mz).im| ^ 2 ≤ (normalizedTrace Mz).im / w.im := by
    have h2 : |(normalizedTrace Mz).im| ≤ ‖normalizedTrace Mz‖ := Complex.abs_im_le_norm _
    have h3 := pow_le_pow_left₀ (abs_nonneg _) (h2.trans hcs) 2
    rwa [Real.sq_sqrt hq] at h3
  rw [div_eq_abs_div_abs hmw] at hsq
  have habs := mde_abs_im_spectral hMDE hs
  rw [← hwdef] at habs
  rw [habs] at hsq
  have hη : 0 < |z.im| := abs_pos.2 hz
  rw [le_div_iff₀ (by positivity)] at hsq
  nlinarith [mul_pos hc hη]

end BlockBand.Native.CEH.LocalLaw
