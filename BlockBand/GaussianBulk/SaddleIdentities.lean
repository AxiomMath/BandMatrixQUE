module

public import Mathlib
public import BlockBand.GaussianBulk.ContourGeometry

/-!
# Saddle identities for the finite external-source MDE

Defines the finite Stieltjes transform of a real source `d`, the scalar finite MDE
`m = N⁻¹ Σ_j (d_j - E - tm)⁻¹`, its saddle point `z₀ = E + tm` and the saddle phase
`(z - E)²/(2t) + N⁻¹ Σ_j log(z - d_j)`. The saddle point is a critical point of the phase,
`|m| ≤ t^{-1/2}`, and the inverse moments and second phase derivative are bounded uniformly in
`N` and `d` on horizontal strips.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.GaussianBulk

open scoped BigOperators

/-- The normalized complex average `N⁻¹ Σ_j f j`. -/
def complexMean {N : ℕ} (f : Fin N → ℂ) : ℂ :=
  (((N : ℝ)⁻¹ : ℝ) : ℂ) * ∑ j, f j

/-- The normalized real average `N⁻¹ Σ_j f j`. -/
def realMean {N : ℕ} (f : Fin N → ℝ) : ℝ := (N : ℝ)⁻¹ * ∑ j, f j

/-- The finite Stieltjes transform `N⁻¹ Σ_j (d_j - z)⁻¹`. -/
def finiteStieltjes {N : ℕ} (d : Fin N → ℝ) (z : ℂ) : ℂ :=
  complexMean (fun j => ((d j : ℂ) - z)⁻¹)

/-- The saddle point `E + tm` of an MDE solution `m`. -/
def saddlePoint (E t : ℝ) (m : ℂ) : ℂ := (E : ℂ) + (t : ℂ) * m

/-- The scalar finite MDE at real energy `E`. -/
def FiniteMDE {N : ℕ} (d : Fin N → ℝ) (E t : ℝ) (m : ℂ) : Prop :=
  m = finiteStieltjes d (saddlePoint E t m)

/-- The saddle phase, with principal logarithms; it is analytic off the real axis. -/
def saddlePhase {N : ℕ} (d : Fin N → ℝ) (E t : ℝ) (z : ℂ) : ℂ :=
  (z - (E : ℂ)) ^ 2 / (2 * (t : ℂ)) +
    complexMean (fun j => Complex.log (z - (d j : ℂ)))

/-- The normalized inverse-power moment `N⁻¹ Σ_j (z - d_j)^{-k}`. -/
def inverseMoment {N : ℕ} (d : Fin N → ℝ) (z : ℂ) (k : ℕ) : ℂ :=
  complexMean (fun j => ((z - (d j : ℂ))⁻¹) ^ k)

/-- The finite level average of inverse squared distances. -/
def levelAverage {N : ℕ} (d : Fin N → ℝ) (z : ℂ) : ℝ :=
  realMean (fun j => (Complex.normSq ((d j : ℂ) - z))⁻¹)

/-- Imaginary parts commute with the normalized average. -/
theorem complexMean_im {N : ℕ} (f : Fin N → ℂ) :
    (complexMean f).im = realMean (fun j => (f j).im) := by
  unfold complexMean realMean
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hsum : (∑ j, f j).im = ∑ j, (f j).im :=
    map_sum Complex.imAddGroupHom _ _
  rw [hsum]

/-- A normalized finite complex average is bounded by the average of norms. -/
theorem norm_complexMean_le {N : ℕ} (f : Fin N → ℂ) :
    ‖complexMean f‖ ≤ realMean (fun j => ‖f j‖) := by
  have hc : 0 ≤ (N : ℝ)⁻¹ := by positivity
  unfold complexMean realMean
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hc

/-- Cauchy–Schwarz for the normalized complex average. -/
theorem norm_complexMean_sq_le {N : ℕ} (hN : 0 < N) (f : Fin N → ℂ) :
    ‖complexMean f‖ ^ 2 ≤ realMean (fun j => ‖f j‖ ^ 2) := by
  have hnonempty : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hmean := norm_complexMean_le f
  have hsq := mul_self_le_mul_self (norm_nonneg (complexMean f)) hmean
  have hcs := @square_mean_le_mean_square (Fin N) inferInstance hnonempty
    (fun j => ‖f j‖)
  have hcs' : (realMean (fun j => ‖f j‖)) ^ 2 ≤
      realMean (fun j => ‖f j‖ ^ 2) := by
    simpa [realMean, div_eq_mul_inv, mul_comm] using hcs
  exact le_trans (by simpa only [pow_two] using hsq) hcs'

/-- Ward identity: `Im s(z) = Im z · levelAverage(z)`. -/
theorem finiteStieltjes_im {N : ℕ} (d : Fin N → ℝ) (z : ℂ) :
    (finiteStieltjes d z).im = z.im * levelAverage d z := by
  unfold finiteStieltjes
  rw [complexMean_im]
  unfold realMean levelAverage realMean
  simp only [Complex.inv_im, Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
  simp only [div_eq_mul_inv]
  rw [← Finset.mul_sum]
  ring

/-- `|d - z|² = (d - Re z)² + (Im z)²`. -/
theorem normSq_real_sub (d : ℝ) (z : ℂ) :
    Complex.normSq ((d : ℂ) - z) = (d - z.re) ^ 2 + z.im ^ 2 := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_sub]
  ring

/-- The saddle has height `t Im m`. -/
theorem saddlePoint_im (E t : ℝ) (m : ℂ) :
    (saddlePoint E t m).im = t * m.im := by
  simp [saddlePoint, Complex.mul_im]

/-- If `t ≥ tmin` and `Im m ≥ v ≥ 0`, the saddle height is at least `tmin · v`. -/
theorem saddlePoint_im_lower (E t tmin v : ℝ) (m : ℂ)
    (htmin : 0 < tmin) (ht : tmin ≤ t) (hv : 0 ≤ v) (hm : v ≤ m.im) :
    tmin * v ≤ (saddlePoint E t m).im := by
  rw [saddlePoint_im]
  exact mul_le_mul ht hm hv (le_of_lt (lt_of_lt_of_le htmin ht))

/-- The imaginary part of the MDE gives the level equation `levelAverage(z₀) = 1/t`. -/
theorem levelAverage_saddle_eq {N : ℕ} (d : Fin N → ℝ) (E t : ℝ) (m : ℂ)
    (ht : 0 < t) (hm : 0 < m.im) (hMDE : FiniteMDE d E t m) :
    levelAverage d (saddlePoint E t m) = 1 / t := by
  have him := congrArg Complex.im hMDE
  rw [finiteStieltjes_im, saddlePoint_im] at him
  have hunit : t * levelAverage d (saddlePoint E t m) = 1 := by
    apply mul_left_cancel₀ (ne_of_gt hm)
    nlinarith only [him]
  apply (eq_div_iff (ne_of_gt ht)).mpr
  nlinarith only [hunit]

/-- The level equation at the saddle in real coordinates. -/
theorem real_level_saddle_eq {N : ℕ} (d : Fin N → ℝ) (E t : ℝ) (m : ℂ)
    (ht : 0 < t) (hm : 0 < m.im) (hMDE : FiniteMDE d E t m) :
    realMean (fun j => 1 /
      ((d j - (saddlePoint E t m).re) ^ 2 + (saddlePoint E t m).im ^ 2)) = 1 / t := by
  simpa only [levelAverage, normSq_real_sub, one_div] using
    levelAverage_saddle_eq d E t m ht hm hMDE

/-- The mean squared resolvent norm equals the level average. -/
theorem resolvent_square_mean_eq_level {N : ℕ} (d : Fin N → ℝ) (z : ℂ) :
    realMean (fun j => ‖((d j : ℂ) - z)⁻¹‖ ^ 2) = levelAverage d z := by
  simp only [Complex.sq_norm, Complex.normSq_inv, levelAverage]

/-- `|m|² ≤ 1/t` for a solution of the MDE with `Im m > 0`, uniformly in `d`. -/
theorem norm_mde_sq_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t : ℝ) (m : ℂ) (ht : 0 < t) (hm : 0 < m.im)
    (hMDE : FiniteMDE d E t m) : ‖m‖ ^ 2 ≤ 1 / t := by
  have hcs := norm_complexMean_sq_le hN
    (fun j => ((d j : ℂ) - saddlePoint E t m)⁻¹)
  change ‖finiteStieltjes d (saddlePoint E t m)‖ ^ 2 ≤ _ at hcs
  rw [← hMDE, resolvent_square_mean_eq_level,
    levelAverage_saddle_eq d E t m ht hm hMDE] at hcs
  exact hcs

/-- The derivative of the saddle phase off the real axis. -/
theorem hasDerivAt_saddlePhase {N : ℕ} (d : Fin N → ℝ) (E t : ℝ)
    (z : ℂ) (ht : t ≠ 0) (hz : z.im ≠ 0) :
    HasDerivAt (saddlePhase d E t)
      ((z - (E : ℂ)) / (t : ℂ) + inverseMoment d z 1) z := by
  have hpoly := (((hasDerivAt_id z).sub_const (E : ℂ)).pow 2).div_const
    (2 * (t : ℂ))
  have hlogs : HasDerivAt (fun w : ℂ => ∑ j, Complex.log (w - (d j : ℂ)))
      (∑ j, (z - (d j : ℂ))⁻¹) z := by
    apply HasDerivAt.fun_sum
    intro j _
    have hslit : z - (d j : ℂ) ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      right
      simpa using hz
    convert! (Complex.hasDerivAt_log hslit).comp_sub_const z (d j : ℂ) using 1
  have hpoly' : HasDerivAt (fun w : ℂ => (w - (E : ℂ)) ^ 2 /
      (2 * (t : ℂ))) ((z - (E : ℂ)) / (t : ℂ)) z := by
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    convert! hpoly using 1
    all_goals first
      | (funext w)
      | (simp only [id_eq]; field_simp [htC]; ring)
  convert! hpoly'.add (hlogs.const_mul (((N : ℝ)⁻¹ : ℝ) : ℂ)) using 1
  all_goals first | rfl | (simp only [inverseMoment, complexMean, pow_one])

/-- The first inverse moment is minus the Stieltjes transform. -/
theorem inverseMoment_one_eq_neg_stieltjes {N : ℕ} (d : Fin N → ℝ) (z : ℂ) :
    inverseMoment d z 1 = -finiteStieltjes d z := by
  unfold inverseMoment finiteStieltjes complexMean
  simp only [pow_one]
  have hsum : (∑ j, (z - (d j : ℂ))⁻¹) =
      -(∑ j, ((d j : ℂ) - z)⁻¹) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [show z - (d j : ℂ) = -((d j : ℂ) - z) by ring, inv_neg]
  rw [hsum]
  ring

/-- The MDE saddle point is a critical point of the saddle phase. -/
theorem hasDerivAt_saddlePhase_zero {N : ℕ} (d : Fin N → ℝ) (E t : ℝ)
    (m : ℂ) (ht : 0 < t) (hm : 0 < m.im) (hMDE : FiniteMDE d E t m) :
    HasDerivAt (saddlePhase d E t) 0 (saddlePoint E t m) := by
  have hz : (saddlePoint E t m).im ≠ 0 := by
    rw [saddlePoint_im]
    exact ne_of_gt (mul_pos ht hm)
  have h := hasDerivAt_saddlePhase d E t (saddlePoint E t m) (ne_of_gt ht) hz
  have heq : (saddlePoint E t m - (E : ℂ)) / (t : ℂ) +
      inverseMoment d (saddlePoint E t m) 1 = 0 := by
    rw [inverseMoment_one_eq_neg_stieltjes, ← hMDE]
    unfold saddlePoint
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
    field_simp [htC]
    ring
  rw [heq] at h
  exact h

/-- `|m| ≤ 1/√t`. -/
theorem norm_mde_le_inv_sqrt {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t : ℝ) (m : ℂ) (ht : 0 < t) (hm : 0 < m.im)
    (hMDE : FiniteMDE d E t m) : ‖m‖ ≤ 1 / Real.sqrt t := by
  have hs := norm_mde_sq_le hN d E t m ht hm hMDE
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have htroot : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt (le_of_lt ht)
  have hbound : (1 / Real.sqrt t) ^ 2 = 1 / t := by
    rw [div_pow, one_pow, htroot]
  have hp : 0 ≤ 1 / Real.sqrt t := le_of_lt (one_div_pos.mpr hsqrt)
  nlinarith [norm_nonneg m]

/-- The saddle height is at most `√t`. -/
theorem saddlePoint_im_le_sqrt {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t : ℝ) (m : ℂ) (ht : 0 < t) (hm : 0 < m.im)
    (hMDE : FiniteMDE d E t m) :
    (saddlePoint E t m).im ≤ Real.sqrt t := by
  rw [saddlePoint_im]
  have hn := norm_mde_le_inv_sqrt hN d E t m ht hm hMDE
  have hmul := mul_le_mul_of_nonneg_left
    (le_trans (Complex.im_le_norm m) hn) (le_of_lt ht)
  have heq : t * (1 / Real.sqrt t) = Real.sqrt t := by
    rw [show t * (1 / Real.sqrt t) = t / Real.sqrt t by ring]
    apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr ht))).mpr
    simpa only [pow_two] using (Real.sq_sqrt (le_of_lt ht)).symm
  simpa only [heq] using hmul

/-- A nonreal point avoids every real pole. -/
theorem shifted_eigenvalue_ne_zero (d : ℝ) (z : ℂ) (hz : z.im ≠ 0) :
    z - (d : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at him
  exact hz him

/-- Derivative recurrence for the inverse moments: `(M_{k+1})' = -(k+1) M_{k+2}`. -/
theorem hasDerivAt_inverseMoment_succ {N : ℕ} (d : Fin N → ℝ) (z : ℂ)
    (hz : z.im ≠ 0) (k : ℕ) :
    HasDerivAt (fun w => inverseMoment d w (k + 1))
      (-((k + 1 : ℕ) : ℂ) * inverseMoment d z (k + 2)) z := by
  have hterms (j : Fin N) :
      HasDerivAt (fun w : ℂ => ((w - (d j : ℂ))⁻¹) ^ (k + 1))
        (-((k + 1 : ℕ) : ℂ) * ((z - (d j : ℂ))⁻¹) ^ (k + 2)) z := by
    have hinv : HasDerivAt (fun w : ℂ => (w - (d j : ℂ))⁻¹)
        (-(1 : ℂ) / (z - (d j : ℂ)) ^ 2) z := by
      convert! ((hasDerivAt_id z).sub_const (d j : ℂ)).inv
        (shifted_eigenvalue_ne_zero (d j) z hz) using 1
    have hpow : HasDerivAt (fun w : ℂ => ((w - (d j : ℂ))⁻¹) ^ (k + 1))
        (((k + 1 : ℕ) : ℂ) * ((z - (d j : ℂ))⁻¹) ^ k *
          (-(1 : ℂ) / (z - (d j : ℂ)) ^ 2)) z := by
      convert! hinv.pow (k + 1) using 1
    apply hpow.congr_deriv
    rw [div_eq_mul_inv, ← inv_pow (z - (d j : ℂ)) 2]
    simp only [pow_succ]
    ring
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterms j)
  have h := hsum.const_mul (((N : ℝ)⁻¹ : ℝ) : ℂ)
  convert! h using 1
  all_goals first
    | rfl
    | (unfold inverseMoment complexMean; rw [← Finset.mul_sum]; ring)

/-- `|(z - d)^{-k}| ≤ η^{-k}` when `|Im z| ≥ η`. -/
theorem norm_inverse_power_le (d : ℝ) (z : ℂ) (η : ℝ) (hη : 0 < η)
    (hz : η ≤ |z.im|) (k : ℕ) :
    ‖((z - (d : ℂ))⁻¹) ^ k‖ ≤ (1 / η) ^ k := by
  have hden : η ≤ ‖z - (d : ℂ)‖ := by
    apply le_trans hz
    simpa using Complex.abs_im_le_norm (z - (d : ℂ))
  have hinv : ‖(z - (d : ℂ))⁻¹‖ ≤ 1 / η := by
    rw [norm_inv, ← one_div]
    exact one_div_le_one_div_of_le hη hden
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hinv k

/-- `|M_k(z)| ≤ η^{-k}` when `|Im z| ≥ η`, uniformly in `N` and `d`. -/
theorem norm_inverseMoment_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (z : ℂ) (η : ℝ) (hη : 0 < η) (hz : η ≤ |z.im|) (k : ℕ) :
    ‖inverseMoment d z k‖ ≤ (1 / η) ^ k := by
  have hmean := norm_complexMean_le (fun j => ((z - (d j : ℂ))⁻¹) ^ k)
  have hsum : (∑ j, ‖((z - (d j : ℂ))⁻¹) ^ k‖) ≤
      ∑ _j : Fin N, (1 / η) ^ k := by
    exact Finset.sum_le_sum (fun j _ => norm_inverse_power_le (d j) z η hη hz k)
  have hc : 0 ≤ (N : ℝ)⁻¹ := by positivity
  have hscale := mul_le_mul_of_nonneg_left hsum hc
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hscale' : realMean (fun j => ‖((z - (d j : ℂ))⁻¹) ^ k‖) ≤
      (1 / η) ^ k := by
    simpa [realMean, Finset.sum_const, hn] using hscale
  exact le_trans hmean hscale'

/-- The ball of radius `tmin · v/2` around the saddle stays at height at least `tmin · v/2`. -/
theorem saddle_neighborhood_height (E t tmin v : ℝ) (m z : ℂ)
    (htmin : 0 < tmin) (ht : tmin ≤ t) (hv : 0 < v) (hm : v ≤ m.im)
    (hnear : ‖z - saddlePoint E t m‖ ≤ tmin * v / 2) :
    tmin * v / 2 ≤ z.im := by
  have hs := saddlePoint_im_lower E t tmin v m htmin ht (le_of_lt hv) hm
  have hdiff : |z.im - (saddlePoint E t m).im| ≤ tmin * v / 2 := by
    exact le_trans (by simpa using Complex.abs_im_le_norm (z - saddlePoint E t m)) hnear
  have hleft := (abs_le.mp hdiff).1
  linarith

/-- Uniform bounds on the inverse moments in that ball. -/
theorem norm_inverseMoment_near_saddle {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t tmin v : ℝ) (m z : ℂ)
    (htmin : 0 < tmin) (ht : tmin ≤ t) (hv : 0 < v) (hm : v ≤ m.im)
    (hnear : ‖z - saddlePoint E t m‖ ≤ tmin * v / 2) (k : ℕ) :
    ‖inverseMoment d z k‖ ≤ (1 / (tmin * v / 2)) ^ k := by
  apply norm_inverseMoment_le hN d z (tmin * v / 2) (by positivity)
  exact le_trans (saddle_neighborhood_height E t tmin v m z htmin ht hv hm hnear)
    (le_abs_self z.im)

/-- Bound on the derivative of the inverse moments on a horizontal strip. -/
theorem norm_deriv_inverseMoment_succ_le {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (z : ℂ) (η : ℝ) (hη : 0 < η)
    (hz : η ≤ |z.im|) (k : ℕ) :
    ‖deriv (fun w => inverseMoment d w (k + 1)) z‖ ≤
      ((k + 1 : ℕ) : ℝ) * (1 / η) ^ (k + 2) := by
  have hzne : z.im ≠ 0 := by
    exact abs_pos.mp (lt_of_lt_of_le hη hz)
  rw [(hasDerivAt_inverseMoment_succ d z hzne k).deriv, norm_mul, norm_neg,
    Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_inverseMoment_le hN d z η hη hz (k + 2))
    (Nat.cast_nonneg (k + 1))

/-- The second derivative of the saddle phase off the real axis: `1/t - M₂(z)`. -/
theorem hasDerivAt_deriv_saddlePhase {N : ℕ} (d : Fin N → ℝ) (E t : ℝ)
    (z : ℂ) (ht : t ≠ 0) (hz : z.im ≠ 0) :
    HasDerivAt (deriv (saddlePhase d E t))
      ((1 : ℂ) / (t : ℂ) - inverseMoment d z 2) z := by
  have hlin := ((hasDerivAt_id z).sub_const (E : ℂ)).div_const (t : ℂ)
  have hmom := hasDerivAt_inverseMoment_succ d z hz 0
  have hsum : HasDerivAt (fun w : ℂ => (w - (E : ℂ)) / (t : ℂ) +
      inverseMoment d w 1) ((1 : ℂ) / (t : ℂ) - inverseMoment d z 2) z := by
    convert! hlin.add hmom using 1
    all_goals simp only [Nat.zero_add, Nat.cast_one, neg_one_mul, sub_eq_add_neg]
  have heq : deriv (saddlePhase d E t) =ᶠ[nhds z]
      (fun w : ℂ => (w - (E : ℂ)) / (t : ℂ) + inverseMoment d w 1) := by
    filter_upwards [(isOpen_ne.preimage Complex.continuous_im).mem_nhds hz] with w hw
    exact (hasDerivAt_saddlePhase d E t w ht hw).deriv
  exact hsum.congr_of_eventuallyEq heq

/-- `|S''(z)| ≤ 1/t + η^{-2}` when `|Im z| ≥ η`. -/
theorem norm_second_deriv_saddlePhase_le {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t : ℝ) (z : ℂ) (ht : 0 < t)
    (η : ℝ) (hη : 0 < η) (hz : η ≤ |z.im|) :
    ‖deriv (deriv (saddlePhase d E t)) z‖ ≤ 1 / t + (1 / η) ^ 2 := by
  have hzne : z.im ≠ 0 := abs_pos.mp (lt_of_lt_of_le hη hz)
  rw [(hasDerivAt_deriv_saddlePhase d E t z (ne_of_gt ht) hzne).deriv]
  calc
    ‖(1 : ℂ) / (t : ℂ) - inverseMoment d z 2‖ ≤
        ‖(1 : ℂ) / (t : ℂ)‖ + ‖inverseMoment d z 2‖ := norm_sub_le _ _
    _ ≤ 1 / t + (1 / η) ^ 2 := by
      rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      exact add_le_add le_rfl (norm_inverseMoment_le hN d z η hη hz 2)

end BlockBand.GaussianBulk
