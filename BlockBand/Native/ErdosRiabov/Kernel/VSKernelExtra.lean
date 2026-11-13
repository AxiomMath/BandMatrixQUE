module

public import BlockBand.Native.ErdosRiabov.Kernel.VSKernel
public import BlockBand.Native.ErdosRiabov.Split.MTermsStatement

/-!
# Variance-scaling kernels: further lemmas

* `hasDerivAt_vsPropagator_left`: the backward derivative `∂_s P̂_{s,t} = -P̂_{s,t} A_s`
  (entrywise, `s, t ∈ [0,1]`, `|μ|, |μ'| < 1`), the input of the Duhamel formula;
  also `vsPropagator_mul` (cocycle `P̂_{s,t} P̂_{r,s} = P̂_{r,t}`).
* Bridges to the definitions of `Split.MTermsStatement`.
* `vsKernel_zero` (`A_0 = Y`) and `cMat_eq_vsKernel_zero` (`S = |m|⁻² T̂_0`, `m ≠ 0`).
* `vsKernel_theta_core`: the bulk clauses of `vsKernel_theta` assuming only `0 < Im z`
  (no `BulkDomain`, no `N ≥ 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Kernel

open Matrix
open BlockBand.External.ErdosRiabov (semicircleM semicircleM_dyson norm_semicircleM_lt_one)
open scoped BigOperators ComplexConjugate

variable {N : ℕ} {S : Matrix (Fin N) (Fin N) ℝ}

/-!
## Bridges to `Split.MTermsStatement`
-/

/-- `StochasticSymm` is field-for-field `Split.ProfileHyp`. -/
theorem stochasticSymm_iff_profileHyp : StochasticSymm S ↔ Split.ProfileHyp S :=
  ⟨fun h => ⟨h.nonneg, h.symm, h.rowSum⟩, fun h => ⟨h.nonneg, h.symm, h.rowSum⟩⟩

/-- `cMat S = Split.profileC S` (`algebraMap ℝ ℂ` versus the coercion). -/
theorem cMat_eq_profileC (S : Matrix (Fin N) (Fin N) ℝ) : cMat S = Split.profileC S := by
  ext x y
  simp [cMat, Split.profileC]

/-- The VS resolvent is `Split.stabOp`: `(1 - tY)⁻¹ = stabOp t S (μμ')`. -/
theorem inv_one_sub_vsY_eq_stabOp (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : ℂ) (t : ℝ) :
    (1 - (t : ℂ) • vsY S μ μ')⁻¹ = Split.stabOp t S (μ * μ') := by
  rw [smul_vsY, cMat_eq_profileC]
  rfl

/-- `A_t = μμ' profileC S * stabOp t S (μμ')`. -/
theorem vsKernel_eq_stabOp (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : ℂ) (t : ℝ) :
    vsKernel S μ μ' t = ((μ * μ') • Split.profileC S) * Split.stabOp t S (μ * μ') := by
  rw [vsKernel, inv_one_sub_vsY_eq_stabOp, vsY, cMat_eq_profileC]

/-!
## The kernel at time zero
-/

/-- `A_0 = Y` (no hypothesis). -/
theorem vsKernel_zero (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : ℂ) :
    vsKernel S μ μ' 0 = vsY S μ μ' := by
  rw [vsKernel, Complex.ofReal_zero, zero_smul, sub_zero, inv_one, Matrix.mul_one]

/-- `S = |m|⁻² T̂_0` exactly, for `μ ≠ 0`, `T̂_0 = A_0(μ, conj μ)`. -/
theorem cMat_eq_vsKernel_zero (S : Matrix (Fin N) (Fin N) ℝ) {μ : ℂ} (hμ : μ ≠ 0) :
    cMat S = (((‖μ‖ ^ 2)⁻¹ : ℝ) : ℂ) • vsKernel S μ (conj μ) 0 := by
  have hn : (‖μ‖ : ℂ) ^ 2 ≠ 0 := by
    have : (‖μ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hμ)
    exact pow_ne_zero 2 this
  rw [vsKernel_zero, vsY, smul_smul, Complex.mul_conj']
  push_cast
  rw [inv_mul_cancel₀ hn, one_smul]

/-!
## Backward derivative and cocycle
-/

/-- **Backward derivative** (`∂_s P̂_{s,t} = -P̂_{s,t} A_s`, entrywise): for a stochastic symmetric
`S`,
`|μ|, |μ'| < 1` and `s, t ∈ [0,1]`. -/
theorem hasDerivAt_vsPropagator_left (hS : StochasticSymm S) {μ μ' : ℂ} (hμ : ‖μ‖ < 1)
    (hμ' : ‖μ'‖ < 1) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (x y : Fin N) :
    HasDerivAt (fun r : ℝ => vsPropagator S μ μ' r t x y)
      (-(vsPropagator S μ μ' s t * vsKernel S μ μ' s) x y) s := by
  have hs := norm_smul_lt_one hμ hμ' hs0 hs1
  have ht := norm_smul_lt_one hμ hμ' ht0 ht1
  set Y := vsY S μ μ'
  set R := (1 - (t : ℂ) • Y)⁻¹
  have h : HasDerivAt (fun r : ℝ => ∑ z, ((1 : Matrix (Fin N) (Fin N) ℂ) x z -
      (r : ℂ) * Y x z) * R z y) (∑ z, (0 - ((1 : ℝ) : ℂ) * Y x z) * R z y) s :=
    HasDerivAt.fun_sum fun z _ =>
      ((hasDerivAt_const s _).sub ((hasDerivAt_id s).ofReal_comp.mul_const _)).mul_const _
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
  · rw [← vsKernel_eq_propagator_mul hS hs ht]
    show _ = -(Y * R) x y
    rw [Matrix.mul_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    push_cast
    ring
  · simp only [vsPropagator, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul]
    rfl

/-- Cocycle `P̂_{s,t} P̂_{r,s} = P̂_{r,t}` (`‖sμμ'‖, ‖tμμ'‖ < 1`; any `r`). -/
theorem vsPropagator_mul (hS : StochasticSymm S) {μ μ' : ℂ} {r s t : ℝ}
    (hs : ‖(s : ℂ) * (μ * μ')‖ < 1) (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) :
    vsPropagator S μ μ' s t * vsPropagator S μ μ' r s = vsPropagator S μ μ' r t := by
  set Y := vsY S μ μ'
  set Br := 1 - (r : ℂ) • Y
  set Bs := 1 - (s : ℂ) • Y
  set Rs := (1 - (s : ℂ) • Y)⁻¹
  set Rt := (1 - (t : ℂ) • Y)⁻¹
  have hXY : ∀ a : ℂ, Commute (1 - a • Y) Y := fun a =>
    (Commute.one_left Y).sub_left ((Commute.refl Y).smul_left a)
  have hc1 : Commute Rt Br :=
    (commute_inv_of_commute_cMat hS (commute_one_sub_vsY_cMat μ μ' r) ht).symm
  have hBB : Commute Bs Br := (Commute.one_right _).sub_right ((hXY _).smul_right _)
  have hRtc : Commute Rt (cMat S) :=
    (commute_inv_of_commute_cMat hS (Commute.refl (cMat S)) ht).symm
  have hRR : Commute Rt Rs := commute_inv_of_commute_cMat hS hRtc hs
  show (Bs * Rt) * (Br * Rs) = Br * Rt
  calc (Bs * Rt) * (Br * Rs) = Bs * (Rt * Br) * Rs := by simp only [Matrix.mul_assoc]
    _ = Bs * (Br * Rt) * Rs := by rw [hc1.eq]
    _ = (Bs * Br) * (Rt * Rs) := by simp only [Matrix.mul_assoc]
    _ = (Br * Bs) * (Rs * Rt) := by rw [hBB.eq, hRR.eq]
    _ = Br * ((Bs * Rs) * Rt) := by simp only [Matrix.mul_assoc]
    _ = Br * Rt := by rw [one_sub_vsY_mul_inv hS hs, Matrix.one_mul]

/-!
## The bulk clauses assuming only `0 < Im z`
-/

/-- **Core form of `vsKernel_theta`**: for a stochastic symmetric `S` on `Fin N`, `z` with
`0 < Im z`, `μ = m = semicircleM z`, `μ' = conj m`, `s, t ∈ [0,1]`, `η_r = vsHeight z r`:
`η_t > 0`; `T̂_t` real and `≥ 0`; `T̂_t 𝟙 = (Im m/η_t) 𝟙`; `Π T̂_t = T̂_t Π = (Im m/η_t) Π`, entries
`Im m/(N η_t)`; `P̂_{s,t} 𝟙 = (η_s/η_t) 𝟙`. -/
theorem vsKernel_theta_core (hS : StochasticSymm S) {z : ℂ} (hη : 0 < z.im) {s t : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < vsHeight z t ∧
    (∀ x y, (vsKernel S (semicircleM z) (conj (semicircleM z)) t x y).im = 0 ∧
      0 ≤ (vsKernel S (semicircleM z) (conj (semicircleM z)) t x y).re) ∧
    (∀ x, ∑ y, vsKernel S (semicircleM z) (conj (semicircleM z)) t x y =
      (((semicircleM z).im / vsHeight z t : ℝ) : ℂ)) ∧
    vsPi N * vsKernel S (semicircleM z) (conj (semicircleM z)) t =
      (((semicircleM z).im / vsHeight z t : ℝ) : ℂ) • vsPi N ∧
    vsKernel S (semicircleM z) (conj (semicircleM z)) t * vsPi N =
      (((semicircleM z).im / vsHeight z t : ℝ) : ℂ) • vsPi N ∧
    (∀ a b, (vsPi N * vsKernel S (semicircleM z) (conj (semicircleM z)) t) a b =
      (((semicircleM z).im / (N * vsHeight z t) : ℝ) : ℂ)) ∧
    (∀ x, ∑ y, vsPropagator S (semicircleM z) (conj (semicircleM z)) s t x y =
      ((vsHeight z s / vsHeight z t : ℝ) : ℂ)) := by
  set m := semicircleM z with hmdef
  have hm1 : ‖m‖ < 1 := norm_semicircleM_lt_one hη.ne'
  have hy : 0 < m.im := semicircleM_im_pos hη
  have hm0 : 0 < ‖m‖ := norm_pos_iff.mpr (ne_zero_of_root (semicircleM_dyson z))
  have hmc : ‖conj m‖ < 1 := by rwa [Complex.norm_conj]
  have ht := norm_smul_lt_one hm1 hmc ht0 ht1
  have hs := norm_smul_lt_one hm1 hmc hs0 hs1
  have hηt : 0 < vsHeight z t := by
    unfold vsHeight
    nlinarith
  have hc : m * conj m = ((‖m‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']
    push_cast
    ring
  have hn2 : ‖m‖ ^ 2 < 1 := by nlinarith
  have hDt : 0 < 1 - t * ‖m‖ ^ 2 := by nlinarith
  have hDs : 0 < 1 - s * ‖m‖ ^ 2 := by nlinarith
  have hrat : ‖m‖ ^ 2 / (1 - t * ‖m‖ ^ 2) = m.im / vsHeight z t := by
    rw [div_eq_div_iff hDt.ne' hηt.ne']
    linear_combination vsHeight_identity z t
  have hcast : m * conj m / (1 - (t : ℂ) * (m * conj m)) =
      ((m.im / vsHeight z t : ℝ) : ℂ) := by
    rw [hc, ← hrat]
    push_cast
    ring
  have hPi : vsPi N * vsKernel S m (conj m) t =
      ((m.im / vsHeight z t : ℝ) : ℂ) • vsPi N := by
    rw [vsPi_mul_vsKernel hS ht, hcast]
  have hratP : (1 - s * ‖m‖ ^ 2) / (1 - t * ‖m‖ ^ 2) = vsHeight z s / vsHeight z t := by
    rw [div_eq_div_iff hDt.ne' hηt.ne']
    have key : ‖m‖ ^ 2 * ((1 - s * ‖m‖ ^ 2) * vsHeight z t -
        vsHeight z s * (1 - t * ‖m‖ ^ 2)) = 0 := by
      linear_combination (1 - s * ‖m‖ ^ 2) * vsHeight_identity z t -
        (1 - t * ‖m‖ ^ 2) * vsHeight_identity z s
    have := (mul_eq_zero.mp key).resolve_left (by positivity)
    linarith
  refine ⟨hηt, fun x y => vsKernel_nonneg hS ht0 ht x y, fun x => ?_, hPi, ?_,
    fun a b => ?_, fun x => ?_⟩
  · rw [vsKernel_rowSum hS ht x, hcast]
  · rw [vsKernel_mul_vsPi hS ht, hcast]
  · have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Fin.pos a).ne'
    rw [hPi, Matrix.smul_apply, smul_eq_mul]
    simp only [vsPi]
    rw [show ((N : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_mul]
    congr 1
    field_simp
  · rw [vsPropagator_rowSum hS ht x, hc, ← hratP]
    push_cast
    ring

end BlockBand.Native.ErdosRiabov.Kernel
