module

public import BlockBand.Transmission.Dual.ExistsCoord
public import BlockBand.Transmission.Dual.GBase
public import BlockBand.SourceProcess.Stochastic.SDE

/-!
# The pair base process in global coordinates

Deterministic. The base process of one pair `(x, y)` with generator `L_X + L_Y` is, in the
global coordinates `(u, v) = (log x, logit y)` of `toFlat`, the SDE with
* the constant drift `uvBaseDrift = (D₀/2, 0)`,
* the same diagonal noise `uvDiff` as the `p = 1` dual (`√(D₀(1+e⁻ᵘ))`,
  `√(D₀(1+eᵛ)(1+e⁻ᵛ))`).
`toFlat_baseDrift`: Itô's formula for `toFlat` returns `flatBaseDrift D₀ 1`; the covariance is
`toFlat_cov`. Non-explosion uses `lyapBase (u, v) = ψ(u) + ψ(v)`,
`ψ(r) = log(1+eʳ) + log(1+e⁻ʳ) = 2 log(1+eʳ) − r`: it is `C^∞`, `≥ |u| + |v| ≥ ‖(u,v)‖`, and its
generator is at most `3D₀(1 + lyapBase)` (`sdeGenerator_lyapBase_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists

/-- The `(u, v)` drift of the pair base process. -/
def uvBaseDrift (D0 : ℝ) (_w : Fin 2 → ℝ) : Fin 2 → ℝ := ![D0 / 2, 0]

theorem locallyLipschitz_uvBaseDrift (D0 : ℝ) : LocallyLipschitz (uvBaseDrift D0) :=
  (LipschitzWith.const _).locallyLipschitz

theorem flatBaseDrift_one_zero (D0 : ℝ) (z : Fin 2 → ℝ) :
    flatBaseDrift D0 1 z 0 = D0 / 2 * (1 + 2 * z 0) := by
  have e : (0 : Fin (1 + 1)) = Fin.castAdd 1 (0 : Fin 1) := rfl
  rw [e, flatBaseDrift, Fin.append_left]; rfl

theorem flatBaseDrift_one_one (D0 : ℝ) (z : Fin 2 → ℝ) :
    flatBaseDrift D0 1 z 1 = D0 / 2 * (1 - 2 * z 1) := by
  have e : (1 : Fin (1 + 1)) = Fin.natAdd 1 (0 : Fin 1) := rfl
  rw [e, flatBaseDrift, Fin.append_right]; rfl

/-- **Itô for `toFlat` returns the flat base drift.** -/
theorem toFlat_baseDrift {D0 : ℝ} (hD0 : 0 < D0) (w : Fin 2 → ℝ) :
    fderiv ℝ toFlat w (uvBaseDrift D0 w) + (1 / 2 : ℝ) • ∑ a, fderiv ℝ (fderiv ℝ toFlat) w
      (uvDiff D0 a w) (uvDiff D0 a w) = flatBaseDrift D0 1 (toFlat w) := by
  have hA : 0 ≤ D0 * (1 + exp (-w 0)) := by positivity
  have hB : 0 ≤ D0 * ((1 + exp (w 1)) * (1 + exp (-w 1))) := by positivity
  have hx := exp_pos (w 0)
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Pi.add_apply, fderiv_toFlat_apply, Pi.smul_apply,
      fderiv_fderiv_toFlat_apply, Fin.sum_univ_two, uvDiff, uvBaseDrift, uvSd,
      Matrix.cons_val_zero, Matrix.cons_val_one, Pi.single_eq_same, smul_eq_mul,
      flatBaseDrift_one_zero, toFlat_zero, ne_eq, zero_ne_one, not_false_eq_true,
      Pi.single_eq_of_ne, mul_zero, add_zero]
    rw [mul_assoc (exp (w 0)), Real.mul_self_sqrt hA, exp_neg]
    field_simp
    ring
  · simp only [Fin.mk_one, Fin.isValue, Pi.add_apply, fderiv_toFlat_apply, Pi.smul_apply,
      fderiv_fderiv_toFlat_apply, Fin.sum_univ_two, uvDiff, uvBaseDrift, uvSd,
      Matrix.cons_val_zero, Matrix.cons_val_one, Pi.single_eq_same, smul_eq_mul,
      flatBaseDrift_one_one, toFlat_one, ne_eq, one_ne_zero, not_false_eq_true,
      Pi.single_eq_of_ne, mul_zero, zero_add]
    rw [mul_assoc (lgt' (w 1) * (1 - 2 * lgt (w 1))), Real.mul_self_sqrt hB]
    have hP := lgt'_mul (w 1)
    linear_combination (D0 / 2 * (1 - 2 * lgt (w 1))) * hP

/-!
## The Lyapunov function
-/

/-- Softplus `log(1 + eʳ)`. -/
def sp (r : ℝ) : ℝ := Real.log (1 + exp r)

theorem one_add_exp_pos (r : ℝ) : 0 < 1 + exp r := by positivity

theorem hasDerivAt_sp (r : ℝ) : HasDerivAt sp (lgt r) r := by
  have h := ((hasDerivAt_exp r).const_add 1).log (one_add_exp_pos r).ne'
  refine h.congr_deriv ?_
  unfold lgt
  rw [exp_neg]
  have := exp_pos r
  field_simp
  ring

theorem contDiff_sp : ContDiff ℝ ⊤ sp :=
  (contDiff_const.add contDiff_exp).log fun r => (one_add_exp_pos r).ne'

theorem le_sp (r : ℝ) : max r 0 ≤ sp r := by
  refine max_le ?_ ?_
  · have : r = Real.log (exp r) := (log_exp r).symm
    calc r = Real.log (exp r) := this
      _ ≤ sp r := Real.log_le_log (exp_pos r) (by linarith)
  · exact Real.log_nonneg (by linarith [exp_pos r])

/-- `ψ(r) = 2 log(1+eʳ) − r = log(1+eʳ) + log(1+e⁻ʳ)`. -/
def psi (r : ℝ) : ℝ := 2 * sp r - r

/-- `ψ' = 2ℓ − 1`. -/
def psi' (r : ℝ) : ℝ := 2 * lgt r - 1

theorem hasDerivAt_psi (r : ℝ) : HasDerivAt psi (psi' r) r :=
  (((hasDerivAt_sp r).const_mul 2).sub (hasDerivAt_id r)).congr_deriv (by simp [psi'])

theorem hasDerivAt_psi' (r : ℝ) : HasDerivAt psi' (2 * lgt' r) r :=
  (((hasDerivAt_lgt r).const_mul 2).sub_const 1).congr_deriv (by simp [lgt'])

theorem abs_le_psi (r : ℝ) : |r| ≤ psi r := by
  have := le_sp r
  unfold psi
  rcases le_total 0 r with h | h
  · rw [abs_of_nonneg h]; rw [max_eq_left h] at this; linarith
  · rw [abs_of_nonpos h]; rw [max_eq_right h] at this; linarith

theorem contDiff_psi : ContDiff ℝ ⊤ psi := (contDiff_const.mul contDiff_sp).sub contDiff_id

/-- The Lyapunov function `ψ(u) + ψ(v)`. -/
def lyapBase (w : Fin 2 → ℝ) : ℝ := psi (w 0) + psi (w 1)

theorem contDiff_lyapBase : ContDiff ℝ ⊤ lyapBase :=
  (contDiff_psi.comp (contDiff_apply ℝ ℝ 0)).add (contDiff_psi.comp (contDiff_apply ℝ ℝ 1))

theorem norm_le_lyapBase (w : Fin 2 → ℝ) : ‖w‖ ≤ lyapBase w := by
  have h0 := abs_le_psi (w 0)
  have h1 := abs_le_psi (w 1)
  have hn : 0 ≤ lyapBase w := by
    unfold lyapBase; linarith [abs_nonneg (w 0), abs_nonneg (w 1)]
  refine (pi_norm_le_iff_of_nonneg hn).2 fun i => ?_
  rw [Real.norm_eq_abs]
  unfold lyapBase
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]; linarith [abs_nonneg (w 1)]
  · simp only [Fin.mk_one, Fin.isValue]; linarith [abs_nonneg (w 0)]

theorem lyapBase_nonneg (w : Fin 2 → ℝ) : 0 ≤ lyapBase w := (norm_nonneg w).trans (norm_le_lyapBase w)

theorem line_lyapBase (w v : Fin 2 → ℝ) :
    (fun r : ℝ => lyapBase (w + r • v)) = fun r => psi (w 0 + r * v 0) + psi (w 1 + r * v 1) := by
  funext r; simp [lyapBase]

theorem hasDerivAt_line_lyapBase (w v : Fin 2 → ℝ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => lyapBase (w + r • v))
      (psi' (w 0 + r * v 0) * v 0 + psi' (w 1 + r * v 1) * v 1) r := by
  rw [line_lyapBase]
  have l : ∀ c s : ℝ, HasDerivAt (fun r : ℝ => c + r * s) s r := fun c s => by
    simpa using ((hasDerivAt_id r).mul_const s).const_add c
  exact ((hasDerivAt_psi _).comp r (l _ _)).add ((hasDerivAt_psi _).comp r (l _ _))

theorem fderiv_lyapBase_apply (w v : Fin 2 → ℝ) :
    fderiv ℝ lyapBase w v = psi' (w 0) * v 0 + psi' (w 1) * v 1 := by
  rw [Exists.fderiv_eq_deriv_line v (contDiff_lyapBase.differentiable (by simp) w),
    (hasDerivAt_line_lyapBase w v 0).deriv]
  simp

theorem fderiv_fderiv_lyapBase_apply (w v : Fin 2 → ℝ) :
    fderiv ℝ (fderiv ℝ lyapBase) w v v =
      2 * lgt' (w 0) * v 0 * v 0 + 2 * lgt' (w 1) * v 1 * v 1 := by
  rw [Exists.fderiv_fderiv_eq_deriv_line v ((contDiff_lyapBase.of_le (by simp)).contDiffAt)]
  have e : deriv (fun r : ℝ => lyapBase (w + r • v)) =
      fun r => psi' (w 0 + r * v 0) * v 0 + psi' (w 1 + r * v 1) * v 1 :=
    funext fun r => (hasDerivAt_line_lyapBase w v r).deriv
  rw [e]
  have l : ∀ c s : ℝ, HasDerivAt (fun r : ℝ => c + r * s) s 0 := fun c s => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const s).const_add c
  have := ((((hasDerivAt_psi' _).comp 0 (l (w 0) (v 0))).mul_const (v 0)).add
    (((hasDerivAt_psi' _).comp 0 (l (w 1) (v 1))).mul_const (v 1))).deriv
  simp only [zero_mul, add_zero] at this
  refine this.trans ?_
  ring

theorem lgt'_mul_one_add_exp_neg (r : ℝ) : lgt' r * (1 + exp (-r)) = 1 - lgt r := by
  unfold lgt' lgt
  have := one_add_exp_neg_pos r
  field_simp

theorem lgt_le_one (r : ℝ) : lgt r ≤ 1 := (lgt_lt_one r).le

/-- **The generator of the Lyapunov function is bounded.** -/
theorem sdeGenerator_lyapBase_le {D0 : ℝ} (hD0 : 0 < D0) (w : Fin 2 → ℝ) :
    sdeGenerator (uvBaseDrift D0) (uvDiff D0) lyapBase w ≤ 3 * D0 * (1 + lyapBase w) := by
  have hA : 0 ≤ D0 * (1 + exp (-w 0)) := by positivity
  have hB : 0 ≤ D0 * ((1 + exp (w 1)) * (1 + exp (-w 1))) := by positivity
  unfold sdeGenerator
  simp only [fderiv_lyapBase_apply, fderiv_fderiv_lyapBase_apply, Fin.sum_univ_two, uvDiff,
    uvBaseDrift, uvSd, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.single_eq_same, ne_eq,
    zero_ne_one, one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero,
    zero_add, Fin.isValue]
  rw [mul_assoc (2 * lgt' (w 0)), Real.mul_self_sqrt hA, mul_assoc (2 * lgt' (w 1)),
    Real.mul_self_sqrt hB]
  have e0 : 2 * lgt' (w 0) * (D0 * (1 + exp (-w 0))) = 2 * D0 * (1 - lgt (w 0)) := by
    rw [← lgt'_mul_one_add_exp_neg]; ring
  have e1 : 2 * lgt' (w 1) * (D0 * ((1 + exp (w 1)) * (1 + exp (-w 1)))) = 2 * D0 := by
    have := lgt'_mul (w 1); linear_combination 2 * D0 * this
  rw [e0, e1]
  have h1 := lgt_pos (w 0)
  have h2 := lgt_le_one (w 0)
  have h3 := lyapBase_nonneg w
  unfold psi'
  nlinarith

end BlockBand.Transmission.Dual.G
