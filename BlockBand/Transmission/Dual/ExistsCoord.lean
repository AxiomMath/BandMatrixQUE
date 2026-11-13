module

public import BlockBand.Transmission.Dual.ExistsCalc
public import BlockBand.Transmission.Dual.UniqueReg

/-!
# `exists_` at `p = 1`: global coordinates of the chamber

The flat chamber `𝒞₁ = {0 < x, 0 < y < 1}` is the image of all of `ℝ²` under
`toFlat (u, v) = (eᵘ, ℓ(v))`, `ℓ(v) = 1/(1 + e⁻ᵛ)`. In the coordinates `(u, v)` the `p = 1` dual
is the SDE with the `C^∞` (hence locally Lipschitz) coefficients
* drift `uvDrift = (D₀/2 · (1 − 2(1+x)/(x+y)), −D₀/(x+y))`,
* diagonal noise `uvSd = (√(D₀(1 + e⁻ᵘ)), √(D₀(1 + eᵛ)(1 + e⁻ᵛ)))`,
with `x = eᵘ`, `y = ℓ(v)`. Itô's formula for `toFlat` turns it into the flat dual:
`toFlat_drift` (`D toFlat[b] + ½ Σ D²toFlat[σ_a, σ_a] = flatDrift D₀ 1 ∘ toFlat`) and
`toFlat_cov` (`Σ_a (D toFlat σ_a)(D toFlat σ_a)ᵀ = flatDiff D₀ 1 ∘ toFlat`). Exit from the
sup-norm ball of radius `n` in `(u, v)` is exit from a compact subset of the chamber, so local
well-posedness with exit times from balls applies.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.Exists

open MeasureTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open scoped NNReal

/-!
## The logistic function
-/

/-- `ℓ(r) = 1/(1 + e⁻ʳ)`. -/
def lgt (r : ℝ) : ℝ := (1 + exp (-r))⁻¹

theorem one_add_exp_neg_pos (r : ℝ) : 0 < 1 + exp (-r) := by positivity

theorem lgt_pos (r : ℝ) : 0 < lgt r := inv_pos.2 (one_add_exp_neg_pos r)

theorem one_sub_lgt (r : ℝ) : 1 - lgt r = (1 + exp r)⁻¹ := by
  have h1 := one_add_exp_neg_pos r
  have h2 : 0 < 1 + exp r := by positivity
  unfold lgt
  rw [exp_neg]
  field_simp
  ring

theorem lgt_lt_one (r : ℝ) : lgt r < 1 := by
  have := one_sub_lgt r
  have h : 0 < (1 + exp r)⁻¹ := inv_pos.2 (by positivity)
  linarith

theorem contDiff_lgt : ContDiff ℝ ⊤ lgt :=
  (contDiff_const.add (contDiff_exp.comp contDiff_neg)).inv fun r => (one_add_exp_neg_pos r).ne'

theorem hasDerivAt_lgt (r : ℝ) : HasDerivAt lgt (lgt r * (1 - lgt r)) r := by
  have h1 : HasDerivAt (fun s => 1 + exp (-s)) (-exp (-r)) r := by
    simpa using ((hasDerivAt_neg r).exp).const_add 1
  have h : HasDerivAt lgt _ r := h1.inv (one_add_exp_neg_pos r).ne'
  refine h.congr_deriv ?_
  rw [one_sub_lgt]
  unfold lgt
  rw [exp_neg]
  have h2 : 0 < 1 + exp r := by positivity
  have h3 : 0 < exp r := exp_pos r
  field_simp
  ring

/-- `ℓ' = ℓ(1 − ℓ)`. -/
def lgt' (r : ℝ) : ℝ := lgt r * (1 - lgt r)

theorem hasDerivAt_lgt' (r : ℝ) : HasDerivAt lgt' (lgt' r * (1 - 2 * lgt r)) r := by
  have h : HasDerivAt lgt' _ r := (hasDerivAt_lgt r).mul ((hasDerivAt_lgt r).const_sub 1)
  refine h.congr_deriv ?_
  unfold lgt'
  ring

theorem deriv_lgt : deriv lgt = lgt' := funext fun r => (hasDerivAt_lgt r).deriv

/-!
## Second derivatives of `h(c + r s)`
-/

theorem deriv_comp_line {h h' : ℝ → ℝ} (hd : ∀ x, HasDerivAt h (h' x) x) (c s : ℝ) :
    deriv (fun r => h (c + r * s)) = fun r => h' (c + r * s) * s := by
  funext r
  have hl : HasDerivAt (fun r : ℝ => c + r * s) s r := by
    simpa using ((hasDerivAt_id r).mul_const s).const_add c
  exact ((hd _).comp r hl).deriv

theorem deriv_deriv_comp_line {h h' h'' : ℝ → ℝ} (hd : ∀ x, HasDerivAt h (h' x) x)
    (hd' : ∀ x, HasDerivAt h' (h'' x) x) (c s : ℝ) :
    deriv (deriv fun r => h (c + r * s)) 0 = h'' c * s * s := by
  rw [deriv_comp_line hd]
  have hl : HasDerivAt (fun r : ℝ => c + r * s) s 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const s).const_add c
  have := (((hd' _).comp 0 hl).mul_const s).deriv
  simpa using this

/-!
## The coordinate map
-/

/-- `(u, v) ↦ (eᵘ, ℓ(v))`, from `ℝ²` onto the flat chamber `𝒞₁`. -/
def toFlat (w : Fin 2 → ℝ) : Fin 2 → ℝ := ![exp (w 0), lgt (w 1)]

/-- Its inverse on the chamber: `(x, y) ↦ (log x, log(y/(1−y)))`. -/
def fromFlat (z : Fin 2 → ℝ) : Fin 2 → ℝ := ![Real.log (z 0), Real.log (z 1 / (1 - z 1))]

@[simp] theorem toFlat_zero (w : Fin 2 → ℝ) : toFlat w 0 = exp (w 0) := rfl
@[simp] theorem toFlat_one (w : Fin 2 → ℝ) : toFlat w 1 = lgt (w 1) := rfl

theorem contDiff_toFlat : ContDiff ℝ ⊤ toFlat := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_exp.comp (contDiff_apply ℝ ℝ 0)
  · exact contDiff_lgt.comp (contDiff_apply ℝ ℝ 1)

theorem toFlat_mem (w : Fin 2 → ℝ) : toFlat w ∈ flatChamber 1 := by
  show ofFlat 1 (toFlat w) ∈ dualChamber 1
  refine ⟨Subsingleton.strictMono _, Subsingleton.strictMono _, fun i => ?_, fun i => ?_⟩
  · have := Fin.fin_one_eq_zero i; subst this; exact exp_pos (w 0)
  · have := Fin.fin_one_eq_zero i; subst this; exact ⟨lgt_pos _, lgt_lt_one _⟩

theorem toFlat_fromFlat {z : Fin 2 → ℝ} (h0 : 0 < z 0) (h1 : 0 < z 1) (h2 : z 1 < 1) :
    toFlat (fromFlat z) = z := by
  funext i
  fin_cases i
  · simp [toFlat, fromFlat, exp_log h0]
  · have h3 : 0 < 1 - z 1 := by linarith
    simp only [toFlat, fromFlat, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
      Fin.mk_one, lgt]
    rw [exp_neg, exp_log (div_pos h1 h3)]
    field_simp
    ring

/-!
## The SDE coefficients in `(u, v)`
-/

/-- `x + y` in the coordinates `(u, v)`. -/
def uvSum (w : Fin 2 → ℝ) : ℝ := exp (w 0) + lgt (w 1)

theorem uvSum_pos (w : Fin 2 → ℝ) : 0 < uvSum w := add_pos (exp_pos _) (lgt_pos _)

/-- The drift in the coordinates `(u, v)`. -/
def uvDrift (D0 : ℝ) (w : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![D0 / 2 * (1 - 2 * (1 + exp (w 0)) / uvSum w), -D0 / uvSum w]

/-- The noise amplitudes in the coordinates `(u, v)`. -/
def uvSd (D0 : ℝ) (w : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![Real.sqrt (D0 * (1 + exp (-w 0))), Real.sqrt (D0 * ((1 + exp (w 1)) * (1 + exp (-w 1))))]

/-- The diagonal noise `σ_a = uvSd_a e_a`. -/
def uvDiff (D0 : ℝ) (a : Fin 2) (w : Fin 2 → ℝ) : Fin 2 → ℝ := Pi.single a (uvSd D0 w a)

theorem contDiff_uvSum : ContDiff ℝ ⊤ uvSum :=
  (contDiff_exp.comp (contDiff_apply ℝ ℝ 0)).add (contDiff_lgt.comp (contDiff_apply ℝ ℝ 1))

theorem contDiff_uvDrift (D0 : ℝ) : ContDiff ℝ ⊤ (uvDrift D0) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_const.mul (contDiff_const.sub ((contDiff_const.mul (contDiff_const.add
      (contDiff_exp.comp (contDiff_apply ℝ ℝ 0)))).div contDiff_uvSum fun w => (uvSum_pos w).ne'))
  · exact contDiff_const.div contDiff_uvSum fun w => (uvSum_pos w).ne'

theorem contDiff_uvSd {D0 : ℝ} (hD0 : 0 < D0) (a : Fin 2) :
    ContDiff ℝ ⊤ fun w => uvSd D0 w a := by
  fin_cases a
  · refine ContDiff.sqrt (contDiff_const.mul (contDiff_const.add
      (contDiff_exp.comp ((contDiff_apply ℝ ℝ 0).neg)))) fun w => ?_
    have : 0 < 1 + exp (-w 0) := by positivity
    exact (mul_pos hD0 this).ne'
  · refine ContDiff.sqrt (contDiff_const.mul ((contDiff_const.add (contDiff_exp.comp
      (contDiff_apply ℝ ℝ 1))).mul (contDiff_const.add (contDiff_exp.comp
      ((contDiff_apply ℝ ℝ 1).neg))))) fun w => ?_
    have h1 : 0 < 1 + exp (w 1) := by positivity
    have h2 : 0 < 1 + exp (-w 1) := by positivity
    exact (mul_pos hD0 (mul_pos h1 h2)).ne'

theorem contDiff_uvDiff {D0 : ℝ} (hD0 : 0 < D0) (a : Fin 2) : ContDiff ℝ ⊤ (uvDiff D0 a) := by
  refine contDiff_pi.2 fun i => ?_
  by_cases h : i = a
  · subst h; simpa [uvDiff] using contDiff_uvSd hD0 i
  · simp only [uvDiff, Pi.single_apply, h, ite_false]; exact contDiff_const

theorem locallyLipschitz_uvDrift (D0 : ℝ) : LocallyLipschitz (uvDrift D0) :=
  ((contDiff_uvDrift D0).of_le (by norm_num)).locallyLipschitz

theorem locallyLipschitz_uvDiff {D0 : ℝ} (hD0 : 0 < D0) (a : Fin 2) :
    LocallyLipschitz (uvDiff D0 a) :=
  ((contDiff_uvDiff hD0 a).of_le (by norm_num)).locallyLipschitz

/-!
## Derivatives of `toFlat`
-/

theorem fderiv_toFlat_apply (w v : Fin 2 → ℝ) :
    fderiv ℝ toFlat w v = ![exp (w 0) * v 0, lgt' (w 1) * v 1] := by
  have hd : DifferentiableAt ℝ toFlat w :=
    (contDiff_toFlat.differentiable (by simp)) w
  funext i
  rw [fderiv_apply_eq_deriv_line v hd]
  fin_cases i
  · simp only [toFlat, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [deriv_comp_line (h := exp) (h' := exp) (fun x => hasDerivAt_exp x)]
    simp
  · simp only [toFlat, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [deriv_comp_line (h := lgt) (h' := lgt') hasDerivAt_lgt]
    simp

theorem fderiv_fderiv_toFlat_apply (w v : Fin 2 → ℝ) :
    fderiv ℝ (fderiv ℝ toFlat) w v v =
      ![exp (w 0) * v 0 * v 0, lgt' (w 1) * (1 - 2 * lgt (w 1)) * v 1 * v 1] := by
  have hc : ContDiffAt ℝ 2 toFlat w := (contDiff_toFlat.of_le (by simp)).contDiffAt
  funext i
  rw [fderiv_fderiv_apply_eq_deriv_line v hc]
  fin_cases i
  · simp only [toFlat, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    exact deriv_deriv_comp_line (fun x => hasDerivAt_exp x) (fun x => hasDerivAt_exp x) _ _
  · simp only [toFlat, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact deriv_deriv_comp_line hasDerivAt_lgt hasDerivAt_lgt' _ _

/-!
## The flat coefficients at level one
-/

theorem flatDrift_one_zero (D0 : ℝ) (z : Fin 2 → ℝ) :
    flatDrift D0 1 z 0 = D0 / 2 * (1 + 2 * z 0 - 2 * z 0 * (1 + z 0) / (z 0 + z 1)) := by
  have e : (0 : Fin (1 + 1)) = Fin.castAdd 1 (0 : Fin 1) := rfl
  rw [e, flatDrift, Fin.append_left]
  simp only [dualDriftX, ofFlat_apply, Finset.univ_unique, Fin.default_eq_zero,
    Finset.erase_singleton, Finset.sum_empty, Finset.sum_singleton]
  have e0 : Fin.castAdd 1 (0 : Fin 1) = (0 : Fin 2) := rfl
  have e1 : Fin.natAdd 1 (0 : Fin 1) = (1 : Fin 2) := rfl
  simp only [e0, e1]
  ring

theorem flatDrift_one_one (D0 : ℝ) (z : Fin 2 → ℝ) :
    flatDrift D0 1 z 1 = D0 / 2 * (1 - 2 * z 1 - 2 * z 1 * (1 - z 1) / (z 0 + z 1)) := by
  have e : (1 : Fin (1 + 1)) = Fin.natAdd 1 (0 : Fin 1) := rfl
  rw [e, flatDrift, Fin.append_right]
  simp only [dualDriftY, ofFlat_apply, Finset.univ_unique, Fin.default_eq_zero,
    Finset.erase_singleton, Finset.sum_empty, Finset.sum_singleton]
  have e0 : Fin.castAdd 1 (0 : Fin 1) = (0 : Fin 2) := rfl
  have e1 : Fin.natAdd 1 (0 : Fin 1) = (1 : Fin 2) := rfl
  simp only [e0, e1]
  ring

theorem flatDiffDiag_one_zero (D0 : ℝ) (z : Fin 2 → ℝ) :
    flatDiffDiag D0 1 z 0 = D0 * (z 0 * (1 + z 0)) := by
  have e : (0 : Fin (1 + 1)) = Fin.castAdd 1 (0 : Fin 1) := rfl
  rw [e, flatDiffDiag, Fin.append_left]; rfl

theorem flatDiffDiag_one_one (D0 : ℝ) (z : Fin 2 → ℝ) :
    flatDiffDiag D0 1 z 1 = D0 * (z 1 * (1 - z 1)) := by
  have e : (1 : Fin (1 + 1)) = Fin.natAdd 1 (0 : Fin 1) := rfl
  rw [e, flatDiffDiag, Fin.append_right]; rfl

/-!
## Itô's formula for `toFlat`: the flat dual coefficients
-/

theorem lgt'_mul (v : ℝ) : lgt' v * ((1 + exp v) * (1 + exp (-v))) = 1 := by
  have h1 : 0 < 1 + exp v := by positivity
  have h2 := one_add_exp_neg_pos v
  unfold lgt'
  rw [one_sub_lgt]
  unfold lgt
  field_simp

theorem toFlat_drift {D0 : ℝ} (hD0 : 0 < D0) (w : Fin 2 → ℝ) :
    fderiv ℝ toFlat w (uvDrift D0 w) + (1 / 2 : ℝ) • ∑ a, fderiv ℝ (fderiv ℝ toFlat) w
      (uvDiff D0 a w) (uvDiff D0 a w) = flatDrift D0 1 (toFlat w) := by
  have hA : 0 ≤ D0 * (1 + exp (-w 0)) := by positivity
  have hB : 0 ≤ D0 * ((1 + exp (w 1)) * (1 + exp (-w 1))) := by positivity
  have hs := uvSum_pos w
  have hx := exp_pos (w 0)
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Pi.add_apply, fderiv_toFlat_apply, Pi.smul_apply,
      fderiv_fderiv_toFlat_apply, Fin.sum_univ_two, uvDiff, uvDrift, uvSd,
      Matrix.cons_val_zero, Matrix.cons_val_one, Pi.single_eq_same, smul_eq_mul,
      flatDrift_one_zero, toFlat_zero, toFlat_one, ne_eq, zero_ne_one, not_false_eq_true,
      Pi.single_eq_of_ne, mul_zero, add_zero]
    rw [mul_assoc (exp (w 0)), Real.mul_self_sqrt hA, exp_neg]
    unfold uvSum at hs ⊢
    field_simp
    ring
  · simp only [Fin.mk_one, Fin.isValue, Pi.add_apply, fderiv_toFlat_apply, Pi.smul_apply,
      fderiv_fderiv_toFlat_apply, Fin.sum_univ_two, uvDiff, uvDrift, uvSd,
      Matrix.cons_val_zero, Matrix.cons_val_one, Pi.single_eq_same, smul_eq_mul,
      flatDrift_one_one, toFlat_zero, toFlat_one, ne_eq, one_ne_zero, not_false_eq_true,
      Pi.single_eq_of_ne, mul_zero, zero_add]
    rw [mul_assoc (lgt' (w 1) * (1 - 2 * lgt (w 1))), Real.mul_self_sqrt hB]
    have hP := lgt'_mul (w 1)
    unfold uvSum at hs ⊢
    have hL : lgt' (w 1) = lgt (w 1) * (1 - lgt (w 1)) := rfl
    linear_combination (D0 / 2 * (1 - 2 * lgt (w 1))) * hP +
      (-D0 / (exp (w 0) + lgt (w 1))) * hL

theorem toFlat_cov {D0 : ℝ} (hD0 : 0 < D0) (w : Fin 2 → ℝ) :
    (Matrix.of fun i j => ∑ a, fderiv ℝ toFlat w (uvDiff D0 a w) i *
      fderiv ℝ toFlat w (uvDiff D0 a w) j) = flatDiff D0 1 (toFlat w) := by
  have hA : 0 ≤ D0 * (1 + exp (-w 0)) := by positivity
  have hB : 0 ≤ D0 * ((1 + exp (w 1)) * (1 + exp (-w 1))) := by positivity
  have hx := exp_pos (w 0)
  have hP := lgt'_mul (w 1)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, fderiv_toFlat_apply,
      Fin.sum_univ_two, uvDiff, uvSd, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.single_eq_same, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne,
      mul_zero, zero_mul, add_zero, zero_add, flatDiff, Matrix.diagonal_apply_eq,
      Matrix.diagonal_apply_ne, flatDiffDiag_one_zero, flatDiffDiag_one_one, toFlat_zero,
      toFlat_one]
  · have e : exp (w 0) * √(D0 * (1 + exp (-w 0))) * (exp (w 0) * √(D0 * (1 + exp (-w 0)))) =
        exp (w 0) * exp (w 0) * (√(D0 * (1 + exp (-w 0))) * √(D0 * (1 + exp (-w 0)))) := by ring
    rw [e, Real.mul_self_sqrt hA, exp_neg]
    field_simp
    ring
  · have e : lgt' (w 1) * √(D0 * ((1 + exp (w 1)) * (1 + exp (-w 1)))) *
        (lgt' (w 1) * √(D0 * ((1 + exp (w 1)) * (1 + exp (-w 1))))) =
        lgt' (w 1) * (lgt' (w 1) * (√(D0 * ((1 + exp (w 1)) * (1 + exp (-w 1)))) *
          √(D0 * ((1 + exp (w 1)) * (1 + exp (-w 1)))))) := by ring
    rw [e, Real.mul_self_sqrt hB]
    have : lgt' (w 1) = lgt (w 1) * (1 - lgt (w 1)) := rfl
    linear_combination (D0 * lgt' (w 1)) * hP + D0 * this

end BlockBand.Transmission.Dual.Exists
