module

public import BlockBand.Critical.Collar.DilationVariance.Resolvent

/-!
# Resolvent jets are factorial multiples of resolvent powers

For any matrix `A` and any `z` with `z - A` invertible, the `k`-th complex derivative of
`w ↦ (w - A)⁻¹` at `z` is `resolventJet k ((z - A)⁻¹) = (-1)^k k! (z - A)^{-(k+1)}`
(`iteratedDeriv_resolvent_eq_resolventJet`); derivatives are taken for the Euclidean
operator-norm structure on matrices (any norm gives the same derivative). Specializations:
`R = (z - (Xh - iY))⁻¹` and `R_t = (z - (Xh + tY))⁻¹`, for every `z` with `Im z > 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open Matrix Filter
open scoped Matrix.Norms.L2Operator Topology ComplexOrder

namespace BlockBand.Critical.Collar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The normalized `k`-th resolvent jet `(-1)^k k! R^{k+1}` (equal to `∂_z^k R` for
`R = (z - A)⁻¹`, see `iteratedDeriv_resolvent_eq_resolventJet`). -/
def resolventJet (k : ℕ) (R : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ((-1 : ℂ) ^ k * (k.factorial : ℂ)) • R ^ (k + 1)

/-- `∂_z (z - A)⁻¹ = -((z - A)⁻¹)²` wherever `z - A` is invertible. -/
theorem hasDerivAt_resolvent (A : Matrix ι ι ℂ) {z : ℂ}
    (hz : IsUnit (z • (1 : Matrix ι ι ℂ) - A)) :
    HasDerivAt (fun w : ℂ => (w • (1 : Matrix ι ι ℂ) - A)⁻¹)
      (-((z • (1 : Matrix ι ι ℂ) - A)⁻¹ ^ 2)) z := by
  have hp : HasDerivAt (fun w : ℂ => w • (1 : Matrix ι ι ℂ) - A) 1 z := by
    simpa using ((hasDerivAt_id z).smul_const (1 : Matrix ι ι ℂ)).sub_const A
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℂ) hz.unit).comp_hasDerivAt z hp
  simp_rw [Matrix.nonsing_inv_eq_ringInverse]
  have e : (fun w : ℂ => Ring.inverse (w • (1 : Matrix ι ι ℂ) - A)) =
      Ring.inverse ∘ fun w : ℂ => w • (1 : Matrix ι ι ℂ) - A := rfl
  rw [e]
  convert hi using 1
  rw [← Ring.inverse_unit hz.unit, IsUnit.unit_spec]
  simp [pow_two]

/-- Derivative of the powers: `∂_z ((z - A)⁻¹)^{n+1} = -(n+1) ((z - A)⁻¹)^{n+2}`. -/
theorem hasDerivAt_resolvent_pow (A : Matrix ι ι ℂ) {z : ℂ}
    (hz : IsUnit (z • (1 : Matrix ι ι ℂ) - A)) (n : ℕ) :
    HasDerivAt (fun w : ℂ => (w • (1 : Matrix ι ι ℂ) - A)⁻¹ ^ (n + 1))
      (-((n + 1 : ℕ) : ℂ) • (z • (1 : Matrix ι ι ℂ) - A)⁻¹ ^ (n + 2)) z := by
  induction n with
  | zero => simpa using hasDerivAt_resolvent A hz
  | succ n ih =>
    have h := ih.fun_mul (hasDerivAt_resolvent A hz)
    have hfun : (fun w : ℂ => (w • (1 : Matrix ι ι ℂ) - A)⁻¹ ^ (n + 1 + 1)) =
        fun w => (w • (1 : Matrix ι ι ℂ) - A)⁻¹ ^ (n + 1) * (w • (1 : Matrix ι ι ℂ) - A)⁻¹ := by
      funext w
      rw [pow_succ]
    rw [hfun]
    convert h using 1
    set Q := (z • (1 : Matrix ι ι ℂ) - A)⁻¹
    rw [Matrix.smul_mul, Matrix.mul_neg, ← pow_succ, ← pow_add]
    rw [show n + 1 + 2 = n + 2 + 1 by ring]
    simp only [Nat.cast_add, Nat.cast_one, neg_add, add_smul, neg_smul, one_smul]

/-- **Jets are factorial multiples of powers.** For every `k`, every matrix `A` and every `z`
with `z - A` invertible, `iteratedDeriv k (w ↦ (w - A)⁻¹) z = (-1)^k k! ((z - A)⁻¹)^{k+1}`. -/
theorem iteratedDeriv_resolvent_eq_resolventJet (A : Matrix ι ι ℂ) (k : ℕ) {z : ℂ}
    (hz : IsUnit (z • (1 : Matrix ι ι ℂ) - A)) :
    iteratedDeriv k (fun w : ℂ => (w • (1 : Matrix ι ι ℂ) - A)⁻¹) z =
      resolventJet k ((z • (1 : Matrix ι ι ℂ) - A)⁻¹) := by
  have hU : IsOpen {w : ℂ | IsUnit (w • (1 : Matrix ι ι ℂ) - A)} :=
    Units.isOpen.preimage (by fun_prop)
  induction k generalizing z with
  | zero => simp [resolventJet]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (fun w : ℂ => (w • (1 : Matrix ι ι ℂ) - A)⁻¹) =ᶠ[𝓝 z]
        fun w => resolventJet k ((w • (1 : Matrix ι ι ℂ) - A)⁻¹) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact ih hw
    rw [hev.deriv_eq]
    have hd := (hasDerivAt_resolvent_pow A hz k).const_smul
      ((-1 : ℂ) ^ k * (k.factorial : ℂ))
    have hd' : HasDerivAt
        (fun w : ℂ => ((-1 : ℂ) ^ k * (k.factorial : ℂ)) • (w • (1 : Matrix ι ι ℂ) - A)⁻¹ ^ (k + 1))
        (((-1 : ℂ) ^ k * (k.factorial : ℂ)) •
          (-((k + 1 : ℕ) : ℂ) • (z • (1 : Matrix ι ι ℂ) - A)⁻¹ ^ (k + 2))) z := hd
    simp only [resolventJet]
    rw [hd'.deriv, smul_smul]
    congr 1
    push_cast [Nat.factorial_succ]
    ring

/-- `R = (z - Xh + iY)⁻¹` written as `(z - X)⁻¹`, `X = Xh - iY`. -/
theorem absorbedResolvent_eq (Xh Y : Matrix ι ι ℂ) (z : ℂ) :
    absorbedResolvent Xh Y z = (z • (1 : Matrix ι ι ℂ) - (Xh - Complex.I • Y))⁻¹ := by
  rw [absorbedResolvent, sub_sub_eq_add_sub, add_comm (z • (1 : Matrix ι ι ℂ)),
    add_sub_assoc, add_comm]

/-- `R_t = (z - Xh - tY)⁻¹` written as `(z - (Xh + tY))⁻¹`. -/
theorem dilationResolvent_eq (Xh Y : Matrix ι ι ℂ) (z : ℂ) (t : ℝ) :
    dilationResolvent Xh Y z t = (z • (1 : Matrix ι ι ℂ) - (Xh + (t : ℂ) • Y))⁻¹ := by
  rw [dilationResolvent, sub_sub]

/-- `∂_z^k R = resolventJet k R` for the absorbed resolvent, every `z` with `Im z > 0`. -/
theorem iteratedDeriv_absorbedResolvent {Xh Y : Matrix ι ι ℂ} (hXh : Xh.IsHermitian)
    (hY : Y.PosSemidef) {z : ℂ} (hz : 0 < z.im) (k : ℕ) :
    iteratedDeriv k (fun w => absorbedResolvent Xh Y w) z =
      resolventJet k (absorbedResolvent Xh Y z) := by
  have hU : IsUnit (z • (1 : Matrix ι ι ℂ) - (Xh - Complex.I • Y)) := by
    have h := isUnit_dilationPencil hXh hY hz (w := Complex.I) (by simp)
    have e : z • (1 : Matrix ι ι ℂ) - (Xh - Complex.I • Y) = dilationPencil Xh Y z Complex.I := by
      unfold dilationPencil
      abel
    rwa [e]
  simp_rw [absorbedResolvent_eq]
  exact iteratedDeriv_resolvent_eq_resolventJet _ k hU

/-- `∂_z^k R_t = resolventJet k R_t` for the dilated resolvent, every real `t`, every `z`
with `Im z > 0`. -/
theorem iteratedDeriv_dilationResolvent {Xh Y : Matrix ι ι ℂ} (hXh : Xh.IsHermitian)
    (hY : Y.PosSemidef) {z : ℂ} (hz : 0 < z.im) (t : ℝ) (k : ℕ) :
    iteratedDeriv k (fun w => dilationResolvent Xh Y w t) z =
      resolventJet k (dilationResolvent Xh Y z t) := by
  have hU : IsUnit (z • (1 : Matrix ι ι ℂ) - (Xh + (t : ℂ) • Y)) := by
    have h := isUnit_dilationPencil hXh hY hz (w := -(t : ℂ)) (by simp)
    rwa [dilationPencil, neg_smul, ← sub_eq_add_neg, sub_sub] at h
  simp_rw [dilationResolvent_eq]
  exact iteratedDeriv_resolvent_eq_resolventJet _ k hU

end BlockBand.Critical.Collar
