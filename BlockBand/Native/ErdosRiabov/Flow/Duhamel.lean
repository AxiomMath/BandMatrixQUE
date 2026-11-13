module

public import Mathlib

/-!
# Deterministic Duhamel formula

Setting: a real Banach space `E` (in the application, `E = ℂ^{[N]^k}` viewed over `ℝ`), a generator
family `L s : E →L[ℝ] E`, and a propagator family `U s t : E →L[ℝ] E` with
`∂_s U(s,t) = -U(s,t) L_s` and `U(t,t) = I`. If `X' = L_s X + F_s` on `[t₀,t]`, then
`X_t = U(t₀,t) X_{t₀} + ∫_{t₀}^t U(s,t) F_s ds` (`duhamel_det`). Proof: the product rule for
`s ↦ U(s,t) X_s` (derivative `U(s,t) F_s`) and the fundamental theorem of calculus.

The stochastic form (with a martingale differential `dM_s`) is not treated in this file; it needs
the Itô product rule.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Flow

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Product rule: if `∂_s U(s,t) = -U(s,t) L_s` and `X' = L_s X + F_s` at `s`, then
`s ↦ U(s,t) X_s` has derivative `U(s,t) F_s` at `s`. -/
theorem hasDerivAt_propagator_apply {U : ℝ → E →L[ℝ] E} {L : E →L[ℝ] E} {X : ℝ → E}
    {F : E} {s : ℝ} (hU : HasDerivAt U (-((U s).comp L)) s)
    (hX : HasDerivAt X (L (X s) + F) s) :
    HasDerivAt (fun r => U r (X r)) (U s F) s := by
  have h := hU.clm_apply hX
  convert h using 1
  simp [map_add]

/-- Let `t₀, t` be reals, `U: ℝ → ℝ → (E →L[ℝ] E)` and `L: ℝ → (E →L[ℝ] E)` with
`∂_s U(s,t) = -U(s,t) ∘ L_s` for every `s` between `t₀` and `t`, and `U(t,t) = id`.
If
`X: ℝ → E` satisfies `X'(s) = L_s X_s + F_s` for every such `s` and `s ↦ U(s,t) F_s` is
interval integrable on `[t₀,t]`, then `X_t = U(t₀,t) X_{t₀} + ∫_{t₀}^t U(s,t) F_s ds`.
No sign condition on `t - t₀` is needed.
-/
theorem duhamel_det {U : ℝ → ℝ → E →L[ℝ] E} {L : ℝ → E →L[ℝ] E} {X F : ℝ → E} {t₀ t : ℝ}
    (hU : ∀ s ∈ uIcc t₀ t, HasDerivAt (fun r => U r t) (-((U s t).comp (L s))) s)
    (hUt : U t t = ContinuousLinearMap.id ℝ E)
    (hX : ∀ s ∈ uIcc t₀ t, HasDerivAt X (L s (X s) + F s) s)
    (hint : IntervalIntegrable (fun s => U s t (F s)) volume t₀ t) :
    X t = U t₀ t (X t₀) + ∫ s in t₀..t, U s t (F s) := by
  have hderiv : ∀ s ∈ uIcc t₀ t, HasDerivAt (fun r => U r t (X r)) (U s t (F s)) s :=
    fun s hs => hasDerivAt_propagator_apply (hU s hs) (hX s hs)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hftc, hUt]
  simp

/-- Homogeneous case of `duhamel_det` (`F ≡ 0`): every solution of `X' = L_s X` on `[t₀,t]`
satisfies `X_t = U(t₀,t) X_{t₀}`. -/
theorem duhamel_det_homogeneous {U : ℝ → ℝ → E →L[ℝ] E} {L : ℝ → E →L[ℝ] E} {X : ℝ → E}
    {t₀ t : ℝ}
    (hU : ∀ s ∈ uIcc t₀ t, HasDerivAt (fun r => U r t) (-((U s t).comp (L s))) s)
    (hUt : U t t = ContinuousLinearMap.id ℝ E)
    (hX : ∀ s ∈ uIcc t₀ t, HasDerivAt X (L s (X s)) s) :
    X t = U t₀ t (X t₀) := by
  have h := duhamel_det (F := fun _ => 0) hU hUt (fun s hs => by simpa using hX s hs)
    (by simp)
  simpa using h

end BlockBand.Native.ErdosRiabov.Flow
