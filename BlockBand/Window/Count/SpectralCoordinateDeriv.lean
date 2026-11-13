module

public import BlockBand.Window.Count.SpectralCoordinateSpectral

/-!
# Trace derivative `D Tr f(M)[K] = Re Tr(f'(M) K)` along affine Hermitian families

*Setting.* `E` a finite-dimensional real normed space, `L : E →ₗ[ℝ] Matrix n n ℂ` real
linear, `F` a matrix, and `H x = L x + F` Hermitian for every `x`. For `f : ℝ → ℝ` of class
`C¹` (no growth condition), `ψ(x) = Tr f(H x) = Σ_j f(λ_j(H x))`.

*Result.* `hasFDerivAt_spectralSum`: `ψ` has Fréchet derivative
`v ↦ Re Tr(f'(H x) · L v)` at every `x` (`f' = deriv f`, `f'(H x) = fcalc (deriv f) (H x)`),
and `continuous_traceDeriv`: this derivative is continuous in `x` (operator norm).

*Route.* For a real polynomial `p`, `Tr p(H x) = Re Tr(aeval (H x) p)` and the noncommutative
power rule plus cyclicity of the trace give the derivative `Re Tr(p'(H x) L v)`
(`hasFDerivAt_re_trace_aeval`). On a ball around `x₀` all eigenvalues lie in `[-R, R]`
(`abs_eigenvalues_le`); Weierstrass approximation of `f'` on `[-R, R]` by `q_m` and the
antiderivatives `p_m` with `p_m(0) = f(0)` give `p_m → f`, `p_m' = q_m → f'` uniformly on
`[-R, R]`; then `hasFDerivAt_of_tendstoUniformlyOn` (Mathlib) applies, and the derivative is
continuous as a uniform limit of continuous maps.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count.SpectralCalculus

open Matrix Filter Topology Polynomial

variable {n : Type*} [Fintype n]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-!
## The trace functionals
-/

/-- The real linear functional `v ↦ Re Tr(A · L v)`. -/
def trLin (L : E →ₗ[ℝ] Matrix n n ℂ) (A : Matrix n n ℂ) : E →ₗ[ℝ] ℝ where
  toFun v := (trace (A * L v)).re
  map_add' v w := by simp [Matrix.mul_add, trace_add]
  map_smul' c v := by
    rw [map_smul, Matrix.mul_smul, trace_smul]
    simp

/-- `v ↦ Re Tr(A · L v)` as a continuous linear functional. -/
def trCLM (L : E →ₗ[ℝ] Matrix n n ℂ) (A : Matrix n n ℂ) : E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (trLin L A)

theorem trCLM_apply (L : E →ₗ[ℝ] Matrix n n ℂ) (A : Matrix n n ℂ) (v : E) :
    trCLM L A v = (trace (A * L v)).re := rfl

theorem trCLM_add (L : E →ₗ[ℝ] Matrix n n ℂ) (A B : Matrix n n ℂ) :
    trCLM L (A + B) = trCLM L A + trCLM L B := by
  ext v
  simp [trCLM_apply, Matrix.add_mul, trace_add]

theorem trCLM_sub (L : E →ₗ[ℝ] Matrix n n ℂ) (A B : Matrix n n ℂ) :
    trCLM L (A - B) = trCLM L A - trCLM L B := by
  ext v
  simp [trCLM_apply, Matrix.sub_mul, trace_sub]

/-- The entry `(a, b)` of `L v` as a continuous linear map. -/
def entryCLM (L : E →ₗ[ℝ] Matrix n n ℂ) (a b : n) : E →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => L v a b
      map_add' := fun v w => by simp
      map_smul' := fun c v => by simp }

/-- `Σ_{a,b} ‖entry_{ab} ∘ L‖`. -/
def entryBound (L : E →ₗ[ℝ] Matrix n n ℂ) : ℝ := ∑ a, ∑ b, ‖entryCLM L a b‖

theorem entryBound_nonneg (L : E →ₗ[ℝ] Matrix n n ℂ) : 0 ≤ entryBound L :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem sum_norm_entry_le (L : E →ₗ[ℝ] Matrix n n ℂ) (v : E) :
    ∑ a, ∑ b, ‖L v a b‖ ≤ entryBound L * ‖v‖ := by
  rw [entryBound, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun b _ => (entryCLM L a b).le_opNorm v

variable [DecidableEq n]

/-- Operator-norm bound `‖v ↦ Re Tr(g(A) L v)‖ ≤ (Σ_j |g(λ_j)|) · entryBound L`. -/
theorem norm_trCLM_cfc_le (L : E →ₗ[ℝ] Matrix n n ℂ) {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (g : ℝ → ℝ) : ‖trCLM L (hA.cfc g)‖ ≤ (∑ j, |g (hA.eigenvalues j)|) * entryBound L := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (entryBound_nonneg L)) fun v => ?_
  rw [trCLM_apply, Real.norm_eq_abs, mul_assoc]
  refine (abs_re_trace_cfc_mul_le hA g (L v)).trans ?_
  exact mul_le_mul_of_nonneg_left (sum_norm_entry_le L v)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-!
## Polynomials
-/

section Poly

open scoped Matrix.Norms.Operator RightActions

/-- `Tr(Σ_{i<k} H^{k-1-i} K H^i) = k Tr(H^{k-1} K)`. -/
theorem trace_sum_pow_mul (H K : Matrix n n ℂ) (k : ℕ) :
    trace (∑ i ∈ Finset.range k, H ^ (k.pred - i) * K * H ^ i) =
      (k : ℂ) * trace (H ^ (k - 1) * K) := by
  rw [trace_sum]
  have : ∀ i ∈ Finset.range k, trace (H ^ (k.pred - i) * K * H ^ i) = trace (H ^ (k - 1) * K) := by
    intro i hi
    rw [trace_mul_cycle, ← pow_add]
    congr 3
    have := Finset.mem_range.mp hi
    simp only [Nat.pred_eq_sub_one]
    omega
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Polynomial trace derivative.** `x ↦ Re Tr p(L x + F)` has derivative
`v ↦ Re Tr(p'(L x + F) L v)`. -/
theorem hasFDerivAt_re_trace_aeval (L : E →ₗ[ℝ] Matrix n n ℂ) (F : Matrix n n ℂ) (p : ℝ[X])
    (x : E) :
    HasFDerivAt (fun x => (trace (aeval (L x + F) p)).re)
      (trCLM L (aeval (L x + F) (derivative p))) x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, trace_add, Complex.add_re, trCLM_add]
    exact hp.add hq
  | monomial k c =>
    set Lc : E →L[ℝ] Matrix n n ℂ := LinearMap.toContinuousLinearMap L
    have hH : HasFDerivAt (fun x => L x + F) Lc x := Lc.hasFDerivAt.add_const F
    have hpow := hH.fun_pow' k
    set T : Matrix n n ℂ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      ((Complex.reLm.comp ((Matrix.traceLinearMap n ℂ ℂ).restrictScalars ℝ)).comp
        (LinearMap.lsmul ℝ (Matrix n n ℂ) c))
    have hT := T.hasFDerivAt.comp x hpow
    have hfun : (fun x => (trace (aeval (L x + F) (monomial k c))).re) =
        T ∘ fun x => (L x + F) ^ k := by
      funext y
      simp [T, aeval_monomial, Algebra.algebraMap_eq_smul_one, trace_smul]
    rw [hfun]
    refine hT.congr_fderiv ?_
    have hTa : ∀ M, T M = (trace (c • M)).re := fun M => rfl
    have hterm : ∀ (a b : Matrix n n ℂ) (w : E), (a •> Lc <• b) w = a * L w * b := fun _ _ _ => rfl
    ext v
    show T ((∑ i ∈ Finset.range k, (L x + F) ^ (k.pred - i) •> Lc <• (L x + F) ^ i) v) = _
    rw [_root_.sum_apply, hTa]
    simp only [hterm]
    rw [trCLM_apply, derivative_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, smul_mul_assoc, trace_smul, trace_smul, trace_sum_pow_mul]
    rw [Complex.smul_re, Complex.smul_re, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    ring

/-- Continuity of `x ↦ (v ↦ Re Tr(p(L x + F) L v))` in operator norm. -/
theorem continuous_trCLM_aeval (L : E →ₗ[ℝ] Matrix n n ℂ) (F : Matrix n n ℂ) (p : ℝ[X]) :
    Continuous fun x => trCLM L (aeval (L x + F) p) := by
  set Lc : E →L[ℝ] Matrix n n ℂ := LinearMap.toContinuousLinearMap L
  set Φ : Matrix n n ℂ →L[ℝ] (E →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
    { toFun := fun A => trCLM L A
      map_add' := fun A B => trCLM_add L A B
      map_smul' := fun c A => by
        ext v
        simp [trCLM_apply, trace_smul] }
  have hH : Continuous fun x => L x + F := Lc.continuous.add continuous_const
  exact Φ.continuous.comp ((Polynomial.continuous_aeval p).comp hH)

end Poly

end BlockBand.Window.Count.SpectralCalculus
