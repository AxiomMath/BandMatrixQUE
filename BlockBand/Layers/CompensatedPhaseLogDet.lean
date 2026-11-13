module

public import Mathlib
public import BlockBand.Layers.TraceFluctuation
public import BlockBand.Layers.CompensatedIncrement

/-!
# A logarithmic determinant on matrices with positive imaginary part; the layer phase identity

* **Domain.** `cplDom n`: square complex matrices `M` with `Im ⟨v, M v⟩ ≥ c ‖v‖²` for some
  `c > 0` (`cplCoercive`); open (`cpl_isOpen_dom`), invertible with `‖M⁻¹‖ ≤ c⁻¹`
  (`cpl_coercive_inv`).
* **The logarithmic determinant** `cplLogDet M = n log i + ∫₀¹ Tr(γ(t)⁻¹ (M - i)) dt` along the
  segment `γ(t) = (1-t) i + t M` (inside `cplDom`). On `cplDom`:
  `dL(M)[H] = Tr(M⁻¹ H)` (`cpl_hasFDerivAt_logDet`: differentiation under the integral sign and
  the fundamental theorem of calculus, the integrand being `d/dt (t Tr(γ(t)⁻¹ H))`), `L` is `C¹`
  (`cpl_contDiffAt_logDet`); `L(U M U*) = L(M)` for unitary `U` (`cpl_logDet_conj`);
  `L(diag d) = Σ log d_x` (`cpl_logDet_diagonal`); `L(a K + w) = Σ_k log(a λ_k(K) + w)` for
  Hermitian `K`, `Im w > 0` (`cpl_logDet_herm`); `L(diag(A, C)) = L(A) + L(C)`
  (`cpl_logDet_fromBlocks_zero`).
* **Phase constancy along paths** (`cpl_im_logDet_path`): `Im L` is constant along a `C¹` path in
  `cplDom` with `Im Tr(M_s⁻¹ M_s') = 0`.
* **Schur path** (`cpl_im_logDet_schur`): for coercive `A`, `Z` and any `B`,
  `Im L([[A, B], [Bᴴ, Z]]) = Im L(A) + Im L(Z - Bᴴ A⁻¹ B)` (path `P_s diag(A, S) Q_s` with
  unipotent `P_s, Q_s`).
* **Phase bound** (`cpl_im_logDet_bounds`): `0 ≤ Im L(M) ≤ dim · π` on `cplDom` (congruence to
  `K + i` with `K` Hermitian along `D_s M̃ D_s`).
* **The phase identity** (`cpl_tendsto_phase`): for Hermitian invertible `D`, any `B`, `Im z > 0`
  and `κ_j = 1/(j+1) → 0`,
  `π⁻¹ Im L([[D + iκ_j, B], [Bᴴ, z + iκ_j]]) → N_-(D) + Θ_z(Bᴴ D⁻¹ B)`: the regularized phase of
  the full absorbing matrix converges to the compensated increment (Schur path, then
  `π⁻¹ Σ arg(λ_k + iκ) → N_-(D)` and continuity of `L` at `z - X₊`).

Norms: `ℓ²` operator norm on matrices (`Matrix.Norms.L2Operator`), Euclidean on vectors.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory Matrix WithLp Filter Topology
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator InnerProductSpace

/-!
## 1. The imaginary quadratic form and the coercive domain
-/

section Form

variable {n : Type} [Fintype n]

/-- `Im (v* M v)`. -/
def cplForm (M : Matrix n n ℂ) (v : n → ℂ) : ℝ := (star v ⬝ᵥ (M *ᵥ v)).im

/-- `‖v‖² = Σ |v_x|²`. -/
def cplSq (v : n → ℂ) : ℝ := ∑ x, ‖v x‖ ^ 2

/-- `Im (v* M v) ≥ c ‖v‖²` for every `v`. -/
def cplCoercive (c : ℝ) (M : Matrix n n ℂ) : Prop := ∀ v : n → ℂ, c * cplSq v ≤ cplForm M v

/-- Matrices with (uniformly) positive definite imaginary part. -/
def cplDom (n : Type) [Fintype n] : Set (Matrix n n ℂ) :=
  {M | ∃ c : ℝ, 0 < c ∧ cplCoercive c M}

theorem cpl_sq_nonneg (v : n → ℂ) : 0 ≤ cplSq v := by
  unfold cplSq; positivity

theorem cpl_star_dot_self (v : n → ℂ) : star v ⬝ᵥ v = ((cplSq v : ℝ) : ℂ) := by
  unfold cplSq dotProduct
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']

theorem cpl_norm_toLp_sq (v : n → ℂ) : ‖(toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 = cplSq v := by
  rw [EuclideanSpace.norm_sq_eq]
  rfl

theorem cpl_star_dot_mulVec_star (M : Matrix n n ℂ) (v : n → ℂ) :
    star (star v ⬝ᵥ (M *ᵥ v)) = star v ⬝ᵥ (Mᴴ *ᵥ v) := by
  rw [star_dotProduct, star_star, star_mulVec, ← dotProduct_mulVec]

theorem cpl_form_add (M N : Matrix n n ℂ) (v : n → ℂ) :
    cplForm (M + N) v = cplForm M v + cplForm N v := by
  unfold cplForm; rw [add_mulVec, dotProduct_add, Complex.add_im]

theorem cpl_form_sub (M N : Matrix n n ℂ) (v : n → ℂ) :
    cplForm (M - N) v = cplForm M v - cplForm N v := by
  unfold cplForm; rw [sub_mulVec, dotProduct_sub, Complex.sub_im]

theorem cpl_form_smul (r : ℝ) (M : Matrix n n ℂ) (v : n → ℂ) :
    cplForm (r • M) v = r * cplForm M v := by
  unfold cplForm
  rw [smul_mulVec, dotProduct_smul, Complex.smul_im, smul_eq_mul]

theorem cpl_form_herm {H : Matrix n n ℂ} (hH : H.IsHermitian) (v : n → ℂ) : cplForm H v = 0 := by
  unfold cplForm
  have h := cpl_star_dot_mulVec_star H v
  rw [hH.eq] at h
  have h2 := congrArg Complex.im h
  rw [Complex.star_def, Complex.conj_im] at h2
  linarith

theorem cpl_coercive_mono {c c' : ℝ} (hcc : c' ≤ c) {M : Matrix n n ℂ} (hM : cplCoercive c M) :
    cplCoercive c' M := fun v =>
  le_trans (mul_le_mul_of_nonneg_right hcc (cpl_sq_nonneg v)) (hM v)

variable [DecidableEq n]

theorem cpl_abs_dot_le (A : Matrix n n ℂ) (v : n → ℂ) :
    ‖star v ⬝ᵥ (A *ᵥ v)‖ ≤ ‖A‖ * cplSq v := by
  have h1 : star v ⬝ᵥ (A *ᵥ v) = ⟪(toLp 2 v : EuclideanSpace ℂ n), toLp 2 (A *ᵥ v)⟫_ℂ := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rw [h1, ← cpl_norm_toLp_sq]
  calc ‖⟪(toLp 2 v : EuclideanSpace ℂ n), toLp 2 (A *ᵥ v)⟫_ℂ‖
      ≤ ‖(toLp 2 v : EuclideanSpace ℂ n)‖ * ‖(toLp 2 (A *ᵥ v) : EuclideanSpace ℂ n)‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖(toLp 2 v : EuclideanSpace ℂ n)‖ * (‖A‖ * ‖(toLp 2 v : EuclideanSpace ℂ n)‖) := by
        gcongr; exact norm_toLp_mulVec_le A v
    _ = ‖A‖ * ‖(toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 := by ring

theorem cpl_abs_form_le (A : Matrix n n ℂ) (v : n → ℂ) : |cplForm A v| ≤ ‖A‖ * cplSq v :=
  (Complex.abs_im_le_norm _).trans (cpl_abs_dot_le A v)

theorem cpl_form_I_one (v : n → ℂ) : cplForm (Complex.I • (1 : Matrix n n ℂ)) v = cplSq v := by
  unfold cplForm
  rw [smul_mulVec, one_mulVec, dotProduct_smul, cpl_star_dot_self, smul_eq_mul, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Coercivity gives the lower bound `c ‖v‖ ≤ ‖M v‖`, hence invertibility with `‖M⁻¹‖ ≤ c⁻¹`. -/
theorem cpl_coercive_inv {c : ℝ} (hc : 0 < c) {M : Matrix n n ℂ} (hM : cplCoercive c M) :
    IsUnit M.det ∧ ‖M⁻¹‖ ≤ c⁻¹ := by
  refine isUnit_det_and_norm_inv_le_of_lower hc fun ξ => ?_
  set v : n → ℂ := ofLp ξ with hv
  have hξ : ξ = toLp 2 v := rfl
  have h1 : toEuclideanLin M ξ = toLp 2 (M *ᵥ v) := by rw [hξ, toLpLin_apply]
  have h2 := hM v
  have h3 : cplForm M v ≤ ‖ξ‖ * ‖toEuclideanLin M ξ‖ := by
    unfold cplForm
    have : star v ⬝ᵥ (M *ᵥ v) = ⟪ξ, toEuclideanLin M ξ⟫_ℂ := by
      rw [h1, hξ, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    rw [this]
    exact (Complex.im_le_norm _).trans (norm_inner_le_norm _ _)
  have h4 : cplSq v = ‖ξ‖ ^ 2 := by rw [hξ, cpl_norm_toLp_sq]
  rw [h4] at h2
  have hξ0 := norm_nonneg ξ
  rcases hξ0.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · have : ‖ξ‖ * (c * ‖ξ‖) ≤ ‖ξ‖ * ‖toEuclideanLin M ξ‖ := by nlinarith
    exact le_of_mul_le_mul_left this hpos

theorem cpl_coercive_isUnit {c : ℝ} (hc : 0 < c) {M : Matrix n n ℂ} (hM : cplCoercive c M) :
    IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (cpl_coercive_inv hc hM).1

theorem cpl_dom_isUnit {M : Matrix n n ℂ} (hM : M ∈ cplDom n) : IsUnit M := by
  obtain ⟨c, hc, h⟩ := hM
  exact cpl_coercive_isUnit hc h

/-- Perturbation: `cplCoercive c M` and `‖M' - M‖ ≤ c/2` give `cplCoercive (c/2) M'`. -/
theorem cpl_coercive_perturb {c : ℝ} {M M' : Matrix n n ℂ} (hM : cplCoercive c M)
    (h : ‖M' - M‖ ≤ c / 2) : cplCoercive (c / 2) M' := by
  intro v
  have h1 := hM v
  have h2 := cpl_abs_form_le (M' - M) v
  rw [cpl_form_sub] at h2
  have h3 : ‖M' - M‖ * cplSq v ≤ c / 2 * cplSq v :=
    mul_le_mul_of_nonneg_right h (cpl_sq_nonneg v)
  rw [abs_le] at h2
  linarith [h2.1]

end Form

/-!
## 2. The logarithmic determinant as a ray integral
-/

section LogDet

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The trace functional `H ↦ Tr H` (real-linear, continuous). -/
def cplTr : Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap n ℂ ℂ).restrictScalars ℝ)

omit [DecidableEq n] in
theorem cplTr_apply (H : Matrix n n ℂ) : cplTr H = H.trace := rfl

/-- `A ↦ (H ↦ Tr(A H))`. -/
def cplTrMul : Matrix n n ℂ →L[ℝ] Matrix n n ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.compL ℝ (Matrix n n ℂ) (Matrix n n ℂ) ℂ cplTr) ∘L
    (ContinuousLinearMap.mul ℝ (Matrix n n ℂ))

theorem cplTrMul_apply (A H : Matrix n n ℂ) : cplTrMul A H = (A * H).trace := by
  simp [cplTrMul, cplTr_apply]

/-- The segment `t ↦ (1-t) i + t M` from `i·1` to `M`. -/
def cplRay (M : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  (1 - t) • (Complex.I • (1 : Matrix n n ℂ)) + t • M

/-- The integrand `Tr(γ(t)⁻¹ (M - i))`. -/
def cplInteg (M : Matrix n n ℂ) (t : ℝ) : ℂ :=
  (Ring.inverse (cplRay M t) * (M - Complex.I • (1 : Matrix n n ℂ))).trace

/-- **The logarithmic determinant** `L(M) = n log i + ∫₀¹ Tr(γ(t)⁻¹ (M - i)) dt`,
`γ(t) = (1-t) i + t M`. On `cplDom` it is a holomorphic branch of `log det` with
`dL(M) = Tr(M⁻¹ dM)`; only this derivative and its normalization are used. -/
def cplLogDet (M : Matrix n n ℂ) : ℂ :=
  (Fintype.card n : ℂ) * (Real.pi / 2 * Complex.I) + ∫ t in (0 : ℝ)..1, cplInteg M t

omit [Fintype n] in
theorem cpl_ray_one (M : Matrix n n ℂ) : cplRay M 1 = M := by
  simp [cplRay]

theorem cpl_form_ray (M : Matrix n n ℂ) (t : ℝ) (v : n → ℂ) :
    cplForm (cplRay M t) v = (1 - t) * cplSq v + t * cplForm M v := by
  rw [cplRay, cpl_form_add, cpl_form_smul, cpl_form_smul, cpl_form_I_one]

theorem cpl_ray_coercive {c : ℝ} {M : Matrix n n ℂ} (_hc : 0 < c) (hM : cplCoercive c M) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : cplCoercive (min 1 c) (cplRay M t) := by
  intro v
  rw [cpl_form_ray]
  have h1 := hM v
  have hs := cpl_sq_nonneg v
  have hm1 : min 1 c ≤ 1 := min_le_left _ _
  have hmc : min 1 c ≤ c := min_le_right _ _
  have e1 : min 1 c * cplSq v = (1 - t) * (min 1 c * cplSq v) + t * (min 1 c * cplSq v) := by
    ring
  rw [e1]
  have ht1' : 0 ≤ 1 - t := by linarith
  have a1 : (1 - t) * (min 1 c * cplSq v) ≤ (1 - t) * cplSq v := by
    apply mul_le_mul_of_nonneg_left _ ht1'
    nlinarith
  have a2 : t * (min 1 c * cplSq v) ≤ t * cplForm M v := by
    apply mul_le_mul_of_nonneg_left _ ht0
    nlinarith
  linarith

theorem cpl_min_pos {c : ℝ} (hc : 0 < c) : 0 < min 1 c := lt_min one_pos hc

theorem cpl_ray_isUnit {c : ℝ} {M : Matrix n n ℂ} (hc : 0 < c) (hM : cplCoercive c M) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : IsUnit (cplRay M t) :=
  cpl_coercive_isUnit (cpl_min_pos hc) (cpl_ray_coercive hc hM ht0 ht1)

theorem cpl_ray_inv_le {c : ℝ} {M : Matrix n n ℂ} (hc : 0 < c) (hM : cplCoercive c M) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ‖Ring.inverse (cplRay M t)‖ ≤ (min 1 c)⁻¹ := by
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  exact (cpl_coercive_inv (cpl_min_pos hc) (cpl_ray_coercive hc hM ht0 ht1)).2

theorem cpl_hasDerivAt_ray (M : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (cplRay M) (M - Complex.I • (1 : Matrix n n ℂ)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (1 - s) • (Complex.I • (1 : Matrix n n ℂ)))
      ((-1 : ℝ) • (Complex.I • (1 : Matrix n n ℂ))) t :=
    ((hasDerivAt_id t).const_sub 1).smul_const _
  have h2 : HasDerivAt (fun s : ℝ => s • M) ((1 : ℝ) • M) t := (hasDerivAt_id t).smul_const M
  have := h1.add h2
  rw [neg_one_smul, one_smul, neg_add_eq_sub] at this
  exact this

omit [Fintype n] in
theorem cpl_continuous_ray (M : Matrix n n ℂ) : Continuous (cplRay M) := by
  unfold cplRay; fun_prop

theorem cpl_continuousOn_inv_ray {c : ℝ} {M : Matrix n n ℂ} (hc : 0 < c) (hM : cplCoercive c M) :
    ContinuousOn (fun t => Ring.inverse (cplRay M t)) (Set.Icc 0 1) := by
  intro t ht
  have hu := cpl_ray_isUnit hc hM ht.1 ht.2
  have h := NormedRing.inverse_continuousAt hu.unit
  rw [IsUnit.unit_spec] at h
  exact (h.comp (cpl_continuous_ray M).continuousAt).continuousWithinAt

theorem cpl_measurable_integ (M : Matrix n n ℂ) : Measurable (cplInteg M) := by
  have h1 : Measurable (fun t => Ring.inverse (cplRay M t)) := by
    have heq : (fun t => Ring.inverse (cplRay M t)) = (fun A : Matrix n n ℂ => A⁻¹) ∘ cplRay M := by
      funext t; simp [Matrix.nonsing_inv_eq_ringInverse]
    rw [heq]
    exact (measurable_matrix_inv (ι := n)).comp (cpl_continuous_ray M).measurable
  unfold cplInteg
  exact (Continuous.matrix_trace (continuous_id.matrix_mul continuous_const)).measurable.comp h1

theorem cpl_continuousOn_integ {c : ℝ} {M : Matrix n n ℂ} (hc : 0 < c) (hM : cplCoercive c M) :
    ContinuousOn (cplInteg M) (Set.Icc 0 1) := by
  have h := cpl_continuousOn_inv_ray hc hM
  unfold cplInteg
  exact (Continuous.matrix_trace (continuous_id.matrix_mul continuous_const)).comp_continuousOn h

/-- The `M`-derivative of the integrand: `H ↦ Tr(R H) - t Tr(R H R (M - i))`, `R = γ(t)⁻¹`. -/
def cplIntegD (M : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ →L[ℝ] ℂ :=
  cplTr ∘L (ContinuousLinearMap.mul ℝ (Matrix n n ℂ) (Ring.inverse (cplRay M t)) -
    t • (((ContinuousLinearMap.mul ℝ (Matrix n n ℂ)).flip
      (Ring.inverse (cplRay M t) * (M - Complex.I • (1 : Matrix n n ℂ)))) ∘L
      ContinuousLinearMap.mul ℝ (Matrix n n ℂ) (Ring.inverse (cplRay M t))))

theorem cplIntegD_apply (M : Matrix n n ℂ) (t : ℝ) (H : Matrix n n ℂ) :
    cplIntegD M t H = (Ring.inverse (cplRay M t) * H).trace -
      t • (Ring.inverse (cplRay M t) * H *
        (Ring.inverse (cplRay M t) * (M - Complex.I • (1 : Matrix n n ℂ)))).trace := by
  simp [cplIntegD, cplTr_apply]

theorem cpl_hasFDerivAt_integ {M : Matrix n n ℂ} {t : ℝ} (hu : IsUnit (cplRay M t)) :
    HasFDerivAt (fun M' => cplInteg M' t) (cplIntegD M t) M := by
  have hg1 : HasFDerivAt (fun M' : Matrix n n ℂ => cplRay M' t)
      (t • ContinuousLinearMap.id ℝ (Matrix n n ℂ)) M := by
    have := ((ContinuousLinearMap.id ℝ (Matrix n n ℂ)).hasFDerivAt (x := M)).const_smul t
    exact this.const_add _
  have hinv : HasFDerivAt Ring.inverse
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑hu.unit⁻¹ ↑hu.unit⁻¹))
      (cplRay M t) := by
    have := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
    rwa [IsUnit.unit_spec] at this
  have hR : (↑hu.unit⁻¹ : Matrix n n ℂ) = Ring.inverse (cplRay M t) := by
    rw [← Ring.inverse_unit, IsUnit.unit_spec]
  have hg2 : HasFDerivAt (fun M' : Matrix n n ℂ => M' - Complex.I • (1 : Matrix n n ℂ))
      (ContinuousLinearMap.id ℝ (Matrix n n ℂ)) M :=
    ((ContinuousLinearMap.id ℝ (Matrix n n ℂ)).hasFDerivAt).sub_const _
  have hprod := (hinv.comp M hg1).mul' hg2
  have htr := cplTr.hasFDerivAt.comp M hprod
  refine htr.congr_fderiv ?_
  ext H
  rw [cplIntegD_apply]
  simp [hR, cplTr_apply, ContinuousLinearMap.mulLeftRight_apply, Matrix.mul_assoc, sub_eq_add_neg]

theorem cpl_continuousOn_integD {c : ℝ} {M : Matrix n n ℂ} (hc : 0 < c) (hM : cplCoercive c M) :
    ContinuousOn (cplIntegD M) (Set.Icc 0 1) := by
  have hR := cpl_continuousOn_inv_ray hc hM
  have h1 : ContinuousOn (fun t => ContinuousLinearMap.mul ℝ (Matrix n n ℂ)
      (Ring.inverse (cplRay M t))) (Set.Icc 0 1) :=
    (ContinuousLinearMap.mul ℝ (Matrix n n ℂ)).continuous.comp_continuousOn hR
  have h2 : ContinuousOn (fun t => (ContinuousLinearMap.mul ℝ (Matrix n n ℂ)).flip
      (Ring.inverse (cplRay M t) * (M - Complex.I • (1 : Matrix n n ℂ)))) (Set.Icc 0 1) :=
    (ContinuousLinearMap.mul ℝ (Matrix n n ℂ)).flip.continuous.comp_continuousOn
      (hR.mul continuousOn_const)
  have h3 := (continuousOn_id.smul (h2.clm_comp h1))
  exact continuousOn_const.clm_comp (h1.sub h3)

theorem cpl_norm_integD_le {c : ℝ} {M : Matrix n n ℂ} (hc : 0 < c) (hM : cplCoercive c M) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖cplIntegD M t‖ ≤ Fintype.card n * ((min 1 c)⁻¹ + (min 1 c)⁻¹ ^ 2 *
      ‖M - Complex.I • (1 : Matrix n n ℂ)‖) := by
  have hm := cpl_min_pos hc
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun H => ?_
  rw [cplIntegD_apply]
  set R := Ring.inverse (cplRay M t) with hRdef
  set K := M - Complex.I • (1 : Matrix n n ℂ)
  have hR : ‖R‖ ≤ (min 1 c)⁻¹ := cpl_ray_inv_le hc hM ht0 ht1
  have h1 := tfl_trace_le (R * H)
  have h2 := tfl_trace_le (R * H * (R * K))
  have hn : (0 : ℝ) ≤ Fintype.card n := Nat.cast_nonneg _
  have hRH : ‖R * H‖ ≤ (min 1 c)⁻¹ * ‖H‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  have hRK : ‖R * K‖ ≤ (min 1 c)⁻¹ * ‖K‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  have hRHRK : ‖R * H * (R * K)‖ ≤ (min 1 c)⁻¹ * ‖H‖ * ((min 1 c)⁻¹ * ‖K‖) :=
    (norm_mul_le _ _).trans (mul_le_mul hRH hRK (norm_nonneg _) (by positivity))
  have ht : ‖t • (R * H * (R * K)).trace‖ ≤ ‖(R * H * (R * K)).trace‖ := by
    rw [norm_smul, Real.norm_of_nonneg ht0]
    exact mul_le_of_le_one_left (norm_nonneg _) ht1
  calc ‖(R * H).trace - t • (R * H * (R * K)).trace‖
      ≤ ‖(R * H).trace‖ + ‖t • (R * H * (R * K)).trace‖ := norm_sub_le _ _
    _ ≤ Fintype.card n * ((min 1 c)⁻¹ * ‖H‖) +
        Fintype.card n * ((min 1 c)⁻¹ * ‖H‖ * ((min 1 c)⁻¹ * ‖K‖)) := by
        gcongr
        · exact h1.trans (mul_le_mul_of_nonneg_left hRH hn)
        · exact ht.trans (h2.trans (mul_le_mul_of_nonneg_left hRHRK hn))
    _ = Fintype.card n * ((min 1 c)⁻¹ + (min 1 c)⁻¹ ^ 2 * ‖K‖) * ‖H‖ := by ring

/-- Fundamental theorem of calculus along the ray: `∫₀¹ dI(M,t)[H] dt = Tr(M⁻¹ H)`, since the
integrand is `d/dt (t Tr(γ(t)⁻¹ H))` (trace cyclicity). -/
theorem cpl_integral_integD_apply {c : ℝ} {M : Matrix n n ℂ} (hc : 0 < c) (hM : cplCoercive c M)
    (H : Matrix n n ℂ) :
    ∫ t in (0 : ℝ)..1, cplIntegD M t H = (Ring.inverse M * H).trace := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt
      (fun s : ℝ => s • (Ring.inverse (cplRay M s) * H).trace) (cplIntegD M t H) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hu := cpl_ray_isUnit hc hM ht.1 ht.2
    have hinv : HasFDerivAt Ring.inverse
        (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑hu.unit⁻¹ ↑hu.unit⁻¹))
        (cplRay M t) := by
      have := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
      rwa [IsUnit.unit_spec] at this
    have hR : (↑hu.unit⁻¹ : Matrix n n ℂ) = Ring.inverse (cplRay M t) := by
      rw [← Ring.inverse_unit, IsUnit.unit_spec]
    have h1 := (hinv.comp_hasDerivAt t (cpl_hasDerivAt_ray M t)).mul_const H
    have h2 := cplTr.hasFDerivAt.comp_hasDerivAt t h1
    have h3 := (hasDerivAt_id t).smul h2
    refine (show HasDerivAt (fun s : ℝ => s • (Ring.inverse (cplRay M s) * H).trace) _ t
      from h3).congr_deriv ?_
    rw [cplIntegD_apply]
    simp only [_root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, hR,
      cplTr_apply, Function.comp_apply, id, one_smul]
    set R := Ring.inverse (cplRay M t)
    set K := M - Complex.I • (1 : Matrix n n ℂ)
    have hcyc : (R * H * (R * K)).trace = (R * K * R * H).trace := by
      rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [hcyc, Matrix.neg_mul, Matrix.trace_neg, smul_neg]
    ring
  have hint : IntervalIntegrable (fun t => cplIntegD M t H) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    exact (cpl_continuousOn_integD hc hM).clm_apply continuousOn_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [cpl_ray_one]

/-- **The derivative of the logarithmic determinant**: on `cplDom`,
`dL(M)[H] = Tr(M⁻¹ H)` (differentiation under the integral sign, then
`cpl_integral_integD_apply`). -/
theorem cpl_hasFDerivAt_logDet {M : Matrix n n ℂ} (hM : M ∈ cplDom n) :
    HasFDerivAt cplLogDet (cplTrMul (Ring.inverse M)) M := by
  obtain ⟨c, hc, hcM⟩ := hM
  have hc2 : 0 < c / 2 := half_pos hc
  set Bd : ℝ := Fintype.card n * ((min 1 (c / 2))⁻¹ + (min 1 (c / 2))⁻¹ ^ 2 *
    (‖M‖ + c / 2 + ‖Complex.I • (1 : Matrix n n ℂ)‖)) with hBd
  have hs : ∀ M' ∈ Metric.ball M (c / 2), cplCoercive (c / 2) M' ∧
      ‖M' - Complex.I • (1 : Matrix n n ℂ)‖ ≤ ‖M‖ + c / 2 + ‖Complex.I • (1 : Matrix n n ℂ)‖ := by
    intro M' hM'
    rw [Metric.mem_ball, dist_eq_norm] at hM'
    refine ⟨cpl_coercive_perturb hcM hM'.le, ?_⟩
    have : ‖M'‖ ≤ ‖M‖ + c / 2 := by
      have := norm_le_norm_add_norm_sub' M' M
      linarith [norm_sub_rev M' M]
    linarith [norm_sub_le M' (Complex.I • (1 : Matrix n n ℂ))]
  have hIoc : Set.uIoc (0 : ℝ) 1 = Set.Ioc 0 1 := Set.uIoc_of_le zero_le_one
  have key := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (a := 0) (b := 1) (F := fun M' t => cplInteg M' t) (F' := cplIntegD) (x₀ := M)
    (bound := fun _ => Bd) (Metric.ball_mem_nhds M hc2)
    (Filter.Eventually.of_forall fun M' => (cpl_measurable_integ M').aestronglyMeasurable)
    (by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le zero_le_one]
      exact cpl_continuousOn_integ hc hcM)
    (by
      rw [hIoc]
      exact ((cpl_continuousOn_integD hc hcM).mono Set.Ioc_subset_Icc_self).aestronglyMeasurable
        measurableSet_Ioc)
    (Filter.Eventually.of_forall fun t ht M' hM' => by
      rw [hIoc] at ht
      obtain ⟨h1, h2⟩ := hs M' hM'
      refine (cpl_norm_integD_le hc2 h1 ht.1.le ht.2).trans ?_
      have hm := cpl_min_pos hc2
      rw [hBd]
      gcongr)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t ht M' hM' => by
      rw [hIoc] at ht
      exact cpl_hasFDerivAt_integ (cpl_ray_isUnit hc2 (hs M' hM').1 ht.1.le ht.2))
  have h2 := key.const_add ((Fintype.card n : ℂ) * (Real.pi / 2 * Complex.I))
  refine h2.congr_fderiv ?_
  ext H
  have hco : ContinuousOn (cplIntegD M) (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact cpl_continuousOn_integD hc hcM
  have hint := ContinuousOn.intervalIntegrable (E := Matrix n n ℂ →L[ℝ] ℂ) (μ := volume) hco
  rw [ContinuousLinearMap.intervalIntegral_apply hint, cpl_integral_integD_apply hc hcM,
    cplTrMul_apply]

theorem cpl_continuousAt_logDet {M : Matrix n n ℂ} (hM : M ∈ cplDom n) :
    ContinuousAt cplLogDet M :=
  (cpl_hasFDerivAt_logDet hM).continuousAt

theorem cpl_isOpen_dom : IsOpen (cplDom n) := by
  rw [Metric.isOpen_iff]
  rintro M ⟨c, hc, hM⟩
  refine ⟨c / 2, half_pos hc, fun M' hM' => ⟨c / 2, half_pos hc, ?_⟩⟩
  rw [Metric.mem_ball, dist_eq_norm] at hM'
  exact cpl_coercive_perturb hM hM'.le

/-- `L` is `C¹` near every point of `cplDom` (its derivative `M ↦ Tr(M⁻¹ ·)` is continuous). -/
theorem cpl_contDiffAt_logDet {M : Matrix n n ℂ} (hM : M ∈ cplDom n) :
    ContDiffAt ℝ 1 cplLogDet M := by
  rw [show (1 : WithTop ℕ∞) = ((0 : ℕ) : WithTop ℕ∞) + 1 from rfl]
  rw [contDiffAt_succ_iff_hasFDerivAt]
  refine ⟨fun M' => cplTrMul (Ring.inverse M'),
    ⟨cplDom n, cpl_isOpen_dom.mem_nhds hM, fun M' hM' => cpl_hasFDerivAt_logDet hM'⟩, ?_⟩
  have hu := cpl_dom_isUnit hM
  have h1 : ContDiffAt ℝ ((0 : ℕ) : WithTop ℕ∞) Ring.inverse (hu.unit : Matrix n n ℂ) :=
    contDiffAt_ringInverse ℝ hu.unit
  rw [IsUnit.unit_spec] at h1
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Matrix n n ℂ) (F := Matrix n n ℂ →L[ℝ] ℂ)
    cplTrMul).contDiffAt.comp M h1

end LogDet

/-!
## 3. Normalization: unitary invariance, diagonal matrices, Hermitian shifts
-/

section Normalization

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cpl_ringInverse_conj {U : Matrix n n ℂ} (hU1 : star U * U = 1) (hU2 : U * star U = 1)
    (A : Matrix n n ℂ) : Ring.inverse (U * A * star U) = U * Ring.inverse A * star U := by
  rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse, Matrix.mul_inv_rev,
    Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hU2, Matrix.inv_eq_left_inv hU1, Matrix.mul_assoc]

theorem cpl_ray_conj {U : Matrix n n ℂ} (hU2 : U * star U = 1) (M : Matrix n n ℂ) (t : ℝ) :
    cplRay (U * M * star U) t = U * cplRay M t * star U := by
  unfold cplRay
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU2]

/-- **Unitary invariance** `L(U M U*) = L(M)`. -/
theorem cpl_logDet_conj {U : Matrix n n ℂ} (hU1 : star U * U = 1) (hU2 : U * star U = 1)
    (M : Matrix n n ℂ) : cplLogDet (U * M * star U) = cplLogDet M := by
  unfold cplLogDet
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  unfold cplInteg
  rw [cpl_ray_conj hU2, cpl_ringInverse_conj hU1 hU2]
  have e : U * M * star U - Complex.I • (1 : Matrix n n ℂ) =
      U * (M - Complex.I • (1 : Matrix n n ℂ)) * star U := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU2]
  rw [e]
  calc (U * Ring.inverse (cplRay M t) * star U * (U * (M - Complex.I • 1) * star U)).trace
      = (U * (Ring.inverse (cplRay M t) * (M - Complex.I • 1)) * star U).trace := by
        congr 1
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (star U) U, hU1, Matrix.one_mul]
    _ = (star U * U * (Ring.inverse (cplRay M t) * (M - Complex.I • 1))).trace := by
        rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = (Ring.inverse (cplRay M t) * (M - Complex.I • 1)).trace := by rw [hU1, Matrix.one_mul]

/-- The scalar ray `(1-t) i + t w`. -/
def cplSRay (w : ℂ) (t : ℝ) : ℂ := ((1 - t : ℝ) : ℂ) * Complex.I + (t : ℂ) * w

theorem cpl_sRay_im (w : ℂ) (t : ℝ) : (cplSRay w t).im = (1 - t) + t * w.im := by
  simp [cplSRay]

theorem cpl_sRay_im_pos {w : ℂ} (hw : 0 < w.im) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < (cplSRay w t).im := by
  rw [cpl_sRay_im]
  rcases ht1.lt_or_eq with h | h
  · have : 0 ≤ t * w.im := mul_nonneg ht0 hw.le
    linarith
  · rw [h]; linarith

theorem cpl_sRay_ne_zero {w : ℂ} (hw : 0 < w.im) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    cplSRay w t ≠ 0 := fun h => by
  have := cpl_sRay_im_pos hw ht0 ht1
  rw [h, Complex.zero_im] at this
  exact lt_irrefl 0 this

/-- The scalar identity `∫₀¹ (w - i)/((1-t) i + t w) dt = log w - log i` for `Im w > 0`. -/
theorem cpl_scalar_integral {w : ℂ} (hw : 0 < w.im) :
    ∫ t in (0 : ℝ)..1, (w - Complex.I) / cplSRay w t = Complex.log w - Complex.log Complex.I := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Complex.log (cplSRay w s)) ((w - Complex.I) / cplSRay w t) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have h1 : HasDerivAt (cplSRay w) (w - Complex.I) t := by
      have ha : HasDerivAt (fun s : ℝ => ((1 - s : ℝ) : ℂ)) (-1) t := by
        have := ((hasDerivAt_id t).const_sub 1).ofReal_comp
        simpa using this
      have hb : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
      have := (ha.mul_const Complex.I).add (hb.mul_const w)
      refine (show HasDerivAt (fun y : ℝ => ((1 - y : ℝ) : ℂ) * Complex.I + (y : ℂ) * w) _ t
        from this).congr_deriv ?_
      ring
    have hslit : cplSRay w t ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inr (cpl_sRay_im_pos hw ht.1 ht.2).ne')
    exact h1.clog_real hslit
  have hcont : ContinuousOn (fun t => (w - Complex.I) / cplSRay w t) (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    refine continuousOn_const.div (by unfold cplSRay; fun_prop) fun t ht =>
      cpl_sRay_ne_zero hw ht.1 ht.2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp [cplSRay]

omit [Fintype n] in
theorem cpl_ray_diagonal (d : n → ℂ) (t : ℝ) :
    cplRay (diagonal d) t = diagonal (fun x => cplSRay (d x) t) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [cplRay, cplSRay, Complex.real_smul]
  · simp [cplRay, diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem cpl_ringInverse_diagonal {v : n → ℂ} (hv : ∀ x, v x ≠ 0) :
    Ring.inverse (diagonal v) = diagonal (fun x => (v x)⁻¹) := by
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  refine Matrix.inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal]
  convert diagonal_one with x
  exact inv_mul_cancel₀ (hv x)

/-- **Diagonal matrices**: `L(diag d) = Σ log d_x` when every `Im d_x > 0`. -/
theorem cpl_logDet_diagonal {d : n → ℂ} (hd : ∀ x, 0 < (d x).im) :
    cplLogDet (diagonal d) = ∑ x, Complex.log (d x) := by
  unfold cplLogDet
  have heq : Set.EqOn (cplInteg (diagonal d))
      (fun t => ∑ x, (d x - Complex.I) / cplSRay (d x) t) (Set.uIcc 0 1) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    unfold cplInteg
    rw [cpl_ray_diagonal, cpl_ringInverse_diagonal fun x => cpl_sRay_ne_zero (hd x) ht.1 ht.2]
    have e : diagonal d - Complex.I • (1 : Matrix n n ℂ) = diagonal (fun x => d x - Complex.I) := by
      ext i j
      by_cases h : i = j
      · subst h; simp
      · simp [diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    rw [e, diagonal_mul_diagonal, trace_diagonal]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [div_eq_inv_mul]
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_finsetSum]
  · simp_rw [cpl_scalar_integral (hd _)]
    rw [Finset.sum_sub_distrib, Complex.log_I, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  · intro x _
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    refine continuousOn_const.div (by unfold cplSRay; fun_prop) fun t ht =>
      cpl_sRay_ne_zero (hd x) ht.1 ht.2

/-- **Hermitian shifts**: for Hermitian `K`, real `a` and `Im w > 0`,
`L(a K + w) = Σ_k log(a λ_k + w)` over the eigenvalues of `K`. -/
theorem cpl_logDet_herm {K : Matrix n n ℂ} (hK : K.IsHermitian) (a : ℝ) {w : ℂ}
    (hw : 0 < w.im) :
    cplLogDet (a • K + w • (1 : Matrix n n ℂ)) =
      ∑ k, Complex.log ((a * hK.eigenvalues k : ℝ) + w) := by
  set U : Matrix n n ℂ := (hK.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hU1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hK.eigenvectorUnitary.2
  have hU2 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hK.eigenvectorUnitary.2
  have hspec : K = U * diagonal (fun k => ((hK.eigenvalues k : ℝ) : ℂ)) * star U := by
    have := hK.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have e0 : a • diagonal (fun k => ((hK.eigenvalues k : ℝ) : ℂ)) + w • (1 : Matrix n n ℂ) =
      diagonal (fun k => ((a * hK.eigenvalues k : ℝ) : ℂ) + w) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Complex.real_smul]
    · simp [diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have e : a • K + w • (1 : Matrix n n ℂ) =
      U * diagonal (fun k => ((a * hK.eigenvalues k : ℝ) : ℂ) + w) * star U := by
    rw [← e0]
    conv_lhs => rw [hspec]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU2]
  rw [e, cpl_logDet_conj hU1 hU2, cpl_logDet_diagonal]
  intro k
  simpa using hw

end Normalization

/-!
## 4. Constancy of the phase along paths, block-diagonal additivity, the Schur path
-/

section Paths

variable {n : Type} [Fintype n] [DecidableEq n]

/-- **Path lemma.** Along a differentiable path in `cplDom` with `Im Tr(M_s⁻¹ M_s') = 0`, the
phase `Im L` is constant. -/
theorem cpl_im_logDet_path {Mp Mp' : ℝ → Matrix n n ℂ}
    (hd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Mp (Mp' s) s)
    (hdom : ∀ s ∈ Set.Icc (0 : ℝ) 1, Mp s ∈ cplDom n)
    (hre : ∀ s ∈ Set.Icc (0 : ℝ) 1, ((Ring.inverse (Mp s) * Mp' s).trace).im = 0) :
    (cplLogDet (Mp 1)).im = (cplLogDet (Mp 0)).im := by
  have hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun s => (cplLogDet (Mp s)).im)
      (((Ring.inverse (Mp s) * Mp' s).trace).im) (Set.Icc 0 1) s := by
    intro s hs
    have h1 := (cpl_hasFDerivAt_logDet (hdom s hs)).comp_hasDerivAt s (hd s hs)
    have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s h1
    refine (show HasDerivAt (fun s => (cplLogDet (Mp s)).im) _ s from h2).hasDerivWithinAt.congr_deriv
      ?_
    simp [cplTrMul_apply]
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (C := 0) hder
    (fun s hs => by rw [hre s (Set.Ico_subset_Icc_self hs), norm_zero]) 1
    (Set.right_mem_Icc.mpr zero_le_one)
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  exact h

end Paths

section Blocks

variable {m p : Type} [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]

omit [DecidableEq m] [DecidableEq p] in
theorem cpl_trace_fromBlocks (A : Matrix m m ℂ) (B : Matrix m p ℂ) (C : Matrix p m ℂ)
    (D : Matrix p p ℂ) : (fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

omit [Fintype m] [Fintype p] in
theorem cpl_I_one_fromBlocks :
    Complex.I • (1 : Matrix (m ⊕ p) (m ⊕ p) ℂ) =
      fromBlocks (Complex.I • (1 : Matrix m m ℂ)) 0 0 (Complex.I • (1 : Matrix p p ℂ)) := by
  rw [← fromBlocks_one, fromBlocks_smul]
  simp only [smul_zero]

omit [Fintype m] [Fintype p] in
theorem cpl_ray_fromBlocks (A : Matrix m m ℂ) (C : Matrix p p ℂ) (t : ℝ) :
    cplRay (fromBlocks A 0 0 C) t = fromBlocks (cplRay A t) 0 0 (cplRay C t) := by
  unfold cplRay
  rw [cpl_I_one_fromBlocks, fromBlocks_smul, fromBlocks_smul, fromBlocks_add]
  simp only [smul_zero, add_zero]

/-- **Block-diagonal additivity** `L(diag(A, C)) = L(A) + L(C)` on `cplDom`. -/
theorem cpl_logDet_fromBlocks_zero {A : Matrix m m ℂ} {C : Matrix p p ℂ} (hA : A ∈ cplDom m)
    (hC : C ∈ cplDom p) :
    cplLogDet (fromBlocks A 0 0 C) = cplLogDet A + cplLogDet C := by
  obtain ⟨a, ha, hA'⟩ := hA
  obtain ⟨c, hc, hC'⟩ := hC
  unfold cplLogDet
  have heq : Set.EqOn (cplInteg (fromBlocks A 0 0 C)) (fun t => cplInteg A t + cplInteg C t)
      (Set.uIcc 0 1) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hua := cpl_ray_isUnit ha hA' ht.1 ht.2
    have huc := cpl_ray_isUnit hc hC' ht.1 ht.2
    simp only [cplInteg]
    rw [cpl_ray_fromBlocks]
    simp only [← Matrix.nonsing_inv_eq_ringInverse]
    rw [inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ (iff_of_true hua huc), cpl_I_one_fromBlocks,
      sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
    simp [fromBlocks_multiply, cpl_trace_fromBlocks, sub_eq_add_neg]
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_add]
  · simp only [Fintype.card_sum, Nat.cast_add]
    ring
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    exact cpl_continuousOn_integ ha hA'
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    exact cpl_continuousOn_integ hc hC'

omit [DecidableEq m] [DecidableEq p] in
theorem cpl_dot_sum (w y : m ⊕ p → ℂ) :
    star w ⬝ᵥ y = star (w ∘ Sum.inl) ⬝ᵥ (y ∘ Sum.inl) + star (w ∘ Sum.inr) ⬝ᵥ (y ∘ Sum.inr) := by
  simp [dotProduct, Fintype.sum_sum_type]

omit [DecidableEq m] [DecidableEq p] in
theorem cpl_sq_sum (w : m ⊕ p → ℂ) : cplSq w = cplSq (w ∘ Sum.inl) + cplSq (w ∘ Sum.inr) := by
  simp [cplSq, Fintype.sum_sum_type]

/-- `Im ⟪y, A⁻¹ y⟫ ≤ 0` when `Im ⟪x, A x⟫ ≥ 0` (here: `A` coercive). -/
theorem cpl_form_inv_nonpos {c : ℝ} (hc : 0 < c) {A : Matrix m m ℂ} (hA : cplCoercive c A)
    (y : m → ℂ) : cplForm (Ring.inverse A) y ≤ 0 := by
  have hu := cpl_coercive_isUnit hc hA
  set x := Ring.inverse A *ᵥ y with hx
  have hy : y = A *ᵥ x := by
    rw [hx, mulVec_mulVec, Ring.mul_inverse_cancel _ hu, one_mulVec]
  have h1 : star y ⬝ᵥ (Ring.inverse A *ᵥ y) = star (star x ⬝ᵥ (A *ᵥ x)) := by
    rw [← hx, cpl_star_dot_mulVec_star, hy, star_mulVec, ← dotProduct_mulVec]
  unfold cplForm
  rw [h1, Complex.star_def, Complex.conj_im]
  have := hA x
  have h0 := cpl_sq_nonneg x
  unfold cplForm at this
  nlinarith

omit [DecidableEq m] [DecidableEq p] in
/-- The real part identity `Im(⟪u, B v⟫ + ⟪v, Bᴴ u⟫) = 0`. -/
theorem cpl_cross_im (B : Matrix m p ℂ) (u : m → ℂ) (v : p → ℂ) :
    (star u ⬝ᵥ (B *ᵥ v) + star v ⬝ᵥ (Bᴴ *ᵥ u)).im = 0 := by
  have h : star v ⬝ᵥ (Bᴴ *ᵥ u) = star (star u ⬝ᵥ (B *ᵥ v)) := by
    rw [star_dotProduct, star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]
  rw [h, Complex.add_im, Complex.star_def, Complex.conj_im, add_neg_cancel]

omit [DecidableEq p] in
/-- Coercivity along the Schur path `[[A, sB], [sBᴴ, Z - (1-s²) Bᴴ A⁻¹ B]]`, `0 ≤ s ≤ 1`. -/
theorem cpl_coercive_schurPath {c : ℝ} (hc : 0 < c) {A : Matrix m m ℂ} {Z : Matrix p p ℂ}
    (hA : cplCoercive c A) (hZ : cplCoercive c Z) (B : Matrix m p ℂ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    cplCoercive c (fromBlocks A (s • B) (s • Bᴴ) (Z - (1 - s ^ 2) • (Bᴴ * Ring.inverse A * B))) := by
  intro w
  set u := w ∘ Sum.inl
  set v := w ∘ Sum.inr
  have hX : cplForm (Bᴴ * Ring.inverse A * B) v = cplForm (Ring.inverse A) (B *ᵥ v) := by
    unfold cplForm
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  have hXn := cpl_form_inv_nonpos hc hA (B *ᵥ v)
  have h1 : cplForm (fromBlocks A (s • B) (s • Bᴴ) (Z - (1 - s ^ 2) • (Bᴴ * Ring.inverse A * B))) w =
      cplForm A u + s * (star u ⬝ᵥ (B *ᵥ v) + star v ⬝ᵥ (Bᴴ *ᵥ u)).im + cplForm Z v -
        (1 - s ^ 2) * cplForm (Bᴴ * Ring.inverse A * B) v := by
    unfold cplForm
    rw [fromBlocks_mulVec, cpl_dot_sum]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, smul_mulVec, sub_mulVec, dotProduct_add,
      dotProduct_sub, dotProduct_smul, Complex.add_im, Complex.sub_im, Complex.smul_im, smul_eq_mul]
    ring
  rw [h1, cpl_cross_im, cpl_sq_sum]
  have hu := hA u
  have hv := hZ v
  have hr : 0 ≤ 1 - s ^ 2 := by nlinarith
  have : (1 - s ^ 2) * cplForm (Bᴴ * Ring.inverse A * B) v ≤ 0 := by
    rw [hX]; exact mul_nonpos_of_nonneg_of_nonpos hr hXn
  nlinarith

omit [DecidableEq p] in
/-- The Schur complement `Z - Bᴴ A⁻¹ B` is coercive. -/
theorem cpl_coercive_schur {c : ℝ} (hc : 0 < c) {A : Matrix m m ℂ} {Z : Matrix p p ℂ}
    (hA : cplCoercive c A) (hZ : cplCoercive c Z) (B : Matrix m p ℂ) :
    cplCoercive c (Z - Bᴴ * Ring.inverse A * B) := by
  intro v
  have hX : cplForm (Bᴴ * Ring.inverse A * B) v = cplForm (Ring.inverse A) (B *ᵥ v) := by
    unfold cplForm
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  have hXn := cpl_form_inv_nonpos hc hA (B *ᵥ v)
  rw [cpl_form_sub, hX]
  linarith [hZ v]

/-- **The Schur path.** For coercive `A`, `Z` (same constant) and any `B`:
`Im L([[A, B], [Bᴴ, Z]]) = Im L(A) + Im L(Z - Bᴴ A⁻¹ B)`. The path
`s ↦ P_s diag(A, S) Q_s` (unipotent `P_s, Q_s`) stays in `cplDom` and has
`Tr(M_s⁻¹ M_s') = Tr(P_s⁻¹ P_s') + Tr(Q_s' Q_s⁻¹) = 0`. -/
theorem cpl_im_logDet_schur {c : ℝ} (hc : 0 < c) {A : Matrix m m ℂ} {Z : Matrix p p ℂ}
    (hA : cplCoercive c A) (hZ : cplCoercive c Z) (B : Matrix m p ℂ) :
    (cplLogDet (fromBlocks A B Bᴴ Z)).im =
      (cplLogDet A).im + (cplLogDet (Z - Bᴴ * Ring.inverse A * B)).im := by
  set Ai := Ring.inverse A with hAi
  have huA := cpl_coercive_isUnit hc hA
  have hAi1 : A * Ai = 1 := Ring.mul_inverse_cancel _ huA
  have hAi2 : Ai * A = 1 := Ring.inverse_mul_cancel _ huA
  set X := Bᴴ * Ai * B with hX
  set S := Z - X with hS
  set NP : Matrix (m ⊕ p) (m ⊕ p) ℂ := fromBlocks 0 0 (Bᴴ * Ai) 0 with hNP
  set NQ : Matrix (m ⊕ p) (m ⊕ p) ℂ := fromBlocks 0 (Ai * B) 0 0 with hNQ
  set Δ : Matrix (m ⊕ p) (m ⊕ p) ℂ := fromBlocks A 0 0 S with hΔ
  set Mp : ℝ → Matrix (m ⊕ p) (m ⊕ p) ℂ := fun s => (1 + s • NP) * Δ * (1 + s • NQ) with hMpdef
  have hMp : ∀ s : ℝ, Mp s = fromBlocks A (s • B) (s • Bᴴ) (Z - (1 - s ^ 2) • X) := by
    intro s
    simp only [hMpdef, hNP, hNQ, hΔ, ← fromBlocks_one, fromBlocks_smul, fromBlocks_add,
      fromBlocks_multiply]
    simp only [smul_zero, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, Matrix.smul_mul, Matrix.mul_smul]
    rw [fromBlocks_inj]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · rw [← Matrix.mul_assoc, hAi1, Matrix.one_mul]
    · rw [Matrix.mul_assoc, hAi2, Matrix.mul_one]
    · rw [hS, hX, Matrix.mul_assoc, ← Matrix.mul_assoc A, hAi1, Matrix.one_mul, smul_smul]
      rw [show Bᴴ * Ai * B = Bᴴ * (Ai * B) from Matrix.mul_assoc _ _ _]
      module
  have hcoer : ∀ s ∈ Set.Icc (0 : ℝ) 1, cplCoercive c (Mp s) := fun s hs => by
    rw [hMp]; exact cpl_coercive_schurPath hc hA hZ B hs.1 hs.2
  have hdom : ∀ s ∈ Set.Icc (0 : ℝ) 1, Mp s ∈ cplDom (m ⊕ p) := fun s hs => ⟨c, hc, hcoer s hs⟩
  have hNP2 : NP * NP = 0 := by simp [hNP, fromBlocks_multiply]
  have hNQ2 : NQ * NQ = 0 := by simp [hNQ, fromBlocks_multiply]
  have htrNP : NP.trace = 0 := by simp [hNP, cpl_trace_fromBlocks]
  have htrNQ : NQ.trace = 0 := by simp [hNQ, cpl_trace_fromBlocks]
  have hinvN : ∀ (N : Matrix (m ⊕ p) (m ⊕ p) ℂ), N * N = 0 → ∀ s : ℝ,
      (1 + s • N)⁻¹ = 1 - s • N := by
    intro N hN s
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hN, smul_zero, add_zero, add_sub_cancel_right]
  have hΔu : IsUnit Δ := by
    have h0 := hcoer 0 (Set.left_mem_Icc.mpr zero_le_one)
    have : Mp 0 = Δ := by simp [hMpdef]
    rw [← this]; exact cpl_coercive_isUnit hc h0
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt Mp (NP * Δ * (1 + s • NQ) + (1 + s • NP) * Δ * NQ) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => 1 + s • NP) NP s := by
      have := ((hasDerivAt_id s).smul_const NP).const_add 1
      simpa using this
    have h2 : HasDerivAt (fun s : ℝ => 1 + s • NQ) NQ s := by
      have := ((hasDerivAt_id s).smul_const NQ).const_add 1
      simpa using this
    exact (h1.mul_const Δ).fun_mul h2
  have htr : ∀ s ∈ Set.Icc (0 : ℝ) 1, ((Ring.inverse (Mp s) *
      (NP * Δ * (1 + s • NQ) + (1 + s • NP) * Δ * NQ)).trace).im = 0 := by
    intro s _
    have hDi1 : Δ * Ring.inverse Δ = 1 := Ring.mul_inverse_cancel _ hΔu
    have hDi2 : Ring.inverse Δ * Δ = 1 := Ring.inverse_mul_cancel _ hΔu
    have hinv : Ring.inverse (Mp s) = (1 - s • NQ) * Ring.inverse Δ * (1 - s • NP) := by
      simp only [hMpdef]
      rw [← Matrix.nonsing_inv_eq_ringInverse, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        hinvN NP hNP2, hinvN NQ hNQ2, Matrix.nonsing_inv_eq_ringInverse, Matrix.mul_assoc]
    have hP : (1 - s • NP) * (1 + s • NP) = 1 := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul, hNP2, smul_zero, add_zero, add_sub_cancel_right]
    have hQ : (1 + s • NQ) * (1 - s • NQ) = 1 := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul, hNQ2, smul_zero, sub_zero, sub_add_cancel]
    have hPN : (1 - s • NP) * NP = NP := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, hNP2, smul_zero, sub_zero]
    have hNQQ : NQ * (1 - s • NQ) = NQ := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hNQ2, smul_zero, sub_zero]
    rw [hinv, Matrix.mul_add, Matrix.trace_add]
    have t1 : ((1 - s • NQ) * Ring.inverse Δ * (1 - s • NP) * (NP * Δ * (1 + s • NQ))).trace =
        NP.trace := by
      calc ((1 - s • NQ) * Ring.inverse Δ * (1 - s • NP) * (NP * Δ * (1 + s • NQ))).trace
          = ((1 + s • NQ) * (1 - s • NQ) * (Ring.inverse Δ * ((1 - s • NP) * NP) * Δ)).trace := by
            have := Matrix.trace_mul_comm ((1 - s • NQ) * Ring.inverse Δ * (1 - s • NP) * NP * Δ)
              (1 + s • NQ)
            simp only [Matrix.mul_assoc] at this ⊢
            exact this
        _ = ((Δ * Ring.inverse Δ) * NP).trace := by
            rw [hQ, Matrix.one_mul, hPN, Matrix.trace_mul_comm, Matrix.mul_assoc]
        _ = NP.trace := by rw [hDi1, Matrix.one_mul]
    have t2 : ((1 - s • NQ) * Ring.inverse Δ * (1 - s • NP) * ((1 + s • NP) * Δ * NQ)).trace =
        NQ.trace := by
      calc ((1 - s • NQ) * Ring.inverse Δ * (1 - s • NP) * ((1 + s • NP) * Δ * NQ)).trace
          = ((1 - s • NQ) * (Ring.inverse Δ * ((1 - s • NP) * (1 + s • NP)) * Δ) * NQ).trace := by
            simp only [Matrix.mul_assoc]
        _ = (NQ * (1 - s • NQ)).trace := by
            rw [hP, Matrix.mul_one, hDi2, Matrix.mul_one, Matrix.trace_mul_comm]
        _ = NQ.trace := by rw [hNQQ]
    rw [t1, t2, htrNP, htrNQ, add_zero, Complex.zero_im]
  have hpath := cpl_im_logDet_path hderiv hdom htr
  have e1 : Mp 1 = fromBlocks A B Bᴴ Z := by
    rw [hMp]; simp
  have e0 : Mp 0 = fromBlocks A 0 0 S := by
    rw [hMp]; simp [hS]
  rw [e1] at hpath
  rw [hpath, e0, cpl_logDet_fromBlocks_zero ⟨c, hc, hA⟩, Complex.add_im]
  exact ⟨c, hc, cpl_coercive_schur hc hA hZ B⟩

end Blocks

/-!
## 5. The phase bound `0 ≤ Im L(M) ≤ dim · π` on `cplDom`
-/

section Bound

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cpl_sq_mulVec_unitary {U : Matrix n n ℂ} (hU1 : star U * U = 1) (v : n → ℂ) :
    cplSq (U *ᵥ v) = cplSq v := by
  have h : ((cplSq (U *ᵥ v) : ℝ) : ℂ) = ((cplSq v : ℝ) : ℂ) := by
    rw [← cpl_star_dot_self, ← cpl_star_dot_self, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
      ← Matrix.star_eq_conjTranspose, hU1, one_mulVec]
  exact_mod_cast h

omit [DecidableEq n] in
theorem cpl_form_conj (U M : Matrix n n ℂ) (v : n → ℂ) :
    cplForm (star U * M * U) v = cplForm M (U *ᵥ v) := by
  unfold cplForm
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec,
    Matrix.star_eq_conjTranspose]

theorem cpl_coercive_conj {c : ℝ} {M U : Matrix n n ℂ} (hU1 : star U * U = 1)
    (h : cplCoercive c M) : cplCoercive c (star U * M * U) := fun v => by
  rw [cpl_form_conj, ← cpl_sq_mulVec_unitary hU1 v]; exact h _

/-- The complex diagonal matrix of a real vector. -/
def cplRDiag (d : n → ℝ) : Matrix n n ℂ := diagonal (fun x => (d x : ℂ))

omit [Fintype n] in
theorem cpl_rDiag_conjTranspose (d : n → ℝ) : (cplRDiag d)ᴴ = cplRDiag d := by
  unfold cplRDiag
  rw [diagonal_conjTranspose]
  congr 1
  funext x
  simp [Complex.conj_ofReal]

theorem cpl_coercive_rDiag_conj {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) {d : n → ℝ}
    (hd : ∀ x, δ ≤ d x) {M : Matrix n n ℂ} (h : cplCoercive c M) :
    cplCoercive (c * δ ^ 2) (cplRDiag d * M * cplRDiag d) := fun v => by
  have h1 := cpl_form_conj (cplRDiag d) M v
  rw [Matrix.star_eq_conjTranspose, cpl_rDiag_conjTranspose] at h1
  rw [h1]
  refine le_trans ?_ (h _)
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  unfold cplSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  simp only [cplRDiag, mulVec_diagonal, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs]
  have : δ ^ 2 ≤ d x ^ 2 := pow_le_pow_left₀ hδ.le (hd x) 2
  exact mul_le_mul_of_nonneg_right this (by positivity)

omit [DecidableEq n] in
theorem cpl_exists_lower (d : n → ℝ) (hd : ∀ x, 0 < d x) : ∃ δ : ℝ, 0 < δ ∧ ∀ x, δ ≤ d x := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, one_pos, fun x => (IsEmpty.false x).elim⟩
  · obtain ⟨x₀, hx₀⟩ := Finite.exists_min d
    exact ⟨d x₀, hd x₀, hx₀⟩

theorem cpl_ringInverse_rDiag {d : n → ℝ} (hd : ∀ x, d x ≠ 0) :
    Ring.inverse (cplRDiag d) = cplRDiag (fun x => (d x)⁻¹) := by
  unfold cplRDiag
  rw [cpl_ringInverse_diagonal fun x => Complex.ofReal_ne_zero.mpr (hd x)]
  congr 1
  funext x
  push_cast; rfl

theorem cpl_rDiag_mul (d e : n → ℝ) : cplRDiag d * cplRDiag e = cplRDiag (fun x => d x * e x) := by
  unfold cplRDiag
  rw [diagonal_mul_diagonal]
  congr 1; funext x; push_cast; rfl

theorem cpl_trace_rDiag_im (d : n → ℝ) : (cplRDiag d).trace.im = 0 := by
  unfold cplRDiag
  rw [trace_diagonal, Complex.im_sum]
  simp

theorem cpl_trace_congr_path {Di Mi D Mt Q : Matrix n n ℂ} (hD1 : D * Di = 1) (hD2 : Di * D = 1)
    (hM1 : Mt * Mi = 1) (hM2 : Mi * Mt = 1) :
    (Di * Mi * Di * (Q * Mt * D + D * Mt * Q)).trace = 2 * (Di * Q).trace := by
  rw [Matrix.mul_add, Matrix.trace_add]
  have t1 : (Di * Mi * Di * (Q * Mt * D)).trace = (Di * Q).trace := by
    have h := Matrix.trace_mul_comm (Di * Mi * Di * Q * Mt) D
    have h' := Matrix.trace_mul_comm (Mi * (Di * Q)) Mt
    calc (Di * Mi * Di * (Q * Mt * D)).trace = (Di * Mi * Di * Q * Mt * D).trace := by
          simp only [Matrix.mul_assoc]
      _ = (D * (Di * Mi * Di * Q * Mt)).trace := h
      _ = (Mi * (Di * Q) * Mt).trace := by
          simp only [← Matrix.mul_assoc]; rw [hD1, Matrix.one_mul]
      _ = (Mt * (Mi * (Di * Q))).trace := h'
      _ = (Di * Q).trace := by rw [← Matrix.mul_assoc, hM1, Matrix.one_mul]
  have t2 : (Di * Mi * Di * (D * Mt * Q)).trace = (Di * Q).trace := by
    congr 1
    calc Di * Mi * Di * (D * Mt * Q) = Di * (Mi * (Di * D) * Mt) * Q := by
          simp only [Matrix.mul_assoc]
      _ = Di * Q := by rw [hD2, Matrix.mul_one, hM2, Matrix.mul_one]
  rw [t1, t2]; ring

/-- **Phase bound.** On `cplDom`, `0 ≤ Im L(M) ≤ dim · π`: congruence by the unitary diagonalizing
`Im M` and the path `D_s M̃ D_s`, `D_s = (1-s) + s (Im M̃)^{-1/2}` (along which
`Tr(M_s⁻¹ M_s') = 2 Tr(D_s⁻¹ D_s')` is real), end at `K + i` with `K` Hermitian, where
`Im L = Σ arg(λ_k + i)`. -/
theorem cpl_im_logDet_bounds {M : Matrix n n ℂ} (hM : M ∈ cplDom n) :
    0 ≤ (cplLogDet M).im ∧ (cplLogDet M).im ≤ Fintype.card n * Real.pi := by
  obtain ⟨c, hc, hcM⟩ := hM
  set S : Matrix n n ℂ := (2 * Complex.I)⁻¹ • (M - Mᴴ) with hSdef
  have h2I : (2 * Complex.I) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  have hMS : M - Mᴴ = (2 * Complex.I) • S := by
    rw [hSdef, smul_smul, mul_inv_cancel₀ h2I, one_smul]
  have hS : S.IsHermitian := by
    unfold IsHermitian
    rw [hSdef, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
    have : star (2 * Complex.I)⁻¹ = -(2 * Complex.I)⁻¹ := by
      rw [star_inv₀, star_mul', Complex.star_def, Complex.conj_I, map_ofNat, mul_neg, inv_neg]
    rw [this, neg_smul, ← smul_neg, neg_sub]
  set U : Matrix n n ℂ := (hS.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hU1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hS.eigenvectorUnitary.2
  have hU2 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hS.eigenvectorUnitary.2
  set σ := hS.eigenvalues with hσdef
  have hspec : S = U * cplRDiag σ * star U := by
    have := hS.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  set Mt := star U * M * U with hMt
  have hMtc : cplCoercive c Mt := cpl_coercive_conj hU1 hcM
  have hLM : cplLogDet M = cplLogDet Mt := by
    have : M = U * Mt * star U := by
      rw [hMt, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU2, Matrix.one_mul, Matrix.mul_assoc,
        hU2, Matrix.mul_one]
    conv_lhs => rw [this]
    exact cpl_logDet_conj hU1 hU2 Mt
  have hdiff : Mt - Mtᴴ = (2 * Complex.I) • cplRDiag σ := by
    have h1 : Mtᴴ = star U * Mᴴ * U := by
      simp only [hMt, conjTranspose_mul, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    have h3 : star U * (U * cplRDiag σ * star U) * U = cplRDiag σ := by
      simp only [← Matrix.mul_assoc, hU1, Matrix.one_mul]
      rw [Matrix.mul_assoc, hU1, Matrix.mul_one]
    rw [h1, hMt, ← Matrix.sub_mul, ← Matrix.mul_sub, hMS, hspec, Matrix.mul_smul, Matrix.smul_mul,
      h3]
  have hσ : ∀ x, σ x = (Mt x x).im := by
    intro x
    have h := congrFun (congrFun hdiff x) x
    simp only [Matrix.sub_apply, conjTranspose_apply, Matrix.smul_apply, cplRDiag,
      diagonal_apply_eq, smul_eq_mul] at h
    have h2 := congrArg Complex.im h
    simp [Complex.mul_im] at h2
    linarith
  have hσc : ∀ x, c ≤ σ x := by
    intro x
    have h := hMtc (Pi.single x 1)
    have hsq : cplSq (Pi.single x (1 : ℂ) : n → ℂ) = 1 := by
      unfold cplSq
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _ hy; simp [hy]
      · simp
    have hf : cplForm Mt (Pi.single x 1) = (Mt x x).im := by
      unfold cplForm
      rw [mulVec_single_one]
      simp [dotProduct, Pi.single_apply]
    rw [hsq, hf, mul_one] at h
    rw [hσ]; exact h
  have hσpos : ∀ x, 0 < σ x := fun x => lt_of_lt_of_le hc (hσc x)
  set r : n → ℝ := fun x => (Real.sqrt (σ x))⁻¹ with hrdef
  have hrpos : ∀ x, 0 < r x := fun x => inv_pos.mpr (Real.sqrt_pos.mpr (hσpos x))
  set P := cplRDiag r with hPdef
  set D : ℝ → Matrix n n ℂ := fun s => (1 - s) • (1 : Matrix n n ℂ) + s • P with hDdef
  have hDdiag : ∀ s, D s = cplRDiag (fun x => 1 - s + s * r x) := by
    intro s
    ext i j
    by_cases h : i = j
    · subst h; simp [hDdef, hPdef, cplRDiag, Complex.real_smul]
    · simp [hDdef, hPdef, cplRDiag, diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hdpos : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x, 0 < 1 - s + s * r x := by
    intro s hs x
    rcases hs.2.lt_or_eq with h | h
    · have := mul_nonneg hs.1 (hrpos x).le; linarith
    · rw [h]; have := hrpos x; linarith
  set Mp : ℝ → Matrix n n ℂ := fun s => D s * Mt * D s with hMpdef
  have hdom : ∀ s ∈ Set.Icc (0 : ℝ) 1, Mp s ∈ cplDom n := by
    intro s hs
    obtain ⟨δ, hδ, hδd⟩ := cpl_exists_lower _ (hdpos s hs)
    refine ⟨c * δ ^ 2, by positivity, ?_⟩
    simp only [hMpdef]
    rw [hDdiag]
    exact cpl_coercive_rDiag_conj hc.le hδ hδd hMtc
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt Mp ((P - 1) * Mt * D s + D s * Mt * (P - 1)) s := by
    intro s _
    have h1 : HasDerivAt D (P - 1) s := by
      have ha := ((hasDerivAt_id s).const_sub 1).smul_const (1 : Matrix n n ℂ)
      have hb := (hasDerivAt_id s).smul_const P
      have := ha.add hb
      refine (show HasDerivAt (fun s : ℝ => (1 - s) • (1 : Matrix n n ℂ) + s • P) _ s
        from this).congr_deriv ?_
      simp only [neg_smul, one_smul]
      abel
    exact (h1.mul_const Mt).fun_mul h1
  have htr : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((Ring.inverse (Mp s) * ((P - 1) * Mt * D s + D s * Mt * (P - 1))).trace).im = 0 := by
    intro s hs
    have hdne : ∀ x, 1 - s + s * r x ≠ 0 := fun x => (hdpos s hs x).ne'
    have huD : IsUnit (D s) := by
      rw [hDdiag]
      refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
      unfold cplRDiag
      rw [det_diagonal]
      exact (Finset.prod_ne_zero_iff.mpr fun x _ => Complex.ofReal_ne_zero.mpr (hdne x)).isUnit
    have huM := cpl_coercive_isUnit hc hMtc
    set Di := Ring.inverse (D s)
    set Mi := Ring.inverse Mt
    have hD1 : D s * Di = 1 := Ring.mul_inverse_cancel _ huD
    have hD2 : Di * D s = 1 := Ring.inverse_mul_cancel _ huD
    have hM1 : Mt * Mi = 1 := Ring.mul_inverse_cancel _ huM
    have hM2 : Mi * Mt = 1 := Ring.inverse_mul_cancel _ huM
    have hinv : Ring.inverse (Mp s) = Di * Mi * Di := by
      simp only [hMpdef]
      rw [← Matrix.nonsing_inv_eq_ringInverse, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_eq_ringInverse, Matrix.nonsing_inv_eq_ringInverse, Matrix.mul_assoc]
    have hreal : (Di * (P - 1)).trace.im = 0 := by
      have e : Di * (P - 1) = cplRDiag (fun x => (1 - s + s * r x)⁻¹ * (r x - 1)) := by
        have hP1 : P - 1 = cplRDiag (fun x => r x - 1) := by
          ext i j
          by_cases h : i = j
          · subst h; simp [hPdef, cplRDiag]
          · simp [hPdef, cplRDiag, diagonal_apply_ne _ h, Matrix.one_apply_ne h]
        simp only [Di]
        rw [hDdiag, cpl_ringInverse_rDiag hdne, hP1, cpl_rDiag_mul]
      rw [e]; exact cpl_trace_rDiag_im _
    rw [hinv, cpl_trace_congr_path hD1 hD2 hM1 hM2, Complex.mul_im, hreal]
    simp
  have hpath := cpl_im_logDet_path hderiv hdom htr
  have e0 : Mp 0 = Mt := by simp [hMpdef, hDdef]
  have e1 : Mp 1 = P * Mt * P := by simp [hMpdef, hDdef]
  set K := P * Mt * P - Complex.I • (1 : Matrix n n ℂ) with hKdef
  have hPh : Pᴴ = P := cpl_rDiag_conjTranspose r
  have hPσP : P * cplRDiag σ * P = 1 := by
    rw [hPdef, cpl_rDiag_mul, cpl_rDiag_mul]
    unfold cplRDiag
    rw [← diagonal_one]
    congr 1
    funext x
    show ((r x * σ x * r x : ℝ) : ℂ) = 1
    have h1 : r x * σ x * r x = 1 := by
      simp only [hrdef]
      have hs := Real.sq_sqrt (hσpos x).le
      have hs0 : Real.sqrt (σ x) ≠ 0 := (Real.sqrt_pos.mpr (hσpos x)).ne'
      field_simp
      linarith
    rw [h1]; simp
  have hK : K.IsHermitian := by
    unfold IsHermitian
    have hIh : (Complex.I • (1 : Matrix n n ℂ))ᴴ = -(Complex.I • (1 : Matrix n n ℂ)) := by
      rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_I, neg_smul]
    rw [hKdef, conjTranspose_sub, hIh, conjTranspose_mul, conjTranspose_mul, hPh,
      ← Matrix.mul_assoc]
    have : P * Mt * P - P * Mtᴴ * P = (2 * Complex.I) • (1 : Matrix n n ℂ) := by
      rw [← Matrix.sub_mul, ← Matrix.mul_sub, hdiff, Matrix.mul_smul, Matrix.smul_mul, hPσP]
    have e2 : (2 * Complex.I) • (1 : Matrix n n ℂ) =
        Complex.I • (1 : Matrix n n ℂ) + Complex.I • (1 : Matrix n n ℂ) := by
      rw [← add_smul]; ring_nf
    rw [e2, sub_eq_iff_eq_add] at this
    rw [sub_neg_eq_add, eq_sub_iff_add_eq, this]
    abel
  have hKI : P * Mt * P = (1 : ℝ) • K + Complex.I • (1 : Matrix n n ℂ) := by
    rw [one_smul, hKdef, sub_add_cancel]
  have hval : (cplLogDet (Mp 1)).im = ∑ k, Complex.arg ((1 * hK.eigenvalues k : ℝ) + Complex.I) := by
    rw [e1, hKI, cpl_logDet_herm hK 1 (by simp), Complex.im_sum]
    simp only [Complex.log_im]
  rw [hpath, e0] at hval
  rw [hLM, hval]
  constructor
  · refine Finset.sum_nonneg fun k _ => ?_
    rw [Complex.arg_nonneg_iff]; simp
  · calc ∑ k, Complex.arg ((1 * hK.eigenvalues k : ℝ) + Complex.I)
        ≤ ∑ _k : n, Real.pi := Finset.sum_le_sum fun k _ => Complex.arg_le_pi _
      _ = Fintype.card n * Real.pi := by simp

end Bound

/-!
## 6. The phase identity for the regularized layer matrix
-/

section PhaseIdentity

open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm (negativeCount)

variable {m p : Type} [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]

/-- The regularization sequence `κ_j = 1/(j+1) → 0`. -/
def cplKappa (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

theorem cpl_kappa_pos (j : ℕ) : 0 < cplKappa j := by unfold cplKappa; positivity

theorem cpl_tendsto_kappa : Tendsto cplKappa atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

theorem cpl_coercive_herm_add {D : Matrix m m ℂ} (hD : D.IsHermitian) {κ : ℝ} :
    cplCoercive κ (D + ((κ : ℂ) * Complex.I) • (1 : Matrix m m ℂ)) := fun v => by
  have e : ((κ : ℂ) * Complex.I) • (1 : Matrix m m ℂ) = κ • (Complex.I • (1 : Matrix m m ℂ)) := by
    rw [← Complex.coe_smul, smul_smul]
  rw [e, cpl_form_add, cpl_form_herm hD, cpl_form_smul, cpl_form_I_one, zero_add]

theorem cpl_coercive_scalar {w : ℂ} : cplCoercive w.im (w • (1 : Matrix p p ℂ)) := fun v => by
  have e : w • (1 : Matrix p p ℂ) = w.re • (1 : Matrix p p ℂ) + w.im • (Complex.I • 1) := by
    conv_lhs => rw [← Complex.re_add_im w]
    rw [add_smul, ← Complex.coe_smul, ← Complex.coe_smul, smul_smul]
  rw [e, cpl_form_add, cpl_form_smul, cpl_form_smul, cpl_form_I_one, cpl_form_herm isHermitian_one]
  ring_nf; rfl

omit [Fintype p] [DecidableEq p] in
theorem cpl_isHermitian_schur {D : Matrix m m ℂ} (hD : D.IsHermitian) (B : Matrix m p ℂ) :
    (Bᴴ * D⁻¹ * B).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv,
    hD.eq, Matrix.mul_assoc]

/-- `π⁻¹ Im L(D + iκ) → N_-(D)` for Hermitian invertible `D` as `κ = κ_j → 0`. -/
theorem cpl_tendsto_count {D : Matrix m m ℂ} (hD : D.IsHermitian) (hDu : IsUnit D.det) :
    Tendsto (fun j => (cplLogDet (D + ((cplKappa j : ℂ) * Complex.I) • (1 : Matrix m m ℂ))).im)
      atTop (𝓝 (Real.pi * negativeCount D)) := by
  have hval : ∀ j, (cplLogDet (D + ((cplKappa j : ℂ) * Complex.I) • (1 : Matrix m m ℂ))).im =
      ∑ k, Complex.arg ((hD.eigenvalues k : ℂ) + (cplKappa j : ℂ) * Complex.I) := by
    intro j
    have h := cpl_logDet_herm hD 1 (w := (cplKappa j : ℂ) * Complex.I) (by
      simp [cpl_kappa_pos j])
    rw [one_smul] at h
    rw [h, Complex.im_sum]
    simp [Complex.log_im]
  simp_rw [hval]
  have hne : ∀ k, hD.eigenvalues k ≠ 0 := by
    intro k hk
    have := hD.det_eq_prod_eigenvalues
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])] at this
    rw [this] at hDu
    exact not_isUnit_zero hDu
  have hlim : ∀ k, Tendsto (fun j => Complex.arg ((hD.eigenvalues k : ℂ) +
      (cplKappa j : ℂ) * Complex.I)) atTop
      (𝓝 (if hD.eigenvalues k < 0 then Real.pi else 0)) := by
    intro k
    have hc : Tendsto (fun j => (hD.eigenvalues k : ℂ) + (cplKappa j : ℂ) * Complex.I) atTop
        (𝓝 (hD.eigenvalues k : ℂ)) := by
      have hcc : Continuous (fun κ : ℝ => (hD.eigenvalues k : ℂ) + (κ : ℂ) * Complex.I) := by
        fun_prop
      have := (hcc.tendsto 0).comp cpl_tendsto_kappa
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
      exact this
    split_ifs with hneg
    · have h1 := Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
        (z := (hD.eigenvalues k : ℂ)) (by simpa using hneg) (by simp)
      refine h1.comp (tendsto_nhdsWithin_iff.mpr ⟨hc, Filter.Eventually.of_forall fun j => ?_⟩)
      simp [(cpl_kappa_pos j).le]
    · have hpos : 0 < hD.eigenvalues k := lt_of_le_of_ne (not_lt.mp hneg) (hne k).symm
      have h1 := Complex.continuousAt_arg (x := (hD.eigenvalues k : ℂ))
        (Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hpos)))
      have h2 := h1.tendsto.comp hc
      rwa [Complex.arg_ofReal_of_nonneg hpos.le] at h2
  have hsum := tendsto_finsetSum Finset.univ fun k _ => hlim k
  convert hsum using 2
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
    negativeCount_of_isHermitian hD, mul_comm]

/-- **The phase identity.** For Hermitian invertible `D`, any `B` and `Im z > 0`, along
`κ = κ_j → 0`: `π⁻¹ Im L([[D + iκ, B], [Bᴴ, z + iκ]]) → N_-(D) + Θ_z(Bᴴ D⁻¹ B)`. -/
theorem cpl_tendsto_phase {D : Matrix m m ℂ} (hD : D.IsHermitian) (hDu : IsUnit D.det)
    (B : Matrix m p ℂ) {z : ℂ} (hz : 0 < z.im) :
    Tendsto (fun j => (cplLogDet (fromBlocks (D + ((cplKappa j : ℂ) * Complex.I) • 1) B Bᴴ
        ((z + (cplKappa j : ℂ) * Complex.I) • 1))).im / Real.pi) atTop
      (𝓝 ((negativeCount D : ℝ) + phaseCount z (Bᴴ * D⁻¹ * B))) := by
  set Dj : ℕ → Matrix m m ℂ := fun j => D + ((cplKappa j : ℂ) * Complex.I) • 1 with hDj
  set Zj : ℕ → Matrix p p ℂ := fun j => (z + (cplKappa j : ℂ) * Complex.I) • 1 with hZj
  have hsplit : ∀ j, (cplLogDet (fromBlocks (Dj j) B Bᴴ (Zj j))).im =
      (cplLogDet (Dj j)).im + (cplLogDet (Zj j - Bᴴ * Ring.inverse (Dj j) * B)).im := by
    intro j
    refine cpl_im_logDet_schur (cpl_kappa_pos j) (cpl_coercive_herm_add hD) ?_ B
    refine cpl_coercive_mono ?_ cpl_coercive_scalar
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one]
    linarith
  have h1 := cpl_tendsto_count hD hDu
  have hDlim : Tendsto Dj atTop (𝓝 D) := by
    have hc : Continuous (fun κ : ℝ => D + ((κ : ℂ) * Complex.I) • (1 : Matrix m m ℂ)) := by
      fun_prop
    have := (hc.tendsto 0).comp cpl_tendsto_kappa
    simp only [Complex.ofReal_zero, zero_mul, zero_smul, add_zero] at this
    exact this
  have hZlim : Tendsto Zj atTop (𝓝 (z • (1 : Matrix p p ℂ))) := by
    have hc : Continuous (fun κ : ℝ => (z + (κ : ℂ) * Complex.I) • (1 : Matrix p p ℂ)) := by
      fun_prop
    have := (hc.tendsto 0).comp cpl_tendsto_kappa
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
    exact this
  have hDunit : IsUnit D := (Matrix.isUnit_iff_isUnit_det D).mpr hDu
  have hinvlim : Tendsto (fun j => Ring.inverse (Dj j)) atTop (𝓝 (Ring.inverse D)) := by
    have hc := NormedRing.inverse_continuousAt hDunit.unit
    rw [IsUnit.unit_spec] at hc
    exact hc.tendsto.comp hDlim
  have hSlim : Tendsto (fun j => Zj j - Bᴴ * Ring.inverse (Dj j) * B) atTop
      (𝓝 (z • (1 : Matrix p p ℂ) - Bᴴ * Ring.inverse D * B)) :=
    hZlim.sub ((((continuous_const (y := Bᴴ)).matrix_mul continuous_id).matrix_mul
      (continuous_const (y := B))).tendsto _ |>.comp hinvlim)
  have hXh : (Bᴴ * Ring.inverse D * B).IsHermitian := by
    rw [← Matrix.nonsing_inv_eq_ringInverse]; exact cpl_isHermitian_schur hD B
  have hlimdom : z • (1 : Matrix p p ℂ) - Bᴴ * Ring.inverse D * B ∈ cplDom p := by
    refine ⟨z.im, hz, fun v => ?_⟩
    rw [cpl_form_sub, cpl_form_herm hXh, sub_zero]
    exact cpl_coercive_scalar v
  have h2 := (Complex.continuous_im.tendsto _).comp
    ((cpl_continuousAt_logDet hlimdom).tendsto.comp hSlim)
  have hval2 : (cplLogDet (z • (1 : Matrix p p ℂ) - Bᴴ * Ring.inverse D * B)).im =
      Real.pi * phaseCount z (Bᴴ * D⁻¹ * B) := by
    have e : z • (1 : Matrix p p ℂ) - Bᴴ * Ring.inverse D * B =
        (-1 : ℝ) • (Bᴴ * Ring.inverse D * B) + z • 1 := by
      rw [neg_one_smul, neg_add_eq_sub]
    rw [e, cpl_logDet_herm hXh (-1) hz, Complex.im_sum, Matrix.nonsing_inv_eq_ringInverse]
    unfold phaseCount
    rw [cph_spectralSum_eq_eigenvalues hXh, mul_div_cancel₀ _ Real.pi_ne_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.log_im]
    congr 1
    push_cast
    ring
  have hsum := (h1.add h2).div_const Real.pi
  rw [hval2] at hsum
  have hfin : (Real.pi * negativeCount D + Real.pi * phaseCount z (Bᴴ * D⁻¹ * B)) / Real.pi =
      (negativeCount D : ℝ) + phaseCount z (Bᴴ * D⁻¹ * B) := by
    field_simp
  rw [hfin] at hsum
  refine hsum.congr fun j => ?_
  simp only [Function.comp_apply]
  rw [← hsplit j]

end PhaseIdentity

end BlockBand.Layers
