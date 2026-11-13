module

public import BlockBand.Layers.FreshCount
public import BlockBand.Layers.CoreMeans
public import BlockBand.Layers.LayerResolventBound

/-!
# The fresh log-heat identity: the heat derivative of the fresh smoothed phase

The upper-half-plane logarithm has the exact heat derivative
`d/dt E Tr log H_t = cW E(a g_t - g_t²/2)`. This file proves `FcHeatDerivative`
(`fcHeatDerivative_holds`), with no hypothesis.

Law: `A = gueOfCoords W τ r`, `r` standard Gaussian (`= GUE_W(c/W)`, `fcd_integral_gue`),
`c = 1 - 2b`, `τ = c/W`. Norms: `ℓ²` operator norm on matrices.

* §1–3 (deterministic): for Hermitian `M` and `y > 0`,
  `Σ_j π⁻¹ arg(λ_j(M) + iy) = W/2 + π⁻¹ ∫_0^1 Im Tr(M(uM + iy)⁻¹) du` (`fcd_phase_eq`), hence
  along a `C¹` Hermitian path `d/ds Σ_j π⁻¹ arg(λ_j(M_s) + iy_s) =
  π⁻¹ Im Tr((M_s + iy_s)⁻¹(M_s' + iy_s'))` (`fcd_phase_hasDerivAt`; no eigenvalue regularity).
* §4: GUE coordinates are real-linear, `Σᵢ Λᵢ G Λᵢ = τ Tr(G)` (`fcd_gue_sandwich`) and Gaussian
  integration by parts `E Tr(GA) = -στ E(Tr G)²` for `G = (C₀ + σA + iκ)⁻¹` (`fcd_ibp`, from
  `core_ibp`).
* §6–8: in `σ = √t` the phase `Ψ(σ) = E π⁻¹ Σ_j arg(λ_j(M_σ) + iy_σ)` is differentiable on
  `[0,1]` (differentiation under the Gaussian integral, `fcd_Psi_hasDerivAt`),
  `Φ(t) = Ψ(√t)` (`fcd_heatPhase_eq_Psi`), and `Ψ'(σ)/(2σ) = (cW/2π) Im a² -
  (cW/2π) Im E(g_{σ²} - a)²` (`fcd_Psi'_eq`: the deterministic derivative gives `ca Tr H⁻¹`, the
  Gaussian one `-(c/2W)(Tr H⁻¹)²`). At `t = 0` the right derivative is the limit of the
  derivative (`hasDerivWithinAt_Ici_of_tendsto_deriv`, continuity of `E(g_t - a)²` by dominated
  convergence).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Complex Filter
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (spectralSum gaussianProduct)
open scoped NNReal ENNReal Topology Matrix.Norms.L2Operator

/-!
## 1. Deterministic resolvent facts
-/

section Det

variable {n : Type} [Fintype n]

/-- `H + iy` with `H` Hermitian and `y > 0` is invertible and `‖(H + iy)⁻¹‖ ≤ y⁻¹`. -/
theorem fcd_herm_inv [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) {y : ℝ} (hy : 0 < y) :
    IsUnit (H + ((y : ℂ) * I) • (1 : Matrix n n ℂ)).det ∧
      ‖(H + ((y : ℂ) * I) • (1 : Matrix n n ℂ))⁻¹‖ ≤ y⁻¹ := by
  have heq : H + ((y : ℂ) * I) • (1 : Matrix n n ℂ) = H + I • diagonal (fun _ : n => (y : ℂ)) := by
    rw [← smul_one_eq_diagonal, smul_smul, mul_comm]
  rw [heq]
  exact isUnit_det_and_norm_inv_le_of_lower hy
    (tfl_lower_of_herm_add_diag hH (fun _ => y) (fun _ => le_rfl))

omit [Fintype n] in
theorem fcd_isHermitian_real_smul {M : Matrix n n ℂ} (hM : M.IsHermitian) (u : ℝ) :
    ((u : ℂ) • M).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_smul, hM.eq, Complex.star_def, Complex.conj_ofReal]

/-- Derivative of the inverse along a path through invertible matrices. -/
theorem fcd_hasDerivAt_inv [DecidableEq n] {Z : ℝ → Matrix n n ℂ} {Z' : Matrix n n ℂ} {s : ℝ}
    (hZ : HasDerivAt Z Z' s) (hu : IsUnit (Z s).det) :
    HasDerivAt (fun s => (Z s)⁻¹) (-((Z s)⁻¹ * Z' * (Z s)⁻¹)) s := by
  have hu' : IsUnit (Z s) := (isUnit_iff_isUnit_det _).mpr hu
  have h := hasFDerivAt_ringInverse (𝕜 := ℝ) hu'.unit
  rw [IsUnit.unit_spec] at h
  have h2 := h.comp_hasDerivAt s hZ
  have hinv : ((hu'.unit⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = (Z s)⁻¹ := by
    rw [← Ring.inverse_unit, IsUnit.unit_spec, nonsing_inv_eq_ringInverse]
  simp only [nonsing_inv_eq_ringInverse] at hinv ⊢
  convert h2 using 1
  · rfl
  · rw [hinv]
    simp [ContinuousLinearMap.mulLeftRight_apply]

/-- The trace as a real continuous linear map. -/
def fcdTr : Matrix n n ℂ →L[ℝ] ℂ :=
  (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n ℂ ℂ)).restrictScalars ℝ

theorem fcdTr_apply (M : Matrix n n ℂ) : fcdTr M = M.trace := rfl

/-- `Im Tr` as a real continuous linear map. -/
def fcdImTr : Matrix n n ℂ →L[ℝ] ℝ := Complex.imCLM.comp fcdTr

theorem fcdImTr_apply (M : Matrix n n ℂ) : fcdImTr M = M.trace.im := rfl

theorem fcd_abs_imTr_le [DecidableEq n] (M : Matrix n n ℂ) : |M.trace.im| ≤ Fintype.card n * ‖M‖ :=
  (abs_im_le_norm _).trans (tfl_trace_le M)

end Det

/-!
## 2. The smoothed phase as a resolvent integral

For `M` Hermitian and `y > 0`: `π⁻¹ Σ_j arg(λ_j + iy) = W/2 + π⁻¹ ∫_0^1 Im Tr(M (uM + iy)⁻¹) du`
(`fcd_phase_eq`): along the ray `u ↦ uM` the phase has derivative `Im Tr(M (uM + iy)⁻¹)`, and it
equals `W/2` at `u = 0`.
-/

section Phase

variable {n : Type} [Fintype n] [DecidableEq n]

theorem fcd_eig_ne_zero (l u : ℝ) {y : ℝ} (hy : 0 < y) : (u : ℂ) * l + (y : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem fcd_continuous_eig (l : ℝ) {y : ℝ} (hy : 0 < y) :
    Continuous fun u : ℝ => ((l : ℂ) / ((u : ℂ) * l + (y : ℂ) * I)).im := by
  refine Complex.continuous_im.comp (continuous_const.div (by fun_prop) fun u => ?_)
  exact fcd_eig_ne_zero l u hy

omit [Fintype n] [DecidableEq n] in
/-- `arg(l + iy) = π/2 + ∫_0^1 Im(l / (ul + iy)) du` for `y > 0`. -/
theorem fcd_arg_eq_integral (l : ℝ) {y : ℝ} (hy : 0 < y) :
    arg ((l : ℂ) + (y : ℂ) * I) =
      Real.pi / 2 + ∫ u in (0 : ℝ)..1, ((l : ℂ) / ((u : ℂ) * l + (y : ℂ) * I)).im := by
  set z : ℝ → ℂ := fun u => (u : ℂ) * l + (y : ℂ) * I with hz
  have hzim : ∀ u, (z u).im = y := by intro u; simp [hz]
  have hslit : ∀ u, z u ∈ slitPlane := fun u =>
    mem_slitPlane_iff.mpr (Or.inr (by rw [hzim]; exact hy.ne'))
  have hzd : ∀ u, HasDerivAt z (l : ℂ) u := by
    intro u
    have := (((hasDerivAt_id u).ofReal_comp).mul_const (l : ℂ)).add_const ((y : ℂ) * I)
    simpa [hz] using this
  have hd : ∀ u, HasDerivAt (fun u => (log (z u)).im) ((l : ℂ) / z u).im u := by
    intro u
    have h1 := (hasDerivAt_log (hslit u)).comp u (hzd u)
    have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt u h1
    convert h2 using 1
    · rfl
    · rw [Complex.imCLM_apply, div_eq_inv_mul]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((fcd_continuous_eig l hy).intervalIntegrable 0 1)
  have e1 : (fun u : ℝ => ((l : ℂ) / ((u : ℂ) * l + (y : ℂ) * I)).im) =
      fun u => ((l : ℂ) / z u).im := rfl
  rw [e1, hftc]
  simp only [hz, log_im, Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, zero_add]
  rw [arg_real_mul I hy, arg_I]
  ring

/-- `Tr(M (uM + iy)⁻¹) = Σ_j λ_j / (uλ_j + iy)` for Hermitian `M`, `y > 0`. -/
theorem fcd_trace_mul_inv {M : Matrix n n ℂ} (hM : M.IsHermitian) (u : ℝ) {y : ℝ} (hy : 0 < y) :
    (M * ((u : ℂ) • M + ((y : ℂ) * I) • (1 : Matrix n n ℂ))⁻¹).trace =
      ∑ k, (hM.eigenvalues k : ℂ) / ((u : ℂ) * hM.eigenvalues k + (y : ℂ) * I) := by
  set U : Matrix n n ℂ := (hM.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hUU' : star U * U = 1 := Unitary.coe_star_mul_self _
  set D : Matrix n n ℂ := diagonal (fun k => (hM.eigenvalues k : ℂ)) with hD
  have hFe : M = U * D * star U := by
    conv_lhs => rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  set w : n → ℂ := fun k => (u : ℂ) * hM.eigenvalues k + (y : ℂ) * I with hw
  have hw0 : ∀ k, w k ≠ 0 := fun k => fcd_eig_ne_zero _ u hy
  have hdw : diagonal w = (u : ℂ) • D + ((y : ℂ) * I) • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [hw, hD]
    · simp [hw, hD, h]
  have hZ : (u : ℂ) • M + ((y : ℂ) * I) • (1 : Matrix n n ℂ) = U * diagonal w * star U := by
    rw [hdw, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hUU, ← hFe]
  have hinv : ((u : ℂ) • M + ((y : ℂ) * I) • (1 : Matrix n n ℂ))⁻¹ =
      U * diagonal (fun k => (w k)⁻¹) * star U := by
    apply inv_eq_right_inv
    rw [hZ]
    calc U * diagonal w * star U * (U * diagonal (fun k => (w k)⁻¹) * star U)
        = U * (diagonal w * (star U * U) * diagonal (fun k => (w k)⁻¹)) * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * star U := by
          rw [hUU', Matrix.mul_one, diagonal_mul_diagonal]
          have : (fun k => w k * (w k)⁻¹) = fun _ => (1 : ℂ) := funext fun k => mul_inv_cancel₀ (hw0 k)
          rw [this, diagonal_one, Matrix.mul_one]
      _ = 1 := hUU
  rw [hinv]
  conv_lhs => rw [hFe]
  have e2 : U * D * star U * (U * diagonal (fun k => (w k)⁻¹) * star U) =
      U * (D * diagonal (fun k => (w k)⁻¹)) * star U := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU', Matrix.one_mul]
  rw [e2, trace_mul_cycle, ← Matrix.mul_assoc, hUU', Matrix.one_mul, hD, diagonal_mul_diagonal,
    trace_diagonal]
  simp only [hw, div_eq_mul_inv]

/-- **The smoothed phase as a resolvent integral**: for Hermitian `M` and `y > 0`,
`Σ_j π⁻¹ arg(λ_j + iy) = W/2 + π⁻¹ ∫_0^1 Im Tr(M (uM + iy)⁻¹) du`. -/
theorem fcd_phase_eq {M : Matrix n n ℂ} (hM : M.IsHermitian) {y : ℝ} (hy : 0 < y) :
    spectralSum M (fcSmoothInd y) = Fintype.card n / 2 +
      Real.pi⁻¹ * ∫ u in (0 : ℝ)..1,
        ((M * ((u : ℂ) • M + ((y : ℂ) * I) • (1 : Matrix n n ℂ))⁻¹).trace).im := by
  rw [fc_spectralSum_eq hM]
  simp_rw [fcd_trace_mul_inv hM _ hy, Complex.im_sum]
  rw [intervalIntegral.integral_finsetSum
    (fun k _ => (fcd_continuous_eig (hM.eigenvalues k) hy).intervalIntegrable 0 1)]
  unfold fcSmoothInd
  simp_rw [fcd_arg_eq_integral _ hy]
  have hpi := Real.pi_pos.ne'
  rw [Finset.mul_sum]
  have : (Fintype.card n : ℝ) / 2 = ∑ _k : n, (1 / 2 : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  rw [this, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp

end Phase

/-!
## 3. Derivative of the smoothed phase along a Hermitian path

`d/ds π⁻¹ Σ_j arg(λ_j(M_s) + i y_s) = π⁻¹ Im Tr((M_s + iy_s)⁻¹ (M_s' + i y_s'))`
(`fcd_phase_hasDerivAt`): differentiate the resolvent integral of `fcd_phase_eq` under the
integral sign; the `u`-integral of the derivative is a total `u`-derivative.
-/

section PhaseDeriv

variable {n : Type} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem fcd_trace_cyc1 (A B R : Matrix n n ℂ) :
    (A * (R * (B * R))).trace = (B * (R * (A * R))).trace := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc B, trace_mul_comm]

omit [DecidableEq n] in
theorem fcd_trace_cyc2 (A R : Matrix n n ℂ) : (A * (R * R)).trace = (R * (A * R)).trace := by
  rw [← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc]

/-- `Im Tr(c R₀) = 0` at `u = 0`: `R₀ = (iy)⁻¹`, `c = iy'`. -/
theorem fcd_im_trace_zero (y y' : ℝ) (hy : y ≠ 0) :
    ((((y' : ℂ) * I) • (((y : ℂ) * I) • (1 : Matrix n n ℂ))⁻¹).trace).im = 0 := by
  have hc : ((y : ℂ) * I) ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hy) I_ne_zero
  have hinv : (((y : ℂ) * I) • (1 : Matrix n n ℂ))⁻¹ =
      ((y : ℂ) * I)⁻¹ • (1 : Matrix n n ℂ) := by
    apply inv_eq_right_inv
    rw [smul_mul_smul, Matrix.one_mul, mul_inv_cancel₀ hc, one_smul]
  rw [hinv, smul_smul, trace_smul, trace_one, smul_eq_mul]
  have : (y' : ℂ) * I * ((y : ℂ) * I)⁻¹ = ((y' / y : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [this]
  simp

theorem fcd_phase_hasDerivAt {U : Set ℝ} (hU : IsOpen U) {M M' : ℝ → Matrix n n ℂ}
    {y y' : ℝ → ℝ} {κ K : ℝ} (hκ : 0 < κ) (hH : ∀ s ∈ U, (M s).IsHermitian)
    (hMd : ∀ s ∈ U, HasDerivAt M (M' s) s) (hyd : ∀ s ∈ U, HasDerivAt y (y' s) s)
    (hy : ∀ s ∈ U, κ ≤ y s) (hMK : ∀ s ∈ U, ‖M s‖ ≤ K) (hM'K : ∀ s ∈ U, ‖M' s‖ ≤ K)
    (hy'K : ∀ s ∈ U, |y' s| ≤ K) {s₀ : ℝ} (hs₀ : s₀ ∈ U) :
    HasDerivAt (fun s => spectralSum (M s) (fcSmoothInd (y s)))
      (Real.pi⁻¹ * (((M s₀ + ((y s₀ : ℂ) * I) • (1 : Matrix n n ℂ))⁻¹ *
        (M' s₀ + ((y' s₀ : ℂ) * I) • (1 : Matrix n n ℂ))).trace).im) s₀ := by
  set Z : ℝ → ℝ → Matrix n n ℂ :=
    fun s u => (u : ℂ) • M s + ((y s : ℂ) * I) • (1 : Matrix n n ℂ) with hZdef
  have hZu : ∀ s ∈ U, ∀ u : ℝ, IsUnit (Z s u).det ∧ ‖(Z s u)⁻¹‖ ≤ κ⁻¹ := by
    intro s hs u
    have hy0 : 0 < y s := lt_of_lt_of_le hκ (hy s hs)
    obtain ⟨h1, h2⟩ := fcd_herm_inv (fcd_isHermitian_real_smul (hH s hs) u) hy0
    exact ⟨h1, h2.trans (inv_anti₀ hκ (hy s hs))⟩
  have hZdu : ∀ s u, HasDerivAt (fun u => Z s u) (M s) u := by
    intro s u
    have := (((hasDerivAt_id u).ofReal_comp).smul_const (M s)).add_const
      (((y s : ℂ) * I) • (1 : Matrix n n ℂ))
    simpa [hZdef] using this
  have hZds : ∀ s ∈ U, ∀ u : ℝ, HasDerivAt (fun s => Z s u)
      ((u : ℂ) • M' s + ((y' s : ℂ) * I) • (1 : Matrix n n ℂ)) s := by
    intro s hs u
    have h1 := (hMd s hs).const_smul (u : ℂ)
    have h2 : HasDerivAt (fun s => ((y s : ℂ) * I) • (1 : Matrix n n ℂ))
        (((y' s : ℂ) * I) • (1 : Matrix n n ℂ)) s :=
      (((hyd s hs).ofReal_comp).mul_const I).smul_const (1 : Matrix n n ℂ)
    exact h1.add h2
  have hRc : ∀ s ∈ U, Continuous fun u => (Z s u)⁻¹ := by
    intro s hs
    exact continuous_iff_continuousAt.2 fun u =>
      (fcd_hasDerivAt_inv (hZdu s u) (hZu s hs u).1).continuousAt
  set h : ℝ → ℝ → ℝ := fun s u => (M s * (Z s u)⁻¹).trace.im with hh
  set h' : ℝ → ℝ → ℝ := fun s u => (M' s * (Z s u)⁻¹ +
    M s * -((Z s u)⁻¹ * ((u : ℂ) • M' s + ((y' s : ℂ) * I) • (1 : Matrix n n ℂ)) *
      (Z s u)⁻¹)).trace.im with hh'
  have hhd : ∀ s ∈ U, ∀ u, HasDerivAt (fun s => h s u) (h' s u) s := by
    intro s hs u
    have hR := fcd_hasDerivAt_inv (hZds s hs u) (hZu s hs u).1
    have hP := (hMd s hs).mul hR
    exact fcdImTr.hasFDerivAt.comp_hasDerivAt s hP
  have hhc : ∀ s ∈ U, Continuous (h s) := by
    intro s hs
    have := hRc s hs
    simp only [hh]
    exact Complex.continuous_im.comp ((continuous_const.mul this).matrix_trace)
  have hh'c : Continuous (h' s₀) := by
    have := hRc s₀ hs₀
    simp only [hh']
    refine Complex.continuous_im.comp (Continuous.matrix_trace ?_)
    fun_prop
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hMK s₀ hs₀)
  set B : ℝ := Fintype.card n * (K * κ⁻¹ + K * (κ⁻¹ * (K + K * ‖(1 : Matrix n n ℂ)‖) * κ⁻¹))
    with hB
  have hbound : ∀ s ∈ U, ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖h' s u‖ ≤ B := by
    intro s hs u hu
    have hR := (hZu s hs u).2
    have hR0 := norm_nonneg (Z s u)⁻¹
    have hκi : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
    have hX : ‖(u : ℂ) • M' s + ((y' s : ℂ) * I) • (1 : Matrix n n ℂ)‖ ≤
        K + K * ‖(1 : Matrix n n ℂ)‖ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
        calc u * ‖M' s‖ ≤ 1 * K :=
              mul_le_mul hu.2 (hM'K s hs) (norm_nonneg _) zero_le_one
          _ = K := one_mul K
      · rw [norm_smul, norm_mul, Complex.norm_real, norm_I, mul_one, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hy'K s hs) (norm_nonneg _)
    rw [Real.norm_eq_abs]
    refine (fcd_abs_imTr_le _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_mul_le _ _).trans (mul_le_mul (hM'K s hs) hR hR0 hK0)
    · refine (norm_mul_le _ _).trans (mul_le_mul (hMK s hs) ?_ (norm_nonneg _) hK0)
      rw [norm_neg]
      refine (norm_mul_le _ _).trans (mul_le_mul ?_ hR hR0 (by positivity))
      exact (norm_mul_le _ _).trans (mul_le_mul hR hX (norm_nonneg _) hκi)
  have hUn : U ∈ 𝓝 s₀ := hU.mem_nhds hs₀
  obtain ⟨_, hInt⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := 0) (b := 1) (bound := fun _ => B) (F := h) (F' := h')
    hUn
    (Filter.eventually_of_mem hUn fun s hs => (hhc s hs).aestronglyMeasurable)
    ((hhc s₀ hs₀).intervalIntegrable 0 1)
    hh'c.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u hu s hs => by
      rw [Set.uIoc_of_le zero_le_one] at hu
      exact hbound s hs u (Set.Ioc_subset_Icc_self hu))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun u _ s hs => hhd s hs u)
  -- the `u`-integral of the derivative is a total derivative
  set Mo := M s₀
  set Mp := M' s₀
  set c : ℂ := (y' s₀ : ℂ) * I with hc
  set R : ℝ → Matrix n n ℂ := fun u => (Z s₀ u)⁻¹ with hRdef
  set Φ : ℝ → ℝ := fun u => ((u : ℂ) • (Mp * R u) + c • R u).trace.im with hΦ
  set Φ' : ℝ → ℝ := fun u => (Mp * R u + (u : ℂ) • (Mp * -(R u * Mo * R u)) +
    c • -(R u * Mo * R u)).trace.im with hΦ'
  have hΦd : ∀ u, HasDerivAt Φ (Φ' u) u := by
    intro u
    have hR : HasDerivAt R (-(R u * Mo * R u)) u :=
      fcd_hasDerivAt_inv (hZdu s₀ u) (hZu s₀ hs₀ u).1
    have h1 := ((hasDerivAt_id u).ofReal_comp).smul (hR.const_mul Mp)
    have h2 := (h1.add (hR.const_smul c))
    have h3 := fcdImTr.hasFDerivAt.comp_hasDerivAt u h2
    convert h3 using 1
    · rfl
    show (Mp * R u + (u : ℂ) • (Mp * -(R u * Mo * R u)) + c • -(R u * Mo * R u)).trace.im = _
    rw [fcdImTr_apply]
    simp only [id, Complex.ofReal_one, one_smul]
    congr 2
    abel
  have hΦ'c : Continuous Φ' := by
    have := hRc s₀ hs₀
    simp only [hΦ']
    refine Complex.continuous_im.comp (Continuous.matrix_trace ?_)
    fun_prop
  have heq : ∀ u, h' s₀ u = Φ' u := by
    intro u
    simp only [hh', hΦ']
    congr 1
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, trace_add, trace_neg, trace_smul, Matrix.mul_assoc,
      smul_neg]
    rw [fcd_trace_cyc1 Mo Mp, fcd_trace_cyc2 Mo, neg_add, ← add_assoc]
  have hval : ∫ u in (0 : ℝ)..1, h' s₀ u =
      (((M s₀ + ((y s₀ : ℂ) * I) • (1 : Matrix n n ℂ))⁻¹ *
        (M' s₀ + ((y' s₀ : ℂ) * I) • (1 : Matrix n n ℂ))).trace).im := by
    rw [intervalIntegral.integral_congr (fun u _ => heq u),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hΦd u) (hΦ'c.intervalIntegrable 0 1)]
    have hy0 : y s₀ ≠ 0 := (lt_of_lt_of_le hκ (hy s₀ hs₀)).ne'
    have h0 : Φ 0 = 0 := by
      simp only [hΦ, hRdef, hZdef, Complex.ofReal_zero, zero_smul, zero_add]
      exact fcd_im_trace_zero (y s₀) (y' s₀) hy0
    rw [h0, sub_zero]
    simp only [hΦ, hRdef, hZdef, Complex.ofReal_one, one_smul]
    congr 1
    rw [Matrix.mul_add, trace_add, trace_add, Matrix.mul_smul, Matrix.mul_one, trace_mul_comm]
  have hev : (fun s => spectralSum (M s) (fcSmoothInd (y s))) =ᶠ[𝓝 s₀]
      fun s => (Fintype.card n : ℝ) / 2 + Real.pi⁻¹ * ∫ u in (0 : ℝ)..1, h s u :=
    Filter.eventually_of_mem hUn fun s hs =>
      fcd_phase_eq (hH s hs) (lt_of_lt_of_le hκ (hy s hs))
  have hfin := (hInt.const_mul Real.pi⁻¹).const_add ((Fintype.card n : ℝ) / 2)
  rw [hval] at hfin
  exact hfin.congr_of_eventuallyEq hev

end PhaseDeriv

/-!
## 4. GUE coordinates: linearity, the Gaussian contraction, integration by parts

`gueOfCoords W t` is real-linear (`fcdGue`), its coordinate matrices are
`Λ_{(αβ,0)} = κ(E_αβ + E_βα)`, `Λ_{(αβ,1)} = κ(iE_αβ - iE_βα)`, `κ² = t/4`, and
`Σᵢ Λᵢ G Λᵢ = t Tr(G) · 1` (`fcd_gue_sandwich`). With `core_ibp` this gives
`E Tr(G A) = -σ t E (Tr G)²` for `G = (C₀ + σA + iκ)⁻¹` (`fcd_ibp`).
-/

section GueCoords

open BlockBand.SourceProcess (circularBrownianCoordinates)
open scoped ComplexConjugate

/-- The coordinate coefficient `κ = √(t/2)/√2`. -/
def fcdKappa (t : ℝ≥0) : ℂ := ((Real.sqrt ((t : ℝ) / 2) / Real.sqrt 2 : ℝ) : ℂ)

theorem fcd_lin0 (W : ℕ) (t : ℝ≥0) (α β : Fin W) :
    gueOfCoords W t (Pi.single ((α, β), 0) 1) =
      fcdKappa t • (single α β (1 : ℂ) + single β α 1) := by
  ext x y
  simp [gueOfCoords, gueSample, circularBrownianCoordinates, Pi.single_apply,
    Matrix.single_apply, fcdKappa]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr two_pos).ne'
  by_cases h1 : x = α <;> by_cases h2 : y = β <;> by_cases h3 : x = β <;> by_cases h4 : y = α <;>
    subst_vars <;> simp_all <;> (try ring_nf) <;> grind

theorem fcd_lin1 (W : ℕ) (t : ℝ≥0) (α β : Fin W) :
    gueOfCoords W t (Pi.single ((α, β), 1) 1) =
      fcdKappa t • (single α β I + single β α (-I)) := by
  ext x y
  simp [gueOfCoords, gueSample, circularBrownianCoordinates, Pi.single_apply,
    Matrix.single_apply, fcdKappa]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr two_pos).ne'
  by_cases h1 : x = α <;> by_cases h2 : y = β <;> by_cases h3 : x = β <;> by_cases h4 : y = α <;>
    subst_vars <;> simp_all <;> (try ring_nf) <;> grind
theorem fcdKappa_sq (t : ℝ≥0) : fcdKappa t * fcdKappa t * 2 = ((t : ℝ) : ℂ) / 2 := by
  have h1 : Real.sqrt ((t : ℝ) / 2) ^ 2 = (t : ℝ) / 2 := Real.sq_sqrt (by positivity)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have : Real.sqrt ((t : ℝ) / 2) / Real.sqrt 2 * (Real.sqrt ((t : ℝ) / 2) / Real.sqrt 2) * 2 =
      (t : ℝ) / 2 := by
    field_simp
    nlinarith [h1, h2]
  rw [fcdKappa]
  exact_mod_cast this

theorem fcd_sum_single_one (W : ℕ) :
    ∑ α : Fin W, single α α (1 : ℂ) = (1 : Matrix (Fin W) (Fin W) ℂ) := by
  ext x y
  rw [Matrix.sum_apply]
  by_cases h : x = y
  · subst h; simp [single_apply]
  · simp [single_apply, one_apply, h]

theorem fcd_gue_sandwich (W : ℕ) (t : ℝ≥0) (G : Matrix (Fin W) (Fin W) ℂ) :
    ∑ i : GaussCoord W, gueOfCoords W t (Pi.single i 1) * G * gueOfCoords W t (Pi.single i 1) =
      (((t : ℝ) : ℂ) * G.trace) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, fcd_lin0, fcd_lin1, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← smul_add, meq_sandwich]
  have h := meq_double_sum G (fun α : Fin W => α) (fun β => β)
  simp only at h
  simp only [smul_smul, ← Finset.smul_sum, h, fcd_sum_single_one, ← add_smul, fcdKappa_sq]
  rw [trace]
  congr 1
  simp only [diag_apply]
  ring

/-- `gueOfCoords W t` as a real continuous linear map. -/
def fcdGue (W : ℕ) (t : ℝ≥0) : (GaussCoord W → ℝ) →L[ℝ] Matrix (Fin W) (Fin W) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := gueOfCoords W t
      map_add' := fun x y => by
        ext a b
        simp only [gueOfCoords, gueSample, circularBrownianCoordinates, Matrix.of_apply,
          Pi.add_apply, Matrix.add_apply, Complex.ofReal_add, map_add, map_div₀, map_mul,
          Complex.conj_ofReal, Complex.conj_I]
        ring
      map_smul' := fun r x => by
        ext a b
        simp only [gueOfCoords, gueSample, circularBrownianCoordinates, Matrix.of_apply,
          Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply, Matrix.smul_apply,
          map_add, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.real_smul]
        ring }

theorem fcdGue_apply (W : ℕ) (t : ℝ≥0) (x : GaussCoord W → ℝ) :
    fcdGue W t x = gueOfCoords W t x := rfl

/-- **Gaussian integration by parts for the GUE resolvent trace.** For Hermitian `C₀`, `σ ≠ 0`,
`κ > 0` and `G = (C₀ + σA + iκ)⁻¹`, `A = gueOfCoords W t r`, `r` standard Gaussian:
`E Tr(G A) = -σ t E (Tr G)²`. -/
theorem fcd_ibp (W : ℕ) (t : ℝ≥0) {C0 : Matrix (Fin W) (Fin W) ℂ} (hC0 : C0.IsHermitian)
    {σ κ : ℝ} (hσ : σ ≠ 0) (hκ : 0 < κ) :
    ∫ r, ((C0 + (σ : ℂ) • gueOfCoords W t r + ((κ : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹ *
        gueOfCoords W t r).trace ∂stdGaussCoordLaw (GaussCoord W) =
      -((σ : ℂ) * ((t : ℝ) : ℂ)) * ∫ r, (((C0 + (σ : ℂ) • gueOfCoords W t r +
        ((κ : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹).trace) ^ 2
          ∂stdGaussCoordLaw (GaussCoord W) := by
  set v : GaussCoord W → ℝ≥0 := fun _ => 1 with hv
  have hstd : stdGaussCoordLaw (GaussCoord W) = gaussianProduct v := rfl
  set L : (GaussCoord W → ℝ) →L[ℝ] Matrix (Fin W) (Fin W) ℂ := σ • fcdGue W t with hLdef
  have hLx : ∀ x, L x = (σ : ℂ) • gueOfCoords W t x := by
    intro x
    rw [hLdef, _root_.smul_apply, fcdGue_apply, Complex.coe_smul]
  have hHx : ∀ x, (C0 + L x).IsHermitian := fun x =>
    hC0.add (by rw [hLx]; exact fcd_isHermitian_real_smul (gueOfCoords_isHermitian W t x) σ)
  have hreg : CoreReg C0 L := by
    intro κ' hκ' x
    obtain ⟨h1, h2⟩ := fcd_herm_inv (hHx x) hκ'
    have he : corePsi C0 L κ' x = C0 + L x + ((κ' : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
      unfold corePsi; abel
    rw [he, ← nonsing_inv_eq_ringInverse]
    exact ⟨(isUnit_iff_isUnit_det _).mpr h1, h2⟩
  set Z : (GaussCoord W → ℝ) → Matrix (Fin W) (Fin W) ℂ := fun x =>
    C0 + (σ : ℂ) • gueOfCoords W t x + ((κ : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ) with hZ
  have hG : ∀ x, coreG C0 L κ x = (Z x)⁻¹ := by
    intro x
    rw [coreG, ← nonsing_inv_eq_ringInverse, hZ]
    congr 1
    unfold corePsi
    rw [hLx]
    abel_nf
  have hS : ∀ G : Matrix (Fin W) (Fin W) ℂ,
      coreS v L G = (((σ : ℂ) ^ 2 * ((t : ℝ) : ℂ)) * G.trace) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
    intro G
    unfold coreS
    simp only [hv, NNReal.coe_one, one_smul, hLx, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [← Finset.smul_sum, fcd_gue_sandwich, smul_smul]
    congr 1
    ring
  have hibp := core_ibp v hreg hκ
  have hGc : Continuous (coreG C0 L κ) := coreG_continuous hreg hκ
  have hGb : ∀ x, ‖coreG C0 L κ x‖ ≤ κ⁻¹ := coreG_norm_le hreg hκ
  have hint1 : Integrable (fun x => L x * coreG C0 L κ x) (gaussianProduct v) := by
    refine ou_integrable_of_norm_le _ ((L.continuous.mul hGc).aestronglyMeasurable) 0
      (‖L‖ * κ⁻¹) fun x => ?_
    rw [zero_add]
    calc ‖L x * coreG C0 L κ x‖ ≤ ‖L x‖ * ‖coreG C0 L κ x‖ := norm_mul_le _ _
      _ ≤ (‖L‖ * ‖x‖) * κ⁻¹ := by
          gcongr
          · exact L.le_opNorm x
          · exact hGb x
      _ = ‖L‖ * κ⁻¹ * ‖x‖ := by ring
  have hSc : Continuous fun x => coreS v L (coreG C0 L κ x) * coreG C0 L κ x := by
    simp only [hS]
    have : Continuous fun x => (coreG C0 L κ x).trace := hGc.matrix_trace
    fun_prop
  have hint2 : Integrable (fun x => coreS v L (coreG C0 L κ x) * coreG C0 L κ x)
      (gaussianProduct v) := by
    refine Integrable.of_bound hSc.aestronglyMeasurable
      (‖(σ : ℂ) ^ 2 * ((t : ℝ) : ℂ)‖ * (W * κ⁻¹) * ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ * κ⁻¹)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [hS]
    have htr : ‖(coreG C0 L κ x).trace‖ ≤ W * κ⁻¹ := by
      refine (tfl_trace_le _).trans ?_
      rw [Fintype.card_fin]
      exact mul_le_mul_of_nonneg_left (hGb x) (Nat.cast_nonneg _)
    calc ‖((((σ : ℂ) ^ 2 * ((t : ℝ) : ℂ)) * (coreG C0 L κ x).trace) •
          (1 : Matrix (Fin W) (Fin W) ℂ)) * coreG C0 L κ x‖
        ≤ ‖(((σ : ℂ) ^ 2 * ((t : ℝ) : ℂ)) * (coreG C0 L κ x).trace) •
          (1 : Matrix (Fin W) (Fin W) ℂ)‖ * ‖coreG C0 L κ x‖ := norm_mul_le _ _
      _ ≤ (‖(σ : ℂ) ^ 2 * ((t : ℝ) : ℂ)‖ * (W * κ⁻¹) * ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖) * κ⁻¹ := by
          rw [norm_smul, norm_mul]
          gcongr
          exact hGb x
  have h1 := congrArg fcdTr hibp
  rw [map_neg, ← fcdTr.integral_comp_comm hint1, ← fcdTr.integral_comp_comm hint2] at h1
  simp only [fcdTr_apply, hS, hLx, hG, Matrix.smul_mul, Matrix.one_mul, trace_smul,
    smul_eq_mul] at h1
  have h2 : ∀ x, (gueOfCoords W t x * (Z x)⁻¹).trace = ((Z x)⁻¹ * gueOfCoords W t x).trace :=
    fun x => trace_mul_comm _ _
  simp only [h2] at h1
  rw [integral_const_mul] at h1
  rw [← hstd] at h1
  have hσ' : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ
  have h3 : ∀ x, (σ : ℂ) ^ 2 * ((t : ℝ) : ℂ) * (Z x)⁻¹.trace * (Z x)⁻¹.trace =
      (σ : ℂ) ^ 2 * ((t : ℝ) : ℂ) * ((Z x)⁻¹.trace) ^ 2 := fun x => by ring
  simp only [h3] at h1
  rw [integral_const_mul] at h1
  show ∫ r, ((Z r)⁻¹ * gueOfCoords W t r).trace ∂stdGaussCoordLaw (GaussCoord W) = _
  apply mul_left_cancel₀ hσ'
  rw [h1]
  ring

theorem fcd_smul_gue_apply (W : ℕ) (t : ℝ≥0) (σ : ℝ) (x : GaussCoord W → ℝ) :
    (σ • fcdGue W t) x = (σ : ℂ) • gueOfCoords W t x := by
  rw [_root_.smul_apply, fcdGue_apply, Complex.coe_smul]

/-- `CoreReg` for the Hermitian family `C₀ + σ A`, `C₀` Hermitian. -/
theorem fcd_coreReg (W : ℕ) (t : ℝ≥0) {C0 : Matrix (Fin W) (Fin W) ℂ} (hC0 : C0.IsHermitian)
    (σ : ℝ) : CoreReg C0 (σ • fcdGue W t) := by
  intro κ' hκ' x
  have hH : (C0 + (σ • fcdGue W t) x).IsHermitian := hC0.add (by
    rw [fcd_smul_gue_apply]; exact fcd_isHermitian_real_smul (gueOfCoords_isHermitian W t x) σ)
  obtain ⟨h1, h2⟩ := fcd_herm_inv hH hκ'
  have he : corePsi C0 (σ • fcdGue W t) κ' x =
      C0 + (σ • fcdGue W t) x + ((κ' : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
    unfold corePsi; abel
  rw [he, ← nonsing_inv_eq_ringInverse]
  exact ⟨(isUnit_iff_isUnit_det _).mpr h1, h2⟩

theorem fcd_coreG_eq (W : ℕ) (t : ℝ≥0) (C0 : Matrix (Fin W) (Fin W) ℂ) (σ κ : ℝ)
    (x : GaussCoord W → ℝ) :
    coreG C0 (σ • fcdGue W t) κ x =
      (C0 + (σ : ℂ) • gueOfCoords W t x + ((κ : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹ := by
  rw [coreG, ← nonsing_inv_eq_ringInverse]
  congr 1
  unfold corePsi
  rw [fcd_smul_gue_apply]
  abel_nf

end GueCoords

/-!
## 5. Measurability, continuity and the transfer to Gaussian coordinates
-/

section Transfer

variable {n : Type} [Fintype n] [DecidableEq n]

theorem fcd_measurable_inv : Measurable (fun M : Matrix n n ℂ => M⁻¹) := by
  have : (fun M : Matrix n n ℂ => M⁻¹) = fun M => (M.det)⁻¹ • M.adjugate := by
    funext M; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact (Continuous.matrix_det continuous_id).measurable.inv.smul
    (Continuous.matrix_adjugate continuous_id).measurable

theorem fcd_continuousAt_inv {X : Type*} [TopologicalSpace X] {Z : X → Matrix n n ℂ} {x : X}
    (hZ : ContinuousAt Z x) (hu : IsUnit (Z x).det) : ContinuousAt (fun x => (Z x)⁻¹) x := by
  have hu' : IsUnit (Z x) := (isUnit_iff_isUnit_det _).mpr hu
  have h := NormedRing.inverse_continuousAt hu'.unit
  rw [IsUnit.unit_spec] at h
  simp only [nonsing_inv_eq_ringInverse]
  exact h.comp hZ

theorem fcd_continuous_inv {X : Type*} [TopologicalSpace X] {Z : X → Matrix n n ℂ}
    (hZ : Continuous Z) (hu : ∀ x, IsUnit (Z x).det) : Continuous fun x => (Z x)⁻¹ :=
  continuous_iff_continuousAt.2 fun x => fcd_continuousAt_inv hZ.continuousAt (hu x)

end Transfer

theorem fcd_continuous_hermPart (W : ℕ) : Continuous (hermPart (ι := Fin W)) := by
  unfold hermPart
  have h1 : Continuous fun A : Matrix (Fin W) (Fin W) ℂ => A + Aᴴ :=
    continuous_id.add continuous_id.matrix_conjTranspose
  exact (continuous_const (y := (1 / 2 : ℂ))).smul h1

/-- **Transfer to Gaussian coordinates**: if `f ∘ hermPart` is a.e.-strongly measurable,
`∫ f dGUE_W(t) = ∫ f(gueOfCoords W t r) dr` (standard Gaussian `r`). -/
theorem fcd_integral_gue {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (W : ℕ)
    (t : ℝ≥0) (f : Matrix (Fin W) (Fin W) ℂ → X)
    (hf : AEStronglyMeasurable (fun A => f (hermPart A)) (gueMeasure (Fin W) t)) :
    ∫ A, f A ∂gueMeasure (Fin W) t =
      ∫ r, f (gueOfCoords W t r) ∂stdGaussCoordLaw (GaussCoord W) := by
  have hae : (fun A => f (hermPart A)) =ᵐ[gueMeasure (Fin W) t] f := by
    filter_upwards [fc_ae_isHermitian_gue W t] with A hA
    rw [hermPart_of_isHermitian hA]
  have hf' : AEStronglyMeasurable f (gueMeasure (Fin W) t) := hf.congr hae
  rw [gueMeasure_eq_map] at hf' ⊢
  exact integral_map (measurable_gueOfCoords W t).aemeasurable hf'

/-!
## 6. The heat path in `σ = √t`

`M_σ(A) = σA - (E + (1-σ²) c Re a) - F`, `y_σ = (1-σ²)γ + ε`, so that `H_{σ²} = M_σ + i y_σ`
for `σ ≥ 0` (`fcd_heatHerm_sq`). The phase `Ψ(σ) = E π⁻¹ Σ_j arg(λ_j(M_σ) + i y_σ)` is
differentiable in `σ` near `[0,1]` (`fcd_Psi_hasDerivAt`) and `Φ(t) = Ψ(√t)`.
-/

section HeatPathSigma

variable (b E : ℝ) {W : ℕ} (F : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ)

/-- The scalar shift `E + (1 - σ²) c Re a`. -/
def fcdS (σ : ℝ) : ℝ := E + (1 - σ ^ 2) * (1 - 2 * b) * (matchedA E).re

/-- `M_σ(A) = σA - (E + (1-σ²) c Re a) - F`. -/
def fcdM (σ : ℝ) (A : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  (σ : ℂ) • A - ((fcdS b E σ : ℝ) : ℂ) • 1 - F

/-- `y_σ = (1 - σ²)γ + ε`. -/
def fcdY (σ : ℝ) : ℝ := fcHeight' b E ε (σ ^ 2)

/-- `σ`-derivative of `M_σ(A)`. -/
def fcdM' (σ : ℝ) (A : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  A - ((-(2 * σ) * (1 - 2 * b) * (matchedA E).re : ℝ) : ℂ) • 1

/-- `σ`-derivative of `y_σ`. -/
def fcdY' (σ : ℝ) : ℝ := -(2 * σ) * fcGamma b E

/-- The integrand `π⁻¹ Σ_j arg(λ_j(M_σ(A)) + i y_σ)`. -/
def fcdP (σ : ℝ) (A : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  spectralSum (fcdM b E F σ A) (fcSmoothInd (fcdY b E ε σ))

/-- Its `σ`-derivative `π⁻¹ Im Tr((M_σ + iy_σ)⁻¹ (M_σ' + iy_σ'))`. -/
def fcdP' (σ : ℝ) (A : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  Real.pi⁻¹ * (((fcdM b E F σ A + ((fcdY b E ε σ : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹ *
    (fcdM' b E σ A + ((fcdY' b E σ : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ))).trace).im

theorem fcd_hasDerivAt_S (σ : ℝ) :
    HasDerivAt (fcdS b E) (-(2 * σ) * (1 - 2 * b) * (matchedA E).re) σ := by
  have h := (((hasDerivAt_pow 2 σ).const_sub 1).mul_const ((1 - 2 * b) * (matchedA E).re)).const_add E
  convert h using 1
  · funext s; simp only [fcdS]; ring
  · push_cast; ring

theorem fcd_hasDerivAt_M (σ : ℝ) (A : Matrix (Fin W) (Fin W) ℂ) :
    HasDerivAt (fun s => fcdM b E F s A) (fcdM' b E σ A) σ := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) • A) A σ := by
    simpa using ((hasDerivAt_id σ).ofReal_comp).smul_const A
  have h2 : HasDerivAt (fun s => ((fcdS b E s : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ))
      (((-(2 * σ) * (1 - 2 * b) * (matchedA E).re : ℝ) : ℂ) • 1) σ :=
    (fcd_hasDerivAt_S b E σ).ofReal_comp.smul_const _
  exact (h1.sub h2).sub_const F

theorem fcd_hasDerivAt_Y (σ : ℝ) : HasDerivAt (fcdY b E ε) (fcdY' b E σ) σ := by
  have h := (((hasDerivAt_pow 2 σ).const_sub 1).mul_const (fcGamma b E)).add_const ε
  convert h using 1
  · funext s; simp only [fcdY, fcHeight']
  · simp only [fcdY']; push_cast; ring

theorem fcd_isHermitian_M {F : Matrix (Fin W) (Fin W) ℂ} (hF : F.IsHermitian) (σ : ℝ)
    {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian) : (fcdM b E F σ A).IsHermitian := by
  unfold fcdM
  refine ((fcd_isHermitian_real_smul hA σ).sub ?_).sub hF
  exact fcd_isHermitian_real_smul isHermitian_one _

theorem fcd_gamma_nonneg {b : ℝ} (hb : b < 1 / 2) (E : ℝ) : 0 ≤ fcGamma b E := by
  unfold fcGamma
  rw [matchedA_im]
  have := Real.sqrt_nonneg (4 - E ^ 2)
  have hc : 0 < 1 - 2 * b := by linarith
  nlinarith

/-- **Pointwise `σ`-derivative of the phase integrand** on an open set `U` where
`y_σ ≥ κ > 0` and `|σ| ≤ R₀`. -/
theorem fcd_P_hasDerivAt {F : Matrix (Fin W) (Fin W) ℂ} (hF : F.IsHermitian)
    {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian) {U : Set ℝ} (hU : IsOpen U)
    {κ R₀ : ℝ} (hκ : 0 < κ) (hYU : ∀ s ∈ U, κ ≤ fcdY b E ε s) (hR : ∀ s ∈ U, |s| ≤ R₀)
    {s₀ : ℝ} (hs₀ : s₀ ∈ U) :
    HasDerivAt (fun s => fcdP b E F ε s A) (fcdP' b E F ε s₀ A) s₀ := by
  set k := (1 - 2 * b) * (matchedA E).re
  set o := ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖
  have hR0 : 0 ≤ R₀ := (abs_nonneg _).trans (hR s₀ hs₀)
  have ho : 0 ≤ o := norm_nonneg _
  set K := (R₀ + 1) * ‖A‖ + (|E| + (1 + R₀ ^ 2) * |k| + 2 * R₀ * |k|) * o + ‖F‖ +
    2 * R₀ * |fcGamma b E| with hK
  have hA0 := norm_nonneg A
  have hF0 := norm_nonneg F
  have hk0 := abs_nonneg k
  have hg0 := abs_nonneg (fcGamma b E)
  have hE0 := abs_nonneg E
  refine fcd_phase_hasDerivAt (M := fun s => fcdM b E F s A) (M' := fun s => fcdM' b E s A)
    (y := fcdY b E ε) (y' := fcdY' b E) (K := K) hU hκ
    (fun s _ => fcd_isHermitian_M b E hF s hA) (fun s _ => fcd_hasDerivAt_M b E F s A)
    (fun s _ => fcd_hasDerivAt_Y b E ε s) hYU ?_ ?_ ?_ hs₀
  · intro s hs
    have hs' := hR s hs
    have hS : |fcdS b E s| ≤ |E| + (1 + R₀ ^ 2) * |k| := by
      unfold fcdS
      have h1 : |(1 - s ^ 2) * (1 - 2 * b) * (matchedA E).re| ≤ (1 + R₀ ^ 2) * |k| := by
        rw [mul_assoc, abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ hk0
        have : s ^ 2 ≤ R₀ ^ 2 := by
          have := sq_abs s; nlinarith [abs_nonneg s]
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg s]
      exact (abs_add_le _ _).trans (by linarith)
    calc ‖fcdM b E F s A‖ ≤ |s| * ‖A‖ + |fcdS b E s| * o + ‖F‖ := by
          unfold fcdM
          refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
            (add_le_add ?_ ?_)) le_rfl)
          · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ R₀ * ‖A‖ + (|E| + (1 + R₀ ^ 2) * |k|) * o + ‖F‖ := by
          gcongr
      _ ≤ K := by rw [hK]; nlinarith [mul_nonneg hR0 hk0, mul_nonneg (mul_nonneg hR0 hk0) ho,
            mul_nonneg hR0 hg0]
  · intro s hs
    have hs' := hR s hs
    calc ‖fcdM' b E s A‖ ≤ ‖A‖ + |-(2 * s) * (1 - 2 * b) * (matchedA E).re| * o := by
          unfold fcdM'
          refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖A‖ + 2 * R₀ * |k| * o := by
          gcongr
          rw [mul_assoc, abs_mul, abs_neg, abs_mul, abs_two]
          exact mul_le_mul_of_nonneg_right (by linarith) hk0
      _ ≤ K := by
          rw [hK]
          nlinarith [mul_nonneg hR0 hA0, mul_nonneg (mul_nonneg (sq_nonneg R₀) hk0) ho,
            mul_nonneg hE0 ho, mul_nonneg hk0 ho, mul_nonneg hR0 hg0]
  · intro s hs
    have hs' := hR s hs
    calc |fcdY' b E s| = 2 * |s| * |fcGamma b E| := by
          unfold fcdY'; rw [abs_mul, abs_neg, abs_mul, abs_two]
      _ ≤ 2 * R₀ * |fcGamma b E| := by gcongr
      _ ≤ K := by
          rw [hK]
          nlinarith [mul_nonneg hR0 hA0, mul_nonneg (mul_nonneg (sq_nonneg R₀) hk0) ho,
            mul_nonneg hE0 ho, mul_nonneg hk0 ho, mul_nonneg (mul_nonneg hR0 hk0) ho]

/-- The GUE variance `c/W`. -/
def fcdTau (b : ℝ) (W : ℕ) : ℝ≥0 := Real.toNNReal ((1 - 2 * b) / W)

/-- `Ψ(σ) = E π⁻¹ Σ_j arg(λ_j(M_σ(A)) + i y_σ)` in Gaussian coordinates. -/
def fcdPsi (σ : ℝ) : ℝ :=
  ∫ r, fcdP b E F ε σ (gueOfCoords W (fcdTau b W) r) ∂stdGaussCoordLaw (GaussCoord W)

/-- `Ψ'(σ) = E fcdP'`. -/
def fcdPsi' (σ : ℝ) : ℝ :=
  ∫ r, fcdP' b E F ε σ (gueOfCoords W (fcdTau b W) r) ∂stdGaussCoordLaw (GaussCoord W)

theorem fcd_continuous_M (σ : ℝ) (t : ℝ≥0) :
    Continuous fun r => fcdM b E F σ (gueOfCoords W t r) := by
  unfold fcdM
  exact (((continuous_const (y := (σ : ℂ))).smul (continuous_gueOfCoords W t)).sub
    continuous_const).sub continuous_const

theorem fcd_measurable_P {F : Matrix (Fin W) (Fin W) ℂ} (hF : F.IsHermitian) (σ : ℝ)
    (t : ℝ≥0) : Measurable fun r => fcdP b E F ε σ (gueOfCoords W t r) :=
  fc_measurable_spectralSum (fcd_continuous_M b E F σ t).measurable
    (fun r => fcd_isHermitian_M b E hF σ (gueOfCoords_isHermitian W t r))
    (fc_measurable_smoothInd _)

/-- **`Ψ` is differentiable on `[0,1]`**, with derivative `Ψ'` (differentiation under the
Gaussian integral; the derivative is dominated by `C(1 + ‖r‖)`). -/
theorem fcd_Psi_hasDerivAt {F : Matrix (Fin W) (Fin W) ℂ} (hF : F.IsHermitian) {b : ℝ}
    (hb : b < 1 / 2) {ε : ℝ} (hε : 0 < ε) {σ₀ : ℝ} (hσ₀ : σ₀ ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fcdPsi b E F ε) (fcdPsi' b E F ε σ₀) σ₀ := by
  set γ := fcGamma b E with hγ
  have hγ0 : 0 ≤ γ := fcd_gamma_nonneg hb E
  set ρ := min 1 (ε / (4 * (γ + 1))) with hρ
  have hρ0 : 0 < ρ := lt_min one_pos (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hργ : ρ * γ ≤ ε / 4 := by
    have h1 : ρ ≤ ε / (4 * (γ + 1)) := min_le_right _ _
    have h2 : ρ * (4 * (γ + 1)) ≤ ε := by rwa [le_div_iff₀ (by positivity)] at h1
    nlinarith
  set U := Metric.ball σ₀ ρ with hU
  have hUo : IsOpen U := Metric.isOpen_ball
  have hUs : ∀ s ∈ U, |s| ≤ 2 ∧ ε / 4 ≤ fcdY b E ε s := by
    intro s hs
    rw [hU, Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    have hs1 : s ≤ 1 + ρ := by linarith [hσ₀.2]
    have hs2 : -ρ ≤ s := by linarith [hσ₀.1]
    refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
    have hsq : s ^ 2 ≤ 1 + 3 * ρ := by nlinarith
    unfold fcdY fcHeight'
    nlinarith
  set κ := ε / 4 with hκ
  have hκ0 : 0 < κ := by positivity
  set τ := fcdTau b W
  set k := (1 - 2 * b) * (matchedA E).re
  set o := ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖
  set c1 := 4 * |k| * o + 4 * γ * o with hc1
  set bound : (GaussCoord W → ℝ) → ℝ := fun r =>
    Real.pi⁻¹ * (W * (κ⁻¹ * (‖fcdGue W τ‖ * ‖r‖ + c1))) with hbound
  have hpi : 0 < Real.pi⁻¹ := inv_pos.mpr Real.pi_pos
  have hP'le : ∀ r, ∀ σ ∈ U, ‖fcdP' b E F ε σ (gueOfCoords W τ r)‖ ≤ bound r := by
    intro r σ hσ
    obtain ⟨hσ2, hYσ⟩ := hUs σ hσ
    set A := gueOfCoords W τ r
    have hY0 : 0 < fcdY b E ε σ := lt_of_lt_of_le hκ0 hYσ
    obtain ⟨_, hRb⟩ := fcd_herm_inv (fcd_isHermitian_M b E hF σ (gueOfCoords_isHermitian W τ r)) hY0
    have hRb' := hRb.trans (inv_anti₀ hκ0 hYσ)
    have hX : ‖fcdM' b E σ A + ((fcdY' b E σ : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤
        ‖fcdGue W τ‖ * ‖r‖ + c1 := by
      have hA : ‖A‖ ≤ ‖fcdGue W τ‖ * ‖r‖ := (fcdGue W τ).le_opNorm r
      have h1 : ‖((-(2 * σ) * (1 - 2 * b) * (matchedA E).re : ℝ) : ℂ) •
          (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 4 * |k| * o := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [mul_assoc, abs_mul, abs_neg, abs_mul, abs_two]
        exact mul_le_mul_of_nonneg_right (by linarith [hσ2]) (abs_nonneg _)
      have h2 : ‖((fcdY' b E σ : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 4 * γ * o := by
        rw [norm_smul, norm_mul, Complex.norm_real, norm_I, mul_one, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        unfold fcdY'
        rw [abs_mul, abs_neg, abs_mul, abs_two, ← hγ, abs_of_nonneg hγ0]
        exact mul_le_mul_of_nonneg_right (by linarith [hσ2]) hγ0
      unfold fcdM'
      calc _ ≤ ‖A - ((-(2 * σ) * (1 - 2 * b) * (matchedA E).re : ℝ) : ℂ) •
            (1 : Matrix (Fin W) (Fin W) ℂ)‖ + ‖((fcdY' b E σ : ℂ) * I) •
              (1 : Matrix (Fin W) (Fin W) ℂ)‖ := norm_add_le _ _
        _ ≤ (‖A‖ + 4 * |k| * o) + 4 * γ * o := add_le_add ((norm_sub_le _ _).trans
            (add_le_add le_rfl h1)) h2
        _ ≤ ‖fcdGue W τ‖ * ‖r‖ + c1 := by rw [hc1]; linarith
    unfold fcdP'
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpi]
    refine mul_le_mul_of_nonneg_left ?_ hpi.le
    refine (fcd_abs_imTr_le _).trans ?_
    rw [Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact (norm_mul_le _ _).trans (mul_le_mul hRb' hX (norm_nonneg _) (inv_nonneg.mpr hκ0.le))
  have hbi : Integrable bound (stdGaussCoordLaw (GaussCoord W)) := by
    have hstd : stdGaussCoordLaw (GaussCoord W) = gaussianProduct (fun _ => (1 : ℝ≥0)) := rfl
    have hid : Integrable (fun r : GaussCoord W → ℝ => ‖r‖) (stdGaussCoordLaw (GaussCoord W)) := by
      rw [hstd]; exact IsGaussian.integrable_id.norm
    exact ((((hid.const_mul ‖fcdGue W τ‖).add (integrable_const c1)).const_mul κ⁻¹).const_mul
      (W : ℝ)).const_mul Real.pi⁻¹
  have hσ₀U : σ₀ ∈ U := Metric.mem_ball_self hρ0
  have hY0 : 0 < fcdY b E ε σ₀ := lt_of_lt_of_le hκ0 (hUs σ₀ hσ₀U).2
  have hP'c : Continuous fun r => fcdP' b E F ε σ₀ (gueOfCoords W τ r) := by
    have hRc : Continuous fun r => (fcdM b E F σ₀ (gueOfCoords W τ r) +
        ((fcdY b E ε σ₀ : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹ :=
      fcd_continuous_inv ((fcd_continuous_M b E F σ₀ τ).add continuous_const) fun r =>
        (fcd_herm_inv (fcd_isHermitian_M b E hF σ₀ (gueOfCoords_isHermitian W τ r)) hY0).1
    have hM'c : Continuous fun r => fcdM' b E σ₀ (gueOfCoords W τ r) := by
      unfold fcdM'
      exact (continuous_gueOfCoords W τ).sub continuous_const
    unfold fcdP'
    exact continuous_const.mul (Complex.continuous_im.comp
      ((hRc.mul (hM'c.add continuous_const)).matrix_trace))
  have hPint : Integrable (fun r => fcdP b E F ε σ₀ (gueOfCoords W τ r))
      (stdGaussCoordLaw (GaussCoord W)) :=
    Integrable.of_bound (fcd_measurable_P b E ε hF σ₀ τ).aestronglyMeasurable (W * 1)
      (Filter.Eventually.of_forall fun r => by
        have h := fc_abs_spectralSum_le
          (fcd_isHermitian_M b E hF σ₀ (gueOfCoords_isHermitian W τ r))
          (fc_abs_smoothInd_le hY0.le)
        rw [Fintype.card_fin] at h
        rw [Real.norm_eq_abs]
        exact h)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := stdGaussCoordLaw (GaussCoord W))
    (F := fun σ r => fcdP b E F ε σ (gueOfCoords W τ r))
    (F' := fun σ r => fcdP' b E F ε σ (gueOfCoords W τ r)) (x₀ := σ₀) (bound := bound)
    (hUo.mem_nhds hσ₀U)
    (Filter.Eventually.of_forall fun σ => (fcd_measurable_P b E ε hF σ τ).aestronglyMeasurable)
    hPint hP'c.aestronglyMeasurable
    (Filter.Eventually.of_forall fun r σ hσ => hP'le r σ hσ) hbi
    (Filter.Eventually.of_forall fun r σ hσ =>
      fcd_P_hasDerivAt b E ε hF (gueOfCoords_isHermitian W τ r) hUo hκ0
        (fun s hs => (hUs s hs).2) (fun s hs => (hUs s hs).1) hσ)
  exact h.2

end HeatPathSigma

/-!
## 7. The heat path `H_t` in Gaussian coordinates
-/

section HeatCoords

variable (b E : ℝ) {W : ℕ} (F : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ)

theorem fcd_heatHerm_sq {σ : ℝ} (hσ : 0 ≤ σ) (A : Matrix (Fin W) (Fin W) ℂ) :
    fcHeatHerm b E F (σ ^ 2) A = fcdM b E F σ A := by
  unfold fcHeatHerm fcdM fcdS
  rw [Real.sqrt_sq hσ]

theorem fcd_heatMatrix_sq {σ : ℝ} (hσ : 0 ≤ σ) (A : Matrix (Fin W) (Fin W) ℂ) :
    fcHeatMatrix b E F ε (σ ^ 2) A =
      fcdM b E F σ A + ((fcdY b E ε σ : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
  unfold fcHeatMatrix
  rw [fcd_heatHerm_sq b E F hσ]
  rfl

theorem fcd_isHermitian_heatHerm {F : Matrix (Fin W) (Fin W) ℂ} (hF : F.IsHermitian) (t : ℝ)
    {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian) : (fcHeatHerm b E F t A).IsHermitian := by
  unfold fcHeatHerm
  refine ((fcd_isHermitian_real_smul hA _).sub ?_).sub hF
  exact fcd_isHermitian_real_smul isHermitian_one _

theorem fcd_continuous_heatHerm (t : ℝ) : Continuous (fcHeatHerm b E F t) := by
  unfold fcHeatHerm
  exact (((continuous_const (y := (Real.sqrt t : ℂ))).smul continuous_id).sub
    continuous_const).sub continuous_const

theorem fcd_continuous_heatMatrix (t : ℝ) : Continuous (fcHeatMatrix b E F ε t) := by
  unfold fcHeatMatrix
  exact (fcd_continuous_heatHerm b E F t).add continuous_const

/-- For `t ≤ 1`: `H_t` is invertible with `‖H_t⁻¹‖ ≤ ε⁻¹`. -/
theorem fcd_heatMatrix_inv {b : ℝ} (hb : b < 1 / 2) {F : Matrix (Fin W) (Fin W) ℂ}
    (hF : F.IsHermitian) {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : t ≤ 1)
    {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian) :
    IsUnit (fcHeatMatrix b E F ε t A).det ∧ ‖(fcHeatMatrix b E F ε t A)⁻¹‖ ≤ ε⁻¹ := by
  have hγ := fcd_gamma_nonneg hb E
  have hy : ε ≤ fcHeight' b E ε t := by
    unfold fcHeight'
    nlinarith
  obtain ⟨h1, h2⟩ := fcd_herm_inv (fcd_isHermitian_heatHerm b E hF t hA) (lt_of_lt_of_le hε hy)
  exact ⟨h1, h2.trans (inv_anti₀ hε hy)⟩

/-- `|g_t| ≤ ε⁻¹` for `t ≤ 1`. -/
theorem fcd_heatTrace_le {b : ℝ} (hb : b < 1 / 2) {F : Matrix (Fin W) (Fin W) ℂ}
    (hF : F.IsHermitian) {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : t ≤ 1) (hW : 0 < W)
    {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian) :
    ‖fcHeatTrace b E F ε t A‖ ≤ ε⁻¹ := by
  have h := (fcd_heatMatrix_inv E hb hF hε ht hA).2
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  unfold fcHeatTrace
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (W : ℝ)⁻¹ * ‖((fcHeatMatrix b E F ε t A)⁻¹).trace‖
      ≤ (W : ℝ)⁻¹ * (W * ε⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hW'.le)
        refine (tfl_trace_le _).trans ?_
        rw [Fintype.card_fin]
        exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
    _ = ε⁻¹ := by field_simp

theorem fcd_measurable_heatTrace (t : ℝ) {X : Type*} [MeasurableSpace X]
    {f : X → Matrix (Fin W) (Fin W) ℂ} (hf : Measurable f) :
    Measurable fun x => fcHeatTrace b E F ε t (f x) := by
  unfold fcHeatTrace
  exact measurable_const.mul ((continuous_id.matrix_trace).measurable.comp
    (fcd_measurable_inv.comp ((fcd_continuous_heatMatrix b E F ε t).measurable.comp hf)))

/-- Transfer of `Φ(t)` to Gaussian coordinates. -/
theorem fcd_heatPhase_coords {F : Matrix (Fin W) (Fin W) ℂ} (hF : F.IsHermitian) (t : ℝ) :
    fcHeatPhase b E F ε t = ∫ r, spectralSum (fcHeatHerm b E F t (gueOfCoords W (fcdTau b W) r))
      (fcSmoothInd (fcHeight' b E ε t)) ∂stdGaussCoordLaw (GaussCoord W) := by
  unfold fcHeatPhase
  refine fcd_integral_gue W _ _ ?_
  exact (fc_measurable_spectralSum ((fcd_continuous_heatHerm b E F t).comp
    (fcd_continuous_hermPart W)).measurable
    (fun A => fcd_isHermitian_heatHerm b E hF t (hermPart_isHermitian A))
    (fc_measurable_smoothInd _)).aestronglyMeasurable

/-- `Φ(t) = Ψ(√t)` for `t ≥ 0`. -/
theorem fcd_heatPhase_eq_Psi {F : Matrix (Fin W) (Fin W) ℂ} (hF : F.IsHermitian) {t : ℝ}
    (ht : 0 ≤ t) : fcHeatPhase b E F ε t = fcdPsi b E F ε (Real.sqrt t) := by
  rw [fcd_heatPhase_coords b E ε hF t]
  unfold fcdPsi fcdP
  have h := Real.sq_sqrt ht
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only
  rw [← fcd_heatHerm_sq b E F (Real.sqrt_nonneg t), h]
  unfold fcdY
  rw [h]

/-- Transfer of `E(g_t - a)²` to Gaussian coordinates. -/
theorem fcd_heatSq_coords (t : ℝ) :
    (∫ A, (fcHeatTrace b E F ε t A - matchedA E) ^ 2
        ∂gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) =
      ∫ r, (fcHeatTrace b E F ε t (gueOfCoords W (fcdTau b W) r) - matchedA E) ^ 2
        ∂stdGaussCoordLaw (GaussCoord W) := by
  refine fcd_integral_gue W _ _ ?_
  exact (((fcd_measurable_heatTrace b E F ε t (measurable_hermPart W)).sub
    measurable_const).pow_const 2).aestronglyMeasurable

end HeatCoords

/-!
## 8. The heat derivative formula

For `σ ∈ (0,1]`: `Ψ'(σ)/(2σ) = (cW/2π) Im a² - (cW/2π) Im E(g_{σ²} - a)²`. Here
`Ψ'(σ) = π⁻¹ Im E Tr(R(A + 2σca))`, `E Tr(RA) = -στ E(Tr R)²` (`fcd_ibp`, `τ = c/W`) and
`Tr R = W g`.
-/

section Formula

variable (b E : ℝ) {W : ℕ} (F : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ)

theorem fcd_tau_coe {b : ℝ} (hb : b < 1 / 2) (W : ℕ) :
    ((fcdTau b W : ℝ≥0) : ℝ) = (1 - 2 * b) / W := by
  unfold fcdTau
  rw [Real.coe_toNNReal _ (div_nonneg (by linarith) (Nat.cast_nonneg _))]

theorem fcd_dir_eq (σ : ℝ) (A : Matrix (Fin W) (Fin W) ℂ) :
    fcdM' b E σ A + ((fcdY' b E σ : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ) =
      A + ((((2 * σ * (1 - 2 * b)) : ℝ) : ℂ) * matchedA E) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
  have hs : -(((-(2 * σ) * (1 - 2 * b) * (matchedA E).re : ℝ) : ℂ)) + (fcdY' b E σ : ℂ) * I =
      (((2 * σ * (1 - 2 * b)) : ℝ) : ℂ) * matchedA E := by
    apply Complex.ext
    · simp [fcdY', fcGamma]
    · simp [fcdY', fcGamma]
      ring
  unfold fcdM'
  rw [← hs, add_smul, neg_smul]
  abel

theorem fcd_Psi'_eq {b : ℝ} (hb : b < 1 / 2) (hW : 0 < W) {F : Matrix (Fin W) (Fin W) ℂ}
    (hF : F.IsHermitian) {ε : ℝ} (hε : 0 < ε) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    fcdPsi' b E F ε σ * (1 / (2 * σ)) =
      (1 - 2 * b) * W / (2 * Real.pi) * (matchedA E ^ 2).im -
        (1 - 2 * b) * W / (2 * Real.pi) *
          (∫ A, (fcHeatTrace b E F ε (σ ^ 2) A - matchedA E) ^ 2
            ∂gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))).im := by
  set τ := fcdTau b W with hτdef
  have hτ := fcd_tau_coe hb W
  set μ := stdGaussCoordLaw (GaussCoord W)
  have hstd : μ = gaussianProduct (fun _ => (1 : ℝ≥0)) := rfl
  set a := matchedA E
  set Y := fcdY b E ε σ with hYdef
  have hγ := fcd_gamma_nonneg hb E
  have hYε : ε ≤ Y := by
    have : σ ^ 2 ≤ 1 := by nlinarith
    simp only [hYdef, fcdY, fcHeight']
    nlinarith
  have hY : 0 < Y := lt_of_lt_of_le hε hYε
  set Z : (GaussCoord W → ℝ) → Matrix (Fin W) (Fin W) ℂ := fun r =>
    fcdM b E F σ (gueOfCoords W τ r) + ((Y : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ) with hZ
  have hZu : ∀ r, IsUnit (Z r).det ∧ ‖(Z r)⁻¹‖ ≤ Y⁻¹ := fun r =>
    fcd_herm_inv (fcd_isHermitian_M b E hF σ (gueOfCoords_isHermitian W τ r)) hY
  have hRc : Continuous fun r => (Z r)⁻¹ :=
    fcd_continuous_inv ((fcd_continuous_M b E F σ τ).add continuous_const) fun r => (hZu r).1
  have hTc : Continuous fun r => ((Z r)⁻¹).trace := hRc.matrix_trace
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hTb : ∀ r, ‖((Z r)⁻¹).trace‖ ≤ W * Y⁻¹ := fun r => by
    refine (tfl_trace_le _).trans ?_
    rw [Fintype.card_fin]
    exact mul_le_mul_of_nonneg_left (hZu r).2 (Nat.cast_nonneg _)
  have hiT : Integrable (fun r => ((Z r)⁻¹).trace) μ :=
    Integrable.of_bound hTc.aestronglyMeasurable _ (Filter.Eventually.of_forall hTb)
  have hiT2 : Integrable (fun r => ((Z r)⁻¹).trace ^ 2) μ := by
    refine Integrable.of_bound (hTc.pow 2).aestronglyMeasurable ((W * Y⁻¹) ^ 2)
      (Filter.Eventually.of_forall fun r => ?_)
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hTb r) 2
  have hiRA : Integrable (fun r => ((Z r)⁻¹ * gueOfCoords W τ r).trace) μ := by
    rw [hstd]
    refine ou_integrable_of_norm_le _ ((hRc.mul (continuous_gueOfCoords W τ)).matrix_trace
      |>.aestronglyMeasurable) 0 (W * (Y⁻¹ * ‖fcdGue W τ‖)) fun r => ?_
    rw [zero_add]
    refine (tfl_trace_le _).trans ?_
    rw [Fintype.card_fin, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc ‖(Z r)⁻¹ * gueOfCoords W τ r‖ ≤ ‖(Z r)⁻¹‖ * ‖gueOfCoords W τ r‖ := norm_mul_le _ _
      _ ≤ Y⁻¹ * (‖fcdGue W τ‖ * ‖r‖) :=
          mul_le_mul (hZu r).2 ((fcdGue W τ).le_opNorm r) (norm_nonneg _)
            (inv_nonneg.mpr hY.le)
      _ = Y⁻¹ * ‖fcdGue W τ‖ * ‖r‖ := by ring
  set w : ℂ := (((2 * σ * (1 - 2 * b)) : ℝ) : ℂ) * a with hw
  have hP' : ∀ r, fcdP' b E F ε σ (gueOfCoords W τ r) =
      Real.pi⁻¹ * (((Z r)⁻¹ * gueOfCoords W τ r).trace + w * ((Z r)⁻¹).trace).im := by
    intro r
    unfold fcdP'
    rw [fcd_dir_eq, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, trace_add, trace_smul,
      smul_eq_mul]
  -- `Ψ'(σ) = π⁻¹ Im (E Tr(RA) + w E Tr R)`
  have hPsi' : fcdPsi' b E F ε σ =
      Real.pi⁻¹ * ((∫ r, ((Z r)⁻¹ * gueOfCoords W τ r).trace ∂μ) +
        w * ∫ r, ((Z r)⁻¹).trace ∂μ).im := by
    unfold fcdPsi'
    have hf : (fun r => fcdP' b E F ε σ (gueOfCoords W τ r)) = fun r =>
        Real.pi⁻¹ * (((Z r)⁻¹ * gueOfCoords W τ r).trace + w * ((Z r)⁻¹).trace).im := funext hP'
    show ∫ r, fcdP' b E F ε σ (gueOfCoords W τ r) ∂μ = _
    rw [hf, integral_const_mul]
    congr 1
    have hi := hiRA.add (hiT.const_mul w)
    have h1 := integral_im hi
    simp only [Pi.add_apply, RCLike.im_to_complex] at h1
    rw [h1, integral_add hiRA (hiT.const_mul w), integral_const_mul]
  -- integration by parts
  have hC0 : (-((fcdS b E σ : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) - F).IsHermitian :=
    by rw [neg_smul]; exact (fcd_isHermitian_real_smul isHermitian_one _).neg.sub hF
  have hibp := fcd_ibp W τ hC0 hσ.ne' hY
  have hZeq : ∀ r, -((fcdS b E σ : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) - F +
      (σ : ℂ) • gueOfCoords W τ r + ((Y : ℂ) * I) • (1 : Matrix (Fin W) (Fin W) ℂ) = Z r := by
    intro r
    simp only [hZ, fcdM, neg_smul]
    abel
  simp only [hZeq] at hibp
  -- the mean square in coordinates
  have hQ : (∫ A, (fcHeatTrace b E F ε (σ ^ 2) A - a) ^ 2
      ∂gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) =
      ((W : ℂ)⁻¹) ^ 2 * (∫ r, ((Z r)⁻¹).trace ^ 2 ∂μ) -
        2 * a * (W : ℂ)⁻¹ * (∫ r, ((Z r)⁻¹).trace ∂μ) + a ^ 2 := by
    have hpt : ∀ r, (fcHeatTrace b E F ε (σ ^ 2) (gueOfCoords W τ r) - a) ^ 2 =
        ((W : ℂ)⁻¹) ^ 2 * ((Z r)⁻¹).trace ^ 2 - 2 * a * (W : ℂ)⁻¹ * ((Z r)⁻¹).trace + a ^ 2 := by
      intro r
      unfold fcHeatTrace
      rw [fcd_heatMatrix_sq b E F ε hσ.le]
      ring
    have hf : (fun r => (fcHeatTrace b E F ε (σ ^ 2) (gueOfCoords W τ r) - a) ^ 2) = fun r =>
        ((W : ℂ)⁻¹) ^ 2 * ((Z r)⁻¹).trace ^ 2 - 2 * a * (W : ℂ)⁻¹ * ((Z r)⁻¹).trace + a ^ 2 :=
      funext hpt
    rw [fcd_heatSq_coords]
    show ∫ r, (fcHeatTrace b E F ε (σ ^ 2) (gueOfCoords W τ r) - a) ^ 2 ∂μ = _
    have i1 : Integrable (fun r => ((W : ℂ)⁻¹) ^ 2 * ((Z r)⁻¹).trace ^ 2 -
        2 * a * (W : ℂ)⁻¹ * ((Z r)⁻¹).trace) μ := (hiT2.const_mul _).sub (hiT.const_mul _)
    have i2 : Integrable (fun r => ((W : ℂ)⁻¹) ^ 2 * ((Z r)⁻¹).trace ^ 2) μ := hiT2.const_mul _
    have i3 : Integrable (fun r => 2 * a * (W : ℂ)⁻¹ * ((Z r)⁻¹).trace) μ := hiT.const_mul _
    rw [hf, integral_add i1 (integrable_const _), integral_sub i2 i3, integral_const_mul,
      integral_const_mul, integral_const, probReal_univ, one_smul]
  rw [hPsi', hibp, hQ, hτ]
  -- algebra
  set X := ∫ r, ((Z r)⁻¹).trace ^ 2 ∂μ
  set T := ∫ r, ((Z r)⁻¹).trace ∂μ
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hWc : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hW.ne'
  have hσc : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
  have key : (((Real.pi⁻¹ * (1 / (2 * σ))) : ℝ) : ℂ) *
      (-((σ : ℂ) * (((1 - 2 * b) / W : ℝ) : ℂ)) * X + w * T) =
      ((((1 - 2 * b) * W / (2 * Real.pi)) : ℝ) : ℂ) *
        (a ^ 2 - (((W : ℂ)⁻¹) ^ 2 * X - 2 * a * (W : ℂ)⁻¹ * T + a ^ 2)) := by
    rw [hw]
    push_cast
    field_simp
    ring
  have e1 := congrArg Complex.im key
  rw [im_ofReal_mul, im_ofReal_mul, sub_im] at e1
  rw [mul_comm (Real.pi⁻¹ * _), mul_assoc, ← mul_assoc (1 / (2 * σ))] at *
  nlinarith [e1]

/-- `t ↦ E(g_t - a)²` is continuous at `t = 0` (dominated convergence, `|g_t| ≤ ε⁻¹`). -/
theorem fcd_heatSq_continuousAt {b : ℝ} (hb : b < 1 / 2) (hE : |E| < 2) (hW : 0 < W)
    {F : Matrix (Fin W) (Fin W) ℂ} (hF : F.IsHermitian) {ε : ℝ} (hε : 0 < ε) :
    ContinuousAt (fun t => ∫ A, (fcHeatTrace b E F ε t A - matchedA E) ^ 2
      ∂gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) 0 := by
  simp only [fcd_heatSq_coords]
  set τ := fcdTau b W
  have ha : ‖matchedA E‖ = 1 := norm_matchedA hE.le
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), t ≤ 1 :=
    Filter.eventually_of_mem (Iio_mem_nhds one_pos) fun t ht => (Set.mem_Iio.mp ht).le
  refine continuousAt_of_dominated (bound := fun _ => (ε⁻¹ + 1) ^ 2) ?_ ?_ (integrable_const _) ?_
  · exact Filter.Eventually.of_forall fun t =>
      (((fcd_measurable_heatTrace b E F ε t (continuous_gueOfCoords W τ).measurable).sub
        measurable_const).pow_const 2).aestronglyMeasurable
  · filter_upwards [hev] with t ht
    refine Filter.Eventually.of_forall fun r => ?_
    have h := fcd_heatTrace_le E hb hF hε ht hW (gueOfCoords_isHermitian W τ r)
    rw [norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    exact (norm_sub_le _ _).trans (by rw [ha]; linarith)
  · refine Filter.Eventually.of_forall fun r => ?_
    have hZc : Continuous fun t => fcHeatMatrix b E F ε t (gueOfCoords W τ r) := by
      unfold fcHeatMatrix fcHeatHerm fcHeight'
      fun_prop
    have hinv := fcd_continuousAt_inv hZc.continuousAt
      (fcd_heatMatrix_inv E hb hF hε zero_le_one (gueOfCoords_isHermitian W τ r)).1
    unfold fcHeatTrace
    exact ((continuousAt_const.mul
      ((continuous_id.matrix_trace).continuousAt.comp hinv)).sub continuousAt_const).pow 2

/-- **The fresh log-heat identity**: the heat derivative of the fresh smoothed phase.
For `b ∈ (0,1/2)`, `|E| < 2`, `W ≥ 1`, Hermitian `F`, `ε > 0`: `Φ(t) = π⁻¹ E Σ_j arg(μ_j(t) + iy_t)`
is continuous on `[0,1]` and, at every `t ∈ [0,1)`, has right derivative
`(cW/2π) Im a² - (cW/2π) Im E(g_t - a)²`. -/
theorem fcHeatDerivative_holds : FcHeatDerivative := by
  intro b hb0 hb E hE W hW F hF ε hε
  set Φ := fcHeatPhase b E F ε with hΦ
  set D : ℝ → ℝ := fun t => (1 - 2 * b) * W / (2 * Real.pi) * (matchedA E ^ 2).im -
    (1 - 2 * b) * W / (2 * Real.pi) *
      (∫ A, (fcHeatTrace b E F ε t A - matchedA E) ^ 2
        ∂gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))).im with hD
  have hΨd : ∀ σ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fcdPsi b E F ε) (fcdPsi' b E F ε σ) σ :=
    fun σ hσ => fcd_Psi_hasDerivAt E hF hb hε hσ
  have hsq : ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.sqrt t ∈ Set.Icc (0 : ℝ) 1 := fun t ht =>
    ⟨Real.sqrt_nonneg t, Real.sqrt_le_one.mpr ht.2⟩
  -- derivative on `(0,1)`
  have hΦd : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt Φ (D t) t := by
    intro t ht
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht.1
    have hs1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht.2.le
    have h1 := (hΨd (Real.sqrt t) (hsq t (Set.Ioo_subset_Icc_self ht))).comp t
      (Real.hasDerivAt_sqrt ht.1.ne')
    have h2 := fcd_Psi'_eq E hb hW hF hε hst hs1
    rw [Real.sq_sqrt ht.1.le] at h2
    rw [h2] at h1
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht.1] with s hs
    exact fcd_heatPhase_eq_Psi b E ε hF (Set.mem_Ioi.mp hs).le
  -- continuity on `[0,1]`
  have hcont : ContinuousOn Φ (Set.Icc 0 1) := by
    have h : ContinuousOn (fun t => fcdPsi b E F ε (Real.sqrt t)) (Set.Icc 0 1) := fun t ht =>
      ((hΨd _ (hsq t ht)).continuousAt.comp Real.continuous_sqrt.continuousAt).continuousWithinAt
    exact h.congr fun t ht => fcd_heatPhase_eq_Psi b E ε hF ht.1
  refine ⟨hcont, fun t ht => ?_⟩
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    -- the endpoint `t = 0`: limit of the derivative
    have hDc : ContinuousAt D 0 :=
      continuousAt_const.sub (continuousAt_const.mul
        (Complex.continuous_im.continuousAt.comp (fcd_heatSq_continuousAt E hb hE hW hF hε)))
    refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioo 0 1)
      (fun t ht => (hΦd t ht).differentiableAt.differentiableWithinAt)
      ((hcont 0 ⟨le_rfl, zero_le_one⟩).mono Set.Ioo_subset_Icc_self)
      (Ioo_mem_nhdsGT one_pos) ?_
    have hev : (fun t => deriv Φ t) =ᶠ[𝓝[>] 0] D :=
      Filter.eventually_of_mem (Ioo_mem_nhdsGT one_pos) fun t ht => (hΦd t ht).deriv
    exact (hDc.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
  · exact (hΦd t ⟨hpos, ht.2⟩).hasDerivWithinAt

end Formula

end BlockBand.Layers
