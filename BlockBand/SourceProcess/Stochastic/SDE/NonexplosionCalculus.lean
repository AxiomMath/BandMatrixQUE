module
public import BlockBand.SourceProcess.Stochastic.SDE
public import BlockBand.Internal.Contracts.Transmission
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The discounted Lyapunov function in coordinates

`itoDrift_lyapFun`: its Itô drift (contract `itoDrift`) for drift `β` and covariance
`α^{ij} = ∑_a γ_a^i γ_a^j` is
`e^{-ct} (-c (1 + Φ(L⁻¹y)) + DΦ(L⁻¹y)[L⁻¹β] + ½ ∑_a D²Φ(L⁻¹y)[L⁻¹γ_a, L⁻¹γ_a])`.
`itoDrift_lyapFun_nonpos_on` / `_off`: with `c ≥ max C 0`, on `K` (where `Φ ≥ 0` and
`𝓛Φ ≤ C(1 + Φ)`) the drift is `≤ 0`, both with the true coefficients (`β = L b(x)`,
`γ_a = L σ_a(x)`) and with switched-off coefficients (`β = 0`, `γ = 0`).
-/

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal BigOperators

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The discounted Lyapunov function `e^{-ct} (1 + Φ(L⁻¹ y))`. -/
def lyapFun (L : E ≃L[ℝ] (Fin d → ℝ)) (Φ : E → ℝ) (c : ℝ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  Real.exp (-c * p.1) * (1 + Φ (L.symm p.2))

/-- Product rule for `G(t) K(y)` on `ℝ × F`. -/
theorem fderiv_mul_prod_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : ℝ → ℝ} {K : F → ℝ} {t : ℝ} {y : F} (hG : DifferentiableAt ℝ G t)
    (hK : DifferentiableAt ℝ K y) (u : ℝ) (v : F) :
    fderiv ℝ (fun q : ℝ × F => G q.1 * K q.2) (t, y) (u, v) =
      u * deriv G t * K y + G t * fderiv ℝ K y v := by
  have h1 : HasFDerivAt (fun q : ℝ × F => G q.1)
      ((fderiv ℝ G t).comp (ContinuousLinearMap.fst ℝ ℝ F)) (t, y) :=
    hG.hasFDerivAt.comp (t, y) (hasFDerivAt_fst)
  have h2 : HasFDerivAt (fun q : ℝ × F => K q.2)
      ((fderiv ℝ K y).comp (ContinuousLinearMap.snd ℝ ℝ F)) (t, y) :=
    hK.hasFDerivAt.comp (t, y) (hasFDerivAt_snd)
  rw [show (fun q : ℝ × F => G q.1 * K q.2) = (fun q => G q.1) * (fun q => K q.2) from rfl,
    (h1.mul h2).fderiv]
  have hu : fderiv ℝ G t u = u * deriv G t := by
    rw [← fderiv_apply_one_eq_deriv, ← smul_eq_mul u ((fderiv ℝ G t) 1), ← map_smul, smul_eq_mul,
      mul_one]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul, hu]
  ring

/-- Directional derivative of an evaluated `CLM`-valued map. -/
theorem fderiv_apply_const {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : X → (Y →L[ℝ] ℝ)} {x : X}
    (hf : DifferentiableAt ℝ f x) (w : Y) (v : X) :
    fderiv ℝ (fun q => f q w) x v = fderiv ℝ f x v w := by
  rw [fderiv_clm_apply hf (differentiableAt_const w)]
  simp

/-- Coordinate expansion of a linear functional on `ℝ^d`. -/
theorem sum_mul_single (ℓ : (Fin d → ℝ) →L[ℝ] ℝ) (β : Fin d → ℝ) :
    ∑ i, β i * ℓ (Pi.single i 1) = ℓ β := by
  have hβ : β = ∑ i, β i • (Pi.single i (1 : ℝ) : Fin d → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hβ]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

/-- Coordinate expansion of a quadratic form `∑_a B(γ_a, γ_a)`. -/
theorem sum_cov_mul_single {κ : Type*} [Fintype κ]
    (B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ) (γ : κ → Fin d → ℝ) (g : ℝ) :
    ∑ i, ∑ j, (∑ a, γ a i * γ a j) * (g * B (Pi.single i 1) (Pi.single j 1)) =
      g * ∑ a, B (γ a) (γ a) := by
  have hB : ∀ a, B (γ a) (γ a) = ∑ i, ∑ j, γ a i * (γ a j * B (Pi.single i 1) (Pi.single j 1)) :=
    fun a => by
      have h := sum_mul_single (B.flip (γ a)) (γ a)
      simp only [ContinuousLinearMap.flip_apply] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sum_mul_single (B (Pi.single i 1)) (γ a), Finset.mul_sum]
  simp only [hB, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => by ring

variable {Φ : E → ℝ} (L : E ≃L[ℝ] (Fin d → ℝ)) (c : ℝ)

theorem contDiff_lyapFun (hΦ : ContDiff ℝ 2 Φ) : ContDiff ℝ 2 (lyapFun L Φ c) :=
  (Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)).mul
    (contDiff_const.add (hΦ.comp ((L.symm : (Fin d → ℝ) →L[ℝ] E).contDiff.comp contDiff_snd)))

theorem hasDerivAt_expc (s : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-c * s)) (Real.exp (-c * s) * (-c)) s := by
  simpa using ((hasDerivAt_id s).const_mul (-c)).exp

/-- The space derivative of `lyapFun` in direction `(0, w)`, at every point. -/
theorem fderiv_lyapFun_space (hΦ : ContDiff ℝ 2 Φ) (q : ℝ × (Fin d → ℝ)) (w : Fin d → ℝ) :
    fderiv ℝ (lyapFun L Φ c) q (0, w) =
      Real.exp (-c * q.1) * fderiv ℝ Φ (L.symm q.2) (L.symm w) := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hH : HasFDerivAt (fun y : Fin d → ℝ => 1 + Φ (L.symm y))
      ((fderiv ℝ Φ (L.symm q.2)).comp (L.symm : (Fin d → ℝ) →L[ℝ] E)) q.2 :=
    ((hΦd _).hasFDerivAt.comp q.2 L.symm.hasFDerivAt).const_add 1
  have h := fderiv_mul_prod_apply (G := fun s => Real.exp (-c * s))
    (K := fun y : Fin d → ℝ => 1 + Φ (L.symm y)) (t := q.1) (y := q.2)
    (hasDerivAt_expc c _).differentiableAt
    hH.differentiableAt 0 w
  rw [hH.fderiv] at h
  simp only [zero_mul, zero_add, ContinuousLinearMap.comp_apply] at h
  exact h

/-- The time derivative of `lyapFun`. -/
theorem fderiv_lyapFun_time (hΦ : ContDiff ℝ 2 Φ) (q : ℝ × (Fin d → ℝ)) :
    fderiv ℝ (lyapFun L Φ c) q (1, 0) = -c * Real.exp (-c * q.1) * (1 + Φ (L.symm q.2)) := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hK : DifferentiableAt ℝ (fun y : Fin d → ℝ => 1 + Φ (L.symm y)) q.2 :=
    ((hΦd _).comp q.2 L.symm.differentiableAt).const_add 1
  have hG := hasDerivAt_expc c q.1
  have h := fderiv_mul_prod_apply (G := fun s => Real.exp (-c * s))
    (K := fun y : Fin d → ℝ => 1 + Φ (L.symm y)) (t := q.1) (y := q.2)
    hG.differentiableAt hK 1 0
  rw [hG.deriv, map_zero, mul_zero, add_zero] at h
  change fderiv ℝ (fun q : ℝ × (Fin d → ℝ) => Real.exp (-c * q.1) * (1 + Φ (L.symm q.2)))
    (q.1, q.2) (1, 0) = _ at h
  unfold lyapFun
  rw [h]
  ring

/-- The second space derivative of `lyapFun`. -/
theorem fderiv_fderiv_lyapFun_space (hΦ : ContDiff ℝ 2 Φ) (p : ℝ × (Fin d → ℝ))
    (v w : Fin d → ℝ) :
    fderiv ℝ (fderiv ℝ (lyapFun L Φ c)) p (0, v) (0, w) =
      Real.exp (-c * p.1) * fderiv ℝ (fderiv ℝ Φ) (L.symm p.2) (L.symm v) (L.symm w) := by
  have hφ1 : Differentiable ℝ (fderiv ℝ (lyapFun L Φ c)) :=
    ((contDiff_lyapFun L c hΦ).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hΦ1 : Differentiable ℝ (fderiv ℝ Φ) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [← fderiv_apply_const (hφ1 p) (0, w) (0, v)]
  have hfun : (fun q => fderiv ℝ (lyapFun L Φ c) q (0, w)) = fun q : ℝ × (Fin d → ℝ) =>
      Real.exp (-c * q.1) * fderiv ℝ Φ (L.symm q.2) (L.symm w) :=
    funext fun q => fderiv_lyapFun_space L c hΦ q w
  rw [hfun]
  have hK : HasFDerivAt (fun y : Fin d → ℝ => fderiv ℝ Φ (L.symm y) (L.symm w))
      ((fderiv ℝ (fun z => fderiv ℝ Φ z (L.symm w)) (L.symm p.2)).comp
        (L.symm : (Fin d → ℝ) →L[ℝ] E)) p.2 :=
    (((hΦ1 _).clm_apply (differentiableAt_const _)).hasFDerivAt).comp p.2 L.symm.hasFDerivAt
  have h := fderiv_mul_prod_apply (G := fun s => Real.exp (-c * s))
    (K := fun y : Fin d → ℝ => fderiv ℝ Φ (L.symm y) (L.symm w)) (t := p.1) (y := p.2)
    (hasDerivAt_expc c _).differentiableAt
    hK.differentiableAt 0 v
  rw [hK.fderiv, zero_mul, zero_mul, zero_add, ContinuousLinearMap.comp_apply,
    fderiv_apply_const (hΦ1 _)] at h
  exact h

/-- **Itô drift of the discounted Lyapunov function.** -/
theorem itoDrift_lyapFun {κ : Type*} [Fintype κ] (hΦ : ContDiff ℝ 2 Φ) (y : Fin d → ℝ)
    (t : ℝ≥0) (β : Fin d → ℝ) (γ : κ → Fin d → ℝ) :
    itoDrift (lyapFun L Φ c) y t β (Matrix.of fun i j => ∑ a, γ a i * γ a j) =
      Real.exp (-c * t) * (-c * (1 + Φ (L.symm y)) + fderiv ℝ Φ (L.symm y) (L.symm β) +
        (1 / 2 : ℝ) * ∑ a, fderiv ℝ (fderiv ℝ Φ) (L.symm y) (L.symm (γ a)) (L.symm (γ a))) := by
  unfold itoDrift partialTime partialSpace partialSpace2
  simp only [Matrix.of_apply, fderiv_lyapFun_time L c hΦ, fderiv_lyapFun_space L c hΦ,
    fderiv_fderiv_lyapFun_space L c hΦ]
  have h1 : ∑ i, β i * (Real.exp (-c * t) * fderiv ℝ Φ (L.symm y) (L.symm (Pi.single i 1))) =
      Real.exp (-c * t) * fderiv ℝ Φ (L.symm y) (L.symm β) := by
    have h := sum_mul_single ((fderiv ℝ Φ (L.symm y)).comp (L.symm : (Fin d → ℝ) →L[ℝ] E)) β
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at h
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h2 := sum_cov_mul_single (((fderiv ℝ (fderiv ℝ Φ) (L.symm y)).bilinearComp
    (L.symm : (Fin d → ℝ) →L[ℝ] E) (L.symm : (Fin d → ℝ) →L[ℝ] E))) γ (Real.exp (-c * t))
  simp only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearEquiv.coe_coe] at h2
  rw [h1, h2]
  ring

/-- Drift bound with the true coefficients, on `K`. -/
theorem itoDrift_lyapFun_nonpos_on {κ : Type*} [Fintype κ] (hΦ : ContDiff ℝ 2 Φ)
    {b : E → E} {σ : κ → E → E} {C : ℝ} (hc : C ≤ c) {x : E} (hΦx : 0 ≤ Φ x)
    (hgen : sdeGenerator b σ Φ x ≤ C * (1 + Φ x)) (t : ℝ≥0) :
    itoDrift (lyapFun L Φ c) (L x) t (L (b x))
      (Matrix.of fun i j => ∑ a, L (σ a x) i * L (σ a x) j) ≤ 0 := by
  rw [itoDrift_lyapFun L c hΦ (L x) t (L (b x)) fun a => L (σ a x)]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
  unfold sdeGenerator at hgen
  nlinarith

/-- Drift bound with switched-off coefficients, on `{Φ ≥ 0}`. -/
theorem itoDrift_lyapFun_nonpos_off {κ : Type*} [Fintype κ] (hΦ : ContDiff ℝ 2 Φ) (hc : 0 ≤ c)
    {y : Fin d → ℝ} (hΦy : 0 ≤ Φ (L.symm y)) (t : ℝ≥0) :
    itoDrift (lyapFun L Φ c) y t 0
      (Matrix.of fun i j => ∑ _a : κ, (0 : Fin d → ℝ) i * (0 : Fin d → ℝ) j) ≤ 0 := by
  rw [itoDrift_lyapFun L c hΦ y t 0 fun _ : κ => 0]
  simp only [map_zero, Finset.sum_const_zero, mul_zero, add_zero]
  refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
  nlinarith

end BlockBand.SourceProcess.Stochastic.NativeSDE
