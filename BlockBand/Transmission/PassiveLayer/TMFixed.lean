module

public import BlockBand.Transmission.PassiveLayer.TMKernel

/-!
# The trace–matrix covariance bound for a bounded smooth resolvent family

Law `μ = gaussianProduct (coordVar W b)` (the coordinates of `freshLaw W b`, `BilCoord`).
`tm_cov_of`: for **any** deterministic `K` and any `C¹` family `x ↦ 𝒢(x)` that is bounded
(`‖𝒢(x)‖ ≤ R`) with `d𝒢(v) = -𝒢 (layerDir v) 𝒢` — e.g. the regularized resolvent `gReg`
(`TMReg`) — the passive words `f = W⁻¹ Tr w_f(𝒢)`, `U = w_U(𝒢)` satisfy
`‖E(fU) - E f E U‖ ≤ (3 ℓ_f ℓ_U K_d^n / W²) · 2 E Λ(K,𝒢)^n`, `n = ℓ_f + ℓ_U + 2`,
`Λ(K,𝒢) = 1 + ‖𝒢‖ + ‖Kι₁𝒢‖`. **The bound does not depend on `R`** nor on `‖K‖`; those only
make the OU identity (`ou_covariance_matrix`, bounded `C¹` class) applicable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open MeasureTheory ProbabilityTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open scoped ENNReal NNReal Matrix.Norms.L2Operator

variable {W : ℕ}

theorem continuous_lam (K : Matrix (Fin W) (Fin W) ℂ) : Continuous (lam K) := by
  unfold lam; fun_prop

theorem lam_le_of_norm_le (K : Matrix (Fin W) (Fin W) ℂ) {G : Matrix (LS W) (LS W) ℂ} {R : ℝ}
    (h : ‖G‖ ≤ R) : lam K G ≤ 1 + R + ‖K * iota1 W‖ * R := by
  unfold lam
  have := (Matrix.l2_opNorm_mul (K * iota1 W) G).trans
    (mul_le_mul_of_nonneg_left h (norm_nonneg _))
  linarith

/-- **Covariance bound for a bounded `C¹` resolvent family** (fixed regularization). -/
theorem tm_cov_of {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W)
    (K : Matrix (Fin W) (Fin W) ℂ) {G : (CoordW W → ℝ) → Matrix (LS W) (LS W) ℂ}
    (hGc : ContDiff ℝ 1 G) {R : ℝ} (hGle : ∀ x, ‖G x‖ ≤ R)
    (hderG : ∀ x, ∃ T : (CoordW W → ℝ) →L[ℝ] Matrix (LS W) (LS W) ℂ,
      HasFDerivAt G T x ∧ ∀ v, T v = -(G x * layerDirC W b v * G x))
    {Kd : ℝ} (hKd : 0 ≤ Kd) {ℓf ℓU : ℕ}
    (wf : Fin ℓf → Fin 6 × Bool) (Df : Fin (ℓf + 1) → Matrix (Fin W) (Fin W) ℂ)
    (wU : Fin ℓU → Fin 6 × Bool) (DU : Fin (ℓU + 1) → Matrix (Fin W) (Fin W) ℂ)
    (hDf : ∀ j, ‖Df j‖ ≤ Kd) (hDU : ∀ j, ‖DU j‖ ≤ Kd) :
    ‖(∫ x, tmTr W (tmWord K wf Df (G x)) • tmWord K wU DU (G x) ∂gaussianProduct (coordVar W b)) -
        (∫ x, tmTr W (tmWord K wf Df (G x)) ∂gaussianProduct (coordVar W b)) •
          (∫ x, tmWord K wU DU (G x) ∂gaussianProduct (coordVar W b))‖ ≤
      3 * ℓf * ℓU * Kd ^ (ℓf + ℓU + 2) / (W : ℝ) ^ 2 *
        (2 * ∫ x, lam K (G x) ^ (ℓf + ℓU + 2) ∂gaussianProduct (coordVar W b)) := by
  set v := coordVar W b with hv
  set μ := gaussianProduct v with hμ
  set Λ := layerDirC W b with hΛdef
  set n := ℓf + ℓU + 2 with hn
  set f : (CoordW W → ℝ) → ℂ := fun x => tmTr W (tmWord K wf Df (G x)) with hfdef
  set U : (CoordW W → ℝ) → Matrix (Fin W) (Fin W) ℂ := fun x => tmWord K wU DU (G x) with hUdef
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hGcont : Continuous G := hGc.continuous
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hGle 0)
  set Lb := 1 + R + ‖K * iota1 W‖ * R with hLb
  have hlam : ∀ x, lam K (G x) ≤ Lb := fun x => lam_le_of_norm_le K (hGle x)
  have hlam0 : ∀ x, 0 ≤ lam K (G x) := fun x => zero_le_one.trans (one_le_lam K (G x))
  have hLb0 : 0 ≤ Lb := (hlam0 0).trans (hlam 0)
  have hΛh : ∀ v', (Λ v')ᴴ = Λ v' := layerDirC_herm b
  have hfd : ContDiff ℝ 1 f := (tmTr W).contDiff.comp (tm_contDiff_word hGc K wf Df)
  have hUd : ContDiff ℝ 1 U := tm_contDiff_word hGc K wU DU
  have hpowle : ∀ (m : ℕ) x, lam K (G x) ^ m ≤ Lb ^ m := fun m x =>
    pow_le_pow_left₀ (hlam0 x) (hlam x) m
  have hfC : ∀ x, ‖f x‖ ≤ Kd ^ (ℓf + 1) * Lb ^ ℓf := fun x =>
    (norm_tmTr_le _).trans ((norm_tmWord_le K hKd wf Df (G x) hDf).trans (mul_le_mul_of_nonneg_left (hpowle ℓf x) (by positivity)))
  have hUC : ∀ x, ‖U x‖ ≤ Kd ^ (ℓU + 1) * Lb ^ ℓU := fun x =>
    (norm_tmWord_le K hKd wU DU (G x) hDU).trans (mul_le_mul_of_nonneg_left (hpowle ℓU x) (by positivity))
  have hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ ‖tmTr W‖ * (ℓf * (Kd ^ (ℓf + 1) * Lb ^ (ℓf + 1)) * ‖Λ‖) :=
    fun x => by
      obtain ⟨T, hT, a, c, hTv, hac⟩ := tm_word_hasFDerivAt hΛh (hderG x) K hKd wf Df hDf
      have hfx : HasFDerivAt f ((tmTr W).comp T) x := (tmTr W).hasFDerivAt.comp x hT
      rw [hfx.fderiv]
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      gcongr
      exact tm_clm_norm_le hTv (by positivity) fun m =>
        (hac m).trans (mul_le_mul_of_nonneg_left (hpowle _ x) (by positivity))
  have hU'C : ∀ x, ‖fderiv ℝ U x‖ ≤ ℓU * (Kd ^ (ℓU + 1) * Lb ^ (ℓU + 1)) * ‖Λ‖ := fun x => by
    obtain ⟨T, hT, a, c, hTv, hac⟩ := tm_word_hasFDerivAt hΛh (hderG x) K hKd wU DU hDU
    rw [hT.fderiv]
    exact tm_clm_norm_le hTv (by positivity) fun m =>
      (hac m).trans (mul_le_mul_of_nonneg_left (hpowle _ x) (by positivity))
  -- the pointwise kernel bound
  set c₀ : ℝ := 3 * ℓf * ℓU * Kd ^ n / (W : ℝ) ^ 2 with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  have hker : ∀ x y : CoordW W → ℝ,
      ‖∑ i, (((v i : ℝ) : ℂ) * fderiv ℝ f x (Pi.single i 1)) • fderiv ℝ U y (Pi.single i 1)‖ ≤
        c₀ * (lam K (G x) ^ n + lam K (G y) ^ n) := by
    intro x y
    obtain ⟨Tf, hTf, a, c, hTfv, hacf⟩ := tm_word_hasFDerivAt hΛh (hderG x) K hKd wf Df hDf
    obtain ⟨TU, hTU, a', c', hTUv, hacU⟩ := tm_word_hasFDerivAt hΛh (hderG y) K hKd wU DU hDU
    have hfx : HasFDerivAt f ((tmTr W).comp Tf) x := (tmTr W).hasFDerivAt.comp x hTf
    have e1 : ∀ i, fderiv ℝ f x (Pi.single i 1) =
        (W : ℂ)⁻¹ * (∑ j, a j * Λ (Pi.single i 1) * c j).trace := fun i => by
      rw [hfx.fderiv, ContinuousLinearMap.comp_apply, hTfv, tmTr_apply]
    have e2 : ∀ i, fderiv ℝ U y (Pi.single i 1) = ∑ k, a' k * Λ (Pi.single i 1) * c' k :=
      fun i => by rw [hTU.fderiv, hTUv]
    simp_rw [e1, e2]
    rw [tm_kernel_eq]
    have hV : ∀ j, (∑ i, (((v i : ℝ) : ℂ) * (c j * a j * Λ (Pi.single i 1)).trace) •
        Λ (Pi.single i 1)) = tmV b (c j * a j) := fun j => rfl
    simp only [hV]
    have hk := tm_kernel_le hb0 hb hW a c a' c' (Bf := Kd ^ (ℓf + 1) * lam K (G x) ^ (ℓf + 1))
      (BU := Kd ^ (ℓU + 1) * lam K (G y) ^ (ℓU + 1)) (by have := hlam0 x; positivity) hacf hacU
    refine hk.trans ?_
    have hamgm := tm_pow_mul_le (hlam0 x) (hlam0 y) (ℓf + 1) (ℓU + 1)
    have e3 : ℓf + 1 + (ℓU + 1) = n := by omega
    rw [e3] at hamgm
    calc 3 * ℓf * ℓU * (Kd ^ (ℓf + 1) * lam K (G x) ^ (ℓf + 1)) *
          (Kd ^ (ℓU + 1) * lam K (G y) ^ (ℓU + 1)) / (W : ℝ) ^ 2
        = c₀ * (lam K (G x) ^ (ℓf + 1) * lam K (G y) ^ (ℓU + 1)) := by
          rw [hc₀, hn, show ℓf + ℓU + 2 = (ℓf + 1) + (ℓU + 1) by omega, pow_add]
          ring
      _ ≤ c₀ * (lam K (G x) ^ n + lam K (G y) ^ n) := mul_le_mul_of_nonneg_left hamgm hc₀0
  -- integrate in `p` and in `t`
  set I : ℝ := ∫ x, lam K (G x) ^ n ∂μ with hI
  have hpc : Continuous (fun x => lam K (G x) ^ n) := ((continuous_lam K).comp hGcont).pow n
  have hkt : ∀ t : ℝ, 0 < t →
      ‖∫ p, ∑ i, (((v i : ℝ) : ℂ) * fderiv ℝ f p.1 (Pi.single i 1)) •
          fderiv ℝ U (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
            (Pi.single i 1) ∂μ.prod μ‖ ≤ c₀ * (2 * I) := by
    intro t ht
    set y : (CoordW W → ℝ) × (CoordW W → ℝ) → (CoordW W → ℝ) :=
      fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2 with hy
    have hyc : Continuous y := by fun_prop
    have hA : Integrable (fun p : (CoordW W → ℝ) × (CoordW W → ℝ) => lam K (G p.1) ^ n)
        (μ.prod μ) :=
      ou_integrable_bdd v (hpc.comp continuous_fst) (C := Lb ^ n) fun p => by
        rw [Real.norm_of_nonneg (by have := hlam0 p.1; positivity)]; exact hpowle n p.1
    have hB : Integrable (fun p : (CoordW W → ℝ) × (CoordW W → ℝ) => lam K (G (y p)) ^ n)
        (μ.prod μ) :=
      ou_integrable_bdd v (hpc.comp hyc) (C := Lb ^ n) fun p => by
        rw [Real.norm_of_nonneg (by have := hlam0 (y p); positivity)]; exact hpowle n (y p)
    have hbd := norm_integral_le_of_norm_le ((hA.add hB).const_mul c₀)
      (Eventually.of_forall fun p => hker p.1 (y p))
    refine hbd.trans (le_of_eq ?_)
    rw [integral_const_mul]
    simp only [Pi.add_apply]
    rw [integral_add hA hB, integral_fun_fst (fun x => lam K (G x) ^ n),
      probReal_univ, one_smul, tm_integral_interp v hpc ht.le]
    ring
  rw [ou_covariance_matrix v hfd hfC hf'C hUd hUC hU'C]
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-t) * (c₀ * (2 * I))) (Set.Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).mul_const _
  refine (norm_integral_le_of_norm_le hexp ?_).trans (le_of_eq ?_)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (hkt t ht) (Real.exp_pos _).le
  · rw [integral_mul_const, integral_exp_neg_Ioi_zero, one_mul]

end BlockBand.Transmission.PassiveLayer
