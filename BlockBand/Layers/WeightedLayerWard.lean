module

public import BlockBand.Layers.WeightedLayerNoise

/-!
# The weighted layer: the weighted covariance and the weighted Ward identity

The weighted Ward identity of `WeightedLayerContract` (`wl_ward_core`), from
`ConditionalBlockGUECount` alone (through `gaussianAbsorption_holds` and `layerComparison_holds`);
the clock-mean identity is derived from it in `wl_clockMean`.

Setting: as in `BlockBand.Layers.WeightedLayerNoise` (one separate-port layer of
`layerLaw W b .separate`, deterministic Hermitian two-port `X`, `E ∈ bulkInterval κ`,
`z = z_∂(E)`, `K = z - X`, `L = K 𝒢₁₂`, `𝒦 = diag(K, 0)`); in addition the scalar domain
`d(X) ≤ d_*` (`matchedDistance`).

Proof.
1. **Weighted covariance** (§1). For one-letter words, `‖Cov(W⁻¹Tr P𝒢, Q𝒢) 𝒦*‖ ≤ C W⁻²`
   uniformly in `X` (`‖P‖, ‖Q‖ ≤ 1`): "the contraction in the trace–matrix lemma still gives
   `W⁻²`; its rightmost factor remains the weighted inverse `𝒢₁₁K*`". In the coordinates, for
   `G_κ = (𝒢⁻¹ + iκ)⁻¹` the OU identity (`ou_covariance_matrix`) with `U_κ = Q G_κ 𝒦*` has kernel
   `W⁻¹ Q G_κ(y) 𝒱(G_κ(x) P G_κ(x)) G_κ(y) 𝒦*`, of norm `≤ 10 W⁻² ‖G_κ(x)‖² ‖G_κ(y)‖
   ‖G_κ(y)𝒦*‖` (`tcv_kernel_le`); `‖G_κ‖, ‖G_κ 𝒦*‖ ≤ 2F` (`F` the weight majorant of
   `WeightedLayerNoise`) and `E F⁴ ≤ C⁴` give a bound uniform in `κ ∈ (0,1]`; the unweighted
   covariances converge as `κ → 0` (dominated convergence) and right multiplication by `𝒦*`
   is continuous.
2. **Weighted mean** (§2, deterministic algebra). The exact mean equation
   (`meanEquation_of_moments`, `meq_blocks`) gives `T̄ (E𝒢)₁₁ = 1 + R₁₁` with
   `T̄ = -E - X - diag(c ḡ_a + b ḡ_{p,a})` the top matrix at the layer means and
   `R₁₁ = meqResidTop`; hence `K (E𝒢)₁₁ K* = K M̄ K* + K M̄ (R 𝒦*)₁₁`, `M̄ = T̄⁻¹`.
3. **Ward identity** (§3): `𝒢₁₂𝒢₁₂* = (i/2η)(𝒢₁₁ - 𝒢₁₁*)`, `η = Im z`, so
   `E LL* = (i/2η)(K(E𝒢)₁₁K* - h.c.)`, and `(i/2η)(K M̄ K* - h.c.) = (KM̄) D (KM̄)*` with
   `D = diag(-Im s/η)`, `KM̄ = 1 + diag(z + E + s) M̄`.
4. **Scalar domain** (§4): by `layerComparison_holds`, `|ḡ - a| ≤ C d + C W⁻²`; with
   `z + E + (1-b) a = 0` and `η = -(1-b) Im a` this gives `‖KM̄ - 1‖, ‖D - 1‖ ≤ C(d + W⁻²)`,
   `‖M̄‖ ≤ 2/η`; with §1, `‖E LL* - 1‖ ≤ C(d + W⁻²)` (the weighted Ward identity).
5. **Clock mean** (in `wl_clockMean`): `E W⁻¹ Tr L*YL = W⁻¹ Re Tr(Y E LL*) ≤ (1 + ‖E LL* - 1‖) u`
   (`wl_norm_trace_weight_le`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix WithLp Filter Topology
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct ConditionalBlockGUECount)
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. The weighted one-letter covariance
-/

section WeightedCov

variable (W : ℕ) (b : ℝ) (σ : LayerShape) (E : ℝ) (z : ℂ)
  (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)

variable {W b X} in
/-- **Weighted covariance at fixed `κ > 0`** (coordinates): with `G = G_κ`, `‖P‖, ‖Q‖ ≤ 1`
and any deterministic `𝒲`,
`‖Cov(W⁻¹Tr PG, Q G 𝒲)‖ ≤ 5 W⁻² (E‖G‖⁴ + E(‖G‖ ‖G 𝒲‖)²)`. -/
theorem wl_cov_reg (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) (hX : X.IsHermitian)
    (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (P Q Wt : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) :
    ‖(∫ x, tcvTr W σ (P * tcvG W b σ E z X κ x) • (Q * tcvG W b σ E z X κ x * Wt)
          ∂gaussianProduct (tflVar W b σ)) -
        (∫ x, tcvTr W σ (P * tcvG W b σ E z X κ x) ∂gaussianProduct (tflVar W b σ)) •
          (∫ x, Q * tcvG W b σ E z X κ x * Wt ∂gaussianProduct (tflVar W b σ))‖ ≤
      5 / (W : ℝ) ^ 2 * ((∫ x, ‖tcvG W b σ E z X κ x‖ ^ 4 ∂gaussianProduct (tflVar W b σ)) +
        ∫ x, (‖tcvG W b σ E z X κ x‖ * ‖tcvG W b σ E z X κ x * Wt‖) ^ 2
          ∂gaussianProduct (tflVar W b σ)) := by
  set v := tflVar W b σ with hv
  set μ := gaussianProduct v with hμ
  set G := tcvG W b σ E z X κ with hGdef
  set Λ := tcvLam W b σ with hΛdef
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hGc : ContDiff ℝ 1 G := tcv_G_contDiff W b σ E z hX hz hκ
  have hGcont : Continuous G := hGc.continuous
  have hGle : ∀ x, ‖G x‖ ≤ κ⁻¹ := tcv_G_le W b σ E z hX hz hκ
  have hκi : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  have hderG := tcv_G_hasFDerivAt W b σ E z hX hz hκ
  set LP := ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) P with hLP
  set LU := ContinuousLinearMap.mulLeftRight ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) Q Wt with hLU
  set f : (TflCoord W σ → ℝ) → ℂ := fun x => tcvTr W σ (P * G x) with hfdef
  set U : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ := fun x => Q * G x * Wt with hUdef
  have hfd : ContDiff ℝ 1 f := (tcvTr W σ).contDiff.comp (LP.contDiff.comp hGc)
  have hUd : ContDiff ℝ 1 U := LU.contDiff.comp hGc
  have hfder : ∀ x, ∃ T : (TflCoord W σ → ℝ) →L[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ, fderiv ℝ f x = (tcvTr W σ).comp (LP.comp T) ∧
      ∀ w, T w = -(G x * Λ w * G x) := by
    intro x
    obtain ⟨T, hT, hTv⟩ := hderG x
    exact ⟨T, ((tcvTr W σ).hasFDerivAt.comp x (LP.hasFDerivAt.comp x hT)).fderiv, hTv⟩
  have hUder : ∀ x, ∃ T : (TflCoord W σ → ℝ) →L[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ, fderiv ℝ U x = LU.comp T ∧
      ∀ w, T w = -(G x * Λ w * G x) := by
    intro x
    obtain ⟨T, hT, hTv⟩ := hderG x
    exact ⟨T, (LU.hasFDerivAt.comp x hT).fderiv, hTv⟩
  have hTn : ∀ x (T : (TflCoord W σ → ℝ) →L[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ), (∀ w, T w = -(G x * Λ w * G x)) →
      ‖T‖ ≤ κ⁻¹ ^ 2 * ‖Λ‖ := by
    intro x T hTv
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    rw [hTv, norm_neg]
    calc ‖G x * Λ w * G x‖ ≤ ‖G x‖ * ‖Λ w‖ * ‖G x‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ κ⁻¹ * (‖Λ‖ * ‖w‖) * κ⁻¹ := by
          gcongr
          · exact hGle x
          · exact Λ.le_opNorm w
          · exact hGle x
      _ = κ⁻¹ ^ 2 * ‖Λ‖ * ‖w‖ := by ring
  have hfC : ∀ x, ‖f x‖ ≤ 4 * κ⁻¹ := fun x => by
    refine (tcv_tr_le σ hW _).trans ?_
    gcongr
    calc ‖P * G x‖ ≤ ‖P‖ * ‖G x‖ := norm_mul_le _ _
      _ ≤ 1 * κ⁻¹ := mul_le_mul hP (hGle x) (norm_nonneg _) zero_le_one
      _ = κ⁻¹ := one_mul _
  have hUC : ∀ x, ‖U x‖ ≤ κ⁻¹ * ‖Wt‖ := fun x => by
    calc ‖Q * G x * Wt‖ ≤ ‖Q‖ * ‖G x‖ * ‖Wt‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * κ⁻¹ * ‖Wt‖ := by gcongr; exact hGle x
      _ = κ⁻¹ * ‖Wt‖ := by ring
  have hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ ‖tcvTr W σ‖ * (‖LP‖ * (κ⁻¹ ^ 2 * ‖Λ‖)) := fun x => by
    obtain ⟨T, hT, hTv⟩ := hfder x
    rw [hT]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    gcongr
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (hTn x T hTv) (norm_nonneg _))
  have hU'C : ∀ x, ‖fderiv ℝ U x‖ ≤ ‖LU‖ * (κ⁻¹ ^ 2 * ‖Λ‖) := fun x => by
    obtain ⟨T, hT, hTv⟩ := hUder x
    rw [hT]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (hTn x T hTv) (norm_nonneg _))
  -- the pointwise kernel bound
  set c₀ : ℝ := 5 / (W : ℝ) ^ 2 with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  set h₁ : (TflCoord W σ → ℝ) → ℝ := fun x => ‖G x‖ ^ 4 with hh₁
  set h₂ : (TflCoord W σ → ℝ) → ℝ := fun x => (‖G x‖ * ‖G x * Wt‖) ^ 2 with hh₂
  have hker : ∀ x y : TflCoord W σ → ℝ,
      ‖∑ i, (((v i : ℝ) : ℂ) * fderiv ℝ f x (Pi.single i 1)) • fderiv ℝ U y (Pi.single i 1)‖ ≤
        c₀ * (h₁ x + h₂ y) := by
    intro x y
    obtain ⟨Tf, hTf, hTfv⟩ := hfder x
    obtain ⟨TU, hTU, hTUv⟩ := hUder y
    have e1 : ∀ i, fderiv ℝ f x (Pi.single i 1) = (W : ℂ)⁻¹ *
        (∑ j : Fin 1, ![-(P * G x)] j * Λ (Pi.single i 1) * ![G x] j).trace := fun i => by
      rw [hTf, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hTfv, tcvTr_apply]
      simp only [Fin.sum_univ_one, Matrix.cons_val_zero, hLP, ContinuousLinearMap.mul_apply']
      congr 2
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    have e2 : ∀ i, fderiv ℝ U y (Pi.single i 1) =
        ∑ k : Fin 1, ![-(Q * G y)] k * Λ (Pi.single i 1) * ![G y * Wt] k := fun i => by
      rw [hTU, ContinuousLinearMap.comp_apply, hTUv]
      simp only [Fin.sum_univ_one, Matrix.cons_val_zero, hLU,
        ContinuousLinearMap.mulLeftRight_apply]
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    simp_rw [e1, e2]
    rw [tcv_kernel_eq]
    have hk := tcv_kernel_le σ hW hb0 hb1 ![-(P * G x)] ![G x] ![-(Q * G y)] ![G y * Wt]
      (Bf := ‖G x‖ ^ 2) (BU := ‖G y‖ * ‖G y * Wt‖) (by positivity)
      (fun j => by
        fin_cases j
        simp only [Matrix.cons_val_zero, norm_neg, Fin.zero_eta]
        calc ‖P * G x‖ * ‖G x‖ ≤ (‖P‖ * ‖G x‖) * ‖G x‖ :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
          _ ≤ (1 * ‖G x‖) * ‖G x‖ := by gcongr
          _ = ‖G x‖ ^ 2 := by ring)
      (fun k => by
        fin_cases k
        simp only [Matrix.cons_val_zero, norm_neg, Fin.zero_eta]
        calc ‖Q * G y‖ * ‖G y * Wt‖ ≤ (‖Q‖ * ‖G y‖) * ‖G y * Wt‖ :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
          _ ≤ (1 * ‖G y‖) * ‖G y * Wt‖ := by gcongr
          _ = ‖G y‖ * ‖G y * Wt‖ := by ring)
    refine le_trans ?_ (hk.trans ?_)
    · exact le_of_eq rfl
    · have hab := mul_nonneg (norm_nonneg (G y)) (norm_nonneg (G y * Wt))
      have hamgm : ‖G x‖ ^ 2 * (‖G y‖ * ‖G y * Wt‖) ≤
          (‖G x‖ ^ 4 + (‖G y‖ * ‖G y * Wt‖) ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖G x‖ ^ 2 - ‖G y‖ * ‖G y * Wt‖)]
      calc 10 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * ‖G x‖ ^ 2 * (‖G y‖ * ‖G y * Wt‖) / (W : ℝ) ^ 2
          = 10 / (W : ℝ) ^ 2 * (‖G x‖ ^ 2 * (‖G y‖ * ‖G y * Wt‖)) := by push_cast; ring
        _ ≤ 10 / (W : ℝ) ^ 2 * ((‖G x‖ ^ 4 + (‖G y‖ * ‖G y * Wt‖) ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left hamgm (by positivity)
        _ = c₀ * (h₁ x + h₂ y) := by rw [hc₀]; ring
  -- integrate in `p` and in `t`
  have hh₁c : Continuous h₁ := (continuous_norm.comp hGcont).pow 4
  have hh₂c : Continuous h₂ :=
    ((continuous_norm.comp hGcont).mul (continuous_norm.comp (hGcont.matrix_mul
      continuous_const))).pow 2
  have hh₁b : ∀ x, ‖h₁ x‖ ≤ κ⁻¹ ^ 4 := fun x => by
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hGle x) 4
  have hh₂b : ∀ x, ‖h₂ x‖ ≤ (κ⁻¹ * (κ⁻¹ * ‖Wt‖)) ^ 2 := fun x => by
    rw [Real.norm_of_nonneg (by positivity)]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    refine mul_le_mul (hGle x) ((norm_mul_le _ _).trans ?_) (norm_nonneg _) hκi
    exact mul_le_mul_of_nonneg_right (hGle x) (norm_nonneg _)
  set I₁ : ℝ := ∫ x, h₁ x ∂μ with hI₁
  set I₂ : ℝ := ∫ x, h₂ x ∂μ with hI₂
  have hkt : ∀ t : ℝ, 0 < t →
      ‖∫ p, ∑ i, (((v i : ℝ) : ℂ) * fderiv ℝ f p.1 (Pi.single i 1)) •
          fderiv ℝ U (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
            (Pi.single i 1) ∂μ.prod μ‖ ≤ c₀ * (I₁ + I₂) := by
    intro t ht
    set y : (TflCoord W σ → ℝ) × (TflCoord W σ → ℝ) → (TflCoord W σ → ℝ) :=
      fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2 with hy
    have hyc : Continuous y := by fun_prop
    have hA : Integrable (fun p : (TflCoord W σ → ℝ) × (TflCoord W σ → ℝ) => h₁ p.1) (μ.prod μ) :=
      ou_integrable_bdd v (hh₁c.comp continuous_fst) fun p => hh₁b p.1
    have hB : Integrable (fun p : (TflCoord W σ → ℝ) × (TflCoord W σ → ℝ) => h₂ (y p))
        (μ.prod μ) :=
      ou_integrable_bdd v (hh₂c.comp hyc) fun p => hh₂b (y p)
    have hbd := norm_integral_le_of_norm_le ((hA.add hB).const_mul c₀)
      (Eventually.of_forall fun p => hker p.1 (y p))
    refine hbd.trans (le_of_eq ?_)
    rw [integral_const_mul]
    simp only [Pi.add_apply]
    rw [integral_add hA hB, integral_fun_fst (fun x => h₁ x), probReal_univ, one_smul,
      tcv_integral_interp v hh₂c ht.le]
  rw [ou_covariance_matrix v hfd hfC hf'C hUd hUC hU'C]
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-t) * (c₀ * (I₁ + I₂))) (Set.Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).mul_const _
  refine (norm_integral_le_of_norm_le hexp ?_).trans (le_of_eq ?_)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (hkt t ht) (Real.exp_pos _).le
  · rw [integral_mul_const, integral_exp_neg_Ioi_zero, one_mul]

end WeightedCov

section WeightedCovLimit

variable {W : ℕ} {b : ℝ} {σ : LayerShape}

/-- `‖G_κ 𝒦*‖ ≤ 2 F` for `0 < κ ≤ 1`, `|E| ≤ 2`, `|z| ≤ 3`, wherever `𝒢⁻¹` is invertible. -/
theorem wl_reg_weighted_right_le {E : ℝ} {z : ℂ} {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ}
    (hX : X.IsHermitian) (hz : 0 ≤ z.im) (hE : |E| ≤ 2) (hzM : ‖z‖ ≤ 3) {κ : ℝ} (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (x : TflCoord W σ → ℝ)
    (hx : IsUnit (layerMatrix σ E z X (tflEmbed W b σ x)).det) :
    ‖tcvG W b σ E z X κ x *
        wlKh (m := PortSite W σ) (z • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X)ᴴ‖ ≤
      2 * wlF E z X (tflEmbed W b σ x) := by
  have hG2 := tflPsi_inv_le_two W b σ E z hX hz hκ x hx
  change ‖tcvG W b σ E z X κ x‖ ≤ _ at hG2
  set g := ‖layerResolvent σ E z X (tflEmbed W b σ x)‖ with hg
  set lam := ‖wlLam (tflEmbed W b σ x)‖ with hlam
  have hg0 : 0 ≤ g := norm_nonneg _
  have hl0 : 0 ≤ lam := norm_nonneg _
  have hFe : wlF E z X (tflEmbed W b σ x) = 1 + 6 * ((1 + lam) * g) := rfl
  have hU : IsUnit (tflReg κ (layerMatrix σ E z X (tflEmbed W b σ x))) := by
    rw [← tflPsi_eq]; exact tflPsi_isUnit W b σ E z hX hz hκ x
  have hGN : tcvG W b σ E z X κ x * tflReg κ (layerMatrix σ E z X (tflEmbed W b σ x)) = 1 := by
    rw [tcvG, tflPsi_eq]; exact Ring.inverse_mul_cancel _ hU
  rw [wl_mul_Kh_eq hGN]
  refine wl_norm_weighted_le'.trans ?_
  have hb := wl_norm_Kh_sub_right_le E z hX (tflEmbed W b σ x) hκ.le
  have hGn0 := norm_nonneg (tcvG W b σ E z X κ x)
  calc 1 + ‖wlKh (z • 1 - X)ᴴ - tflReg κ (layerMatrix σ E z X (tflEmbed W b σ x)) *
        wlJ (PhysSite W σ) (PortSite W σ)‖ * ‖tcvG W b σ E z X κ x‖
      ≤ 1 + (‖z‖ + |E| + κ + lam) * (2 * g) :=
        add_le_add le_rfl (mul_le_mul hb hG2 hGn0 (by positivity))
    _ ≤ 2 * wlF E z X (tflEmbed W b σ x) := by
        rw [hFe]
        have : ‖z‖ + |E| + κ ≤ 6 := by linarith
        nlinarith

/-- **Weighted one-letter covariance in the coordinates** (`κ → 0`): with the a.e.
invertibility, `‖𝒢‖, ‖𝒢‖² ∈ L¹` and `E F⁴ ≤ C⁴`, the unweighted covariance of
`f = W⁻¹Tr P𝒢`, `U = Q𝒢` satisfies `‖Cov(f, U) 𝒦*‖ ≤ 160 C⁴/W²`. -/
theorem wl_cov_weighted_core (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) {E : ℝ} {z : ℂ}
    (hz : 0 ≤ z.im) (hE : |E| ≤ 2) (hzM : ‖z‖ ≤ 3)
    (P Q : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) {C : ℝ}
    (hinv : ∀ᵐ x ∂gaussianProduct (tflVar W b σ),
      IsUnit (layerMatrix σ E z X (tflEmbed W b σ x)).det)
    (hG1 : Integrable (fun x => ‖layerResolvent σ E z X (tflEmbed W b σ x)‖)
      (gaussianProduct (tflVar W b σ)))
    (hG2 : Integrable (fun x => ‖layerResolvent σ E z X (tflEmbed W b σ x)‖ ^ 2)
      (gaussianProduct (tflVar W b σ)))
    (hF4 : Integrable (fun x => wlF E z X (tflEmbed W b σ x) ^ 4) (gaussianProduct (tflVar W b σ)))
    (hF4C : ∫ x, wlF E z X (tflEmbed W b σ x) ^ 4 ∂gaussianProduct (tflVar W b σ) ≤ C ^ 4) :
    ‖((∫ x, tcvTr W σ (P * layerResolvent σ E z X (tflEmbed W b σ x)) •
          (Q * layerResolvent σ E z X (tflEmbed W b σ x)) ∂gaussianProduct (tflVar W b σ)) -
        (∫ x, tcvTr W σ (P * layerResolvent σ E z X (tflEmbed W b σ x))
          ∂gaussianProduct (tflVar W b σ)) •
          (∫ x, Q * layerResolvent σ E z X (tflEmbed W b σ x) ∂gaussianProduct (tflVar W b σ))) *
        wlKh (m := PortSite W σ) (z • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X)ᴴ‖ ≤
      160 * C ^ 4 / (W : ℝ) ^ 2 := by
  set μ := gaussianProduct (tflVar W b σ) with hμ
  set Wt : Matrix (LayerSite W σ) (LayerSite W σ) ℂ := wlKh (z • 1 - X)ᴴ with hWt
  set Gr : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun x => layerResolvent σ E z X (tflEmbed W b σ x) with hGrdef
  have hGr : Measurable Gr :=
    (measurable_layerResolvent σ E z X).comp (tfl_measurable_embed W b σ)
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set Fc : (TflCoord W σ → ℝ) → ℝ := fun x => wlF E z X (tflEmbed W b σ x) with hFc
  have hFcm : Measurable Fc := (wl_measurable_wlF E z X).comp (tfl_measurable_embed W b σ)
  have hFc0 : ∀ x, 0 ≤ Fc x := fun x => wlF_nonneg _ _ _ _
  -- the regularized family
  set κm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hκm
  have hκpos : ∀ m, 0 < κm m := fun m => by rw [hκm]; positivity
  have hκ1 : ∀ m, κm m ≤ 1 := fun m => by
    rw [hκm, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hκlim : Tendsto κm atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set Gm : ℕ → (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun m => tcvG W b σ E z X (κm m) with hGm
  have hGmc : ∀ m, Continuous (Gm m) := fun m =>
    (tcv_G_contDiff W b σ E z hX hz (hκpos m)).continuous
  have hGm2 : ∀ m, ∀ᵐ x ∂μ, ‖Gm m x‖ ≤ 2 * ‖Gr x‖ := fun m => by
    filter_upwards [hinv] with x hx
    exact tflPsi_inv_le_two W b σ E z hX hz (hκpos m) x hx
  have hGmlim : ∀ᵐ x ∂μ, Tendsto (fun m => Gm m x) atTop (𝓝 (Gr x)) := by
    filter_upwards [hinv] with x hx
    exact tcv_G_tendsto σ E z hx hκlim
  have hFc : Continuous (fun N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ => tcvTr W σ (P * N)) :=
    (tcvTr W σ).continuous.comp (continuous_const.mul continuous_id)
  have hUc : Continuous (fun N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ => Q * N) :=
    continuous_const.mul continuous_id
  have hFle : ∀ N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖tcvTr W σ (P * N)‖ ≤ 4 * ‖N‖ :=
    fun N => (tcv_tr_le σ hW _).trans (by
      gcongr
      calc ‖P * N‖ ≤ ‖P‖ * ‖N‖ := norm_mul_le _ _
        _ ≤ 1 * ‖N‖ := by gcongr
        _ = ‖N‖ := one_mul _)
  have hUle : ∀ N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖Q * N‖ ≤ ‖N‖ := fun N =>
    (norm_mul_le _ _).trans (by
      calc ‖Q‖ * ‖N‖ ≤ 1 * ‖N‖ := by gcongr
        _ = ‖N‖ := one_mul _)
  have hFUle : ∀ N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      ‖tcvTr W σ (P * N) • (Q * N)‖ ≤ 4 * ‖N‖ ^ 2 := fun N => by
    rw [norm_smul, sq]
    calc ‖tcvTr W σ (P * N)‖ * ‖Q * N‖ ≤ (4 * ‖N‖) * ‖N‖ :=
          mul_le_mul (hFle N) (hUle N) (norm_nonneg _) (by positivity)
      _ = 4 * (‖N‖ * ‖N‖) := by ring
  -- dominated convergence for the three means
  have hlimFU : Tendsto (fun m => ∫ x, tcvTr W σ (P * Gm m x) • (Q * Gm m x) ∂μ) atTop
      (𝓝 (∫ x, tcvTr W σ (P * Gr x) • (Q * Gr x) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => 16 * ‖Gr x‖ ^ 2)
      (fun m => ((hFc.comp (hGmc m)).smul (hUc.comp (hGmc m))).aestronglyMeasurable)
      (hG2.const_mul _) (fun m => ?_) ?_
    · filter_upwards [hGm2 m] with x hx
      refine (hFUle _).trans ?_
      have := pow_le_pow_left₀ (norm_nonneg _) hx 2
      nlinarith
    · filter_upwards [hGmlim] with x hx
      exact ((hFc.tendsto _).comp hx).smul ((hUc.tendsto _).comp hx)
  have hlimF : Tendsto (fun m => ∫ x, tcvTr W σ (P * Gm m x) ∂μ) atTop
      (𝓝 (∫ x, tcvTr W σ (P * Gr x) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => 8 * ‖Gr x‖)
      (fun m => (hFc.comp (hGmc m)).aestronglyMeasurable) (hG1.const_mul _) (fun m => ?_) ?_
    · filter_upwards [hGm2 m] with x hx
      refine (hFle _).trans ?_
      linarith
    · filter_upwards [hGmlim] with x hx
      exact (hFc.tendsto _).comp hx
  have hlimU : Tendsto (fun m => ∫ x, Q * Gm m x ∂μ) atTop (𝓝 (∫ x, Q * Gr x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => 2 * ‖Gr x‖)
      (fun m => (hUc.comp (hGmc m)).aestronglyMeasurable) (hG1.const_mul _) (fun m => ?_) ?_
    · filter_upwards [hGm2 m] with x hx
      exact (hUle _).trans hx
    · filter_upwards [hGmlim] with x hx
      exact (hUc.tendsto _).comp hx
  have hRc : Continuous (fun M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ => ‖M * Wt‖) :=
    continuous_norm.comp (continuous_id.mul continuous_const)
  have hlim := (hRc.tendsto _).comp (hlimFU.sub (hlimF.smul hlimU))
  refine le_of_tendsto' hlim fun m => ?_
  simp only [Function.comp_apply]
  -- the bound for each `κ_m`
  have hκ := hκpos m
  have hb := wl_cov_reg σ E z hW hb0 hb1 hX hz hκ P Q Wt hP hQ
  set G := tcvG W b σ E z X (κm m) with hGdef
  have hGle : ∀ x, ‖G x‖ ≤ (κm m)⁻¹ := tcv_G_le W b σ E z hX hz hκ
  have hGc : Continuous G := hGmc m
  -- right multiplication commutes with the regularized means
  have hiFU : Integrable (fun x => tcvTr W σ (P * G x) • (Q * G x)) μ :=
    Integrable.of_bound ((hFc.comp hGc).smul (hUc.comp hGc)).aestronglyMeasurable
      (4 * (κm m)⁻¹ ^ 2) (ae_of_all _ fun x => (hFUle _).trans (by gcongr; exact hGle x))
  have hiU : Integrable (fun x => Q * G x) μ :=
    Integrable.of_bound (hUc.comp hGc).aestronglyMeasurable (κm m)⁻¹
      (ae_of_all _ fun x => (hUle _).trans (hGle x))
  set Rm := ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) |>.flip Wt
    with hRm
  have hR : ∀ M, Rm M = M * Wt := fun M => rfl
  have e1 : (∫ x, tcvTr W σ (P * G x) • (Q * G x * Wt) ∂μ) =
      (∫ x, tcvTr W σ (P * G x) • (Q * G x) ∂μ) * Wt := by
    rw [← hR, ← Rm.integral_comp_comm hiFU]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hR, Matrix.smul_mul]
  have e2 : (∫ x, Q * G x * Wt ∂μ) = (∫ x, Q * G x ∂μ) * Wt := by
    rw [← hR, ← Rm.integral_comp_comm hiU]
    rfl
  have e3 : ((∫ x, tcvTr W σ (P * G x) • (Q * G x) ∂μ) -
      (∫ x, tcvTr W σ (P * G x) ∂μ) • (∫ x, Q * G x ∂μ)) * Wt =
      (∫ x, tcvTr W σ (P * G x) • (Q * G x * Wt) ∂μ) -
        (∫ x, tcvTr W σ (P * G x) ∂μ) • (∫ x, Q * G x * Wt ∂μ) := by
    rw [e1, e2, Matrix.sub_mul, Matrix.smul_mul]
  change ‖((∫ x, tcvTr W σ (P * G x) • (Q * G x) ∂μ) -
      (∫ x, tcvTr W σ (P * G x) ∂μ) • (∫ x, Q * G x ∂μ)) * Wt‖ ≤ _
  rw [e3]
  refine hb.trans ?_
  -- uniform moments
  have hI1 : ∫ x, ‖G x‖ ^ 4 ∂μ ≤ 16 * C ^ 4 := by
    have hint : Integrable (fun x => ‖G x‖ ^ 4) μ :=
      Integrable.of_bound ((continuous_norm.comp hGc).pow 4).aestronglyMeasurable ((κm m)⁻¹ ^ 4)
        (ae_of_all _ fun x => by
          rw [Real.norm_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hGle x) 4)
    calc ∫ x, ‖G x‖ ^ 4 ∂μ ≤ ∫ x, 16 * Fc x ^ 4 ∂μ := by
          refine integral_mono_ae hint (hF4.const_mul _) ?_
          filter_upwards [hinv] with x hx
          have h1 := (wl_reg_weighted_le (b := b) hX hz hE hzM hκ (hκ1 m) x hx).1
          have := pow_le_pow_left₀ (norm_nonneg _) h1 4
          change ‖G x‖ ^ 4 ≤ 16 * Fc x ^ 4
          calc ‖G x‖ ^ 4 ≤ (2 * Fc x) ^ 4 := this
            _ = 16 * Fc x ^ 4 := by ring
      _ = 16 * ∫ x, Fc x ^ 4 ∂μ := integral_const_mul _ _
      _ ≤ 16 * C ^ 4 := by gcongr
  have hI2 : ∫ x, (‖G x‖ * ‖G x * Wt‖) ^ 2 ∂μ ≤ 16 * C ^ 4 := by
    have hint : Integrable (fun x => (‖G x‖ * ‖G x * Wt‖) ^ 2) μ :=
      Integrable.of_bound (((continuous_norm.comp hGc).mul (continuous_norm.comp
        (hGc.mul continuous_const))).pow 2).aestronglyMeasurable
        (((κm m)⁻¹ * ((κm m)⁻¹ * ‖Wt‖)) ^ 2)
        (ae_of_all _ fun x => by
          rw [Real.norm_of_nonneg (by positivity)]
          refine pow_le_pow_left₀ (by positivity) ?_ 2
          refine mul_le_mul (hGle x) ((norm_mul_le _ _).trans ?_) (norm_nonneg _)
            (by positivity)
          exact mul_le_mul_of_nonneg_right (hGle x) (norm_nonneg _))
    calc ∫ x, (‖G x‖ * ‖G x * Wt‖) ^ 2 ∂μ ≤ ∫ x, 16 * Fc x ^ 4 ∂μ := by
          refine integral_mono_ae hint (hF4.const_mul _) ?_
          filter_upwards [hinv] with x hx
          have h1 := (wl_reg_weighted_le (b := b) hX hz hE hzM hκ (hκ1 m) x hx).1
          have h2 := wl_reg_weighted_right_le (b := b) hX hz hE hzM hκ (hκ1 m) x hx
          change (‖G x‖ * ‖G x * Wt‖) ^ 2 ≤ 16 * Fc x ^ 4
          have h3 : ‖G x‖ * ‖G x * Wt‖ ≤ (2 * Fc x) * (2 * Fc x) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by linarith [hFc0 x])
          calc (‖G x‖ * ‖G x * Wt‖) ^ 2 ≤ ((2 * Fc x) * (2 * Fc x)) ^ 2 :=
                pow_le_pow_left₀ (by positivity) h3 2
            _ = 16 * Fc x ^ 4 := by ring
      _ = 16 * ∫ x, Fc x ^ 4 ∂μ := integral_const_mul _ _
      _ ≤ 16 * C ^ 4 := by gcongr
  calc 5 / (W : ℝ) ^ 2 * ((∫ x, ‖G x‖ ^ 4 ∂μ) + ∫ x, (‖G x‖ * ‖G x * Wt‖) ^ 2 ∂μ)
      ≤ 5 / (W : ℝ) ^ 2 * (16 * C ^ 4 + 16 * C ^ 4) := by gcongr
    _ = 160 * C ^ 4 / (W : ℝ) ^ 2 := by ring

end WeightedCovLimit

section WeightedCovLaw

/-- **Weighted one-letter covariance**: `b` and `η₀ > 0` first; then
`C, W₀`; for `W ≥ W₀`, every shape, Hermitian `X`, `|E| ≤ 2`, `Im z ≥ η₀`, `|z| ≤ 3` and
`‖P‖, ‖Q‖ ≤ 1`: `‖Cov(W⁻¹ Tr P𝒢, Q𝒢) 𝒦*‖ ≤ C W⁻²` under `layerLaw` (`𝒦 = diag(z - X, 0)`). -/
theorem wl_cov_weighted (hcount : ConditionalBlockGUECount) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {η₀ : ℝ} (hη₀ : 0 < η₀) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ (σ : LayerShape)
      (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian → ∀ (E : ℝ) (z : ℂ),
      η₀ ≤ z.im → ‖z‖ ≤ 3 → |E| ≤ 2 →
      ∀ P Q : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖P‖ ≤ 1 → ‖Q‖ ≤ 1 →
        ‖meqCov (layerLaw W b σ) (fun ω => (W : ℂ)⁻¹ * (P * layerResolvent σ E z X ω).trace)
            (fun ω => Q * layerResolvent σ E z X ω) *
          wlKh (m := PortSite W σ) (z • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X)ᴴ‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C4, W₀, hC4, hmom⟩ := wl_moment_setup hcount hb0 hb1 hη₀ (q := 4) (by norm_num)
  refine ⟨160 * C4 ^ 4, W₀, by positivity, ?_⟩
  intro W hW hWW σ X hX E z hz hzM hE P Q hP hQ
  obtain ⟨hinv, hF⟩ := hmom W hW hWW σ X hX E z hz hzM
  have hz0 : 0 ≤ z.im := hη₀.le.trans hz
  set μc := gaussianProduct (tflVar W b σ) with hμc
  set Φ := tflEmbed W b σ with hΦdef
  have hΦ : Measurable Φ := tfl_measurable_embed W b σ
  have hlaw : layerLaw W b σ = μc.map Φ := tfl_layerLaw_eq_map W b σ
  have hinvc : ∀ᵐ x ∂μc, IsUnit (layerMatrix σ E z X (Φ x)).det := by
    rw [hlaw] at hinv
    exact ae_of_ae_map hΦ.aemeasurable hinv
  set Fc : (TflCoord W σ → ℝ) → ℝ := fun x => wlF E z X (Φ x) with hFc
  have hFcm : Measurable Fc := (wl_measurable_wlF E z X).comp hΦ
  have hFc0 : ∀ x, 0 ≤ Fc x := fun x => wlF_nonneg _ _ _ _
  have hFcL : eLpNorm (fun x => ‖Fc x‖) (ENNReal.ofReal ((4 : ℕ) : ℝ)) μc ≤ ENNReal.ofReal C4 := by
    have e : (fun x => ‖Fc x‖) = Fc := funext fun x => Real.norm_of_nonneg (hFc0 x)
    rw [e]
    have h1 : eLpNorm Fc (ENNReal.ofReal 4) μc =
        eLpNorm (wlF E z X) (ENNReal.ofReal 4) (layerLaw W b σ) := by
      rw [hlaw, eLpNorm_map_measure (wl_measurable_wlF E z X).aestronglyMeasurable
        hΦ.aemeasurable]
      rfl
    rw [show ((4 : ℕ) : ℝ) = 4 by norm_num, h1]
    exact hF
  obtain ⟨hF4i, hF4b⟩ := tcv_moment (m := 4) (by norm_num) hC4 hFcL
  have e4 : (fun x => ‖Fc x‖ ^ 4) = fun x => Fc x ^ 4 :=
    funext fun x => by rw [Real.norm_of_nonneg (hFc0 x)]
  rw [e4] at hF4i hF4b
  set Gr : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun x => layerResolvent σ E z X (Φ x) with hGrdef
  have hGrm : Measurable Gr := (measurable_layerResolvent σ E z X).comp hΦ
  have hGF : ∀ x, ‖Gr x‖ ≤ Fc x := fun x => by
    have hg0 := norm_nonneg (Gr x)
    have hl0 := norm_nonneg (wlLam (Φ x))
    change ‖Gr x‖ ≤ 1 + 6 * ((1 + ‖wlLam (Φ x)‖) * ‖Gr x‖)
    nlinarith
  have hdom : Integrable (fun x => 1 + Fc x ^ 4) μc := (integrable_const 1).add hF4i
  have hG1 : Integrable (fun x => ‖Gr x‖) μc :=
    Integrable.mono' hdom hGrm.norm.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      have := hGF x; have := hFc0 x
      nlinarith [sq_nonneg (Fc x), sq_nonneg (Fc x ^ 2 - 1), sq_nonneg (Fc x - 1)])
  have hG2 : Integrable (fun x => ‖Gr x‖ ^ 2) μc :=
    Integrable.mono' hdom (hGrm.norm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (by positivity)]
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (hGF x) 2
      have := hFc0 x
      nlinarith [sq_nonneg (Fc x ^ 2 - 1)])
  have hcore := wl_cov_weighted_core hW hb0 hb1 hX hz0 hE hzM P Q hP hQ hinvc hG1 hG2 hF4i hF4b
  -- transfer `meqCov` to the coordinates
  set f : LayerSample W σ → ℂ := fun ω => (W : ℂ)⁻¹ * (P * layerResolvent σ E z X ω).trace
    with hfdef
  set U : LayerSample W σ → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun ω => Q * layerResolvent σ E z X ω with hUdef
  have hGm := measurable_layerResolvent σ E z X
  have hfm : Measurable f :=
    (continuous_const.mul ((continuous_const.matrix_mul continuous_id).matrix_trace)).measurable.comp
      hGm
  have hUm : Measurable U := (continuous_const.matrix_mul continuous_id).measurable.comp hGm
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hfU_le : ∀ x, ‖f (Φ x) • U (Φ x)‖ ≤ 4 * ‖Gr x‖ ^ 2 := fun x => by
    rw [norm_smul, sq]
    have h1 : ‖f (Φ x)‖ ≤ 4 * ‖Gr x‖ := by
      refine (tcv_tr_le σ hW (P * Gr x)).trans ?_
      gcongr
      calc ‖P * Gr x‖ ≤ ‖P‖ * ‖Gr x‖ := norm_mul_le _ _
        _ ≤ 1 * ‖Gr x‖ := by gcongr
        _ = ‖Gr x‖ := one_mul _
    have h2 : ‖U (Φ x)‖ ≤ ‖Gr x‖ := (norm_mul_le _ _).trans (by
      calc ‖Q‖ * ‖Gr x‖ ≤ 1 * ‖Gr x‖ := by gcongr
        _ = ‖Gr x‖ := one_mul _)
    calc ‖f (Φ x)‖ * ‖U (Φ x)‖ ≤ (4 * ‖Gr x‖) * ‖Gr x‖ :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = 4 * (‖Gr x‖ * ‖Gr x‖) := by ring
  have hiFU : Integrable (fun x => f (Φ x) • U (Φ x)) μc :=
    Integrable.mono' (hG2.const_mul 4) ((hfm.smul hUm).comp hΦ).aestronglyMeasurable
      (ae_of_all _ hfU_le)
  have hiU : Integrable (fun x => U (Φ x)) μc :=
    Integrable.mono' hG1 (hUm.comp hΦ).aestronglyMeasurable (ae_of_all _ fun x =>
      (norm_mul_le _ _).trans (by
        calc ‖Q‖ * ‖Gr x‖ ≤ 1 * ‖Gr x‖ := by gcongr
          _ = ‖Gr x‖ := one_mul _))
  have hcov : meqCov (layerLaw W b σ) f U =
      (∫ x, tcvTr W σ (P * Gr x) • (Q * Gr x) ∂μc) -
        (∫ x, tcvTr W σ (P * Gr x) ∂μc) • (∫ x, Q * Gr x ∂μc) := by
    rw [meqCov, tcv_matrixExpect_eq (Y := fun ω => f ω • U ω) (hfm.smul hUm) hiFU, tcv_matrixExpect_eq hUm hiU, hlaw,
      integral_map hΦ.aemeasurable hfm.aestronglyMeasurable]
    rfl
  rw [hcov]
  exact hcore

end WeightedCovLaw

/-!
## 2. The pointwise Ward identity and its expectation
-/

section WardPointwise

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem wl_toBlocks11_conjTranspose (G : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (Gᴴ).toBlocks₁₁ = (G.toBlocks₁₁)ᴴ := by
  ext x y; simp [toBlocks₁₁, conjTranspose_apply]

theorem wl_toBlocks11_diag_mul (G : Matrix (n ⊕ m) (n ⊕ m) ℂ) (w : ℂ) :
    (G * diagonal (Sum.elim (fun _ : n => (0 : ℂ)) (fun _ : m => w)) * Gᴴ).toBlocks₁₁ =
      w • (G.toBlocks₁₂ * (G.toBlocks₁₂)ᴴ) := by
  ext x y
  simp only [toBlocks₁₁, toBlocks₁₂, Matrix.of_apply]
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [Matrix.mul_diagonal, Sum.elim_inl, Sum.elim_inr, mul_zero, zero_mul,
    Finset.sum_const_zero, zero_add, conjTranspose_apply]
  rw [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [conjTranspose_apply]
  ring

/-- **Exact weighted Ward identity**: for a sample with Hermitian blocks,
`(K𝒢₁₂)(K𝒢₁₂)* = (i/2η) (K𝒢₁₁K* - K𝒢₁₁*K*)`, `η = Im z ≠ 0`, every `K`. -/
theorem wl_ward_pointwise {W : ℕ} {σ : LayerShape} (E : ℝ) {z : ℂ} (hη : z.im ≠ 0)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (ω : LayerSample W σ)
    (hA : ∀ j, (ω.1 j).IsHermitian) (hN : IsUnit (layerMatrix σ E z X ω).det)
    (K : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) :
    (K * (layerResolvent σ E z X ω).toBlocks₁₂) * (K * (layerResolvent σ E z X ω).toBlocks₁₂)ᴴ =
      (Complex.I / (2 * z.im)) • (K * (layerResolvent σ E z X ω).toBlocks₁₁ * Kᴴ -
        K * ((layerResolvent σ E z X ω).toBlocks₁₁)ᴴ * Kᴴ) := by
  set N := layerMatrix σ E z X ω with hNdef
  set G := layerResolvent σ E z X ω with hGdef
  have h1 : G * N = 1 := nonsing_inv_mul _ hN
  have hid : G - Gᴴ = G * (Nᴴ - N) * Gᴴ := by
    have e1 : G * Nᴴ * Gᴴ = G := by
      rw [Matrix.mul_assoc, ← conjTranspose_mul, h1, conjTranspose_one, Matrix.mul_one]
    have e2 : G * N * Gᴴ = Gᴴ := by rw [h1, Matrix.one_mul]
    rw [Matrix.mul_sub, Matrix.sub_mul, e1, e2]
  rw [lct_layerMatrix_conj_sub E z hX ω hA] at hid
  have h11 := congrArg Matrix.toBlocks₁₁ hid
  rw [wl_toBlocks11_diag_mul] at h11
  have hsub : (G - Gᴴ).toBlocks₁₁ = G.toBlocks₁₁ - (G.toBlocks₁₁)ᴴ := by
    rw [← wl_toBlocks11_conjTranspose]; ext x y; rfl
  rw [hsub] at h11
  have hw : (conj z - z) = -(2 * z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp; ring
  have hGG : G.toBlocks₁₂ * (G.toBlocks₁₂)ᴴ =
      (Complex.I / (2 * z.im)) • (G.toBlocks₁₁ - (G.toBlocks₁₁)ᴴ) := by
    rw [h11, smul_smul, hw]
    have h2 : (2 * (z.im : ℂ)) ≠ 0 := by
      have : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη
      exact mul_ne_zero two_ne_zero this
    have : Complex.I / (2 * z.im) * (-(2 * z.im : ℂ) * Complex.I) = 1 := by
      field_simp
      rw [Complex.I_sq]; ring
    rw [this, one_smul]
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc G.toBlocks₁₂, hGG,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub]
  simp only [Matrix.mul_assoc]

end WardPointwise

/-!
## 3. The deterministic top mean inverse (the two-port Dyson equation near the matched point)
-/

section WardDet

theorem wl_sandwich_le {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖(1 + A) * (1 + B) * (1 + A)ᴴ - 1‖ ≤ 5 * ‖A‖ + 2 * ‖B‖ := by
  have e : (1 + A) * (1 + B) * (1 + A)ᴴ - 1 =
      A * ((1 + B) * (1 + Aᴴ)) + B * (1 + Aᴴ) + Aᴴ := by
    rw [conjTranspose_add, conjTranspose_one]; noncomm_ring
  rw [e]
  have h1 := lct_norm_one_le (n := n)
  have hAh : ‖Aᴴ‖ = ‖A‖ := l2_opNorm_conjTranspose A
  have hA0 := norm_nonneg A
  have hB0 := norm_nonneg B
  have h1A : ‖1 + Aᴴ‖ ≤ 2 := (norm_add_le _ _).trans (by rw [hAh]; linarith)
  have h1B : ‖1 + B‖ ≤ 2 := (norm_add_le _ _).trans (by linarith)
  have hP : ‖(1 + B) * (1 + Aᴴ)‖ ≤ 4 :=
    (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (1 + B), norm_nonneg (1 + Aᴴ)])
  calc ‖A * ((1 + B) * (1 + Aᴴ)) + B * (1 + Aᴴ) + Aᴴ‖
      ≤ ‖A‖ * ‖(1 + B) * (1 + Aᴴ)‖ + ‖B‖ * ‖1 + Aᴴ‖ + ‖Aᴴ‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))) le_rfl)
    _ ≤ ‖A‖ * 4 + ‖B‖ * 2 + ‖A‖ := by
        rw [hAh]
        gcongr
    _ = 5 * ‖A‖ + 2 * ‖B‖ := by ring

theorem wl_norm_diag_le {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ p, ‖d p‖ ≤ ε) : ‖diagonal d‖ ≤ ε := by
  rw [l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hε).mpr h

/-- `‖(i/2η) (Y - Y*)‖ ≤ ‖Y‖/η`. -/
theorem wl_norm_im_le {n : Type*} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) {η : ℝ}
    (hη : 0 < η) : ‖(Complex.I / (2 * η)) • (Y - Yᴴ)‖ ≤ ‖Y‖ / η := by
  rw [norm_smul]
  have h1 : ‖Complex.I / (2 * (η : ℂ))‖ = 1 / (2 * η) := by
    rw [norm_div, Complex.norm_I, norm_mul, Complex.norm_real, Real.norm_of_nonneg hη.le]
    simp
  rw [h1]
  have h2 : ‖Y - Yᴴ‖ ≤ 2 * ‖Y‖ :=
    (norm_sub_le _ _).trans (by rw [l2_opNorm_conjTranspose]; linarith)
  calc 1 / (2 * η) * ‖Y - Yᴴ‖ ≤ 1 / (2 * η) * (2 * ‖Y‖) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ‖Y‖ / η := by field_simp

variable {W : ℕ}

/-- **The weighted mean near the matched point** (deterministic): let
`T = -E - X - diag(s_i)` with `|z + E + s_i| ≤ ε`, `|-Im s_i - η| ≤ ε ≤ η/2` (`η = Im z`) and
`Ḡ = T⁻¹ (1 + R)`. Then `T` is invertible and, with `K = z - X`,
`‖(i/2η)(K Ḡ K* - K Ḡ* K*) - 1‖ ≤ 12 ε/η + 2 ‖R K*‖/η`. -/
theorem wl_ward_det {E : ℝ} {z : ℂ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) (s : Fin 2 → ℂ) {ε : ℝ} (hη : 0 < z.im) (hε0 : 0 ≤ ε)
    (hε : ε ≤ z.im / 2) (hsh : ∀ i, ‖z + E + s i‖ ≤ ε) (him : ∀ i, |-(s i).im - z.im| ≤ ε)
    (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    IsUnit (cmpTopH E X - diagonal (cmpExt s)).det ∧
    ‖(Complex.I / (2 * z.im)) •
        ((z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X) *
            ((cmpTopH E X - diagonal (cmpExt s))⁻¹ * (1 + R)) *
            (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ -
          (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X) *
            ((cmpTopH E X - diagonal (cmpExt s))⁻¹ * (1 + R))ᴴ *
            (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ) - 1‖ ≤
      12 * ε / z.im + 2 * ‖R * (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ‖ /
        z.im := by
  set η := z.im with hηdef
  set T := cmpTopH E X - diagonal (cmpExt s) with hTdef
  set K := z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X with hKdef
  have hs : ∀ i, η / 2 ≤ -(s i).im := fun i => by
    have := (abs_le.mp (him i)).1; linarith
  obtain ⟨hTu, hTn⟩ := lct_top_inv E hX s (by positivity : 0 < η / 2) hs
  refine ⟨hTu, ?_⟩
  set M := T⁻¹ with hMdef
  have hTM : T * M = 1 := mul_nonsing_inv T hTu
  have hMT : M * T = 1 := nonsing_inv_mul T hTu
  have hMn : ‖M‖ ≤ 2 / η := by
    rw [hMdef]; refine hTn.trans (le_of_eq ?_); field_simp
  set D1 := diagonal (cmpExt (W := W) fun i => z + E + s i) with hD1def
  have hKeq : K = T + D1 := by
    ext p q
    simp only [hKdef, hTdef, hD1def, cmpTopH, cmpExt, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.neg_apply, diagonal_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> ring
  have hKM : K * M = 1 + D1 * M := by rw [hKeq, Matrix.add_mul, hTM]
  have hD1 : ‖D1‖ ≤ ε := wl_norm_diag_le _ hε0 fun p => hsh p.1
  have hA : ‖D1 * M‖ ≤ 2 * ε / η := by
    calc ‖D1 * M‖ ≤ ‖D1‖ * ‖M‖ := norm_mul_le _ _
      _ ≤ ε * (2 / η) := mul_le_mul hD1 hMn (norm_nonneg _) hε0
      _ = 2 * ε / η := by ring
  set D2 := diagonal (cmpExt (W := W) fun i => (((-(s i).im / η : ℝ)) : ℂ)) with hD2def
  have hB : ‖D2 - 1‖ ≤ ε / η := by
    have e : D2 - 1 = diagonal (cmpExt (W := W) fun i => (((-(s i).im - η) / η : ℝ) : ℂ)) := by
      ext p q
      simp only [hD2def, cmpExt, Matrix.sub_apply, diagonal_apply, Matrix.one_apply]
      split_ifs
      · push_cast; field_simp
      · simp
    rw [e]
    refine wl_norm_diag_le _ (by positivity) fun p => ?_
    simp only [cmpExt, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hη]
    exact div_le_div_of_nonneg_right (him p.1) hη.le
  -- the imaginary part of the top inverse
  have hTT : Tᴴ - T = diagonal (cmpExt (W := W) fun i => s i - conj (s i)) := by
    rw [hTdef, conjTranspose_sub, (cmpTopH_isHermitian E hX).eq, diagonal_conjTranspose]
    ext p q
    simp only [cmpExt, Matrix.sub_apply, diagonal_apply, Pi.star_apply, Complex.star_def]
    split_ifs <;> ring
  have hMM : M - Mᴴ = M * (Tᴴ - T) * Mᴴ := by
    have e1 : M * Tᴴ * Mᴴ = M := by
      rw [Matrix.mul_assoc, ← conjTranspose_mul, hMT, conjTranspose_one, Matrix.mul_one]
    have e2 : M * T * Mᴴ = Mᴴ := by rw [hMT, Matrix.one_mul]
    rw [Matrix.mul_sub, Matrix.sub_mul, e1, e2]
  have hscal : (Complex.I / (2 * η)) • (Tᴴ - T) = D2 := by
    rw [hTT, ← diagonal_smul]
    congr 1
    funext p
    simp only [cmpExt, Pi.smul_apply, smul_eq_mul]
    have hη0 : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη.ne'
    have : s p.1 - conj (s p.1) = 2 * ((s p.1).im : ℂ) * Complex.I := by
      apply Complex.ext
      · simp
      · simp; ring
    rw [this]
    push_cast
    field_simp
    rw [Complex.I_sq]; ring
  have hmain : (Complex.I / (2 * η)) • (K * M * Kᴴ - K * Mᴴ * Kᴴ) = (K * M) * D2 * (K * M)ᴴ := by
    have e : K * M * Kᴴ - K * Mᴴ * Kᴴ = K * (M - Mᴴ) * Kᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul (K * M) (K * Mᴴ) Kᴴ]
    rw [← hscal, e, hMM, conjTranspose_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  -- split off the residual
  have hsplit : (Complex.I / (2 * η)) • (K * (M * (1 + R)) * Kᴴ - K * (M * (1 + R))ᴴ * Kᴴ) - 1 =
      ((K * M) * D2 * (K * M)ᴴ - 1) +
        (Complex.I / (2 * η)) • (K * M * (R * Kᴴ) - (K * M * (R * Kᴴ))ᴴ) := by
    rw [← hmain]
    simp only [conjTranspose_mul, conjTranspose_add, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, conjTranspose_conjTranspose, smul_sub,
      smul_add, Matrix.mul_assoc]
    abel
  rw [hsplit]
  have hε1 : 2 * ε / η ≤ 1 := by rw [div_le_one hη]; linarith
  have hε2 : ε / η ≤ 1 := by rw [div_le_one hη]; linarith
  have hS := wl_sandwich_le (D1 * M) (D2 - 1) (hA.trans hε1) (hB.trans hε2)
  rw [← hKM, show 1 + (D2 - 1) = D2 by abel] at hS
  have hKMn : ‖K * M‖ ≤ 2 := by
    rw [hKM]
    exact (norm_add_le _ _).trans (by linarith [lct_norm_one_le (n := Fin 2 × Fin W)])
  have hY : ‖K * M * (R * Kᴴ)‖ ≤ 2 * ‖R * Kᴴ‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hKMn (norm_nonneg _))
  have hI := wl_norm_im_le (K * M * (R * Kᴴ)) hη
  calc ‖((K * M) * D2 * (K * M)ᴴ - 1) +
        (Complex.I / (2 * η)) • (K * M * (R * Kᴴ) - (K * M * (R * Kᴴ))ᴴ)‖
      ≤ (5 * ‖D1 * M‖ + 2 * ‖D2 - 1‖) + ‖K * M * (R * Kᴴ)‖ / η :=
        (norm_add_le _ _).trans (add_le_add hS hI)
    _ ≤ (5 * (2 * ε / η) + 2 * (ε / η)) + 2 * ‖R * Kᴴ‖ / η := by
        gcongr
    _ = 12 * ε / η + 2 * ‖R * Kᴴ‖ / η := by ring

end WardDet

/-!
## 4. The residual after the weight, and the expectation of the Ward identity
-/

section WardMean

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The compression `M ↦ M₁₁` as a real continuous linear map. -/
def wlB11 : Matrix (n ⊕ m) (n ⊕ m) ℂ →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M.toBlocks₁₁
      map_add' := fun _ _ => by ext; rfl
      map_smul' := fun _ _ => by ext; rfl }

theorem wlB11_apply (M : Matrix (n ⊕ m) (n ⊕ m) ℂ) : wlB11 M = M.toBlocks₁₁ := rfl

/-- **Expectation of the Ward form**: for integrable `G`,
`E[c (K G₁₁ K* - K G₁₁* K*)] = c (K (EG)₁₁ K* - K (EG)₁₁* K*)`. -/
theorem wl_integral_ward {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {G : Ω → Matrix (n ⊕ m) (n ⊕ m) ℂ} (hG : Integrable G ν) (K : Matrix n n ℂ) (c : ℂ) :
    Integrable (fun ω => c • (K * (G ω).toBlocks₁₁ * Kᴴ - K * ((G ω).toBlocks₁₁)ᴴ * Kᴴ)) ν ∧
    ∫ ω, c • (K * (G ω).toBlocks₁₁ * Kᴴ - K * ((G ω).toBlocks₁₁)ᴴ * Kᴴ) ∂ν =
      c • (K * (∫ ω, G ω ∂ν).toBlocks₁₁ * Kᴴ - K * ((∫ ω, G ω ∂ν).toBlocks₁₁)ᴴ * Kᴴ) := by
  set L := ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) K Kᴴ
  have h1 : Integrable (fun ω => (G ω).toBlocks₁₁) ν := wlB11.integrable_comp hG
  have h2 : Integrable (fun ω => K * (G ω).toBlocks₁₁ * Kᴴ) ν := L.integrable_comp h1
  have h3 : Integrable (fun ω => ((G ω).toBlocks₁₁)ᴴ) ν :=
    (tcvConjCLM (n := n)).integrable_comp h1
  have h4 : Integrable (fun ω => K * ((G ω).toBlocks₁₁)ᴴ * Kᴴ) ν := L.integrable_comp h3
  refine ⟨(h2.sub h4).smul c, ?_⟩
  rw [integral_smul, integral_sub h2 h4]
  have e3 : ∫ ω, ((G ω).toBlocks₁₁)ᴴ ∂ν = (∫ ω, (G ω).toBlocks₁₁ ∂ν)ᴴ :=
    (tcvConjCLM (n := n)).integral_comp_comm h1
  have e4 : ∫ ω, (G ω).toBlocks₁₁ ∂ν = (∫ ω, G ω ∂ν).toBlocks₁₁ :=
    wlB11.integral_comp_comm hG
  have e1 : ∫ ω, K * (G ω).toBlocks₁₁ * Kᴴ ∂ν = K * (∫ ω, G ω ∂ν).toBlocks₁₁ * Kᴴ := by
    rw [← e4]
    exact L.integral_comp_comm h1
  have e2 : ∫ ω, K * ((G ω).toBlocks₁₁)ᴴ * Kᴴ ∂ν = K * ((∫ ω, G ω ∂ν).toBlocks₁₁)ᴴ * Kᴴ := by
    rw [← e4, ← e3]
    exact L.integral_comp_comm h3
  rw [e1, e2]

variable {W : ℕ} {σ : LayerShape}

/-- **Physical residual after the weight**: if every covariance of `R_phys`, multiplied on the
right by `𝒲`, has norm `≤ B`, then `‖(Σ ...) 𝒲‖ ≤ (#blocks + #blocks·#ports) B`. -/
theorem wl_resid_weighted_le {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (Wt : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) {B : ℝ}
    (h1 : ∀ a, ‖meqCov ν (fun ω => physBlockTrace (G ω) a) (fun ω => meqPhysProj a * G ω) * Wt‖ ≤
      B)
    (h2 : ∀ a j, ‖meqCov ν (fun ω => portBlockTrace (G ω) j) (fun ω => meqPhysProj a * G ω) *
      Wt‖ ≤ B) :
    ‖(∑ a, (1 - 2 * (b : ℂ)) • meqCov ν (fun ω => physBlockTrace (G ω) a)
          (fun ω => meqPhysProj a * G ω) +
        ∑ a, ∑ j, ((b : ℂ) * meqInc σ a j) •
          meqCov ν (fun ω => portBlockTrace (G ω) j) (fun ω => meqPhysProj a * G ω)) * Wt‖ ≤
      (σ.blocks + σ.blocks * σ.ports : ℕ) * B := by
  have hc : ‖(1 - 2 * (b : ℂ))‖ ≤ 1 := by
    rw [show (1 - 2 * (b : ℂ)) = ((1 - 2 * b : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
    linarith
  have hbn : ∀ a j, ‖(b : ℂ) * meqInc σ a j‖ ≤ 1 := fun a j => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0]
    have := lct_norm_meqInc_le a j
    have := norm_nonneg (meqInc σ a j)
    nlinarith
  rw [Matrix.add_mul, Finset.sum_mul]
  simp only [Finset.sum_mul, Matrix.smul_mul]
  refine (norm_add_le _ _).trans ?_
  have hA : ‖∑ a, (1 - 2 * (b : ℂ)) • (meqCov ν (fun ω => physBlockTrace (G ω) a)
      (fun ω => meqPhysProj a * G ω) * Wt)‖ ≤ σ.blocks * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖(1 - 2 * (b : ℂ)) • (meqCov ν (fun ω => physBlockTrace (G ω) a)
          (fun ω => meqPhysProj a * G ω) * Wt)‖ ≤ ∑ _a : Fin σ.blocks, B := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [norm_smul]
          have := norm_nonneg (meqCov ν (fun ω => physBlockTrace (G ω) a)
            (fun ω => meqPhysProj a * G ω) * Wt)
          nlinarith [h1 a, norm_nonneg (1 - 2 * (b : ℂ))]
      _ = σ.blocks * B := by simp
  have hP : ‖∑ a, ∑ j, ((b : ℂ) * meqInc σ a j) • (meqCov ν (fun ω => portBlockTrace (G ω) j)
      (fun ω => meqPhysProj a * G ω) * Wt)‖ ≤ (σ.blocks * σ.ports : ℕ) * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖∑ j, ((b : ℂ) * meqInc σ a j) • (meqCov ν (fun ω => portBlockTrace (G ω) j)
          (fun ω => meqPhysProj a * G ω) * Wt)‖ ≤ ∑ _a : Fin σ.blocks, ∑ _j : Fin σ.ports, B := by
          refine Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans ?_
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_smul]
          have := norm_nonneg (meqCov ν (fun ω => portBlockTrace (G ω) j)
            (fun ω => meqPhysProj a * G ω) * Wt)
          nlinarith [h2 a j, hbn a j, norm_nonneg ((b : ℂ) * meqInc σ a j)]
      _ = (σ.blocks * σ.ports : ℕ) * B := by simp; ring
  push_cast at hP ⊢
  linarith

end WardMean

/-!
## 5. The weighted Ward identity
-/

section Ward

/-- `LL*` for one separate-port step, `L = K 𝒢₁₂`, `K = z_∂ - X`. -/
def wlLL (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .separate) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ((boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X) *
      (layerResolvent .separate E (boundaryZ b E) X ω).toBlocks₁₂) *
    ((boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X) *
      (layerResolvent .separate E (boundaryZ b E) X ω).toBlocks₁₂)ᴴ

/-- **The weighted Ward identity, Bochner form**: `b, κ` first;
then `d_* > 0`, `C ≥ 0`, `W₀`; for `W ≥ W₀`, Hermitian `X`, `E ∈ I` with `d(X) ≤ d_*`:
`LL*` is integrable and `‖E LL* - 1‖ ≤ C (d(X) + W⁻²)`. -/
theorem wl_ward_core (hcount : ConditionalBlockGUECount) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ 0 ≤ C ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
      matchedDistance b E X ≤ dstar →
      Integrable (wlLL b E X) (layerLaw W b .separate) ∧
      ‖∫ ω, wlLL b E X ω ∂layerLaw W b .separate - 1‖ ≤
        C * (matchedDistance b E X + 1 / (W : ℝ) ^ 2) := by
  intro b hb0 hb1 κ hκ
  obtain ⟨η₀, hη₀, hbulk⟩ := wl_bulk hb0 hb1 hκ
  obtain ⟨d₁, Cc, Wc, hd₁, hcmp⟩ := layerComparison_holds hcount b hb0 hb1 κ hκ
  obtain ⟨Cw, Ww, hCw, hcov⟩ := wl_cov_weighted hcount hb0 hb1 hη₀
  obtain ⟨C2, W2, hC2, hmom⟩ := wl_moment_setup hcount hb0 hb1 hη₀ (q := 2) (by norm_num)
  set C' := max Cc 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  obtain ⟨Ws, hWs⟩ := lct_small C' (ε := η₀ / 4) (by positivity)
  refine ⟨min d₁ (η₀ / (4 * (C' + 1))), (12 * C' + 12 * Cw) / η₀,
    max (max Wc Ww) (max W2 Ws), lt_min hd₁ (by positivity), by positivity, ?_⟩
  intro W hW hWW X hX E hE hd
  have hWc : Wc ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hWW)
  have hWw : Ww ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hWW)
  have hW2 : W2 ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hWW)
  have hWs' : Ws ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hWW)
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨hz, hzM, hE2⟩ := hbulk E hE
  have hEabs : |E| < 2 := abs_lt_two_of_mem_bulkInterval hκ hE
  set z := boundaryZ b E with hzdef
  have hη : 0 < z.im := lt_of_lt_of_le hη₀ hz
  set μ := layerLaw W b .separate with hμ
  set 𝒢 := fun ω => layerResolvent .separate E z X ω with h𝒢
  have hGm : Measurable 𝒢 := measurable_layerResolvent .separate E z X
  obtain ⟨hinv, hF⟩ := hmom W hW hW2 .separate X hX E z hz hzM
  have := bond_isProbabilityMeasure_layerLaw W b .separate
  -- integrability of `𝒢`
  set F := wlF (σ := .separate) E z X with hFdef
  have hFm : Measurable F := wl_measurable_wlF _ _ _
  have hFmem : MemLp F 2 μ := by
    have h1 : MemLp F (ENNReal.ofReal 2) μ := memLp_iff.mpr (lt_of_le_of_lt hF ENNReal.ofReal_lt_top)
    simpa using h1
  have hGF : ∀ ω, ‖𝒢 ω‖ ≤ F ω := fun ω => by
    have hg0 := norm_nonneg (𝒢 ω)
    have hl0 := norm_nonneg (wlLam ω)
    change ‖𝒢 ω‖ ≤ 1 + 6 * ((1 + ‖wlLam ω‖) * ‖𝒢 ω‖)
    nlinarith
  have hG2 : Integrable (fun ω => ‖layerResolvent .separate E z X ω‖ ^ 2) μ := by
    refine Integrable.mono' hFmem.integrable_sq ((hGm.norm.pow_const 2).aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hGF ω) 2
  have hG1 : Integrable (fun ω => ‖𝒢 ω‖) μ := by
    have hd : Integrable (fun ω => 1 + ‖layerResolvent .separate E z X ω‖ ^ 2) μ :=
      (integrable_const (1 : ℝ)).add hG2
    refine Integrable.mono' hd hGm.norm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    change ‖𝒢 ω‖ ≤ 1 + ‖𝒢 ω‖ ^ 2
    nlinarith [sq_nonneg (‖𝒢 ω‖ - 1), norm_nonneg (𝒢 ω)]
  have hGi : Integrable 𝒢 μ := Integrable.mono' hG1 hGm.aestronglyMeasurable
    (ae_of_all _ fun _ => le_rfl)
  -- the mean equation and the top block
  have hme := meanEquation_of_moments hW hb0.le hb1.le .separate hX E hη.le hinv hG2
  have hblk := (meq_blocks hme).1
  rw [meq_resid_toBlocks11, meqTop_separate] at hblk
  set gA := meqMeanA μ (layerResolvent .separate E z X) with hgA
  set gP := meqMeanP μ (layerResolvent .separate E z X) with hgP
  set R := meqResidTop μ (1 - 2 * (b : ℂ)) b (layerResolvent .separate E z X) with hR
  set s : Fin 2 → ℂ := fun i => (1 - 2 * (b : ℂ)) * gA i + b * gP i with hs
  set T := cmpTopH E X - diagonal (cmpExt (W := W) s) with hT
  have hTeq : (-((E : ℂ) • (1 : Matrix (PhysSite W .separate) (PhysSite W .separate) ℂ)) - X -
      diagonal (fun x : PhysSite W .separate => (1 - 2 * (b : ℂ)) * gA x.1 + b * gP x.1)) = T :=
    rfl
  rw [hTeq] at hblk
  -- the comparison solution and the scalar deviations
  have hd0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
  obtain ⟨⟨m, u, -, -, hclose, hmeans⟩, -⟩ := hcmp W hW hWc X hX E hE (hd.trans (min_le_left _ _))
  set a := matchedA E with ha
  set ε : ℝ := C' * matchedDistance b E X + C' / (W : ℝ) ^ 2 with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hgA : ∀ i, ‖gA i - a‖ ≤ ε := fun i => by
    have h1 := (hmeans i).1
    have h2 := hclose i
    have h3 : ‖m i - a‖ ≤ Cc * matchedDistance b E X := (le_add_of_nonneg_right
      (norm_nonneg _)).trans h2
    calc ‖gA i - a‖ ≤ ‖gA i - m i‖ + ‖m i - a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ Cc / (W : ℝ) ^ 2 + Cc * matchedDistance b E X := add_le_add h1 h3
      _ ≤ ε := by
          rw [hεdef]
          have : Cc / (W : ℝ) ^ 2 ≤ C' / (W : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
          nlinarith [mul_le_mul_of_nonneg_right (le_max_left Cc 0) hd0]
  have hgP : ∀ i, ‖gP i - a‖ ≤ ε := fun i => by
    have h1 := (hmeans i).2
    have h2 := hclose i
    have h3 : ‖u i - a‖ ≤ Cc * matchedDistance b E X := (le_add_of_nonneg_left
      (norm_nonneg _)).trans h2
    calc ‖gP i - a‖ ≤ ‖gP i - u i‖ + ‖u i - a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ Cc / (W : ℝ) ^ 2 + Cc * matchedDistance b E X := add_le_add h1 h3
      _ ≤ ε := by
          rw [hεdef]
          have : Cc / (W : ℝ) ^ 2 ≤ C' / (W : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
          nlinarith [mul_le_mul_of_nonneg_right (le_max_left Cc 0) hd0]
  have hcb : (0 : ℝ) ≤ 1 - 2 * b := by linarith
  have hsh : ∀ i, ‖z + E + s i‖ ≤ ε := fun i => by
    have hz' := boundaryZ_eq (b := b) hE2
    have e : z + E + s i = ((1 - 2 * b : ℝ) : ℂ) * (gA i - a) + (b : ℂ) * (gP i - a) := by
      rw [hzdef, hz', hs]; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hcb,
      Real.norm_of_nonneg hb0.le]
    nlinarith [hgA i, hgP i, norm_nonneg (gA i - a), norm_nonneg (gP i - a)]
  have him : ∀ i, |-(s i).im - z.im| ≤ ε := fun i => by
    have hzi := boundaryZ_im (b := b) hE2
    have hsim : (s i).im = (1 - 2 * b) * (gA i).im + b * (gP i).im := by
      rw [hs]
      simp [Complex.mul_im]
    have e : -(s i).im - z.im = -((1 - 2 * b) * (gA i - a).im) - b * (gP i - a).im := by
      rw [hsim, hzdef, hzi, Complex.sub_im, Complex.sub_im]
      ring
    rw [e]
    have h1 := Complex.abs_im_le_norm (gA i - a)
    have h2 := Complex.abs_im_le_norm (gP i - a)
    have h3 := hgA i
    have h4 := hgP i
    rw [abs_le]
    constructor <;> nlinarith [abs_le.mp (h1.trans h3), abs_le.mp (h2.trans h4)]
  have hεη : ε ≤ z.im / 2 := by
    have h1 : C' * matchedDistance b E X ≤ η₀ / 4 := by
      have hd' : matchedDistance b E X ≤ η₀ / (4 * (C' + 1)) := hd.trans (min_le_right _ _)
      calc C' * matchedDistance b E X ≤ (C' + 1) * (η₀ / (4 * (C' + 1))) :=
            mul_le_mul (by linarith) hd' hd0 (by positivity)
        _ = η₀ / 4 := by field_simp
    have h2 := hWs W hW hWs'
    rw [hεdef]
    linarith
  obtain ⟨hTu, hdet⟩ := wl_ward_det hX s hη hε0 hεη hsh him R
  -- the expectation of `𝒢₁₁`
  have hEbar : (matrixExpect μ (layerResolvent .separate E z X)).toBlocks₁₁ = T⁻¹ * (1 + R) := by
    rw [← hblk, ← Matrix.mul_assoc, nonsing_inv_mul _ hTu, Matrix.one_mul]
  have hME : matrixExpect μ (layerResolvent .separate E z X) = ∫ ω, 𝒢 ω ∂μ :=
    meq_matrixExpect_eq hGi
  -- the Ward identity, pointwise and in mean
  set K := z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X with hK
  set c : ℂ := Complex.I / (2 * z.im) with hc
  have hae : ∀ᵐ ω ∂μ, wlLL b E X ω =
      c • (K * (𝒢 ω).toBlocks₁₁ * Kᴴ - K * ((𝒢 ω).toBlocks₁₁)ᴴ * Kᴴ) := by
    filter_upwards [hinv, lct_ae_blocks_isHermitian W b .separate] with ω hω hA
    exact wl_ward_pointwise E hη.ne' hX ω hA hω K
  obtain ⟨hint, hval⟩ := wl_integral_ward hGi K c
  refine ⟨hint.congr (hae.mono fun ω h => h.symm), ?_⟩
  rw [integral_congr_ae hae, hval, ← hME, hEbar]
  refine hdet.trans ?_
  -- the weighted residual
  have hRK : ‖R * Kᴴ‖ ≤ 6 * (Cw / (W : ℝ) ^ 2) := by
    set S := ∑ a, (1 - 2 * (b : ℂ)) • meqCov μ
          (fun ω => physBlockTrace (layerResolvent .separate E z X ω) a)
          (fun ω => meqPhysProj a * layerResolvent .separate E z X ω) +
        ∑ a, ∑ j, ((b : ℂ) * meqInc .separate a j) •
          meqCov μ (fun ω => portBlockTrace (layerResolvent .separate E z X ω) j)
            (fun ω => meqPhysProj a * layerResolvent .separate E z X ω) with hSdef
    have hRS : R * Kᴴ = (S * wlKh (m := PortSite W .separate) Kᴴ).toBlocks₁₁ := by
      rw [wl_mul_Kh_toBlocks11]; rfl
    rw [hRS]
    refine (wl_norm_toBlocks11_le _).trans ?_
    have h := wl_resid_weighted_le μ hb0.le hb1.le (layerResolvent .separate E z X)
      (wlKh (m := PortSite W .separate) Kᴴ) (B := Cw / (W : ℝ) ^ 2)
      (fun a => by
        rw [lct_cov_phys_eq]
        exact hcov W hW hWw .separate X hX E z hz hzM hE2 _ _ (meq_norm_physProj_le a)
          (meq_norm_physProj_le a))
      (fun a j => by
        rw [lct_cov_port_eq]
        exact hcov W hW hWw .separate X hX E z hz hzM hE2 _ _ (meq_norm_portProj_le j)
          (meq_norm_physProj_le a))
    refine h.trans (le_of_eq ?_)
    norm_num
  have hd' := hd0
  calc 12 * ε / z.im + 2 * ‖R * Kᴴ‖ / z.im
      ≤ 12 * ε / η₀ + 2 * (6 * (Cw / (W : ℝ) ^ 2)) / η₀ := by
        gcongr
    _ = (12 * C' * matchedDistance b E X + 12 * C' / (W : ℝ) ^ 2 + 12 * Cw / (W : ℝ) ^ 2) / η₀ := by
        rw [hεdef]; ring
    _ ≤ (12 * C' + 12 * Cw) / η₀ * (matchedDistance b E X + 1 / (W : ℝ) ^ 2) := by
        rw [div_mul_eq_mul_div]
        refine div_le_div_of_nonneg_right ?_ hη₀.le
        have h1 : 0 ≤ 12 * Cw * matchedDistance b E X := by positivity
        have e : (12 * C' + 12 * Cw) * (matchedDistance b E X + 1 / (W : ℝ) ^ 2) =
            12 * C' * matchedDistance b E X + 12 * C' / (W : ℝ) ^ 2 + 12 * Cw / (W : ℝ) ^ 2 +
              12 * Cw * matchedDistance b E X := by ring
        rw [e]; linarith

end Ward

end BlockBand.Layers
