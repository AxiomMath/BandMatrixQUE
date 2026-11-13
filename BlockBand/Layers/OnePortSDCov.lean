module

public import BlockBand.Layers.CoreMeans
public import BlockBand.Layers.TraceCovariance

/-!
# One-letter trace–matrix covariance for an affine Gaussian family (passive-ready)

## Setting

A finite real Gaussian vector `x ~ gaussianProduct v` and an affine matrix family
`x ↦ C₀ + L x` with the regularity hypothesis `CoreReg C₀ L` of `CoreMeans`
(`Ψ_κ(x) = C₀ + iκ + Lx` invertible with `‖Ψ_κ(x)⁻¹‖ ≤ κ⁻¹` for all `x`, `κ > 0`). No Hermitian
structure of `C₀` is used: this is what makes the bound available for **passive** inputs, whose
layer matrix has `Im ⪰ 0` but is not Hermitian. The only structural input is a contraction bound
`‖𝒱(K)‖ ≤ γ‖K‖` for `𝒱(K) = Σᵢ vᵢ Tr(KΛᵢ) Λᵢ`, `Λᵢ = L eᵢ`.

## Results

* `osdCov μ f U = E[fU] - E[f] E[U]` (Bochner integrals).
* `osd_cov_reg` (fixed `κ > 0`): for `f_κ = w Tr(P G_κ)`, `U_κ = Q G_κ 𝒲` (any deterministic `𝒲`),
  `‖Cov(f_κ, U_κ)‖ ≤ (|w|γ‖P‖‖Q‖/2) (E‖G_κ‖⁴ + E(‖G_κ‖ ‖G_κ𝒲‖)²)` (OU identity
  `ou_covariance_matrix`, the kernel `w Q G_κ(y) 𝒱(G_κ(x) P G_κ(x)) G_κ(y) 𝒲`, AM–GM and
  `x_t ~ μ`).
* `osd_cov_limit` (`κ → 0`): if `C₀ + Lx` is a.s. invertible and a majorant `H` with `E H⁴ < ∞`
  dominates `‖G_κ‖` and `‖G_κ 𝒲‖` a.s. for every `κ ∈ (0,1]`, then `f = w Tr(P G)`, `U = Q G 𝒲`
  (`G = (C₀ + Lx)⁻¹`) and `fU` are integrable and `‖Cov(f, U)‖ ≤ |w|γ‖P‖‖Q‖ E H⁴`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Inputs (gaussianProduct)
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator

/-- The covariance `Cov(f, U) = E[f U] - E[f] E[U]` (Bochner integrals). -/
def osdCov {Ω : Type*} [MeasurableSpace Ω] {m : Type*} [Fintype m] [DecidableEq m]
    (μ : Measure Ω) (f : Ω → ℂ) (U : Ω → Matrix m m ℂ) : Matrix m m ℂ :=
  (∫ x, f x • U x ∂μ) - (∫ x, f x ∂μ) • ∫ x, U x ∂μ

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
  {n : Type} [Fintype n] [DecidableEq n]
  {C0 : Matrix n n ℂ} {L : (ι → ℝ) →L[ℝ] Matrix n n ℂ}

/-- **Fixed-`κ` one-letter covariance bound** for an affine Gaussian family with `CoreReg` and a
contraction bound `‖Σᵢ vᵢ Tr(KΛᵢ)Λᵢ‖ ≤ γ‖K‖`: with `f_κ = w Tr(P G_κ)`, `U_κ = Q G_κ 𝒲`,
`‖Cov(f_κ, U_κ)‖ ≤ (|w|γ‖P‖‖Q‖/2)(E‖G_κ‖⁴ + E(‖G_κ‖‖G_κ𝒲‖)²)`. -/
theorem osd_cov_reg (hreg : CoreReg C0 L) {γ : ℝ} (hγ : 0 ≤ γ)
    (hV : ∀ K : Matrix n n ℂ,
      ‖∑ i, (((v i : ℝ) : ℂ) * (K * L (Pi.single i 1)).trace) • L (Pi.single i 1)‖ ≤ γ * ‖K‖)
    (w : ℝ) (P Q Wt : Matrix n n ℂ) {κ : ℝ} (hκ : 0 < κ) :
    ‖osdCov (gaussianProduct v) (coreF C0 L w P κ) (fun x => Q * coreG C0 L κ x * Wt)‖ ≤
      |w| * γ * ‖P‖ * ‖Q‖ / 2 * ((∫ x, ‖coreG C0 L κ x‖ ^ 4 ∂gaussianProduct v) +
        ∫ x, (‖coreG C0 L κ x‖ * ‖coreG C0 L κ x * Wt‖) ^ 2 ∂gaussianProduct v) := by
  set μ := gaussianProduct v with hμ
  set G := coreG C0 L κ with hGdef
  have hGc : ContDiff ℝ 1 G := coreG_contDiff hreg hκ
  have hGcont : Continuous G := hGc.continuous
  have hGle : ∀ x, ‖G x‖ ≤ κ⁻¹ := coreG_norm_le hreg hκ
  have hκi : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  set TG : (ι → ℝ) → ((ι → ℝ) →L[ℝ] Matrix n n ℂ) := fun x =>
    (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (G x) (G x))).comp L with hTG
  have hderG : ∀ x, HasFDerivAt G (TG x) x := fun x => coreG_hasFDerivAt hreg hκ x
  have hTGv : ∀ x y, TG x y = -(G x * L y * G x) := fun x y => by
    simp only [hTG, ContinuousLinearMap.comp_apply, _root_.neg_apply,
      ContinuousLinearMap.mulLeftRight_apply]
  have hTn : ∀ x, ‖TG x‖ ≤ κ⁻¹ ^ 2 * ‖L‖ := by
    intro x
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
    rw [hTGv, norm_neg]
    calc ‖G x * L y * G x‖ ≤ ‖G x‖ * ‖L y‖ * ‖G x‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ κ⁻¹ * (‖L‖ * ‖y‖) * κ⁻¹ := by
          gcongr
          · exact hGle x
          · exact L.le_opNorm y
          · exact hGle x
      _ = κ⁻¹ ^ 2 * ‖L‖ * ‖y‖ := by ring
  set Tr := LinearMap.toContinuousLinearMap (coreTrLin (n := n) w P) with hTr
  set LU := ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) Q Wt with hLU
  set f : (ι → ℝ) → ℂ := coreF C0 L w P κ with hfdef
  set U : (ι → ℝ) → Matrix n n ℂ := fun x => Q * G x * Wt with hUdef
  have hfd : ContDiff ℝ 1 f := coreF_contDiff hreg w P hκ
  have hUd : ContDiff ℝ 1 U := LU.contDiff.comp hGc
  have hfder : ∀ x, fderiv ℝ f x = Tr.comp (TG x) := fun x =>
    (Tr.hasFDerivAt.comp x (hderG x)).fderiv
  have hUder : ∀ x, fderiv ℝ U x = LU.comp (TG x) := fun x =>
    (LU.hasFDerivAt.comp x (hderG x)).fderiv
  have hfC : ∀ x, ‖f x‖ ≤ |w| * (Fintype.card n * (‖P‖ * κ⁻¹)) := fun x => by
    refine (coreF_norm_le w P κ x).trans ?_
    gcongr
    exact hGle x
  have hUC : ∀ x, ‖U x‖ ≤ ‖Q‖ * κ⁻¹ * ‖Wt‖ := fun x => by
    calc ‖Q * G x * Wt‖ ≤ ‖Q‖ * ‖G x‖ * ‖Wt‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖Q‖ * κ⁻¹ * ‖Wt‖ := by gcongr; exact hGle x
  have hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ ‖Tr‖ * (κ⁻¹ ^ 2 * ‖L‖) := fun x => by
    rw [hfder]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (hTn x) (norm_nonneg _))
  have hU'C : ∀ x, ‖fderiv ℝ U x‖ ≤ ‖LU‖ * (κ⁻¹ ^ 2 * ‖L‖) := fun x => by
    rw [hUder]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (hTn x) (norm_nonneg _))
  -- the pointwise kernel bound
  set c₀ : ℝ := |w| * γ * ‖P‖ * ‖Q‖ / 2 with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  set h₁ : (ι → ℝ) → ℝ := fun x => ‖G x‖ ^ 4 with hh₁
  set h₂ : (ι → ℝ) → ℝ := fun x => (‖G x‖ * ‖G x * Wt‖) ^ 2 with hh₂
  have hker : ∀ x y : ι → ℝ,
      ‖∑ i, (((v i : ℝ) : ℂ) * fderiv ℝ f x (Pi.single i 1)) • fderiv ℝ U y (Pi.single i 1)‖ ≤
        c₀ * (h₁ x + h₂ y) := by
    intro x y
    set K := G x * P * G x with hK
    have e1 : ∀ i, fderiv ℝ f x (Pi.single i 1) = -((w : ℂ) * (K * L (Pi.single i 1)).trace) :=
      fun i => coreF_fderiv hreg w P hκ x _
    have e2 : ∀ i, fderiv ℝ U y (Pi.single i 1) =
        -(Q * (G y * L (Pi.single i 1) * G y) * Wt) := fun i => by
      rw [hUder, ContinuousLinearMap.comp_apply, hTGv, hLU, ContinuousLinearMap.mulLeftRight_apply]
      simp only [Matrix.mul_neg, Matrix.neg_mul]
    have hsum : ∑ i, (((v i : ℝ) : ℂ) * fderiv ℝ f x (Pi.single i 1)) •
        fderiv ℝ U y (Pi.single i 1) = (w : ℂ) • (Q * G y *
          (∑ i, (((v i : ℝ) : ℂ) * (K * L (Pi.single i 1)).trace) • L (Pi.single i 1)) *
            (G y * Wt)) := by
      simp only [e1, e2, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_neg, neg_smul, neg_neg,
        Matrix.mul_assoc, mul_neg]
      congr 1
      ring
    rw [hsum, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have hVK := hV K
    have hKn : ‖K‖ ≤ ‖P‖ * ‖G x‖ ^ 2 := by
      calc ‖K‖ ≤ ‖G x * P‖ * ‖G x‖ := norm_mul_le _ _
        _ ≤ ‖G x‖ * ‖P‖ * ‖G x‖ := by gcongr; exact norm_mul_le _ _
        _ = ‖P‖ * ‖G x‖ ^ 2 := by ring
    set V := ∑ i, (((v i : ℝ) : ℂ) * (K * L (Pi.single i 1)).trace) • L (Pi.single i 1)
    have h1 : ‖Q * G y * V * (G y * Wt)‖ ≤ ‖Q‖ * ‖G y‖ * ‖V‖ * ‖G y * Wt‖ := by
      refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact norm_mul_le _ _
    have hGy := norm_nonneg (G y)
    have hGyW := norm_nonneg (G y * Wt)
    have hQ := norm_nonneg Q
    have hP := norm_nonneg P
    have hab := mul_nonneg hGy hGyW
    have hamgm : ‖G x‖ ^ 2 * (‖G y‖ * ‖G y * Wt‖) ≤
        (‖G x‖ ^ 4 + (‖G y‖ * ‖G y * Wt‖) ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖G x‖ ^ 2 - ‖G y‖ * ‖G y * Wt‖)]
    calc |w| * ‖Q * G y * V * (G y * Wt)‖
        ≤ |w| * (‖Q‖ * ‖G y‖ * ‖V‖ * ‖G y * Wt‖) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ |w| * (‖Q‖ * ‖G y‖ * (γ * (‖P‖ * ‖G x‖ ^ 2)) * ‖G y * Wt‖) := by
          gcongr
          exact hVK.trans (mul_le_mul_of_nonneg_left hKn hγ)
      _ = (|w| * γ * ‖P‖ * ‖Q‖) * (‖G x‖ ^ 2 * (‖G y‖ * ‖G y * Wt‖)) := by ring
      _ ≤ (|w| * γ * ‖P‖ * ‖Q‖) * ((‖G x‖ ^ 4 + (‖G y‖ * ‖G y * Wt‖) ^ 2) / 2) :=
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
    set y : (ι → ℝ) × (ι → ℝ) → (ι → ℝ) :=
      fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2 with hy
    have hyc : Continuous y := by fun_prop
    have hA : Integrable (fun p : (ι → ℝ) × (ι → ℝ) => h₁ p.1) (μ.prod μ) :=
      ou_integrable_bdd v (hh₁c.comp continuous_fst) fun p => hh₁b p.1
    have hB : Integrable (fun p : (ι → ℝ) × (ι → ℝ) => h₂ (y p)) (μ.prod μ) :=
      ou_integrable_bdd v (hh₂c.comp hyc) fun p => hh₂b (y p)
    have hbd := norm_integral_le_of_norm_le ((hA.add hB).const_mul c₀)
      (Eventually.of_forall fun p => hker p.1 (y p))
    refine hbd.trans (le_of_eq ?_)
    rw [integral_const_mul]
    simp only [Pi.add_apply]
    rw [integral_add hA hB, integral_fun_fst (fun x => h₁ x), probReal_univ, one_smul,
      tcv_integral_interp v hh₂c ht.le]
  rw [osdCov, ou_covariance_matrix v hfd hfC hf'C hUd hUC hU'C]
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-t) * (c₀ * (I₁ + I₂))) (Set.Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).mul_const _
  refine (norm_integral_le_of_norm_le hexp ?_).trans (le_of_eq ?_)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (hkt t ht) (Real.exp_pos _).le
  · rw [integral_mul_const, integral_exp_neg_Ioi_zero, one_mul]

omit [DecidableEq ι] in
/-- `h ≤ 1 + h⁴` and `h² ≤ 1 + h⁴`. -/
theorem osd_le_one_add_pow4 (h : ℝ) : h ≤ 1 + h ^ 4 ∧ h ^ 2 ≤ 1 + h ^ 4 := by
  constructor
  · nlinarith [sq_nonneg (h ^ 2 - 1 / 2), sq_nonneg (h - 1 / 2)]
  · nlinarith [sq_nonneg (h ^ 2 - 1 / 2)]

/-- **One-letter covariance bound in the limit `κ → 0`.** Under `CoreReg`, the contraction bound,
a.s. invertibility of `C₀ + Lx`, and a majorant `H` with `‖G_κ‖ ≤ H`, `‖G_κ𝒲‖ ≤ H` a.s. for every
`κ ∈ (0,1]` and `H⁴ ∈ L¹`: `f = w Tr(P G)`, `U = Q G 𝒲` and `fU` are integrable and
`‖Cov(f, U)‖ ≤ |w|γ‖P‖‖Q‖ E H⁴`, `G = (C₀ + Lx)⁻¹`. -/
theorem osd_cov_limit (hreg : CoreReg C0 L) {γ : ℝ} (hγ : 0 ≤ γ)
    (hV : ∀ K : Matrix n n ℂ,
      ‖∑ i, (((v i : ℝ) : ℂ) * (K * L (Pi.single i 1)).trace) • L (Pi.single i 1)‖ ≤ γ * ‖K‖)
    (w : ℝ) (P Q Wt : Matrix n n ℂ)
    (hinv : ∀ᵐ x ∂gaussianProduct v, IsUnit (C0 + L x).det)
    {H : (ι → ℝ) → ℝ} (hHm : AEStronglyMeasurable H (gaussianProduct v))
    (hH : ∀ κ : ℝ, 0 < κ → κ ≤ 1 → ∀ᵐ x ∂gaussianProduct v,
      ‖coreG C0 L κ x‖ ≤ H x ∧ ‖coreG C0 L κ x * Wt‖ ≤ H x)
    (hH4 : Integrable (fun x => H x ^ 4) (gaussianProduct v)) :
    Integrable (fun x => (w : ℂ) * (P * (C0 + L x)⁻¹).trace) (gaussianProduct v) ∧
      Integrable (fun x => Q * (C0 + L x)⁻¹ * Wt) (gaussianProduct v) ∧
      Integrable (fun x => ((w : ℂ) * (P * (C0 + L x)⁻¹).trace) • (Q * (C0 + L x)⁻¹ * Wt))
        (gaussianProduct v) ∧
      ‖osdCov (gaussianProduct v) (fun x => (w : ℂ) * (P * (C0 + L x)⁻¹).trace)
          (fun x => Q * (C0 + L x)⁻¹ * Wt)‖ ≤
        |w| * γ * ‖P‖ * ‖Q‖ * ∫ x, H x ^ 4 ∂gaussianProduct v := by
  set μ := gaussianProduct v with hμ
  set G0 : (ι → ℝ) → Matrix n n ℂ := fun x => (C0 + L x)⁻¹ with hG0
  have hG0m : Measurable G0 :=
    measurable_matrix_inv.comp (continuous_const.add L.continuous).measurable
  set κm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hκm
  have hκpos : ∀ m, 0 < κm m := fun m => by rw [hκm]; positivity
  have hκ1 : ∀ m, κm m ≤ 1 := fun m => by
    rw [hκm, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hκlim : Tendsto κm atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set Gm : ℕ → (ι → ℝ) → Matrix n n ℂ := fun m => coreG C0 L (κm m) with hGm
  have hGmc : ∀ m, Continuous (Gm m) := fun m => coreG_continuous hreg (hκpos m)
  have hconv : ∀ᵐ x ∂μ, Tendsto (fun m => Gm m x) atTop (𝓝 (G0 x)) := by
    filter_upwards [hinv] with x hx
    set N := C0 + L x with hN
    have hU : IsUnit N := (Matrix.isUnit_iff_isUnit_det N).mpr hx
    have hcN : Continuous (fun κ : ℝ => C0 + ((κ : ℂ) * Complex.I) • (1 : Matrix n n ℂ) + L x) := by
      fun_prop
    have h1 : Tendsto (fun m => corePsi C0 L (κm m) x) atTop (𝓝 N) := by
      have := (hcN.tendsto 0).comp hκlim
      simp only [Complex.ofReal_zero, zero_mul, zero_smul, add_zero] at this
      exact this
    have h2 : Tendsto (fun m => Ring.inverse (corePsi C0 L (κm m) x)) atTop
        (𝓝 (Ring.inverse N)) := by
      have hc := NormedRing.inverse_continuousAt hU.unit
      rw [IsUnit.unit_spec] at hc
      exact hc.tendsto.comp h1
    have hG0x : G0 x = Ring.inverse N := by
      rw [hG0]; simp only; rw [Matrix.nonsing_inv_eq_ringInverse]
    rw [hG0x]
    exact h2
  have hHall : ∀ᵐ x ∂μ, ∀ m, ‖Gm m x‖ ≤ H x ∧ ‖Gm m x * Wt‖ ≤ H x :=
    ae_all_iff.mpr fun m => hH (κm m) (hκpos m) (hκ1 m)
  have hlimb : ∀ᵐ x ∂μ, ‖G0 x‖ ≤ H x ∧ ‖G0 x * Wt‖ ≤ H x := by
    filter_upwards [hconv, hHall] with x hx hb
    constructor
    · exact le_of_tendsto' (hx.norm) fun m => (hb m).1
    · exact le_of_tendsto' ((hx.mul_const Wt).norm) fun m => (hb m).2
  have hH0 : ∀ᵐ x ∂μ, 0 ≤ H x := by
    filter_upwards [hlimb] with x hx
    exact (norm_nonneg _).trans hx.1
  have hH1 : Integrable H μ := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hH4) hHm ?_
    filter_upwards [hH0] with x hx
    rw [Real.norm_of_nonneg hx]
    exact (osd_le_one_add_pow4 (H x)).1
  have hH2 : Integrable (fun x => H x ^ 2) μ := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hH4) (hHm.pow 2) ?_
    filter_upwards [hH0] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact (osd_le_one_add_pow4 (H x)).2
  set cn : ℝ := (Fintype.card n : ℝ) with hcn
  have hcn0 : 0 ≤ cn := Nat.cast_nonneg _
  -- the scalar and matrix functions
  set fF : Matrix n n ℂ → ℂ := fun M => (w : ℂ) * (P * M).trace with hfF
  set UF : Matrix n n ℂ → Matrix n n ℂ := fun M => Q * M * Wt with hUF
  have hfFc : Continuous fF :=
    continuous_const.mul (continuous_const.matrix_mul continuous_id).matrix_trace
  have hUFc : Continuous UF := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hfFb : ∀ M : Matrix n n ℂ, ‖fF M‖ ≤ |w| * cn * ‖P‖ * ‖M‖ := fun M => by
    simp only [hfF, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have := (tfl_trace_le (P * M)).trans (mul_le_mul_of_nonneg_left (norm_mul_le P M) hcn0)
    calc |w| * ‖(P * M).trace‖ ≤ |w| * (cn * (‖P‖ * ‖M‖)) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = |w| * cn * ‖P‖ * ‖M‖ := by ring
  have hUFb : ∀ M : Matrix n n ℂ, ‖UF M‖ ≤ ‖Q‖ * ‖M * Wt‖ := fun M => by
    simp only [hUF, Matrix.mul_assoc]
    exact norm_mul_le _ _
  have hfUb : ∀ M : Matrix n n ℂ, ‖fF M • UF M‖ ≤ |w| * cn * ‖P‖ * ‖Q‖ * (‖M‖ * ‖M * Wt‖) :=
    fun M => by
      rw [norm_smul]
      calc ‖fF M‖ * ‖UF M‖ ≤ (|w| * cn * ‖P‖ * ‖M‖) * (‖Q‖ * ‖M * Wt‖) :=
            mul_le_mul (hfFb M) (hUFb M) (norm_nonneg _) (by positivity)
        _ = _ := by ring
  -- integrability at `κ = 0`
  have hf0i : Integrable (fun x => fF (G0 x)) μ := by
    refine Integrable.mono' (hH1.const_mul (|w| * cn * ‖P‖))
      (hfFc.comp_aestronglyMeasurable hG0m.aestronglyMeasurable) ?_
    filter_upwards [hlimb] with x hx
    exact (hfFb _).trans (mul_le_mul_of_nonneg_left hx.1 (by positivity))
  have hU0i : Integrable (fun x => UF (G0 x)) μ := by
    refine Integrable.mono' (hH1.const_mul ‖Q‖)
      (hUFc.comp_aestronglyMeasurable hG0m.aestronglyMeasurable) ?_
    filter_upwards [hlimb] with x hx
    exact (hUFb _).trans (mul_le_mul_of_nonneg_left hx.2 (norm_nonneg _))
  have hfU0i : Integrable (fun x => fF (G0 x) • UF (G0 x)) μ := by
    refine Integrable.mono' (hH2.const_mul (|w| * cn * ‖P‖ * ‖Q‖))
      ((hfFc.smul hUFc).comp_aestronglyMeasurable hG0m.aestronglyMeasurable) ?_
    filter_upwards [hlimb, hH0] with x hx h0
    refine (hfUb _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [sq]
    exact mul_le_mul hx.1 hx.2 (norm_nonneg _) h0
  refine ⟨hf0i, hU0i, hfU0i, ?_⟩
  -- convergence of the three integrals
  have hlim1 : Tendsto (fun m => ∫ x, fF (Gm m x) • UF (Gm m x) ∂μ) atTop
      (𝓝 (∫ x, fF (G0 x) • UF (G0 x) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |w| * cn * ‖P‖ * ‖Q‖ * H x ^ 2)
      (fun m => ((hfFc.smul hUFc).comp (hGmc m)).aestronglyMeasurable)
      (hH2.const_mul _) (fun m => ?_) ?_
    · filter_upwards [hHall, hH0] with x hx h0
      refine (hfUb _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      rw [sq]
      exact mul_le_mul (hx m).1 (hx m).2 (norm_nonneg _) h0
    · filter_upwards [hconv] with x hx
      exact ((hfFc.smul hUFc).tendsto _).comp hx
  have hlim2 : Tendsto (fun m => ∫ x, fF (Gm m x) ∂μ) atTop (𝓝 (∫ x, fF (G0 x) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |w| * cn * ‖P‖ * H x)
      (fun m => (hfFc.comp (hGmc m)).aestronglyMeasurable) (hH1.const_mul _) (fun m => ?_) ?_
    · filter_upwards [hHall] with x hx
      exact (hfFb _).trans (mul_le_mul_of_nonneg_left (hx m).1 (by positivity))
    · filter_upwards [hconv] with x hx
      exact (hfFc.tendsto _).comp hx
  have hlim3 : Tendsto (fun m => ∫ x, UF (Gm m x) ∂μ) atTop (𝓝 (∫ x, UF (G0 x) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖Q‖ * H x)
      (fun m => (hUFc.comp (hGmc m)).aestronglyMeasurable) (hH1.const_mul _) (fun m => ?_) ?_
    · filter_upwards [hHall] with x hx
      exact (hUFb _).trans (mul_le_mul_of_nonneg_left (hx m).2 (norm_nonneg _))
    · filter_upwards [hconv] with x hx
      exact (hUFc.tendsto _).comp hx
  have hlim := (hlim1.sub (hlim2.smul hlim3)).norm
  -- the bound at each `κ_m`
  have hbd : ∀ m, ‖(∫ x, fF (Gm m x) • UF (Gm m x) ∂μ) -
      (∫ x, fF (Gm m x) ∂μ) • ∫ x, UF (Gm m x) ∂μ‖ ≤
        |w| * γ * ‖P‖ * ‖Q‖ * ∫ x, H x ^ 4 ∂μ := by
    intro m
    have h := osd_cov_reg v hreg hγ hV w P Q Wt (hκpos m)
    have e : osdCov μ (coreF C0 L w P (κm m)) (fun x => Q * coreG C0 L (κm m) x * Wt) =
        (∫ x, fF (Gm m x) • UF (Gm m x) ∂μ) - (∫ x, fF (Gm m x) ∂μ) • ∫ x, UF (Gm m x) ∂μ :=
      rfl
    rw [e] at h
    refine h.trans ?_
    have hGb : ∀ x, ‖Gm m x‖ ≤ (κm m)⁻¹ := coreG_norm_le hreg (hκpos m)
    have hκi : 0 ≤ (κm m)⁻¹ := inv_nonneg.mpr (hκpos m).le
    have hi1 : Integrable (fun x => ‖Gm m x‖ ^ 4) μ :=
      Integrable.of_bound ((continuous_norm.comp (hGmc m)).pow 4).aestronglyMeasurable
        ((κm m)⁻¹ ^ 4) (ae_of_all _ fun x => by
          rw [Real.norm_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hGb x) 4)
    have hi2 : Integrable (fun x => (‖Gm m x‖ * ‖Gm m x * Wt‖) ^ 2) μ :=
      Integrable.of_bound (((continuous_norm.comp (hGmc m)).mul
        (continuous_norm.comp ((hGmc m).matrix_mul continuous_const))).pow 2).aestronglyMeasurable
        (((κm m)⁻¹ * ((κm m)⁻¹ * ‖Wt‖)) ^ 2)
        (ae_of_all _ fun x => by
          rw [Real.norm_of_nonneg (by positivity)]
          refine pow_le_pow_left₀ (by positivity) ?_ 2
          refine mul_le_mul (hGb x) ((norm_mul_le _ _).trans ?_) (norm_nonneg _) hκi
          exact mul_le_mul_of_nonneg_right (hGb x) (norm_nonneg _))
    have hm1 : ∫ x, ‖Gm m x‖ ^ 4 ∂μ ≤ ∫ x, H x ^ 4 ∂μ := by
      refine integral_mono_ae hi1 hH4 ?_
      filter_upwards [hHall] with x hx
      exact pow_le_pow_left₀ (norm_nonneg _) (hx m).1 4
    have hm2 : ∫ x, (‖Gm m x‖ * ‖Gm m x * Wt‖) ^ 2 ∂μ ≤ ∫ x, H x ^ 4 ∂μ := by
      refine integral_mono_ae hi2 hH4 ?_
      filter_upwards [hHall, hH0] with x hx h0
      have : ‖Gm m x‖ * ‖Gm m x * Wt‖ ≤ H x ^ 2 := by
        rw [sq]; exact mul_le_mul (hx m).1 (hx m).2 (norm_nonneg _) h0
      calc (‖Gm m x‖ * ‖Gm m x * Wt‖) ^ 2 ≤ (H x ^ 2) ^ 2 :=
            pow_le_pow_left₀ (by positivity) this 2
        _ = H x ^ 4 := by ring
    have hc : 0 ≤ |w| * γ * ‖P‖ * ‖Q‖ / 2 := by positivity
    calc |w| * γ * ‖P‖ * ‖Q‖ / 2 * ((∫ x, ‖coreG C0 L (κm m) x‖ ^ 4 ∂μ) +
          ∫ x, (‖coreG C0 L (κm m) x‖ * ‖coreG C0 L (κm m) x * Wt‖) ^ 2 ∂μ)
        ≤ |w| * γ * ‖P‖ * ‖Q‖ / 2 * ((∫ x, H x ^ 4 ∂μ) + ∫ x, H x ^ 4 ∂μ) :=
          mul_le_mul_of_nonneg_left (add_le_add hm1 hm2) hc
      _ = |w| * γ * ‖P‖ * ‖Q‖ * ∫ x, H x ^ 4 ∂μ := by ring
  exact le_of_tendsto' hlim hbd

end Generic

end BlockBand.Layers
