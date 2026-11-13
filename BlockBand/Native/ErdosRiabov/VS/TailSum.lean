module

public import BlockBand.Native.ErdosRiabov.VS.ResolventItoGlue

set_option autoImplicit false

/-!
# Brackets of linear combinations of chain test functions

A time-dependent linear combination of chain test functions along the VS process is one continuous
semimartingale, and its bracket is computed in `d⟨𝓜, 𝓜̄⟩` form.

* `chainBracket_nonneg`.
* Time-dependent real linear combinations `linComb c φ (t, y) = ∑_α c_α(t) φ_α(t, y)` of `C²`
  test functions with `C²` coefficients: `partialSpace_linComb` (spatial partials are linear;
  the coefficients only depend on time), and `vsNoise_linComb_ito`: `linComb c φ (t, Y_t - Y_0)`
  is **one** continuous semimartingale with bracket density
  `∑_i v_i (∑_α c_α(t) ∂_i φ_α)²` (the bracket of the sum, not the sum of brackets).
* Complex combinations of chains: for chain data `(z_α, B_α, K_α)` of length `k` and
  `C²` coefficients `c_α : ℝ → ℂ`, `F(t, y) = ∑_α c_α(t) tr(K_α C_α(t, y))`
  (`chainComb`); `Re F = linComb … (combTestRe …)` and `Im F = linComb … (combTestIm …)`
  (`linComb_combTestRe`, `linComb_combTestIm`). `chainComb_ito_re`, `chainComb_ito_im`: `Re F`
  and `Im F` along `Y_t - Y_0` are continuous semimartingales with bracket densities
  `∑_i v_i (Re D_i)²`, `∑_i v_i (Im D_i)²`, `D_i = ∑_α c_α(t) tr(K_α firstVar_α[L e_i])`
  (`combDir`); and **`combBracket_re_add_im`**, the bracket in `d⟨𝓜, 𝓜̄⟩` form:
  `∑_i v_i (Re D_i)² + ∑_i v_i (Im D_i)² = ∑_{a,b} S_ab |∑_α c_α(t) tr(K_α firstVar_α[e_ab])|²`.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.VS
open MeasureTheory Set Matrix Function
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.CEH.Flow
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal

/-- The chain bracket density is nonnegative. -/
theorem chainBracket_nonneg {p : BlockBand.Parameters} {k : ℕ} (A₀ : RingMat p)
    (zf : Fin k → ℝ → ℂ) (B : Fin k → RingMat p) (K : RingMat p) (t : ℝ)
    (y : Fin (ringDim p) → ℝ) : 0 ≤ chainBracket A₀ zf B K t y :=
  Finset.sum_nonneg fun i _ => mul_nonneg (ringVariance_nonneg p i) (sq_nonneg _)

/-!
### Time-dependent linear combinations of test functions
-/

section LinComb

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- `linComb c φ (t, y) = ∑_α c_α(t) φ_α(t, y)`. -/
def linComb (c : ι → ℝ → ℝ) (φ : ι → ℝ × (Fin d → ℝ) → ℝ) (q : ℝ × (Fin d → ℝ)) : ℝ :=
  ∑ α, c α q.1 * φ α q

theorem hasFDerivAt_linComb {c : ι → ℝ → ℝ} {φ : ι → ℝ × (Fin d → ℝ) → ℝ}
    {q : ℝ × (Fin d → ℝ)} (hc : ∀ α, DifferentiableAt ℝ (c α) q.1)
    (hφ : ∀ α, DifferentiableAt ℝ (φ α) q) :
    HasFDerivAt (linComb c φ) (∑ α, (c α q.1 • fderiv ℝ (φ α) q +
      φ α q • (fderiv ℝ (c α) q.1).comp (ContinuousLinearMap.fst ℝ ℝ (Fin d → ℝ)))) q := by
  have h : ∀ α ∈ (Finset.univ : Finset ι), HasFDerivAt (fun q' => c α q'.1 * φ α q')
      (c α q.1 • fderiv ℝ (φ α) q +
        φ α q • (fderiv ℝ (c α) q.1).comp (ContinuousLinearMap.fst ℝ ℝ (Fin d → ℝ))) q :=
    fun α _ => ((hc α).hasFDerivAt.comp q hasFDerivAt_fst).mul (hφ α).hasFDerivAt
  exact HasFDerivAt.fun_sum h

/-- Spatial partials of a time-dependent linear combination are linear. -/
theorem partialSpace_linComb {c : ι → ℝ → ℝ} {φ : ι → ℝ × (Fin d → ℝ) → ℝ}
    {q : ℝ × (Fin d → ℝ)} (hc : ∀ α, DifferentiableAt ℝ (c α) q.1)
    (hφ : ∀ α, DifferentiableAt ℝ (φ α) q) (i : Fin d) :
    partialSpace (linComb c φ) q i = ∑ α, c α q.1 * partialSpace (φ α) q i := by
  rw [partialSpace, (hasFDerivAt_linComb hc hφ).fderiv]
  simp [partialSpace]

theorem contDiff_linComb {c : ι → ℝ → ℝ} {φ : ι → ℝ × (Fin d → ℝ) → ℝ}
    (hc : ∀ α, ContDiff ℝ 2 (c α)) (hφ : ∀ α, ContDiff ℝ 2 (φ α)) :
    ContDiff ℝ 2 (linComb c φ) :=
  ContDiff.sum fun α _ => ((hc α).comp contDiff_fst).mul (hφ α)

theorem measurable_linComb {c : ι → ℝ → ℝ} {φ : ι → ℝ × (Fin d → ℝ) → ℝ}
    (hc : ∀ α, Measurable (c α)) (hφ : ∀ α, Measurable (φ α)) : Measurable (linComb c φ) :=
  Finset.measurable_fun_sum _ fun α _ => ((hc α).comp measurable_fst).mul (hφ α)

end LinComb

section Ito

variable {p : BlockBand.Parameters} {ι : Type*} [Fintype ι]

/-- **One semimartingale for a linear combination.** For `C²` coefficients `c_α` and
Borel `C²` test functions `φ_α`, `linComb c φ (t, Y_t - Y_0)` is a continuous semimartingale with
drift `itoDrift (linComb c φ)` and bracket density `∑_i v_i (∑_α c_α(t) ∂_i φ_α)²`. -/
theorem vsNoise_linComb_ito (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    (c : ι → ℝ → ℝ) (φ : ι → ℝ × (Fin (ringDim p) → ℝ) → ℝ) (hc : ∀ α, ContDiff ℝ 2 (c α))
    (hφm : ∀ α, Measurable (φ α)) (hφ : ∀ α, ContDiff ℝ 2 (φ α)) :
    IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
      (driverAugmented (κ := Fin (ringDim p)) μ)
      (fun t x (_ : Fin 1) => linComb c φ ((t : ℝ), vsNoise p t x))
      (fun t x (_ : Fin 1) => itoDrift (linComb c φ) (vsNoise p t x) t 0
        (diagonal (ringVariance p)))
      (fun t x => Matrix.of fun (_ _ : Fin 1) => ∑ i, ringVariance p i *
        (∑ α, c α t * partialSpace (φ α) ((t : ℝ), vsNoise p t x) i) ^ 2) := by
  have H := vsNoise_itoFormula μ isOpen_univ (ae_of_all _ fun _ _ => Set.mem_univ _)
    (measurable_linComb (fun α => (hc α).continuous.measurable) hφm)
    (contDiff_linComb hc hφ).contDiffOn
  refine isContinuousSemimartingale_congr_data H rfl rfl ?_
  funext t x
  simp only [itoBracket_diagonal]
  congr 1
  funext _ _
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [partialSpace_linComb (fun α => ((hc α).differentiable (by norm_num)) _)
    (fun α => ((hφ α).differentiable (by norm_num)) _)]

end Ito

/-!
### Complex combinations of resolvent chains
-/

section Chains

variable {p : BlockBand.Parameters} {k : ℕ} {ι : Type*} [Fintype ι]

theorem reTr_I_smul {κ : Type} [Fintype κ] (K X : Matrix κ κ ℂ) :
    reTr (Complex.I • K) X = -(trace (K * X)).im := by
  simp [reTr, Matrix.smul_mul, trace_smul, Complex.mul_re]

/-- The complex chain combination `F(t, y) = ∑_α c_α(t) tr(K_α C_α(t, y))`. -/
def chainComb (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ) (B : ι → Fin k → RingMat p)
    (K : ι → RingMat p) (c : ι → ℝ → ℂ) (q : ℝ × (Fin (ringDim p) → ℝ)) : ℂ :=
  ∑ α, c α q.1 * trace (K α * resChain A₀ (ringMatrixFin p) (fun j => zf α j q.1) (B α) q.2)

/-- Real coefficients for `Re F`, `Im F`: `Re c_α` at `(α, false)`, `Im c_α` at `(α, true)`. -/
def combCoef (c : ι → ℝ → ℂ) : ι × Bool → ℝ → ℝ
  | (α, false) => fun t => (c α t).re
  | (α, true) => fun t => (c α t).im

/-- Test functions for `Re F`: weight `K_α` at `(α, false)`, `i K_α` at `(α, true)`. -/
def combTestRe (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ) (B : ι → Fin k → RingMat p)
    (K : ι → RingMat p) : ι × Bool → ℝ × (Fin (ringDim p) → ℝ) → ℝ
  | (α, false) => chainTestT A₀ (ringMatrixFin p) (zf α) (B α) (K α)
  | (α, true) => chainTestT A₀ (ringMatrixFin p) (zf α) (B α) (Complex.I • K α)

/-- Test functions for `Im F`: weight `-i K_α` at `(α, false)`, `K_α` at `(α, true)`. -/
def combTestIm (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ) (B : ι → Fin k → RingMat p)
    (K : ι → RingMat p) : ι × Bool → ℝ × (Fin (ringDim p) → ℝ) → ℝ
  | (α, false) => chainTestT A₀ (ringMatrixFin p) (zf α) (B α) (-Complex.I • K α)
  | (α, true) => chainTestT A₀ (ringMatrixFin p) (zf α) (B α) (K α)

theorem linComb_combTestRe (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ)
    (B : ι → Fin k → RingMat p) (K : ι → RingMat p) (c : ι → ℝ → ℂ)
    (q : ℝ × (Fin (ringDim p) → ℝ)) :
    linComb (combCoef c) (combTestRe A₀ zf B K) q = (chainComb A₀ zf B K c q).re := by
  rw [linComb, Fintype.sum_prod_type, chainComb, Complex.re_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Fintype.sum_bool]
  simp only [combCoef, combTestRe, chainTestT, chainTest, reTr_I_smul, Complex.mul_re]
  rw [reTr]
  ring

theorem linComb_combTestIm (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ)
    (B : ι → Fin k → RingMat p) (K : ι → RingMat p) (c : ι → ℝ → ℂ)
    (q : ℝ × (Fin (ringDim p) → ℝ)) :
    linComb (combCoef c) (combTestIm A₀ zf B K) q = (chainComb A₀ zf B K c q).im := by
  rw [linComb, Fintype.sum_prod_type, chainComb, Complex.im_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Fintype.sum_bool]
  simp only [combCoef, combTestIm, chainTestT, chainTest, reTr_neg_I_smul, Complex.mul_im]
  rw [reTr]
  ring

/-- The `ℂ`-linear direction functional of the combination at `(t, y)`:
`X ↦ ∑_α c_α(t) tr(K_α firstVar(R_α)[X])`. -/
def combDir (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ) (B : ι → Fin k → RingMat p)
    (K : ι → RingMat p) (c : ι → ℝ → ℂ) (t : ℝ) (y : Fin (ringDim p) → ℝ) :
    RingMat p →ₗ[ℂ] ℂ :=
  ∑ α, c α t • chainDirLin (B α) (ringSlots A₀ (zf α) t y) (K α)

theorem combDir_apply (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ) (B : ι → Fin k → RingMat p)
    (K : ι → RingMat p) (c : ι → ℝ → ℂ) (t : ℝ) (y : Fin (ringDim p) → ℝ) (X : RingMat p) :
    combDir A₀ zf B K c t y X =
      ∑ α, c α t * trace (K α * firstVar (B α) (ringSlots A₀ (zf α) t y) X) := by
  simp [combDir, chainDirLin_apply]

/-- Bracket density of `Re F`: `∑_i v_i (Re D_i)²`. -/
def combBracketRe (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ) (B : ι → Fin k → RingMat p)
    (K : ι → RingMat p) (c : ι → ℝ → ℂ) (t : ℝ) (y : Fin (ringDim p) → ℝ) : ℝ :=
  ∑ i, ringVariance p i * (combDir A₀ zf B K c t y (ringMatrixFin p (Pi.single i 1))).re ^ 2

/-- Bracket density of `Im F`: `∑_i v_i (Im D_i)²`. -/
def combBracketIm (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ) (B : ι → Fin k → RingMat p)
    (K : ι → RingMat p) (c : ι → ℝ → ℂ) (t : ℝ) (y : Fin (ringDim p) → ℝ) : ℝ :=
  ∑ i, ringVariance p i * (combDir A₀ zf B K c t y (ringMatrixFin p (Pi.single i 1))).im ^ 2

theorem combBracketRe_nonneg (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ)
    (B : ι → Fin k → RingMat p) (K : ι → RingMat p) (c : ι → ℝ → ℂ) (t : ℝ)
    (y : Fin (ringDim p) → ℝ) : 0 ≤ combBracketRe A₀ zf B K c t y :=
  Finset.sum_nonneg fun i _ => mul_nonneg (ringVariance_nonneg p i) (sq_nonneg _)

theorem combBracketIm_nonneg (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ)
    (B : ι → Fin k → RingMat p) (K : ι → RingMat p) (c : ι → ℝ → ℂ) (t : ℝ)
    (y : Fin (ringDim p) → ℝ) : 0 ≤ combBracketIm A₀ zf B K c t y :=
  Finset.sum_nonneg fun i _ => mul_nonneg (ringVariance_nonneg p i) (sq_nonneg _)

/-- **The bracket of the combination in `d⟨𝓜, 𝓜̄⟩` form:**
`∑_i v_i (Re D_i)² + ∑_i v_i (Im D_i)² = ∑_{a,b} S_ab |∑_α c_α(t) tr(K_α firstVar_α[e_ab])|²`. -/
theorem combBracket_re_add_im (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ)
    (B : ι → Fin k → RingMat p) (K : ι → RingMat p) (c : ι → ℝ → ℂ) (t : ℝ)
    (y : Fin (ringDim p) → ℝ) :
    combBracketRe A₀ zf B K c t y + combBracketIm A₀ zf B K c t y =
      ∑ a, ∑ b, shortRingProfile p.b p.n p.W a b *
        ‖combDir A₀ zf B K c t y (single a b 1)‖ ^ 2 := by
  rw [← bracket_matrix_fin, combBracketRe, combBracketIm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

variable {A₀ : RingMat p} (hA₀ : A₀.IsHermitian) {zf : ι → Fin k → ℝ → ℂ}
  (hzC : ∀ α j, ContDiff ℝ 2 (zf α j)) (hzim : ∀ α j t, (zf α j t).im ≠ 0)

omit [Fintype ι] in
include hA₀ hzC hzim in
theorem contDiff_chainTestT_ring (B : Fin k → RingMat p) (K : RingMat p) (α : ι) :
    ContDiff ℝ 2 (chainTestT A₀ (ringMatrixFin p) (zf α) B K) := by
  have h := contDiffOn_chainTestT A₀ (ringMatrixFin p) (zf α) B K (U := Set.univ)
    (fun t y _ j => isUnit_det_ring hA₀ (hzim α j t) y) (hzC α)
  rwa [Set.univ_prod_univ, contDiffOn_univ] at h

omit [Fintype ι] in
include hzC in
theorem measurable_chainTestT_ring (B : Fin k → RingMat p) (K : RingMat p) (α : ι) :
    Measurable (chainTestT A₀ (ringMatrixFin p) (zf α) B K) :=
  measurable_chainTestT A₀ _ (zf α) B K fun j => (hzC α j).continuous.measurable

omit [Fintype ι] in
include hA₀ hzC hzim in
theorem partialSpace_chainTestT_ring (B : Fin k → RingMat p) (K : RingMat p) (α : ι) (t : ℝ)
    (y : Fin (ringDim p) → ℝ) (i : Fin (ringDim p)) :
    partialSpace (chainTestT A₀ (ringMatrixFin p) (zf α) B K) (t, y) i =
      -(trace (K * firstVar B (ringSlots A₀ (zf α) t y) (ringMatrixFin p (Pi.single i 1)))).re :=
  partialSpace_chainTestT A₀ _ (zf α) B K (fun j => isUnit_det_ring hA₀ (hzim α j t) y)
    (fun j => ((hzC α j).differentiable (by norm_num)) t) i

include hA₀ hzC hzim in
/-- **`Re F` along the VS process** is one continuous semimartingale with bracket density
`combBracketRe` (`c_α` `C²`). -/
theorem chainComb_ito_re (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    (B : ι → Fin k → RingMat p) (K : ι → RingMat p) (c : ι → ℝ → ℂ)
    (hc : ∀ α, ContDiff ℝ 2 (c α)) :
    IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
      (driverAugmented (κ := Fin (ringDim p)) μ)
      (fun t x (_ : Fin 1) =>
        linComb (combCoef c) (combTestRe A₀ zf B K) ((t : ℝ), vsNoise p t x))
      (fun t x (_ : Fin 1) => itoDrift (linComb (combCoef c) (combTestRe A₀ zf B K))
        (vsNoise p t x) t 0 (diagonal (ringVariance p)))
      (fun t x => Matrix.of fun (_ _ : Fin 1) =>
        combBracketRe A₀ zf B K c t (vsNoise p t x)) := by
  have hcc : ∀ ab, ContDiff ℝ 2 (combCoef c ab) := fun
    | (α, false) => Complex.reCLM.contDiff.comp (hc α)
    | (α, true) => Complex.imCLM.contDiff.comp (hc α)
  have hT : ∀ ab, ContDiff ℝ 2 (combTestRe A₀ zf B K ab) := fun
    | (α, false) => contDiff_chainTestT_ring hA₀ hzC hzim (B α) (K α) α
    | (α, true) => contDiff_chainTestT_ring hA₀ hzC hzim (B α) (Complex.I • K α) α
  have hTm : ∀ ab, Measurable (combTestRe A₀ zf B K ab) := fun
    | (α, false) => measurable_chainTestT_ring hzC (B α) (K α) α
    | (α, true) => measurable_chainTestT_ring hzC (B α) (Complex.I • K α) α
  refine isContinuousSemimartingale_congr_data
    (vsNoise_linComb_ito μ (combCoef c) (combTestRe A₀ zf B K) hcc hTm hT) rfl rfl ?_
  funext t x
  congr 1
  funext _ _
  rw [combBracketRe]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hinner : ∑ ab, combCoef c ab t *
      partialSpace (combTestRe A₀ zf B K ab) ((t : ℝ), vsNoise p t x) i =
      -(combDir A₀ zf B K c t (vsNoise p t x) (ringMatrixFin p (Pi.single i 1))).re := by
    rw [Fintype.sum_prod_type, combDir_apply, Complex.re_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Fintype.sum_bool]
    simp only [combCoef, combTestRe, partialSpace_chainTestT_ring hA₀ hzC hzim, Matrix.smul_mul,
      trace_smul, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im]
    ring
  rw [hinner, neg_sq]

include hA₀ hzC hzim in
/-- **`Im F` along the VS process** is one continuous semimartingale with bracket density
`combBracketIm`. -/
theorem chainComb_ito_im (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    (B : ι → Fin k → RingMat p) (K : ι → RingMat p) (c : ι → ℝ → ℂ)
    (hc : ∀ α, ContDiff ℝ 2 (c α)) :
    IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
      (driverAugmented (κ := Fin (ringDim p)) μ)
      (fun t x (_ : Fin 1) =>
        linComb (combCoef c) (combTestIm A₀ zf B K) ((t : ℝ), vsNoise p t x))
      (fun t x (_ : Fin 1) => itoDrift (linComb (combCoef c) (combTestIm A₀ zf B K))
        (vsNoise p t x) t 0 (diagonal (ringVariance p)))
      (fun t x => Matrix.of fun (_ _ : Fin 1) =>
        combBracketIm A₀ zf B K c t (vsNoise p t x)) := by
  have hcc : ∀ ab, ContDiff ℝ 2 (combCoef c ab) := fun
    | (α, false) => Complex.reCLM.contDiff.comp (hc α)
    | (α, true) => Complex.imCLM.contDiff.comp (hc α)
  have hT : ∀ ab, ContDiff ℝ 2 (combTestIm A₀ zf B K ab) := fun
    | (α, false) => contDiff_chainTestT_ring hA₀ hzC hzim (B α) (-Complex.I • K α) α
    | (α, true) => contDiff_chainTestT_ring hA₀ hzC hzim (B α) (K α) α
  have hTm : ∀ ab, Measurable (combTestIm A₀ zf B K ab) := fun
    | (α, false) => measurable_chainTestT_ring hzC (B α) (-Complex.I • K α) α
    | (α, true) => measurable_chainTestT_ring hzC (B α) (K α) α
  refine isContinuousSemimartingale_congr_data
    (vsNoise_linComb_ito μ (combCoef c) (combTestIm A₀ zf B K) hcc hTm hT) rfl rfl ?_
  funext t x
  congr 1
  funext _ _
  rw [combBracketIm]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hinner : ∑ ab, combCoef c ab t *
      partialSpace (combTestIm A₀ zf B K ab) ((t : ℝ), vsNoise p t x) i =
      -(combDir A₀ zf B K c t (vsNoise p t x) (ringMatrixFin p (Pi.single i 1))).im := by
    rw [Fintype.sum_prod_type, combDir_apply, Complex.im_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Fintype.sum_bool]
    simp only [combCoef, combTestIm, partialSpace_chainTestT_ring hA₀ hzC hzim, Matrix.smul_mul,
      trace_smul, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [hinner, neg_sq]

end Chains

end BlockBand.Native.ErdosRiabov.VS
