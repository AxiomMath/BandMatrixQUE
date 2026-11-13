module

public import BlockBand.Native.ErdosRiabov.VS.ResolventIto

set_option autoImplicit false

/-!
# Glue for Lemma `dG`: `Fin (p.n * p.W)` generator/bracket, complex bracket, adaptedness

* `generator_matrix_fin`, `bracket_matrix_fin`: the matrix generator and bracket identities of
  the band variance profile read on `Fin (p.n * p.W)` with the directions
  `ringMatrixFin p (e_i)` and the profile `S = shortRingProfile p.b p.n p.W`:
  `∑_i v_i B(E_i, E_i) = ∑_{a,b} S_ab B(e_ab, e_ba)`, `∑_i v_i |L E_i|² = ∑_{a,b} S_ab |L e_ab|²`.
* `chainDirLin`: the `ℂ`-linear direction functional `X ↦ tr(K · firstVar B R X)` of the
  complex chain `F = tr(K C)`; `chainBracket_add_im`: the brackets of `Re F` (weight `K`) and
  `Im F` (weight `-i K`) add up to the bracket density `d⟨𝓜, 𝓜̄⟩/dt`:
  `chainBracket K + chainBracket (-i K) = ∑_{a,b} S_ab |tr(K firstVar(R)[e_ab])|²`.
* `vsBandFin p t x = ringMatrixFin p (Y_t - Y_0)` (the matrix process on `Fin (p.n * p.W)`) :
  Hermitian, `H_0 = 0`, continuous paths; `stronglyMeasurable_vsBand(Fin)`,
  `isStronglyProgressive_vsBand(Fin)`: adapted and progressive for `driverAugmented μ`.
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
open BlockBand.Adapters.ErdosRiabov
open scoped NNReal

variable {p : BlockBand.Parameters} {k : ℕ}

/-! ### Generator and bracket on `Fin (p.n * p.W)` -/

theorem reindex_ringSiteEquiv_single (x y : p.Site) :
    reindex (ringSiteEquiv p) (ringSiteEquiv p) (single x y (1 : ℂ)) =
      single (ringSiteEquiv p x) (ringSiteEquiv p y) 1 := by
  simp [reindex_apply]

/-- Double sums over sites as double sums over `Fin (p.n * p.W)`. -/
theorem sum_sum_ringSiteEquiv {M : Type*} [AddCommMonoid M] (g : Fin (p.n * p.W) →
    Fin (p.n * p.W) → M) :
    ∑ x, ∑ y, g (ringSiteEquiv p x) (ringSiteEquiv p y) = ∑ a, ∑ b, g a b := by
  rw [← (ringSiteEquiv p).sum_comp]
  exact Finset.sum_congr rfl fun x _ => (ringSiteEquiv p).sum_comp (g (ringSiteEquiv p x))

/-- **Matrix generator on `Fin (p.n * p.W)`**: for every `ℂ`-bilinear `B`,
`∑_i v_i B(E_i, E_i) = ∑_{a,b} S_ab B(e_ab, e_ba)`, `E_i = ringMatrixFin p (e_i)`. -/
theorem generator_matrix_fin (B : RingMat p →ₗ[ℂ] RingMat p →ₗ[ℂ] ℂ) :
    ∑ i, (ringVariance p i : ℂ) *
        B (ringMatrixFin p (Pi.single i 1)) (ringMatrixFin p (Pi.single i 1)) =
      ∑ a, ∑ b, (shortRingProfile p.b p.n p.W a b : ℂ) * B (single a b 1) (single b a 1) := by
  set T := (reindexLinearEquiv ℂ ℂ (ringSiteEquiv p) (ringSiteEquiv p)).toLinearMap
  have h := generator_matrix p ((B.comp T).compl₂ T)
  simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, T, LinearEquiv.coe_coe,
    coe_reindexLinearEquiv, reindex_ringSiteEquiv_single] at h
  rw [← sum_sum_ringSiteEquiv]
  refine h.trans (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_)
  rw [shortRingProfile_ringSiteEquiv]

/-- **Matrix bracket on `Fin (p.n * p.W)`**: for every `ℂ`-linear `L`,
`∑_i v_i |L E_i|² = ∑_{a,b} S_ab |L e_ab|²`, `E_i = ringMatrixFin p (e_i)`. -/
theorem bracket_matrix_fin (L : RingMat p →ₗ[ℂ] ℂ) :
    ∑ i, ringVariance p i * ‖L (ringMatrixFin p (Pi.single i 1))‖ ^ 2 =
      ∑ a, ∑ b, shortRingProfile p.b p.n p.W a b * ‖L (single a b 1)‖ ^ 2 := by
  set T := (reindexLinearEquiv ℂ ℂ (ringSiteEquiv p) (ringSiteEquiv p)).toLinearMap
  have h := bracket_matrix p (L.comp T)
  simp only [LinearMap.comp_apply, T, LinearEquiv.coe_coe, coe_reindexLinearEquiv,
    reindex_ringSiteEquiv_single] at h
  rw [← sum_sum_ringSiteEquiv]
  refine h.trans (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_)
  rw [shortRingProfile_ringSiteEquiv]

/-! ### The complex chain bracket -/

/-- The `ℂ`-linear direction functional `X ↦ tr(K · firstVar B R X)`. -/
def chainDirLin {ι : Type} [Fintype ι] [DecidableEq ι] (B R : Fin k → Matrix ι ι ℂ)
    (K : Matrix ι ι ℂ) : Matrix ι ι ℂ →ₗ[ℂ] ℂ where
  toFun X := trace (K * firstVar B R X)
  map_add' X Y := by
    simp only [firstVar, slotProd_update, Matrix.mul_add, Matrix.add_mul,
      Finset.sum_add_distrib, trace_add]
  map_smul' c X := by
    simp only [firstVar, slotProd_update, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum,
      trace_smul, smul_eq_mul, RingHom.id_apply]

theorem chainDirLin_apply {ι : Type} [Fintype ι] [DecidableEq ι] (B R : Fin k → Matrix ι ι ℂ)
    (K X : Matrix ι ι ℂ) : chainDirLin B R K X = trace (K * firstVar B R X) := rfl

/-- **The complex chain bracket**: the bracket densities of `Re tr(K C)` and `Im tr(K C)` add up
to `∑_{a,b} S_ab |tr(K firstVar(R)[e_ab])|²` (the bracket density `d⟨𝓜, 𝓜̄⟩/dt`). -/
theorem chainBracket_add_im (A₀ : RingMat p) (zf : Fin k → ℝ → ℂ) (B : Fin k → RingMat p)
    (K : RingMat p) (t : ℝ) (y : Fin (ringDim p) → ℝ) :
    chainBracket A₀ zf B K t y + chainBracket A₀ zf B (-Complex.I • K) t y =
      ∑ a, ∑ b, shortRingProfile p.b p.n p.W a b *
        ‖trace (K * firstVar B (ringSlots A₀ zf t y) (single a b 1))‖ ^ 2 := by
  have h := bracket_matrix_fin (p := p) (chainDirLin B (ringSlots A₀ zf t y) K)
  simp only [chainDirLin_apply] at h
  rw [← h, chainBracket, chainBracket, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [reTr_neg_I_smul, reTr, Complex.sq_norm, Complex.normSq_apply]
  ring

/-! ### The matrix process on `Fin (p.n * p.W)` and adaptedness -/

variable (p) in
/-- The VS band process on `Fin (p.n * p.W)`: `H_t = ringMatrixFin p (Y_t - Y_0)`. -/
def vsBandFin (t : ℝ≥0) (x : RingSample p) : RingMat p := ringMatrixFin p (vsNoise p t x)

theorem vsBandFin_isHermitian (t : ℝ≥0) (x : RingSample p) : (vsBandFin p t x).IsHermitian :=
  ringMatrixFin_isHermitian _

theorem vsBandFin_zero (x : RingSample p) : vsBandFin p 0 x = 0 := by
  rw [vsBandFin, vsNoise_zero, map_zero]

theorem continuous_ringMatrixFin : Continuous (ringMatrixFin p) :=
  (LinearMap.toContinuousLinearMap (ringMatrixFin p)).continuous

theorem continuous_vsBandFin (x : RingSample p) : Continuous fun t => vsBandFin p t x :=
  continuous_ringMatrixFin.comp (continuous_vsNoise p x)

/-- `H_t` (site matrix) is `driverAugmented μ`-adapted. -/
theorem stronglyMeasurable_vsBand (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    (t : ℝ≥0) : StronglyMeasurable[driverAugmented (κ := Fin (ringDim p)) μ t] (vsBand p t) :=
  (continuous_ringMatrix p).comp_stronglyMeasurable
    ((isContinuousSemimartingale_vsNoise μ).adapted t)

/-- `H_t` (site matrix) is `driverAugmented μ`-progressive. -/
theorem isStronglyProgressive_vsBand (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] :
    IsStronglyProgressive (driverAugmented (κ := Fin (ringDim p)) μ) (vsBand p) := fun s =>
  (continuous_ringMatrix p).comp_stronglyMeasurable
    ((isContinuousSemimartingale_vsNoise μ).progressive s)

/-- `H_t` on `Fin (p.n * p.W)` is `driverAugmented μ`-adapted. -/
theorem stronglyMeasurable_vsBandFin (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    (t : ℝ≥0) :
    StronglyMeasurable[driverAugmented (κ := Fin (ringDim p)) μ t] (vsBandFin p t) :=
  continuous_ringMatrixFin.comp_stronglyMeasurable
    ((isContinuousSemimartingale_vsNoise μ).adapted t)

/-- `H_t` on `Fin (p.n * p.W)` is `driverAugmented μ`-progressive. -/
theorem isStronglyProgressive_vsBandFin (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] :
    IsStronglyProgressive (driverAugmented (κ := Fin (ringDim p)) μ) (vsBandFin p) := fun s =>
  continuous_ringMatrixFin.comp_stronglyMeasurable
    ((isContinuousSemimartingale_vsNoise μ).progressive s)

end BlockBand.Native.ErdosRiabov.VS
