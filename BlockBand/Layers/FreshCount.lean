module

public import BlockBand.Layers.FreshCountHeat
public import BlockBand.Model.Construction.SpectralEigenvalues

/-!
# The fresh-count lemma: the fresh Gaussian block count

The fresh-count lemma (`FreshCountContract`) for the law `A ~ GUE_W(c/W)`
(`gueMeasure (Fin W) ((1-2b)/W)`), a deterministic Hermitian `F` and real `E`.

* The fluctuation field of the contract: `freshCount_fluctuation` (module `FreshCountFluct`), proved with no
  hypothesis, `C_p = 2 e^{1/2} p`.
* The mean field of the contract. The proof of the paper splits as
  `E N_- - Θ_{z₀}(F) - (cW/2π) Im a² = [E N_- - E Θ^ε] + [E Θ^ε - Θ_{z₀+iε}(F) - (cW/2π) Im a²]
    + [Θ_{z₀+iε}(F) - Θ_{z₀}(F)]`, with `ε = W^{-3/5}` and the smoothed phase
  `Θ^ε(A) = π⁻¹ Σ_j arg(λ_j(A - E - F) + iε) = π⁻¹ Im Tr log(A - E - F + iε)`.
  - Smoothing ("replacing the smoothed phase by the sharp negative count costs
    `CWε log(2/ε)` in expectation"): `fc_smoothing_le`, from `ConditionalBlockGUECount`
    (the PSSS count, via `absorbedCount_factorialMoment` with one block):
    `|E N_- - E Θ^ε| ≤ (L+1)·4C/√c·Wε + Wε` whenever `2^L ε ≥ 1`.
  - Height removal: `fc_phaseCount_height_le` (module `FreshCountHeat`).
  - The heat interpolation itself (the heat derivative of the logarithm, the fresh count
    variance bound, the scalar branch and its stability, the
    comparison of `E g_t` with it and the integration in `t`) is the isolated input
    `FcHeatCore`: the bracket `E Θ^ε - Θ_{z₀+iε}(F) - (cW/2π) Im a²` at `ε = W^{-3/5}` is
    `O(W d² + W^{2/5} log 2W)` for `d ≤ d_*`. It is stated at exactly the measure, domain,
    quantifier order and uniformity of the contract.
  - Assembly: `freshCount_mean_of_heatCore (hcount) (hcore)`, and
    `freshCount_holds_of_heatCore (hcount) (hcore) : FreshCountContract`.
* The heat core itself is reduced (`fcHeatCore_of`) to two narrower inputs, with the
  integration in `t` proved (`fc_fence`, fencing inequality) and both endpoints identified
  (`fcHeatPhase_one`, `fcHeatPhase_zero`):
  - `FcHeatDerivative`: `Φ(t) = π⁻¹ Im E Tr log H_t` is continuous on `[0,1]` with right
    derivative `(cW/2π) Im a² - (cW/2π) Im E(g_t - a)²` (the fresh log-heat identity);
  - `FcMeanSquare`: `E|g_t - a|² ≤ C(d² + ε² + W⁻² y_t⁻³)` for `d ≤ d_*`, `ε = W^{-3/5}`.
  `freshCount_holds_of_heat (hcount) (hder) (hms) : FreshCountContract`.

`FcHeatDerivative` and `FcMeanSquare` (equivalently the stronger packaging `FcHeatCore`) are
hypotheses here (proved as `fcHeatDerivative_holds` and `fcMeanSquare_holds`).
`Inputs.GaussianLpGradient` is not used in this file.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Complex
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (ConditionalBlockGUECount spectralSum)
open BlockBand.External
open scoped NNReal ENNReal Topology

/-!
## 1. Measurable spectral sums
-/

section SpectralMeas

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem fc_spectralSum_eq_raw {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (f : ℝ → ℝ) :
    spectralSum M f =
      ∑ i : Fin (Fintype.card ι), f (BlockBand.Model.Construction.rawIncreasingEigenvalue i M) := by
  unfold spectralSum
  rw [hM.roots_charpoly_eq_eigenvalues₀, Multiset.map_map, Finset.sum_eq_multiset_sum]
  simp only [BlockBand.Model.Construction.rawIncreasingEigenvalue_eq _ _ hM,
    BlockBand.Foundations.Spectral.increasingEigenvalue]
  exact (Equiv.sum_comp Fin.revPerm (fun j => f (hM.eigenvalues₀ j))).symm

/-- A spectral sum of a measurable function along a measurable Hermitian family. -/
theorem fc_measurable_spectralSum {Ω : Type*} [MeasurableSpace Ω] {M : Ω → Matrix ι ι ℂ}
    (hM : Measurable M) (hH : ∀ ω, (M ω).IsHermitian) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable fun ω => spectralSum (M ω) f := by
  have : (fun ω => spectralSum (M ω) f) = fun ω => ∑ i : Fin (Fintype.card ι),
      f (BlockBand.Model.Construction.rawIncreasingEigenvalue i (M ω)) := by
    funext ω; exact fc_spectralSum_eq_raw (hH ω) f
  rw [this]
  exact Finset.measurable_sum _ fun i _ =>
    hf.comp ((BlockBand.Model.Construction.measurable_rawIncreasingEigenvalue i).comp hM)

theorem fc_abs_spectralSum_le {M : Matrix ι ι ℂ} (hM : M.IsHermitian) {f : ℝ → ℝ} {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) : |spectralSum M f| ≤ Fintype.card ι * B := by
  rw [fc_spectralSum_eq hM]
  calc |∑ k, f (hM.eigenvalues k)| ≤ ∑ k, |f (hM.eigenvalues k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : ι, B := Finset.sum_le_sum fun k _ => hf _
    _ = Fintype.card ι * B := by rw [Finset.sum_const, nsmul_eq_mul]; rfl

theorem fc_negativeCount_eq_spectralSum {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    (negativeCount M : ℝ) = spectralSum M fcNegInd := by
  rw [fc_spectralSum_eq hM, negativeCount_of_isHermitian hM]
  simp only [fcNegInd]
  rw [Finset.sum_boole]

end SpectralMeas

theorem fc_measurable_negInd : Measurable fcNegInd := by
  unfold fcNegInd
  exact Measurable.ite measurableSet_Iio measurable_const measurable_const

theorem fc_measurable_smoothInd (ε : ℝ) : Measurable (fcSmoothInd ε) := by
  unfold fcSmoothInd
  have : Measurable fun x : ℝ => (x : ℂ) + (ε : ℂ) * I := by fun_prop
  exact (Complex.measurable_arg.comp this).div_const _

theorem fc_measurable_ball (r : ℝ) : Measurable (fcBall r) := by
  unfold fcBall
  exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    measurable_const measurable_const

theorem fc_abs_negInd_le (x : ℝ) : |fcNegInd x| ≤ 1 := by
  unfold fcNegInd; split_ifs <;> simp

theorem fc_abs_smoothInd_le {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) : |fcSmoothInd ε x| ≤ 1 := by
  have h := fcSmoothInd_mem hε x
  rw [abs_le]; constructor <;> linarith [h.1, h.2]

theorem fc_abs_ball_le (r x : ℝ) : |fcBall r x| ≤ 1 := by
  unfold fcBall; split_ifs <;> simp

/-!
## 2. The expected eigenvalue density (PSSS, one block)
-/

/-- The Hermitian-part shift `herm(A) - E - F`, Hermitian for every `A`. -/
def fcShift {W : ℕ} (E : ℝ) (F : Matrix (Fin W) (Fin W) ℂ) (A : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  hermPart A - (E : ℂ) • 1 - F

theorem fcShift_isHermitian {W : ℕ} (E : ℝ) {F : Matrix (Fin W) (Fin W) ℂ} (hF : F.IsHermitian)
    (A : Matrix (Fin W) (Fin W) ℂ) : (fcShift E F A).IsHermitian :=
  fc_isHermitian_shift (hermPart_isHermitian A) hF E

theorem continuous_fcShift {W : ℕ} (E : ℝ) (F : Matrix (Fin W) (Fin W) ℂ) :
    Continuous (fcShift E F) := by
  unfold fcShift
  have : Continuous (hermPart (ι := Fin W)) := by
    unfold hermPart
    have h1 : Continuous fun A : Matrix (Fin W) (Fin W) ℂ => A + Aᴴ :=
      continuous_id.add continuous_id.matrix_conjTranspose
    exact (continuous_const (y := (1 / 2 : ℂ))).smul h1
  exact (this.sub continuous_const).sub continuous_const

theorem measurable_fcShift {W : ℕ} (E : ℝ) (F : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (fcShift E F) :=
  (continuous_fcShift E F).measurable

theorem fcShift_ae_eq {W : ℕ} (t : ℝ≥0) (E : ℝ) (F : Matrix (Fin W) (Fin W) ℂ) :
    ∀ᵐ A ∂gueMeasure (Fin W) t, A - (E : ℂ) • 1 - F = fcShift E F A := by
  filter_upwards [fc_ae_isHermitian_gue W t] with A hA
  rw [fcShift, hermPart_of_isHermitian hA]

/-- The deterministic `X = F` of `absorbedMatrix`, on one block. -/
def fcOneBlock {W : ℕ} {F : Matrix (Fin W) (Fin W) ℂ} (hF : F.IsHermitian) :
    PSSS.HermitianMatrix (Fin 1 × Fin W) :=
  ⟨F.submatrix Prod.snd Prod.snd, hF.submatrix Prod.snd⟩

theorem fc_absorbedMatrix_oneBlock {W : ℕ} (E : ℝ) {F : Matrix (Fin W) (Fin W) ℂ}
    (hF : F.IsHermitian) (A : Matrix (Fin W) (Fin W) ℂ) :
    absorbedMatrix E (fcOneBlock hF) (fun _ : Fin 1 => A) =
      Counting.hermitianReindex (Equiv.uniqueProd (Fin W) (Fin 1)).symm
        ⟨fcShift E F A, fcShift_isHermitian E hF A⟩ := by
  apply Subtype.ext
  ext ⟨i₁, i⟩ ⟨j₁, j⟩
  have hij : i₁ = j₁ := Subsingleton.elim _ _
  subst hij
  simp [absorbedMatrix, Counting.hermitianReindex, fcShift, fcOneBlock,
    Internal.Contracts.Layers.blockDiag, hermBlocks, Matrix.one_apply]

/-- `#{j : λ_j(herm A - E - F) ∈ J}` as a spectral sum of an indicator. -/
theorem fc_absorbedCount_oneBlock {W : ℕ} (E : ℝ) {F : Matrix (Fin W) (Fin W) ℂ}
    (hF : F.IsHermitian) (r : ℝ) (A : Matrix (Fin W) (Fin W) ℂ) :
    (absorbedCount E (fcOneBlock hF) (Set.Icc (-r) r) (fun _ : Fin 1 => A) : ℝ) =
      spectralSum (fcShift E F A) (fcBall r) := by
  unfold absorbedCount
  rw [fc_absorbedMatrix_oneBlock, Counting.nativeEigenCount_hermitianReindex,
    eigenCount_eq_card_eigenvalues, fc_spectralSum_eq (fcShift_isHermitian E hF A)]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [fcBall, Set.mem_Icc, ← abs_le]
  rw [Finset.sum_boole]

/-- **Expected eigenvalue density** (the external count theorem, one block): with `C` the PSSS
constant, for `W ≥ 1`, `c > 0`, real `E`, Hermitian `F`, `r ≥ 0`, under `GUE_W(c/W)`:
`E #{j : |λ_j(A - E - F)| ≤ r} ≤ C/√c · W · 2r`, and the count is integrable. -/
theorem fc_ballCount_le (hcount : ConditionalBlockGUECount) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ), 0 < W → ∀ c : ℝ, 0 < c → ∀ (E : ℝ)
      (F : Matrix (Fin W) (Fin W) ℂ), F.IsHermitian → ∀ r : ℝ, 0 ≤ r →
      (∫ A, spectralSum (fcShift E F A) (fcBall r) ∂gueMeasure (Fin W) (Real.toNNReal (c / W))) ≤
        C / Real.sqrt c * W * (2 * r) := by
  obtain ⟨C, hC, h⟩ := absorbedCount_factorialMoment hcount
  refine ⟨C, hC, fun W hW c hc E F hF r hr => ?_⟩
  obtain ⟨_, hbd⟩ := h 1 W hW c hc E (fcOneBlock hF) (-r) r (by linarith) 1 le_rfl
  set μ := gueMeasure (Fin W) (Real.toNNReal (c / W)) with hμ
  have hint : ∫ A, PSSS.factorialCount (absorbedCount E (fcOneBlock hF) (Set.Icc (-r) r)) 1 A
      ∂(blockLaw 1 W c) = ∫ A, spectralSum (fcShift E F A) (fcBall r) ∂μ := by
    rw [← (measurePreserving_funUnique μ (Fin 1)).integral_comp']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hx : x = fun _ : Fin 1 => x default := funext fun i => by rw [Subsingleton.elim i default]
    simp only [PSSS.factorialCount, Nat.descFactorial_one]
    rw [hx, fc_absorbedCount_oneBlock E hF r (x default)]
    rfl
  rw [hint] at hbd
  calc _ ≤ (C / Real.sqrt c * ((1 : ℕ) * W) * (r - -r)) ^ 1 := hbd
    _ = C / Real.sqrt c * W * (2 * r) := by push_cast; ring

/-!
## 3. Sharp count versus smoothed phase
-/

/-- Pointwise dyadic domination of `|N_- - Θ^ε|` by eigenvalue counts in dyadic windows. -/
theorem fc_count_sub_smooth_le {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) {ε : ℝ} (hε : 0 < ε) {L : ℕ} (hL : 1 ≤ 2 ^ L * ε) :
    |spectralSum M fcNegInd - spectralSum M (fcSmoothInd ε)| ≤
      (∑ m ∈ Finset.range (L + 1), 2 / 2 ^ m * spectralSum M (fcBall (2 ^ m * ε))) +
        Fintype.card ι * ε := by
  simp only [fc_spectralSum_eq hM, ← Finset.sum_sub_distrib, Finset.mul_sum]
  calc |∑ k, (fcNegInd (hM.eigenvalues k) - fcSmoothInd ε (hM.eigenvalues k))|
      ≤ ∑ k, |fcNegInd (hM.eigenvalues k) - fcSmoothInd ε (hM.eigenvalues k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ((∑ m ∈ Finset.range (L + 1), 2 / 2 ^ m * fcBall (2 ^ m * ε) (hM.eigenvalues k))
          + ε) := Finset.sum_le_sum fun k _ => fc_kernel_le_dyadic hε hL _
    _ = (∑ m ∈ Finset.range (L + 1), ∑ k, 2 / 2 ^ m * fcBall (2 ^ m * ε) (hM.eigenvalues k)) +
          Fintype.card ι * ε := by
        rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_const, nsmul_eq_mul]
        rfl

/-- **Sharp count versus smoothed phase**, from `ConditionalBlockGUECount`. With `C` the PSSS
constant: for `W ≥ 1`, `c > 0`, real `E`, Hermitian `F`, `ε > 0` and `L` with `2^L ε ≥ 1`, under
`GUE_W(c/W)`:
`|E N_-(A - E - F) - E π⁻¹ Σ_j arg(λ_j(A - E - F) + iε)| ≤ (L+1)·4C/√c·Wε + Wε`. -/
theorem fc_smoothing_le (hcount : ConditionalBlockGUECount) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ), 0 < W → ∀ c : ℝ, 0 < c → ∀ (E : ℝ)
      (F : Matrix (Fin W) (Fin W) ℂ), F.IsHermitian → ∀ ε : ℝ, 0 < ε → ∀ L : ℕ,
      1 ≤ 2 ^ L * ε →
      |(∫ A, (negativeCount (A - (E : ℂ) • 1 - F) : ℝ)
          ∂gueMeasure (Fin W) (Real.toNNReal (c / W))) -
        ∫ A, spectralSum (A - (E : ℂ) • 1 - F) (fcSmoothInd ε)
          ∂gueMeasure (Fin W) (Real.toNNReal (c / W))| ≤
        (L + 1) * (4 * (C / Real.sqrt c) * W * ε) + W * ε := by
  obtain ⟨C, hC, hball⟩ := fc_ballCount_le hcount
  refine ⟨C, hC, fun W hW c hc E F hF ε hε L hL => ?_⟩
  set μ := gueMeasure (Fin W) (Real.toNNReal (c / W)) with hμ
  have hH := fcShift_isHermitian E hF
  have hMm := measurable_fcShift E F
  have h1 : (∫ A, (negativeCount (A - (E : ℂ) • 1 - F) : ℝ) ∂μ) =
      ∫ A, spectralSum (fcShift E F A) fcNegInd ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [fcShift_ae_eq (Real.toNNReal (c / W)) E F] with A hA
    rw [hA, fc_negativeCount_eq_spectralSum (hH A)]
  have h2 : (∫ A, spectralSum (A - (E : ℂ) • 1 - F) (fcSmoothInd ε) ∂μ) =
      ∫ A, spectralSum (fcShift E F A) (fcSmoothInd ε) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [fcShift_ae_eq (Real.toNNReal (c / W)) E F] with A hA
    rw [hA]
  have hcard : (Fintype.card (Fin W) : ℝ) = W := by simp
  have hint : ∀ f : ℝ → ℝ, Measurable f → (∀ x, |f x| ≤ 1) →
      Integrable (fun A => spectralSum (fcShift E F A) f) μ := by
    intro f hf hf1
    refine fc_integrable_of_bound (fc_measurable_spectralSum hMm hH hf) (W * 1) fun A => ?_
    have := fc_abs_spectralSum_le (hH A) hf1
    rwa [hcard] at this
  have hN := hint _ fc_measurable_negInd fc_abs_negInd_le
  have hS := hint _ (fc_measurable_smoothInd ε) (fc_abs_smoothInd_le hε.le)
  have hB : ∀ m : ℕ, Integrable (fun A => spectralSum (fcShift E F A) (fcBall (2 ^ m * ε))) μ :=
    fun m => hint _ (fc_measurable_ball _) (fc_abs_ball_le _)
  rw [h1, h2, ← integral_sub hN hS]
  have hdom : Integrable (fun A => (∑ m ∈ Finset.range (L + 1),
      2 / 2 ^ m * spectralSum (fcShift E F A) (fcBall (2 ^ m * ε))) + W * ε) μ :=
    (integrable_finsetSum _ fun m _ => (hB m).const_mul _).add (integrable_const _)
  calc |∫ A, (spectralSum (fcShift E F A) fcNegInd - spectralSum (fcShift E F A) (fcSmoothInd ε))
        ∂μ|
      ≤ ∫ A, |spectralSum (fcShift E F A) fcNegInd -
          spectralSum (fcShift E F A) (fcSmoothInd ε)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ A, ((∑ m ∈ Finset.range (L + 1),
          2 / 2 ^ m * spectralSum (fcShift E F A) (fcBall (2 ^ m * ε))) + W * ε) ∂μ := by
        refine integral_mono (hN.sub hS).abs hdom fun A => ?_
        have := fc_count_sub_smooth_le (hH A) hε hL
        rwa [hcard] at this
    _ = (∑ m ∈ Finset.range (L + 1),
          2 / 2 ^ m * ∫ A, spectralSum (fcShift E F A) (fcBall (2 ^ m * ε)) ∂μ) + W * ε := by
        rw [integral_add (integrable_finsetSum _ fun m _ => (hB m).const_mul _)
          (integrable_const _), integral_finsetSum _ fun m _ => (hB m).const_mul _]
        simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
    _ ≤ (∑ m ∈ Finset.range (L + 1),
          2 / 2 ^ m * (C / Real.sqrt c * W * (2 * (2 ^ m * ε)))) + W * ε := by
        gcongr with m hm
        exact hball W hW c hc E F hF _ (by positivity)
    _ = (L + 1) * (4 * (C / Real.sqrt c) * W * ε) + W * ε := by
        congr 1
        rw [Finset.sum_congr rfl fun m _ => show 2 / 2 ^ m * (C / Real.sqrt c * W *
            (2 * (2 ^ m * ε))) = 4 * (C / Real.sqrt c) * W * ε by field_simp; ring]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast; ring

/-!
## 4. Scalar bookkeeping for `ε = W^{-3/5}`
-/

/-- The height `ε = W^{-3/5}` of the proof. -/
def fcHeight (W : ℕ) : ℝ := (W : ℝ) ^ (-(3 / 5 : ℝ))

theorem fcHeight_pos {W : ℕ} (hW : 0 < W) : 0 < fcHeight W :=
  Real.rpow_pos_of_pos (by exact_mod_cast hW) _

theorem fc_mul_height {W : ℕ} (hW : 0 < W) : (W : ℝ) * fcHeight W = (W : ℝ) ^ (2 / 5 : ℝ) := by
  have hWp : (0 : ℝ) < W := by exact_mod_cast hW
  unfold fcHeight
  conv_lhs => arg 1; rw [← Real.rpow_one (W : ℝ)]
  rw [← Real.rpow_add hWp]
  norm_num

theorem fc_one_le_rpow {W : ℕ} (hW : 0 < W) : 1 ≤ (W : ℝ) ^ (2 / 5 : ℝ) :=
  Real.one_le_rpow (by exact_mod_cast hW) (by norm_num)

theorem fc_one_le_dyadic {W : ℕ} (hW : 0 < W) :
    1 ≤ 2 ^ (Nat.log 2 W + 1) * fcHeight W := by
  have h1 : (W : ℝ) ≤ 2 ^ (Nat.log 2 W + 1) := by
    have := (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) W).le
    exact_mod_cast this
  calc (1 : ℝ) ≤ (W : ℝ) ^ (2 / 5 : ℝ) := fc_one_le_rpow hW
    _ = W * fcHeight W := (fc_mul_height hW).symm
    _ ≤ 2 ^ (Nat.log 2 W + 1) * fcHeight W :=
        mul_le_mul_of_nonneg_right h1 (fcHeight_pos hW).le

theorem fc_log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem fc_log_two_le {W : ℕ} (hW : 0 < W) : Real.log 2 ≤ Real.log (2 * W) := by
  refine Real.log_le_log (by norm_num) ?_
  have : (1 : ℝ) ≤ W := by exact_mod_cast hW
  linarith

/-- `L + 1 = Nat.log 2 W + 2 ≤ 3 log(2W) / log 2`. -/
theorem fc_dyadic_count_le {W : ℕ} (hW : 0 < W) :
    (((Nat.log 2 W + 1 : ℕ) : ℝ) + 1) ≤ 3 * Real.log (2 * W) / Real.log 2 := by
  have hl := fc_log_two_pos
  have h1 : (Nat.log 2 W : ℝ) ≤ Real.log W / Real.log 2 := by
    have := Real.natLog_le_logb W 2
    simpa [Real.logb] using this
  have hWp : (0 : ℝ) < W := by exact_mod_cast hW
  have h2 : Real.log W ≤ Real.log (2 * W) := Real.log_le_log hWp (by linarith)
  have h3 := fc_log_two_le hW
  rw [le_div_iff₀ hl]
  have h1' : (Nat.log 2 W : ℝ) * Real.log 2 ≤ Real.log W := by
    rwa [le_div_iff₀ hl] at h1
  push_cast
  nlinarith

/-!
## 5. The heat-interpolation core and the assembly
-/

/-- **Input: the heat interpolation of the fresh-count lemma**. With
`ε = W^{-3/5}`, `H_t = √t A - E - F - (1-t)ca + iε` and the upper-half-plane logarithm, the
bracket `π⁻¹ Im (E Tr log H_1 - Tr log H_0) - (cW/2π) Im a²` is `O(W d² + W^{2/5} log 2W)` for
`d ≤ d_*`. Here `π⁻¹ Im Tr log H_1 = π⁻¹ Σ_j arg(λ_j(A - E - F) + iε)` (`fcSmoothInd`) and
`π⁻¹ Im Tr log H_0 = Θ_{z₀+iε}(F)`. In the paper this follows from the heat derivative
`d/dt E Tr log H_t = cW E(a g_t - g_t²/2)` (the fresh log-heat identity), the variance bound
`E|g_t - E g_t|² ≤ C/(W² y_t³)` (Gaussian Poincaré and the counting bound), the stable scalar
branch `m_t` within `C(d+ε)` of `a`, the comparison `|E g_t - a| ≤ C(d + ε + W⁻² y_t⁻³)` by
Gaussian integration by parts and continuation from `t = 0`, and the integration in `t`
(cost `C(Wd² + Wε² + (Wε²)⁻¹) ≤ C(Wd² + W^{1/5})`). Same law (`GUE_W(c/W)`, `c = 1-2b`),
domain (`E ∈ bulkInterval κ`, Hermitian `F` of any norm, `W ≥ 1`) and quantifier order
(`b, κ`, then `d_*, C`) as `FreshCountContract.mean`. Not proved here. -/
def FcHeatCore : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ dstar C : ℝ, 0 < dstar ∧
      ∀ (W : ℕ), 0 < W → ∀ F : Matrix (Fin W) (Fin W) ℂ, F.IsHermitian →
      ∀ E ∈ bulkInterval κ,
        let a := matchedA E
        let z₀ : ℂ := -(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * a
        let d := ‖(W : ℂ)⁻¹ * ((z₀ • 1 - F)⁻¹).trace - a‖
        d ≤ dstar →
          |(∫ A, spectralSum (A - (E : ℂ) • 1 - F) (fcSmoothInd (fcHeight W))
              ∂gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) -
            phaseCount (z₀ + (fcHeight W : ℂ) * I) F -
            (1 - 2 * b) * W / (2 * Real.pi) * (a ^ 2).im| ≤
            C * (W * d ^ 2 + (W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * W))

/-- `Im z₀ = -c Im a ≥ c √(4 - (2-κ')²)/2 > 0` on `bulkInterval κ`, `κ' = min κ 2`. -/
theorem fc_z0_im_ge {b κ E : ℝ} (hb : b < 1 / 2) (hE : E ∈ bulkInterval κ) :
    (1 - 2 * b) * (Real.sqrt (4 - (2 - min κ 2) ^ 2) / 2) ≤
      (-(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * matchedA E).im := by
  have hE' : E ∈ bulkInterval (min κ 2) := by
    have h1 := hE.1; have h2 := hE.2
    have : min κ 2 ≤ κ := min_le_left _ _
    exact ⟨by linarith, by linarith⟩
  have him := matchedA_im_le_of_mem_bulkInterval hE'
  have hc : 0 < 1 - 2 * b := by linarith
  have : (-(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * matchedA E).im = -(1 - 2 * b) * (matchedA E).im := by
    simp only [sub_im, neg_im, ofReal_im, mul_im, ofReal_re, zero_mul, add_zero]
    ring
  rw [this]
  nlinarith

theorem fc_bulk_delta_pos {b κ : ℝ} (hb : b < 1 / 2) (hκ : 0 < κ) :
    0 < (1 - 2 * b) * (Real.sqrt (4 - (2 - min κ 2) ^ 2) / 2) := by
  have hc : 0 < 1 - 2 * b := by linarith
  have hk0 : 0 < min κ 2 := lt_min hκ (by norm_num)
  have hk4 : min κ 2 < 4 := (min_le_right _ _).trans_lt (by norm_num)
  have := Real.sqrt_pos.mpr (four_sub_sq_pos hk0 hk4)
  positivity

/-- **The fresh-count lemma, mean field, from the heat core.** The fresh count bound follows from
`ConditionalBlockGUECount` (sharp count versus smoothed phase) and the hypothesis `FcHeatCore`
(heat interpolation), with the deterministic height removal. -/
theorem freshCount_mean_of_heatCore (hcount : ConditionalBlockGUECount) (hcore : FcHeatCore) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ dstar C : ℝ, 0 < dstar ∧
      ∀ (W : ℕ), 0 < W → ∀ F : Matrix (Fin W) (Fin W) ℂ, F.IsHermitian →
      ∀ E ∈ bulkInterval κ,
        let a := matchedA E
        let z₀ : ℂ := -(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * a
        let d := ‖(W : ℂ)⁻¹ * ((z₀ • 1 - F)⁻¹).trace - a‖
        d ≤ dstar →
          |(∫ A, (negativeCount (A - (E : ℂ) • 1 - F) : ℝ)
              ∂gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) - phaseCount z₀ F -
            (1 - 2 * b) * W / (2 * Real.pi) * (a ^ 2).im| ≤
            C * (W * d ^ 2 + (W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * W)) := by
  intro b hb0 hb κ hκ
  obtain ⟨dstar, CH, hdstar, hH⟩ := hcore b hb0 hb κ hκ
  obtain ⟨CS, hCS, hS⟩ := fc_smoothing_le hcount
  set c := 1 - 2 * b with hc
  have hcpos : 0 < c := by linarith
  set δ := c * (Real.sqrt (4 - (2 - min κ 2) ^ 2) / 2) with hδ
  have hδpos : 0 < δ := fc_bulk_delta_pos hb hκ
  set lam := Real.log 2 with hlam
  have hlam0 : 0 < lam := fc_log_two_pos
  set K := 12 * (CS / Real.sqrt c) / lam + 1 / lam + 1 / (δ * lam) with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ CS / Real.sqrt c := div_nonneg hCS.le (Real.sqrt_nonneg _)
    positivity
  refine ⟨dstar, |CH| + K, hdstar, fun W hW F hF E hE => ?_⟩
  intro a z₀ d hd
  have hcore' := hH W hW F hF E hE hd
  set ε := fcHeight W with hε
  have hεpos : 0 < ε := fcHeight_pos hW
  set L := Nat.log 2 W + 1 with hL
  have hsm := hS W hW c hcpos E F hF ε hεpos L (fc_one_le_dyadic hW)
  have hz0 : δ ≤ z₀.im := fc_z0_im_ge hb hE
  have hht := fc_phaseCount_height_le hF (lt_of_lt_of_le hδpos hz0) hεpos.le (z := z₀)
  simp only [Fintype.card_fin] at hht
  set P := (W : ℝ) ^ (2 / 5 : ℝ) with hP
  set ℓ := Real.log (2 * W) with hℓ
  have hWε : (W : ℝ) * ε = P := fc_mul_height hW
  have hP1 : 1 ≤ P := fc_one_le_rpow hW
  have hℓlam : lam ≤ ℓ := fc_log_two_le hW
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hlam0 hℓlam
  have hLcount := fc_dyadic_count_le hW
  have hd2 : 0 ≤ (W : ℝ) * d ^ 2 := by positivity
  -- the three pieces
  set X := (1 - 2 * b) * W / (2 * Real.pi) * (a ^ 2).im with hX
  set EN := ∫ A, (negativeCount (A - (E : ℂ) • 1 - F) : ℝ)
    ∂gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W)) with hEN
  set ES := ∫ A, spectralSum (A - (E : ℂ) • 1 - F) (fcSmoothInd ε)
    ∂gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W)) with hES
  -- piece 1: smoothing
  have hT1 : |EN - ES| ≤ (12 * (CS / Real.sqrt c) / lam + 1 / lam) * (P * ℓ) := by
    have hcs : 0 ≤ CS / Real.sqrt c := div_nonneg hCS.le (Real.sqrt_nonneg _)
    have e1 : ((L : ℝ) + 1) * (4 * (CS / Real.sqrt c) * W * ε) + W * ε =
        ((L : ℝ) + 1) * (4 * (CS / Real.sqrt c)) * P + P := by
      rw [← hWε]; ring
    have e2 : ((L : ℝ) + 1) * (4 * (CS / Real.sqrt c)) * P ≤
        12 * (CS / Real.sqrt c) / lam * (P * ℓ) := by
      have := mul_le_mul_of_nonneg_right hLcount
        (show 0 ≤ 4 * (CS / Real.sqrt c) * P by positivity)
      calc ((L : ℝ) + 1) * (4 * (CS / Real.sqrt c)) * P
          = ((L : ℝ) + 1) * (4 * (CS / Real.sqrt c) * P) := by ring
        _ ≤ 3 * ℓ / lam * (4 * (CS / Real.sqrt c) * P) := this
        _ = 12 * (CS / Real.sqrt c) / lam * (P * ℓ) := by ring
    have e3 : P ≤ 1 / lam * (P * ℓ) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hlam0]
      exact mul_le_mul_of_nonneg_left hℓlam (by linarith)
    have := hsm
    rw [e1] at this
    linarith
  -- piece 3: height removal
  have hT3 : |phaseCount (z₀ + (ε : ℂ) * I) F - phaseCount z₀ F| ≤ 1 / (δ * lam) * (P * ℓ) := by
    refine hht.trans ?_
    have h1 : (W : ℝ) * (ε / z₀.im) ≤ P / δ := by
      rw [← hWε, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hεpos.le hδpos hz0) (by positivity)
    refine h1.trans ?_
    rw [div_le_iff₀ hδpos]
    have : 1 / (δ * lam) * (P * ℓ) * δ = P * ℓ / lam := by field_simp
    rw [this, le_div_iff₀ hlam0]
    exact mul_le_mul_of_nonneg_left hℓlam (by linarith)
  -- piece 2: the core
  have hT2 : |ES - phaseCount (z₀ + (ε : ℂ) * I) F - X| ≤ |CH| * (W * d ^ 2 + P * ℓ) := by
    refine hcore'.trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have htri : |EN - phaseCount z₀ F - X| ≤ |EN - ES| + |ES - phaseCount (z₀ + (ε : ℂ) * I) F - X|
      + |phaseCount (z₀ + (ε : ℂ) * I) F - phaseCount z₀ F| := by
    have : EN - phaseCount z₀ F - X = (EN - ES) + (ES - phaseCount (z₀ + (ε : ℂ) * I) F - X)
        + (phaseCount (z₀ + (ε : ℂ) * I) F - phaseCount z₀ F) := by ring
    rw [this]
    exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
  have hPℓ : 0 ≤ P * ℓ := by positivity
  calc |EN - phaseCount z₀ F - X| ≤ _ := htri
    _ ≤ (12 * (CS / Real.sqrt c) / lam + 1 / lam) * (P * ℓ) + |CH| * (W * d ^ 2 + P * ℓ) +
          1 / (δ * lam) * (P * ℓ) := add_le_add (add_le_add hT1 hT2) hT3
    _ = |CH| * (W * d ^ 2 + P * ℓ) + K * (P * ℓ) := by rw [hK]; ring
    _ ≤ |CH| * (W * d ^ 2 + P * ℓ) + K * (W * d ^ 2 + P * ℓ) := by
        gcongr; linarith
    _ = (|CH| + K) * (W * d ^ 2 + P * ℓ) := by ring

/-- **The fresh-count lemma** (`FreshCountContract`), from `ConditionalBlockGUECount` and the
heat-interpolation hypothesis `FcHeatCore`. The `fluctuation` field uses no hypothesis
(`freshCount_fluctuation`). -/
theorem freshCount_holds_of_heatCore (hcount : ConditionalBlockGUECount) (hcore : FcHeatCore) :
    FreshCountContract where
  mean := freshCount_mean_of_heatCore hcount hcore
  fluctuation := freshCount_fluctuation

/-!
## 6. The heat core from the heat derivative and the mean-square bound
-/

/-- `Σ` over the spectrum of `-s - F`: `spectralSum (-s - F) f = Σ_k f(-s - λ_k(F))`. -/
theorem fc_spectralSum_neg_shift {ι : Type} [Fintype ι] [DecidableEq ι] {F : Matrix ι ι ℂ}
    (hF : F.IsHermitian) (s : ℝ) (f : ℝ → ℝ) :
    spectralSum (-(s : ℂ) • (1 : Matrix ι ι ℂ) - F) f = ∑ k, f (-s - hF.eigenvalues k) := by
  set U : Matrix ι ι ℂ := (hF.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hUU' : star U * U = 1 := Unitary.coe_star_mul_self _
  have hFe : F = U * diagonal (fun k => (hF.eigenvalues k : ℂ)) * star U := by
    conv_lhs => rw [hF.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have hD : diagonal (fun k => (((-s - hF.eigenvalues k : ℝ)) : ℂ)) =
      -(s : ℂ) • (1 : Matrix ι ι ℂ) - diagonal (fun k => (hF.eigenvalues k : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have hM : -(s : ℂ) • (1 : Matrix ι ι ℂ) - F =
      U * diagonal (fun k => (((-s - hF.eigenvalues k : ℝ)) : ℂ)) * star U := by
    rw [hD, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, hUU, ← hFe]
  unfold spectralSum
  rw [hM, charpoly_mul_comm, ← mul_assoc, hUU', one_mul, charpoly_diagonal,
    Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _)]
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map,
    Function.comp_def, Complex.ofReal_re]
  rfl

section HeatPath

variable (b E : ℝ) {W : ℕ} (F : Matrix (Fin W) (Fin W) ℂ)

/-- `γ = c(-Im a) = Im z₀`. -/
def fcGamma : ℝ := (1 - 2 * b) * -(matchedA E).im

/-- `y_t = (1-t) γ + ε`. -/
def fcHeight' (ε t : ℝ) : ℝ := (1 - t) * fcGamma b E + ε

/-- The Hermitian part `√t A - E - F - (1-t) c Re a` of `H_t`. -/
def fcHeatHerm (t : ℝ) (A : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  (Real.sqrt t : ℂ) • A - ((E + (1 - t) * (1 - 2 * b) * (matchedA E).re : ℝ) : ℂ) • 1 - F

/-- `H_t = √t A - E - F - (1-t) c a + iε`. -/
def fcHeatMatrix (ε t : ℝ) (A : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  fcHeatHerm b E F t A + ((fcHeight' b E ε t : ℂ) * I) • 1

/-- `g_t = W⁻¹ Tr H_t⁻¹`. -/
def fcHeatTrace (ε t : ℝ) (A : Matrix (Fin W) (Fin W) ℂ) : ℂ :=
  (W : ℂ)⁻¹ * ((fcHeatMatrix b E F ε t A)⁻¹).trace

/-- `Φ(t) = π⁻¹ Im E Tr log H_t = E π⁻¹ Σ_j arg(μ_j(t) + i y_t)`, `μ_j(t)` the eigenvalues of the
Hermitian part (`H_t` is normal with eigenvalues `μ_j(t) + i y_t`). -/
def fcHeatPhase (ε t : ℝ) : ℝ :=
  ∫ A, spectralSum (fcHeatHerm b E F t A) (fcSmoothInd (fcHeight' b E ε t))
    ∂gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))

end HeatPath

theorem fcHeatPhase_one (b E : ℝ) {W : ℕ} (F : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ) :
    fcHeatPhase b E F ε 1 = ∫ A, spectralSum (A - (E : ℂ) • 1 - F) (fcSmoothInd ε)
      ∂gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W)) := by
  unfold fcHeatPhase fcHeatHerm fcHeight'
  simp

theorem fcHeatPhase_zero (b E : ℝ) {W : ℕ} {F : Matrix (Fin W) (Fin W) ℂ} (hF : F.IsHermitian)
    (ε : ℝ) :
    fcHeatPhase b E F ε 0 =
      phaseCount (-(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * matchedA E + (ε : ℂ) * I) F := by
  unfold fcHeatPhase fcHeatHerm
  simp only [Real.sqrt_zero, Complex.ofReal_zero, zero_smul, zero_sub, sub_zero, one_mul,
    integral_const, probReal_univ, one_smul]
  rw [show -(((E + (1 - 2 * b) * (matchedA E).re : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) - F
      = -(((E + (1 - 2 * b) * (matchedA E).re : ℝ) : ℂ)) • 1 - F by rw [neg_smul]]
  rw [fc_spectralSum_neg_shift hF, fc_phaseCount_eq hF]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold fcSmoothInd fcHeight' fcGamma
  congr 2
  apply Complex.ext
  · simp; ring
  · simp

/-- **Input (i): the heat derivative** (the fresh log-heat identity). For
`b ∈ (0,1/2)`, `E ∈ (-2,2)`, Hermitian `F`, `W ≥ 1` and `ε > 0`: `Φ` is continuous on
`[0,1]` and has, at every `t ∈ [0,1)`, the right derivative
`(cW/2π) Im a² - (cW/2π) Im E(g_t - a)²` (`= π⁻¹ Im cW E(a g_t - g_t²/2)`). Not proved here. -/
def FcHeatDerivative : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, |E| < 2 → ∀ (W : ℕ), 0 < W →
    ∀ F : Matrix (Fin W) (Fin W) ℂ, F.IsHermitian → ∀ ε : ℝ, 0 < ε →
      ContinuousOn (fcHeatPhase b E F ε) (Set.Icc 0 1) ∧
      ∀ t ∈ Set.Ico (0 : ℝ) 1, HasDerivWithinAt (fcHeatPhase b E F ε)
        ((1 - 2 * b) * W / (2 * Real.pi) * (matchedA E ^ 2).im -
          (1 - 2 * b) * W / (2 * Real.pi) *
            (∫ A, (fcHeatTrace b E F ε t A - matchedA E) ^ 2
              ∂gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))).im) (Set.Ici t) t

/-- **Input (ii): the mean-square comparison** (in the paper: the fresh count
variance bound, the stable scalar branch, Gaussian integration by parts and
continuation): with `ε = W^{-3/5}`, for `d ≤ d_*` and `t ∈ [0,1)`,
`E|g_t - a|² ≤ C(d² + ε² + W⁻² y_t⁻³)`. Constants after `b, κ`; uniform in `W ≥ 1`,
Hermitian `F` and `E ∈ bulkInterval κ`. Not proved here. -/
def FcMeanSquare : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ dstar C : ℝ, 0 < dstar ∧
      ∀ (W : ℕ), 0 < W → ∀ F : Matrix (Fin W) (Fin W) ℂ, F.IsHermitian →
      ∀ E ∈ bulkInterval κ,
        let a := matchedA E
        let z₀ : ℂ := -(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * a
        let d := ‖(W : ℂ)⁻¹ * ((z₀ • 1 - F)⁻¹).trace - a‖
        d ≤ dstar → ∀ t ∈ Set.Ico (0 : ℝ) 1,
          (∫ A, ‖fcHeatTrace b E F (fcHeight W) t A - a‖ ^ 2
              ∂gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) ≤
            C * (d ^ 2 + fcHeight W ^ 2 +
              ((W : ℝ) ^ 2)⁻¹ * (fcHeight' b E (fcHeight W) t ^ 3)⁻¹)

theorem fcHeight_le_one {W : ℕ} (hW : 0 < W) : fcHeight W ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hW) (by norm_num)

/-- `W ε² ≤ W^{2/5}` and `W⁻¹ ε⁻² ≤ W^{2/5}` for `ε = W^{-3/5}`. -/
theorem fc_height_sq_bounds {W : ℕ} (hW : 0 < W) :
    (W : ℝ) * fcHeight W ^ 2 ≤ (W : ℝ) ^ (2 / 5 : ℝ) ∧
      (W : ℝ) * (((W : ℝ) ^ 2)⁻¹ * (fcHeight W ^ 2)⁻¹) ≤ (W : ℝ) ^ (2 / 5 : ℝ) := by
  have hWp : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hε := fcHeight_pos hW
  have hε1 := fcHeight_le_one hW
  have hP := fc_mul_height hW
  set P := (W : ℝ) ^ (2 / 5 : ℝ) with hPdef
  have hP1 := fc_one_le_rpow hW
  constructor
  · calc (W : ℝ) * fcHeight W ^ 2 = (W * fcHeight W) * fcHeight W := by ring
      _ ≤ (W * fcHeight W) * 1 := mul_le_mul_of_nonneg_left hε1 (by positivity)
      _ = P := by rw [hP, mul_one]
  · have hP3 : (W : ℝ) ≤ P ^ 3 := by
      rw [hPdef, ← Real.rpow_mul_natCast hWp.le]
      calc (W : ℝ) = (W : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (W : ℝ) ^ (2 / 5 * ((3 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
    have heq : (W : ℝ) * (((W : ℝ) ^ 2)⁻¹ * (fcHeight W ^ 2)⁻¹) = W / P ^ 2 := by
      rw [← hP]; field_simp
    rw [heq, div_le_iff₀ (by positivity)]
    nlinarith

/-- **Integration in `t` (fencing).** Let `y_t = (1-t)γ + ε` (`γ, ε > 0`). If `Φ` is continuous
on `[0,1]` with right derivative `X - k Im G(t)` on `[0,1)`, `k ≥ 0`, and
`‖G(t)‖ ≤ C (s + w y_t⁻³)` (`s, w ≥ 0`), then `|Φ(1) - Φ(0) - X| ≤ k |C| (s + w ε⁻² / (2γ))`. -/
theorem fc_fence {Φ : ℝ → ℝ} {G : ℝ → ℂ} {X k C s w γ ε : ℝ} (hk : 0 ≤ k) (hs : 0 ≤ s)
    (hw : 0 ≤ w) (hγ : 0 < γ) (hε : 0 < ε) (hcont : ContinuousOn Φ (Set.Icc 0 1))
    (hder : ∀ t ∈ Set.Ico (0 : ℝ) 1, HasDerivWithinAt Φ (X - k * (G t).im) (Set.Ici t) t)
    (hG : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖G t‖ ≤ C * (s + w * (((1 - t) * γ + ε) ^ 3)⁻¹)) :
    |Φ 1 - Φ 0 - X| ≤ k * |C| * (s + w * (ε ^ 2)⁻¹ / (2 * γ)) := by
  set y : ℝ → ℝ := fun t => (1 - t) * γ + ε with hy
  have hyt : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < y t := by
    intro t ht
    simp only [hy]
    nlinarith [ht.2]
  have hyd : ∀ t, HasDerivAt y (-γ) t := by
    intro t
    have := (((hasDerivAt_id t).const_sub 1).mul_const γ).add_const ε
    simpa [hy] using this
  set M := k * |C| with hM
  have hM0 : 0 ≤ M := mul_nonneg hk (abs_nonneg _)
  set B : ℝ → ℝ := fun t => M * (s * t + w * ((y t ^ 2)⁻¹ - (y 0 ^ 2)⁻¹) / (2 * γ)) with hB
  set B' : ℝ → ℝ := fun t => M * (s + w * (y t ^ 3)⁻¹) with hB'
  set ψ : ℝ → ℝ := fun t => Φ t - Φ 0 - X * t with hψ
  have hfence := image_norm_le_of_norm_deriv_right_le_deriv_boundary' (f := ψ)
    (f' := fun t => -(k * (G t).im)) (a := 0) (b := 1) (B := B) (B' := B')
    (by
      have h : ContinuousOn (fun t => Φ t - Φ 0 - X * t) (Set.Icc 0 1) :=
        ContinuousOn.sub (ContinuousOn.sub hcont (continuousOn_const (c := Φ 0)))
          (Continuous.continuousOn (by fun_prop : Continuous fun t : ℝ => X * t))
      exact h)
    (by
      intro t ht
      have h2 : HasDerivWithinAt (fun r => Φ r - Φ 0 - X * r) (X - k * (G t).im - X * 1)
          (Set.Ici t) t :=
        ((hder t ht).sub_const (Φ 0)).sub ((hasDerivAt_id t).const_mul X).hasDerivWithinAt
      convert h2 using 1
      ring)
    (by simp [hψ, hB])
    (by
      intro t ht
      have hy0 : y t ≠ 0 := (hyt t ht).ne'
      refine ContinuousAt.continuousWithinAt ?_
      have hyc : ContinuousAt y t := (hyd t).continuousAt
      have h1 : ContinuousAt (fun t => (y t ^ 2)⁻¹) t := (hyc.pow 2).inv₀ (pow_ne_zero 2 hy0)
      have h2 : ContinuousAt (fun t => M * (s * t + w * ((y t ^ 2)⁻¹ - (y 0 ^ 2)⁻¹) / (2 * γ))) t :=
        continuousAt_const.mul ((continuousAt_const.mul continuousAt_id).add
          ((continuousAt_const.mul (h1.sub continuousAt_const)).div_const _))
      exact h2)
    (by
      intro t ht
      have hy0 : y t ≠ 0 := (hyt t (Set.Ico_subset_Icc_self ht)).ne'
      have h1 : HasDerivAt (fun r => y r ^ 2) (2 * y t * (-γ)) t := by
        have := (hyd t).pow 2
        convert this using 1
        push_cast; ring
      have h2 := h1.inv (pow_ne_zero 2 hy0)
      have h3 := (((hasDerivAt_id t).const_mul s).add
          (((h2.sub_const ((y 0 ^ 2)⁻¹)).const_mul w).div_const (2 * γ))).const_mul M
      convert h3.hasDerivWithinAt using 1
      · funext r
        simp only [hB, id, Pi.add_apply, Pi.inv_apply]
      · simp only [hB']
        field_simp)
    (by
      intro t ht
      have hyp := hyt t (Set.Ico_subset_Icc_self ht)
      have hnn : 0 ≤ s + w * (y t ^ 3)⁻¹ := by positivity
      simp only [hB', norm_neg, Real.norm_eq_abs, abs_mul, abs_of_nonneg hk, hM, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hk
      calc |(G t).im| ≤ ‖G t‖ := abs_im_le_norm _
        _ ≤ C * (s + w * (y t ^ 3)⁻¹) := hG t ht
        _ ≤ |C| * (s + w * (y t ^ 3)⁻¹) := mul_le_mul_of_nonneg_right (le_abs_self _) hnn)
  have h1 := hfence (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
  have hy1 : y 1 = ε := by simp [hy]
  have hψ1 : ‖ψ 1‖ = |Φ 1 - Φ 0 - X| := by simp [hψ]
  rw [hψ1] at h1
  refine h1.trans ?_
  simp only [hB, hy1, mul_one]
  refine mul_le_mul_of_nonneg_left ?_ hM0
  have : 0 ≤ (y 0 ^ 2)⁻¹ := by positivity
  have h2 : w * ((ε ^ 2)⁻¹ - (y 0 ^ 2)⁻¹) ≤ w * (ε ^ 2)⁻¹ :=
    mul_le_mul_of_nonneg_left (by linarith) hw
  have h3 := div_le_div_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 2 * γ)
  linarith

/-- **The heat core from the two inputs** ("integrating
the heat derivative costs at most `C(Wd² + Wε² + (Wε²)⁻¹)`"): `FcHeatDerivative` and
`FcMeanSquare` imply `FcHeatCore`, by `fc_fence` with `k = cW/2π`, `s = d² + ε²`, `w = W⁻²`,
then `W ε² ≤ W^{2/5}`, `W⁻¹ε⁻² = W^{1/5} ≤ W^{2/5}` and `γ = Im z₀ ≥ δ_κ`. -/
theorem fcHeatCore_of (hder : FcHeatDerivative) (hms : FcMeanSquare) : FcHeatCore := by
  intro b hb0 hb κ hκ
  obtain ⟨dstar, C2, hds, hC2⟩ := hms b hb0 hb κ hκ
  have hcpos : 0 < 1 - 2 * b := by linarith
  have hδpos := fc_bulk_delta_pos hb hκ
  set δ := (1 - 2 * b) * (Real.sqrt (4 - (2 - min κ 2) ^ 2) / 2) with hδ
  have hlam0 := fc_log_two_pos
  set K := (1 - 2 * b) / (2 * Real.pi) * |C2| * (1 + (1 + 1 / (2 * δ)) / Real.log 2) with hK
  refine ⟨dstar, K, hds, fun W hW F hF E hE => ?_⟩
  intro a z₀ d hd
  have hms' := hC2 W hW F hF E hE hd
  have hεpos := fcHeight_pos hW
  have hE2 : |E| < 2 := by
    have h := abs_le_of_mem_bulkInterval hE; linarith
  obtain ⟨hcont, hderiv⟩ := hder b hb0 hb E hE2 W hW F hF (fcHeight W) hεpos
  have hγδ : δ ≤ fcGamma b E := by
    have h := fc_z0_im_ge hb hE
    have : (-(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * matchedA E).im = fcGamma b E := by
      rw [fcGamma]
      simp only [sub_im, neg_im, ofReal_im, mul_im, ofReal_re, zero_mul, add_zero]
      ring
    rw [this] at h; exact h
  have hγpos : 0 < fcGamma b E := lt_of_lt_of_le hδpos hγδ
  have hWp : (0 : ℝ) < W := by exact_mod_cast hW
  have hfen := fc_fence (Φ := fcHeatPhase b E F (fcHeight W))
    (G := fun t => ∫ A, (fcHeatTrace b E F (fcHeight W) t A - a) ^ 2
      ∂gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W)))
    (X := (1 - 2 * b) * W / (2 * Real.pi) * (a ^ 2).im) (k := (1 - 2 * b) * W / (2 * Real.pi))
    (C := C2) (s := d ^ 2 + fcHeight W ^ 2) (w := ((W : ℝ) ^ 2)⁻¹) (γ := fcGamma b E)
    (ε := fcHeight W) (by positivity) (by positivity) (by positivity) hγpos hεpos hcont hderiv
    (fun t ht => by
      refine (norm_integral_le_integral_norm _).trans ?_
      simp only [norm_pow]
      have := hms' t ht
      simp only [fcHeight'] at this
      linarith)
  rw [fcHeatPhase_one, fcHeatPhase_zero b E hF] at hfen
  refine hfen.trans ?_
  -- numerics
  obtain ⟨hb1, hb2⟩ := fc_height_sq_bounds hW
  set P := (W : ℝ) ^ (2 / 5 : ℝ) with hP
  set ℓ := Real.log (2 * W) with hℓ
  have hP1 : 1 ≤ P := fc_one_le_rpow hW
  have hℓlam : Real.log 2 ≤ ℓ := fc_log_two_le hW
  set k0 := (1 - 2 * b) / (2 * Real.pi) * |C2| with hk0
  have hk00 : 0 ≤ k0 := by positivity
  have hstep1 : (1 - 2 * b) * W / (2 * Real.pi) * |C2| *
      (d ^ 2 + fcHeight W ^ 2 + ((W : ℝ) ^ 2)⁻¹ * (fcHeight W ^ 2)⁻¹ / (2 * fcGamma b E)) =
      k0 * (W * d ^ 2 + W * fcHeight W ^ 2 +
        (W : ℝ) * (((W : ℝ) ^ 2)⁻¹ * (fcHeight W ^ 2)⁻¹) / (2 * fcGamma b E)) := by
    rw [hk0]; ring
  rw [hstep1]
  have hq : (W : ℝ) * (((W : ℝ) ^ 2)⁻¹ * (fcHeight W ^ 2)⁻¹) / (2 * fcGamma b E) ≤
      P / (2 * δ) := by
    calc (W : ℝ) * (((W : ℝ) ^ 2)⁻¹ * (fcHeight W ^ 2)⁻¹) / (2 * fcGamma b E)
        ≤ P / (2 * fcGamma b E) := div_le_div_of_nonneg_right hb2 (by positivity)
      _ ≤ P / (2 * δ) := div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
  have hPl : P ≤ P * ℓ / Real.log 2 := by
    rw [le_div_iff₀ hlam0]; exact mul_le_mul_of_nonneg_left hℓlam (by linarith)
  have hsum : W * d ^ 2 + W * fcHeight W ^ 2 +
      (W : ℝ) * (((W : ℝ) ^ 2)⁻¹ * (fcHeight W ^ 2)⁻¹) / (2 * fcGamma b E) ≤
      (1 + (1 + 1 / (2 * δ)) / Real.log 2) * (W * d ^ 2 + P * ℓ) := by
    have hd0 : 0 ≤ (W : ℝ) * d ^ 2 := by positivity
    have hPℓ : 0 ≤ P * ℓ := mul_nonneg (by linarith) (by linarith)
    have e1 : P + P / (2 * δ) = (1 + 1 / (2 * δ)) * P := by field_simp
    have e2 : (1 + 1 / (2 * δ)) * P ≤ (1 + 1 / (2 * δ)) * (P * ℓ / Real.log 2) :=
      mul_le_mul_of_nonneg_left hPl (by positivity)
    have e3 : (1 + (1 + 1 / (2 * δ)) / Real.log 2) * (W * d ^ 2 + P * ℓ) =
        (W * d ^ 2 + P * ℓ) + (1 + 1 / (2 * δ)) * (P * ℓ / Real.log 2) +
          (1 + 1 / (2 * δ)) / Real.log 2 * (W * d ^ 2) := by
      field_simp
      ring
    have e4 : 0 ≤ (1 + 1 / (2 * δ)) / Real.log 2 * (W * d ^ 2) := by positivity
    rw [e3]
    linarith
  calc k0 * (W * d ^ 2 + W * fcHeight W ^ 2 +
        (W : ℝ) * (((W : ℝ) ^ 2)⁻¹ * (fcHeight W ^ 2)⁻¹) / (2 * fcGamma b E))
      ≤ k0 * ((1 + (1 + 1 / (2 * δ)) / Real.log 2) * (W * d ^ 2 + P * ℓ)) :=
        mul_le_mul_of_nonneg_left hsum hk00
    _ = K * (W * d ^ 2 + P * ℓ) := by rw [hK, hk0]; ring

/-- **The fresh-count lemma** from `ConditionalBlockGUECount` and the two analytic hypotheses
`FcHeatDerivative` and `FcMeanSquare` of the heat interpolation. -/
theorem freshCount_holds_of_heat (hcount : ConditionalBlockGUECount)
    (hder : FcHeatDerivative) (hms : FcMeanSquare) : FreshCountContract :=
  freshCount_holds_of_heatCore hcount (fcHeatCore_of hder hms)

end BlockBand.Layers
