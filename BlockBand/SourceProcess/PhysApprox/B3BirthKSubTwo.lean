module

public import BlockBand.SourceProcess.PhysApprox.B3BirthKSubRes
public import BlockBand.SourceProcess.PhysApprox.B3BirthPCross

/-!
# The closing correction at birth from two-leg (bilinear) path estimates

Measures: `closedLaw b W np` (path, probes, phase) for the target, `growthPathLaw W b` and
`phaseLaw` for the estimates. At length `n = j + 1`, `M(θ) = R(θ)Π𝕊` (`resOutMat`),
`X_c = 𝒰ᴴι_{p_c}` (`colMap … 1`), `Y_c = X_cX_cᴴ = Y_{n;k_c}` (`colMap_mul_conjTranspose`).

The closing correction is kept **bilinear** (no Cauchy–Schwarz split of its two legs):
`corr_{aa'} = 2iηz √(m_a/W)√(m_{a'}/W) g_aᴴ(X_aᴴMX_{a'})g_{a'}` (`birthKCorrAt_eq_bilinear`).
* Two distinct born probes: averaging over `g_a` and then `g_{a'}` gives
  `E|corr_{aa'}| ≤ 2|η| √(m_a/W)√(m_{a'}/W) E_θE_ω (Re Tr(MᴴY_aMY_{a'}))^{1/2}`.
* One probe (`a = a'`): `E|g^*Kg| ≤ |Tr K| + ‖K‖_HS` gives
  `E|corr_{aa}| ≤ 2|η|(m_a/W) E_θE_ω(|Tr(MY_a)| + (Re Tr(MᴴY_aMY_a))^{1/2})`.
* Unborn probes have zero columns. Two distinct newborns at the same step do not occur eventually
  (`BirthP.eventually_floor_ne`, `τ` injective).

**Path-only estimates** (unstopped), stated as hypotheses:
* `BirthKCorrTwoLeg`: the mixed two-leg phase mean `→ 0` at birth steps;
* `BirthKCorrDiag`: the newborn diagonal one-probe phase mean `→ 0` at its birth step.

`complexBirthKClosing_of_twoLeg : BirthKCorrTwoLeg → BirthKCorrDiag → ComplexBirthKClosing`. By
Khintchine the two estimates are equivalent, up to universal constants, to the unstopped version of
the target with the probes integrated out; this equivalence is not used here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.BirthKSub

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosingLeak BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.FullSourceStops
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate

variable {W np : ℕ}

/-!
## Gaussian averages (general row type)
-/

theorem dot_mulVec_eq_quad' {ρ κ : Type*} [Fintype ρ] [Fintype κ] (L : Matrix ρ κ ℂ)
    (g : κ → ℂ) : star (L *ᵥ g) ⬝ᵥ (L *ᵥ g) = Counting.complexQuadraticForm (Lᴴ * L) g := by
  rw [dot_mulVec_self]
  simp only [Counting.complexQuadraticForm, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  simp only [Complex.star_def]
  ring

theorem lintegral_l2_sq_mulVec' {ρ : Type*} [Fintype ρ] (L : Matrix ρ (Fin W) ℂ) :
    ∫⁻ v, ENNReal.ofReal (l2 (L *ᵥ v) ^ 2) ∂circularVectorLaw (Fin W) =
      ENNReal.ofReal (Lᴴ * L).trace.re := by
  have hpt : ∀ v, l2 (L *ᵥ v) ^ 2 = (Counting.complexQuadraticForm (Lᴴ * L) v).re := by
    intro v
    rw [l2_sq, dot_mulVec_eq_quad']
  simp_rw [hpt]
  have h0 : 0 ≤ᵐ[circularVectorLaw (Fin W)] fun v =>
      (Counting.complexQuadraticForm (Lᴴ * L) v).re :=
    ae_of_all _ fun v => by
      simp only [Pi.zero_apply]
      rw [← hpt]
      positivity
  have hI : Integrable (fun v => (Counting.complexQuadraticForm (Lᴴ * L) v).re)
      (circularVectorLaw (Fin W)) := (Birth.integrable_quad' (Lᴴ * L)).re
  have hre := integral_re (Birth.integrable_quad' (Lᴴ * L))
  simp only [RCLike.re_to_complex] at hre
  rw [← ofReal_integral_eq_lintegral_ofReal hI h0, hre, Birth.integral_quad']

theorem measurable_ofReal_l2_mulVec_gen {α ρ κ : Type*} [MeasurableSpace α] [Fintype ρ]
    [Fintype κ] {L : α → Matrix ρ κ ℂ} {v : α → κ → ℂ} (hL : Measurable L) (hv : Measurable v) :
    Measurable fun a => ENNReal.ofReal (l2 (L a *ᵥ v a)) := by
  refine (continuous_l2.measurable.comp (measurable_pi_iff.2 fun y => ?_)).ennreal_ofReal
  simp only [mulVec, dotProduct]
  exact Finset.measurable_sum _ fun a _ => hL.eval_matrix.mul ((measurable_pi_apply a).comp hv)

/-- `E‖Lg‖ ≤ ‖L‖_HS`. -/
theorem lintegral_l2_mulVec_le {ρ : Type*} [Fintype ρ] (L : Matrix ρ (Fin W) ℂ) :
    ∫⁻ v, ENNReal.ofReal (l2 (L *ᵥ v)) ∂circularVectorLaw (Fin W) ≤
      ENNReal.ofReal (Real.sqrt (Lᴴ * L).trace.re) := by
  refine BirthP.lintegral_le_sqrt_of_sq ?_ (re_trace_conjTranspose_mul_self_nonneg L)
    (le_of_eq ?_)
  · exact (measurable_ofReal_l2_mulVec_gen (L := fun _ : Fin W → ℂ => L) measurable_const
      measurable_id).aemeasurable
  · have e : ∀ v, ENNReal.ofReal (l2 (L *ᵥ v)) ^ 2 = ENNReal.ofReal (l2 (L *ᵥ v) ^ 2) :=
      fun v => (ENNReal.ofReal_pow (l2_nonneg _) 2).symm
    simp_rw [e]
    exact lintegral_l2_sq_mulVec' L

theorem bilinear_eq_sum (u : Fin W → ℂ) (K : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) :
    bilinear u K v = ∑ x, (K *ᵥ v) x * conj (u x) := by
  simp only [bilinear, dotProduct, Pi.star_apply, Complex.star_def]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- `E_u|u*Kv| ≤ ‖Kv‖`. -/
theorem lintegral_bilinear_left_le (K : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) :
    ∫⁻ u, ‖bilinear u K v‖ₑ ∂circularVectorLaw (Fin W) ≤ ENNReal.ofReal (l2 (K *ᵥ v)) := by
  simp_rw [bilinear_eq_sum]
  exact BirthP.lintegral_conj_lin_le (K *ᵥ v)

theorem bilinear_self_eq_quad (K : Matrix (Fin W) (Fin W) ℂ) (g : Fin W → ℂ) :
    bilinear g K g = Counting.complexQuadraticForm K g := by
  simp only [bilinear, Counting.complexQuadraticForm, dotProduct, mulVec, Pi.star_apply,
    Finset.mul_sum, Complex.star_def]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  ring

/-- `E|g*Kg| ≤ |Tr K| + ‖K‖_HS`. -/
theorem lintegral_bilinear_self_le (K : Matrix (Fin W) (Fin W) ℂ) :
    ∫⁻ g, ‖bilinear g K g‖ₑ ∂circularVectorLaw (Fin W) ≤
      ENNReal.ofReal (‖K.trace‖ + Real.sqrt (K * Kᴴ).trace.re) := by
  simp_rw [bilinear_self_eq_quad]
  have hm : Measurable fun g : Fin W → ℂ =>
      ‖Counting.complexQuadraticForm K g - K.trace‖ₑ :=
    ((Birth.measurable_quad K).sub_const _).enorm
  calc ∫⁻ g, ‖Counting.complexQuadraticForm K g‖ₑ ∂circularVectorLaw (Fin W)
      ≤ ∫⁻ g, (‖Counting.complexQuadraticForm K g - K.trace‖ₑ + ‖K.trace‖ₑ)
          ∂circularVectorLaw (Fin W) := lintegral_mono fun g => by
        calc ‖Counting.complexQuadraticForm K g‖ₑ =
              ‖(Counting.complexQuadraticForm K g - K.trace) + K.trace‖ₑ := by
              rw [sub_add_cancel]
          _ ≤ _ := enorm_add_le _ _
    _ = ∫⁻ g, ‖Counting.complexQuadraticForm K g - K.trace‖ₑ ∂circularVectorLaw (Fin W) +
          ‖K.trace‖ₑ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (Real.sqrt (K * Kᴴ).trace.re) + ENNReal.ofReal ‖K.trace‖ := by
        rw [ofReal_norm]
        gcongr
        exact Birth.lintegral_quad_sub_le K
    _ = ENNReal.ofReal (‖K.trace‖ + Real.sqrt (K * Kᴴ).trace.re) := by
        rw [add_comm, ENNReal.ofReal_add (norm_nonneg _) (Real.sqrt_nonneg _)]

/-!
## The block frames
-/

/-- `X_pX_pᴴ = Y_{n;k}`, `p = n − 1 − k`. -/
theorem colMap_mul_conjTranspose (b E : ℝ) {n k : ℕ} (hk : k < n) (ω : GrowthPath W) :
    colMap b E W n 1 ⟨n - 1 - k, by omega⟩ ω * (colMap b E W n 1 ⟨n - 1 - k, by omega⟩ ω)ᴴ =
      tagResponse b E W n k ω := by
  set U := boundaryToInterior b E W n ω
  set p : Fin n := ⟨n - 1 - k, by omega⟩
  ext x y
  have h1 : (colMap b E W n 1 p ω * (colMap b E W n 1 p ω)ᴴ) x y =
      ∑ a, star (U (p, a) x) * U (p, a) y := by
    simp [colMap, Matrix.mul_apply, conjTranspose_apply, U]
  have h2 : tagResponse b E W n k ω x y =
      ∑ u, star (U u x) * ((if k < n ∧ u.1.val = n - 1 - k then 1 else 0) * U u y) := by
    rw [tagResponse, tagProjection, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Matrix.mul_diagonal, conjTranspose_apply]
    ring
  rw [h1, h2, Fintype.sum_prod_type, Finset.sum_eq_single p]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp [p, hk]
  · intro q _ hq
    refine Finset.sum_eq_zero fun a _ => ?_
    have : ¬ (k < n ∧ q.val = n - 1 - k) := fun h => hq (Fin.ext h.2)
    simp [this]
  · simp

/-- `‖X_aᴴMX_b‖_HS² = Tr(MᴴY_aMY_b)`. -/
theorem trace_two_leg {κ : Type*} [Fintype κ] (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (Xa Xb : Matrix (Fin 2 × Fin W) κ ℂ) :
    ((Xaᴴ * M * Xb)ᴴ * (Xaᴴ * M * Xb)).trace =
      (Mᴴ * (Xa * Xaᴴ) * M * (Xb * Xbᴴ)).trace := by
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    show Xbᴴ * (Mᴴ * Xa) * (Xaᴴ * M * Xb) = Xbᴴ * (Mᴴ * Xa * Xaᴴ * M * Xb) by
      simp only [Matrix.mul_assoc], trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem trace_one_leg {κ : Type*} [Fintype κ] (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (Xa : Matrix (Fin 2 × Fin W) κ ℂ) : (Xaᴴ * M * Xa).trace = (M * (Xa * Xaᴴ)).trace := by
  rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]

/-!
## The closing correction as a bilinear form of the probes
-/

theorem birthKCorrAt_eq_dot (b E s h : ℝ) (τ m : Fin np → ℝ) (n : ℕ) (y : ProbedPath W np × ℝ)
    (a a' : Fin np) :
    birthKCorrAt b E s h τ m W n y a a' = (((2 * etaZ b E : ℝ) : ℂ) * Complex.I * phase y.2) *
      (star ((probeFrame b E W n τ m y.1)ᵀ a) ⬝ᵥ
        (resOutMat b E s h W n y.1.1 y.2 *ᵥ (probeFrame b E W n τ m y.1)ᵀ a')) := by
  rw [birthKCorrAt, Matrix.smul_apply, smul_eq_mul]
  congr 1
  rw [← col_mul, ← conjTranspose_mul_apply_eq]
  simp only [resOutMat, birthKRes, closingN, Matrix.mul_assoc]

/-- **The bilinear form of the two probes**: for born probes `a, a'`,
`corr_{aa'} = 2iηz √(m_a/W)√(m_{a'}/W) g_aᴴ(X_aᴴMX_{a'})g_{a'}`. -/
theorem birthKCorrAt_eq_bilinear (b E s h : ℝ) (τ m : Fin np → ℝ) {n : ℕ} (a a' : Fin np)
    (ha : ⌊(W : ℝ) * τ a⌋₊ < n) (ha' : ⌊(W : ℝ) * τ a'⌋₊ < n) (y : ProbedPath W np × ℝ) :
    birthKCorrAt b E s h τ m W n y a a' = (((2 * etaZ b E : ℝ) : ℂ) * Complex.I * phase y.2) *
      (((Real.sqrt (m a / W) * Real.sqrt (m a' / W) : ℝ) : ℂ) *
        bilinear (y.1.2 a) ((colMap b E W n 1 ⟨n - 1 - ⌊(W : ℝ) * τ a⌋₊, by omega⟩ y.1.1)ᴴ *
          resOutMat b E s h W n y.1.1 y.2 *
          colMap b E W n 1 ⟨n - 1 - ⌊(W : ℝ) * τ a'⌋₊, by omega⟩ y.1.1) (y.1.2 a')) := by
  rw [birthKCorrAt_eq_dot]
  congr 1
  have hc : ∀ c : Fin np, ⌊(W : ℝ) * τ c⌋₊ < n → (probeFrame b E W n τ m y.1)ᵀ c =
      ((Real.sqrt (m c / W) : ℝ) : ℂ) •
        (colMap b E W n 1 ⟨n - 1 - ⌊(W : ℝ) * τ c⌋₊, by omega⟩ y.1.1 *ᵥ y.1.2 c) := by
    intro c hc
    have := col_mul_probeFrame b E τ m c hc 1 y.1
    rwa [Matrix.one_mul] at this
  rw [hc a ha, hc a' ha', star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, star_mulVec,
    ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, bilinear, smul_eq_mul, smul_eq_mul,
    Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
  simp only [Matrix.mul_assoc]
  ring

/-!
## The two-leg path estimates
-/

/-- **`BirthKCorrTwoLeg`** (mixed entries; unstopped, path only): for distinct born
probes `a, a'`, one of them newborn at `j`,
`E_θE_ω[√(m_a/W)√(m_{a'}/W) (Re Tr(MᴴY_aMY_{a'}))^{1/2}] → 0`, `M = R(θ)Π𝕊`. -/
def BirthKCorrTwoLeg : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ), ComplexSourceLawDomain b E τ m T → 0 < s →
    (∀ j, s < τ j) → 0 < h → h < 1 → ∀ δ : ℝ, 0 < δ → ∀ a a' : Fin np, a ≠ a' →
      ∀ᶠ W in atTop, ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ →
        (⌊(W : ℝ) * τ a⌋₊ = j ∨ ⌊(W : ℝ) * τ a'⌋₊ = j) → ⌊(W : ℝ) * τ a⌋₊ ≤ j →
        ⌊(W : ℝ) * τ a'⌋₊ ≤ j →
        ∫⁻ θ, ∫⁻ ω, ENNReal.ofReal (Real.sqrt (m a / W) * Real.sqrt (m a' / W) *
            Real.sqrt ((resOutMat b E s h W (j + 1) ω θ)ᴴ *
              tagResponse b E W (j + 1) ⌊(W : ℝ) * τ a⌋₊ ω * resOutMat b E s h W (j + 1) ω θ *
              tagResponse b E W (j + 1) ⌊(W : ℝ) * τ a'⌋₊ ω).trace.re)
          ∂growthPathLaw W b ∂phaseLaw ≤ ENNReal.ofReal δ

/-- **`BirthKCorrDiag`** (newborn diagonal; unstopped, path only): at its birth step,
`E_θE_ω[(m_a/W)(|Tr(MY_a)| + (Re Tr(MᴴY_aMY_a))^{1/2})] → 0`. -/
def BirthKCorrDiag : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ), ComplexSourceLawDomain b E τ m T → 0 < s →
    (∀ j, s < τ j) → 0 < h → h < 1 → ∀ δ : ℝ, 0 < δ → ∀ a : Fin np,
      ∀ᶠ W in atTop, ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → ⌊(W : ℝ) * τ a⌋₊ = j →
        ∫⁻ θ, ∫⁻ ω, ENNReal.ofReal (m a / W *
            (‖(resOutMat b E s h W (j + 1) ω θ * tagResponse b E W (j + 1) j ω).trace‖ +
              Real.sqrt ((resOutMat b E s h W (j + 1) ω θ)ᴴ * tagResponse b E W (j + 1) j ω *
                resOutMat b E s h W (j + 1) ω θ * tagResponse b E W (j + 1) j ω).trace.re))
          ∂growthPathLaw W b ∂phaseLaw ≤ ENNReal.ofReal δ

/-!
## Measurability in the path at a fixed phase
-/

theorem measurable_birthKRes_path (b E s h : ℝ) (W n : ℕ) (θ : ℝ) :
    Measurable fun ω : GrowthPath W => birthKRes b E s h W n ω θ := by
  unfold birthKRes closingN
  exact measurable_matrix_inv.comp (measurable_matrix_sub measurable_const
    (measurable_matrix_smul (phase θ) (measurable_matrix_mul' (measurable_matrix_mul'
      (measurable_farEmbed (measurable_closingPairing b E h (closeLen s W)))
      (measurable_scatteringMatrix b E n))
      (measurable_farEmbed (measurable_omittedProj b E h (closeLen s W))))))

theorem measurable_resOutMat_path (b E s h : ℝ) (W n : ℕ) (θ : ℝ) :
    Measurable fun ω : GrowthPath W => resOutMat b E s h W n ω θ :=
  measurable_matrix_mul' (measurable_birthKRes_path b E s h W n θ)
    (measurable_matrix_mul' (measurable_farEmbed (measurable_closingPairing b E h (closeLen s W)))
      (measurable_scatteringMatrix b E n))

theorem enorm_corrCoeff (b E θ : ℝ) :
    ‖((2 * etaZ b E : ℝ) : ℂ) * Complex.I * phase θ‖ₑ = ENNReal.ofReal |2 * etaZ b E| := by
  rw [← ofReal_norm, norm_corrCoeff]

theorem enorm_ofReal_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ₑ = ENNReal.ofReal r := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hr]

/-!
## The probe averages at a fixed phase
-/

/-- **Two distinct born probes**: `E_x|corr_{aa'}(x, θ)| ≤ 2|η| E_ω[√(m_a/W)√(m_{a'}/W)
(Re Tr(MᴴY_aMY_{a'}))^{1/2}]`. -/
theorem lintegral_corr_pair_le (b E s h : ℝ) (τ m : Fin np → ℝ) {n : ℕ}
    {a a' : Fin np} (haa : a ≠ a') (ha : ⌊(W : ℝ) * τ a⌋₊ < n) (ha' : ⌊(W : ℝ) * τ a'⌋₊ < n)
    (θ : ℝ) :
    ∫⁻ x, ‖birthKCorrAt b E s h τ m W n (x, θ) a a'‖ₑ ∂probedPathLaw W np b ≤
      ENNReal.ofReal |2 * etaZ b E| * ∫⁻ ω, ENNReal.ofReal (Real.sqrt (m a / W) *
        Real.sqrt (m a' / W) * Real.sqrt ((resOutMat b E s h W n ω θ)ᴴ *
          tagResponse b E W n ⌊(W : ℝ) * τ a⌋₊ ω * resOutMat b E s h W n ω θ *
          tagResponse b E W n ⌊(W : ℝ) * τ a'⌋₊ ω).trace.re) ∂growthPathLaw W b := by
  set pa : Fin n := ⟨n - 1 - ⌊(W : ℝ) * τ a⌋₊, by omega⟩
  set pa' : Fin n := ⟨n - 1 - ⌊(W : ℝ) * τ a'⌋₊, by omega⟩
  set Kf : GrowthPath W → Matrix (Fin W) (Fin W) ℂ := fun ω =>
    (colMap b E W n 1 pa ω)ᴴ * resOutMat b E s h W n ω θ * colMap b E W n 1 pa' ω with hKf
  set r : ℝ := Real.sqrt (m a / W) * Real.sqrt (m a' / W)
  have hr : 0 ≤ r := by positivity
  set c0 : ℝ := |2 * etaZ b E| * r
  have hc0 : 0 ≤ c0 := by positivity
  have hK : Measurable Kf :=
    measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose'
      (measurable_colMap b E pa (M := fun _ => 1) measurable_const measurable_id))
      (measurable_resOutMat_path b E s h W n θ))
      (measurable_colMap b E pa' (M := fun _ => 1) measurable_const measurable_id)
  have hpt : ∀ (ω : GrowthPath W) (G : Fin np → Fin W → ℂ),
      ‖birthKCorrAt b E s h τ m W n ((ω, G), θ) a a'‖ₑ =
        ENNReal.ofReal c0 * ‖bilinear (G a) (Kf ω) (G a')‖ₑ := by
    intro ω G
    rw [birthKCorrAt_eq_bilinear b E s h τ m a a' ha ha', enorm_mul, enorm_corrCoeff, enorm_mul,
      enorm_ofReal_nonneg hr, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _)]
  have hΨ : Measurable fun w : GrowthPath W × (Fin W → ℂ) =>
      ENNReal.ofReal c0 * ENNReal.ofReal (l2 (Kf w.1 *ᵥ w.2)) :=
    measurable_const.mul (measurable_ofReal_l2_mulVec_gen (hK.comp measurable_fst) measurable_snd)
  refine (BirthP.lintegral_probed_pair_le haa
    (Φ := fun ω u v => ENNReal.ofReal c0 * ‖bilinear u (Kf ω) v‖ₑ)
    (Ψ := fun w => ENNReal.ofReal c0 * ENNReal.ofReal (l2 (Kf w.1 *ᵥ w.2)))
    (ae_of_all _ fun ω G => (hpt ω G).le)
    (fun ω => measurable_const.mul
      (BirthP.measurable_bilinear_vec (Kf ω) measurable_fst measurable_snd).enorm)
    (ae_of_all _ fun ω v => by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      exact lintegral_bilinear_left_le _ _)
    hΨ.aemeasurable).trans ?_
  rw [lintegral_prod _ hΨ.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal c0 * ∫⁻ v, ENNReal.ofReal (l2 (Kf ω *ᵥ v)) ∂circularVectorLaw (Fin W)
      ≤ ENNReal.ofReal c0 * ENNReal.ofReal (Real.sqrt ((Kf ω)ᴴ * Kf ω).trace.re) := by
        gcongr
        exact lintegral_l2_mulVec_le _
    _ = _ := by
        rw [hKf]
        simp only
        rw [trace_two_leg, colMap_mul_conjTranspose b E ha, colMap_mul_conjTranspose b E ha',
          ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul (abs_nonneg _)]
        congr 1
        ring

/-- **One newborn probe**: `E_x|corr_{aa}(x, θ)| ≤ 2|η| E_ω[(m_a/W)(|Tr(MY_a)| +
(Re Tr(MᴴY_aMY_a))^{1/2})]`. -/
theorem lintegral_corr_diag_le (b E s h : ℝ) (τ m : Fin np → ℝ) (hm : ∀ c, 0 ≤ m c) {n : ℕ}
    {a : Fin np} (ha : ⌊(W : ℝ) * τ a⌋₊ < n) (θ : ℝ) :
    ∫⁻ x, ‖birthKCorrAt b E s h τ m W n (x, θ) a a‖ₑ ∂probedPathLaw W np b ≤
      ENNReal.ofReal |2 * etaZ b E| * ∫⁻ ω, ENNReal.ofReal (m a / W *
        (‖(resOutMat b E s h W n ω θ * tagResponse b E W n ⌊(W : ℝ) * τ a⌋₊ ω).trace‖ +
          Real.sqrt ((resOutMat b E s h W n ω θ)ᴴ * tagResponse b E W n ⌊(W : ℝ) * τ a⌋₊ ω *
            resOutMat b E s h W n ω θ * tagResponse b E W n ⌊(W : ℝ) * τ a⌋₊ ω).trace.re))
        ∂growthPathLaw W b := by
  set pa : Fin n := ⟨n - 1 - ⌊(W : ℝ) * τ a⌋₊, by omega⟩
  set Kf : GrowthPath W → Matrix (Fin W) (Fin W) ℂ := fun ω =>
    (colMap b E W n 1 pa ω)ᴴ * resOutMat b E s h W n ω θ * colMap b E W n 1 pa ω with hKf
  set c1 : ℝ := |2 * etaZ b E| * (m a / W)
  have hma : 0 ≤ m a / W := div_nonneg (hm a) (Nat.cast_nonneg W)
  have hc1 : 0 ≤ c1 := by positivity
  have hpt : ∀ (ω : GrowthPath W) (G : Fin np → Fin W → ℂ),
      ‖birthKCorrAt b E s h τ m W n ((ω, G), θ) a a‖ₑ =
        ENNReal.ofReal c1 * ‖bilinear (G a) (Kf ω) (G a)‖ₑ := by
    intro ω G
    rw [birthKCorrAt_eq_bilinear b E s h τ m a a ha ha, enorm_mul, enorm_corrCoeff, enorm_mul,
      Real.mul_self_sqrt hma, enorm_ofReal_nonneg hma, ← mul_assoc,
      ← ENNReal.ofReal_mul (abs_nonneg _)]
  rw [probedPathLaw]
  refine (lintegral_prod_le _).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  simp_rw [hpt]
  have hF : Measurable fun g : Fin W → ℂ => ENNReal.ofReal c1 * ‖bilinear g (Kf ω) g‖ₑ :=
    measurable_const.mul (BirthP.measurable_bilinear_vec (Kf ω) measurable_id measurable_id).enorm
  rw [(measurePreserving_eval (fun _ : Fin np => circularVectorLaw (Fin W)) a).lintegral_comp
    (f := fun g => ENNReal.ofReal c1 * ‖bilinear g (Kf ω) g‖ₑ) hF,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hT : (Kf ω).trace = (resOutMat b E s h W n ω θ *
      tagResponse b E W n ⌊(W : ℝ) * τ a⌋₊ ω).trace := by
    rw [hKf]
    simp only
    rw [trace_one_leg, colMap_mul_conjTranspose b E ha]
  have hH : (Kf ω * (Kf ω)ᴴ).trace = ((resOutMat b E s h W n ω θ)ᴴ *
      tagResponse b E W n ⌊(W : ℝ) * τ a⌋₊ ω * resOutMat b E s h W n ω θ *
      tagResponse b E W n ⌊(W : ℝ) * τ a⌋₊ ω).trace := by
    rw [trace_mul_comm, hKf]
    simp only
    rw [trace_two_leg, colMap_mul_conjTranspose b E ha]
  calc ENNReal.ofReal c1 * ∫⁻ g, ‖bilinear g (Kf ω) g‖ₑ ∂circularVectorLaw (Fin W)
      ≤ ENNReal.ofReal c1 * ENNReal.ofReal (‖(Kf ω).trace‖ +
          Real.sqrt (Kf ω * (Kf ω)ᴴ).trace.re) := by
        gcongr
        exact lintegral_bilinear_self_le _
    _ = _ := by
        rw [hT, hH, ← ENNReal.ofReal_mul hc1, ← ENNReal.ofReal_mul (abs_nonneg _)]
        congr 1
        ring

/-!
## Assembly
-/

/-- From a per-phase probe bound to the alive-set target. -/
theorem lintegral_alive_le {b : ℝ} {A : Set (ProbedPath W np × ℝ)}
    {f : ProbedPath W np × ℝ → ℂ} {κ : ℝ} (hκ : 0 ≤ κ) {F : ℝ → ℝ≥0∞} {θ : ℝ} (hθ : 0 < θ)
    (hF : ∀ θ', ∫⁻ x, ‖f (x, θ')‖ₑ ∂probedPathLaw W np b ≤ ENNReal.ofReal κ * F θ')
    (hI : ∫⁻ θ', F θ' ∂phaseLaw ≤ ENNReal.ofReal (θ / (κ + 1))) :
    ∫⁻ y, ‖A.indicator f y‖ₑ ∂closedLaw b W np ≤ ENNReal.ofReal θ := by
  calc ∫⁻ y, ‖A.indicator f y‖ₑ ∂closedLaw b W np ≤ ∫⁻ y, ‖f y‖ₑ ∂closedLaw b W np :=
        lintegral_mono fun y => by
          by_cases hy : y ∈ A
          · rw [Set.indicator_of_mem hy]
          · rw [Set.indicator_of_notMem hy, enorm_zero]
            exact zero_le
    _ = ∫⁻ z, ‖f z.swap‖ₑ ∂phaseLaw.prod (probedPathLaw W np b) :=
        (lintegral_prod_swap (fun y => ‖f y‖ₑ)).symm
    _ ≤ ∫⁻ θ', ∫⁻ x, ‖f (x, θ')‖ₑ ∂probedPathLaw W np b ∂phaseLaw := lintegral_prod_le _
    _ ≤ ∫⁻ θ', ENNReal.ofReal κ * F θ' ∂phaseLaw := lintegral_mono hF
    _ = ENNReal.ofReal κ * ∫⁻ θ', F θ' ∂phaseLaw := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal κ * ENNReal.ofReal (θ / (κ + 1)) := by gcongr
    _ = ENNReal.ofReal (κ * (θ / (κ + 1))) := (ENNReal.ofReal_mul hκ).symm
    _ ≤ ENNReal.ofReal θ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith

theorem probeFrame_col_eq_zero (b E : ℝ) (τ m : Fin np → ℝ) (c : Fin np) {n : ℕ}
    (hc : ¬ ⌊(W : ℝ) * τ c⌋₊ < n) (x : ProbedPath W np) : (probeFrame b E W n τ m x)ᵀ c = 0 := by
  have := col_mul_probeFrame_eq_zero b E τ m c hc 1 x
  rwa [Matrix.one_mul] at this

/-- **`ComplexBirthKClosing` from the two-leg path estimates.** -/
theorem complexBirthKClosing_of_twoLeg (hX : BirthKCorrTwoLeg) (hD : BirthKCorrDiag) :
    ComplexBirthKClosing := by
  intro b E np τ m T s h K Vs hDom R θ hθ a a'
  obtain ⟨hCSL, hs, hsτ, hh0, hh1, -⟩ := hDom
  have hinj : Function.Injective τ := hCSL.2.2.2.2.1
  have hτ0 : ∀ j, 0 < τ j := hCSL.2.2.2.2.2.1
  have hm : ∀ j, 0 ≤ m j := hCSL.2.2.2.2.2.2.1
  set κ : ℝ := |2 * etaZ b E|
  have hκ : 0 ≤ κ := abs_nonneg _
  have hδ : 0 < θ / (κ + 1) := by positivity
  by_cases haa : a = a'
  · subst haa
    filter_upwards [hD b E np τ m T s h hCSL hs hsτ hh0 hh1 _ hδ a] with W hW
    intro j hj1 hj2 hnew
    have hja : ⌊(W : ℝ) * τ a⌋₊ = j := hnew.elim id id
    refine lintegral_alive_le hκ hθ
      (fun θ' => lintegral_corr_diag_le b E s h τ m hm (by omega) θ') ?_
    rw [hja]
    exact hW j hj1 hj2 hja
  · filter_upwards [hX b E np τ m T s h hCSL hs hsτ hh0 hh1 _ hδ a a' haa,
      BirthP.eventually_floor_ne (hτ0 a) (hτ0 a') (hinj.ne haa)] with W hW _
    intro j hj1 hj2 hnew
    by_cases hb : ⌊(W : ℝ) * τ a⌋₊ ≤ j ∧ ⌊(W : ℝ) * τ a'⌋₊ ≤ j
    · exact lintegral_alive_le hκ hθ
        (fun θ' => lintegral_corr_pair_le b E s h τ m haa (by omega) (by omega) θ')
        (hW j hj1 hj2 hnew hb.1 hb.2)
    · have h0 : ∀ y : ProbedPath W np × ℝ, birthKCorrAt b E s h τ m W (j + 1) y a a' = 0 := by
        intro y
        rw [birthKCorrAt_eq_dot]
        rcases not_and_or.1 hb with hn | hn
        · rw [probeFrame_col_eq_zero b E τ m a (by omega), star_zero, zero_dotProduct, mul_zero]
        · rw [probeFrame_col_eq_zero b E τ m a' (by omega), mulVec_zero, dotProduct_zero,
            mul_zero]
      have hz : ∀ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
          (fun y => birthKCorrAt b E s h τ m W (j + 1) y a a') y‖ₑ = 0 := by
        intro y
        simp [h0]
      rw [lintegral_congr hz, lintegral_zero]
      exact zero_le

end BlockBand.SourceProcess.PhysApprox.B3.BirthKSub
