module

public import BlockBand.SourceProcess.PhysApprox.B3GenStep

/-!
# The Doob split of the `𝒦` brackets

The paper separates the one-step `𝒦` increment into its mean (size `C(δ₀ + W⁻²) Tr M_pr`) and its
centred part (opposite-sign covariance `D₀P⊗P'/(2W)`, equal-sign covariance with the contracting
letters). This file proves that split for the bracket estimates:

* `gen_condExp_mul_eq_centred` (generic, `L²`): `E[FG|𝓕] = E[(F - E[F|𝓕])(G - E[G|𝓕])|𝓕] +
  E[F|𝓕]E[G|𝓕]` a.e.;
* `gen_lintegral_condExp_mul_le`: the bracket error is at most the centred-covariance error plus
  `∫‖E[F|𝓕]‖² + ∫‖E[G|𝓕]‖²`;
* `genBrStep_le`, `genConjStep_le`: the same for the closed process;
* `kStepBracket_of_cov`, `kStepConj_of_cov`: `KStepBracket` and `KStepConj` follow from
  the centred-covariance estimates `KStepCov`, `KStepConjCov`, the **mean estimate**
  `GenStepMeanL2` (`∫‖E_j[1_{A_j} dX_c]‖² ≤ C/W²`) and the integrability estimate `GenStepMemL2`.

For the brackets the paper mean size suffices: `Σ_j C/W² = O(W⁻¹)`. For the drift itself it does
not, so `KStepDrift` keeps the `SummedStep` shape.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate

/-!
## Generic Doob split in `L²`
-/

section Generic

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Doob split of a conditional product.** -/
theorem gen_condExp_mul_eq_centred [IsFiniteMeasure μ] (hm : m ≤ m0) {F G : Ω → ℂ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    μ[F * G | m] =ᵐ[μ] μ[(F - μ[F | m]) * (G - μ[G | m]) | m] + μ[F | m] * μ[G | m] := by
  set a := μ[F | m] with ha_def
  set c := μ[G | m] with hc_def
  have ha2 : MemLp a 2 μ := hF.condExp (by norm_num)
  have hc2 : MemLp c 2 μ := hG.condExp (by norm_num)
  have hasm : StronglyMeasurable[m] a := stronglyMeasurable_condExp
  have hcsm : StronglyMeasurable[m] c := stronglyMeasurable_condExp
  have iF : Integrable F μ := hF.integrable (by norm_num)
  have iG : Integrable G μ := hG.integrable (by norm_num)
  have iFG : Integrable (F * G) μ := hF.integrable_mul hG
  have iaG : Integrable (a * G) μ := ha2.integrable_mul hG
  have iFc : Integrable (F * c) μ := hF.integrable_mul hc2
  have iac : Integrable (a * c) μ := ha2.integrable_mul hc2
  have hexp : (F - a) * (G - c) = F * G - a * G - F * c + a * c := by ring
  have h1 : μ[F * G - a * G - F * c + a * c | m] =ᵐ[μ]
      μ[F * G | m] - μ[a * G | m] - μ[F * c | m] + μ[a * c | m] := by
    filter_upwards [condExp_add ((iFG.sub iaG).sub iFc) iac m,
      condExp_sub (iFG.sub iaG) iFc m, condExp_sub iFG iaG m] with y e1 e2 e3
    simp only [Pi.add_apply, Pi.sub_apply] at e1 e2 e3 ⊢
    rw [e1, e2, e3]
  have h2 : μ[a * G | m] =ᵐ[μ] a * c := by
    have h := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hasm
      (f := a) (g := G) (by simp only [ContinuousLinearMap.mul_apply']; exact iaG) iG
    simp only [ContinuousLinearMap.mul_apply'] at h
    exact h
  have h3 : μ[F * c | m] =ᵐ[μ] a * c := by
    have h := condExp_bilin_of_stronglyMeasurable_right (ContinuousLinearMap.mul ℝ ℂ) hcsm
      (f := F) (g := c) (by simp only [ContinuousLinearMap.mul_apply']; exact iFc) iF
    simp only [ContinuousLinearMap.mul_apply'] at h
    exact h
  have h4 : μ[a * c | m] = a * c := condExp_of_stronglyMeasurable hm (hasm.mul hcsm) iac
  rw [hexp]
  rw [h4] at h1
  filter_upwards [h1, h2, h3] with y e1 e2 e3
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at e1 e2 e3 ⊢
  rw [e1, e2, e3]
  ring

theorem gen_mul_le_sq_add_sq (x y : ℝ≥0∞) : x * y ≤ x ^ 2 + y ^ 2 := by
  rcases le_total x y with hxy | hxy
  · calc x * y ≤ y * y := by gcongr
      _ = y ^ 2 := (sq y).symm
      _ ≤ x ^ 2 + y ^ 2 := le_add_self
  · calc x * y ≤ x * x := by gcongr
      _ = x ^ 2 := (sq x).symm
      _ ≤ x ^ 2 + y ^ 2 := le_self_add

/-- **The bracket error is at most the centred-covariance error plus the two mean squares.** -/
theorem gen_lintegral_condExp_mul_le [IsFiniteMeasure μ] (hm : m ≤ m0) (A : Set Ω) {F G : Ω → ℂ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) (κ : Ω → ℂ) :
    ∫⁻ y, ‖A.indicator (fun y => μ[F * G | m] y - κ y) y‖ₑ ∂μ ≤
      ∫⁻ y, ‖A.indicator (fun y =>
          μ[(F - μ[F | m]) * (G - μ[G | m]) | m] y - κ y) y‖ₑ ∂μ +
        (∫⁻ y, ‖μ[F | m] y‖ₑ ^ 2 ∂μ + ∫⁻ y, ‖μ[G | m] y‖ₑ ^ 2 ∂μ) := by
  have hae := gen_condExp_mul_eq_centred hm hF hG
  have hma : Measurable fun y => ‖μ[F | m] y‖ₑ ^ 2 :=
    ((stronglyMeasurable_condExp.mono hm).measurable.enorm).pow_const 2
  have hmc : Measurable fun y => ‖μ[G | m] y‖ₑ ^ 2 :=
    ((stronglyMeasurable_condExp.mono hm).measurable.enorm).pow_const 2
  calc ∫⁻ y, ‖A.indicator (fun y => μ[F * G | m] y - κ y) y‖ₑ ∂μ
      ≤ ∫⁻ y, (‖A.indicator (fun y =>
          μ[(F - μ[F | m]) * (G - μ[G | m]) | m] y - κ y) y‖ₑ +
          (‖μ[F | m] y‖ₑ ^ 2 + ‖μ[G | m] y‖ₑ ^ 2)) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with y hy
        by_cases hyA : y ∈ A
        · simp only [Set.indicator_of_mem hyA]
          rw [hy]
          simp only [Pi.add_apply, Pi.mul_apply]
          calc ‖μ[(F - μ[F | m]) * (G - μ[G | m]) | m] y + μ[F | m] y * μ[G | m] y - κ y‖ₑ
              = ‖(μ[(F - μ[F | m]) * (G - μ[G | m]) | m] y - κ y) +
                  μ[F | m] y * μ[G | m] y‖ₑ := by ring_nf
            _ ≤ ‖μ[(F - μ[F | m]) * (G - μ[G | m]) | m] y - κ y‖ₑ +
                  ‖μ[F | m] y * μ[G | m] y‖ₑ := enorm_add_le _ _
            _ ≤ _ := by
                gcongr
                rw [enorm_mul]
                exact gen_mul_le_sq_add_sq _ _
        · simp only [Set.indicator_of_notMem hyA, enorm_zero, zero_add]
          exact bot_le
    _ = ∫⁻ y, ‖A.indicator (fun y =>
          μ[(F - μ[F | m]) * (G - μ[G | m]) | m] y - κ y) y‖ₑ ∂μ +
          ∫⁻ y, (‖μ[F | m] y‖ₑ ^ 2 + ‖μ[G | m] y‖ₑ ^ 2) ∂μ :=
        lintegral_add_right' _ (hma.add hmc).aemeasurable
    _ = _ := by
        congr 1
        exact lintegral_add_left hma _

end Generic

/-!
## The closed process
-/

theorem gen_sigma_le (W j np : ℕ) :
    b3Sigma W j np ≤ (inferInstance : MeasurableSpace (ProbedPath W np × ℝ)) := by
  refine Measurable.comap_le ?_
  exact ((measurable_pastCoords W j).comp (measurable_fst.comp measurable_fst)).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

/-- The centred-covariance error of `c, c'` at step `j`: `F = 1_{A_j} dX_c`, `G = 1_{A_j} dX_c'`,
`E|1_{A_j}(E_j[(F - E_jF)(G - E_jG)] - W⁻¹ cCov)|`. -/
def genCovStep (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c c' : CIdx K np) : ℝ≥0∞ :=
  let μ := closedLaw b W np
  let A := b3Alive b E s h τ m R W j Vs
  let F := A.indicator (b3dX b E s h τ m W j Vs c)
  let G := A.indicator (b3dX b E s h τ m W j Vs c')
  ∫⁻ y, ‖A.indicator (fun y =>
      μ[(F - μ[F | b3Sigma W j np]) * (G - μ[G | b3Sigma W j np]) | b3Sigma W j np] y -
        (W : ℂ)⁻¹ * cCov b E c c' (b3ClosedGramAt b E s h τ m W j Vs y)) y‖ₑ ∂μ

/-- The centred conjugate-covariance error of `𝒦_ij, 𝒦_kl` at step `j`. -/
def genConjCovStep (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij kl : Fin np × Fin np) :
    ℝ≥0∞ :=
  let μ := closedLaw b W np
  let A := b3Alive b E s h τ m R W j Vs
  let F := A.indicator (b3dX b E s h τ m W j Vs (Sum.inr ij : CIdx K np))
  let G := A.indicator (fun y => conj (b3dX b E s h τ m W j Vs (Sum.inr kl : CIdx K np) y))
  ∫⁻ y, ‖A.indicator (fun y =>
      μ[(F - μ[F | b3Sigma W j np]) * (G - μ[G | b3Sigma W j np]) | b3Sigma W j np] y -
        (W : ℂ)⁻¹ * kConjCov b E ij kl (b3ClosedGramAt b E s h τ m W j Vs y)) y‖ₑ ∂μ

/-- The mean square of the conditional increment of `c` at step `j`: `∫‖E_j[1_{A_j} dX_c]‖²`. -/
def genMeanSq (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c : CIdx K np) : ℝ≥0∞ :=
  ∫⁻ y, ‖(closedLaw b W np)[(b3Alive b E s h τ m R W j Vs).indicator
      (b3dX b E s h τ m W j Vs c) | b3Sigma W j np] y‖ₑ ^ 2 ∂closedLaw b W np

/-- **Closed bracket ≤ centred covariance + mean squares.** -/
theorem genBrStep_le (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c c' : CIdx K np)
    (hF : MemLp ((b3Alive b E s h τ m R W j Vs).indicator (b3dX b E s h τ m W j Vs c)) 2
      (closedLaw b W np))
    (hG : MemLp ((b3Alive b E s h τ m R W j Vs).indicator (b3dX b E s h τ m W j Vs c')) 2
      (closedLaw b W np)) :
    genBrStep b E s h τ m R W j Vs c c' ≤
      genCovStep b E s h τ m R W j Vs c c' +
        (genMeanSq b E s h τ m R W j Vs c + genMeanSq b E s h τ m R W j Vs c') := by
  unfold genBrStep genCovStep genMeanSq
  rw [Set.indicator_mul]
  exact gen_lintegral_condExp_mul_le (gen_sigma_le W j np) _ hF hG _

/-- **Closed conjugate bracket ≤ centred conjugate covariance + mean squares.** -/
theorem genConjStep_le (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij kl : Fin np × Fin np)
    (hF : MemLp ((b3Alive b E s h τ m R W j Vs).indicator
      (b3dX b E s h τ m W j Vs (Sum.inr ij : CIdx K np))) 2 (closedLaw b W np))
    (hG : MemLp ((b3Alive b E s h τ m R W j Vs).indicator
      (b3dX b E s h τ m W j Vs (Sum.inr kl : CIdx K np))) 2 (closedLaw b W np)) :
    genConjStep (K := K) b E s h τ m R W j Vs ij kl ≤
      genConjCovStep (K := K) b E s h τ m R W j Vs ij kl +
        (genMeanSq b E s h τ m R W j Vs (Sum.inr ij : CIdx K np) +
          genMeanSq b E s h τ m R W j Vs (Sum.inr kl : CIdx K np)) := by
  set μ := closedLaw b W np
  set A := b3Alive b E s h τ m R W j Vs
  set g := b3dX b E s h τ m W j Vs (Sum.inr kl : CIdx K np)
  have hconj : A.indicator (fun y => conj (g y)) =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ A.indicator g := by
    funext y
    by_cases hy : y ∈ A
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  have hG' : MemLp (A.indicator (fun y => conj (g y))) 2 μ := by
    rw [hconj]; exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp_memLp' hG
  have hmean : ∫⁻ y, ‖μ[A.indicator (fun y => conj (g y)) | b3Sigma W j np] y‖ₑ ^ 2 ∂μ =
      ∫⁻ y, ‖μ[A.indicator g | b3Sigma W j np] y‖ₑ ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp_condExp_comm (m := b3Sigma W j np)
      (hG.integrable (by norm_num)) (μ := μ)
    rw [hconj]
    filter_upwards [h] with y hy
    rw [← hy]
    simp
  have key := gen_lintegral_condExp_mul_le (gen_sigma_le W j np) A hF hG'
    (fun y => (W : ℂ)⁻¹ * kConjCov b E ij kl (b3ClosedGramAt b E s h τ m W j Vs y))
  unfold genConjStep genConjCovStep genMeanSq
  rw [Set.indicator_mul]
  rw [hmean] at key
  exact key

/-!
## The bracket estimates from the centred covariances and the mean size
-/

/-- **Square integrability of the alive increments** (from the stopped moments: the
stopped fourth moment for `𝒦`, the one-step Gram growth for Gram coordinates). -/
def GenStepMemL2 : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ,
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ c : CIdx K np,
      MemLp ((b3Alive b E s h τ m R W j (Vs W)).indicator (b3dX b E s h τ m W j (Vs W) c)) 2
        (closedLaw b W np)

/-- **The mean size of the increments, in `L²`** (mean `C(δ₀ + W⁻²) Tr M_pr`
with `‖δ₀‖_{L²} ≤ C/W` and `Tr M_pr < R` alive; for a Gram coordinate the `O(R/W)` drift):
`∫‖E_j[1_{A_j} dX_c]‖² ≤ C/W²`. -/
def GenStepMeanL2 : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ c : CIdx K np,
      genMeanSq b E s h τ m R W j (Vs W) c ≤ ENNReal.ofReal (C / (W : ℝ) ^ 2)

/-- **One-step centred covariances with a `𝒦` coordinate** (the
opposite-sign covariance of `𝒜` is `D₀P⊗P'/(2W)`; the equal-sign one carries the contracting
letters, whence the geometric part). -/
def KStepCov : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ (ij : Fin np × Fin np) (c' : CIdx K np),
      genCovStep b E s h τ m R W j (Vs W) (Sum.inr ij) c' ≤
        ENNReal.ofReal (C / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W))

/-- **One-step centred conjugate covariances**. -/
def KStepConjCov : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ ij kl : Fin np × Fin np,
      genConjCovStep (K := K) b E s h τ m R W j (Vs W) ij kl ≤
        ENNReal.ofReal (C / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W))

/-- The combination of a `SummedStep` bound with two `C/W²` mean squares. -/
theorem gen_stepBound_add_meanSq {ρ s C₁ C₂ : ℝ} {np : ℕ} (τ : Fin np → ℝ) (hρ0 : 0 ≤ ρ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) {W : ℕ} (hW : 1 ≤ W) (j : ℕ) {x y z : ℝ≥0∞}
    (hx : x ≤ ENNReal.ofReal (C₁ / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W)))
    (hy : y ≤ ENNReal.ofReal (C₂ / (W : ℝ) ^ 2)) (hz : z ≤ ENNReal.ofReal (C₂ / (W : ℝ) ^ 2)) :
    x + (y + z) ≤
      ENNReal.ofReal ((C₁ + 2 * C₂) / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W)) := by
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hsq : 0 < Real.sqrt W := Real.sqrt_pos.2 hWpos
  have hr := genStepRate_nonneg hρ0 s τ W j
  have hsqle : Real.sqrt W ≤ W := by
    calc Real.sqrt W ≤ Real.sqrt (W * W) := Real.sqrt_le_sqrt (by nlinarith)
      _ = W := Real.sqrt_mul_self hWpos.le
  have hinv : 1 / (W : ℝ) ≤ 1 / Real.sqrt W := one_div_le_one_div_of_le hsq hsqle
  have hq : C₂ / (W : ℝ) ^ 2 ≤ C₂ / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W) := by
    have : C₂ / (W : ℝ) ^ 2 = C₂ / W * (1 / W) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (hinv.trans (le_add_of_nonneg_left hr))
      (div_nonneg hC₂ hWpos.le)
  have hA : 0 ≤ C₁ / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W) :=
    mul_nonneg (div_nonneg hC₁ hWpos.le) (add_nonneg hr (one_div_nonneg.2 hsq.le))
  have hB : 0 ≤ C₂ / (W : ℝ) ^ 2 := div_nonneg hC₂ (sq_nonneg _)
  calc x + (y + z) ≤ ENNReal.ofReal (C₁ / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W)) +
        (ENNReal.ofReal (C₂ / (W : ℝ) ^ 2) + ENNReal.ofReal (C₂ / (W : ℝ) ^ 2)) :=
        add_le_add hx (add_le_add hy hz)
    _ = ENNReal.ofReal (C₁ / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W) +
          (C₂ / (W : ℝ) ^ 2 + C₂ / (W : ℝ) ^ 2)) := by
        rw [ENNReal.ofReal_add hA (add_nonneg hB hB), ENNReal.ofReal_add hB hB]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : (C₁ + 2 * C₂) / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W) =
            C₁ / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W) +
              2 * (C₂ / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W)) := by ring
        rw [this]
        linarith

/-- **`GenStepMemL2 + GenStepMeanL2 + KStepCov ⇒ KStepBracket`.** -/
theorem kStepBracket_of_cov (hL : GenStepMemL2) (hM : GenStepMeanL2) (hC : KStepCov) :
    KStepBracket := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨C₂, hC₂, hevM⟩ := hM b E np τ m T s h K Vs hD R
  obtain ⟨C₁, ρ, hC₁, hρ0, hρ1, hevC⟩ := hC b E np τ m T s h K Vs hD R
  refine ⟨C₁ + 2 * C₂, ρ, by linarith, hρ0, hρ1, ?_⟩
  filter_upwards [hL b E np τ m T s h K Vs hD R, hevM, hevC, eventually_ge_atTop 1]
    with W hWL hWM hWC hW1 j hj ij c'
  exact (genBrStep_le b E s h τ m R W j (Vs W) _ c' (hWL j hj _) (hWL j hj c')).trans
    (gen_stepBound_add_meanSq τ hρ0 hC₁ hC₂ hW1 j (hWC j hj ij c') (hWM j hj _) (hWM j hj c'))

/-- **`GenStepMemL2 + GenStepMeanL2 + KStepConjCov ⇒ KStepConj`.** -/
theorem kStepConj_of_cov (hL : GenStepMemL2) (hM : GenStepMeanL2) (hC : KStepConjCov) :
    KStepConj := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨C₂, hC₂, hevM⟩ := hM b E np τ m T s h K Vs hD R
  obtain ⟨C₁, ρ, hC₁, hρ0, hρ1, hevC⟩ := hC b E np τ m T s h K Vs hD R
  refine ⟨C₁ + 2 * C₂, ρ, by linarith, hρ0, hρ1, ?_⟩
  filter_upwards [hL b E np τ m T s h K Vs hD R, hevM, hevC, eventually_ge_atTop 1]
    with W hWL hWM hWC hW1 j hj ij kl
  exact (genConjStep_le b E s h τ m R W j (Vs W) ij kl (hWL j hj _) (hWL j hj _)).trans
    (gen_stepBound_add_meanSq τ hρ0 hC₁ hC₂ hW1 j (hWC j hj ij kl) (hWM j hj _) (hWM j hj _))

/-- **`ComplexClosedSummed` from the finest `𝒦` estimates and the other halves.** -/
theorem complexClosedSummed_of_cov (hGD : GenReqGramDrift) (hGB : GenReqGramBracket)
    (hB : GenReqBirth) (hKD : KStepDrift) (hL : GenStepMemL2) (hM : GenStepMeanL2)
    (hKB : KStepCov) (hKC : KStepConjCov) : ComplexClosedSummed :=
  complexClosedSummed_of_steps hGD hGB hB hKD (kStepBracket_of_cov hL hM hKB)
    (kStepConj_of_cov hL hM hKC)

end BlockBand.SourceProcess.PhysApprox.B3
