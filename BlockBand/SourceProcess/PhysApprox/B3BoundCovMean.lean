module

public import BlockBand.SourceProcess.PhysApprox.B3BoundCovLayer
public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanGram

/-!
# The closed one-step mean structure without the `err⁶` term

* **`B3LayerMeanAt2`** (restated): an error field with `‖err‖₂ ≤ C/W` and, a.e., the drift
  integrand is at most `C(|err|·S_j + err² + W^{-3/2})`. Its consumer only uses Hölder `(2, 2)`
  with `S_j` and `‖err²‖₁ = ‖err‖₂²`;
  estimates **`B3ClosedGramLayerMean2`**, **`B3ClosedKLayerMean2`**;
* `b3_driftStep_le_of_layer2`, `decay_step_arith2`, `b3_stepBound_of_layer_decay2` (versions of
  `b3_driftStep_le_of_layer`, `decay_step_arith`, `b3_stepBound_of_layer_decay` without the sixth
  power), hence **`kStepDrift_of_decay2`** and
  **`gramSumStepDrift_of_decay2`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedSum
open BlockBand.SourceProcess.ContractingWords (currentOf layerErr layerRem)
open BlockBand.SourceProcess.ClosedSummedProof (contrGram incr layerGram sigD sigVals
  FreshFour integrable_layerGramEntry)
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal

/-!
## The restated mean structure
-/

/-- **The closed one-step mean structure without `err⁶`**: an error field with `‖err‖₂ ≤ C/W`
and, a.e., the drift integrand of `genDriftStep` is at most `C(|err|·S_j + err² + W^{-3/2})`. -/
def B3LayerMeanAt2 (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (C : ℝ) (c : CIdx K np) :
    Prop :=
  ∃ err : ProbedPath W np × ℝ → ℝ,
    eLpNorm err 2 (closedLaw b W np) ≤ ENNReal.ofReal (C / W) ∧
    ∀ᵐ y ∂closedLaw b W np,
      ‖(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
          (closedLaw b W np)[(b3Alive b E s h τ m R W j Vs).indicator
              (b3dX b E s h τ m W j Vs c) | b3Sigma W j np] y -
            (W : ℂ)⁻¹ * cDrift b E c (b3ClosedGramAt b E s h τ m W j Vs y)) y‖ ≤
        C * (‖err y‖ * b3ContrSum b E s h τ m R W j Vs y + ‖err y‖ ^ 2 +
          1 / ((W : ℝ) * Real.sqrt W))

/-- **The closed one-step Gram mean structure without `err⁶`.** -/
def B3ClosedGramLayerMean2 : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
    ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
      B3LayerMeanAt2 b E s h τ m R W j (Vs W) C (Sum.inl e : CIdx K np)

/-- **The closed one-step `𝒦` mean structure without `err⁶`.** -/
def B3ClosedKLayerMean2 : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ ij : Fin np × Fin np,
      B3LayerMeanAt2 b E s h τ m R W j (Vs W) C (Sum.inr ij : CIdx K np)

/-!
## The per-step reduction
-/

/-- The arithmetic of the per-step bound (`decay_step_arith` without the sixth power). -/
theorem decay_step_arith2 {C N D r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) {W : ℕ} (hW : 1 ≤ W) :
    C * (C / W * (N * (D * (r + 1 / Real.sqrt W))) + (C / W) ^ 2 +
        1 / ((W : ℝ) * Real.sqrt W)) ≤
      C * (C * N * D + C ^ 2 + 1) / W * (r + 1 / Real.sqrt W) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hsq : 0 < Real.sqrt W := Real.sqrt_pos.2 hW0
  set w : ℝ := 1 / Real.sqrt W with hwdef
  set u : ℝ := 1 / (W : ℝ) with hudef
  have hw0 : 0 < w := by positivity
  have hw1 : w ≤ 1 := by
    rw [hwdef, div_le_one hsq]; exact Real.one_le_sqrt.2 hW1
  have hu : u = w * w := by
    rw [hudef, hwdef, div_mul_div_comm, one_mul, Real.mul_self_sqrt hW0.le]
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hu1 : u ≤ w := by rw [hu]; nlinarith
  have hCW : C / W = C * u := by rw [hudef]; ring
  have hWW : 1 / ((W : ℝ) * Real.sqrt W) = u * w := by
    rw [hudef, hwdef, div_mul_div_comm, one_mul]
  have hR : C * (C * N * D + C ^ 2 + 1) / W * (r + w) =
      C * ((C * N * D + C ^ 2 + 1) * (u * (r + w))) := by rw [hudef]; ring
  rw [hCW, hWW, hR]
  refine mul_le_mul_of_nonneg_left ?_ hC
  have hrw : u ≤ r + w := by linarith
  have h2 : u ^ 2 ≤ u * (r + w) := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hrw hu0
  have hC2 : (C * u) ^ 2 ≤ C ^ 2 * (u * (r + w)) := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hw' : u * w ≤ u * (r + w) := mul_le_mul_of_nonneg_left (by linarith) hu0
  have h1 : C * u * (N * (D * (r + w))) = C * N * D * (u * (r + w)) := by ring
  nlinarith [h1, hC2, hw']

/-- **The per-step drift bound from the restated layer structure** and an `L²` bound on the
contracting coordinates. -/
theorem b3_driftStep_le_of_layer2 (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) {W : ℕ}
    (j : ℕ) {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) {c : CIdx K np} (hL : B3LayerMeanAt2 b E s h τ m R W j Vs C c)
    (hQ : ∀ x : ContrIdx K np,
      eLpNorm (b3ContrAlive b E s h τ m R W j Vs x) 2 (closedLaw b W np) ≤ ENNReal.ofReal D) :
    genDriftStep b E s h τ m R W j Vs c ≤
      ENNReal.ofReal (C * (C / W * ((Fintype.card (ContrIdx K np) : ℝ) * D) + (C / W) ^ 2 +
        1 / ((W : ℝ) * Real.sqrt W))) := by
  set μ := closedLaw b W np
  set N : ℝ := (Fintype.card (ContrIdx K np) : ℝ)
  set κ : ℝ := 1 / ((W : ℝ) * Real.sqrt W)
  have hκ : 0 ≤ κ := by positivity
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hCW : 0 ≤ C / W := div_nonneg hC (Nat.cast_nonneg _)
  obtain ⟨err, herr2, hpt⟩ := hL
  have herrm : AEStronglyMeasurable err μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top herr2)
  have hQm : ∀ x, AEStronglyMeasurable (b3ContrAlive b E s h τ m R W j Vs x) μ := fun x =>
    aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hQ x))
  set S : ProbedPath W np × ℝ → ℝ := b3ContrSum b E s h τ m R W j Vs
  have hS : eLpNorm S 2 μ ≤ ENNReal.ofReal (N * D) := by
    have hSeq : S = ∑ x : ContrIdx K np, fun y => ‖b3ContrAlive b E s h τ m R W j Vs x y‖ := by
      funext y; simp only [S, b3ContrSum, Finset.sum_apply]
    rw [hSeq]
    refine (eLpNorm_sum_le (by norm_num)).trans ?_
    calc ∑ x : ContrIdx K np, eLpNorm (fun y => ‖b3ContrAlive b E s h τ m R W j Vs x y‖) 2 μ
        = ∑ x : ContrIdx K np, eLpNorm (b3ContrAlive b E s h τ m R W j Vs x) 2 μ :=
          Finset.sum_congr rfl fun x _ => eLpNorm_norm _ (hQm x)
      _ ≤ ∑ _x : ContrIdx K np, ENNReal.ofReal D := Finset.sum_le_sum fun x _ => hQ x
      _ = ENNReal.ofReal (N * D) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul hN,
            ENNReal.ofReal_natCast]
  have he1 : eLpNorm (fun y => ‖err y‖ * S y) 1 μ ≤
      ENNReal.ofReal (C / W) * ENNReal.ofReal (N * D) := by
    refine (decay_eLpNorm_mul_le _ _).trans ?_
    rw [eLpNorm_norm err herrm]
    exact mul_le_mul' herr2 hS
  have he2 : eLpNorm (fun y => ‖err y‖ ^ 2) 1 μ ≤ ENNReal.ofReal ((C / W) ^ 2) :=
    decay_eLpNorm_pow_le herrm 2 (by norm_num) hCW (by simpa using herr2)
  have he4 : eLpNorm (fun _ : ProbedPath W np × ℝ => κ) 1 μ = ENNReal.ofReal κ := by
    rw [eLpNorm_const _ one_ne_zero (IsProbabilityMeasure.ne_zero μ), measure_univ,
      ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal hκ]
  set G : ProbedPath W np × ℝ → ℝ := fun y => C * (‖err y‖ * S y + ‖err y‖ ^ 2 + κ)
  have hGeq : G = C • ((fun y => ‖err y‖ * S y) + (fun y => ‖err y‖ ^ 2) + fun _ => κ) := by
    funext y; simp only [G, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have hstep1 : genDriftStep b E s h τ m R W j Vs c ≤ ∫⁻ y, ‖G y‖ₑ ∂μ := by
    unfold genDriftStep
    refine lintegral_mono_ae (hpt.mono fun y hy => ?_)
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hy.trans (Real.le_norm_self _))
  refine hstep1.trans (lintegral_enorm_le_eLpNorm_one.trans ?_)
  rw [hGeq, eLpNorm_const_smul, Real.enorm_eq_ofReal hC]
  have hsum : eLpNorm ((fun y => ‖err y‖ * S y) + (fun y => ‖err y‖ ^ 2) + fun _ => κ) 1 μ ≤
      ENNReal.ofReal (C / W) * ENNReal.ofReal (N * D) + ENNReal.ofReal ((C / W) ^ 2) +
        ENNReal.ofReal κ := by
    refine (eLpNorm_add_le le_rfl).trans ?_
    rw [he4]
    exact add_le_add ((eLpNorm_add_le le_rfl).trans (add_le_add he1 he2)) le_rfl
  refine (mul_le_mul' le_rfl hsum).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul hCW, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) hκ, ← ENNReal.ofReal_mul hC]

/-- The per-step `SummedStep` bound from the restated layer structure and the decay at `p = 2`. -/
theorem b3_stepBound_of_layer_decay2 (hD : B3ClosedContrDecay) {b E : ℝ} {np : ℕ}
    {τ m : Fin np → ℝ} {T s h : ℝ} {K : ℕ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hF : FrameDomain b E τ m T s h K Vs) (R : ℝ) (P : CIdx K np → Prop)
    (hL : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ c, P c →
      B3LayerMeanAt2 b E s h τ m R W j (Vs W) C c) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ c, P c →
      genDriftStep b E s h τ m R W j (Vs W) c ≤
        ENNReal.ofReal (C / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W)) := by
  obtain ⟨CL, hCL, hevL⟩ := hL
  obtain ⟨C₂, ρ, hC₂, hρ0, hρ1, hevD⟩ := hD b E np τ m T s h K Vs hF R 2 (by norm_num)
  set N : ℝ := (Fintype.card (ContrIdx K np) : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨CL * (CL * N * C₂ + CL ^ 2 + 1), ρ, by positivity, hρ0, hρ1, ?_⟩
  filter_upwards [hevL, hevD, eventually_ge_atTop 1] with W hWL hWD hW1 j hj c hc
  have hj' := hj
  simp only [genNoBirthSteps, Finset.mem_filter, Finset.mem_Ico] at hj'
  have hr : 0 ≤ genStepRate ρ s τ W j := genStepRate_nonneg hρ0 s τ W j
  have hQ : ∀ x : ContrIdx K np, eLpNorm (b3ContrAlive b E s h τ m R W j (Vs W) x) 2
      (closedLaw b W np) ≤ ENNReal.ofReal (C₂ * (genStepRate ρ s τ W j + 1 / Real.sqrt W)) :=
    fun x => by
      have := hWD j hj'.1.1 hj'.1.2.le x.1 x.2.1 x.2.2
      rwa [ENNReal.ofReal_ofNat] at this
  refine (b3_driftStep_le_of_layer2 b E s h τ m R j hCL (by positivity) (hWL j hj c hc)
    hQ).trans (ENNReal.ofReal_le_ofReal ?_)
  exact decay_step_arith2 hCL hr hW1

/-!
## The two drift estimates
-/

/-- **`KStepDrift` from the closed decay and the restated `𝒦` mean structure.** -/
theorem kStepDrift_of_decay2 (hD : B3ClosedContrDecay) (hK : B3ClosedKLayerMean2) :
    KStepDrift := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := b3_stepBound_of_layer_decay2 hD hF R
    (fun c => ∃ ij : Fin np × Fin np, c = Sum.inr ij)
    (by
      obtain ⟨C, hC, hev⟩ := hK b E np τ m T s h K Vs hF R
      exact ⟨C, hC, hev.mono fun W hW j hj c ⟨ij, hij⟩ => hij ▸ hW j hj ij⟩)
  exact ⟨C, ρ, hC, hρ0, hρ1, hev.mono fun W hW j hj ij => hW j hj _ ⟨ij, rfl⟩⟩

/-- **`GramSumStepDrift` from the closed decay and the restated Gram mean structure.** -/
theorem gramSumStepDrift_of_decay2 (hD : B3ClosedContrDecay) (hG : B3ClosedGramLayerMean2) :
    GramSumStepDrift := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := b3_stepBound_of_layer_decay2 hD hF R
    (fun c => ∃ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np), c = Sum.inl e)
    (by
      obtain ⟨C, hC, hev⟩ := hG b E np τ m T s h K Vs hF R
      exact ⟨C, hC, hev.mono fun W hW j hj c ⟨e, he⟩ => he ▸ hW j hj e⟩)
  exact ⟨C, ρ, hC, hρ0, hρ1, hev.mono fun W hW j hj e => hW j hj _ ⟨e, rfl⟩⟩

/-!
## The Gram layer mean from the chain
-/

/-- **`B3ClosedGramLayerMean2` from the closed chain and the `p = 4` moment of `e`.** -/
theorem b3ClosedGramLayerMean2_of_chain (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hC : B3ClosedChainPin)
    (hEr : CovErrMoments2 b3CovErr) : B3ClosedGramLayerMean2 := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hF.1
  have hh : h ^ 2 < 1 := by nlinarith [hF.2.2.2.1, hF.2.2.2.2.1]
  set M := b3ErrBound b E with hMdef
  have hM0 : 0 ≤ M := b3ErrBound_nonneg hb hE1 hE2
  obtain ⟨hκ, hE⟩ := cov_bulk hE1 hE2
  set R' := max R 0 with hR'
  obtain ⟨C₁, W₁, hC₁, hLD⟩ :=
    ClosedSummedProof.gram_layer_drift hGA hLp hP hb0 hb hκ R'
  obtain ⟨C₄, W₂, hC₄, hfp⟩ := ClosedSummedProof.fresh_pow_bound hGA hb0 hb hκ
  obtain ⟨C₂, hC₂, hch⟩ := hC b E np τ m T s h K Vs hF R
  obtain ⟨C₃, hC₃, herr⟩ := hEr b E np τ m T s h K Vs hF R
  set C := max (max (C₁ * C₂) (C₁ * (1 + M ^ 4))) C₃ with hCdef
  have hC0 : 0 ≤ C := le_max_of_le_right hC₃
  have hCa : C₁ * C₂ ≤ C := le_max_of_le_left (le_max_left _ _)
  have hCb : C₁ * (1 + M ^ 4) ≤ C := le_max_of_le_left (le_max_right _ _)
  have hCc : C₃ ≤ C := le_max_right _ _
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hch, herr, eventually_ge_atTop (max W₁ (max W₂ 1)), hF.2.2.2.2.2] with
    W hchW herrW hW hVs j hj e
  simp only [max_le_iff] at hW
  obtain ⟨hW1, hW2, hW0⟩ := hW
  have hjc : closeLen s W ≤ j := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).1
  have hVm : Measurable (Vs W) :=
    hVs.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hVinv : ∀ ω, Vs W (extPast W j (pastCoords W j ω)) = Vs W ω :=
    fun ω => growth_fun_extPast hjc hVs.1 ω
  obtain ⟨XX, hXm, hXinv, hXae⟩ := hchW j hj
  set μ := closedLaw b W np
  set A := b3Alive b E s h τ m R W j (Vs W)
  have h4 : FreshFour b W E C₄ := fun X' hX' => hfp W hW2 E hE X' hX'
  have hce := condExp_b3_chain (τ := τ) (m := m) (h := h) (R := R) (R' := R')
    (by linarith : b < 1) hE1 hE2 hjc (le_max_left R 0) hVm hVinv hXm hXinv
    (by filter_upwards [hXae] with y hy hyA
        exact ⟨(hy hyA).1, (hy hyA).2.2.1⟩)
    (R' * (C₄ + 2)) e
    (fun X' hX' V' hV' => ClosedSummedProof.lintegral_incr_le (h4 X' hX').1 (h4 X' hX').2 V'
      (le_max_right R 0) hV' e)
  refine ⟨A.indicator (b3CovErr b E np τ m s h K W (Vs W) j), ?_, ?_⟩
  · exact ((eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)).trans (herrW j hj)).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hCc (by positivity)))
  filter_upwards [hce, hXae, ae_b3CovErr_le hb0 hb hE1 hE2 s h hh τ m hW0 (Vs W) j]
    with y hy hX hbdd
  by_cases hyA : y ∈ A
  · rw [Set.indicator_of_mem hyA, hy hyA, Set.indicator_of_mem hyA]
    obtain ⟨hH, hNS, -, hCur, hCG⟩ := hX hyA
    set XY := XX y
    set V := b3ClosedFrameAt b E s h τ m W j (Vs W) y
    have hTr : (Vᴴ * V).trace.re ≤ R' := (hyA.2 j hjc le_rfl).le.trans (le_max_left R 0)
    have hJ : currentOf b E XY = V * sigD (sigVals K (Fin np)) * Vᴴ := by
      rw [hCur, ClosedSummedProof.srcSignature_eq]
    have hbd := hLD W hW1 E hE (b3Jet b E) (b3Jet_spec hb0 hb hE1 hE2) XY hH V
      (sigVals K (Fin np)) (ClosedSummedProof.abs_sigVals_le K (Fin np)) hJ hTr e
    have hi : ∫ f, incr b E XY V e f ∂freshLaw W b =
        (∫ f, gramEntry e (layerGram b E XY V f) ∂freshLaw W b) -
          gramEntry e (gramPair (nearProjection W) V) := by
      rw [show (fun f => incr b E XY V e f) = fun f => gramEntry e (layerGram b E XY V f) -
        gramEntry e (gramPair (nearProjection W) V) from rfl,
        integral_sub (integrable_layerGramEntry h4 hH V e) (integrable_const _),
        integral_const, probReal_univ, one_smul]
    have hLE : layerErr b E (b3Jet b E) XY = b3CovErr b E np τ m s h K W (Vs W) j y :=
      layerErr_eq_b3LayerErrX hb0 hb hE1 hE2 (b3Jet_spec hb0 hb hE1 hE2) hNS
    have hZ : b3CovZ b E np τ m s h K W (Vs W) j y =
        b3ContrSum b E s h τ m R W j (Vs W) y := by
      simp only [b3CovZ, b3ContrSum, b3ContrAlive]
      exact Finset.sum_congr rfl fun x _ => by rw [Set.indicator_of_mem hyA]
    have hdrift : cDrift b E (Sum.inl e : CIdx K np) (b3ClosedGramAt b E s h τ m W j (Vs W) y) =
        gramDriftEntry (transportD0 b E) (sigD (sigVals K (Fin np))) e
          (gramPair (nearProjection W) V) := by
      simp only [cDrift, ClosedSummedProof.srcSignature_eq]
      rfl
    rw [hi, hdrift]
    rw [hLE] at hbd
    set ev := b3CovErr b E np τ m s h K W (Vs W) j y
    set S := b3ContrSum b E s h τ m R W j (Vs W) y
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hG0 : 0 ≤ contrGram b E XY V := ClosedSummedProof.contrGram_nonneg b E XY V
    have hev : ev ≤ ‖ev‖ := Real.le_norm_self ev
    have hGZ : contrGram b E XY V ≤ C₂ * S := by rw [← hZ]; exact hCG
    have h6 : |ev| ^ 6 = ev ^ 6 := by
      rw [← abs_pow]; exact abs_of_nonneg (by positivity)
    have hrem : layerRem W 1 ev = 1 / ((W : ℝ) * Real.sqrt W) + ‖ev‖ ^ 2 + ‖ev‖ ^ 6 := by
      rw [layerRem, Real.norm_eq_abs, sq_abs, h6, one_div, mul_inv, div_eq_mul_inv]
    refine hbd.trans ?_
    rw [hrem]
    have hW0' : (0 : ℝ) ≤ 1 / ((W : ℝ) * Real.sqrt W) := by positivity
    have hA1 : C₁ * ev * contrGram b E XY V ≤ C * (‖ev‖ * S) :=
      calc C₁ * ev * contrGram b E XY V ≤ C₁ * ‖ev‖ * (C₂ * S) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hev hC₁) hGZ hG0 ?_
            exact mul_nonneg hC₁ (norm_nonneg _)
        _ = (C₁ * C₂) * (‖ev‖ * S) := by ring
        _ ≤ C * (‖ev‖ * S) := mul_le_mul_of_nonneg_right hCa
            (mul_nonneg (norm_nonneg _) hS0)
    have hn6 : ‖ev‖ ^ 6 ≤ M ^ 4 * ‖ev‖ ^ 2 := by
      have hnM : ‖ev‖ ≤ M := by rw [Real.norm_of_nonneg hbdd.1]; exact hbdd.2
      have e6 : ‖ev‖ ^ 6 = ‖ev‖ ^ 4 * ‖ev‖ ^ 2 := by ring
      rw [e6]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnM 4)
        (sq_nonneg _)
    have hA2 : C₁ * (1 / ((W : ℝ) * Real.sqrt W) + ‖ev‖ ^ 2 + ‖ev‖ ^ 6) ≤
        C * (1 / ((W : ℝ) * Real.sqrt W) + ‖ev‖ ^ 2) := by
      have hM4 : 0 ≤ M ^ 4 := by positivity
      have hin : 1 / ((W : ℝ) * Real.sqrt W) + ‖ev‖ ^ 2 + ‖ev‖ ^ 6 ≤
          (1 + M ^ 4) * (1 / ((W : ℝ) * Real.sqrt W) + ‖ev‖ ^ 2) := by
        have e2 : (1 + M ^ 4) * (1 / ((W : ℝ) * Real.sqrt W) + ‖ev‖ ^ 2) =
            1 / ((W : ℝ) * Real.sqrt W) + ‖ev‖ ^ 2 + M ^ 4 * ‖ev‖ ^ 2 +
              M ^ 4 * (1 / ((W : ℝ) * Real.sqrt W)) := by ring
        rw [e2]
        have := mul_nonneg hM4 hW0'
        linarith
      calc C₁ * (1 / ((W : ℝ) * Real.sqrt W) + ‖ev‖ ^ 2 + ‖ev‖ ^ 6)
          ≤ C₁ * ((1 + M ^ 4) * (1 / ((W : ℝ) * Real.sqrt W) + ‖ev‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hin hC₁
        _ = (C₁ * (1 + M ^ 4)) * (1 / ((W : ℝ) * Real.sqrt W) + ‖ev‖ ^ 2) := by ring
        _ ≤ C * (1 / ((W : ℝ) * Real.sqrt W) + ‖ev‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hCb (by positivity)
    calc C₁ * ev * contrGram b E XY V + C₁ * (1 / ((W : ℝ) * Real.sqrt W) + ‖ev‖ ^ 2 + ‖ev‖ ^ 6)
        ≤ C * (‖ev‖ * S) + C * (1 / ((W : ℝ) * Real.sqrt W) + ‖ev‖ ^ 2) :=
          add_le_add hA1 hA2
      _ = C * (‖ev‖ * S + ‖ev‖ ^ 2 + 1 / ((W : ℝ) * Real.sqrt W)) := by ring
  · rw [Set.indicator_of_notMem hyA, norm_zero]
    have : 0 ≤ b3ContrSum b E s h τ m R W j (Vs W) y :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    positivity

/-- **`ComplexClosedSummed` through the closed chain at `N = 2`, with both drift estimates from
the restated mean structures.** -/
theorem complexClosedSummed_of_chain2_decay (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hB : GenReqBirth)
    (hCh : B3ClosedChainPin) (hKM : B3ClosedKLayerMean2)
    (hKG : CovLayerHypKG2 b3CovErr b3CovZ) (hE : CovErrMoments2 b3CovErr)
    (hD : B3ClosedContrDecay) : ComplexClosedSummed :=
  complexClosedSummed_of_chain2 hGA hLp hP
    (gramSumStepDrift_of_decay2 hD (b3ClosedGramLayerMean2_of_chain hGA hLp hP hCh hE)) hB
    (kStepDrift_of_decay2 hD hKM) hCh hKG hE hD

end BlockBand.SourceProcess.PhysApprox.B3
