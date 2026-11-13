module

public import BlockBand.SourceProcess.PhysApprox.B3DecayDefs

/-!
# `KStepDrift` and `GramSumStepDrift` from the closed decay

* `b3_driftStep_le_of_layer`: the layer bound and `‖1_{A_j}Q‖_{L²} ≤ D` give
  `genDriftStep c ≤ C(C/W·N·D + (C/W)² + (C/W)⁶ + W^{-3/2})`, `N = 4|SrcCol|²`.
* **`kStepDrift_of_decay : B3ClosedContrDecay → B3ClosedKLayerMean → KStepDrift`**.
* **`gramSumStepDrift_of_decay : B3ClosedContrDecay → B3ClosedGramLayerMean → GramSumStepDrift`**.
* `b3ClosedContrCesaro_of_decay`: the decay implies its Cesàro form.
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
## The closed one-step mean structure
-/

/-- The index set of the closed contracting coordinates. -/
abbrev ContrIdx (K np : ℕ) := Fin 4 × SrcCol K (Fin np) × SrcCol K (Fin np)

/-- The alive closed contracting coordinate of index `x` at length `j`. -/
def b3ContrAlive (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (x : ContrIdx K np) :
    ProbedPath W np × ℝ → ℂ :=
  (b3Alive b E s h τ m R W j Vs).indicator (b3ContrCoord b E s h τ m W j Vs x.1 x.2.1 x.2.2)

/-- The sum `S_j = Σ_{σ,k,l}‖1_{A_j}Q^σ_{kl}(j)‖` of the alive closed contracting coordinates. -/
def b3ContrSum (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (y : ProbedPath W np × ℝ) : ℝ :=
  ∑ x : ContrIdx K np, ‖b3ContrAlive b E s h τ m R W j Vs x y‖

/-- **The closed one-step mean structure of coordinate `c` at step `j`**, with constant `C`: an
error field `err` with `‖err‖_{L⁶} ≤ C/W` and, a.e., the drift integrand of `genDriftStep` is at
most `C(|err|·S_j + err² + err⁶ + W^{-3/2})`. -/
def B3LayerMeanAt (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (C : ℝ) (c : CIdx K np) :
    Prop :=
  ∃ err : ProbedPath W np × ℝ → ℝ,
    eLpNorm err 6 (closedLaw b W np) ≤ ENNReal.ofReal (C / W) ∧
    ∀ᵐ y ∂closedLaw b W np,
      ‖(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
          (closedLaw b W np)[(b3Alive b E s h τ m R W j Vs).indicator
              (b3dX b E s h τ m W j Vs c) | b3Sigma W j np] y -
            (W : ℂ)⁻¹ * cDrift b E c (b3ClosedGramAt b E s h τ m W j Vs y)) y‖ ≤
        C * (‖err y‖ * b3ContrSum b E s h τ m R W j Vs y + ‖err y‖ ^ 2 + ‖err y‖ ^ 6 +
          1 / ((W : ℝ) * Real.sqrt W))

/-- **The closed one-step Gram mean structure** (`LayerDrift` at the closed state). -/
def B3ClosedGramLayerMean : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
    ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
      B3LayerMeanAt b E s h τ m R W j (Vs W) C (Sum.inl e : CIdx K np)

/-- **The closed one-step `𝒦` mean structure** (for the closed system). -/
def B3ClosedKLayerMean : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ ij : Fin np × Fin np,
      B3LayerMeanAt b E s h τ m R W j (Vs W) C (Sum.inr ij : CIdx K np)

/-!
## Two `eLpNorm` facts
-/

section Generic

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- `‖ |f|^n ‖_{L¹} ≤ a^n` from `‖f‖_{Lⁿ} ≤ a`. -/
theorem decay_eLpNorm_pow_le {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (n : ℕ) (hn : 0 < n)
    {a : ℝ} (ha : 0 ≤ a) (h : eLpNorm f n μ ≤ ENNReal.ofReal a) :
    eLpNorm (fun y => ‖f y‖ ^ n) 1 μ ≤ ENNReal.ofReal (a ^ n) := by
  have hq : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : (fun y => ‖f y‖ ^ n) = fun y => ‖f y‖ ^ (n : ℝ) := by
    funext y; rw [Real.rpow_natCast]
  rw [e1, eLpNorm_norm_rpow f hf hq, one_mul, ENNReal.ofReal_natCast]
  calc eLpNorm f n μ ^ (n : ℝ) ≤ ENNReal.ofReal a ^ (n : ℝ) :=
        ENNReal.rpow_le_rpow h hq.le
    _ = ENNReal.ofReal (a ^ n) := by
        rw [ENNReal.ofReal_rpow_of_nonneg ha hq.le, Real.rpow_natCast]

/-- Hölder `L² × L² → L¹` for real functions. -/
theorem decay_eLpNorm_mul_le (f g : α → ℝ) :
    eLpNorm (fun y => f y * g y) 1 μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm_of_pos (μ := μ) (p := 2) (q := 2) (r := 1)
    (f := f) (g := g) (fun x y : ℝ => x * y) 1 continuous_mul
    (Eventually.of_forall fun y => by simp [norm_mul]) one_pos
  simpa using h

end Generic

/-!
## The per-step reduction
-/

/-- The arithmetic of the per-step bound. -/
theorem decay_step_arith {C N D r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    {W : ℕ} (hW : 1 ≤ W) :
    C * (C / W * (N * (D * (r + 1 / Real.sqrt W))) + (C / W) ^ 2 + (C / W) ^ 6 +
        1 / ((W : ℝ) * Real.sqrt W)) ≤
      C * (C * N * D + C ^ 2 + C ^ 6 + 1) / W * (r + 1 / Real.sqrt W) := by
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
  have hu1' : u ≤ 1 := hu1.trans hw1
  have hCW : C / W = C * u := by rw [hudef]; ring
  have hWW : 1 / ((W : ℝ) * Real.sqrt W) = u * w := by
    rw [hudef, hwdef, div_mul_div_comm, one_mul]
  have hR : C * (C * N * D + C ^ 2 + C ^ 6 + 1) / W * (r + w) =
      C * ((C * N * D + C ^ 2 + C ^ 6 + 1) * (u * (r + w))) := by rw [hudef]; ring
  rw [hCW, hWW, hR]
  refine mul_le_mul_of_nonneg_left ?_ hC
  have hrw : u ≤ r + w := by linarith
  have h2 : u ^ 2 ≤ u * (r + w) := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hrw hu0
  have h6 : u ^ 6 ≤ u * (r + w) := by
    have : u ^ 6 ≤ u ^ 2 := pow_le_pow_of_le_one hu0 hu1' (by norm_num)
    exact this.trans h2
  have hC2 : (C * u) ^ 2 ≤ C ^ 2 * (u * (r + w)) := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hC6 : (C * u) ^ 6 ≤ C ^ 6 * (u * (r + w)) := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left h6 (by positivity)
  have hw' : u * w ≤ u * (r + w) := mul_le_mul_of_nonneg_left (by linarith) hu0
  have h1 : C * u * (N * (D * (r + w))) = C * N * D * (u * (r + w)) := by ring
  nlinarith [h1, hC2, hC6, hw']

/-- **The per-step drift bound from the layer structure and an `L²` bound on the contracting
coordinates.** -/
theorem b3_driftStep_le_of_layer (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) {W : ℕ}
    (j : ℕ) {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) {c : CIdx K np} (hL : B3LayerMeanAt b E s h τ m R W j Vs C c)
    (hQ : ∀ x : ContrIdx K np,
      eLpNorm (b3ContrAlive b E s h τ m R W j Vs x) 2 (closedLaw b W np) ≤ ENNReal.ofReal D) :
    genDriftStep b E s h τ m R W j Vs c ≤
      ENNReal.ofReal (C * (C / W * ((Fintype.card (ContrIdx K np) : ℝ) * D) + (C / W) ^ 2 +
        (C / W) ^ 6 + 1 / ((W : ℝ) * Real.sqrt W))) := by
  set μ := closedLaw b W np
  set N : ℝ := (Fintype.card (ContrIdx K np) : ℝ)
  set κ : ℝ := 1 / ((W : ℝ) * Real.sqrt W)
  have hκ : 0 ≤ κ := by positivity
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hCW : 0 ≤ C / W := div_nonneg hC (Nat.cast_nonneg _)
  obtain ⟨err, herr, hpt⟩ := hL
  have herrm : AEStronglyMeasurable err μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top herr)
  have hQm : ∀ x, AEStronglyMeasurable (b3ContrAlive b E s h τ m R W j Vs x) μ := fun x =>
    aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hQ x))
  set S : ProbedPath W np × ℝ → ℝ := b3ContrSum b E s h τ m R W j Vs
  -- `‖S‖₂ ≤ N D`
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
  -- `‖err‖₂ ≤ C/W`
  have herr2 : eLpNorm err 2 μ ≤ ENNReal.ofReal (C / W) :=
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)).trans herr
  have he1 : eLpNorm (fun y => ‖err y‖ * S y) 1 μ ≤
      ENNReal.ofReal (C / W) * ENNReal.ofReal (N * D) := by
    refine (decay_eLpNorm_mul_le _ _).trans ?_
    rw [eLpNorm_norm err herrm]
    exact mul_le_mul' herr2 hS
  have he2 : eLpNorm (fun y => ‖err y‖ ^ 2) 1 μ ≤ ENNReal.ofReal ((C / W) ^ 2) :=
    decay_eLpNorm_pow_le herrm 2 (by norm_num) hCW (by simpa using herr2)
  have he3 : eLpNorm (fun y => ‖err y‖ ^ 6) 1 μ ≤ ENNReal.ofReal ((C / W) ^ 6) :=
    decay_eLpNorm_pow_le herrm 6 (by norm_num) hCW (by simpa using herr)
  have he4 : eLpNorm (fun _ : ProbedPath W np × ℝ => κ) 1 μ = ENNReal.ofReal κ := by
    rw [eLpNorm_const _ one_ne_zero (IsProbabilityMeasure.ne_zero μ), measure_univ,
      ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal hκ]
  set G : ProbedPath W np × ℝ → ℝ := fun y =>
    C * (‖err y‖ * S y + ‖err y‖ ^ 2 + ‖err y‖ ^ 6 + κ)
  have hGeq : G = C • ((fun y => ‖err y‖ * S y) + (fun y => ‖err y‖ ^ 2) +
      (fun y => ‖err y‖ ^ 6) + fun _ => κ) := by
    funext y; simp only [G, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have hstep1 : genDriftStep b E s h τ m R W j Vs c ≤ ∫⁻ y, ‖G y‖ₑ ∂μ := by
    unfold genDriftStep
    refine lintegral_mono_ae (hpt.mono fun y hy => ?_)
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hy.trans (Real.le_norm_self _))
  refine hstep1.trans (lintegral_enorm_le_eLpNorm_one.trans ?_)
  rw [hGeq, eLpNorm_const_smul, Real.enorm_eq_ofReal hC]
  have hsum : eLpNorm ((fun y => ‖err y‖ * S y) + (fun y => ‖err y‖ ^ 2) +
      (fun y => ‖err y‖ ^ 6) + fun _ => κ) 1 μ ≤
      ENNReal.ofReal (C / W) * ENNReal.ofReal (N * D) + ENNReal.ofReal ((C / W) ^ 2) +
        ENNReal.ofReal ((C / W) ^ 6) + ENNReal.ofReal κ := by
    refine (eLpNorm_add_le le_rfl).trans ?_
    rw [he4]
    refine add_le_add ((eLpNorm_add_le le_rfl).trans ?_) le_rfl
    exact add_le_add ((eLpNorm_add_le le_rfl).trans (add_le_add he1 he2)) he3
  refine (mul_le_mul' le_rfl hsum).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul hCW, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) hκ, ← ENNReal.ofReal_mul hC]

/-- The per-step `SummedStep` bound from the layer structure and the decay at `p = 2`. -/
theorem b3_stepBound_of_layer_decay (hD : B3ClosedContrDecay) {b E : ℝ} {np : ℕ}
    {τ m : Fin np → ℝ} {T s h : ℝ} {K : ℕ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hF : FrameDomain b E τ m T s h K Vs) (R : ℝ) (P : CIdx K np → Prop)
    (hL : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ c, P c →
      B3LayerMeanAt b E s h τ m R W j (Vs W) C c) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ c, P c →
      genDriftStep b E s h τ m R W j (Vs W) c ≤
        ENNReal.ofReal (C / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W)) := by
  obtain ⟨CL, hCL, hevL⟩ := hL
  obtain ⟨C₂, ρ, hC₂, hρ0, hρ1, hevD⟩ := hD b E np τ m T s h K Vs hF R 2 (by norm_num)
  set N : ℝ := (Fintype.card (ContrIdx K np) : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨CL * (CL * N * C₂ + CL ^ 2 + CL ^ 6 + 1), ρ, by positivity, hρ0, hρ1, ?_⟩
  filter_upwards [hevL, hevD, eventually_ge_atTop 1] with W hWL hWD hW1 j hj c hc
  have hj' := hj
  simp only [genNoBirthSteps, mem_filter, mem_Ico] at hj'
  have hr : 0 ≤ genStepRate ρ s τ W j := genStepRate_nonneg hρ0 s τ W j
  have hQ : ∀ x : ContrIdx K np, eLpNorm (b3ContrAlive b E s h τ m R W j (Vs W) x) 2
      (closedLaw b W np) ≤ ENNReal.ofReal (C₂ * (genStepRate ρ s τ W j + 1 / Real.sqrt W)) :=
    fun x => by
      have := hWD j hj'.1.1 hj'.1.2.le x.1 x.2.1 x.2.2
      rwa [ENNReal.ofReal_ofNat] at this
  refine (b3_driftStep_le_of_layer b E s h τ m R j hCL (by positivity) (hWL j hj c hc)
    hQ).trans (ENNReal.ofReal_le_ofReal ?_)
  exact decay_step_arith hCL hr hW1

/-!
## The two drift estimates
-/

/-- **`KStepDrift` from the closed decay and the closed `𝒦` mean structure.** -/
theorem kStepDrift_of_decay (hD : B3ClosedContrDecay) (hK : B3ClosedKLayerMean) : KStepDrift := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := b3_stepBound_of_layer_decay hD hF R
    (fun c => ∃ ij : Fin np × Fin np, c = Sum.inr ij)
    (by
      obtain ⟨C, hC, hev⟩ := hK b E np τ m T s h K Vs hF R
      exact ⟨C, hC, hev.mono fun W hW j hj c ⟨ij, hij⟩ => hij ▸ hW j hj ij⟩)
  exact ⟨C, ρ, hC, hρ0, hρ1, hev.mono fun W hW j hj ij => hW j hj _ ⟨ij, rfl⟩⟩

/-- **`GramSumStepDrift` from the closed decay and the closed Gram mean structure.** -/
theorem gramSumStepDrift_of_decay (hD : B3ClosedContrDecay) (hG : B3ClosedGramLayerMean) :
    GramSumStepDrift := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := b3_stepBound_of_layer_decay hD hF R
    (fun c => ∃ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np), c = Sum.inl e)
    (by
      obtain ⟨C, hC, hev⟩ := hG b E np τ m T s h K Vs hF R
      exact ⟨C, hC, hev.mono fun W hW j hj c ⟨e, he⟩ => he ▸ hW j hj e⟩)
  exact ⟨C, ρ, hC, hρ0, hρ1, hev.mono fun W hW j hj e => hW j hj _ ⟨e, rfl⟩⟩

/-- The summed drifts follow (by the summation lemmas of the generator and Gram sums). -/
theorem kDriftSummed_of_decay (hD : B3ClosedContrDecay) (hK : B3ClosedKLayerMean) :
    KDriftSummed :=
  kDriftSummed_of_step (kStepDrift_of_decay hD hK)

theorem genReqGramDrift_of_decay (hD : B3ClosedContrDecay) (hG : B3ClosedGramLayerMean) :
    GenReqGramDrift :=
  genReqGramDrift_of_step (gramSumStepDrift_of_decay hD hG)

/-!
## The Cesàro form
-/

/-- **The decay implies its Cesàro form.** -/
theorem b3ClosedContrCesaro_of_decay (hD : B3ClosedContrDecay) : B3ClosedContrCesaro := by
  intro b E np τ m T s h K Vs hF R p hp σ k l
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := hD b E np τ m T s h K Vs hF R p hp
  have key := gen_tendsto_sum_of_stepBound s T τ hρ0 hρ1 hC
    (fun W => Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊) (fun _ => subset_rfl)
    (fun W j => (W : ℝ≥0∞)⁻¹ * eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator
      (b3ContrCoord b E s h τ m W j (Vs W) σ k l)) (ENNReal.ofReal p) (closedLaw b W np))
    (by
      filter_upwards [hev, eventually_ge_atTop 1] with W hW hW1 j hj
      simp only [mem_Ico] at hj
      have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
      refine (mul_le_mul' le_rfl (hW j hj.1 hj.2.le σ k l)).trans (le_of_eq ?_)
      rw [div_mul_eq_mul_div, ENNReal.ofReal_div_of_pos hWpos, ENNReal.ofReal_natCast,
        ENNReal.div_eq_inv_mul])
  simpa only [Finset.mul_sum] using key

end BlockBand.SourceProcess.PhysApprox.B3
