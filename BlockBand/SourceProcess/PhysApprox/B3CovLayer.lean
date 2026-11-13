module

public import BlockBand.SourceProcess.PhysApprox.B3CovDoob
public import BlockBand.SourceProcess.ContractingWords.LiftL2

/-!
# The bracket estimates from a `LayerCov`-shaped bound and decay

* `CovField`: a real field on the closed process at every width and length (the closed layer
  error scale `e`, and the contracting-coordinate sum `Z`);
* **`CovLayerHyp e Z`**, **`ConjLayerHyp e Z`** (hypotheses): the `LayerCov` shape, pointwise a.e.
  on the alive set, for the raw closed brackets `E_j[1_{A_j} dX_c dX_c']` and
  `E_j[1_{A_j} d𝒦_ij conj d𝒦_kl]`;
* **`CovErrMoments e`** (hypothesis): `‖1_{A_j} e^n‖₄ ≤ (C_n/W)^n` (the jet bound
  `‖δ₀‖_{L^p} ≤ C_p/W`);
* **`CovDecayHyp Z`** (hypothesis):
  `‖1_{A_j} Z_j‖₄ ≤ C(genStepRate ρ j + W^{-1/2})`;
* `covStepBracketAll_of_layer`, hence `kStepBracket_of_layer` and
  `gramSumStepBracket_of_layer`; and `kStepConj_of_layer`;
* the targets **`kStepCov_of_layer`**, **`kStepConjCov_of_layer`** and
  **`gramSumStepCov_of_layer`**, each through the reverse Doob bound with the `L²` estimates;
* `complexClosedSummed_of_layer`: `ComplexClosedSummed` from the two drift estimates, the birth half
  and the four hypotheses above. No `L²` estimate is needed here.
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
## Generic lift: from a pointwise `LayerCov` shape to `L¹`
-/

section Generic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem cov_indicator_pow (A : Set Ω) (e : Ω → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (fun y => A.indicator e y ^ n) = A.indicator (fun y => e y ^ n) := by
  funext y
  by_cases hy : y ∈ A
  · simp [Set.indicator_of_mem hy]
  · simp [Set.indicator_of_notMem hy, zero_pow (by omega : n ≠ 0)]

/-- **The lifted `LayerCov` shape.** If on `A` the error is at most
`C₁ e|Z| + C₁(c + e² + e^N)`, with `‖1_A e‖₄ ≤ a₄`, `‖1_A e²‖₄ ≤ a₂`, `‖1_A e^N‖₄ ≤ a_N` and
`‖1_A Z‖₄ ≤ z`, then `E|1_A f| ≤ C₁ a₄ z + C₁(c + a₂ + a_N)`. -/
theorem cov_lift_lintegral_le (A : Set Ω) (f : Ω → ℂ) (e Z : Ω → ℝ) (N : ℕ) (hN : 2 ≤ N)
    {C₁ a₄ a₂ aN z c : ℝ} (hC₁ : 0 ≤ C₁) (ha₄ : 0 ≤ a₄) (hz : 0 ≤ z) (hc : 0 ≤ c)
    (ha₂ : 0 ≤ a₂) (haN : 0 ≤ aN)
    (hpt : ∀ᵐ y ∂μ, y ∈ A → ‖f y‖ ≤ C₁ * (e y * ‖Z y‖) + C₁ * (c + e y ^ 2 + e y ^ N))
    (h4 : eLpNorm (A.indicator e) 4 μ ≤ ENNReal.ofReal a₄)
    (h2 : eLpNorm (A.indicator fun y => e y ^ 2) 4 μ ≤ ENNReal.ofReal a₂)
    (hNm : eLpNorm (A.indicator fun y => e y ^ N) 4 μ ≤ ENNReal.ofReal aN)
    (hZ : eLpNorm (A.indicator Z) 4 μ ≤ ENNReal.ofReal z) :
    ∫⁻ y, ‖A.indicator f y‖ₑ ∂μ ≤ ENNReal.ofReal (C₁ * (a₄ * z) + C₁ * (c + a₂ + aN)) := by
  have h2' : eLpNorm (fun y => A.indicator e y ^ 2) 2 μ ≤ ENNReal.ofReal a₂ := by
    rw [cov_indicator_pow A e (by norm_num : 1 ≤ 2)]
    exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)).trans h2
  have hN' : eLpNorm (fun y => A.indicator e y ^ N) 2 μ ≤ ENNReal.ofReal aN := by
    rw [cov_indicator_pow A e (by omega : 1 ≤ N)]
    exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)).trans hNm
  have hem : AEStronglyMeasurable (A.indicator e) μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top (h4.trans_lt ENNReal.ofReal_lt_top).ne
  have hZA : AEStronglyMeasurable (A.indicator Z) μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top (hZ.trans_lt ENNReal.ofReal_lt_top).ne
  let Zc : Unit → Ω → ℂ := fun _ y => ((A.indicator Z y : ℝ) : ℂ)
  have hZcm : ∀ i, AEStronglyMeasurable (Zc i) μ := fun _ =>
    Complex.continuous_ofReal.comp_aestronglyMeasurable hZA
  have hZc : ∀ i ∈ [()], eLpNorm (Set.univ.indicator (Zc i)) 4 μ ≤ ENNReal.ofReal z := by
    intro i _
    rw [Set.indicator_univ]
    refine le_trans (le_of_eq ?_) hZ
    refine eLpNorm_congr_enorm_ae (hZcm i) hZA (Eventually.of_forall fun y => ?_)
    show ‖((A.indicator Z y : ℝ) : ℂ)‖ₑ = ‖A.indicator Z y‖ₑ
    rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  have hL := BlockBand.SourceProcess.ContractingWords.eLpNorm_lifted_le [()] Zc Set.univ
    MeasurableSet.univ (A.indicator e) hem hZcm N hC₁ ha₄ hz hc ha₂ haN h4 h2' hN' hZc
  have hg : (fun y => C₁ * ([()].map fun i => A.indicator e y *
      ‖Set.univ.indicator (Zc i) y‖).sum + C₁ * (c + A.indicator e y ^ 2 + A.indicator e y ^ N)) =
      fun y => C₁ * (A.indicator e y * ‖A.indicator Z y‖) +
        C₁ * (c + A.indicator e y ^ 2 + A.indicator e y ^ N) := by
    funext y
    simp [Zc, Complex.norm_real]
  rw [hg] at hL
  simp only [List.length_singleton, Nat.cast_one, one_mul] at hL
  calc ∫⁻ y, ‖A.indicator f y‖ₑ ∂μ ≤ ∫⁻ y, ‖C₁ * (A.indicator e y * ‖A.indicator Z y‖) +
        C₁ * (c + A.indicator e y ^ 2 + A.indicator e y ^ N)‖ₑ ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpt] with y hy
        by_cases hyA : y ∈ A
        · rw [Set.indicator_of_mem hyA, ← ofReal_norm, ← ofReal_norm]
          refine ENNReal.ofReal_le_ofReal ((hy hyA).trans
            (le_of_eq_of_le ?_ (Real.le_norm_self _)))
          simp only [Set.indicator_of_mem hyA]
        · simp [Set.indicator_of_notMem hyA]
    _ ≤ eLpNorm (fun y => C₁ * (A.indicator e y * ‖A.indicator Z y‖) +
          C₁ * (c + A.indicator e y ^ 2 + A.indicator e y ^ N)) 1 μ :=
        lintegral_enorm_le_eLpNorm_one
    _ ≤ eLpNorm (fun y => C₁ * (A.indicator e y * ‖A.indicator Z y‖) +
          C₁ * (c + A.indicator e y ^ 2 + A.indicator e y ^ N)) 2 μ :=
        eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
    _ ≤ _ := hL

end Generic

/-- The arithmetic: the lifted bound has the `SummedStep` shape. -/
theorem cov_step_of_parts {W : ℕ} (hW : 1 ≤ W) {C₁ Ce Cz c₂ cN r : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hC₁ : 0 ≤ C₁) (hr : 0 ≤ r) (hcN : 0 ≤ cN) {x : ℝ≥0∞}
    (hx : x ≤ ENNReal.ofReal (C₁ * (Ce / W * (Cz * (r + 1 / Real.sqrt W))) +
      C₁ * ((W : ℝ)⁻¹ / Real.sqrt W + (c₂ / W) ^ 2 + (cN / W) ^ N))) :
    x ≤ ENNReal.ofReal ((C₁ * 1 * Ce * Cz + C₁ * (1 + c₂ ^ 2 + cN ^ N)) / W *
      (r + 1 / Real.sqrt W)) := by
  have h := BlockBand.SourceProcess.ContractingWords.stepErr_of_parts hW (M := 1) (Ce := Ce)
    (Cz := Cz) (c₂ := c₂) hN hC₁ hr hr hcN rfl
  rw [one_mul] at h
  exact hx.trans (ENNReal.ofReal_le_ofReal h)

/-!
## The hypotheses on the closed process
-/

/-- A real field on the closed process, at every width `W` and length `j`. -/
abbrev CovField : Type :=
  ∀ (_b _E : ℝ) (np : ℕ) (_τ _m : Fin np → ℝ) (_s _h : ℝ) (K W : ℕ)
    (_Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (_j : ℕ),
    ProbedPath W np × ℝ → ℝ

/-- **The `LayerCov` shape for the raw closed brackets** (the full-source calculation of
`ContractingWords.LayerCov` on the closed system). There are `C ≥ 0` and `N ≥ 2` such that,
eventually in `W`, at every no-birth step `j`, for all coordinates `c, c'`, a.e. on the alive set
`A_j`:
`‖E_j[1_{A_j} dX_c dX_c'] - W⁻¹ cCov_{c,c'}(G_j)‖ ≤ C e_j|Z_j| + C(W^{-3/2} + e_j² + e_j^N)`.
-/
def CovLayerHyp (e Z : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ 2 ≤ N ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ c c' : CIdx K np,
      ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j (Vs W) →
        ‖(closedLaw b W np)[(b3Alive b E s h τ m R W j (Vs W)).indicator
            (fun y => b3dX b E s h τ m W j (Vs W) c y * b3dX b E s h τ m W j (Vs W) c' y) |
            b3Sigma W j np] y -
          (W : ℂ)⁻¹ * cCov b E c c' (b3ClosedGramAt b E s h τ m W j (Vs W) y)‖ ≤
        C * (e b E np τ m s h K W (Vs W) j y * ‖Z b E np τ m s h K W (Vs W) j y‖) +
          C * ((W : ℝ)⁻¹ / Real.sqrt W + e b E np τ m s h K W (Vs W) j y ^ 2 +
            e b E np τ m s h K W (Vs W) j y ^ N)

/-- **The `LayerCov` shape for the raw closed conjugate brackets**,
in the same form as `CovLayerHyp`, for `E_j[1_{A_j} d𝒦_ij conj d𝒦_kl]` and `W⁻¹ kConjCov`. -/
def ConjLayerHyp (e Z : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ 2 ≤ N ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ ij kl : Fin np × Fin np,
      ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j (Vs W) →
        ‖(closedLaw b W np)[(b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
            b3dX b E s h τ m W j (Vs W) (Sum.inr ij : CIdx K np) y *
              conj (b3dX b E s h τ m W j (Vs W) (Sum.inr kl : CIdx K np) y)) |
            b3Sigma W j np] y -
          (W : ℂ)⁻¹ * kConjCov b E ij kl (b3ClosedGramAt b E s h τ m W j (Vs W) y)‖ ≤
        C * (e b E np τ m s h K W (Vs W) j y * ‖Z b E np τ m s h K W (Vs W) j y‖) +
          C * ((W : ℝ)⁻¹ / Real.sqrt W + e b E np τ m s h K W (Vs W) j y ^ 2 +
            e b E np τ m s h K W (Vs W) j y ^ N)

/-- **Moments of the closed layer error scale** (the jet bound `‖δ₀‖_{L^p} ≤ C_p/W`): for every
`n ≥ 1`, `‖1_{A_j} e_j^n‖₄ ≤ (C_n/W)^n` eventually, at every no-birth step. -/
def CovErrMoments (e : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator
          (fun y => e b E np τ m s h K W (Vs W) j y ^ n)) 4 (closedLaw b W np) ≤
        ENNReal.ofReal ((C / W) ^ n)

/-- **`CovDecayHyp`: decay of the contracting coordinates after each restart**:
`‖1_{A_j} Z_j‖₄ ≤ C(genStepRate ρ j + W^{-1/2})` eventually, at every no-birth step. -/
def CovDecayHyp (Z : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator (Z b E np τ m s h K W (Vs W) j)) 4
          (closedLaw b W np) ≤
        ENNReal.ofReal (C * (genStepRate ρ s τ W j + 1 / Real.sqrt W))

/-!
## The raw bracket estimates
-/

/-- The raw closed bracket of every coordinate pair, in the `SummedStep` shape. -/
def CovStepBracketAll : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ c c' : CIdx K np,
      genBrStep b E s h τ m R W j (Vs W) c c' ≤
        ENNReal.ofReal (C / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W))

/-- **`CovLayerHyp + CovErrMoments + CovDecayHyp ⇒ CovStepBracketAll`.** -/
theorem covStepBracketAll_of_layer {e Z : CovField} (hL : CovLayerHyp e Z)
    (hE : CovErrMoments e) (hD : CovDecayHyp Z) : CovStepBracketAll := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨C₁, N, hC₁, hN, hevL⟩ := hL b E np τ m T s h K Vs hFD R
  obtain ⟨Ce, hCe, hev1⟩ := hE b E np τ m T s h K Vs hFD R 1 le_rfl
  obtain ⟨c₂, hc₂, hev2⟩ := hE b E np τ m T s h K Vs hFD R 2 (by norm_num)
  obtain ⟨cN, hcN, hevN⟩ := hE b E np τ m T s h K Vs hFD R N (by omega)
  obtain ⟨Cz, ρ, hCz, hρ0, hρ1, hevZ⟩ := hD b E np τ m T s h K Vs hFD R
  refine ⟨C₁ * 1 * Ce * Cz + C₁ * (1 + c₂ ^ 2 + cN ^ N), ρ, by positivity, hρ0, hρ1, ?_⟩
  filter_upwards [hevL, hev1, hev2, hevN, hevZ, eventually_ge_atTop 1]
    with W hWL hW1' hW2 hWN hWZ hW1 j hj c c'
  have hr := genStepRate_nonneg hρ0 s τ W j
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hlift := cov_lift_lintegral_le (μ := closedLaw b W np)
    (b3Alive b E s h τ m R W j (Vs W)) _ (e b E np τ m s h K W (Vs W) j)
    (Z b E np τ m s h K W (Vs W) j) N hN hC₁ (a₄ := Ce / W) (a₂ := (c₂ / W) ^ 2)
    (aN := (cN / W) ^ N) (z := Cz * (genStepRate ρ s τ W j + 1 / Real.sqrt W))
    (c := (W : ℝ)⁻¹ / Real.sqrt W) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (hWL j hj c c') (by simpa only [pow_one] using hW1' j hj)
    (hW2 j hj) (hWN j hj) (hWZ j hj)
  unfold genBrStep
  exact cov_step_of_parts hW1 hN hC₁ hr hcN hlift

/-- The raw closed conjugate bracket, in the `SummedStep` shape (this is `KStepConj`). -/
theorem kStepConj_of_layer {e Z : CovField} (hL : ConjLayerHyp e Z)
    (hE : CovErrMoments e) (hD : CovDecayHyp Z) : KStepConj := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨C₁, N, hC₁, hN, hevL⟩ := hL b E np τ m T s h K Vs hFD R
  obtain ⟨Ce, hCe, hev1⟩ := hE b E np τ m T s h K Vs hFD R 1 le_rfl
  obtain ⟨c₂, hc₂, hev2⟩ := hE b E np τ m T s h K Vs hFD R 2 (by norm_num)
  obtain ⟨cN, hcN, hevN⟩ := hE b E np τ m T s h K Vs hFD R N (by omega)
  obtain ⟨Cz, ρ, hCz, hρ0, hρ1, hevZ⟩ := hD b E np τ m T s h K Vs hFD R
  refine ⟨C₁ * 1 * Ce * Cz + C₁ * (1 + c₂ ^ 2 + cN ^ N), ρ, by positivity, hρ0, hρ1, ?_⟩
  filter_upwards [hevL, hev1, hev2, hevN, hevZ, eventually_ge_atTop 1]
    with W hWL hW1' hW2 hWN hWZ hW1 j hj ij kl
  have hr := genStepRate_nonneg hρ0 s τ W j
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hlift := cov_lift_lintegral_le (μ := closedLaw b W np)
    (b3Alive b E s h τ m R W j (Vs W)) _ (e b E np τ m s h K W (Vs W) j)
    (Z b E np τ m s h K W (Vs W) j) N hN hC₁ (a₄ := Ce / W) (a₂ := (c₂ / W) ^ 2)
    (aN := (cN / W) ^ N) (z := Cz * (genStepRate ρ s τ W j + 1 / Real.sqrt W))
    (c := (W : ℝ)⁻¹ / Real.sqrt W) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (hWL j hj ij kl) (by simpa only [pow_one] using hW1' j hj)
    (hW2 j hj) (hWN j hj) (hWZ j hj)
  unfold genConjStep
  exact cov_step_of_parts hW1 hN hC₁ hr hcN hlift

/-- `CovStepBracketAll` contains `KStepBracket`. -/
theorem kStepBracket_of_all (h : CovStepBracketAll) : KStepBracket := by
  intro b E np τ m T s h' K Vs hFD R
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := h b E np τ m T s h' K Vs hFD R
  exact ⟨C, ρ, hC, hρ0, hρ1, hev.mono fun W hW j hj ij c' => hW j hj _ c'⟩

/-- `CovStepBracketAll` contains `GramSumStepBracket`. -/
theorem gramSumStepBracket_of_all (h : CovStepBracketAll) : GramSumStepBracket := by
  intro b E np τ m T s h' K Vs hFD R
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := h b E np τ m T s h' K Vs hFD R
  exact ⟨C, ρ, hC, hρ0, hρ1, hev.mono fun W hW j hj e e' => hW j hj _ _⟩

/-- **`KStepBracket` from the `LayerCov` shape and decay.** -/
theorem kStepBracket_of_layer {e Z : CovField} (hL : CovLayerHyp e Z) (hE : CovErrMoments e)
    (hD : CovDecayHyp Z) : KStepBracket :=
  kStepBracket_of_all (covStepBracketAll_of_layer hL hE hD)

/-- **`GramSumStepBracket` from the `LayerCov` shape and decay.** -/
theorem gramSumStepBracket_of_layer {e Z : CovField} (hL : CovLayerHyp e Z)
    (hE : CovErrMoments e) (hD : CovDecayHyp Z) : GramSumStepBracket :=
  gramSumStepBracket_of_all (covStepBracketAll_of_layer hL hE hD)

/-!
## The three targets
-/

/-- **Target `KStepCov`** from the `L²` estimates, the `LayerCov` shape and decay. -/
theorem kStepCov_of_layer {e Z : CovField} (hL2 : GenStepMemL2) (hM : GenStepMeanL2)
    (hL : CovLayerHyp e Z) (hE : CovErrMoments e) (hD : CovDecayHyp Z) : KStepCov :=
  kStepCov_of_bracket hL2 hM (kStepBracket_of_layer hL hE hD)

/-- **Target `KStepConjCov`** from the `L²` estimates, the conjugate `LayerCov` shape and decay. -/
theorem kStepConjCov_of_layer {e Z : CovField} (hL2 : GenStepMemL2) (hM : GenStepMeanL2)
    (hL : ConjLayerHyp e Z) (hE : CovErrMoments e) (hD : CovDecayHyp Z) : KStepConjCov :=
  kStepConjCov_of_conj hL2 hM (kStepConj_of_layer hL hE hD)

/-- **Target `GramSumStepCov`** from the Gram `L²` estimates, the `LayerCov` shape and decay. -/
theorem gramSumStepCov_of_layer {e Z : CovField} (hL2 : GramSumStepMemL2)
    (hM : GramSumStepMeanL2) (hL : CovLayerHyp e Z) (hE : CovErrMoments e)
    (hD : CovDecayHyp Z) : GramSumStepCov :=
  gramSumStepCov_of_bracket hL2 hM (gramSumStepBracket_of_layer hL hE hD)

/-- **`ComplexClosedSummed` from the layer hypotheses**: the two drift estimates, the birth half, and
the `LayerCov` shapes with decay. The `L²` estimates are not needed here. -/
theorem complexClosedSummed_of_layer {e Z : CovField} (hGD : GramSumStepDrift)
    (hB : GenReqBirth) (hKD : KStepDrift) (hCL : CovLayerHyp e Z) (hCC : ConjLayerHyp e Z)
    (hE : CovErrMoments e) (hD : CovDecayHyp Z) : ComplexClosedSummed :=
  complexClosedSummed_of_gramSteps hGD (gramSumStepBracket_of_layer hCL hE hD) hB hKD
    (kStepBracket_of_layer hCL hE hD) (kStepConj_of_layer hCC hE hD)

end BlockBand.SourceProcess.PhysApprox.B3
