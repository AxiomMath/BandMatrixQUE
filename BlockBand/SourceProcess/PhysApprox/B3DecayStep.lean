module

public import BlockBand.SourceProcess.PhysApprox.B3DecayDrift
public import BlockBand.SourceProcess.ContractingWords.Recursion

/-!
# The closed decay from the closed one-step estimates

* `B3ClosedContrStepMean` (SM): `‖1_{A_j}(E_j[1_{A_j}Q_{j+1}] - λQ_j)‖_p ≤ C/W`, `|λ| ≤ ρ < 1`;
* `B3ClosedContrStepFluct` (SF): `‖1_{A_j}(Q_{j+1} - E_j[1_{A_j}Q_{j+1}])‖_p ≤ C/√W`;
* `B3ClosedContrBound` (D0): `|1_{A_j}Q_j| ≤ C` a.s.
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
## The closed one-step estimates
-/

/-- **(SM): the closed one-step mean of a contracting coordinate** (`LayerFreshBound` at
the closed state with closed jets). -/
def B3ClosedContrStepMean : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p →
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ (σ : Fin 4) (k l : SrcCol K (Fin np)),
      ∃ lam : ℂ, ‖lam‖ ≤ ρ ∧
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
          (closedLaw b W np)[(b3Alive b E s h τ m R W j (Vs W)).indicator
              (b3ContrCoord b E s h τ m W (j + 1) (Vs W) σ k l) | b3Sigma W j np] y -
            lam * b3ContrCoord b E s h τ m W j (Vs W) σ k l y))
        (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- **(SF): the closed one-step fluctuation of a contracting coordinate**
(`LayerFreshBound` at the closed state with closed jets). -/
def B3ClosedContrStepFluct : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p →
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ (σ : Fin 4) (k l : SrcCol K (Fin np)),
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
          b3ContrCoord b E s h τ m W (j + 1) (Vs W) σ k l y -
            (closedLaw b W np)[(b3Alive b E s h τ m R W j (Vs W)).indicator
              (b3ContrCoord b E s h τ m W (j + 1) (Vs W) σ k l) | b3Sigma W j np] y))
        (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / Real.sqrt W)

/-- **(D0): the alive closed contracting coordinates are bounded** (closed unitarity
`‖P𝕊_jC_j(z)v‖ ≤ ‖v‖` for `Av = 0`, so `|Q^σ_{kl}| ≤ Tr M_j < R`). -/
def B3ClosedContrBound : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j, closeLen s W ≤ j → j ≤ ⌊(W : ℝ) * T⌋₊ →
    ∀ (σ : Fin 4) (k l : SrcCol K (Fin np)), ∀ᵐ y ∂closedLaw b W np,
      ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
        (b3ContrCoord b E s h τ m W j (Vs W) σ k l) y‖ ≤ C

/-!
## Restarts
-/

/-- The geometric rate dominates the term of any restart `r ≤ j`. -/
theorem pow_le_genStepRate {ρ : ℝ} (hρ0 : 0 ≤ ρ) (s : ℝ) {np : ℕ} (τ : Fin np → ℝ) (W : ℕ)
    {r j : ℕ} (hr : r ∈ genRestarts s τ W) (hrj : r ≤ j) :
    ρ ^ (j - r) ≤ genStepRate ρ s τ W j := by
  unfold genStepRate
  have h := single_le_sum (f := fun r => if r ≤ j then ρ ^ (j - r) else 0)
    (fun r _ => gen_stepTerm_nonneg hρ0 r j) hr
  simpa only [hrj, ↓reduceIte] using h

/-- The last restart `≤ j` (for `n_s ≤ j`). -/
def lastRestart (s : ℝ) {np : ℕ} (τ : Fin np → ℝ) (W j : ℕ) : ℕ :=
  ((genRestarts s τ W).filter (· ≤ j)).sup id

theorem closeLen_mem_genRestarts (s : ℝ) {np : ℕ} (τ : Fin np → ℝ) (W : ℕ) :
    closeLen s W ∈ genRestarts s τ W := mem_insert_self _ _

theorem lastRestart_spec (s : ℝ) {np : ℕ} (τ : Fin np → ℝ) {W j : ℕ} (hj : closeLen s W ≤ j) :
    lastRestart s τ W j ∈ genRestarts s τ W ∧ lastRestart s τ W j ≤ j ∧
      closeLen s W ≤ lastRestart s τ W j := by
  have hne : ((genRestarts s τ W).filter (· ≤ j)).Nonempty :=
    ⟨closeLen s W, mem_filter.2 ⟨closeLen_mem_genRestarts s τ W, hj⟩⟩
  obtain ⟨r, hr, hreq⟩ := exists_mem_eq_sup _ hne id
  have hr' := mem_filter.1 hr
  have hle : ∀ r' ∈ (genRestarts s τ W).filter (· ≤ j), r' ≤ lastRestart s τ W j :=
    fun r' hr' => le_sup (f := id) hr'
  refine ⟨?_, ?_, hle _ (mem_filter.2 ⟨closeLen_mem_genRestarts s τ W, hj⟩)⟩
  · rw [lastRestart, hreq]; exact hr'.1
  · rw [lastRestart, hreq]; exact hr'.2

/-- No birth in `[r_j, j)`. -/
theorem not_birth_of_lastRestart (s : ℝ) {np : ℕ} (τ : Fin np → ℝ) {W j i : ℕ}
    (hi : lastRestart s τ W j ≤ i) (hij : i < j) : ¬ IsBirthStep τ W i := by
  rintro ⟨a, ha⟩
  have hmem : i + 1 ∈ (genRestarts s τ W).filter (· ≤ j) := by
    refine mem_filter.2 ⟨?_, by omega⟩
    exact mem_insert_of_mem (mem_image.2 ⟨a, mem_univ _, by simp [ha]⟩)
  have h2 : i + 1 ≤ lastRestart s τ W j := le_sup (f := id) hmem
  omega

/-!
## The one-step Minkowski bound
-/

/-- `‖1_{A'}Z'‖ ≤ |λ|‖1_AZ‖ + ‖1_A(Y - λZ)‖ + ‖1_A(Z' - Y)‖` for `A' ⊆ A`. -/
theorem decay_minkowski_step {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    (hp : 1 ≤ p) {A A' : Set α} (hsub : A' ⊆ A) {Z Z' Y : α → ℂ} (lam : ℂ)
    (hm : AEStronglyMeasurable (A'.indicator Z') μ) :
    eLpNorm (A'.indicator Z') p μ ≤ ‖lam‖ₑ * eLpNorm (A.indicator Z) p μ +
      eLpNorm (A.indicator fun y => Y y - lam * Z y) p μ +
      eLpNorm (A.indicator fun y => Z' y - Y y) p μ := by
  have hmono : eLpNorm (A'.indicator Z') p μ ≤ eLpNorm (A.indicator Z') p μ := by
    refine eLpNorm_mono_ae hm (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ A'
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hsub hy)]
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact norm_nonneg _
  have hsplit : A.indicator Z' = lam • A.indicator Z + A.indicator (fun y => Y y - lam * Z y) +
      A.indicator (fun y => Z' y - Y y) := by
    funext y
    by_cases hy : y ∈ A
    · simp only [Pi.add_apply, Pi.smul_apply, Set.indicator_of_mem hy, smul_eq_mul]; ring
    · simp [Set.indicator_of_notMem hy]
  refine hmono.trans ?_
  rw [hsplit]
  refine (eLpNorm_add_le hp).trans (add_le_add ((eLpNorm_add_le hp).trans ?_) le_rfl)
  rw [eLpNorm_const_smul]

/-!
## The decay
-/

/-- **The closed contracting-word decay from the closed one-step estimates and the bound (D0).** -/
theorem b3ClosedContrDecay_of_steps (hM : B3ClosedContrStepMean) (hF : B3ClosedContrStepFluct)
    (hB : B3ClosedContrBound) : B3ClosedContrDecay := by
  intro b E np τ m T s h K Vs hFD R p hp
  obtain ⟨C₁, ρ, hC₁, hρ0, hρ1, hevM⟩ := hM b E np τ m T s h K Vs hFD R p hp
  obtain ⟨C₂, hC₂, hevF⟩ := hF b E np τ m T s h K Vs hFD R p hp
  obtain ⟨C₀, hC₀, hevB⟩ := hB b E np τ m T s h K Vs hFD R
  obtain ⟨hD, -, -, -, -, hVs⟩ := id hFD
  have hb1 : b < 1 := by linarith [hD.2.1]
  have h1ρ : 0 < 1 - ρ := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  refine ⟨C₀ + (C₁ + C₂) / (1 - ρ), ρ, add_nonneg hC₀ (div_nonneg (add_nonneg hC₁ hC₂) h1ρ.le),
    hρ0, hρ1, ?_⟩
  filter_upwards [hevM, hevF, hevB, hVs, eventually_ge_atTop 1]
    with W hWM hWF hWB hVW hW1 j hj hjT σ k l
  have hmV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hsq : 0 < Real.sqrt W := Real.sqrt_pos.2 hWpos
  set μ := closedLaw b W np
  set a : ℕ → ℝ≥0∞ := fun i => eLpNorm ((b3Alive b E s h τ m R W i (Vs W)).indicator
    (b3ContrCoord b E s h τ m W i (Vs W) σ k l)) (ENNReal.ofReal p) μ
  set c : ℝ := C₁ / W + C₂ / Real.sqrt W
  have hc1 : 0 ≤ C₁ / W := div_nonneg hC₁ hWpos.le
  have hc2 : 0 ≤ C₂ / Real.sqrt W := div_nonneg hC₂ hsq.le
  have hc : 0 ≤ c := add_nonneg hc1 hc2
  obtain ⟨hrR, hrj, hsr⟩ := lastRestart_spec s τ hj
  set r := lastRestart s τ W j
  have h0 : a r ≤ ENNReal.ofReal C₀ := by
    refine (eLpNorm_le_of_ae_bound (aestronglyMeasurable_contr hb1 hD.2.2.1 hD.2.2.2.1 s h τ m
      R W r hmV r σ k l) (hWB r hsr (hrj.trans hjT) σ k l)).trans (le_of_eq ?_)
    rw [measure_univ, ENNReal.one_rpow, one_mul]
  have hstep : ∀ i, r ≤ i → i < j → a (i + 1) ≤ ENNReal.ofReal ρ * a i + ENNReal.ofReal c := by
    intro i hri hij
    have hiS : i ∈ genNoBirthSteps s T τ W := by
      simp only [genNoBirthSteps, mem_filter, mem_Ico]
      exact ⟨⟨hsr.trans hri, by omega⟩, not_birth_of_lastRestart s τ hri hij⟩
    obtain ⟨lam, hlam, hmean⟩ := hWM i hiS σ k l
    have hfl := hWF i hiS σ k l
    refine (decay_minkowski_step hp1 (genMem_b3Alive_succ_subset b E s h τ m R W i (Vs W))
      (Z := b3ContrCoord b E s h τ m W i (Vs W) σ k l)
      (Y := fun y => μ[(b3Alive b E s h τ m R W i (Vs W)).indicator
        (b3ContrCoord b E s h τ m W (i + 1) (Vs W) σ k l) | b3Sigma W i np] y) lam
      (aestronglyMeasurable_contr hb1 hD.2.2.1 hD.2.2.2.1 s h τ m R W (i + 1) hmV (i + 1)
        σ k l)).trans ?_
    rw [show ENNReal.ofReal c = ENNReal.ofReal (C₁ / W) + ENNReal.ofReal (C₂ / Real.sqrt W) from
      ENNReal.ofReal_add hc1 hc2, ← add_assoc]
    refine add_le_add (add_le_add ?_ hmean) hfl
    refine mul_le_mul' ?_ le_rfl
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hlam
  have hfin := ContractingWords.geometric_iterate hρ0 hρ1 hc hC₀ h0 hstep (j - r) (by omega)
  rw [show r + (j - r) = j by omega] at hfin
  refine hfin.trans (ENNReal.ofReal_le_ofReal ?_)
  have hrate : ρ ^ (j - r) ≤ genStepRate ρ s τ W j := pow_le_genStepRate hρ0 s τ W hrR hrj
  have hw : (1 : ℝ) / W ≤ 1 / Real.sqrt W := by
    have h1 : Real.sqrt W ≤ W := by
      have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
      have := Real.sqrt_le_sqrt (show (W : ℝ) ≤ W * W by nlinarith)
      rwa [Real.sqrt_mul_self hWpos.le] at this
    exact one_div_le_one_div_of_le hsq h1
  have hc' : c ≤ (C₁ + C₂) * (1 / Real.sqrt W) := by
    have e1 : C₁ / W = C₁ * (1 / W) := by ring
    have e2 : C₂ / Real.sqrt W = C₂ * (1 / Real.sqrt W) := by ring
    simp only [c, e1, e2]
    nlinarith [mul_le_mul_of_nonneg_left hw hC₁]
  have hcd : c / (1 - ρ) ≤ (C₁ + C₂) / (1 - ρ) * (1 / Real.sqrt W) := by
    rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hc' h1ρ.le
  have hD' : 0 ≤ (C₁ + C₂) / (1 - ρ) := div_nonneg (add_nonneg hC₁ hC₂) h1ρ.le
  have hs' : 0 ≤ 1 / Real.sqrt W := by positivity
  have hr0 : 0 ≤ genStepRate ρ s τ W j := genStepRate_nonneg hρ0 s τ W j
  nlinarith [mul_le_mul_of_nonneg_left hrate hC₀, mul_nonneg hD' hr0, mul_nonneg hC₀ hs', hcd]

end BlockBand.SourceProcess.PhysApprox.B3
