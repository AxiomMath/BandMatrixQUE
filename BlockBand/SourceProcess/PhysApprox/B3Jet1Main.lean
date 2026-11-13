module

public import BlockBand.SourceProcess.PhysApprox.B3Jet1Rec
public import BlockBand.SourceProcess.PhysApprox.B3CovRepErr
public import BlockBand.Transmission.LengthUniform.Jet

/-!
# The closed `δ₁` jet in every `L^p`

* **`eLpNorm_closedJet1_le`** (one width): for any input family that is Borel, past-determined,
  a.e. passive and follows the fresh recursion on `[j₀, i]`, and any decreasing null-measurable
  family `A_j`: `‖1_{A_{j₀}}v_{j₀}‖_p ≤ C₁/W` and `‖1_{A_j}δ₀,j‖_p ≤ C₀/W` (`j₀ ≤ j < i`) give
  `‖1_{A_i}v_i‖_p ≤ (C₁ + ((C₂ + M/d₀)C₀ + C_m + C_f)/(1-ρ₁))/W`. The start value is propagated,
  not forgotten: no burn-in;
* **`closedJet1Lp_of`** (main theorem): `ClosedJet1Lp` from `GaussianAbsorptionContract`,
  `GaussianLpGradient`, the passivity and recursion of `b3ClosedX` (hypotheses `hP`, `hRec`, that
  is `ClosedInputPassive b3ClosedX` and `ClosedInputRecursion b3ClosedX`), and two inputs:
  - **`ClosedJet0LpSteps`**: the closed `δ₀` at scale `1/W` in every `L^p` at **every** step
    `n_s ≤ j < ⌊WT⌋` (births included), on the alive set. It implies `ClosedJet0Lp`
    (`closedJet0Lp_of_steps`). It is needed at birth steps too: `δ₁` at a no-birth step `j`
    feels `δ₀` at all earlier steps through the recursion;
  - **`ClosedJet1Start`**: `‖1_{A_{n_s}}δ₁(X_cl,n_s)‖_p ≤ C_p/W` (when `n_s < ⌊WT⌋`). This is
    `ClosedJet1Lp` at `j = n_s` (a no-birth step since `s < τ_k`), so it cannot be avoided.

The argument is parametric in the jet functional where it can be: the fresh error under
`closedLaw` (`eLpNorm_jetFluctOf_le`) and the propagated linear recursion
(`eLpNorm_linrec_from`, `indicator_step_le`) hold for any `Φ`. The `δ₀` step holds only on the
scalar domain (no linear bound off it), so `ClosedJet0LpSteps` needs exits paid by Markov
(`closedJetLp_of`), with its own start at `n_s` at scale `1/W`; `closedJet0LpSteps_of_fam`
connects the two.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet1

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PathJet BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.ClosedPath BlockBand.Transmission.LengthUniform
open scoped ENNReal ComplexOrder

/-!
## The measurable first jet and one fresh step
-/

/-- `v(X) = ‖-W⁻¹Tr(z - X)⁻² - s‖` at `z = z_∂`: a measurable version of `δ₁` (equal for passive
`X`, `jetDistance1_eq_crossTr`). -/
def jet1V (b E : ℝ) (s : ℂ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ‖-crossTr X (boundaryZ b E) (boundaryZ b E) - s‖

theorem jet1V_nonneg (b E : ℝ) (s : ℂ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) :
    0 ≤ jet1V b E s X := norm_nonneg _

theorem measurable_jet1V (b E : ℝ) (s : ℂ) {W : ℕ} :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => jet1V b E s X :=
  (((measurable_crossTr_mat _).neg).sub measurable_const).norm

/-- `1_A δ₁(X) = 1_A v(X)` a.e. when `X` is a.e. passive. -/
theorem indicator_jetDistance1_ae_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) (s : ℂ) {W : ℕ}
    (X : α → Matrix (Fin W) (Fin W) ℂ) (A : Set α)
    (hp : ∀ᵐ y ∂μ, (passiveY (X y)).PosSemidef) :
    A.indicator (fun y => jetDistance1 b E s (X y)) =ᵐ[μ]
      A.indicator (fun y => jet1V b E s (X y)) := by
  filter_upwards [hp] with y hy
  by_cases hA : y ∈ A
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA,
      jetDistance1_eq_crossTr hb h1 h2 s hy]
    rfl
  · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA]

/-- **One fresh `δ₁` step** (deterministic): for passive `X` and `X₊ = freshSchur E X F`,
`v(X₊) ≤ ρ₁v(X) + ((C₂ + M/d₀)δ₀(X) + C/W² + ‖jetFun(X, F) - E jetFun(X, ·)‖)`. -/
theorem jet1_step_le {b κ E d₀ ρ₁ C₂ Cm : ℝ} {W : ℕ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) {s : ℂ} (hs : IsStationaryJet b E s) (hd₀ : 0 < d₀)
    (hρ₁ : 0 ≤ ρ₁) (hC₂ : 0 ≤ C₂) (hCm : 0 ≤ Cm)
    (hmean : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      jetDistance0 b E X ≤ d₀ →
        ‖(∫ ω, freshJet b E X ω ∂freshLaw W b) - s‖ ≤
          ρ₁ * jetDistance1 b E s X + C₂ * jetDistance0 b E X + Cm / (W : ℝ) ^ 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef)
    (F : LayerSample W .oneBlockOnePort) (hXs : (passiveY (freshSchur E X F)).PosSemidef) :
    jet1V b E s (freshSchur E X F) ≤ ρ₁ * jet1V b E s X +
      ((C₂ + jetM b κ / d₀) * jetDistance0 b E X + Cm / (W : ℝ) ^ 2 +
        ‖jetFun b E X F - ∫ F', jetFun b E X F' ∂freshLaw W b‖) := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hy1 : jet1V b E s (freshSchur E X F) = ‖jetFun b E X F - s‖ := rfl
  have hyj : jet1V b E s X = jetDistance1 b E s X :=
    (jetDistance1_eq_crossTr (by linarith) h1 h2 s hX).symm
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hM0 : 0 ≤ jetM b κ := by unfold jetM; positivity
  have hξ0 : 0 ≤ ‖jetFun b E X F - ∫ F', jetFun b E X F' ∂freshLaw W b‖ := norm_nonneg _
  have hy0 : 0 ≤ jet1V b E s X := norm_nonneg _
  have hCW : 0 ≤ Cm / (W : ℝ) ^ 2 := by positivity
  have hMd : 0 ≤ jetM b κ / d₀ * jetDistance0 b E X := by positivity
  by_cases hd : jetDistance0 b E X ≤ d₀
  · have hm := hmean X hX hd
    rw [← integral_jetFun_eq (by linarith) h1 h2 hX] at hm
    have htri : jet1V b E s (freshSchur E X F) ≤
        ‖(∫ F', jetFun b E X F' ∂freshLaw W b) - s‖ +
          ‖jetFun b E X F - ∫ F', jetFun b E X F' ∂freshLaw W b‖ := by
      rw [hy1]
      have := norm_add_le (jetFun b E X F - ∫ F', jetFun b E X F' ∂freshLaw W b)
        ((∫ F', jetFun b E X F' ∂freshLaw W b) - s)
      rw [show jetFun b E X F - ∫ F', jetFun b E X F' ∂freshLaw W b +
        ((∫ F', jetFun b E X F' ∂freshLaw W b) - s) = jetFun b E X F - s by ring] at this
      linarith
    rw [hyj]
    nlinarith [add_mul C₂ (jetM b κ / d₀) (jetDistance0 b E X)]
  · push Not at hd
    have hbd : jet1V b E s (freshSchur E X F) ≤ jetM b κ := crossTr_jet_le hb0 hb hκ hE hs hXs
    have : jetM b κ ≤ jetM b κ / d₀ * jetDistance0 b E X := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd₀]
      exact mul_le_mul_of_nonneg_left hd.le hM0
    have : 0 ≤ ρ₁ * jet1V b E s X := mul_nonneg hρ₁ hy0
    nlinarith [add_mul C₂ (jetM b κ / d₀) (jetDistance0 b E X), mul_nonneg hC₂ hδ0]

/-!
## The closed `δ₁` at one width
-/

/-- **The closed `δ₁` jet at one width, from a start at scale `1/W`.** For inputs `X j` that are
Borel, past-determined and a.e. passive on `[j₀, i]` and follow the fresh recursion there, and a
decreasing null-measurable family `A j`: if `‖1_{A_{j₀}}v(X_{j₀})‖_p ≤ C₁/W` and
`‖1_{A_j}δ₀(X_j)‖_p ≤ C₀/W` for `j₀ ≤ j < i`, then
`‖1_{A_i}v(X_i)‖_p ≤ (C₁ + ((C₂ + M/d₀)C₀ + C_m + C_f)/(1-ρ₁))/W`. -/
theorem eLpNorm_closedJet1_le {b κ E d₀ ρ₁ C₂ Cm Cf C₀ C₁ p : ℝ} {W np : ℕ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) {s : ℂ} (hs : IsStationaryJet b E s)
    (hd₀ : 0 < d₀) (hρ₁0 : 0 ≤ ρ₁) (hρ₁1 : ρ₁ < 1) (hC₂ : 0 ≤ C₂) (hCm : 0 ≤ Cm) (hCf : 0 ≤ Cf)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hp : 1 ≤ p) (hW1 : 1 ≤ W)
    (hmean : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      jetDistance0 b E X ≤ d₀ →
        ‖(∫ ω, freshJet b E X ω ∂freshLaw W b) - s‖ ≤
          ρ₁ * jetDistance1 b E s X + C₂ * jetDistance0 b E X + Cm / (W : ℝ) ^ 2)
    (hfl : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      eLpNorm (fun ω => ‖jetFun b E X ω - ∫ ω', jetFun b E X ω' ∂freshLaw W b‖)
        (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal (Cf / W))
    (X : ℕ → ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ)
    (A : ℕ → Set (ProbedPath W np × ℝ)) (hA : ∀ j, A (j + 1) ⊆ A j)
    (hAm : ∀ j, NullMeasurableSet (A j) (closedLaw b W np)) {j₀ i : ℕ} (hji : j₀ ≤ i)
    (hXm : ∀ j, Measurable (X j))
    (hXi : ∀ j, j₀ ≤ j → j ≤ i → ∀ y, X j (b3Ext W j y) = X j y)
    (hXp : ∀ j, j₀ ≤ j → j ≤ i → ∀ᵐ y ∂closedLaw b W np, (passiveY (X j y)).PosSemidef)
    (hXr : ∀ j, j₀ ≤ j → j < i → ∀ᵐ y ∂closedLaw b W np,
      X (j + 1) y = freshSchur E (X j y) (freshSample W j y.1.1))
    (h0 : ∀ j, j₀ ≤ j → j < i →
      eLpNorm ((A j).indicator fun y => jetDistance0 b E (X j y)) (ENNReal.ofReal p)
        (closedLaw b W np) ≤ ENNReal.ofReal (C₀ / W))
    (h1 : eLpNorm ((A j₀).indicator fun y => jet1V b E s (X j₀ y)) (ENNReal.ofReal p)
        (closedLaw b W np) ≤ ENNReal.ofReal (C₁ / W)) :
    eLpNorm ((A i).indicator fun y => jet1V b E s (X i y)) (ENNReal.ofReal p)
        (closedLaw b W np) ≤
      ENNReal.ofReal ((C₁ + ((C₂ + jetM b κ / d₀) * C₀ + Cm + Cf) / (1 - ρ₁)) / W) := by
  set μ := closedLaw b W np
  have hx : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hx1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hM0 : 0 ≤ jetM b κ := by
    unfold jetM; have := etaLow_pos (by linarith : b < 1) hκ; positivity
  set k := C₂ + jetM b κ / d₀ with hk
  have hk0 : 0 ≤ k := by positivity
  have hc : 0 ≤ Cm / (W : ℝ) ^ 2 := by positivity
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hΦ : Measurable fun q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort =>
      jetFun b E q.1 q.2 := measurable_jetFun_comp b E measurable_fst measurable_snd
  set Y : ℕ → ProbedPath W np × ℝ → ℝ := fun j => (A j).indicator fun y => jet1V b E s (X j y)
    with hY
  set e : ℕ → ProbedPath W np × ℝ → ℝ := fun j y =>
    k * (A j).indicator (fun y => jetDistance0 b E (X j y)) y + Cm / (W : ℝ) ^ 2 +
      jetFluctOf (jetFun b E) b (X j) j y with he
  have hY0 : ∀ j y, 0 ≤ Y j y := fun j y =>
    Set.indicator_nonneg (fun y _ => jet1V_nonneg b E s (X j y)) y
  have hYm : ∀ j, AEStronglyMeasurable (Y j) μ := fun j =>
    ((measurable_jet1V b E s).comp (hXm j)).aestronglyMeasurable.indicator₀ (hAm j)
  have hstep : ∀ j, j₀ ≤ j → j < i → ∀ᵐ y ∂μ, Y (j + 1) y ≤ ρ₁ * Y j y + e j y := by
    intro j hj hji2
    filter_upwards [hXr j hj hji2, hXp j hj hji2.le, hXp (j + 1) (by omega) hji2] with y hy hp hp1
    have hst := jet1_step_le hb0 hb hκ hE hs hd₀ hρ₁0 hC₂ hCm hmean hp (freshSample W j y.1.1)
      (hy ▸ hp1)
    rw [← hy] at hst
    exact indicator_step_le (hA j) hρ₁0 hk0 hc (fun y => jet1V_nonneg b E s (X j y))
      (fun y => norm_nonneg _) (jetFluctOf_nonneg (jetFun b E) b (X j) j) y hst
  have hB : 0 ≤ (k * C₀ + Cm + Cf) / W := by positivity
  have hee : ∀ j, j₀ ≤ j → j < i → eLpNorm (e j) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal ((k * C₀ + Cm + Cf) / W) := by
    intro j hj hji2
    have hξ := eLpNorm_jetFluctOf_le hΦ (by linarith : (0 : ℝ) < p) (hXm j) (hXi j hj hji2.le)
      (hXp j hj hji2.le) hfl
    refine (eLpNorm_err_le hp hk0 hc (h0 j hj hji2) hξ (by positivity)
      (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
    have : Cm / (W : ℝ) ^ 2 ≤ Cm / W :=
      div_le_div_of_nonneg_left hCm hx (by nlinarith)
    rw [add_div, add_div, mul_div_assoc]
    linarith
  have key := eLpNorm_linrec_from μ hp1 hρ₁0 hρ₁1 (by positivity) hB hji hY0 hYm hstep h1 hee
  refine key.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  ring

/-!
## The family statements
-/

/-- **Input `ClosedJet0LpSteps`: the closed `δ₀` jet in every `L^p` at every step** `n_s ≤ j <
⌊WT⌋`, births included, on the alive set (the strengthening of `ClosedJet0Lp` from the no-birth
steps to all steps). -/
def ClosedJet0LpSteps : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator
          (fun y => jetDistance0 b E (b3ClosedX b E s h τ m W j y)))
          (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- **`ClosedJet1Start`: the closed `δ₁` at the restart** (at `j = n_s`):
`‖1_{A_{n_s}}δ₁(X_cl,n_s)‖_p ≤ C_p/W` at the stationary jet, whenever `n_s < ⌊WT⌋`. -/
def ClosedJet1Start : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, closeLen s W < ⌊(W : ℝ) * T⌋₊ →
      eLpNorm ((b3Alive b E s h τ m R W (closeLen s W) (Vs W)).indicator
          (fun y => jetDistance1 b E (b3Jet b E) (b3ClosedX b E s h τ m W (closeLen s W) y)))
          (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- `ClosedJet0LpSteps ⇒ ClosedJet0Lp` (no-birth steps are steps). -/
theorem closedJet0Lp_of_steps (h : ClosedJet0LpSteps) : ClosedJet0Lp := by
  intro b E np τ m T s h' K Vs hFD R p hp
  obtain ⟨C, hC, hev⟩ := h b E np τ m T s h' K Vs hFD R p hp
  exact ⟨C, hC, hev.mono fun W hW j hj => hW j (Finset.mem_filter.1 hj).1⟩

/-- **Main theorem: `ClosedJet1Lp`** from the contract hypotheses, the passivity (`hP`) and the
one-port recursion (`hRec`) of `b3ClosedX` (`ClosedInputPassive b3ClosedX` and
`ClosedInputRecursion b3ClosedX`), the closed `δ₀` at all steps and the closed `δ₁` at the
restart. -/
theorem closedJet1Lp_of (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ᶠ W in atTop,
        ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          ∀ᵐ y ∂closedLaw b W np, (passiveY (b3ClosedX b E s h τ m W j y)).PosSemidef)
    (hRec : ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ᶠ W in atTop,
        ∀ j : ℕ, closeLen s W ≤ j → j + 1 < ⌊(W : ℝ) * T⌋₊ →
          ∀ᵐ y ∂closedLaw b W np, b3ClosedX b E s h τ m W (j + 1) y =
            freshSchur E (b3ClosedX b E s h τ m W j y) (freshSample W j y.1.1))
    (h0 : ClosedJet0LpSteps) (hS : ClosedJet1Start) : ClosedJet1Lp := by
  intro b E np τ m T s h K Vs hFD R p hp
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, -, -, -, -, -⟩ := id hFD
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval (min (2 + E) (2 - E)) :=
    ⟨by have := min_le_left (2 + E) (2 - E); linarith,
      by have := min_le_right (2 + E) (2 - E); linarith⟩
  set κ := min (2 + E) (2 - E) with hκdef
  have hjs := b3Jet_spec hb0 hb hE1 hE2
  obtain ⟨d₀, ρ₁, C₂, Cm, Wm, hd₀, hρ₁0, hρ₁1, hC₂, hCm, hmean⟩ :=
    passiveJetMeanStep_holds (BlockBand.Transmission.PassiveLayer.passiveBounds_holds hGA hLp) b
      hb0 hb κ hκ
  obtain ⟨Cf, Wf, hCf, hfl⟩ := passiveJetFluctuationStep_holds hGA hLp b hb0 hb κ hκ p hp
  obtain ⟨C₀, hC₀, hev0⟩ := h0 b E np τ m T s h K Vs hFD R p hp
  obtain ⟨C₁, hC₁, hev1⟩ := hS b E np τ m T s h K Vs hFD R p hp
  have hM0 : 0 ≤ jetM b κ := by
    unfold jetM; have := etaLow_pos (by linarith : b < 1) hκ; positivity
  refine ⟨(C₁ + ((C₂ + jetM b κ / d₀) * C₀ + Cm + Cf) / (1 - ρ₁)), ?_, ?_⟩
  · have : 0 < 1 - ρ₁ := by linarith
    positivity
  filter_upwards [hev0, hev1, hP b E np τ m T s h K Vs hFD, hRec b E np τ m T s h K Vs hFD,
    hFD.2.2.2.2.2, eventually_ge_atTop (max (max Wm Wf) 1)] with W hW0 hW1 hWP hWR hVW hWb j hj
  simp only [max_le_iff] at hWb
  obtain ⟨⟨hWm, hWf⟩, hW1'⟩ := hWb
  obtain ⟨hjs', hjT⟩ := Finset.mem_Ico.1 (Finset.mem_filter.1 hj).1
  have hV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hXp : ∀ j', closeLen s W ≤ j' → j' ≤ j →
      ∀ᵐ y ∂closedLaw b W np, (passiveY (b3ClosedX b E s h τ m W j' y)).PosSemidef :=
    fun j' h1 h2 => hWP j' (Finset.mem_Ico.2 ⟨h1, lt_of_le_of_lt h2 hjT⟩)
  have hstart : eLpNorm ((b3Alive b E s h τ m R W (closeLen s W) (Vs W)).indicator fun y =>
      jet1V b E (b3Jet b E) (b3ClosedX b E s h τ m W (closeLen s W) y)) (ENNReal.ofReal p)
        (closedLaw b W np) ≤ ENNReal.ofReal (C₁ / W) :=
    (eLpNorm_congr_ae (indicator_jetDistance1_ae_eq (μ := closedLaw b W np) (by linarith) hE1
      hE2 (b3Jet b E) (b3ClosedX b E s h τ m W (closeLen s W))
      (b3Alive b E s h τ m R W (closeLen s W) (Vs W)) (hXp _ le_rfl hjs'))).symm.trans_le
      (hW1 (lt_of_le_of_lt hjs' hjT))
  have key := eLpNorm_closedJet1_le hb0 hb hκ hEb hjs hd₀ hρ₁0 hρ₁1 hC₂ hCm hCf hC₀ hC₁ hp hW1'
    (hmean W hWm E hEb (b3Jet b E) hjs)
    (fun X' hX' => jetFun_fluct hb0 hb hκ hfl hWf hEb X' hX')
    (fun j' => b3ClosedX b E s h τ m W j') (fun j' => b3Alive b E s h τ m R W j' (Vs W))
    (fun j' => genMem_b3Alive_succ_subset b E s h τ m R W j' (Vs W))
    (fun j' => nullMeasurableSet_b3Alive (by linarith) hE1 hE2 s h τ m R W j' hV) hjs'
    (fun j' => measurable_b3ClosedX b E s h τ m j')
    (fun j' h1 _ y => b3ClosedX_b3Ext h1 le_rfl y) hXp
    (fun j' h1 h2 => hWR j' h1 (by omega))
    (fun j' h1 h2 => hW0 j' (Finset.mem_Ico.2 ⟨h1, by omega⟩)) hstart
  exact (eLpNorm_congr_ae (indicator_jetDistance1_ae_eq (μ := closedLaw b W np) (by linarith)
    hE1 hE2 (b3Jet b E) (b3ClosedX b E s h τ m W j) (b3Alive b E s h τ m R W j (Vs W))
    (hXp _ hjs' le_rfl))).trans_le key

/-!
## The restart value from the open jet and the closing shift
-/

/-- The first-jet derivative `∂_w W⁻¹Tr(w - X)⁻¹` at `w = z_∂` (so `δ₁(X) = ‖jet1D X - s‖`). -/
def jet1D (b E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) : ℂ :=
  deriv (fun w : ℂ => (W : ℂ)⁻¹ * ((w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹).trace)
    (boundaryZ b E)

/-- **The closing shift of the first jet** at length `r`: `‖jet1D(X) - jet1D(X_r)‖`,
`X_r = pathX` the open one-port input. -/
def jet1Shift (b E : ℝ) {W np : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) (r : ℕ)
    (y : ProbedPath W np × ℝ) : ℝ :=
  ‖jet1D b E X - jet1D b E (pathX b E W r y.1.1)‖

/-- **`ClosedJet1ShiftLp`: the closing shift of `δ₁` at the restart is `O(1/W)` in every `L^p`**
on the alive set (the closing shifts the normalized near trace by `≤ C_pW⁻¹Σ_{omitted}t_i^p`; here
its `w`-derivative), whenever `n_s < ⌊WT⌋`. -/
def ClosedJet1ShiftLp : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, closeLen s W < ⌊(W : ℝ) * T⌋₊ →
      eLpNorm ((b3Alive b E s h τ m R W (closeLen s W) (Vs W)).indicator
          (fun y => jet1Shift b E (b3ClosedX b E s h τ m W (closeLen s W) y) (closeLen s W) y))
          (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

theorem closedLaw_map_path (b : ℝ) (W np : ℕ) :
    (closedLaw b W np).map (fun y : ProbedPath W np × ℝ => y.1.1) = growthPathLaw W b := by
  have := isProbabilityMeasure_growthPathLaw W b
  rw [show (fun y : ProbedPath W np × ℝ => y.1.1) = Prod.fst ∘ Prod.fst from rfl,
    ← Measure.map_map measurable_fst measurable_fst, closedLaw, Measure.map_fst_prod,
    measure_univ, one_smul, probedPathLaw, Measure.map_fst_prod, measure_univ, one_smul]

/-- **`ClosedJet1Start` from the open jet and the closing shift.** -/
theorem closedJet1Start_of_shift (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ᶠ W in atTop,
        ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          ∀ᵐ y ∂closedLaw b W np, (passiveY (b3ClosedX b E s h τ m W j y)).PosSemidef)
    (hSh : ClosedJet1ShiftLp) : ClosedJet1Start := by
  intro b E np τ m T s h K Vs hFD R p hp
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, hs, -, -, -, -⟩ := id hFD
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval (min (2 + E) (2 - E)) :=
    ⟨by have := min_le_left (2 + E) (2 - E); linarith,
      by have := min_le_right (2 + E) (2 - E); linarith⟩
  have hjs := b3Jet_spec hb0 hb hE1 hE2
  obtain ⟨Co, hCo⟩ := lengthUniform_jet_holds hMT hGA hLp b hb0 hb _ (s / 2) p hκ
    (by positivity) hp
  obtain ⟨W₀, hW₀⟩ := hCo s
  obtain ⟨Cs, hCs, hevs⟩ := hSh b E np τ m T s h K Vs hFD R p hp
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  refine ⟨Cs + max Co 0, by positivity, ?_⟩
  filter_upwards [hevs, hP b E np τ m T s h K Vs hFD, hFD.2.2.2.2.2,
    eventually_ge_atTop (max W₀ (max 1 ⌈2 / s⌉₊))] with W hWs hWP hVW hWb hlt
  have hWs := hWs hlt
  have hV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hfm : AEStronglyMeasurable ((b3Alive b E s h τ m R W (closeLen s W) (Vs W)).indicator
      fun y => jetDistance1 b E (b3Jet b E) (b3ClosedX b E s h τ m W (closeLen s W) y))
      (closedLaw b W np) :=
    (((measurable_jet1V b E (b3Jet b E)).comp (measurable_b3ClosedX b E s h τ m
      (closeLen s W))).aestronglyMeasurable.indicator₀ (nullMeasurableSet_b3Alive
        (by linarith) hE1 hE2 s h τ m R W (closeLen s W) hV)).congr
      (indicator_jetDistance1_ae_eq (by linarith) hE1 hE2 _ _ _
        (hWP _ (Finset.mem_Ico.2 ⟨le_rfl, hlt⟩))).symm
  simp only [max_le_iff] at hWb
  obtain ⟨hW0, hW1, hW2⟩ := hWb
  have hx0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  set r := closeLen s W with hr
  have hWs2 : 2 ≤ (W : ℝ) * s := by
    have h1 := (Nat.le_ceil (2 / s)).trans (by exact_mod_cast hW2 : (⌈2 / s⌉₊ : ℝ) ≤ W)
    rw [div_le_iff₀ hs] at h1
    linarith
  have hrlo : s / 2 * W ≤ r := by
    have := Nat.lt_floor_add_one ((W : ℝ) * s)
    rw [hr]
    nlinarith
  have hrhi : (r : ℝ) ≤ s * W := by
    rw [hr, mul_comm]; exact Nat.floor_le (by positivity)
  have hopen := hW₀ W hW0 E hEb (b3Jet b E) hjs r hrlo hrhi
  have hopen1 : eLpNorm (fun ω => jetDistance1 b E (b3Jet b E) (pathX b E W r ω))
      (ENNReal.ofReal p) (growthPathLaw W b) ≤ ENNReal.ofReal (max Co 0 / W) :=
    (le_add_self.trans hopen).trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) hx0.le))
  -- the open jet under the closed law
  have hae : (fun ω => jetDistance1 b E (b3Jet b E) (pathX b E W r ω)) =ᵐ[growthPathLaw W b]
      pathJetV b E (b3Jet b E) W r := pathJet1_ae_eq (by linarith) hE1 hE2 _ r
  have hgm : AEStronglyMeasurable (fun ω => jetDistance1 b E (b3Jet b E) (pathX b E W r ω))
      (growthPathLaw W b) :=
    (measurable_pathJetV b E (b3Jet b E) r).aestronglyMeasurable.congr hae.symm
  have hg : eLpNorm (fun y : ProbedPath W np × ℝ =>
      jetDistance1 b E (b3Jet b E) (pathX b E W r y.1.1)) (ENNReal.ofReal p)
      (closedLaw b W np) ≤ ENNReal.ofReal (max Co 0 / W) := by
    have hm : AEMeasurable (fun y : ProbedPath W np × ℝ => y.1.1) (closedLaw b W np) :=
      (measurable_fst.comp measurable_fst).aemeasurable
    rw [← closedLaw_map_path b W np] at hgm
    have := eLpNorm_map_measure hgm hm (p := ENNReal.ofReal p)
    rw [closedLaw_map_path b W np] at this
    rw [show (fun y : ProbedPath W np × ℝ => jetDistance1 b E (b3Jet b E) (pathX b E W r y.1.1)) =
      (fun ω => jetDistance1 b E (b3Jet b E) (pathX b E W r ω)) ∘ fun y => y.1.1 from rfl,
      ← this]
    exact hopen1
  -- the pointwise triangle inequality
  set A := b3Alive b E s h τ m R W r (Vs W)
  have hpt : ∀ y, ‖A.indicator (fun y => jetDistance1 b E (b3Jet b E)
      (b3ClosedX b E s h τ m W r y)) y‖ ≤
      ‖(A.indicator (fun y => jet1Shift b E (b3ClosedX b E s h τ m W r y) r y) +
        fun y : ProbedPath W np × ℝ => jetDistance1 b E (b3Jet b E) (pathX b E W r y.1.1)) y‖ :=
      by
    intro y
    have hn1 : 0 ≤ jetDistance1 b E (b3Jet b E) (pathX b E W r y.1.1) := norm_nonneg _
    by_cases hy : y ∈ A
    · have ha : 0 ≤ jetDistance1 b E (b3Jet b E) (b3ClosedX b E s h τ m W r y) := norm_nonneg _
      have hb' : 0 ≤ jet1Shift b E (b3ClosedX b E s h τ m W r y) r y := norm_nonneg _
      rw [Set.indicator_of_mem hy, Pi.add_apply, Set.indicator_of_mem hy,
        Real.norm_of_nonneg ha, Real.norm_of_nonneg (add_nonneg hb' hn1)]
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    · rw [Set.indicator_of_notMem hy, Pi.add_apply, Set.indicator_of_notMem hy, zero_add,
        norm_zero]
      exact norm_nonneg _
  refine (eLpNorm_mono hfm hpt).trans ((eLpNorm_add_le hp1).trans ?_)
  refine (add_le_add hWs hg).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_div]

/-- **`ClosedJet1Lp` from the contract hypotheses, passivity, recursion, the closed `δ₀` at all
steps, and the closing shift of `δ₁` at the restart.** -/
theorem closedJet1Lp_of_shift (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient)
    (hP : ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ᶠ W in atTop,
        ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          ∀ᵐ y ∂closedLaw b W np, (passiveY (b3ClosedX b E s h τ m W j y)).PosSemidef)
    (hRec : ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ᶠ W in atTop,
        ∀ j : ℕ, closeLen s W ≤ j → j + 1 < ⌊(W : ℝ) * T⌋₊ →
          ∀ᵐ y ∂closedLaw b W np, b3ClosedX b E s h τ m W (j + 1) y =
            freshSchur E (b3ClosedX b E s h τ m W j y) (freshSample W j y.1.1))
    (h0 : ClosedJet0LpSteps) (hSh : ClosedJet1ShiftLp) : ClosedJet1Lp :=
  closedJet1Lp_of hGA hLp hP hRec h0 (closedJet1Start_of_shift hMT hGA hLp hP hSh)

end BlockBand.SourceProcess.PhysApprox.B3.Jet1
