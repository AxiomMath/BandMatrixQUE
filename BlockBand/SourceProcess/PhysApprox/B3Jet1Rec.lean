module

public import BlockBand.SourceProcess.PhysApprox.B3MeanFresh
public import BlockBand.SourceProcess.PhysApprox.B3StepK
public import BlockBand.Transmission.PathJet.PathRec

/-!
# Closed jet recursions without burn-in (generic in the jet functional)

Two pieces of the closed jet argument (the iteration of the contraction for the passive jet
moments) that do not depend on the jet index:

* **`eLpNorm_jetFluctOf_le`**: for any jointly measurable fresh functional `Φ(X, F)` and an
  input `X` that is Borel, `b3Ext W j`-invariant and a.e. passive under `closedLaw`, the centred
  fresh error `‖Φ(X, F_j) - E_F Φ(X, F)‖` has `L^p(closedLaw)` norm at most any uniform bound of
  the fresh `L^p` norm over passive inputs (Fubini over the fresh layer). With
  `Φ = freshPortTrace` this is `eLpNorm_jetFluct_le` (`δ₀`); with `Φ = jetFun` it is
  the `δ₁` error of the first jet.
* **`eLpNorm_linrec_from`** (a shifted `eLpNorm_linrec`): if `0 ≤ Y_{j+1} ≤ ρY_j + e_j` a.e.
  for `j₀ ≤ j < i`, `‖Y_{j₀}‖_p ≤ A` and `‖e_j‖_p ≤ B`, then `‖Y_i‖_p ≤ A + B/(1-ρ)`: the start
  value is propagated, **no burn-in** is needed when the start is already at the target scale;
  `indicator_step_le`: the step survives restriction to a decreasing family of sets.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet1

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped ENNReal ComplexOrder

/-! ## The linear recursion from a start, and its restriction to decreasing sets -/

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The linear recursion from step `j₀`**: `‖Y_i‖_p ≤ A + B/(1-ρ)` for `j₀ ≤ i`. -/
theorem eLpNorm_linrec_from (μ : Measure Ω) {Y e : ℕ → Ω → ℝ} {ρ A B : ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hA : 0 ≤ A) (hB : 0 ≤ B) {j₀ i : ℕ}
    (hji : j₀ ≤ i) (hY0 : ∀ j ω, 0 ≤ Y j ω) (hYm : ∀ j, AEStronglyMeasurable (Y j) μ)
    (hstep : ∀ j, j₀ ≤ j → j < i → ∀ᵐ ω ∂μ, Y (j + 1) ω ≤ ρ * Y j ω + e j ω)
    (h0 : eLpNorm (Y j₀) p μ ≤ ENNReal.ofReal A)
    (he : ∀ j, j₀ ≤ j → j < i → eLpNorm (e j) p μ ≤ ENNReal.ofReal B) :
    eLpNorm (Y i) p μ ≤ ENNReal.ofReal (A + B / (1 - ρ)) := by
  have h := BlockBand.Transmission.PathJet.eLpNorm_linrec μ (y := fun k => Y (j₀ + k - 1))
    (e := fun k => e (j₀ + k - 1)) hp hρ0 hρ1 hA hB (n := i - j₀ + 1)
    (fun k ω => hY0 _ ω) (fun k => hYm _)
    (fun k hk1 hkn => by
      show ∀ᵐ ω ∂μ, Y (j₀ + (k + 1) - 1) ω ≤ ρ * Y (j₀ + k - 1) ω + e (j₀ + k - 1) ω
      rw [show j₀ + (k + 1) - 1 = j₀ + k - 1 + 1 by omega]
      exact hstep _ (by omega) (by omega))
    (by show eLpNorm (Y (j₀ + 1 - 1)) p μ ≤ _; rw [Nat.add_sub_cancel]; exact h0)
    (fun k hk1 hkn => he _ (by omega) (by omega)) (i - j₀ + 1) (by omega) le_rfl
  have e1 : j₀ + (i - j₀ + 1) - 1 = i := by omega
  simp only [e1] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have : ρ ^ (i - j₀ + 1 - 1) * A ≤ A := mul_le_of_le_one_left hA (pow_le_one₀ hρ0 hρ1.le)
  linarith

omit [MeasurableSpace Ω] in
/-- **The step on a decreasing family of sets**: from `v' ≤ ρv + (kf + c + g)` with all terms
nonnegative and `S' ⊆ S`, `1_{S'}v' ≤ ρ1_Sv + (k1_Sf + c + g)`. -/
theorem indicator_step_le {S S' : Set Ω} (hS : S' ⊆ S) {v v' f g : Ω → ℝ} {ρ k c : ℝ}
    (hρ : 0 ≤ ρ) (hk : 0 ≤ k) (hc : 0 ≤ c) (hv : ∀ ω, 0 ≤ v ω) (hf : ∀ ω, 0 ≤ f ω)
    (hg : ∀ ω, 0 ≤ g ω) (ω : Ω) (h : v' ω ≤ ρ * v ω + (k * f ω + c + g ω)) :
    S'.indicator v' ω ≤ ρ * S.indicator v ω + (k * S.indicator f ω + c + g ω) := by
  by_cases h' : ω ∈ S'
  · rw [Set.indicator_of_mem h', Set.indicator_of_mem (hS h'), Set.indicator_of_mem (hS h')]
    exact h
  · rw [Set.indicator_of_notMem h']
    have h1 : 0 ≤ S.indicator v ω := Set.indicator_nonneg (fun x _ => hv x) ω
    have h2 : 0 ≤ S.indicator f ω := Set.indicator_nonneg (fun x _ => hf x) ω
    have := hg ω
    positivity

end Abstract

/-! ## The fresh error of a generic jet functional under the closed law -/

variable {W np : ℕ}

/-- The fresh error `‖Φ(X, F_j) - E_F Φ(X, F)‖` of the closed step `j → j+1` at the input `X`. -/
def jetFluctOf (Φ : Matrix (Fin W) (Fin W) ℂ → LayerSample W .oneBlockOnePort → ℂ) (b : ℝ)
    (X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ) (j : ℕ) (y : ProbedPath W np × ℝ) :
    ℝ :=
  ‖Φ (X y) (freshSample W j y.1.1) - ∫ F, Φ (X y) F ∂freshLaw W b‖

theorem jetFluctOf_nonneg (Φ : Matrix (Fin W) (Fin W) ℂ → LayerSample W .oneBlockOnePort → ℂ)
    (b : ℝ) (X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ) (j : ℕ)
    (y : ProbedPath W np × ℝ) : 0 ≤ jetFluctOf Φ b X j y := norm_nonneg _

/-- The centred fresh value on (conditioning coordinates) × (fresh layer). -/
def jetPhiOf (Φ : Matrix (Fin W) (Fin W) ℂ → LayerSample W .oneBlockOnePort → ℂ) (b : ℝ)
    (X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ) (j : ℕ)
    (q : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort) : ℝ :=
  ‖Φ (X (b3Rebuild W j q.1)) q.2 - ∫ F, Φ (X (b3Rebuild W j q.1)) F ∂freshLaw W b‖

section Fresh

variable {Φ : Matrix (Fin W) (Fin W) ℂ → LayerSample W .oneBlockOnePort → ℂ}
  (hΦ : Measurable fun q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort =>
    Φ q.1 q.2)
include hΦ

theorem measurable_jetPhiOf (b : ℝ) {X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ}
    (hX : Measurable X) (j : ℕ) : Measurable (jetPhiOf Φ b X j) := by
  have hXr : Measurable fun x => X (b3Rebuild W j x) := hX.comp (measurable_b3Rebuild W j)
  have hF : Measurable fun q : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
      LayerSample W .oneBlockOnePort => Φ (X (b3Rebuild W j q.1)) q.2 :=
    hΦ.comp ((hXr.comp measurable_fst).prodMk measurable_snd)
  have hI : Measurable fun x : PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) =>
      ∫ F, Φ (X (b3Rebuild W j x)) F ∂freshLaw W b :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := freshLaw W b)).measurable
  exact (hF.sub (hI.comp measurable_fst)).norm

omit hΦ in
theorem jetFluctOf_eq_comp (b : ℝ) {X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ}
    {j : ℕ} (hinv : ∀ y, X (b3Ext W j y) = X y) :
    jetFluctOf Φ b X j = jetPhiOf Φ b X j ∘ fun y => (b3Past W j y, freshSample W j y.1.1) := by
  funext y
  simp only [jetFluctOf, jetPhiOf, Function.comp, b3Rebuild_b3Past, hinv]

theorem measurable_jetFluctOf (b : ℝ) {X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ}
    (hX : Measurable X) {j : ℕ} (hinv : ∀ y, X (b3Ext W j y) = X y) :
    Measurable (jetFluctOf Φ b X j) := by
  have hT : Measurable fun y : ProbedPath W np × ℝ => (b3Past W j y, freshSample W j y.1.1) :=
    (measurable_b3Past W j).prodMk
      ((measurable_freshSample W j).comp (measurable_fst.comp measurable_fst))
  rw [jetFluctOf_eq_comp b hinv]
  exact (measurable_jetPhiOf hΦ b hX j).comp hT

/-- **Moments of the closed fresh error of `Φ`**: a uniform fresh `L^p` bound over passive
inputs is inherited under `closedLaw` by a Borel, past-determined, a.e. passive input. -/
theorem eLpNorm_jetFluctOf_le {b p C : ℝ} (hp : 0 < p)
    {X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ} (hX : Measurable X) {j : ℕ}
    (hinv : ∀ y, X (b3Ext W j y) = X y)
    (hpas : ∀ᵐ y ∂closedLaw b W np, (passiveY (X y)).PosSemidef)
    (hfl : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      eLpNorm (fun ω => ‖Φ X ω - ∫ ω', Φ X ω' ∂freshLaw W b‖) (ENNReal.ofReal p)
        (freshLaw W b) ≤ ENNReal.ofReal C) :
    eLpNorm (jetFluctOf Φ b X j) (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal C := by
  have hT : Measurable fun y : ProbedPath W np × ℝ => (b3Past W j y, freshSample W j y.1.1) :=
    (measurable_b3Past W j).prodMk
      ((measurable_freshSample W j).comp (measurable_fst.comp measurable_fst))
  have hP := measurable_jetPhiOf hΦ b hX j
  rw [jetFluctOf_eq_comp b hinv, ← eLpNorm_map_measure hP.aestronglyMeasurable
    hT.aemeasurable, closedLaw_map_past_fresh]
  refine eLpNorm_prod_le_of_section _ _ hP hp ?_
  have hXr : Measurable fun x => X (b3Rebuild W j x) := hX.comp (measurable_b3Rebuild W j)
  have hset : MeasurableSet {x : PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) |
      (passiveY (X (b3Rebuild W j x))).PosSemidef} := hXr step_measurableSet_passive
  have hpasP : ∀ᵐ x ∂((pastLaw W j b).prod (probePhaseLaw W np)),
      (passiveY (X (b3Rebuild W j x))).PosSemidef := by
    rw [← closedLaw_map_b3Past b W np j, ae_map_iff (measurable_b3Past W j).aemeasurable hset]
    filter_upwards [hpas] with y hy
    rw [b3Rebuild_b3Past, hinv]
    exact hy
  filter_upwards [hpasP] with x hx
  exact hfl _ hx

end Fresh

end BlockBand.SourceProcess.PhysApprox.B3.Jet1
