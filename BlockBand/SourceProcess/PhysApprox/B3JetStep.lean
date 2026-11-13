module

public import BlockBand.SourceProcess.PhysApprox.B3JetRec
public import BlockBand.SourceProcess.PhysApprox.B3MeanFresh
public import BlockBand.SourceProcess.PhysApprox.B3StepK
public import BlockBand.Transmission.PathScalar.AbsorbedStep
public import BlockBand.Transmission.PathScalar.Dissipative
public import BlockBand.Transmission.PathScalar.Exit

/-!
# The closed scalar jet at one width (fixed-`W` recursion)

The passive jet moments, from the one-layer recursion `δ_{0,+} ≤ ρδ₀ + C/W² + |ξ₊|`.

Setting: one width `W`, the closed law `closedLaw b W np`, and a family of one-port inputs
`X j` (`j₀ ≤ j ≤ i`) that are Borel, functions of the past at `j` (`b3Ext W j`-invariant),
a.e. passive, and follow the fresh one-port recursion `X (j+1) = freshSchur E (X j) F_j` a.e.
(`F_j = freshSample W j`). No law of the path before `j₀` is used: in particular the closed path
is **not** required to have the law `pathLaw`.

* `jet_step_le` (deterministic): on the scalar domain, `δ₀(X₊) ≤ ρδ₀(X) + C/W² + ξ(X, F)` for
  every fresh layer `F`, from the shape of `PassiveMeanStep`;
* `eLpNorm_jetFluct_le`: the fresh error of the closed step has `‖ξ_{j+1}‖_p ≤ C_p/W` under
  `closedLaw` (Fubini over the fresh layer, `closedLaw_map_past_fresh`, and the shape of
  `PassiveFluctuationStep`, uniform over passive inputs);
* **`lintegral_jet_four_le`**: `E δ₀(X i)⁴ ≤ (ρ^{i-j₀}d₀/2 + (C/W² + C₄/W)/(1-ρ))⁴
  + M⁴(μ(δ₀(X j₀) > d₀/2) + (i - j₀)(t⁻¹C₆/W)⁶)`, `M = η⁻¹ + 1`, `t = (1-ρ)d₀/2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped ENNReal ComplexOrder

variable {W np : ℕ}

/-! ## The deterministic step -/

/-- **One fresh step on the scalar domain**: `δ₀(X₊) ≤ ρδ₀(X) + C/W² + ξ(X, F)`. -/
theorem jet_step_le {b E d₀ ρ Cm : ℝ}
    (hmean : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      jetDistance0 b E X ≤ d₀ →
        ‖(∫ ω, freshPortTrace b E X ω ∂freshLaw W b) - matchedA E‖ ≤
          ρ * jetDistance0 b E X + Cm / (W : ℝ) ^ 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef) (hd : jetDistance0 b E X ≤ d₀)
    (F : LayerSample W .oneBlockOnePort) :
    jetDistance0 b E (freshSchur E X F) ≤ ρ * jetDistance0 b E X + Cm / (W : ℝ) ^ 2 +
      ‖freshPortTrace b E X F - ∫ F', freshPortTrace b E X F' ∂freshLaw W b‖ := by
  rw [jetDistance0_freshSchur]
  have h := norm_sub_le_norm_sub_add_norm_sub (freshPortTrace b E X F)
    (∫ F', freshPortTrace b E X F' ∂freshLaw W b) (matchedA E)
  have h2 := hmean X hX hd
  linarith

/-! ## The fresh error under the closed law -/

/-- The fresh error of the closed step `j → j+1` at the input `X`. -/
def jetFluct (b E : ℝ) (X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ) (j : ℕ)
    (y : ProbedPath W np × ℝ) : ℝ :=
  ‖freshPortTrace b E (X y) (freshSample W j y.1.1) -
    ∫ F, freshPortTrace b E (X y) F ∂freshLaw W b‖

theorem jetFluct_nonneg (b E : ℝ) (X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ) (j : ℕ)
    (y : ProbedPath W np × ℝ) : 0 ≤ jetFluct b E X j y := norm_nonneg _

/-- The centred fresh trace on (conditioning coordinates) × (fresh layer). -/
def jetPhi (b E : ℝ) (X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ) (j : ℕ)
    (q : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort) : ℝ :=
  ‖freshPortTrace b E (X (b3Rebuild W j q.1)) q.2 -
    ∫ F, freshPortTrace b E (X (b3Rebuild W j q.1)) F ∂freshLaw W b‖

theorem measurable_jetPhi (b E : ℝ) {X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ}
    (hX : Measurable X) (j : ℕ) : Measurable (jetPhi b E X j) := by
  have hXr : Measurable fun x => X (b3Rebuild W j x) := hX.comp (measurable_b3Rebuild W j)
  have hF : Measurable fun q : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
      LayerSample W .oneBlockOnePort => freshPortTrace b E (X (b3Rebuild W j q.1)) q.2 :=
    measurable_freshPortTrace_comp b E (hXr.comp measurable_fst) measurable_snd
  have hI : Measurable fun x : PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) =>
      ∫ F, freshPortTrace b E (X (b3Rebuild W j x)) F ∂freshLaw W b :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := freshLaw W b)).measurable
  exact (hF.sub (hI.comp measurable_fst)).norm

theorem jetFluct_eq_comp (b E : ℝ) {X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ} {j : ℕ}
    (hinv : ∀ y, X (b3Ext W j y) = X y) :
    jetFluct b E X j = jetPhi b E X j ∘ fun y => (b3Past W j y, freshSample W j y.1.1) := by
  funext y
  simp only [jetFluct, jetPhi, Function.comp, b3Rebuild_b3Past, hinv]

theorem measurable_jetFluct (b E : ℝ) {X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ}
    (hX : Measurable X) {j : ℕ} (hinv : ∀ y, X (b3Ext W j y) = X y) :
    Measurable (jetFluct b E X j) := by
  have hT : Measurable fun y : ProbedPath W np × ℝ => (b3Past W j y, freshSample W j y.1.1) :=
    (measurable_b3Past W j).prodMk
      ((measurable_freshSample W j).comp (measurable_fst.comp measurable_fst))
  rw [jetFluct_eq_comp b E hinv]
  exact (measurable_jetPhi b E hX j).comp hT

/-- **Moments of the closed fresh error**: `‖ξ_{j+1}‖_{L^p(closedLaw)} ≤ C/W` from the uniform
fresh bound over passive inputs. -/
theorem eLpNorm_jetFluct_le {b E p C : ℝ} (hp : 0 < p)
    {X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ} (hX : Measurable X) {j : ℕ}
    (hinv : ∀ y, X (b3Ext W j y) = X y)
    (hpas : ∀ᵐ y ∂closedLaw b W np, (passiveY (X y)).PosSemidef)
    (hfl : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      eLpNorm (fun ω => ‖freshPortTrace b E X ω - ∫ ω', freshPortTrace b E X ω' ∂freshLaw W b‖)
        (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal (C / W)) :
    eLpNorm (jetFluct b E X j) (ENNReal.ofReal p) (closedLaw b W np) ≤
      ENNReal.ofReal (C / W) := by
  have hT : Measurable fun y : ProbedPath W np × ℝ => (b3Past W j y, freshSample W j y.1.1) :=
    (measurable_b3Past W j).prodMk
      ((measurable_freshSample W j).comp (measurable_fst.comp measurable_fst))
  have hΦ := measurable_jetPhi b E hX j
  rw [jetFluct_eq_comp b E hinv, ← eLpNorm_map_measure hΦ.aestronglyMeasurable hT.aemeasurable,
    closedLaw_map_past_fresh]
  refine eLpNorm_prod_le_of_section _ _ hΦ hp ?_
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
  simp only [jetPhi]
  exact hfl _ hx

/-! ## The fourth moment at one width -/

/-- **The closed jet at one width.** For inputs `X j`, `j₀ ≤ j ≤ i`, that are Borel,
past-determined, a.e. passive and follow the fresh recursion a.e.:
`E δ₀(X i)⁴ ≤ (ρ^{i-j₀}d₀/2 + (C/W² + C₄/W)/(1-ρ))⁴ + M⁴(μ(δ₀(X j₀) > d₀/2) + (i-j₀)t⁻⁶(C₆/W)⁶)`
with `M = η⁻¹ + 1` and `t = (1-ρ)d₀/2`. -/
theorem lintegral_jet_four_le {b E d₀ ρ Cm C4 C6 : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (hd₀ : 0 < d₀) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hCm : 0 ≤ Cm)
    (hC4 : 0 ≤ C4) (hC6 : 0 ≤ C6) (hW : Cm / (W : ℝ) ^ 2 ≤ (1 - ρ) * d₀ / 2)
    (hmean : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      jetDistance0 b E X ≤ d₀ →
        ‖(∫ ω, freshPortTrace b E X ω ∂freshLaw W b) - matchedA E‖ ≤
          ρ * jetDistance0 b E X + Cm / (W : ℝ) ^ 2)
    (hfl4 : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      eLpNorm (fun ω => ‖freshPortTrace b E X ω - ∫ ω', freshPortTrace b E X ω' ∂freshLaw W b‖)
        (ENNReal.ofReal 4) (freshLaw W b) ≤ ENNReal.ofReal (C4 / W))
    (hfl6 : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      eLpNorm (fun ω => ‖freshPortTrace b E X ω - ∫ ω', freshPortTrace b E X ω' ∂freshLaw W b‖)
        (ENNReal.ofReal 6) (freshLaw W b) ≤ ENNReal.ofReal (C6 / W))
    (X : ℕ → ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ) {j₀ i : ℕ} (hji : j₀ ≤ i)
    (hXm : ∀ j, j₀ ≤ j → j ≤ i → Measurable (X j))
    (hXi : ∀ j, j₀ ≤ j → j ≤ i → ∀ y, X j (b3Ext W j y) = X j y)
    (hXp : ∀ j, j₀ ≤ j → j ≤ i → ∀ᵐ y ∂closedLaw b W np, (passiveY (X j y)).PosSemidef)
    (hXr : ∀ j, j₀ ≤ j → j < i → ∀ᵐ y ∂closedLaw b W np,
      X (j + 1) y = freshSchur E (X j y) (freshSample W j y.1.1)) :
    ∫⁻ y, ENNReal.ofReal (jetDistance0 b E (X i y) ^ 4) ∂closedLaw b W np ≤
      ENNReal.ofReal ((ρ ^ (i - j₀) * (d₀ / 2) + (Cm / (W : ℝ) ^ 2 + C4 / W) / (1 - ρ)) ^ 4) +
        ENNReal.ofReal (((etaZ b E)⁻¹ + 1) ^ 4) *
          (closedLaw b W np {y | d₀ / 2 < jetDistance0 b E (X j₀ y)} +
            ENNReal.ofReal ((i - j₀ : ℕ) * (((1 - ρ) * d₀ / 2)⁻¹ ^ 6 * (C6 / W) ^ 6))) := by
  set μ := closedLaw b W np
  set cl : ℕ → ℕ := fun k => max j₀ (min k i) with hcl
  have hcl1 : ∀ k, j₀ ≤ cl k := fun k => le_max_left _ _
  have hcl2 : ∀ k, cl k ≤ i := fun k => max_le hji (min_le_right _ _)
  have hcl : ∀ k, j₀ ≤ k → k ≤ i → cl k = k := fun k h1 h2 => by
    simp only [hcl]; omega
  set n := i - j₀ + 1 with hn
  set δ : ℕ → ProbedPath W np × ℝ → ℝ := fun k y => jetDistance0 b E (X (cl (j₀ + k - 1)) y)
  set ξ : ℕ → ProbedPath W np × ℝ → ℝ := fun k => jetFluct b E (X (cl (j₀ + k - 2)))
    (cl (j₀ + k - 2))
  set t := (1 - ρ) * d₀ / 2 with ht
  have h1ρ : 0 < 1 - ρ := by linarith
  have ht0 : 0 < t := by positivity
  have hc : 0 ≤ Cm / (W : ℝ) ^ 2 := by positivity
  have hct : Cm / (W : ℝ) ^ 2 + t ≤ (1 - ρ) * d₀ := by rw [ht]; linarith
  have hδ0 : ∀ k y, 0 ≤ δ k y := fun k y => norm_nonneg _
  have hξ0 : ∀ k y, 0 ≤ ξ k y := fun k y => jetFluct_nonneg b E _ _ y
  have hδm : ∀ k, Measurable (δ k) := fun k =>
    (measurable_jetDistance0 b E).comp (hXm _ (hcl1 _) (hcl2 _))
  have hξm : ∀ k, Measurable (ξ k) := fun k =>
    measurable_jetFluct b E (hXm _ (hcl1 _) (hcl2 _)) (hXi _ (hcl1 _) (hcl2 _))
  have hstep : ∀ᵐ y ∂μ, ∀ k, 1 ≤ k → k < n → δ k y ≤ d₀ →
      δ (k + 1) y ≤ ρ * δ k y + Cm / (W : ℝ) ^ 2 + ξ (k + 1) y := by
    rw [ae_all_iff]
    intro k
    by_cases hk : 1 ≤ k ∧ k < n
    · have hj1 : j₀ ≤ j₀ + k - 1 := by omega
      have hj2 : j₀ + k - 1 < i := by omega
      have e1 : cl (j₀ + k - 1) = j₀ + k - 1 := hcl _ hj1 hj2.le
      have e2 : cl (j₀ + (k + 1) - 1) = j₀ + k - 1 + 1 := by
        rw [show j₀ + (k + 1) - 1 = j₀ + k - 1 + 1 by omega]; exact hcl _ (by omega) (by omega)
      have e3 : cl (j₀ + (k + 1) - 2) = j₀ + k - 1 := by
        rw [show j₀ + (k + 1) - 2 = j₀ + k - 1 by omega]; exact hcl _ hj1 hj2.le
      filter_upwards [hXr _ hj1 hj2, hXp _ hj1 hj2.le] with y hy hp _ _ hd
      simp only [δ, ξ, e1, e2, e3] at hd ⊢
      rw [hy]
      exact jet_step_le hmean hp hd _
    · exact Filter.Eventually.of_forall fun y h1 h2 => absurd ⟨h1, h2⟩ hk
  have hξ4 : ∀ k, 2 ≤ k → k ≤ n → eLpNorm (ξ k) (ENNReal.ofReal 4) μ ≤
      ENNReal.ofReal (C4 / W) := fun k _ _ =>
    eLpNorm_jetFluct_le (by norm_num) (hXm _ (hcl1 _) (hcl2 _)) (hXi _ (hcl1 _) (hcl2 _))
      (hXp _ (hcl1 _) (hcl2 _)) hfl4
  have hM : ∀ᵐ y ∂μ, δ n y ≤ (etaZ b E)⁻¹ + 1 := by
    filter_upwards [hXp _ (hcl1 (j₀ + n - 1)) (hcl2 _)] with y hy
    exact jetDistance0_le_bound hb0 hb hE1 hE2 hy
  have key := lintegral_delta_four_geom_le μ (t := t) hρ0 hρ1 hd₀ hc hct (by positivity) hδ0 hξ0
    hδm hξm hstep hξ4 (by omega : 1 ≤ n) hM
  have hbad := measure_bad_le (δ := δ) (ξ := ξ) (d := d₀) (t := t) μ n
  have hm6 : ∀ k ∈ Finset.Icc 2 n, μ {y | t < ξ k y} ≤
      ENNReal.ofReal (t⁻¹ ^ 6 * (C6 / W) ^ 6) := fun k _ => by
    have h := markov_ofReal μ (hξ0 k) (by norm_num : (0 : ℝ) < 6) ht0 (by positivity)
      (eLpNorm_jetFluct_le (by norm_num) (hXm _ (hcl1 _) (hcl2 _)) (hXi _ (hcl1 _) (hcl2 _))
        (hXp _ (hcl1 _) (hcl2 _)) hfl6)
    rwa [Real.rpow_ofNat, Real.rpow_ofNat] at h
  have hsum : ∑ k ∈ Finset.Icc 2 n, μ {y | t < ξ k y} ≤
      ENNReal.ofReal ((i - j₀ : ℕ) * (t⁻¹ ^ 6 * (C6 / W) ^ 6)) := by
    refine (Finset.sum_le_card_nsmul _ _ _ hm6).trans ?_
    rw [nsmul_eq_mul, Nat.card_Icc, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    have hle : n + 1 - 2 ≤ i - j₀ := by omega
    exact mul_le_mul' (by exact_mod_cast hle) le_rfl
  have e0 : cl (j₀ + 1 - 1) = j₀ := by
    rw [show j₀ + 1 - 1 = j₀ by omega]; exact hcl _ le_rfl hji
  have eδ1 : {y | d₀ / 2 < δ 1 y} = {y | d₀ / 2 < jetDistance0 b E (X j₀ y)} := by
    simp only [δ, e0]
  have en : cl (j₀ + n - 1) = i := by
    rw [show j₀ + n - 1 = i by omega]; exact hcl _ hji le_rfl
  have hn1 : n - 1 = i - j₀ := by omega
  have eint : ∫⁻ y, ENNReal.ofReal (jetDistance0 b E (X i y) ^ 4) ∂μ =
      ∫⁻ y, ENNReal.ofReal (δ n y ^ 4) ∂μ :=
    lintegral_congr fun y => by simp only [δ, en]
  calc ∫⁻ y, ENNReal.ofReal (jetDistance0 b E (X i y) ^ 4) ∂μ
      = ∫⁻ y, ENNReal.ofReal (δ n y ^ 4) ∂μ := eint
    _ ≤ _ := key
    _ ≤ _ := by
        rw [hn1]
        gcongr
        exact hbad.trans (add_le_add (le_of_eq (congrArg μ eδ1)) hsum)

end BlockBand.SourceProcess.PhysApprox.B3.Jet
