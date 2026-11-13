module

public import BlockBand.SourceProcess.PhysApprox.B3JetShift
public import BlockBand.SourceProcess.PhysApprox.B3CovRepErr

/-!
# The closed `δ₀` jet in every `L^p` from the closing time on

* `eLpNorm_jet_le`: the fixed-`W` bound;
* **`closedJetLp_of`**: `Regular + Recursion + StartLp ⇒ ‖δ₀(Xcl_j)‖_p ≤ C_p/W` at every step
  `n_s ≤ j < ⌊WT⌋` (unstopped);
* **`closedJetL4Fam_b3ClosedX_of_start`**: **`ClosedJetL4Fam b3ClosedX`** from the same hypotheses
  (with weaker hypotheses: `closedJetL4Fam_b3ClosedX_of_shift`);
* `closedJetEntrance_of_startLp`: the start estimate implies the entrance estimate at `s' = s`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.LengthUniform BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.ClosedPath
open scoped ENNReal ComplexOrder

variable {W np : ℕ}

/-!
## The fixed-`W` bound with an `L^p` start
-/

/-- **The closed jet at one width with an `L^p` start**: `‖δ₀(X i)‖_p ≤ s₁ + (C/W² + C_p/W)/(1-ρ)
+ (μ(δ₀(X j₀) > d₀/2) + (i - j₀)(t⁻¹C_q/W)^{p+2})^{1/p} M`, `M = η⁻¹ + 1`, `t = (1-ρ)d₀/2`. -/
theorem eLpNorm_jet_le {b E d₀ ρ Cm Cp Cq p s₁ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (hp : 1 ≤ p) (hd₀ : 0 < d₀) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hCm : 0 ≤ Cm) (hCp : 0 ≤ Cp) (hCq : 0 ≤ Cq) (hs₁ : 0 ≤ s₁)
    (hW : Cm / (W : ℝ) ^ 2 ≤ (1 - ρ) * d₀ / 2)
    (hmean : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      jetDistance0 b E X ≤ d₀ →
        ‖(∫ ω, freshPortTrace b E X ω ∂freshLaw W b) - matchedA E‖ ≤
          ρ * jetDistance0 b E X + Cm / (W : ℝ) ^ 2)
    (hflp : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      eLpNorm (fun ω => ‖freshPortTrace b E X ω - ∫ ω', freshPortTrace b E X ω' ∂freshLaw W b‖)
        (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal (Cp / W))
    (hflq : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      eLpNorm (fun ω => ‖freshPortTrace b E X ω - ∫ ω', freshPortTrace b E X ω' ∂freshLaw W b‖)
        (ENNReal.ofReal (p + 2)) (freshLaw W b) ≤ ENNReal.ofReal (Cq / W))
    (X : ℕ → ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ) {j₀ i : ℕ} (hji : j₀ ≤ i)
    (hXm : ∀ j, j₀ ≤ j → j ≤ i → Measurable (X j))
    (hXi : ∀ j, j₀ ≤ j → j ≤ i → ∀ y, X j (b3Ext W j y) = X j y)
    (hXp : ∀ j, j₀ ≤ j → j ≤ i → ∀ᵐ y ∂closedLaw b W np, (passiveY (X j y)).PosSemidef)
    (hXr : ∀ j, j₀ ≤ j → j < i → ∀ᵐ y ∂closedLaw b W np,
      X (j + 1) y = freshSchur E (X j y) (freshSample W j y.1.1))
    (hstart : eLpNorm (fun y => jetDistance0 b E (X j₀ y)) (ENNReal.ofReal p) (closedLaw b W np) ≤
      ENNReal.ofReal s₁) :
    eLpNorm (fun y => jetDistance0 b E (X i y)) (ENNReal.ofReal p) (closedLaw b W np) ≤
      ENNReal.ofReal (s₁ + (Cm / (W : ℝ) ^ 2 + Cp / W) / (1 - ρ)) +
        (closedLaw b W np {y | d₀ / 2 < jetDistance0 b E (X j₀ y)} +
          ENNReal.ofReal ((i - j₀ : ℕ) *
            (((1 - ρ) * d₀ / 2)⁻¹ ^ (p + 2) * (Cq / W) ^ (p + 2)))) ^
          (ENNReal.ofReal p).toReal⁻¹ * ENNReal.ofReal ((etaZ b E)⁻¹ + 1) := by
  set μ := closedLaw b W np
  set cl : ℕ → ℕ := fun k => max j₀ (min k i) with hcldef
  have hcl1 : ∀ k, j₀ ≤ cl k := fun k => le_max_left _ _
  have hcl2 : ∀ k, cl k ≤ i := fun k => max_le hji (min_le_right _ _)
  have hcl : ∀ k, j₀ ≤ k → k ≤ i → cl k = k := fun k h1 h2 => by
    simp only [hcldef]; omega
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
      filter_upwards [hXr _ hj1 hj2, hXp _ hj1 hj2.le] with y hy hp' _ _ hd
      simp only [δ, ξ, e1, e2, e3] at hd ⊢
      rw [hy]
      exact jet_step_le hmean hp' hd _
    · exact Filter.Eventually.of_forall fun y h1 h2 => absurd ⟨h1, h2⟩ hk
  have hξp : ∀ k, 2 ≤ k → k ≤ n → eLpNorm (ξ k) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (Cp / W) := fun k _ _ =>
    eLpNorm_jetFluct_le (by linarith) (hXm _ (hcl1 _) (hcl2 _)) (hXi _ (hcl1 _) (hcl2 _))
      (hXp _ (hcl1 _) (hcl2 _)) hflp
  have hM : ∀ᵐ y ∂μ, δ n y ≤ (etaZ b E)⁻¹ + 1 := by
    filter_upwards [hXp _ (hcl1 (j₀ + n - 1)) (hcl2 _)] with y hy
    exact jetDistance0_le_bound hb0 hb hE1 hE2 hy
  have e0 : cl (j₀ + 1 - 1) = j₀ := by
    rw [show j₀ + 1 - 1 = j₀ by omega]; exact hcl _ le_rfl hji
  have eδ1f : δ 1 = fun y => jetDistance0 b E (X j₀ y) := by
    funext y; simp only [δ, e0]
  have h1 : eLpNorm (δ 1) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal s₁ := by
    rw [eδ1f]; exact hstart
  have key := eLpNorm_delta_le (δ := δ) (ξ := ξ) (d := d₀) (t := t) (n := n) μ hp hρ0 hρ1 hd₀
    hc hct hs₁ (by positivity) hδ0 hξ0 hδm hξm hstep h1 hξp (by omega : 1 ≤ n) le_rfl hM
  have hbad := measure_bad_le (δ := δ) (ξ := ξ) (d := d₀) (t := t) μ n
  have hmq : ∀ k ∈ Finset.Icc 2 n, μ {y | t < ξ k y} ≤
      ENNReal.ofReal (t⁻¹ ^ (p + 2) * (Cq / W) ^ (p + 2)) := fun k _ =>
    markov_ofReal μ (hξ0 k) (by linarith : (0 : ℝ) < p + 2) ht0 (by positivity)
      (eLpNorm_jetFluct_le (by linarith) (hXm _ (hcl1 _) (hcl2 _)) (hXi _ (hcl1 _) (hcl2 _))
        (hXp _ (hcl1 _) (hcl2 _)) hflq)
  have hsum : ∑ k ∈ Finset.Icc 2 n, μ {y | t < ξ k y} ≤
      ENNReal.ofReal ((i - j₀ : ℕ) * (t⁻¹ ^ (p + 2) * (Cq / W) ^ (p + 2))) := by
    refine (Finset.sum_le_card_nsmul _ _ _ hmq).trans ?_
    rw [nsmul_eq_mul, Nat.card_Icc, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    have hle : n + 1 - 2 ≤ i - j₀ := by omega
    exact mul_le_mul' (by exact_mod_cast hle) le_rfl
  have eδ1 : {y | d₀ / 2 < δ 1 y} = {y | d₀ / 2 < jetDistance0 b E (X j₀ y)} := by
    rw [eδ1f]
  have en : cl (j₀ + n - 1) = i := by
    rw [show j₀ + n - 1 = i by omega]; exact hcl _ hji le_rfl
  have eδn : δ n = fun y => jetDistance0 b E (X i y) := by
    funext y; simp only [δ, en]
  rw [eδn] at key
  refine key.trans (add_le_add le_rfl (mul_le_mul' (ENNReal.rpow_le_rpow
    (hbad.trans (add_le_add (le_of_eq (congrArg μ eδ1)) hsum)) (by positivity)) le_rfl))

/-!
## The start estimates
-/

/-- **`ClosedJetStartLp Xcl`: the closed start is at the `W⁻¹` scale**: at the closing
time `n_s`, `‖δ₀(Xcl_{n_s})‖_p ≤ C_p/W` for every `p ≥ 1`. -/
def ClosedJetStartLp (Xcl : ClosedInputFam) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ, ∀ᶠ W in atTop,
      eLpNorm (fun y => jetDistance0 b E (Xcl b E s h τ m W (closeLen s W) y))
        (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- **`ClosedJetShiftStartLp Xcl`: the closing shift of the jet at the closing time is
at the `W⁻¹` scale**: `‖Δ_{n_s}‖_p ≤ C_p/W` for every `p ≥ 1`, with
`Δ = |W⁻¹Tr(z - Xcl)⁻¹ - W⁻¹Tr(z - X_open)⁻¹|`. -/
def ClosedJetShiftStartLp (Xcl : ClosedInputFam) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ, ∀ᶠ W in atTop,
      eLpNorm (fun y => jetShift b E (Xcl b E s h τ m W (closeLen s W) y) (closeLen s W) y)
        (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- The open jet read on the closed law. -/
theorem eLpNorm_open_closedLaw (b E : ℝ) (W np r : ℕ) (p : ℝ≥0∞) :
    eLpNorm (fun y : ProbedPath W np × ℝ => jetDistance0 b E (pathX b E W r y.1.1)) p
        (closedLaw b W np) =
      eLpNorm (fun ω => jetDistance0 b E (pathX b E W r ω)) p (growthPathLaw W b) := by
  have hf : Measurable fun y : ProbedPath W np × ℝ => y.1.1 := measurable_fst.comp measurable_fst
  have hmap : (closedLaw b W np).map (fun y : ProbedPath W np × ℝ => y.1.1) =
      growthPathLaw W b := by
    ext A hA
    rw [Measure.map_apply hf hA]
    exact closedLaw_path_set b W np A
  have hg : Measurable fun ω => jetDistance0 b E (pathX b E W r ω) :=
    measurable_absorbedDelta b E (fun _ => 0) r
  rw [← hmap, eLpNorm_map_measure (by rw [hmap]; exact hg.aestronglyMeasurable) hf.aemeasurable]
  rfl

/-- **The closed start from the open jet and the closing shift at `n_s`** (Minkowski). -/
theorem closedJetStartLp_of_shift (hδ : DeltaZeroLengthUniform) {Xcl : ClosedInputFam}
    (hXm : ∀ (b E s h : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (W j : ℕ),
      Measurable (Xcl b E s h τ m W j))
    (hSh : ClosedJetShiftStartLp Xcl) : ClosedJetStartLp Xcl := by
  intro b E np τ m T s h K Vs hF p hp
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, hs, -, -, -, -⟩ := id hF
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval (min (2 + E) (2 - E)) :=
    ⟨by have := min_le_left (2 + E) (2 - E); linarith,
      by have := min_le_right (2 + E) (2 - E); linarith⟩
  obtain ⟨Cδ, hCδ, hδT⟩ := hδ b hb0 hb _ p hκ hp
  obtain ⟨W₀, hW₀⟩ := hδT s
  obtain ⟨C₁, hC₁⟩ := hSh b E np τ m T s h K Vs hF p hp
  refine ⟨Cδ + max C₁ 0, ?_⟩
  filter_upwards [hC₁, eventually_ge_atTop (max W₀ (max 1 ⌈s⁻¹⌉₊))] with W hW hWb
  simp only [max_le_iff] at hWb
  obtain ⟨hW0, hW1, hWs⟩ := hWb
  have hx1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hx0 : (0 : ℝ) < W := by linarith
  set r := closeLen s W with hr
  have hr1 : 1 ≤ r := by
    rw [hr, closeLen, Nat.one_le_floor_iff]
    have h1 := (Nat.le_ceil s⁻¹).trans (by exact_mod_cast hWs : (⌈s⁻¹⌉₊ : ℝ) ≤ W)
    rw [inv_le_iff_one_le_mul₀ hs] at h1
    linarith
  have hrT : (r : ℝ) ≤ s * W := by
    rw [hr, closeLen, mul_comm]; exact Nat.floor_le (by positivity)
  have hopen := hW₀ W hW0 E hEb r hr1 hrT
  rw [← eLpNorm_open_closedLaw b E W np r] at hopen
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hpt : ∀ y : ProbedPath W np × ℝ, ‖jetDistance0 b E (Xcl b E s h τ m W r y)‖ ≤
      ‖jetDistance0 b E (pathX b E W r y.1.1) + jetShift b E (Xcl b E s h τ m W r y) r y‖ := by
    intro y
    have htri := norm_sub_le_norm_sub_add_norm_sub
      ((W : ℂ)⁻¹ * (passiveResolvent b E (Xcl b E s h τ m W r y)).trace)
      ((W : ℂ)⁻¹ * (passiveResolvent b E (pathX b E W r y.1.1)).trace) (matchedA E)
    have h0 : 0 ≤ jetDistance0 b E (Xcl b E s h τ m W r y) := norm_nonneg _
    have h0' : 0 ≤ jetDistance0 b E (pathX b E W r y.1.1) := norm_nonneg _
    have h0'' : 0 ≤ jetShift b E (Xcl b E s h τ m W r y) r y := norm_nonneg _
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (by positivity)]
    unfold jetDistance0 jetShift
    linarith
  have hmX : AEStronglyMeasurable (fun y => jetDistance0 b E (Xcl b E s h τ m W r y))
      (closedLaw b W np) :=
    ((measurable_jetDistance0 b E).comp (hXm b E s h np τ m W r)).aestronglyMeasurable
  calc eLpNorm (fun y => jetDistance0 b E (Xcl b E s h τ m W r y)) (ENNReal.ofReal p)
        (closedLaw b W np)
      ≤ eLpNorm ((fun y : ProbedPath W np × ℝ => jetDistance0 b E (pathX b E W r y.1.1)) +
          fun y => jetShift b E (Xcl b E s h τ m W r y) r y) (ENNReal.ofReal p)
            (closedLaw b W np) :=
        eLpNorm_mono hmX hpt
    _ ≤ ENNReal.ofReal (Cδ / W) + ENNReal.ofReal (max C₁ 0 / W) :=
        (eLpNorm_add_le hp1).trans (add_le_add hopen (hW.trans (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (le_max_left _ _) hx0.le))))
    _ = ENNReal.ofReal ((Cδ + max C₁ 0) / W) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_div]

/-- The start estimate gives the entrance estimate at `s' = s` (Markov at `p = q`). -/
theorem closedJetEntrance_of_startLp {Xcl : ClosedInputFam} (hS : ClosedJetStartLp Xcl) {q : ℕ}
    (hq : 1 ≤ q) : ClosedJetEntrance q Xcl := by
  intro b E np τ m T s h K Vs hF
  obtain ⟨-, -, hsτ, -, -, -⟩ := id hF
  refine ⟨s, le_rfl, hsτ, fun d hd => ?_⟩
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨C, hC⟩ := hS b E np τ m T s h K Vs hF q hq'
  refine ⟨d⁻¹ ^ q * max C 0 ^ q, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with W hW hW1
  have hx0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hmk := markov_ofReal (closedLaw b W np) (fun y => norm_nonneg _)
    (by positivity : (0 : ℝ) < q) hd (by positivity : (0 : ℝ) ≤ max C 0 / W)
    (hW.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hx0.le)))
  rw [Real.rpow_natCast, Real.rpow_natCast] at hmk
  refine hmk.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [div_pow]; ring

/-!
## The closed jet in every `L^p`
-/

/-- **The closed jet in every `L^p` from the closing time on**: `‖δ₀(Xcl_j)‖_p ≤ C_p/W` at every
step `n_s ≤ j < ⌊WT⌋` (unstopped). -/
theorem closedJetLp_of (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {Xcl : ClosedInputFam} (hReg : ClosedInputRegular Xcl) (hRec : ClosedInputRecursion Xcl)
    (hStart : ClosedJetStartLp Xcl) :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ W in atTop,
        ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          eLpNorm (fun y => jetDistance0 b E (Xcl b E s h τ m W j y)) (ENNReal.ofReal p)
            (closedLaw b W np) ≤ ENNReal.ofReal (C / W) := by
  intro b E np τ m T s h K Vs hF p hp
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, -, -, -, -, -⟩ := id hF
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval (min (2 + E) (2 - E)) :=
    ⟨by have := min_le_left (2 + E) (2 - E); linarith,
      by have := min_le_right (2 + E) (2 - E); linarith⟩
  obtain ⟨d₀, ρ, Cm, Wm, hd₀, hρ0, hρ1, hCm, hmean⟩ :=
    passiveMeanStep_holds (passiveBounds_holds hGA hLp) b hb0 hb _ hκ
  obtain ⟨Cp, Wp, hCp, hflp⟩ := passiveFluctuationStep_holds hGA hLp b hb0 hb _ hκ p hp
  obtain ⟨Cq, Wq, hCq, hflq⟩ :=
    passiveFluctuationStep_holds hGA hLp b hb0 hb _ hκ (p + 2) (by linarith)
  obtain ⟨S1, hS1⟩ := hStart b E np τ m T s h K Vs hF p hp
  obtain ⟨S2, hS2⟩ := hStart b E np τ m T s h K Vs hF (p + 2) (by linarith)
  have h1ρ : 0 < 1 - ρ := by linarith
  set t := (1 - ρ) * d₀ / 2 with ht
  have ht0 : 0 < t := by positivity
  set M := (etaZ b E)⁻¹ + 1 with hM
  have hM0 : 0 ≤ M := by
    have := (etaLow_pos (by linarith : b < 1) hκ).le.trans
      (etaLow_le (by linarith : b < 1) hκ hEb)
    positivity
  set S1' := max S1 0
  set S2' := max S2 0
  have hS1'0 : 0 ≤ S1' := le_max_right _ _
  have hS2'0 : 0 ≤ S2' := le_max_right _ _
  set A := (d₀ / 2)⁻¹ ^ (p + 2) * S2' ^ (p + 2) with hA
  set B := t⁻¹ ^ (p + 2) * Cq ^ (p + 2) with hB
  have hA0 : 0 ≤ A := mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (le_max_right _ _) _)
  have hB0 : 0 ≤ B := mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hCq _)
  refine ⟨S1' + (Cm + Cp) / (1 - ρ) + 1 * M, by positivity, ?_⟩
  filter_upwards [hReg b E np τ m T s h K Vs hF, hRec b E np τ m T s h K Vs hF, hS1, hS2,
    eventually_ge_atTop (max (max Wm (max Wp Wq))
      (max 1 (max ⌈A + max T 0 * B⌉₊ ⌈Cm / ((1 - ρ) * d₀ / 2)⌉₊)))]
    with W hWreg hWrec hWS1 hWS2 hWbig j hj
  simp only [max_le_iff] at hWbig
  obtain ⟨⟨hWm, hWp, hWq⟩, hW1, hWA, hWC⟩ := hWbig
  have hx : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hx0 : (0 : ℝ) < W := by linarith
  obtain ⟨hjs, hjT⟩ := Finset.mem_Ico.1 hj
  set j₀ := closeLen s W with hj₀
  have hWd : Cm / (W : ℝ) ^ 2 ≤ (1 - ρ) * d₀ / 2 := by
    have hud : 0 < (1 - ρ) * d₀ / 2 := by positivity
    have h1 := (Nat.le_ceil (Cm / ((1 - ρ) * d₀ / 2))).trans
      (by exact_mod_cast hWC : (⌈Cm / ((1 - ρ) * d₀ / 2)⌉₊ : ℝ) ≤ W)
    rw [div_le_iff₀ hud] at h1
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hS1' : eLpNorm (fun y => jetDistance0 b E (Xcl b E s h τ m W j₀ y)) (ENNReal.ofReal p)
      (closedLaw b W np) ≤ ENNReal.ofReal (S1' / W) :=
    hWS1.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hx0.le))
  have hS2' : eLpNorm (fun y => jetDistance0 b E (Xcl b E s h τ m W j₀ y))
      (ENNReal.ofReal (p + 2)) (closedLaw b W np) ≤ ENNReal.ofReal (S2' / W) :=
    hWS2.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hx0.le))
  have key := eLpNorm_jet_le (np := np) hb0 hb hE1 hE2 hp hd₀ hρ0 hρ1 hCm hCp hCq
    (by positivity : 0 ≤ S1' / W) hWd (fun X hX hd => hmean W hWm E hEb X hX hd)
    (fun X hX => hflp W hWp E hEb X hX) (fun X hX => hflq W hWq E hEb X hX)
    (fun j => Xcl b E s h τ m W j) hjs
    (fun j' h1 h2 => (hWreg j' (Finset.mem_Ico.2 ⟨h1, lt_of_le_of_lt h2 hjT⟩)).1)
    (fun j' h1 h2 => (hWreg j' (Finset.mem_Ico.2 ⟨h1, lt_of_le_of_lt h2 hjT⟩)).2.1)
    (fun j' h1 h2 => (hWreg j' (Finset.mem_Ico.2 ⟨h1, lt_of_le_of_lt h2 hjT⟩)).2.2)
    (fun j' h1 h2 => hWrec j' h1 (by omega)) hS1'
  have hm1 := markov_ofReal (closedLaw b W np) (fun y => norm_nonneg _)
    (by linarith : (0 : ℝ) < p + 2) (by positivity : (0 : ℝ) < d₀ / 2)
    (by positivity : (0 : ℝ) ≤ S2' / W) hS2'
  have hWi : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  have hdiv : ∀ y : ℝ, 0 ≤ y → (y / W) ^ (p + 2) = y ^ (p + 2) * (W : ℝ)⁻¹ ^ (p + 2) :=
    fun y hy => by rw [div_eq_mul_inv, Real.mul_rpow hy hWi]
  have hnT : ((j - j₀ : ℕ) : ℝ) ≤ T * W := by
    have hT1 : 0 < ⌊(W : ℝ) * T⌋₊ := lt_of_le_of_lt (Nat.zero_le _) hjT
    have hWT : 0 ≤ (W : ℝ) * T := le_trans zero_le_one (Nat.floor_pos.1 hT1)
    have h1 : ((j - j₀ : ℕ) : ℝ) ≤ j := by exact_mod_cast Nat.sub_le j j₀
    have h2 : (j : ℝ) ≤ ⌊(W : ℝ) * T⌋₊ := by exact_mod_cast hjT.le
    have h3 := Nat.floor_le hWT
    linarith
  have hWA' : A + max T 0 * B ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWA)
  have hbadR : (d₀ / 2)⁻¹ ^ (p + 2) * (S2' / W) ^ (p + 2) +
      ((j - j₀ : ℕ) : ℝ) * (t⁻¹ ^ (p + 2) * (Cq / W) ^ (p + 2)) ≤ (W : ℝ)⁻¹ ^ p := by
    have := bad_arith_uniform (A := A) (B := B) (T := T) (p := p) (r := j - j₀) hA0 hB0 hx hnT
      hWA'
    rw [hdiv S2' (le_max_right _ _), hdiv Cq hCq]
    calc (d₀ / 2)⁻¹ ^ (p + 2) * (S2' ^ (p + 2) * (W : ℝ)⁻¹ ^ (p + 2)) +
          ((j - j₀ : ℕ) : ℝ) * (t⁻¹ ^ (p + 2) * (Cq ^ (p + 2) * (W : ℝ)⁻¹ ^ (p + 2)))
        = A * (W : ℝ)⁻¹ ^ (p + 2) + ((j - j₀ : ℕ) : ℝ) * (B * (W : ℝ)⁻¹ ^ (p + 2)) := by
          simp only [hA, hB]; ring
      _ ≤ _ := this
  have hp0 : (0 : ℝ) < p := by linarith
  have hpow : (closedLaw b W np {y | d₀ / 2 < jetDistance0 b E (Xcl b E s h τ m W j₀ y)} +
      ENNReal.ofReal (((j - j₀ : ℕ) : ℝ) *
        (((1 - ρ) * d₀ / 2)⁻¹ ^ (p + 2) * (Cq / W) ^ (p + 2)))) ^
        (ENNReal.ofReal p).toReal⁻¹ ≤ ENNReal.ofReal (1 * (W : ℝ)⁻¹) := by
    rw [ENNReal.toReal_ofReal hp0.le, one_mul]
    have hsum : closedLaw b W np {y | d₀ / 2 < jetDistance0 b E (Xcl b E s h τ m W j₀ y)} +
        ENNReal.ofReal (((j - j₀ : ℕ) : ℝ) *
          (((1 - ρ) * d₀ / 2)⁻¹ ^ (p + 2) * (Cq / W) ^ (p + 2))) ≤
        ENNReal.ofReal ((W : ℝ)⁻¹ ^ p) := by
      refine (add_le_add hm1 le_rfl).trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal hbadR
    refine (ENNReal.rpow_le_rpow hsum (inv_nonneg.2 hp0.le)).trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (inv_nonneg.2 hp0.le),
      Real.rpow_rpow_inv hWi hp0.ne']
  refine key.trans ?_
  calc ENNReal.ofReal (S1' / W + (Cm / (W : ℝ) ^ 2 + Cp / W) / (1 - ρ)) +
        (closedLaw b W np {y | d₀ / 2 < jetDistance0 b E (Xcl b E s h τ m W j₀ y)} +
          ENNReal.ofReal (((j - j₀ : ℕ) : ℝ) *
            (((1 - ρ) * d₀ / 2)⁻¹ ^ (p + 2) * (Cq / W) ^ (p + 2)))) ^
          (ENNReal.ofReal p).toReal⁻¹ * ENNReal.ofReal M
      ≤ ENNReal.ofReal (S1' / W + (Cm / (W : ℝ) ^ 2 + Cp / W) / (1 - ρ)) +
          ENNReal.ofReal (1 * (W : ℝ)⁻¹) * ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal (S1' / W + (Cm / (W : ℝ) ^ 2 + Cp / W) / (1 - ρ) +
          1 * (W : ℝ)⁻¹ * M) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
    _ ≤ ENNReal.ofReal ((S1' + (Cm + Cp) / (1 - ρ) + 1 * M) / W) :=
        ENNReal.ofReal_le_ofReal (absorbed_final_arith hx hCm hρ1)

/-!
## The targets at `b3ClosedX`
-/

/-- **`ClosedJet0Lp`** from the closed-input properties of `b3ClosedX` and
the start estimate. -/
theorem closedJet0Lp_of_start (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : ClosedInputPassive b3ClosedX) (hRec : ClosedInputRecursion b3ClosedX)
    (hStart : ClosedJetStartLp b3ClosedX) : ClosedJet0Lp := by
  intro b E np τ m T s h K Vs hF R p hp
  obtain ⟨C, hC0, hC⟩ := closedJetLp_of hGA hLp (closedInputRegular_b3ClosedX hP) hRec hStart
    b E np τ m T s h K Vs hF p hp
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hC, hF.2.2.2.2.2] with W hW hVW j hj
  have hjI : j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊ := (Finset.mem_filter.1 hj).1
  have hV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  obtain ⟨⟨-, hb1, hE1, hE2, -⟩, -⟩ := id hF
  exact (eLpNorm_indicator_le _ (nullMeasurableSet_b3Alive (by linarith) hE1 hE2 s h τ m R W j
    hV)).trans (hW j hjI)

/-- **`ClosedJetL4Fam`** for a closed input family from its properties and the start estimate. -/
theorem closedJetL4Fam_of_start (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {Xcl : ClosedInputFam} (hReg : ClosedInputRegular Xcl) (hRec : ClosedInputRecursion Xcl)
    (hStart : ClosedJetStartLp Xcl) : ClosedJetL4Fam Xcl := by
  intro b E np τ m T s h K Vs hF
  obtain ⟨C, hC0, hC⟩ := closedJetLp_of hGA hLp hReg hRec hStart b E np τ m T s h K Vs hF 4
    (by norm_num)
  refine ⟨C ^ 4, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1, hReg b E np τ m T s h K Vs hF]
    with W hW hW1 hWreg j hj _
  have hx0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hm : Measurable fun y => jetDistance0 b E (Xcl b E s h τ m W j y) :=
    (measurable_jetDistance0 b E).comp (hWreg j hj).1
  refine (lintegral_ofReal_pow_four_le _ (fun y => norm_nonneg _) hm (by positivity)
    (hW j hj)).trans (le_of_eq ?_)
  rw [div_pow]

/-- **Main theorem (`ClosedJet0Lp`) at the input hypothesis level**: from `MatchedTracesContract`,
`GaussianAbsorptionContract`, `GaussianLpGradient` and the three closed-input hypotheses on
`b3ClosedX`: passivity and the one-port recursion (exact algebra) and the closing shift at the
closing time.
-/
theorem closedJet0Lp_b3ClosedX (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : ClosedInputPassive b3ClosedX)
    (hRec : ClosedInputRecursion b3ClosedX) (hSh : ClosedJetShiftStartLp b3ClosedX) :
    ClosedJet0Lp :=
  closedJet0Lp_of_start hGA hLp hP hRec
    (closedJetStartLp_of_shift (deltaZeroLengthUniform_holds hMT hGA hLp)
      (fun b E s h _ τ m _ j => measurable_b3ClosedX b E s h τ m j) hSh)

/-- **Main theorem (`ClosedJetL4Fam b3ClosedX`) at the input hypothesis level**, from the same
hypotheses as `closedJet0Lp_b3ClosedX`.
-/
theorem closedJetL4Fam_b3ClosedX_of_start (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : ClosedInputPassive b3ClosedX) (hRec : ClosedInputRecursion b3ClosedX)
    (hSh : ClosedJetShiftStartLp b3ClosedX) : ClosedJetL4Fam b3ClosedX :=
  closedJetL4Fam_of_start hGA hLp (closedInputRegular_b3ClosedX hP) hRec
    (closedJetStartLp_of_shift (deltaZeroLengthUniform_holds hMT hGA hLp)
      (fun b E s h _ τ m _ j => measurable_b3ClosedX b E s h τ m j) hSh)

end BlockBand.SourceProcess.PhysApprox.B3.Jet
