module

public import BlockBand.SourceProcess.PhysApprox.B3JetMain

/-!
# The closed entrance from the closing shift of the jet

The entrance hypothesis `ClosedJetEntrance q Xcl` splits into the open jet, which is
`DeltaZeroLengthUniform` (proved from `MatchedTracesContract`, `GaussianAbsorptionContract`,
`GaussianLpGradient`), and the **closing shift** of the scalar jet,
`Δ = |W⁻¹Tr(z - Xcl)⁻¹ - W⁻¹Tr(z - X_open)⁻¹|` at one time `⌊Ws'⌋`:

* **`ClosedJetShiftTail q Xcl`**, stated as a hypothesis: for every `d > 0`, `μ(Δ > d) ≤ C/W^q`;
* **`closedJetEntrance_of_shift`**: `DeltaZeroLengthUniform + ClosedJetShiftTail q Xcl ⇒
  ClosedJetEntrance q Xcl` (`q ≥ 1`; triangle inequality, Markov at `p = q` for the open jet);
* **`closedJetL4Fam_b3ClosedX_of_shift`**: `ClosedJetL4Fam b3ClosedX` from the contract
  hypotheses `MatchedTracesContract`, `GaussianAbsorptionContract`, `GaussianLpGradient` and
  three closed-input hypotheses (passivity, recursion, shift tail).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.LengthUniform
open scoped ENNReal ComplexOrder

/-- The closing shift of the scalar jet at length `r`: `|W⁻¹Tr(z - Xcl)⁻¹ - W⁻¹Tr(z - X_r)⁻¹|`,
`X_r = pathX` the open one-port input. -/
def jetShift (b E : ℝ) {W np : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) (r : ℕ)
    (y : ProbedPath W np × ℝ) : ℝ :=
  ‖(W : ℂ)⁻¹ * (passiveResolvent b E X).trace -
    (W : ℂ)⁻¹ * (passiveResolvent b E (pathX b E W r y.1.1)).trace‖

/-- **`ClosedJetShiftTail q Xcl`: the closing shift of the jet is small in probability**: there is a time `s ≤ s' < min τ` such that for every `d > 0`,
eventually `μ(jetShift(Xcl_{⌊Ws'⌋}) > d) ≤ C/W^q`. -/
def ClosedJetShiftTail (q : ℕ) (Xcl : ClosedInputFam) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∃ s' : ℝ, s ≤ s' ∧ (∀ k, s' < τ k) ∧
      ∀ d : ℝ, 0 < d → ∃ C : ℝ, ∀ᶠ W in atTop,
        closedLaw b W np {y | d < jetShift b E (Xcl b E s h τ m W ⌊(W : ℝ) * s'⌋₊ y)
          ⌊(W : ℝ) * s'⌋₊ y} ≤ ENNReal.ofReal (C / (W : ℝ) ^ q)

/-- The path marginal of the closed law. -/
theorem closedLaw_path_set (b : ℝ) (W np : ℕ) (A : Set (GrowthPath W)) :
    closedLaw b W np {y | y.1.1 ∈ A} = growthPathLaw W b A := by
  have : {y : ProbedPath W np × ℝ | y.1.1 ∈ A} = (A ×ˢ Set.univ) ×ˢ Set.univ := by
    ext y; simp
  rw [this, closedLaw, Measure.prod_prod, probedPathLaw, Measure.prod_prod, measure_univ,
    measure_univ, mul_one, mul_one]

/-- **The entrance from the open jet and the closing shift.** -/
theorem closedJetEntrance_of_shift (hδ : DeltaZeroLengthUniform) {q : ℕ} (hq : 1 ≤ q)
    {Xcl : ClosedInputFam} (hS : ClosedJetShiftTail q Xcl) : ClosedJetEntrance q Xcl := by
  intro b E np τ m T s h K Vs hF
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, hs, -, -, -, -⟩ := id hF
  obtain ⟨s', hss', hs'τ, hsh⟩ := hS b E np τ m T s h K Vs hF
  refine ⟨s', hss', hs'τ, fun d hd => ?_⟩
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval (min (2 + E) (2 - E)) :=
    ⟨by have := min_le_left (2 + E) (2 - E); linarith,
      by have := min_le_right (2 + E) (2 - E); linarith⟩
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨Cδ, hCδ, hδT⟩ := hδ b hb0 hb _ q hκ hq'
  obtain ⟨W₀, hW₀⟩ := hδT (s' + 1)
  obtain ⟨C₁, hC₁⟩ := hsh (d / 2) (by positivity)
  have hs'0 : 0 < s' := lt_of_lt_of_le hs hss'
  refine ⟨(d / 2)⁻¹ ^ q * Cδ ^ q + max C₁ 0, ?_⟩
  filter_upwards [hC₁, eventually_ge_atTop (max W₀ (max 1 ⌈s'⁻¹⌉₊))] with W hW hWb
  simp only [max_le_iff] at hWb
  obtain ⟨hW0, hW1, hWs⟩ := hWb
  have hx : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hx0 : (0 : ℝ) < W := by linarith
  set r := ⌊(W : ℝ) * s'⌋₊ with hr
  have hr1 : 1 ≤ r := by
    rw [hr, Nat.one_le_floor_iff]
    have h1 := (Nat.le_ceil s'⁻¹).trans (by exact_mod_cast hWs : (⌈s'⁻¹⌉₊ : ℝ) ≤ W)
    rw [inv_le_iff_one_le_mul₀ hs'0] at h1
    linarith
  have hrT : (r : ℝ) ≤ (s' + 1) * W := by
    have := Nat.floor_le (by positivity : (0 : ℝ) ≤ (W : ℝ) * s')
    nlinarith
  have hopen := hW₀ W hW0 E hEb r hr1 hrT
  have hmk := markov_ofReal (growthPathLaw W b) (fun ω => norm_nonneg _)
    (by positivity : (0 : ℝ) < q) (by positivity : (0 : ℝ) < d / 2)
    (by positivity : (0 : ℝ) ≤ Cδ / W) hopen
  rw [Real.rpow_natCast, Real.rpow_natCast] at hmk
  have hsub : {y : ProbedPath W np × ℝ | d < jetDistance0 b E (Xcl b E s h τ m W r y)} ⊆
      {y | y.1.1 ∈ {ω | d / 2 < jetDistance0 b E (pathX b E W r ω)}} ∪
        {y | d / 2 < jetShift b E (Xcl b E s h τ m W r y) r y} := by
    intro y hy
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    by_contra hc
    rw [not_or, not_lt, not_lt] at hc
    obtain ⟨h1, h2⟩ := hc
    have htri := norm_sub_le_norm_sub_add_norm_sub
      ((W : ℂ)⁻¹ * (passiveResolvent b E (Xcl b E s h τ m W r y)).trace)
      ((W : ℂ)⁻¹ * (passiveResolvent b E (pathX b E W r y.1.1)).trace) (matchedA E)
    have hy' : d < jetDistance0 b E (Xcl b E s h τ m W r y) := hy
    unfold jetDistance0 at hy' h1
    unfold jetShift at h2
    linarith
  calc closedLaw b W np {y | d < jetDistance0 b E (Xcl b E s h τ m W r y)}
      ≤ closedLaw b W np {y | y.1.1 ∈ {ω | d / 2 < jetDistance0 b E (pathX b E W r ω)}} +
          closedLaw b W np {y | d / 2 < jetShift b E (Xcl b E s h τ m W r y) r y} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal ((d / 2)⁻¹ ^ q * (Cδ / W) ^ q) +
          ENNReal.ofReal (max C₁ 0 / (W : ℝ) ^ q) := by
        rw [closedLaw_path_set]
        exact add_le_add hmk (hW.trans (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))))
    _ = ENNReal.ofReal (((d / 2)⁻¹ ^ q * Cδ ^ q + max C₁ 0) / (W : ℝ) ^ q) := by
        have hC₁0 : 0 ≤ max C₁ 0 / (W : ℝ) ^ q := by
          have := le_max_right C₁ 0; positivity
        rw [← ENNReal.ofReal_add (by positivity) hC₁0, div_pow, add_div]
        congr 1
        ring

/-- **`ClosedJetL4Fam b3ClosedX` from the contract hypotheses and three closed-input
hypotheses**: passivity (`ClosedInputPassive`), the one-port recursion (`ClosedInputRecursion`)
and the closing-shift tail (`ClosedJetShiftTail 4`). -/
theorem closedJetL4Fam_b3ClosedX_of_shift (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : ClosedInputPassive b3ClosedX) (hRec : ClosedInputRecursion b3ClosedX)
    (hSh : ClosedJetShiftTail 4 b3ClosedX) : ClosedJetL4Fam b3ClosedX :=
  closedJetL4Fam_b3ClosedX hGA hLp hP hRec
    (closedJetEntrance_of_shift (deltaZeroLengthUniform_holds hMT hGA hLp) (by norm_num) hSh)

/-- **`ClosedJetHalf b3ClosedX`** from the same hypotheses, with the weaker shift tail
`q = 2`. -/
theorem closedJetHalf_b3ClosedX_of_shift (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : ClosedInputPassive b3ClosedX) (hRec : ClosedInputRecursion b3ClosedX)
    (hSh : ClosedJetShiftTail 2 b3ClosedX) : ClosedJetHalf b3ClosedX :=
  closedJetHalf_b3ClosedX hGA hLp hP hRec
    (closedJetEntrance_of_shift (deltaZeroLengthUniform_holds hMT hGA hLp) (by norm_num) hSh)

end BlockBand.SourceProcess.PhysApprox.B3.Jet
