module

public import BlockBand.SourceProcess.ClosedSumProof.ClosedWindow

/-!
# `ClosedSummed`: its three clauses, and the integrability supplied by `ClosedFourth`

* `ClosedDriftSummed`, `ClosedBracketSummed`, `ClosedBirthSummed`: the three sums of
  `closedSummedErr` as separate hypotheses (one-layer drift; one-layer bracket; Gaussian
  birth concentration). **`closedSummed_of`**: together they give `ClosedSummed`.
* **`integrable_steps_of_fourth`**: `ClosedFourth` makes, eventually in `W`,
  every stopped step `1_{A_j}ΔG_e` and every product `1_{A_j}ΔG_eΔG_{e'}` integrable, so the
  conditional expectations in `ClosedSummed` are not Mathlib's junk value `0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSumProof

open MeasureTheory Matrix Finset Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedIdent
open BlockBand.SourceProcess.ClosedSum
open scoped ENNReal

/-- The hypotheses common to the three clauses of `ClosedSummed`, with the summed error as a function of
the data. -/
def SummedPin (err : ∀ {p K M : ℕ}, ℝ → ℝ → ℝ → ℝ → ℝ → (Fin p → ℝ → ℝ) → ℝ → ∀ W : ℕ,
    (GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) →
    (Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M)) →
    (Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M)) → ℝ≥0∞) : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s T : ℝ, 0 < s → s < T →
    ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) → ∀ h : ℝ, 0 < h → h < 1 →
    ∀ K M : ℕ, 0 < M → ∀ R : ℝ,
    ∀ Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ,
      (∀ᶠ W in atTop, IsTimeSFrame b E s h K W (Vs W)) →
    ∀ e e' : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M),
      Tendsto (fun W => err b E s T h q R W (Vs W) e e') atTop (𝓝 0)

/-- The drift sum (first sum of `closedSummedErr`). -/
def driftSum {p K M : ℕ} (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (e _e' : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M)) : ℝ≥0∞ :=
  ∑ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, ∫⁻ y,
    ‖(closedAlive b E s T h q R W j Vs ∩ noBirth j).indicator (fun y =>
      (lawW b T q M W)[(closedAlive b E s T h q R W j Vs ∩ noBirth j).indicator (fun y =>
        zc b E s T h q W Vs e (j + 1) y - zc b E s T h q W Vs e j y) |
          closedSigma W j p M] y - (W : ℂ)⁻¹ * gramDriftEntry (transportD0 b E)
            (srcSignature K (Fin p × Fin M)) e (closedGramAt b E s T h q W j Vs y)) y‖ₑ
      ∂lawW b T q M W

/-- The bracket sum (second sum of `closedSummedErr`). -/
def bracketSum {p K M : ℕ} (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (e e' : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M)) : ℝ≥0∞ :=
  ∑ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, ∫⁻ y,
    ‖(closedAlive b E s T h q R W j Vs ∩ noBirth j).indicator (fun y =>
      (lawW b T q M W)[(closedAlive b E s T h q R W j Vs ∩ noBirth j).indicator (fun y =>
        (zc b E s T h q W Vs e (j + 1) y - zc b E s T h q W Vs e j y) *
          (zc b E s T h q W Vs e' (j + 1) y - zc b E s T h q W Vs e' j y)) |
          closedSigma W j p M] y - (W : ℂ)⁻¹ * gramCovEntry (transportD0 b E)
            (srcSignature K (Fin p × Fin M)) e e' (closedGramAt b E s T h q W j Vs y)) y‖ₑ
      ∂lawW b T q M W

/-- The birth sum (third sum of `closedSummedErr`). -/
def birthSum {p K M : ℕ} (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (e _e' : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M)) : ℝ≥0∞ :=
  ∑ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, ∫⁻ y,
    ‖(closedAlive b E s T h q R W j Vs \ noBirth j).indicator (fun y =>
      gramEntry e (closedGramAt b E s T h q W (j + 1) Vs y - closedGramAt b E s T h q W j Vs y -
        birthAt b s T q j y)) y‖ₑ ∂lawW b T q M W

/-- **Hypothesis**: the one-layer drift of the closed Gram coordinates, summed. -/
def ClosedDriftSummed : Prop := SummedPin driftSum

/-- **Hypothesis**: the one-layer bracket of the closed Gram coordinates, summed. -/
def ClosedBracketSummed : Prop := SummedPin bracketSum

/-- **Hypothesis**: the birth jumps of the sampled probes, summed. -/
def ClosedBirthSummed : Prop := SummedPin birthSum

/-- **`ClosedSummed` from its three clauses.** -/
theorem closedSummed_of (hD : ClosedDriftSummed) (hB : ClosedBracketSummed)
    (hJ : ClosedBirthSummed) : ClosedSummed := by
  intro b hb0 hb E hE1 hE2 s T hs hsT p q hq h hh0 hh1 K M hM R Vs hVs e e'
  have h1 := hD b hb0 hb E hE1 hE2 s T hs hsT p q hq h hh0 hh1 K M hM R Vs hVs e e'
  have h2 := hB b hb0 hb E hE1 hE2 s T hs hsT p q hq h hh0 hh1 K M hM R Vs hVs e e'
  have h3 := hJ b hb0 hb E hE1 hE2 s T hs hsT p q hq h hh0 hh1 K M hM R Vs hVs e e'
  have := (h1.add h2).add h3
  simp only [add_zero] at this
  refine this.congr fun W => ?_
  rw [closedSummedErr_eq]; rfl

/-- **Integrability from `ClosedFourth`**. -/
theorem integrable_steps_of_fourth (hF : ClosedFourth) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {s T : ℝ} (hs : 0 < s) (hsT : s < T) {p : ℕ}
    {q : Fin p → ℝ → ℝ} (hq : ∀ i, IsSourceTest s T (q i)) {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    {K M : ℕ} (hM : 0 < M) (R : ℝ)
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : ∀ᶠ W in atTop, IsTimeSFrame b E s h K W (Vs W))
    (e e' : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M)) :
    ∀ᶠ W in atTop, ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
      Integrable ((closedAlive b E s T h q R W j (Vs W) ∩ noBirth j).indicator fun y =>
        zc b E s T h q W (Vs W) e (j + 1) y - zc b E s T h q W (Vs W) e j y) (lawW b T q M W) ∧
      Integrable ((closedAlive b E s T h q R W j (Vs W) ∩ noBirth j).indicator fun y =>
        (zc b E s T h q W (Vs W) e (j + 1) y - zc b E s T h q W (Vs W) e j y) *
          (zc b E s T h q W (Vs W) e' (j + 1) y - zc b E s T h q W (Vs W) e' j y))
        (lawW b T q M W) := by
  have hq' : ∀ i x, 0 ≤ q i x := fun i x => (hq i).1 x
  have hb1 : b < 1 := by linarith
  have h1 := (ENNReal.tendsto_nhds_zero.mp (hF b hb0 hb E hE1 hE2 s T hs hsT p q hq h hh0 hh1 K M
    hM R Vs hVs e)) 1 one_pos
  have h2 := (ENNReal.tendsto_nhds_zero.mp (hF b hb0 hb E hE1 hE2 s T hs hsT p q hq h hh0 hh1 K M
    hM R Vs hVs e')) 1 one_pos
  filter_upwards [hVs, h1, h2] with W hV hW1 hW2 j hj
  have hP : IsProbabilityMeasure (lawW b T q M W) := by
    have := isProbabilityMeasure_sampledPathLaw (b := b) (W := W) (M := M) hq' ⌊(W : ℝ) * T⌋₊
    unfold lawW; infer_instance
  have hjs := (Finset.mem_Ico.mp hj).1
  have hA := am_ae_eq (b := b) (E := E) (s := s) (T := T) (h := h) (R := R) (Vs := Vs W)
    hb1 hE1 hE2 hq' (M := M) j
  have key : ∀ f : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M),
      closedFourthErr b E s T h q R W (Vs W) f ≤ 1 →
      AEStronglyMeasurable ((closedAlive b E s T h q R W j (Vs W) ∩ noBirth j).indicator fun y =>
        zc b E s T h q W (Vs W) f (j + 1) y - zc b E s T h q W (Vs W) f j y) (lawW b T q M W) ∧
      Integrable (fun y => ‖(closedAlive b E s T h q R W j (Vs W) ∩ noBirth j).indicator (fun y =>
        zc b E s T h q W (Vs W) f (j + 1) y - zc b E s T h q W (Vs W) f j y) y‖ ^ 4)
        (lawW b T q M W) := fun f hf => by
    have hm : AEStronglyMeasurable ((closedAlive b E s T h q R W j (Vs W) ∩ noBirth j).indicator
        fun y => zc b E s T h q W (Vs W) f (j + 1) y - zc b E s T h q W (Vs W) f j y)
        (lawW b T q M W) :=
      (aestronglyMeasurable_step f hV.1 hjs _).congr (indicator_ae_eq_of_ae_eq_set hA).symm
    refine ⟨hm, ⟨hm.norm.pow 4, ?_⟩⟩
    have hle : ∫⁻ y, ‖(closedAlive b E s T h q R W j (Vs W) ∩ noBirth j).indicator (fun y =>
        zc b E s T h q W (Vs W) f (j + 1) y - zc b E s T h q W (Vs W) f j y) y‖ₑ ^ 4
          ∂lawW b T q M W ≤ 1 :=
      (Finset.single_le_sum (f := fun j => ∫⁻ y, ‖(closedAlive b E s T h q R W j (Vs W) ∩
        noBirth j).indicator (fun y => gramEntry f (closedGramAt b E s T h q W (j + 1) (Vs W) y) -
          gramEntry f (closedGramAt b E s T h q W j (Vs W) y)) y‖ₑ ^ 4 ∂lawW b T q M W)
        (fun _ _ => zero_le) hj).trans hf
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (le_of_eq ?_) (hle.trans_lt ENNReal.one_lt_top)
    refine lintegral_congr fun y => ?_
    rw [enorm_pow, enorm_norm]
  obtain ⟨m1, i1⟩ := key e hW1
  obtain ⟨m2, i2⟩ := key e' hW2
  refine ⟨integrable_of_pow4 m1 i1, ?_⟩
  have s1 := integrable_sq_of_pow4 m1 i1
  have s2 := integrable_sq_of_pow4 m2 i2
  have e1 : ((closedAlive b E s T h q R W j (Vs W) ∩ noBirth j).indicator fun y =>
      (zc b E s T h q W (Vs W) e (j + 1) y - zc b E s T h q W (Vs W) e j y) *
        (zc b E s T h q W (Vs W) e' (j + 1) y - zc b E s T h q W (Vs W) e' j y)) = fun y =>
      (closedAlive b E s T h q R W j (Vs W) ∩ noBirth j).indicator (fun y =>
        zc b E s T h q W (Vs W) e (j + 1) y - zc b E s T h q W (Vs W) e j y) y *
      (closedAlive b E s T h q R W j (Vs W) ∩ noBirth j).indicator (fun y =>
        zc b E s T h q W (Vs W) e' (j + 1) y - zc b E s T h q W (Vs W) e' j y) y := by
    funext y; by_cases hy : y ∈ closedAlive b E s T h q R W j (Vs W) ∩ noBirth j <;> simp [hy]
  rw [e1]
  refine Integrable.mono' ((s1.add s2).div_const 2) (m1.mul m2)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_mul]
  have := two_mul_le_add_sq ‖(closedAlive b E s T h q R W j (Vs W) ∩ noBirth j).indicator (fun y =>
    zc b E s T h q W (Vs W) e (j + 1) y - zc b E s T h q W (Vs W) e j y) y‖
    ‖(closedAlive b E s T h q R W j (Vs W) ∩ noBirth j).indicator (fun y =>
    zc b E s T h q W (Vs W) e' (j + 1) y - zc b E s T h q W (Vs W) e' j y) y‖
  simp only [Pi.add_apply]
  linarith

end BlockBand.SourceProcess.ClosedSumProof
