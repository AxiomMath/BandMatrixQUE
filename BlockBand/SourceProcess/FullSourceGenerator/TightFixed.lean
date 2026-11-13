module

public import BlockBand.SourceProcess.FullSourceGenerator.TightStep
public import BlockBand.SourceProcess.FullSourceGenerator.TightBlocks

/-!
# The modulus of a real trace polynomial at fixed `W`

`modulus_fixed`: at fixed `W`, the probability that a real trace polynomial oscillates by more
than a given amount over a short time interval is bounded through the summed drift and carré du
champ errors, the fourth moments, and the probability of exceeding the stop level.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MeasureTheory MvPolynomial Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal

/-- Summed errors over a window inside the summation range of `EarlySummed`. -/
theorem sum_integral_norm_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (u : ℕ → Ω → ℂ)
    (hu : ∀ j, AEStronglyMeasurable (u j) μ) (s : Finset ℕ) (j₁ n : ℕ)
    (hs : ∀ i < n, j₁ + i ∈ s) {B : ℝ} (hB : ∑ j ∈ s, ∫⁻ ω, ‖u j ω‖ₑ ∂μ ≤ ENNReal.ofReal B) :
    (∀ i < n, Integrable (fun ω => ‖u (j₁ + i) ω‖) μ) ∧
      ∑ i ∈ range n, ∫ ω, ‖u (j₁ + i) ω‖ ∂μ ≤ max B 0 := by
  have hsub : (range n).map (addLeftEmbedding j₁) ⊆ s := fun j hj => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    exact hs i (Finset.mem_range.mp hi)
  have hle : ∑ i ∈ range n, ∫⁻ ω, ‖u (j₁ + i) ω‖ₑ ∂μ ≤ ENNReal.ofReal B := by
    refine le_trans ?_ hB
    have e := Finset.sum_map (range n) (addLeftEmbedding j₁) (fun j => ∫⁻ ω, ‖u j ω‖ₑ ∂μ)
    simp only [addLeftEmbedding_apply] at e
    rw [← e]
    exact Finset.sum_le_sum_of_subset hsub
  have hfin : ∀ i < n, ∫⁻ ω, ‖u (j₁ + i) ω‖ₑ ∂μ ≠ ⊤ := fun i hi =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((Finset.single_le_sum (f := fun i =>
      ∫⁻ ω, ‖u (j₁ + i) ω‖ₑ ∂μ) (fun _ _ => zero_le) (Finset.mem_range.mpr hi)).trans hle)
  have hint : ∀ i < n, Integrable (u (j₁ + i)) μ := fun i hi => ⟨hu _, (hfin i hi).lt_top⟩
  refine ⟨fun i hi => (hint i hi).norm, ?_⟩
  rw [Finset.sum_congr rfl fun i _ => integral_norm_eq_lintegral_enorm (hu (j₁ + i)),
    ← ENNReal.toReal_sum fun i hi => hfin i (Finset.mem_range.mp hi), ← ENNReal.toReal_ofReal']
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hle

variable {W nT nI : ℕ}

theorem aestronglyMeasurable_driftErr (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε : ℝ)
    (Φ : TracePoly nT nI) (j : ℕ) :
    AEStronglyMeasurable (driftErr b E k q K ε W Φ j) (growthPathLaw W b) :=
  ((stronglyMeasurable_condExp.mono (growthSigma_le' W j)).aestronglyMeasurable.sub
    ((measurable_polyValue b E k q j _).const_mul _).aestronglyMeasurable).indicator
      (growthSigma_le' W j _ (ContractingWords.measurableSet_alive b E k q K ε j))

theorem aestronglyMeasurable_carreErr (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε : ℝ)
    (Φ : TracePoly nT nI) (j : ℕ) :
    AEStronglyMeasurable (carreErr b E k q K ε W Φ j) (growthPathLaw W b) :=
  ((stronglyMeasurable_condExp.mono (growthSigma_le' W j)).aestronglyMeasurable.sub
    ((measurable_polyValue b E k q j _).const_mul _).aestronglyMeasurable).indicator
      (growthSigma_le' W j _ (ContractingWords.measurableSet_alive b E k q K ε j))

/-- Without exceedance of the stop level up to `(T+1)W`, every length up to `(T+1)W` is alive. -/
theorem mem_alive_of_notMem_stop {b E : ℝ} {k : Fin nT → ℕ} {q : Fin nI → ℝ → ℝ} {K ε T' : ℝ}
    {ω : GrowthPath W} (hω : ω ∉ {ω | ∃ j : ℕ, ε * W ≤ j ∧ (j : ℝ) ≤ T' * W ∧
      K < traceLoad b E k q W j ω}) {j : ℕ} (hj : (j : ℝ) ≤ T' * W) :
    ω ∈ alive b E k q K ε W j := by
  rw [ContractingWords.alive_eq]
  simp only [Set.mem_iInter, Finset.mem_range, Set.mem_ofPred_eq]
  intro i hi ⟨hεi, hK⟩
  exact hω ⟨i, hεi, (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hi)).trans hj, hK⟩

theorem sum_Ico_telescope (f : ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y) :
    ∑ i ∈ Finset.Ico x y, (f (i + 1) - f i) = f y - f x := by
  rw [Finset.sum_Ico_eq_sub _ hxy, Finset.sum_range_sub, Finset.sum_range_sub]; ring

/-- `⌊a + b⌋ ≤ ⌊a⌋ + ⌊b⌋ + 1`. -/
theorem floor_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : ⌊a + b⌋₊ ≤ ⌊a⌋₊ + ⌊b⌋₊ + 1 := by
  have h1 := Nat.floor_le (add_nonneg ha hb)
  have h2 := Nat.lt_floor_add_one a
  have h3 := Nat.lt_floor_add_one b
  have : (⌊a + b⌋₊ : ℝ) < ⌊a⌋₊ + ⌊b⌋₊ + 2 := by linarith
  have : ⌊a + b⌋₊ < ⌊a⌋₊ + ⌊b⌋₊ + 2 := by exact_mod_cast this
  omega

/-- **The modulus of a real trace polynomial at fixed `W`.** -/
theorem modulus_fixed {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 2 ≤ W)
    (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (hq : IsIntervalTests q) {t₀ : ℝ}
    (hq0 : ∀ a t, t₀ < t → q a t = 0) (Φ : TracePoly nT nI) (hΦ : IsOrdinaryPoly Φ)
    (hR : IsRealPoly b E q Φ) {K : ℝ} (hK : 0 ≤ K) {t₁ T δ lam κ η : ℝ} (ht₀ : 0 < t₀)
    (ht₁ : t₀ ≤ t₁) (hT : t₁ < T) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hlam : 0 < lam) (hκ : 0 < κ)
    (hεj : t₀ / 2 * W ≤ ⌊(W : ℝ) * t₁⌋₊)
    (hthr : 3 * lam + (δ + 1 / W) * aliveBound K (wordGenerator b E q (t₀ + 1) Φ) + κ ≤ η)
    {CL : ℝ≥0∞} (hCL : CL ≠ ⊤) (hL : ∀ j : ℕ, t₀ / 2 * W ≤ j → (j : ℝ) ≤ (T + 1) * W →
      ∫⁻ ω, ENNReal.ofReal (wordLoad b E k q W j ω) ^ (4 * polyExp Φ + 1)
        ∂growthPathLaw W b ≤ CL)
    {Bd Bc : ℝ} (Br : ℕ → ℝ)
    (hSd : ∑ j ∈ (range ⌊(T + 1) * W⌋₊).filter (fun j : ℕ => ⌊(W : ℝ) * t₁⌋₊ ≤ j),
      ∫⁻ ω, ‖driftErr b E k q K (t₀ / 2) W Φ j ω‖ₑ ∂growthPathLaw W b ≤ ENNReal.ofReal Bd)
    (hSc : ∑ j ∈ (range ⌊(T + 1) * W⌋₊).filter (fun j : ℕ => ⌊(W : ℝ) * t₁⌋₊ ≤ j),
      ∫⁻ ω, ‖carreErr b E k q K (t₀ / 2) W Φ j ω‖ₑ ∂growthPathLaw W b ≤ ENNReal.ofReal Bc)
    (hSr : ∀ r < 5, ∑ j ∈ (range ⌊(T + 1) * W⌋₊).filter (fun j : ℕ => ⌊(W : ℝ) * t₁⌋₊ ≤ j),
      ∫⁻ ω, ‖driftErr b E k q K (t₀ / 2) W (Φ ^ r) j ω‖ₑ ∂growthPathLaw W b ≤
        ENNReal.ofReal (Br r)) :
    growthPathLaw W b {ω | ∃ t ∈ Set.Icc t₁ T, ∃ t' ∈ Set.Icc t₁ T, |t - t'| ≤ δ ∧
        η < |realVal b E k q W ⌊(W : ℝ) * t⌋₊ Φ ω - realVal b E k q W ⌊(W : ℝ) * t'⌋₊ Φ ω|} ≤
      growthPathLaw W b {ω | ∃ j : ℕ, t₀ / 2 * W ≤ j ∧ (j : ℝ) ≤ (T + 1) * W ∧
          K < traceLoad b E k q W j ω} +
        (ENNReal.ofReal ((16 * aliveBound K (wordCarre b E Φ) ^ 2 * (T + 1) * (δ + 1 / W) +
          16 * max Bc 0 ^ 2 + 8 * lam ^ 2 * max Bc 0 +
          48 * ∑ r ∈ range 5, (Nat.choose 4 r : ℝ) * aliveBound K Φ ^ (4 - r) * max (Br r) 0) /
            lam ^ 4) + ENNReal.ofReal (max Bd 0 / κ)) := by
  set μ := growthPathLaw W b
  set ε := t₀ / 2
  set j₁ := ⌊(W : ℝ) * t₁⌋₊
  set j₂ := ⌊(W : ℝ) * T⌋₊
  set ℓ := ⌊(W : ℝ) * δ⌋₊ + 1 with hℓdef
  set N := (j₂ - j₁) / ℓ + 1
  set CA := aliveBound K (wordGenerator b E q (t₀ + 1) Φ)
  set CG := aliveBound K (wordCarre b E Φ)
  set CX := aliveBound K Φ
  set steps := (range ⌊(T + 1) * W⌋₊).filter (fun j : ℕ => j₁ ≤ j)
  have hW1 : 1 ≤ W := by omega
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have ht₀1 : t₀ < t₁ + 1 := by linarith
  have hℓ : 0 < ℓ := Nat.succ_pos _
  have hj12 : j₁ ≤ j₂ := Nat.floor_mono (mul_le_mul_of_nonneg_left hT.le hW0.le)
  have hNℓ1 : j₂ - j₁ < N * ℓ := by
    have := Nat.lt_div_mul_add (a := j₂ - j₁) hℓ; rw [Nat.succ_mul]; exact this
  have hNℓ2 : N * ℓ ≤ j₂ - j₁ + ℓ := by
    rw [Nat.succ_mul]; exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
  have hT0 : 0 < T := by linarith
  have hj2r : (j₂ : ℝ) ≤ W * T := Nat.floor_le (by positivity)
  have hℓr : (ℓ : ℝ) ≤ W * δ + 1 := by
    rw [hℓdef]; push_cast; linarith [Nat.floor_le (mul_nonneg hW0.le hδ.le)]
  have hj1r : (W : ℝ) * t₁ < j₁ + 1 := Nat.lt_floor_add_one _
  have hNℓr : (j₁ : ℝ) + (N * ℓ : ℕ) ≤ (T + 1) * W := by
    have : (j₁ + N * ℓ : ℕ) ≤ j₂ + ℓ := by omega
    have h' : ((j₁ + N * ℓ : ℕ) : ℝ) ≤ j₂ + ℓ := by exact_mod_cast this
    push_cast at h' ⊢; nlinarith
  -- index facts
  have hidx : ∀ i ≤ N * ℓ, ε * W ≤ ((j₁ + i : ℕ) : ℝ) ∧ ((j₁ + i : ℕ) : ℝ) ≤ (T + 1) * W :=
    fun i hi => ⟨hεj.trans (by exact_mod_cast Nat.le_add_right _ _), by
      have : ((j₁ + i : ℕ) : ℝ) ≤ j₁ + (N * ℓ : ℕ) := by exact_mod_cast Nat.add_le_add_left hi _
      exact this.trans hNℓr⟩
  have hsteps : ∀ i < N * ℓ, j₁ + i ∈ steps := fun i hi => by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, Nat.le_add_right _ _⟩
    have h1 : ((j₁ + i + 1 : ℕ) : ℝ) ≤ (T + 1) * W := by
      have := (hidx (i + 1) hi).2; simpa [Nat.add_assoc] using this
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_floor h1)
  have hit : ∀ i, t₀ < ((j₁ + i + 1 : ℕ) : ℝ) / W := fun i => by
    rw [lt_div_iff₀ hW0]; push_cast
    nlinarith [mul_le_mul_of_nonneg_left ht₁ hW0.le, (Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  -- the summed errors
  obtain ⟨hgI, hGle⟩ := sum_integral_norm_le (μ := μ) _ (aestronglyMeasurable_driftErr b E k q K ε Φ)
    steps j₁ (N * ℓ) hsteps hSd
  obtain ⟨hfI, hFle⟩ := sum_integral_norm_le (μ := μ) _ (aestronglyMeasurable_carreErr b E k q K ε Φ)
    steps j₁ (N * ℓ) hsteps hSc
  have hrI := fun r (hr : r < 5) => sum_integral_norm_le (μ := μ) _
    (aestronglyMeasurable_driftErr b E k q K ε (Φ ^ r)) steps j₁ (N * ℓ) hsteps (hSr r hr)
  -- the increments
  set d : ℕ → GrowthPath W → ℝ := fun i => stepInc b E k q K ε W Φ (j₁ + i)
  have hX4 : ∀ i ≤ N * ℓ, Integrable (fun ω => realVal b E k q W (j₁ + i) Φ ω ^ 4) μ :=
    fun i hi => integrable_realVal_pow4 b E k q Φ hb hE1 hE2 hW1 hq hΦ _ hCL
      (hL _ (hidx i hi).1 (hidx i hi).2)
  have hd4 : ∀ i < N * ℓ, Integrable (fun ω => d i ω ^ 4) μ := fun i hi => by
    refine integrable_of_norm_le ((((stronglyMeasurable_stepInc b E k q K ε Φ (j₁ + i)).mono
      (growthSigma_le' W _)).aestronglyMeasurable).pow 4)
      (((hX4 (i + 1) hi).add (hX4 i hi.le)).const_mul 8) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Even.pow_nonneg (by decide) _)]
    simp only [d, stepInc, Pi.add_apply]
    by_cases h : ω ∈ alive b E k q K ε W (j₁ + i)
    · rw [Set.indicator_of_mem h]; exact sub_pow4_le _ _
    · rw [Set.indicator_of_notMem h]
      nlinarith [Even.pow_nonneg (by decide : Even 4) (realVal b E k q W (j₁ + i) Φ ω),
        Even.pow_nonneg (by decide : Even 4) (realVal b E k q W (j₁ + (i + 1)) Φ ω)]
  have hmt := modulus_tail (μ := μ) (fun i => growthSigma W (j₁ + i)) (fun i => growthSigma_le' W _)
    (fun i j hij => FullSource.growthSigma_mono (by omega)) N ℓ hℓ d
    (fun i ω => ‖carreErr b E k q K ε W Φ (j₁ + i) ω‖)
    (fun i ω => ‖driftErr b E k q K ε W Φ (j₁ + i) ω‖) ((W : ℝ)⁻¹ * CG) ((W : ℝ)⁻¹ * CA) lam κ
    (mul_nonneg (by positivity) (aliveBound_nonneg hK _))
    (mul_nonneg (by positivity) (aliveBound_nonneg hK _)) hlam hκ
    (fun i => stronglyMeasurable_stepInc b E k q K ε Φ (j₁ + i)) hd4 (fun i ω => norm_nonneg _)
    hfI (fun i hi => condExp_stepInc_sq_le k q K ε Φ hb hE1 hE2 hW1 hq hΦ hR hK (hidx i hi.le).1)
    (fun i ω => norm_nonneg _) hgI
    (fun i hi => ae_abs_condExp_stepInc_le k q K ε Φ hb hE1 hE2 hW1 hq hΦ hR hK hq0
      (hidx i hi.le).1 (hit i))
  -- the fourth moments
  have hD : ∑ i ∈ range (N * ℓ), ∫ ω, d i ω ^ 4 ∂μ ≤
      ∑ r ∈ range 5, (Nat.choose 4 r : ℝ) * CX ^ (4 - r) * max (Br r) 0 := by
    calc ∑ i ∈ range (N * ℓ), ∫ ω, d i ω ^ 4 ∂μ
        ≤ ∑ i ∈ range (N * ℓ), ∑ r ∈ range 5, (Nat.choose 4 r : ℝ) * CX ^ (4 - r) *
            ∫ ω, ‖driftErr b E k q K ε W (Φ ^ r) (j₁ + i) ω‖ ∂μ :=
          Finset.sum_le_sum fun i hi => integral_stepInc_pow4_le k q K ε Φ hb hE1 hE2 hW1 hq hΦ hR
            hK (hidx i (Finset.mem_range.mp hi).le).1 (hX4 i (Finset.mem_range.mp hi).le)
            (hX4 (i + 1) (Finset.mem_range.mp hi))
            (fun r hr => (hrI r hr).1 i (Finset.mem_range.mp hi))
      _ = ∑ r ∈ range 5, (Nat.choose 4 r : ℝ) * CX ^ (4 - r) *
            ∑ i ∈ range (N * ℓ), ∫ ω, ‖driftErr b E k q K ε W (Φ ^ r) (j₁ + i) ω‖ ∂μ := by
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_left
          (hrI r (Finset.mem_range.mp hr)).2 (by have := aliveBound_nonneg hK Φ; positivity)
  -- the inclusion
  set Stop := {ω : GrowthPath W | ∃ j : ℕ, ε * W ≤ j ∧ (j : ℝ) ≤ (T + 1) * W ∧
    K < traceLoad b E k q W j ω}
  have hincl : {ω | ∃ t ∈ Set.Icc t₁ T, ∃ t' ∈ Set.Icc t₁ T, |t - t'| ≤ δ ∧
      η < |realVal b E k q W ⌊(W : ℝ) * t⌋₊ Φ ω - realVal b E k q W ⌊(W : ℝ) * t'⌋₊ Φ ω|} ⊆
      Stop ∪ {ω | ∃ x y, x ≤ y ∧ y ≤ N * ℓ ∧ y ≤ x + ℓ ∧
        3 * lam + ℓ * ((W : ℝ)⁻¹ * CA) + κ < |∑ i ∈ Finset.Ico x y, d i ω|} := by
    intro ω ⟨t, ht, t', ht', htt, hgt⟩
    by_cases hS : ω ∈ Stop
    · exact Or.inl hS
    right
    have claim : ∀ u ∈ Set.Icc t₁ T, ∀ v ∈ Set.Icc t₁ T, u ≤ v → v - u ≤ δ →
        η < |realVal b E k q W ⌊(W : ℝ) * v⌋₊ Φ ω - realVal b E k q W ⌊(W : ℝ) * u⌋₊ Φ ω| →
        ∃ x y, x ≤ y ∧ y ≤ N * ℓ ∧ y ≤ x + ℓ ∧
          3 * lam + ℓ * ((W : ℝ)⁻¹ * CA) + κ < |∑ i ∈ Finset.Ico x y, d i ω| := by
      intro u hu v hv huv hvu hη
      have hu1 : j₁ ≤ ⌊(W : ℝ) * u⌋₊ := Nat.floor_mono (mul_le_mul_of_nonneg_left hu.1 hW0.le)
      have hv1 : j₁ ≤ ⌊(W : ℝ) * v⌋₊ := Nat.floor_mono (mul_le_mul_of_nonneg_left hv.1 hW0.le)
      have hv2 : ⌊(W : ℝ) * v⌋₊ ≤ j₂ := Nat.floor_mono (mul_le_mul_of_nonneg_left hv.2 hW0.le)
      have huv' : ⌊(W : ℝ) * u⌋₊ ≤ ⌊(W : ℝ) * v⌋₊ :=
        Nat.floor_mono (mul_le_mul_of_nonneg_left huv hW0.le)
      have hu0 : 0 ≤ (W : ℝ) * u := mul_nonneg hW0.le (by linarith [hu.1])
      have hvl : ⌊(W : ℝ) * v⌋₊ ≤ ⌊(W : ℝ) * u⌋₊ + ℓ := by
        have h1 : ⌊(W : ℝ) * v⌋₊ ≤ ⌊(W : ℝ) * u + W * δ⌋₊ :=
          Nat.floor_mono (by nlinarith)
        exact h1.trans (floor_add_le hu0 (mul_nonneg hW0.le hδ.le))
      refine ⟨⌊(W : ℝ) * u⌋₊ - j₁, ⌊(W : ℝ) * v⌋₊ - j₁, by omega, by omega, by omega, ?_⟩
      have hsum : ∑ i ∈ Finset.Ico (⌊(W : ℝ) * u⌋₊ - j₁) (⌊(W : ℝ) * v⌋₊ - j₁), d i ω =
          realVal b E k q W ⌊(W : ℝ) * v⌋₊ Φ ω - realVal b E k q W ⌊(W : ℝ) * u⌋₊ Φ ω := by
        rw [Finset.sum_congr rfl fun i hi => ?_, sum_Ico_telescope
          (fun i => realVal b E k q W (j₁ + i) Φ ω) (by omega),
          Nat.add_sub_cancel' hv1, Nat.add_sub_cancel' hu1]
        have hi' : i < N * ℓ := by have := (Finset.mem_Ico.mp hi).2; omega
        exact Set.indicator_of_mem (mem_alive_of_notMem_stop hS (hidx i hi'.le).2) _
      rw [hsum]
      refine lt_of_le_of_lt ?_ hη
      have : (ℓ : ℝ) * ((W : ℝ)⁻¹ * CA) ≤ (δ + 1 / W) * CA := by
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (aliveBound_nonneg hK _)
        rw [← div_eq_mul_inv, div_le_iff₀ hW0, add_mul, one_div, inv_mul_cancel₀ hW0.ne',
          mul_comm δ]
        exact hℓr
      linarith
    rcases le_total t t' with h | h
    · exact claim t ht t' ht' h (by rw [abs_sub_comm] at htt; linarith [le_abs_self (t' - t)])
        (by rwa [abs_sub_comm] at hgt)
    · exact claim t' ht' t ht h (by linarith [le_abs_self (t - t')]) hgt
  refine (measure_mono hincl).trans ((measure_union_le _ _).trans (add_le_add le_rfl
    (hmt.trans (add_le_add (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_le_ofReal ?_)))))
  · refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hF0 : 0 ≤ ∑ i ∈ range (N * ℓ), ∫ ω, ‖carreErr b E k q K ε W Φ (j₁ + i) ω‖ ∂μ :=
      Finset.sum_nonneg fun i _ => integral_nonneg fun ω => norm_nonneg _
    have hCG : (W : ℝ)⁻¹ ^ 2 * ((N * ℓ : ℕ) : ℝ) * ℓ ≤ (T + 1) * (δ + 1 / W) := by
      have h1 : ((N * ℓ : ℕ) : ℝ) ≤ (T + 1) * W := by
        have := Nat.cast_nonneg (α := ℝ) j₁; linarith
      have h2 : (W : ℝ)⁻¹ * ((N * ℓ : ℕ) : ℝ) ≤ T + 1 := by
        rw [← div_eq_inv_mul, div_le_iff₀ hW0]; exact h1
      have h3 : (W : ℝ)⁻¹ * ℓ ≤ δ + 1 / W := by
        rw [← div_eq_inv_mul, div_le_iff₀ hW0, add_mul, one_div, inv_mul_cancel₀ hW0.ne']
        linarith
      calc (W : ℝ)⁻¹ ^ 2 * ((N * ℓ : ℕ) : ℝ) * ℓ =
            ((W : ℝ)⁻¹ * ((N * ℓ : ℕ) : ℝ)) * ((W : ℝ)⁻¹ * ℓ) := by ring
        _ ≤ (T + 1) * (δ + 1 / W) := mul_le_mul h2 h3 (by positivity) (by linarith)
    have hCG' : 16 * ((W : ℝ)⁻¹ * CG) ^ 2 * ((N : ℝ) * ℓ) * ℓ ≤
        16 * CG ^ 2 * (T + 1) * (δ + 1 / W) := by
      have e : 16 * ((W : ℝ)⁻¹ * CG) ^ 2 * ((N : ℝ) * ℓ) * ℓ =
          16 * CG ^ 2 * ((W : ℝ)⁻¹ ^ 2 * ((N * ℓ : ℕ) : ℝ) * ℓ) := by push_cast; ring
      have e2 : 16 * CG ^ 2 * (T + 1) * (δ + 1 / W) = 16 * CG ^ 2 * ((T + 1) * (δ + 1 / W)) := by
        ring
      rw [e, e2]
      exact mul_le_mul_of_nonneg_left hCG (by positivity)
    have hF2 := pow_le_pow_left₀ hF0 hFle 2
    have h8 := mul_le_mul_of_nonneg_left hFle (by positivity : (0 : ℝ) ≤ 8 * lam ^ 2)
    linarith [hD]
  · exact div_le_div_of_nonneg_right hGle hκ.le

end BlockBand.SourceProcess.FullSourceGenerator
