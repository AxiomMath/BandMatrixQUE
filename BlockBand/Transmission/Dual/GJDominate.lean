module

public import BlockBand.Transmission.Dual.GJLemma1

/-!
# Domination at a fixed domain, and the collision bound

`Z` is a base solution from `z`, `W ∋ z` an interior domain of the chamber.
* `flatH_le_sum`: `H_{q+1} ≤ Σ_j G_j` on `𝒞_{q+1}` (`cauchyH_le_sum`, `flatG_eq`).
* `densH_le_sum`, `setIntegral_densH_le_sum`: the density of `H_{q+1}` is dominated by
  `Σ_j c_j` times the density of `G_j`, `c_j = G_j(z)/H_{q+1}(z)`.
* **`dominate_B1`**: for every comparison solution `Y₀` of the `(q+1)`-dual in `W` from `z` and
  pair/rest families, for all radii `n₁, n₂ ≥ N`, every `t₀` and every measurable path set `B`,
  `Q₀((Y₀^{τ_W})^{t₀} ∈ B) ≤ Σ_j c_j Q^{(j)}((Y^{(j),τ_W})^{t₀} ∈ B)` (the local Doob identity and
  its product form). This is the domination inequality on each `𝒜_n`; the extension to
  `σ(⋃_n 𝒜_n)` is `dominate_stopSeq`.
* **`lemmaC_bound`**: if `H_q ≤ M` on `A ∩ closure W` then
  `Q₂(Y₂^{τ_W}_{t₀} ∈ A) ≤ M / H_q(z)`; the event is the cylinder `{w(t₀) ∈ A}` of the stopped,
  truncated path, so no exit-time functional is needed. **`lemmaC_gap`**: with the gap set of
  `exists_cauchyH_le_of_gap`, the bound is `C_{q,η,K} δ / H_q(z)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Dual
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {q : ℕ} {D0 : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

theorem integrable_densH {U W : Set (Fin (q + q) → ℝ)} {h : (Fin (q + q) → ℝ) → ℝ}
    {bt : (Fin (q + q) → ℝ) → Fin (q + q) → ℝ} {Z : ℝ≥0 → Ω → Fin (q + q) → ℝ}
    {z : Fin (q + q) → ℝ} (hh : IsHTransform D0 q U h bt) (hZ : IsBaseSol D0 q P 𝓖 Z z)
    (hW : IsInteriorDomain W U) (hzW : z ∈ W) (t : ℝ≥0) : Integrable (densH h W Z z t) P := by
  obtain ⟨M, g, hg, hMe, -⟩ := exists_tiltH hh hZ hW hzW
  exact (hg.mart.integrable t).congr (hMe t)

/-- `H_{q+1} ≤ Σ_j G_j` on the chamber. -/
theorem flatH_le_sum {w : Fin ((q + 1) + (q + 1)) → ℝ} (hw : w ∈ flatChamber (q + 1)) :
    flatH (q + 1) w ≤ ∑ j, flatG j w := by
  calc flatH (q + 1) w = cauchyH (q + 1) (ofFlat (q + 1) w) := rfl
    _ ≤ _ := cauchyH_le_sum hw
    _ = ∑ j, flatG j w := by simp only [flatG_eq]

section Dominate

variable {Z : ℝ≥0 → Ω → Fin ((q + 1) + (q + 1)) → ℝ} {z : Fin ((q + 1) + (q + 1)) → ℝ}
  {W : Set (Fin ((q + 1) + (q + 1)) → ℝ)}

omit [IsProbabilityMeasure P] in
theorem densH_le_sum (hZ : IsBaseSol D0 (q + 1) P 𝓖 Z z)
    (hW : IsInteriorDomain W (flatChamber (q + 1))) (hzW : z ∈ W) (t : ℝ≥0) (ω : Ω) :
    densH (flatH (q + 1)) W Z z t ω ≤
      ∑ j, flatG j z / flatH (q + 1) z * densH (flatG j) W Z z t ω := by
  have hz : z ∈ flatChamber (q + 1) := hW.2.2 (subset_closure hzW)
  have hw := hW.2.2 (stopZ_mem_closure hZ hW.1 hzW t ω)
  have e : ∀ j, flatG j z / flatH (q + 1) z * densH (flatG j) W Z z t ω =
      flatG j (stopZ W Z t ω) / flatH (q + 1) z := fun j => by
    rw [densH, div_mul_div_comm, mul_comm (flatG j z),
      mul_div_mul_right _ _ (flatG_pos hz j).ne']
  simp only [e, ← Finset.sum_div]
  exact div_le_div_of_nonneg_right (flatH_le_sum hw) (cauchyH_pos hz).le

theorem setIntegral_densH_le_sum (hZ : IsBaseSol D0 (q + 1) P 𝓖 Z z)
    (hW : IsInteriorDomain W (flatChamber (q + 1))) (hzW : z ∈ W) (t : ℝ≥0) {S : Set Ω}
    (hS : MeasurableSet S) :
    ∫ ω in S, densH (flatH (q + 1)) W Z z t ω ∂P ≤
      ∑ j, flatG j z / flatH (q + 1) z * ∫ ω in S, densH (flatG j) W Z z t ω ∂P := by
  have hi : ∀ j, Integrable (densH (flatG j) W Z z t) P := fun j =>
    integrable_densH (isHTransform_flatG D0 j) hZ hW hzW t
  calc ∫ ω in S, densH (flatH (q + 1)) W Z z t ω ∂P ≤
        ∫ ω in S, ∑ j, flatG j z / flatH (q + 1) z * densH (flatG j) W Z z t ω ∂P :=
      setIntegral_mono_on (integrable_densH (isHTransform_cauchyH D0) hZ hW hzW t).integrableOn
        (integrable_finsetSum _ fun j _ => (hi j).const_mul _).integrableOn hS
        fun ω _ => densH_le_sum hZ hW hzW t ω
    _ = _ := by
      rw [integral_finsetSum _ fun j _ => ((hi j).const_mul _).integrableOn]
      simp only [integral_const_mul]

/-- **The domination inequality on a fixed domain** (the local Doob identity and its product
form, with the comparison processes `Q^{(j)}`). -/
theorem dominate_B1 (hD0 : 0 < D0) (hZ : IsBaseSol D0 (q + 1) P 𝓖 Z z)
    (hW : IsInteriorDomain W (flatChamber (q + 1))) (hzW : z ∈ W) {Ω₀ : Type}
    [MeasurableSpace Ω₀] {Q₀ : Measure Ω₀} [IsProbabilityMeasure Q₀]
    {𝓗 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₀)}
    {Y₀ : ℝ≥0 → Ω₀ → Fin ((q + 1) + (q + 1)) → ℝ}
    (h₀ : IsMPSolutionOn Q₀ 𝓗 (flatDrift D0 (q + 1)) (flatDiff D0 (q + 1)) W Y₀)
    (h₀0 : Q₀.map (Y₀ 0) = Measure.dirac z)
    (F₁ : ∀ j : Fin (q + 1), B1Family D0 1 (leftPart (z ∘ (slotEquiv j).symm)))
    (F₂ : ∀ j : Fin (q + 1), B1Family D0 q (rightPart (z ∘ (slotEquiv j).symm))) :
    ∃ N : ℕ, ∀ n₁ n₂, N ≤ n₁ → N ≤ n₂ → ∀ (t₀ : ℝ≥0) {B : Set (ℝ≥0 → Fin ((q + 1) + (q + 1)) → ℝ)},
      MeasurableSet B →
      Q₀.real {ω | (fun t => stoppedProcess Y₀ (exitTimeFrom W Y₀) (min t t₀) ω) ∈ B} ≤
        ∑ j, flatG j z / flatH (q + 1) z * ((Pq 1).prod (Pq q)).real
          {x | (fun t => stoppedProcess (slotPath j ((F₁ j).Yf n₁) ((F₂ j).Yf n₂))
            (exitTimeFrom W (slotPath j ((F₁ j).Yf n₁) ((F₂ j).Yf n₂))) (min t t₀) x) ∈ B} := by
  choose N hN using fun j => lemma1J_B1 hD0 hZ hW hzW j (F₁ j) (F₂ j)
  refine ⟨Finset.univ.sup N, fun n₁ n₂ h₁ h₂ t₀ B hB => ?_⟩
  have hj : ∀ j, N j ≤ Finset.univ.sup N := fun j => Finset.le_sup (Finset.mem_univ j)
  have hS : MeasurableSet {ω | (fun t => stopZ W Z (min t t₀) ω) ∈ B} :=
    (measurable_stopZ_path hZ hW.1 t₀).mono (𝓖.le t₀) le_rfl hB
  rw [lemma1H hD0 (isHTransform_cauchyH D0) hZ hW hzW h₀ h₀0 t₀ hB]
  refine (setIntegral_densH_le_sum hZ hW hzW t₀ hS).trans
    (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  rw [hN j n₁ n₂ ((hj j).trans h₁) ((hj j).trans h₂) t₀ hB]

end Dominate

/-!
## The collision bound with the cylinder event
-/

section LemmaC

variable {Z : ℝ≥0 → Ω → Fin (q + q) → ℝ} {z : Fin (q + q) → ℝ} {W : Set (Fin (q + q) → ℝ)}
  {Ω₂ : Type} [MeasurableSpace Ω₂] {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₂]
  {𝓗 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)} {Y₂ : ℝ≥0 → Ω₂ → Fin (q + q) → ℝ}

/-- **The Doob bound for collisions** for the cylinder event `{Y₂^{τ_W}_{t₀} ∈ A}`. -/
theorem lemmaC_bound (hD0 : 0 < D0) (hZ : IsBaseSol D0 q P 𝓖 Z z)
    (hW : IsInteriorDomain W (flatChamber q)) (hzW : z ∈ W)
    (h₂ : IsMPSolutionOn Q₂ 𝓗 (flatDrift D0 q) (flatDiff D0 q) W Y₂)
    (h₂0 : Q₂.map (Y₂ 0) = Measure.dirac z) (t₀ : ℝ≥0) {A : Set (Fin (q + q) → ℝ)}
    (hA : MeasurableSet A) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ w ∈ A ∩ closure W, flatH q w ≤ M) :
    Q₂.real {ω | stoppedProcess Y₂ (exitTimeFrom W Y₂) t₀ ω ∈ A} ≤ M / flatH q z := by
  have hz : z ∈ flatChamber q := hW.2.2 (subset_closure hzW)
  have hc : 0 ≤ M / flatH q z := div_nonneg hM0 (cauchyH_pos hz).le
  have hB : MeasurableSet {w : ℝ≥0 → Fin (q + q) → ℝ | w t₀ ∈ A} := measurable_pi_apply t₀ hA
  have H := lemma1H hD0 (isHTransform_cauchyH D0) hZ hW hzW h₂ h₂0 t₀ hB
  simp only [mem_ofPred_eq, min_self] at H
  rw [H]
  have hS : MeasurableSet {ω | stopZ W Z t₀ ω ∈ A} :=
    ((stronglyMeasurable_stopZ hZ hW.1 t₀).measurable.mono (𝓖.le t₀) le_rfl) hA
  calc ∫ ω in {ω | stopZ W Z t₀ ω ∈ A}, densH (flatH q) W Z z t₀ ω ∂P ≤
        ∫ ω in {ω | stopZ W Z t₀ ω ∈ A}, M / flatH q z ∂P :=
      setIntegral_mono_on (integrable_densH (isHTransform_cauchyH D0) hZ hW hzW t₀).integrableOn
        (integrable_const _).integrableOn hS fun ω hω =>
          div_le_div_of_nonneg_right (hM _ ⟨hω, stopZ_mem_closure hZ hW.1 hzW t₀ ω⟩)
            (cauchyH_pos hz).le
    _ = P.real {ω | stopZ W Z t₀ ω ∈ A} * (M / flatH q z) := by
      rw [setIntegral_const, smul_eq_mul]
    _ ≤ 1 * (M / flatH q z) := mul_le_mul_of_nonneg_right measureReal_le_one hc
    _ = M / flatH q z := one_mul _

/-- **The collision bound** (cylinder form): on the gap set of `exists_cauchyH_le_of_gap`,
the bound is `C_{q,η,K} δ / H_q(z)`. -/
theorem lemmaC_gap (hD0 : 0 < D0) (hZ : IsBaseSol D0 q P 𝓖 Z z)
    (hW : IsInteriorDomain W (flatChamber q)) (hzW : z ∈ W)
    (h₂ : IsMPSolutionOn Q₂ 𝓗 (flatDrift D0 q) (flatDiff D0 q) W Y₂)
    (h₂0 : Q₂.map (Y₂ 0) = Measure.dirac z) {η : ℝ} (hη : 0 < η) (K : ℝ) :
    ∃ C : ℝ, ∀ (t₀ : ℝ≥0) {δ : ℝ}, 0 ≤ δ → ∀ {A : Set (Fin (q + q) → ℝ)}, MeasurableSet A →
      (∀ w ∈ A, (∀ i j, η ≤ (ofFlat q w).1 i + (ofFlat q w).2 j) ∧ (∀ i, (ofFlat q w).1 i ≤ K) ∧
        ((∃ i k, i < k ∧ (ofFlat q w).1 k - (ofFlat q w).1 i ≤ δ) ∨
          (∃ i k, i < k ∧ (ofFlat q w).2 k - (ofFlat q w).2 i ≤ δ))) →
      Q₂.real {ω | stoppedProcess Y₂ (exitTimeFrom W Y₂) t₀ ω ∈ A} ≤ max C 0 * δ / flatH q z := by
  obtain ⟨C, hC⟩ := exists_cauchyH_le_of_gap q hη K
  refine ⟨C, fun t₀ δ hδ A hA hAg => lemmaC_bound hD0 hZ hW hzW h₂ h₂0 t₀ hA
    (mul_nonneg (le_max_right _ _) hδ) fun w hw => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hAg w hw.1
  exact (hC _ (hW.2.2 hw.2) h1 h2 δ h3).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ)

end LemmaC

end BlockBand.Transmission.Dual.G
