module

public import BlockBand.Transmission.Dual.GJTransform
public import BlockBand.Transmission.Dual.GHLemma1
public import BlockBand.Transmission.Dual.GB1

/-!
# The product-transform identity and the comparison process `Q^{(j)}`

Level `p = q + 1`, `j : Fin (q + 1)`, `e = slotEquiv j`.
* `isMPSolutionOn_slotPath`: a level-1 solution `Y₁` of the flat dual in an open `U₁ ⊆ 𝒞₁` and a
  level-`q` solution `Y₂` in an open `U₂ ⊆ 𝒞_q` give, on `Q₁ ⊗ Q₂` with the product filtration,
  a solution of the `(gDrift D₀ j, flatDiff D₀ (q+1))` problem in every `W` whose pair and rest
  projections lie in `U₁`, `U₂` (`isMPSolutionOn_prod`, `isMPSolutionOn_reindex`).
* **`lemma1J`**: the local Doob identity for the product transform `G_j` and such a comparison
  process: `Q^{(j)}((Y^{τ_W})^{t₀} ∈ B) = E⁰[G_j(Z_{t₀∧τ_W})/G_j(z); (Z^{τ_W})^{t₀} ∈ B]`
  (`lemma1H` with `isHTransform_flatG`).
* `B1Family.exists_forall_isMPSolutionOn_Yf`, **`lemma1J_B1`**: the comparison process is the
  product of two families of the dual up to exhaustion (pair, rest), relabelled, for all radii
  `n₁, n₂ ≥ N`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Levy BlockBand.Transmission.Dual
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {q : ℕ} {D0 : ℝ}

section Comparison

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  {Q₁ : Measure Ω₁} {Q₂ : Measure Ω₂}
  {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)}
  {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)}
  {Y₁ : ℝ≥0 → Ω₁ → Fin (1 + 1) → ℝ} {Y₂ : ℝ≥0 → Ω₂ → Fin (q + q) → ℝ}
  {U₁ : Set (Fin (1 + 1) → ℝ)} {U₂ : Set (Fin (q + q) → ℝ)}
  {W : Set (Fin ((q + 1) + (q + 1)) → ℝ)}

/-- **The comparison process `Q^{(j)}`**: pair and rest solutions, relabelled by `slotEquiv j`. -/
theorem isMPSolutionOn_slotPath [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
    (h₁ : IsMPSolutionOn Q₁ 𝓖₁ (flatDrift D0 1) (flatDiff D0 1) U₁ Y₁)
    (h₂ : IsMPSolutionOn Q₂ 𝓖₂ (flatDrift D0 q) (flatDiff D0 q) U₂ Y₂)
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU₁c : U₁ ⊆ flatChamber 1) (hU₂c : U₂ ⊆ flatChamber q)
    (j : Fin (q + 1)) (hW : ∀ w ∈ W, leftPart (w ∘ (slotEquiv j).symm) ∈ U₁ ∧
      rightPart (w ∘ (slotEquiv j).symm) ∈ U₂) :
    IsMPSolutionOn (Q₁.prod Q₂) (prodFiltration 𝓖₁ 𝓖₂) (gDrift D0 j) (flatDiff D0 (q + 1)) W
      (slotPath j Y₁ Y₂) := by
  have H := isMPSolutionOn_reindex (slotEquiv j) (isMPSolutionOn_prod h₁ h₂ hU₁ hU₂
    ((continuousOn_flatDrift D0).mono hU₁c) (contDiff_flatDiff D0).continuous.continuousOn
    ((continuousOn_flatDrift D0).mono hU₂c) (contDiff_flatDiff D0).continuous.continuousOn)
  rw [reindexDiff_slot_base] at H
  exact isMPSolutionOn_mono H fun w hw => hW w hw

omit [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] in
theorem slotPath_zero {z : Fin ((q + 1) + (q + 1)) → ℝ} (j : Fin (q + 1))
    (h₁0 : ∀ ω, Y₁ 0 ω = leftPart (z ∘ (slotEquiv j).symm))
    (h₂0 : ∀ ω, Y₂ 0 ω = rightPart (z ∘ (slotEquiv j).symm)) (x : Ω₁ × Ω₂) :
    slotPath j Y₁ Y₂ 0 x = z := by
  simp only [slotPath, prodPath, h₁0, h₂0]
  exact append_slot_comp j z

theorem map_slotPath_zero [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
    {z : Fin ((q + 1) + (q + 1)) → ℝ} (j : Fin (q + 1))
    (h₁0 : ∀ ω, Y₁ 0 ω = leftPart (z ∘ (slotEquiv j).symm))
    (h₂0 : ∀ ω, Y₂ 0 ω = rightPart (z ∘ (slotEquiv j).symm)) :
    (Q₁.prod Q₂).map (slotPath j Y₁ Y₂ 0) = Measure.dirac z := by
  have e : slotPath j Y₁ Y₂ 0 = fun _ => z := funext (slotPath_zero j h₁0 h₂0)
  rw [e, Measure.map_const, measure_univ, one_smul]

end Comparison

/-- **The product-transform identity** for a comparison process built from a pair solution and
a rest solution: for every interior domain `W ∋ z` of `𝒞_{q+1}`, every `t₀` and every measurable
path set `B`, `Q^{(j)}((Y^{τ_W})^{t₀} ∈ B) = E_P[G_j(Z_{t₀∧τ_W})/G_j(z); (Z^{τ_W})^{t₀} ∈ B]`. -/
theorem lemma1J (hD0 : 0 < D0) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {Z : ℝ≥0 → Ω → Fin ((q + 1) + (q + 1)) → ℝ} {z : Fin ((q + 1) + (q + 1)) → ℝ}
    (hZ : IsBaseSol D0 (q + 1) P 𝓖 Z z) {W : Set (Fin ((q + 1) + (q + 1)) → ℝ)}
    (hW : IsInteriorDomain W (flatChamber (q + 1))) (hzW : z ∈ W) (j : Fin (q + 1))
    {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {Q₁ : Measure Ω₁} {Q₂ : Measure Ω₂}
    [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
    {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)}
    {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)}
    {Y₁ : ℝ≥0 → Ω₁ → Fin (1 + 1) → ℝ} {Y₂ : ℝ≥0 → Ω₂ → Fin (q + q) → ℝ}
    {U₁ : Set (Fin (1 + 1) → ℝ)} {U₂ : Set (Fin (q + q) → ℝ)}
    (h₁ : IsMPSolutionOn Q₁ 𝓖₁ (flatDrift D0 1) (flatDiff D0 1) U₁ Y₁)
    (h₂ : IsMPSolutionOn Q₂ 𝓖₂ (flatDrift D0 q) (flatDiff D0 q) U₂ Y₂)
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU₁c : U₁ ⊆ flatChamber 1) (hU₂c : U₂ ⊆ flatChamber q)
    (hWU : ∀ w ∈ W, leftPart (w ∘ (slotEquiv j).symm) ∈ U₁ ∧
      rightPart (w ∘ (slotEquiv j).symm) ∈ U₂)
    (h₁0 : ∀ ω, Y₁ 0 ω = leftPart (z ∘ (slotEquiv j).symm))
    (h₂0 : ∀ ω, Y₂ 0 ω = rightPart (z ∘ (slotEquiv j).symm))
    (t₀ : ℝ≥0) {B : Set (ℝ≥0 → Fin ((q + 1) + (q + 1)) → ℝ)} (hB : MeasurableSet B) :
    (Q₁.prod Q₂).real {x | (fun t => stoppedProcess (slotPath j Y₁ Y₂)
        (exitTimeFrom W (slotPath j Y₁ Y₂)) (min t t₀) x) ∈ B} =
      ∫ ω in {ω | (fun t => stopZ W Z (min t t₀) ω) ∈ B}, densH (flatG j) W Z z t₀ ω ∂P :=
  lemma1H hD0 (isHTransform_flatG D0 j) hZ hW hzW
    (isMPSolutionOn_slotPath h₁ h₂ hU₁ hU₂ hU₁c hU₂c j hWU) (map_slotPath_zero j h₁0 h₂0) t₀ hB

/-!
## The comparison process from two families
-/

theorem chartQ_ball_mono {m n : ℕ} (h : m ≤ n) :
    chartQ q '' Metric.ball 0 m ⊆ chartQ q '' Metric.ball 0 n :=
  image_mono (Metric.ball_subset_ball (Nat.cast_le.2 h))

/-- For an interior domain `W` of `𝒞_{q+1}`, interior domains of `𝒞₁`, `𝒞_q` containing its pair
and rest projections. -/
theorem exists_factor_interiorDomains {W : Set (Fin ((q + 1) + (q + 1)) → ℝ)}
    (hW : IsInteriorDomain W (flatChamber (q + 1))) (j : Fin (q + 1)) :
    ∃ (W₁ : Set (Fin (1 + 1) → ℝ)) (W₂ : Set (Fin (q + q) → ℝ)),
      IsInteriorDomain W₁ (flatChamber 1) ∧ IsInteriorDomain W₂ (flatChamber q) ∧
      ∀ w ∈ W, leftPart (w ∘ (slotEquiv j).symm) ∈ W₁ ∧
        rightPart (w ∘ (slotEquiv j).symm) ∈ W₂ := by
  have c₁ : Continuous fun w : Fin ((q + 1) + (q + 1)) → ℝ => leftPart (w ∘ (slotEquiv j).symm) :=
    (leftL.comp (compL (slotEquiv j).symm)).continuous
  have c₂ : Continuous fun w : Fin ((q + 1) + (q + 1)) → ℝ => rightPart (w ∘ (slotEquiv j).symm) :=
    (rightL.comp (compL (slotEquiv j).symm)).continuous
  obtain ⟨W₁, hW₁, hK₁⟩ := exists_interiorDomain_superset (hW.2.1.image c₁) (isOpen_flatChamber 1)
    (by rintro _ ⟨w, hw, rfl⟩; exact left_slot_mem (hW.2.2 hw) j)
  obtain ⟨W₂, hW₂, hK₂⟩ := exists_interiorDomain_superset (hW.2.1.image c₂) (isOpen_flatChamber q)
    (by rintro _ ⟨w, hw, rfl⟩; exact right_slot_mem (hW.2.2 hw) j)
  exact ⟨W₁, W₂, hW₁, hW₂, fun w hw =>
    ⟨hK₁ ⟨w, subset_closure hw, rfl⟩, hK₂ ⟨w, subset_closure hw, rfl⟩⟩⟩

/-- A `B1Family` solves the flat dual problem in an interior domain for all large radii. -/
theorem B1Family.exists_forall_isMPSolutionOn_Yf (hD0 : 0 < D0) {z : Fin (q + q) → ℝ}
    (F : B1Family D0 q z) {W : Set (Fin (q + q) → ℝ)} (hW : IsInteriorDomain W (flatChamber q)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      IsMPSolutionOn (Pq q) (𝓖q q) (flatDrift D0 q) (flatDiff D0 q) W (F.Yf n) := by
  obtain ⟨N, hN⟩ := exists_ball_superset hW.2.1 hW.2.2
  exact ⟨N, fun n hn => isMPSolutionOn_mono (F.isMPSolutionOn_Yf hD0 n)
    (subset_closure.trans (hN.trans (chartQ_ball_mono hn)))⟩

/-- **The product-transform identity for the comparison process**
`Q^{(j)} = (pair family ⊗ rest family) ∘ slotEquiv j`, for all radii `n₁, n₂ ≥ N`. -/
theorem lemma1J_B1 (hD0 : 0 < D0) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {Z : ℝ≥0 → Ω → Fin ((q + 1) + (q + 1)) → ℝ} {z : Fin ((q + 1) + (q + 1)) → ℝ}
    (hZ : IsBaseSol D0 (q + 1) P 𝓖 Z z) {W : Set (Fin ((q + 1) + (q + 1)) → ℝ)}
    (hW : IsInteriorDomain W (flatChamber (q + 1))) (hzW : z ∈ W) (j : Fin (q + 1))
    (F₁ : B1Family D0 1 (leftPart (z ∘ (slotEquiv j).symm)))
    (F₂ : B1Family D0 q (rightPart (z ∘ (slotEquiv j).symm))) :
    ∃ N : ℕ, ∀ n₁ n₂, N ≤ n₁ → N ≤ n₂ → ∀ (t₀ : ℝ≥0) {B : Set (ℝ≥0 → Fin ((q + 1) + (q + 1)) → ℝ)},
      MeasurableSet B →
      ((Pq 1).prod (Pq q)).real {x | (fun t => stoppedProcess (slotPath j (F₁.Yf n₁) (F₂.Yf n₂))
        (exitTimeFrom W (slotPath j (F₁.Yf n₁) (F₂.Yf n₂))) (min t t₀) x) ∈ B} =
      ∫ ω in {ω | (fun t => stopZ W Z (min t t₀) ω) ∈ B}, densH (flatG j) W Z z t₀ ω ∂P := by
  have hz : z ∈ flatChamber (q + 1) := hW.2.2 (subset_closure hzW)
  obtain ⟨W₁, W₂, hW₁, hW₂, hWW⟩ := exists_factor_interiorDomains hW j
  obtain ⟨N₁, hN₁⟩ := F₁.exists_forall_isMPSolutionOn_Yf hD0 hW₁
  obtain ⟨N₂, hN₂⟩ := F₂.exists_forall_isMPSolutionOn_Yf hD0 hW₂
  refine ⟨max N₁ N₂, fun n₁ n₂ h₁ h₂ t₀ B hB => lemma1J hD0 hZ hW hzW j
    (hN₁ n₁ ((le_max_left _ _).trans h₁)) (hN₂ n₂ ((le_max_right _ _).trans h₂)) hW₁.1 hW₂.1
    (subset_closure.trans hW₁.2.2) (subset_closure.trans hW₂.2.2) hWW
    (F₁.Yf_zero (left_slot_mem hz j) n₁) (F₂.Yf_zero (right_slot_mem hz j) n₂) t₀ hB⟩

end BlockBand.Transmission.Dual.G
