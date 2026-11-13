module

public import BlockBand.Transmission.Dual.GDomPath
public import BlockBand.Transmission.Dual.GJDominate

/-!
# The domination inequality on `σ(⋃ₙ 𝒜ₙ)` for the laws of the dual up to exhaustion

* `exists_dominate_B1`: `dominate_B1` with the radius bound chosen before the
  comparison solution `Y₀` (same proof).
* **`dominate_stopSeq`**: there are radius bounds `R n` such that for all monotone radii
  `r, a, b ≥ R`, the laws of the stop sequences (`n ↦ pstop (W n) t₀ (path)`, on `ℕ → CPath`)
  satisfy `law(F.stopSeq r) ≤ Σ_j c_j law(slotSeq j a b)`, `c_j = G_j(z)/H_{q+1}(z)`.
  Every event of the boundary classification (rational times, stopped paths `Z^{ρ_n ∧ t₀}`,
  the left limit `z*`, `Bad`, `Coll`) is a measurable set of `ℕ → CPath`, so this is the
  domination inequality on all of `𝒜`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Dual
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {q : ℕ} {D0 : ℝ}

/-- `dominate_B1` with the radius bound before the comparison solution. -/
theorem exists_dominate_B1 (hD0 : 0 < D0) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {Z : ℝ≥0 → Ω → Fin ((q + 1) + (q + 1)) → ℝ} {z : Fin ((q + 1) + (q + 1)) → ℝ}
    (hZ : IsBaseSol D0 (q + 1) P 𝓖 Z z) {W : Set (Fin ((q + 1) + (q + 1)) → ℝ)}
    (hW : IsInteriorDomain W (flatChamber (q + 1))) (hzW : z ∈ W)
    (F₁ : ∀ j : Fin (q + 1), B1Family D0 1 (leftPart (z ∘ (slotEquiv j).symm)))
    (F₂ : ∀ j : Fin (q + 1), B1Family D0 q (rightPart (z ∘ (slotEquiv j).symm))) :
    ∃ N : ℕ, ∀ n₁ n₂, N ≤ n₁ → N ≤ n₂ → ∀ {Ω₀ : Type} [MeasurableSpace Ω₀] {Q₀ : Measure Ω₀}
      [IsProbabilityMeasure Q₀] {𝓗 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₀)}
      {Y₀ : ℝ≥0 → Ω₀ → Fin ((q + 1) + (q + 1)) → ℝ},
      IsMPSolutionOn Q₀ 𝓗 (flatDrift D0 (q + 1)) (flatDiff D0 (q + 1)) W Y₀ →
      Q₀.map (Y₀ 0) = Measure.dirac z →
      ∀ (t₀ : ℝ≥0) {B : Set (ℝ≥0 → Fin ((q + 1) + (q + 1)) → ℝ)}, MeasurableSet B →
      Q₀.real {ω | (fun t => stoppedProcess Y₀ (exitTimeFrom W Y₀) (min t t₀) ω) ∈ B} ≤
        ∑ j, flatG j z / flatH (q + 1) z * ((Pq 1).prod (Pq q)).real
          {x | (fun t => stoppedProcess (slotPath j ((F₁ j).Yf n₁) ((F₂ j).Yf n₂))
            (exitTimeFrom W (slotPath j ((F₁ j).Yf n₁) ((F₂ j).Yf n₂))) (min t t₀) x) ∈ B} := by
  choose N hN using fun j => lemma1J_B1 hD0 hZ hW hzW j (F₁ j) (F₂ j)
  refine ⟨Finset.univ.sup N, fun n₁ n₂ h₁ h₂ Ω₀ _ Q₀ _ 𝓗 Y₀ h₀ h₀0 t₀ B hB => ?_⟩
  have hj : ∀ j, N j ≤ Finset.univ.sup N := fun j => Finset.le_sup (Finset.mem_univ j)
  have hS : MeasurableSet {ω | (fun t => stopZ W Z (min t t₀) ω) ∈ B} :=
    (measurable_stopZ_path hZ hW.1 t₀).mono (𝓖.le t₀) le_rfl hB
  rw [lemma1H hD0 (isHTransform_cauchyH D0) hZ hW hzW h₀ h₀0 t₀ hB]
  refine (setIntegral_densH_le_sum hZ hW hzW t₀ hS).trans
    (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  rw [hN j n₁ n₂ ((hj j).trans h₁) ((hj j).trans h₂) t₀ hB]

/-- From a real inequality to a measure inequality. -/
theorem measure_le_sum_of_real {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {ι : Type*} [Fintype ι] {P : Measure Ω} [IsFiniteMeasure P] {Q : Measure Ω'}
    [IsFiniteMeasure Q] {S : Set Ω} {T : ι → Set Ω'} {c : ι → ℝ} (hc : ∀ j, 0 ≤ c j)
    (h : P.real S ≤ ∑ j, c j * Q.real (T j)) :
    P S ≤ ∑ j, ENNReal.ofReal (c j) * Q (T j) := by
  rw [← ofReal_measureReal (μ := P)]
  calc ENNReal.ofReal (P.real S) ≤ ENNReal.ofReal (∑ j, c j * Q.real (T j)) :=
        ENNReal.ofReal_le_ofReal h
    _ = ∑ j, ENNReal.ofReal (c j) * Q (T j) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hc j) measureReal_nonneg)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ENNReal.ofReal_mul (hc j), ofReal_measureReal]

/-- A monotone majorant. -/
def majorant (f : ℕ → ℕ) (n : ℕ) : ℕ := (Finset.range (n + 1)).sup f

theorem le_majorant (f : ℕ → ℕ) (n : ℕ) : f n ≤ majorant f n :=
  Finset.le_sup (Finset.self_mem_range_succ n)

theorem monotone_majorant (f : ℕ → ℕ) : Monotone (majorant f) := fun _ _ h =>
  Finset.sup_mono (Finset.range_subset_range.2 (by omega))

theorem B1Family.map_Yf_zero {z : Fin (q + q) → ℝ} (F : B1Family D0 q z)
    (hz : z ∈ flatChamber q) (m : ℕ) : (Pq q).map (F.Yf m 0) = Measure.dirac z := by
  have e : F.Yf m 0 = fun _ => z := funext (F.Yf_zero hz m)
  rw [e, Measure.map_const, measure_univ, one_smul]

/-- **The domination inequality on `σ(⋃ₙ 𝒜ₙ)`** for the laws of the stop sequences:
`law(F.stopSeq r) ≤ Σ_j c_j law(slotSeq j a b)`. -/
theorem dominate_stopSeq (hD0 : 0 < D0) {z : Fin ((q + 1) + (q + 1)) → ℝ}
    {W : ℕ → Set (Fin ((q + 1) + (q + 1)) → ℝ)}
    (hW : ∀ n, IsInteriorDomain (W n) (flatChamber (q + 1))) (hmono : Monotone W) (hz : z ∈ W 0)
    (F : B1Family D0 (q + 1) z)
    (F₁ : ∀ j : Fin (q + 1), B1Family D0 1 (leftPart (z ∘ (slotEquiv j).symm)))
    (F₂ : ∀ j : Fin (q + 1), B1Family D0 q (rightPart (z ∘ (slotEquiv j).symm))) (t₀ : ℝ≥0) :
    ∃ R : ℕ → ℕ, ∀ r a b : ℕ → ℕ, Monotone r → Monotone a → Monotone b →
      (∀ n, R n ≤ r n ∧ R n ≤ a n ∧ R n ≤ b n) →
      (Pq (q + 1)).map (F.stopSeq W t₀ r) ≤
        ∑ j, ENNReal.ofReal (flatG j z / flatH (q + 1) z) •
          ((Pq 1).prod (Pq q)).map (slotSeq j (F₁ j) (F₂ j) W t₀ a b) := by
  have hz' : z ∈ flatChamber (q + 1) := (hW 0).2.2 (subset_closure hz)
  have hzn : ∀ n, z ∈ W n := fun n => hmono (Nat.zero_le n) hz
  obtain ⟨Ω, _, P, _, 𝓖, Z, hZ⟩ := exists_baseSol hD0 (q + 1) z (flatChamber_subset_flatO _ hz')
  choose Nb hNb using fun n => exists_ball_superset (hW n).2.1 (hW n).2.2
  choose W₁ W₂ hW₁ hW₂ hWW using fun n j => exists_factor_interiorDomains (hW n) j
  choose N₁ hN₁ using fun n j => exists_ball_superset (hW₁ n j).2.1 (hW₁ n j).2.2
  choose N₂ hN₂ using fun n j => exists_ball_superset (hW₂ n j).2.1 (hW₂ n j).2.2
  choose Nd hNd using fun n => exists_dominate_B1 hD0 hZ (hW n) (hzn n) F₁ F₂
  refine ⟨fun n => max (Nb n) (max (Finset.univ.sup (N₁ n)) (max (Finset.univ.sup (N₂ n))
    (Nd n))), fun r a b hr ha hb hR => ?_⟩
  have hNbr : ∀ n, Nb n ≤ r n := fun n => (le_max_left _ _).trans (hR n).1
  have hN₁a : ∀ n j, N₁ n j ≤ a n := fun n j => (Finset.le_sup (Finset.mem_univ j)).trans
    (((le_max_left _ _).trans (le_max_right _ _)).trans (hR n).2.1)
  have hN₂b : ∀ n j, N₂ n j ≤ b n := fun n j => (Finset.le_sup (Finset.mem_univ j)).trans
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (hR n).2.2)
  have hNda : ∀ n, Nd n ≤ a n := fun n =>
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (hR n).2.1
  have hNdb : ∀ n, Nd n ≤ b n := fun n =>
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (hR n).2.2
  have hballr : ∀ n, W n ⊆ chartQ (q + 1) '' Metric.ball 0 (r n) := fun n =>
    subset_closure.trans ((hNb n).trans (chartQ_ball_mono (hNbr n)))
  have hball : ∀ j n, ∀ w ∈ W n,
      leftPart (w ∘ (slotEquiv j).symm) ∈ chartQ 1 '' Metric.ball 0 (a n) ∧
      rightPart (w ∘ (slotEquiv j).symm) ∈ chartQ q '' Metric.ball 0 (b n) := fun j n w hw =>
    ⟨chartQ_ball_mono (hN₁a n j) ((hN₁ n j) (subset_closure (hWW n j w hw).1)),
      chartQ_ball_mono (hN₂b n j) ((hN₂ n j) (subset_closure (hWW n j w hw).2))⟩
  have hc : ∀ j, 0 ≤ flatG j z / flatH (q + 1) z := fun j =>
    div_nonneg (flatG_pos hz' j).le (cauchyH_pos hz').le
  refine map_le_of_stopSeq (fun n => (hW n).1) (F.measurable_stopSeq (fun n => (hW n).1) r)
    (fun j => measurable_slotSeq j (F₁ j) (F₂ j) (fun n => (hW n).1) a b)
    (F.isStopSeq_stopSeq hD0 (fun n => (hW n).1) hmono hr hballr)
    (fun j => isStopSeq_slotSeq hD0 j (F₁ j) (F₂ j) (fun n => (hW n).1) hmono ha hb (hball j))
    (fun j => ENNReal.ofReal_ne_top) fun n B hB => measure_le_sum_of_real hc ?_
  exact hNd n (a n) (b n) (hNda n) (hNdb n)
    (isMPSolutionOn_mono (F.isMPSolutionOn_Yf hD0 (r n)) (hballr n))
    (F.map_Yf_zero hz' (r n)) t₀ hB

end BlockBand.Transmission.Dual.G
