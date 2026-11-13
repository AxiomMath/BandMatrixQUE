module

public import BlockBand.Transmission.LawDuality.KillLevelMart

/-!
# The full-level ratio martingale, stopped at `τ`

`M_r = G(ρ) − ∫_{(0,ρ]} 𝒟F(Z_u) du` (`fullMart`).

* `fullMart_eq_sum` (telescoping, pathwise): `M_r = G(0) + Σ_{q=1}^p L^q_r`, using
  `σ_p = 0`, `G(ρ ∧ σ_0) = G(ρ)` (`F = 1` at level `0`) and `Σ_q 𝒟_qF·1{N=q} = 𝒟F`
  (`𝒟F = 0` at level `0`).
* **`integral_mul_fullMart_sub_eq_zero`**: for a normalized dual realization, a stopping
  time `τ` with `StaysIn N X Y τ M ε`, `s ≤ t` and bounded `𝓖_s`-measurable `A`,
  `E[A (M_t − M_s)] = 0`. This is the martingale input of the proof of `RatioDualityPrinciple`.
* `abs_fullMart_sub_le`, `aestronglyMeasurable_fullMart_sub`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

section Defs

variable {Ω : Type*}

/-- **The full-level stopped ratio martingale** `G(ρ) − ∫_{(0,ρ]} 𝒟F(Z_u) du`, `ρ = r ∧ τ`. -/
def fullMart (D0 : ℝ) (ν : FiniteMeasure unitInterval) (N : ℝ≥0 → Ω → ℕ)
    (X Y : ℝ≥0 → Ω → ℕ → ℝ) (τ : Ω → WithTop ℝ≥0) (r : ℝ≥0) (ω : Ω) : ℝ :=
  pathRatio ν N X Y (stopAt τ r ω) ω -
    ∫ u in Ioc (0 : ℝ) (stopAt τ r ω), pathGen D0 ν N X Y u.toNNReal ω

theorem ratioOn_level_zero (ν : FiniteMeasure unitInterval) (z : DualCoord 0) :
    ratioOn ν z = 1 := by
  simp [ratioOn, transmissionRatio, ratioIntegrand]

theorem sum_dualLift_eq {p k : ℕ} (hk : k ≤ p) (f : ∀ m : ℕ, DualCoord m → ℝ)
    (hf0 : ∀ z : DualCoord 0, f 0 z = 0) (a b : ℕ → ℝ) :
    ∑ j ∈ Finset.range p, dualLift (f (j + 1)) k a b = f k (dualCoordOf k a b) := by
  rcases k with _ | k
  · rw [hf0]
    exact Finset.sum_eq_zero fun j _ => by simp [dualLift]
  · rw [Finset.sum_eq_single k (fun j _ hj => by simp [dualLift, Ne.symm hj])
      (fun hk' => absurd (Finset.mem_range.2 (by omega)) hk')]
    simp [dualLift]

variable {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

theorem integrableOn_liftGen {ω : Ω}
    (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)) (D0 : ℝ)
    (ν : FiniteMeasure unitInterval) {τ : Ω → WithTop ℝ≥0} {M ε : ℝ} (hM : 0 ≤ M)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hU : StaysIn N X Y τ M ε) (q : ℕ) (r : ℝ≥0) :
    IntegrableOn (fun u : ℝ => dualLift (dualGenerator D0 (ratioOn ν : DualCoord q → ℝ))
      (N u.toNNReal ω) (X u.toNNReal ω) (Y u.toNNReal ω)) (Ioc (0 : ℝ) (stopAt τ r ω)) := by
  refine Measure.integrableOn_of_bounded (M := genMass D0 q M ε ν) measure_Ioc_lt_top.ne
    (measurable_liftGen_real hP D0 ν).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_))
  rw [Real.norm_eq_abs]
  refine abs_liftGen_le hP D0 ν hM hε hε1 (hU ω _ ((WithTop.coe_le_coe.2 ?_).trans
    (stopAt_le_tau τ r ω)))
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1.le]; exact hu.2

/-- **Telescoping over the levels.** -/
theorem fullMart_eq_sum {p : ℕ} {ω : Ω}
    (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (hstart : N 0 ω = p) (D0 : ℝ) (ν : FiniteMeasure unitInterval) {τ : Ω → WithTop ℝ≥0}
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1) (hU : StaysIn N X Y τ M ε) (r : ℝ≥0) :
    fullMart D0 ν N X Y τ r ω = pathRatio ν N X Y 0 ω +
      ∑ j ∈ Finset.range p, levelMart D0 ν N X Y τ (j + 1) r ω := by
  set n : ℝ≥0 → ℕ := fun t => N t ω with hn
  set ρ := stopAt τ r ω with hρ
  set G : ℕ → ℝ := fun j =>
    pathRatio ν N X Y (min (ρ : WithTop ℝ≥0) (entryTime n j)).untopA ω with hG
  have hsplit : ∀ j, levelMart D0 ν N X Y τ (j + 1) r ω = (G j - G (j + 1)) -
      ∫ u in Ioc (0 : ℝ) ρ, dualLift (dualGenerator D0 (ratioOn ν : DualCoord (j + 1) → ℝ))
        (N u.toNNReal ω) (X u.toNNReal ω) (Y u.toNNReal ω) := fun j => by
    simp only [levelMart, hG, Nat.add_sub_cancel, hn, hρ]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub' G p,
    ← integral_finsetSum _ fun j _ => integrableOn_liftGen hP D0 ν hM hε hε1 hU (j + 1) r]
  have hint : ∫ u in Ioc (0 : ℝ) ρ, pathGen D0 ν N X Y u.toNNReal ω =
      ∫ u in Ioc (0 : ℝ) ρ, ∑ j ∈ Finset.range p,
        dualLift (dualGenerator D0 (ratioOn ν : DualCoord (j + 1) → ℝ))
          (N u.toNNReal ω) (X u.toNNReal ω) (Y u.toNNReal ω) := by
    congr 1; funext u
    have hk : N u.toNNReal ω ≤ p := hstart ▸ hP.antitone zero_le
    rw [sum_dualLift_eq hk (fun m => dualGenerator D0 (ratioOn ν : DualCoord m → ℝ))
      (fun z => dualGenerator_zero D0 _ z)]
    rfl
  -- `σ_p = 0` and `G(ρ ∧ σ_0) = G(ρ)`
  have hGp : G p = pathRatio ν N X Y 0 ω := by
    have h0 : entryTime n p = ((0 : ℝ≥0) : WithTop ℝ≥0) :=
      le_antisymm ((entryTime_le_iff hP p 0).2 hstart.le)
        (by rw [WithTop.coe_zero]; exact zero_le)
    simp only [hG, h0, min_eq_right (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ ρ from
      WithTop.coe_le_coe.2 zero_le)]
    rfl
  have hG0 : G 0 = pathRatio ν N X Y ρ ω := by
    by_cases hz : entryTime n 0 ≤ ρ
    · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hz)
      have hns : n s = 0 := level_at_entry hP (Nat.zero_le _) hs.symm
      have hsρ : s ≤ ρ := WithTop.coe_le_coe.1 (hs ▸ hz)
      have hnρ : n ρ = 0 := Nat.le_zero.1 (hns ▸ hP.antitone hsρ)
      have hmin : (min (ρ : WithTop ℝ≥0) (entryTime n 0)).untopA = s := by
        rw [← hs, min_eq_right (WithTop.coe_le_coe.2 hsρ)]; rfl
      simp only [hG, hmin]
      show ratioOn ν (dualCoordOf (n s) (X s ω) (Y s ω)) =
        ratioOn ν (dualCoordOf (n ρ) (X ρ ω) (Y ρ ω))
      have e : ∀ (k : ℕ) (a b : ℕ → ℝ), k = 0 → ratioOn ν (dualCoordOf k a b) = 1 := by
        intro k a b hk; subst hk; exact ratioOn_level_zero ν _
      rw [e _ _ _ hns, e _ _ _ hnρ]
    · simp only [hG, min_eq_left (le_of_not_ge hz)]
      rfl
  rw [hGp, hG0, ← hint]
  simp only [fullMart, hρ]
  ring

end Defs

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 m} {D0 : ℝ} {p : ℕ} {x y : Fin p → ℝ}
  {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

omit m in
theorem fullMart_sub_eq_sum
    (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (hstart : ∀ ω, N 0 ω = p) (ν : FiniteMeasure unitInterval) {τ : Ω → WithTop ℝ≥0}
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1) (hU : StaysIn N X Y τ M ε) (s t : ℝ≥0)
    (ω : Ω) : fullMart D0 ν N X Y τ t ω - fullMart D0 ν N X Y τ s ω =
      ∑ j ∈ Finset.range p, (levelMart D0 ν N X Y τ (j + 1) t ω -
        levelMart D0 ν N X Y τ (j + 1) s ω) := by
  rw [fullMart_eq_sum (hpath ω) (hstart ω) D0 ν hM hε hε1 hU,
    fullMart_eq_sum (hpath ω) (hstart ω) D0 ν hM hε hε1 hU, Finset.sum_sub_distrib]
  ring

omit m in
theorem abs_fullMart_sub_le
    (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (hstart : ∀ ω, N 0 ω = p) (ν : FiniteMeasure unitInterval) {τ : Ω → WithTop ℝ≥0}
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1) (hU : StaysIn N X Y τ M ε) (s t : ℝ≥0)
    (ω : Ω) : |fullMart D0 ν N X Y τ t ω - fullMart D0 ν N X Y τ s ω| ≤
      ∑ j ∈ Finset.range p, ((2 + genMass D0 (j + 1) M ε ν * t) +
        (2 + genMass D0 (j + 1) M ε ν * s)) := by
  rw [fullMart_sub_eq_sum hpath hstart ν hM hε hε1 hU]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  exact (abs_sub _ _).trans (add_le_add
    (abs_levelMart_le (hpath ω) D0 ν hM hε hε1 hU _ t)
    (abs_levelMart_le (hpath ω) D0 ν hM hε hε1 hU _ s))

theorem aestronglyMeasurable_fullMart_sub (h : IsDualDeletionProcess P 𝓖 D0 x y N X Y)
    (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (hstart : ∀ ω, N 0 ω = p) (ν : FiniteMeasure unitInterval) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓖 τ) {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hU : StaysIn N X Y τ M ε) (s t : ℝ≥0) :
    AEStronglyMeasurable
      (fun ω => fullMart D0 ν N X Y τ t ω - fullMart D0 ν N X Y τ s ω) P := by
  have e : (fun ω => fullMart D0 ν N X Y τ t ω - fullMart D0 ν N X Y τ s ω) =
      fun ω => ∑ j ∈ Finset.range p, (levelMart D0 ν N X Y τ (j + 1) t ω -
        levelMart D0 ν N X Y τ (j + 1) s ω) :=
    funext (fullMart_sub_eq_sum hpath hstart ν hM hε hε1 hU s t)
  rw [e]
  refine Finset.aestronglyMeasurable_fun_sum _ fun j hj => ?_
  have hjp : j + 1 ≤ p := Finset.mem_range.1 hj
  exact (aestronglyMeasurable_levelMart h hpath hstart ν hτ hM hε hε1 hU (by omega) hjp t).sub
    (aestronglyMeasurable_levelMart h hpath hstart ν hτ hM hε hε1 hU (by omega) hjp s)

/-- **Orthogonality of the increments of the full-level stopped martingale.** -/
theorem integral_mul_fullMart_sub_eq_zero (h : IsDualDeletionProcess P 𝓖 D0 x y N X Y)
    (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (hstart : ∀ ω, N 0 ω = p) (ν : FiniteMeasure unitInterval) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓖 τ) {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hU : StaysIn N X Y τ M ε) {s t : ℝ≥0} (hst : s ≤ t)
    {A : Ω → ℝ} (hA : StronglyMeasurable[𝓖 s] A) {CA : ℝ} (hAb : ∀ ω, |A ω| ≤ CA) :
    ∫ ω, A ω * (fullMart D0 ν N X Y τ t ω - fullMart D0 ν N X Y τ s ω) ∂P = 0 := by
  have hAm : AEStronglyMeasurable A P := (hA.mono (𝓖.le s)).aestronglyMeasurable
  simp_rw [fullMart_sub_eq_sum hpath hstart ν hM hε hε1 hU s t, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero fun j hj => ?_
    have hjp : j + 1 ≤ p := Finset.mem_range.1 hj
    exact integral_mul_levelMart_sub_eq_zero h hpath hstart ν hτ hM hε hε1 hU (by omega) hjp
      hst hA hAb
  · intro j hj
    have hjp : j + 1 ≤ p := Finset.mem_range.1 hj
    refine Integrable.of_bound (hAm.mul
      ((aestronglyMeasurable_levelMart h hpath hstart ν hτ hM hε hε1 hU (by omega) hjp t).sub
        (aestronglyMeasurable_levelMart h hpath hstart ν hτ hM hε hε1 hU (by omega) hjp s)))
      (CA * ((2 + genMass D0 (j + 1) M ε ν * t) + (2 + genMass D0 (j + 1) M ε ν * s)))
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hAb ω) ((abs_sub _ _).trans (add_le_add
      (abs_levelMart_le (hpath ω) D0 ν hM hε hε1 hU _ t)
      (abs_levelMart_le (hpath ω) D0 ν hM hε hε1 hU _ s))) (abs_nonneg _)
      ((abs_nonneg _).trans (hAb ω))

end BlockBand.Transmission.LawDuality
