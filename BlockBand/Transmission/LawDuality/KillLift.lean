module

public import BlockBand.Transmission.LawDuality.RatioMass
public import BlockBand.Transmission.LawDuality.RatioPath
public import BlockBand.Transmission.Dual.TestProc

/-!
# The full-level ratio along a deletion path: values, generator, measurability

* `pathRatio_mem`: `0 < G ≤ 1`;
* `tendsto_lift_right_of_continuousAt`: `Dual.tendsto_lift_right` for a test that is only
  continuous at the points of `𝒞_q` (here `𝒟_qF_·(ν)`);
* **`measurable_liftGen`**: `u ↦ dualLift (𝒟_qF_·(ν)) (Z_u)` is measurable on `ℝ≥0` (it is
  right-continuous), and its real-time version `u ↦ … (Z_{u⁺})` on `ℝ`;
* `level_eq_of_le_hit`: before the exit `θ` of `{h > 1/2}` and after `σ_q < θ`, the level is
  `q` (this is the step "`key`" of `Dual.dualMartingale_eq_of_le_hit`, exported).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- `G(t) = F_{Z_t}(ν)`, at the current level. -/
def pathRatio {Ω : Type*} (ν : FiniteMeasure unitInterval) (N : ℝ≥0 → Ω → ℕ)
    (X Y : ℝ≥0 → Ω → ℕ → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ratioOn ν (dualCoordOf (N t ω) (X t ω) (Y t ω))

/-- `𝒟F_·(ν)(Z_t)`, at the current level (`0` at level `0`). -/
def pathGen {Ω : Type*} (D0 : ℝ) (ν : FiniteMeasure unitInterval) (N : ℝ≥0 → Ω → ℕ)
    (X Y : ℝ≥0 → Ω → ℕ → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  dualGenerator D0 (ratioOn ν) (dualCoordOf (N t ω) (X t ω) (Y t ω))

theorem dualLift_eq_of_eq {k q : ℕ} (hk : k = q) (f : ∀ m : ℕ, DualCoord m → ℝ)
    (a b : ℕ → ℝ) : dualLift (f q) k a b = f k (dualCoordOf k a b) := by
  subst hk; simp [dualLift]

theorem dualGenerator_zero (D0 : ℝ) (f : DualCoord 0 → ℝ) (z : DualCoord 0) :
    dualGenerator D0 f z = 0 := by
  simp [dualGenerator]

theorem ratioOn_mem {q : ℕ} {z : DualCoord q} (hz : z ∈ dualChamber q)
    (ν : FiniteMeasure unitInterval) : 0 < ratioOn ν z ∧ ratioOn ν z ≤ 1 :=
  transmissionRatio_mem_vec (IsRatioParameter.isRatioRange hz) ν

theorem continuousAt_dualGenerator_ratioOn_z (D0 : ℝ) {q : ℕ} {z : DualCoord q}
    (hz : z ∈ dualChamber q) (ν : FiniteMeasure unitInterval) :
    ContinuousAt (dualGenerator D0 (ratioOn ν)) z :=
  (continuousAt_dualGenerator_ratioOn D0 hz ν).comp (f := fun w : DualCoord q => (w, ν))
    (continuous_id.prodMk continuous_const).continuousAt

section PathLemmas

variable {n : ℝ≥0 → ℕ} {x y : ℝ≥0 → ℕ → ℝ} {q : ℕ}

theorem tendsto_lift_right_of_continuousAt (hP : IsDeletionPath n x y) {F : DualCoord q → ℝ}
    (hF : ∀ z ∈ dualChamber q, ContinuousAt F z) (t : ℝ≥0) :
    Tendsto (fun u => dualLift F (n u) (x u) (y u)) (𝓝[≥] t)
      (𝓝 (dualLift F (n t) (x t) (y t))) := by
  obtain ⟨b, hb, hlev⟩ := exists_right_level hP t
  have hev : ∀ᶠ u in 𝓝[≥] t, n u = n t := mem_of_superset (Ico_mem_nhdsGE hb) hlev
  by_cases h : n t = q
  · have hc : Tendsto (fun u => dualCoordOf q (x u) (y u)) (𝓝[≥] t)
        (𝓝 (dualCoordOf q (x t) (y t))) := by
      refine Tendsto.prodMk_nhds (tendsto_pi_nhds.2 fun i => ?_) (tendsto_pi_nhds.2 fun i => ?_)
      · exact (tendsto_coord_right hP t (by rw [h]; exact i.2)).1
      · exact (tendsto_coord_right hP t (by rw [h]; exact i.2)).2
    have hmem : dualCoordOf q (x t) (y t) ∈ dualChamber q := by
      have := hP.chamber t; rw [h] at this; exact this
    have e : dualLift F (n t) (x t) (y t) = F (dualCoordOf q (x t) (y t)) := by
      simp [dualLift, h]
    rw [e]
    refine ((hF _ hmem).tendsto.comp hc).congr' ?_
    filter_upwards [hev] with u hu
    simp [dualLift, hu, h]
  · have e : dualLift F (n t) (x t) (y t) = 0 := by simp [dualLift, h]
    rw [e]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with u hu
    simp [dualLift, hu, h]

/-- **Measurability of the lifted generator along a deletion path.** -/
theorem measurable_liftGen (hP : IsDeletionPath n x y) (D0 : ℝ) (ν : FiniteMeasure unitInterval) :
    Measurable fun u : ℝ≥0 =>
      dualLift (dualGenerator D0 (ratioOn ν : DualCoord q → ℝ)) (n u) (x u) (y u) :=
  measurable_of_tendsto_nhdsGE
    (tendsto_lift_right_of_continuousAt hP fun _ hz => continuousAt_dualGenerator_ratioOn_z D0 hz ν)

theorem measurable_liftGen_real (hP : IsDeletionPath n x y) (D0 : ℝ)
    (ν : FiniteMeasure unitInterval) :
    Measurable fun u : ℝ => dualLift (dualGenerator D0 (ratioOn ν : DualCoord q → ℝ))
      (n u.toNNReal) (x u.toNNReal) (y u.toNNReal) :=
  (measurable_liftGen hP D0 ν).comp measurable_real_toNNReal

theorem pathRatio_mem {Ω : Type*} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ} {ω : Ω}
    (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (ν : FiniteMeasure unitInterval) (t : ℝ≥0) :
    0 < pathRatio ν N X Y t ω ∧ pathRatio ν N X Y t ω ≤ 1 :=
  ratioOn_mem (hP.chamber t) ν

theorem abs_pathRatio_le {Ω : Type*} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ} {ω : Ω}
    (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (ν : FiniteMeasure unitInterval) (t : ℝ≥0) : |pathRatio ν N X Y t ω| ≤ 1 := by
  obtain ⟨h1, h2⟩ := pathRatio_mem hP ν t
  rw [abs_of_pos h1]; exact h2

/-- **The level is `q` between `σ_q` and the exit `θ` of `{h > 1/2}`.** -/
theorem level_eq_of_le_hit (hP : IsDeletionPath n x y) (hq : 1 ≤ q) {h : DualCoord q → ℝ}
    (hh : Continuous h) (hh0 : ∀ z ∉ dualChamber q, h z = 0) {θ : WithTop ℝ≥0}
    (hθ : ∀ u : ℝ≥0, (u : WithTop ℝ≥0) < θ → 1 / 2 < testVal q h (n u) (x u) (y u))
    {r : ℝ≥0} (hr : (r : WithTop ℝ≥0) ≤ θ) (hE : entryTime n q ≤ r) (hEθ : entryTime n q < θ) :
    n r = q := by
  have hle : n r ≤ q := (entryTime_le_iff hP q r).1 hE
  have hP12 : 1 / 2 ≤ testVal q h (n r) (x r) (y r) := by
    rcases lt_or_eq_of_le hr with hlt | heq
    · exact (hθ r hlt).le
    · have hne : entryTime n q ≠ r := by
        intro e; rw [e] at hEθ; exact hEθ.ne heq
      have hupos : 0 < r := by
        rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ r) with h0 | h0
        · exfalso; apply hne
          rw [← h0] at hE ⊢
          exact le_antisymm hE (by rw [WithTop.coe_zero]; exact zero_le)
        · exact h0
      have : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hupos⟩
      refine ge_of_tendsto (tendsto_testVal_left_of_ne hP hh hh0 hq hupos hne) ?_
      filter_upwards [self_mem_nhdsWithin] with v hv
      exact (hθ v (lt_of_lt_of_le (WithTop.coe_lt_coe.2 hv) heq.le)).le
  have hnot : ¬ q < n r := not_lt.2 hle
  simp only [testVal, hnot, ↓reduceIte, add_zero] at hP12
  by_contra hnr
  simp [dualLift, hnr] at hP12
  linarith

end PathLemmas

end BlockBand.Transmission.LawDuality
