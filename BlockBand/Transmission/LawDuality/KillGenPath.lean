module

public import BlockBand.Transmission.LawDuality.KillLift
public import BlockBand.Transmission.Dual.LevelPath

/-!
# The drift integral of `F` along a deletion path, inside `{x ≤ M, y ≤ 1 − ε}`

* `abs_liftGen_le`: `|dualLift (𝒟_qF_·(ν)) (Z_u)| ≤ C` while `x_i ≤ M`, `y_j ≤ 1 − ε`
  (`abs_dualGenerator_ratioOn_le_mass`, corners and collisions included);
* `abs_integral_liftGen_le`: `|∫_{(0,a]} …| ≤ C·a`;
* **`tendsto_integral_liftGen`**: as the cutoff exits `θ_k` grow (`θ_k ≤ σ_{q−1}` and
  eventually `t < θ_k` for `σ_q ≤ t < σ_{q−1}`), `∫_{(0,ρ∧θ_k]} … → ∫_{(0,ρ]} …`
  (dominated convergence; the integrand vanishes off level `q`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- The mass-linear generator bound `|D₀|/2·(6q+8q²)(1+M)²/ε²·ν[0,1]`. -/
def genMass (D0 : ℝ) (q : ℕ) (M ε : ℝ) (ν : FiniteMeasure unitInterval) : ℝ :=
  |D0| / 2 * ((6 * q + 8 * q ^ 2) * ((1 + M) ^ 2 / ε ^ 2)) * (ν : Measure unitInterval).real univ

theorem genMass_nonneg (D0 : ℝ) (q : ℕ) (M ε : ℝ) (ν : FiniteMeasure unitInterval) :
    0 ≤ genMass D0 q M ε ν := by
  unfold genMass
  have : 0 ≤ (ν : Measure unitInterval).real univ := measureReal_nonneg
  positivity

variable {n : ℝ≥0 → ℕ} {x y : ℝ≥0 → ℕ → ℝ} {q : ℕ}

theorem abs_liftGen_le (hP : IsDeletionPath n x y) (D0 : ℝ) (ν : FiniteMeasure unitInterval)
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1) {u : ℝ≥0}
    (hU : ∀ i, i < n u → x u i ≤ M ∧ y u i ≤ 1 - ε) :
    |dualLift (dualGenerator D0 (ratioOn ν : DualCoord q → ℝ)) (n u) (x u) (y u)| ≤
      genMass D0 q M ε ν := by
  by_cases h : n u = q
  · have hz : dualCoordOf q (x u) (y u) ∈ dualChamber q := by
      have := hP.chamber u; rw [h] at this; exact this
    simp only [dualLift, h, ↓reduceIte]
    exact abs_dualGenerator_ratioOn_le_mass ν D0 hM hε hε1 hz
      (fun (i : Fin q) => (hU (i : ℕ) (by rw [h]; exact i.2)).1)
      (fun (j : Fin q) => (hU (j : ℕ) (by rw [h]; exact j.2)).2)
  · simp only [dualLift, h, ↓reduceIte, abs_zero]
    exact genMass_nonneg D0 q M ε ν

theorem abs_integral_liftGen_le (hP : IsDeletionPath n x y) (D0 : ℝ)
    (ν : FiniteMeasure unitInterval) {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {a : ℝ≥0} (hU : ∀ u : ℝ≥0, u ≤ a → ∀ i, i < n u → x u i ≤ M ∧ y u i ≤ 1 - ε) :
    |∫ u in Ioc (0 : ℝ) a, dualLift (dualGenerator D0 (ratioOn ν : DualCoord q → ℝ))
        (n u.toNNReal) (x u.toNNReal) (y u.toNNReal)| ≤ genMass D0 q M ε ν * a := by
  rw [← Real.norm_eq_abs]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) a)
    (C := genMass D0 q M ε ν) (f := fun u : ℝ => dualLift
      (dualGenerator D0 (ratioOn ν : DualCoord q → ℝ)) (n u.toNNReal) (x u.toNNReal)
      (y u.toNNReal)) measure_Ioc_lt_top fun u hu => by
    rw [Real.norm_eq_abs]
    refine abs_liftGen_le hP D0 ν hM hε hε1 (hU _ ?_)
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1.le]; exact hu.2
  refine h.trans (le_of_eq ?_)
  rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by simp), sub_zero]

/-- **The drift integral up to the cutoff exits converges to the one up to `ρ`.** -/
theorem tendsto_integral_liftGen (hP : IsDeletionPath n x y) (D0 : ℝ)
    (ν : FiniteMeasure unitInterval) {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hq : 1 ≤ q) (rho : ℝ≥0)
    (hU : ∀ u : ℝ≥0, u ≤ rho → ∀ i, i < n u → x u i ≤ M ∧ y u i ≤ 1 - ε)
    (θ : ℕ → WithTop ℝ≥0)
    (hc : ∀ t : ℝ≥0, entryTime n q ≤ t → (t : WithTop ℝ≥0) < entryTime n (q - 1) →
      ∀ᶠ k in atTop, (t : WithTop ℝ≥0) < θ k) :
    Tendsto (fun k => ∫ u in Ioc (0 : ℝ) (min (rho : WithTop ℝ≥0) (θ k)).untopA,
        dualLift (dualGenerator D0 (ratioOn ν : DualCoord q → ℝ))
          (n u.toNNReal) (x u.toNNReal) (y u.toNNReal)) atTop
      (𝓝 (∫ u in Ioc (0 : ℝ) rho, dualLift (dualGenerator D0 (ratioOn ν : DualCoord q → ℝ))
          (n u.toNNReal) (x u.toNNReal) (y u.toNNReal))) := by
  set f : ℝ → ℝ := fun u => dualLift (dualGenerator D0 (ratioOn ν : DualCoord q → ℝ))
    (n u.toNNReal) (x u.toNNReal) (y u.toNNReal) with hfdef
  have hfm : Measurable f := measurable_liftGen_real hP D0 ν
  set r' : ℕ → ℝ≥0 := fun k => (min (rho : WithTop ℝ≥0) (θ k)).untopA with hr'
  have hr'le : ∀ k, r' k ≤ rho := fun k => by
    have hfin : min (rho : WithTop ℝ≥0) (θ k) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    have := min_le_left (rho : WithTop ℝ≥0) (θ k)
    rw [← coe_untopA_of_ne_top hfin] at this
    exact WithTop.coe_le_coe.1 this
  have e : ∀ k, ∫ u in Ioc (0 : ℝ) (r' k), f u =
      ∫ u in Ioc (0 : ℝ) rho, (Ioc (0 : ℝ) (r' k)).indicator f u := by
    intro k
    rw [setIntegral_indicator measurableSet_Ioc]
    congr 1
    rw [inter_eq_right.2 (Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 (hr'le k)))]
  show Tendsto (fun k => ∫ u in Ioc (0 : ℝ) (r' k), f u) atTop
    (𝓝 (∫ u in Ioc (0 : ℝ) rho, f u))
  rw [show (fun k => ∫ u in Ioc (0 : ℝ) (r' k), f u) = fun k =>
    ∫ u in Ioc (0 : ℝ) rho, (Ioc (0 : ℝ) (r' k)).indicator f u from funext e]
  have hbd : ∀ u ∈ Ioc (0 : ℝ) rho, ‖f u‖ ≤ genMass D0 q M ε ν := fun u hu => by
    rw [Real.norm_eq_abs]
    refine abs_liftGen_le hP D0 ν hM hε hε1 (hU _ ?_)
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1.le]; exact hu.2
  refine tendsto_integral_of_dominated_convergence (fun _ => genMass D0 q M ε ν)
    (fun k => (hfm.indicator measurableSet_Ioc).aestronglyMeasurable) (integrable_const _)
    (fun k => ?_) ?_
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
    by_cases hk : u ∈ Ioc (0 : ℝ) (r' k)
    · rw [indicator_of_mem hk]; exact hbd u hu
    · rw [indicator_of_notMem hk, norm_zero]; exact genMass_nonneg D0 q M ε ν
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
    by_cases hf0 : f u = 0
    · refine tendsto_const_nhds.congr fun k => ?_
      by_cases hk : u ∈ Ioc (0 : ℝ) (r' k)
      · rw [indicator_of_mem hk, hf0]
      · rw [indicator_of_notMem hk, hf0]
    · have hnq : n u.toNNReal = q := by
        by_contra hne; exact hf0 (by simp [hfdef, dualLift, hne])
      have h1 : entryTime n q ≤ u.toNNReal := (entryTime_le_iff hP q _).2 hnq.le
      have h2 : (u.toNNReal : WithTop ℝ≥0) < entryTime n (q - 1) := by
        by_contra hc'
        have := (entryTime_le_iff hP (q - 1) _).1 (not_lt.1 hc')
        omega
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hc _ h1 h2] with k hk
      have hur : u ≤ r' k := by
        have hfin : min (rho : WithTop ℝ≥0) (θ k) ≠ ⊤ :=
          ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
        have hle : (u.toNNReal : WithTop ℝ≥0) ≤ min (rho : WithTop ℝ≥0) (θ k) := by
          refine le_min ?_ hk.le
          refine WithTop.coe_le_coe.2 ?_
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1.le]; exact hu.2
        rw [← coe_untopA_of_ne_top hfin] at hle
        have := NNReal.coe_le_coe.2 (WithTop.coe_le_coe.1 hle)
        rwa [Real.coe_toNNReal _ hu.1.le] at this
      rw [indicator_of_mem (show u ∈ Ioc (0 : ℝ) (r' k) from ⟨hu.1, hur⟩)]

end BlockBand.Transmission.LawDuality
