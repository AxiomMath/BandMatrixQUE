module

public import BlockBand.Transmission.LawDuality.KillMeas

/-!
# The real-time stopped processes of the killed identity, pathwise

* `ratioStop`: `Φ_s = F_{Z_{s⁺∧τ}}(ν)`;
* `genStop`: `G_u = 𝒟F(Z_{u⁺}) 1{u⁺ < τ} 1{u > 0}`;
* `killRate`, `killFac`, `killDer`: `K_s = exp(−∫_0^{s⁺} k(v)R_v 1{v<τ} dv)` and
  `K'_u = −k(u)R_u1{u<τ}K_u`.
Pathwise: continuity, `0 < K ≤ 1`, the FTC `K_b − K_a = ∫_a^b K'` (`killFac_sub_eq`), and the
link with the full-level martingale `fullMart`: `Φ_t − Φ_s − ∫_s^t G = M_{t⁺} − M_{s⁺}`
(`ratioStop_sub_eq_fullMart`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set intervalIntegral
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable {Ω : Type*}

theorem continuous_stopAt (τ : Ω → WithTop ℝ≥0) (ω : Ω) : Continuous fun r => stopAt τ r ω := by
  cases hτ : τ ω with
  | top =>
    have : (fun r => stopAt τ r ω) = fun r => r := funext fun r => by
      simp only [stopAt, hτ, min_top_right]; rfl
    rw [this]; exact continuous_id
  | coe c =>
    have : (fun r => stopAt τ r ω) = fun r => min r c := funext fun r => by
      simp only [stopAt, hτ]; rw [← WithTop.coe_min]; rfl
    rw [this]; exact continuous_id.min continuous_const

/-- `Φ_s = F_{Z_{s⁺∧τ}}(ν)`. -/
def ratioStop (ν : FiniteMeasure unitInterval) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ)
    (τ : Ω → WithTop ℝ≥0) (s : ℝ) (ω : Ω) : ℝ :=
  pathRatio ν N X Y (stopAt τ s.toNNReal ω) ω

/-- The rate path `v ↦ k(v)R_{v⁺}`. -/
def killRate (k : ℝ → ℝ) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (ω : Ω) (v : ℝ) : ℝ :=
  k v * dualTotal (N v.toNNReal ω) (X v.toNNReal ω) (Y v.toNNReal ω)

/-- `K_s = exp(−∫_0^{s⁺} k R 1{·<τ})`. -/
def killFac (k : ℝ → ℝ) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (τ : Ω → WithTop ℝ≥0)
    (s : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-killExp (killRate k N X Y ω) (τ ω) (max s 0))

/-- `K'_u = −k(u)R_u1{u<τ}K_u`. -/
def killDer (k : ℝ → ℝ) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (τ : Ω → WithTop ℝ≥0)
    (u : ℝ) (ω : Ω) : ℝ :=
  -(killRate k N X Y ω u * killInd (τ ω) u) * killFac k N X Y τ u ω

/-- `G_u = 𝒟F(Z_{u⁺})1{u⁺<τ}1{u>0}`. -/
def genStop (D0 : ℝ) (ν : FiniteMeasure unitInterval) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ)
    (τ : Ω → WithTop ℝ≥0) (u : ℝ) (ω : Ω) : ℝ :=
  pathGen D0 ν N X Y u.toNNReal ω * killInd (τ ω) u * (if 0 < u then 1 else 0)

variable {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ} {ω : Ω} {k : ℝ → ℝ}
  {τ : Ω → WithTop ℝ≥0}

section Path

variable (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
include hP

theorem continuous_killRate (hk : Continuous k) : Continuous (killRate k N X Y ω) :=
  hk.mul ((continuous_total hP).comp continuous_real_toNNReal)

theorem continuous_ratioStop (ν : FiniteMeasure unitInterval) :
    Continuous fun s => ratioStop ν N X Y τ s ω :=
  (continuous_ratioPath hP ν).comp ((continuous_stopAt τ ω).comp continuous_real_toNNReal)

theorem continuous_killFac (hk : Continuous k) : Continuous fun s => killFac k N X Y τ s ω :=
  Real.continuous_exp.comp
    ((continuous_killExp (continuous_killRate hP hk) _).comp (continuous_id.max continuous_const)).neg

theorem killFac_mem (hk0 : ∀ v, 0 ≤ k v) (s : ℝ) :
    0 < killFac k N X Y τ s ω ∧ killFac k N X Y τ s ω ≤ 1 := by
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.2 (neg_nonpos.2 ?_)⟩
  exact intervalIntegral.integral_nonneg (le_max_right s 0) fun u _ =>
    mul_nonneg (mul_nonneg (hk0 u) (dualTotal_nonneg hP _)) (killInd_mem _ _).1

/-- **FTC for `K`.** -/
theorem killFac_sub_eq (hk : Continuous k) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    killFac k N X Y τ b ω - killFac k N X Y τ a ω = ∫ u in a..b, killDer k N X Y τ u ω := by
  have h := killExp_sub_eq (continuous_killRate hP hk) (τ ω) hab
  simp only [killFac, max_eq_left ha, max_eq_left (ha.trans hab)]
  rw [h]
  refine integral_congr fun u hu => ?_
  rw [uIcc_of_le hab] at hu
  simp only [killDer, killFac, max_eq_left (ha.trans hu.1)]

end Path

theorem killFac_eq_integral (s : ℝ) : killFac k N X Y τ s ω =
    Real.exp (-∫ v in Ioc (0 : ℝ) (s.toNNReal : ℝ), (k (v.toNNReal : ℝ) *
      dualTotal (N v.toNNReal ω) (X v.toNNReal ω) (Y v.toNNReal ω) * stopInd τ v.toNNReal ω)) := by
  unfold killFac killExp
  rw [show max s 0 = (s.toNNReal : ℝ) from (Real.coe_toNNReal' s).symm,
    integral_of_le (s.toNNReal).coe_nonneg]
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
  simp only [killRate, Real.coe_toNNReal _ hv.1.le]
  rfl

theorem integral_genStop_eq (D0 : ℝ) (ν : FiniteMeasure unitInterval) (t : ℝ) :
    ∫ u in (0 : ℝ)..t, genStop D0 ν N X Y τ u ω =
      ∫ u in Ioc (0 : ℝ) (t.toNNReal : ℝ), pathGen D0 ν N X Y u.toNNReal ω *
        stopInd τ u.toNNReal ω := by
  rcases le_total 0 t with ht | ht
  · rw [integral_of_le ht, Real.coe_toNNReal _ ht]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    simp only [genStop, hu.1, ↓reduceIte, mul_one]
    rfl
  · rw [integral_symm, intervalIntegral.integral_of_le ht, Real.toNNReal_of_nonpos ht]
    simp only [NNReal.coe_zero, Ioc_self, Measure.restrict_empty, integral_zero_measure,
      neg_eq_zero]
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
    simp [genStop, not_lt.2 hu.2]

section Bounds

variable {p : ℕ} (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
  (hstart : ∀ ω, N 0 ω = p) {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1)
  (hU : StaysIn N X Y τ M ε)
include hpath hstart hM hε hε1 hU

theorem abs_pathGen_le (D0 : ℝ) (ν : FiniteMeasure unitInterval) (ω : Ω) {u : ℝ≥0}
    (hu : (u : WithTop ℝ≥0) ≤ τ ω) :
    |pathGen D0 ν N X Y u ω| ≤ ∑ j ∈ Finset.range p, genMass D0 (j + 1) M ε ν := by
  rw [pathGen_eq_sum hpath hstart ν u ω]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ =>
    abs_liftGen_le (hpath ω) D0 ν hM hε hε1 (hU ω u hu))

theorem abs_genStop_le (D0 : ℝ) (ν : FiniteMeasure unitInterval) (ω : Ω) (u : ℝ) :
    |genStop D0 ν N X Y τ u ω| ≤ ∑ j ∈ Finset.range p, genMass D0 (j + 1) M ε ν := by
  have hC : 0 ≤ ∑ j ∈ Finset.range p, genMass D0 (j + 1) M ε ν :=
    Finset.sum_nonneg fun j _ => genMass_nonneg _ _ _ _ _
  unfold genStop killInd
  split_ifs with h1 h2
  · simpa using abs_pathGen_le hpath hstart hM hε hε1 hU D0 ν ω h1.le
  · simpa using hC
  · simpa using hC
  · simpa using hC

omit hε1 in
theorem abs_killDer_le {Ck : ℝ} (hk0 : ∀ v, 0 ≤ k v) (hkC : ∀ v, k v ≤ Ck) (ω : Ω) (u : ℝ) :
    |killDer k N X Y τ u ω| ≤ Ck * (p * (M + 1)) := by
  have hK := killFac_mem (τ := τ) (hpath ω) hk0 u
  have hCk : 0 ≤ Ck := (hk0 0).trans (hkC 0)
  have hpM : 0 ≤ (p : ℝ) * (M + 1) := by positivity
  unfold killDer killInd
  split_ifs with h1
  · have hR : dualTotal (N u.toNNReal ω) (X u.toNNReal ω) (Y u.toNNReal ω) ≤ p * (M + 1) := by
      have hN : N u.toNNReal ω ≤ p := hstart ω ▸ (hpath ω).antitone zero_le
      calc dualTotal (N u.toNNReal ω) (X u.toNNReal ω) (Y u.toNNReal ω)
          ≤ ∑ _i ∈ Finset.range (N u.toNNReal ω), (M + 1) := Finset.sum_le_sum fun i hi => by
            obtain ⟨a, b⟩ := hU ω _ h1.le i (Finset.mem_range.1 hi)
            linarith
        _ = (N u.toNNReal ω : ℝ) * (M + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ p * (M + 1) := mul_le_mul_of_nonneg_right (by exact_mod_cast hN) (by linarith)
    have hR0 := dualTotal_nonneg (hpath ω) u.toNNReal
    simp only [killRate, mul_one, abs_mul, abs_neg, abs_of_pos hK.1,
      abs_of_nonneg (hk0 u), abs_of_nonneg hR0]
    calc k u * dualTotal (N u.toNNReal ω) (X u.toNNReal ω) (Y u.toNNReal ω) *
          killFac k N X Y τ u ω
        ≤ Ck * (p * (M + 1)) * 1 := mul_le_mul (mul_le_mul (hkC u) hR hR0 hCk) hK.2 hK.1.le
          (by positivity)
      _ = Ck * (p * (M + 1)) := mul_one _
  · simp only [mul_zero, neg_zero, zero_mul, abs_zero]; positivity

omit hM hε hε1 hU in
theorem measurable_genStop (D0 : ℝ) (ν : FiniteMeasure unitInterval) (ω : Ω) :
    Measurable fun u => genStop D0 ν N X Y τ u ω := by
  have hg : Measurable fun u : ℝ => pathGen D0 ν N X Y u.toNNReal ω := by
    simp_rw [pathGen_eq_sum hpath hstart ν _ ω]
    exact Finset.measurable_fun_sum _ fun j _ => measurable_liftGen_real (hpath ω) D0 ν
  exact (hg.mul (measurable_killInd _)).mul (Measurable.ite measurableSet_Ioi measurable_const
    measurable_const)

theorem intervalIntegrable_genStop (D0 : ℝ) (ν : FiniteMeasure unitInterval) (ω : Ω)
    (a b : ℝ) : IntervalIntegrable (fun u => genStop D0 ν N X Y τ u ω) volume a b :=
  (intervalIntegrable_const (c := ∑ j ∈ Finset.range p, genMass D0 (j + 1) M ε ν)).mono_fun
    (measurable_genStop hpath hstart D0 ν ω).aestronglyMeasurable
    (Eventually.of_forall fun u => by
      show ‖genStop D0 ν N X Y τ u ω‖ ≤ ‖∑ j ∈ Finset.range p, genMass D0 (j + 1) M ε ν‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact (abs_genStop_le hpath hstart hM hε hε1 hU D0 ν ω u).trans (le_abs_self _))

omit hpath hstart hM hε hε1 hU in
/-- The drift integral up to `r` with the strict stop equals the one up to `r ∧ τ`. -/
theorem integral_pathGen_stopInd_eq (D0 : ℝ) (ν : FiniteMeasure unitInterval) (ω : Ω)
    (r : ℝ≥0) :
    ∫ u in Ioc (0 : ℝ) r, pathGen D0 ν N X Y u.toNNReal ω * stopInd τ u.toNNReal ω =
      ∫ u in Ioc (0 : ℝ) (stopAt τ r ω), pathGen D0 ν N X Y u.toNNReal ω := by
  have hρr : (stopAt τ r ω : ℝ) ≤ r := NNReal.coe_le_coe.2 (stopAt_le τ r ω)
  have hae : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) r)),
      pathGen D0 ν N X Y u.toNNReal ω * stopInd τ u.toNNReal ω =
        (Ioc (0 : ℝ) (stopAt τ r ω)).indicator
          (fun u => pathGen D0 ν N X Y u.toNNReal ω) u := by
    have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ ((τ ω).untopA : ℝ) := by
      rw [ae_iff]; simp
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards [hne] with u hu hmem
    have hu0 : (u.toNNReal : ℝ) = u := Real.coe_toNNReal _ hmem.1.le
    have hiff : (u.toNNReal : WithTop ℝ≥0) < τ ω ↔ u ∈ Ioc (0 : ℝ) (stopAt τ r ω) := by
      have hρ := coe_stopAt τ r ω
      have hur : u.toNNReal ≤ r := by
        rw [← NNReal.coe_le_coe, hu0]; exact hmem.2
      constructor
      · intro h
        refine ⟨hmem.1, ?_⟩
        have : (u.toNNReal : WithTop ℝ≥0) ≤ stopAt τ r ω := by
          rw [hρ]; exact le_min (WithTop.coe_le_coe.2 hur) h.le
        rw [← hu0]; exact NNReal.coe_le_coe.2 (WithTop.coe_le_coe.1 this)
      · intro h
        have h2 : (u.toNNReal : WithTop ℝ≥0) ≤ τ ω := by
          refine le_trans (WithTop.coe_le_coe.2 ?_) (stopAt_le_tau τ r ω)
          rw [← NNReal.coe_le_coe, hu0]; exact h.2
        refine lt_of_le_of_ne h2 fun e => hu ?_
        rw [← e]; exact hu0.symm
    by_cases h : (u.toNNReal : WithTop ℝ≥0) < τ ω
    · rw [indicator_of_mem (hiff.1 h)]
      unfold stopInd
      split_ifs
      rw [mul_one]
    · rw [indicator_of_notMem (mt hiff.2 h)]
      unfold stopInd
      split_ifs
      rw [mul_zero]
  rw [setIntegral_congr_ae measurableSet_Ioc (by
      filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 hae] with u hu hmem
      exact hu hmem),
    setIntegral_indicator measurableSet_Ioc, inter_eq_right.2 (Ioc_subset_Ioc_right hρr)]

/-- **Link with `fullMart`**: `Φ_t − Φ_s − ∫_s^t G = M_{t⁺} − M_{s⁺}`. -/
theorem ratioStop_sub_eq_fullMart (D0 : ℝ) (ν : FiniteMeasure unitInterval) (ω : Ω) (s t : ℝ) :
    ratioStop ν N X Y τ t ω - ratioStop ν N X Y τ s ω -
        ∫ u in s..t, genStop D0 ν N X Y τ u ω =
      fullMart D0 ν N X Y τ t.toNNReal ω - fullMart D0 ν N X Y τ s.toNNReal ω := by
  rw [← integral_interval_sub_left (intervalIntegrable_genStop hpath hstart hM hε hε1 hU D0 ν ω 0 t)
    (intervalIntegrable_genStop hpath hstart hM hε hε1 hU D0 ν ω 0 s),
    integral_genStop_eq, integral_genStop_eq,
    integral_pathGen_stopInd_eq, integral_pathGen_stopInd_eq]
  simp only [fullMart, ratioStop]
  ring

end Bounds

end BlockBand.Transmission.LawDuality
