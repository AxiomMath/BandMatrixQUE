module

public import BlockBand.Transmission.DualEntrance.LiftEntrance
public import BlockBand.Transmission.DualFeller.Interface
public import BlockBand.Transmission.DualBoundary.Transfer

/-!
# The lift's realizations and its `dualTransform` integrand

Setting: the driver space `LΩ S` (any `S`, any probability `μ`) with the lifted
families; deterministic starts `sectionStart x y` on `LΩ Unit` for (a); any boundary
realization for the integrand facts. Norms: sup norm on `ℝ²`.

* (a) **`isBoundaryDualProcess_lift`**, **`isDualDeletionProcess_lift`**: *every* lifted
  family from `σ(x, y)` gives an `IsBoundaryDualProcess` (boundary start) resp.
  `IsDualDeletionProcess` (interior start) through `(N₂, X₂, Y₂)`.
* (b) **`dualTotal_lift`**: `R_s = Z̄_s⁰ + Z̄_s¹` with `Z̄ = liftZbar F`, at every `ω`.
* (c) `absorptionRate_nonneg`, `absorptionRate_le`; **`ae_dualTotal_nonneg`** (`R ≥ 0` a.s. for
  every boundary realization from `x, y ≥ 0`); `dualIntegrand` (the integrand of
  `dualTransform`), `dualIntegrand_mem` (values in `[0,1]`), `aestronglyMeasurable_dualIntegrand`,
  `integrable_dualIntegrand`; `abs_exp_neg_sub_le`.
* (d) `le_toNNReal_iff_untopA` (`ζ ≤ u ↔ ζ ∧ T ≤ u` for `0 ≤ u < T`);
  **`ae_dualExtinction_lift_iff`** (`dualExtinction N₂ ≤ t ↔ F.zeta ≤ t`, a.s.).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.DualLift BlockBand.Transmission.DualFeller
open scoped NNReal ENNReal

/-!
## (a) Realizations from a given family
-/

section Realize

variable {D0 : ℝ}

/-- **(a) Every family from a boundary start is a boundary realization**
(`IsBoundaryDualProcess`). -/
theorem isBoundaryDualProcess_lift (hD0 : 0 < D0) {x y : ℝ} (hxy : IsDualStart ![x] ![y])
    (F : LiftFamily (Measure.dirac ()) D0 (sectionStart x y)) :
    IsBoundaryDualProcess (LP (Measure.dirac ())) (L𝓖 (Measure.dirac ())) D0 ![x] ![y]
      F.N₂ F.X₂ F.Y₂ := by
  have hx : 0 ≤ x := hxy.2.2.1 0
  have hy := hxy.2.2.2.1 0
  have hs : 0 < x + y := hxy.2.2.2.2 0 0
  have hξ := isLiftStart_section hx hy.1 hy.2 hs
  exact
    { prob := inferInstance
      adapted := F.adapted₂ hD0 hξ
      start := Eventually.of_forall fun ω => ⟨F.N₂_zero ω, fun i => start_values F hx ω i⟩
      paths := by
        filter_upwards [F.ae_good₂ hD0 hξ,
          DualEntrance.liftEntrance_holds hD0 Unit (Measure.dirac ()) _ hξ F] with ω h1 h2
        exact F.isBoundaryDeletionPath_N₂ hξ h1 h2
      martingale := fun q hq hq1 f hf hfc hfs => by
        obtain rfl : q = 1 := le_antisymm hq1 hq
        exact F.martingale_dualMartingale₂ hD0 hξ hf hfc hfs }

/-- **(a) Every family from an interior start is a deletion process** (`IsDualDeletionProcess`). -/
theorem isDualDeletionProcess_lift (hD0 : 0 < D0) {x y : ℝ} (hxy : IsRatioParameter ![x] ![y])
    (F : LiftFamily (Measure.dirac ()) D0 (sectionStart x y)) :
    IsDualDeletionProcess (LP (Measure.dirac ())) (L𝓖 (Measure.dirac ())) D0 ![x] ![y]
      F.N₂ F.X₂ F.Y₂ := by
  have hx : 0 ≤ x := (hxy.2.2.1 0).le
  have hy := hxy.2.2.2 0
  have hξ := isLiftStart_section hx hy.1.le hy.2.le (by simp at hy ⊢; linarith [hxy.2.2.1 0])
  have h0 : ∀ ω, liftProj (sectionStart x y ω) ∈ Dual.flatChamber 1 := fun ω => by
    rw [sectionStart, liftProj_liftSection hx]
    simpa using Dual.Exists.flat_mem_of_ratio hxy
  exact
    { prob := inferInstance
      adapted := F.adapted₂ hD0 hξ
      start := Eventually.of_forall fun ω => ⟨F.N₂_zero ω, fun i => start_values F hx ω i⟩
      paths := by
        filter_upwards [F.ae_good₂ hD0 hξ,
          DualEntrance.liftEntrance_holds hD0 Unit (Measure.dirac ()) _ hξ F] with ω h1 h2
        exact F.isDeletionPath_N₂ hξ h1 h2 (h0 ω)
      martingale := fun q hq hq1 f hf hfc hfs => by
        obtain rfl : q = 1 := le_antisymm hq1 hq
        exact F.martingale_dualMartingale₂ hD0 hξ hf hfc hfs }

/-- Interior starts are boundary starts. -/
theorem isDualStart_of_ratio {x y : ℝ} (hxy : IsRatioParameter ![x] ![y]) :
    IsDualStart ![x] ![y] := by
  have hx := hxy.2.2.1 0
  have hy := hxy.2.2.2 0
  simp only [Matrix.cons_val_fin_one] at hx hy
  refine ⟨Subsingleton.strictMono _, Subsingleton.strictMono _, fun i => ?_, fun i => ?_,
    fun i j => ?_⟩ <;> simp only [Matrix.cons_val_fin_one]
  · exact hx.le
  · exact ⟨hy.1.le, hy.2.le⟩
  · linarith [hy.1]

end Realize

/-!
## (b) The total coordinate of the lift
-/

/-- **(b) `R_s = Z̄_s⁰ + Z̄_s¹`** for the lifted realization, at every `ω`. -/
theorem dualTotal_lift {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S}
    [IsProbabilityMeasure μ] {ξ : LΩ S → Fin 6 → ℝ} (F : LiftFamily μ D0 ξ) (s : ℝ≥0)
    (ω : LΩ S) :
    dualTotal (F.N₂ s ω) (F.X₂ s ω) (F.Y₂ s ω) = liftZbar F s ω 0 + liftZbar F s ω 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (F.N₂_le_one s ω) with h | h <;>
    simp [dualTotal, liftZbar, h, LiftFamily.X₂, LiftFamily.Y₂]

/-!
## (c) The integrand: nonnegative rate, values in `[0,1]`, measurability
-/

theorem absorptionRate_nonneg {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) (E s : ℝ) :
    0 ≤ absorptionRate E κ s := by
  have := hκ.2.1 s
  unfold absorptionRate Parameters.semicircleDensity
  positivity

/-- The rate bound `H = 4πρ(E)·max K 0`. -/
def rateBound (E K : ℝ) : ℝ := 4 * Real.pi * Parameters.semicircleDensity E * max K 0

theorem rateBound_nonneg (E K : ℝ) : 0 ≤ rateBound E K := by
  unfold rateBound Parameters.semicircleDensity; positivity

theorem absorptionRate_le {κ : ℝ → ℝ} {K : ℝ} (hK : ∀ s, κ s ≤ K) (E s : ℝ) :
    absorptionRate E κ s ≤ rateBound E K := by
  unfold absorptionRate rateBound
  have h0 : 0 ≤ 4 * Real.pi * Parameters.semicircleDensity E := by
    unfold Parameters.semicircleDensity; positivity
  exact mul_le_mul_of_nonneg_left ((hK s).trans (le_max_left _ _)) h0

/-- The integral `I_t = ∫_0^t h(t−s) R_s ds` of the `dualTransform`. -/
def dualIntegral {Ω : Type*} (E : ℝ) (κ : ℝ → ℝ) (t : ℝ) (N : ℝ≥0 → Ω → ℕ)
    (X Y : ℝ≥0 → Ω → ℕ → ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..t,
    absorptionRate E κ (t - s) * dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω)

/-- The integrand `1{ζ ≤ t} e^{−I_t}` of the `dualTransform`. -/
def dualIntegrand {Ω : Type*} (E : ℝ) (κ : ℝ → ℝ) (t : ℝ) (N : ℝ≥0 → Ω → ℕ)
    (X Y : ℝ≥0 → Ω → ℕ → ℝ) (ω : Ω) : ℝ :=
  if dualExtinction N ω ≤ ENNReal.ofReal t then Real.exp (-dualIntegral E κ t N X Y ω) else 0

theorem dualTransform_eq_integral {Ω : Type*} [MeasurableSpace Ω] (E : ℝ) (κ : ℝ → ℝ) (t : ℝ)
    (P : Measure Ω) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) :
    dualTransform E κ t P N X Y = ∫ ω, dualIntegrand E κ t N X Y ω ∂P := rfl

section Integrand

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 m} {D0 : ℝ}
  {x y : ℝ} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

/-- **`R ≥ 0` a.s.** for every boundary realization from `x, y ≥ 0`. -/
theorem ae_dualTotal_nonneg (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) (hx : 0 ≤ x)
    (hy : 0 ≤ y) : ∀ᵐ ω ∂P, ∀ s, 0 ≤ dualTotal (N s ω) (X s ω) (Y s ω) := by
  filter_upwards [h.start, h.paths] with ω h0 hp s
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs | hs
  · subst hs
    have e1 : X 0 ω 0 = x := by simpa using (h0.2 0).1
    have e2 : Y 0 ω 0 = y := by simpa using (h0.2 0).2
    simp only [dualTotal, h0.1, Nat.succ_eq_add_one, zero_add, Finset.range_one,
      Finset.sum_singleton, e1, e2]
    linarith
  · have hc := hp.chamber s hs
    refine Finset.sum_nonneg fun i hi => ?_
    have hi' : i < N s ω := Finset.mem_range.1 hi
    have h1 := hc.2.2.1 ⟨i, hi'⟩
    have h2 := (hc.2.2.2 ⟨i, hi'⟩).1
    simp only [dualCoordOf] at h1 h2
    linarith

theorem dualIntegral_nonneg {E : ℝ} {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) {t : ℝ}
    (ht : 0 ≤ t) {ω : Ω} (hR : ∀ s, 0 ≤ dualTotal (N s ω) (X s ω) (Y s ω)) :
    0 ≤ dualIntegral E κ t N X Y ω :=
  intervalIntegral.integral_nonneg ht fun _ _ =>
    mul_nonneg (absorptionRate_nonneg hκ E _) (hR _)

theorem dualIntegrand_mem {E : ℝ} {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) {t : ℝ}
    (ht : 0 ≤ t) {ω : Ω} (hR : ∀ s, 0 ≤ dualTotal (N s ω) (X s ω) (Y s ω)) :
    0 ≤ dualIntegrand E κ t N X Y ω ∧ dualIntegrand E κ t N X Y ω ≤ 1 := by
  unfold dualIntegrand
  split_ifs
  · exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (neg_nonpos.2 (dualIntegral_nonneg hκ ht hR))⟩
  · exact ⟨le_rfl, zero_le_one⟩

theorem ae_norm_dualIntegrand_le (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) (hx : 0 ≤ x)
    (hy : 0 ≤ y) {E : ℝ} {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ‖dualIntegrand E κ t N X Y ω‖ ≤ 1 := by
  filter_upwards [ae_dualTotal_nonneg h hx hy] with ω hR
  have := dualIntegrand_mem (E := E) hκ ht hR
  rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2

theorem aestronglyMeasurable_dualIntegrand (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y)
    (E : ℝ) {κ : ℝ → ℝ} (hκ : Continuous κ) {t : ℝ} (ht : 0 ≤ t) :
    AEStronglyMeasurable (dualIntegrand E κ t N X Y) P := by
  have hc : Measurable fun s => absorptionRate E κ (t - s) :=
    (continuous_const.mul (hκ.comp (continuous_const.sub continuous_id))).measurable
  exact ((measurable_transformG hc t).comp (measurable_truncDualState h)).aestronglyMeasurable.congr
    (transform_ae_eq E hκ ht h).symm

theorem integrable_dualIntegrand (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) (hx : 0 ≤ x)
    (hy : 0 ≤ y) {E : ℝ} {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (dualIntegrand E κ t N X Y) P := by
  have := h.prob
  exact Integrable.of_bound (aestronglyMeasurable_dualIntegrand h E hκ.1 ht) 1
    (ae_norm_dualIntegrand_le h hx hy hκ ht)

end Integrand

/-- `|e^{−a} − e^{−b}| ≤ |a − b|` for `a, b ≥ 0`. -/
theorem abs_exp_neg_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
    intro a b ha hab
    have e : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
      rw [← Real.exp_add]; ring_nf
    have h1 := Real.add_one_le_exp (-(b - a))
    have h2 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h3 : 0 < Real.exp (-a) := Real.exp_pos _
    have h4 : Real.exp (-(b - a)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [e, abs_of_nonneg (by nlinarith), abs_of_nonpos (by linarith)]
    nlinarith
  rcases le_total a b with h | h
  · exact key a b ha h
  · rw [abs_sub_comm, abs_sub_comm a]; exact key b a hb h

/-!
## (d) `1{ζ ≤ t}` through `ζ ∧ T`
-/

/-- `ζ ≤ u ↔ ζ ∧ T ≤ u` for `0 ≤ u < T`. -/
theorem le_toNNReal_iff_untopA {T : ℝ≥0} {z : WithTop ℝ≥0} {u : ℝ} (hu0 : 0 ≤ u)
    (huT : u < T) :
    z ≤ (u.toNNReal : WithTop ℝ≥0) ↔ (((min (T : WithTop ℝ≥0) z).untopA : ℝ≥0) : ℝ) ≤ u := by
  induction z using WithTop.recTopCoe with
  | top =>
    simp only [top_le_iff, WithTop.coe_ne_top, false_iff, not_le, min_top_right]
    exact huT
  | coe z =>
    rw [← WithTop.coe_min, show ((min T z : ℝ≥0) : WithTop ℝ≥0).untopA = min T z from rfl,
      WithTop.coe_le_coe]
    constructor
    · intro hz
      have hzT : z ≤ T := hz.trans (Real.toNNReal_le_iff_le_coe.2 huT.le)
      rw [min_eq_right hzT]
      exact (Real.le_toNNReal_iff_coe_le hu0).1 hz
    · intro hm
      have hT : ¬ T ≤ z := fun hTz => by
        rw [min_eq_left hTz] at hm; linarith
      rw [min_eq_right (le_of_not_ge hT)] at hm
      exact (Real.le_toNNReal_iff_coe_le hu0).2 hm

/-- **On the boundary realization `F.N₂, F.X₂, F.Y₂`, `ζ ≤ t` for the `dualExtinction` is
`F.zeta ≤ t`**, a.s. -/
theorem ae_dualExtinction_lift_iff {D0 : ℝ} (hD0 : 0 < D0) {S : Type} [MeasurableSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ] {ξ : LΩ S → Fin 6 → ℝ} (hξ : IsLiftStart μ ξ)
    (F : LiftFamily μ D0 ξ) {x y : ℝ}
    (hB : IsBoundaryDualProcess (LP μ) (L𝓖 μ) D0 ![x] ![y] F.N₂ F.X₂ F.Y₂) :
    ∀ᵐ ω ∂LP μ, ∀ t : ℝ,
      dualExtinction F.N₂ ω ≤ ENNReal.ofReal t ↔ F.zeta ω ≤ (t.toNNReal : WithTop ℝ≥0) := by
  filter_upwards [hB.paths, F.ae_good₂ hD0 hξ] with ω hp hω t
  rw [dualExtinction_le_iff hp (F.N₂_zero ω) t]
  simp only [LiftFamily.N₂, hω, ite_true, F.Nd_of_good (F.good₂_spec hω).1]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => h'.elim, fun h' => absurd h' h⟩

end BlockBand.Transmission.DualBoundary
