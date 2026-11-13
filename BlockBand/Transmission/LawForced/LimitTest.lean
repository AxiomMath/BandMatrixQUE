module

public import BlockBand.Transmission.LawForced.Discrete

/-!
# Past tests at finite `W` and their limits

* `testAt b E κ W u Φ = Φ(μ^{⌊Wu_l⌋})_l` with the measurable states `stateAt`: a bounded
  `𝓕_{⌊Ws⌋}`-measurable test when every `u_l ≤ s` (`measurable_testAt`, `abs_testAt_le`); a.s.
  it is `Φ(μ_W(u_l))_l` (`testAt_ae_eq`);
* **`tendsto_test_mul`**: along a subsequential limit, for `v > 0` and a bounded continuous `H`,
  `E_W[testAt · H(μ_W(v))] → E[Φ(μ(u_l))_l · H(μ_v)]` (the `fdd` clause at the `m + 1` times
  `(u, v)`);
* `driftBCF`, `ratioBCF'`: the bounded continuous functions `ν ↦ ratioDrift(u, z, ν)` and
  `ν ↦ F_z(ν)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.LawDuality
open scoped NNReal ENNReal BoundedContinuousFunction

variable {W : ℕ}

/-- The finite-`W` past test `Φ(μ^{⌊Wu_l⌋})_l` (measurable states). -/
def testAt (b E : ℝ) (κ : ℝ → ℝ) (W : ℕ) {m : ℕ} (u : Fin m → ℝ)
    (Φ : BoundedContinuousFunction (Fin m → FiniteMeasure unitInterval) ℝ) (ω : GrowthPath W) :
    ℝ :=
  Φ fun l => stateAt b E κ W ⌊(W : ℝ) * u l⌋₊ ω

theorem measurable_testAt (b E : ℝ) (κ : ℝ → ℝ) {m : ℕ} {u : Fin m → ℝ} {s : ℝ}
    (hu : ∀ l, 0 ≤ u l ∧ u l ≤ s)
    (Φ : BoundedContinuousFunction (Fin m → FiniteMeasure unitInterval) ℝ) :
    Measurable[growthSigma W ⌊(W : ℝ) * s⌋₊] (testAt b E κ W u Φ) := by
  have hpi : Measurable[growthSigma W ⌊(W : ℝ) * s⌋₊]
      (fun ω => fun l => stateAt b E κ W ⌊(W : ℝ) * u l⌋₊ ω) := by
    refine @Measurable.of_eval _ _ _ (growthSigma W ⌊(W : ℝ) * s⌋₊) _ _ fun l => ?_
    refine (measurable_stateAt b E κ _).mono (Generator.growthSigma_mono ?_) le_rfl
    exact Nat.floor_mono (mul_le_mul_of_nonneg_left (hu l).2 (Nat.cast_nonneg _))
  exact Φ.continuous.measurable.comp hpi

theorem abs_testAt_le (b E : ℝ) (κ : ℝ → ℝ) {m : ℕ} (u : Fin m → ℝ)
    (Φ : BoundedContinuousFunction (Fin m → FiniteMeasure unitInterval) ℝ) (ω : GrowthPath W) :
    |testAt b E κ W u Φ ω| ≤ ‖Φ‖ := by
  rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _

theorem testAt_ae_eq {b E : ℝ} {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) (hb : b < 1) (hE1 : -2 < E)
    (hE2 : E < 2) {m : ℕ} (u : Fin m → ℝ)
    (Φ : BoundedContinuousFunction (Fin m → FiniteMeasure unitInterval) ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b,
      testAt b E κ W u Φ ω = Φ fun l => transmissionProcess b E κ W (u l) ω := by
  filter_upwards [ae_stateAt_eq hκ hb hE1 hE2] with ω hω
  simp only [testAt, hω]
  rfl

/-- `ν ↦ ratioDrift(u, z, ν)` as a bounded continuous function. -/
def driftBCF (D0 E : ℝ) {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) {p : ℕ} {z : DualCoord p}
    (hz : z ∈ dualChamber p) (u : ℝ) : BoundedContinuousFunction (FiniteMeasure unitInterval) ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun ν => ratioDrift D0 E κ u z ν, continuous_ratioDrift_nu D0 E hκ.1 hz u⟩
    (2 * (exists_bound_drift D0 E hκ hz).choose) fun ν ν' => by
      have h := (exists_bound_drift D0 E hκ hz).choose_spec.2
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have := abs_sub (ratioDrift D0 E κ u z ν) (ratioDrift D0 E κ u z ν')
      linarith [h u ν, h u ν']

theorem driftBCF_apply (D0 E : ℝ) {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) {p : ℕ}
    {z : DualCoord p} (hz : z ∈ dualChamber p) (u : ℝ) (ν : FiniteMeasure unitInterval) :
    driftBCF D0 E hκ hz u ν = ratioDrift D0 E κ u z ν := rfl

/-- `ν ↦ F_z(ν)` as a bounded continuous function. -/
def ratioBCF' {p : ℕ} {z : DualCoord p} (hz : z ∈ dualChamber p) :
    BoundedContinuousFunction (FiniteMeasure unitInterval) ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun ν => transmissionRatio z.1 z.2 ν, continuous_ratio_nu hz⟩
    1 fun ν ν' => by
      have h := transmissionRatio_mem_vec (IsRatioParameter.isRatioRange hz) ν
      have h' := transmissionRatio_mem_vec (IsRatioParameter.isRatioRange hz) ν'
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      rw [abs_le]; constructor <;> linarith

theorem ratioBCF'_apply {p : ℕ} {z : DualCoord p} (hz : z ∈ dualChamber p)
    (ν : FiniteMeasure unitInterval) : ratioBCF' hz ν = transmissionRatio z.1 z.2 ν := rfl

/-- `x ↦ x ∘ castSucc`. -/
def initMap (m : ℕ) :
    C(Fin (m + 1) → FiniteMeasure unitInterval, Fin m → FiniteMeasure unitInterval) :=
  ⟨fun x l => x (Fin.castSucc l), continuous_pi fun _ => continuous_apply _⟩

/-- `x ↦ x (last m)`. -/
def lastMap (m : ℕ) : C(Fin (m + 1) → FiniteMeasure unitInterval, FiniteMeasure unitInterval) :=
  ⟨fun x => x (Fin.last m), continuous_apply _⟩

/-- **Past test times a bounded continuous function of a later state: the limit.** -/
theorem tendsto_test_mul {b E : ℝ} {κ : ℝ → ℝ} {φ : ℕ → ℕ} (hκ : ∀ s, 0 ≤ κ s) (hb : b < 1)
    (hE1 : -2 < E) (hE2 : E < 2) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : ℝ → Ω → FiniteMeasure unitInterval} (h : IsTransmissionSubLimit b E κ φ P μ) {m : ℕ}
    {u : Fin m → ℝ} (hu : ∀ l, 0 < u l)
    (Φ : BoundedContinuousFunction (Fin m → FiniteMeasure unitInterval) ℝ) {v : ℝ} (hv : 0 < v)
    (H : BoundedContinuousFunction (FiniteMeasure unitInterval) ℝ) :
    Tendsto (fun n => ∫ ω, testAt b E κ (φ n) u Φ ω * H (transmissionProcess b E κ (φ n) v ω)
        ∂growthPathLaw (φ n) b) atTop
      (𝓝 (∫ ω, Φ (fun l => μ (u l) ω) * H (μ v ω) ∂P)) := by
  set τ : Fin (m + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) u v
  have hτ : ∀ i, 0 < τ i := fun i => by
    refine Fin.lastCases ?_ (fun l => ?_) i
    · simp only [τ, Fin.snoc_last]; exact hv
    · simp only [τ, Fin.snoc_castSucc]; exact hu l
  set Ψ : BoundedContinuousFunction (Fin (m + 1) → FiniteMeasure unitInterval) ℝ :=
    Φ.compContinuous (initMap m) * H.compContinuous (lastMap m)
  have hΨ : ∀ ν : ℝ → FiniteMeasure unitInterval,
      Ψ (fun i => ν (τ i)) = Φ (fun l => ν (u l)) * H (ν v) := by
    intro ν
    simp only [Ψ, BoundedContinuousFunction.coe_mul, Pi.mul_apply,
      BoundedContinuousFunction.compContinuous_apply, initMap, lastMap, ContinuousMap.coe_mk, τ,
      Fin.snoc_castSucc, Fin.snoc_last]
  have hf := h.fdd (m + 1) τ hτ Ψ
  rw [integral_congr_ae (Eventually.of_forall fun ω => hΨ (fun t => μ t ω))] at hf
  refine hf.congr fun n => ?_
  rw [integral_congr_ae (Eventually.of_forall fun ω =>
    hΨ (fun t => transmissionProcess b E κ (φ n) t ω))]
  refine integral_congr_ae ?_
  filter_upwards [testAt_ae_eq (W := φ n) hκ hb hE1 hE2 u Φ] with ω hω
  rw [hω]

end BlockBand.Transmission.LawForced
