module

public import BlockBand.Transmission.Generator.LimitDrift
public import BlockBand.Transmission.Generator.OdeCompare
public import Mathlib.Probability.Moments.Variance

/-!
# The mean conductance of every limit: `E P_1(t) ≤ 2/(D₀t)` (field `meanConductance`)

* `limit_nonneg`: limits of `Tr T^k ≥ 0` are `≥ 0` a.s. (portmanteau with one bounded test).
* `limit_sq_bound_unif`: `sup_{u ∈ [s,t]} E P_k(u)² < ∞`.
* `mean_identity`: `y(b) - y(a) = -(D₀/2)∫_a^b E P_1(u)² du` (`y = E P_1`), from the `k = 1` drift
  martingale (`limit_drift_martingale`, test `Φ = 1`) and Fubini.
* `meanConductance_along hLU hD`: along a moving energy, every limit has
  `∫⁻ |P_1(t)| ≤ 2/(D₀t)` (`ode_compare` on `[s,t]`, Jensen `y² ≤ E P_1²`, then `s ↓ 0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology ProbabilityTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

theorem drift_one (D : ℝ) (P : ℕ → ℝ) : transmissionDrift D 1 P = -(D / 2) * P 1 ^ 2 := by
  simp [transmissionDrift]; ring

theorem limit_nonneg {b : ℝ} (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {Ce : ℝ}
    {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e) {P : Measure Ω} {Pk : ℕ → ℝ → Ω → ℝ}
    {σ : ℕ → ℕ} (hS : LimitSetup b e P Pk σ) {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, 0 ≤ Pk k t ω := by
  have := hS.prob
  set Φ := clampBCF (fun x : Fin 1 → ℝ => max (-x 0) 0) (by fun_prop) 1
  have hΦ : ∀ x, Φ x = min 1 (max (-x 0) 0) := fun x => by
    simp only [Φ, clampBCF_apply]
    exact max_eq_right (by have := le_min zero_le_one (le_max_right (-x 0) 0); linarith)
  have hfin : ∀ᶠ n in atTop, ∫ ω, Φ (fun l => pathPower b (e (σ n)) (σ n) ((fun _ => k) l)
      ⌊((σ n : ℕ) : ℝ) * (fun _ => t) l⌋₊ ω) ∂growthPathLaw (σ n) b = 0 := by
    filter_upwards [hS.tends.eventually_ge_atTop
      (EnergyUniform.windowWidth (min (2 + E) (2 - E)) Ce)] with n hn
    obtain ⟨he1, he2⟩ := bulk_bounds' (by linarith [(mem_bulk_min hE1 hE2).1])
      (along_mem_bulk hE1 hE2 he hn)
    refine integral_eq_zero_of_ae ?_
    filter_upwards [pathPower_mem (W := σ n) (by linarith : b < 1) he1 he2] with ω hω
    rw [hΦ]; simp [(hω k _ hk).1]
  have hT := hS.fdd 1 (fun _ => k) (fun _ => t) (fun _ => ⟨hk, ht⟩) Φ
  have h0 : ∫ ω, Φ (fun _ => Pk k t ω) ∂P = 0 :=
    tendsto_nhds_unique hT (tendsto_const_nhds.congr' (hfin.mono fun n hn => hn.symm))
  have hnn : 0 ≤ᵐ[P] fun ω => Φ (fun _ => Pk k t ω) :=
    Eventually.of_forall fun ω => by
      show 0 ≤ Φ _
      rw [hΦ]; exact le_min zero_le_one (le_max_right _ _)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn (integrable_bcf_comp
    (measurable_pi_iff.mpr fun _ => hS.meas k hk t ht) Φ)).mp h0
  filter_upwards [hae] with ω hω
  simp only [Pi.zero_apply, hΦ] at hω
  by_contra hneg
  have hneg' := not_le.mp hneg
  have : 0 < min 1 (max (-Pk k t ω) 0) := lt_min one_pos (lt_max_of_lt_left (by linarith))
  linarith

theorem limit_sq_bound_unif (hLU : TransmissionLengthUniformContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ}
    (he : IsMovingEnergy E Ce e) {P : Measure Ω} {Pk : ℕ → ℝ → Ω → ℝ} {σ : ℕ → ℕ}
    (hS : LimitSetup b e P Pk σ) {k : ℕ} (hk : 1 ≤ k) {s t : ℝ} (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc s t, ∫⁻ ω, ‖Pk k u ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C := by
  have := hS.prob
  obtain ⟨C₂, hC₂0, hC₂⟩ := moment_pow_along hLU hb0 hb hE1 hE2 he hs 2 (by norm_num)
  obtain ⟨W₂, hW₂⟩ := hC₂ t
  refine ⟨C₂, hC₂0, fun u hu => ?_⟩
  have hu0 : 0 < u := lt_of_lt_of_le hs hu.1
  have hpt : ∀ l : Fin 1, 1 ≤ ((![(k, u)] : Fin 1 → ℕ × ℝ) l).1 ∧
      0 < ((![(k, u)] : Fin 1 → ℕ × ℝ) l).2 := fun l => by fin_cases l; exact ⟨hk, hu0⟩
  have hC : ∀ᶠ N in atTop, ∫⁻ ω, ‖(fun x : Fin 1 → ℝ => x 0)
      (finVec b e (σ N) ![(k, u)] ω)‖ₑ ^ 2 ∂growthPathLaw (σ N) b ≤ ENNReal.ofReal C₂ := by
    filter_upwards [hS.tends.eventually_ge_atTop W₂] with n hn
    simpa [finVec] using hW₂ _ hn u hu.1 hu.2 k hk
  simpa [limVec] using (fdd_tendsto hS.meas hS.fdd _ hpt (continuous_apply 0) hC).1

/-- **The mean identity** `y(b) - y(a) = -(D₀/2)∫_a^b E P_1²`, with interval integrability. -/
theorem mean_identity (hLU : TransmissionLengthUniformContract) (hD : PowerDriftSummable)
    {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {Ce : ℝ}
    {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e) {P : Measure Ω} {Pk : ℕ → ℝ → Ω → ℝ}
    (h : IsPowerTraceLimitAlong b e P Pk) {σ : ℕ → ℕ} (hS : LimitSetup b e P Pk σ) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) :
    (∫ ω, Pk 1 y ω ∂P) - ∫ ω, Pk 1 x ω ∂P =
        -(transportD0 b E / 2) * ∫ u in x..y, ∫ ω, Pk 1 u ω ^ 2 ∂P ∧
      IntervalIntegrable (fun u => ∫ ω, Pk 1 u ω ^ 2 ∂P) volume x y := by
  have := hS.prob
  have hDpos : 0 < (transportD0 b E) := transportD0_pos hb0 hE1 hE2
  have hH : Continuous (transmissionDrift (transportD0 b E) 1) :=
    continuous_transmissionDrift (transportD0 b E) 1 (v := fun x => x) fun j => continuous_apply j
  obtain ⟨K₁, -, -, hK₁⟩ := drift_point_tendsto hLU hb0 hb hE1 hE2 he hS 1 hx (t := y)
    (m := 0) Fin.elim0 (fun l => l.elim0) (BoundedContinuousFunction.const _ 1)
  have hHC : ∀ u ∈ Set.Icc x y, ∫⁻ ω, ‖transmissionDrift (transportD0 b E) 1 (cutVec Pk u ω)‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal K₁ := fun u hu => by simpa [drift_cutVec] using (hK₁ u hu).1
  obtain ⟨hF1, hF2, hF3⟩ := limit_fubini h.measurable h.continuous hH hx hxy
    (ψ := fun _ => (1 : ℝ)) measurable_const (B := 1) (by simp) hHC
  have hA : ∀ u, ∫ ω, 1 * transmissionDrift (transportD0 b E) 1 (cutVec Pk u ω) ∂P =
      -((transportD0 b E) / 2) * ∫ ω, Pk 1 u ω ^ 2 ∂P := fun u => by
    simp only [one_mul, drift_cutVec, drift_one]; exact integral_const_mul _ _
  simp only [hA] at hF2 hF3
  simp only [one_mul] at hF2
  obtain ⟨-, hMt⟩ := limit_drift_martingale hLU hD hb0 hb hE1 hE2 he h (k := 1) le_rfl x y hx
    (lt_of_lt_of_le hx hxy) hxy
  have h0 := hMt 0 Fin.elim0 Fin.elim0 (fun l => l.elim0) (BoundedContinuousFunction.const _ 1)
  simp only [BoundedContinuousFunction.const_apply, one_smul] at h0
  obtain ⟨Cy, -, hCy⟩ := limit_sq_bound hLU hb0 hb hE1 hE2 he hS le_rfl (lt_of_lt_of_le hx hxy)
  obtain ⟨Cx, -, hCx⟩ := limit_sq_bound hLU hb0 hb hE1 hE2 he hS le_rfl hx
  have hPy := (sq_integrable_of (h.measurable 1 le_rfl y (lt_of_lt_of_le hx hxy)).aestronglyMeasurable hCy).2.1
  have hPx := (sq_integrable_of (h.measurable 1 le_rfl x hx).aestronglyMeasurable hCx).2.1
  have hF1' : Integrable (fun ω => ∫ u in x..y, transmissionDrift (transportD0 b E) 1 (fun i => Pk i u ω)) P := by
    simpa [drift_cutVec] using hF1
  simp only [drift_cutVec] at hF2
  rw [integral_sub (f := fun ω => Pk 1 y ω - Pk 1 x ω) (hPy.sub hPx) hF1', integral_sub hPy hPx, hF2,
    intervalIntegral.integral_const_mul] at h0
  refine ⟨by linarith, ?_⟩
  have := hF3.const_mul (-(2 / (transportD0 b E)))
  refine this.congr fun u _ => ?_
  have hD' : transportD0 b E ≠ 0 := hDpos.ne'
  field_simp

end BlockBand.Transmission.Generator
