module

public import BlockBand.Transmission.Generator.LimitSteps

/-!
# Convergence of the tested terms of the drift martingale problem

For a bounded continuous test `Φ` of past points `pts` (`IsPowerTraceLimitAlong`, fdd along
`σ`), and `0 < s ≤ t`:
* `drift_point_tendsto`: uniformly for `u ∈ [s,t]`, `E_n|Φ·A_k(P_{⌊Wu⌋})|² ≤ K` eventually, the
  limit inherits it, and `E_n[Φ·A_k(P_{⌊Wu⌋})] → E[Φ·A_k(P(u))]`;
* `increment_tendsto`: `E_n[Φ(P_k(⌊Wt⌋) - P_k(⌊Ws⌋))] → E[Φ(P_k(t) - P_k(s))]`;
* `limit_sq_bound`: `E|P_k(t)|² ≤ C` for the limit (integrability).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

theorem finVec_append (b : ℝ) (e : ℕ → ℝ) (W : ℕ) {m q : ℕ} (p₁ : Fin m → ℕ × ℝ)
    (p₂ : Fin q → ℕ × ℝ) (ω : GrowthPath W) :
    (fun l => finVec b e W (Fin.append p₁ p₂) ω (Fin.castAdd q l)) = finVec b e W p₁ ω ∧
      (fun l => finVec b e W (Fin.append p₁ p₂) ω (Fin.natAdd m l)) = finVec b e W p₂ ω :=
  ⟨funext fun l => by simp [finVec], funext fun l => by simp [finVec]⟩

omit [MeasurableSpace Ω] in
theorem limVec_append (Pk : ℕ → ℝ → Ω → ℝ) {m q : ℕ} (p₁ : Fin m → ℕ × ℝ)
    (p₂ : Fin q → ℕ × ℝ) (ω : Ω) :
    (fun l => limVec Pk (Fin.append p₁ p₂) ω (Fin.castAdd q l)) = limVec Pk p₁ ω ∧
      (fun l => limVec Pk (Fin.append p₁ p₂) ω (Fin.natAdd m l)) = limVec Pk p₂ ω :=
  ⟨funext fun l => by simp [limVec], funext fun l => by simp [limVec]⟩

theorem append_pos {m q : ℕ} {p₁ : Fin m → ℕ × ℝ} {p₂ : Fin q → ℕ × ℝ}
    (h₁ : ∀ l, 1 ≤ (p₁ l).1 ∧ 0 < (p₁ l).2) (h₂ : ∀ l, 1 ≤ (p₂ l).1 ∧ 0 < (p₂ l).2) :
    ∀ l, 1 ≤ (Fin.append p₁ p₂ l).1 ∧ 0 < (Fin.append p₁ p₂ l).2 :=
  Fin.addCases (fun l => by simpa using h₁ l) (fun l => by simpa using h₂ l)

theorem pathPower_one (b E : ℝ) (W r : ℕ) (ω : GrowthPath W) :
    pathPower b E W 1 r ω = pathConductance b E W r ω := by
  simp [pathPower, pathConductance, conductanceOf]

theorem abs_bcf_le {n : ℕ} (Φ : BoundedContinuousFunction (Fin n → ℝ) ℝ) (x : Fin n → ℝ) :
    |Φ x| ≤ ‖Φ‖ := by
  rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm x

theorem transportD0_pos {b E : ℝ} (hb0 : 0 < b) (hE1 : -2 < E) (hE2 : E < 2) :
    0 < transportD0 b E := by
  have : 0 < 4 - E ^ 2 := by nlinarith
  unfold transportD0; positivity

/-- Setup shared by the limit lemmas. -/
structure LimitSetup (b : ℝ) (e : ℕ → ℝ) (P : Measure Ω) (Pk : ℕ → ℝ → Ω → ℝ) (σ : ℕ → ℕ) :
    Prop where
  prob : IsProbabilityMeasure P
  meas : ∀ k, 1 ≤ k → ∀ t, 0 < t → Measurable (Pk k t)
  tends : Tendsto σ atTop atTop
  fdd : FddAlong b e P Pk σ

/-- **The drift term at one time, uniformly on `[s, t]`.** -/
theorem drift_point_tendsto (hLU : TransmissionLengthUniformContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ}
    (he : IsMovingEnergy E Ce e) {P : Measure Ω} {Pk : ℕ → ℝ → Ω → ℝ} {σ : ℕ → ℕ}
    (hS : LimitSetup b e P Pk σ) (k : ℕ) {s t : ℝ} (hs : 0 < s) {m : ℕ}
    (pts : Fin m → ℕ × ℝ) (hpts : ∀ l, 1 ≤ (pts l).1 ∧ 0 < (pts l).2)
    (Φ : BoundedContinuousFunction (Fin m → ℝ) ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ᶠ n in atTop, ∀ u ∈ Set.Icc s t, ∫⁻ ω, ‖Φ (finVec b e (σ n) pts ω) *
        transmissionDrift (transportD0 b E) k (pathPowers b (e (σ n)) (σ n)
          ⌊((σ n : ℕ) : ℝ) * u⌋₊ ω)‖ₑ ^ 2 ∂growthPathLaw (σ n) b ≤ ENNReal.ofReal K) ∧
      ∀ u ∈ Set.Icc s t,
        ∫⁻ ω, ‖Φ (limVec Pk pts ω) * transmissionDrift (transportD0 b E) k
          (fun i => Pk i u ω)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal K ∧
        Tendsto (fun n => ∫ ω, Φ (finVec b e (σ n) pts ω) *
          transmissionDrift (transportD0 b E) k (pathPowers b (e (σ n)) (σ n)
            ⌊((σ n : ℕ) : ℝ) * u⌋₊ ω) ∂growthPathLaw (σ n) b) atTop
          (𝓝 (∫ ω, Φ (limVec Pk pts ω) * transmissionDrift (transportD0 b E) k
            (fun i => Pk i u ω) ∂P)) := by
  have := hS.prob
  set D := transportD0 b E
  have hD0 : 0 ≤ D := (transportD0_pos hb0 hE1 hE2).le
  obtain ⟨C₄, hC₄0, hC₄⟩ := moment_pow_along hLU hb0 hb hE1 hE2 he hs 4 (by norm_num)
  obtain ⟨W₄, hW₄⟩ := hC₄ t
  set Wb := EnergyUniform.windowWidth (min (2 + E) (2 - E)) Ce
  set c := ‖Φ‖ * (D * k ^ 2)
  -- the finite-`W` bound
  have hfin : ∀ᶠ n in atTop, ∀ u ∈ Set.Icc s t, ∫⁻ ω, ‖Φ (finVec b e (σ n) pts ω) *
      transmissionDrift D k (pathPowers b (e (σ n)) (σ n) ⌊((σ n : ℕ) : ℝ) * u⌋₊ ω)‖ₑ ^ 2
        ∂growthPathLaw (σ n) b ≤ ENNReal.ofReal (2 * c ^ 2 * (C₄ + 0)) := by
    filter_upwards [hS.tends.eventually_ge_atTop (max W₄ Wb)] with n hn u hu
    set W := σ n
    have hmem := along_mem_bulk hE1 hE2 he (le_trans (le_max_right _ _) hn)
    obtain ⟨he1, he2⟩ := bulk_bounds' (by linarith [(mem_bulk_min hE1 hE2).1]) hmem
    set r := ⌊(W : ℝ) * u⌋₊
    refine lintegral_sq_le_of_abs_le (g₁ := fun ω => (pathPower b (e W) W 1 r ω) ^ 2)
      (g₂ := fun _ => 0) hC₄0 le_rfl ((measurable_pathPower _ _ _ _).pow_const 2) ?_ ?_ (by simp)
    · filter_upwards [pathPower_mem (W := W) (by linarith : b < 1) he1 he2] with ω hω
      have hA : |transmissionDrift D k (pathPowers b (e W) W r ω)| ≤
          D * k ^ 2 * (pathPower b (e W) W 1 r ω) ^ 2 :=
        abs_transmissionDrift_le hD0 k fun j hj _ => by
          obtain ⟨h0, h1, -⟩ := hω j r hj
          show |pathPower b (e W) W j r ω| ≤ _
          rw [abs_of_nonneg h0, pathPower_one]; exact h1
      rw [abs_mul, abs_zero, add_zero, abs_of_nonneg (sq_nonneg (pathPower b (e W) W 1 r ω))]
      calc _ ≤ ‖Φ‖ * (D * k ^ 2 * (pathPower b (e W) W 1 r ω) ^ 2) :=
            mul_le_mul (abs_bcf_le Φ _) hA (abs_nonneg _) (norm_nonneg _)
        _ = c * pathPower b (e W) W 1 r ω ^ 2 := by ring
    · have := hW₄ W (le_trans (le_max_left _ _) hn) u hu.1 hu.2 1 le_rfl
      refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) this
      rw [enorm_pow, ← pow_mul]
  refine ⟨2 * c ^ 2 * (C₄ + 0), by positivity, hfin, fun u hu => ?_⟩
  have hu0 : 0 < u := lt_of_lt_of_le hs hu.1
  have hpt := append_pos hpts (ptVec_pos (k := k) hu0)
  have hG : Continuous fun x : Fin (m + k) → ℝ => Φ (fun l => x (Fin.castAdd k l)) *
      transmissionDrift D k (extendVec k fun l => x (Fin.natAdd m l)) :=
    (Φ.continuous.comp (continuous_pi fun l => continuous_apply _)).mul
      ((continuous_transmissionDrift D k (v := fun x : ℕ → ℝ => x) fun j => continuous_apply j).comp
        ((continuous_extendVec k).comp (continuous_pi fun l => continuous_apply _)))
  have hfinG : ∀ n ω, (fun x : Fin (m + k) → ℝ => Φ (fun l => x (Fin.castAdd k l)) *
      transmissionDrift D k (extendVec k fun l => x (Fin.natAdd m l)))
        (finVec b e (σ n) (Fin.append pts (ptVec k u)) ω) =
      Φ (finVec b e (σ n) pts ω) *
        transmissionDrift D k (pathPowers b (e (σ n)) (σ n) ⌊((σ n : ℕ) : ℝ) * u⌋₊ ω) := by
    intro n ω
    obtain ⟨h1, h2⟩ := finVec_append b e (σ n) pts (ptVec k u) ω
    simp only [h1, h2, drift_extend_fin]
  have hlimG : ∀ ω, (fun x : Fin (m + k) → ℝ => Φ (fun l => x (Fin.castAdd k l)) *
      transmissionDrift D k (extendVec k fun l => x (Fin.natAdd m l)))
        (limVec Pk (Fin.append pts (ptVec k u)) ω) =
      Φ (limVec Pk pts ω) * transmissionDrift D k (fun i => Pk i u ω) := by
    intro ω
    obtain ⟨h1, h2⟩ := limVec_append Pk pts (ptVec k u) ω
    simp only [h1, h2, (drift_extend_lim D k Pk u ω).1]
  have hC : ∀ᶠ N in atTop, ∫⁻ ω, ‖(fun x : Fin (m + k) → ℝ => Φ (fun l => x (Fin.castAdd k l)) *
      transmissionDrift D k (extendVec k fun l => x (Fin.natAdd m l)))
        (finVec b e (σ N) (Fin.append pts (ptVec k u)) ω)‖ₑ ^ 2 ∂growthPathLaw (σ N) b ≤
        ENNReal.ofReal (2 * c ^ 2 * (C₄ + 0)) := by
    filter_upwards [hfin] with n hn
    simp only [hfinG]; exact hn u hu
  obtain ⟨hL, hT⟩ := fdd_tendsto hS.meas hS.fdd _ hpt hG hC
  simp only [hfinG, hlimG] at hL hT
  exact ⟨hL, hT⟩

/-- **The tested increment.** -/
theorem increment_tendsto (hLU : TransmissionLengthUniformContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ}
    (he : IsMovingEnergy E Ce e) {P : Measure Ω} {Pk : ℕ → ℝ → Ω → ℝ} {σ : ℕ → ℕ}
    (hS : LimitSetup b e P Pk σ) {k : ℕ} (hk : 1 ≤ k) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    {m : ℕ} (pts : Fin m → ℕ × ℝ) (hpts : ∀ l, 1 ≤ (pts l).1 ∧ 0 < (pts l).2)
    (Φ : BoundedContinuousFunction (Fin m → ℝ) ℝ) :
    Tendsto (fun n => ∫ ω, Φ (finVec b e (σ n) pts ω) *
        (pathPower b (e (σ n)) (σ n) k ⌊((σ n : ℕ) : ℝ) * t⌋₊ ω -
          pathPower b (e (σ n)) (σ n) k ⌊((σ n : ℕ) : ℝ) * s⌋₊ ω) ∂growthPathLaw (σ n) b) atTop
      (𝓝 (∫ ω, Φ (limVec Pk pts ω) * (Pk k t ω - Pk k s ω) ∂P)) := by
  have := hS.prob
  obtain ⟨C₂, hC₂0, hC₂⟩ := moment_pow_along hLU hb0 hb hE1 hE2 he hs 2 (by norm_num)
  obtain ⟨W₂, hW₂⟩ := hC₂ t
  set q : Fin 2 → ℕ × ℝ := ![(k, s), (k, t)]
  have hq : ∀ l, 1 ≤ (q l).1 ∧ 0 < (q l).2 := by
    intro l; fin_cases l
    · exact ⟨hk, hs⟩
    · exact ⟨hk, lt_of_lt_of_le hs hst⟩
  have hpt := append_pos hpts hq
  set G : (Fin (m + 2) → ℝ) → ℝ := fun x => Φ (fun l => x (Fin.castAdd 2 l)) *
    (x (Fin.natAdd m 1) - x (Fin.natAdd m 0))
  have hG : Continuous G := (Φ.continuous.comp (continuous_pi fun l => continuous_apply _)).mul
    ((continuous_apply _).sub (continuous_apply _))
  have hfinG : ∀ n ω, G (finVec b e (σ n) (Fin.append pts q) ω) =
      Φ (finVec b e (σ n) pts ω) * (pathPower b (e (σ n)) (σ n) k ⌊((σ n : ℕ) : ℝ) * t⌋₊ ω -
          pathPower b (e (σ n)) (σ n) k ⌊((σ n : ℕ) : ℝ) * s⌋₊ ω) := by
    intro n ω
    simp only [G, (finVec_append b e (σ n) pts q ω).1]
    simp [finVec, q]
  have hlimG : ∀ ω, G (limVec Pk (Fin.append pts q) ω) =
      Φ (limVec Pk pts ω) * (Pk k t ω - Pk k s ω) := by
    intro ω
    simp only [G, (limVec_append Pk pts q ω).1]
    simp [limVec, q]
  have hC : ∀ᶠ N in atTop, ∫⁻ ω, ‖G (finVec b e (σ N) (Fin.append pts q) ω)‖ₑ ^ 2
      ∂growthPathLaw (σ N) b ≤ ENNReal.ofReal (2 * ‖Φ‖ ^ 2 * (C₂ + C₂)) := by
    filter_upwards [hS.tends.eventually_ge_atTop W₂] with n hn
    simp only [hfinG]
    refine lintegral_sq_le_of_abs_le hC₂0 hC₂0 (measurable_pathPower _ _ _ _) ?_
      (hW₂ _ hn t hst le_rfl k hk) (hW₂ _ hn s le_rfl hst k hk)
    refine Eventually.of_forall fun ω => ?_
    rw [abs_mul]
    exact mul_le_mul (abs_bcf_le Φ _) (abs_sub _ _) (abs_nonneg _) (norm_nonneg _)
  have h := (fdd_tendsto hS.meas hS.fdd _ hpt hG hC).2
  simp only [hfinG, hlimG] at h
  exact h

/-- **Second moments of the limit** at positive times. -/
theorem limit_sq_bound (hLU : TransmissionLengthUniformContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ}
    (he : IsMovingEnergy E Ce e) {P : Measure Ω} {Pk : ℕ → ℝ → Ω → ℝ} {σ : ℕ → ℕ}
    (hS : LimitSetup b e P Pk σ) {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∫⁻ ω, ‖Pk k t ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C := by
  have := hS.prob
  obtain ⟨C₂, hC₂0, hC₂⟩ := moment_pow_along hLU hb0 hb hE1 hE2 he ht 2 (by norm_num)
  obtain ⟨W₂, hW₂⟩ := hC₂ t
  refine ⟨C₂, hC₂0, ?_⟩
  have hpt : ∀ l : Fin 1, 1 ≤ ((![(k, t)] : Fin 1 → ℕ × ℝ) l).1 ∧
      0 < ((![(k, t)] : Fin 1 → ℕ × ℝ) l).2 := fun l => by fin_cases l; exact ⟨hk, ht⟩
  have hC : ∀ᶠ N in atTop, ∫⁻ ω, ‖(fun x : Fin 1 → ℝ => x 0)
      (finVec b e (σ N) ![(k, t)] ω)‖ₑ ^ 2 ∂growthPathLaw (σ N) b ≤ ENNReal.ofReal C₂ := by
    filter_upwards [hS.tends.eventually_ge_atTop W₂] with n hn
    simpa [finVec] using hW₂ _ hn t le_rfl le_rfl k hk
  have h := (fdd_tendsto hS.meas hS.fdd _ hpt (continuous_apply 0) hC).1
  simpa [limVec] using h

end BlockBand.Transmission.Generator
