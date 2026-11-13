module

public import BlockBand.Transmission.LawFinite.EntranceAlive

/-!
# One step of the alive reciprocal

**`alive_step`**: for `j ≥ 1`,
`K⁻¹P(A_j ∩ {q_{j+1} < K}) + E[1_{A_{j+1}} r_K(q_{j+1})] ≤ E[1_{A_j} r_K(q_j)] + e₀ + (C/K)Eδ₀,j`
with `e₀ = C(W⁻¹ + (WK)⁻¹ + Kκ/(W²K)) + C_A W^{-A}`. Proof: positivity of `q_{j+1}` on `A_j`
(`ae_passiveMass_freshSchur_pos`, so that `r_K(q_{j+1}) = K⁻¹` at a crossing), `step_lintegral_le`
with `hrd` at `X = X_j`, `ε = κ((j+1)/W)/W²`, and `driftBound_le` on `A_j`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped ENNReal ComplexOrder

variable {W : ℕ}

theorem recipK_nonneg {K q : ℝ} (hK : 0 ≤ K) (hq : 0 ≤ q) : 0 ≤ recipK K q :=
  le_min (inv_nonneg.mpr hq) (inv_nonneg.mpr hK)

theorem recipK_le {K q : ℝ} : recipK K q ≤ K⁻¹ := min_le_right _ _

theorem recipK_of_lt {K q : ℝ} (hq : 0 < q) (hqK : q < K) : recipK K q = K⁻¹ :=
  min_eq_right (inv_le_inv₀ (hq.trans hqK) hq |>.mpr hqK.le)

theorem recipK_of_le {K q : ℝ} (hK : 0 < K) (hKq : K ≤ q) : recipK K q = q⁻¹ :=
  min_eq_left ((inv_le_inv₀ (hK.trans_le hKq) hK).mpr hKq)

/-- The reciprocal-drift bound `q⁻¹ + C(W⁻¹ + δ₀/q + (Wq)⁻¹ + ε/q) + C_A W^{-A}`. -/
def driftBound (C CA A ε : ℝ) (W : ℕ) (q δ : ℝ) : ℝ :=
  q⁻¹ + C * ((W : ℝ)⁻¹ + δ / q + ((W : ℝ) * q)⁻¹ + ε / q) + CA * (W : ℝ) ^ (-A)

theorem measurable_driftBound (C CA A ε : ℝ) (W : ℕ) :
    Measurable fun x : ℝ × ℝ => driftBound C CA A ε W x.1 x.2 := by
  unfold driftBound; fun_prop

/-- On the alive event: `driftBound ≤ r_K(q) + e₀ + (C/K)δ₀`. -/
theorem driftBound_le {C CA A ε K Kκ q δ : ℝ} (hC : 0 ≤ C) (hK : 0 < K) (hKq : K ≤ q)
    (hδ : 0 ≤ δ) (hε0 : 0 ≤ ε) (hε : ε ≤ Kκ / (W : ℝ) ^ 2) :
    driftBound C CA A ε W q δ ≤ recipK K q +
      (C * ((W : ℝ)⁻¹ + ((W : ℝ) * K)⁻¹ + Kκ / ((W : ℝ) ^ 2 * K)) + CA * (W : ℝ) ^ (-A)) +
      C / K * δ := by
  have hq : 0 < q := hK.trans_le hKq
  rw [driftBound, recipK_of_le hK hKq]
  have h1 : δ / q ≤ δ / K := div_le_div_of_nonneg_left hδ hK hKq
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have h2 : ((W : ℝ) * q)⁻¹ ≤ ((W : ℝ) * K)⁻¹ := by
    rcases hW0.eq_or_lt with h | h
    · rw [← h]; simp
    · exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hKq hW0)
  have h3 : ε / q ≤ Kκ / ((W : ℝ) ^ 2 * K) := by
    calc ε / q ≤ ε / K := div_le_div_of_nonneg_left hε0 hK hKq
      _ ≤ Kκ / (W : ℝ) ^ 2 / K := div_le_div_of_nonneg_right hε hK.le
      _ = _ := by rw [div_div]
  have : C * ((W : ℝ)⁻¹ + δ / q + ((W : ℝ) * q)⁻¹ + ε / q) ≤
      C * ((W : ℝ)⁻¹ + ((W : ℝ) * K)⁻¹ + Kκ / ((W : ℝ) ^ 2 * K)) + C / K * δ := by
    have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add (le_refl ((W : ℝ)⁻¹)) h1) h2) h3) hC
    calc _ ≤ C * ((W : ℝ)⁻¹ + δ / K + ((W : ℝ) * K)⁻¹ + Kκ / ((W : ℝ) ^ 2 * K)) := this
      _ = _ := by ring
  linarith

/-- The past form of an alive event at a growth sample extending `p`. -/
theorem alive_of_past {b E : ℝ} {κ : ℝ → ℝ} {K d : ℝ} {j : ℕ} {S : Set (PastSample W j)}
    (hS : pastCoords W j ⁻¹' S = aliveSet b E κ W K d j) {p : PastSample W j} (hp : p ∈ S)
    (hj : 1 ≤ j) :
    K ≤ passiveMass b E (pastX b E κ W j p) ∧ jetDistance0 b E (pastX b E κ W j p) ≤ d := by
  have hω : extendPast p ∈ aliveSet b E κ W K d j := by
    rw [← hS, Set.mem_preimage, pastCoords_extendPast]; exact hp
  have := hω j hj le_rfl
  rwa [pathNearSchur_eq_past, pastCoords_extendPast] at this

/-- **One step of the alive reciprocal**: with the reciprocal drift `hrd` at
`(W, E)` (`ReciprocalDrift` instantiated), for `j ≥ 1`,
`K⁻¹P(A_j ∩ {q_{j+1} < K}) + E[1_{A_{j+1}} r_K(q_{j+1})] ≤ E[1_{A_j} r_K(q_j)] + e₀ + (C/K)Eδ₀,j`,
`e₀ = C(W⁻¹ + (WK)⁻¹ + Kκ/(W²K)) + C_A W^{-A}`. -/
theorem alive_step {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hW : 1 ≤ W) {κ : ℝ → ℝ} (hκ0 : ∀ s, 0 ≤ κ s) {Kκ : ℝ} (hKκ : ∀ s, κ s ≤ Kκ)
    {K d C CA A : ℝ} (hK : 0 < K) (hC : 0 ≤ C)
    (hrd : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → jetDistance0 b E X ≤ d →
      K ≤ passiveMass b E X → ∀ ε : ℝ, 0 ≤ ε → ε ≤ Kκ / (W : ℝ) ^ 2 →
        ∫ f, recipK K (passiveMass b E (freshSchur E (absorbedInput X ε) f)) ∂freshLaw W b ≤
          driftBound C CA A ε W (passiveMass b E X) (jetDistance0 b E X))
    (j : ℕ) (hj : 1 ≤ j) :
    ENNReal.ofReal K⁻¹ * growthPathLaw W b (aliveSet b E κ W K d j ∩
        {ω | passiveMass b E (pathNearSchur b E κ W (j + 1) ω) < K}) +
      ∫⁻ ω, (aliveSet b E κ W K d (j + 1)).indicator (fun ω =>
        ENNReal.ofReal (recipK K (passiveMass b E (pathNearSchur b E κ W (j + 1) ω)))) ω
        ∂growthPathLaw W b ≤
    ∫⁻ ω, (aliveSet b E κ W K d j).indicator (fun ω =>
        ENNReal.ofReal (recipK K (passiveMass b E (pathNearSchur b E κ W j ω)))) ω
        ∂growthPathLaw W b +
      ENNReal.ofReal (C * ((W : ℝ)⁻¹ + ((W : ℝ) * K)⁻¹ + Kκ / ((W : ℝ) ^ 2 * K)) +
        CA * (W : ℝ) ^ (-A)) +
      ENNReal.ofReal (C / K) * ∫⁻ ω, ENNReal.ofReal (jetDistance0 b E
        (pathNearSchur b E κ W j ω)) ∂growthPathLaw W b := by
  set μ := growthPathLaw W b
  set q : ℕ → GrowthPath W → ℝ := fun i ω => passiveMass b E (pathNearSchur b E κ W i ω)
  set δ : ℕ → GrowthPath W → ℝ := fun i ω => jetDistance0 b E (pathNearSchur b E κ W i ω)
  set ε := layerAbsorption W κ (j + 1) 0
  obtain ⟨hε0, hεK⟩ := layerAbsorption_mem (W := W) hκ0 hKκ (j + 1) 0
  obtain ⟨S, hSm, hS⟩ := exists_past_aliveSet b E κ K d j (W := W)
  have hq : ∀ i, Measurable (q i) := fun i =>
    (SourceMixing.measurable_passiveMass b E).comp ((pathNearSchur_adapted b E κ W i).mono
      (Generator.growthSigma_le W i) le_rfl)
  have hδ : ∀ i, Measurable (δ i) := fun i =>
    (measurable_jetDistance0 b E).comp ((pathNearSchur_adapted b E κ W i).mono
      (Generator.growthSigma_le W i) le_rfl)
  have hAm := measurableSet_aliveSet b E κ K d j (W := W)
  have hAm' := measurableSet_aliveSet b E κ K d (j + 1) (W := W)
  have hae : ∀ᵐ ω ∂μ, pathNearSchur b E κ W (j + 1) ω =
      freshSchur E (stepInput b E κ W j (pastCoords W j ω)) (freshSample W j ω) := by
    filter_upwards [ae_pathNearSchur_succ_abs hb h1 h2 hW hκ0] with ω hω
    rw [hω j hj, pathNearSchur_eq_past]; rfl
  -- the past bounds
  have hpast : ∀ p ∈ S, p ∈ hermPast W j →
      (passiveY (pastX b E κ W j p)).PosSemidef ∧ K ≤ passiveMass b E (pastX b E κ W j p) ∧
        jetDistance0 b E (pastX b E κ W j p) ≤ d ∧ 0 < passiveMass b E (stepInput b E κ W j p) := by
    intro p hp hph
    have hY := passiveY_pastX (b := b) (E := E) (by linarith) h1 h2 hκ0 hph
    obtain ⟨hKq, hdq⟩ := alive_of_past hS hp hj
    refine ⟨hY, hKq, hdq, ?_⟩
    have := passiveMass_le_absorb hb0 hb h1 h2 hY hε0
    have hq0 : 0 < passiveMass b E (pastX b E κ W j p) := hK.trans_le hKq
    have : 0 < (1 + ε / etaZ b E) ^ 2 * passiveMass b E (stepInput b E κ W j p) := hq0.trans_le this
    exact pos_of_mul_pos_right this (sq_nonneg _)
  -- (a) positivity of `q_{j+1}` on `A_j`
  have hpos : ∀ᵐ ω ∂μ, ω ∈ aliveSet b E κ W K d j → 0 < q (j + 1) ω := by
    have hF : Measurable ((Set.Iic (0 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞))) :=
      measurable_const.indicator measurableSet_Iic
    have hint := step_lintegral_le κ j (measurable_stepInput b E κ j) hae hSm hF
      (measurable_const (a := (0 : ℝ≥0∞))) (by
        filter_upwards [ae_pastLaw_hermitian W j b] with p hph hp
        obtain ⟨hY, -, -, hqs⟩ := hpast p hp hph
        have h0 := ae_passiveMass_freshSchur_pos hb0 hb h1 h2 hW
          (passiveY_absorb hY hε0) hqs
        refine le_of_eq ((lintegral_congr_ae ?_).trans lintegral_zero)
        filter_upwards [h0] with f hf
        exact Set.indicator_of_notMem (fun h => absurd (Set.mem_Iic.mp h) (not_le.mpr hf)) _)
    rw [hS] at hint
    have hint0 : ∫⁻ ω, (aliveSet b E κ W K d j).indicator (fun ω =>
        (Set.Iic (0 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) (q (j + 1) ω)) ω ∂μ = 0 :=
      le_antisymm (hint.trans (by simp)) bot_le
    have hm : Measurable fun ω => (aliveSet b E κ W K d j).indicator (fun ω =>
        (Set.Iic (0 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) (q (j + 1) ω)) ω :=
      (hF.comp (hq (j + 1))).indicator hAm
    filter_upwards [(lintegral_eq_zero_iff hm).mp hint0] with ω hω hA
    by_contra hle
    rw [Set.indicator_of_mem hA, Set.indicator_of_mem (by simpa using hle)] at hω
    exact one_ne_zero hω
  -- (b) Fubini with the reciprocal drift
  set g : PastSample W j → ℝ≥0∞ := fun p => ENNReal.ofReal (driftBound C CA A ε W
    (passiveMass b E (pastX b E κ W j p)) (jetDistance0 b E (pastX b E κ W j p)))
  have hg : Measurable g := ENNReal.measurable_ofReal.comp ((measurable_driftBound C CA A ε W).comp
    (((SourceMixing.measurable_passiveMass b E).comp (measurable_pastX b E κ j)).prodMk
      ((measurable_jetDistance0 b E).comp (measurable_pastX b E κ j))))
  have hFub := step_lintegral_le κ j (measurable_stepInput b E κ j) hae hSm
    (ENNReal.measurable_ofReal.comp (measurable_recipK K)) hg (by
      filter_upwards [ae_pastLaw_hermitian W j b] with p hph hp
      simp only [Function.comp_apply]
      obtain ⟨hY, hKq, hdq, -⟩ := hpast p hp hph
      have hb' := hrd _ hY hdq hKq ε hε0 hεK
      have hnn : ∀ᵐ f ∂freshLaw W b, 0 ≤ recipK K
          (passiveMass b E (freshSchur E (stepInput b E κ W j p) f)) := by
        filter_upwards [PathScalar.ae_layer_herm (W := W) b] with f hA
        exact recipK_nonneg hK.le (PassiveCovariance.passiveMass_nonneg b E
          (PathScalar.passiveY_freshSchur E (passiveY_absorb hY hε0) f hA))
      have hmf : Measurable fun f => recipK K
          (passiveMass b E (freshSchur E (stepInput b E κ W j p) f)) :=
        (measurable_recipK K).comp ((SourceMixing.measurable_passiveMass b E).comp
          (measurable_freshSchur_comp E measurable_const measurable_id))
      have hI : Integrable (fun f => recipK K
          (passiveMass b E (freshSchur E (stepInput b E κ W j p) f))) (freshLaw W b) := by
        refine Integrable.of_bound (C := K⁻¹) hmf.aestronglyMeasurable ?_
        filter_upwards [hnn] with f hf
        rw [Real.norm_of_nonneg hf]; exact recipK_le
      rw [← ofReal_integral_eq_lintegral_ofReal hI hnn]
      exact ENNReal.ofReal_le_ofReal hb')
  rw [hS] at hFub
  -- (c) the pointwise bound on `A_j`
  have hc : ∫⁻ ω, (aliveSet b E κ W K d j).indicator (fun ω => g (pastCoords W j ω)) ω ∂μ ≤
      ∫⁻ ω, ((aliveSet b E κ W K d j).indicator (fun ω => ENNReal.ofReal (recipK K (q j ω))) ω +
        ENNReal.ofReal (C * ((W : ℝ)⁻¹ + ((W : ℝ) * K)⁻¹ + Kκ / ((W : ℝ) ^ 2 * K)) +
          CA * (W : ℝ) ^ (-A)) + ENNReal.ofReal (C / K) * ENNReal.ofReal (δ j ω)) ∂μ := by
    refine lintegral_mono fun ω => ?_
    by_cases hA : ω ∈ aliveSet b E κ W K d j
    · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA]
      obtain ⟨hKq, hdq⟩ := hA j hj le_rfl
      have hb1 := driftBound_le (CA := CA) (A := A) (W := W) (δ := δ j ω) hC hK hKq
        (norm_nonneg _) hε0 hεK
      simp only [g, ← pathNearSchur_eq_past]
      refine (ENNReal.ofReal_le_ofReal hb1).trans ?_
      refine (ENNReal.ofReal_add_le).trans (add_le_add ENNReal.ofReal_add_le ?_)
      rw [ENNReal.ofReal_mul (by positivity)]
    · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA]; exact bot_le
  have hm2 : Measurable fun ω => ENNReal.ofReal (δ j ω) := ENNReal.measurable_ofReal.comp (hδ j)
  have hm1 : Measurable fun ω => ENNReal.ofReal (C / K) * ENNReal.ofReal (δ j ω) :=
    hm2.const_mul _
  rw [lintegral_add_right _ hm1, lintegral_add_right _ measurable_const, lintegral_const,
    measure_univ, mul_one, lintegral_const_mul _ hm2] at hc
  -- (a') the split of `1_{A_j} r_K(q_{j+1})`
  have hsplit : ENNReal.ofReal K⁻¹ * μ (aliveSet b E κ W K d j ∩ {ω | q (j + 1) ω < K}) +
      ∫⁻ ω, (aliveSet b E κ W K d (j + 1)).indicator
        (fun ω => ENNReal.ofReal (recipK K (q (j + 1) ω))) ω ∂μ ≤
      ∫⁻ ω, (aliveSet b E κ W K d j).indicator
        (fun ω => ENNReal.ofReal (recipK K (q (j + 1) ω))) ω ∂μ := by
    have hB : MeasurableSet (aliveSet b E κ W K d j ∩ {ω | q (j + 1) ω < K}) :=
      hAm.inter (measurableSet_lt (hq (j + 1)) measurable_const)
    rw [← lintegral_indicator_const hB, ← lintegral_add_left
      ((measurable_const.indicator hB))]
    refine lintegral_mono_ae ?_
    filter_upwards [hpos] with ω hω
    by_cases hA : ω ∈ aliveSet b E κ W K d j
    · rw [Set.indicator_of_mem hA]
      by_cases hlt : q (j + 1) ω < K
      · have hn : ω ∉ aliveSet b E κ W K d (j + 1) := fun h =>
          absurd (aliveSet_succ_disj b E κ K d j h) (not_le.mpr hlt)
        rw [Set.indicator_of_mem (show ω ∈ aliveSet b E κ W K d j ∩ {ω | q (j + 1) ω < K} from
          ⟨hA, hlt⟩), Set.indicator_of_notMem hn, add_zero, recipK_of_lt (hω hA) hlt]
      · rw [Set.indicator_of_notMem (fun h => hlt h.2), zero_add]
        exact Set.indicator_le_self _ _ _
    · rw [Set.indicator_of_notMem (fun h => hA h.1), Set.indicator_of_notMem
        (fun h => hA (aliveSet_succ_subset b E κ K d j h)), Set.indicator_of_notMem hA, zero_add]
  calc _ ≤ _ := hsplit
    _ ≤ _ := hFub
    _ ≤ _ := hc

end BlockBand.Transmission.LawFinite
