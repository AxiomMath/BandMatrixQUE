module

public import BlockBand.Transmission.LawFinite.EntranceAux

/-!
# The transmission entrance bound, with absorption

Proof of `TransmissionEntranceBulk`: the probability that the conductance `g_r` drops to `K`
before `tW` steps is `O((1+K)t)`, uniformly on the bulk. Hypotheses `PassiveBoundsStatement`
(through `reciprocalDrift_holds` and `finiteCoreEntrance_of`) and `PassiveInitialScalarContract`
(`absorbedMoment` at `p = 1` for `Σ Eδ₀ ≤ Ct`, at `p = 2` for the domain exit).

* `entrance_arith`: the summed one-step errors (pure);
* `entrance_fixed`: at fixed `(W, E)`, `P(min_{r ≤ tW} g_r ≤ K) ≤ P(q₁ < aW) + [P(q₁ < aW) +
  Kd/(aW) + tC(Kd + 1 + Kκ + C₁) + Kd·C_A/W] + C₂/W`, `Kd = K·Li > K/(4η)`: `crossing_subset`,
  `telescope` of `alive_step`, `lintegral_recipK_le`;
* **`transmissionEntranceBulk_of hA hP : TransmissionEntranceBulk`** with
  `C = C₀(Li + 1 + Kκ + C₁)` (`C₀` of `ReciprocalDrift`, `C₁` of `absorbedMoment` at `p = 1`,
  `Li = 1/etaLow`, `Kκ` the profile bound), `A = 2`, and `FiniteCoreEntrance` at `r = 1` only.
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

/-- The summed errors (pure): `Kd·V ≤ Kd/(aW) + t·C(Kd + 1 + Kκ + C₁) + Kd·CA/W`, where
`V = (aW)⁻¹ + N(e₀ + (C/Kd)(C₁/W))`, `N ≤ tW`, `t ≤ 1`, `W ≥ 1`. -/
theorem entrance_arith {Kd a C CA Kκ C₁ t Wr N : ℝ} (hKd : 0 < Kd) (ha : 0 < a) (hC : 0 ≤ C)
    (hCA : 0 ≤ CA) (hKκ : 0 ≤ Kκ) (hC₁ : 0 ≤ C₁) (ht : 0 < t) (ht1 : t ≤ 1) (hW : 1 ≤ Wr)
    (hN : N ≤ t * Wr) :
    Kd * ((a * Wr)⁻¹ + N * ((C * (Wr⁻¹ + (Wr * Kd)⁻¹ + Kκ / (Wr ^ 2 * Kd)) + CA * Wr ^ (-2 : ℝ)) +
        C / Kd * (C₁ / Wr))) ≤
      Kd / (a * Wr) + t * (C * (Kd + 1 + Kκ + C₁)) + Kd * CA / Wr := by
  have hW0 : 0 < Wr := by linarith
  have hr : Wr ^ (-2 : ℝ) = (Wr ^ 2)⁻¹ := by
    rw [Real.rpow_neg hW0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hr]
  have hNW : N / Wr ≤ t := by rw [div_le_iff₀ hW0]; linarith
  have hNW2 : N / Wr ^ 2 ≤ t / Wr := by
    rw [div_le_div_iff₀ (by positivity) hW0]; nlinarith
  have e : Kd * ((a * Wr)⁻¹ + N * ((C * (Wr⁻¹ + (Wr * Kd)⁻¹ + Kκ / (Wr ^ 2 * Kd)) + CA * (Wr ^ 2)⁻¹) +
      C / Kd * (C₁ / Wr))) = Kd / (a * Wr) + (N / Wr) * (C * (Kd + 1 + C₁)) +
        (N / Wr ^ 2) * (C * Kκ + Kd * CA) := by
    field_simp; ring
  rw [e]
  have h1 : N / Wr * (C * (Kd + 1 + C₁)) ≤ t * (C * (Kd + 1 + C₁)) :=
    mul_le_mul_of_nonneg_right hNW (by positivity)
  have h2 : N / Wr ^ 2 * (C * Kκ + Kd * CA) ≤ t / Wr * (C * Kκ + Kd * CA) :=
    mul_le_mul_of_nonneg_right hNW2 (by positivity)
  have h3 : t / Wr * (C * Kκ) ≤ t * (C * Kκ) := by
    rw [div_mul_eq_mul_div]; exact div_le_self (by positivity) hW
  have h4 : t / Wr * (Kd * CA) ≤ Kd * CA / Wr := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hW0]; nlinarith [mul_nonneg hKd.le hCA]
  nlinarith

/-- **The entrance at fixed `(W, E)`**: the three pieces of `crossing_subset`,
with the telescoped `alive_step` for the middle one. -/
theorem entrance_fixed {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hW : 1 ≤ W) {κ : ℝ → ℝ} (hκ0 : ∀ s, 0 ≤ κ s) {Kκ : ℝ} (hKκ0 : 0 ≤ Kκ)
    (hKκ : ∀ s, κ s ≤ Kκ) {K t Kd d C CA a C₁ C₂ θ5 : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hKd : 0 < Kd) (hC : 0 ≤ C) (hCA : 0 ≤ CA) (ha : 0 < a) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hKK : K < 4 * etaZ b E * Kd)
    (hrd : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → jetDistance0 b E X ≤ d →
      Kd ≤ passiveMass b E X → ∀ ε : ℝ, 0 ≤ ε → ε ≤ Kκ / (W : ℝ) ^ 2 →
        ∫ f, recipK Kd (passiveMass b E (freshSchur E (absorbedInput X ε) f)) ∂freshLaw W b ≤
          driftBound C CA 2 ε W (passiveMass b E X) (jetDistance0 b E X))
    (hmom1 : ∀ r, 1 ≤ r → r ≤ W → ∫⁻ ω, ENNReal.ofReal (jetDistance0 b E
      (pathNearSchur b E κ W r ω)) ∂growthPathLaw W b ≤ ENNReal.ofReal (C₁ / W))
    (hmom2 : ∀ r, 1 ≤ r → r ≤ W → growthPathLaw W b
      {ω | d < jetDistance0 b E (pathNearSchur b E κ W r ω)} ≤ ENNReal.ofReal (C₂ / W ^ 2))
    (hcore : growthPathLaw W b {ω | passiveMass b E (pathNearSchur b E κ W 1 ω) < a * W} ≤
      ENNReal.ofReal θ5) (haW : Kd ≤ a * W) :
    growthPathLaw W b (entranceEvent b E κ K t W) ≤ ENNReal.ofReal θ5 +
      (ENNReal.ofReal θ5 + ENNReal.ofReal (Kd / (a * W) + t * (C * (Kd + 1 + Kκ + C₁)) +
        Kd * CA / W)) + ENNReal.ofReal (C₂ / W) := by
  set μ := growthPathLaw W b
  have hη := PassiveCovariance.etaZ_pos b E (by linarith) h1 h2
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  set N := ⌊t * W⌋₊
  have hN : (N : ℝ) ≤ t * W := Nat.floor_le (by positivity)
  have hNW : N ≤ W := by
    have : (N : ℝ) ≤ W := hN.trans (by nlinarith)
    exact_mod_cast this
  refine (measure_mono ((entranceEvent_subset hη hKK).trans (crossing_subset b E κ Kd d N))).trans ?_
  refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add ?_
    ((measure_biUnion_finset_le _ _).trans ?_))) ((measure_biUnion_finset_le _ _).trans ?_))
  · exact (measure_mono fun ω (hω : _ < Kd) => (show _ < a * W from hω.trans_le haW)).trans hcore
  · -- the alive crossings
    set e₀ := C * ((W : ℝ)⁻¹ + ((W : ℝ) * Kd)⁻¹ + Kκ / ((W : ℝ) ^ 2 * Kd)) + CA * (W : ℝ) ^ (-2 : ℝ)
    have he₀ : 0 ≤ e₀ := by positivity
    have htel := telescope (c := ENNReal.ofReal Kd⁻¹) (e := ENNReal.ofReal e₀)
      (Φ := fun j => ∫⁻ ω, (aliveSet b E κ W Kd d j).indicator (fun ω =>
        ENNReal.ofReal (recipK Kd (passiveMass b E (pathNearSchur b E κ W j ω)))) ω ∂μ)
      (D := fun j => ENNReal.ofReal (C / Kd) * ∫⁻ ω, ENNReal.ofReal (jetDistance0 b E
        (pathNearSchur b E κ W j ω)) ∂μ)
      (fun j hj => alive_step hb0 hb h1 h2 hW hκ0 hKκ hKd hC hrd j hj) N
    have hΦ1 : ∫⁻ ω, (aliveSet b E κ W Kd d 1).indicator (fun ω =>
        ENNReal.ofReal (recipK Kd (passiveMass b E (pathNearSchur b E κ W 1 ω)))) ω ∂μ ≤
        ENNReal.ofReal Kd⁻¹ * μ {ω | passiveMass b E (pathNearSchur b E κ W 1 ω) < a * W} +
          ENNReal.ofReal (a * W)⁻¹ :=
      (lintegral_mono fun ω => Set.indicator_le_self _ _ ω).trans
        (lintegral_recipK_le (by positivity))
    set y := e₀ + C / Kd * (C₁ / W)
    have hy : 0 ≤ y := by positivity
    have hsum : ∑ j ∈ Finset.Ico 1 N, (ENNReal.ofReal e₀ + ENNReal.ofReal (C / Kd) *
        ∫⁻ ω, ENNReal.ofReal (jetDistance0 b E (pathNearSchur b E κ W j ω)) ∂μ) ≤
        ENNReal.ofReal (N * y) := by
      refine (Finset.sum_le_card_nsmul _ _ (ENNReal.ofReal y) fun j hj => ?_).trans ?_
      · obtain ⟨hj1, hjN⟩ := Finset.mem_Ico.mp hj
        refine (add_le_add le_rfl (mul_le_mul_right (hmom1 j hj1 (by omega)) _)).trans ?_
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add he₀ (by positivity)]
      · rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hy)
        rw [Nat.card_Ico]; exact_mod_cast Nat.sub_le N 1
    have hmain : ENNReal.ofReal Kd⁻¹ * ∑ j ∈ Finset.Ico 1 N, μ (aliveSet b E κ W Kd d j ∩
        {ω | passiveMass b E (pathNearSchur b E κ W (j + 1) ω) < Kd}) ≤
        ENNReal.ofReal Kd⁻¹ * μ {ω | passiveMass b E (pathNearSchur b E κ W 1 ω) < a * W} +
          ENNReal.ofReal ((a * W)⁻¹ + N * y) := by
      refine htel.trans ((add_le_add hΦ1 hsum).trans (le_of_eq ?_))
      rw [add_assoc, ENNReal.ofReal_add (by positivity) (by positivity)]
    have hone : ENNReal.ofReal Kd * ENNReal.ofReal Kd⁻¹ = 1 := by
      rw [← ENNReal.ofReal_mul hKd.le, mul_inv_cancel₀ hKd.ne', ENNReal.ofReal_one]
    calc ∑ j ∈ Finset.Ico 1 N, μ (aliveSet b E κ W Kd d j ∩
          {ω | passiveMass b E (pathNearSchur b E κ W (j + 1) ω) < Kd})
        = ENNReal.ofReal Kd * (ENNReal.ofReal Kd⁻¹ * ∑ j ∈ Finset.Ico 1 N, μ (aliveSet b E κ W
          Kd d j ∩ {ω | passiveMass b E (pathNearSchur b E κ W (j + 1) ω) < Kd})) := by
          rw [← mul_assoc, hone, one_mul]
      _ ≤ ENNReal.ofReal Kd * (ENNReal.ofReal Kd⁻¹ * μ {ω | passiveMass b E
          (pathNearSchur b E κ W 1 ω) < a * W} + ENNReal.ofReal ((a * W)⁻¹ + N * y)) :=
          mul_le_mul_right hmain _
      _ = μ {ω | passiveMass b E (pathNearSchur b E κ W 1 ω) < a * W} +
          ENNReal.ofReal (Kd * ((a * W)⁻¹ + N * y)) := by
          rw [mul_add, ← mul_assoc, hone, one_mul, ← ENNReal.ofReal_mul hKd.le]
      _ ≤ _ := add_le_add hcore (ENNReal.ofReal_le_ofReal (entrance_arith hKd ha hC hCA hKκ0
          hC₁ ht ht1 hW1 hN))
  · -- the domain exit
    refine (Finset.sum_le_card_nsmul _ _ (ENNReal.ofReal (C₂ / W ^ 2)) fun r hr => ?_).trans ?_
    · obtain ⟨hr1, hrN⟩ := Finset.mem_Icc.mp hr
      exact hmom2 r hr1 (by omega)
    · rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hNW' : (N : ℝ) ≤ W := by exact_mod_cast hNW
      calc (N : ℝ) * (C₂ / (W : ℝ) ^ 2) ≤ W * (C₂ / (W : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hNW' (by positivity)
        _ = C₂ / W := by field_simp

/-- **`TransmissionEntranceBulk`** (with absorption) from `PassiveLayer.PassiveBoundsStatement`
and `PassiveInitialScalarContract` (`absorbedMoment` at `p = 1, 2`; the latter is proved as
`Assembly.passiveInitialScalar_holds`).
-/
theorem transmissionEntranceBulk_of (hA : PassiveLayer.PassiveBoundsStatement)
    (hP : PassiveInitialScalarContract) : TransmissionEntranceBulk := by
  intro b hb0 hb κI hκI κ hκ
  obtain ⟨-, hκ0, K0, hK0⟩ := id hκ
  set Kκ := max K0 0
  have hKκ0 : 0 ≤ Kκ := le_max_right _ _
  have hKκ : ∀ s, κ s ≤ Kκ := fun s => (hK0 s).trans (le_max_left _ _)
  obtain ⟨d, C₀, hd, hRD⟩ := reciprocalDrift_holds hA b hb0 hb κI Kκ hκI hKκ0
  obtain ⟨C₁, W₁, hC₁⟩ := hP.absorbedMoment b hb0 hb κI 1 Kκ 1 hκI hKκ0 le_rfl
  obtain ⟨C₂, W₂, hC₂⟩ := hP.absorbedMoment b hb0 hb κI 1 Kκ 2 hκI hKκ0 (by norm_num)
  have hηL : 0 < etaLow b κI := etaLow_pos (by linarith) hκI
  set Li := (etaLow b κI)⁻¹
  have hLi0 : 0 < Li := inv_pos.mpr hηL
  set C₀' := max C₀ 0
  set C₁' := max C₁ 0
  set C₂' := max C₂ 0
  refine ⟨C₀' * (Li + 1 + Kκ + C₁'), fun K t θ hK ht ht1 hθ => ?_⟩
  set Kd := K * Li
  have hKd : 0 < Kd := by positivity
  obtain ⟨CA, W₃, hCA⟩ := hRD Kd 2 hKd two_pos
  set CA' := max CA 0
  obtain ⟨a, ha, W₄, hcore⟩ := finiteCoreEntrance_of hA hP b hb0 hb κI hκI κ hκ
    (θ / 5) (by positivity) 1 le_rfl
  set M := Kd / a + 5 * Kd / (a * θ) + 5 * Kd * CA' / θ + 5 * C₂' ^ 2 / (d ^ 2 * θ) + 1
  refine ⟨max (max (max W₁ W₂) (max W₃ W₄)) ⌈M⌉₊, fun W hW E hE => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW₁, hW₂⟩, hW₃, hW₄⟩, hWM⟩ := hW
  have hMr : M ≤ (W : ℝ) := (Nat.le_ceil M).trans (by exact_mod_cast hWM)
  have hθ5 : 0 < θ / 5 := by positivity
  have hpos : 0 ≤ Kd / a + 5 * Kd / (a * θ) + 5 * Kd * CA' / θ + 5 * C₂' ^ 2 / (d ^ 2 * θ) := by
    positivity
  have hW1r : (1 : ℝ) ≤ W := by simp only [M] at hMr; linarith
  have hW1 : 1 ≤ W := by exact_mod_cast hW1r
  have hWp : (0 : ℝ) < W := by linarith
  have h1 : -2 < E := by linarith [hE.1]
  have h2 : E < 2 := by linarith [hE.2]
  have hη := PassiveCovariance.etaZ_pos b E (by linarith) h1 h2
  have hLi : (etaZ b E)⁻¹ ≤ Li := inv_anti₀ hηL (etaLow_le (by linarith) hκI hE)
  have hηLi : 1 ≤ etaZ b E * Li := by
    have := mul_le_mul_of_nonneg_left hLi hη.le; rwa [mul_inv_cancel₀ hη.ne'] at this
  have hKK : K < 4 * etaZ b E * Kd := by
    have : K * 1 ≤ K * (etaZ b E * Li) := mul_le_mul_of_nonneg_left hηLi hK.le
    simp only [Kd]; nlinarith
  -- the reciprocal drift with nonnegative constants
  have hrd : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → jetDistance0 b E X ≤ d →
      Kd ≤ passiveMass b E X → ∀ ε : ℝ, 0 ≤ ε → ε ≤ Kκ / (W : ℝ) ^ 2 →
        ∫ f, recipK Kd (passiveMass b E (freshSchur E (absorbedInput X ε) f)) ∂freshLaw W b ≤
          driftBound C₀' CA' 2 ε W (passiveMass b E X) (jetDistance0 b E X) := by
    intro X hY hδ hKq ε hε0 hεK
    refine (hCA W hW₃ E hE X hY ε hε0 hεK hδ hKq).trans ?_
    have hq : 0 < passiveMass b E X := hKd.trans_le hKq
    have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
    have hbr : 0 ≤ (W : ℝ)⁻¹ + jetDistance0 b E X / passiveMass b E X +
        ((W : ℝ) * passiveMass b E X)⁻¹ + ε / passiveMass b E X := by positivity
    have hWA : 0 ≤ (W : ℝ) ^ (-(2 : ℝ)) := by positivity
    rw [driftBound]
    have := mul_le_mul_of_nonneg_right (le_max_left C₀ 0) hbr
    have := mul_le_mul_of_nonneg_right (le_max_left CA 0) hWA
    linarith
  -- the moments of `δ₀`
  have hmom1 : ∀ r, 1 ≤ r → r ≤ W → ∫⁻ ω, ENNReal.ofReal (jetDistance0 b E
      (pathNearSchur b E κ W r ω)) ∂growthPathLaw W b ≤ ENNReal.ofReal (C₁' / W) := by
    intro r hr hrW
    have h := hC₁ W hW₁ E hE r hr (by rw [one_mul]; exact_mod_cast hrW) (layerAbsorption W κ r)
      (layerAbsorption_mem hκ0 hKκ r)
    have hm : AEStronglyMeasurable (fun ω => jetDistance0 b E (pathNearSchur b E κ W r ω))
        (growthPathLaw W b) := ((measurable_jetDistance0 b E).comp
          ((pathNearSchur_adapted b E κ W r).mono (Generator.growthSigma_le W r) le_rfl)).aestronglyMeasurable
    have h' : eLpNorm (fun ω => jetDistance0 b E (pathNearSchur b E κ W r ω)) (ENNReal.ofReal 1)
        (growthPathLaw W b) ≤ ENNReal.ofReal (C₁ / W) := h
    rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm hm] at h'
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) (h'.trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hWp.le)))
    exact (Real.enorm_of_nonneg (norm_nonneg _)).symm
  have hmom2 : ∀ r, 1 ≤ r → r ≤ W → growthPathLaw W b
      {ω | d < jetDistance0 b E (pathNearSchur b E κ W r ω)} ≤
        ENNReal.ofReal (C₂' ^ 2 / d ^ 2 / W ^ 2) := by
    intro r hr hrW
    have h := hC₂ W hW₂ E hE r hr (by rw [one_mul]; exact_mod_cast hrW) (layerAbsorption W κ r)
      (layerAbsorption_mem hκ0 hKκ r)
    have h' : eLpNorm (fun ω => jetDistance0 b E (pathNearSchur b E κ W r ω)) (ENNReal.ofReal 2)
        (growthPathLaw W b) ≤ ENNReal.ofReal (C₂' / W) :=
      h.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hWp.le))
    refine (markov_ofReal _ (fun _ => norm_nonneg _) two_pos hd (by positivity) h').trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [Real.rpow_two, Real.rpow_two]; field_simp
  have haW : Kd ≤ a * W := by
    have : Kd / a ≤ W := by
      have : 0 ≤ 5 * Kd / (a * θ) + 5 * Kd * CA' / θ + 5 * C₂' ^ 2 / (d ^ 2 * θ) := by positivity
      simp only [M] at hMr; linarith
    rwa [div_le_iff₀ ha, mul_comm] at this
  have hF := entrance_fixed (C₂ := C₂' ^ 2 / d ^ 2) hb0 hb h1 h2 hW1 hκ0 hKκ0 hKκ ht ht1 hKd
    (le_max_right C₀ 0) (le_max_right CA 0) ha (le_max_right C₁ 0) (by positivity) hKK hrd hmom1
    hmom2
    (hcore W hW₄ E hE) haW
  refine hF.trans ?_
  -- the final arithmetic
  have hx1 : Kd / (a * W) ≤ θ / 5 := by
    rw [div_le_iff₀ (by positivity)]
    have : 5 * Kd / (a * θ) ≤ W := by
      have : 0 ≤ Kd / a + 5 * Kd * CA' / θ + 5 * C₂' ^ 2 / (d ^ 2 * θ) := by positivity
      simp only [M] at hMr; linarith
    rw [div_le_iff₀ (by positivity)] at this; nlinarith
  have hx2 : Kd * CA' / W ≤ θ / 5 := by
    rw [div_le_iff₀ hWp]
    have : 5 * Kd * CA' / θ ≤ W := by
      have : 0 ≤ Kd / a + 5 * Kd / (a * θ) + 5 * C₂' ^ 2 / (d ^ 2 * θ) := by positivity
      simp only [M] at hMr; linarith
    rw [div_le_iff₀ hθ] at this; nlinarith
  have hx3 : C₂' ^ 2 / d ^ 2 / W ≤ θ / 5 := by
    rw [div_le_iff₀ hWp, div_le_iff₀ (by positivity)]
    have : 5 * C₂' ^ 2 / (d ^ 2 * θ) ≤ W := by
      have : 0 ≤ Kd / a + 5 * Kd / (a * θ) + 5 * Kd * CA' / θ := by positivity
      simp only [M] at hMr; linarith
    rw [div_le_iff₀ (by positivity)] at this; nlinarith
  have hx4 : t * (C₀' * (Kd + 1 + Kκ + C₁')) ≤ C₀' * (Li + 1 + Kκ + C₁') * (1 + K) * t := by
    have hC0 : 0 ≤ C₀' := le_max_right _ _
    have hC1 : 0 ≤ C₁' := le_max_right _ _
    have : Kd + 1 + Kκ + C₁' ≤ (Li + 1 + Kκ + C₁') * (1 + K) := by
      simp only [Kd]; nlinarith
    have := mul_le_mul_of_nonneg_left this hC0
    nlinarith
  rw [← ENNReal.ofReal_add hθ5.le (by positivity), ← ENNReal.ofReal_add hθ5.le (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end BlockBand.Transmission.LawFinite
