module

public import BlockBand.Endpoints.Response.NearSchattenExitTools

/-!
# The dissipation mass after the stop

Part of the proof of the near-Schatten decay theorem: on a trace stop, the fixed clock/current
moments remove the stops.

**Proved here** (fixed width `W`; input: a.s. unitarity from `ConditionalBlockGUECount`).
* `nsx_drift_lower`: the word identity for the drift of `Tr(QP)` after the injection,
  `|𝒜 Tr(QP)| ≥ (D/2) g Tr A` (`nsf_polyValue_wordDrift_clockWord` at `r = 0`).
* `nsx_mass_le`: `Σ_{j₁≤j≤j₂} W⁻¹ E[1{j≥σ}(-𝒢_ε(j))⁺] ≤ M_ε E[1{σ≤j₂} X_W]
  + (u₂-u₁+2)(D/2)M_ε E[1{σ≤j₂} (sup Tr Q)²]`, where `X_W = Σ W⁻¹|𝒜 Tr(QP)|` is the drift
  total variation of `FullSourceStopsContract.compensatorUI` (`nss_abs_genExpr_le`:
  `|𝒢_ε| ≤ (D/2)M_ε(g Tr A + (Tr A)²)`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Filter Topology Set Finset
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

variable {W : ℕ}

/-- The clock polynomial `Tr(QP)` (`π(x) = x`). -/
def nsxClockOne : TracePoly 0 1 := nsfClockPoly (fun _ => 1) 1

theorem nsx_isOrdinaryPoly_clockOne : IsOrdinaryPoly nsxClockOne :=
  nsf_isOrdinaryPoly_clockPoly _ _

/-- The drift total variation `Σ_{εW≤j<TW} W⁻¹|𝒜_{(j+1)/W} Tr(QP)|` of `compensatorUI`
(`ε = u₁/2`, `T = u₂ + 1`). -/
def nsxDrift (b E : ℝ) (q : ℝ → ℝ) (u₁ u₂ : ℝ) (W : ℕ) (ω : GrowthPath W) : ℝ≥0∞ :=
  ∑ j ∈ (Finset.range ⌊(u₂ + 1) * W⌋₊).filter (fun j : ℕ => u₁ / 2 * W ≤ (j : ℝ)),
    (W : ℝ≥0∞)⁻¹ * ‖polyValue b E (noTags W) (fun _ => q) W j ω
      (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) nsxClockOne)‖ₑ

theorem nsx_measurable_drift (b E : ℝ) (q : ℝ → ℝ) (u₁ u₂ : ℝ) (W : ℕ) :
    Measurable (nsxDrift b E q u₁ u₂ W) := by
  unfold nsxDrift
  exact Finset.measurable_sum _ fun j _ =>
    measurable_const.mul (nss_measurable_polyValue b E (noTags W) _ W j _).enorm

/-- **The drift of `Tr(QP)` after the injection**: `(D/2) g Tr A ≤ |𝒜_t Tr(QP)|` (`q(t) = 0`,
`𝕊` unitary). -/
theorem nsx_drift_lower {b E : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2) {q : ℝ → ℝ}
    (hq : ∀ x, 0 ≤ q x) {j : ℕ} {ω : GrowthPath W}
    (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1) {t : ℝ}
    (hqt : q t = 0) :
    transportD0 b E / 2 * nsgConductance (scatteringMatrix b E W j ω) *
        (nearClock b E W j q ω).trace.re ≤
      ‖polyValue b E (noTags W) (fun _ => q) W j ω
        (wordGenerator b E (fun _ => q) t nsxClockOne)‖ := by
  have e : polyValue b E (noTags W) (fun _ => q) W j ω
      (wordGenerator b E (fun _ => q) t nsxClockOne) =
      -(((transportD0 b E / 2 : ℝ) : ℂ) * ((1 / 2 : ℂ) * ((pathCurrent b E W j ω) ^ 2).trace) *
        nsfT b E q W j ω 1) := by
    unfold nsxClockOne
    rw [nsf_polyValue_wordGenerator_clockPoly b E q W j ω (noTags W) (fun _ => 1) 1 t hqt,
      Finset.sum_range_one, nsf_polyValue_wordDrift_clockWord b E q W j ω (noTags W)
        (transportD0 b E) 0]
    simp
  rw [e, norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by have := (ns_transportD0_pos hb hE hE').le; positivity)]
  have hg0 := nsg_conductance_nonneg hS
  have hA0 := (trace_nearClock_le b E W j q hq ω).1
  have hg : nsgConductance (scatteringMatrix b E W j ω) ≤
      ‖(1 / 2 : ℂ) * ((pathCurrent b E W j ω) ^ 2).trace‖ := by
    refine le_trans (le_of_eq ?_) (Complex.re_le_norm _)
    rw [nsg_pathCurrent_eq]
    simp only [Complex.mul_re]
    norm_num
    ring
  have hT : (nearClock b E W j q ω).trace.re ≤ ‖nsfT b E q W j ω 1‖ := by
    unfold nsfT; rw [pow_one]; exact Complex.re_le_norm _
  have hD := (ns_transportD0_pos hb hE hE').le
  gcongr

/-- **After the stop, one length** (`𝕊` unitary, after the injection, `j ≤ j₂` in the window):
`1{j≥σ}(-𝒢_ε)⁺ ≤ 1{σ≤j₂}(M_ε|𝒜 Tr(QP)| + (D/2)M_ε (sup Tr Q)²)`. -/
theorem nsx_mass_pointwise {b E p ε : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hε : 0 < ε) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {K u₁ u₂ : ℝ} {j j₂ : ℕ}
    {ω : GrowthPath W} (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1)
    (hqt : q (((j + 1 : ℕ) : ℝ) / W) = 0) (hj1 : u₁ / 2 * W ≤ j)
    (hjT : (j : ℝ) ≤ (u₂ + 1) * W) (hj2 : j ≤ j₂) :
    (nsfAlive b E q K u₁ W j)ᶜ.indicator
        (fun ω => ENNReal.ofReal (-nsgGenExpr b E p ε q W j ω)) ω ≤
      (nsfAlive b E q K u₁ W j₂)ᶜ.indicator (fun ω => ENNReal.ofReal (nssGenConst p ε) *
          ‖polyValue b E (noTags W) (fun _ => q) W j ω
            (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) nsxClockOne)‖ₑ +
        ENNReal.ofReal (transportD0 b E / 2 * nssGenConst p ε) *
          nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ 2) ω := by
  by_cases hal : ω ∈ nsfAlive b E q K u₁ W j
  · rw [Set.indicator_of_notMem (show ω ∉ (nsfAlive b E q K u₁ W j)ᶜ from fun h => h hal)]
    exact zero_le
  have hd : ω ∉ nsfAlive b E q K u₁ W j₂ := fun h => hal
    (show (j : ℕ∞) < _ from lt_of_le_of_lt (by exact_mod_cast hj2) h)
  rw [Set.indicator_of_mem (show ω ∈ (nsfAlive b E q K u₁ W j)ᶜ from hal),
    Set.indicator_of_mem (show ω ∈ (nsfAlive b E q K u₁ W j₂)ᶜ from hd)]
  have hM : 0 ≤ nssGenConst p ε :=
    (mul_nonneg hp0 (Real.rpow_nonneg hε.le _)).trans (le_max_left _ _)
  have hD := (ns_transportD0_pos hb hE hE').le
  have hG := nss_abs_genExpr_le hb hE hE' hp0 hp1 hε hq hS
  have hdr := nsx_drift_lower hb hE hE' hq hS hqt
  have hA0 := (trace_nearClock_le b E W j q hq ω).1
  set A := (nearClock b E W j q ω).trace.re
  set gen := ‖polyValue b E (noTags W) (fun _ => q) W j ω
    (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) nsxClockOne)‖
  have hreal : -nsgGenExpr b E p ε q W j ω ≤
      nssGenConst p ε * gen + transportD0 b E / 2 * nssGenConst p ε * A ^ 2 := by
    have h1 := neg_le_abs (nsgGenExpr b E p ε q W j ω)
    have h2 : nssGenConst p ε * (transportD0 b E / 2 *
        nsgConductance (scatteringMatrix b E W j ω) * A) ≤ nssGenConst p ε * gen :=
      mul_le_mul_of_nonneg_left hdr hM
    nlinarith
  calc ENNReal.ofReal (-nsgGenExpr b E p ε q W j ω)
      ≤ ENNReal.ofReal (nssGenConst p ε * gen + transportD0 b E / 2 * nssGenConst p ε * A ^ 2) :=
        ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal (nssGenConst p ε * gen) +
        ENNReal.ofReal (transportD0 b E / 2 * nssGenConst p ε * A ^ 2) := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (nssGenConst p ε) * ENNReal.ofReal gen +
        ENNReal.ofReal (transportD0 b E / 2 * nssGenConst p ε) * ENNReal.ofReal A ^ 2 := by
        rw [ENNReal.ofReal_mul hM, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hA0]
    _ ≤ _ := by
        rw [ofReal_norm]
        gcongr
        exact nsx_trA_le_supQ b E hq hj1 hjT ω

/-- `Σ_{j₁≤j≤j₂} W⁻¹ ≤ u₂ - u₁ + 2`. -/
theorem nsx_card_le {u₁ u₂ : ℝ} (hW : 0 < W) (hu₁ : 0 ≤ u₁) (hu : u₁ ≤ u₂) :
    ((Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊).card : ℝ≥0∞) * (W : ℝ≥0∞)⁻¹ ≤
      ENNReal.ofReal (u₂ - u₁ + 2) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h1 : (W : ℝ) * u₁ < ⌊(W : ℝ) * u₁⌋₊ + 1 := Nat.lt_floor_add_one _
  have h2 : (⌊(W : ℝ) * u₂⌋₊ : ℝ) ≤ W * u₂ := Nat.floor_le (mul_nonneg hW'.le (by linarith))
  rw [Nat.card_Icc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast W,
    ← ENNReal.ofReal_inv_of_pos hW', ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← div_eq_mul_inv, div_le_iff₀ hW']
  rcases le_or_gt ⌊(W : ℝ) * u₁⌋₊ (⌊(W : ℝ) * u₂⌋₊ + 1) with h | h
  · rw [Nat.cast_sub h]; push_cast; nlinarith
  · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
    have : 0 ≤ u₂ - u₁ + 2 := by linarith
    positivity

/-- **The dissipation mass after the stop at a fixed width.** -/
theorem nsx_mass_le (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    {b E p ε : ℝ} (hb : 0 < b) (hb1 : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hε : 0 < ε) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {K u₁ u₂ : ℝ} (hu₁ : 0 < u₁)
    (hu : u₁ ≤ u₂) (hW : 0 < W) (hjW : u₁ / 2 * W ≤ ⌊(W : ℝ) * u₁⌋₊)
    (hqt : ∀ j, ⌊(W : ℝ) * u₁⌋₊ ≤ j → q (((j + 1 : ℕ) : ℝ) / W) = 0) :
    ∑ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, (W : ℝ≥0∞)⁻¹ *
        ∫⁻ ω, (nsfAlive b E q K u₁ W j)ᶜ.indicator
          (fun ω => ENNReal.ofReal (-nsgGenExpr b E p ε q W j ω)) ω ∂growthPathLaw W b ≤
      ENNReal.ofReal (nssGenConst p ε) *
          ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ.indicator
            (nsxDrift b E q u₁ u₂ W) ω ∂growthPathLaw W b +
        ENNReal.ofReal ((u₂ - u₁ + 2) * (transportD0 b E / 2 * nssGenConst p ε)) *
          ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ.indicator
            (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ 2) ω ∂growthPathLaw W b := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  set j₁ := ⌊(W : ℝ) * u₁⌋₊ with hj₁
  set j₂ := ⌊(W : ℝ) * u₂⌋₊ with hj₂
  set D := (nsfAlive b E q K u₁ W j₂)ᶜ with hDdef
  set S := nsxSupQ b E q (u₁ / 2) (u₂ + 1) W with hSdef
  set Mε := ENNReal.ofReal (nssGenConst p ε) with hMε
  set c' := ENNReal.ofReal (transportD0 b E / 2 * nssGenConst p ε) with hc'
  set gen : ℕ → GrowthPath W → ℝ≥0∞ := fun j ω => ‖polyValue b E (noTags W) (fun _ => q) W j ω
    (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) nsxClockOne)‖ₑ with hgen
  have hj₂le : (j₂ : ℝ) ≤ W * u₂ := Nat.floor_le (mul_nonneg hW'.le (by linarith))
  have hDm : MeasurableSet D := (nss_measurableSet_alive b E (noTags W) q K (u₁ / 2) W j₂).compl
  have hSm := nsx_measurable_supQ b E q (u₁ / 2) (u₂ + 1) W
  have hgm : ∀ j, Measurable (D.indicator (fun ω => Mε * gen j ω + c' * S ω ^ 2)) := fun j =>
    ((measurable_const.mul (nss_measurable_polyValue b E (noTags W) _ W j _).enorm).add
      (measurable_const.mul (hSm.pow_const 2))).indicator hDm
  have hwin : ∀ j ∈ Finset.Icc j₁ j₂, u₁ / 2 * W ≤ j ∧ (j : ℝ) ≤ (u₂ + 1) * W := fun j hj => by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    exact ⟨hjW.trans (by exact_mod_cast h1), (Nat.cast_le.2 h2).trans (by nlinarith)⟩
  have hsub : Finset.Icc j₁ j₂ ⊆
      (Finset.range ⌊(u₂ + 1) * W⌋₊).filter (fun j : ℕ => u₁ / 2 * W ≤ (j : ℝ)) := by
    intro j hj
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_of_succ_le (Nat.le_floor ?_), (hwin j hj).1⟩
    have : (j : ℝ) ≤ j₂ := by exact_mod_cast h2
    push_cast; nlinarith
  calc _ ≤ ∑ j ∈ Finset.Icc j₁ j₂, (W : ℝ≥0∞)⁻¹ *
        ∫⁻ ω, D.indicator (fun ω => Mε * gen j ω + c' * S ω ^ 2) ω ∂growthPathLaw W b := by
        refine Finset.sum_le_sum fun j hj => ?_
        refine mul_le_mul' le_rfl (lintegral_mono_ae ?_)
        filter_upwards [nsg_ae_scattering_unitary hCount hb1 hE hE' hW j] with ω hS
        exact nsx_mass_pointwise hb hE hE' hp0 hp1 hε hq hS (hqt j (Finset.mem_Icc.1 hj).1)
          (hwin j hj).1 (hwin j hj).2 (Finset.mem_Icc.1 hj).2
    _ = ∫⁻ ω, ∑ j ∈ Finset.Icc j₁ j₂, (W : ℝ≥0∞)⁻¹ *
          D.indicator (fun ω => Mε * gen j ω + c' * S ω ^ 2) ω ∂growthPathLaw W b := by
        rw [lintegral_finsetSum _ fun j _ => (hgm j).const_mul _]
        exact Finset.sum_congr rfl fun j _ => (lintegral_const_mul _ (hgm j)).symm
    _ ≤ ∫⁻ ω, (Mε * D.indicator (nsxDrift b E q u₁ u₂ W) ω +
          ENNReal.ofReal ((u₂ - u₁ + 2) * (transportD0 b E / 2 * nssGenConst p ε)) *
            D.indicator (fun ω => S ω ^ 2) ω) ∂growthPathLaw W b := by
        refine lintegral_mono fun ω => ?_
        by_cases hω : ω ∈ D
        · simp only [Set.indicator_of_mem hω]
          simp only [mul_add, Finset.sum_add_distrib]
          gcongr
          · calc _ = Mε * ∑ j ∈ Finset.Icc j₁ j₂, (W : ℝ≥0∞)⁻¹ * gen j ω := by
                  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
              _ ≤ _ := by
                  gcongr
                  exact Finset.sum_le_sum_of_subset hsub
          · rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
              ENNReal.ofReal_mul (by linarith), ← hc']
            calc _ ≤ ENNReal.ofReal (u₂ - u₁ + 2) * (c' * S ω ^ 2) :=
                  mul_le_mul' (nsx_card_le hW hu₁.le hu) le_rfl
              _ = _ := by ring
        · simp only [Set.indicator_of_notMem hω, mul_zero, Finset.sum_const_zero]
          exact zero_le
    _ = _ := by
        rw [lintegral_add_left (((nsx_measurable_drift b E q u₁ u₂ W).indicator hDm).const_mul Mε),
          lintegral_const_mul _ ((nsx_measurable_drift b E q u₁ u₂ W).indicator hDm),
          lintegral_const_mul _ ((hSm.pow_const 2).indicator hDm)]

end BlockBand.Endpoints
