module

public import BlockBand.Endpoints.Response.RemoteHigherExitTools

/-!
# The dissipation mass of the higher functional after the stop

`rhx_mass_le` bounds, at a fixed width, the time-summed dissipation of the higher regularized
functional on the complement of the stop survival event by the post-stop drifts of the clock
polynomials and the probability that the stop has occurred.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Filter Topology Set Finset
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-- The dissipation mass of the higher functional after the stop at a fixed width. -/
theorem rhx_mass_le (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    {b E p r ε : ℝ} (hb : 0 < b) (hb1 : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hr : 1 ≤ r) (hε : 0 < ε) {k : ℕ} (hrk : r ≤ k + 1) {q : ℝ → ℝ}
    (hq : ∀ x, 0 ≤ q x) {K u₁ u₂ : ℝ} (hu₁ : 0 < u₁) (hu : u₁ ≤ u₂) {W : ℕ} (hW : 0 < W)
    (hjW : u₁ / 2 * W ≤ ⌊(W : ℝ) * u₁⌋₊)
    (hqt : ∀ j, ⌊(W : ℝ) * u₁⌋₊ ≤ j → q (((j + 1 : ℕ) : ℝ) / W) = 0) :
    ∑ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, (W : ℝ≥0∞)⁻¹ *
        ∫⁻ ω, (nsfAlive b E q K u₁ W j)ᶜ.indicator
          (fun ω => ENNReal.ofReal (-rhlGenExpr b E p r ε q W j ω)) ω ∂growthPathLaw W b ≤
      ENNReal.ofReal (rhxK1 p r ε k) *
          ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ.indicator
            (rhxDrift b E q u₁ u₂ nsxClockOne W) ω ∂growthPathLaw W b +
        ENNReal.ofReal (rhxK1 p r ε k) *
          ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ.indicator
            (rhxDrift b E q u₁ u₂ (rhxPowPoly k) W) ω ∂growthPathLaw W b +
        ENNReal.ofReal ((u₂ - u₁ + 2) * rhxK2 b E p r ε k) *
          growthPathLaw W b (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ +
        ENNReal.ofReal ((u₂ - u₁ + 2) * rhxK2 b E p r ε k) *
          ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ.indicator
            (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (k + 3)) ω ∂growthPathLaw W b := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  obtain ⟨hK1, hK2⟩ := rhx_K_nonneg hb hE hE' hp0 hr hε k
  have hL : 0 ≤ u₂ - u₁ + 2 := by linarith
  set j₁ := ⌊(W : ℝ) * u₁⌋₊ with hj₁
  set j₂ := ⌊(W : ℝ) * u₂⌋₊ with hj₂
  set D := (nsfAlive b E q K u₁ W j₂)ᶜ with hDdef
  set S := nsxSupQ b E q (u₁ / 2) (u₂ + 1) W with hSdef
  set a := ENNReal.ofReal (rhxK1 p r ε k) with ha
  set c := ENNReal.ofReal (rhxK2 b E p r ε k) with hc
  set g1 : ℕ → GrowthPath W → ℝ≥0∞ := fun j ω => ‖polyValue b E (noTags W) (fun _ => q) W j ω
    (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) nsxClockOne)‖ₑ with hg1
  set gn : ℕ → GrowthPath W → ℝ≥0∞ := fun j ω => ‖polyValue b E (noTags W) (fun _ => q) W j ω
    (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (rhxPowPoly k))‖ₑ with hgn
  have hj₂le : (j₂ : ℝ) ≤ W * u₂ := Nat.floor_le (mul_nonneg hW'.le (by linarith))
  have hDm : MeasurableSet D := (nss_measurableSet_alive b E (noTags W) q K (u₁ / 2) W j₂).compl
  have hSm := nsx_measurable_supQ b E q (u₁ / 2) (u₂ + 1) W
  have hgm : ∀ j, Measurable (D.indicator (fun ω => a * g1 j ω + a * gn j ω + c +
      c * S ω ^ (k + 3))) := fun j =>
    ((((measurable_const.mul (nss_measurable_polyValue b E (noTags W) _ W j _).enorm).add
      (measurable_const.mul (nss_measurable_polyValue b E (noTags W) _ W j _).enorm)).add
        measurable_const).add (measurable_const.mul (hSm.pow_const _))).indicator hDm
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
  have hcard := nsx_card_le (W := W) hW hu₁.le hu
  have hLc : ENNReal.ofReal ((u₂ - u₁ + 2) * rhxK2 b E p r ε k) =
      ENNReal.ofReal (u₂ - u₁ + 2) * c := by rw [ENNReal.ofReal_mul hL]
  calc _ ≤ ∑ j ∈ Finset.Icc j₁ j₂, (W : ℝ≥0∞)⁻¹ *
        ∫⁻ ω, D.indicator (fun ω => a * g1 j ω + a * gn j ω + c + c * S ω ^ (k + 3)) ω
          ∂growthPathLaw W b := by
        refine Finset.sum_le_sum fun j hj => ?_
        refine mul_le_mul' le_rfl (lintegral_mono_ae ?_)
        filter_upwards [nsg_ae_scattering_unitary hCount hb1 hE hE' hW j] with ω hS
        exact rhx_mass_pointwise hb hE hE' hp0 hp1 hr hε hrk hq hS (hqt j (Finset.mem_Icc.1 hj).1)
          (hwin j hj).1 (hwin j hj).2 (Finset.mem_Icc.1 hj).2
    _ = ∫⁻ ω, ∑ j ∈ Finset.Icc j₁ j₂, (W : ℝ≥0∞)⁻¹ *
          D.indicator (fun ω => a * g1 j ω + a * gn j ω + c + c * S ω ^ (k + 3)) ω
          ∂growthPathLaw W b := by
        rw [lintegral_finsetSum _ fun j _ => (hgm j).const_mul _]
        exact Finset.sum_congr rfl fun j _ => (lintegral_const_mul _ (hgm j)).symm
    _ ≤ ∫⁻ ω, (a * D.indicator (rhxDrift b E q u₁ u₂ nsxClockOne W) ω +
          a * D.indicator (rhxDrift b E q u₁ u₂ (rhxPowPoly k) W) ω +
          ENNReal.ofReal ((u₂ - u₁ + 2) * rhxK2 b E p r ε k) * D.indicator 1 ω +
          ENNReal.ofReal ((u₂ - u₁ + 2) * rhxK2 b E p r ε k) *
            D.indicator (fun ω => S ω ^ (k + 3)) ω) ∂growthPathLaw W b := by
        refine lintegral_mono fun ω => ?_
        by_cases hω : ω ∈ D
        · simp only [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
          simp only [mul_add, Finset.sum_add_distrib]
          rw [hLc]
          gcongr
          · calc _ = a * ∑ j ∈ Finset.Icc j₁ j₂, (W : ℝ≥0∞)⁻¹ * g1 j ω := by
                  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
              _ ≤ _ := by
                  gcongr
                  exact Finset.sum_le_sum_of_subset hsub
          · calc _ = a * ∑ j ∈ Finset.Icc j₁ j₂, (W : ℝ≥0∞)⁻¹ * gn j ω := by
                  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
              _ ≤ _ := by
                  gcongr
                  exact Finset.sum_le_sum_of_subset hsub
          · rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
            exact mul_le_mul' hcard le_rfl
          · rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
            calc _ ≤ ENNReal.ofReal (u₂ - u₁ + 2) * (c * S ω ^ (k + 3)) :=
                  mul_le_mul' hcard le_rfl
              _ = _ := by ring
        · simp only [Set.indicator_of_notMem hω, mul_zero, Finset.sum_const_zero]
          exact zero_le
    _ = _ := by
        have h1 := ((rhx_measurable_drift b E q u₁ u₂ nsxClockOne W).indicator hDm).const_mul a
        have h2 := ((rhx_measurable_drift b E q u₁ u₂ (rhxPowPoly k) W).indicator hDm).const_mul a
        have h3 := (measurable_one.indicator hDm).const_mul
          (ENNReal.ofReal ((u₂ - u₁ + 2) * rhxK2 b E p r ε k))
        have h12 : Measurable (fun ω => a * D.indicator (rhxDrift b E q u₁ u₂ nsxClockOne W) ω +
            a * D.indicator (rhxDrift b E q u₁ u₂ (rhxPowPoly k) W) ω) := h1.add h2
        have h123 : Measurable (fun ω => a * D.indicator (rhxDrift b E q u₁ u₂ nsxClockOne W) ω +
            a * D.indicator (rhxDrift b E q u₁ u₂ (rhxPowPoly k) W) ω +
            ENNReal.ofReal ((u₂ - u₁ + 2) * rhxK2 b E p r ε k) * D.indicator 1 ω) := h12.add h3
        rw [lintegral_add_left h123, lintegral_add_left h12, lintegral_add_left h1,
          lintegral_const_mul _ ((rhx_measurable_drift b E q u₁ u₂ nsxClockOne W).indicator hDm),
          lintegral_const_mul _ ((rhx_measurable_drift b E q u₁ u₂ (rhxPowPoly k) W).indicator
            hDm),
          lintegral_const_mul _ (measurable_one.indicator hDm), lintegral_indicator_one hDm,
          lintegral_const_mul _ ((hSm.pow_const _).indicator hDm)]

/-- **The after-stop dissipation mass of the higher functional is small for large `K`**. -/
theorem rhx_afterStop_small (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hStops : FullSourceStopsContract) {b E p r ε : ℝ} (hb : 0 < b) (hb1 : b < 1 / 2)
    (hE : -2 < E) (hE' : E < 2) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r) (hε : 0 < ε) {k : ℕ}
    (hrk : r ≤ k + 1) {t₁ R : ℝ} {q : ℝ → ℝ} (hq : IsUnitSource t₁ R q) {u₁ u₂ : ℝ}
    (hu₁ : t₁ + R < u₁) (hu : u₁ ≤ u₂) {θ : ℝ} (hθ : 0 < θ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ K : ℝ, K₀ ≤ K → ∀ᶠ W : ℕ in atTop,
      ∑ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, (W : ℝ≥0∞)⁻¹ *
          ∫⁻ ω, (nsfAlive b E q K u₁ W j)ᶜ.indicator
            (fun ω => ENNReal.ofReal (-rhlGenExpr b E p r ε q W j ω)) ω ∂growthPathLaw W b ≤
        ENNReal.ofReal θ := by
  have hq0 : ∀ x, 0 ≤ q x := hq.2.2.2.1.1
  have hu₁0 : 0 < u₁ := by linarith [hq.1, hq.2.1]
  have hIT : IsIntervalTests (fun _ : Fin 1 => q) := fun _ => ⟨t₁, t₁ + R, hq.2.2.2.1⟩
  obtain ⟨hK1, hK2⟩ := rhx_K_nonneg hb hE hE' hp0 hr hε k
  have hL : 0 ≤ (u₂ - u₁ + 2) * rhxK2 b E p r ε k := by
    have : 0 ≤ u₂ - u₁ + 2 := by linarith
    positivity
  have hUIS := nsx_ui_of_moment (b := b) (fun W ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (k + 3))
    (nsx_supQ_moment hStops hb hb1 hE hE' hIT (by positivity : 0 < u₁ / 2) (by linarith) (k + 2))
  obtain ⟨K₁, hK₁, h1⟩ := nsx_dead_small hStops hb hb1 hE hE' hIT hu₁0 hu _
    (rhx_drift_ui hStops hb hb1 hE hE' hIT hu₁0 hu nsx_isOrdinaryPoly_clockOne)
    (θ := θ / 4 / (rhxK1 p r ε k + 1)) (by positivity)
  obtain ⟨K₂, hK₂, h2⟩ := nsx_dead_small hStops hb hb1 hE hE' hIT hu₁0 hu _
    (rhx_drift_ui hStops hb hb1 hE hE' hIT hu₁0 hu (rhx_isOrdinaryPoly_pow k))
    (θ := θ / 4 / (rhxK1 p r ε k + 1)) (by positivity)
  obtain ⟨K₃, hK₃, h3⟩ := nsx_eventually_dead_le hStops hb hb1 hE hE' hIT hu₁0 hu
    (ρ := θ / 4 / ((u₂ - u₁ + 2) * rhxK2 b E p r ε k + 1)) (by positivity)
  obtain ⟨K₄, hK₄, h4⟩ := nsx_dead_small hStops hb hb1 hE hE' hIT hu₁0 hu _ hUIS
    (θ := θ / 4 / ((u₂ - u₁ + 2) * rhxK2 b E p r ε k + 1)) (by positivity)
  refine ⟨max (max K₁ K₂) (max K₃ K₄), lt_max_of_lt_left (lt_max_of_lt_left hK₁),
    fun K hK => ?_⟩
  have hk1 : K₁ ≤ K := (le_max_left _ _).trans ((le_max_left _ _).trans hK)
  have hk2 : K₂ ≤ K := (le_max_right _ _).trans ((le_max_left _ _).trans hK)
  have hk3 : K₃ ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans hK)
  have hk4 : K₄ ≤ K := (le_max_right _ _).trans ((le_max_right _ _).trans hK)
  filter_upwards [h1 K hk1, h2 K hk2, h3 K hk3, h4 K hk4, nsx_eventually_index hq hu₁]
    with W hW1 hW2 hW3 hW4 ⟨hW0, hjW, hqt⟩
  refine (rhx_mass_le hCount hb hb1 hE hE' hp0 hp1 hr hε hrk hq0 hu₁0 hu hW0 hjW hqt).trans ?_
  rw [nsx_ofReal_quarters hθ.le]
  gcongr
  · exact nsx_const_mul_le hK1 (by positivity) hW1
  · exact nsx_const_mul_le hK1 (by positivity) hW2
  · exact nsx_const_mul_le hL (by positivity) hW3
  · exact nsx_const_mul_le hL (by positivity) hW4

end BlockBand.Endpoints
