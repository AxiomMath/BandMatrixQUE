module

public import BlockBand.Transmission.Generator.ProdConv

/-!
# The limit side: Fubini for the product `M_kM_l - ∫B`

**`limit_pieces hLU`**: on an fdd limit, for a past test `Φ` and `0 < s ≤ t`,
`Φ·(M_kM_l - ∫_s^tB)` is integrable and its expectation is
`limTest hYY - ∫ limTest(hYA, k, l) - ∫ limTest(hYA, l, k) + ∫∫ limTest(hAA) - ∫ limTest(hBr)`,
the limit of `prod_conv`. Route: jointly measurable versions `F_k` of `A_k(P(u))`
(`limit_version`); `fubini_slices` for `Y_k ∫A_l`, `Y_l ∫A_k`, `∫B`; for `∫A_k ∫A_l` two nested
`fubini_slices` (the inner one also bounds `E|ΦA_l(P(v))∫A_k|`, which is the slice bound of the
outer one). Slice bounds come from the limit `L²` bounds of `poly_point`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology Finset
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

theorem lintegral_enorm_le_of_sq {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (h : ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal K) :
    ∫⁻ ω, ‖f ω‖ₑ ∂μ ≤ ENNReal.ofReal (1 + K) := by
  calc ∫⁻ ω, ‖f ω‖ₑ ∂μ ≤ ∫⁻ ω, (1 + ‖f ω‖ₑ ^ 2) ∂μ := lintegral_mono fun ω => enorm_le_one_add_sq _
    _ = 1 + ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (1 + K) := by
        rw [ENNReal.ofReal_add zero_le_one hK, ENNReal.ofReal_one]; gcongr

/-- A version of `A(P(u))` for a continuous coefficient `H` that only reads `P_j`, `j ≥ 1`. -/
theorem limit_version' {P : Measure Ω} {Pk : ℕ → ℝ → Ω → ℝ}
    (hmeas : ∀ k, 1 ≤ k → ∀ t, 0 < t → Measurable (Pk k t))
    (hcont : ∀ k, 1 ≤ k → ∀ᵐ ω ∂P, ContinuousOn (fun t => Pk k t ω) (Set.Ioi 0))
    {H : (ℕ → ℝ) → ℝ} (hH : Continuous H)
    (hcut : ∀ u ω, H (cutVec Pk u ω) = H (fun i => Pk i u ω)) {s t : ℝ} (hs : 0 < s) :
    ∃ F : ℝ → Ω → ℝ, Measurable (Function.uncurry F) ∧
      ∀ᵐ ω ∂P, ∀ u ∈ Set.Icc s t, F u ω = H (fun i => Pk i u ω) := by
  obtain ⟨F, hF, hFa⟩ := limit_version hmeas hcont hH (t := t) hs
  exact ⟨F, hF, hFa.mono fun ω h u hu => (h u hu).trans (hcut u ω)⟩

omit [MeasurableSpace Ω] in
theorem intervalIntegral_eq_of_version {F : ℝ → Ω → ℝ} {G : ℝ → Ω → ℝ} {s t : ℝ} (hst : s ≤ t)
    {ω : Ω} (h : ∀ u ∈ Set.Icc s t, F u ω = G u ω) :
    ∫ u in s..t, G u ω = ∫ u in s..t, F u ω :=
  intervalIntegral.integral_congr fun u hu => (h u (by rwa [Set.uIcc_of_le hst] at hu)).symm

/-- **The limit-side identity.** -/
theorem limit_pieces (hLU : TransmissionLengthUniformContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ}
    (he : IsMovingEnergy E Ce e) {P : Measure Ω} {Pk : ℕ → ℝ → Ω → ℝ} {σ : ℕ → ℕ}
    (hS : LimitSetup b e P Pk σ)
    (hcont : ∀ k, 1 ≤ k → ∀ᵐ ω ∂P, ContinuousOn (fun t => Pk k t ω) (Set.Ioi 0))
    {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) {m : ℕ}
    (pts : Fin m → ℕ × ℝ) (hpts : ∀ i, 1 ≤ (pts i).1 ∧ 0 < (pts i).2)
    (Φ : BoundedContinuousFunction (Fin m → ℝ) ℝ) :
    Integrable (fun ω => Φ (limVec Pk pts ω) *
      ((Pk k t ω - Pk k s ω - ∫ u in s..t, transmissionDrift (transportD0 b E) k
          (fun i => Pk i u ω)) *
        (Pk l t ω - Pk l s ω - ∫ u in s..t, transmissionDrift (transportD0 b E) l
          (fun i => Pk i u ω)) -
        ∫ u in s..t, transmissionBracket (transportD0 b E) k l (fun i => Pk i u ω))) P ∧
    ∫ ω, Φ (limVec Pk pts ω) *
      ((Pk k t ω - Pk k s ω - ∫ u in s..t, transmissionDrift (transportD0 b E) k
          (fun i => Pk i u ω)) *
        (Pk l t ω - Pk l s ω - ∫ u in s..t, transmissionDrift (transportD0 b E) l
          (fun i => Pk i u ω)) -
        ∫ u in s..t, transmissionBracket (transportD0 b E) k l (fun i => Pk i u ω)) ∂P =
      limTest P Pk pts Φ hYY (ptYY k l s t) -
        (∫ u in s..t, limTest P Pk pts Φ (hYA (transportD0 b E) l) (ptYA k l s t u)) -
        (∫ u in s..t, limTest P Pk pts Φ (hYA (transportD0 b E) k) (ptYA l k s t u)) +
        (∫ v in s..t, ∫ u in s..t,
          limTest P Pk pts Φ (hAA (transportD0 b E) l k) (ptAA l k v u)) -
        ∫ u in s..t, limTest P Pk pts Φ (hBr (transportD0 b E) k l) (ptVec (k + l + 1) u) := by
  have := hS.prob
  set D := transportD0 b E
  have hD : 0 ≤ D := transportD0_nonneg hb0 hE1 hE2
  have ht : 0 < t := lt_of_lt_of_le hs hst
  set ψ : Ω → ℝ := fun ω => Φ (limVec Pk pts ω)
  have hψm : Measurable ψ := Φ.continuous.measurable.comp (measurable_limVec hS.meas pts hpts)
  set Y : ℕ → Ω → ℝ := fun j ω => Pk j t ω - Pk j s ω
  have hYm : ∀ j, 1 ≤ j → Measurable (Y j) := fun j hj =>
    (hS.meas j hj t ht).sub (hS.meas j hj s hs)
  -- versions
  have hcA : ∀ j, Continuous (transmissionDrift D j) := fun j =>
    continuous_transmissionDrift D j (v := fun x : ℕ → ℝ => x) fun i => continuous_apply i
  obtain ⟨Fk, hFk, hFka⟩ := limit_version' hS.meas hcont (hcA k)
    (fun u ω => drift_cutVec D k Pk u ω) (t := t) hs
  obtain ⟨Fl, hFl, hFla⟩ := limit_version' hS.meas hcont (hcA l)
    (fun u ω => drift_cutVec D l Pk u ω) (t := t) hs
  obtain ⟨Fb, hFb, hFba⟩ := limit_version' hS.meas hcont (continuous_transmissionBracket D k l
    (v := fun x : ℕ → ℝ => x) fun i => continuous_apply i)
    (fun u ω => bracket_cutVec D Pk hk l u ω) (t := t) hs
  -- limit `L²` bounds
  obtain ⟨K1, hK1, -, hl1⟩ := poly_point hLU hb0 hb hE1 hE2 he hS (T := t) hs pts hpts Φ
    continuous_hYY hYY_le
  obtain ⟨K2, hK2, -, hl2⟩ := poly_point hLU hb0 hb hE1 hE2 he hS (T := t) hs pts hpts Φ
    (continuous_hYA D l) (hYA_le hD l)
  obtain ⟨K3, hK3, -, hl3⟩ := poly_point hLU hb0 hb hE1 hE2 he hS (T := t) hs pts hpts Φ
    (continuous_hYA D k) (hYA_le hD k)
  obtain ⟨K4, hK4, -, hl4⟩ := poly_point hLU hb0 hb hE1 hE2 he hS (T := t) hs pts hpts Φ
    (continuous_hAA D l k) (hAA_le hD l k)
  obtain ⟨K5, hK5, -, hl5⟩ := poly_point hLU hb0 hb hE1 hE2 he hS (T := t) hs pts hpts Φ
    (continuous_hBr D k l) (hBr_le hD k l)
  -- `Y_k Y_l`
  have hYY1 := (hl1 _ (ptYY_mem hk hl hst)).1
  simp only [hYY_lim] at hYY1
  have iYY : Integrable (fun ω => ψ ω * (Y k ω * Y l ω)) P :=
    (sq_integrable_of ((hψm.mul ((hYm k hk).mul (hYm l hl))).aestronglyMeasurable) hYY1).2.1
  have vYY : ∫ ω, ψ ω * (Y k ω * Y l ω) ∂P = limTest P Pk pts Φ hYY (ptYY k l s t) := by
    simp only [limTest, hYY_lim]; rfl
  -- `Y_j ∫A_{j'}`
  have hYA : ∀ (j j' : ℕ), 1 ≤ j → ∀ {F : ℝ → Ω → ℝ}, Measurable (Function.uncurry F) →
      (∀ᵐ ω ∂P, ∀ u ∈ Set.Icc s t, F u ω = transmissionDrift D j' (fun i => Pk i u ω)) →
      ∀ {K : ℝ}, 0 ≤ K → (∀ u ∈ Set.Icc s t, ∫⁻ ω, ‖ψ ω * hYA D j' (limVec Pk (ptYA j j' s t u) ω)‖ₑ ^ 2
        ∂P ≤ ENNReal.ofReal K) →
      Integrable (fun ω => ψ ω * Y j ω * ∫ u in s..t, F u ω) P ∧
        ∫ ω, ψ ω * Y j ω * (∫ u in s..t, F u ω) ∂P =
          ∫ u in s..t, limTest P Pk pts Φ (hYA D j') (ptYA j j' s t u) := by
    intro j j' hj F hF hFa K hK hKb
    have hC : ∀ u ∈ Set.Ioc s t, ∫⁻ ω, ‖ψ ω * Y j ω * F u ω‖ₑ ∂P ≤ ENNReal.ofReal (1 + K) := by
      intro u hu
      refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (lintegral_enorm_le_of_sq hK
        (hKb u ⟨hu.1.le, hu.2⟩))
      filter_upwards [hFa] with ω hω
      rw [hω u ⟨hu.1.le, hu.2⟩, hYA_lim, mul_assoc]
    have hψY : Measurable fun ω => ψ ω * Y j ω := hψm.mul (hYm j hj)
    obtain ⟨h1, -, h3, -⟩ := fubini_slices hF hψY hst hC
    refine ⟨h1, h3.trans (intervalIntegral.integral_congr fun u hu => ?_)⟩
    rw [Set.uIcc_of_le hst] at hu
    refine integral_congr_ae ?_
    filter_upwards [hFa] with ω hω
    simp only [hω u hu, hYA_lim, ψ, Y, mul_assoc]
  obtain ⟨iYAkl, vYAkl⟩ := hYA k l hk hFl hFla hK2 fun u hu => (hl2 _ (ptYA_mem hk hst hu)).1
  obtain ⟨iYAlk, vYAlk⟩ := hYA l k hl hFk hFka hK3 fun u hu => (hl3 _ (ptYA_mem hl hst hu)).1
  -- `∫A_k ∫A_l`
  have hAAb : ∀ v ∈ Set.Icc s t, ∀ u ∈ Set.Ioc s t, ∫⁻ ω, ‖ψ ω * Fl v ω * Fk u ω‖ₑ ∂P ≤
      ENNReal.ofReal (1 + K4) := by
    intro v hv u hu
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (lintegral_enorm_le_of_sq hK4
      ((hl4 _ (ptAA_mem hv ⟨hu.1.le, hu.2⟩)).1))
    filter_upwards [hFka, hFla] with ω hωk hωl
    rw [hωk u ⟨hu.1.le, hu.2⟩, hωl v hv, hAA_lim, mul_assoc]
  have hFlm : ∀ v, Measurable (Fl v) := fun v => hFl.comp (measurable_const.prodMk measurable_id)
  have hIk : Measurable fun ω => ∫ u in s..t, Fk u ω := measurable_intervalIntegral_of_uncurry hFk hst
  have hψFl : ∀ v, Measurable fun ω => ψ ω * Fl v ω := fun v => hψm.mul (hFlm v)
  have hψIk : Measurable fun ω => ψ ω * ∫ u in s..t, Fk u ω := hψm.mul hIk
  have hinner := fun v (hv : v ∈ Set.Icc s t) =>
    fubini_slices hFk (hψFl v) hst (hAAb v hv)
  have hCo : ∀ v ∈ Set.Ioc s t, ∫⁻ ω, ‖ψ ω * (∫ u in s..t, Fk u ω) * Fl v ω‖ₑ ∂P ≤
      ENNReal.ofReal ((t - s) * (1 + K4)) := by
    intro v hv
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) (hinner v ⟨hv.1.le, hv.2⟩).2.1
    congr 1; ring
  obtain ⟨iAA, -, vAA0, -⟩ := fubini_slices hFl hψIk hst hCo
  have vAA : ∫ ω, ψ ω * (∫ u in s..t, Fk u ω) * (∫ u in s..t, Fl u ω) ∂P =
      ∫ v in s..t, ∫ u in s..t, limTest P Pk pts Φ (hAA D l k) (ptAA l k v u) := by
    rw [vAA0]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le hst] at hv
    have e1 : ∫ ω, ψ ω * (∫ u in s..t, Fk u ω) * Fl v ω ∂P =
        ∫ ω, ψ ω * Fl v ω * (∫ u in s..t, Fk u ω) ∂P :=
      integral_congr_ae (ae_of_all _ fun ω => by ring)
    rw [e1, (hinner v hv).2.2.1]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hst] at hu
    refine integral_congr_ae ?_
    filter_upwards [hFka, hFla] with ω hωk hωl
    simp only [hωk u hu, hωl v hv, hAA_lim, ψ, mul_assoc]
  -- `∫B`
  have hCb : ∀ u ∈ Set.Ioc s t, ∫⁻ ω, ‖ψ ω * Fb u ω‖ₑ ∂P ≤ ENNReal.ofReal (1 + K5) := by
    intro u hu
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (lintegral_enorm_le_of_sq hK5
      ((hl5 _ (ptVec_mem ⟨hu.1.le, hu.2⟩)).1))
    filter_upwards [hFba] with ω hω
    rw [hω u ⟨hu.1.le, hu.2⟩, hBr_lim D Pk hk]
  obtain ⟨iB, -, vB0, -⟩ := fubini_slices hFb hψm hst hCb
  have vB : ∫ ω, ψ ω * (∫ u in s..t, Fb u ω) ∂P =
      ∫ u in s..t, limTest P Pk pts Φ (hBr D k l) (ptVec (k + l + 1) u) := by
    rw [vB0]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hst] at hu
    refine integral_congr_ae ?_
    filter_upwards [hFba] with ω hω
    simp only [hω u hu, hBr_lim D Pk hk, ψ]
  -- assemble
  have hae : (fun ω => Φ (limVec Pk pts ω) *
      ((Pk k t ω - Pk k s ω - ∫ u in s..t, transmissionDrift D k (fun i => Pk i u ω)) *
        (Pk l t ω - Pk l s ω - ∫ u in s..t, transmissionDrift D l (fun i => Pk i u ω)) -
        ∫ u in s..t, transmissionBracket D k l (fun i => Pk i u ω))) =ᵐ[P]
      fun ω => ψ ω * (Y k ω * Y l ω) - ψ ω * Y k ω * (∫ u in s..t, Fl u ω) -
        ψ ω * Y l ω * (∫ u in s..t, Fk u ω) +
        ψ ω * (∫ u in s..t, Fk u ω) * (∫ u in s..t, Fl u ω) - ψ ω * ∫ u in s..t, Fb u ω := by
    filter_upwards [hFka, hFla, hFba] with ω hωk hωl hωb
    rw [intervalIntegral_eq_of_version (G := fun u ω => transmissionDrift D k fun i => Pk i u ω)
      hst hωk, intervalIntegral_eq_of_version (G := fun u ω => transmissionDrift D l
      fun i => Pk i u ω) hst hωl, intervalIntegral_eq_of_version
      (G := fun u ω => transmissionBracket D k l fun i => Pk i u ω) hst hωb]
    simp only [ψ, Y]; ring
  have i12 : Integrable (fun ω => ψ ω * (Y k ω * Y l ω) -
      ψ ω * Y k ω * (∫ u in s..t, Fl u ω)) P := iYY.sub iYAkl
  have i123 : Integrable (fun ω => ψ ω * (Y k ω * Y l ω) - ψ ω * Y k ω * (∫ u in s..t, Fl u ω) -
      ψ ω * Y l ω * (∫ u in s..t, Fk u ω)) P := i12.sub iYAlk
  have i1234 : Integrable (fun ω => ψ ω * (Y k ω * Y l ω) - ψ ω * Y k ω * (∫ u in s..t, Fl u ω) -
      ψ ω * Y l ω * (∫ u in s..t, Fk u ω) +
      ψ ω * (∫ u in s..t, Fk u ω) * (∫ u in s..t, Fl u ω)) P := i123.add iAA
  refine ⟨(i1234.sub iB).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_sub i1234 iB, integral_add i123 iAA, integral_sub i12 iYAlk,
    integral_sub iYY iYAkl, vYY, vYAkl, vYAlk, vAA, vB]

end BlockBand.Transmission.Generator
