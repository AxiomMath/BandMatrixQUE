module

public import BlockBand.Transmission.Absorbed.MixShift

/-!
# The absorbed source-mixing step and its forcing

The two atoms are run **together**, `mixSum = ‖Tr Qf‖ + hs(Q, f)`, because the shift bound
`mix_absorb_le` controls their sum only. Along `X_{j+1} = freshSchur E X'_j fresh_j`,
`X'_j = absIn j = X_j − iε_j`, with the excesses `mx_excess` at the passive input `X'_j`:

**`ae_mix_step`**: a.s., for every `j ≥ 1`, `mixSum(X_{j+1}) ≤ ρ·mixSum(X_j) + mixForce_j`,
`mixForce_j = ρ·mixErr(ε_j, q(X_j)) + 2C·mx_err(X'_j) + exc_tr(X'_j, ·) + exc_hs(X'_j, ·)`.

**`eLpNorm_mixForce_le`**: `‖mixForce_j‖_p ≤ mixB/√W` from the one-layer excess bounds
(`mx_layer_bulk`, at every passive input) and `‖q(X_j)‖_{2p} ≤ K_q`, `‖δ₀(X_j)‖_{2p},
‖δ₁(X_j)‖_{2p} ≤ D/W`; the absorption costs `ρ·cMix(K_q + 1)/√W` (`sqrtW_mixErr_le`)
and the shifted moments `abs_input_moments`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LawFinite
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder

variable {W : ℕ}

/-- The two source-mixing atoms together. -/
def mixSum (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ := mx_trG b E X + mx_hsG b E X

theorem measurable_mixSum (b E : ℝ) : Measurable (mixSum (W := W) b E) :=
  (measurable_mx_trG b E).add (measurable_mx_hsG b E)

theorem mixSum_nonneg (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : 0 ≤ mixSum b E X :=
  add_nonneg (mx_G_nonneg_tr b E X) (mx_G_nonneg_hs b E X)

/-- The forcing of the absorbed source-mixing step `j → j+1`. -/
def mixForce (b E : ℝ) (κ : ℝ → ℝ) (ρ C : ℝ) (s : ℂ) (W j : ℕ) (ω : GrowthPath W) : ℝ :=
  ρ * mixErr b E (layerAbsorption W κ (j + 1) 0) (passiveMass b E (pathNearSchur b E κ W j ω)) W +
    2 * C * mx_err b E s (absIn b E κ W j ω) +
    mx_excess (mx_trG b E) ρ C b E s (absIn b E κ W j ω, freshSample W j ω) +
    mx_excess (mx_hsG b E) ρ C b E s (absIn b E κ W j ω, freshSample W j ω)

/-- **The absorbed source-mixing step, almost surely.** -/
theorem ae_mix_step {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hW1 : 1 ≤ W) {κ : ℝ → ℝ} {K : ℝ} (hκ : ∀ t, 0 ≤ κ t ∧ κ t ≤ K) {ρ C : ℝ} (hρ : 0 ≤ ρ)
    (s : ℂ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j →
      mixSum b E (pathNearSchur b E κ W (j + 1) ω) ≤
        ρ * mixSum b E (pathNearSchur b E κ W j ω) + mixForce b E κ ρ C s W j ω := by
  have hκ0 : ∀ t, 0 ≤ κ t := fun t => (hκ t).1
  have hb1 : b < 1 := by linarith
  filter_upwards [ae_pathNearSchur_succ_abs hb h1 h2 hW1 hκ0,
    ae_passiveSample W hκ0 hb1 h1 h2] with ω hrec hP j hj
  obtain ⟨hε0, -⟩ := layerAbsorption_succ_bounds (W := W) hκ j
  set X := pathNearSchur b E κ W j ω
  set ε := layerAbsorption W κ (j + 1) 0
  have hX' : absIn b E κ W j ω = absorbedInput X ε := stepInput_eq_absorbedInput b E κ j ω
  have hrec' : pathNearSchur b E κ W (j + 1) ω =
      freshSchur E (absIn b E κ W j ω) (freshSample W j ω) := by rw [hX']; exact hrec j hj
  have hY : (passiveY X).PosSemidef := pathNearSchur_passive hP j
  have hsh := mix_absorb_le hb0 hb h1 h2 hY hε0
  have hsh' : mixSum b E (absIn b E κ W j ω) ≤ mixSum b E X + mixErr b E ε (passiveMass b E X) W := by
    rw [hX']; exact hsh
  set Y := absIn b E κ W j ω
  set f := freshSample W j ω
  have etr : mx_trG b E (freshSchur E Y f) ≤ ρ * mx_trG b E Y + C * mx_err b E s Y +
      mx_excess (mx_trG b E) ρ C b E s (Y, f) := by
    have := le_max_right 0 (mx_trG b E (freshSchur E Y f) - ρ * mx_trG b E Y - C * mx_err b E s Y)
    unfold mx_excess; linarith
  have ehs : mx_hsG b E (freshSchur E Y f) ≤ ρ * mx_hsG b E Y + C * mx_err b E s Y +
      mx_excess (mx_hsG b E) ρ C b E s (Y, f) := by
    have := le_max_right 0 (mx_hsG b E (freshSchur E Y f) - ρ * mx_hsG b E Y - C * mx_err b E s Y)
    unfold mx_excess; linarith
  have hρs := mul_le_mul_of_nonneg_left hsh' hρ
  rw [hrec']
  unfold mixSum mixForce at *
  nlinarith

/-- The constant of `eLpNorm_mixForce_le`. -/
def mixB (cM ρ C C' Kq Kq' D' : ℝ) : ℝ :=
  ρ * (cM * (Kq + 1)) + 2 * C * (2 * D' * Kq' + Kq' ^ 2 + Kq') + 2 * (C' * Kq')

/-- **The `L^p` norm of the absorbed forcing.** -/
theorem eLpNorm_mixForce_le {b κI E K : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκI : 0 < κI)
    (hE : E ∈ bulkInterval κI) {κ : ℝ → ℝ} (hκ : ∀ t, 0 ≤ κ t ∧ κ t ≤ K) (s : ℂ)
    (hW1 : 1 ≤ W) (hWK : K / etaLow b κI ≤ W) (j : ℕ) {p Kq D ρ C C' : ℝ} (hp : 1 ≤ p)
    (hKq : 0 ≤ Kq) (hD : 0 ≤ D) (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hL : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      eLpNorm (fun ω => mx_excess (mx_trG b E) ρ C b E s (X, ω)) (ENNReal.ofReal p)
          (freshLaw W b) ≤ ENNReal.ofReal (C' / Real.sqrt W * passiveMass b E X) ∧
      eLpNorm (fun ω => mx_excess (mx_hsG b E) ρ C b E s (X, ω)) (ENNReal.ofReal p)
          (freshLaw W b) ≤ ENNReal.ofReal (C' / Real.sqrt W * passiveMass b E X))
    (hq : eLpNorm (fun ω => passiveMass b E (pathNearSchur b E κ W j ω)) (ENNReal.ofReal (2 * p))
      (growthPathLaw W b) ≤ ENNReal.ofReal Kq)
    (hδ0 : eLpNorm (fun ω => jetDistance0 b E (pathNearSchur b E κ W j ω))
      (ENNReal.ofReal (2 * p)) (growthPathLaw W b) ≤ ENNReal.ofReal (D / W))
    (hδ1 : eLpNorm (fun ω => mx_jet1 b E s (pathNearSchur b E κ W j ω)) (ENNReal.ofReal (2 * p))
      (growthPathLaw W b) ≤ ENNReal.ofReal (D / W)) :
    eLpNorm (mixForce b E κ ρ C s W j) (ENNReal.ofReal p) (growthPathLaw W b) ≤
      ENNReal.ofReal (mixB (cMix (etaLow b κI)⁻¹ K) ρ C C' Kq
        (4 * Kq + K / etaLow b κI ^ 2) (D + K / etaLow b κI ^ 2 + 2 * K / etaLow b κI ^ 3) /
          Real.sqrt W) := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκI hE
  have hb1 : b < 1 := by linarith
  have hηL := etaLow_pos hb1 hκI
  have hκ0 : ∀ t, 0 ≤ κ t := fun t => (hκ t).1
  have hK : 0 ≤ K := (hκ 0).1.trans (hκ 0).2
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.2 hW0
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hmono : ENNReal.ofReal p ≤ ENNReal.ofReal (2 * p) := ENNReal.ofReal_le_ofReal (by linarith)
  set P := growthPathLaw W b
  set cM := cMix (etaLow b κI)⁻¹ K
  have hcM : 0 ≤ cM := by
    have : 0 ≤ (etaLow b κI)⁻¹ := by positivity
    simp only [cM, cMix]; positivity
  set Kq' := 4 * Kq + K / etaLow b κI ^ 2
  set D' := D + K / etaLow b κI ^ 2 + 2 * K / etaLow b κI ^ 3
  have hKq' : 0 ≤ Kq' := by positivity
  have hD' : 0 ≤ D' := by positivity
  obtain ⟨mq, m0, m1⟩ := abs_input_moments hb0 hb hκI hE hκ s hW1 hWK j (by linarith) hKq hD hq
    hδ0 hδ1
  obtain ⟨hε0, hεK⟩ := layerAbsorption_succ_bounds (W := W) hκ j
  -- (a) the absorption: `ρ·mixErr ≤ ρ·cM(q + 1)/√W`
  have hmixm : Measurable fun x : ℝ => mixErr b E (layerAbsorption W κ (j + 1) 0) x W := by
    unfold mixErr; fun_prop
  have ta : eLpNorm (fun ω => mixErr b E (layerAbsorption W κ (j + 1) 0)
      (passiveMass b E (pathNearSchur b E κ W j ω)) W) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (cM / Real.sqrt W * Kq + cM / Real.sqrt W) := by
    refine (eLpNorm_mono_ae_real (hmixm.comp ((measurable_passiveMass b E).comp
      (measurable_pathNearSchur' b E κ j))).aestronglyMeasurable
      (g := fun ω => cM / Real.sqrt W * passiveMass b E (pathNearSchur b E κ W j ω) +
        cM / Real.sqrt W) ?_).trans
      (eLpNorm_affine_le hp1 (by positivity) (by positivity)
        ((eLpNorm_le_eLpNorm_of_exponent_le hmono).trans hq) hKq)
    filter_upwards [ae_passiveSample W hκ0 hb1 h1 h2] with ω hP
    have hY := pathNearSchur_passive hP j
    have hf := (abs_shift_facts hb0 hb hκI hE hY s hK hW1 hWK hε0 hεK).2.2.2
    have h0 : 0 ≤ mixErr b E (layerAbsorption W κ (j + 1) 0)
        (passiveMass b E (pathNearSchur b E κ W j ω)) W := by
      unfold mixErr
      have := passiveMass_nonneg b E hY
      have := etaZ_pos b E hb1 h1 h2
      positivity
    change ‖mixErr b E (layerAbsorption W κ (j + 1) 0)
      (passiveMass b E (pathNearSchur b E κ W j ω)) W‖ ≤ _
    rw [Real.norm_of_nonneg h0]
    calc _ ≤ cM * (passiveMass b E (pathNearSchur b E κ W j ω) + 1) / Real.sqrt W := hf
      _ = _ := by ring
  have tA := mx_const_mul_le hρ ta
  -- (b) the mean forcing at the shifted input
  have tB := mx_err_moment (μ := P) (b := b) (E := E) hW1 (Y := absIn b E κ W j)
    (C := 2 * C) (by positivity) (s := s) hp hKq' hD' mq m0 m1
  -- (c) the two excesses (Fubini at the shifted input)
  have hqp : eLpNorm (fun ω => passiveMass b E (absIn b E κ W j ω)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal Kq' := (eLpNorm_le_eLpNorm_of_exponent_le hmono).trans mq
  have tC : ∀ G : Matrix (Fin W) (Fin W) ℂ → ℝ, Measurable G →
      (∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        eLpNorm (fun ω => mx_excess G ρ C b E s (X, ω)) (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal (C' / Real.sqrt W * passiveMass b E X)) →
      eLpNorm (fun ω => mx_excess G ρ C b E s (absIn b E κ W j ω, freshSample W j ω))
        (ENNReal.ofReal p) P ≤ ENNReal.ofReal (C' / Real.sqrt W * Kq') := by
    intro G hG hbd
    refine (abs_eLpNorm_path_le hb1 h1 h2 hκ0 (measurable_mx_excess hG ρ C b E s)
      (measurable_passiveMass b E) hp0 (by positivity) j hbd).trans ?_
    rw [ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' le_rfl hqp
  have tC1 := tC _ (measurable_mx_trG b E) fun X hX => (hL X hX).1
  have tC2 := tC _ (measurable_mx_hsG b E) fun X hX => (hL X hX).2
  have s1 := mx_add_le hp1 (by positivity) (by positivity) tA tB
  have s2 := mx_add_le hp1 (by positivity) (by positivity) s1 tC1
  have s3 := mx_add_le hp1 (by positivity) (by positivity) s2 tC2
  refine s3.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  simp only [mixB]
  field_simp
  ring

end BlockBand.Transmission.Absorbed
