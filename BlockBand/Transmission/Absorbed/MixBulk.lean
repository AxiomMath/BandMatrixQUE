module

public import BlockBand.Transmission.Absorbed.MixStep
public import BlockBand.Transmission.Absorbed.MixSource
public import BlockBand.Transmission.SourceMixingBulk.Mixing

/-!
# Absorbed source mixing holds

`absorbedSourceMixingBulk_holds`: `AbsorbedSourceMixingBulk` from the matched-traces and Gaussian
layer hypotheses.

Route: `SourceMixingBulk.passiveSourceMixingBulk_holds` / `mx_G_final_bulk` along the
absorbed path, run on the sum `mixSum = ‖Tr Qf‖ + hs(Q, f)` (`MixStep`):
* ratio `ρ = max (b/(b + kGap)) ½ < 1` (`thetaStar_le_bulk`), excesses `mx_layer_bulk`
  at `p' = max p 2` at the passive input `X'_j`;
* moments on `[εW/2, TW]`: `absorbedMassMoment_bulk` (`2p'`) and
  `absorbedJetMoments_holds` (time floor `ε/2`, `2p'`);
* forcing `‖mixForce_j‖_{p'} ≤ mixB/√W` (`eLpNorm_mixForce_le`), start
  `mixSum(X_{r₀}) ≤ 2Λq`, `Λ = η_L⁻¹ + 1/((1-b)κ_I)`, `r₀ = ⌈εW/2⌉`;
* the linear recursion bound `linrec_from` (sibling module) and `ρ^{r-r₀} ≤ 2/W`
  (`pow_le_two_div`).
The absorption enters only through `ρ·mixErr = O((q+1)/√W)` per step and the shifted moments;
the contraction keeps the `C/√W` rate. `C` depends on `b, κ_I, ε, T, p` and the profile bound.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.SourceMixingBulk
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LengthUniform
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `mixSum ≤ 2Λq` on the bulk (`‖f‖ ≤ η⁻¹ + ‖c₀‖ ≤ Λ`). -/
theorem mixSum_le_mass {b κI E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκI : 0 < κI)
    (hE : E ∈ bulkInterval κI) {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef) :
    mixSum b E X ≤ 2 * ((etaLow b κI)⁻¹ + 1 / ((1 - b) * κI)) * passiveMass b E X := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκI hE
  have hF : ‖passiveF b E X‖ ≤ (etaLow b κI)⁻¹ + 1 / ((1 - b) * κI) :=
    (SourceMixing.norm_passiveF_le hb0 hb h1 h2 hX).trans
      (add_le_add (inv_etaZ_le_bulk hb hκI hE) (PassiveLayer.norm_cZero_le hb hκI hE))
  have hfq := mul_le_mul_of_nonneg_right hF (passiveMass_nonneg b E hX)
  have hQ : (passiveQ b E X).PosSemidef := hX.conjTranspose_mul_mul_same _
  have a1 := mx_trace_le hQ (passiveF b E X)
  have a2 := hsSandwich_le_norm hQ (passiveF b E X)
  unfold mixSum mx_trG mx_hsG
  change ‖passiveF b E X‖ * (passiveQ b E X).trace.re ≤ _ * (passiveQ b E X).trace.re at hfq
  change _ ≤ _ * (passiveQ b E X).trace.re
  linarith

/-- The final scalar step. -/
theorem mix_final_arith {A B ρ x P : ℝ} (hA : 0 ≤ A) (hρ1 : ρ < 1) (hx : 1 ≤ x)
    (hP : P ≤ 2 / x) :
    2 * (P * A + B / Real.sqrt x / (1 - ρ)) ≤ 2 * (2 * A + B / (1 - ρ)) / Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hs1 : Real.sqrt x ≤ x := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have h2W : 2 / x ≤ 2 / Real.sqrt x := div_le_div_of_nonneg_left (by norm_num) hs0 hs1
  have h1ρ : 0 < 1 - ρ := by linarith
  have := mul_le_mul_of_nonneg_right (hP.trans h2W) hA
  have e : 2 * (2 * A + B / (1 - ρ)) / Real.sqrt x =
      2 * (2 / Real.sqrt x * A + B / Real.sqrt x / (1 - ρ)) := by field_simp
  rw [e]; linarith

/-- `AbsorbedSourceMixingBulk` from `MatchedTracesContract`, `GaussianAbsorptionContract`,
`GaussianLpGradient`. -/
theorem absorbedSourceMixingBulk_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) : AbsorbedSourceMixingBulk := by
  intro b hb0 hb κI ε T p hκI hε _ hp κ hκ
  have hκp := hκ
  obtain ⟨-, hκ0, K, hKb⟩ := hκ
  have hκK : ∀ t, 0 ≤ κ t ∧ κ t ≤ K := fun t => ⟨hκ0 t, hKb t⟩
  have hK : 0 ≤ K := (hκ0 0).trans (hKb 0)
  have hb1 : b < 1 := by linarith
  have hηL := etaLow_pos hb1 hκI
  set ρ := max (b / (b + kGap b κI)) (1 / 2)
  have hρh : (1 : ℝ) / 2 ≤ ρ := le_max_right _ _
  have hρ1 : ρ < 1 := max_lt (rhoBulk_lt_one hb0 hb hκI) (by norm_num)
  have hρ0 : 0 ≤ ρ := by linarith
  set p' := max p 2
  have hp' : 1 ≤ p' := hp.trans (le_max_left _ _)
  obtain ⟨C, C', W₁, hC, hC', hL⟩ := mx_layer_bulk (PassiveLayer.passiveBounds_holds hGA hLp)
    hb0 hb hκI (ρ := ρ) (le_max_right p 2)
  obtain ⟨Km, hKm0, hKmT⟩ := absorbedMassMoment_bulk hMT hGA hLp hb0 hb hκI hK (2 * p')
    (by linarith)
  obtain ⟨Wq, hq⟩ := hKmT T
  obtain ⟨Cj, hJT⟩ := absorbedJetMoments_holds hMT hGA hLp b hb0 hb κI (ε / 2) (2 * p') hκI
    (half_pos hε) (by linarith) κ hκp
  obtain ⟨Wj, hj⟩ := hJT T
  obtain ⟨Wl, hl⟩ := log_le_eps_mul (1 / Real.log (1 / ρ)) (half_pos hε)
  set D := max Cj 0
  set Kq := Km * (1 + 2 / ε)
  have hKq : 0 ≤ Kq := by positivity
  set Λ := (etaLow b κI)⁻¹ + 1 / ((1 - b) * κI)
  have hΛ : 0 ≤ Λ := by have : 0 < 1 - b := by linarith
                        positivity
  set Bm := mixB (cMix (etaLow b κI)⁻¹ K) ρ C C' Kq (4 * Kq + K / etaLow b κI ^ 2)
    (D + K / etaLow b κI ^ 2 + 2 * K / etaLow b κI ^ 3)
  have hBm : 0 ≤ Bm := by
    have : 0 ≤ (etaLow b κI)⁻¹ := by positivity
    have : 0 ≤ D := le_max_right _ _
    simp only [Bm, mixB, cMix]; positivity
  refine ⟨2 * (2 * (2 * Λ * Kq) + Bm / (1 - ρ)),
    max (max (max W₁ Wq) (max Wj Wl)) (max ⌈K / etaLow b κI⌉₊ 1), fun W hW E hE r hr1 hr2 => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW₁, hWq⟩, hWj, hWl⟩, hWK', hW1⟩ := hW
  obtain ⟨h1, h2⟩ := bulk_bounds hκI hE
  obtain ⟨s, hs⟩ := stationaryJet_exists hb0 hb h1 h2
  have hθ : ‖thetaStar b E s‖ ≤ ρ := (thetaStar_le_bulk hb0 hb hκI hE hs).trans (le_max_left _ _)
  set P := growthPathLaw W b
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hWK : K / etaLow b κI ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWK')
  set r₀ := ⌈ε * W / 2⌉₊
  have hr₀a : ε * W / 2 ≤ r₀ := Nat.le_ceil _
  have hr₀b : (r₀ : ℝ) < ε * W / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hr₀1 : 1 ≤ r₀ := Nat.one_le_iff_ne_zero.mpr (by
    intro h; rw [h] at hr₀a; simp at hr₀a; nlinarith [mul_pos hε hW0])
  have hr₀r : r₀ ≤ r := Nat.ceil_le.mpr (by
    have := mul_pos hε hW0; have : ε * W ≤ r := hr1; linarith)
  -- moments on `r₀ ≤ j ≤ TW`
  have hrange : ∀ j : ℕ, r₀ ≤ j → (j : ℝ) ≤ T * W →
      eLpNorm (fun ω => passiveMass b E (pathNearSchur b E κ W j ω)) (ENNReal.ofReal (2 * p')) P ≤
          ENNReal.ofReal Kq ∧
        eLpNorm (fun ω => jetDistance0 b E (pathNearSchur b E κ W j ω)) (ENNReal.ofReal (2 * p'))
          P ≤ ENNReal.ofReal (D / W) ∧
        eLpNorm (fun ω => mx_jet1 b E s (pathNearSchur b E κ W j ω)) (ENNReal.ofReal (2 * p'))
          P ≤ ENNReal.ofReal (D / W) := by
    intro j hj0 hjT
    have hjr : ε / 2 * W ≤ j := by
      have : ε * W / 2 ≤ (j : ℝ) := hr₀a.trans (by exact_mod_cast hj0)
      linarith
    have hj1 : 1 ≤ j := hr₀1.trans hj0
    have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
    refine ⟨(hq W hWq E hE κ hκK j hj1 hjT).trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
    · have : (W : ℝ) / j ≤ 2 / ε := by
        rw [div_le_div_iff₀ hjpos hε]; nlinarith
      have := mul_le_mul_of_nonneg_left (add_le_add_right this 1) hKm0
      simpa only [Kq, add_comm] using this
    have hJ := hj W hWj E hE s hs j hjr hjT
    have hae : (fun ω => jetDistance1 b E s (pathNearSchur b E κ W j ω)) =ᵐ[P]
        fun ω => mx_jet1 b E s (pathNearSchur b E κ W j ω) := by
      filter_upwards [ae_passiveSample W hκ0 hb1 h1 h2] with ω hP
      exact mx_jet1_eq hb1 h1 h2 s (pathNearSchur_passive hP j)
    rw [eLpNorm_congr_ae hae] at hJ
    have hDW : ENNReal.ofReal (Cj / W) ≤ ENNReal.ofReal (D / W) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hW0.le)
    exact ⟨(le_add_right le_rfl).trans (hJ.trans hDW), (le_add_left le_rfl).trans (hJ.trans hDW)⟩
  -- the start `‖mixSum(X_{r₀})‖_{p'} ≤ 2ΛK_q`
  have hr₀T : (r₀ : ℝ) ≤ T * W := (by exact_mod_cast hr₀r : (r₀ : ℝ) ≤ r).trans hr2
  have hmS : ∀ j, Measurable fun ω => mixSum b E (pathNearSchur b E κ W j ω) := fun j =>
    (measurable_mixSum b E).comp (measurable_pathNearSchur' b E κ j)
  have hstart : eLpNorm (fun ω => mixSum b E (pathNearSchur b E κ W r₀ ω)) (ENNReal.ofReal p') P ≤
      ENNReal.ofReal (2 * Λ * Kq) := by
    have hle : eLpNorm (fun ω => mixSum b E (pathNearSchur b E κ W r₀ ω)) (ENNReal.ofReal p') P ≤
        eLpNorm (fun ω => 2 * Λ * passiveMass b E (pathNearSchur b E κ W r₀ ω))
          (ENNReal.ofReal p') P := by
      refine eLpNorm_mono_ae_real (hmS r₀).aestronglyMeasurable ?_
      filter_upwards [ae_passiveSample W hκ0 hb1 h1 h2] with ω hP
      rw [Real.norm_of_nonneg (mixSum_nonneg _ _ _)]
      exact mixSum_le_mass hb0 hb hκI hE (pathNearSchur_passive hP r₀)
    refine hle.trans (mx_const_mul_le (by positivity) ?_)
    exact (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))).trans
      (hrange r₀ le_rfl hr₀T).1
  -- the absorbed recursion
  have hae := ae_mix_step (C := C) hb0 hb h1 h2 hW1 hκK hρ0 s
  have hrec := linrec_from P (y := fun j ω => mixSum b E (pathNearSchur b E κ W j ω))
    (e := mixForce b E κ ρ C s W) (ENNReal.one_le_ofReal.2 hp') hρ0 hρ1 (by positivity)
    (by positivity : 0 ≤ Bm / Real.sqrt W) hr₀1 hr₀r (fun j ω => mixSum_nonneg _ _ _)
    (fun j => (hmS j).aestronglyMeasurable)
    (fun j hj _ => hae.mono fun ω hω => hω j (hr₀1.trans hj)) hstart
    (fun j hj0 hjr => by
      have hjT : (j : ℝ) ≤ T * W := (by exact_mod_cast hjr.le : (j : ℝ) ≤ r).trans hr2
      obtain ⟨a, c, d⟩ := hrange j hj0 hjT
      exact eLpNorm_mixForce_le hb0 hb hκI hE hκK s hW1 hWK j hp' hKq (le_max_right _ _) hρ0 hC
        hC' (fun X hX => hL W hW₁ E hE s hs hθ X hX) a c d)
  -- back to the two atoms at exponent `p`
  have hmono : ENNReal.ofReal p ≤ ENNReal.ofReal p' := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hS := (eLpNorm_le_eLpNorm_of_exponent_le hmono).trans hrec
  have a1 : eLpNorm (fun ω => (passiveQ b E (pathNearSchur b E κ W r ω) *
      passiveF b E (pathNearSchur b E κ W r ω)).trace) (ENNReal.ofReal p) P ≤
      eLpNorm (fun ω => mixSum b E (pathNearSchur b E κ W r ω)) (ENNReal.ofReal p) P :=
    eLpNorm_mono_real ((measurable_traceQF b E).comp
      (measurable_pathNearSchur' b E κ r)).aestronglyMeasurable fun ω =>
        le_add_of_le_of_nonneg le_rfl (mx_G_nonneg_hs b E _)
  have a2 : eLpNorm (fun ω => hsSandwich (passiveQ b E (pathNearSchur b E κ W r ω))
      (passiveF b E (pathNearSchur b E κ W r ω))) (ENNReal.ofReal p) P ≤
      eLpNorm (fun ω => mixSum b E (pathNearSchur b E κ W r ω)) (ENNReal.ofReal p) P :=
    eLpNorm_mono_real ((measurable_mx_hsG b E).comp
      (measurable_pathNearSchur' b E κ r)).aestronglyMeasurable fun ω => by
        rw [Real.norm_of_nonneg (show 0 ≤ hsSandwich _ _ from mx_G_nonneg_hs b E _)]
        exact le_add_of_nonneg_left (mx_G_nonneg_tr b E _)
  have hpow : ρ ^ (r - r₀) ≤ 2 / W := by
    have h := PathJet.pow_le_two_div (W := W) (r := r - r₀ + 1) hρh hρ1 hW1 (by omega) (by
      rw [Nat.cast_add, Nat.cast_sub hr₀r, Nat.cast_one]
      have := hl W hWl
      have : ε * W ≤ r := hr1
      linarith)
    simpa using h
  refine (add_le_add (a1.trans hS) (a2.trans hS)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := mix_final_arith (B := Bm) (by positivity : 0 ≤ 2 * Λ * Kq) hρ1 hWr hpow
  linarith

end BlockBand.Transmission.Absorbed
