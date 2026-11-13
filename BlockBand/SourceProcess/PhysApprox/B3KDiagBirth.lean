module

public import BlockBand.SourceProcess.PhysApprox.B3KDiagStep
public import BlockBand.SourceProcess.PhysApprox.B3ClosedForm
public import BlockBand.SourceProcess.PhysApprox.B3BirthKSubBirth
public import BlockBand.SourceProcess.PhysApprox.B3BirthKSum
public import BlockBand.SourceProcess.PhysApprox.B3BirthMDiag
public import BlockBand.SourceProcess.PhysApprox.B3MomK
public import BlockBand.SourceProcess.RawTag.StepScalar
public import BlockBand.SourceProcess.RawTag.MomentTools

/-!
# The summed births `KStopBirthSum`, without jet input

`KStopBirthSum` asks for the fourth moment of the sum of the stopped `𝒦_cl`
steps over the at most `np` birth steps. Here every **single** stopped step
`Z_i = 1_{A_i}(𝒦_cl,i+1 − 𝒦_cl,i)_{ab}` has `E|Z_i|⁴ ≤ C_R` (`lintegral_kStopStep_four_bounded`):

* both tags old: `ClosedKStepForm b3ClosedX` (`closedKStepForm_holds`) writes `Z_i = u*Δv` with
  frames `≤ √R`, and the fresh fourth moment `C C_f⁸(δ₀ + W^{-1/2})⁴` is bounded with the
  deterministic port bound `δ₀ ≤ η⁻¹ + 1`; **no jet input**;
* a tag born at `i`: `Z_i = 1_{A_i}𝒦_cl,i+1(a, a')` and the closed birth identities
  (`closedK_birth_old_new`, `closedK_birth_new_old`, `closedK_birth_new_new'` below, with
  `birthG_eq`, `birthK_mul_birthG`) give `𝒦_cl,i+1(a, a') = B + u'*Δ(X_cl, F_i)v'` with
  `|B|, ‖u'‖‖v'‖ ≤ L(1 + ‖c g_a‖² + ‖c g_{a'}‖²)` (`‖R_cl‖ ≤ η⁻¹`, old frames clipped at `√R`
  on `A_i`); the fresh fourth moment (`lintegral_closed_four_le`) and the Gaussian eighth
  moments of the probes (`lintegral_probe_eight_le`) bound it;
* a tag unborn at `i + 1`: `Z_i = 0`.

Hence **`kStopBirthSum_holds`**: `GaussianAbsorptionContract`, `GaussianLpGradient` ⇒
`KStopBirthSum`. So the maximal stopped `𝒦` moment needs neither `ComplexKCorrMoment` nor
`ClosedTraceFour`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.KDiag

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.ClosingAux
open BlockBand.SourceProcess.PhysApprox.B3.BirthKSub
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W np : ℕ}

/-!
## Small algebra
-/

theorem add_pow_four_le_real {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (a + c) ^ 4 ≤ 8 * (a ^ 4 + c ^ 4) := by
  nlinarith [mul_nonneg (sq_nonneg (a - c))
    (by positivity : (0 : ℝ) ≤ 7 * a ^ 2 + 10 * a * c + 7 * c ^ 2)]

theorem bilinear_add_mid (u : Fin W → ℂ) (A B : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) :
    bilinear u (A + B) v = bilinear u A v + bilinear u B v := by
  simp only [bilinear, add_mulVec, dotProduct_add]

theorem bilinear_mul_right' (u : Fin W → ℂ) (A B : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) :
    bilinear u (A * B) v = bilinear u A (B *ᵥ v) := by
  simp only [bilinear, ← mulVec_mulVec]

theorem bilinear_mul_left' (u : Fin W → ℂ) (A B : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) :
    bilinear u (A * B) v = bilinear (Aᴴ *ᵥ u) B v := by
  rw [bilinear, bilinear, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec,
    conjTranspose_conjTranspose, ← dotProduct_mulVec]

theorem bilinear_mul_mul' (u : Fin W → ℂ) (A B C : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) :
    bilinear u (A * B * C) v = bilinear (Aᴴ *ᵥ u) B (C *ᵥ v) := by
  rw [bilinear_mul_right', bilinear_mul_left']

theorem norm_bilinear_one_le (u v : Fin W → ℂ) : ‖bilinear u 1 v‖ ≤ vecNorm u * vecNorm v := by
  refine (norm_bilinear_le u 1 v).trans ?_
  have h := norm_one_matrix_le (n := Fin W)
  have hu := vecNorm_nonneg u
  have hv := vecNorm_nonneg v
  calc vecNorm u * ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ * vecNorm v ≤ vecNorm u * 1 * vecNorm v := by
        gcongr
    _ = vecNorm u * vecNorm v := by ring

theorem kdiag_clipVec_of_le {C : ℝ} {w : Fin W → ℂ} (h : vecNorm w ≤ C) : clipVec C w = w := by
  simp [clipVec, h]

theorem kdiag_L_bounds {r e : ℝ} (hr : 0 ≤ r) (he : 0 ≤ e) :
    e ≤ (r + 1) * (e + 1) ^ 2 ∧ e * e ≤ (r + 1) * (e + 1) ^ 2 ∧ r ≤ (r + 1) * (e + 1) ^ 2 ∧
      r * e ≤ (r + 1) * (e + 1) ^ 2 := by
  have h1 : 1 ≤ (e + 1) ^ 2 := by nlinarith
  have h2 : e + 1 ≤ (e + 1) ^ 2 := by nlinarith
  have h3 : (e + 1) ^ 2 ≤ (r + 1) * (e + 1) ^ 2 := by nlinarith
  refine ⟨by linarith, by nlinarith, by nlinarith, by nlinarith⟩

theorem mul_le_one_add_sq (a c : ℝ) : a * c ≤ 1 + a ^ 2 + c ^ 2 := by
  nlinarith [sq_nonneg (a - c)]

theorem le_one_add_sq_left {a c : ℝ} : a ≤ 1 + a ^ 2 + c ^ 2 := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg c]

theorem le_one_add_sq_right {a c : ℝ} : c ≤ 1 + a ^ 2 + c ^ 2 := by
  nlinarith [sq_nonneg (c - 1), sq_nonneg a]

/-!
## One fresh step at order 4 with any frames
-/

/-- **One fresh step at order 4** (from the contract hypotheses): for passive `X`,
`E_F|u*Δ(X, F)v|⁴ ≤ C_q(‖u‖‖v‖)⁴`, uniformly in `W ≥ W₀` (port bound `δ₀ ≤ η⁻¹ + 1`). -/
theorem lintegral_fresh_four_le (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) :
    ∃ (Cq : ℝ) (W₀ : ℕ), 0 ≤ Cq ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ u v : Fin W → ℂ,
        ∫⁻ F, ENNReal.ofReal (‖bilinear u (freshDelta b E X F) v‖ ^ 4) ∂freshLaw W b ≤
          ENNReal.ofReal (Cq * (vecNorm u * vecNorm v) ^ 4) := by
  obtain ⟨hκ, hEκ⟩ := StepFresh.bulk_of_lt hE1 hE2
  obtain ⟨Cm, Cf, W₁, hCm, hCf, hDl⟩ :=
    RawTag.delta_fresh_bounds hGA hLp b hb0 hb _ hκ 4 (by norm_num)
  have hη : 0 < etaZ b E := etaZ_pos b E (by linarith) hE1 hE2
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = (etaZ b E)⁻¹ + 1 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    have := inv_pos.2 hη
    linarith
  have hCq : 0 ≤ 8 * ((Cm * (D + 1)) ^ 4 + (Cf * (D + 1)) ^ 4) := by positivity
  refine ⟨8 * ((Cm * (D + 1)) ^ 4 + (Cf * (D + 1)) ^ 4), max W₁ 1, hCq,
    fun W hW X hX u v => ?_⟩
  have hW₁ : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
  obtain ⟨hI, hmean, hF⟩ := hDl W hW₁ E hEκ X hX
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hδD : jetDistance0 b E X ≤ D := hDdef ▸ jetDistance0_le_bound hb0 hb hE1 hE2 hX
  have hWinv : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
  have hsqinv : (Real.sqrt W)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 hW1)
  generalize hδdef : jetDistance0 b E X = δ at hmean hF hδ0 hδD
  generalize hMdef : matrixExpect (freshLaw W b) (freshDelta b E X) = M at hmean hF
  have hN0 : 0 ≤ vecNorm u * vecNorm v := mul_nonneg (vecNorm_nonneg u) (vecNorm_nonneg v)
  have hμ : ‖bilinear u M v‖ ≤ Cm * (D + 1) * (vecNorm u * vecNorm v) := by
    refine (norm_bilinear_le u M v).trans ?_
    have h1 : ‖M‖ ≤ Cm * (D + 1) := hmean.trans (mul_le_mul_of_nonneg_left (by linarith) hCm)
    calc vecNorm u * ‖M‖ * vecNorm v = ‖M‖ * (vecNorm u * vecNorm v) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 hN0
  have hu0 := vecNorm_nonneg u
  have hv0 := vecNorm_nonneg v
  have hs0 : 0 ≤ Cf * ((Real.sqrt W)⁻¹ + δ) * vecNorm u * vecNorm v := by positivity
  have hsle : Cf * ((Real.sqrt W)⁻¹ + δ) * vecNorm u * vecNorm v ≤
      Cf * (D + 1) * (vecNorm u * vecNorm v) := by
    rw [mul_assoc (Cf * ((Real.sqrt W)⁻¹ + δ))]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hCf) hN0
  have hdecomp : ∀ F, bilinear u (freshDelta b E X F) v =
      bilinear u M v + bilinear u (freshDelta b E X F - M) v := by
    intro F
    rw [RawTag.bilinear_sub_mid]
    ring
  have hDM : ∀ i j, Integrable (fun F => (freshDelta b E X F - M) i j) (freshLaw W b) :=
    fun i j => (hI i j).sub (integrable_const _)
  have hdi : Integrable (fun F => bilinear u (freshDelta b E X F - M) v) (freshLaw W b) :=
    FullSource.integrable_bilinear (fun F => freshDelta b E X F - M) hDM u v
  have hFl : eLpNorm (fun F => bilinear u (freshDelta b E X F - M) v)
      (ENNReal.ofReal (4 * ((1 : ℕ) : ℝ))) (freshLaw W b) ≤
      ENNReal.ofReal (Cf * ((Real.sqrt W)⁻¹ + δ) * vecNorm u * vecNorm v) := by
    have e : (4 * ((1 : ℕ) : ℝ)) = 4 := by norm_num
    rw [e]
    exact hF u v
  have hdm := RawTag.lintegral_pow_le_of_eLpNorm hdi.aestronglyMeasurable (m := 1) le_rfl hs0
    hFl
  simp only [Nat.reduceMul] at hdm
  have hpt : ∀ F, ENNReal.ofReal (‖bilinear u (freshDelta b E X F) v‖ ^ 4) ≤
      ENNReal.ofReal (8 * ‖bilinear u M v‖ ^ 4) +
        ENNReal.ofReal 8 * ENNReal.ofReal ((‖bilinear u (freshDelta b E X F - M) v‖ ^ 2) ^ 2) := by
    intro F
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add
      (by positivity : (0 : ℝ) ≤ 8 * ‖bilinear u M v‖ ^ 4)
      (by positivity : (0 : ℝ) ≤ 8 * (‖bilinear u (freshDelta b E X F - M) v‖ ^ 2) ^ 2)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hdecomp F]
    have h1 := norm_add_le (bilinear u M v) (bilinear u (freshDelta b E X F - M) v)
    have h2 := add_pow_four_le_real (norm_nonneg (bilinear u M v))
      (norm_nonneg (bilinear u (freshDelta b E X F - M) v))
    have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 4
    have e : (‖bilinear u (freshDelta b E X F - M) v‖ ^ 2) ^ 2 =
        ‖bilinear u (freshDelta b E X F - M) v‖ ^ 4 := by ring
    rw [e]
    linarith
  calc ∫⁻ F, ENNReal.ofReal (‖bilinear u (freshDelta b E X F) v‖ ^ 4) ∂freshLaw W b
      ≤ ∫⁻ F, (ENNReal.ofReal (8 * ‖bilinear u M v‖ ^ 4) + ENNReal.ofReal 8 *
          ENNReal.ofReal ((‖bilinear u (freshDelta b E X F - M) v‖ ^ 2) ^ 2)) ∂freshLaw W b :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (8 * ‖bilinear u M v‖ ^ 4) + ENNReal.ofReal 8 *
          ∫⁻ F, ENNReal.ofReal ((‖bilinear u (freshDelta b E X F - M) v‖ ^ 2) ^ 2)
            ∂freshLaw W b := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (8 * (Cm * (D + 1) * (vecNorm u * vecNorm v)) ^ 4) + ENNReal.ofReal 8 *
          ENNReal.ofReal ((Cf * (D + 1) * (vecNorm u * vecNorm v)) ^ 4) := by
        exact add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) hμ 4) (by norm_num)))
          (mul_le_mul_right (hdm.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hs0 hsle 4))) _)
    _ = ENNReal.ofReal (8 * ((Cm * (D + 1)) ^ 4 + (Cf * (D + 1)) ^ 4) *
          (vecNorm u * vecNorm v) ^ 4) := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        ring

/-- **One closed fresh step at order 4 with any past-determined frames** (fresh-layer Fubini). -/
theorem lintegral_closed_four_le (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) :
    ∃ (Cq : ℝ) (W₀ : ℕ), 0 ≤ Cq ∧ ∀ W : ℕ, W₀ ≤ W → ∀ (np j : ℕ)
      (u v : ProbedPath W np × ℝ → Fin W → ℂ)
      (X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ),
      Measurable u → Measurable v → Measurable X →
      (∀ y, u (b3Ext W j y) = u y) → (∀ y, v (b3Ext W j y) = v y) →
      (∀ y, X (b3Ext W j y) = X y) →
      (∀ᵐ y ∂closedLaw b W np, (passiveY (X y)).PosSemidef) →
        ∫⁻ y, ENNReal.ofReal (‖bilinear (u y)
            (freshDelta b E (X y) (freshSample W j y.1.1)) (v y)‖ ^ 4) ∂closedLaw b W np ≤
          ∫⁻ y, ENNReal.ofReal (Cq * (vecNorm (u y) * vecNorm (v y)) ^ 4)
            ∂closedLaw b W np := by
  obtain ⟨Cq, W₀, hCq, H⟩ := lintegral_fresh_four_le hGA hLp hb0 hb hE1 hE2
  refine ⟨Cq, W₀, hCq, fun W hW np j u v X hu hv hX hu' hv' hX' hpas => ?_⟩
  set μ := closedLaw b W np
  set μP := (pastLaw W j b).prod
    ((Measure.pi fun _ : Fin np => circularVectorLaw (Fin W)).prod phaseLaw)
  set π : ProbedPath W np × ℝ → PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) :=
    fun y => (pastCoords W j y.1.1, (y.1.2, y.2))
  set r : PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) → ProbedPath W np × ℝ :=
    fun p => ((extPast W j p.1, p.2.1), p.2.2)
  have hπ : Measurable π := measurable_b3Sigma_map W j np
  have hr : Measurable r :=
    (((measurable_extPast j).comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)
  set φ : ProbedPath W np × ℝ → LayerSample W .oneBlockOnePort := fun y => freshSample W j y.1.1
  have hφ : Measurable φ := (measurable_freshSample W j).comp (measurable_fst.comp measurable_fst)
  have hmap : μ.map (fun y => (π y, φ y)) = μP.prod (freshLaw W b) :=
    closedPastFreshLaw_holds b W np j
  have hmapπ : μ.map π = μP := by
    have h := congrArg (fun m => m.map Prod.fst) hmap
    rw [Measure.map_map measurable_fst (hπ.prodMk hφ), Measure.map_fst_prod, measure_univ,
      one_smul] at h
    exact h
  have hrπ : ∀ y, r (π y) = b3Ext W j y := fun y => rfl
  have hpasP : ∀ᵐ p ∂μP, (passiveY (X (r p))).PosSemidef := by
    have hset : MeasurableSet {p | (passiveY (X (r p))).PosSemidef} :=
      (hX.comp hr) step_measurableSet_passive
    rw [← hmapπ, ae_map_iff hπ.aemeasurable hset]
    filter_upwards [hpas] with y hy
    rw [hrπ, hX']
    exact hy
  have hDm : Measurable fun z : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
      LayerSample W .oneBlockOnePort => freshDelta b E (X (r z.1)) z.2 :=
    FullSource.measurable_freshDelta_comp b E ((hX.comp hr).comp measurable_fst) measurable_snd
  set Φ : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort →
      ℝ≥0∞ := fun z => ENNReal.ofReal (‖bilinear (u (r z.1))
        (freshDelta b E (X (r z.1)) z.2) (v (r z.1))‖ ^ 4) with hΦdef
  have hΦ : Measurable Φ :=
    ENNReal.measurable_ofReal.comp ((RawTag.measurable_bilinear_jt
      ((hu.comp hr).comp measurable_fst) hDm ((hv.comp hr).comp measurable_fst)).norm.pow_const 4)
  set Ψ : PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Cq * (vecNorm (u (r p)) * vecNorm (v (r p))) ^ 4) with hΨdef
  have hΨ : Measurable Ψ :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (((measurable_vecNorm_comp (hu.comp hr)).mul (measurable_vecNorm_comp (hv.comp hr))).pow_const
        4))
  calc ∫⁻ y, ENNReal.ofReal (‖bilinear (u y)
          (freshDelta b E (X y) (freshSample W j y.1.1)) (v y)‖ ^ 4) ∂μ
      = ∫⁻ y, Φ (π y, φ y) ∂μ := by
        refine lintegral_congr fun y => ?_
        simp only [Φ, hrπ, hu', hv', hX', φ]
    _ = ∫⁻ z, Φ z ∂(μP.prod (freshLaw W b)) := by
        rw [← hmap, lintegral_map hΦ (hπ.prodMk hφ)]
    _ = ∫⁻ p, ∫⁻ F, Φ (p, F) ∂freshLaw W b ∂μP := lintegral_prod _ hΦ.aemeasurable
    _ ≤ ∫⁻ p, Ψ p ∂μP := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpasP] with p hp
        exact H W hW (X (r p)) hp (u (r p)) (v (r p))
    _ = ∫⁻ y, Ψ (π y) ∂μ := by rw [← hmapπ, lintegral_map hΨ hπ]
    _ = ∫⁻ y, ENNReal.ofReal (Cq * (vecNorm (u y) * vecNorm (v y)) ^ 4) ∂μ := by
        refine lintegral_congr fun y => ?_
        simp only [Ψ, hrπ, hu', hv']

/-!
## Gaussian moments of the probes
-/

theorem vecNorm_sq_eq (w : Fin W → ℂ) : vecNorm w ^ 2 = ∑ a, ‖w a‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem vecNorm_real_smul_sq (r : ℝ) (w : Fin W → ℂ) :
    vecNorm (((r : ℝ) : ℂ) • w) ^ 2 = r ^ 2 * vecNorm w ^ 2 := by
  rw [vecNorm_sq_eq, vecNorm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem vecNorm_probe_pow_eight (W : ℕ) {c : ℝ} (hc : 0 ≤ c) (g : Fin W → ℂ) :
    vecNorm (((Real.sqrt (c / W) : ℝ) : ℂ) • g) ^ 8 =
      c ^ 4 * vecNorm (RawTag.unitVec W g) ^ 8 := by
  have hu : RawTag.unitVec W g = ((Real.sqrt (1 / W) : ℝ) : ℂ) • g := by
    funext a
    simp [RawTag.unitVec]
  have e8 : ∀ t : ℝ, t ^ 8 = (t ^ 2) ^ 4 := fun t => by ring
  rw [hu, e8, e8, vecNorm_real_smul_sq, vecNorm_real_smul_sq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)]
  ring

/-- **Eighth moment of a mass-`c` probe** `√(c/W)g_k` under `closedLaw`. -/
theorem lintegral_probe_eight_le (b : ℝ) (hW : 1 ≤ W) (k : Fin np) {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ y, ENNReal.ofReal (vecNorm (((Real.sqrt (c / W) : ℝ) : ℂ) • y.1.2 k) ^ 8)
        ∂closedLaw b W np ≤
      ENNReal.ofReal (c ^ 4 * ((2 * RawTag.gaussMoment 8) ^ (1 / 8 : ℝ)) ^ 8) := by
  set f : (Fin W → ℂ) → ℝ≥0∞ := fun g =>
    ENNReal.ofReal (vecNorm (((Real.sqrt (c / W) : ℝ) : ℂ) • g) ^ 8) with hfdef
  have hf : Measurable f := ENNReal.measurable_ofReal.comp
    ((measurable_vecNorm.comp (continuous_const_smul _).measurable).pow_const 8)
  have hG := RawTag.gaussMoment_nonneg 8
  have hCg : 0 ≤ (2 * RawTag.gaussMoment 8) ^ (1 / 8 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hmom := RawTag.lintegral_pow_le_of_momBd' (μ := circularVectorLaw (Fin W)) (n := 8)
    (by norm_num) (by exact_mod_cast RawTag.momBd_unitVec (r := 8) (by norm_num) W hW) hCg
    (fun g => vecNorm_nonneg _)
  calc ∫⁻ y, f (y.1.2 k) ∂closedLaw b W np = ∫⁻ x, f (x.2 k) ∂probedPathLaw W np b :=
        lintegral_closedLaw_fst b (hf.comp ((measurable_pi_apply k).comp measurable_snd))
    _ = ∫⁻ ω, ∫⁻ g, f g ∂circularVectorLaw (Fin W) ∂growthPathLaw W b :=
        BirthM.lintegral_probed_eval b k (hf.comp measurable_snd)
    _ = ∫⁻ g, f g ∂circularVectorLaw (Fin W) := by rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ g, ENNReal.ofReal (c ^ 4) * ENNReal.ofReal (vecNorm (RawTag.unitVec W g) ^ 8)
          ∂circularVectorLaw (Fin W) := by
        refine lintegral_congr fun g => ?_
        rw [hfdef]
        beta_reduce
        rw [vecNorm_probe_pow_eight W hc g, ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (c ^ 4) * ∫⁻ g, ENNReal.ofReal (vecNorm (RawTag.unitVec W g) ^ 8)
          ∂circularVectorLaw (Fin W) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (c ^ 4) *
          ENNReal.ofReal (((2 * RawTag.gaussMoment 8) ^ (1 / 8 : ℝ)) ^ 8) :=
        mul_le_mul_right hmom _
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

/-!
## The newborn/newborn closed entry
-/

/-- **New/new for two tags born at the same step**: `𝒦_cl,l+1(k, k') = (c g_k)*𝒢(c' g_{k'})`
(`closedK_birth_new_new` with two columns). -/
theorem closedK_birth_new_new' (b E s h : ℝ) (τ m : Fin np → ℝ) {l : ℕ}
    (y : ProbedPath W np × ℝ) (hblk : GclSuccBlocks b E s h W l y.1.1 (phase y.2))
    {k k' : Fin np} (hk : ⌊(W : ℝ) * τ k⌋₊ = l) (hk' : ⌊(W : ℝ) * τ k'⌋₊ = l) :
    b3ClosedKAt b E s h τ m W (l + 1) y k k' =
      bilinear (((Real.sqrt (m k / W) : ℝ) : ℂ) • y.1.2 k) (birthG b E s h W l y.1.1 (phase y.2))
        (((Real.sqrt (m k' / W) : ℝ) : ℂ) • y.1.2 k') := by
  rw [b3ClosedKAt_eq_gcl, entry_eq_dot, RawTag.dot_reindex (headEquiv l W),
    probeColumns_comp_new τ m y.1.2 hk, probeColumns_comp_new τ m y.1.2 hk', hblk,
    RawTag.dot_fromBlocks]
  simp only [star_zero, zero_dotProduct, mulVec_zero, add_zero]
  rfl

/-!
## Every stopped step has a bounded fourth moment
-/

theorem one_add_add_pow_four_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (1 + A + B) ^ 4 ≤ 64 * (1 + A ^ 4 + B ^ 4) := by
  have h1 := add_pow_four_le_real zero_le_one (add_nonneg hA hB)
  have h2 := add_pow_four_le_real hA hB
  rw [one_pow] at h1
  have e : 1 + A + B = 1 + (A + B) := by ring
  rw [e]
  linarith

theorem lintegral_sum3_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {F a c : α → ℝ} (ha : Measurable fun x => ENNReal.ofReal (a x))
    (ha0 : ∀ x, 0 ≤ a x) (hc0 : ∀ x, 0 ≤ c x) (hF : ∀ x, F x ≤ 64 + 64 * a x + 64 * c x)
    {A C : ℝ} (hA0 : 0 ≤ A) (hC0 : 0 ≤ C) (hA : ∫⁻ x, ENNReal.ofReal (a x) ∂μ ≤ ENNReal.ofReal A)
    (hC : ∫⁻ x, ENNReal.ofReal (c x) ∂μ ≤ ENNReal.ofReal C) :
    ∫⁻ x, ENNReal.ofReal (F x) ∂μ ≤ ENNReal.ofReal (64 + 64 * A + 64 * C) := by
  have h64 : (0 : ℝ) ≤ 64 := by norm_num
  calc ∫⁻ x, ENNReal.ofReal (F x) ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal 64 + ENNReal.ofReal 64 * ENNReal.ofReal (a x) +
          ENNReal.ofReal 64 * ENNReal.ofReal (c x)) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul h64, ← ENNReal.ofReal_mul h64,
          ← ENNReal.ofReal_add h64 (mul_nonneg h64 (ha0 x)),
          ← ENNReal.ofReal_add (add_nonneg h64 (mul_nonneg h64 (ha0 x)))
            (mul_nonneg h64 (hc0 x))]
        exact ENNReal.ofReal_le_ofReal (hF x)
    _ = ENNReal.ofReal 64 + ENNReal.ofReal 64 * ∫⁻ x, ENNReal.ofReal (a x) ∂μ +
          ENNReal.ofReal 64 * ∫⁻ x, ENNReal.ofReal (c x) ∂μ := by
        have hm : Measurable fun x =>
            ENNReal.ofReal 64 + ENNReal.ofReal 64 * ENNReal.ofReal (a x) :=
          measurable_const.add (ha.const_mul _)
        rw [lintegral_add_left hm, lintegral_add_left measurable_const, lintegral_const,
          measure_univ, mul_one, lintegral_const_mul _ ha,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal 64 + ENNReal.ofReal 64 * ENNReal.ofReal A +
          ENNReal.ofReal 64 * ENNReal.ofReal C :=
        add_le_add (add_le_add le_rfl (mul_le_mul_right hA _)) (mul_le_mul_right hC _)
    _ = ENNReal.ofReal (64 + 64 * A + 64 * C) := by
        rw [← ENNReal.ofReal_mul h64, ← ENNReal.ofReal_mul h64,
          ← ENNReal.ofReal_add h64 (mul_nonneg h64 hA0),
          ← ENNReal.ofReal_add (add_nonneg h64 (mul_nonneg h64 hA0)) (mul_nonneg h64 hC0)]

/-- **Every stopped closed `𝒦` step has a bounded fourth moment** (all steps, all entries; no jet
input): from the contract hypotheses, `ClosedKStepForm b3ClosedX` and the closed birth
identities. -/
theorem lintegral_kStopStep_four_bounded (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ W in atTop,
        ∀ i ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, ∀ ij : Fin np × Fin np,
          ∫⁻ y, ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ∂closedLaw b W np ≤
            ENNReal.ofReal C := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hb0, hb, hE1, hE2, -, -, hm0, -⟩ := hF.1
  have hh : h ^ 2 < 1 := by nlinarith [hF.2.2.2.1, hF.2.2.2.2.1]
  have hη : 0 < etaZ b E := etaZ_pos b E (by linarith) hE1 hE2
  have hηZ : 0 < (boundaryZ b E).im := boundaryZ_im_pos (by linarith) hE1 hE2
  obtain ⟨C4, W₄, hC4, H4⟩ :=
    lintegral_closed_bilinear_four_le hGA hLp closedPastFreshLaw_holds hb0 hb hE1 hE2
  obtain ⟨Cf, hCf⟩ := closedKStepForm_holds b E np τ m T s h K Vs hF R
  obtain ⟨Cq, Wq, hCq, Hq⟩ := lintegral_closed_four_le hGA hLp hb0 hb hE1 hE2
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = (etaZ b E)⁻¹ := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by
    rw [he]
    exact (inv_pos.2 hη).le
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = (Real.sqrt R + 1) * (e + 1) ^ 2 := ⟨_, rfl⟩
  obtain ⟨hLe, hLee, hLr, hLre⟩ := kdiag_L_bounds (Real.sqrt_nonneg R) he0
  rw [← hL] at hLe hLee hLr hLre
  have hL0 : 0 ≤ L := he0.trans hLe
  obtain ⟨Mm, hMm⟩ : ∃ Mm : ℝ, Mm = ∑ k, m k := ⟨_, rfl⟩
  have hmM : ∀ k, m k ≤ Mm := fun k => by
    rw [hMm]
    exact Finset.single_le_sum (fun k _ => hm0 k) (Finset.mem_univ k)
  have hMm0 : 0 ≤ Mm := by
    rw [hMm]
    exact Finset.sum_nonneg fun k _ => hm0 k
  obtain ⟨Cg, hCgd⟩ : ∃ Cg : ℝ, Cg = ((2 * RawTag.gaussMoment 8) ^ (1 / 8 : ℝ)) ^ 8 :=
    ⟨_, rfl⟩
  have hCg : 0 ≤ Cg := by
    rw [hCgd]
    positivity
  obtain ⟨Cold, hCold⟩ : ∃ C : ℝ, C = C4 * max Cf 0 ^ 8 * (e + 2) ^ 4 := ⟨_, rfl⟩
  obtain ⟨Cnew, hCnew⟩ : ∃ C : ℝ,
      C = (8 * L ^ 4 + 8 * (Cq * L ^ 4)) * (64 * (1 + 2 * (Mm ^ 4 * Cg))) := ⟨_, rfl⟩
  have hCold0 : 0 ≤ Cold := by
    rw [hCold]
    positivity
  have hCnew0 : 0 ≤ Cnew := by
    rw [hCnew]
    positivity
  refine ⟨Cold + Cnew, by linarith, ?_⟩
  filter_upwards [hCf, eventually_ge_atTop (max (max W₄ Wq) 1),
    B3Cur.eventually_one_le_closeLen hF.2.1] with W hCfW hW hs1 i hi ij
  have hW₄ : W₄ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWq : Wq ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 hi
  have hci : 1 ≤ i := hs1.trans hi1
  have hCC : ENNReal.ofReal Cold ≤ ENNReal.ofReal (Cold + Cnew) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hCC' : ENNReal.ofReal Cnew ≤ ENNReal.ofReal (Cold + Cnew) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  -- a tag unborn at `i + 1`
  by_cases hun : i + 1 ≤ ⌊(W : ℝ) * τ ij.1⌋₊ ∨ i + 1 ≤ ⌊(W : ℝ) * τ ij.2⌋₊
  · have h0 : ∀ y, kStopStep b E s h τ m R W i (Vs W) ij y = 0 := fun y =>
      kStopStep_eq_zero_of_unborn b E s h τ m R W i (Vs W) ij hun y
    simp only [h0, enorm_zero]
    simp
  simp only [not_or, not_le] at hun
  -- two old tags
  by_cases hold : ⌊(W : ℝ) * τ ij.1⌋₊ < i ∧ ⌊(W : ℝ) * τ ij.2⌋₊ < i
  · obtain ⟨hXm, hXi, hXp, hform⟩ := hCfW i hi
    obtain ⟨u, v, hu, hv, hu', hv', hub, hvb, hae⟩ := hform ij hold.1 hold.2
    rw [lintegral_congr_ae (hae.mono fun y hy => by rw [hy])]
    refine ((H4 W hW₄ np i u v (b3ClosedX b E s h τ m W i) (max Cf 0) hu hv hXm
      (le_max_right _ _) hu' hv' hXi (fun y => (hub y).trans (le_max_left _ _))
      (fun y => (hvb y).trans (le_max_left _ _)) hXp).trans ?_).trans hCC
    calc ∫⁻ y, ENNReal.ofReal (C4 * max Cf 0 ^ 8 *
          (jetDistance0 b E (b3ClosedX b E s h τ m W i y) + (Real.sqrt W)⁻¹) ^ 4)
            ∂closedLaw b W np
        ≤ ∫⁻ _y, ENNReal.ofReal Cold ∂closedLaw b W np := by
          refine lintegral_mono_ae (hXp.mono fun y hy => ENNReal.ofReal_le_ofReal ?_)
          have hd := jetDistance0_le_bound hb0 hb hE1 hE2 hy
          have hd0 : 0 ≤ jetDistance0 b E (b3ClosedX b E s h τ m W i y) := norm_nonneg _
          have hs : (Real.sqrt W)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 hWr)
          have hs0 : 0 ≤ (Real.sqrt W)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
          rw [← he] at hd
          rw [hCold]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) 4)
            (by positivity)
      _ = ENNReal.ofReal Cold := by rw [lintegral_const, measure_univ, mul_one]
  -- a tag born at `i`: the entry at length `i` vanishes
  have hx0 : ∀ y, b3ClosedKAt b E s h τ m W i y ij.1 ij.2 = 0 := by
    intro y
    by_cases h1 : ⌊(W : ℝ) * τ ij.1⌋₊ < i
    · exact Birth.b3ClosedKAt_unborn_col (by omega) y ij.1
    · exact Birth.b3ClosedKAt_unborn_row (by omega) y ij.2
  obtain ⟨f, hfd⟩ : ∃ f : ProbedPath W np × ℝ → ℂ, ∀ y, f y =
      (b3Alive b E s h τ m R W i (Vs W)).indicator
        (fun y => b3ClosedKAt b E s h τ m W (i + 1) y ij.1 ij.2) y := ⟨_, fun _ => rfl⟩
  have hks : ∀ y, ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 =
      ENNReal.ofReal (‖f y‖ ^ 4) := by
    intro y
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), hfd]
    simp only [kStopStep, hx0, sub_zero]
  rw [lintegral_congr hks]
  -- the probes and the weight `P`
  have hw1m : Measurable fun y : ProbedPath W np × ℝ =>
      ((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1 :=
    (continuous_const_smul _).measurable.comp
      ((measurable_pi_apply ij.1).comp (measurable_snd.comp measurable_fst))
  have hw2m : Measurable fun y : ProbedPath W np × ℝ =>
      ((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2 :=
    (continuous_const_smul _).measurable.comp
      ((measurable_pi_apply ij.2).comp (measurable_snd.comp measurable_fst))
  obtain ⟨P, hPd⟩ : ∃ P : ProbedPath W np × ℝ → ℝ, ∀ y, P y =
      1 + vecNorm (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1) ^ 2 +
        vecNorm (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2) ^ 2 := ⟨_, fun _ => rfl⟩
  have hPm : Measurable P := by
    have e : P = fun y => 1 + vecNorm (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1) ^ 2 +
        vecNorm (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2) ^ 2 := funext hPd
    rw [e]
    exact (measurable_const.add ((measurable_vecNorm.comp hw1m).pow_const 2)).add
      ((measurable_vecNorm.comp hw2m).pow_const 2)
  have hP1 : ∀ y, 1 ≤ P y := fun y => by
    rw [hPd]
    have := sq_nonneg (vecNorm (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1))
    have := sq_nonneg (vecNorm (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2))
    linarith
  have hw1P : ∀ y, vecNorm (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1) ≤ P y := fun y => by
    rw [hPd]
    exact le_one_add_sq_left
  have hw2P : ∀ y, vecNorm (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2) ≤ P y := fun y => by
    rw [hPd]
    exact le_one_add_sq_right
  have hw12P : ∀ y, vecNorm (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1) *
      vecNorm (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2) ≤ P y := fun y => by
    rw [hPd]
    exact mul_le_one_add_sq _ _
  have hPint : ∫⁻ y, ENNReal.ofReal (P y ^ 4) ∂closedLaw b W np ≤
      ENNReal.ofReal (64 * (1 + 2 * (Mm ^ 4 * Cg))) := by
    have hX1 := lintegral_probe_eight_le (np := np) b hW1 ij.1 (hm0 ij.1)
    have hX2 := lintegral_probe_eight_le (np := np) b hW1 ij.2 (hm0 ij.2)
    rw [← hCgd] at hX1 hX2
    have hm1 : m ij.1 ^ 4 * Cg ≤ Mm ^ 4 * Cg :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hm0 _) (hmM _) 4) hCg
    have hm2 : m ij.2 ^ 4 * Cg ≤ Mm ^ 4 * Cg :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hm0 _) (hmM _) 4) hCg
    refine (lintegral_sum3_le (closedLaw b W np)
      (a := fun y => vecNorm (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1) ^ 8)
      (c := fun y => vecNorm (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2) ^ 8)
      (ENNReal.measurable_ofReal.comp ((measurable_vecNorm.comp hw1m).pow_const 8))
      (fun y => by positivity) (fun y => by positivity) (fun y => ?_)
      (by positivity) (by positivity) hX1 hX2).trans (ENNReal.ofReal_le_ofReal (by linarith))
    rw [hPd]
    have h := one_add_add_pow_four_le
      (sq_nonneg (vecNorm (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1)))
      (sq_nonneg (vecNorm (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2)))
    have e1 : ∀ t : ℝ, (t ^ 2) ^ 4 = t ^ 8 := fun t => by ring
    rw [e1, e1] at h
    linarith
  -- the generic split bound
  have hpas := ae_passive_b3ClosedX (np := np) hb0 hb hE1 hE2 s h hh τ m hW1 i
  have hgen : ∀ (a' c' : ProbedPath W np × ℝ → Fin W → ℂ), Measurable a' → Measurable c' →
      (∀ y, a' (b3Ext W i y) = a' y) → (∀ y, c' (b3Ext W i y) = c' y) →
      (∀ᵐ y ∂closedLaw b W np, ‖f y‖ ≤ L * P y + ‖bilinear (a' y)
        (freshDelta b E (b3ClosedX b E s h τ m W i y) (freshSample W i y.1.1)) (c' y)‖) →
      (∀ᵐ y ∂closedLaw b W np, vecNorm (a' y) * vecNorm (c' y) ≤ L * P y) →
      ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 4) ∂closedLaw b W np ≤ ENNReal.ofReal Cnew := by
    intro a' c' ha hc ha' hc' hfb hN
    have hbil := Hq W hWq np i a' c' (b3ClosedX b E s h τ m W i) ha hc
      (measurable_b3ClosedX b E s h τ m i) ha' hc' (fun y => b3ClosedX_b3Ext hi1 le_rfl y) hpas
    have hP4m : Measurable fun y => ENNReal.ofReal (P y ^ 4) :=
      ENNReal.measurable_ofReal.comp (hPm.pow_const 4)
    have h8 : (0 : ℝ) ≤ 8 := by norm_num
    have h8L : (0 : ℝ) ≤ 8 * L ^ 4 := by positivity
    have hqL : (0 : ℝ) ≤ Cq * L ^ 4 := by positivity
    calc ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 4) ∂closedLaw b W np
        ≤ ∫⁻ y, (ENNReal.ofReal (8 * L ^ 4) * ENNReal.ofReal (P y ^ 4) +
            ENNReal.ofReal 8 * ENNReal.ofReal (‖bilinear (a' y)
              (freshDelta b E (b3ClosedX b E s h τ m W i y) (freshSample W i y.1.1))
                (c' y)‖ ^ 4)) ∂closedLaw b W np := by
          refine lintegral_mono_ae (hfb.mono fun y hy => ?_)
          have hP0 : 0 ≤ P y := zero_le_one.trans (hP1 y)
          have h1 := pow_le_pow_left₀ (norm_nonneg _) hy 4
          have h2 := add_pow_four_le_real (mul_nonneg hL0 hP0) (norm_nonneg (bilinear (a' y)
            (freshDelta b E (b3ClosedX b E s h τ m W i y) (freshSample W i y.1.1)) (c' y)))
          rw [← ENNReal.ofReal_mul h8L, ← ENNReal.ofReal_mul h8,
            ← ENNReal.ofReal_add (mul_nonneg h8L (by positivity : (0 : ℝ) ≤ P y ^ 4))
              (mul_nonneg h8 (by positivity))]
          refine ENNReal.ofReal_le_ofReal ?_
          have e : (L * P y) ^ 4 = L ^ 4 * P y ^ 4 := by ring
          rw [e] at h2
          linarith
      _ = ENNReal.ofReal (8 * L ^ 4) * ∫⁻ y, ENNReal.ofReal (P y ^ 4) ∂closedLaw b W np +
          ENNReal.ofReal 8 * ∫⁻ y, ENNReal.ofReal (‖bilinear (a' y)
            (freshDelta b E (b3ClosedX b E s h τ m W i y) (freshSample W i y.1.1))
              (c' y)‖ ^ 4) ∂closedLaw b W np := by
          rw [lintegral_add_left (hP4m.const_mul _), lintegral_const_mul _ hP4m,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (8 * L ^ 4) * ∫⁻ y, ENNReal.ofReal (P y ^ 4) ∂closedLaw b W np +
          ENNReal.ofReal 8 * (ENNReal.ofReal (Cq * L ^ 4) *
            ∫⁻ y, ENNReal.ofReal (P y ^ 4) ∂closedLaw b W np) := by
          refine add_le_add le_rfl (mul_le_mul_right (hbil.trans ?_) _)
          rw [← lintegral_const_mul _ hP4m]
          refine lintegral_mono_ae (hN.mono fun y hy => ?_)
          rw [← ENNReal.ofReal_mul hqL]
          refine ENNReal.ofReal_le_ofReal ?_
          have h0 : 0 ≤ vecNorm (a' y) * vecNorm (c' y) :=
            mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)
          have h1 := pow_le_pow_left₀ h0 hy 4
          calc Cq * (vecNorm (a' y) * vecNorm (c' y)) ^ 4 ≤ Cq * (L * P y) ^ 4 :=
                mul_le_mul_of_nonneg_left h1 hCq
            _ = Cq * L ^ 4 * P y ^ 4 := by ring
      _ = ENNReal.ofReal (8 * L ^ 4 + 8 * (Cq * L ^ 4)) *
          ∫⁻ y, ENNReal.ofReal (P y ^ 4) ∂closedLaw b W np := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul h8, ← add_mul,
            ← ENNReal.ofReal_add h8L (mul_nonneg h8 hqL)]
      _ ≤ ENNReal.ofReal (8 * L ^ 4 + 8 * (Cq * L ^ 4)) *
          ENNReal.ofReal (64 * (1 + 2 * (Mm ^ 4 * Cg))) := mul_le_mul_right hPint _
      _ = ENNReal.ofReal Cnew := by
          rw [hCnew, ← ENNReal.ofReal_mul (by positivity)]
  -- the a.s. good set at the step `i → i + 1`
  have hgood : ∀ᵐ y ∂closedLaw b W np, GclSuccBlocks b E s h W i y.1.1 (phase y.2) ∧
      (passiveY (closedNearX b E s h W i y.1.1 (phase y.2))).PosSemidef ∧
      scatteringMatrix b E W i y.1.1 * (scatteringMatrix b E W i y.1.1)ᴴ = 1 ∧
      IsUnit (1 - phase y.2 • closingN (scatteringMatrix b E W i y.1.1)
        (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
        (farEmbed (closingPairing b E h W (closeLen s W) y.1.1))).det := by
    filter_upwards [ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW1,
      ae_closedPhase_good (W := W) (np := np) b E s h i] with y hP hQ
    obtain ⟨hA, hFp, hB, hS⟩ := hP
    obtain ⟨hU, hU', hY, h4⟩ := hQ
    have hR := h4.resolve_left (isUnit_closedR0 b E h s i y.1.1 hA hηZ (hFp i)).ne_zero
    have hX := passive_closedNearX b E s h hh i y.1.1 y.2 hηZ (hS i) (isUnit_iff_ne_zero.2 hU)
      (isUnit_iff_ne_zero.2 hR)
    exact ⟨gclAt_succ_blocks b E s h hci y.1.1 (phase y.2) hA hηZ (hFp i) (hFp (i + 1))
      (hB (i + 1)) (isUnit_iff_ne_zero.2 hU) (isUnit_iff_ne_zero.2 hU')
      (isUnit_iff_ne_zero.2 hY) (isUnit_iff_ne_zero.2 hR) hX, hX, hS i,
      isUnit_iff_ne_zero.2 hU⟩
  have hRm : Measurable fun y : ProbedPath W np × ℝ =>
      passiveResolvent b E (b3ClosedX b E s h τ m W i y) := by
    unfold passiveResolvent
    exact Transmission.Bridge.measurable_matrix_inv.comp
      (measurable_matrix_sub measurable_const (measurable_b3ClosedX b E s h τ m i))
  have hRn : ∀ y, (passiveY (b3ClosedX b E s h τ m W i y)).PosSemidef →
      ‖passiveResolvent b E (b3ClosedX b E s h τ m W i y)‖ ≤ e := fun y hX => by
    rw [he]
    exact norm_passiveResolvent_le hb0 hb hE1 hE2 hX
  have hRv : ∀ y, (passiveY (b3ClosedX b E s h τ m W i y)).PosSemidef → ∀ w : Fin W → ℂ,
      vecNorm (passiveResolvent b E (b3ClosedX b E s h τ m W i y) *ᵥ w) ≤ e * vecNorm w ∧
      vecNorm ((passiveResolvent b E (b3ClosedX b E s h τ m W i y))ᴴ *ᵥ w) ≤ e * vecNorm w :=
    fun y hX w => ⟨(vecNorm_mulVec_le _ _).trans
      (mul_le_mul_of_nonneg_right (hRn y hX) (vecNorm_nonneg _)),
      (vecNorm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right
        ((Matrix.l2_opNorm_conjTranspose _).le.trans (hRn y hX)) (vecNorm_nonneg _))⟩
  have hfz : ∀ y, y ∉ b3Alive b E s h τ m R W i (Vs W) → ∀ t : ℝ, 0 ≤ t → ‖f y‖ ≤ t :=
    fun y hy t ht => by
      rw [hfd, Set.indicator_of_notMem hy, norm_zero]
      exact ht
  have hLP : ∀ y, 0 ≤ L * P y := fun y => mul_nonneg hL0 (zero_le_one.trans (hP1 y))
  refine le_trans ?_ hCC'
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hun.1) with h1 | h1 <;>
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hun.2) with h2 | h2
  · exact absurd ⟨h1, h2⟩ hold
  · -- old/new
    refine hgen (fun y => clipVec (Real.sqrt R) (closedNearU b E s h τ m W i ij.1 y))
      (fun y => passiveResolvent b E (b3ClosedX b E s h τ m W i y) *ᵥ
        (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2))
      (measurable_clipVec_comp _ (measurable_closedNearU b E s h τ m i ij.1))
      (RawTag.measurable_mulVec' hRm hw2m)
      (fun y => by rw [closedNearU_b3Ext hi1 le_rfl ij.1 y])
      (fun y => by rw [b3ClosedX_b3Ext hi1 le_rfl y]; rfl) ?_ ?_
    · filter_upwards [hgood] with y hy
      obtain ⟨hblk, hX, -, -⟩ := hy
      by_cases hyA : y ∈ b3Alive b E s h τ m R W i (Vs W)
      · have htr : ((b3ClosedGramAt b E s h τ m W i (Vs W) y).1.trace).re < R :=
          hyA.2 i hi1 le_rfl
        have hub := norm_closedNearU_le b E s h τ m i (Vs W) ij.1 y htr
        rw [hfd, Set.indicator_of_mem hyA, kdiag_clipVec_of_le hub,
          closedK_birth_old_new b E s h τ m y hblk h1 h2,
          (birthK_mul_birthG s h hη y.1.1 (phase y.2) hX).1, bilinear_add_mid,
          bilinear_mul_right']
        have hA : ‖bilinear (closedNearU b E s h τ m W i ij.1 y) 1
            (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2)‖ ≤ L * P y :=
          (norm_bilinear_one_le _ _).trans (mul_le_mul (hub.trans hLr) (hw2P y)
            (vecNorm_nonneg _) hL0)
        exact (norm_add_le _ _).trans (add_le_add hA le_rfl)
      · exact hfz y hyA _ (add_nonneg (hLP y) (norm_nonneg _))
    · filter_upwards [hpas] with y hX
      have h1' := vecNorm_clipVec_le (Real.sqrt_nonneg R) (closedNearU b E s h τ m W i ij.1 y)
      have h2' := (hRv y hX (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2)).1
      calc vecNorm (clipVec (Real.sqrt R) (closedNearU b E s h τ m W i ij.1 y)) *
            vecNorm (passiveResolvent b E (b3ClosedX b E s h τ m W i y) *ᵥ
              (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2))
          ≤ Real.sqrt R * (e * vecNorm (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2)) :=
            mul_le_mul h1' h2' (vecNorm_nonneg _) (Real.sqrt_nonneg R)
        _ = (Real.sqrt R * e) * vecNorm (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2) := by
            ring
        _ ≤ L * P y := mul_le_mul hLre (hw2P y) (vecNorm_nonneg _) hL0
  · -- new/old
    refine hgen (fun y => (passiveResolvent b E (b3ClosedX b E s h τ m W i y))ᴴ *ᵥ
        (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1))
      (fun y => clipVec (Real.sqrt R) (closedNearV b E s h τ m W i ij.2 y))
      (RawTag.measurable_mulVec' (measurable_matrix_conjTranspose' hRm) hw1m)
      (measurable_clipVec_comp _ (measurable_closedNearV b E s h τ m i ij.2))
      (fun y => by rw [b3ClosedX_b3Ext hi1 le_rfl y]; rfl)
      (fun y => by rw [closedNearV_b3Ext hi1 le_rfl ij.2 y]) ?_ ?_
    · filter_upwards [hgood] with y hy
      obtain ⟨hblk, hX, hS, hU⟩ := hy
      by_cases hyA : y ∈ b3Alive b E s h τ m R W i (Vs W)
      · have htr : ((b3ClosedGramAt b E s h τ m W i (Vs W) y).1.trace).re < R :=
          hyA.2 i hi1 le_rfl
        have hvb := norm_closedNearV_le b E s h hh τ m i (Vs W) ij.2 y hS hU htr
        rw [hfd, Set.indicator_of_mem hyA, kdiag_clipVec_of_le hvb,
          closedK_birth_new_old b E s h τ m y hblk h1 h2,
          (birthK_mul_birthG s h hη y.1.1 (phase y.2) hX).2, bilinear_add_mid,
          bilinear_mul_left']
        have hA : ‖bilinear (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1) 1
            (closedNearV b E s h τ m W i ij.2 y)‖ ≤ L * P y := by
          refine (norm_bilinear_one_le _ _).trans ?_
          calc vecNorm (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1) *
                vecNorm (closedNearV b E s h τ m W i ij.2 y)
              ≤ P y * L := mul_le_mul (hw1P y) (hvb.trans hLr) (vecNorm_nonneg _)
                (zero_le_one.trans (hP1 y))
            _ = L * P y := mul_comm _ _
        exact (norm_add_le _ _).trans (add_le_add hA le_rfl)
      · exact hfz y hyA _ (add_nonneg (hLP y) (norm_nonneg _))
    · filter_upwards [hpas] with y hX
      have h1' := (hRv y hX (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1)).2
      have h2' := vecNorm_clipVec_le (Real.sqrt_nonneg R) (closedNearV b E s h τ m W i ij.2 y)
      calc vecNorm ((passiveResolvent b E (b3ClosedX b E s h τ m W i y))ᴴ *ᵥ
              (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1)) *
            vecNorm (clipVec (Real.sqrt R) (closedNearV b E s h τ m W i ij.2 y))
          ≤ (e * vecNorm (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1)) * Real.sqrt R :=
            mul_le_mul h1' h2' (vecNorm_nonneg _) (mul_nonneg he0 (vecNorm_nonneg _))
        _ = (Real.sqrt R * e) * vecNorm (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1) := by
            ring
        _ ≤ L * P y := mul_le_mul hLre (hw1P y) (vecNorm_nonneg _) hL0
  · -- new/new
    refine hgen (fun y => (passiveResolvent b E (b3ClosedX b E s h τ m W i y))ᴴ *ᵥ
        (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1))
      (fun y => passiveResolvent b E (b3ClosedX b E s h τ m W i y) *ᵥ
        (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2))
      (RawTag.measurable_mulVec' (measurable_matrix_conjTranspose' hRm) hw1m)
      (RawTag.measurable_mulVec' hRm hw2m)
      (fun y => by rw [b3ClosedX_b3Ext hi1 le_rfl y]; rfl)
      (fun y => by rw [b3ClosedX_b3Ext hi1 le_rfl y]; rfl) ?_ ?_
    · filter_upwards [hgood] with y hy
      obtain ⟨hblk, hX, -, -⟩ := hy
      by_cases hyA : y ∈ b3Alive b E s h τ m R W i (Vs W)
      · rw [hfd, Set.indicator_of_mem hyA, closedK_birth_new_new' b E s h τ m y hblk h1 h2,
          birthG_eq s h hη y.1.1 (phase y.2) hX, bilinear_add_mid, bilinear_mul_mul']
        have hA : ‖bilinear (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1)
            (passiveResolvent b E (closedNearX b E s h W i y.1.1 (phase y.2)))
            (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2)‖ ≤ L * P y := by
          refine (norm_bilinear_le _ _ _).trans ?_
          have hn := hRn y hX
          have h0 := vecNorm_nonneg (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1)
          have h0' := vecNorm_nonneg (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2)
          calc vecNorm (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1) *
                ‖passiveResolvent b E (closedNearX b E s h W i y.1.1 (phase y.2))‖ *
                vecNorm (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2)
              ≤ vecNorm (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1) * e *
                vecNorm (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn h0) h0'
            _ = e * (vecNorm (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1) *
                vecNorm (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2)) := by ring
            _ ≤ L * P y := mul_le_mul hLe (hw12P y) (mul_nonneg h0 h0') hL0
        exact (norm_add_le _ _).trans (add_le_add hA le_rfl)
      · exact hfz y hyA _ (add_nonneg (hLP y) (norm_nonneg _))
    · filter_upwards [hpas] with y hX
      have h1' := (hRv y hX (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1)).2
      have h2' := (hRv y hX (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2)).1
      have h0 := vecNorm_nonneg (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1)
      have h0' := vecNorm_nonneg (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2)
      calc vecNorm ((passiveResolvent b E (b3ClosedX b E s h τ m W i y))ᴴ *ᵥ
              (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1)) *
            vecNorm (passiveResolvent b E (b3ClosedX b E s h τ m W i y) *ᵥ
              (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2))
          ≤ (e * vecNorm (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1)) *
              (e * vecNorm (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2)) :=
            mul_le_mul h1' h2' (vecNorm_nonneg _) (mul_nonneg he0 h0)
        _ = (e * e) * (vecNorm (((Real.sqrt (m ij.1 / W) : ℝ) : ℂ) • y.1.2 ij.1) *
              vecNorm (((Real.sqrt (m ij.2 / W) : ℝ) : ℂ) • y.1.2 ij.2)) := by ring
        _ ≤ L * P y := mul_le_mul hLee (hw12P y) (mul_nonneg h0 h0') hL0

/-!
## `KStopBirthSum`
-/

/-- **`KStopBirthSum` holds** (input hypotheses `GaussianAbsorptionContract`, `GaussianLpGradient`;
no jet, no per-length P4): at most `np` birth steps, each with a bounded stopped fourth moment.
-/
theorem kStopBirthSum_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    KStopBirthSum := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C, hC0, hC⟩ := lintegral_kStopStep_four_bounded hGA hLp b E np τ m T s h K Vs hF R
  refine ⟨(np : ℝ) ^ 3 * ((np : ℝ) * C), ?_⟩
  have hb1 : b < 1 := by linarith [hF.1.2.1]
  have hE1 := hF.1.2.2.1
  have hE2 := hF.1.2.2.2.1
  filter_upwards [hC, hF.2.2.2.2.2] with W hW hVW ij
  have hmV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  set F := (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter (fun i => IsBirthStep τ W i)
  have hcard : F.card ≤ np := Birth.card_steps_le τ W _
  have hstep : ∀ i ∈ F, ∫⁻ y, ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4
      ∂closedLaw b W np ≤ ENNReal.ofReal C := fun i hiF =>
    hW i (Finset.mem_filter.1 hiF).1 ij
  have hae : ∀ i ∈ F, AEMeasurable (fun y => ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4)
      (closedLaw b W np) := fun i _ =>
    (aemeasurable_kStopStep hb1 hE1 hE2 s h τ m R W i hmV ij).enorm.pow_const 4
  calc ∫⁻ y, (∑ i ∈ F, ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ) ^ 4 ∂closedLaw b W np
      ≤ ∫⁻ y, (F.card : ℝ≥0∞) ^ 3 *
          ∑ i ∈ F, ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ∂closedLaw b W np :=
        lintegral_mono fun y => birthK_sum_pow_four_le F _
    _ = (F.card : ℝ≥0∞) ^ 3 *
          ∑ i ∈ F, ∫⁻ y, ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ∂closedLaw b W np := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum' _ hae]
    _ ≤ (np : ℝ≥0∞) ^ 3 * (F.card • ENNReal.ofReal C) := by
        gcongr
        exact Finset.sum_le_card_nsmul _ _ _ hstep
    _ ≤ (np : ℝ≥0∞) ^ 3 * ((np : ℝ≥0∞) * ENNReal.ofReal C) := by
        rw [nsmul_eq_mul]
        gcongr
    _ = ENNReal.ofReal ((np : ℝ) ^ 3 * ((np : ℝ) * C)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]

end BlockBand.SourceProcess.PhysApprox.B3.KDiag

