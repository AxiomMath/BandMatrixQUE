module

public import BlockBand.SourceProcess.PhysApprox.B3GramStep
public import BlockBand.SourceProcess.PhysApprox.B3GramStepU
public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormDefs
public import BlockBand.SourceProcess.PhysApprox.B3MeanFresh
public import BlockBand.SourceProcess.PhysApprox.B3MeanClosed
public import BlockBand.SourceProcess.PhysApprox.B3StepK

/-!
# `ClosedGramStepFourAt` from the closed Gram update

The closed objects are the closed input `b3ClosedX` (`X_cl = z − R_cl⁻¹`) and the closing factor
`physClosingZAt`. Their frames `closedNearU`, `closedNearV` are for probe columns; here the same
frames for every column of the open frame `b3OpenFrameAt` (current and probe columns):
`gramNearU d = ι*C_j(z)*X_je_d` (the near rows of `b3ClosedFrameAt`) and
`gramNearV d = ι*𝕊_j(1 + Z_j(z))X_je_d` (the near rows of the closed outgoing frame `L_cl`).

* `gramForm`: the closed exact update of a Gram coordinate,
  `ΔM_kl = c u_k*Δv_l + (c u_l*Δv_k)^*`, `c = −(2iη)⁻¹`, and `ΔB_kl = u_k*(U − 1)u_l`, with
  `Δ = Δ(X_cl, F_j)`, `U = U(X_cl, F_j)`.
* **`eLpNorm_gramForm_le`** (from the contract hypotheses):
  `‖gramForm‖_{L⁴(F)} ≤ C(δ₀(X) + W^{-1/2})` for passive `X`, frames of norm `≤ C_f` and leak
  `Tr(1 − SS*) ≤ C_T`.
* **`lintegral_closed_fresh_le`** (the generic stopped fresh-layer step): under `closedLaw`,
  `E Φ(y, F_j) ≤ E B` when `∫Φ(y, F) dfreshLaw ≤ B(y)` and `Φ`, `B` are functions of the past at
  `j` (Tonelli via `closedLaw_map_past_fresh`).
* Stated here as hypotheses:
  * `ClosedGramUpdate`: `X_cl` a.e. passive, and every old Gram step is `gramForm` a.e.;
  * `ClosedNearVBound`: on the alive set, `‖gramNearV d‖ ≤ C_v`;
  * `ClosedLeakBound`: on the alive set, the closed one-port leak `Tr(1 − SS*)(X_cl) ≤ C_T` (on
    the cap event it is at most the number of retained modes);
  * `ClosedJetStopHalf`: the stopped closed jet `E[1_{A_j}δ₀(X_cl,j)⁴] ≤ C/W²` at every step
    `n_s ≤ j < ⌊WT⌋`. It follows from `ClosedJetL4` at every step (`closedJetStopHalf_of_L4`).
* **`closedGramStepFourAt_of_closed`**: the four inputs and the contract hypotheses give
  `ClosedGramStepFourAt`; hence `GramStopStepFour`, `ComplexGramLindeberg` and the Gram rows of
  `ComplexBirthOldL2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.ClosedLimit
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W np K : ℕ}

/-!
## The closed near frames of every column
-/

/-- Column `d` of the open frame `X_j`. -/
def gramCol (b E s : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (d : SrcCol K (Fin np))
    (x : ProbedPath W np) : Fin 2 × Fin W → ℂ :=
  fun a => b3OpenFrameAt b E s τ m W j Vs x a d

/-- The left closed near frame `u_d = ι*C_j(z)*X_je_d` (near rows of `b3ClosedFrameAt`). -/
def gramNearU (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (d : SrcCol K (Fin np))
    (y : ProbedPath W np × ℝ) : Fin W → ℂ :=
  nearSel W *ᵥ ((physClosingMapAt b E s h W j y.1.1 (phase y.2))ᴴ *ᵥ
    gramCol b E s τ m W j Vs d y.1)

/-- The right closed near frame `v_d = ι*𝕊_j(1 + Z_j(z))X_je_d` (near rows of `L_cl`). -/
def gramNearV (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (d : SrcCol K (Fin np))
    (y : ProbedPath W np × ℝ) : Fin W → ℂ :=
  nearSel W *ᵥ (scatteringMatrix b E W j y.1.1 *ᵥ
    ((1 + physClosingZAt b E s h W j y.1.1 (phase y.2)) *ᵥ gramCol b E s τ m W j Vs d y.1))

theorem nearSel_mulVec_apply (w : Fin 2 × Fin W → ℂ) (x : Fin W) :
    (nearSel W *ᵥ w) x = w (0, x) := by
  simp [nearSel, mulVec, dotProduct]

theorem gramNearU_apply (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (d : SrcCol K (Fin np))
    (y : ProbedPath W np × ℝ) (x : Fin W) :
    gramNearU b E s h τ m W j Vs d y x = b3ClosedFrameAt b E s h τ m W j Vs y (0, x) d := by
  rw [gramNearU, nearSel_mulVec_apply, b3ClosedFrameAt, Matrix.mul_apply]
  rfl

theorem measurable_gramCol (b E s : ℝ) (τ m : Fin np → ℝ) (j : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    (d : SrcCol K (Fin np)) : Measurable (gramCol b E s τ m W j Vs d) :=
  Measurable.of_eval fun _ => (measurable_b3OpenFrameAt b E s τ m W j hV).eval_matrix

theorem measurable_gramNearU (b E s h : ℝ) (τ m : Fin np → ℝ) (j : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    (d : SrcCol K (Fin np)) : Measurable (gramNearU b E s h τ m W j Vs d) :=
  RawTag.measurable_mulVec' measurable_const (RawTag.measurable_mulVec'
    (measurable_matrix_conjTranspose' (measurable_physClosingMapAt_comp b E s h j
      (measurable_fst.comp measurable_fst) (measurable_phase.comp measurable_snd)))
    ((measurable_gramCol b E s τ m j hV d).comp measurable_fst))

theorem measurable_gramNearV (b E s h : ℝ) (τ m : Fin np → ℝ) (j : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    (d : SrcCol K (Fin np)) : Measurable (gramNearV b E s h τ m W j Vs d) :=
  RawTag.measurable_mulVec' measurable_const (RawTag.measurable_mulVec'
    ((measurable_scatteringMatrix b E j).comp (measurable_fst.comp measurable_fst))
    (RawTag.measurable_mulVec' (measurable_matrix_add measurable_const
      (measurable_physClosingZAt_comp b E s h j (measurable_fst.comp measurable_fst)
        (measurable_phase.comp measurable_snd)))
      ((measurable_gramCol b E s τ m j hV d).comp measurable_fst)))

section Invariance

variable {b E s h : ℝ} {τ m : Fin np → ℝ} {j : ℕ}

theorem gramCol_b3Ext (hs : closeLen s W ≤ j)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : Measurable[growthSigma W (closeLen s W)] Vs) (d : SrcCol K (Fin np))
    (y : ProbedPath W np × ℝ) :
    gramCol b E s τ m W j Vs d (b3Ext W j y).1 = gramCol b E s τ m W j Vs d y.1 := by
  funext a
  simp only [gramCol, b3OpenFrameAt, probeFrame, b3Ext,
    Modul.boundaryToInterior_extPast b E (le_refl j), Modul.eq_of_growth hs hV,
    ClosedSumProof.stepProd_extPast b E (closeLen s W) _ (j - closeLen s W)
      (by omega : closeLen s W + (j - closeLen s W) ≤ j)]

theorem gramNearU_b3Ext (hs : closeLen s W ≤ j)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : Measurable[growthSigma W (closeLen s W)] Vs) (d : SrcCol K (Fin np))
    (y : ProbedPath W np × ℝ) :
    gramNearU b E s h τ m W j Vs d (b3Ext W j y) = gramNearU b E s h τ m W j Vs d y := by
  have e := gramCol_b3Ext (b := b) (E := E) (τ := τ) (m := m) hs hV d y
  simp only [gramNearU, e]
  simp only [b3Ext, Modul.physClosingMapAt_extPast s h hs (le_refl j)]

theorem gramNearV_b3Ext (hs : closeLen s W ≤ j)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : Measurable[growthSigma W (closeLen s W)] Vs) (d : SrcCol K (Fin np))
    (y : ProbedPath W np × ℝ) :
    gramNearV b E s h τ m W j Vs d (b3Ext W j y) = gramNearV b E s h τ m W j Vs d y := by
  have e := gramCol_b3Ext (b := b) (E := E) (τ := τ) (m := m) hs hV d y
  have eZ := physClosingZAt_b3Ext (b := b) (E := E) (s := s) (h := h) hs (le_refl j)
    (phase y.2) y
  simp only [gramNearV, e]
  simp only [b3Ext] at eZ ⊢
  rw [eZ, ClosedSumProof.scatteringMatrix_extPast (le_refl j)]

end Invariance

/-!
## The corrected closed update of a Gram coordinate
-/

/-- `c = −(2iη)⁻¹`. -/
def gramC (b E : ℝ) : ℂ := -(2 * Complex.I * (etaZ b E : ℂ))⁻¹

/-- **The closed exact update** of the Gram coordinate `e = (σ, k, l)` (on the closed path,
with the near rows `v` of `L_cl`): for `σ = 0` (`M`) `c u_k*Δv_l + (c u_l*Δv_k)^*`, for `σ = 1`
(`B`) `u_k*(U − 1)u_l`, at the input `X` and the fresh layer `F`. -/
def gramForm (b E : ℝ) {c : Type*} (e : Fin 2 × c × c) (u v : c → Fin W → ℂ)
    (X : Matrix (Fin W) (Fin W) ℂ) (F : LayerSample W .oneBlockOnePort) : ℂ :=
  if e.1 = 0 then
    gramC b E * bilinear (u e.2.1) (freshDelta b E X F) (v e.2.2) +
      star (gramC b E * bilinear (u e.2.2) (freshDelta b E X F) (v e.2.1))
  else bilinear (u e.2.1) (freshU b E X F - 1) (u e.2.2)

theorem measurable_gramForm (b E : ℝ) {c : Type*} (e : Fin 2 × c × c) {α : Type*}
    [MeasurableSpace α] {u v : α → c → Fin W → ℂ} {X : α → Matrix (Fin W) (Fin W) ℂ}
    {F : α → LayerSample W .oneBlockOnePort} (hu : ∀ d, Measurable fun a => u a d)
    (hv : ∀ d, Measurable fun a => v a d) (hX : Measurable X) (hF : Measurable F) :
    Measurable fun a => gramForm b E e (u a) (v a) (X a) (F a) := by
  have hΔ := FullSource.measurable_freshDelta_comp b E hX hF
  by_cases he : e.1 = 0
  · simp only [gramForm, he, ↓reduceIte]
    exact ((RawTag.measurable_bilinear_jt (hu _) hΔ (hv _)).const_mul _).add
      (continuous_star.measurable.comp
        ((RawTag.measurable_bilinear_jt (hu _) hΔ (hv _)).const_mul _))
  · simp only [gramForm, he, ↓reduceIte]
    have hL := FullSource.measurable_freshL_comp b E hX hF
    exact RawTag.measurable_bilinear_jt (hu _) (measurable_matrix_sub
      (measurable_matrix_mul' hL (measurable_matrix_conjTranspose' hL)) measurable_const) (hu _)

theorem norm_gramC (b E : ℝ) (hη : 0 < etaZ b E) : ‖gramC b E‖ = (2 * etaZ b E)⁻¹ := by
  rw [gramC, norm_neg, norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hη]
  norm_num

/-- **`‖gramForm‖_{L⁴(F)} ≤ C(C_f² + C_f²C_T⁺)(δ₀(X) + W^{-1/2})`** for passive `X`, frames of
norm `≤ C_f` and leak `≤ C_T` (from the contract hypotheses: `eLpNorm_bilinear_freshDelta_le`,
`eLpNorm_bilinear_freshUSub_le`). -/
theorem eLpNorm_gramForm_le (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ {c : Type} (e : Fin 2 × c × c)
      (u v : c → Fin W → ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (Cf CT : ℝ),
      (passiveY X).PosSemidef → 0 ≤ Cf → (∀ d, vecNorm (u d) ≤ Cf) →
      (∀ d, vecNorm (v d) ≤ Cf) → GramStepU.oneLeak b E X ≤ CT →
        eLpNorm (fun F => gramForm b E e u v X F) 4 (freshLaw W b) ≤
          ENNReal.ofReal (C * (Cf ^ 2 + Cf ^ 2 * max CT 0) *
            (jetDistance0 b E X + (Real.sqrt W)⁻¹)) := by
  have hη : 0 < etaZ b E := etaZ_pos b E (by linarith) hE1 hE2
  obtain ⟨C4, W4, hC4, h4⟩ :=
    GramStepU.eLpNorm_bilinear_freshDelta_le hGA hLp hb0 hb hE1 hE2 (p := 4) (by norm_num)
  obtain ⟨CU, WU, hCU, hU⟩ := GramStepU.eLpNorm_bilinear_freshUSub_le hGA hLp hb0 hb hE1 hE2
  refine ⟨4 * (2 * etaZ b E)⁻¹ * C4 + 2 * CU, max W4 WU, by positivity,
    fun W hW c e u v X Cf CT hX hCf hu hv hT => ?_⟩
  have hW4 : W4 ≤ W := le_trans (le_max_left _ _) hW
  have hWU : WU ≤ W := le_trans (le_max_right _ _) hW
  set D := jetDistance0 b E X + (Real.sqrt W)⁻¹ with hD
  have hD0 : 0 ≤ D := add_nonneg (norm_nonneg _) (inv_nonneg.2 (Real.sqrt_nonneg _))
  have hT0 : 0 ≤ max CT 0 := le_max_right _ _
  have hΔm : Measurable (freshDelta b E X) :=
    FullSource.measurable_freshDelta_comp b E measurable_const measurable_id
  have hbil : ∀ a c' : Fin W → ℂ, Measurable fun F => bilinear a (freshDelta b E X F) c' :=
    fun a c' => RawTag.measurable_bilinear_jt measurable_const hΔm measurable_const
  have h4' : ∀ a c' : Fin W → ℂ, vecNorm a ≤ Cf → vecNorm c' ≤ Cf →
      eLpNorm (fun F => bilinear a (freshDelta b E X F) c') 4 (freshLaw W b) ≤
        ENNReal.ofReal (C4 * D * Cf * Cf) := fun a c' ha hc => by
    have := h4 W hW4 X hX a c'
    rw [ENNReal.ofReal_ofNat] at this
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    have := vecNorm_nonneg a
    have := vecNorm_nonneg c'
    gcongr
  by_cases he : e.1 = 0
  · simp only [gramForm, he, ↓reduceIte]
    have e1 : (fun F => gramC b E * bilinear (u e.2.1) (freshDelta b E X F) (v e.2.2) +
        star (gramC b E * bilinear (u e.2.2) (freshDelta b E X F) (v e.2.1))) =
        (gramC b E • fun F => bilinear (u e.2.1) (freshDelta b E X F) (v e.2.2)) +
          star (gramC b E • fun F => bilinear (u e.2.2) (freshDelta b E X F) (v e.2.1)) := by
      funext F; simp only [Pi.add_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul]
    rw [e1]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    rw [eLpNorm_star, eLpNorm_const_smul, eLpNorm_const_smul, ← ofReal_norm, norm_gramC b E hη]
    calc ENNReal.ofReal (2 * etaZ b E)⁻¹ *
          eLpNorm (fun F => bilinear (u e.2.1) (freshDelta b E X F) (v e.2.2)) 4 (freshLaw W b) +
        ENNReal.ofReal (2 * etaZ b E)⁻¹ *
          eLpNorm (fun F => bilinear (u e.2.2) (freshDelta b E X F) (v e.2.1)) 4 (freshLaw W b)
        ≤ ENNReal.ofReal (2 * etaZ b E)⁻¹ * ENNReal.ofReal (C4 * D * Cf * Cf) +
            ENNReal.ofReal (2 * etaZ b E)⁻¹ * ENNReal.ofReal (C4 * D * Cf * Cf) := by
          gcongr
          · exact h4' _ _ (hu _) (hv _)
          · exact h4' _ _ (hu _) (hv _)
      _ = ENNReal.ofReal (2 * ((2 * etaZ b E)⁻¹ * (C4 * D * Cf * Cf))) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          ring_nf
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : 0 ≤ Cf ^ 2 * max CT 0 * D := by positivity
          have h2 : 0 ≤ (2 * etaZ b E)⁻¹ * C4 := by positivity
          nlinarith [mul_nonneg (mul_nonneg h2 (sq_nonneg Cf)) hD0,
            mul_nonneg (mul_nonneg h2 (by norm_num : (0 : ℝ) ≤ 2)) h1,
            mul_nonneg hCU (mul_nonneg (sq_nonneg Cf) hD0), mul_nonneg hCU h1]
  · simp only [gramForm, he, ↓reduceIte]
    refine (hU W hWU X hX (u e.2.1) (u e.2.2)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hu1 := hu e.2.1
    have hu2 := hu e.2.2
    have hn1 := vecNorm_nonneg (u e.2.1)
    have hn2 := vecNorm_nonneg (u e.2.2)
    have hL : GramStepU.oneLeak b E X ≤ max CT 0 := hT.trans (le_max_left _ _)
    have hL0 : 0 ≤ GramStepU.oneLeak b E X := by
      rw [GramStepU.oneLeak_eq hη hX]
      have := (Matrix.PosSemidef.mul_mul_conjTranspose_same hX
        (passiveResolvent b E X)).trace_nonneg
      have h' := (Complex.nonneg_iff.1 this).1
      positivity
    have hp : vecNorm (u e.2.1) * vecNorm (u e.2.2) ≤ Cf ^ 2 := by
      rw [sq]; exact mul_le_mul hu1 hu2 hn2 hCf
    have hq : (vecNorm (u e.2.1) ^ 2 + vecNorm (u e.2.2) ^ 2) * GramStepU.oneLeak b E X ≤
        (2 * Cf ^ 2) * max CT 0 := by
      have : vecNorm (u e.2.1) ^ 2 + vecNorm (u e.2.2) ^ 2 ≤ 2 * Cf ^ 2 := by
        nlinarith [pow_le_pow_left₀ hn1 hu1 2, pow_le_pow_left₀ hn2 hu2 2]
      exact mul_le_mul this hL hL0 (by positivity)
    have hin : vecNorm (u e.2.1) * vecNorm (u e.2.2) +
        (vecNorm (u e.2.1) ^ 2 + vecNorm (u e.2.2) ^ 2) * GramStepU.oneLeak b E X ≤
        2 * (Cf ^ 2 + Cf ^ 2 * max CT 0) := by nlinarith [sq_nonneg Cf]
    have hin0 : 0 ≤ vecNorm (u e.2.1) * vecNorm (u e.2.2) +
        (vecNorm (u e.2.1) ^ 2 + vecNorm (u e.2.2) ^ 2) * GramStepU.oneLeak b E X := by
      positivity
    calc CU * D * (vecNorm (u e.2.1) * vecNorm (u e.2.2) +
          (vecNorm (u e.2.1) ^ 2 + vecNorm (u e.2.2) ^ 2) * GramStepU.oneLeak b E X)
        ≤ CU * D * (2 * (Cf ^ 2 + Cf ^ 2 * max CT 0)) :=
          mul_le_mul_of_nonneg_left hin (mul_nonneg hCU hD0)
      _ ≤ _ := by
          have h1 : 0 ≤ (Cf ^ 2 + Cf ^ 2 * max CT 0) * D := by positivity
          have h2 : 0 ≤ 4 * (2 * etaZ b E)⁻¹ * C4 := by positivity
          nlinarith [mul_nonneg h2 h1]

/-!
## The generic stopped fresh-layer step under the closed law
-/

/-- **One fresh step under `closedLaw`** (Tonelli through
`closedLaw_map_past_fresh`): if `Φ(y, ·)` and `B` are unchanged by `b3Ext W j` (functions of the
past at `j`, the probes and the phase) and `∫Φ(y, F) dfreshLaw(F) ≤ B(y)` for every `y`, then
`E Φ(y, F_j) ≤ E B`. -/
theorem lintegral_closed_fresh_le (b : ℝ) (j : ℕ)
    {Φ : ProbedPath W np × ℝ → LayerSample W .oneBlockOnePort → ℝ≥0∞}
    (hΦ : Measurable fun z : (ProbedPath W np × ℝ) × LayerSample W .oneBlockOnePort =>
      Φ z.1 z.2)
    (hΦ' : ∀ y, Φ (b3Ext W j y) = Φ y) {B : ProbedPath W np × ℝ → ℝ≥0∞} (hBm : Measurable B)
    (hB' : ∀ y, B (b3Ext W j y) = B y) (hB : ∀ y, ∫⁻ F, Φ y F ∂freshLaw W b ≤ B y) :
    ∫⁻ y, Φ y (freshSample W j y.1.1) ∂closedLaw b W np ≤ ∫⁻ y, B y ∂closedLaw b W np := by
  set μ := closedLaw b W np
  have hπ := measurable_b3Past (np := np) W j
  have hr := measurable_b3Rebuild (np := np) W j
  have hT : Measurable fun y : ProbedPath W np × ℝ => (b3Past W j y, freshSample W j y.1.1) :=
    hπ.prodMk ((measurable_freshSample W j).comp (measurable_fst.comp measurable_fst))
  set G : (Transmission.PathScalar.PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
      LayerSample W .oneBlockOnePort → ℝ≥0∞ := fun z => Φ (b3Rebuild W j z.1) z.2
  have hG : Measurable G := hΦ.comp ((hr.comp measurable_fst).prodMk measurable_snd)
  have e1 : ∀ y, Φ y (freshSample W j y.1.1) = G (b3Past W j y, freshSample W j y.1.1) :=
    fun y => by simp only [G, b3Rebuild_b3Past, hΦ']
  calc ∫⁻ y, Φ y (freshSample W j y.1.1) ∂μ
      = ∫⁻ z, G z ∂(((pastLaw W j b).prod (probePhaseLaw W np)).prod (freshLaw W b)) := by
        rw [lintegral_congr e1, ← closedLaw_map_past_fresh b W np j, lintegral_map hG hT]
    _ = ∫⁻ p, ∫⁻ F, G (p, F) ∂freshLaw W b ∂((pastLaw W j b).prod (probePhaseLaw W np)) :=
        lintegral_prod _ hG.aemeasurable
    _ ≤ ∫⁻ p, B (b3Rebuild W j p) ∂((pastLaw W j b).prod (probePhaseLaw W np)) :=
        lintegral_mono fun p => hB (b3Rebuild W j p)
    _ = ∫⁻ y, B (b3Rebuild W j (b3Past W j y)) ∂μ := by
        rw [← closedLaw_map_b3Past b W np j,
          lintegral_map (show Measurable fun p => B (b3Rebuild W j p) from hBm.comp hr) hπ]
    _ = ∫⁻ y, B y ∂μ := by simp only [b3Rebuild_b3Past, hB']

/-!
## Measurability and frame bounds on the alive set
-/

theorem measurable_vecNorm_comp {α : Type*} [MeasurableSpace α] {f : α → Fin W → ℂ}
    (hf : Measurable f) : Measurable fun a => vecNorm (f a) := by
  unfold vecNorm
  exact Real.continuous_sqrt.measurable.comp
    (Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hf).norm.pow_const 2)

theorem measurable_oneLeak_comp (b E : ℝ) {α : Type*} [MeasurableSpace α]
    {X : α → Matrix (Fin W) (Fin W) ℂ} (hX : Measurable X) :
    Measurable fun a => GramStepU.oneLeak b E (X a) := by
  have hR : Measurable fun a => passiveResolvent b E (X a) := by
    simp only [passiveResolvent]
    exact Transmission.Bridge.measurable_matrix_inv.comp
      (measurable_matrix_sub measurable_const hX)
  have hS : Measurable fun a => GramStepU.oneS b E (X a) :=
    measurable_matrix_sub measurable_const (measurable_matrix_cmul measurable_const hR)
  have hM : Measurable fun a => 1 - GramStepU.oneS b E (X a) * (GramStepU.oneS b E (X a))ᴴ :=
    measurable_matrix_sub measurable_const
      (measurable_matrix_mul' hS (measurable_matrix_conjTranspose' hS))
  simp only [GramStepU.oneLeak, Matrix.trace, Matrix.diag, Complex.re_sum]
  exact Finset.measurable_sum _ fun i _ => Complex.measurable_re.comp hM.eval_matrix

/-- **The left frame is bounded on the alive set**: `‖u_d‖² ≤ Re Tr M_j < R`. -/
theorem vecNorm_gramNearU_le {b E s h : ℝ} {τ m : Fin np → ℝ} {R : ℝ} {j : ℕ}
    (hs : closeLen s W ≤ j) {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    {y : ProbedPath W np × ℝ} (hy : y ∈ b3AliveM b E s h τ m R W j Vs)
    (d : SrcCol K (Fin np)) :
    vecNorm (gramNearU b E s h τ m W j Vs d y) ≤ Real.sqrt (max R 0) := by
  set F := b3ClosedFrameAt b E s h τ m W j Vs y
  have htr : Four.frameSq F < R := by
    have := hy.2 j hs le_rfl
    simp only [b3ClosedGramAt, Stochastic.gramPair, BlockBand.SourceProcess.sourceGram,
      Four.reTrace_conjTranspose_mul] at this
    exact this
  have hcol : ∑ x, ‖gramNearU b E s h τ m W j Vs d y x‖ ^ 2 ≤ Four.frameSq F := by
    simp only [gramNearU_apply]
    calc ∑ x, ‖F (0, x) d‖ ^ 2 ≤ ∑ x, ∑ d', ‖F (0, x) d'‖ ^ 2 :=
          Finset.sum_le_sum fun x _ => Finset.single_le_sum (f := fun d' => ‖F (0, x) d'‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ d)
      _ ≤ Four.frameSq F := by
          rw [Four.frameSq, Fintype.sum_prod_type, Fin.sum_univ_two]
          have : 0 ≤ ∑ x, ∑ d', ‖F (1, x) d'‖ ^ 2 :=
            Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
          linarith
  rw [vecNorm]
  exact Real.sqrt_le_sqrt (hcol.trans (htr.le.trans (le_max_left _ _)))

/-!
## The inputs
-/

/-- **`ClosedGramUpdate`: the closed exact update of the Gram coordinates** (on the far-closed
path, with `v` the near rows of `L_cl`): on the domain, eventually, at every step
`n_s ≤ j < ⌊WT⌋`, the closed input `X_cl` is a.e. passive and every Gram step with no newborn
column is a.e. `gramForm` at `(gramNearU, gramNearV, X_cl, F_j)`. It is `ClosedStepForm` for the
Gram coordinates (current and probe columns). -/
def ClosedGramUpdate : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ᶠ W in atTop,
      ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
        (∀ᵐ y ∂closedLaw b W np, (passiveY (b3ClosedX b E s h τ m W j y)).PosSemidef) ∧
        ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
          ¬ IsNewCoord τ W j (Sum.inl e : CIdx K np) →
          b3dX b E s h τ m W j (Vs W) (Sum.inl e : CIdx K np) =ᵐ[closedLaw b W np] fun y =>
            gramForm b E e (fun d => gramNearU b E s h τ m W j (Vs W) d y)
              (fun d => gramNearV b E s h τ m W j (Vs W) d y) (b3ClosedX b E s h τ m W j y)
              (freshSample W j y.1.1)

/-- **`ClosedNearVBound`**: on the alive set the right closed near frames are bounded,
`‖gramNearV d‖ ≤ C_v` (through unitarity of `𝕊`, `ΠΠ* = A` and `closingMap_mul_conj`). -/
def ClosedNearVBound : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ Cv : ℝ, ∀ᶠ W in atTop,
      ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
        ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j (Vs W) →
          ∀ d, vecNorm (gramNearV b E s h τ m W j (Vs W) d y) ≤ Cv

/-- **`ClosedLeakBound`**: on the alive set the closed one-port leak `Tr(1 − SS*)(X_cl)` (the
transmission of the near end of the far-closed path) is bounded (on the cap event by the number
`≤ K` of retained far channels). -/
def ClosedLeakBound : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ CT : ℝ, ∀ᶠ W in atTop,
      ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
        ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j (Vs W) →
          GramStepU.oneLeak b E (b3ClosedX b E s h τ m W j y) ≤ CT

/-- **`ClosedJetStopHalf`: the stopped closed jet at the `W^{-1/2}` scale**,
`E[1_{A_j}δ₀(X_cl,j)⁴] ≤ C/W²` at every step `n_s ≤ j < ⌊WT⌋` (current columns are present from
`n_s`, so no step is exempt). -/
def ClosedJetStopHalf : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ Cδ : ℝ, ∀ᶠ W in atTop,
      ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
        ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
            ENNReal.ofReal (jetDistance0 b E (b3ClosedX b E s h τ m W j y) ^ 4)) y
          ∂closedLaw b W np ≤ ENNReal.ofReal (Cδ / (W : ℝ) ^ 2)

/-- **The stopped jet from the unstopped `ClosedJetL4` at every step.** -/
theorem closedJetStopHalf_of_L4
    (hJ : ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∃ Cj : ℝ, ∀ᶠ W in atTop,
        ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          ClosedJetL4 b E W np Cj (b3ClosedX b E s h τ m W j)) :
    ClosedJetStopHalf := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨Cj, hCj⟩ := hJ b E np τ m T s h K Vs hD
  refine ⟨max Cj 0, ?_⟩
  filter_upwards [hCj, eventually_ge_atTop 1] with W hW hW1 j hj
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  refine (lintegral_mono fun y => Set.indicator_le_self _ _ y).trans ?_
  have e : ∀ y, ENNReal.ofReal (jetDistance0 b E (b3ClosedX b E s h τ m W j y) ^ 4) =
      ENNReal.ofReal (jetDistance0 b E (b3ClosedX b E s h τ m W j y)) ^ 4 :=
    fun y => ENNReal.ofReal_pow (norm_nonneg _) 4
  rw [lintegral_congr e]
  refine (hW j hj).trans (ENNReal.ofReal_le_ofReal ?_)
  have h2 : (W : ℝ) ^ 2 ≤ (W : ℝ) ^ 4 := pow_le_pow_right₀ hW1r (by norm_num)
  calc Cj / (W : ℝ) ^ 4 ≤ max Cj 0 / (W : ℝ) ^ 4 :=
        div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max Cj 0 / (W : ℝ) ^ 2 :=
        div_le_div_of_nonneg_left (le_max_right _ _) (by positivity) h2

/-!
## `ClosedGramStepFourAt`
-/

set_option maxHeartbeats 800000 in

/-- **The per-step closed Gram bound up to the stopped jet**: from the
closed update and the frame/leak bounds on the alive set, eventually in `W`, at every step and for
every old Gram coordinate,
`E[1_{A_j}|dX_e|⁴] ≤ C·E[1_{A_j}δ₀(X_cl,j)⁴] + C/W²`. No jet input is used. -/
theorem lintegral_gramStep_le_jet (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hU : ClosedGramUpdate) (hV : ClosedNearVBound)
    (hT : ClosedLeakBound) :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ W in atTop,
        ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
            ¬ IsNewCoord τ W j (Sum.inl e : CIdx K np) →
            ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
                (b3dX b E s h τ m W j (Vs W) (Sum.inl e : CIdx K np)) y‖ₑ ^ 4
              ∂closedLaw b W np ≤
              ENNReal.ofReal C * ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
                ENNReal.ofReal (jetDistance0 b E (b3ClosedX b E s h τ m W j y) ^ 4)) y
                  ∂closedLaw b W np + ENNReal.ofReal (C / (W : ℝ) ^ 2) := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hD.1
  have hb1 : b < 1 := by linarith
  obtain ⟨Cg, Wg, hCg, hg⟩ := eLpNorm_gramForm_le hGA hLp hb0 hb hE1 hE2
  obtain ⟨Cv, hVev⟩ := hV b E np τ m T s h K Vs hD R
  obtain ⟨CT, hTev⟩ := hT b E np τ m T s h K Vs hD R
  set Cf := max (Real.sqrt (max R 0)) (max Cv 0) with hCf
  have hCf0 : 0 ≤ Cf := le_max_of_le_right (le_max_right _ _)
  set Cs := Cg * (Cf ^ 2 + Cf ^ 2 * max CT 0) with hCs
  have hCs0 : 0 ≤ Cs := by positivity
  refine ⟨8 * Cs ^ 4, by positivity, ?_⟩
  filter_upwards [hU b E np τ m T s h K Vs hD, hVev, hTev, hD.2.2.2.2.2,
    eventually_ge_atTop (max Wg 1)] with W hUW hVW hTW hFr hW j hj e he
  have hWg : Wg ≤ W := le_trans (le_max_left _ _) hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hs : closeLen s W ≤ j := (Finset.mem_Ico.1 hj).1
  have hVg := hFr.1
  have hVm : Measurable (Vs W) :=
    hVg.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  obtain ⟨hpas, hupd⟩ := hUW j hj
  have hform := hupd e he
  set μ := closedLaw b W np
  set X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ := b3ClosedX b E s h τ m W j with hXdef
  set u : ProbedPath W np × ℝ → SrcCol K (Fin np) → Fin W → ℂ :=
    fun y d => gramNearU b E s h τ m W j (Vs W) d y with hudef
  set v : ProbedPath W np × ℝ → SrcCol K (Fin np) → Fin W → ℂ :=
    fun y d => gramNearV b E s h τ m W j (Vs W) d y with hvdef
  set w : ℝ := (Real.sqrt W)⁻¹ with hw
  set A := b3Alive b E s h τ m R W j (Vs W)
  set AM := b3AliveM b E s h τ m R W j (Vs W)
  set Good : Set (ProbedPath W np × ℝ) := {y | (passiveY (X y)).PosSemidef ∧
    (∀ d, vecNorm (v y d) ≤ Cv) ∧ GramStepU.oneLeak b E (X y) ≤ CT} with hGooddef
  set S := AM ∩ Good with hSdef
  have hXm : Measurable X := measurable_b3ClosedX b E s h τ m j
  have hum : ∀ d, Measurable fun y => u y d := fun d => measurable_gramNearU b E s h τ m j hVm d
  have hvm : ∀ d, Measurable fun y => v y d := fun d => measurable_gramNearV b E s h τ m j hVm d
  have hAMm : MeasurableSet AM := measurableSet_b3AliveM b E s h τ m R W j hVm
  have hGood : MeasurableSet Good := by
    have e1 : Good = {y | (passiveY (X y)).PosSemidef} ∩ ((⋂ d, {y | vecNorm (v y d) ≤ Cv}) ∩
        {y | GramStepU.oneLeak b E (X y) ≤ CT}) := by
      ext y; simp [hGooddef]
    rw [e1]
    exact (hXm step_measurableSet_passive).inter ((MeasurableSet.iInter fun d =>
      measurableSet_le (measurable_vecNorm_comp (hvm d)) measurable_const).inter
      (measurableSet_le (measurable_oneLeak_comp b E hXm) measurable_const))
  have hSm : MeasurableSet S := hAMm.inter hGood
  -- invariance under the past at `j`
  have hXi : ∀ y, X (b3Ext W j y) = X y := fun y => b3ClosedX_b3Ext hs le_rfl y
  have hui : ∀ y, u (b3Ext W j y) = u y := fun y => funext fun d => gramNearU_b3Ext hs hVg d y
  have hvi : ∀ y, v (b3Ext W j y) = v y := fun y => funext fun d => gramNearV_b3Ext hs hVg d y
  have hSi : ∀ y, b3Ext W j y ∈ S ↔ y ∈ S := by
    intro y
    have hA := mem_b3AliveM_b3Ext b E s h τ m R hs le_rfl (Modul.eq_of_growth hs hVg) y
    simp only [hSdef, hGooddef, Set.mem_inter_iff, Set.mem_ofPred_eq, hXi, hvi]
    rw [hA]
  -- the stopped step is the stopped closed update
  have hAe := b3Alive_ae_eq hb1 hE1 hE2 s h τ m R W j (Vs W)
  have hae : (fun y => ‖A.indicator (b3dX b E s h τ m W j (Vs W) (Sum.inl e : CIdx K np)) y‖ₑ ^
      4) =ᵐ[μ] fun y => ‖S.indicator (fun y => gramForm b E e (u y) (v y) (X y)
        (freshSample W j y.1.1)) y‖ₑ ^ 4 := by
    filter_upwards [hform, hAe, hpas, hVW j hj, hTW j hj] with y h1 h2 h3 h4 h5
    have h2' : (y ∈ A) = (y ∈ AM) := h2
    by_cases hy : y ∈ A
    · have hyM : y ∈ AM := h2' ▸ hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show y ∈ S from
        ⟨hyM, h3, h4 hy, h5 hy⟩), h1]
    · have hyM : y ∉ AM := h2' ▸ hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h' => hyM h'.1)]
  -- the fresh-layer integrand
  set G : (ProbedPath W np × ℝ) × LayerSample W .oneBlockOnePort → ℂ :=
    fun z => gramForm b E e (u z.1) (v z.1) (X z.1) z.2 with hGdef
  have hGm : Measurable G := measurable_gramForm b E e (fun d => (hum d).comp measurable_fst)
    (fun d => (hvm d).comp measurable_fst) (hXm.comp measurable_fst) measurable_snd
  set Φ : ProbedPath W np × ℝ → LayerSample W .oneBlockOnePort → ℝ≥0∞ := fun y F =>
    ‖S.indicator (fun y => gramForm b E e (u y) (v y) (X y) F) y‖ₑ ^ 4 with hΦdef
  have hind : ∀ z : (ProbedPath W np × ℝ) × LayerSample W .oneBlockOnePort, Φ z.1 z.2 =
      ‖(S ×ˢ (Set.univ : Set (LayerSample W .oneBlockOnePort))).indicator G z‖ₑ ^ 4 := by
    intro z
    by_cases hz : z.1 ∈ S
    · rw [hΦdef]; beta_reduce
      rw [Set.indicator_of_mem hz,
        Set.indicator_of_mem (show z ∈ S ×ˢ Set.univ from ⟨hz, Set.mem_univ _⟩), hGdef]
    · rw [hΦdef]; beta_reduce
      rw [Set.indicator_of_notMem hz,
        Set.indicator_of_notMem (fun h' => hz (Set.mem_prod.1 h').1)]
  have hΦm : Measurable fun z : (ProbedPath W np × ℝ) × LayerSample W .oneBlockOnePort =>
      Φ z.1 z.2 := by
    rw [show (fun z : (ProbedPath W np × ℝ) × LayerSample W .oneBlockOnePort => Φ z.1 z.2) =
      fun z => ‖(S ×ˢ (Set.univ : Set (LayerSample W .oneBlockOnePort))).indicator G z‖ₑ ^ 4
      from funext hind]
    exact ((hGm.indicator (hSm.prod MeasurableSet.univ)).enorm).pow_const 4
  have hΦi : ∀ y, Φ (b3Ext W j y) = Φ y := by
    intro y; funext F
    by_cases hy : y ∈ S
    · rw [hΦdef]; beta_reduce
      rw [Set.indicator_of_mem ((hSi y).2 hy), Set.indicator_of_mem hy, hui, hvi, hXi]
    · rw [hΦdef]; beta_reduce
      rw [Set.indicator_of_notMem (fun h' => hy ((hSi y).1 h')),
        Set.indicator_of_notMem hy]
  set Bf : ProbedPath W np × ℝ → ℝ≥0∞ := S.indicator fun y =>
    ENNReal.ofReal ((Cs * (jetDistance0 b E (X y) + w)) ^ 4) with hBfdef
  have hBm : Measurable Bf :=
    (ENNReal.measurable_ofReal.comp ((measurable_const.mul
      (((Transmission.PathScalar.measurable_jetDistance0 b E).comp hXm).add
        measurable_const)).pow_const 4)).indicator hSm
  have hBi : ∀ y, Bf (b3Ext W j y) = Bf y := by
    intro y
    by_cases hy : y ∈ S
    · rw [hBfdef, Set.indicator_of_mem ((hSi y).2 hy), Set.indicator_of_mem hy, hXi]
    · rw [hBfdef, Set.indicator_of_notMem (fun h' => hy ((hSi y).1 h')),
        Set.indicator_of_notMem hy]
  have hBb : ∀ y, ∫⁻ F, Φ y F ∂freshLaw W b ≤ Bf y := by
    intro y
    by_cases hy : y ∈ S
    · rw [hΦdef, hBfdef]; beta_reduce
      simp only [Set.indicator_of_mem hy]
      have hub : ∀ d, vecNorm (u y d) ≤ Cf := fun d =>
        (vecNorm_gramNearU_le hs hy.1 d).trans (le_max_left _ _)
      have hvb : ∀ d, vecNorm (v y d) ≤ Cf := fun d =>
        (hy.2.2.1 d).trans ((le_max_left _ _).trans (le_max_right _ _))
      have hb := hg W hWg e (u y) (v y) (X y) Cf CT hy.2.1 hCf0 hub hvb hy.2.2.2
      have hGy : Measurable fun F => gramForm b E e (u y) (v y) (X y) F :=
        measurable_gramForm b E e (fun d => measurable_const) (fun d => measurable_const)
          measurable_const measurable_id
      rw [← mart_eLpNorm_pow_four hGy.aestronglyMeasurable]
      have hD0 : 0 ≤ Cs * (jetDistance0 b E (X y) + w) :=
        mul_nonneg hCs0 (add_nonneg (norm_nonneg _) (inv_nonneg.2 (Real.sqrt_nonneg _)))
      calc eLpNorm (fun F => gramForm b E e (u y) (v y) (X y) F) 4 (freshLaw W b) ^ 4 ≤
            ENNReal.ofReal (Cs * (jetDistance0 b E (X y) + w)) ^ 4 :=
            pow_le_pow_left₀ zero_le hb 4
        _ = _ := (ENNReal.ofReal_pow hD0 4).symm
    · rw [hΦdef, hBfdef]; beta_reduce
      simp only [Set.indicator_of_notMem hy, enorm_zero]
      simp
  -- the pointwise jet weight
  have hpt : ∀ y, Bf y ≤ ENNReal.ofReal (8 * Cs ^ 4) *
      AM.indicator (fun y => ENNReal.ofReal (jetDistance0 b E (X y) ^ 4)) y +
        ENNReal.ofReal (8 * Cs ^ 4 * w ^ 4) := by
    intro y
    by_cases hy : y ∈ S
    · rw [hBfdef, Set.indicator_of_mem hy, Set.indicator_of_mem hy.1]
      have hδ0 : 0 ≤ jetDistance0 b E (X y) := norm_nonneg _
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h8 := Four.add_pow_four_le_real (jetDistance0 b E (X y)) w
      calc (Cs * (jetDistance0 b E (X y) + w)) ^ 4 =
            Cs ^ 4 * (jetDistance0 b E (X y) + w) ^ 4 := by ring
        _ ≤ Cs ^ 4 * (8 * (jetDistance0 b E (X y) ^ 4 + w ^ 4)) :=
            mul_le_mul_of_nonneg_left h8 (by positivity)
        _ = _ := by ring
    · rw [hBfdef, Set.indicator_of_notMem hy]; exact zero_le
  have hw4 : w ^ 4 = ((W : ℝ) ^ 2)⁻¹ := by
    rw [hw, inv_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hW0.le]
  calc ∫⁻ y, ‖A.indicator (b3dX b E s h τ m W j (Vs W) (Sum.inl e : CIdx K np)) y‖ₑ ^ 4 ∂μ
      = ∫⁻ y, Φ y (freshSample W j y.1.1) ∂μ := by
        rw [lintegral_congr_ae hae]
        refine lintegral_congr fun y => ?_
        rw [hΦdef]
        beta_reduce
        by_cases hy : y ∈ S
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
    _ ≤ ∫⁻ y, Bf y ∂μ := lintegral_closed_fresh_le b j hΦm hΦi hBm hBi hBb
    _ ≤ ∫⁻ y, (ENNReal.ofReal (8 * Cs ^ 4) *
          AM.indicator (fun y => ENNReal.ofReal (jetDistance0 b E (X y) ^ 4)) y +
            ENNReal.ofReal (8 * Cs ^ 4 * w ^ 4)) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal (8 * Cs ^ 4) *
          ∫⁻ y, A.indicator (fun y => ENNReal.ofReal (jetDistance0 b E (X y) ^ 4)) y ∂μ +
            ENNReal.ofReal (8 * Cs ^ 4 * w ^ 4) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const, measure_univ, mul_one,
          lintegral_congr_ae (indicator_ae_eq_of_ae_eq_set hAe.symm)]
    _ = _ := by rw [hw4, div_eq_mul_inv]

/-- **`ClosedGramStepFourAt` from the closed exact update**: the closed update, the frame and leak
bounds on the alive set, the stopped closed jet `ClosedJetStopHalf` and the input hypotheses.
-/
theorem closedGramStepFourAt_of_closed (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hU : ClosedGramUpdate) (hV : ClosedNearVBound)
    (hT : ClosedLeakBound) (hJ : ClosedJetStopHalf) : ClosedGramStepFourAt := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨C, hC0, hC⟩ := lintegral_gramStep_le_jet hGA hLp hU hV hT b E np τ m T s h K Vs hD R
  obtain ⟨Cδ, hJev⟩ := hJ b E np τ m T s h K Vs hD R
  refine ⟨C * (max Cδ 0 + 1), ?_⟩
  filter_upwards [hC, hJev, eventually_ge_atTop 1] with W hW hJW hW1 j hj e he
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  refine (hW j hj e he).trans ?_
  calc ENNReal.ofReal C * ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
          ENNReal.ofReal (jetDistance0 b E (b3ClosedX b E s h τ m W j y) ^ 4)) y
            ∂closedLaw b W np + ENNReal.ofReal (C / (W : ℝ) ^ 2)
      ≤ ENNReal.ofReal C * ENNReal.ofReal (max Cδ 0 / (W : ℝ) ^ 2) +
          ENNReal.ofReal (C / (W : ℝ) ^ 2) :=
        add_le_add (mul_le_mul' le_rfl ((hJW j hj).trans (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))))) le_rfl
    _ = ENNReal.ofReal (C * (max Cδ 0 + 1) / (W : ℝ) ^ 2) := by
        have hm : 0 ≤ max Cδ 0 := le_max_right _ _
        rw [← ENNReal.ofReal_mul hC0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        ring

end BlockBand.SourceProcess.PhysApprox.B3
