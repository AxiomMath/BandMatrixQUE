module

public import BlockBand.SourceProcess.PhysApprox.B3BirthKSubCross
public import BlockBand.SourceProcess.PhysApprox.B3BirthPTrace
public import BlockBand.SourceProcess.PhysApprox.B3JetFam
public import BlockBand.SourceProcess.TagBirth.FreshTrace

/-!
# The closed fresh `𝒦` diagonal at a birth step

Measure `closedLaw b W np`; domain `FrameDomain`. At the birth length `j + 1` of tag `i`
(`closedK_birth_new_new`, `birthG_eq`), `𝒦_cl,ii = (m/W)Q_𝒢(g)`, `𝒢 = R_cl + R_clΔR_cl`, so
`𝒦_cl,ii − am = (m/W)(Q_𝒢(g) − Tr 𝒢) + m(W⁻¹Tr 𝒢 − a)`. Then:
* Gaussian concentration over the newborn probe (`Birth.lintegral_quad_sub_le`,
  `BirthP.inv_mul_sqrt_trace_le`): `(m/W)E|Q − Tr| ≤ m W^{-1/2}‖𝒢‖`, `‖𝒢‖ ≤ e + e²‖Δ‖`,
  `e = η⁻¹` (passivity), `E‖Δ‖ ≤ C₂`;
* the fresh-layer trace (`TagBirth.freshPhysTraceLp_holds` at `p = 1`, through the fresh-layer
  Fubini): `E|W⁻¹Tr 𝒢 − a| ≤ A E δ₀(X_cl) + B/√W`;
* the closed jet `ClosedJet0Fam` at **`p = 1`**: `E δ₀(X_cl) ≤ C/W`.
The alive indicator is dropped (`≤`).

**Proved**: `complexBirthKDiag_of_jet hGA hLp (hJ : ClosedJet0Fam) : ComplexBirthKDiag`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosingLeak BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.PhysApprox.ClosedForm BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.ClosingAux
open scoped NNReal ENNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

variable {W np : ℕ}

namespace BirthKSub

/-- **Averaging over one probe** under the closed law. -/
theorem lintegral_closed_single_le {b : ℝ} (i : Fin np) {f : ProbedPath W np × ℝ → ℝ≥0∞}
    {Φ : GrowthPath W × ℝ → (Fin W → ℂ) → ℝ≥0∞} {D : GrowthPath W × ℝ → ℝ≥0∞}
    (hf : ∀ᵐ y ∂closedLaw b W np, f y ≤ Φ (y.1.1, y.2) (y.1.2 i))
    (hΦ : Measurable fun q : (GrowthPath W × ℝ) × (Fin W → ℂ) => Φ q.1 q.2)
    (hin : ∀ p, ∫⁻ g, Φ p g ∂circularVectorLaw (Fin W) ≤ D p) (hD : Measurable D) :
    ∫⁻ y, f y ∂closedLaw b W np ≤ ∫⁻ y, D (y.1.1, y.2) ∂closedLaw b W np := by
  refine (lintegral_mono_ae hf).trans ?_
  have hF : Measurable fun y : ProbedPath W np × ℝ => Φ (y.1.1, y.2) (y.1.2 i) :=
    hΦ.comp (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)))
  have hDy : Measurable fun y : ProbedPath W np × ℝ => D (y.1.1, y.2) :=
    hD.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  rw [closedLaw, lintegral_prod _ hF.aemeasurable, lintegral_prod _ hDy.aemeasurable,
    probedPathLaw, lintegral_prod _ hF.lintegral_prod_right'.aemeasurable,
    lintegral_prod _ hDy.lintegral_prod_right'.aemeasurable]
  refine lintegral_mono fun ω => ?_
  have hsw : Measurable (Function.uncurry fun (G : Fin np → Fin W → ℂ) (θ : ℝ) =>
      Φ (ω, θ) (G i)) :=
    hΦ.comp ((measurable_const.prodMk measurable_snd).prodMk
      ((measurable_pi_apply i).comp measurable_fst))
  dsimp only
  rw [lintegral_lintegral_swap hsw.aemeasurable]
  calc ∫⁻ θ, ∫⁻ G, Φ (ω, θ) (G i) ∂Measure.pi (fun _ : Fin np => circularVectorLaw (Fin W))
        ∂phaseLaw
      ≤ ∫⁻ θ, D (ω, θ) ∂phaseLaw := by
        refine lintegral_mono fun θ => ?_
        have hΦp : Measurable fun g : Fin W → ℂ => Φ (ω, θ) g :=
          hΦ.comp (measurable_const.prodMk measurable_id)
        rw [(measurePreserving_eval (fun _ : Fin np => circularVectorLaw (Fin W)) i).lintegral_comp
          hΦp]
        exact hin _
    _ = ∫⁻ G, ∫⁻ θ, D (ω, θ) ∂phaseLaw ∂Measure.pi (fun _ : Fin np => circularVectorLaw (Fin W)) :=
        by rw [lintegral_const, measure_univ, mul_one]

/-- The fresh corner `𝒢 = R_cl + R_clΔR_cl` at `(ω, θ)`. -/
def gcl (b E s h : ℝ) (W j : ℕ) (p : GrowthPath W × ℝ) : Matrix (Fin W) (Fin W) ℂ :=
  passiveResolvent b E (xcl b E s h W j p) +
    passiveResolvent b E (xcl b E s h W j p) * dcl b E s h W j p *
      passiveResolvent b E (xcl b E s h W j p)

theorem measurable_gcl (b E s h : ℝ) (W j : ℕ) : Measurable (gcl b E s h W j) :=
  measurable_matrix_add (measurable_rcl b E s h W j)
    (measurable_matrix_mul' (measurable_matrix_mul' (measurable_rcl b E s h W j)
      (measurable_dcl b E s h W j)) (measurable_rcl b E s h W j))

theorem measurable_trace_comp {α : Type*} [MeasurableSpace α] {M : α → Matrix (Fin W) (Fin W) ℂ}
    (hM : Measurable M) : Measurable fun a => (M a).trace := by
  unfold Matrix.trace Matrix.diag
  exact Finset.measurable_sum _ fun z _ => hM.eval_matrix

/-- **The newborn diagonal at its birth length**, split into a probe fluctuation and a trace. -/
theorem closedK_diag_split (b E s h : ℝ) (τ m : Fin np → ℝ) (hm : ∀ c, 0 ≤ m c) {j : ℕ}
    (y : ProbedPath W np × ℝ) (hblk : GclSuccBlocks b E s h W j y.1.1 (phase y.2))
    (hη : 0 < etaZ b E) (hX : (passiveY (closedNearX b E s h W j y.1.1 (phase y.2))).PosSemidef)
    {i : Fin np} (hi : ⌊(W : ℝ) * τ i⌋₊ = j) :
    ‖b3ClosedKAt b E s h τ m W (j + 1) y i i - matchedA E * (m i : ℂ)‖ₑ ≤
      ENNReal.ofReal (m i / W) * ‖Counting.complexQuadraticForm (gcl b E s h W j (y.1.1, y.2))
          (y.1.2 i) - (gcl b E s h W j (y.1.1, y.2)).trace‖ₑ +
        ENNReal.ofReal (m i) *
          ‖(W : ℂ)⁻¹ * (gcl b E s h W j (y.1.1, y.2)).trace - matchedA E‖ₑ := by
  have hma : 0 ≤ m i / W := div_nonneg (hm i) (Nat.cast_nonneg W)
  have hG : birthG b E s h W j y.1.1 (phase y.2) = gcl b E s h W j (y.1.1, y.2) :=
    birthG_eq s h hη y.1.1 (phase y.2) hX
  rw [closedK_birth_new_new b E s h τ m y hblk hi, bilinear_smul_left, bilinear_smul_right,
    hG, bilinear_self_eq_quad, ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt hma]
  set Q := Counting.complexQuadraticForm (gcl b E s h W j (y.1.1, y.2)) (y.1.2 i)
  set t := (gcl b E s h W j (y.1.1, y.2)).trace
  have e : ((m i / W : ℝ) : ℂ) * Q - matchedA E * (m i : ℂ) =
      ((m i / W : ℝ) : ℂ) * (Q - t) + (m i : ℂ) * ((W : ℂ)⁻¹ * t - matchedA E) := by
    rw [Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  rw [e]
  refine (enorm_add_le _ _).trans ?_
  rw [enorm_mul, enorm_mul, enorm_ofReal_nonneg hma, enorm_ofReal_nonneg (hm i)]

/-- Abbreviation for the past coordinates. -/
abbrev PS (W j : ℕ) := BlockBand.Transmission.PathScalar.PastSample W j

/-- **The fresh-layer trace** (`FreshPhysTraceLp` at `p = 1`, fresh-layer Fubini):
`E|W⁻¹Tr 𝒢 − a| ≤ E[A δ₀(X_cl) + B/√W]`. -/
theorem lintegral_trace_fresh_le (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    ∃ (A B : ℝ) (W₀ : ℕ), 0 ≤ A ∧ 0 ≤ B ∧ ∀ W : ℕ, W₀ ≤ W → 1 ≤ W → ∀ (s h : ℝ), h ^ 2 < 1 →
      ∀ (np j : ℕ), closeLen s W ≤ j →
        ∫⁻ y, ‖(W : ℂ)⁻¹ * (gcl b E s h W j (y.1.1, y.2)).trace - matchedA E‖ₑ
            ∂closedLaw b W np ≤
          ∫⁻ y, ENNReal.ofReal (A * jetDistance0 b E (xcl b E s h W j (y.1.1, y.2)) +
            B / Real.sqrt W) ∂closedLaw b W np := by
  obtain ⟨hκ, hEκ⟩ := BlockBand.SourceProcess.TagBirth.mem_bulkInterval_self hE1 hE2
  obtain ⟨A, B, W₀, hA, hB, hF⟩ :=
    BlockBand.SourceProcess.TagBirth.freshPhysTraceLp_holds hGA hLp b hb0 hb _ hκ 1 le_rfl
  refine ⟨A, B, W₀, hA, hB, fun W hW hW1 s h hh np j hs => ?_⟩
  have hη : 0 < etaZ b E := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  set τ0 : Fin np → ℝ := fun _ => 0
  set X := b3ClosedX b E s h τ0 τ0 W j with hXdef
  have hXm : Measurable X := measurable_b3ClosedX b E s h τ0 τ0 j
  have hX' : ∀ y, X (b3Ext W j y) = X y := fun y => b3ClosedX_b3Ext hs le_rfl y
  have hXr : Measurable fun z : (PS W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
      LayerSample W .oneBlockOnePort => X (b3Rebuild W j z.1) :=
    hXm.comp ((measurable_b3Rebuild W j).comp measurable_fst)
  have hRr : Measurable fun z : (PS W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
      LayerSample W .oneBlockOnePort => passiveResolvent b E (X (b3Rebuild W j z.1)) := by
    unfold passiveResolvent
    exact measurable_matrix_inv.comp (measurable_matrix_sub measurable_const hXr)
  have hDr := BlockBand.SourceProcess.FullSource.measurable_freshDelta_comp b E hXr
    measurable_snd
  set g : (PS W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort →
      ℝ≥0∞ := fun z => ‖(W : ℂ)⁻¹ * (passiveResolvent b E (X (b3Rebuild W j z.1)) +
        passiveResolvent b E (X (b3Rebuild W j z.1)) * freshDelta b E (X (b3Rebuild W j z.1)) z.2 *
          passiveResolvent b E (X (b3Rebuild W j z.1))).trace - matchedA E‖ₑ with hgdef
  have hg : Measurable g :=
    ((measurable_const.mul (measurable_trace_comp (measurable_matrix_add hRr
      (measurable_matrix_mul' (measurable_matrix_mul' hRr hDr) hRr)))).sub_const _).enorm
  have hT : Measurable fun y : ProbedPath W np × ℝ => (b3Past W j y, freshSample W j y.1.1) :=
    (measurable_b3Past W j).prodMk
      ((measurable_freshSample W j).comp (measurable_fst.comp measurable_fst))
  have hgT : (fun y => g (b3Past W j y, freshSample W j y.1.1)) =
      fun y => ‖(W : ℂ)⁻¹ * (gcl b E s h W j (y.1.1, y.2)).trace - matchedA E‖ₑ := by
    funext y
    simp only [hgdef, b3Rebuild_b3Past, hX']
    rfl
  rw [← hgT, ← lintegral_map hg hT, closedLaw_map_past_fresh, lintegral_prod _ hg.aemeasurable,
    ← closedLaw_map_b3Past b W np j,
    lintegral_map hg.lintegral_prod_right' (measurable_b3Past W j)]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_passive_b3ClosedX hb0 hb hE1 hE2 s h hh τ0 τ0 hW1 j] with y hy
  simp only [hgdef, b3Rebuild_b3Past, hX']
  have h1 := hF W hW E hEκ (X y) hy
  have hmeas : AEStronglyMeasurable (fun F => BlockBand.Transmission.PathScalar.physTr b E (X y) F -
      matchedA E) (freshLaw W b) :=
    ((measurable_const.mul (measurable_trace_comp (measurable_g11 E _ (X y)))).sub_const
      _).aestronglyMeasurable
  rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm hmeas] at h1
  refine le_trans (le_of_eq ?_) h1
  refine lintegral_congr fun F => ?_
  rw [← BlockBand.SourceProcess.TagBirth.g11_eq_resolvent_add hη hy F]
  rfl

/-- **The probe fluctuation**: `E[(m/W)(Re Tr 𝒢𝒢ᴴ)^{1/2}] ≤ m W^{-1/2} η⁻¹ E‖1 + ΔR_cl‖`. -/
theorem lintegral_hs_gcl_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (s h : ℝ) (hh : h ^ 2 < 1) (hW1 : 1 ≤ W) (j : ℕ) {mi : ℝ} (hmi : 0 ≤ mi) :
    ∫⁻ y, ENNReal.ofReal (mi / W) * ENNReal.ofReal (Real.sqrt
        ((gcl b E s h W j (y.1.1, y.2)) * (gcl b E s h W j (y.1.1, y.2))ᴴ).trace.re)
        ∂closedLaw b W np ≤
      ENNReal.ofReal (mi * (Real.sqrt W)⁻¹ * (etaZ b E)⁻¹) *
        ∫⁻ y, ENNReal.ofReal ‖mOld b E s h W j (y.1.1, y.2)‖ ∂closedLaw b W np := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_passive_b3ClosedX (np := np) hb0 hb hE1 hE2 s h hh (fun _ => 0) (fun _ => 0)
    hW1 j] with y hy
  have hR := BlockBand.Transmission.PassiveCovariance.norm_passiveResolvent_le hb0 hb hE1 hE2 hy
  set Rm := passiveResolvent b E (xcl b E s h W j (y.1.1, y.2))
  have hG : gcl b E s h W j (y.1.1, y.2) = Rm * mOld b E s h W j (y.1.1, y.2) := by
    simp only [gcl, mOld, Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc, Rm]
  have hn : ‖gcl b E s h W j (y.1.1, y.2)‖ ≤ (etaZ b E)⁻¹ * ‖mOld b E s h W j (y.1.1, y.2)‖ := by
    rw [hG]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  have hmW : 0 ≤ mi / W := div_nonneg hmi (Nat.cast_nonneg W)
  have hη : 0 < etaZ b E := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  have hc : 0 ≤ mi * (Real.sqrt W)⁻¹ * (etaZ b E)⁻¹ :=
    mul_nonneg (mul_nonneg hmi (inv_nonneg.2 (Real.sqrt_nonneg _))) (inv_nonneg.2 hη.le)
  rw [← ENNReal.ofReal_mul hmW, ← ENNReal.ofReal_mul hc]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := BirthP.inv_mul_sqrt_trace_le (gcl b E s h W j (y.1.1, y.2))
  calc mi / W * Real.sqrt ((gcl b E s h W j (y.1.1, y.2)) *
        (gcl b E s h W j (y.1.1, y.2))ᴴ).trace.re
      = mi * ((W : ℝ)⁻¹ * Real.sqrt ((gcl b E s h W j (y.1.1, y.2)) *
        (gcl b E s h W j (y.1.1, y.2))ᴴ).trace.re) := by ring
    _ ≤ mi * ((Real.sqrt W)⁻¹ * ‖gcl b E s h W j (y.1.1, y.2)‖) :=
        mul_le_mul_of_nonneg_left h1 hmi
    _ ≤ mi * ((Real.sqrt W)⁻¹ * ((etaZ b E)⁻¹ * ‖mOld b E s h W j (y.1.1, y.2)‖)) := by
        gcongr
    _ = mi * (Real.sqrt W)⁻¹ * (etaZ b E)⁻¹ * ‖mOld b E s h W j (y.1.1, y.2)‖ := by ring

theorem measurable_quad_gcl (b E s h : ℝ) (W j : ℕ) :
    Measurable fun q : (GrowthPath W × ℝ) × (Fin W → ℂ) =>
      Counting.complexQuadraticForm (gcl b E s h W j q.1) q.2 := by
  unfold Counting.complexQuadraticForm
  refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun a' _ => ?_
  exact (((measurable_gcl b E s h W j).eval_matrix).comp measurable_fst).mul
    ((Complex.continuous_conj.measurable.comp ((measurable_pi_apply a).comp measurable_snd)).mul
      ((measurable_pi_apply a').comp measurable_snd))

theorem tendsto_inv_sqrt_nat : Tendsto (fun W : ℕ => (Real.sqrt W)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

theorem tendsto_inv_nat : Tendsto (fun W : ℕ => ((W : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

end BirthKSub

open BirthKSub

/-- **`ComplexBirthKDiag` from the closed jet at `p = 1`** (with `GaussianAbsorptionContract` and
`GaussianLpGradient`). -/
theorem complexBirthKDiag_of_jet (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hJ : ClosedJet0Fam) : ComplexBirthKDiag := by
  intro b E np τ m T s h K Vs hDom R θ hθ i
  have hDom' := hDom
  obtain ⟨hCSL, hs, -, hh0, hh1, -⟩ := hDom
  obtain ⟨hb0, hb, hE1, hE2, -, -, hm, -⟩ := hCSL
  have hh : h ^ 2 < 1 := by nlinarith
  have hη : 0 < etaZ b E := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  obtain ⟨CJ, hCJ⟩ := hJ b E np τ m T s h K Vs hDom' 1 le_rfl
  obtain ⟨C₂, W₀, hC₂, hMom⟩ := lintegral_m_le hGA hb0 hb hE1 hE2
  obtain ⟨A, B, W₁, hA, hB, hTr⟩ := lintegral_trace_fresh_le hGA hLp hb0 hb hE1 hE2
  set e : ℝ := (etaZ b E)⁻¹
  have he : 0 ≤ e := inv_nonneg.2 hη.le
  set q : ℝ := C₂ / etaZ b E
  have hq : 0 ≤ q := div_nonneg hC₂ hη.le
  set CJ' : ℝ := max CJ 0
  set c1 : ℝ := m i * e * (1 + q) + m i * B
  set c2 : ℝ := m i * A * CJ'
  have hc1 : 0 ≤ c1 := by have := hm i; positivity
  have hc2 : 0 ≤ c2 := by have := hm i; have : 0 ≤ CJ' := le_max_right _ _; positivity
  have hTot : Tendsto (fun W : ℕ => c1 * (Real.sqrt W)⁻¹ + c2 * ((W : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_sqrt_nat.const_mul c1).add (tendsto_inv_nat.const_mul c2)
  have hcl : ∀ᶠ W : ℕ in atTop, 1 ≤ closeLen s W :=
    (tendsto_nat_floor_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const hs)).eventually_ge_atTop 1
  filter_upwards [eventually_ge_atTop (max (max W₀ W₁) 1), hcl, hCJ,
    hTot.eventually (gt_mem_nhds hθ)] with W hW hclW hJW hTW
  intro j hj1 hj2 hji
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have hW0 : W₀ ≤ W := (le_max_left _ _).trans (le_of_max_le_left hW)
  have hW1' : W₁ ≤ W := (le_max_right _ _).trans (le_of_max_le_left hW)
  have hj : 1 ≤ j := hclW.trans hj1
  have hmW : 0 ≤ m i / W := div_nonneg (hm i) (Nat.cast_nonneg W)
  set Gp := gcl b E s h W j
  -- the probe average
  have hmain : ∫⁻ y, ‖b3ClosedKAt b E s h τ m W (j + 1) y i i - matchedA E * (m i : ℂ)‖ₑ
      ∂closedLaw b W np ≤
      ∫⁻ y, (ENNReal.ofReal (m i / W) * ENNReal.ofReal (Real.sqrt
          (Gp (y.1.1, y.2) * (Gp (y.1.1, y.2))ᴴ).trace.re) +
        ENNReal.ofReal (m i) * ‖(W : ℂ)⁻¹ * (Gp (y.1.1, y.2)).trace - matchedA E‖ₑ)
        ∂closedLaw b W np := by
    refine lintegral_closed_single_le i
      (Φ := fun p g => ENNReal.ofReal (m i / W) *
        ‖Counting.complexQuadraticForm (Gp p) g - (Gp p).trace‖ₑ +
        ENNReal.ofReal (m i) * ‖(W : ℂ)⁻¹ * (Gp p).trace - matchedA E‖ₑ)
      (D := fun p => ENNReal.ofReal (m i / W) * ENNReal.ofReal (Real.sqrt
          (Gp p * (Gp p)ᴴ).trace.re) +
        ENNReal.ofReal (m i) * ‖(W : ℂ)⁻¹ * (Gp p).trace - matchedA E‖ₑ) ?_ ?_ ?_ ?_
    · filter_upwards [ae_birth_good (np := np) hb0 hb hE1 hE2 s h hh τ m hW1 hj] with y hy0
      obtain ⟨hblk, hX, -, -⟩ := hy0
      exact closedK_diag_split b E s h τ m hm y hblk hη hX hji
    · have hGm := measurable_gcl b E s h W j
      exact (measurable_const.mul ((measurable_quad_gcl b E s h W j).sub
        (measurable_trace_comp (hGm.comp measurable_fst))).enorm).add
        (measurable_const.mul ((measurable_const.mul (measurable_trace_comp
          (hGm.comp measurable_fst))).sub_const _).enorm)
    · intro p
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      exact Birth.lintegral_quad_sub_le (Gp p)
    · have hGm := measurable_gcl b E s h W j
      refine (measurable_const.mul (Real.continuous_sqrt.measurable.comp
        (Complex.measurable_re.comp (measurable_trace_comp (measurable_matrix_mul' hGm
          (measurable_matrix_conjTranspose' hGm))))).ennreal_ofReal).add ?_
      exact measurable_const.mul ((measurable_const.mul (measurable_trace_comp hGm)).sub_const
        _).enorm
  -- the two expectations
  have hGm := measurable_gcl b E s h W j
  have hp1m : Measurable fun y : ProbedPath W np × ℝ => ENNReal.ofReal (m i / W) *
      ENNReal.ofReal (Real.sqrt (Gp (y.1.1, y.2) * (Gp (y.1.1, y.2))ᴴ).trace.re) :=
    measurable_const.mul (Real.continuous_sqrt.measurable.comp
      (Complex.measurable_re.comp (measurable_trace_comp (measurable_matrix_mul'
        (hGm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
        (measurable_matrix_conjTranspose'
          (hGm.comp ((measurable_fst.comp measurable_fst).prodMk
            measurable_snd))))))).ennreal_ofReal
  have hP1 : ∫⁻ y, ENNReal.ofReal (m i / W) * ENNReal.ofReal (Real.sqrt
        (Gp (y.1.1, y.2) * (Gp (y.1.1, y.2))ᴴ).trace.re) ∂closedLaw b W np ≤
      ENNReal.ofReal (m i * (Real.sqrt W)⁻¹ * e) * ENNReal.ofReal (1 + q) := by
    refine (lintegral_hs_gcl_le (np := np) hb0 hb hE1 hE2 s h hh hW1 j (hm i)).trans ?_
    gcongr
    exact (hMom W hW0 hW1 s h hh np j hj1).1
  have hP2 := hTr W hW1' hW1 s h hh np j hj1
  have hδ : ∫⁻ y, ENNReal.ofReal (jetDistance0 b E (xcl b E s h W j (y.1.1, y.2)))
      ∂closedLaw b W np ≤ ENNReal.ofReal (CJ' / W) := by
    have h0 := hJW j (Finset.mem_Ico.2 ⟨hj1, hj2⟩)
    have hmeas : AEStronglyMeasurable (fun y => jetDistance0 b E (b3ClosedX b E s h τ m W j y))
        (closedLaw b W np) := by
      unfold jetDistance0 passiveResolvent
      exact ((measurable_const.mul (measurable_trace_comp (measurable_matrix_inv.comp
        (measurable_matrix_sub measurable_const (measurable_b3ClosedX b E s h τ m j))))).sub_const
        _).norm.aestronglyMeasurable
    rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm hmeas] at h0
    refine le_trans (le_of_eq ?_) (h0.trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg W))))
    refine lintegral_congr fun y => ?_
    have hd : 0 ≤ jetDistance0 b E (b3ClosedX b E s h τ m W j y) := norm_nonneg _
    rw [Real.enorm_eq_ofReal hd]
    rfl
  have hP2' : ∫⁻ y, ENNReal.ofReal (A * jetDistance0 b E (xcl b E s h W j (y.1.1, y.2)) +
      B / Real.sqrt W) ∂closedLaw b W np ≤
      ENNReal.ofReal (A * (CJ' / W) + B / Real.sqrt W) := by
    have hsplit : ∀ y : ProbedPath W np × ℝ,
        ENNReal.ofReal (A * jetDistance0 b E (xcl b E s h W j (y.1.1, y.2)) + B / Real.sqrt W) =
          ENNReal.ofReal A * ENNReal.ofReal (jetDistance0 b E (xcl b E s h W j (y.1.1, y.2))) +
            ENNReal.ofReal (B / Real.sqrt W) := fun y => by
      have hd : 0 ≤ jetDistance0 b E (xcl b E s h W j (y.1.1, y.2)) := norm_nonneg _
      rw [ENNReal.ofReal_add (mul_nonneg hA hd) (by positivity),
        ENNReal.ofReal_mul hA]
    simp_rw [hsplit]
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_add (by positivity)
        (by positivity), ENNReal.ofReal_mul hA]
    gcongr
  calc ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
          b3ClosedKAt b E s h τ m W (j + 1) y i i - matchedA E * (m i : ℂ)) y‖ₑ
          ∂closedLaw b W np
      ≤ ∫⁻ y, ‖b3ClosedKAt b E s h τ m W (j + 1) y i i - matchedA E * (m i : ℂ)‖ₑ
          ∂closedLaw b W np := lintegral_mono fun y => by
        by_cases hy : y ∈ b3Alive b E s h τ m R W j (Vs W)
        · rw [Set.indicator_of_mem hy]
        · rw [Set.indicator_of_notMem hy, enorm_zero]
          exact zero_le
    _ ≤ _ := hmain
    _ = ∫⁻ y, ENNReal.ofReal (m i / W) * ENNReal.ofReal (Real.sqrt
          (Gp (y.1.1, y.2) * (Gp (y.1.1, y.2))ᴴ).trace.re) ∂closedLaw b W np +
        ENNReal.ofReal (m i) * ∫⁻ y, ‖(W : ℂ)⁻¹ * (Gp (y.1.1, y.2)).trace - matchedA E‖ₑ
          ∂closedLaw b W np := by
        rw [lintegral_add_left hp1m,
          lintegral_const_mul' (ENNReal.ofReal (m i)) _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (m i * (Real.sqrt W)⁻¹ * e) * ENNReal.ofReal (1 + q) +
        ENNReal.ofReal (m i) * ENNReal.ofReal (A * (CJ' / W) + B / Real.sqrt W) := by
        exact add_le_add hP1 (by gcongr; exact hP2.trans hP2')
    _ = ENNReal.ofReal (c1 * (Real.sqrt W)⁻¹ + c2 * ((W : ℝ))⁻¹) := by
        have hA' : 0 ≤ A * (CJ' / W) + B / Real.sqrt W := by
          have : 0 ≤ CJ' := le_max_right _ _
          positivity
        rw [← ENNReal.ofReal_mul (by have := hm i; positivity), ← ENNReal.ofReal_mul (hm i),
          ← ENNReal.ofReal_add (by have := hm i; positivity) (mul_nonneg (hm i) hA')]
        congr 1
        simp only [c1, c2, div_eq_mul_inv]
        ring
    _ ≤ ENNReal.ofReal θ := ENNReal.ofReal_le_ofReal hTW.le

end BlockBand.SourceProcess.PhysApprox.B3
