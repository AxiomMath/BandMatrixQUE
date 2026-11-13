module

public import BlockBand.SourceProcess.PhysApprox.ClosingGramInt
public import BlockBand.SourceProcess.PhysApprox.Assembly
public import BlockBand.SourceProcess.ComplexConstruct.Tight
public import BlockBand.SourceProcess.RawTag.Holds

/-!
# The closing error of the Gram coordinates and the current

This file proves `TargetT3`. Measure `μ_W = probedPathLaw W np b ⊗ phaseLaw`. With the column
norms `a_j = ‖V e_j‖`, `d_j = ‖(V_cl - V)e_j‖`, `e_j = ‖P𝕊Z V e_j‖` (`colA`, `colD`, `colE`),
almost surely (`gramErr_le` and AM–GM with weight `λ`)
`|Δ_{r,ik}| ≤ λ(a_i² + a_k²) + (1/λ + 1)(d_i² + d_k² + e_i² + e_k²)` for `r ≠ 0`, and
* `lintegral_colA_le`: `E a_j² ≤ B` for all large `W` (raw tag moments, `E M_jj`);
* `lintegral_colD_le`: `E d_j² ≤ 2 m_j E Tr(A_- Y_j)/W` (Hardy identity, one probe Gaussian),
  the integrand of the input leakage `TagChannelLeakage` at `τ_j`;
* `lintegral_colE_le`: `E e_j² ≤ m_j E Tr(A_+ 𝕊Y_j𝕊ᴴ)/W` (cavity bound), the integrand of the
  output leakage `TagChannelLeakageOut`.
Choosing `λ` from `B` and then `h`, `W` from the two leakages gives `GramClosingSmall`:
`gramClosingSmall_of_raw : RawTagMoments → TagChannelLeakage → TagChannelLeakageOut →
GramClosingSmall`; `t3 : TargetT3`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosingLeak
open BlockBand.SourceProcess.ClosingAux BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal

variable {W np : ℕ}

/-- `‖V e_j‖` (probe frame column). -/
def colA (b E T : ℝ) (τ m : Fin np → ℝ) (W : ℕ) (j : Fin np) (y : ProbedPath W np × ℝ) : ℝ :=
  l2 ((probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m y.1)ᵀ j)

/-- `‖(V_cl - V) e_j‖`. -/
def colD (b E s T h : ℝ) (τ m : Fin np → ℝ) (W : ℕ) (j : Fin np) (y : ProbedPath W np × ℝ) :
    ℝ :=
  l2 ((closedFrame b E s T h τ m W (phase y.2) y.1 - probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m y.1)ᵀ j)

/-- `‖P𝕊Z V e_j‖`. -/
def colE (b E s T h : ℝ) (τ m : Fin np → ℝ) (W : ℕ) (j : Fin np) (y : ProbedPath W np × ℝ) :
    ℝ :=
  l2 ((nearProjection W * scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ y.1.1 *
    closingZ (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ y.1.1)
      (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ y.1.1))
      (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ y.1.1)) (phase y.2) *
    probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m y.1)ᵀ j)

theorem measurable_colA (b E T : ℝ) (τ m : Fin np → ℝ) (W : ℕ) (j : Fin np) :
    Measurable (colA b E T τ m W j) :=
  measurable_l2_col ((measurable_probeFrame b E W _ τ m).comp measurable_fst) j

theorem measurable_colD (b E s T h : ℝ) (τ m : Fin np → ℝ) (W : ℕ) (j : Fin np) :
    Measurable (colD b E s T h τ m W j) :=
  measurable_l2_col (measurable_matrix_sub
    (measurable_closedFrame_comp b E s T h τ m measurable_fst
      (measurable_phase.comp measurable_snd))
    ((measurable_probeFrame b E W _ τ m).comp measurable_fst)) j

theorem measurable_colE (b E s T h : ℝ) (τ m : Fin np → ℝ) (W : ℕ) (j : Fin np) :
    Measurable (colE b E s T h τ m W j) := by
  have hω : Measurable fun y : ProbedPath W np × ℝ => y.1.1 := measurable_fst.comp measurable_fst
  have hz : Measurable fun y : ProbedPath W np × ℝ => phase y.2 :=
    measurable_phase.comp measurable_snd
  have hS : Measurable fun y : ProbedPath W np × ℝ =>
      scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ y.1.1 :=
    (measurable_scatteringMatrix b E _).comp hω
  have hN := measurable_physClosingN_comp b E s T h hω
  have hinv : Measurable fun y : ProbedPath W np × ℝ =>
      (1 - phase y.2 • physClosingN b E s T h W y.1.1)⁻¹ :=
    measurable_matrix_inv.comp (measurable_matrix_sub measurable_const
      (measurable_matrix_cmul hz hN))
  have hPiS : Measurable fun y : ProbedPath W np × ℝ =>
      farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ y.1.1) *
        scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ y.1.1 :=
    measurable_matrix_mul' (measurable_farEmbed ((measurable_closingPairing b E h _).comp hω)) hS
  have hZ := measurable_matrix_cmul hz (measurable_matrix_mul' hinv hPiS)
  exact measurable_l2_col (measurable_matrix_mul' (measurable_matrix_mul'
    (measurable_matrix_mul' measurable_const hS) hZ)
    ((measurable_probeFrame b E W _ τ m).comp measurable_fst)) j

/-- AM–GM with weight: `ad ≤ (λ/2)a² + (1/(2λ))d²`. -/
theorem mul_le_amgm {l : ℝ} (hl : 0 < l) (a d : ℝ) :
    a * d ≤ l / 2 * a ^ 2 + 1 / (2 * l) * d ^ 2 := by
  rw [← sub_nonneg]
  have e : l / 2 * a ^ 2 + 1 / (2 * l) * d ^ 2 - a * d = (l * a - d) ^ 2 / (2 * l) := by
    field_simp
    ring
  rw [e]
  positivity

/-- The weighted pointwise bound. -/
theorem six_le {l : ℝ} (hl : 0 < l) (ai ak di dk ei ek : ℝ) :
    (ai * dk + di * ak + di * dk) + (ai * ek + ei * ak + ei * ek) ≤
      l * (ai ^ 2 + ak ^ 2) + (1 / l + 1) * (di ^ 2 + dk ^ 2 + ei ^ 2 + ek ^ 2) := by
  have h1 := mul_le_amgm hl ai dk
  have h2 := mul_le_amgm hl ak di
  have h3 := mul_le_amgm hl ai ek
  have h4 := mul_le_amgm hl ak ei
  have h5 : di * dk ≤ (di ^ 2 + dk ^ 2) / 2 := by nlinarith [sq_nonneg (di - dk)]
  have h6 : ei * ek ≤ (ei ^ 2 + ek ^ 2) / 2 := by nlinarith [sq_nonneg (ei - ek)]
  have hl' : 1 / (2 * l) ≤ 1 / l := by
    rw [div_le_div_iff₀ (by positivity) hl]
    linarith
  have hD : 0 ≤ di ^ 2 + dk ^ 2 + ei ^ 2 + ek ^ 2 := by positivity
  have e1 : di * ak = ak * di := mul_comm _ _
  have e2 : ei * ak = ak * ei := mul_comm _ _
  nlinarith [mul_le_mul_of_nonneg_right hl' (sq_nonneg di),
    mul_le_mul_of_nonneg_right hl' (sq_nonneg dk), mul_le_mul_of_nonneg_right hl' (sq_nonneg ei),
    mul_le_mul_of_nonneg_right hl' (sq_nonneg ek)]

/-- `ofReal` of the weighted bound, split. -/
theorem ofReal_six {l c ai ak di dk ei ek : ℝ} (hl : 0 ≤ l) (hc : 0 ≤ c) (hai : 0 ≤ ai)
    (hak : 0 ≤ ak) (hdi : 0 ≤ di) (hdk : 0 ≤ dk) (hei : 0 ≤ ei) (hek : 0 ≤ ek) :
    ENNReal.ofReal (l * (ai + ak) + c * (di + dk + ei + ek)) =
      ENNReal.ofReal l * (ENNReal.ofReal ai + ENNReal.ofReal ak) +
        ENNReal.ofReal c * (ENNReal.ofReal di + ENNReal.ofReal dk + ENNReal.ofReal ei +
          ENNReal.ofReal ek) := by
  rw [ENNReal.ofReal_add (show 0 ≤ l * (ai + ak) by positivity)
      (show 0 ≤ c * (di + dk + ei + ek) by positivity),
    ENNReal.ofReal_mul hl, ENNReal.ofReal_mul hc, ENNReal.ofReal_add hai hak,
    ENNReal.ofReal_add (show 0 ≤ di + dk + ei by positivity) hek,
    ENNReal.ofReal_add (show 0 ≤ di + dk by positivity) hei, ENNReal.ofReal_add hdi hdk]

/-- `a.e.` on the joint sample from `a.e.` on the growth path. -/
theorem ae_joint_of_ae {b : ℝ} {p : GrowthPath W → Prop} (hp : ∀ᵐ ω ∂growthPathLaw W b, p ω) :
    ∀ᵐ y ∂((probedPathLaw W np b).prod phaseLaw), p y.1.1 := by
  have h1 : ∀ᵐ x ∂probedPathLaw W np b, p x.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)
      (ν := Measure.pi fun _ : Fin np => circularVectorLaw (Fin W))).ae hp
  exact (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw W np b) (ν := phaseLaw)).ae h1

theorem ae_probed_of_ae {b : ℝ} {p : GrowthPath W → Prop} (hp : ∀ᵐ ω ∂growthPathLaw W b, p ω) :
    ∀ᵐ x ∂probedPathLaw W np b, p x.1 :=
  (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)
    (ν := Measure.pi fun _ : Fin np => circularVectorLaw (Fin W))).ae hp

section SupNorm

attribute [local instance] Matrix.normedAddCommGroup

theorem norm_entry_le_sourceDataMoment_one (y : SourceData np) (r : Fin 4) (i j : Fin np) :
    ‖y r i j‖ ≤ sourceDataMoment 1 y :=
  (Matrix.norm_entry_le_entrywise_sup_norm (y r)).trans
    ((norm_le_pi_norm y r).trans (norm_le_sourceDataMoment_one y))

end SupNorm

/-- **Moments of `a_j²`**: bounded for all large `W`. -/
theorem lintegral_colA_le (hR : RawTagMoments) {b E : ℝ} {τ m : Fin np → ℝ} {T : ℝ}
    (hD : ComplexSourceLawDomain b E τ m T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ W₀ : ℕ, ∀ W, W₀ ≤ W → ∀ j : Fin np,
      ∫⁻ y, ENNReal.ofReal (colA b E T τ m W j y ^ 2)
        ∂((probedPathLaw W np b).prod phaseLaw) ≤ ENNReal.ofReal B := by
  obtain ⟨hb0, hb1, hE0, hE1, -, -, hm, -⟩ := hD
  set κ := min (2 + E) (2 - E)
  have hκ : 0 < κ := lt_min (by linarith) (by linarith)
  have hEκ : E ∈ bulkInterval κ :=
    ⟨by linarith [min_le_left (2 + E) (2 - E)], by linarith [min_le_right (2 + E) (2 - E)]⟩
  obtain ⟨C, W₀, hC⟩ := hR b hb0 hb1 κ hκ (max T 0) 1 le_rfl
  have hη := Transmission.PassiveCovariance.etaZ_pos b E (by linarith) hE0 hE1
  refine ⟨(momentBound (etaZ b E) 1 C m).toReal, ENNReal.toReal_nonneg, W₀, fun W hW j => ?_⟩
  rw [ENNReal.ofReal_toReal (momentBound_ne_top _ _ _ _)]
  have hmom := lintegral_sourceDataMoment_le b E hη _ τ m hm le_rfl
    (hC W hW E hEκ _ (floor_le_max_mul le_rfl))
  refine (lintegral_prod_le _).trans ?_
  refine le_trans (lintegral_mono fun x => ?_) hmom
  have e : ∀ θ : ℝ, colA b E T τ m W j (x, θ) ^ 2 =
      ‖complexSourceData b E W ⌊(W : ℝ) * T⌋₊ τ m x 1 j j‖ := by
    intro θ
    rw [colA, l2_sq_eq_sum]
    exact (norm_gram_diag (probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x) j).symm
  simp_rw [e]
  rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.ofReal_le_ofReal (norm_entry_le_sourceDataMoment_one _ 1 j j)

/-- `Tr((AU)P(AU)ᴴ) = Tr(A UPUᴴ)` for an orthogonal projection `A`. -/
theorem trace_proj_sandwich {ι κ : Type*} [Fintype ι] [Fintype κ] {A : Matrix ι ι ℂ}
    (hA2 : A * A = A) (hAH : Aᴴ = A) (U : Matrix κ ι ℂ) (P : Matrix κ κ ℂ) :
    ((A * Uᴴ) * P * (A * Uᴴ)ᴴ).trace = (A * (Uᴴ * P * U)).trace := by
  rw [conjTranspose_mul, conjTranspose_conjTranspose, hAH,
    show A * Uᴴ * P * (U * A) = (A * (Uᴴ * P * U)) * A by simp only [Matrix.mul_assoc],
    trace_mul_comm, ← Matrix.mul_assoc, hA2]

/-- **`E d_j² ≤ 2 m_j E Tr(A_- Y_j)/W`**, for all large `W`. -/
theorem lintegral_colD_le {b E s T h : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hs : 0 < s) (hsT : s < T) (hh0 : 0 < h) (hh1 : h < 1) (τ m : Fin np → ℝ)
    (hm : ∀ j, 0 ≤ m j) :
    ∀ᶠ W in atTop, ∀ j : Fin np,
      ∫⁻ y, ENNReal.ofReal (colD b E s T h τ m W j y ^ 2)
          ∂((probedPathLaw W np b).prod phaseLaw) ≤
        ENNReal.ofReal (2 * m j) * ∫⁻ ω, ENNReal.ofReal
          ((farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
            tagResponse b E W ⌊(W : ℝ) * T⌋₊ ⌊(W : ℝ) * τ j⌋₊ ω).trace.re / W)
          ∂growthPathLaw W b := by
  filter_upwards [closedReflection_holds b hb0 hb E hE1 hE2 s T h hs hsT hh0 hh1,
    eventually_ae_phaseAvg_physClosingDefect hb0 hb hE1 hE2 hs hsT hh0 hh1] with W hN hD j
  have hae := ae_probed_of_ae (np := np) (hN.and hD)
  calc ∫⁻ y, ENNReal.ofReal (colD b E s T h τ m W j y ^ 2) ∂((probedPathLaw W np b).prod phaseLaw)
      ≤ ∫⁻ x, ∫⁻ θ, ENNReal.ofReal (colD b E s T h τ m W j (x, θ) ^ 2) ∂phaseLaw
          ∂probedPathLaw W np b := lintegral_prod_le _
    _ ≤ ∫⁻ x, ENNReal.ofReal (2 * l2 (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ x.1) *ᵥ
          (probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ j) ^ 2) ∂probedPathLaw W np b := by
        refine lintegral_mono_ae (hae.mono fun x hx => le_of_eq ?_)
        have e : ∀ θ : ℝ, colD b E s T h τ m W j (x, θ) =
            l2 ((physClosingMap b E s T h W x.1 (phase θ) - 1)ᴴ *ᵥ
              (probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ j) := by
          intro θ
          rw [colD, ← mul_transpose_apply_eq, conjTranspose_sub, conjTranspose_one,
            Matrix.sub_mul, Matrix.one_mul]
          rfl
        simp_rw [e]
        exact lintegral_phase_defect hx.1 hx.2 _
    _ ≤ ∫⁻ ω, ∫⁻ g, ENNReal.ofReal (2 * l2 (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *ᵥ
          (probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m (ω, g))ᵀ j) ^ 2)
          ∂(Measure.pi fun _ : Fin np => circularVectorLaw (Fin W)) ∂growthPathLaw W b :=
        lintegral_prod_le (μ := growthPathLaw W b)
          (ν := Measure.pi fun _ : Fin np => circularVectorLaw (Fin W)) _
    _ = ∫⁻ ω, ENNReal.ofReal (2 * m j) * ENNReal.ofReal
          ((farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
            tagResponse b E W ⌊(W : ℝ) * T⌋₊ ⌊(W : ℝ) * τ j⌋₊ ω).trace.re / W)
          ∂growthPathLaw W b := by
        refine lintegral_congr fun ω => ?_
        have e : ∀ g : Fin np → Fin W → ℂ,
            l2 (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *ᵥ
              (probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m (ω, g))ᵀ j) =
            l2 ((farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
              (boundaryToInterior b E W ⌊(W : ℝ) * T⌋₊ ω)ᴴ) *ᵥ
              (probeColumns W ⌊(W : ℝ) * T⌋₊ τ m g)ᵀ j) := by
          intro g
          rw [probeFrame, mul_transpose_apply_eq, mulVec_mulVec]
        simp_rw [e]
        conv_lhs => arg 2; ext g; rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_probe_col _ τ m j (hm j),
          ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num),
          ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * m j by linarith [hm j]),
          trace_proj_sandwich (by rw [farEmbed_mul, omittedProj_mul_self])
            (by rw [farEmbed_conjTranspose, omittedProj_conjTranspose])]
        congr 1
        rw [tagResponse]
        ring
    _ = ENNReal.ofReal (2 * m j) * ∫⁻ ω, ENNReal.ofReal
          ((farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
            tagResponse b E W ⌊(W : ℝ) * T⌋₊ ⌊(W : ℝ) * τ j⌋₊ ω).trace.re / W)
          ∂growthPathLaw W b := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **`E e_j² ≤ m_j E Tr(A_+ 𝕊Y_j𝕊ᴴ)/W`**, for all large `W`. -/
theorem lintegral_colE_le {b E s T h : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hs : 0 < s) (hsT : s < T) (hh0 : 0 < h) (hh1 : h < 1) (τ m : Fin np → ℝ)
    (hm : ∀ j, 0 ≤ m j) :
    ∀ᶠ W in atTop, ∀ j : Fin np,
      ∫⁻ y, ENNReal.ofReal (colE b E s T h τ m W j y ^ 2)
          ∂((probedPathLaw W np b).prod phaseLaw) ≤
        ENNReal.ofReal (m j) * ∫⁻ ω, ENNReal.ofReal
          ((farEmbed ((closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω)ᴴ *
              closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω) *
            scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω *
            tagResponse b E W ⌊(W : ℝ) * T⌋₊ ⌊(W : ℝ) * τ j⌋₊ ω *
            (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω)ᴴ).trace.re / W)
          ∂growthPathLaw W b := by
  have hh2 : h ^ 2 < 1 := by nlinarith
  filter_upwards [closedReflection_holds b hb0 hb E hE1 hE2 s T h hs hsT hh0 hh1] with W hN j
  have hae := ae_probed_of_ae (np := np) ((ae_growth_isHermitian W b).and hN)
  calc ∫⁻ y, ENNReal.ofReal (colE b E s T h τ m W j y ^ 2) ∂((probedPathLaw W np b).prod phaseLaw)
      ≤ ∫⁻ x, ∫⁻ θ, ENNReal.ofReal (colE b E s T h τ m W j (x, θ) ^ 2) ∂phaseLaw
          ∂probedPathLaw W np b := lintegral_prod_le _
    _ ≤ ∫⁻ x, ENNReal.ofReal (l2 (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ x.1) *ᵥ
          (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1 *ᵥ
            (probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ j)) ^ 2) ∂probedPathLaw W np b := by
        refine lintegral_mono_ae (hae.mono fun x hx => ?_)
        have e : ∀ θ : ℝ, colE b E s T h τ m W j (x, θ) =
            l2 (nearProjection W *ᵥ (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1 *ᵥ
              (closingZ (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1)
                (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ x.1))
                (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ x.1)) (phase θ) *ᵥ
              (probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ j))) := by
          intro θ
          rw [colE, mul_transpose_apply_eq, ← mulVec_mulVec, ← mulVec_mulVec]
        simp_rw [e]
        exact lintegral_phase_cavity hh2 (conjTranspose_mul_scattering b E _ x.1 hx.1) hx.2 _
    _ ≤ ∫⁻ ω, ∫⁻ g, ENNReal.ofReal (l2 (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω) *ᵥ
          (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω *ᵥ
            (probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m (ω, g))ᵀ j)) ^ 2)
          ∂(Measure.pi fun _ : Fin np => circularVectorLaw (Fin W)) ∂growthPathLaw W b :=
        lintegral_prod_le (μ := growthPathLaw W b)
          (ν := Measure.pi fun _ : Fin np => circularVectorLaw (Fin W)) _
    _ = ∫⁻ ω, ENNReal.ofReal (m j) * ENNReal.ofReal
          ((farEmbed ((closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω)ᴴ *
              closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω) *
            scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω *
            tagResponse b E W ⌊(W : ℝ) * T⌋₊ ⌊(W : ℝ) * τ j⌋₊ ω *
            (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω)ᴴ).trace.re / W)
          ∂growthPathLaw W b := by
        refine lintegral_congr fun ω => ?_
        set Pi := farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω) with hPi
        set S := scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω with hS
        set U := boundaryToInterior b E W ⌊(W : ℝ) * T⌋₊ ω with hU
        have e : ∀ g : Fin np → Fin W → ℂ,
            l2 (Pi *ᵥ (S *ᵥ (probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m (ω, g))ᵀ j)) =
            l2 ((Pi * S * Uᴴ) *ᵥ (probeColumns W ⌊(W : ℝ) * T⌋₊ τ m g)ᵀ j) := by
          intro g
          rw [probeFrame, mul_transpose_apply_eq, mulVec_mulVec, mulVec_mulVec]
        simp_rw [e]
        rw [lintegral_probe_col _ τ m j (hm j), ← ENNReal.ofReal_mul (hm j)]
        congr 1
        have e1 : Pi * S * Uᴴ * tagProjection W ⌊(W : ℝ) * T⌋₊ ⌊(W : ℝ) * τ j⌋₊ *
            (Pi * S * Uᴴ)ᴴ =
            (Pi * (S * (Uᴴ * tagProjection W ⌊(W : ℝ) * T⌋₊ ⌊(W : ℝ) * τ j⌋₊ * U) * Sᴴ)) *
              Piᴴ := by
          rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
          simp only [Matrix.mul_assoc]
        have e2 : (farEmbed ((closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω)ᴴ *
              closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω) * S *
            tagResponse b E W ⌊(W : ℝ) * T⌋₊ ⌊(W : ℝ) * τ j⌋₊ ω * Sᴴ).trace =
            (Piᴴ * (Pi * (S * (Uᴴ * tagProjection W ⌊(W : ℝ) * T⌋₊ ⌊(W : ℝ) * τ j⌋₊ * U) *
              Sᴴ))).trace := by
          rw [hPi, farEmbed_conjTranspose, ← Matrix.mul_assoc, farEmbed_mul, tagResponse]
          simp only [Matrix.mul_assoc]
          rfl
        rw [e1, trace_mul_comm, ← e2]
        ring
    _ = ENNReal.ofReal (m j) * ∫⁻ ω, ENNReal.ofReal
          ((farEmbed ((closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω)ᴴ *
              closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω) *
            scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω *
            tagResponse b E W ⌊(W : ℝ) * T⌋₊ ⌊(W : ℝ) * τ j⌋₊ ω *
            (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω)ᴴ).trace.re / W)
          ∂growthPathLaw W b := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **`GramClosingSmall` from the raw tag moments and the two leakages.** -/
theorem gramClosingSmall_of_raw (hR : RawTagMoments) (hL : TagChannelLeakage)
    (hLo : TagChannelLeakageOut) : GramClosingSmall := by
  intro b E np τ m T hD s hs hτ r hr i k ε hε
  obtain ⟨B, hB0, W₀, hA⟩ := lintegral_colA_le hR hD
  obtain ⟨hb0, hb1, hE1, hE2, -, -, hm, hτT⟩ := hD
  have hsT : s < T := (hτ i).trans (hτT i)
  set l : ℝ := ε / (4 * (B + 1)) with hl
  have hl0 : 0 < l := by positivity
  set c : ℝ := 1 / l + 1 with hc
  have hc0 : 0 < c := by positivity
  set M : ℝ := m i + m k + 1 with hMdef
  have hM0 : 0 < M := by linarith [hm i, hm k]
  set δ : ℝ := ε / (2 * c * (6 * M)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hlt : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < 1 := nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
  filter_upwards [hL b hb0 hb1 E hE1 hE2 s (τ i) T hs (hτ i) (hτT i) δ hδ0,
    hL b hb0 hb1 E hE1 hE2 s (τ k) T hs (hτ k) (hτT k) δ hδ0,
    hLo b hb0 hb1 E hE1 hE2 s (τ i) T hs (hτ i) (hτT i) δ hδ0,
    hLo b hb0 hb1 E hE1 hE2 s (τ k) T hs (hτ k) (hτT k) δ hδ0, hlt, self_mem_nhdsWithin]
    with h hLi hLk hOi hOk hh1 hh0
  have hh0' : (0 : ℝ) < h := hh0
  have hh2 : h ^ 2 < 1 := by nlinarith
  filter_upwards [hLi, hLk, hOi, hOk, eventually_ge_atTop W₀,
    closedReflection_holds b hb0 hb1 E hE1 hE2 s T h hs hsT hh0' hh1,
    lintegral_colD_le (np := np) hb0 hb1 hE1 hE2 hs hsT hh0' hh1 τ m hm,
    lintegral_colE_le (np := np) hb0 hb1 hE1 hE2 hs hsT hh0' hh1 τ m hm]
    with W hWi hWk hWOi hWOk hW0 hWN hWD hWE
  have hAi : Measurable fun y => ENNReal.ofReal (colA b E T τ m W i y ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_colA b E T τ m W i).pow_const 2)
  have hAk : Measurable fun y => ENNReal.ofReal (colA b E T τ m W k y ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_colA b E T τ m W k).pow_const 2)
  have hDi : Measurable fun y => ENNReal.ofReal (colD b E s T h τ m W i y ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_colD b E s T h τ m W i).pow_const 2)
  have hDk : Measurable fun y => ENNReal.ofReal (colD b E s T h τ m W k y ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_colD b E s T h τ m W k).pow_const 2)
  have hEi : Measurable fun y => ENNReal.ofReal (colE b E s T h τ m W i y ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_colE b E s T h τ m W i).pow_const 2)
  have hEk : Measurable fun y => ENNReal.ofReal (colE b E s T h τ m W k y ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_colE b E s T h τ m W k).pow_const 2)
  have hae : ∀ᵐ y ∂((probedPathLaw W np b).prod phaseLaw),
      ENNReal.ofReal ‖closedSourceData b E s T h τ m W (phase y.2) y.1 r i k -
          complexSourceData b E W ⌊(W : ℝ) * T⌋₊ τ m y.1 r i k‖ ≤
        ENNReal.ofReal l * (ENNReal.ofReal (colA b E T τ m W i y ^ 2) +
            ENNReal.ofReal (colA b E T τ m W k y ^ 2)) +
          ENNReal.ofReal c * (ENNReal.ofReal (colD b E s T h τ m W i y ^ 2) +
            ENNReal.ofReal (colD b E s T h τ m W k y ^ 2) +
            ENNReal.ofReal (colE b E s T h τ m W i y ^ 2) +
            ENNReal.ofReal (colE b E s T h τ m W k y ^ 2)) := by
    filter_upwards [ae_joint_of_ae (np := np) ((ae_growth_isHermitian W b).and hWN)] with y hy
    have hH : ClosingHyp b E h ⌊(W : ℝ) * s⌋₊ ⌊(W : ℝ) * T⌋₊ y.1.1 (phase y.2) :=
      ⟨scattering_mul_conjTranspose b E _ y.1.1 hy.1,
        conjTranspose_mul_scattering b E _ y.1.1 hy.1, hh2,
        isUnit_det_of_tendsto hy.2 (norm_phase _), phase_mul_star _⟩
    have h6 := gramErr_le b E s T h τ m y.1 (phase y.2) hH r hr i k
    rw [← ofReal_six hl0.le hc0.le (sq_nonneg _) (sq_nonneg _) (sq_nonneg _) (sq_nonneg _)
      (sq_nonneg _) (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (h6.trans ?_)
    exact six_le hl0 _ _ _ _ _ _
  refine (lintegral_mono_ae hae).trans ?_
  have hA2 : Measurable fun y => ENNReal.ofReal (colA b E T τ m W i y ^ 2) +
      ENNReal.ofReal (colA b E T τ m W k y ^ 2) := hAi.add hAk
  have hAll : Measurable fun y => ENNReal.ofReal l * (ENNReal.ofReal (colA b E T τ m W i y ^ 2) +
      ENNReal.ofReal (colA b E T τ m W k y ^ 2)) := hA2.const_mul _
  have hD2 : Measurable fun y => ENNReal.ofReal (colD b E s T h τ m W i y ^ 2) +
      ENNReal.ofReal (colD b E s T h τ m W k y ^ 2) := hDi.add hDk
  have hD3 : Measurable fun y => ENNReal.ofReal (colD b E s T h τ m W i y ^ 2) +
      ENNReal.ofReal (colD b E s T h τ m W k y ^ 2) +
      ENNReal.ofReal (colE b E s T h τ m W i y ^ 2) := hD2.add hEi
  have hD4 : Measurable fun y => ENNReal.ofReal (colD b E s T h τ m W i y ^ 2) +
      ENNReal.ofReal (colD b E s T h τ m W k y ^ 2) +
      ENNReal.ofReal (colE b E s T h τ m W i y ^ 2) +
      ENNReal.ofReal (colE b E s T h τ m W k y ^ 2) := hD3.add hEk
  rw [lintegral_add_left hAll, lintegral_const_mul _ hA2, lintegral_const_mul _ hD4,
    lintegral_add_left hAi, lintegral_add_left hD3, lintegral_add_left hD2,
    lintegral_add_left hDi]
  have hmi := hm i
  have hmk := hm k
  calc ENNReal.ofReal l * (∫⁻ y, ENNReal.ofReal (colA b E T τ m W i y ^ 2)
          ∂((probedPathLaw W np b).prod phaseLaw) +
        ∫⁻ y, ENNReal.ofReal (colA b E T τ m W k y ^ 2) ∂((probedPathLaw W np b).prod phaseLaw)) +
      ENNReal.ofReal c * (∫⁻ y, ENNReal.ofReal (colD b E s T h τ m W i y ^ 2)
          ∂((probedPathLaw W np b).prod phaseLaw) +
        ∫⁻ y, ENNReal.ofReal (colD b E s T h τ m W k y ^ 2)
          ∂((probedPathLaw W np b).prod phaseLaw) +
        ∫⁻ y, ENNReal.ofReal (colE b E s T h τ m W i y ^ 2)
          ∂((probedPathLaw W np b).prod phaseLaw) +
        ∫⁻ y, ENNReal.ofReal (colE b E s T h τ m W k y ^ 2)
          ∂((probedPathLaw W np b).prod phaseLaw))
      ≤ ENNReal.ofReal l * (ENNReal.ofReal B + ENNReal.ofReal B) +
        ENNReal.ofReal c * (ENNReal.ofReal (2 * m i) * ENNReal.ofReal δ +
          ENNReal.ofReal (2 * m k) * ENNReal.ofReal δ + ENNReal.ofReal (m i) * ENNReal.ofReal δ +
          ENNReal.ofReal (m k) * ENNReal.ofReal δ) := by
        refine add_le_add (mul_le_mul_right (add_le_add (hA W hW0 i) (hA W hW0 k)) _)
          (mul_le_mul_right (add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_) _)
        · exact (hWD i).trans (mul_le_mul_right hWi _)
        · exact (hWD k).trans (mul_le_mul_right hWk _)
        · exact (hWE i).trans (mul_le_mul_right hWOi _)
        · exact (hWE k).trans (mul_le_mul_right hWOk _)
    _ = ENNReal.ofReal (l * (B + B) +
          c * (2 * m i * δ + 2 * m k * δ + m i * δ + m k * δ)) := by
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * m i by linarith),
          ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * m k by linarith),
          ← ENNReal.ofReal_mul hmi, ← ENNReal.ofReal_mul hmk,
          ← ENNReal.ofReal_add hB0 hB0, ← ENNReal.ofReal_mul hl0.le,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hc0.le,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ε := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : l * (B + B) ≤ ε / 2 := by
          rw [hl, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        have h2 : c * δ * (6 * M) = ε / 2 := by
          rw [hδ]
          field_simp
        have h3 : c * (2 * m i * δ + 2 * m k * δ + m i * δ + m k * δ) ≤ c * δ * (6 * M) := by
          have : 2 * m i * δ + 2 * m k * δ + m i * δ + m k * δ ≤ δ * (6 * M) := by
            rw [hMdef]
            nlinarith
          nlinarith
        linarith

/-- **`TargetT3`.** -/
theorem t3 : TargetT3 := fun hMT hGA hSR hLp _ hL hLo =>
  gramClosingSmall_of_raw (RawTag.rawTagMoments_holds hGA hLp hSR hMT) hL hLo

end BlockBand.SourceProcess.PhysApprox
