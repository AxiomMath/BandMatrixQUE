module

public import BlockBand.SourceProcess.PhysApprox.B3BirthKSubBirth
public import BlockBand.SourceProcess.PhysApprox.B3ClosedForm
public import BlockBand.SourceProcess.PhysApprox.B3CovRepKCond
public import BlockBand.SourceProcess.PhysApprox.B3BirthClose
public import BlockBand.SourceProcess.TagBirth.Main

/-!
# The closed `𝒦` cross entries at a birth step

`complexBirthCrossK_holds`: under `GaussianAbsorptionContract`, the estimate `ComplexBirthCrossK`
holds, directly on the closed law. By the closed birth form, an old/new entry is `u_k*(K𝒢)(c g)` and
a new/old entry is `(c g)*(𝒢K)v_{k'}`; averaging over the newborn probe `g` and bounding the fresh
factors `1 + ΔR_cl`, `1 + R_clΔ` in mean gives a bound `O(√(m/W))`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosingLeak BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.PhysApprox.ClosedForm BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.ClosingAux
open scoped NNReal ENNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

variable {W np : ℕ}

namespace BirthKSub

/-!
## Tonelli over the newborn probe
-/

/-- **Averaging over one probe** under the closed law: if `f ≤ Φ((ω, θ), g_i, g_k)` a.e. and the
`g_i`-average of `Φ` is at most `D(ω, θ)`, then `E f ≤ E D`. -/
theorem lintegral_closed_pair_le {b : ℝ} {i k : Fin np} (hik : i ≠ k)
    {f : ProbedPath W np × ℝ → ℝ≥0∞}
    {Φ : GrowthPath W × ℝ → (Fin W → ℂ) → (Fin W → ℂ) → ℝ≥0∞} {D : GrowthPath W × ℝ → ℝ≥0∞}
    (hf : ∀ᵐ y ∂closedLaw b W np, f y ≤ Φ (y.1.1, y.2) (y.1.2 i) (y.1.2 k))
    (hΦ : Measurable fun q : (GrowthPath W × ℝ) × ((Fin W → ℂ) × (Fin W → ℂ)) =>
      Φ q.1 q.2.1 q.2.2)
    (hin : ∀ p h, ∫⁻ g, Φ p g h ∂circularVectorLaw (Fin W) ≤ D p) (hD : Measurable D) :
    ∫⁻ y, f y ∂closedLaw b W np ≤ ∫⁻ y, D (y.1.1, y.2) ∂closedLaw b W np := by
  refine (lintegral_mono_ae hf).trans ?_
  have hpair : Measurable fun G : Fin np → Fin W → ℂ => (G i, G k) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply k)
  have hF : Measurable fun y : ProbedPath W np × ℝ => Φ (y.1.1, y.2) (y.1.2 i) (y.1.2 k) :=
    hΦ.comp (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (hpair.comp (measurable_snd.comp measurable_fst)))
  have hDy : Measurable fun y : ProbedPath W np × ℝ => D (y.1.1, y.2) :=
    hD.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  rw [closedLaw, lintegral_prod _ hF.aemeasurable, lintegral_prod _ hDy.aemeasurable,
    probedPathLaw, lintegral_prod _ hF.lintegral_prod_right'.aemeasurable,
    lintegral_prod _ hDy.lintegral_prod_right'.aemeasurable]
  refine lintegral_mono fun ω => ?_
  have hG : ∀ θ : ℝ, Measurable fun G : Fin np → Fin W → ℂ => Φ (ω, θ) (G i) (G k) := fun θ =>
    hΦ.comp (measurable_const.prodMk hpair)
  have hsw : Measurable (Function.uncurry fun (G : Fin np → Fin W → ℂ) (θ : ℝ) =>
      Φ (ω, θ) (G i) (G k)) :=
    hΦ.comp ((measurable_const.prodMk measurable_snd).prodMk (hpair.comp measurable_fst))
  dsimp only
  rw [lintegral_lintegral_swap hsw.aemeasurable]
  calc ∫⁻ θ, ∫⁻ G, Φ (ω, θ) (G i) (G k) ∂Measure.pi (fun _ : Fin np => circularVectorLaw (Fin W))
        ∂phaseLaw
      ≤ ∫⁻ θ, D (ω, θ) ∂phaseLaw := by
        refine lintegral_mono fun θ => ?_
        have hΦp : Measurable fun p : (Fin W → ℂ) × (Fin W → ℂ) => Φ (ω, θ) p.1 p.2 :=
          hΦ.comp (measurable_const.prodMk measurable_id)
        have e : ∫⁻ G, Φ (ω, θ) (G i) (G k) ∂Measure.pi (fun _ : Fin np =>
            circularVectorLaw (Fin W)) = ∫⁻ p, Φ (ω, θ) p.1 p.2
              ∂(circularVectorLaw (Fin W)).prod (circularVectorLaw (Fin W)) := by
          rw [← pi_map_pair (circularVectorLaw (Fin W)) hik, lintegral_map hΦp hpair]
        rw [e, lintegral_prod_symm _ hΦp.aemeasurable]
        calc ∫⁻ h, ∫⁻ g, Φ (ω, θ) g h ∂circularVectorLaw (Fin W) ∂circularVectorLaw (Fin W)
            ≤ ∫⁻ _h, D (ω, θ) ∂circularVectorLaw (Fin W) := lintegral_mono fun h => hin _ h
          _ = D (ω, θ) := by rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ G, ∫⁻ θ, D (ω, θ) ∂phaseLaw ∂Measure.pi (fun _ : Fin np => circularVectorLaw (Fin W)) :=
        by rw [lintegral_const, measure_univ, mul_one]

/-!
## Norms and measurability
-/

theorem measurable_vecNorm : Measurable (vecNorm : (Fin W → ℂ) → ℝ) :=
  continuous_l2.measurable

theorem norm_one_le_one : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 :=
  BlockBand.Transmission.PassiveCovariance.opNorm_le_of_vec _ zero_le_one fun x => by
    rw [one_mulVec, one_mul]

/-- `‖1 + AB‖ ≤ 1 + ‖A‖‖B‖`. -/
theorem norm_one_add_mul_le (A B : Matrix (Fin W) (Fin W) ℂ) : ‖1 + A * B‖ ≤ 1 + ‖A‖ * ‖B‖ :=
  (norm_add_le _ _).trans (add_le_add norm_one_le_one (norm_mul_le _ _))

theorem measurable_bilinear_gen {α : Type*} [MeasurableSpace α] {u v : α → Fin W → ℂ}
    {M : α → Matrix (Fin W) (Fin W) ℂ} (hu : Measurable u) (hM : Measurable M)
    (hv : Measurable v) : Measurable fun a => bilinear (u a) (M a) (v a) := by
  simp only [bilinear, dotProduct, mulVec, Pi.star_apply]
  exact Finset.measurable_sum _ fun x _ =>
    (Complex.continuous_conj.measurable.comp ((measurable_pi_apply x).comp hu)).mul
      (Finset.measurable_sum _ fun y _ => hM.eval_matrix.mul ((measurable_pi_apply y).comp hv))

/-- `E_g|u*Mg| ≤ ‖Mᴴu‖`. -/
theorem lintegral_bilinear_right_le (M : Matrix (Fin W) (Fin W) ℂ) (u : Fin W → ℂ) :
    ∫⁻ g, ‖bilinear u M g‖ₑ ∂circularVectorLaw (Fin W) ≤ ENNReal.ofReal (vecNorm (Mᴴ *ᵥ u)) := by
  have e : ∀ g : Fin W → ℂ, bilinear u M g = ∑ a, star ((Mᴴ *ᵥ u) a) * g a := by
    intro g
    have hs : star u ᵥ* M = star (Mᴴ *ᵥ u) := by rw [star_mulVec, conjTranspose_conjTranspose]
    rw [bilinear, dotProduct_mulVec, hs]
    simp only [dotProduct, Pi.star_apply]
  simp_rw [e]
  refine (BirthP.lintegral_lin_le _).trans (le_of_eq ?_)
  simp only [norm_star, vecNorm]

/-- The input `X_cl` at `(ω, θ)`. -/
def xcl (b E s h : ℝ) (W j : ℕ) (p : GrowthPath W × ℝ) : Matrix (Fin W) (Fin W) ℂ :=
  closedNearX b E s h W j p.1 (phase p.2)

/-- `Δ(X_cl, F_j)` at `(ω, θ)`. -/
def dcl (b E s h : ℝ) (W j : ℕ) (p : GrowthPath W × ℝ) : Matrix (Fin W) (Fin W) ℂ :=
  freshDelta b E (xcl b E s h W j p) (freshSample W j p.1)

theorem measurable_xcl (b E s h : ℝ) (W j : ℕ) : Measurable (xcl b E s h W j) := by
  have hR : Measurable fun p : GrowthPath W × ℝ => closedNearR b E s h W j p.1 (phase p.2) :=
    measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_mul' measurable_const
      (measurable_boundaryResolvent_comp b E j measurable_fst))
      (measurable_physClosingMapAt_comp b E s h j measurable_fst
        (measurable_phase.comp measurable_snd))) measurable_const
  unfold xcl closedNearX
  exact measurable_matrix_sub measurable_const (measurable_matrix_inv.comp hR)

theorem measurable_dcl (b E s h : ℝ) (W j : ℕ) : Measurable (dcl b E s h W j) :=
  BlockBand.SourceProcess.FullSource.measurable_freshDelta_comp b E (measurable_xcl b E s h W j)
    ((measurable_freshSample W j).comp measurable_fst)

theorem measurable_rcl (b E s h : ℝ) (W j : ℕ) :
    Measurable fun p => passiveResolvent b E (xcl b E s h W j p) := by
  unfold passiveResolvent
  exact measurable_matrix_inv.comp (measurable_matrix_sub measurable_const
    (measurable_xcl b E s h W j))

/-- A closed near frame depends on its own probe only. -/
def onProbe {np : ℕ} (p : GrowthPath W × ℝ) (v : Fin W → ℂ) : ProbedPath W np × ℝ :=
  ((p.1, fun _ => v), p.2)

theorem measurable_onProbe {np : ℕ} :
    Measurable fun q : (GrowthPath W × ℝ) × ((Fin W → ℂ) × (Fin W → ℂ)) =>
      (onProbe (np := np) q.1 q.2.2 : ProbedPath W np × ℝ) :=
  ((measurable_fst.comp measurable_fst).prodMk (Measurable.of_eval fun _ =>
    measurable_snd.comp measurable_snd)).prodMk (measurable_snd.comp measurable_fst)

theorem probeCol_onProbe (b E : ℝ) (τ m : Fin np → ℝ) (j : ℕ) (k : Fin np)
    (y : ProbedPath W np × ℝ) :
    probeCol b E τ m W j k (onProbe (y.1.1, y.2) (y.1.2 k)).1 = probeCol b E τ m W j k y.1 := by
  funext x
  simp [probeCol, probeFrame, Matrix.mul_apply, probeColumns, onProbe]

theorem closedNearU_onProbe (b E s h : ℝ) (τ m : Fin np → ℝ) (j : ℕ) (k : Fin np)
    (y : ProbedPath W np × ℝ) :
    closedNearU b E s h τ m W j k (onProbe (y.1.1, y.2) (y.1.2 k)) =
      closedNearU b E s h τ m W j k y := by
  simp only [closedNearU, probeCol_onProbe]
  rfl

theorem closedNearV_onProbe (b E s h : ℝ) (τ m : Fin np → ℝ) (j : ℕ) (k : Fin np)
    (y : ProbedPath W np × ℝ) :
    closedNearV b E s h τ m W j k (onProbe (y.1.1, y.2) (y.1.2 k)) =
      closedNearV b E s h τ m W j k y := by
  simp only [closedNearV, probeCol_onProbe]
  rfl

/-- The two fresh factors `1 + ΔR_cl` and `1 + R_clΔ` at `(ω, θ)`. -/
def mOld (b E s h : ℝ) (W j : ℕ) (p : GrowthPath W × ℝ) : Matrix (Fin W) (Fin W) ℂ :=
  1 + dcl b E s h W j p * passiveResolvent b E (xcl b E s h W j p)

def mNew (b E s h : ℝ) (W j : ℕ) (p : GrowthPath W × ℝ) : Matrix (Fin W) (Fin W) ℂ :=
  1 + passiveResolvent b E (xcl b E s h W j p) * dcl b E s h W j p

theorem measurable_mOld (b E s h : ℝ) (W j : ℕ) : Measurable (mOld b E s h W j) :=
  measurable_matrix_add measurable_const
    (measurable_matrix_mul' (measurable_dcl b E s h W j) (measurable_rcl b E s h W j))

theorem measurable_mNew (b E s h : ℝ) (W j : ℕ) : Measurable (mNew b E s h W j) :=
  measurable_matrix_add measurable_const
    (measurable_matrix_mul' (measurable_rcl b E s h W j) (measurable_dcl b E s h W j))

theorem bilinear_smul_right (u : Fin W → ℂ) (M : Matrix (Fin W) (Fin W) ℂ) (c : ℝ)
    (v : Fin W → ℂ) : bilinear u M ((c : ℂ) • v) = (c : ℂ) * bilinear u M v := by
  rw [bilinear, bilinear, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem bilinear_smul_left (u : Fin W → ℂ) (M : Matrix (Fin W) (Fin W) ℂ) (c : ℝ)
    (v : Fin W → ℂ) : bilinear ((c : ℂ) • u) M v = (c : ℂ) * bilinear u M v := by
  rw [bilinear, bilinear, star_smul, smul_dotProduct, Complex.star_def, Complex.conj_ofReal,
    smul_eq_mul]

/-- The almost-sure facts at a birth step. -/
theorem ae_birth_good {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (s h : ℝ) (hh : h ^ 2 < 1) (τ m : Fin np → ℝ) (hW : 1 ≤ W) {j : ℕ} (hj : 1 ≤ j) :
    ∀ᵐ y ∂closedLaw b W np, GclSuccBlocks b E s h W j y.1.1 (phase y.2) ∧
      (passiveY (closedNearX b E s h W j y.1.1 (phase y.2))).PosSemidef ∧
      scatteringMatrix b E W j y.1.1 * (scatteringMatrix b E W j y.1.1)ᴴ = 1 ∧
      IsUnit (1 - phase y.2 • closingN (scatteringMatrix b E W j y.1.1)
        (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
        (farEmbed (closingPairing b E h W (closeLen s W) y.1.1))).det := by
  have hη := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  filter_upwards [ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW,
    ae_closedPhase_good (W := W) (np := np) b E s h j,
    ae_passive_b3ClosedX hb0 hb hE1 hE2 s h hh τ m hW j] with y hP hQ hX
  obtain ⟨hA, hF, hBu, hS⟩ := hP
  obtain ⟨h1, h2, h3, h4⟩ := hQ
  have hR := h4.resolve_left (isUnit_closedR0 b E h s j y.1.1 hA hη (hF j)).ne_zero
  exact ⟨gclAt_succ_blocks b E s h hj y.1.1 (phase y.2) hA hη (hF j) (hF (j + 1)) (hBu (j + 1))
    (isUnit_iff_ne_zero.2 h1) (isUnit_iff_ne_zero.2 h2) (isUnit_iff_ne_zero.2 h3)
    (isUnit_iff_ne_zero.2 hR) hX, hX, hS j, isUnit_iff_ne_zero.2 h1⟩

/-!
## The two mixed entries at a birth step
-/

/-- **Old/new**: `E[1_A|𝒦_cl,j+1(a,a')|] ≤ √(m_{a'}/W)√R E‖1 + ΔR_cl‖`. -/
theorem lintegral_birth_old_new_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (s h : ℝ) (hh : h ^ 2 < 1) (τ m : Fin np → ℝ) (R : ℝ) {K : ℕ}
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (hW : 1 ≤ W) {j : ℕ}
    (hj : 1 ≤ j) (hs : closeLen s W ≤ j) {a a' : Fin np} (haa : a ≠ a')
    (ha : ⌊(W : ℝ) * τ a⌋₊ < j) (ha' : ⌊(W : ℝ) * τ a'⌋₊ = j) :
    ∫⁻ y, ‖(b3Alive b E s h τ m R W j Vs).indicator
        (fun y => b3ClosedKAt b E s h τ m W (j + 1) y a a') y‖ₑ ∂closedLaw b W np ≤
      ∫⁻ y, ENNReal.ofReal (Real.sqrt (m a' / W) * Real.sqrt R) *
        ENNReal.ofReal ‖mOld b E s h W j (y.1.1, y.2)‖ ∂closedLaw b W np := by
  have hη := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  set c : ℝ := Real.sqrt (m a' / W)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  set uf : GrowthPath W × ℝ → (Fin W → ℂ) → Fin W → ℂ := fun p v =>
    closedNearU b E s h τ m W j a (onProbe (np := np) p v) with huf
  have hufm : Measurable fun q : (GrowthPath W × ℝ) × ((Fin W → ℂ) × (Fin W → ℂ)) =>
      uf q.1 q.2.2 := (measurable_closedNearU b E s h τ m j a).comp measurable_onProbe
  refine lintegral_closed_pair_le haa.symm
    (Φ := fun p g v => if vecNorm (uf p v) ≤ Real.sqrt R then
      ENNReal.ofReal c * ‖bilinear (uf p v) (mOld b E s h W j p) g‖ₑ else 0)
    (D := fun p => ENNReal.ofReal (c * Real.sqrt R) * ENNReal.ofReal ‖mOld b E s h W j p‖)
    ?_ ?_ ?_ ?_
  · filter_upwards [ae_birth_good (np := np) hb0 hb hE1 hE2 s h hh τ m hW hj] with y hy0
    obtain ⟨hblk, hX, -, -⟩ := hy0
    by_cases hy : y ∈ b3Alive b E s h τ m R W j Vs
    · have hu := norm_closedNearU_le b E s h τ m j Vs a y (hy.2 j hs le_rfl)
      have e : uf (y.1.1, y.2) (y.1.2 a) = closedNearU b E s h τ m W j a y :=
        closedNearU_onProbe b E s h τ m j a y
      rw [Set.indicator_of_mem hy, closedK_birth_old_new b E s h τ m y hblk ha ha',
        (birthK_mul_birthG s h hη y.1.1 (phase y.2) hX).1, e,
        ite_eq_left_of_eq_true _ _ (eq_true hu), bilinear_smul_right,
        enorm_mul, enorm_ofReal_nonneg hc]
      rfl
    · rw [Set.indicator_of_notMem hy, enorm_zero]
      exact zero_le
  · refine Measurable.ite (measurableSet_le
      ((BirthKSub.measurable_vecNorm).comp hufm) measurable_const)
      (measurable_const.mul (measurable_bilinear_gen hufm
        ((measurable_mOld b E s h W j).comp measurable_fst)
        (measurable_fst.comp measurable_snd)).enorm) measurable_const
  · intro p v
    split_ifs with hv
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hc, mul_assoc]
      gcongr
      refine (lintegral_bilinear_right_le _ _).trans ?_
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc vecNorm ((mOld b E s h W j p)ᴴ *ᵥ uf p v)
          ≤ ‖(mOld b E s h W j p)ᴴ‖ * vecNorm (uf p v) :=
            BlockBand.Transmission.PassiveCovariance.vecNorm_mulVec_le _ _
        _ ≤ ‖mOld b E s h W j p‖ * Real.sqrt R := by
            rw [Matrix.l2_opNorm_conjTranspose]
            exact mul_le_mul_of_nonneg_left hv (norm_nonneg _)
        _ = Real.sqrt R * ‖mOld b E s h W j p‖ := mul_comm _ _
    · rw [lintegral_zero]
      exact zero_le
  · exact measurable_const.mul (continuous_norm.measurable.comp
      (measurable_mOld b E s h W j)).ennreal_ofReal

/-- **New/old**: `E[1_A|𝒦_cl,j+1(a,a')|] ≤ √(m_a/W)√R E‖1 + R_clΔ‖`. -/
theorem lintegral_birth_new_old_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (s h : ℝ) (hh : h ^ 2 < 1) (τ m : Fin np → ℝ) (R : ℝ) {K : ℕ}
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (hW : 1 ≤ W) {j : ℕ}
    (hj : 1 ≤ j) (hs : closeLen s W ≤ j) {a a' : Fin np} (haa : a ≠ a')
    (ha : ⌊(W : ℝ) * τ a⌋₊ = j) (ha' : ⌊(W : ℝ) * τ a'⌋₊ < j) :
    ∫⁻ y, ‖(b3Alive b E s h τ m R W j Vs).indicator
        (fun y => b3ClosedKAt b E s h τ m W (j + 1) y a a') y‖ₑ ∂closedLaw b W np ≤
      ∫⁻ y, ENNReal.ofReal (Real.sqrt (m a / W) * Real.sqrt R) *
        ENNReal.ofReal ‖mNew b E s h W j (y.1.1, y.2)‖ ∂closedLaw b W np := by
  have hη := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  set c : ℝ := Real.sqrt (m a / W)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  set vf : GrowthPath W × ℝ → (Fin W → ℂ) → Fin W → ℂ := fun p v =>
    closedNearV b E s h τ m W j a' (onProbe (np := np) p v) with hvf
  have hvfm : Measurable fun q : (GrowthPath W × ℝ) × ((Fin W → ℂ) × (Fin W → ℂ)) =>
      vf q.1 q.2.2 := (measurable_closedNearV b E s h τ m j a').comp measurable_onProbe
  refine lintegral_closed_pair_le haa
    (Φ := fun p g v => if vecNorm (vf p v) ≤ Real.sqrt R then
      ENNReal.ofReal c * ‖bilinear g (mNew b E s h W j p) (vf p v)‖ₑ else 0)
    (D := fun p => ENNReal.ofReal (c * Real.sqrt R) * ENNReal.ofReal ‖mNew b E s h W j p‖)
    ?_ ?_ ?_ ?_
  · filter_upwards [ae_birth_good (np := np) hb0 hb hE1 hE2 s h hh τ m hW hj] with y hy0
    obtain ⟨hblk, hX, hS, hU⟩ := hy0
    by_cases hy : y ∈ b3Alive b E s h τ m R W j Vs
    · have hv := norm_closedNearV_le b E s h hh τ m j Vs a' y hS hU (hy.2 j hs le_rfl)
      have e : vf (y.1.1, y.2) (y.1.2 a') = closedNearV b E s h τ m W j a' y :=
        closedNearV_onProbe b E s h τ m j a' y
      rw [Set.indicator_of_mem hy, closedK_birth_new_old b E s h τ m y hblk ha ha',
        (birthK_mul_birthG s h hη y.1.1 (phase y.2) hX).2, e,
        ite_eq_left_of_eq_true _ _ (eq_true hv), bilinear_smul_left,
        enorm_mul, enorm_ofReal_nonneg hc]
      rfl
    · rw [Set.indicator_of_notMem hy, enorm_zero]
      exact zero_le
  · refine Measurable.ite (measurableSet_le
      ((BirthKSub.measurable_vecNorm).comp hvfm) measurable_const)
      (measurable_const.mul (measurable_bilinear_gen (measurable_fst.comp measurable_snd)
        ((measurable_mNew b E s h W j).comp measurable_fst) hvfm).enorm) measurable_const
  · intro p v
    split_ifs with hv
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hc, mul_assoc]
      gcongr
      refine (lintegral_bilinear_left_le _ _).trans ?_
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc l2 (mNew b E s h W j p *ᵥ vf p v)
          ≤ ‖mNew b E s h W j p‖ * vecNorm (vf p v) :=
            BlockBand.Transmission.PassiveCovariance.vecNorm_mulVec_le _ _
        _ ≤ ‖mNew b E s h W j p‖ * Real.sqrt R :=
            mul_le_mul_of_nonneg_left hv (norm_nonneg _)
        _ = Real.sqrt R * ‖mNew b E s h W j p‖ := mul_comm _ _
    · rw [lintegral_zero]
      exact zero_le
  · exact measurable_const.mul (continuous_norm.measurable.comp
      (measurable_mNew b E s h W j)).ennreal_ofReal

/-!
## The fresh moment
-/

/-- **`E‖1 + ΔR_cl‖, E‖1 + R_clΔ‖ ≤ 1 + C₂/η`** under the closed law (first moment of `Δ`, from
the second, `lintegral_freshDelta_sq_le`; passivity of `X_cl`). -/
theorem lintegral_m_le (hGA : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    ∃ (C₂ : ℝ) (W₀ : ℕ), 0 ≤ C₂ ∧ ∀ W : ℕ, W₀ ≤ W → 1 ≤ W → ∀ (s h : ℝ), h ^ 2 < 1 →
      ∀ (np j : ℕ), closeLen s W ≤ j →
        ∫⁻ y, ENNReal.ofReal ‖mOld b E s h W j (y.1.1, y.2)‖ ∂closedLaw b W np ≤
            ENNReal.ofReal (1 + C₂ / etaZ b E) ∧
          ∫⁻ y, ENNReal.ofReal ‖mNew b E s h W j (y.1.1, y.2)‖ ∂closedLaw b W np ≤
            ENNReal.ofReal (1 + C₂ / etaZ b E) := by
  obtain ⟨hκ, hEκ⟩ := BlockBand.SourceProcess.TagBirth.mem_bulkInterval_self hE1 hE2
  obtain ⟨C₂, W₀, hC₂, hM⟩ := lintegral_freshDelta_sq_le hGA hb0 hb hκ
  refine ⟨C₂, W₀, hC₂, fun W hW hW1 s h hh np j hs => ?_⟩
  set τ : Fin np → ℝ := fun _ => 0
  set m : Fin np → ℝ := fun _ => 0
  have hη : 0 < etaZ b E := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  have hD2 := hM W hW E hEκ np j (X := b3ClosedX b E s h τ m W j)
    (measurable_b3ClosedX b E s h τ m j) (fun y => b3ClosedX_b3Ext hs le_rfl y)
    (ae_passive_b3ClosedX hb0 hb hE1 hE2 s h hh τ m hW1 j)
  have hDm : Measurable fun y : ProbedPath W np × ℝ =>
      ENNReal.ofReal ‖dcl b E s h W j (y.1.1, y.2)‖ :=
    (continuous_norm.measurable.comp ((measurable_dcl b E s h W j).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))).ennreal_ofReal
  have hD1 : ∫⁻ y, ENNReal.ofReal ‖dcl b E s h W j (y.1.1, y.2)‖ ∂closedLaw b W np ≤
      ENNReal.ofReal C₂ := by
    have e : ∀ y : ProbedPath W np × ℝ, ENNReal.ofReal ‖dcl b E s h W j (y.1.1, y.2)‖ ^ 2 =
        ENNReal.ofReal (‖freshDelta b E (b3ClosedX b E s h τ m W j y)
          (freshSample W j y.1.1)‖ ^ 2) := fun y => (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
    have := BirthP.lintegral_le_sqrt_of_sq hDm.aemeasurable (sq_nonneg C₂)
      (by simp_rw [e]; exact hD2)
    rwa [Real.sqrt_sq hC₂] at this
  have hfin : ∀ (M : GrowthPath W × ℝ → Matrix (Fin W) (Fin W) ℂ),
      (∀ᵐ y ∂closedLaw b W np, ‖M (y.1.1, y.2)‖ ≤
        1 + (etaZ b E)⁻¹ * ‖dcl b E s h W j (y.1.1, y.2)‖) →
      ∫⁻ y, ENNReal.ofReal ‖M (y.1.1, y.2)‖ ∂closedLaw b W np ≤
        ENNReal.ofReal (1 + C₂ / etaZ b E) := by
    intro M hMb
    calc ∫⁻ y, ENNReal.ofReal ‖M (y.1.1, y.2)‖ ∂closedLaw b W np
        ≤ ∫⁻ y, (1 + ENNReal.ofReal (etaZ b E)⁻¹ *
            ENNReal.ofReal ‖dcl b E s h W j (y.1.1, y.2)‖) ∂closedLaw b W np := by
          refine lintegral_mono_ae ?_
          filter_upwards [hMb] with y hy
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_mul (inv_nonneg.2 hη.le),
            ← ENNReal.ofReal_add zero_le_one (by positivity)]
          exact ENNReal.ofReal_le_ofReal hy
      _ = 1 + ENNReal.ofReal (etaZ b E)⁻¹ *
            ∫⁻ y, ENNReal.ofReal ‖dcl b E s h W j (y.1.1, y.2)‖ ∂closedLaw b W np := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ 1 + ENNReal.ofReal (etaZ b E)⁻¹ * ENNReal.ofReal C₂ := by gcongr
      _ = ENNReal.ofReal (1 + C₂ / etaZ b E) := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 hη.le), ← ENNReal.ofReal_one,
            ← ENNReal.ofReal_add zero_le_one (by positivity), div_eq_inv_mul]
  have hX := ae_passive_b3ClosedX (np := np) hb0 hb hE1 hE2 s h hh τ m hW1 j
  have hR : ∀ᵐ y ∂closedLaw b W np,
      ‖passiveResolvent b E (xcl b E s h W j (y.1.1, y.2))‖ ≤ (etaZ b E)⁻¹ := by
    filter_upwards [hX] with y hy
    exact BlockBand.Transmission.PassiveCovariance.norm_passiveResolvent_le hb0 hb hE1 hE2 hy
  constructor
  · refine hfin _ ?_
    filter_upwards [hR] with y hy
    have h1 := norm_one_add_mul_le (dcl b E s h W j (y.1.1, y.2))
      (passiveResolvent b E (xcl b E s h W j (y.1.1, y.2)))
    have h2 := mul_le_mul_of_nonneg_left hy (norm_nonneg (dcl b E s h W j (y.1.1, y.2)))
    show ‖mOld b E s h W j (y.1.1, y.2)‖ ≤ _
    unfold mOld
    linarith
  · refine hfin _ ?_
    filter_upwards [hR] with y hy
    have h1 := norm_one_add_mul_le (passiveResolvent b E (xcl b E s h W j (y.1.1, y.2)))
      (dcl b E s h W j (y.1.1, y.2))
    have h2 := mul_le_mul_of_nonneg_right hy (norm_nonneg (dcl b E s h W j (y.1.1, y.2)))
    show ‖mNew b E s h W j (y.1.1, y.2)‖ ≤ _
    unfold mNew
    linarith

/-- A closed `𝒦` entry with an unborn tag is zero. -/
theorem b3ClosedKAt_unborn_right (b E s h : ℝ) (τ m : Fin np → ℝ) {n : ℕ} {a a' : Fin np}
    (ha' : ¬ ⌊(W : ℝ) * τ a'⌋₊ < n) (y : ProbedPath W np × ℝ) :
    b3ClosedKAt b E s h τ m W n y a a' = 0 := by
  rw [b3ClosedKAt_eq_gcl, entry_eq_dot, probeColumn_eq_zero n τ m y.1.2 a' ha', mulVec_zero,
    dotProduct_zero]

theorem b3ClosedKAt_unborn_left (b E s h : ℝ) (τ m : Fin np → ℝ) {n : ℕ} {a a' : Fin np}
    (ha : ¬ ⌊(W : ℝ) * τ a⌋₊ < n) (y : ProbedPath W np × ℝ) :
    b3ClosedKAt b E s h τ m W n y a a' = 0 := by
  rw [b3ClosedKAt_eq_gcl, entry_eq_dot, probeColumn_eq_zero n τ m y.1.2 a ha, star_zero,
    zero_dotProduct]

theorem lintegral_indicator_zero_of {b : ℝ} {A : Set (ProbedPath W np × ℝ)}
    {f : ProbedPath W np × ℝ → ℂ} (hf : ∀ y, f y = 0) {θ : ℝ} :
    ∫⁻ y, ‖A.indicator f y‖ₑ ∂closedLaw b W np ≤ ENNReal.ofReal θ := by
  have hz : ∀ y, ‖A.indicator f y‖ₑ = 0 := fun y => by simp [hf]
  rw [lintegral_congr hz, lintegral_zero]
  exact zero_le

/-- The final arithmetic: `ofReal(c√R)·X ≤ θ` from `X ≤ 1 + C₂/η` and `c√R(1 + C₂/η) ≤ θ`. -/
theorem final_le {c Rr q θ : ℝ} (hc : 0 ≤ c) (h : c * (Real.sqrt Rr * (1 + q)) ≤ θ)
    {X : ℝ≥0∞} (hX : X ≤ ENNReal.ofReal (1 + q)) :
    ENNReal.ofReal (c * Real.sqrt Rr) * X ≤ ENNReal.ofReal θ := by
  calc ENNReal.ofReal (c * Real.sqrt Rr) * X
      ≤ ENNReal.ofReal (c * Real.sqrt Rr) * ENNReal.ofReal (1 + q) := by gcongr
    _ = ENNReal.ofReal (c * (Real.sqrt Rr * (1 + q))) := by
        rw [← ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ ≤ ENNReal.ofReal θ := ENNReal.ofReal_le_ofReal h

theorem eventually_sqrt_small (mc K θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ W : ℕ in atTop, Real.sqrt (mc / W) * K ≤ θ := by
  have h0 : Tendsto (fun W : ℕ => Real.sqrt (mc / W) * K) atTop (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp
      (tendsto_const_div_atTop_nhds_zero_nat mc)).mul_const K
    simpa [Real.sqrt_zero] using this
  filter_upwards [h0.eventually (gt_mem_nhds hθ)] with W hW
  exact hW.le

end BirthKSub

open BirthKSub

/-- **`ComplexBirthCrossK` holds** (direct closed birth form, newborn-probe and fresh averages). -/
theorem complexBirthCrossK_holds (hGA : GaussianAbsorptionContract) : ComplexBirthCrossK := by
  intro b E np τ m T s h K Vs hDom R θ hθ a a'
  obtain ⟨hCSL, hs, hsτ, hh0, hh1, -⟩ := hDom
  obtain ⟨hb0, hb, hE1, hE2, hinj, hτ0, hm, -⟩ := hCSL
  have hh : h ^ 2 < 1 := by nlinarith
  have hη : 0 < etaZ b E := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  obtain ⟨C₂, W₀, hC₂, hMom⟩ := lintegral_m_le hGA hb0 hb hE1 hE2
  set q : ℝ := C₂ / etaZ b E
  have hcl : ∀ᶠ W : ℕ in atTop, 1 ≤ closeLen s W :=
    (tendsto_nat_floor_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const hs)).eventually_ge_atTop 1
  by_cases haa : a = a'
  · subst haa
    filter_upwards with W
    intro j _ _ hnew hnd
    rcases hnew with hn | hn <;> exact absurd ⟨a, hn, Or.inl rfl⟩ hnd
  · filter_upwards [eventually_ge_atTop (max W₀ 1), hcl,
      eventually_sqrt_small (m a) (Real.sqrt R * (1 + q)) θ hθ,
      eventually_sqrt_small (m a') (Real.sqrt R * (1 + q)) θ hθ,
      BirthP.eventually_floor_ne (hτ0 a) (hτ0 a') (hinj.ne haa)] with W hW hcl hsa hsa' hne
    intro j hj1 hj2 hnew _
    have hW1 : 1 ≤ W := le_of_max_le_right hW
    have hW0 : W₀ ≤ W := le_of_max_le_left hW
    have hj : 1 ≤ j := hcl.trans hj1
    obtain ⟨hmo, hmn⟩ := hMom W hW0 hW1 s h hh np j hj1
    rcases hnew with hna | hna'
    · rcases lt_trichotomy ⌊(W : ℝ) * τ a'⌋₊ j with hlt | heq | hgt
      · refine (lintegral_birth_new_old_le hb0 hb hE1 hE2 s h hh τ m R (Vs W) hW1 hj hj1 haa
          hna hlt).trans ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact final_le (Real.sqrt_nonneg _) hsa hmn
      · exact absurd (hna.trans heq.symm) hne
      · exact lintegral_indicator_zero_of
          (b3ClosedKAt_unborn_right b E s h τ m (by omega))
    · rcases lt_trichotomy ⌊(W : ℝ) * τ a⌋₊ j with hlt | heq | hgt
      · refine (lintegral_birth_old_new_le hb0 hb hE1 hE2 s h hh τ m R (Vs W) hW1 hj hj1 haa
          hlt hna').trans ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact final_le (Real.sqrt_nonneg _) hsa' hmo
      · exact absurd (heq.trans hna'.symm) hne
      · exact lintegral_indicator_zero_of
          (b3ClosedKAt_unborn_left b E s h τ m (by omega))

end BlockBand.SourceProcess.PhysApprox.B3
