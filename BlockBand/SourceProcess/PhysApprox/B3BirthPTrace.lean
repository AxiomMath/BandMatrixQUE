module

public import BlockBand.SourceProcess.PhysApprox.B3BirthFresh
public import BlockBand.SourceProcess.RawTag.UpdPins
public import BlockBand.SourceProcess.RawTag.Birth
public import BlockBand.SourceProcess.TagBirth.PathTrace
public import BlockBand.SourceProcess.ComplexSourceLaw.ExtTag

/-!
# The path-only estimate `ComplexBirthKFreshTrace`

At its birth length `j + 1` (`j ≥ 1`), the newest block of `G₁₁` is a.s. the fresh
`B = R + RΔR = 𝒢₁₁(X_j)` (`BirthP.birthBlock_succ_eq`, from the proved `RawTag.rawBirth_holds`
read entrywise, and `TagBirth.g11_eq_resolvent_add`). Then
* `W⁻¹ Tr B = ⟨𝒢₁₁(X_j)⟩`, and the proved fresh-layer bound `TagBirth.freshPhysTraceLp_holds`
  with the length-uniform `δ₀` moments `LengthUniform.deltaZeroLengthUniform_holds` give
  `E|W⁻¹ Tr B − a| ≤ A·C/W + B'/√W` (`BirthP.lintegral_trace_sub_le`);
* `Re Tr BBᴴ ≤ W‖B‖²` and `‖B‖ ≤ e + e²‖Δ‖` (`‖R‖ ≤ e`) with `E‖Δ‖ ≤ C_Δ`
  (`RawTag.momBd_stepDelta`) give `E[W⁻¹(Re Tr BBᴴ)^{1/2}] ≤ (e + e²C_Δ)/√W`
  (`BirthP.lintegral_hs_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.LengthUniform
open BlockBand.SourceProcess.FullSource BlockBand.SourceProcess.RawTag
open BlockBand.SourceProcess.TagBirth BlockBand.SourceProcess.ClosedPath
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

namespace BirthP

variable {W : ℕ}

/-- The newborn unit tag at length `j + 1` is the mass-one tag vector at position `0`. -/
theorem unitTag_newborn (j : ℕ) (g : Fin W → ℂ) :
    unitTag W (j + 1) j g = tagVector W (j + 1) 0 1 g := by
  rw [tagVector_eq_smul_unitTag (j + 1) 0 zero_le_one g]
  simp

/-- The newborn raw form on unit vectors is `W⁻¹` times the entry of the newest block. -/
theorem rawForm_newborn_single (b E : ℝ) (j : ℕ) (ω : GrowthPath W) (a a' : Fin W) :
    rawForm b E W (j + 1) j j ω (Pi.single a 1) (Pi.single a' 1) =
      (W : ℂ)⁻¹ * birthBlock b E W (j + 1) 0 ω a a' := by
  have e := ComplexSourceLaw.tagForm_tagVector (fullInverse b E W (j + 1) ω).toBlocks₁₁ 0 0
    (Pi.single a 1) (Pi.single a' 1)
  unfold rawForm
  rw [unitTag_newborn, unitTag_newborn]
  refine e.trans ?_
  simp [birthBlock, Pi.single_apply]

/-- A bilinear form on two unit vectors `W^{-1/2}e_a`, `W^{-1/2}e_{a'}`. -/
theorem bilinear_unitVec_single (M : Matrix (Fin W) (Fin W) ℂ) (a a' : Fin W) :
    bilinear (unitVec W (Pi.single a 1)) M (unitVec W (Pi.single a' 1)) = (W : ℂ)⁻¹ * M a a' := by
  have hu : ∀ c : Fin W, unitVec W (Pi.single c 1) = Pi.single c ((Real.sqrt (1 / W) : ℝ) : ℂ) := by
    intro c
    funext x
    by_cases h : x = c
    · subst h
      simp [unitVec]
    · simp [unitVec, h]
  rw [hu, hu, bilinear, Pi.star_single, single_dotProduct]
  simp only [mulVec, dotProduct_single, Complex.star_def, Complex.conj_ofReal]
  linear_combination M a a' * ComplexSourceLaw.sqrt_inv_mul_self W

/-- **The newest block at its birth length** is a.s. `R + RΔR` (`RawTag.rawBirth_holds`). -/
theorem birthBlock_succ_eq {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) : ∀ᵐ ω ∂growthPathLaw W b, ∀ j : ℕ, 1 ≤ j →
      birthBlock b E W (j + 1) 0 ω = stepR b E W j ω +
        stepR b E W j ω * stepDelta b E W j ω * stepR b E W j ω := by
  filter_upwards [rawBirth_holds b E hb0 hb hE1 hE2 W hW] with ω hω j hj
  ext a a'
  have h := (hω j hj).2.2 (Pi.single a 1) (Pi.single a' 1)
  rw [rawForm_newborn_single, bilinear_unitVec_single] at h
  have hW0 : (W : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr (by omega))
  exact mul_left_cancel₀ hW0 h

/-- `‖R_j‖ ≤ ((1-b)κ/4)⁻¹` almost surely. -/
theorem ae_norm_stepR_le {b E κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) (j : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, ‖stepR b E W j ω‖ ≤ ((1 - b) * κ / 4)⁻¹ := by
  obtain ⟨hE1, hE2⟩ := bulk_bounds hκ hE
  have hη₀ : 0 < (1 - b) * κ / 4 := by
    have : 0 < 1 - b := by linarith
    positivity
  filter_upwards [ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) (by linarith : b < 1)
    hE1 hE2] with ω hw
  exact (norm_passiveResolvent_le hb0 hb hE1 hE2 (pathNearSchur_passive hw j)).trans
    (inv_anti₀ hη₀ (etaZ_ge hb0 hb hκ hE))

/-- **The fresh normalized trace of the newest block** in `L¹`:
`E|W⁻¹ Tr B − a| ≤ A·(C/W) + B'/√W`, from the fresh-layer bound and the `δ₀` moment at `X_j`. -/
theorem lintegral_trace_sub_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hW : 1 ≤ W) {j : ℕ}
    (hj : 1 ≤ j)
    (hF : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      eLpNorm (fun ω => physTr b E X ω - matchedA E) (ENNReal.ofReal 1) (freshLaw W b) ≤
        ENNReal.ofReal (A * jetDistance0 b E X + B / Real.sqrt W))
    (hδ : eLpNorm (fun ω => jetDistance0 b E (pathX b E W j ω)) (ENNReal.ofReal 1)
      (growthPathLaw W b) ≤ ENNReal.ofReal (C / W)) :
    ∫⁻ ω, ‖(W : ℂ)⁻¹ * (birthBlock b E W (j + 1) 0 ω).trace - matchedA E‖ₑ ∂growthPathLaw W b ≤
      ENNReal.ofReal (A * (C / W) + B / Real.sqrt W) := by
  have hη := etaZ_pos b E (by linarith) hE1 hE2
  have hmap := growthPathLaw_map_past_fresh W j b
  have hπ := measurable_pastCoords W j
  have hφ := measurable_freshSample W j
  set Φ : PastSample W j × LayerSample W .oneBlockOnePort → ℂ := fun q =>
    physTr b E (nearSchur (boundaryZ b E) (pastXX E W j q.1)) q.2 - matchedA E with hΦdef
  have hΦ : Measurable Φ := (measurable_physTr_past b E j).sub measurable_const
  have hae : ∀ᵐ ω ∂growthPathLaw W b,
      ‖(W : ℂ)⁻¹ * (birthBlock b E W (j + 1) 0 ω).trace - matchedA E‖ₑ =
        ‖Φ (pastCoords W j ω, freshSample W j ω)‖ₑ := by
    filter_upwards [birthBlock_succ_eq hb0 hb hE1 hE2 hW,
      ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) (by linarith : b < 1) hE1 hE2]
      with ω hB hw
    have hY := pathNearSchur_passive hw j
    have hg : stepR b E W j ω + stepR b E W j ω * stepDelta b E W j ω * stepR b E W j ω =
        g11 E (boundaryZ b E) (pathX b E W j ω) (freshSample W j ω) :=
      (g11_eq_resolvent_add hη hY (freshSample W j ω)).symm
    have e1 : physTr b E (pathX b E W j ω) (freshSample W j ω) =
        (W : ℂ)⁻¹ * (g11 E (boundaryZ b E) (pathX b E W j ω) (freshSample W j ω)).trace := rfl
    rw [hB j hj, hg, ← e1]
    simp only [hΦdef, pathX_eq_past]
  have hfm : AEStronglyMeasurable (fun ω => Φ (pastCoords W j ω, freshSample W j ω))
      (growthPathLaw W b) := (hΦ.comp (hπ.prodMk hφ)).aestronglyMeasurable
  rw [lintegral_congr_ae hae, ← eLpNorm_one_eq_lintegral_enorm hfm, ← ENNReal.ofReal_one]
  set gq : PastSample W j → ℝ := fun q =>
    A * jetDistance0 b E (nearSchur (boundaryZ b E) (pastXX E W j q)) + B / Real.sqrt W with hgq
  have hg : Measurable gq := by
    refine (measurable_const.mul ?_).add measurable_const
    exact (measurable_jetDistance0 b E).comp (measurable_nearSchur_comp _ (measurable_pastXX E j))
  have hstep : ∀ᵐ q ∂pastLaw W j b, eLpNorm (fun x => ‖Φ (q, x)‖) (ENNReal.ofReal 1)
      (freshLaw W b) ≤ ENNReal.ofReal (gq q) := by
    filter_upwards [ae_pastLaw_hermitian W j b] with q hq
    have hYq := nearSchur_passive hη (pastXX_isHermitian E hq)
    have hm : AEStronglyMeasurable (fun x => Φ (q, x)) (freshLaw W b) :=
      (hΦ.comp measurable_prodMk_left).aestronglyMeasurable
    rw [eLpNorm_norm _ hm]
    simp only [hΦdef]
    exact hF _ hYq
  refine (eLpNorm_le_of_fresh hπ hφ hmap one_pos hfm hΦ.norm hg
    (Eventually.of_forall fun _ => le_rfl) hstep).trans ?_
  have hgπ : (fun ω => gq (pastCoords W j ω)) =
      (fun ω => A * jetDistance0 b E (pathX b E W j ω)) + fun _ => B / Real.sqrt W := by
    funext ω
    simp only [hgq, Pi.add_apply, pathX_eq_past]
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 1 := by simp
  have hp0 : ENNReal.ofReal 1 ≠ 0 := by simp
  rw [hgπ]
  refine (eLpNorm_add_le hp1).trans ?_
  rw [eLpNorm_const_prob _ hp0, show (fun ω => A * jetDistance0 b E (pathX b E W j ω)) =
    A • fun ω => jetDistance0 b E (pathX b E W j ω) from rfl, eLpNorm_const_smul]
  refine (add_le_add (mul_le_mul_right hδ _) le_rfl).trans (le_of_eq ?_)
  rw [Real.enorm_of_nonneg hA, Real.enorm_of_nonneg (show 0 ≤ B / Real.sqrt W by positivity),
    ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- `Re Tr BBᴴ ≤ W‖B‖²`. -/
theorem trace_mul_conjTranspose_re_le (B : Matrix (Fin W) (Fin W) ℂ) :
    (B * Bᴴ).trace.re ≤ W * ‖B‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos W with h0 | hW
  · subst h0
    simp [Matrix.trace]
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 := BlockBand.Transmission.PathScalar.norm_normTrace_le (B * Bᴴ)
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hW'] at h1
  have h2 : ‖B * Bᴴ‖ ≤ ‖B‖ ^ 2 :=
    calc ‖B * Bᴴ‖ ≤ ‖B‖ * ‖Bᴴ‖ := Matrix.l2_opNorm_mul B Bᴴ
      _ = ‖B‖ ^ 2 := by rw [Matrix.l2_opNorm_conjTranspose, sq]
  calc (B * Bᴴ).trace.re ≤ ‖(B * Bᴴ).trace‖ := Complex.re_le_norm _
    _ ≤ W * ‖B * Bᴴ‖ := h1
    _ ≤ W * ‖B‖ ^ 2 := mul_le_mul_of_nonneg_left h2 hW'.le

/-- `W⁻¹(Re Tr BBᴴ)^{1/2} ≤ W^{-1/2}‖B‖`. -/
theorem inv_mul_sqrt_trace_le (B : Matrix (Fin W) (Fin W) ℂ) :
    (W : ℝ)⁻¹ * Real.sqrt (B * Bᴴ).trace.re ≤ (Real.sqrt W)⁻¹ * ‖B‖ := by
  rcases Nat.eq_zero_or_pos W with h0 | hW
  · subst h0
    simp
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hs : Real.sqrt (B * Bᴴ).trace.re ≤ Real.sqrt W * ‖B‖ := by
    rw [← Real.sqrt_sq (norm_nonneg B), ← Real.sqrt_mul hW'.le]
    exact Real.sqrt_le_sqrt (trace_mul_conjTranspose_re_le B)
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW'
  calc (W : ℝ)⁻¹ * Real.sqrt (B * Bᴴ).trace.re ≤ (W : ℝ)⁻¹ * (Real.sqrt W * ‖B‖) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (Real.sqrt W * Real.sqrt W)⁻¹ * (Real.sqrt W * ‖B‖) := by
        rw [Real.mul_self_sqrt hW'.le]
    _ = (Real.sqrt W)⁻¹ * ‖B‖ := by
        field_simp

/-- **The normalized Hilbert–Schmidt norm of the newest block** in `L¹`:
`E[W⁻¹(Re Tr BBᴴ)^{1/2}] ≤ W^{-1/2}(e + e²C_Δ)` when `‖R_j‖ ≤ e` a.s. and `‖‖Δ_j‖‖_{L¹} ≤ C_Δ`. -/
theorem lintegral_hs_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) {j : ℕ} (hj : 1 ≤ j) {e CΔ : ℝ} (he : 0 ≤ e) (hCΔ : 0 ≤ CΔ)
    (hR : ∀ᵐ ω ∂growthPathLaw W b, ‖stepR b E W j ω‖ ≤ e)
    (hΔ : MomBd (growthPathLaw W b) (fun ω => ‖stepDelta b E W j ω‖) 1 CΔ) :
    ∫⁻ ω, ENNReal.ofReal ((W : ℝ)⁻¹ * Real.sqrt ((birthBlock b E W (j + 1) 0 ω) *
        (birthBlock b E W (j + 1) 0 ω)ᴴ).trace.re) ∂growthPathLaw W b ≤
      ENNReal.ofReal ((Real.sqrt W)⁻¹ * (e + e ^ 2 * CΔ)) := by
  have hsW : 0 ≤ (Real.sqrt W)⁻¹ := by positivity
  have hM : MomBd (growthPathLaw W b)
      (fun ω => (Real.sqrt W)⁻¹ * (e + e ^ 2 * ‖stepDelta b E W j ω‖)) 1
      ((Real.sqrt W)⁻¹ * (|e| + e ^ 2 * CΔ)) :=
    ((MomBd.const e 1 one_pos).add le_rfl (hΔ.const_mul (sq_nonneg e)) (abs_nonneg _)
      (by positivity)).const_mul hsW
  have hI := lintegral_rpow_le_of_momBd hM one_pos (by positivity)
  rw [abs_of_nonneg he, Real.rpow_one] at hI
  refine le_trans (lintegral_mono_ae ?_) hI
  filter_upwards [birthBlock_succ_eq hb0 hb hE1 hE2 hW, hR] with ω hB hRω
  rw [Real.rpow_one]
  refine ENNReal.ofReal_le_ofReal ((inv_mul_sqrt_trace_le _).trans (le_trans ?_ (le_abs_self _)))
  rw [hB j hj]
  refine mul_le_mul_of_nonneg_left ?_ hsW
  have := norm_res_le (M := stepDelta b E W j ω) he hRω
  linarith

/-- `E ∈ (-2, 2)` lies in the bulk interval of width `min(E + 2, 2 − E)`. -/
theorem mem_bulkInterval_min {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    0 < min (E + 2) (2 - E) ∧ E ∈ bulkInterval (min (E + 2) (2 - E)) :=
  ⟨lt_min (by linarith) (by linarith),
    ⟨by linarith [min_le_left (E + 2) (2 - E)], by linarith [min_le_right (E + 2) (2 - E)]⟩⟩

/-- Eventually `1 ≤ ⌊Ws⌋`. -/
theorem eventually_one_le_closeLen {s : ℝ} (hs : 0 < s) :
    ∀ᶠ W : ℕ in atTop, 1 ≤ closeLen s W := by
  filter_upwards [(tendsto_natCast_atTop_atTop.atTop_mul_const hs).eventually_ge_atTop 1]
    with W hW
  exact Nat.le_floor (by simpa using hW)

/-- `j < ⌊WT⌋` gives `j ≤ TW`. -/
theorem le_mul_of_lt_floor {W j : ℕ} {T : ℝ} (hj : j < ⌊(W : ℝ) * T⌋₊) : (j : ℝ) ≤ T * W := by
  have := Nat.lt_of_lt_floor hj
  rw [mul_comm] at this
  exact this.le

end BirthP

/-- **`ComplexBirthKFreshTrace` from the input hypotheses** (`MatchedTracesContract`,
`GaussianAbsorptionContract`, `GaussianLpGradient`).
-/
theorem complexBirthKFreshTrace_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) : ComplexBirthKFreshTrace := by
  intro b E np τ m T s hD hs _ θ hθ
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hD
  obtain ⟨hκ, hE⟩ := BirthP.mem_bulkInterval_min hE1 hE2
  set κ := min (E + 2) (2 - E)
  obtain ⟨A, B, W₁, hA, hB, hF⟩ := freshPhysTraceLp_holds hGA hLp b hb0 hb κ hκ 1 le_rfl
  obtain ⟨C, hC, hδ⟩ := deltaZeroLengthUniform_holds hMT hGA hLp b hb0 hb κ 1 hκ le_rfl
  obtain ⟨W₂, hδ'⟩ := hδ T
  obtain ⟨CΔ, W₃, hCΔ, hΔ⟩ := momBd_stepDelta hGA hb0 hb hκ (r := 1) le_rfl
  set e := ((1 - b) * κ / 4)⁻¹
  have he : 0 ≤ e := by
    have : 0 < 1 - b := by linarith
    positivity
  have hsq : Tendsto (fun W : ℕ => Real.sqrt W) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun W : ℕ => A * (C / W)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).const_mul A
  have h2 : Tendsto (fun W : ℕ => B / Real.sqrt W) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsq
  have h3 : Tendsto (fun W : ℕ => (Real.sqrt W)⁻¹ * (e + e ^ 2 * CΔ)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hsq).mul_const (e + e ^ 2 * CΔ)
  have hlim := (h1.add h2).add h3
  rw [add_zero, add_zero] at hlim
  filter_upwards [eventually_ge_atTop (max (max W₁ W₂) (max W₃ 1)),
    (tendsto_order.1 hlim).2 θ hθ, BirthP.eventually_one_le_closeLen hs] with W hW hsmall hcl
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hW₂⟩, hW₃, hW1⟩ := hW
  intro j hj1 hj2
  have hj : 1 ≤ j := hcl.trans hj1
  have hjT := BirthP.le_mul_of_lt_floor hj2
  have hsW : 0 ≤ Real.sqrt W := Real.sqrt_nonneg _
  have p1 : 0 ≤ A * (C / W) := by positivity
  have p2 : 0 ≤ B / Real.sqrt W := by positivity
  have p3 : 0 ≤ (Real.sqrt W)⁻¹ * (e + e ^ 2 * CΔ) := by positivity
  constructor
  · refine (BirthP.lintegral_trace_sub_le hb0 hb hE1 hE2 hA hB hC hW1 hj
      (fun X hY => hF W hW₁ E hE X hY) (hδ' W hW₂ E hE j hj hjT)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    linarith
  · refine (BirthP.lintegral_hs_le hb0 hb hE1 hE2 hW1 hj he hCΔ
      (BirthP.ae_norm_stepR_le hb0 hb hκ hE j) (hΔ W hW₃ E hE j)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    linarith

end BlockBand.SourceProcess.PhysApprox.B3
