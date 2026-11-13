module

public import BlockBand.SourceProcess.PhysApprox.B3GramStepSmall
public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormBound
public import BlockBand.SourceProcess.PhysApprox.B3ClosedForm
public import BlockBand.SourceProcess.PhysApprox.B3JetFam
public import BlockBand.SourceProcess.ClosedFeas.Main
public import BlockBand.Transmission.LawForced.RatioLog
public import BlockBand.Transmission.Generator.StepExact

/-!
# The jet bridge and the frame and leak bounds of the closed Gram update

* **`closedJetStopHalf_of_fam`**, **`closedJetStopSmall_of_fam`**: the jet hypothesis
  `ClosedJet0Fam` (whole space, `‖δ₀‖_p ≤ C_p/W`) gives the stopped jets `ClosedJetStopHalf`,
  `ClosedJetStopSmall` (indicator, `p = 4`, `W⁻⁴ ≤ W⁻²`).
* **`closedNearVBound_holds : ClosedNearVBound`** (no hypothesis): for every column (current and
  probe) `‖gramNearV d‖² ≤ Re Tr M_cl,j < R` on the alive set, by the lossless-closing inequality
  `posSemidef_closed_gram_sub` applied to the open-frame column.
* **`closedLeakBound_holds : ClosedLeakBound`** (no hypothesis), deterministically on the cap
  event: `Tr(1 − SS*)(X_cl) ≤ W − Tr A ≤ K`, `A` the omitted projection. The first step is
  `1 − S_cl*S_cl = G*G`, `G = F𝕊(1 + Z)ι*`, `F = 1 − ι*ι − Π*Π` a Hermitian idempotent of trace
  `W − Tr A`, and `‖G‖ ≤ 1`; the second is the cap (`physTseq_le_of_cap`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.PhysApprox.ClosedForm
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W np K : ℕ}

/-!
## The jet bridge
-/

/-- **`ClosedJet0Fam ⇒ ClosedJetStopHalf`**: `E[1_Aδ₀⁴] ≤ Eδ₀⁴ ≤ (C⁺/W)⁴ ≤ C⁺⁴/W²`. -/
theorem closedJetStopHalf_of_fam (hJ : ClosedJet0Fam) : ClosedJetStopHalf := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨C, hC⟩ := hJ b E np τ m T s h K Vs hD 4 (by norm_num)
  refine ⟨(max C 0) ^ 4, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with W hW hW1 j hj
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hle : eLpNorm (fun y => jetDistance0 b E (b3ClosedX b E s h τ m W j y))
      (ENNReal.ofReal 4) (closedLaw b W np) ≤ ENNReal.ofReal (max C 0 / W) :=
    (hW j hj).trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) hW0.le))
  have h4 := jetFam_lintegral_four_le (closedLaw b W np) (fun y => norm_nonneg _)
    (div_nonneg (le_max_right _ _) hW0.le) hle
  refine (lintegral_mono fun y => Set.indicator_le_self _ _ y).trans
    (h4.trans (ENNReal.ofReal_le_ofReal ?_))
  rw [div_pow]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_right₀ hW1r (by norm_num))

/-- **`ClosedJet0Fam ⇒ ClosedJetStopSmall`.** -/
theorem closedJetStopSmall_of_fam (hJ : ClosedJet0Fam) : ClosedJetStopSmall :=
  closedJetStopSmall_of_half (closedJetStopHalf_of_fam hJ)

/-!
## The right frame bound for every column
-/

theorem closedFrame_gramCol (b E s h : ℝ) (τ m : Fin np → ℝ) (j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (d : SrcCol K (Fin np))
    (y : ProbedPath W np × ℝ) :
    (fun a => b3ClosedFrameAt b E s h τ m W j Vs y a d) =
      (physClosingMapAt b E s h W j y.1.1 (phase y.2))ᴴ *ᵥ gramCol b E s τ m W j Vs d y.1 := by
  funext a
  simp [b3ClosedFrameAt, Matrix.mul_apply, mulVec, dotProduct, gramCol]

/-- **The right frame bound** `‖v_d‖² ≤ Re Tr M_cl` for every column `d`, on `|z| = 1`. -/
theorem vecNorm_gramNearV_le (b E s h : ℝ) (hh : h ^ 2 < 1) (τ m : Fin np → ℝ) (j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (d : SrcCol K (Fin np))
    {R : ℝ} (y : ProbedPath W np × ℝ)
    (hS : scatteringMatrix b E W j y.1.1 * (scatteringMatrix b E W j y.1.1)ᴴ = 1)
    (hU : IsUnit (1 - phase y.2 • closingN (scatteringMatrix b E W j y.1.1)
      (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
      (farEmbed (closingPairing b E h W (closeLen s W) y.1.1))).det)
    (hy : ((b3ClosedGramAt b E s h τ m W j Vs y).1.trace).re < R) :
    vecNorm (gramNearV b E s h τ m W j Vs d y) ≤ Real.sqrt R := by
  set S := scatteringMatrix b E W j y.1.1
  set A := farEmbed (omittedProj b E h W (closeLen s W) y.1.1)
  set Pi := farEmbed (closingPairing b E h W (closeLen s W) y.1.1)
  set z := phase y.2
  set x := gramCol b E s τ m W j Vs d y.1
  have hA2 : A * A = A := by rw [farEmbed_mul, omittedProj_mul_self]
  have hAH : Aᴴ = A := by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hAPi : A * Pi = Pi := by rw [farEmbed_mul, omittedProj_mul_closingPairing]
  have hPi : Pi * Piᴴ = A := by
    rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh]
  have hD := posSemidef_closed_gram_sub hA2 hAH hAPi hPi hS (phase_mul_star y.2) hU
    (farEmbed_mul_nearSel_conj _) nearSel_mul_conjTranspose
  have h0 := hD.dotProduct_mulVec_nonneg x
  have h0' : 0 ≤ (star x ⬝ᵥ ((closingMap S A Pi z * (closingMap S A Pi z)ᴴ -
      (nearSel W * (S * (1 + closingZ S A Pi z)))ᴴ *
        (nearSel W * (S * (1 + closingZ S A Pi z)))) *ᵥ x)).re := by
    have := (Complex.le_def.1 h0).1
    simpa using this
  rw [sub_mulVec, dotProduct_sub, Complex.sub_re, re_dot_gram,
    ← conjTranspose_conjTranspose (closingMap S A Pi z), conjTranspose_conjTranspose
      ((closingMap S A Pi z)ᴴ), re_dot_gram, sub_nonneg] at h0'
  have hv : gramNearV b E s h τ m W j Vs d y =
      (nearSel W * (S * (1 + closingZ S A Pi z))) *ᵥ x := by
    simp only [gramNearV, physClosingZAt, ← mulVec_mulVec]
    rfl
  have hcol : ∑ a, ‖((closingMap S A Pi z)ᴴ *ᵥ x) a‖ ^ 2 ≤
      ((b3ClosedGramAt b E s h τ m W j Vs y).1.trace).re := by
    have e : ∀ a, ((closingMap S A Pi z)ᴴ *ᵥ x) a = b3ClosedFrameAt b E s h τ m W j Vs y a d :=
      fun a => (congrFun (closedFrame_gramCol b E s h τ m j Vs d y) a).symm
    simp only [e]
    exact col_sq_le_trace (b3ClosedFrameAt b E s h τ m W j Vs y) d
  refine Real.sqrt_le_sqrt ?_
  rw [hv]
  exact h0'.trans (hcol.trans hy.le)

/-- **`ClosedNearVBound` holds** (`C_v = √(max R 0)`). -/
theorem closedNearVBound_holds : ClosedNearVBound := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨⟨hb0, hb, hE1, hE2, -⟩, -, -, hh0, hh1, -⟩ := hD
  have hh : h ^ 2 < 1 := by nlinarith
  refine ⟨Real.sqrt (max R 0), ?_⟩
  filter_upwards [eventually_ge_atTop 1] with W hW j hj
  filter_upwards [ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW,
    ae_closedPhase_good (W := W) (np := np) b E s h j] with y hP hQ hy d
  exact vecNorm_gramNearV_le b E s h hh τ m j (Vs W) d y (hP.2.2.2 j)
    (isUnit_iff_ne_zero.2 hQ.1)
    (lt_of_lt_of_le (hy.2 j (Finset.mem_Ico.1 hj).1 le_rfl) (le_max_left _ _))

/-!
## The closed one-port leak
-/

theorem trace_farEmbed (X : Matrix (Fin W) (Fin W) ℂ) : (farEmbed X).trace = X.trace := by
  simp [farEmbed, Matrix.trace, Fintype.sum_prod_type]

theorem sandwich_one_sub {n : Type*} [Fintype n] [DecidableEq n] (F X : Matrix n n ℂ)
    (hFH : Fᴴ = F) (hFF : F * F = F) (hX : F * X * F = X) : Fᴴ * (1 - X) * F = F - X := by
  rw [hFH, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hFF, hX]

/-- **The leak of the far-closed one port is at most the retained trace**: on `|z| = 1`, with
`𝕊_j` unitary and the closing denominators invertible,
`Tr(1 − SS*)(X_cl) ≤ W − Re Tr A`, `A` the omitted projection at `n_s`. -/
theorem oneLeak_closedNearX_le (b E s h : ℝ) (hh : h ^ 2 < 1) (j : ℕ) (ω : GrowthPath W)
    (θ : ℝ) (hS : scatteringMatrix b E W j ω * (scatteringMatrix b E W j ω)ᴴ = 1)
    (hU : IsUnit (1 - phase θ • closingN (scatteringMatrix b E W j ω)
      (farEmbed (omittedProj b E h W (closeLen s W) ω))
      (farEmbed (closingPairing b E h W (closeLen s W) ω))).det)
    (hR : IsUnit (closedNearR b E s h W j ω (phase θ)).det) :
    GramStepU.oneLeak b E (closedNearX b E s h W j ω (phase θ)) ≤
      (W : ℝ) - ((omittedProj b E h W (closeLen s W) ω).trace).re := by
  set S := scatteringMatrix b E W j ω
  set A := farEmbed (omittedProj b E h W (closeLen s W) ω)
  set Pi := farEmbed (closingPairing b E h W (closeLen s W) ω)
  set z := phase θ
  set ns := nearSel W
  set Ccl := closingMap S A Pi z
  set Z := closingZ S A Pi z
  set B := S * (1 + Z)
  set M := ns * B
  have hA2 : A * A = A := by rw [farEmbed_mul, omittedProj_mul_self]
  have hAH : Aᴴ = A := by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hAPi : A * Pi = Pi := by rw [farEmbed_mul, omittedProj_mul_closingPairing]
  have hPi : Pi * Piᴴ = A := by
    rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh]
  have hnn : ns * nsᴴ = 1 := nearSel_mul_conjTranspose
  have hz : z * star z = 1 := phase_mul_star θ
  have hSS : Sᴴ * S = 1 := mul_eq_one_comm.mp hS
  -- the one-port scattering of `X_cl` is `ι𝕊(1 + Z)ιᴴ`
  have hRX : passiveResolvent b E (closedNearX b E s h W j ω z) =
      closedNearR b E s h W j ω z := by
    simp only [passiveResolvent, closedNearX, sub_sub_cancel]
    exact Matrix.nonsing_inv_nonsing_inv _ hR
  have hnC : ns * Ccl = ns :=
    ns_mul_closingMap (nearSel_mul_farEmbed _) (nearSel_mul_farEmbed _) hU
  have hAns : A * nsᴴ = 0 := farEmbed_mul_nearSel_conj _
  have hCns : Ccl * nsᴴ = (1 + Z) * nsᴴ := by
    simp only [Ccl, Z, closingMap, closingT, closingZ, Matrix.add_mul, Matrix.sub_mul,
      Matrix.one_mul, hAns, sub_zero, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_zero]
  have hRe : closedNearR b E s h W j ω z = ns * (boundaryResolvent b E W j ω * (Ccl * nsᴴ)) := by
    rw [closedNearR, Matrix.mul_assoc, Matrix.mul_assoc]; rfl
  have hoS : GramStepU.oneS b E (closedNearX b E s h W j ω z) = M * nsᴴ := by
    have hcS : S = 1 - (boundaryZ b E - star (boundaryZ b E)) • boundaryResolvent b E W j ω := by
      simp only [S, scatteringMatrix, c_eq_sub_star]
    have e1 : M * nsᴴ = ns * (S * (Ccl * nsᴴ)) := by
      simp only [M, B, Matrix.mul_assoc]; rw [hCns]
    rw [GramStepU.oneS, hRX, c_eq_sub_star, e1, hcS, hRe, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc ns Ccl, hnC, hnn]
  -- `1 − S*S = G*G`
  set F : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := 1 - nsᴴ * ns - Piᴴ * Pi with hFdef
  have hFH : Fᴴ = F := by
    simp only [F, conjTranspose_sub, conjTranspose_one, conjTranspose_mul,
      conjTranspose_conjTranspose]
  have hPins : Pi * nsᴴ = 0 := farEmbed_mul_nearSel_conj _
  have hnsPi' : ns * Piᴴ = 0 := by
    have := congrArg conjTranspose hPins
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] at this
  have hFF : F * F = F := by
    have e1 : nsᴴ * ns * (nsᴴ * ns) = nsᴴ * ns := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc ns, hnn, Matrix.one_mul]
    have e2 : Piᴴ * Pi * (Piᴴ * Pi) = Piᴴ * Pi := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Pi, hPi, hAPi]
    have e3 : nsᴴ * ns * (Piᴴ * Pi) = 0 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc ns, hnsPi', Matrix.zero_mul, Matrix.mul_zero]
    have e4 : Piᴴ * Pi * (nsᴴ * ns) = 0 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Pi, hPins, Matrix.zero_mul, Matrix.mul_zero]
    simp only [F, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, e1, e2, e3, e4]
    abel
  have hCC := closingMap_mul_conj hA2 hAH hPi hS hz hU
  have hPB : Pi * B = star z • Z := pi_s_one_add_z hAPi hU hz
  have hBB : Bᴴ * B = (1 + Z)ᴴ * (1 + Z) := by
    simp only [B, conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Sᴴ S, hSS, Matrix.one_mul]
  have hZZ : (Pi * B)ᴴ * (Pi * B) = Zᴴ * Z := by
    rw [hPB, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_star, hz,
      one_smul]
  have hkey : Ccl * Cclᴴ - Mᴴ * M = Bᴴ * F * B := by
    have e : Bᴴ * F * B = Bᴴ * B - (ns * B)ᴴ * (ns * B) - (Pi * B)ᴴ * (Pi * B) := by
      simp only [F, conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        Matrix.mul_assoc]
    rw [e, hBB, hZZ, hCC]
    simp only [M, conjTranspose_add, conjTranspose_one, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one]
    abel
  have hCCn : ns * (Ccl * Cclᴴ) * nsᴴ = 1 := by
    have e : ns * (Ccl * Cclᴴ) * nsᴴ = (ns * Ccl) * (ns * Ccl)ᴴ := by
      rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e, hnC, hnn]
  set G : Matrix (Fin 2 × Fin W) (Fin W) ℂ := F * B * nsᴴ with hGdef
  have hP : 1 - (M * nsᴴ)ᴴ * (M * nsᴴ) = Gᴴ * G := by
    have e : 1 - (M * nsᴴ)ᴴ * (M * nsᴴ) = ns * (Ccl * Cclᴴ - Mᴴ * M) * nsᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hCCn, conjTranspose_mul, conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
    rw [e, hkey, hGdef]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hFH, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F F, hFF]
  -- `‖G‖ ≤ 1`, hence `1 − GG* ⪰ 0`
  have hGG1 : (1 - Gᴴ * G).PosSemidef := by
    rw [← hP, sub_sub_cancel]; exact posSemidef_conjTranspose_mul_self _
  have hnG : ‖Gᴴ * G‖ ≤ 1 :=
    Transmission.Generator.norm_le_one_of_psd (posSemidef_conjTranspose_mul_self G) hGG1
  have hnG' : ‖G * Gᴴ‖ ≤ 1 := by
    have e1 := Matrix.l2_opNorm_conjTranspose_mul_self G
    have e2 := Matrix.l2_opNorm_conjTranspose_mul_self Gᴴ
    rw [conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at e2
    rw [e2, ← e1]; exact hnG
  have h1 : (1 - G * Gᴴ).PosSemidef :=
    Transmission.LawForced.one_sub_posSemidef_of_norm_le (isHermitian_mul_conjTranspose_self G)
      hnG'
  have hFG : F * G = G := by rw [hGdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hFF]
  have h2 := (h1.conjTranspose_mul_mul_same F).trace_nonneg
  have h2' : 0 ≤ ((Fᴴ * (1 - G * Gᴴ) * F).trace).re := (Complex.nonneg_iff.1 h2).1
  have eT : (Fᴴ * (1 - G * Gᴴ) * F).trace = F.trace - (G * Gᴴ).trace := by
    have hGF : Gᴴ * F = Gᴴ := by
      have := congrArg conjTranspose hFG
      rwa [conjTranspose_mul, hFH] at this
    have hX : F * (G * Gᴴ) * F = G * Gᴴ := by
      rw [← Matrix.mul_assoc, hFG, Matrix.mul_assoc, hGF]
    rw [sandwich_one_sub F (G * Gᴴ) hFH hFF hX, trace_sub]
  -- the trace of `F`
  have hTF : (F.trace).re = (W : ℝ) - ((omittedProj b E h W (closeLen s W) ω).trace).re := by
    have t1 : (nsᴴ * ns).trace = (W : ℂ) := by
      rw [trace_mul_comm, hnn, trace_one, Fintype.card_fin]
    have t2 : (Piᴴ * Pi).trace = (omittedProj b E h W (closeLen s W) ω).trace := by
      rw [trace_mul_comm, hPi, trace_farEmbed]
    rw [hFdef, trace_sub, trace_sub, trace_one, t1, t2, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
    simp only [Complex.sub_re, Complex.natCast_re, Nat.cast_mul, Nat.cast_ofNat]
    rw [show ((2 : ℂ) * (W : ℂ)).re = 2 * (W : ℝ) by simp]
    ring
  -- assemble
  rw [GramStepU.oneLeak, hoS]
  have eL : (1 - M * nsᴴ * (M * nsᴴ)ᴴ).trace = (Gᴴ * G).trace := by
    rw [← hP, trace_sub, trace_sub, trace_mul_comm (M * nsᴴ)]
  rw [eL, trace_mul_comm, ← hTF]
  rw [eT, Complex.sub_re] at h2'
  linarith

/-- **On the cap event the retained trace is at most `K`**: `W − Re Tr A = #{t_k > h²} ≤ K`. -/
theorem retained_le_of_cap (b E s h : ℝ) (K : ℕ) (ω : GrowthPath W)
    (hcap : ∀ k, K ≤ k → physTseq b E s W ω k ≤ h ^ 2) :
    (W : ℝ) - ((omittedProj b E h W (closeLen s W) ω).trace).re ≤ K := by
  set hT := isHermitian_farTransmission b E W (closeLen s W) ω
  set g : ℝ → ℝ := fun t => if h ^ 2 < t then 1 else 0 with hg
  have hsum : (W : ℝ) - ((omittedProj b E h W (closeLen s W) ω).trace).re =
      ∑ i, g (hT.eigenvalues i) := by
    rw [omittedProj, ClosedFeas.trace_cfc hT, Complex.re_sum]
    simp only [Complex.ofReal_re]
    rw [show (W : ℝ) = ∑ _i : Fin W, (1 : ℝ) by simp, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hg, omitIndicator]
    split_ifs with h1 h2 <;> linarith
  rw [hsum]
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin W)))
  have h1 : ∑ i, g (hT.eigenvalues i) = ∑ j, g (hT.eigenvalues₀ j) :=
    Equiv.sum_comp e.symm (fun j => g (hT.eigenvalues₀ j))
  have h2 : ∑ j, g (hT.eigenvalues₀ j) =
      ∑ k ∈ Finset.range (Fintype.card (Fin W)), g (physTseq b E s W ω k) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => by simp only [physTseq, j.isLt, ↓reduceDIte]
  rw [h1, h2]
  have hz : ∀ k ∈ Finset.range (Fintype.card (Fin W)), g (physTseq b E s W ω k) ≠ 0 → k < K := by
    intro k _ hk
    by_contra hK
    exact hk (by simp [hg, not_lt.2 (hcap k (not_lt.1 hK))])
  rw [← Finset.sum_filter_of_ne hz]
  calc ∑ k ∈ (Finset.range (Fintype.card (Fin W))).filter (· < K), g (physTseq b E s W ω k)
      ≤ ∑ k ∈ (Finset.range (Fintype.card (Fin W))).filter (· < K), (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => by simp only [hg]; split_ifs <;> norm_num
    _ = (((Finset.range (Fintype.card (Fin W))).filter (· < K)).card : ℝ) := by simp
    _ ≤ K := by
        have : ((Finset.range (Fintype.card (Fin W))).filter (· < K)).card ≤ K :=
          (Finset.card_le_card fun k hk => Finset.mem_range.2 (Finset.mem_filter.1 hk).2).trans
            (Finset.card_range K).le
        exact_mod_cast this

/-- **`ClosedLeakBound` holds** (`C_T = K`): on the cap event, almost surely,
`Tr(1 − SS*)(X_cl,j) ≤ W − Re Tr A ≤ K`. -/
theorem closedLeakBound_holds : ClosedLeakBound := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨⟨hb0, hb, hE1, hE2, -⟩, -, -, hh0, hh1, -⟩ := hD
  have hh : h ^ 2 < 1 := by nlinarith
  have hη := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  refine ⟨K, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with W hW j hj
  have hq : Measure.QuasiMeasurePreserving (fun y : ProbedPath W np × ℝ => y.1.1)
      (closedLaw b W np) (growthPathLaw W b) :=
    (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)).comp
      (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw W np b))
  filter_upwards [ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW,
    ae_closedPhase_good (W := W) (np := np) b E s h j,
    hq.ae (ClosedReduce.ae_physCapEvent_iff hb hE1 hE2 hW s h K)] with y hP hQ hcapI hy
  obtain ⟨hA, hF, -, hS⟩ := hP
  obtain ⟨h1, -, -, h4⟩ := hQ
  have hR := h4.resolve_left (isUnit_closedR0 b E h s j y.1.1 hA hη (hF j)).ne_zero
  have hcap := ClosedFeas.physTseq_le_of_cap (hS (closeLen s W)) (hcapI.1 hy.1)
  exact (oneLeak_closedNearX_le b E s h hh j y.1.1 y.2 (hS j) (isUnit_iff_ne_zero.2 h1)
    (isUnit_iff_ne_zero.2 hR)).trans (retained_le_of_cap b E s h K y.1.1 hcap)

/-!
## The closed-update argument with only the update and the jet as hypotheses
-/

/-- **`ClosedGramStepFourSmall` from the closed update and the jet hypothesis** (the frame and
leak bounds are proved here). -/
theorem closedGramStepFourSmall_of_update (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hU : ClosedGramUpdate) (hJ : ClosedJet0Fam) :
    ClosedGramStepFourSmall :=
  closedGramStepFourSmall_of_closed hGA hLp hU closedNearVBound_holds closedLeakBound_holds
    (closedJetStopSmall_of_fam hJ)

/-- **`ClosedGramStepFourAt` from the closed update and the jet hypothesis.** -/
theorem closedGramStepFourAt_of_update (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hU : ClosedGramUpdate) (hJ : ClosedJet0Fam) :
    ClosedGramStepFourAt :=
  closedGramStepFourAt_of_closed hGA hLp hU closedNearVBound_holds closedLeakBound_holds
    (closedJetStopHalf_of_fam hJ)

end BlockBand.SourceProcess.PhysApprox.B3
