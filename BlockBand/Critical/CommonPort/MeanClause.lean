module

public import BlockBand.Critical.CommonPort.MeanAssembly

/-!
# Common-port mean: the `mean` clause and the constructor of `CommonPortMeanContract`

Law: `layerLaw W b .common`, conditional on the deformation (every deterministic Hermitian `X`).
The `mean` clause holds on the fixed small regularity domain `δ = matchedDistance b e X ≤ δ₀`.

* `matrixExpect_K_toBlocks11`: `E[K N₁₁ Kᴴ] = K (E N)₁₁ Kᴴ` (Bochner integrable `N`).
* `meqTop_common_eq_cmp`: the top block `-e - X - diag(c ḡ_a + b ḡ_p)` in the `cmpTopH` form.
* **`commonPortMean_mean`**: the `mean` field of `Critical.CommonPortMeanContract`.
* **`commonPortMean_holds`**: the constructor of `Critical.CommonPortMeanContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.CommonPort

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical BlockBand.Layers
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator

/-- `E[K N₁₁ Kᴴ] = K (E N)₁₁ Kᴴ` for Bochner integrable `N` (entrywise expectations). -/
theorem matrixExpect_K_toBlocks11 {Ω n m : Type*} [MeasurableSpace Ω] [Fintype n]
    [DecidableEq n] [Fintype m] [DecidableEq m] {ν : Measure Ω}
    {N : Ω → Matrix (n ⊕ m) (n ⊕ m) ℂ} (hN : Integrable N ν) (K : Matrix n n ℂ) :
    matrixExpect ν (fun ω => K * (N ω).toBlocks₁₁ * Kᴴ) =
      K * (matrixExpect ν N).toBlocks₁₁ * Kᴴ := by
  let Φl : Matrix (n ⊕ m) (n ⊕ m) ℂ →ₗ[ℂ] Matrix n n ℂ :=
    { toFun := fun A => K * A.toBlocks₁₁ * Kᴴ
      map_add' := fun A B => by
        have : (A + B).toBlocks₁₁ = A.toBlocks₁₁ + B.toBlocks₁₁ := by ext; rfl
        rw [this, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c A => by
        have : (c • A).toBlocks₁₁ = c • A.toBlocks₁₁ := by ext; rfl
        rw [this, Matrix.mul_smul, Matrix.smul_mul]; rfl }
  let Φ := LinearMap.toContinuousLinearMap Φl
  have hΦ : ∀ A, Φ A = K * A.toBlocks₁₁ * Kᴴ := fun A => rfl
  have hi : Integrable (fun ω => K * (N ω).toBlocks₁₁ * Kᴴ) ν := by
    simpa only [hΦ] using Φ.integrable_comp hN
  rw [meq_matrixExpect_eq hi, meq_matrixExpect_eq hN, ← hΦ]
  simpa only [hΦ] using Φ.integral_comp_comm hN

/-- The top block of `𝒟 - 𝒮_{c,b}(g)` for the common port in the `cmpTopH` form. -/
theorem meqTop_common_eq_cmp {W : ℕ} (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (gA : Fin LayerShape.common.blocks → ℂ) (gP : Fin LayerShape.common.ports → ℂ) :
    meqTop .common e X (1 - 2 * (b : ℂ)) b gA gP =
      cmpTopH e X - diagonal (cmpExt fun j => ((1 - 2 * b : ℝ) : ℂ) * gA j + (b : ℂ) * gP 0) := by
  rw [meqTop_common]
  unfold cmpTopH
  congr 2
  funext p
  simp only [cmpExt]
  push_cast
  ring

/-- **Common-port mean, `mean` clause.**
Law `layerLaw W b .common` (conditional on the deformation: every deterministic Hermitian `X`).
Quantifiers:
`0 < b < 1/2`, `κ > 0` first, then `δ₀ > 0, C, W₀`; uniformly in `W ≥ W₀`, Hermitian
`X` and `e ∈ bulkInterval κ` with `δ = matchedDistance b e X ≤ δ₀`: the entries of `LL*` are
integrable and `‖E(LL*) - γ I_{2W}‖ ≤ C (δ + W⁻²)` (operator norm, entrywise `matrixExpect`,
`γ = (1-b)/c`).
Hypotheses: `GaussianAbsorptionContract` (also for the unweighted covariances, via
`traceCovariance_holds`) and `LayerComparisonContract` (common part: the one-resolvent means are
within `C W⁻²` of a comparison solution within `C δ` of `a`). Other inputs: `twoResolvent_equation`,
`meanEquation_holds`, `commonPort_residuals` (with `weightedCov_holds`), `mean_assembly`,
`commonPortMean_moments`.
-/
theorem commonPortMean_mean (hGA : GaussianAbsorptionContract) (hLC : LayerComparisonContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
      ∃ (δ₀ C : ℝ) (W₀ : ℕ), 0 < δ₀ ∧
        ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
          X.IsHermitian → ∀ e ∈ bulkInterval κ, matchedDistance b e X ≤ δ₀ →
            (∀ x y, Integrable (fun ω => commonPortLL b e X ω x y) (layerLaw W b .common)) ∧
            ‖matrixExpect (layerLaw W b .common) (commonPortLL b e X) -
                ((commonPortGamma b : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ ≤
              C * (matchedDistance b e X + 1 / (W : ℝ) ^ 2) := by
  intro b hb0 hb1 κ hκ
  by_cases hκ2 : 2 < κ
  · refine ⟨1, 0, 0, one_pos, fun W _ _ X _ e he => ?_⟩
    exact absurd (le_trans he.1 he.2) (by linarith)
  push Not at hκ2
  set η₀ : ℝ := (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 with hη₀
  have hη0 : 0 < η₀ := by
    have hs := Real.sqrt_pos.mpr (BlockBand.Layers.four_sub_sq_pos hκ (by linarith))
    have : 0 < 1 - 2 * b := by linarith
    positivity
  obtain ⟨α₀, hα₀, -, hbulk⟩ := cmp_bulk_setup hκ
  obtain ⟨dstar, CL₀, WL, hdstar, hLC'⟩ := hLC b hb0 hb1 κ hκ
  obtain ⟨CR, WR, hCR0, hres⟩ := commonPort_residuals hGA b hb0 hb1 κ hκ
  obtain ⟨ε₁, CG, hε₁, hCG, hGA'⟩ := hGA b hb0 hb1 η₀ 3 hη0
  obtain ⟨WME, hME⟩ := meanEquation_holds hGA b hb0 hb1 η₀ 3 hη0
  obtain ⟨CLL, WLL, hmomL⟩ := commonPortMean_moments hGA b hb0 hb1 κ hκ 2 (by norm_num)
  set Cg : ℝ := max CL₀ 1 with hCg
  have hCg0 : 0 ≤ Cg := zero_le_one.trans (le_max_right _ _)
  set Cr : ℝ := 2 * CR with hCr
  have hCr0 : 0 ≤ Cr := by positivity
  set T₀ : ℝ := CG ^ 2 with hT₀
  have hT₀0 : 0 ≤ T₀ := by positivity
  set Sm : ℝ := asmSmall b α₀ Cg with hSm
  have hSm0 : 0 ≤ Sm := asmSmall_nonneg hb0 hb1 hα₀ hCg0
  set ε₀ : ℝ := 1 / (Sm + 1) with hε₀
  have hε₀0 : 0 < ε₀ := by positivity
  refine ⟨min dstar (ε₀ / 2), asmConst b α₀ Cg Cr T₀,
    max (max (max WL WR) (max WME WLL)) (max ⌈(3 : ℝ) / ε₁⌉₊ ⌈2 / ε₀⌉₊),
    lt_min hdstar (by positivity), ?_⟩
  intro W hW hW₀ X hX e he hδ
  have hWL : WL ≤ W := le_trans (by simp) hW₀
  have hWR : WR ≤ W := le_trans (by simp) hW₀
  have hWME : WME ≤ W := le_trans (by simp) hW₀
  have hWLL : WLL ≤ W := le_trans (by simp) hW₀
  have hW3 : ⌈(3 : ℝ) / ε₁⌉₊ ≤ W := le_trans (by simp) hW₀
  have hW2 : ⌈2 / ε₀⌉₊ ≤ W := le_trans (by simp) hW₀
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h3W : (3 : ℝ) ≤ ε₁ * W := by
    have h1 : (3 : ℝ) / ε₁ ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hW3)
    rw [div_le_iff₀ hε₁] at h1; linarith
  -- the error scale
  set δ := matchedDistance b e X with hδdef
  have hδ0 : 0 ≤ δ := by
    rw [hδdef]; unfold matchedDistance; exact (norm_nonneg _).trans (le_max_left _ _)
  set ε : ℝ := δ + 1 / (W : ℝ) ^ 2 with hεdef
  have hW2' : 1 / (W : ℝ) ^ 2 ≤ ε₀ / 2 := by
    have h1 : 2 / ε₀ ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hW2)
    have h2 : 1 / (W : ℝ) ^ 2 ≤ 1 / W := by
      rw [div_le_div_iff₀ (by positivity) hW']; nlinarith
    have h3 : 1 / (W : ℝ) ≤ ε₀ / 2 := by
      rw [div_le_iff₀ hW']; rw [div_le_iff₀ hε₀0] at h1; linarith
    linarith
  have hiW : 0 ≤ 1 / (W : ℝ) ^ 2 := by positivity
  have hε0 : 0 ≤ ε := by rw [hεdef]; linarith
  have hδε : δ ≤ ε := by rw [hεdef]; linarith
  have hiWε : 1 / (W : ℝ) ^ 2 ≤ ε := by rw [hεdef]; linarith
  have hsm : Sm * ε ≤ 1 := by
    have hεε : ε ≤ ε₀ := by
      have := hδ.trans (min_le_right _ _); rw [hεdef]; linarith
    calc Sm * ε ≤ Sm * ε₀ := mul_le_mul_of_nonneg_left hεε hSm0
      _ = Sm / (Sm + 1) := by rw [hε₀]; ring
      _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  -- bulk facts
  obtain ⟨heabs, ha1, haim⟩ := hbulk e he
  have hzim : η₀ ≤ (commonZ b e).im := commonZ_im_ge_of_mem_bulkInterval hb1.le hκ he
  have hznorm : ‖commonZ b e‖ ≤ 3 := norm_commonZ_le hb0.le (by linarith) heabs.le
  have hz0 : 0 ≤ (commonZ b e).im := hη0.le.trans hzim
  obtain ⟨hinv, hmom⟩ := hGA' W hW .common X hX e (commonZ b e) hzim hznorm
  have := bond_isProbabilityMeasure_layerLaw W b .common
  set ν := layerLaw W b .common with hν
  set G := commonPortResolvent b e X with hGdef
  set P : Matrix (LayerSite W .common) (LayerSite W .common) ℂ := meqPortProj 0 with hPdef
  set F : LayerSample W .common → Matrix (LayerSite W .common) (LayerSite W .common) ℂ :=
    fun ω => G ω * P * (G ω)ᴴ with hFdef
  set K := matchedLeadK b e X with hKdef
  have hGm : Measurable G := measurable_layerResolvent .common e (commonZ b e) X
  -- moments of `𝒢`
  have hG3 : Integrable (fun ω => ‖G ω‖ ^ 3) ν := by
    have h := hmom 3 (by norm_num) h3W
    have h' : eLpNorm (fun ω => ‖G ω‖) (ENNReal.ofReal ((3 : ℕ) : ℝ)) ν ≤ ENNReal.ofReal CG := by
      rw [Nat.cast_ofNat]; exact h
    exact (tcv_moment (by norm_num : 1 ≤ 3) hCG.le h').1
  have hG2 : Integrable (fun ω => ‖G ω‖ ^ 2) ν ∧ ∫ ω, ‖G ω‖ ^ 2 ∂ν ≤ CG ^ 2 := by
    have h := hmom 2 (by norm_num) (by linarith)
    have h' : eLpNorm (fun ω => ‖G ω‖) (ENNReal.ofReal ((2 : ℕ) : ℝ)) ν ≤ ENNReal.ofReal CG := by
      rw [Nat.cast_ofNat]; exact h
    exact tcv_moment (by norm_num : 1 ≤ 2) hCG.le h'
  obtain ⟨hGi, hFi, -, -, -⟩ := sd_integrability (P := P) hGm norm_commonP_le hG3
  -- the one-resolvent mean equation
  have hme := hME W hW hWME .common X hX e (commonZ b e) hzim hznorm
  have hG : (cmpTopH e X - diagonal (cmpExt fun j => ((1 - 2 * b : ℝ) : ℂ) *
        meqMeanA ν G j + (b : ℂ) * meqMeanP ν G 0)) * (matrixExpect ν G).toBlocks₁₁ =
      1 + meqResidTop ν (1 - 2 * (b : ℂ)) b G := by
    have h := (meq_blocks hme).1
    rw [meq_resid_toBlocks11, meqTop_common_eq_cmp] at h
    exact h
  -- the two-resolvent equation
  have h2 : (tflConst .common e (commonZ b e) X -
        meqShift .common (1 - 2 * (b : ℂ)) b (meqMeanA ν G) (meqMeanP ν G)) * matrixExpect ν F =
      P * matrixExpect ν (fun ω => (G ω)ᴴ) +
        meqShift .common (1 - 2 * (b : ℂ)) b (meqMeanA ν F) (meqMeanP ν F) *
          matrixExpect ν (fun ω => (G ω)ᴴ) +
        sdResid ν (1 - 2 * (b : ℂ)) b G F + sdResid ν (1 - 2 * (b : ℂ)) b F (fun ω => (G ω)ᴴ) :=
    twoResolvent_equation hW hb0.le hb1.le hX e hz0 P hinv hG3
  set R : Matrix (LayerSite W .common) (LayerSite W .common) ℂ :=
    sdResid ν (1 - 2 * (b : ℂ)) b G F + sdResid ν (1 - 2 * (b : ℂ)) b F (fun ω => (G ω)ᴴ)
    with hRdef
  have h2' : (tflConst .common e (commonZ b e) X -
        meqShift .common (1 - 2 * (b : ℂ)) b (meqMeanA ν G) (meqMeanP ν G)) * matrixExpect ν F =
      (meqPortProj 0 + meqShift .common (1 - 2 * (b : ℂ)) b (meqMeanA ν F) (meqMeanP ν F)) *
        matrixExpect ν (fun ω => (G ω)ᴴ) + R := by
    rw [h2, Matrix.add_mul, hRdef]; abel
  have hEH : matrixExpect ν (fun ω => (G ω)ᴴ) = (matrixExpect ν G)ᴴ :=
    matrixExpect_conjTranspose G
  set F11 := (matrixExpect ν F).toBlocks₁₁ with hF11
  set G11 := (matrixExpect ν G).toBlocks₁₁ with hG11
  have htA : ∀ j, meqMeanA ν F j = blockTrace F11 j := fun j => by
    rw [← meq_physBlockTrace_matrixExpect hFi j]; rfl
  set tp : ℂ := meqMeanP ν F 0 with htpdef
  have hF : (cmpTopH e X - diagonal (cmpExt fun j => ((1 - 2 * b : ℝ) : ℂ) *
        meqMeanA ν G j + (b : ℂ) * meqMeanP ν G 0)) * F11 =
      diagonal (cmpExt fun j => ((1 - 2 * b : ℝ) : ℂ) * blockTrace F11 j + (b : ℂ) * tp) *
        G11ᴴ + R.toBlocks₁₁ := by
    have h := two_res_top h2'
    rw [meqTop_common_eq_cmp, hEH, toBlocks11_conjTranspose] at h
    rw [h]
    congr 3
    funext p
    simp only [cmpExt, htA, htpdef]
    push_cast
    ring
  have htp : (commonZ b e - (b : ℂ) * (meqMeanA ν G 0 + meqMeanA ν G 1)) * tp =
      (1 + (b : ℂ) * (blockTrace F11 0 + blockTrace F11 1)) * conj (meqMeanP ν G 0) +
        portBlockTrace R 0 := by
    have h := two_res_port h2'
    rw [hEH, portBlockTrace_conjTranspose, meq_portBlockTrace_matrixExpect hGi,
      meq_portBlockTrace_matrixExpect hFi, htA, htA] at h
    exact h
  set RK := (R * (padTop K)ᴴ).toBlocks₁₁ with hRKdef
  have hRK : R.toBlocks₁₁ * Kᴴ = RK := (toBlocks11_mul_padTop_conj R K).symm
  -- residual bounds
  obtain ⟨r1, r2, r3, r4, r5⟩ := hres W hW hWR X hX e he
  have hCRε : CR / (W : ℝ) ^ 2 ≤ CR * ε := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hiWε hCR0
  have hRn : ‖R‖ ≤ Cr * ε := by
    refine (norm_add_le _ _).trans ?_
    rw [hCr]; linarith only [r1, r2, hCRε]
  have hR11 : ‖R.toBlocks₁₁‖ ≤ Cr * ε := (lct_norm_toBlocks11_le R).trans hRn
  have hRKn : ‖RK‖ ≤ Cr * ε := by
    refine (lct_norm_toBlocks11_le _).trans ?_
    rw [hRdef, Matrix.add_mul]
    refine (norm_add_le _ _).trans ?_
    rw [hCr]; linarith only [r3, r4, hCRε]
  have hR0 : ‖meqResidTop ν (1 - 2 * (b : ℂ)) b G‖ ≤ Cr * ε := by
    have h0 : 0 ≤ CR * ε := mul_nonneg hCR0 hε0
    rw [hCr]; linarith only [r5, hCRε, h0]
  have hrp : ‖portBlockTrace R 0‖ ≤ Cr * ε := (meq_norm_portBlockTrace_le R 0).trans hRn
  -- comparison of the means
  obtain ⟨-, m, u₀, -, -, -, hm, hu, hgm, hgu⟩ :=
    hLC' W hW hWL X hX e he (hδ.trans (min_le_left _ _))
  have hCLε : CL₀ * δ + CL₀ / (W : ℝ) ^ 2 ≤ Cg * ε := by
    have h1 : CL₀ * δ ≤ Cg * δ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0
    have h2 : CL₀ / (W : ℝ) ^ 2 ≤ Cg / (W : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
    have h3 : Cg * ε = Cg * δ + Cg / (W : ℝ) ^ 2 := by rw [hεdef]; ring
    linarith only [h1, h2, h3]
  have hg : ∀ j, ‖meqMeanA ν G j - matchedA e‖ ≤ Cg * ε := by
    intro j
    have h := (norm_sub_le_norm_sub_add_norm_sub (meqMeanA ν G j) (m j) (matchedA e)).trans
      (add_le_add (hgm j) (hm j))
    linarith only [h, hCLε]
  have hgp : ‖meqMeanP ν G 0 - matchedA e‖ ≤ Cg * ε := by
    have h := (norm_sub_le_norm_sub_add_norm_sub (meqMeanP ν G 0) u₀ (matchedA e)).trans
      (add_le_add hgu hu)
    linarith only [h, hCLε]
  -- a priori bounds on the traces of `F̄`
  have hEF : ‖matrixExpect ν F‖ ≤ T₀ := by
    refine (norm_matrixExpect_le hFi).trans ?_
    refine (integral_mono hFi.norm hG2.1 fun ω => ?_).trans hG2.2
    refine (norm_mul_le _ _).trans ?_
    rw [l2_opNorm_conjTranspose]
    calc ‖G ω * P‖ * ‖G ω‖ ≤ ‖G ω‖ * 1 * ‖G ω‖ := by
          gcongr; exact (norm_mul_le _ _).trans (by gcongr; exact norm_commonP_le)
      _ = ‖G ω‖ ^ 2 := by ring
  have ht0 : ∀ j, ‖blockTrace F11 j‖ ≤ T₀ := fun j =>
    (lct_norm_blockTrace_le _ j).trans ((lct_norm_toBlocks11_le _).trans hEF)
  have htp0 : ‖tp‖ ≤ T₀ := by
    rw [htpdef, ← meq_portBlockTrace_matrixExpect hFi]
    exact (meq_norm_portBlockTrace_le _ 0).trans hEF
  -- integrability and `E[LL*] = K F̄₁₁ Kᴴ`
  have hL2 : MemLp (fun ω => ‖commonPortL b e X ω‖) 2 ν := by
    have := (hmomL W hW hWLL X hX e he).1
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact lt_of_le_of_lt this ENNReal.ofReal_lt_top
  refine ⟨integrable_commonPortLL_entry b e X hL2, ?_⟩
  have hELL : matrixExpect ν (commonPortLL b e X) = K * F11 * Kᴴ := by
    have : commonPortLL b e X = fun ω => K * (F ω).toBlocks₁₁ * Kᴴ := by
      funext ω; exact commonPortLL_eq_K b e X ω
    rw [this, matrixExpect_K_toBlocks11 hFi K]
  rw [hELL]
  exact mean_assembly hb0 hb1 heabs ha1 hα₀ haim hX (meqMeanA ν G) (meqMeanP ν G 0) tp
    (portBlockTrace R 0) G11 F11 (meqResidTop ν (1 - 2 * (b : ℂ)) b G) R.toBlocks₁₁
    RK hG hF htp hRK hCg0 hCr0 hT₀0 hε0 hg hgp hR0 hR11 hRKn hrp ht0
    htp0 hδε hsm

/-- Law `layerLaw W b.common`, conditional on the deformation (every
deterministic Hermitian `X`); quantifiers and uniformity are those of the fields of
`CommonPortMeanContract`.
Hypotheses:
`Layers.GaussianAbsorptionContract` (all three fields),
`Layers.LayerComparisonContract` (common-port comparison, `mean`).
-/
theorem commonPortMean_holds (hGA : GaussianAbsorptionContract) (hLC : LayerComparisonContract) :
    CommonPortMeanContract where
  mean := commonPortMean_mean hGA hLC
  fluctuation := commonPortMean_fluctuation hGA
  moments := commonPortMean_moments hGA

end BlockBand.Critical.CommonPort
