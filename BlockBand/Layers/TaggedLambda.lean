module

public import BlockBand.Layers.TaggedDecayPair
public import BlockBand.Layers.FullEnergyTrace

/-!
# `TgtLambdaBound`: `‖λ_{eg}‖_q ≤ C_q`, and the assembly of the tagged-trace lemma

The second half of the tagged base case of the tagged-trace lemma.

## Proof

1. **Transfer and coordinates** (`tdl_eLpNorm_lambda`, `tdl_lam_assemble`): under the edge
   splitting `λ_{eg} = W⁻¹ Tr R_e⁰* B_{eg} R_e⁰` has the law of
   `W⁻¹ Tr R⁰* (P' + S_π) R⁰` under `rpLaw W b s ⊗ pathLaw W (n-2) b`, with `R⁰ = tdcPairRes`,
   `P' = (P_g)_{SS}` and `S_π = K*YK`, `Y` the tagged source of the exterior path
   (`tdc_source_eq`; the identification of `C*(H_R - E)⁻¹P_g(H_R - E)⁻¹C` with the tagged clock).
2. **Direct injection**: `|W⁻¹ Tr R⁰* P' R⁰| ≤ 2‖R⁰‖² ≤ 2/(Im sμ)²`.
3. **Residual clock** (`tdl_pair_clock`): `R⁰ = G*`, `G = (V - E - X - sa)⁻¹` normal, so
   `W⁻¹ Tr R⁰* S R⁰ = W⁻¹ Tr G* S G = u_G`, and `‖u_G‖_{L^q(rpLaw)} ≤ 2 E u_G ≤ 2 C₃ u`
   (`fetT_uG_Lp`, `fetT_uG_mean` of `BlockBand.Layers.FullEnergyTrace`: Ward identity, matrix mean
   identity, Gaussian `L^q` gradient inequality; **no operator-norm moments of `V`**), for every
   Hermitian `X`, `u = W⁻¹ Tr Y`.
4. **Fubini over the path** and the clock moments `‖W⁻¹ Tr Y‖_{L^q(pathLaw)} ≤ C`
   (`tdc_path_clock`, the clock-moments lemma; the tag covers the two exterior blocks `g, g+1`).

## Main results

* `tgtLambdaBound_holds (hcount) (hgrad) : TgtLambdaBound` (no further hypothesis);
* `taggedTrace_of_fet (hcount) (hgrad) (FetResidualBound) : TaggedTraceStatement`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.Inputs (GaussianLpGradient ConditionalBlockGUECount
  gaussianProduct)
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. Deterministic facts
-/

section Det

variable {W : ℕ}

/-- `‖z‖ = Re z` for `0 ≤ z` in `ℂ`. -/
theorem tdl_norm_of_nonneg {z : ℂ} (hz : 0 ≤ z) : ‖z‖ = z.re := by
  obtain ⟨h1, h2⟩ := Complex.nonneg_iff.mp hz
  have e : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h2])
  rw [e, Complex.norm_real, Real.norm_of_nonneg h1]
  simp

/-- `W⁻¹ Tr M = Σ_i W⁻¹ Tr_i M` on `Fin 2 × Fin W`. -/
theorem tdl_trace_eq_blockTrace (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (W : ℂ)⁻¹ * M.trace = blockTrace M 0 + blockTrace M 1 := by
  unfold blockTrace Matrix.trace
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, mul_add]
  rfl

theorem tdl_norm_trace_le (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ‖(W : ℂ)⁻¹ * M.trace‖ ≤ 2 * ‖M‖ := by
  rw [tdl_trace_eq_blockTrace]
  refine (norm_add_le _ _).trans ?_
  have := lct_norm_blockTrace_le M 0
  have := lct_norm_blockTrace_le M 1
  linarith

theorem tdl_trace_submatrix {m n : Type*} [Fintype m] [Fintype n] (σ : m ≃ n)
    (M : Matrix n n ℂ) : (M.submatrix σ σ).trace = M.trace := by
  unfold Matrix.trace
  simp only [submatrix_apply, diag_apply]
  exact Equiv.sum_comp σ (fun j => M j j)

end Det

/-!
## 2. The residual clock of the final pair
-/

/-- The constant of `fetT_uG_mean` with `16/W` replaced by `16` (`W ≥ 1`). -/
def tdlC3 (s y Cg : ℝ) : ℝ :=
  2 * (s * y)⁻¹ * (1 + 2 * ((s * y)⁻¹ + 1) * (1 + 2 * ((s * y)⁻¹ + 1) * (s * y)⁻¹)) +
    ((s * y)⁻¹ * (1 + 2 * ((s * y)⁻¹ + 1) * (s * y)⁻¹)) ^ 2 *
      (16 * (Cg * Real.sqrt 2 * 16 * (s * y)⁻¹ ^ 2) ^ 2)

theorem tdlC3_nonneg {s y Cg : ℝ} (hs : 0 < s) (hy : 0 < y) : 0 ≤ tdlC3 s y Cg := by
  unfold tdlC3
  have : 0 < s * y := mul_pos hs hy
  positivity

theorem tdl_C3_le {s y Cg : ℝ} (hs : 0 < s) (hy : 0 < y) {W : ℕ} (hW : 0 < W) :
    2 * (s * y)⁻¹ * (1 + 2 * ((s * y)⁻¹ + 1) * (1 + 2 * ((s * y)⁻¹ + 1) * (s * y)⁻¹)) +
        ((s * y)⁻¹ * (1 + 2 * ((s * y)⁻¹ + 1) * (s * y)⁻¹)) ^ 2 *
          (16 * (Cg * Real.sqrt 2 * (16 / W) * (s * y)⁻¹ ^ 2) ^ 2) ≤ tdlC3 s y Cg := by
  unfold tdlC3
  have hsy : 0 < s * y := mul_pos hs hy
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h16 : 16 / (W : ℝ) ≤ 16 := by rw [div_le_iff₀ (by linarith)]; linarith
  have h160 : 0 ≤ 16 / (W : ℝ) := by positivity
  have hsq : (Cg * Real.sqrt 2 * (16 / W) * (s * y)⁻¹ ^ 2) ^ 2 ≤
      (Cg * Real.sqrt 2 * 16 * (s * y)⁻¹ ^ 2) ^ 2 := by
    have hK0 : 0 ≤ (s * y)⁻¹ ^ 2 := by positivity
    have e1 : Cg * Real.sqrt 2 * (16 / W) * (s * y)⁻¹ ^ 2 =
        (16 / W) * (Cg * Real.sqrt 2 * (s * y)⁻¹ ^ 2) := by ring
    have e2 : Cg * Real.sqrt 2 * 16 * (s * y)⁻¹ ^ 2 = 16 * (Cg * Real.sqrt 2 * (s * y)⁻¹ ^ 2) := by
      ring
    rw [e1, e2, mul_pow, mul_pow]
    have : (16 / (W : ℝ)) ^ 2 ≤ 16 ^ 2 := pow_le_pow_left₀ h160 h16 2
    have h0 : 0 ≤ (Cg * Real.sqrt 2 * (s * y)⁻¹ ^ 2) ^ 2 := sq_nonneg _
    nlinarith
  gcongr

set_option maxHeartbeats 400000 in
/-- **The residual clock of the final pair** (in the paper: "the final trace pairing with `Y`").
Law: `rpLaw W b s`, `s = min(1 - 2b, b)`, conditional on deterministic Hermitian `X` and `Y ⪰ 0`;
`S = K*YK`, `K = z_∂ - X`, `R⁰ = tdcPairRes`. After `b, κ, q ≥ 1` there are `C ≥ 0, W₀`; for
`W ≥ W₀`, every Hermitian `X` (no restriction on `d(X)`), `Y ⪰ 0`, `E ∈ bulkInterval κ`:
`‖W⁻¹ Tr R⁰* S R⁰‖_{L^q(rpLaw)} ≤ C W⁻¹ Tr Y`. Inputs: `Inputs.GaussianLpGradient` only (through
`fetT_uG_Lp`, `fetT_uG_mean`). -/
theorem tdl_pair_clock (hgrad : GaussianLpGradient) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) {q : ℝ} (hq : 1 ≤ q) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ X Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → Y.PosSemidef →
      ∀ E ∈ bulkInterval κ,
        eLpNorm (fun v : RpSample W => (W : ℂ)⁻¹ * ((tdcPairRes b E X v)ᴴ *
            ((tdcK b E X)ᴴ * Y * tdcK b E X) * tdcPairRes b E X v).trace)
          (ENNReal.ofReal q) (rpLaw W b (min (1 - 2 * b) b)) ≤
        ENNReal.ofReal (C * clkTrace Y) := by
  set s := min (1 - 2 * b) b with hsdef
  have hs : 0 < s := lt_min (by linarith) hb0
  obtain ⟨Cg, hCg0, hgr⟩ := hgrad
  obtain ⟨ya, hya0, hyaE⟩ := rp_im_a_lower hκ
  obtain ⟨η₀, hη₀, hbulk⟩ := dcv_bulk hb0 hb1 hκ
  refine ⟨2 * tdlC3 s ya Cg, ⌈24 * ((s * ya)⁻¹ * Cg) ^ 2 * q⌉₊,
    by have := tdlC3_nonneg (Cg := Cg) hs hya0; positivity, ?_⟩
  intro W hW hWW X Y hX hY E hE
  have hα : 0 ≤ rlAlpha b s := by
    unfold rlAlpha; have := min_le_left (1 - 2 * b) b; linarith
  have hβ : 0 ≤ rlBeta b s := by
    unfold rlBeta; have := min_le_right (1 - 2 * b) b; linarith
  have hα1 : rlAlpha b s ≤ 1 := by unfold rlAlpha; linarith
  have hβ1 : rlBeta b s ≤ 1 := by unfold rlBeta; linarith
  obtain ⟨hya, hE2⟩ := hyaE E hE
  have hz : 0 < (boundaryZ b E).im := lt_of_lt_of_le hη₀ (hbulk E hE).1
  have hWp : 24 * ((s * ya)⁻¹ * Cg) ^ 2 * q ≤ W :=
    (Nat.le_ceil _).trans (by exact_mod_cast hWW)
  set K := tdcK b E X with hK
  set S := Kᴴ * Y * K with hSdef
  have hS : S.PosSemidef := hY.conjTranspose_mul_mul_same K
  set ν := gaussianProduct (rlVar W b s) with hν
  have hEm := rl_measurable_embed W b s
  have hRm : Measurable (fun v : RpSample W => tdcPairRes b E X v) :=
    tdc_measurable_pairRes b E measurable_const measurable_id
  set f := fun v : RpSample W => (W : ℂ)⁻¹ * ((tdcPairRes b E X v)ᴴ * S * tdcPairRes b E X v).trace
    with hf
  have hfm : Measurable f :=
    measurable_const.mul (Continuous.measurable (continuous_id.matrix_trace) |>.comp
      (srec_measurable_mul (srec_measurable_mul (srec_measurable_conjTranspose hRm)
        measurable_const) hRm))
  -- transfer to Gaussian coordinates
  have h1 : eLpNorm f (ENNReal.ofReal q) (rpLaw W b s) = eLpNorm (f ∘ rlEmbed W b s)
      (ENNReal.ofReal q) ν := by
    rw [rl_law_eq_map]
    exact eLpNorm_map_measure hfm.aestronglyMeasurable hEm.aemeasurable
  -- the pointwise identity `|f ∘ embed| = u_G`
  have hpt : ∀ x, ‖(f ∘ rlEmbed W b s) x‖ = ‖fetTu b E s X S x‖ := by
    intro x
    set G := rlG b E s X x with hG
    have hGe : rpResolvent E s X (rlEmbed W b s x) = G := (rl_matrix_eq b E s X x).symm
    have hR : tdcPairRes b E X (rlEmbed W b s x) = Gᴴ := by
      rw [tdp_pairRes_eq hX _ (rl_embed_herm W b s x), ← hsdef, hGe]
    have hN : Gᴴ * G = G * Gᴴ := fetT_G_normal hX x
    have htr : (Gᴴᴴ * S * Gᴴ).trace = (Gᴴ * S * G).trace := by
      rw [conjTranspose_conjTranspose]
      calc (G * S * Gᴴ).trace = (Gᴴ * (G * S)).trace := Matrix.trace_mul_comm _ _
        _ = (G * Gᴴ * S).trace := by rw [← Matrix.mul_assoc, hN]
        _ = (Gᴴ * S * G).trace := by rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    have hpsd : (Gᴴ * S * G).PosSemidef := hS.conjTranspose_mul_mul_same G
    simp only [Function.comp_apply, hf, hR]
    rw [htr, norm_mul, tdl_norm_of_nonneg hpsd.trace_nonneg]
    unfold fetTu fetTct
    rw [← hG, Real.norm_of_nonneg (mul_nonneg (by positivity) (by
      have := (Complex.nonneg_iff.mp hpsd.trace_nonneg).1; exact this))]
    simp
  have hum : Continuous (fun x => fetTu b E s X S x) :=
    continuous_const.mul (fetT_ct_G_continuous hW hs hα hβ hX hya0 hya hα1 hβ1 hE2 hS hCg0.le hgr)
  have h2 : eLpNorm (f ∘ rlEmbed W b s) (ENNReal.ofReal q) ν =
      eLpNorm (fetTu b E s X S) (ENNReal.ofReal q) ν :=
    eLpNorm_congr_norm_ae (hfm.comp hEm).aestronglyMeasurable hum.aestronglyMeasurable
      (ae_of_all _ hpt)
  rw [h1, h2]
  refine (fetT_uG_Lp hW hs hα hβ hX hya0 hya hα1 hβ1 hE2 hS hCg0.le hgr hq hWp).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hm := fetT_uG_mean hW hs hα hβ hX hya0 hya hα1 hβ1 hE2 hS hCg0.le hgr
  have hRp := fetT_Rp_eq hW hs hα hβ hX hya0 hya hE2
  have hu : (W : ℝ)⁻¹ * fetTct S (fetTRp b E s X) = clkTrace Y := by
    rw [← hRp]
    unfold fetTct fetR
    rw [tdmH_Y_eq hz hX Y]
    rfl
  rw [hu] at hm
  have hC3 := tdl_C3_le (Cg := Cg) hs hya0 hW
  have hu0 := clkTrace_nonneg hY
  have := mul_le_mul_of_nonneg_right hC3 hu0
  nlinarith

/-!
## 3. Transfer and coordinates
-/

section Lambda

variable {p : Parameters}

/-- `λ_{eg}` in Schur form: `W⁻¹ Tr R_e⁰* B_{eg} R_e⁰`, `R_e⁰ = (K_e - sμ)⁻¹` (`tdcR0`). -/
def tdlLam (e g : ZMod p.n) (E : ℝ) (H : p.SiteMatrix) : ℂ :=
  (p.W : ℂ)⁻¹ * ((tdcR0 e H E)ᴴ * tgtB p e g H E * tdcR0 e H E).trace

theorem tdl_measurable_lam (e g : ZMod p.n) (E : ℝ) : Measurable (tdlLam (p := p) e g E) := by
  have hR : Measurable (fun H : p.SiteMatrix => tdcR0 e H E) :=
    measurable_matrix_inv.comp ((tdc_measurable_edgeSchur e E).sub measurable_const)
  unfold tdlLam
  exact measurable_const.mul ((Continuous.measurable continuous_id.matrix_trace).comp
    (srec_measurable_mul (srec_measurable_mul (srec_measurable_conjTranspose hR)
      (tdc_measurable_tgtB e g E)) hR))

/-- For Hermitian `H^{(e)}` with `H_R - E` invertible, `λ_{eg}` is the Schur form `tdlLam`. -/
theorem tdl_lambda_eq {e : ZMod p.n} (g : ZMod p.n) {H : p.SiteMatrix} (hH : H.IsHermitian)
    {E : ℝ} (hdet : (exteriorBlock p e H - (E : ℂ) • 1).det ≠ 0) :
    tgtLambda p e g H E = tdlLam e g E H := by
  unfold tgtLambda tgtR0 tdlLam tdcR0
  rw [BlockBand.Center.ctr_compressed_eq_schur hH hdet]
  rfl

/-- **Transfer of `λ_{eg}` to the explicit law** `rpLaw ⊗ pathLaw (n-2)` of `H^{(e)}`. -/
theorem tdl_eLpNorm_lambda {model : p.GaussianRingModel} (X : PairExtension p model)
    {e : ZMod p.n} {G : X.Ω → PairMatrix p e} (hs : IsCenterSplitting X G) (E : ℝ)
    (g : ZMod p.n) (q : ℝ≥0∞) :
    eLpNorm (fun ω => tgtLambda p e g (X.Hm ω - embedPair p e (G ω)) E) q X.P =
      eLpNorm (fun x => tdlLam e g E (assemble p e (rpSplitAssemble e x) 0)) q
        ((rpLaw p.W p.b (splitS p)).prod (pathLaw p.W (p.n - 2) p.b)) := by
  rw [← tgt_eLpNorm_residual_eq X hs (tdl_measurable_lam e g E) q]
  refine eLpNorm_congr_ae ?_
  filter_upwards [tgt_ae_residual_isHermitian X hs, tgt_ae_residual_exterior_det X hs E]
    with ω hH hd
  exact tdl_lambda_eq g hH hd

/-- **`λ_{eg}` in residual-pair and path coordinates** (deterministic):
`tdlLam = W⁻¹ Tr R⁰* (P' + S_π) R⁰` at `H^{(e)} = assemble (rpSplitAssemble x) 0`. -/
theorem tdl_lam_assemble (e g : ZMod p.n) (E : ℝ) (x : RpSample p.W × PathSample p.W (p.n - 2)) :
    tdlLam e g E (assemble p e (rpSplitAssemble e x) 0) =
      (p.W : ℂ)⁻¹ * ((tdcPairRes p.b E (pathSchur E x.2) x.1)ᴴ *
        (tdcPairProj e g + tdcPathSource E (fun j : Fin (p.n - 2) => tdcTag e g j) x.2) *
          tdcPairRes p.b E (pathSchur E x.2) x.1).trace := by
  set σ := (rpPairEquiv e).symm
  set ρ := (rpExtEquiv e).symm
  set H := assemble p e (rpSplitAssemble e x) 0
  have hK : edgeSchur p e H E =
      (rpMatrix x.1 - pathSchur E x.2 - (E : ℂ) • 1).submatrix σ σ := by
    rw [← rp_pairResidual_assemble]
    unfold edgeSchur pairResidual
    rw [tdc_ext_assemble, tdc_coup_assemble, tdc_pair_assemble]
  have hR : tdcR0 e H E = (tdcPairRes p.b E (pathSchur E x.2) x.1).submatrix σ σ := by
    unfold tdcR0 tdcPairRes
    rw [hK, tdc_sub_smul_submatrix, ← inv_submatrix_equiv]
    congr 2
    unfold tgtZeta splitS Parameters.c
    abel
  have hN : exteriorBlock p e H - (E : ℂ) • 1 = (pathMatrix x.2 - (E : ℂ) • 1).submatrix ρ ρ := by
    rw [tdc_ext_assemble, ← tdc_sub_smul_submatrix]
    rfl
  have hB : tgtB p e g H E = (tdcPairProj e g +
      tdcPathSource E (fun j : Fin (p.n - 2) => tdcTag e g j) x.2).submatrix σ σ := by
    unfold tgtB tdcPathSource
    rw [hN, tdc_coup_assemble, tdc_extProj, tdc_pairProj_eq, inv_submatrix_equiv]
    change _ + ((pathPortCoupling x.2).submatrix ρ σ)ᴴ * _ * _ * _ * (pathPortCoupling x.2).submatrix ρ σ = _
    rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_mul_equiv,
      submatrix_mul_equiv]
    rfl
  unfold tdlLam
  rw [hR, hB, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv,
    tdl_trace_submatrix]

/-- **The path-source term integrates** (Fubini over the residual pair, conditionally on the
exterior path): the conditional residual clock bound `tdl_pair_clock` and an `L^q(pathLaw)` bound
`Cu` of the clock give `‖W⁻¹ Tr R⁰* S_π R⁰‖_{L^q(rpLaw ⊗ pathLaw)} ≤ C₁ Cu`. -/
theorem tdl_T2_bound {r : ℕ} {E : ℝ} (hz : 0 < (boundaryZ p.b E).im) (τ : Fin r → Bool)
    {q : ℝ} (hq : 1 ≤ q) {C₁ Cu : ℝ} (hC₁ : 0 ≤ C₁)
    (hpc : ∀ X Y : Matrix (Fin 2 × Fin p.W) (Fin 2 × Fin p.W) ℂ, X.IsHermitian →
      Y.PosSemidef →
      eLpNorm (fun v : RpSample p.W => (p.W : ℂ)⁻¹ * ((tdcPairRes p.b E X v)ᴴ *
          ((tdcK p.b E X)ᴴ * Y * tdcK p.b E X) * tdcPairRes p.b E X v).trace)
        (ENNReal.ofReal q) (rpLaw p.W p.b (splitS p)) ≤ ENNReal.ofReal (C₁ * clkTrace Y))
    (hu : eLpNorm (fun π : PathSample p.W r => clkTrace (clkCoreSource p.b E τ π))
      (ENNReal.ofReal q) (pathLaw p.W r p.b) ≤ ENNReal.ofReal Cu) :
    eLpNorm (fun x : RpSample p.W × PathSample p.W r => (p.W : ℂ)⁻¹ *
        ((tdcPairRes p.b E (pathSchur E x.2) x.1)ᴴ * tdcPathSource E τ x.2 *
          tdcPairRes p.b E (pathSchur E x.2) x.1).trace) (ENNReal.ofReal q)
      ((rpLaw p.W p.b (splitS p)).prod (pathLaw p.W r p.b)) ≤ ENNReal.ofReal (C₁ * Cu) := by
  have hq0 : (0 : ℝ) < q := by linarith
  set T2 := fun x : RpSample p.W × PathSample p.W r => (p.W : ℂ)⁻¹ *
    ((tdcPairRes p.b E (pathSchur E x.2) x.1)ᴴ * tdcPathSource E τ x.2 *
      tdcPairRes p.b E (pathSchur E x.2) x.1).trace with hT2
  have hX2 : Measurable (fun x : RpSample p.W × PathSample p.W r => pathSchur E x.2) :=
    (measurable_pathSchur p.W r E).comp measurable_snd
  have hRm := tdc_measurable_pairRes (Ω := RpSample p.W × PathSample p.W r) p.b E hX2 measurable_fst
  have hT2m : Measurable T2 :=
    measurable_const.mul ((Continuous.measurable continuous_id.matrix_trace).comp
      (srec_measurable_mul (srec_measurable_mul (srec_measurable_conjTranspose hRm)
        ((tdc_measurable_pathSource p.W r E τ).comp measurable_snd)) hRm))
  set F : PathSample p.W r × RpSample p.W → ℝ := fun y => ‖T2 (y.2, y.1)‖ with hF
  have hFm : Measurable F := hT2m.norm.comp (measurable_snd.prodMk measurable_fst)
  have hgm : Measurable (fun π : PathSample p.W r => C₁ * clkTrace (clkCoreSource p.b E τ π)) :=
    measurable_const.mul (clk_measurable_trace (clk_measurable_coreSource p.W r p.b E τ))
  have h1 : eLpNorm T2 (ENNReal.ofReal q) ((rpLaw p.W p.b (splitS p)).prod (pathLaw p.W r p.b)) =
      eLpNorm F (ENNReal.ofReal q) ((pathLaw p.W r p.b).prod (rpLaw p.W p.b (splitS p))) := by
    rw [← eLpNorm_norm _ hT2m.aestronglyMeasurable]
    rw [← eLpNorm_comp_measurePreserving hT2m.norm.aestronglyMeasurable
      (Measure.measurePreserving_swap (μ := pathLaw p.W r p.b) (ν := rpLaw p.W p.b (splitS p)))]
    rfl
  rw [h1]
  refine (clk_eLpNorm_prod_le hFm hgm hq0 (c := 1) ?_).trans ?_
  · filter_upwards [tdc_ae_path_herm p.W r p.b E] with π ⟨hH, hX⟩
    rw [ENNReal.ofReal_one, one_mul, Real.enorm_eq_ofReal (mul_nonneg hC₁
      (clkTrace_nonneg (clkCoreSource_posSemidef p.b E τ π)))]
    have hS := tdc_source_eq hz τ π hH hX
    have e : (fun v => F (π, v)) = fun v => ‖(p.W : ℂ)⁻¹ *
        ((tdcPairRes p.b E (pathSchur E π) v)ᴴ *
        ((tdcK p.b E (pathSchur E π))ᴴ * clkCoreSource p.b E τ π * tdcK p.b E (pathSchur E π)) *
          tdcPairRes p.b E (pathSchur E π) v).trace‖ := by
      funext v; simp only [hF, hT2, tdcPathSource, hS]
    have hm : Measurable (fun v : RpSample p.W => tdcPairRes p.b E (pathSchur E π) v) :=
      tdc_measurable_pairRes p.b E measurable_const measurable_id
    rw [e, eLpNorm_norm]
    swap
    · exact (measurable_const.mul ((Continuous.measurable continuous_id.matrix_trace).comp
        (srec_measurable_mul (srec_measurable_mul (srec_measurable_conjTranspose hm)
          measurable_const) hm))).aestronglyMeasurable
    exact hpc _ _ hX (clkCoreSource_posSemidef p.b E τ π)
  · rw [ENNReal.ofReal_one, one_mul]
    exact tdc_eLpNorm_smul_le hC₁ hu

end Lambda

/-!
## 4. `TgtLambdaBound` and the assembly
-/

section Assembly

set_option maxHeartbeats 400000 in
/-- **`TgtLambdaBound`: `‖λ_{eg}‖_{L^q} ≤ C_q`** (the second half of the tagged base case).

*Statement.* `λ_{eg} = W⁻¹ Tr (R_e⁰)* B_{eg} R_e⁰` (`tgtLambda`, `R_e⁰ = (K_e - sμ)⁻¹` realized by
the compressed resolvent, `μ = ā`, `s = min(c, b)`, `B_{eg} = (P_g)_{SS} + C*(H_R - E)⁻¹(P_g)_{RR}
(H_R - E)⁻¹C`), `g ≠ e`: `‖λ_{eg}‖_{L^q(X.P)} ≤ C_q`.

*Law.* Any extension `X` of the exact physical law with an edge splitting
`IsCenterSplitting X G`; only the law of `H^{(e)}` is used, the image of
`rpLaw W b s ⊗ pathLaw W (n-2) b` (`tgt_eLpNorm_residual_eq`).

*Domain, quantifiers, uniformity.* `b ∈ (0, 1/2)`, `κ > 0`, `T`, then `q ≥ 1`, then `C_q, W₀`
(`C_q = 2/(Im sμ)²_min + C₁ C_u`, `C₁` of `tdl_pair_clock`, `C_u` of `tdc_path_clock`); uniformly in
`W > W₀`, `n ≤ TW`, the model, `e`, the extension and splitting, `E ∈ bulkInterval κ`, `g ≠ e`.
No limits are taken.

*Norms.* `L^q(X.P)` of the complex scalar; `ℓ²` operator norms and `W⁻¹ Tr` inside.

*Proof.* `λ = W⁻¹ Tr R⁰*P'R⁰ + W⁻¹ Tr R⁰* S_π R⁰` (`tdl_lam_assemble`); the first term is
`≤ 2‖R⁰‖² ≤ 2/(Im sμ)²`; the second is the residual clock of the final pair with the tagged clock
`Y` of the exterior path as source (`tdc_source_eq`), bounded conditionally by `C₁ W⁻¹ Tr Y`
(`tdl_pair_clock`) and then by the clock moments (`tdc_path_clock`, the clock-moments lemma).

*Inputs.* `ConditionalBlockGUECount` (clock moments) and `GaussianLpGradient` (clock moments;
the residual clock through `BlockBand.Layers.FullEnergyTrace`, §9). -/
theorem tgtLambdaBound_holds (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient) :
    TgtLambdaBound := by
  intro b hb0 hb1 κ T hκ q hq
  have hq0 : (0 : ℝ) < q := by linarith
  obtain ⟨y, hy, hyE⟩ := tdc_im_smu_lower hb0 hb1 hκ
  obtain ⟨η, hη, hbulk⟩ := srec_boundaryZ_im_lower (b := b) (by linarith) hκ
  obtain ⟨C₁, W₁, hC₁, hpc⟩ := tdl_pair_clock hgrad hb0 hb1 hκ hq
  obtain ⟨Cu, Wu, hCu, hclk⟩ := tdc_path_clock hcount hgrad b hb0 hb1 κ T hκ q hq
  refine ⟨2 * (y⁻¹) ^ 2 + C₁ * Cu, max (W₁ : ℝ) (Wu : ℝ), ?_⟩
  intro p hpb hnT hW model e X G hs E hE g hg
  subst hpb
  have hW₁ : W₁ ≤ p.W := by
    have : (W₁ : ℝ) < p.W := lt_of_le_of_lt (le_max_left _ _) hW
    exact_mod_cast this.le
  have hWu : Wu ≤ p.W := by
    have : (Wu : ℝ) < p.W := lt_of_le_of_lt (le_max_right _ _) hW
    exact_mod_cast this.le
  have hW0 : 0 < p.W := p.W_pos
  have hz : 0 < (boundaryZ p.b E).im := lt_of_lt_of_le hη (hbulk E hE).1
  rw [tdl_eLpNorm_lambda X hs E g _]
  set μ := (rpLaw p.W p.b (splitS p)).prod (pathLaw p.W (p.n - 2) p.b) with hμ
  have hprob : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  set τ : Fin (p.n - 2) → Bool := fun j => tdcTag e g j with hτ
  set R := fun x : RpSample p.W × PathSample p.W (p.n - 2) => tdcPairRes p.b E (pathSchur E x.2) x.1
    with hR
  have hX2 : Measurable (fun x : RpSample p.W × PathSample p.W (p.n - 2) => pathSchur E x.2) :=
    (measurable_pathSchur p.W _ E).comp measurable_snd
  have hRm : Measurable R := tdc_measurable_pairRes p.b E hX2 measurable_fst
  set T1 := fun x => (p.W : ℂ)⁻¹ * ((R x)ᴴ * tdcPairProj e g * R x).trace with hT1
  set T2 := fun x => (p.W : ℂ)⁻¹ * ((R x)ᴴ * tdcPathSource E τ x.2 * R x).trace with hT2
  have hT1m : Measurable T1 := measurable_const.mul ((Continuous.measurable
    continuous_id.matrix_trace).comp (srec_measurable_mul (srec_measurable_mul
      (srec_measurable_conjTranspose hRm) measurable_const) hRm))
  have hT2m : Measurable T2 := measurable_const.mul ((Continuous.measurable
    continuous_id.matrix_trace).comp (srec_measurable_mul (srec_measurable_mul
      (srec_measurable_conjTranspose hRm) ((tdc_measurable_pathSource p.W _ E τ).comp
        measurable_snd)) hRm))
  have hfun : ∀ x, ‖tdlLam e g E (assemble p e (rpSplitAssemble e x) 0)‖ ≤ ‖T1 x‖ + ‖T2 x‖ := by
    intro x
    rw [tdl_lam_assemble, Matrix.mul_add, Matrix.add_mul, trace_add, mul_add]
    exact norm_add_le _ _
  -- the direct injection inside the pair
  have hT1b : eLpNorm (fun x => ‖T1 x‖) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (2 * (y⁻¹) ^ 2) := by
    rw [eLpNorm_norm _ hT1m.aestronglyMeasurable]
    refine (eLpNorm_le_of_ae_bound (C := 2 * (y⁻¹) ^ 2) hT1m.aestronglyMeasurable ?_).trans ?_
    · filter_upwards [tdc_ae_prod_herm p.W (p.n - 2) p.b (splitS p) E] with x ⟨hv, hX⟩
      have hRn := tdc_norm_pairRes_le hX x.1 hv hy (hyE E hE)
      have hP := tdc_norm_pairProj_le e g
      refine (tdl_norm_trace_le _).trans ?_
      have h3 := tdm_norm_mul3_le (R x)ᴴ (tdcPairProj e g) (R x)
      rw [l2_opNorm_conjTranspose] at h3
      have hR0 := norm_nonneg (R x)
      have h4 : ‖R x‖ * ‖tdcPairProj e g‖ * ‖R x‖ ≤ (y⁻¹) ^ 2 := by
        have := mul_le_mul hRn hRn hR0 (by positivity)
        nlinarith [norm_nonneg (tdcPairProj e g)]
      linarith
    · rw [measure_univ, ENNReal.one_rpow, one_mul]
  -- the path source
  have hr : 1 ≤ p.n - 2 := by have := p.n_ge_four; omega
  have hrT : ((p.n - 2 : ℕ) : ℝ) ≤ T * p.W := by
    refine le_trans ?_ hnT
    exact_mod_cast Nat.sub_le _ _
  have htag : ∀ j, tdcTag e g j = true → j = (g - e).val - 2 ∨ j = (g - e).val - 1 :=
    fun j h => tdc_tag_pos h
  have hu := hclk p.W hWu hW0 (p.n - 2) hr hrT E hE (tdcTag e g) _ _ htag
  have hT2b : eLpNorm (fun x => ‖T2 x‖) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (C₁ * Cu) := by
    rw [eLpNorm_norm _ hT2m.aestronglyMeasurable]
    exact tdl_T2_bound hz τ hq hC₁ (fun X' Y' hX' hY' => hpc p.W hW0 hW₁ X' Y' hX' hY' E hE) hu
  have hmeasF : AEStronglyMeasurable (fun x => tdlLam e g E
      (assemble p e (rpSplitAssemble e x) 0)) μ :=
    ((tdl_measurable_lam e g E).comp ((rsl_measurable_assemble e).comp
      ((rp_measurable_splitAssemble e).prodMk measurable_const))).aestronglyMeasurable
  exact (eLpNorm_mono_real hmeasF hfun).trans (tdc_eLpNorm_add_le hq (by positivity)
    (by positivity) hT1b hT2b)

/-- **The tagged-trace lemma from `FetResidualBound`** (`TaggedTraceStatement`). Law, domain,
norms and quantifiers as in `TaggedTraceStatement`. Inputs: `ConditionalBlockGUECount`,
`GaussianLpGradient` and `FetResidualBound`; the `λ` bound is `tgtLambdaBound_holds` and the
tagged decay bound is `tgtDecayBound_of_fet`. -/
theorem taggedTrace_of_fet (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient)
    (hfet : FetResidualBound) : TaggedTraceStatement :=
  taggedTrace_of_open hcount hgrad (tgtLambdaBound_holds hcount hgrad)
    (tgtDecayBound_of_fet hcount hgrad hfet)

end Assembly

end BlockBand.Layers
