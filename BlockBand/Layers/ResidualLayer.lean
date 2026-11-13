module

public import BlockBand.Layers.ResidualLayerMeans

/-!
# The residual pair layer bound `ResidualPairLayerBound`

Step 5 of the proof of the matched-traces theorem: "The last residual Gaussian layer then has
diagonal variance `(c − s/2)/W` and internal-bond variance `(b − s/2)/W`. Its test matrix is
`(V − E − X − sa)⁻¹`, and the row sum of its mean variance is `1 − b − s`. At the matched value `a`
its inverse is again `(z − X)⁻¹`, and the stability gap ... is at least `s/(1−b)`."
`residualPairLayerBound_holds` proves `ResidualPairLayerBound` from `GaussianLpGradient`
(`ConditionalBlockGUECount` is accepted but not used: the test matrix is deterministically
bounded).

Law: `rpLaw W b s`. Quantifiers: `b ∈ (0, 1/2)`, `κ > 0`, `0 < s < 2 min(c, b)` first; then
`d_* = rlDstar`, `C`, `ε = 1`; uniformly in `W ≥ 1`, Hermitian `X`, `E ∈ bulkInterval κ`.

## Proof

1. Coordinates (`rl_law_eq_map`): `rpLaw` is the image of `gaussianProduct (rlVar W b s)`.
2. Fluctuation (`rl_fluct`, `D = P_j`): `‖W⁻¹Tr P_j G - E‖_q ≤ 16 Cg K² √q / W` for every
   `q ≥ 1`, `K = (s y_lo)⁻¹` (`y_lo ≤ -Im a` on the bulk, `rp_im_a_lower`).
3. Mean equation (`rl_resid_bound`): `m̄ = tr (H - diag σ(m̄))⁻¹ + e`, `|e_j| ≤ C_e / W²`.
4. Stability (`rl_stability`, `λ = α + β + s = 1 - b`, reference `R = (z_∂ - X)⁻¹` via
   `cmp_resolvent_eq`): `|m̄_j - a| ≤ C_s (d(X) + C_e/W²)` when `C_e/W² ≤ η_*`; otherwise the
   crude bound `|m̄_j - a| ≤ K + 1 ≤ (K + 1) C_e / (η_* W²)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct weightedGradientNorm)
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-- Transfer of the block-trace means from `rpLaw` to coordinates. -/
theorem rl_integral_transfer {W : ℕ} (b E s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (j : Fin 2) :
    ∫ ω, blockTrace (rpResolvent E s X ω) j ∂((gaussianProduct (rlVar W b s)).map (rlEmbed W b s)) =
      rlMean b E s X j := by
  have hm : Measurable (fun ω : RpSample W => blockTrace (rpResolvent E s X ω) j) :=
    srec_measurable_blockTrace (rp_measurable_resolvent E s (Xf := fun _ => X) (ωf := fun ω => ω)
      measurable_const measurable_id) j
  rw [integral_map (rl_measurable_embed W b s).aemeasurable hm.aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  rw [← rl_matrix_eq]
  rfl

theorem rl_mean_norm_le {W : ℕ} {b E s : ℝ} (hs : 0 < s)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y)
    (hya : y ≤ -(matchedA E).im) (j : Fin 2) : ‖rlMean b E s X j‖ ≤ (s * y)⁻¹ := by
  have h := norm_integral_le_of_norm_le_const (μ := gaussianProduct (rlVar W b s))
    (f := fun x => blockTrace (rlG b E s X x) j) (C := (s * y)⁻¹)
    (ae_of_all _ fun x => (lct_norm_blockTrace_le _ j).trans (rl_norm_G_le b E hs hX hy hya x))
  rwa [probReal_univ, mul_one] at h

/-- The constant of the mean-equation residual: `|e_j| ≤ rlCe / W²`. -/
def rlCe (Cg α β K : ℝ) : ℝ := 2 * (α + β) * ((Cg * Real.sqrt 2 * 16) ^ 2 * K ^ 5)

theorem rl_resid_eq {W : ℕ} (hW : 0 < W) (Cg α β K : ℝ) :
    2 * (α + β) * (rlA Cg W K K * rlA Cg W 1 K) = rlCe Cg α β K / (W : ℝ) ^ 2 := by
  have hW' : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  unfold rlA rlCe
  field_simp

/-- **Fluctuation clause on `rpLaw`**: `‖W⁻¹Tr P_j G - E‖_q ≤ 16 Cg K² √q / W`, `q ≥ 1`. -/
theorem rl_fluct_law {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
        eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
            (gaussianProduct v) ≤
          ENNReal.ofReal (Cg * Real.sqrt p) *
            eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v))
    {W : ℕ} (hW : 0 < W) {b E s : ℝ} (hs : 0 < s) (hα : 0 ≤ rlAlpha b s) (hβ : 0 ≤ rlBeta b s)
    (hα1 : rlAlpha b s ≤ 1) (hβ1 : rlBeta b s ≤ 1)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y)
    (hya : y ≤ -(matchedA E).im) {q : ℝ} (hq1 : 1 ≤ q) (j : Fin 2) :
    eLpNorm (fun ω => blockTrace (rpResolvent E s X ω) j -
        ∫ ω', blockTrace (rpResolvent E s X ω') j ∂rpLaw W b s) (ENNReal.ofReal q) (rpLaw W b s) ≤
      ENNReal.ofReal (16 * Cg * (s * y)⁻¹ ^ 2 * Real.sqrt q / W) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [rl_law_eq_map]
  have hm : Measurable (fun ω : RpSample W => blockTrace (rpResolvent E s X ω) j) :=
    srec_measurable_blockTrace (rp_measurable_resolvent E s (Xf := fun _ => X) (ωf := fun ω => ω)
      measurable_const measurable_id) j
  have hm2 : AEStronglyMeasurable (fun ω => blockTrace (rpResolvent E s X ω) j -
      ∫ ω', blockTrace (rpResolvent E s X ω') j
        ∂((gaussianProduct (rlVar W b s)).map (rlEmbed W b s)))
      ((gaussianProduct (rlVar W b s)).map (rlEmbed W b s)) :=
    (hm.sub measurable_const).aestronglyMeasurable
  rw [eLpNorm_map_measure hm2 (rl_measurable_embed W b s).aemeasurable, rl_integral_transfer]
  have hfun : ((fun ω => blockTrace (rpResolvent E s X ω) j - rlMean b E s X j) ∘
      rlEmbed W b s) = fun x => rlF b E s X (rlProj j) x -
        ∫ x', rlF b E s X (rlProj j) x' ∂gaussianProduct (rlVar W b s) := by
    funext x
    simp only [Function.comp_apply]
    rw [← rl_matrix_eq, rl_blockTrace_proj, rlMean]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x' => ?_)
    show blockTrace (rlG b E s X x') j = _
    rw [rl_blockTrace_proj]
    rfl
  rw [hfun]
  refine (rl_fluct hCg hgr hW hs hα hβ hα1 hβ1 hX hy hya (rlProj j) hq1).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hP := rl_norm_proj_le (W := W) j
  have e : 16 * Cg * (s * y)⁻¹ ^ 2 * Real.sqrt q / W =
      Cg * Real.sqrt q * (16 * 1 / W) * (s * y)⁻¹ ^ 2 := by ring
  rw [e]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (by linarith) hW'.le) (by positivity)) (sq_nonneg _)

/-- **`ResidualPairLayerBound` holds** (the residual pair layer bound of `ResidualPair`). -/
theorem residualPairLayerBound_holds (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : Internal.Contracts.Inputs.GaussianLpGradient) : ResidualPairLayerBound := by
  have _ := hcount
  intro b hb0 hb1 κ s hκ hs0 hs1
  obtain ⟨Cg, hCg, hgr⟩ := hgrad
  obtain ⟨ylo, hylo, hyloE⟩ := rp_im_a_lower hκ
  have hsc : s < 2 * (1 - 2 * b) := hs1.trans_le (by gcongr; exact min_le_left _ _)
  have hsb : s < 2 * b := hs1.trans_le (by gcongr; exact min_le_right _ _)
  set α := rlAlpha b s with hαdef
  set β := rlBeta b s with hβdef
  have hα : 0 < α := by rw [hαdef, rlAlpha]; linarith
  have hβ : 0 < β := by rw [hβdef, rlBeta]; linarith
  have hα1 : α ≤ 1 := by rw [hαdef, rlAlpha]; linarith
  have hβ1 : β ≤ 1 := by rw [hβdef, rlBeta]; linarith
  have hlam : α + β + s = 1 - b := by rw [hαdef, hβdef, rlAlpha, rlBeta]; ring
  have hlam1 : α + β + s ≤ 1 := by rw [hlam]; linarith
  set K := rlK s ylo with hKdef
  have hK0 : 0 < K := rlK_pos hs0 hylo
  set Cs := rlStabC s α β ylo with hCs
  set ηs := rlEtaStar s α β ylo with hηs
  set ds := rlDstar s α β ylo with hds
  set Ce := rlCe Cg α β K with hCe
  have hCs0 : 0 < Cs := rlStabC_pos hs0 hα.le hβ.le hylo
  have hηs0 : 0 < ηs := rlEtaStar_pos hs0 hα.le hβ.le hylo
  have hCe0 : 0 ≤ Ce := by rw [hCe, rlCe]; have := hα.le; have := hβ.le; positivity
  set C := Cs + Cs * Ce + (K + 1) * Ce / ηs + 16 * Cg * K ^ 2 with hC
  refine ⟨ds, C, 1, rlDstar_pos hs0 hα.le hβ.le hylo, one_pos, ?_⟩
  intro W hW X hX E hE
  obtain ⟨hyE, hEabs⟩ := hyloE E hE
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hya0 : 0 < -(matchedA E).im := lt_of_lt_of_le hylo hyE
  have ha1 : ‖matchedA E‖ = 1 := norm_matchedA hEabs
  have hKs : (s * ylo)⁻¹ = K := rfl
  constructor
  · intro hd j
    rw [rl_law_eq_map, rl_integral_transfer]
    set m := rlMean b E s X with hmdef
    set e : Fin 2 → ℂ := fun k =>
      m k - blockTrace (cmpInv (cmpTopH E X) (rlShift s α β (matchedA E) m)) k with hedef
    have hres : ∀ k, ‖e k‖ ≤ Ce / (W : ℝ) ^ 2 := fun k => by
      have h := rl_resid_bound hCg.le hgr hW hs0 hα.le hβ.le hα1 hβ1 hX hylo hyE k
      rw [hKs, rl_resid_eq hW] at h
      exact h
    have hmK : ∀ k, ‖m k‖ ≤ K := fun k => rl_mean_norm_le hs0 hX hylo hyE k
    have hd0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
    have hη0 : 0 ≤ Ce / (W : ℝ) ^ 2 := by positivity
    by_cases hsmall : Ce / (W : ℝ) ^ 2 ≤ ηs
    · have hdR : ∀ k, ‖blockTrace (cmpInv (cmpTopH E X)
          (fun _ => ((α + β + s : ℝ) : ℂ) * matchedA E)) k - matchedA E‖ ≤
          matchedDistance b E X := fun k => by
        have h1 := cmp_le_matchedDistance b E X k
        rw [cmp_resolvent_eq hEabs X] at h1
        have h2 : (fun _ : Fin 2 => ((α + β + s : ℝ) : ℂ) * matchedA E) =
            fun _ => (1 - (b : ℂ)) * matchedA E := by
          funext _; rw [hlam]; push_cast; ring
        rw [h2]; exact h1
      have hst := rl_stability (cmpTopH E X) (cmpTopH_isHermitian E hX) hs0 hα.le hβ.le hlam1
        hylo ha1.le hyE hdR hd hsmall m e (fun k => by rw [hedef]; ring) hres
        (fun k => rl_mean_im_nonpos hs0 hX hylo hyE k) hmK j
      refine hst.trans ?_
      rw [mul_add]
      have e1 : Cs * (Ce / (W : ℝ) ^ 2) = Cs * Ce / (W : ℝ) ^ 2 := by ring
      rw [e1]
      have hCd : Cs * matchedDistance b E X ≤ C * matchedDistance b E X := by
        refine mul_le_mul_of_nonneg_right ?_ hd0
        rw [hC]
        have : 0 ≤ (K + 1) * Ce / ηs := by positivity
        nlinarith [mul_nonneg hCs0.le hCe0, mul_nonneg hCg.le (sq_nonneg K)]
      have hCW : Cs * Ce / (W : ℝ) ^ 2 ≤ C / (W : ℝ) ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [hC]
        have : 0 ≤ (K + 1) * Ce / ηs := by positivity
        nlinarith [mul_nonneg hCg.le (sq_nonneg K)]
      linarith
    · rw [not_le] at hsmall
      have h1 : ‖m j - matchedA E‖ ≤ K + 1 := (norm_sub_le _ _).trans (by rw [ha1]; linarith [hmK j])
      have h2 : K + 1 ≤ (K + 1) * Ce / ηs / (W : ℝ) ^ 2 := by
        rw [div_div, le_div_iff₀ (by positivity)]
        have := mul_lt_mul_of_pos_left hsmall (by linarith : (0 : ℝ) < K + 1)
        rw [lt_div_iff₀ (by positivity)] at hsmall
        nlinarith
      have h3 : (K + 1) * Ce / ηs / (W : ℝ) ^ 2 ≤ C / (W : ℝ) ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [hC]
        nlinarith [mul_nonneg hCs0.le hCe0, mul_nonneg hCg.le (sq_nonneg K)]
      have h4 : 0 ≤ C * matchedDistance b E X := by
        refine mul_nonneg ?_ hd0
        rw [hC]; positivity
      linarith
  · intro q hq2 _ j
    have hq1 : 1 ≤ q := by linarith
    refine (rl_fluct_law hCg.le hgr hW hs0 hα.le hβ.le hα1 hβ1 hX hylo hyE hq1 j).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hW'.le))
    rw [hKs]
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg q)
    have h1 : 0 ≤ (K + 1) * Ce / ηs := by positivity
    have h2 : 0 ≤ Cs * Ce := mul_nonneg hCs0.le hCe0
    linarith

end BlockBand.Layers
