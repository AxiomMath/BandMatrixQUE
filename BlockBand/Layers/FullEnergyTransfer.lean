module

public import BlockBand.Layers.FullEnergyCore
public import BlockBand.Layers.FullEnergyTrace
public import BlockBand.Layers.FullEnergyRecursion

/-!
# The full-energy trace bound: transfer to `ε'` through the law of `H^{(e)}`

The last sentence of the energy paragraph in the proof of the tagged-trace lemma ("The final
energy derivative gives the full-energy trace bound"):
`fullEnergyTraceBound_of_fet (hcount) (hgrad) (hres) (hpath) :
BlockBand.Center.FullEnergyTraceBound`, from the two named layer inputs `FetResidualBound`
(final residual pair layer) and `FetPathBound` (exterior path clause) of
`BlockBand.Layers.FullEnergyPath`, the clock-moments lemma (`clockMoments_holds`) and the
matched-traces theorem (`matchedTraces_holds`, path clause).

Final theorem: `fullEnergyTraceBound_holds (hcount) (hgrad) : BlockBand.Center.FullEnergyTraceBound`,
with `FetResidualBound` from `fetResidualBound_holds` (`BlockBand.Layers.FullEnergyTrace`) and
`FetPathBound` from `fetPathBound_holds` (`BlockBand.Layers.FullEnergyRecursion`).

## Proof

1. **Exact derivative** (`fetX_eLpNorm_deriv_eq`): a.s. under `X.P`, `ε'_{e,k}(E) = Ψ(H^{(e)})` with
   the measurable functional `Ψ` (`fetXPsi`) of `tgt_hasDerivAt_eps_energy`.
2. **Law** (`tgt_eLpNorm_residual_eq`): `‖Ψ(H^{(e)})‖_{L^q(X.P)}` is a moment under
   `rpLaw W b s ⊗ pathLaw W (n-2) b`, `s = min(c, b)`, at `H = assemble (rpSplitAssemble x) 0`.
3. **Deterministic identification** (`fetX_norm_psi_le`): for Hermitian blocks and off the
   exterior poles, `Ψ(H) = conj ρ'_a` with `ρ' = fetRho E s X_r X_r'`, `X_r = pathSchur E π`,
   `X_r' = fetXd E π` (derivative uniqueness: near `E`, `ε_{e,k}(E') = conj(W⁻¹ Tr P_a
   (V - E' - X_r(E') - s a(E'))⁻¹ - a(E'))` by the Schur complement, and `X_r'(E) = fetXd`).
4. **Conditioning on the path** (`clk_eLpNorm_prod_le` after a swap): for a.e. path, the
   residual-pair moment is at most `N(π) = C d + C (1 + 1/d_*) (1+u) δ + C (1+u)/√W`
   (`FetResidualBound`, crude bound on `δ > d_*` using `1 ≤ δ/d_*`), with `d = fetPathDist`,
   `u` the full energy clock (`= fetClock`, `clkCoreSource_eq_source`), `δ = d(X_r)`.
5. **Path moments**: `‖d‖_q ≤ C(r+1)/√W` (`FetPathBound`, `r = n - 2`), `‖u‖_{2q} ≤ C(r+1)`
   (`clockMoments_holds`), `‖δ‖_{2q} ≤ C√(2q)/W` (`matchedTraces_holds.path`), Hölder
   (`wl_eLpNorm_mul_le`). Hence `‖ε'‖_q ≤ C_q n/√W`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE BlockBand.Model.Construction
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. Deterministic facts
-/

section Deterministic

/-- `K - z` is invertible for Hermitian `K` and `Im z < 0`. -/
theorem fetX_isUnit_sub {n : Type*} [Fintype n] [DecidableEq n] {K : Matrix n n ℂ}
    (hK : K.IsHermitian) {z : ℂ} (hz : z.im < 0) : IsUnit (K - z • (1 : Matrix n n ℂ)).det := by
  have hc : 0 < (conj z).im := by rw [Complex.conj_im]; linarith
  have h := dcv_K_isUnit hK hc
  have e : (K - z • (1 : Matrix n n ℂ))ᴴ = -((conj z) • (1 : Matrix n n ℂ) - K) := by
    rw [conjTranspose_sub, hK.eq, conjTranspose_smul, conjTranspose_one, Complex.star_def]
    abel
  have h2 : IsUnit (K - z • (1 : Matrix n n ℂ))ᴴ.det := by
    rw [e, det_neg]
    exact ((isUnit_neg_one (α := ℂ)).pow _).mul h
  rw [det_conjTranspose] at h2
  rw [isUnit_iff_ne_zero] at h2 ⊢
  intro h0
  exact h2 (by rw [h0, star_zero])

/-- `Im(s a) < 0` for `s > 0` on the bulk. -/
theorem fetX_im_sa_neg {κ s E : ℝ} (hκ : 0 < κ) (hs : 0 < s) (hE : E ∈ bulkInterval κ) :
    ((s : ℂ) * matchedA E).im < 0 := by
  obtain ⟨η, hη, hEη⟩ := rp_im_a_lower hκ
  rw [Complex.im_ofReal_mul]
  have := (hEη E hE).1
  nlinarith

/-- `X_r' = B_p*(H - E)⁻²B_p ⪰ 0` for Hermitian path blocks. -/
theorem fetX_fetXd_posSemidef {W r : ℕ} (E : ℝ) (π : PathSample W r)
    (hA : ∀ j, (π.1 j).IsHermitian) : (fetXd E π).PosSemidef := by
  have hH : (pathMatrix π - (E : ℂ) • (1 : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ)).IsHermitian := by
    refine (srec_pathMatrix_isHermitian π hA).sub ?_
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  have hD := hH.inv
  have e : fetXd E π = ((pathMatrix π - (E : ℂ) • 1)⁻¹ * pathPortCoupling π)ᴴ *
      ((pathMatrix π - (E : ℂ) • 1)⁻¹ * pathPortCoupling π) := by
    rw [conjTranspose_mul, hD.eq, fetXd]
    simp only [Matrix.mul_assoc]
  rw [e]
  exact posSemidef_conjTranspose_mul_self _

/-- The full energy clock is `fetClock` at `(X_r, X_r')` for Hermitian path blocks. -/
theorem fetX_clock_eq {W r : ℕ} (b E : ℝ) (π : PathSample W r) (hA : ∀ j, (π.1 j).IsHermitian) :
    clkTrace (clkCoreSource b E (fun _ => true) π) = fetClock b E (pathSchur E π) (fetXd E π) := by
  rw [clkCoreSource_eq_source b E _ π (srec_pathMatrix_isHermitian π hA), fetClock]
  have hP : clkProj (W := W) (fun _ : Fin r => true) = 1 := by
    unfold clkProj
    simp
  rw [hP, Matrix.mul_one]
  rfl

/-- `fetClock ≥ 0` for `S ⪰ 0`. -/
theorem fetX_clock_nonneg {W : ℕ} (b E : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hS : S.PosSemidef) : 0 ≤ fetClock b E X S := by
  unfold fetClock clkTrace
  have h := (hS.conjTranspose_mul_mul_same (fetR b E X)).trace_nonneg
  have h2 : 0 ≤ (((fetR b E X)ᴴ * S * fetR b E X).trace).re := (Complex.le_def.mp h).1
  positivity

end Deterministic

/-!
## 2. The residual at an assembled sample and the derivative identification
-/

section Identification

variable {p : Parameters} {e : ZMod p.n}

/-- The residual `H^{(e)} = assemble (rpSplitAssemble x) 0` of a residual-pair sample and an exterior
path. -/
def fetXH (e : ZMod p.n) (x : RpSample p.W × PathSample p.W (p.n - 2)) : p.SiteMatrix :=
  assemble p e (rpSplitAssemble e x) 0

theorem fetX_measurable_H (e : ZMod p.n) : Measurable (fetXH (p := p) e) :=
  ((BlockBand.Layers.rsl_measurable_assemble e).comp (measurable_id.prodMk measurable_const)).comp
    (rp_measurable_splitAssemble e)

theorem fetX_split_H (x : RpSample p.W × PathSample p.W (p.n - 2)) :
    tgtSplit e (fetXH e x) = rpSplitAssemble e x :=
  rsl_unassemble_assemble e _

/-- The inverse of the shifted pair residual is the reindexed residual-pair resolvent. -/
theorem fetX_inv_submatrix (x : RpSample p.W × PathSample p.W (p.n - 2)) (E s : ℝ) :
    (pairResidual p e (rpSplitAssemble e x) E - ((s : ℂ) * matchedA E) • 1)⁻¹ =
      (rpResolvent E s (pathSchur E x.2) x.1).submatrix (rpPairEquiv e).symm (rpPairEquiv e).symm := by
  rw [rp_pairResidual_assemble, rpResolvent, ← inv_submatrix_equiv]
  congr 1
  rw [show rpMatrix x.1 - (E : ℂ) • 1 - pathSchur E x.2 - ((s : ℂ) * matchedA E) • 1 =
      (rpMatrix x.1 - pathSchur E x.2 - (E : ℂ) • 1) - ((s : ℂ) * matchedA E) • 1 by abel]
  rw [show ((rpMatrix x.1 - pathSchur E x.2 - (E : ℂ) • 1) - ((s : ℂ) * matchedA E) •
      (1 : Matrix (Fin 2 × Fin p.W) (Fin 2 × Fin p.W) ℂ)).submatrix (rpPairEquiv e).symm
        (rpPairEquiv e).symm = (rpMatrix x.1 - pathSchur E x.2 - (E : ℂ) • 1).submatrix
        (rpPairEquiv e).symm (rpPairEquiv e).symm - ((s : ℂ) * matchedA E) •
        (1 : Matrix (Fin 2 × Fin p.W) (Fin 2 × Fin p.W) ℂ).submatrix (rpPairEquiv e).symm
          (rpPairEquiv e).symm from rfl, submatrix_one_equiv]

/-- The exterior block of the assembled residual is the reindexed path matrix. -/
theorem fetX_ext_det (x : RpSample p.W × PathSample p.W (p.n - 2)) (E : ℝ) :
    (exteriorBlock p e (fetXH e x) - (E : ℂ) • 1).det =
      (pathMatrix x.2 - (E : ℂ) • 1).det := by
  have h0 : exteriorBlock p e (fetXH e x) = (tgtSplit e (fetXH e x)).1 := rfl
  rw [h0, fetX_split_H]
  have h1 : (rpSplitAssemble e x).1 - (E : ℂ) • 1 =
      (pathMatrix x.2 - (E : ℂ) • 1).submatrix (rpExtEquiv e).symm (rpExtEquiv e).symm := by
    rw [show (pathMatrix x.2 - (E : ℂ) • 1).submatrix (rpExtEquiv e).symm (rpExtEquiv e).symm =
        (pathMatrix x.2).submatrix (rpExtEquiv e).symm (rpExtEquiv e).symm -
          (E : ℂ) • (1 : Matrix (Fin (p.n - 2) × Fin p.W) (Fin (p.n - 2) × Fin p.W) ℂ).submatrix
            (rpExtEquiv e).symm (rpExtEquiv e).symm from rfl, submatrix_one_equiv]
    rfl
  rw [h1, det_submatrix_equiv_self]

/-- **The residual trace at an assembled sample** (Schur complement, conjugate form): off the
exterior poles, `ε_{e,k}(E) = conj(W⁻¹ Tr P_a (V - E - X_r(E) - s a)⁻¹ - a)`, `k = e + off(a)`. -/
theorem fetX_eps_eq {x : RpSample p.W × PathSample p.W (p.n - 2)} (hH : (fetXH e x).IsHermitian)
    {E : ℝ} (hdet : (exteriorBlock p e (fetXH e x) - (E : ℂ) • 1).det ≠ 0) (a : Fin 2) :
    tgtEps p e (fetXH e x) E (rngBlk e (rpPairOff a)) =
      conj (blockTrace (rpResolvent E (splitS p) (pathSchur E x.2) x.1) a - matchedA E) := by
  have hz : (splitS p : ℂ) * tgtMu E = conj ((splitS p : ℂ) * matchedA E) := by
    rw [tgtMu, map_mul, Complex.conj_ofReal]
  unfold tgtEps tgtR0
  rw [hz, BlockBand.Center.ctr_compressed_conj hH, tgt_pairBlockTrace_conjTranspose,
    BlockBand.Center.ctr_compressed_eq_schur hH hdet, tgt_edgeSchur_eq, fetX_split_H,
    fetX_inv_submatrix, rp_pairBlockTrace_submatrix, tgtMu, ← map_sub]

end Identification

/-!
## 3. The energy derivative at an assembled sample
-/

section Derivative

variable {p : Parameters} {e : ZMod p.n}

/-- **The residual-pair derivative**: where `H - E` and `V - E - X_r - sa` are invertible,
`E' ↦ W⁻¹ Tr P_a (V - E' - X_r(E') - s a(E'))⁻¹ - a(E')` has derivative `ρ'_a = fetRho` at
`(X_r, X_r')`. -/
theorem fetX_hasDerivAt_rp {W r : ℕ} {E : ℝ} (hE : E ∈ Set.Ioo (-2 : ℝ) 2) (s : ℝ)
    (π : PathSample W r) (ω : RpSample W) (hU : IsUnit (pathMatrix π - (E : ℂ) • 1).det)
    (hR : IsUnit (rpMatrix ω - (E : ℂ) • 1 - pathSchur E π - ((s : ℂ) * matchedA E) • 1).det)
    (a : Fin 2) :
    HasDerivAt (fun E' : ℝ => blockTrace (rpResolvent E' s (pathSchur E' π) ω) a - matchedA E')
      (fetRho E s (pathSchur E π) (fetXd E π) ω a) E := by
  have hA := tgt_hasDerivAt_matchedA hE
  have h1 := (fetC_hasDerivAt_smul_one (n := Fin 2 × Fin W) E).const_sub (rpMatrix ω)
  have h2 := h1.sub (fetC_hasDerivAt_pathSchur E π hU)
  have h3 := h2.sub ((hA.const_mul (s : ℂ)).smul_const (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))
  have hinv := tgt_hasDerivAt_inv_comp h3 hR
  have h4 := ((fetCB W a).hasFDerivAt.comp_hasDerivAt E hinv).sub hA
  convert h4 using 1
  · funext E'
    rfl
  unfold fetRho
  congr 1
  show blockTrace _ a = blockTrace _ a
  congr 1
  have e : -(1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - fetXd E π -
      ((s : ℂ) * tgtAd E) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) =
      -(1 + fetXd E π + ((s : ℂ) * tgtAd E) • 1) := by abel
  rw [e, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  rfl

/-- The explicit energy derivative of `ε_{e,k}` (`tgt_hasDerivAt_eps_energy`), as a measurable
functional of the residual. -/
def fetXPsi (p : Parameters) (e : ZMod p.n) (E : ℝ) (k : ZMod p.n) (H : p.SiteMatrix) : ℂ :=
  tgtTraceCLM e k (-((BlockBand.Center.ctrFull p e H E (tgtZeta p E))⁻¹ *
    (-(1 : p.SiteMatrix) - ((splitS p : ℂ) * conj (tgtAd E)) • pairProjector p e) *
      (BlockBand.Center.ctrFull p e H E (tgtZeta p E))⁻¹)) - conj (tgtAd E)

theorem fetX_measurable_psi (p : Parameters) (e : ZMod p.n) (E : ℝ) (k : ZMod p.n) :
    Measurable (fetXPsi p e E k) := by
  have hF : Measurable (fun H : p.SiteMatrix => (BlockBand.Center.ctrFull p e H E (tgtZeta p E))⁻¹) := by
    refine measurable_matrix_inv.comp ?_
    unfold BlockBand.Center.ctrFull
    exact (measurable_id.sub measurable_const).sub measurable_const
  have hM := srec_measurable_mul (srec_measurable_mul hF (measurable_const (a :=
    (-(1 : p.SiteMatrix) - ((splitS p : ℂ) * conj (tgtAd E)) • pairProjector p e)))) hF
  exact ((tgtTraceCLM e k).continuous.measurable.comp hM.neg).sub measurable_const

/-- **Deterministic identification**: for Hermitian blocks and off the exterior poles,
`|Ψ(H)| = |ρ'_a| ≤ max_k |ρ'_k|` at `(X_r, X_r') = (pathSchur E π, fetXd E π)`. -/
theorem fetX_norm_psi_le {κ : ℝ} (hκ : 0 < κ) {E : ℝ} (hE : E ∈ bulkInterval κ)
    {x : RpSample p.W × PathSample p.W (p.n - 2)} (hH : (fetXH e x).IsHermitian)
    (hdet : (exteriorBlock p e (fetXH e x) - (E : ℂ) • 1).det ≠ 0)
    (hπ : ∀ j, (x.2.1 j).IsHermitian) (hω : ∀ j, (x.1.1 j).IsHermitian) (a : Fin 2) :
    ‖fetXPsi p e E (rngBlk e (rpPairOff a)) (fetXH e x)‖ ≤
      fetRhoMax E (splitS p) (pathSchur E x.2) (fetXd E x.2) x.1 := by
  have hE2 : |E| < 2 := abs_lt_two_of_mem_bulkInterval hκ hE
  have hEI : E ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [(abs_lt.mp hE2).1], (abs_lt.mp hE2).2⟩
  have hM := tgt_ctrFull_det_ne (e := e) hH hdet (tgt_zeta_im_pos (p := p) hE2)
  have h1 := tgt_hasDerivAt_eps_energy (e := e) (fetXH e x) hEI hM (rngBlk e (rpPairOff a))
  have hU : IsUnit (pathMatrix x.2 - (E : ℂ) • 1).det := by
    rw [← fetX_ext_det (e := e) x E]; exact isUnit_iff_ne_zero.mpr hdet
  have hK : (rpMatrix x.1 - (E : ℂ) • (1 : Matrix (Fin 2 × Fin p.W) (Fin 2 × Fin p.W) ℂ) -
      pathSchur E x.2).IsHermitian := by
    refine ((rp_rpMatrix_isHermitian x.1 hω).sub ?_).sub (srec_pathSchur_isHermitian E x.2 hπ)
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  have hR := fetX_isUnit_sub hK (fetX_im_sa_neg hκ (BlockBand.Center.ctr_splitS_pos (p := p)) hE)
  have h2 := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt E
    (fetX_hasDerivAt_rp hEI (splitS p) x.2 x.1 hU hR a)
  have hev : ∀ᶠ E' : ℝ in 𝓝 E, (exteriorBlock p e (fetXH e x) - (E' : ℂ) • 1).det ≠ 0 := by
    have hc : Continuous (fun E' : ℝ => (exteriorBlock p e (fetXH e x) - (E' : ℂ) • 1).det) := by
      refine Continuous.matrix_det ?_
      exact continuous_const.sub (Complex.continuous_ofReal.smul continuous_const)
    exact hc.continuousAt.eventually_ne hdet
  have heq : (fun E' : ℝ => tgtEps p e (fetXH e x) E' (rngBlk e (rpPairOff a))) =ᶠ[𝓝 E]
      (fun E' : ℝ => (Complex.conjCLE : ℂ →L[ℝ] ℂ)
        (blockTrace (rpResolvent E' (splitS p) (pathSchur E' x.2) x.1) a - matchedA E')) := by
    filter_upwards [hev] with E' hE'
    exact fetX_eps_eq hH hE' a
  have h3 := h1.unique (h2.congr_of_eventuallyEq heq)
  have h4 : fetXPsi p e E (rngBlk e (rpPairOff a)) (fetXH e x) =
      conj (fetRho E (splitS p) (pathSchur E x.2) (fetXd E x.2) x.1 a) := h3
  rw [h4, Complex.norm_conj]
  unfold fetRhoMax
  rcases rng_fin2_cases a with rfl | rfl
  · exact le_max_left _ _
  · exact le_max_right _ _

end Derivative

/-!
## 4. Laws: the transfer to `rpLaw ⊗ pathLaw` and the almost-sure good events
-/

section Laws

theorem fetX_ae_rp_herm (W : ℕ) (b s : ℝ) : ∀ᵐ ω ∂rpLaw W b s, ∀ j, (ω.1 j).IsHermitian := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  have h := ae_blocks_isHermitian 2 W (Real.toNNReal ((1 - 2 * b - s / 2) / W))
  unfold rpLaw
  filter_upwards [(Measure.quasiMeasurePreserving_fst).ae h] with ω hω
  exact hω

theorem fetX_ae_path_herm (W r : ℕ) (b : ℝ) : ∀ᵐ π ∂pathLaw W r b, ∀ j, (π.1 j).IsHermitian := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  have h := ae_blocks_isHermitian r W (Real.toNNReal ((1 - 2 * b) / W))
  unfold pathLaw
  filter_upwards [(Measure.quasiMeasurePreserving_fst).ae h] with π hπ
  exact hπ

variable {p : Parameters} {model : p.GaussianRingModel} {e : ZMod p.n}

/-- The good event `{H Hermitian, det(H_R - E) ≠ 0}` is measurable. -/
theorem fetX_measurableSet_good (e : ZMod p.n) (E : ℝ) :
    MeasurableSet {H : p.SiteMatrix |
      H.IsHermitian ∧ (exteriorBlock p e H - (E : ℂ) • 1).det ≠ 0} := by
  have hc : Continuous (fun H : p.SiteMatrix => (exteriorBlock p e H - (E : ℂ) • 1).det) := by
    refine Continuous.matrix_det ?_
    refine Continuous.sub ?_ continuous_const
    unfold exteriorBlock
    exact continuous_pi fun x => continuous_pi fun y => continuous_apply_apply _ _
  have h1 : MeasurableSet {H : p.SiteMatrix | H.IsHermitian} :=
    (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
  have h2 : MeasurableSet {H : p.SiteMatrix | (exteriorBlock p e H - (E : ℂ) • 1).det ≠ 0} :=
    (isOpen_ne_fun hc continuous_const).measurableSet
  exact h1.inter h2

/-- Under an edge splitting, a.s. under `rpLaw ⊗ pathLaw (n-2)` the assembled residual is Hermitian
and has no exterior pole at `E`. -/
theorem fetX_ae_good (X : PairExtension p model) {G : X.Ω → PairMatrix p e}
    (hs : IsCenterSplitting X G) (E : ℝ) :
    ∀ᵐ x ∂((rpLaw p.W p.b (splitS p)).prod (pathLaw p.W (p.n - 2) p.b)),
      (fetXH e x).IsHermitian ∧ (exteriorBlock p e (fetXH e x) - (E : ℂ) • 1).det ≠ 0 := by
  have hF : Measurable (fun ω => X.Hm ω - embedPair p e (G ω)) := tgt_measurable_residual X hs.1
  have h0 : ∀ᵐ ω ∂X.P, (X.Hm ω - embedPair p e (G ω)).IsHermitian ∧
      (exteriorBlock p e (X.Hm ω - embedPair p e (G ω)) - (E : ℂ) • 1).det ≠ 0 := by
    filter_upwards [tgt_ae_residual_isHermitian X hs, tgt_ae_residual_exterior_det X hs E]
      with ω h1 h2
    exact ⟨h1, h2⟩
  have h1 := (ae_map_iff hF.aemeasurable (fetX_measurableSet_good e E)).mpr h0
  rw [tgt_map_residual_eq X hs] at h1
  exact (ae_map_iff (fetX_measurable_H e).aemeasurable (fetX_measurableSet_good e E)).mp h1

/-- **Transfer** (`tgt_eLpNorm_residual_eq`): the `L^q(X.P)` norm of `ε'_{e,k}(E)` is the norm of
`|Ψ|` at the assembled residual under `pathLaw (n-2) ⊗ rpLaw`. -/
theorem fetX_eLpNorm_deriv_eq (X : PairExtension p model) {G : X.Ω → PairMatrix p e}
    (hs : IsCenterSplitting X G) {κ : ℝ} (hκ : 0 < κ) {E : ℝ} (hE : E ∈ bulkInterval κ)
    (k : ZMod p.n) (q : ℝ≥0∞) :
    eLpNorm (fun ω => deriv (fun E' : ℝ => tgtEps p e (X.Hm ω - embedPair p e (G ω)) E' k) E) q X.P =
      eLpNorm (fun y : PathSample p.W (p.n - 2) × RpSample p.W =>
          ‖fetXPsi p e E k (fetXH e (y.2, y.1))‖) q
        ((pathLaw p.W (p.n - 2) p.b).prod (rpLaw p.W p.b (splitS p))) := by
  have hE2 : |E| < 2 := abs_lt_two_of_mem_bulkInterval hκ hE
  have hEI : E ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [(abs_lt.mp hE2).1], (abs_lt.mp hE2).2⟩
  have hΨ := fetX_measurable_psi p e E k
  have h1 : eLpNorm (fun ω => deriv (fun E' : ℝ => tgtEps p e (X.Hm ω - embedPair p e (G ω)) E' k) E)
      q X.P = eLpNorm (fun ω => fetXPsi p e E k (X.Hm ω - embedPair p e (G ω))) q X.P := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [tgt_ae_eps_energy_hasDerivAt X hs hκ hE k] with ω hω
    exact (tgt_hasDerivAt_eps_energy _ hEI hω.1 k).deriv
  have hm : Measurable (fun x : RpSample p.W × PathSample p.W (p.n - 2) =>
      ‖fetXPsi p e E k (fetXH e x)‖) := (hΨ.comp (fetX_measurable_H e)).norm
  rw [h1, tgt_eLpNorm_residual_eq X hs hΨ q]
  have h3 := eLpNorm_norm (p := q) (μ := (rpLaw p.W p.b (splitS p)).prod
    (pathLaw p.W (p.n - 2) p.b)) _ (hΨ.comp (fetX_measurable_H e)).aestronglyMeasurable
  change eLpNorm (fetXPsi p e E k ∘ fetXH e) q _ = _
  rw [← h3]
  have h2 := eLpNorm_comp_measurePreserving (p := q) hm.aestronglyMeasurable
    (Measure.measurePreserving_swap (μ := pathLaw p.W (p.n - 2) p.b)
      (ν := rpLaw p.W p.b (splitS p)))
  exact h2.symm

end Laws

/-!
## 5. `L^p` and scalar arithmetic
-/

section Arith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `‖c₀ d + c₁ (1+u) δ + c₂ (1+u)‖_q ≤ c₀ A + c₁ (1+B) D + c₂ (1+B)` from `‖d‖_q ≤ A`,
`‖u‖_{2q} ≤ B`, `‖δ‖_{2q} ≤ D` (Minkowski and Hölder). -/
theorem fetX_eLpNorm_N {q : ℝ} (hq : 1 ≤ q) {d u δ : Ω → ℝ} (hu : AEStronglyMeasurable u μ)
    (hδ : AEStronglyMeasurable δ μ) {c₀ c₁ c₂ A B D : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hD0 : 0 ≤ D)
    (hA : eLpNorm d (ENNReal.ofReal q) μ ≤ ENNReal.ofReal A)
    (hB : eLpNorm u (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal B)
    (hD : eLpNorm δ (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal D) :
    eLpNorm (fun ω => c₀ * d ω + c₁ * ((1 + u ω) * δ ω) + c₂ * (1 + u ω)) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (c₀ * A + c₁ * ((1 + B) * D) + c₂ * (1 + B)) := by
  have h2q : 1 ≤ 2 * q := by linarith
  have h1u : eLpNorm (fun ω => 1 + u ω) (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal (1 + B) := by
    have h := fetC_eLpNorm_comb (μ := μ) h2q (f := fun _ => (1 : ℝ)) (g := u) zero_le_one
      zero_le_one zero_le_one hB0 (fetC_eLpNorm_one _) hB
    have e : (fun ω => (1 : ℝ) * (fun _ : Ω => (1 : ℝ)) ω + 1 * u ω) = fun ω => 1 + u ω := by
      funext ω; ring
    rw [e, show (1 : ℝ) * 1 + 1 * B = 1 + B by ring] at h
    exact h
  have hprod : eLpNorm (fun ω => (1 + u ω) * δ ω) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal ((1 + B) * D) := by
    refine (wl_eLpNorm_mul_le (show AEStronglyMeasurable (fun ω => 1 + u ω) μ from
      aestronglyMeasurable_const.add hu) hδ (by linarith)).trans ?_
    exact le_of_le_of_eq (mul_le_mul' h1u hD) (ENNReal.ofReal_mul (by linarith)).symm
  have h1u' : eLpNorm (fun ω => 1 + u ω) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (1 + B) :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))).trans h1u
  have h1 := fetC_eLpNorm_comb (μ := μ) hq hc₀ hc₁ hA0 (by positivity) hA hprod
  have h2 := fetC_eLpNorm_comb (μ := μ) hq zero_le_one hc₂ (by positivity) (by positivity) h1 h1u'
  have e : (fun ω => (1 : ℝ) * (c₀ * d ω + c₁ * ((1 + u ω) * δ ω)) + c₂ * (1 + u ω)) =
      fun ω => c₀ * d ω + c₁ * ((1 + u ω) * δ ω) + c₂ * (1 + u ω) := by
    funext ω; ring
  rw [e, one_mul] at h2
  exact h2

/-- The scalar bookkeeping of the final bound. -/
theorem fetX_arith {CR CP CK CM d₀ m r w q : ℝ} (hCR : 0 ≤ CR) (hCP : 0 ≤ CP) (hCK : 0 ≤ CK)
    (hCM : 0 ≤ CM) (hd₀ : 0 < d₀) (hm : 1 ≤ m) (hrm : r + 1 ≤ m)
    (hw : 1 ≤ w) :
    CR * (CP * (r + 1) / w) + (CR + CR / d₀) * ((1 + CK * (r + 1)) * (CM * Real.sqrt q / w ^ 2)) +
        CR / w * (1 + CK * (r + 1)) ≤
      (CR * CP + (CR + CR / d₀) * (1 + CK) * CM * Real.sqrt q + CR * (1 + CK)) * m / w := by
  have hw0 : 0 < w := by linarith
  have hK : 1 + CK * (r + 1) ≤ (1 + CK) * m := by nlinarith
  have hsq : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hC1 : 0 ≤ CR + CR / d₀ := by positivity
  have t1 : CR * (CP * (r + 1) / w) ≤ CR * CP * m / w := by
    rw [mul_div_assoc', mul_assoc]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hrm hCP) hCR) hw0.le
  have t2 : (CR + CR / d₀) * ((1 + CK * (r + 1)) * (CM * Real.sqrt q / w ^ 2)) ≤
      (CR + CR / d₀) * (1 + CK) * CM * Real.sqrt q * m / w := by
    have hw2 : CM * Real.sqrt q / w ^ 2 ≤ CM * Real.sqrt q / w := by
      refine div_le_div_of_nonneg_left (by positivity) hw0 ?_
      nlinarith
    have hpos : 0 ≤ CM * Real.sqrt q / w := by positivity
    calc (CR + CR / d₀) * ((1 + CK * (r + 1)) * (CM * Real.sqrt q / w ^ 2))
        ≤ (CR + CR / d₀) * (((1 + CK) * m) * (CM * Real.sqrt q / w)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hK hw2 (by positivity) (by positivity)) hC1
      _ = _ := by ring
  have t3 : CR / w * (1 + CK * (r + 1)) ≤ CR * (1 + CK) * m / w := by
    calc CR / w * (1 + CK * (r + 1)) ≤ CR / w * ((1 + CK) * m) :=
          mul_le_mul_of_nonneg_left hK (by positivity)
      _ = _ := by ring
  have e : (CR * CP + (CR + CR / d₀) * (1 + CK) * CM * Real.sqrt q + CR * (1 + CK)) * m / w =
      CR * CP * m / w + (CR + CR / d₀) * (1 + CK) * CM * Real.sqrt q * m / w +
        CR * (1 + CK) * m / w := by ring
  rw [e]
  linarith

end Arith

/-!
## 6. The full-energy trace bound
-/

/-- **The full-energy trace bound** from the two named layer inputs.

*Law.* `X.P`, for every model, adjacent pair `S_e = {e, e+1}` and extension `X` carrying an edge
splitting `G` (`IsCenterSplitting`); the residual `H^{(e)} = X.Hm - embed G` has the law of
`assemble (rpSplitAssemble x) 0` under `rpLaw W b s ⊗ pathLaw W (n-2) b`, `s = min(c, b)`
(`tgt_map_residual_eq`).
*Object.* `∂_E ε_{e,k}(E)` (Lean `deriv`), `ε_{e,k}(E') = W⁻¹ Tr P_k ℛ_e(E', s ā(E')) - ā(E')`.
*Domain, norms, quantifiers.* `b ∈ (0, 1/2)`, `κ > 0`, `T`, `q ≥ 1` first; then `C_q`, `W₀`;
uniformly in parameters with `p.b = b`, `n ≤ TW`, `W > W₀`, deterministic `E ∈ bulkInterval κ`
and `k ∈ {e, e+1}`: `‖∂_E ε_{e,k}(E)‖_{L^q(X.P)} ≤ C_q n/√W`.
*Inputs.* `FetResidualBound` (final residual pair layer, at moment order `q`), `FetPathBound`
(exterior path, `r = n - 2`, order `q`), `clockMoments_holds` (full energy clock, order `2q`) and
`matchedTraces_holds` (path clause, order `2q`), the last two from `ConditionalBlockGUECount` and
`GaussianLpGradient`. -/
theorem fullEnergyTraceBound_of_fet
    (hcount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : BlockBand.Internal.Contracts.Inputs.GaussianLpGradient)
    (hres : FetResidualBound) (hpath : FetPathBound) :
    BlockBand.Center.FullEnergyTraceBound := by
  intro b hb0 hb1 κ T hκ q hq
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = min (1 - 2 * b) b := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; exact lt_min (by linarith) hb0
  have hs1 : s < 2 * min (1 - 2 * b) b := by rw [hsdef]; linarith
  obtain ⟨dstar, CR, WR, hd0, hCR, hR⟩ := hres b hb0 hb1 κ s hκ hs0 hs1 q hq
  obtain ⟨CP, WP, hCP, hP⟩ := hpath b hb0 hb1 κ T hκ q hq
  obtain ⟨CK, WK, hCK, hK⟩ := clockMoments_holds hcount hgrad b hb0 hb1 κ T hκ (2 * q)
    (by linarith)
  obtain ⟨ε₀, CM, hε₀, hM⟩ := (matchedTraces_holds hcount hgrad).path b hb0 hb1 κ T hκ
  refine ⟨CR * CP + (CR + CR / dstar) * (1 + CK) * max CM 0 * Real.sqrt (2 * q) + CR * (1 + CK),
    max (max (WR : ℝ) WP) (max (WK : ℝ) (2 * q / ε₀)), ?_⟩
  intro p hpb hnT hW model e X G hsplit E hE k hk
  subst hpb
  have hsp : splitS p = s := by rw [hsdef]; rfl
  have hWpos : 0 < p.W := p.W_pos
  have hW' : (0 : ℝ) < p.W := by exact_mod_cast hWpos
  have hWR : WR ≤ p.W := by
    have h := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hW)
    exact_mod_cast h.le
  have hWP : WP ≤ p.W := by
    have h := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hW)
    exact_mod_cast h.le
  have hWK : WK ≤ p.W := by
    have h := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hW)
    exact_mod_cast h.le
  have hqW : 2 * q ≤ ε₀ * p.W := by
    have h := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hW)
    rw [div_lt_iff₀ hε₀] at h
    linarith
  set r := p.n - 2 with hrdef
  have hn4 := p.n_ge_four
  have hr1 : 1 ≤ r := by omega
  have hrn : (r : ℝ) + 1 ≤ p.n := by exact_mod_cast (by omega : r + 1 ≤ p.n)
  have hrT : (r : ℝ) ≤ T * p.W := le_trans (by exact_mod_cast (by omega : r ≤ p.n)) hnT
  have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast (by omega : 1 ≤ p.n)
  have hsqW : 1 ≤ Real.sqrt (p.W : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hWpos)
  -- the block index
  obtain ⟨a, rfl⟩ : ∃ a : Fin 2, k = rngBlk e (rpPairOff a) := by
    rcases hk with rfl | rfl
    · exact ⟨1, by simp [rpPairOff, rngBlk_zero]⟩
    · exact ⟨0, by simp [rpPairOff, rngBlk]⟩
  -- path functionals
  set d : PathSample p.W r → ℝ := fun π => fetPathDist p.b E π with hddef
  set u : PathSample p.W r → ℝ := fun π => clkTrace (clkCoreSource p.b E (fun _ => true) π)
    with hudef
  set δ : PathSample p.W r → ℝ := fun π => matchedDistance p.b E (pathSchur E π) with hδdef
  set N : PathSample p.W r → ℝ := fun π => CR * d π + (CR + CR / dstar) * ((1 + u π) * δ π) +
    CR / Real.sqrt p.W * (1 + u π) with hNdef
  have hdm : Measurable d := fetC_measurable_pathDist p.b E
  have hum : Measurable u := clk_measurable_trace (clk_measurable_coreSource p.W r p.b E _)
  have hδm : Measurable δ :=
    (srec_measurable_matchedDistance p.b E p.W).comp (measurable_pathSchur p.W r E)
  have hNm : Measurable N :=
    ((measurable_const.mul hdm).add (measurable_const.mul ((measurable_const.add hum).mul hδm))).add
      (measurable_const.mul (measurable_const.add hum))
  have hFm : Measurable (fun y : PathSample p.W r × RpSample p.W =>
      ‖fetXPsi p e E (rngBlk e (rpPairOff a)) (fetXH e (y.2, y.1))‖) :=
    ((fetX_measurable_psi p e E _).comp ((fetX_measurable_H e).comp measurable_swap)).norm
  change eLpNorm (fun ω => deriv (fun E' : ℝ =>
    tgtEps p e (X.Hm ω - embedPair p e (G ω)) E' (rngBlk e (rpPairOff a))) E) _ _ ≤ _
  rw [fetX_eLpNorm_deriv_eq X hsplit hκ hE _ _]
  refine (clk_eLpNorm_prod_le (c := 1) hFm hNm (by linarith : (0 : ℝ) < q) ?_).trans ?_
  · -- conditioning on the exterior path
    have hg := fetX_ae_good X hsplit E
    have hg' := (Measure.measurePreserving_swap (μ := pathLaw p.W r p.b)
      (ν := rpLaw p.W p.b (splitS p))).quasiMeasurePreserving.ae hg
    have hg'' := Measure.ae_ae_of_ae_prod hg'
    filter_upwards [hg'', fetX_ae_path_herm p.W r p.b] with π hπg hπ
    have hX := srec_pathSchur_isHermitian E π hπ
    have hS := fetX_fetXd_posSemidef E π hπ
    have hu : u π = fetClock p.b E (pathSchur E π) (fetXd E π) := fetX_clock_eq _ _ π hπ
    have hu0 : 0 ≤ u π := hu ▸ fetX_clock_nonneg _ _ _ hS
    have hd0' : 0 ≤ d π := (norm_nonneg _).trans (le_max_left _ _)
    have hδ0 : 0 ≤ δ π := (norm_nonneg _).trans (le_max_left _ _)
    have hN0 : 0 ≤ N π := by simp only [hNdef]; positivity
    have hsec : eLpNorm (fun ω => ‖fetXPsi p e E (rngBlk e (rpPairOff a)) (fetXH e (ω, π))‖)
        (ENNReal.ofReal q) (rpLaw p.W p.b (splitS p)) ≤
        eLpNorm (fetRhoMax E (splitS p) (pathSchur E π) (fetXd E π)) (ENNReal.ofReal q)
          (rpLaw p.W p.b (splitS p)) := by
      refine eLpNorm_mono_ae (((fetX_measurable_psi p e E _).comp ((fetX_measurable_H e).comp
        (measurable_id.prodMk measurable_const))).norm.aestronglyMeasurable) ?_
      filter_upwards [hπg, fetX_ae_rp_herm p.W p.b (splitS p)] with ω hgω hω
      have h0 : 0 ≤ fetRhoMax E (splitS p) (pathSchur E π) (fetXd E π) ω :=
        (norm_nonneg _).trans (le_max_left _ _)
      rw [norm_norm, Real.norm_of_nonneg h0]
      exact fetX_norm_psi_le (x := (ω, π)) hκ hE hgω.1 hgω.2 hπ hω a
    refine hsec.trans ?_
    rw [hsp, ENNReal.ofReal_one, one_mul, Real.enorm_of_nonneg hN0]
    obtain ⟨hcr, hfine⟩ := hR p.W hWpos hWR (pathSchur E π) (fetXd E π) hX hS E hE
    have hC1 : 0 ≤ CR / dstar * ((1 + u π) * δ π) := by positivity
    by_cases hδd : δ π ≤ dstar
    · refine (hfine hδd).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [← hu]
      have e1 : N π = CR * (d π + (1 + u π) * (δ π + 1 / Real.sqrt p.W)) +
          CR / dstar * ((1 + u π) * δ π) := by
        simp only [hNdef]; ring
      have e2 : fetDist p.b E (pathSchur E π) (fetXd E π) = d π := rfl
      rw [e1, e2]
      change CR * (d π + (1 + u π) * (δ π + 1 / Real.sqrt p.W)) ≤ _
      linarith
    · refine hcr.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [← hu]
      have hlt : dstar < δ π := lt_of_not_ge hδd
      have h1 : CR * (1 + u π) * 1 ≤ CR * (1 + u π) * (δ π / dstar) :=
        mul_le_mul_of_nonneg_left (by rw [le_div_iff₀ hd0]; linarith) (by positivity)
      have e1 : CR / dstar * ((1 + u π) * δ π) = CR * (1 + u π) * (δ π / dstar) := by ring
      have h2 : 0 ≤ CR * d π := mul_nonneg hCR hd0'
      have h3 : 0 ≤ CR * ((1 + u π) * δ π) := by positivity
      have h4 : 0 ≤ CR / Real.sqrt p.W * (1 + u π) := by positivity
      have e2 : N π = CR * d π + CR * ((1 + u π) * δ π) + CR / dstar * ((1 + u π) * δ π) +
          CR / Real.sqrt p.W * (1 + u π) := by
        simp only [hNdef]; ring
      rw [e2]
      linarith
  · -- path moments
    rw [ENNReal.ofReal_one, one_mul]
    have hd := hP p.W hWpos hWP r hr1 hrT E hE
    have hu := (hK p.W hWK hWpos).1 r hr1 hrT E hE
    have hδ := hM p.W hWpos (2 * q) (by linarith) hqW r hr1 hrT E hE
    have hδ' : eLpNorm δ (ENNReal.ofReal (2 * q)) (pathLaw p.W r p.b) ≤
        ENNReal.ofReal (max CM 0 * Real.sqrt (2 * q) / (Real.sqrt p.W) ^ 2) := by
      rw [Real.sq_sqrt hW'.le]
      refine hδ.trans (ENNReal.ofReal_le_ofReal ?_)
      gcongr
      exact le_max_left _ _
    have hN := fetX_eLpNorm_N (μ := pathLaw p.W r p.b) hq (d := d) hum.aestronglyMeasurable
      hδm.aestronglyMeasurable (c₀ := CR) (c₁ := CR + CR / dstar) (c₂ := CR / Real.sqrt p.W)
      hCR (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) hd hu hδ'
    refine hN.trans (ENNReal.ofReal_le_ofReal ?_)
    exact fetX_arith hCR hCP hCK (le_max_right _ _) hd0 hn1 hrn hsqW

/-!
## The final theorem
-/

/-- **The full-energy trace bound** of the tagged-trace lemma: the moment half
`BlockBand.Center.FullEnergyTraceBound` (equivalently `FullEnergyTraceStatement`, by
`fullEnergyTrace_iff`), the last input of `CenterDomainContract.small`.

* *Statement in the paper.* `sup_{E ∈ I} max_i ‖ε'_{e,i}(E)‖_{L^p} ≤ C_p n/√W`.
* *Law.* `X.P` of a pair extension carrying an edge splitting `G` (`IsCenterSplitting`:
  `G_e ~ GUE_{2W}(s/(2W))` independent of `H^{(e)} = H - G_e`, `H = X.Hm` with the exact physical
  law), `s = splitS p = min(c, b)`. Equivalently (`tgt_map_residual_eq`) the law
  `rpLaw W b s ⊗ pathLaw W (n-2) b` of the residual pair layer and the exterior path.
* *Object.* `ε_{e,k}(E') = W⁻¹ Tr P_k ℛ_e(E', s ā(E')) - ā(E')` built from `H^{(e)}` (`csmEps`,
  `tgtEps`), and `ε'` is Lean's `deriv` in the energy at the deterministic `E` (the full energy
  derivative, including the `E`-dependence of `μ = ā` and of `sμ`).
* *Domain.* `b ∈ (0, 1/2)`, `I = bulkInterval κ` (`κ > 0`), both pair blocks `k ∈ {i, i+1}`,
  every parameter set with `p.b = b` and `n ≤ TW` (`n ≥ 4` is built into `Parameters`), every
  model, pair and splitting.
* *Norms.* `L^q(X.P)` of `‖ε'‖` (complex modulus), `q ≥ 1`; the supremum over `E` is outside the
  moment (deterministic energies).
* *Quantifier order.* `b, κ, T, q` first; then `C_q`, `W₀`; then uniformly in `W > W₀`, `n ≤ TW`,
  the model, `i`, the extension, the splitting, `E ∈ I` and `k`.
* *Uniformity.* `C_q, W₀` depend only on `b, κ, T, q` (through the constants of the inputs below);
  no order of limits is involved (finite `n, W`).
* *Proof.* `fullEnergyTraceBound_of_fet` (transfer to the product law, a.s. identification of
  `|ε'_{e,k}|` with the residual-pair derivative `|ρ'|` of `fetRho`, Fubini over the exterior path,
  the crude clause on `{δ > d_*}` via `1 ≤ δ/d_*`) from `fetResidualBound_holds` (the final residual
  pair: Ward identity, derivative mean equation with stability gap `s/(1-b)`, Gaussian noise) and
  `fetPathBound_holds` (`‖f'_r - a'‖_{L^p} ≤ C(r+1)/√W` on the exterior path at `r = n - 2 ≤ TW`). -/
theorem fullEnergyTraceBound_holds
    (hcount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : BlockBand.Internal.Contracts.Inputs.GaussianLpGradient) :
    BlockBand.Center.FullEnergyTraceBound :=
  fullEnergyTraceBound_of_fet hcount hgrad (fetResidualBound_holds hcount hgrad)
    (fetPathBound_holds hcount hgrad)

end BlockBand.Layers
