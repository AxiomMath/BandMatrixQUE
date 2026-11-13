module

public import BlockBand.Layers.TaggedDecayStep

/-!
# The tagged decay bound (`TgtDecayBound`): the final residual pair and the assembly

The tagged decay bound of the tagged-trace lemma ("its clock is the final trace pairing with
`Y`"), conditional on the two named statements `TdcLayerMean` (proved by `tdcLayerMean_holds`)
and `TdcPairStep` (proved by `tdcPairStep_of_fet`); the conditional constructor is
`tgtDecayBound_of_steps`.

## Proof

1. **Exact derivative** (`tdc_xiDeriv_eq`): for Hermitian `H^{(e)}` off the exterior poles,
   `∂_{ξ_g} ε_{e,k} = -W⁻¹ Tr P_k R_e⁰ B_{eg} R_e⁰` with `R_e⁰ = (K_e - sμ)⁻¹` and
   `B_{eg} = ∂_{ξ_g} K_e` (`tgt_hasDerivAt_edgeSchur`); a.s. under every edge splitting.
2. **The explicit law** (`tgt_eLpNorm_residual_eq`): `H^{(e)}` is the assembly of the residual
   pair `V ~ rpLaw` and the exterior path `π ~ pathLaw (n-2)`; in these coordinates
   (`tdc_pairF_assemble`) the derivative is `-W⁻¹ Tr P_a R⁰ (P' + S_π) R⁰`, `P' = (P_g)_{SS}` (a
   direct injection inside the pair, nonzero only for `d(e, g) = 1`) and
   `S_π = B_p*(H_π - E)⁻¹ P_τ (H_π - E)⁻¹ B_p = K*YK`, `Y` the tagged source of the exterior
   path with the tag `τ` of the blocks `g, g+1` (`tdc_source_eq`).
3. **The final residual pair** (`TdcPairStep`, a named statement with its full content): with a
   fixed stability gap and a bounded coefficient, conditionally on the path,
   `‖W⁻¹ Tr P_a R⁰ K*YK R⁰‖_{L^q(rpLaw)} ≤ C (max_i |D_i(X, Y)| + (d(X) + W^{-1/2}) u)`.
4. **The path** (`tdc_path_decay`, from `TdcLayerMean`): `‖max_i |D_i|‖_q ≤ C(q_*^ℓ + W^{-1/2})`
   with `ℓ ≥ d(e,g) - 2` untagged layers after the last injection ("at least `d(e,g) - 2`
   untagged layers remain after its last injection"), the clock moments (`tdc_path_clock`) and
   the scalar moments of the matched-traces theorem (path clause).
5. **Assembly** (`tgtDecayBound_of_steps`): `ρ = max(q_*, 1/2)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.Inputs (GaussianLpGradient ConditionalBlockGUECount)
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. The exact derivative of `ε_{e,k}` along `P_{S_g}`
-/

section PairFormula

variable {p : Parameters} {e : ZMod p.n}

/-- `R_e⁰ = (K_e - sμ)⁻¹`. -/
def tdcR0 (e : ZMod p.n) (Hres : p.SiteMatrix) (E : ℝ) : PairMatrix p e :=
  (edgeSchur p e Hres E - tgtZeta p E • 1)⁻¹

/-- The pair formula `-W⁻¹ Tr P_k R_e⁰ B_{eg} R_e⁰`. -/
def tdcPairF (e g k : ZMod p.n) (E : ℝ) (Hres : p.SiteMatrix) : ℂ :=
  -pairBlockTrace p e (tdcR0 e Hres E * tgtB p e g Hres E * tdcR0 e Hres E) k

theorem tdc_pairProjector_isHermitian (g : ZMod p.n) : (pairProjector p g).IsHermitian := by
  unfold pairProjector
  refine isHermitian_diagonal_of_self_adjoint _ ?_
  funext x
  simp only [Pi.star_apply]
  split_ifs <;> simp

/-- The pair block trace as a real-linear continuous map. -/
def tdcPairTraceCLM (e k : ZMod p.n) : PairMatrix p e →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => pairBlockTrace p e M k
      map_add' := fun A B => by
        unfold pairBlockTrace
        rw [← mul_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        split_ifs <;> simp
      map_smul' := fun r A => by
        unfold pairBlockTrace
        simp only [Matrix.smul_apply, RingHom.id_apply, Complex.real_smul]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        split_ifs <;> ring }

theorem tdc_isUnit_K_sub {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) {E : ℝ} (hE : |E| < 2) :
    IsUnit (edgeSchur p e Hres E - tgtZeta p E • 1).det := by
  have hU := dcv_K_isUnit (tgt_edgeSchur_isHermitian (e := e) hH E) (tgt_zeta_im_pos (p := p) hE)
  have hneg : edgeSchur p e Hres E - tgtZeta p E • 1 = -(tgtZeta p E • 1 - edgeSchur p e Hres E) := by
    abel
  rw [hneg, Matrix.det_neg]
  exact (isUnit_pow_iff (by simp)).mpr (by simp) |>.mul hU

/-- **The exact `ξ_g`-derivative in Schur form**: for Hermitian `H^{(e)}`,
`|E| < 2` and `H^{(e)}_R - E` invertible, `∂_{ξ_g} ε_{e,k} = -W⁻¹ Tr P_k R_e⁰ B_{eg} R_e⁰`. -/
theorem tdc_xiDeriv_eq (g : ZMod p.n) {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) {E : ℝ}
    (hE : |E| < 2) (hdet : (exteriorBlock p e Hres - (E : ℂ) • 1).det ≠ 0) (k : ZMod p.n) :
    tgtXiDeriv p (fun H => tgtEps p e H E k) g Hres = tdcPairF e g k E Hres := by
  set P := pairProjector p g
  have hPh : P.IsHermitian := tdc_pairProjector_isHermitian g
  have hHt : ∀ t : ℝ, (Hres + (t : ℂ) • P).IsHermitian := fun t => by
    refine hH.add ?_
    unfold IsHermitian
    rw [conjTranspose_smul, hPh.eq, Complex.star_def, Complex.conj_ofReal]
  have hcont : Continuous (fun t : ℝ => (exteriorBlock p e (Hres + (t : ℂ) • P) - (E : ℂ) • 1).det) := by
    have : (fun t : ℝ => (exteriorBlock p e (Hres + (t : ℂ) • P) - (E : ℂ) • 1).det) =
        fun t : ℝ => ((exteriorBlock p e Hres - (E : ℂ) • 1) + (t : ℂ) • exteriorBlock p e P).det := by
      funext t; rw [tgt_exteriorBlock_add, tgt_exteriorBlock_smul]; congr 1; abel
    rw [this]
    exact (continuous_const.add (Complex.continuous_ofReal.smul continuous_const)).matrix_det
  have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      (exteriorBlock p e (Hres + (t : ℂ) • P) - (E : ℂ) • 1).det ≠ 0 := by
    have h0 : (fun t : ℝ => (exteriorBlock p e (Hres + (t : ℂ) • P) - (E : ℂ) • 1).det) 0 ≠ 0 := by
      simpa using hdet
    exact hcont.continuousAt.eventually_ne h0
  have hfun : (fun t : ℝ => tgtEps p e (Hres + (t : ℂ) • P) E k) =ᶠ[𝓝 (0 : ℝ)]
      fun t : ℝ => tdcPairTraceCLM e k ((edgeSchur p e (Hres + (t : ℂ) • P) E - tgtZeta p E • 1)⁻¹) -
        tgtMu E := by
    filter_upwards [hev] with t ht
    unfold tgtEps tgtR0
    rw [BlockBand.Center.ctr_compressed_eq_schur (hHt t) ht]
    rfl
  have hK : HasDerivAt (fun t : ℝ => edgeSchur p e (Hres + (t : ℂ) • P) E - tgtZeta p E • 1)
      (tgtB p e g Hres E) 0 := (tgt_hasDerivAt_edgeSchur e g Hres E hdet).sub_const _
  have hU : IsUnit ((fun t : ℝ => edgeSchur p e (Hres + (t : ℂ) • P) E - tgtZeta p E • 1) 0).det := by
    simpa using tdc_isUnit_K_sub (e := e) hH hE
  have hinv := tgt_hasDerivAt_inv_comp hK hU
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at hinv
  have hd : HasDerivAt (fun t : ℝ => tdcPairTraceCLM e k
      ((edgeSchur p e (Hres + (t : ℂ) • P) E - tgtZeta p E • 1)⁻¹) - tgtMu E)
      (tdcPairTraceCLM e k (-((edgeSchur p e Hres E - tgtZeta p E • 1)⁻¹ * tgtB p e g Hres E *
        (edgeSchur p e Hres E - tgtZeta p E • 1)⁻¹))) 0 :=
    ((tdcPairTraceCLM e k).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hinv).sub_const (tgtMu E)
  unfold tgtXiDeriv
  rw [hfun.deriv_eq, hd.deriv]
  unfold tdcPairF tdcR0
  change pairBlockTrace p e _ k = _
  rw [show -((edgeSchur p e Hres E - tgtZeta p E • 1)⁻¹ * tgtB p e g Hres E *
      (edgeSchur p e Hres E - tgtZeta p E • 1)⁻¹) = (-1 : ℝ) • ((edgeSchur p e Hres E -
        tgtZeta p E • 1)⁻¹ * tgtB p e g Hres E * (edgeSchur p e Hres E - tgtZeta p E • 1)⁻¹) by
    rw [neg_one_smul]]
  change tdcPairTraceCLM e k ((-1 : ℝ) • _) = _
  rw [map_smul, neg_one_smul]
  rfl

end PairFormula

/-!
## 2. Transfer to the explicit law of `H^{(e)}`
-/

section Transfer

variable {p : Parameters}

theorem tdc_measurable_blocks (e : ZMod p.n) :
    Measurable (fun H : p.SiteMatrix => exteriorBlock p e H) ∧
      Measurable (fun H : p.SiteMatrix => couplingBlock p e H) ∧
        Measurable (fun H : p.SiteMatrix => pairBlock p e H) :=
  ⟨measurable_pi_iff.mpr fun _ => measurable_pi_iff.mpr fun _ => pg_entry measurable_id _ _,
    measurable_pi_iff.mpr fun _ => measurable_pi_iff.mpr fun _ => pg_entry measurable_id _ _,
    measurable_pi_iff.mpr fun _ => measurable_pi_iff.mpr fun _ => pg_entry measurable_id _ _⟩

theorem tdc_measurable_edgeSchur (e : ZMod p.n) (E : ℝ) :
    Measurable (fun H : p.SiteMatrix => edgeSchur p e H E) := by
  obtain ⟨h1, h2, h3⟩ := tdc_measurable_blocks (p := p) e
  unfold edgeSchur physicalCoareaF physicalCoareaResolvent
  exact (h3.sub (srec_measurable_mul (srec_measurable_mul (srec_measurable_conjTranspose h2)
    (measurable_matrix_inv.comp (h1.sub measurable_const))) h2)).sub measurable_const

theorem tdc_measurable_tgtB (e g : ZMod p.n) (E : ℝ) :
    Measurable (fun H : p.SiteMatrix => tgtB p e g H E) := by
  obtain ⟨h1, h2, -⟩ := tdc_measurable_blocks (p := p) e
  have hN : Measurable (fun H : p.SiteMatrix => (exteriorBlock p e H - (E : ℂ) • 1)⁻¹) :=
    measurable_matrix_inv.comp (h1.sub measurable_const)
  unfold tgtB
  exact measurable_const.add (srec_measurable_mul (srec_measurable_mul (srec_measurable_mul
    (srec_measurable_mul (srec_measurable_conjTranspose h2) hN) measurable_const) hN) h2)

theorem tdc_measurable_pairF (e g k : ZMod p.n) (E : ℝ) :
    Measurable (tdcPairF (p := p) e g k E) := by
  have hR : Measurable (fun H : p.SiteMatrix => tdcR0 e H E) :=
    measurable_matrix_inv.comp ((tdc_measurable_edgeSchur e E).sub measurable_const)
  unfold tdcPairF
  exact ((BlockBand.Center.ctr_continuous_pairBlockTrace k).measurable.comp
    (srec_measurable_mul (srec_measurable_mul hR (tdc_measurable_tgtB e g E)) hR)).neg

/-- **Transfer of the derivative to the explicit law**: under every edge splitting, at
deterministic `E ∈ bulkInterval κ`, the `L^q(X.P)` norm of `∂_{ξ_g} ε_{e,k}` is that of the pair
formula under `rpLaw ⊗ pathLaw (n-2)` at `H^{(e)} = assemble (rpSplitAssemble x) 0`. -/
theorem tdc_eLpNorm_xiDeriv {model : p.GaussianRingModel} (X : PairExtension p model)
    {e : ZMod p.n} {G : X.Ω → PairMatrix p e} (hs : IsCenterSplitting X G) {κ : ℝ} (hκ : 0 < κ)
    {E : ℝ} (hE : E ∈ bulkInterval κ) (g k : ZMod p.n) (q : ℝ≥0∞) :
    eLpNorm (fun ω => tgtXiDeriv p (fun H => tgtEps p e H E k) g (X.Hm ω - embedPair p e (G ω)))
        q X.P =
      eLpNorm (fun x => tdcPairF e g k E (assemble p e (rpSplitAssemble e x) 0)) q
        ((rpLaw p.W p.b (splitS p)).prod (pathLaw p.W (p.n - 2) p.b)) := by
  have hE2 : |E| < 2 := abs_lt_two_of_mem_bulkInterval hκ hE
  rw [← tgt_eLpNorm_residual_eq X hs (tdc_measurable_pairF e g k E) q]
  refine eLpNorm_congr_ae ?_
  filter_upwards [tgt_ae_residual_isHermitian X hs, tgt_ae_residual_exterior_det X hs E]
    with ω hH hd
  exact tdc_xiDeriv_eq g hH hE2 hd k

end Transfer

/-!
## 3. The pair formula in residual-pair and path coordinates
-/

section Coordinates

variable {p : Parameters}

theorem tdc_ext_assemble (e : ZMod p.n) (ω : SplitState p e) :
    exteriorBlock p e (assemble p e ω 0) = ω.1 := by
  ext x y; exact rsl_assemble_ee e ω 0 x y

theorem tdc_coup_assemble (e : ZMod p.n) (ω : SplitState p e) :
    couplingBlock p e (assemble p e ω 0) = ω.2.1 := by
  ext x y; exact rsl_assemble_ep e ω 0 x y

theorem tdc_pair_assemble (e : ZMod p.n) (ω : SplitState p e) :
    pairBlock p e (assemble p e ω 0) = ω.2.2 := by
  ext x y
  change assemble p e ω 0 x.1 y.1 = _
  rw [rsl_assemble_pp]; simp

theorem tdc_rpExtEquiv_val (e : ZMod p.n) (j : Fin (p.n - 2)) (x : Fin p.W) :
    (rpExtEquiv e (j, x)).1 = (rngBlk e (j.val + 2), x) := rfl

/-- The position tag of the exterior blocks `g, g+1` (exterior position `j ↔` ring block
`e + 2 + j`). -/
def tdcTag (e g : ZMod p.n) : ℕ → Bool :=
  fun j => decide (j < p.n - 2 ∧ (rngBlk e (j + 2) = g ∨ rngBlk e (j + 2) = g + 1))

/-- `(P_g)_{RR}` in path coordinates is the tag projection `clkProj (tdcTag e g)`. -/
theorem tdc_extProj (e g : ZMod p.n) :
    exteriorBlock p e (pairProjector p g) =
      (clkProj (W := p.W) fun j : Fin (p.n - 2) => tdcTag e g j).submatrix (rpExtEquiv e).symm
        (rpExtEquiv e).symm := by
  ext x y
  obtain ⟨u, rfl⟩ := (rpExtEquiv e).surjective x
  obtain ⟨v, rfl⟩ := (rpExtEquiv e).surjective y
  simp only [exteriorBlock, pairProjector, clkProj, submatrix_apply, Equiv.symm_apply_apply,
    diagonal_apply]
  have hinj : (rpExtEquiv e u).1 = (rpExtEquiv e v).1 ↔ u = v :=
    ⟨fun h => (rpExtEquiv e).injective (Subtype.ext h), fun h => by rw [h]⟩
  by_cases huv : u = v
  · subst huv
    simp only [ite_true]
    obtain ⟨j, a⟩ := u
    rw [tdc_rpExtEquiv_val]
    simp [tdcTag, j.isLt]
  · have h1 : ¬ (rpExtEquiv e u).1 = (rpExtEquiv e v).1 := fun h => huv (hinj.mp h)
    simp only [h1, huv, ite_false]

/-- `(P_g)_{SS}` in pair coordinates. -/
def tdcPairProj (e g : ZMod p.n) : Matrix (Fin 2 × Fin p.W) (Fin 2 × Fin p.W) ℂ :=
  (pairBlock p e (pairProjector p g)).submatrix (rpPairEquiv e) (rpPairEquiv e)

theorem tdc_pairProj_eq (e g : ZMod p.n) :
    pairBlock p e (pairProjector p g) =
      (tdcPairProj e g).submatrix (rpPairEquiv e).symm (rpPairEquiv e).symm := by
  rw [tdcPairProj, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]

/-- `(P_g)_{SS}` is a diagonal `0/1` matrix. -/
theorem tdc_pairProj_diag (e g : ZMod p.n) :
    tdcPairProj e g = diagonal fun y =>
      if (rpPairEquiv e y).1.1 = g ∨ (rpPairEquiv e y).1.1 = g + 1 then 1 else 0 := by
  ext x y
  simp only [tdcPairProj, pairBlock, pairProjector, submatrix_apply, diagonal_apply]
  by_cases hxy : x = y
  · subst hxy; simp
  · have : (rpPairEquiv e x).1 ≠ (rpPairEquiv e y).1 := fun h =>
      hxy ((rpPairEquiv e).injective (Subtype.ext h))
    simp only [this, hxy, ite_false]

theorem tdc_norm_pairProj_le (e g : ZMod p.n) : ‖tdcPairProj e g‖ ≤ 1 := by
  rw [tdc_pairProj_diag, l2_opNorm_diagonal]
  refine pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun x => ?_
  split_ifs <;> simp

/-- The path source `S_π = B_p*(H_π - E)⁻¹ P_τ (H_π - E)⁻¹ B_p`. -/
def tdcPathSource {W r : ℕ} (E : ℝ) (τ : Fin r → Bool) (π : PathSample W r) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (pathPortCoupling π)ᴴ * (pathMatrix π - (E : ℂ) • 1)⁻¹ * clkProj (W := W) τ *
    (pathMatrix π - (E : ℂ) • 1)⁻¹ * pathPortCoupling π

/-- The residual-pair resolvent `R⁰ = (V - E - X - sμ)⁻¹`, `μ = ā`, of the tagged-trace lemma. -/
def tdcPairRes {W : ℕ} (b E : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (v : RpSample W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (rpMatrix v - (E : ℂ) • 1 - X - (((min (1 - 2 * b) b : ℝ) : ℂ) * tgtMu E) • 1)⁻¹

theorem tdc_sub_smul_submatrix {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (σ : m ≃ n) (M : Matrix n n ℂ) (c : ℂ) :
    M.submatrix σ σ - c • (1 : Matrix m m ℂ) = (M - c • 1).submatrix σ σ := by
  rw [show (M - c • 1).submatrix σ σ = M.submatrix σ σ - c • (1 : Matrix n n ℂ).submatrix σ σ
    from rfl, submatrix_one_equiv]

/-- **The pair formula in coordinates** (deterministic): at `H^{(e)} = assemble (rpSplitAssemble x) 0`,
for the pair block `k = e + rpPairOff a`,
`-W⁻¹ Tr P_k R_e⁰ B_{eg} R_e⁰ = -W⁻¹ Tr_a R⁰ (P' + S_π) R⁰` with `R⁰ = tdcPairRes`,
`P' = (P_g)_{SS}` and `S_π` the path source with the tag of `g, g+1`. -/
theorem tdc_pairF_assemble (e g : ZMod p.n) (E : ℝ) (x : RpSample p.W × PathSample p.W (p.n - 2))
    (a : Fin 2) :
    tdcPairF e g (rngBlk e (rpPairOff a)) E (assemble p e (rpSplitAssemble e x) 0) =
      -blockTrace (tdcPairRes p.b E (pathSchur E x.2) x.1 *
        (tdcPairProj e g + tdcPathSource E (fun j : Fin (p.n - 2) => tdcTag e g j) x.2) *
          tdcPairRes p.b E (pathSchur E x.2) x.1) a := by
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
  unfold tdcPairF
  rw [hR, hB, submatrix_mul_equiv, submatrix_mul_equiv, rp_pairBlockTrace_submatrix]

end Coordinates

/-!
## 4. The final residual-pair step
-/

/-- **The final residual pair** (named statement; "The final residual pair has a
fixed stability gap, as in the matched-traces theorem; it needs a bounded coefficient, not a
further contraction"). Law: the residual pair layer `rpLaw W b s`, `s = min(1 - 2b, b)`
(`A_j ~ GUE_W((c - s/2)/W)`, bond `Gin((b - s/2)/W)`), conditional on the deterministic
Hermitian exterior Schur matrix `X` and the clock `Y ⪰ 0` of the exterior path (source
`S = K*YK`, `K = z_∂ - X`). Object: `W⁻¹ Tr P_a R⁰ S R⁰` with `R⁰ = (V - E - X - sμ)⁻¹`,
`μ = ā` (`tdcPairRes`), the `S`-insertion part of `∂_{ξ_g} ε_{e,k}` (`tdc_pairF_assemble`).
Quantifiers: `b ∈ (0, 1/2)`, `κ > 0` and the moment order `q ≥ 1` first; then `C ≥ 0`, `W₀`;
uniformly in `W ≥ W₀`, Hermitian `X`, `Y ⪰ 0`, `E ∈ bulkInterval κ` and `a ∈ {0, 1}`:
`‖W⁻¹ Tr P_a R⁰ S R⁰‖_{L^q(rpLaw)} ≤ C (max_i |D_i(X, Y)| + (d(X) + W^{-1/2}) W⁻¹ Tr Y)`.
(proof idea: differentiate the residual-pair mean equation (`BlockBand.Layers.ResidualLayerMeans`)
along `X - hS`; the mean-field inverse at the matched point is `(z_∂ - X)⁻¹` since
`(c - s/2) + (b - s/2) + s = 1 - b`, so the source is `D(X, Y)` up to `Cd(X)u`; the stability gap
`s/(1-b)` bounds the coefficient; the covariance derivative is `O(u/W)` and the Gaussian noise
`O_q(u/√W)`. No restriction `d(X) ≤ d₀` is needed: for `d(X) ≥ d₀` the crude bound
`‖K R⁰‖ ≤ C(1 + ‖V‖)` and the moments of `‖V‖` give `C u ≤ (C/d₀) d(X) u`.) -/
def TdcPairStep : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ q : ℝ, 1 ≤ q →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ X Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → Y.PosSemidef →
      ∀ E ∈ bulkInterval κ, ∀ a : Fin 2,
        eLpNorm (fun v : RpSample W => blockTrace (tdcPairRes b E X v *
            ((tdcK b E X)ᴴ * Y * tdcK b E X) * tdcPairRes b E X v) a)
          (ENNReal.ofReal q) (rpLaw W b (min (1 - 2 * b) b)) ≤
        ENNReal.ofReal (C * (tdcMaxD b E X Y +
          (matchedDistance b E X + (W : ℝ) ^ (-(1 / 2 : ℝ))) * clkTrace Y))

/-!
## 5. Bounds on the final pair
-/

section Bounds

variable {p : Parameters}

/-- `‖R⁰‖ ≤ y⁻¹` for `0 < y ≤ Im(sμ)` (`V - X` Hermitian). -/
theorem tdc_norm_pairRes_le {W : ℕ} {b E : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) (v : RpSample W) (hv : ∀ j, (v.1 j).IsHermitian) {y : ℝ} (hy : 0 < y)
    (hyc : y ≤ ((((min (1 - 2 * b) b : ℝ) : ℂ) * tgtMu E)).im) :
    ‖tdcPairRes b E X v‖ ≤ y⁻¹ := by
  set c : ℂ := ((min (1 - 2 * b) b : ℝ) : ℂ) * tgtMu E
  have hH : (rpMatrix v - (E : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X).IsHermitian := by
    refine ((rp_rpMatrix_isHermitian v hv).sub ?_).sub hX
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  have hc : (rpMatrix v - (E : ℂ) • 1 - X - c • 1)ᴴ =
      (rpMatrix v - (E : ℂ) • 1 - X) - diagonal (fun _ => star c) := by
    rw [conjTranspose_sub, hH.eq, conjTranspose_smul, conjTranspose_one, smul_one_eq_diagonal (star c)]
  unfold tdcPairRes
  rw [← l2_opNorm_conjTranspose, conjTranspose_nonsing_inv, hc]
  refine lct_norm_shifted_inv_le _ hH _ hy fun _ => ?_
  rw [Complex.star_def, Complex.conj_im, neg_neg]
  exact hyc

/-- A uniform lower bound for `Im(sμ)` on `bulkInterval κ`. -/
theorem tdc_im_smu_lower {b κ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) :
    ∃ y : ℝ, 0 < y ∧ ∀ E ∈ bulkInterval κ,
      y ≤ ((((min (1 - 2 * b) b : ℝ) : ℂ) * tgtMu E)).im := by
  have hs : 0 < min (1 - 2 * b) b := lt_min (by linarith) hb0
  refine ⟨min (1 - 2 * b) b * Real.sqrt (2 * κ) / 2, by positivity, fun E hE => ?_⟩
  have hm : (tgtMu E).im = Real.sqrt (4 - E ^ 2) / 2 := by
    simp [tgtMu, matchedA]; ring
  rw [Complex.im_ofReal_mul, hm]
  obtain ⟨h1, h2⟩ := hE
  have hκ2 : κ ≤ 2 := by linarith
  have h4 : 2 * κ ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt h4
  have hs' := hs.le
  nlinarith

/-- `‖W⁻¹ Tr_a R P' R‖ ≤ ‖R‖²`. -/
theorem tdc_norm_T1_le (e g : ZMod p.n) (R : Matrix (Fin 2 × Fin p.W) (Fin 2 × Fin p.W) ℂ)
    (a : Fin 2) : ‖blockTrace (R * tdcPairProj e g * R) a‖ ≤ ‖R‖ ^ 2 := by
  refine (lct_norm_blockTrace_le _ a).trans ?_
  calc ‖R * tdcPairProj e g * R‖ ≤ ‖R‖ * ‖tdcPairProj e g‖ * ‖R‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ‖R‖ * 1 * ‖R‖ := by gcongr; exact tdc_norm_pairProj_le e g
    _ = ‖R‖ ^ 2 := by ring

/-!
### Ring combinatorics
-/

theorem tdc_sub_val_pos {e g : ZMod p.n} (hg : g ≠ e) : 0 < (g - e).val := by
  rw [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero, sub_eq_zero]; exact hg

theorem tdc_edgeDistance_eq {e g : ZMod p.n} (hg : g ≠ e) :
    edgeDistance p e g = min (g - e).val (p.n - (g - e).val) := by
  unfold edgeDistance
  rw [show e - g = -(g - e) by ring, ZMod.neg_val]
  simp only [sub_ne_zero.mpr hg, ite_false]

theorem tdc_val_of_eq {e g : ZMod p.n} {o : ℕ} (ho : o < p.n) (h : rngBlk e o = g) :
    (g - e).val = o := by
  rw [← h]
  simp only [rngBlk, add_sub_cancel_left, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt ho

theorem tdc_val_of_eq_succ {e g : ZMod p.n} {o : ℕ} (ho : o + 1 < p.n) (h : rngBlk e (o + 1) = g + 1) :
    (g - e).val = o := by
  have : g = rngBlk e o := by
    have h' : rngBlk e o + 1 = g + 1 := by rw [rngBlk_succ]; exact h
    exact (add_right_cancel h').symm
  exact tdc_val_of_eq (by omega) this.symm

/-- The tagged exterior positions are `m - 2` and `m - 1`, `m = (g - e).val`. -/
theorem tdc_tag_pos {e g : ZMod p.n} {j : ℕ} (h : tdcTag e g j = true) :
    j = (g - e).val - 2 ∨ j = (g - e).val - 1 := by
  simp only [tdcTag, decide_eq_true_eq] at h
  obtain ⟨hj, h1 | h1⟩ := h
  · left; rw [tdc_val_of_eq (by omega) h1]; omega
  · right; rw [tdc_val_of_eq_succ (o := j + 1) (by omega) h1]; omega

/-- Every tagged exterior position is at distance `≥ d(e, g) - 2` from both ends of the exterior
path. -/
theorem tdc_tag_dist {e g : ZMod p.n} (hg : g ≠ e) {j : ℕ} (hj : j < p.n - 2)
    (h : tdcTag e g j = true) :
    edgeDistance p e g - 2 ≤ j ∧ edgeDistance p e g - 2 + j + 1 ≤ p.n - 2 := by
  rw [tdc_edgeDistance_eq hg]
  simp only [tdcTag, decide_eq_true_eq] at h
  obtain ⟨-, h1 | h1⟩ := h
  · have := tdc_val_of_eq (by omega) h1; omega
  · have := tdc_val_of_eq_succ (o := j + 1) (by omega) h1; omega

/-- `(P_g)_{SS} = 0` as soon as `d(e, g) ≥ 2`. -/
theorem tdc_pairProj_zero {e g : ZMod p.n} (hg : g ≠ e) (hd : 2 ≤ edgeDistance p e g) :
    tdcPairProj e g = 0 := by
  have : Fact (1 < p.n) := ⟨by have := p.n_ge_four; omega⟩
  rw [tdc_pairProj_diag]
  ext x y
  simp only [diagonal_apply, Matrix.zero_apply]
  split_ifs with hxy hc
  · exfalso
    rw [tdc_edgeDistance_eq hg] at hd
    have hpair := (rpPairEquiv e x).2
    have hlt : (g - e).val < p.n := ZMod.val_lt _
    rcases hpair with h1 | h1 <;> rcases hc with h2 | h2
    · exact hg (h2.symm.trans h1)
    · -- `e = g + 1`
      have : g - e = -1 := by rw [← h1, h2]; ring
      rw [this, ZMod.neg_val] at hd
      simp only [one_ne_zero, ite_false, ZMod.val_one] at hd
      omega
    · -- `e + 1 = g`
      have : g - e = 1 := by rw [← h2, h1]; ring
      rw [this, ZMod.val_one] at hd
      omega
    · exact hg (add_right_cancel (h1.symm.trans h2)).symm
  · rfl
  · rfl

end Bounds

/-!
## 6. Fubini over the residual pair
-/

section Fubini

variable {p : Parameters}

theorem tdc_measurable_pairRes {Ω : Type*} [MeasurableSpace Ω] {W : ℕ} (b E : ℝ)
    {Xf : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {vf : Ω → RpSample W}
    (hX : Measurable Xf) (hv : Measurable vf) :
    Measurable (fun t => tdcPairRes b E (Xf t) (vf t)) := by
  unfold tdcPairRes
  exact measurable_matrix_inv.comp (((((rp_measurable_rpMatrix W).comp hv).sub
    measurable_const).sub hX).sub measurable_const)

theorem tdc_measurable_pathSource (W r : ℕ) (E : ℝ) (τ : Fin r → Bool) :
    Measurable (fun π : PathSample W r => tdcPathSource E τ π) := by
  have hM : Measurable (fun π : PathSample W r => (pathMatrix π - (E : ℂ) • 1)⁻¹) :=
    measurable_matrix_inv.comp ((measurable_pathMatrix W r).sub measurable_const)
  have hB := measurable_pathPortCoupling W r
  unfold tdcPathSource
  exact srec_measurable_mul (srec_measurable_mul (srec_measurable_mul (srec_measurable_mul
    (srec_measurable_conjTranspose hB) hM) measurable_const) hM) hB

theorem tdc_ae_path_herm (W r : ℕ) (b E : ℝ) :
    ∀ᵐ π ∂pathLaw W r b, (pathMatrix π).IsHermitian ∧ (pathSchur E π).IsHermitian := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  have h := ae_blocks_isHermitian r W (Real.toNNReal ((1 - 2 * b) / W))
  unfold pathLaw
  filter_upwards [(Measure.quasiMeasurePreserving_fst).ae h] with ω hω
  exact ⟨srec_pathMatrix_isHermitian ω hω, srec_pathSchur_isHermitian E ω hω⟩

/-- **The `S`-insertion term integrates** (Fubini over the residual pair, conditionally on the
exterior path): the conditional bound `TdcPairStep` and an `L^q(pathLaw)` bound `M` on
`max|D| + (d + w)u` give `‖W⁻¹ Tr_a R⁰ S_π R⁰‖_{L^q(rpLaw ⊗ pathLaw)} ≤ C₂ M`. -/
theorem tdc_T2_bound {r : ℕ} {E : ℝ} (hz : 0 < (boundaryZ p.b E).im) (τ : Fin r → Bool)
    (a : Fin 2) {q : ℝ} (hq : 1 ≤ q) {C₂ M w : ℝ} (hC₂ : 0 ≤ C₂) (hw : 0 ≤ w)
    (hpair : ∀ X Y : Matrix (Fin 2 × Fin p.W) (Fin 2 × Fin p.W) ℂ, X.IsHermitian →
      Y.PosSemidef →
      eLpNorm (fun v : RpSample p.W => blockTrace (tdcPairRes p.b E X v *
          ((tdcK p.b E X)ᴴ * Y * tdcK p.b E X) * tdcPairRes p.b E X v) a)
        (ENNReal.ofReal q) (rpLaw p.W p.b (splitS p)) ≤
      ENNReal.ofReal (C₂ * (tdcMaxD p.b E X Y + (matchedDistance p.b E X + w) * clkTrace Y)))
    (hG : eLpNorm (fun π : PathSample p.W r => tdcMaxD p.b E (pathSchur E π)
        (clkCoreSource p.b E τ π) + (matchedDistance p.b E (pathSchur E π) + w) *
          clkTrace (clkCoreSource p.b E τ π)) (ENNReal.ofReal q) (pathLaw p.W r p.b) ≤
      ENNReal.ofReal M) :
    eLpNorm (fun x : RpSample p.W × PathSample p.W r => blockTrace
        (tdcPairRes p.b E (pathSchur E x.2) x.1 * tdcPathSource E τ x.2 *
          tdcPairRes p.b E (pathSchur E x.2) x.1) a) (ENNReal.ofReal q)
      ((rpLaw p.W p.b (splitS p)).prod (pathLaw p.W r p.b)) ≤ ENNReal.ofReal (C₂ * M) := by
  have hq0 : (0 : ℝ) < q := by linarith
  set T2 := fun x : RpSample p.W × PathSample p.W r => blockTrace
    (tdcPairRes p.b E (pathSchur E x.2) x.1 * tdcPathSource E τ x.2 *
      tdcPairRes p.b E (pathSchur E x.2) x.1) a with hT2
  have hX2 : Measurable (fun x : RpSample p.W × PathSample p.W r => pathSchur E x.2) :=
    (measurable_pathSchur p.W r E).comp measurable_snd
  have hRm := tdc_measurable_pairRes (Ω := RpSample p.W × PathSample p.W r) p.b E hX2 measurable_fst
  have hT2m : Measurable T2 :=
    (tdc_continuous_blockTrace a).measurable.comp (srec_measurable_mul (srec_measurable_mul hRm
      ((tdc_measurable_pathSource p.W r E τ).comp measurable_snd)) hRm)
  set F : PathSample p.W r × RpSample p.W → ℝ := fun y => ‖T2 (y.2, y.1)‖ with hF
  have hFm : Measurable F := hT2m.norm.comp (measurable_snd.prodMk measurable_fst)
  set gfun : PathSample p.W r → ℝ := fun π => tdcMaxD p.b E (pathSchur E π)
    (clkCoreSource p.b E τ π) + (matchedDistance p.b E (pathSchur E π) + w) *
      clkTrace (clkCoreSource p.b E τ π) with hgfun
  have hg0 : ∀ π, 0 ≤ gfun π := fun π => by
    have := tdcMaxD_nonneg p.b E (pathSchur E π) (clkCoreSource p.b E τ π)
    have := clk_matchedDistance_nonneg p.b E (pathSchur E π)
    have := clkTrace_nonneg (clkCoreSource_posSemidef p.b E τ π)
    simp only [hgfun]; positivity
  have hgm : Measurable (fun π => C₂ * gfun π) := by
    have hX := measurable_pathSchur p.W r E
    have hY := clk_measurable_coreSource p.W r p.b E τ
    exact measurable_const.mul ((tdc_measurable_maxD p.b E hX hY).add
      ((((srec_measurable_matchedDistance p.b E p.W).comp hX).add measurable_const).mul
        (clk_measurable_trace hY)))
  have h1 : eLpNorm T2 (ENNReal.ofReal q) ((rpLaw p.W p.b (splitS p)).prod (pathLaw p.W r p.b)) =
      eLpNorm F (ENNReal.ofReal q) ((pathLaw p.W r p.b).prod (rpLaw p.W p.b (splitS p))) := by
    rw [← eLpNorm_norm _ hT2m.aestronglyMeasurable]
    rw [← eLpNorm_comp_measurePreserving hT2m.norm.aestronglyMeasurable
      (Measure.measurePreserving_swap (μ := pathLaw p.W r p.b) (ν := rpLaw p.W p.b (splitS p)))]
    rfl
  rw [h1]
  refine (clk_eLpNorm_prod_le hFm hgm hq0 (c := 1) ?_).trans ?_
  · filter_upwards [tdc_ae_path_herm p.W r p.b E] with π ⟨hH, hX⟩
    rw [ENNReal.ofReal_one, one_mul, Real.enorm_eq_ofReal (mul_nonneg hC₂ (hg0 π))]
    have hS := tdc_source_eq hz τ π hH hX
    have e : (fun v => F (π, v)) = fun v => ‖blockTrace (tdcPairRes p.b E (pathSchur E π) v *
        ((tdcK p.b E (pathSchur E π))ᴴ * clkCoreSource p.b E τ π * tdcK p.b E (pathSchur E π)) *
          tdcPairRes p.b E (pathSchur E π) v) a‖ := by
      funext v; simp only [hF, hT2, tdcPathSource, hS]
    have hm : Measurable (fun v : RpSample p.W => tdcPairRes p.b E (pathSchur E π) v) :=
      tdc_measurable_pairRes p.b E measurable_const measurable_id
    rw [e, eLpNorm_norm]
    swap
    · exact ((tdc_continuous_blockTrace a).measurable.comp (srec_measurable_mul
        (srec_measurable_mul hm measurable_const) hm)).aestronglyMeasurable
    exact hpair _ _ hX (clkCoreSource_posSemidef p.b E τ π)
  · rw [ENNReal.ofReal_one, one_mul]
    exact tdc_eLpNorm_smul_le hC₂ hG

end Fubini

/-!
## 7. Assembly
-/

section Assembly

variable {p : Parameters}

theorem tdc_blockTrace_add {W : ℕ} (A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    blockTrace (A + B) i = blockTrace A i + blockTrace B i := by
  unfold blockTrace
  simp only [Matrix.add_apply, Finset.sum_add_distrib, mul_add]

/-- Almost surely under `rpLaw ⊗ pathLaw` the residual-pair blocks and the path Schur matrix are
Hermitian. -/
theorem tdc_ae_prod_herm (W r : ℕ) (b s E : ℝ) :
    ∀ᵐ x ∂(rpLaw W b s).prod (pathLaw W r b),
      (∀ j, (x.1.1 j).IsHermitian) ∧ (pathSchur E x.2).IsHermitian := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  have h1 : ∀ᵐ v ∂rpLaw W b s, ∀ j, (v.1 j).IsHermitian := by
    unfold rpLaw
    exact (Measure.quasiMeasurePreserving_fst).ae
      (ae_blocks_isHermitian 2 W (Real.toNNReal ((1 - 2 * b - s / 2) / W)))
  filter_upwards [(Measure.quasiMeasurePreserving_fst).ae h1,
    (Measure.quasiMeasurePreserving_snd).ae (srec_ae_pathSchur_isHermitian W r b E)] with x hx1 hx2
  exact ⟨hx1, hx2⟩

/-- The final arithmetic: `c₁ + C₂ (C₃ (q^ℓ + w) + B' w) ≤ (A + B)(ρ^d + w)`. -/
theorem tdc_final_arith {ρ qs y C₂ C₃ B' w c₁ : ℝ} {d ℓ : ℕ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hqs0 : 0 ≤ qs) (hqs : qs ≤ ρ) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hB' : 0 ≤ B') (hw : 0 ≤ w)
    (hdℓ : d ≤ ℓ + 2) (hc₁' : 2 ≤ d ∨ c₁ ≤ (y⁻¹) ^ 2) (hc₁'' : 2 ≤ d → c₁ = 0) :
    c₁ + C₂ * (C₃ * (qs ^ ℓ + w) + B' * w) ≤
      ((y⁻¹) ^ 2 / ρ + C₂ * C₃ / ρ ^ 2 + C₂ * (C₃ + B')) * (ρ ^ d + w) := by
  have hρd : 0 ≤ ρ ^ d := pow_nonneg hρ0.le d
  have h1 : c₁ ≤ (y⁻¹) ^ 2 / ρ * ρ ^ d := by
    rcases le_or_gt 2 d with hd | hd
    · rw [hc₁'' hd]; positivity
    · have hc := hc₁'.resolve_left (by omega)
      have hpow : ρ ^ 1 ≤ ρ ^ d := pow_le_pow_of_le_one hρ0.le hρ1 (by omega)
      rw [pow_one] at hpow
      calc c₁ ≤ (y⁻¹) ^ 2 := hc
        _ = (y⁻¹) ^ 2 / ρ * ρ := by field_simp
        _ ≤ (y⁻¹) ^ 2 / ρ * ρ ^ d := by gcongr
  have h2 : qs ^ ℓ ≤ ρ ^ d / ρ ^ 2 := by
    have h3 : qs ^ ℓ ≤ ρ ^ ℓ := pow_le_pow_left₀ hqs0 hqs ℓ
    have h4 : ρ ^ (ℓ + 2) ≤ ρ ^ d := pow_le_pow_of_le_one hρ0.le hρ1 hdℓ
    rw [le_div_iff₀ (by positivity)]
    calc qs ^ ℓ * ρ ^ 2 ≤ ρ ^ ℓ * ρ ^ 2 := by gcongr
      _ = ρ ^ (ℓ + 2) := by ring
      _ ≤ ρ ^ d := h4
  have h5 : C₂ * C₃ * qs ^ ℓ ≤ C₂ * C₃ / ρ ^ 2 * ρ ^ d := by
    calc C₂ * C₃ * qs ^ ℓ ≤ C₂ * C₃ * (ρ ^ d / ρ ^ 2) := by gcongr
      _ = _ := by ring
  have hA : 0 ≤ (y⁻¹) ^ 2 / ρ + C₂ * C₃ / ρ ^ 2 := by positivity
  have hB : 0 ≤ C₂ * (C₃ + B') := by positivity
  nlinarith [mul_nonneg hA hw, mul_nonneg hB hρd]

/-- **The tagged decay bound (`TgtDecayBound`, a clause of the tagged-trace lemma), conditional on
the two isolated steps `TdcLayerMean` and `TdcPairStep`.**

*Statement.* `‖∂_{ξ_g} ε_{e,k}‖_{L^q(X.P)} ≤ C_q (ρ^{d(e,g)} + W^{-1/2})` for `g ≠ e`,
`k ∈ {e, e+1}`, with `ε_{e,k} = W⁻¹ Tr P_k R_e⁰ - μ`, `R_e⁰ = (K_e - sμ)⁻¹` (`tgtEps`, realized by
the compressed resolvent), `μ = ā`, `s = min(c, b)`, `d = edgeDistance`, and `∂_{ξ_g}` the
pointwise derivative of `t ↦ ε_{e,k}(H^{(e)} + t P_{S_g})` at `0` (`tgtXiDeriv`).

*Law.* Any extension `X` of the exact physical law (`X.Hm ~ model.law`) with an edge splitting
`IsCenterSplitting X G` (`G_e ~ GUE_{2W}(s/(2W))` independent of `H^{(e)} = H - G_e`); the
proof uses only the law of `H^{(e)}`, the explicit image of `rpLaw W b s ⊗ pathLaw W (n-2) b`
(`tgt_map_residual_eq`), and inside it the growing-path law `growthLaw` (`measurePreserving_pgPath`).

*Domain, quantifiers, uniformity.* `b ∈ (0, 1/2)`, `κ > 0`, `T` first; then `ρ ∈ [0, 1)`,
`ρ = max(q_*, 1/2)` with `q_*` of `TdcLayerMean` (depending on `b, κ` only); then the moment
order `q ≥ 1`; then `C_q, W₀`; uniformly in `W > W₀`, `n ≤ TW`, the model, the edge `e`, the
extension and splitting, deterministic `E ∈ bulkInterval κ`, `g ≠ e` and `k`.

*Norms.* `L^q(X.P)` norm (`eLpNorm`) of the complex scalar; the internal estimates use the `ℓ²`
operator norm on matrices and the normalized traces `W⁻¹ Tr`.

*Inputs.* `ConditionalBlockGUECount`, `GaussianLpGradient` (through `matchedTraces_holds`,
`scalarRecursionContract_holds` (`exit`), `clockMoments_holds`, `diffCovarianceFamily_holds'`
(noise clause)), and the two isolated statements `TdcLayerMean` (differentiated mean equation of
one untagged layer) and `TdcPairStep` (the final residual pair). No limits are taken. -/
theorem tgtDecayBound_of_steps (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient)
    (hM : TdcLayerMean) (hP : TdcPairStep) : TgtDecayBound := by
  intro b hb0 hb1 κ T hκ
  obtain ⟨qs, hqs0, hqs1, hPD⟩ := tdc_path_decay hcount hgrad hM b hb0 hb1 κ T hκ
  obtain ⟨y, hy, hyE⟩ := tdc_im_smu_lower hb0 hb1 hκ
  obtain ⟨η, hη, hbulk⟩ := srec_boundaryZ_im_lower (b := b) (by linarith) hκ
  set ρ := max qs (1 / 2) with hρ
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hρ1 : ρ < 1 := max_lt hqs1 (by norm_num)
  refine ⟨ρ, hρ0.le, hρ1, fun q hq => ?_⟩
  have hq0 : (0 : ℝ) < q := by linarith
  obtain ⟨C₃, W₃, hC₃, hdec⟩ := hPD q hq
  obtain ⟨C₂, W₂, hC₂, hpair⟩ := hP b hb0 hb1 κ hκ q hq
  obtain ⟨Cu, Wu, hCu, hclk⟩ := tdc_path_clock hcount hgrad b hb0 hb1 κ T hκ (2 * q) (by linarith)
  obtain ⟨ε₀, Cd, hε₀, hpath⟩ := (matchedTraces_holds hcount hgrad).path b hb0 hb1 κ T hκ
  set Cd' := max Cd 0 with hCd'
  have hCd'0 : 0 ≤ Cd' := le_max_right _ _
  set B' := (Cd' * Real.sqrt (2 * q) + 1) * Cu with hB'
  have hB'0 : 0 ≤ B' := by positivity
  refine ⟨(y⁻¹) ^ 2 / ρ + C₂ * C₃ / ρ ^ 2 + C₂ * (C₃ + B'),
    max (max (W₂ : ℝ) W₃) (max (Wu : ℝ) (2 * q / ε₀)), ?_⟩
  intro p hpb hnT hW model e X G hs E hE g hg k hk
  subst hpb
  have hW₂ : W₂ ≤ p.W := by
    have : (W₂ : ℝ) < p.W := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hW
    exact_mod_cast this.le
  have hW₃ : W₃ ≤ p.W := by
    have : (W₃ : ℝ) < p.W := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hW
    exact_mod_cast this.le
  have hWu : Wu ≤ p.W := by
    have : (Wu : ℝ) < p.W := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hW
    exact_mod_cast this.le
  have hWε : 2 * q ≤ ε₀ * p.W := by
    have : 2 * q / ε₀ < p.W := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hW
    rw [div_lt_iff₀ hε₀] at this; linarith
  have hW0 : 0 < p.W := p.W_pos
  have hWr : (0 : ℝ) < p.W := by exact_mod_cast hW0
  have hz : 0 < (boundaryZ p.b E).im := lt_of_lt_of_le hη (hbulk E hE).1
  set w := (p.W : ℝ) ^ (-(1 / 2 : ℝ)) with hw
  have hw0 : 0 ≤ w := tdc_rpow_half_nonneg _
  have hinvw : 1 / (p.W : ℝ) ≤ w := tdc_inv_le_rpow_half hW0
  set d := edgeDistance p e g with hd
  set ℓ := d - 2 with hℓdef
  obtain ⟨a, rfl⟩ : ∃ a : Fin 2, k = rngBlk e (rpPairOff a) := by
    rcases hk with rfl | rfl
    · exact ⟨1, by simp [rpPairOff, rngBlk_zero]⟩
    · exact ⟨0, by simp [rpPairOff, rngBlk]⟩
  rw [tdc_eLpNorm_xiDeriv X hs hκ hE g _ _]
  have hprob : IsProbabilityMeasure ((rpLaw p.W p.b (splitS p)).prod (pathLaw p.W (p.n - 2) p.b)) :=
    inferInstance
  set μ := (rpLaw p.W p.b (splitS p)).prod (pathLaw p.W (p.n - 2) p.b) with hμ
  set τ : Fin (p.n - 2) → Bool := fun j => tdcTag e g j with hτ
  set R := fun x : RpSample p.W × PathSample p.W (p.n - 2) => tdcPairRes p.b E (pathSchur E x.2) x.1
    with hR
  have hX2 : Measurable (fun x : RpSample p.W × PathSample p.W (p.n - 2) => pathSchur E x.2) :=
    (measurable_pathSchur p.W _ E).comp measurable_snd
  have hRm : Measurable R := tdc_measurable_pairRes p.b E hX2 measurable_fst
  set T1 := fun x => blockTrace (R x * tdcPairProj e g * R x) a with hT1
  set T2 := fun x => blockTrace (R x * tdcPathSource E τ x.2 * R x) a with hT2
  have hT1m : Measurable T1 := (tdc_continuous_blockTrace a).measurable.comp
    (srec_measurable_mul (srec_measurable_mul hRm measurable_const) hRm)
  have hT2m : Measurable T2 := (tdc_continuous_blockTrace a).measurable.comp
    (srec_measurable_mul (srec_measurable_mul hRm
      ((tdc_measurable_pathSource p.W _ E τ).comp measurable_snd)) hRm)
  have hfun : ∀ x, ‖tdcPairF e g (rngBlk e (rpPairOff a)) E (assemble p e (rpSplitAssemble e x) 0)‖ ≤
      ‖T1 x‖ + ‖T2 x‖ := by
    intro x
    rw [tdc_pairF_assemble, norm_neg, Matrix.mul_add, Matrix.add_mul, tdc_blockTrace_add]
    exact norm_add_le _ _
  -- the direct injection inside the pair
  set c₁ : ℝ := if 2 ≤ d then 0 else (y⁻¹) ^ 2 with hc₁
  have hc₁0 : 0 ≤ c₁ := by simp only [hc₁]; split_ifs <;> positivity
  have hT1b : eLpNorm (fun x => ‖T1 x‖) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal c₁ := by
    rw [eLpNorm_norm _ hT1m.aestronglyMeasurable]
    refine (eLpNorm_le_of_ae_bound (C := c₁) hT1m.aestronglyMeasurable ?_).trans ?_
    · filter_upwards [tdc_ae_prod_herm p.W (p.n - 2) p.b (splitS p) E] with x ⟨hv, hX⟩
      simp only [hc₁]
      split_ifs with h2
      · simp only [hT1, tdc_pairProj_zero hg h2, Matrix.mul_zero, Matrix.zero_mul]
        simp [blockTrace]
      · refine (tdc_norm_T1_le e g (R x) a).trans ?_
        have hRn := tdc_norm_pairRes_le hX x.1 hv hy (hyE E hE)
        exact pow_le_pow_left₀ (norm_nonneg _) hRn 2
    · rw [measure_univ, ENNReal.one_rpow, one_mul]
  -- the path source
  have hr : 1 ≤ p.n - 2 := by have := p.n_ge_four; omega
  have hrT : ((p.n - 2 : ℕ) : ℝ) ≤ T * p.W := by
    refine le_trans ?_ hnT
    exact_mod_cast Nat.sub_le _ _
  have htag : ∀ j, tdcTag e g j = true → j = (g - e).val - 2 ∨ j = (g - e).val - 1 :=
    fun j h => tdc_tag_pos h
  have hdist : ∀ j, j < p.n - 2 → tdcTag e g j = true → ℓ ≤ j ∧ ℓ + j + 1 ≤ p.n - 2 :=
    fun j hj h => tdc_tag_dist hg hj h
  have hmaxD := hdec p.W hW₃ hW0 (p.n - 2) hr hrT E hE (tdcTag e g) _ _ ℓ htag hdist
  have hu := hclk p.W hWu hW0 (p.n - 2) hr hrT E hE (tdcTag e g) _ _ htag
  have hdm := hpath p.W hW0 (2 * q) (by linarith) hWε (p.n - 2) hr hrT E hE
  set M := C₃ * (qs ^ ℓ + w) + B' * w with hM
  have hG : eLpNorm (fun π : PathSample p.W (p.n - 2) => tdcMaxD p.b E (pathSchur E π)
      (clkCoreSource p.b E τ π) + (matchedDistance p.b E (pathSchur E π) + w) *
        clkTrace (clkCoreSource p.b E τ π)) (ENNReal.ofReal q) (pathLaw p.W (p.n - 2) p.b) ≤
      ENNReal.ofReal M := by
    have hum : Measurable (fun π : PathSample p.W (p.n - 2) => clkTrace (clkCoreSource p.b E τ π)) :=
      clk_measurable_trace (clk_measurable_coreSource _ _ p.b E τ)
    have hdmm : Measurable (fun π : PathSample p.W (p.n - 2) =>
        matchedDistance p.b E (pathSchur E π)) :=
      (srec_measurable_matchedDistance p.b E p.W).comp (measurable_pathSchur _ _ E)
    have hdu : eLpNorm (fun π : PathSample p.W (p.n - 2) => matchedDistance p.b E (pathSchur E π) *
        clkTrace (clkCoreSource p.b E τ π)) (ENNReal.ofReal q) (pathLaw p.W (p.n - 2) p.b) ≤
        ENNReal.ofReal (Cd' * Real.sqrt (2 * q) * w * Cu) := by
      refine (wl_eLpNorm_mul_le hdmm.aestronglyMeasurable hum.aestronglyMeasurable hq0).trans ?_
      have h1 : ENNReal.ofReal (Cd * Real.sqrt (2 * q) / p.W) ≤
          ENNReal.ofReal (Cd' * Real.sqrt (2 * q) * w) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hs := Real.sqrt_nonneg (2 * q)
        calc Cd * Real.sqrt (2 * q) / p.W ≤ Cd' * Real.sqrt (2 * q) / p.W := by
              gcongr; exact le_max_left _ _
          _ = Cd' * Real.sqrt (2 * q) * (1 / p.W) := by ring
          _ ≤ Cd' * Real.sqrt (2 * q) * w := by gcongr
      calc _ ≤ ENNReal.ofReal (Cd' * Real.sqrt (2 * q) * w) * ENNReal.ofReal Cu :=
            mul_le_mul' (le_trans hdm h1) hu
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
    have hwu : eLpNorm (fun π : PathSample p.W (p.n - 2) => w * clkTrace (clkCoreSource p.b E τ π))
        (ENNReal.ofReal q) (pathLaw p.W (p.n - 2) p.b) ≤ ENNReal.ofReal (w * Cu) :=
      tdc_eLpNorm_smul_le hw0 ((eLpNorm_le_eLpNorm_of_exponent_le
        (ENNReal.ofReal_le_ofReal (by linarith))).trans hu)
    have e1 : (fun π : PathSample p.W (p.n - 2) => tdcMaxD p.b E (pathSchur E π)
        (clkCoreSource p.b E τ π) + (matchedDistance p.b E (pathSchur E π) + w) *
          clkTrace (clkCoreSource p.b E τ π)) = fun π => tdcMaxD p.b E (pathSchur E π)
        (clkCoreSource p.b E τ π) + (matchedDistance p.b E (pathSchur E π) *
          clkTrace (clkCoreSource p.b E τ π) + w * clkTrace (clkCoreSource p.b E τ π)) := by
      funext π; ring
    rw [e1]
    refine (tdc_eLpNorm_add_le hq (by positivity) (by positivity) hmaxD
      (tdc_eLpNorm_add_le hq (by positivity) (by positivity) hdu hwu)).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    simp only [hM, hB']; ring
  have hT2b : eLpNorm (fun x => ‖T2 x‖) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (C₂ * M) := by
    rw [eLpNorm_norm _ hT2m.aestronglyMeasurable]
    exact tdc_T2_bound hz τ a hq hC₂ hw0 (fun X' Y' hX' hY' =>
      hpair p.W hW0 hW₂ X' Y' hX' hY' E hE a) hG
  -- combination
  have hmeasF : AEStronglyMeasurable (fun x => tdcPairF e g (rngBlk e (rpPairOff a)) E
      (assemble p e (rpSplitAssemble e x) 0)) μ :=
    ((tdc_measurable_pairF e g _ E).comp ((rsl_measurable_assemble e).comp
      ((rp_measurable_splitAssemble e).prodMk measurable_const))).aestronglyMeasurable
  refine (eLpNorm_mono_real hmeasF hfun).trans ((tdc_eLpNorm_add_le hq hc₁0 (by
    have := pow_nonneg hqs0 ℓ; positivity) hT1b hT2b).trans (ENNReal.ofReal_le_ofReal ?_))
  refine tdc_final_arith hρ0 hρ1.le hqs0 (le_max_left _ _) hC₂ hC₃ hB'0 hw0 (by omega) ?_ ?_
  · simp only [hc₁]; split_ifs with h <;> [exact Or.inl h; exact Or.inr le_rfl]
  · intro h; simp only [hc₁, h, ite_true]

/-- **The tagged-trace lemma from `TgtLambdaBound` and the two isolated decay steps** (assembly with
`taggedTrace_of_open`). Same law, domain, norms and quantifiers as `TaggedTraceStatement`. -/
theorem taggedTrace_of_steps (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient)
    (hlam : TgtLambdaBound) (hM : TdcLayerMean) (hP : TdcPairStep) : TaggedTraceStatement :=
  taggedTrace_of_open hcount hgrad hlam (tgtDecayBound_of_steps hcount hgrad hM hP)

end Assembly

end BlockBand.Layers
