module

public import BlockBand.Critical.Collar.Density.CollarBlocks
public import BlockBand.Palm.MomentFlow.BridgeLaw

/-!
# The fresh-row three-block bound

*Law.* `collarLaw W b`: `A_0, A_1 ~ GUE_W(t)`, `G ~ GUE(t)` on `Fin 1 × Fin W`, `t = c/W`,
`c = 1 - 2b`, bonds `B_j ~ Gin(b/W)`, all independent; `0 < b < 1/2`, `W ≥ 1`.
*Domain.* every Hermitian `X` (no norm bound), every real energy `e`, every `z` with `Im z > 0`,
every complex `w` (the deterministic coefficient `z̄_b + e + s` of the row) and every
deterministic `q ∈ ℂ^{2W}`.
*Vector.* `collarRowVec w q ω = ((w - A) q, -B* q)`: for `w = conj(z_b + e + s)` this is
`ρ* q` for the fresh row `ρ = (z_b + e + s - A, -B)` (`Kernel.collarRow`).

## Main results

* `lintegral_gue_halves`: `GUE_W(t) = GUE_W(t/2) ∗ GUE_W(t/2)` in integrated form (from
  `gueMeasure_conv`).
* `lintegral_im_resolvent_selfBlock_le`: for one end block `A_j` and the vector `A_j q_j` carried
  by that same block, `E_{A_j} Im⟨A_j q_j, (ℋ - z)⁻¹ A_j q_j⟩ ≤ 2 W √(π t) ‖q_j‖²` (halves
  `A_j = A' + A''`, rank-one averaging over one half conditional on the other,
  `E‖A' q‖² = W (t/2) ‖q‖²`).
* `lintegral_norm_sq_bond_mulVec`: `E ‖B* q‖² = W (b/W) ‖q‖²` for the common-port bonds.
* `lintegral_im_resolvent_collarRow_le`: **the fresh-row bound**
  `E_collar Im⟨ρ*q, (ℋ_X - z)⁻¹ ρ*q⟩ ≤ 3 (3 K |w|² + 4 W √(π t) + K W (b/W)) ‖q‖²`,
  `K = √(π/(2t))`, i.e. `≤ C_{b,w} √W ‖q‖²` (`collarRowConst`), uniformly in `X`, `e` and `z`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ENNReal NNReal ComplexConjugate

/-!
## Generalities
-/

section General

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `ω ↦ Im⟨v(ω), M(ω)⁻¹ v(ω)⟩` is measurable for measurable `M`, `v`. -/
theorem measurable_ofReal_im_form {Ω : Type*} [MeasurableSpace Ω] {M : Ω → Matrix ι ι ℂ}
    {v : Ω → ι → ℂ} (hM : Measurable M) (hv : Measurable v) :
    Measurable fun ω => ENNReal.ofReal ((star (v ω) ⬝ᵥ ((M ω)⁻¹ *ᵥ v ω)).im) := by
  have hinv := (BlockBand.Wegner.measurable_matrix_inv (n := ι)).comp hM
  have hcont : Continuous fun p : Matrix ι ι ℂ × (ι → ℂ) => (star p.2 ⬝ᵥ (p.1 *ᵥ p.2)).im :=
    Complex.continuous_im.comp ((continuous_star.comp continuous_snd).dotProduct
      (continuous_fst.matrix_mulVec continuous_snd))
  exact (hcont.measurable.comp (hinv.prodMk hv)).ennreal_ofReal

omit [DecidableEq ι] in
theorem im_form_neg (R : Matrix ι ι ℂ) (v : ι → ℂ) :
    star (-v) ⬝ᵥ (R *ᵥ -v) = star v ⬝ᵥ (R *ᵥ v) := by
  simp [mulVec_neg]

variable {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype ι] [DecidableEq n] in
theorem blockVec_add (f : n → ι) (hf : Function.Injective f) (y y' : n → ℂ) :
    blockVec f hf (y + y') = blockVec f hf y + blockVec f hf y' := by
  funext i
  simp only [blockVec, Function.comp_apply, Pi.add_apply]
  rcases blockEquiv f hf i with a | a <;> simp [embedVec]

omit [Fintype ι] [DecidableEq n] in
theorem embedVia_add (f : n → ι) (hf : Function.Injective f) (G G' : Matrix n n ℂ) :
    embedVia f hf (G + G') = embedVia f hf G + embedVia f hf G' := by
  ext i j
  simp only [embedVia, submatrix_apply, Matrix.add_apply]
  rcases blockEquiv f hf i with a | a <;> rcases blockEquiv f hf j with b | b <;>
    simp [embedBlock]

omit [DecidableEq n] in
theorem sum_norm_sq_blockVec (f : n → ι) (hf : Function.Injective f) (y : n → ℂ) :
    ∑ i, ‖blockVec f hf y i‖ ^ 2 = ∑ a, ‖y a‖ ^ 2 := by
  rw [← (blockEquiv f hf).symm.sum_comp, Fintype.sum_sum_type]
  simp [blockVec, embedVec]

end General

/-!
## Halves of one GUE block
-/

section Halves

variable {N : ℕ}

/-- **Halves** (from `gueMeasure_conv`): `∫ g dGUE(t) = ∫∫ g(M' + M'') dGUE(t/2) dGUE(t/2)`. -/
theorem lintegral_gue_halves (t : ℝ≥0) {g : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ M, g M ∂gueMeasure (Fin N) t =
      ∫⁻ M', ∫⁻ M'', g (M' + M'') ∂gueMeasure (Fin N) (t / 2) ∂gueMeasure (Fin N) (t / 2) := by
  have hconv := BlockBand.Palm.MomentFlow.gueMeasure_conv (N := N) (t / 2) (t / 2)
  rw [add_halves] at hconv
  rw [← hconv, lintegral_map hg BlockBand.Palm.MomentFlow.measurable_matrix_add]
  exact lintegral_prod (fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ => g (p.1 + p.2))
    (hg.comp BlockBand.Palm.MomentFlow.measurable_matrix_add).aemeasurable

end Halves

/-!
## Second moment of the common-port bonds
-/

section Bond

/-- `E Σ_q y_q² = |κ| v` for white noise of variance `v`. -/
theorem lintegral_sum_sq_whiteNoise (κ : Type*) [Fintype κ] (v : ℝ≥0) :
    ∫⁻ y, ENNReal.ofReal (∑ q, y q ^ 2) ∂BlockBand.Layers.whiteNoise κ v =
      ENNReal.ofReal (Fintype.card κ * v) := by
  have hone : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂gaussianReal 0 v = ENNReal.ofReal v := by
    have hL2 : MemLp (fun x : ℝ => x) 2 (gaussianReal 0 v) := by
      exact memLp_id_gaussianReal (μ := 0) (v := v) 2
    have hint : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := hL2.integrable_sq
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg x)]
    congr 1
    have hvar := variance_eq_sub hL2
    rw [variance_fun_id_gaussianReal] at hvar
    have hmean : ∫ x, x ∂gaussianReal 0 v = 0 := integral_id_gaussianReal
    simp only [Pi.pow_apply] at hvar
    rw [hmean] at hvar
    linarith
  rw [show (fun y : κ → ℝ => ENNReal.ofReal (∑ q, y q ^ 2)) =
      fun y => ∑ q, ENNReal.ofReal (y q ^ 2) from funext fun y =>
        ENNReal.ofReal_sum_of_nonneg fun q _ => sq_nonneg _]
  rw [lintegral_finsetSum _ fun q _ => ((measurable_pi_apply q).pow_const 2).ennreal_ofReal]
  have heach : ∀ q : κ, ∫⁻ y, ENNReal.ofReal (y q ^ 2) ∂BlockBand.Layers.whiteNoise κ v =
      ENNReal.ofReal v := by
    intro q
    classical
    unfold BlockBand.Layers.whiteNoise
    rw [← hone]
    exact (measurePreserving_eval (fun _ : κ => gaussianReal 0 v) q).lintegral_comp
      (f := fun x : ℝ => ENNReal.ofReal (x ^ 2)) ((measurable_id.pow_const 2).ennreal_ofReal)
  simp_rw [heach]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
  simp

variable {W : ℕ}

/-- **Second moment of the bonds** (`E BB* = W t I` on the common port): for the common-port bond
law `B_j ~ Gin_W(t)` (independent, `j = 0, 1`) and every `v ∈ ℂ^{2W}`,
`E ‖B* v‖² = W t ‖v‖²` (`= b ‖v‖²` for `t = b/W`). -/
theorem lintegral_norm_sq_bond_mulVec (t : ℝ≥0) (v : Fin 2 × Fin W → ℂ) :
    ∫⁻ B, ENNReal.ofReal (∑ x, ‖((bondMatrix .common B)ᴴ *ᵥ v) x‖ ^ 2)
        ∂BlockBand.Layers.bondLaw 2 1 W t =
      ENNReal.ofReal (W * t * ∑ x, ‖v x‖ ^ 2) := by
  set inc := LayerShape.common.incident
  set m : ℝ≥0 := Real.toNNReal (BlockBand.Layers.portMass inc v 0)
  have hm : BlockBand.Layers.portMass inc v 0 = ∑ x, ‖v x‖ ^ 2 := by
    simp [BlockBand.Layers.portMass, inc, LayerShape.incident]
  have hmc : (m : ℝ) = ∑ x, ‖v x‖ ^ 2 := by
    rw [Real.coe_toNNReal _ (by rw [hm]; positivity), hm]
  have hM : ∀ u : Fin W × Fin 2 → ℝ,
      ∑ i, (∑ q, u q * BlockBand.Layers.portMatrix inc v 0 q i) ^ 2 = m * ∑ q, u q ^ 2 := by
    intro u
    rw [Real.coe_toNNReal _ (by rw [hm]; positivity)]
    exact BlockBand.Layers.portMatrix_isometry inc v 0 u
  have hpt : ∀ r : Fin 2 × (Fin 1 × (Fin W × Fin W × Fin 2)) → ℝ,
      ∑ x, ‖((bondMatrix .common (BlockBand.Layers.bondAssemble r))ᴴ *ᵥ v) x‖ ^ 2 =
        ∑ q, (∑ i, BlockBand.Layers.portMatrix inc v 0 q i * r i) ^ 2 := by
    intro r
    rw [Fintype.sum_prod_type, Fin.sum_univ_one, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [BlockBand.Layers.bondMatrix_mulVec_apply, Fin.sum_univ_two,
      ← BlockBand.Layers.portVec_re, ← BlockBand.Layers.portVec_im, Complex.sq_norm,
      Complex.normSq_apply]
    ring
  have hL : Measurable (fun x : Fin 2 × (Fin 1 × (Fin W × Fin W × Fin 2)) → ℝ =>
      fun q => ∑ i, BlockBand.Layers.portMatrix inc v 0 q i * x i) := by fun_prop
  have hg : Measurable fun B : Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ =>
      ENNReal.ofReal (∑ x, ‖((bondMatrix .common B)ᴴ *ᵥ v) x‖ ^ 2) := by
    refine (Finset.measurable_sum _ fun x _ => ?_).ennreal_ofReal
    rcases x with ⟨j, β⟩
    have : (fun B : Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ =>
        ‖((bondMatrix .common B)ᴴ *ᵥ v) (j, β)‖ ^ 2) =
        fun B => ‖BlockBand.Layers.portVec LayerShape.common.incident B v j β‖ ^ 2 :=
      funext fun B => by rw [BlockBand.Layers.bondMatrix_mulVec_apply]
    rw [this]
    exact ((BlockBand.Layers.measurable_portVec _ v j β).norm).pow_const 2
  rw [BlockBand.Layers.bondLaw_eq_map, lintegral_map hg BlockBand.Layers.measurable_bondAssemble]
  simp_rw [hpt]
  rw [← lintegral_map (f := fun y : Fin W × Fin 2 → ℝ => ENNReal.ofReal (∑ q, y q ^ 2))
      (Finset.measurable_sum _ fun q _ => (measurable_pi_apply q).pow_const 2).ennreal_ofReal hL,
    BlockBand.Layers.whiteNoise_map_linear (t / 2) m _ hM, lintegral_sum_sq_whiteNoise]
  congr 1
  simp only [Fintype.card_prod, Fintype.card_fin, NNReal.coe_mul, NNReal.coe_div, hmc]
  push_cast
  ring

end Bond

/-!
## The self-block term `A_j q_j`
-/

section SelfBlock

variable {W : ℕ}

theorem measurable_setA (j : Fin 2) (ω : CollarSample W) :
    Measurable fun M : Matrix (Fin W) (Fin W) ℂ => setA j M ω := by
  unfold setA
  exact (((measurable_update ω.1.1 (a := j))).prodMk measurable_const).prodMk measurable_const

theorem collarMatrix_setA_add (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (j : Fin 2) (M M' : Matrix (Fin W) (Fin W) ℂ) (ω : CollarSample W) :
    collarMatrix e X (setA j (M + M') ω) =
      collarMatrix e X (setA j M ω) + embedVia (siteA j) (siteA_injective j) M' := by
  rw [collarMatrix_eq_add_embed_A e X (setA j (M + M') ω) j,
    collarMatrix_eq_add_embed_A e X (setA j M ω) j, zeroA_setA, zeroA_setA, setA_apply,
    setA_apply, embedVia_add, add_assoc]

theorem collarMatrix_setA_isHermitian (e : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) (j : Fin 2) {M : Matrix (Fin W) (Fin W) ℂ} (hM : M.IsHermitian)
    {ω : CollarSample W} (hA : ∀ k, k ≠ j → (ω.1.1 k).IsHermitian) (hG : ω.2.IsHermitian) :
    (collarMatrix e X (setA j M ω)).IsHermitian := by
  have hA' : ∀ k, ((setA j M ω).1.1 k).IsHermitian := by
    intro k
    by_cases hk : k = j
    · subst hk; simpa [setA] using hM
    · simpa [setA, Function.update_of_ne hk] using hA k hk
  have hD : (BlockBand.Internal.Contracts.Layers.blockDiag (setA j M ω).1.1).IsHermitian :=
    BlockBand.Critical.Collar.Kernel.blockDiag_isHermitian' hA'
  have hc : ((e : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)).IsHermitian := by
    simp [IsHermitian, conjTranspose_smul]
  have hc' : ((e : ℂ) • (1 : Matrix (PortSite W .common) (PortSite W .common) ℂ)).IsHermitian := by
    simp [IsHermitian, conjTranspose_smul]
  exact IsHermitian.fromBlocks ((hD.sub hc).sub hX) rfl ((show (setA j M ω).2 = ω.2 from rfl) ▸
    hG |>.sub hc')

/-- **Self-block term.** Law: `A_j ~ GUE_W(t)`, `t > 0`, the other collar variables fixed (other end
block and middle block Hermitian), every Hermitian `X`, real `e`, `Im z > 0`, `q_j ∈ ℂ^W`:
`E_{A_j} Im⟨A_j q_j, (ℋ_X - z)⁻¹ A_j q_j⟩ ≤ 2 (K' W (t/2) ‖q_j‖² + K' W (t/2) ‖q_j‖²)`,
`K' = √(π/(2 (t/2)))` (`= 2 W √(π t) ‖q_j‖²`), the vector carried by block `j`. Proof: halves
`A_j = A' + A''`; `Im⟨u + u', R(u+u')⟩ ≤ 2(Im⟨u,Ru⟩ + Im⟨u',Ru'⟩)`; average `A' q_j` over `A''`
and `A'' q_j` over `A'` (rank-one), then `E‖A' q_j‖² = W(t/2)‖q_j‖²`. -/
theorem lintegral_im_resolvent_selfBlock_le (e : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) {t : ℝ≥0} (ht : 0 < t) {z : ℂ} (hz : 0 < z.im) (j : Fin 2)
    (qj : Fin W → ℂ) {ω : CollarSample W} (hA : ∀ k, k ≠ j → (ω.1.1 k).IsHermitian)
    (hG : ω.2.IsHermitian) :
    ∫⁻ M, ENNReal.ofReal ((star (blockVec (siteA j) (siteA_injective j) (M *ᵥ qj)) ⬝ᵥ
        ((collarMatrix e X (setA j M ω) -
          z • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ))⁻¹ *ᵥ
          blockVec (siteA j) (siteA_injective j) (M *ᵥ qj))).im) ∂gueMeasure (Fin W) t ≤
      ENNReal.ofReal (2 * (Real.sqrt (Real.pi / (2 * ((t / 2 : ℝ≥0) : ℝ))) *
          (W * ((t / 2 : ℝ≥0) : ℝ) * ∑ a, ‖qj a‖ ^ 2) +
        Real.sqrt (Real.pi / (2 * ((t / 2 : ℝ≥0) : ℝ))) *
          (W * ((t / 2 : ℝ≥0) : ℝ) * ∑ a, ‖qj a‖ ^ 2))) := by
  set τ : ℝ≥0 := t / 2
  have hτ : 0 < τ := by simp [τ, ht]
  set K := Real.sqrt (Real.pi / (2 * (τ : ℝ)))
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  set S := ∑ a, ‖qj a‖ ^ 2
  set μ := gueMeasure (Fin W) τ
  set bv : Matrix (Fin W) (Fin W) ℂ → LayerSite W .common → ℂ := fun M =>
    blockVec (siteA j) (siteA_injective j) (M *ᵥ qj)
  set Rs : Matrix (Fin W) (Fin W) ℂ → Matrix (LayerSite W .common) (LayerSite W .common) ℂ :=
    fun M => collarMatrix e X (setA j M ω) -
      z • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ)
  have hRs : Measurable Rs := by
    have h1 := (measurable_collarMatrix e X).comp (measurable_setA j ω)
    exact Measurable.of_eval_matrix _ fun a c =>
      ((Matrix.measurable_apply).comp h1).sub measurable_const
  have hbv : Measurable bv := by
    have hlin : Continuous fun M : Matrix (Fin W) (Fin W) ℂ =>
        blockVec (siteA j) (siteA_injective j) (M *ᵥ qj) := by
      refine continuous_pi fun i => ?_
      simp only [blockVec, Function.comp_apply]
      rcases blockEquiv (siteA j) (siteA_injective j) i with a | a
      · exact (continuous_apply a).comp (continuous_id.matrix_mulVec continuous_const)
      · exact continuous_const
    exact hlin.measurable
  -- the integrand and its two pieces
  set F : Matrix (Fin W) (Fin W) ℂ → ℝ≥0∞ := fun M =>
    ENNReal.ofReal ((star (bv M) ⬝ᵥ ((Rs M)⁻¹ *ᵥ bv M)).im)
  have hF : Measurable F := measurable_ofReal_im_form hRs hbv
  set F₁ : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((star (bv p.1) ⬝ᵥ ((Rs (p.1 + p.2))⁻¹ *ᵥ bv p.1)).im)
  set F₂ : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((star (bv p.2) ⬝ᵥ ((Rs (p.1 + p.2))⁻¹ *ᵥ bv p.2)).im)
  have hadd := BlockBand.Palm.MomentFlow.measurable_matrix_add (N := W)
  have hF₁ : Measurable F₁ := measurable_ofReal_im_form (hRs.comp hadd) (hbv.comp measurable_fst)
  have hF₂ : Measurable F₂ := measurable_ofReal_im_form (hRs.comp hadd) (hbv.comp measurable_snd)
  have hHerm := ae_isHermitian_gueMeasure (ι := Fin W) τ
  -- pointwise split
  have hsplit : ∀ M' M'' : Matrix (Fin W) (Fin W) ℂ, M'.IsHermitian → M''.IsHermitian →
      F (M' + M'') ≤ 2 * (F₁ (M', M'') + F₂ (M', M'')) := by
    intro M' M'' h1 h2
    have hH := collarMatrix_setA_isHermitian e hX j (h1.add h2) hA hG
    have h := im_quad_sum_le hH hz Finset.univ ![bv M', bv M'']
    simp only [Fin.sum_univ_two, Finset.card_univ, Fintype.card_fin, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h
    have hb : bv M' + bv M'' = bv (M' + M'') := by
      simp only [bv, add_mulVec, blockVec_add]
    rw [hb] at h
    have n1 := im_dotProduct_inv_mulVec_nonneg' hH hz (bv M')
    have n2 := im_dotProduct_inv_mulVec_nonneg' hH hz (bv M'')
    simp only [F, F₁, F₂, Rs]
    rw [← ENNReal.ofReal_add n1 n2, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by push_cast at h; linarith)
  -- rank-one bounds
  have hb1 : ∀ M' : Matrix (Fin W) (Fin W) ℂ, M'.IsHermitian →
      ∫⁻ M'', F₁ (M', M'') ∂μ ≤ ENNReal.ofReal (K * ∑ a, ‖(M' *ᵥ qj) a‖ ^ 2) := by
    intro M' h1
    have hH0 := collarMatrix_setA_isHermitian e hX j h1 hA hG
    refine le_of_eq_of_le (lintegral_congr fun M'' => ?_)
      (lintegral_im_resolvent_embedVia_le (siteA j) (siteA_injective j) hH0 hτ hz (M' *ᵥ qj))
    simp only [F₁, Rs, bv]
    rw [collarMatrix_setA_add]
  have hb2 : ∀ M'' : Matrix (Fin W) (Fin W) ℂ, M''.IsHermitian →
      ∫⁻ M', F₂ (M', M'') ∂μ ≤ ENNReal.ofReal (K * ∑ a, ‖(M'' *ᵥ qj) a‖ ^ 2) := by
    intro M'' h2
    have hH0 := collarMatrix_setA_isHermitian e hX j h2 hA hG
    refine le_of_eq_of_le (lintegral_congr fun M' => ?_)
      (lintegral_im_resolvent_embedVia_le (siteA j) (siteA_injective j) hH0 hτ hz (M'' *ᵥ qj))
    simp only [F₂, Rs, bv]
    rw [add_comm M' M'', collarMatrix_setA_add]
  have hmom : ∫⁻ M, ENNReal.ofReal (K * ∑ a, ‖(M *ᵥ qj) a‖ ^ 2) ∂μ =
      ENNReal.ofReal (K * (W * (τ : ℝ) * S)) := by
    simp_rw [ENNReal.ofReal_mul hK]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      BlockBand.Critical.WeightedDensity.lintegral_norm_sq_mulVec_gue]
  have hmeasR : Measurable fun M : Matrix (Fin W) (Fin W) ℂ =>
      ENNReal.ofReal (K * ∑ a, ‖(M *ᵥ qj) a‖ ^ 2) := by
    refine (Measurable.const_mul ?_ K).ennreal_ofReal
    exact Finset.measurable_sum _ fun a _ =>
      (((continuous_apply a).comp (continuous_id.matrix_mulVec continuous_const)).norm.pow
        2).measurable
  have hF₁' : Measurable fun M' => ∫⁻ M'', F₁ (M', M'') ∂μ := hF₁.lintegral_prod_right'
  have hF₂' : Measurable fun M' => ∫⁻ M'', F₂ (M', M'') ∂μ := hF₂.lintegral_prod_right'
  rw [lintegral_gue_halves t hF]
  calc ∫⁻ M', ∫⁻ M'', F (M' + M'') ∂μ ∂μ
      ≤ ∫⁻ M', ∫⁻ M'', 2 * (F₁ (M', M'') + F₂ (M', M'')) ∂μ ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hHerm] with M' h1
        refine lintegral_mono_ae ?_
        filter_upwards [hHerm] with M'' h2
        exact hsplit M' M'' h1 h2
    _ = 2 * (∫⁻ M', ∫⁻ M'', F₁ (M', M'') ∂μ ∂μ + ∫⁻ M', ∫⁻ M'', F₂ (M', M'') ∂μ ∂μ) := by
        have hin : ∀ M', ∫⁻ M'', 2 * (F₁ (M', M'') + F₂ (M', M'')) ∂μ =
            2 * (∫⁻ M'', F₁ (M', M'') ∂μ + ∫⁻ M'', F₂ (M', M'') ∂μ) := by
          intro M'
          rw [lintegral_const_mul' _ _ (by simp),
            lintegral_add_left (f := fun M'' => F₁ (M', M'')) (hF₁.comp measurable_prodMk_left)]
        simp_rw [hin]
        rw [lintegral_const_mul' _ _ (by simp),
          lintegral_add_left (f := fun M' => ∫⁻ M'', F₁ (M', M'') ∂μ) hF₁']
    _ ≤ 2 * (ENNReal.ofReal (K * (W * (τ : ℝ) * S)) + ENNReal.ofReal (K * (W * (τ : ℝ) * S))) := by
        gcongr
        · rw [← hmom]
          refine lintegral_mono_ae ?_
          filter_upwards [hHerm] with M' h1
          exact hb1 M' h1
        · rw [lintegral_lintegral_swap hF₂.aemeasurable, ← hmom]
          refine lintegral_mono_ae ?_
          filter_upwards [hHerm] with M'' h2
          exact hb2 M'' h2
    _ = _ := by
        have h0 : 0 ≤ K * (W * (τ : ℝ) * S) :=
          mul_nonneg hK (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity))
        rw [← ENNReal.ofReal_add h0 h0, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
          ← ENNReal.ofReal_mul (by norm_num)]

end SelfBlock

end BlockBand.Critical.Collar.Density

namespace BlockBand.Critical.Collar.Density

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ENNReal NNReal ComplexConjugate

/-!
## The fresh-row bound
-/

section Row

variable {W : ℕ}

/-- The fresh-row vector `((w - A) q, -B* q)` on `LayerSite W .common` (`= ρ* q` for
`w = conj(z_b + e + s)`, `ρ = (z_b + e + s - A, -B)`). -/
def collarRowVec (w : ℂ) (q : Fin 2 × Fin W → ℂ) (ω : CollarSample W) :
    LayerSite W .common → ℂ :=
  Sum.elim (w • q - blockDiag ω.1.1 *ᵥ q) (-((bondMatrix .common ω.1.2)ᴴ *ᵥ q))

theorem measurable_collarRowVec (w : ℂ) (q : Fin 2 × Fin W → ℂ) :
    Measurable (collarRowVec (W := W) w q) := by
  have hA : ∀ (k : Fin 2) (a c : Fin W),
      Measurable fun ω : CollarSample W => ω.1.1 k a c := fun k a c =>
    (Matrix.measurable_apply).comp ((measurable_pi_apply k).comp (measurable_fst.comp measurable_fst))
  have hB : ∀ (k : Fin 2) (l : Fin 1) (a c : Fin W),
      Measurable fun ω : CollarSample W => ω.1.2 k l a c := fun k l a c =>
    (Matrix.measurable_apply).comp ((measurable_pi_apply l).comp ((measurable_pi_apply k).comp
      (measurable_snd.comp measurable_fst)))
  refine measurable_pi_iff.2 fun i => ?_
  rcases i with x | p
  · simp only [collarRowVec, Sum.elim_inl, Pi.sub_apply, Pi.smul_apply, mulVec, dotProduct]
    refine measurable_const.sub (Finset.measurable_sum _ fun y _ => ?_)
    refine Measurable.mul ?_ measurable_const
    simp only [BlockBand.Internal.Contracts.Layers.blockDiag]
    split_ifs
    · exact hA _ _ _
    · exact measurable_const
  · simp only [collarRowVec, Sum.elim_inr, Pi.neg_apply, mulVec, dotProduct, conjTranspose_apply]
    refine (Finset.measurable_sum _ fun y _ => ?_).neg
    refine Measurable.mul ?_ measurable_const
    simp only [BlockBand.Internal.Contracts.Layers.bondMatrix]
    split_ifs
    · exact Complex.continuous_conj.measurable.comp (hB _ _ _ _)
    · exact measurable_const

/-- `ℋ_X` is Hermitian `collarLaw`-a.s. (Hermitian `X`). -/
theorem ae_collarMatrix_isHermitian (b e : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) : ∀ᵐ ω ∂collarLaw W b, (collarMatrix e X ω).IsHermitian ∧
      (∀ k, (ω.1.1 k).IsHermitian) ∧ ω.2.IsHermitian := by
  set t := Real.toNNReal ((1 - 2 * b) / W)
  have hA : ∀ᵐ L ∂layerLaw W b .common, ∀ k, (L.1 k).IsHermitian := by
    have h1 : ∀ᵐ A ∂(Measure.pi fun _ : Fin 2 => gueMeasure (Fin W) t),
        ∀ k, (A k).IsHermitian := by
      rw [ae_all_iff]
      intro k
      exact (Measure.quasiMeasurePreserving_eval _ k).ae
        (ae_isHermitian_gueMeasure (ι := Fin W) _)
    exact (Measure.quasiMeasurePreserving_fst).ae h1
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := layerLaw W b .common)
    (ν := gueMeasure (PortSite W .common) t)).ae hA
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := layerLaw W b .common)
    (ν := gueMeasure (PortSite W .common) t)).ae (ae_isHermitian_gueMeasure (ι := PortSite W .common) t)
  filter_upwards [h1, h2] with ω h1 h2
  refine ⟨?_, h1, h2⟩
  have hD : (BlockBand.Internal.Contracts.Layers.blockDiag ω.1.1).IsHermitian :=
    BlockBand.Critical.Collar.Kernel.blockDiag_isHermitian' h1
  have hc : ((e : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)).IsHermitian := by
    simp [IsHermitian, conjTranspose_smul]
  have hc' : ((e : ℂ) • (1 : Matrix (PortSite W .common) (PortSite W .common) ℂ)).IsHermitian := by
    simp [IsHermitian, conjTranspose_smul]
  exact IsHermitian.fromBlocks ((hD.sub hc).sub hX) rfl (h2.sub hc')

/-- The block decomposition of the fresh-row vector: deterministic part, the two end-block parts
`A_j q_j` (with a sign) and the bond part. -/
theorem collarRowVec_eq (w : ℂ) (q : Fin 2 × Fin W → ℂ) (ω : CollarSample W) :
    collarRowVec w q ω = Sum.elim (w • q) 0 +
      (-(blockVec (siteA 0) (siteA_injective 0) (ω.1.1 0 *ᵥ fun a => q (0, a)) +
          blockVec (siteA 1) (siteA_injective 1) (ω.1.1 1 *ᵥ fun a => q (1, a)))) +
      blockVec siteG siteG_injective (-((bondMatrix .common ω.1.2)ᴴ *ᵥ q)) := by
  have hv := vec_eq_sum_blocks (Sum.elim (-(blockDiag ω.1.1 *ᵥ q)) 0 : LayerSite W .common → ℂ)
  have hv' := vec_eq_sum_blocks
    (Sum.elim 0 (-((bondMatrix .common ω.1.2)ᴴ *ᵥ q)) : LayerSite W .common → ℂ)
  have hz0 : ∀ j : Fin 2, (fun a => (Sum.elim 0 (-((bondMatrix .common ω.1.2)ᴴ *ᵥ q)) :
      LayerSite W .common → ℂ) (siteA j a)) = 0 := fun j => by funext a; simp [siteA]
  have hzG : (fun p => (Sum.elim (-(blockDiag ω.1.1 *ᵥ q)) 0 : LayerSite W .common → ℂ)
      (siteG p)) = 0 := by funext p; simp [siteG]
  have hblk : ∀ j : Fin 2, (fun a => (Sum.elim (-(blockDiag ω.1.1 *ᵥ q)) 0 :
      LayerSite W .common → ℂ) (siteA j a)) = -(ω.1.1 j *ᵥ fun a => q (j, a)) := by
    intro j
    funext a
    simp only [siteA, Sum.elim_inl, Pi.neg_apply, mulVec, dotProduct,
      BlockBand.Internal.Contracts.Layers.blockDiag, Fintype.sum_prod_type]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  have hbz : ∀ (f : Fin W → LayerSite W .common) (hf : Function.Injective f),
      blockVec f hf (0 : Fin W → ℂ) = 0 := fun f hf => by
    funext i; simp only [blockVec, Function.comp_apply]
    rcases blockEquiv f hf i with a | a <;> simp [embedVec]
  have hbzG : blockVec siteG siteG_injective (0 : PortSite W .common → ℂ) = 0 := by
    funext i; simp only [blockVec, Function.comp_apply]
    rcases blockEquiv siteG siteG_injective i with a | a <;> simp [embedVec]
  have hneg : ∀ (j : Fin 2) (y : Fin W → ℂ),
      blockVec (siteA j) (siteA_injective j) (-y) = -blockVec (siteA j) (siteA_injective j) y := by
    intro j y
    funext i; simp only [blockVec, Function.comp_apply, Pi.neg_apply]
    rcases blockEquiv (siteA j) (siteA_injective j) i with a | a <;> simp [embedVec]
  rw [hz0, hz0, hbz, hbz, zero_add, zero_add] at hv'
  rw [hblk, hblk, hzG, hbzG, add_zero, hneg, hneg] at hv
  have hG : (fun p => (Sum.elim 0 (-((bondMatrix .common ω.1.2)ᴴ *ᵥ q)) :
      LayerSite W .common → ℂ) (siteG p)) = -((bondMatrix .common ω.1.2)ᴴ *ᵥ q) := by
    funext p; simp [siteG]
  rw [hG] at hv'
  rw [← hv', neg_add, ← hv]
  funext i
  rcases i with x | p <;> simp [collarRowVec, sub_eq_add_neg]

/-- **Fresh-row three-block bound** (the global collar density bound in resolvent form). Law `collarLaw W b`, `0 < b < 1/2`, `W ≥ 1`, `t = c/W`. For every Hermitian `X`
(no norm bound), real `e`, `Im z > 0`, complex `w` and deterministic `q`:
`E_collar Im⟨v, (ℋ_X - z)⁻¹ v⟩ ≤ 3 (3 K |w|² + 8 K' W (t/2) + K W (b/W)) ‖q‖²`, `v = ((w - A)q, -B*q)`,
`K = √(π/(2t))`, `K' = √(π/(2 (t/2)))` (all `O(√W)`). The row is split into its deterministic,
end-block and bond parts (`im_quad_sum_le`, `k = 3`); the deterministic part is averaged over the
end blocks, each `A_j q_j` over halves of `A_j`, and `B* q` over the middle block `G`
(conditional on the bonds), followed by `E‖B*q‖² = W(b/W)‖q‖²`. -/
theorem lintegral_im_resolvent_collarRow_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 0 < W)
    (e : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (w : ℂ) (q : Fin 2 × Fin W → ℂ) :
    ∫⁻ ω, ENNReal.ofReal ((star (collarRowVec w q ω) ⬝ᵥ ((collarMatrix e X ω -
        z • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ))⁻¹ *ᵥ
          collarRowVec w q ω)).im) ∂collarLaw W b ≤
      ENNReal.ofReal (3 * (3 * Real.sqrt (Real.pi / (2 * Real.toNNReal ((1 - 2 * b) / W))) *
          ‖w‖ ^ 2 +
        8 * Real.sqrt (Real.pi / (2 * ((Real.toNNReal ((1 - 2 * b) / W) / 2 : ℝ≥0) : ℝ))) *
          (W * ((Real.toNNReal ((1 - 2 * b) / W) / 2 : ℝ≥0) : ℝ)) +
        Real.sqrt (Real.pi / (2 * Real.toNNReal ((1 - 2 * b) / W))) *
          (W * Real.toNNReal (b / W))) * ∑ x, ‖q x‖ ^ 2) := by
  set t := Real.toNNReal ((1 - 2 * b) / W)
  have ht : 0 < t := Real.toNNReal_pos.2 (div_pos (by linarith) (by exact_mod_cast hW))
  set K := Real.sqrt (Real.pi / (2 * t))
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  set K' := Real.sqrt (Real.pi / (2 * ((t / 2 : ℝ≥0) : ℝ)))
  have hK' : 0 ≤ K' := Real.sqrt_nonneg _
  set τ : ℝ := ((t / 2 : ℝ≥0) : ℝ)
  have hτ : 0 ≤ τ := NNReal.coe_nonneg _
  set S := ∑ x, ‖q x‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  set qj : Fin 2 → Fin W → ℂ := fun j a => q (j, a)
  set Sj : Fin 2 → ℝ := fun j => ∑ a, ‖qj j a‖ ^ 2
  have hSj : S = Sj 0 + Sj 1 := by
    simp only [S, Sj, qj, Fintype.sum_prod_type, Fin.sum_univ_two]
  set R : CollarSample W → Matrix (LayerSite W .common) (LayerSite W .common) ℂ := fun ω =>
    collarMatrix e X ω - z • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ)
  have hR : Measurable R := Measurable.of_eval_matrix _ fun i j =>
    ((Matrix.measurable_apply).comp (measurable_collarMatrix e X)).sub measurable_const
  set I : (CollarSample W → LayerSite W .common → ℂ) → CollarSample W → ℝ≥0∞ := fun u ω =>
    ENNReal.ofReal ((star (u ω) ⬝ᵥ ((R ω)⁻¹ *ᵥ u ω)).im)
  have hI : ∀ u, Measurable u → Measurable (I u) := fun u hu => measurable_ofReal_im_form hR hu
  -- the pieces
  set vdet : CollarSample W → LayerSite W .common → ℂ := fun _ => Sum.elim (w • q) 0
  set bvA : Fin 2 → CollarSample W → LayerSite W .common → ℂ := fun j ω =>
    blockVec (siteA j) (siteA_injective j) (ω.1.1 j *ᵥ qj j)
  set vB : CollarSample W → LayerSite W .common → ℂ := fun ω =>
    blockVec siteG siteG_injective (-((bondMatrix .common ω.1.2)ᴴ *ᵥ q))
  have hmA : ∀ j, Measurable (bvA j) := by
    intro j
    have hlin : Continuous fun M : Matrix (Fin W) (Fin W) ℂ =>
        blockVec (siteA j) (siteA_injective j) (M *ᵥ qj j) := by
      refine continuous_pi fun i => ?_
      simp only [blockVec, Function.comp_apply]
      rcases blockEquiv (siteA j) (siteA_injective j) i with a | a
      · exact (continuous_apply a).comp (continuous_id.matrix_mulVec continuous_const)
      · exact continuous_const
    exact hlin.measurable.comp ((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst))
  have hmB : Measurable vB := by
    have h := measurable_collarRowVec (W := W) 0 q
    have hcomp : vB = fun ω => blockVec siteG siteG_injective (fun p => collarRowVec 0 q ω (siteG p)) := by
      funext ω; simp only [vB, collarRowVec, siteG, Sum.elim_inr]
    rw [hcomp]
    have hlin : Continuous fun u : LayerSite W .common → ℂ =>
        blockVec siteG siteG_injective (fun p => u (siteG p)) := by
      refine continuous_pi fun i => ?_
      simp only [blockVec, Function.comp_apply]
      rcases blockEquiv siteG siteG_injective i with a | a
      · exact continuous_apply _
      · exact continuous_const
    exact hlin.measurable.comp h
  have hae := ae_collarMatrix_isHermitian b e hX (W := W)
  -- pointwise split
  have hsplit : ∀ᵐ ω ∂collarLaw W b, I (collarRowVec w q) ω ≤
      3 * (I vdet ω + 2 * (I (bvA 0) ω + I (bvA 1) ω) + I vB ω) := by
    filter_upwards [hae] with ω hω
    have hH := hω.1
    have h3 := im_quad_sum_le hH hz Finset.univ ![vdet ω, -(bvA 0 ω + bvA 1 ω), vB ω]
    simp only [Fin.sum_univ_three, Finset.card_univ, Fintype.card_fin, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h3
    rw [← collarRowVec_eq w q ω, im_form_neg] at h3
    have h2 := im_quad_sum_le hH hz Finset.univ ![bvA 0 ω, bvA 1 ω]
    simp only [Fin.sum_univ_two, Finset.card_univ, Fintype.card_fin, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h2
    have n0 := im_dotProduct_inv_mulVec_nonneg' hH hz (vdet ω)
    have n1 := im_dotProduct_inv_mulVec_nonneg' hH hz (bvA 0 ω)
    have n2 := im_dotProduct_inv_mulVec_nonneg' hH hz (bvA 1 ω)
    have n3 := im_dotProduct_inv_mulVec_nonneg' hH hz (vB ω)
    simp only [I, R]
    rw [← ENNReal.ofReal_add n1 n2, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add n0 (by positivity),
      ← ENNReal.ofReal_add (by positivity) n3, show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp,
      ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast at h2 h3
    nlinarith
  -- deterministic part
  have hdet : ∫⁻ ω, I vdet ω ∂collarLaw W b ≤ ENNReal.ofReal (3 * (K * (‖w‖ ^ 2 * S))) := by
    have h := lintegral_im_resolvent_collar_le hb hW e hX hz (Sum.elim (w • q) 0 :
      LayerSite W .common → ℂ)
    have hn : ∑ i, ‖(Sum.elim (w • q) 0 : LayerSite W .common → ℂ) i‖ ^ 2 = ‖w‖ ^ 2 * S := by
      rw [Fintype.sum_sum_type]
      simp [S, Finset.mul_sum, mul_pow]
    rw [hn] at h
    exact h
  -- end blocks
  have hblk : ∀ j : Fin 2, ∫⁻ ω, I (bvA j) ω ∂collarLaw W b ≤
      ENNReal.ofReal (2 * (K' * (W * τ * Sj j) + K' * (W * τ * Sj j))) := by
    intro j
    refine collar_lintegral_le_of_A b j (hI _ (hmA j)) fun ω hA hG => ?_
    have := lintegral_im_resolvent_selfBlock_le e hX ht hz j (qj j) hA hG
    refine le_of_eq_of_le (lintegral_congr fun M => ?_) this
    simp only [I, R, bvA, setA_apply]
  -- bond part
  have hbond : ∫⁻ ω, I vB ω ∂collarLaw W b ≤ ENNReal.ofReal (K * (W * Real.toNNReal (b / W) * S)) := by
    have hlaw : collarLaw W b = (layerLaw W b .common).prod (gueMeasure (PortSite W .common) t) := rfl
    have hIB := hI vB hmB
    rw [hlaw, lintegral_prod _ hIB.aemeasurable]
    have hAe : ∀ᵐ L ∂layerLaw W b .common, ∀ k, (L.1 k).IsHermitian := by
      have h1 : ∀ᵐ A ∂(Measure.pi fun _ : Fin 2 => gueMeasure (Fin W) t),
          ∀ k, (A k).IsHermitian := by
        rw [ae_all_iff]
        intro k
        exact (Measure.quasiMeasurePreserving_eval _ k).ae
          (ae_isHermitian_gueMeasure (ι := Fin W) _)
      exact (Measure.quasiMeasurePreserving_fst).ae h1
    have hinner : ∀ᵐ L ∂layerLaw W b .common,
        ∫⁻ G, I vB (L, G) ∂gueMeasure (PortSite W .common) t ≤
          ENNReal.ofReal (K * ∑ p, ‖(-((bondMatrix .common L.2)ᴴ *ᵥ q)) p‖ ^ 2) := by
      filter_upwards [hAe] with L hL
      have hH0 : (collarMatrix e X (zeroG (L, 0))).IsHermitian := by
        have hD : (BlockBand.Internal.Contracts.Layers.blockDiag L.1).IsHermitian :=
          BlockBand.Critical.Collar.Kernel.blockDiag_isHermitian' hL
        have hc : ((e : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)).IsHermitian := by
          simp [IsHermitian, conjTranspose_smul]
        have hc' : ((e : ℂ) • (1 : Matrix (PortSite W .common) (PortSite W .common) ℂ)).IsHermitian := by
          simp [IsHermitian, conjTranspose_smul]
        exact IsHermitian.fromBlocks ((hD.sub hc).sub hX) rfl
          ((show (zeroG (L, (0 : Matrix (PortSite W .common) (PortSite W .common) ℂ))).2 = 0 from rfl) ▸
            (by simp [IsHermitian] : (0 : Matrix (PortSite W .common) (PortSite W .common) ℂ).IsHermitian)
              |>.sub hc')
      have := lintegral_im_resolvent_embedVia_le siteG siteG_injective hH0 ht hz
        (-((bondMatrix .common L.2)ᴴ *ᵥ q))
      refine le_of_eq_of_le (lintegral_congr fun M => ?_) this
      simp only [I, R, vB]
      rw [collarMatrix_eq_add_embed_G e X (L, M)]
      rfl
    have hmeasB : Measurable fun L : LayerSample W .common =>
        ENNReal.ofReal (∑ p, ‖((bondMatrix .common L.2)ᴴ *ᵥ q) p‖ ^ 2) := by
      have h := measurable_collarRowVec (W := W) 0 q
      have hc : Continuous fun u : LayerSite W .common → ℂ => ∑ p : PortSite W .common,
          ‖u (Sum.inr p)‖ ^ 2 :=
        continuous_finsetSum _ fun p _ => ((continuous_apply _).norm).pow 2
      have : (fun L : LayerSample W .common =>
          ENNReal.ofReal (∑ p, ‖((bondMatrix .common L.2)ᴴ *ᵥ q) p‖ ^ 2)) =
          fun L => ENNReal.ofReal (∑ p : PortSite W .common,
            ‖collarRowVec 0 q (L, (0 : Matrix (PortSite W .common) (PortSite W .common) ℂ))
              (Sum.inr p)‖ ^ 2) := by
        funext L; simp [collarRowVec]
      rw [this]
      exact (hc.measurable.comp (h.comp (measurable_id.prodMk measurable_const))).ennreal_ofReal
    calc ∫⁻ L, ∫⁻ G, I vB (L, G) ∂gueMeasure (PortSite W .common) t ∂layerLaw W b .common
        ≤ ∫⁻ L, ENNReal.ofReal (K * ∑ p, ‖(-((bondMatrix .common L.2)ᴴ *ᵥ q)) p‖ ^ 2)
            ∂layerLaw W b .common := lintegral_mono_ae hinner
      _ = ENNReal.ofReal K * ∫⁻ L, ENNReal.ofReal (∑ p, ‖((bondMatrix .common L.2)ᴴ *ᵥ q) p‖ ^ 2)
            ∂layerLaw W b .common := by
          simp_rw [Pi.neg_apply, norm_neg, ENNReal.ofReal_mul hK]
          exact lintegral_const_mul _ hmeasB
      _ = ENNReal.ofReal K * ENNReal.ofReal (W * Real.toNNReal (b / W) * S) := by
          congr 1
          have hl : layerLaw W b .common = (Measure.pi fun _ : Fin 2 =>
              gueMeasure (Fin W) t).prod (BlockBand.Layers.bondLaw 2 1 W (Real.toNNReal (b / W))) :=
            rfl
          have : IsProbabilityMeasure (BlockBand.Layers.bondLaw 2 1 W (Real.toNNReal (b / W))) := by
            unfold BlockBand.Layers.bondLaw; infer_instance
          rw [hl, lintegral_prod _ hmeasB.aemeasurable]
          simp only [lintegral_const, measure_univ, mul_one]
          rw [lintegral_norm_sq_bond_mulVec]
      _ = _ := by rw [← ENNReal.ofReal_mul hK]
  -- assemble
  have hm0 := hI vdet measurable_const
  have hm1 := hI _ (hmA 0)
  have hm2 := hI _ (hmA 1)
  have hm3 := hI vB hmB
  calc ∫⁻ ω, I (collarRowVec w q) ω ∂collarLaw W b
      ≤ ∫⁻ ω, 3 * (I vdet ω + 2 * (I (bvA 0) ω + I (bvA 1) ω) + I vB ω) ∂collarLaw W b :=
        lintegral_mono_ae hsplit
    _ = 3 * (∫⁻ ω, I vdet ω ∂collarLaw W b + 2 * (∫⁻ ω, I (bvA 0) ω ∂collarLaw W b +
          ∫⁻ ω, I (bvA 1) ω ∂collarLaw W b) + ∫⁻ ω, I vB ω ∂collarLaw W b) := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_add_right _ hm3,
          lintegral_add_left hm0, lintegral_const_mul' _ _ (by simp), lintegral_add_left hm1]
    _ ≤ 3 * (ENNReal.ofReal (3 * (K * (‖w‖ ^ 2 * S))) +
          2 * (ENNReal.ofReal (2 * (K' * (W * τ * Sj 0) + K' * (W * τ * Sj 0))) +
            ENNReal.ofReal (2 * (K' * (W * τ * Sj 1) + K' * (W * τ * Sj 1)))) +
          ENNReal.ofReal (K * (W * Real.toNNReal (b / W) * S))) := by
        exact mul_le_mul_right (add_le_add (add_le_add hdet
          (mul_le_mul_right (add_le_add (hblk 0) (hblk 1)) 2)) hbond) 3
    _ = _ := by
        have hS0 : 0 ≤ Sj 0 := Finset.sum_nonneg fun _ _ => by positivity
        have hS1 : 0 ≤ Sj 1 := Finset.sum_nonneg fun _ _ => by positivity
        have hWn : (0 : ℝ) ≤ W := by positivity
        have hb' : (0 : ℝ) ≤ Real.toNNReal (b / W) := NNReal.coe_nonneg _
        have a0 : 0 ≤ 3 * (K * (‖w‖ ^ 2 * S)) := by positivity
        have a1 : 0 ≤ 2 * (K' * (W * τ * Sj 0) + K' * (W * τ * Sj 0)) := by positivity
        have a2 : 0 ≤ 2 * (K' * (W * τ * Sj 1) + K' * (W * τ * Sj 1)) := by positivity
        have a3 : 0 ≤ K * (W * Real.toNNReal (b / W) * S) := by positivity
        rw [← ENNReal.ofReal_add a1 a2, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add a0 (by positivity),
          ← ENNReal.ofReal_add (by positivity) a3, show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        rw [hSj]
        ring

/-- The `W`-free constant of the fresh-row bound:
`C_{b,w} = 3 (3 |w|² √(π/(2c)) + 4 √(π c) + b √(π/(2c)))`, `c = 1 - 2b`. -/
def collarRowConst (b : ℝ) (w : ℂ) : ℝ :=
  3 * (3 * ‖w‖ ^ 2 * Real.sqrt (Real.pi / (2 * (1 - 2 * b))) +
    4 * Real.sqrt (Real.pi * (1 - 2 * b)) + b * Real.sqrt (Real.pi / (2 * (1 - 2 * b))))

theorem collarRowConst_nonneg {b : ℝ} (hb0 : 0 ≤ b) (w : ℂ) : 0 ≤ collarRowConst b w := by
  unfold collarRowConst; positivity

theorem collarRowConst_mono (b : ℝ) {w w' : ℂ} (h : ‖w‖ ≤ ‖w'‖) :
    collarRowConst b w ≤ collarRowConst b w' := by
  unfold collarRowConst
  have : ‖w‖ ^ 2 ≤ ‖w'‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  gcongr

/-- **Fresh-row bound, `√W` form**: `E_collar Im⟨ρ*q, (ℋ_X - z)⁻¹ ρ*q⟩ ≤ C_{b,w} √W ‖q‖²`
(`collarRowConst`), uniformly in `W ≥ 1`, Hermitian `X`, real `e` and `Im z > 0`. -/
theorem lintegral_im_resolvent_collarRow_le_sqrt {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hW : 0 < W) (e : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (w : ℂ) (q : Fin 2 × Fin W → ℂ) :
    ∫⁻ ω, ENNReal.ofReal ((star (collarRowVec w q ω) ⬝ᵥ ((collarMatrix e X ω -
        z • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ))⁻¹ *ᵥ
          collarRowVec w q ω)).im) ∂collarLaw W b ≤
      ENNReal.ofReal (collarRowConst b w * Real.sqrt W * ∑ x, ‖q x‖ ^ 2) := by
  refine (lintegral_im_resolvent_collarRow_le hb0 hb hW e hX hz w q).trans
    (le_of_eq (congrArg ENNReal.ofReal ?_))
  set c := 1 - 2 * b with hc_def
  have hc : 0 < c := by linarith
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have ht : ((Real.toNNReal (c / W) : ℝ≥0) : ℝ) = c / W := Real.coe_toNNReal _ (by positivity)
  have ht2 : ((Real.toNNReal (c / W) / 2 : ℝ≥0) : ℝ) = c / W / 2 := by
    rw [NNReal.coe_div, ht]; rfl
  have hbW : ((Real.toNNReal (b / W) : ℝ≥0) : ℝ) = b / W := Real.coe_toNNReal _ (by positivity)
  rw [ht, ht2, hbW]
  have h1 : Real.pi / (2 * (c / W)) = W * (Real.pi / (2 * c)) := by field_simp
  have h2 : Real.pi / (2 * (c / W / 2)) = W * (Real.pi / c) := by field_simp
  have h3 : Real.sqrt (Real.pi * c) = c * Real.sqrt (Real.pi / c) := by
    rw [show Real.pi * c = c ^ 2 * (Real.pi / c) by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hc.le]
  rw [h1, h2, Real.sqrt_mul hWr.le, Real.sqrt_mul hWr.le, collarRowConst, ← hc_def, h3]
  field_simp
  ring

end Row

end BlockBand.Critical.Collar.Density
