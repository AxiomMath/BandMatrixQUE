module

public import Mathlib
public import BlockBand.Wegner.ProjectedWegnerOneBlock
public import BlockBand.Wegner.ProjectedWegnerSchur
public import BlockBand.Wegner.ProjectedWegnerIndep

/-!
# The projected Wegner estimate

Proves `Internal.Contracts.Inputs.ProjectedWegner`: for block models with independent
`GUE_W(c/W)` blocks, `E[-Im Tr P_B G] ≤ π (C/√c) W |B|` for the resolvent
`G = (H - e + iY + iη)⁻¹` and every union `B` of blocks.

Proof. For a block `j`, the Schur complement onto block `j` (`trace_blockProjector_inv_embed`)
gives `Tr P_j G = Tr (A_j + S)⁻¹` with `S = schurBlock X₀ j` a measurable function of
`(D, Y, A_{-j})` and with imaginary margin `η` (`hasImMargin_schurBlock`). Independence of
`A_j` and `(D, Y, A_{-j})` (Tonelli on the product law) and the one-block bound
`lintegral_oneBlock_le` (Poisson representation at `ζ = i`, real-background PSSS density,
`∫ η/(x²+η²) = π`) give `E[-Im Tr P_j G] ≤ π (C/√c) W`. Summing over `j ∈ B` gives clause 1
(`isFreshBlock_of_isIndependent` reduces it to clause 2); integrability holds since
`0 ≤ -Im Tr P_B G ≤ η⁻¹ Σ_{xy} |(P_B)_{xy}|`. Clauses 3–4 follow by Fatou for `η ↓ 0`.

The only input is `PSSS.SourceContract` (through `gueCoordinate_count_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

open MeasureTheory ProbabilityTheory Set Complex Matrix Filter Topology
open BlockBand.External BlockBand.Internal.Contracts.Inputs
open scoped ENNReal ComplexOrder

/-!
## Deterministic sign and size of `-Im Tr P_B G`
-/

section Deterministic

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Diagonal entries of the inverse of a matrix with positive imaginary margin have
nonpositive imaginary part. -/
theorem HasImMargin.im_inv_apply_self_nonpos {η : ℝ} (hη : 0 < η) {N : Matrix n n ℂ}
    (h : HasImMargin η N) (b : n) : (N⁻¹ b b).im ≤ 0 := by
  set u : n → ℂ := N⁻¹ *ᵥ Pi.single b 1 with hu
  have hNu : N *ᵥ u = Pi.single b 1 := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (h.isUnit_det hη), Matrix.one_mulVec]
  have hub : u b = N⁻¹ b b := by
    rw [hu]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hq : star u ⬝ᵥ (N *ᵥ u) = star (u b) := by
    rw [hNu, dotProduct_single, mul_one]
    rfl
  have h1 := h u
  rw [hq] at h1
  have h2 : 0 ≤ (star u ⬝ᵥ u).re := by
    rw [re_star_dotProduct_self]
    positivity
  have h3 : (star (u b)).im = -(u b).im := by simp
  rw [← hub]
  nlinarith [mul_nonneg hη.le h2]

variable {k W : ℕ}

theorem neg_im_trace_blockProjector_mul_inv_nonneg {η : ℝ} (hη : 0 < η)
    {N : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ} (h : HasImMargin η N) (B : Finset (Fin k)) :
    0 ≤ -((blockProjector B * N⁻¹).trace).im := by
  simp only [blockProjector, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Complex.im_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_nonneg fun x _ => ?_
  by_cases hx : x.1 ∈ B
  · simp [hx, h.im_inv_apply_self_nonpos hη x]
  · simp [hx]

theorem abs_im_trace_mul_inv_le {η : ℝ} (hη : 0 < η) {N : Matrix n n ℂ} (h : HasImMargin η N)
    (Q : Matrix n n ℂ) : |(-((Q * N⁻¹).trace).im)| ≤ (∑ a, ∑ b, ‖Q a b‖) * η⁻¹ := by
  rw [abs_neg]
  exact (abs_im_le_norm _).trans (h.norm_trace_mul_inv_le hη Q)

end Deterministic

/-!
## The model
-/

section Model

variable {k W : ℕ}

/-- The absorbed matrix `H - e + iY + iη` (so `absorbedResolvent = (absorbedMatrix)⁻¹`). -/
def absorbedMatrix (M : BlockModel k W) (e η : ℝ) (w : M.Ω) :
    Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ :=
  M.H w - (e : ℂ) • (1 : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) + Complex.I • M.Y w +
    ((η : ℂ) * Complex.I) • (1 : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ)

theorem projectedDensity_eq (M : BlockModel k W) (B : Finset (Fin k)) (e η : ℝ) (w : M.Ω) :
    M.projectedDensity B e η w = -((blockProjector B * (absorbedMatrix M e η w)⁻¹).trace).im :=
  rfl

theorem measurable_absorbedMatrix (M : BlockModel k W) (e η : ℝ) :
    Measurable (absorbedMatrix M e η) := by
  have hA : ∀ i a b, Measurable (fun w => M.A w i a b) := fun i a b =>
    (measurable_pi_apply b).comp ((measurable_pi_apply a).comp
      ((measurable_pi_apply i).comp M.measurable_A))
  have hD : ∀ x y, Measurable (fun w => M.D w x y) := fun x y =>
    (measurable_pi_apply y).comp ((measurable_pi_apply x).comp M.measurable_D)
  have hY : ∀ x y, Measurable (fun w => M.Y w x y) := fun x y =>
    (measurable_pi_apply y).comp ((measurable_pi_apply x).comp M.measurable_Y)
  rw [Matrix.measurable_iff]
  intro x y
  have hS : Measurable (fun w => M.blockSum w x y) := by
    unfold BlockModel.blockSum
    by_cases hxy : x.1 = y.1
    · simp only [hxy, ↓reduceIte]
      exact hA _ _ _
    · simp only [hxy, ↓reduceIte]
      exact measurable_const
  exact ((((hD x y).add hS).sub measurable_const).add (measurable_const.mul (hY x y))).add
    measurable_const

theorem measurable_projectedDensity (M : BlockModel k W) (B : Finset (Fin k)) (e η : ℝ) :
    Measurable (M.projectedDensity B e η) := by
  have hc : Continuous (fun N : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ =>
      -((blockProjector B * N).trace).im) :=
    (Complex.continuous_im.comp (continuous_const.matrix_mul continuous_id).matrix_trace).neg
  exact hc.measurable.comp (measurable_matrix_inv.comp (measurable_absorbedMatrix M e η))

theorem projectedDensity_nonneg (M : BlockModel k W) (B : Finset (Fin k)) (e : ℝ) {η : ℝ}
    (hη : 0 < η) (w : M.Ω) : 0 ≤ M.projectedDensity B e η w :=
  neg_im_trace_blockProjector_mul_inv_nonneg hη (hasImMargin_absorbed M e η w) B

theorem integrable_projectedDensity (M : BlockModel k W) (B : Finset (Fin k)) (e : ℝ) {η : ℝ}
    (hη : 0 < η) : Integrable (M.projectedDensity B e η) M.P := by
  refine Integrable.of_bound (measurable_projectedDensity M B e η).aestronglyMeasurable
    ((∑ a, ∑ b, ‖blockProjector (W := W) B a b‖) * η⁻¹) (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs]
  exact abs_im_trace_mul_inv_le hη (hasImMargin_absorbed M e η w) _

/-- Conditioning data `(D, Y, A_{-j})`. -/
abbrev FreshData (k W : ℕ) : Type :=
  Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ × Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ ×
    (Fin k → Matrix (Fin W) (Fin W) ℂ)

/-- The background `X₀ = D + ⊕_{i ≠ j} A_i - e + iY + iη` as a function of the conditioning
data `r = (D, Y, A_{-j})` (block `j` of `A_{-j}` is `0`). -/
def freshBackground (e η : ℝ) (r : FreshData k W) :
    Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ :=
  r.1 + familyBlockSum r.2.2 - (e : ℂ) • (1 : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) +
    Complex.I • r.2.1 + ((η : ℂ) * Complex.I) • (1 : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ)

theorem measurable_freshBackground (e η : ℝ) :
    Measurable (freshBackground (k := k) (W := W) e η) := by
  rw [Matrix.measurable_iff]
  intro x y
  have h1 : Measurable (fun r : FreshData k W => r.1 x y) := (measurable_pi_apply y).comp ((measurable_pi_apply x).comp measurable_fst)
  have h2 : Measurable (fun r : FreshData k W => r.2.1 x y) :=
    (measurable_pi_apply y).comp ((measurable_pi_apply x).comp (measurable_fst.comp measurable_snd))
  have h3 : Measurable (fun r : FreshData k W => familyBlockSum r.2.2 x y) := by
    unfold familyBlockSum
    by_cases hxy : x.1 = y.1
    · simp only [hxy, ↓reduceIte]
      exact (measurable_pi_apply y.2).comp ((measurable_pi_apply x.2).comp
        ((measurable_pi_apply y.1).comp (measurable_snd.comp measurable_snd)))
    · simp only [hxy, ↓reduceIte]
      exact measurable_const
  exact ((((h1.add h3).sub measurable_const).add (measurable_const.mul h2))).add measurable_const

/-- The one-block observable `ψ(a, r) = -Im Tr (a + S(r))⁻¹`, `S = schurBlock X₀ j`. -/
def freshObservable (j : Fin k) (e η : ℝ) (p : Matrix (Fin W) (Fin W) ℂ × FreshData k W) : ℝ :=
  -((p.1 + schurBlock (freshBackground e η p.2) j)⁻¹.trace).im

theorem measurable_freshObservable (j : Fin k) (e η : ℝ) :
    Measurable (freshObservable (W := W) j e η) := by
  have hS : Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × FreshData k W =>
      schurBlock (freshBackground e η p.2) j) :=
    (measurable_schurBlock (W := W) j).comp
      ((measurable_freshBackground (k := k) (W := W) e η).comp measurable_snd)
  have hsum : Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × FreshData k W =>
      p.1 + schurBlock (freshBackground e η p.2) j) := by
    rw [Matrix.measurable_iff]
    intro a b
    exact ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp measurable_fst)).add
      ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp hS))
  have hc : Continuous (fun N : Matrix (Fin W) (Fin W) ℂ => -(N.trace).im) :=
    (Complex.continuous_im.comp (continuous_id.matrix_trace)).neg
  exact hc.measurable.comp (measurable_matrix_inv.comp hsum)

/-- Schur form of the single-block density: `-Im Tr P_j G = ψ(A_j, (D, Y, A_{-j}))`. -/
theorem projectedDensity_singleton_eq (M : BlockModel k W) (j : Fin k) (e : ℝ) {η : ℝ}
    (hη : 0 < η) (w : M.Ω) :
    M.projectedDensity {j} e η w = freshObservable j e η
      (M.A w j, (M.D w, M.Y w, fun i => if i = j then 0 else M.A w i)) := by
  have hAm : ∀ i, (if i = j then (0 : Matrix (Fin W) (Fin W) ℂ) else M.A w i).IsHermitian := by
    intro i
    by_cases hij : i = j
    · simp only [hij, ↓reduceIte]
      exact Matrix.isHermitian_zero
    · simp only [hij, ↓reduceIte]
      exact M.hermitian_A w i
  have hmargin : HasImMargin η (freshBackground e η
      (M.D w, M.Y w, fun i => if i = j then 0 else M.A w i)) :=
    hasImMargin_background (M.hermitian_D w) hAm (M.posSemidef_Y w) e
  have hsplit : absorbedMatrix M e η w = freshBackground e η
      (M.D w, M.Y w, fun i => if i = j then 0 else M.A w i) +
        blockEmbed (W := W) j * M.A w j * (blockEmbed (W := W) j)ᴴ := by
    simp only [absorbedMatrix, freshBackground, BlockModel.H, blockSum_eq_familyBlockSum]
    rw [familyBlockSum_split (M.A w) j]
    abel
  rw [projectedDensity_eq, hsplit,
    trace_blockProjector_inv_embed hη hmargin j (M.A w j) (M.hermitian_A w j)]
  rfl

/-- Clause 2 in lintegral form. Under `GUECountBound C` (`C ≥ 0`), for a fresh block `j`,
`∫⁻ ofReal(-Im Tr P_j G) ≤ ofReal(C/√c · W · π)` for every `e` and `η > 0`. -/
theorem lintegral_projectedDensity_singleton_le {C : ℝ} (hC : GUECountBound C) (hC0 : 0 ≤ C)
    (hW : 0 < W) {c : ℝ} (hc : 0 < c) (M : BlockModel k W) (j : Fin k)
    (hj : M.IsFreshBlock c j) (e : ℝ) {η : ℝ} (hη : 0 < η) :
    ∫⁻ w, ENNReal.ofReal (M.projectedDensity {j} e η w) ∂M.P ≤
      ENNReal.ofReal (C / Real.sqrt c * (W : ℝ) * Real.pi) := by
  obtain ⟨hlaw, hind⟩ := hj
  set R : M.Ω → FreshData k W :=
    fun w => (M.D w, M.Y w, fun i => if i = j then 0 else M.A w i) with hRdef
  have hAj : Measurable (fun w => M.A w j) := (measurable_pi_apply j).comp M.measurable_A
  have hR : Measurable R := by
    refine M.measurable_D.prodMk (M.measurable_Y.prodMk ?_)
    refine measurable_pi_iff.mpr fun i => ?_
    by_cases hij : i = j
    · simp only [hij, ↓reduceIte]
      exact measurable_const
    · simp only [hij, ↓reduceIte]
      exact (measurable_pi_apply i).comp M.measurable_A
  set F : Matrix (Fin W) (Fin W) ℂ × FreshData k W → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (freshObservable j e η p) with hFdef
  have hF : Measurable F := ENNReal.measurable_ofReal.comp (measurable_freshObservable j e η)
  have hpt : ∀ w, ENNReal.ofReal (M.projectedDensity {j} e η w) = F (M.A w j, R w) := by
    intro w
    rw [projectedDensity_singleton_eq M j e hη w]
  simp_rw [hpt]
  have hprod : M.P.map (fun w => (M.A w j, R w)) = (M.P.map (fun w => M.A w j)).prod (M.P.map R) :=
    (indepFun_iff_map_prod_eq_prod_map_map hAj.aemeasurable hR.aemeasurable).mp hind
  have hmapA : M.P.map (fun w => M.A w j) = gueMatrixLaw W (Real.toNNReal (c / W)) := hlaw.map_eq
  have : IsProbabilityMeasure (Johansson.coordinateMeasure W (Real.toNNReal (c / W))) :=
    Johansson.coordinateMeasure_probability W _
  have hgue : IsProbabilityMeasure (gueMatrixLaw W (Real.toNNReal (c / W))) := by
    unfold gueMatrixLaw
    exact (Measure.isProbabilityMeasure_map_iff (measurable_gaussianMatrix_val W).aemeasurable).mpr
      inferInstance
  have : IsProbabilityMeasure (M.P.map R) := 
    (Measure.isProbabilityMeasure_map_iff hR.aemeasurable).mpr inferInstance
  rw [← lintegral_map hF (hAj.prodMk hR), hprod, hmapA, lintegral_prod_symm' F hF,
    lintegral_map (hF.lintegral_prod_left') hR]
  -- inner bound for every realized conditioning datum
  have hinner : ∀ w, ∫⁻ a, F (a, R w) ∂gueMatrixLaw W (Real.toNNReal (c / W)) ≤
      ENNReal.ofReal (C / Real.sqrt c * (W : ℝ) * Real.pi) := by
    intro w
    have hAm : ∀ i, (if i = j then (0 : Matrix (Fin W) (Fin W) ℂ) else M.A w i).IsHermitian := by
      intro i
      by_cases hij : i = j
      · simp only [hij, ↓reduceIte]
        exact Matrix.isHermitian_zero
      · simp only [hij, ↓reduceIte]
        exact M.hermitian_A w i
    have hmargin : HasImMargin η (schurBlock (freshBackground e η (R w)) j) :=
      hasImMargin_schurBlock hη
        (hasImMargin_background (M.hermitian_D w) hAm (M.posSemidef_Y w) e) j
    have hFa : Measurable (fun a : Matrix (Fin W) (Fin W) ℂ => F (a, R w)) :=
      hF.comp (measurable_id.prodMk measurable_const)
    have key := lintegral_oneBlock_le hC hC0 hW hc hη hmargin
    unfold gueMatrixLaw
    rw [lintegral_map hFa (measurable_gaussianMatrix_val W)]
    simp only [hFdef, freshObservable]
    exact key
  calc ∫⁻ w, ∫⁻ a, F (a, R w) ∂gueMatrixLaw W (Real.toNNReal (c / W)) ∂M.P
      ≤ ∫⁻ _w, ENNReal.ofReal (C / Real.sqrt c * (W : ℝ) * Real.pi) ∂M.P :=
        lintegral_mono hinner
    _ = ENNReal.ofReal (C / Real.sqrt c * (W : ℝ) * Real.pi) := by
        rw [lintegral_const, measure_univ, mul_one]

/-- `-Im Tr P_B G = Σ_{j ∈ B} (-Im Tr P_j G)`. -/
theorem projectedDensity_eq_sum (M : BlockModel k W) (B : Finset (Fin k)) (e η : ℝ) (w : M.Ω) :
    M.projectedDensity B e η w = ∑ j ∈ B, M.projectedDensity {j} e η w := by
  simp only [projectedDensity_eq]
  rw [trace_blockProjector_mul_eq_sum, Complex.im_sum, ← Finset.sum_neg_distrib]

/-- Clause 1 in lintegral form: `∫⁻ ofReal(-Im Tr P_B G) ≤ ofReal(π (C/√c) W |B|)`. -/
theorem lintegral_projectedDensity_le {C : ℝ} (hC : GUECountBound C) (hC0 : 0 ≤ C)
    (hW : 0 < W) {c : ℝ} (hc : 0 < c) (M : BlockModel k W) (hM : M.IsIndependent c)
    (B : Finset (Fin k)) (e : ℝ) {η : ℝ} (hη : 0 < η) :
    ∫⁻ w, ENNReal.ofReal (M.projectedDensity B e η w) ∂M.P ≤
      ENNReal.ofReal (Real.pi * (C / Real.sqrt c) * (W : ℝ) * (B.card : ℝ)) := by
  have hpt : ∀ w, ENNReal.ofReal (M.projectedDensity B e η w) =
      ∑ j ∈ B, ENNReal.ofReal (M.projectedDensity {j} e η w) := by
    intro w
    rw [projectedDensity_eq_sum, ENNReal.ofReal_sum_of_nonneg fun j _ =>
      projectedDensity_nonneg M {j} e hη w]
  simp_rw [hpt]
  rw [lintegral_finsetSum _ fun j _ => (measurable_projectedDensity M {j} e η).ennreal_ofReal]
  calc ∑ j ∈ B, ∫⁻ w, ENNReal.ofReal (M.projectedDensity {j} e η w) ∂M.P
      ≤ ∑ _j ∈ B, ENNReal.ofReal (C / Real.sqrt c * (W : ℝ) * Real.pi) :=
        Finset.sum_le_sum fun j _ => lintegral_projectedDensity_singleton_le hC hC0 hW hc M j
          (isFreshBlock_of_isIndependent M c hM j) e hη
    _ = ENNReal.ofReal (Real.pi * (C / Real.sqrt c) * (W : ℝ) * (B.card : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        ring

/-- Fatou for `η ↓ 0` from a bound uniform in `η > 0`. -/
theorem lintegral_liminf_projectedDensity_le (M : BlockModel k W) (B : Finset (Fin k)) (e : ℝ)
    {b : ℝ≥0∞} (h : ∀ η : ℝ, 0 < η → ∫⁻ w, ENNReal.ofReal (M.projectedDensity B e η w) ∂M.P ≤ b) :
    (∫⁻ w, Filter.liminf (fun η => ENNReal.ofReal (M.projectedDensity B e η w))
        (𝓝[>] (0 : ℝ)) ∂M.P) ≤ b := by
  refine (lintegral_liminf_le' fun η =>
    (ENNReal.measurable_ofReal.comp (measurable_projectedDensity M B e η)).aemeasurable).trans ?_
  refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact h η hη

/-- Real-valued conclusion from the lintegral bound and nonnegativity. -/
theorem integral_projectedDensity_le_of_lintegral (M : BlockModel k W) (B : Finset (Fin k))
    (e : ℝ) {η : ℝ} (hη : 0 < η) {b : ℝ} (hb : 0 ≤ b)
    (h : ∫⁻ w, ENNReal.ofReal (M.projectedDensity B e η w) ∂M.P ≤ ENNReal.ofReal b) :
    (∫ w, M.projectedDensity B e η w ∂M.P) ≤ b := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun w => projectedDensity_nonneg M B e hη w)
    (measurable_projectedDensity M B e η).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hb h

end Model

/-- The projected Wegner estimate `Internal.Contracts.Inputs.ProjectedWegner`.

One absolute constant `C > 0` (the PSSS constant `source.C`, `K_c = C/√c`) is chosen first.
For every `k`, `W ≥ 1`, `c > 0` and every block model `M` (law `M.P`; random Hermitian `D`,
random `Y ⪰ 0`, no norm bound): (1) if the blocks are independent `GUE_W(c/W)` and `(D, Y)` is
independent of them, then for every real `e`, `η > 0` and union `B` of blocks,
`-Im Tr P_B G` (with `G = (H - e + iY + iη)⁻¹`) is integrable and
`E[-Im Tr P_B G] ≤ π K_c W |B|`; (2) the same for a single fresh block `j` (`IsFreshBlock`)
with bound `π K_c W`; (3), (4) the boundary-value (Fatou) versions
`E liminf_{η↓0} (-Im Tr P_B G_η) ≤ π K_c W |B|` (resp. `π K_c W`), as lintegrals.

Inputs: only `PSSS.SourceContract` (via `gueCoordinate_count_le`). -/
theorem projectedWegner_holds (source : PSSS.SourceContract.{0}) :
    Internal.Contracts.Inputs.ProjectedWegner := by
  obtain ⟨C, hCpos, hC⟩ := gueCoordinate_count_le source
  have hC' : GUECountBound C := hC
  refine ⟨C, hCpos, ?_⟩
  intro k W hW c hc M
  have hb : ∀ n : ℕ, 0 ≤ Real.pi * (C / Real.sqrt c) * (W : ℝ) * (n : ℝ) := fun n => by
    have := Real.pi_pos
    positivity
  have hsingle : ∀ j : Fin k, M.IsFreshBlock c j → ∀ (e η : ℝ), 0 < η →
      ∫⁻ w, ENNReal.ofReal (M.projectedDensity {j} e η w) ∂M.P ≤
        ENNReal.ofReal (Real.pi * (C / Real.sqrt c) * (W : ℝ)) := by
    intro j hj e η hη
    refine (lintegral_projectedDensity_singleton_le hC' hCpos.le hW hc M j hj e hη).trans
      (le_of_eq ?_)
    congr 1
    ring
  refine ⟨fun hM e η hη B => ⟨integrable_projectedDensity M B e hη,
      integral_projectedDensity_le_of_lintegral M B e hη (hb _)
        (lintegral_projectedDensity_le hC' hCpos.le hW hc M hM B e hη)⟩,
    fun j hj e η hη => ⟨integrable_projectedDensity M {j} e hη,
      integral_projectedDensity_le_of_lintegral M {j} e hη (by simpa using hb 1)
        (hsingle j hj e η hη)⟩,
    fun hM e B => lintegral_liminf_projectedDensity_le M B e fun η hη =>
      lintegral_projectedDensity_le hC' hCpos.le hW hc M hM B e hη,
    fun j hj e => lintegral_liminf_projectedDensity_le M {j} e fun η hη =>
      hsingle j hj e η hη⟩

end BlockBand.Wegner
