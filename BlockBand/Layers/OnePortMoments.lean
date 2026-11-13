module

public import BlockBand.Layers.OnePortMomentsPoisson
public import BlockBand.Layers.WeightedLayerNoise
public import BlockBand.Layers.CompensatedPhaseLogDet
public import BlockBand.Internal.Contracts.LayersOnePort
public import BlockBand.Model.Construction.GaussianPolynomialNull

/-!
# Passive one-port layer: inverse moments and operator moments of `L = K𝒢₁₂`

`OnePortOperatorMomentsContract`, with its foundation, the inverse moments of the fresh one-port
layer for passive input `X` (`-Im X ⪰ 0`): the passive-bounds lemma, through its Poisson
extension and the identity `K𝒢₁₁ = I + …`.

## Setting

The fresh one-block one-port layer `layerLaw W b .oneBlockOnePort` (`A ~ GUE_W((1-2b)/W)`,
`B ~ Gin(b/W)` independent), `z = z_∂(E) = boundaryZ b E`, `E ∈ bulkInterval κ`, a deterministic
`W × W` input `X` placed on the physical sites by `onePortLift`, `𝒢 = onePortResolvent b E X`
(Lean's totalized inverse of `[[A - E - X, B], [B*, z]]`), `K = z - X`, `L = onePortL b E X = K𝒢₁₂`.
Norms: `ℓ²` operator norm on matrices; `L^p` norms (`eLpNorm`) under `layerLaw`.

## Main results

* `opm_passive_inverse_moments` (the foundation, used by the `OnePortMean` constructor): for `b ∈ (0,1/2)`, `κ > 0`, `p ≥ 1` there are `C > 0`, `W₀` such that for
  `W ≥ W₀`, every passive `X` and `E ∈ bulkInterval κ` the layer matrix is a.s. invertible,
  `‖‖𝒢‖‖_{L^p} ≤ C` and `‖‖𝒢₁₁‖‖_{L^p} ≤ C`.
* `onePortOperatorMoments_holds`: `OnePortOperatorMomentsContract`.

## Proof

* **Hermitian/dissipative split.** `X = X_h - iY` with `X_h = (X + X*)/2` Hermitian and
  `Y = onePortDissipation X ⪰ 0`; for complex `ζ` the layer matrix at input `X_h - ζY` is the affine
  pencil `T₀ + ζ P`, `T₀` the layer matrix at `X_h`, `P = diag(Y, 0)` (`opm_layerMatrix_pencil`); the
  passive layer is `ζ = i`, real `ζ` are Hermitian inputs.
* **Bounded pencil (a.s.).** For a GUE sample (Hermitian `A`) and an invertible bond `B` (Ginibre
  bonds are a.s. invertible, `opm_ae_det_ginibre_ne_zero`), the Schur complement
  `A - E - X_h + ζY - z⁻¹BB*` has `Im ⪰ η|z|⁻²σ_min(B)² > 0` for `Im ζ ≥ 0`
  (`opm_schur_coercive`), so `T₀ + ζP` is invertible with `‖(T₀ + ζP)⁻¹‖ ≤ K(ω)` on the closed upper
  half-plane (`opm_pencil_bound`, via `fromBlocks_inv`).
* **Poisson step.** `opm_poisson_lintegral` (`OnePortMomentsPoisson`):
  `‖𝒢(X)‖ ≤ 2 ∫ ‖(T₀ + t(θ)P)⁻¹‖ dθ/2π` with real `t(θ)`; Jensen, then Tonelli over
  `layerLaw ⊗ dθ/2π` (`opm_lintegral_pencil_le`) — no supremum inside the expectation — and
  `gaussianAbsorption_holds` (Hermitian inputs, uniform in `X`) give `E‖𝒢(X)‖^p ≤ 2^p C_A^p`.
* **The operator `L = (K𝒢)₁₂`.** We have `K𝒢 = J + (𝒦 - J𝒢⁻¹)𝒢` with
  `‖𝒦 - J𝒢⁻¹‖ ≤ |z| + |E| + ‖Λ‖` for every `X` (only the word `K𝒢` is used; `wl_Kh_mul_eq`, `wl_norm_Kh_sub_left_le`), so
  `‖L‖ ≤ 1 + 6(1 + ‖Λ‖)‖𝒢‖` (`opm_norm_onePortL_le`), `Λ = [[A, B], [B*, 0]]`; Hölder with the
  Gaussian moments `wl_lam_eLpNorm_le_layer` (GUE block and Ginibre bond together) and the `2p`-th
  inverse moment above.

The only hypothesis is `ConditionalBlockGUECount` (through `gaussianAbsorption_holds`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Filter Topology Real
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.LayersOnePort
open BlockBand.Internal.Contracts.Inputs (ConditionalBlockGUECount)
open scoped ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. Ginibre bonds are a.s. invertible
-/

/-- **Ginibre blocks are a.s. invertible** (`t > 0`): `det B` is a nonzero polynomial in the real
Gaussian coordinates (it is `1` at the identity), whose zero set is Lebesgue-null. (Same proof as
`BlockBand.Center.csm_ae_det_ginibre_ne_zero`, restated here to keep `Layers` independent of
`Center`.) -/
theorem opm_ae_det_ginibre_ne_zero (W : ℕ) {t : ℝ≥0} (ht : t ≠ 0) :
    ∀ᵐ B ∂ginibreMeasure (Fin W) (Fin W) t, B.det ≠ 0 := by
  let P : Matrix (Fin W) (Fin W) (MvPolynomial (Fin W × Fin W × Fin 2) ℂ) :=
    fun x y => MvPolynomial.X (x, y, 0) + MvPolynomial.X (x, y, 1) * MvPolynomial.C Complex.I
  have hev : ∀ r : Fin W × Fin W × Fin 2 → ℝ,
      MvPolynomial.eval (fun j => (r j : ℂ)) P.det =
        (BlockBand.Layers.ginibreAssemble (ι := Fin W) (κ := Fin W) r).det := by
    intro r
    rw [RingHom.map_det]
    congr 1
    ext x y
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    simp [P, BlockBand.Layers.ginibreAssemble]
  set Q := BlockBand.Parameters.mvPolynomialNormSq P.det
  have hQx : ∀ r, MvPolynomial.eval r Q =
      Complex.normSq (BlockBand.Layers.ginibreAssemble (ι := Fin W) (κ := Fin W) r).det := by
    intro r
    rw [BlockBand.Parameters.eval_mvPolynomialNormSq, hev]
  have hQ : Q ≠ 0 := by
    intro h0
    let r₀ : Fin W × Fin W × Fin 2 → ℝ := fun j => if j.1 = j.2.1 ∧ j.2.2 = 0 then 1 else 0
    have hr₀ : BlockBand.Layers.ginibreAssemble (ι := Fin W) (κ := Fin W) r₀ = 1 := by
      ext x y
      by_cases h : x = y
      · subst h; simp [BlockBand.Layers.ginibreAssemble, r₀]
      · simp [BlockBand.Layers.ginibreAssemble, r₀, h, Matrix.one_apply_ne h]
    have h := hQx r₀
    rw [h0, map_zero, hr₀, Matrix.det_one, Complex.normSq_one] at h
    exact zero_ne_one h
  have hnull := BlockBand.Parameters.volume_mvPolynomial_zeroSet_fintype Q hQ
  have ht2 : t / 2 ≠ 0 := by
    intro h; apply ht
    have := congrArg (fun u : ℝ≥0 => u * 2) h
    simpa using this
  have hac := BlockBand.Parameters.pi_absolutelyContinuous_volume
    (fun _ : Fin W × Fin W × Fin 2 => gaussianReal 0 (t / 2))
    (fun _ => gaussianReal_absolutelyContinuous 0 ht2)
  have hmeasS : MeasurableSet {B : Matrix (Fin W) (Fin W) ℂ | B.det = 0} :=
    measurableSet_eq_fun (continuous_id.matrix_det).measurable measurable_const
  rw [ae_iff]
  simp only [ne_eq, not_not]
  rw [BlockBand.Layers.ginibreMeasure_eq_map, Measure.map_apply
    BlockBand.Layers.measurable_ginibreAssemble hmeasS]
  apply hac
  convert hnull using 2
  ext r
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hQx, Complex.normSq_eq_zero]

/-!
## 2. The one-port vocabulary: lift, Hermitian part, pencil, bond
-/

section Vocabulary

variable {W : ℕ}

/-- The reindexing `Fin 1 × Fin W ≃ Fin W` of the one-port sites. -/
abbrev opmE (W : ℕ) : Fin 1 × Fin W ≃ Fin W := Equiv.uniqueProd (Fin W) (Fin 1)

theorem opm_lift_eq (X : Matrix (Fin W) (Fin W) ℂ) :
    onePortLift X = X.submatrix (opmE W) (opmE W) := by
  ext u v; rfl

theorem opm_lift_sub (A B : Matrix (Fin W) (Fin W) ℂ) :
    onePortLift (A - B) = onePortLift A - onePortLift B := by
  ext u v; simp [onePortLift]

theorem opm_lift_smul (c : ℂ) (A : Matrix (Fin W) (Fin W) ℂ) :
    onePortLift (c • A) = c • onePortLift A := by
  ext u v; simp [onePortLift]

theorem opm_lift_isHermitian {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian) :
    (onePortLift X).IsHermitian := by
  rw [opm_lift_eq]; exact hX.submatrix _

theorem opm_lift_posSemidef {Y : Matrix (Fin W) (Fin W) ℂ} (hY : Y.PosSemidef) :
    (onePortLift Y).PosSemidef := by
  rw [opm_lift_eq]; exact hY.submatrix _

/-- The Hermitian part `X_h = (X + X*)/2`. -/
def opmHerm (X : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ := (1 / 2 : ℂ) • (X + Xᴴ)

theorem opmHerm_isHermitian (X : Matrix (Fin W) (Fin W) ℂ) : (opmHerm X).IsHermitian := by
  unfold IsHermitian opmHerm
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  congr 1
  simp

/-- `X = X_h - i Y`, `Y = -Im X = onePortDissipation X`. -/
theorem opm_decomp (X : Matrix (Fin W) (Fin W) ℂ) :
    X = opmHerm X - Complex.I • onePortDissipation X := by
  ext i j
  simp only [opmHerm, onePortDissipation, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Real shifts of a Hermitian matrix along a Hermitian direction stay Hermitian. -/
theorem opm_isHermitian_sub_real_smul {X Y : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) (r : ℝ) : (X - (r : ℂ) • Y).IsHermitian := by
  refine hX.sub ?_
  unfold IsHermitian
  rw [conjTranspose_smul, hY.eq, Complex.star_def, Complex.conj_ofReal]

/-- **The pencil**: `layerMatrix` at input `X₀ - ζ Y₀` is `layerMatrix` at `X₀` plus
`ζ · diag(Y₀, 0)`. -/
theorem opm_layerMatrix_pencil {σ : LayerShape} (E : ℝ) (z ζ : ℂ)
    (X₀ Y₀ : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (ω : LayerSample W σ) :
    layerMatrix σ E z (X₀ - ζ • Y₀) ω = layerMatrix σ E z X₀ ω + ζ • fromBlocks Y₀ 0 0 0 := by
  rw [layerMatrix, layerMatrix, fromBlocks_smul, fromBlocks_add]
  simp only [smul_zero, add_zero]
  congr 1
  abel

/-- The one-port bond matrix is the reindexed bond block `B₀₀`. -/
theorem opm_bond_eq (B : Fin 1 → Fin 1 → Matrix (Fin W) (Fin W) ℂ) :
    bondMatrix .oneBlockOnePort B = (B 0 0).submatrix (opmE W) (opmE W) := by
  ext x y
  obtain ⟨i, a⟩ := x
  obtain ⟨j, c⟩ := y
  obtain rfl : i = 0 := Subsingleton.elim i 0
  obtain rfl : j = 0 := Subsingleton.elim j 0
  rfl

theorem opm_bond_isUnit {B : Fin 1 → Fin 1 → Matrix (Fin W) (Fin W) ℂ} (h : (B 0 0).det ≠ 0) :
    IsUnit (bondMatrix .oneBlockOnePort B).det := by
  rw [opm_bond_eq, det_submatrix_equiv_self]
  exact isUnit_iff_ne_zero.mpr h

end Vocabulary

/-!
## 3. The bounded pencil on the closed upper half-plane
-/

section Pencil

variable {n : Type} [Fintype n] [DecidableEq n]

/-- **Schur coercivity** (the passive-bounds lemma: `Im F⁻¹ ⪰ η|z|⁻²σ_min(B)²`). For
Hermitian `D`, `Y ⪰ 0`, `B*` invertible, `Im z > 0` and `Im ζ ≥ 0`:
`Im ⟨v, (D + ζY - z⁻¹BB*) v⟩ ≥ Im(-z⁻¹) (1 + ‖(B*)⁻¹‖)⁻² ‖v‖²`. Deterministic. -/
theorem opm_schur_coercive {D Y B : Matrix n n ℂ} (hD : D.IsHermitian) (hY : Y.PosSemidef)
    (hB : IsUnit Bᴴ.det) {z ζ : ℂ} (hz : 0 < z.im) (hζ : 0 ≤ ζ.im) :
    cplCoercive ((-z⁻¹).im / (1 + ‖(Bᴴ)⁻¹‖) ^ 2) (D + ζ • Y - z⁻¹ • (B * Bᴴ)) := by
  intro v
  set β := ‖(Bᴴ)⁻¹‖ with hβ
  have hβ0 : 0 ≤ β := norm_nonneg _
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_im] at hz; exact lt_irrefl 0 hz
  have ha : 0 ≤ (-z⁻¹).im := by
    rw [im_neg_inv]; exact div_nonneg hz.le (Complex.normSq_nonneg _)
  set u := Bᴴ *ᵥ v with hu
  have hv : v = (Bᴴ)⁻¹ *ᵥ u := by rw [hu, mulVec_mulVec, nonsing_inv_mul _ hB, one_mulVec]
  have hnorm : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ ≤
      (1 + β) * ‖(WithLp.toLp 2 u : EuclideanSpace ℂ n)‖ := by
    have h1 : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ ≤
        β * ‖(WithLp.toLp 2 u : EuclideanSpace ℂ n)‖ := by
      conv_lhs => rw [hv]
      exact norm_toLp_mulVec_le _ _
    have := norm_nonneg (WithLp.toLp 2 u : EuclideanSpace ℂ n)
    nlinarith
  have hsq : cplSq v ≤ (1 + β) ^ 2 * cplSq u := by
    rw [← cpl_norm_toLp_sq, ← cpl_norm_toLp_sq, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hY0 : 0 ≤ cplForm (ζ • Y) v := by
    have hq := hY.dotProduct_mulVec_nonneg v
    rw [Complex.le_def, Complex.zero_re, Complex.zero_im] at hq
    unfold cplForm
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_im, ← hq.2, mul_zero, zero_add]
    exact mul_nonneg hζ hq.1
  have hBB : cplForm (z⁻¹ • (B * Bᴴ)) v = z⁻¹.im * cplSq u := by
    unfold cplForm
    have e : star v ⬝ᵥ ((B * Bᴴ) *ᵥ v) = ((cplSq u : ℝ) : ℂ) := by
      rw [← mulVec_mulVec, dotProduct_mulVec, ← cpl_star_dot_self u, hu, star_mulVec,
        conjTranspose_conjTranspose]
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul, e, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, mul_zero, zero_add]
  rw [cpl_form_sub, cpl_form_add, cpl_form_herm hD, zero_add, hBB]
  have hpos : 0 < (1 + β) ^ 2 := by positivity
  have hneg : -(z⁻¹.im * cplSq u) = (-z⁻¹).im * cplSq u := by rw [Complex.neg_im]; ring
  calc (-z⁻¹).im / (1 + β) ^ 2 * cplSq v ≤ (-z⁻¹).im / (1 + β) ^ 2 * ((1 + β) ^ 2 * cplSq u) :=
        mul_le_mul_of_nonneg_left hsq (div_nonneg ha hpos.le)
    _ = (-z⁻¹).im * cplSq u := by field_simp
    _ ≤ cplForm (ζ • Y) v - z⁻¹.im * cplSq u := by linarith

/-- **The pencil is bounded on the closed upper half-plane** (the passive-bounds lemma:
"`F` is analytic and bounded on the closed upper half-plane"). For Hermitian `D`, `Y ⪰ 0`,
invertible `B`, `Im z > 0`: there is `K` with `[[D + ζY, B], [B*, z]]` invertible and of inverse
norm `≤ K` for every `Im ζ ≥ 0`. Deterministic (`K` depends on `B, z`). -/
theorem opm_pencil_bound {D Y B : Matrix n n ℂ} (hD : D.IsHermitian) (hY : Y.PosSemidef)
    (hB : IsUnit B.det) {z : ℂ} (hz : 0 < z.im) :
    ∃ K : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.im →
      IsUnit (fromBlocks D B Bᴴ (z • (1 : Matrix n n ℂ)) + ζ • fromBlocks Y 0 0 0).det ∧
      ‖(fromBlocks D B Bᴴ (z • (1 : Matrix n n ℂ)) + ζ • fromBlocks Y 0 0 0)⁻¹‖ ≤ K := by
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_im] at hz; exact lt_irrefl 0 hz
  have hBh : IsUnit Bᴴ.det := by rw [det_conjTranspose]; exact hB.star
  set c := (-z⁻¹).im / (1 + ‖(Bᴴ)⁻¹‖) ^ 2 with hc
  have hc0 : 0 < c := by
    refine div_pos ?_ (by positivity)
    rw [im_neg_inv]; exact div_pos hz (Complex.normSq_pos.mpr hz0)
  refine ⟨(1 + ‖B‖ / ‖z‖) ^ 2 * c⁻¹ + ‖z‖⁻¹, fun ζ hζ => ?_⟩
  have heq : fromBlocks D B Bᴴ (z • (1 : Matrix n n ℂ)) + ζ • fromBlocks Y 0 0 0 =
      fromBlocks (D + ζ • Y) B Bᴴ (z • (1 : Matrix n n ℂ)) := by
    rw [fromBlocks_smul, fromBlocks_add]; simp
  obtain ⟨hSu, hSn⟩ := cpl_coercive_inv hc0 (opm_schur_coercive hD hY hBh hz hζ)
  obtain ⟨hGu, hGn⟩ := BlockBand.Layers.fromBlocks_inv (D + ζ • Y) B z hz0 hSu
  rw [heq]
  exact ⟨hGu, hGn.trans (by gcongr)⟩

end Pencil

/-!
## 4. Poisson + Jensen + Tonelli
-/

section Tonelli

/-- Jensen on a probability space: `(∫ ‖g‖ₑ)^p ≤ ∫ ‖g‖ₑ^p`, `p ≥ 1`. -/
theorem opm_jensen {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {g : α → ℝ} (hg : AEStronglyMeasurable g ν) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ θ, ‖g θ‖ₑ ∂ν) ^ p ≤ ∫⁻ θ, ‖g θ‖ₑ ^ p ∂ν := by
  have hp0 : 0 < p := by linarith
  have h := eLpNorm_le_eLpNorm_of_exponent_le (f := g) (μ := ν) (p := 1)
    (q := ENNReal.ofReal p) (ENNReal.one_le_ofReal.mpr hp)
  rw [eLpNorm_one_eq_lintegral_enorm hg, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp0) ENNReal.ofReal_ne_top hg,
    ENNReal.toReal_ofReal hp0.le] at h
  calc (∫⁻ θ, ‖g θ‖ₑ ∂ν) ^ p ≤ ((∫⁻ θ, ‖g θ‖ₑ ^ p ∂ν) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow h hp0.le
    _ = ∫⁻ θ, ‖g θ‖ₑ ^ p ∂ν := by rw [one_div, ENNReal.rpow_inv_rpow hp0.ne']

/-- `opmCayley (circleMap 0 1 θ)` is real. -/
theorem opm_cayley_circle_real (θ : ℝ) :
    opmCayley (circleMap 0 1 θ) = ((opmCayley (circleMap 0 1 θ)).re : ℂ) := by
  refine Complex.ext rfl ?_
  rw [Complex.ofReal_im, opmCayley_im_eq_zero]
  simp [norm_circleMap_zero]

/-- **Poisson moments for a random affine pencil.** Let `T₀ : Ω → Matrix n n ℂ` be measurable,
`P` fixed, `p ≥ 1`, `μ` s-finite. If for `μ`-a.e. `ω` the pencil `T₀ ω + ζP` is invertible and
bounded (by some `K(ω)`) on the closed upper half-plane, and its real points have
`∫ ‖(T₀ ω + rP)⁻¹‖ₑ^p dμ ≤ M` uniformly in real `r`, then
`∫ ‖(T₀ ω + iP)⁻¹‖ₑ^p dμ ≤ 2^p M`. (Poisson bound pointwise, Jensen in `θ`, Tonelli; no
measurability of `K` is used.) -/
theorem opm_lintegral_pencil_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {n : Type*} [Fintype n] [DecidableEq n] {T₀ : Ω → Matrix n n ℂ} (hT₀ : Measurable T₀)
    (P : Matrix n n ℂ) {p : ℝ} (hp : 1 ≤ p)
    (hgood : ∀ᵐ ω ∂μ, ∃ K : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.im →
      IsUnit (T₀ ω + ζ • P).det ∧ ‖(T₀ ω + ζ • P)⁻¹‖ ≤ K)
    {M : ℝ≥0∞} (hreal : ∀ r : ℝ, ∫⁻ ω, ‖(T₀ ω + (r : ℂ) • P)⁻¹‖ₑ ^ p ∂μ ≤ M) :
    ∫⁻ ω, ‖(T₀ ω + Complex.I • P)⁻¹‖ₑ ^ p ∂μ ≤ 2 ^ p * M := by
  have hp0 : 0 < p := by linarith
  set c : ℝ → ℂ := fun θ => opmCayley (circleMap 0 1 θ) with hc
  have hcm : Measurable c := measurable_opmCayley.comp (continuous_circleMap 0 1).measurable
  have hinvm : Measurable (fun q : Ω × ℝ => (T₀ q.1 + c q.2 • P)⁻¹) :=
    measurable_matrix_inv.comp ((hT₀.comp measurable_fst).add ((hcm.comp measurable_snd).smul_const P))
  set g : Ω → ℝ → ℝ≥0∞ := fun ω θ => ‖(T₀ ω + c θ • P)⁻¹‖ₑ ^ p with hg
  have hgm : Measurable (Function.uncurry g) :=
    (measurable_enorm.comp hinvm).pow_const p
  have hpt : ∀ᵐ ω ∂μ, ‖(T₀ ω + Complex.I • P)⁻¹‖ₑ ^ p ≤ 2 ^ p * ∫⁻ θ, g ω θ ∂opmAngle := by
    filter_upwards [hgood] with ω hω
    obtain ⟨K, hK⟩ := hω
    have h := opm_poisson_lintegral (T₀ ω) P (fun ζ hζ => (hK ζ hζ).1) (fun ζ hζ => (hK ζ hζ).2)
    simp only [ofReal_norm] at h
    have hgθ : Measurable (fun θ => ‖(T₀ ω + c θ • P)⁻¹‖) :=
      continuous_norm.measurable.comp
        (measurable_matrix_inv.comp (measurable_const.add (hcm.smul_const P)))
    have hJ := opm_jensen (ν := opmAngle) hgθ.aestronglyMeasurable hp
    simp only [enorm_norm] at hJ
    calc ‖(T₀ ω + Complex.I • P)⁻¹‖ₑ ^ p
        ≤ (2 * ∫⁻ θ, ‖(T₀ ω + c θ • P)⁻¹‖ₑ ∂opmAngle) ^ p := ENNReal.rpow_le_rpow h hp0.le
      _ = 2 ^ p * (∫⁻ θ, ‖(T₀ ω + c θ • P)⁻¹‖ₑ ∂opmAngle) ^ p :=
          ENNReal.mul_rpow_of_nonneg _ _ hp0.le
      _ ≤ 2 ^ p * ∫⁻ θ, g ω θ ∂opmAngle := by gcongr
  calc ∫⁻ ω, ‖(T₀ ω + Complex.I • P)⁻¹‖ₑ ^ p ∂μ
      ≤ ∫⁻ ω, 2 ^ p * ∫⁻ θ, g ω θ ∂opmAngle ∂μ := lintegral_mono_ae hpt
    _ = 2 ^ p * ∫⁻ ω, ∫⁻ θ, g ω θ ∂opmAngle ∂μ :=
        lintegral_const_mul _ hgm.lintegral_prod_right'
    _ = 2 ^ p * ∫⁻ θ, ∫⁻ ω, g ω θ ∂μ ∂opmAngle := by
        rw [lintegral_lintegral_swap hgm.aemeasurable]
    _ ≤ 2 ^ p * ∫⁻ _θ, M ∂opmAngle := by
        gcongr with θ
        have h := hreal (c θ).re
        rwa [← opm_cayley_circle_real θ] at h
    _ = 2 ^ p * M := by rw [lintegral_const, measure_univ, mul_one]

/-- `eLpNorm` to lower integral: `‖f‖_p ≤ C ⇒ ∫ ‖f‖ₑ^p ≤ C^p`. -/
theorem opm_lintegral_le_of_eLpNorm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {p C : ℝ} (hp : 0 < p)
    (h : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C) :
    ∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ ≤ ENNReal.ofReal C ^ p := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le] at h
  calc ∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ = ((∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ) ^ (1 / p)) ^ p := by
        rw [one_div, ENNReal.rpow_inv_rpow hp.ne']
    _ ≤ ENNReal.ofReal C ^ p := ENNReal.rpow_le_rpow h hp.le

/-- Lower integral to `eLpNorm`: `∫ ‖f‖ₑ^p ≤ C^p ⇒ ‖f‖_p ≤ C`. -/
theorem opm_eLpNorm_le_of_lintegral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {p C : ℝ} (hp : 0 < p)
    (h : ∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ ≤ ENNReal.ofReal C ^ p) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le]
  calc (∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ) ^ (1 / p) ≤ (ENNReal.ofReal C ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = ENNReal.ofReal C := by rw [one_div, ENNReal.rpow_rpow_inv hp.ne']

end Tonelli

/-!
## 5. The one-port layer: good samples
-/

section Layer

variable {W : ℕ}

/-- Under `layerLaw W b .oneBlockOnePort` (`0 < b < 1/2`, `W ≥ 1`), a.s. the GUE block is
Hermitian and the bond matrix is invertible. -/
theorem opm_ae_good {b : ℝ} (hb0 : 0 < b) (hW : 0 < W) :
    ∀ᵐ ω ∂layerLaw W b .oneBlockOnePort,
      (blockDiag ω.1).IsHermitian ∧ IsUnit (bondMatrix .oneBlockOnePort ω.2).det := by
  have ht : Real.toNNReal (b / W) ≠ 0 := by
    have : 0 < b / W := div_pos hb0 (by exact_mod_cast hW)
    exact (Real.toNNReal_pos.mpr this).ne'
  have hA : ∀ᵐ A ∂blockLaw (LayerShape.oneBlockOnePort.blocks) W (1 - 2 * b),
      ∀ j, (A j).IsHermitian :=
    ae_blocks_isHermitian _ W (Real.toNNReal ((1 - 2 * b) / W))
  have hB : ∀ᵐ B ∂absnBondLaw W b .oneBlockOnePort, (B 0 0).det ≠ 0 := by
    have h1 := opm_ae_det_ginibre_ne_zero W ht
    have h2 : ∀ᵐ B₀ ∂(Measure.pi fun _ : Fin 1 =>
        ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))), (B₀ 0).det ≠ 0 :=
      (measurePreserving_eval (fun _ : Fin 1 =>
        ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) 0).quasiMeasurePreserving.ae
        (p := fun B : Matrix (Fin W) (Fin W) ℂ => B.det ≠ 0) h1
    exact (measurePreserving_eval (fun _ : Fin 1 => Measure.pi fun _ : Fin 1 =>
        ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) 0).quasiMeasurePreserving.ae
        (p := fun B₀ : Fin 1 → Matrix (Fin W) (Fin W) ℂ => (B₀ 0).det ≠ 0) h2
  rw [absn_layerLaw_eq]
  have hA' := (Measure.quasiMeasurePreserving_fst
    (μ := blockLaw (LayerShape.oneBlockOnePort.blocks) W (1 - 2 * b))
    (ν := absnBondLaw W b .oneBlockOnePort)).ae
    (p := fun A : Fin 1 → Matrix (Fin W) (Fin W) ℂ => ∀ j, (A j).IsHermitian) hA
  have hB' := (Measure.quasiMeasurePreserving_snd
    (μ := blockLaw (LayerShape.oneBlockOnePort.blocks) W (1 - 2 * b))
    (ν := absnBondLaw W b .oneBlockOnePort)).ae
    (p := fun B : Fin 1 → Fin 1 → Matrix (Fin W) (Fin W) ℂ => (B 0 0).det ≠ 0) hB
  filter_upwards [hA', hB'] with ω h1 h2
  exact ⟨blockDiag_isHermitian h1, opm_bond_isUnit h2⟩

/-- **Bounded one-port pencil on good samples.** If the GUE block is Hermitian and the bond is
invertible, `X_h` Hermitian, `Y ⪰ 0`, `Im z > 0`, then the layer matrix at input `X_h - ζY`,
`T₀ + ζ diag(Y,0)`, is invertible and bounded on the closed upper half-plane. Deterministic. -/
theorem opm_layer_pencil_bound (E : ℝ) {z : ℂ} (hz : 0 < z.im) {Xh Y : Matrix (Fin W) (Fin W) ℂ}
    (hXh : Xh.IsHermitian) (hY : Y.PosSemidef) {ω : LayerSample W .oneBlockOnePort}
    (hA : (blockDiag ω.1).IsHermitian) (hB : IsUnit (bondMatrix .oneBlockOnePort ω.2).det) :
    ∃ K : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.im →
      IsUnit (layerMatrix .oneBlockOnePort E z (onePortLift Xh) ω +
        ζ • fromBlocks (onePortLift Y) 0 0 0).det ∧
      ‖(layerMatrix .oneBlockOnePort E z (onePortLift Xh) ω +
        ζ • fromBlocks (onePortLift Y) 0 0 0)⁻¹‖ ≤ K :=
  opm_pencil_bound (layerDiag_isHermitian E _ (opm_lift_isHermitian hXh) ω hA)
    (opm_lift_posSemidef hY) hB hz

end Layer

/-!
## 6. Inverse moments for passive input
-/

/-- **Inverse moments of the passive one-port layer** (the passive-bounds lemma: "all fixed
operator moments of `𝒢` … are bounded uniformly in `W ≥ W₀(p), X`", via the Poisson extension).

* Law: `layerLaw W b .oneBlockOnePort` (`A ~ GUE_W((1-2b)/W)`, `B ~ Gin(b/W)` independent) at
  `z = boundaryZ b E`; the input `X` (`W × W`, on the physical sites via `onePortLift`) is
  deterministic (an independent `X` by Fubini).
* Domain: passive `X` (`IsPassiveInput X`: `-Im X ⪰ 0`; every Hermitian `X`), no norm bound on `X`;
  `E ∈ bulkInterval κ`.
* Norms: `ℓ²` operator norm of `𝒢 = onePortResolvent b E X` and of its physical (top, `Sum.inl`)
  block `𝒢₁₁ = 𝒢.toBlocks₁₁`; `L^p` norm `eLpNorm · (ofReal p)` under the layer law.
* Quantifiers: `b ∈ (0,1/2)`, `κ > 0`, `p ≥ 1` first; then `C > 0` and `W₀` (`W₀ = ⌈p/ε₁⌉`
  depends on `p`); then uniformly in `W ≥ W₀`, every passive `X` and `E ∈ bulkInterval κ`.
* Conclusion: the layer matrix is a.s. invertible (so `𝒢` is a.s. the true inverse), and
  `‖‖𝒢‖‖_{L^p} ≤ C`, `‖‖𝒢₁₁‖‖_{L^p} ≤ C`; here `C = 2 C_A`, `C_A` the absorption constant at
  `η₀(b, κ)`, `M = 3`.
* Inputs: `ConditionalBlockGUECount` (through `gaussianAbsorption_holds`, at the Hermitian inputs
  `X_h - tY`, `t` real). No order of limits is involved (fixed `W`). -/
theorem opm_passive_inverse_moments (hcount : ConditionalBlockGUECount) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), 0 < C ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin W) (Fin W) ℂ, IsPassiveInput X → ∀ E ∈ bulkInterval κ,
      (∀ᵐ ω ∂layerLaw W b .oneBlockOnePort,
        IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E) (onePortLift X) ω).det) ∧
      eLpNorm (fun ω => ‖onePortResolvent b E X ω‖) (ENNReal.ofReal p)
          (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C ∧
      eLpNorm (fun ω => ‖(onePortResolvent b E X ω).toBlocks₁₁‖) (ENNReal.ofReal p)
          (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C := by
  intro b hb0 hb1 κ hκ p hp
  have hp0 : 0 < p := by linarith
  obtain ⟨η₀, hη₀, hbulk⟩ := wl_bulk hb0 hb1 hκ
  obtain ⟨ε₁, CA, hε₁, hCA, habs⟩ := gaussianAbsorption_holds hcount b hb0 hb1 η₀ 3 hη₀
  refine ⟨2 * CA, ⌈p / ε₁⌉₊, by positivity, ?_⟩
  intro W hW hWW X hX E hE
  obtain ⟨hz, hzM, -⟩ := hbulk E hE
  have hzpos : 0 < (boundaryZ b E).im := lt_of_lt_of_le hη₀ hz
  have hpW : p ≤ ε₁ * W := by
    have h1 : p / ε₁ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWW)
    rw [div_le_iff₀ hε₁] at h1; linarith
  set μ := layerLaw W b .oneBlockOnePort with hμ
  set z := boundaryZ b E with hzdef
  set Xh := opmHerm X with hXh
  set Y := onePortDissipation X with hYdef
  have hY : Y.PosSemidef := hX
  have hXhH : Xh.IsHermitian := opmHerm_isHermitian X
  set P : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
    fromBlocks (onePortLift Y) 0 0 0 with hP
  set T₀ : LayerSample W .oneBlockOnePort →
      Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
    fun ω => layerMatrix .oneBlockOnePort E z (onePortLift Xh) ω with hT₀
  have hT₀m : Measurable T₀ := measurable_layerMatrix _ E z _
  have hpen : ∀ (ζ : ℂ) ω, layerMatrix .oneBlockOnePort E z (onePortLift (Xh - ζ • Y)) ω =
      T₀ ω + ζ • P := fun ζ ω => by
    rw [opm_lift_sub, opm_lift_smul, opm_layerMatrix_pencil]
  have hXI : ∀ ω, layerMatrix .oneBlockOnePort E z (onePortLift X) ω = T₀ ω + Complex.I • P :=
    fun ω => by
      have := hpen Complex.I ω
      rwa [← opm_decomp X] at this
  -- the good samples: bounded pencil on the closed upper half-plane
  have hgood : ∀ᵐ ω ∂μ, ∃ K : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.im →
      IsUnit (T₀ ω + ζ • P).det ∧ ‖(T₀ ω + ζ • P)⁻¹‖ ≤ K := by
    filter_upwards [opm_ae_good hb0 hW] with ω hω
    exact opm_layer_pencil_bound E hzpos hXhH hY hω.1 hω.2
  -- the Hermitian (real `ζ`) moments, uniform in the real shift
  have hreal : ∀ r : ℝ, ∫⁻ ω, ‖(T₀ ω + (r : ℂ) • P)⁻¹‖ₑ ^ p ∂μ ≤ ENNReal.ofReal CA ^ p := by
    intro r
    have hXr : (onePortLift (Xh - (r : ℂ) • Y)).IsHermitian :=
      opm_lift_isHermitian (opm_isHermitian_sub_real_smul hXhH hY.isHermitian r)
    obtain ⟨-, hm⟩ := habs W hW .oneBlockOnePort _ hXr E z hz hzM
    have h := opm_lintegral_le_of_eLpNorm
      (measurable_norm_layerResolvent _ E z _).aestronglyMeasurable hp0 (hm p hp hpW)
    simp only [enorm_norm, layerResolvent, hpen] at h
    exact h
  have := sing_isProbabilityMeasure_layerLaw W b .oneBlockOnePort
  have hmain := opm_lintegral_pencil_le hT₀m P hp hgood hreal
  have hGm : Measurable (fun ω => ‖onePortResolvent b E X ω‖) :=
    measurable_norm_layerResolvent _ E z _
  have hGbound : eLpNorm (fun ω => ‖onePortResolvent b E X ω‖) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (2 * CA) := by
    refine opm_eLpNorm_le_of_lintegral hGm.aestronglyMeasurable hp0 ?_
    have e : ∀ ω, ‖‖onePortResolvent b E X ω‖‖ₑ = ‖(T₀ ω + Complex.I • P)⁻¹‖ₑ := fun ω => by
      rw [enorm_norm, onePortResolvent, layerResolvent, hXI]
    simp only [e]
    refine hmain.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
  refine ⟨?_, hGbound, ?_⟩
  · filter_upwards [hgood] with ω hω
    obtain ⟨K, hK⟩ := hω
    rw [hXI]
    exact (hK Complex.I (by rw [Complex.I_im]; exact zero_le_one)).1
  · have hm : Measurable (fun ω => ‖(onePortResolvent b E X ω).toBlocks₁₁‖) :=
      (continuous_norm.comp wl_continuous_toBlocks11).measurable.comp
        (measurable_layerResolvent _ E z _)
    refine (eLpNorm_mono_ae hm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)).trans hGbound
    rw [norm_norm, norm_norm]
    exact wl_norm_toBlocks11_le _

/-!
## 7. Operator moments of `L = K𝒢₁₂`
-/

section Transfer

variable {W : ℕ}

/-- The site embedding `x ↦ (0, x)` of `Fin W` into the one-port sites. -/
abbrev opmIncl (W : ℕ) : Fin W → Fin 1 × Fin W := fun x => (0, x)

theorem opmIncl_bijective : Function.Bijective (opmIncl W) := by
  refine ⟨fun x y h => congrArg Prod.snd h, fun q => ⟨q.2, ?_⟩⟩
  rcases q with ⟨i, x⟩
  rw [Subsingleton.elim i 0]

/-- `L` as a compression of the weighted product: `onePortL = ((𝒦𝒢)₁₂)_{(0,·),(0,·)}`,
`𝒦 = diag(z - X̃, 0)`, `X̃ = onePortLift X`. -/
theorem opm_onePortL_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    onePortL b E X ω =
      ((wlKh (m := PortSite W .oneBlockOnePort)
          (boundaryZ b E • (1 : Matrix (PhysSite W .oneBlockOnePort)
            (PhysSite W .oneBlockOnePort) ℂ) - onePortLift X) *
        onePortResolvent b E X ω).toBlocks₁₂).submatrix (opmIncl W) (opmIncl W) := by
  rw [wl_Kh_mul_toBlocks12, submatrix_mul _ _ _ _ _ opmIncl_bijective]
  have h1 : (boundaryZ b E • (1 : Matrix (PhysSite W .oneBlockOnePort)
      (PhysSite W .oneBlockOnePort) ℂ) - onePortLift X).submatrix (opmIncl W) (opmIncl W) =
      boundaryZ b E • 1 - X := by
    ext x y
    by_cases h : x = y
    · subst h; simp [onePortLift]
    · simp [onePortLift, h, Matrix.one_apply_ne h]
  rw [h1]
  rfl

/-- `ω ↦ L` is Borel (Lean's totalized inverse). -/
theorem opm_measurable_onePortL (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (onePortL b E X) := by
  have hG : Measurable (onePortResolvent b E X) :=
    measurable_layerResolvent .oneBlockOnePort E (boundaryZ b E) (onePortLift X)
  have hc : Continuous (fun M : Matrix (LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort) ℂ =>
      (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) *
        M.submatrix (fun x => Sum.inl ((0 : Fin 1), x)) (fun y => Sum.inr ((0 : Fin 1), y))) :=
    continuous_const.matrix_mul (continuous_id.matrix_submatrix _ _)
  exact hc.measurable.comp hG

/-- **Pointwise transfer bound** (the word `K𝒢` only): wherever the
one-port layer matrix is invertible, for every `X` (no Hermiticity or passivity), `|E| ≤ 2` and
`|z_∂| ≤ 3`: `‖L‖ ≤ 1 + 6 (1 + ‖Λ‖) ‖𝒢‖ = wlF`. Deterministic. -/
theorem opm_norm_onePortL_le {b E : ℝ} (hE : |E| ≤ 2) (hz : ‖boundaryZ b E‖ ≤ 3)
    (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort)
    (hN : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E) (onePortLift X) ω).det) :
    ‖onePortL b E X ω‖ ≤ wlF E (boundaryZ b E) (onePortLift X) ω := by
  set z := boundaryZ b E with hzdef
  set N := layerMatrix .oneBlockOnePort E z (onePortLift X) ω with hNdef
  set G := layerResolvent .oneBlockOnePort E z (onePortLift X) ω with hGdef
  have h1 : N * G = 1 := mul_nonsing_inv _ hN
  have hG0 := norm_nonneg G
  have hl0 := norm_nonneg (wlLam ω)
  have hr : ‖z‖ + |E| + 0 ≤ 5 := by linarith
  have hK : ‖wlKh (m := PortSite W .oneBlockOnePort)
      (z • (1 : Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ) -
        onePortLift X) * G‖ ≤ wlF E z (onePortLift X) ω := by
    rw [wl_Kh_mul_eq h1]
    refine wl_norm_weighted_le.trans ?_
    have hb := wl_norm_Kh_sub_left_le E z (onePortLift X) ω (le_refl (0 : ℝ))
    rw [wl_tflReg_zero] at hb
    refine (add_le_add le_rfl (mul_le_mul_of_nonneg_right hb hG0)).trans ?_
    exact wl_shift_le hr hG0 _ hl0
  rw [opm_onePortL_eq]
  refine (wl_norm_submatrix_le _ opmIncl_bijective.1 opmIncl_bijective.1).trans ?_
  exact (wl_norm_toBlocks12_le _).trans hK

end Transfer

/-- **Operator-norm moments of the one-port transfer `L = K𝒢₁₂`**
(`LayersOnePort.OnePortOperatorMomentsContract`; the passive-bounds lemma, the one-port form of
the moment clause of the weighted-layer lemma).

* `measurable`: `ω ↦ onePortL b E X ω` is Borel for every `W, b, E, X`
  (`opm_measurable_onePortL`; Lean's totalized inverse).
* `moments`: law `layerLaw W b .oneBlockOnePort` at `z = z_∂(E)`; domain: passive `X`
  (`-Im X ⪰ 0`, unbounded `K = z - X` allowed) and `E ∈ bulkInterval κ`; norms: `ℓ²` operator norm
  of `L`, `L^p` norm under the layer law; quantifiers: `b ∈ (0,1/2)`, `κ > 0`, `p ≥ 1` first, then
  `C_p = 1 + 6 C_Λ C_A(2p)` and `W₀ = max(W₀(2p), ⌈2p⌉)` (depending on `p`), then uniformly in
  `W ≥ W₀`, passive `X`, `E ∈ bulkInterval κ`: `‖‖L‖‖_{L^p} ≤ C_p`. No order of limits.
* Proof: `‖L‖ ≤ 1 + 6(1 + ‖Λ‖)‖𝒢‖` a.s. for every `X` (`opm_norm_onePortL_le`, only the word
  `K𝒢`), Hölder (`wl_eLpNorm_F_le`) with the Gaussian moments of `Λ = [[A, B], [B*, 0]]`
  (`wl_lam_eLpNorm_le_layer`, GUE block and Ginibre bond) and the passive inverse moments
  `opm_passive_inverse_moments` at order `2p`.
* Inputs: `ConditionalBlockGUECount` only (`GaussianLpGradient` is not used). -/
theorem onePortOperatorMoments_holds (hcount : ConditionalBlockGUECount) :
    OnePortOperatorMomentsContract where
  measurable W b E X := opm_measurable_onePortL b E X
  moments := by
    intro b hb0 hb1 κ hκ p hp
    obtain ⟨η₀, hη₀, hbulk⟩ := wl_bulk hb0 hb1 hκ
    obtain ⟨CA, W₁, hCA, h1⟩ := opm_passive_inverse_moments hcount b hb0 hb1 κ hκ (2 * p)
      (by linarith)
    refine ⟨1 + 6 * (wlLamConst * CA), max W₁ ⌈2 * p⌉₊, ?_⟩
    intro W hW hWW X hX E hE
    obtain ⟨-, hzM, hE2⟩ := hbulk E hE
    obtain ⟨hinv, hG, -⟩ := h1 W hW (le_of_max_le_left hWW) X hX E hE
    have hW2 : 2 * p ≤ W :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hWW)
    have := bond_isProbabilityMeasure_layerLaw W b .oneBlockOnePort
    have hF := wl_eLpNorm_F_le (μ := layerLaw W b .oneBlockOnePort)
      (Lam := fun ω => ‖wlLam ω‖) (Gn := fun ω => ‖onePortResolvent b E X ω‖)
      (continuous_norm.measurable.comp wl_measurable_wlLam).aestronglyMeasurable
      (measurable_norm_layerResolvent _ E _ _).aestronglyMeasurable hp wlLamConst_pos.le hCA.le
      (wl_lam_eLpNorm_le_layer hb0 hb1 (by linarith) hW2) hG
    refine (eLpNorm_mono_ae (opm_measurable_onePortL b E X).norm.aestronglyMeasurable
      (hinv.mono fun ω hω => ?_)).trans hF
    rw [norm_norm]
    refine (opm_norm_onePortL_le hE2 hzM X ω hω).trans (le_of_eq ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    rfl

end BlockBand.Layers
