module

public import BlockBand.Layers.AbsorberCount
public import BlockBand.Layers.BondSingular
public import BlockBand.Layers.BondMoments
public import BlockBand.Layers.LayerResolventBound
public import BlockBand.Layers.LayerMeasurability

/-!
# Gaussian absorption: almost-sure invertibility and resolvent moments

The Gaussian absorption lemma for all four layer shapes: `GaussianAbsorptionContract` from
`ConditionalBlockGUECount` alone (`gaussianAbsorption_holds`).

Proof. Fix the shape `σ`, `W ≥ 1`, a deterministic Hermitian `X`, real `E` and `z` with
`Im z ≥ η₀`, `|z| ≤ M`. For a block sample `A` (Hermitian a.s.) put `D = diag(A) - E - X`,
`δ = absorbedGap (W/8)` (`min(1, |λ|_{(⌊W/8⌋+1)}(D))`), `P` the spectral projection of `D` on
`{|λ| < δ}` and `S` its range (`dim S ≤ ⌊W/8⌋`). For bonds `B` put `d = singFloor S B` and
`K = ‖B‖`. Then (`layerResolvent_bound`) `‖𝒢‖ ≤ L (1+K)⁶ d⁻² δ⁻²`,
`L = layerResolventConstant η₀ M`, whenever `d, δ > 0`, which holds almost surely. By AM–GM,
`(1+K)^{6p} d^{-2p} ≤ ((1+K)^{12p} + d^{-4p})/2`. Tonelli over `layerLaw = blockLaw ⊗ bondLaw`:
the inner bond integral is bounded by the bond moments (`bond_lintegral_rpow_le`, `q = 12p ≤ W`)
and the singular-floor moments, uniform in the (block-dependent) subspace `S`
(`singFloor_inv_moment`, `q = 4p ≤ W/2`); the outer block integral by the gap moments
(`absorbedGap_inv_moment`, `q = 2p ≤ W/16`). With `ε₁ = 1/48`: `E‖𝒢‖^p ≤ C^p`,
`C = L Cδ² (C_K¹² + C_d⁴)`, depending only on `b, η₀, M` (and the PSSS constant).

No measurability of `d` or of the subspace `S` in `A` is used: the integrand `‖𝒢‖^p` is
measurable (`measurable_norm_layerResolvent`), Tonelli is applied to it, and the majorants are
integrated only after the integration variables are separated. Bond-only integrals and null
sets are transferred from `layerLaw` to the bond factor (`absn_lintegral_bond_le`,
`absn_ae_bond`), since the block factor is a probability measure.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Module Filter Topology
open BlockBand.Internal.Contracts.Layers
open BlockBand.External
open BlockBand.Internal.Contracts.Inputs (ConditionalBlockGUECount)
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-!
## 1. The bond factor of `layerLaw`
-/

/-- The bond factor of `layerLaw W b σ`: independent `Gin(b/W)` blocks. -/
abbrev absnBondLaw (W : ℕ) (b : ℝ) (σ : LayerShape) :
    Measure (Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ) :=
  Measure.pi fun _ : Fin σ.blocks => Measure.pi fun _ : Fin σ.ports =>
    ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))

/-- `layerLaw = blockLaw ⊗ absnBondLaw` (definitional). -/
theorem absn_layerLaw_eq (W : ℕ) (b : ℝ) (σ : LayerShape) :
    layerLaw W b σ = (blockLaw σ.blocks W (1 - 2 * b)).prod (absnBondLaw W b σ) :=
  rfl

/-- The bond factor is the image of `layerLaw` under `ω ↦ ω.2`. -/
theorem absn_map_snd (W : ℕ) (b : ℝ) (σ : LayerShape) :
    (layerLaw W b σ).map Prod.snd = absnBondLaw W b σ := by
  rw [absn_layerLaw_eq, Measure.map_snd_prod, measure_univ, one_smul]

/-- **Bond-only integrals**: for every (not necessarily measurable) `g`,
`∫⁻ g dν ≤ ∫⁻ g(ω.2) d(layerLaw)`. -/
theorem absn_lintegral_bond_le (W : ℕ) (b : ℝ) (σ : LayerShape)
    (g : (Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ) → ℝ≥0∞) :
    ∫⁻ B, g B ∂absnBondLaw W b σ ≤ ∫⁻ ω, g ω.2 ∂layerLaw W b σ := by
  calc ∫⁻ B, g B ∂absnBondLaw W b σ = ∫⁻ B, g B ∂((layerLaw W b σ).map Prod.snd) := by
        rw [absn_map_snd]
    _ ≤ ∫⁻ ω, g ω.2 ∂layerLaw W b σ := lintegral_map_le g measurable_snd.aemeasurable

/-- **Bond-only null sets**: an event of the bonds that is `layerLaw`-null is null for the
bond factor (no measurability used). -/
theorem absn_ae_bond (W : ℕ) (b : ℝ) (σ : LayerShape)
    {P : (Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ) → Prop}
    (h : ∀ᵐ ω ∂layerLaw W b σ, P ω.2) : ∀ᵐ B ∂absnBondLaw W b σ, P B := by
  rw [ae_iff] at h ⊢
  have hset : {ω : LayerSample W σ | ¬P ω.2} = Set.univ ×ˢ {B | ¬P B} := by ext ω; simp
  rw [hset, absn_layerLaw_eq, Measure.prod_prod, measure_univ, one_mul] at h
  exact h

/-- The bond matrix is measurable on the bond factor. -/
theorem absn_measurable_bondMatrix {W : ℕ} (σ : LayerShape) :
    Measurable (fun B : Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ =>
      bondMatrix σ B) := by
  have h := (bond_measurable_bondMatrix (W := W) σ).comp
    ((measurable_const (a := (0 : Fin σ.blocks → Matrix (Fin W) (Fin W) ℂ))).prodMk
      measurable_id)
  exact h

/-!
## 2. The absorbed gap and the low subspace
-/

/-- **`δ > 0` almost surely** under `blockLaw` (from `absorbedGap_tail` as `t → 0`). -/
theorem absn_gap_pos_ae (hcount : ConditionalBlockGUECount) {k W : ℕ} (hW : 0 < W) {c : ℝ}
    (hc : 0 < c) (E : ℝ) (X : PSSS.HermitianMatrix (Fin k × Fin W)) :
    ∀ᵐ A ∂blockLaw k W c, 0 < absorbedGap (W / 8) E X A := by
  obtain ⟨C, _, htail⟩ := absorbedGap_tail hcount
  rw [ae_iff]
  simp only [not_lt]
  refine le_antisymm ?_ bot_le
  set C' := gapTailConstant C k c
  have hT : Tendsto (fun t : ℝ => ENNReal.ofReal ((C' * t) ^ (W / 8 + 1))) (𝓝[>] 0)
      (𝓝 0) := by
    have hcont : Continuous (fun t : ℝ => ENNReal.ofReal ((C' * t) ^ (W / 8 + 1))) :=
      ENNReal.continuous_ofReal.comp ((continuous_const.mul continuous_id).pow _)
    have h0 := hcont.tendsto 0
    have e : ENNReal.ofReal ((C' * 0) ^ (W / 8 + 1)) = 0 := by
      rw [mul_zero, zero_pow (Nat.succ_ne_zero _), ENNReal.ofReal_zero]
    rw [e] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hT ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  have hsub : {A | absorbedGap (W / 8) E X A ≤ 0} ⊆ {A | absorbedGap (W / 8) E X A < t} :=
    fun A hA => lt_of_le_of_lt hA ht.1
  exact (measure_mono hsub).trans (htail k W hW c hc E X t ht.1 ht.2)

/-- The absorbed gap `δ(A)` of a layer with deterministic Hermitian `X`. -/
def absnGap {W : ℕ} {σ : LayerShape} (E : ℝ) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (hX : X.IsHermitian) (A : Fin σ.blocks → Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  absorbedGap (W / 8) E ⟨X, hX⟩ A

/-- The low subspace `S(A)`: span of the eigenvectors of `D` with `|λ| < δ(A)`. -/
def absnSub {W : ℕ} {σ : LayerShape} (E : ℝ) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (hX : X.IsHermitian) (A : Fin σ.blocks → Matrix (Fin W) (Fin W) ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (PhysSite W σ)) :=
  lowSubspace (absorbedMatrix E ⟨X, hX⟩ A).2 (absnGap E X hX A)

/-- `dim S(A) ≤ ⌊W/8⌋` (at most `⌊W/8⌋` eigenvalues satisfy `|λ| < δ`). -/
theorem absn_finrank_sub_le {W : ℕ} {σ : LayerShape} (E : ℝ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (hX : X.IsHermitian)
    (A : Fin σ.blocks → Matrix (Fin W) (Fin W) ℂ) :
    finrank ℂ (absnSub E X hX A) ≤ W / 8 := by
  have h1 := finrank_lowSubspace_le (absorbedMatrix E ⟨X, hX⟩ A).2 (absnGap E X hX A)
  have h2 := smallCount_eq_card (absorbedMatrix E ⟨X, hX⟩ A) (absnGap E X hX A)
  have h3 : smallCount (absorbedMatrix E ⟨X, hX⟩ A) (absnGap E X hX A) ≤ W / 8 :=
    smallCount_gapFloor_le (W / 8) _
  rw [Fintype.card_eq_nat_card, ← h2] at h1
  exact h1.trans h3

/-!
## 3. The pointwise bound
-/

/-- **Pointwise layer bound**: for a sample with Hermitian blocks,
`δ(A) > 0` and `d = singFloor S(A) B > 0`, the layer matrix is invertible and
`‖𝒢‖ ≤ L (1+K)⁶ / (d δ)²`, `K = ‖B‖`. Deterministic. -/
theorem absn_pointwise {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (hX : X.IsHermitian) (ω : LayerSample W σ)
    (hA : ∀ j, (ω.1 j).IsHermitian) {η₀ M : ℝ} (hη : 0 < η₀) (hz : η₀ ≤ z.im)
    (hM : ‖z‖ ≤ M) (hδ : 0 < absnGap E X hX ω.1) (hd : 0 < singFloor (absnSub E X hX ω.1) ω.2) :
    IsUnit (layerMatrix σ E z X ω).det ∧
      ‖layerResolvent σ E z X ω‖ ≤ layerResolventConstant η₀ M *
        (1 + ‖bondMatrix σ ω.2‖) ^ 6 /
          (singFloor (absnSub E X hX ω.1) ω.2 * absnGap E X hX ω.1) ^ 2 := by
  set H := absorbedMatrix E ⟨X, hX⟩ ω.1 with hH
  have hval : H.1 = blockDiag ω.1 - (E : ℂ) • 1 - X := absorbedMatrix_val E ⟨X, hX⟩ hA
  refine layerResolvent_bound σ E z X hX ω (blockDiag_isHermitian hA) hη hz hM
    (lowProjection H.2 (absnGap E X hX ω.1)) _ _ _ hd
    (singFloor_le_one _ _) hδ (absorbedGap_le_one _ _ _ _) le_rfl ?_ ?_
  · intro v
    calc absnGap E X hX ω.1 * ‖v - toEuclideanLin (lowProjection H.2 (absnGap E X hX ω.1)) v‖
        ≤ ‖toEuclideanLin H.1 v‖ := lowProjection_gap H.2 hδ.le v
      _ = ‖toEuclideanLin (blockDiag ω.1 - (E : ℂ) • 1 - X) v‖ := by rw [hval]
  · intro v
    exact singFloor_hPB_lowProjection ω.2 H.2 (absnGap E X hX ω.1) v

/-- **AM–GM majorant**: if `0 ≤ G ≤ L (1+K)⁶/(dδ)²` with `d, δ > 0` then
`G^p ≤ L^p ((1+K)^{12p} + d^{-4p})/2 · δ^{-2p}`. -/
theorem absn_rpow_bound {G L K d δ p : ℝ} (hG0 : 0 ≤ G) (hL : 0 ≤ L) (hK : 0 ≤ K) (hd : 0 < d)
    (hδ : 0 < δ) (hp : 0 ≤ p) (hG : G ≤ L * (1 + K) ^ 6 / (d * δ) ^ 2) :
    G ^ p ≤ L ^ p * (((1 + K) ^ (12 * p) + d⁻¹ ^ (4 * p)) / 2) * δ⁻¹ ^ (2 * p) := by
  have hK1 : 0 ≤ 1 + K := by linarith
  have hdi : 0 ≤ d⁻¹ := (inv_pos.mpr hd).le
  have hδi : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  have e0 : L * (1 + K) ^ 6 / (d * δ) ^ 2 = L * ((1 + K) ^ 6 * ((d⁻¹ ^ 2) * (δ⁻¹ ^ 2))) := by
    field_simp
  rw [e0] at hG
  have h1 : G ^ p ≤ (L * ((1 + K) ^ 6 * ((d⁻¹ ^ 2) * (δ⁻¹ ^ 2)))) ^ p :=
    Real.rpow_le_rpow hG0 hG hp
  rw [Real.mul_rpow hL (by positivity), Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)] at h1
  have eK : ((1 + K) ^ 6) ^ p = (1 + K) ^ (6 * p) := by
    rw [← Real.rpow_natCast_mul hK1]; norm_num
  have ed : (d⁻¹ ^ 2) ^ p = d⁻¹ ^ (2 * p) := by
    rw [← Real.rpow_natCast_mul hdi]; norm_num
  have eδ : (δ⁻¹ ^ 2) ^ p = δ⁻¹ ^ (2 * p) := by
    rw [← Real.rpow_natCast_mul hδi]; norm_num
  rw [eK, ed, eδ] at h1
  set x := (1 + K) ^ (6 * p)
  set y := d⁻¹ ^ (2 * p)
  have ex : (1 + K) ^ (12 * p) = x ^ 2 := by
    rw [← Real.rpow_mul_natCast hK1]; ring_nf
  have ey : d⁻¹ ^ (4 * p) = y ^ 2 := by
    rw [← Real.rpow_mul_natCast hdi]; ring_nf
  rw [ex, ey]
  have hx : 0 ≤ x := Real.rpow_nonneg hK1 _
  have hy : 0 ≤ y := Real.rpow_nonneg hdi _
  have hu : 0 ≤ δ⁻¹ ^ (2 * p) := Real.rpow_nonneg hδi _
  have hLp : 0 ≤ L ^ p := Real.rpow_nonneg hL _
  have hxy : x * y ≤ (x ^ 2 + y ^ 2) / 2 := by nlinarith [sq_nonneg (x - y)]
  calc G ^ p ≤ L ^ p * (x * (y * δ⁻¹ ^ (2 * p))) := h1
    _ = L ^ p * (x * y) * δ⁻¹ ^ (2 * p) := by ring
    _ ≤ L ^ p * ((x ^ 2 + y ^ 2) / 2) * δ⁻¹ ^ (2 * p) := by gcongr

/-- The same majorant in `ℝ≥0∞`, split for Tonelli:
`ofReal(G^p) ≤ ofReal(L^p/2 · δ^{-2p}) (ofReal((1+K)^{12p}) + ofReal(d^{-4p}))`. -/
theorem absn_ofReal_bound {G L K d δ p : ℝ} (hG0 : 0 ≤ G) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hd : 0 < d) (hδ : 0 < δ) (hp : 0 ≤ p) (hG : G ≤ L * (1 + K) ^ 6 / (d * δ) ^ 2) :
    ENNReal.ofReal (G ^ p) ≤ ENNReal.ofReal (L ^ p / 2 * δ⁻¹ ^ (2 * p)) *
      (ENNReal.ofReal ((1 + K) ^ (12 * p)) + ENNReal.ofReal (d⁻¹ ^ (4 * p))) := by
  have hK1 : 0 ≤ 1 + K := by linarith
  have ha : 0 ≤ (1 + K) ^ (12 * p) := Real.rpow_nonneg hK1 _
  have hc : 0 ≤ d⁻¹ ^ (4 * p) := Real.rpow_nonneg (inv_pos.mpr hd).le _
  have hu : 0 ≤ L ^ p / 2 * δ⁻¹ ^ (2 * p) :=
    mul_nonneg (div_nonneg (Real.rpow_nonneg hL _) zero_le_two)
      (Real.rpow_nonneg (inv_pos.mpr hδ).le _)
  rw [← ENNReal.ofReal_add ha hc, ← ENNReal.ofReal_mul hu]
  refine ENNReal.ofReal_le_ofReal ((absn_rpow_bound hG0 hL hK hd hδ hp hG).trans (le_of_eq ?_))
  ring

/-!
## 4. Constants
-/

/-- `0 < layerResolventConstant η₀ M` for `η₀ > 0`. -/
theorem absn_layerResolventConstant_pos {η₀ : ℝ} (hη : 0 < η₀) (M : ℝ) :
    0 < layerResolventConstant η₀ M := by
  unfold layerResolventConstant
  have : 0 < η₀⁻¹ := inv_pos.mpr hη
  positivity

/-- Final constant arithmetic:
`L^p/2 · Cδ^{2p} (C_K^{12p} + C_d^{4p}) ≤ (L Cδ² (C_K¹² + C_d⁴))^p`. -/
theorem absn_const_le {L Cδ CK Cd p : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ Cδ) (hK : 0 ≤ CK) (hd : 0 ≤ Cd)
    (hp : 0 ≤ p) :
    L ^ p / 2 * Cδ ^ (2 * p) * (CK ^ (12 * p) + Cd ^ (4 * p)) ≤
      (L * Cδ ^ 2 * (CK ^ 12 + Cd ^ 4)) ^ p := by
  have hT : 0 ≤ CK ^ 12 + Cd ^ 4 := by positivity
  rw [Real.mul_rpow (by positivity) hT, Real.mul_rpow hL (by positivity)]
  have eδ : (Cδ ^ 2) ^ p = Cδ ^ (2 * p) := by
    rw [← Real.rpow_natCast_mul hδ]; norm_num
  have eK : CK ^ (12 * p) = (CK ^ 12) ^ p := by
    rw [← Real.rpow_natCast_mul hK]; norm_num
  have ed : Cd ^ (4 * p) = (Cd ^ 4) ^ p := by
    rw [← Real.rpow_natCast_mul hd]; norm_num
  rw [eδ, eK, ed]
  have h1 : (CK ^ 12) ^ p ≤ (CK ^ 12 + Cd ^ 4) ^ p :=
    Real.rpow_le_rpow (by positivity) (by linarith [pow_nonneg hd 4]) hp
  have h2 : (Cd ^ 4) ^ p ≤ (CK ^ 12 + Cd ^ 4) ^ p :=
    Real.rpow_le_rpow (by positivity) (by linarith [pow_nonneg hK 12]) hp
  have hA : 0 ≤ L ^ p * Cδ ^ (2 * p) := mul_nonneg (Real.rpow_nonneg hL _) (Real.rpow_nonneg hδ _)
  calc L ^ p / 2 * Cδ ^ (2 * p) * ((CK ^ 12) ^ p + (Cd ^ 4) ^ p)
      = (L ^ p * Cδ ^ (2 * p)) * (((CK ^ 12) ^ p + (Cd ^ 4) ^ p) / 2) := by ring
    _ ≤ (L ^ p * Cδ ^ (2 * p)) * (CK ^ 12 + Cd ^ 4) ^ p := by
        gcongr; linarith
    _ = L ^ p * Cδ ^ (2 * p) * (CK ^ 12 + Cd ^ 4) ^ p := rfl

/-!
## 5. The Gaussian absorption lemma
-/

/-- **The Gaussian absorption lemma**, all four layer shapes, from `ConditionalBlockGUECount`
alone. Law `layerLaw W b σ`. For `0 < b < 1/2`, `η₀ > 0` and `M`: `ε₁ = 1/48` and
`C = L Cδ² (C_K¹² + C_d⁴)` with `L = layerResolventConstant η₀ M`,
`Cδ = max_{k ∈ {1,2}} gapMomentConstant C_PSSS k (1-2b)`, `C_K = bondMomentConst b`,
`C_d = singMomentConst b` (depending only on `b, η₀, M` and the PSSS constant). Uniformly in
`W ≥ 1`, the shape, deterministic Hermitian `X`, real `E` and `z` with `Im z ≥ η₀`, `|z| ≤ M`:
the layer matrix is a.s. invertible and `‖‖𝒢‖‖_{L^p} ≤ C` for `1 ≤ p ≤ W/48`. -/
theorem gaussianAbsorption_holds (hcount : ConditionalBlockGUECount) :
    GaussianAbsorptionContract := by
  intro b hb hb2 η₀ M hη
  obtain ⟨Cg, _, hgap⟩ := absorbedGap_inv_moment hcount
  have hc : 0 < 1 - 2 * b := by linarith
  set Cδ := max (gapMomentConstant Cg 1 (1 - 2 * b)) (gapMomentConstant Cg 2 (1 - 2 * b))
    with hCδ
  set CK := bondMomentConst b with hCKdef
  set Cd := singMomentConst b with hCddef
  set L := layerResolventConstant η₀ M with hLdef
  have hL : 0 < L := absn_layerResolventConstant_pos hη M
  have hCδ0 : 0 < Cδ := lt_max_of_lt_left (gapMomentConstant_pos _ _ _)
  have hCK : 0 < CK := bondMomentConst_pos b
  have hCd : 0 < Cd := singMomentConst_pos b
  set Cfin := L * Cδ ^ 2 * (CK ^ 12 + Cd ^ 4) with hCfin
  have hC0 : 0 < Cfin := by positivity
  refine ⟨1 / 48, Cfin, by norm_num, hC0, ?_⟩
  intro W hW σ X hX E z hz hM
  have hgood : ∀ᵐ A ∂blockLaw σ.blocks W (1 - 2 * b),
      (∀ j, (A j).IsHermitian) ∧ 0 < absnGap E X hX A := by
    filter_upwards [ae_blocks_isHermitian σ.blocks W (Real.toNNReal ((1 - 2 * b) / W)),
      absn_gap_pos_ae hcount hW hc E ⟨X, hX⟩] with A h1 h2
    exact ⟨h1, h2⟩
  have hbond : ∀ A, ∀ᵐ B ∂absnBondLaw W b σ, 0 < singFloor (absnSub E X hX A) B := fun A =>
    absn_ae_bond W b σ (singFloor_pos_ae σ hW hb _ (absn_finrank_sub_le E X hX A))
  refine ⟨?_, ?_⟩
  · -- almost-sure invertibility
    have hmeas : MeasurableSet {ω : LayerSample W σ | (layerMatrix σ E z X ω).det ≠ 0} :=
      (measurableSet_singleton 0).compl.preimage
        ((continuous_id.matrix_det).measurable.comp (measurable_layerMatrix σ E z X))
    have h : ∀ᵐ ω ∂layerLaw W b σ, (layerMatrix σ E z X ω).det ≠ 0 := by
      rw [absn_layerLaw_eq, Measure.ae_prod_iff_ae_ae hmeas]
      filter_upwards [hgood] with A hA
      filter_upwards [hbond A] with B hB
      exact (absn_pointwise σ E z X hX (A, B) hA.1 hη hz hM hA.2 hB).1.ne_zero
    filter_upwards [h] with ω hω
    exact isUnit_iff_ne_zero.mpr hω
  · intro p hp1 hpW
    have hp0 : 0 < p := by linarith
    have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
    have h2p1 : 1 ≤ 2 * p := by linarith
    have h2pW : 2 * p ≤ (W : ℝ) / 16 := by linarith
    have h4p1 : 1 ≤ 4 * p := by linarith
    have h4pW : 4 * p ≤ (W : ℝ) / 2 := by linarith
    have h12p1 : 1 ≤ 12 * p := by linarith
    have h12pW : 12 * p ≤ (W : ℝ) := by linarith
    have hLp : 0 ≤ L ^ p / 2 := div_nonneg (Real.rpow_nonneg hL.le _) zero_le_two
    have hgi : ∀ A, 0 ≤ (absnGap E X hX A)⁻¹ ^ (2 * p) := fun A =>
      Real.rpow_nonneg (inv_nonneg.mpr (absorbedGap_nonneg _ _ _ _)) _
    set Q := ENNReal.ofReal (CK ^ (12 * p)) + ENNReal.ofReal (Cd ^ (4 * p)) with hQ
    have hQtop : Q ≠ ∞ := ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
    -- the inner (bond) integral, for a good block sample
    have hinner : ∀ A, (∀ j, (A j).IsHermitian) ∧ 0 < absnGap E X hX A →
        ∫⁻ B, ENNReal.ofReal (‖layerResolvent σ E z X (A, B)‖ ^ p) ∂absnBondLaw W b σ ≤
          ENNReal.ofReal (L ^ p / 2 * (absnGap E X hX A)⁻¹ ^ (2 * p)) * Q := by
      intro A hA
      calc ∫⁻ B, ENNReal.ofReal (‖layerResolvent σ E z X (A, B)‖ ^ p) ∂absnBondLaw W b σ
          ≤ ∫⁻ B, ENNReal.ofReal (L ^ p / 2 * (absnGap E X hX A)⁻¹ ^ (2 * p)) *
              (ENNReal.ofReal ((1 + ‖bondMatrix σ B‖) ^ (12 * p)) +
                ENNReal.ofReal ((singFloor (absnSub E X hX A) B)⁻¹ ^ (4 * p)))
                ∂absnBondLaw W b σ := by
            refine lintegral_mono_ae ?_
            filter_upwards [hbond A] with B hB
            exact absn_ofReal_bound (norm_nonneg _) hL.le (norm_nonneg _) hB hA.2 hp0.le
              (absn_pointwise σ E z X hX (A, B) hA.1 hη hz hM hA.2 hB).2
        _ = ENNReal.ofReal (L ^ p / 2 * (absnGap E X hX A)⁻¹ ^ (2 * p)) *
              (∫⁻ B, ENNReal.ofReal ((1 + ‖bondMatrix σ B‖) ^ (12 * p)) ∂absnBondLaw W b σ +
                ∫⁻ B, ENNReal.ofReal ((singFloor (absnSub E X hX A) B)⁻¹ ^ (4 * p))
                  ∂absnBondLaw W b σ) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left]
            exact ENNReal.measurable_ofReal.comp
              (((continuous_norm.measurable.comp (absn_measurable_bondMatrix σ)).const_add
                1).pow_const _)
        _ ≤ ENNReal.ofReal (L ^ p / 2 * (absnGap E X hX A)⁻¹ ^ (2 * p)) * Q := by
            refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) zero_le
            · exact (absn_lintegral_bond_le W b σ
                (fun B => ENNReal.ofReal ((1 + ‖bondMatrix σ B‖) ^ (12 * p)))).trans
                (bond_lintegral_rpow_le σ hb h12p1 h12pW)
            · exact (absn_lintegral_bond_le W b σ
                (fun B => ENNReal.ofReal ((singFloor (absnSub E X hX A) B)⁻¹ ^ (4 * p)))).trans
                (singFloor_inv_moment σ hW hb _ (absn_finrank_sub_le E X hX A) h4p1 h4pW)
    -- the outer (block) integral: gap moments
    have hgapm : ∫⁻ A, ENNReal.ofReal ((absnGap E X hX A)⁻¹ ^ (2 * p))
        ∂blockLaw σ.blocks W (1 - 2 * b) ≤ ENNReal.ofReal (Cδ ^ (2 * p)) := by
      refine (hgap σ.blocks W hW (1 - 2 * b) hc E ⟨X, hX⟩ (2 * p) h2p1 h2pW).trans ?_
      refine ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (gapMomentConstant_pos _ _ _).le ?_ (by linarith))
      cases σ
      · exact le_max_right _ _
      · exact le_max_right _ _
      · exact le_max_left _ _
      · exact le_max_left _ _
    have hF : Measurable (fun ω : LayerSample W σ =>
        ENNReal.ofReal (‖layerResolvent σ E z X ω‖ ^ p)) :=
      ENNReal.measurable_ofReal.comp ((measurable_norm_layerResolvent σ E z X).pow_const p)
    have hmom : ∫⁻ ω, ENNReal.ofReal (‖layerResolvent σ E z X ω‖ ^ p) ∂layerLaw W b σ ≤
        ENNReal.ofReal (Cfin ^ p) := by
      rw [absn_layerLaw_eq, lintegral_prod _ hF.aemeasurable]
      calc ∫⁻ A, ∫⁻ B, ENNReal.ofReal (‖layerResolvent σ E z X (A, B)‖ ^ p)
            ∂absnBondLaw W b σ ∂blockLaw σ.blocks W (1 - 2 * b)
          ≤ ∫⁻ A, ENNReal.ofReal (L ^ p / 2) *
              ENNReal.ofReal ((absnGap E X hX A)⁻¹ ^ (2 * p)) * Q
              ∂blockLaw σ.blocks W (1 - 2 * b) := by
            refine lintegral_mono_ae ?_
            filter_upwards [hgood] with A hA
            refine (hinner A hA).trans (le_of_eq ?_)
            rw [ENNReal.ofReal_mul hLp]
        _ = ENNReal.ofReal (L ^ p / 2) * (∫⁻ A, ENNReal.ofReal ((absnGap E X hX A)⁻¹ ^ (2 * p))
              ∂blockLaw σ.blocks W (1 - 2 * b)) * Q := by
            rw [lintegral_mul_const' _ _ hQtop, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal (L ^ p / 2) * ENNReal.ofReal (Cδ ^ (2 * p)) * Q := by gcongr
        _ = ENNReal.ofReal (L ^ p / 2 * Cδ ^ (2 * p) * (CK ^ (12 * p) + Cd ^ (4 * p))) := by
            rw [ENNReal.ofReal_mul (mul_nonneg hLp (Real.rpow_nonneg hCδ0.le _)),
              ENNReal.ofReal_mul hLp, ENNReal.ofReal_add (Real.rpow_nonneg hCK.le _)
                (Real.rpow_nonneg hCd.le _)]
        _ ≤ ENNReal.ofReal (Cfin ^ p) :=
            ENNReal.ofReal_le_ofReal (absn_const_le hL.le hCδ0.le hCK.le hCd.le hp0.le)
    -- the `L^p` norm
    have hmeasG : AEStronglyMeasurable (fun ω => ‖layerResolvent σ E z X ω‖) (layerLaw W b σ) :=
      (measurable_norm_layerResolvent σ E z X).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top hmeasG,
      ENNReal.toReal_ofReal hp0.le]
    have hint : ∫⁻ ω, ‖‖layerResolvent σ E z X ω‖‖ₑ ^ p ∂layerLaw W b σ =
        ∫⁻ ω, ENNReal.ofReal (‖layerResolvent σ E z X ω‖ ^ p) ∂layerLaw W b σ := by
      refine lintegral_congr fun ω => ?_
      rw [Real.enorm_eq_ofReal (norm_nonneg _),
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
    rw [hint]
    calc (∫⁻ ω, ENNReal.ofReal (‖layerResolvent σ E z X ω‖ ^ p) ∂layerLaw W b σ) ^ (1 / p)
        ≤ (ENNReal.ofReal (Cfin ^ p)) ^ (1 / p) := ENNReal.rpow_le_rpow hmom (by positivity)
      _ = ENNReal.ofReal Cfin := by
          rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hC0.le _) (by positivity), one_div,
            Real.rpow_rpow_inv hC0.le hp0.ne']

end BlockBand.Layers
