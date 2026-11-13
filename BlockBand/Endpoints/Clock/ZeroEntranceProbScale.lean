module

public import BlockBand.Endpoints.Clock.ZeroEntranceProbDefs
public import BlockBand.Layers.LayerMeasurability
public import BlockBand.Layers.GinibreTails
public import BlockBand.Layers.PathGrowth
public import BlockBand.Endpoints.Clock.CavityMeanStability

/-!
# The zero-entrance lemma: one-layer inputs uniform in `b` by rescaling the Gaussians

We couple the blocks as `A = √c A⁽⁰⁾` and `B = √b B⁽⁰⁾` to obtain the cavity-mean lemma (clauses
(ii)–(iii), `k = 0`) and the Gaussian absorption lemma (one physical block and one port) uniformly
for `b` in a compact set. `CavityMeanStatement` and `GaussianAbsorptionContract` are stated with `b`
fixed first (constants depending on `b, η₀, M`); here a single base `b₀ = 1/4` serves the whole
compact set `κ ≤ b`, `κ ≤ 1 - 2b`.

## The coupling

With `c = 1 - 2b`, `c₀ = 1 - 2b₀`, `s = √(c/c₀)`, `t = √(b/b₀)`, `k = t²/s`:
* `layerLaw_map_scale`: `(A, B) ↦ (sA, tB)` maps `layerLaw W b₀ σ` onto `layerLaw W b σ`
  (`gueMeasure_map_smul`, `ginibreMeasure_map_smul`; every shape `σ`);
* `freshSchur_scale`, `cavityHplus_scale`: `X₊(sA, tB; e, X) = k X₊(A, B; e/s, s⁻¹X)`, hence
  `h₊(z')(sA, tB; e, X) = k⁻¹ h₊(z'/k)(A, B; e/s, s⁻¹X)`;
* `cavityU_scale`: the unique solution of the cavity equations transforms as
  `u(X, b, e, z') = k⁻¹ u(s⁻¹X, b₀, e/s, z'/k)` (`v = v₀/s`, `u = u₀/k`; uniqueness from
  `cavityMatrix_existsUnique`);
* `layerMatrix_scale`: `𝒢_b⁻¹(sA, tB; E, z, X) = Δ 𝒢_{b₀}⁻¹(A, B; E/s, z/k, s⁻¹X) Δ`,
  `Δ = diag(√s, t/√s)`, so `‖𝒢_b‖ ≤ ‖Δ⁻¹‖² ‖𝒢_{b₀}‖`.
On the compact set, `2κ ≤ k ≤ 2/κ` and `‖Δ⁻¹‖² ≤ κ⁻¹` (`scale_facts`), so the base contracts are
used on the domain `Im ≥ η₀κ/2`, `|·| ≤ M/(2κ)`.

## Results

* `cavityLayerUniform_of : CavityMeanStatement → CavityLayerUniform` (the `k = 0` mean bound
  `C/W²` and fluctuation `C√p/W`, `2 ≤ p ≤ a₀W`, uniform for `b` in the compact set, all
  Hermitian `X`, all `e`, `Im z' ≥ η₀`, `|z'| ≤ M`, `W ≥ 1`);
* `absorptionUniform_of : GaussianAbsorptionContract → AbsorptionUniform` (one block, one port:
  a.s. invertibility and `(E‖𝒢‖^p)^{1/p} ≤ C`, `1 ≤ p ≤ ε₁W`, uniform for `b` in the compact set).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Matrix.Norms.L2Operator

namespace ZeroEntranceScale

/-!
## 1. The scaled fresh layer
-/

/-- `(A, B) ↦ (s A, t B)` on a layer sample. -/
def scaleLayer {W : ℕ} {σ : LayerShape} (s t : ℝ) (ω : LayerSample W σ) : LayerSample W σ :=
  (fun j => (s : ℂ) • ω.1 j, fun j k => (t : ℂ) • ω.2 j k)

theorem measurable_smul_matrix {m n : Type*} (c : ℂ) :
    Measurable (fun A : Matrix m n ℂ => c • A) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun k => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact measurable_const.mul ((measurable_pi_apply k).comp (measurable_pi_apply i))

theorem measurable_scaleLayer {W : ℕ} {σ : LayerShape} (s t : ℝ) :
    Measurable (scaleLayer (W := W) (σ := σ) s t) := by
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_iff.mpr fun j =>
      (measurable_smul_matrix _).comp ((measurable_pi_apply j).comp measurable_fst)
  · exact measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun k =>
      (measurable_smul_matrix _).comp
        ((measurable_pi_apply k).comp ((measurable_pi_apply j).comp measurable_snd))

theorem scaleLayer_scaleLayer {W : ℕ} {σ : LayerShape} (s t s' t' : ℝ) (ω : LayerSample W σ) :
    scaleLayer s t (scaleLayer s' t' ω) = scaleLayer (s * s') (t * t') ω := by
  simp only [scaleLayer, smul_smul, Complex.ofReal_mul]

theorem scaleLayer_one {W : ℕ} {σ : LayerShape} (ω : LayerSample W σ) :
    scaleLayer 1 1 ω = ω := by
  simp [scaleLayer]

/-- The scaling as a measurable equivalence (`s, t ≠ 0`). -/
def scaleEquiv (W : ℕ) (σ : LayerShape) {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) :
    LayerSample W σ ≃ᵐ LayerSample W σ where
  toFun := scaleLayer s t
  invFun := scaleLayer s⁻¹ t⁻¹
  left_inv ω := by
    rw [scaleLayer_scaleLayer, inv_mul_cancel₀ hs, inv_mul_cancel₀ ht, scaleLayer_one]
  right_inv ω := by
    rw [scaleLayer_scaleLayer, mul_inv_cancel₀ hs, mul_inv_cancel₀ ht, scaleLayer_one]
  measurable_toFun := measurable_scaleLayer s t
  measurable_invFun := measurable_scaleLayer s⁻¹ t⁻¹

/-!
## 2. The law of the scaled layer
-/

open BlockBand.Internal.Contracts.CoareaPalm in
theorem measurable_gueSample {ι : Type*} (t : ℝ≥0) :
    Measurable (gueSample (ι := ι) t) := by
  refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun c => ?_
  simp only [gueSample, Matrix.of_apply]
  exact measurable_const.mul ((measurable_pi_apply _).add
    (continuous_star.measurable.comp (measurable_pi_apply _)))

open BlockBand.Internal.Contracts.CoareaPalm in
/-- `s • GUE(t) = GUE(t')` when `√(t'/2) = s √(t/2)`. -/
theorem gueMeasure_map_smul {ι : Type*} [Fintype ι] (t t' : ℝ≥0) (s : ℝ)
    (h : Real.sqrt ((t' : ℝ) / 2) = s * Real.sqrt ((t : ℝ) / 2)) :
    (gueMeasure ι t).map (fun A => (s : ℂ) • A) = gueMeasure ι t' := by
  unfold gueMeasure
  rw [Measure.map_map (measurable_smul_matrix _) (measurable_gueSample t)]
  congr 1
  funext X
  ext a c
  simp only [Function.comp_apply, gueSample, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, h,
    Complex.ofReal_mul]
  ring

theorem measurable_ginibreAssemble' {ι κ : Type*} :
    Measurable (fun r : ι × κ × Fin 2 → ℝ =>
      (Matrix.of fun x y => (r (x, y, 0) : ℂ) + (r (x, y, 1) : ℂ) * Complex.I :
        Matrix ι κ ℂ)) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  simp only [Matrix.of_apply]
  exact (Complex.measurable_ofReal.comp (measurable_pi_apply _)).add
    ((Complex.measurable_ofReal.comp (measurable_pi_apply _)).mul measurable_const)

/-- `τ • Gin(t) = Gin(τ² t)`. -/
theorem ginibreMeasure_map_smul {ι κ : Type*} [Fintype ι] [Fintype κ] (t t' : ℝ≥0) (τ : ℝ)
    (h : τ ^ 2 * (t : ℝ) = t') :
    (ginibreMeasure ι κ t).map (fun B => (τ : ℂ) • B) = ginibreMeasure ι κ t' := by
  unfold ginibreMeasure
  rw [Measure.map_map (measurable_smul_matrix _) measurable_ginibreAssemble']
  have hcomp : ((fun B : Matrix ι κ ℂ => (τ : ℂ) • B) ∘
      (fun r : ι × κ × Fin 2 → ℝ =>
        (Matrix.of fun x y => (r (x, y, 0) : ℂ) + (r (x, y, 1) : ℂ) * Complex.I :
          Matrix ι κ ℂ))) =
      (fun r : ι × κ × Fin 2 → ℝ =>
        (Matrix.of fun x y => (r (x, y, 0) : ℂ) + (r (x, y, 1) : ℂ) * Complex.I :
          Matrix ι κ ℂ)) ∘ (fun r i => τ * r i) := by
    funext r
    ext x y
    simp only [Function.comp_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
      Complex.ofReal_mul]
    ring
  have hmτ : Measurable (fun r : ι × κ × Fin 2 → ℝ => fun i => τ * r i) :=
    measurable_pi_iff.mpr fun i => (measurable_const (a := τ)).mul (measurable_pi_apply i)
  rw [hcomp, ← Measure.map_map measurable_ginibreAssemble' hmτ]
  congr 1
  rw [Measure.pi_map_pi (fun _ => (measurable_const_mul τ).aemeasurable)]
  congr 1
  funext i
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_div, ← h]
  push_cast
  ring

instance isFiniteMeasure_ginibreMeasure {ι κ : Type*} [Fintype ι] [Fintype κ] (t : ℝ≥0) :
    IsFiniteMeasure (ginibreMeasure ι κ t) := by
  unfold ginibreMeasure; infer_instance

open BlockBand.Internal.Contracts.CoareaPalm in
instance isFiniteMeasure_gueMeasure' (W : ℕ) (t : ℝ≥0) :
    IsFiniteMeasure (gueMeasure (Fin W) t) := by
  have := BlockBand.Layers.isProbabilityMeasure_gueMeasure W t
  infer_instance

open BlockBand.Internal.Contracts.CoareaPalm in
/-- **Law of the rescaled layer**: with `s = √((1-2b)/(1-2b₀))`, `t = √(b/b₀)`,
`(A, B) ↦ (s A, t B)` maps `layerLaw W b₀ σ` to `layerLaw W b σ`. -/
theorem layerLaw_map_scale (W : ℕ) (σ : LayerShape) {b₀ b : ℝ} (hb₀ : 0 < b₀)
    (hc₀ : 0 < 1 - 2 * b₀) (hb : 0 ≤ b) (hc : 0 ≤ 1 - 2 * b) :
    (layerLaw W b₀ σ).map
        (scaleLayer (Real.sqrt ((1 - 2 * b) / (1 - 2 * b₀))) (Real.sqrt (b / b₀))) =
      layerLaw W b σ := by
  set s := Real.sqrt ((1 - 2 * b) / (1 - 2 * b₀))
  set t := Real.sqrt (b / b₀)
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hgue : (gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b₀) / W))).map
      (fun A => (s : ℂ) • A) = gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W)) := by
    refine gueMeasure_map_smul _ _ s ?_
    rw [Real.coe_toNNReal _ (div_nonneg hc hW), Real.coe_toNNReal _ (div_nonneg hc₀.le hW),
      ← Real.sqrt_mul (div_nonneg hc hc₀.le)]
    congr 1
    field_simp
  have hgin : (ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b₀ / W))).map
      (fun B => (t : ℂ) • B) = ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)) := by
    refine ginibreMeasure_map_smul _ _ t ?_
    rw [Real.coe_toNNReal _ (div_nonneg hb hW), Real.coe_toNNReal _ (div_nonneg hb₀.le hW),
      Real.sq_sqrt (div_nonneg hb hb₀.le)]
    field_simp
  have hsplit : scaleLayer (W := W) (σ := σ) s t =
      Prod.map (fun (A : Fin σ.blocks → Matrix (Fin W) (Fin W) ℂ) j => (s : ℂ) • A j)
        (fun (B : Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ) j k =>
          (t : ℂ) • B j k) := rfl
  have hmA : Measurable (fun (A : Fin σ.blocks → Matrix (Fin W) (Fin W) ℂ) j =>
      (s : ℂ) • A j) :=
    measurable_pi_iff.mpr fun j => (measurable_smul_matrix _).comp (measurable_pi_apply j)
  have hmB : Measurable (fun (B : Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ) j k =>
      (t : ℂ) • B j k) :=
    measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun k =>
      (measurable_smul_matrix _).comp ((measurable_pi_apply k).comp (measurable_pi_apply j))
  unfold layerLaw
  rw [hsplit, ← Measure.map_prod_map _ _ hmA hmB]
  congr 1
  · rw [Measure.pi_map_pi (fun _ => (measurable_smul_matrix _).aemeasurable)]
    congr 1
    funext j
    exact hgue
  · have hk : (fun (B : Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ) j k =>
        (t : ℂ) • B j k) = fun B j => (fun Bj k => (t : ℂ) • Bj k) (B j) := rfl
    rw [hk, Measure.pi_map_pi
      (f := fun _ (Bj : Fin σ.ports → Matrix (Fin W) (Fin W) ℂ) k => (t : ℂ) • Bj k)
      (fun _ => (measurable_pi_iff.mpr fun k =>
      (measurable_smul_matrix _).comp (measurable_pi_apply k)).aemeasurable)]
    congr 1
    funext j
    rw [Measure.pi_map_pi (fun _ => (measurable_smul_matrix _).aemeasurable)]
    congr 1
    funext k
    exact hgin

/-!
## 3. Scaling algebra
-/

theorem blockDiag_smul {k W : ℕ} (c : ℂ) (A : Fin k → Matrix (Fin W) (Fin W) ℂ) :
    Internal.Contracts.Layers.blockDiag (fun j => c • A j) =
      c • Internal.Contracts.Layers.blockDiag A := by
  ext x y
  simp only [Internal.Contracts.Layers.blockDiag, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem bondMatrix_smul {W : ℕ} (σ : LayerShape) (c : ℂ)
    (B : Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ) :
    bondMatrix σ (fun j k => c • B j k) = c • bondMatrix σ B := by
  ext x y
  simp only [bondMatrix, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- `(k M)⁻¹ = k⁻¹ M⁻¹` for `k ≠ 0` (both sides vanish for singular `M`). -/
theorem inv_smul_of_ne {n : Type*} [Fintype n] [DecidableEq n] {k : ℂ} (hk : k ≠ 0)
    (M : Matrix n n ℂ) : (k • M)⁻¹ = k⁻¹ • M⁻¹ := by
  by_cases h : IsUnit M.det
  · exact Matrix.inv_smul' M (Units.mk0 k hk) h
  · have h' : ¬ IsUnit (k • M).det := by
      rw [Matrix.det_smul, isUnit_iff_ne_zero]
      rw [isUnit_iff_ne_zero, not_not] at h
      simp [h]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h', Matrix.nonsing_inv_apply_not_isUnit _ h,
      smul_zero]

theorem isHermitian_real_smul {n : Type*} {X : Matrix n n ℂ} (hX : X.IsHermitian) (r : ℝ) :
    ((r : ℂ) • X).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hX.eq, Complex.star_def, Complex.conj_ofReal]

/-- `X₊` of the rescaled layer: `layerSchur σ E X (sA, tB) = (t²/s) layerSchur σ (E/s) (s⁻¹X) (A, B)`. -/
theorem layerSchur_scale {W : ℕ} (σ : LayerShape) (E : ℝ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) {s : ℝ} (hs : s ≠ 0) (t : ℝ)
    (ω : LayerSample W σ) :
    layerSchur σ E X (scaleLayer s t ω) =
      ((t ^ 2 / s : ℝ) : ℂ) • layerSchur σ (E / s) (((s⁻¹ : ℝ) : ℂ) • X) ω := by
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  unfold layerSchur scaleLayer
  simp only
  rw [blockDiag_smul, bondMatrix_smul]
  have key : (s : ℂ) • blockDiag ω.1 - (E : ℂ) • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X =
      (s : ℂ) • (blockDiag ω.1 - ((E / s : ℝ) : ℂ) • 1 - ((s⁻¹ : ℝ) : ℂ) • X) := by
    rw [smul_sub, smul_sub, smul_smul, smul_smul]
    congr 2
    · congr 1; push_cast; field_simp
    · push_cast; rw [mul_inv_cancel₀ hsC, one_smul]
  rw [key, inv_smul_of_ne hsC, Matrix.conjTranspose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  rw [Complex.star_def, Complex.conj_ofReal]
  push_cast
  field_simp

/-- `X₊ = B*(A - e - X)⁻¹B` of the rescaled layer. -/
theorem freshSchur_scale {W : ℕ} (e : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) {s : ℝ} (hs : s ≠ 0)
    (t : ℝ) (ω : LayerSample W .oneBlockOnePort) :
    Internal.Contracts.TransmissionStatements.freshSchur e X (scaleLayer s t ω) =
      ((t ^ 2 / s : ℝ) : ℂ) •
        Internal.Contracts.TransmissionStatements.freshSchur (e / s) (((s⁻¹ : ℝ) : ℂ) • X) ω := by
  have hl : (Matrix.of fun (u v : Fin 1 × Fin W) => ((((s⁻¹ : ℝ) : ℂ) • X) u.2 v.2)) =
      ((s⁻¹ : ℝ) : ℂ) • Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2 := by
    ext u v; simp
  ext x y
  unfold Internal.Contracts.TransmissionStatements.freshSchur
  rw [Matrix.of_apply, Matrix.smul_apply, Matrix.of_apply, hl, layerSchur_scale _ _ _ hs]
  rfl

/-- `W⁻¹ Tr (z - kY)⁻¹ = k⁻¹ W⁻¹ Tr (z/k - Y)⁻¹`. -/
theorem normalizedResolventTrace_smul {W : ℕ} (Y : Matrix (Fin W) (Fin W) ℂ) {k : ℂ}
    (hk : k ≠ 0) (z : ℂ) :
    normalizedResolventTrace (k • Y) z = k⁻¹ * normalizedResolventTrace Y (z / k) := by
  unfold normalizedResolventTrace
  have : z • (1 : Matrix (Fin W) (Fin W) ℂ) - k • Y = k • ((z / k) • 1 - Y) := by
    rw [smul_sub, smul_smul, mul_div_cancel₀ _ hk]
  rw [this, inv_smul_of_ne hk, Matrix.trace_smul, smul_eq_mul]
  ring

/-- `h₊` of the rescaled layer. -/
theorem cavityHplus_scale {W : ℕ} (e : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) {s t : ℝ} (hs : s ≠ 0)
    (ht : t ≠ 0) (z' : ℂ) (ω : LayerSample W .oneBlockOnePort) :
    cavityHplus e X z' (scaleLayer s t ω) =
      ((t ^ 2 / s : ℝ) : ℂ)⁻¹ *
        cavityHplus (e / s) (((s⁻¹ : ℝ) : ℂ) • X) (z' / ((t ^ 2 / s : ℝ) : ℂ)) ω := by
  have hk : ((t ^ 2 / s : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  unfold cavityHplus
  rw [freshSchur_scale e X hs t ω, normalizedResolventTrace_smul _ hk]

/-- The cavity solution of the rescaled problem: with `1 - 2b = s²(1 - 2b₀)` and `b = s k b₀`,
`u(X, b, e, z') = k⁻¹ u(s⁻¹X, b₀, e/s, z'/k)` (uniqueness, `cavityMatrix_existsUnique`). -/
theorem cavityU_scale {W : ℕ} (hW : 0 < W) {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian)
    {b₀ b : ℝ} (hb₀ : 0 < b₀) (hb₀' : b₀ < 1 / 2) (hb : 0 < b) (hb' : b < 1 / 2) {s k : ℝ}
    (hs : 0 < s) (hk : 0 < k) (hc : 1 - 2 * b = s ^ 2 * (1 - 2 * b₀)) (hbb : b = s * k * b₀)
    (e : ℝ) {z' : ℂ} (hz : 0 < z'.im) :
    cavityU X b e z' = (k : ℂ)⁻¹ * cavityU (((s⁻¹ : ℝ) : ℂ) • X) b₀ (e / s) (z' / k) := by
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  have hX' := isHermitian_real_smul hX s⁻¹
  have hz' : 0 < (z' / k).im := by rw [Complex.div_ofReal_im]; positivity
  obtain ⟨h1, h2, h3, h4⟩ := cavitySol_spec hW hX' hb₀ hb₀' (e / s) hz'
  set v₀ := cavityV (((s⁻¹ : ℝ) : ℂ) • X) b₀ (e / s) (z' / k)
  set u₀ := cavityU (((s⁻¹ : ℝ) : ℂ) • X) b₀ (e / s) (z' / k)
  have hcC : ((1 - 2 * b : ℝ) : ℂ) = (s : ℂ) ^ 2 * ((1 - 2 * b₀ : ℝ) : ℂ) := by
    rw [hc]; push_cast; ring
  have hbC : (b : ℂ) = s * k * b₀ := by rw [hbb]; push_cast; ring
  have hsinv : ((s⁻¹ : ℝ) : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; positivity
  have hsol : IsCavityMatrixSolution X b (1 - 2 * b) e z' (v₀ / s) (u₀ / k) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [normalizedResolventTrace_smul _ hsinv] at h1
      have harg : (-((e / s : ℝ) : ℂ) - ((1 - 2 * b₀ : ℝ) : ℂ) * v₀ - (b₀ : ℂ) * u₀) /
          ((s⁻¹ : ℝ) : ℂ) = -(e : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * (v₀ / s) - (b : ℂ) * (u₀ / k) := by
        rw [hcC, hbC]
        push_cast
        field_simp
      rw [harg, Complex.ofReal_inv, inv_inv] at h1
      conv_lhs => rw [h1]
      field_simp
    · rw [h2, hbC]
      have : z' - (s : ℂ) * k * b₀ * (v₀ / s) = (k : ℂ) * (z' / k - b₀ * v₀) := by
        field_simp
      rw [this, mul_inv]
      ring
    · rw [Complex.div_ofReal_im]; exact div_neg_of_neg_of_pos h3 hs
    · rw [Complex.div_ofReal_im]; exact div_neg_of_neg_of_pos h4 hk
  have hc' : 0 < 1 - 2 * b := by linarith
  obtain ⟨vu, -, huniq⟩ := cavityMatrix_existsUnique (e := e) hW hX hb hc' hz
  have hA := (huniq _ _ (cavitySol_spec hW hX hb hb' e hz)).2
  have hB := (huniq _ _ hsol).2
  rw [hA, ← hB]
  ring

/-!
## 4. The base parameter `b₀ = 1/4` and the scale bounds
-/

/-- Scale facts for `b₀ = 1/4`: with `s = √((1-2b)/(1/2))`, `t = √(4b)`, `k = t²/s`, on the compact
set `κ ≤ b`, `κ ≤ 1 - 2b`: `s, t > 0`, `2κ ≤ k ≤ 2/κ`, `1 - 2b = s²(1 - 2b₀)`, `b = s k b₀`. -/
theorem scale_facts {κ b : ℝ} (hκ : 0 < κ) (hb : κ ≤ b) (hc : κ ≤ 1 - 2 * b) :
    0 < Real.sqrt ((1 - 2 * b) / (1 - 2 * (1 / 4))) ∧ 0 < Real.sqrt (b / (1 / 4)) ∧
      2 * κ ≤ Real.sqrt (b / (1 / 4)) ^ 2 / Real.sqrt ((1 - 2 * b) / (1 - 2 * (1 / 4))) ∧
      Real.sqrt (b / (1 / 4)) ^ 2 / Real.sqrt ((1 - 2 * b) / (1 - 2 * (1 / 4))) ≤ 2 / κ ∧
      1 - 2 * b = Real.sqrt ((1 - 2 * b) / (1 - 2 * (1 / 4))) ^ 2 * (1 - 2 * (1 / 4)) ∧
      b = Real.sqrt ((1 - 2 * b) / (1 - 2 * (1 / 4))) *
        (Real.sqrt (b / (1 / 4)) ^ 2 / Real.sqrt ((1 - 2 * b) / (1 - 2 * (1 / 4)))) * (1 / 4) := by
  set s := Real.sqrt ((1 - 2 * b) / (1 - 2 * (1 / 4)))
  set t := Real.sqrt (b / (1 / 4))
  have hb0 : 0 < b := hκ.trans_le hb
  have hc0 : 0 < 1 - 2 * b := hκ.trans_le hc
  have hκ3 : κ ≤ 1 / 3 := by linarith
  have hs2 : s ^ 2 = 2 * (1 - 2 * b) := by
    rw [Real.sq_sqrt (by positivity)]; ring
  have ht2 : t ^ 2 = 4 * b := by
    rw [Real.sq_sqrt (by positivity)]; ring
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have ht : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have hsκ : κ ≤ s := by nlinarith
  have hs2' : s ≤ 2 := by nlinarith
  refine ⟨hs, ht, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hs, ht2]; nlinarith
  · rw [div_le_div_iff₀ hs hκ, ht2]; nlinarith
  · rw [hs2]; ring
  · rw [mul_div_cancel₀ _ hs.ne', ht2]; ring

/-!
## 5. the cavity-mean lemma, `k = 0`, uniformly in `b`
-/

/-- **The cavity-mean lemma (ii)–(iii), uniform for `b` in the compact set**, from `CavityMeanStatement` at the single base `b₀ = 1/4`. -/
theorem cavityLayerUniform_aux (hQ : CavityMeanStatement) : CavityLayerUniform := by
  intro κ hκ η₀ M hη
  obtain ⟨⟨a₀, C₀, ha₀, hC₀, hQb⟩, -⟩ :=
    hQ (1 / 4) (by norm_num) (by norm_num) (η₀ * κ / 2) (M / (2 * κ)) (by positivity)
  refine ⟨a₀, C₀ / (2 * κ), ha₀, by positivity, ?_⟩
  intro b hb hcb W hW X hX e z' hz hzM
  obtain ⟨hs, ht, hk1, hk2, hcs, hbs⟩ := scale_facts hκ hb hcb
  set s := Real.sqrt ((1 - 2 * b) / (1 - 2 * (1 / 4)))
  set t := Real.sqrt (b / (1 / 4))
  set k := t ^ 2 / s with hkdef
  have hk : 0 < k := by positivity
  have hb0 : 0 < b := hκ.trans_le hb
  have hb1 : b < 1 / 2 := by linarith
  have hz0 : 0 < z'.im := hη.trans_le hz
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hzM
  set X' := ((s⁻¹ : ℝ) : ℂ) • X
  have hX' : X'.IsHermitian := isHermitian_real_smul hX s⁻¹
  have hz' : η₀ * κ / 2 ≤ (z' / (k : ℂ)).im := by
    rw [Complex.div_ofReal_im, le_div_iff₀ hk]
    have : k * κ ≤ 2 := by rwa [le_div_iff₀ hκ] at hk2
    nlinarith
  have hzM' : ‖z' / (k : ℂ)‖ ≤ M / (2 * κ) := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hk.le, div_le_div_iff₀ hk (by positivity)]
    nlinarith
  obtain ⟨-, -, hmean, hfl⟩ := hQb W hW X' hX' (e / s) (z' / k) hz' hzM'
  have hlaw := layerLaw_map_scale W .oneBlockOnePort (b₀ := 1 / 4) (b := b) (by norm_num)
    (by norm_num) hb0.le (hκ.trans_le hcb).le
  set μ₀ := layerLaw W (1 / 4) .oneBlockOnePort
  have hkinv : k⁻¹ ≤ 1 / (2 * κ) := by
    rw [one_div]; exact inv_anti₀ (by positivity) hk1
  -- the integral
  have hI : ∫ ω, cavityHplus e X z' ω ∂layerLaw W b .oneBlockOnePort =
      (k : ℂ)⁻¹ * ∫ ω, cavityHplus (e / s) X' (z' / k) ω ∂μ₀ := by
    rw [← hlaw, integral_map (measurable_scaleLayer s t).aemeasurable
      (CavityMeanProb.measurable_cavityHplus e X z').aestronglyMeasurable]
    simp_rw [cavityHplus_scale e X hs.ne' ht.ne' z']
    rw [integral_const_mul]
  have hU := cavityU_scale hW hX (b₀ := 1 / 4) (by norm_num) (by norm_num) hb0 hb1 hs hk hcs hbs
    e hz0
  refine ⟨?_, ?_⟩
  · rw [hI, hU, ← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hk.le]
    calc k⁻¹ * ‖(∫ ω, cavityHplus (e / s) X' (z' / k) ω ∂μ₀) -
          cavityU X' (1 / 4) (e / s) (z' / k)‖ ≤ (1 / (2 * κ)) * (C₀ / (W : ℝ) ^ 2) :=
          mul_le_mul hkinv hmean (norm_nonneg _) (by positivity)
      _ = C₀ / (2 * κ) / (W : ℝ) ^ 2 := by ring
  · intro p hp hpW
    rw [hI, ← hlaw, eLpNorm_map_measure
      ((CavityMeanProb.measurable_cavityHplus e X z').sub_const _).aestronglyMeasurable
      (measurable_scaleLayer s t).aemeasurable]
    have hfun : ((fun ω => cavityHplus e X z' ω -
        (k : ℂ)⁻¹ * ∫ ω, cavityHplus (e / s) X' (z' / k) ω ∂μ₀) ∘ scaleLayer s t) =
        (k : ℂ)⁻¹ • fun ω => cavityHplus (e / s) X' (z' / k) ω -
          ∫ ω', cavityHplus (e / s) X' (z' / k) ω' ∂μ₀ := by
      funext ω
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
      rw [cavityHplus_scale e X hs.ne' ht.ne' z']
      ring
    rw [hfun, eLpNorm_const_smul]
    have hn : ‖(k : ℂ)⁻¹‖ₑ = ENNReal.ofReal k⁻¹ := by
      rw [← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_of_nonneg hk.le]
    rw [hn]
    calc ENNReal.ofReal k⁻¹ * eLpNorm (fun ω => cavityHplus (e / s) X' (z' / k) ω -
          ∫ ω', cavityHplus (e / s) X' (z' / k) ω' ∂μ₀) (ENNReal.ofReal p) μ₀
        ≤ ENNReal.ofReal (1 / (2 * κ)) * ENNReal.ofReal (C₀ * Real.sqrt p / W) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hkinv) (hfl p hp hpW)
      _ = ENNReal.ofReal (C₀ / (2 * κ) * Real.sqrt p / W) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring

/-!
## 6. The Gaussian absorption lemma, one block and one port, uniformly in `b`
-/

/-- `Δ = diag(r on the physical sites, α on the port sites)`. -/
def scaleDiag {W : ℕ} {σ : LayerShape} (r α : ℂ) : Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  Matrix.diagonal (Sum.elim (fun _ => r) (fun _ => α))

theorem scaleDiag_eq {W : ℕ} {σ : LayerShape} (r α : ℂ) :
    scaleDiag (W := W) (σ := σ) r α = Matrix.fromBlocks (r • 1) 0 0 (α • 1) := by
  rw [scaleDiag, ← Matrix.fromBlocks_diagonal, Matrix.smul_one_eq_diagonal,
    Matrix.smul_one_eq_diagonal]

theorem scaleDiag_mul {W : ℕ} {σ : LayerShape} (r α r' α' : ℂ) :
    scaleDiag (W := W) (σ := σ) r α * scaleDiag r' α' = scaleDiag (r * r') (α * α') := by
  rw [scaleDiag, scaleDiag, scaleDiag, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  cases i <;> rfl

theorem scaleDiag_one {W : ℕ} {σ : LayerShape} : scaleDiag (W := W) (σ := σ) 1 1 = 1 := by
  rw [scaleDiag, ← Matrix.diagonal_one]
  congr 1
  funext i
  cases i <;> rfl

theorem norm_scaleDiag_le {W : ℕ} {σ : LayerShape} (r α : ℂ) {K : ℝ} (hr : ‖r‖ ≤ K)
    (hα : ‖α‖ ≤ K) : ‖scaleDiag (W := W) (σ := σ) r α‖ ≤ K := by
  rw [scaleDiag, Matrix.l2_opNorm_diagonal]
  refine pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans hr) |>.mpr fun i => ?_
  cases i <;> simpa

/-- The augmented layer matrix of the rescaled layer:
`layerMatrix σ E z X (sA, tB) = Δ · layerMatrix σ (E/s) (z/k) (s⁻¹X) (A, B) · Δ`, `Δ = diag(√s, t/√s)`,
`k = t²/s`. -/
theorem layerMatrix_scale {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (ω : LayerSample W σ) :
    layerMatrix σ E z X (scaleLayer s t ω) =
      scaleDiag (Real.sqrt s : ℂ) ((t / Real.sqrt s : ℝ) : ℂ) *
        layerMatrix σ (E / s) (z / ((t ^ 2 / s : ℝ) : ℂ)) (((s⁻¹ : ℝ) : ℂ) • X) ω *
        scaleDiag (Real.sqrt s : ℂ) ((t / Real.sqrt s : ℝ) : ℂ) := by
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hrC : ((Real.sqrt s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hrr : ((Real.sqrt s : ℝ) : ℂ) * (Real.sqrt s : ℂ) = s := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs.le]
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  unfold layerMatrix scaleLayer
  simp only
  rw [blockDiag_smul, bondMatrix_smul, scaleDiag_eq, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal]
  simp only [smul_zero, add_zero]
  have h2 : ((Real.sqrt s : ℝ) : ℂ) ^ 2 = s := by rw [sq, hrr]
  congr 1
  · rw [hrr]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    field_simp
  · rw [smul_smul]; congr 1; push_cast; field_simp
  · congr 1; push_cast; field_simp
  · congr 1
    push_cast
    field_simp
    rw [h2]

/-- For the one-block one-port layer, **uniform for `b` in the compact set**, from
`GaussianAbsorptionContract` at the single base `b₀ = 1/4`:
`‖𝒢_b‖ ≤ ‖Δ⁻¹‖² ‖𝒢_{b₀}‖ ≤ κ⁻¹ ‖𝒢_{b₀}‖`.
-/
theorem absorptionUniform_aux (habs : GaussianAbsorptionContract) : AbsorptionUniform := by
  intro κ hκ η₀ M hη
  obtain ⟨ε₁, C₀, hε, hC₀, hA⟩ :=
    habs (1 / 4) (by norm_num) (by norm_num) (η₀ * κ / 2) (M / (2 * κ)) (by positivity)
  refine ⟨ε₁, C₀ / κ, hε, by positivity, ?_⟩
  intro b hb hcb W hW X hX E z hz hzM
  obtain ⟨hs, ht, hk1, hk2, -, -⟩ := scale_facts hκ hb hcb
  set s := Real.sqrt ((1 - 2 * b) / (1 - 2 * (1 / 4)))
  set t := Real.sqrt (b / (1 / 4))
  set k := t ^ 2 / s with hkdef
  have hk : 0 < k := by positivity
  have hb0 : 0 < b := hκ.trans_le hb
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hzM
  have hs2 : s ^ 2 = 2 * (1 - 2 * b) := by
    rw [Real.sq_sqrt (by have := hκ.trans_le hcb; positivity)]; ring
  have ht2 : t ^ 2 = 4 * b := by rw [Real.sq_sqrt (by positivity)]; ring
  have hsκ : κ ≤ s := by
    have : κ ≤ 1 / 3 := by linarith
    nlinarith
  set X' := ((s⁻¹ : ℝ) : ℂ) • X
  have hX' : X'.IsHermitian := isHermitian_real_smul hX s⁻¹
  have hz' : η₀ * κ / 2 ≤ (z / (k : ℂ)).im := by
    rw [Complex.div_ofReal_im, le_div_iff₀ hk]
    have : k * κ ≤ 2 := by rwa [le_div_iff₀ hκ] at hk2
    nlinarith
  have hzM' : ‖z / (k : ℂ)‖ ≤ M / (2 * κ) := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hk.le, div_le_div_iff₀ hk (by positivity)]
    nlinarith
  obtain ⟨hinv, hmom⟩ := hA W hW .oneBlockOnePort X' hX' (E / s) (z / k) hz' hzM'
  have hlaw := layerLaw_map_scale W .oneBlockOnePort (b₀ := 1 / 4) (b := b) (by norm_num)
    (by norm_num) hb0.le (hκ.trans_le hcb).le
  have hemb : MeasurableEmbedding (scaleLayer (W := W) (σ := .oneBlockOnePort) s t) :=
    (scaleEquiv W .oneBlockOnePort hs.ne' ht.ne').measurableEmbedding
  -- the diagonal `Δ` and its inverse
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  set Δ : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
    scaleDiag (Real.sqrt s : ℂ) ((t / Real.sqrt s : ℝ) : ℂ)
  set Δ' : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
    scaleDiag ((Real.sqrt s)⁻¹ : ℝ) (((t / Real.sqrt s)⁻¹ : ℝ) : ℂ)
  have hΔ'Δ : Δ' * Δ = 1 := by
    rw [scaleDiag_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hr.ne', inv_mul_cancel₀ (by positivity), Complex.ofReal_one, scaleDiag_one]
  have hΔinv : Δ⁻¹ = Δ' := Matrix.inv_eq_left_inv hΔ'Δ
  have hΔunit : IsUnit Δ.det := Matrix.isUnit_det_of_left_inverse hΔ'Δ
  have hΔ'norm : ‖Δ'‖ ≤ Real.sqrt (1 / κ) := by
    refine norm_scaleDiag_le _ _ ?_ ?_
    · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), ← Real.sqrt_inv]
      exact Real.sqrt_le_sqrt (by rw [one_div]; exact inv_anti₀ hκ hsκ)
    · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), inv_div]
      rw [show Real.sqrt s / t = Real.sqrt (s / t ^ 2) by
        rw [Real.sqrt_div' _ (sq_nonneg t), Real.sqrt_sq ht.le]]
      refine Real.sqrt_le_sqrt ?_
      rw [div_le_div_iff₀ (by positivity) hκ, ht2]
      nlinarith
  have hΔ'sq : ‖Δ'‖ * ‖Δ'‖ ≤ 1 / κ := by
    have h0 := norm_nonneg Δ'
    have := mul_le_mul hΔ'norm hΔ'norm h0 (Real.sqrt_nonneg _)
    rwa [Real.mul_self_sqrt (by positivity)] at this
  refine ⟨?_, ?_⟩
  · rw [← hlaw, hemb.ae_map_iff]
    filter_upwards [hinv] with ω hω
    rw [layerMatrix_scale _ _ _ _ hs ht, Matrix.det_mul, Matrix.det_mul]
    exact (hΔunit.mul hω).mul hΔunit
  · intro p hp hpW
    rw [← hlaw, hemb.eLpNorm_map_measure]
    have hpt : ∀ ω, ‖((fun ω => ‖layerResolvent .oneBlockOnePort E z X ω‖) ∘
        scaleLayer s t) ω‖ ≤
        ‖((1 / κ : ℝ) • fun ω => ‖layerResolvent .oneBlockOnePort (E / s) (z / k) X' ω‖) ω‖ := by
      intro ω
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, norm_norm, norm_mul,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / κ)]
      rw [layerResolvent, layerMatrix_scale _ _ _ _ hs ht, Matrix.mul_inv_rev,
        Matrix.mul_inv_rev, hΔinv]
      calc ‖Δ' * ((layerMatrix .oneBlockOnePort (E / s) (z / ((t ^ 2 / s : ℝ) : ℂ)) X' ω)⁻¹ *
            Δ')‖ ≤ ‖Δ'‖ * (‖(layerMatrix .oneBlockOnePort (E / s)
              (z / ((t ^ 2 / s : ℝ) : ℂ)) X' ω)⁻¹‖ * ‖Δ'‖) :=
            (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left
              (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
        _ = (‖Δ'‖ * ‖Δ'‖) * ‖layerResolvent .oneBlockOnePort (E / s) (z / k) X' ω‖ := by
            rw [layerResolvent]; ring
        _ ≤ 1 / κ * ‖layerResolvent .oneBlockOnePort (E / s) (z / k) X' ω‖ :=
            mul_le_mul_of_nonneg_right hΔ'sq (norm_nonneg _)
    refine (eLpNorm_mono ((BlockBand.Layers.measurable_norm_layerResolvent _ _ _ _).comp
      (measurable_scaleLayer s t)).aestronglyMeasurable hpt).trans ?_
    rw [eLpNorm_const_smul]
    have hn : ‖(1 / κ : ℝ)‖ₑ = ENNReal.ofReal (1 / κ) := by
      rw [← ofReal_norm, Real.norm_of_nonneg (by positivity)]
    rw [hn]
    calc ENNReal.ofReal (1 / κ) *
          eLpNorm (fun ω => ‖layerResolvent .oneBlockOnePort (E / s) (z / k) X' ω‖)
            (ENNReal.ofReal p) (layerLaw W (1 / 4) .oneBlockOnePort)
        ≤ ENNReal.ofReal (1 / κ) * ENNReal.ofReal C₀ := mul_le_mul' le_rfl (hmom p hp hpW)
      _ = ENNReal.ofReal (C₀ / κ) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

end ZeroEntranceScale

/-- The cavity-mean clauses (ii)–(iii) uniformly in `b` (`CavityLayerUniform`), from
`CavityMeanStatement`. -/
theorem cavityLayerUniform_of (hQ : CavityMeanStatement) : CavityLayerUniform :=
  ZeroEntranceScale.cavityLayerUniform_aux hQ

/-- The Gaussian absorption lemma (one block, one port) uniformly in `b` (`AbsorptionUniform`),
from `GaussianAbsorptionContract`. -/
theorem absorptionUniform_of (habs : GaussianAbsorptionContract) : AbsorptionUniform :=
  ZeroEntranceScale.absorptionUniform_aux habs

/-!
## 7. The deterministic stability of the cavity solution, uniformly in `b`
-/

/-- `Σ p_i (ζ - x_i/s)⁻¹ = s Σ p_i (sζ - x_i)⁻¹`. -/
theorem cavityStieltjes_scale {ι : Type*} [Fintype ι] (p x : ι → ℝ) {s : ℝ} (hs : s ≠ 0)
    (ζ : ℂ) :
    cavityStieltjes p (fun i => x i / s) ζ = s * cavityStieltjes p x (s * ζ) := by
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  unfold cavityStieltjes
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ζ - ((x i / s : ℝ) : ℂ) = (s * ζ - x i) / s := by push_cast; field_simp
  rw [this, inv_div, div_eq_mul_inv]
  ring

/-- **Deterministic stability of the cavity solution, uniform for `b` in the compact
set**: `cavity_stability` at the single base `b₀ = 1/4`, transported by `v₀ = s v`, `u₀ = k u`, `x ↦ x/s`, `e ↦ e/s`, `z' ↦ z'/k`
(residuals scale by `s` and `k`). -/
theorem cavityStability_uniform {κ : ℝ} (hκ : 0 < κ) {η M astar : ℝ} (hη : 0 < η) (hM : 0 ≤ M)
    (ha : 0 < astar) : ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ, κ ≤ b → κ ≤ 1 - 2 * b →
      ∀ (ι : Type) [Fintype ι] (p x : ι → ℝ) (e : ℝ) (z' v u vbar ubar : ℂ) (ε : ℝ),
      IsCavityWeights p → η ≤ z'.im → ‖z'‖ ≤ M →
      IsCavitySolution p x b (1 - 2 * b) e z' v u → vbar.im ≤ 0 → astar ≤ ‖ubar‖ →
      η * ‖ubar‖ ^ 2 ≤ -ubar.im →
      ‖vbar - cavityStieltjes p x (-e - ((1 - 2 * b : ℝ) : ℂ) * vbar - b * ubar)‖ ≤ ε →
      ‖ubar - (z' - b * vbar)⁻¹‖ ≤ ε →
      ‖vbar - v‖ + ‖ubar - u‖ ≤ C * ε := by
  obtain ⟨C₀, hC₀, hst⟩ := cavity_stability (b := 1 / 4) (c := 1 - 2 * (1 / 4))
    (η := η * κ / 2) (M := M / (2 * κ)) (astar := 2 * κ * astar) (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by positivity)
  refine ⟨C₀ * (2 / κ) / κ, by positivity, ?_⟩
  intro b hb hcb ι _ p x e z' v u vbar ubar ε hp hz hzM hsol hvb hua hport h1 h2
  obtain ⟨hs, ht, hk1, hk2, hcs, hbs⟩ := ZeroEntranceScale.scale_facts hκ hb hcb
  set s := Real.sqrt ((1 - 2 * b) / (1 - 2 * (1 / 4)))
  set t := Real.sqrt (b / (1 / 4))
  set k := t ^ 2 / s with hkdef
  have hk : 0 < k := by positivity
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  have hε : 0 ≤ ε := (norm_nonneg _).trans h2
  have hκ3 : κ ≤ 1 / 3 := by linarith
  have hs2 : s ^ 2 = 2 * (1 - 2 * b) := by
    rw [Real.sq_sqrt (by have := hκ.trans_le hcb; positivity)]; ring
  have hsκ : κ ≤ s := by nlinarith
  have hs2' : s ≤ 2 / κ := by
    rw [le_div_iff₀ hκ]; nlinarith
  have hcC : ((1 - 2 * b : ℝ) : ℂ) = (s : ℂ) ^ 2 * ((1 - 2 * (1 / 4) : ℝ) : ℂ) := by
    rw [hcs]; push_cast; ring
  have hbC : (b : ℂ) = s * k * ((1 / 4 : ℝ) : ℂ) := by
    conv_lhs => rw [hbs]
    push_cast; ring
  set x' : ι → ℝ := fun i => x i / s
  -- the argument and the port identities
  have harg : ∀ w y : ℂ, (s : ℂ) * (-((e / s : ℝ) : ℂ) - ((1 - 2 * (1 / 4) : ℝ) : ℂ) * (s * w) -
      ((1 / 4 : ℝ) : ℂ) * (k * y)) = -(e : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * w - (b : ℂ) * y := by
    intro w y
    rw [hcC, hbC]
    push_cast
    field_simp
  have hportId : ∀ w : ℂ, (z' / k - ((1 / 4 : ℝ) : ℂ) * (s * w))⁻¹ = (k : ℂ) * (z' - b * w)⁻¹ := by
    intro w
    have : z' / k - ((1 / 4 : ℝ) : ℂ) * (s * w) = (z' - b * w) / k := by
      rw [hbC]; field_simp
    rw [this, inv_div, div_eq_mul_inv]
  obtain ⟨hs1, hs2s, hs3, hs4⟩ := hsol
  have hsol₀ : IsCavitySolution p x' (1 / 4) (1 - 2 * (1 / 4)) (e / s) (z' / k) (s * v)
      (k * u) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [cavityStieltjes_scale p x hs.ne', harg]
      conv_lhs => rw [hs1]
    · rw [hportId]; conv_lhs => rw [hs2s]
    · rw [Complex.im_ofReal_mul]; exact mul_neg_of_pos_of_neg hs hs3
    · rw [Complex.im_ofReal_mul]; exact mul_neg_of_pos_of_neg hk hs4
  have hz' : η * κ / 2 ≤ (z' / (k : ℂ)).im := by
    rw [Complex.div_ofReal_im, le_div_iff₀ hk]
    have : k * κ ≤ 2 := by rwa [le_div_iff₀ hκ] at hk2
    nlinarith
  have hzM' : ‖z' / (k : ℂ)‖ ≤ M / (2 * κ) := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hk.le, div_le_div_iff₀ hk (by positivity)]
    nlinarith
  have hnk : ∀ w : ℂ, ‖(k : ℂ) * w‖ = k * ‖w‖ := fun w => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hk.le]
  have hns : ∀ w : ℂ, ‖(s : ℂ) * w‖ = s * ‖w‖ := fun w => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
  have hvb₀ : ((s : ℂ) * vbar).im ≤ 0 := by
    rw [Complex.im_ofReal_mul]; exact mul_nonpos_of_nonneg_of_nonpos hs.le hvb
  have hua₀ : 2 * κ * astar ≤ ‖(k : ℂ) * ubar‖ := by
    rw [hnk]; exact mul_le_mul hk1 hua ha.le hk.le
  have hport₀ : η * κ / 2 * ‖(k : ℂ) * ubar‖ ^ 2 ≤ -((k : ℂ) * ubar).im := by
    rw [hnk, Complex.im_ofReal_mul]
    have hkk : k * κ ≤ 2 := by rwa [le_div_iff₀ hκ] at hk2
    have hu2 := sq_nonneg ‖ubar‖
    have : η * κ / 2 * (k * ‖ubar‖) ^ 2 ≤ k * (η * ‖ubar‖ ^ 2) := by
      have : η * κ / 2 * (k * ‖ubar‖) ^ 2 = (k * κ / 2) * (k * (η * ‖ubar‖ ^ 2)) := by ring
      rw [this]
      have h0 : 0 ≤ k * (η * ‖ubar‖ ^ 2) := by positivity
      nlinarith
    nlinarith
  have h1₀ : ‖(s : ℂ) * vbar - cavityStieltjes p x' (-((e / s : ℝ) : ℂ) -
      ((1 - 2 * (1 / 4) : ℝ) : ℂ) * (s * vbar) - ((1 / 4 : ℝ) : ℂ) * (k * ubar))‖ ≤
      2 / κ * ε := by
    rw [cavityStieltjes_scale p x hs.ne', harg, ← mul_sub, hns]
    exact (mul_le_mul_of_nonneg_left h1 hs.le).trans (mul_le_mul_of_nonneg_right hs2' hε)
  have h2₀ : ‖(k : ℂ) * ubar - (z' / k - ((1 / 4 : ℝ) : ℂ) * (s * vbar))⁻¹‖ ≤ 2 / κ * ε := by
    rw [hportId, ← mul_sub, hnk]
    exact (mul_le_mul_of_nonneg_left h2 hk.le).trans (mul_le_mul_of_nonneg_right hk2 hε)
  have key := hst ι p x' (e / s) (z' / k) (s * v) (k * u) (s * vbar) (k * ubar) (2 / κ * ε) hp
    hz' hzM' hsol₀ hvb₀ hua₀ hport₀ h1₀ h2₀
  rw [← mul_sub, ← mul_sub, hns, hnk] at key
  have hk1' : κ ≤ k := by linarith
  have hlow : κ * (‖vbar - v‖ + ‖ubar - u‖) ≤ s * ‖vbar - v‖ + k * ‖ubar - u‖ := by
    have e1 := mul_le_mul_of_nonneg_right hsκ (norm_nonneg (vbar - v))
    have e2 := mul_le_mul_of_nonneg_right hk1' (norm_nonneg (ubar - u))
    rw [mul_add]
    exact add_le_add e1 e2
  have hfin := hlow.trans key
  rw [div_mul_eq_mul_div, le_div_iff₀ hκ, mul_comm, mul_assoc]
  exact hfin

end BlockBand.Endpoints.Clock
