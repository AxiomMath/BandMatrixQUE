module

public import BlockBand.Palm.CoarseRelativeFluctuation

/-!
# Good spectral event: laws of the matrix Brownian flow

* `hermitianBrownian_eq_gueCoord`: `B(u) = gueCoord (1/N) (w(u))`, `w(u)` the real Wiener
  coordinates at time `u`.
* `flowLaw_increment` (and the outer-measure form `flowLaw_increment_le`): the increment
  `B(v) - B(u)`, `0 ≤ u ≤ v`, has law `GUE_N((v-u)/N)` (used for the dyadic subdivision).
* `flowLaw_map_flowNormalized` (and `flowLaw_preimage_normalized_le`): for `0 < a ≤ σ`,
  `G_σ := σ^{-1/2}(G_a + B(σ - a))` has law `GUE_N(1/N)`, and
  `flowMatrix F a ω σ = F + √σ G_σ` (`flowMatrix_eq_normalized`), so every fixed-time
  statement about `F + √σ GUE_N(1/N)` (e.g. the coarse relative local law) transfers to the flow.

Proof: every law is the image of a Gaussian product law under the real-linear `gueCoord`;
scaling `gaussianReal 0 δ = (gaussianReal 0 1).map (√δ ·)` and, per real coordinate, the
convolution `gaussianReal 0 a ∗ gaussianReal 0 u = gaussianReal 0 (a + u)`.
No measurability assumption is placed on the events of the `_le` forms (outer measure).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.GoodEvent

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm.CoarseRelative BlockBand.SourceProcess
open scoped ComplexConjugate NNReal ENNReal

variable {N : ℕ}

/-- Coordinate index of the real Gaussian coordinates of an `N × N` matrix. -/
abbrev CoordIdx (N : ℕ) := (Fin N × Fin N) × Fin 2

instance isProbabilityMeasure_gueMeasure_goodEvent (ι : Type*) [Fintype ι] (t : ℝ≥0) :
    IsProbabilityMeasure (gueMeasure ι t) := by
  unfold gueMeasure commonCircularIncrementLaw
  infer_instance

/-- `flowLaw N a` is a probability measure. -/
instance flowLaw_isProb (N : ℕ) (a : ℝ) : IsProbabilityMeasure (flowLaw N a) := by
  unfold flowLaw
  infer_instance

theorem measurable_gueCoord (t : ℝ≥0) : Measurable (gueCoord (ι := Fin N) t) := by
  have hc : Measurable (circularBrownianCoordinates (ι := Fin N)) := by
    apply Measurable.of_eval
    intro u
    unfold circularBrownianCoordinates
    fun_prop
  have hg : Continuous (gueSample (ι := Fin N) t) := by
    unfold gueSample
    fun_prop
  exact hg.measurable.comp hc

theorem gueCoord_add (t : ℝ≥0) (y y' : CoordIdx N → ℝ) :
    gueCoord t (y + y') = gueCoord t y + gueCoord t y' :=
  (gueCoordLin (ι := Fin N) t).map_add y y'

theorem gueCoord_smul (t : ℝ≥0) (r : ℝ) (y : CoordIdx N → ℝ) :
    gueCoord t (r • y) = r • gueCoord t y :=
  (gueCoordLin (ι := Fin N) t).map_smul r y

/-- Variance scaling: `gueCoord (c/N) y = √c • gueCoord (1/N) y` for `c ≥ 0`. -/
theorem gueCoord_scale {c : ℝ} (hc : 0 ≤ c) (y : CoordIdx N → ℝ) :
    gueCoord (Real.toNNReal (c / N)) y = Real.sqrt c • gueCoord (Real.toNNReal (1 / N)) y := by
  ext k l
  simp only [gueCoord, gueSample, Matrix.of_apply, Matrix.smul_apply, Complex.real_smul]
  rw [← mul_assoc]
  congr 1
  rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
  rw [← Complex.ofReal_mul]
  congr 1
  rw [← Real.sqrt_mul hc]
  congr 1
  ring

/-- `B(u) = gueCoord (1/N) (w(u))`. -/
theorem hermitianBrownian_eq_gueCoord (B : FlowNoise N) (u : ℝ) :
    hermitianBrownian B u = gueCoord (Real.toNNReal (1 / N)) (fun q => B q (Real.toNNReal u)) := by
  ext k l
  simp only [hermitianBrownian, gueCoord, gueSample, Matrix.of_apply]
  congr 1
  rw [Real.coe_toNNReal _ (by positivity), ← Complex.ofReal_inv, ← Real.sqrt_inv]
  congr 2
  ring

/-- The real Wiener coordinates at time `u`. -/
def wienerAt (u : ℝ) (B : FlowNoise N) : CoordIdx N → ℝ := fun q => B q (Real.toNNReal u)

theorem measurable_wienerAt (u : ℝ) : Measurable (wienerAt (N := N) u) :=
  Measurable.of_eval fun q =>
    (ContinuousMap.measurable_eval (Real.toNNReal u)).comp (measurable_pi_apply q)

theorem measurable_hermitianBrownian (u : ℝ) :
    Measurable (fun B : FlowNoise N => hermitianBrownian B u) := by
  have : (fun B : FlowNoise N => hermitianBrownian B u) =
      gueCoord (Real.toNNReal (1 / N)) ∘ wienerAt u := by
    funext B; exact hermitianBrownian_eq_gueCoord B u
  rw [this]
  exact (measurable_gueCoord _).comp (measurable_wienerAt u)

/-- `∏ γ(0,δ) = (∏ γ(0,1)).map (√δ •)`. -/
theorem pi_gaussian_scale (ι : Type*) [Fintype ι] (δ : ℝ≥0) :
    Measure.pi (fun _ : ι => gaussianReal 0 δ) =
      (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun y => Real.sqrt δ • y) := by
  have h := Measure.pi_map_pi (μ := fun _ : ι => gaussianReal 0 1)
    (f := fun _ (x : ℝ) => Real.sqrt δ * x) (fun _ => (measurable_const_mul _).aemeasurable)
  have hf : (fun (x : ι → ℝ) (i : ι) => Real.sqrt δ * x i) = fun y => Real.sqrt δ • y := by
    funext y i; rfl
  rw [hf] at h
  rw [h]
  congr 1
  funext i
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  simp [Real.sq_sqrt (NNReal.coe_nonneg δ)]

/-- `(∏ γ(0,δ)).map (gueCoord (1/N)) = GUE_N(δ/N)`. -/
theorem map_gueCoord_pi (δ : ℝ≥0) :
    (Measure.pi fun _ : CoordIdx N => gaussianReal 0 δ).map (gueCoord (Real.toNNReal (1 / N))) =
      gueMeasure (Fin N) (Real.toNNReal ((δ : ℝ) / N)) := by
  have hs : Measurable (fun y : CoordIdx N → ℝ => Real.sqrt δ • y) := measurable_const_smul _
  rw [pi_gaussian_scale, Measure.map_map (measurable_gueCoord _) hs,
    gueMeasure_eq_map_gaussianProduct]
  congr 1
  funext y
  simp only [Function.comp_apply]
  rw [gueCoord_smul, gueCoord_scale (NNReal.coe_nonneg δ)]

/-!
## Increments
-/

theorem measurable_matrix_of {α : Type*} [MeasurableSpace α] {f : α → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ i j, Measurable fun x => f x i j) : Measurable f :=
  Measurable.of_eval fun i => Measurable.of_eval fun j => h i j

theorem measurable_matrix_entry {α : Type*} [MeasurableSpace α] {f : α → Matrix (Fin N) (Fin N) ℂ}
    (hf : Measurable f) (i j : Fin N) : Measurable fun x => f x i j :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hf)

theorem gueCoord_sub (t : ℝ≥0) (y y' : CoordIdx N → ℝ) :
    gueCoord t (y - y') = gueCoord t y - gueCoord t y' :=
  (gueCoordLin (ι := Fin N) t).map_sub y y'

theorem flowLaw_map_increment (N : ℕ) (a : ℝ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (flowLaw N a).map (fun ω : FlowSample N => hermitianBrownian ω.2 v - hermitianBrownian ω.2 u) =
      gueMeasure (Fin N) (Real.toNNReal ((v - u) / N)) := by
  have hX := (hasLaw_commonRealBrownian_increment (S := Matrix (Fin N) (Fin N) ℂ)
    (κ := CoordIdx N) (gueMeasure (Fin N) (Real.toNNReal (a / N)))
    (Real.toNNReal u) (Real.toNNReal v)).map_eq
  have hXm : Measurable (fun x : FlowSample N => fun q =>
      commonRealBrownian (Real.toNNReal v) x q - commonRealBrownian (Real.toNNReal u) x q) := by
    apply Measurable.of_eval
    intro q
    unfold commonRealBrownian
    exact ((ContinuousMap.measurable_eval _).comp ((measurable_pi_apply q).comp measurable_snd)).sub
      ((ContinuousMap.measurable_eval _).comp ((measurable_pi_apply q).comp measurable_snd))
  have hf : (fun ω : FlowSample N => hermitianBrownian ω.2 v - hermitianBrownian ω.2 u) =
      gueCoord (Real.toNNReal (1 / N)) ∘ (fun x : FlowSample N => fun q =>
        commonRealBrownian (Real.toNNReal v) x q - commonRealBrownian (Real.toNNReal u) x q) := by
    funext ω
    simp only [Function.comp_apply, hermitianBrownian_eq_gueCoord]
    rw [← gueCoord_sub]
    rfl
  unfold flowLaw
  rw [hf, ← Measure.map_map (measurable_gueCoord _) hXm, hX, map_gueCoord_pi]
  congr 2
  rw [coe_nndist, NNReal.dist_eq, Real.coe_toNNReal _ (by linarith),
    Real.coe_toNNReal _ hu, abs_of_nonneg (by linarith)]

theorem measurable_increment (v u : ℝ) :
    Measurable (fun ω : FlowSample N => hermitianBrownian ω.2 v - hermitianBrownian ω.2 u) := by
  apply measurable_matrix_of
  intro i j
  exact (measurable_matrix_entry ((measurable_hermitianBrownian v).comp measurable_snd) i j).sub
    (measurable_matrix_entry ((measurable_hermitianBrownian u).comp measurable_snd) i j)

/-- **Increment law.** `B(v) - B(u) ~ GUE_N((v-u)/N)` for `0 ≤ u ≤ v`. -/
theorem flowLaw_increment (N : ℕ) (a : ℝ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (S : Set (Matrix (Fin N) (Fin N) ℂ)) (hS : MeasurableSet S) :
    flowLaw N a {ω | hermitianBrownian ω.2 v - hermitianBrownian ω.2 u ∈ S} =
      gueMeasure (Fin N) (Real.toNNReal ((v - u) / N)) S := by
  rw [← flowLaw_map_increment N a hu huv, Measure.map_apply (measurable_increment v u) hS]
  rfl

/-- **Increment law, outer-measure form** (no measurability of `S`). -/
theorem flowLaw_increment_le (N : ℕ) (a : ℝ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (S : Set (Matrix (Fin N) (Fin N) ℂ)) :
    flowLaw N a {ω | hermitianBrownian ω.2 v - hermitianBrownian ω.2 u ∈ S} ≤
      gueMeasure (Fin N) (Real.toNNReal ((v - u) / N)) S := by
  set μ := gueMeasure (Fin N) (Real.toNNReal ((v - u) / N))
  calc flowLaw N a {ω | hermitianBrownian ω.2 v - hermitianBrownian ω.2 u ∈ S}
      ≤ flowLaw N a {ω | hermitianBrownian ω.2 v - hermitianBrownian ω.2 u ∈ toMeasurable μ S} :=
        measure_mono (fun ω hω => subset_toMeasurable μ S hω)
    _ = μ (toMeasurable μ S) := flowLaw_increment N a hu huv _ (measurableSet_toMeasurable μ S)
    _ = μ S := measure_toMeasurable S

/-!
## The normalized matrix at a fixed time
-/

/-- `G_σ = σ^{-1/2}(G_a + B(σ - a))`. -/
def flowNormalized (a σ : ℝ) (ω : FlowSample N) : Matrix (Fin N) (Fin N) ℂ :=
  ((Real.sqrt σ)⁻¹ : ℂ) • (ω.1 + hermitianBrownian ω.2 (σ - a))

theorem measurable_flowNormalized (a σ : ℝ) : Measurable (flowNormalized (N := N) a σ) := by
  apply measurable_matrix_of
  intro i j
  simp only [flowNormalized, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  exact ((measurable_matrix_entry measurable_fst i j).add
    (measurable_matrix_entry ((measurable_hermitianBrownian _).comp measurable_snd) i j)).const_mul _

/-- `H_σ = F + √σ G_σ`. -/
theorem flowMatrix_eq_normalized (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N)
    {σ : ℝ} (hσ : 0 < σ) :
    flowMatrix F a ω σ = F + (Real.sqrt σ : ℂ) • flowNormalized a σ ω := by
  have hne : (Real.sqrt σ : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hσ).ne'
  unfold flowMatrix flowNormalized
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul, add_assoc]

/-- The law of the Wiener coordinates at a fixed time. -/
theorem commonWienerLaw_map_wienerAt (u : ℝ) :
    (commonWienerLaw (CoordIdx N)).map (wienerAt u) =
      Measure.pi fun _ : CoordIdx N => gaussianReal 0 (Real.toNNReal u) := by
  unfold commonWienerLaw
  have h := Measure.pi_map_pi (μ := fun _ : CoordIdx N => canonicalWienerLaw)
    (f := fun _ (ω : CanonicalWienerPath) => ω (Real.toNNReal u))
    (fun _ => (ContinuousMap.measurable_eval _).aemeasurable)
  change Measure.map (fun (x : CoordIdx N → CanonicalWienerPath) (i : CoordIdx N) =>
    x i (Real.toNNReal u)) _ = _
  rw [h]
  congr 1
  funext i
  exact (canonicalWiener_isBrownian.toIsPreBrownianReal.hasLaw_eval (Real.toNNReal u)).map_eq

/-- One coordinate: `(γ(0,a) ⊗ γ(0,u)).map ((x,w) ↦ (√σ)⁻¹(x + w)) = γ(0,1)` when `a + u = σ`. -/
theorem gaussian_pair_normalize {a u σ : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) (hσ : a + u = σ)
    (hσpos : 0 < σ) :
    ((gaussianReal 0 (Real.toNNReal a)).prod (gaussianReal 0 (Real.toNNReal u))).map
        (fun p : ℝ × ℝ => (Real.sqrt σ)⁻¹ * (p.1 + p.2)) = gaussianReal 0 1 := by
  have hcomp : (fun p : ℝ × ℝ => (Real.sqrt σ)⁻¹ * (p.1 + p.2)) =
      (fun x => (Real.sqrt σ)⁻¹ * x) ∘ (fun p : ℝ × ℝ => p.1 + p.2) := rfl
  rw [hcomp, ← Measure.map_map (measurable_const_mul _) measurable_add]
  change Measure.map _ (gaussianReal 0 (Real.toNNReal a) ∗ gaussianReal 0 (Real.toNNReal u)) = _
  rw [gaussianReal_conv_gaussianReal, gaussianReal_map_const_mul, add_zero, mul_zero]
  congr 1
  ext
  simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_add, Real.coe_toNNReal _ ha,
    Real.coe_toNNReal _ hu, NNReal.coe_one, inv_pow, Real.sq_sqrt hσpos.le, hσ]
  field_simp

/-- **Fixed-time law.** For `0 < a ≤ σ`, `G_σ ~ GUE_N(1/N)` under `flowLaw N a`. -/
theorem flowLaw_map_flowNormalized (_hN : 0 < N) {a σ : ℝ} (ha : 0 < a) (haσ : a ≤ σ) :
    (flowLaw N a).map (flowNormalized a σ) = gueMeasure (Fin N) (Real.toNNReal (1 / N)) := by
  have hσpos : 0 < σ := lt_of_lt_of_le ha haσ
  set u := σ - a with hu
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  set γa := Measure.pi fun _ : CoordIdx N => gaussianReal 0 (Real.toNNReal a)
  set γu := Measure.pi fun _ : CoordIdx N => gaussianReal 0 (Real.toNNReal u)
  set W := commonWienerLaw (CoordIdx N)
  have hga : gueMeasure (Fin N) (Real.toNNReal (a / N)) =
      γa.map (gueCoord (Real.toNNReal (1 / N))) := by
    rw [map_gueCoord_pi, Real.coe_toNNReal _ ha.le]
  have hgm : Measurable (gueCoord (ι := Fin N) (Real.toNNReal (1 / N))) := measurable_gueCoord _
  have hflow : flowLaw N a = (γa.prod W).map (Prod.map (gueCoord (Real.toNNReal (1 / N))) id) := by
    unfold flowLaw
    rw [hga, ← Measure.map_prod_map γa W hgm measurable_id, Measure.map_id]
  let L : (CoordIdx N → ℝ) × (CoordIdx N → ℝ) → CoordIdx N → ℝ :=
    fun p => (Real.sqrt σ)⁻¹ • (p.1 + p.2)
  have hLm : Measurable L := by
    change Measurable (fun p : (CoordIdx N → ℝ) × (CoordIdx N → ℝ) => (Real.sqrt σ)⁻¹ • (p.1 + p.2))
    fun_prop
  have hcomp : flowNormalized (N := N) a σ ∘ Prod.map (gueCoord (Real.toNNReal (1 / N))) id =
      gueCoord (Real.toNNReal (1 / N)) ∘ L ∘ Prod.map id (wienerAt u) := by
    funext p
    obtain ⟨y, B⟩ := p
    change ((Real.sqrt σ)⁻¹ : ℂ) • (gueCoord (Real.toNNReal (1 / N)) y + hermitianBrownian B (σ - a)) =
      gueCoord (Real.toNNReal (1 / N)) ((Real.sqrt σ)⁻¹ • (y + wienerAt u B))
    rw [hermitianBrownian_eq_gueCoord, gueCoord_smul, gueCoord_add]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Complex.real_smul, smul_eq_mul,
      Complex.ofReal_inv, hu]
    rfl
  have hWm := measurable_wienerAt (N := N) u
  rw [hflow, Measure.map_map (measurable_flowNormalized a σ) (hgm.prodMap measurable_id), hcomp,
    ← Measure.map_map hgm (hLm.comp (measurable_id.prodMap hWm)),
    ← Measure.map_map hLm (measurable_id.prodMap hWm),
    ← Measure.map_prod_map γa W measurable_id hWm, Measure.map_id, commonWienerLaw_map_wienerAt]
  -- `L` pushes `γa ⊗ γu` to the standard product law
  have hpair := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (CoordIdx N)
    (fun _ => gaussianReal 0 (Real.toNNReal a)) (fun _ => gaussianReal 0 (Real.toNNReal u))).map_eq
  have hLeq : L ∘ (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (CoordIdx N)) =
      fun (z : CoordIdx N → ℝ × ℝ) i => (fun p : ℝ × ℝ => (Real.sqrt σ)⁻¹ * (p.1 + p.2)) (z i) := by
    funext z i
    rfl
  have hstd : (γa.prod γu).map L = Measure.pi fun _ : CoordIdx N => gaussianReal 0 1 := by
    rw [← hpair, Measure.map_map hLm (MeasurableEquiv.measurable _), hLeq,
      Measure.pi_map_pi (fun _ => (by fun_prop : Measurable
        (fun p : ℝ × ℝ => (Real.sqrt σ)⁻¹ * (p.1 + p.2))).aemeasurable)]
    congr 1
    funext i
    exact gaussian_pair_normalize ha.le hu0 (by rw [hu]; ring) hσpos
  rw [hstd, gueMeasure_eq_map_gaussianProduct]
  rfl

/-- **Fixed-time law, outer-measure form** (no measurability of `S`). -/
theorem flowLaw_preimage_normalized_le (hN : 0 < N) {a σ : ℝ} (ha : 0 < a) (haσ : a ≤ σ)
    (S : Set (Matrix (Fin N) (Fin N) ℂ)) :
    flowLaw N a {ω | flowNormalized a σ ω ∈ S} ≤ gueMeasure (Fin N) (Real.toNNReal (1 / N)) S := by
  set μ := gueMeasure (Fin N) (Real.toNNReal (1 / N))
  calc flowLaw N a {ω | flowNormalized a σ ω ∈ S}
      ≤ flowLaw N a (flowNormalized a σ ⁻¹' toMeasurable μ S) :=
        measure_mono (fun ω hω => subset_toMeasurable μ S hω)
    _ = (flowLaw N a).map (flowNormalized a σ) (toMeasurable μ S) :=
        (Measure.map_apply (measurable_flowNormalized a σ) (measurableSet_toMeasurable μ S)).symm
    _ = μ (toMeasurable μ S) := by rw [flowLaw_map_flowNormalized hN ha haσ]
    _ = μ S := measure_toMeasurable S

end BlockBand.Palm.GoodEvent
