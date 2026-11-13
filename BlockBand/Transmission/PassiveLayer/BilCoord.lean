module

public import BlockBand.Transmission.PassiveLayer.Moments

/-!
# Real Gaussian coordinates of the fresh layer, and the variance of its derivative

* `CoordW W`, `coordVar W b`, `coordMap W b`: GUE coordinates (variance 1, through
  `Bridge.gueRaw`) ⊕ Ginibre coordinates (variance `(b/W)/2`, through `ginibreRaw`).
* `freshLaw_eq_map`: `freshLaw W b = (Inputs.gaussianProduct (coordVar W b)).map coordMap`.
* `layerMatrix_line`: `M(ρ + te) = M(ρ) + t · layerDir b e` (the layer matrix is affine in the
  coordinates); `layerDir_isHermitian`.
* `layerDir_sum_le`: `Σ_i v_i |a · (∂_i M) c|² ≤ (4/W)‖a‖²‖c‖²`, the covariance contraction
  behind the `W^{-1/2}` gradient bound.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open scoped Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

open BlockBand.Transmission

/-- Real Gaussian coordinates of the fresh layer: GUE coordinates ⊕ Ginibre coordinates. -/
abbrev CoordW (W : ℕ) : Type := ((Fin W × Fin W) × Fin 2) ⊕ (Fin W × Fin W × Fin 2)

/-- Their variances: `1` for the GUE coordinates, `(b/W)/2` for the Ginibre ones. -/
def coordVar (W : ℕ) (b : ℝ) : CoordW W → ℝ≥0 :=
  Sum.elim (fun _ => 1) (fun _ => Real.toNNReal (b / W) / 2)

/-- The GUE variance `t_A = ((1-2b)/W)₊`. -/
def tA (W : ℕ) (b : ℝ) : ℝ≥0 := Real.toNNReal ((1 - 2 * b) / W)

/-- The coordinate map onto the fresh layer sample. -/
def coordMap (W : ℕ) (b : ℝ) (ρ : CoordW W → ℝ) : LayerSample W .oneBlockOnePort :=
  (fun _ => Bridge.gueRaw (tA W b) (fun i => ρ (Sum.inl i)),
    fun _ _ => ginibreRaw (fun i => ρ (Sum.inr i)))

theorem measurable_coordMap (W : ℕ) (b : ℝ) : Measurable (coordMap W b) := by
  have h1 := Bridge.measurable_gueRaw W (tA W b)
  have h2 := measurable_ginibreRaw (n := W)
  unfold coordMap
  fun_prop

theorem pi_fin_one_eq_map {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] :
    Measure.pi (fun _ : Fin 1 => μ) = μ.map (fun x _ => x) := by
  have h := (measurePreserving_funUnique μ (Fin 1)).symm
  refine h.map_eq.symm.trans ?_
  congr 1

/-- **`freshLaw W b` is the image of the Gaussian product `gaussianProduct (coordVar W b)`.** -/
theorem freshLaw_eq_map (W : ℕ) (b : ℝ) :
    freshLaw W b = (gaussianProduct (coordVar W b)).map (coordMap W b) := by
  set e := MeasurableEquiv.sumPiEquivProdPi (fun _ : CoordW W => ℝ)
  have he := measurePreserving_sumPiEquivProdPi (fun i : CoordW W => gaussianReal 0 (coordVar W b i))
  set c₁ : Matrix (Fin W) (Fin W) ℂ → (Fin 1 → Matrix (Fin W) (Fin W) ℂ) := fun x _ => x
  set c₂ : Matrix (Fin W) (Fin W) ℂ → (Fin 1 → Fin 1 → Matrix (Fin W) (Fin W) ℂ) := fun x _ _ => x
  have hc₁ : Measurable c₁ := by fun_prop
  have hc₂ : Measurable c₂ := by fun_prop
  have hg1 := Bridge.measurable_gueRaw W (tA W b)
  have hg2 := measurable_ginibreRaw (n := W)
  have hcm : coordMap W b = Prod.map (c₁ ∘ Bridge.gueRaw (tA W b)) (c₂ ∘ ginibreRaw) ∘ e := by
    funext ρ; rfl
  rw [gaussianProduct, hcm, ← Measure.map_map (by fun_prop) e.measurable, he.map_eq,
    ← Measure.map_prod_map _ _ (hc₁.comp hg1) (hc₂.comp hg2), ← Measure.map_map hc₁ hg1,
    ← Measure.map_map hc₂ hg2]
  simp only [coordVar, Sum.elim_inl, Sum.elim_inr]
  rw [← Bridge.gueMeasure_eq_map, ← ginibreMeasure_eq_map, freshLaw, layerLaw]
  congr 1
  · exact pi_fin_one_eq_map _
  · rw [pi_fin_one_eq_map, pi_fin_one_eq_map, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl

variable {W : ℕ}

theorem liftX_add (M N : Matrix (Fin W) (Fin W) ℂ) : liftX (M + N) = liftX M + liftX N := by
  ext u v; simp [liftX]

theorem gueRaw_add_smul' (t : ℝ≥0) (ρ e : (Fin W × Fin W) × Fin 2 → ℝ) (c : ℝ) :
    Bridge.gueRaw t (ρ + c • e) = Bridge.gueRaw t ρ + (c : ℂ) • Bridge.gueRaw t e := by
  ext a b
  simp only [Bridge.gueRaw, gueSample, BlockBand.SourceProcess.circularBrownianCoordinates,
    Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, map_add, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

theorem ginibreRaw_add_smul (ρ e : Fin W × Fin W × Fin 2 → ℝ) (c : ℝ) :
    ginibreRaw (ρ + c • e) = ginibreRaw ρ + (c : ℂ) • ginibreRaw e := by
  ext a b
  simp only [ginibreRaw, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  push_cast; ring

theorem gueRaw_isHermitian' (t : ℝ≥0) (ρ : (Fin W × Fin W) × Fin 2 → ℝ) :
    (Bridge.gueRaw t ρ).IsHermitian := Bridge.gueSample_isHermitian t _

/-- The direction of the layer matrix along a coordinate direction `e`. -/
def layerDir (b : ℝ) (e : CoordW W → ℝ) :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  fromBlocks (liftX (Bridge.gueRaw (tA W b) fun i => e (Sum.inl i)))
    (liftX (ginibreRaw fun i => e (Sum.inr i))) (liftX (ginibreRaw fun i => e (Sum.inr i)))ᴴ 0

theorem layerDir_isHermitian (b : ℝ) (e : CoordW W → ℝ) : (layerDir b e).IsHermitian := by
  rw [layerDir, Matrix.IsHermitian, fromBlocks_conjTranspose, conjTranspose_conjTranspose,
    conjTranspose_zero, (liftX_isHermitian (gueRaw_isHermitian' _ _)).eq]

theorem layerMatrix_line (E : ℝ) (w : ℂ) (b : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ρ e : CoordW W → ℝ) (t : ℝ) :
    layerMatrix .oneBlockOnePort E w (liftX X) (coordMap W b (ρ + t • e)) =
      layerMatrix .oneBlockOnePort E w (liftX X) (coordMap W b ρ) + (t : ℂ) • layerDir b e := by
  have h1 : (fun i => (ρ + t • e) (Sum.inl i)) = (fun i => ρ (Sum.inl i)) + t • fun i => e (Sum.inl i) := rfl
  have h2 : (fun i => (ρ + t • e) (Sum.inr i)) = (fun i => ρ (Sum.inr i)) + t • fun i => e (Sum.inr i) := rfl
  rw [layerMatrix_eq, layerMatrix_eq, layerDir, bondL, bondL, blockDiag_one_eq, blockDiag_one_eq,
    bondMatrix_one_eq, bondMatrix_one_eq]
  simp only [coordMap]
  rw [h1, h2, gueRaw_add_smul', ginibreRaw_add_smul]
  rw [fromBlocks_smul, fromBlocks_add]
  congr 1
  all_goals simp only [liftX_add, liftX_smul, conjTranspose_add, conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, smul_zero, add_zero]
  abel

theorem dot_liftX (a c : Fin 1 × Fin W → ℂ) (D : Matrix (Fin W) (Fin W) ℂ) :
    a ⬝ᵥ (liftX D *ᵥ c) = (a ∘ embed0) ⬝ᵥ (D *ᵥ (c ∘ embed0)) := by
  simp only [dotProduct, mulVec, liftX, Matrix.of_apply, Function.comp_apply, embed0,
    Fintype.sum_prod_type, Fin.sum_univ_one]

theorem vecNorm_comp_embed0 (x : Fin 1 × Fin W → ℂ) : vecNorm (x ∘ embed0) = vecNorm x := by
  rw [vecNorm, vecNorm]; congr 1
  simp [embed0, Fintype.sum_prod_type]

theorem dot_fromBlocks {m : Type*} [Fintype m] (P Q R : Matrix m m ℂ) (a c : m ⊕ m → ℂ) :
    a ⬝ᵥ (fromBlocks P Q R 0 *ᵥ c) = (a ∘ Sum.inl) ⬝ᵥ (P *ᵥ (c ∘ Sum.inl)) +
      (a ∘ Sum.inl) ⬝ᵥ (Q *ᵥ (c ∘ Sum.inr)) + (a ∘ Sum.inr) ⬝ᵥ (R *ᵥ (c ∘ Sum.inl)) := by
  rw [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zero_mulVec, add_zero, Pi.add_apply, mul_add,
    Finset.sum_add_distrib, dotProduct, Function.comp_apply]

theorem conjTranspose_form (H : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ) :
    star y ⬝ᵥ (Hᴴ *ᵥ x) = star (star x ⬝ᵥ (H *ᵥ y)) := by
  simp only [dotProduct, mulVec, conjTranspose_apply, star_sum, star_mul', star_star,
    Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem norm_add_sq_le' (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have := norm_add_le a b
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a + b), sq_nonneg (‖a‖ - ‖b‖)]

/-- Linear coefficients of a GUE bilinear form, variance proxy `4t`. -/
theorem gue_coeff (t : ℝ≥0) (x y : Fin W → ℂ) : ∃ c : (Fin W × Fin W) × Fin 2 → ℂ,
    (∀ ρ, star y ⬝ᵥ (Bridge.gueRaw t ρ *ᵥ x) = ∑ k, (ρ k : ℂ) * c k) ∧
      ∑ k, ‖c k‖ ^ 2 ≤ 4 * t * vecNorm x ^ 2 * vecNorm y ^ 2 := by
  obtain ⟨c₁, h₁, hv₁⟩ := isGaussMatrix_gueHalf (n := W) t x y
  obtain ⟨c₂, h₂, hv₂⟩ := isGaussMatrix_gueHalf (n := W) t y x
  refine ⟨fun k => c₁ k + star (c₂ k), fun ρ => ?_, ?_⟩
  · rw [gueRaw_eq, add_mulVec, dotProduct_add, h₁, conjTranspose_form, h₂, star_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_add, Complex.conj_ofReal]
  · simp only [NNReal.coe_one, one_mul] at hv₁ hv₂
    calc ∑ k, ‖c₁ k + star (c₂ k)‖ ^ 2 ≤ ∑ k, (2 * ‖c₁ k‖ ^ 2 + 2 * ‖c₂ k‖ ^ 2) :=
          Finset.sum_le_sum fun k _ => by simpa using norm_add_sq_le' (c₁ k) (star (c₂ k))
      _ = 2 * ∑ k, ‖c₁ k‖ ^ 2 + 2 * ∑ k, ‖c₂ k‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := by nlinarith

theorem sum_single_mul {κ : Type*} [Fintype κ] [DecidableEq κ] (k : κ) (c : κ → ℂ) :
    ∑ j, (((Pi.single k (1 : ℝ) : κ → ℝ) j : ℝ) : ℂ) * c j = c k := by
  rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem vecNorm_star {m : Type*} [Fintype m] (x : m → ℂ) : vecNorm (star x) = vecNorm x := by
  simp [vecNorm]

theorem vecNorm_sq_sum {m : Type*} [Fintype m] (x : m ⊕ m → ℂ) :
    vecNorm x ^ 2 = vecNorm (x ∘ Sum.inl) ^ 2 + vecNorm (x ∘ Sum.inr) ^ 2 := by
  rw [vecNorm_sq_eq, vecNorm_sq_eq, vecNorm_sq_eq, Fintype.sum_sum_type]; rfl

/-- **The Gaussian variance of the layer derivative**: for all vectors `a, c`,
`Σ_i v_i |a·(∂_i M)c|² ≤ (4/W)‖a‖²‖c‖²`. -/
theorem layerDir_sum_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W)
    (a c : LayerSite W .oneBlockOnePort → ℂ) :
    ∑ i, (coordVar W b i : ℝ) * ‖a ⬝ᵥ (layerDir b (Pi.single i 1) *ᵥ c)‖ ^ 2 ≤
      4 / W * vecNorm a ^ 2 * vecNorm c ^ 2 := by
  set a₁ := (a ∘ Sum.inl) ∘ embed0
  set a₂ := (a ∘ Sum.inr) ∘ embed0
  set c₁ := (c ∘ Sum.inl) ∘ embed0
  set c₂ := (c ∘ Sum.inr) ∘ embed0
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have htA : ((tA W b : ℝ≥0) : ℝ) ≤ 1 / W := by
    rw [tA, Real.coe_toNNReal _ (by apply div_nonneg <;> linarith)]
    exact div_le_div_of_nonneg_right (by linarith) hW'.le
  have htB : ((Real.toNNReal (b / W) : ℝ≥0) : ℝ) ≤ 1 / W := by
    rw [Real.coe_toNNReal _ (by positivity)]
    exact div_le_div_of_nonneg_right (by linarith) hW'.le
  obtain ⟨g, hg, hgv⟩ := gue_coeff (tA W b) c₁ (star a₁)
  obtain ⟨d₁, hd₁, hdv₁⟩ := isGaussMatrix_ginibreRaw (n := W) (Real.toNNReal (b / W)) c₂ (star a₁)
  obtain ⟨d₂, hd₂, hdv₂⟩ := isGaussMatrix_ginibreRaw (n := W) (Real.toNNReal (b / W)) (star a₂) c₁
  have hinl : ∀ k, a ⬝ᵥ (layerDir b (Pi.single (Sum.inl k) 1) *ᵥ c) = g k := by
    intro k
    have e1 : (fun j => (Pi.single (Sum.inl k) (1 : ℝ) : CoordW W → ℝ) (Sum.inr j)) = 0 := by
      funext j; simp
    have e2 : (fun j => (Pi.single (Sum.inl k) (1 : ℝ) : CoordW W → ℝ) (Sum.inl j)) =
        Pi.single k 1 := by
      funext j; by_cases h : j = k <;> simp [h]
    have g0 : ginibreRaw (0 : Fin W × Fin W × Fin 2 → ℝ) = 0 := by ext; simp [ginibreRaw]
    rw [layerDir, e1, e2, g0, dot_fromBlocks]
    simp only [show liftX (0 : Matrix (Fin W) (Fin W) ℂ) = 0 by ext; simp [liftX],
      conjTranspose_zero, zero_mulVec, dotProduct_zero, add_zero]
    rw [dot_liftX, ← sum_single_mul k g, ← hg, star_star]
  have hinr : ∀ k, a ⬝ᵥ (layerDir b (Pi.single (Sum.inr k) 1) *ᵥ c) = d₁ k + star (d₂ k) := by
    intro k
    have e1 : (fun j => (Pi.single (Sum.inr k) (1 : ℝ) : CoordW W → ℝ) (Sum.inl j)) = 0 := by
      funext j; simp
    have e2 : (fun j => (Pi.single (Sum.inr k) (1 : ℝ) : CoordW W → ℝ) (Sum.inr j)) =
        Pi.single k 1 := by
      funext j; by_cases h : j = k <;> simp [h]
    have g0 : Bridge.gueRaw (tA W b) (0 : (Fin W × Fin W) × Fin 2 → ℝ) = 0 := by
      ext
      simp [Bridge.gueRaw, gueSample, BlockBand.SourceProcess.circularBrownianCoordinates]
    rw [layerDir, e1, e2, g0, dot_fromBlocks]
    simp only [show liftX (0 : Matrix (Fin W) (Fin W) ℂ) = 0 by ext; simp [liftX],
      zero_mulVec, dotProduct_zero, zero_add]
    rw [dot_liftX, ← liftX_conjTranspose, dot_liftX]
    congr 1
    · rw [← sum_single_mul k d₁, ← hd₁, star_star]
    · have := conjTranspose_form (ginibreRaw (Pi.single k 1)) c₁ (star a₂)
      rw [star_star] at this
      rw [this, hd₂, sum_single_mul]
  rw [Fintype.sum_sum_type]
  simp only [coordVar, Sum.elim_inl, Sum.elim_inr, NNReal.coe_one, one_mul, hinl, hinr]
  have hn1 : vecNorm (star a₁) = vecNorm (a ∘ Sum.inl) := by
    rw [vecNorm_star]; exact vecNorm_comp_embed0 _
  have hn2 : vecNorm (star a₂) = vecNorm (a ∘ Sum.inr) := by
    rw [vecNorm_star]; exact vecNorm_comp_embed0 _
  have hm1 : vecNorm c₁ = vecNorm (c ∘ Sum.inl) := vecNorm_comp_embed0 _
  have hm2 : vecNorm c₂ = vecNorm (c ∘ Sum.inr) := vecNorm_comp_embed0 _
  rw [hn1, hm1] at hgv
  rw [hn1, hm2] at hdv₁
  rw [hn2, hm1] at hdv₂
  rw [vecNorm_sq_sum a, vecNorm_sq_sum c]
  set X₁ := vecNorm (a ∘ Sum.inl) ^ 2
  set X₂ := vecNorm (a ∘ Sum.inr) ^ 2
  set Y₁ := vecNorm (c ∘ Sum.inl) ^ 2
  set Y₂ := vecNorm (c ∘ Sum.inr) ^ 2
  have hX₁ : 0 ≤ X₁ := by positivity
  have hX₂ : 0 ≤ X₂ := by positivity
  have hY₁ : 0 ≤ Y₁ := by positivity
  have hY₂ : 0 ≤ Y₂ := by positivity
  set tB : ℝ := ((Real.toNNReal (b / W) : ℝ≥0) : ℝ)
  have hB2 : ∑ k, ((Real.toNNReal (b / W) / 2 : ℝ≥0) : ℝ) * ‖d₁ k + star (d₂ k)‖ ^ 2 ≤
      2 * tB * (Y₂ * X₁) + 2 * tB * (Y₁ * X₂) := by
    have h1 : ∑ k, ((Real.toNNReal (b / W) / 2 : ℝ≥0) : ℝ) * ‖d₁ k + star (d₂ k)‖ ^ 2 ≤
        ∑ k, (2 * (((Real.toNNReal (b / W) / 2 : ℝ≥0) : ℝ) * ‖d₁ k‖ ^ 2) +
          2 * (((Real.toNNReal (b / W) / 2 : ℝ≥0) : ℝ) * ‖d₂ k‖ ^ 2)) := by
      refine Finset.sum_le_sum fun k _ => ?_
      have := norm_add_sq_le' (d₁ k) (star (d₂ k))
      rw [norm_star] at this
      have h0 : (0 : ℝ) ≤ ((Real.toNNReal (b / W) / 2 : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
      nlinarith
    refine h1.trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
    nlinarith
  have hgv' : ∑ k, ‖g k‖ ^ 2 ≤ 4 * (1 / W) * Y₁ * X₁ := by
    refine hgv.trans ?_
    have : (0 : ℝ) ≤ Y₁ * X₁ := by positivity
    nlinarith
  have htB' : tB ≤ 1 / W := htB
  have h4 : 0 ≤ (1 : ℝ) / W := by positivity
  calc ∑ k, ‖g k‖ ^ 2 + ∑ k, ((Real.toNNReal (b / W) / 2 : ℝ≥0) : ℝ) * ‖d₁ k + star (d₂ k)‖ ^ 2
      ≤ 4 * (1 / W) * Y₁ * X₁ + (2 * tB * (Y₂ * X₁) + 2 * tB * (Y₁ * X₂)) := add_le_add hgv' hB2
    _ ≤ 4 / W * (X₁ + X₂) * (Y₁ + Y₂) := by
        have e : 4 / (W : ℝ) = 4 * (1 / W) := by ring
        rw [e]
        nlinarith [mul_nonneg hY₂ hX₁, mul_nonneg hY₁ hX₂, mul_nonneg hX₂ hY₂]

end BlockBand.Transmission.PassiveLayer
