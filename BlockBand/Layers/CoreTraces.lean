module

public import BlockBand.Layers.CoreMeans

/-!
# Matched traces of the one- and two-block cores (the matched-traces theorem, `r ∈ {1, 2}`)

Steps 1–2 of the proof of the matched-traces theorem: `coreTraces_holds` proves the `path` clause
of `MatchedTracesContract` restricted to the cores `r ∈ {1, 2}`, from
`ConditionalBlockGUECount` and `GaussianLpGradient`.

Law: `pathLaw W r b` (independent `GUE_W(c/W)` blocks, `c = 1 - 2b`, and `Gin(b/W)` bonds);
deterministic `E ∈ bulkInterval κ`, `z = z_∂(E) = boundaryZ b E`, `a = matchedA E`. Norms: `L^p`
of the scalar `max_i |W⁻¹ Tr(R_r)_{ii} - a|`, `R_r = pathPortResolvent b E`; `ℓ²` operator norm on
matrices. Uniformity: `ε₀, C` depend only on `b ∈ (0, 1/2)` and `κ > 0`; the bound holds for every
`W ≥ 1` and `2 ≤ p ≤ ε₀ W`.

## Proof

1. **Layer identifications** (§1–2). `r = 1`: `coreOne` maps a `.oneBlockTwoPorts` layer sample to
   the one-block path (`coreOne_measurePreserving`), `pathMatrix = diag A`, the port coupling is the
   layer bond matrix, and `R_1` is the port block of the layer resolvent with `X = 0`
   (`coreOne_portResolvent`, Schur complement). `r = 2`: conditioning on the internal bond `β`,
   `coreTwo (β, ℓ)` is the two-block path (`coreTwo_measurePreserving`: the law is
   `Gin(b/W) ⊗ layerLaw .separate`), `pathMatrix = diag A + coreOff β` (`β` at `(0,1)`, `βᴴ` at
   `(1,0)`, the bond orientation of `pathMatrix`), and `R_2` is the port block of the
   `.separate` layer resolvent with `X = -coreOff β` (`coreTwo_portResolvent`).
2. **Mean equations** (the vector Dyson equation). `r = 1`: the layer identity `meq_limit_law`
   with `X = 0`; its shift is block-constant (`core_shift_one`), giving the `S₃` system. `r = 2`:
   the internal bond is one more Gaussian coordinate: `coreEmbed` realizes `Gin ⊗ layerLaw` as the
   image of `gaussianProduct (coreVar W b)` (`core_law_eq_map`), the matrix is affine
   (`core_matrix_eq`), and `core_limit_identity` applies; the contraction is the layer shift plus
   the β-shift `b (g_1 P_0 + g_0 P_1)` (`coreS_eq`, `core_bondS`), giving the `S₄` system
   (`core_mean2`, `core_shift_two`). Residuals: `|e_β| ≤ Σ_γ |w_βγ| |Cov(g_γ, g_β)| ≤ A²`,
   `A = C_f √2 / W`, by `core_cov_tr`.
3. **Fluctuations**. `r = 1`: `traceFluctuation_holds` with `D = P_β` (`‖D‖ ≤ 1`). `r = 2`:
   `core_fluctuation` in all coordinates (`core_fluct2`), with `Γ = 5` (`core_weighted_le`:
   layer part `≤ 16‖K‖²`, bond part `≤ 4‖K‖²`) and the moments of `‖𝒢‖` under
   `Gin ⊗ layerLaw` from `GaussianAbsorptionContract` uniformly in `X` (`core_mom2`, Tonelli),
   a.s. invertibility likewise (`core_ae_unit2`).
4. **Stability** (`CoreDyson`): `coreDyson_one`, `coreDyson_two` give `|ū_j - a| ≤ C_D A²`
   (signs `-Im m̄ ≥ 0` from `lct_im_physBlockTrace_nonpos`, bound `|m̄| ≤ C_A`).
5. **Assembly** (`core_final`, Minkowski) and transfer to `pathLaw` (`core_transfer`):
   `‖max_j |g_j - a|‖_p ≤ 2 C_f √p/W + C_D A² ≤ (2C_f + 2C_D C_f²) √p / W`.
   Small `W` is vacuous: `ε₀ ≤ εD/(C_f² + 1)` forces `2 (C_f² + 1) ≤ εD W` whenever some
   `p ∈ [2, ε₀ W]` exists.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct weightedGradientNorm GaussianLpGradient)
open BlockBand.Internal.Contracts.CoareaPalm (gueMeasure gueSample)
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator

/-!
## 1. The one-block core is a `.oneBlockTwoPorts` layer with `X = 0`
-/

/-- The path of one block from a `.oneBlockTwoPorts` layer sample. -/
def coreOne {W : ℕ} (ℓ : LayerSample W .oneBlockTwoPorts) : PathSample W 1 :=
  (ℓ.1, fun i => i.elim0, fun j => ℓ.2 0 j)

theorem coreOne_pathMatrix {W : ℕ} (ℓ : LayerSample W .oneBlockTwoPorts) :
    pathMatrix (coreOne ℓ) = Internal.Contracts.Layers.blockDiag ℓ.1 := by
  ext x y
  have hx : x.1 = y.1 := Subsingleton.elim _ _
  simp [pathMatrix, Internal.Contracts.Layers.blockDiag, hx, coreOne]

theorem coreOne_portCoupling {W : ℕ} (ℓ : LayerSample W .oneBlockTwoPorts) :
    pathPortCoupling (coreOne ℓ) = bondMatrix .oneBlockTwoPorts ℓ.2 := by
  ext x y
  have hx : x.1 = 0 := Subsingleton.elim _ _
  have hy : y.1 = 0 ∨ y.1 = 1 := by
    rcases y with ⟨j, β⟩; fin_cases j <;> simp
  have hc : (y.1 = 0 ∧ x.1.val = 0) ∨ (y.1 = 1 ∧ x.1.val + 1 = 1) := by
    rw [hx]
    rcases hy with h | h
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr ⟨h, rfl⟩
  simp only [pathPortCoupling, bondMatrix, LayerShape.incident, coreOne]
  simp only [hx, Fin.val_zero, Fin.isValue]
  rcases hy with h | h <;> simp [h]

/-- `R_1` is the port block of the layer resolvent with `X = 0`. -/
theorem coreOne_portResolvent {W : ℕ} (b E : ℝ) (ℓ : LayerSample W .oneBlockTwoPorts)
    (hH : IsUnit (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 - 0).det) :
    pathPortResolvent b E (coreOne ℓ) =
      (layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0 ℓ).toBlocks₂₂ := by
  rw [layerResolvent, layerMatrix, pg_toBlocks22_inv _ _ _ _ hH, pathPortResolvent, pathSchur,
    coreOne_pathMatrix, coreOne_portCoupling, sub_zero]

/-- The law of the one-block path is the image of the `.oneBlockTwoPorts` layer law. -/
theorem coreOne_measurePreserving (W : ℕ) (b : ℝ) :
    MeasurePreserving (coreOne (W := W)) (layerLaw W b .oneBlockTwoPorts) (pathLaw W 1 b) := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  set μ := ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  have : IsEmpty (Fin (1 - 1)) := ⟨fun i => Fin.elim0 i⟩
  have h0 : (Measure.pi fun _ : Fin (1 - 1) => μ) = Measure.dirac (fun i => i.elim0) :=
    Measure.pi_of_empty _ _
  have hB : MeasurePreserving (fun B : Fin 1 → Fin 2 → Matrix (Fin W) (Fin W) ℂ => B 0)
      (Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin 2 => μ)
      (Measure.pi fun _ : Fin 2 => μ) :=
    measurePreserving_funUnique (Measure.pi fun _ : Fin 2 => μ) (Fin 1)
  have hP : MeasurePreserving
      (fun B : Fin 2 → Matrix (Fin W) (Fin W) ℂ => ((fun i => i.elim0 : Fin (1 - 1) → _), B))
      (Measure.pi fun _ : Fin 2 => μ)
      ((Measure.pi fun _ : Fin (1 - 1) => μ).prod (Measure.pi fun _ : Fin 2 => μ)) := by
    refine ⟨measurable_prodMk_left, ?_⟩
    rw [h0, Measure.dirac_prod]
  exact (MeasurePreserving.id _).prod (hP.comp hB)

/-!
## 2. The two-block core is a `.separate` layer with the internal bond as `X`
-/

/-- The internal bond as an off-diagonal block matrix: `β` at `(0, 1)`, `βᴴ` at `(1, 0)`. -/
def coreOff {W : ℕ} (β : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (PhysSite W .separate) (PhysSite W .separate) ℂ :=
  fun x y => if x.1 = 0 ∧ y.1 = 1 then β x.2 y.2
    else if x.1 = 1 ∧ y.1 = 0 then star (β y.2 x.2) else 0

theorem coreOff_isHermitian {W : ℕ} (β : Matrix (Fin W) (Fin W) ℂ) :
    (coreOff β).IsHermitian := by
  ext ⟨a, α⟩ ⟨c, γ⟩
  fin_cases a <;> fin_cases c <;> simp [coreOff]

/-- The two-block path from a `.separate` layer sample and an internal bond. -/
def coreTwo {W : ℕ} (q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate) : PathSample W 2 :=
  (q.2.1, fun _ => q.1, fun j => q.2.2 j j)

theorem coreTwo_pathMatrix {W : ℕ} (q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate) :
    pathMatrix (coreTwo q) = Internal.Contracts.Layers.blockDiag q.2.1 + coreOff q.1 := by
  ext ⟨a, α⟩ ⟨c, γ⟩
  fin_cases a <;> fin_cases c <;>
    simp [pathMatrix, Internal.Contracts.Layers.blockDiag, coreOff, coreTwo]

theorem coreTwo_portCoupling {W : ℕ} (q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate) :
    pathPortCoupling (coreTwo q) = bondMatrix .separate q.2.2 := by
  ext ⟨a, α⟩ ⟨j, γ⟩
  fin_cases a <;> fin_cases j <;>
    simp [pathPortCoupling, bondMatrix, LayerShape.incident, coreTwo]

/-- `R_2` is the port block of the `.separate` layer resolvent with `X = -coreOff β`. -/
theorem coreTwo_portResolvent {W : ℕ} (b E : ℝ)
    (q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate)
    (hH : IsUnit (Internal.Contracts.Layers.blockDiag q.2.1 - (E : ℂ) • 1 - -coreOff q.1).det) :
    pathPortResolvent b E (coreTwo q) =
      (layerResolvent .separate E (boundaryZ b E) (-coreOff q.1) q.2).toBlocks₂₂ := by
  rw [layerResolvent, layerMatrix, pg_toBlocks22_inv _ _ _ _ hH, pathPortResolvent, pathSchur,
    coreTwo_pathMatrix, coreTwo_portCoupling, sub_neg_eq_add, sub_add_eq_add_sub]

/-- The law of the two-block path: independent internal bond `Gin(b/W)` and `.separate` layer. -/
theorem coreTwo_measurePreserving (W : ℕ) (b : ℝ) :
    MeasurePreserving (coreTwo (W := W))
      ((ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))).prod (layerLaw W b .separate))
      (pathLaw W 2 b) := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  set g := gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))
  set μ := ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  set μA := Measure.pi fun _ : Fin 2 => g
  set μB := Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ
  -- `(β, (A, B)) ↦ (A, (β, B))`
  have h1 := (measurePreserving_prodAssoc μ μA μB).symm MeasurableEquiv.prodAssoc
  have h2 := ((Measure.measurePreserving_swap (μ := μ) (ν := μA)).prod (MeasurePreserving.id μB))
  have h3 := measurePreserving_prodAssoc μA μ μB
  have hR := h3.comp (h2.comp h1)
  have hc : MeasurePreserving (fun β : Matrix (Fin W) (Fin W) ℂ => fun _ : Fin (2 - 1) => β) μ
      (Measure.pi fun _ : Fin (2 - 1) => μ) := by
    convert (measurePreserving_funUnique μ (Fin 1)).symm (MeasurableEquiv.funUnique (Fin 1) _)
      using 2
    rfl
  have hF := (MeasurePreserving.id μA).prod (hc.prod (pg_mp_growPorts μ))
  convert hF.comp hR using 1
  all_goals rfl

/-!
## 3. Gaussian coordinates of the two-block core
-/

/-- Real coordinates of the internal bond. -/
abbrev CoreBetaCoord (W : ℕ) := Fin W × Fin W × Fin 2

/-- All real coordinates of the two-block core: the internal bond, then the `.separate` layer. -/
abbrev CoreCoord (W : ℕ) := CoreBetaCoord W ⊕ TflCoord W .separate

/-- Variances: `b/(2W)` on the bond coordinates, `tflVar` on the layer coordinates. -/
def coreVar (W : ℕ) (b : ℝ) : CoreCoord W → ℝ≥0 :=
  Sum.elim (fun _ => tflTB W b / 2) (tflVar W b .separate)

/-- The internal bond and the layer sample from the real coordinates. -/
def coreEmbed (W : ℕ) (b : ℝ) (x : CoreCoord W → ℝ) :
    Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate :=
  (ginibreAssemble (fun c => x (Sum.inl c)), tflEmbed W b .separate (fun c => x (Sum.inr c)))

theorem core_measurable_embed (W : ℕ) (b : ℝ) : Measurable (coreEmbed W b) :=
  (measurable_ginibreAssemble.comp (by fun_prop)).prodMk
    ((tfl_measurable_embed W b .separate).comp (by fun_prop))

/-- **The law of the two-block core in real coordinates.** -/
theorem core_law_eq_map (W : ℕ) (b : ℝ) :
    (ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))).prod (layerLaw W b .separate) =
      (gaussianProduct (coreVar W b)).map (coreEmbed W b) := by
  have h3 := (measurePreserving_sumPiEquivProdPi
      (fun i : CoreCoord W => gaussianReal 0 (coreVar W b i))).map_eq
  rw [ginibreMeasure_eq_map, tfl_layerLaw_eq_map,
    Measure.map_prod_map _ _ measurable_ginibreAssemble (tfl_measurable_embed W b .separate)]
  change _ = (Measure.pi fun i : CoreCoord W => gaussianReal 0 (coreVar W b i)).map _
  rw [show (whiteNoise (Fin W × Fin W × Fin 2) (Real.toNNReal (b / W) / 2)).prod
      (gaussianProduct (tflVar W b .separate)) =
      (Measure.pi fun i => gaussianReal 0 (coreVar W b (Sum.inl i)) : Measure (CoreBetaCoord W → ℝ)).prod
        (Measure.pi fun i => gaussianReal 0 (coreVar W b (Sum.inr i))) from rfl, ← h3, Measure.map_map (measurable_ginibreAssemble.prodMap (tfl_measurable_embed W b _))
    (MeasurableEquiv.measurable _)]
  rfl

/-- The internal bond as a matrix on the layer sites. -/
def coreLb {W : ℕ} (β : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
  fromBlocks (coreOff β) 0 0 0

theorem coreOff_add {W : ℕ} (β β' : Matrix (Fin W) (Fin W) ℂ) :
    coreOff (β + β') = coreOff β + coreOff β' := by
  ext x y; simp only [coreOff, Matrix.add_apply, star_add]; split_ifs <;> simp

theorem coreOff_smul {W : ℕ} (r : ℝ) (β : Matrix (Fin W) (Fin W) ℂ) :
    coreOff (r • β) = r • coreOff β := by
  ext x y
  simp only [coreOff, Matrix.smul_apply]
  split_ifs <;> simp [Complex.real_smul]

/-- The linear part of the two-block core matrix: internal bond plus layer coordinates. -/
def coreLinMap (W : ℕ) (b : ℝ) :
    (CoreCoord W → ℝ) →ₗ[ℝ] Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ where
  toFun x := coreLb (ginibreAssemble (fun c => x (Sum.inl c))) +
    tflLin W b .separate (fun c => x (Sum.inr c))
  map_add' x y := by
    have h1 : ginibreAssemble (fun c => (x + y) (Sum.inl c)) =
        ginibreAssemble (fun c => x (Sum.inl c)) + ginibreAssemble (fun c => y (Sum.inl c)) := by
      ext; simp [ginibreAssemble]; ring
    have h2 : tflLin W b .separate (fun c => x (Sum.inr c) + y (Sum.inr c)) =
        tflLin W b .separate (fun c => x (Sum.inr c)) +
          tflLin W b .separate (fun c => y (Sum.inr c)) :=
      tflLin_add W b .separate (fun c => x (Sum.inr c)) (fun c => y (Sum.inr c))
    simp only [Pi.add_apply] at h1 ⊢
    rw [h1, h2, coreLb, coreLb, coreLb, coreOff_add]
    have : fromBlocks (coreOff (ginibreAssemble fun c => x (Sum.inl c)) +
        coreOff (ginibreAssemble fun c => y (Sum.inl c))) (0 : Matrix (PhysSite W .separate)
          (PortSite W .separate) ℂ) 0 (0 : Matrix (PortSite W .separate) (PortSite W .separate) ℂ) =
        fromBlocks (coreOff (ginibreAssemble fun c => x (Sum.inl c))) 0 0 0 +
          fromBlocks (coreOff (ginibreAssemble fun c => y (Sum.inl c))) 0 0 0 := by
      rw [fromBlocks_add]; simp
    rw [this]
    abel
  map_smul' r x := by
    have h1 : ginibreAssemble (fun c => (r • x) (Sum.inl c)) =
        r • ginibreAssemble (fun c => x (Sum.inl c)) := by
      ext; simp [ginibreAssemble, Complex.real_smul]; ring
    have h2 : tflLin W b .separate (fun c => r • x (Sum.inr c)) =
        r • tflLin W b .separate (fun c => x (Sum.inr c)) :=
      tflLin_smul W b .separate r (fun c => x (Sum.inr c))
    simp only [Pi.smul_apply] at h1 ⊢
    rw [h1, h2, coreLb, coreLb, coreOff_smul, RingHom.id_apply, smul_add]
    congr 1
    rw [fromBlocks_smul, smul_zero]

/-- The linear part as a continuous linear map. -/
def coreLin (W : ℕ) (b : ℝ) :
    (CoreCoord W → ℝ) →L[ℝ] Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
  LinearMap.toContinuousLinearMap (coreLinMap W b)

theorem coreLin_apply (W : ℕ) (b : ℝ) (x : CoreCoord W → ℝ) :
    coreLin W b x = coreLb (ginibreAssemble (fun c => x (Sum.inl c))) +
      tflLin W b .separate (fun c => x (Sum.inr c)) := rfl

/-- The constant part `diag(-E, z)`. -/
def coreC0 (W : ℕ) (E : ℝ) (z : ℂ) : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
  tflConst .separate E z 0

/-- **The two-block core matrix in coordinates**: `C₀ + L x` is the `.separate` layer matrix
with `X = -coreOff β`. -/
theorem core_matrix_eq (W : ℕ) (b E : ℝ) (z : ℂ) (x : CoreCoord W → ℝ) :
    coreC0 W E z + coreLin W b x =
      layerMatrix .separate E z (-coreOff (coreEmbed W b x).1) (coreEmbed W b x).2 := by
  rw [coreEmbed, tfl_layerMatrix_embed, coreLin_apply, coreC0, tflConst, tflConst, coreLb]
  rw [← add_assoc, fromBlocks_add]
  congr 2 <;> simp

theorem core_reg (W : ℕ) (b E : ℝ) {z : ℂ} (hz : 0 ≤ z.im) :
    CoreReg (coreC0 W E z) (coreLin W b) := by
  intro κ hκ x
  have he : corePsi (coreC0 W E z) (coreLin W b) κ x =
      tflReg κ (layerMatrix .separate E z (-coreOff (coreEmbed W b x).1) (coreEmbed W b x).2) := by
    rw [← core_matrix_eq, corePsi, tflReg]; abel
  have hX : (-coreOff (coreEmbed W b x).1).IsHermitian := (coreOff_isHermitian _).neg
  obtain ⟨h1, h2⟩ := tfl_reg_inv_le .separate E hX (coreEmbed W b x).2
    (tflEmbed_blockDiag_isHermitian W b .separate _) hz hκ
  rw [he, ← Matrix.nonsing_inv_eq_ringInverse, Matrix.isUnit_iff_isUnit_det]
  exact ⟨h1, h2⟩

/-!
## 4. The Gaussian contraction of the two-block core
-/

theorem coreLin_inr (W : ℕ) (b : ℝ) (c : TflCoord W .separate) :
    coreLin W b (Pi.single (Sum.inr c) 1) = tflLin W b .separate (Pi.single c 1) := by
  rw [coreLin_apply]
  have h1 : (fun d => (Pi.single (Sum.inr c) (1 : ℝ) : CoreCoord W → ℝ) (Sum.inl d)) = 0 := by
    funext d; simp
  have h2 : (fun d => (Pi.single (Sum.inr c) (1 : ℝ) : CoreCoord W → ℝ) (Sum.inr d)) =
      Pi.single c 1 := by
    funext d; simp [Pi.single_apply]
  rw [h1, h2]
  have h3 : ginibreAssemble (0 : CoreBetaCoord W → ℝ) = 0 := by ext; simp [ginibreAssemble]
  have h4 : coreOff (0 : Matrix (Fin W) (Fin W) ℂ) = 0 := by ext; simp [coreOff]
  rw [h3, coreLb, h4, fromBlocks_zero, zero_add]

theorem coreLin_inl (W : ℕ) (b : ℝ) (c : CoreBetaCoord W) :
    coreLin W b (Pi.single (Sum.inl c) 1) =
      coreLb (ginibreAssemble (Pi.single c 1)) := by
  rw [coreLin_apply]
  have h1 : (fun d => (Pi.single (Sum.inl c) (1 : ℝ) : CoreCoord W → ℝ) (Sum.inl d)) =
      Pi.single c 1 := by
    funext d; simp [Pi.single_apply]
  have h2 : (fun d => (Pi.single (Sum.inl c) (1 : ℝ) : CoreCoord W → ℝ) (Sum.inr d)) = 0 := by
    funext d; simp
  rw [h1, h2]
  have h3 : tflLin W b .separate 0 = 0 := by
    have := tflLin_smul W b .separate 0 0
    simpa using this
  rw [h3, add_zero]

theorem coreLb_single0 {W : ℕ} (α γ : Fin W) :
    coreLb (ginibreAssemble (Pi.single ((α, γ, 0) : CoreBetaCoord W) 1)) =
      single (Sum.inl ((0 : Fin 2), α) : LayerSite W .separate) (Sum.inl ((1 : Fin 2), γ)) 1 +
        single (Sum.inl ((1 : Fin 2), γ)) (Sum.inl ((0 : Fin 2), α)) 1 := by
  ext p q
  rcases p with ⟨c, α'⟩ | ⟨c, α'⟩ <;> rcases q with ⟨d, γ'⟩ | ⟨d, γ'⟩ <;>
    fin_cases c <;> fin_cases d <;>
    simp [coreLb, coreOff, ginibreAssemble, Pi.single_apply, Matrix.single_apply] <;>
    (try split_ifs) <;> simp_all [eq_comm]

theorem coreLb_single1 {W : ℕ} (α γ : Fin W) :
    coreLb (ginibreAssemble (Pi.single ((α, γ, 1) : CoreBetaCoord W) 1)) =
      single (Sum.inl ((0 : Fin 2), α) : LayerSite W .separate) (Sum.inl ((1 : Fin 2), γ))
          Complex.I +
        single (Sum.inl ((1 : Fin 2), γ)) (Sum.inl ((0 : Fin 2), α)) (-Complex.I) := by
  ext p q
  rcases p with ⟨c, α'⟩ | ⟨c, α'⟩ <;> rcases q with ⟨d, γ'⟩ | ⟨d, γ'⟩ <;>
    fin_cases c <;> fin_cases d <;>
    simp [coreLb, coreOff, ginibreAssemble, Pi.single_apply, Matrix.single_apply] <;>
    (try split_ifs) <;> simp_all [eq_comm]

/-- The internal-bond part of the contraction:
`Σ_{bond coords} vᵢ Λᵢ G Λᵢ = t_B (Tr_1 G · P_0 + Tr_0 G · P_1)` (unnormalized traces). -/
theorem core_bondS (W : ℕ) (b : ℝ) (G : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) :
    ∑ c : CoreBetaCoord W, (coreVar W b (Sum.inl c) : ℝ) •
      (coreLin W b (Pi.single (Sum.inl c) 1) * G * coreLin W b (Pi.single (Sum.inl c) 1)) =
      ((tflTB W b : ℝ) : ℂ) • (meqTrA G 1 • meqPhysProj 0 + meqTrA G 0 • meqPhysProj 1) := by
  have hpair : ∀ α γ : Fin W, ∑ s : Fin 2, (coreVar W b (Sum.inl (α, γ, s)) : ℝ) •
      (coreLin W b (Pi.single (Sum.inl (α, γ, s)) 1) * G *
        coreLin W b (Pi.single (Sum.inl (α, γ, s)) 1)) =
      ((tflTB W b : ℝ) : ℂ) •
        (single (Sum.inl ((0 : Fin 2), α) : LayerSite W .separate) (Sum.inl ((0 : Fin 2), α))
            (G (Sum.inl ((1 : Fin 2), γ)) (Sum.inl ((1 : Fin 2), γ))) +
          single (Sum.inl ((1 : Fin 2), γ)) (Sum.inl ((1 : Fin 2), γ))
            (G (Sum.inl ((0 : Fin 2), α)) (Sum.inl ((0 : Fin 2), α)))) := by
    intro α γ
    rw [Fin.sum_univ_two]
    rw [coreLin_inl W b (α, γ, 0), coreLin_inl W b (α, γ, 1), coreLb_single0, coreLb_single1]
    simp only [coreVar, Sum.elim_inl]
    rw [← smul_add, meq_sandwich, ← Complex.coe_smul, smul_smul]
    congr 1
    push_cast
    ring
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun α _ => (Fintype.sum_prod_type _).trans
    (Finset.sum_congr rfl fun γ _ => hpair α γ)]
  have h := meq_double_sum G (fun α : Fin W => (Sum.inl ((0 : Fin 2), α) : LayerSite W .separate))
    (fun γ => Sum.inl ((1 : Fin 2), γ))
  calc ∑ α : Fin W, ∑ γ : Fin W, ((tflTB W b : ℝ) : ℂ) •
        (single (Sum.inl ((0 : Fin 2), α) : LayerSite W .separate) (Sum.inl ((0 : Fin 2), α))
            (G (Sum.inl ((1 : Fin 2), γ)) (Sum.inl ((1 : Fin 2), γ))) +
          single (Sum.inl ((1 : Fin 2), γ)) (Sum.inl ((1 : Fin 2), γ))
            (G (Sum.inl ((0 : Fin 2), α)) (Sum.inl ((0 : Fin 2), α))))
      = ((tflTB W b : ℝ) : ℂ) • ∑ α : Fin W, ∑ γ : Fin W,
        (single (Sum.inl ((0 : Fin 2), α) : LayerSite W .separate) (Sum.inl ((0 : Fin 2), α))
            (G (Sum.inl ((1 : Fin 2), γ)) (Sum.inl ((1 : Fin 2), γ))) +
          single (Sum.inl ((1 : Fin 2), γ)) (Sum.inl ((1 : Fin 2), γ))
            (G (Sum.inl ((0 : Fin 2), α)) (Sum.inl ((0 : Fin 2), α)))) := by
        simp only [Finset.smul_sum]
    _ = _ := by
        rw [h, meq_sum_single_phys (W := W) (σ := .separate) 0,
          meq_sum_single_phys (W := W) (σ := .separate) 1]
        rfl

/-- **The contraction of the two-block core**: the `.separate` layer shift plus the internal-bond
shift `b (g_1 P_0 + g_0 P_1)`. -/
theorem coreS_eq {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (G : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) :
    coreS (coreVar W b) (coreLin W b) G =
      meqShift .separate (1 - 2 * (b : ℂ)) b (physBlockTrace G) (portBlockTrace G) +
        (b : ℂ) • (physBlockTrace G 1 • meqPhysProj 0 + physBlockTrace G 0 • meqPhysProj 1) := by
  have hW' : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hW.ne'
  unfold coreS
  rw [Fintype.sum_sum_type, core_bondS, add_comm]
  congr 1
  · have : ∀ c : TflCoord W .separate, (coreVar W b (Sum.inr c) : ℝ) •
        (coreLin W b (Pi.single (Sum.inr c) 1) * G * coreLin W b (Pi.single (Sum.inr c) 1)) =
        (tflVar W b .separate c : ℝ) •
          (tflLin W b .separate (Pi.single c 1) * G * tflLin W b .separate (Pi.single c 1)) :=
      fun c => by rw [coreLin_inr]; rfl
    rw [Finset.sum_congr rfl fun c _ => this c]
    change meqS W b .separate G = _
    rw [meqS_eq hW, meq_coefA hW hb1, meq_coefB hW hb0]
  · rw [← meq_coefB hW hb0]
    simp only [physBlockTrace, smul_add, smul_smul]
    congr 2
    · unfold meqTrA; field_simp
    · unfold meqTrA; field_simp

/-!
## 5. Block-constant forms
-/

/-- The diagonal `h = (-E, z)` per block. -/
def coreH {σ : LayerShape} (E : ℝ) (z : ℂ) : Fin σ.blocks ⊕ Fin σ.ports → ℂ :=
  Sum.elim (fun _ => -(E : ℂ)) (fun _ => z)

theorem core_tflConst_eq {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ) :
    tflConst σ E z (0 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) =
      diagonal (fun x => coreH (σ := σ) E z (coreBlk x)) := by
  ext p q
  rcases p with p | p <;> rcases q with q | q <;>
    simp [tflConst, coreH, coreBlk, diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

/-- The `S₃` weights (one block, two ports). -/
def coreW1 (b : ℝ) : Fin 1 ⊕ Fin 2 → Fin 1 ⊕ Fin 2 → ℂ
  | .inl _, .inl _ => ((1 - 2 * b : ℝ) : ℂ)
  | .inl _, .inr _ => (b : ℂ)
  | .inr _, .inl _ => (b : ℂ)
  | .inr _, .inr _ => 0

/-- The `S₄` weights (two blocks, one port each). -/
def coreW2 (b : ℝ) : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2 → ℂ
  | .inl a, .inl a' => if a = a' then ((1 - 2 * b : ℝ) : ℂ) else (b : ℂ)
  | .inl a, .inr j => if a = j then (b : ℂ) else 0
  | .inr j, .inl a => if a = j then (b : ℂ) else 0
  | .inr _, .inr _ => 0

theorem core_shift_one {W : ℕ} (b : ℝ)
    (G : Matrix (LayerSite W .oneBlockTwoPorts) (LayerSite W .oneBlockTwoPorts) ℂ) :
    meqShift .oneBlockTwoPorts (1 - 2 * (b : ℂ)) b (physBlockTrace G) (portBlockTrace G) =
      diagonal (fun x : LayerSite W .oneBlockTwoPorts => ∑ γ, coreW1 b (coreBlk x) γ * coreTr G γ) := by
  ext p q
  rcases p with ⟨a, α⟩ | ⟨j, α⟩ <;> rcases q with ⟨c, γ⟩ | ⟨k, γ⟩
  all_goals
    have ha : ∀ a' : Fin 1, a' = 0 := fun _ => Subsingleton.elim _ _
    simp [meqShift, diagonal_apply, coreBlk, coreTr, coreW1, Fintype.sum_sum_type,
      Fin.sum_univ_two, meqInc, LayerShape.incident, ha]
  all_goals (split_ifs <;> ring)

theorem core_shift_two {W : ℕ} (b : ℝ)
    (G : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) :
    meqShift .separate (1 - 2 * (b : ℂ)) b (physBlockTrace G) (portBlockTrace G) +
        (b : ℂ) • (physBlockTrace G 1 • meqPhysProj 0 + physBlockTrace G 0 • meqPhysProj 1) =
      diagonal (fun x : LayerSite W .separate => ∑ γ, coreW2 b (coreBlk x) γ * coreTr G γ) := by
  ext p q
  rcases p with ⟨a, α⟩ | ⟨j, α⟩ <;> rcases q with ⟨c, γ⟩ | ⟨k, γ⟩ <;>
    (try fin_cases a) <;> (try fin_cases j) <;>
    simp [meqShift, meqPhysProj, diagonal_apply, coreBlk, coreTr, coreW2, Fintype.sum_sum_type,
      Fin.sum_univ_two, meqInc, LayerShape.incident] <;>
    (try split_ifs) <;> (try simp_all) <;> ring

/-!
## 6. The gradient constant of the two-block core
-/

theorem core_subsum_le {W : ℕ} (g : LayerSite W .separate → ℝ) (hg : ∀ x, 0 ≤ g x) (a : Fin 2) :
    ∑ γ : Fin W, g (Sum.inl (a, γ)) ≤ ∑ x, g x := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  have h1 : ∑ γ : Fin W, g (Sum.inl (a, γ)) ≤ ∑ a' : Fin 2, ∑ γ : Fin W, g (Sum.inl (a', γ)) :=
    Finset.single_le_sum (f := fun a' : Fin 2 => ∑ γ : Fin W, g (Sum.inl (a', γ)))
      (fun _ _ => Finset.sum_nonneg fun _ _ => hg _) (Finset.mem_univ a)
  have h2 : 0 ≤ ∑ y : PortSite W .separate, g (Sum.inr y) := Finset.sum_nonneg fun _ _ => hg _
  linarith

theorem core_trace_bond_le {W : ℕ} (b : ℝ) (K : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ)
    (α γ : Fin W) (s : Fin 2) :
    ‖(K * coreLin W b (Pi.single (Sum.inl (α, γ, s)) 1)).trace‖ ^ 2 ≤
      2 * (‖K (Sum.inl ((1 : Fin 2), γ)) (Sum.inl ((0 : Fin 2), α))‖ ^ 2 +
        ‖K (Sum.inl ((0 : Fin 2), α)) (Sum.inl ((1 : Fin 2), γ))‖ ^ 2) := by
  rw [coreLin_inl]
  fin_cases s
  · simp only [Fin.zero_eta]
    rw [coreLb_single0, Matrix.mul_add, Matrix.trace_add, trace_mul_single, trace_mul_single]
    simp only [MulOpposite.op_one, one_smul]
    have := tfl_norm_sq_add_le (K (Sum.inl ((1 : Fin 2), γ)) (Sum.inl ((0 : Fin 2), α)))
      (K (Sum.inl ((0 : Fin 2), α)) (Sum.inl ((1 : Fin 2), γ))) 1 1 1 (by simp) (by simp)
    simpa using this
  · simp only [Fin.mk_one]
    rw [coreLb_single1, Matrix.mul_add, Matrix.trace_add, trace_mul_single, trace_mul_single]
    have := tfl_norm_sq_add_le (K (Sum.inl ((1 : Fin 2), γ)) (Sum.inl ((0 : Fin 2), α)))
      (K (Sum.inl ((0 : Fin 2), α)) (Sum.inl ((1 : Fin 2), γ))) Complex.I (-Complex.I) 1
      (by simp) (by simp)
    simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] at *
    convert this using 2
    ring

/-- **Weighted coordinate traces of the two-block core**: `Σᵢ vᵢ |Tr(K Λᵢ)|² ≤ 5² ‖K‖²`. -/
theorem core_weighted_le {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (K : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) :
    ∑ i, (coreVar W b i : ℝ) * ‖(K * coreLin W b (Pi.single i 1)).trace‖ ^ 2 ≤ 5 ^ 2 * ‖K‖ ^ 2 := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨hA, hB⟩ := tfl_TA_TB_le hW hb0 hb1
  have hB0 : (0 : ℝ) ≤ tflTB W b := (tflTB W b).2
  rw [Fintype.sum_sum_type]
  -- the layer coordinates
  have hlay : ∑ c : TflCoord W .separate, (coreVar W b (Sum.inr c) : ℝ) *
      ‖(K * coreLin W b (Pi.single (Sum.inr c) 1)).trace‖ ^ 2 ≤ 16 * ‖K‖ ^ 2 := by
    have e : ∀ c : TflCoord W .separate, (coreVar W b (Sum.inr c) : ℝ) *
        ‖(K * coreLin W b (Pi.single (Sum.inr c) 1)).trace‖ ^ 2 =
        (tflVar W b .separate c : ℝ) * ‖(K * tflLin W b .separate (Pi.single c 1)).trace‖ ^ 2 :=
      fun c => by rw [coreLin_inr]; rfl
    rw [Finset.sum_congr rfl fun c _ => e c]
    refine (tfl_weighted_trace_le W b .separate K).trans ?_
    have h2 := tfl_hs_le K
    have h3 := tfl_card_layerSite_le W .separate
    have hc : 2 * (tflTA W b : ℝ) + 2 * (tflTB W b : ℝ) ≤ 4 / W := by
      have : (4 : ℝ) / W = 2 * (1 / W) + 2 * (1 / W) := by ring
      rw [this]; linarith
    calc (2 * (tflTA W b : ℝ) + 2 * (tflTB W b : ℝ)) * ∑ x, ∑ y, ‖K x y‖ ^ 2
        ≤ (4 / W) * (4 * W * ‖K‖ ^ 2) := by
          gcongr
          exact h2.trans (mul_le_mul_of_nonneg_right h3 (by positivity))
      _ = 16 * ‖K‖ ^ 2 := by field_simp; ring
  -- the bond coordinates
  have hbond : ∑ c : CoreBetaCoord W, (coreVar W b (Sum.inl c) : ℝ) *
      ‖(K * coreLin W b (Pi.single (Sum.inl c) 1)).trace‖ ^ 2 ≤ 4 * ‖K‖ ^ 2 := by
    simp only [coreVar, Sum.elim_inl, NNReal.coe_div, NNReal.coe_ofNat]
    have hpt : ∀ c : CoreBetaCoord W, (tflTB W b : ℝ) / 2 *
        ‖(K * coreLin W b (Pi.single (Sum.inl c) 1)).trace‖ ^ 2 ≤
        (tflTB W b : ℝ) * (‖K (Sum.inl ((1 : Fin 2), c.2.1)) (Sum.inl ((0 : Fin 2), c.1))‖ ^ 2 +
          ‖K (Sum.inl ((0 : Fin 2), c.1)) (Sum.inl ((1 : Fin 2), c.2.1))‖ ^ 2) := by
      rintro ⟨α, γ, s⟩
      have := core_trace_bond_le b K α γ s
      nlinarith
    refine (Finset.sum_le_sum fun c _ => hpt c).trans ?_
    have hcol1 : ∀ α : Fin W,
        ∑ γ : Fin W, ‖K (Sum.inl ((1 : Fin 2), γ)) (Sum.inl ((0 : Fin 2), α))‖ ^ 2 ≤ ‖K‖ ^ 2 :=
      fun α => (core_subsum_le (fun x => ‖K x (Sum.inl ((0 : Fin 2), α))‖ ^ 2)
        (fun _ => by positivity) 1).trans (tfl_col_sq_le K _)
    have hrow : ∀ α : Fin W,
        ∑ γ : Fin W, ‖K (Sum.inl ((0 : Fin 2), α)) (Sum.inl ((1 : Fin 2), γ))‖ ^ 2 ≤ ‖K‖ ^ 2 := by
      intro α
      have h := (core_subsum_le (fun y => ‖Kᴴ y (Sum.inl ((0 : Fin 2), α))‖ ^ 2)
        (fun _ => by positivity) 1).trans (tfl_col_sq_le Kᴴ _)
      simpa [conjTranspose_apply, Matrix.l2_opNorm_conjTranspose] using h
    have hBW : (tflTB W b : ℝ) * W ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hB hW'.le
      rwa [one_div, inv_mul_cancel₀ hW'.ne'] at this
    rw [Fintype.sum_prod_type]
    calc ∑ α : Fin W, ∑ q : Fin W × Fin 2, (tflTB W b : ℝ) *
          (‖K (Sum.inl ((1 : Fin 2), (α, q).2.1)) (Sum.inl ((0 : Fin 2), (α, q).1))‖ ^ 2 +
            ‖K (Sum.inl ((0 : Fin 2), (α, q).1)) (Sum.inl ((1 : Fin 2), (α, q).2.1))‖ ^ 2)
        ≤ ∑ _α : Fin W, 4 * (tflTB W b : ℝ) * ‖K‖ ^ 2 := by
          refine Finset.sum_le_sum fun α _ => ?_
          rw [Fintype.sum_prod_type]
          simp only [Fin.sum_univ_two]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
          have := hcol1 α
          have := hrow α
          nlinarith
      _ = 4 * ((tflTB W b : ℝ) * W) * ‖K‖ ^ 2 := by simp; ring
      _ ≤ 4 * 1 * ‖K‖ ^ 2 := by gcongr
      _ = 4 * ‖K‖ ^ 2 := by ring
  nlinarith [sq_nonneg ‖K‖]

/-!
## 7. The two-block core in the layer frame: law, invertibility, moments
-/

/-- The law of (internal bond, `.separate` layer). -/
def coreLaw2 (W : ℕ) (b : ℝ) : Measure (Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate) :=
  (ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))).prod (layerLaw W b .separate)

instance core_isProbabilityMeasure_law2 (W : ℕ) (b : ℝ) : IsProbabilityMeasure (coreLaw2 W b) := by
  unfold coreLaw2; infer_instance

/-- The layer resolvent of the two-block core. -/
def coreG2 {W : ℕ} (E : ℝ) (z : ℂ) (q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate) :
    Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
  layerResolvent .separate E z (-coreOff q.1) q.2

theorem coreG2_embed (W : ℕ) (b E : ℝ) (z : ℂ) (x : CoreCoord W → ℝ) :
    coreG2 E z (coreEmbed W b x) = (coreC0 W E z + coreLin W b x)⁻¹ := by
  rw [coreG2, layerResolvent, core_matrix_eq]

theorem core_layerMatrix_eq {W : ℕ} (E : ℝ) (z : ℂ)
    (q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate) :
    layerMatrix .separate E z (-coreOff q.1) q.2 = layerMatrix .separate E z 0 q.2 + coreLb q.1 := by
  rw [layerMatrix, layerMatrix, coreLb, fromBlocks_add]
  congr 1 <;> abel

theorem measurable_coreOff (W : ℕ) :
    Measurable (fun β : Matrix (Fin W) (Fin W) ℂ => coreOff β) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  unfold coreOff
  split_ifs
  · exact pg_entry measurable_id _ _
  · exact continuous_star.measurable.comp (pg_entry measurable_id _ _)
  · exact measurable_const

theorem measurable_coreLayerMatrix {W : ℕ} (E : ℝ) (z : ℂ) :
    Measurable (fun q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate =>
      layerMatrix .separate E z (-coreOff q.1) q.2) := by
  have e : (fun q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate =>
      layerMatrix .separate E z (-coreOff q.1) q.2) =
      fun q => layerMatrix .separate E z 0 q.2 + coreLb q.1 :=
    funext fun q => core_layerMatrix_eq E z q
  rw [e]
  refine ((measurable_layerMatrix .separate E z 0).comp measurable_snd).add ?_
  have hc : Continuous (fun A : Matrix (PhysSite W .separate) (PhysSite W .separate) ℂ =>
      (fromBlocks A 0 0 0 : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ)) :=
    continuous_id.matrix_fromBlocks continuous_const continuous_const continuous_const
  exact hc.measurable.comp ((measurable_coreOff W).comp measurable_fst)

theorem measurable_coreG2 {W : ℕ} (E : ℝ) (z : ℂ) :
    Measurable (fun q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate => coreG2 E z q) :=
  measurable_matrix_inv.comp (measurable_coreLayerMatrix E z)

/-- **A.s. invertibility of the two-block core** (from `GaussianAbsorptionContract`, conditionally
on the internal bond). -/
theorem core_ae_unit2 {W : ℕ} {b E : ℝ} {z : ℂ}
    (h : ∀ X : Matrix (PhysSite W .separate) (PhysSite W .separate) ℂ, X.IsHermitian →
      ∀ᵐ ω ∂layerLaw W b .separate, IsUnit (layerMatrix .separate E z X ω).det) :
    ∀ᵐ q ∂coreLaw2 W b, IsUnit (layerMatrix .separate E z (-coreOff q.1) q.2).det := by
  have hmeas : MeasurableSet {q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate |
      IsUnit (layerMatrix .separate E z (-coreOff q.1) q.2).det} := by
    have hm : Measurable (fun q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate =>
        (layerMatrix .separate E z (-coreOff q.1) q.2).det) :=
      (continuous_id.matrix_det).measurable.comp (measurable_coreLayerMatrix E z)
    have : {q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate |
        IsUnit (layerMatrix .separate E z (-coreOff q.1) q.2).det} =
        (fun q => (layerMatrix .separate E z (-coreOff q.1) q.2).det) ⁻¹' {0}ᶜ := by
      ext q; simp [isUnit_iff_ne_zero]
    rw [this]
    exact hm (measurableSet_singleton 0).compl
  have hfib : ∀ β : Matrix (Fin W) (Fin W) ℂ, ∀ᵐ y ∂layerLaw W b .separate,
      IsUnit (layerMatrix .separate E z (-coreOff (β, y).1) (β, y).2).det :=
    fun β => h (-coreOff β) (coreOff_isHermitian β).neg
  rw [coreLaw2]
  exact core_ae_prod (ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)))
    (layerLaw W b .separate) hmeas hfib

/-- **Moments of the two-block core resolvent** (uniformity of the absorber bound in `X`). -/
theorem core_mom2 {W : ℕ} {b E : ℝ} {z : ℂ} {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ∞) {C : ℝ}
    (h : ∀ X : Matrix (PhysSite W .separate) (PhysSite W .separate) ℂ, X.IsHermitian →
      eLpNorm (fun ω => ‖layerResolvent .separate E z X ω‖) q (layerLaw W b .separate) ≤
        ENNReal.ofReal C) :
    eLpNorm (fun r => ‖coreG2 E z r‖) q (coreLaw2 W b) ≤ ENNReal.ofReal C := by
  rw [coreLaw2]
  have hfib : ∀ β : Matrix (Fin W) (Fin W) ℂ,
      eLpNorm (fun y => ‖coreG2 E z (β, y)‖) q (layerLaw W b .separate) ≤ ENNReal.ofReal C := by
    intro β
    have := h (-coreOff β) (coreOff_isHermitian β).neg
    unfold coreG2
    exact this
  exact core_eLpNorm_prod_le (ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)))
    (layerLaw W b .separate) (f := fun r => ‖coreG2 E z r‖) (measurable_coreG2 E z).norm hq0 hqt
    hfib

/-!
## 8. Mean identity and fluctuations of the two-block core
-/

theorem core_ae_coords {W : ℕ} {b E : ℝ} {z : ℂ}
    (hinv : ∀ᵐ q ∂coreLaw2 W b, IsUnit (layerMatrix .separate E z (-coreOff q.1) q.2).det) :
    ∀ᵐ x ∂gaussianProduct (coreVar W b), IsUnit (coreC0 W E z + coreLin W b x).det := by
  rw [coreLaw2, core_law_eq_map] at hinv
  have := ae_of_ae_map (core_measurable_embed W b).aemeasurable hinv
  filter_upwards [this] with x hx
  rwa [core_matrix_eq]

/-- **The Schwinger–Dyson identity of the two-block core** (the vector Dyson equation for `S₄`,
Bochner form): IBP in the layer coordinates and in the internal bond. -/
theorem core_mean2 {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (E : ℝ) {z : ℂ}
    (hz : 0 ≤ z.im)
    (hinv : ∀ᵐ q ∂coreLaw2 W b, IsUnit (layerMatrix .separate E z (-coreOff q.1) q.2).det)
    (hG2 : Integrable (fun q => ‖coreG2 E z q‖ ^ 2) (coreLaw2 W b)) :
    diagonal (fun x => coreH (σ := .separate) E z (coreBlk x)) * ∫ q, coreG2 E z q ∂coreLaw2 W b -
      ∫ q, diagonal (fun x : LayerSite W .separate => ∑ γ, coreW2 b (coreBlk x) γ *
        coreTr (coreG2 E z q) γ) * coreG2 E z q ∂coreLaw2 W b = 1 := by
  have hΦ := core_measurable_embed W b
  have hm := measurable_coreG2 (W := W) E z
  have hinvC := core_ae_coords hinv
  have hG2C : Integrable (fun x => ‖(coreC0 W E z + coreLin W b x)⁻¹‖ ^ 2)
      (gaussianProduct (coreVar W b)) := by
    rw [coreLaw2, core_law_eq_map, integrable_map_measure
      (g := fun q => ‖coreG2 E z q‖ ^ 2)
      ((continuous_norm.pow 2).measurable.comp hm).aestronglyMeasurable hΦ.aemeasurable] at hG2
    refine hG2.congr (ae_of_all _ fun x => ?_)
    simp only [Function.comp_apply, coreG2_embed]
  have key := core_limit_identity (coreVar W b) (core_reg W b E hz) hinvC hG2C
  have hc : Continuous (fun M : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ =>
      diagonal (fun x : LayerSite W .separate => ∑ γ, coreW2 b (coreBlk x) γ * coreTr M γ) * M) := by
    refine Continuous.mul ?_ continuous_id
    refine continuous_pi fun x => continuous_pi fun y => ?_
    simp only [diagonal_apply]
    split_ifs
    · exact continuous_finsetSum _ fun γ _ => continuous_const.mul
        (core_continuous_tr (W := W) (σ := .separate) γ)
    · exact continuous_const
  rw [coreLaw2, core_law_eq_map, integral_map hΦ.aemeasurable hm.aestronglyMeasurable,
    integral_map (f := fun q => diagonal (fun x : LayerSite W .separate => ∑ γ, coreW2 b (coreBlk x) γ *
        coreTr (coreG2 E z q) γ) * coreG2 E z q) hΦ.aemeasurable
      (hc.measurable.comp hm).aestronglyMeasurable]
  simp only [coreG2_embed]
  rw [← core_tflConst_eq]
  have e : (fun x : CoreCoord W → ℝ =>
      (diagonal fun y : LayerSite W .separate => ∑ γ, coreW2 b (coreBlk y) γ *
        coreTr (coreC0 W E z + (coreLin W b) x)⁻¹ γ) * (coreC0 W E z + (coreLin W b) x)⁻¹) =
      fun x => coreS (coreVar W b) (coreLin W b) (coreC0 W E z + (coreLin W b) x)⁻¹ *
        (coreC0 W E z + (coreLin W b) x)⁻¹ := by
    funext x
    rw [coreS_eq hW hb0.le hb1.le, core_shift_two]
  rw [e]
  exact key

/-- **Fluctuation of the block traces of the two-block core** (Gaussian `L^p` gradient
inequality in all coordinates, internal bond included). -/
theorem core_fluct2 {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
        eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
            (gaussianProduct v) ≤
          ENNReal.ofReal (Cg * Real.sqrt p) *
            eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v))
    {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (E : ℝ) {z : ℂ} (hz : 0 ≤ z.im)
    {p : ℝ} (hp : 1 ≤ p) {CA : ℝ} (hCA : 0 ≤ CA)
    (hinv : ∀ᵐ q ∂coreLaw2 W b, IsUnit (layerMatrix .separate E z (-coreOff q.1) q.2).det)
    (hmom : eLpNorm (fun q => ‖coreG2 E z q‖) (ENNReal.ofReal (2 * p)) (coreLaw2 W b) ≤
      ENNReal.ofReal CA)
    (β : Fin LayerShape.separate.blocks ⊕ Fin LayerShape.separate.ports) :
    eLpNorm (fun q => coreTr (coreG2 E z q) β - ∫ q', coreTr (coreG2 E z q') β ∂coreLaw2 W b)
        (ENNReal.ofReal p) (coreLaw2 W b) ≤
      ENNReal.ofReal (20 * Cg * CA ^ 2 * Real.sqrt p / W) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hΦ := core_measurable_embed W b
  have hm := measurable_coreG2 (W := W) E z
  have hinvC := core_ae_coords hinv
  have hmomC : eLpNorm (fun x => ‖(coreC0 W E z + coreLin W b x)⁻¹‖) (ENNReal.ofReal (2 * p))
      (gaussianProduct (coreVar W b)) ≤ ENNReal.ofReal CA := by
    rw [coreLaw2, core_law_eq_map, eLpNorm_map_measure hm.norm.aestronglyMeasurable
      hΦ.aemeasurable] at hmom
    refine le_of_eq_of_le ?_ hmom
    congr 1
    funext x
    simp only [Function.comp_apply, coreG2_embed]
  have h := core_fluctuation (coreVar W b) hCg hgr (core_reg W b E hz) (by norm_num : (0 : ℝ) ≤ 5)
    (core_weighted_le hW hb0 hb1) (W : ℝ)⁻¹ (coreProj β) hp hCA hinvC hmomC
  have htr : ∀ M : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ,
      (((W : ℝ)⁻¹ : ℝ) : ℂ) * (coreProj β * M).trace = coreTr M β := fun M => by
    rw [core_tr_eq_trace]; push_cast; rfl
  have hcm : Measurable (fun q => coreTr (coreG2 E z q) β) :=
    (core_continuous_tr β).measurable.comp hm
  rw [coreLaw2, core_law_eq_map, integral_map hΦ.aemeasurable hcm.aestronglyMeasurable,
    eLpNorm_map_measure (hcm.sub_const _).aestronglyMeasurable hΦ.aemeasurable]
  simp only [htr] at h
  refine le_trans (le_of_eq ?_) (h.trans (ENNReal.ofReal_le_ofReal ?_))
  · congr 1
    funext x
    simp only [Function.comp_apply, coreG2_embed]
  · have hD := core_norm_proj_le (W := W) β
    have hsp := Real.sqrt_nonneg p
    rw [abs_of_pos (inv_pos.mpr hW')]
    calc Cg * Real.sqrt p * (4 * (W : ℝ)⁻¹ * 5 * ‖coreProj β‖) * CA ^ 2
        ≤ Cg * Real.sqrt p * (4 * (W : ℝ)⁻¹ * 5 * 1) * CA ^ 2 := by gcongr
      _ = 20 * Cg * CA ^ 2 * Real.sqrt p / W := by field_simp; ring

/-!
## 9. Transfer to the path law
-/

/-- The observable of the `path` clause. -/
def coreObs {W r : ℕ} (b E : ℝ) (ω : PathSample W r) : ℝ :=
  max ‖blockTrace (pathPortResolvent b E ω) 0 - matchedA E‖
    ‖blockTrace (pathPortResolvent b E ω) 1 - matchedA E‖

theorem measurable_coreObs (W r : ℕ) (b E : ℝ) :
    Measurable (fun ω : PathSample W r => coreObs b E ω) := by
  have hR : Measurable (fun ω : PathSample W r => pathPortResolvent b E ω) :=
    measurable_matrix_inv.comp (measurable_const.sub (measurable_pathSchur W r E))
  have hc : ∀ j : Fin 2, Continuous
      (fun M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => ‖blockTrace M j - matchedA E‖) := by
    intro j
    unfold blockTrace
    fun_prop
  exact ((hc 0).measurable.comp hR).max ((hc 1).measurable.comp hR)

/-- **Transfer**: a bound on the layer-frame observable gives the `path` bound. -/
theorem core_transfer {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {W r : ℕ} {b E : ℝ}
    (Φ : Ω → PathSample W r) (hΦ : MeasurePreserving Φ μ (pathLaw W r b)) (F : Ω → ℝ)
    (hF : ∀ᵐ q ∂μ, coreObs b E (Φ q) = F q) (p : ℝ≥0∞) {B : ℝ≥0∞} (hB : eLpNorm F p μ ≤ B) :
    eLpNorm (fun ω => max ‖blockTrace (pathPortResolvent b E ω) 0 - matchedA E‖
        ‖blockTrace (pathPortResolvent b E ω) 1 - matchedA E‖) p (pathLaw W r b) ≤ B := by
  change eLpNorm (fun ω => coreObs b E ω) p (pathLaw W r b) ≤ B
  rw [← hΦ.map_eq, eLpNorm_map_measure (measurable_coreObs W r b E).aestronglyMeasurable
    hΦ.measurable.aemeasurable]
  rw [eLpNorm_congr_ae (f := (fun ω => coreObs b E ω) ∘ Φ) (g := F) (hF.mono fun q hq => hq)]
  exact hB

/-!
## 10. The two-block core: the matched-traces theorem for `r = 2`
-/

/-- Absolute row sums of the `S₄` weights are at most one. -/
theorem coreW2_rowsum {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (β : Fin 2 ⊕ Fin 2) :
    ∑ γ, ‖coreW2 b β γ‖ ≤ 1 := by
  have hc : ‖(1 - 2 * (b : ℂ))‖ = 1 - 2 * b := by
    rw [show (1 - 2 * (b : ℂ)) = ((1 - 2 * b : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hb : |b| = b := abs_of_nonneg hb0
  rcases β with a | a <;> fin_cases a <;>
    simp [coreW2, Fintype.sum_sum_type, Fin.sum_univ_two] <;> rw [hb] <;> (try rw [hc]) <;>
    linarith

/-- **The matched-traces theorem, `path` clause, two-block core (`r = 2`).** -/
theorem coreTraces_two (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : Internal.Contracts.Inputs.GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∃ ε₀ C : ℝ, 0 < ε₀ ∧
      ∀ (W : ℕ), 0 < W → ∀ p : ℝ, 2 ≤ p → p ≤ ε₀ * W → ∀ E ∈ bulkInterval κ,
        eLpNorm (fun ω => max ‖blockTrace (pathPortResolvent b E ω) 0 - matchedA E‖
            ‖blockTrace (pathPortResolvent b E ω) 1 - matchedA E‖)
          (ENNReal.ofReal p) (pathLaw W 2 b) ≤ ENNReal.ofReal (C * Real.sqrt p / W) := by
  intro b hb0 hb1 κ hκ
  by_cases hex : ∃ E₀, E₀ ∈ bulkInterval κ
  swap
  · exact ⟨1, 0, one_pos, fun W _ p _ _ E hE => absurd ⟨E, hE⟩ hex⟩
  obtain ⟨E₀, hE₀⟩ := hex
  have hb1' : b < 1 := by linarith
  have hζ : 0 < coreZeta b κ := (core_matched_facts hb0.le hb1' hκ hE₀).2.2.1
  obtain ⟨ε₁, CA, hε₁, hCA, habs⟩ :=
    gaussianAbsorption_holds hcount b hb0 hb1 (coreZeta b κ) 3 hζ
  obtain ⟨Cg, hCg, hgr⟩ := hgrad
  obtain ⟨εD, CD, hεD, hCD, hdys⟩ := coreDyson_two hb0 hb1 hκ hCA
  set Cf := 20 * Cg * CA ^ 2 with hCf
  have hCf0 : 0 ≤ Cf := by positivity
  refine ⟨min (ε₁ / 2) (εD / (Cf ^ 2 + 1)), 2 * Cf + 2 * CD * Cf ^ 2,
    lt_min (by positivity) (by positivity), ?_⟩
  intro W hW p hp2 hpε E hE
  obtain ⟨hE2, hz3, -, hzim, hna, ha, haz⟩ := core_matched_facts hb0.le hb1' hκ hE
  have hz0 : 0 ≤ (boundaryZ b E).im := hζ.le.trans hzim
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hpW1 : p ≤ ε₁ / 2 * W := hpε.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hW'.le)
  have hpW2 : p ≤ εD / (Cf ^ 2 + 1) * W :=
    hpε.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hW'.le)
  have h2p : 2 * p ≤ ε₁ * W := by linarith
  -- absorption facts
  have hXa := fun (X : Matrix (PhysSite W .separate) (PhysSite W .separate) ℂ) (hX : X.IsHermitian) =>
    habs W hW .separate X hX E (boundaryZ b E) hzim hz3
  have hinv := core_ae_unit2 (W := W) (b := b) (E := E) (z := boundaryZ b E)
    fun X hX => (hXa X hX).1
  have hmom : ∀ q : ℝ, 1 ≤ q → q ≤ ε₁ * W →
      eLpNorm (fun r => ‖coreG2 E (boundaryZ b E) r‖) (ENNReal.ofReal q) (coreLaw2 W b) ≤
        ENNReal.ofReal CA := fun q hq1 hq2 =>
    core_mom2 (by simp; linarith) ENNReal.ofReal_ne_top fun X hX => (hXa X hX).2 q hq1 hq2
  have hGm : AEStronglyMeasurable (coreG2 (W := W) E (boundaryZ b E)) (coreLaw2 W b) :=
    (measurable_coreG2 E _).aestronglyMeasurable
  have hG2 : Integrable (fun r => ‖coreG2 E (boundaryZ b E) r‖ ^ 2) (coreLaw2 W b) := by
    have h := hmom 2 one_le_two (by linarith)
    rw [show ENNReal.ofReal 2 = 2 by simp] at h
    exact (memLp_two_iff_integrable_sq hGm.norm).mp (memLp_iff.mpr (lt_of_le_of_lt h ENNReal.ofReal_lt_top))
  have hfl : ∀ β, ∀ q : ℝ, 1 ≤ q → 2 * q ≤ ε₁ * W →
      eLpNorm (fun r => coreTr (coreG2 E (boundaryZ b E) r) β -
        ∫ r', coreTr (coreG2 E (boundaryZ b E) r') β ∂coreLaw2 W b) (ENNReal.ofReal q)
        (coreLaw2 W b) ≤ ENNReal.ofReal (Cf * Real.sqrt q / W) := fun β q hq1 hq2 =>
    core_fluct2 hCg.le hgr hW hb0 hb1 E hz0 hq1 hCA.le hinv (hmom (2 * q) (by linarith) hq2) β
  -- covariances
  set A := Cf * Real.sqrt 2 / W with hA
  have hA0 : 0 ≤ A := by positivity
  have hfl2 : ∀ β, eLpNorm (fun r => coreTr (coreG2 E (boundaryZ b E) r) β -
      ∫ r', coreTr (coreG2 E (boundaryZ b E) r') β ∂coreLaw2 W b) 2 (coreLaw2 W b) ≤
      ENNReal.ofReal A := fun β => by
    have h := hfl β 2 one_le_two (by linarith)
    rwa [show ENNReal.ofReal 2 = 2 by simp] at h
  have hcov := core_cov_tr hGm hG2 hA0 hfl2
  -- the vector Dyson equation `S₄`
  have hvd := core_vector_dyson hW hGm hG2 (coreH E (boundaryZ b E)) (coreW2 b)
    (core_mean2 hW hb0 hb1 E hz0 hinv hG2)
  set m : Fin 2 ⊕ Fin 2 → ℂ := fun β => ∫ r, coreTr (coreG2 E (boundaryZ b E) r) β ∂coreLaw2 W b
    with hm
  set e : Fin 2 ⊕ Fin 2 → ℂ := fun β => ∑ γ, coreW2 b β γ *
    ((∫ r, coreTr (coreG2 E (boundaryZ b E) r) γ * coreTr (coreG2 E (boundaryZ b E) r) β
      ∂coreLaw2 W b) - m γ * m β) with he
  have hele : ∀ β, ‖e β‖ ≤ A * A := fun β =>
    core_resid_le _ _ (coreW2_rowsum hb0.le hb1.le β) (fun γ => hcov γ β) (by positivity)
  have heq : ∀ β : Fin 2 ⊕ Fin 2,
      (coreH (σ := .separate) E (boundaryZ b E) β - ∑ γ, coreW2 b β γ * m γ) * m β = 1 + e β :=
    fun β => hvd β
  -- signs and bounds
  have hherm : ∀ᵐ r ∂coreLaw2 W b, ∀ j, (r.2.1 j).IsHermitian := by
    rw [coreLaw2]
    exact (Measure.quasiMeasurePreserving_snd).ae (lct_ae_blocks_isHermitian W b .separate)
  have him : ∀ a : Fin 2, (m (Sum.inl a)).im ≤ 0 := fun a => by
    refine lct_im_integral_nonpos ?_
    filter_upwards [hherm] with r hr
    exact lct_im_physBlockTrace_nonpos E hz0 (coreOff_isHermitian r.1).neg r.2 hr a
  have hmK : ∀ β, ‖m β‖ ≤ CA := fun β => by
    have h := hmom 1 le_rfl (by nlinarith)
    rw [ENNReal.ofReal_one] at h
    exact core_norm_mean_le hGm hCA.le h β
  -- residual size
  have hAA : A * A = 2 * Cf ^ 2 / W ^ 2 := by
    rw [hA, div_mul_div_comm, mul_mul_mul_comm, Real.mul_self_sqrt (by norm_num)]
    ring
  have hεle : A * A ≤ εD := by
    have h1 : 2 * (Cf ^ 2 + 1) ≤ εD * W := by
      have := hpW2
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
      nlinarith
    rw [hAA, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hW1 (by positivity : (0 : ℝ) ≤ εD * W)]
  -- the deterministic stability of `S₄`
  have hm0 := heq (Sum.inl 0)
  have hm1 := heq (Sum.inl 1)
  have hu0 := heq (Sum.inr 0)
  have hu1 := heq (Sum.inr 1)
  simp only [coreH, coreW2, Fintype.sum_sum_type, Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr,
    Fin.isValue] at hm0 hm1 hu0 hu1
  norm_num at hm0 hm1 hu0 hu1
  obtain ⟨-, -, hd0, hd1⟩ := hdys E hE (m (Sum.inl 0)) (m (Sum.inl 1)) (m (Sum.inr 0))
    (m (Sum.inr 1)) (e (Sum.inl 0)) (e (Sum.inl 1)) (e (Sum.inr 0)) (e (Sum.inr 1)) (A * A)
    (him 0) (him 1) (hmK _) (hmK _) (hele _) (hele _) (hele _) (hele _) hεle
    (by push_cast; linear_combination hm0) (by push_cast; linear_combination hm1)
    (by linear_combination hu0) (by linear_combination hu1)
  -- the final bound in the layer frame
  have hp1 : 1 ≤ p := by linarith
  have hfin := core_final (ν := coreLaw2 W b) hp1
    (((core_continuous_tr (W := W) (σ := .separate) (Sum.inr 0)).comp_aestronglyMeasurable hGm))
    (((core_continuous_tr (W := W) (σ := .separate) (Sum.inr 1)).comp_aestronglyMeasurable hGm))
    (m (Sum.inr 0)) (m (Sum.inr 1)) (matchedA E) (by positivity) (by positivity)
    (hfl (Sum.inr 0) p hp1 h2p) (hfl (Sum.inr 1) p hp1 h2p) hd0 hd1
  refine core_transfer coreTwo (coreTwo_measurePreserving W b)
    (fun r => max ‖coreTr (coreG2 E (boundaryZ b E) r) (Sum.inr 0) - matchedA E‖
      ‖coreTr (coreG2 E (boundaryZ b E) r) (Sum.inr 1) - matchedA E‖) ?_ _ (hfin.trans ?_)
  · have hH := (coreTwo_measurePreserving W b).quasiMeasurePreserving.ae
      (ae_isUnit_det_pathMatrix W 2 hb1 E)
    filter_upwards [hH] with r hr
    have hr' : IsUnit (Internal.Contracts.Layers.blockDiag r.2.1 - (E : ℂ) • 1 -
        -coreOff r.1).det := by
      rw [coreTwo_pathMatrix] at hr
      convert hr using 2
      abel
    unfold coreObs
    rw [coreTwo_portResolvent b E r hr']
    rfl
  · refine ENNReal.ofReal_le_ofReal ?_
    have hsp : 1 ≤ Real.sqrt p := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
    have hBle : CD * (A * A) ≤ 2 * CD * Cf ^ 2 * Real.sqrt p / W := by
      have hWinv : (W : ℝ)⁻¹ ≤ Real.sqrt p := (inv_le_one_of_one_le₀ hW1).trans hsp
      have h0 : 0 ≤ 2 * CD * Cf ^ 2 / W := by positivity
      calc CD * (A * A) = 2 * CD * Cf ^ 2 / W * (W : ℝ)⁻¹ := by rw [hAA]; field_simp
        _ ≤ 2 * CD * Cf ^ 2 / W * Real.sqrt p := mul_le_mul_of_nonneg_left hWinv h0
        _ = 2 * CD * Cf ^ 2 * Real.sqrt p / W := by ring
    calc 2 * (Cf * Real.sqrt p / W) + CD * (A * A)
        ≤ 2 * (Cf * Real.sqrt p / W) + 2 * CD * Cf ^ 2 * Real.sqrt p / W := by gcongr
      _ = (2 * Cf + 2 * CD * Cf ^ 2) * Real.sqrt p / W := by ring

/-!
## 11. The one-block core: the matched-traces theorem for `r = 1`
-/

/-- Absolute row sums of the `S₃` weights are at most one. -/
theorem coreW1_rowsum {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (β : Fin 1 ⊕ Fin 2) :
    ∑ γ, ‖coreW1 b β γ‖ ≤ 1 := by
  have hc : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0]
  rcases β with a | a <;>
    simp only [coreW1, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_two, hc, hb,
      norm_zero] <;> linarith

/-- The mean identity of the one-block core (layer Schwinger–Dyson with `X = 0`). -/
theorem core_mean1 {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (E : ℝ) {z : ℂ}
    (hz : 0 ≤ z.im)
    (hinv : ∀ᵐ ω ∂layerLaw W b .oneBlockTwoPorts, IsUnit (layerMatrix .oneBlockTwoPorts E z 0 ω).det)
    (hG2 : Integrable (fun ω => ‖layerResolvent .oneBlockTwoPorts E z 0 ω‖ ^ 2)
      (layerLaw W b .oneBlockTwoPorts)) :
    diagonal (fun x => coreH (σ := .oneBlockTwoPorts) E z (coreBlk x)) *
        ∫ ω, layerResolvent .oneBlockTwoPorts E z 0 ω ∂layerLaw W b .oneBlockTwoPorts -
      ∫ ω, diagonal (fun x : LayerSite W .oneBlockTwoPorts => ∑ γ, coreW1 b (coreBlk x) γ *
        coreTr (layerResolvent .oneBlockTwoPorts E z 0 ω) γ) *
          layerResolvent .oneBlockTwoPorts E z 0 ω ∂layerLaw W b .oneBlockTwoPorts = 1 := by
  have key := meq_limit_law b .oneBlockTwoPorts E (X := 0) (Matrix.isHermitian_zero) hz hinv hG2
  rw [← core_tflConst_eq]
  have e : (fun ω => (diagonal fun x : LayerSite W .oneBlockTwoPorts => ∑ γ, coreW1 b (coreBlk x) γ *
        coreTr (layerResolvent .oneBlockTwoPorts E z 0 ω) γ) *
          layerResolvent .oneBlockTwoPorts E z 0 ω) =
      fun ω => meqS W b .oneBlockTwoPorts (layerResolvent .oneBlockTwoPorts E z 0 ω) *
        layerResolvent .oneBlockTwoPorts E z 0 ω := by
    funext ω
    rw [meqS_eq hW, meq_coefA hW hb1.le, meq_coefB hW hb0.le, core_shift_one]
  rw [e]
  exact key

/-- **The matched-traces theorem, `path` clause, one-block core (`r = 1`).** -/
theorem coreTraces_one (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : Internal.Contracts.Inputs.GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∃ ε₀ C : ℝ, 0 < ε₀ ∧
      ∀ (W : ℕ), 0 < W → ∀ p : ℝ, 2 ≤ p → p ≤ ε₀ * W → ∀ E ∈ bulkInterval κ,
        eLpNorm (fun ω => max ‖blockTrace (pathPortResolvent b E ω) 0 - matchedA E‖
            ‖blockTrace (pathPortResolvent b E ω) 1 - matchedA E‖)
          (ENNReal.ofReal p) (pathLaw W 1 b) ≤ ENNReal.ofReal (C * Real.sqrt p / W) := by
  intro b hb0 hb1 κ hκ
  by_cases hex : ∃ E₀, E₀ ∈ bulkInterval κ
  swap
  · exact ⟨1, 0, one_pos, fun W _ p _ _ E hE => absurd ⟨E, hE⟩ hex⟩
  obtain ⟨E₀, hE₀⟩ := hex
  have hb1' : b < 1 := by linarith
  have hζ : 0 < coreZeta b κ := (core_matched_facts hb0.le hb1' hκ hE₀).2.2.1
  have habs0 := gaussianAbsorption_holds hcount
  obtain ⟨ε₁, CA, hε₁, hCA, habs⟩ := habs0 b hb0 hb1 (coreZeta b κ) 3 hζ
  obtain ⟨ε₃, Cf0, hε₃, hfluct⟩ := traceFluctuation_holds hgrad habs0 b hb0 hb1 (coreZeta b κ) 3 hζ 1
  obtain ⟨εD, CD, hεD, hCD, hdys⟩ := coreDyson_one hb0 hb1 hκ hCA
  set Cf := max Cf0 0 with hCf
  have hCf0 : 0 ≤ Cf := le_max_right _ _
  refine ⟨min (min ε₁ ε₃) (εD / (Cf ^ 2 + 1)), 2 * Cf + 2 * CD * Cf ^ 2,
    lt_min (lt_min hε₁ hε₃) (by positivity), ?_⟩
  intro W hW p hp2 hpε E hE
  obtain ⟨hE2, hz3, -, hzim, hna, ha, haz⟩ := core_matched_facts hb0.le hb1' hκ hE
  have hz0 : 0 ≤ (boundaryZ b E).im := hζ.le.trans hzim
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hpW1 : p ≤ ε₁ * W := hpε.trans (mul_le_mul_of_nonneg_right
    ((min_le_left _ _).trans (min_le_left _ _)) hW'.le)
  have hpW3 : p ≤ ε₃ * W := hpε.trans (mul_le_mul_of_nonneg_right
    ((min_le_left _ _).trans (min_le_right _ _)) hW'.le)
  have hpW2 : p ≤ εD / (Cf ^ 2 + 1) * W :=
    hpε.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hW'.le)
  set μ := layerLaw W b .oneBlockTwoPorts with hμ
  set G : LayerSample W .oneBlockTwoPorts → Matrix (LayerSite W .oneBlockTwoPorts)
    (LayerSite W .oneBlockTwoPorts) ℂ := layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0
    with hGdef
  have hμP : IsProbabilityMeasure μ := pg_isProbabilityMeasure_layerLaw W b .oneBlockTwoPorts
  obtain ⟨hinv, hmom⟩ := habs W hW .oneBlockTwoPorts 0 Matrix.isHermitian_zero E (boundaryZ b E)
    hzim hz3
  have hGm : AEStronglyMeasurable G μ :=
    (measurable_layerResolvent .oneBlockTwoPorts E _ 0).aestronglyMeasurable
  have hG2 : Integrable (fun ω => ‖G ω‖ ^ 2) μ := by
    have h := hmom 2 one_le_two (by linarith)
    rw [show ENNReal.ofReal 2 = 2 by simp] at h
    exact (memLp_two_iff_integrable_sq hGm.norm).mp
      (memLp_iff.mpr (lt_of_le_of_lt h ENNReal.ofReal_lt_top))
  have hfl : ∀ β, ∀ q : ℝ, 2 ≤ q → q ≤ ε₃ * W →
      eLpNorm (fun ω => coreTr (G ω) β - ∫ ω', coreTr (G ω') β ∂μ) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (Cf * Real.sqrt q / W) := by
    intro β q hq2 hq3
    have h := hfluct W hW .oneBlockTwoPorts 0 Matrix.isHermitian_zero E (boundaryZ b E) hzim hz3
      (coreProj β) (core_norm_proj_le β) q hq2 hq3
    have htr : ∀ M : Matrix (LayerSite W .oneBlockTwoPorts) (LayerSite W .oneBlockTwoPorts) ℂ,
        (W : ℂ)⁻¹ * (coreProj β * M).trace = coreTr M β := fun M => (core_tr_eq_trace M β).symm
    simp only [htr] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have := Real.sqrt_nonneg q
    gcongr
    exact le_max_left _ _
  -- covariances
  set A := Cf * Real.sqrt 2 / W with hA
  have hA0 : 0 ≤ A := by positivity
  have hfl2 : ∀ β, eLpNorm (fun ω => coreTr (G ω) β - ∫ ω', coreTr (G ω') β ∂μ) 2 μ ≤
      ENNReal.ofReal A := fun β => by
    have h := hfl β 2 le_rfl (by linarith)
    rwa [show ENNReal.ofReal 2 = 2 by simp] at h
  have hcov := core_cov_tr hGm hG2 hA0 hfl2
  have hvd := core_vector_dyson hW hGm hG2 (coreH E (boundaryZ b E)) (coreW1 b)
    (core_mean1 hW hb0 hb1 E hz0 hinv hG2)
  set m : Fin 1 ⊕ Fin 2 → ℂ := fun β => ∫ ω, coreTr (G ω) β ∂μ with hm
  set e : Fin 1 ⊕ Fin 2 → ℂ := fun β => ∑ γ, coreW1 b β γ *
    ((∫ ω, coreTr (G ω) γ * coreTr (G ω) β ∂μ) - m γ * m β) with he
  have hele : ∀ β, ‖e β‖ ≤ A * A := fun β =>
    core_resid_le _ _ (coreW1_rowsum hb0.le hb1.le β) (fun γ => hcov γ β) (by positivity)
  have heq : ∀ β : Fin 1 ⊕ Fin 2,
      (coreH (σ := .oneBlockTwoPorts) E (boundaryZ b E) β - ∑ γ, coreW1 b β γ * m γ) * m β =
        1 + e β := fun β => hvd β
  have him : (m (Sum.inl 0)).im ≤ 0 := lct_im_meanA_nonpos E hz0 Matrix.isHermitian_zero 0
  have hmK : ∀ β, ‖m β‖ ≤ CA := fun β => by
    have h := hmom 1 le_rfl (by linarith)
    rw [ENNReal.ofReal_one] at h
    exact core_norm_mean_le hGm hCA.le h β
  have hAA : A * A = 2 * Cf ^ 2 / W ^ 2 := by
    rw [hA, div_mul_div_comm, mul_mul_mul_comm, Real.mul_self_sqrt (by norm_num)]
    ring
  have hεle : A * A ≤ εD := by
    have h1 : 2 * (Cf ^ 2 + 1) ≤ εD * W := by
      have := hpW2
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
      nlinarith
    rw [hAA, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hW1 (by positivity : (0 : ℝ) ≤ εD * W)]
  have hm0 := heq (Sum.inl 0)
  have hu0 := heq (Sum.inr 0)
  have hu1 := heq (Sum.inr 1)
  simp only [coreH, coreW1, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_two,
    Sum.elim_inl, Sum.elim_inr, zero_mul, add_zero] at hm0 hu0 hu1
  obtain ⟨-, hd0, hd1⟩ := hdys E hE (m (Sum.inl 0)) (m (Sum.inr 0)) (m (Sum.inr 1))
    (e (Sum.inl 0)) (e (Sum.inr 0)) (e (Sum.inr 1)) (A * A) him (hmK _) (hele _) (hele _)
    (hele _) hεle (by linear_combination hm0) (by linear_combination hu0)
    (by linear_combination hu1)
  have hp1 : 1 ≤ p := by linarith
  have hfin := core_final (ν := μ) hp1
    (((core_continuous_tr (W := W) (σ := .oneBlockTwoPorts) (Sum.inr 0)).comp_aestronglyMeasurable hGm))
    (((core_continuous_tr (W := W) (σ := .oneBlockTwoPorts) (Sum.inr 1)).comp_aestronglyMeasurable hGm))
    (m (Sum.inr 0)) (m (Sum.inr 1)) (matchedA E) (by positivity) (by positivity)
    (hfl (Sum.inr 0) p hp2 hpW3) (hfl (Sum.inr 1) p hp2 hpW3) hd0 hd1
  refine core_transfer coreOne (coreOne_measurePreserving W b)
    (fun ω => max ‖coreTr (G ω) (Sum.inr 0) - matchedA E‖
      ‖coreTr (G ω) (Sum.inr 1) - matchedA E‖) ?_ _ (hfin.trans ?_)
  · have hH := (coreOne_measurePreserving W b).quasiMeasurePreserving.ae
      (ae_isUnit_det_pathMatrix W 1 hb1 E)
    filter_upwards [hH] with ω hω
    have hω' : IsUnit (Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1 - 0).det := by
      rw [coreOne_pathMatrix] at hω
      rwa [sub_zero]
    unfold coreObs
    rw [coreOne_portResolvent b E ω hω']
    rfl
  · refine ENNReal.ofReal_le_ofReal ?_
    have hsp : 1 ≤ Real.sqrt p := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
    have hBle : CD * (A * A) ≤ 2 * CD * Cf ^ 2 * Real.sqrt p / W := by
      have hWinv : (W : ℝ)⁻¹ ≤ Real.sqrt p := (inv_le_one_of_one_le₀ hW1).trans hsp
      have h0 : 0 ≤ 2 * CD * Cf ^ 2 / W := by positivity
      calc CD * (A * A) = 2 * CD * Cf ^ 2 / W * (W : ℝ)⁻¹ := by rw [hAA]; field_simp
        _ ≤ 2 * CD * Cf ^ 2 / W * Real.sqrt p := mul_le_mul_of_nonneg_left hWinv h0
        _ = 2 * CD * Cf ^ 2 * Real.sqrt p / W := by ring
    calc 2 * (Cf * Real.sqrt p / W) + CD * (A * A)
        ≤ 2 * (Cf * Real.sqrt p / W) + 2 * CD * Cf ^ 2 * Real.sqrt p / W := by gcongr
      _ = (2 * Cf + 2 * CD * Cf ^ 2) * Real.sqrt p / W := by ring

/-!
## 12. The path clause for both cores
-/

/-- **The matched-traces theorem, `path` clause, cores `r ∈ {1, 2}`**, from
`ConditionalBlockGUECount` and `GaussianLpGradient`. Law `pathLaw W r b`, deterministic
`E ∈ bulkInterval κ`, `2 ≤ p ≤ ε₀ W`, `W ≥ 1`: `‖max_i |W⁻¹ Tr(R_r)_{ii} - a|‖_p ≤ C √p / W`,
with `ε₀, C` depending only on `b, κ`. -/
theorem coreTraces_holds (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : Internal.Contracts.Inputs.GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∃ ε₀ C : ℝ, 0 < ε₀ ∧
      ∀ (W : ℕ), 0 < W → ∀ p : ℝ, 2 ≤ p → p ≤ ε₀ * W → ∀ r : ℕ, (r = 1 ∨ r = 2) →
        ∀ E ∈ bulkInterval κ,
          eLpNorm (fun ω => max ‖blockTrace (pathPortResolvent b E ω) 0 - matchedA E‖
              ‖blockTrace (pathPortResolvent b E ω) 1 - matchedA E‖)
            (ENNReal.ofReal p) (pathLaw W r b) ≤ ENNReal.ofReal (C * Real.sqrt p / W) := by
  intro b hb0 hb1 κ hκ
  obtain ⟨ε1, C1, hε1, h1⟩ := coreTraces_one hcount hgrad b hb0 hb1 κ hκ
  obtain ⟨ε2, C2, hε2, h2⟩ := coreTraces_two hcount hgrad b hb0 hb1 κ hκ
  refine ⟨min ε1 ε2, max C1 C2, lt_min hε1 hε2, ?_⟩
  intro W hW p hp2 hpε r hr E hE
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hmono : ∀ C : ℝ, C ≤ max C1 C2 →
      ENNReal.ofReal (C * Real.sqrt p / W) ≤ ENNReal.ofReal (max C1 C2 * Real.sqrt p / W) :=
    fun C hC => ENNReal.ofReal_le_ofReal (by gcongr)
  rcases hr with rfl | rfl
  · exact (h1 W hW p hp2 (hpε.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hW'.le)) E
      hE).trans (hmono C1 (le_max_left _ _))
  · exact (h2 W hW p hp2 (hpε.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hW'.le)) E
      hE).trans (hmono C2 (le_max_right _ _))

end BlockBand.Layers
