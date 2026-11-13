module

public import BlockBand.Layers.AbsorberCount
public import BlockBand.Layers.GinibreTails

/-!
# Real Gaussian coordinates of one layer

Support for the gradient step of the trace–matrix lemma: `d𝒢 = -𝒢(d𝓗)𝒢` gives a
Hilbert–Schmidt gradient bounded by `CW^{-1/2}‖𝒢‖²`, to which the Gaussian `L^p` gradient
inequality applies, with covariance `O(W^{-1})`.

* `tfl_layerLaw_eq_map`: `layerLaw W b σ` (`A_a ~ GUE_W(c/W)`, `c = 1-2b`, bonds `Gin(b/W)`, all
  independent) is the image of the white-noise product `Inputs.gaussianProduct (tflVar W b σ)`
  on the finite coordinate set
  `TflCoord W σ = (blocks × ((W×W) × 2)) ⊕ (blocks × ports × (W×W×2))` under the explicit
  map `tflEmbed` (`gueOfCoords` on block coordinates of variance `1`, `bondAssemble` on bond
  coordinates of variance `b/(2W)`). Proof: `gueMeasure_eq_map`, `pi_map_whiteNoise`,
  `bondLaw_eq_map`, `measurePreserving_sumPiEquivProdPi`.
* `tfl_layerMatrix_embed`, `tflLinMap`: the layer matrix is `tflConst + tflLin x` with
  `tflLin` real-linear in the coordinates.
* `tfl_weighted_trace_le`: for every matrix `K` on the layer sites,
  `Σᵢ vᵢ |Tr(K ∂ᵢ𝒢⁻¹)|² ≤ (2t_A + 2t_B) ‖K‖²_HS`, `t_A = c/W`, `t_B = b/W` (explicit trace
  against each coordinate matrix: `tfl_trace_inl_le`, `tfl_trace_inr_le`).

Deterministic and dimension-free; no hypothesis beyond the definitions.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct)
open BlockBand.Internal.Contracts.CoareaPalm (gueMeasure gueSample)
open BlockBand.SourceProcess (circularBrownianCoordinates)
open scoped ENNReal NNReal ComplexConjugate

/-- Real coordinates of the diagonal blocks: block `a`, then `((α, β), s)`. -/
abbrev TflCoordA (k W : ℕ) := Fin k × GaussCoord W

/-- Real coordinates of the bonds: block `a`, port `j`, then `(α, β, s)`. -/
abbrev TflCoordB (k p W : ℕ) := Fin k × (Fin p × (Fin W × Fin W × Fin 2))

/-- All real Gaussian coordinates of a layer. -/
abbrev TflCoord (W : ℕ) (σ : LayerShape) := TflCoordA σ.blocks W ⊕ TflCoordB σ.blocks σ.ports W

/-- Entry variance of the diagonal blocks, `c/W` with `c = 1 - 2b`. -/
def tflTA (W : ℕ) (b : ℝ) : ℝ≥0 := Real.toNNReal ((1 - 2 * b) / W)

/-- Entry variance of the bonds, `b/W`. -/
def tflTB (W : ℕ) (b : ℝ) : ℝ≥0 := Real.toNNReal (b / W)

/-- Variances of the real coordinates: `1` on the block coordinates (the scale sits in
`gueOfCoords`), `b/(2W)` on the bond coordinates. -/
def tflVar (W : ℕ) (b : ℝ) (σ : LayerShape) : TflCoord W σ → ℝ≥0 :=
  Sum.elim (fun _ => 1) (fun _ => tflTB W b / 2)

/-- The layer sample assembled from real coordinates. -/
def tflEmbed (W : ℕ) (b : ℝ) (σ : LayerShape) (x : TflCoord W σ → ℝ) : LayerSample W σ :=
  (fun a => gueOfCoords W (tflTA W b) (fun c => x (Sum.inl (a, c))),
    bondAssemble (fun r => x (Sum.inr r)))

theorem tfl_measurable_embed (W : ℕ) (b : ℝ) (σ : LayerShape) :
    Measurable (tflEmbed W b σ) := by
  unfold tflEmbed
  refine Measurable.prodMk ?_ ?_
  · refine measurable_pi_iff.mpr fun a => ?_
    exact (measurable_gueOfCoords W _).comp (by fun_prop)
  · exact measurable_bondAssemble.comp (by fun_prop)

/-- **The layer law in real Gaussian coordinates**: `layerLaw W b σ` is the image of
`gaussianProduct (tflVar W b σ)` under `tflEmbed`. -/
theorem tfl_layerLaw_eq_map (W : ℕ) (b : ℝ) (σ : LayerShape) :
    layerLaw W b σ = (gaussianProduct (tflVar W b σ)).map (tflEmbed W b σ) := by
  have h1 : (Measure.pi fun _ : Fin σ.blocks => gueMeasure (Fin W) (tflTA W b)) =
      (whiteNoise (TflCoordA σ.blocks W) 1).map
        (fun r a => gueOfCoords W (tflTA W b) (fun c => r (a, c))) := by
    simp only [gueMeasure_eq_map]
    exact pi_map_whiteNoise 1 _ (measurable_gueOfCoords W _)
  have h2 := bondLaw_eq_map σ.blocks σ.ports W (tflTB W b)
  have h3 : (whiteNoise (TflCoordA σ.blocks W) 1).prod
      (whiteNoise (TflCoordB σ.blocks σ.ports W) (tflTB W b / 2)) =
      (gaussianProduct (tflVar W b σ)).map
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : TflCoord W σ => ℝ)) :=
    ((measurePreserving_sumPiEquivProdPi
      (fun i : TflCoord W σ => gaussianReal 0 (tflVar W b σ i))).map_eq).symm
  have hg : Measurable (fun (r : TflCoordA σ.blocks W → ℝ) (a : Fin σ.blocks) =>
      gueOfCoords W (tflTA W b) (fun c => r (a, c))) :=
    measurable_pi_iff.mpr fun a => (measurable_gueOfCoords W _).comp (by fun_prop)
  change (Measure.pi fun _ : Fin σ.blocks => gueMeasure (Fin W) (tflTA W b)).prod
    (bondLaw σ.blocks σ.ports W (tflTB W b)) = _
  rw [h1, h2, Measure.map_prod_map _ _ hg measurable_bondAssemble, h3,
    Measure.map_map (hg.prodMap measurable_bondAssemble) (MeasurableEquiv.measurable _)]
  rfl

/-!
## The layer matrix is affine in the coordinates
-/

/-- The coordinate-linear part of the layer matrix: `[[diag A, B], [Bᴴ, 0]]`. -/
def tflLin (W : ℕ) (b : ℝ) (σ : LayerShape) (x : TflCoord W σ → ℝ) :
    Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  fromBlocks (Internal.Contracts.Layers.blockDiag (tflEmbed W b σ x).1)
    (bondMatrix σ (tflEmbed W b σ x).2)
    (bondMatrix σ (tflEmbed W b σ x).2)ᴴ 0

/-- The constant part of the layer matrix: `[[-E - X, 0], [0, z]]`. -/
def tflConst {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) : Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  fromBlocks (-((E : ℂ) • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)) - X) 0 0 (z • 1)

theorem tfl_layerMatrix_embed (W : ℕ) (b : ℝ) (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (x : TflCoord W σ → ℝ) :
    layerMatrix σ E z X (tflEmbed W b σ x) = tflConst σ E z X + tflLin W b σ x := by
  rw [layerMatrix, tflConst, tflLin, fromBlocks_add]
  congr 1 <;> abel

theorem tflLin_add (W : ℕ) (b : ℝ) (σ : LayerShape) (x y : TflCoord W σ → ℝ) :
    tflLin W b σ (x + y) = tflLin W b σ x + tflLin W b σ y := by
  ext i j
  rcases i with ⟨a, α⟩ | ⟨a, α⟩ <;> rcases j with ⟨c, β⟩ | ⟨c, β⟩ <;>
    simp [tflLin, tflEmbed, Internal.Contracts.Layers.blockDiag, bondMatrix, gueOfCoords,
      gueSample, circularBrownianCoordinates, bondAssemble, ginibreAssemble, map_add, map_mul,
      Complex.conj_ofReal, Complex.conj_I] <;>
    (try split_ifs) <;>
    (try simp only [map_add, map_mul, map_zero, Complex.conj_ofReal, Complex.conj_I]) <;>
    ring

theorem tflLin_smul (W : ℕ) (b : ℝ) (σ : LayerShape) (r : ℝ) (x : TflCoord W σ → ℝ) :
    tflLin W b σ (r • x) = r • tflLin W b σ x := by
  ext i j
  rcases i with ⟨a, α⟩ | ⟨a, α⟩ <;> rcases j with ⟨c, β⟩ | ⟨c, β⟩ <;>
    simp [tflLin, tflEmbed, Internal.Contracts.Layers.blockDiag, bondMatrix, gueOfCoords,
      gueSample, circularBrownianCoordinates, bondAssemble, ginibreAssemble, map_add, map_mul,
      Complex.conj_ofReal, Complex.conj_I] <;>
    (try split_ifs) <;>
    (try simp only [map_add, map_mul, map_zero, Complex.conj_ofReal, Complex.conj_I]) <;>
    ring

/-- The coordinate-linear part as an `ℝ`-linear map. -/
def tflLinMap (W : ℕ) (b : ℝ) (σ : LayerShape) :
    (TflCoord W σ → ℝ) →ₗ[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ where
  toFun := tflLin W b σ
  map_add' := tflLin_add W b σ
  map_smul' := tflLin_smul W b σ

/-!
## Traces against the coordinate matrices
-/

/-- `‖u c + w d‖² ≤ 2q(‖u‖² + ‖w‖²)` when `‖c‖², ‖d‖² ≤ q`. -/
theorem tfl_norm_sq_add_le (u w c d : ℂ) (q : ℝ) (hc : ‖c‖ ^ 2 ≤ q) (hd : ‖d‖ ^ 2 ≤ q) :
    ‖u * c + w * d‖ ^ 2 ≤ 2 * q * (‖u‖ ^ 2 + ‖w‖ ^ 2) := by
  have h1 : ‖u * c + w * d‖ ≤ ‖u‖ * ‖c‖ + ‖w‖ * ‖d‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
  have h0 : 0 ≤ ‖u * c + w * d‖ := norm_nonneg _
  have hu := norm_nonneg u
  have hw := norm_nonneg w
  have hc0 := norm_nonneg c
  have hd0 := norm_nonneg d
  have h2 : ‖u * c + w * d‖ ^ 2 ≤ (‖u‖ * ‖c‖ + ‖w‖ * ‖d‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : (‖u‖ * ‖c‖ + ‖w‖ * ‖d‖) ^ 2 ≤ 2 * (‖u‖ ^ 2 * ‖c‖ ^ 2) + 2 * (‖w‖ ^ 2 * ‖d‖ ^ 2) := by
    nlinarith [sq_nonneg (‖u‖ * ‖c‖ - ‖w‖ * ‖d‖)]
  have h4 : ‖u‖ ^ 2 * ‖c‖ ^ 2 ≤ ‖u‖ ^ 2 * q := mul_le_mul_of_nonneg_left hc (by positivity)
  have h5 : ‖w‖ ^ 2 * ‖d‖ ^ 2 ≤ ‖w‖ ^ 2 * q := mul_le_mul_of_nonneg_left hd (by positivity)
  nlinarith

/-- Pushing the incidence test inside other tests (a `simp` normal form). -/
theorem tfl_ite_incident_swap {σ : LayerShape} (i : Fin σ.blocks) (j : Fin σ.ports) (c : Prop)
    [Decidable c] (f : ℂ) : (if σ.incident i j = true then (if c then f else 0) else 0) =
      if c then (if σ.incident i j = true then f else 0) else 0 := by
  split_ifs <;> rfl

/-- Trace against a block coordinate matrix: for the coordinate `((α, β), s)` of block `a`,
`|Tr(K ∂𝒢⁻¹)|² ≤ (t/2)(|K_{aβ,aα}|² + |K_{aα,aβ}|²)`, `t = c/W`. -/
theorem tfl_trace_inl_le (W : ℕ) (b : ℝ) (σ : LayerShape)
    (K : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (a : Fin σ.blocks) (α β : Fin W)
    (s : Fin 2) :
    ‖(K * tflLin W b σ (Pi.single (Sum.inl (a, ((α, β), s))) 1)).trace‖ ^ 2 ≤
      2 * ((tflTA W b : ℝ) / 4) *
        (‖K (Sum.inl (a, β)) (Sum.inl (a, α))‖ ^ 2 +
          ‖K (Sum.inl (a, α)) (Sum.inl (a, β))‖ ^ 2) := by
  have ht := (tflTA W b).2
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hst : Real.sqrt (tflTA W b : ℝ) ^ 2 = tflTA W b := Real.sq_sqrt ht
  have hs2p : 0 < Real.sqrt 2 := by positivity
  fin_cases s <;>
  simp only [Fin.zero_eta, Fin.mk_one] <;>
  simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, tflLin,
      tflEmbed, Internal.Contracts.Layers.blockDiag, bondMatrix, gueOfCoords, gueSample,
      circularBrownianCoordinates, bondAssemble, ginibreAssemble, Pi.single_apply, ite_and,
      mul_add, Finset.sum_add_distrib, apply_ite (fun r : ℝ => (r : ℂ)), mul_ite, ite_mul,
      Finset.sum_ite_eq', Finset.sum_ite_irrel, apply_ite (starRingEnd ℂ), ite_div] <;>
  refine le_trans (tfl_norm_sq_add_le _ _ _ _ ((tflTA W b : ℝ) / 4) ?_ ?_) (le_of_eq (by ring)) <;>
  simp [Complex.norm_real, mul_pow, div_pow, inv_pow, hs2, hst, abs_of_pos hs2p] <;>
  linarith

/-- Trace against a bond coordinate matrix: for the coordinate `(α, β, s)` of the bond
`(a, j)`, `|Tr(K ∂𝒢⁻¹)|² ≤ 2(|K_{jβ,aα}|² + |K_{aα,jβ}|²)`. -/
theorem tfl_trace_inr_le (W : ℕ) (b : ℝ) (σ : LayerShape)
    (K : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (a : Fin σ.blocks) (j : Fin σ.ports)
    (α β : Fin W) (s : Fin 2) :
    ‖(K * tflLin W b σ (Pi.single (Sum.inr (a, j, α, β, s)) 1)).trace‖ ^ 2 ≤
      2 * 1 * (‖K (Sum.inr (j, β)) (Sum.inl (a, α))‖ ^ 2 +
        ‖K (Sum.inl (a, α)) (Sum.inr (j, β))‖ ^ 2) := by
  have hR : 0 ≤ 2 * 1 * (‖K (Sum.inr (j, β)) (Sum.inl (a, α))‖ ^ 2 +
      ‖K (Sum.inl (a, α)) (Sum.inr (j, β))‖ ^ 2) := by positivity
  fin_cases s <;>
  simp only [Fin.zero_eta, Fin.mk_one] <;>
  simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_sum_type,
      Fintype.sum_prod_type, tflLin, tflEmbed, Internal.Contracts.Layers.blockDiag, bondMatrix,
      gueOfCoords, gueSample, circularBrownianCoordinates, bondAssemble, ginibreAssemble,
      Pi.single_apply, ite_and, Finset.sum_add_distrib, apply_ite (fun r : ℝ => (r : ℂ)),
      mul_ite, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_irrel,
      apply_ite (starRingEnd ℂ), tfl_ite_incident_swap] <;>
  split_ifs <;>
  first
  | (simpa using hR)
  | (simpa using tfl_norm_sq_add_le (K (Sum.inr (j, β)) (Sum.inl (a, α)))
      (K (Sum.inl (a, α)) (Sum.inr (j, β))) 1 1 1 (by simp) (by simp))
  | (simpa using tfl_norm_sq_add_le (K (Sum.inr (j, β)) (Sum.inl (a, α)))
      (K (Sum.inl (a, α)) (Sum.inr (j, β))) Complex.I (-Complex.I) 1 (by simp) (by simp))

/-- Diagonal physical blocks are part of the physical-physical Hilbert–Schmidt mass. -/
theorem tfl_diag_blocks_le {k W : ℕ} (g : Fin k × Fin W → Fin k × Fin W → ℝ)
    (hg : ∀ x y, 0 ≤ g x y) :
    ∑ a : Fin k, ∑ α : Fin W, ∑ β : Fin W, g (a, α) (a, β) ≤ ∑ x, ∑ y, g x y := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun α _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.single_le_sum (f := fun a' => ∑ β : Fin W, g (a, α) (a', β))
    (fun a' _ => Finset.sum_nonneg fun β _ => hg _ _) (Finset.mem_univ a)

/-- **Weighted coordinate traces** (gradient form of `d𝒢 = -𝒢 (d𝓗) 𝒢`). For every matrix
`K` on the layer sites, with the coordinate variances `tflVar`,
`Σᵢ vᵢ |Tr(K ∂ᵢ𝒢⁻¹)|² ≤ (2t_A + 2t_B) ‖K‖²_HS`, `t_A = c/W`, `t_B = b/W`. -/
theorem tfl_weighted_trace_le (W : ℕ) (b : ℝ) (σ : LayerShape)
    (K : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    ∑ i, (tflVar W b σ i : ℝ) * ‖(K * tflLin W b σ (Pi.single i 1)).trace‖ ^ 2 ≤
      (2 * (tflTA W b : ℝ) + 2 * (tflTB W b : ℝ)) * ∑ x, ∑ y, ‖K x y‖ ^ 2 := by
  set tA : ℝ := ((tflTA W b : ℝ≥0) : ℝ) with htA
  set tB : ℝ := ((tflTB W b : ℝ≥0) : ℝ) with htB
  have htA0 : 0 ≤ tA := (tflTA W b).2
  have htB0 : 0 ≤ tB := (tflTB W b).2
  -- the four Hilbert–Schmidt blocks
  set Hll := ∑ x : PhysSite W σ, ∑ y : PhysSite W σ, ‖K (Sum.inl x) (Sum.inl y)‖ ^ 2 with hHll
  set Hlr := ∑ x : PhysSite W σ, ∑ y : PortSite W σ, ‖K (Sum.inl x) (Sum.inr y)‖ ^ 2 with hHlr
  set Hrl := ∑ y : PortSite W σ, ∑ x : PhysSite W σ, ‖K (Sum.inr y) (Sum.inl x)‖ ^ 2 with hHrl
  set Hrr := ∑ y : PortSite W σ, ∑ y' : PortSite W σ, ‖K (Sum.inr y) (Sum.inr y')‖ ^ 2 with hHrr
  have hHS : ∑ x, ∑ y, ‖K x y‖ ^ 2 = Hll + Hlr + (Hrl + Hrr) := by
    rw [Fintype.sum_sum_type]
    simp only [Fintype.sum_sum_type, Finset.sum_add_distrib]
    rfl
  have hll0 : 0 ≤ Hll := by positivity
  have hlr0 : 0 ≤ Hlr := by positivity
  have hrl0 : 0 ≤ Hrl := by positivity
  have hrr0 : 0 ≤ Hrr := by positivity
  -- block coordinates
  have hA : ∑ i : TflCoordA σ.blocks W, (tflVar W b σ (Sum.inl i) : ℝ) *
      ‖(K * tflLin W b σ (Pi.single (Sum.inl i) 1)).trace‖ ^ 2 ≤ 2 * tA * Hll := by
    have h1 : ∀ i : TflCoordA σ.blocks W, (tflVar W b σ (Sum.inl i) : ℝ) *
        ‖(K * tflLin W b σ (Pi.single (Sum.inl i) 1)).trace‖ ^ 2 ≤
        2 * (tA / 4) * (‖K (Sum.inl (i.1, i.2.1.2)) (Sum.inl (i.1, i.2.1.1))‖ ^ 2 +
          ‖K (Sum.inl (i.1, i.2.1.1)) (Sum.inl (i.1, i.2.1.2))‖ ^ 2) := by
      rintro ⟨a, ⟨⟨α, β⟩, s⟩⟩
      simp only [tflVar, Sum.elim_inl, NNReal.coe_one, one_mul]
      exact tfl_trace_inl_le W b σ K a α β s
    set S := ∑ a : Fin σ.blocks, ∑ α : Fin W, ∑ β : Fin W,
      ‖K (Sum.inl (a, α)) (Sum.inl (a, β))‖ ^ 2 with hS
    have hS' : ∑ a : Fin σ.blocks, ∑ α : Fin W, ∑ β : Fin W,
        ‖K (Sum.inl (a, β)) (Sum.inl (a, α))‖ ^ 2 = S := by
      rw [hS]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    have hSle : S ≤ Hll := tfl_diag_blocks_le (fun x y => ‖K (Sum.inl x) (Sum.inl y)‖ ^ 2)
      (fun _ _ => by positivity)
    refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    rw [hS']
    nlinarith
  -- bond coordinates
  have hB : ∑ i : TflCoordB σ.blocks σ.ports W, (tflVar W b σ (Sum.inr i) : ℝ) *
      ‖(K * tflLin W b σ (Pi.single (Sum.inr i) 1)).trace‖ ^ 2 ≤ 2 * tB * (Hrl + Hlr) := by
    have h1 : ∀ i : TflCoordB σ.blocks σ.ports W, (tflVar W b σ (Sum.inr i) : ℝ) *
        ‖(K * tflLin W b σ (Pi.single (Sum.inr i) 1)).trace‖ ^ 2 ≤
        tB / 2 * (2 * 1 * (‖K (Sum.inr (i.2.1, i.2.2.2.1)) (Sum.inl (i.1, i.2.2.1))‖ ^ 2 +
          ‖K (Sum.inl (i.1, i.2.2.1)) (Sum.inr (i.2.1, i.2.2.2.1))‖ ^ 2)) := by
      rintro ⟨a, j, α, β, s⟩
      simp only [tflVar, Sum.elim_inr, NNReal.coe_div, NNReal.coe_ofNat]
      exact mul_le_mul_of_nonneg_left (tfl_trace_inr_le W b σ K a j α β s) (by positivity)
    refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
    have e1 : ∑ a : Fin σ.blocks, ∑ j : Fin σ.ports, ∑ α : Fin W, ∑ β : Fin W,
        ‖K (Sum.inr (j, β)) (Sum.inl (a, α))‖ ^ 2 = Hrl := by
      rw [hHrl]
      simp only [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      calc _ = ∑ a : Fin σ.blocks, ∑ β : Fin W, ∑ α : Fin W,
            ‖K (Sum.inr (j, β)) (Sum.inl (a, α))‖ ^ 2 :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    have e2 : ∑ a : Fin σ.blocks, ∑ j : Fin σ.ports, ∑ α : Fin W, ∑ β : Fin W,
        ‖K (Sum.inl (a, α)) (Sum.inr (j, β))‖ ^ 2 = Hlr := by
      rw [hHlr]
      simp only [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    rw [e1, e2]
    nlinarith
  rw [Fintype.sum_sum_type, hHS]
  nlinarith

end BlockBand.Layers
