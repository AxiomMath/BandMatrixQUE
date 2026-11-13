module

public import BlockBand.Endpoints.Clock.CavityMeanMatrix
public import BlockBand.Layers.LayerMeanBounds
public import BlockBand.Layers.ScalarRecursion
public import BlockBand.Internal.Contracts.TransmissionStatements
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# The cavity-mean lemma: the fresh one-port layer and its Schur identity

The old Schur complement term is a deterministic Hermitian `X : Matrix (Fin W) (Fin W) ℂ`; the fresh
layer `ω = (A, B)` has law `layerLaw W b .oneBlockOnePort` (`A ~ GUE_W(c/W)`, `c = 1 - 2b`,
`B ~ Gin(b/W)`), and all expectations are over this law, i.e. conditional on `X`.
* `X₊ = B*(A - e - X)⁻¹B` is `TransmissionStatements.freshSchur e X ω`;
* `h₊(z') = W⁻¹ Tr (z' - X₊)⁻¹` is `cavityHplus e X z' ω` (`= normalizedResolventTrace X₊ z'`);
* the layer resolvent is `𝒢 = layerResolvent .oneBlockOnePort e z' (cavityLift X) ω`, where
  `cavityLift X` is the matrix `X` on the physical sites `Fin 1 × Fin W`.

Results (no contract is used in this file):
* `cavityHplus_eq_portBlockTrace`, `ae_cavityHplus_eq_portBlockTrace`: almost surely
  `h₊(z') = W⁻¹ Tr 𝒢_port` (the bottom block of `𝒢` is `(z' - X₊)⁻¹`; the top block `A - e - X`
  is a.s. invertible, `srec_ae_isUnit_top`);
* `ae_freshSchur_isHermitian`, `norm_cavityHplus_le`: a.s. `X₊` is Hermitian, hence
  `|h₊(z')| ≤ (Im z')⁻¹`;
* `cavityHplus_port_ward`: the Ward inequality `-Im h₊ ≥ Im z' |h₊|²` for one sample;
* `cavity_blockTrace_lift_inv`: `W⁻¹ Tr [(ζ - X)⁻¹ on the physical block] = f(ζ)`;
* measurability of `X₊` and joint measurability of `(ζ, ω) ↦ h₊(ζ)(ω)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements (freshSchur)
open scoped Matrix.Norms.L2Operator

/-- The old Schur term `X` placed on the physical sites `Fin 1 × Fin W` of the one-block layer
(the embedding used by the `freshSchur`).
-/
def cavityLift {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ :=
  Matrix.of fun u v => X u.2 v.2

/-- `h₊(z') = W⁻¹ Tr (z' - X₊)⁻¹`, `X₊ = B*(A - e - X)⁻¹B`. -/
def cavityHplus {W : ℕ} (e : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (z' : ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  normalizedResolventTrace (freshSchur e X ω) z'

/-- The one-block layer law is a probability measure. -/
instance cavityProb_isProbabilityMeasure_layerLaw (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (layerLaw W b .oneBlockOnePort) :=
  BlockBand.Layers.pg_isProbabilityMeasure_layerLaw W b _

namespace CavityMeanProb

/-- `Fin 1 × Fin W ≃ Fin W`. -/
abbrev liftEquiv (W : ℕ) : Fin 1 × Fin W ≃ Fin W := Equiv.uniqueProd (Fin W) (Fin 1)

theorem cavityLift_eq {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) :
    cavityLift X = X.submatrix (liftEquiv W) (liftEquiv W) := by
  ext u v; rfl

theorem cavityLift_isHermitian {W : ℕ} {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian) :
    (cavityLift X).IsHermitian := by
  rw [cavityLift_eq]; exact hX.submatrix _

theorem freshSchur_eq {W : ℕ} (e : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    freshSchur e X ω = (layerSchur .oneBlockOnePort e (cavityLift X) ω).submatrix
      (liftEquiv W).symm (liftEquiv W).symm := by
  ext x y; rfl

/-- `(ζ - Y∘e)⁻¹ = (ζ - Y)⁻¹ ∘ e` for an equivalence `e`. -/
theorem inv_shift_submatrix {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (Y : Matrix n n ℂ) (f : m ≃ n) (ζ : ℂ) :
    (ζ • (1 : Matrix m m ℂ) - Y.submatrix f f)⁻¹ = (ζ • (1 : Matrix n n ℂ) - Y)⁻¹.submatrix f f := by
  have h : ζ • (1 : Matrix m m ℂ) - Y.submatrix f f = (ζ • (1 : Matrix n n ℂ) - Y).submatrix f f := by
    ext i j
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, f.injective.eq_iff]
  rw [h, Matrix.inv_submatrix_equiv]

theorem trace_submatrix_equiv {m n : Type*} [Fintype m] [Fintype n] (N : Matrix n n ℂ) (f : m ≃ n) :
    (N.submatrix f f).trace = N.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp f (fun i => N i i)

theorem sum_fin_one_prod {W : ℕ} (g : Fin 1 × Fin W → ℂ) :
    ∑ p : Fin 1 × Fin W, g p = ∑ a : Fin W, g (0, a) := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]

/-- The trace of the top-left `(Fin 1 × Fin W)` block: `W⁻¹ Σ_a N_{(0,a)(0,a)} = W⁻¹ Tr N`. -/
theorem normalized_trace_eq_sum {W : ℕ} (N : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) :
    (W : ℂ)⁻¹ * N.trace = (W : ℂ)⁻¹ * ∑ a : Fin W, N (0, a) (0, a) := by
  rw [Matrix.trace, sum_fin_one_prod]; rfl

/-- `W⁻¹ Tr [(ζ - X)⁻¹]` on the physical block of the lifted matrix equals `f(ζ)`. -/
theorem cavity_blockTrace_lift_inv {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) (ζ : ℂ) :
    blockTrace (ζ • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) - cavityLift X)⁻¹ 0 =
      normalizedResolventTrace X ζ := by
  rw [cavityLift_eq, inv_shift_submatrix, normalizedResolventTrace, ← trace_submatrix_equiv _
    (liftEquiv W), normalized_trace_eq_sum]
  rfl

/-- **Schur identity**: if the top block `A - e - X` is invertible, the port
block of `𝒢` is `(z' - X₊)⁻¹`, so `W⁻¹ Tr 𝒢_port = h₊(z')`. -/
theorem cavityHplus_eq_portBlockTrace {W : ℕ} (e : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (z' : ℂ)
    (ω : LayerSample W .oneBlockOnePort)
    (hS : IsUnit (Internal.Contracts.Layers.blockDiag ω.1 - (e : ℂ) • 1 - cavityLift X).det) :
    cavityHplus e X z' ω =
      portBlockTrace (layerResolvent .oneBlockOnePort e z' (cavityLift X) ω) 0 := by
  have h22 : (layerResolvent .oneBlockOnePort e z' (cavityLift X) ω).toBlocks₂₂ =
      (z' • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) -
        layerSchur .oneBlockOnePort e (cavityLift X) ω)⁻¹ := by
    rw [layerResolvent, layerMatrix, BlockBand.Layers.pg_toBlocks22_inv _ _ _ _ hS]
    rfl
  rw [cavityHplus, freshSchur_eq, normalizedResolventTrace, inv_shift_submatrix,
    trace_submatrix_equiv, normalized_trace_eq_sum, ← h22]
  rfl

/-- Almost surely (`b < 1/2`) `h₊(z') = W⁻¹ Tr 𝒢_port`. -/
theorem ae_cavityHplus_eq_portBlockTrace {W : ℕ} {b : ℝ} (hb : b < 1 / 2) (e : ℝ)
    (X : Matrix (Fin W) (Fin W) ℂ) (z' : ℂ) :
    ∀ᵐ ω ∂layerLaw W b .oneBlockOnePort, cavityHplus e X z' ω =
      portBlockTrace (layerResolvent .oneBlockOnePort e z' (cavityLift X) ω) 0 := by
  filter_upwards [BlockBand.Layers.srec_ae_isUnit_top hb .oneBlockOnePort e (cavityLift X)]
    with ω hω
  exact cavityHplus_eq_portBlockTrace e X z' ω hω

/-- `X₊` is Hermitian for Hermitian `X` and a Hermitian fresh block `A`. -/
theorem freshSchur_isHermitian {W : ℕ} (e : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) (ω : LayerSample W .oneBlockOnePort) (hA : ∀ j, (ω.1 j).IsHermitian) :
    (freshSchur e X ω).IsHermitian := by
  rw [freshSchur_eq]
  refine Matrix.IsHermitian.submatrix ?_ _
  exact Matrix.isHermitian_conjTranspose_mul_mul _
    (BlockBand.Layers.lct_top_isHermitian e (cavityLift_isHermitian hX) hA).inv

/-- Almost surely `X₊` is Hermitian. -/
theorem ae_freshSchur_isHermitian (W : ℕ) (b e : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) :
    ∀ᵐ ω ∂layerLaw W b .oneBlockOnePort, (freshSchur e X ω).IsHermitian := by
  filter_upwards [BlockBand.Layers.lct_ae_blocks_isHermitian W b .oneBlockOnePort] with ω hω
  exact freshSchur_isHermitian e hX ω hω

/-- `|W⁻¹ Tr (z - Y)⁻¹| ≤ (Im z)⁻¹` for Hermitian `Y`, `Im z > 0`. -/
theorem norm_normalizedResolventTrace_le {W : ℕ} (hW : 0 < W) {Y : Matrix (Fin W) (Fin W) ℂ}
    (hY : Y.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    ‖normalizedResolventTrace Y z‖ ≤ 1 / z.im := by
  rw [normalizedResolventTrace_eq hY hz.ne']
  exact CavityMean.norm_cavityStieltjes_le hY.eigenvalues (isCavityWeights_uniform hW) hz

/-- **Ward inequality** for one Hermitian sample: `Im z |f(z)|² ≤ -Im f(z)`,
`f(z) = W⁻¹ Tr (z - Y)⁻¹`. -/
theorem normalizedResolventTrace_ward {W : ℕ} (hW : 0 < W) {Y : Matrix (Fin W) (Fin W) ℂ}
    (hY : Y.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    z.im * ‖normalizedResolventTrace Y z‖ ^ 2 ≤ -(normalizedResolventTrace Y z).im := by
  rw [normalizedResolventTrace_eq hY hz.ne', CavityMean.im_cavityStieltjes]
  have := CavityMean.norm_sq_cavityStieltjes_le hY.eigenvalues (isCavityWeights_uniform hW) z
  nlinarith

/-- `|h₊(z')| ≤ (Im z')⁻¹` whenever `X₊` is Hermitian. -/
theorem norm_cavityHplus_le {W : ℕ} (hW : 0 < W) (e : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    {ω : LayerSample W .oneBlockOnePort} (hH : (freshSchur e X ω).IsHermitian) {z' : ℂ}
    (hz : 0 < z'.im) : ‖cavityHplus e X z' ω‖ ≤ 1 / z'.im :=
  norm_normalizedResolventTrace_le hW hH hz

/-- The port Ward inequality `Im z' |h₊|² ≤ -Im h₊` whenever `X₊` is Hermitian. -/
theorem cavityHplus_port_ward {W : ℕ} (hW : 0 < W) (e : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    {ω : LayerSample W .oneBlockOnePort} (hH : (freshSchur e X ω).IsHermitian) {z' : ℂ}
    (hz : 0 < z'.im) : z'.im * ‖cavityHplus e X z' ω‖ ^ 2 ≤ -(cavityHplus e X z' ω).im :=
  normalizedResolventTrace_ward hW hH hz

/-!
## Measurability
-/

theorem measurable_entry {Ω m n : Type*} [MeasurableSpace Ω] {f : Ω → Matrix m n ℂ}
    (hf : Measurable f) (a : m) (c : n) : Measurable (fun ω => f ω a c) :=
  (measurable_pi_apply c).comp ((measurable_pi_apply a).comp hf)

theorem measurable_of_entries {Ω m n : Type*} [MeasurableSpace Ω] {f : Ω → Matrix m n ℂ}
    (hf : ∀ a c, Measurable (fun ω => f ω a c)) : Measurable f :=
  measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun c => hf a c

/-- `ω ↦ X₊(ω)` is measurable. -/
theorem measurable_freshSchur {W : ℕ} (e : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (fun ω : LayerSample W .oneBlockOnePort => freshSchur e X ω) := by
  have hL := BlockBand.Layers.measurable_layerMatrix .oneBlockOnePort e 0 (cavityLift X)
  have hB : Measurable (fun ω : LayerSample W .oneBlockOnePort =>
      (layerMatrix .oneBlockOnePort e 0 (cavityLift X) ω).toBlocks₁₂) :=
    measurable_of_entries fun a c => measurable_entry hL (Sum.inl a) (Sum.inr c)
  have hD : Measurable (fun ω : LayerSample W .oneBlockOnePort =>
      (layerMatrix .oneBlockOnePort e 0 (cavityLift X) ω).toBlocks₁₁) :=
    measurable_of_entries fun a c => measurable_entry hL (Sum.inl a) (Sum.inl c)
  have hS : Measurable (fun ω : LayerSample W .oneBlockOnePort =>
      layerSchur .oneBlockOnePort e (cavityLift X) ω) := by
    have h := BlockBand.Layers.srec_measurable_mul (BlockBand.Layers.srec_measurable_mul
      (BlockBand.Layers.srec_measurable_conjTranspose hB)
      (BlockBand.Layers.measurable_matrix_inv.comp hD)) hB
    convert h using 1
    funext ω
    simp [layerSchur, layerMatrix, Function.comp]
  simp only [freshSchur_eq]
  exact measurable_of_entries fun a c => measurable_entry hS _ _

/-- `(ζ, ω) ↦ h₊(ζ)(ω)` is jointly measurable. -/
theorem measurable_cavityHplus_uncurry {W : ℕ} (e : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (fun q : ℂ × LayerSample W .oneBlockOnePort => cavityHplus e X q.1 q.2) := by
  have hY : Measurable (fun q : ℂ × LayerSample W .oneBlockOnePort => freshSchur e X q.2) :=
    (measurable_freshSchur e X).comp measurable_snd
  have hM : Measurable (fun q : ℂ × LayerSample W .oneBlockOnePort =>
      q.1 • (1 : Matrix (Fin W) (Fin W) ℂ) - freshSchur e X q.2) := by
    refine measurable_of_entries fun a c => ?_
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact (measurable_fst.mul measurable_const).sub (measurable_entry hY a c)
  have hI := BlockBand.Layers.measurable_matrix_inv.comp hM
  unfold cavityHplus normalizedResolventTrace Matrix.trace
  simp only [Matrix.diag_apply]
  exact measurable_const.mul (Finset.measurable_sum _ fun a _ => measurable_entry hI a a)

/-- For each `ζ`, `ω ↦ h₊(ζ)(ω)` is measurable. -/
theorem measurable_cavityHplus {W : ℕ} (e : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (z' : ℂ) :
    Measurable (fun ω : LayerSample W .oneBlockOnePort => cavityHplus e X z' ω) :=
  (measurable_cavityHplus_uncurry e X).comp (f := fun ω => (z', ω))
    (measurable_const.prodMk measurable_id)

end CavityMeanProb

end BlockBand.Endpoints.Clock
