module

public import BlockBand.Critical.Collar.Density.RegularWindow

/-!
# `W`-uniform second moment of the fresh row and the uniform regular phase bound

*Law.* `collarLaw W b`, `W ≥ 1`, `0 < b < 1/2`.

* `lintegral_norm_sq_collarRowVec_le`: `E‖(w - A)q, -B*q‖² ≤ (2|w|² + 2(1-2b) + b)‖q‖²`.
* `im_dotProduct_inv_sub_I_le`: `Im⟨y,(H - i)⁻¹y⟩ ≤ ‖y‖²` (Hermitian `H`).
* `lintegral_collarRow_le_of_regular'`: the regular phase bound `lintegral_collarRow_le_of_regular`
  with a `W`-uniform tail `ε(1+δ⁻²)π⁻¹(2|w|² + 2(1-2b) + b)‖q‖²` (needed at fixed height `ε = ν`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw
open BlockBand.Foundations.Spectral BlockBand.Critical.WeightedDensity
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

variable {W : ℕ}

theorem blockDiag_mulVec_apply (A : Fin 2 → Matrix (Fin W) (Fin W) ℂ) (q : Fin 2 × Fin W → ℂ)
    (k : Fin 2) (a : Fin W) :
    (BlockBand.Internal.Contracts.Layers.blockDiag A *ᵥ q) (k, a) = (A k *ᵥ fun c => q (k, c)) a := by
  simp only [mulVec, dotProduct, BlockBand.Internal.Contracts.Layers.blockDiag,
    Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_eq_single k]
  · simp
  · intro k' _ hk; simp [Ne.symm hk]
  · simp

theorem sum_norm_sq_blockDiag_mulVec (A : Fin 2 → Matrix (Fin W) (Fin W) ℂ)
    (q : Fin 2 × Fin W → ℂ) :
    ∑ x, ‖(BlockBand.Internal.Contracts.Layers.blockDiag A *ᵥ q) x‖ ^ 2 =
      ∑ k : Fin 2, ∑ a, ‖(A k *ᵥ fun c => q (k, c)) a‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp_rw [blockDiag_mulVec_apply]

theorem lintegral_norm_sq_block_le (b : ℝ) (k : Fin 2) (q : Fin 2 × Fin W → ℂ) :
    ∫⁻ ω, ENNReal.ofReal (∑ a, ‖(ω.1.1 k *ᵥ fun c => q (k, c)) a‖ ^ 2) ∂collarLaw W b ≤
      ENNReal.ofReal (W * Real.toNNReal ((1 - 2 * b) / W) * ∑ c, ‖q (k, c)‖ ^ 2) := by
  have hm : Measurable fun ω : CollarSample W =>
      ENNReal.ofReal (∑ a, ‖(ω.1.1 k *ᵥ fun c => q (k, c)) a‖ ^ 2) := by
    have hc : Continuous fun M : Matrix (Fin W) (Fin W) ℂ =>
        ENNReal.ofReal (∑ a, ‖(M *ᵥ fun c => q (k, c)) a‖ ^ 2) :=
      ENNReal.continuous_ofReal.comp (continuous_finsetSum _ fun a _ =>
        (((continuous_apply a).comp (continuous_id.matrix_mulVec continuous_const)).norm).pow 2)
    exact hc.measurable.comp ((measurable_pi_apply k).comp (measurable_fst.comp measurable_fst))
  refine collar_lintegral_le_of_A b k hm fun ω _ _ => ?_
  simp only [setA_apply]
  rw [lintegral_norm_sq_mulVec_gue]

theorem lintegral_norm_sq_bond_collar (b : ℝ) (q : Fin 2 × Fin W → ℂ) :
    ∫⁻ ω, ENNReal.ofReal (∑ p, ‖((bondMatrix .common ω.1.2)ᴴ *ᵥ q) p‖ ^ 2) ∂collarLaw W b =
      ENNReal.ofReal (W * Real.toNNReal (b / W) * ∑ x, ‖q x‖ ^ 2) := by
  set t := Real.toNNReal ((1 - 2 * b) / W)
  have hmB : Measurable fun L : LayerSample W .common =>
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
  have hl : collarLaw W b = (layerLaw W b .common).prod (gueMeasure (PortSite W .common) t) := rfl
  have hl2 : layerLaw W b .common = (Measure.pi fun _ : Fin 2 =>
      gueMeasure (Fin W) t).prod (BlockBand.Layers.bondLaw 2 1 W (Real.toNNReal (b / W))) := rfl
  have : IsProbabilityMeasure (BlockBand.Layers.bondLaw 2 1 W (Real.toNNReal (b / W))) := by
    unfold BlockBand.Layers.bondLaw; infer_instance
  rw [hl, lintegral_prod (fun z : LayerSample W .common × Matrix (PortSite W .common)
      (PortSite W .common) ℂ => ENNReal.ofReal (∑ p, ‖((bondMatrix .common z.1.2)ᴴ *ᵥ q) p‖ ^ 2))
      (hmB.comp measurable_fst).aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [hl2, lintegral_prod (fun L : (Fin 2 → Matrix (Fin W) (Fin W) ℂ) ×
      (Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ) =>
        ENNReal.ofReal (∑ p, ‖((bondMatrix .common L.2)ᴴ *ᵥ q) p‖ ^ 2)) hmB.aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [lintegral_norm_sq_bond_mulVec]

/-- **`W`-uniform second moment of the fresh row.** -/
theorem lintegral_norm_sq_collarRowVec_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 0 < W)
    (w : ℂ) (q : Fin 2 × Fin W → ℂ) :
    ∫⁻ ω, ENNReal.ofReal (∑ x, ‖collarRowVec w q ω x‖ ^ 2) ∂collarLaw W b ≤
      ENNReal.ofReal ((2 * ‖w‖ ^ 2 + 2 * (1 - 2 * b) + b) * ∑ x, ‖q x‖ ^ 2) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  set Sq := ∑ x, ‖q x‖ ^ 2
  have hSq : 0 ≤ Sq := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set Sk : Fin 2 → ℝ := fun k => ∑ c, ‖q (k, c)‖ ^ 2
  have hSk : Sk 0 + Sk 1 = Sq := by
    simp only [Sk, Sq, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hSk0 : ∀ k, 0 ≤ Sk k := fun k => Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- pointwise
  set fA : Fin 2 → CollarSample W → ℝ := fun k ω => ∑ a, ‖(ω.1.1 k *ᵥ fun c => q (k, c)) a‖ ^ 2
  set fB : CollarSample W → ℝ := fun ω => ∑ p, ‖((bondMatrix .common ω.1.2)ᴴ *ᵥ q) p‖ ^ 2
  have hpt : ∀ ω, ENNReal.ofReal (∑ x, ‖collarRowVec w q ω x‖ ^ 2) ≤
      ENNReal.ofReal (2 * ‖w‖ ^ 2 * Sq) + 2 * ENNReal.ofReal (fA 0 ω) + 2 * ENNReal.ofReal (fA 1 ω) +
        ENNReal.ofReal (fB ω) := by
    intro ω
    have hA0 : 0 ≤ fA 0 ω := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hA1 : 0 ≤ fA 1 ω := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hB0 : 0 ≤ fB ω := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hsplit : ∑ x, ‖collarRowVec w q ω x‖ ^ 2 =
        ∑ i, ‖(w • q - blockDiag ω.1.1 *ᵥ q) i‖ ^ 2 + fB ω := by
      rw [Fintype.sum_sum_type]
      simp only [collarRowVec, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, norm_neg, fB]
    have hA : ∑ i, ‖(w • q - blockDiag ω.1.1 *ᵥ q) i‖ ^ 2 ≤
        2 * ‖w‖ ^ 2 * Sq + 2 * (fA 0 ω + fA 1 ω) := by
      have h1 : ∀ i, ‖(w • q - blockDiag ω.1.1 *ᵥ q) i‖ ^ 2 ≤
          2 * (‖w‖ ^ 2 * ‖q i‖ ^ 2) + 2 * ‖(blockDiag ω.1.1 *ᵥ q) i‖ ^ 2 := by
        intro i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have := norm_sub_le (w * q i) ((blockDiag ω.1.1 *ᵥ q) i)
        rw [norm_mul] at this
        nlinarith [norm_nonneg (w * q i - (blockDiag ω.1.1 *ᵥ q) i), norm_nonneg w,
          norm_nonneg (q i), norm_nonneg ((blockDiag ω.1.1 *ᵥ q) i),
          sq_nonneg (‖w‖ * ‖q i‖ - ‖(blockDiag ω.1.1 *ᵥ q) i‖)]
      refine (Finset.sum_le_sum fun i _ => h1 i).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        sum_norm_sq_blockDiag_mulVec, Fin.sum_univ_two]
      ring
    rw [hsplit, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) hB0]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith
  have hmA : ∀ k, Measurable fun ω => ENNReal.ofReal (fA k ω) := fun k => by
    have hc : Continuous fun M : Matrix (Fin W) (Fin W) ℂ =>
        ENNReal.ofReal (∑ a, ‖(M *ᵥ fun c => q (k, c)) a‖ ^ 2) :=
      ENNReal.continuous_ofReal.comp (continuous_finsetSum _ fun a _ =>
        (((continuous_apply a).comp (continuous_id.matrix_mulVec continuous_const)).norm).pow 2)
    exact hc.measurable.comp ((measurable_pi_apply k).comp (measurable_fst.comp measurable_fst))
  have hmB : Measurable fun ω => ENNReal.ofReal (fB ω) := by
    have h := measurable_collarRowVec (W := W) 0 q
    have hc : Continuous fun u : LayerSite W .common → ℂ => ∑ p : PortSite W .common,
        ‖u (Sum.inr p)‖ ^ 2 :=
      continuous_finsetSum _ fun p _ => ((continuous_apply _).norm).pow 2
    have : (fun ω : CollarSample W => ENNReal.ofReal (fB ω)) =
        fun ω => ENNReal.ofReal (∑ p : PortSite W .common,
          ‖collarRowVec 0 q (ω.1, (0 : Matrix (PortSite W .common) (PortSite W .common) ℂ))
            (Sum.inr p)‖ ^ 2) := by
      funext ω; simp [collarRowVec, fB]
    rw [this]
    exact (hc.measurable.comp (h.comp (measurable_fst.prodMk measurable_const))).ennreal_ofReal
  have ht : ((Real.toNNReal ((1 - 2 * b) / W) : ℝ≥0) : ℝ) = (1 - 2 * b) / W :=
    Real.coe_toNNReal _ (div_nonneg (by linarith) hWr.le)
  have hbW : ((Real.toNNReal (b / W) : ℝ≥0) : ℝ) = b / W := Real.coe_toNNReal _ (by positivity)
  calc ∫⁻ ω, ENNReal.ofReal (∑ x, ‖collarRowVec w q ω x‖ ^ 2) ∂collarLaw W b
      ≤ ∫⁻ ω, (ENNReal.ofReal (2 * ‖w‖ ^ 2 * Sq) + 2 * ENNReal.ofReal (fA 0 ω) +
          2 * ENNReal.ofReal (fA 1 ω) + ENNReal.ofReal (fB ω)) ∂collarLaw W b := lintegral_mono hpt
    _ = ENNReal.ofReal (2 * ‖w‖ ^ 2 * Sq) + 2 * ∫⁻ ω, ENNReal.ofReal (fA 0 ω) ∂collarLaw W b +
          2 * ∫⁻ ω, ENNReal.ofReal (fA 1 ω) ∂collarLaw W b +
            ∫⁻ ω, ENNReal.ofReal (fB ω) ∂collarLaw W b := by
        rw [lintegral_add_right _ hmB, lintegral_add_right _ ((hmA 1).const_mul _),
          lintegral_add_right _ ((hmA 0).const_mul _), lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ (hmA 0), lintegral_const_mul _ (hmA 1)]
    _ ≤ ENNReal.ofReal (2 * ‖w‖ ^ 2 * Sq) +
          2 * ENNReal.ofReal (W * Real.toNNReal ((1 - 2 * b) / W) * Sk 0) +
          2 * ENNReal.ofReal (W * Real.toNNReal ((1 - 2 * b) / W) * Sk 1) +
            ENNReal.ofReal (W * Real.toNNReal (b / W) * Sq) := by
        rw [lintegral_norm_sq_bond_collar]
        gcongr
        · exact lintegral_norm_sq_block_le b 0 q
        · exact lintegral_norm_sq_block_le b 1 q
    _ = ENNReal.ofReal ((2 * ‖w‖ ^ 2 + 2 * (1 - 2 * b) + b) * Sq) := by
        have hc0 : (0 : ℝ) ≤ W * Real.toNNReal ((1 - 2 * b) / W) :=
          mul_nonneg (Nat.cast_nonneg _) (NNReal.coe_nonneg _)
        have hb0' : (0 : ℝ) ≤ W * Real.toNNReal (b / W) :=
          mul_nonneg (Nat.cast_nonneg _) (NNReal.coe_nonneg _)
        have e0 : 0 ≤ 2 * ‖w‖ ^ 2 * Sq := by positivity
        have e1 : 0 ≤ 2 * (W * Real.toNNReal ((1 - 2 * b) / W) * Sk 0) :=
          mul_nonneg (by norm_num) (mul_nonneg hc0 (hSk0 0))
        have e2 : 0 ≤ 2 * (W * Real.toNNReal ((1 - 2 * b) / W) * Sk 1) :=
          mul_nonneg (by norm_num) (mul_nonneg hc0 (hSk0 1))
        have e3 : 0 ≤ W * Real.toNNReal (b / W) * Sq := mul_nonneg hb0' hSq
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add e0 e1, ← ENNReal.ofReal_add (add_nonneg e0 e1) e2,
          ← ENNReal.ofReal_add (add_nonneg (add_nonneg e0 e1) e2) e3, ht, hbW]
        congr 1
        rw [← hSk]
        field_simp
        ring

/-- `Im⟨y,(H - i)⁻¹y⟩ ≤ ‖y‖²` for Hermitian `H`. -/
theorem im_dotProduct_inv_sub_I_le {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (y : ι → ℂ) :
    (star y ⬝ᵥ ((H - (⟨0, 1⟩ : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ y)).im ≤ ∑ a, ‖y a‖ ^ 2 := by
  rw [inv_sub_eq_specSum hH (by simp), dotProduct_specSum_mulVec, Complex.im_sum,
    sum_norm_sq_eq_sum_eigen hH y]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [Complex.im_mul_ofReal]
  refine mul_le_of_le_one_left (sq_nonneg _) ?_
  set l := increasingEigenvalue hH r
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
  have h : 0 < (l - 0) * (l - 0) + (0 - 1) * (0 - 1) := by nlinarith
  rw [div_le_one h]
  nlinarith

/-- `E π⁻¹ Im⟨y,(ℋ - i)⁻¹y⟩ ≤ π⁻¹(2|w|² + 2(1-2b) + b)‖q‖²`, uniformly in `W`. -/
theorem lintegral_collarRowForm_I_le (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (e : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (w : ℂ)
    (q : Fin 2 × Fin W → ℂ) :
    ∫⁻ ω, ENNReal.ofReal (Real.pi⁻¹ * (star (collarRowVec w q ω) ⬝ᵥ
        ((collarMatrix e X ω - (⟨0, 1⟩ : ℂ) • (1 : Matrix (LayerSite W .common)
          (LayerSite W .common) ℂ))⁻¹ *ᵥ collarRowVec w q ω)).im) ∂collarLaw W b ≤
      ENNReal.ofReal (Real.pi⁻¹ * ((2 * ‖w‖ ^ 2 + 2 * (1 - 2 * b) + b) * ∑ x, ‖q x‖ ^ 2)) := by
  have hpi : 0 ≤ Real.pi⁻¹ := inv_nonneg.2 Real.pi_pos.le
  calc ∫⁻ ω, ENNReal.ofReal (Real.pi⁻¹ * (star (collarRowVec w q ω) ⬝ᵥ
        ((collarMatrix e X ω - (⟨0, 1⟩ : ℂ) • (1 : Matrix (LayerSite W .common)
          (LayerSite W .common) ℂ))⁻¹ *ᵥ collarRowVec w q ω)).im) ∂collarLaw W b
      ≤ ∫⁻ ω, ENNReal.ofReal Real.pi⁻¹ * ENNReal.ofReal (∑ x, ‖collarRowVec w q ω x‖ ^ 2)
          ∂collarLaw W b := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_collarMatrix_isHermitian (W := W) b e hX] with ω hω
        rw [← ENNReal.ofReal_mul hpi]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
          (im_dotProduct_inv_sub_I_le hω.1 _) hpi)
    _ = ENNReal.ofReal Real.pi⁻¹ * ∫⁻ ω, ENNReal.ofReal (∑ x, ‖collarRowVec w q ω x‖ ^ 2)
          ∂collarLaw W b := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal Real.pi⁻¹ * ENNReal.ofReal ((2 * ‖w‖ ^ 2 + 2 * (1 - 2 * b) + b) *
          ∑ x, ‖q x‖ ^ 2) := by gcongr; exact lintegral_norm_sq_collarRowVec_le hb0 hb hW w q
    _ = _ := by rw [← ENNReal.ofReal_mul hpi]

/-- **Regular phase bound with a `W`-uniform tail** (variant of
`lintegral_collarRow_le_of_regular`; same hypotheses). -/
theorem lintegral_collarRow_le_of_regular' (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ' dstar Cr : ℝ} {W₀ : ℕ} (hreg : CollarDensityRegularClause b κ' dstar Cr W₀)
    (hW₀ : W₀ ≤ W) {e' δ : ℝ} (hδ : 0 < δ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) (z : ℂ) {M η : ℝ} (hη : 0 < η)
    (hwin : ∀ x : ℝ, |x| ≤ δ → e' + x ∈ bulkInterval κ' ∧ matchedDistance b (e' + x) X ≤ dstar ∧
      η ≤ (boundaryZ b (e' + x)).im ∧ ‖z - x - boundaryZ b (e' + x)‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) (q : Fin 2 × Fin W → ℂ) :
    ∫⁻ ω, ENNReal.ofReal (Real.pi⁻¹ * (star (collarRowVec (star z + e') q ω) ⬝ᵥ
        ((collarMatrix e' X ω - (⟨0, ε⟩ : ℂ) • (1 : Matrix (LayerSite W .common)
          (LayerSite W .common) ℂ))⁻¹ *ᵥ collarRowVec (star z + e') q ω)).im) ∂collarLaw W b ≤
      ENNReal.ofReal (2 * max Cr 0 * (1 + M ^ 2 / η ^ 2) * ∑ a, ‖q a‖ ^ 2) +
        ENNReal.ofReal (ε * (1 + δ⁻¹ ^ 2)) * ENNReal.ofReal (Real.pi⁻¹ *
          ((2 * ‖star z + (e' : ℂ)‖ ^ 2 + 2 * (1 - 2 * b) + b) * ∑ a, ‖q a‖ ^ 2)) := by
  rw [← lintegral_cauchyKernel_collarWeightedForm hW hb e' hX z q hε]
  set A := 2 * max Cr 0 * (1 + M ^ 2 / η ^ 2) * ∑ a, ‖q a‖ ^ 2
  set ρ := collarWeightedForm W b e' X z q
  have hρ0 : ∀ x, 0 ≤ ρ x := collarWeightedForm_nonneg hW b e' hX z q
  have hP0 : ∀ ε' x, 0 < ε' → 0 ≤ cauchyKernel ε' x := fun ε' x h => cauchyKernel_nonneg h.le x
  have hc0 : 0 ≤ ε * (1 + δ⁻¹ ^ 2) := by positivity
  have hpt : ∀ x, ENNReal.ofReal (cauchyKernel ε (0 - x) * ρ x) ≤
      ENNReal.ofReal (cauchyKernel ε (0 - x)) * ENNReal.ofReal A +
        ENNReal.ofReal (ε * (1 + δ⁻¹ ^ 2)) * ENNReal.ofReal (cauchyKernel 1 (0 - x) * ρ x) := by
    intro x
    by_cases hx : |x| ≤ δ
    · obtain ⟨h1, h2, h3, h4⟩ := hwin x hx
      have hw := collarWeightedForm_le_of_regular hW hreg hW₀ h1 hX h2 z hη h3 h4 q
      refine le_add_right ?_
      rw [← ENNReal.ofReal_mul (hP0 ε _ hε)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hw (hP0 ε _ hε))
    · push Not at hx
      have ht := cauchyKernel_le_tail hε hδ (x := 0 - x) (by rw [zero_sub, abs_neg]; exact hx.le)
      refine le_add_left ?_
      rw [← ENNReal.ofReal_mul hc0]
      refine ENNReal.ofReal_le_ofReal ?_
      calc cauchyKernel ε (0 - x) * ρ x ≤ ε * (1 + δ⁻¹ ^ 2) * cauchyKernel 1 (0 - x) * ρ x :=
            mul_le_mul_of_nonneg_right ht (hρ0 x)
        _ = _ := by ring
  have hm1 : Measurable fun x : ℝ => ENNReal.ofReal (cauchyKernel ε (0 - x)) * ENNReal.ofReal A :=
    (((continuous_cauchyKernel hε).comp (continuous_const.sub continuous_id)).measurable
      ).ennreal_ofReal.mul_const _
  calc ∫⁻ x, ENNReal.ofReal (cauchyKernel ε (0 - x) * ρ x)
      ≤ ∫⁻ x, (ENNReal.ofReal (cauchyKernel ε (0 - x)) * ENNReal.ofReal A +
          ENNReal.ofReal (ε * (1 + δ⁻¹ ^ 2)) * ENNReal.ofReal (cauchyKernel 1 (0 - x) * ρ x)) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal A + ENNReal.ofReal (ε * (1 + δ⁻¹ ^ 2)) *
          ∫⁻ x, ENNReal.ofReal (cauchyKernel 1 (0 - x) * ρ x) := by
        rw [lintegral_add_left hm1, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          lintegral_ofReal_cauchyKernel hε, one_mul, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := by
        gcongr
        rw [lintegral_cauchyKernel_collarWeightedForm hW hb e' hX z q one_pos]
        exact lintegral_collarRowForm_I_le hW hb0 hb e' hX _ q

end BlockBand.Critical.Collar.Density
