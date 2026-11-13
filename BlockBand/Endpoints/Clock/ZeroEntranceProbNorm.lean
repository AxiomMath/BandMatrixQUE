module

public import BlockBand.Endpoints.Clock.ZeroEntranceProbDefs
public import BlockBand.Layers.BondMoments

/-!
# The zero-entrance lemma: operator-norm moments of the fresh blocks

Every derivative of the blocks of a fresh layer has a fixed polynomial bound in `1+‖A‖+‖B‖`; the
moments of `‖A‖` and `‖B‖` below are used for the perturbation in the initial matrix. No contract
is used.

The law is `layerLaw W b .oneBlockOnePort`; `ω.1 0 = A ~ GUE_W((1-2b)/W)` (`gueMeasure`,
`A = √(t/2)(X + Xᴴ)` with `X` of standard circular entries), `ω.2 0 0 = B ~ Gin(b/W)`. All norms
are `ℓ²` operator norms (`Matrix.Norms.L2Operator`).

* `opNorm_submatrix_le`, `opNorm_submatrix_equiv`, `opNorm_toBlocks11_le` (and `12`, `21`, `22`):
  reindexing by injections does not increase the operator norm; by equivalences it preserves it;
  blocks are bounded by the whole matrix.
* `bondBlock_lintegral_pow_le`: for every `q : ℕ`, `E‖B‖^q ≤ C_q` for `W ≥ max q 1`, uniformly
  in `0 < b < 1/2` (from `bond_lintegral_rpow_le`, `C₂(b) = 6(1+10√b)` increasing in `b`).
* `gueBlock_lintegral_pow_le`: for every `q : ℕ`, `E‖A‖^q ≤ 100^q` for `W ≥ max q 1`, uniformly
  in `0 ≤ b < 1/2`. Proof: `‖A‖ ≤ √(2t)‖X‖`; the circular matrix `X` has law `Gin(1)`
  (`commonCircularIncrementLaw_map_circMat`, via `whiteNoise_map_linear`), which is the bond law
  of the layer with `b = W`, so `bond_lintegral_rpow_le` gives `E‖X‖^q ≤ (6(1+10√W))^q`, and
  `√(2t) · 6(1+10√W) ≤ 100` for `t ≤ 1/W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Layers BlockBand.SourceProcess
open scoped ENNReal NNReal Matrix.Norms.L2Operator ComplexConjugate

/-!
## Operator norm of reindexed matrices and of blocks
-/

namespace ZeroEntranceNorm

/-- The selection matrix of `f : m → n`: `S_ij = 1{f i = j}`, so `S M Tᴴ = M.submatrix f g`. -/
def selMat {m n : Type*} [DecidableEq n] (f : m → n) : Matrix m n ℂ :=
  Matrix.of fun i j => if f i = j then 1 else 0

theorem selMat_mul_conjTranspose {m n : Type*} [Fintype n] [DecidableEq m] [DecidableEq n]
    {f : m → n} (hf : f.Injective) : selMat f * (selMat f)ᴴ = 1 := by
  ext i i'
  simp only [selMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.one_apply]
  have : ∀ j, (if f i = j then (1 : ℂ) else 0) * star (if f i' = j then (1 : ℂ) else 0) =
      if f i = j then (if f i' = j then 1 else 0) else 0 := by
    intro j; split_ifs <;> simp
  simp only [this, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, hf.eq_iff]
  by_cases h : i = i' <;> simp [h, eq_comm]

theorem submatrix_eq_selMat {m n k l : Type*} [Fintype n] [Fintype l] [DecidableEq n]
    [DecidableEq l] (M : Matrix n l ℂ) (f : m → n) (g : k → l) :
    M.submatrix f g = selMat f * M * (selMat g)ᴴ := by
  ext i i'
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, selMat, Matrix.of_apply,
    Matrix.conjTranspose_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte]
  have : ∀ j, M (f i) j * star (if g i' = j then (1 : ℂ) else 0) =
      if g i' = j then M (f i) j else 0 := by
    intro j; split_ifs <;> simp
  simp only [this, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

theorem norm_one_le {m : Type*} [Fintype m] [DecidableEq m] :
    ‖(1 : Matrix m m ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun _ => by simp

theorem norm_selMat_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {f : m → n} (hf : f.Injective) : ‖selMat f‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (selMat f)ᴴ
  rw [Matrix.conjTranspose_conjTranspose, selMat_mul_conjTranspose hf,
    Matrix.l2_opNorm_conjTranspose] at h
  have h1 := norm_one_le (m := m)
  rw [h] at h1
  nlinarith [norm_nonneg (selMat f)]

end ZeroEntranceNorm

open ZeroEntranceNorm

/-- Reindexing by injections does not increase the `L²` operator norm. -/
theorem opNorm_submatrix_le {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]
    [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq l] (M : Matrix n l ℂ)
    {f : m → n} {g : k → l} (hf : f.Injective) (hg : g.Injective) :
    ‖M.submatrix f g‖ ≤ ‖M‖ := by
  rw [submatrix_eq_selMat]
  calc ‖selMat f * M * (selMat g)ᴴ‖ ≤ ‖selMat f * M‖ * ‖(selMat g)ᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖selMat f‖ * ‖M‖ * ‖(selMat g)ᴴ‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * ‖M‖ * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
        · exact norm_selMat_le hf
        · exact norm_selMat_le hg
    _ = ‖M‖ := by ring

/-- Reindexing by two equivalences preserves the `L²` operator norm. -/
theorem opNorm_submatrix_equiv_equiv {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k]
    [Fintype l] [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq l]
    (M : Matrix n l ℂ) (f : m ≃ n) (g : k ≃ l) : ‖M.submatrix f g‖ = ‖M‖ := by
  refine le_antisymm (opNorm_submatrix_le M f.injective g.injective) ?_
  have h : M = (M.submatrix f g).submatrix f.symm g.symm := by
    simp [Matrix.submatrix_submatrix]
  calc ‖M‖ = ‖(M.submatrix f g).submatrix f.symm g.symm‖ := by rw [← h]
    _ ≤ ‖M.submatrix f g‖ := opNorm_submatrix_le _ f.symm.injective g.symm.injective

/-- Reindexing by an equivalence preserves the `L²` operator norm. -/
theorem opNorm_submatrix_equiv {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (M : Matrix n n ℂ) (f : m ≃ n) : ‖M.submatrix f f‖ = ‖M‖ :=
  opNorm_submatrix_equiv_equiv M f f

section Blocks

variable {l m : Type*} [Fintype l] [Fintype m] [DecidableEq l] [DecidableEq m]

theorem opNorm_toBlocks11_le (M : Matrix (l ⊕ m) (l ⊕ m) ℂ) : ‖M.toBlocks₁₁‖ ≤ ‖M‖ :=
  opNorm_submatrix_le M (f := Sum.inl) (g := Sum.inl) Sum.inl_injective Sum.inl_injective

theorem opNorm_toBlocks12_le (M : Matrix (l ⊕ m) (l ⊕ m) ℂ) : ‖M.toBlocks₁₂‖ ≤ ‖M‖ :=
  opNorm_submatrix_le M (f := Sum.inl) (g := Sum.inr) Sum.inl_injective Sum.inr_injective

theorem opNorm_toBlocks21_le (M : Matrix (l ⊕ m) (l ⊕ m) ℂ) : ‖M.toBlocks₂₁‖ ≤ ‖M‖ :=
  opNorm_submatrix_le M (f := Sum.inr) (g := Sum.inl) Sum.inr_injective Sum.inl_injective

theorem opNorm_toBlocks22_le (M : Matrix (l ⊕ m) (l ⊕ m) ℂ) : ‖M.toBlocks₂₂‖ ≤ ‖M‖ :=
  opNorm_submatrix_le M (f := Sum.inr) (g := Sum.inr) Sum.inr_injective Sum.inr_injective

end Blocks

/-!
## Marginals of the layer law
-/

namespace ZeroEntranceNorm

theorem lintegral_gueBlock {W : ℕ} (b : ℝ) {f : Matrix (Fin W) (Fin W) ℂ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ ω, f (ω.1 0) ∂layerLaw W b .oneBlockOnePort =
      ∫⁻ A, f A ∂gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W)) := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  have h1 : MeasurePreserving (fun ω : LayerSample W .oneBlockOnePort => ω.1)
      (layerLaw W b .oneBlockOnePort)
      (Measure.pi fun _ : Fin 1 => gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) := by
    unfold layerLaw; exact measurePreserving_fst
  have h2 := measurePreserving_eval
    (μ := fun _ : Fin 1 => gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) 0
  exact (h2.comp h1).lintegral_comp hf

theorem lintegral_bondBlock {W : ℕ} (b : ℝ) {f : Matrix (Fin W) (Fin W) ℂ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ ω, f (ω.2 0 0) ∂layerLaw W b .oneBlockOnePort =
      ∫⁻ B, f B ∂ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)) := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  have h1 : MeasurePreserving (fun ω : LayerSample W .oneBlockOnePort => ω.2)
      (layerLaw W b .oneBlockOnePort)
      (Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin 1 =>
        ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) := by
    unfold layerLaw; exact measurePreserving_snd
  have h2 := measurePreserving_eval (μ := fun _ : Fin 1 => Measure.pi fun _ : Fin 1 =>
    ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) 0
  have h3 := measurePreserving_eval
    (μ := fun _ : Fin 1 => ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) 0
  exact ((h3.comp h2).comp h1).lintegral_comp hf

/-- The one-block bond matrix is a reindexing of `ω.2 0 0`. -/
theorem bondMatrix_oneBlock_eq {W : ℕ} (B : Fin 1 → Fin 1 → Matrix (Fin W) (Fin W) ℂ) :
    bondMatrix .oneBlockOnePort B = (B 0 0).submatrix (Equiv.uniqueProd (Fin W) (Fin 1))
      (Equiv.uniqueProd (Fin W) (Fin 1)) := by
  ext x y
  obtain ⟨a, i⟩ := x
  obtain ⟨c, j⟩ := y
  have ha : a = 0 := Subsingleton.elim _ _
  have hc : c = 0 := Subsingleton.elim _ _
  subst ha hc
  simp [bondMatrix, LayerShape.incident]

theorem norm_bondBlock_eq {W : ℕ} (B : Fin 1 → Fin 1 → Matrix (Fin W) (Fin W) ℂ) :
    ‖bondMatrix .oneBlockOnePort B‖ = ‖B 0 0‖ := by
  rw [bondMatrix_oneBlock_eq]; exact opNorm_submatrix_equiv _ _

theorem enorm_pow_le_ofReal {E : Type*} [SeminormedAddCommGroup E] (x : E) (q : ℕ) :
    ‖x‖ₑ ^ q ≤ ENNReal.ofReal ((1 + ‖x‖) ^ (q : ℝ)) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.rpow_natCast]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (by linarith) q)

/-- `E‖B‖^q ≤ C₂(b)^q` for `1 ≤ q ≤ W`. -/
theorem bond_lintegral_pow_le_aux {W : ℕ} {b : ℝ} (hb : 0 < b) {q : ℕ} (hq : 1 ≤ q)
    (hqW : q ≤ W) :
    ∫⁻ ω, ‖(ω.2 0 0 : Matrix (Fin W) (Fin W) ℂ)‖ₑ ^ q ∂layerLaw W b .oneBlockOnePort ≤
      ENNReal.ofReal (bondMomentConst b ^ (q : ℝ)) := by
  refine le_trans (lintegral_mono fun ω => ?_)
    (bond_lintegral_rpow_le .oneBlockOnePort hb (q := q) (by exact_mod_cast hq)
      (by exact_mod_cast hqW))
  rw [norm_bondBlock_eq]
  exact enorm_pow_le_ofReal _ q

/-!
## The circular matrix of the GUE sample
-/

/-- The matrix of a flat complex array. -/
def circMat {ι : Type*} (X : ι × ι → ℂ) : Matrix ι ι ℂ := Matrix.of fun a b => X (a, b)

theorem measurable_circMat {ι : Type*} [Fintype ι] : Measurable (circMat (ι := ι)) := by
  refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
  exact measurable_pi_apply (a, b)

theorem measurable_circularBrownianCoordinates {ι : Type*} [Fintype ι] :
    Measurable (circularBrownianCoordinates (ι := ι)) := by
  apply Measurable.of_eval
  intro u
  unfold circularBrownianCoordinates
  fun_prop

theorem measurable_gueSample' {ι : Type*} [Fintype ι] (t : ℝ≥0) :
    Measurable (gueSample (ι := ι) t) := by
  refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
  simp only [gueSample, Matrix.of_apply]
  have h1 : Measurable fun X : ι × ι → ℂ => X (a, b) := measurable_pi_apply _
  have h2 : Measurable fun X : ι × ι → ℂ => X (b, a) := measurable_pi_apply _
  exact measurable_const.mul (h1.add (continuous_star.measurable.comp h2))

/-- The reindexing `ι × ι × Fin 2 ≃ (ι × ι) × Fin 2`. -/
abbrev flatEquiv (ι : Type*) : ι × ι × Fin 2 ≃ (ι × ι) × Fin 2 :=
  (Equiv.prodAssoc ι ι (Fin 2)).symm

/-- The linear map `r ↦ r ∘ e / √2`. -/
def circCoef (ι : Type*) [DecidableEq ι] (k : ι × ι × Fin 2) (i : (ι × ι) × Fin 2) : ℝ :=
  if i = flatEquiv ι k then (Real.sqrt 2)⁻¹ else 0

theorem circCoef_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (r : (ι × ι) × Fin 2 → ℝ)
    (k : ι × ι × Fin 2) : ∑ i, circCoef ι k i * r i = (Real.sqrt 2)⁻¹ * r (flatEquiv ι k) := by
  simp only [circCoef, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem circCoef_isometry {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ι × ι × Fin 2 → ℝ) :
    ∑ i, (∑ k, t k * circCoef ι k i) ^ 2 = ((1 / 2 : ℝ≥0) : ℝ) * ∑ k, t k ^ 2 := by
  rw [← Equiv.sum_comp (flatEquiv ι)]
  have h : ∀ k : ι × ι × Fin 2, ∑ k', t k' * circCoef ι k' (flatEquiv ι k) =
      t k * (Real.sqrt 2)⁻¹ := by
    intro k
    simp only [circCoef, (flatEquiv ι).injective.eq_iff, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
  simp only [h, mul_pow, inv_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [← Finset.sum_mul, mul_comm]
  push_cast
  ring

/-- The circular matrix has the law `Gin(1)`. -/
theorem commonCircularIncrementLaw_map_circMat (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (commonCircularIncrementLaw ι 1).map circMat = ginibreMeasure ι ι 1 := by
  set L : ((ι × ι) × Fin 2 → ℝ) → (ι × ι × Fin 2 → ℝ) :=
    fun x k => ∑ i, circCoef ι k i * x i with hL
  have hLm : Measurable L := by rw [hL]; fun_prop
  have hcomp : circMat ∘ circularBrownianCoordinates = ginibreAssemble ∘ L := by
    funext r
    ext a b
    simp only [Function.comp_apply, circMat, circularBrownianCoordinates, ginibreAssemble,
      Matrix.of_apply, hL, circCoef_sum]
    simp only [flatEquiv, Equiv.prodAssoc_symm_apply]
    push_cast
    ring
  unfold commonCircularIncrementLaw
  rw [Measure.map_map measurable_circMat measurable_circularBrownianCoordinates, hcomp,
    ← Measure.map_map measurable_ginibreAssemble hLm]
  have hw := whiteNoise_map_linear (ι := (ι × ι) × Fin 2) (κ := ι × ι × Fin 2) 1 (1 / 2)
    (circCoef ι) circCoef_isometry
  change ((whiteNoise ((ι × ι) × Fin 2) 1).map L).map ginibreAssemble = _
  rw [hL, hw, ginibreMeasure_eq_map]
  congr 2
  norm_num

theorem gueSample_eq {ι : Type*} (t : ℝ≥0) (X : ι × ι → ℂ) :
    gueSample t X = ((Real.sqrt ((t : ℝ) / 2) : ℝ) : ℂ) • (circMat X + (circMat X)ᴴ) := by
  ext a b
  simp [gueSample, circMat, Matrix.conjTranspose_apply]

theorem norm_gueSample_le {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℝ≥0) (X : ι × ι → ℂ) :
    ‖gueSample t X‖ ≤ 2 * Real.sqrt ((t : ℝ) / 2) * ‖circMat X‖ := by
  rw [gueSample_eq]
  refine (norm_smul_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have : ‖circMat X + (circMat X)ᴴ‖ ≤ 2 * ‖circMat X‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose]; ring_nf; rfl
  calc Real.sqrt ((t : ℝ) / 2) * ‖circMat X + (circMat X)ᴴ‖
      ≤ Real.sqrt ((t : ℝ) / 2) * (2 * ‖circMat X‖) :=
        mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt ((t : ℝ) / 2) * ‖circMat X‖ := by ring

/-- `E‖X‖^q ≤ (6(1+10√W))^q` for the `Gin(1)` matrix, `1 ≤ q ≤ W`. -/
theorem ginibreOne_lintegral_pow_le {W : ℕ} {q : ℕ} (hq : 1 ≤ q) (hqW : q ≤ W) :
    ∫⁻ M, ‖(M : Matrix (Fin W) (Fin W) ℂ)‖ₑ ^ q ∂ginibreMeasure (Fin W) (Fin W) 1 ≤
      ENNReal.ofReal (bondMomentConst W ^ (q : ℝ)) := by
  have hW : (0 : ℝ) < W := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hq.trans hqW
    linarith
  have hf : Measurable fun M : Matrix (Fin W) (Fin W) ℂ => ‖M‖ₑ ^ q :=
    continuous_enorm.measurable.pow_const _
  have h1 : Real.toNNReal ((W : ℝ) / W) = 1 := by
    rw [div_self hW.ne']; simp
  have h := lintegral_bondBlock (W := W) (W : ℝ) hf
  rw [h1] at h
  rw [← h]
  exact bond_lintegral_pow_le_aux hW hq hqW

end ZeroEntranceNorm

/-!
## The moment bounds
-/

/-- **Bond moments**: `E‖B‖^q ≤ C` for `W ≥ W₀(q)`, uniformly in
`0 < b < 1/2`. -/
theorem bondBlock_lintegral_pow_le (q : ℕ) : ∃ (C : ℝ) (W₀ : ℕ), 0 < C ∧
    ∀ W : ℕ, W₀ ≤ W → ∀ b : ℝ, 0 < b → b < 1 / 2 →
      ∫⁻ ω, ‖(ω.2 0 0 : Matrix (Fin W) (Fin W) ℂ)‖ₑ ^ q ∂layerLaw W b .oneBlockOnePort ≤
        ENNReal.ofReal C := by
  refine ⟨bondMomentConst (1 / 2) ^ (q : ℝ), max q 1,
    Real.rpow_pos_of_pos (bondMomentConst_pos _) _, fun W hW b hb0 hb1 => ?_⟩
  have := bond_isProbabilityMeasure_layerLaw W b .oneBlockOnePort
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp
  · refine (ZeroEntranceNorm.bond_lintegral_pow_le_aux hb0 hq
      ((le_max_left _ _).trans hW)).trans (ENNReal.ofReal_le_ofReal ?_)
    refine Real.rpow_le_rpow (bondMomentConst_pos _).le ?_ (Nat.cast_nonneg _)
    unfold bondMomentConst
    gcongr

/-- **GUE block moments**: `E‖A‖^q ≤ 100^q` for `W ≥ max q 1`,
uniformly in `0 ≤ b < 1/2`. -/
theorem gueBlock_lintegral_pow_le (q : ℕ) : ∃ (C : ℝ) (W₀ : ℕ), 0 < C ∧
    ∀ W : ℕ, W₀ ≤ W → ∀ b : ℝ, 0 ≤ b → b < 1 / 2 →
      ∫⁻ ω, ‖(ω.1 0 : Matrix (Fin W) (Fin W) ℂ)‖ₑ ^ q ∂layerLaw W b .oneBlockOnePort ≤
        ENNReal.ofReal C := by
  open ZeroEntranceNorm in
  refine ⟨100 ^ q, max q 1, by positivity, fun W hW b hb0 hb1 => ?_⟩
  have := bond_isProbabilityMeasure_layerLaw W b .oneBlockOnePort
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp
  have hqW : q ≤ W := (le_max_left _ _).trans hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (le_max_right _ _).trans hW
  have hW0 : (0 : ℝ) < W := by linarith
  set t : ℝ≥0 := Real.toNNReal ((1 - 2 * b) / W) with ht
  set x : ℝ := 2 * Real.sqrt ((t : ℝ) / 2) with hx
  have hx0 : 0 ≤ x := by positivity
  have hf : Measurable fun M : Matrix (Fin W) (Fin W) ℂ => ‖M‖ₑ ^ q :=
    continuous_enorm.measurable.pow_const _
  rw [lintegral_gueBlock b hf]
  change ∫⁻ A, ‖A‖ₑ ^ q ∂(commonCircularIncrementLaw (Fin W) 1).map (gueSample t) ≤ _
  rw [lintegral_map hf (measurable_gueSample' t)]
  have hpt : ∀ X : Fin W × Fin W → ℂ,
      ‖gueSample t X‖ₑ ^ q ≤ ENNReal.ofReal x ^ q * ‖circMat X‖ₑ ^ q := by
    intro X
    rw [← mul_pow]
    refine pow_le_pow_left₀ bot_le ?_ q
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hx0]
    exact ENNReal.ofReal_le_ofReal (norm_gueSample_le t X)
  have hcm : Measurable fun X : Fin W × Fin W → ℂ => ‖circMat X‖ₑ ^ q :=
    hf.comp measurable_circMat
  calc ∫⁻ X, ‖gueSample t X‖ₑ ^ q ∂commonCircularIncrementLaw (Fin W) 1
      ≤ ∫⁻ X, ENNReal.ofReal x ^ q * ‖circMat X‖ₑ ^ q ∂commonCircularIncrementLaw (Fin W) 1 :=
        lintegral_mono hpt
    _ = ENNReal.ofReal x ^ q *
          ∫⁻ X, ‖circMat X‖ₑ ^ q ∂commonCircularIncrementLaw (Fin W) 1 :=
        lintegral_const_mul _ hcm
    _ = ENNReal.ofReal x ^ q * ∫⁻ M, ‖M‖ₑ ^ q ∂ginibreMeasure (Fin W) (Fin W) 1 := by
        rw [← commonCircularIncrementLaw_map_circMat, lintegral_map hf measurable_circMat]
    _ ≤ ENNReal.ofReal x ^ q * ENNReal.ofReal (bondMomentConst W ^ (q : ℝ)) :=
        mul_le_mul_right (ginibreOne_lintegral_pow_le hq hqW) _
    _ ≤ ENNReal.ofReal (100 ^ q) := by
        rw [← ENNReal.ofReal_pow hx0, ← ENNReal.ofReal_mul (by positivity), Real.rpow_natCast,
          ← mul_pow]
        refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (mul_nonneg hx0
          (bondMomentConst_pos _).le) ?_ q)
        -- `x · 6(1 + 10√W) ≤ 100`
        have htW : (t : ℝ) ≤ 1 / W := by
          rw [ht, Real.coe_toNNReal']
          refine max_le ?_ (by positivity)
          exact div_le_div_of_nonneg_right (by linarith) hW0.le
        have hx2 : x ^ 2 = 2 * t := by
          rw [hx, mul_pow, Real.sq_sqrt (by positivity)]; ring
        have hsW : 1 ≤ Real.sqrt W := by
          rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hW1
        have hsW2 : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW0.le
        set y := bondMomentConst W with hy
        have hy0 : 0 ≤ y := (bondMomentConst_pos _).le
        have hyle : y ≤ 66 * Real.sqrt W := by
          rw [hy]; unfold bondMomentConst; nlinarith
        have hy2 : y ^ 2 ≤ 4356 * W := by
          have := pow_le_pow_left₀ hy0 hyle 2
          nlinarith
        have hxy2 : (x * y) ^ 2 ≤ 100 ^ 2 := by
          rw [mul_pow, hx2]
          have h2t : 2 * (t : ℝ) * W ≤ 2 := by
            have := mul_le_mul_of_nonneg_right htW hW0.le
            rw [div_mul_cancel₀ _ hW0.ne'] at this
            linarith
          have ht0 : (0 : ℝ) ≤ t := t.2
          nlinarith
        exact (pow_le_pow_iff_left₀ (mul_nonneg hx0 hy0) (by norm_num) two_ne_zero).mp hxy2

end BlockBand.Endpoints.Clock
