module

public import BlockBand.Critical.WeightedDensity.RankOne

/-!
# Rank-one spectral averaging in one embedded GUE block (the `k`-block bound)

*Law.* One diagonal block `G ~ gueMeasure n t` (`t > 0`), embedded as `fromBlocks G 0 0 0` in a
matrix on `n ⊕ m`; everything else (`H`, Hermitian, any finite `m`, no norm bound) is
deterministic, i.e. conditioned on.
*Domain.* every finite block index `n`, every complement `m`, every Hermitian `H`, every `z` with
`Im z > 0`, every vector `y` supported in the block. Exact non-asymptotic bounds, constant
`√(π/(2t))` (for `t = c/W`: `√(πW/(2c))`).

## Main results

* `lintegral_im_resolvent_embed_le`: `E_G Im⟨ŷ, (H + G ⊕ 0 - z)⁻¹ ŷ⟩ ≤ √(π/(2t)) ‖y‖²`,
  `ŷ = (y, 0)`.
* `im_quad_sum_le`: `Im⟨Σ_{j∈s} v_j, R Σ v_j⟩ ≤ |s| Σ_j Im⟨v_j, R v_j⟩` for `R = (H - z)⁻¹`,
  `H` Hermitian, `Im z > 0` (the positivity step `|Σ v_i|_D² ≤ k Σ |v_i|_D²`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw
  BlockBand.Critical.WeightedDensity
open CoareaNative.BlockBand (HermitianCoordinate hermitianMatrixOfCoordinates)
open scoped ENNReal NNReal ComplexConjugate

/-!
## Deterministic resolvent facts on an arbitrary finite index type
-/

section General

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `H - z` is invertible for Hermitian `H` and `Im z > 0` (any finite index type). -/
theorem isUnit_det_sub_smul_one' {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) : IsUnit (H - z • (1 : Matrix ι ι ℂ)).det := by
  have hm : BlockBand.Wegner.HasImMargin z.im (z • (1 : Matrix ι ι ℂ) - H) := by
    intro v
    have h1 : (star v ⬝ᵥ v).im = 0 := by
      have := BlockBand.Wegner.im_star_dotProduct_mulVec_hermitian
        (isHermitian_one (n := ι) (α := ℂ)) v
      rwa [one_mulVec] at this
    rw [sub_mulVec, dotProduct_sub, Complex.sub_im,
      BlockBand.Wegner.im_star_dotProduct_mulVec_hermitian hH, sub_zero, smul_mulVec, one_mulVec,
      dotProduct_smul, smul_eq_mul, Complex.mul_im, h1, mul_zero, zero_add]
  have h := hm.isUnit_det hz
  have heq : H - z • (1 : Matrix ι ι ℂ) = -(z • 1 - H) := by abel
  rw [heq, det_neg]
  exact (isUnit_one.neg.pow _).mul h

/-- `Im⟨y,(H - z)⁻¹y⟩ = Im z ‖(H - z)⁻¹y‖²` (any finite index type). -/
theorem im_dotProduct_inv_mulVec' {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (y : ι → ℂ) :
    (star y ⬝ᵥ ((H - z • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ y)).im =
      z.im * (star ((H - z • 1)⁻¹ *ᵥ y) ⬝ᵥ ((H - z • 1)⁻¹ *ᵥ y)).re := by
  set A := H - z • (1 : Matrix ι ι ℂ)
  have hAu : IsUnit A.det := isUnit_det_sub_smul_one' hH hz
  set w := A⁻¹ *ᵥ y
  have hAw : A *ᵥ w = y := by
    show A *ᵥ (A⁻¹ *ᵥ y) = y
    rw [mulVec_mulVec, mul_nonsing_inv _ hAu, one_mulVec]
  have hAH : Aᴴ = H - (star z) • 1 := by
    simp only [A, conjTranspose_sub, hH.eq, conjTranspose_smul, conjTranspose_one]
  have h1 : star y ⬝ᵥ w = star w ⬝ᵥ (Aᴴ *ᵥ w) := by
    rw [← hAw, star_mulVec, ← dotProduct_mulVec]
  have hr : (star w ⬝ᵥ (H *ᵥ w)).im = 0 :=
    BlockBand.Wegner.im_star_dotProduct_mulVec_hermitian hH w
  have hr1 : (star w ⬝ᵥ w).im = 0 := by
    have := BlockBand.Wegner.im_star_dotProduct_mulVec_hermitian
      (isHermitian_one (n := ι) (α := ℂ)) w
    rwa [one_mulVec] at this
  rw [h1, hAH, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul,
    smul_eq_mul, Complex.sub_im, hr, Complex.mul_im, hr1]
  simp

/-- `Im⟨y,(H - z)⁻¹y⟩ ≥ 0`. -/
theorem im_dotProduct_inv_mulVec_nonneg' {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (y : ι → ℂ) :
    0 ≤ (star y ⬝ᵥ ((H - z • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ y)).im := by
  rw [im_dotProduct_inv_mulVec' hH hz]
  refine mul_nonneg hz.le ?_
  rw [BlockBand.Wegner.re_star_dotProduct_self]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The diagonal resolvent entry has strictly positive imaginary part. -/
theorem im_inv_apply_self_pos' {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (k : ι) : 0 < ((H - z • (1 : Matrix ι ι ℂ))⁻¹ k k).im := by
  set A := H - z • (1 : Matrix ι ι ℂ)
  have he : star (Pi.single k (1 : ℂ)) ⬝ᵥ (A⁻¹ *ᵥ Pi.single k 1) = A⁻¹ k k := by
    simp [mulVec_single, dotProduct, Pi.single_apply]
  have h := im_dotProduct_inv_mulVec' hH hz (Pi.single k (1 : ℂ))
  rw [he] at h
  rw [h]
  refine mul_pos hz ?_
  rw [BlockBand.Wegner.re_star_dotProduct_self]
  have hAu : IsUnit A.det := isUnit_det_sub_smul_one' hH hz
  set w := A⁻¹ *ᵥ Pi.single k (1 : ℂ)
  have hAw : A *ᵥ w = Pi.single k 1 := by
    show A *ᵥ (A⁻¹ *ᵥ Pi.single k (1 : ℂ)) = _
    rw [mulVec_mulVec, mul_nonsing_inv _ hAu, one_mulVec]
  have hw : w ≠ 0 := by
    intro h0
    rw [h0, mulVec_zero] at hAw
    have := congrFun hAw k
    simp at this
  obtain ⟨b, hb⟩ : ∃ b, w b ≠ 0 := Function.ne_iff.1 hw
  exact lt_of_lt_of_le (by positivity : (0 : ℝ) < ‖w b‖ ^ 2)
    (Finset.single_le_sum (f := fun a => ‖w a‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ b))

/-- **One entry of a rank-one perturbation** (Sherman–Morrison, any finite index type):
`((H + g E_kk - z)⁻¹)_kk = a/(1 + g a)`, `a = ((H - z)⁻¹)_kk`. -/
theorem inv_add_single_apply' {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (k : ι) (g : ℝ) :
    (H + (g : ℂ) • single k k (1 : ℂ) - z • (1 : Matrix ι ι ℂ))⁻¹ k k =
      (H - z • 1)⁻¹ k k / (1 + g * (H - z • 1)⁻¹ k k) := by
  set A := H - z • (1 : Matrix ι ι ℂ)
  have hE : (single k k (1 : ℂ)).IsHermitian := by
    rw [IsHermitian, conjTranspose_single, star_one]
  have hH' : (H + (g : ℂ) • single k k (1 : ℂ)).IsHermitian :=
    hH.add (hE.smul (Complex.conj_ofReal g))
  set B := H + (g : ℂ) • single k k (1 : ℂ) - z • (1 : Matrix ι ι ℂ)
  have hA := isUnit_det_sub_smul_one' hH hz
  have hB := isUnit_det_sub_smul_one' hH' hz
  have hBA : B = A + (g : ℂ) • single k k 1 := by simp only [A, B]; abel
  have hres : A⁻¹ - B⁻¹ = (g : ℂ) • (A⁻¹ * single k k 1 * B⁻¹) := by
    have : (g : ℂ) • (A⁻¹ * single k k 1 * B⁻¹) = A⁻¹ * (B - A) * B⁻¹ := by
      rw [hBA, add_sub_cancel_left, Matrix.mul_smul, Matrix.smul_mul]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, mul_nonsing_inv _ hB,
      Matrix.mul_one, nonsing_inv_mul _ hA, Matrix.one_mul]
  have hkk := congrFun (congrFun hres k) k
  have hprod : (A⁻¹ * single k k (1 : ℂ) * B⁻¹) k k = A⁻¹ k k * B⁻¹ k k := by
    simp [Matrix.mul_apply, single_apply, ite_and]
  rw [Matrix.sub_apply, Matrix.smul_apply, hprod, smul_eq_mul] at hkk
  have hne : 1 + (g : ℂ) * A⁻¹ k k ≠ 0 := by
    by_cases hg : g = 0
    · simp [hg]
    · intro h0
      have := congrArg Complex.im h0
      simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, zero_add, add_zero, Complex.zero_im] at this
      exact (mul_ne_zero hg (im_inv_apply_self_pos' hH hz k).ne') this
  rw [eq_div_iff hne]
  linear_combination -hkk

/-- Resolvent entries `G ↦ ((F + G - z)⁻¹)_ab` are Borel measurable (any finite index type). -/
theorem measurable_resolvent_entry' (F : Matrix ι ι ℂ) (z : ℂ) (a b : ι) :
    Measurable fun G : Matrix ι ι ℂ => (F + G - z • (1 : Matrix ι ι ℂ))⁻¹ a b := by
  have h1 : Measurable fun G : Matrix ι ι ℂ => F + G - z • (1 : Matrix ι ι ℂ) :=
    ((continuous_const.add continuous_id).sub continuous_const).measurable
  have h2 := (BlockBand.Wegner.measurable_matrix_inv (n := ι)).comp h1
  exact (measurable_pi_apply b).comp ((measurable_pi_apply a).comp h2)

/-- Conjugating a resolvent quadratic form by a unitary (any finite index type). -/
theorem dotProduct_inv_unitary_conj' {V : Matrix ι ι ℂ}
    (hV : V ∈ unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) (y : ι → ℂ) :
    star y ⬝ᵥ (A⁻¹ *ᵥ y) = star (V *ᵥ y) ⬝ᵥ ((V * A * star V)⁻¹ *ᵥ (V *ᵥ y)) := by
  have h1 : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.1 hV
  have h2 : V * star V = 1 := Matrix.mem_unitaryGroup_iff.1 hV
  have hinv : (V * A * star V)⁻¹ = V * A⁻¹ * star V := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv h2,
      Matrix.inv_eq_left_inv h1, Matrix.mul_assoc]
  rw [hinv, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec,
    ← star_eq_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one,
    ← Matrix.mul_assoc, h1, Matrix.one_mul]

/-- **Positivity step of the `k`-block bound**:
`Im⟨Σ_{j∈s} v_j, R Σ v_j⟩ ≤ |s| Σ_{j∈s} Im⟨v_j, R v_j⟩`, `R = (H - z)⁻¹`, `H` Hermitian,
`Im z > 0` (`D = Im R ⪰ 0`; Cauchy–Schwarz on `‖R·‖²`). -/
theorem im_quad_sum_le {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im)
    {κ : Type*} (s : Finset κ) (v : κ → ι → ℂ) :
    (star (∑ j ∈ s, v j) ⬝ᵥ ((H - z • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ ∑ j ∈ s, v j)).im ≤
      (s.card : ℝ) * ∑ j ∈ s, (star (v j) ⬝ᵥ ((H - z • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ v j)).im := by
  simp_rw [im_dotProduct_inv_mulVec' hH hz, BlockBand.Wegner.re_star_dotProduct_self]
  set R := (H - z • (1 : Matrix ι ι ℂ))⁻¹
  rw [← Finset.mul_sum, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ hz.le
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mulVec_sum, Finset.sum_apply]
  have h1 : ‖∑ j ∈ s, (R *ᵥ v j) i‖ ≤ ∑ j ∈ s, ‖(R *ᵥ v j) i‖ := norm_sum_le _ _
  have h2 : (∑ j ∈ s, ‖(R *ᵥ v j) i‖) ^ 2 ≤ (s.card : ℝ) * ∑ j ∈ s, ‖(R *ᵥ v j) i‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := s) (f := fun j => ‖(R *ᵥ v j) i‖)
  calc ‖∑ j ∈ s, (R *ᵥ v j) i‖ ^ 2 ≤ (∑ j ∈ s, ‖(R *ᵥ v j) i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

end General

/-!
## The embedded block
-/

section Embedded

variable {m : Type} [Fintype m] [DecidableEq m]

/-- The block `G` embedded as `fromBlocks G 0 0 0` on `n ⊕ m`. -/
abbrev embedBlock {n : Type} (G : Matrix n n ℂ) (m : Type) : Matrix (n ⊕ m) (n ⊕ m) ℂ :=
  fromBlocks G 0 0 0

/-- The vector `y` embedded as `(y, 0)` on `n ⊕ m`. -/
abbrev embedVec {n : Type} (y : n → ℂ) (m : Type) : n ⊕ m → ℂ := Sum.elim y 0

omit [Fintype m] [DecidableEq m] in
theorem embedBlock_add {n : Type} (G G' : Matrix n n ℂ) :
    embedBlock (G + G') m = embedBlock G m + embedBlock G' m := by
  simp [embedBlock, fromBlocks_add]

omit [Fintype m] in
theorem embedBlock_smul_single {n : Type} [DecidableEq n] (g : ℂ) (k : n) :
    embedBlock (g • single k k (1 : ℂ)) m = g • single (Sum.inl k) (Sum.inl k) (1 : ℂ) := by
  ext (i | i) (j | j) <;> simp [embedBlock, single_apply]

omit [Fintype m] [DecidableEq m] in
theorem embedBlock_isHermitian {n : Type} {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    (embedBlock G m).IsHermitian := by
  simp [embedBlock, IsHermitian, fromBlocks_conjTranspose, hG.eq]

/-- Diagonal resolvent entry in the embedded block, `n = Fin N`:
`E Im((H + G ⊕ 0 - z)⁻¹)_{kk} ≤ √(π/(2t))`. -/
theorem lintegral_im_resolvent_embed_apply_self_le {N : ℕ}
    {H : Matrix (Fin N ⊕ m) (Fin N ⊕ m) ℂ} (hH : H.IsHermitian)
    {t : ℝ≥0} (ht : 0 < t) {z : ℂ} (hz : 0 < z.im) (k : Fin N) :
    ∫⁻ G, ENNReal.ofReal
        (((H + embedBlock G m - z • (1 : Matrix (Fin N ⊕ m) (Fin N ⊕ m) ℂ))⁻¹
          (Sum.inl k) (Sum.inl k)).im) ∂gueMeasure (Fin N) t ≤
      ENNReal.ofReal (Real.sqrt (Real.pi / (2 * t))) := by
  set C := ENNReal.ofReal (Real.sqrt (Real.pi / (2 * t)))
  have hemb : Measurable fun G : Matrix (Fin N) (Fin N) ℂ => embedBlock G m :=
    Measurable.of_eval_matrix _ fun i j => by
      rcases i with i | i <;> rcases j with j | j <;>
        simp only [embedBlock, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
          fromBlocks_apply₂₂] <;> first | exact measurable_const | exact Matrix.measurable_apply
  set f : (HermitianCoordinate N → ℝ) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (((H + embedBlock (hermitianMatrixOfCoordinates q) m -
      z • (1 : Matrix (Fin N ⊕ m) (Fin N ⊕ m) ℂ))⁻¹ (Sum.inl k) (Sum.inl k)).im)
  have hent := measurable_resolvent_entry' H z (Sum.inl k) (Sum.inl k)
  have hf : Measurable f :=
    (Complex.measurable_im.comp ((hent.comp hemb).comp
      (measurable_hermitianMatrixOfCoordinates N))).ennreal_ofReal
  have hg : Measurable fun G : Matrix (Fin N) (Fin N) ℂ =>
      ENNReal.ofReal (((H + embedBlock G m - z • (1 : Matrix (Fin N ⊕ m) (Fin N ⊕ m) ℂ))⁻¹
        (Sum.inl k) (Sum.inl k)).im) :=
    (Complex.measurable_im.comp (hent.comp hemb)).ennreal_ofReal
  rw [gueMeasure_eq_map_hermitianMatrixOfCoordinates,
    lintegral_map hg (measurable_hermitianMatrixOfCoordinates N)]
  change ∫⁻ q, f q ∂hermCoordGaussian N t ≤ C
  unfold hermCoordGaussian
  classical
  rw [lintegral_eq_lmarginal_univ (0 : HermitianCoordinate N → ℝ),
    ← Finset.insert_erase (Finset.mem_univ (Sum.inl k : HermitianCoordinate N)),
    lmarginal_insert' f hf (Finset.notMem_erase _ _)]
  have hin : ∀ x : HermitianCoordinate N → ℝ,
      ∫⁻ g, f (Function.update x (.inl k) g) ∂gaussianReal 0 (hermCoordVariance t (.inl k)) ≤ C := by
    intro x
    set H' := H + embedBlock (hermitianMatrixOfCoordinates (Function.update x (.inl k) 0)) m
    have hH' : H'.IsHermitian :=
      hH.add (embedBlock_isHermitian
        (CoareaNative.BlockBand.hermitianMatrixOfCoordinates_isHermitian _))
    have hpt : ∀ g : ℝ, f (Function.update x (.inl k) g) =
        ENNReal.ofReal (((H' - z • (1 : Matrix (Fin N ⊕ m) (Fin N ⊕ m) ℂ))⁻¹
            (Sum.inl k) (Sum.inl k) /
          (1 + (g : ℂ) * (H' - z • 1)⁻¹ (Sum.inl k) (Sum.inl k))).im) := by
      intro g
      simp only [f]
      rw [hermitianMatrixOfCoordinates_update_inl, embedBlock_add, embedBlock_smul_single,
        ← add_assoc, inv_add_single_apply' hH' hz (Sum.inl k) g]
    simp_rw [hpt]
    exact lintegral_gaussian_im_le _ (im_inv_apply_self_pos' hH' hz _) ht.ne'
  calc (∫⋯∫⁻_(Finset.univ.erase (Sum.inl k)), (fun x =>
          ∫⁻ g, f (Function.update x (.inl k) g) ∂gaussianReal 0 (hermCoordVariance t (.inl k)))
          ∂fun k => gaussianReal 0 (hermCoordVariance t k)) 0
      ≤ (∫⋯∫⁻_(Finset.univ.erase (Sum.inl k)), (fun _ => C)
          ∂fun k => gaussianReal 0 (hermCoordVariance t k)) 0 := lmarginal_mono hin 0
    _ = C := by
        simp [lmarginal, lintegral_const]

/-- The block unitary `diag(V, I)`. -/
abbrev blockUnitary {n : Type} [Fintype n] [DecidableEq n] (V : Matrix n n ℂ) (m : Type)
    [DecidableEq m] : Matrix (n ⊕ m) (n ⊕ m) ℂ :=
  fromBlocks V 0 0 1

theorem blockUnitary_mem {n : Type} [Fintype n] [DecidableEq n] {V : Matrix n n ℂ}
    (hV : V ∈ unitaryGroup n ℂ) : blockUnitary V m ∈ unitaryGroup (n ⊕ m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h := Matrix.mem_unitaryGroup_iff.1 hV
  rw [blockUnitary, star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply,
    ← star_eq_conjTranspose, h, ← fromBlocks_one]
  simp

theorem blockUnitary_conj_embedBlock {n : Type} [Fintype n] [DecidableEq n] (V : Matrix n n ℂ)
    (G : Matrix n n ℂ) :
    blockUnitary V m * embedBlock G m * star (blockUnitary V m) =
      embedBlock (V * G * star V) m := by
  simp [blockUnitary, embedBlock, star_eq_conjTranspose, fromBlocks_conjTranspose,
    fromBlocks_multiply]

theorem blockUnitary_mulVec_embedVec {n : Type} [Fintype n] [DecidableEq n] (V : Matrix n n ℂ)
    (y : n → ℂ) : blockUnitary V m *ᵥ embedVec y m = embedVec (V *ᵥ y) m := by
  funext i
  rcases i with i | i <;>
    simp [blockUnitary, embedVec, mulVec, dotProduct, Sum.elim]

/-- **Embedded-block rank-one spectral averaging**, `n = Fin N`. -/
theorem lintegral_im_resolvent_embed_le_fin {N : ℕ}
    {H : Matrix (Fin N ⊕ m) (Fin N ⊕ m) ℂ} (hH : H.IsHermitian)
    {t : ℝ≥0} (ht : 0 < t) {z : ℂ} (hz : 0 < z.im) (y : Fin N → ℂ) :
    ∫⁻ G, ENNReal.ofReal ((star (embedVec y m) ⬝ᵥ
        ((H + embedBlock G m - z • (1 : Matrix (Fin N ⊕ m) (Fin N ⊕ m) ℂ))⁻¹ *ᵥ
          embedVec y m)).im) ∂gueMeasure (Fin N) t ≤
      ENNReal.ofReal (Real.sqrt (Real.pi / (2 * t)) * ∑ a, ‖y a‖ ^ 2) := by
  by_cases hy : y = 0
  · subst hy
    have : embedVec (0 : Fin N → ℂ) m = 0 := by funext i; rcases i with i | i <;> rfl
    simp [this]
  obtain ⟨b, -⟩ := Function.ne_iff.1 hy
  obtain ⟨V, hV, hVy⟩ := exists_unitary_mulVec_eq y b
  set r := Real.sqrt (∑ a, ‖y a‖ ^ 2)
  set U := blockUnitary V m
  have hU : U ∈ unitaryGroup (Fin N ⊕ m) ℂ := blockUnitary_mem hV
  set H' := U * H * star U
  have hH' : H'.IsHermitian := by
    simp only [H', star_eq_conjTranspose]
    exact isHermitian_mul_mul_conjTranspose U hH
  have h2 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have hconj : ∀ G : Matrix (Fin N) (Fin N) ℂ,
      U * (H + embedBlock G m - z • (1 : Matrix (Fin N ⊕ m) (Fin N ⊕ m) ℂ)) * star U =
        H' + embedBlock (V * G * star V) m - z • 1 := by
    intro G
    rw [Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, h2, blockUnitary_conj_embedBlock]
  have hUy : U *ᵥ embedVec y m = Pi.single (Sum.inl b) (r : ℂ) := by
    rw [blockUnitary_mulVec_embedVec, hVy]
    funext i
    rcases i with i | i <;> simp [embedVec, Pi.single_apply]
  have hpt : ∀ G : Matrix (Fin N) (Fin N) ℂ,
      (star (embedVec y m) ⬝ᵥ ((H + embedBlock G m -
          z • (1 : Matrix (Fin N ⊕ m) (Fin N ⊕ m) ℂ))⁻¹ *ᵥ embedVec y m)).im =
        r ^ 2 * ((H' + embedBlock (V * G * star V) m -
          z • (1 : Matrix (Fin N ⊕ m) (Fin N ⊕ m) ℂ))⁻¹ (Sum.inl b) (Sum.inl b)).im := by
    intro G
    rw [dotProduct_inv_unitary_conj' hU, hconj, hUy]
    have : ∀ M : Matrix (Fin N ⊕ m) (Fin N ⊕ m) ℂ,
        star (Pi.single (Sum.inl b) (r : ℂ)) ⬝ᵥ (M *ᵥ Pi.single (Sum.inl b) (r : ℂ)) =
          ((r ^ 2 : ℝ) : ℂ) * M (Sum.inl b) (Sum.inl b) := by
      intro M
      simp [mulVec_single, dotProduct, Pi.single_apply, apply_ite (starRingEnd ℂ), ite_mul,
        Finset.sum_ite_eq']
      ring
    rw [this, Complex.im_ofReal_mul]
  simp_rw [hpt]
  have hemb : Measurable fun G : Matrix (Fin N) (Fin N) ℂ => embedBlock G m :=
    Measurable.of_eval_matrix _ fun i j => by
      rcases i with i | i <;> rcases j with j | j <;>
        simp only [embedBlock, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
          fromBlocks_apply₂₂] <;> first | exact measurable_const | exact Matrix.measurable_apply
  have hm : Measurable fun G : Matrix (Fin N) (Fin N) ℂ =>
      ENNReal.ofReal ((H' + embedBlock G m -
        z • (1 : Matrix (Fin N ⊕ m) (Fin N ⊕ m) ℂ))⁻¹ (Sum.inl b) (Sum.inl b)).im :=
    (Complex.measurable_im.comp
      ((measurable_resolvent_entry' H' z (Sum.inl b) (Sum.inl b)).comp hemb)).ennreal_ofReal
  have hψ : Measurable fun G : Matrix (Fin N) (Fin N) ℂ =>
      ENNReal.ofReal (r ^ 2 * ((H' + embedBlock G m -
        z • (1 : Matrix (Fin N ⊕ m) (Fin N ⊕ m) ℂ))⁻¹ (Sum.inl b) (Sum.inl b)).im) :=
    (measurable_const.mul (Complex.measurable_im.comp
      ((measurable_resolvent_entry' H' z (Sum.inl b) (Sum.inl b)).comp hemb))).ennreal_ofReal
  have hc : Measurable fun G : Matrix (Fin N) (Fin N) ℂ => V * G * star V :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  rw [← lintegral_map hψ hc, gueMeasure_map_unitary_conj t hV]
  simp_rw [ENNReal.ofReal_mul (sq_nonneg r)]
  rw [lintegral_const_mul _ hm, mul_comm (Real.sqrt _),
    ENNReal.ofReal_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have hr2 : r ^ 2 = ∑ a, ‖y a‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [hr2]
  exact mul_le_mul_right (lintegral_im_resolvent_embed_apply_self_le hH' ht hz b) _

/-- Quadratic forms of a resolvent are invariant under simultaneous relabelling. -/
theorem quad_inv_submatrix {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (σ : ι ≃ κ) (A : Matrix κ κ ℂ) (v : κ → ℂ) :
    star (v ∘ σ) ⬝ᵥ ((A.submatrix σ σ)⁻¹ *ᵥ (v ∘ σ)) = star v ⬝ᵥ (A⁻¹ *ᵥ v) := by
  rw [inv_submatrix_equiv, submatrix_mulVec_equiv]
  have : v ∘ σ ∘ σ.symm = v := by funext i; simp
  rw [Function.comp_assoc, this]
  change (star v ∘ σ) ⬝ᵥ ((A⁻¹ *ᵥ v) ∘ σ) = _
  rw [← dotProduct_comp_equiv_symm]
  congr 1
  funext i; simp

/-- **Embedded-block rank-one spectral averaging** (the conditional step of the `k`-block bound),
in its transported form. Law: one block `G ~ gueMeasure n t`, `t > 0`, any
finite block index `n`. For any finite ambient index `ι` with a labelling `σ : ι ≃ n ⊕ m` of the
block, every Hermitian `H` on `ι` (all other entries conditioned on; no norm bound), every `z` with
`Im z > 0` and every `y : n → ℂ`, with `ŷ = (y, 0) ∘ σ` and `ι_σ(G) = (G ⊕ 0) ∘ σ`:
`E_G Im⟨ŷ, (H + ι_σ(G) - z)⁻¹ ŷ⟩ ≤ √(π/(2t)) ‖y‖²`. No contract. -/
theorem lintegral_im_resolvent_embed_le {ι n : Type} [Fintype ι] [DecidableEq ι] [Fintype n]
    [DecidableEq n] (σ : ι ≃ n ⊕ m) {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {t : ℝ≥0} (ht : 0 < t) {z : ℂ} (hz : 0 < z.im) (y : n → ℂ) :
    ∫⁻ G, ENNReal.ofReal ((star (embedVec y m ∘ σ) ⬝ᵥ
        ((H + (embedBlock G m).submatrix σ σ - z • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ
          (embedVec y m ∘ σ))).im) ∂gueMeasure n t ≤
      ENNReal.ofReal (Real.sqrt (Real.pi / (2 * t)) * ∑ a, ‖y a‖ ^ 2) := by
  set e := Fintype.equivFin n
  set τ : n ⊕ m ≃ Fin (Fintype.card n) ⊕ m := Equiv.sumCongr e (Equiv.refl m)
  set σ' : ι ≃ Fin (Fintype.card n) ⊕ m := σ.trans τ
  set H' : Matrix (Fin (Fintype.card n) ⊕ m) (Fin (Fintype.card n) ⊕ m) ℂ :=
    H.submatrix σ'.symm σ'.symm
  have hH' : H'.IsHermitian := hH.submatrix σ'.symm
  have hblk : ∀ G : Matrix n n ℂ, (embedBlock G m).submatrix σ σ =
      (embedBlock (Matrix.reindex e e G) m).submatrix σ' σ' := by
    intro G
    ext i j
    simp only [submatrix_apply, σ', Equiv.trans_apply]
    rcases σ i with a | a <;> rcases σ j with b | b <;> simp [τ, embedBlock]
  have hvec : embedVec y m ∘ σ = embedVec (y ∘ e.symm) m ∘ σ' := by
    funext i
    simp only [Function.comp_apply, σ', Equiv.trans_apply]
    rcases σ i with a | a <;> simp [τ, embedVec]
  have hpt : ∀ G : Matrix n n ℂ,
      (star (embedVec y m ∘ σ) ⬝ᵥ ((H + (embedBlock G m).submatrix σ σ -
          z • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ (embedVec y m ∘ σ))).im =
        (star (embedVec (y ∘ e.symm) m) ⬝ᵥ ((H' + embedBlock (Matrix.reindex e e G) m -
          z • (1 : Matrix (Fin (Fintype.card n) ⊕ m) (Fin (Fintype.card n) ⊕ m) ℂ))⁻¹ *ᵥ
            embedVec (y ∘ e.symm) m)).im := by
    intro G
    have hM : H + (embedBlock G m).submatrix σ σ - z • (1 : Matrix ι ι ℂ) =
        (H' + embedBlock (Matrix.reindex e e G) m - z • 1).submatrix σ' σ' := by
      rw [hblk]
      ext i j
      simp [H', Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
        σ'.injective.eq_iff]
    rw [hM, hvec, quad_inv_submatrix]
  simp_rw [hpt]
  have hemb : Measurable fun G : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ =>
      embedBlock G m :=
    Measurable.of_eval_matrix _ fun i j => by
      rcases i with i | i <;> rcases j with j | j <;>
        simp only [embedBlock, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
          fromBlocks_apply₂₂] <;> first | exact measurable_const | exact Matrix.measurable_apply
  have hψ : Measurable fun G : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ =>
      ENNReal.ofReal ((star (embedVec (y ∘ e.symm) m) ⬝ᵥ ((H' + embedBlock G m -
          z • (1 : Matrix (Fin (Fintype.card n) ⊕ m) (Fin (Fintype.card n) ⊕ m) ℂ))⁻¹ *ᵥ
            embedVec (y ∘ e.symm) m)).im) := by
    have hinv : Measurable fun G : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ =>
        (H' + embedBlock G m -
          z • (1 : Matrix (Fin (Fintype.card n) ⊕ m) (Fin (Fintype.card n) ⊕ m) ℂ))⁻¹ :=
      (BlockBand.Wegner.measurable_matrix_inv).comp
        (((continuous_const.add continuous_id).sub continuous_const).measurable.comp hemb)
    have hcont : Continuous fun A : Matrix (Fin (Fintype.card n) ⊕ m)
        (Fin (Fintype.card n) ⊕ m) ℂ =>
        (star (embedVec (y ∘ e.symm) m) ⬝ᵥ (A *ᵥ embedVec (y ∘ e.symm) m)).im :=
      Complex.continuous_im.comp (continuous_const.dotProduct
        (continuous_id.matrix_mulVec continuous_const))
    exact (hcont.measurable.comp hinv).ennreal_ofReal
  have hre : Measurable (Matrix.reindex e e : Matrix n n ℂ → _) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  rw [← lintegral_map hψ hre, gueMeasure_map_reindex e t]
  have hy : ∑ a, ‖(y ∘ e.symm) a‖ ^ 2 = ∑ a, ‖y a‖ ^ 2 :=
    e.symm.sum_comp (fun a => ‖y a‖ ^ 2)
  rw [← hy]
  exact lintegral_im_resolvent_embed_le_fin hH' ht hz (y ∘ e.symm)

end Embedded

end BlockBand.Critical.Collar.Density
