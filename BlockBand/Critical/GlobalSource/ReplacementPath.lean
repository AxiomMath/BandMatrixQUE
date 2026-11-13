module

public import BlockBand.Critical.GlobalSource.ReplacementMoments

/-!
# Global Gaussian source, source replacement: path averages of the block moments

* `weightVec_tagWeight_castSucc`: a tag weight applied to a full circular vector is the
  `tagVector` of its block (with `circularVectorLaw_map_row`, the block is a standard circular
  vector);
* `pairHS_sq_le_lintegral`: `pairHS² ≤ E|ξ^*Gξ'|⁴` for independent tags (exact Gaussian identities);
* `lintegral_pairHS_sq_le`, `lintegral_pairFour_le`: path averages, from the hypothesis
  `RawTagFour` (the first clause of `rawTagMoments` at `p = 4`);
* `measurable_swapRemainder`: joint measurability of the swap remainder.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)
open BlockBand.Internal.Contracts.CriticalEntire (tagGroup)
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ComplexConjugate NNReal ENNReal Matrix RealInnerProductSpace
open Complex (exp I)

section Tags
variable {W L : ℕ}

theorem tagWeight_castSucc (m : ℝ) (k : Fin L) (x : Fin L × Fin W) :
    tagWeight W L m k.castSucc x = if x.1 = k then Real.sqrt (m / W) else 0 := by
  unfold tagWeight
  simp only [Fin.val_castSucc, Fin.val_inj]

/-- A tag weight on block `k` applied to a full vector is the tag (`tagVector`) of its block `k`. -/
theorem weightVec_tagWeight_castSucc (m : ℝ) (k : Fin L) (h : Fin L × Fin W → ℂ) :
    weightVec (tagWeight W L m k.castSucc) h = tagVector W L k m (fun y => h (k, y)) := by
  funext x
  unfold weightVec tagVector
  rw [tagWeight_castSucc]
  by_cases hx : x.1 = k
  · simp only [hx, ↓reduceIte]
    rw [show (k, x.2) = x from Prod.ext hx.symm rfl]
  · simp [hx]

/-- Sum over the sites of one block. -/
theorem sum_ite_block {R : Type*} [AddCommMonoid R] (k : Fin L) (f : Fin L × Fin W → R) :
    (∑ x, if x.1 = k then f x else 0) = ∑ y, f (k, y) := by
  rw [Fintype.sum_prod_type]
  simp only
  rw [Finset.sum_eq_single k]
  · simp
  · intro k' _ hk; simp [hk]
  · simp

/-- The tag bilinear form as a bilinear form on `ℂ^W`. -/
def tagBlockMatrix (W L : ℕ) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (m₁ m₂ : ℝ)
    (k k' : Fin L) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun y y' => ((Real.sqrt (m₁ / W) * Real.sqrt (m₂ / W) : ℝ) : ℂ) * G (k, y) (k', y')

theorem tag_form_eq (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (m₁ m₂ : ℝ) (k k' : Fin L)
    (g g' : Fin W → ℂ) :
    star (tagVector W L k m₁ g) ⬝ᵥ (G *ᵥ tagVector W L k' m₂ g') =
      star ((tagBlockMatrix W L G m₁ m₂ k k')ᴴ *ᵥ g) ⬝ᵥ g' := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec]
  unfold dotProduct Matrix.mulVec dotProduct tagVector tagBlockMatrix
  simp only [Pi.star_apply, RCLike.star_def, apply_ite (starRingEnd ℂ), map_mul, map_zero,
    Complex.conj_ofReal, ite_mul, zero_mul, mul_ite, mul_zero, Matrix.of_apply]
  rw [sum_ite_block k]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [sum_ite_block k', Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  push_cast; ring

theorem hs_tagBlockMatrix (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {m₁ m₂ : ℝ}
    (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) (k k' : Fin L) :
    ∑ y, ∑ y', ‖(tagBlockMatrix W L G m₁ m₂ k k')ᴴ y y'‖ ^ 2 =
      ∑ x, ∑ z, tagWeight W L m₁ k.castSucc x ^ 2 * ‖G x z‖ ^ 2 *
        tagWeight W L m₂ k'.castSucc z ^ 2 := by
  simp_rw [tagWeight_castSucc, ite_pow, zero_pow two_ne_zero, ite_mul, zero_mul, mul_ite, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [sum_ite_block k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [sum_ite_block k']
  refine Finset.sum_congr rfl fun y' _ => ?_
  unfold tagBlockMatrix
  rw [Matrix.conjTranspose_apply, norm_star, Matrix.of_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs, mul_pow, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)]
  ring

/-- **Block-pair Hilbert–Schmidt square below the tag fourth moment**:
`pairHS² ≤ E|ξ^*Gξ'|⁴` for independent tags of masses `m₁`, `m₂` on blocks `k`, `k'`. -/
theorem pairHS_sq_le_lintegral (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {m₁ m₂ : ℝ}
    (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) (k k' : Fin L) :
    ENNReal.ofReal ((∑ x, ∑ z, tagWeight W L m₁ k.castSucc x ^ 2 * ‖G x z‖ ^ 2 *
        tagWeight W L m₂ k'.castSucc z ^ 2) ^ 2) ≤
      ∫⁻ q, ENNReal.ofReal (‖star (tagVector W L k m₁ q.1) ⬝ᵥ
        (G *ᵥ tagVector W L k' m₂ q.2)‖ ^ 4)
        ∂(circularVectorLaw (Fin W)).prod (circularVectorLaw (Fin W)) := by
  set B := (tagBlockMatrix W L G m₁ m₂ k k')ᴴ
  simp_rw [tag_form_eq]
  have hm : Measurable fun q : (Fin W → ℂ) × (Fin W → ℂ) =>
      ENNReal.ofReal (‖star (B *ᵥ q.1) ⬝ᵥ q.2‖ ^ 4) := by
    have : Continuous fun q : (Fin W → ℂ) × (Fin W → ℂ) => ‖star (B *ᵥ q.1) ⬝ᵥ q.2‖ ^ 4 := by
      unfold dotProduct Matrix.mulVec dotProduct; fun_prop
    exact ENNReal.measurable_ofReal.comp this.measurable
  rw [lintegral_prod _ hm.aemeasurable]
  simp_rw [lintegral_norm_pow_four_dotc]
  rw [← hs_tagBlockMatrix G h₁ h₂ k k']
  have h2 : ∀ g : Fin W → ℂ, ENNReal.ofReal (2 * (∑ i, ‖(B *ᵥ g) i‖ ^ 2) ^ 2) =
      ENNReal.ofReal 2 * ENNReal.ofReal ((∑ i, ‖(B *ᵥ g) i‖ ^ 2) ^ 2) := fun g =>
    ENNReal.ofReal_mul (by norm_num)
  simp_rw [h2]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal ((∑ y, ∑ y', ‖B y y'‖ ^ 2) ^ 2)
      ≤ ENNReal.ofReal 2 * ENNReal.ofReal ((∑ y, ∑ y', ‖B y y'‖ ^ 2) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (∑ y, ∑ y', ‖B y y'‖ ^ 2)])
    _ ≤ _ := mul_le_mul_right (le_lintegral_sq_sum_norm_sq_mulVec B) _

end Tags

section Path
variable {W L J : ℕ}

/-- `G = G_int`, the interior block of the inverse of the path with its two leads. -/
def leadG (b E : ℝ) (W L : ℕ) (ω : GrowthPath W) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  (fullInverse b E W L ω).toBlocks₁₁

theorem measurable_leadG (b E : ℝ) (W L : ℕ) : Measurable (leadG b E W L) := by
  have h := measurable_matrix_inv.comp (measurable_fullPathMatrix b E W L)
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  exact (measurable_pi_apply (Sum.inl y)).comp ((measurable_pi_apply (Sum.inl x)).comp h)

theorem tagVector_eq (k : Fin L) (m : ℝ) (g : Fin W → ℂ) :
    tagVector W L k m g = fun x => (tagWeight W L m k.castSucc x : ℂ) * g x.2 := by
  funext x
  unfold tagVector
  rw [tagWeight_castSucc]
  split_ifs <;> simp

theorem measurable_tag_form {Ω : Type*} [MeasurableSpace Ω]
    {G : Ω → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hG : Measurable G)
    (k k' : Fin L) (m₁ m₂ : ℝ) (p : ℕ) :
    Measurable fun x : Ω × ((Fin W → ℂ) × (Fin W → ℂ)) =>
      ENNReal.ofReal (‖star (tagVector W L k m₁ x.2.1) ⬝ᵥ
        (G x.1 *ᵥ tagVector W L k' m₂ x.2.2)‖ ^ p) := by
  simp_rw [tagVector_eq]
  have hG' : ∀ y z, Measurable fun x : Ω × ((Fin W → ℂ) × (Fin W → ℂ)) => G x.1 y z :=
    fun y z => (measurable_pi_apply z).comp ((measurable_pi_apply y).comp (hG.comp measurable_fst))
  refine ENNReal.measurable_ofReal.comp ((Measurable.norm ?_).pow_const p)
  unfold dotProduct Matrix.mulVec dotProduct
  refine Finset.measurable_sum _ fun y _ => Measurable.mul ?_ (Finset.measurable_sum _ fun z _ =>
    (hG' y z).mul ?_)
  · exact (continuous_star.measurable).comp (measurable_const.mul
      ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)))
  · exact measurable_const.mul ((measurable_pi_apply _).comp (measurable_snd.comp measurable_snd))

theorem pairHS_last_left (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (r₁ r₂ : Fin L → ℝ)
    (o' : Fin (L + 1)) : pairHS W L G r₁ r₂ (Fin.last L) o' = 0 := by
  unfold pairHS; simp [tagWeight_last]

theorem pairHS_last_right (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (r₁ r₂ : Fin L → ℝ)
    (o : Fin (L + 1)) : pairHS W L G r₁ r₂ o (Fin.last L) = 0 := by
  unfold pairHS; simp [tagWeight_last]

theorem pairHS_conjTranspose (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (r₁ r₂ : Fin L → ℝ)
    (o o' : Fin (L + 1)) : pairHS W L Gᴴ r₁ r₂ o o' = pairHS W L G r₂ r₁ o' o := by
  unfold pairHS
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.conjTranspose_apply, norm_star]
  ring

theorem profileMass_nonneg {r : Fin L → ℝ} (hr : ∀ k, 0 ≤ r k) : 0 ≤ profileMass W L r := by
  unfold profileMass; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => hr k)

/-- The raw tag hypothesis in the form provided by `ComplexSourceLawContract.rawTagMoments`
(`p = 4`, first clause), at a fixed width, energy and length. -/
def RawTagFour (b E : ℝ) (W L : ℕ) (C : ℝ) : Prop :=
  ∀ (k k' : Fin L) (m₁ m₂ : ℝ), 0 ≤ m₁ → 0 ≤ m₂ →
    ∫⁻ x, ENNReal.ofReal (‖star (tagVector W L k m₁ x.2.1) ⬝ᵥ
        ((fullInverse b E W L x.1).toBlocks₁₁ *ᵥ tagVector W L k' m₂ x.2.2)‖ ^ (4 : ℝ))
      ∂(growthPathLaw W b).prod ((circularVectorLaw (Fin W)).prod (circularVectorLaw (Fin W))) ≤
      ENNReal.ofReal (C * (m₁ * m₂) ^ ((4 : ℝ) / 2))

/-- **Path average of the block-pair Hilbert–Schmidt square** (from the raw tag moments `RawTagFour`). -/
theorem lintegral_pairHS_sq_le {b E : ℝ} {C : ℝ} (hraw : RawTagFour b E W L C)
    {r₁ r₂ : Fin L → ℝ} (hr₁ : ∀ k, 0 ≤ r₁ k) (hr₂ : ∀ k, 0 ≤ r₂ k) (o o' : Fin (L + 1)) :
    ∫⁻ ω, ENNReal.ofReal (pairHS W L (leadG b E W L ω) r₁ r₂ o o' ^ 2) ∂growthPathLaw W b ≤
      ENNReal.ofReal (max C 0 * (profileMass W L r₁ * profileMass W L r₂) ^ 2) := by
  induction o using Fin.lastCases with
  | last => simp [pairHS_last_left]
  | cast k =>
    induction o' using Fin.lastCases with
    | last => simp [pairHS_last_right]
    | cast k' =>
      have h₁ := profileMass_nonneg (W := W) hr₁
      have h₂ := profileMass_nonneg (W := W) hr₂
      have hpt : ∀ ω, ENNReal.ofReal (pairHS W L (leadG b E W L ω) r₁ r₂ k.castSucc k'.castSucc ^ 2) ≤
          ∫⁻ q, ENNReal.ofReal (‖star (tagVector W L k (profileMass W L r₁) q.1) ⬝ᵥ
            (leadG b E W L ω *ᵥ tagVector W L k' (profileMass W L r₂) q.2)‖ ^ 4)
            ∂(circularVectorLaw (Fin W)).prod (circularVectorLaw (Fin W)) :=
        fun ω => pairHS_sq_le_lintegral (leadG b E W L ω) h₁ h₂ k k'
      refine (lintegral_mono hpt).trans ?_
      rw [← lintegral_prod _ (measurable_tag_form (measurable_leadG b E W L) k k' _ _ 4).aemeasurable]
      have h4 := hraw k k' _ _ h₁ h₂
      simp_rw [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h4
      rw [show ((4 : ℕ) : ℝ) / 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h4
      refine h4.trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

theorem measurable_pairHS (r₁ r₂ : Fin L → ℝ) (o o' : Fin (L + 1)) :
    Continuous fun G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ => pairHS W L G r₁ r₂ o o' := by
  unfold pairHS; fun_prop

/-- **Path average of the pair fourth moment.** -/
theorem lintegral_pairFour_le {b E : ℝ} {C : ℝ} (hraw : RawTagFour b E W L C)
    {r : Fin J → Fin L → ℝ} (hr : ∀ a k, 0 ≤ r a k) {μ : ℝ} (hμ : ∀ a, profileMass W L (r a) ≤ μ)
    (b' a : Fin J) (adj : Bool) :
    ∫⁻ ω, ENNReal.ofReal (4 * pairFour W L r
        (if adj then (leadG b E W L ω)ᴴ else leadG b E W L ω) b' a) ∂growthPathLaw W b ≤
      ENNReal.ofReal (4 * (max C 0 * μ ^ 4)) := by
  have hm0 : ∀ a, 0 ≤ profileMass W L (r a) := fun a => profileMass_nonneg (hr a)
  have hμ0 : 0 ≤ μ := (hm0 a).trans (hμ a)
  have hprob : ∀ a, IsProbabilityMeasure (discreteBlockLaw W L (r a)) := fun a =>
    isProbabilityMeasure_discreteBlockLaw (hr a)
  have hpt : ∀ ω, ENNReal.ofReal (4 * pairFour W L r
      (if adj then (leadG b E W L ω)ᴴ else leadG b E W L ω) b' a) =
      ENNReal.ofReal 4 * ∑ o, ∑ o', ENNReal.ofReal ((discreteBlockLaw W L (r b')).real {o} *
        (discreteBlockLaw W L (r a)).real {o'}) *
        ENNReal.ofReal ((if adj then pairHS W L (leadG b E W L ω) (r a) (r b') o' o
          else pairHS W L (leadG b E W L ω) (r b') (r a) o o') ^ 2) := by
    intro ω
    rw [ENNReal.ofReal_mul (by norm_num)]
    congr 1
    unfold pairFour
    rw [ENNReal.ofReal_sum_of_nonneg fun o _ => Finset.sum_nonneg fun o' _ =>
      mul_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg) (sq_nonneg _)]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun o' _ =>
      mul_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg) (sq_nonneg _)]
    refine Finset.sum_congr rfl fun o' _ => ?_
    rw [ENNReal.ofReal_mul (mul_nonneg measureReal_nonneg measureReal_nonneg)]
    cases adj
    · rfl
    · simp only [↓reduceIte, pairHS_conjTranspose]
  simp_rw [hpt]
  have hmeas : ∀ o o', Measurable fun ω => ENNReal.ofReal ((if adj then
      pairHS W L (leadG b E W L ω) (r a) (r b') o' o
        else pairHS W L (leadG b E W L ω) (r b') (r a) o o') ^ 2) := by
    intro o o'
    cases adj
    · exact ENNReal.measurable_ofReal.comp
        (((measurable_pairHS _ _ _ _).measurable.comp (measurable_leadG b E W L)).pow_const 2)
    · exact ENNReal.measurable_ofReal.comp
        (((measurable_pairHS _ _ _ _).measurable.comp (measurable_leadG b E W L)).pow_const 2)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finsetSum _ fun o _ => Finset.measurable_sum _ fun o' _ =>
      (hmeas o o').const_mul _]
  simp_rw [lintegral_finsetSum _ fun o' _ => (hmeas _ o').const_mul _]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hb : ∀ o o', ∫⁻ ω, ENNReal.ofReal ((if adj then
      pairHS W L (leadG b E W L ω) (r a) (r b') o' o
        else pairHS W L (leadG b E W L ω) (r b') (r a) o o') ^ 2) ∂growthPathLaw W b ≤
      ENNReal.ofReal (max C 0 * μ ^ 4) := by
    intro o o'
    have hmm : (profileMass W L (r a) * profileMass W L (r b')) ^ 2 ≤ μ ^ 4 := by
      have := mul_le_mul (hμ a) (hμ b') (hm0 b') hμ0
      calc (profileMass W L (r a) * profileMass W L (r b')) ^ 2 ≤ (μ * μ) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg (hm0 a) (hm0 b')) this 2
        _ = μ ^ 4 := by ring
    cases adj
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine (lintegral_pairHS_sq_le hraw (hr b') (hr a) o o').trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact hmm) (le_max_right _ _)
    · simp only [↓reduceIte]
      refine (lintegral_pairHS_sq_le hraw (hr a) (hr b') o' o).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_left hmm (le_max_right _ _)
  calc ENNReal.ofReal 4 * ∑ o, ∑ o', ENNReal.ofReal ((discreteBlockLaw W L (r b')).real {o} *
        (discreteBlockLaw W L (r a)).real {o'}) * ∫⁻ ω, ENNReal.ofReal ((if adj then
          pairHS W L (leadG b E W L ω) (r a) (r b') o' o
            else pairHS W L (leadG b E W L ω) (r b') (r a) o o') ^ 2) ∂growthPathLaw W b
      ≤ ENNReal.ofReal 4 * ∑ o, ∑ o', ENNReal.ofReal ((discreteBlockLaw W L (r b')).real {o} *
        (discreteBlockLaw W L (r a)).real {o'}) * ENNReal.ofReal (max C 0 * μ ^ 4) := by
        gcongr with o _ o' _
        exact hb o o'
    _ = ENNReal.ofReal (4 * (max C 0 * μ ^ 4)) := by
        have hsum : ∑ o, ∑ o', ENNReal.ofReal ((discreteBlockLaw W L (r b')).real {o} *
            (discreteBlockLaw W L (r a)).real {o'}) = 1 := by
          rw [← ENNReal.ofReal_one, ← sum_discreteBlockLaw_real (W := W) (hr b'),
            ENNReal.ofReal_sum_of_nonneg fun o _ => measureReal_nonneg]
          refine Finset.sum_congr rfl fun o _ => ?_
          rw [← ENNReal.ofReal_sum_of_nonneg fun o' _ =>
            mul_nonneg measureReal_nonneg measureReal_nonneg, ← Finset.mul_sum,
            sum_discreteBlockLaw_real (hr a), mul_one]
        simp_rw [← Finset.sum_mul]
        rw [hsum, one_mul, ← ENNReal.ofReal_mul (by norm_num)]

end Path

section Measurability
variable {W L J M : ℕ}

/-- The swap remainder as a function of `(G, η, X)`. -/
def swapRemainderFun (W L M : ℕ) {J : ℕ} (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) (a : Fin J)
    (q : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ × (Fin J → Fin L × Fin W → ℂ) ×
      (Fin L × Fin W → ℂ)) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt M)⁻¹ ^ 3 *
    (4 * |(star (linVec (coefU u) q.1 q.2.1 a) ⬝ᵥ q.2.2).re| ^ 3 +
      |(star (linVec (coefU u) q.1 q.2.1 a) ⬝ᵥ q.2.2).re| *
        |(coefU u a a * (star q.2.2 ⬝ᵥ (q.1 *ᵥ q.2.2))).re| +
      5 * (coefU u a a * (star q.2.2 ⬝ᵥ (q.1 *ᵥ q.2.2))).re ^ 2))

theorem continuous_linVec (coef : Fin J → Fin J → ℂ) (a : Fin J) :
    Continuous fun q : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ × (Fin J → Fin L × Fin W → ℂ) =>
      linVec coef q.1 q.2 a := by
  unfold linVec
  refine (continuous_finsetSum _ fun b _ => ?_).add (continuous_finsetSum _ fun c _ => ?_)
  · have hb : Continuous fun q : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ ×
        (Fin J → Fin L × Fin W → ℂ) => q.2 b := by fun_prop
    exact (continuous_fst.matrix_conjTranspose.matrix_mulVec hb).const_smul (star (coef b a))
  · have hc : Continuous fun q : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ ×
        (Fin J → Fin L × Fin W → ℂ) => q.2 c := by fun_prop
    exact (continuous_fst.matrix_mulVec hc).const_smul (coef a c)

theorem measurable_swapRemainderFun (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) (a : Fin J) :
    Measurable (swapRemainderFun W L M u a) := by
  have hα : Continuous fun q : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ ×
      (Fin J → Fin L × Fin W → ℂ) × (Fin L × Fin W → ℂ) =>
      (star (linVec (coefU u) q.1 q.2.1 a) ⬝ᵥ q.2.2).re :=
    Complex.continuous_re.comp (((continuous_linVec (coefU u) a).comp
      (continuous_fst.prodMk continuous_snd.fst)).star.dotProduct continuous_snd.snd)
  have hβ : Continuous fun q : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ ×
      (Fin J → Fin L × Fin W → ℂ) × (Fin L × Fin W → ℂ) =>
      (coefU u a a * (star q.2.2 ⬝ᵥ (q.1 *ᵥ q.2.2))).re :=
    Complex.continuous_re.comp (continuous_const.mul (continuous_snd.snd.star.dotProduct
      (continuous_fst.matrix_mulVec continuous_snd.snd)))
  unfold swapRemainderFun
  exact ENNReal.measurable_ofReal.comp (continuous_const.mul
    (((continuous_const.mul (hα.abs.pow 3)).add (hα.abs.mul hβ.abs)).add
      (continuous_const.mul (hβ.pow 2)))).measurable

theorem swapRemainder_eq_fun (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (Λ₀ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ) (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2))
    (j : Fin (J * M)) (lam : Fin (L + 1) → Fin L × Fin W → ℝ) (x : Fin (J * M) → SlotSample W L)
    (y' : SlotSample W L) :
    swapRemainder G Λ₀ u j lam x y' = swapRemainderFun W L M u (tagGroup j)
      (G, slotSum (zeroAt j Λ₀) x, weightVec (lam y'.1) y'.2) := rfl

/-- Joint measurability of the swap remainder in the path, the other slots and the swapped slot. -/
theorem measurable_swapRemainder {Ω : Type*} [MeasurableSpace Ω]
    {G : Ω → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hG : Measurable G)
    (Λ₀ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ) (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2))
    (j : Fin (J * M)) (lam : Fin (L + 1) → Fin L × Fin W → ℝ) :
    Measurable fun z : (Ω × (Fin (J * M) → SlotSample W L)) × SlotSample W L =>
      swapRemainder (G z.1.1) Λ₀ u j lam z.1.2 z.2 := by
  simp_rw [swapRemainder_eq_fun]
  have h : Measurable fun z : (Ω × (Fin (J * M) → SlotSample W L)) × SlotSample W L =>
      (G z.1.1, slotSum (zeroAt j Λ₀) z.1.2, weightVec (lam z.2.1) z.2.2) :=
    (hG.comp (measurable_fst.comp measurable_fst)).prodMk
      (((measurable_slotSum _).comp (measurable_snd.comp measurable_fst)).prodMk
        ((measurable_weightVec_slot lam).comp measurable_snd))
  exact (measurable_swapRemainderFun u (tagGroup j)).comp h

end Measurability

end BlockBand.Critical.GlobalSource
