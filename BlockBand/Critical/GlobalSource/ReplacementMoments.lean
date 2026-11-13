module

public import BlockBand.Critical.GlobalSource.ReplacementSwap

/-!
# Global Gaussian source, source replacement: deterministic moment bounds for one swap

* `lintegral_dotc_slotSum_pow_four_le`: for admissible weights (`IsSlotWeight`: removed, tag, or
  Gaussian), `E|v^*η_b|⁴ ≤ 2 N_b(v)`, `N_b(v) = E_o (Σ_x tagW(o)_x²|v_x|²)²`, uniformly in `M`
  (Wick for the independent slot vectors, Cauchy–Schwarz over the `M` slots, Jensen over blocks);
* `lintegral_slot_blockFour_le`: averaging over the swapped slot,
  `E 2N_b(GX) ≤ 4 Σ_{o,o'} p_b(o)p_a(o') pairHS(o,o')²`, with `pairHS` the block-pair
  Hilbert–Schmidt mass (`= E|ξ^*Gξ'|²` for independent block tags);
* `swapRemainder_le`: the scalar remainder is at most
  `t³(1+2‖u‖)³(5 + 40J³ Σ_b(|η_b^*GX|⁴ + |η_b^*G^*X|⁴) + 6|X^*GX|²)`;
* `lintegral_swapRemainder_le`: the expected remainder of one swap is at most
  `t³(1+2‖u‖)³(5 + 40J³ Σ_b (4 pairFour(G) + 4 pairFour(G^*)) + 6 quadMoment)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)
open BlockBand.Internal.Contracts.CriticalEntire (tagGroup)
open scoped ComplexConjugate NNReal ENNReal Matrix RealInnerProductSpace
open Complex (exp I)

section Det
variable {W L J M : ℕ}

/-- Admissible slot weights: removed, a tag of the group mass, or a Gaussian of the group profile. -/
def IsSlotWeight (W L : ℕ) {J M : ℕ} (r : Fin J → Fin L → ℝ) (s : Fin (J * M))
    (lam : Fin (L + 1) → Fin L × Fin W → ℝ) : Prop :=
  lam = 0 ∨ lam = tagWeight W L (profileMass W L (r (tagGroup s))) ∨
    lam = fun _ => gaussWeight W L (r (tagGroup s))

theorem isSlotWeight_slotWeight (r : Fin J → Fin L → ℝ) (S : Finset (Fin (J * M)))
    (s : Fin (J * M)) : IsSlotWeight W L r s (slotWeight W L r S s) := by
  unfold slotWeight IsSlotWeight
  by_cases h : s ∈ S
  · right; left; funext o; simp [h]
  · right; right; funext o; simp [h]

theorem isSlotWeight_zeroAt {r : Fin J → Fin L → ℝ}
    {Λ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ} (hΛ : ∀ s, IsSlotWeight W L r s (Λ s))
    (j s : Fin (J * M)) : IsSlotWeight W L r s (zeroAt j Λ s) := by
  unfold zeroAt
  split_ifs
  · left; rfl
  · exact hΛ s

/-- `Σ_x tagWeight(o)_x² |v_x|²` (the squared norm of `diag(tagWeight o) v`). -/
def tagSq (W L : ℕ) (r : Fin L → ℝ) (o : Fin (L + 1)) (v : Fin L × Fin W → ℂ) : ℝ :=
  ∑ x, tagWeight W L (profileMass W L r) o x ^ 2 * ‖v x‖ ^ 2

/-- `N(v) = E_o (tagSq o v)²` over the block law. -/
def blockFour (W L : ℕ) (r : Fin L → ℝ) (v : Fin L × Fin W → ℂ) : ℝ :=
  ∑ o, (discreteBlockLaw W L r).real {o} * tagSq W L r o v ^ 2

theorem tagSq_nonneg (r : Fin L → ℝ) (o : Fin (L + 1)) (v : Fin L × Fin W → ℂ) :
    0 ≤ tagSq W L r o v := by unfold tagSq; positivity

theorem blockFour_nonneg (r : Fin L → ℝ) (v : Fin L × Fin W → ℂ) : 0 ≤ blockFour W L r v := by
  unfold blockFour
  exact Finset.sum_nonneg fun o _ => mul_nonneg measureReal_nonneg (sq_nonneg _)

/-- Jensen over the block law: `(E c)² ≤ E c²`. -/
theorem sq_sum_blockLaw_le {r : Fin L → ℝ} (hr : ∀ k, 0 ≤ r k) (c : Fin (L + 1) → ℝ) :
    (∑ o, (discreteBlockLaw W L r).real {o} * c o) ^ 2 ≤
      ∑ o, (discreteBlockLaw W L r).real {o} * c o ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun o => Real.sqrt ((discreteBlockLaw W L r).real {o}))
    (fun o => Real.sqrt ((discreteBlockLaw W L r).real {o}) * c o)
  have hp : ∀ o, Real.sqrt ((discreteBlockLaw W L r).real {o}) ^ 2 =
      (discreteBlockLaw W L r).real {o} := fun o => Real.sq_sqrt measureReal_nonneg
  simp only [← mul_assoc, ← sq, hp, mul_pow, sum_discreteBlockLaw_real hr, one_mul] at h
  exact h

/-- The Gaussian squared norm is the block mixture of the tag squared norms. -/
theorem gaussSq_eq {r : Fin L → ℝ} (hr : ∀ k, 0 ≤ r k) (v : Fin L × Fin W → ℂ) :
    ∑ x, gaussWeight W L r x ^ 2 * ‖v x‖ ^ 2 =
      ∑ o, (discreteBlockLaw W L r).real {o} * tagSq W L r o v := by
  unfold tagSq
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← sum_discreteBlockLaw_tagWeight_sq hr x, Finset.sum_mul]
  refine Finset.sum_congr rfl fun o _ => ?_
  ring

theorem lintegral_blockLaw_eq {r : Fin L → ℝ} (hr : ∀ k, 0 ≤ r k) (f : Fin (L + 1) → ℝ)
    (hf : ∀ o, 0 ≤ f o) :
    ∫⁻ o, ENNReal.ofReal (f o) ∂discreteBlockLaw W L r =
      ENNReal.ofReal (∑ o, (discreteBlockLaw W L r).real {o} * f o) := by
  have := isProbabilityMeasure_discreteBlockLaw (W := W) hr
  rw [lintegral_fintype, ENNReal.ofReal_sum_of_nonneg fun o _ => mul_nonneg measureReal_nonneg (hf o)]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [ENNReal.ofReal_mul measureReal_nonneg, ofReal_measureReal (measure_ne_top _ _), mul_comm]

/-- For any admissible weight, `E_o ‖diag(λ_o) v‖⁴ ≤ N(v)`. -/
theorem lintegral_blockLaw_slot_le {r : Fin J → Fin L → ℝ} (hr : ∀ a k, 0 ≤ r a k)
    (s : Fin (J * M)) (lam : Fin (L + 1) → Fin L × Fin W → ℝ) (hlam : IsSlotWeight W L r s lam)
    (v : Fin L × Fin W → ℂ) :
    ∫⁻ o, ENNReal.ofReal ((∑ x, lam o x ^ 2 * ‖v x‖ ^ 2) ^ 2)
        ∂discreteBlockLaw W L (r (tagGroup s)) ≤
      ENNReal.ofReal (blockFour W L (r (tagGroup s)) v) := by
  rw [lintegral_blockLaw_eq (hr _) _ fun o => sq_nonneg _]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases hlam with h | h | h
  · subst h
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      Finset.sum_const_zero, mul_zero]
    exact blockFour_nonneg _ _
  · subst h; rfl
  · subst h
    simp only
    rw [← Finset.sum_mul, sum_discreteBlockLaw_real (hr _), one_mul, gaussSq_eq (hr _)]
    exact sq_sum_blockLaw_le (hr _) _

/-- Reindexing the slots of one group. -/
theorem sum_tagGroup_ite {R : Type*} [AddCommMonoid R] (f : Fin (J * M) → R) (b : Fin J) :
    (∑ s, if tagGroup s = b then f s else 0) = ∑ i : Fin M, f (finProdFinEquiv (b, i)) := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [tagGroup, Equiv.symm_apply_apply]
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hb; simp [hb]
  · simp

/-- `star v ⬝ᵥ η_b` as a sum of independent linear forms of the slot vectors. -/
theorem dotc_slotSum (Λ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ)
    (κ : Fin (J * M) → Fin (L + 1)) (H : Fin (J * M) → Fin L × Fin W → ℂ)
    (v : Fin L × Fin W → ℂ) (b : Fin J) :
    star v ⬝ᵥ slotSum Λ (fun s => (κ s, H s)) b =
      ∑ s, star (fun x => if tagGroup s = b then
        (((Real.sqrt M)⁻¹ * Λ s (κ s) x : ℝ) : ℂ) * v x else 0) ⬝ᵥ H s := by
  unfold slotSum dotProduct
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun x _ => ?_
  by_cases h : tagGroup s = b
  · simp only [h, ↓reduceIte, Pi.star_apply, RCLike.star_def, map_mul, Complex.conj_ofReal]
    push_cast; ring
  · simp [h]

theorem sum_norm_sq_slotVec (Λ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ)
    (κ : Fin (J * M) → Fin (L + 1)) (v : Fin L × Fin W → ℂ) (b : Fin J) (s : Fin (J * M)) :
    ∑ x, ‖(fun x => if tagGroup s = b then
        (((Real.sqrt M)⁻¹ * Λ s (κ s) x : ℝ) : ℂ) * v x else (0 : ℂ)) x‖ ^ 2 =
      if tagGroup s = b then (Real.sqrt M)⁻¹ ^ 2 * ∑ x, Λ s (κ s) x ^ 2 * ‖v x‖ ^ 2 else 0 := by
  split_ifs
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]; ring
  · simp

/-- **Conditional Gaussian fourth moment of a group vector**: for admissible
weights, `E|v^* η_b|⁴ ≤ 2 N_b(v)` uniformly in `M` (Wick on the slot vectors, Cauchy–Schwarz over
the `M` slots, Jensen over each block law). -/
theorem lintegral_dotc_slotSum_pow_four_le {r : Fin J → Fin L → ℝ} (hr : ∀ a k, 0 ≤ r a k)
    (hM : 0 < M) {Λ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ}
    (hΛ : ∀ s, IsSlotWeight W L r s (Λ s)) (v : Fin L × Fin W → ℂ) (b : Fin J) :
    ∫⁻ x, ENNReal.ofReal (‖star v ⬝ᵥ slotSum Λ x b‖ ^ 4) ∂Measure.pi (slotMeasures W L r) ≤
      ENNReal.ofReal (2 * blockFour W L (r b) v) := by
  classical
  have hblk : ∀ s : Fin (J * M), IsProbabilityMeasure (discreteBlockLaw W L (r (tagGroup s))) := fun s =>
    isProbabilityMeasure_discreteBlockLaw (hr _)
  set e := MeasurableEquiv.arrowProdEquivProdArrow (Fin (L + 1)) (Fin L × Fin W → ℂ) (Fin (J * M))
  have hmp : MeasurePreserving e (Measure.pi (slotMeasures W L r))
      ((Measure.pi fun s => discreteBlockLaw W L (r (tagGroup s))).prod
        (Measure.pi fun _ : Fin (J * M) => circularVectorLaw (Fin L × Fin W))) :=
    measurePreserving_arrowProdEquivProdArrow _ _ _ _ _
  set f : (Fin (J * M) → SlotSample W L) → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (‖star v ⬝ᵥ slotSum Λ x b‖ ^ 4)
  have hf : Measurable f := by
    have hc : Continuous fun η : Fin J → Fin L × Fin W → ℂ => ‖star v ⬝ᵥ η b‖ ^ 4 := by
      unfold dotProduct; fun_prop
    exact ENNReal.measurable_ofReal.comp (hc.measurable.comp (measurable_slotSum Λ))
  rw [← (hmp.symm e).lintegral_comp_emb e.symm.measurableEmbedding f,
    lintegral_prod (fun p => f (e.symm p)) (hf.comp e.symm.measurable).aemeasurable]
  set t : ℝ := (Real.sqrt M)⁻¹
  set a : Fin (J * M) → Fin (L + 1) → ℝ := fun s o => ∑ x, Λ s o x ^ 2 * ‖v x‖ ^ 2
  have hinner : ∀ κ : Fin (J * M) → Fin (L + 1),
      ∫⁻ H, f (e.symm (κ, H)) ∂Measure.pi (fun _ : Fin (J * M) => circularVectorLaw _) ≤
        ENNReal.ofReal (2 * t ^ 4 * M * ∑ i : Fin M,
          a (finProdFinEquiv (b, i)) (κ (finProdFinEquiv (b, i))) ^ 2) := by
    intro κ
    have he : ∀ H, e.symm (κ, H) = fun s => (κ s, H s) := fun H => rfl
    simp only [f, he, dotc_slotSum]
    rw [lintegral_norm_pow_four_sum_dotc_pi]
    refine ENNReal.ofReal_le_ofReal ?_
    simp_rw [sum_norm_sq_slotVec]
    rw [sum_tagGroup_ite (fun s => t ^ 2 * a s (κ s)) b, ← Finset.mul_sum]
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun i : Fin M => a (finProdFinEquiv (b, i)) (κ (finProdFinEquiv (b, i))))
    simp only [Finset.card_univ, Fintype.card_fin] at hcs
    have ht : 0 ≤ t := by positivity
    calc 2 * (t ^ 2 * ∑ i : Fin M, a (finProdFinEquiv (b, i)) (κ (finProdFinEquiv (b, i)))) ^ 2
        = 2 * t ^ 4 * (∑ i : Fin M, a (finProdFinEquiv (b, i)) (κ (finProdFinEquiv (b, i)))) ^ 2 := by
          ring
      _ ≤ 2 * t ^ 4 * (M * ∑ i : Fin M,
            a (finProdFinEquiv (b, i)) (κ (finProdFinEquiv (b, i))) ^ 2) := by gcongr
      _ = _ := by ring
  refine (lintegral_mono hinner).trans ?_
  have ha : ∀ s o, 0 ≤ a s o := fun s o => by positivity
  simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * t ^ 4 * M),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => measurable_of_countable _),
    lintegral_finsetSum _ fun i _ => measurable_of_countable _]
  have hev : ∀ i : Fin M, ∫⁻ κ, ENNReal.ofReal (a (finProdFinEquiv (b, i))
      (κ (finProdFinEquiv (b, i))) ^ 2)
        ∂Measure.pi (fun s => discreteBlockLaw W L (r (tagGroup s))) ≤
      ENNReal.ofReal (blockFour W L (r b) v) := by
    intro i
    set s := finProdFinEquiv (b, i)
    have hs : tagGroup s = b := by simp [s, tagGroup]
    have hmap : (Measure.pi fun s => discreteBlockLaw W L (r (tagGroup s))).map
        (Function.eval s) = discreteBlockLaw W L (r (tagGroup s)) := by
      rw [Measure.pi_map_eval]; simp
    have := lintegral_map (μ := Measure.pi fun s => discreteBlockLaw W L (r (tagGroup s)))
      (f := fun o => ENNReal.ofReal (a s o ^ 2)) (measurable_of_countable _)
      (measurable_pi_apply s)
    rw [hmap] at this
    rw [← this]
    have h2 := lintegral_blockLaw_slot_le hr s (Λ s) (hΛ s) v
    rw [hs] at h2
    simpa only [a, hs] using h2
  refine (mul_le_mul_right (Finset.sum_le_sum fun i _ => hev i) _).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have ht4 : t ^ 4 * (M : ℝ) ^ 2 = 1 := by
    simp only [t, inv_pow]
    rw [show Real.sqrt M ^ 4 = (Real.sqrt M ^ 2) ^ 2 by ring, Real.sq_sqrt hM'.le]
    field_simp
  linear_combination (2 * blockFour W L (r b) v) * ht4

/-- `Σ_o μ{o} ofReal(c_o) = ofReal(E c)` for the block law. -/
theorem sum_blockLaw_mul_ofReal {r : Fin L → ℝ} (hr : ∀ k, 0 ≤ r k) (c : Fin (L + 1) → ℝ)
    (hc : ∀ o, 0 ≤ c o) :
    ∑ o, (discreteBlockLaw W L r) {o} * ENNReal.ofReal (c o) =
      ENNReal.ofReal (∑ o, (discreteBlockLaw W L r).real {o} * c o) := by
  rw [← lintegral_blockLaw_eq hr c hc, lintegral_fintype]
  exact Finset.sum_congr rfl fun o _ => mul_comm _ _

/-- Block-pair Hilbert–Schmidt mass `Σ_{x,y} tagW₁(o)_x² |G_xy|² tagW₂(o')_y²`
(`= E|ξ^*Gξ'|²` for independent tags on the blocks `o`, `o'`). -/
def pairHS (W L : ℕ) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (r₁ r₂ : Fin L → ℝ)
    (o o' : Fin (L + 1)) : ℝ :=
  ∑ x, ∑ y, tagWeight W L (profileMass W L r₁) o x ^ 2 * ‖G x y‖ ^ 2 *
    tagWeight W L (profileMass W L r₂) o' y ^ 2

theorem pairHS_nonneg (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (r₁ r₂ : Fin L → ℝ)
    (o o' : Fin (L + 1)) : 0 ≤ pairHS W L G r₁ r₂ o o' := by
  unfold pairHS; positivity

/-- The matrix `diag(tagW₁ o) G diag(λ)`. -/
def sandwich (W L : ℕ) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (r₁ : Fin L → ℝ)
    (o : Fin (L + 1)) (lam : Fin L × Fin W → ℝ) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Matrix.of fun x y => (tagWeight W L (profileMass W L r₁) o x : ℂ) * G x y * (lam y : ℂ)

theorem tagSq_mulVec_weightVec (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (r₁ : Fin L → ℝ) (o : Fin (L + 1)) (lam : Fin L × Fin W → ℝ) (h : Fin L × Fin W → ℂ) :
    tagSq W L r₁ o (G *ᵥ weightVec lam h) = ∑ x, ‖(sandwich W L G r₁ o lam *ᵥ h) x‖ ^ 2 := by
  unfold tagSq
  refine Finset.sum_congr rfl fun x _ => ?_
  have : (sandwich W L G r₁ o lam *ᵥ h) x =
      (tagWeight W L (profileMass W L r₁) o x : ℂ) * (G *ᵥ weightVec lam h) x := by
    unfold sandwich Matrix.mulVec dotProduct weightVec
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Matrix.of_apply]; ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem hs_sandwich (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (r₁ : Fin L → ℝ)
    (o : Fin (L + 1)) (lam : Fin L × Fin W → ℝ) :
    ∑ x, ∑ y, ‖sandwich W L G r₁ o lam x y‖ ^ 2 =
      ∑ x, ∑ y, tagWeight W L (profileMass W L r₁) o x ^ 2 * ‖G x y‖ ^ 2 * lam y ^ 2 := by
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  unfold sandwich
  simp only [Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- **Second stage** of the conditional moment bound: average over the swapped slot. -/
theorem lintegral_slot_blockFour_le {r : Fin J → Fin L → ℝ} (hr : ∀ a k, 0 ≤ r a k)
    (a b : Fin J) (lam : Fin (L + 1) → Fin L × Fin W → ℝ)
    (hlam : lam = tagWeight W L (profileMass W L (r a)) ∨ lam = fun _ => gaussWeight W L (r a))
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    ∫⁻ y', ENNReal.ofReal (2 * blockFour W L (r b) (G *ᵥ weightVec (lam y'.1) y'.2))
        ∂slotLaw W L (r a) ≤
      ENNReal.ofReal (4 * ∑ o, ∑ o', (discreteBlockLaw W L (r b)).real {o} *
        (discreteBlockLaw W L (r a)).real {o'} * pairHS W L G (r b) (r a) o o' ^ 2) := by
  have hmeas : Measurable fun y' : SlotSample W L =>
      ENNReal.ofReal (2 * blockFour W L (r b) (G *ᵥ weightVec (lam y'.1) y'.2)) := by
    refine ENNReal.measurable_ofReal.comp (measurable_slot_of fun o => ?_)
    unfold blockFour tagSq weightVec Matrix.mulVec dotProduct
    exact (by fun_prop : Continuous fun h : Fin L × Fin W → ℂ => _).measurable
  rw [lintegral_slotLaw hmeas]
  -- the inner Gaussian integral for a fixed block of the swapped slot
  have hin : ∀ o', ∫⁻ h, ENNReal.ofReal (2 * blockFour W L (r b) (G *ᵥ weightVec (lam o') h))
      ∂circularVectorLaw (Fin L × Fin W) ≤
      ENNReal.ofReal (4 * ∑ o, (discreteBlockLaw W L (r b)).real {o} *
        (∑ x, ∑ y, tagWeight W L (profileMass W L (r b)) o x ^ 2 * ‖G x y‖ ^ 2 *
          lam o' y ^ 2) ^ 2) := by
    intro o'
    have hint : ∀ o, Integrable (fun h => (∑ x, ‖(sandwich W L G (r b) o (lam o') *ᵥ h) x‖ ^ 2) ^ 2)
        (circularVectorLaw (Fin L × Fin W)) := fun o => integrable_sq_sum_norm_sq_mulVec _
    have hint2 : Integrable (fun h => 2 * blockFour W L (r b) (G *ᵥ weightVec (lam o') h))
        (circularVectorLaw (Fin L × Fin W)) := by
      unfold blockFour
      simp_rw [tagSq_mulVec_weightVec]
      exact (integrable_finsetSum _ fun o _ => (hint o).const_mul _).const_mul 2
    rw [← ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all _ fun h =>
      mul_nonneg zero_le_two (blockFour_nonneg _ _))]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold blockFour
    simp_rw [tagSq_mulVec_weightVec]
    rw [integral_const_mul, integral_finsetSum _ fun o _ => (hint o).const_mul _]
    simp_rw [integral_const_mul]
    have hb : ∀ o, (discreteBlockLaw W L (r b)).real {o} *
        ∫ h, (∑ x, ‖(sandwich W L G (r b) o (lam o') *ᵥ h) x‖ ^ 2) ^ 2
          ∂circularVectorLaw (Fin L × Fin W) ≤
        (discreteBlockLaw W L (r b)).real {o} * (2 * (∑ x, ∑ y,
          tagWeight W L (profileMass W L (r b)) o x ^ 2 * ‖G x y‖ ^ 2 * lam o' y ^ 2) ^ 2) := by
      intro o
      have h1 := integral_sq_sum_norm_sq_mulVec_le (sandwich W L G (r b) o (lam o'))
      rw [hs_sandwich] at h1
      exact mul_le_mul_of_nonneg_left h1 measureReal_nonneg
    calc 2 * ∑ o, (discreteBlockLaw W L (r b)).real {o} *
          ∫ h, (∑ x, ‖(sandwich W L G (r b) o (lam o') *ᵥ h) x‖ ^ 2) ^ 2
            ∂circularVectorLaw (Fin L × Fin W)
        ≤ 2 * ∑ o, (discreteBlockLaw W L (r b)).real {o} * (2 * (∑ x, ∑ y,
          tagWeight W L (profileMass W L (r b)) o x ^ 2 * ‖G x y‖ ^ 2 * lam o' y ^ 2) ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun o _ => hb o) (by norm_num)
      _ = _ := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun o _ => ?_
          ring
  refine (Finset.sum_le_sum fun o' _ => mul_le_mul_right (hin o') _).trans (le_of_eq_of_le
    (sum_blockLaw_mul_ofReal (hr a) _ fun o' => by positivity) ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  rcases hlam with h | h
  · subst h
    unfold pairHS
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun o _ => Finset.sum_le_sum fun o' _ => le_of_eq ?_
    ring
  · subst h
    simp only
    rw [← Finset.sum_mul, sum_discreteBlockLaw_real (hr a), one_mul, Finset.mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun o _ => ?_
    have hD : ∑ x, ∑ y, tagWeight W L (profileMass W L (r b)) o x ^ 2 * ‖G x y‖ ^ 2 *
        gaussWeight W L (r a) y ^ 2 =
        ∑ o', (discreteBlockLaw W L (r a)).real {o'} * pairHS W L G (r b) (r a) o o' := by
      symm
      calc ∑ o', (discreteBlockLaw W L (r a)).real {o'} * pairHS W L G (r b) (r a) o o'
          = ∑ o', ∑ x, ∑ y, (discreteBlockLaw W L (r a)).real {o'} *
              (tagWeight W L (profileMass W L (r b)) o x ^ 2 * ‖G x y‖ ^ 2 *
                tagWeight W L (profileMass W L (r a)) o' y ^ 2) := by
            unfold pairHS; simp_rw [Finset.mul_sum]
        _ = ∑ x, ∑ y, ∑ o', (discreteBlockLaw W L (r a)).real {o'} *
              (tagWeight W L (profileMass W L (r b)) o x ^ 2 * ‖G x y‖ ^ 2 *
                tagWeight W L (profileMass W L (r a)) o' y ^ 2) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
            rw [← sum_discreteBlockLaw_tagWeight_sq (hr a) y, Finset.mul_sum]
            refine Finset.sum_congr rfl fun o' _ => ?_
            ring
    rw [hD]
    have hJ := sq_sum_blockLaw_le (W := W) (hr a) (fun o' => pairHS W L G (r b) (r a) o o')
    have hp := measureReal_nonneg (μ := discreteBlockLaw W L (r b)) (s := {o})
    calc 4 * ((discreteBlockLaw W L (r b)).real {o} *
          (∑ o', (discreteBlockLaw W L (r a)).real {o'} * pairHS W L G (r b) (r a) o o') ^ 2)
        ≤ 4 * ((discreteBlockLaw W L (r b)).real {o} *
          ∑ o', (discreteBlockLaw W L (r a)).real {o'} * pairHS W L G (r b) (r a) o o' ^ 2) := by
          gcongr
      _ = _ := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun o' _ => ?_
          ring

/-!
## Pointwise bound of the swap remainder
-/

theorem dotc_swap {σ : Type*} [Fintype σ] (G : Matrix σ σ ℂ) (X η : σ → ℂ) :
    ‖star X ⬝ᵥ (G *ᵥ η)‖ = ‖star η ⬝ᵥ (Gᴴ *ᵥ X)‖ := by
  have h : star X ⬝ᵥ (G *ᵥ η) = star (star η ⬝ᵥ (Gᴴ *ᵥ X)) := by
    unfold dotProduct Matrix.mulVec dotProduct
    rw [star_sum]
    simp_rw [Finset.mul_sum, star_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.star_apply, star_mul', star_star, Matrix.conjTranspose_apply]
    ring
  rw [h, norm_star]

theorem remainder_real_le {a bb Z Q K t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ bb) (hZ : 0 ≤ Z) (hQ : 0 ≤ Q)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (haZ : a ≤ K * Z) (hbQ : bb ≤ K * Q) :
    t ^ 3 * (4 * a ^ 3 + a * bb + 5 * bb ^ 2) ≤ t ^ 3 * (K ^ 3 * (5 + 5 * Z ^ 4 + 6 * Q ^ 2)) := by
  have hK0 : 0 ≤ K := by linarith
  have h1 : a ^ 3 ≤ K ^ 3 * Z ^ 3 := by rw [← mul_pow]; exact pow_le_pow_left₀ ha haZ 3
  have h2 : a * bb ≤ K ^ 2 * (Z * Q) := by
    calc a * bb ≤ (K * Z) * (K * Q) := mul_le_mul haZ hbQ hb (by positivity)
      _ = K ^ 2 * (Z * Q) := by ring
  have h3 : bb ^ 2 ≤ K ^ 2 * Q ^ 2 := by rw [← mul_pow]; exact pow_le_pow_left₀ hb hbQ 2
  have hK2 : K ^ 2 ≤ K ^ 3 := pow_le_pow_right₀ hK (by norm_num)
  have hZ3 : Z ^ 3 ≤ 1 + Z ^ 4 := by
    rcases le_or_gt Z 1 with h | h
    · have : Z ^ 3 ≤ 1 := pow_le_one₀ hZ h
      nlinarith [pow_nonneg hZ 4]
    · have : Z ^ 3 ≤ Z ^ 4 := pow_le_pow_right₀ h.le (by norm_num)
      linarith
  have hZQ : Z * Q ≤ (1 + Z ^ 4) / 4 + Q ^ 2 / 2 := by
    nlinarith [sq_nonneg (Z - Q), sq_nonneg (Z ^ 2 - 1)]
  have key : 4 * a ^ 3 + a * bb + 5 * bb ^ 2 ≤ K ^ 3 * (5 + 5 * Z ^ 4 + 6 * Q ^ 2) := by
    have e1 : 4 * a ^ 3 ≤ K ^ 3 * (4 * Z ^ 3) := by nlinarith
    have e2 : a * bb ≤ K ^ 3 * (Z * Q) := le_trans h2 (mul_le_mul_of_nonneg_right hK2 (by positivity))
    have e3 : 5 * bb ^ 2 ≤ K ^ 3 * (5 * Q ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_right hK2 (sq_nonneg Q)]
    have e4 : 4 * Z ^ 3 + Z * Q + 5 * Q ^ 2 ≤ 5 + 5 * Z ^ 4 + 6 * Q ^ 2 := by
      have := pow_nonneg hZ 4; have := sq_nonneg Q; linarith
    have : K ^ 3 * (4 * Z ^ 3) + K ^ 3 * (Z * Q) + K ^ 3 * (5 * Q ^ 2) ≤
        K ^ 3 * (5 + 5 * Z ^ 4 + 6 * Q ^ 2) := by
      rw [← mul_add, ← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  exact mul_le_mul_of_nonneg_left key (by positivity)

theorem sum_pow_four_le {J : ℕ} (A B : Fin J → ℝ) (hA : ∀ b, 0 ≤ A b) (hB : ∀ b, 0 ≤ B b) :
    (∑ b, (A b + B b)) ^ 4 ≤ 8 * (J : ℝ) ^ 3 * ∑ b, (A b ^ 4 + B b ^ 4) := by
  have h := pow_sum_le_card_mul_sum_pow (s := Finset.univ) (f := fun b => A b + B b)
    (fun b _ => add_nonneg (hA b) (hB b)) 3
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have h2 : ∀ b, (A b + B b) ^ 4 ≤ 8 * (A b ^ 4 + B b ^ 4) := by
    intro b
    nlinarith [sq_nonneg (A b - B b), sq_nonneg (A b + B b), mul_nonneg (hA b) (hB b),
      sq_nonneg (A b ^ 2 - B b ^ 2), mul_nonneg (mul_nonneg (hA b) (hB b)) (sq_nonneg (A b - B b))]
  calc (∑ b, (A b + B b)) ^ 4 ≤ (J : ℝ) ^ 3 * ∑ b, (A b + B b) ^ 4 := h
    _ ≤ (J : ℝ) ^ 3 * ∑ b, 8 * (A b ^ 4 + B b ^ 4) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => h2 b) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- **Pointwise remainder bound**: `R ≤ t³ (1+2‖u‖)³ (5 + 40J³ Σ_b (|η_b^*GX|⁴ + |η_b^*G^*X|⁴) +
6|X^*GX|²)`. -/
theorem swapRemainder_le (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (Λ₀ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ) (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2))
    (j : Fin (J * M)) (lam : Fin (L + 1) → Fin L × Fin W → ℝ) (x : Fin (J * M) → SlotSample W L)
    (y' : SlotSample W L) :
    swapRemainder G Λ₀ u j lam x y' ≤ ENNReal.ofReal ((Real.sqrt M)⁻¹ ^ 3 *
      ((1 + 2 * ‖u‖) ^ 3 * (5 + 5 * (8 * (J : ℝ) ^ 3 * ∑ b,
        (‖star (slotSum (zeroAt j Λ₀) x b) ⬝ᵥ (G *ᵥ weightVec (lam y'.1) y'.2)‖ ^ 4 +
          ‖star (slotSum (zeroAt j Λ₀) x b) ⬝ᵥ (Gᴴ *ᵥ weightVec (lam y'.1) y'.2)‖ ^ 4)) +
        6 * ‖star (weightVec (lam y'.1) y'.2) ⬝ᵥ (G *ᵥ weightVec (lam y'.1) y'.2)‖ ^ 2))) := by
  set η := slotSum (zeroAt j Λ₀) x
  set X0 := weightVec (lam y'.1) y'.2
  set A : Fin J → ℝ := fun b => ‖star (η b) ⬝ᵥ (G *ᵥ X0)‖
  set B : Fin J → ℝ := fun b => ‖star (η b) ⬝ᵥ (Gᴴ *ᵥ X0)‖
  set Q := ‖star X0 ⬝ᵥ (G *ᵥ X0)‖
  set Z := ∑ b, (A b + B b)
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun b _ => add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hα : |swapAlpha G Λ₀ u j lam x y'| ≤ (1 + 2 * ‖u‖) * Z := by
    unfold swapAlpha
    rw [← re_lin_eq]
    refine (Complex.abs_re_le_norm _).trans ?_
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖∑ b, coefU u b (tagGroup j) * (star (η b) ⬝ᵥ (G *ᵥ X0))‖ ≤ 2 * ‖u‖ * ∑ b, A b := by
      rw [Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_coefU_le u b _) (norm_nonneg _)
    have h2 : ‖∑ c, coefU u (tagGroup j) c * (star X0 ⬝ᵥ (G *ᵥ η c))‖ ≤ 2 * ‖u‖ * ∑ b, B b := by
      rw [Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
      rw [norm_mul, dotc_swap]
      exact mul_le_mul_of_nonneg_right (norm_coefU_le u _ c) (norm_nonneg _)
    have hu : 0 ≤ ‖u‖ := norm_nonneg _
    have hA : 0 ≤ ∑ b, A b := Finset.sum_nonneg fun b _ => norm_nonneg _
    have hB : 0 ≤ ∑ b, B b := Finset.sum_nonneg fun b _ => norm_nonneg _
    have hZ : Z = ∑ b, A b + ∑ b, B b := Finset.sum_add_distrib
    rw [hZ]
    nlinarith
  have hβ : |swapBeta G u j lam y'| ≤ (1 + 2 * ‖u‖) * Q := by
    unfold swapBeta
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    have := norm_coefU_le u (tagGroup j) (tagGroup j)
    have hQ : 0 ≤ Q := norm_nonneg _
    nlinarith
  unfold swapRemainder
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← sq_abs (swapBeta G u j lam y')]
  have hK : 1 ≤ 1 + 2 * ‖u‖ := by have := norm_nonneg u; linarith
  have hmain := remainder_real_le (abs_nonneg _) (abs_nonneg _) hZ0 (norm_nonneg _) hK
    (by positivity : (0 : ℝ) ≤ (Real.sqrt M)⁻¹) hα hβ
  have hZ4 := sum_pow_four_le A B (fun b => norm_nonneg _) (fun b => norm_nonneg _)
  refine hmain.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
    (by positivity))
  have : 5 * Z ^ 4 ≤ 5 * (8 * (J : ℝ) ^ 3 * ∑ b, (A b ^ 4 + B b ^ 4)) := by linarith
  linarith

end Det

section FixedG
variable {W L J M : ℕ}

theorem norm_dotc_comm {σ : Type*} [Fintype σ] (a b : σ → ℂ) :
    ‖star a ⬝ᵥ b‖ = ‖star b ⬝ᵥ a‖ := by
  have h : star a ⬝ᵥ b = star (star b ⬝ᵥ a) := by
    unfold dotProduct
    rw [star_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.star_apply, star_mul', star_star]
    ring
  rw [h, norm_star]

theorem measurable_weightVec_slot (lam : Fin (L + 1) → Fin L × Fin W → ℝ) :
    Measurable fun y' : SlotSample W L => weightVec (lam y'.1) y'.2 := by
  refine Measurable.of_eval fun x => ?_
  unfold weightVec
  exact ((measurable_of_countable fun o : Fin (L + 1) => (lam o x : ℂ)).comp measurable_fst).mul
    ((measurable_pi_apply x).comp measurable_snd)

/-- Block-pair fourth moment `Σ_{o,o'} p_b(o) p_a(o') pairHS(o,o')²`. -/
def pairFour (W L : ℕ) {J : ℕ} (r : Fin J → Fin L → ℝ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (b a : Fin J) : ℝ :=
  ∑ o, ∑ o', (discreteBlockLaw W L (r b)).real {o} * (discreteBlockLaw W L (r a)).real {o'} *
    pairHS W L G (r b) (r a) o o' ^ 2

theorem pairFour_nonneg (r : Fin J → Fin L → ℝ) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (b a : Fin J) : 0 ≤ pairFour W L r G b a := by
  unfold pairFour
  exact Finset.sum_nonneg fun o _ => Finset.sum_nonneg fun o' _ =>
    mul_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg) (sq_nonneg _)

/-- `|η_b^* G X|⁴` for the swapped slot vector `X`. -/
def swapA (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (Λ₀ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ) (j : Fin (J * M))
    (lam : Fin (L + 1) → Fin L × Fin W → ℝ) (b : Fin J) (x : Fin (J * M) → SlotSample W L)
    (y' : SlotSample W L) : ℝ :=
  ‖star (slotSum (zeroAt j Λ₀) x b) ⬝ᵥ (G *ᵥ weightVec (lam y'.1) y'.2)‖ ^ 4

/-- `|X^* G X|²` for the swapped slot vector `X`. -/
def swapQ (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (lam : Fin (L + 1) → Fin L × Fin W → ℝ)
    (y' : SlotSample W L) : ℝ :=
  ‖star (weightVec (lam y'.1) y'.2) ⬝ᵥ (G *ᵥ weightVec (lam y'.1) y'.2)‖ ^ 2

/-- The quadratic-form second moment `E|X^*GX|²` of the swapped slot. -/
def quadMoment (W L : ℕ) (r : Fin L → ℝ) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (lam : Fin (L + 1) → Fin L × Fin W → ℝ) : ℝ≥0∞ :=
  ∫⁻ y', ENNReal.ofReal (swapQ G lam y') ∂slotLaw W L r

theorem ofReal_combo {J : ℕ} (c Q : ℝ) (S S' : Fin J → ℝ) (hc : 0 ≤ c) (hS : ∀ b, 0 ≤ S b)
    (hS' : ∀ b, 0 ≤ S' b) (hQ : 0 ≤ Q) :
    ENNReal.ofReal (c * (5 + 40 * (J : ℝ) ^ 3 * ∑ b, (S b + S' b) + 6 * Q)) =
      ENNReal.ofReal c * (ENNReal.ofReal 5 + ENNReal.ofReal (40 * (J : ℝ) ^ 3) *
        ∑ b, (ENNReal.ofReal (S b) + ENNReal.ofReal (S' b)) +
        ENNReal.ofReal 6 * ENNReal.ofReal Q) := by
  have hsum : 0 ≤ ∑ b, (S b + S' b) := Finset.sum_nonneg fun b _ => add_nonneg (hS b) (hS' b)
  rw [ENNReal.ofReal_mul hc]
  congr 1
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by norm_num) (by positivity),
    ENNReal.ofReal_mul (p := 40 * (J : ℝ) ^ 3) (by positivity),
    ENNReal.ofReal_mul (p := (6 : ℝ)) (by norm_num), ENNReal.ofReal_sum_of_nonneg fun b _ =>
      add_nonneg (hS b) (hS' b)]
  simp_rw [ENNReal.ofReal_add (hS _) (hS' _)]

theorem swapRemainder_le_ennreal (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (Λ₀ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ) (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2))
    (j : Fin (J * M)) (lam : Fin (L + 1) → Fin L × Fin W → ℝ) (x : Fin (J * M) → SlotSample W L)
    (y' : SlotSample W L) :
    swapRemainder G Λ₀ u j lam x y' ≤
      ENNReal.ofReal ((Real.sqrt M)⁻¹ ^ 3 * (1 + 2 * ‖u‖) ^ 3) *
        (ENNReal.ofReal 5 + ENNReal.ofReal (40 * (J : ℝ) ^ 3) *
          ∑ b, (ENNReal.ofReal (swapA G Λ₀ j lam b x y') +
            ENNReal.ofReal (swapA Gᴴ Λ₀ j lam b x y')) +
          ENNReal.ofReal 6 * ENNReal.ofReal (swapQ G lam y')) := by
  refine (swapRemainder_le G Λ₀ u j lam x y').trans (le_of_eq ?_)
  have hA : ∀ (G' : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) b, 0 ≤ swapA G' Λ₀ j lam b x y' :=
    fun G' b => by unfold swapA; positivity
  have hQ : 0 ≤ swapQ G lam y' := by unfold swapQ; positivity
  have e : (Real.sqrt M)⁻¹ ^ 3 * ((1 + 2 * ‖u‖) ^ 3 * (5 + 5 * (8 * (J : ℝ) ^ 3 * ∑ b,
      (‖star (slotSum (zeroAt j Λ₀) x b) ⬝ᵥ (G *ᵥ weightVec (lam y'.1) y'.2)‖ ^ 4 +
        ‖star (slotSum (zeroAt j Λ₀) x b) ⬝ᵥ (Gᴴ *ᵥ weightVec (lam y'.1) y'.2)‖ ^ 4)) +
      6 * ‖star (weightVec (lam y'.1) y'.2) ⬝ᵥ (G *ᵥ weightVec (lam y'.1) y'.2)‖ ^ 2)) =
      ((Real.sqrt M)⁻¹ ^ 3 * (1 + 2 * ‖u‖) ^ 3) * (5 + 40 * (J : ℝ) ^ 3 *
        ∑ b, (swapA G Λ₀ j lam b x y' + swapA Gᴴ Λ₀ j lam b x y') + 6 * swapQ G lam y') := by
    unfold swapA swapQ; ring
  rw [e]
  exact ofReal_combo _ _ _ _ (by positivity) (hA G) (hA Gᴴ) hQ

theorem measurable_swapA (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (Λ₀ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ) (j : Fin (J * M))
    (lam : Fin (L + 1) → Fin L × Fin W → ℝ) (b : Fin J) :
    Measurable fun p : (Fin (J * M) → SlotSample W L) × SlotSample W L =>
      ENNReal.ofReal (swapA G Λ₀ j lam b p.1 p.2) := by
  have hc : Continuous fun q : (Fin J → Fin L × Fin W → ℂ) × (Fin L × Fin W → ℂ) =>
      ‖star (q.1 b) ⬝ᵥ (G *ᵥ q.2)‖ ^ 4 := by
    unfold dotProduct Matrix.mulVec dotProduct; fun_prop
  have h1 : Measurable fun p : (Fin (J * M) → SlotSample W L) × SlotSample W L =>
      (slotSum (zeroAt j Λ₀) p.1, weightVec (lam p.2.1) p.2.2) :=
    ((measurable_slotSum (zeroAt j Λ₀)).comp measurable_fst).prodMk
      ((measurable_weightVec_slot lam).comp measurable_snd)
  have h2 := ENNReal.measurable_ofReal.comp (hc.measurable.comp h1)
  unfold swapA
  exact h2

theorem measurable_swapQ (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (lam : Fin (L + 1) → Fin L × Fin W → ℝ) :
    Measurable fun y' : SlotSample W L => ENNReal.ofReal (swapQ G lam y') := by
  have hc : Continuous fun X : Fin L × Fin W → ℂ => ‖star X ⬝ᵥ (G *ᵥ X)‖ ^ 2 := by
    unfold dotProduct Matrix.mulVec dotProduct; fun_prop
  exact ENNReal.measurable_ofReal.comp (hc.measurable.comp (measurable_weightVec_slot lam))

/-- Fourth moment of `η_b^* G X` for the swapped slot, averaged over everything. -/
theorem lintegral_swapA_le {r : Fin J → Fin L → ℝ} (hr : ∀ a k, 0 ≤ r a k) (hM : 0 < M)
    {Λ₀ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ} (hΛ : ∀ s, IsSlotWeight W L r s (Λ₀ s))
    (j : Fin (J * M)) (lam : Fin (L + 1) → Fin L × Fin W → ℝ)
    (hlam : lam = tagWeight W L (profileMass W L (r (tagGroup j))) ∨
      lam = fun _ => gaussWeight W L (r (tagGroup j)))
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (b : Fin J) :
    ∫⁻ x, ∫⁻ y', ENNReal.ofReal (swapA G Λ₀ j lam b x y') ∂slotLaw W L (r (tagGroup j))
        ∂Measure.pi (slotMeasures W L r) ≤
      ENNReal.ofReal (4 * pairFour W L r G b (tagGroup j)) := by
  have hμ : ∀ s : Fin (J * M), IsProbabilityMeasure (slotMeasures W L r s) := fun s =>
    isProbabilityMeasure_slotLaw (hr _)
  have hj : IsProbabilityMeasure (slotLaw W L (r (tagGroup j))) :=
    isProbabilityMeasure_slotLaw (hr _)
  rw [lintegral_lintegral_swap (measurable_swapA G Λ₀ j lam b).aemeasurable]
  have hin : ∀ y' : SlotSample W L, ∫⁻ x, ENNReal.ofReal (swapA G Λ₀ j lam b x y')
      ∂Measure.pi (slotMeasures W L r) ≤
      ENNReal.ofReal (2 * blockFour W L (r b) (G *ᵥ weightVec (lam y'.1) y'.2)) := by
    intro y'
    unfold swapA
    simp_rw [norm_dotc_comm (slotSum (zeroAt j Λ₀) _ b)]
    exact lintegral_dotc_slotSum_pow_four_le hr hM (isSlotWeight_zeroAt hΛ j) _ b
  refine (lintegral_mono hin).trans ?_
  exact lintegral_slot_blockFour_le hr (tagGroup j) b lam hlam G

theorem lintegral_swapQ_eq {r : Fin J → Fin L → ℝ} (hr : ∀ a k, 0 ≤ r a k)
    (j : Fin (J * M)) (lam : Fin (L + 1) → Fin L × Fin W → ℝ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    ∫⁻ _x : Fin (J * M) → SlotSample W L, ∫⁻ y', ENNReal.ofReal (swapQ G lam y')
        ∂slotLaw W L (r (tagGroup j)) ∂Measure.pi (slotMeasures W L r) =
      quadMoment W L (r (tagGroup j)) G lam := by
  have hμ : ∀ s : Fin (J * M), IsProbabilityMeasure (slotMeasures W L r s) := fun s =>
    isProbabilityMeasure_slotLaw (hr _)
  rw [lintegral_const, measure_univ, mul_one]
  rfl

/-- **The expected remainder of one swap for a fixed matrix `G`.** -/
theorem lintegral_swapRemainder_le {r : Fin J → Fin L → ℝ} (hr : ∀ a k, 0 ≤ r a k) (hM : 0 < M)
    {Λ₀ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ} (hΛ : ∀ s, IsSlotWeight W L r s (Λ₀ s))
    (j : Fin (J * M)) (lam : Fin (L + 1) → Fin L × Fin W → ℝ)
    (hlam : lam = tagWeight W L (profileMass W L (r (tagGroup j))) ∨
      lam = fun _ => gaussWeight W L (r (tagGroup j)))
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) :
    ∫⁻ x, ∫⁻ y', swapRemainder G Λ₀ u j lam x y' ∂slotLaw W L (r (tagGroup j))
        ∂Measure.pi (slotMeasures W L r) ≤
      ENNReal.ofReal ((Real.sqrt M)⁻¹ ^ 3 * (1 + 2 * ‖u‖) ^ 3) *
        (ENNReal.ofReal 5 + ENNReal.ofReal (40 * (J : ℝ) ^ 3) *
          ∑ b, (ENNReal.ofReal (4 * pairFour W L r G b (tagGroup j)) +
            ENNReal.ofReal (4 * pairFour W L r Gᴴ b (tagGroup j))) +
          ENNReal.ofReal 6 * quadMoment W L (r (tagGroup j)) G lam) := by
  have hμ : ∀ s : Fin (J * M), IsProbabilityMeasure (slotMeasures W L r s) := fun s =>
    isProbabilityMeasure_slotLaw (hr _)
  have hj : IsProbabilityMeasure (slotLaw W L (r (tagGroup j))) :=
    isProbabilityMeasure_slotLaw (hr _)
  set P := Measure.pi (slotMeasures W L r)
  set ρ := slotLaw W L (r (tagGroup j))
  set c := ENNReal.ofReal ((Real.sqrt M)⁻¹ ^ 3 * (1 + 2 * ‖u‖) ^ 3)
  have hbound := fun x y' => swapRemainder_le_ennreal G Λ₀ u j lam x y'
  refine (lintegral_mono fun x => lintegral_mono fun y' => hbound x y').trans (le_of_eq_of_le
    (b := c * (ENNReal.ofReal 5 + ENNReal.ofReal (40 * (J : ℝ) ^ 3) *
      ∑ b, (∫⁻ x, ∫⁻ y', ENNReal.ofReal (swapA G Λ₀ j lam b x y') ∂ρ ∂P +
        ∫⁻ x, ∫⁻ y', ENNReal.ofReal (swapA Gᴴ Λ₀ j lam b x y') ∂ρ ∂P) +
      ENNReal.ofReal 6 * ∫⁻ x, ∫⁻ y', ENNReal.ofReal (swapQ G lam y') ∂ρ ∂P)) ?_ ?_)
  · -- linearity on the product space
    have hA := measurable_swapA G Λ₀ j lam (M := M)
    have hB := measurable_swapA Gᴴ Λ₀ j lam (M := M)
    have hQ : Measurable fun p : (Fin (J * M) → SlotSample W L) × SlotSample W L =>
        ENNReal.ofReal (swapQ G lam p.2) := (measurable_swapQ G lam).comp measurable_snd
    have hit : ∀ f : (Fin (J * M) → SlotSample W L) × SlotSample W L → ℝ≥0∞, Measurable f →
        ∫⁻ x, ∫⁻ y', f (x, y') ∂ρ ∂P = ∫⁻ p, f p ∂P.prod ρ := fun f hf =>
      (lintegral_prod f hf.aemeasurable).symm
    rw [hit (fun p => c * (ENNReal.ofReal 5 + ENNReal.ofReal (40 * (J : ℝ) ^ 3) *
        ∑ b, (ENNReal.ofReal (swapA G Λ₀ j lam b p.1 p.2) +
          ENNReal.ofReal (swapA Gᴴ Λ₀ j lam b p.1 p.2)) +
        ENNReal.ofReal 6 * ENNReal.ofReal (swapQ G lam p.2)))
      (measurable_const.mul ((measurable_const.add (measurable_const.mul
        (Finset.measurable_sum _ fun b _ => (hA b).add (hB b)))).add (measurable_const.mul hQ)))]
    rw [hit _ hQ]
    simp_rw [fun b => hit _ (hA b), fun b => hit _ (hB b)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    rw [lintegral_add_right (fun p => ENNReal.ofReal 5 + ENNReal.ofReal (40 * (J : ℝ) ^ 3) *
        ∑ b, (ENNReal.ofReal (swapA G Λ₀ j lam b p.1 p.2) +
          ENNReal.ofReal (swapA Gᴴ Λ₀ j lam b p.1 p.2))) (hQ.const_mul _),
      lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_finsetSum _ fun b _ => show Measurable fun p : (Fin (J * M) → SlotSample W L) ×
        SlotSample W L => ENNReal.ofReal (swapA G Λ₀ j lam b p.1 p.2) +
          ENNReal.ofReal (swapA Gᴴ Λ₀ j lam b p.1 p.2) from (hA b).add (hB b)]
    simp_rw [lintegral_add_left (hA _)]
  · gcongr with b
    · exact lintegral_swapA_le hr hM hΛ j lam hlam G b
    · exact lintegral_swapA_le hr hM hΛ j lam hlam Gᴴ b
    · exact (lintegral_swapQ_eq hr j lam G).le

end FixedG

end BlockBand.Critical.GlobalSource
