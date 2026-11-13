module

public import BlockBand.SourceProcess.ComplexSourceLaw.ExtTrace

/-!
# The Hilbert–Schmidt term of the extended source moments

Writing the squared Hilbert–Schmidt norm of the extended source matrix `A_Q` as a weighted sum over
tag pairs `(k, l)` with weights `(q_k/W)(q_l/W)`, Jensen and the two-tag raw bound give
`E‖A_Q‖_HS^p ≤ 1 + S^{2(r-1)} · S² · C'`, `S = Σ_k q_k/W` (`lintegral_hs_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionLaws

variable {W n : ℕ}

/-- The unit-mass two-tag form `ξ_k*Gξ'_l` with independent Gaussians `x = (g, h)`. -/
def tagY (b E : ℝ) (kl : Fin n × Fin n) (ω : GrowthPath W)
    (x : (Fin W → ℂ) × (Fin W → ℂ)) : ℂ :=
  tagForm (fullInverse b E W n ω).toBlocks₁₁ (tagVector W n kl.1 1 x.1)
    (tagVector W n kl.2 1 x.2)

theorem measurable_tagY_rpow (b E : ℝ) (kl : Fin n × Fin n) (p : ℝ) :
    Measurable fun z : GrowthPath W × ((Fin W → ℂ) × (Fin W → ℂ)) =>
      ENNReal.ofReal (‖tagY b E kl z.1 z.2‖ ^ p) :=
  ((measurable_tagForm ((measurable_interior b E n).comp measurable_fst)
    ((measurable_tagVector n kl.1 1).comp (measurable_fst.comp measurable_snd))
    ((measurable_tagVector n kl.2 1).comp (measurable_snd.comp measurable_snd))).norm.pow_const
      p).ennreal_ofReal

/-- The pair weight `w_{kl} = (q_k/W)(q_l/W)`. -/
def pairW (W : ℕ) (q : Fin n → ℝ) (kl : Fin n × Fin n) : ℝ := q kl.1 / W * (q kl.2 / W)

/-- `V_{kl} = W⁻² Σ_{a,b}|G_{(k,a),(l,b)}|² = E|ξ_k*Gξ'_l|²`. -/
def pairV (b E : ℝ) (ω : GrowthPath W) (kl : Fin n × Fin n) : ℝ :=
  ((W : ℝ)⁻¹) ^ 2 * ∑ a, ∑ b', ‖(fullInverse b E W n ω).toBlocks₁₁ (kl.1, a) (kl.2, b')‖ ^ 2

theorem pairW_nonneg (q : Fin n → ℝ) (hq : ∀ k, 0 ≤ q k) (kl : Fin n × Fin n) :
    0 ≤ pairW W q kl :=
  mul_nonneg (div_nonneg (hq _) (Nat.cast_nonneg W)) (div_nonneg (hq _) (Nat.cast_nonneg W))

theorem pairV_nonneg (b E : ℝ) (ω : GrowthPath W) (kl : Fin n × Fin n) : 0 ≤ pairV b E ω kl := by
  unfold pairV; positivity

/-- The squared HS norm as a weighted sum over tag pairs. -/
theorem hs_extended_pairs (b E : ℝ) (q : Fin n → ℝ) (hq : ∀ k, 0 ≤ q k) (ω : GrowthPath W) :
    ∑ x, ∑ y, ‖extendedSourceMatrix b E W n q ω x y‖ ^ 2 =
      ∑ kl : Fin n × Fin n, pairW W q kl * pairV b E ω kl := by
  rw [hs_extended b E q hq ω, Fintype.sum_prod_type]
  rfl

theorem sum_pairW (q : Fin n → ℝ) :
    ∑ kl : Fin n × Fin n, pairW W q kl = (∑ k, q k / W) ^ 2 := by
  rw [Fintype.sum_prod_type, sq, Finset.sum_mul_sum]
  rfl

theorem rpow_two_mul {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) :
    ENNReal.ofReal (x ^ 2) ^ r = ENNReal.ofReal (x ^ (2 * r)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hr, ← Real.rpow_natCast,
    ← Real.rpow_mul hx]
  norm_num

theorem sqrt_rpow_le {H p : ℝ} (hH : 0 ≤ H) (hp : 1 ≤ p) :
    Real.sqrt H ^ p ≤ 1 + H ^ (max p 2 / 2) := by
  have h := rpow_le_one_add (Real.sqrt_nonneg H) (by linarith : (0 : ℝ) ≤ p) (le_max_left p 2)
  have e : Real.sqrt H ^ max p 2 = H ^ (max p 2 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hH]; ring_nf
  linarith

/-- `V_{kl}^r ≤ E|ξ_k*Gξ'_l|^{2r}` (conditional Jensen). -/
theorem pairV_rpow_le (b E : ℝ) (ω : GrowthPath W) (kl : Fin n × Fin n) {r : ℝ} (hr : 1 ≤ r) :
    ENNReal.ofReal (pairV b E ω kl ^ r) ≤
      ∫⁻ x, ENNReal.ofReal (‖tagY b E kl ω x‖ ^ (2 * r))
        ∂(circularVectorLaw (Fin W)).prod (circularVectorLaw (Fin W)) := by
  have hm : Measurable fun x : (Fin W → ℂ) × (Fin W → ℂ) => ENNReal.ofReal
      (‖tagForm (fullInverse b E W n ω).toBlocks₁₁ (tagVector W n kl.1 1 x.1)
        (tagVector W n kl.2 1 x.2)‖ ^ 2) :=
    ((measurable_tagForm measurable_const ((measurable_tagVector n kl.1 1).comp measurable_fst)
      ((measurable_tagVector n kl.2 1).comp measurable_snd)).norm.pow_const 2).ennreal_ofReal
  rw [← ENNReal.ofReal_rpow_of_nonneg (pairV_nonneg b E ω kl) (by linarith)]
  have e : ENNReal.ofReal (pairV b E ω kl) = ∫⁻ x, ENNReal.ofReal
      (‖tagForm (fullInverse b E W n ω).toBlocks₁₁ (tagVector W n kl.1 1 x.1)
        (tagVector W n kl.2 1 x.2)‖ ^ 2)
        ∂(circularVectorLaw (Fin W)).prod (circularVectorLaw (Fin W)) :=
    (lintegral_tagY_sq _ kl.1 kl.2).symm
  rw [e]
  exact (rpow_lintegral_le _ hm.aemeasurable hr).trans_eq
    (lintegral_congr fun x => rpow_two_mul (norm_nonneg _) (by linarith))

/-- Pointwise in the path: `‖A_Q‖_HS^p ≤ 1 + S^{2(r-1)} Σ_{kl} w_{kl} E|ξ_k*Gξ'_l|^{p'}`. -/
theorem hs_rpow_le (b E : ℝ) (q : Fin n → ℝ) (hq : ∀ k, 0 ≤ q k) (ω : GrowthPath W)
    {p : ℝ} (hp : 1 ≤ p) :
    ENNReal.ofReal (Real.sqrt (∑ x, ∑ y, ‖extendedSourceMatrix b E W n q ω x y‖ ^ 2) ^ p) ≤
      1 + ENNReal.ofReal (((∑ k, q k / W) ^ 2) ^ (max p 2 / 2 - 1)) *
        ∑ kl : Fin n × Fin n, ENNReal.ofReal (pairW W q kl) *
          ∫⁻ x, ENNReal.ofReal (‖tagY b E kl ω x‖ ^ (2 * (max p 2 / 2)))
            ∂(circularVectorLaw (Fin W)).prod (circularVectorLaw (Fin W)) := by
  have hr : 1 ≤ max p 2 / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]; linarith [le_max_right p 2]
  have hw := pairW_nonneg (W := W) q hq
  have hV := pairV_nonneg (n := n) b E ω
  have hJ := weighted_rpow_le Finset.univ (pairW W q) (pairV b E ω) (fun kl _ => hw kl)
    (fun kl _ => hV kl) hr
  rw [sum_pairW] at hJ
  have h0 := sqrt_rpow_le (H := ∑ x, ∑ y, ‖extendedSourceMatrix b E W n q ω x y‖ ^ 2)
    (by positivity) hp
  rw [hs_extended_pairs b E q hq ω] at h0 ⊢
  refine (ENNReal.ofReal_le_ofReal (h0.trans (add_le_add_right hJ 1))).trans ?_
  have hs : 0 ≤ ∑ kl, pairW W q kl * pairV b E ω kl ^ (max p 2 / 2) :=
    Finset.sum_nonneg fun kl _ => mul_nonneg (hw kl) (Real.rpow_nonneg (hV kl) _)
  rw [ENNReal.ofReal_add zero_le_one (mul_nonneg (Real.rpow_nonneg (sq_nonneg _) _) hs),
    ENNReal.ofReal_one, ENNReal.ofReal_mul (Real.rpow_nonneg (sq_nonneg _) _),
    ENNReal.ofReal_sum_of_nonneg fun kl _ => mul_nonneg (hw kl) (Real.rpow_nonneg (hV kl) _)]
  gcongr with kl
  rw [ENNReal.ofReal_mul (hw kl)]
  exact mul_le_mul_right (pairV_rpow_le b E ω kl hr) _

/-- **The Hilbert–Schmidt term**: `E‖A_Q‖_HS^p ≤ 1 + S^{2(r-1)} · S² · C'`, from the two-tag
raw bound at exponent `p' = max(p, 2)` and unit masses. -/
theorem lintegral_hs_le (b E : ℝ) (q : Fin n → ℝ) (hq : ∀ k, 0 ≤ q k) {p C' : ℝ} (hp : 1 ≤ p)
    (hraw : RawTagBoundAt b E W n (max p 2) C') :
    ∫⁻ ω, ENNReal.ofReal (Real.sqrt (∑ x, ∑ y, ‖extendedSourceMatrix b E W n q ω x y‖ ^ 2) ^ p)
      ∂growthPathLaw W b ≤
      1 + ENNReal.ofReal (((∑ k, q k / W) ^ 2) ^ (max p 2 / 2 - 1)) *
        (ENNReal.ofReal ((∑ k, q k / W) ^ 2) * ENNReal.ofReal C') := by
  have : IsProbabilityMeasure (growthPathLaw W b) :=
    Transmission.Bridge.isProbabilityMeasure_growthPathLaw W b
  have e2 : 2 * (max p 2 / 2) = max p 2 := by ring
  have hpt := fun ω : GrowthPath W => hs_rpow_le b E q hq ω hp
  simp_rw [e2] at hpt
  have hF : ∀ kl : Fin n × Fin n, Measurable fun ω => ∫⁻ x, ENNReal.ofReal
      (‖tagY b E kl ω x‖ ^ max p 2) ∂(circularVectorLaw (Fin W)).prod (circularVectorLaw (Fin W)) :=
    fun kl => (measurable_tagY_rpow (W := W) b E kl _).lintegral_prod_right'
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_const_mul _ (Finset.measurable_sum _ fun kl _ => (hF kl).const_mul _),
    lintegral_finsetSum _ fun kl _ => (hF kl).const_mul _]
  refine add_le_add_right (mul_le_mul_right ?_ _) _
  rw [← sum_pairW, ENNReal.ofReal_sum_of_nonneg fun kl _ => pairW_nonneg q hq kl, Finset.sum_mul]
  refine Finset.sum_le_sum fun kl _ => ?_
  rw [lintegral_const_mul _ (hF kl)]
  refine mul_le_mul_right ?_ _
  rw [← lintegral_prod _ (measurable_tagY_rpow b E kl _).aemeasurable]
  have h := (hraw kl.1 kl.2 1 1 zero_le_one zero_le_one).1
  simp only [mul_one, Real.one_rpow] at h
  exact h

end BlockBand.SourceProcess.ComplexSourceLaw
