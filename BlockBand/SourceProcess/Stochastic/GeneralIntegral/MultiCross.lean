module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.BracketElem
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Cross increments of two martingales with a given cross bracket

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖`; `X, Y` two `𝓖`-martingales in
`L²(Q)` at every time, `B` an integrable process and `K` a `𝓖`-martingale with
`K_t = X_t Y_t - B_t` a.s. (so `⟨X, Y⟩ = B`; no sign or symmetry assumption).

* `setIntegral_cross_same`: `∫_D (X_b - X_a)(Y_b - Y_a) = ∫_D (B_b - B_a)` for `D ∈ 𝓖_a`.
* `setIntegral_cross_incr` (asymmetric increment covariance): for `a₁ ≤ b₁`, `a₂ ≤ b₂`,
  `D ∈ 𝓖_{a₁ ∨ a₂}`,
  `∫_D (X_{b₁} - X_{a₁})(Y_{b₂} - Y_{a₂}) = ∫_D (B_{c ∨ d} - B_c)`, `c = a₁ ∨ a₂`,
  `d = b₁ ∧ b₂` (zero when the intervals do not overlap). This is the rectangle-level
  input of the cross isometry `E[∫H dN^i ∫K dN^j] = E ∫ H K a_ij` (the scalar case is
  `IsL2Integrator.setIntegral_incr_mul_incr`).
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
  {𝓖 : Filtration ℝ≥0 mΩ}

/-- Hypotheses of a pair of `L²` martingales with cross bracket `B`. -/
structure CrossPair (Q : Measure Ω) (𝓖 : Filtration ℝ≥0 mΩ) (X Y B : ℝ≥0 → Ω → ℝ) : Prop where
  martX : Martingale X 𝓖 Q
  martY : Martingale Y 𝓖 Q
  memX : ∀ t, MemLp (X t) 2 Q
  memY : ∀ t, MemLp (Y t) 2 Q
  intB : ∀ t, Integrable (B t) Q
  cross : ∃ K : ℝ≥0 → Ω → ℝ, Martingale K 𝓖 Q ∧ ∀ t, K t =ᵐ[Q] fun ω => X t ω * Y t ω - B t ω

namespace CrossPair

variable {X Y B : ℝ≥0 → Ω → ℝ}

omit [IsFiniteMeasure Q] in
theorem symm (h : CrossPair Q 𝓖 X Y B) : CrossPair Q 𝓖 Y X B := by
  obtain ⟨K, hK, hKe⟩ := h.cross
  exact ⟨h.martY, h.martX, h.memY, h.memX, h.intB, K, hK, fun t => (hKe t).trans
    (Eventually.of_forall fun ω => by simp only [mul_comm])⟩

/-- **Cross bracket of one increment.** -/
theorem setIntegral_cross_same (h : CrossPair Q 𝓖 X Y B) {a b : ℝ≥0} (hab : a ≤ b)
    {D : Set Ω} (hD : MeasurableSet[𝓖 a] D) :
    ∫ ω in D, (X b ω - X a ω) * (Y b ω - Y a ω) ∂Q = ∫ ω in D, (B b ω - B a ω) ∂Q := by
  obtain ⟨K, hK, hKe⟩ := h.cross
  have hDm : MeasurableSet D := 𝓖.le a D hD
  have e1 : ∫ ω in D, (X b ω * Y b ω - B b ω) ∂Q = ∫ ω in D, (X a ω * Y a ω - B a ω) ∂Q := by
    rw [← setIntegral_congr_ae hDm ((hKe a).mono fun ω h _ => h),
      ← setIntegral_congr_ae hDm ((hKe b).mono fun ω h _ => h)]
    exact (hK.setIntegral_eq hab hD).symm
  have e2 := setIntegral_mul_sub_eq_zero h.martY hab (h.memY b) hD (h.memX a)
    (h.martX.stronglyMeasurable a).aestronglyMeasurable
  have e3 := setIntegral_mul_sub_eq_zero h.martX hab (h.memX b) hD (h.memY a)
    (h.martY.stronglyMeasurable a).aestronglyMeasurable
  have i1 : Integrable (fun ω => X b ω * Y b ω - B b ω) Q :=
    ((h.memX b).integrable_mul (h.memY b)).sub (h.intB b)
  have i2 : Integrable (fun ω => X a ω * Y a ω - B a ω) Q :=
    ((h.memX a).integrable_mul (h.memY a)).sub (h.intB a)
  have i3 : Integrable (fun ω => B b ω - B a ω) Q := (h.intB b).sub (h.intB a)
  have i4 : Integrable (fun ω => X a ω * (Y b ω - Y a ω)) Q :=
    (h.memX a).integrable_mul ((h.memY b).sub (h.memY a))
  have i5 : Integrable (fun ω => Y a ω * (X b ω - X a ω)) Q :=
    (h.memY a).integrable_mul ((h.memX b).sub (h.memX a))
  have hexp : (fun ω => (X b ω - X a ω) * (Y b ω - Y a ω)) = fun ω =>
      ((X b ω * Y b ω - B b ω) - (X a ω * Y a ω - B a ω) + (B b ω - B a ω)) -
        (X a ω * (Y b ω - Y a ω)) - (Y a ω * (X b ω - X a ω)) := by
    funext ω; ring
  have j1 : Integrable (fun ω => (X b ω * Y b ω - B b ω) - (X a ω * Y a ω - B a ω)) Q :=
    i1.sub i2
  have j2 : Integrable (fun ω => (X b ω * Y b ω - B b ω) - (X a ω * Y a ω - B a ω) +
      (B b ω - B a ω)) Q := j1.add i3
  have j3 : Integrable (fun ω => (X b ω * Y b ω - B b ω) - (X a ω * Y a ω - B a ω) +
      (B b ω - B a ω) - X a ω * (Y b ω - Y a ω)) Q := j2.sub i4
  rw [hexp, integral_sub j3.integrableOn i5.integrableOn,
    integral_sub j2.integrableOn i4.integrableOn,
    integral_add j1.integrableOn i3.integrableOn,
    integral_sub i1.integrableOn i2.integrableOn, e1, e2, e3]
  ring

omit [IsFiniteMeasure Q] in
theorem memLp_incrX (h : CrossPair Q 𝓖 X Y B) (a b : ℝ≥0) :
    MemLp (fun ω => X b ω - X a ω) 2 Q := (h.memX b).sub (h.memX a)

omit [IsFiniteMeasure Q] in
theorem aesm_incrX (h : CrossPair Q 𝓖 X Y B) {a b c : ℝ≥0} (ha : a ≤ c) (hb : b ≤ c) :
    AEStronglyMeasurable[𝓖 c] (fun ω => X b ω - X a ω) Q :=
  (((h.martX.stronglyMeasurable b).mono (𝓖.mono hb)).sub
    ((h.martX.stronglyMeasurable a).mono (𝓖.mono ha))).aestronglyMeasurable

/-- Two increments from a common left endpoint. -/
theorem setIntegral_cross_common (h : CrossPair Q 𝓖 X Y B) {a b₁ b₂ : ℝ≥0}
    (h₁ : a ≤ b₁) (h₂ : a ≤ b₂) {D : Set Ω} (hD : MeasurableSet[𝓖 a] D) :
    ∫ ω in D, (X b₁ ω - X a ω) * (Y b₂ ω - Y a ω) ∂Q =
      ∫ ω in D, (B (min b₁ b₂) ω - B a ω) ∂Q := by
  rcases le_total b₁ b₂ with hle | hle
  · have hD1 : MeasurableSet[𝓖 b₁] D := 𝓖.mono h₁ D hD
    have e0 := setIntegral_mul_sub_eq_zero h.martY hle (h.memY b₂) hD1 (h.memLp_incrX a b₁)
      (h.aesm_incrX h₁ le_rfl)
    have hsplit : (fun ω => (X b₁ ω - X a ω) * (Y b₂ ω - Y a ω)) =
        fun ω => (X b₁ ω - X a ω) * (Y b₁ ω - Y a ω) + (X b₁ ω - X a ω) * (Y b₂ ω - Y b₁ ω) := by
      funext ω; ring
    have i1 : Integrable (fun ω => (X b₁ ω - X a ω) * (Y b₁ ω - Y a ω)) Q :=
      (h.memLp_incrX a b₁).integrable_mul ((h.memY b₁).sub (h.memY a))
    have i2 : Integrable (fun ω => (X b₁ ω - X a ω) * (Y b₂ ω - Y b₁ ω)) Q :=
      (h.memLp_incrX a b₁).integrable_mul ((h.memY b₂).sub (h.memY b₁))
    rw [hsplit, integral_add i1.integrableOn i2.integrableOn, e0, add_zero, min_eq_left hle,
      h.setIntegral_cross_same h₁ hD]
  · have hs := h.symm
    have hD2 : MeasurableSet[𝓖 b₂] D := 𝓖.mono h₂ D hD
    have e0 := setIntegral_mul_sub_eq_zero h.martX hle (h.memX b₁) hD2 (hs.memLp_incrX a b₂)
      (hs.aesm_incrX h₂ le_rfl)
    have hsplit : (fun ω => (X b₁ ω - X a ω) * (Y b₂ ω - Y a ω)) =
        fun ω => (Y b₂ ω - Y a ω) * (X b₂ ω - X a ω) + (Y b₂ ω - Y a ω) * (X b₁ ω - X b₂ ω) := by
      funext ω; ring
    have i1 : Integrable (fun ω => (Y b₂ ω - Y a ω) * (X b₂ ω - X a ω)) Q :=
      (hs.memLp_incrX a b₂).integrable_mul ((h.memX b₂).sub (h.memX a))
    have i2 : Integrable (fun ω => (Y b₂ ω - Y a ω) * (X b₁ ω - X b₂ ω)) Q :=
      (hs.memLp_incrX a b₂).integrable_mul ((h.memX b₁).sub (h.memX b₂))
    rw [hsplit, integral_add i1.integrableOn i2.integrableOn, e0, add_zero, min_eq_right hle,
      hs.setIntegral_cross_same h₂ hD]

/-- **Asymmetric increment covariance** for a cross pair. -/
theorem setIntegral_cross_incr (h : CrossPair Q 𝓖 X Y B) {a₁ b₁ a₂ b₂ : ℝ≥0}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) {D : Set Ω} (hD : MeasurableSet[𝓖 (max a₁ a₂)] D) :
    ∫ ω in D, (X b₁ ω - X a₁ ω) * (Y b₂ ω - Y a₂ ω) ∂Q =
      ∫ ω in D, (B (max (max a₁ a₂) (min b₁ b₂)) ω - B (max a₁ a₂) ω) ∂Q := by
  rcases le_total a₁ a₂ with hle | hle
  · rw [max_eq_right hle] at hD ⊢
    by_cases hb : b₁ ≤ a₂
    · have e0 := setIntegral_mul_sub_eq_zero h.martY h₂ (h.memY b₂) hD (h.memLp_incrX a₁ b₁)
        (h.aesm_incrX (h₁.trans hb) hb)
      rw [max_eq_left ((min_le_left _ _).trans hb)]
      simp only [sub_self, integral_zero]
      exact e0
    · have hlt : a₂ ≤ b₁ := (lt_of_not_ge hb).le
      have e0 := setIntegral_mul_sub_eq_zero h.martY h₂ (h.memY b₂) hD (h.memLp_incrX a₁ a₂)
        (h.aesm_incrX hle le_rfl)
      have hsplit : (fun ω => (X b₁ ω - X a₁ ω) * (Y b₂ ω - Y a₂ ω)) =
          fun ω => (X a₂ ω - X a₁ ω) * (Y b₂ ω - Y a₂ ω) +
            (X b₁ ω - X a₂ ω) * (Y b₂ ω - Y a₂ ω) := by
        funext ω; ring
      have i1 : Integrable (fun ω => (X a₂ ω - X a₁ ω) * (Y b₂ ω - Y a₂ ω)) Q :=
        (h.memLp_incrX a₁ a₂).integrable_mul ((h.memY b₂).sub (h.memY a₂))
      have i2 : Integrable (fun ω => (X b₁ ω - X a₂ ω) * (Y b₂ ω - Y a₂ ω)) Q :=
        (h.memLp_incrX a₂ b₁).integrable_mul ((h.memY b₂).sub (h.memY a₂))
      rw [hsplit, integral_add i1.integrableOn i2.integrableOn, e0, zero_add,
        h.setIntegral_cross_common hlt h₂ hD, max_eq_right (le_min hlt h₂)]
  · have hs := h.symm
    rw [max_eq_left hle] at hD ⊢
    have hswap : (fun ω => (X b₁ ω - X a₁ ω) * (Y b₂ ω - Y a₂ ω)) =
        fun ω => (Y b₂ ω - Y a₂ ω) * (X b₁ ω - X a₁ ω) := by
      funext ω; ring
    by_cases hb : b₂ ≤ a₁
    · have e0 := setIntegral_mul_sub_eq_zero h.martX h₁ (h.memX b₁) hD (hs.memLp_incrX a₂ b₂)
        (hs.aesm_incrX (h₂.trans hb) hb)
      rw [max_eq_left ((min_le_right _ _).trans hb), hswap]
      simp only [sub_self, integral_zero]
      exact e0
    · have hlt : a₁ ≤ b₂ := (lt_of_not_ge hb).le
      have e0 := setIntegral_mul_sub_eq_zero h.martX h₁ (h.memX b₁) hD (hs.memLp_incrX a₂ a₁)
        (hs.aesm_incrX hle le_rfl)
      have hsplit : (fun ω => (X b₁ ω - X a₁ ω) * (Y b₂ ω - Y a₂ ω)) =
          fun ω => (Y a₁ ω - Y a₂ ω) * (X b₁ ω - X a₁ ω) +
            (X b₁ ω - X a₁ ω) * (Y b₂ ω - Y a₁ ω) := by
        funext ω; ring
      have i1 : Integrable (fun ω => (Y a₁ ω - Y a₂ ω) * (X b₁ ω - X a₁ ω)) Q :=
        (hs.memLp_incrX a₂ a₁).integrable_mul ((h.memX b₁).sub (h.memX a₁))
      have i2 : Integrable (fun ω => (X b₁ ω - X a₁ ω) * (Y b₂ ω - Y a₁ ω)) Q :=
        (h.memLp_incrX a₁ b₁).integrable_mul ((h.memY b₂).sub (h.memY a₁))
      rw [hsplit, integral_add i1.integrableOn i2.integrableOn, e0, zero_add,
        h.setIntegral_cross_common h₁ hlt hD, max_eq_right (le_min h₁ hlt)]

end CrossPair

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
