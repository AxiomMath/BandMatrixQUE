module

public import BlockBand.Palm.RelativeLocalizationBridgeSpec
public import BlockBand.Palm.RelativeLocalizationBridge

/-!
# Relative localization: identification of the generators and pathwise coefficient properties

* `shortGenerator_eq_massGenerator`, `referenceGenerator_eq_massGenerator` (pointwise, `funext`):
  `shortGenerator = massGenerator shortRate 0`, `referenceGenerator = massGenerator shortRate β̂`.
  The diagonal conventions differ only in form (`Σ` over `filter (m ≠ k ∧ |k-m| < ℓ)` against
  `Σ` over `univ.erase k` of rates vanishing on long pairs); no difference in value.
* `NoCollision F a c ω` (`ω.1` Hermitian and simple spectrum at every `σ ∈ [a,c]`) holds
  `flowLaw N a`-a.e. for `a > 0` (`ae_noCollision`).
* On `NoCollision`, the rates and the damping are continuous on `[a,c]`; they are symmetric and
  nonnegative for every sample and every time (`flowRate` is `0` on a collision). No
  modification on the null set is needed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization.StochasticBridge

open MeasureTheory Set BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Transmission (DysonBrownianMotion)
open BlockBand.Palm.RelativeLocalization (flowLam flowLam_eq_at collision_null ae_fst_isHermitian
  flowLam_continuous)

variable {N : ℕ}

/-!
## Identification of the mass equations and generators
-/

theorem forwardMassSolution_eq :
    @ForwardMassSolution N = @BlockBand.Internal.Contracts.TransmissionFlow.ForwardMassSolution N :=
  rfl

theorem backwardPropagator_eq :
    @BackwardPropagator N = @BlockBand.Internal.Contracts.TransmissionFlow.BackwardPropagator N :=
  rfl

theorem sum_erase_shortRate (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (ℓ : ℕ)
    (σ : ℝ) (k : Fin N) :
    ∑ m ∈ Finset.univ.erase k, shortRate F a ω ℓ σ k m =
      ∑ m ∈ Finset.univ.filter (fun m => m ≠ k ∧ labelDist k m < ℓ), flowRate F a ω σ k m := by
  rw [Finset.sum_erase _ (by simp [shortRate]), Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [shortRate, ne_comm]

theorem shortGenerator_eq_massGenerator (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ)
    (ω : FlowSample N) (ℓ : ℕ) :
    shortGenerator F a ω ℓ =
      BlockBand.Internal.Contracts.TransmissionFlow.massGenerator (shortRate F a ω ℓ)
        (fun _ _ => 0) := by
  funext σ k l
  simp only [shortGenerator, BlockBand.Internal.Contracts.TransmissionFlow.massGenerator]
  by_cases hkl : k = l
  · subst hkl
    rw [ite_eq_left rfl, ite_eq_left rfl, sum_erase_shortRate, sub_zero]
  · rw [ite_eq_right hkl, ite_eq_right hkl]
    simp only [shortRate, true_and, hkl, ne_eq, not_false_eq_true]

theorem referenceGenerator_eq_massGenerator (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ)
    (ω : FlowSample N) (ℓ : ℕ) :
    referenceGenerator F a b₀ ω ℓ =
      BlockBand.Internal.Contracts.TransmissionFlow.massGenerator (shortRate F a ω ℓ)
        (refDamping F a b₀ ω ℓ) := by
  funext σ k l
  have h := congrFun (congrFun (congrFun (shortGenerator_eq_massGenerator F a ω ℓ) σ) k) l
  simp only [referenceGenerator, h, BlockBand.Internal.Contracts.TransmissionFlow.massGenerator,
    refDamping]
  by_cases hkl : k = l
  · subst hkl; simp
  · simp [hkl]

/-!
## Pathwise properties of the coefficients
-/

theorem labelDist_comm (k l : Fin N) : labelDist k l = labelDist l k := by
  simp only [labelDist]
  rw [← Int.natAbs_neg, neg_sub]

theorem flowRate_comm (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (σ : ℝ)
    (k l : Fin N) : flowRate F a ω σ k l = flowRate F a ω σ l k := by
  simp only [flowRate]
  congr 2
  ring

theorem flowRate_nonneg' (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (σ : ℝ)
    (k l : Fin N) : 0 ≤ flowRate F a ω σ k l :=
  inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg _))

theorem shortRate_comm (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (ℓ : ℕ)
    (σ : ℝ) (k l : Fin N) : shortRate F a ω ℓ σ k l = shortRate F a ω ℓ σ l k := by
  simp only [shortRate, ne_comm (a := k), labelDist_comm k l, flowRate_comm F a ω σ k l]

theorem shortRate_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (ℓ : ℕ)
    (σ : ℝ) (k l : Fin N) : 0 ≤ shortRate F a ω ℓ σ k l := by
  unfold shortRate
  split_ifs
  · exact flowRate_nonneg' F a ω σ k l
  · exact le_rfl

theorem longCoupling_nonneg' (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (ℓ : ℕ)
    (σ : ℝ) (k : Fin N) : 0 ≤ longCoupling F a ω ℓ σ k := by
  simp only [longCoupling]
  exact Finset.sum_nonneg fun m _ => flowRate_nonneg' F a ω σ k m

theorem refDamping_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ) (ω : FlowSample N) (ℓ : ℕ)
    (σ : ℝ) (k : Fin N) : 0 ≤ refDamping F a b₀ ω ℓ σ k :=
  le_max_of_le_left (longCoupling_nonneg' F a ω ℓ σ k)

/-- No collision on `[a,c]`: `ω.1` is Hermitian and the spectrum of `H_σ` is simple for every
`σ ∈ [a,c]`. -/
def NoCollision (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (ω : FlowSample N) : Prop :=
  ω.1.IsHermitian ∧ ∀ σ ∈ Icc a c, ∀ k l : Fin N, k ≠ l →
    flowEigenvalue F a ω σ k ≠ flowEigenvalue F a ω σ l

/-- **Non-collision on the closed window `[a,c]`, almost surely** (for `a > 0`). -/
theorem ae_noCollision (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∀ᵐ ω ∂flowLaw N a, NoCollision F a c ω := by
  have hpair : ∀ p : Fin N × Fin N, ∀ᵐ ω ∂flowLaw N a, ω.1.IsHermitian → p.1 ≠ p.2 →
      ∀ σ ∈ Icc a c, flowEigenvalue F a ω σ p.1 ≠ flowEigenvalue F a ω σ p.2 := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ae_of_all _ fun _ _ h => absurd hp h
    · rw [ae_iff]
      refine measure_mono_null (fun ω hω => ?_)
        (collision_null hDBM hF ha (Real.toNNReal (c - a)) hp)
      simp only [mem_ofPred_eq, not_imp, not_forall, not_not] at hω
      obtain ⟨hH, -, σ, hσ, heq⟩ := hω
      refine mem_iInter.mpr fun n => ⟨Real.toNNReal (σ - a), ?_, ?_⟩
      · exact Real.toNNReal_le_toNNReal (by linarith [hσ.2])
      · rw [← flowLam_eq_at hσ.1 hH, heq, sub_self, abs_zero]
        positivity
  filter_upwards [ae_fst_isHermitian (N := N) a, ae_all_iff.mpr hpair] with ω hH h
  exact ⟨hH, fun σ hσ k l hkl => h (k, l) hH hkl σ hσ⟩

theorem continuousOn_flowEigenvalue {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {ω : FlowSample N} (hH : ω.1.IsHermitian) (a c : ℝ) (k : Fin N) :
    ContinuousOn (fun σ => flowEigenvalue F a ω σ k) (Icc a c) := by
  have hc : Continuous fun σ : ℝ => flowLam F (Real.toNNReal (σ - a)) ω k :=
    (continuous_apply k).comp ((flowLam_continuous hF ω).comp
      (continuous_real_toNNReal.comp (continuous_id.sub continuous_const)))
  exact hc.continuousOn.congr fun σ hσ => congrFun (flowLam_eq_at hσ.1 hH) k

theorem continuousOn_flowRate {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ}
    {ω : FlowSample N} (hω : NoCollision F a c ω) (k l : Fin N) :
    ContinuousOn (fun σ => flowRate F a ω σ k l) (Icc a c) := by
  by_cases hkl : k = l
  · subst hkl
    simpa [flowRate] using continuousOn_const
  · refine ContinuousOn.inv₀ (continuousOn_const.mul
      (((continuousOn_flowEigenvalue hF hω.1 a c k).sub
        (continuousOn_flowEigenvalue hF hω.1 a c l)).pow 2)) fun σ hσ => ?_
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Fin.pos k)
    exact mul_ne_zero hN.ne' (pow_ne_zero 2 (sub_ne_zero.mpr (hω.2 σ hσ k l hkl)))

theorem continuousOn_shortRate {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ}
    {ω : FlowSample N} (hω : NoCollision F a c ω) (ℓ : ℕ) :
    ContinuousOn (shortRate F a ω ℓ) (Icc a c) := by
  refine continuousOn_pi.mpr fun k => continuousOn_pi.mpr fun l => ?_
  by_cases h : k ≠ l ∧ labelDist k l < ℓ
  · simp only [shortRate, ite_eq_left h]
    exact continuousOn_flowRate hF hω k l
  · simp only [shortRate, ite_eq_right h]
    exact continuousOn_const

theorem continuousOn_refDamping {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ}
    {ω : FlowSample N} (hω : NoCollision F a c ω) (b₀ : ℝ) (ℓ : ℕ) :
    ContinuousOn (refDamping F a b₀ ω ℓ) (Icc a c) := by
  refine continuousOn_pi.mpr fun k => ?_
  simp only [refDamping, longCoupling]
  exact ContinuousOn.sup (continuousOn_finsetSum _ fun m _ => continuousOn_flowRate hF hω k m)
    continuousOn_const

end BlockBand.Palm.RelativeLocalization.StochasticBridge
