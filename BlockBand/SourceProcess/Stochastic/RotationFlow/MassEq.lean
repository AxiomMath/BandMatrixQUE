module
public import BlockBand.SourceProcess.Stochastic.RotationFlow.Mass
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The integrated mass equation

Notation as for `secondMoment`. `secondMoment_eq`: for a rotation flow `M` started at `s` and all
`t ≥ 0`, `m_t(k,j) = δ_kj + ∫_{(0,t]} ∑_l L(u)_kl m_u(l,j) du`, with
`L(u) = massGenerator r κ (clampTime a c (s + u⁺))`.
-/

namespace BlockBand.SourceProcess.Stochastic.RotationFlow
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.Stochastic.NativeSDE BlockBand.SourceProcess.Stochastic.Integral
open BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.Internal.Contracts.TransmissionFlow

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace

variable {N : ℕ} {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
variable {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ} {a c s : ℝ}

/-- The generator along the flow time, as a jointly continuous function of `(t, Y)`. -/
theorem continuous_entryDrift (hac : a ≤ c) (hrc : ContinuousOn r (Set.Icc a c))
    (hκc : ContinuousOn κ (Set.Icc a c)) (k j : Fin N) :
    Continuous fun q : ℝ≥0 × Matrix (Fin N) (Fin N) ℂ =>
      ∑ l, massGenerator r κ (clampTime a c (s + q.1)) k l * ‖q.2 l j‖ ^ 2 := by
  have hL := continuous_clamped hac (continuousOn_massGenerator hrc hκc) s
  refine continuous_finsetSum _ fun l _ => ?_
  have h1 : Continuous fun q : ℝ≥0 × Matrix (Fin N) (Fin N) ℂ =>
      massGenerator r κ (clampTime a c (s + q.1)) k l :=
    (continuous_apply l).comp ((continuous_apply k).comp (hL.comp continuous_fst))
  exact h1.mul ((continuous_entry_sq l j).comp continuous_snd)

theorem continuous_entryNoise (hac : a ≤ c) (hrc : ContinuousOn r (Set.Icc a c)) (k j : Fin N)
    (α : (Fin N × Fin N) × Fin 2) :
    Continuous fun q : ℝ≥0 × Matrix (Fin N) (Fin N) ℂ =>
      entryForm k j (noiseAt r a c s α q.1 * q.2) q.2 +
        entryForm k j q.2 (noiseAt r a c s α q.1 * q.2) := by
  have h1 := continuous_noiseCoeff (s := s) hac hrc α
  exact (((entryForm k j).continuous.comp h1).clm_apply continuous_snd).add
    (((entryForm k j).continuous.comp continuous_snd).clm_apply h1)

/-- **Integrated mass equation.** -/
theorem secondMoment_eq (hac : a ≤ c) (hrc : ContinuousOn r (Set.Icc a c))
    (hκc : ContinuousOn κ (Set.Icc a c)) (hs : ∀ x k l, r x k l = r x l k)
    (hr : ∀ x k l, 0 ≤ r x k l) (hk : ∀ x k, 0 ≤ κ x k)
    {M : ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ} (hM : IsRotationFlow μ r κ a c s M)
    (t : ℝ≥0) (k j : Fin N) :
    secondMoment μ M t k j = (if k = j then 1 else 0) +
      ∫ u in Ioc (0 : ℝ) t, ∑ l, massGenerator r κ (clampTime a c (s + u.toNNReal)) k l *
        secondMoment μ M u.toNNReal l j := by
  obtain ⟨K, hK0, hK⟩ := exists_coeff_bound hac hrc hκc
  obtain ⟨KL, hKL0, hKL⟩ := exists_massGenerator_bound hrc hκc
  have hb := isRotationFlow_norm_le hs hr hk hM
  set P := driverLaw (κ := (Fin N × Fin N) × Fin 2) μ
  set one : ℝ := ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖
  have hP := ItoNative.itoProductRuleFor_holds (κ := (Fin N × Fin N) × Fin 2) μ
    (E := Matrix (Fin N) (Fin N) ℂ) (F := Matrix (Fin N) (Fin N) ℂ) (G := ℝ) _ _ _ _ _ _ hM.1 hM.1
    (entryForm k j)
  have hP' : IsNativeItoProcess μ (fun (t : ℝ≥0) (x : FlowSample S N) => ‖M t x k j‖ ^ 2)
      (fun (t : ℝ≥0) (x : FlowSample S N) =>
        ∑ l, massGenerator r κ (clampTime a c (s + t)) k l * ‖M t x l j‖ ^ 2)
      (fun α (t : ℝ≥0) (x : FlowSample S N) =>
        entryForm k j (rotationNoise (r (clampTime a c (s + t))) α * M t x) (M t x) +
          entryForm k j (M t x) (rotationNoise (r (clampTime a c (s + t))) α * M t x)) := by
    convert hP using 1
    · funext t x
      exact (entryForm_self k j (M t x)).symm
    · funext t x
      exact (entry_drift_eq_massGenerator r κ _ (hs _) (hr _) _ k j).symm
  set ℓ : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ
  have hG := nativeIntegrand_coeffF_ae (μ := μ)
    (σ := fun α (t : ℝ≥0) (Y : Matrix (Fin N) (Fin N) ℂ) =>
      entryForm k j (noiseAt r a c s α t * Y) Y + entryForm k j Y (noiseAt r a c s α t * Y))
    (continuous_entryNoise hac hrc k j) hM.1.adapted hM.1.continuous
    (C := 2 * ‖entryForm k j‖ * (K * one) * one) (by
      filter_upwards [hb] with x hx α u
      have hn : ‖noiseAt r a c s α u * M u x‖ ≤ K * one :=
        (frobenius_norm_mul _ _).trans (mul_le_mul ((hK s u).2 α) (hx u) (norm_nonneg _) hK0)
      refine (norm_add_le _ _).trans ?_
      have h1 := (entryForm k j).le_opNorm₂ (noiseAt r a c s α u * M u x) (M u x)
      have h2 := (entryForm k j).le_opNorm₂ (M u x) (noiseAt r a c s α u * M u x)
      have hβ := norm_nonneg (entryForm k j)
      have h3 : ‖entryForm k j‖ * ‖noiseAt r a c s α u * M u x‖ * ‖M u x‖ ≤
          ‖entryForm k j‖ * (K * one) * one :=
        mul_le_mul (mul_le_mul_of_nonneg_left hn hβ) (hx u) (norm_nonneg _)
          (mul_nonneg hβ (mul_nonneg hK0 (norm_nonneg _)))
      have h4 : ‖entryForm k j‖ * ‖M u x‖ * ‖noiseAt r a c s α u * M u x‖ ≤
          ‖entryForm k j‖ * (K * one) * one := by
        calc _ = ‖entryForm k j‖ * ‖noiseAt r a c s α u * M u x‖ * ‖M u x‖ := by ring
          _ ≤ _ := h3
      linarith) ℓ t
  obtain ⟨hs', hid⟩ := hP'.identity ℓ (fun _ => ⊤) isStoppingTime_top t hG t le_rfl
  set F : ℝ × FlowSample S N → ℝ := fun p =>
    ∑ l, massGenerator r κ (clampTime a c (s + p.1.toNNReal)) k l * ‖M p.1.toNNReal p.2 l j‖ ^ 2
    with hFdef
  have hD : ∀ x, stoppedDrift (fun _ => ⊤) (fun (t : ℝ≥0) (x : FlowSample S N) =>
      ∑ l, massGenerator r κ (clampTime a c (s + t)) k l * ‖M t x l j‖ ^ 2) t x =
      ∫ u in Ioc (0 : ℝ) t, F (u, x) := fun x => by
    unfold stoppedDrift
    simp only [le_top, ite_true, hFdef]
  have hFm : AEStronglyMeasurable F (timeProbMeasure t P) :=
    ((continuous_entryDrift (s := s) hac hrc hκc k j).comp_aestronglyMeasurable
      (aesm_clock.prodMk (aesm_processFun hM.1.adapted hM.1.continuous))).mono
      (predictableSpace_le _)
  have hFb : ∀ᵐ p ∂timeProbMeasure t P, ‖F p‖ ≤ Fintype.card (Fin N) * (KL * one ^ 2) := by
    filter_upwards [ae_timeProb_of_ae (T := t) hb] with p hp
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => KL * one ^ 2) fun l _ => ?_).trans
      (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])
    simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_norm]
    exact mul_le_mul (hKL _ (clampTime_mem hac _) k l)
      (pow_le_pow_left₀ (norm_nonneg _) ((norm_entry_le _ l j).trans (hp _)) 2)
      (sq_nonneg _) hKL0
  have hFint : Integrable F (timeProbMeasure t P) := Integrable.of_bound hFm _ hFb
  have hFint' : Integrable F ((volume.restrict (Ioc (0 : ℝ) t)).prod P) := hFint
  have hsq := fun u : ℝ≥0 => fun l : Fin N => integrable_entry_sq hM.1.adapted hb u l j
  -- expectation of the identity
  have hzero := integral_nativeIntegralOf_eq_zero hs'
  have hcongr : ∫ x, (‖M t x k j‖ ^ 2 - ‖M 0 x k j‖ ^ 2 - ∫ u in Ioc (0 : ℝ) t, F (u, x)) ∂P =
      ∫ x, (nativeIntegralOf hs' : FlowSample S N → ℝ) x ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hid] with x hx
    rw [← hx, hD x]
    simp only [ℓ, ContinuousLinearMap.id_apply]
    rw [stoppedProcess_eq_of_le (τ := fun _ : FlowSample S N => (⊤ : WithTop ℝ≥0)) le_top]
  have hA : Integrable (fun x => ‖M t x k j‖ ^ 2 - ‖M 0 x k j‖ ^ 2) P := (hsq t k).sub (hsq 0 k)
  have hC : Integrable (fun x => ∫ u in Ioc (0 : ℝ) t, F (u, x)) P := hFint'.integral_prod_right
  rw [hzero, integral_sub hA hC, integral_sub (hsq t k) (hsq 0 k)] at hcongr
  have h0 : ∫ x, ‖M 0 x k j‖ ^ 2 ∂P = if k = j then 1 else 0 := secondMoment_zero hM.2 k j
  have hF : ∫ x, (∫ u in Ioc (0 : ℝ) t, F (u, x)) ∂P =
      ∫ u in Ioc (0 : ℝ) t, ∑ l, massGenerator r κ (clampTime a c (s + u.toNNReal)) k l *
        secondMoment μ M u.toNNReal l j := by
    rw [← integral_prod_symm F hFint', integral_prod F hFint']
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    simp only [hFdef, secondMoment]
    rw [integral_finsetSum _ fun l _ => (hsq _ l).const_mul _]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact integral_const_mul _ _
  rw [h0, hF] at hcongr
  have hm : secondMoment μ M t k j = ∫ x, ‖M t x k j‖ ^ 2 ∂P := rfl
  rw [hm]
  linarith

end BlockBand.SourceProcess.Stochastic.RotationFlow
