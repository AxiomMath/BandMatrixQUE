module
public import BlockBand.SourceProcess.Stochastic.SDE.NativeUniqueStep
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Stopped pathwise uniqueness by Gronwall

`Ω = DriverSample S κ`, `P = driverLaw μ`, augmented filtration `F_t ∨ N`, horizon `T`,
augmented stopping time `ρ`.

`stoppedProcess_ae_eq_of_lipschitz`: let `X, Y` be augmented-adapted with a.s. continuous
paths, `X_0 = Y_0` a.s., satisfying the identities (`StoppedIdentity`) with drifts
`β, β'` and diffusions `γ, γ'` up to `ρ` on `[0,T]`. If on `{0 < s ≤ ρ}` the coefficients
are bounded by `C` and `K`-Lipschitz along the two paths
(`‖β_s − β'_s‖, ‖γ_{a,s} − γ'_{a,s}‖ ≤ K ‖X_s − Y_s‖`), then `X_{t∧ρ} = Y_{t∧ρ}` a.s. for
every `t ≤ T`.

Proof: with `Ψ(s) = E[1{s ≤ ρ} ‖X_s − Y_s‖²]` and coordinates `ℓ_j` of a basis,
`Ψ(s) ≤ C_E ∑_j E|ℓ_j(X_{s∧ρ} − Y_{s∧ρ})|² ≤ L ∫_0^s Ψ` (`lintegral_sq_functional_sub_le`
with `H = K ‖X − Y‖ 1{s ≤ ρ}`), `Ψ` is bounded (same lemma with `H = 2C`), hence `Ψ = 0`
(`eq_zero_of_lintegral_volterra`), and then every coordinate difference vanishes.
-/

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem timeProbMeasure_univ (t : ℝ≥0) :
    timeProbMeasure t (driverLaw (κ := κ) μ) univ = ENNReal.ofReal t := by
  unfold timeProbMeasure
  rw [← univ_prod_univ, Measure.prod_prod, measure_univ (μ := driverLaw (κ := κ) μ), mul_one,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc, sub_zero]

/-- **Stopped uniqueness for Lipschitz-along-paths coefficients.** -/
theorem stoppedProcess_ae_eq_of_lipschitz {T : ℝ≥0} {ρ : DriverSample S κ → WithTop ℝ≥0}
    (hρ : IsStoppingTime (driverAugmented (κ := κ) μ) ρ)
    {X Y β β' : ℝ≥0 → DriverSample S κ → E} {γ γ' : κ → ℝ≥0 → DriverSample S κ → E}
    (hXa : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (X t))
    (hYa : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (Y t))
    (hXc : ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => X t x)
    (hYc : ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => Y t x)
    (h0 : ∀ᵐ x ∂driverLaw (κ := κ) μ, X 0 x = Y 0 x)
    (hX : StoppedIdentity μ T ρ X β γ) (hY : StoppedIdentity μ T ρ Y β' γ') {K C : ℝ}
    (hlip : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ x →
      ‖β s x - β' s x‖ ≤ K * ‖X s x - Y s x‖ ∧ ∀ a, ‖γ a s x - γ' a s x‖ ≤ K * ‖X s x - Y s x‖)
    (hbd : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ x →
      ‖β s x‖ ≤ C ∧ ‖β' s x‖ ≤ C ∧ ∀ a, ‖γ a s x‖ ≤ C ∧ ‖γ' a s x‖ ≤ C)
    (hβ : ∀ᵐ x ∂driverLaw (κ := κ) μ,
      AEStronglyMeasurable (fun s : ℝ => β s.toNNReal x) (volume.restrict (Ioc 0 (T : ℝ))))
    (hβ' : ∀ᵐ x ∂driverLaw (κ := κ) μ,
      AEStronglyMeasurable (fun s : ℝ => β' s.toNNReal x) (volume.restrict (Ioc 0 (T : ℝ)))) :
    ∀ t ≤ T, stoppedProcess X ρ t =ᵐ[driverLaw (κ := κ) μ] stoppedProcess Y ρ t := by
  classical
  set Z : ℝ≥0 → DriverSample S κ → E := fun t x => X t x - Y t x with hZdef
  have hZa : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (Z t) := fun t =>
    (hXa t).sub (hYa t)
  have hZc : ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => Z t x := by
    filter_upwards [hXc, hYc] with x h1 h2
    exact h1.sub h2
  set F : ℝ × DriverSample S κ → ℝ≥0∞ := fun p => ‖stoppedFun ρ Z p‖ₑ with hFdef
  have hFm : AEMeasurable F (timeProbMeasure T (driverLaw (κ := κ) μ)) :=
    ((aesm_stoppedFun (T := T) hZa hZc hρ).mono (predictableSpace_le _)).enorm
  have hFpath : ∀ᵐ x ∂driverLaw (κ := κ) μ,
      AEMeasurable (fun s : ℝ => F (s, x)) (volume.restrict (Ioc 0 (T : ℝ))) := by
    filter_upwards [hZc] with x hx
    refine Measurable.aemeasurable ?_
    refine Measurable.enorm ?_
    refine Measurable.ite (measurableSet_toNNReal_le (ρ x)) ?_ measurable_const
    exact (hx.comp continuous_real_toNNReal).measurable
  have hFeq : ∀ x (s : ℝ≥0), (s : WithTop ℝ≥0) ≤ ρ x → F ((s : ℝ), x) = ‖Z s x‖ₑ := by
    intro x s hs
    simp only [hFdef, stoppedFun, Real.toNNReal_coe, hs, ite_true]
  -- the two dominations
  have hdom₁ : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ x →
      ‖β s x - β' s x‖ₑ ≤ ENNReal.ofReal K * F ((s : ℝ), x) ∧
        ∀ a, ‖γ a s x - γ' a s x‖ₑ ≤ ENNReal.ofReal K * F ((s : ℝ), x) := by
    filter_upwards [hlip] with x hx s hs0 hs
    rw [hFeq x s hs, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul' (norm_nonneg _)]
    refine ⟨ENNReal.ofReal_le_ofReal (hx s hs0 hs).1, fun a => ?_⟩
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((hx s hs0 hs).2 a)
  have hdom₂ : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ x →
      ‖β s x - β' s x‖ₑ ≤ ENNReal.ofReal (2 * C) ∧
        ∀ a, ‖γ a s x - γ' a s x‖ₑ ≤ ENNReal.ofReal (2 * C) := by
    filter_upwards [hbd] with x hx s hs0 hs
    obtain ⟨h1, h2, h3⟩ := hx s hs0 hs
    refine ⟨?_, fun a => ?_⟩
    · rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans (by linarith))
    · rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans (by linarith [(h3 a).1, (h3 a).2]))
  have hbdβ : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ x →
      ‖β s x‖ ≤ C ∧ ‖β' s x‖ ≤ C := by
    filter_upwards [hbd] with x hx s hs0 hs
    exact ⟨(hx s hs0 hs).1, (hx s hs0 hs).2.1⟩
  -- per-coordinate bounds
  set ℓ : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ := coordCLM E
  set Φ : ℝ≥0 → Fin (Module.finrank ℝ E) → ℝ≥0∞ := fun t j =>
    ∫⁻ x, ‖ℓ j (stoppedProcess X ρ t x) - ℓ j (stoppedProcess Y ρ t x)‖ₑ ^ 2
      ∂driverLaw (κ := κ) μ with hΦdef
  set L₀ : Fin (Module.finrank ℝ E) → ℝ≥0∞ := fun j =>
    2 * ‖ℓ j‖ₑ ^ 2 * (ENNReal.ofReal T + Fintype.card κ)
  have hL₀ : ∀ j, L₀ j ≠ ⊤ := fun j =>
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top enorm_ne_top))
      (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.natCast_ne_top _⟩)
  have hΦlip : ∀ t ≤ T, ∀ j, Φ t j ≤ L₀ j * ENNReal.ofReal K ^ 2 *
      ∫⁻ p, F p ^ 2 ∂timeProbMeasure t (driverLaw (κ := κ) μ) := by
    intro t ht j
    have h := lintegral_sq_functional_sub_le h0 hX hY hbdβ hβ hβ'
      (hFm.const_mul (ENNReal.ofReal K)) (by
        filter_upwards [hFpath] with x hx
        exact hx.const_mul _) hdom₁ (ℓ j) ht
    refine h.trans ?_
    simp only [mul_pow]
    rw [lintegral_const_mul' _ _ (by simp)]
    have hle : ENNReal.ofReal t ≤ ENNReal.ofReal T := ENNReal.ofReal_le_ofReal (by exact_mod_cast ht)
    calc 2 * ‖ℓ j‖ₑ ^ 2 * (ENNReal.ofReal t + Fintype.card κ) *
          (ENNReal.ofReal K ^ 2 * ∫⁻ p, F p ^ 2 ∂timeProbMeasure t (driverLaw (κ := κ) μ))
        ≤ 2 * ‖ℓ j‖ₑ ^ 2 * (ENNReal.ofReal T + Fintype.card κ) *
          (ENNReal.ofReal K ^ 2 * ∫⁻ p, F p ^ 2 ∂timeProbMeasure t (driverLaw (κ := κ) μ)) := by
          gcongr
      _ = _ := by simp only [L₀]; ring
  have hΦbd : ∀ t ≤ T, ∀ j, Φ t j ≤ L₀ j * ENNReal.ofReal (2 * C) ^ 2 * ENNReal.ofReal T := by
    intro t ht j
    have h := lintegral_sq_functional_sub_le (H := fun _ => ENNReal.ofReal (2 * C)) h0 hX hY
      hbdβ hβ hβ' aemeasurable_const (Eventually.of_forall fun _ => aemeasurable_const) hdom₂
      (ℓ j) ht
    refine h.trans ?_
    rw [lintegral_const, timeProbMeasure_univ]
    have hle : ENNReal.ofReal t ≤ ENNReal.ofReal T := ENNReal.ofReal_le_ofReal (by exact_mod_cast ht)
    calc 2 * ‖ℓ j‖ₑ ^ 2 * (ENNReal.ofReal t + Fintype.card κ) *
          (ENNReal.ofReal (2 * C) ^ 2 * ENNReal.ofReal t)
        ≤ 2 * ‖ℓ j‖ₑ ^ 2 * (ENNReal.ofReal T + Fintype.card κ) *
          (ENNReal.ofReal (2 * C) ^ 2 * ENNReal.ofReal T) := by
          gcongr
      _ = _ := by simp only [L₀]; ring
  -- the Volterra function
  set Ψ : ℝ → ℝ≥0∞ := fun s => ∫⁻ x, F (s, x) ^ 2 ∂driverLaw (κ := κ) μ with hΨdef
  have hF2 : AEMeasurable (fun p => F p ^ 2) (timeProbMeasure T (driverLaw (κ := κ) μ)) :=
    hFm.pow_const 2
  have hΨm : AEMeasurable Ψ (volume.restrict (Ioc 0 (T : ℝ))) := by
    unfold timeProbMeasure at hF2
    exact hF2.lintegral_prod_right'
  have hQ : ∀ t ≤ T, ∫⁻ p, F p ^ 2 ∂timeProbMeasure t (driverLaw (κ := κ) μ) =
      ∫⁻ s in Ioc 0 (t : ℝ), Ψ s := by
    intro t ht
    have h := hF2.mono_measure (timeProbMeasure_le_of_le ht)
    unfold timeProbMeasure at h ⊢
    exact lintegral_prod _ h
  obtain ⟨CE, hCE, hCEle⟩ := enorm_sq_le_coord E
  have hΨΦ : ∀ s : ℝ, 0 ≤ s → Ψ s ≤ CE * ∑ j, Φ s.toNNReal j := by
    intro s hs
    have hpt : ∀ x, F (s, x) ^ 2 ≤ CE * ∑ j, ‖ℓ j (stoppedProcess X ρ s.toNNReal x) -
        ℓ j (stoppedProcess Y ρ s.toNNReal x)‖ₑ ^ 2 := by
      intro x
      have h1 : F (s, x) ^ 2 ≤ ‖stoppedProcess X ρ s.toNNReal x -
          stoppedProcess Y ρ s.toNNReal x‖ₑ ^ 2 := by
        simp only [hFdef, stoppedFun]
        split_ifs with h
        · rw [stoppedProcess_eq_of_le h, stoppedProcess_eq_of_le h]
        · simp
      refine h1.trans ((hCEle _).trans (le_of_eq ?_))
      simp only [map_sub]
      rfl
    have hmeas : ∀ j, AEMeasurable (fun x => ‖ℓ j (stoppedProcess X ρ s.toNNReal x) -
        ℓ j (stoppedProcess Y ρ s.toNNReal x)‖ₑ ^ 2) (driverLaw (κ := κ) μ) := fun j =>
      ((((ℓ j).continuous.comp_aestronglyMeasurable
        (aestronglyMeasurable_stoppedProcess hXa hXc hρ _)).sub
        ((ℓ j).continuous.comp_aestronglyMeasurable
        (aestronglyMeasurable_stoppedProcess hYa hYc hρ _))).enorm).pow_const 2
    calc Ψ s ≤ ∫⁻ x, CE * ∑ j, ‖ℓ j (stoppedProcess X ρ s.toNNReal x) -
          ℓ j (stoppedProcess Y ρ s.toNNReal x)‖ₑ ^ 2 ∂driverLaw (κ := κ) μ :=
          lintegral_mono hpt
      _ = CE * ∑ j, Φ s.toNNReal j := by
          rw [lintegral_const_mul' _ _ hCE, lintegral_finsetSum' _ fun j _ => hmeas j]
  set Lfull : ℝ≥0∞ := CE * ∑ j, L₀ j * ENNReal.ofReal K ^ 2
  set Mfull : ℝ≥0∞ := CE * ∑ j, L₀ j * ENNReal.ofReal (2 * C) ^ 2 * ENNReal.ofReal T
  have hLfull : Lfull ≠ ⊤ := ENNReal.mul_ne_top hCE (ENNReal.sum_ne_top.2 fun j _ =>
    ENNReal.mul_ne_top (hL₀ j) (by simp))
  have hMfull : Mfull ≠ ⊤ := ENNReal.mul_ne_top hCE (ENNReal.sum_ne_top.2 fun j _ =>
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (hL₀ j) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
      ENNReal.ofReal_ne_top)
  have hTnn : (s : ℝ) → s ∈ Icc 0 (T : ℝ) → s.toNNReal ≤ T := fun s hs => by
    rw [Real.toNNReal_le_iff_le_coe]
    exact hs.2
  have hzero := eq_zero_of_lintegral_volterra (Ψ := Ψ) (T := (T : ℝ)) T.2 hΨm hMfull hLfull
    (fun s hs => (hΨΦ s hs.1).trans (mul_le_mul_right (Finset.sum_le_sum fun j _ =>
      hΦbd _ (hTnn s hs) j) _))
    (fun s hs => by
      refine (hΨΦ s hs.1).trans ?_
      have hst := hTnn s hs
      calc CE * ∑ j, Φ s.toNNReal j ≤ CE * ∑ j, L₀ j * ENNReal.ofReal K ^ 2 *
            ∫⁻ p, F p ^ 2 ∂timeProbMeasure s.toNNReal (driverLaw (κ := κ) μ) :=
            mul_le_mul_right (Finset.sum_le_sum fun j _ => hΦlip _ hst j) _
        _ = Lfull * ∫⁻ r in Ioc 0 s, Ψ r := by
            rw [hQ _ hst, Real.coe_toNNReal _ hs.1, ← Finset.sum_mul, mul_assoc])
  intro t ht
  have hQ0 : ∫⁻ p, F p ^ 2 ∂timeProbMeasure t (driverLaw (κ := κ) μ) = 0 := by
    rw [hQ t ht]
    refine (setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_).trans lintegral_zero
    exact hzero s ⟨hs.1.le, hs.2.trans (by exact_mod_cast ht)⟩
  have hΦ0 : ∀ j, Φ t j = 0 := fun j => by
    have := hΦlip t ht j
    rw [hQ0, mul_zero] at this
    exact le_antisymm this zero_le
  have hcoord : ∀ j, ∀ᵐ x ∂driverLaw (κ := κ) μ,
      ℓ j (stoppedProcess X ρ t x) - ℓ j (stoppedProcess Y ρ t x) = 0 := by
    intro j
    have hm : AEMeasurable (fun x => ‖ℓ j (stoppedProcess X ρ t x) -
        ℓ j (stoppedProcess Y ρ t x)‖ₑ ^ 2) (driverLaw (κ := κ) μ) :=
      ((((ℓ j).continuous.comp_aestronglyMeasurable
        (aestronglyMeasurable_stoppedProcess hXa hXc hρ _)).sub
        ((ℓ j).continuous.comp_aestronglyMeasurable
        (aestronglyMeasurable_stoppedProcess hYa hYc hρ _))).enorm).pow_const 2
    have h := (lintegral_eq_zero_iff' hm).1 (hΦ0 j)
    filter_upwards [h] with x hx
    simpa using hx
  filter_upwards [ae_all_iff.2 hcoord] with x hx
  have : stoppedProcess X ρ t x - stoppedProcess Y ρ t x = 0 :=
    eq_zero_of_coord E fun j => by rw [map_sub]; exact hx j
  exact sub_eq_zero.1 this

end BlockBand.SourceProcess.Stochastic.NativeSDE
