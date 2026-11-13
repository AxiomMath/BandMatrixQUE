module

public import BlockBand.Endpoints.Sine.FlowAdmissionDefs
public import BlockBand.Endpoints.Poisson.FiniteLogRecoveryRing
public import BlockBand.Endpoints.Poisson.PhaseFractionalLaw
public import BlockBand.Internal.Contracts.Inputs

/-!
# Uniform bound for the shifted observable

`fa_shifted_obs_le`: fixed `0 < b < 1/2`, bulk `E`, continuous compactly supported `χ ≥ 0`. There
is `B` such that for every admissible `p` with `p.b = b`, every model, pair and every real shift
`a`: `E Σ_α χ(u_α(H + aP_S))|(n/2)‖P_Sψ_α(H + aP_S)‖² - 1| ≤ B`
(`B = C_b∫χ/ρ + 2‖χ‖_∞ C L/(√c ρ)`, `supp χ ⊆ [-L, L]`), uniformly in `W`, `n`, the pair and the
shift. The mass-weighted term is bounded through the shifted mass Palm identity (`fa_mass_le`)
and the count term through the eigenvalue count (`fa_count_lintegral_le`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open BlockBand.Model.Construction BlockBand.External
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.Inputs
open scoped ENNReal

/-!
## Generalities
-/

/-- Finite superadditivity of the lower integral (no measurability). -/
theorem fa_sum_lintegral_le {α ι : Type*} [MeasurableSpace α] {μ : Measure α} (s : Finset ι)
    (f : ι → α → ℝ≥0∞) : ∑ k ∈ s, ∫⁻ x, f k x ∂μ ≤ ∫⁻ x, ∑ k ∈ s, f k x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

theorem fa_rho_pos {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    0 < Parameters.semicircleDensity E := by
  unfold Parameters.semicircleDensity
  apply div_pos
  · apply Real.sqrt_pos.mpr
    nlinarith
  · positivity

section Pair

variable (p : Parameters) (i : ZMod p.n)

theorem fa_measurable_pairMass (α : Fin p.N) : Measurable fun H => pairMass p i α H :=
  (measurable_physicalOrderedBlockMass p α i).add (measurable_physicalOrderedBlockMass p α (i + 1))

theorem fa_pairMass_nonneg (α : Fin p.N) (H : p.SiteMatrix) : 0 ≤ pairMass p i α H :=
  add_nonneg (physicalOrderedBlockMass_nonneg p H α i)
    (physicalOrderedBlockMass_nonneg p H α (i + 1))

theorem fa_measurable_microCoord (E : ℝ) : Measurable (microCoord p E) := by
  unfold microCoord
  fun_prop

theorem fa_measurable_obs (E : ℝ) {χ : ℝ → ℝ} (hχ : Continuous χ) :
    Measurable (fa_obs p i E χ) := by
  unfold fa_obs
  refine Finset.measurable_sum _ fun α _ => ENNReal.measurable_ofReal.comp ?_
  exact ((hχ.measurable.comp ((fa_measurable_microCoord p E).comp
    (measurable_physicalOrderedEigenvalue p α))).mul
    ((((fa_measurable_pairMass p i α).const_mul _).sub_const 1).abs))

/-!
## The mass-weighted term
-/

/-- `Σ_ℓ 𝒜_{ℓ,e}[c] ≤ Z(e) c` for a constant `c` (the sector indicators sum to at most one). -/
theorem fa_sum_sectorFiber_const_le
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (ω : SplitState p i)
    (e : ℝ) (c : ℝ≥0∞) (hc : c ≠ ⊤) :
    ∑ ℓ ∈ Finset.range (2 * p.W), pairSectorFiber p i U ω e ℓ (fun _ => c) ≤
      pairNormalizer p i U ω e * c := by
  classical
  unfold pairSectorFiber pairNormalizer
  refine (fa_sum_lintegral_le _ _).trans ?_
  rw [← lintegral_mul_const' _ _ hc]
  refine lintegral_mono fun v => ?_
  refine (fa_sum_lintegral_le _ _).trans ?_
  rw [← lintegral_mul_const' _ _ hc]
  refine lintegral_mono fun G' => ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_ite_eq]
  gcongr
  exact mul_le_of_le_one_right zero_le (by split_ifs <;> simp)

/-- The exterior of a fresh-pair split is almost surely Hermitian. -/
theorem fa_ae_isHermitianExterior (model : p.GaussianRingModel) (s : ℝ)
    (Pω : Measure (SplitState p i)) (h : IsPairSplitting p i model s Pω) :
    ∀ᵐ ω ∂Pω, IsHermitianExterior p i ω := by
  have hP : IsProbabilityMeasure (gueMeasure (PairSite p i) (pairTime p s)) :=
    isProbabilityMeasure_gueMeasure _ _
  have h1 : ∀ᵐ x ∂(Pω.prod (gueMeasure (PairSite p i) (pairTime p s))),
      (assemble p i x.1 x.2).IsHermitian := by
    have h0 := model.isPhysical.1
    rw [← h] at h0
    exact ae_of_ae_map (measurable_assemble p i).aemeasurable h0
  have h2 := Measure.ae_ae_of_ae_prod h1
  filter_upwards [h2] with ω hω
  obtain ⟨G, hG1, hG2⟩ :=
    (hω.and (PhaseFractional.ae_gue_isHermitian (PairSite p i) (pairTime p s))).exists
  refine ⟨?_, ?_⟩
  · have h3 : (exteriorBlock p i (assemble p i ω G)).IsHermitian := hG1.submatrix Subtype.val
    rwa [exteriorBlock_assemble] at h3
  · have hb : pairBlock p i (assemble p i ω G) = ω.2.2 + G := by
      ext a b; simp [pairBlock, assemble, a.2, b.2]
    have h3 : (pairBlock p i (assemble p i ω G)).IsHermitian := hG1.submatrix Subtype.val
    rw [hb] at h3
    simpa using h3.sub hG2

/-- Mass-weighted term under a shift. `b` first, then `C ≥ 0`; for every `p` with `p.b = b`,
model, pair, real shift `a`, energy `E` and continuous `χ ≥ 0`:
`E Σ_α q_{αS}(H + aP_S) χ(u_α(H + aP_S)) ≤ C·2W ∫ χ(u(e)) de`. -/
theorem fa_mass_le (hPalm : ExactPalmContract) (hCo : CoareaContract)
    (hShift : FaShiftedMassPalm) (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Parameters), p.b = b → ∀ (model : p.GaussianRingModel)
      (i : ZMod p.n) (a E : ℝ) (χ : ℝ → ℝ), Continuous χ →
      (∫⁻ H, ∑ α : Fin p.N,
          ENNReal.ofReal (pairMass p i α (H + (a : ℂ) • pairProjector p i)) *
          ENNReal.ofReal (χ (microCoord p E
            (physicalOrderedEigenvalue p (H + (a : ℂ) • pairProjector p i) α)))
        ∂(model.law : Measure p.SiteMatrix)) ≤
        ENNReal.ofReal (C * (2 * p.W)) * ∫⁻ e, ENNReal.ofReal (χ (microCoord p E e)) := by
  obtain ⟨C, hC⟩ := hPalm.upper b hb hb'
  refine ⟨max C 0, le_max_right _ _, fun p hp model i a E χ hχ => ?_⟩
  obtain ⟨Pω, hPω⟩ := hCo.splitting_exists p model i (pairS p)
    (lt_min p.b_pos p.c_pos) (by rw [pairS, min_comm])
  obtain ⟨U, hU⟩ := hCo.frame_exists p i
  have hPprob := isProbabilityMeasure_of_splitting p i model _ Pω hPω
  let f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞ := fun e _ => ENNReal.ofReal (χ (microCoord p E e))
  have hf : Measurable (Function.uncurry f) :=
    (ENNReal.measurable_ofReal.comp (hχ.measurable.comp (fa_measurable_microCoord p E))).comp
      measurable_fst
  have hmain := hShift p model i Pω hPω U hU a f hf
  refine (le_of_eq hmain).trans ?_
  calc _ ≤ ∫⁻ _ω, (ENNReal.ofReal (max C 0 * (2 * p.W)) *
        ∫⁻ e, ENNReal.ofReal (χ (microCoord p E e))) ∂Pω := by
        refine lintegral_mono_ae ?_
        filter_upwards [fa_ae_isHermitianExterior p i model _ Pω hPω] with ω hω
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono fun e => ?_
        have hω' : IsHermitianExterior p i (fa_shiftExterior p i a ω) :=
          ⟨hω.1, hω.2.add (isHermitian_real_smul_one a)⟩
        refine (fa_sum_sectorFiber_const_le p i U _ e _ ENNReal.ofReal_ne_top).trans ?_
        gcongr
        refine (hC p hp i U hU _ hω' e).trans (ENNReal.ofReal_le_ofReal ?_)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

/-- The energy-window Jacobian: `∫ χ(Nρ(e - E)) de = (Nρ)⁻¹ ∫ χ`. -/
theorem fa_lintegral_microCoord (E : ℝ) (hρ : 0 < Parameters.semicircleDensity E)
    {χ : ℝ → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) :
    ∫⁻ e, ENNReal.ofReal (χ (microCoord p E e)) =
      ENNReal.ofReal (((p.N : ℝ) * Parameters.semicircleDensity E)⁻¹ * ∫ x, χ x) := by
  set c : ℝ := (p.N : ℝ) * Parameters.semicircleDensity E with hc_def
  have hc : 0 < c := mul_pos (Nat.cast_pos.mpr p.N_pos) hρ
  have hint : Integrable χ := hχc.integrable_of_hasCompactSupport hχs
  have hint' : Integrable (fun e => χ (c * (e - E))) :=
    (hint.comp_mul_left' hc.ne').comp_sub_right E
  have hmc : ∀ e, microCoord p E e = c * (e - E) := fun e => rfl
  simp_rw [hmc]
  rw [← ofReal_integral_eq_lintegral_ofReal hint' (ae_of_all _ fun _ => hχ0 _)]
  congr 1
  rw [integral_sub_right_eq_self (fun e => χ (c * e)) E, Measure.integral_comp_mul_left,
    smul_eq_mul, abs_inv, abs_of_pos hc]

/-!
## The count term
-/

/-- `eigenCount A J = Tr 1_J(A)`. -/
theorem fa_eigenCount_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A : PSSS.HermitianMatrix ι)
    (J : Set ℝ) :
    (PSSS.eigenCount A J : ℝ) = unfoldedSpectralSum A.1 A.2 0 1 (J.indicator 1) := by
  classical
  unfold PSSS.eigenCount unfoldedSpectralSum
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Set.indicator_apply]

/-- `#{α : λ_α(H) ∈ J} = Tr 1_J(H)` for Hermitian `H`. -/
theorem fa_card_eigenvalue_eq (H : p.SiteMatrix) (hH : H.IsHermitian) (J : Set ℝ)
    [DecidablePred (· ∈ J)] :
    ((Finset.univ.filter fun α : Fin p.N => physicalOrderedEigenvalue p H α ∈ J).card : ℝ) =
      unfoldedSpectralSum H hH 0 1 (J.indicator 1) := by
  classical
  rw [Finset.card_filter]
  push_cast
  unfold unfoldedSpectralSum
  refine Fintype.sum_equiv (finCongr (physicalSite_card p).symm) _ _ fun α => ?_
  simp only [physicalOrderedEigenvalue, rawIncreasingEigenvalue_eq _ H hH, physicalSpectralRank,
    finCongr_apply, one_mul, sub_zero, Set.indicator_apply, Pi.one_apply]

theorem fa_unfoldedSpectralSum_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : Matrix ι ι ℂ} (h : X = Y) (hX : X.IsHermitian) (hY : Y.IsHermitian) (E Λ : ℝ)
    (f : ℝ → ℝ) : unfoldedSpectralSum X hX E Λ f = unfoldedSpectralSum Y hY E Λ f := by
  subst h; rfl

theorem fa_isHermitian_shift (a : ℝ) : ((a : ℂ) • pairProjector p i).IsHermitian := by
  ext x y
  by_cases h : x = y
  · subst h
    simp only [pairProjector, conjTranspose_apply, Matrix.smul_apply, diagonal_apply_eq]
    split_ifs <;> simp
  · simp [pairProjector, h, Ne.symm h]

/-- The constant deformation `aP_S`, restricted to the sites of all blocks. -/
def fa_constDeformation (a : ℝ) :
    p.SiteMatrix → PSSS.HermitianMatrix (BlockSites p Finset.univ) := fun _ =>
  ⟨((a : ℂ) • pairProjector p i).submatrix Subtype.val Subtype.val,
    (fa_isHermitian_shift p i a).submatrix _⟩

/-- On Hermitian `H`, the count of `H + aP_S` is the `R = all blocks` subsystem count of
`PhysicalBlockConditionalCount` with the constant deformation `aP_S`. -/
theorem fa_count_eq_subsystemCount (H : p.SiteMatrix) (hH : H.IsHermitian) (a : ℝ)
    (J : Set ℝ) [DecidablePred (· ∈ J)] :
    ((Finset.univ.filter fun α : Fin p.N =>
        physicalOrderedEigenvalue p (H + (a : ℂ) • pairProjector p i) α ∈ J).card : ℝ) =
      (subsystemCount p Finset.univ (fa_constDeformation p i a) J H : ℝ) := by
  let e : BlockSites p Finset.univ ≃ p.Site :=
    Equiv.subtypeUnivEquiv (fun x : p.Site => Finset.mem_univ x.1)
  have hHa := hH.add (fa_isHermitian_shift p i a)
  have hv : (p.physicalHermitianVersion H).1 = H :=
    p.gaussianReconstruction_gaussianExtraction H hH
  unfold subsystemCount
  rw [fa_eigenCount_eq, fa_card_eigenvalue_eq p _ hHa]
  refine (unfoldedSpectralSum_submatrix e hHa (hHa.submatrix e) 0 1 _).symm.trans ?_
  refine fa_unfoldedSpectralSum_congr ?_ _ _ _ _ _
  simp only [fa_constDeformation, hv, Matrix.submatrix_add]
  rfl

/-- Counts under a deterministic shift (through `PhysicalBlockConditionalCount`, `r = 1`, all
blocks fresh). One `C > 0`; for every `p`, model, pair, real `a` and `lo ≤ hi`:
`E #{α : λ_α(H + aP_S) ∈ [lo, hi]} ≤ C/√c · nW · (hi - lo)`. -/
theorem fa_count_lintegral_le (hCount : PhysicalBlockConditionalCount) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters) (model : p.GaussianRingModel) (i : ZMod p.n)
      (a lo hi : ℝ), lo ≤ hi →
      ∫⁻ H, ((Finset.univ.filter fun α : Fin p.N =>
          physicalOrderedEigenvalue p (H + (a : ℂ) • pairProjector p i) α ∈
            Set.Icc lo hi).card : ℝ≥0∞) ∂(model.law : Measure p.SiteMatrix) ≤
        ENNReal.ofReal (C / Real.sqrt p.c * ((p.n * p.W : ℕ) : ℝ) * (hi - lo)) := by
  obtain ⟨C, hC, h⟩ := hCount
  refine ⟨C, hC, fun p model i a lo hi hlh => ?_⟩
  obtain ⟨hint, hle⟩ := h p model Finset.univ (fa_constDeformation p i a) measurable_const
    lo hi hlh 1 le_rfl
  have hae : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ((Finset.univ.filter fun α : Fin p.N =>
          physicalOrderedEigenvalue p (H + (a : ℂ) • pairProjector p i) α ∈
            Set.Icc lo hi).card : ℝ≥0∞) =
        ENNReal.ofReal (PSSS.factorialCount
          (subsystemCount p Finset.univ (fa_constDeformation p i a) (Set.Icc lo hi)) 1 H) := by
    filter_upwards [model.isPhysical.1] with H hH
    rw [PSSS.factorialCount, Nat.descFactorial_one, ← fa_count_eq_subsystemCount p i H hH a,
      ENNReal.ofReal_natCast]
  rw [lintegral_congr_ae hae, ← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun _ => Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (hle.trans_eq ?_)
  rw [pow_one, Finset.card_univ, ZMod.card]

end Pair

/-!
## The uniform bound
-/

/-- `sup_{a, W} E Σ_α χ(u_α)|x_α - 1|(H + aP_S) < ∞`. Fixed `0 < b < 1/2`, bulk `-2 < E < 2`,
continuous compactly supported `χ ≥ 0`; then `B ≥ 0`; for every `p` with `p.b = b`, every model,
pair and real shift `a`. -/
theorem fa_shifted_obs_le (hPalm : ExactPalmContract) (hCo : CoareaContract)
    (hShift : FaShiftedMassPalm) (hCount : PhysicalBlockConditionalCount)
    (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ) (hE1 : -2 < E) (hE2 : E < 2)
    {χ : ℝ → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (p : Parameters), p.b = b → ∀ (model : p.GaussianRingModel)
      (i : ZMod p.n) (a : ℝ),
      ∫⁻ H, fa_obs p i E χ (H + (a : ℂ) • pairProjector p i)
        ∂(model.law : Measure p.SiteMatrix) ≤ ENNReal.ofReal B := by
  obtain ⟨Cm, hCm0, hCm⟩ := fa_mass_le hPalm hCo hShift b hb hb'
  obtain ⟨Cc, hCc0, hCc⟩ := fa_count_lintegral_le hCount
  obtain ⟨M, hM⟩ := hχc.bounded_above_of_compact_support hχs
  obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 ≤ L ∧ ∀ x, L < |x| → χ x = 0 := by
    obtain ⟨L, hL⟩ := (hχs.isCompact.isBounded).subset_closedBall 0
    refine ⟨max L 0, le_max_right _ _, fun x hx => ?_⟩
    refine image_eq_zero_of_notMem_tsupport fun hxs => ?_
    have := hL hxs
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact absurd (this.trans (le_max_left _ _)) (not_le.mpr hx)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hχM : ∀ x, χ x ≤ M := fun x => (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hM x)
  set ρ := Parameters.semicircleDensity E with hρ_def
  have hρ : 0 < ρ := fa_rho_pos hE1 hE2
  set m := ∫ x, χ x with hm_def
  have hm0 : 0 ≤ m := integral_nonneg hχ0
  refine ⟨Cm * m / ρ + M * (Cc / Real.sqrt (1 - 2 * b) * (2 * L / ρ)), by positivity,
    fun p hp model i a => ?_⟩
  set H' : p.SiteMatrix → p.SiteMatrix := fun H => H + (a : ℂ) • pairProjector p i
  have hH' : Measurable H' := measurable_id.add_const _
  set N : ℝ := (p.N : ℝ) with hN_def
  have hNpos : 0 < N := Nat.cast_pos.mpr p.N_pos
  have hNρ : 0 < N * ρ := mul_pos hNpos hρ
  -- the pointwise split `χ|x-1| ≤ (n/2) q χ + χ`
  set X : p.SiteMatrix → ℝ≥0∞ := fun H => ∑ α : Fin p.N,
    ENNReal.ofReal (pairMass p i α (H' H)) *
      ENNReal.ofReal (χ (microCoord p E (physicalOrderedEigenvalue p (H' H) α)))
  set Y : p.SiteMatrix → ℝ≥0∞ := fun H => ∑ α : Fin p.N,
    ENNReal.ofReal (χ (microCoord p E (physicalOrderedEigenvalue p (H' H) α)))
  have hpt : ∀ H, fa_obs p i E χ (H' H) ≤ ENNReal.ofReal ((p.n : ℝ) / 2) * X H + Y H := by
    intro H
    simp only [fa_obs, X, Y, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun α _ => ?_
    have hq := fa_pairMass_nonneg p i α (H' H)
    have hχα := hχ0 (microCoord p E (physicalOrderedEigenvalue p (H' H) α))
    rw [← ENNReal.ofReal_mul hq, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) hχα]
    refine ENNReal.ofReal_le_ofReal ?_
    have hx : 0 ≤ (p.n : ℝ) / 2 * pairMass p i α (H' H) := by positivity
    have habs : |(p.n : ℝ) / 2 * pairMass p i α (H' H) - 1| ≤
        (p.n : ℝ) / 2 * pairMass p i α (H' H) + 1 := by
      rw [abs_le]; constructor <;> linarith
    nlinarith [mul_le_mul_of_nonneg_left habs hχα]
  have hXm : Measurable X := by
    refine Finset.measurable_sum _ fun α _ => ?_
    exact (ENNReal.measurable_ofReal.comp ((fa_measurable_pairMass p i α).comp hH')).mul
      (ENNReal.measurable_ofReal.comp (hχc.measurable.comp ((fa_measurable_microCoord p E).comp
        ((measurable_physicalOrderedEigenvalue p α).comp hH'))))
  -- count term, pointwise
  set lo := E - L / (N * ρ)
  set hi := E + L / (N * ρ)
  have hlh : lo ≤ hi := by
    have : 0 ≤ L / (N * ρ) := div_nonneg hL0 hNρ.le
    simp only [lo, hi]; linarith
  have hYle : ∀ H, Y H ≤ ENNReal.ofReal M * ((Finset.univ.filter fun α : Fin p.N =>
      physicalOrderedEigenvalue p (H' H) α ∈ Set.Icc lo hi).card : ℝ≥0∞) := by
    intro H
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun α _ => ?_
    by_cases hin : physicalOrderedEigenvalue p (H' H) α ∈ Set.Icc lo hi
    · simp only [hin, ite_true, Nat.cast_one, mul_one]
      exact ENNReal.ofReal_le_ofReal (hχM _)
    · simp only [hin, ite_false, Nat.cast_zero, mul_zero, nonpos_iff_eq_zero,
        ENNReal.ofReal_eq_zero]
      refine le_of_eq (hL _ ?_)
      set l := physicalOrderedEigenvalue p (H' H) α
      have hfar : L / (N * ρ) < |l - E| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hin
        rcases hin with h | h
        · rw [abs_sub_comm, abs_of_pos (by simp only [lo] at h; linarith)]
          simp only [lo] at h; linarith
        · rw [abs_of_pos (by simp only [hi] at h; linarith)]
          simp only [hi] at h; linarith
      have : microCoord p E l = (N * ρ) * (l - E) := rfl
      rw [this, abs_mul, abs_of_pos hNρ]
      rwa [div_lt_iff₀' hNρ] at hfar
  -- integrate
  calc ∫⁻ H, fa_obs p i E χ (H' H) ∂(model.law : Measure p.SiteMatrix)
      ≤ ∫⁻ H, (ENNReal.ofReal ((p.n : ℝ) / 2) * X H + Y H)
          ∂(model.law : Measure p.SiteMatrix) := lintegral_mono hpt
    _ = ENNReal.ofReal ((p.n : ℝ) / 2) * ∫⁻ H, X H ∂(model.law : Measure p.SiteMatrix) +
          ∫⁻ H, Y H ∂(model.law : Measure p.SiteMatrix) := by
        rw [lintegral_add_left (hXm.const_mul _), lintegral_const_mul _ hXm]
    _ ≤ ENNReal.ofReal ((p.n : ℝ) / 2) * (ENNReal.ofReal (Cm * (2 * p.W)) *
          ENNReal.ofReal ((N * ρ)⁻¹ * m)) +
          ENNReal.ofReal M * ENNReal.ofReal (Cc / Real.sqrt p.c * ((p.n * p.W : ℕ) : ℝ) *
            (hi - lo)) := by
        gcongr
        · have h1 := hCm p hp model i a E χ hχc
          rwa [fa_lintegral_microCoord p E hρ hχc hχs hχ0] at h1
        · refine (lintegral_mono hYle).trans ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          gcongr
          exact hCc p model i a lo hi hlh
    _ = ENNReal.ofReal (Cm * m / ρ + M * (Cc / Real.sqrt (1 - 2 * b) * (2 * L / ρ))) := by
        have hc : p.c = 1 - 2 * b := by rw [Parameters.c, hp]
        have hW : (0 : ℝ) < p.W := Nat.cast_pos.mpr p.W_pos
        have hn : (0 : ℝ) < p.n := Nat.cast_pos.mpr p.n_pos
        have hNnW : N = (p.n : ℝ) * p.W := by simp [N, Parameters.N]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul hM0, ← ENNReal.ofReal_add (by positivity)]
        · congr 1
          rw [hc]
          simp only [hi, lo]
          push_cast
          rw [hNnW]
          field_simp
          ring
        · refine mul_nonneg hM0 (mul_nonneg (mul_nonneg (by positivity) (by positivity)) ?_)
          linarith

end BlockBand.Endpoints
