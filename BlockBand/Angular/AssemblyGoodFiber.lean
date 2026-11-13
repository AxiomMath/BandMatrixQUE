module

public import BlockBand.Angular.AssemblyGoodTransfer

/-!
# The comparison on one good fiber of the physical angular estimate

`fiber_bound`: at a fixed exterior `ω` with Hermitian blocks and an energy `E` with `(ω, E)` in
the good set, given angular data `D` (`D.K = K_e(E)`, `s = splitS`, the center
identity `j_*(J) = j_e`, the root bounds and the first moment `hFM` with remainder `r`),
the angular comparison (with `𝓛 = 𝓛_E` = `reconMat`, `J = pairContrast`,
`Φ = ρ(φ(𝓛v/‖𝓛v‖))`, cutoff `stepSixCutoff R₀`) gives for the signed fiber integrals of the
good observable
`|∫(obsG)⁺ - ∫(obsG)⁻| ≤ K (zT + r + sT)`, `K = |compConst · (M + L)/(2W)|`,
where `zT = ∫ν c𝓡(n/2)𝔷` (the angular mass `Z`) and `sT = ∫ν c𝓡(n/2)𝔷‖score‖` bounds the score
term `ν(χ‖∇Zf‖)` (`gradNorm_stepOneDensity_le`). Both fiber integrals are finite.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.AssemblyGood

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.FiberAngular
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.QUE
open BlockBand.Angular.Assembly BlockBand.Angular.ProjectiveStein BlockBand.Angular.PairCoareaBridge
open BlockBand.DeterminantScore BlockBand.DeterminantScore.PhysicalColumn BlockBand.Coarea
open BlockBand.Model.Construction BlockBand.QUE.PhysicalAngularReduction
open BlockBand.Angular.Ratio BlockBand.Angular.Stein BlockBand.Angular.Stein.AngularData
open BlockBand.Angular.StepTwoGlue BlockBand.Angular.DetFactor
open scoped ENNReal NNReal

variable {p : BlockBand.Parameters} {i : ZMod p.n}

/-- The fiber angular mass `∫ν c_{d,t}𝓡(n/2)𝔷_E` (the `Z` of the angular comparison). -/
def zT (α : Fin p.N) (U : FrameMap p i) (ω : SplitState p i) (E : ℝ) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (angularWeight p i (splitS p) ω E v) * detFactor p i α (splitS p) U ω E v
    ∂projectiveHaar (PairSite p i)

/-- The fiber score mass `∫ν c_{d,t}𝓡(n/2)𝔷_E ‖score‖`. -/
def sT (α : Fin p.N) (U : FrameMap p i) (ω : SplitState p i) (E : ℝ) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (angularWeight p i (splitS p) ω E v) * detFactor p i α (splitS p) U ω E v *
      ENNReal.ofReal (l2Norm (score α (splitS p) U (ω, E, v))) ∂projectiveHaar (PairSite p i)

theorem unit_of_normSqSum {v : PairSite p i → ℂ} (hv : normSqSum v = 1) : l2Norm v = 1 := by
  show Real.sqrt (normSqSum v) = 1
  rw [hv, Real.sqrt_one]

/-- The angular weight times the determinant factor is `e^{expo} Zf` at unit `v`. -/
theorem weight_eq (α : Fin p.N) {U : FrameMap p i} (hU : IsPairFrame p i U) {ω : SplitState p i}
    (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian) {E : ℝ} (D : AngularData (PairSite p i))
    (hDK : D.K = edgeSchur p i (asm p i ω) E) (hDs : D.s = splitS p) {v : PairSite p i → ℂ}
    (hv : l2Norm v = 1) :
    ENNReal.ofReal (angularWeight p i (splitS p) ω E v) * detFactor p i α (splitS p) U ω E v =
      ENNReal.ofReal (Real.exp (D.expo v) * stepOneDensity p i α (splitS p) ω E v) := by
  have hDK' : D.K = physicalCoareaF ω.1 ω.2.1 ω.2.2 E - (E : ℂ) • 1 := by
    rw [hDK, edgeSchur_asm]; rfl
  have haw := angularWeight_eq_exp_expo p i ω hR hV E D hDK' hv
  rw [hDs] at haw
  rw [haw, detFactor_eq_ofReal p i α _ hU hR hV E hv, stepOneDensity,
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (BlockBand.Angular.FirstMoment.coareaConstant_nonneg _ _) (by positivity))
      (Real.exp_pos _).le)]
  congr 1
  ring

/-- **The comparison on one good fiber** at fixed `(ω, E)`. -/
theorem fiber_bound (hScore : DeterminantScoreStatement) (α : Fin p.N) {U : FrameMap p i}
    (hU : IsPairFrame p i U) {cst : CenterDomainConstants} {M₀ R₀ : ℝ} {φ : (p.Site → ℂ) → ℂ}
    {M L : ℝ} (hφ : IsAngularTest φ M L) {ρ : ℂ → ℝ} (hρ : IsRealPart ρ)
    (hgm : Measurable (Function.uncurry (obsG p i cst α M₀ R₀ φ ρ)))
    {ω : SplitState p i} (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian) {E : ℝ}
    (hx : (ω, E) ∈ goodSet p i cst α M₀) (D : AngularData (PairSite p i))
    (hDK : D.K = edgeSchur p i (asm p i ω) E) (hDs : D.s = splitS p)
    (hj : D.jStar (pairContrast p i) = dCH p i cst α (ω, E))
    {σ Y Zb C₀ r : ℝ} (hs1 : D.s ≤ σ) (hs2 : D.s⁻¹ ≤ σ) (hY : D.ζ.im⁻¹ ≤ Y) (hZb : ‖D.ζ‖ ≤ Zb)
    (hC₀ : 0 ≤ C₀) (hr : 0 ≤ r)
    (hFM : ∀ w : PairSite p i → ℂ,
      ∫ v, Real.exp (D.expo v) * stepOneDensity p i α (splitS p) ω E v * ‖star w ⬝ᵥ v‖ ^ 2
          ∂projectiveHaar (PairSite p i) ≤
        C₀ * ((∫ v, Real.exp (D.expo v) * stepOneDensity p i α (splitS p) ω E v
            ∂projectiveHaar (PairSite p i)) + r) / Fintype.card (PairSite p i) *
          (star w ⬝ᵥ (D.Γ *ᵥ w)).re) :
    angInt α U (obsG p i cst α M₀ R₀ φ ρ) 1 ω E ≠ ∞ ∧
      angInt α U (obsG p i cst α M₀ R₀ φ ρ) (-1) ω E ≠ ∞ ∧
      ENNReal.ofReal |(angInt α U (obsG p i cst α M₀ R₀ φ ρ) 1 ω E).toReal -
          (angInt α U (obsG p i cst α M₀ R₀ φ ρ) (-1) ω E).toReal| ≤
        ENNReal.ofReal |compConst σ Y Zb C₀ (stepSixCutoff R₀) * (M + L) /
            Fintype.card (PairSite p i)| *
          (zT α U ω E + ENNReal.ofReal r + sT α U ω E) := by
  set Zf := stepOneDensity p i α (splitS p) ω E with hZfdef
  set w : (PairSite p i → ℂ) → ℝ := fun v => Real.exp (D.expo v) * Zf v with hwdef
  obtain ⟨h, hhdef⟩ : ∃ h : (PairSite p i → ℂ) → ℝ,
      h = fun v => obsG p i cst α M₀ R₀ φ ρ (ω, E) (schurLift p i ω.1 ω.2.1 E v) := ⟨_, rfl⟩
  have hZ0 : ∀ v, 0 ≤ Zf v := stepOneDensity_nonneg α _ hR hV E
  have hw0 : ∀ v, 0 ≤ w v := fun v => mul_nonneg (Real.exp_pos _).le (hZ0 v)
  have hZc : ContDiffOn ℝ 1 Zf {z | z ≠ 0} :=
    contDiffOn_const.mul (contDiffOn_pairAngularDensity α _ hR hV E)
  have hZi : BlockBand.Angular.DegreeZero.IsScaleInvariant Zf := fun z t ht => by
    show _ * pairAngularDensity p i α (splitS p) ω E (t • z) = _ * pairAngularDensity p i α _ ω E z
    rw [isScaleInvariant_pairAngularDensity α _ hR hV E z t ht]
  have hwc : ContinuousOn w {z | z ≠ 0} :=
    (Real.continuous_exp.comp_continuousOn D.expo_c1.continuousOn).mul hZc.continuousOn
  have hwi : Integrable w (projectiveHaar (PairSite p i)) := integrable_of_continuousOn hwc
  have hsl : Measurable fun v : PairSite p i → ℂ => schurLift p i ω.1 ω.2.1 E v := by
    have e : (fun v : PairSite p i → ℂ => schurLift p i ω.1 ω.2.1 E v) =
        fun v => reconMat p i ω.1 ω.2.1 E *ᵥ v :=
      funext fun v => (reconMat_mulVec p i _ _ _ v).symm
    rw [e]
    exact measurable_mulVec' measurable_const measurable_id
  have hhm : Measurable h := by
    have h0 : Measurable fun _ : PairSite p i → ℂ => ((ω, E) : SplitState p i × ℝ) :=
      measurable_const
    have h1 := h0.prodMk hsl
    have h2 := hgm.comp h1
    rw [hhdef]
    exact h2
  have hB : ∀ v, |h v| ≤ 2 * M := fun v => by rw [hhdef]; exact abs_obsG_le hφ hρ _ _
  obtain ⟨hf1, hf2, heq⟩ := toReal_sub_eq_integral hw0 hwi hhm hB
  -- the fiber integrals in density form
  have hA : ∀ sgn : ℝ, angInt α U (obsG p i cst α M₀ R₀ φ ρ) sgn ω E =
      ∫⁻ v, ENNReal.ofReal (w v) * ENNReal.ofReal (sgn * h v) ∂projectiveHaar (PairSite p i) := by
    intro sgn
    unfold angInt
    refine lintegral_congr_ae ?_
    filter_upwards [ae_projectiveHaar_unit (ι := PairSite p i)] with v hv
    rw [mul_right_comm, weight_eq α hU hR hV D hDK hDs (unit_of_normSqSum hv), hhdef]
  have hA1 : angInt α U (obsG p i cst α M₀ R₀ φ ρ) 1 ω E =
      ∫⁻ v, ENNReal.ofReal (w v) * ENNReal.ofReal (h v) ∂projectiveHaar (PairSite p i) := by
    rw [hA]; simp only [one_mul]
  have hA2 : angInt α U (obsG p i cst α M₀ R₀ φ ρ) (-1) ω E =
      ∫⁻ v, ENNReal.ofReal (w v) * ENNReal.ofReal (-h v) ∂projectiveHaar (PairSite p i) := by
    rw [hA]; simp only [neg_one_mul]
  refine ⟨hA1 ▸ hf1, hA2 ▸ hf2, ?_⟩
  rw [hA1, hA2, heq]
  -- the comparison
  set Lm := reconMat p i ω.1 ω.2.1 E
  set J := pairContrast p i
  set X := stepSixCutoff R₀
  have hcomp := angular_comparison D (reconMat_injective p i ω.1 ω.2.1 E)
    (isContraction_pairContrast p i) hs1 hs2 hY hZb X (measurable_stepOneDensity α _ hR hV E) hZi
    hZc hZ0 hC₀ hr hFM (abs_obs_le (reconMat_injective p i ω.1 ω.2.1 E) hφ hρ)
    (IsAngularTest.lip_nonneg hφ) (reconLip_obs (reconMat_injective p i ω.1 ω.2.1 E) hφ hρ)
  have hint : (∫ v, w v * h v ∂projectiveHaar (PairSite p i)) =
      ∫ v, Real.exp (D.expo v) * Zf v * (X.χ (D.b₂ v) * (quadQuot J v - D.jStar J) *
        ρ (φ (recon Lm v))) ∂projectiveHaar (PairSite p i) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_projectiveHaar_unit (ι := PairSite p i)] with v hv
    have hv0 : v ≠ 0 := ne_zero_of_l2Norm (unit_of_normSqSum hv)
    rw [hhdef]
    simp only [hwdef]
    rw [obsG_schurLift hx D hDK hj hv0]
  rw [hint]
  set Zi := ∫ v, Real.exp (D.expo v) * Zf v ∂projectiveHaar (PairSite p i)
  set Si := ∫ v, Real.exp (D.expo v) * X.χ (D.b₂ v) * gradNorm Zf v ∂projectiveHaar (PairSite p i)
  have hZi0 : 0 ≤ Zi := integral_nonneg fun v => hw0 v
  have hSi0 : 0 ≤ Si := integral_nonneg fun v =>
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (X.nonneg _)) (Real.sqrt_nonneg _)
  set K := compConst σ Y Zb C₀ X * (M + L) / Fintype.card (PairSite p i)
  have h1 : |∫ v, Real.exp (D.expo v) * Zf v * (X.χ (D.b₂ v) * (quadQuot J v - D.jStar J) *
      ρ (φ (recon Lm v))) ∂projectiveHaar (PairSite p i)| ≤ |K| * (Zi + r + Si) :=
    hcomp.trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
  refine (ENNReal.ofReal_le_ofReal h1).trans ?_
  rw [ENNReal.ofReal_mul (abs_nonneg K)]
  gcongr
  refine (ENNReal.ofReal_add_le).trans (add_le_add (ENNReal.ofReal_add_le.trans
    (add_le_add ?_ le_rfl)) ?_)
  · -- `Z`
    rw [ofReal_integral_eq_lintegral_ofReal hwi (Filter.Eventually.of_forall hw0)]
    unfold zT
    refine le_of_eq (lintegral_congr_ae ?_)
    filter_upwards [ae_projectiveHaar_unit (ι := PairSite p i)] with v hv
    rw [weight_eq α hU hR hV D hDK hDs (unit_of_normSqSum hv)]
  · -- the score term
    have hE : (ω.1 - (E : ℂ) • 1).det ≠ 0 := by
      rw [goodSet_eq] at hx; exact hx.2.1.1
    have hpt : ∀ᵐ v ∂projectiveHaar (PairSite p i),
        ENNReal.ofReal (Real.exp (D.expo v) * X.χ (D.b₂ v) * gradNorm Zf v) ≤
          ENNReal.ofReal (angularWeight p i (splitS p) ω E v) * detFactor p i α (splitS p) U ω E v *
            ENNReal.ofReal (l2Norm (score α (splitS p) U (ω, E, v))) := by
      filter_upwards [ae_projectiveHaar_unit (ι := PairSite p i)] with v hv
      have hv1 := unit_of_normSqSum hv
      rw [weight_eq α hU hR hV D hDK hDs hv1, ← ENNReal.ofReal_mul (hw0 v)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hg := gradNorm_stepOneDensity_le hScore α (splitS_pos p) hU hR hV hE hv1
      have hχ : X.χ (D.b₂ v) ≤ 1 := X.le _
      have hgn : 0 ≤ gradNorm Zf v := Real.sqrt_nonneg _
      calc Real.exp (D.expo v) * X.χ (D.b₂ v) * gradNorm Zf v
          ≤ Real.exp (D.expo v) * 1 * (Zf v * l2Norm (score α (splitS p) U (ω, E, v))) := by
            gcongr
        _ = _ := by ring
    by_cases hSint : Integrable (fun v => Real.exp (D.expo v) * X.χ (D.b₂ v) * gradNorm Zf v)
        (projectiveHaar (PairSite p i))
    · rw [ofReal_integral_eq_lintegral_ofReal hSint (Filter.Eventually.of_forall fun v =>
        mul_nonneg (mul_nonneg (Real.exp_pos _).le (X.nonneg _)) (Real.sqrt_nonneg _))]
      exact lintegral_mono_ae hpt
    · rw [show Si = 0 from integral_undef hSint, ENNReal.ofReal_zero]
      exact zero_le

end BlockBand.Angular.AssemblyGood
