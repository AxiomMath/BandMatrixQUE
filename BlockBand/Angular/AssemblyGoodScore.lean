module

public import BlockBand.Angular.StepTwoGlue
public import BlockBand.Angular.AssemblyGoodSigned
public import BlockBand.Angular.RatioBasic
public import BlockBand.DeterminantScore.Statements

/-!
# The score term of the angular estimate: `‖∇Zf‖ ≤ Zf ‖score‖`

* `angularDensity_smul`, `pairAngularDensity_smul`, `stepOneDensity_smul`: the density is
  invariant under every nonzero complex scalar (frames of `v^⊥` are frames of `(cv)^⊥`,
  `isFrame_smul`, and `angularDensity_eq`). This is the phase invariance of `𝔷`.
* `gradNorm_le_of_horizontal` (generic): for `f ≥ 0` differentiable at `v ≠ 0`, invariant along
  `r v` (`r > 0`) and `c v` (`|c| = 1`), the gradient is horizontal (`∇f(v) ⊥ v`) and, if
  `Df(v) = f(v)·L` with `L h = Re(h* s)` on `h ⊥ v`, then `‖∇f(v)‖ ≤ f(v)‖s‖` (the case
  `f(v) = 0` is a minimum).
* `gradNorm_stepOneDensity_le`: for the angular density `Zf = c_{2W,t}(n/2)𝔷_E`, Hermitian
  blocks, a non-pole energy, a pair frame and a unit `v`,
  `‖∇Zf(v)‖ ≤ Zf(v) ‖score(ω, E, v)‖` (`score = -4R̄QK₀v`), from `DeterminantScoreStatement.exact`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.AssemblyGood

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.FiberAngular
open BlockBand.Angular.DetFactor BlockBand.Angular.DegreeZero BlockBand.Angular.Stein.AngularData
open BlockBand.Angular.Ratio BlockBand.Angular.Stein BlockBand.Angular.StepTwoGlue
open BlockBand.Angular.ProjectiveStein BlockBand.DeterminantScore
open scoped ENNReal NNReal ComplexConjugate

/-!
## Phase invariance of the density
-/

section Phase

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}

theorem angularDensity_smul (hcard : Fintype.card ι = m + 1) (t : ℝ≥0) {K : Matrix ι ι ℂ}
    (hK : K.IsHermitian) (ℓ : ℕ) {c : ℂ} (hc : c ≠ 0) (v : ι → ℂ) :
    angularDensity m t ℓ K (c • v) = angularDensity m t ℓ K v := by
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨U, hU⟩ := exists_isFrame hcard hv
  have hcv : c • v ≠ 0 := smul_ne_zero hc hv
  rw [angularDensity_eq hcard t hK ℓ hcv ((isFrame_smul hc).2 hU), angularDensity_eq hcard t hK ℓ hv hU]

variable (p : BlockBand.Parameters) (i : ZMod p.n)

theorem pairAngularDensity_smul (α : Fin p.N) (s : ℝ) {ω : SplitState p i}
    (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian) (E : ℝ) {c : ℂ} (hc : c ≠ 0)
    (v : PairSite p i → ℂ) :
    pairAngularDensity p i α s ω E (c • v) = pairAngularDensity p i α s ω E v := by
  unfold pairAngularDensity
  split_ifs
  · exact angularDensity_smul (card_pairSite_eq p i) _ (pairK_isHermitian p i hR hV E) _ hc v
  · rfl

theorem stepOneDensity_smul (α : Fin p.N) (s : ℝ) {ω : SplitState p i}
    (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian) (E : ℝ) {c : ℂ} (hc : c ≠ 0)
    (v : PairSite p i → ℂ) :
    stepOneDensity p i α s ω E (c • v) = stepOneDensity p i α s ω E v := by
  unfold stepOneDensity
  rw [pairAngularDensity_smul p i α s hR hV E hc v]

end Phase

/-!
## Horizontal gradients
-/

section Gradient

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem fderiv_eq_zero_of_const_curve {f : (ι → ℂ) → ℝ} {v : ι → ℂ}
    (hfd : DifferentiableAt ℝ f v) {γ : ℝ → (ι → ℂ)} {w : ι → ℂ} (hγ : HasDerivAt γ w 0)
    (h0 : γ 0 = v) (hc : ∀ᶠ t in nhds (0 : ℝ), f (γ t) = f v) : fderiv ℝ f v w = 0 := by
  have h1 : HasDerivAt (fun t => f (γ t)) (fderiv ℝ f v w) 0 := by
    have := (h0 ▸ hfd).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ
    rw [h0] at this
    exact this
  have h2 : HasDerivAt (fun t => f (γ t)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (f v)).congr_of_eventuallyEq hc
  exact h1.unique h2

/-- **The gradient of a degree-zero phase-invariant function is horizontal and bounded by its
horizontal derivative.** -/
theorem gradNorm_le_of_horizontal {f : (ι → ℂ) → ℝ} {v : ι → ℂ} (hf0 : ∀ z, 0 ≤ f z)
    (hfd : DifferentiableAt ℝ f v) (hsc : ∀ r : ℝ, 0 < r → f (r • v) = f v)
    (hph : ∀ c : ℂ, ‖c‖ = 1 → f (c • v) = f v) (s : ι → ℂ)
    (hder : f v ≠ 0 → ∃ L : (ι → ℂ) →L[ℝ] ℝ, HasFDerivAt f (f v • L) v ∧
      ∀ h : ι → ℂ, star h ⬝ᵥ v = 0 → L h = (star h ⬝ᵥ s).re) :
    gradNorm f v ≤ f v * l2Norm s := by
  set g := grad f v with hgdef
  -- radial and phase directions
  have hD1 : fderiv ℝ f v v = 0 := by
    refine fderiv_eq_zero_of_const_curve hfd (γ := fun t => v + t • v) ?_ (by simp) ?_
    · simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add v
    · filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with t ht
      have : v + t • v = (1 + t) • v := by rw [add_smul, one_smul]
      rw [this, hsc _ (by simp only [Set.mem_Ioi] at ht; linarith)]
  have hD2 : fderiv ℝ f v (Complex.I • v) = 0 := by
    have hc : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) Complex.I 0 := by
      have h1 := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp
      simpa using h1
    refine fderiv_eq_zero_of_const_curve hfd
      (γ := fun t => Complex.exp ((t : ℂ) * Complex.I) • v) (hc.smul_const v)
      (by simp) (Filter.Eventually.of_forall fun t => hph _ (Complex.norm_exp_ofReal_mul_I t))
  have hre : ∀ w, fderiv ℝ f v w = reInner w g := fun w => fderiv_eq_reInner_grad f v w
  have hsq : l2Norm g ^ 2 = fderiv ℝ f v g := by
    rw [hre, reInner_self, l2Norm_sq_eq]
  have hg0 : 0 ≤ l2Norm g := Real.sqrt_nonneg _
  have hs0 : 0 ≤ l2Norm s := Real.sqrt_nonneg _
  have hfv := hf0 v
  -- horizontality: `g* v = 0`
  have hz : star g ⬝ᵥ v = 0 := by
    have e1 : (∑ a, conj (v a) * g a).re = 0 := by
      have := hre v; rw [hD1] at this; unfold reInner at this; linarith
    have e2 : (∑ a, conj (v a) * g a).im = 0 := by
      have := hre (Complex.I • v); rw [hD2] at this; unfold reInner at this
      have h' : (∑ a, conj ((Complex.I • v) a) * g a) = -Complex.I * ∑ a, conj (v a) * g a := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I]; ring
      rw [h'] at this
      simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im] at this
      linarith
    have hzero : (∑ a, conj (v a) * g a) = 0 := Complex.ext e1 e2
    have : star g ⬝ᵥ v = conj (∑ a, conj (v a) * g a) := by
      simp only [dotProduct, Pi.star_apply, map_sum, map_mul, Complex.conj_conj, Complex.star_def]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    rw [this, hzero, map_zero]
  by_cases hv0 : f v = 0
  · -- a minimum: the derivative vanishes
    have hmin : IsLocalMin f v := Filter.Eventually.of_forall fun z => by rw [hv0]; exact hf0 z
    have hD : fderiv ℝ f v = 0 := hmin.fderiv_eq_zero
    have : l2Norm g ^ 2 = 0 := by rw [hsq, hD]; rfl
    have hg : l2Norm g = 0 := by nlinarith
    show l2Norm g ≤ _
    rw [hg, hv0, zero_mul]
  · obtain ⟨L, hL, hLh⟩ := hder hv0
    have hD : fderiv ℝ f v = f v • L := hL.fderiv
    have hDg : fderiv ℝ f v g = f v * (star g ⬝ᵥ s).re := by
      rw [hD, _root_.smul_apply, smul_eq_mul, hLh g hz]
    have hcs : (star g ⬝ᵥ s).re ≤ l2Norm g * l2Norm s := by
      have h := abs_reInner_le g s
      have : reInner g s = (star g ⬝ᵥ s).re := by
        unfold reInner; simp only [dotProduct, Pi.star_apply, Complex.star_def]
      rw [this] at h
      exact (le_abs_self _).trans h
    have key : l2Norm g ^ 2 ≤ f v * l2Norm s * l2Norm g := by
      rw [hsq, hDg]
      calc f v * (star g ⬝ᵥ s).re ≤ f v * (l2Norm g * l2Norm s) :=
            mul_le_mul_of_nonneg_left hcs hfv
        _ = _ := by ring
    show l2Norm g ≤ _
    rcases hg0.lt_or_eq with hpos | hzero
    · nlinarith
    · rw [← hzero]; positivity

end Gradient

/-!
## The angular density
-/

section Density

variable {p : BlockBand.Parameters} {i : ZMod p.n}

theorem normalize_eq_smul (z : PairSite p i → ℂ) :
    FiberAngular.normalize z = ((l2Norm z)⁻¹ : ℂ) • z := rfl

/-- **`‖∇Zf(v)‖ ≤ Zf(v)‖score‖`** for the angular density, from the exact
clause of the determinant score theorem. -/
theorem gradNorm_stepOneDensity_le (hScore : DeterminantScoreStatement) (α : Fin p.N) {s : ℝ}
    (hs : 0 < s) {U : FrameMap p i} (hU : IsPairFrame p i U) {ω : SplitState p i}
    (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian) {E : ℝ} (hE : (ω.1 - (E : ℂ) • 1).det ≠ 0)
    {v : PairSite p i → ℂ} (hv : l2Norm v = 1) :
    gradNorm (stepOneDensity p i α s ω E) v ≤
      stepOneDensity p i α s ω E v * l2Norm (score α s U (ω, E, v)) := by
  have hv0 : v ≠ 0 := by
    intro h; rw [h] at hv; simp [l2Norm] at hv
  set c : ℝ := coareaConstant (2 * p.W) (pairTime p s) * ((p.n : ℝ) / 2)
    with hcdef
  set f := pairAngularDensity p i α s ω E with hfdef
  have hZ : stepOneDensity p i α s ω E = fun z => c * f z := rfl
  have hfc := contDiffOn_pairAngularDensity α s hR hV E
  have hopen : {z : PairSite p i → ℂ | z ≠ 0} ∈ nhds v := isOpen_ne.mem_nhds hv0
  have hfd : DifferentiableAt ℝ f v :=
    (hfc.differentiableOn one_ne_zero).differentiableAt hopen
  refine gradNorm_le_of_horizontal (stepOneDensity_nonneg α s hR hV E)
    (by rw [hZ]; exact hfd.const_mul c)
    (fun r hr => by
      show c * f (r • v) = c * f v
      exact congrArg (c * ·) (isScaleInvariant_pairAngularDensity α s hR hV E v r hr))
    (fun c' hc' => stepOneDensity_smul p i α s hR hV E
      (by intro h; rw [h, norm_zero] at hc'; exact zero_ne_one hc') v) _ ?_
  intro hne
  have hc0 : c ≠ 0 := by intro h; apply hne; rw [hZ]; simp [h]
  have hf0 : f v ≠ 0 := by intro h; apply hne; rw [hZ]; simp [h]
  have hfpos : 0 < f v := lt_of_le_of_ne (pairAngularDensity_nonneg α s hR hV E v) (Ne.symm hf0)
  have hdet : detFactor p i α s U ω E v ≠ 0 := by
    rw [detFactor_eq_ofReal p i α s hU hR hV E hv]
    exact (ENNReal.ofReal_pos.2 hfpos).ne'
  obtain ⟨L, hL, hLh⟩ := hScore.exact p α i s hs U hU ω hR hV E hE v hv hdet
  -- the log-derivative of `f`
  have hloc : (fun z => Real.log (detFactor p i α s U ω E (FiberAngular.normalize z)).toReal)
      =ᶠ[nhds v] fun z => Real.log (f z) := by
    filter_upwards [hopen] with z hz
    have hz1 : l2Norm (FiberAngular.normalize z) = 1 := l2Norm_normalize hz
    rw [detFactor_eq_ofReal p i α s hU hR hV E hz1,
      ENNReal.toReal_ofReal (pairAngularDensity_nonneg α s hR hV E _), normalize_eq_smul,
      pairAngularDensity_smul p i α s hR hV E (by
        have := (l2Norm_pos_of_ne_zero hz).ne'
        exact_mod_cast inv_ne_zero this) z]
  have hlogf : HasFDerivAt (fun z => Real.log (f z)) L v := hL.congr_of_eventuallyEq hloc.symm
  have hlog2 : HasFDerivAt (fun z => Real.log (f z)) ((f v)⁻¹ • fderiv ℝ f v) v := by
    have := hfd.hasFDerivAt.log hf0
    simpa [smul_eq_mul, div_eq_inv_mul] using this
  have hLeq : L = (f v)⁻¹ • fderiv ℝ f v := hlogf.unique hlog2
  have hDf : fderiv ℝ f v = f v • L := by
    rw [hLeq, smul_smul, mul_inv_cancel₀ hf0, one_smul]
  refine ⟨L, ?_, hLh⟩
  have h := hfd.hasFDerivAt.const_mul c
  rw [hDf, smul_smul] at h
  rw [hZ]
  exact h

end Density

end BlockBand.Angular.AssemblyGood
