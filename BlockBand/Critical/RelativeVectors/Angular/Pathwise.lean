module

public import BlockBand.Critical.RelativeVectors.Angular.PhaseContinuity
public import BlockBand.Critical.RelativeVectors.Angular.Generator
public import BlockBand.Critical.RelativeVectors.Angular.Telescope

/-!
# The telescoping data of one sample path

For the setting with `F + G_t` Hermitian and continuous in `t` for every sample, gap level
`n > 0`, `σ = gapStop … s n`, and a space-time test (`IsSpaceTimeAngularTest`), every sample `ω`
gives `IsTelescopeData` with constants uniform in `ω` (`exists_isTelescopeData`), for

* the array path `arrPath x = frameArray V (F + G_{s+x})` and stop `stopTime = u ∧ σ`;
* the generator path `genPath v x = 𝒜(λ(F + G_{s+x})) h(v, ·) (arrPath x)`.

Ingredients: before `σ` the spectrum is simple and the couplings are `≤ n²/N` (`GapStop`); the
array has deterministic norm `≤ √N Σ|V_xa|`; `y ↦ ht(x, arrPath y)` is continuous at `x < σ` by
phase invariance (`PhaseContinuity`; `ht(x, ·)` inherits phase invariance from `h`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.Angular

open MeasureTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Foundations.Spectral BlockBand.Model.Construction BlockBand.Palm.MomentFlow
open scoped NNReal

variable {N r : ℕ} {Ω : Type*}

/-- The array path `x ↦ frameArray V (F + G_{s+x})`. -/
def arrPath (F : Ω → Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (V : Matrix (Fin N) (Fin r) ℂ) (s : ℝ≥0) (ω : Ω) (x : ℝ) : Fin N → Fin r → ℂ :=
  frameArray V (F ω + G (s + x.toNNReal) ω)

/-- The increasing eigenvalues along the path. -/
def eigPath (F : Ω → Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (s : ℝ≥0) (ω : Ω) (x : ℝ) : Fin N → ℝ :=
  fun ℓ => freshEigenvalue (F ω + G (s + x.toNNReal) ω) ℓ

/-- The generator of `h(v, ·)` along the path at time `x`. -/
def genPath (F : Ω → Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (V : Matrix (Fin N) (Fin r) ℂ) (s : ℝ≥0) (h : Ω → ℝ → (Fin N → Fin r → ℂ) → ℝ) (ω : Ω)
    (v x : ℝ) : ℝ :=
  complexAngularGenerator N r (eigPath F G s ω x) (h ω v) (arrPath F G V s ω x)

/-- The stopped horizon `u ∧ σ` as a real number. -/
def stopTime (σ : Ω → WithTop ℝ≥0) (u : ℝ≥0) (ω : Ω) : ℝ :=
  ((min (u : WithTop ℝ≥0) (σ ω)).untopA : ℝ)

theorem stopTime_nonneg (σ : Ω → WithTop ℝ≥0) (u : ℝ≥0) (ω : Ω) : 0 ≤ stopTime σ u ω :=
  NNReal.coe_nonneg _

theorem min_coe_ne_top (u : ℝ≥0) (w : WithTop ℝ≥0) : min (u : WithTop ℝ≥0) w ≠ ⊤ :=
  ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)

theorem stopTime_le (σ : Ω → WithTop ℝ≥0) (u : ℝ≥0) (ω : Ω) : stopTime σ u ω ≤ u := by
  unfold stopTime
  have : (min (u : WithTop ℝ≥0) (σ ω)).untopA ≤ u :=
    (WithTop.untopA_le_iff (min_coe_ne_top u _)).2 (min_le_left _ _)
  exact_mod_cast this

theorem coe_lt_of_lt_stopTime {σ : Ω → WithTop ℝ≥0} {u : ℝ≥0} {ω : Ω} {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x < stopTime σ u ω) : ((x.toNNReal : ℝ≥0) : WithTop ℝ≥0) < σ ω := by
  unfold stopTime at hx
  have h1 : x.toNNReal < (min (u : WithTop ℝ≥0) (σ ω)).untopA := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal x hx0]; exact hx
  exact lt_of_lt_of_le ((WithTop.lt_untopA_iff (min_coe_ne_top u _)).1 h1) (min_le_right _ _)

/-- Simple spectrum from a positive gap (increasing ranks). -/
theorem hasSimpleSpectrum_of_gap' {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian) {δ : ℝ}
    (hδ : 0 < δ) (h : ∀ i j : Fin N, i ≠ j → δ < |dysonEigenvalue N K i - dysonEigenvalue N K j|) :
    HasSimpleSpectrum N K := by
  rw [hasSimpleSpectrum_iff_strictMono hK]
  have hmono : Monotone (freshEigenvalue K) := by
    intro i j hij
    simp only [freshEigenvalue, rawIncreasingEigenvalue_eq _ K hK]
    exact increasingEigenvalue_monotone hK (Fin.cast_le_cast _ |>.2 hij)
  refine hmono.strictMono_of_injective fun i j hij => ?_
  by_contra hne
  have hne' : i.rev ≠ j.rev := fun e => hne (Fin.rev_injective e)
  have := h i.rev j.rev hne'
  rw [dysonEigenvalue_rev hK, dysonEigenvalue_rev hK, hij, sub_self, abs_zero] at this
  linarith

theorem measurable_frameArray (V : Matrix (Fin N) (Fin r) ℂ) :
    Measurable (frameArray V : Matrix (Fin N) (Fin N) ℂ → Fin N → Fin r → ℂ) := by
  refine measurable_pi_iff.2 fun i => ?_
  have hu : Measurable fun K : Matrix (Fin N) (Fin N) ℂ => freshEigenvector K i :=
    measurable_pi_iff.2 fun x => measurable_rawOrderedColumnSelection _ x
  have hc : Continuous fun v : Fin N → ℂ => ((Real.sqrt N : ℝ) : ℂ) • (Vᴴ *ᵥ v) :=
    (continuous_const (y := ((Real.sqrt N : ℝ) : ℂ))).smul
      (Continuous.matrix_mulVec continuous_const continuous_id)
  exact hc.measurable.comp hu

theorem continuous_rotX (i j : Fin N) : Continuous (rotX (r := r) i j) := by
  refine continuous_pi fun k => ?_
  unfold rotX
  split_ifs
  · exact continuous_apply j
  · exact (continuous_apply i).neg
  · exact continuous_const

theorem continuous_rotY (i j : Fin N) : Continuous (rotY (r := r) i j) := by
  refine continuous_pi fun k => ?_
  unfold rotY
  split_ifs
  · exact (continuous_const (y := Complex.I)).smul
      (continuous_apply j : Continuous fun z : Fin N → Fin r → ℂ => z j)
  · exact (continuous_const (y := Complex.I)).smul
      (continuous_apply i : Continuous fun z : Fin N → Fin r → ℂ => z i)
  · exact continuous_const

theorem continuous_fieldSq {W : (Fin N → Fin r → ℂ) → (Fin N → Fin r → ℂ)} (hW : Continuous W)
    {g : (Fin N → Fin r → ℂ) → ℝ} (hg : ContDiff ℝ 2 g) : Continuous (fieldSq W g) := by
  have h1 : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  have h2 : Continuous (fderiv ℝ (fderiv ℝ g)) :=
    (hg.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by simp)
  unfold fieldSq
  exact ((h2.clm_apply hW).clm_apply hW).add (h1.clm_apply (hW.comp hW))

theorem measurable_dysonCoupling (i j : Fin N) :
    Measurable fun lam : Fin N → ℝ => dysonCoupling N lam i j := by
  unfold dysonCoupling
  exact measurable_const.div (measurable_const.mul
    (((measurable_pi_apply i).sub (measurable_pi_apply j)).pow_const 2))

theorem measurable_generator_comp {α : Type*} [MeasurableSpace α] {lam : α → Fin N → ℝ}
    {z : α → Fin N → Fin r → ℂ} (hlam : Measurable lam) (hz : Measurable z)
    {g : (Fin N → Fin r → ℂ) → ℝ} (hg : ContDiff ℝ 2 g) :
    Measurable fun x => complexAngularGenerator N r (lam x) g (z x) := by
  unfold complexAngularGenerator
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _
    fun j _ => ((measurable_dysonCoupling i j).comp hlam).mul ?_)
  exact (((continuous_fieldSq (continuous_rotX i j) hg).measurable.comp hz).add
    ((continuous_fieldSq (continuous_rotY i j) hg).measurable.comp hz))

/-- The time derivative of a phase-invariant family is phase invariant. -/
theorem isLabelPhaseInvariant_deriv {g gt : ℝ → (Fin N → Fin r → ℂ) → ℝ}
    (hg : ∀ v, IsLabelPhaseInvariant (g v)) {x : ℝ}
    (hd : ∀ z, HasDerivAt (fun v => g v z) (gt x z) x) : IsLabelPhaseInvariant (gt x) := by
  intro α z
  have e : (fun v => g v (fun i => Complex.exp ((α i : ℂ) * Complex.I) • z i)) =
      fun v => g v z := funext fun v => hg v α z
  have h1 := hd (fun i => Complex.exp ((α i : ℂ) * Complex.I) • z i)
  rw [e] at h1
  exact h1.unique (hd z)

theorem continuousOn_slice_fderiv {X : Type*} [TopologicalSpace X] {S : Set ℝ}
    {f : ℝ × (Fin N → Fin r → ℂ) → X}
    (hf : ContinuousOn f (S ×ˢ univ)) (z : Fin N → Fin r → ℂ) :
    ContinuousOn (fun v => f (v, z)) S :=
  hf.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ hv => ⟨hv, mem_univ _⟩)

variable {F : Ω → Matrix (Fin N) (Fin N) ℂ} {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}

theorem continuous_path (hGc : ∀ ω, Continuous fun t => G t ω) (s : ℝ≥0) (ω : Ω) :
    Continuous fun x : ℝ => F ω + G (s + x.toNNReal) ω :=
  continuous_const.add ((hGc ω).comp (continuous_const.add continuous_real_toNNReal))

/-- **Pathwise telescoping data**, with constants uniform in the sample. -/
theorem exists_isTelescopeData (hGc : ∀ ω, Continuous fun t => G t ω)
    (hH : ∀ t ω, (F ω + G t ω).IsHermitian) (s : ℝ≥0) (V : Matrix (Fin N) (Fin r) ℂ) {n : ℕ}
    (hn : 0 < n) {T : ℝ≥0} {𝓛 : MeasurableSpace Ω} {h ht : Ω → ℝ → (Fin N → Fin r → ℂ) → ℝ}
    (hT : IsSpaceTimeAngularTest 𝓛 (gapStop N (fun t ω => F ω + G t ω) s n) T h ht)
    {u : ℝ≥0} (huT : u ≤ T) :
    ∃ C Ct Ma R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ ω, IsTelescopeData (h ω) (ht ω) (genPath F G V s h ω)
      (arrPath F G V s ω) (stopTime (gapStop N (fun t ω => F ω + G t ω) s n) u ω) u T
        C Ct Ma R := by
  obtain ⟨Cb, hCb⟩ := hT.bound
  obtain ⟨Ctm, hCt⟩ := hT.time_bound
  set σ := gapStop N (fun t ω => F ω + G t ω) s n
  set R := frameBound V
  have hR : 0 ≤ R := by simp only [R]; unfold frameBound; positivity
  refine ⟨max Cb 0, Ctm * (1 + R ^ 2), (N : ℝ) ^ 2 * ((n : ℝ) ^ 2 / N) * max Cb 0 * (R ^ 2 + R),
    R, le_max_right _ _, hR, fun ω => ?_⟩
  set t := stopTime σ u ω
  have htT : t ≤ T := (stopTime_le σ u ω).trans (by exact_mod_cast huT)
  have hgap : ∀ x ∈ Ioo 0 t, ∀ i j : Fin N, i ≠ j → 1 / (n : ℝ) <
      |dysonEigenvalue N (F ω + G (s + x.toNNReal) ω) i -
        dysonEigenvalue N (F ω + G (s + x.toNNReal) ω) j| := fun x hx i j hij =>
    gap_gt_of_lt_gapStop (fun t ω => F ω + G t ω) s n ω
      (coe_lt_of_lt_stopTime hx.1.le hx.2) hij
  have hsimple : ∀ x ∈ Ioo 0 t, HasSimpleSpectrum N (F ω + G (s + x.toNNReal) ω) :=
    fun x hx => hasSimpleSpectrum_of_gap' (hH _ ω) (by positivity) (hgap x hx)
  have hz : ∀ x, ‖arrPath F G V s ω x‖ ≤ R := fun x => norm_frameArray_le V _
  refine
    { t_nonneg := stopTime_nonneg σ u ω
      t_le := stopTime_le σ u ω
      u_le := by exact_mod_cast huT
      cont := (hT.continuousOn ω).1
      deriv := fun z v hv => hT.hasDerivAt ω z v hv
      ht_cont := fun z => continuousOn_slice_fderiv (hT.continuousOn ω).2.2.2 z
      bound := fun v hv z => (hCb ω v hv z).1.trans (le_max_left _ _)
      ht_bound := ?_
      phi_bound := fun x _ => hz x
      phi_cont := ?_
      a_meas := ?_
      a_bound := ?_
      a_cont := ?_ }
  · intro v hv z hzR
    have h1 := hCt ω v ⟨hv.1, hv.2.trans_le htT⟩ (coe_lt_of_lt_stopTime hv.1.le hv.2) z
    have hpos : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
    have hCt0 : 0 ≤ Ctm := by
      by_contra hneg
      push Not at hneg
      have : Ctm * (1 + ‖z‖ ^ 2) < 0 := mul_neg_of_neg_of_pos hneg hpos
      linarith [abs_nonneg (ht ω v z)]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hCt0)
    have : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzR 2
    linarith
  · intro x hx
    have hxT : x ∈ Ioo (0 : ℝ) T := ⟨hx.1, hx.2.trans_le htT⟩
    have hphase : IsLabelPhaseInvariant (ht ω x) :=
      isLabelPhaseInvariant_deriv (hT.phase ω) (fun z => hT.hasDerivAt ω z x hxT)
    have hopen : Ioo (0 : ℝ) T ×ˢ (univ : Set (Fin N → Fin r → ℂ)) ∈
        𝓝 (x, arrPath F G V s ω x) := (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hxT, mem_univ _⟩
    have hjoint := ((hT.continuousOn ω).2.2.2).continuousAt hopen
    have hzc : ContinuousAt (ht ω x) (frameArray V (F ω + G (s + x.toNNReal) ω)) :=
      hjoint.comp (f := fun z => (x, z)) (continuous_const.prodMk continuous_id).continuousAt
    exact tendsto_phaseInvariant_frameArray ((continuous_path hGc s ω).tendsto x)
      (fun y => hH _ ω) (hH _ ω) (hsimple x hx) V hphase hzc
  · intro v hv
    have hlam : Measurable fun x => eigPath F G s ω x :=
      measurable_pi_iff.2 fun ℓ =>
        (measurable_rawIncreasingEigenvalue _).comp (continuous_path hGc s ω).measurable
    have hzm : Measurable fun x => arrPath F G V s ω x :=
      (measurable_frameArray V).comp (continuous_path hGc s ω).measurable
    exact (measurable_generator_comp hlam hzm (hT.contDiff ω v hv)).aestronglyMeasurable
  · intro v hv x hx
    have hM : ∀ i j : Fin N, i < j → 0 ≤ dysonCoupling N (eigPath F G s ω x) i j ∧
        dysonCoupling N (eigPath F G s ω x) i j ≤ (n : ℝ) ^ 2 / N := fun i j hij =>
      dysonCoupling_fresh_le (fun t ω => F ω + G t ω) s n ω
        (coe_lt_of_lt_stopTime hx.1.le hx.2) (hH _ ω) hn hij
    have h1 := abs_complexAngularGenerator_le (eigPath F G s ω x) (by positivity) hM
      (h ω v) (arrPath F G V s ω x) ((hCb ω v hv _).2.1.trans (le_max_left Cb 0))
      ((hCb ω v hv _).2.2.trans (le_max_left Cb 0))
    refine h1.trans ?_
    have hzz : ‖arrPath F G V s ω x‖ ^ 2 + ‖arrPath F G V s ω x‖ ≤ R ^ 2 + R := by
      have := hz x
      have : ‖arrPath F G V s ω x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      linarith [hz x]
    exact mul_le_mul_of_nonneg_left hzz (by positivity)
  · intro x hx
    have hxI : x ∈ Icc (0 : ℝ) T := ⟨hx.1.le, (hx.2.trans_le htT).le⟩
    refine ContinuousOn.continuousWithinAt ?_ hxI
    set lam := eigPath F G s ω x
    set z := arrPath F G V s ω x
    have hD1 : ContinuousOn (fun v => fderiv ℝ (h ω v) z) (Icc 0 T) :=
      continuousOn_slice_fderiv (f := fun p : ℝ × (Fin N → Fin r → ℂ) => fderiv ℝ (h ω p.1) p.2)
        (hT.continuousOn ω).2.1 z
    have hD2 : ContinuousOn (fun v => fderiv ℝ (fderiv ℝ (h ω v)) z) (Icc 0 T) :=
      continuousOn_slice_fderiv
        (f := fun p : ℝ × (Fin N → Fin r → ℂ) => fderiv ℝ (fderiv ℝ (h ω p.1)) p.2)
        (hT.continuousOn ω).2.2.1 z
    have hfs : ∀ W : (Fin N → Fin r → ℂ) → (Fin N → Fin r → ℂ),
        ContinuousOn (fun v => fieldSq W (h ω v) z) (Icc 0 T) := fun W =>
      ((hD2.clm_apply continuousOn_const).clm_apply continuousOn_const).add
        (hD1.clm_apply continuousOn_const)
    unfold genPath complexAngularGenerator
    refine continuousOn_const.mul (continuousOn_finsetSum _ fun i _ =>
      continuousOn_finsetSum _ fun j _ => continuousOn_const.mul ((hfs _).add (hfs _)))

end BlockBand.Critical.RelativeVectors.Angular
