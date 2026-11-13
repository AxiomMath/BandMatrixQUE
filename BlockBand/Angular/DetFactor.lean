module

public import BlockBand.Angular.DetFactorFrame
public import BlockBand.Angular.FiberAngular
public import BlockBand.Window.Count.RefinedCount

/-!
# The coarea determinant factor as an angular density `𝔷`

Generic part (`ι` finite, `card ι = m + 1`, `K` Hermitian, `G ~ G_m(t)` = `hermGaussian m t`,
every `t ≥ 0`, every sector `ℓ`):
* `angularDensity m t ℓ K v` — **frame-free definition**: `Re Z_ℓ(UᴴKU)` for *some*
  orthonormal frame `U` of `v^⊥` (`0` if none). `angularDensity_eq`: it equals
  `Re Z_ℓ(UᴴKU)` for **every** frame `U` of `v ≠ 0` (unitary invariance of `G_m(t)`,
  `sectorMass_frame_indep`).
* `angularDensity_nonneg`, `isScaleInvariant_angularDensity`,
  `contDiffOn_angularDensity` (`C¹` on `{v ≠ 0}`: on each patch `{v j₀ ≠ 0}` it is
  `Re ∘ massCoord ∘ coord ∘ (v ↦ U_vᴴKU_v)` with the smooth Householder frame and the `C¹`
  coordinate sector mass `contDiff_massCoord`), `measurable_angularDensity`.
* `hasFDerivAt_angularDensity` — the derivative (as in the sector integration-by-parts lemma):
  `D𝔷(v₀)[h] = Re(2 E[1{N_-=ℓ} P² Tr(R ∂K)])`, `K(v) = U_vᴴKU_v` (Householder frame at `v₀`),
  `∂K = paramDeriv K v₀ h`, from `mass_hasFDerivAt`.

Pair specialization (`ι = PairSite p i`, `m = 2W - 1`, `K₀ = F(E) - E`, `t = pairTime p s`,
zero-based rank `α`, `ℓ = α - N_R(E)`):
* `pairAngularDensity` and **`detFactor_eq_ofReal`**: for every measurable pair frame `U`
  (`IsPairFrame`), Hermitian blocks of `ω` and unit `v`,
  `detFactor p i α s U ω E v = ofReal (pairAngularDensity p i α s ω E v)`; hence
  `detFactor_lt_top` (finiteness: Gaussian polynomial moments, `integrable_cut`).
* `pairAngularDensity_nonneg`, `isScaleInvariant_pairAngularDensity`,
  `contDiffOn_pairAngularDensity`, `measurable_pairAngularDensity`: the four hypotheses on `Zf`
  of `angular_ratio`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.DetFactor

open MeasureTheory Matrix Filter
open BlockBand.DeterminantScore.Sector
open BlockBand.Internal.Contracts
open BlockBand.Angular.DegreeZero
open scoped NNReal Topology ENNReal

/-!
## Reality and nonnegativity of the sector mass
-/

section Mass

variable {m : ℕ}

theorem det_im_eq_zero {κ : Type} [Fintype κ] [DecidableEq κ] {M : Matrix κ κ ℂ}
    (hM : M.IsHermitian) : M.det.im = 0 := by
  have h := congrArg Matrix.det hM.eq
  rw [det_conjTranspose] at h
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

theorem integrable_sectorDetSq (t : ℝ≥0) {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian)
    (ℓ : ℕ) : Integrable (sectorDetSq A ℓ) (hermGaussian m t) := by
  rw [sectorDetSq_eq_cut, hermGaussian_eq]
  exact integrable_cut hA ℓ _ _

theorem re_sectorDetSq_nonneg {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) (ℓ : ℕ)
    (x : HermCoord m → ℝ) : 0 ≤ (sectorDetSq A ℓ x).re := by
  unfold sectorDetSq
  split_ifs
  · rw [pow_two, Complex.mul_re, det_im_eq_zero (hA.add (isHermitian_hermOfCoord x))]
    nlinarith [sq_nonneg (A + hermOfCoord x).det.re]
  · simp

theorem re_sectorMass_eq (t : ℝ≥0) {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian)
    (ℓ : ℕ) : (sectorMass m t A ℓ).re = ∫ x, (sectorDetSq A ℓ x).re ∂hermGaussian m t := by
  unfold sectorMass
  exact (integral_re (integrable_sectorDetSq t hA ℓ)).symm

theorem re_sectorMass_nonneg (t : ℝ≥0) {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian)
    (ℓ : ℕ) : 0 ≤ (sectorMass m t A ℓ).re := by
  rw [re_sectorMass_eq t hA ℓ]
  exact integral_nonneg fun x => re_sectorDetSq_nonneg hA ℓ x

end Mass

/-!
## The frame-free angular density
-/

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The angular density** `𝔷(v) = E[det(UᴴKU + G_m(t))² 1{N_-(UᴴKU + G) = ℓ}]` for an
orthonormal frame `U` of `v^⊥` (frame independent: `angularDensity_eq`; `0` if there is no
frame). -/
def angularDensity (m : ℕ) (t : ℝ≥0) (ℓ : ℕ) (K : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ := by
  classical
  exact if h : ∃ U : Matrix ι (Fin m) ℂ, IsFrame U v then
    (sectorMass m t ((Classical.choose h)ᴴ * K * Classical.choose h) ℓ).re
  else 0

variable {m : ℕ}

/-- **Frame independence**: `𝔷(v) = Re Z_ℓ(UᴴKU)` for every orthonormal frame `U` of
`v^⊥`, `v ≠ 0`. -/
theorem angularDensity_eq (hcard : Fintype.card ι = m + 1) (t : ℝ≥0) {K : Matrix ι ι ℂ}
    (hK : K.IsHermitian) (ℓ : ℕ) {U : Matrix ι (Fin m) ℂ} {v : ι → ℂ} (hv : v ≠ 0)
    (hU : IsFrame U v) : angularDensity m t ℓ K v = (sectorMass m t (Uᴴ * K * U) ℓ).re := by
  have h : ∃ U : Matrix ι (Fin m) ℂ, IsFrame U v := ⟨U, hU⟩
  rw [angularDensity, dite_eq_left_of_eq_true (eq_true h),
    sectorMass_frame_indep hcard t hK hv hU (Classical.choose_spec h)]

/-- `𝔷 ≥ 0`. -/
theorem angularDensity_nonneg (t : ℝ≥0) {K : Matrix ι ι ℂ} (hK : K.IsHermitian) (ℓ : ℕ)
    (v : ι → ℂ) : 0 ≤ angularDensity m t ℓ K v := by
  unfold angularDensity
  split_ifs with h
  · exact re_sectorMass_nonneg t (isHermitian_conjTranspose_mul_mul _ hK) ℓ
  · exact le_rfl

/-- `𝔷(rv) = 𝔷(v)` for `r > 0`. -/
theorem isScaleInvariant_angularDensity (hcard : Fintype.card ι = m + 1) (t : ℝ≥0)
    {K : Matrix ι ι ℂ} (hK : K.IsHermitian) (ℓ : ℕ) :
    IsScaleInvariant (angularDensity m t ℓ K) := by
  intro v r hr
  by_cases hv : v = 0
  · rw [hv, smul_zero]
  obtain ⟨U, hU⟩ := exists_isFrame hcard hv
  have hrv : r • v ≠ 0 := smul_ne_zero hr.ne' hv
  rw [angularDensity_eq hcard t hK ℓ hv hU,
    angularDensity_eq hcard t hK ℓ hrv ((isFrame_real_smul hr.ne').2 hU)]

/-- On the patch `{v j₀ ≠ 0}`, `𝔷 = Re ∘ massCoord ∘ coord ∘ (v ↦ U_vᴴKU_v)` with the
Householder frame. -/
theorem angularDensity_eq_patch (hcard : Fintype.card ι = m + 1) (t : ℝ≥0)
    {K : Matrix ι ι ℂ} (hK : K.IsHermitian) (ℓ : ℕ) {j₀ : ι} {e : Fin m → ι}
    (he : Function.Injective e) (hne : ∀ k, e k ≠ j₀) {v : ι → ℂ} (hv : v ∈ patch j₀) :
    angularDensity m t ℓ K v =
      (massCoord m t ℓ (coordOfMatrix ((hhFrame j₀ e v)ᴴ * K * hhFrame j₀ e v))).re := by
  have hv0 : v ≠ 0 := fun h => hv (by rw [h]; rfl)
  rw [angularDensity_eq hcard t hK ℓ hv0 (isFrame_hhFrame j₀ e he hne hv),
    sectorMass_eq_massCoord t (isHermitian_conjTranspose_mul_mul _ hK)]

theorem exists_patch {v : ι → ℂ} (hv : v ≠ 0) : ∃ j₀, v ∈ patch j₀ := by
  by_contra h
  push Not at h
  exact hv (funext fun j => by simpa [patch] using h j)

/-- **`𝔷` is `C¹` off the origin.** -/
theorem contDiffOn_angularDensity (hcard : Fintype.card ι = m + 1) (t : ℝ≥0)
    {K : Matrix ι ι ℂ} (hK : K.IsHermitian) (ℓ : ℕ) :
    ContDiffOn ℝ 1 (angularDensity m t ℓ K) {z | z ≠ 0} := by
  refine contDiffOn_of_locally_contDiffOn fun v hv => ?_
  obtain ⟨j₀, hj₀⟩ := exists_patch hv
  obtain ⟨e, he, hne⟩ := exists_frameEmbedding hcard j₀
  refine ⟨patch j₀, isOpen_patch j₀, hj₀, ?_⟩
  have hg : ContDiffOn ℝ 1 (fun v =>
      (massCoord m t ℓ (coordOfMatrix ((hhFrame j₀ e v)ᴴ * K * hhFrame j₀ e v))).re)
      (patch j₀) :=
    Complex.reCLM.contDiff.comp_contDiffOn
      ((contDiff_massCoord t ℓ).comp_contDiffOn (contDiffOn_coord_hhCompress j₀ e K))
  exact (hg.mono Set.inter_subset_right).congr fun v hv =>
    angularDensity_eq_patch hcard t hK ℓ he hne hv.2

/-- `𝔷` is Borel measurable. -/
theorem measurable_angularDensity (hcard : Fintype.card ι = m + 1) (t : ℝ≥0)
    {K : Matrix ι ι ℂ} (hK : K.IsHermitian) (ℓ : ℕ) :
    Measurable (angularDensity m t ℓ K) :=
  measurable_of_continuousOn_compl_singleton 0
    (contDiffOn_angularDensity hcard t hK ℓ).continuousOn

/-- **The derivative of `𝔷`** (as in the sector integration-by-parts lemma): with the Householder frame
`U_v` on the patch of `v₀` and `K(v) = U_vᴴKU_v`,
`D𝔷(v₀)[h] = Re(2 E[1{N_-(K(v₀)+G)=ℓ} P² Tr(R ∂K)])`, `P = det(K(v₀)+G)`,
`R = (K(v₀)+G)⁻¹`, `∂K = paramDeriv K v₀ h`. -/
theorem hasFDerivAt_angularDensity (hcard : Fintype.card ι = m + 1) (t : ℝ≥0)
    {K : Matrix ι ι ℂ} (hK : K.IsHermitian) (ℓ : ℕ) {j₀ : ι} {e : Fin m → ι}
    (he : Function.Injective e) (hne : ∀ k, e k ≠ j₀) {v₀ : ι → ℂ} (hv₀ : v₀ ∈ patch j₀) :
    ∃ L : (ι → ℂ) →L[ℝ] ℂ,
      HasFDerivAt (angularDensity m t ℓ K) (Complex.reCLM.comp L) v₀ ∧
      ∀ h : ι → ℂ, L h = 2 * ∫ x,
        (if InSector ((hhFrame j₀ e v₀)ᴴ * K * hhFrame j₀ e v₀) ℓ x then
          ((hhFrame j₀ e v₀)ᴴ * K * hhFrame j₀ e v₀ + hermOfCoord x).det ^ 2 *
            (((hhFrame j₀ e v₀)ᴴ * K * hhFrame j₀ e v₀ + hermOfCoord x)⁻¹ *
              paramDeriv (fun v => (hhFrame j₀ e v)ᴴ * K * hhFrame j₀ e v) v₀ h).trace
        else 0) ∂hermGaussian m t := by
  have hnhds : patch j₀ ∈ 𝓝 v₀ := (isOpen_patch j₀).mem_nhds hv₀
  have hd : ∀ a b, DifferentiableAt ℝ
      (fun v => ((hhFrame j₀ e v)ᴴ * K * hhFrame j₀ e v) a b) v₀ := fun a b =>
    ((contDiffOn_hhCompress_apply j₀ e K a b (n := 1)).differentiableOn one_ne_zero
      v₀ hv₀).differentiableAt hnhds
  obtain ⟨L, hL, hLf⟩ := mass_hasFDerivAt t ℓ (fun v => (hhFrame j₀ e v)ᴴ * K * hhFrame j₀ e v)
    v₀ (fun v => isHermitian_conjTranspose_mul_mul _ hK) hd
  refine ⟨L, ?_, hLf⟩
  have hre := (Complex.reCLM.hasFDerivAt (x := sectorMass m t
    ((hhFrame j₀ e v₀)ᴴ * K * hhFrame j₀ e v₀) ℓ)).comp v₀ hL
  refine hre.congr_of_eventuallyEq ?_
  filter_upwards [hnhds] with v hv
  have hv0 : v ≠ 0 := fun h => hv (by rw [h]; rfl)
  rw [angularDensity_eq hcard t hK ℓ hv0 (isFrame_hhFrame j₀ e he hne hv)]
  rfl

end Generic

/-!
## The pair determinant factor
-/

section Pair

open BlockBand.Angular.FiberAngular CoareaPalm BlockBand.Coarea

variable (p : BlockBand.Parameters) (i : ZMod p.n)

theorem card_pairSite_eq : Fintype.card (PairSite p i) = (2 * p.W - 1) + 1 := by
  rw [card_pairSite]; have := p.W_pos; omega

/-- `K₀ = F(E) - E` on the exposed pair. -/
def pairK (ω : SplitState p i) (E : ℝ) : PairMatrix p i :=
  physicalCoareaF ω.1 ω.2.1 ω.2.2 E - (E : ℂ) • 1

theorem pairK_isHermitian {ω : SplitState p i} (hR : ω.1.IsHermitian)
    (hV : ω.2.2.IsHermitian) (E : ℝ) : (pairK p i ω E).IsHermitian := by
  refine (physicalCoareaF_isHermitian hR ω.2.1 hV E).sub ?_
  unfold IsHermitian; rw [conjTranspose_smul, conjTranspose_one]; simp

/-- **The pair angular density** `𝔷_E(v)`: the angular density of `K₀ = F(E) - E`
at `t = pairTime p s` in the sector `ℓ = α - N_R(E)` (zero-based rank `α`; `0` when
`N_R(E) > α`, where the inertia indicator is never satisfied). -/
def pairAngularDensity (α : Fin p.N) (s : ℝ) (ω : SplitState p i) (E : ℝ)
    (v : PairSite p i → ℂ) : ℝ :=
  if negativeCount (ω.1 - (E : ℂ) • 1) ≤ α.val then
    angularDensity (2 * p.W - 1) (pairTime p s) (α.val - negativeCount (ω.1 - (E : ℂ) • 1))
      (pairK p i ω E) v
  else 0

theorem measurable_negativeCount_nat {κ : Type} [Fintype κ] [DecidableEq κ] :
    Measurable (fun M : Matrix κ κ ℂ => negativeCount M) := by
  refine measurable_to_countable' fun k => ?_
  have h : (fun M : Matrix κ κ ℂ => negativeCount M) ⁻¹' {k} =
      (fun M : Matrix κ κ ℂ => (negativeCount M : ℝ)) ⁻¹' {(k : ℝ)} := by
    ext M; simp
  rw [h]
  exact BlockBand.Window.Count.measurable_negativeCount_real (measurableSet_singleton _)

/-- **The coarea determinant factor is the angular density**: for every measurable pair frame,
Hermitian blocks and unit `v`, `detFactor = ofReal 𝔷_E(v)`. -/
theorem detFactor_eq_ofReal (α : Fin p.N) (s : ℝ)
    {U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ} (hU : IsPairFrame p i U)
    {ω : SplitState p i} (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian) (E : ℝ)
    {v : PairSite p i → ℂ} (hv : l2Norm v = 1) :
    detFactor p i α s U ω E v = ENNReal.ofReal (pairAngularDensity p i α s ω E v) := by
  set N := negativeCount (ω.1 - (E : ℂ) • 1)
  set A : Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ := (U v)ᴴ * pairK p i ω E * U v
  have hA : A.IsHermitian := isHermitian_conjTranspose_mul_mul _ (pairK_isHermitian p i hR hV E)
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp [l2Norm] at hv
  have hmeas : Measurable fun G' : Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ =>
      ENNReal.ofReal (Complex.normSq (A + G').det) *
        (if negativeCount (A + G') + N = α.val then (1 : ℝ≥0∞) else 0) := by
    refine Measurable.mul ?_ (Measurable.ite ?_ measurable_const measurable_const)
    · exact ENNReal.measurable_ofReal.comp (Complex.continuous_normSq.comp
        (continuous_const.add continuous_id).matrix_det).measurable
    · exact (measurableSet_singleton _).preimage
        ((measurable_negativeCount_nat.comp (measurable_const_add A)).add_const N)
  have h1 : detFactor p i α s U ω E v = ∫⁻ x, ENNReal.ofReal (Complex.normSq
      (A + hermOfCoord x).det) * (if negativeCount (A + hermOfCoord x) + N = α.val then
        (1 : ℝ≥0∞) else 0) ∂hermGaussian (2 * p.W - 1) (pairTime p s) := by
    unfold detFactor
    simp_rw [frameM_eq_compress p i hU ω E hv]
    rw [← map_hermOfCoord_hermGaussian]
    exact lintegral_map hmeas continuous_hermOfCoord.measurable
  rw [h1]
  unfold pairAngularDensity
  split_ifs with hN
  · set ℓ := α.val - N
    have hi : Integrable (fun x => (sectorDetSq A ℓ x).re)
        (hermGaussian (2 * p.W - 1) (pairTime p s)) := (integrable_sectorDetSq _ hA ℓ).re
    rw [angularDensity_eq (card_pairSite_eq p i) (pairTime p s) (pairK_isHermitian p i hR hV E)
      ℓ hv0 (hU.2 v hv), re_sectorMass_eq _ hA ℓ,
      ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => re_sectorDetSq_nonneg hA ℓ x)]
    refine lintegral_congr fun x => ?_
    have him := det_im_eq_zero (hA.add (isHermitian_hermOfCoord x))
    unfold sectorDetSq InSector
    by_cases hx : negativeCount (A + hermOfCoord x) = ℓ
    · have hl : ℓ + N = α.val := by omega
      simp only [hx, hl, ↓reduceIte, mul_one]
      congr 1
      rw [Complex.normSq_apply, pow_two, Complex.mul_re, him]
      ring
    · have hx' : ¬ negativeCount (A + hermOfCoord x) + N = α.val := by omega
      simp only [hx', hx, ↓reduceIte, mul_zero, Complex.zero_re, ENNReal.ofReal_zero]
  · rw [ENNReal.ofReal_zero]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    · exact ae_of_all _ fun x => by
        have hx' : ¬ negativeCount (A + hermOfCoord x) + N = α.val := by omega
        simp [hx']

/-- **Finiteness** of the determinant factor. -/
theorem detFactor_lt_top (α : Fin p.N) (s : ℝ)
    {U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ} (hU : IsPairFrame p i U)
    {ω : SplitState p i} (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian) (E : ℝ)
    {v : PairSite p i → ℂ} (hv : l2Norm v = 1) : detFactor p i α s U ω E v < ⊤ := by
  rw [detFactor_eq_ofReal p i α s hU hR hV E hv]
  exact ENNReal.ofReal_lt_top

variable {p i}

theorem pairAngularDensity_nonneg (α : Fin p.N) (s : ℝ) {ω : SplitState p i}
    (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian) (E : ℝ) (v : PairSite p i → ℂ) :
    0 ≤ pairAngularDensity p i α s ω E v := by
  unfold pairAngularDensity
  split_ifs
  · exact angularDensity_nonneg _ (pairK_isHermitian p i hR hV E) _ v
  · exact le_rfl

theorem isScaleInvariant_pairAngularDensity (α : Fin p.N) (s : ℝ) {ω : SplitState p i}
    (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian) (E : ℝ) :
    IsScaleInvariant (pairAngularDensity p i α s ω E) := by
  intro v r hr
  unfold pairAngularDensity
  split_ifs
  · exact isScaleInvariant_angularDensity (card_pairSite_eq p i) _
      (pairK_isHermitian p i hR hV E) _ v r hr
  · rfl

theorem contDiffOn_pairAngularDensity (α : Fin p.N) (s : ℝ) {ω : SplitState p i}
    (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian) (E : ℝ) :
    ContDiffOn ℝ 1 (pairAngularDensity p i α s ω E) {z | z ≠ 0} := by
  unfold pairAngularDensity
  split_ifs
  · exact contDiffOn_angularDensity (card_pairSite_eq p i) _ (pairK_isHermitian p i hR hV E) _
  · exact contDiffOn_const

theorem measurable_pairAngularDensity (α : Fin p.N) (s : ℝ) {ω : SplitState p i}
    (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian) (E : ℝ) :
    Measurable (pairAngularDensity p i α s ω E) := by
  unfold pairAngularDensity
  split_ifs
  · exact measurable_angularDensity (card_pairSite_eq p i) _ (pairK_isHermitian p i hR hV E) _
  · exact measurable_const

end Pair

end BlockBand.Angular.DetFactor
