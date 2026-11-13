module

public import BlockBand.Endpoints.Response.TaggedConvexOrderWitnessDefs
public import BlockBand.Endpoints.Response.TaggedConvexOrderStepDrift
public import BlockBand.Endpoints.Response.ResponseVariancePath

/-!
# The explicit witness: sign clause and the reduction to the remainder-only input

Steps 2–4 of the proof of the tagged convex-order theorem.

**Results.**
* `tcw_X_eq`: `X = ‖Q^{1/2}h‖² = Z_{l;k}` (the witness lives on the tagged clock).
* `tcw_measurable_X`, `tcw_measurable_G`: measurability on the probed path space.
* `tcw_ae_drift`: under `probedClockLaw W b`, a.s. `0 ≤ X`, `0 ≤ G ≤ X²` (from `tcs_drift_sign`,
  `tcs_pathProjection` at paths with Hermitian blocks and invertible `𝓜`; both a.s. by
  `ae_growthPath_isHermitian` and `rv_ae_isUnit_fullPathMatrix`, the latter from
  `ConditionalBlockGUECount`).
* `tcw_deficit_sign_clause`: the sign clause of `TcsOneStepSplitAlong` for `tcw_deficit`, given the
  moments `E Z^p < ∞`, `p ≤ M + 2`.
* `tcw_abs_deficit_le`: `|d_l(m)| ≤ (D₀/2W)|m(m-1)| E Z_{l;k}^m` (the crude bound used in the
  stop removal).
* `tcsOneStepSplitCoreFixed_of_remainder`: `TcsOneStepSplitCoreFixed` from
  `FullSourceMomentsContract`, `ConditionalBlockGUECount` and the remainder-only
  `TcwRemainderCoreFixed`; hence (`tcoTagComparisonCoreFixed_of_remainder`)
  `TcoTagComparisonCoreFixed` with the additional `TagBirthValueContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial Finset Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal NNReal

/-!
## The square root and `X = Z_{l;k}`
-/

theorem tcw_tagQ_nonneg (b e : ℝ) (W l k : ℕ) (ω : GrowthPath W) : 0 ≤ tco_tagQ b e W l k ω :=
  Matrix.nonneg_iff_posSemidef.2 (tco_posSemidef_tagQ b e W l k ω)

theorem tcw_sqrtQ_conjTranspose (b e : ℝ) (W l k : ℕ) (ω : GrowthPath W) :
    (tcw_sqrtQ b e W l k ω)ᴴ = tcw_sqrtQ b e W l k ω :=
  (CFC.sqrt_nonneg (tco_tagQ b e W l k ω)).isSelfAdjoint

theorem tcw_sqrtQ_mul_self (b e : ℝ) (W l k : ℕ) (ω : GrowthPath W) :
    tcw_sqrtQ b e W l k ω * tcw_sqrtQ b e W l k ω = tco_tagQ b e W l k ω :=
  CFC.sqrt_mul_sqrt_self _ (tcw_tagQ_nonneg b e W l k ω)

/-- `‖Sh‖² = h*(S*S)h`. -/
theorem tcw_normSq_mulVec {ι : Type*} [Fintype ι] (S : Matrix ι ι ℂ) (h : ι → ℂ) :
    star (S *ᵥ h) ⬝ᵥ (S *ᵥ h) = star h ⬝ᵥ ((Sᴴ * S) *ᵥ h) := by
  rw [← mulVec_mulVec, dotProduct_mulVec (star h) Sᴴ, star_mulVec]

/-- **The witness lives on the tagged clock**: `X = ‖Q^{1/2}h‖² = h*Qh = Z_{l;k}`. -/
theorem tcw_X_eq (b e : ℝ) (W l k : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    tcw_X b e W l k x = lmf_tagResponseClock b e W l k x := by
  rw [tco_tagClock_eq_quadForm]
  unfold tcw_X tcw_v quadForm
  rw [tcw_normSq_mulVec, tcw_sqrtQ_conjTranspose, tcw_sqrtQ_mul_self]

theorem tcw_X_nonneg (b e : ℝ) (W l k : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    0 ≤ tcw_X b e W l k x := by
  rw [tcw_X_eq]; exact tco_tagClock_nonneg b e W l k x

/-!
## Measurability
-/

theorem tcw_measurable_tagQ (b e : ℝ) (W l k : ℕ) :
    Measurable (fun ω : GrowthPath W => tco_tagQ b e W l k ω) := by
  unfold tco_tagQ
  exact (continuous_const_smul ((W : ℝ)⁻¹)).measurable.comp (tco_measurable_tagResponse b e W l k)

theorem tcw_measurable_sqrtQ (b e : ℝ) (W l k : ℕ) :
    Measurable (fun ω : GrowthPath W => tcw_sqrtQ b e W l k ω) :=
  CFC.measurable_sqrt.comp (tcw_measurable_tagQ b e W l k)

theorem tcw_continuous_toBlocks₂₂ {m n : Type*} :
    Continuous (fun M : Matrix (m ⊕ n) (m ⊕ n) ℂ => M.toBlocks₂₂) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_apply (Sum.inr j)).comp (continuous_apply (Sum.inr i))

theorem tcw_measurable_scattering (b e : ℝ) (W l : ℕ) :
    Measurable (fun ω : GrowthPath W => scatteringMatrix b e W l ω) := by
  have hF : Measurable (fun ω : GrowthPath W => fullInverse b e W l ω) :=
    measurable_fullInverse_of b W l (α := GrowthPath W) measurable_const measurable_id
  have hc : Continuous (fun G : Matrix (FullSite W l) (FullSite W l) ℂ =>
      (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
        ((2 * etaZ b e : ℝ) * Complex.I) • G.toBlocks₂₂) :=
    continuous_const.sub ((continuous_const_smul _).comp tcw_continuous_toBlocks₂₂)
  exact hc.measurable.comp hF

theorem tcw_measurable_conjProj (b e : ℝ) (W l : ℕ) :
    Measurable (fun ω : GrowthPath W => tcw_conjProj b e W l ω) := by
  have hc : Continuous (fun S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
      Sᴴ * nearProjection W * S) :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  exact hc.measurable.comp (tcw_measurable_scattering b e W l)

theorem tcw_measurable_v (b e : ℝ) (W l k : ℕ) :
    Measurable (fun x : GrowthPath W × (Fin 2 × Fin W → ℂ) => tcw_v b e W l k x) := by
  have hc : Continuous (fun p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × (Fin 2 × Fin W → ℂ) =>
      p.1 *ᵥ p.2) := continuous_fst.matrix_mulVec continuous_snd
  exact hc.measurable.comp (((tcw_measurable_sqrtQ b e W l k).comp measurable_fst).prodMk
    measurable_snd)

theorem tcw_measurable_X (b e : ℝ) (W l k : ℕ) :
    Measurable (fun x : GrowthPath W × (Fin 2 × Fin W → ℂ) => tcw_X b e W l k x) := by
  have hc : Continuous (fun v : Fin 2 × Fin W → ℂ => (star v ⬝ᵥ v).re) :=
    Complex.continuous_re.comp (continuous_star.dotProduct continuous_id)
  exact hc.measurable.comp (tcw_measurable_v b e W l k)

theorem tcw_measurable_G (b e : ℝ) (W l k : ℕ) :
    Measurable (fun x : GrowthPath W × (Fin 2 × Fin W → ℂ) => tcw_G b e W l k x) := by
  have hv := tcw_measurable_v b e W l k
  have hP : Measurable (fun x : GrowthPath W × (Fin 2 × Fin W → ℂ) => tcw_conjProj b e W l x.1) :=
    (tcw_measurable_conjProj b e W l).comp measurable_fst
  have h1 : Continuous (fun v : Fin 2 × Fin W → ℂ => (star v ⬝ᵥ (nearProjection W *ᵥ v)).re) :=
    Complex.continuous_re.comp (continuous_star.dotProduct (continuous_const.matrix_mulVec
      continuous_id))
  have h2 : Continuous (fun p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × (Fin 2 × Fin W → ℂ) =>
      (star p.2 ⬝ᵥ (p.1 *ᵥ p.2)).re) :=
    Complex.continuous_re.comp ((continuous_star.comp continuous_snd).dotProduct
      (continuous_fst.matrix_mulVec continuous_snd))
  have hm1 : Measurable (fun x : GrowthPath W × (Fin 2 × Fin W → ℂ) =>
      (star (tcw_v b e W l k x) ⬝ᵥ (nearProjection W *ᵥ tcw_v b e W l k x)).re) := by
    exact h1.measurable.comp hv
  have hq := hP.prodMk hv
  have hm2 := h2.measurable.comp hq
  have e2 : ((fun p : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × (Fin 2 × Fin W → ℂ) =>
      (star p.2 ⬝ᵥ (p.1 *ᵥ p.2)).re) ∘ fun x : GrowthPath W × (Fin 2 × Fin W → ℂ) =>
        (tcw_conjProj b e W l x.1, tcw_v b e W l k x)) = fun x =>
      (star (tcw_v b e W l k x) ⬝ᵥ (tcw_conjProj b e W l x.1 *ᵥ tcw_v b e W l k x)).re := rfl
  rw [e2] at hm2
  have e3 : (fun x : GrowthPath W × (Fin 2 × Fin W → ℂ) => tcw_G b e W l k x) = fun x =>
      (star (tcw_v b e W l k x) ⬝ᵥ (nearProjection W *ᵥ tcw_v b e W l k x)).re *
      (star (tcw_v b e W l k x) ⬝ᵥ (tcw_conjProj b e W l x.1 *ᵥ tcw_v b e W l k x)).re := rfl
  rw [e3]
  exact hm1.mul hm2

/-!
## The almost-sure drift sign
-/

/-- **A.s. drift sign**: under `probedClockLaw W b`, a.s. `0 ≤ X`, `0 ≤ G ≤ X²`. `P' = 𝕊*P𝕊` is an
orthogonal projection at every path with Hermitian blocks and invertible `𝓜`
(`tcs_pathProjection`), which holds a.s. (`ae_growthPath_isHermitian`, and
`rv_ae_isUnit_fullPathMatrix` from `ConditionalBlockGUECount`). -/
theorem tcw_ae_drift (hCount : ConditionalBlockGUECount) {b e : ℝ} (hb1 : b < 1 / 2)
    (he1 : -2 < e) (he2 : e < 2) {W : ℕ} (hW : 0 < W) (l k : ℕ) :
    ∀ᵐ x ∂probedClockLaw W b, 0 ≤ tcw_X b e W l k x ∧ 0 ≤ tcw_G b e W l k x ∧
      tcw_G b e W l k x ≤ tcw_X b e W l k x ^ 2 := by
  have hgood : ∀ᵐ ω ∂growthPathLaw W b,
      (∀ i, (ω.1 i).IsHermitian) ∧ IsUnit (fullPathMatrix b e W l ω).det :=
    (ae_growthPath_isHermitian W b).and (rv_ae_isUnit_fullPathMatrix hCount hb1 he1 he2 hW l)
  have h2 : ∀ᵐ x ∂probedClockLaw W b,
      (∀ i, (x.1.1 i).IsHermitian) ∧ IsUnit (fullPathMatrix b e W l x.1).det :=
    Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst) hgood
  filter_upwards [h2] with x hx
  obtain ⟨hP'h, hP'P'⟩ := tcs_pathProjection (n := l) hx.1 hx.2
  have hd := tcs_drift_sign (tcs_nearProjection_hermitian W) (tcs_nearProjection_idem W)
    hP'h hP'P' (tcw_v b e W l k x)
  exact ⟨tcw_X_nonneg b e W l k x, hd.1, hd.2⟩

/-!
## The sign clause for the explicit witness
-/

theorem tcw_integrable_X_pow {b e : ℝ} {W l k : ℕ} {p : ℕ}
    (h : Integrable (fun x => lmf_tagResponseClock b e W l k x ^ p) (probedClockLaw W b)) :
    Integrable (fun x => tcw_X b e W l k x ^ p) (probedClockLaw W b) := by
  simpa only [tcw_X_eq] using h

/-- Integrability of the deficit integrand `m(m-1)X^{m-2}(G - X²)` from the moment of order
`m - 2 + 2` (a.s. `|G - X²| ≤ X²`). -/
theorem tcw_integrable_deficit (hCount : ConditionalBlockGUECount) {b e : ℝ} (hb1 : b < 1 / 2)
    (he1 : -2 < e) (he2 : e < 2) {W : ℕ} (hW : 0 < W) (l k m : ℕ)
    (hmom : Integrable (fun x => lmf_tagResponseClock b e W l k x ^ (m - 2 + 2))
      (probedClockLaw W b)) :
    Integrable (fun x => (m : ℝ) * ((m : ℝ) - 1) * tcw_X b e W l k x ^ (m - 2) *
      (tcw_G b e W l k x - tcw_X b e W l k x ^ 2)) (probedClockLaw W b) := by
  have hI := ((tcw_integrable_X_pow hmom).const_mul (|(m : ℝ) * ((m : ℝ) - 1)|))
  refine hI.mono' ?_ ?_
  · exact (((measurable_const.mul ((tcw_measurable_X b e W l k).pow_const _)).mul
      ((tcw_measurable_G b e W l k).sub
        ((tcw_measurable_X b e W l k).pow_const _)))).aestronglyMeasurable
  · filter_upwards [tcw_ae_drift hCount hb1 he1 he2 hW l k] with x hx
    obtain ⟨hX, hG0, hG1⟩ := hx
    have hX2 : 0 ≤ tcw_X b e W l k x ^ (m - 2) := pow_nonneg hX _
    have habs : |tcw_G b e W l k x - tcw_X b e W l k x ^ 2| ≤ tcw_X b e W l k x ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hX2, pow_add, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habs hX2) (abs_nonneg _)

/-- **The sign clause for the explicit witness**: for every polynomial `ψ`
convex on `[0,∞)` with `deg ψ ≤ M`, `Σ_{m≤M} ψ_m d_l(m) ≤ 0`, given the moments of order
`≤ M + 2` of `Z_{l;k}`. -/
theorem tcw_deficit_sign_clause (hCount : ConditionalBlockGUECount) {b e : ℝ} (hb : 0 < b)
    (hb1 : b < 1 / 2) (he1 : -2 < e) (he2 : e < 2) {W : ℕ} (hW : 0 < W) (l k M : ℕ)
    (hmom : ∀ p ≤ M + 2, Integrable (fun x => lmf_tagResponseClock b e W l k x ^ p)
      (probedClockLaw W b))
    {ψ : ℝ[X]} (hψ : ConvexOn ℝ (Set.Ici 0) (fun x => ψ.eval x)) (hdeg : ψ.natDegree ≤ M) :
    ∑ m ∈ range (M + 1), ψ.coeff m * tcw_deficit b e W l k m ≤ 0 := by
  have hc : 0 ≤ transportD0 b e / (2 * W) :=
    div_nonneg (transportD0_pos hb he1 he2).le (by positivity)
  have hXG : ∀ᵐ x ∂probedClockLaw W b, 0 ≤ tcw_X b e W l k x ∧
      tcw_G b e W l k x ≤ tcw_X b e W l k x ^ 2 := by
    filter_upwards [tcw_ae_drift hCount hb1 he1 he2 hW l k] with x hx
    exact ⟨hx.1, hx.2.2⟩
  exact tcs_deficit_sign_clause (probedClockLaw W b) (tcw_X b e W l k) (tcw_G b e W l k) hXG hc M
    (fun m hm => tcw_integrable_deficit hCount hb1 he1 he2 hW l k m
      (hmom _ (by simp at hm; omega))) hψ hdeg

/-- **Crude bound on the witness** (used in the stop removal):
`|d_l(m)| ≤ (D₀/2W)|m(m-1)| E Z_{l;k}^m`. -/
theorem tcw_abs_deficit_le (hCount : ConditionalBlockGUECount) {b e : ℝ} (hb : 0 < b)
    (hb1 : b < 1 / 2) (he1 : -2 < e) (he2 : e < 2) {W : ℕ} (hW : 0 < W) (l k m : ℕ)
    (hmom : Integrable (fun x => lmf_tagResponseClock b e W l k x ^ (m - 2 + 2))
      (probedClockLaw W b)) :
    |tcw_deficit b e W l k m| ≤ transportD0 b e / (2 * W) * (|(m : ℝ) * ((m : ℝ) - 1)| *
      ∫ x, lmf_tagResponseClock b e W l k x ^ (m - 2 + 2) ∂probedClockLaw W b) := by
  have hc : 0 ≤ transportD0 b e / (2 * W) :=
    div_nonneg (transportD0_pos hb he1 he2).le (by positivity)
  unfold tcw_deficit
  rw [abs_mul, abs_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => abs_nonneg _) (hmom.const_mul _) ?_)
  filter_upwards [tcw_ae_drift hCount hb1 he1 he2 hW l k] with x hx
  obtain ⟨hX, hG0, hG1⟩ := hx
  have hX2 : 0 ≤ tcw_X b e W l k x ^ (m - 2) := pow_nonneg hX _
  have habs : |tcw_G b e W l k x - tcw_X b e W l k x ^ 2| ≤ tcw_X b e W l k x ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith
  rw [abs_mul, abs_mul, abs_of_nonneg hX2, ← tcw_X_eq, pow_add, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habs hX2) (abs_nonneg _)

/-!
## The reduction
-/

/-- Moments of `Z_{l;k}` under `probedClockLaw` from a moment bound for its law `tcc_law`. -/
theorem tcw_integrable_tagClock_pow {b e : ℝ} {W l k p : ℕ} {C : ℝ}
    (h : ∫⁻ x, ENNReal.ofReal (x ^ (2 * p)) ∂tcc_law b e W l k ≤ ENNReal.ofReal C) :
    Integrable (fun x => lmf_tagResponseClock b e W l k x ^ p) (probedClockLaw W b) := by
  have := tcc_law_prob b e W l k
  have hI := (tco_integrable_of_lintegral_pow p h).2
  unfold tcc_law at hI
  exact (integrable_map_measure (continuous_pow p).aestronglyMeasurable
    (tco_measurable_tagClock b e W l k).aemeasurable).1 hI

/-- **The reduction**: `TcsOneStepSplitCoreFixed` from `FullSourceMomentsContract`,
`ConditionalBlockGUECount` (a.s. invertibility of `𝓜`, so that `P'` is a projection a.s.) and the
remainder-only `TcwRemainderCoreFixed`. The witness is the explicit `tcw_deficit`; its sign clause
is `tcw_deficit_sign_clause`. -/
theorem tcsOneStepSplitCoreFixed_of_remainder (hMom : FullSourceMomentsContract)
    (hCount : ConditionalBlockGUECount) (hR : TcwRemainderCoreFixed) :
    TcsOneStepSplitCoreFixed := by
  intro b hb hb' E hE1 hE2 s τ hs σ hσ M δ hδ
  choose Cf hCf using tcc_momentsAlong_fixed hMom hb hb' hE1 hE2 σ hσ
  have hmomE : ∀ᶠ j in atTop, ∀ p ∈ range (M + 3), ∀ l, σ.k j < l → l ≤ σ.n j →
      ∫⁻ x, ENNReal.ofReal (x ^ (2 * p)) ∂tcc_law b (σ.energy j) (σ.W j) l (σ.k j) ≤
        ENNReal.ofReal (Cf p) :=
    (eventually_all_finset _).2 fun p _ => hCf p
  filter_upwards [hmomE, hR b hb hb' E hE1 hE2 s τ hs σ hσ M δ hδ] with j hmj hRj
  refine ⟨fun l m => tcw_deficit b (σ.energy j) (σ.W j) l (σ.k j) m, ?_, hRj⟩
  intro l hl ψ hψ hdeg
  obtain ⟨hl1, hl2⟩ := mem_Ico.1 hl
  have he1 : -2 < σ.energy j := by rw [hσ j]; exact hE1
  have he2 : σ.energy j < 2 := by rw [hσ j]; exact hE2
  exact tcw_deficit_sign_clause hCount hb hb' he1 he2 (σ.W_pos j) l (σ.k j) M
    (fun p hp => tcw_integrable_tagClock_pow (hmj p (by simp; omega) l (by omega) (by omega)))
    hψ hdeg

/-- `TcoTagComparisonCoreFixed` from `FullSourceMomentsContract`, `TagBirthValueContract`,
`ConditionalBlockGUECount` and the remainder-only `TcwRemainderCoreFixed`. -/
theorem tcoTagComparisonCoreFixed_of_remainder (hMom : FullSourceMomentsContract)
    (hBirth : TagBirthValueContract) (hCount : ConditionalBlockGUECount)
    (hR : TcwRemainderCoreFixed) : TcoTagComparisonCoreFixed :=
  tcoTagComparisonCoreFixed_of_split hMom hBirth
    (tcsOneStepSplitCoreFixed_of_remainder hMom hCount hR)

end BlockBand.Endpoints
