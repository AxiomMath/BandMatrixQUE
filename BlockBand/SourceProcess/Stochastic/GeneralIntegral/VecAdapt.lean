module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.VecIntegral
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Bracket
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Adaptedness of the cross bracket `∫_0^t H K a^{ij}`

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖`, finite `ι`,
`h : IsL2IntegratorVec Q 𝓖 N a` with symmetric `a` (`hs`), horizon `T`, `ν̄ = barMeasure Q a T`,
`H, K ∈ PredL2 𝓖 ν̄` with canonical representatives `H̃, K̃`.

`crossTerm a i j f g t ω = ∫_{(0,t]} f(r,ω) g(r,ω) a^{ij}_r(ω) dr`.

**`aesm_crossTerm`**: `crossTerm a i j H̃ K̃ (t ∧ T)` is a.e. `𝓖_t`-measurable. Proof by double
polarization through the scalar theory: with `c_± = (e_i ± e_j)/2`, the combinations `c_± · N`
are scalar integrators (`IsL2IntegratorVec.combo`) with densities
`A_± = c_±ᵀ a c_± ≤ tr a` (`comboA_half_le_trace`) and `A_+ - A_- = a^{ij}`
(`comboA_half_sub`), so
`H̃ K̃ a^{ij} = ¼ ((H̃+K̃)² - (H̃-K̃)²)(A_+ - A_-)`, and each `∫_0^{t∧T} F² A_±` is adapted
(`IsL2Integrator.aestronglyMeasurable_bracketProc` for the restriction of `F ∈ PredL2(ν̄)` to
`PredL2(ν^{c_±})`, `aesm_bracketTerm_of_le`).
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {ι : Type*} [Fintype ι]

omit mΩ [Fintype ι] in
/-- The pathwise cross bracket `∫_{(0,t]} f g a^{ij}`. -/
def crossTerm (a : ι → ι → ℝ≥0 → Ω → ℝ) (i j : ι) (f g : ℝ × Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r in Ioc (0 : ℝ) t, f (r, ω) * g (r, ω) * a i j r.toNNReal ω

/-- **Adapted brackets of restricted integrands**: for a scalar integrator with `ν_β ≤ μ'` and
`f` a representative of `F ∈ PredL2(μ')`, `∫_0^{t∧T} f² β` is a.e. `𝓖_t`-measurable. -/
theorem aesm_bracketTerm_of_le [IsFiniteMeasure Q] {M β : ℝ≥0 → Ω → ℝ}
    (g : IsL2Integrator Q 𝓖 M β) {T : ℝ≥0} {μ' : Measure (ℝ × Ω)}
    (hle : bracketMeasure Q β T ≤ μ') (F : PredL2 𝓖 μ') {f : ℝ × Ω → ℝ}
    (hf : StronglyMeasurable f) (hfF : ((F : Lp ℝ 2 μ') : ℝ × Ω → ℝ) =ᵐ[μ'] f) (t : ℝ≥0) :
    AEStronglyMeasurable[𝓖 t] (bracketTerm β f (min t T)) Q := by
  set G := predRestrict 𝓖 hle F
  have hG : ((G : Lp ℝ 2 (bracketMeasure Q β T)) : ℝ × Ω → ℝ) =ᵐ[bracketMeasure Q β T] f :=
    (predRestrict_coeFn 𝓖 hle F).trans
      ((Measure.absolutelyContinuous_of_le hle).ae_le hfF)
  have hfin₁ := IsL2Integrator.lintegral_sq_ne_top (Q := Q) (α := β) T
    (G : Lp ℝ 2 (bracketMeasure Q β T))
  have hfin₂ : ∫⁻ p, ‖f p‖ₑ ^ 2 ∂bracketMeasure Q β T ≠ ∞ := by
    rw [lintegral_congr_ae (hG.mono fun p hp => congrArg (fun x : ℝ => ‖x‖ₑ ^ 2) hp.symm)]
    exact hfin₁
  exact (g.aestronglyMeasurable_bracketProc T G t).congr
    (bracketTerm_ae_eq_of_ae_eq g.alpha_measurable g.alpha_nonneg (Lp.stronglyMeasurable _) hf
      hfin₁ hfin₂ hG (min_le_right t T))

omit mΩ in
/-- The half vector `(e_i + s e_j)/2`. -/
def halfVec [DecidableEq ι] (i j : ι) (s : ℝ) : ι → ℝ :=
  fun k => (1 / 2) * ((if k = i then 1 else 0) + s * (if k = j then 1 else 0))

omit mΩ in
theorem comboA_halfVec [DecidableEq ι] (a : ι → ι → ℝ≥0 → Ω → ℝ) (i j : ι) (s : ℝ)
    (t : ℝ≥0) (ω : Ω) :
    IsL2IntegratorVec.comboA a (halfVec i j s) t ω =
      (1 / 4) * (a i i t ω + s * a i j t ω + s * a j i t ω + s ^ 2 * a j j t ω) := by
  rw [← quadForm_two (fun k l => a k l t ω) i j s, Finset.mul_sum, IsL2IntegratorVec.comboA]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [halfVec]
  ring

namespace IsL2IntegratorVec

variable {N : ι → ℝ≥0 → Ω → ℝ} {a : ι → ι → ℝ≥0 → Ω → ℝ} (h : IsL2IntegratorVec Q 𝓖 N a)
  (hs : ∀ i j t ω, a i j t ω = a j i t ω)
include h hs

theorem comboA_half_le_trace [DecidableEq ι] (i j : ι) {s : ℝ} (hs1 : s = 1 ∨ s = -1)
    (t : ℝ≥0) (ω : Ω) : comboA a (halfVec i j s) t ω ≤ traceA a t ω := by
  have hab := abs_le_of_psd_symm (h.psd t ω) (fun i j => hs i j t ω) i j
  have htr := half_diag_le_trace (A := fun k l => a k l t ω) (fun k => h.diag_nonneg k t ω) i j
  rw [comboA_halfVec, hs j i t ω, traceA]
  rcases hs1 with rfl | rfl
  · have := le_abs_self (a i j t ω); nlinarith
  · have := neg_abs_le (a i j t ω); nlinarith

omit h mΩ in
theorem comboA_half_sub [DecidableEq ι] (i j : ι) (t : ℝ≥0) (ω : Ω) :
    comboA a (halfVec i j 1) t ω - comboA a (halfVec i j (-1)) t ω = a i j t ω := by
  rw [comboA_halfVec, comboA_halfVec, hs j i t ω]
  ring

/-- **The cross bracket is adapted**: `∫_0^{t∧T} H̃ K̃ a^{ij}` is a.e. `𝓖_t`-measurable. -/
theorem aesm_crossTerm [IsFiniteMeasure Q] (T : ℝ≥0) (i j : ι)
    (H K : PredL2 𝓖 (barMeasure Q a T)) (t : ℝ≥0) :
    AEStronglyMeasurable[𝓖 t] (crossTerm a i j ((H : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ)
      ((K : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ) (min t T)) Q := by
  classical
  set f : ℝ × Ω → ℝ := ((H : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ)
  set g : ℝ × Ω → ℝ := ((K : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ)
  have hfm : StronglyMeasurable f := Lp.stronglyMeasurable _
  have hgm : StronglyMeasurable g := Lp.stronglyMeasurable _
  have hpl : ((H + K : PredL2 𝓖 (barMeasure Q a T)) : Lp ℝ 2 (barMeasure Q a T)) =ᵐ[barMeasure Q a T]
      fun p => f p + g p := Lp.coeFn_add _ _
  have hmi : ((H - K : PredL2 𝓖 (barMeasure Q a T)) : Lp ℝ 2 (barMeasure Q a T)) =ᵐ[barMeasure Q a T]
      fun p => f p - g p := Lp.coeFn_sub _ _
  -- the two combinations and their bracket measures
  let A : ℝ → ℝ≥0 → Ω → ℝ := fun s => comboA a (halfVec i j s)
  have hA (s : ℝ) := h.combo (halfVec i j s)
  have hle (s : ℝ) (hs1 : s = 1 ∨ s = -1) : bracketMeasure Q (A s) T ≤ barMeasure Q a T :=
    bracketMeasure_mono_density Q T (h.comboA_half_le_trace hs i j hs1)
  have hfin (s : ℝ) (hs1 : s = 1 ∨ s = -1) (F : PredL2 𝓖 (barMeasure Q a T)) {u : ℝ × Ω → ℝ}
      (hu : ((F : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ) =ᵐ[barMeasure Q a T] u) :
      ∫⁻ p, ‖u p‖ₑ ^ 2 ∂bracketMeasure Q (A s) T ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono' (hle s hs1) le_rfl)
    rw [lintegral_congr_ae (hu.mono fun p hp => congrArg (fun x : ℝ => ‖x‖ₑ ^ 2) hp.symm)]
    exact IsL2Integrator.lintegral_sq_ne_top (α := traceA a) T _
  have hint (s : ℝ) (hs1 : s = 1 ∨ s = -1) (F : PredL2 𝓖 (barMeasure Q a T)) {u : ℝ × Ω → ℝ}
      (hum : StronglyMeasurable u)
      (hu : ((F : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ) =ᵐ[barMeasure Q a T] u) :=
    ae_integrableOn_sq (hA s).alpha_measurable (hA s).alpha_nonneg hum (hfin s hs1 F hu)
  have h1 : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  have h2 : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
  have hsub : Ioc (0 : ℝ) (min t T : ℝ≥0) ⊆ Ioc 0 T :=
    Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 (min_le_right t T))
  have hae : crossTerm a i j f g (min t T) =ᵐ[Q] fun ω => (1 / 4 : ℝ) *
      (bracketTerm (A 1) (fun p => f p + g p) (min t T) ω -
        bracketTerm (A (-1)) (fun p => f p + g p) (min t T) ω -
        bracketTerm (A 1) (fun p => f p - g p) (min t T) ω +
        bracketTerm (A (-1)) (fun p => f p - g p) (min t T) ω) := by
    filter_upwards [hint 1 h1 _ (u := fun p => f p + g p) (hfm.add hgm) hpl,
      hint (-1) h2 _ (u := fun p => f p + g p) (hfm.add hgm) hpl,
      hint 1 h1 _ (u := fun p => f p - g p) (hfm.sub hgm) hmi,
      hint (-1) h2 _ (u := fun p => f p - g p) (hfm.sub hgm) hmi] with ω i1 i2 i3 i4
    simp only [bracketTerm, crossTerm, A]
    have e3 := integral_sub (i1.mono_set hsub) (i2.mono_set hsub)
    have e2 := integral_sub ((i1.mono_set hsub).sub (i2.mono_set hsub)) (i3.mono_set hsub)
    have e1 := integral_add (((i1.mono_set hsub).sub (i2.mono_set hsub)).sub (i3.mono_set hsub))
      (i4.mono_set hsub)
    simp only [Pi.sub_apply] at e1 e2 e3
    rw [← e3, ← e2, ← e1, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    have hd := comboA_half_sub hs i j r.toNNReal ω
    simp only
    rw [← hd]
    ring
  refine AEStronglyMeasurable.congr ?_ hae.symm
  refine AEStronglyMeasurable.const_mul ?_ _
  exact (((aesm_bracketTerm_of_le (hA 1) (hle 1 h1) _ (hfm.add hgm) hpl t).sub
    (aesm_bracketTerm_of_le (hA (-1)) (hle (-1) h2) _ (hfm.add hgm) hpl t)).sub
    (aesm_bracketTerm_of_le (hA 1) (hle 1 h1) _ (hfm.sub hgm) hmi t)).add
    (aesm_bracketTerm_of_le (hA (-1)) (hle (-1) h2) _ (hfm.sub hgm) hmi t)

end IsL2IntegratorVec

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
