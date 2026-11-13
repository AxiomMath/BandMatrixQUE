module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.FixPSD
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.FixSymm
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Direct constructors of integrators from a.e. versions of the density

Setting: `(Ω, m₀, Q)`, raw filtration `𝓖`. `IsL2Integrator.congr_alpha` (`VersionAlpha`)
needs an integrator for the original density `α`, including `alpha_measurable` for `α`, which is
exactly what is unknown for `α = φ(Y)1{· ≤ τ}`. Here the data are `N`'s own fields, a
measurable nonnegative `α'` and the bracket identity for **any** `α` with `α' = α` pathwise a.s.
for `t > 0`; `α` itself needs no measurability or integrability.

* `IsL2Integrator.of_ae_alpha`: the scalar constructor.
* `IsL2IntegratorVec.of_ae_density`: the matrix constructor (`a'` PSD everywhere, measurable,
  a.s. locally integrable; cross brackets `N^i N^j - ∫ a^{ij}` for any `a` with `a' = a` a.s.
  for `t > 0`).
* `setIntegral_alphaVersionPos` (missing in `VersionAlpha`).
* `integrableOn_of_abs_le_continuous`, `integrableOn_psdVersion`: on a continuous path the
  version is locally integrable (bounded by a continuous function on compacts).
* `IsL2IntegratorVec.of_psdVersion`: **martingale-problem entry point**. `Y` adapted with a.s.
  continuous paths, `φ` continuous and PSD on all of `E`, `τ` a raw stopping time, `N` with
  a.s. continuous `L²` paths and martingale modifications, and cross brackets
  `N^i N^j - ∫_{(0,t]} φ_{ij}(Y_r) 1{r ≤ τ} dr` with martingale modifications: then
  `IsL2IntegratorVec Q 𝓖 N (psdVersion τ φ Y)`. Its density is symmetric when `φ` is.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}

omit mΩ in
theorem setIntegral_congr_of_pos {α α' : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (he : ∀ t : ℝ≥0, 0 < t → α' t ω = α t ω) (t : ℝ≥0) :
    ∫ r in Ioc (0 : ℝ) t, α' r.toNNReal ω = ∫ r in Ioc (0 : ℝ) t, α r.toNNReal ω :=
  setIntegral_congr_fun measurableSet_Ioc fun _ hr => he _ (Real.toNNReal_pos.2 hr.1)

/-- **Direct scalar constructor** from an a.e. version of the density. -/
theorem IsL2Integrator.of_ae_alpha {N α α' : ℝ≥0 → Ω → ℝ}
    (hc : ∀ᵐ ω ∂Q, Continuous fun t => N t ω) (hL : ∀ t, MemLp (N t) 2 Q)
    (hM : ∃ M : ℝ≥0 → Ω → ℝ, Martingale M 𝓖 Q ∧ ∀ t, M t =ᵐ[Q] N t)
    (h0 : ∀ t ω, 0 ≤ α' t ω) (hm : Measurable fun p : ℝ × Ω => α' p.1.toNNReal p.2)
    (hint : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, IntegrableOn (fun r : ℝ => α' r.toNNReal ω) (Ioc 0 t))
    (hK : ∃ K : ℝ≥0 → Ω → ℝ, Martingale K 𝓖 Q ∧
      ∀ t, K t =ᵐ[Q] fun ω => N t ω ^ 2 - ∫ r in Ioc (0 : ℝ) t, α r.toNNReal ω)
    (heq : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, 0 < t → α' t ω = α t ω) : IsL2Integrator Q 𝓖 N α' where
  continuous := hc
  memLp := hL
  martingale := hM
  alpha_nonneg := h0
  alpha_measurable := hm
  alpha_integrable := hint
  bracket := by
    obtain ⟨K, hK, hKe⟩ := hK
    refine ⟨K, hK, fun t => ?_⟩
    filter_upwards [hKe t, heq] with ω h1 he
    rw [h1, setIntegral_congr_of_pos he]

variable {ι : Type*} [Fintype ι]

/-- **Direct matrix constructor** from an a.e. version `a'` of the density matrix `a`. -/
theorem IsL2IntegratorVec.of_ae_density {N : ι → ℝ≥0 → Ω → ℝ} {a a' : ι → ι → ℝ≥0 → Ω → ℝ}
    (hc : ∀ i, ∀ᵐ ω ∂Q, Continuous fun t => N i t ω) (hL : ∀ i t, MemLp (N i t) 2 Q)
    (hM : ∀ i, ∃ M : ℝ≥0 → Ω → ℝ, Martingale M 𝓖 Q ∧ ∀ t, M t =ᵐ[Q] N i t)
    (hpsd : ∀ t ω (v : ι → ℝ), 0 ≤ ∑ i, ∑ j, v i * v j * a' i j t ω)
    (hm : ∀ i j, Measurable fun p : ℝ × Ω => a' i j p.1.toNNReal p.2)
    (hint : ∀ i j, ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, IntegrableOn (fun r : ℝ => a' i j r.toNNReal ω) (Ioc 0 t))
    (hcross : ∀ i j, ∃ K : ℝ≥0 → Ω → ℝ, Martingale K 𝓖 Q ∧ ∀ t, K t =ᵐ[Q] fun ω =>
      N i t ω * N j t ω - ∫ r in Ioc (0 : ℝ) t, a i j r.toNNReal ω)
    (heq : ∀ i j, ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, 0 < t → a' i j t ω = a i j t ω) :
    IsL2IntegratorVec Q 𝓖 N a' where
  coord i := by
    refine IsL2Integrator.of_ae_alpha (α := a i i) (hc i) (hL i) (hM i)
      (fun t ω => psd_diag_nonneg (hpsd t ω) i) (hm i i) (hint i i) ?_ (heq i i)
    obtain ⟨K, hK, hKe⟩ := hcross i i
    exact ⟨K, hK, fun t => (hKe t).trans (Eventually.of_forall fun ω => by simp only [sq])⟩
  psd := hpsd
  measurable := hm
  integrable := hint
  cross i j := by
    obtain ⟨K, hK, hKe⟩ := hcross i j
    refine ⟨K, hK, fun t => ?_⟩
    filter_upwards [hKe t, heq i j] with ω h1 he
    rw [h1, setIntegral_congr_of_pos he]

variable {E : Type*} [TopologicalSpace E]

omit mΩ in
theorem setIntegral_alphaVersionPos {τ : Ω → WithTop ℝ≥0} {φ : E → ℝ} (hφ : Continuous φ)
    (hφ0 : ∀ y, 0 ≤ φ y) {Y : ℝ≥0 → Ω → E} {ω : Ω} (hω : Continuous fun t => Y t ω)
    (a b : ℝ) (ha : 0 ≤ a) :
    ∫ r in Ioc a b, alphaVersionPos τ φ Y r.toNNReal ω =
      ∫ r in Ioc a b, stoppedComposite τ φ Y (r, ω) := by
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  rw [alphaVersionPos_eq hφ hφ0 hω (Real.toNNReal_pos.2 (ha.trans_lt hr.1)), stoppedComposite]

/-- A measurable `f` dominated for `r > 0` by a continuous `|g(r)|` is integrable on `(0,t]`. -/
theorem integrableOn_of_abs_le_continuous {f : ℝ → ℝ} (hf : Measurable f) {g : ℝ≥0 → ℝ}
    (hg : Continuous g) (hle : ∀ r : ℝ, 0 < r → |f r| ≤ |g r.toNNReal|) (t : ℝ≥0) :
    IntegrableOn f (Ioc 0 t) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_bound_of_continuousOn
    hg.continuousOn
  refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne
    hf.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [Real.norm_eq_abs]
  refine (hle r hr.1).trans ?_
  have h := hC r.toNNReal ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hr.2⟩
  rwa [Real.norm_eq_abs] at h

variable {τ : Ω → WithTop ℝ≥0} {φ : ι → ι → E → ℝ} {Y : ℝ≥0 → Ω → E}

omit [Fintype ι] in
/-- On a continuous path the PSD version is locally integrable. -/
theorem integrableOn_psdVersion [Finite ι] (hτ : IsStoppingTime 𝓖 τ)
    (hφ : ∀ i j, Continuous (φ i j)) (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t)) {ω : Ω}
    (hω : Continuous fun t => Y t ω) (i j : ι) (t : ℝ≥0) :
    IntegrableOn (fun r : ℝ => psdVersion τ φ Y i j r.toNNReal ω) (Ioc 0 t) := by
  refine integrableOn_of_abs_le_continuous
    ((measurable_psdVersion 𝓖 hτ hφ hY i j).comp (measurable_id.prodMk measurable_const))
    ((hφ i j).comp hω) (fun r hr => ?_) t
  show |psdVersion τ φ Y i j r.toNNReal ω| ≤ |φ i j (Y r.toNNReal ω)|
  rw [psdVersion_eq hφ hω (Real.toNNReal_pos.2 hr) i j]
  split_ifs
  · exact le_rfl
  · simp

/-- **Martingale-problem entry point**: a PSD predictable version of `φ(Y)1{· ≤ τ}` is the
density matrix of a vector integrator. -/
theorem IsL2IntegratorVec.of_psdVersion {N : ι → ℝ≥0 → Ω → ℝ} (hτ : IsStoppingTime 𝓖 τ)
    (hφ : ∀ i j, Continuous (φ i j)) (hpsd : ∀ y (v : ι → ℝ), 0 ≤ ∑ i, ∑ j, v i * v j * φ i j y)
    (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t)) (hYc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω)
    (hc : ∀ i, ∀ᵐ ω ∂Q, Continuous fun t => N i t ω) (hL : ∀ i t, MemLp (N i t) 2 Q)
    (hM : ∀ i, ∃ M : ℝ≥0 → Ω → ℝ, Martingale M 𝓖 Q ∧ ∀ t, M t =ᵐ[Q] N i t)
    (hcross : ∀ i j, ∃ K : ℝ≥0 → Ω → ℝ, Martingale K 𝓖 Q ∧ ∀ t, K t =ᵐ[Q] fun ω =>
      N i t ω * N j t ω - ∫ r in Ioc (0 : ℝ) t, stoppedComposite τ (φ i j) Y (r, ω)) :
    IsL2IntegratorVec Q 𝓖 N (psdVersion τ φ Y) := by
  refine IsL2IntegratorVec.of_ae_density (a := fun i j t ω => stoppedComposite τ (φ i j) Y
    ((t : ℝ), ω)) hc hL hM (fun t ω v => psdVersion_psd hpsd t ω v)
    (measurable_psdVersion 𝓖 hτ hφ hY) ?_ ?_ ?_
  · intro i j
    filter_upwards [hYc] with ω hω t using integrableOn_psdVersion hτ hφ hY hω i j t
  · intro i j
    obtain ⟨K, hK, hKe⟩ := hcross i j
    refine ⟨K, hK, fun t => (hKe t).trans (Eventually.of_forall fun ω => ?_)⟩
    refine congrArg (fun x => N i t ω * N j t ω - x) ?_
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    simp only [Real.coe_toNNReal _ hr.1.le]
  · intro i j
    filter_upwards [hYc] with ω hω t ht
    rw [psdVersion_eq hφ hω ht i j, stoppedComposite, Real.toNNReal_coe]

omit mΩ [Fintype ι] [TopologicalSpace E] in
theorem psdVersion_symm (hs : ∀ i j y, φ i j y = φ j i y) (i j : ι) (t : ℝ≥0) (ω : Ω) :
    psdVersion τ φ Y i j t ω = psdVersion τ φ Y j i t ω := by
  have hφ : φ i j = φ j i := funext (hs i j)
  simp only [psdVersion, hφ]

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
