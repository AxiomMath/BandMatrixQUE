module

public import BlockBand.Critical.MatrixClosing.Bridge
public import BlockBand.Critical.MatrixClosing.MiddleShift.Bound

/-!
# The matrix closing theorem: stability against old-measurable tests

The deterministic uniform matrix closing statement implies, by Fubini, that the closing family
built from random old data independent of the collar converges in law stably: its limit is
independent of the old data.

* Measurability: `measurable_middleScattering`, `measurable_oldScattering_comp`,
  `measurable_shiftedClosing_prod` (jointly in measurable old data and the collar),
  `measurable_matchedDistance_comp`.
* **`MatrixClosingStatement.stable`**: old data `X_n, J_n` on arbitrary
  probability spaces `(Ωo n, μo n)`, independent of the collar (`μo n ⊗ collarLaw`), Hermitian and
  orthonormal a.s., `d(X_n) → 0` in probability; for bounded old-measurable `g_n` and bounded
  continuous `Φ`: `E[g_n Φ(𝒞_n)] - E[g_n] E Φ((𝖢_r(x_a))_a) → 0`.
* **`MatrixClosingStatement.stable_joint`**: with an old random element `Z_n` (Polish space)
  converging in law to `ν` (in the bounded-continuous form of `IsRingProbeCriticalLimit`),
  `(Z_n, 𝒞_n) ⇒ ν ⊗ Law((𝖢_r(x_a))_a)` against every bounded continuous joint test.
* `MatrixClosingStatement.stable_joint_atZero`: the same at the single shift `0`, with the limit
  `C₀` of a canonical Cauchy field at zero.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Critical.Herglotz
open BlockBand.Critical.Collar.Kernel

variable {W : ℕ}

/-!
## Joint measurability in the old data and the collar
-/

theorem measurable_middleScattering (b e s : ℝ) :
    Measurable fun ω : CollarSample W => middleScattering b e s ω := by
  have hK : Measurable fun ω : CollarSample W => middleReaction b e s ω := by
    unfold middleReaction
    exact measurable_matrix_sub' (measurable_matrix_sub' measurable_blockDiag_collar
      measurable_const) (measurable_matrix_mul' (measurable_matrix_mul' measurable_bondMatrix_collar
        (measurable_matrix_inv' (measurable_matrix_sub' measurable_snd measurable_const)))
        (measurable_matrix_conjTranspose' measurable_bondMatrix_collar))
  unfold middleScattering
  exact measurable_matrix_sub' measurable_const (measurable_matrix_smul' _
    (measurable_matrix_inv' (measurable_matrix_add' hK measurable_const)))

theorem measurable_oldScattering_comp {Ω : Type*} [MeasurableSpace Ω] (b e : ℝ)
    {X : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : Measurable X) :
    Measurable fun o => oldScattering b e (X o) := by
  unfold oldScattering
  exact measurable_matrix_sub' measurable_const (measurable_matrix_smul' _
    (measurable_matrix_inv' (measurable_matrix_sub' measurable_const hX)))

/-- `(o, ω) ↦ (closing matrices at the shifts x_a)` is measurable for measurable old data. -/
theorem measurable_shiftedClosing_prod {Ω : Type*} [MeasurableSpace Ω] {r k : ℕ} (b e : ℝ)
    (x : Fin k → ℝ) {X : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {J : Ω → Matrix (Fin 2 × Fin W) (Fin r) ℂ} (hX : Measurable X) (hJ : Measurable J) :
    Measurable fun p : Ω × CollarSample W => shiftedClosing b e x (X p.1) (J p.1) p.2 := by
  refine Measurable.of_eval fun a => ?_
  have hJ1 : Measurable fun p : Ω × CollarSample W => J p.1 := hJ.comp measurable_fst
  have hU : Measurable fun p : Ω × CollarSample W => middleScattering b e (microShift W e (x a)) p.2 :=
    (measurable_middleScattering b e _).comp measurable_snd
  have hr : Measurable fun p : Ω × CollarSample W => oldScattering b e (X p.1) :=
    measurable_oldScattering_comp b e (hX.comp measurable_fst)
  unfold shiftedClosing closingMatrix
  exact measurable_matrix_smul' _ (measurable_matrix_mul' (measurable_matrix_mul'
    (measurable_matrix_conjTranspose' hJ1) (measurable_matrix_sub' (measurable_matrix_smul' _
      (measurable_matrix_inv' (measurable_matrix_sub' measurable_const
        (measurable_matrix_mul' hU hr)))) measurable_const)) hJ1)

/-- `o ↦ d(X(o))` is measurable for measurable `X`. -/
theorem measurable_matchedDistance_comp {Ω : Type*} [MeasurableSpace Ω] (b e : ℝ)
    {X : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : Measurable X) :
    Measurable fun o => matchedDistance b e (X o) := by
  have hR : Measurable fun o => (boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      X o)⁻¹ := measurable_matrix_inv' (measurable_matrix_sub' measurable_const hX)
  have hT : ∀ j : Fin 2, Measurable fun o => blockTrace ((boundaryZ b e •
      (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X o)⁻¹) j := by
    intro j
    unfold blockTrace
    refine measurable_const.mul (Finset.measurable_sum _ fun a _ => ?_)
    have := (Matrix.measurable_apply (i := (j, a)) (j := (j, a))).comp hR
    simpa [Function.comp_def] using this
  unfold matchedDistance
  exact Measurable.max ((hT 0).sub measurable_const).norm ((hT 1).sub measurable_const).norm

/-!
## Stability against bounded old-measurable tests
-/

/-- *Law.* Old data on arbitrary probability spaces `(Ωo n, μo n)` (the old path), independent of the
fresh collar: the product `μo n ⊗ collarLaw (W n) b`. Measurable old responses `X n` (Hermitian
a.s., i.e. lossless) and frames `J n` (`Jᴴ J = 1` a.s.), with `d(X n) → 0` in probability; widths
`W n → ∞`, energies `e n ∈ bulkInterval κ`.
*Tests.* Bounded old-measurable `g n` (`|g n| ≤ M`) and a bounded continuous `Φ` of the joint
closing family at the middle shifts `x_a`.
*Conclusion.* `E[g_n(old) Φ(𝒞_n)] - E[g_n] E Φ((𝖢_r(x_a))_a) → 0`: the limit law is independent
of the old path. This is the Fubini consequence of the deterministic uniform statement. -/
theorem MatrixClosingStatement.stable (h : MatrixClosingStatement) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) {r k : ℕ} (x : Fin k → ℝ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))} {C : Ω' → ℂ → Matrix (Fin r) (Fin r) ℂ}
    (hC : IsCanonicalCauchy r P' Ξ C)
    (Φ : BoundedContinuousFunction (Fin k → Matrix (Fin r) (Fin r) ℂ) ℝ)
    {Ωo : ℕ → Type*} [∀ n, MeasurableSpace (Ωo n)] (μo : ∀ n, Measure (Ωo n))
    [∀ n, IsProbabilityMeasure (μo n)]
    (W : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWt : Tendsto W atTop atTop) (e : ℕ → ℝ)
    (he : ∀ n, e n ∈ bulkInterval κ)
    (X : ∀ n, Ωo n → Matrix (Fin 2 × Fin (W n)) (Fin 2 × Fin (W n)) ℂ)
    (hXm : ∀ n, Measurable (X n)) (hXh : ∀ n, ∀ᵐ o ∂μo n, (X n o).IsHermitian)
    (J : ∀ n, Ωo n → Matrix (Fin 2 × Fin (W n)) (Fin r) ℂ) (hJm : ∀ n, Measurable (J n))
    (hJf : ∀ n, ∀ᵐ o ∂μo n, (J n o)ᴴ * J n o = 1)
    (hd : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => μo n {o | δ < matchedDistance b (e n) (X n o)}) atTop (𝓝 0))
    (g : ∀ n, Ωo n → ℝ) (hgm : ∀ n, Measurable (g n)) (M : ℝ) (hg : ∀ n o, |g n o| ≤ M) :
    Tendsto (fun n => ∫ p, g n p.1 * Φ (shiftedClosing b (e n) x (X n p.1) (J n p.1) p.2)
        ∂(μo n).prod (collarLaw (W n) b) -
        (∫ o, g n o ∂μo n) * ∫ ω, Φ (fun a => C ω (x a)) ∂P') atTop (𝓝 0) := by
  have := hC.decorated.prob
  set c := ∫ ω, Φ (fun a => C ω (x a)) ∂P'
  set B := ‖Φ‖
  have hΦb : ∀ m, |Φ m| ≤ B := fun m => by
    rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm m
  have hcb : |c| ≤ B := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := B) (Eventually.of_forall fun ω => ?_)).trans ?_
    · rw [Real.norm_eq_abs]; exact hΦb _
    · simp
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / (2 * (|M| + 1))
  have hε' : 0 < ε' := div_pos hε (by positivity)
  obtain ⟨δ, W₀, hδ, hmain⟩ := h b hb0 hb κ hκ r k x Ω' P' Ξ C hC Φ ε' hε'
  set η := ε / (4 * (|M| + 1) * (B + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hbad : ∀ᶠ n in atTop, (μo n).real {o | δ < matchedDistance b (e n) (X n o)} ≤ η := by
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hd δ hδ)
    simp only [ENNReal.toReal_zero] at h1
    exact (h1.eventually (Iic_mem_nhds hη)).mono fun n hn => hn
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (hbad.and (hWt.eventually_ge_atTop W₀)))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hbadn, hWn⟩ := hN n hn
  set 𝒞 := fun p : Ωo n × CollarSample (W n) => shiftedClosing b (e n) x (X n p.1) (J n p.1) p.2
  have h𝒞 : Measurable 𝒞 := measurable_shiftedClosing_prod b (e n) x (hXm n) (hJm n)
  have hf : Measurable fun p : Ωo n × CollarSample (W n) => g n p.1 * Φ (𝒞 p) :=
    ((hgm n).comp measurable_fst).mul (Φ.continuous.measurable.comp h𝒞)
  have hfi : Integrable (fun p : Ωo n × CollarSample (W n) => g n p.1 * Φ (𝒞 p))
      ((μo n).prod (collarLaw (W n) b)) := by
    refine Integrable.of_bound hf.aestronglyMeasurable (|M| * B) (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((hg n p.1).trans (le_abs_self M)) (hΦb _) (abs_nonneg _) (abs_nonneg _)
  set H : Ωo n → ℝ := fun o => ∫ ω, Φ (𝒞 (o, ω)) ∂collarLaw (W n) b
  have hHb : ∀ o, |H o| ≤ B := by
    intro o
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := B) (Eventually.of_forall fun ω => ?_)).trans ?_
    · rw [Real.norm_eq_abs]; exact hΦb _
    · simp
  have hgH : Integrable (fun o => g n o * H o) (μo n) := by
    have := hfi.integral_prod_left
    refine this.congr (Eventually.of_forall fun o => ?_)
    simp only [H]
    rw [integral_const_mul]
  have hgi : Integrable (g n) (μo n) :=
    Integrable.of_bound (hgm n).aestronglyMeasurable M (Eventually.of_forall fun o => by
      rw [Real.norm_eq_abs]; exact hg n o)
  have hprod : ∫ p, g n p.1 * Φ (𝒞 p) ∂(μo n).prod (collarLaw (W n) b) = ∫ o, g n o * H o ∂μo n := by
    rw [integral_prod _ hfi]
    refine integral_congr_ae (Eventually.of_forall fun o => ?_)
    simp only [H]
    rw [integral_const_mul]
  have hdiff : ∫ p, g n p.1 * Φ (𝒞 p) ∂(μo n).prod (collarLaw (W n) b) - (∫ o, g n o ∂μo n) * c =
      ∫ o, g n o * (H o - c) ∂μo n := by
    rw [hprod, ← integral_mul_const, ← integral_sub hgH (hgi.mul_const c)]
    refine integral_congr_ae (Eventually.of_forall fun o => ?_)
    simp only; ring
  -- the bad set
  set bad := {o | δ < matchedDistance b (e n) (X n o)}
  have hbadm : MeasurableSet bad :=
    measurableSet_lt measurable_const (measurable_matchedDistance_comp b (e n) (hXm n))
  have hpt : ∀ᵐ o ∂μo n, |g n o * (H o - c)| ≤ |M| * (ε' + bad.indicator (fun _ => 2 * B) o) := by
    filter_upwards [hXh n, hJf n] with o hXo hJo
    rw [abs_mul]
    refine mul_le_mul ((hg n o).trans (le_abs_self M)) ?_ (abs_nonneg _) (abs_nonneg _)
    by_cases hbo : o ∈ bad
    · rw [Set.indicator_of_mem hbo]
      have : |H o - c| ≤ 2 * B := by
        have := abs_sub (H o) c
        linarith [hHb o, hcb]
      linarith
    · rw [Set.indicator_of_notMem hbo, add_zero]
      have hdo : matchedDistance b (e n) (X n o) ≤ δ := not_lt.1 hbo
      exact (hmain (W n) (hW n) hWn (e n) (he n) (X n o) hXo hdo (J n o) hJo).2
  have hint2 : Integrable (fun o => |M| * (ε' + bad.indicator (fun _ => 2 * B) o)) (μo n) :=
    ((integrable_const ε').add ((integrable_const (2 * B)).indicator hbadm)).const_mul _
  have hbound : |∫ o, g n o * (H o - c) ∂μo n| ≤ |M| * (ε' + 2 * B * η) := by
    refine (abs_integral_le_integral_abs).trans ?_
    refine (integral_mono_ae ((hgH.sub (hgi.mul_const c)).abs.congr ?_) hint2 hpt).trans ?_
    · exact Eventually.of_forall fun o => by simp only [Pi.sub_apply, mul_sub]
    have hu1 : (μo n).real Set.univ = 1 := by simp [measureReal_def]
    rw [integral_const_mul, integral_add (integrable_const _)
      ((integrable_const (2 * B)).indicator hbadm), integral_const, integral_indicator hbadm,
      setIntegral_const, hu1, one_smul, smul_eq_mul]
    have hB : 0 ≤ B := norm_nonneg _
    have : (μo n).real bad * (2 * B) ≤ 2 * B * η := by nlinarith
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg M)
  rw [Real.dist_eq, sub_zero, hdiff]
  refine lt_of_le_of_lt hbound ?_
  have hM1 : (0 : ℝ) < |M| + 1 := by positivity
  have e1 : |M| * ε' ≤ ε / 2 := by
    simp only [ε']
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg M]
  have e2 : |M| * (2 * B * η) < ε / 2 := by
    simp only [η]
    have hB : 0 ≤ B := norm_nonneg _
    rw [show |M| * (2 * B * (ε / (4 * (|M| + 1) * (B + 1)))) =
      ε / 2 * ((|M| / (|M| + 1)) * (B / (B + 1))) by field_simp; ring]
    have h1 : |M| / (|M| + 1) < 1 := by rw [div_lt_one hM1]; linarith
    have h2 : B / (B + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    have h3 : 0 ≤ |M| / (|M| + 1) := by positivity
    have h4 : 0 ≤ B / (B + 1) := by positivity
    have : (|M| / (|M| + 1)) * (B / (B + 1)) < 1 := by nlinarith
    nlinarith
  nlinarith

/-!
## Joint convergence with a converging old random element
-/

section Joint

open scoped BoundedContinuousFunction

/-- Matrices with the product topology are second countable (local instance). -/
local instance matrix_secondCountableTopology' (r : ℕ) :
    SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin r → Fin r → ℂ))

/-- Matrices with the product topology are Polish (local). -/
local instance matrix_polishSpace' (r : ℕ) : PolishSpace (Matrix (Fin r) (Fin r) ℂ) :=
  inferInstanceAs (PolishSpace (Fin r → Fin r → ℂ))

/-- Bounded continuous functions separate points of a completely regular `T₁` space. -/
theorem exists_bcf_ne {Y : Type*} [TopologicalSpace Y] [CompletelyRegularSpace Y] [T1Space Y]
    {y y' : Y} (h : y ≠ y') : ∃ f : Y →ᵇ ℝ, f y ≠ f y' := by
  obtain ⟨f, hf, hfy, hfK⟩ := CompletelyRegularSpace.completely_regular y {y'}
    isClosed_singleton (by simpa using h)
  refine ⟨BoundedContinuousFunction.mkOfBound ⟨fun z => (f z : ℝ),
    continuous_subtype_val.comp hf⟩ 1 fun a c => ?_, ?_⟩
  · simp only [ContinuousMap.coe_mk, Real.dist_eq]
    have h1 := (f a).2
    have h2 := (f c).2
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · simp only [BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk]
    rw [hfy, hfK (Set.mem_singleton y')]
    simp

variable {E M : Type*} [TopologicalSpace E] [TopologicalSpace M]

/-- Product tests `(z, m) ↦ g(z)h(m)`. -/
def prodTest (g : E →ᵇ ℝ) (h : M →ᵇ ℝ) : (E × M) →ᵇ ℝ :=
  g.compContinuous ⟨Prod.fst, continuous_fst⟩ * h.compContinuous ⟨Prod.snd, continuous_snd⟩

theorem prodTest_apply (g : E →ᵇ ℝ) (h : M →ᵇ ℝ) (p : E × M) : prodTest g h p = g p.1 * h p.2 :=
  rfl

theorem prodTest_mul (g g' : E →ᵇ ℝ) (h h' : M →ᵇ ℝ) :
    prodTest g h * prodTest g' h' = prodTest (g * g') (h * h') := by
  ext p
  simp only [BoundedContinuousFunction.coe_mul, Pi.mul_apply, prodTest_apply]
  ring

/-- The span of product tests. -/
abbrev prodSpan (E M : Type*) [TopologicalSpace E] [TopologicalSpace M] :
    Submodule ℝ ((E × M) →ᵇ ℝ) :=
  Submodule.span ℝ (Set.range fun q : (E →ᵇ ℝ) × (M →ᵇ ℝ) => prodTest q.1 q.2)

theorem prodTest_mem (g : E →ᵇ ℝ) (h : M →ᵇ ℝ) : prodTest g h ∈ prodSpan E M :=
  Submodule.subset_span ⟨(g, h), rfl⟩

theorem prodSpan_mul_mem {f f' : (E × M) →ᵇ ℝ} (hf : f ∈ prodSpan E M) (hf' : f' ∈ prodSpan E M) :
    f * f' ∈ prodSpan E M := by
  induction hf using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨⟨g, h⟩, rfl⟩ := ha
    induction hf' using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨⟨g', h'⟩, rfl⟩ := hb
      rw [prodTest_mul]; exact prodTest_mem _ _
    | zero => rw [mul_zero]; exact zero_mem _
    | add b c _ _ hb hc => rw [mul_add]; exact add_mem hb hc
    | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hb
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha

theorem prodTest_one_one : prodTest (1 : E →ᵇ ℝ) (1 : M →ᵇ ℝ) = 1 := by
  ext p; simp [prodTest_apply]

/-- The star algebra spanned by product tests. -/
def prodAlg (E M : Type*) [TopologicalSpace E] [TopologicalSpace M] :
    StarSubalgebra ℝ ((E × M) →ᵇ ℝ) :=
  { (prodSpan E M).toSubalgebra (by rw [← prodTest_one_one]; exact prodTest_mem 1 1)
      (fun _ _ hx hy => prodSpan_mul_mem hx hy) with
    star_mem' := fun {a} ha => by
      have : star a = a := by ext p; simp
      rw [this]; exact ha }

theorem mem_prodAlg {f : (E × M) →ᵇ ℝ} : f ∈ prodAlg E M ↔ f ∈ prodSpan E M := Iff.rfl

theorem prodAlg_separatesPoints [CompletelyRegularSpace E] [T1Space E] [CompletelyRegularSpace M]
    [T1Space M] : ((prodAlg E M).map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  rintro ⟨z, m⟩ ⟨z', m'⟩ hne
  by_cases hz : z = z'
  · subst hz
    have hm : m ≠ m' := fun h => hne (by rw [h])
    obtain ⟨f, hf⟩ := exists_bcf_ne hm
    refine ⟨_, ⟨(BoundedContinuousFunction.toContinuousMapStarₐ ℝ) (prodTest 1 f),
      ⟨prodTest 1 f, prodTest_mem 1 f, rfl⟩, rfl⟩, ?_⟩
    simpa [prodTest_apply] using hf
  · obtain ⟨g, hg⟩ := exists_bcf_ne hz
    refine ⟨_, ⟨(BoundedContinuousFunction.toContinuousMapStarₐ ℝ) (prodTest g 1),
      ⟨prodTest g 1, prodTest_mem g 1, rfl⟩, rfl⟩, ?_⟩
    simpa [prodTest_apply] using hg

/-- A convergent sequence of probability measures on a Polish space is tight. -/
theorem isTightMeasureSet_of_tendsto' {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [PolishSpace Y] [BorelSpace Y] {u : ℕ → ProbabilityMeasure Y} {a : ProbabilityMeasure Y}
    (hu : Tendsto u atTop (𝓝 a)) : IsTightMeasureSet {((u n : ProbabilityMeasure Y) : Measure Y) | n} := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable Y
  have hK := hu.isCompact_insert_range
  have hcl : IsCompact (closure (Set.range u)) :=
    hK.of_isClosed_subset isClosed_closure (closure_minimal (Set.subset_insert _ _) hK.isClosed)
  refine (isTightMeasureSet_of_isCompact_closure hcl).subset ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨u n, ⟨n, rfl⟩, rfl⟩

omit [TopologicalSpace E] in

/-- Joint stable convergence: if an old random element `Z_n` in a Polish space converges in law to
`ν`, then `(Z_n, 𝒞_n)` converges in law to `ν ⊗ Law((C(x_a))_a)`. -/
theorem MatrixClosingStatement.stable_joint (h : MatrixClosingStatement) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) {r k : ℕ} (x : Fin k → ℝ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))} {C : Ω' → ℂ → Matrix (Fin r) (Fin r) ℂ}
    (hC : IsCanonicalCauchy r P' Ξ C)
    {Ωo : ℕ → Type*} [∀ n, MeasurableSpace (Ωo n)] (μo : ∀ n, Measure (Ωo n))
    [∀ n, IsProbabilityMeasure (μo n)]
    (W : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWt : Tendsto W atTop atTop) (e : ℕ → ℝ)
    (he : ∀ n, e n ∈ bulkInterval κ)
    (X : ∀ n, Ωo n → Matrix (Fin 2 × Fin (W n)) (Fin 2 × Fin (W n)) ℂ)
    (hXm : ∀ n, Measurable (X n)) (hXh : ∀ n, ∀ᵐ o ∂μo n, (X n o).IsHermitian)
    (J : ∀ n, Ωo n → Matrix (Fin 2 × Fin (W n)) (Fin r) ℂ) (hJm : ∀ n, Measurable (J n))
    (hJf : ∀ n, ∀ᵐ o ∂μo n, (J n o)ᴴ * J n o = 1)
    (hd : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => μo n {o | δ < matchedDistance b (e n) (X n o)}) atTop (𝓝 0))
    [TopologicalSpace E] [MeasurableSpace E] [PolishSpace E] [BorelSpace E]
    (Z : ∀ n, Ωo n → E) (hZm : ∀ n, Measurable (Z n)) (ν : Measure E) [IsProbabilityMeasure ν]
    (hZ : ∀ φ : E →ᵇ ℝ, Tendsto (fun n => ∫ o, φ (Z n o) ∂μo n) atTop (𝓝 (∫ z, φ z ∂ν)))
    (F : (E × (Fin k → Matrix (Fin r) (Fin r) ℂ)) →ᵇ ℝ) :
    Tendsto (fun n => ∫ p, F (Z n p.1, shiftedClosing b (e n) x (X n p.1) (J n p.1) p.2)
        ∂(μo n).prod (collarLaw (W n) b)) atTop
      (𝓝 (∫ q, F (q.1, fun a => C q.2 (x a)) ∂ν.prod P')) := by
  have := hC.decorated.prob
  set 𝒞 : ∀ n, Ωo n × CollarSample (W n) → Fin k → Matrix (Fin r) (Fin r) ℂ :=
    fun n p => shiftedClosing b (e n) x (X n p.1) (J n p.1) p.2
  have h𝒞 : ∀ n, Measurable (𝒞 n) := fun n =>
    measurable_shiftedClosing_prod b (e n) x (hXm n) (hJm n)
  set Cx : Ω' → Fin k → Matrix (Fin r) (Fin r) ℂ := fun ω a => C ω (x a)
  have hCx : Measurable Cx := by
    refine Measurable.of_eval fun a => ?_
    exact Measurable.of_eval_matrix _ fun i j => hC.measurable (x a) i j
  set jn : ∀ n, Ωo n × CollarSample (W n) → E × (Fin k → Matrix (Fin r) (Fin r) ℂ) :=
    fun n p => (Z n p.1, 𝒞 n p)
  have hjn : ∀ n, Measurable (jn n) := fun n => ((hZm n).comp measurable_fst).prodMk (h𝒞 n)
  set jl : E × Ω' → E × (Fin k → Matrix (Fin r) (Fin r) ℂ) := fun q => (q.1, Cx q.2)
  have hjl : Measurable jl := measurable_fst.prodMk (hCx.comp measurable_snd)
  -- product tests
  have hprod : ∀ (g : E →ᵇ ℝ) (h' : (Fin k → Matrix (Fin r) (Fin r) ℂ) →ᵇ ℝ),
      Tendsto (fun n => ∫ p, g (Z n p.1) * h' (𝒞 n p) ∂(μo n).prod (collarLaw (W n) b)) atTop
        (𝓝 ((∫ z, g z ∂ν) * ∫ ω, h' (Cx ω) ∂P')) := by
    intro g h'
    have hst := h.stable hb0 hb hκ x hC h' μo W hW hWt e he X hXm hXh J hJm hJf hd
      (fun n o => g (Z n o)) (fun n => g.continuous.measurable.comp (hZm n)) ‖g‖
      (fun n o => by rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm _)
    have h2 := hst.add ((hZ g).mul_const (∫ ω, h' (Cx ω) ∂P'))
    rw [zero_add] at h2
    refine h2.congr fun n => ?_
    simp only [Cx, 𝒞]
    ring
  set L : ℕ → ProbabilityMeasure (E × (Fin k → Matrix (Fin r) (Fin r) ℂ)) :=
    fun n => ⟨((μo n).prod (collarLaw (W n) b)).map (jn n), inferInstance⟩
  set Linf : ProbabilityMeasure (E × (Fin k → Matrix (Fin r) (Fin r) ℂ)) :=
    ⟨(ν.prod P').map jl, inferInstance⟩
  have hLint : ∀ n (f : (E × (Fin k → Matrix (Fin r) (Fin r) ℂ)) →ᵇ ℝ),
      ∫ y, f y ∂(L n : Measure (E × (Fin k → Matrix (Fin r) (Fin r) ℂ))) =
        ∫ p, f (jn n p) ∂(μo n).prod (collarLaw (W n) b) := fun n f =>
    integral_map (hjn n).aemeasurable f.continuous.aestronglyMeasurable
  have hLinfint : ∀ f : (E × (Fin k → Matrix (Fin r) (Fin r) ℂ)) →ᵇ ℝ,
      ∫ y, f y ∂(Linf : Measure (E × (Fin k → Matrix (Fin r) (Fin r) ℂ))) =
        ∫ q, f (jl q) ∂ν.prod P' := fun f =>
    integral_map hjl.aemeasurable f.continuous.aestronglyMeasurable
  suffices hT : Tendsto L atTop (𝓝 Linf) by
    have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hT) F
    simp only [hLint, hLinfint] at this
    exact this
  -- tightness of the marginals
  set LZ : ℕ → ProbabilityMeasure E := fun n => ⟨(μo n).map (Z n), inferInstance⟩
  set LZinf : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have htZ : Tendsto LZ atTop (𝓝 LZinf) := by
    refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun φ => ?_
    simp only [LZ, LZinf, ProbabilityMeasure.coe_mk]
    have e1 : ∀ n, ∫ z, φ z ∂(μo n).map (Z n) = ∫ o, φ (Z n o) ∂μo n := fun n =>
      integral_map (hZm n).aemeasurable φ.continuous.aestronglyMeasurable
    simp only [e1]
    exact hZ φ
  set LC : ℕ → ProbabilityMeasure (Fin k → Matrix (Fin r) (Fin r) ℂ) :=
    fun n => ⟨((μo n).prod (collarLaw (W n) b)).map (𝒞 n), inferInstance⟩
  set LCinf : ProbabilityMeasure (Fin k → Matrix (Fin r) (Fin r) ℂ) := ⟨P'.map Cx, inferInstance⟩
  have htC : Tendsto LC atTop (𝓝 LCinf) := by
    refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun φ => ?_
    simp only [LC, LCinf, ProbabilityMeasure.coe_mk]
    have e1 : ∀ n, ∫ m, φ m ∂((μo n).prod (collarLaw (W n) b)).map (𝒞 n) =
        ∫ p, (1 : E →ᵇ ℝ) (Z n p.1) * φ (𝒞 n p) ∂(μo n).prod (collarLaw (W n) b) := fun n => by
      rw [integral_map (h𝒞 n).aemeasurable φ.continuous.aestronglyMeasurable]
      simp
    have e2 : ∫ m, φ m ∂P'.map Cx = (∫ z, (1 : E →ᵇ ℝ) z ∂ν) * ∫ ω, φ (Cx ω) ∂P' := by
      rw [integral_map hCx.aemeasurable φ.continuous.aestronglyMeasurable]
      simp
    simp only [e1, e2]
    exact hprod 1 φ
  have htight : IsTightMeasureSet
      {((L n : ProbabilityMeasure (E × (Fin k → Matrix (Fin r) (Fin r) ℂ))) :
        Measure (E × (Fin k → Matrix (Fin r) (Fin r) ℂ))) | n} := by
    refine IsTightMeasureSet.prodMk ?_ ?_
    · refine (isTightMeasureSet_of_tendsto' htZ).subset ?_
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      refine ⟨n, ?_⟩
      simp only [L, LZ, ProbabilityMeasure.coe_mk]
      rw [show jn n = fun p => ((Z n ∘ Prod.fst) p, 𝒞 n p) from rfl,
        Measure.fst_map_prodMk ((hZm n).comp measurable_fst) (h𝒞 n),
        ← Measure.map_map (hZm n) measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
    · refine (isTightMeasureSet_of_tendsto' htC).subset ?_
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      refine ⟨n, ?_⟩
      simp only [L, LC, ProbabilityMeasure.coe_mk]
      exact (Measure.snd_map_prodMk ((hZm n).comp measurable_fst) (h𝒞 n)).symm
  refine ProbabilityMeasure.tendsto_of_tight_of_separatesPoints ℝ htight prodAlg_separatesPoints ?_
  intro f hf
  rw [mem_prodAlg] at hf
  induction hf using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨⟨g, h'⟩, rfl⟩ := ha
    simp only [hLint, hLinfint]
    simp only [prodTest_apply]
    have e3 : ∫ q, g (jl q).1 * h' (jl q).2 ∂ν.prod P' = (∫ z, g z ∂ν) * ∫ ω, h' (Cx ω) ∂P' :=
      integral_prod_mul (fun z => g z) (fun ω => h' (Cx ω))
    rw [e3]
    exact hprod g h'
  | zero => simp
  | add a c _ _ ha hc =>
    simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
    have e : ∀ μ : Measure (E × (Fin k → Matrix (Fin r) (Fin r) ℂ)), [IsFiniteMeasure μ] →
        ∫ y, (a y + c y) ∂μ = ∫ y, a y ∂μ + ∫ y, c y ∂μ := fun μ _ =>
      integral_add (a.integrable μ) (c.integrable μ)
    simp only [e]
    exact ha.add hc
  | smul t a _ ha =>
    simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul, integral_const_mul]
    exact ha.const_mul t

omit [TopologicalSpace E] in

/-- Joint stable convergence at the shift `0`: `(Z_n, closingMatrix at s = 0)` converges in law to
`ν ⊗ Law(C₀)` for a canonical Cauchy field at zero `C₀`. -/
theorem MatrixClosingStatement.stable_joint_atZero (h : MatrixClosingStatement) {b : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) {r : ℕ}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))} {C₀ : Ω' → Matrix (Fin r) (Fin r) ℂ}
    (hC₀ : IsCanonicalCauchyAtZero r P' Ξ C₀)
    {Ωo : ℕ → Type*} [∀ n, MeasurableSpace (Ωo n)] (μo : ∀ n, Measure (Ωo n))
    [∀ n, IsProbabilityMeasure (μo n)]
    (W : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWt : Tendsto W atTop atTop) (e : ℕ → ℝ)
    (he : ∀ n, e n ∈ bulkInterval κ)
    (X : ∀ n, Ωo n → Matrix (Fin 2 × Fin (W n)) (Fin 2 × Fin (W n)) ℂ)
    (hXm : ∀ n, Measurable (X n)) (hXh : ∀ n, ∀ᵐ o ∂μo n, (X n o).IsHermitian)
    (J : ∀ n, Ωo n → Matrix (Fin 2 × Fin (W n)) (Fin r) ℂ) (hJm : ∀ n, Measurable (J n))
    (hJf : ∀ n, ∀ᵐ o ∂μo n, (J n o)ᴴ * J n o = 1)
    (hd : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => μo n {o | δ < matchedDistance b (e n) (X n o)}) atTop (𝓝 0))
    [TopologicalSpace E] [MeasurableSpace E] [PolishSpace E] [BorelSpace E]
    (Z : ∀ n, Ωo n → E) (hZm : ∀ n, Measurable (Z n)) (ν : Measure E) [IsProbabilityMeasure ν]
    (hZ : ∀ φ : E →ᵇ ℝ, Tendsto (fun n => ∫ o, φ (Z n o) ∂μo n) atTop (𝓝 (∫ z, φ z ∂ν)))
    (F : (E × Matrix (Fin r) (Fin r) ℂ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ p, F (Z n p.1, closingMatrix b (e n) 0 (X n p.1) (J n p.1) p.2)
        ∂(μo n).prod (collarLaw (W n) b)) atTop
      (𝓝 (∫ q, F (q.1, C₀ q.2) ∂ν.prod P')) := by
  have := hC₀.decorated.prob
  obtain ⟨C, hC, hae⟩ := exists_isCanonicalCauchy_ae_eq hC₀
  let G : C(E × (Fin 1 → Matrix (Fin r) (Fin r) ℂ), E × Matrix (Fin r) (Fin r) ℂ) :=
    ⟨fun q => (q.1, q.2 0), continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd)⟩
  have hT := h.stable_joint hb0 hb hκ (fun _ : Fin 1 => (0 : ℝ)) hC μo W hW hWt e he X hXm hXh
    J hJm hJf hd Z hZm ν hZ (F.compContinuous G)
  have e1 : ∀ n, ∫ p, (F.compContinuous G) (Z n p.1, shiftedClosing b (e n) (fun _ => 0)
      (X n p.1) (J n p.1) p.2) ∂(μo n).prod (collarLaw (W n) b) =
      ∫ p, F (Z n p.1, closingMatrix b (e n) 0 (X n p.1) (J n p.1) p.2)
        ∂(μo n).prod (collarLaw (W n) b) := by
    intro n
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp [G, shiftedClosing, microShift_zero]
  have e2 : ∫ q, (F.compContinuous G) (q.1, fun _ : Fin 1 => C q.2 ((0 : ℝ) : ℂ)) ∂ν.prod P' =
      ∫ q, F (q.1, C₀ q.2) ∂ν.prod P' := by
    refine integral_congr_ae ?_
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hae] with q hq
    simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk, G,
      Complex.ofReal_zero]
    rw [hq]
  simp only [e1, e2] at hT
  exact hT

end Joint

end BlockBand.Critical.MatrixClosing
