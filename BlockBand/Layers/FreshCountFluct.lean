module

public import BlockBand.Layers.AbsorberCount
public import BlockBand.Layers.SchurInertia

/-!
# Fluctuation of the fresh negative count

The fluctuation field of the fresh-count lemma: expose the independent upper-triangular row
groups of `A`. Replacing one group changes the matrix by rank at most two and therefore changes
its negative count by at most two, and the bounded martingale-difference inequality gives
`‖N_- - E_A N_-‖_{L^p} ≤ C_p √W`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open scoped NNReal ENNReal Topology

section LinAlg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The form only sees the entries off row and column `a` on vectors vanishing at `a`. -/
theorem fc_quadForm_eq_of_eqOn {M M' : Matrix ι ι ℂ} (a : ι)
    (h : ∀ i j, i ≠ a → j ≠ a → M i j = M' i j) {x : ι → ℂ} (hx : x a = 0) :
    quadForm M x = quadForm M' x := by
  unfold quadForm
  congr 1
  simp only [dotProduct, mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = a
  · subst hi; simp [hx]
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = a
    · subst hj; simp [hx]
    · rw [h i j hi hj]

/-- **Row/column change of the negative count.** If two Hermitian matrices agree off the row and
the column of one index `a`, their negative counts differ by at most one (Cauchy interlacing,
via the variational characterization). -/
theorem fc_negativeCount_le_succ {M M' : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (hM' : M'.IsHermitian) (a : ι) (h : ∀ i j, i ≠ a → j ≠ a → M i j = M' i j) :
    negativeCount M ≤ negativeCount M' + 1 := by
  obtain ⟨V, hV, hdim⟩ := exists_isNegDefOn_finrank_eq_negativeCount hM
  let φ : (ι → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj a
  let K := LinearMap.ker φ
  have hneg : IsNegDefOn M' (V ⊓ K) := by
    intro x hx hx0
    have hxa : x a = 0 := hx.2
    rw [← fc_quadForm_eq_of_eqOn a h hxa]
    exact hV x hx.1 hx0
  have hle := finrank_le_negativeCount_of_isNegDefOn hM' hneg
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq V K
  have h2 : Module.finrank ℂ ↥(V ⊔ K) ≤ Fintype.card ι := by
    have := Submodule.finrank_le (V ⊔ K)
    simpa using this
  have h3 : Module.finrank ℂ ↥(LinearMap.range φ) + Module.finrank ℂ ↥K =
      Fintype.card ι := by
    have := LinearMap.finrank_range_add_finrank_ker φ
    simpa using this
  have h4 : Module.finrank ℂ ↥(LinearMap.range φ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range φ)
    simpa using this
  rw [← hdim]
  omega

/-- Two-sided version: `|N_-(M) - N_-(M')| ≤ 1`. -/
theorem fc_abs_negativeCount_sub_le {M M' : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (hM' : M'.IsHermitian) (a : ι) (h : ∀ i j, i ≠ a → j ≠ a → M i j = M' i j) :
    |(negativeCount M : ℝ) - negativeCount M'| ≤ 1 := by
  have h1 := fc_negativeCount_le_succ hM hM' a h
  have h2 := fc_negativeCount_le_succ hM' hM a fun i j hi hj => (h i j hi hj).symm
  rw [abs_le]
  constructor
  · have : (negativeCount M' : ℝ) ≤ negativeCount M + 1 := by exact_mod_cast h2
    linarith
  · have : (negativeCount M : ℝ) ≤ negativeCount M' + 1 := by exact_mod_cast h1
    linarith

omit [DecidableEq ι] in
/-- Homogeneity of the form under a real scalar. -/
theorem fc_quadForm_smul (M : Matrix ι ι ℂ) (r : ℝ) (x : ι → ℂ) :
    quadForm M ((r : ℂ) • x) = r ^ 2 * quadForm M x := by
  unfold quadForm
  rw [Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

/-- **Lower semicontinuity of `N_-`** along a continuous Hermitian family. -/
theorem fc_lowerSemicontinuous_negativeCount {X : Type*} [TopologicalSpace X]
    {M : X → Matrix ι ι ℂ} (hc : Continuous M) (hH : ∀ x, (M x).IsHermitian) :
    LowerSemicontinuous fun x => (negativeCount (M x) : ℝ) := by
  intro x₀ y hy
  obtain ⟨V, hV, hdim⟩ := exists_isNegDefOn_finrank_eq_negativeCount (hH x₀)
  set S : Set (ι → ℂ) := Metric.sphere 0 1 ∩ (V : Set (ι → ℂ)) with hS
  have hSc : IsCompact S :=
    (isCompact_sphere 0 1).inter_right (Submodule.closed_of_finiteDimensional V)
  have hcont : Continuous fun z : X × (ι → ℂ) => quadForm (M z.1) z.2 := by
    unfold quadForm
    refine Complex.continuous_re.comp ?_
    refine Continuous.dotProduct (continuous_star.comp continuous_snd) ?_
    exact Continuous.matrix_mulVec (hc.comp continuous_fst) continuous_snd
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ v ∈ S, quadForm (M x) v < 0 := by
    refine hSc.eventually_forall_of_forall_eventually fun v hv => ?_
    have hv0 : v ≠ 0 := by
      intro h0
      have := hv.1
      rw [h0, mem_sphere_iff_norm, sub_zero, norm_zero] at this
      exact zero_ne_one this
    have hlt : quadForm (M (x₀, v).1) (x₀, v).2 < 0 := hV v hv.2 hv0
    exact (hcont.continuousAt.eventually_lt continuousAt_const hlt)
  filter_upwards [hev] with x hx
  have hneg : IsNegDefOn (M x) V := by
    intro v hv hv0
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    set u : ι → ℂ := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hu
    have huS : u ∈ S := by
      refine ⟨?_, V.smul_mem _ hv⟩
      rw [mem_sphere_iff_norm, sub_zero, hu, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have hvu : v = ((‖v‖ : ℝ) : ℂ) • u := by
      rw [hu, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one,
        one_smul]
    rw [hvu, fc_quadForm_smul]
    exact mul_neg_of_pos_of_neg (by positivity) (hx u huS)
  have := finrank_le_negativeCount_of_isNegDefOn (hH x) hneg
  rw [hdim] at this
  calc y < negativeCount (M x₀) := hy
    _ ≤ negativeCount (M x) := by exact_mod_cast this

end LinAlg

section McDiarmid

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-- Bounded differences: changing one coordinate changes `f` by at most `c`. -/
def FcBddDiff {n : ℕ} (f : (Fin n → Ω₀) → ℝ) (c : ℝ) : Prop :=
  ∀ x y : Fin n → Ω₀, ∀ k : Fin n, (∀ j, j ≠ k → x j = y j) → |f x - f y| ≤ c

theorem fc_integrable_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)

theorem fc_abs_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    |∫ x, f x ∂μ| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := B)
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
  simpa [Real.norm_eq_abs] using this

theorem fc_exp_bound {B t m u : ℝ} (hu : |u| ≤ B) (hm : |m| ≤ B) :
    |Real.exp (t * (u - m))| ≤ Real.exp (|t| * (2 * B)) := by
  rw [abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  calc t * (u - m) ≤ |t * (u - m)| := le_abs_self _
    _ = |t| * |u - m| := abs_mul _ _
    _ ≤ |t| * (2 * B) := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc |u - m| ≤ |u| + |m| := abs_sub _ _
        _ ≤ 2 * B := by linarith

/-- **Bounded differences, exponential moment (McDiarmid).** Under a product of `n` copies of a
probability law, a bounded measurable `f` with one-coordinate differences at most `c` satisfies
`E exp(t (f - E f)) ≤ exp(n c² t² / 2)` for every real `t`. -/
theorem fc_mgf_le (μ₀ : Measure Ω₀) [IsProbabilityMeasure μ₀] :
    ∀ (n : ℕ) (f : (Fin n → Ω₀) → ℝ) (c B : ℝ), Measurable f → (∀ x, |f x| ≤ B) →
      FcBddDiff f c → ∀ t : ℝ,
      ∫ x, Real.exp (t * (f x - ∫ y, f y ∂Measure.pi fun _ => μ₀)) ∂(Measure.pi fun _ => μ₀) ≤
        Real.exp (n * c ^ 2 * t ^ 2 / 2) := by
  intro n
  induction n with
  | zero =>
    intro f c B hf hB hd t
    have hconst : ∀ x, f x = f default := fun x => by rw [Subsingleton.elim x default]
    simp_rw [hconst]
    simp
  | succ n ih =>
    intro f c B hf hB hd t
    obtain ⟨y₀⟩ := nonempty_of_isProbabilityMeasure μ₀
    set π' : Measure (Fin n → Ω₀) := Measure.pi fun _ => μ₀ with hπ'
    set π : Measure (Fin (n + 1) → Ω₀) := Measure.pi fun _ => μ₀ with hπ
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω₀) 0 with he
    have hmp : MeasurePreserving e π (μ₀.prod π') := measurePreserving_piFinSuccAbove _ 0
    have hsymm : ∀ p : Ω₀ × (Fin n → Ω₀), e.symm p = Fin.cons p.1 p.2 := by
      intro p
      simp [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
      rfl
    have hiter : ∀ F : (Fin (n + 1) → Ω₀) → ℝ, Measurable F → ∀ C : ℝ, (∀ x, |F x| ≤ C) →
        ∫ x, F x ∂π = ∫ x₀, ∫ x', F (Fin.cons x₀ x') ∂π' ∂μ₀ := by
      intro F hF C hFB
      rw [← hmp.symm.integral_comp' F]
      have hint : Integrable (fun p => F (e.symm p)) (μ₀.prod π') :=
        fc_integrable_of_bound (hF.comp e.symm.measurable) C fun p => hFB _
      rw [integral_prod _ hint]
      simp_rw [hsymm]
    have hfc : Measurable fun p : Ω₀ × (Fin n → Ω₀) => f (Fin.cons p.1 p.2) := by
      have := hf.comp e.symm.measurable
      convert this using 1
      funext p
      simp [hsymm]
    set h : Ω₀ → (Fin n → Ω₀) → ℝ := fun x₀ x' => f (Fin.cons x₀ x') with hh
    have hhm : ∀ x₀, Measurable (h x₀) := fun x₀ => hfc.comp measurable_prodMk_left
    have hhB : ∀ x₀ x', |h x₀ x'| ≤ B := fun x₀ x' => hB _
    have hhd : ∀ x₀, FcBddDiff (h x₀) c := by
      intro x₀ x y k hk
      refine hd _ _ k.succ fun j hj => ?_
      induction j using Fin.cases with
      | zero => simp
      | succ j' =>
        have : j' ≠ k := fun h' => hj (by rw [h'])
        simpa using hk j' this
    set g : Ω₀ → ℝ := fun x₀ => ∫ x', h x₀ x' ∂π' with hg
    have hgm : Measurable g := hfc.stronglyMeasurable.integral_prod_right'.measurable
    have hgB : ∀ x₀, |g x₀| ≤ B := fun x₀ => fc_abs_integral_le B (hhB x₀)
    have hgd : ∀ x₀ y₀, |g x₀ - g y₀| ≤ c := by
      intro x₀ y₀
      have hsub : g x₀ - g y₀ = ∫ x', (h x₀ x' - h y₀ x') ∂π' := by
        rw [hg, integral_sub (fc_integrable_of_bound (hhm x₀) B (hhB x₀))
          (fc_integrable_of_bound (hhm y₀) B (hhB y₀))]
      rw [hsub]
      refine fc_abs_integral_le c fun x' => hd _ _ 0 fun j hj => ?_
      induction j using Fin.cases with
      | zero => exact absurd rfl hj
      | succ j' => simp
    set m : ℝ := ∫ y, f y ∂π with hm
    have hmg : m = ∫ x₀, g x₀ ∂μ₀ := hiter f hf B hB
    have hmB : |m| ≤ B := fc_abs_integral_le B hB
    -- inner bound
    have hinner : ∀ x₀, ∫ x', Real.exp (t * (h x₀ x' - g x₀)) ∂π' ≤
        Real.exp (n * c ^ 2 * t ^ 2 / 2) := fun x₀ =>
      ih (h x₀) c B (hhm x₀) (hhB x₀) (hhd x₀) t
    -- Hoeffding for `g`
    have hhoeff := hasSubgaussianMGF_of_mem_Icc (μ := μ₀) (X := g) (a := g y₀ - c)
      (b := g y₀ + c) hgm.aemeasurable (Filter.Eventually.of_forall fun x₀ => by
        have := hgd x₀ y₀
        rw [abs_le] at this
        exact ⟨by linarith, by linarith⟩)
    have hcpar : (((‖(g y₀ + c) - (g y₀ - c)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = c ^ 2 := by
      push_cast
      rw [Real.norm_eq_abs]
      have : g y₀ + c - (g y₀ - c) = 2 * c := by ring
      rw [this, abs_mul, abs_two, mul_div_assoc, mul_div_cancel₀ _ (two_ne_zero' ℝ), sq_abs]
    have houter : ∫ x₀, Real.exp (t * (g x₀ - m)) ∂μ₀ ≤ Real.exp (c ^ 2 * t ^ 2 / 2) := by
      have := hhoeff.mgf_le t
      rw [hcpar] at this
      rw [hmg]
      simpa [mgf] using this
    -- assemble
    have hF : Measurable fun x => Real.exp (t * (f x - m)) := by fun_prop
    rw [hiter (fun x => Real.exp (t * (f x - m))) hF _ (fun x => fc_exp_bound (hB x) hmB)]
    have hsplit : ∀ x₀, ∫ x', Real.exp (t * (f (Fin.cons x₀ x') - m)) ∂π' =
        Real.exp (t * (g x₀ - m)) * ∫ x', Real.exp (t * (h x₀ x' - g x₀)) ∂π' := by
      intro x₀
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
      simp only [hh]
      rw [← Real.exp_add]
      ring_nf
    simp_rw [hsplit]
    have hK : 0 ≤ Real.exp (n * c ^ 2 * t ^ 2 / 2) := (Real.exp_pos _).le
    calc ∫ x₀, Real.exp (t * (g x₀ - m)) * ∫ x', Real.exp (t * (h x₀ x' - g x₀)) ∂π' ∂μ₀
        ≤ ∫ x₀, Real.exp (t * (g x₀ - m)) * Real.exp (n * c ^ 2 * t ^ 2 / 2) ∂μ₀ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x₀ => ?_) ?_
            (Filter.Eventually.of_forall fun x₀ => ?_)
          · exact mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => (Real.exp_pos _).le)
          · refine Integrable.mul_const ?_ _
            exact fc_integrable_of_bound (by fun_prop) _ fun x₀ => fc_exp_bound (hgB x₀) hmB
          · exact mul_le_mul_of_nonneg_left (hinner x₀) (Real.exp_pos _).le
      _ = (∫ x₀, Real.exp (t * (g x₀ - m)) ∂μ₀) * Real.exp (n * c ^ 2 * t ^ 2 / 2) :=
          integral_mul_const _ _
      _ ≤ Real.exp (c ^ 2 * t ^ 2 / 2) * Real.exp (n * c ^ 2 * t ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right houter hK
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * c ^ 2 * t ^ 2 / 2) := by
          rw [← Real.exp_add]; push_cast; ring_nf

end McDiarmid

section Moments

/-- `y^p ≤ a^p e^{p y / a}` for `y ≥ 0`, `a > 0`, `p ≥ 0`. -/
theorem fc_rpow_le_exp {y a p : ℝ} (hy : 0 ≤ y) (ha : 0 < a) (hp : 0 ≤ p) :
    y ^ p ≤ a ^ p * Real.exp (p * y / a) := by
  have hya : 0 ≤ y / a := div_nonneg hy ha.le
  have h1 : y / a ≤ Real.exp (y / a - 1) := by linarith [Real.add_one_le_exp (y / a - 1)]
  have h2 : (y / a) ^ p ≤ Real.exp (y / a - 1) ^ p := Real.rpow_le_rpow hya h1 hp
  rw [← Real.exp_mul] at h2
  have h3 : Real.exp ((y / a - 1) * p) ≤ Real.exp (p * y / a) := by
    refine Real.exp_le_exp.mpr ?_
    have : (y / a - 1) * p = p * y / a - p := by ring
    linarith
  have h4 : y = a * (y / a) := by field_simp
  calc y ^ p = a ^ p * (y / a) ^ p := by
        conv_lhs => rw [h4]
        exact Real.mul_rpow ha.le hya
    _ ≤ a ^ p * Real.exp (p * y / a) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (Real.rpow_nonneg ha.le _)

theorem fc_exp_abs_le (u : ℝ) : Real.exp |u| ≤ Real.exp u + Real.exp (-u) := by
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-u)]
  · rw [abs_of_nonpos h]; linarith [Real.exp_pos u]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- **Moments from a sub-Gaussian exponential bound.** If `E e^{tX} ≤ e^{s t²/2}` for all `t`,
then `E|X|^p ≤ (p √s)^p · 2 e^{1/2}`. -/
theorem fc_integral_rpow_le {X : α → ℝ} (hX : Measurable X) (B : ℝ) (hB : ∀ x, |X x| ≤ B)
    {s : ℝ} (hs : 0 < s) (hmgf : ∀ t : ℝ, ∫ x, Real.exp (t * X x) ∂μ ≤ Real.exp (s * t ^ 2 / 2))
    {p : ℝ} (hp : 1 ≤ p) :
    ∫ x, |X x| ^ p ∂μ ≤ (p * Real.sqrt s) ^ p * (2 * Real.exp (1 / 2)) := by
  set σ := Real.sqrt s with hσ
  have hσpos : 0 < σ := Real.sqrt_pos.mpr hs
  have hp0 : 0 < p := by linarith
  have ha : 0 < p * σ := mul_pos hp0 hσpos
  have hpt : ∀ x, |X x| ^ p ≤
      (p * σ) ^ p * (Real.exp (σ⁻¹ * X x) + Real.exp ((-σ⁻¹) * X x)) := by
    intro x
    refine (fc_rpow_le_exp (abs_nonneg _) ha hp0.le).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ha.le _)
    have : p * |X x| / (p * σ) = |σ⁻¹ * X x| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hσpos)]
      field_simp
    rw [this]
    have := fc_exp_abs_le (σ⁻¹ * X x)
    simpa [neg_mul] using this
  have hexpint : ∀ t : ℝ, Integrable (fun x => Real.exp (t * X x)) μ := by
    intro t
    refine fc_integrable_of_bound (by fun_prop) (Real.exp (|t| * B)) fun x => ?_
    rw [abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    calc t * X x ≤ |t * X x| := le_abs_self _
      _ = |t| * |X x| := abs_mul _ _
      _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hB x) (abs_nonneg _)
  have hst : s * σ⁻¹ ^ 2 / 2 = 1 / 2 := by
    rw [inv_pow, hσ, Real.sq_sqrt hs.le]
    field_simp
  have hst' : s * (-σ⁻¹) ^ 2 / 2 = 1 / 2 := by rw [neg_sq]; exact hst
  calc ∫ x, |X x| ^ p ∂μ
      ≤ ∫ x, (p * σ) ^ p * (Real.exp (σ⁻¹ * X x) + Real.exp ((-σ⁻¹) * X x)) ∂μ := by
        refine integral_mono ?_ ?_ hpt
        · refine fc_integrable_of_bound (by fun_prop) (B ^ p) fun x => ?_
          rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
          exact Real.rpow_le_rpow (abs_nonneg _) (hB x) hp0.le
        · exact ((hexpint _).add (hexpint _)).const_mul _
    _ = (p * σ) ^ p * ((∫ x, Real.exp (σ⁻¹ * X x) ∂μ) + ∫ x, Real.exp ((-σ⁻¹) * X x) ∂μ) := by
        rw [integral_const_mul, integral_add (hexpint _) (hexpint _)]
    _ ≤ (p * σ) ^ p * (Real.exp (1 / 2) + Real.exp (1 / 2)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (Real.rpow_nonneg ha.le _)
        · exact (hmgf _).trans (le_of_eq (by rw [hst]))
        · exact (hmgf _).trans (le_of_eq (by rw [hst']))
    _ = (p * σ) ^ p * (2 * Real.exp (1 / 2)) := by ring

/-- **`L^p` norm from a sub-Gaussian exponential bound:**
`‖X‖_p ≤ 2 e^{1/2} p √s`. -/
theorem fc_eLpNorm_le {X : α → ℝ} (hX : Measurable X) (B : ℝ) (hB : ∀ x, |X x| ≤ B)
    {s : ℝ} (hs : 0 < s) (hmgf : ∀ t : ℝ, ∫ x, Real.exp (t * X x) ∂μ ≤ Real.exp (s * t ^ 2 / 2))
    {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm X (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (2 * Real.exp (1 / 2) * p * Real.sqrt s) := by
  have hp0 : 0 < p := by linarith
  have hmem : MemLp X (ENNReal.ofReal p) μ :=
    MemLp.of_bound hX.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by simpa using hp0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  refine ENNReal.ofReal_le_ofReal ?_
  simp_rw [Real.norm_eq_abs]
  set K := 2 * Real.exp (1 / 2) with hK
  have hK1 : 1 ≤ K := by
    have := Real.one_le_exp (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [hK]; linarith
  have ha : 0 ≤ p * Real.sqrt s := mul_nonneg hp0.le (Real.sqrt_nonneg _)
  have hI := fc_integral_rpow_le hX B hB hs hmgf hp
  have hInn : 0 ≤ ∫ x, |X x| ^ p ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
  calc (∫ x, |X x| ^ p ∂μ) ^ p⁻¹ ≤ ((p * Real.sqrt s) ^ p * K) ^ p⁻¹ :=
        Real.rpow_le_rpow hInn hI (inv_nonneg.mpr hp0.le)
    _ = p * Real.sqrt s * K ^ p⁻¹ := by
        rw [Real.mul_rpow (Real.rpow_nonneg ha _) (by linarith),
          Real.rpow_rpow_inv ha hp0.ne']
    _ ≤ p * Real.sqrt s * K := by
        refine mul_le_mul_of_nonneg_left ?_ ha
        calc K ^ p⁻¹ ≤ K ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hK1 (inv_le_one_of_one_le₀ hp)
          _ = K := Real.rpow_one K
    _ = K * p * Real.sqrt s := by ring

end Moments

section GUERows

open BlockBand.SourceProcess (circularBrownianCoordinates)
open scoped ComplexConjugate

/-- The real coordinates of one row group `a`: `r_{(a,b),s}`, `b : Fin W`, `s : Fin 2`. -/
abbrev FcRow (W : ℕ) := Fin W × Fin 2 → ℝ

/-- Law of one row group: i.i.d. standard real Gaussians. -/
def fcRowLaw (W : ℕ) : Measure (FcRow W) := Measure.pi fun _ => gaussianReal 0 1

instance fcRowLaw_isProbability (W : ℕ) : IsProbabilityMeasure (fcRowLaw W) := by
  unfold fcRowLaw; infer_instance

/-- Flattening of the row groups into the coordinates of `stdGaussCoordLaw`. -/
def fcFlatten (W : ℕ) (x : Fin W → FcRow W) : GaussCoord W → ℝ := fun i => x i.1.1 (i.1.2, i.2)

theorem continuous_fcFlatten (W : ℕ) : Continuous (fcFlatten W) :=
  continuous_pi fun i => (continuous_apply (i.1.2, i.2)).comp (continuous_apply i.1.1)

theorem measurable_fcFlatten (W : ℕ) : Measurable (fcFlatten W) :=
  (continuous_fcFlatten W).measurable

/-- The row groups are independent: the flattened product is `stdGaussCoordLaw`. -/
theorem fc_map_flatten (W : ℕ) :
    (Measure.pi fun _ : Fin W => fcRowLaw W).map (fcFlatten W) = stdGaussCoordLaw (GaussCoord W) := by
  unfold stdGaussCoordLaw
  symm
  refine Measure.pi_eq fun S hS => ?_
  rw [Measure.map_apply (measurable_fcFlatten W) (MeasurableSet.univ_pi hS)]
  have hpre : fcFlatten W ⁻¹' Set.univ.pi S =
      Set.univ.pi fun a : Fin W => Set.univ.pi fun bs : Fin W × Fin 2 => S ((a, bs.1), bs.2) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, fcFlatten]
    constructor
    · intro h a bs; exact h ((a, bs.1), bs.2)
    · intro h i; exact h i.1.1 (i.1.2, i.2)
  rw [hpre, Measure.pi_pi]
  simp_rw [fcRowLaw, Measure.pi_pi]
  simp only [Fintype.prod_prod_type]

theorem continuous_gueOfCoords (W : ℕ) (t : ℝ≥0) : Continuous (gueOfCoords W t) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [gueOfCoords, gueSample, circularBrownianCoordinates, Matrix.of_apply]
  have hc : Continuous (fun z : ℂ => conj z) := Complex.continuous_conj
  fun_prop

/-- `gueMeasure` realized on the independent row groups. -/
theorem fc_gueMeasure_eq_map (W : ℕ) (t : ℝ≥0) :
    gueMeasure (Fin W) t =
      (Measure.pi fun _ : Fin W => fcRowLaw W).map (gueOfCoords W t ∘ fcFlatten W) := by
  rw [gueMeasure_eq_map, ← fc_map_flatten,
    Measure.map_map (measurable_gueOfCoords W t) (measurable_fcFlatten W)]

theorem fc_ae_isHermitian_gue (W : ℕ) (t : ℝ≥0) :
    ∀ᵐ A ∂gueMeasure (Fin W) t, A.IsHermitian := by
  have hS : MeasurableSet {A : Matrix (Fin W) (Fin W) ℂ | A.IsHermitian} :=
    (isClosed_eq (by fun_prop : Continuous (fun A : Matrix (Fin W) (Fin W) ℂ => Aᴴ))
      continuous_id).measurableSet
  rw [gueMeasure_eq_map, ae_map_iff (measurable_gueOfCoords W t).aemeasurable hS]
  exact Filter.Eventually.of_forall fun r => gueOfCoords_isHermitian W t r

/-- The entries of a GUE sample off row and column `k` do not see row group `k`. -/
theorem fc_gueOfCoords_eqOn (W : ℕ) (t : ℝ≥0) {x y : Fin W → FcRow W} (k : Fin W)
    (hxy : ∀ j, j ≠ k → x j = y j) (i j : Fin W) (hi : i ≠ k) (hj : j ≠ k) :
    gueOfCoords W t (fcFlatten W x) i j = gueOfCoords W t (fcFlatten W y) i j := by
  simp only [gueOfCoords, gueSample, circularBrownianCoordinates, Matrix.of_apply, fcFlatten,
    hxy i hi, hxy j hj]

theorem fc_isHermitian_shift {ι : Type*} [Fintype ι] [DecidableEq ι] {H F : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hF : F.IsHermitian) (E : ℝ) :
    (H - (E : ℂ) • (1 : Matrix ι ι ℂ) - F).IsHermitian := by
  refine (hH.sub ?_).sub hF
  exact isHermitian_one.smul (by simp [IsSelfAdjoint])

theorem fc_negativeCount_le_card {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    negativeCount M ≤ Fintype.card ι := by
  unfold negativeCount
  split_ifs
  · exact (Finset.card_filter_le _ _).trans (by simp)
  · exact Nat.zero_le _

/-- The fresh count on the row-group coordinates. -/
def fcRowCount (W : ℕ) (t : ℝ≥0) (E : ℝ) (F : Matrix (Fin W) (Fin W) ℂ)
    (x : Fin W → FcRow W) : ℝ :=
  (negativeCount (gueOfCoords W t (fcFlatten W x) - (E : ℂ) • 1 - F) : ℝ)

theorem fcRowCount_bddDiff (W : ℕ) (t : ℝ≥0) (E : ℝ) {F : Matrix (Fin W) (Fin W) ℂ}
    (hF : F.IsHermitian) : FcBddDiff (fcRowCount W t E F) 1 := by
  intro x y k hxy
  refine fc_abs_negativeCount_sub_le (fc_isHermitian_shift (gueOfCoords_isHermitian _ _ _) hF E)
    (fc_isHermitian_shift (gueOfCoords_isHermitian _ _ _) hF E) k fun i j hi hj => ?_
  simp only [Matrix.sub_apply, fc_gueOfCoords_eqOn W t k hxy i j hi hj]

theorem fcRowCount_abs_le (W : ℕ) (t : ℝ≥0) (E : ℝ) (F : Matrix (Fin W) (Fin W) ℂ)
    (x : Fin W → FcRow W) : |fcRowCount W t E F x| ≤ W := by
  unfold fcRowCount
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  have := fc_negativeCount_le_card (gueOfCoords W t (fcFlatten W x) - (E : ℂ) • 1 - F)
  simp only [Fintype.card_fin] at this
  exact_mod_cast this

theorem measurable_fcRowCount (W : ℕ) (t : ℝ≥0) (E : ℝ) {F : Matrix (Fin W) (Fin W) ℂ}
    (hF : F.IsHermitian) : Measurable (fcRowCount W t E F) := by
  refine LowerSemicontinuous.measurable ?_
  refine fc_lowerSemicontinuous_negativeCount (M := fun x =>
    gueOfCoords W t (fcFlatten W x) - (E : ℂ) • 1 - F) ?_ fun x =>
      fc_isHermitian_shift (gueOfCoords_isHermitian _ _ _) hF E
  exact (((continuous_gueOfCoords W t).comp (continuous_fcFlatten W)).sub continuous_const).sub
    continuous_const

/-- The count with the Hermitian part, measurable on all matrices. -/
def fcHermCount {W : ℕ} (E : ℝ) (F : Matrix (Fin W) (Fin W) ℂ) (A : Matrix (Fin W) (Fin W) ℂ) :
    ℝ :=
  (negativeCount (hermPart A - (E : ℂ) • 1 - F) : ℝ)

theorem measurable_fcHermCount {W : ℕ} (E : ℝ) {F : Matrix (Fin W) (Fin W) ℂ}
    (hF : F.IsHermitian) : Measurable (fcHermCount E F) := by
  refine LowerSemicontinuous.measurable ?_
  refine fc_lowerSemicontinuous_negativeCount (M := fun A =>
    hermPart A - (E : ℂ) • 1 - F) ?_ fun A => fc_isHermitian_shift (hermPart_isHermitian _) hF E
  have : Continuous (hermPart (ι := Fin W)) := by
    unfold hermPart
    have h1 : Continuous fun A : Matrix (Fin W) (Fin W) ℂ => A + Aᴴ :=
      continuous_id.add continuous_id.matrix_conjTranspose
    exact (continuous_const (y := (1 / 2 : ℂ))).smul h1
  exact (this.sub continuous_const).sub continuous_const

theorem fcHermCount_ae_eq (W : ℕ) (t : ℝ≥0) (E : ℝ) (F : Matrix (Fin W) (Fin W) ℂ) :
    (fun A => (negativeCount (A - (E : ℂ) • 1 - F) : ℝ)) =ᵐ[gueMeasure (Fin W) t]
      fcHermCount E F := by
  filter_upwards [fc_ae_isHermitian_gue W t] with A hA
  simp only [fcHermCount, hermPart_of_isHermitian hA]

theorem fcHermCount_comp (W : ℕ) (t : ℝ≥0) (E : ℝ) (F : Matrix (Fin W) (Fin W) ℂ) :
    fcHermCount E F ∘ (gueOfCoords W t ∘ fcFlatten W) = fcRowCount W t E F := by
  funext x
  simp only [Function.comp_apply, fcHermCount, fcRowCount,
    hermPart_of_isHermitian (gueOfCoords_isHermitian _ _ _)]

/-- **Fluctuation of the fresh count**, any GUE variance `t`: for every Hermitian `F`, real `E`
and `p ≥ 1`, `‖N_-(A - E - F) - E N_-‖_{L^p(GUE_W(t))} ≤ 2 e^{1/2} p √W`. -/
theorem fc_fluctuation_le (W : ℕ) (hW : 0 < W) (t : ℝ≥0) (E : ℝ)
    {F : Matrix (Fin W) (Fin W) ℂ} (hF : F.IsHermitian) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun A => (negativeCount (A - (E : ℂ) • 1 - F) : ℝ) -
        ∫ A', (negativeCount (A' - (E : ℂ) • 1 - F) : ℝ) ∂gueMeasure (Fin W) t)
        (ENNReal.ofReal p) (gueMeasure (Fin W) t) ≤
      ENNReal.ofReal (2 * Real.exp (1 / 2) * p * Real.sqrt W) := by
  set ν : Measure (Fin W → FcRow W) := Measure.pi fun _ => fcRowLaw W with hν
  set T := gueOfCoords W t ∘ fcFlatten W with hT
  have hTm : Measurable T := (measurable_gueOfCoords W t).comp (measurable_fcFlatten W)
  have hμ : gueMeasure (Fin W) t = ν.map T := fc_gueMeasure_eq_map W t
  have hae := fcHermCount_ae_eq W t E F
  rw [integral_congr_ae hae]
  have hint : ∫ A, fcHermCount E F A ∂gueMeasure (Fin W) t = ∫ x, fcRowCount W t E F x ∂ν := by
    rw [hμ, integral_map hTm.aemeasurable (measurable_fcHermCount E hF).aestronglyMeasurable,
      ← fcHermCount_comp W t E F]
    rfl
  rw [hint]
  set m := ∫ x, fcRowCount W t E F x ∂ν with hm
  have hae' : (fun A => (negativeCount (A - (E : ℂ) • 1 - F) : ℝ) - m) =ᵐ[gueMeasure (Fin W) t]
      fun A => fcHermCount E F A - m := by
    filter_upwards [hae] with A hA
    rw [hA]
  rw [eLpNorm_congr_ae hae', hμ, eLpNorm_map_measure
    ((measurable_fcHermCount E hF).sub_const m).aestronglyMeasurable hTm.aemeasurable]
  have hcomp : (fun A => fcHermCount E F A - m) ∘ T = fun x => fcRowCount W t E F x - m := by
    funext x
    simp only [Function.comp_apply]
    rw [← fcHermCount_comp W t E F]
    rfl
  rw [hcomp]
  have hmB : |m| ≤ W := fc_abs_integral_le _ (fcRowCount_abs_le W t E F)
  have hmgf := fc_mgf_le (fcRowLaw W) W (fcRowCount W t E F) 1 W (measurable_fcRowCount W t E hF)
    (fcRowCount_abs_le W t E F) (fcRowCount_bddDiff W t E hF)
  refine fc_eLpNorm_le ((measurable_fcRowCount W t E hF).sub_const m) (2 * W)
    (fun x => ?_) (s := W) (by exact_mod_cast hW) (fun s => ?_) hp
  · calc |fcRowCount W t E F x - m| ≤ |fcRowCount W t E F x| + |m| := abs_sub _ _
      _ ≤ 2 * W := by linarith [fcRowCount_abs_le W t E F x]
  · simpa using hmgf s

/-- **The fresh-count lemma, fluctuation field**. No hypothesis:
for every `b ∈ (0,1/2)` and `p ≥ 1`, with `C_p = 2 e^{1/2} p`, for every `W ≥ 1`, Hermitian
`F` and real `E`, `‖N_-(A - E - F) - E_A N_-‖_{L^p} ≤ C_p √W` under `A ~ GUE_W(c/W)`. -/
theorem freshCount_fluctuation : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ p : ℝ, 1 ≤ p → ∃ Cp : ℝ,
    ∀ (W : ℕ), 0 < W → ∀ F : Matrix (Fin W) (Fin W) ℂ, F.IsHermitian → ∀ E : ℝ,
      let μ := gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))
      eLpNorm (fun A => (negativeCount (A - (E : ℂ) • 1 - F) : ℝ) -
          ∫ A', (negativeCount (A' - (E : ℂ) • 1 - F) : ℝ) ∂μ) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Cp * Real.sqrt W) := by
  intro b _ _ p hp
  refine ⟨2 * Real.exp (1 / 2) * p, fun W hW F hF E => ?_⟩
  exact fc_fluctuation_le W hW _ E hF hp

end GUERows

end BlockBand.Layers
