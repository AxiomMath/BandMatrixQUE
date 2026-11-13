module

public import BlockBand.Layers.FullEnergyPath

/-!
# The energy derivative of the one- and two-block cores (`FetCoreBound`)

The cores in the energy paragraph of the proof of the tagged-trace lemma ("The finite-core
derivatives follow by differentiating their stable finite mean equations"):
`fetCoreBound_holds (hcount) (hgrad) : FetCoreBound`.

## Proof (in place of differentiating the core mean equations)

For the cores there is no source: along the energy the augmented core matrix
`N(E) = [[H - E, B_p], [B_p*, z_∂(E)]]` (`fetCN`) moves by the *bounded* insertion
`N'(E) = diag(-1, z_∂'(E)) = tgtD0 (z_∂')`, and the path trace is its port block,
`W⁻¹ Tr(R_r)_{ii} = W⁻¹ Tr[N(E)⁻¹]_{port, ii}` (`fetC_trace_eq`, Schur complement). Hence:

1. **Derivative identity** (`fetC_fetFd_eq`): `f'_{r,i} = fetFd(X_r, X_r')_i = -W⁻¹Tr[N⁻¹N'N⁻¹]_{port,ii}`
   (derivative uniqueness: `E ↦ W⁻¹Tr(z_∂ - X_r)⁻¹_{ii}` has derivative `fetFd` and agrees near
   `E` with `E ↦ W⁻¹ Tr[N(E)⁻¹]_{port,ii}`).
2. **Second-order remainder** (`fetC_inv_rem`): with `N₁ = N(E + h)`, `N₀ = N(E)`,
   `N₁⁻¹ - N₀⁻¹ + h N₀⁻¹N'N₀⁻¹ = -N₀⁻¹(Δ - hN')N₀⁻¹ + N₁⁻¹ΔN₀⁻¹ΔN₀⁻¹`, `Δ = N₁ - N₀`, and
   `‖Δ - hN'‖ ≤ |z_∂(E+h) - z_∂(E) - h z_∂'(E)| ≤ L h²`, `‖Δ‖ ≤ C h` (`fetC_scalar`: `a'`, `z_∂'`
   are Lipschitz on `bulkInterval (κ/2)`).
3. **Interpolation** (`fetC_pointwise`): for every `i`,
   `h |f'_i - a'| ≤ |f_i(E+h) - a(E+h)| + |f_i(E) - a(E)| + h² K(1 + 2‖N₀⁻¹‖³ + ‖N₁⁻¹‖³) + L h²`.
4. **Moments** (`fetC_core_absorb`): under `pathLaw W r b`, `r ∈ {1, 2}`, `N(E)` is a.s. invertible
   and `‖ ‖N(E)⁻¹‖ ‖_{L^q} ≤ C_A` for `q ≤ ε₁ W` (the Gaussian absorption lemma: `r = 1` is the
   `.oneBlockTwoPorts` layer with `X = 0`, `r = 2` the `.separate` layer with `X = -coreOff β`,
   uniformly in `β`). The values are the matched-traces theorem (`path`, `‖·‖_p ≤ C √p / W`).
5. With `h = W^{-1/2}`: `‖max_i |f'_i - a'|‖_p ≤ 2C√p'·W^{1/2}/W + C' W^{-1/2} = C''/√W`.

This uses only values of the cores (the matched-traces theorem) and resolvent moments (the
Gaussian absorption lemma); the derivative is never differentiated under the expectation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. Scalar facts: Lipschitz derivatives of `a` and `z_∂` on the bulk
-/

/-- A first-order Taylor remainder from a Lipschitz derivative on `[E, E + h]`. -/
theorem fetC_taylor {f f' : ℝ → ℂ} {E h L : ℝ} (hh : 0 ≤ h) (hL0 : 0 ≤ L)
    (hd : ∀ t ∈ Set.Icc E (E + h), HasDerivAt f (f' t) t)
    (hl : ∀ t ∈ Set.Icc E (E + h), ‖f' t - f' E‖ ≤ L * (t - E)) :
    ‖f (E + h) - f E - (h : ℂ) * f' E‖ ≤ L * h * h := by
  set φ : ℝ → ℂ := fun t => f t - (t : ℂ) * f' E with hφ
  have hφd : ∀ t ∈ Set.Icc E (E + h), HasDerivWithinAt φ (f' t - f' E) (Set.Icc E (E + h)) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * f' E) (1 * f' E) t :=
      (hasDerivAt_id t).ofReal_comp.mul_const _
    rw [one_mul] at h1
    exact ((hd t ht).sub h1).hasDerivWithinAt
  have hb : ∀ t ∈ Set.Ico E (E + h), ‖f' t - f' E‖ ≤ L * h := by
    intro t ht
    have h1 := hl t (Set.Ico_subset_Icc_self ht)
    calc ‖f' t - f' E‖ ≤ L * (t - E) := h1
      _ ≤ L * h := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hL0
  have := norm_image_sub_le_of_norm_deriv_le_segment' hφd hb (E + h) ⟨by linarith, le_rfl⟩
  have e : φ (E + h) - φ E = f (E + h) - f E - (h : ℂ) * f' E := by
    simp only [hφ]; push_cast; ring
  rw [e] at this
  calc _ ≤ L * h * (E + h - E) := this
    _ = L * h * h := by ring

theorem fetC_bulk_mono {κ E : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    E ∈ bulkInterval (κ / 2) :=
  ⟨by linarith [hE.1], by linarith [hE.2]⟩

theorem fetC_bulk_shift {κ E h : ℝ} (hE : E ∈ bulkInterval κ) (hh : 0 ≤ h) (hhk : h ≤ κ / 2)
    {t : ℝ} (ht : t ∈ Set.Icc E (E + h)) : t ∈ bulkInterval (κ / 2) :=
  ⟨by linarith [hE.1, ht.1], by linarith [hE.2, ht.2]⟩

/-- On `bulkInterval κ`, `|1 - a²| ≥ √κ`. -/
theorem fetC_one_sub_sq_ge {κ E : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    Real.sqrt κ ≤ ‖1 - matchedA E ^ 2‖ := by
  have hE2 := abs_le_of_mem_bulkInterval hE
  have hE1 : |E| ≤ 2 := by linarith
  have hk : κ ≤ 4 - E ^ 2 := by
    have h0 : 0 ≤ |E| := abs_nonneg E
    have h3 : E ^ 2 = |E| ^ 2 := (sq_abs E).symm
    nlinarith
  rw [← Real.sqrt_sq (norm_nonneg (1 - matchedA E ^ 2)), tgt_norm_one_sub_sq hE1]
  exact Real.sqrt_le_sqrt hk

theorem fetC_mem_Ioo {κ E : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    E ∈ Set.Ioo (-2 : ℝ) 2 := by
  have := abs_lt_two_of_mem_bulkInterval hκ hE
  exact ⟨by linarith [(abs_lt.mp this).1], (abs_lt.mp this).2⟩

/-- `‖a'‖ ≤ 1/√κ` on `bulkInterval κ`. -/
theorem fetC_norm_ad_le {κ E : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    ‖tgtAd E‖ ≤ 1 / Real.sqrt κ := by
  have hE1 : |E| ≤ 2 := (abs_lt_two_of_mem_bulkInterval hκ hE).le
  have hs := fetC_one_sub_sq_ge hκ hE
  have hs0 : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  unfold tgtAd
  rw [norm_div, norm_pow, norm_matchedA hE1, one_pow]
  exact one_div_le_one_div_of_le hs0 hs

/-- `a` is `1/√κ`-Lipschitz on `bulkInterval κ` (to the right). -/
theorem fetC_a_lip {κ E t : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) (ht : t ∈ bulkInterval κ)
    (hEt : E ≤ t) : ‖matchedA t - matchedA E‖ ≤ 1 / Real.sqrt κ * (t - E) := by
  have hseg : ∀ s ∈ Set.Icc E t, s ∈ bulkInterval κ := fun s hs =>
    ⟨by linarith [hE.1, hs.1], by linarith [ht.2, hs.2]⟩
  refine norm_image_sub_le_of_norm_deriv_le_segment' (f' := tgtAd) (fun s hs => ?_)
    (fun s hs => fetC_norm_ad_le hκ (hseg s (Set.Ico_subset_Icc_self hs))) t ⟨hEt, le_rfl⟩
  exact (tgt_hasDerivAt_matchedA (fetC_mem_Ioo hκ (hseg s hs))).hasDerivWithinAt

/-- The common algebra: `x/(1-x) - y/(1-y) = (x-y)/((1-x)(1-y))` type bound for `a²`. -/
theorem fetC_sq_diff_le {κ E t : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ)
    (ht : t ∈ bulkInterval κ) (hEt : E ≤ t) :
    ‖matchedA t ^ 2 - matchedA E ^ 2‖ ≤ 2 / Real.sqrt κ * (t - E) := by
  have hE1 : |E| ≤ 2 := (abs_lt_two_of_mem_bulkInterval hκ hE).le
  have ht1 : |t| ≤ 2 := (abs_lt_two_of_mem_bulkInterval hκ ht).le
  have e : matchedA t ^ 2 - matchedA E ^ 2 =
      (matchedA t - matchedA E) * (matchedA t + matchedA E) := by ring
  rw [e, norm_mul]
  have h2 : ‖matchedA t + matchedA E‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_matchedA ht1, norm_matchedA hE1]; norm_num
  have h1 := fetC_a_lip hκ hE ht hEt
  have hs0 : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hte : 0 ≤ t - E := by linarith
  calc ‖matchedA t - matchedA E‖ * ‖matchedA t + matchedA E‖
      ≤ (1 / Real.sqrt κ * (t - E)) * 2 :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = 2 / Real.sqrt κ * (t - E) := by ring

/-- `a'` is Lipschitz on `bulkInterval κ`. -/
theorem fetC_ad_lip {κ E t : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) (ht : t ∈ bulkInterval κ)
    (hEt : E ≤ t) : ‖tgtAd t - tgtAd E‖ ≤ 2 / (Real.sqrt κ) ^ 3 * (t - E) := by
  have hE2 : |E| < 2 := abs_lt_two_of_mem_bulkInterval hκ hE
  have ht2 : |t| < 2 := abs_lt_two_of_mem_bulkInterval hκ ht
  have h1 := tgt_one_sub_sq_ne_zero hE2
  have h2 := tgt_one_sub_sq_ne_zero ht2
  have e : tgtAd t - tgtAd E = (matchedA t ^ 2 - matchedA E ^ 2) /
      ((1 - matchedA t ^ 2) * (1 - matchedA E ^ 2)) := by
    unfold tgtAd; field_simp; ring
  rw [e, norm_div, norm_mul]
  have hs0 : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hlt := fetC_one_sub_sq_ge hκ ht
  have hlE := fetC_one_sub_sq_ge hκ hE
  have hd := fetC_sq_diff_le hκ hE ht hEt
  have hden : Real.sqrt κ * Real.sqrt κ ≤ ‖1 - matchedA t ^ 2‖ * ‖1 - matchedA E ^ 2‖ :=
    mul_le_mul hlt hlE hs0.le (norm_nonneg _)
  have hte : 0 ≤ t - E := by linarith
  rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hden)]
  calc ‖matchedA t ^ 2 - matchedA E ^ 2‖ ≤ 2 / Real.sqrt κ * (t - E) := hd
    _ = 2 / Real.sqrt κ ^ 3 * (t - E) * (Real.sqrt κ * Real.sqrt κ) := by
        field_simp
    _ ≤ 2 / Real.sqrt κ ^ 3 * (t - E) * (‖1 - matchedA t ^ 2‖ * ‖1 - matchedA E ^ 2‖) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

/-- `z_∂'` is Lipschitz on `bulkInterval κ` (`z_∂' = (b a² - 1)/(1 - a²)`). -/
theorem fetC_zd_lip {b κ E t : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) (ht : t ∈ bulkInterval κ) (hEt : E ≤ t) :
    ‖tgtZd b t - tgtZd b E‖ ≤ 2 / (Real.sqrt κ) ^ 3 * (t - E) := by
  have hE2 : |E| < 2 := abs_lt_two_of_mem_bulkInterval hκ hE
  have ht2 : |t| < 2 := abs_lt_two_of_mem_bulkInterval hκ ht
  have h1 := tgt_one_sub_sq_ne_zero hE2
  have h2 := tgt_one_sub_sq_ne_zero ht2
  have hE0 := tgt_matchedA_ne_zero hE2.le
  have ht0 := tgt_matchedA_ne_zero ht2.le
  have e : tgtZd b t - tgtZd b E = ((b : ℂ) - 1) * (tgtAd t - tgtAd E) := by
    unfold tgtZd tgtAd; field_simp; ring
  rw [e, norm_mul]
  have hb : ‖(b : ℂ) - 1‖ ≤ 1 := by
    rw [show (b : ℂ) - 1 = ((b - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hd := fetC_ad_lip hκ hE ht hEt
  have hte : 0 ≤ t - E := by linarith
  calc ‖(b : ℂ) - 1‖ * ‖tgtAd t - tgtAd E‖ ≤ 1 * (2 / Real.sqrt κ ^ 3 * (t - E)) :=
        mul_le_mul hb hd (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **Scalar second-order bounds** on the bulk: for `E ∈ bulkInterval κ` and `0 ≤ h ≤ κ/2`,
`|a(E+h) - a(E) - h a'(E)| ≤ L h²` and `|z_∂(E+h) - z_∂(E) - h z_∂'(E)| ≤ L h²`. -/
theorem fetC_scalar {b κ : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hκ : 0 < κ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ E ∈ bulkInterval κ, ∀ h : ℝ, 0 ≤ h → h ≤ κ / 2 →
      ‖matchedA (E + h) - matchedA E - (h : ℂ) * tgtAd E‖ ≤ L * h * h ∧
      ‖boundaryZ b (E + h) - boundaryZ b E - (h : ℂ) * tgtZd b E‖ ≤ L * h * h := by
  have hκ2 : 0 < κ / 2 := by positivity
  refine ⟨2 / Real.sqrt (κ / 2) ^ 3, by positivity, fun E hE h hh hhk => ⟨?_, ?_⟩⟩
  · refine fetC_taylor hh (by positivity) (fun t ht => tgt_hasDerivAt_matchedA (fetC_mem_Ioo hκ2
      (fetC_bulk_shift hE hh hhk ht))) (fun t ht => ?_)
    exact fetC_ad_lip hκ2 (fetC_bulk_mono hκ hE) (fetC_bulk_shift hE hh hhk ht) ht.1
  · refine fetC_taylor hh (by positivity) (fun t ht => tgt_hasDerivAt_boundaryZ b (fetC_mem_Ioo hκ2
      (fetC_bulk_shift hE hh hhk ht))) (fun t ht => ?_)
    exact fetC_zd_lip hb0 hb1 hκ2 (fetC_bulk_mono hκ hE) (fetC_bulk_shift hE hh hhk ht) ht.1

/-!
## 2. The augmented core matrix and the derivative identity
-/

section Deterministic

variable {W r : ℕ}

/-- The augmented core matrix `N(E) = [[H - E, B_p], [B_p*, z_∂(E)]]` of a path sample; its port
block inverse is `R_r` (`fetC_trace_eq`). -/
def fetCN (b E : ℝ) (ω : PathSample W r) :
    Matrix ((Fin r × Fin W) ⊕ (Fin 2 × Fin W)) ((Fin r × Fin W) ⊕ (Fin 2 × Fin W)) ℂ :=
  fromBlocks (pathMatrix ω - (E : ℂ) • 1) (pathPortCoupling ω) (pathPortCoupling ω)ᴴ
    (boundaryZ b E • 1)

/-- `M ↦ A M B` as a real continuous linear map. -/
def fetCSand {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix n m ℂ) (B : Matrix m n ℂ) : Matrix m m ℂ →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => A * M * B
      map_add' := fun M N => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c M => by simp }

/-- The block trace `M ↦ W⁻¹ Tr M_{ii}` of a two-port matrix, as a real continuous linear map. -/
def fetCB (W : ℕ) (i : Fin 2) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => blockTrace M i
      map_add' := fun M N => by
        simp only [blockTrace, Matrix.add_apply, Finset.sum_add_distrib, mul_add]
      map_smul' := fun c M => by
        simp only [blockTrace, Matrix.smul_apply, RingHom.id_apply, Complex.real_smul,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => by ring }

/-- The port block trace `M ↦ W⁻¹ Tr (M_{port})_{ii}`, as a real continuous linear map. -/
def fetCT {m : Type*} [Fintype m] [DecidableEq m] (W : ℕ) (i : Fin 2) :
    Matrix (m ⊕ (Fin 2 × Fin W)) (m ⊕ (Fin 2 × Fin W)) ℂ →L[ℝ] ℂ :=
  (fetCB W i).comp (LinearMap.toContinuousLinearMap
    { toFun := fun M => M.toBlocks₂₂
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl })

theorem fetCT_apply {m : Type*} [Fintype m] [DecidableEq m] (i : Fin 2)
    (M : Matrix (m ⊕ (Fin 2 × Fin W)) (m ⊕ (Fin 2 × Fin W)) ℂ) :
    fetCT W i M = blockTrace M.toBlocks₂₂ i := rfl

theorem fetCT_smul {m : Type*} [Fintype m] [DecidableEq m] (i : Fin 2) (c : ℂ)
    (M : Matrix (m ⊕ (Fin 2 × Fin W)) (m ⊕ (Fin 2 × Fin W)) ℂ) :
    fetCT W i (c • M) = c * fetCT W i M := by
  simp only [fetCT_apply, blockTrace, toBlocks₂₂, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => by ring

/-- `|W⁻¹ Tr (M_{port})_{ii}| ≤ ‖M‖`. -/
theorem fetCT_norm_le {m : Type*} [Fintype m] [DecidableEq m] (i : Fin 2)
    (M : Matrix (m ⊕ (Fin 2 × Fin W)) (m ⊕ (Fin 2 × Fin W)) ℂ) : ‖fetCT W i M‖ ≤ ‖M‖ := by
  rw [fetCT_apply, blockTrace, norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : ‖∑ a : Fin W, M.toBlocks₂₂ (i, a) (i, a)‖ ≤ W * ‖M‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a : Fin W, ‖M.toBlocks₂₂ (i, a) (i, a)‖ ≤ ∑ _a : Fin W, ‖M‖ :=
          Finset.sum_le_sum fun a _ => tfl_entry_le M _ _
      _ = W * ‖M‖ := by simp
  calc (W : ℝ)⁻¹ * ‖∑ a : Fin W, M.toBlocks₂₂ (i, a) (i, a)‖ ≤ (W : ℝ)⁻¹ * (W * ‖M‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ‖M‖ := by field_simp

/-- `E' ↦ E' I` has derivative `I`. -/
theorem fetC_hasDerivAt_smul_one {n : Type*} [Fintype n] [DecidableEq n] (E : ℝ) :
    HasDerivAt (fun E' : ℝ => ((E' : ℂ) • (1 : Matrix n n ℂ))) (1 : Matrix n n ℂ) E := by
  have := (hasDerivAt_id E).smul_const (1 : Matrix n n ℂ)
  simpa [Complex.coe_smul] using this

/-- **`X_r' = B_p*(H - E)⁻² B_p`** is the energy derivative of `X_r = pathSchur E ω`. -/
theorem fetC_hasDerivAt_pathSchur (E : ℝ) (ω : PathSample W r)
    (hU : IsUnit (pathMatrix ω - (E : ℂ) • 1).det) :
    HasDerivAt (fun E' : ℝ => pathSchur E' ω) (fetXd E ω) E := by
  have hD := (fetC_hasDerivAt_smul_one (n := Fin r × Fin W) E).const_sub (pathMatrix ω)
  have hinv := tgt_hasDerivAt_inv_comp hD hU
  have h3 := (fetCSand (pathPortCoupling ω)ᴴ (pathPortCoupling ω)).hasFDerivAt.comp_hasDerivAt E hinv
  have e : fetXd E ω = fetCSand (pathPortCoupling ω)ᴴ (pathPortCoupling ω)
      (-((pathMatrix ω - (E : ℂ) • 1)⁻¹ * -1 * (pathMatrix ω - (E : ℂ) • 1)⁻¹)) := by
    show _ = (pathPortCoupling ω)ᴴ * (-((pathMatrix ω - (E : ℂ) • 1)⁻¹ * -1 *
      (pathMatrix ω - (E : ℂ) • 1)⁻¹)) * pathPortCoupling ω
    simp only [fetXd, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, neg_neg, Matrix.mul_assoc]
  rw [e]
  exact h3

/-- **The path trace derivative is `fetFd`**: where `H - E` and `z_∂ - X_r` are invertible,
`E' ↦ W⁻¹ Tr(R_r(E'))_{ii}` has derivative `W⁻¹ Tr[R(X_r' - z_∂')R]_{ii}`. -/
theorem fetC_hasDerivAt_pathTrace (b : ℝ) {E : ℝ} (hE : E ∈ Set.Ioo (-2 : ℝ) 2)
    (ω : PathSample W r) (hU : IsUnit (pathMatrix ω - (E : ℂ) • 1).det)
    (hK : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      pathSchur E ω).det) (i : Fin 2) :
    HasDerivAt (fun E' : ℝ => blockTrace (pathPortResolvent b E' ω) i)
      (fetFd b E (pathSchur E ω) (fetXd E ω) i) E := by
  have hz := (tgt_hasDerivAt_boundaryZ b hE).smul_const
    (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
  have hKd := hz.sub (fetC_hasDerivAt_pathSchur E ω hU)
  have hinv := tgt_hasDerivAt_inv_comp hKd hK
  have h3 := (fetCB W i).hasFDerivAt.comp_hasDerivAt E hinv
  have e : fetFd b E (pathSchur E ω) (fetXd E ω) i = fetCB W i
      (-((boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - pathSchur E ω)⁻¹ *
        (tgtZd b E • 1 - fetXd E ω) *
        (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - pathSchur E ω)⁻¹)) := by
    show blockTrace _ i = blockTrace _ i
    congr 1
    rw [fetR, ← neg_sub (tgtZd b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) (fetXd E ω),
      Matrix.mul_neg, Matrix.neg_mul]
  rw [e]
  exact h3

/-- `E' ↦ N(E')` has derivative `N' = diag(-1, z_∂') = tgtD0 z_∂'`. -/
theorem fetC_hasDerivAt_N (b : ℝ) {E : ℝ} (hE : E ∈ Set.Ioo (-2 : ℝ) 2) (ω : PathSample W r) :
    HasDerivAt (fun E' : ℝ => fetCN b E' ω) (tgtD0 (tgtZd b E)) E := by
  have ha := (fetC_hasDerivAt_smul_one (n := Fin r × Fin W) E).const_sub (pathMatrix ω)
  have hb := (tgt_hasDerivAt_boundaryZ b hE).smul_const
    (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
  have h := ((tgtBlk (n := Fin r × Fin W) (m := Fin 2 × Fin W)).hasFDerivAt.comp_hasDerivAt E
    (ha.prodMk hb)).const_add (fromBlocks 0 (pathPortCoupling ω) (pathPortCoupling ω)ᴴ 0)
  have e1 : (fun E' : ℝ => fetCN b E' ω) = fun E' : ℝ =>
      fromBlocks 0 (pathPortCoupling ω) (pathPortCoupling ω)ᴴ 0 +
        (tgtBlk ∘ fun E' : ℝ => (pathMatrix ω - (E' : ℂ) • 1, boundaryZ b E' •
          (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))) E' := by
    funext E'
    simp only [Function.comp, tgtBlk_apply, fetCN, fromBlocks_add, zero_add, add_zero]
  have e2 : (tgtD0 (tgtZd b E) : Matrix ((Fin r × Fin W) ⊕ (Fin 2 × Fin W)) _ ℂ) =
      tgtBlk (-(1 : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ), tgtZd b E •
        (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) := by
    rw [tgtBlk_apply]; rfl
  rw [e1, e2]
  exact h

/-- **Schur identity**: where `H - E` is invertible, `R_r` is the port block of `N(E)⁻¹`. -/
theorem fetC_trace_eq (b E : ℝ) (ω : PathSample W r) (hU : IsUnit (pathMatrix ω - (E : ℂ) • 1).det)
    (i : Fin 2) :
    blockTrace (pathPortResolvent b E ω) i = fetCT W i (fetCN b E ω)⁻¹ := by
  rw [fetCT_apply, fetCN, pg_toBlocks22_inv _ _ _ _ hU]
  rfl

/-- `z_∂ - X_r` is invertible when `H - E` and `N(E)` are. -/
theorem fetC_K_isUnit (b E : ℝ) (ω : PathSample W r) (hU : IsUnit (pathMatrix ω - (E : ℂ) • 1).det)
    (hN : IsUnit (fetCN b E ω).det) :
    IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - pathSchur E ω).det := by
  let _ := invertibleOfIsUnitDet _ hU
  rw [fetCN, det_fromBlocks₁₁, invOf_eq_nonsing_inv] at hN
  exact (IsUnit.mul_iff.mp hN).2

/-- `H - E'` stays invertible near `E`. -/
theorem fetC_eventually_unit (E : ℝ) (ω : PathSample W r)
    (hU : IsUnit (pathMatrix ω - (E : ℂ) • 1).det) :
    ∀ᶠ E' : ℝ in 𝓝 E, IsUnit (pathMatrix ω - (E' : ℂ) • 1).det := by
  have hc : Continuous (fun E' : ℝ => (pathMatrix ω - (E' : ℂ) • 1).det) := by
    refine Continuous.matrix_det ?_
    exact continuous_const.sub (Complex.continuous_ofReal.smul continuous_const)
  have := hc.continuousAt.eventually_ne (isUnit_iff_ne_zero.mp hU)
  filter_upwards [this] with E' h
  exact isUnit_iff_ne_zero.mpr h

/-- **Derivative identity**: `f'_{r,i} = -W⁻¹ Tr[N⁻¹ N' N⁻¹]_{port, ii}`. -/
theorem fetC_fetFd_eq (b : ℝ) {E : ℝ} (hE : E ∈ Set.Ioo (-2 : ℝ) 2) (ω : PathSample W r)
    (hU : IsUnit (pathMatrix ω - (E : ℂ) • 1).det) (hN : IsUnit (fetCN b E ω).det) (i : Fin 2) :
    fetFd b E (pathSchur E ω) (fetXd E ω) i =
      fetCT W i (-((fetCN b E ω)⁻¹ * tgtD0 (tgtZd b E) * (fetCN b E ω)⁻¹)) := by
  have h1 := fetC_hasDerivAt_pathTrace b hE ω hU (fetC_K_isUnit b E ω hU hN) i
  have h2 := (fetCT W i).hasFDerivAt.comp_hasDerivAt E
    (tgt_hasDerivAt_inv_comp (fetC_hasDerivAt_N b hE ω) hN)
  have heq : (fun E' : ℝ => blockTrace (pathPortResolvent b E' ω) i) =ᶠ[𝓝 E]
      (fetCT W i ∘ fun E' : ℝ => (fetCN b E' ω)⁻¹) := by
    filter_upwards [fetC_eventually_unit E ω hU] with E' hE'
    exact fetC_trace_eq b E' ω hE' i
  exact h1.unique (h2.congr_of_eventuallyEq heq)

/-!
## 3. The second-order remainder
-/

/-- `N(E + h) = N(E) + diag(-h, z_∂(E+h) - z_∂(E))`. -/
theorem fetC_N_shift (b E h : ℝ) (ω : PathSample W r) :
    fetCN b (E + h) ω = fetCN b E ω + fromBlocks (-(h : ℂ) • (1 : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ)) 0 0
      ((boundaryZ b (E + h) - boundaryZ b E) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) := by
  rw [fetCN, fetCN, fromBlocks_add]
  congr 1
  · push_cast; rw [add_smul, neg_smul]; abel
  · rw [add_zero]
  · rw [add_zero]
  · rw [sub_smul]; abel

/-- `‖diag(0, w I)‖ ≤ |w|`. -/
theorem fetC_corner_norm_le {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (w : ℂ) : ‖(fromBlocks 0 0 0 (w • 1) : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖ ≤ ‖w‖ := by
  rw [tgt_fromBlocks22_eq]
  refine (dcv_norm_sandwich_le _ Sum.inr_injective Sum.inr_injective).trans ?_
  refine (norm_smul_le _ _).trans ?_
  have := dcv_norm_one_le (n := m)
  nlinarith [norm_nonneg w]

/-- **Second resolvent identity**: `N₁⁻¹ - N₀⁻¹ + h N₀⁻¹PN₀⁻¹ = -N₀⁻¹(Δ - hP)N₀⁻¹ + N₁⁻¹ΔN₀⁻¹ΔN₀⁻¹`
for `N₁ = N₀ + Δ`, both invertible, and its norm bound. -/
theorem fetC_inv_rem {ι : Type*} [Fintype ι] [DecidableEq ι] {N0 N1 Δ : Matrix ι ι ℂ}
    (hN : N1 = N0 + Δ) (h1 : IsUnit N1.det) (h0 : IsUnit N0.det) (P : Matrix ι ι ℂ) (h : ℂ) :
    ‖N1⁻¹ - N0⁻¹ + h • (N0⁻¹ * P * N0⁻¹)‖ ≤
      ‖N0⁻¹‖ ^ 2 * ‖Δ - h • P‖ + ‖N1⁻¹‖ * ‖N0⁻¹‖ ^ 2 * ‖Δ‖ ^ 2 := by
  have hs := tgt_inv_sub_of_add hN h1 h0
  have hA : N1⁻¹ = N0⁻¹ - N1⁻¹ * Δ * N0⁻¹ := by
    calc N1⁻¹ = (N1⁻¹ - N0⁻¹) + N0⁻¹ := by abel
      _ = -(N1⁻¹ * Δ * N0⁻¹) + N0⁻¹ := by rw [hs]
      _ = N0⁻¹ - N1⁻¹ * Δ * N0⁻¹ := by abel
  have h2 : N1⁻¹ * Δ * N0⁻¹ = N0⁻¹ * Δ * N0⁻¹ - N1⁻¹ * Δ * N0⁻¹ * Δ * N0⁻¹ := by
    conv_lhs => rw [hA]
    simp only [Matrix.sub_mul]
  have e : N1⁻¹ - N0⁻¹ + h • (N0⁻¹ * P * N0⁻¹) =
      -(N0⁻¹ * (Δ - h • P) * N0⁻¹) + N1⁻¹ * Δ * N0⁻¹ * Δ * N0⁻¹ := by
    rw [hs]
    nth_rewrite 1 [h2]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_neg]
    calc ‖N0⁻¹ * (Δ - h • P) * N0⁻¹‖ ≤ ‖N0⁻¹‖ * ‖Δ - h • P‖ * ‖N0⁻¹‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = _ := by ring
  · calc ‖N1⁻¹ * Δ * N0⁻¹ * Δ * N0⁻¹‖
        ≤ ‖N1⁻¹‖ * ‖Δ‖ * ‖N0⁻¹‖ * ‖Δ‖ * ‖N0⁻¹‖ := by
          refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
          refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
          refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
          exact norm_mul_le _ _
      _ = _ := by ring

/-- **Pointwise interpolation** (deterministic): on the regular set, for `0 < h ≤ min(κ/2, 1)`,
`max_i |f'_i - a'| ≤ h⁻¹ (d(E+h) + d(E)) + h ((K + L) + K (2‖N₀⁻¹‖³ + ‖N₁⁻¹‖³))`, where
`d = coreObs` is the value observable and `K = L + (1 + B_z + L)²`. -/
theorem fetC_pointwise {b κ L Bz : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L) {E h : ℝ}
    (hE : E ∈ bulkInterval κ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hsc : ‖matchedA (E + h) - matchedA E - (h : ℂ) * tgtAd E‖ ≤ L * h * h ∧
      ‖boundaryZ b (E + h) - boundaryZ b E - (h : ℂ) * tgtZd b E‖ ≤ L * h * h)
    (hzd : ‖tgtZd b E‖ ≤ Bz) (ω : PathSample W r)
    (hU0 : IsUnit (pathMatrix ω - (E : ℂ) • 1).det)
    (hU1 : IsUnit (pathMatrix ω - ((E + h : ℝ) : ℂ) • 1).det)
    (hN0 : IsUnit (fetCN b E ω).det) (hN1 : IsUnit (fetCN b (E + h) ω).det) :
    fetPathDist b E ω ≤ h⁻¹ * (coreObs b (E + h) ω + coreObs b E ω) +
      h * ((L + (1 + Bz + L) ^ 2 + L) + (L + (1 + Bz + L) ^ 2) *
        (2 * ‖(fetCN b E ω)⁻¹‖ ^ 3 + ‖(fetCN b (E + h) ω)⁻¹‖ ^ 3)) := by
  have hEI := fetC_mem_Ioo hκ hE
  set N0 := fetCN b E ω with hN0def
  set N1 := fetCN b (E + h) ω with hN1def
  set P : Matrix ((Fin r × Fin W) ⊕ (Fin 2 × Fin W)) ((Fin r × Fin W) ⊕ (Fin 2 × Fin W)) ℂ := tgtD0 (tgtZd b E) with hPdef
  set Δ : Matrix ((Fin r × Fin W) ⊕ (Fin 2 × Fin W)) ((Fin r × Fin W) ⊕ (Fin 2 × Fin W)) ℂ :=
    fromBlocks (-(h : ℂ) • (1 : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ)) 0 0
      ((boundaryZ b (E + h) - boundaryZ b E) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) with hΔdef
  have hshift : N1 = N0 + Δ := fetC_N_shift b E h ω
  set x := ‖N0⁻¹‖ with hx
  set y := ‖N1⁻¹‖ with hy
  have hx0 : 0 ≤ x := norm_nonneg _
  have hy0 : 0 ≤ y := norm_nonneg _
  -- the insertion bounds
  have hΔP : Δ - (h : ℂ) • P = fromBlocks 0 0 0
      ((boundaryZ b (E + h) - boundaryZ b E - (h : ℂ) * tgtZd b E) • 1) := by
    rw [hΔdef, hPdef, tgtD0, fromBlocks_smul, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
    congr 1
    · simp
    · simp
    · simp
    · simp only [smul_smul, sub_eq_add_neg, add_smul, neg_smul]
  have hΔPn : ‖Δ - (h : ℂ) • P‖ ≤ L * h * h := by
    rw [hΔP]; exact (fetC_corner_norm_le _).trans hsc.2
  have hPn : ‖(h : ℂ) • P‖ ≤ h * (1 + Bz) := by
    refine (norm_smul_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_of_nonneg hh.le]
    exact mul_le_mul_of_nonneg_left ((tgt_norm_tgtD0_le _).trans (by linarith)) hh.le
  have hΔn : ‖Δ‖ ≤ h * (1 + Bz + L) := by
    have e : Δ = (Δ - (h : ℂ) • P) + (h : ℂ) • P := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have : L * h * h ≤ L * h := by
      have := mul_le_mul_of_nonneg_left hh1 (mul_nonneg hL hh.le); linarith
    nlinarith
  have hrem := fetC_inv_rem hshift hN1 hN0 P (h : ℂ)
  -- the trace identity
  have hval : ∀ i : Fin 2,
      ‖fetFd b E (pathSchur E ω) (fetXd E ω) i - tgtAd E‖ ≤
        h⁻¹ * (coreObs b (E + h) ω + coreObs b E ω) +
          h * (L * x ^ 2 + (1 + Bz + L) ^ 2 * (y * x ^ 2) + L) := by
    intro i
    have hD := fetC_fetFd_eq b hEI ω hU0 hN0 i
    have hf1 := fetC_trace_eq b (E + h) ω hU1 i
    have hf0 := fetC_trace_eq b E ω hU0 i
    set D := fetFd b E (pathSchur E ω) (fetXd E ω) i
    have hTrem : fetCT W i (N1⁻¹ - N0⁻¹ + (h : ℂ) • (N0⁻¹ * P * N0⁻¹)) =
        blockTrace (pathPortResolvent b (E + h) ω) i - blockTrace (pathPortResolvent b E ω) i -
          (h : ℂ) * D := by
      rw [map_add, map_sub, fetCT_smul, hf1, hf0, hD, map_neg]; ring
    have hkey : (h : ℂ) * (D - tgtAd E) =
        (blockTrace (pathPortResolvent b (E + h) ω) i - matchedA (E + h)) -
          (blockTrace (pathPortResolvent b E ω) i - matchedA E) -
          fetCT W i (N1⁻¹ - N0⁻¹ + (h : ℂ) • (N0⁻¹ * P * N0⁻¹)) +
          (matchedA (E + h) - matchedA E - (h : ℂ) * tgtAd E) := by
      rw [hTrem]; ring
    have ho : ∀ (E' : ℝ), ‖blockTrace (pathPortResolvent b E' ω) i - matchedA E'‖ ≤ coreObs b E' ω := by
      intro E'
      unfold coreObs
      rcases rng_fin2_cases i with rfl | rfl
      · exact le_max_left _ _
      · exact le_max_right _ _
    have hT := fetCT_norm_le (W := W) i (N1⁻¹ - N0⁻¹ + (h : ℂ) • (N0⁻¹ * P * N0⁻¹))
    have hb1 : ‖(h : ℂ) * (D - tgtAd E)‖ ≤ coreObs b (E + h) ω + coreObs b E ω +
        (x ^ 2 * (L * h * h) + y * x ^ 2 * (h * (1 + Bz + L)) ^ 2) + L * h * h := by
      rw [hkey]
      refine (norm_add_le _ _).trans (add_le_add ?_ hsc.1)
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · exact (norm_sub_le _ _).trans (add_le_add (ho _) (ho _))
      · refine hT.trans (hrem.trans (add_le_add ?_ ?_))
        · exact mul_le_mul_of_nonneg_left hΔPn (by positivity)
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hΔn 2)
            (by positivity)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hh.le] at hb1
    have hh' : h * h⁻¹ = 1 := mul_inv_cancel₀ hh.ne'
    have e2 : h⁻¹ * (coreObs b (E + h) ω + coreObs b E ω) +
        h * (L * x ^ 2 + (1 + Bz + L) ^ 2 * (y * x ^ 2) + L) =
        h⁻¹ * (coreObs b (E + h) ω + coreObs b E ω +
          (x ^ 2 * (L * h * h) + y * x ^ 2 * (h * (1 + Bz + L)) ^ 2) + L * h * h) := by
      field_simp; ring
    rw [e2, le_inv_mul_iff₀ hh]
    exact hb1
  have hpoly : L * x ^ 2 + (1 + Bz + L) ^ 2 * (y * x ^ 2) + L ≤
      (L + (1 + Bz + L) ^ 2 + L) + (L + (1 + Bz + L) ^ 2) * (2 * x ^ 3 + y ^ 3) := by
    have hx2 : x ^ 2 ≤ 1 + x ^ 3 := by nlinarith [sq_nonneg (x - 1), sq_nonneg x]
    have hyx : y * x ^ 2 ≤ x ^ 3 + y ^ 3 := by
      nlinarith [mul_nonneg hx0 hy0, sq_nonneg (x - y), mul_nonneg (mul_nonneg hx0 hy0) hx0,
        mul_nonneg (sq_nonneg (x - y)) (add_nonneg hx0 hy0)]
    have hc : 0 ≤ (1 + Bz + L) ^ 2 := sq_nonneg _
    have h3x : 0 ≤ x ^ 3 := pow_nonneg hx0 3
    have h3y : 0 ≤ y ^ 3 := pow_nonneg hy0 3
    nlinarith [mul_le_mul_of_nonneg_left hx2 hL, mul_le_mul_of_nonneg_left hyx hc,
      mul_nonneg hL h3x, mul_nonneg hL h3y, mul_nonneg hc h3x]
  unfold fetPathDist fetDist
  have hfin : ∀ i : Fin 2, ‖fetFd b E (pathSchur E ω) (fetXd E ω) i - tgtAd E‖ ≤
      h⁻¹ * (coreObs b (E + h) ω + coreObs b E ω) +
        h * ((L + (1 + Bz + L) ^ 2 + L) + (L + (1 + Bz + L) ^ 2) * (2 * x ^ 3 + y ^ 3)) :=
    fun i => (hval i).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hpoly hh.le))
  exact max_le (hfin 0) (hfin 1)

end Deterministic

/-!
## 4. Laws: invertibility and moments of `N(E)⁻¹` under `pathLaw W r b`, `r ∈ {1, 2}`
-/

section Laws

variable {W r : ℕ}

theorem fetC_measurable_N (b E : ℝ) : Measurable (fun ω : PathSample W r => fetCN b E ω) := by
  have hA := (measurable_pathMatrix W r).sub
    (measurable_const (a := ((E : ℂ) • (1 : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ))))
  have hB := measurable_pathPortCoupling W r
  have hC := srec_measurable_conjTranspose hB
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  rcases x with x | x <;> rcases y with y | y
  · exact pg_entry hA x y
  · exact pg_entry hB x y
  · exact pg_entry hC x y
  · exact measurable_const

theorem fetC_measurable_normInv (b E : ℝ) :
    Measurable (fun ω : PathSample W r => ‖(fetCN b E ω)⁻¹‖) :=
  (measurable_matrix_inv.comp (fetC_measurable_N b E)).norm

theorem fetC_measurable_pathDist (b E : ℝ) :
    Measurable (fun ω : PathSample W r => fetPathDist b E ω) := by
  have hD : Measurable (fun ω : PathSample W r => (pathMatrix ω - (E : ℂ) • 1)⁻¹) :=
    measurable_matrix_inv.comp ((measurable_pathMatrix W r).sub measurable_const)
  have hB := measurable_pathPortCoupling W r
  have hXd : Measurable (fun ω : PathSample W r => fetXd E ω) :=
    srec_measurable_mul (srec_measurable_mul (srec_measurable_mul
      (srec_measurable_conjTranspose hB) hD) hD) hB
  have hR : Measurable (fun ω : PathSample W r => fetR b E (pathSchur E ω)) :=
    measurable_matrix_inv.comp (measurable_const.sub (measurable_pathSchur W r E))
  have hM : Measurable (fun ω : PathSample W r => fetR b E (pathSchur E ω) *
      (fetXd E ω - tgtZd b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) *
        fetR b E (pathSchur E ω)) :=
    srec_measurable_mul (srec_measurable_mul hR (hXd.sub measurable_const)) hR
  have hc : ∀ j : Fin 2, Continuous
      (fun M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => ‖blockTrace M j - tgtAd E‖) := by
    intro j
    unfold blockTrace
    fun_prop
  exact ((hc 0).measurable.comp hM).max ((hc 1).measurable.comp hM)

theorem fetC_N_one (b E : ℝ) (ℓ : LayerSample W .oneBlockTwoPorts) :
    fetCN b E (coreOne ℓ) = layerMatrix .oneBlockTwoPorts E (boundaryZ b E) 0 ℓ := by
  rw [fetCN, coreOne_pathMatrix, coreOne_portCoupling, layerMatrix, sub_zero]

theorem fetC_N_two (b E : ℝ) (q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate) :
    fetCN b E (coreTwo q) = layerMatrix .separate E (boundaryZ b E) (-coreOff q.1) q.2 := by
  rw [fetCN, coreTwo_pathMatrix, coreTwo_portCoupling, layerMatrix]
  congr 1; abel

/-- **Absorption for the cores**: from the layer bounds of the Gaussian absorption lemma (every shape,
every Hermitian `X`), `N(E)` is a.s. invertible under `pathLaw W r b`, `r ∈ {1,2}`, with the same
`L^q` bound on `‖N(E)⁻¹‖`. -/
theorem fetC_core_absorb (hr : r = 1 ∨ r = 2) {b E : ℝ} {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ∞)
    {C : ℝ}
    (hinv : ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian →
      ∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E (boundaryZ b E) X ω).det)
    (hmom : ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian →
      eLpNorm (fun ω => ‖layerResolvent σ E (boundaryZ b E) X ω‖) q (layerLaw W b σ) ≤
        ENNReal.ofReal C) :
    (∀ᵐ ω ∂pathLaw W r b, IsUnit (fetCN b E ω).det) ∧
      eLpNorm (fun ω => ‖(fetCN b E ω)⁻¹‖) q (pathLaw W r b) ≤ ENNReal.ofReal C := by
  have hset : MeasurableSet {ω : PathSample W r | IsUnit (fetCN b E ω).det} := by
    have hm : Measurable (fun ω : PathSample W r => (fetCN b E ω).det) :=
      (continuous_id.matrix_det).measurable.comp (fetC_measurable_N b E)
    have : {ω : PathSample W r | IsUnit (fetCN b E ω).det} =
        (fun ω => (fetCN b E ω).det) ⁻¹' {0}ᶜ := by
      ext ω; simp [isUnit_iff_ne_zero]
    rw [this]
    exact hm (measurableSet_singleton 0).compl
  rcases hr with rfl | rfl
  · have hmp := coreOne_measurePreserving W b
    refine ⟨?_, ?_⟩
    · rw [← hmp.map_eq, ae_map_iff hmp.measurable.aemeasurable hset]
      filter_upwards [hinv .oneBlockTwoPorts 0 isHermitian_zero] with ℓ hℓ
      rw [fetC_N_one]; exact hℓ
    · rw [← hmp.map_eq, eLpNorm_map_measure (fetC_measurable_normInv b E).aestronglyMeasurable
        hmp.measurable.aemeasurable]
      have e : ((fun ω : PathSample W 1 => ‖(fetCN b E ω)⁻¹‖) ∘ coreOne) =
          fun ℓ => ‖layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0 ℓ‖ := by
        funext ℓ; simp only [Function.comp, fetC_N_one, layerResolvent]
      rw [e]
      exact hmom .oneBlockTwoPorts 0 isHermitian_zero
  · have hmp := coreTwo_measurePreserving W b
    refine ⟨?_, ?_⟩
    · rw [← hmp.map_eq, ae_map_iff hmp.measurable.aemeasurable hset]
      filter_upwards [core_ae_unit2 (hinv .separate)] with q hq
      rw [fetC_N_two]; exact hq
    · rw [← hmp.map_eq, eLpNorm_map_measure (fetC_measurable_normInv b E).aestronglyMeasurable
        hmp.measurable.aemeasurable]
      have e : ((fun ω : PathSample W 2 => ‖(fetCN b E ω)⁻¹‖) ∘ coreTwo) =
          fun q => ‖coreG2 E (boundaryZ b E) q‖ := by
        funext q; simp only [Function.comp, fetC_N_two, coreG2, layerResolvent]
      rw [e]
      exact core_mom2 hq0 hqt (hmom .separate)

end Laws

/-!
## 5. `L^p` arithmetic
-/

section Lp

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Minkowski for a nonnegative combination: `‖a f + c g‖_p ≤ a A + c B`. -/
theorem fetC_eLpNorm_comb {p : ℝ} (hp : 1 ≤ p) {f g : Ω → ℝ} {a c A B : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hA0 : 0 ≤ A)
    (hB0 : 0 ≤ B) (hA : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal A)
    (hB : eLpNorm g (ENNReal.ofReal p) μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => a * f ω + c * g ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (a * A + c * B) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hsm : ∀ (k : ℝ) (u : Ω → ℝ), eLpNorm (fun ω => k * u ω) (ENNReal.ofReal p) μ =
      ‖k‖ₑ * eLpNorm u (ENNReal.ofReal p) μ := fun k u => by
    exact eLpNorm_const_smul k u (ENNReal.ofReal p) μ
  calc eLpNorm (fun ω => a * f ω + c * g ω) (ENNReal.ofReal p) μ
      ≤ eLpNorm (fun ω => a * f ω) (ENNReal.ofReal p) μ +
          eLpNorm (fun ω => c * g ω) (ENNReal.ofReal p) μ :=
        eLpNorm_add_le (f := fun ω => a * f ω) (g := fun ω => c * g ω) hp1
    _ ≤ ENNReal.ofReal a * ENNReal.ofReal A + ENNReal.ofReal c * ENNReal.ofReal B := by
        rw [hsm, hsm, Real.enorm_of_nonneg ha, Real.enorm_of_nonneg hc]
        gcongr
    _ = ENNReal.ofReal (a * A + c * B) := by
        rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hc,
          ← ENNReal.ofReal_add (mul_nonneg ha hA0) (mul_nonneg hc hB0)]

/-- `‖1‖_p ≤ 1` on a probability space. -/
theorem fetC_eLpNorm_one [IsProbabilityMeasure μ] (q : ℝ≥0∞) :
    eLpNorm (fun _ : Ω => (1 : ℝ)) q μ ≤ ENNReal.ofReal 1 := by
  have := eLpNorm_le_of_ae_bound (μ := μ) (p := q) (f := fun _ : Ω => (1 : ℝ)) (C := 1)
    aestronglyMeasurable_const (ae_of_all _ fun _ => by simp)
  simpa [measure_univ] using this

/-- `‖u³‖_p = ‖u‖_{3p}³ ≤ C³`. -/
theorem fetC_eLpNorm_cube {p : ℝ} (hp : 0 < p) {u : Ω → ℝ} (hu : AEStronglyMeasurable u μ)
    (hu0 : ∀ ω, 0 ≤ u ω) {C : ℝ} (hC : 0 ≤ C)
    (h : eLpNorm u (ENNReal.ofReal (3 * p)) μ ≤ ENNReal.ofReal C) :
    eLpNorm (fun ω => u ω ^ 3) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (C ^ 3) := by
  have e := eLpNorm_norm_rpow (μ := μ) (p := ENNReal.ofReal p) u hu (q := 3) (by norm_num)
  have e1 : (fun ω => ‖u ω‖ ^ (3 : ℝ)) = fun ω => u ω ^ 3 := by
    funext ω; rw [Real.norm_of_nonneg (hu0 ω)]; exact_mod_cast Real.rpow_natCast (u ω) 3
  rw [e1] at e
  rw [e, ← ENNReal.ofReal_mul hp.le, show p * 3 = 3 * p by ring]
  calc eLpNorm u (ENNReal.ofReal (3 * p)) μ ^ (3 : ℝ) ≤ ENNReal.ofReal C ^ (3 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal (C ^ 3) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hC (by norm_num)]
        norm_cast

end Lp

/-!
## 6. `FetCoreBound`
-/

/-- **The cores `r ∈ {1, 2}` of the energy paragraph of the tagged-trace lemma** (`FetCoreBound`;
in the paper, "The finite-core derivatives follow by differentiating their stable finite mean
equations"; used in the path clause `FetPathBound` of the full-energy trace bound).

*Law.* `pathLaw W r b` (independent `GUE_W(c/W)` blocks, `c = 1 - 2b`, `Gin(b/W)` internal and
port bonds), `r ∈ {1, 2}`. *Domain.* `b ∈ (0, 1/2)`, deterministic `E ∈ bulkInterval κ`,
`z = z_∂(E)`, `a = matchedA E`, `a' = tgtAd E`, `z_∂' = tgtZd b E`. *Object.* `fetPathDist b E ω =
max_i |f'_{r,i} - a'|`, `f'_{r,i} = W⁻¹ Tr[R_r (X_r' - z_∂') R_r]_{ii}`, `R_r = (z_∂ - X_r)⁻¹`,
`X_r' = B_p*(H - E)⁻²B_p`, the exact energy derivative of `W⁻¹ Tr(R_r)_{ii}` (`fetC_fetFd_eq`).
*Norm.* `L^p(pathLaw W r b)` of that real scalar. *Quantifiers and uniformity.* `b`, `κ` and the
moment order `p ≥ 1` first; then `C ≥ 0` and `W₀`; then uniformly in `W ≥ W₀`, both cores and
`E ∈ bulkInterval κ`: `‖max_i |f'_{r,i} - a'|‖_{L^p} ≤ C/√W`.

*Proof.* Interpolation between the values (the matched-traces theorem, `path`, at `E` and `E + h`,
`h = W^{-1/2}`, both in `bulkInterval (κ/2)`) and a second-order resolvent remainder controlled by
the moments of the Gaussian absorption lemma (`fetC_pointwise`, `fetC_core_absorb`). -/
theorem fetCoreBound_holds (hcount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : BlockBand.Internal.Contracts.Inputs.GaussianLpGradient) : FetCoreBound := by
  intro b hb0 hb1 κ hκ p hp
  have hκ2 : 0 < κ / 2 := by positivity
  obtain ⟨L, hL, hsc⟩ := fetC_scalar hb0.le (by linarith : b ≤ 1) hκ
  set Bz := (b + 1) / Real.sqrt (2 * κ) with hBz
  have hBz0 : 0 ≤ Bz := by positivity
  obtain ⟨η₀, hη₀, hbulk⟩ := dcv_bulk hb0 hb1 hκ2
  obtain ⟨ε₁, CA, hε₁, hCA, habs⟩ := gaussianAbsorption_holds hcount b hb0 hb1 η₀ 3 hη₀
  obtain ⟨ε₀, Cm, hε₀, hmt⟩ := (matchedTraces_holds hcount hgrad).path b hb0 hb1 (κ / 2) 2 hκ2
  set p' := max p 2 with hp'
  set Cm' := max Cm 0 with hCm'
  have hCm'0 : 0 ≤ Cm' := le_max_right _ _
  set K := L + (1 + Bz + L) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set Ctot := 2 * Cm' * Real.sqrt p' + ((K + L) + K * (2 * CA ^ 3 + 1 * CA ^ 3)) with hCtot
  refine ⟨Ctot, ⌈p' / ε₀⌉₊ + ⌈3 * p / ε₁⌉₊ + ⌈4 / κ ^ 2⌉₊ + 1, by positivity, ?_⟩
  intro W hW hWW r hr E hE
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (show 1 ≤ W by omega)
  have hW0 : (0 : ℝ) < W := by linarith
  have hWc : (⌈p' / ε₀⌉₊ + ⌈3 * p / ε₁⌉₊ + ⌈4 / κ ^ 2⌉₊ + 1 : ℝ) ≤ W := by exact_mod_cast hWW
  have hc1 := Nat.le_ceil (p' / ε₀)
  have hc2 := Nat.le_ceil (3 * p / ε₁)
  have hc3 := Nat.le_ceil (4 / κ ^ 2)
  have hc0 : (0 : ℝ) ≤ ⌈p' / ε₀⌉₊ := Nat.cast_nonneg _
  have hc0' : (0 : ℝ) ≤ ⌈3 * p / ε₁⌉₊ := Nat.cast_nonneg _
  have hc0'' : (0 : ℝ) ≤ ⌈4 / κ ^ 2⌉₊ := Nat.cast_nonneg _
  have hp'W : p' ≤ ε₀ * W := by
    have : p' / ε₀ ≤ W := by linarith
    rw [div_le_iff₀ hε₀] at this; linarith
  have h3pW : 3 * p ≤ ε₁ * W := by
    have : 3 * p / ε₁ ≤ W := by linarith
    rw [div_le_iff₀ hε₁] at this; linarith
  have hκW : 4 / κ ^ 2 ≤ W := by linarith
  -- the step `h = W^{-1/2}`
  set sW := Real.sqrt W with hsW
  have hsW0 : 0 < sW := Real.sqrt_pos.mpr hW0
  have hsWsq : sW * sW = W := Real.mul_self_sqrt hW0.le
  set h := sW⁻¹ with hh
  have hh0 : 0 < h := inv_pos.mpr hsW0
  have hsW1 : 1 ≤ sW := by rw [hsW, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hW1
  have hh1 : h ≤ 1 := inv_le_one_of_one_le₀ hsW1
  have hhk : h ≤ κ / 2 := by
    have h2 : 2 / κ ≤ sW := by
      rw [hsW, show 2 / κ = Real.sqrt ((2 / κ) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (by rw [div_pow]; norm_num; linarith)
    rw [hh, inv_le_comm₀ hsW0 hκ2]
    calc (κ / 2)⁻¹ = 2 / κ := by field_simp
      _ ≤ sW := h2
  have hE2 := fetC_bulk_mono hκ hE
  have hEh : E + h ∈ bulkInterval (κ / 2) :=
    fetC_bulk_shift hE hh0.le hhk ⟨by linarith, le_rfl⟩
  -- absorption at `E` and `E + h`
  have hq0 : ENNReal.ofReal (3 * p) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
  have habsE : ∀ E' ∈ bulkInterval (κ / 2),
      (∀ᵐ ω ∂pathLaw W r b, IsUnit (fetCN b E' ω).det) ∧
        eLpNorm (fun ω => ‖(fetCN b E' ω)⁻¹‖) (ENNReal.ofReal (3 * p)) (pathLaw W r b) ≤
          ENNReal.ofReal CA := by
    intro E' hE'
    refine fetC_core_absorb hr hq0 ENNReal.ofReal_ne_top (fun σ X hX => ?_) (fun σ X hX => ?_)
    · exact (habs W hW σ X hX E' _ (hbulk E' hE').1 (hbulk E' hE').2.1).1
    · exact (habs W hW σ X hX E' _ (hbulk E' hE').1 (hbulk E' hE').2.1).2 (3 * p) (by linarith)
        h3pW
  obtain ⟨hN0ae, hN0m⟩ := habsE E hE2
  obtain ⟨hN1ae, hN1m⟩ := habsE (E + h) hEh
  -- values at `E` and `E + h`
  have hr1 : 1 ≤ r := by rcases hr with rfl | rfl <;> norm_num
  have hr2 : (r : ℝ) ≤ 2 * W := by rcases hr with rfl | rfl <;> push_cast <;> linarith
  have hval : ∀ E' ∈ bulkInterval (κ / 2),
      eLpNorm (fun ω => coreObs b E' ω) (ENNReal.ofReal p) (pathLaw W r b) ≤
        ENNReal.ofReal (Cm' * Real.sqrt p' / W) := by
    intro E' hE'
    have h1 := hmt W hW p' (le_max_right _ _) hp'W r hr1 hr2 E' hE'
    refine (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (le_max_left p 2))).trans
      (h1.trans (ENNReal.ofReal_le_ofReal ?_))
    gcongr
    exact le_max_left _ _
  -- the pointwise bound
  have hpt : ∀ᵐ ω ∂pathLaw W r b, fetPathDist b E ω ≤
      h⁻¹ * (1 * coreObs b (E + h) ω + 1 * coreObs b E ω) +
        h * ((K + L) * 1 + K * (2 * ‖(fetCN b E ω)⁻¹‖ ^ 3 + 1 * ‖(fetCN b (E + h) ω)⁻¹‖ ^ 3)) := by
    filter_upwards [ae_isUnit_det_pathMatrix W r hb1 E, ae_isUnit_det_pathMatrix W r hb1 (E + h),
      hN0ae, hN1ae] with ω hU0 hU1 hN0 hN1
    have := fetC_pointwise (b := b) hκ hL hE hh0 hh1 (hsc E hE h hh0.le hhk)
      (tgt_norm_tgtZd_le hb0.le hκ hE) ω hU0 hU1 hN0 hN1
    simpa only [one_mul, mul_one, ← hK] using this
  -- the `L^p` bound of the majorant
  have hmaj : eLpNorm (fun ω => h⁻¹ * (1 * coreObs b (E + h) ω + 1 * coreObs b E ω) +
        h * ((K + L) * 1 + K * (2 * ‖(fetCN b E ω)⁻¹‖ ^ 3 + 1 * ‖(fetCN b (E + h) ω)⁻¹‖ ^ 3)))
      (ENNReal.ofReal p) (pathLaw W r b) ≤
      ENNReal.ofReal (h⁻¹ * (1 * (Cm' * Real.sqrt p' / W) + 1 * (Cm' * Real.sqrt p' / W)) +
        h * ((K + L) * 1 + K * (2 * CA ^ 3 + 1 * CA ^ 3))) := by
    have hp0 : 0 < p := by linarith
    have hO : 0 ≤ Cm' * Real.sqrt p' / W := by positivity
    have hx := fetC_eLpNorm_cube hp0 (fetC_measurable_normInv b E).aestronglyMeasurable
      (fun ω => norm_nonneg _) hCA.le hN0m
    have hy := fetC_eLpNorm_cube hp0 (fetC_measurable_normInv b (E + h)).aestronglyMeasurable
      (fun ω => norm_nonneg _) hCA.le hN1m
    have hY := fetC_eLpNorm_comb hp (by norm_num : (0 : ℝ) ≤ 2) zero_le_one (by positivity)
      (by positivity) hx hy
    have hV := fetC_eLpNorm_comb hp (by positivity : (0 : ℝ) ≤ K + L) hK0 zero_le_one
      (by positivity) (fetC_eLpNorm_one (μ := pathLaw W r b) _) hY
    have hU := fetC_eLpNorm_comb hp zero_le_one zero_le_one hO hO (hval (E + h) hEh) (hval E hE2)
    exact fetC_eLpNorm_comb hp (inv_nonneg.mpr hh0.le) hh0.le (by positivity) (by positivity) hU hV
  by_cases hfm : AEStronglyMeasurable (fun ω => fetPathDist b E ω) (pathLaw W r b)
  swap
  · exact absurd (fetC_measurable_pathDist b E).aestronglyMeasurable hfm
  refine (eLpNorm_mono_ae hfm ?_).trans (hmaj.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  · filter_upwards [hpt] with ω hω
    have h0 : 0 ≤ fetPathDist b E ω := (norm_nonneg _).trans (le_max_left _ _)
    rw [Real.norm_of_nonneg h0]
    exact hω.trans (le_abs_self _)
  · rw [hh, inv_inv, hCtot]
    field_simp
    rw [← hsWsq]
    ring

end BlockBand.Layers
