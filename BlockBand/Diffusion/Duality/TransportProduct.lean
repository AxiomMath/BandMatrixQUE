module
public import BlockBand.Diffusion.Duality.Transport
public import BlockBand.Diffusion.Duality.MollifyDuality
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Product solutions and `C^{0,2}` duality for the base diffusion

Base diffusion `Z = (X, Y)` (`IsExBaseDiffusion P 𝓖 D0 z Z`, `0 < D0`, start `z` in the closed
strip), in `Fin 2` coordinates via `baseFin`, `finProd`; open strip `openStripFin`
(`exOpenStrip = (0, ∞) × (0, 1)` in strip coordinates).

* `IsExBaseDiffusion.duality_C02`, `IsExBaseDiffusion.condExp_duality_C02`: the base duality
  under `C^{0,2}` regularity (`IsC02On` on `(0, t) × openStripFin`, `spGen = 0`), by time mollification.
* `IsC02On1 w wt w1 w2 I J`: one-dimensional data on `I × J ⊆ ℝ × ℝ` (curried `w τ x`): `wt`,
  `w1`, `w2` are `∂_τ w`, `∂ₓ w`, `∂ₓ² w` (`HasDerivAt`), and `w, wt, w1, w2` are jointly
  continuous on `I × J`.
* **Product rule** (`isC02On_prodU`, `spGen_prodU`): if `uX(τ, x)` solves the forward X equation
  `∂_τ uX = (D₀/2)[x(1+x) ∂ₓ²uX + (1+2x) ∂ₓuX]` on `(0, t) × (0, ∞)` and `uY(τ, y)` the forward
  Y equation `∂_τ uY = (D₀/2)[y(1-y) ∂ᵧ²uY + (1-2y) ∂ᵧuY]` on `(0, t) × (0, 1)`, then
  `u(s, y) = uX(t - s, y₀) uY(t - s, y₁)` (time reversal `τ = t - s`) is `C^{0,2}` on
  `(0, t) × openStripFin` with explicit derivatives `prodUt`, `prodU1`, `prodU2` and solves the
  backward equation `spGen (baseDrift D0) (baseCov D0) = 0` there.
* **Main result** `IsExBaseDiffusion.duality_product`: if moreover `uX`, `uY` are continuous on
  `[0, t) × (0, ∞)`, resp. `[0, t) × (0, 1)`, continuous there within at `(t, z₁)`, resp.
  `(t, z₂)`, and bounded there, then `E[uX(0, X_t) uY(0, Y_t)] = uX(t, z₁) uY(t, z₂)`;
  `IsExBaseDiffusion.condExp_duality_product`: for `s < t`,
  `E[uX(0, X_t) uY(0, Y_t) | 𝓖_s] = uX(t - s, X_s) uY(t - s, Y_s)` a.s.

No joint regularity in `(τ, x)` of `uX` beyond `C^{0,2}` with a continuous `∂_τ` is used (the
time mollification `IsC02On.tconv` supplies the joint `C²` needed by `IsExBaseDiffusion.duality`).
-/

namespace BlockBand.Diffusion
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {z : ℝ × ℝ}
  {Z : ℝ≥0 → Ω → ℝ × ℝ}

/-!
### `C^{0,2}` duality for the base diffusion
-/

section BaseC02

variable (h : IsExBaseDiffusion P 𝓖 D0 z Z) (hD0 : 0 < D0) {t : ℝ≥0}
  {u ut : ℝ × (Fin 2 → ℝ) → ℝ} {u1 : ℝ × (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℝ}
  {u2 : ℝ × (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) →L[ℝ] ℝ}
  (hd : IsC02On u ut u1 u2 (Ioo 0 (t : ℝ) ×ˢ openStripFin))
  (hpde : ∀ p ∈ Ioo 0 (t : ℝ) ×ˢ openStripFin, spGen (baseDrift D0) (baseCov D0) ut u1 u2 p = 0)
  (hcont : ContinuousOn u (Ioc 0 (t : ℝ) ×ˢ openStripFin))
  (hu0 : ContinuousWithinAt u (Ioc 0 (t : ℝ) ×ˢ openStripFin) (0, finProd.symm z))
  {C : ℝ} (hC : ∀ p ∈ Ioc 0 (t : ℝ) ×ˢ openStripFin, |u p| ≤ C)
include h hD0 hd hpde hcont hu0 hC

/-- **Base duality under `C^{0,2}` regularity.** `E[u(t, Z_t)] = u(0, z)` (`Fin 2`
coordinates). -/
theorem IsExBaseDiffusion.duality_C02 (ht : 0 < t) :
    ∫ ω, u ((t : ℝ), baseFin Z t ω) ∂P = u (0, finProd.symm z) := by
  have := h.prob
  obtain ⟨hT, hz, hin⟩ := h.isTestMP_args hD0 t
  exact hT.duality_C02 isOpen_univ (continuous_baseDrift D0).continuousOn
    (continuous_baseCov D0).continuousOn (fun y _ i j => baseCov_symm D0 y i j)
    isOpen_openStripFin (subset_univ _) (mem_univ _) hz hin hd hpde hcont hu0 hC ht

/-- **Base conditional duality under `C^{0,2}` regularity.** For `s < t`,
`E[u(t, Z_t) | 𝓖_s] = u(s, Z_s)` a.s. (`Fin 2` coordinates). -/
theorem IsExBaseDiffusion.condExp_duality_C02 {s : ℝ≥0} (hst : s < t) :
    P[fun ω => u ((t : ℝ), baseFin Z t ω) | 𝓖 s] =ᵐ[P] fun ω => u ((s : ℝ), baseFin Z s ω) := by
  have := h.prob
  obtain ⟨hT, hz, hin⟩ := h.isTestMP_args hD0 t
  exact hT.condExp_duality_C02 isOpen_univ (continuous_baseDrift D0).continuousOn
    (continuous_baseCov D0).continuousOn (fun y _ i j => baseCov_symm D0 y i j)
    isOpen_openStripFin (subset_univ _) (mem_univ _) hz hin hd hpde hcont hu0 hC hst

end BaseC02

/-!
### One-dimensional data and the product rule
-/

/-- One-dimensional `C^{0,2}` data on `I × J` (curried `w τ x`). -/
structure IsC02On1 (w wt w1 w2 : ℝ → ℝ → ℝ) (I J : Set ℝ) : Prop where
  hasDerivAt_time : ∀ τ ∈ I, ∀ x ∈ J, HasDerivAt (fun τ => w τ x) (wt τ x) τ
  hasDerivAt_space : ∀ τ ∈ I, ∀ x ∈ J, HasDerivAt (w τ) (w1 τ x) x
  hasDerivAt_space2 : ∀ τ ∈ I, ∀ x ∈ J, HasDerivAt (w1 τ) (w2 τ x) x
  continuousOn : ContinuousOn (fun q : ℝ × ℝ => w q.1 q.2) (I ×ˢ J)
  continuousOn_time : ContinuousOn (fun q : ℝ × ℝ => wt q.1 q.2) (I ×ˢ J)
  continuousOn_space : ContinuousOn (fun q : ℝ × ℝ => w1 q.1 q.2) (I ×ˢ J)
  continuousOn_space2 : ContinuousOn (fun q : ℝ × ℝ => w2 q.1 q.2) (I ×ˢ J)

section Product

variable (t : ℝ) (uX uXt uX1 uX2 uY uYt uY1 uY2 : ℝ → ℝ → ℝ)

/-- Coordinate projection `y ↦ y i` on `ℝ²`. -/
abbrev pr2 (i : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i

/-- The product `u(s, y) = uX(t - s, y₀) uY(t - s, y₁)`. -/
def prodU (p : ℝ × (Fin 2 → ℝ)) : ℝ := uX (t - p.1) (p.2 0) * uY (t - p.1) (p.2 1)

/-- `∂ₛ` of the product (time reversal `τ = t - s`). -/
def prodUt (p : ℝ × (Fin 2 → ℝ)) : ℝ :=
  -(uXt (t - p.1) (p.2 0) * uY (t - p.1) (p.2 1) + uX (t - p.1) (p.2 0) * uYt (t - p.1) (p.2 1))

/-- Spatial derivative of the product. -/
def prodU1 (p : ℝ × (Fin 2 → ℝ)) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  (uX1 (t - p.1) (p.2 0) * uY (t - p.1) (p.2 1)) • pr2 0 +
    (uX (t - p.1) (p.2 0) * uY1 (t - p.1) (p.2 1)) • pr2 1

/-- Second spatial derivative of the product. -/
def prodU2 (p : ℝ × (Fin 2 → ℝ)) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) →L[ℝ] ℝ :=
  (pr2 0).smulRight ((uX2 (t - p.1) (p.2 0) * uY (t - p.1) (p.2 1)) • pr2 0 +
      (uX1 (t - p.1) (p.2 0) * uY1 (t - p.1) (p.2 1)) • pr2 1) +
    (pr2 1).smulRight ((uX1 (t - p.1) (p.2 0) * uY1 (t - p.1) (p.2 1)) • pr2 0 +
      (uX (t - p.1) (p.2 0) * uY2 (t - p.1) (p.2 1)) • pr2 1)

variable {t uX uXt uX1 uX2 uY uYt uY1 uY2}

theorem mem_of_mem_strip {p : ℝ × (Fin 2 → ℝ)} (hp : p ∈ Ioo 0 t ×ˢ openStripFin) :
    t - p.1 ∈ Ioo 0 t ∧ p.2 0 ∈ Ioi 0 ∧ p.2 1 ∈ Ioo 0 1 :=
  ⟨⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩, hp.2.1, hp.2.2.1, hp.2.2.2⟩

theorem continuousOn_comp_rev {w : ℝ → ℝ → ℝ} {I J : Set ℝ} {S : Set (ℝ × (Fin 2 → ℝ))}
    (hw : ContinuousOn (fun q : ℝ × ℝ => w q.1 q.2) (I ×ˢ J)) (i : Fin 2)
    (hS : ∀ p ∈ S, t - p.1 ∈ I ∧ p.2 i ∈ J) :
    ContinuousOn (fun p : ℝ × (Fin 2 → ℝ) => w (t - p.1) (p.2 i)) S :=
  hw.comp (f := fun p : ℝ × (Fin 2 → ℝ) => (t - p.1, p.2 i)) (by fun_prop) fun p hp => hS p hp

/-- **Product rule, regularity**: the time-reversed product is `C^{0,2}` on
`(0, t) × openStripFin` with derivatives `prodUt`, `prodU1`, `prodU2`. -/
theorem isC02On_prodU (hX : IsC02On1 uX uXt uX1 uX2 (Ioo 0 t) (Ioi 0))
    (hY : IsC02On1 uY uYt uY1 uY2 (Ioo 0 t) (Ioo 0 1)) :
    IsC02On (prodU t uX uY) (prodUt t uX uXt uY uYt) (prodU1 t uX uX1 uY uY1)
      (prodU2 t uX uX1 uX2 uY uY1 uY2) (Ioo 0 t ×ˢ openStripFin) := by
  have hSX : ∀ p ∈ Ioo 0 t ×ˢ openStripFin, t - p.1 ∈ Ioo 0 t ∧ p.2 0 ∈ Ioi 0 :=
    fun p hp => ⟨(mem_of_mem_strip hp).1, (mem_of_mem_strip hp).2.1⟩
  have hSY : ∀ p ∈ Ioo 0 t ×ˢ openStripFin, t - p.1 ∈ Ioo 0 t ∧ p.2 1 ∈ Ioo 0 1 :=
    fun p hp => ⟨(mem_of_mem_strip hp).1, (mem_of_mem_strip hp).2.2⟩
  have cX := continuousOn_comp_rev hX.continuousOn 0 hSX
  have cXt := continuousOn_comp_rev hX.continuousOn_time 0 hSX
  have cX1 := continuousOn_comp_rev hX.continuousOn_space 0 hSX
  have cX2 := continuousOn_comp_rev hX.continuousOn_space2 0 hSX
  have cY := continuousOn_comp_rev hY.continuousOn 1 hSY
  have cYt := continuousOn_comp_rev hY.continuousOn_time 1 hSY
  have cY1 := continuousOn_comp_rev hY.continuousOn_space 1 hSY
  have cY2 := continuousOn_comp_rev hY.continuousOn_space2 1 hSY
  have hpr : ∀ (i : Fin 2) (y : Fin 2 → ℝ), HasFDerivAt (fun y : Fin 2 → ℝ => y i) (pr2 i) y :=
    fun i y => hasFDerivAt_apply i y
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, cX.mul cY, ((cXt.mul cY).add
    (cX.mul cYt)).neg, ((cX1.mul cY).smul continuousOn_const).add
    ((cX.mul cY1).smul continuousOn_const), ?_⟩
  · obtain ⟨hτ, hx, hy⟩ := mem_of_mem_strip hp
    have hr : HasDerivAt (fun σ : ℝ => t - σ) (-1) p.1 := (hasDerivAt_id p.1).const_sub t
    have h1 := (hX.hasDerivAt_time _ hτ _ hx).comp p.1 hr
    have h2 := (hY.hasDerivAt_time _ hτ _ hy).comp p.1 hr
    refine (h1.mul h2).congr_deriv ?_
    simp only [prodUt, Function.comp]; ring
  · obtain ⟨hτ, hx, hy⟩ := mem_of_mem_strip hp
    have h1 := (hX.hasDerivAt_space _ hτ _ hx).comp_hasFDerivAt p.2 (hpr 0 p.2)
    have h2 := (hY.hasDerivAt_space _ hτ _ hy).comp_hasFDerivAt p.2 (hpr 1 p.2)
    refine (h1.mul h2).congr_fderiv ?_
    ext k
    simp [prodU1]
    ring
  · obtain ⟨hτ, hx, hy⟩ := mem_of_mem_strip hp
    have hX1 := (hX.hasDerivAt_space _ hτ _ hx).comp_hasFDerivAt p.2 (hpr 0 p.2)
    have hX2 := (hX.hasDerivAt_space2 _ hτ _ hx).comp_hasFDerivAt p.2 (hpr 0 p.2)
    have hY1 := (hY.hasDerivAt_space _ hτ _ hy).comp_hasFDerivAt p.2 (hpr 1 p.2)
    have hY2 := (hY.hasDerivAt_space2 _ hτ _ hy).comp_hasFDerivAt p.2 (hpr 1 p.2)
    have hA := (hX2.mul hY1).smul_const (pr2 0)
    have hB := (hX1.mul hY2).smul_const (pr2 1)
    refine (hA.add hB).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun k => ContinuousLinearMap.ext fun l => ?_
    simp [prodU2]
    ring
  · have hin : ContinuousOn (fun p : ℝ × (Fin 2 → ℝ) =>
        (uX2 (t - p.1) (p.2 0) * uY (t - p.1) (p.2 1)) • pr2 0 +
          (uX1 (t - p.1) (p.2 0) * uY1 (t - p.1) (p.2 1)) • pr2 1) (Ioo 0 t ×ˢ openStripFin) :=
      ((cX2.mul cY).smul continuousOn_const).add ((cX1.mul cY1).smul continuousOn_const)
    have hin' : ContinuousOn (fun p : ℝ × (Fin 2 → ℝ) =>
        (uX1 (t - p.1) (p.2 0) * uY1 (t - p.1) (p.2 1)) • pr2 0 +
          (uX (t - p.1) (p.2 0) * uY2 (t - p.1) (p.2 1)) • pr2 1) (Ioo 0 t ×ˢ openStripFin) :=
      ((cX1.mul cY1).smul continuousOn_const).add ((cX.mul cY2).smul continuousOn_const)
    exact ((ContinuousLinearMap.smulRightL ℝ (Fin 2 → ℝ) ((Fin 2 → ℝ) →L[ℝ] ℝ)
      (pr2 0)).continuous.comp_continuousOn hin).add
      ((ContinuousLinearMap.smulRightL ℝ (Fin 2 → ℝ) ((Fin 2 → ℝ) →L[ℝ] ℝ)
      (pr2 1)).continuous.comp_continuousOn hin')

/-- **Product rule, equation.** Forward X and Y equations give the backward 2-d equation for
the time-reversed product. -/
theorem spGen_prodU
    (hXpde : ∀ τ ∈ Ioo 0 t, ∀ x ∈ Ioi (0 : ℝ),
      uXt τ x = D0 / 2 * (x * (1 + x) * uX2 τ x + (1 + 2 * x) * uX1 τ x))
    (hYpde : ∀ τ ∈ Ioo 0 t, ∀ y ∈ Ioo (0 : ℝ) 1,
      uYt τ y = D0 / 2 * (y * (1 - y) * uY2 τ y + (1 - 2 * y) * uY1 τ y))
    {p : ℝ × (Fin 2 → ℝ)} (hp : p ∈ Ioo 0 t ×ˢ openStripFin) :
    spGen (baseDrift D0) (baseCov D0) (prodUt t uX uXt uY uYt) (prodU1 t uX uX1 uY uY1)
      (prodU2 t uX uX1 uX2 uY uY1 uY2) p = 0 := by
  obtain ⟨hτ, hx, hy⟩ := mem_of_mem_strip hp
  have e1 := hXpde _ hτ _ hx
  have e2 := hYpde _ hτ _ hy
  simp only [spGen, prodUt, prodU1, prodU2, Fin.sum_univ_two]
  simp [baseDrift, baseCov, e1, e2]
  ring

end Product

/-!
### Duality for products
-/

section ProductDuality

variable {uX uXt uX1 uX2 uY uYt uY1 uY2 : ℝ → ℝ → ℝ}
  (h : IsExBaseDiffusion P 𝓖 D0 z Z) (hD0 : 0 < D0) {t : ℝ≥0}
  (hX : IsC02On1 uX uXt uX1 uX2 (Ioo 0 (t : ℝ)) (Ioi 0))
  (hY : IsC02On1 uY uYt uY1 uY2 (Ioo 0 (t : ℝ)) (Ioo 0 1))
  (hXpde : ∀ τ ∈ Ioo 0 (t : ℝ), ∀ x ∈ Ioi (0 : ℝ),
    uXt τ x = D0 / 2 * (x * (1 + x) * uX2 τ x + (1 + 2 * x) * uX1 τ x))
  (hYpde : ∀ τ ∈ Ioo 0 (t : ℝ), ∀ y ∈ Ioo (0 : ℝ) 1,
    uYt τ y = D0 / 2 * (y * (1 - y) * uY2 τ y + (1 - 2 * y) * uY1 τ y))
  (hXc : ContinuousOn (fun q : ℝ × ℝ => uX q.1 q.2) (Ico 0 (t : ℝ) ×ˢ Ioi 0))
  (hYc : ContinuousOn (fun q : ℝ × ℝ => uY q.1 q.2) (Ico 0 (t : ℝ) ×ˢ Ioo 0 1))
  (hX0 : ContinuousWithinAt (fun q : ℝ × ℝ => uX q.1 q.2) (Ico 0 (t : ℝ) ×ˢ Ioi 0) (t, z.1))
  (hY0 : ContinuousWithinAt (fun q : ℝ × ℝ => uY q.1 q.2) (Ico 0 (t : ℝ) ×ˢ Ioo 0 1) (t, z.2))
  {CX CY : ℝ} (hCX : ∀ q ∈ Ico 0 (t : ℝ) ×ˢ Ioi 0, |uX q.1 q.2| ≤ CX)
  (hCY : ∀ q ∈ Ico 0 (t : ℝ) ×ˢ Ioo 0 1, |uY q.1 q.2| ≤ CY)

section Hyp

include hXc hYc

theorem continuousOn_prodU :
    ContinuousOn (prodU t uX uY) (Ioc 0 (t : ℝ) ×ˢ openStripFin) := by
  have hS : ∀ p ∈ Ioc 0 (t : ℝ) ×ˢ openStripFin,
      t - p.1 ∈ Ico 0 (t : ℝ) ∧ p.2 0 ∈ Ioi 0 ∧ p.2 1 ∈ Ioo 0 1 := fun p hp =>
    ⟨⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩, hp.2.1, hp.2.2.1, hp.2.2.2⟩
  exact (continuousOn_comp_rev hXc 0 fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩).mul
    (continuousOn_comp_rev hYc 1 fun p hp => ⟨(hS p hp).1, (hS p hp).2.2⟩)

end Hyp

theorem continuousWithinAt_prodU (hX0 : ContinuousWithinAt (fun q : ℝ × ℝ => uX q.1 q.2)
      (Ico 0 (t : ℝ) ×ˢ Ioi 0) (t, z.1))
    (hY0 : ContinuousWithinAt (fun q : ℝ × ℝ => uY q.1 q.2) (Ico 0 (t : ℝ) ×ˢ Ioo 0 1)
      (t, z.2)) :
    ContinuousWithinAt (prodU t uX uY) (Ioc 0 (t : ℝ) ×ˢ openStripFin) (0, finProd.symm z) := by
  have hS : ∀ p ∈ Ioc 0 (t : ℝ) ×ˢ openStripFin,
      t - p.1 ∈ Ico 0 (t : ℝ) ∧ p.2 0 ∈ Ioi 0 ∧ p.2 1 ∈ Ioo 0 1 := fun p hp =>
    ⟨⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩, hp.2.1, hp.2.2.1, hp.2.2.2⟩
  have h1 : ContinuousWithinAt (fun p : ℝ × (Fin 2 → ℝ) => uX (t - p.1) (p.2 0))
      (Ioc 0 (t : ℝ) ×ˢ openStripFin) (0, finProd.symm z) :=
    hX0.comp_of_eq (f := fun p : ℝ × (Fin 2 → ℝ) => ((t : ℝ) - p.1, p.2 0))
      (by fun_prop) (fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩) (by simp)
  have h2 : ContinuousWithinAt (fun p : ℝ × (Fin 2 → ℝ) => uY (t - p.1) (p.2 1))
      (Ioc 0 (t : ℝ) ×ˢ openStripFin) (0, finProd.symm z) :=
    hY0.comp_of_eq (f := fun p : ℝ × (Fin 2 → ℝ) => ((t : ℝ) - p.1, p.2 1))
      (by fun_prop) (fun p hp => ⟨(hS p hp).1, (hS p hp).2.2⟩) (by simp)
  exact h1.mul h2

theorem abs_prodU_le (hCX : ∀ q ∈ Ico 0 (t : ℝ) ×ˢ Ioi 0, |uX q.1 q.2| ≤ CX)
    (hCY : ∀ q ∈ Ico 0 (t : ℝ) ×ˢ Ioo 0 1, |uY q.1 q.2| ≤ CY) :
    ∀ p ∈ Ioc 0 (t : ℝ) ×ˢ openStripFin, |prodU t uX uY p| ≤ CX * CY := by
  intro p hp
  have hτ : t - p.1 ∈ Ico 0 (t : ℝ) := ⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩
  have h1 := hCX (t - p.1, p.2 0) ⟨hτ, hp.2.1⟩
  have h2 := hCY (t - p.1, p.2 1) ⟨hτ, hp.2.2.1, hp.2.2.2⟩
  rw [prodU, abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

include h hD0 hX hY hXpde hYpde hXc hYc hX0 hY0 hCX hCY

/-- **Duality for products of one-dimensional solutions.**
`E[uX(0, X_t) uY(0, Y_t)] = uX(t, z₁) uY(t, z₂)`. -/
theorem IsExBaseDiffusion.duality_product (ht : 0 < t) :
    ∫ ω, uX 0 (Z t ω).1 * uY 0 (Z t ω).2 ∂P = uX t z.1 * uY t z.2 := by
  have H := h.duality_C02 hD0 (isC02On_prodU hX hY) (fun p hp => spGen_prodU hXpde hYpde hp)
    (continuousOn_prodU hXc hYc) (continuousWithinAt_prodU hX0 hY0) (abs_prodU_le hCX hCY) ht
  simpa [prodU] using H

/-- **Conditional duality for products.** For `s < t`,
`E[uX(0, X_t) uY(0, Y_t) | 𝓖_s] = uX(t - s, X_s) uY(t - s, Y_s)` a.s. -/
theorem IsExBaseDiffusion.condExp_duality_product {s : ℝ≥0} (hst : s < t) :
    P[fun ω => uX 0 (Z t ω).1 * uY 0 (Z t ω).2 | 𝓖 s] =ᵐ[P]
      fun ω => uX (t - s) (Z s ω).1 * uY (t - s) (Z s ω).2 := by
  have H := h.condExp_duality_C02 hD0 (isC02On_prodU hX hY)
    (fun p hp => spGen_prodU hXpde hYpde hp) (continuousOn_prodU hXc hYc)
    (continuousWithinAt_prodU hX0 hY0) (abs_prodU_le hCX hCY) hst
  simpa [prodU] using H

end ProductDuality

end BlockBand.Diffusion
