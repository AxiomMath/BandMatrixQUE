module

public import BlockBand.Diffusion.Base.TransitionLawDefs

/-!
# The product solution `u(s, z) = P_{t-s}(g ⊗ k)(z)` of the base backward equation

Lebesgue measure on `ℝ`, `ℝ × ℝ`; `D₀ > 0`; `g, k : ℝ → ℝ` continuous with `|g|, |k| ≤ M`.
* `skSemigroupY0 D0 k (h, y)` is `P_h k(y) = skSemigroupY D0 k h y` for `h > 0` and `k(y)` for
  `h ≤ 0` (the sphere analogue of `mkSemigroupX`);
  `sk_semigroupY0_continuousOn`: it is continuous on `[0, ∞) × [0, 1]` (approximate identity
  `sk_semigroupY_approx` at `h = 0`, `sk_semigroupY_continuousOn` for `h > 0`).
* `exProdSol D0 g k t (s, (x, y)) = mkSemigroupX D0 g (t - s, x) · skSemigroupY0 D0 k (t - s, y)`.
  - `exProd_tmInputs` (**uses `McKeanBackwardFacts D0`**): the factors
    `uX(τ, x) = mkSemigroupX D0 g (τ, x)`, `uY(τ, y) = skSemigroupY0 D0 k (τ, y)` satisfy every
    hypothesis of `TimeMollifyDuality` (`ExIsC02On1` on `(0, t) × (0, ∞)`, resp.
    `(0, t) × (0, 1)`, forward equations, continuity up to `τ = 0` and at `(t, z)`, bounds).
    The X factor equals `mkUX D0 g` for `τ > 0`. The sphere factor is replaced, on
    `(0,∞) × [0,1]`, by its smooth Legendre extension `skSer D0 (skLegFam (skCoef k))`
    (`sk_semigroupY_eq_ser`), whose partials are the series of the derived families
    (`sk_ser_hasDerivAt_t`, `sk_ser_hasDerivAt_y`) and which solves the sphere equation
    (`sk_legFam_pde`).
  - `exProdSol_continuousOn`: continuous on `[0, t] × exBaseStrip`; `abs_exProdSol_le`:
    `|u| ≤ M²` there; `exProdSol_terminal`: `u(t, z) = g(x) k(y)`;
    `exProdSol_eq_integral`: for `s < t`, `u(s, w) = ∫ exKernel D0 (t - s) w z' g(x') k(y') dz'`
    (every `w`, Fubini); `measurable_exProdSol`: `w ↦ u(s, w)` is measurable.
* `integrable_exKernel_mul`: `z' ↦ exKernel D0 h w z' F(z')` is integrable for `h > 0`,
  `w ∈ exBaseStrip` and bounded measurable `F`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

/-!
### Kernel bounds
-/

theorem abs_integral_mul_le_of_mass {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {q f : α → ℝ} (hq : Integrable q μ) (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∫ a, q a ∂μ = 1) {M : ℝ}
    (hM : ∀ a, |f a| ≤ M) : |∫ a, q a * f a ∂μ| ≤ M := by
  have h := norm_integral_le_of_norm_le (f := fun a => q a * f a) (hq.mul_const M)
    (ae_of_all _ fun a => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 a)]
      exact mul_le_mul_of_nonneg_left (hM a) (hq0 a))
  rwa [integral_mul_const, hq1, one_mul, Real.norm_eq_abs] at h

theorem mk_integrable_kernelX {D0 t x : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hx : 0 ≤ x) :
    Integrable (mkKernelX D0 t x) :=
  (mk_integrableOn_kernelX hD0 ht hx).integrable_of_forall_notMem_eq_zero fun x' hx' => by
    have : ¬ 0 ≤ x' := hx'
    simp [mkKernelX, this]

theorem abs_mkSemigroupX_le {D0 : ℝ} (hD0 : 0 < D0) {g : ℝ → ℝ} {M : ℝ}
    (hM : ∀ y, |g y| ≤ M) {p : ℝ × ℝ} (hp : 0 ≤ p.2) : |mkSemigroupX D0 g p| ≤ M := by
  unfold mkSemigroupX
  split_ifs with h
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x' hx' => by
      have : ¬ 0 ≤ x' := hx'
      simp [mkKernelX, this]]
    exact abs_integral_mul_le_of_mass (mk_integrable_kernelX hD0 h hp)
      (mk_kernelX_nonneg hD0 _ _) (mk_integral_kernelX_univ hD0 h hp) hM
  · exact hM _

/-!
### The sphere semigroup extended by `k` at `h ≤ 0`
-/

/-- `P_h k(y)` for `h > 0`, `k(y)` for `h ≤ 0`. -/
def skSemigroupY0 (D0 : ℝ) (k : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if 0 < p.1 then skSemigroupY D0 k p.1 p.2 else k p.2

theorem skSemigroupY0_of_pos {D0 : ℝ} {k : ℝ → ℝ} {p : ℝ × ℝ} (hp : 0 < p.1) :
    skSemigroupY0 D0 k p = skSemigroupY D0 k p.1 p.2 := by
  simp [skSemigroupY0, hp]

theorem abs_skSemigroupY0_le {D0 : ℝ} (hD0 : 0 < D0) {k : ℝ → ℝ} {M : ℝ}
    (hM : ∀ y, |k y| ≤ M) {p : ℝ × ℝ} (hp : p.2 ∈ Icc (0 : ℝ) 1) :
    |skSemigroupY0 D0 k p| ≤ M := by
  unfold skSemigroupY0
  split_ifs with h
  · exact abs_integral_mul_le_of_mass (sk_integrable_kernelY hD0 _ _)
      (sk_kernelY_nonneg hD0 _ _) (sk_integral_kernelY hD0 h hp) hM
  · exact hM _

/-- **Continuity of `(h, y) ↦ P_h k(y)` on `[0, ∞) × [0, 1]`**, with `P_0 k = k`. -/
theorem sk_semigroupY0_continuousOn {D0 : ℝ} (hD0 : 0 < D0) {k : ℝ → ℝ} (hk : Continuous k)
    {M : ℝ} (hM : ∀ y, |k y| ≤ M) :
    ContinuousOn (skSemigroupY0 D0 k) (Ici 0 ×ˢ Icc 0 1) := by
  have hkm : AEStronglyMeasurable k (volume.restrict (Icc (0 : ℝ) 1)) :=
    hk.aestronglyMeasurable
  have hkb : ∀ w ∈ Icc (0 : ℝ) 1, |k w| ≤ M := fun w _ => hM w
  rintro ⟨t₀, y₀⟩ ⟨ht₀, hy₀⟩
  have ht₀' : 0 ≤ t₀ := ht₀
  rcases ht₀'.eq_or_lt with h0 | hpos
  · subst h0
    rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ₁, hδ₁, H⟩ := sk_semigroupY_approx hD0 hk.continuousOn (half_pos hε)
    obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.continuousAt_iff.1 hk.continuousAt (ε / 2) (half_pos hε)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun p hp hpd => ?_⟩
    rw [Prod.dist_eq] at hpd
    have hd1 : dist p.1 0 < δ₁ :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hpd (min_le_left _ _))
    have hd2 : dist p.2 y₀ < δ₂ :=
      lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hpd (min_le_right _ _))
    have hk2 : dist (k p.2) (k y₀) < ε / 2 := hδ₂' hd2
    have h00 : skSemigroupY0 D0 k (0, y₀) = k y₀ := by simp [skSemigroupY0]
    rw [h00]
    by_cases hp1 : 0 < p.1
    · have hlt : p.1 < δ₁ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hp1] at hd1; exact hd1
      have hu := H p.1 hp1 hlt p.2 hp.2
      simp only [skSemigroupY0, hp1, ↓reduceIte]
      rw [Real.dist_eq] at hk2 ⊢
      calc |skSemigroupY D0 k p.1 p.2 - k y₀|
          ≤ |skSemigroupY D0 k p.1 p.2 - k p.2| + |k p.2 - k y₀| := abs_sub_le _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add hu hk2
        _ = ε := by ring
    · simp only [skSemigroupY0, hp1, ↓reduceIte]
      linarith
  · have hc := sk_semigroupY_continuousOn hD0 hkm hkb (t₀, y₀) ⟨hpos, hy₀⟩
    have hN : Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) ∈ 𝓝 (t₀, y₀) :=
      (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hpos, mem_univ _⟩
    rw [← continuousWithinAt_inter hN]
    have hset : Ici (0 : ℝ) ×ˢ Icc (0 : ℝ) 1 ∩ Ioi 0 ×ˢ univ = Ioi 0 ×ˢ Icc 0 1 := by
      ext q; simp only [mem_inter_iff, mem_prod, mem_Ici, mem_Ioi, mem_univ, and_true]
      constructor
      · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1.le, h2⟩, h1⟩
    rw [hset]
    refine hc.congr (fun q hq => ?_) ?_
    · simp [skSemigroupY0, show (0 : ℝ) < q.1 from hq.1]
    · simp [skSemigroupY0, hpos]

/-!
### The product solution
-/

/-- `u(s, (x, y)) = P_{t-s} g(x) · P_{t-s} k(y)`, with `P_0 = id`. -/
def exProdSol (D0 : ℝ) (g k : ℝ → ℝ) (t : ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  mkSemigroupX D0 g (t - p.1, p.2.1) * skSemigroupY0 D0 k (t - p.1, p.2.2)

theorem exProdSol_terminal (D0 : ℝ) (g k : ℝ → ℝ) (t : ℝ) (w : ℝ × ℝ) :
    exProdSol D0 g k t (t, w) = g w.1 * k w.2 := by
  simp [exProdSol, mkSemigroupX, skSemigroupY0]

theorem mem_openStrip_iff' {w : ℝ × ℝ} : w ∈ exOpenStrip ↔ 0 < w.1 ∧ w.2 ∈ Ioo (0 : ℝ) 1 :=
  Iff.rfl

/-- **The one-dimensional factors satisfy the hypotheses of `TimeMollifyDuality`** (given the
McKean facts): `uX(τ, x) = mkSemigroupX D0 g (τ, x)` and `uY(τ, y) = skSemigroupY0 D0 k (τ, y)`
are `C^{0,2}` on `(0, t) × (0, ∞)`, resp. `(0, t) × (0, 1)`, solve the forward X, Y equations
there, are continuous on `[0, t) × (0, ∞)`, resp. `[0, t) × (0, 1)`, continuous within these sets
at `(t, z₁)`, resp. `(t, z₂)`, for `z` in the closed strip, and bounded by `M`. The sphere
derivatives are those of the smooth Legendre extension `skSer D0 (skLegFam (skCoef k))`. -/
theorem exProd_tmInputs {D0 : ℝ} (hD0 : 0 < D0) (hX : McKeanBackwardFacts D0)
    {g k : ℝ → ℝ} (hg : Continuous g) (hk : Continuous k) {M : ℝ} (hgM : ∀ y, |g y| ≤ M)
    (hkM : ∀ y, |k y| ≤ M) {t : ℝ} (ht : 0 ≤ t) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip) :
    ∃ uXt uX1 uX2 uYt uY1 uY2 : ℝ → ℝ → ℝ,
      ExIsC02On1 (fun τ x => mkSemigroupX D0 g (τ, x)) uXt uX1 uX2 (Ioo 0 t) (Ioi 0) ∧
      ExIsC02On1 (fun τ y => skSemigroupY0 D0 k (τ, y)) uYt uY1 uY2 (Ioo 0 t) (Ioo 0 1) ∧
      (∀ τ ∈ Ioo 0 t, ∀ x ∈ Ioi (0 : ℝ),
        uXt τ x = D0 / 2 * (x * (1 + x) * uX2 τ x + (1 + 2 * x) * uX1 τ x)) ∧
      (∀ τ ∈ Ioo 0 t, ∀ y ∈ Ioo (0 : ℝ) 1,
        uYt τ y = D0 / 2 * (y * (1 - y) * uY2 τ y + (1 - 2 * y) * uY1 τ y)) ∧
      ContinuousOn (fun q : ℝ × ℝ => mkSemigroupX D0 g (q.1, q.2)) (Ico 0 t ×ˢ Ioi 0) ∧
      ContinuousOn (fun q : ℝ × ℝ => skSemigroupY0 D0 k (q.1, q.2)) (Ico 0 t ×ˢ Ioo 0 1) ∧
      ContinuousWithinAt (fun q : ℝ × ℝ => mkSemigroupX D0 g (q.1, q.2))
        (Ico 0 t ×ˢ Ioi 0) (t, z.1) ∧
      ContinuousWithinAt (fun q : ℝ × ℝ => skSemigroupY0 D0 k (q.1, q.2))
        (Ico 0 t ×ˢ Ioo 0 1) (t, z.2) ∧
      (∀ q ∈ Ico 0 t ×ˢ Ioi 0, |mkSemigroupX D0 g (q.1, q.2)| ≤ M) ∧
      (∀ q ∈ Ico 0 t ×ˢ Ioo 0 1, |skSemigroupY0 D0 k (q.1, q.2)| ≤ M) := by
  obtain ⟨u1, u2, ut, hd, c1, c2, cT⟩ := hX g hg.measurable M hgM
  have hkb : ∀ w ∈ Icc (0 : ℝ) 1, |k w| ≤ M := fun w _ => hkM w
  have hkm : AEStronglyMeasurable k (volume.restrict (Icc (0 : ℝ) 1)) :=
    hk.aestronglyMeasurable
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hkM 0)
  set Q : ℕ → Polynomial ℝ := skLegFam (skCoef k) with hQ
  have hG : SkGrowth Q := sk_growth_coef hkb
  have hG1 : SkGrowth (skDy Q) := sk_growth_dy hG
  have hG2 : SkGrowth (skDy (skDy Q)) := sk_growth_dy hG1
  have hGt : SkGrowth (skDt D0 Q) := sk_growth_dt hG D0
  have eqY : ∀ q : ℝ × ℝ, 0 < q.1 → q.2 ∈ Icc (0 : ℝ) 1 →
      skSemigroupY0 D0 k q = skSer D0 Q q.1 q.2 := fun q h1 h2 => by
    rw [skSemigroupY0_of_pos h1, sk_semigroupY_eq_ser hD0 hkm hkb h1 h2]
  have eqX : ∀ q : ℝ × ℝ, 0 < q.1 → mkSemigroupX D0 g q = mkUX D0 g q.1 q.2 := fun q h1 => by
    simp [mkSemigroupX, mkUX, h1]
  have cXall := mk_semigroupX_continuousOn hD0 hg hgM
  have cYall := sk_semigroupY0_continuousOn hD0 hk hkM
  have hsubX : Ico 0 t ×ˢ Ioi (0 : ℝ) ⊆ Ici 0 ×ˢ Ici 0 :=
    prod_mono Ico_subset_Ici_self Ioi_subset_Ici_self
  have hsubY : Ico 0 t ×ˢ Ioo (0 : ℝ) 1 ⊆ Ici 0 ×ˢ Icc 0 1 :=
    prod_mono Ico_subset_Ici_self Ioo_subset_Icc_self
  have hsubS : ∀ R : ℕ → Polynomial ℝ, SkGrowth R →
      ContinuousOn (fun q : ℝ × ℝ => skSer D0 R q.1 q.2) (Ioo 0 t ×ˢ Ioo 0 1) := fun R hR =>
    (sk_ser_contDiffOn hD0 hR).continuousOn.mono
      (prod_mono (fun τ hτ => hτ.1) (subset_univ _))
  have hIoo : Ioo 0 t ×ˢ Ioi (0 : ℝ) ⊆ Ioi 0 ×ˢ Ioi 0 := prod_mono (fun τ hτ => hτ.1) le_rfl
  refine ⟨ut, u1, u2, skSer D0 (skDt D0 Q), skSer D0 (skDy Q), skSer D0 (skDy (skDy Q)),
    ⟨fun τ hτ x hx => ?_, fun τ hτ x hx => ?_, fun τ hτ x hx => (hd τ x hτ.1 hx).2.1,
      (cXall.mono (hIoo.trans (prod_mono Ioi_subset_Ici_self Ioi_subset_Ici_self))),
      cT.mono hIoo, c1.mono hIoo, c2.mono hIoo⟩,
    ⟨fun τ hτ y hy => ?_, fun τ hτ y hy => ?_,
      fun τ hτ y hy => sk_ser_hasDerivAt_y hD0 hG1 hτ.1 y,
      cYall.mono (prod_mono (fun τ hτ => le_of_lt hτ.1) Ioo_subset_Icc_self),
      hsubS _ hGt, hsubS _ hG1, hsubS _ hG2⟩,
    fun τ hτ x hx => ?_, fun τ hτ y hy => ?_, cXall.mono hsubX, cYall.mono hsubY,
    (cXall (t, z.1) ⟨ht, hz.1⟩).mono hsubX, (cYall (t, z.2) ⟨ht, hz.2⟩).mono hsubY,
    fun q hq => abs_mkSemigroupX_le hD0 hgM (p := (q.1, q.2)) (le_of_lt hq.2),
    fun q hq => abs_skSemigroupY0_le hD0 hkM (p := (q.1, q.2)) (Ioo_subset_Icc_self hq.2)⟩
  · -- X, time
    refine (hd τ x hτ.1 hx).2.2.1.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hτ.1] with r hr
    exact eqX (r, x) hr
  · -- X, space
    exact (hd τ x hτ.1 hx).1.congr_of_eventuallyEq
      (Eventually.of_forall fun r => eqX (τ, r) hτ.1)
  · -- Y, time
    refine (sk_ser_hasDerivAt_t hD0 hG hτ.1 y).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hτ.1] with r hr
    exact eqY (r, y) hr (Ioo_subset_Icc_self hy)
  · -- Y, space
    refine (sk_ser_hasDerivAt_y hD0 hG hτ.1 y).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hy] with r hr
    exact eqY (τ, r) hτ.1 (Ioo_subset_Icc_self hr)
  · -- X equation
    obtain ⟨hd1, hd2, hdt, hpde⟩ := hd τ x hτ.1 hx
    have hdd : deriv (deriv fun z => mkUX D0 g τ z) x = u2 τ x := by
      have e : deriv (fun z => mkUX D0 g τ z) =ᶠ[𝓝 x] fun z => u1 τ z := by
        filter_upwards [lt_mem_nhds (show (0 : ℝ) < x from hx)] with w hw
        exact (hd τ w hτ.1 hw).1.deriv
      rw [e.deriv_eq]; exact hd2.deriv
    rw [← hdt.deriv, hpde, hdd, hd1.deriv]
  · -- Y equation
    exact sk_legFam_pde hD0 (A := 2 * M) (K := 16) (by positivity) (by norm_num)
      (sk_coef_le hkb) hτ.1 y

/-- **Continuity of the product solution** on `[0, t] × exBaseStrip`. -/
theorem exProdSol_continuousOn {D0 : ℝ} (hD0 : 0 < D0) {g k : ℝ → ℝ} (hg : Continuous g)
    (hk : Continuous k) {M : ℝ} (hgM : ∀ y, |g y| ≤ M) (hkM : ∀ y, |k y| ≤ M) (t : ℝ) :
    ContinuousOn (exProdSol D0 g k t) (Icc 0 t ×ˢ exBaseStrip) := by
  have h1 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => mkSemigroupX D0 g (t - p.1, p.2.1))
      (Icc 0 t ×ˢ exBaseStrip) :=
    (mk_semigroupX_continuousOn hD0 hg hgM).comp (by fun_prop) fun p hp =>
      ⟨show 0 ≤ t - p.1 by linarith [hp.1.2], hp.2.1⟩
  have h2 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => skSemigroupY0 D0 k (t - p.1, p.2.2))
      (Icc 0 t ×ˢ exBaseStrip) :=
    (sk_semigroupY0_continuousOn hD0 hk hkM).comp (by fun_prop) fun p hp =>
      ⟨show 0 ≤ t - p.1 by linarith [hp.1.2], hp.2.2⟩
  exact h1.mul h2

theorem abs_exProdSol_le {D0 : ℝ} (hD0 : 0 < D0) {g k : ℝ → ℝ} {M : ℝ}
    (hgM : ∀ y, |g y| ≤ M) (hkM : ∀ y, |k y| ≤ M) (t : ℝ) {p : ℝ × (ℝ × ℝ)}
    (hp : p.2 ∈ exBaseStrip) : |exProdSol D0 g k t p| ≤ M * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hgM 0)
  unfold exProdSol
  rw [abs_mul]
  exact mul_le_mul (abs_mkSemigroupX_le hD0 hgM (p := (t - p.1, p.2.1)) hp.1)
    (abs_skSemigroupY0_le hD0 hkM (p := (t - p.1, p.2.2)) hp.2) (abs_nonneg _) hM0

/-- For `s < t`, `u(s, w) = ∫ p_{t-s}(w, z') g(x') k(y') dz'` (every `w`; Fubini). -/
theorem exProdSol_eq_integral (D0 : ℝ) (g k : ℝ → ℝ) {s t : ℝ} (hst : s < t) (w : ℝ × ℝ) :
    exProdSol D0 g k t (s, w) = ∫ z', exKernel D0 (t - s) w z' * (g z'.1 * k z'.2) := by
  have hh : 0 < t - s := by linarith
  unfold exProdSol
  simp only
  rw [skSemigroupY0_of_pos hh]
  simp only [mkSemigroupX, hh, ↓reduceIte]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x' hx' => by
      have : ¬ 0 ≤ x' := hx'
      simp [mkKernelX, this]]
  unfold skSemigroupY
  rw [Measure.volume_eq_prod, ← integral_prod_mul]
  refine integral_congr_ae (ae_of_all _ fun z' => ?_)
  simp only [exKernel]
  ring

theorem measurable_exProdSol (D0 : ℝ) {g k : ℝ → ℝ} (hg : Measurable g) (hk : Measurable k)
    {s t : ℝ} (hst : s < t) (hD0 : 0 < D0) : Measurable fun w => exProdSol D0 g k t (s, w) := by
  have hh : 0 < t - s := by linarith
  have e : (fun w => exProdSol D0 g k t (s, w)) = fun w =>
      (∫ x', mkKernelX D0 (t - s) w.1 x' * g x') * ∫ y', skKernelY D0 (t - s) w.2 y' * k y' := by
    funext w
    unfold exProdSol
    simp only
    rw [skSemigroupY0_of_pos hh]
    simp only [mkSemigroupX, hh, ↓reduceIte]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x' hx' => by
        have : ¬ 0 ≤ x' := hx'
        simp [mkKernelX, this]]
    rfl
  rw [e]
  have hX : StronglyMeasurable fun q : ℝ × ℝ => mkKernelX D0 (t - s) q.1 q.2 * g q.2 :=
    (((mk_kernelX_measurable D0).comp (f := fun q : ℝ × ℝ => (t - s, q.1, q.2))
      (by fun_prop)).mul (hg.comp measurable_snd)).stronglyMeasurable
  have hY : StronglyMeasurable fun q : ℝ × ℝ => skKernelY D0 (t - s) q.1 q.2 * k q.2 :=
    (((sk_kernelY_measurable hD0).comp (f := fun q : ℝ × ℝ => (t - s, q.1, q.2))
      (by fun_prop)).mul (hk.comp measurable_snd)).stronglyMeasurable
  exact ((hX.integral_prod_right' (ν := volume)).measurable.comp measurable_fst).mul
    ((hY.integral_prod_right' (ν := volume)).measurable.comp measurable_snd)

/-- Integrability of the product kernel against bounded measurable functions. -/
theorem integrable_exKernel_mul {D0 h : ℝ} (hD0 : 0 < D0) (hh : 0 < h) {w : ℝ × ℝ}
    (hw : w ∈ exBaseStrip) {F : ℝ × ℝ → ℝ} (hF : AEStronglyMeasurable F volume) {C : ℝ}
    (hFC : ∀ z', |F z'| ≤ C) : Integrable (fun z' => exKernel D0 h w z' * F z') := by
  have hp : Integrable (fun z' : ℝ × ℝ => exKernel D0 h w z') := by
    rw [Measure.volume_eq_prod]
    exact (mk_integrable_kernelX hD0 hh hw.1).mul_prod (sk_integrable_kernelY hD0 h w.2)
  exact hp.mul_bdd hF (ae_of_all _ fun z' => by rw [Real.norm_eq_abs]; exact hFC z')

theorem exKernel_nonneg {D0 : ℝ} (hD0 : 0 < D0) (t : ℝ) (z z' : ℝ × ℝ) :
    0 ≤ exKernel D0 t z z' :=
  mul_nonneg (mk_kernelX_nonneg hD0 _ _ _) (sk_kernelY_nonneg hD0 _ _ _)

theorem exKernel_measurable {D0 : ℝ} (hD0 : 0 < D0) :
    Measurable fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => exKernel D0 w.1 w.2.1 w.2.2 := by
  have hX : Measurable fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => mkKernelX D0 w.1 w.2.1.1 w.2.2.1 :=
    (mk_kernelX_measurable D0).comp
      (f := fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => (w.1, w.2.1.1, w.2.2.1)) (by fun_prop)
  have hY : Measurable fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => skKernelY D0 w.1 w.2.1.2 w.2.2.2 :=
    (sk_kernelY_measurable hD0).comp
      (f := fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => (w.1, w.2.1.2, w.2.2.2)) (by fun_prop)
  exact hX.mul hY

end BlockBand.Diffusion
