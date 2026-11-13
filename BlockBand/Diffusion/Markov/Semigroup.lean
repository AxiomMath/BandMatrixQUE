module

public import BlockBand.Diffusion.Markov.Fdd

/-!
# Transition semigroups given by densities: Chapman–Kolmogorov and consistency

* each `p t` is jointly measurable;
* from `a ∈ S` the time-`t` law (`t > 0`) charges only `S`: `p t a y ≠ 0 → y ∈ S` for μ-a.e. `y`;
* `∫⁻ p_s(a, y) p_t(y, b) dμ(y) = p_{s+t}(a, b)` for `s, t > 0`, `a ∈ S`, every `b`.

It is **sub-Markov / Markov on `S`** if `∫⁻ p_t(a, ·) dμ ≤ 1` (resp. `= 1`) for `t > 0`, `a ∈ S`.
The associated kernels are `transitionKernel μ p t = μ.withDensity (p t a)` (Mathlib
`Kernel.withDensity` of `ProbabilityTheory.Kernel.const`).

**Proved here.**
* `transitionKernel_comp`: Chapman–Kolmogorov at the kernel level,
  `(P_t ∘ₖ P_s) a = P_{s+t} a` for `a ∈ S` (Mathlib `ProbabilityTheory.Kernel.comp`);
  `transitionKernel_apply_univ` (mass), `isMarkovKernel_transitionKernel`,
  `isFiniteKernel_transitionKernel` (for `S = univ`); `lintegral_fddMeasure_one`: the one-time
  finite-dimensional law is `P_t(z, ·)`.
* `lintegral_removeNth_fddDensity` (**consistency, a middle time**): for `0 < t₁ < ⋯ < t_{k+1}`,
  a non-last index `j` and measurable `F ≥ 0`,
  `∫⁻ F(zs without z_j) · Πp(ts)(zs) dμ^{k+1} = ∫⁻ F · Πp(ts without t_j) dμ^k`
  (Chapman–Kolmogorov only; sub-Markov suffices).
* `lintegral_init_fddDensity` (**consistency, the last time**): for a Markov density,
  `∫⁻ F(zs without z_{k+1}) · Πp(ts)(zs) dμ^{k+1} = ∫⁻ F · Πp(ts without t_{k+1}) dμ^k`;
  `lintegral_init_fddDensity_le`: `≤` for a sub-Markov density.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E]

/-!
### Definitions
-/

/-- **Chapman–Kolmogorov transition densities** on the state space `S` relative to `μ`. -/
structure IsCKDensity (μ : Measure E) (S : Set E) (p : ℝ → E → E → ℝ≥0∞) : Prop where
  meas : ∀ t, Measurable fun q : E × E => p t q.1 q.2
  stays : ∀ t, 0 < t → ∀ a ∈ S, ∀ᵐ y ∂μ, p t a y ≠ 0 → y ∈ S
  ck : ∀ s t, 0 < s → 0 < t → ∀ a ∈ S, ∀ b, ∫⁻ y, p s a y * p t y b ∂μ = p (s + t) a b

/-- Sub-Markov on `S`: `∫⁻ p_t(a, ·) dμ ≤ 1` for `t > 0`, `a ∈ S`. -/
def IsSubMarkovOn (μ : Measure E) (S : Set E) (p : ℝ → E → E → ℝ≥0∞) : Prop :=
  ∀ t, 0 < t → ∀ a ∈ S, ∫⁻ b, p t a b ∂μ ≤ 1

/-- Markov on `S`: `∫⁻ p_t(a, ·) dμ = 1` for `t > 0`, `a ∈ S`. -/
def IsMarkovOn (μ : Measure E) (S : Set E) (p : ℝ → E → E → ℝ≥0∞) : Prop :=
  ∀ t, 0 < t → ∀ a ∈ S, ∫⁻ b, p t a b ∂μ = 1

theorem IsMarkovOn.isSubMarkovOn {μ : Measure E} {S : Set E} {p : ℝ → E → E → ℝ≥0∞}
    (h : IsMarkovOn μ S p) : IsSubMarkovOn μ S p :=
  fun t ht a ha => (h t ht a ha).le

/-- The transition kernel `P_t(a, db) = p_t(a, b) μ(db)`. -/
def transitionKernel (μ : Measure E) [SFinite μ] (p : ℝ → E → E → ℝ≥0∞) (t : ℝ) : Kernel E E :=
  Kernel.withDensity (Kernel.const E μ) (p t)

/-!
### The kernel level
-/

section Kernel

variable {μ : Measure E} [SFinite μ] {S : Set E} {p : ℝ → E → E → ℝ≥0∞}

theorem transitionKernel_apply (hp : ∀ t, Measurable fun q : E × E => p t q.1 q.2) (t : ℝ)
    (a : E) : transitionKernel μ p t a = μ.withDensity (p t a) := by
  rw [transitionKernel, Kernel.withDensity_apply _ (hp t), Kernel.const_apply]

theorem transitionKernel_apply_set (hp : ∀ t, Measurable fun q : E × E => p t q.1 q.2) (t : ℝ)
    (a : E) {B : Set E} (hB : MeasurableSet B) :
    transitionKernel μ p t a B = ∫⁻ b in B, p t a b ∂μ := by
  rw [transitionKernel_apply hp, withDensity_apply _ hB]

theorem transitionKernel_apply_univ (hp : ∀ t, Measurable fun q : E × E => p t q.1 q.2) (t : ℝ)
    (a : E) : transitionKernel μ p t a univ = ∫⁻ b, p t a b ∂μ := by
  rw [transitionKernel_apply_set hp t a MeasurableSet.univ, Measure.restrict_univ]

/-- **Chapman–Kolmogorov at the kernel level**: `(P_t ∘ₖ P_s) a = P_{s+t} a` for `a ∈ S`. -/
theorem transitionKernel_comp (hp : IsCKDensity μ S p) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {a : E} (ha : a ∈ S) :
    (transitionKernel μ p t ∘ₖ transitionKernel μ p s) a = transitionKernel μ p (s + t) a := by
  ext B hB
  have hpa : Measurable (p s a) := (hp.meas s).comp (measurable_const.prodMk measurable_id)
  rw [Kernel.comp_apply' _ _ _ hB, transitionKernel_apply hp.meas s a,
    lintegral_withDensity_eq_lintegral_mul _ hpa (Kernel.measurable_coe _ hB),
    transitionKernel_apply_set hp.meas _ _ hB]
  simp only [Pi.mul_apply]
  have hint : ∀ y, p s a y * transitionKernel μ p t y B = ∫⁻ b in B, p s a y * p t y b ∂μ := by
    intro y
    rw [transitionKernel_apply_set hp.meas t y hB, lintegral_const_mul]
    exact (hp.meas t).comp (measurable_const.prodMk measurable_id)
  simp_rw [hint]
  rw [lintegral_lintegral_swap]
  · refine lintegral_congr fun b => hp.ck s t hs ht a ha b
  · exact (((hp.meas s).comp (measurable_const.prodMk measurable_fst)).mul
      (hp.meas t)).aemeasurable

theorem isMarkovKernel_transitionKernel (hp : ∀ t, Measurable fun q : E × E => p t q.1 q.2)
    {t : ℝ} (h1 : ∀ a, ∫⁻ b, p t a b ∂μ = 1) : IsMarkovKernel (transitionKernel μ p t) :=
  ⟨fun a => ⟨by rw [transitionKernel_apply_univ hp, h1]⟩⟩

theorem isFiniteKernel_transitionKernel (hp : ∀ t, Measurable fun q : E × E => p t q.1 q.2)
    {t : ℝ} (h1 : ∀ a, ∫⁻ b, p t a b ∂μ ≤ 1) : IsFiniteKernel (transitionKernel μ p t) :=
  ⟨⟨1, ENNReal.one_lt_top, fun a => by rw [transitionKernel_apply_univ hp]; exact h1 a⟩⟩

end Kernel

/-!
### Tuple bookkeeping
-/

section Tuple

variable {α : Type*}

theorem removeNth_succ_cons {k : ℕ} (j : Fin (k + 1)) (y : α) (ws : Fin (k + 1) → α) :
    Fin.removeNth j.succ (Fin.cons y ws : Fin (k + 2) → α) =
      (Fin.cons y (Fin.removeNth j ws) : Fin (k + 1) → α) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [Fin.removeNth]
  · simp [Fin.removeNth, Fin.succ_succAbove_succ]

theorem init_cons {k : ℕ} (y : α) (ws : Fin (k + 1) → α) :
    Fin.init (Fin.cons y ws : Fin (k + 2) → α) = (Fin.cons y (Fin.init ws) : Fin (k + 1) → α) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [Fin.init]
  · simp [Fin.init]

theorem measurable_removeNth {k : ℕ} (j : Fin (k + 1)) :
    Measurable (Fin.removeNth j : (Fin (k + 1) → E) → Fin k → E) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem measurable_init {k : ℕ} : Measurable (Fin.init : (Fin (k + 1) → E) → Fin k → E) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem measurable_cons_pair {k : ℕ} :
    Measurable fun q : E × (Fin k → E) => (Fin.cons q.1 q.2 : Fin (k + 1) → E) :=
  measurable_pi_iff.2 fun i => Fin.cases (by simpa using measurable_fst)
    (fun j => by simp only [Fin.cons_succ]; exact (measurable_pi_apply j).comp measurable_snd) i

theorem measurable_cons_left {k : ℕ} (y : E) :
    Measurable fun ws : Fin k → E => (Fin.cons y ws : Fin (k + 1) → E) :=
  measurable_pi_iff.2 fun j => measurable_cons_apply y j

end Tuple

/-!
### Consistency
-/

section Consistency

variable {μ : Measure E} [SigmaFinite μ] {S : Set E} {p : ℝ → E → E → ℝ≥0∞}

/-- **The one-time law is the transition kernel**: `fddMeasure μ p z ![t]` is the image of
`P_t(z, ·)` under `x ↦ (fun _ => x)`, in integrated form. -/
theorem lintegral_fddMeasure_one (hp : ∀ t, Measurable fun q : E × E => p t q.1 q.2) (z : E)
    (t : ℝ) {F : (Fin 1 → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ zs, F zs ∂(fddMeasure μ p z ![t]) = ∫⁻ x, F (fun _ => x) ∂(transitionKernel μ p t z) := by
  rw [lintegral_fddMeasure μ hp z _ hF, lintegral_pi_one μ (f := fun zs => F zs *
      fddDensity p z ![t] zs) (hF.mul (measurable_fddDensity hp z _)), transitionKernel_apply hp,
    lintegral_withDensity_eq_lintegral_mul _ (f := p t z)
      ((hp t).comp (measurable_const.prodMk measurable_id)) (g := fun x => F fun _ => x)
      (hF.comp (measurable_pi_iff.2 fun _ => measurable_id))]
  refine lintegral_congr fun x => ?_
  rw [fddDensity_succ, fddDensity_zero, mul_one]
  simp only [Matrix.cons_val_zero, Pi.mul_apply]
  ring

/-- **Consistency of the finite-dimensional densities at a middle time** (Chapman–Kolmogorov):
for `0 < t₁ < ⋯ < t_{k+1}`, `j ≠ k + 1` (zero-based: `j ≠ Fin.last k`), a start `z ∈ S` and
measurable `F ≥ 0`, integrating out `z_j` replaces `ts` by `ts` without `t_j`. -/
theorem lintegral_removeNth_fddDensity (hp : IsCKDensity μ S p) :
    ∀ {k : ℕ} {z : E}, z ∈ S → ∀ (ts : Fin (k + 1) → ℝ), StrictMono ts → (∀ i, 0 < ts i) →
      ∀ (j : Fin (k + 1)), j ≠ Fin.last k → ∀ {F : (Fin k → E) → ℝ≥0∞}, Measurable F →
        ∫⁻ zs, F (Fin.removeNth j zs) * fddDensity p z ts zs
            ∂(Measure.pi fun _ : Fin (k + 1) => μ) =
          ∫⁻ zs, F zs * fddDensity p z (Fin.removeNth j ts) zs
            ∂(Measure.pi fun _ : Fin k => μ) := by
  intro k
  induction k with
  | zero =>
    intro z _ ts _ _ j hj
    exact absurd (Fin.fin_one_eq_zero j) hj
  | succ m ih =>
    intro z hz ts hts hpos j hj F hF
    have hD := measurable_fddDensity hp.meas
    have h0 : 0 < ts 0 := hpos 0
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · -- marginalizing the first time: Chapman–Kolmogorov at `z`
      have hm : Measurable fun zs : Fin (m + 2) → E =>
          F (Fin.removeNth 0 zs) * fddDensity p z ts zs :=
        (hF.comp (measurable_removeNth 0)).mul (hD z ts)
      rw [lintegral_pi_cons μ hm, lintegral_lintegral_swap (f := fun x ws =>
        F (Fin.removeNth 0 (Fin.cons x ws : Fin (m + 2) → E)) *
          fddDensity p z ts (Fin.cons x ws : Fin (m + 2) → E))
        ((hm.comp measurable_cons_pair).aemeasurable)]
      refine lintegral_congr fun ws => ?_
      simp only [Fin.removeNth_zero, Fin.tail_cons]
      have h1 : 0 < ts (0 : Fin (m + 1)).succ - ts 0 := shift_pos hts 0
      have hx : ∀ x, F ws * fddDensity p z ts (Fin.cons x ws) =
          (F ws * fddDensity p (ws 0)
            (fun i => (ts i.succ.succ - ts 0) - (ts (0 : Fin (m + 1)).succ - ts 0)) (Fin.tail ws)) *
            (p (ts 0) z x * p (ts (0 : Fin (m + 1)).succ - ts 0) x (ws 0)) := by
        intro x
        rw [fddDensity_succ, fddDensity_succ]
        simp only [Fin.cons_zero, Fin.tail_cons]
        ring
      simp_rw [hx]
      rw [lintegral_const_mul (f := fun x =>
          p (ts 0) z x * p (ts (0 : Fin (m + 1)).succ - ts 0) x (ws 0)) _
          (((hp.meas _).comp (measurable_const.prodMk measurable_id)).mul
          ((hp.meas _).comp (measurable_id.prodMk measurable_const))),
        hp.ck _ _ h0 h1 z hz, add_sub_cancel, fddDensity_succ]
      have ht : (fun i : Fin m => (ts i.succ.succ - ts 0) - (ts (0 : Fin (m + 1)).succ - ts 0)) =
          fun i => Fin.removeNth 0 ts i.succ - Fin.removeNth 0 ts 0 := by
        funext i
        simp only [Fin.removeNth_zero, Fin.tail]
        ring
      rw [ht]
      simp only [Fin.removeNth_zero, Fin.tail]
      ring
    · -- a later time: restart at `z₁` and induct
      have hj'' : j' ≠ Fin.last m := fun h => hj (by rw [h, Fin.succ_last])
      have hm : Measurable fun zs : Fin (m + 2) → E =>
          F (Fin.removeNth j'.succ zs) * fddDensity p z ts zs :=
        (hF.comp (measurable_removeNth _)).mul (hD z ts)
      have hm' : Measurable fun zs : Fin (m + 1) → E =>
          F zs * fddDensity p z (Fin.removeNth j'.succ ts) zs := hF.mul (hD z _)
      rw [lintegral_pi_cons μ hm, lintegral_pi_cons μ hm']
      have hL : ∀ y : E, ∫⁻ ws, F (Fin.removeNth j'.succ (Fin.cons y ws : Fin (m + 2) → E)) *
            fddDensity p z ts (Fin.cons y ws : Fin (m + 2) → E)
              ∂(Measure.pi fun _ : Fin (m + 1) => μ) =
          p (ts 0) z y * ∫⁻ ws, F (Fin.cons y (Fin.removeNth j' ws)) *
            fddDensity p y (fun i => ts i.succ - ts 0) ws
              ∂(Measure.pi fun _ : Fin (m + 1) => μ) := by
        intro y
        rw [← lintegral_const_mul (f := fun ws => F (Fin.cons y (Fin.removeNth j' ws)) *
            fddDensity p y (fun i => ts i.succ - ts 0) ws) _
          (((hF.comp (measurable_cons_left y)).comp (measurable_removeNth j')).mul (hD _ _))]
        refine lintegral_congr fun ws => ?_
        rw [removeNth_succ_cons, fddDensity_succ]
        simp only [Fin.cons_zero, Fin.tail_cons]
        ring
      have hR : ∀ y : E, ∫⁻ ws, F (Fin.cons y ws : Fin (m + 1) → E) *
            fddDensity p z (Fin.removeNth j'.succ ts) (Fin.cons y ws : Fin (m + 1) → E)
              ∂(Measure.pi fun _ : Fin m => μ) =
          p (ts 0) z y * ∫⁻ ws, F (Fin.cons y ws) *
            fddDensity p y (Fin.removeNth j' fun i => ts i.succ - ts 0) ws
              ∂(Measure.pi fun _ : Fin m => μ) := by
        intro y
        rw [← lintegral_const_mul (f := fun ws => F (Fin.cons y ws : Fin (m + 1) → E) *
            fddDensity p y (Fin.removeNth j' fun i => ts i.succ - ts 0) ws) _
          ((hF.comp (measurable_cons_left y)).mul (hD _ _))]
        refine lintegral_congr fun ws => ?_
        rw [fddDensity_succ]
        simp only [Fin.cons_zero, Fin.tail_cons]
        have h0' : Fin.removeNth j'.succ ts 0 = ts 0 := by simp [Fin.removeNth]
        have ht : (fun i : Fin m => Fin.removeNth j'.succ ts i.succ - ts 0) =
            Fin.removeNth j' fun i => ts i.succ - ts 0 := by
          funext i
          simp [Fin.removeNth, Fin.succ_succAbove_succ]
        rw [h0', ht]
        ring
      simp_rw [hL, hR]
      refine lintegral_congr_ae ?_
      filter_upwards [hp.stays _ h0 z hz] with y hy
      by_cases hpy : p (ts 0) z y = 0
      · simp [hpy]
      · rw [ih (hy hpy) _ (shift_strictMono hts) (shift_pos hts) j' hj''
          (F := fun ws => F (Fin.cons y ws)) (hF.comp (measurable_cons_left y))]

/-- **Consistency of the finite-dimensional densities at the last time** for a Markov density:
integrating out `z_{k+1}` replaces `ts` by `Fin.init ts`. -/
theorem lintegral_init_fddDensity (hp : IsCKDensity μ S p) (hM : IsMarkovOn μ S p) :
    ∀ {k : ℕ} {z : E}, z ∈ S → ∀ (ts : Fin (k + 1) → ℝ), StrictMono ts → (∀ i, 0 < ts i) →
      ∀ {F : (Fin k → E) → ℝ≥0∞}, Measurable F →
        ∫⁻ zs, F (Fin.init zs) * fddDensity p z ts zs ∂(Measure.pi fun _ : Fin (k + 1) => μ) =
          ∫⁻ zs, F zs * fddDensity p z (Fin.init ts) zs ∂(Measure.pi fun _ : Fin k => μ) := by
  intro k
  have hD := measurable_fddDensity hp.meas
  induction k with
  | zero =>
    intro z hz ts _ hpos F hF
    rw [lintegral_pi_one μ (f := fun zs => F (Fin.init zs) * fddDensity p z ts zs)
        ((hF.comp measurable_init).mul (hD z ts)),
      lintegral_pi_zero μ (f := fun zs => F zs * fddDensity p z (Fin.init ts) zs)
        (hF.mul (hD z _)) Fin.elim0, fddDensity_zero, mul_one]
    have hc : ∀ x : E, F (Fin.init fun _ : Fin 1 => x) * fddDensity p z ts (fun _ => x) =
        F Fin.elim0 * p (ts 0) z x := by
      intro x
      rw [fddDensity_succ, fddDensity_zero, mul_one, Subsingleton.elim (Fin.init _) Fin.elim0]
    simp_rw [hc]
    rw [lintegral_const_mul (f := fun x => p (ts 0) z x) _
      ((hp.meas _).comp (measurable_const.prodMk measurable_id)), hM _ (hpos 0) z hz, mul_one]
  | succ m ih =>
    intro z hz ts hts hpos F hF
    have hm : Measurable fun zs : Fin (m + 2) → E => F (Fin.init zs) * fddDensity p z ts zs :=
      (hF.comp measurable_init).mul (hD z ts)
    rw [lintegral_pi_cons μ hm, lintegral_pi_cons μ
      (f := fun zs => F zs * fddDensity p z (Fin.init ts) zs) (hF.mul (hD z _))]
    refine lintegral_congr_ae ?_
    filter_upwards [hp.stays _ (hpos 0) z hz] with y hy
    have hL : ∫⁻ ws, F (Fin.init (Fin.cons y ws : Fin (m + 2) → E)) *
          fddDensity p z ts (Fin.cons y ws : Fin (m + 2) → E)
            ∂(Measure.pi fun _ : Fin (m + 1) => μ) =
        p (ts 0) z y * ∫⁻ ws, F (Fin.cons y (Fin.init ws)) *
          fddDensity p y (fun i => ts i.succ - ts 0) ws ∂(Measure.pi fun _ : Fin (m + 1) => μ) := by
      rw [← lintegral_const_mul (f := fun ws => F (Fin.cons y (Fin.init ws)) *
          fddDensity p y (fun i => ts i.succ - ts 0) ws) _
        (((hF.comp (measurable_cons_left y)).comp measurable_init).mul (hD _ _))]
      refine lintegral_congr fun ws => ?_
      rw [init_cons, fddDensity_succ]
      simp only [Fin.cons_zero, Fin.tail_cons]
      ring
    have hR : ∫⁻ ws, F (Fin.cons y ws : Fin (m + 1) → E) *
          fddDensity p z (Fin.init ts) (Fin.cons y ws : Fin (m + 1) → E)
            ∂(Measure.pi fun _ : Fin m => μ) =
        p (ts 0) z y * ∫⁻ ws, F (Fin.cons y ws) *
          fddDensity p y (Fin.init fun i => ts i.succ - ts 0) ws
            ∂(Measure.pi fun _ : Fin m => μ) := by
      rw [← lintegral_const_mul (f := fun ws => F (Fin.cons y ws : Fin (m + 1) → E) *
          fddDensity p y (Fin.init fun i => ts i.succ - ts 0) ws) _
        ((hF.comp (measurable_cons_left y)).mul (hD _ _))]
      refine lintegral_congr fun ws => ?_
      rw [fddDensity_succ]
      simp only [Fin.cons_zero, Fin.tail_cons]
      simp only [Fin.init, Fin.castSucc_zero]
      have ht : (fun i : Fin m => ts i.succ.castSucc - ts 0) =
          Fin.init fun i => ts i.succ - ts 0 := by
        funext i
        simp only [Fin.init, Fin.succ_castSucc]
      rw [ht]
      ring
    rw [hL, hR]
    by_cases hpy : p (ts 0) z y = 0
    · simp [hpy]
    · rw [ih (hy hpy) _ (shift_strictMono hts) (shift_pos hts)
        (F := fun ws => F (Fin.cons y ws)) (hF.comp (measurable_cons_left y))]

/-- **Last-time consistency for a sub-Markov density** (the killed case): integrating out
`z_{k+1}` gives at most the density at `Fin.init ts`. -/
theorem lintegral_init_fddDensity_le (hp : IsCKDensity μ S p) (hM : IsSubMarkovOn μ S p) :
    ∀ {k : ℕ} {z : E}, z ∈ S → ∀ (ts : Fin (k + 1) → ℝ), StrictMono ts → (∀ i, 0 < ts i) →
      ∀ {F : (Fin k → E) → ℝ≥0∞}, Measurable F →
        ∫⁻ zs, F (Fin.init zs) * fddDensity p z ts zs ∂(Measure.pi fun _ : Fin (k + 1) => μ) ≤
          ∫⁻ zs, F zs * fddDensity p z (Fin.init ts) zs ∂(Measure.pi fun _ : Fin k => μ) := by
  intro k
  have hD := measurable_fddDensity hp.meas
  induction k with
  | zero =>
    intro z hz ts _ hpos F hF
    rw [lintegral_pi_one μ (f := fun zs => F (Fin.init zs) * fddDensity p z ts zs)
        ((hF.comp measurable_init).mul (hD z ts)),
      lintegral_pi_zero μ (f := fun zs => F zs * fddDensity p z (Fin.init ts) zs)
        (hF.mul (hD z _)) Fin.elim0, fddDensity_zero, mul_one]
    have hc : ∀ x : E, F (Fin.init fun _ : Fin 1 => x) * fddDensity p z ts (fun _ => x) =
        F Fin.elim0 * p (ts 0) z x := by
      intro x
      rw [fddDensity_succ, fddDensity_zero, mul_one, Subsingleton.elim (Fin.init _) Fin.elim0]
    simp_rw [hc]
    rw [lintegral_const_mul (f := fun x => p (ts 0) z x) _
      ((hp.meas _).comp (measurable_const.prodMk measurable_id))]
    calc F Fin.elim0 * ∫⁻ x, p (ts 0) z x ∂μ ≤ F Fin.elim0 * 1 := by
          gcongr; exact hM _ (hpos 0) z hz
      _ = F Fin.elim0 := mul_one _
  | succ m ih =>
    intro z hz ts hts hpos F hF
    have hm : Measurable fun zs : Fin (m + 2) → E => F (Fin.init zs) * fddDensity p z ts zs :=
      (hF.comp measurable_init).mul (hD z ts)
    rw [lintegral_pi_cons μ hm, lintegral_pi_cons μ
      (f := fun zs => F zs * fddDensity p z (Fin.init ts) zs) (hF.mul (hD z _))]
    refine lintegral_mono_ae ?_
    filter_upwards [hp.stays _ (hpos 0) z hz] with y hy
    have hL : ∫⁻ ws, F (Fin.init (Fin.cons y ws : Fin (m + 2) → E)) *
          fddDensity p z ts (Fin.cons y ws : Fin (m + 2) → E)
            ∂(Measure.pi fun _ : Fin (m + 1) => μ) =
        p (ts 0) z y * ∫⁻ ws, F (Fin.cons y (Fin.init ws)) *
          fddDensity p y (fun i => ts i.succ - ts 0) ws ∂(Measure.pi fun _ : Fin (m + 1) => μ) := by
      rw [← lintegral_const_mul (f := fun ws => F (Fin.cons y (Fin.init ws)) *
          fddDensity p y (fun i => ts i.succ - ts 0) ws) _
        (((hF.comp (measurable_cons_left y)).comp measurable_init).mul (hD _ _))]
      refine lintegral_congr fun ws => ?_
      rw [init_cons, fddDensity_succ]
      simp only [Fin.cons_zero, Fin.tail_cons]
      ring
    have hR : ∫⁻ ws, F (Fin.cons y ws : Fin (m + 1) → E) *
          fddDensity p z (Fin.init ts) (Fin.cons y ws : Fin (m + 1) → E)
            ∂(Measure.pi fun _ : Fin m => μ) =
        p (ts 0) z y * ∫⁻ ws, F (Fin.cons y ws) *
          fddDensity p y (Fin.init fun i => ts i.succ - ts 0) ws
            ∂(Measure.pi fun _ : Fin m => μ) := by
      rw [← lintegral_const_mul (f := fun ws => F (Fin.cons y ws : Fin (m + 1) → E) *
          fddDensity p y (Fin.init fun i => ts i.succ - ts 0) ws) _
        ((hF.comp (measurable_cons_left y)).mul (hD _ _))]
      refine lintegral_congr fun ws => ?_
      rw [fddDensity_succ]
      simp only [Fin.cons_zero, Fin.tail_cons]
      simp only [Fin.init, Fin.castSucc_zero]
      have ht : (fun i : Fin m => ts i.succ.castSucc - ts 0) =
          Fin.init fun i => ts i.succ - ts 0 := by
        funext i
        simp only [Fin.init, Fin.succ_castSucc]
      rw [ht]
      ring
    rw [hL, hR]
    by_cases hpy : p (ts 0) z y = 0
    · simp [hpy]
    · gcongr
      exact ih (hy hpy) _ (shift_strictMono hts) (shift_pos hts)
        (F := fun ws => F (Fin.cons y ws)) (hF.comp (measurable_cons_left y))

end Consistency

end BlockBand.Diffusion
