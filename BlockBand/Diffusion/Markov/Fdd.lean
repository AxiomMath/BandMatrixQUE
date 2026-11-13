module

public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite-dimensional densities of a process with transition densities

* `lastTime ts = t_k` (`0` if `k = 0`), `lastPoint z zs = z_k` (`z` if `k = 0`);
* `fddDensity p z ts zs = ∏ᵢ p_{tᵢ - tᵢ₋₁}(zᵢ₋₁, zᵢ)` — the density, relative to `μ^k`, of the
  finite-dimensional law `fddMeasure μ p z ts` of the process started at `z`.

**Proved here** (no hypotheses beyond measurability):
* `fddDensity_succ` (front recursion: first step, then the shifted process from `z₁`),
  `fddDensity_snoc` (back recursion: last step);
* `lintegral_pi_cons`, `lintegral_pi_snoc`: splitting `μ^{k+1}` at the first/last coordinate;
* `lintegral_fddMeasure`: the density form `∫⁻ F d(fdd) = ∫⁻ F · Πp dμ^k`;
* `lintegral_fddDensity_snoc`: the iterated-kernel form
  `∫⁻ F · Πp(ts ⧺ t) = ∫⁻ Πp(ts) · ∫⁻ F(zs ⧺ x) p_{t - t_k}(z_k, x) dμ(x) dμ^k(zs)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-!
### Notation
-/

/-- The last time `t_k` of `t₁, …, t_k` (`0` if `k = 0`). -/
def lastTime {k : ℕ} (ts : Fin k → ℝ) : ℝ := (Fin.cons 0 ts : Fin (k + 1) → ℝ) (Fin.last k)

/-- The last point `z_k` of `z₀ = z, z₁, …, z_k` (`z` if `k = 0`). -/
def lastPoint {α : Type*} (z : α) {k : ℕ} (zs : Fin k → α) : α :=
  (Fin.cons z zs : Fin (k + 1) → α) (Fin.last k)

/-- **The finite-dimensional density** `p_{t₁}(z, z₁) p_{t₂-t₁}(z₁, z₂) ⋯ p_{t_k-t_{k-1}}(z_{k-1},
z_k)` of the process with transition densities `p` started at `z` (`t₀ = 0`, `z₀ = z`). -/
def fddDensity {E : Type*} (p : ℝ → E → E → ℝ≥0∞) (z : E) {k : ℕ} (ts : Fin k → ℝ)
    (zs : Fin k → E) : ℝ≥0∞ :=
  ∏ i : Fin k, p (ts i - (Fin.cons 0 ts : Fin (k + 1) → ℝ) i.castSucc)
    ((Fin.cons z zs : Fin (k + 1) → E) i.castSucc) (zs i)

/-- **The finite-dimensional law** at times `ts` of the process with transition densities `p`
relative to `μ`, started at `z`: `μ^k` with density `fddDensity p z ts`. -/
def fddMeasure {E : Type*} [MeasurableSpace E] (μ : Measure E) (p : ℝ → E → E → ℝ≥0∞) (z : E)
    {k : ℕ} (ts : Fin k → ℝ) : Measure (Fin k → E) :=
  (Measure.pi fun _ : Fin k => μ).withDensity (fddDensity p z ts)

/-!
### Bookkeeping
-/

section Bookkeeping

variable {α : Type*}

theorem lastTime_zero (ts : Fin 0 → ℝ) : lastTime ts = 0 := rfl

theorem lastTime_succ {k : ℕ} (ts : Fin (k + 1) → ℝ) : lastTime ts = ts (Fin.last k) := by
  simp only [lastTime, ← Fin.succ_last, Fin.cons_succ]

theorem lastPoint_zero (z : α) (zs : Fin 0 → α) : lastPoint z zs = z := rfl

theorem lastPoint_succ (z : α) {k : ℕ} (zs : Fin (k + 1) → α) :
    lastPoint z zs = zs (Fin.last k) := by
  simp only [lastPoint, ← Fin.succ_last, Fin.cons_succ]

/-- The last point of `z₀, z₁, …, z_{k+1}` is the last point of `z₁, …, z_{k+1}`. -/
theorem lastPoint_succ_tail (z : α) {k : ℕ} (zs : Fin (k + 1) → α) :
    lastPoint z zs = lastPoint (zs 0) (Fin.tail zs) := by
  cases k with
  | zero => rw [lastPoint_succ, lastPoint_zero]; rfl
  | succ m => rw [lastPoint_succ, lastPoint_succ]; rfl

theorem lastPoint_snoc (z : α) {k : ℕ} (zs : Fin k → α) (x : α) :
    lastPoint z (Fin.snoc zs x : Fin (k + 1) → α) = x := by
  rw [lastPoint_succ, Fin.snoc_last]

theorem lastTime_snoc {k : ℕ} (ts : Fin k → ℝ) (t : ℝ) :
    lastTime (Fin.snoc ts t : Fin (k + 1) → ℝ) = t := by
  rw [lastTime_succ, Fin.snoc_last]

theorem cons_succ_castSucc (a : α) {k : ℕ} (f : Fin (k + 1) → α) (i : Fin k) :
    (Fin.cons a f : Fin (k + 2) → α) i.succ.castSucc = f i.castSucc := by
  rw [← Fin.succ_castSucc, Fin.cons_succ]

theorem cons_snoc_castSucc (a : α) {k : ℕ} (f : Fin k → α) (x : α) (i : Fin (k + 1)) :
    (Fin.cons a (Fin.snoc f x : Fin (k + 1) → α) : Fin (k + 2) → α) i.castSucc =
      (Fin.cons a f : Fin (k + 1) → α) i := by
  rw [Fin.cons_snoc_eq_snoc_cons, Fin.snoc_castSucc]

theorem lastTime_nonneg {k : ℕ} {ts : Fin k → ℝ} (hpos : ∀ i, 0 < ts i) : 0 ≤ lastTime ts := by
  cases k with
  | zero => exact le_rfl
  | succ m => rw [lastTime_succ]; exact (hpos _).le

theorem forall_lt_iff_lastTime_lt {k : ℕ} {ts : Fin k → ℝ} (hts : StrictMono ts) {t : ℝ}
    (ht : 0 < t) : (∀ i, ts i < t) ↔ lastTime ts < t := by
  cases k with
  | zero => simp [lastTime_zero, ht]
  | succ m =>
    rw [lastTime_succ]
    exact ⟨fun h => h _, fun h i => lt_of_le_of_lt (hts.monotone (Fin.le_last i)) h⟩

/-- The previous time `t_{i-1}` of a strictly increasing positive family is `< t_i`. -/
theorem cons_castSucc_lt {k : ℕ} {ts : Fin k → ℝ} (hts : StrictMono ts) (hpos : ∀ i, 0 < ts i)
    (i : Fin k) : (Fin.cons 0 ts : Fin (k + 1) → ℝ) i.castSucc < ts i := by
  cases k with
  | zero => exact i.elim0
  | succ m =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hpos 0
    · rw [← Fin.succ_castSucc, Fin.cons_succ]
      exact hts (Fin.castSucc_lt_succ)

/-- The shifted times `t_{i+1} - t₁` of the process restarted at the first time. -/
theorem shift_strictMono {k : ℕ} {ts : Fin (k + 1) → ℝ} (hts : StrictMono ts) :
    StrictMono fun i : Fin k => ts i.succ - ts 0 :=
  fun _ _ hij => sub_lt_sub_right (hts (Fin.succ_lt_succ_iff.2 hij)) _

theorem shift_pos {k : ℕ} {ts : Fin (k + 1) → ℝ} (hts : StrictMono ts) (i : Fin k) :
    0 < ts i.succ - ts 0 :=
  sub_pos.2 (hts (Fin.succ_pos i))

end Bookkeeping

/-!
### Recursions for the density
-/

section Recursion

variable {E : Type*}

/-- The shifted times seen from the first time, with `0` prepended. -/
theorem cons_zero_shift {k : ℕ} (ts : Fin (k + 1) → ℝ) (j : Fin (k + 1)) :
    (Fin.cons 0 (fun i : Fin k => ts i.succ - ts 0) : Fin (k + 1) → ℝ) j = ts j - ts 0 := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp
  · simp

theorem fddDensity_zero (p : ℝ → E → E → ℝ≥0∞) (z : E) (ts : Fin 0 → ℝ) (zs : Fin 0 → E) :
    fddDensity p z ts zs = 1 := by
  simp [fddDensity]

/-- **Front recursion**: the first step `p_{t₁}(z, z₁)`, then the process restarted at `z₁` with
the shifted times `t_{i+1} - t₁`. -/
theorem fddDensity_succ (p : ℝ → E → E → ℝ≥0∞) (z : E) {k : ℕ} (ts : Fin (k + 1) → ℝ)
    (zs : Fin (k + 1) → E) :
    fddDensity p z ts zs =
      p (ts 0) z (zs 0) * fddDensity p (zs 0) (fun i => ts i.succ - ts 0) (Fin.tail zs) := by
  unfold fddDensity
  rw [Fin.prod_univ_succ]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun i _ => ?_
    have ht : ts i.succ - (Fin.cons 0 ts : Fin (k + 2) → ℝ) i.succ.castSucc =
        (ts i.succ - ts 0) -
          (Fin.cons 0 (fun j : Fin k => ts j.succ - ts 0) : Fin (k + 1) → ℝ) i.castSucc := by
      rw [cons_succ_castSucc, cons_zero_shift]
      ring
    have hz : (Fin.cons z zs : Fin (k + 2) → E) i.succ.castSucc =
        (Fin.cons (zs 0) (Fin.tail zs) : Fin (k + 1) → E) i.castSucc := by
      rw [cons_succ_castSucc, Fin.cons_self_tail]
    rw [ht, hz]
    rfl

/-- **Back recursion**: the density at `ts ⧺ t`, `zs ⧺ x` is the density at `ts`, `zs` times the
last step `p_{t - t_k}(z_k, x)`. -/
theorem fddDensity_snoc (p : ℝ → E → E → ℝ≥0∞) (z : E) {k : ℕ} (ts : Fin k → ℝ) (t : ℝ)
    (zs : Fin k → E) (x : E) :
    fddDensity p z (Fin.snoc ts t : Fin (k + 1) → ℝ) (Fin.snoc zs x : Fin (k + 1) → E) =
      fddDensity p z ts zs * p (t - lastTime ts) (lastPoint z zs) x := by
  unfold fddDensity
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [cons_snoc_castSucc, cons_snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [cons_snoc_castSucc, cons_snoc_castSucc, Fin.snoc_last, Fin.snoc_last]
    rfl

end Recursion

/-!
### Measurability
-/

section Measurability

variable {E : Type*} [MeasurableSpace E]

theorem measurable_cons_apply (z : E) {k : ℕ} (j : Fin (k + 1)) :
    Measurable fun zs : Fin k → E => (Fin.cons z zs : Fin (k + 1) → E) j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cons_zero]
    exact measurable_const
  · simp only [Fin.cons_succ]
    exact measurable_pi_apply i

theorem measurable_lastPoint (z : E) {k : ℕ} :
    Measurable fun zs : Fin k → E => lastPoint z zs :=
  measurable_cons_apply z (Fin.last k)

/-- The finite-dimensional density is measurable when each `p t` is jointly measurable. -/
theorem measurable_fddDensity {p : ℝ → E → E → ℝ≥0∞}
    (hp : ∀ t, Measurable fun q : E × E => p t q.1 q.2) (z : E) {k : ℕ} (ts : Fin k → ℝ) :
    Measurable (fddDensity p z ts) := by
  unfold fddDensity
  refine Finset.measurable_prod _ fun i _ => ?_
  exact (hp _).comp ((measurable_cons_apply z i.castSucc).prodMk (measurable_pi_apply i))

end Measurability

/-!
### Splitting the product measure
-/

section Split

variable {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]

/-- Splitting `μ^{k+1}` at the first coordinate. -/
theorem lintegral_pi_cons {k : ℕ} {f : (Fin (k + 1) → E) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ zs, f zs ∂(Measure.pi fun _ : Fin (k + 1) => μ) =
      ∫⁻ y, ∫⁻ zs, f (Fin.cons y zs) ∂(Measure.pi fun _ : Fin k => μ) ∂μ := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0).symm
  rw [← h.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have hm : Measurable fun q : E × (Fin k → E) => f (Fin.cons q.1 q.2) :=
    hf.comp (measurable_pi_iff.2 fun i => Fin.cases (by simpa using measurable_fst)
      (fun j => by simp only [Fin.cons_succ]; exact (measurable_pi_apply j).comp measurable_snd)
      i)
  have he : (fun q : E × (Fin k → E) =>
      f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => E) 0).symm q)) =
      fun q => f (Fin.cons q.1 q.2) := by
    funext q
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply]
    show f (Fin.insertNth 0 q.1 q.2) = _
    rw [Fin.insertNth_zero']
  rw [he, lintegral_prod _ hm.aemeasurable]

/-- Splitting `μ^{k+1}` at the last coordinate. -/
theorem lintegral_pi_snoc {k : ℕ} {f : (Fin (k + 1) → E) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ zs, f zs ∂(Measure.pi fun _ : Fin (k + 1) => μ) =
      ∫⁻ zs, ∫⁻ x, f (Fin.snoc zs x) ∂μ ∂(Measure.pi fun _ : Fin k => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) (Fin.last k)).symm
  rw [← h.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have hm : Measurable fun q : E × (Fin k → E) => f (Fin.snoc q.2 q.1) := by
    refine hf.comp (measurable_pi_iff.2 fun i => ?_)
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      exact measurable_fst
    · simp only [Fin.snoc_castSucc]
      exact (measurable_pi_apply j).comp measurable_snd
  have he : (fun q : E × (Fin k → E) =>
      f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => E) (Fin.last k)).symm q)) =
      fun q => f (Fin.snoc q.2 q.1) := by
    funext q
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply]
    show f (Fin.insertNth (Fin.last k) q.1 q.2) = _
    rw [Fin.insertNth_last']
  rw [he, lintegral_prod _ hm.aemeasurable,
    lintegral_lintegral_swap (f := fun x y => f (Fin.snoc y x)) hm.aemeasurable]

omit [SigmaFinite μ] in
/-- Integration against `μ^0` is evaluation. -/
theorem lintegral_pi_zero {f : (Fin 0 → E) → ℝ≥0∞} (hf : Measurable f) (zs : Fin 0 → E) :
    ∫⁻ zs, f zs ∂(Measure.pi fun _ : Fin 0 => μ) = f zs := by
  rw [Measure.pi_of_empty (fun _ : Fin 0 => μ) zs, lintegral_dirac' _ hf]

/-- Integration against `μ^1` is integration against `μ`. -/
theorem lintegral_pi_one {f : (Fin 1 → E) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ zs, f zs ∂(Measure.pi fun _ : Fin 1 => μ) = ∫⁻ x, f (fun _ => x) ∂μ := by
  rw [lintegral_pi_cons μ hf]
  refine lintegral_congr fun y => ?_
  rw [lintegral_pi_zero μ (f := fun zs => f (Fin.cons y zs))
    (hf.comp (measurable_pi_iff.2 fun j => measurable_cons_apply y j)) Fin.elim0]
  congr 1
  funext i
  rw [Fin.fin_one_eq_zero i]
  rfl

end Split

/-!
### The density form and the iterated-kernel form
-/

section Forms

variable {E : Type*} [MeasurableSpace E] (μ : Measure E) {p : ℝ → E → E → ℝ≥0∞}

/-- **The density form** of the finite-dimensional law:
`∫⁻ F d(fddMeasure μ p z ts) = ∫⁻ F · fddDensity p z ts dμ^k`. -/
theorem lintegral_fddMeasure (hp : ∀ t, Measurable fun q : E × E => p t q.1 q.2) (z : E)
    {k : ℕ} (ts : Fin k → ℝ) {F : (Fin k → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ zs, F zs ∂(fddMeasure μ p z ts) =
      ∫⁻ zs, F zs * fddDensity p z ts zs ∂(Measure.pi fun _ : Fin k => μ) := by
  rw [fddMeasure, lintegral_withDensity_eq_lintegral_mul _ (measurable_fddDensity hp z ts) hF]
  refine lintegral_congr fun zs => ?_
  simp only [Pi.mul_apply]
  ring

theorem fddMeasure_apply (z : E) {k : ℕ} (ts : Fin k → ℝ) {B : Set (Fin k → E)}
    (hB : MeasurableSet B) :
    fddMeasure μ p z ts B = ∫⁻ zs in B, fddDensity p z ts zs ∂(Measure.pi fun _ : Fin k => μ) :=
  withDensity_apply _ hB

variable [SigmaFinite μ]

/-- **The iterated-kernel form** (Markov property of the finite-dimensional laws at the last
time): `∫⁻ F · Πp(ts ⧺ t) dμ^{k+1} = ∫⁻ Πp(ts)(zs) ∫⁻ F(zs ⧺ x) p_{t - t_k}(z_k, x) dμ(x) dμ^k`. -/
theorem lintegral_fddDensity_snoc (hp : ∀ t, Measurable fun q : E × E => p t q.1 q.2) (z : E)
    {k : ℕ} (ts : Fin k → ℝ) (t : ℝ) {F : (Fin (k + 1) → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ zs, F zs * fddDensity p z (Fin.snoc ts t : Fin (k + 1) → ℝ) zs
        ∂(Measure.pi fun _ : Fin (k + 1) => μ) =
      ∫⁻ zs, fddDensity p z ts zs *
          ∫⁻ x, F (Fin.snoc zs x) * p (t - lastTime ts) (lastPoint z zs) x ∂μ
        ∂(Measure.pi fun _ : Fin k => μ) := by
  rw [lintegral_pi_snoc μ (f := fun zs => F zs * fddDensity p z _ zs)
    (hF.mul (measurable_fddDensity hp z _))]
  refine lintegral_congr fun zs => ?_
  have hx : Measurable fun x => F (Fin.snoc zs x) * p (t - lastTime ts) (lastPoint z zs) x := by
    have hs : Measurable fun x : E => (Fin.snoc zs x : Fin (k + 1) → E) := by
      refine measurable_pi_iff.2 fun i => ?_
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        exact measurable_id
      · simp only [Fin.snoc_castSucc]
        exact measurable_const
    exact (hF.comp hs).mul ((hp _).comp (measurable_const.prodMk measurable_id))
  rw [← lintegral_const_mul _ hx]
  refine lintegral_congr fun x => ?_
  rw [fddDensity_snoc]
  ring

end Forms

end BlockBand.Diffusion
