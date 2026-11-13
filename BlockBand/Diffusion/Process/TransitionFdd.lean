module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite-dimensional laws of Markov chains and bridges built from transition densities

**Setting.**  `α` is a measurable space with a σ-finite reference measure `ν` (for instance
Lebesgue measure on `ℝ × ℝ`, or its restriction to a measurable state set `S`).  A transition
density is `q : ℝ → α → α → ℝ≥0∞` (`q s x y` = density at `y` w.r.t. `ν` of the law at time
`s > 0` started from `x`), jointly measurable in `(x, y)` for each `s` and satisfying
Chapman–Kolmogorov for positive times:
`∫⁻ w, q s x w * q u w y ∂ν = q (s + u) x y` (`0 < s`, `0 < u`, all `x y`).

**Space-time harmonic terminal weight.**  Both the forward Markov family and the bridge are
instances of one Doob-transformed chain: a terminal weight `h : ℝ → α → ℝ≥0∞` with
`∫⁻ w, q (s - s₀) x w * h s w ∂ν = h s₀ x` for `s₀ < s`, `s ∈ D`.  For the forward chain
`h = 1` (this is the Markov property `∫⁻ y, q s x y ∂ν = 1`; with a strictly sub-Markov
kernel the forward family is *not* consistent); for the bridge to `e` at time `t`,
`h s x = q (t - s) x e` (this is Chapman–Kolmogorov, and needs **no** Markov property).

**Main statements.**
* `chainDensity q h s₀ x₀ ts zs` =
  `q (t₁ - s₀) x₀ z₁ · q (t₂ - t₁) z₁ z₂ ⋯ q (t_k - t_{k-1}) z_{k-1} z_k · h t_k z_k`;
  `chainDensity_eq_prod` gives the explicit product form.
* `lintegral_chainDensity_insertNth`: integrating out one node gives the chain without it.
* `map_comp_chainFddMeasure`: for every strictly increasing `g : Fin m → Fin n`, the
  coordinate marginal of `chainFddMeasure … ts` along `g` is `chainFddMeasure … (ts ∘ g)`.
* `isProjectiveMeasureFamily_chainFamily`: the family indexed by `Finset T` of a linearly
  ordered time index `T` (time map `τ` strictly monotone) is projective;
  `map_eval_of_isProjectiveLimit_chainFamily` reads off the fdd of any projective limit at
  arbitrary strictly increasing times.
* Bridges: `bridgeFddDensity` (same shape as `bridgeFddDensity` of the base diffusion, with the
  kernel already `ℝ≥0∞`-valued), `bridgeFamily` on `T = Ioo 0 t`,
  `isProjectiveMeasureFamily_bridgeFamily`, `isProbabilityMeasure_bridgeFamily` (given
  `0 < q t z e < ∞`), `bridgeFddMeasure` (density `bridgeFddDensity` w.r.t. `ν ⊗ ⋯ ⊗ ν`),
  `bridgeFddMeasure_eq_smul`, and `map_eval_of_isProjectiveLimit_bridgeFamily`.
* Forward chains: `markovFamily` on `T = Ioi 0`, projective and probability under the Markov
  property.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Set
open scoped ENNReal

variable {α : Type*}

/-!
### The chain density
-/

/-- The Doob-transformed chain density: `q (t₁ - s₀) x₀ z₁ · ∏ q (t_{i+1} - t_i) z_i z_{i+1}`
times the terminal weight `h t_k z_k` (and `h s₀ x₀` for the empty chain). -/
def chainDensity (q : ℝ → α → α → ℝ≥0∞) (h : ℝ → α → ℝ≥0∞) :
    {k : ℕ} → ℝ → α → (Fin k → ℝ) → (Fin k → α) → ℝ≥0∞
  | 0, s₀, x₀, _, _ => h s₀ x₀
  | _ + 1, s₀, x₀, ts, zs =>
      q (ts 0 - s₀) x₀ (zs 0) * chainDensity q h (ts 0) (zs 0) (Fin.tail ts) (Fin.tail zs)

section ChainDensity

variable (q : ℝ → α → α → ℝ≥0∞) (h : ℝ → α → ℝ≥0∞)

@[simp] theorem chainDensity_zero (s₀ : ℝ) (x₀ : α) (ts : Fin 0 → ℝ) (zs : Fin 0 → α) :
    chainDensity q h s₀ x₀ ts zs = h s₀ x₀ := rfl

theorem chainDensity_succ {k : ℕ} (s₀ : ℝ) (x₀ : α) (ts : Fin (k + 1) → ℝ)
    (zs : Fin (k + 1) → α) :
    chainDensity q h s₀ x₀ ts zs =
      q (ts 0 - s₀) x₀ (zs 0) * chainDensity q h (ts 0) (zs 0) (Fin.tail ts) (Fin.tail zs) :=
  rfl

@[simp] theorem chainDensity_cons {k : ℕ} (s₀ : ℝ) (x₀ : α) (t : ℝ) (ts : Fin k → ℝ) (z : α)
    (zs : Fin k → α) :
    chainDensity q h s₀ x₀ (Fin.cons t ts) (Fin.cons z zs) =
      q (t - s₀) x₀ z * chainDensity q h t z ts zs := by
  rw [chainDensity_succ]
  simp

/-- Explicit product form of the chain density (with `t₀ = s₀`, `z₀ = x₀`). -/
theorem chainDensity_eq_prod : ∀ {k : ℕ} (s₀ : ℝ) (x₀ : α) (ts : Fin k → ℝ) (zs : Fin k → α),
    chainDensity q h s₀ x₀ ts zs =
      (∏ i : Fin k, q (ts i - (Fin.cons s₀ ts : Fin (k + 1) → ℝ) i.castSucc)
        ((Fin.cons x₀ zs : Fin (k + 1) → α) i.castSucc) (zs i)) *
      h ((Fin.cons s₀ ts : Fin (k + 1) → ℝ) (Fin.last k))
        ((Fin.cons x₀ zs : Fin (k + 1) → α) (Fin.last k))
  | 0, s₀, x₀, ts, zs => by simp
  | k + 1, s₀, x₀, ts, zs => by
    rw [chainDensity_succ, chainDensity_eq_prod (ts 0) (zs 0) (Fin.tail ts) (Fin.tail zs),
      Fin.prod_univ_succ, mul_assoc]
    congr 1
    simp [Fin.tail]

variable {q h} [MeasurableSpace α]

/-- Joint measurability of the chain density in the starting point and the nodes. -/
theorem measurable_chainDensity (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2)
    (hhm : ∀ s, Measurable (h s)) :
    ∀ {k : ℕ} (s₀ : ℝ) (ts : Fin k → ℝ),
      Measurable fun p : α × (Fin k → α) => chainDensity q h s₀ p.1 ts p.2
  | 0, s₀, ts => by
    exact (hhm s₀).comp measurable_fst
  | k + 1, s₀, ts => by
    simp only [chainDensity_succ]
    refine Measurable.mul ?_ ?_
    · exact (hq _).comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
    · refine (measurable_chainDensity hq hhm (ts 0) (Fin.tail ts)).comp
        (f := fun p : α × (Fin (k + 1) → α) => (p.2 0, Fin.tail p.2)) ?_
      refine ((measurable_pi_apply 0).comp measurable_snd).prodMk ?_
      exact Measurable.of_eval fun i => (measurable_pi_apply _).comp measurable_snd

theorem measurable_insertNth {k : ℕ} (j : Fin (k + 1)) (zs : Fin k → α) :
    Measurable fun w : α => (j.insertNth w zs : Fin (k + 1) → α) := by
  have := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) j).symm.measurable.comp
    (measurable_id.prodMk (measurable_const (a := zs)))
  exact this

theorem measurable_chainDensity_insertNth (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2)
    (hhm : ∀ s, Measurable (h s)) {k : ℕ} (s₀ : ℝ) (x₀ : α) (ts : Fin (k + 1) → ℝ)
    (j : Fin (k + 1)) (zs : Fin k → α) :
    Measurable fun w : α => chainDensity q h s₀ x₀ ts (j.insertNth w zs) :=
  (measurable_chainDensity hq hhm s₀ ts).comp
    (measurable_const.prodMk (measurable_insertNth j zs))

/-- Chapman–Kolmogorov for positive times. -/
def ChapmanKolmogorov (ν : Measure α) (q : ℝ → α → α → ℝ≥0∞) : Prop :=
  ∀ s u : ℝ, 0 < s → 0 < u → ∀ x y : α, ∫⁻ w, q s x w * q u w y ∂ν = q (s + u) x y

/-- Space-time harmonicity of the terminal weight on the time set `D`. -/
def IsSpaceTimeHarmonic (ν : Measure α) (q : ℝ → α → α → ℝ≥0∞) (h : ℝ → α → ℝ≥0∞)
    (D : Set ℝ) : Prop :=
  ∀ s₀ s : ℝ, s₀ < s → s ∈ D → ∀ x : α, ∫⁻ w, q (s - s₀) x w * h s w ∂ν = h s₀ x

variable {ν : Measure α} {D : Set ℝ}

theorem lintegral_chainDensity_insertNth_zero
    (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2)
    (hCK : ChapmanKolmogorov ν q) (hh : IsSpaceTimeHarmonic ν q h D)
    {k : ℕ} (s₀ : ℝ) (x₀ : α) (ts : Fin k → ℝ) (zs : Fin k → α) (s : ℝ)
    (hpos : s₀ < s) (hmono : StrictMono (Fin.cons s ts : Fin (k + 1) → ℝ)) (hs : s ∈ D) :
    ∫⁻ w, chainDensity q h s₀ x₀ (Fin.cons s ts) (Fin.cons w zs) ∂ν =
      chainDensity q h s₀ x₀ ts zs := by
  simp only [chainDensity_cons]
  cases k with
  | zero => simpa using hh s₀ s hpos hs x₀
  | succ k =>
    have hlt : s < ts 0 := by
      simpa using hmono (show (0 : Fin (k + 2)) < 1 from Fin.zero_lt_one)
    simp only [chainDensity_succ, ← mul_assoc]
    rw [lintegral_mul_const]
    · rw [hCK _ _ (sub_pos.2 hpos) (sub_pos.2 hlt)]
      congr 2
      ring
    · exact ((hq _).comp (measurable_const.prodMk measurable_id)).mul
        ((hq _).comp (measurable_id.prodMk measurable_const))

/-- **Integrating out one node of the chain** (Chapman–Kolmogorov / harmonicity step). -/
theorem lintegral_chainDensity_insertNth
    (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2) (hhm : ∀ s, Measurable (h s))
    (hCK : ChapmanKolmogorov ν q) (hh : IsSpaceTimeHarmonic ν q h D) :
    ∀ {k : ℕ} (s₀ : ℝ) (x₀ : α) (ts : Fin k → ℝ) (zs : Fin k → α) (j : Fin (k + 1)) (s : ℝ),
      (∀ i, s₀ < (j.insertNth s ts : Fin (k + 1) → ℝ) i) →
      StrictMono (j.insertNth s ts : Fin (k + 1) → ℝ) → s ∈ D →
      ∫⁻ w, chainDensity q h s₀ x₀ (j.insertNth s ts) (j.insertNth w zs) ∂ν =
        chainDensity q h s₀ x₀ ts zs
  | k, s₀, x₀, ts, zs, j, s, hpos, hmono, hs => by
    induction j using Fin.cases with
    | zero =>
      simp only [Fin.insertNth_zero'] at hpos hmono ⊢
      exact lintegral_chainDensity_insertNth_zero hq hCK hh s₀ x₀ ts zs s
        (by simpa using hpos 0) hmono hs
    | succ j =>
      cases k with
      | zero => exact j.elim0
      | succ k =>
        rw [← Fin.cons_self_tail ts, ← Fin.cons_self_tail zs] at *
        simp only [Fin.insertNth_succ_cons] at hpos hmono ⊢
        simp only [chainDensity_cons]
        rw [lintegral_const_mul]
        · congr 1
          refine lintegral_chainDensity_insertNth hq hhm hCK hh (ts 0) (zs 0) (Fin.tail ts)
            (Fin.tail zs) j s ?_ ?_ hs
          · intro i
            have := hmono (show (0 : Fin (k + 2)) < i.succ from Fin.succ_pos i)
            simpa using this
          · exact hmono.comp (Fin.strictMono_succ)
        · exact (measurable_chainDensity hq hhm _ _).comp
            (measurable_const.prodMk (measurable_insertNth j _))

end ChainDensity

variable [MeasurableSpace α]

/-!
### Finite-dimensional measures
-/

section FddMeasure

variable (ν : Measure α) (q : ℝ → α → α → ℝ≥0∞) (h : ℝ → α → ℝ≥0∞)

/-- The finite-dimensional measure of the chain at times `ts`: density `chainDensity` w.r.t.
`ν ⊗ ⋯ ⊗ ν`. -/
def chainFddMeasure (s₀ : ℝ) (x₀ : α) {k : ℕ} (ts : Fin k → ℝ) : Measure (Fin k → α) :=
  (Measure.pi fun _ : Fin k => ν).withDensity (chainDensity q h s₀ x₀ ts)

variable {ν q h} [SigmaFinite ν] {D : Set ℝ}

/-- Removing one time node: the marginal of the chain law along `succAbove j`. -/
theorem map_comp_succAbove_chainFddMeasure
    (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2) (hhm : ∀ s, Measurable (h s))
    (hCK : ChapmanKolmogorov ν q) (hh : IsSpaceTimeHarmonic ν q h D)
    (s₀ : ℝ) (x₀ : α) {n : ℕ} (ts : Fin (n + 1) → ℝ) (hpos : ∀ i, s₀ < ts i)
    (hmono : StrictMono ts) (j : Fin (n + 1)) (hD : ts j ∈ D) :
    (chainFddMeasure ν q h s₀ x₀ ts).map (fun zs => zs ∘ j.succAbove) =
      chainFddMeasure ν q h s₀ x₀ (ts ∘ j.succAbove) := by
  have hmeas : Measurable fun zs : Fin (n + 1) → α => zs ∘ j.succAbove :=
    Measurable.of_eval fun i => measurable_pi_apply _
  have hdens := measurable_chainDensity (h := h) hq hhm s₀ ts
  have hdens' : Measurable (chainDensity q h s₀ x₀ ts) :=
    hdens.comp (measurable_const.prodMk measurable_id)
  ext S hS
  rw [Measure.map_apply hmeas hS, chainFddMeasure, chainFddMeasure,
    withDensity_apply _ (hmeas hS), withDensity_apply _ hS,
    ← lintegral_indicator (hmeas hS), ← lintegral_indicator hS]
  have mp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) j).symm
  rw [← mp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  rw [lintegral_prod_symm]
  · refine lintegral_congr fun zs => ?_
    have hpre : ∀ w : α, (Fin.insertNth j w zs : Fin (n + 1) → α) ∈
        (fun zs : Fin (n + 1) → α => zs ∘ j.succAbove) ⁻¹' S ↔ zs ∈ S := by
      intro w
      simp only [mem_preimage]
      have : (Fin.insertNth j w zs : Fin (n + 1) → α) ∘ j.succAbove = zs := by
        funext i
        simp
      rw [this]
    have hfun : ∀ w : α, (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) j).symm
        (w, zs) = (Fin.insertNth j w zs : Fin (n + 1) → α) := fun w => rfl
    simp only [hfun]
    by_cases hzs : zs ∈ S
    · have hind : ∀ w : α, ((fun zs : Fin (n + 1) → α => zs ∘ j.succAbove) ⁻¹' S).indicator
          (chainDensity q h s₀ x₀ ts) (Fin.insertNth j w zs) =
            chainDensity q h s₀ x₀ ts (Fin.insertNth j w zs) := fun w =>
        indicator_of_mem ((hpre w).2 hzs) _
      simp only [hind, indicator_of_mem hzs]
      have hts : ts = (j.insertNth (ts j) (j.removeNth ts) : Fin (n + 1) → ℝ) :=
        (Fin.insertNth_self_removeNth j ts).symm
      have key := lintegral_chainDensity_insertNth hq hhm hCK hh s₀ x₀ (j.removeNth ts) zs j
        (ts j) (by rw [← hts]; exact hpos) (by rw [← hts]; exact hmono) hD
      rw [← hts] at key
      exact key
    · have hind : ∀ w : α, ((fun zs : Fin (n + 1) → α => zs ∘ j.succAbove) ⁻¹' S).indicator
          (chainDensity q h s₀ x₀ ts) (Fin.insertNth j w zs) = 0 := fun w =>
        indicator_of_notMem (fun h' => hzs ((hpre w).1 h')) _
      simp only [hind, indicator_of_notMem hzs, lintegral_zero]
  · refine (Measurable.indicator hdens' (hmeas hS)).comp_aemeasurable ?_
    exact (MeasurableEquiv.measurable _).aemeasurable

/-- **Consistency of the chain laws under every strictly increasing sub-selection of times.** -/
theorem map_comp_chainFddMeasure
    (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2) (hhm : ∀ s, Measurable (h s))
    (hCK : ChapmanKolmogorov ν q) (hh : IsSpaceTimeHarmonic ν q h D) (s₀ : ℝ) (x₀ : α) :
    ∀ {n : ℕ} (ts : Fin n → ℝ), (∀ i, s₀ < ts i) → StrictMono ts → (∀ i, ts i ∈ D) →
      ∀ {m : ℕ} (g : Fin m → Fin n), StrictMono g →
        (chainFddMeasure ν q h s₀ x₀ ts).map (fun zs => zs ∘ g) =
          chainFddMeasure ν q h s₀ x₀ (ts ∘ g)
  | 0, ts, _, _, _, m, g, _ => by
    cases m with
    | succ m => exact (g 0).elim0
    | zero =>
      have h1 : (fun zs : Fin 0 → α => zs ∘ g) = id := by
        funext zs i
        exact i.elim0
      have h2 : ts ∘ g = ts := Subsingleton.elim _ _
      rw [h1, Measure.map_id, h2]
  | n + 1, ts, hpos, hmono, hD, m, g, hg => by
    by_cases hsurj : ∃ j, ∀ i, g i ≠ j
    · obtain ⟨j, hj⟩ := hsurj
      have hex : ∀ i, ∃ z, j.succAbove z = g i := fun i => Fin.exists_succAbove_eq (hj i)
      choose g' hg' using hex
      have hgg : g = j.succAbove ∘ g' := funext fun i => (hg' i).symm
      have hg'mono : StrictMono g' := by
        intro a b hab
        have : g a < g b := hg hab
        rw [hgg] at this
        exact (Fin.strictMono_succAbove j).lt_iff_lt.1 this
      have hm1 : Measurable fun zs : Fin (n + 1) → α => zs ∘ j.succAbove :=
        Measurable.of_eval fun i => measurable_pi_apply _
      have hm2 : Measurable fun zs : Fin n → α => zs ∘ g' :=
        Measurable.of_eval fun i => measurable_pi_apply _
      have hcomp : (fun zs : Fin (n + 1) → α => zs ∘ g) =
          (fun zs : Fin n → α => zs ∘ g') ∘ (fun zs : Fin (n + 1) → α => zs ∘ j.succAbove) := by
        funext zs
        simp [hgg, Function.comp_assoc]
      rw [hcomp, ← Measure.map_map hm2 hm1,
        map_comp_succAbove_chainFddMeasure hq hhm hCK hh s₀ x₀ ts hpos hmono j (hD j),
        map_comp_chainFddMeasure hq hhm hCK hh s₀ x₀ (ts ∘ j.succAbove) (fun i => hpos _)
          (hmono.comp (Fin.strictMono_succAbove j)) (fun i => hD _) g' hg'mono, hgg]
      rfl
    · push Not at hsurj
      have hbij : Function.Bijective g := ⟨hg.injective, fun j => hsurj j⟩
      have hm : m = n + 1 := by
        simpa using Fintype.card_congr (Equiv.ofBijective g hbij)
      subst hm
      have hid : g = id := hg.eq_id
      subst hid
      have h1 : (fun zs : Fin (n + 1) → α => zs ∘ (id : Fin (n + 1) → Fin (n + 1))) = id := rfl
      rw [h1, Measure.map_id]
      rfl

/-- The total mass of the chain law is the terminal weight at the start. -/
theorem chainFddMeasure_univ
    (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2) (hhm : ∀ s, Measurable (h s))
    (hCK : ChapmanKolmogorov ν q) (hh : IsSpaceTimeHarmonic ν q h D) (s₀ : ℝ) (x₀ : α)
    {n : ℕ} (ts : Fin n → ℝ) (hpos : ∀ i, s₀ < ts i) (hmono : StrictMono ts)
    (hD : ∀ i, ts i ∈ D) :
    chainFddMeasure ν q h s₀ x₀ ts univ = h s₀ x₀ := by
  have hmap := map_comp_chainFddMeasure hq hhm hCK hh s₀ x₀ ts hpos hmono hD
    (Fin.elim0 : Fin 0 → Fin n) (fun a => a.elim0)
  have hm : Measurable fun zs : Fin n → α => zs ∘ (Fin.elim0 : Fin 0 → Fin n) :=
    Measurable.of_eval fun i => i.elim0
  have hu := congrArg (fun μ : Measure (Fin 0 → α) => μ univ) hmap
  simp only [Measure.map_apply hm MeasurableSet.univ, preimage_univ] at hu
  rw [hu, chainFddMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp

end FddMeasure

/-!
### The projective family indexed by finite sets of times
-/

section Family

variable (ν : Measure α) (q : ℝ → α → α → ℝ≥0∞) (h : ℝ → α → ℝ≥0∞)
variable {T : Type*} [LinearOrder T] (τ : T → ℝ)

/-- The chain law on `J → α` for a finite set `J` of (abstract, linearly ordered) times, with
real time map `τ`: the chain law at the increasing enumeration of `J`, reindexed by `J`. -/
def chainFamily (s₀ : ℝ) (x₀ : α) (J : Finset T) : Measure (J → α) :=
  (chainFddMeasure ν q h s₀ x₀ (fun i => τ (J.orderIsoOfFin rfl i))).map
    (fun zs j => zs ((J.orderIsoOfFin rfl).symm j))

variable {ν q h τ} [SigmaFinite ν] {D : Set ℝ}

theorem measurable_reindex {J : Finset T} :
    Measurable fun (zs : Fin J.card → α) (j : J) => zs ((J.orderIsoOfFin rfl).symm j) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- Marginal of the chain family on `J` along any strictly increasing `g : Fin m → T` with
values in `J`. -/
theorem map_chainFamily_eval
    (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2) (hhm : ∀ s, Measurable (h s))
    (hCK : ChapmanKolmogorov ν q) (hh : IsSpaceTimeHarmonic ν q h D)
    (hτ : StrictMono τ) (s₀ : ℝ) (hpos : ∀ i, s₀ < τ i) (hD : ∀ i, τ i ∈ D) (x₀ : α)
    (J : Finset T) {m : ℕ} (u : Fin m → T) (hu : StrictMono u) (huJ : ∀ i, u i ∈ J) :
    (chainFamily ν q h τ s₀ x₀ J).map (fun x i => x ⟨u i, huJ i⟩) =
      chainFddMeasure ν q h s₀ x₀ (τ ∘ u) := by
  let e := J.orderIsoOfFin rfl
  let g : Fin m → Fin J.card := fun i => e.symm ⟨u i, huJ i⟩
  have hg : StrictMono g := fun a b hab => e.symm.strictMono (hu hab)
  have hm : Measurable fun (x : J → α) (i : Fin m) => x ⟨u i, huJ i⟩ :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  rw [chainFamily, Measure.map_map hm measurable_reindex]
  have hcomp : ((fun (x : J → α) (i : Fin m) => x ⟨u i, huJ i⟩) ∘
      fun (zs : Fin J.card → α) (j : J) => zs (e.symm j)) = fun zs => zs ∘ g := rfl
  rw [hcomp, map_comp_chainFddMeasure hq hhm hCK hh s₀ x₀ _ (fun i => hpos _)
    (hτ.comp e.strictMono) (fun i => hD _) g hg]
  congr 1
  funext i
  simp only [Function.comp_apply, g, e, OrderIso.apply_symm_apply]

/-- **The chain family is projective.** -/
theorem isProjectiveMeasureFamily_chainFamily
    (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2) (hhm : ∀ s, Measurable (h s))
    (hCK : ChapmanKolmogorov ν q) (hh : IsSpaceTimeHarmonic ν q h D)
    (hτ : StrictMono τ) (s₀ : ℝ) (hpos : ∀ i, s₀ < τ i) (hD : ∀ i, τ i ∈ D) (x₀ : α) :
    IsProjectiveMeasureFamily (α := fun _ : T => α) (chainFamily ν q h τ s₀ x₀) := by
  intro I J hJI
  let eI := I.orderIsoOfFin rfl
  let eJ := J.orderIsoOfFin rfl
  let u : Fin J.card → T := fun i => (eJ i : T)
  have hu : StrictMono u := fun a b hab => eJ.strictMono hab
  have huI : ∀ i, u i ∈ I := fun i => hJI (eJ i).2
  have hres : Measurable (Finset.restrict₂ (π := fun _ : T => α) hJI) :=
    Finset.measurable_restrict₂ _
  have hrw : (Finset.restrict₂ (π := fun _ : T => α) hJI) =
      (fun (zs : Fin J.card → α) (j : J) => zs (eJ.symm j)) ∘
        (fun (x : I → α) (i : Fin J.card) => x ⟨u i, huI i⟩) := by
    funext x j
    simp [u]
  rw [hrw, ← Measure.map_map (g := fun (zs : Fin J.card → α) (j : J) => zs (eJ.symm j))
    (f := fun (x : I → α) (i : Fin J.card) => x ⟨u i, huI i⟩) measurable_reindex
    (Measurable.of_eval fun _ => measurable_pi_apply _),
    map_chainFamily_eval hq hhm hCK hh hτ s₀ hpos hD x₀ I u hu huI]
  rfl

/-- Every finite-dimensional measure of the chain family has total mass `h s₀ x₀`. -/
theorem chainFamily_univ
    (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2) (hhm : ∀ s, Measurable (h s))
    (hCK : ChapmanKolmogorov ν q) (hh : IsSpaceTimeHarmonic ν q h D)
    (hτ : StrictMono τ) (s₀ : ℝ) (hpos : ∀ i, s₀ < τ i) (hD : ∀ i, τ i ∈ D) (x₀ : α)
    (J : Finset T) :
    chainFamily ν q h τ s₀ x₀ J univ = h s₀ x₀ := by
  rw [chainFamily, Measure.map_apply measurable_reindex MeasurableSet.univ, preimage_univ]
  exact chainFddMeasure_univ hq hhm hCK hh s₀ x₀ _ (fun i => hpos _)
    (hτ.comp (J.orderIsoOfFin rfl).strictMono) (fun i => hD _)

/-- Finite-dimensional laws of any projective limit of a constant multiple `c •` of the chain
family, at arbitrary strictly increasing times `u : Fin m → T`. -/
theorem map_eval_of_isProjectiveLimit_smul_chainFamily
    (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2) (hhm : ∀ s, Measurable (h s))
    (hCK : ChapmanKolmogorov ν q) (hh : IsSpaceTimeHarmonic ν q h D)
    (hτ : StrictMono τ) (s₀ : ℝ) (hpos : ∀ i, s₀ < τ i) (hD : ∀ i, τ i ∈ D) (x₀ : α)
    (c : ℝ≥0∞) {μ : Measure (T → α)}
    (hμ : IsProjectiveLimit (α := fun _ : T => α) μ (fun J => c • chainFamily ν q h τ s₀ x₀ J))
    {m : ℕ} (u : Fin m → T) (hu : StrictMono u) :
    μ.map (fun x i => x (u i)) = c • chainFddMeasure ν q h s₀ x₀ (τ ∘ u) := by
  classical
  let J : Finset T := Finset.univ.image u
  have huJ : ∀ i, u i ∈ J := fun i => Finset.mem_image_of_mem u (Finset.mem_univ i)
  have hm : Measurable fun (x : J → α) (i : Fin m) => x ⟨u i, huJ i⟩ :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  have hcomp : (fun (x : T → α) (i : Fin m) => x (u i)) =
      (fun (x : J → α) (i : Fin m) => x ⟨u i, huJ i⟩) ∘ J.restrict := rfl
  rw [hcomp, ← Measure.map_map hm (Finset.measurable_restrict J), hμ J, Measure.map_smul,
    map_chainFamily_eval hq hhm hCK hh hτ s₀ hpos hD x₀ J u hu huJ]
  exact hm.aemeasurable

/-- Finite-dimensional laws of any projective limit of the chain family, at arbitrary strictly
increasing times `u : Fin m → T`. -/
theorem map_eval_of_isProjectiveLimit_chainFamily
    (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2) (hhm : ∀ s, Measurable (h s))
    (hCK : ChapmanKolmogorov ν q) (hh : IsSpaceTimeHarmonic ν q h D)
    (hτ : StrictMono τ) (s₀ : ℝ) (hpos : ∀ i, s₀ < τ i) (hD : ∀ i, τ i ∈ D) (x₀ : α)
    {μ : Measure (T → α)}
    (hμ : IsProjectiveLimit (α := fun _ : T => α) μ (chainFamily ν q h τ s₀ x₀))
    {m : ℕ} (u : Fin m → T) (hu : StrictMono u) :
    μ.map (fun x i => x (u i)) = chainFddMeasure ν q h s₀ x₀ (τ ∘ u) := by
  have := map_eval_of_isProjectiveLimit_smul_chainFamily hq hhm hCK hh hτ s₀ hpos hD x₀ 1
    (μ := μ) (by simpa using hμ) u hu
  simpa using this

end Family

/-!
### Bridges
-/

section Bridge

variable (ν : Measure α) (q : ℝ → α → α → ℝ≥0∞)

/-- **The finite-dimensional bridge density** of the kernel `q` from `z` to `e` of length `t` at
times `ts` and points `zs` (`t₀ = 0`, `z₀ = z`):
`q_{t₁}(z,z₁) q_{t₂-t₁}(z₁,z₂) ⋯ q_{t-t_k}(z_k,e) / q_t(z,e)`.  Same shape as
`bridgeFddDensity p` of the base diffusion with `q = ENNReal.ofReal ∘ p`. -/
def bridgeFddDensity (z e : α) (t : ℝ) {k : ℕ} (ts : Fin k → ℝ) (zs : Fin k → α) : ℝ≥0∞ :=
  (∏ i : Fin k, q (ts i - (Fin.cons 0 ts : Fin (k + 1) → ℝ) i.castSucc)
      ((Fin.cons z zs : Fin (k + 1) → α) i.castSucc) (zs i)) *
    q (t - (Fin.cons 0 ts : Fin (k + 1) → ℝ) (Fin.last k))
      ((Fin.cons z zs : Fin (k + 1) → α) (Fin.last k)) e /
    q t z e

/-- The bridge terminal weight `h s x = q (t - s) x e`. -/
def bridgeWeight (e : α) (t : ℝ) : ℝ → α → ℝ≥0∞ := fun s x => q (t - s) x e

omit [MeasurableSpace α] in
theorem bridgeFddDensity_eq (z e : α) (t : ℝ) {k : ℕ} (ts : Fin k → ℝ) (zs : Fin k → α) :
    bridgeFddDensity q z e t ts zs =
      (q t z e)⁻¹ * chainDensity q (bridgeWeight q e t) 0 z ts zs := by
  rw [chainDensity_eq_prod, bridgeFddDensity, div_eq_mul_inv, mul_comm]
  rfl

/-- The bridge fdd law at times `ts`: density `bridgeFddDensity` w.r.t. `ν ⊗ ⋯ ⊗ ν`. -/
def bridgeFddMeasure (z e : α) (t : ℝ) {k : ℕ} (ts : Fin k → ℝ) : Measure (Fin k → α) :=
  (Measure.pi fun _ : Fin k => ν).withDensity (bridgeFddDensity q z e t ts)

variable {ν q}

theorem measurable_bridgeWeight (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2)
    (e : α) (t s : ℝ) : Measurable (bridgeWeight q e t s) :=
  (hq _).comp (measurable_id.prodMk measurable_const)

theorem isSpaceTimeHarmonic_bridgeWeight (hCK : ChapmanKolmogorov ν q) (e : α) (t : ℝ) :
    IsSpaceTimeHarmonic ν q (bridgeWeight q e t) (Iio t) := by
  intro s₀ s hs hst x
  simp only [bridgeWeight]
  rw [hCK _ _ (sub_pos.2 hs) (sub_pos.2 hst)]
  congr 1
  ring

theorem bridgeFddMeasure_eq_smul (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2)
    (z e : α) (t : ℝ) {k : ℕ} (ts : Fin k → ℝ) :
    bridgeFddMeasure ν q z e t ts =
      (q t z e)⁻¹ • chainFddMeasure ν q (bridgeWeight q e t) 0 z ts := by
  rw [bridgeFddMeasure, chainFddMeasure, ← withDensity_smul]
  · congr 1
    funext zs
    rw [bridgeFddDensity_eq]
    rfl
  · exact (measurable_chainDensity hq (measurable_bridgeWeight hq e t) 0 ts).comp
      (measurable_const.prodMk measurable_id)

theorem measurable_bridgeFddDensity (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2)
    (z e : α) (t : ℝ) {k : ℕ} (ts : Fin k → ℝ) : Measurable (bridgeFddDensity q z e t ts) := by
  have : bridgeFddDensity q z e t ts =
      fun zs => (q t z e)⁻¹ * chainDensity q (bridgeWeight q e t) 0 z ts zs :=
    funext (bridgeFddDensity_eq q z e t ts)
  rw [this]
  exact ((measurable_chainDensity hq (measurable_bridgeWeight hq e t) 0 ts).comp
    (measurable_const.prodMk measurable_id)).const_mul _

/-- The bridge family on finite subsets of `Ioo 0 t`. -/
def bridgeFamily (ν : Measure α) (q : ℝ → α → α → ℝ≥0∞) (z e : α) (t : ℝ)
    (J : Finset (Ioo (0 : ℝ) t)) : Measure (J → α) :=
  (q t z e)⁻¹ • chainFamily ν q (bridgeWeight q e t) (Subtype.val) 0 z J

variable [SigmaFinite ν]

/-- **The bridge family is projective** (Chapman–Kolmogorov only; no Markov property). -/
theorem isProjectiveMeasureFamily_bridgeFamily
    (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2) (hCK : ChapmanKolmogorov ν q)
    (z e : α) (t : ℝ) :
    IsProjectiveMeasureFamily (α := fun _ : Ioo (0 : ℝ) t => α) (bridgeFamily ν q z e t) := by
  intro I J hJI
  have := isProjectiveMeasureFamily_chainFamily (ν := ν) (q := q) (D := Iio t)
    (τ := (Subtype.val : Ioo (0 : ℝ) t → ℝ)) hq (measurable_bridgeWeight hq e t) hCK
    (isSpaceTimeHarmonic_bridgeWeight hCK e t) (fun _ _ h => h) 0 (fun i => i.2.1)
    (fun i => i.2.2) z I J hJI
  rw [bridgeFamily, bridgeFamily, this, Measure.map_smul]
  exact (Finset.measurable_restrict₂ _).aemeasurable

/-- **The bridge fdd measures are probability measures** when `0 < q t z e < ∞`. -/
theorem isProbabilityMeasure_bridgeFamily
    (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2) (hCK : ChapmanKolmogorov ν q)
    (z e : α) {t : ℝ} (h0 : q t z e ≠ 0) (htop : q t z e ≠ ∞) (J : Finset (Ioo (0 : ℝ) t)) :
    IsProbabilityMeasure (bridgeFamily ν q z e t J) := by
  constructor
  rw [bridgeFamily, Measure.smul_apply, chainFamily_univ (D := Iio t)
    (τ := (Subtype.val : Ioo (0 : ℝ) t → ℝ)) hq
    (measurable_bridgeWeight hq e t) hCK (isSpaceTimeHarmonic_bridgeWeight hCK e t)
    (fun _ _ h => h) 0 (fun i => i.2.1) (fun i => i.2.2) z J]
  simp only [bridgeWeight, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 htop

/-- **Bridge fdd of a projective limit**: at all strictly increasing times
`0 < t₁ < ⋯ < t_k < t` (given as `u : Fin k → Ioo 0 t`), the law of the coordinates is the
bridge fdd measure. -/
theorem map_eval_of_isProjectiveLimit_bridgeFamily
    (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2) (hCK : ChapmanKolmogorov ν q)
    (z e : α) (t : ℝ) {μ : Measure (Ioo (0 : ℝ) t → α)}
    (hμ : IsProjectiveLimit (α := fun _ : Ioo (0 : ℝ) t => α) μ (bridgeFamily ν q z e t))
    {m : ℕ} (u : Fin m → Ioo (0 : ℝ) t) (hu : StrictMono u) :
    μ.map (fun x i => x (u i)) = bridgeFddMeasure ν q z e t (fun i => (u i : ℝ)) := by
  rw [map_eval_of_isProjectiveLimit_smul_chainFamily (D := Iio t)
    (τ := (Subtype.val : Ioo (0 : ℝ) t → ℝ)) hq
    (measurable_bridgeWeight hq e t) hCK (isSpaceTimeHarmonic_bridgeWeight hCK e t)
    (fun _ _ h => h) 0 (fun i => i.2.1) (fun i => i.2.2) z _ hμ u hu,
    bridgeFddMeasure_eq_smul hq]
  rfl

end Bridge

/-!
### Forward Markov chains
-/

section Markov

/-- Markov property of a transition density: total mass one at every positive time. -/
def IsMarkovDensity (ν : Measure α) (q : ℝ → α → α → ℝ≥0∞) : Prop :=
  ∀ s : ℝ, 0 < s → ∀ x : α, ∫⁻ y, q s x y ∂ν = 1

variable {ν : Measure α} {q : ℝ → α → α → ℝ≥0∞}

theorem isSpaceTimeHarmonic_one (hM : IsMarkovDensity ν q) :
    IsSpaceTimeHarmonic ν q (fun _ _ => 1) univ := by
  intro s₀ s hs _ x
  simpa using hM (s - s₀) (sub_pos.2 hs) x

/-- The forward Markov family started at `z` at time `0`, on finite sets of positive times. -/
def markovFamily (ν : Measure α) (q : ℝ → α → α → ℝ≥0∞) (z : α)
    (J : Finset (Ioi (0 : ℝ))) : Measure (J → α) :=
  chainFamily ν q (fun _ _ => 1) Subtype.val 0 z J

variable [SigmaFinite ν]

/-- **The forward Markov family is projective** (Chapman–Kolmogorov and the Markov property). -/
theorem isProjectiveMeasureFamily_markovFamily
    (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2) (hCK : ChapmanKolmogorov ν q)
    (hM : IsMarkovDensity ν q) (z : α) :
    IsProjectiveMeasureFamily (α := fun _ : Ioi (0 : ℝ) => α) (markovFamily ν q z) :=
  isProjectiveMeasureFamily_chainFamily (τ := (Subtype.val : Ioi (0 : ℝ) → ℝ)) hq
    (fun _ => measurable_const) hCK (isSpaceTimeHarmonic_one hM) (fun _ _ h => h) 0
    (fun i => i.2) (fun _ => mem_univ _) z

/-- The forward Markov fdd measures are probability measures. -/
theorem isProbabilityMeasure_markovFamily
    (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2) (hCK : ChapmanKolmogorov ν q)
    (hM : IsMarkovDensity ν q) (z : α) (J : Finset (Ioi (0 : ℝ))) :
    IsProbabilityMeasure (markovFamily ν q z J) :=
  ⟨chainFamily_univ (τ := (Subtype.val : Ioi (0 : ℝ) → ℝ)) hq (fun _ => measurable_const) hCK
    (isSpaceTimeHarmonic_one hM) (fun _ _ h => h) 0 (fun i => i.2) (fun _ => mem_univ _) z J⟩

/-- Fdd of a projective limit of the forward Markov family at increasing positive times: density
`∏ q (t_i - t_{i-1}) z_{i-1} z_i` (`t₀ = 0`, `z₀ = z`) w.r.t. `ν ⊗ ⋯ ⊗ ν`. -/
theorem map_eval_of_isProjectiveLimit_markovFamily
    (hq : ∀ s, Measurable fun p : α × α => q s p.1 p.2) (hCK : ChapmanKolmogorov ν q)
    (hM : IsMarkovDensity ν q) (z : α) {μ : Measure (Ioi (0 : ℝ) → α)}
    (hμ : IsProjectiveLimit (α := fun _ : Ioi (0 : ℝ) => α) μ (markovFamily ν q z))
    {m : ℕ} (u : Fin m → Ioi (0 : ℝ)) (hu : StrictMono u) :
    μ.map (fun x i => x (u i)) =
      chainFddMeasure ν q (fun _ _ => 1) 0 z (fun i => (u i : ℝ)) :=
  map_eval_of_isProjectiveLimit_chainFamily (τ := (Subtype.val : Ioi (0 : ℝ) → ℝ)) hq
    (fun _ => measurable_const) hCK (isSpaceTimeHarmonic_one hM) (fun _ _ h => h) 0
    (fun i => i.2) (fun _ => mem_univ _) z hμ u hu

end Markov

end BlockBand.Diffusion
