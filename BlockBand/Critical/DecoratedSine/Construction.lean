module

public import BlockBand.Endpoints.VagueMeasurability
public import BlockBand.Critical.DecoratedSine.Windows

/-!
# The decorated point measure `Σ δ_{(x_{n,j}, m(n,j))}`

Given a locally finite point measure `ξ` on `ℝ`, with points `x_{n,j}` enumerated by unit window
`n` and rank `j`, and marks `m : ℤ × ℕ → Y`, `decoratedPoint ξ m` is the point measure
`Σ_{n, j < N_n} δ_{(x_{n,j}, m(n,j))}` on `ℝ × Y`. Its ground process is `ξ`, integrals of tests
supported in `|x| ≤ R` are finite sums, and `(ξ, m) ↦ decoratedPoint ξ m` is measurable.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.DecoratedSine

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

/-!
## Integration against a countable sum of Dirac masses
-/

/-- Integral against `Σ_{p : c p} δ_{y p}` is the finite sum over any finset `T` of indices with
`c p` outside of which `g ∘ y` vanishes on `{c}`. -/
theorem integral_sum_ite_dirac {X ι : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [Countable ι] (c : ι → Prop) [DecidablePred c] (y : ι → X) (g : X → ℝ)
    (hg : Integrable g (Measure.sum fun p => if c p then Measure.dirac (y p) else 0))
    (T : Finset ι) (hT : ∀ p ∈ T, c p) (hout : ∀ p, c p → p ∉ T → g (y p) = 0) :
    ∫ x, g x ∂(Measure.sum fun p => if c p then Measure.dirac (y p) else 0) =
      ∑ p ∈ T, g (y p) := by
  rw [integral_sum_measure hg]
  have hterm : ∀ p, ∫ x, g x ∂(if c p then Measure.dirac (y p) else 0) =
      if c p then g (y p) else 0 := by
    intro p
    by_cases hp : c p
    · rw [ite_eq_left hp, ite_eq_left hp, integral_dirac]
    · rw [ite_eq_right hp, ite_eq_right hp, integral_zero_measure]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := T)]
  · exact Finset.sum_congr rfl fun p hp => ite_eq_left (hT p hp)
  · intro p hp
    by_cases hc : c p
    · rw [ite_eq_left hc, hout p hc hp]
    · rw [ite_eq_right hc]

/-- A countable sum of Dirac masses is `ℕ ∪ {∞}`-valued. -/
theorem sum_ite_dirac_integer {X ι : Type*} [MeasurableSpace X] (c : ι → Prop) [DecidablePred c]
    (y : ι → X) {A : Set X} (hA : MeasurableSet A) :
    (Measure.sum fun p => if c p then Measure.dirac (y p) else 0) A = ∞ ∨
      ∃ n : ℕ, (Measure.sum fun p => if c p then Measure.dirac (y p) else 0) A = n := by
  set S : Set ι := {p | c p ∧ y p ∈ A}
  have hterm : ∀ p, (if c p then Measure.dirac (y p) else 0) A = S.indicator 1 p := by
    intro p
    by_cases hp : c p
    · rw [ite_eq_left hp, Measure.dirac_apply' _ hA]
      by_cases hy : y p ∈ A
      · rw [indicator_of_mem hy, indicator_of_mem (show p ∈ S from ⟨hp, hy⟩)]
        rfl
      · rw [indicator_of_notMem hy, indicator_of_notMem (show p ∉ S from fun h => hy h.2)]
    · rw [ite_eq_right hp, indicator_of_notMem (show p ∉ S from fun h => hp h.1)]
      rfl
  have hsum : (Measure.sum fun p => if c p then Measure.dirac (y p) else 0) A = S.encard := by
    rw [Measure.sum_apply _ hA]
    simp_rw [hterm]
    rw [← tsum_subtype S (1 : ι → ℝ≥0∞)]
    exact ENNReal.tsum_set_one S
  rw [hsum]
  by_cases h : S.encard = ⊤
  · left
    rw [h]
    rfl
  · right
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    exact ⟨n, by rw [← hn]; rfl⟩

/-!
## A generic constructor for locally finite integer-valued measures
-/

/-- The `VaguePointMeasure` carried by a measure that is finite on compacts and
`ℕ ∪ {∞}`-valued (counts are the values on relatively compact sets). -/
def vaguePointMeasureOfMeasure {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (hfin : ∀ K : Set X, IsCompact K → μ K < ∞)
    (hint : ∀ A : Set X, MeasurableSet A → μ A = ∞ ∨ ∃ n : ℕ, μ A = n) :
    VaguePointMeasure X where
  measure := μ
  finite_on_compact := hfin
  integer_valued := hint
  count A := ⌊(μ A.carrier).toReal⌋₊
  measure_eq_count A := by
    have hlt : μ A.carrier < ∞ :=
      lt_of_le_of_lt (measure_mono subset_closure) (hfin _ A.compact_closure)
    rcases hint _ A.measurable with h | ⟨k, hk⟩
    · exact absurd h hlt.ne
    · rw [hk, ENNReal.toReal_natCast, Nat.floor_natCast]

/-!
## The decorated point measure
-/

variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]

/-- The Dirac mass at the `j`-th point of window `n` decorated with the mark `m (n, j)`. -/
def decoratedAtom (ξ : VaguePointMeasure ℝ) (m : ℤ × ℕ → Y) (p : ℤ × ℕ) : Measure (ℝ × Y) :=
  if p.2 < windowCount ξ p.1 then Measure.dirac (windowAtom ξ p.1 p.2, m p) else 0

/-- `Σ_{n, j < N_n} δ_{(x_{n,j}, m(n,j))}`. -/
def decoratedMeasure (ξ : VaguePointMeasure ℝ) (m : ℤ × ℕ → Y) : Measure (ℝ × Y) :=
  Measure.sum (decoratedAtom ξ m)

omit [TopologicalSpace Y] in
theorem map_fst_decoratedMeasure (ξ : VaguePointMeasure ℝ) (m : ℤ × ℕ → Y) :
    (decoratedMeasure ξ m).map Prod.fst = ξ.measure := by
  rw [decoratedMeasure, Measure.map_sum measurable_fst.aemeasurable,
    measure_eq_sum_groundAtom ξ]
  congr 1
  funext p
  simp only [decoratedAtom, groundAtom]
  split_ifs
  · exact Measure.map_dirac' measurable_fst _
  · exact Measure.map_zero _

omit [TopologicalSpace Y] in
theorem decoratedMeasure_prod_univ (ξ : VaguePointMeasure ℝ) (m : ℤ × ℕ → Y) {A : Set ℝ}
    (hA : MeasurableSet A) : decoratedMeasure ξ m (A ×ˢ univ) = ξ.measure A := by
  rw [← map_fst_decoratedMeasure ξ m, Measure.map_apply measurable_fst hA, prod_univ]

theorem decoratedMeasure_lt_top (ξ : VaguePointMeasure ℝ) (m : ℤ × ℕ → Y) (K : Set (ℝ × Y))
    (hK : IsCompact K) : decoratedMeasure ξ m K < ∞ := by
  have hK1 : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  calc decoratedMeasure ξ m K ≤ decoratedMeasure ξ m ((Prod.fst '' K) ×ˢ univ) :=
        measure_mono fun z hz => ⟨mem_image_of_mem _ hz, mem_univ _⟩
    _ = ξ.measure (Prod.fst '' K) := decoratedMeasure_prod_univ ξ m hK1.isClosed.measurableSet
    _ < ∞ := ξ.finite_on_compact _ hK1

/-- The decorated point measure `Σ_{n, j < N_n} δ_{(x_{n,j}, m(n,j))}` in the vague
state space on `ℝ × Y`. -/
def decoratedPoint (ξ : VaguePointMeasure ℝ) (m : ℤ × ℕ → Y) : VaguePointMeasure (ℝ × Y) :=
  vaguePointMeasureOfMeasure (decoratedMeasure ξ m) (decoratedMeasure_lt_top ξ m)
    (fun _ hA => sum_ite_dirac_integer _ _ hA)

theorem decoratedPoint_measure (ξ : VaguePointMeasure ℝ) (m : ℤ × ℕ → Y) :
    (decoratedPoint ξ m).measure = decoratedMeasure ξ m :=
  rfl

/-- The ground process of the decoration is `ξ`. -/
theorem decoratedPoint_measure_prod_univ (ξ : VaguePointMeasure ℝ) (m : ℤ × ℕ → Y) {A : Set ℝ}
    (hA : MeasurableSet A) : (decoratedPoint ξ m).measure (A ×ˢ univ) = ξ.measure A :=
  decoratedMeasure_prod_univ ξ m hA

/-!
## Finite index sets of the points in a bounded region
-/

/-- The windows `[n, n+1)` meeting `[-R, R]` (a superset). -/
def coveringWindows (R : ℝ) : Finset ℤ :=
  Finset.Icc (-(⌈R⌉₊ : ℤ) - 1) (⌈R⌉₊ : ℤ)

theorem lt_abs_of_notMem_coveringWindows {R : ℝ} {n : ℤ} (hn : n ∉ coveringWindows R) {x : ℝ}
    (hx : x ∈ window n) : R < |x| := by
  simp only [coveringWindows, Finset.mem_Icc, not_and_or, not_le] at hn
  have hc : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
  obtain ⟨hx1, hx2⟩ := hx
  rcases hn with h | h
  · have h' : (n : ℝ) + 1 ≤ -(⌈R⌉₊ : ℝ) - 1 := by
      have : n + 1 ≤ -(⌈R⌉₊ : ℤ) - 1 := by omega
      exact_mod_cast this
    rw [abs_of_neg (by linarith)]
    linarith
  · have h' : (⌈R⌉₊ : ℝ) + 1 ≤ (n : ℝ) := by
      have : (⌈R⌉₊ : ℤ) + 1 ≤ n := by omega
      exact_mod_cast this
    rw [abs_of_pos (by linarith)]
    linarith

/-- Indices `(n, j)` of the points of `ξ` in the covering windows of `[-R, R]`. -/
def atomIndex (ξ : VaguePointMeasure ℝ) (R : ℝ) : Finset (ℤ × ℕ) :=
  (coveringWindows R ×ˢ Finset.range ((coveringWindows R).sup (windowCount ξ) + 1)).filter
    fun p => p.2 < windowCount ξ p.1

theorem mem_atomIndex {ξ : VaguePointMeasure ℝ} {R : ℝ} {p : ℤ × ℕ} :
    p ∈ atomIndex ξ R ↔ p.1 ∈ coveringWindows R ∧ p.2 < windowCount ξ p.1 := by
  simp only [atomIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    have := Finset.le_sup (f := windowCount ξ) h1
    exact ⟨⟨h1, by omega⟩, h3⟩

theorem lt_abs_windowAtom_of_notMem {ξ : VaguePointMeasure ℝ} {R : ℝ} {p : ℤ × ℕ}
    (hp : p.2 < windowCount ξ p.1) (hT : p ∉ atomIndex ξ R) :
    R < |windowAtom ξ p.1 p.2| := by
  refine lt_abs_of_notMem_coveringWindows (fun h => hT (mem_atomIndex.mpr ⟨h, hp⟩)) ?_
  exact windowAtom_mem ξ p.1 hp

/-- Integral of a test vanishing for `|x| > R` against the ground measure. -/
theorem integral_ground_eq_sum (ξ : VaguePointMeasure ℝ) (h : ℝ → ℝ)
    (hint : Integrable h ξ.measure) (R : ℝ) (hR : ∀ x, R < |x| → h x = 0) :
    ∫ x, h x ∂ξ.measure = ∑ p ∈ atomIndex ξ R, h (windowAtom ξ p.1 p.2) := by
  have he := measure_eq_sum_groundAtom ξ
  rw [he] at hint ⊢
  exact integral_sum_ite_dirac (fun p : ℤ × ℕ => p.2 < windowCount ξ p.1)
    (fun p => windowAtom ξ p.1 p.2) h hint _ (fun _p hp => (mem_atomIndex.mp hp).2)
    (fun _p hp hT => hR _ (lt_abs_windowAtom_of_notMem hp hT))

variable [MeasurableSingletonClass Y]

omit [TopologicalSpace Y] in
/-- Integral of a test vanishing for `|x| > R` against the decorated measure. -/
theorem integral_decorated_eq_sum (ξ : VaguePointMeasure ℝ) (m : ℤ × ℕ → Y) (f : ℝ × Y → ℝ)
    (hint : Integrable f (decoratedMeasure ξ m)) (R : ℝ) (hR : ∀ z : ℝ × Y, R < |z.1| → f z = 0) :
    ∫ z, f z ∂decoratedMeasure ξ m = ∑ p ∈ atomIndex ξ R, f (windowAtom ξ p.1 p.2, m p) :=
  integral_sum_ite_dirac (fun p : ℤ × ℕ => p.2 < windowCount ξ p.1)
    (fun p => (windowAtom ξ p.1 p.2, m p)) f hint _ (fun _p hp => (mem_atomIndex.mp hp).2)
    (fun _p hp hT => hR _ (lt_abs_windowAtom_of_notMem hp hT))

/-!
## Measurability of the decoration map
-/

variable [BorelSpace Y] [T2Space Y] [SecondCountableTopology Y] [LocallyCompactSpace Y]

theorem measurable_decoratedPoint :
    Measurable fun ω : VaguePointMeasure ℝ × (ℤ × ℕ → Y) => decoratedPoint ω.1 ω.2 := by
  refine BlockBand.Endpoints.measurable_to_vaguePointMeasure fun g hg => ?_
  have hfun : (fun ω : VaguePointMeasure ℝ × (ℤ × ℕ → Y) => (decoratedPoint ω.1 ω.2).coordinate g) =
      fun ω => (∑' p : ℤ × ℕ, if p.2 < windowCount ω.1 p.1 then
        ENNReal.ofReal (g (windowAtom ω.1 p.1 p.2, ω.2 p)) else 0).toReal := by
    funext ω
    rw [VaguePointMeasure.coordinate, decoratedPoint_measure,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg)
        g.continuous.aestronglyMeasurable, decoratedMeasure, lintegral_sum_measure]
    congr 1
    refine tsum_congr fun p => ?_
    simp only [decoratedAtom]
    split_ifs
    · exact lintegral_dirac _ _
    · exact lintegral_zero_measure _
  rw [hfun]
  refine Measurable.ennreal_toReal (Measurable.tsum fun p => ?_)
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurable_fst (measurableSet_lt_windowCount p.1 p.2)
  · exact ENNReal.measurable_ofReal.comp (g.continuous.measurable.comp
      (((measurable_windowAtom p.1 p.2).comp measurable_fst).prodMk
        ((measurable_pi_apply p).comp measurable_snd)))

end BlockBand.Critical.DecoratedSine
