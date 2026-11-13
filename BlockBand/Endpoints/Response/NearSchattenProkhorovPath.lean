module

public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Continuous extension of dyadic grid paths (deterministic part of the Prokhorov realization)

The realization is built on the countable product `ι × ℕ × ℕ → ℂ` of word values at the dyadic
grid times `nspTime t₀ k j = t₀ + k / 2^j`. A grid path `y : ℕ × ℕ → ℂ` is *good*
(`NspGridGood`) if it is uniformly continuous on the grid points of every `[t₀, t₀ + N]`
(`NspGridOsc` is the oscillation event). For good paths:

* `nsp_tendsto_ext`: along the dyadic lower approximations `nspIdx t₀ t j = ⌊2^j (t - t₀)⌋₊`
  the grid values converge, to `nspExt t₀ y t`;
* `nsp_ext_modulus`: the grid modulus passes to `nspExt`;
* `nsp_continuousOn_ext`: `nspExt t₀ y` is continuous on `[t₀, ∞)`.

`nspZ t₀ i t` is a measurable version of `x ↦ nspExt t₀ (x (i, ·)) t` on the product space
(`nsp_measurable_nspZ`), equal to it on good paths for `t ≥ t₀` (`nsp_nspZ_eq`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set

/-- Dyadic grid time `t₀ + k / 2^j`. -/
def nspTime (t₀ : ℝ) (k j : ℕ) : ℝ := t₀ + (k : ℝ) / 2 ^ j

/-- Dyadic lower index of `t` at level `j`: `⌊2^j (t - t₀)⌋₊`. -/
def nspIdx (t₀ t : ℝ) (j : ℕ) : ℕ := ⌊(2 : ℝ) ^ j * (t - t₀)⌋₊

theorem nsp_le_time (t₀ : ℝ) (k j : ℕ) : t₀ ≤ nspTime t₀ k j := by
  unfold nspTime; have : (0 : ℝ) ≤ (k : ℝ) / 2 ^ j := by positivity
  linarith

theorem nsp_time_idx_le {t₀ t : ℝ} (ht : t₀ ≤ t) (j : ℕ) : nspTime t₀ (nspIdx t₀ t j) j ≤ t := by
  unfold nspTime nspIdx
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have hfl : (⌊(2 : ℝ) ^ j * (t - t₀)⌋₊ : ℝ) ≤ 2 ^ j * (t - t₀) :=
    Nat.floor_le (mul_nonneg h2.le (sub_nonneg.2 ht))
  have : (⌊(2 : ℝ) ^ j * (t - t₀)⌋₊ : ℝ) / 2 ^ j ≤ t - t₀ := by
    rw [div_le_iff₀ h2]; linarith
  linarith

theorem nsp_sub_lt_time_idx (t₀ t : ℝ) (j : ℕ) :
    t - (1 / 2) ^ j < nspTime t₀ (nspIdx t₀ t j) j := by
  unfold nspTime nspIdx
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have hfl : 2 ^ j * (t - t₀) < (⌊(2 : ℝ) ^ j * (t - t₀)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have e : t - (1 / 2 : ℝ) ^ j - t₀ = (2 ^ j * (t - t₀) - 1) / 2 ^ j := by
    rw [one_div_pow]; field_simp; ring
  have : t - (1 / 2 : ℝ) ^ j - t₀ < (⌊(2 : ℝ) ^ j * (t - t₀)⌋₊ : ℝ) / 2 ^ j := by
    rw [e]; exact div_lt_div_of_pos_right (by linarith) h2
  linarith

/-- Eventually `(1/2)^j < c`, for `c > 0`. -/
theorem nsp_eventually_half_pow_lt {c : ℝ} (hc : 0 < c) : ∀ᶠ j : ℕ in atTop, (1 / 2 : ℝ) ^ j < c := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc (by norm_num : (1 / 2 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop n] with j hj
  exact lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj) hn

/-- The grid oscillation event of a grid path `y` on `[t₀, t₀ + N]`: two grid times within `δ`
with values more than `η` apart. -/
def NspGridOsc (t₀ : ℝ) (y : ℕ × ℕ → ℂ) (N : ℕ) (η δ : ℝ) : Prop :=
  ∃ k j k' j' : ℕ, nspTime t₀ k j ≤ t₀ + N ∧ nspTime t₀ k' j' ≤ t₀ + N ∧
    |nspTime t₀ k j - nspTime t₀ k' j'| ≤ δ ∧ η < ‖y (k, j) - y (k', j')‖

/-- A good grid path: uniformly continuous on the grid points of each `[t₀, t₀ + N]`. -/
def NspGridGood (t₀ : ℝ) (y : ℕ × ℕ → ℂ) : Prop :=
  ∀ N k : ℕ, ∃ j : ℕ, ¬ NspGridOsc t₀ y N (1 / ((k : ℝ) + 1)) (1 / ((j : ℝ) + 1))

theorem nsp_not_osc {t₀ : ℝ} {y : ℕ × ℕ → ℂ} {N : ℕ} {η δ : ℝ} (h : ¬ NspGridOsc t₀ y N η δ)
    {k j k' j' : ℕ} (h₁ : nspTime t₀ k j ≤ t₀ + N) (h₂ : nspTime t₀ k' j' ≤ t₀ + N)
    (h₃ : |nspTime t₀ k j - nspTime t₀ k' j'| ≤ δ) : ‖y (k, j) - y (k', j')‖ ≤ η :=
  not_lt.1 fun h₄ => h ⟨k, j, k', j', h₁, h₂, h₃, h₄⟩

/-- The extension of a grid path: limit along the dyadic lower approximations. -/
def nspExt (t₀ : ℝ) (y : ℕ × ℕ → ℂ) (t : ℝ) : ℂ :=
  limUnder atTop fun j => y (nspIdx t₀ t j, j)

/-- Two dyadic approximations of times `t, t' ≥ t₀` at levels `j, j'` are within
`|t - t'| + (1/2)^min`. -/
theorem nsp_abs_time_sub_lt {t₀ t t' : ℝ} (ht : t₀ ≤ t) (ht' : t₀ ≤ t') (j j' : ℕ) {c : ℝ}
    (hj : (1 / 2 : ℝ) ^ j ≤ c) (hj' : (1 / 2 : ℝ) ^ j' ≤ c) :
    |nspTime t₀ (nspIdx t₀ t j) j - nspTime t₀ (nspIdx t₀ t' j') j'| < |t - t'| + c := by
  have a1 := nsp_time_idx_le ht j
  have a2 := nsp_sub_lt_time_idx t₀ t j
  have a3 := nsp_time_idx_le ht' j'
  have a4 := nsp_sub_lt_time_idx t₀ t' j'
  have b1 := le_abs_self (t - t')
  have b2 := neg_abs_le (t - t')
  rw [abs_lt]; constructor <;> linarith

theorem nsp_tendsto_ext {t₀ : ℝ} {y : ℕ × ℕ → ℂ} (hy : NspGridGood t₀ y) {t : ℝ} (ht : t₀ ≤ t) :
    Tendsto (fun j => y (nspIdx t₀ t j, j)) atTop (𝓝 (nspExt t₀ y t)) := by
  have hC : CauchySeq fun j => y (nspIdx t₀ t j, j) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨j₀, hj₀⟩ := hy ⌈t - t₀⌉₊ k
    have hN : t ≤ t₀ + (⌈t - t₀⌉₊ : ℝ) := by linarith [Nat.le_ceil (t - t₀)]
    have hpos : (0 : ℝ) < 1 / ((j₀ : ℝ) + 1) := by positivity
    obtain ⟨J, hJ⟩ := (nsp_eventually_half_pow_lt hpos).exists_forall_of_atTop
    refine ⟨J, fun j hj => ?_⟩
    have hle : ∀ i, J ≤ i → (1 / 2 : ℝ) ^ i ≤ (1 / 2) ^ J := fun i hi =>
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hi
    have h3 := nsp_abs_time_sub_lt ht ht j J (hle j hj) le_rfl
    rw [sub_self, abs_zero, zero_add] at h3
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (nsp_not_osc hj₀ ((nsp_time_idx_le ht j).trans hN)
      ((nsp_time_idx_le ht J).trans hN) (h3.trans (hJ J le_rfl)).le) hk
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hC
  exact tendsto_nhds_limUnder ⟨c, hc⟩

/-- The grid modulus passes to the extension. -/
theorem nsp_ext_modulus {t₀ : ℝ} {y : ℕ × ℕ → ℂ} (hy : NspGridGood t₀ y) {N : ℕ} {η δ : ℝ}
    (h : ¬ NspGridOsc t₀ y N η δ) {t t' : ℝ} (ht : t₀ ≤ t) (ht' : t₀ ≤ t')
    (htN : t ≤ t₀ + N) (ht'N : t' ≤ t₀ + N) (htt' : |t - t'| < δ) :
    ‖nspExt t₀ y t - nspExt t₀ y t'‖ ≤ η := by
  have hlim := ((nsp_tendsto_ext hy ht).sub (nsp_tendsto_ext hy ht')).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [nsp_eventually_half_pow_lt (sub_pos.2 htt')] with j hj
  have h3 := nsp_abs_time_sub_lt ht ht' j j hj.le hj.le
  exact nsp_not_osc h ((nsp_time_idx_le ht j).trans htN) ((nsp_time_idx_le ht' j).trans ht'N)
    (by linarith)

theorem nsp_continuousOn_ext {t₀ : ℝ} {y : ℕ × ℕ → ℂ} (hy : NspGridGood t₀ y) :
    ContinuousOn (nspExt t₀ y) (Ici t₀) := by
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨j₀, hj₀⟩ := hy (⌈t - t₀⌉₊ + 1) k
  refine ⟨min 1 (1 / ((j₀ : ℝ) + 1)), by positivity, fun t' ht' hd => ?_⟩
  rw [Real.dist_eq] at hd
  have hd1 := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 := lt_of_lt_of_le hd (min_le_right _ _)
  have hc := Nat.le_ceil (t - t₀)
  have hN : ((⌈t - t₀⌉₊ + 1 : ℕ) : ℝ) = (⌈t - t₀⌉₊ : ℝ) + 1 := by push_cast; ring
  have h1 : t' ≤ t₀ + ((⌈t - t₀⌉₊ + 1 : ℕ) : ℝ) := by
    rw [hN]; have := le_abs_self (t' - t); linarith
  have h2 : t ≤ t₀ + ((⌈t - t₀⌉₊ + 1 : ℕ) : ℝ) := by rw [hN]; linarith
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (nsp_ext_modulus hy hj₀ ht' ht h1 h2 hd2) hk

/-!
## The measurable version on the product space
-/

/-- The measurable version of `x ↦ nspExt t₀ (x (i, ·)) t`: the limit along the dyadic lower
approximations where it exists, `0` elsewhere. -/
def nspZ (t₀ : ℝ) {ι : Type*} (i : ι) (t : ℝ) (x : ι × ℕ × ℕ → ℂ) : ℂ :=
  open Classical in
  if ∃ c, Tendsto (fun j => x (i, nspIdx t₀ t j, j)) atTop (𝓝 c) then
    nspExt t₀ (fun p => x (i, p)) t else 0

theorem nsp_measurable_nspZ (t₀ : ℝ) {ι : Type*} [Countable ι] (i : ι) (t : ℝ) :
    Measurable (nspZ t₀ i t) := by
  classical
  let S : Set (ι × ℕ × ℕ → ℂ) :=
    {x | ∃ c, Tendsto (fun j => x (i, nspIdx t₀ t j, j)) atTop (𝓝 c)}
  have hS : MeasurableSet S := measurableSet_exists_tendsto (l := atTop)
    (f := fun j (x : ι × ℕ × ℕ → ℂ) => x (i, nspIdx t₀ t j, j))
    fun j => measurable_pi_apply _
  let f : ℕ → (ι × ℕ × ℕ → ℂ) → ℂ := fun j x => if x ∈ S then x (i, nspIdx t₀ t j, j) else 0
  have hf : ∀ j, Measurable (f j) := fun j =>
    Measurable.ite hS (measurable_pi_apply _) measurable_const
  refine measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.2 fun x => ?_)
  by_cases hx : x ∈ S
  · have hx' : ∃ c, Tendsto (fun j => x (i, nspIdx t₀ t j, j)) atTop (𝓝 c) := hx
    simp only [f, nspZ, hx, hx', ↓reduceIte]
    exact tendsto_nhds_limUnder hx'
  · have hx' : ¬ ∃ c, Tendsto (fun j => x (i, nspIdx t₀ t j, j)) atTop (𝓝 c) := hx
    simp only [f, nspZ, hx, hx', ↓reduceIte]
    exact tendsto_const_nhds

theorem nsp_nspZ_eq {t₀ : ℝ} {ι : Type*} {i : ι} {x : ι × ℕ × ℕ → ℂ}
    (hx : NspGridGood t₀ fun p => x (i, p)) {t : ℝ} (ht : t₀ ≤ t) :
    nspZ t₀ i t x = nspExt t₀ (fun p => x (i, p)) t := by
  have h : ∃ c, Tendsto (fun j => x (i, nspIdx t₀ t j, j)) atTop (𝓝 c) :=
    ⟨_, nsp_tendsto_ext hx ht⟩
  unfold nspZ
  simp only [h, ↓reduceIte]

theorem nsp_continuousOn_nspZ {t₀ : ℝ} {ι : Type*} {i : ι} {x : ι × ℕ × ℕ → ℂ}
    (hx : NspGridGood t₀ fun p => x (i, p)) :
    ContinuousOn (fun t => nspZ t₀ i t x) (Ici t₀) :=
  (nsp_continuousOn_ext hx).congr fun _ ht => nsp_nspZ_eq hx ht

theorem nsp_tendsto_nspZ {t₀ : ℝ} {ι : Type*} {i : ι} {x : ι × ℕ × ℕ → ℂ}
    (hx : NspGridGood t₀ fun p => x (i, p)) {t : ℝ} (ht : t₀ ≤ t) :
    Tendsto (fun j => x (i, nspIdx t₀ t j, j)) atTop (𝓝 (nspZ t₀ i t x)) := by
  rw [nsp_nspZ_eq hx ht]; exact nsp_tendsto_ext hx ht

end BlockBand.Endpoints
