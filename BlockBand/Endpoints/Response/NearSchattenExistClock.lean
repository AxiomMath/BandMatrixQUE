module

public import BlockBand.Endpoints.Response.NearSchattenExistHausdorff
public import BlockBand.Endpoints.Response.NearSchattenDefs

/-!
# Limiting clock measures exist a.s. at every fixed time

Law and setting. The unabsorbed two-input path `growthPathLaw W b`, the one-source family with a
nonnegative interval test `q` (no tags), and any `(P, Z)` along which the ordinary word values
converge in finite-dimensional distributions (`NsFddAlong` along some `φ`, bounded continuous
tests) on `[t₀, ∞)`, with `Z_w(t)` measurable for ordinary `w`, `t ≥ t₀`, and `P` a probability.

* Finite width (`nse_haus_trace_nonneg`): for `A = nearClock ⪰ 0` with eigenvalues `λ_r`,
  `a = Tr A`, the moments `c_k = Re Tr A^{k+1} = Σ_r λ_r^{k+1}` satisfy
  `H_{j,l}(c) = Σ_r λ_r^{j+1} (a - λ_r)^l ≥ 0` (all `j, l`).
* Closed conditions pass to the limit (`nse_ae_haus_nonneg`): the bounded continuous test
  `min(1, max(0, -H_{j,l}))` of the first `j+l+1` clock words vanishes at finite width, so its
  `P`-integral at the limit is `0`, hence `H_{j,l} ≥ 0` `P`-a.s.; countably many `(j, l)`.
* Hausdorff (`nse_hausdorff_exists`): on the good set the moment sequence
  `c_k = Re Z_{(QP)^{k+1}}(t)` is that of a finite measure on `[0, Re Z_{QP}(t)]`. The choice
  `nseClockMeas` is this measure on the good set and `0` elsewhere; `IsClockMeasure` holds a.s. at
  every fixed `t ≥ t₀` (`nse_ae_isClockMeasure`; one null set per time).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-!
## The Hausdorff tests
-/

/-- Real parts of a vector of word values, extended by `0`. -/
def nseCoeffs {m : ℕ} (z : Fin m → ℂ) (k : ℕ) : ℝ :=
  if h : k < m then (z ⟨k, h⟩).re else 0

theorem nse_continuous_coeffs {m : ℕ} (k : ℕ) : Continuous fun z : Fin m → ℂ => nseCoeffs z k := by
  unfold nseCoeffs
  split_ifs with h
  · exact Complex.continuous_re.comp (continuous_apply _)
  · exact continuous_const

theorem nse_continuous_haus (m j l : ℕ) :
    Continuous fun z : Fin m → ℂ => nseHaus (nseCoeffs z) (nseCoeffs z 0) j l := by
  unfold nseHaus
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((continuous_const.mul ((nse_continuous_coeffs 0).pow _)).mul continuous_const).mul
    (nse_continuous_coeffs _)

/-- The test `min(1, max(0, -H_{j,l}(Re z)))` (`a = Re z_0`). -/
def nseHausFun (j l : ℕ) (z : Fin (j + l + 1) → ℂ) : ℝ :=
  min 1 (max 0 (-nseHaus (nseCoeffs z) (nseCoeffs z 0) j l))

theorem nse_continuous_hausFun (j l : ℕ) : Continuous (nseHausFun j l) :=
  continuous_const.min (continuous_const.max (nse_continuous_haus _ j l).neg)

theorem nse_hausFun_nonneg (j l : ℕ) (z : Fin (j + l + 1) → ℂ) : 0 ≤ nseHausFun j l z :=
  le_min zero_le_one (le_max_left _ _)

theorem nse_hausFun_le_one (j l : ℕ) (z : Fin (j + l + 1) → ℂ) : nseHausFun j l z ≤ 1 :=
  min_le_left _ _

/-- The test as a bounded continuous function. -/
def nseHausBCF (j l : ℕ) : BoundedContinuousFunction (Fin (j + l + 1) → ℂ) ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨nseHausFun j l, nse_continuous_hausFun j l⟩ 1
    fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have := nse_hausFun_nonneg j l x
      have := nse_hausFun_nonneg j l y
      have := nse_hausFun_le_one j l x
      have := nse_hausFun_le_one j l y
      rw [abs_le]; constructor <;> linarith

theorem nse_hausBCF_apply (j l : ℕ) (z : Fin (j + l + 1) → ℂ) :
    nseHausBCF j l z = nseHausFun j l z := rfl

theorem nse_hausFun_eq_zero {j l : ℕ} {z : Fin (j + l + 1) → ℂ}
    (h : 0 ≤ nseHaus (nseCoeffs z) (nseCoeffs z 0) j l) : nseHausFun j l z = 0 := by
  unfold nseHausFun
  rw [max_eq_left (by linarith), min_eq_right zero_le_one]

theorem nse_haus_nonneg_of_hausFun {j l : ℕ} {z : Fin (j + l + 1) → ℂ}
    (h : nseHausFun j l z = 0) : 0 ≤ nseHaus (nseCoeffs z) (nseCoeffs z 0) j l := by
  unfold nseHausFun at h
  by_contra hneg
  replace hneg := lt_of_not_ge hneg
  have h1 : 0 < max 0 (-nseHaus (nseCoeffs z) (nseCoeffs z 0) j l) :=
    lt_max_of_lt_right (by linarith)
  have : 0 < min 1 (max 0 (-nseHaus (nseCoeffs z) (nseCoeffs z 0) j l)) := lt_min one_pos h1
  linarith

/-- `H_{j,l}` only reads `c_0, …, c_{j+l}`. -/
theorem nse_haus_congr {c c' : ℕ → ℝ} (a : ℝ) (j l : ℕ) (h : ∀ k, k ≤ j + l → c k = c' k) :
    nseHaus c a j l = nseHaus c' a j l := by
  unfold nseHaus
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h _ (by have := Finset.mem_range.1 hi; omega)]

/-!
## Finite width
-/

/-- `H_{j,l}(Σ_r λ_r^{k+1}) = Σ_r λ_r^{j+1} (a - λ_r)^l`. -/
theorem nse_haus_eigen {n : Type*} [Fintype n] (ev : n → ℝ) (a : ℝ) (j l : ℕ) :
    nseHaus (fun k => ∑ r, ev r ^ (k + 1)) a j l = ∑ r, ev r ^ (j + 1) * (a - ev r) ^ l := by
  unfold nseHaus
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sub_eq_neg_add, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_pow]
  ring

/-- **Finite-width Hausdorff conditions** for the trace moments of `A ⪰ 0`. -/
theorem nse_haus_trace_nonneg {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) {m : ℕ} (j l : ℕ) (hm : j + l < m) :
    0 ≤ nseHaus (nseCoeffs (fun i : Fin m => (A ^ ((i : ℕ) + 1)).trace))
      (nseCoeffs (fun i : Fin m => (A ^ ((i : ℕ) + 1)).trace) 0) j l := by
  set ev := hA.isHermitian.eigenvalues
  have hc : ∀ k, k < m →
      nseCoeffs (fun i : Fin m => (A ^ ((i : ℕ) + 1)).trace) k = ∑ r, ev r ^ (k + 1) := by
    intro k hk
    unfold nseCoeffs
    rw [dite_eq_left hk]
    exact ns_trace_pow_re A hA.isHermitian (k + 1)
  rw [hc 0 (by omega), nse_haus_congr _ j l (c' := fun k => ∑ r, ev r ^ (k + 1))
    (fun k hk => hc k (by omega)), nse_haus_eigen]
  refine Finset.sum_nonneg fun r _ => ?_
  have h0 : ∀ s, 0 ≤ ev s := hA.eigenvalues_nonneg
  have hle : ev r ≤ ∑ s, ev s := by
    have := Finset.single_le_sum (f := ev) (fun s _ => h0 s) (Finset.mem_univ r)
    simpa using this
  have : 0 ≤ ∑ s, ev s ^ (0 + 1) - ev r := by simpa using hle
  have := h0 r
  positivity

/-!
## The limit
-/

/-- The limiting clock moments `c_k = Re Z_{(QP)^{k+1}}(t, ω)`. -/
def nseClockCoeffs {Ω : Type*} (Z : ClockWord → ℝ → Ω → ℂ) (t : ℝ) (ω : Ω) (k : ℕ) : ℝ :=
  (Z (clockWord (k + 1)) t ω).re

theorem nse_coeffs_clockVec {Ω : Type*} (Z : ClockWord → ℝ → Ω → ℂ) (t : ℝ) (ω : Ω)
    {m : ℕ} {k : ℕ} (hk : k < m) :
    nseCoeffs (fun i : Fin m => Z (clockWord ((i : ℕ) + 1)) t ω) k = nseClockCoeffs Z t ω k := by
  unfold nseCoeffs nseClockCoeffs
  rw [dite_eq_left hk]

theorem nse_haus_clockVec {Ω : Type*} (Z : ClockWord → ℝ → Ω → ℂ) (t : ℝ) (ω : Ω) (j l : ℕ) :
    nseHaus (nseCoeffs (fun i : Fin (j + l + 1) => Z (clockWord ((i : ℕ) + 1)) t ω))
        (nseCoeffs (fun i : Fin (j + l + 1) => Z (clockWord ((i : ℕ) + 1)) t ω) 0) j l =
      nseHaus (nseClockCoeffs Z t ω) (nseClockCoeffs Z t ω 0) j l := by
  rw [nse_coeffs_clockVec Z t ω (by omega : 0 < j + l + 1)]
  exact nse_haus_congr _ j l fun k hk => nse_coeffs_clockVec Z t ω (by omega)

/-- **Closed Hausdorff conditions pass to fdd limits**: `H_{j,l}(c(t)) ≥ 0` for all `j, l`,
`P`-a.s., at every fixed `t ≥ t₀`. -/
theorem nse_ae_haus_nonneg {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {t₀ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Z : ClockWord → ℝ → Ω → ℂ}
    (hmeas : ∀ w, IsOrdinaryWord w → ∀ t, t₀ ≤ t → Measurable (Z w t)) {φ : ℕ → ℕ}
    (hfdd : NsFddAlong b E q t₀ P Z φ) {t : ℝ} (ht : t₀ ≤ t) :
    ∀ᵐ ω ∂P, ∀ j l : ℕ, 0 ≤ nseHaus (nseClockCoeffs Z t ω) (nseClockCoeffs Z t ω 0) j l := by
  refine ae_all_iff.2 fun j => ae_all_iff.2 fun l => ?_
  set m := j + l + 1
  let ws : Fin m → ClockWord := fun i => clockWord ((i : ℕ) + 1)
  have hlim := hfdd m ws (fun _ => t) (fun i => ⟨ns_isOrdinaryWord_clockWord (by omega), ht⟩)
    (nseHausBCF j l)
  have hfin : ∀ n, ∫ ω, nseHausBCF j l (fun i => wordValue b E (noTags (φ n)) (fun _ => q) (φ n)
      ⌊(φ n : ℝ) * t⌋₊ ω (ws i)) ∂growthPathLaw (φ n) b = 0 := by
    intro n
    refine integral_eq_zero_of_ae (Eventually.of_forall fun ω => ?_)
    simp only [Pi.zero_apply, nse_hausBCF_apply, ws]
    apply nse_hausFun_eq_zero
    have e : (fun i : Fin m => wordValue b E (noTags (φ n)) (fun _ => q) (φ n) ⌊(φ n : ℝ) * t⌋₊ ω
        (clockWord ((i : ℕ) + 1))) = fun i : Fin m =>
        ((nearClock b E (φ n) ⌊(φ n : ℝ) * t⌋₊ q ω) ^ ((i : ℕ) + 1)).trace := by
      funext i
      exact ns_wordValue_clockWord_eq b E q _ _ ω _ (by omega)
    rw [e]
    exact nse_haus_trace_nonneg (ns_nearClock_posSemidef b E _ _ q hq ω) j l (by omega)
  have hint : ∫ ω, nseHausBCF j l (fun i => Z (ws i) t ω) ∂P = 0 := by
    refine tendsto_nhds_unique hlim ?_
    exact tendsto_const_nhds.congr fun n => (hfin n).symm
  have hvec : Measurable fun ω => fun i : Fin m => Z (ws i) t ω :=
    measurable_pi_iff.2 fun i => hmeas _ (ns_isOrdinaryWord_clockWord (by omega)) t ht
  have hF : Measurable fun ω => nseHausBCF j l (fun i => Z (ws i) t ω) :=
    (nseHausBCF j l).continuous.measurable.comp hvec
  have hI : Integrable (fun ω => nseHausBCF j l (fun i => Z (ws i) t ω)) P := by
    refine Integrable.of_bound hF.aestronglyMeasurable 1 (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, nse_hausBCF_apply, abs_of_nonneg (nse_hausFun_nonneg j l _)]
    exact nse_hausFun_le_one j l _
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => nse_hausFun_nonneg j l _) hI).1 hint
  filter_upwards [hae] with ω hω
  rw [← nse_haus_clockVec]
  exact nse_haus_nonneg_of_hausFun hω

/-- The clock measure of the Hausdorff theorem on the good set, `0` elsewhere. -/
def nseClockMeas {Ω : Type*} (Z : ClockWord → ℝ → Ω → ℂ) (t : ℝ) (ω : Ω) : Measure ℝ :=
  open Classical in
  if h : ∀ j l : ℕ, 0 ≤ nseHaus (nseClockCoeffs Z t ω) (nseClockCoeffs Z t ω 0) j l then
    Classical.choose (nse_hausdorff_exists (by simpa [nseHaus] using h 0 0) h)
  else 0

theorem nse_isClockMeasure_of_haus {Ω : Type*} (Z : ClockWord → ℝ → Ω → ℂ) (t : ℝ) (ω : Ω)
    (h : ∀ j l : ℕ, 0 ≤ nseHaus (nseClockCoeffs Z t ω) (nseClockCoeffs Z t ω 0) j l) :
    IsClockMeasure Z t ω (nseClockMeas Z t ω) := by
  have hspec := Classical.choose_spec (nse_hausdorff_exists (by simpa [nseHaus] using h 0 0) h)
  unfold nseClockMeas
  rw [dite_eq_left h]
  obtain ⟨h1, h2, h3, h4⟩ := hspec
  refine ⟨h1, h2, ?_, fun k hk => ?_⟩
  · simpa [nseClockCoeffs] using h3
  · rw [h4 (k - 1)]
    unfold nseClockCoeffs
    rw [Nat.sub_add_cancel hk]

/-- **Limiting clock measures exist a.s. at every fixed time** `t ≥ t₀` of an fdd limit. -/
theorem nse_ae_isClockMeasure {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {t₀ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Z : ClockWord → ℝ → Ω → ℂ}
    (hmeas : ∀ w, IsOrdinaryWord w → ∀ t, t₀ ≤ t → Measurable (Z w t)) {φ : ℕ → ℕ}
    (hfdd : NsFddAlong b E q t₀ P Z φ) {t : ℝ} (ht : t₀ ≤ t) :
    ∀ᵐ ω ∂P, IsClockMeasure Z t ω (nseClockMeas Z t ω) := by
  filter_upwards [nse_ae_haus_nonneg hq hmeas hfdd ht] with ω hω
  exact nse_isClockMeasure_of_haus Z t ω hω

end BlockBand.Endpoints
