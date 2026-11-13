module

public import BlockBand.Endpoints.Response.RemoteHigherDefs
public import BlockBand.Endpoints.Response.RemoteHigherPinching
public import BlockBand.Endpoints.Response.RemoteHigherReversal
public import BlockBand.Endpoints.Response.NearSchattenUpper

/-!
# The remote higher-order clock bound from the near-clock bounds

## Main results

* `remoteHigher_holds (hN : RhNearHigherLimsupDecay) (hL : RhHigherLimitDecay) :
  RemoteHigherStatement`.

The remote bound is proved in `rh_core`: reverse the path for its far clock, pinch the complete
positive clock, and partition the source into intervals of length at most one; the deterministic
inequality `H_p(Q_1+Q_2) ≤ H_p(Q_1)+H_p(Q_2)` and an `L^r` summation add up the exponentially
decreasing travel bounds. In detail:
1. pieces: `K = ⌈2(τ-2R)⌉₊ + 2` unit sources `1_{[a_m, a_m+1/2]}`, `a_m = τ - R - m/2`, at
   travel `s_m = R - 1/2 + m/2 ≥ 1` from the near end, cover `[R - 1/2, τ - R + 1/2]`;
2. pinching (`rh_fracTrace_le_portBlocks`): `Tr Q^p ≤ Tr Q_near^p + Tr Q_far^p`;
3. near block: `Q_near(q) ⪯ Σ_m Q_near(1_m)` (grid monotonicity), then subadditivity;
4. far block: `Q_far(q)(ω) = Q_near(q')(rev ω)` with `q'(x) = q((n+1)/W - x)`
   (`rh_farBlock_eq_nearClock_revPath`); for `|(n+1)/W - τ| ≤ 1/2` the grid support of `q'` lies
   in `[R - 1/2, τ - R + 1/2]`, so again `⪯ Σ_m Q_near(1_m)(rev ω)`; the reversal preserves the
   law (`growthPathLaw_map_revPath`);
5. `L^r` summation: `(Σ_j x_j)^r ≤ (Σ_j w_j)^{r-1} Σ_j w_j^{1-r} x_j^r` with
   `w_m = e^{-cm/(4r)}` (in place of Minkowski) and `(x+y)^r ≤ 2^{r-1}(x^r+y^r)`;
6. limsup: subadditivity of `limsup` in `ℝ≥0∞`; the geometric sums are bounded independently of
   `K`, i.e. of the total length.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Endpoints

/-!
## Scalar inequalities
-/

/-- Weighted power mean: `(Σ_j x_j)^r ≤ (Σ_j w_j)^{r-1} Σ_j w_j^{1-r} x_j^r` (`x ≥ 0`, `w > 0`,
`r ≥ 1`). -/
theorem rh_rpow_sum_le {κ : Type*} (s : Finset κ) (x w : κ → ℝ) (hx : ∀ j ∈ s, 0 ≤ x j)
    (hw : ∀ j ∈ s, 0 < w j) {r : ℝ} (hr : 1 ≤ r) :
    (∑ j ∈ s, x j) ^ r ≤ (∑ j ∈ s, w j) ^ (r - 1) * ∑ j ∈ s, w j ^ (1 - r) * x j ^ r := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp [Real.zero_rpow (by linarith : r ≠ 0)]
  set S := ∑ j ∈ s, w j
  have hS : 0 < S := Finset.sum_pos hw hne
  have hJ := (convexOn_rpow hr).map_sum_le (t := s) (w := fun j => w j / S)
    (p := fun j => S * x j / w j) (fun j hj => (div_pos (hw j hj) hS).le)
    (by rw [← Finset.sum_div, div_self hS.ne'])
    (fun j hj => Set.mem_Ici.mpr (div_nonneg (mul_nonneg hS.le (hx j hj)) (hw j hj).le))
  simp only [smul_eq_mul] at hJ
  have h1 : ∑ j ∈ s, w j / S * (S * x j / w j) = ∑ j ∈ s, x j :=
    Finset.sum_congr rfl fun j hj => by field_simp [(hw j hj).ne', hS.ne']
  have h2 : ∑ j ∈ s, w j / S * (S * x j / w j) ^ r =
      S ^ (r - 1) * ∑ j ∈ s, w j ^ (1 - r) * x j ^ r := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hwj := hw j hj
    have hxj := hx j hj
    have hwr : 0 < w j ^ r := Real.rpow_pos_of_pos hwj r
    have hSr : 0 < S ^ r := Real.rpow_pos_of_pos hS r
    rw [Real.div_rpow (mul_nonneg hS.le hxj) hwj.le, Real.mul_rpow hS.le hxj, Real.rpow_sub hS,
      Real.rpow_sub hwj, Real.rpow_one, Real.rpow_one]
    field_simp
  rw [h1, h2] at hJ
  exact hJ

/-- `Σ_{m<K} e^{-θm} ≤ 1/(1 - e^{-θ})` for `θ > 0`. -/
theorem rh_sum_exp_le {θ : ℝ} (hθ : 0 < θ) (K : ℕ) :
    ∑ m ∈ Finset.range K, Real.exp (-(θ * m)) ≤ 1 / (1 - Real.exp (-θ)) := by
  have hx0 : 0 ≤ Real.exp (-θ) := (Real.exp_pos _).le
  have hx1 : Real.exp (-θ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := K) hx0 hx1
  rw [pow_zero, ← Finset.range_eq_Ico] at h
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun m _ => ?_)) h
  rw [← Real.exp_nat_mul]; ring_nf

/-- The constant of the remote bound. -/
def rhConst (C c r : ℝ) : ℝ :=
  2 ^ r * (1 / (1 - Real.exp (-(c / (4 * r))))) ^ (r - 1) * C * Real.exp (c / 2) /
    (1 - Real.exp (-(c / 4)))

/-- The weights `w_m = e^{-cm/(4r)}`. -/
def rhWeight (c r : ℝ) (m : ℕ) : ℝ := Real.exp (-(c / (4 * r) * m))

/-- The coefficient `2^{r-1} (Σ_{m<K} w_m)^{r-1} w_m^{1-r}` of piece `m`. -/
def rhCoeff (c r : ℝ) (K m : ℕ) : ℝ :=
  2 ^ (r - 1) * (∑ i ∈ Finset.range K, rhWeight c r i) ^ (r - 1) * rhWeight c r m ^ (1 - r)

theorem rh_coeff_nonneg (c r : ℝ) (K m : ℕ) : 0 ≤ rhCoeff c r K m := by
  unfold rhCoeff rhWeight
  have : 0 ≤ ∑ i ∈ Finset.range K, Real.exp (-(c / (4 * r) * i)) :=
    Finset.sum_nonneg fun i _ => (Real.exp_pos _).le
  positivity

/-- The final geometric estimate. -/
theorem rh_sum_coeff_le {C c r R : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hr : 1 ≤ r) (K : ℕ) :
    ∑ m ∈ Finset.range K, rhCoeff c r K m * 2 * (C * Real.exp (-(c * (R - 1 / 2 + m / 2)))) ≤
      rhConst C c r * Real.exp (-(c * R)) := by
  have hr0 : 0 < r := by linarith
  set θ := c / (4 * r) with hθdef
  have hθ : 0 < θ := by positivity
  set S := ∑ i ∈ Finset.range K, rhWeight c r i
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => (Real.exp_pos _).le
  have hS : S ≤ 1 / (1 - Real.exp (-θ)) := rh_sum_exp_le hθ K
  have hSr : S ^ (r - 1) ≤ (1 / (1 - Real.exp (-θ))) ^ (r - 1) :=
    Real.rpow_le_rpow hS0 hS (by linarith)
  have hρ : 0 < 1 - Real.exp (-(c / 4)) := by
    have := Real.exp_lt_one_iff.mpr (show -(c / 4) < 0 by linarith); linarith
  -- each term
  have hterm : ∀ m : ℕ, rhWeight c r m ^ (1 - r) * Real.exp (-(c * (m / 2))) ≤
      Real.exp (-(c / 4 * m)) := by
    intro m
    unfold rhWeight
    rw [← Real.exp_mul, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    have : c / (4 * r) * (r - 1) ≤ c / 4 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  have hgeom : ∑ m ∈ Finset.range K, Real.exp (-(c / 4 * m)) ≤ 1 / (1 - Real.exp (-(c / 4))) :=
    rh_sum_exp_le (by positivity) K
  have hexp : ∀ m : ℕ, Real.exp (-(c * (R - 1 / 2 + m / 2))) =
      Real.exp (-(c * R)) * Real.exp (c / 2) * Real.exp (-(c * (m / 2))) := by
    intro m; rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have h2 : (2 : ℝ) ^ (r - 1) * 2 = 2 ^ r := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one]; field_simp
  calc ∑ m ∈ Finset.range K, rhCoeff c r K m * 2 * (C * Real.exp (-(c * (R - 1 / 2 + m / 2))))
      = 2 ^ r * S ^ (r - 1) * C * Real.exp (-(c * R)) * Real.exp (c / 2) *
          ∑ m ∈ Finset.range K, rhWeight c r m ^ (1 - r) * Real.exp (-(c * (m / 2))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hexp m, ← h2]; unfold rhCoeff; ring
    _ ≤ 2 ^ r * (1 / (1 - Real.exp (-θ))) ^ (r - 1) * C * Real.exp (-(c * R)) *
          Real.exp (c / 2) * (1 / (1 - Real.exp (-(c / 4)))) := by
        have hsum : 0 ≤ ∑ m ∈ Finset.range K, rhWeight c r m ^ (1 - r) *
            Real.exp (-(c * (m / 2))) := Finset.sum_nonneg fun m _ => by
          unfold rhWeight; positivity
        have hsum' : ∑ m ∈ Finset.range K, rhWeight c r m ^ (1 - r) *
            Real.exp (-(c * (m / 2))) ≤ 1 / (1 - Real.exp (-(c / 4))) :=
          (Finset.sum_le_sum fun m _ => hterm m).trans hgeom
        have hA : 0 ≤ (2 : ℝ) ^ r * S ^ (r - 1) * C * Real.exp (-(c * R)) * Real.exp (c / 2) := by
          positivity
        calc _ ≤ 2 ^ r * S ^ (r - 1) * C * Real.exp (-(c * R)) * Real.exp (c / 2) *
              (1 / (1 - Real.exp (-(c / 4)))) := mul_le_mul_of_nonneg_left hsum' hA
          _ ≤ _ := by
            gcongr
    _ = rhConst C c r * Real.exp (-(c * R)) := by
        unfold rhConst; rw [hθdef]; field_simp

/-!
## `limsup` in `ℝ≥0∞`
-/

theorem rh_limsup_add_le (u v : ℕ → ℝ≥0∞) :
    limsup (fun W => u W + v W) atTop ≤ limsup u atTop + limsup v atTop := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt => ?_
  have hu : limsup u atTop < limsup u atTop + (ε / 2 : NNReal) :=
    ENNReal.lt_add_right (ne_top_of_le_ne_top hlt.ne (le_self_add)) (by simpa using hε.ne')
  have hv : limsup v atTop < limsup v atTop + (ε / 2 : NNReal) :=
    ENNReal.lt_add_right (ne_top_of_le_ne_top hlt.ne le_add_self) (by simpa using hε.ne')
  have h1 := eventually_lt_of_limsup_lt hu
  have h2 := eventually_lt_of_limsup_lt hv
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [h1, h2] with W hW1 hW2
  calc u W + v W ≤ (limsup u atTop + (ε / 2 : NNReal)) + (limsup v atTop + (ε / 2 : NNReal)) :=
        add_le_add hW1.le hW2.le
    _ = limsup u atTop + limsup v atTop + ε := by
        rw [add_add_add_comm, ← ENNReal.coe_add, add_halves]

theorem rh_limsup_sum_le {κ : Type*} (s : Finset κ) (u : κ → ℕ → ℝ≥0∞) :
    limsup (fun W => ∑ i ∈ s, u i W) atTop ≤ ∑ i ∈ s, limsup (u i) atTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (rh_limsup_add_le (u i) fun W => ∑ j ∈ s, u j W).trans (add_le_add le_rfl ih)

/-!
## Unit pieces
-/

/-- The unit piece `1_{[a, a+1/2]}`. -/
def rhInd (a : ℝ) : ℝ → ℝ := (Set.Icc a (a + 1 / 2)).indicator fun _ => 1

theorem rh_ind_nonneg (a x : ℝ) : 0 ≤ rhInd a x := by
  unfold rhInd; simp only [Set.indicator_apply]; split_ifs <;> norm_num

theorem rh_ind_le_one (a x : ℝ) : rhInd a x ≤ 1 := by
  unfold rhInd; simp only [Set.indicator_apply]; split_ifs <;> norm_num

theorem rh_isUnitSource_ind {a : ℝ} (ha : 0 ≤ a) : IsUnitSource a (1 / 2) (rhInd a) := by
  refine ⟨ha, by norm_num, by norm_num, ⟨rh_ind_nonneg a, fun x hx => ?_, ?_⟩, rh_ind_le_one a⟩
  · unfold rhInd; exact indicator_of_notMem hx (fun _ => (1 : ℝ))
  · refine (continuousOn_const (c := (1 : ℝ))).congr fun x hx => ?_
    unfold rhInd; exact indicator_of_mem hx (fun _ => (1 : ℝ))

/-- The piece positions `a_m = τ - R - m/2`. -/
def rhPos (τ R : ℝ) (m : ℕ) : ℝ := τ - R - m / 2

/-- The number of pieces `K = ⌈2(τ - 2R)⌉₊ + 2`. -/
def rhCount (τ R : ℝ) : ℕ := ⌈2 * (τ - 2 * R)⌉₊ + 2

theorem rh_cover {τ R : ℝ} {x : ℝ} (hx : x ∈ Icc (R - 1 / 2) (τ - R + 1 / 2)) :
    1 ≤ ∑ m ∈ Finset.range (rhCount τ R), rhInd (rhPos τ R m) x := by
  set m := ⌈2 * (τ - R - x)⌉₊
  have hm1 : 2 * (τ - R - x) ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < max (2 * (τ - R - x)) 0 + 1 := by
    rcases le_or_gt (2 * (τ - R - x)) 0 with h | h
    · have : m = 0 := Nat.ceil_eq_zero.mpr h
      rw [this]; push_cast; linarith [le_max_right (2 * (τ - R - x)) 0]
    · have := Nat.ceil_lt_add_one h.le; rw [max_eq_left h.le]; exact this
  have hmK : m < rhCount τ R := by
    unfold rhCount
    have h' : (m : ℝ) < ((⌈2 * (τ - 2 * R)⌉₊ + 2 : ℕ) : ℝ) := by
      push_cast
      have h1 := hx.1
      have h2 := Nat.le_ceil (2 * (τ - 2 * R))
      rcases le_or_gt (2 * (τ - R - x)) 0 with h | h
      · rw [max_eq_right h] at hm2
        have : (0 : ℝ) ≤ ⌈2 * (τ - 2 * R)⌉₊ := Nat.cast_nonneg _
        linarith
      · rw [max_eq_left h.le] at hm2; linarith
    exact_mod_cast h'
  have hmem : x ∈ Icc (rhPos τ R m) (rhPos τ R m + 1 / 2) := by
    unfold rhPos
    constructor
    · linarith
    · rcases le_or_gt (2 * (τ - R - x)) 0 with h | h
      · rw [max_eq_right h] at hm2
        have : m = 0 := Nat.ceil_eq_zero.mpr h
        rw [this]; push_cast; linarith [hx.2]
      · rw [max_eq_left h.le] at hm2; linarith
  have hone : rhInd (rhPos τ R m) x = 1 := by
    unfold rhInd; exact indicator_of_mem hmem (fun _ => (1 : ℝ))
  calc (1 : ℝ) = rhInd (rhPos τ R m) x := hone.symm
    _ ≤ _ := Finset.single_le_sum (fun i _ => rh_ind_nonneg _ x) (Finset.mem_range.mpr hmK)

theorem rh_pos_nonneg {τ R : ℝ} (hR : 2 ≤ R) (h2R : 2 * R ≤ τ) {m : ℕ} (hm : m < rhCount τ R) :
    0 ≤ rhPos τ R m := by
  unfold rhPos
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * (τ - 2 * R) by linarith)
  have : (m : ℝ) ≤ ⌈2 * (τ - 2 * R)⌉₊ + 1 := by
    unfold rhCount at hm; exact_mod_cast (show m ≤ ⌈2 * (τ - 2 * R)⌉₊ + 1 by omega)
  linarith

/-!
## The pointwise bound
-/

section Pointwise

variable {b e p : ℝ} {W : ℕ}

theorem rh_fracTrace_nearClock_le (hp : 0 < p) (hp1 : p ≤ 1) (j K : ℕ) (a : ℕ → ℝ)
    {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    (hgrid : ∀ k : ℕ, k < j → q (((k + 1 : ℕ) : ℝ) / W) ≤
      ∑ m ∈ Finset.range K, rhInd (a m) (((k + 1 : ℕ) : ℝ) / W)) (ω : GrowthPath W) :
    fracTrace p (nearClock b e W j q ω) ≤
      ∑ m ∈ Finset.range K, fracTrace p (nearClock b e W j (rhInd (a m)) ω) := by
  set g : ℝ → ℝ := ∑ m ∈ Finset.range K, rhInd (a m)
  have hg0 : ∀ x, 0 ≤ g x := fun x => by
    simp only [g, Finset.sum_apply]; exact Finset.sum_nonneg fun m _ => rh_ind_nonneg _ x
  have hmono : (nearClock b e W j g ω - nearClock b e W j q ω).PosSemidef := by
    unfold nearClock
    rw [← rh_portBlock_sub]
    refine rh_portBlock_posSemidef (rh_intervalSource_mono b e (fun k hk => ?_) ω) 0
    simp only [g, Finset.sum_apply]; exact hgrid k hk
  calc fracTrace p (nearClock b e W j q ω) ≤ fracTrace p (nearClock b e W j g ω) :=
        fracTrace_mono (ns_nearClock_posSemidef b e W j q hq0 ω).isHermitian
          (ns_nearClock_posSemidef b e W j g hg0 ω).isHermitian hmono hp.le
    _ = fracTrace p (∑ m ∈ Finset.range K, nearClock b e W j (rhInd (a m)) ω) := by
        rw [rh_nearClock_sum]
    _ ≤ _ := rh_fracTrace_sum_le _ _ (fun m _ =>
        ns_nearClock_posSemidef b e W j _ (rh_ind_nonneg _) ω) hp hp1

/-- The pointwise remote bound at one width: near and far blocks dominated by the unit pieces of
the path and of the reversed path. -/
theorem rh_pointwise (hp : 0 < p) (hp1 : p ≤ 1) {τ R : ℝ} (hW : 0 < W)
    (n : ℕ) {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∀ x, q x ≤ 1)
    (hqs : ∀ x, x ∉ Icc R (τ - R) → q x = 0) (hn : |((n : ℝ) + 1) / W - τ| ≤ 1 / 2)
    (ω : GrowthPath W) :
    fracTrace p (intervalSource b e W n q ω) ≤
      ∑ m ∈ Finset.range (rhCount τ R),
          fracTrace p (nearClock b e W n (rhInd (rhPos τ R m)) ω) +
        ∑ m ∈ Finset.range (rhCount τ R),
          fracTrace p (nearClock b e W n (rhInd (rhPos τ R m)) (revPath n ω)) := by
  have hQ := intervalSource_posSemidef b e W n q hq0 ω
  refine (rh_fracTrace_le_portBlocks hQ hp.le hp1).trans (add_le_add ?_ ?_)
  · -- near block
    refine rh_fracTrace_nearClock_le hp hp1 n _ _ hq0 (fun k _ => ?_) ω
    set x : ℝ := ((k + 1 : ℕ) : ℝ) / W
    by_cases hx : x ∈ Icc R (τ - R)
    · have hc := rh_cover (τ := τ) (R := R) (x := x) ⟨by linarith [hx.1], by linarith [hx.2]⟩
      exact (hq1 x).trans hc
    · rw [hqs x hx]; exact Finset.sum_nonneg fun m _ => rh_ind_nonneg _ x
  · -- far block, through the reversal
    set q' : ℝ → ℝ := fun x => q (((n : ℝ) + 1) / W - x)
    have hrev : ∀ k : ℕ, k < n → q' (((n - k : ℕ) : ℝ) / W) = q (((k + 1 : ℕ) : ℝ) / W) := by
      intro k hk
      simp only [q']
      congr 1
      have hWr : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
      rw [Nat.cast_sub hk.le]; push_cast; field_simp; ring
    rw [rh_farBlock_eq_nearClock_revPath b e q q' hrev ω]
    have hq'0 : ∀ x, 0 ≤ q' x := fun x => hq0 _
    refine rh_fracTrace_nearClock_le hp hp1 n _ _ hq'0 (fun k _ => ?_) _
    set x : ℝ := ((k + 1 : ℕ) : ℝ) / W
    by_cases hx : ((n : ℝ) + 1) / W - x ∈ Icc R (τ - R)
    · have habs := abs_le.mp hn
      have hc := rh_cover (τ := τ) (R := R) (x := x)
        ⟨by linarith [hx.2, habs.1, habs.2], by linarith [hx.1, habs.1, habs.2]⟩
      exact (hq1 _).trans hc
    · show q (((n : ℝ) + 1) / W - x) ≤ _
      rw [hqs _ hx]; exact Finset.sum_nonneg fun m _ => rh_ind_nonneg _ x

end Pointwise

/-!
## Integration at one width
-/

theorem rh_fracTrace_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ} (hp : 0 < p) :
    fracTrace p (0 : Matrix ι ι ℂ) = 0 := by
  unfold fracTrace
  rw [charpoly_zero, Polynomial.roots_X_pow, Multiset.map_nsmul, Multiset.sum_nsmul,
    Multiset.map_singleton, Multiset.sum_singleton]
  simp [Real.zero_rpow hp.ne']

theorem rh_measurable_fracTrace_nearClock {b e p : ℝ} (hp : 0 < p) (W j : ℕ) {q : ℝ → ℝ}
    (hq : ∀ x, 0 ≤ q x) : Measurable (fun ω : GrowthPath W => fracTrace p (nearClock b e W j q ω)) :=
  rh_measurable_fracTrace (ns_measurable_nearClock b e W j q)
    (fun ω => (ns_nearClock_posSemidef b e W j q hq ω).isHermitian) hp

/-- The real form of the `L^r` summation. -/
theorem rh_real_power_bound {c r : ℝ} (hr : 1 ≤ r) (K : ℕ) {F : ℝ} (x y : ℕ → ℝ) (hF : 0 ≤ F)
    (hx : ∀ m, 0 ≤ x m) (hy : ∀ m, 0 ≤ y m)
    (hFle : F ≤ ∑ m ∈ Finset.range K, x m + ∑ m ∈ Finset.range K, y m) :
    F ^ r ≤ ∑ m ∈ Finset.range K, rhCoeff c r K m * (x m ^ r + y m ^ r) := by
  have hr0 : 0 ≤ r := by linarith
  set X := ∑ m ∈ Finset.range K, x m
  set Y := ∑ m ∈ Finset.range K, y m
  set S := ∑ i ∈ Finset.range K, rhWeight c r i
  have hX : 0 ≤ X := Finset.sum_nonneg fun m _ => hx m
  have hY : 0 ≤ Y := Finset.sum_nonneg fun m _ => hy m
  have hw : ∀ m ∈ Finset.range K, 0 < rhWeight c r m := fun m _ => Real.exp_pos _
  have h2 : (X + Y) ^ r ≤ 2 ^ (r - 1) * (X ^ r + Y ^ r) := by
    have := rh_rpow_sum_le (Finset.univ : Finset (Fin 2)) ![X, Y] (fun _ => 1)
      (fun j _ => by fin_cases j <;> simp [hX, hY]) (fun _ _ => one_pos) hr
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.one_rpow, one_mul] at this
    norm_num at this
    exact this
  have hXr := rh_rpow_sum_le (Finset.range K) x (rhWeight c r) (fun m _ => hx m) hw hr
  have hYr := rh_rpow_sum_le (Finset.range K) y (rhWeight c r) (fun m _ => hy m) hw hr
  have h2r : (0 : ℝ) ≤ 2 ^ (r - 1) := by positivity
  calc F ^ r ≤ (X + Y) ^ r := Real.rpow_le_rpow hF hFle hr0
    _ ≤ 2 ^ (r - 1) * (X ^ r + Y ^ r) := h2
    _ ≤ 2 ^ (r - 1) * (S ^ (r - 1) * ∑ m ∈ Finset.range K, rhWeight c r m ^ (1 - r) * x m ^ r +
          S ^ (r - 1) * ∑ m ∈ Finset.range K, rhWeight c r m ^ (1 - r) * y m ^ r) := by
        gcongr
    _ = ∑ m ∈ Finset.range K, rhCoeff c r K m * (x m ^ r + y m ^ r) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        unfold rhCoeff; ring

/-- The remote bound at one width: `E (Tr Q^p)^r ≤ Σ_m 2 c_m E (Tr A_m^p)^r`, `A_m` the near
clock of the unit piece `m`. -/
theorem rh_lintegral_le {b e p r c τ R : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hr : 1 ≤ r) {W : ℕ}
    (hW : 0 < W) (n : ℕ) {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∀ x, q x ≤ 1)
    (hqs : ∀ x, x ∉ Icc R (τ - R) → q x = 0) (hn : |((n : ℝ) + 1) / W - τ| ≤ 1 / 2) :
    ∫⁻ ω, ENNReal.ofReal (fracTrace p (intervalSource b e W n q ω)) ^ r ∂growthPathLaw W b ≤
      ∑ m ∈ Finset.range (rhCount τ R), ENNReal.ofReal (rhCoeff c r (rhCount τ R) m) *
        (∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b e W n (rhInd (rhPos τ R m)) ω)) ^ r
            ∂growthPathLaw W b +
          ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b e W n (rhInd (rhPos τ R m)) ω)) ^ r
            ∂growthPathLaw W b) := by
  have hr0 : 0 ≤ r := by linarith
  set K := rhCount τ R
  set h : ℕ → GrowthPath W → ℝ := fun m ω =>
    fracTrace p (nearClock b e W n (rhInd (rhPos τ R m)) ω)
  have hmeas : ∀ m, Measurable (h m) := fun m =>
    rh_measurable_fracTrace_nearClock hp W n (rh_ind_nonneg _)
  have hmeasr : ∀ m, Measurable (fun ω => ENNReal.ofReal (h m ω) ^ r) := fun m =>
    (ENNReal.measurable_ofReal.comp (hmeas m)).pow_const r
  have hrevm := measurable_revPath n W
  -- pointwise
  have hpt : ∀ ω, ENNReal.ofReal (fracTrace p (intervalSource b e W n q ω)) ^ r ≤
      ∑ m ∈ Finset.range K, ENNReal.ofReal (rhCoeff c r K m) *
        (ENNReal.ofReal (h m ω) ^ r + ENNReal.ofReal (h m (revPath n ω)) ^ r) := by
    intro ω
    have hF := rh_pointwise (b := b) (e := e) hp hp1 (τ := τ) (R := R) hW n hq0 hq1 hqs hn ω
    have hreal := rh_real_power_bound (c := c) hr K (fun m => h m ω)
      (fun m => h m (revPath n ω)) (fracTrace_nonneg _ _) (fun m => fracTrace_nonneg _ _)
      (fun m => fracTrace_nonneg _ _) hF
    rw [ENNReal.ofReal_rpow_of_nonneg (fracTrace_nonneg _ _) hr0]
    refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_sum_of_nonneg fun m _ => mul_nonneg (rh_coeff_nonneg c r K m)
      (add_nonneg (Real.rpow_nonneg (fracTrace_nonneg _ _) _)
        (Real.rpow_nonneg (fracTrace_nonneg _ _) _))]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ENNReal.ofReal_mul (rh_coeff_nonneg c r K m),
      ENNReal.ofReal_add (Real.rpow_nonneg (fracTrace_nonneg _ _) _)
        (Real.rpow_nonneg (fracTrace_nonneg _ _) _),
      ENNReal.ofReal_rpow_of_nonneg (fracTrace_nonneg _ _) hr0,
      ENNReal.ofReal_rpow_of_nonneg (fracTrace_nonneg _ _) hr0]
  have hadd : ∀ m, Measurable (fun ω =>
      ENNReal.ofReal (h m ω) ^ r + ENNReal.ofReal (h m (revPath n ω)) ^ r) := fun m =>
    (hmeasr m).add ((hmeasr m).comp hrevm)
  have hsm : ∀ m, Measurable (fun ω => ENNReal.ofReal (rhCoeff c r K m) *
      (ENNReal.ofReal (h m ω) ^ r + ENNReal.ofReal (h m (revPath n ω)) ^ r)) := fun m =>
    (hadd m).const_mul _
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  rw [lintegral_finsetSum _ fun m _ => hsm m]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [lintegral_const_mul _ (hadd m), lintegral_add_left (hmeasr m)]
  congr 2
  have := lintegral_map (μ := growthPathLaw W b) (hmeasr m) hrevm
  rw [growthPathLaw_map_revPath] at this
  exact this.symm

/-!
## The core: from near-piece bounds to the remote bound
-/

/-- Core of the remote clock bound. For energies `e_W`, lengths `n_W` with `n_W/W → τ`, a source
`0 ≤ q ≤ 1` vanishing off `[R, τ-R]`, `R ≥ 2`: if every unit piece `1_{[a, a+1/2]}` with `a ≥ 0`
at travel `s ≥ 1` (`a + 1/2 + s = τ`) has near-clock bound `limsup_W E (Tr A^p)^r ≤ C e^{-cs}`,
then `limsup_W E (Tr Q(q)^p)^r ≤ rhConst C c r · e^{-cR}`. -/
theorem rh_core {b p r C c τ R : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hr : 1 ≤ r) (hC : 0 ≤ C)
    (hc : 0 < c) (hR : 2 ≤ R) (e : ℕ → ℝ) (n : ℕ → ℕ)
    (hn : Tendsto (fun W : ℕ => (n W : ℝ) / W) atTop (𝓝 τ)) {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    (hq1 : ∀ x, q x ≤ 1) (hqs : ∀ x, x ∉ Icc R (τ - R) → q x = 0)
    (hpiece : ∀ a s : ℝ, 0 ≤ a → 1 ≤ s → a + 1 / 2 + s = τ →
      limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
          (fracTrace p (nearClock b (e W) W (n W) (rhInd a) ω)) ^ r ∂growthPathLaw W b) atTop ≤
        ENNReal.ofReal (C * Real.exp (-(c * s)))) :
    limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
        (fracTrace p (intervalSource b (e W) W (n W) q ω)) ^ r ∂growthPathLaw W b) atTop ≤
      ENNReal.ofReal (rhConst C c r * Real.exp (-(c * R))) := by
  have hr0 : 0 < r := by linarith
  by_cases h2R : 2 * R ≤ τ
  swap
  · -- the source vanishes
    have hq : q = 0 := by
      funext x
      exact hqs x fun hx => h2R (by linarith [hx.1, hx.2])
    subst hq
    have : (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
        (fracTrace p (intervalSource b (e W) W (n W) 0 ω)) ^ r ∂growthPathLaw W b) = fun _ => 0 := by
      funext W
      simp only [rh_intervalSource_zero, rh_fracTrace_zero hp, ENNReal.ofReal_zero,
        ENNReal.zero_rpow_of_pos hr0, lintegral_zero]
    rw [this, limsup_const]
    exact bot_le
  set K := rhCount τ R
  -- eventually `W ≥ 1` and `|(n_W + 1)/W - τ| ≤ 1/2`
  have hn' : Tendsto (fun W : ℕ => ((n W : ℝ) + 1) / W) atTop (𝓝 τ) := by
    have := hn.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [add_zero] at this
    refine this.congr fun W => ?_
    rw [add_div]
  have hev : ∀ᶠ W : ℕ in atTop, 0 < W ∧ |((n W : ℝ) + 1) / W - τ| ≤ 1 / 2 := by
    filter_upwards [eventually_ge_atTop 1,
      hn'.eventually (Metric.closedBall_mem_nhds τ (by norm_num : (0 : ℝ) < 1 / 2))]
      with W hW1 hW2
    exact ⟨hW1, by rw [Real.dist_eq] at hW2; exact hW2⟩
  set G : ℕ → ℕ → ℝ≥0∞ := fun m W => ∫⁻ ω, ENNReal.ofReal
    (fracTrace p (nearClock b (e W) W (n W) (rhInd (rhPos τ R m)) ω)) ^ r ∂growthPathLaw W b
  have hstep : limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
        (fracTrace p (intervalSource b (e W) W (n W) q ω)) ^ r ∂growthPathLaw W b) atTop ≤
      limsup (fun W => ∑ m ∈ Finset.range K,
        ENNReal.ofReal (rhCoeff c r K m) * (G m W + G m W)) atTop := by
    refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [hev] with W hW
    exact rh_lintegral_le hp hp1 hr hW.1 (n W) hq0 hq1 hqs hW.2
  refine hstep.trans ((rh_limsup_sum_le _ _).trans ?_)
  have hm : ∀ m ∈ Finset.range K, limsup (fun W => ENNReal.ofReal (rhCoeff c r K m) *
      (G m W + G m W)) atTop ≤ ENNReal.ofReal (rhCoeff c r K m * 2 *
        (C * Real.exp (-(c * (R - 1 / 2 + m / 2))))) := by
    intro m hmK
    rw [ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
    have hpc := hpiece (rhPos τ R m) (R - 1 / 2 + m / 2)
      (rh_pos_nonneg hR h2R (Finset.mem_range.mp hmK))
      (by have : (0 : ℝ) ≤ m := m.cast_nonneg; linarith) (by unfold rhPos; ring)
    have h2 : limsup (fun W => G m W + G m W) atTop ≤
        ENNReal.ofReal (C * Real.exp (-(c * (R - 1 / 2 + m / 2)))) +
          ENNReal.ofReal (C * Real.exp (-(c * (R - 1 / 2 + m / 2)))) :=
      (rh_limsup_add_le _ _).trans (add_le_add hpc hpc)
    have hCe : 0 ≤ C * Real.exp (-(c * (R - 1 / 2 + m / 2))) := by positivity
    rw [mul_assoc, ENNReal.ofReal_mul (rh_coeff_nonneg c r K m)]
    gcongr
    refine h2.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add hCe hCe]; congr 1; ring
  refine (Finset.sum_le_sum hm).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun m _ => by
    have := rh_coeff_nonneg c r K m; positivity]
  exact ENNReal.ofReal_le_ofReal (rh_sum_coeff_le hC hc hr K)

/-!
## The remote higher-order clock theorem
-/

theorem rh_tendsto_floor_div {τ : ℝ} (hτ : 0 ≤ τ) :
    Tendsto (fun W : ℕ => ((⌊(W : ℝ) * τ⌋₊ : ℕ) : ℝ) / W) atTop (𝓝 τ) := by
  have := (tendsto_nat_floor_mul_div_atTop (R := ℝ) hτ).comp tendsto_natCast_atTop_atTop
  refine this.congr fun W => ?_
  simp only [Function.comp_apply, mul_comm]

theorem rh_travelLength_eq {W : ℕ} {a s τ : ℝ} (h : a + 1 / 2 + s = τ) :
    travelLength W a (1 / 2) s = ⌊(W : ℝ) * τ⌋₊ := by
  unfold travelLength; rw [h]

/-- The remote higher-order clock theorem `RemoteHigherStatement`, from the near-clock input
`RhNearHigherLimsupDecay` (clause `limsupBound`, through `rh_core`) and the limit input
`RhHigherLimitDecay` (clause `limitDecay`). -/
theorem remoteHigher_holds (hN : RhNearHigherLimsupDecay) (hL : RhHigherLimitDecay) :
    RemoteHigherStatement := by
  refine ⟨?_, hL⟩
  intro b hb hb' E hE hE' p r hp hp1 hr hpr
  obtain ⟨C, c, hc, hC⟩ := hN b hb hb' E hE hE' p r hp hp1 hr hpr
  refine ⟨rhConst (max C 0) c r, c, hc, fun τ R hτ hR q hq hq1 => ?_⟩
  refine rh_core hp hp1.le hr (le_max_right C 0) hc hR (fun _ => E) (fun W => ⌊(W : ℝ) * τ⌋₊)
    (rh_tendsto_floor_div hτ.le) hq.1 hq1 hq.2.1 fun a s ha hs has => ?_
  have h := hC a (1 / 2) (rhInd a) (rh_isUnitSource_ind ha) s hs
  simp only [rh_travelLength_eq has] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  gcongr
  exact le_max_left _ _

/-- **Uniform **, `RemoteHigherUniformStatement`, from the
isolated uniform near-clock input `RhNearHigherLimsupDecayUniform`.
-/
theorem remoteHigherUniform_holds (hNU : RhNearHigherLimsupDecayUniform) :
    RemoteHigherUniformStatement := by
  intro b hb hb' E hE hE' p r hp hp1 hr hpr K hK
  obtain ⟨C, c, hc, hC⟩ := hNU b hb hb' E hE hE' p r hp hp1 hr hpr K hK
  refine ⟨rhConst (max C 0) c r, c, hc, fun τ R hτ hR e n he hn q hq0 hq1 hqs => ?_⟩
  refine rh_core hp hp1.le hr (le_max_right C 0) hc hR e n hn hq0 hq1 hqs
    fun a s ha hs has => ?_
  have h := hC a (1 / 2) (rhInd a) (rh_isUnitSource_ind ha) s hs e n he (by rw [has]; exact hn)
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  gcongr
  exact le_max_left _ _

/-- The uniform statement contains `limsupBound` of `RemoteHigherStatement` (constant energy,
`K = 0`, lengths `⌊Wτ⌋`, continuous source tests). -/
theorem rh_limsupBound_of_uniform (hU : RemoteHigherUniformStatement) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < 1 → 1 ≤ r → p * r < 1 →
      ∃ C c : ℝ, 0 < c ∧ ∀ τ R : ℝ, 0 < τ → 2 ≤ R → ∀ q : ℝ → ℝ,
        IsSourceTest R (τ - R) q → (∀ x, q x ≤ 1) →
          limsup (fun W : ℕ => ∫⁻ w, ENNReal.ofReal
              (fracTrace p (intervalSource b E W ⌊(W : ℝ) * τ⌋₊ q w)) ^ r
              ∂growthPathLaw W b) atTop ≤
            ENNReal.ofReal (C * Real.exp (-(c * R))) := by
  intro b hb hb' E hE hE' p r hp hp1 hr hpr
  obtain ⟨C, c, hc, hC⟩ := hU b hb hb' E hE hE' p r hp hp1 hr hpr 0 le_rfl
  refine ⟨C, c, hc, fun τ R hτ hR q hq hq1 => ?_⟩
  exact hC τ R hτ hR (fun _ => E) (fun W => ⌊(W : ℝ) * τ⌋₊)
    (Eventually.of_forall fun W => by simp) (rh_tendsto_floor_div hτ.le) q hq.1 hq1 hq.2.1

/-!
## The case `r = 1` from near-Schatten decay
-/

/-- Isolated input 1 at `r = 1` is the `NearSchattenDecayContract.limsupDecay`. -/
theorem rh_nearHigherLimsupDecay_one (hDec : NearSchattenDecayContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ p : ℝ, 0 < p → p < 1 →
      ∃ C c : ℝ, 0 < c ∧ ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q → ∀ s : ℝ, 1 ≤ s →
        limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
            (fracTrace p (nearClock b E W (travelLength W t₁ R s) q ω)) ^ (1 : ℝ)
            ∂growthPathLaw W b) atTop ≤
          ENNReal.ofReal (C * Real.exp (-(c * s))) := by
  intro b hb hb' E hE hE' p hp hp1
  obtain ⟨C, hC⟩ := hDec.limsupDecay b hb hb' E hE hE' p hp hp1
  have hD : 0 < transportD0 b E := by
    unfold transportD0
    have : 0 < 4 - E ^ 2 := by nlinarith
    positivity
  refine ⟨C, transportD0 b E * p * (1 - p) / 2, by
    have : 0 < 1 - p := by linarith
    positivity, fun t₁ R q hq s hs => ?_⟩
  simp only [ENNReal.rpow_one]
  have h := hC t₁ R q hq s hs
  unfold clockFracMoment at h
  refine h.trans (le_of_eq ?_)
  congr 3; ring

/-- Isolated input 2 at `r = 1` is the `NearSchattenDecayContract.limitDecay`. -/
theorem rh_higherLimitDecay_one (hDec : NearSchattenDecayContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ p : ℝ, 0 < p → p < 1 →
    ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (Z : ClockWord → ℝ → Ω → ℂ),
      BlockBand.Internal.Contracts.TransmissionStatements.IsWordLimit b E noTags (fun _ => q)
        (t₁ + R) P Z →
    ∀ μ : ℝ → Ω → Measure ℝ, (∀ t : ℝ, t₁ + R ≤ t → ∀ᵐ w ∂P, IsClockMeasure Z t w (μ t w)) →
    ∀ s t : ℝ, 0 < s → 0 ≤ t →
      ∫⁻ w, limitFracTrace p (μ (t₁ + R + s + t) w) ^ (1 : ℝ) ∂P ≤
        ENNReal.ofReal (Real.exp (-(transportD0 b E * 1 * p * (1 - 1 * p) * t / 2))) *
          ∫⁻ w, limitFracTrace p (μ (t₁ + R + s) w) ^ (1 : ℝ) ∂P := by
  intro b hb hb' E hE hE' p hp hp1 t₁ R q hq Ω _ P Z hZ μ hμ s t hs ht
  simp only [ENNReal.rpow_one, mul_one, one_mul]
  exact hDec.limitDecay b hb hb' E hE hE' p hp hp1 t₁ R q hq Ω _ P Z hZ μ hμ s t hs ht

/-- **The remote clock tail for source tests** (`[0,1]`-valued sources continuous on
`[R, τ-R]`): the case `r = 1` of `limsupBound`, from `NearSchattenDecayContract` alone. -/
theorem rh_remoteClockTail (hDec : NearSchattenDecayContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ p : ℝ, 0 < p → p < 1 →
      ∃ C c : ℝ, 0 < c ∧ ∀ τ R : ℝ, 0 < τ → 2 ≤ R → ∀ q : ℝ → ℝ,
        IsSourceTest R (τ - R) q → (∀ x, q x ≤ 1) →
          limsup (fun W : ℕ => ∫⁻ w, ENNReal.ofReal
              (fracTrace p (intervalSource b E W ⌊(W : ℝ) * τ⌋₊ q w)) ∂growthPathLaw W b) atTop ≤
            ENNReal.ofReal (C * Real.exp (-(c * R))) := by
  intro b hb hb' E hE hE' p hp hp1
  obtain ⟨C, c, hc, hC⟩ := rh_nearHigherLimsupDecay_one hDec b hb hb' E hE hE' p hp hp1
  refine ⟨rhConst (max C 0) c 1, c, hc, fun τ R hτ hR q hq hq1 => ?_⟩
  have h := rh_core (r := 1) hp hp1.le le_rfl (le_max_right C 0) hc hR (fun _ => E)
    (fun W => ⌊(W : ℝ) * τ⌋₊) (rh_tendsto_floor_div hτ.le) hq.1 hq1 hq.2.1
    fun a s ha hs has => by
      have h := hC a (1 / 2) (rhInd a) (rh_isUnitSource_ind ha) s hs
      simp only [rh_travelLength_eq has] at h
      refine h.trans (ENNReal.ofReal_le_ofReal ?_)
      gcongr
      exact le_max_left _ _
  simpa only [ENNReal.rpow_one] using h

end BlockBand.Endpoints
