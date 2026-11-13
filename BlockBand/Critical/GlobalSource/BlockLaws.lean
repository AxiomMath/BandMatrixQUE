module

public import BlockBand.Critical.GlobalSource.Replacement

/-!
# Global Gaussian source: continuum versus discrete block laws

The birth time of a probe tag has a continuum law on `[0, τ]` with density proportional to the
profile; `blockIndex` sends it to a block of the remaining path, giving the continuum block law
`contBlockLaw`. Along every critical sequence this law approaches the reference weights
`contRefWeight` (`q(i)/(W m)` on the remaining path) in total variation.

* `sum_abs_contBlockLaw_sub_le` (explicit bound) and `tendsto_sum_abs_contBlockLaw_sub` (limit).
* `eq_zero_of_probeMass_eq_zero`, `sum_abs_prod_sub_prod_le`, `norm_integral_pi_sub_le`: total
  variation of product laws.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open BlockBand.Internal.Contracts.CriticalEntire

/-- The block index of a birth time `t` on the path of `L` blocks: `L - 1 - ⌊W t⌋₊` if `⌊W t⌋₊ < L`
(the position used by `probeColumns`), else `L` (no tag). -/
def blockIndex (W L : ℕ) (t : ℝ) : Fin (L + 1) :=
  if h : ⌊(W : ℝ) * t⌋₊ < L then ⟨L - 1 - ⌊(W : ℝ) * t⌋₊, by omega⟩ else Fin.last L

/-- `blockIndex` is Borel. -/
theorem measurable_blockIndex (W L : ℕ) : Measurable (blockIndex W L) := by
  have hf : Measurable fun t : ℝ => ⌊(W : ℝ) * t⌋₊ :=
    Nat.measurable_floor.comp (measurable_const.mul measurable_id)
  have : blockIndex W L = (fun k : ℕ => if h : k < L then (⟨L - 1 - k, by omega⟩ : Fin (L + 1))
      else Fin.last L) ∘ fun t : ℝ => ⌊(W : ℝ) * t⌋₊ := by
    funext t; simp [blockIndex]
  rw [this]
  exact (measurable_from_nat (f := fun k : ℕ => if h : k < L then
    (⟨L - 1 - k, by omega⟩ : Fin (L + 1)) else Fin.last L)).comp hf

/-- The birth law of a set: `(1/m) ∫_{S ∩ [0,τ]} q(t/τ) dt` (positive mass `m`). -/
theorem probeBirthLaw_toReal {τ : ℝ} {Q : C(BlockBand.Torus, ℝ)} (hQ : ∀ x, 0 ≤ Q x)
    (hm : 0 < probeMass τ Q) {S : Set ℝ} (hS : MeasurableSet S) :
    (probeBirthLaw τ Q S).toReal =
      (probeMass τ Q)⁻¹ * ∫ t in S ∩ Set.Icc 0 τ, Q (QuotientAddGroup.mk (t / τ)) := by
  unfold probeBirthLaw
  rw [withDensity_apply _ hS, Measure.restrict_restrict hS]
  have hd : ∀ t, birthDensity τ Q t = Q (QuotientAddGroup.mk (t / τ)) / probeMass τ Q := by
    intro t; simp only [birthDensity, hm, ↓reduceIte]
  simp_rw [hd]
  rw [← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t => div_nonneg (hQ _) hm.le)
    (by fun_prop), integral_div]
  ring

/-- `⌊W t⌋₊ = k ↔ k/W ≤ t < (k+1)/W` for `t ≥ 0`. -/
theorem floor_mul_eq_iff {W : ℕ} (hW : 0 < W) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    ⌊(W : ℝ) * t⌋₊ = k ↔ (k : ℝ) / W ≤ t ∧ t < ((k : ℝ) + 1) / W := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [Nat.floor_eq_iff (by positivity), div_le_iff₀ hW', lt_div_iff₀ hW']
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Birth times of block `k` within `[0,τ]` lie in `[k/W, (k+1)/W)`. -/
theorem blockSet_subset {W : ℕ} (hW : 0 < W) (τ : ℝ) (k : ℕ) :
    {t : ℝ | ⌊(W : ℝ) * t⌋₊ = k} ∩ Set.Icc 0 τ ⊆ Set.Ico ((k : ℝ) / W) (((k : ℝ) + 1) / W) := by
  rintro t ⟨h1, h2, -⟩
  exact (floor_mul_eq_iff hW h2 k).1 h1

/-- For an interior block (`(k+1)/W ≤ τ`) the birth-time set is `[k/W, (k+1)/W)`. -/
theorem blockSet_eq {W : ℕ} (hW : 0 < W) {τ : ℝ} {k : ℕ} (hk : ((k : ℝ) + 1) / W ≤ τ) :
    {t : ℝ | ⌊(W : ℝ) * t⌋₊ = k} ∩ Set.Icc 0 τ = Set.Ico ((k : ℝ) / W) (((k : ℝ) + 1) / W) := by
  refine Set.Subset.antisymm (blockSet_subset hW τ k) fun t ht => ?_
  have h0 : (0 : ℝ) ≤ (k : ℝ) / W := by positivity
  refine ⟨(floor_mul_eq_iff hW (h0.trans ht.1) k).2 ht, h0.trans ht.1, (ht.2.le.trans hk)⟩

/-- The birth-time set of a block is measurable. -/
theorem measurableSet_blockSet (W : ℕ) (τ : ℝ) (k : ℕ) :
    MeasurableSet ({t : ℝ | ⌊(W : ℝ) * t⌋₊ = k} ∩ Set.Icc 0 τ) :=
  ((Nat.measurable_floor.comp (measurable_const.mul measurable_id))
    (measurableSet_singleton k)).inter measurableSet_Icc

/-- The birth-time set of a block has length at most `1/W`. -/
theorem volume_blockSet_le {W : ℕ} (hW : 0 < W) (τ : ℝ) (k : ℕ) :
    (volume ({t : ℝ | ⌊(W : ℝ) * t⌋₊ = k} ∩ Set.Icc 0 τ)).toReal ≤ (W : ℝ)⁻¹ := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have h := measure_mono (μ := volume) (blockSet_subset hW τ k)
  rw [Real.volume_Ico] at h
  have : ((k : ℝ) + 1) / W - (k : ℝ) / W = (W : ℝ)⁻¹ := by field_simp; ring
  rw [this] at h
  exact (ENNReal.toReal_le_of_le_ofReal (by positivity) h)

/-- An interior block's birth-time set has length `1/W`. -/
theorem volume_blockSet_eq {W : ℕ} (hW : 0 < W) {τ : ℝ} {k : ℕ} (hk : ((k : ℝ) + 1) / W ≤ τ) :
    (volume ({t : ℝ | ⌊(W : ℝ) * t⌋₊ = k} ∩ Set.Icc 0 τ)).toReal = (W : ℝ)⁻¹ := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [blockSet_eq hW hk, Real.volume_Ico, ENNReal.toReal_ofReal (by
    rw [sub_nonneg]; gcongr; linarith)]
  field_simp; ring

/-- **Per-block Riemann estimate**: for a uniformly continuous profile (`|x - y| ≤ δ ⇒ |q(x) - q(y)| ≤ η`)
and `1/(τW) + |n/(τW) - 1| + 2/n ≤ δ`, `|∫_{block k} q(t/τ) dt - W⁻¹ q((k+2)/n)| ≤ η/W` for interior
blocks and `≤ η/W + qmax/W` otherwise (`k ≤ n`). -/
theorem block_estimate {τ : ℝ} (hτ : 0 < τ) {Q : C(BlockBand.Torus, ℝ)} {qmax η δ : ℝ}
    (hqmax : ∀ x, ‖Q x‖ ≤ qmax) (hUC : ∀ x y : ℝ, |x - y| ≤ δ →
      |Q (QuotientAddGroup.mk x) - Q (QuotientAddGroup.mk y)| ≤ η)
    {W n : ℕ} (hW : 0 < W) (hn : 0 < n)
    (hδ : 1 / (τ * W) + |(n : ℝ) / (τ * W) - 1| + 2 / n ≤ δ) {k : ℕ} (hk : k ≤ n) :
    |(∫ t in {t : ℝ | ⌊(W : ℝ) * t⌋₊ = k} ∩ Set.Icc 0 τ, Q (QuotientAddGroup.mk (t / τ))) -
        (W : ℝ)⁻¹ * Q (QuotientAddGroup.mk (((k : ℝ) + 2) / n))| ≤
      η / W + (if ((k : ℝ) + 1) / W ≤ τ then 0 else qmax / W) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set A := {t : ℝ | ⌊(W : ℝ) * t⌋₊ = k} ∩ Set.Icc 0 τ
  set c := Q (QuotientAddGroup.mk (((k : ℝ) + 2) / n))
  have hAfin : volume A < ⊤ := (measure_mono Set.inter_subset_right).trans_lt
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
  have hint : IntegrableOn (fun t : ℝ => Q (QuotientAddGroup.mk (t / τ))) A := by
    refine IntegrableOn.mono_set ?_ Set.inter_subset_right
    exact (by fun_prop : Continuous fun t : ℝ => Q (QuotientAddGroup.mk (t / τ))).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hsplit : (∫ t in A, Q (QuotientAddGroup.mk (t / τ))) - (W : ℝ)⁻¹ * c =
      (∫ t in A, (Q (QuotientAddGroup.mk (t / τ)) - c)) +
        ((volume A).toReal - (W : ℝ)⁻¹) * c := by
    rw [integral_sub hint (integrableOn_const hAfin.ne), setIntegral_const, smul_eq_mul,
      Measure.real]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · -- the oscillation term
    have hb : ∀ t ∈ A, ‖Q (QuotientAddGroup.mk (t / τ)) - c‖ ≤ η := by
      rintro t ⟨ht1, ht2, -⟩
      rw [Real.norm_eq_abs]
      refine hUC _ _ ?_
      have hfl := (floor_mul_eq_iff hW ht2 k).1 ht1
      have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
      -- |t/τ - (k+2)/n| ≤ 1/(τW) + |n/(τW) - 1| + 2/n
      have e1 : |t / τ - (k : ℝ) / (τ * W)| ≤ 1 / (τ * W) := by
        have key : t / τ - (k : ℝ) / (τ * W) = ((W : ℝ) * t - k) / (τ * W) := by
          field_simp
        rw [key, abs_div, abs_of_pos (by positivity : (0:ℝ) < τ * W)]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have h1 := hfl.1
        have h2 := hfl.2
        rw [div_le_iff₀ hW'] at h1
        rw [lt_div_iff₀ hW'] at h2
        rw [abs_le]; constructor <;> nlinarith
      have e2 : |(k : ℝ) / (τ * W) - (k : ℝ) / n| ≤ |(n : ℝ) / (τ * W) - 1| := by
        have : (k : ℝ) / (τ * W) - (k : ℝ) / n = ((k : ℝ) / n) * ((n : ℝ) / (τ * W) - 1) := by
          field_simp
        rw [this, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) / n)]
        have : (k : ℝ) / n ≤ 1 := by rw [div_le_one hn']; exact hkn
        exact mul_le_of_le_one_left (abs_nonneg _) this
      have e3 : |(k : ℝ) / n - ((k : ℝ) + 2) / n| = 2 / n := by
        rw [div_sub_div_same, show (k : ℝ) - (k + 2) = -2 by ring, abs_div, abs_neg,
          abs_of_pos hn']; norm_num
      calc |t / τ - ((k : ℝ) + 2) / n| ≤ |t / τ - (k : ℝ) / (τ * W)| +
            |(k : ℝ) / (τ * W) - (k : ℝ) / n| + |(k : ℝ) / n - ((k : ℝ) + 2) / n| := by
            have := abs_sub_le (t / τ) ((k : ℝ) / (τ * W)) (((k : ℝ) + 2) / n)
            have := abs_sub_le ((k : ℝ) / (τ * W)) ((k : ℝ) / n) (((k : ℝ) + 2) / n)
            linarith
        _ ≤ δ := by rw [e3]; linarith
    have := norm_setIntegral_le_of_norm_le_const hAfin hb
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    rw [Measure.real, div_eq_mul_inv]
    have hη : 0 ≤ η := (abs_nonneg _).trans (hUC 0 0 (by simp; exact
      (by positivity : (0:ℝ) ≤ 1 / (τ * W) + |(n : ℝ) / (τ * W) - 1| + 2 / n).trans hδ))
    have hv : (volume A).toReal ≤ (W : ℝ)⁻¹ := volume_blockSet_le hW τ k
    nlinarith
  · split_ifs with hk1
    · rw [volume_blockSet_eq hW hk1, sub_self, zero_mul, abs_zero]
    · rw [abs_mul]
      have h1 : |(volume A).toReal - (W : ℝ)⁻¹| ≤ (W : ℝ)⁻¹ := by
        rw [abs_le]; constructor
        · have := ENNReal.toReal_nonneg (a := volume A); linarith
        · have : (volume A).toReal ≤ (W : ℝ)⁻¹ := volume_blockSet_le hW τ k
          have : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
          linarith
      have h2 : |c| ≤ qmax := (Real.norm_eq_abs c) ▸ hqmax _
      calc |(volume A).toReal - (W : ℝ)⁻¹| * |c| ≤ (W : ℝ)⁻¹ * qmax :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = qmax / W := by rw [div_eq_mul_inv, mul_comm]

/-- **Continuum block law** of one tag: the image of `probeBirthLaw` under `blockIndex`
(`k = ⌊Wt⌋`); a zero-mass group has no tag. -/
def contBlockLaw (τ : ℝ) (Q : C(BlockBand.Torus, ℝ)) (W L : ℕ) : Measure (Fin (L + 1)) :=
  if 0 < probeMass τ Q then (probeBirthLaw τ Q).map (blockIndex W L) else Measure.dirac (Fin.last L)

/-- Birth times sent to block `i`. -/
theorem blockIndex_preimage_castSucc (W L : ℕ) (i : Fin L) :
    blockIndex W L ⁻¹' {i.castSucc} = {t : ℝ | ⌊(W : ℝ) * t⌋₊ = L - 1 - i} := by
  ext t
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, blockIndex]
  split_ifs with h
  · rw [Fin.ext_iff]; simp only [Fin.val_castSucc]; omega
  · rw [Fin.ext_iff]; simp only [Fin.val_last, Fin.val_castSucc]; omega

/-- Birth times beyond the path (no tag). -/
theorem blockIndex_preimage_last (W L : ℕ) :
    blockIndex W L ⁻¹' {Fin.last L} = {t : ℝ | L ≤ ⌊(W : ℝ) * t⌋₊} := by
  ext t
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, blockIndex]
  split_ifs with h
  · rw [Fin.ext_iff]; simp only [Fin.val_last]; omega
  · simp; omega

/-- The probability of no tag is at most `(qmax/m) max(τ - L/W, 0)`. -/
theorem contBlockLaw_last_le {τ : ℝ} {Q : C(BlockBand.Torus, ℝ)} (hQ : ∀ x, 0 ≤ Q x)
    (hm : 0 < probeMass τ Q) {qmax : ℝ} (hqmax : ∀ x, ‖Q x‖ ≤ qmax) {W L : ℕ} (hW : 0 < W) :
    (contBlockLaw τ Q W L {Fin.last L}).toReal ≤
      (probeMass τ Q)⁻¹ * (qmax * max (τ - (L : ℝ) / W) 0) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  simp only [contBlockLaw, hm, ↓reduceIte]
  rw [Measure.map_apply (measurable_blockIndex W L) (measurableSet_singleton _),
    blockIndex_preimage_last]
  have hS : MeasurableSet {t : ℝ | L ≤ ⌊(W : ℝ) * t⌋₊} :=
    (Nat.measurable_floor.comp (measurable_const.mul measurable_id)) measurableSet_Ici
  rw [probeBirthLaw_toReal hQ hm hS]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hm.le)
  set A := {t : ℝ | L ≤ ⌊(W : ℝ) * t⌋₊} ∩ Set.Icc 0 τ
  have hsub : A ⊆ Set.Icc ((L : ℝ) / W) τ := by
    rintro t ⟨h1, h2, h3⟩
    refine ⟨?_, h3⟩
    rw [div_le_iff₀ hW']
    have := Nat.floor_le (by positivity : (0 : ℝ) ≤ (W : ℝ) * t)
    have h1' : (L : ℝ) ≤ ⌊(W : ℝ) * t⌋₊ := by exact_mod_cast h1
    linarith
  have hAfin : volume A < ⊤ := (measure_mono Set.inter_subset_right).trans_lt
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
  have hb := norm_setIntegral_le_of_norm_le_const hAfin (C := qmax)
    (f := fun t => Q (QuotientAddGroup.mk (t / τ))) fun t _ => hqmax _
  rw [Real.norm_eq_abs] at hb
  refine (le_abs_self _).trans (hb.trans ?_)
  have hq0 : 0 ≤ qmax := (norm_nonneg _).trans (hqmax 0)
  refine mul_le_mul_of_nonneg_left ?_ hq0
  rw [Measure.real]
  have := measure_mono (μ := volume) hsub
  rw [Real.volume_Icc] at this
  exact (ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) (this.trans
    (ENNReal.ofReal_le_ofReal (le_max_left _ _))))

/-- Reference weights `q(i)/(W m)` on the remaining path (`q = pathProfileValue`), `0` for no tag. -/
def contRefWeight (τ : ℝ) (Q : C(BlockBand.Torus, ℝ)) (W n : ℕ)
    (o : Fin (probePathLength n + 1)) : ℝ :=
  if h : o.val < probePathLength n then
    pathProfileValue n Q ⟨o.val, h⟩ / ((W : ℝ) * probeMass τ Q) else 0

/-- At most `L - ⌊τW⌋₊` blocks of the path are not interior. -/
theorem sum_ite_bad_le (W L : ℕ) (hW : 0 < W) {τ c : ℝ} (hτ : 0 ≤ τ) (hc : 0 ≤ c) :
    ∑ i : Fin L, (if (((L - 1 - i.val : ℕ) : ℝ) + 1) / W ≤ τ then 0 else c) ≤
      c * ((L - ⌊τ * W⌋₊ : ℕ) : ℝ) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hrev : ∑ i : Fin L, (if (((L - 1 - i.val : ℕ) : ℝ) + 1) / W ≤ τ then 0 else c) =
      ∑ i : Fin L, (if (((i.val : ℕ) : ℝ) + 1) / W ≤ τ then 0 else c) := by
    refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
    simp only [Fin.revPerm_apply, Fin.val_rev]
    rw [show L - (i.val + 1) = L - 1 - i.val by omega]
  rw [hrev, Fin.sum_univ_eq_sum_range (fun i => if ((i : ℝ) + 1) / W ≤ τ then 0 else c)]
  calc ∑ i ∈ Finset.range L, (if ((i : ℝ) + 1) / W ≤ τ then 0 else c)
      ≤ ∑ i ∈ Finset.range L, (if ⌊τ * W⌋₊ ≤ i then c else 0) := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs with h1 h2 h2
        · exact hc
        · exact le_rfl
        · exact le_rfl
        · exfalso; apply h1
          rw [div_le_iff₀ hW']
          have : i + 1 ≤ ⌊τ * W⌋₊ := by omega
          have h3 : ((i : ℝ) + 1) ≤ ⌊τ * W⌋₊ := by exact_mod_cast this
          have := Nat.floor_le (by positivity : (0 : ℝ) ≤ τ * W)
          linarith
    _ = c * (((Finset.range L).filter (fun i => ⌊τ * W⌋₊ ≤ i)).card : ℝ) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          mul_comm]
    _ ≤ c * ((L - ⌊τ * W⌋₊ : ℕ) : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ hc
        have : (Finset.range L).filter (fun i => ⌊τ * W⌋₊ ≤ i) ⊆ Finset.Ico ⌊τ * W⌋₊ L := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi
          exact Finset.mem_Ico.2 ⟨hi.2, hi.1⟩
        have h := Finset.card_le_card this
        rw [Nat.card_Ico] at h
        exact_mod_cast h

/-- **Explicit total-variation bound** between the continuum block law and the reference weights
(remaining path of `n - 3` blocks, positive mass `m`):
`Σ_o |P(o) - v(o)| ≤ m⁻¹ (L η/W + qmax (L - ⌊τW⌋₊)/W + qmax max(τ - L/W, 0))`. -/
theorem sum_abs_contBlockLaw_sub_le {τ : ℝ} (hτ : 0 < τ) {Q : C(BlockBand.Torus, ℝ)}
    (hQ : ∀ x, 0 ≤ Q x) (hm : 0 < probeMass τ Q) {qmax η δ : ℝ}
    (hqmax : ∀ x, ‖Q x‖ ≤ qmax) (hUC : ∀ x y : ℝ, |x - y| ≤ δ →
      |Q (QuotientAddGroup.mk x) - Q (QuotientAddGroup.mk y)| ≤ η)
    {W n : ℕ} (hW : 0 < W) (hn : 4 ≤ n)
    (hδ : 1 / (τ * W) + |(n : ℝ) / (τ * W) - 1| + 2 / n ≤ δ) :
    ∑ o, |(contBlockLaw τ Q W (probePathLength n) {o}).toReal - contRefWeight τ Q W n o| ≤
      (probeMass τ Q)⁻¹ * ((probePathLength n : ℝ) * η / W +
        qmax * ((probePathLength n - ⌊τ * W⌋₊ : ℕ) : ℝ) / W +
        qmax * max (τ - (probePathLength n : ℝ) / W) 0) := by
  set L := probePathLength n with hL
  set m := probeMass τ Q
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hq0 : 0 ≤ qmax := (norm_nonneg _).trans (hqmax 0)
  rw [Fin.sum_univ_castSucc]
  have hlast : contRefWeight τ Q W n (Fin.last L) = 0 := by
    simp [contRefWeight, L]
  rw [hlast, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  have hblock : ∀ i : Fin L,
      |(contBlockLaw τ Q W L {i.castSucc}).toReal - contRefWeight τ Q W n i.castSucc| ≤
        m⁻¹ * (η / W + (if (((L - 1 - i.val : ℕ) : ℝ) + 1) / W ≤ τ then 0 else qmax / W)) := by
    intro i
    have hS : MeasurableSet {t : ℝ | ⌊(W : ℝ) * t⌋₊ = L - 1 - i} :=
      (Nat.measurable_floor.comp (measurable_const.mul measurable_id)) (measurableSet_singleton _)
    have hcb : contBlockLaw τ Q W L = (probeBirthLaw τ Q).map (blockIndex W L) := by
      have hm' : 0 < probeMass τ Q := hm
      simp [contBlockLaw, hm']
    rw [hcb, Measure.map_apply (measurable_blockIndex W L) (measurableSet_singleton _),
      blockIndex_preimage_castSucc, probeBirthLaw_toReal hQ hm hS]
    have hv : contRefWeight τ Q W n i.castSucc = m⁻¹ * ((W : ℝ)⁻¹ *
        Q (QuotientAddGroup.mk ((((L - 1 - i.val : ℕ) : ℝ) + 2) / n))) := by
      have hi : i.val < probePathLength n := i.isLt
      simp only [contRefWeight, Fin.val_castSucc, hi, ↓reduceDIte, pathProfileValue,
        pathRingBlock]
      have : ((n - 2 - i.val : ℕ) : ℝ) = ((L - 1 - i.val : ℕ) : ℝ) + 2 := by
        have hi := i.isLt
        simp only [hL, probePathLength] at hi ⊢
        rw [show n - 2 - i.val = (n - 3 - 1 - i.val) + 2 by omega]
        push_cast; ring
      rw [this]
      have hm' : probeMass τ Q ≠ 0 := hm.ne'
      field_simp
      rfl
    rw [hv, ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hm)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hm.le)
    have hk : L - 1 - i.val ≤ n := by simp only [hL, probePathLength]; omega
    exact block_estimate hτ hqmax hUC hW (by omega) hδ hk
  calc ∑ i : Fin L, |(contBlockLaw τ Q W L {i.castSucc}).toReal -
          contRefWeight τ Q W n i.castSucc| + (contBlockLaw τ Q W L {Fin.last L}).toReal
      ≤ ∑ i : Fin L, m⁻¹ * (η / W + (if (((L - 1 - i.val : ℕ) : ℝ) + 1) / W ≤ τ then 0
          else qmax / W)) + m⁻¹ * (qmax * max (τ - (L : ℝ) / W) 0) :=
        add_le_add (Finset.sum_le_sum fun i _ => hblock i)
          (contBlockLaw_last_le hQ hm hqmax hW)
    _ ≤ m⁻¹ * ((L : ℝ) * η / W + qmax * ((L - ⌊τ * W⌋₊ : ℕ) : ℝ) / W +
          qmax * max (τ - (L : ℝ) / W) 0) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hm.le)
        have := sum_ite_bad_le W L hW hτ.le (div_nonneg hq0 hW'.le)
        have e : (L : ℝ) * (η / W) = (L : ℝ) * η / W := by ring
        have e2 : qmax / W * ((L - ⌊τ * W⌋₊ : ℕ) : ℝ) = qmax * ((L - ⌊τ * W⌋₊ : ℕ) : ℝ) / W := by
          ring
        linarith

/-- A continuous profile on the torus is uniformly continuous on `ℝ`. -/
theorem uniformContinuous_comp_mk (Q : C(BlockBand.Torus, ℝ)) :
    UniformContinuous fun x : ℝ => Q (QuotientAddGroup.mk x : BlockBand.Torus) := by
  have hmk : LipschitzWith 1 (QuotientAddGroup.mk : ℝ → BlockBand.Torus) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, ← QuotientAddGroup.mk_sub, NNReal.coe_one, one_mul]
    exact QuotientAddGroup.norm_mk_le_norm
  exact (CompactSpace.uniformContinuous_of_continuous Q.continuous).comp hmk.uniformContinuous

/-- `(L - f)/W ≤ |L/W - f/W|` for truncated subtraction. -/
theorem natCast_sub_div_le (L f W : ℕ) :
    ((L - f : ℕ) : ℝ) / W ≤ |(L : ℝ) / W - (f : ℝ) / W| := by
  rcases le_total f L with h | h
  · rw [Nat.cast_sub h, sub_div]; exact le_abs_self _
  · rw [Nat.sub_eq_zero_of_le h]; simp

/-- **Riemann convergence of the block laws**: along every critical sequence, for a
nonnegative continuous profile of positive mass, the continuum block law of a tag on the remaining
path approaches the reference weights `q(i)/(W m)` in total variation. -/
theorem tendsto_sum_abs_contBlockLaw_sub {τ : ℝ} (hτ : 0 < τ) {Q : C(BlockBand.Torus, ℝ)}
    (hQ : ∀ x, 0 ≤ Q x) (hm : 0 < probeMass τ Q) (s : BlockBand.CriticalSequence τ) :
    Tendsto (fun j => ∑ o, |(contBlockLaw τ Q (s.W j) (probePathLength (s.n j)) {o}).toReal -
      contRefWeight τ Q (s.W j) (s.n j) o|) atTop (𝓝 0) := by
  set m := probeMass τ Q
  set qmax := ‖Q‖
  have hqmax : ∀ x, ‖Q x‖ ≤ qmax := fun x => Q.norm_coe_le_norm x
  have hq0 : 0 ≤ qmax := norm_nonneg _
  have hWr : Tendsto (fun j => (s.W j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp s.width_tendsto
  have hWpos : ∀ j, (0 : ℝ) < s.W j := fun j => by exact_mod_cast s.W_pos j
  have hLW := tendsto_probePathLength_div τ s
  have he1 : Tendsto (fun j => |(probePathLength (s.n j) : ℝ) / s.W j -
      (⌊τ * s.W j⌋₊ : ℝ) / s.W j|) atTop (𝓝 0) := by
    have hf : Tendsto (fun j => (⌊τ * s.W j⌋₊ : ℝ) / s.W j) atTop (𝓝 τ) :=
      (tendsto_nat_floor_mul_div_atTop hτ.le).comp hWr
    simpa using (hLW.sub hf).abs
  have he2 : Tendsto (fun j => max (τ - (probePathLength (s.n j) : ℝ) / s.W j) 0) atTop
      (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := τ)).sub hLW).max (tendsto_const_nhds (x := (0 : ℝ)))
    simpa using h
  have hδ : Tendsto (fun j => 1 / (τ * s.W j) + |(s.n j : ℝ) / (τ * s.W j) - 1| +
      2 / (s.n j : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => 1 / (τ * s.W j)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hWr.const_mul_atTop hτ)
    have h2 : Tendsto (fun j => |(s.n j : ℝ) / (τ * s.W j) - 1|) atTop (𝓝 0) := by
      have := (s.ratio_tendsto.div_const τ).sub (tendsto_const_nhds (x := (1 : ℝ)))
      rw [div_self hτ.ne', sub_self] at this
      refine (this.abs.congr fun j => ?_).trans (by simp)
      rw [div_div, mul_comm (s.W j : ℝ) τ]
    have h3 : Tendsto (fun j => 2 / (s.n j : ℝ)) atTop (𝓝 0) := by
      have h2W : Tendsto (fun j => 2 / (s.W j : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hWr
      have := h2W.div s.ratio_tendsto hτ.ne'
      rw [zero_div] at this
      refine this.congr fun j => ?_
      have := hWpos j
      simp only [Pi.div_apply]
      field_simp
    simpa using (h1.add h2).add h3
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun j =>
    ha.trans_le (Finset.sum_nonneg fun o _ => abs_nonneg _), fun ε hε => ?_⟩
  set η := ε * m / (4 * (τ + 1))
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδpos, hδUC⟩ := Metric.uniformContinuous_iff.1 (uniformContinuous_comp_mk Q) η hη
  have hUC : ∀ x y : ℝ, |x - y| ≤ δ / 2 →
      |Q (QuotientAddGroup.mk x) - Q (QuotientAddGroup.mk y)| ≤ η := by
    intro x y h
    have := hδUC (a := x) (b := y) (by rw [Real.dist_eq]; linarith)
    rw [Real.dist_eq] at this
    exact this.le
  have hE := ((he1.add he2).const_mul (m⁻¹ * qmax)).eventually
    (gt_mem_nhds (show m⁻¹ * qmax * (0 + 0) < ε / 2 by simp; positivity))
  filter_upwards [hδ.eventually (ge_mem_nhds (half_pos hδpos)),
    hLW.eventually (ge_mem_nhds (show τ < τ + 1 by linarith)), hE] with j hj1 hj2 hj3
  have hb := sum_abs_contBlockLaw_sub_le hτ hQ hm hqmax hUC (s.W_pos j) (s.n_ge_four j) hj1
  refine hb.trans_lt ?_
  have hW := hWpos j
  have hsub := natCast_sub_div_le (probePathLength (s.n j)) ⌊τ * s.W j⌋₊ (s.W j)
  have hmi : 0 < m⁻¹ := inv_pos.2 hm
  have k1 : m⁻¹ * ((probePathLength (s.n j) : ℝ) * η / s.W j) ≤ ε / 4 := by
    have : (probePathLength (s.n j) : ℝ) * η / s.W j =
        ((probePathLength (s.n j) : ℝ) / s.W j) * η := by ring
    rw [this]
    calc m⁻¹ * (((probePathLength (s.n j) : ℝ) / s.W j) * η) ≤ m⁻¹ * ((τ + 1) * η) := by
          gcongr
      _ = ε / 4 := by simp only [η]; field_simp
  have k2 : m⁻¹ * (qmax * ((probePathLength (s.n j) - ⌊τ * s.W j⌋₊ : ℕ) : ℝ) / s.W j +
      qmax * max (τ - (probePathLength (s.n j) : ℝ) / s.W j) 0) <  ε / 2 := by
    refine lt_of_le_of_lt ?_ hj3
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hmi.le
    rw [mul_add, mul_div_assoc]
    gcongr
  calc m⁻¹ * ((probePathLength (s.n j) : ℝ) * η / s.W j +
        qmax * ((probePathLength (s.n j) - ⌊τ * s.W j⌋₊ : ℕ) : ℝ) / s.W j +
        qmax * max (τ - (probePathLength (s.n j) : ℝ) / s.W j) 0)
      = m⁻¹ * ((probePathLength (s.n j) : ℝ) * η / s.W j) +
        m⁻¹ * (qmax * ((probePathLength (s.n j) - ⌊τ * s.W j⌋₊ : ℕ) : ℝ) / s.W j +
          qmax * max (τ - (probePathLength (s.n j) : ℝ) / s.W j) 0) := by ring
    _ < ε / 4 + ε / 2 := add_lt_add_of_le_of_lt k1 k2
    _ < ε := by linarith

/-- A nonnegative continuous profile with zero mass vanishes identically. -/
theorem eq_zero_of_probeMass_eq_zero {τ : ℝ} (hτ : 0 < τ) {Q : C(BlockBand.Torus, ℝ)}
    (hQ : ∀ x, 0 ≤ Q x) (hm : probeMass τ Q = 0) (x : BlockBand.Torus) : Q x = 0 := by
  have hint : ∫ r, Q r = 0 := by
    unfold probeMass at hm
    rcases mul_eq_zero.1 hm with h | h
    · exact absurd h hτ.ne'
    · exact h
  have hi : Integrable (fun r => Q r) (volume : Measure BlockBand.Torus) :=
    Q.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun r => hQ r) hi).1 hint
  have := (Continuous.ae_eq_iff_eq volume Q.continuous continuous_const).1 hae
  exact congrFun this x

/-- Telescoping: the total variation of product probability vectors is at most the sum of the coordinate total variations. -/
theorem sum_abs_prod_sub_prod_le {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]
    (a b : ι → K → ℝ) (ha : ∀ i k, 0 ≤ a i k) (hb : ∀ i k, 0 ≤ b i k)
    (ha1 : ∀ i, ∑ k, a i k = 1) (hb1 : ∀ i, ∑ k, b i k = 1) :
    ∑ κ : ι → K, |∏ i, a i (κ i) - ∏ i, b i (κ i)| ≤ ∑ i, ∑ k, |a i k - b i k| := by
  classical
  let c : Finset ι → ι → K → ℝ := fun s i => if i ∈ s then a i else b i
  have hc0 : ∀ s i k, 0 ≤ c s i k := fun s i k => by
    simp only [c]; split_ifs; exacts [ha i k, hb i k]
  have hc1 : ∀ s i, ∑ k, c s i k = 1 := fun s i => by
    simp only [c]; split_ifs; exacts [ha1 i, hb1 i]
  have key : ∀ s : Finset ι, ∑ κ : ι → K, |∏ i, c s i (κ i) - ∏ i, b i (κ i)| ≤
      ∑ i ∈ s, ∑ k, |a i k - b i k| := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [c]
    | insert j s hj ih =>
      have hstep : ∀ κ : ι → K, |∏ i, c (insert j s) i (κ i) - ∏ i, c s i (κ i)| =
          ∏ i, (if i = j then fun k => |a j k - b j k| else c s i) (κ i) := by
        intro κ
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
          ← Finset.mul_prod_erase Finset.univ (fun i => c s i (κ i)) (Finset.mem_univ j),
          ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        have he : ∏ i ∈ Finset.univ.erase j, c (insert j s) i (κ i) =
            ∏ i ∈ Finset.univ.erase j, c s i (κ i) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have hij : i ≠ j := Finset.ne_of_mem_erase hi
          simp [c, Finset.mem_insert, hij]
        have he2 : ∏ i ∈ Finset.univ.erase j,
            (if i = j then fun k => |a j k - b j k| else c s i) (κ i) =
            ∏ i ∈ Finset.univ.erase j, c s i (κ i) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          simp [Finset.ne_of_mem_erase hi]
        rw [he, he2, ← sub_mul, abs_mul, abs_of_nonneg (Finset.prod_nonneg fun i _ => hc0 s i _)]
        simp [c, hj]
      calc ∑ κ : ι → K, |∏ i, c (insert j s) i (κ i) - ∏ i, b i (κ i)|
          ≤ ∑ κ : ι → K, (|∏ i, c (insert j s) i (κ i) - ∏ i, c s i (κ i)| +
              |∏ i, c s i (κ i) - ∏ i, b i (κ i)|) :=
            Finset.sum_le_sum fun κ _ => abs_sub_le _ _ _
        _ = ∑ k, |a j k - b j k| + ∑ κ : ι → K, |∏ i, c s i (κ i) - ∏ i, b i (κ i)| := by
            rw [Finset.sum_add_distrib]
            congr 1
            simp_rw [hstep]
            rw [← Fintype.prod_sum]
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
            simp only [ite_true]
            rw [Finset.prod_eq_one fun i hi => by
              simp only [Finset.ne_of_mem_erase hi, ite_false]; exact hc1 s i, mul_one]
        _ ≤ ∑ k, |a j k - b j k| + ∑ i ∈ s, ∑ k, |a i k - b i k| := by gcongr
        _ = ∑ i ∈ insert j s, ∑ k, |a i k - b i k| := by rw [Finset.sum_insert hj]
  have h := key Finset.univ
  simp only [c, Finset.mem_univ, ite_true] at h
  exact h.trans (le_of_eq rfl)

/-- **Total-variation bound for product laws** on a finite space: for a test bounded by `1`,
`|∫ h d(Π μ_i) - ∫ h d(Π ν_i)| ≤ Σ_i Σ_k |μ_i{k} - ν_i{k}|`. -/
theorem norm_integral_pi_sub_le {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]
    [MeasurableSpace K] [MeasurableSingletonClass K] (μ ν : ι → Measure K)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (h : (ι → K) → ℂ) (hh : ∀ κ, ‖h κ‖ ≤ 1) :
    ‖∫ κ, h κ ∂Measure.pi μ - ∫ κ, h κ ∂Measure.pi ν‖ ≤
      ∑ i, ∑ k, |(μ i).real {k} - (ν i).real {k}| := by
  classical
  have hmeas : Measurable h := measurable_of_countable h
  have hint : ∀ P : Measure (ι → K), IsFiniteMeasure P → Integrable h P := fun P _ =>
    (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable (Eventually.of_forall hh)
  have hpi : ∀ (P : ι → Measure K) [∀ i, IsProbabilityMeasure (P i)] (κ : ι → K),
      (Measure.pi P).real {κ} = ∏ i, (P i).real {κ i} := by
    intro P _ κ
    rw [Measure.real, ← Set.univ_pi_singleton, Measure.pi_pi, ENNReal.toReal_prod]
    rfl
  rw [integral_fintype (hint _ inferInstance), integral_fintype (hint _ inferInstance),
    ← Finset.sum_sub_distrib]
  simp_rw [hpi, ← sub_smul]
  refine (norm_sum_le _ _).trans ?_
  have hsum1 : ∀ (P : ι → Measure K) [∀ i, IsProbabilityMeasure (P i)] (i : ι),
      ∑ k, (P i).real {k} = 1 := by
    intro P _ i
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  refine le_trans (Finset.sum_le_sum fun κ _ => ?_) (sum_abs_prod_sub_prod_le
    (fun i k => (μ i).real {k}) (fun i k => (ν i).real {k}) (fun _ _ => measureReal_nonneg)
    (fun _ _ => measureReal_nonneg) (hsum1 μ) (hsum1 ν))
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (hh κ)

end BlockBand.Critical.GlobalSource
