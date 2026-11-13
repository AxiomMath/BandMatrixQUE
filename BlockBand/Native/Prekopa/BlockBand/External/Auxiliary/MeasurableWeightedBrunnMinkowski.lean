module

public import BlockBand.Native.Prekopa.BlockBand.External.Auxiliary.ScalarPrekopaLeindlerAssembly
public import BlockBand.Native.Prekopa.BlockBand.External.Auxiliary.CenteredIntervalRearrangement
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.Order.Compact

/-!
# Measurable one-dimensional weighted Brunn–Minkowski

This module proves the extended-nonnegative-real inequality
`MeasurableWeightedBrunnMinkowski` used by the scalar
Prékopa–Leindler assembly.  The proof is one-dimensional: compact sets are cut
at an attained extreme point, and arbitrary measurable finite-volume sets are
reached by compact inner regularity of Lebesgue measure.

Both this module and the assembly state the unrestricted measurable-set
inequality in `ℝ≥0∞`, so an infinite-volume target is handled automatically.
The intermediate `Measure.real` lemma below is used only in the finite-target
branch of that proof.  No integral or scalar Prékopa–Leindler statement is used.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PrekopaNative.BlockBand

open MeasureTheory Set
open scoped ENNReal Pointwise

private theorem volume_smul_set_of_pos (S : Set ℝ) {a : ℝ} (ha : 0 < a) :
    volume (a • S) = ENNReal.ofReal a * volume S := by
  have hset : a • S = (fun x : ℝ => a⁻¹ * x) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [ha.ne'] using hy
    · intro hx
      refine ⟨a⁻¹ * x, hx, ?_⟩
      simp [ha.ne']
  rw [hset, Real.volume_preimage_mul_left (inv_ne_zero ha.ne')]
  simp [abs_of_pos ha]

/-- The one-dimensional Brunn–Minkowski estimate for nonempty compact sets.
The two translated copies are separated by the sum of an attained maximum and
an attained minimum, and overlap only in that (Lebesgue-null) point. -/
theorem weightedBrunnMinkowskiData_isCompact
    {K L : Set ℝ} (hK : IsCompact K) (hL : IsCompact L)
    (hKn : K.Nonempty) (hLn : L.Nonempty)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    WeightedBrunnMinkowskiData K L a b := by
  let S : Set ℝ := a • K
  let T : Set ℝ := b • L
  have hSc : IsCompact S := hK.smul a
  have hTc : IsCompact T := hL.smul b
  have hSn : S.Nonempty := by
    rcases hKn with ⟨k, hk⟩
    exact ⟨a * k, ⟨k, hk, rfl⟩⟩
  have hTn : T.Nonempty := by
    rcases hLn with ⟨l, hl⟩
    exact ⟨b * l, ⟨l, hl, rfl⟩⟩
  obtain ⟨smax, hsmax⟩ := hSc.exists_isGreatest hSn
  obtain ⟨tmin, htmin⟩ := hTc.exists_isLeast hTn
  let U : Set ℝ := tmin +ᵥ S
  let V : Set ℝ := smax +ᵥ T
  have hUc : IsCompact U := hSc.vadd tmin
  have hVc : IsCompact V := hTc.vadd smax
  have hinter : U ∩ V ⊆ {smax + tmin} := by
    intro z hz
    rcases hz.1 with ⟨s, hs, rfl⟩
    rcases hz.2 with ⟨t, ht, heq⟩
    have hle : tmin + s ≤ tmin + smax := by
      simpa [add_comm] using add_le_add_left (hsmax.2 hs) tmin
    have hge : tmin + smax ≤ smax + t := by
      simpa [add_comm] using add_le_add_left (htmin.2 ht) smax
    have : tmin + s = smax + t := heq.symm
    have he : tmin + s = tmin + smax := le_antisymm hle (this ▸ hge)
    simpa [add_comm] using he
  have hdisj : AEDisjoint volume U V := by
    apply measure_mono_null hinter
    exact measure_singleton (smax + tmin)
  have hunion : U ∪ V ⊆ S + T := by
    intro z hz
    rcases hz with hz | hz
    · rcases hz with ⟨s, hs, rfl⟩
      exact ⟨s, hs, tmin, htmin.1, by simp [add_comm]
        ⟩
    · rcases hz with ⟨t, ht, rfl⟩
      exact ⟨smax, hsmax.1, t, ht, rfl⟩
  have hmeasure : volume S + volume T ≤ volume (S + T) := by
    rw [← measure_vadd volume tmin S, ← measure_vadd volume smax T]
    rw [← measure_union₀ hVc.measurableSet.nullMeasurableSet hdisj]
    exact measure_mono hunion
  rw [WeightedBrunnMinkowskiData]
  have hSt : volume S ≠ ∞ := hSc.measure_lt_top.ne
  have hTt : volume T ≠ ∞ := hTc.measure_lt_top.ne
  have hSTt : volume (S + T) ≠ ∞ := (hSc.add hTc).measure_lt_top.ne
  have hreal := ENNReal.toReal_mono hSTt hmeasure
  dsimp [S, T] at hreal
  rw [ENNReal.toReal_add hSt hTt, volume_smul_set_of_pos K ha,
    volume_smul_set_of_pos L hb] at hreal
  simpa [Measure.real, ENNReal.toReal_mul, ha.le, hb.le] using hreal

/-- Real-valued weighted Brunn–Minkowski for nonempty measurable finite-volume
subsets of `ℝ` whose weighted Minkowski sum also has finite volume. Compact
inner approximants are made nonempty by adjoining one source point, and the
compact estimate is passed to the limit in real measure. -/
theorem weightedBrunnMinkowskiData_of_measurable_of_ne_top
    {A B : Set ℝ} (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hAf : volume A ≠ ∞) (hBf : volume B ≠ ∞)
    (hAn : A.Nonempty) (hBn : B.Nonempty)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hTarget : volume (a • A + b • B) ≠ ∞) :
    WeightedBrunnMinkowskiData A B a b := by
  rw [WeightedBrunnMinkowskiData]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨xA, hxA⟩ := hAn
  obtain ⟨xB, hxB⟩ := hBn
  obtain ⟨K₀, hK₀A, hK₀c, hKA⟩ :=
    hAm.exists_isCompact_lt_add hAf (ENNReal.ofReal_pos.mpr hε).ne'
  obtain ⟨L₀, hL₀B, hL₀c, hLB⟩ :=
    hBm.exists_isCompact_lt_add hBf (ENNReal.ofReal_pos.mpr hε).ne'
  let K : Set ℝ := K₀ ∪ {xA}
  let L : Set ℝ := L₀ ∪ {xB}
  have hKc : IsCompact K := hK₀c.union (isCompact_singleton)
  have hLc : IsCompact L := hL₀c.union (isCompact_singleton)
  have hKn : K.Nonempty := ⟨xA, by simp [K]⟩
  have hLn : L.Nonempty := ⟨xB, by simp [L]⟩
  have hKA' : K ⊆ A := by
    intro x hx
    rcases hx with hx | hx
    · exact hK₀A hx
    · rcases hx with rfl
      exact hxA
  have hLB' : L ⊆ B := by
    intro x hx
    rcases hx with hx | hx
    · exact hL₀B hx
    · rcases hx with rfl
      exact hxB
  have hKtop : volume K ≠ ∞ := hKc.measure_lt_top.ne
  have hLtop : volume L ≠ ∞ := hLc.measure_lt_top.ne
  have hAapprox : volume.real A < volume.real K + ε := by
    have hmono : volume K₀ ≤ volume K := measure_mono subset_union_left
    have hlt : volume A < volume K + ENNReal.ofReal ε := by
      exact hKA.trans_le (add_le_add hmono le_rfl)
    have haddtop : volume K + ENNReal.ofReal ε ≠ ∞ := by
      simp [hKtop]
    have := (ENNReal.toReal_lt_toReal hAf haddtop).mpr hlt
    simpa [Measure.real, ENNReal.toReal_add hKtop, hε.le] using this
  have hBapprox : volume.real B < volume.real L + ε := by
    have hmono : volume L₀ ≤ volume L := measure_mono subset_union_left
    have hlt : volume B < volume L + ENNReal.ofReal ε := by
      exact hLB.trans_le (add_le_add hmono le_rfl)
    have haddtop : volume L + ENNReal.ofReal ε ≠ ∞ := by
      simp [hLtop]
    have := (ENNReal.toReal_lt_toReal hBf haddtop).mpr hlt
    simpa [Measure.real, ENNReal.toReal_add hLtop, hε.le] using this
  have hcompact := weightedBrunnMinkowskiData_isCompact hKc hLc hKn hLn ha hb
  have hsumsub : a • K + b • L ⊆ a • A + b • B := by
    exact add_subset_add (smul_set_mono hKA') (smul_set_mono hLB')
  have htarget :
      a * volume.real K + b * volume.real L ≤
        volume.real (a • A + b • B) :=
    hcompact.trans (measureReal_mono hsumsub hTarget)
  have hstrict :
      a * volume.real A + b * volume.real B <
        (a * volume.real K + b * volume.real L) + ε := by
    calc
      a * volume.real A + b * volume.real B <
          a * (volume.real K + ε) + b * (volume.real L + ε) :=
        add_lt_add (mul_lt_mul_of_pos_left hAapprox ha)
          (mul_lt_mul_of_pos_left hBapprox hb)
      _ = (a * volume.real K + b * volume.real L) + ε := by
        rw [mul_add, mul_add]
        nlinarith [hab]
  exact hstrict.le.trans (by
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right htarget ε)

/-- The unconditional one-dimensional weighted Brunn–Minkowski inequality in
its mathematically natural `ℝ≥0∞` form. If the target has infinite volume the
claim is immediate; otherwise the real-valued compact-approximation theorem
above converts back without loss. -/
theorem ennreal_weightedBrunnMinkowski
    {A B : Set ℝ} (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hAf : volume A ≠ ∞) (hBf : volume B ≠ ∞)
    (hAn : A.Nonempty) (hBn : B.Nonempty)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    ENNReal.ofReal a * volume A + ENNReal.ofReal b * volume B ≤
      volume (a • A + b • B) := by
  by_cases hTarget : volume (a • A + b • B) = ∞
  · simp [hTarget]
  exact ennreal_weighted_measure_le_of_brunnMinkowski ha hb hAf hBf
    (weightedBrunnMinkowskiData_of_measurable_of_ne_top
      hAm hBm hAf hBf hAn hBn ha hb hab hTarget)
    (Subset.rfl)

end PrekopaNative.BlockBand
