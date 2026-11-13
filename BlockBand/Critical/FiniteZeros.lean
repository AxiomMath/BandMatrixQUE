module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Meromorphic.Divisor

/-!
# Finite zero carriers for recovery

A nonzero entire function has finitely many zeros in every compact set.  This file packages
the zeros on a compact window, with their analytic multiplicities, and their restriction to
smaller windows, such as the rational real windows of a countable exhaustion.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section
open Filter Set Topology
open scoped BigOperators
namespace BlockBand.Critical

/-- Compact sets contain finitely many zeros of a nonzero entire function.  This is an
unconditional consequence of Mathlib's codiscrete zero-set theorem and compactness. -/
theorem finite_zeros_inter_compact
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnonzero : ∃ z, f z ≠ 0) {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ {z | f z = 0}).Finite := by
  obtain ⟨z₀, hz₀⟩ := hnonzero
  have hana : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hcodisc : f ⁻¹' ({0} : Set ℂ)ᶜ ∈ codiscrete ℂ :=
    hana.preimage_zero_mem_codiscrete hz₀
  have hdisc : IsDiscrete (f ⁻¹' ({0} : Set ℂ)) := by
    simpa only [Set.preimage_compl, compl_compl] using (mem_codiscrete'.mp hcodisc).2
  have hclosed : IsClosed {z : ℂ | f z = 0} := by
    exact isClosed_eq hf.continuous continuous_const
  apply (hK.inter_right hclosed).finite
  exact hdisc.mono (by
    intro z hz
    exact hz.2)

/-- Closed real window with rational endpoints, used in a countable exhaustion. -/
def rationalRealWindow (a b : ℚ) : Set ℂ :=
  Complex.ofReal '' Set.Icc (a : ℝ) (b : ℝ)

/-- Rational real windows are compact. -/
theorem isCompact_rationalRealWindow (a b : ℚ) :
    IsCompact (rationalRealWindow a b) :=
  isCompact_Icc.image Complex.continuous_ofReal

/-- Exact finite zero data on one compact window.  The carrier has no arbitrary
extraneous points, and `multiplicity` is the analytic order at that point. -/
structure CompactZeroWindow (f : ℂ → ℂ) (window : Set ℂ) where
  zeros : Finset ℂ
  mem_zeros : ∀ z, z ∈ zeros ↔ z ∈ window ∧ f z = 0

namespace CompactZeroWindow

/-- Construct exact finite-window zero data for a nonzero entire function. -/
def ofCompact
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnonzero : ∃ z, f z ≠ 0) (window : Set ℂ) (hwindow : IsCompact window) :
    CompactZeroWindow f window where
  zeros := (finite_zeros_inter_compact hf hnonzero hwindow).toFinset
  mem_zeros z := by
    simp [Set.mem_inter_iff]

/-- Multiplicity of a stored zero, using Mathlib's analytic order. -/
def multiplicity {f : ℂ → ℂ} {window : Set ℂ}
    (_data : CompactZeroWindow f window) (z : ℂ) : ℕ :=
  analyticOrderNatAt f z

/-- Total number of zeros in the window, counted with analytic multiplicity. -/
def count {f : ℂ → ℂ} {window : Set ℂ}
    (data : CompactZeroWindow f window) : ℕ :=
  ∑ z ∈ data.zeros, data.multiplicity z

/-- Restrict exact zero data to a smaller window. -/
noncomputable def restrict {f : ℂ → ℂ} {large small : Set ℂ}
    (data : CompactZeroWindow f large) (hsub : small ⊆ large) :
    CompactZeroWindow f small := by
  classical
  exact
    { zeros := data.zeros.filter fun z => z ∈ small
      mem_zeros := fun z => by
        simp only [Finset.mem_filter, data.mem_zeros]
        constructor
        · rintro ⟨⟨_zlarge, hz⟩, hzsmall⟩
          exact ⟨hzsmall, hz⟩
        · rintro ⟨hzsmall, hz⟩
          exact ⟨⟨hsub hzsmall, hz⟩, hzsmall⟩ }

/-- Projective consistency of finite-window carriers under two successive
restrictions. -/
theorem restrict_zeros_trans
    {f : ℂ → ℂ} {large middle small : Set ℂ}
    (data : CompactZeroWindow f large)
    (hml : middle ⊆ large) (hsm : small ⊆ middle) :
    ((data.restrict hml).restrict hsm).zeros =
      (data.restrict (hsm.trans hml)).zeros := by
  classical
  ext z
  simp only [restrict, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hzdata, _hzmiddle⟩, hzsmall⟩
    exact ⟨hzdata, hzsmall⟩
  · rintro ⟨hzdata, hzsmall⟩
    exact ⟨⟨hzdata, hsm hzsmall⟩, hzsmall⟩

/-- Zeros discarded when passing to a smaller window. -/
noncomputable def discarded {f : ℂ → ℂ} {large : Set ℂ}
    (data : CompactZeroWindow f large) (small : Set ℂ) : Finset ℂ := by
  classical
  exact data.zeros.filter fun z => z ∉ small

/-- Counts on nested windows split exactly into the retained and discarded finite
zeros; no analytic argument principle is involved. -/
theorem count_restrict_add_count_discarded
    {f : ℂ → ℂ} {large small : Set ℂ}
    (data : CompactZeroWindow f large) (hsub : small ⊆ large) :
    (data.restrict hsub).count +
        (∑ z ∈ data.discarded small, data.multiplicity z) = data.count := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not data.zeros
    (fun z => z ∈ small) (fun z => analyticOrderNatAt f z)
  simpa [count, restrict, discarded, multiplicity] using hsplit

end CompactZeroWindow

end BlockBand.Critical
