module

public import BlockBand.Transmission.Dual.Generator
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# A smooth exhaustion of the open chamber

`exists_chamber_exhaustion q` gives smooth cutoffs `u_n : DualCoord q → [0, 1]`, compactly
supported in `𝒞_q`, with
* `u_{n+1} = 1` on an open set containing the support of `u_n`;
* every compact subset of `𝒞_q` lies in `{u_n = 1}` for all large `n`.

Built from a compact exhaustion of the subtype `𝒞_q` and the smooth Urysohn lemma
`exists_contDiff_support_eq_eq_one_iff`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath

theorem exists_chamber_exhaustion (q : ℕ) :
    ∃ u : ℕ → DualCoord q → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (u n)) ∧
      (∀ n, HasCompactSupport (u n)) ∧ (∀ n, tsupport (u n) ⊆ dualChamber q) ∧
      (∀ n z, 0 ≤ u n z ∧ u n z ≤ 1) ∧
      (∀ n, ∃ O : Set (DualCoord q), IsOpen O ∧ Function.support (u n) ⊆ O ∧
        ∀ z ∈ O, u (n + 1) z = 1) ∧
      (∀ L : Set (DualCoord q), IsCompact L → L ⊆ dualChamber q →
        ∃ n₀, ∀ n, n₀ ≤ n → ∀ z ∈ L, u n z = 1) := by
  have hopen := isOpen_dualChamber q
  have : LocallyCompactSpace (dualChamber q) := hopen.locallyCompactSpace
  let K := CompactExhaustion.choice (dualChamber q)
  let Ka : ℕ → Set (DualCoord q) := fun n => (↑) '' (K n)
  have hKa : ∀ n, IsCompact (Ka n) := fun n => (K.isCompact n).image continuous_subtype_val
  have hKaC : ∀ n, Ka n ⊆ dualChamber q := fun n => by
    rintro _ ⟨z, -, rfl⟩; exact z.2
  have hKaint : ∀ n, Ka n ⊆ interior (Ka (n + 1)) := fun n =>
    (image_mono (K.subset_interior_succ n)).trans
      (hopen.isOpenMap_subtype_val.image_interior_subset _)
  have hex : ∀ n, ∃ f : DualCoord q → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ range f ⊆ Icc 0 1 ∧
      Function.support f = interior (Ka (n + 1)) ∧ ∀ z, z ∈ Ka n ↔ f z = 1 := fun n =>
    exists_contDiff_support_eq_eq_one_iff isOpen_interior (hKa n).isClosed (hKaint n)
  choose u hsm hrange hsupp hone using hex
  have htsupp : ∀ n, tsupport (u n) ⊆ Ka (n + 1) := fun n => by
    rw [tsupport, hsupp n]
    exact closure_minimal interior_subset (hKa (n + 1)).isClosed
  refine ⟨u, hsm, fun n => (hKa (n + 1)).of_isClosed_subset (isClosed_tsupport _) (htsupp n),
    fun n => (htsupp n).trans (hKaC _), fun n z => ?_, fun n => ?_, fun L hL hLC => ?_⟩
  · have := hrange n ⟨z, rfl⟩; exact ⟨this.1, this.2⟩
  · refine ⟨interior (Ka (n + 1)), isOpen_interior, (hsupp n).le, fun z hz => ?_⟩
    exact (hone (n + 1) z).1 (interior_subset hz)
  · have hL' : IsCompact (((↑) : dualChamber q → DualCoord q) ⁻¹' L) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hLC]
      exact hL
    obtain ⟨n₀, hn₀⟩ := K.exists_superset_of_isCompact hL'
    refine ⟨n₀, fun n hn z hz => (hone n z).1 ?_⟩
    exact ⟨⟨z, hLC hz⟩, K.subset hn (hn₀ hz), rfl⟩

end BlockBand.Transmission.Dual
