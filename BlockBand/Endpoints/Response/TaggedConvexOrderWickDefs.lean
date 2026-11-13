module

public import BlockBand.Endpoints.Response.TaggedConvexOrderWitnessStop

/-!
# The Wick trace polynomial of the probe moment and the two algebraic inputs (a), (b)

Step 3 of the proof of the tagged convex-order theorem.

**Objects** (one tag, no interval source: `nT = 1`, `nI = 0`).
* `tcx_tagWord r = [(Q, I)]^r`, the ordinary word `Tr Q^r` (`tcx_wordValue_tagWord`:
  its value at length `l` is `Tr Q_{l;k}^r`).
* `tcx_wickPoly m = Σ_{π∈S_m} Π_{c cycle of π} Tr Q^{|c|}` (cycles counted with fixed points,
  `Equiv.Perm.partition`), an ordinary trace polynomial (`tcx_isOrdinaryPoly_wickPoly`).

**The two isolated algebraic inputs** (deterministic: no estimate on the path law).
* `TcxWickMoment` (item (a)): the complex Wick formula
  `E_h (h*Qh)^m = Σ_{π∈S_m} Π_c Tr Q^{|c|}` for `h ~ circularVectorLaw ι` (`E hh* = I`) and every
  positive semidefinite `Q`. Consequence: `tcx_F_eq_polyValue`, `E_h Z_{l;k}^m = Φ_m(Q_{l;k})`.
* `TcxWickGenerator` (item (b)): a.s. on the path,
  `Re polyValue(𝒜 Φ_m) = (D₀/2) m(m-1) E_h[X^{m-2}(v*Pv)(v*P'v)]` (`= tcw_H`), where `𝒜` is
  `wordGenerator` (`pairTerm` within words and `crossTerm` between words, `P' = P + J`).
  At `m = 2` both sides are `D₀[Tr(QP)Tr(QP') + Tr(QPQP')]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionStatements
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal NNReal

/-- The ordinary tag word `Tr Q^r = Tr((Q·I)^r)` (one tag, no interval source). -/
def tcx_tagWord (r : ℕ) : TraceWord 1 0 := List.replicate r (TraceLetter.tag 0, Separator.id)

/-- **The Wick trace polynomial** `Φ_m = Σ_{π∈S_m} Π_{c cycle of π} Tr Q^{|c|}` (fixed points are
cycles of length `1`). -/
def tcx_wickPoly (m : ℕ) : TracePoly 1 0 :=
  ∑ π : Equiv.Perm (Fin m), (π.partition.parts.map fun r => wv (tcx_tagWord r)).prod

/-- **(a) The complex Wick formula** for the standard circular Gaussian vector (`E hh* = I`):
for every `m`, finite `ι` and `Q ⪰ 0`, `E_h (h*Qh)^m = Σ_{π∈S_m} Π_{c cycle of π} Tr Q^{|c|}`.
Deterministic (a Gaussian integral at a fixed matrix). -/
def TcxWickMoment : Prop :=
  ∀ (m : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℂ), Q.PosSemidef →
    ((∫ h, quadForm Q h ^ m ∂circularVectorLaw ι : ℝ) : ℂ) =
      ∑ π : Equiv.Perm (Fin m), (π.partition.parts.map fun r => (Q ^ r).trace).prod

/-- **(b) The generator identity**: for `0 < b < 1/2`, bulk `e`, `W > 0`, every `l, k, m`, every
time `t` (the injection vanishes on tag words), a.s. on the path,
`Re polyValue_l(wordGenerator Φ_m) = (D₀/2) m(m-1) E_h[X^{m-2}(v*Pv)(v*P'v)]` (`tcw_H`, with
`v = Q_{l;k}^{1/2}h`, `P' = 𝕊*P𝕊 = P + J_l`). A deterministic combinatorial identity between the
word generator and the Wick expansion; at `m = 2` both sides are
`D₀[Tr(QP)Tr(QP') + Tr(QPQP')]`. -/
def TcxWickGenerator : Prop :=
  ∀ (m : ℕ) (b : ℝ), 0 < b → b < 1 / 2 → ∀ e : ℝ, -2 < e → e < 2 → ∀ W : ℕ, 0 < W →
    ∀ (l k : ℕ) (t : ℝ), ∀ᵐ ω ∂growthPathLaw W b,
      (polyValue b e (tcw_tagFamily k) tcw_noInterval W l ω
        (wordGenerator b e tcw_noInterval t (tcx_wickPoly m))).re = tcw_H b e W l k m ω

/-!
## Elementary properties
-/

theorem tcx_isOrdinaryWord_tagWord {r : ℕ} (hr : 0 < r) : IsOrdinaryWord (tcx_tagWord r) := by
  refine ⟨?_, fun x hx => ?_⟩
  · unfold tcx_tagWord
    exact List.ne_nil_of_length_pos (by simpa using hr)
  · unfold tcx_tagWord at hx
    rw [List.eq_of_mem_replicate hx]
    exact Or.inl rfl

/-- `Φ_m` is an ordinary trace polynomial. -/
theorem tcx_isOrdinaryPoly_wickPoly (m : ℕ) : IsOrdinaryPoly (tcx_wickPoly m) := by
  let S : Set (TracePoly 1 0) := {Φ | ∀ w ∈ Φ.vars, IsOrdinaryWord w}
  have hadd : ∀ Φ Ψ, Φ ∈ S → Ψ ∈ S → Φ + Ψ ∈ S := fun Φ Ψ hΦ hΨ w hw => by
    rcases Finset.mem_union.1 (MvPolynomial.vars_add_subset Φ Ψ hw) with h | h
    · exact hΦ w h
    · exact hΨ w h
  have hmul : ∀ Φ Ψ, Φ ∈ S → Ψ ∈ S → Φ * Ψ ∈ S := fun Φ Ψ hΦ hΨ w hw => by
    rcases Finset.mem_union.1 (MvPolynomial.vars_mul Φ Ψ hw) with h | h
    · exact hΦ w h
    · exact hΨ w h
  have hzero : (0 : TracePoly 1 0) ∈ S := fun w hw => by simp at hw
  have hone : (1 : TracePoly 1 0) ∈ S := fun w hw => by simp at hw
  unfold tcx_wickPoly
  refine Finset.sum_induction _ (· ∈ S) hadd hzero fun π _ => ?_
  refine Multiset.prod_induction (· ∈ S) _ hmul hone fun p hp => ?_
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hp
  intro w hw
  rw [MvPolynomial.vars_X, Finset.mem_singleton] at hw
  rw [hw]
  exact tcx_isOrdinaryWord_tagWord (π.partition.parts_pos hr)

theorem tcx_letterMatrix_tag (b e : ℝ) (W l k : ℕ) (ω : GrowthPath W) :
    letterMatrix b e (tcw_tagFamily k) tcw_noInterval W l ω (TraceLetter.tag 0) =
      tco_tagQ b e W l k ω := by
  simp only [letterMatrix, tco_tagQ]
  ext x y
  simp [Complex.real_smul]

/-- The value of the tag word `Tr Q^r` at length `l` is `Tr Q_{l;k}^r`. -/
theorem tcx_wordValue_tagWord (b e : ℝ) (W l k r : ℕ) (ω : GrowthPath W) :
    wordValue b e (tcw_tagFamily k) tcw_noInterval W l ω (tcx_tagWord r) =
      ((tco_tagQ b e W l k ω) ^ r).trace := by
  unfold wordValue tcx_tagWord
  rw [List.map_replicate, List.prod_replicate]
  simp only [separatorMatrix, mul_one, tcx_letterMatrix_tag]

/-- The value of `Φ_m` at length `l`: `Σ_{π∈S_m} Π_c Tr Q_{l;k}^{|c|}`. -/
theorem tcx_polyValue_wickPoly (b e : ℝ) (W l k m : ℕ) (ω : GrowthPath W) :
    polyValue b e (tcw_tagFamily k) tcw_noInterval W l ω (tcx_wickPoly m) =
      ∑ π : Equiv.Perm (Fin m),
        (π.partition.parts.map fun r => ((tco_tagQ b e W l k ω) ^ r).trace).prod := by
  unfold polyValue tcx_wickPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun r _ => ?_
  simp only [Function.comp_apply, MvPolynomial.eval_X, tcx_wordValue_tagWord]

/-- **(a) on the path**: `E_h Z_{l;k}^m = Φ_m(Q_{l;k})` (as a complex number). -/
theorem tcx_F_eq_polyValue (hWick : TcxWickMoment) (b e : ℝ) (W l k m : ℕ) (ω : GrowthPath W) :
    ((tcw_F b e W l k m ω : ℝ) : ℂ) =
      polyValue b e (tcw_tagFamily k) tcw_noInterval W l ω (tcx_wickPoly m) := by
  rw [tcx_polyValue_wickPoly, ← hWick m (Fin 2 × Fin W) _ (tco_posSemidef_tagQ b e W l k ω)]
  unfold tcw_F
  congr 2
  funext h
  rw [tco_tagClock_eq_quadForm]

end BlockBand.Endpoints
