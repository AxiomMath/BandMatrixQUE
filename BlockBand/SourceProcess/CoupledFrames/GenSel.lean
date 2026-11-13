module

public import BlockBand.SourceProcess.ModelExist.KerProj
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# A generic measurable selection of a normalized kernel vector

Data on a measurable parameter space `Z`: a constraint matrix `G z`, a quadratic form `Q z` and a
target `v z`. With `Π = specProj (G z)` (the measurable kernel projection of `KerProj`), the
candidates are `q_k = Π e_k ∈ ker G z`; `genSel` takes the first `k` (in a fixed enumeration)
with `r_k = Re(q_kᴴ Q q_k) > 0` and returns `√(v / r_k) q_k`.

* `measurable_genSel`: measurable when `G`, `Q`, `v` are.
* `genSel_spec`: if `Q z ⪰ 0`, `v z ≥ 0` and some `w` has `G z w = 0`, `Q z w ≠ 0`, then
  `G z (genSel z) = 0` and `genSel zᴴ Q z genSel z = v z`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open Matrix Finset MeasureTheory BlockBand.SourceProcess.ModelExist
open scoped ComplexOrder

variable {Z : Type*} {r c : Type*} [Fintype r] [Fintype c] [DecidableEq c]
  (G : Z → Matrix r c ℂ) (Q : Z → Matrix c c ℂ) (v : Z → ℝ)

/-- The candidate columns `q_k = Π e_k`. -/
def gCand (z : Z) (k : c) : c → ℂ := specProj (G z) *ᵥ Pi.single k 1

/-- Their `Q`-norms. -/
def gNorm (z : Z) (k : c) : ℝ := (star (gCand G z k) ⬝ᵥ (Q z *ᵥ gCand G z k)).re

/-- `j` is the first index with a positive candidate. -/
def GFirst (z : Z) (j : Fin (Fintype.card c)) : Prop :=
  0 < gNorm G Q z ((Fintype.equivFin c).symm j) ∧
    ∀ j' < j, ¬ 0 < gNorm G Q z ((Fintype.equivFin c).symm j')

instance (z : Z) (j : Fin (Fintype.card c)) : Decidable (GFirst G Q z j) := by
  unfold GFirst; infer_instance

/-- **The selection.** -/
def genSel (z : Z) : c → ℂ :=
  ∑ j, if GFirst G Q z j then
    ((Real.sqrt (v z / gNorm G Q z ((Fintype.equivFin c).symm j)) : ℝ) : ℂ) •
      gCand G z ((Fintype.equivFin c).symm j) else 0

variable [MeasurableSpace Z]

theorem measurable_gCand (hG : Measurable G) (k : c) : Measurable fun z => gCand G z k :=
  (continuous_id.matrix_mulVec continuous_const).measurable.comp (measurable_specProj.comp hG)

omit [DecidableEq c] in
theorem secMatC : SecondCountableTopology (Matrix c c ℂ) :=
  inferInstanceAs (SecondCountableTopology (c → c → ℂ))

attribute [local instance] secMatC

theorem measurable_gNorm (hG : Measurable G) (hQ : Measurable Q) (k : c) :
    Measurable fun z => gNorm G Q z k := by
  have hc : Continuous fun p : (c → ℂ) × Matrix c c ℂ => star p.1 ⬝ᵥ (p.2 *ᵥ p.1) :=
    Continuous.dotProduct continuous_fst.star (continuous_snd.matrix_mulVec continuous_fst)
  exact Complex.measurable_re.comp (hc.measurable.comp ((measurable_gCand G hG k).prodMk hQ))

theorem measurableSet_gFirst (hG : Measurable G) (hQ : Measurable Q)
    (j : Fin (Fintype.card c)) : MeasurableSet {z | GFirst G Q z j} := by
  simp only [GFirst, Set.ofPred_and]
  refine (measurableSet_lt measurable_const (measurable_gNorm G Q hG hQ _)).inter ?_
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j' => MeasurableSet.iInter fun _ =>
    (measurableSet_lt measurable_const (measurable_gNorm G Q hG hQ _)).compl

/-- **The selection is measurable.** -/
theorem measurable_genSel (hG : Measurable G) (hQ : Measurable Q) (hv : Measurable v) :
    Measurable (genSel G Q v) := by
  classical
  refine measurable_pi_iff.2 fun x => ?_
  simp only [genSel, Finset.sum_apply]
  refine Finset.measurable_fun_sum _ fun j _ => ?_
  have hf : Measurable fun z =>
      ((Real.sqrt (v z / gNorm G Q z ((Fintype.equivFin c).symm j)) : ℝ) : ℂ) *
        gCand G z ((Fintype.equivFin c).symm j) x :=
    (Complex.measurable_ofReal.comp (hv.div (measurable_gNorm G Q hG hQ _)).sqrt).mul
      ((measurable_pi_apply x).comp (measurable_gCand G hG _))
  have hite := @Measurable.piecewise _ _ _ _ _ _ _ (fun _ => Classical.propDecidable _)
    (measurableSet_gFirst G Q hG hQ j) hf (measurable_const (a := (0 : ℂ)))
  convert hite using 1
  funext z
  simp only [Set.piecewise, Set.mem_ofPred_eq]
  split_ifs <;> simp

omit [MeasurableSpace Z] in
theorem gCand_ker (z : Z) (k : c) : G z *ᵥ gCand G z k = 0 := by
  rw [gCand, mulVec_mulVec, mul_specProj, zero_mulVec]

omit [MeasurableSpace Z] in
theorem exists_gNorm_pos {z : Z} (hQ : (Q z).PosSemidef)
    (hE : ∃ w, G z *ᵥ w = 0 ∧ Q z *ᵥ w ≠ 0) : ∃ k, 0 < gNorm G Q z k := by
  obtain ⟨w, hw, hQw⟩ := hE
  have hPw := specProj_mulVec_of (G z) hw
  by_contra hall
  push Not at hall
  have hMq : ∀ k, Q z *ᵥ gCand G z k = 0 := fun k => by
    have h0 := hQ.dotProduct_mulVec_nonneg (gCand G z k)
    have hz : star (gCand G z k) ⬝ᵥ (Q z *ᵥ gCand G z k) = 0 := by
      obtain ⟨hre, him⟩ := Complex.le_def.1 h0
      apply Complex.ext
      · exact le_antisymm (hall k) hre
      · exact him.symm
    exact (hQ.dotProduct_mulVec_zero_iff).1 hz
  have hMP : Q z * specProj (G z) = 0 := by
    ext i k
    have := congrFun (hMq k) i
    rw [gCand, mulVec_mulVec] at this
    simpa [mulVec, dotProduct, Pi.single_apply] using this
  apply hQw
  rw [← hPw, mulVec_mulVec, hMP, zero_mulVec]

omit [MeasurableSpace Z] in
/-- **The selection meets its specification.** -/
theorem genSel_spec {z : Z} (hv : 0 ≤ v z) (hQ : (Q z).PosSemidef)
    (hE : ∃ w, G z *ᵥ w = 0 ∧ Q z *ᵥ w ≠ 0) :
    G z *ᵥ genSel G Q v z = 0 ∧ star (genSel G Q v z) ⬝ᵥ (Q z *ᵥ genSel G Q v z) = (v z : ℂ) := by
  set e := Fintype.equivFin c
  obtain ⟨k0, hk0⟩ := exists_gNorm_pos G Q hQ hE
  set S := univ.filter fun j : Fin (Fintype.card c) => 0 < gNorm G Q z (e.symm j)
  have hS : S.Nonempty := ⟨e k0, by simp [S, hk0]⟩
  set j0 := S.min' hS
  have hj0 : GFirst G Q z j0 := by
    refine ⟨(Finset.mem_filter.1 (S.min'_mem hS)).2, fun j' hj' hpos => ?_⟩
    have hmem : j' ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hpos⟩
    exact absurd (S.min'_le j' hmem) (not_le.2 hj')
  have huniq : ∀ j, GFirst G Q z j → j = j0 := fun j hj => by
    rcases lt_trichotomy j j0 with h | h | h
    · exact absurd hj.1 (hj0.2 j h)
    · exact h
    · exact absurd hj0.1 (hj.2 j0 h)
  have hsel : genSel G Q v z =
      ((Real.sqrt (v z / gNorm G Q z (e.symm j0)) : ℝ) : ℂ) • gCand G z (e.symm j0) := by
    unfold genSel
    rw [Finset.sum_eq_single j0 (fun j _ hj => ite_eq_right (fun h => hj (huniq j h))) (by simp),
      ite_eq_left hj0]
  rw [hsel]
  refine ⟨by rw [mulVec_smul, gCand_ker, smul_zero], ?_⟩
  set q := gCand G z (e.symm j0)
  have hr : 0 < gNorm G Q z (e.symm j0) := hj0.1
  have hreal : star q ⬝ᵥ (Q z *ᵥ q) = ((gNorm G Q z (e.symm j0) : ℝ) : ℂ) := by
    obtain ⟨-, him⟩ := Complex.le_def.1 (hQ.dotProduct_mulVec_nonneg q)
    apply Complex.ext
    · rfl
    · simpa using him.symm
  rw [mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, hreal]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (div_nonneg hv hr.le),
    ← Complex.ofReal_mul, div_mul_cancel₀ (v z) hr.ne']

end BlockBand.SourceProcess.CoupledFrames
