module

public import BlockBand.Critical.RelativeVectors.Angular.Pathwise

/-!
# One grid cell of the space-time angular martingale

On the cell `[p_k, p_{k+1}]` of the grid of `[0, u]`, the fixed-time angular martingale problem is
applied at start `s + p_k`, with eigenvector selection `revSelection`, frame `√N V`, and the random
test `f_k ω Z = Λ ω 1{p_k < σ(ω)} h(ω, p_{k+1}, R Z)` (`cellTest`). On `{p_k < σ}` the restarted gap
stop satisfies `p_k + (u' ∧ σ^{(s+p_k)}) = (p_k + u') ∧ σ` (`stopIndex_shift`), so the stopped
variable is, for every sample, `Λ` times the cell term of `gridSum` (`contractVariable_eq`); on
`{σ ≤ p_k}` both vanish.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.Angular

open MeasureTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.TransmissionAngular
open scoped NNReal

variable {N r : ℕ}

/-- Grid point as a nonnegative time. -/
def gridNN (u : ℝ≥0) (K k : ℕ) : ℝ≥0 := (gridPt u K k).toNNReal

theorem coe_gridNN (u : ℝ≥0) (K k : ℕ) : (gridNN u K k : ℝ) = gridPt u K k :=
  Real.coe_toNNReal _ (gridPt_nonneg u.2 k)

theorem gridNN_succ (u : ℝ≥0) (K k : ℕ) :
    gridNN u K (k + 1) = gridNN u K k + ((u : ℝ) / K).toNNReal := by
  apply NNReal.eq
  rw [NNReal.coe_add, coe_gridNN, coe_gridNN, Real.coe_toNNReal _ (by positivity), gridPt_succ]

theorem untopA_min_coe_of_le {a b : ℝ≥0} (hab : a ≤ b) (w : WithTop ℝ≥0) :
    (((min (a : WithTop ℝ≥0) w).untopA : ℝ≥0) : ℝ) =
      min (((min (b : WithTop ℝ≥0) w).untopA : ℝ≥0) : ℝ) a := by
  induction w using WithTop.recTopCoe with
  | top =>
    simp only [min_top_right]
    change (a : ℝ) = min (b : ℝ) a
    rw [min_eq_right (by exact_mod_cast hab)]
  | coe c =>
    have e1 : min (a : WithTop ℝ≥0) c = ((min a c : ℝ≥0) : WithTop ℝ≥0) := by
      rw [WithTop.coe_min]
    have e2 : min (b : WithTop ℝ≥0) c = ((min b c : ℝ≥0) : WithTop ℝ≥0) := by
      rw [WithTop.coe_min]
    rw [e1, e2]
    change ((min a c : ℝ≥0) : ℝ) = min ((min b c : ℝ≥0) : ℝ) a
    push_cast
    rw [min_comm (b : ℝ) c, min_assoc, min_eq_right (show (a : ℝ) ≤ b by exact_mod_cast hab),
      min_comm]

theorem untopA_coe (a : ℝ≥0) : (a : WithTop ℝ≥0).untopA = a := rfl

/-- The random test of the cell `k`. -/
def cellTest {Ω : Type*} (σ : Ω → WithTop ℝ≥0) (Λ : Ω → ℝ)
    (h : Ω → ℝ → (Fin N → Fin r → ℂ) → ℝ) (u : ℝ≥0) (K k : ℕ) (ω : Ω)
    (Z : Fin N → Fin r → ℂ) : ℝ :=
  (if ((gridNN u K k : ℝ≥0) : WithTop ℝ≥0) < σ ω then Λ ω else 0) *
    h ω (gridPt u K (k + 1)) (relabelArray Z)

/-- The cell term of `gridSum`. -/
def cellTerm {E : Type*} (h : ℝ → E → ℝ) (a : ℝ → ℝ → ℝ) (φ : ℝ → E) (t u : ℝ) (K k : ℕ) : ℝ :=
  h (gridPt u K (k + 1)) (φ (gridMu t u K (k + 1))) - h (gridPt u K (k + 1)) (φ (gridMu t u K k)) -
    ∫ x in Ioc (gridMu t u K k) (gridMu t u K (k + 1)), a (gridPt u K (k + 1)) x

theorem gridSum_eq_sum_cellTerm {E : Type*} (h : ℝ → E → ℝ) (a : ℝ → ℝ → ℝ) (φ : ℝ → E)
    (t u : ℝ) (K : ℕ) :
    gridSum h a φ t u K = ∑ k ∈ Finset.range K, cellTerm h a φ t u K k := rfl

theorem dysonEigenvalue_eq_rev {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian) :
    dysonEigenvalue N K = fun i => freshEigenvalue K i.rev := by
  funext i
  have := BlockBand.Palm.MomentFlow.dysonEigenvalue_rev hK i.rev
  rwa [Fin.rev_rev] at this

/-- The generator of a cell test is the scalar times the generator along the array. -/
theorem contractGenerator_cellTest_apply {g : (Fin N → Fin r → ℂ) → ℝ} (hg : ContDiff ℝ 2 g)
    (c : ℝ) {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian) (V : Matrix (Fin N) (Fin r) ℂ) :
    BlockBand.Internal.Contracts.TransmissionAngular.complexAngularGenerator N r
        (dysonEigenvalue N K) (fun Z => c * g (relabelArray Z))
        (angularArray (scaledFrame V) (revSelection N K)) =
      c * complexAngularGenerator N r (fun ℓ => freshEigenvalue K ℓ) g (frameArray V K) := by
  have hg' : ContDiff ℝ 2 (fun Z => g (relabelArray Z)) := hg.comp (relabelCLE N r).contDiff
  rw [contractGenerator_const_mul _ hg', dysonEigenvalue_eq_rev hK,
    contractGenerator_comp_relabel, ← frameArray_eq_relabel]

theorem integral_Ioc_shift (A : ℝ → ℝ) (a : ℝ) {m : ℝ} (hm : 0 ≤ m) :
    ∫ w in Ioc 0 m, A (a + w) = ∫ x in Ioc a (a + m), A x := by
  rw [← intervalIntegral.integral_of_le hm, intervalIntegral.integral_comp_add_left, add_zero,
    intervalIntegral.integral_of_le (by linarith)]

theorem toNNReal_coe_add {a : ℝ≥0} {w : ℝ} (hw : 0 ≤ w) :
    ((a : ℝ) + w).toNNReal = a + w.toNNReal := by
  rw [Real.toNNReal_add a.coe_nonneg hw, Real.toNNReal_coe]

/-- **The stopped variable of the cell `k`**, for every sample: `Λ` times the cell term. -/
theorem contractVariable_eq {Ω : Type*} {F : Ω → Matrix (Fin N) (Fin N) ℂ}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} (hH : ∀ t ω, (F ω + G t ω).IsHermitian)
    (s : ℝ≥0) (V : Matrix (Fin N) (Fin r) ℂ) (n : ℕ) {T : ℝ≥0}
    {h : Ω → ℝ → (Fin N → Fin r → ℂ) → ℝ} (hcd : ∀ ω, ∀ v ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (h ω v))
    {u : ℝ≥0} (huT : u ≤ T) (Λ : Ω → ℝ) {K k : ℕ} (hK : K ≠ 0) (hk : k < K) (ω : Ω) :
    stoppedProcess (fun (v : ℝ≥0) ω =>
        cellTest (gapStop N (fun t ω => F ω + G t ω) s n) Λ h u K k ω
            (angularArray (scaledFrame V) (revSelection N (F ω + G (s + gridNN u K k + v) ω))) -
          cellTest (gapStop N (fun t ω => F ω + G t ω) s n) Λ h u K k ω
            (angularArray (scaledFrame V) (revSelection N (F ω + G (s + gridNN u K k + 0) ω))) -
          ∫ w in Ioc (0 : ℝ) v,
            BlockBand.Internal.Contracts.TransmissionAngular.complexAngularGenerator N r
              (dysonEigenvalue N (F ω + G (s + gridNN u K k + w.toNNReal) ω))
              (cellTest (gapStop N (fun t ω => F ω + G t ω) s n) Λ h u K k ω)
              (angularArray (scaledFrame V)
                (revSelection N (F ω + G (s + gridNN u K k + w.toNNReal) ω))))
        (gapStop N (fun t ω => F ω + G t ω) (s + gridNN u K k) n) (((u : ℝ) / K).toNNReal) ω =
      Λ ω * cellTerm (h ω) (genPath F G V s h ω) (arrPath F G V s ω)
        (stopTime (gapStop N (fun t ω => F ω + G t ω) s n) u ω) u K k := by
  set σ := gapStop N (fun t ω => F ω + G t ω) s n
  set sk := gridNN u K k
  set c : ℝ := if (sk : WithTop ℝ≥0) < σ ω then Λ ω else 0 with hc_def
  set p := gridPt u K (k + 1)
  have hp : p ∈ Icc (0 : ℝ) T := ⟨gridPt_nonneg u.2 _, (gridPt_le u.2 hK (by omega)).trans
    (by exact_mod_cast huT)⟩
  have hcell : ∀ K' : Matrix (Fin N) (Fin N) ℂ,
      cellTest σ Λ h u K k ω (angularArray (scaledFrame V) (revSelection N K')) =
        c * h ω p (frameArray V K') := by
    intro K'; unfold cellTest; rw [← frameArray_eq_relabel]
  have hgen : ∀ t' : ℝ≥0,
      BlockBand.Internal.Contracts.TransmissionAngular.complexAngularGenerator N r
        (dysonEigenvalue N (F ω + G t' ω)) (cellTest σ Λ h u K k ω)
        (angularArray (scaledFrame V) (revSelection N (F ω + G t' ω))) =
      c * complexAngularGenerator N r (fun ℓ => freshEigenvalue (F ω + G t' ω) ℓ) (h ω p)
        (frameArray V (F ω + G t' ω)) := fun t' =>
    contractGenerator_cellTest_apply (hcd ω p hp) c (hH t' ω) V
  simp only [stoppedProcess, hcell, hgen, add_zero]
  set m := (min ((((u : ℝ) / K).toNNReal : ℝ≥0) : WithTop ℝ≥0)
    (gapStop N (fun t ω => F ω + G t ω) (s + sk) n ω)).untopA
  have hsku : sk ≤ u := by
    rw [← NNReal.coe_le_coe, coe_gridNN]; exact gridPt_le u.2 hK hk.le
  have hsk1u : gridNN u K (k + 1) ≤ u := by
    rw [← NNReal.coe_le_coe, coe_gridNN]; exact gridPt_le u.2 hK (by omega)
  by_cases hc : (sk : WithTop ℝ≥0) < σ ω
  · have hcΛ : c = Λ ω := by rw [hc_def]; split_ifs; rfl
    have hshift := stopIndex_shift (fun t ω => F ω + G t ω) s sk n ω hc (((u : ℝ) / K).toNNReal)
    rw [← gridNN_succ] at hshift
    have hmu1 : gridMu (stopTime σ u ω) u K (k + 1) = ((sk + m : ℝ≥0) : ℝ) := by
      unfold gridMu stopTime
      rw [hshift, untopA_min_coe_of_le hsk1u, coe_gridNN]
    have hmu0 : gridMu (stopTime σ u ω) u K k = (sk : ℝ) := by
      unfold gridMu
      rw [← coe_gridNN]
      refine min_eq_right ?_
      unfold stopTime
      have : sk ≤ (min (u : WithTop ℝ≥0) (σ ω)).untopA :=
        (WithTop.le_untopA_iff (min_coe_ne_top u _)).2 (le_min (by exact_mod_cast hsku) hc.le)
      exact_mod_cast this
    unfold cellTerm
    rw [hmu1, hmu0]
    have hI : ∫ w in Ioc (0 : ℝ) (m : ℝ), c * complexAngularGenerator N r
          (fun ℓ => freshEigenvalue (F ω + G (s + sk + w.toNNReal) ω) ℓ) (h ω p)
          (frameArray V (F ω + G (s + sk + w.toNNReal) ω)) =
        c * ∫ x in Ioc (sk : ℝ) ((sk + m : ℝ≥0) : ℝ), genPath F G V s h ω p x := by
      rw [← integral_const_mul]
      rw [NNReal.coe_add]
      refine Eq.trans ?_ (integral_Ioc_shift (fun x => c * genPath F G V s h ω p x) (sk : ℝ) m.2)
      refine setIntegral_congr_fun measurableSet_Ioc fun w hw => ?_
      unfold genPath eigPath arrPath
      simp only [toNNReal_coe_add hw.1.le, add_assoc]
    rw [hI]
    simp only [arrPath, Real.toNNReal_coe, add_assoc]
    rw [hcΛ]
    ring
  · have hc0 : c = 0 := by rw [hc_def]; split_ifs; rfl
    have hle : stopTime σ u ω ≤ gridPt u K k := by
      unfold stopTime
      have : (min (u : WithTop ℝ≥0) (σ ω)).untopA ≤ sk :=
        (WithTop.untopA_le_iff (min_coe_ne_top u _)).2 ((min_le_right _ _).trans (not_lt.1 hc))
      rw [← coe_gridNN]; exact_mod_cast this
    have hmu0 : gridMu (stopTime σ u ω) u K k = stopTime σ u ω := min_eq_left hle
    have hmu1 : gridMu (stopTime σ u ω) u K (k + 1) = stopTime σ u ω :=
      min_eq_left (hle.trans (gridPt_mono u.2 (Nat.le_succ k)))
    unfold cellTerm
    rw [hmu0, hmu1, hc0]
    simp

end BlockBand.Critical.RelativeVectors.Angular
