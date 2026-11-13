module

public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFSplit

/-!
# Continuity of the reference generator along a regular family

`rfGeneratorContinuous_holds` proves `RFGeneratorContinuousStatement`. If
`ρ : ℝ → Fin N → Fin N → ℝ` and `κ : ℝ → Fin N → ℝ` are continuous on `[a, c]`, and
`(s, z) ↦ D_z g_s(z)` and `(s, z) ↦ D_z² g_s(z)` are continuous on `[a, c] × ℂ^{N×r}` (as maps
into the spaces of continuous (bi)linear maps, operator norm), then
`(s, z) ↦ refGenerator ρ κ s (g s) z` is continuous on `[a, c] × ℂ^{N×r}`.

Proof: `refGenerator` is a finite sum of products of the coefficients `ρ s i j`, `κ s i` with
evaluations of `D g_s(z)` and `D² g_s(z)` at vectors depending continuously on `z`
(`lmul X z`, `lmul X (lmul X z)`, `rowProj i z`, constants); evaluation of a continuously
varying continuous linear map at a continuously varying vector is continuous
(`ContinuousOn.clm_apply`). Continuity of `g` itself is not needed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.AbstractFlow

open Set

variable {N r : ℕ}

theorem continuous_lmul (X : Matrix (Fin N) (Fin N) ℂ) :
    Continuous (BlockBand.Palm.ReferenceFlow.lmul (p := r) X) := by
  unfold BlockBand.Palm.ReferenceFlow.lmul
  fun_prop

theorem continuous_rowProj (i : Fin N) :
    Continuous (BlockBand.Palm.ReferenceFlow.rowProj (p := r) i) := by
  refine continuous_pi fun k => continuous_pi fun β => ?_
  show Continuous fun z : Fin N → Fin r → ℂ => if k = i then z k β else 0
  by_cases hki : k = i
  · simp only [hki, ite_true]
    exact (continuous_apply β).comp (continuous_apply i)
  · simp only [hki, ite_false]
    exact continuous_const

/-- Continuity of `(s, z) ↦ refGenerator ρ κ s (g s) z` on `[a, c] × ℂ^{N×r}`. -/
theorem rfGeneratorContinuous_holds :
    ∀ N r, BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF.RFGeneratorContinuousStatement N r := by
  intro N r ρ κ a c hρ hκ g hD1 hD2
  have hfst : MapsTo (fun p : ℝ × (Fin N → Fin r → ℂ) => p.1)
      (Icc a c ×ˢ univ) (Icc a c) := fun p hp => hp.1
  have hρij : ∀ i j, ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => ρ p.1 i j)
      (Icc a c ×ˢ univ) := by
    intro i j
    have h1 : ContinuousOn (fun x => ρ x i j) (Icc a c) :=
      continuousOn_pi.mp (continuousOn_pi.mp hρ i) j
    exact h1.comp continuousOn_fst hfst
  have hκi : ∀ i, ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => κ p.1 i)
      (Icc a c ×ˢ univ) := by
    intro i
    have h1 : ContinuousOn (fun x => κ x i) (Icc a c) :=
      continuousOn_pi.mp hκ i
    exact h1.comp continuousOn_fst hfst
  have hvec : ∀ v : (Fin N → Fin r → ℂ) → (Fin N → Fin r → ℂ), Continuous v →
      ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => v p.2) (Icc a c ×ˢ univ) :=
    fun v hv => (hv.comp continuous_snd).continuousOn
  have hD1v : ∀ v : (Fin N → Fin r → ℂ) → (Fin N → Fin r → ℂ), Continuous v →
      ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => fderiv ℝ (g p.1) p.2 (v p.2))
        (Icc a c ×ˢ univ) :=
    fun v hv => hD1.clm_apply (hvec v hv)
  have hD2v : ∀ u v : (Fin N → Fin r → ℂ) → (Fin N → Fin r → ℂ), Continuous u → Continuous v →
      ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) =>
        BlockBand.Palm.ReferenceFlow.D2 (g p.1) p.2 (u p.2) (v p.2)) (Icc a c ×ˢ univ) :=
    fun u v hu hv => (hD2.clm_apply (hvec u hu)).clm_apply (hvec v hv)
  have hvf : ∀ X : Matrix (Fin N) (Fin N) ℂ,
      ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) =>
        BlockBand.Palm.ReferenceFlow.vfSq X (g p.1) p.2) (Icc a c ×ˢ univ) := by
    intro X
    unfold BlockBand.Palm.ReferenceFlow.vfSq
    exact (hD2v _ _ (continuous_lmul X) (continuous_lmul X)).add
      (hD1v _ ((continuous_lmul X).comp (continuous_lmul X)))
  unfold BlockBand.Palm.ReferenceFlow.refGenerator
  refine ContinuousOn.add (continuousOn_const.mul (continuousOn_finsetSum _ fun i _ =>
    continuousOn_finsetSum _ fun j _ => ?_)) (continuousOn_finsetSum _ fun i _ => ?_)
  · by_cases hij : i < j
    · simp only [hij, ite_true]
      exact (hρij i j).mul ((hvf _).add (hvf _))
    · simp only [hij, ite_false]
      exact continuousOn_const
  · refine (hκi i).mul ((continuousOn_const.mul (hD1v _ (continuous_rowProj i))).add
      (continuousOn_const.mul (continuousOn_finsetSum _ fun α _ => ?_)))
    exact (hD2v _ _ continuous_const continuous_const).add
      (hD2v _ _ continuous_const continuous_const)

end BlockBand.Critical.RelativeVectors.AbstractFlow
