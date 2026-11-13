module

public import BlockBand.Palm.MomentFlow.MultiDrift
public import BlockBand.Palm.MomentFlow.MaxPrinciple
public import BlockBand.Palm.RelativeLocalizationODE

/-!
# `r`-particle finite speed: the moment generator as a matrix on the sector

* `cfgMat c r p q = (𝓑_c δ_{ξ_q})(ξ_p)`; `cfgMat_act`: `Σ_q cfgMat p q f(ξ_q) = (𝓑_c f)(ξ_p)`.
* `cfgMat_isSubGenerator`: for nonnegative off-diagonal rates it is a sub-generator
  (off-diagonal `≥ 0`, row sums `= 0`).
* `continuous_cfgRate`, `continuous_cfgMat_comp`: with truncated short rates (`g > 0`) it is
  continuous in `λ`.
* `cfgExt v`: extension of `v : ℝ^M` to configurations (zero off the sector);
  `isMomentFlowSolution_of_forwardMass`: a solution of the mass ODE gives a solution of the
  moment flow `IsMomentFlowSolution c r s u` (the form used by the conditional-moments lemma).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Finset Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm.RelativeLocalization

variable {N : ℕ}

/-- Number of `r`-particle configurations. -/
abbrev sectorCard (N r : ℕ) : ℕ := (sector N r).card

/-- Enumeration of the `r`-particle sector. -/
def sectorEnum (N r : ℕ) (p : Fin (sectorCard N r)) : Occ N :=
  ((sector N r).equivFin.symm p : Occ N)

theorem sectorEnum_mem (r : ℕ) (p : Fin (sectorCard N r)) : sectorEnum N r p ∈ sector N r :=
  ((sector N r).equivFin.symm p).2

theorem sectorEnum_injective (r : ℕ) : Function.Injective (sectorEnum N r) := by
  intro p q h
  have : (sector N r).equivFin.symm p = (sector N r).equivFin.symm q := Subtype.ext h
  exact (sector N r).equivFin.symm.injective this

/-- Index of a configuration of the sector. -/
def sectorIndex {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r) : Fin (sectorCard N r) :=
  (sector N r).equivFin ⟨ξ, hξ⟩

theorem sectorEnum_index {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r) :
    sectorEnum N r (sectorIndex hξ) = ξ := by
  simp [sectorEnum, sectorIndex]

/-- Sums over the enumeration are sums over the sector. -/
theorem sum_sectorEnum (r : ℕ) (f : Occ N → ℝ) :
    ∑ p, f (sectorEnum N r p) = ∑ ξ ∈ sector N r, f ξ := by
  rw [← Finset.sum_coe_sort (sector N r)]
  exact Fintype.sum_equiv (sector N r).equivFin.symm _ _ fun p => rfl

/-- Extension by zero of a vector on the enumeration to all configurations. -/
def cfgExt (r : ℕ) (v : Fin (sectorCard N r) → ℝ) (ζ : Occ N) : ℝ :=
  ∑ q, if sectorEnum N r q = ζ then v q else 0

theorem cfgExt_enum (r : ℕ) (v : Fin (sectorCard N r) → ℝ) (p : Fin (sectorCard N r)) :
    cfgExt r v (sectorEnum N r p) = v p := by
  unfold cfgExt
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    rw [ite_eq_right fun h => hq (sectorEnum_injective r h)]
  · simp

theorem cfgExt_of_mem {r : ℕ} (v : Fin (sectorCard N r) → ℝ) {ξ : Occ N}
    (hξ : ξ ∈ sector N r) : cfgExt r v ξ = v (sectorIndex hξ) := by
  conv_lhs => rw [← sectorEnum_index hξ]
  exact cfgExt_enum r v _

/-- Matrix of `𝓑_c` on the sector: `(𝓑_c δ_{ξ_q})(ξ_p)`. -/
def cfgMat (c : Fin N → Fin N → ℝ) (r : ℕ) (p q : Fin (sectorCard N r)) : ℝ :=
  momentGenerator c (fun ζ => if ζ = sectorEnum N r q then 1 else 0) (sectorEnum N r p)

/-- Linearity of the generator over finite sums. -/
theorem momentGenerator_sum {ι : Type*} (s : Finset ι) (c : Fin N → Fin N → ℝ) (a : ι → ℝ)
    (g : ι → Occ N → ℝ) (ξ : Occ N) :
    momentGenerator c (fun ζ => ∑ q ∈ s, a q * g q ζ) ξ =
      ∑ q ∈ s, a q * momentGenerator c (g q) ξ := by
  unfold momentGenerator
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-- `Σ_q cfgMat p q f(ξ_q) = (𝓑_c f)(ξ_p)`. -/
theorem cfgMat_act (c : Fin N → Fin N → ℝ) (r : ℕ) (f : Occ N → ℝ) (p : Fin (sectorCard N r)) :
    ∑ q, cfgMat c r p q * f (sectorEnum N r q) = momentGenerator c f (sectorEnum N r p) := by
  have hcongr : ∀ ζ ∈ sector N r,
      (fun ζ => ∑ q, f (sectorEnum N r q) * (if ζ = sectorEnum N r q then 1 else 0)) ζ = f ζ := by
    intro ζ hζ
    simp only
    rw [Finset.sum_eq_single (sectorIndex hζ)]
    · rw [sectorEnum_index hζ]; simp
    · intro q _ hq
      rw [ite_eq_right fun h => hq (sectorEnum_injective r (by rw [sectorEnum_index hζ]; exact h.symm)),
        mul_zero]
    · simp
  rw [← momentGenerator_congr_sector c hcongr (sectorEnum_mem r p), momentGenerator_sum]
  exact Finset.sum_congr rfl fun q _ => by unfold cfgMat; ring

theorem cfgMat_offdiag_nonneg {c : Fin N → Fin N → ℝ} (hc : ∀ i j, i ≠ j → 0 ≤ c i j) (r : ℕ)
    {p q : Fin (sectorCard N r)} (hpq : p ≠ q) : 0 ≤ cfgMat c r p q := by
  unfold cfgMat momentGenerator
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j hj => ?_
  have hij : i ≠ j := Ne.symm (mem_erase.1 hj).1
  have hne : sectorEnum N r p ≠ sectorEnum N r q := fun h => hpq (sectorEnum_injective r h)
  simp only [ite_eq_right hne, sub_zero]
  refine mul_nonneg (mul_nonneg (hc i j hij) (jumpCoeff_nonneg _ i j)) ?_
  split_ifs <;> norm_num

theorem cfgMat_rowSum (c : Fin N → Fin N → ℝ) (r : ℕ) (p : Fin (sectorCard N r)) :
    ∑ q, cfgMat c r p q = 0 := by
  have := cfgMat_act c r (fun _ => 1) p
  simp only [mul_one, momentGenerator_const] at this
  exact this

theorem cfgMat_isSubGenerator {c : ℝ → Fin N → Fin N → ℝ}
    (hc : ∀ x i j, i ≠ j → 0 ≤ c x i j) (r : ℕ) (s u : ℝ) :
    IsSubGenerator (fun x => cfgMat (c x) r) s u :=
  fun x _ => ⟨fun _ _ hpq => cfgMat_offdiag_nonneg (hc x) r hpq,
    fun p => (cfgMat_rowSum (c x) r p).le⟩

theorem continuous_cfgRate (hN : 0 < N) (ℓ : ℕ) {g : ℝ} (hg : 0 < g) :
    Continuous fun lam : Fin N → ℝ => cfgRate N lam ℓ g := by
  classical
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold cfgRate
  split_ifs
  · exact (continuous_truncRate hN hg).comp ((continuous_apply i).sub (continuous_apply j))
  · exact continuous_const

theorem continuous_cfgMat_comp {X : Type*} [TopologicalSpace X] {c : X → Fin N → Fin N → ℝ}
    (hc : Continuous c) (r : ℕ) : Continuous fun x => cfgMat (c x) r := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  unfold cfgMat momentGenerator
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (((continuous_apply j).comp ((continuous_apply i).comp hc)).mul continuous_const).mul
    continuous_const

/-- A solution of the mass ODE on the enumeration is a solution of the moment flow. -/
theorem isMomentFlowSolution_of_forwardMass {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {s u : ℝ}
    {v₀ : Fin (sectorCard N r) → ℝ} {v : ℝ → Fin (sectorCard N r) → ℝ}
    (hv : ForwardMassSolution (fun x => cfgMat (c x) r) s u v₀ v) :
    IsMomentFlowSolution c r s u (fun x => cfgExt r (v x)) := by
  intro ξ hξ
  have hfun : (fun x => cfgExt r (v x) ξ) = fun x => v x (sectorIndex hξ) :=
    funext fun x => cfgExt_of_mem (v x) hξ
  refine ⟨?_, fun x hx => ?_⟩
  · rw [hfun]; exact (continuousOn_pi.1 hv.2.1) _
  · rw [hfun]
    have h := hasDerivAt_pi.1 (hv.2.2 x hx) (sectorIndex hξ)
    have e := cfgMat_act (c x) r (cfgExt r (v x)) (sectorIndex hξ)
    rw [sectorEnum_index hξ] at e
    simp only [cfgExt_enum] at e
    rw [← e]
    exact h

end BlockBand.Palm.MomentFlow
