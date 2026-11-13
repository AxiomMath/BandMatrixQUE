module

public import BlockBand.SourceProcess.Stochastic.MartingaleProblem
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Calculus for the martingale-problem converse

* `mpGenerator_congr`: `𝓛φ(y)` depends only on the germ of `φ` at `y`;
* `mpGenerator_coord`: `𝓛(y_i) = b_i`; `mpGenerator_coord_mul`: `𝓛(y_i y_j) = b_i y_j + b_j y_i +
  a_ij` when `a(y)` is symmetric;
* `continuous_mpGenerator`: `𝓛φ` is continuous for a `C²` test supported in an open `U` on
  which `b, a` are continuous;
* `exists_cutoff`: for `W` with compact closure in an open `U`, a smooth compactly supported
  `χ` with `tsupport χ ⊆ U` and `χ = 1` on an open neighbourhood of `closure W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {d : ℕ} {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}

theorem mpGenerator_congr {φ ψ : (Fin d → ℝ) → ℝ} {y : Fin d → ℝ} (h : φ =ᶠ[𝓝 y] ψ) :
    mpGenerator b a φ y = mpGenerator b a ψ y := by
  have h1 := h.fderiv (𝕜 := ℝ)
  simp only [mpGenerator, h1.eq_of_nhds, h1.fderiv_eq]

theorem mpGenerator_coord (i : Fin d) (y : Fin d → ℝ) :
    mpGenerator b a (fun z => z i) y = b y i := by
  have hd : ∀ w, fderiv ℝ (fun z : Fin d → ℝ => z i) w = ContinuousLinearMap.proj i :=
    fun w => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).fderiv
  have hdd : fderiv ℝ (fderiv ℝ fun z : Fin d → ℝ => z i) y = 0 := by
    rw [show (fderiv ℝ fun z : Fin d → ℝ => z i) = fun _ => ContinuousLinearMap.proj i from
      funext hd]
    exact fderiv_const_apply _
  simp only [mpGenerator, hd, hdd, ContinuousLinearMap.proj_apply, Pi.single_apply]
  simp

theorem mpGenerator_coord_mul (i j : Fin d) (y : Fin d → ℝ) (hsym : a y i j = a y j i) :
    mpGenerator b a (fun z => z i * z j) y = b y i * y j + b y j * y i + a y i j := by
  set Pi_ := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)
  set Pj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j)
  have hd : ∀ w : Fin d → ℝ, fderiv ℝ (fun z : Fin d → ℝ => z i * z j) w =
      w i • Pj + w j • Pi_ := fun w => (Pi_.hasFDerivAt.mul Pj.hasFDerivAt).fderiv
  have hdd : fderiv ℝ (fderiv ℝ fun z : Fin d → ℝ => z i * z j) y =
      Pi_.smulRight Pj + Pj.smulRight Pi_ := by
    rw [show (fderiv ℝ fun z : Fin d → ℝ => z i * z j) = fun w => w i • Pj + w j • Pi_ from
      funext hd]
    exact ((Pi_.hasFDerivAt.smul_const Pj).add (Pj.hasFDerivAt.smul_const Pi_)).fderiv
  have key : ∀ (f : Fin d → ℝ) (m : Fin d), ∑ k, f k * Pi.single (M := fun _ => ℝ) k 1 m = f m := by
    intro f m; simp [Pi.single_apply]
  simp only [mpGenerator, hd, hdd, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    Pi_, Pj, ContinuousLinearMap.proj_apply, smul_eq_mul]
  have e1 : ∑ k, b y k * (y i * Pi.single (M := fun _ => ℝ) k 1 j +
      y j * Pi.single (M := fun _ => ℝ) k 1 i) =
      y i * ∑ k, b y k * Pi.single (M := fun _ => ℝ) k 1 j +
        y j * ∑ k, b y k * Pi.single (M := fun _ => ℝ) k 1 i := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ k, ∑ l, a y k l * (Pi.single (M := fun _ => ℝ) k 1 i *
      Pi.single (M := fun _ => ℝ) l 1 j + Pi.single (M := fun _ => ℝ) k 1 j *
      Pi.single (M := fun _ => ℝ) l 1 i) = a y i j + a y j i := by
    have : ∀ k, ∑ l, a y k l * (Pi.single (M := fun _ => ℝ) k 1 i *
        Pi.single (M := fun _ => ℝ) l 1 j + Pi.single (M := fun _ => ℝ) k 1 j *
        Pi.single (M := fun _ => ℝ) l 1 i) =
        a y k j * Pi.single (M := fun _ => ℝ) k 1 i +
          a y k i * Pi.single (M := fun _ => ℝ) k 1 j := by
      intro k
      have h1 := key (fun l => a y k l) j
      have h2 := key (fun l => a y k l) i
      rw [← h1, ← h2, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_add_distrib]
    have h3 := key (fun k => a y k j) i
    have h4 := key (fun k => a y k i) j
    rw [h3, h4]
  rw [e1, e2, key, key, hsym]
  ring

theorem continuous_mpGenerator {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hb : ContinuousOn b U)
    (ha : ContinuousOn a U) {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : tsupport φ ⊆ U) : Continuous (mpGenerator b a φ) := by
  have h1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv two_ne_zero
  have h2 : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  refine continuous_iff_continuousAt.2 fun y => ?_
  by_cases hy : y ∈ U
  · refine ContinuousOn.continuousAt ?_ (hU.mem_nhds hy)
    unfold mpGenerator
    refine ContinuousOn.add (continuousOn_finsetSum _ fun i _ => ?_)
      (continuousOn_const.mul (continuousOn_finsetSum _ fun i _ =>
        continuousOn_finsetSum _ fun j _ => ?_))
    · exact (((continuous_apply i).comp_continuousOn hb)).mul
        (h1.clm_apply continuous_const).continuousOn
    · exact ((continuous_apply j).comp (continuous_apply i) |>.comp_continuousOn ha).mul
        ((h2.clm_apply continuous_const).clm_apply continuous_const).continuousOn
  · have hnot : y ∉ tsupport φ := fun h => hy (hφs h)
    have hev : ∀ᶠ w in 𝓝 y, w ∉ tsupport φ := (isClosed_tsupport φ).isOpen_compl.mem_nhds hnot
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [hev] with w hw
    rw [mpGenerator_congr (notMem_tsupport_iff_eventuallyEq.1 hw)]
    simp [mpGenerator]

theorem exists_cutoff {U W : Set (Fin d → ℝ)} (hU : IsOpen U) (hWc : IsCompact (closure W))
    (hWU : closure W ⊆ U) :
    ∃ (χ : (Fin d → ℝ) → ℝ) (V : Set (Fin d → ℝ)), IsOpen V ∧ closure W ⊆ V ∧
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ (∀ y ∈ V, χ y = 1) ∧
      ∀ y, 0 ≤ χ y ∧ χ y ≤ 1 := by
  obtain ⟨V₁, hV₁o, hWV₁, hV₁U, hV₁c⟩ := exists_open_between_and_isCompact_closure hWc hU hWU
  obtain ⟨V₂, hV₂o, hWV₂, hV₂V₁, -⟩ :=
    exists_open_between_and_isCompact_closure hWc hV₁o hWV₁
  obtain ⟨χ, hχs, hχr, hχsupp, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    hV₁o isClosed_closure hV₂V₁
  have hts : tsupport χ ⊆ closure V₁ := by rw [tsupport, hχsupp]
  refine ⟨χ, V₂, hV₂o, hWV₂, hχs, hV₁c.of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans hV₁U, fun y hy => (hχ1 y).1 (subset_closure hy), fun y => ?_⟩
  have := hχr ⟨y, rfl⟩
  exact ⟨this.1, this.2⟩

end BlockBand.Transmission.Dual
