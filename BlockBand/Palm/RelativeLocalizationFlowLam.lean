module

public import BlockBand.Palm.RelativeLocalizationAdapter
public import BlockBand.Palm.RelativeLocalizationLabels
public import BlockBand.Palm.RelativeLocalizationSemimart
public import BlockBand.Palm.RelativeLocalizationDrift
public import BlockBand.Model.Construction.OrderedSpectrum
public import BlockBand.Coarea.FreshPalmDensity

/-!
# Relative localization: the eigenvalue process in fixed labels

`flowLam F t ω k = freshEigenvalue (flowInit F ω + flowBM N t ω) k` is the increasing
eigenvalue path of the matrix flow `flowH` (equal to `flowEigenvalue F a ω (a + t)` when `ω.1`
is Hermitian, `flowMatrix_eq`). Proved:

* `flowLam_continuous` : continuous in `t` for **every** sample (Hermitian `F`);
* `flowLam_adapted` : `flowLam F t` is `flowFiltration N t`-measurable;
* `dysonDrift_comp_perm` : `dysonDrift N (λ ∘ σ) k = dysonDrift N λ (σ k)` (permutations);
* `flowLam_semimartingale` : from `DysonBrownianMotion`, for every start `s > 0`,
  `u ↦ flowLam F (s+u)` is a continuous semimartingale for `shiftFiltration (flowFiltration N) s`
  with drift `dysonDrift N (flowLam F (s+u) ω)` and covariance `δ_kl/N`
  (nonincreasing labels are converted with `freshEigenvalue_eq_dyson`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {N : ℕ}

/-- The matrix flow `H_t = flowInit F + flowBM N t` (time measured from `a`). -/
def flowH (F : Matrix (Fin N) (Fin N) ℂ) (t : ℝ≥0) (ω : FlowSample N) :
    Matrix (Fin N) (Fin N) ℂ :=
  flowInit F ω + flowBM N t ω

/-- Increasing eigenvalues of the matrix flow `flowH`. -/
def flowLam (F : Matrix (Fin N) (Fin N) ℂ) (t : ℝ≥0) (ω : FlowSample N) : Fin N → ℝ :=
  fun k => freshEigenvalue (flowH F t ω) k

theorem flowH_isHermitian {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (t : ℝ≥0)
    (ω : FlowSample N) : (flowH F t ω).IsHermitian :=
  (flowInit_isHermitian hF ω).add ((flowBM_isHermitianBrownian (N := N) 0).hermitian t ω)

theorem flowLam_continuous {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (ω : FlowSample N) : Continuous fun t => flowLam F t ω := by
  have hpath : Continuous fun t => flowH F t ω :=
    continuous_const.add ((flowBM_isHermitianBrownian (N := N) 0).continuous ω)
  have hsub : Continuous fun t =>
      (⟨flowH F t ω, flowH_isHermitian hF t ω⟩ : BlockBand.Model.Construction.HermitianMatrix (Fin N)) :=
    hpath.subtype_mk _
  refine continuous_pi fun k => ?_
  have := (BlockBand.Model.Construction.continuous_increasingEigenvalue
    (Fin.cast (Fintype.card_fin N).symm k)).comp hsub
  refine this.congr fun t => ?_
  simp only [Function.comp, flowLam, freshEigenvalue,
    BlockBand.Model.Construction.rawIncreasingEigenvalue_eq _ _ (flowH_isHermitian hF t ω)]

theorem flowLam_adapted (F : Matrix (Fin N) (Fin N) ℂ) (t : ℝ≥0) :
    Measurable[flowFiltration N t] (flowLam F t) := by
  have h1 : Measurable[flowFiltration N t] (flowInit F) :=
    (measurable_flowInit F).mono ((flowFiltration N).mono (zero_le (a := t))) le_rfl
  have h2 : Measurable[flowFiltration N t] (flowBM N t) :=
    (flowBM_isHermitianBrownian (N := N) 0).adapted t
  have hadd : Measurable fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ =>
      p.1 + p.2 := by
    apply Measurable.of_eval_matrix
    intro i j
    exact (measurable_fst.eval_matrix).add (measurable_snd.eval_matrix)
  have hH : Measurable[flowFiltration N t] (flowH F t) := hadd.comp (h1.prodMk h2)
  refine @measurable_pi_iff (FlowSample N) (Fin N) (fun _ => ℝ) (flowFiltration N t) _ _ |>.mpr
    fun k => ?_
  exact (BlockBand.Coarea.FreshPalm.measurable_freshEigenvalue k).comp hH

/-- The Dyson drift is permutation-equivariant. -/
theorem dysonDrift_comp_perm (lam : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (k : Fin N) :
    dysonDrift N (lam ∘ σ) k = dysonDrift N lam (σ k) := by
  unfold dysonDrift
  congr 1
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Function.comp, sub_self, div_zero, sub_zero]
  exact Equiv.sum_comp σ (fun j => 1 / (lam (σ k) - lam j))

/-- The eigenvalue path `u ↦ flowLam F (s+u)` is a continuous semimartingale with drift
`dysonDrift` and covariance `δ_kl/N`. -/
theorem flowLam_semimartingale (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) (a : ℝ) (s : ℝ≥0) (hs : 0 < s) :
    IsContinuousSemimartingale (flowLaw N a) (shiftFiltration (flowFiltration N) s)
      (fun u ω => flowLam F (s + u) ω)
      (fun u ω k => dysonDrift N (flowLam F (s + u) ω) k)
      (fun _ _ => Matrix.of fun k l => if k = l then 1 / (N : ℝ) else 0) := by
  have h := (hDBM (FlowSample N) (flowLaw N a) (flowFiltration N) (flowBM N) (flowInit F)
    (flowBM_isHermitianBrownian a) (measurable_flowInit F) (flowInit_isHermitian hF)).2.1 s hs 0
  have hr := IsContinuousSemimartingale.reindex h (fun k : Fin N => finSumFinEquiv (Sum.inl k.rev))
  have hlam : ∀ u ω, (fun k : Fin N => dysonState N 0 (flowInit F ω + flowBM N (s + u) ω)
      (finSumFinEquiv (Sum.inl k.rev))) = flowLam F (s + u) ω := by
    intro u ω
    funext k
    simp only [dysonState, Equiv.symm_apply_apply, flowLam]
    exact (freshEigenvalue_eq_dyson (flowH_isHermitian hF (s + u) ω) k).symm
  have hdrift : ∀ u ω, (fun k : Fin N => dysonStateDrift N
      (dysonState N 0 (flowInit F ω + flowBM N (s + u) ω)) (finSumFinEquiv (Sum.inl k.rev))) =
      fun k => dysonDrift N (flowLam F (s + u) ω) k := by
    intro u ω
    funext k
    simp only [dysonStateDrift, Equiv.symm_apply_apply]
    have : (fun i : Fin N => dysonState N 0 (flowInit F ω + flowBM N (s + u) ω)
        (finSumFinEquiv (Sum.inl i))) = flowLam F (s + u) ω ∘ Fin.revPerm := by
      funext i
      simp only [dysonState, Equiv.symm_apply_apply, Function.comp, flowLam,
        Fin.revPerm_apply]
      have := freshEigenvalue_eq_dyson (flowH_isHermitian hF (s + u) ω) i.rev
      rw [Fin.rev_rev] at this
      exact this.symm
    rw [this, dysonDrift_comp_perm]
    simp
  have hcov : ∀ u ω, (Matrix.of fun k l : Fin N => dysonStateCov N
      (dysonState N 0 (flowInit F ω + flowBM N (s + u) ω)) (finSumFinEquiv (Sum.inl k.rev))
        (finSumFinEquiv (Sum.inl l.rev))) =
      Matrix.of fun k l => if k = l then 1 / (N : ℝ) else 0 := by
    intro u ω
    ext k l
    simp [dysonStateCov, Fin.rev_inj]
  convert hr using 1
  · funext u ω; exact (hlam u ω).symm
  · funext u ω; exact (hdrift u ω).symm
  · funext u ω; exact (hcov u ω).symm

end BlockBand.Palm.RelativeLocalization
