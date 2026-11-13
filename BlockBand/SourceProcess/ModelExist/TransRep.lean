module

public import BlockBand.SourceProcess.ModelExist.TransMeas

/-!
# The born compensated coordinates are the transformed compensated coordinates

`BornRepresents ω`: the continuous part of `G − J` is the transform of the increments of `𝒢`
after the birth times (this is where the perpendicular births enter). Under it, along a
continuous path of `𝒢`:
* `bornCompensated_eq_bornRep`: `bornCompensated D₀ 𝖣 G J e = bornRep (gramCompensated 𝒢) e`;
* `integral_cov_bornG` (proved in a sibling module): `∫_0^t Γ(G_s) ds = ∫_0^t Σ 1{θ_e ∨ θ_e' < s} c_e c_e' Γ'(𝒢_s) ds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Finset
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.BornUnique
open scoped NNReal ENNReal

variable {Ω : Type*} {c c' F : Type*} [Fintype c] [DecidableEq c] [Fintype c'] [Fintype F]

/-- The jump process `J_t = birthSum j β t`. -/
def bJ (j : F → Matrix c c ℂ × Matrix c c ℂ) (β : F → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    Matrix c c ℂ × Matrix c c ℂ :=
  birthSum j (fun f => β f ω) t

/-- The continuous part of `G − J` is the transform of the increments of `𝒢` after `θ_e`. -/
def BornRepresents (𝒢 : ℝ≥0 → Ω → Matrix c' c' ℂ × Matrix c' c' ℂ) (θ : c → Ω → ℝ≥0)
    (lam : c → Ω → c' → ℂ) (j : F → Matrix c c ℂ × Matrix c c ℂ) (β : F → Ω → ℝ) (ω : Ω) :
    Prop :=
  ∀ (t : ℝ≥0) (e : Fin 2 × c × c),
    gramEntry e (bornG 𝒢 θ lam t ω - bJ j β t ω) - gramEntry e (bornG 𝒢 θ lam 0 ω - bJ j β 0 ω) =
      ∑ x, ∑ x', bCoef lam e ω x x' * (gramEntry (e.1, x, x') (𝒢 t ω) -
        gramEntry (e.1, x, x') (𝒢 (stopTime (bTime θ e ω) t) ω))

variable {D0 : ℝ} {D : Matrix c c ℂ} {D' : Matrix c' c' ℂ}
  {𝒢 : ℝ≥0 → Ω → Matrix c' c' ℂ × Matrix c' c' ℂ} {θ : c → Ω → ℝ≥0} {lam : c → Ω → c' → ℂ}
  {j : F → Matrix c c ℂ × Matrix c c ℂ} {β : F → Ω → ℝ}

omit [DecidableEq c] in
theorem integrableOn_drift_path {ω : Ω} (hc : Continuous fun t => 𝒢 t ω)
    (r : Fin 2) (x x' : c') (t : ℝ≥0) :
    IntegrableOn (fun s : ℝ => gramDriftEntry D0 D' (r, x, x') (𝒢 s.toNNReal ω)) (Ioc 0 t) :=
  integrableOn_comp_path hc (continuous_gramDriftEntry D0 D' (r, x, x')) t

theorem bornCompensated_eq_bornRep (hsig : ∀ t ω, bornL θ lam t ω * D * (bornL θ lam t ω)ᴴ = D')
    {ω : Ω} (hrep : BornRepresents 𝒢 θ lam j β ω) (hc : Continuous fun t => 𝒢 t ω)
    (e : Fin 2 × c × c) (t : ℝ≥0) :
    bornCompensated D0 D (bornG 𝒢 θ lam) (bJ j β) e t ω =
      bornRep θ lam (gramCompensated D0 D' 𝒢) e t ω := by
  have hd : ∀ s : ℝ, gramDriftEntry D0 D e (bornG 𝒢 θ lam s.toNNReal ω) =
      ∑ x, ∑ x', (if bTime θ e ω ≤ (s.toNNReal : WithTop ℝ≥0) then
        bCoef lam e ω x x' * gramDriftEntry D0 D' (e.1, x, x') (𝒢 s.toNNReal ω) else 0) := by
    intro s
    rw [gramDriftEntry_bornG D0 𝒢 hsig]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
    split_ifs <;> simp
  have hI : ∀ x x', IntegrableOn (fun s : ℝ => bCoef lam e ω x x' *
      gramDriftEntry D0 D' (e.1, x, x') (𝒢 s.toNNReal ω)) (Ioc 0 t) := fun x x' =>
    (integrableOn_drift_path hc e.1 x x' t).const_mul _
  have hint : ∫ s in Ioc (0 : ℝ) t, gramDriftEntry D0 D e (bornG 𝒢 θ lam s.toNNReal ω) =
      ∑ x, ∑ x', bCoef lam e ω x x' * ((∫ s in Ioc (0 : ℝ) t,
        gramDriftEntry D0 D' (e.1, x, x') (𝒢 s.toNNReal ω)) - ∫ s in Ioc (0 : ℝ)
          (stopTime (bTime θ e ω) t), gramDriftEntry D0 D' (e.1, x, x') (𝒢 s.toNNReal ω)) := by
    simp_rw [hd]
    rw [integral_finsetSum _ fun x _ => integrable_finsetSum _ fun x' _ =>
      integrableOn_ite_le (hI x x') _]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_finsetSum _ fun x' _ => integrableOn_ite_le (hI x x') _]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [setIntegral_ite_ge _ _ (hI x x'), integral_const_mul, integral_const_mul, mul_sub]
  unfold bornCompensated
  rw [show bJ j β 0 ω = bJ j β 0 ω from rfl, hrep t e, hint, bornRep, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x' _ => ?_
  simp only [gramCompensated, stoppedProcess_eq_stopTime]
  ring

end BlockBand.SourceProcess.ModelExist
