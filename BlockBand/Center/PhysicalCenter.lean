module

public import BlockBand.Center.PhysicalCenterLaw
public import BlockBand.Center.DivergenceSecondMoment

/-!
# The physical center bound

The four probabilistic inputs are stated as propositions:
* `PcSplittingExists` — an exact simultaneous splitting exists;
* `PcEnergyPrimitive` — the per-edge Gaussian integration by parts with Hellmann–Feynman behind
  the energy primitive identity, before the cyclic sum;
* `PcDivergenceIsometry` — the divergence isometry;
* `PcCenterCyclic` — the cyclic invariance used in the energy primitive identity, for the center
  family itself.

Proved here, with the energy cutoff `ϑ ≡ 1` (the smooth center is already
supported in a fixed bulk interval, so `F_e` is bounded without it):
1. replacement of `j_e` by `j_e^{sm}` under the pair law, error `C_2 W⁻²`
   (`SmoothCenterContract`, replacement field with `D = 2`; `pc_replace_le`);
2. transport of the pair law between extensions (`pc_pair_integral_transfer`,
   `pc_isCenterSplitting_of_exact`);
3. the cyclic sum `Σ_e E♯_e f_e(Λ) = (n/2) E ∫_{e_α}^{Λ} D` (`pc_energy_sum`);
4. the divergence bound from the divergence isometry through
   `secondMoment_le_physical_budget_of_isometry`, with `E f_e² ≤ C/W⁴` and
   `‖∂_{ξ_g} f_e‖₂ ≤ C W⁻¹(ρ^{d(e,g)} + W^{-1/2})` by Hölder from the smooth center bounds
   (`q = 4`), and the cyclic row sum `pc_geom_sum_le` (`pc_divergence_le`);
5. the expectation random-energy bound with `ω = (n√W)⁻¹` from the rank location bound
   (`q = 4`), through the elementary `pc_terminal_energy_le`;
6. `C_2 W⁻² ≤ C_2 √T/(√n W^{3/2})` for `n ≤ TW`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE BlockBand.QUE.Fourier BlockBand.Model.Construction
open BlockBand.QUE.PairResidual
open scoped ENNReal NNReal Interval

/-!
## 1. The probabilistic inputs
-/

/-- **Existence of the simultaneous splitting**: a diagonal block receives total variance
`s/W ≤ c/W` and a bond receives `s/(2W) ≤ b/W`. For every parameter set and model there is an
extension with the exact physical law carrying `H = V + Σ_g (G_g⁰ + ξ_g I_{S_g})` with all
clauses of `SimultaneousSplitting.IsExact`. -/
def PcSplittingExists : Prop :=
  ∀ (p : Parameters) (model : p.GaussianRingModel), ∃ S : SimultaneousSplitting p model, S.IsExact

/-- **Per-edge energy primitive** (the Gaussian integration by parts and Hellmann–Feynman step of
the energy primitive identity, before the cyclic sum). Law: an exact
simultaneous splitting `S` (any parameters, model, rank `α`, edge `g`). For every jointly Borel
`Ψ` with `|Ψ| ≤ 1` and every deterministic `e₀`, with `Λ = λ_α(H)`, `H^{(g)} = H - G_g`,
`σ² = s/(2W)²` (`σ⁻² = (2W)²/s`, `s = splitS p`):
`ξ_g ∫_{e₀}^{Λ} Ψ(H^{(g)}, E) dE` is integrable and
`E♯_{α,g} Ψ(H^{(g)}, Λ) = (n/2) σ⁻² E[ξ_g ∫_{e₀}^{Λ} Ψ(H^{(g)}, E) dE]`.
(`F_g = ∫_{e_α}^{Λ} f_g` has `∂_{ξ_g} F_g = q_g f_g(Λ)`, `q_g = p_g + p_{g+1}`, since
`H^{(g)}` does not contain `ξ_g` and `∂_{ξ_g} Λ = q_g` a.e.; Stein's identity
`E ξ F = σ² E ∂_ξ F`; `E♯_{α,g} = (n/2) E[q_g ·]`.) -/
def PcEnergyPrimitive : Prop :=
  ∀ (p : Parameters) (model : p.GaussianRingModel) (S : SimultaneousSplitting p model), S.IsExact →
    ∀ (α : Fin p.N) (g : ZMod p.n) (Ψ : p.SiteMatrix → ℝ → ℝ),
      Measurable (fun x : p.SiteMatrix × ℝ => Ψ x.1 x.2) → (∀ H E, |Ψ H E| ≤ 1) → ∀ e₀ : ℝ,
        Integrable (fun ω => S.ξ g ω * ∫ E in e₀..physicalOrderedEigenvalue p (S.X.Hm ω) α,
          Ψ (S.X.Hm ω - embedPair p g (S.G g ω)) E) S.X.P ∧
        (∫ ω, Ψ (S.X.Hm ω - embedPair p g (S.G g ω)) (physicalOrderedEigenvalue p (S.X.Hm ω) α)
            ∂extendedPairMeasure p α g S.X.P S.X.Hm) =
          (p.n : ℝ) / 2 * ((2 * (p.W : ℝ)) ^ 2 / splitS p) *
            ∫ ω, S.ξ g ω * (∫ E in e₀..physicalOrderedEigenvalue p (S.X.Hm ω) α,
              Ψ (S.X.Hm ω - embedPair p g (S.G g ω)) E) ∂S.X.P

/-- **The divergence isometry**. Law: an exact
simultaneous splitting `S`. For every family `Ψ_g` (`g ∈ ℤ/n`) of Borel functions of the
residual with `|Ψ_g| ≤ 1`, `C¹` along all shift lines `H₀ + Σ_h x_h P_{S_h}` through Hermitian
band matrices with invertible exterior bonds (an almost-sure set), and
with derivatives `∂_{ξ_h} Ψ_g = ∂_t Ψ_g(H^{(g)} + t P_{S_h})|_{t=0}` in `L⁴` for `h ≠ g`; put
`f_g = Ψ_g(H^{(g)})²`, `∂_{ξ_h} f_g = 2 Ψ_g ∂_{ξ_h} Ψ_g`, `D = σ⁻² Σ_g ξ_g f_g`. Then the
derivatives are a.e. strongly measurable, `D²` is integrable and
`E D² = σ⁻² Σ_g E f_g² + Σ_{g ≠ h} E[(∂_{ξ_h} f_g)(∂_{ξ_g} f_h)]`.
(Two integrations by parts; the second derivative vanishes since `f_h` does not contain
`ξ_h`; Gaussian Sobolev approximation justifies it with first derivatives only.) -/
def PcDivergenceIsometry : Prop :=
  ∀ (p : Parameters) (model : p.GaussianRingModel) (S : SimultaneousSplitting p model), S.IsExact →
    ∀ Ψ : ZMod p.n → p.SiteMatrix → ℝ, (∀ g, Measurable (Ψ g)) → (∀ g H, |Ψ g H| ≤ 1) →
      (∀ g (H₀ : p.SiteMatrix), H₀.IsHermitian → IsRingBanded p H₀ →
        ExteriorBondsInvertible p g H₀ →
        ContDiff ℝ 1 (fun x : ZMod p.n → ℝ => Ψ g (H₀ + ∑ h, (x h : ℂ) • pairProjector p h))) →
      (∀ g h, g ≠ h → eLpNorm (fun ω => deriv (fun t : ℝ =>
          Ψ g (S.X.Hm ω - embedPair p g (S.G g ω) + (t : ℂ) • pairProjector p h)) 0) 4 S.X.P < ⊤) →
      (∀ g h, g ≠ h → AEStronglyMeasurable (fun ω => deriv (fun t : ℝ =>
          Ψ g (S.X.Hm ω - embedPair p g (S.G g ω) + (t : ℂ) • pairProjector p h)) 0) S.X.P) ∧
      Integrable (fun ω => (((2 * (p.W : ℝ)) ^ 2 / splitS p) *
          ∑ g, S.ξ g ω * Ψ g (S.X.Hm ω - embedPair p g (S.G g ω)) ^ 2) ^ 2) S.X.P ∧
      (∫ ω, (((2 * (p.W : ℝ)) ^ 2 / splitS p) *
          ∑ g, S.ξ g ω * Ψ g (S.X.Hm ω - embedPair p g (S.G g ω)) ^ 2) ^ 2 ∂S.X.P) =
        ((2 * (p.W : ℝ)) ^ 2 / splitS p) *
            (∑ g, ∫ ω, (Ψ g (S.X.Hm ω - embedPair p g (S.G g ω)) ^ 2) ^ 2 ∂S.X.P) +
          ∑ g, ∑ h ∈ Finset.univ.erase g,
            ∫ ω, (2 * Ψ g (S.X.Hm ω - embedPair p g (S.G g ω)) * deriv (fun t : ℝ =>
                Ψ g (S.X.Hm ω - embedPair p g (S.G g ω) + (t : ℂ) • pairProjector p h)) 0) *
              (2 * Ψ h (S.X.Hm ω - embedPair p h (S.G h ω)) * deriv (fun t : ℝ =>
                Ψ h (S.X.Hm ω - embedPair p h (S.G h ω) + (t : ℂ) • pairProjector p g)) 0)
              ∂S.X.P

/-- **Cyclic invariance of the center** (used in the energy primitive identity and the
stationarity proposition): for every parameter set,
model and rank, the pair-law second moment of the center of `pairCenterFamily0` is the same at
every pair `g`. (The physical law is invariant under the block rotation, `dysonCenter` is
equivariant — its root is unique for Hermitian residuals, `ctr_root_unique` — and
`physicalOrderedEigenvalue` and the pair masses at a simple eigenvalue are invariant.) -/
def PcCenterCyclic : Prop :=
  ∀ (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N) (g g' : ZMod p.n),
    (∫ ω, (pairCenterFamily0 p model α g).center ω ^ 2 ∂extendedPairMeasure p α g
        (pairCenterFamily0 p model α g).X.P (pairCenterFamily0 p model α g).X.Hm) =
      ∫ ω, (pairCenterFamily0 p model α g').center ω ^ 2 ∂extendedPairMeasure p α g'
        (pairCenterFamily0 p model α g').X.P (pairCenterFamily0 p model α g').X.Hm

/-!
## 2. Per-parameter estimates
-/

section Estimates

variable {p : Parameters} {model : p.GaussianRingModel}

theorem pc_measurable_res (S : SimultaneousSplitting p model) (g : ZMod p.n) :
    Measurable (fun ω => S.X.Hm ω - embedPair p g (S.G g ω)) :=
  csm_measurable_res S.X (S.measurable_G g)

theorem pc_W_pos : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos

theorem pc_rpow_neg_half : (p.W : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt p.W := by
  rw [Real.rpow_neg pc_W_pos.le, ← Real.sqrt_eq_rpow, one_div]

/-- The divergence bound at a deterministic energy: `E D(E)² ≤ V n/W²` with
`V = 4A/s + 2BR + 2BT`, `A = c⁴`, `B = 4c⁴`, `R = 2/(1-ρ²)`, from the divergence isometry
and the moment bounds `‖j^{sm}‖₄ ≤ c/W`, `‖∂_{ξ_g} j^{sm}‖₄ ≤ c(ρ^{d(e,g)} + W^{-1/2})`. -/
theorem pc_divergence_le (hiso : PcDivergenceIsometry) (S : SimultaneousSplitting p model)
    (hS : S.IsExact) (φ : ZMod p.n → p.SiteMatrix → ℝ → ℝ)
    (hbdd : ∀ g H E, |φ g H E| ≤ 1)
    (hmeas : ∀ g, Measurable (fun x : p.SiteMatrix × ℝ => φ g x.1 x.2))
    (hsm : ∀ g (H₀ : p.SiteMatrix), H₀.IsHermitian → IsRingBanded p H₀ →
      ExteriorBondsInvertible p g H₀ →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : (ZMod p.n → ℝ) × ℝ => φ g (H₀ + ∑ h, (x.1 h : ℂ) • pairProjector p h) x.2))
    {c ρ T : ℝ} (hc : 0 ≤ c) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hnT : (p.n : ℝ) ≤ T * p.W)
    (hmom : ∀ (e g : ZMod p.n) (E : ℝ),
      eLpNorm (fun ω => φ e (S.X.Hm ω - embedPair p e (S.G e ω)) E) (ENNReal.ofReal 4) S.X.P ≤
          ENNReal.ofReal (c / p.W) ∧
        (g ≠ e → eLpNorm (fun ω => deriv (fun t : ℝ =>
            φ e (S.X.Hm ω - embedPair p e (S.G e ω) + (t : ℂ) • pairProjector p g) E) 0)
            (ENNReal.ofReal 4) S.X.P ≤
          ENNReal.ofReal (c * (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ))))))
    (E : ℝ) :
    Integrable (fun ω => (((2 * (p.W : ℝ)) ^ 2 / splitS p) *
        ∑ g, S.ξ g ω * φ g (S.X.Hm ω - embedPair p g (S.G g ω)) E ^ 2) ^ 2) S.X.P ∧
      (∫ ω, (((2 * (p.W : ℝ)) ^ 2 / splitS p) *
        ∑ g, S.ξ g ω * φ g (S.X.Hm ω - embedPair p g (S.G g ω)) E ^ 2) ^ 2 ∂S.X.P) ≤
      ((4 * c ^ 4 / splitS p + 2 * (4 * c ^ 4) * (2 / (1 - ρ ^ 2))) +
          2 * (4 * c ^ 4) * T) * p.n / (p.W : ℝ) ^ 2 := by
  have hP : IsProbabilityMeasure S.X.P := csm_isProb_ext S.X
  have hW := pc_W_pos (p := p)
  have hs : 0 < splitS p := ctr_splitS_pos
  set Ψ : ZMod p.n → p.SiteMatrix → ℝ := fun g H => φ g H E with hΨdef
  have hΨm : ∀ g, Measurable (Ψ g) := fun g =>
    (hmeas g).comp (measurable_id.prodMk measurable_const)
  have hΨsm : ∀ g (H₀ : p.SiteMatrix), H₀.IsHermitian → IsRingBanded p H₀ →
      ExteriorBondsInvertible p g H₀ →
      ContDiff ℝ 1 (fun x : ZMod p.n → ℝ => Ψ g (H₀ + ∑ h, (x h : ℂ) • pairProjector p h)) := by
    intro g H₀ h1 h2 h3
    have h := (hsm g H₀ h1 h2 h3).comp (contDiff_id.prodMk (contDiff_const (c := E)))
    exact h.of_le (by exact_mod_cast le_top)
  have hfin : ∀ g h, g ≠ h → eLpNorm (fun ω => deriv (fun t : ℝ =>
      Ψ g (S.X.Hm ω - embedPair p g (S.G g ω) + (t : ℂ) • pairProjector p h)) 0) 4 S.X.P < ⊤ := by
    intro g h hgh
    have := (hmom g h E).2 (Ne.symm hgh)
    rw [show ENNReal.ofReal 4 = 4 by norm_num] at this
    exact lt_of_le_of_lt this ENNReal.ofReal_lt_top
  obtain ⟨haesm, hDint, hident⟩ := hiso p model S hS Ψ hΨm (fun g H => hbdd g H E) hΨsm hfin
  refine ⟨hDint, ?_⟩
  -- the objects of the budget theorem
  set res : ZMod p.n → S.X.Ω → p.SiteMatrix := fun g ω => S.X.Hm ω - embedPair p g (S.G g ω)
    with hresdef
  set dΨ : ZMod p.n → ZMod p.n → S.X.Ω → ℝ := fun g h ω => deriv (fun t : ℝ =>
      Ψ g (res g ω + (t : ℂ) • pairProjector p h)) 0 with hdΨdef
  set f : ZMod p.n → S.X.Ω → ℝ := fun g ω => Ψ g (res g ω) ^ 2 with hfdef
  set df : ZMod p.n → ZMod p.n → S.X.Ω → ℝ := fun g h ω =>
    if h = g then 0 else 2 * Ψ g (res g ω) * dΨ g h ω with hdfdef
  have hresm : ∀ g, Measurable (res g) := fun g => pc_measurable_res S g
  have hΨres : ∀ g, Measurable (fun ω => Ψ g (res g ω)) := fun g => (hΨm g).comp (hresm g)
  have hdfm : ∀ g h, AEStronglyMeasurable (df g h) S.X.P := by
    intro g h
    by_cases hgh : h = g
    · rw [show df g h = fun _ => 0 from funext fun ω => ite_eq_left hgh]
      exact aestronglyMeasurable_const
    · rw [show df g h = fun ω => 2 * Ψ g (res g ω) * dΨ g h ω from funext fun ω => ite_eq_right hgh]
      exact ((measurable_const.mul (hΨres g)).aestronglyMeasurable).mul
        (haesm g h (Ne.symm hgh))
  -- moments of `Ψ` and of its derivative
  have hΨ4 : ∀ g, ∫⁻ ω, ‖Ψ g (res g ω)‖ₑ ^ 4 ∂S.X.P ≤ ENNReal.ofReal ((c / p.W) ^ 4) := by
    intro g
    have h := (hmom g g E).1
    exact pc_lintegral_pow_le_of_eLpNorm (hΨres g).aestronglyMeasurable (r := 4) (by norm_num)
      (by positivity) (by simpa using h)
  set a : ZMod p.n → ZMod p.n → ℝ := fun e g => ρ ^ edgeDistance p e g with hadef
  have hdΨ4 : ∀ g h, h ≠ g → ∫⁻ ω, ‖dΨ g h ω‖ₑ ^ 4 ∂S.X.P ≤
      ENNReal.ofReal ((c * (a g h + 1 / Real.sqrt p.W)) ^ 4) := by
    intro g h hgh
    have h1 := (hmom g h E).2 hgh
    rw [pc_rpow_neg_half] at h1
    exact pc_lintegral_pow_le_of_eLpNorm (haesm g h (Ne.symm hgh)) (r := 4) (by norm_num)
      (by positivity) (by simpa using h1)
  have hdf2 : ∀ g h, Integrable (fun ω => df g h ω ^ 2) S.X.P ∧
      (∫ ω, df g h ω ^ 2 ∂S.X.P) ≤ ((4 * c ^ 4) / (p.W : ℝ) ^ 2) * (a g h + 1 / Real.sqrt p.W) ^ 2 := by
    intro g h
    by_cases hgh : h = g
    · rw [show df g h = fun _ => 0 from funext fun ω => ite_eq_left hgh]
      refine ⟨by simp, ?_⟩
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
      positivity
    · have hmul := pc_lintegral_mul_sq_le (μ := S.X.P) (hΨres g).aemeasurable
        (haesm g h (Ne.symm hgh)).aemeasurable (hΨ4 g) (hdΨ4 g h hgh)
      have h2 : ∫⁻ ω, ‖df g h ω‖ₑ ^ 2 ∂S.X.P ≤
          ENNReal.ofReal ((2 * (c / p.W * (c * (a g h + 1 / Real.sqrt p.W)))) ^ 2) := by
        have heq : (fun ω => ‖df g h ω‖ₑ ^ 2) =
            fun ω => 4 * ‖Ψ g (res g ω) * dΨ g h ω‖ₑ ^ 2 := by
          funext ω
          rw [show df g h ω = 2 * Ψ g (res g ω) * dΨ g h ω from ite_eq_right hgh]
          rw [mul_assoc, enorm_mul, mul_pow]
          congr 1
          rw [Real.enorm_eq_ofReal (by norm_num), ← ENNReal.ofReal_pow (by norm_num)]
          norm_num
        rw [heq, lintegral_const_mul' _ _ (by norm_num)]
        calc 4 * ∫⁻ ω, ‖Ψ g (res g ω) * dΨ g h ω‖ₑ ^ 2 ∂S.X.P
            ≤ 4 * ENNReal.ofReal ((c / p.W * (c * (a g h + 1 / Real.sqrt p.W))) ^ 2) := by
              gcongr
          _ = _ := by
              rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
              congr 1; ring
      obtain ⟨hi, hb⟩ := pc_sq_integral_le (hdfm g h) h2
      refine ⟨hi, hb.trans (le_of_eq ?_)⟩
      rw [max_eq_left (by positivity)]
      field_simp
      ring
  have hrow : ∀ e, ∑ g, a e g ^ 2 ≤ 2 / (1 - ρ ^ 2) := fun e =>
    pc_geom_sum_le p.n e hρ0 hρ1
  have hf4 : ∀ e, (∫ ω, f e ω ^ 2 ∂S.X.P) ≤ c ^ 4 / (p.W : ℝ) ^ 4 := by
    intro e
    have h := pc_sq_integral_le (μ := S.X.P) (f := f e) ((hΨres e).pow_const 2).aestronglyMeasurable
      (V := (c / p.W) ^ 4) (by
        refine le_trans (le_of_eq ?_) (hΨ4 e)
        refine lintegral_congr fun ω => ?_
        simp only [hfdef, enorm_pow]; ring)
    refine h.2.trans (le_of_eq ?_)
    rw [max_eq_left (by positivity), div_pow]
  have hisom : (∫ ω, (((2 * (p.W : ℝ)) ^ 2 / splitS p) *
        ∑ g, S.ξ g ω * f g ω) ^ 2 ∂S.X.P) =
      ((2 * (p.W : ℝ)) ^ 2 / splitS p) * (∑ e, ∫ ω, f e ω ^ 2 ∂S.X.P) +
        ∑ e, ∑ g ∈ Finset.univ.erase e, ∫ ω, df e g ω * df g e ω ∂S.X.P := by
    rw [hident]
    congr 1
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun g hg => ?_
    have hge : g ≠ e := Finset.ne_of_mem_erase hg
    rw [show df e g = fun ω => 2 * Ψ e (res e ω) * dΨ e g ω from funext fun ω => ite_eq_right hge,
      show df g e = fun ω => 2 * Ψ g (res g ω) * dΨ g e ω from funext fun ω => ite_eq_right hge.symm]
  have hbudget := secondMoment_le_physical_budget_of_isometry S.X.P f df
    (fun ω => ((2 * (p.W : ℝ)) ^ 2 / splitS p) * ∑ g, S.ξ g ω * f g ω)
    hdfm (fun e g => (hdf2 e g).1) a (p.W : ℝ) (splitS p) (c ^ 4) (4 * c ^ 4)
    (2 / (1 - ρ ^ 2)) hW hs (by positivity) hrow hf4 (fun e g => (hdf2 e g).2) hisom
  have hcard : (Fintype.card (ZMod p.n) : ℝ) = p.n := by rw [ZMod.card]
  rw [hcard] at hbudget
  have hlin := physical_budget_le_linear_budget (n := (p.n : ℝ)) (W := (p.W : ℝ)) (T := T)
    (C := 4 * c ^ 4 / splitS p + 2 * (4 * c ^ 4) * (2 / (1 - ρ ^ 2))) (B := 4 * c ^ 4)
    (Nat.cast_nonneg _) hW (by positivity) hnT
  refine hbudget.trans (le_trans (le_of_eq ?_) hlin)
  ring

/-- The cyclic sum of the per-edge energy primitives:
`Σ_g E♯_{α,g} φ_g(H^{(g)}, Λ)² = (n/2) E ∫_{e₀}^{Λ} D(E) dE`, `D(E) = σ⁻² Σ_g ξ_g φ_g(H^{(g)}, E)²`. -/
theorem pc_energy_sum (henergy : PcEnergyPrimitive) (S : SimultaneousSplitting p model)
    (hS : S.IsExact) (α : Fin p.N) (φ : ZMod p.n → p.SiteMatrix → ℝ → ℝ)
    (hbdd : ∀ g H E, |φ g H E| ≤ 1)
    (hmeas : ∀ g, Measurable (fun x : p.SiteMatrix × ℝ => φ g x.1 x.2)) (e₀ : ℝ) :
    (∑ g, ∫ ω, φ g (S.X.Hm ω - embedPair p g (S.G g ω))
        (physicalOrderedEigenvalue p (S.X.Hm ω) α) ^ 2 ∂extendedPairMeasure p α g S.X.P S.X.Hm) =
      (p.n : ℝ) / 2 * ∫ ω, (∫ E in e₀..physicalOrderedEigenvalue p (S.X.Hm ω) α,
        ((2 * (p.W : ℝ)) ^ 2 / splitS p) *
          ∑ g, S.ξ g ω * φ g (S.X.Hm ω - embedPair p g (S.G g ω)) E ^ 2) ∂S.X.P := by
  set σi : ℝ := (2 * (p.W : ℝ)) ^ 2 / splitS p with hσi
  have hΨm : ∀ g, Measurable (fun x : p.SiteMatrix × ℝ => φ g x.1 x.2 ^ 2) :=
    fun g => (hmeas g).pow_const 2
  have hΨb : ∀ g H E, |φ g H E ^ 2| ≤ 1 := fun g H E => by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hbdd g H E)
  have hE := fun g => henergy p model S hS α g (fun H E => φ g H E ^ 2) (hΨm g) (hΨb g) e₀
  -- the interval integral of the sum
  have hinner : ∀ ω, (∫ E in e₀..physicalOrderedEigenvalue p (S.X.Hm ω) α, σi *
      ∑ g, S.ξ g ω * φ g (S.X.Hm ω - embedPair p g (S.G g ω)) E ^ 2) =
      σi * ∑ g, S.ξ g ω * ∫ E in e₀..physicalOrderedEigenvalue p (S.X.Hm ω) α,
        φ g (S.X.Hm ω - embedPair p g (S.G g ω)) E ^ 2 := by
    intro ω
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
    · congr 1
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [intervalIntegral.integral_const_mul]
    · intro g _
      have hm : Measurable fun E => S.ξ g ω * φ g (S.X.Hm ω - embedPair p g (S.G g ω)) E ^ 2 :=
        measurable_const.mul ((hΨm g).comp (measurable_const.prodMk measurable_id))
      refine (intervalIntegrable_const (c := |S.ξ g ω|)).mono_fun' hm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun E => ?_)
      dsimp only
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hΨb g _ _)
  simp_rw [hinner]
  rw [integral_const_mul, integral_finsetSum _ fun g _ => (hE g).1, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [(hE g).2]
  ring

/-- Replacement on one extension carrying the edge splitting, whose center is the Dyson center. -/
theorem pc_replace_aux (α : Fin p.N) (g : ZMod p.n) (φg : p.SiteMatrix → ℝ → ℝ)
    (hmeas : Measurable (fun x : p.SiteMatrix × ℝ => φg x.1 x.2)) (hbdd : ∀ H E, |φg H E| ≤ 1)
    (δ : ℝ) (X : PairExtension p model) (G : X.Ω → PairMatrix p g) (hG : IsCenterSplitting X G)
    (hrepl : extendedPairMeasure p α g X.P X.Hm
          {ω | φg (X.Hm ω - embedPair p g (G ω)) (physicalOrderedEigenvalue p (X.Hm ω) α) ≠
            dysonCenter p g cst0 α (X.Hm ω - embedPair p g (G ω))
              (physicalOrderedEigenvalue p (X.Hm ω) α)} ≤ ENNReal.ofReal δ)
    (c : X.Ω → ℝ) (hc : ∀ ω, c ω = dysonCenter p g cst0 α (X.Hm ω - embedPair p g (G ω))
      (physicalOrderedEigenvalue p (X.Hm ω) α))
    (S : SimultaneousSplitting p model) (hS : S.IsExact) :
    (∫ ω, c ω ^ 2 ∂extendedPairMeasure p α g X.P X.Hm) ≤
      (∫ ω, φg (S.X.Hm ω - embedPair p g (S.G g ω))
          (physicalOrderedEigenvalue p (S.X.Hm ω) α) ^ 2 ∂extendedPairMeasure p α g S.X.P S.X.Hm) +
        max δ 0 := by
  have hprob : IsProbabilityMeasure (extendedPairMeasure p α g X.P X.Hm) :=
    extendedPairMeasure_isProbability p model α g X
  set F : p.SiteMatrix × p.SiteMatrix → ℝ := fun x => φg x.1 (physicalOrderedEigenvalue p x.2 α) ^ 2
    with hFdef
  have hF : Measurable F :=
    (hmeas.comp (measurable_fst.prodMk
      ((measurable_physicalOrderedEigenvalue p α).comp measurable_snd))).pow_const 2
  have htr1 := pc_pair_integral_transfer α g X hG F hF
  have htr2 := pc_pair_integral_transfer α g S.X (pc_isCenterSplitting_of_exact S hS g) F hF
  set bad : Set X.Ω := {ω | φg (X.Hm ω - embedPair p g (G ω)) (physicalOrderedEigenvalue p (X.Hm ω) α) ≠
      dysonCenter p g cst0 α (X.Hm ω - embedPair p g (G ω))
        (physicalOrderedEigenvalue p (X.Hm ω) α)} with hbad
  set B : Set X.Ω := toMeasurable (extendedPairMeasure p α g X.P X.Hm) bad with hB
  have hBm : MeasurableSet B := measurableSet_toMeasurable _ _
  have hres : Measurable (fun ω => X.Hm ω - embedPair p g (G ω)) := csm_measurable_res X hG.1
  have hφm : Measurable (fun ω => F (X.Hm ω - embedPair p g (G ω), X.Hm ω)) :=
    hF.comp (hres.prodMk X.measurable_Hm)
  have hint1 : Integrable (fun ω => F (X.Hm ω - embedPair p g (G ω), X.Hm ω))
      (extendedPairMeasure p α g X.P X.Hm) := by
    refine Integrable.of_bound hφm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, hFdef, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (hbdd _ _)
  have hint2 : Integrable (B.indicator (1 : X.Ω → ℝ)) (extendedPairMeasure p α g X.P X.Hm) :=
    (integrable_const (1 : ℝ)).indicator hBm
  have hpt : ∀ ω, c ω ^ 2 ≤ F (X.Hm ω - embedPair p g (G ω), X.Hm ω) + B.indicator 1 ω := by
    intro ω
    rw [hc ω, hFdef]
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω, Pi.one_apply]
      have h1 := ctr_abs_dysonCenter_le (i := g) cst0 α (X.Hm ω - embedPair p g (G ω))
        (physicalOrderedEigenvalue p (X.Hm ω) α)
      have h2 : dysonCenter p g cst0 α (X.Hm ω - embedPair p g (G ω))
          (physicalOrderedEigenvalue p (X.Hm ω) α) ^ 2 ≤ 1 := by
        rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) h1
      dsimp only
      nlinarith [sq_nonneg (φg (X.Hm ω - embedPair p g (G ω)) (physicalOrderedEigenvalue p (X.Hm ω) α))]
    · rw [Set.indicator_of_notMem hω, add_zero]
      have hnb : ω ∉ bad := fun h => hω (subset_toMeasurable _ bad h)
      simp only [hbad, Set.mem_ofPred_eq, not_not] at hnb
      dsimp only
      rw [hnb]
  calc (∫ ω, c ω ^ 2 ∂extendedPairMeasure p α g X.P X.Hm)
      ≤ ∫ ω, (F (X.Hm ω - embedPair p g (G ω), X.Hm ω) + B.indicator 1 ω)
          ∂extendedPairMeasure p α g X.P X.Hm :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
          (hint1.add hint2) (Filter.Eventually.of_forall hpt)
    _ = (∫ ω, F (X.Hm ω - embedPair p g (G ω), X.Hm ω) ∂extendedPairMeasure p α g X.P X.Hm) +
          (extendedPairMeasure p α g X.P X.Hm bad).toReal := by
        rw [integral_add hint1 hint2, integral_indicator_one hBm, measureReal_def, hB,
          measure_toMeasurable]
    _ ≤ _ := by
        rw [htr1, ← htr2]
        gcongr
        calc (extendedPairMeasure p α g X.P X.Hm bad).toReal ≤ (ENNReal.ofReal δ).toReal :=
              ENNReal.toReal_mono ENNReal.ofReal_ne_top hrepl
          _ = max δ 0 := ENNReal.toReal_ofReal'

/-- **Replacement of `j_e` by `j_e^{sm}`** under the pair law (`SmoothCenterContract`,
replacement field) and transport of the pair law from the witness extension of
`pairCenterFamily0` to an exact simultaneous splitting `S`:
`E♯ j_g(λ_α)² ≤ E♯_S φ_g(H^{(g)}, Λ)² + max δ 0`. -/
theorem pc_replace_le (α : Fin p.N) (g : ZMod p.n) (φg : p.SiteMatrix → ℝ → ℝ)
    (hmeas : Measurable (fun x : p.SiteMatrix × ℝ => φg x.1 x.2)) (hbdd : ∀ H E, |φg H E| ≤ 1)
    (δ : ℝ)
    (hrepl : ∀ (X : PairExtension p model) (G : X.Ω → PairMatrix p g), IsCenterSplitting X G →
      extendedPairMeasure p α g X.P X.Hm
          {ω | φg (X.Hm ω - embedPair p g (G ω)) (physicalOrderedEigenvalue p (X.Hm ω) α) ≠
            dysonCenter p g cst0 α (X.Hm ω - embedPair p g (G ω))
              (physicalOrderedEigenvalue p (X.Hm ω) α)} ≤ ENNReal.ofReal δ)
    (S : SimultaneousSplitting p model) (hS : S.IsExact) :
    (∫ ω, (pairCenterFamily0 p model α g).center ω ^ 2 ∂extendedPairMeasure p α g
        (pairCenterFamily0 p model α g).X.P (pairCenterFamily0 p model α g).X.Hm) ≤
      (∫ ω, φg (S.X.Hm ω - embedPair p g (S.G g ω))
          (physicalOrderedEigenvalue p (S.X.Hm ω) α) ^ 2 ∂extendedPairMeasure p α g S.X.P S.X.Hm) +
        max δ 0 := by
  obtain ⟨G, hG, hcenter⟩ := pairCenterFamily0_isDyson p model α g
  exact pc_replace_aux α g φg hmeas hbdd δ _ G hG (hrepl _ G hG) _ hcenter S hS

end Estimates

/-!
## 3. Final algebra
-/

theorem pc_final_algebra {n W cl cd V T' : ℝ} (hn : 0 < n) (hW : 0 < W) (hcl : 0 ≤ cl)
    (hcd : 0 ≤ cd) (hV : 0 ≤ V) (hT : 0 ≤ T') (hnT : n ≤ T' * W) :
    Real.pi * ((cl + 1) / (n * Real.sqrt W)) * (Real.sqrt (V * n) / W) + cd / W ^ 2 ≤
      (Real.pi * (cl + 1) * Real.sqrt V + cd * Real.sqrt T') /
        (Real.sqrt n * (W * Real.sqrt W)) := by
  set a := Real.sqrt n with ha
  set w := Real.sqrt W with hw
  have ha0 : 0 < a := Real.sqrt_pos.mpr hn
  have hw0 : 0 < w := Real.sqrt_pos.mpr hW
  have hn' : n = a ^ 2 := (Real.sq_sqrt hn.le).symm
  have hW' : W = w ^ 2 := (Real.sq_sqrt hW.le).symm
  have hVn : Real.sqrt (V * n) = Real.sqrt V * a := Real.sqrt_mul hV n
  have haw : a ≤ Real.sqrt T' * w := by
    rw [ha, hw, ← Real.sqrt_mul hT]; exact Real.sqrt_le_sqrt hnT
  rw [hVn, hn', hW']
  rw [show Real.pi * ((cl + 1) / (a ^ 2 * w)) * (Real.sqrt V * a / w ^ 2) =
      Real.pi * (cl + 1) * Real.sqrt V / (a * (w ^ 2 * w)) by field_simp]
  rw [add_div]
  refine add_le_add le_rfl ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsT : 0 ≤ Real.sqrt T' := Real.sqrt_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left haw (show 0 ≤ cd * w ^ 3 by positivity)]

theorem pc_bulk_mono {p : Parameters} {θ ϑ : ℝ} (h : ϑ ≤ θ) {α : Fin p.N}
    (hα : IsBulkRank p θ α) : IsBulkRank p ϑ α :=
  ⟨h.trans hα.1, hα.2.trans (by linarith)⟩

/-!
## 4. The physical center theorem
-/

/-- **The physical center bound**.

*Law.* The exact pair law (`extendedPairMeasure`, density
`(n/2)(p_{αi} + p_{α,i+1})`) on the witness extension of `pairCenterFamily0`
(`SplitState × PairMatrix`, `P = Pω ⊗ GUE_{2W}(s/(2W))`, `s = min(c, b)`), whose center is the
Dyson center `j_i(λ_α)` built from `H - G_i`, extended by zero off the
regular domain of `cst0` (`pairCenterFamily0_isDyson`).
*Domain.* `0 < b < 1/2`, `θ > 0` (for `θ ≥ 1/2` the bulk condition is used through
`ϑ = min(θ, 1/4)`; `θ ≤ 0` would include edge ranks and is not claimed), `T` arbitrary.
*Norms.* Real second moment of the center under the pair law.
*Quantifier order / uniformity.* `b, θ, T` first; then `B` (from the constants `C₄` of
the smooth center bounds at `q = 4`, `C₂` of the replacement field at `D = 2`, the rank-location
constant at `q = 4`, `ρ` and `s(b)`), then `n, W`, the model, `α`, `i`. -/
theorem physicalCenter_holds_of (hrank : RankLocationContract)
    (hsmooth : SmoothCenterContract cst0) (hsplit : PcSplittingExists)
    (henergy : PcEnergyPrimitive) (hiso : PcDivergenceIsometry) (hcyc : PcCenterCyclic) :
    ∀ (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), 0 < θ →
      PhysicalCenterContract b θ T hb hb' pairCenterFamily0 := by
  intro b θ T hb hb' hθ
  set ϑ : ℝ := min θ (1 / 4) with hϑdef
  have hϑ0 : 0 < ϑ := lt_min hθ (by norm_num)
  have hϑ1 : ϑ < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨ρ, κ', hρ0, hρ1, _hκ', Φ, hbdd, hmeas, hsm, _hsupp, _hagree, hmom, hrepl⟩ :=
    hsmooth b hb hb' ϑ T hϑ0 hϑ1
  obtain ⟨C4, hC4⟩ := hmom 4 (by norm_num)
  obtain ⟨CD, hCD⟩ := hrepl 2
  obtain ⟨CL, hCL⟩ := hrank.location b hb hb' T ϑ hϑ0 hϑ1 4 (by norm_num)
  set c4 : ℝ := max C4 0 with hc4
  set cd : ℝ := max CD 0 with hcd
  set cl : ℝ := max CL 0 with hcl
  set T' : ℝ := max T 0 with hT'
  set V : ℝ := (4 * c4 ^ 4 / min (1 - 2 * b) b + 2 * (4 * c4 ^ 4) * (2 / (1 - ρ ^ 2))) +
    2 * (4 * c4 ^ 4) * T' with hVdef
  have hc40 : 0 ≤ c4 := le_max_right _ _
  have hcd0 : 0 ≤ cd := le_max_right _ _
  have hcl0 : 0 ≤ cl := le_max_right _ _
  have hT'0 : 0 ≤ T' := le_max_right _ _
  have hsb : 0 < min (1 - 2 * b) b := lt_min (by linarith) hb
  have hρ2 : 0 < 1 - ρ ^ 2 := by nlinarith
  have hV0 : 0 ≤ V := by positivity
  refine ⟨Real.pi * (cl + 1) * Real.sqrt V + cd * Real.sqrt T', 0, by positivity, ?_⟩
  intro n W hn hW hnT _hW0 p model α hα i
  have hpb : p.b = b := rfl
  have hsplitS : splitS p = min (1 - 2 * b) b := rfl
  have hnTp : (p.n : ℝ) ≤ T * p.W := hnT
  clear_value p
  have hαϑ : IsBulkRank p ϑ α := pc_bulk_mono (min_le_left _ _) hα
  obtain ⟨S, hS⟩ := hsplit p model
  have hP : IsProbabilityMeasure S.X.P := csm_isProb_ext S.X
  have hWpos : (0 : ℝ) < p.W := pc_W_pos
  have hnpos : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  have hnT' : (p.n : ℝ) ≤ T' * p.W :=
    hnTp.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hWpos.le)
  set φ : ZMod p.n → p.SiteMatrix → ℝ → ℝ := Φ p α with hφdef
  -- moment data with nonnegative constants
  have hmom' : ∀ (e g : ZMod p.n) (E : ℝ),
      eLpNorm (fun ω => φ e (S.X.Hm ω - embedPair p e (S.G e ω)) E) (ENNReal.ofReal 4) S.X.P ≤
          ENNReal.ofReal (c4 / p.W) ∧
        (g ≠ e → eLpNorm (fun ω => deriv (fun t : ℝ =>
            φ e (S.X.Hm ω - embedPair p e (S.G e ω) + (t : ℂ) • pairProjector p g) E) 0)
            (ENNReal.ofReal 4) S.X.P ≤
          ENNReal.ofReal (c4 * (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ))))) := by
    intro e g E
    obtain ⟨h1, h2⟩ := hC4 p hpb hnTp model S hS α hαϑ e g E
    refine ⟨h1.trans (ENNReal.ofReal_le_ofReal ?_), fun hge => (h2 hge).trans
      (ENNReal.ofReal_le_ofReal ?_)⟩
    · exact div_le_div_of_nonneg_right (le_max_left _ _) hWpos.le
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  -- the divergence bound
  have hdiv : ∀ E : ℝ, Integrable (fun ω => (((2 * (p.W : ℝ)) ^ 2 / splitS p) *
        ∑ g, S.ξ g ω * φ g (S.X.Hm ω - embedPair p g (S.G g ω)) E ^ 2) ^ 2) S.X.P ∧
      (∫ ω, (((2 * (p.W : ℝ)) ^ 2 / splitS p) *
        ∑ g, S.ξ g ω * φ g (S.X.Hm ω - embedPair p g (S.G g ω)) E ^ 2) ^ 2 ∂S.X.P) ≤
        V * p.n / (p.W : ℝ) ^ 2 := by
    intro E
    have h := pc_divergence_le hiso S hS φ (hbdd p α) (hmeas p α) (hsm p α) hc40 hρ0 hρ1 hnT'
      hmom' E
    rw [hsplitS] at h
    rw [hsplitS]
    exact h
  -- the random-energy bound
  set σi : ℝ := (2 * (p.W : ℝ)) ^ 2 / splitS p with hσi
  set D : S.X.Ω × ℝ → ℝ := fun z =>
    σi * ∑ g, S.ξ g z.1 * φ g (S.X.Hm z.1 - embedPair p g (S.G g z.1)) z.2 ^ 2 with hDdef
  have hDm : Measurable D := by
    refine measurable_const.mul (Finset.measurable_sum _ fun g _ => ?_)
    refine ((S.measurable_ξ g).comp measurable_fst).mul ?_
    exact ((hmeas p α g).comp (((pc_measurable_res S g).comp measurable_fst).prodMk
      measurable_snd)).pow_const 2
  set e₀ : ℝ := classicalLocation p α with he₀
  set Λ : S.X.Ω → ℝ := fun ω => physicalOrderedEigenvalue p (S.X.Hm ω) α with hΛdef
  have hΛm : Measurable Λ := (measurable_physicalOrderedEigenvalue p α).comp S.X.measurable_Hm
  set M : ℝ := (cl + 1) / (p.n * Real.sqrt p.W) with hMdef
  have hM : 0 < M := by positivity
  set K : ℝ := Real.sqrt (V * p.n) / p.W with hKdef
  have hK : 0 ≤ K := by positivity
  have hterm : ∫⁻ x, ‖Λ x - e₀‖ₑ ^ 4 ∂S.X.P ≤ ENNReal.ofReal (M ^ 4) := by
    have hloc := hCL p hpb hnTp model MassLaw.physical α hαϑ
    have hmeasH : Measurable (fun H : p.SiteMatrix => physicalOrderedEigenvalue p H α - e₀) :=
      (measurable_physicalOrderedEigenvalue p α).sub measurable_const
    have heq : eLpNorm (fun x => Λ x - e₀) (ENNReal.ofReal 4) S.X.P =
        eLpNorm (fun H : p.SiteMatrix => physicalOrderedEigenvalue p H α - e₀) (ENNReal.ofReal 4)
          (model.law : Measure p.SiteMatrix) := by
      rw [← S.X.map_eq, eLpNorm_map_measure (by rw [S.X.map_eq]; exact hmeasH.aestronglyMeasurable)
        S.X.measurable_Hm.aemeasurable]
      rfl
    have hbound : eLpNorm (fun x => Λ x - e₀) (ENNReal.ofReal ((4 : ℕ) : ℝ)) S.X.P ≤
        ENNReal.ofReal M := by
      rw [show ((4 : ℕ) : ℝ) = 4 by norm_num, heq]
      refine hloc.trans (ENNReal.ofReal_le_ofReal ?_)
      exact div_le_div_of_nonneg_right ((le_max_left _ _).trans (by linarith)) (by positivity)
    exact pc_lintegral_pow_le_of_eLpNorm (hΛm.sub measurable_const).aestronglyMeasurable
      (by norm_num) hM.le hbound
  have hDk : ∀ E, ∫⁻ x, ‖D (x, E)‖ₑ ^ 2 ∂S.X.P ≤ ENNReal.ofReal (K ^ 2) := by
    intro E
    obtain ⟨hi, hb2⟩ := hdiv E
    refine pc_lintegral_sq_le_of_integral (f := fun x => D (x, E)) hi (hb2.trans (le_of_eq ?_))
    rw [hKdef, div_pow, Real.sq_sqrt (by positivity)]
  have hre := pc_terminal_energy_le S.X.P D hDm Λ hΛm e₀ M K hM hK hterm hDk
  -- the cyclic sum, the energy primitive and replacement
  have hsum := pc_energy_sum henergy S hS α φ (hbdd p α) (hmeas p α) e₀
  set LHS : ZMod p.n → ℝ := fun g => ∫ ω, (pairCenterFamily0 p model α g).center ω ^ 2
    ∂extendedPairMeasure p α g (pairCenterFamily0 p model α g).X.P
      (pairCenterFamily0 p model α g).X.Hm with hLHS
  have hrep : ∀ g, LHS g ≤ (∫ ω, φ g (S.X.Hm ω - embedPair p g (S.G g ω))
      (physicalOrderedEigenvalue p (S.X.Hm ω) α) ^ 2 ∂extendedPairMeasure p α g S.X.P S.X.Hm) +
        cd / (p.W : ℝ) ^ 2 := by
    intro g
    refine (pc_replace_le α g (φ g) (hmeas p α g) (hbdd p α g) (CD * (p.W : ℝ) ^ (-(2 : ℝ)))
      (fun X G hG => hCD p hpb hnTp model α hαϑ g X G hG) S hS).trans ?_
    gcongr
    rw [Real.rpow_neg hWpos.le, Real.rpow_two, ← div_eq_mul_inv]
    exact max_le (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
  have hcycl : ∀ g, LHS g = LHS i := fun g => hcyc p model α g i
  have hnL : (p.n : ℝ) * LHS i ≤ (p.n : ℝ) / 2 * |∫ x, (∫ E in e₀..Λ x, D (x, E)) ∂S.X.P| +
      (p.n : ℝ) * (cd / (p.W : ℝ) ^ 2) := by
    have h1 : (p.n : ℝ) * LHS i = ∑ g, LHS g := by
      rw [Finset.sum_congr rfl fun g _ => hcycl g, Finset.sum_const, Finset.card_univ, ZMod.card,
        nsmul_eq_mul]
    rw [h1]
    calc ∑ g, LHS g ≤ ∑ g, ((∫ ω, φ g (S.X.Hm ω - embedPair p g (S.G g ω))
          (physicalOrderedEigenvalue p (S.X.Hm ω) α) ^ 2 ∂extendedPairMeasure p α g S.X.P S.X.Hm) +
            cd / (p.W : ℝ) ^ 2) := Finset.sum_le_sum fun g _ => hrep g
      _ = (p.n : ℝ) / 2 * (∫ x, (∫ E in e₀..Λ x, D (x, E)) ∂S.X.P) +
            (p.n : ℝ) * (cd / (p.W : ℝ) ^ 2) := by
          rw [Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ, ZMod.card,
            nsmul_eq_mul]
      _ ≤ _ := by
          gcongr
          exact le_abs_self _
  have hfinal : LHS i ≤ Real.pi * M * K + cd / (p.W : ℝ) ^ 2 := by
    have h2 : (p.n : ℝ) * LHS i ≤ (p.n : ℝ) * (Real.pi * M * K + cd / (p.W : ℝ) ^ 2) := by
      refine hnL.trans ?_
      have := mul_le_mul_of_nonneg_left hre (show (0 : ℝ) ≤ p.n / 2 by positivity)
      nlinarith
    exact le_of_mul_le_mul_left h2 hnpos
  refine hfinal.trans ?_
  have halg := pc_final_algebra (n := (p.n : ℝ)) (W := (p.W : ℝ)) (cl := cl) (cd := cd) (V := V)
    (T' := T') hnpos hWpos hcl0 hcd0 hV0 hT'0 hnT'
  refine le_trans (le_of_eq ?_) halg
  rw [hMdef, hKdef]

end BlockBand.Center
