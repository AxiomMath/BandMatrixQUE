module

public import BlockBand.Endpoints.Sine.CrossingSineAlgebra
public import BlockBand.Endpoints.Sine.CrossingSineSandwich
public import BlockBand.Internal.Contracts.ClocksCommonPort
public import BlockBand.Endpoints.Response.EdgeClockMoments
public import BlockBand.Model.Construction.GaussianSimpleSpectrum
public import BlockBand.Asymptotics.CriticalSequence

/-!
# The crossing process of the scalar pair flow has a sine limit

Statement (`crossingSine`). Law: the exact physical ring law `model.law` (every
`GaussianRingModel`) along a critical sequence (`CriticalSequence τ`, `n_j/W_j → τ`,
`W_j → ∞`, every fixed ratio `τ`), fixed `0 < b < 1/2`, deterministic bulk energy
`-2 < E < 2`, `ρ = ρ(E)`, `𝒩 = 2W`, any adjacent pair `S_j = {i_j, i_j + 1}`. The crossing
process `𝒞_W = Σ_j δ_{t_j}` of `H(t) = H + t/(𝒩ρ) P_S` (real `t_j` with `E ∈ Spec H(t_j)`,
with multiplicity; `crossingSum`) converges to the unit-intensity sine process: for every
nonnegative `f ∈ C_c(ℝ)`, `E exp(-Σ_j f(t_j)) → L_sine(f)` (`sineLaplaceFunctional`, the Laplace
functional that characterizes `IsSineLaw`). The expectation is a lower Lebesgue integral in
`ℝ≥0∞` (`crossingLaplace`), so no measurability of the crossing statistic is presupposed.

Proof. Conditional on the exterior `ω`, `Σ_j f(t_j) = Σ_k f(-𝒩ρ μ_k)` with `μ_k` the
eigenvalues of `G + K(E)` (`crossingSum_eq`, `pairSchur_assemble`); this is the unfolded
spectrum at energy `0` of the deformed GUE `K(E) + G` reflected (`reflectTest`,
`sineLaplaceFunctional_reflect`). On the regular event the external sine theorem (`ExternalSine`)
applies uniformly; its unfolding uses the deformed density `ρ_W(0)`, which tends to `ρ`, and the
dilation is absorbed by the sandwich `exists_dilation_sandwich`. The exceptional event costs at
most its outer probability since the Laplace functional lies in `[0, 1]`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Filter Topology
open BlockBand.External
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

/-!
## The GUE law bridge
-/

/-- **The two `GUE_d(t)` encodings agree.** `gueMeasure ι t` (`√(t/2)(X + X*)`, standard
circular `X`, the fresh pair Gaussian of the pair splitting), reindexed to `Fin N`, is
`gueMatrixLaw N t` (independent Johansson coordinates of total entry variance `t`, the law of the
external sine theorem). Both have real diagonal `N(0,t)` and independent off-diagonal
real/imaginary parts `N(0,t/2)`. Proved without hypotheses as `guelawBridge_holds`
(characteristic functions on the upper coordinates); `crossingSine_of_contracts` is
`crossingSine` with this input discharged.
-/
def GUELawBridge : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (e : ι ≃ Fin N) (t : ℝ≥0),
    (gueMeasure ι t).map (Matrix.reindex e e) = gueMatrixLaw N t

/-- The pair residual `K(E)` of the split state, reindexed to `Fin 𝒩'`,
`𝒩' = card PairSite` (`= 2W`, `card_pairSite`). -/
def pairResidualFin (p : Parameters) (i : ZMod p.n) (ω : SplitState p i) (E : ℝ) :
    Matrix (Fin (Fintype.card (PairSite p i))) (Fin (Fintype.card (PairSite p i))) ℂ :=
  Matrix.reindex (Fintype.equivFin (PairSite p i)) (Fintype.equivFin (PairSite p i))
    (pairResidual p i ω E)

/-- `E exp(-Σ_j f(t_j))` of the crossing process under the exact physical law (lower
integral). -/
def crossingLaplace (p : Parameters) (model : p.GaussianRingModel) (i : ZMod p.n) (E : ℝ)
    (f : CompactlySupportedContinuousMap ℝ ℝ) : ℝ≥0∞ :=
  ∫⁻ H, ENNReal.ofReal (Real.exp (-crossingSum p i f H E)) ∂(model.law : Measure p.SiteMatrix)

/-!
## Hermitian part and measurability
-/

/-- The Hermitian part `(M + M*)/2`. -/
def hermPart {n : Type*} (M : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℂ) • (M + Mᴴ)

theorem hermPart_isHermitian {n : Type*} (M : Matrix n n ℂ) : (hermPart M).IsHermitian := by
  unfold hermPart IsHermitian
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  congr 1
  simp

theorem hermPart_of_isHermitian {n : Type*} {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    hermPart M = M := by
  unfold hermPart; rw [hM.eq, ← two_smul ℂ M, smul_smul]; norm_num

theorem continuous_hermPart {n : Type*} : Continuous (hermPart : Matrix n n ℂ → Matrix n n ℂ) := by
  unfold hermPart
  exact (continuous_const (y := (1 / 2 : ℂ))).smul (continuous_id.add
    (continuous_id.matrix_conjTranspose : Continuous fun M : Matrix n n ℂ => Mᴴ))

theorem orderedEigenvalue_congr {N : ℕ} {X Y : Matrix (Fin N) (Fin N) ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) (h : X = Y) (k : Fin (Fintype.card (Fin N))) :
    BlockBand.Model.Construction.orderedEigenvalue ⟨X, hX⟩ k =
      BlockBand.Model.Construction.orderedEigenvalue ⟨Y, hY⟩ k := by
  subst h; rfl

theorem measurable_entry_matrixC {n m X : Type*} [MeasurableSpace X] {A : X → Matrix n m ℂ}
    (hA : Measurable A) (a : n) (k : m) : Measurable fun x => A x a k :=
  (measurable_pi_apply k).comp ((measurable_pi_apply a).comp hA)

theorem measurable_mul_matrixC {n m l X : Type*} [Fintype m] [MeasurableSpace X]
    {A : X → Matrix l m ℂ} {B : X → Matrix m n ℂ} (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x => A x * B x := by
  refine Measurable.of_eval fun a => Measurable.of_eval fun b => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_entry_matrixC hA a k).mul (measurable_entry_matrixC hB k b)

theorem measurable_inv_matrixC {n : Type*} [Fintype n] [DecidableEq n] :
    Measurable fun M : Matrix n n ℂ => M⁻¹ := by
  have : (fun M : Matrix n n ℂ => M⁻¹) = fun M => (M.det)⁻¹ • M.adjugate := by
    funext M; rw [inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact ((continuous_id.matrix_det).measurable.inv).smul (continuous_id.matrix_adjugate).measurable

section Pair

variable (p : Parameters) (i : ZMod p.n)

theorem continuous_exteriorBlock :
    Continuous fun H : p.SiteMatrix => exteriorBlock p i H :=
  continuous_pi fun a => continuous_pi fun b => (continuous_apply b.1).comp (continuous_apply a.1)

theorem measurable_pairSchur (E : ℝ) : Measurable fun H : p.SiteMatrix => pairSchur p i H E := by
  have h1 : Continuous fun H : p.SiteMatrix => pairBlock p i H :=
    continuous_pi fun a => continuous_pi fun b => (continuous_apply b.1).comp (continuous_apply a.1)
  have h2 : Continuous fun H : p.SiteMatrix => pairExteriorBlock p i H :=
    continuous_pi fun a => continuous_pi fun b => (continuous_apply b.1).comp (continuous_apply a.1)
  have h3 : Continuous fun H : p.SiteMatrix => couplingBlock p i H :=
    continuous_pi fun a => continuous_pi fun b => (continuous_apply b.1).comp (continuous_apply a.1)
  have h4 : Measurable fun H : p.SiteMatrix => (exteriorBlock p i H - (E : ℂ) • 1)⁻¹ :=
    measurable_inv_matrixC.comp ((continuous_exteriorBlock p i).sub continuous_const).measurable
  unfold pairSchur
  exact (h1.measurable.sub measurable_const).sub
    (measurable_mul_matrixC (measurable_mul_matrixC h2.measurable h4) h3.measurable)

theorem measurable_assemble :
    Measurable fun x : SplitState p i × PairMatrix p i => assemble p i x.1 x.2 := by
  have hV : Measurable fun x : SplitState p i × PairMatrix p i => x.1.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hC : Measurable fun x : SplitState p i × PairMatrix p i => x.1.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hR : Measurable fun x : SplitState p i × PairMatrix p i => x.1.1 :=
    measurable_fst.comp measurable_fst
  have hG : Measurable fun x : SplitState p i × PairMatrix p i => x.2 := measurable_snd
  refine Measurable.of_eval fun a => Measurable.of_eval fun b => ?_
  unfold assemble
  split_ifs
  · exact (measurable_entry_matrixC hV _ _).add (measurable_entry_matrixC hG _ _)
  · exact Complex.continuous_conj.measurable.comp (measurable_entry_matrixC hC _ _)
  · exact measurable_entry_matrixC hC _ _
  · exact measurable_entry_matrixC hR _ _

theorem card_pairSite : Fintype.card (PairSite p i) = 2 * p.W := by
  classical
  have hne : i ≠ i + 1 := by
    intro h
    have h1 : ((1 : ℕ) : ZMod p.n) = 0 := by
      have := congrArg (fun x => x - i) h
      simp only [sub_self, add_sub_cancel_left] at this
      exact_mod_cast this.symm
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := Nat.le_of_dvd one_pos h1
    have := p.n_ge_four
    omega
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun x : p.Site => x.1 = i ∨ x.1 = i + 1) =
      ({i, i + 1} : Finset (ZMod p.n)) ×ˢ (Finset.univ : Finset (Fin p.W)) := by
    ext x; simp
  rw [this, Finset.card_product, Finset.card_pair hne, Finset.card_univ, Fintype.card_fin]

/-- `exp(-Σ_k f(-𝒩ρ μ_k))`, `μ_k` the ordered eigenvalues of the Hermitian part of `M`. -/
def schurProxy (E : ℝ) (f : CompactlySupportedContinuousMap ℝ ℝ)
    (M : Matrix (Fin (Fintype.card (PairSite p i))) (Fin (Fintype.card (PairSite p i))) ℂ) :
    ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-∑ k : Fin (Fintype.card (Fin (Fintype.card (PairSite p i)))),
    reflectTest f (crossingScale p E * BlockBand.Model.Construction.orderedEigenvalue
      ⟨hermPart M, hermPart_isHermitian _⟩ k)))

theorem measurable_schurProxy (E : ℝ) (f : CompactlySupportedContinuousMap ℝ ℝ) :
    Measurable (schurProxy p i E f) := by
  unfold schurProxy
  have hB : Measurable fun M : Matrix (Fin (Fintype.card (PairSite p i)))
      (Fin (Fintype.card (PairSite p i))) ℂ =>
      (⟨hermPart M, hermPart_isHermitian _⟩ :
        BlockBand.Model.Construction.HermitianMatrix (Fin (Fintype.card (PairSite p i)))) :=
    Measurable.subtype_mk continuous_hermPart.measurable
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.neg ?_))
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (reflectTest f).continuous.measurable.comp (measurable_const.mul
    ((BlockBand.Model.Construction.measurable_orderedEigenvalue k).comp hB))

theorem measurable_reindex_matrixC {m l : Type*} (e : m ≃ l) :
    Measurable fun G : Matrix m m ℂ => Matrix.reindex e e G :=
  Measurable.of_eval fun a => Measurable.of_eval fun b =>
    (measurable_entry_matrixC measurable_id (e.symm a) (e.symm b) :)

/-- The measurable proxy of the crossing Laplace integrand: `schurProxy` of the reindexed Schur
complement (equal to the crossing integrand on the good set, `crossingProxy_eq`). -/
def crossingProxy (E : ℝ) (f : CompactlySupportedContinuousMap ℝ ℝ) (H : p.SiteMatrix) : ℝ≥0∞ :=
  schurProxy p i E f (Matrix.reindex (Fintype.equivFin (PairSite p i))
    (Fintype.equivFin (PairSite p i)) (pairSchur p i H E))

theorem measurable_crossingProxy (E : ℝ) (f : CompactlySupportedContinuousMap ℝ ℝ) :
    Measurable (crossingProxy p i E f) :=
  (measurable_schurProxy p i E f).comp ((measurable_reindex_matrixC _).comp (measurable_pairSchur p i E))

theorem crossingSum_nonneg (f : CompactlySupportedContinuousMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    (H : p.SiteMatrix) (E : ℝ) : 0 ≤ crossingSum p i f H E :=
  Multiset.sum_nonneg fun x hx => by
    obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hx
    exact hf _

theorem crossingProxy_le_one (E : ℝ) (f : CompactlySupportedContinuousMap ℝ ℝ)
    (hf : ∀ x, 0 ≤ f x) (H : p.SiteMatrix) : crossingProxy p i E f H ≤ 1 := by
  unfold crossingProxy schurProxy
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr ?_)
  simp only [Left.neg_nonpos_iff]
  exact Finset.sum_nonneg fun k _ => hf _

/-- On the good set (Hermitian `H`, invertible exterior minor) the proxy is the crossing
integrand. -/
theorem crossingProxy_eq (E : ℝ) (f : CompactlySupportedContinuousMap ℝ ℝ) (H : p.SiteMatrix)
    (hH : H.IsHermitian) (hdet : (exteriorBlock p i H - (E : ℂ) • 1).det ≠ 0)
    (hsc : crossingScale p E ≠ 0) :
    ENNReal.ofReal (Real.exp (-crossingSum p i f H E)) = crossingProxy p i E f H := by
  unfold crossingProxy schurProxy
  congr 3
  rw [crossingSum_eq p i f H hH E hdet hsc]
  have hS := pairSchur_isHermitian p i H hH E
  have hB : (Matrix.reindex (Fintype.equivFin (PairSite p i)) (Fintype.equivFin (PairSite p i))
      (pairSchur p i H E)).IsHermitian := by
    unfold IsHermitian at hS ⊢
    rw [reindex_apply, conjTranspose_submatrix, hS]
  rw [← sum_orderedEigenvalue_reindex (Fintype.equivFin (PairSite p i)) hS hB
    (fun x => f (-(crossingScale p E * x)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [reflectTest_apply, orderedEigenvalue_congr _ hB (hermPart_of_isHermitian hB) k]

/-!
## The conditional crossing integral at a fixed exterior
-/

theorem crossingProxy_assemble (E : ℝ) (f : CompactlySupportedContinuousMap ℝ ℝ)
    (ω : SplitState p i) (G : PairMatrix p i) :
    crossingProxy p i E f (assemble p i ω G) =
      schurProxy p i E f (Matrix.reindex (Fintype.equivFin (PairSite p i))
        (Fintype.equivFin (PairSite p i)) G + pairResidualFin p i ω E) := by
  unfold crossingProxy pairResidualFin
  rw [pairSchur_assemble]
  congr 1

/-- The unfolded integrand of the external sine theorem at energy `0` and density `ρ'`. -/
def unfoldedIntegrand (N : ℕ) (ρ' : ℝ) (g : CompactlySupportedContinuousMap ℝ ℝ)
    (B : Johansson.HermitianMatrix N) : ℝ :=
  Real.exp (-(∑ k, g ((N : ℝ) * ρ' * (Model.Construction.orderedEigenvalue B k - 0))))

theorem measurable_unfoldedIntegrand (N : ℕ) (ρ' : ℝ) (g : CompactlySupportedContinuousMap ℝ ℝ) :
    Measurable (unfoldedIntegrand N ρ' g) := by
  unfold unfoldedIntegrand
  refine Real.measurable_exp.comp (Measurable.neg ?_)
  refine Finset.measurable_sum _ fun k _ => ?_
  exact g.continuous.measurable.comp (measurable_const.mul
    ((BlockBand.Model.Construction.measurable_orderedEigenvalue k).sub measurable_const))

theorem measurable_deformedSample {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) :
    Measurable fun z : Johansson.UpperPair N → ℝ × ℝ =>
      (⟨F + (Johansson.gaussianMatrix z).1, hF.add (Johansson.gaussianMatrix z).2⟩ :
        Johansson.HermitianMatrix N) :=
  Measurable.subtype_mk (measurable_const.add
    (measurable_subtype_coe.comp Johansson.measurable_gaussianMatrix))

theorem isProbabilityMeasure_deformedGUELaw (N : ℕ) (t : ℝ≥0) (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian) : IsProbabilityMeasure (deformedGUELaw N t F hF) := by
  have := Johansson.coordinateMeasure_probability N (Johansson.sourceTime N t)
  unfold deformedGUELaw
  infer_instance

/-- `ofReal` of the unfolded Laplace functional is the lower integral of its integrand. -/
theorem ofReal_unfoldedLaplace (N : ℕ) (t : ℝ≥0) (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian) (ρ' : ℝ) (g : CompactlySupportedContinuousMap ℝ ℝ) (hg : ∀ x, 0 ≤ g x) :
    ENNReal.ofReal (unfoldedLaplace N t F hF 0 ρ' g) =
      ∫⁻ B, ENNReal.ofReal (unfoldedIntegrand N ρ' g B) ∂deformedGUELaw N t F hF := by
  have := isProbabilityMeasure_deformedGUELaw N t F hF
  have hle : ∀ B, unfoldedIntegrand N ρ' g B ≤ 1 := fun B =>
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Finset.sum_nonneg fun k _ => hg _))
  have hint : Integrable (unfoldedIntegrand N ρ' g) (deformedGUELaw N t F hF) :=
    Integrable.of_bound (C := 1) (measurable_unfoldedIntegrand N ρ' g).aestronglyMeasurable
      (Eventually.of_forall fun B => by
        rw [Real.norm_eq_abs]
        unfold unfoldedIntegrand at hle ⊢
        rw [abs_of_pos (Real.exp_pos _)]; exact hle B)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun B => (Real.exp_pos _).le)]
  rfl

/-- The conditional crossing integral at a fixed exterior with Hermitian residual: under the GUE
law bridge, `∫ exp(-Σ_j f(t_j)) dGUE(G)` is the lower integral, under the deformed GUE law
(deformation `K(E)`, variance `s`), of `exp(-Σ_k f(-𝒩ρ λ_k))`. -/
theorem lintegral_crossingProxy_assemble (hGUE : GUELawBridge) (E : ℝ)
    (f : CompactlySupportedContinuousMap ℝ ℝ) (ω : SplitState p i)
    (hK : (pairResidualFin p i ω E).IsHermitian) :
    ∫⁻ G, crossingProxy p i E f (assemble p i ω G) ∂gueMeasure (PairSite p i) (pairTime p (pairS p)) =
      ∫⁻ B, ENNReal.ofReal (Real.exp (-∑ k, reflectTest f (crossingScale p E *
          Model.Construction.orderedEigenvalue B k)))
        ∂deformedGUELaw (Fintype.card (PairSite p i)) (pairS p).toNNReal (pairResidualFin p i ω E)
          hK := by
  set N := Fintype.card (PairSite p i)
  set e := Fintype.equivFin (PairSite p i)
  set F := pairResidualFin p i ω E
  have hF := hK
  have hpos : 0 < pairS p := lt_min p.b_pos (by unfold Parameters.c; linarith [p.b_lt_half])
  have hN : (N : ℝ) = 2 * p.W := by simp only [N]; rw [card_pairSite]; push_cast; ring
  have htime : pairTime p (pairS p) = Johansson.sourceTime N (pairS p).toNNReal := by
    apply NNReal.eq
    rw [Johansson.sourceTime_coe, Real.coe_toNNReal _ hpos.le, pairTime,
      Real.coe_toNNReal _ (div_nonneg hpos.le (by positivity)), hN]
  simp_rw [crossingProxy_assemble]
  have hre : Measurable fun G : PairMatrix p i => Matrix.reindex e e G := measurable_reindex_matrixC e
  have hsh : Measurable fun Y : Matrix (Fin N) (Fin N) ℂ => schurProxy p i E f (Y + F) :=
    (measurable_schurProxy p i E f).comp (measurable_id.add measurable_const)
  rw [← lintegral_map hsh hre, hGUE (PairSite p i) N e, htime]
  unfold gueMatrixLaw deformedGUELaw
  rw [lintegral_map (g := fun z : Johansson.UpperPair N → ℝ × ℝ => (Johansson.gaussianMatrix z).1)
      hsh (measurable_subtype_coe.comp Johansson.measurable_gaussianMatrix),
    lintegral_map _ (measurable_deformedSample F hF)]
  · refine lintegral_congr fun z => ?_
    unfold schurProxy
    have hX : ∀ k, Model.Construction.orderedEigenvalue
        ⟨hermPart ((Johansson.gaussianMatrix z).1 + F), hermPart_isHermitian _⟩ k =
        Model.Construction.orderedEigenvalue
          ⟨F + (Johansson.gaussianMatrix z).1, hF.add (Johansson.gaussianMatrix z).2⟩ k :=
      fun k => orderedEigenvalue_congr _ _ (by
        rw [hermPart_of_isHermitian ((Johansson.gaussianMatrix z).2.add hF), add_comm]) k
    simp only [hX]
  · refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.neg ?_))
    refine Finset.measurable_sum _ fun k _ => ?_
    exact (reflectTest f).continuous.measurable.comp (measurable_const.mul
      (BlockBand.Model.Construction.measurable_orderedEigenvalue k))

/-- Sandwich of the conditional integral. If `ρ' > 0` and `g⁻ ≤ f(-r·) ≤ g⁺` for
`r = 𝒩ρ/(𝒩'ρ')`, the conditional integral lies between the unfolded Laplace functionals of the
external sine theorem at `g⁺` and `g⁻`. -/
theorem unfoldedLaplace_sandwich (N : ℕ) (t : ℝ≥0) (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian) (σ ρ' : ℝ) (f gm gp : CompactlySupportedContinuousMap ℝ ℝ)
    (hgm : ∀ x, 0 ≤ gm x) (hgp : ∀ x, 0 ≤ gp x)
    (hsand : ∀ y, gm y ≤ f (σ / ((N : ℝ) * ρ') * y) ∧ f (σ / ((N : ℝ) * ρ') * y) ≤ gp y)
    (hρ' : (N : ℝ) * ρ' ≠ 0) :
    ENNReal.ofReal (unfoldedLaplace N t F hF 0 ρ' gp) ≤
        ∫⁻ B, ENNReal.ofReal (Real.exp (-∑ k, f (σ * Model.Construction.orderedEigenvalue B k)))
          ∂deformedGUELaw N t F hF ∧
      ∫⁻ B, ENNReal.ofReal (Real.exp (-∑ k, f (σ * Model.Construction.orderedEigenvalue B k)))
          ∂deformedGUELaw N t F hF ≤ ENNReal.ofReal (unfoldedLaplace N t F hF 0 ρ' gm) := by
  have hkey : ∀ x : ℝ, f (σ * x) = f (σ / ((N : ℝ) * ρ') * ((N : ℝ) * ρ' * (x - 0))) := by
    intro x; congr 1; rw [sub_zero, ← mul_assoc, div_mul_cancel₀ σ hρ']
  rw [ofReal_unfoldedLaplace N t F hF ρ' gp hgp, ofReal_unfoldedLaplace N t F hF ρ' gm hgm]
  constructor
  · refine lintegral_mono fun B => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    refine neg_le_neg (Finset.sum_le_sum fun k _ => ?_)
    rw [hkey]; exact (hsand _).2
  · refine lintegral_mono fun B => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    refine neg_le_neg (Finset.sum_le_sum fun k _ => ?_)
    rw [hkey]; exact (hsand _).1

/-!
## Integration over the fresh-pair split
-/

theorem isProbabilityMeasure_of_splitting (model : p.GaussianRingModel) (s : ℝ)
    (Pω : Measure (SplitState p i)) (h : IsPairSplitting p i model s Pω) :
    IsProbabilityMeasure Pω := by
  have := isProbabilityMeasure_gueMeasure (PairSite p i) (pairTime p s)
  constructor
  have h1 := congrArg (fun μ : Measure p.SiteMatrix => μ Set.univ) h
  rw [Measure.map_apply (measurable_assemble p i) MeasurableSet.univ, Set.preimage_univ,
    ← Set.univ_prod_univ, Measure.prod_prod, measure_univ (μ := gueMeasure (PairSite p i) _),
    mul_one, measure_univ (μ := (model.law : Measure p.SiteMatrix))] at h1
  exact h1

/-- Bounds from the conditional integrals. If on a set `R` of exteriors with outer probability of
its complement at most `ε` the exterior minor is invertible and the conditional crossing integral
lies in `[lo, hi]`, then `lo (1 - ε) ≤ E exp(-Σ_j f(t_j)) ≤ hi + ε`. -/
theorem crossingLaplace_bounds (model : p.GaussianRingModel) (E : ℝ)
    (f : CompactlySupportedContinuousMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x) (Pω : Measure (SplitState p i))
    (hsplit : IsPairSplitting p i model (pairS p) Pω) (hsc : crossingScale p E ≠ 0)
    (lo hi : ℝ≥0∞) (ε : ℝ) (R : Set (SplitState p i))
    (hR : ∀ ω ∈ R, (ω.1 - (E : ℂ) • 1).det ≠ 0 ∧
      lo ≤ ∫⁻ G, crossingProxy p i E f (assemble p i ω G)
        ∂gueMeasure (PairSite p i) (pairTime p (pairS p)) ∧
      ∫⁻ G, crossingProxy p i E f (assemble p i ω G)
        ∂gueMeasure (PairSite p i) (pairTime p (pairS p)) ≤ hi)
    (hRc : Pω Rᶜ ≤ ENNReal.ofReal ε) :
    lo * (1 - ENNReal.ofReal ε) ≤ crossingLaplace p model i E f ∧
      crossingLaplace p model i E f ≤ hi + ENNReal.ofReal ε := by
  set GUE := gueMeasure (PairSite p i) (pairTime p (pairS p))
  have : IsProbabilityMeasure GUE := isProbabilityMeasure_gueMeasure _ _
  have : IsProbabilityMeasure Pω := isProbabilityMeasure_of_splitting p i model _ Pω hsplit
  set D : Set p.SiteMatrix := {H | (exteriorBlock p i H - (E : ℂ) • 1).det ≠ 0}
  have hD : MeasurableSet D :=
    (((continuous_exteriorBlock p i).sub continuous_const).matrix_det.measurable)
      (measurableSet_singleton 0).compl
  set Ψ := crossingProxy p i E f
  have hΨ : Measurable Ψ := measurable_crossingProxy p i E f
  have hasm := measurable_assemble p i
  have hlaw : (model.law : Measure p.SiteMatrix) =
      (Pω.prod GUE).map fun x => assemble p i x.1 x.2 := hsplit.symm
  have hherm : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), H.IsHermitian := model.isPhysical.1
  have hmemD : ∀ ω G, (ω.1 - (E : ℂ) • 1).det ≠ 0 → assemble p i ω G ∈ D := by
    intro ω G h
    change (exteriorBlock p i (assemble p i ω G) - (E : ℂ) • 1).det ≠ 0
    rw [exteriorBlock_assemble]; exact h
  have hΦΨ : ∀ H : p.SiteMatrix, H.IsHermitian → H ∈ D →
      ENNReal.ofReal (Real.exp (-crossingSum p i f H E)) = Ψ H :=
    fun H hH hHD => crossingProxy_eq p i E f H hH hHD hsc
  have hΦ1 : ∀ H : p.SiteMatrix, ENNReal.ofReal (Real.exp (-crossingSum p i f H E)) ≤ 1 := by
    intro H
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (crossingSum_nonneg p i f hf H E)))
  have hcomp : ∀ u : p.SiteMatrix → ℝ≥0∞, Measurable u →
      ∫⁻ H, u H ∂(model.law : Measure p.SiteMatrix) =
        ∫⁻ ω, ∫⁻ G, u (assemble p i ω G) ∂GUE ∂Pω := by
    intro u hu
    rw [hlaw, lintegral_map hu hasm]
    exact lintegral_prod (fun x => u (assemble p i x.1 x.2)) (hu.comp hasm).aemeasurable
  have hRS : ∀ S : Set (SplitState p i), R ⊆ S → Pω Sᶜ ≤ ENNReal.ofReal ε :=
    fun S hS => (measure_mono (Set.compl_subset_compl.mpr hS)).trans hRc
  constructor
  · -- lower bound
    set hl : SplitState p i → ℝ≥0∞ := fun ω => ∫⁻ G, D.indicator Ψ (assemble p i ω G) ∂GUE
    have hlm : Measurable hl := ((hΨ.indicator hD).comp hasm).lintegral_prod_right'
    set S := {ω | lo ≤ hl ω}
    have hS : MeasurableSet S := measurableSet_le measurable_const hlm
    have hRS' : R ⊆ S := by
      intro ω hω
      obtain ⟨hdet, hlo, -⟩ := hR ω hω
      change lo ≤ ∫⁻ G, D.indicator Ψ (assemble p i ω G) ∂GUE
      have : (fun G => D.indicator Ψ (assemble p i ω G)) = fun G => Ψ (assemble p i ω G) :=
        funext fun G => Set.indicator_of_mem (hmemD ω G hdet) _
      rw [this]; exact hlo
    have hPS : 1 - ENNReal.ofReal ε ≤ Pω S := by
      rw [tsub_le_iff_right, ← measure_univ (μ := Pω), ← measure_add_measure_compl hS]
      exact add_le_add le_rfl (hRS S hRS')
    calc lo * (1 - ENNReal.ofReal ε) ≤ lo * Pω S := mul_le_mul' le_rfl hPS
      _ = ∫⁻ ω, S.indicator (fun _ => lo) ω ∂Pω := (lintegral_indicator_const hS lo).symm
      _ ≤ ∫⁻ ω, hl ω ∂Pω := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : ω ∈ S
          · rw [Set.indicator_of_mem hω]; exact hω
          · rw [Set.indicator_of_notMem hω]; exact bot_le
      _ = ∫⁻ H, D.indicator Ψ H ∂(model.law : Measure p.SiteMatrix) :=
          (hcomp _ (hΨ.indicator hD)).symm
      _ ≤ crossingLaplace p model i E f := by
          refine lintegral_mono_ae (hherm.mono fun H hH => ?_)
          by_cases hHD : H ∈ D
          · rw [Set.indicator_of_mem hHD, hΦΨ H hH hHD]
          · rw [Set.indicator_of_notMem hHD]; exact bot_le
  · -- upper bound
    set u : p.SiteMatrix → ℝ≥0∞ := fun H => D.indicator Ψ H + Dᶜ.indicator 1 H
    have hu : Measurable u := (hΨ.indicator hD).add (measurable_one.indicator hD.compl)
    set hu' : SplitState p i → ℝ≥0∞ := fun ω => ∫⁻ G, u (assemble p i ω G) ∂GUE
    have hum : Measurable hu' := (hu.comp hasm).lintegral_prod_right'
    have hu1 : ∀ ω, hu' ω ≤ 1 := by
      intro ω
      calc hu' ω ≤ ∫⁻ _G, 1 ∂GUE := by
            refine lintegral_mono fun G => ?_
            change D.indicator Ψ _ + Dᶜ.indicator 1 _ ≤ 1
            by_cases h : assemble p i ω G ∈ D
            · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr h), add_zero]
              exact crossingProxy_le_one p i E f hf _
            · rw [Set.indicator_of_notMem h, Set.indicator_of_mem (show _ ∈ Dᶜ from h), zero_add]
              rfl
        _ = 1 := by rw [lintegral_const, measure_univ, one_mul]
    set S := {ω | hu' ω ≤ hi}
    have hS : MeasurableSet S := measurableSet_le hum measurable_const
    have hRS' : R ⊆ S := by
      intro ω hω
      obtain ⟨hdet, -, hhi⟩ := hR ω hω
      change ∫⁻ G, u (assemble p i ω G) ∂GUE ≤ hi
      have : (fun G => u (assemble p i ω G)) = fun G => Ψ (assemble p i ω G) := by
        funext G
        change D.indicator Ψ _ + Dᶜ.indicator 1 _ = _
        rw [Set.indicator_of_mem (hmemD ω G hdet),
          Set.indicator_of_notMem (Set.notMem_compl_iff.mpr (hmemD ω G hdet)), add_zero]
      rw [this]; exact hhi
    calc crossingLaplace p model i E f ≤ ∫⁻ H, u H ∂(model.law : Measure p.SiteMatrix) := by
          refine lintegral_mono_ae (hherm.mono fun H hH => ?_)
          change _ ≤ D.indicator Ψ H + Dᶜ.indicator 1 H
          by_cases hHD : H ∈ D
          · rw [Set.indicator_of_mem hHD, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hHD), add_zero,
              hΦΨ H hH hHD]
          · rw [Set.indicator_of_notMem hHD, Set.indicator_of_mem (show H ∈ Dᶜ from hHD),
              zero_add]
            exact hΦ1 H
      _ = ∫⁻ ω, hu' ω ∂Pω := hcomp u hu
      _ ≤ ∫⁻ ω, (hi + Sᶜ.indicator 1 ω) ∂Pω := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : ω ∈ S
          · exact le_add_right hω
          · rw [Set.indicator_of_mem (show ω ∈ Sᶜ from hω)]
            exact (hu1 ω).trans le_add_self
      _ = hi + Pω Sᶜ := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_indicator_one hS.compl]
      _ ≤ hi + ENNReal.ofReal ε := add_le_add le_rfl (hRS S hRS')

end Pair

/-!
## The exterior minor is a.s. invertible at a deterministic energy
-/

section Minor

variable (p : Parameters) (i : ZMod p.n)

/-- A real diagonal matrix is reconstructed from its active Gaussian coordinates. -/
theorem gaussianActiveReconstruction_realDiagonal (d : p.Site → ℝ) :
    p.gaussianActiveReconstruction (p.gaussianActiveExtraction
      (Matrix.diagonal fun x => (d x : ℂ))) = Matrix.diagonal fun x => (d x : ℂ) := by
  classical
  have hcoord : p.gaussianActiveValue (p.gaussianActiveExtraction
      (Matrix.diagonal fun x => (d x : ℂ))) =
      p.gaussianExtraction (Matrix.diagonal fun x => (d x : ℂ)) := by
    funext c
    unfold Parameters.gaussianActiveValue Parameters.gaussianActiveExtraction
    split_ifs with hc
    · rfl
    · cases c with
      | inl x => exact False.elim (hc (p.gaussianCoordinateVariance_diagonal_ne_zero x))
      | inr xy =>
          rcases xy with ⟨x, y, b⟩
          by_cases hxy : x = y
          · subst y
            simp [Parameters.gaussianExtraction]
          · simp [Parameters.gaussianExtraction, Matrix.diagonal_apply_ne _ hxy]
  rw [Parameters.gaussianActiveReconstruction, hcoord]
  apply p.gaussianReconstruction_gaussianExtraction
  rw [Matrix.isHermitian_diagonal_iff]
  intro x
  simp [IsSelfAdjoint]

/-- `det(H_RR - E) ≠ 0` almost surely under every physical law, at every deterministic real `E`:
it is a nonzero polynomial in the active Gaussian coordinates (witness: the diagonal matrix
`(E + 1) I`, for which `H_RR - E = I`). -/
theorem ae_det_exteriorBlock_ne_zero (model : p.GaussianRingModel) (E : ℝ) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), (exteriorBlock p i H - (E : ℂ) • 1).det ≠ 0 := by
  classical
  set U := p.gaussianUniversalMatrix
  set Ue : Matrix (ExteriorSite p i) (ExteriorSite p i) (MvPolynomial p.GaussianActiveCoordinate ℂ) :=
    fun a b => U a.1 b.1 - if a = b then MvPolynomial.C (E : ℂ) else 0
  have heval : ∀ g : p.GaussianActiveCoordinate → ℝ,
      MvPolynomial.eval (fun j => (g j : ℂ)) Ue.det =
        (exteriorBlock p i (p.gaussianActiveReconstruction g) - (E : ℂ) • 1).det := by
    intro g
    rw [RingHom.map_det]
    congr 1
    ext a b
    have h := congrFun (congrFun (p.gaussianUniversalMatrix_map_eval g) a.1) b.1
    simp only [Matrix.map_apply] at h
    change MvPolynomial.eval (fun j => (g j : ℂ)) (Ue a b) = _
    simp only [Ue, U, map_sub, h, exteriorBlock, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  set d : p.Site → ℝ := fun _ => E + 1
  set z₀ := p.gaussianActiveExtraction (Matrix.diagonal fun x => (d x : ℂ))
  have h₀ : MvPolynomial.eval (fun j => (z₀ j : ℂ)) Ue.det ≠ 0 := by
    rw [heval, gaussianActiveReconstruction_realDiagonal]
    have : exteriorBlock p i (Matrix.diagonal fun x => (d x : ℂ)) - (E : ℂ) • 1 = 1 := by
      ext a b
      by_cases hab : a = b
      · subst hab; simp [exteriorBlock, d]
      · have : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
        simp [exteriorBlock, Matrix.diagonal_apply_ne _ this, Matrix.one_apply_ne hab]
    rw [this, det_one]; exact one_ne_zero
  filter_upwards [model.ae_activePolynomial_ne_zero Ue.det z₀ h₀,
    model.ae_gaussianActiveReconstruction_eq] with H hpoly hrec
  rwa [heval, hrec] at hpoly

/-- Under every splitting law the exterior minor is a.s. invertible at deterministic `E`. -/
theorem splitting_det_null (model : p.GaussianRingModel) (s : ℝ) (Pω : Measure (SplitState p i))
    (h : IsPairSplitting p i model s Pω) (E : ℝ) :
    Pω {ω | (ω.1 - (E : ℂ) • 1).det = 0} = 0 := by
  have := isProbabilityMeasure_gueMeasure (PairSite p i) (pairTime p s)
  set S : Set p.SiteMatrix := {H | (exteriorBlock p i H - (E : ℂ) • 1).det = 0}
  have hS : MeasurableSet S :=
    (((continuous_exteriorBlock p i).sub continuous_const).matrix_det.measurable)
      (measurableSet_singleton 0)
  have hnull : (model.law : Measure p.SiteMatrix) S = 0 := by
    have := ae_det_exteriorBlock_ne_zero p i model E
    rw [ae_iff] at this
    simpa [S] using this
  rw [← h, Measure.map_apply (measurable_assemble p i) hS] at hnull
  have hpre : (fun x : SplitState p i × PairMatrix p i => assemble p i x.1 x.2) ⁻¹' S =
      {ω : SplitState p i | (ω.1 - (E : ℂ) • 1).det = 0} ×ˢ Set.univ := by
    ext x; simp [S, exteriorBlock_assemble]
  rw [hpre, Measure.prod_prod, measure_univ, mul_one] at hnull
  exact hnull

end Minor

/-!
## Consequences of the pair regular event (`PairRegularEventContract`)
-/

theorem l2_opNorm_le_of_l2Norm {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, l2Norm (K *ᵥ x) ≤ C * l2Norm x) : ‖K‖ ≤ C := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  have h1 := h (WithLp.ofLp x)
  simp only [l2Norm] at h1
  simpa [EuclideanSpace.norm_eq, Matrix.toEuclideanLin] using h1

theorem l2_opNorm_real_smul_one_le {N : ℕ} (E : ℝ) :
    ‖((E : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))‖ ≤ |E| := by
  refine l2_opNorm_le_of_l2Norm _ (abs_nonneg E) fun x => ?_
  simp only [l2Norm, smul_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]

/-- The boundary MDE from a fixed point of the fresh Dyson equation: for Hermitian `F`,
`s > 0`, real `E` and `m` with `Im m > 0` and `m = ⟨(F - E - s m)⁻¹⟩`, the matrix
`M = (F - E - s m)⁻¹` solves `IsBoundaryMDE s (F - E) 0 M` and `⟨M⟩ = m`. -/
theorem isBoundaryMDE_of_fixedPoint {N : ℕ} {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {s : ℝ} (hs : 0 < s) (E : ℝ) {m : ℂ} (hm : 0 < m.im)
    (hfix : m = (N : ℂ)⁻¹ * (F - ((E : ℂ) + (s : ℂ) * m) • 1)⁻¹.trace) :
    IsBoundaryMDE s (F - (E : ℂ) • 1) 0 (F - ((E : ℂ) + (s : ℂ) * m) • 1)⁻¹ ∧
      CEH.normalizedTrace (F - ((E : ℂ) + (s : ℂ) * m) • 1)⁻¹ = m := by
  set z : ℂ := (E : ℂ) + (s : ℂ) * m
  set X := F - z • 1
  have hzim : z.im = s * m.im := by simp [z]
  have hzpos : 0 < z.im := by rw [hzim]; positivity
  have hdet : X.det ≠ 0 := by
    have : X = F + (-z) • 1 := by simp [X, sub_eq_add_neg, neg_smul]
    rw [this, det_add_smul_one_eq_prod hF]
    refine Finset.prod_ne_zero_iff.mpr fun k _ h => ?_
    have := congrArg Complex.im h
    simp at this
    linarith
  have hu : IsUnit X.det := isUnit_iff_ne_zero.mpr hdet
  have hMX : X⁻¹ * X = 1 := nonsing_inv_mul X hu
  have hXM : X * X⁻¹ = 1 := mul_nonsing_inv X hu
  have htr : CEH.normalizedTrace X⁻¹ = m := by rw [CEH.normalizedTrace, ← hfix]
  refine ⟨⟨?_, ?_⟩, htr⟩
  · rw [htr]
    have : F - (E : ℂ) • 1 - (((0 : ℝ) : ℂ) + (s : ℂ) * m) • 1 = X := by
      simp only [X, z, Complex.ofReal_zero, zero_add, add_smul]; abel
    rw [this, hXM]
  · -- `Im M = Im z · M M*`
    have hXh : Xᴴ = F - (starRingEnd ℂ z) • 1 := by
      simp only [X, conjTranspose_sub, hF.eq, conjTranspose_smul, conjTranspose_one]; rfl
    have hXhM : Xᴴ * (X⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, hMX, conjTranspose_one]
    have hdiff : X⁻¹ - (X⁻¹)ᴴ = (2 * Complex.I * (z.im : ℂ)) • (X⁻¹ * (X⁻¹)ᴴ) := by
      have h1 : X⁻¹ - (X⁻¹)ᴴ = X⁻¹ * (Xᴴ - X) * (X⁻¹)ᴴ := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hXhM, Matrix.mul_one, hMX,
          Matrix.one_mul]
      rw [h1, hXh]
      have : F - (starRingEnd ℂ z) • 1 - X = (2 * Complex.I * (z.im : ℂ)) • (1 : Matrix _ _ ℂ) := by
        simp only [X, sub_sub_sub_cancel_left, ← sub_smul]
        congr 1
        apply Complex.ext <;> simp; ring
      rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    have hpd : (X⁻¹ * (X⁻¹)ᴴ).PosDef := by
      refine PosDef.mul_conjTranspose_self _ fun v w hvw => ?_
      have := congrArg (fun u => u ᵥ* X) hvw
      simpa only [vecMul_vecMul, hMX, vecMul_one] using this
    rw [CEH.imaginaryPart, hdiff, smul_smul]
    have hc : (2 * Complex.I)⁻¹ * (2 * Complex.I * (z.im : ℂ)) = ((z.im : ℝ) : ℂ) := by
      field_simp
    rw [hc]
    exact hpd.smul (by exact_mod_cast hzpos)

section Regular

variable (p : Parameters) (i : ZMod p.n)

/-- **From the regular event to the inputs of the external sine theorem.** On
`IsPairRegular` at `e = E` (reindexing `Fintype.equivFin`), the reindexed pair residual
`K(E) = F(E) - E` is Hermitian, `‖K‖ ≤ 𝒩'^(max A 0 + 2)`, and `M = freshM F s E` solves the
boundary MDE of `K` at energy `0` with `v₀ ≤ Im⟨M⟩` and `|Im⟨M⟩/π - ρ(E)| ≤ η/π`
(`Im conj(a(E)) = πρ(E)`).
-/
theorem pairRegular_externalSine_inputs {A r₀ s₀ v₀ η E : ℝ}
    (hFC : FreshConstants (pairS p) r₀ s₀ v₀) (hE : |E| ≤ 2) (ω : SplitState p i)
    (h : IsPairRegular p i (Fintype.equivFin (PairSite p i)) A r₀ s₀ v₀ η E ω) :
    (pairResidualFin p i ω E).IsHermitian ∧
      ‖pairResidualFin p i ω E‖ ≤ (Fintype.card (PairSite p i) : ℝ) ^ (max A 0 + 2) ∧
      ∃ M, IsBoundaryMDE (pairS p) (pairResidualFin p i ω E) 0 M ∧
        v₀ ≤ (CEH.normalizedTrace M).im ∧
        |(CEH.normalizedTrace M).im / Real.pi - Parameters.semicircleDensity E| ≤
          η / Real.pi := by
  obtain ⟨-, -, hr₀, hs₀, -, hv₀⟩ := hFC
  obtain ⟨⟨hF, hnorm, hreg⟩, hdys⟩ := h
  set F := pairDeformation p i (Fintype.equivFin (PairSite p i)) ω E
  have hKF : pairResidualFin p i ω E = F - (E : ℂ) • 1 := by
    ext a b
    simp only [pairResidualFin, F, pairDeformation, pairResidual,
      reindex_apply, submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq]
  have hspos : 0 < pairS p := lt_min p.b_pos (by unfold Parameters.c; linarith [p.b_lt_half])
  have hv := (hreg (pairS p) ⟨by linarith, le_rfl⟩ E (by simp; linarith)
    0 ⟨le_rfl, zero_le_one⟩).1
  set m := freshDyson F (pairS p) (E : ℂ)
  have hm' : (freshDyson F (pairS p) ⟨E, 0⟩) = m := rfl
  rw [hm'] at hv
  have hm0 : 0 < m.im := lt_of_lt_of_le hv₀ hv
  have hspec : 0 < m.im ∧
      m = ((Fintype.card (PairSite p i) : ℕ) : ℂ)⁻¹ * (F - ((E : ℂ) + (pairS p : ℂ) * m) • 1)⁻¹.trace := by
    have hm1 := hm0
    simp only [m, freshDyson] at hm1 ⊢
    split_ifs at hm1 ⊢ with hex
    · exact Classical.choose_spec hex
    · simp at hm1
  obtain ⟨hMDE, htr⟩ := isBoundaryMDE_of_fixedPoint hF hspos E hspec.1 hspec.2
  have hK : (pairResidualFin p i ω E).IsHermitian := by
    rw [hKF]; exact hF.sub (isHermitian_real_smul_one E)
  refine ⟨hK, ?_, _, hKF ▸ hMDE, by rw [htr]; exact hv, ?_⟩
  · -- the norm
    have hN2 : (2 : ℝ) ≤ (Fintype.card (PairSite p i) : ℕ) := by
      have : Fintype.card (PairSite p i) = 2 * p.W := card_pairSite p i
      have hW : 1 ≤ p.W := p.W_pos
      have : (2 : ℕ) ≤ Fintype.card (PairSite p i) := by omega
      exact_mod_cast this
    have hN1 : (1 : ℝ) ≤ (Fintype.card (PairSite p i) : ℕ) := by linarith
    have hFn : ‖F‖ ≤ ((Fintype.card (PairSite p i) : ℕ) : ℝ) ^ A :=
      l2_opNorm_le_of_l2Norm F (Real.rpow_nonneg (by linarith) _) hnorm
    set A' := max A 0
    have h1 : ((Fintype.card (PairSite p i) : ℕ) : ℝ) ^ A ≤ ((Fintype.card (PairSite p i) : ℕ) : ℝ) ^ A' := Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left _ _)
    have h2 : (1 : ℝ) ≤ ((Fintype.card (PairSite p i) : ℕ) : ℝ) ^ A' := Real.one_le_rpow hN1 (le_max_right _ _)
    have h3 : ((Fintype.card (PairSite p i) : ℕ) : ℝ) ^ (A' + 2) = ((Fintype.card (PairSite p i) : ℕ) : ℝ) ^ A' * ((Fintype.card (PairSite p i) : ℕ) : ℝ) ^ 2 := by
      rw [Real.rpow_add (by linarith), show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    rw [hKF, h3]
    calc ‖F - (E : ℂ) • 1‖ ≤ ‖F‖ + ‖(E : ℂ) • (1 : Matrix (Fin (Fintype.card (PairSite p i))) (Fin (Fintype.card (PairSite p i))) ℂ)‖ := norm_sub_le _ _
      _ ≤ ((Fintype.card (PairSite p i) : ℕ) : ℝ) ^ A + 2 := add_le_add hFn ((l2_opNorm_real_smul_one_le E).trans hE)
      _ ≤ ((Fintype.card (PairSite p i) : ℕ) : ℝ) ^ A' * ((Fintype.card (PairSite p i) : ℕ) : ℝ) ^ 2 := by
          have h4 : (4 : ℝ) ≤ ((Fintype.card (PairSite p i) : ℕ) : ℝ) ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left h4 (by linarith :
            (0 : ℝ) ≤ ((Fintype.card (PairSite p i) : ℕ) : ℝ) ^ A')]
  · -- the density
    rw [htr]
    have hρ : Real.pi * Parameters.semicircleDensity E = (starRingEnd ℂ (matchedA E)).im := by
      simp [Parameters.semicircleDensity, matchedA]
      field_simp
    have him : |m.im - (starRingEnd ℂ (matchedA E)).im| ≤ η := by
      rw [← Complex.sub_im]
      exact (Complex.abs_im_le_norm _).trans hdys
    rw [div_sub' Real.pi_ne_zero, abs_div, abs_of_pos Real.pi_pos, hρ]
    exact div_le_div_of_nonneg_right him Real.pi_pos.le

end Regular

/-!
## The crossing sine lemma
-/

theorem sineLaplaceFunctional_mem (f : CompactlySupportedContinuousMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ sineLaplaceFunctional f ∧ sineLaplaceFunctional f ≤ 1 := by
  obtain ⟨P, hP⟩ := exists_isSineLaw
  rw [← hP.2 f hf]
  constructor
  · exact integral_nonneg fun ξ => (Real.exp_pos _).le
  · calc ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure) ∂(P : Measure (VaguePointMeasure ℝ))
        ≤ ∫ _ξ, (1 : ℝ) ∂(P : Measure (VaguePointMeasure ℝ)) :=
          integral_mono_of_nonneg (Eventually.of_forall fun ξ => (Real.exp_pos _).le)
            (integrable_const 1) (Eventually.of_forall fun ξ =>
              Real.exp_le_one_iff.mpr (neg_nonpos.mpr (integral_nonneg hf)))
      _ = 1 := by simp

/-- **The crossing process has a sine limit.** For every critical
sequence (`n_j/W_j → τ`, `W_j → ∞`; every fixed critical ratio), fixed `0 < b < 1/2`,
deterministic bulk `-2 < E < 2`, every exact physical model and every adjacent pair `S_j`, the
crossing process `𝒞_W = Σ_j δ_{t_j}` of the pair flow `H(t) = H + t/(𝒩ρ) P_S` converges to the
unit-intensity sine process: for every nonnegative `f ∈ C_c(ℝ)`,
`E exp(-Σ_j f(t_j)) → L_sine(f)`.
This is a process in the pair perturbation parameter, not in the energy.
Hypotheses: `ExternalSine`, `CoareaContract` (existence of the splitting),
`PairRegularEventContract` and `GUELawBridge` (discharged by `guelawBridge_holds` in
`crossingSine_of_contracts`).
-/
theorem crossingSine (hExt : ExternalSine) (hCo : CoareaContract)
    (hPair : PairRegularEventContract) (hGUE : GUELawBridge) :
    ∀ (τ : ℝ) (s : CriticalSequence τ) (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), -2 < E → E < 2 →
      ∀ (model : ∀ j, (s.parameters b hb hb' j).GaussianRingModel)
        (i : ∀ j, ZMod (s.parameters b hb hb' j).n)
        (f : CompactlySupportedContinuousMap ℝ ℝ), (∀ x, 0 ≤ f x) →
          Tendsto (fun j => crossingLaplace (s.parameters b hb hb' j) (model j) (i j) E f) atTop
            (𝓝 (ENNReal.ofReal (sineLaplaceFunctional f))) := by
  intro τ s b E hb hb' hE hE' model i f hf
  set L := sineLaplaceFunctional f
  obtain ⟨hL0, hL1⟩ := sineLaplaceFunctional_mem f hf
  set ρ := Parameters.semicircleDensity E with hρdef
  have hρ : 0 < ρ := by
    unfold ρ Parameters.semicircleDensity
    refine div_pos (Real.sqrt_pos.mpr ?_) (by positivity)
    nlinarith
  set sv : ℝ := min b (1 - 2 * b)
  have hsv : 0 < sv := lt_min hb (by linarith)
  have hpairS : ∀ p : Parameters, p.b = b → pairS p = sv := by
    intro p hpb; simp only [pairS, Parameters.c, hpb, sv]
  set κ : ℝ := min (2 - E) (2 + E)
  have hκ : 0 < κ := lt_min (by linarith) (by linarith)
  have hEκ : E ∈ bulkInterval κ :=
    ⟨by linarith [min_le_right (2 - E) (2 + E)], by linarith [min_le_left (2 - E) (2 + E)]⟩
  have hE2 : |E| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨r₀, s₀, v₀, hFC, hD⟩ := hPair b hb hb' κ (τ + 1) hκ
  have hv : 0 < v₀ := hFC.2.2.2.2.2
  obtain ⟨A₀, hA₀⟩ := hD 1 one_pos
  set A : ℝ := max A₀ 0 + 2
  rw [ENNReal.tendsto_nhds ENNReal.ofReal_ne_top]
  intro η' hη'
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hη'
  have hrpos : 0 < r := by
    by_contra h
    rw [ENNReal.ofReal_of_nonpos (not_lt.mp h)] at hr1
    exact lt_irrefl _ hr1
  set η : ℝ := r / 5
  have hη : 0 < η := by positivity
  -- the dilation sandwich of the reflected test
  obtain ⟨δ, hδ, -, gm, gp, hgm, hgp, hsand, hgmL, hgpL⟩ :=
    exists_dilation_sandwich (reflectTest f) (fun x => hf _) hη
  rw [sineLaplaceFunctional_reflect] at hgmL hgpL
  -- the external sine theorem at variance `s`, energy `0`
  obtain ⟨-, hc⟩ := hExt A sv sv v₀ 0 0 0 hsv le_rfl hv
  obtain ⟨Np, hNp⟩ := hc gp hgp η hη
  obtain ⟨Nm, hNm⟩ := hc gm hgm η hη
  -- the regular event
  set ε' : ℝ := min η (min (ρ / 2) (δ * ρ / 2))
  have hε' : 0 < ε' := lt_min hη (lt_min (by positivity) (by positivity))
  obtain ⟨W₁, hW₁⟩ := hA₀ (Real.pi * ε') (by positivity)
  set W₀ : ℕ := max W₁ ⌈1 / ε'⌉₊
  have hWev : ∀ᶠ j in atTop, max W₀ (max Np Nm) ≤ s.W j :=
    s.width_tendsto.eventually_ge_atTop _
  have hnev : ∀ᶠ j in atTop, (s.n j : ℝ) ≤ (τ + 1) * s.W j := by
    filter_upwards [s.ratio_tendsto.eventually (gt_mem_nhds (show τ < τ + 1 by linarith))] with j hj
    have hW : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
    rw [div_lt_iff₀ hW] at hj
    exact hj.le
  have key : ∀ (p : Parameters), p.b = b → ∀ (mdl : p.GaussianRingModel) (ii : ZMod p.n),
      max W₀ (max Np Nm) ≤ p.W → (p.n : ℝ) ≤ (τ + 1) * p.W →
      ENNReal.ofReal (L - 2 * η) * (1 - ENNReal.ofReal ε') ≤ crossingLaplace p mdl ii E f ∧
        crossingLaplace p mdl ii E f ≤ ENNReal.ofReal (L + 2 * η) + ENNReal.ofReal ε' := by
    intro p hpb mdl ii hpW hnj
    have hWpos : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
    have hN : (Fintype.card (PairSite p ii) : ℝ) = 2 * p.W := by
      rw [card_pairSite]; push_cast; ring
    have hsc : crossingScale p E ≠ 0 := by unfold crossingScale; positivity
    obtain ⟨Pω, hPω⟩ := hCo.splitting_exists p mdl ii (pairS p)
      (by rw [hpairS p hpb]; exact hsv) (by rw [min_comm]; exact le_rfl)
    have hW₀p : W₀ ≤ p.W := le_trans (le_max_left _ _) hpW
    have hbad := hW₁ p hpb (le_trans (le_max_left _ _) hW₀p) hnj mdl ii Pω hPω
      (Fintype.equivFin (PairSite p ii)) E hEκ
    have hnull := splitting_det_null p ii mdl (pairS p) Pω hPω E
    have hFC' : FreshConstants (pairS p) r₀ s₀ v₀ := by rw [hpairS p hpb]; exact hFC
    have hWinv : (p.W : ℝ) ^ (-(1 : ℝ)) ≤ ε' := by
      have h1 : 1 / ε' ≤ p.W := (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hW₀p)
      rw [Real.rpow_neg_one, ← one_div, div_le_iff₀ hWpos]
      rw [div_le_iff₀ hε'] at h1
      linarith
    refine crossingLaplace_bounds p ii mdl E f hf Pω hPω hsc
      (ENNReal.ofReal (L - 2 * η)) (ENNReal.ofReal (L + 2 * η)) ε'
      {ω | IsPairRegular p ii (Fintype.equivFin (PairSite p ii)) A₀ r₀ s₀ v₀ (Real.pi * ε') E ω ∧
        (ω.1 - (E : ℂ) • 1).det ≠ 0} ?_ ?_
    rotate_left
    · calc Pω {ω | IsPairRegular p ii (Fintype.equivFin (PairSite p ii)) A₀ r₀ s₀ v₀
            (Real.pi * ε') E ω ∧ (ω.1 - (E : ℂ) • 1).det ≠ 0}ᶜ
          ≤ Pω ({ω | ¬ IsPairRegular p ii (Fintype.equivFin (PairSite p ii)) A₀ r₀ s₀ v₀
              (Real.pi * ε') E ω} ∪ {ω | (ω.1 - (E : ℂ) • 1).det = 0}) := by
            refine measure_mono fun ω hω => ?_
            simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_not] at hω
            exact hω
        _ ≤ ENNReal.ofReal ((p.W : ℝ) ^ (-(1 : ℝ))) + 0 :=
            (measure_union_le _ _).trans (add_le_add hbad hnull.le)
        _ ≤ ENNReal.ofReal ε' := by rw [add_zero]; exact ENNReal.ofReal_le_ofReal hWinv
    intro ω hωR
    obtain ⟨hreg, hdet⟩ := hωR
    obtain ⟨hF, hnorm, M, hMDE, hvM, hρM⟩ :=
      pairRegular_externalSine_inputs p ii hFC' hE2 ω hreg
    rw [mul_div_cancel_left₀ _ Real.pi_ne_zero] at hρM
    refine ⟨hdet, ?_⟩
    rw [lintegral_crossingProxy_assemble p ii hGUE E f ω hF]
    set F := pairResidualFin p ii ω E
    set t : ℝ≥0 := (pairS p).toNNReal
    have ht : (t : ℝ) = sv := by
      rw [Real.coe_toNNReal _ (le_of_lt (by rw [hpairS p hpb]; exact hsv)), hpairS p hpb]
    set ρ' := (CEH.normalizedTrace M).im / Real.pi
    have hρ'v : v₀ / Real.pi ≤ ρ' := div_le_div_of_nonneg_right hvM Real.pi_pos.le
    have hρ'ρ : |ρ' - ρ| ≤ ε' := hρM
    have hρ'low : ρ / 2 ≤ ρ' := by
      have := (abs_le.mp hρ'ρ).1
      have : ε' ≤ ρ / 2 := (min_le_right _ _).trans (min_le_left _ _)
      linarith
    have hρ'pos : 0 < ρ' := lt_of_lt_of_le (by positivity) hρ'low
    have hNρ' : (Fintype.card (PairSite p ii) : ℝ) * ρ' ≠ 0 := by rw [hN]; positivity
    have hrat : crossingScale p E / ((Fintype.card (PairSite p ii) : ℝ) * ρ') = ρ / ρ' := by
      unfold crossingScale; rw [hN, ← hρdef]; field_simp
    have hr : |crossingScale p E / ((Fintype.card (PairSite p ii) : ℝ) * ρ') - 1| ≤ δ := by
      rw [hrat, show ρ / ρ' - 1 = (ρ - ρ') / ρ' by field_simp, abs_div, abs_of_pos hρ'pos,
        div_le_iff₀ hρ'pos, abs_sub_comm]
      have h1 : ε' ≤ δ * ρ / 2 := (min_le_right _ _).trans (min_le_right _ _)
      nlinarith
    have hS := unfoldedLaplace_sandwich (Fintype.card (PairSite p ii)) t F hF (crossingScale p E) ρ' (reflectTest f) gm gp
      hgm hgp (hsand _ hr) hNρ'
    have hNN : ∀ N₀ : ℕ, N₀ ≤ p.W → N₀ ≤ Fintype.card (PairSite p ii) := by
      intro N₀ h
      have : Fintype.card (PairSite p ii) = 2 * p.W := card_pairSite p ii
      omega
    have hMDE' : IsBoundaryMDE (t : ℝ) F 0 M := by rw [ht, ← hpairS p hpb]; exact hMDE
    have htI : (t : ℝ) ∈ Set.Icc sv sv := by rw [ht]; exact ⟨le_rfl, le_rfl⟩
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 0 := ⟨le_rfl, le_rfl⟩
    have hp' := hNp (Fintype.card (PairSite p ii)) (hNN Np ((le_max_left _ _).trans ((le_max_right _ _).trans hpW))) F hF
      hnorm t htI 0 h0 M hMDE' hvM
    have hm' := hNm (Fintype.card (PairSite p ii)) (hNN Nm ((le_max_right _ _).trans ((le_max_right _ _).trans hpW))) F hF
      hnorm t htI 0 h0 M hMDE' hvM
    constructor
    · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hS.1
      linarith [(abs_le.mp hp').1, (abs_le.mp hgpL).1]
    · refine le_trans hS.2 (ENNReal.ofReal_le_ofReal ?_)
      linarith [(abs_le.mp hm').2, (abs_le.mp hgmL).2]
  filter_upwards [hWev, hnev] with j hWj hnj
  have hbounds := key (s.parameters b hb hb' j) rfl (model j) (i j) hWj hnj
  obtain ⟨hlow, hupp⟩ := hbounds
  have hε'η : ε' ≤ η := min_le_left _ _
  have h5 : ENNReal.ofReal (5 * η) ≤ η' := by
    have : 5 * η = r := by simp only [η]; ring
    rw [this]; exact hr2.le
  -- lower bound
  have hlow' : ENNReal.ofReal (L - 3 * η) ≤ crossingLaplace (s.parameters b hb hb' j) (model j) (i j) E f := by
    refine le_trans ?_ hlow
    by_cases hL3 : L - 3 * η ≤ 0
    · rw [ENNReal.ofReal_of_nonpos hL3]; exact bot_le
    · have hL2 : 0 ≤ L - 2 * η := by linarith
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hε'.le, ← ENNReal.ofReal_mul hL2]
      refine ENNReal.ofReal_le_ofReal ?_
      have : (L - 2 * η) * ε' ≤ η := by
        calc (L - 2 * η) * ε' ≤ 1 * ε' := mul_le_mul_of_nonneg_right (by linarith) hε'.le
          _ ≤ η := by linarith
      nlinarith
  constructor
  · rw [tsub_le_iff_right]
    calc ENNReal.ofReal L = ENNReal.ofReal (L - 3 * η + 3 * η) := by congr 1; ring
      _ ≤ ENNReal.ofReal (L - 3 * η) + ENNReal.ofReal (3 * η) := ENNReal.ofReal_add_le
      _ ≤ crossingLaplace (s.parameters b hb hb' j) (model j) (i j) E f + η' := by
          refine add_le_add hlow' (le_trans (ENNReal.ofReal_le_ofReal (by linarith)) h5)
  · calc crossingLaplace (s.parameters b hb hb' j) (model j) (i j) E f ≤ ENNReal.ofReal (L + 2 * η) + ENNReal.ofReal ε' :=
          hupp
      _ = ENNReal.ofReal L + ENNReal.ofReal (2 * η + ε') := by
          rw [← ENNReal.ofReal_add (by linarith) hε'.le, ← ENNReal.ofReal_add hL0 (by linarith)]
          congr 1; ring
      _ ≤ ENNReal.ofReal L + η' :=
          add_le_add le_rfl (le_trans (ENNReal.ofReal_le_ofReal (by linarith)) h5)

end BlockBand.Endpoints
