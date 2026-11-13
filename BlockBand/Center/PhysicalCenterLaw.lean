module

public import BlockBand.Center.CenterResidualEnergy
public import BlockBand.Center.PhysicalCenterAnalysis

/-!
# Laws of the simultaneous splitting and of the pair law

* **`pc_isCenterSplitting_of_exact`**: an exact
  simultaneous splitting `S` (`SimultaneousSplitting.IsExact`) carries the edge splitting of
  every edge `g`: `G_g ~ GUE_{2W}(s/(2W))` is independent of `H - G_g = V + Σ_{h ≠ g} G_h`
  (`IsCenterSplitting S.X (S.G g)`). Proof: the `G_h = G_h⁰ + ξ_h I` are mutually independent
  (composition of the independent pairs `(G_h⁰, ξ_h)`), `V ⊥ (G_h)_h`, and
  `pc_indepFun_prodMk_left`.
* **`pc_pair_integral_transfer`** (the pair law does not depend on the extension): for every
  extension carrying the edge-`g` splitting and every Borel `F`, the pair-law integral of
  `F(H - G_g, H)` equals the one on the extension of `pairCenterFamily0`. Proof: the joint law
  of `(split state of H - G_g, G_g)` is `Pω ⊗ GUE`, and `Pω` is unique
  (`rsl_splitting_unique`, deconvolution of the Gaussian pair part).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE BlockBand.QUE.Fourier BlockBand.Model.Construction
open scoped ENNReal NNReal

variable {p : Parameters} {model : p.GaussianRingModel}

theorem pc_measurable_sum_embed {ι : Type*} [MeasurableSpace ι] (s : Finset (ZMod p.n))
    (A : ι → ∀ h : ZMod p.n, PairMatrix p h) (hA : ∀ h, Measurable fun z => A z h) :
    Measurable fun z => ∑ h ∈ s, embedPair p h (A z h) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  simp only [Matrix.sum_apply]
  exact Finset.measurable_sum s fun h _ =>
    BlockBand.Layers.pg_entry ((ctr_measurable_embedPair h).comp (hA h)) x y

/-- **An exact simultaneous splitting carries every edge splitting**. -/
theorem pc_isCenterSplitting_of_exact (S : SimultaneousSplitting p model) (hS : S.IsExact)
    (g : ZMod p.n) : IsCenterSplitting S.X (S.G g) := by
  obtain ⟨hlaw, hdec, hiid, hV⟩ := hS
  have hP : IsProbabilityMeasure S.X.P := csm_isProb_ext S.X
  refine ⟨S.measurable_G g, hlaw g, ?_⟩
  -- the family `(G_h)_h` is mutually independent
  have hcomb : ∀ h : ZMod p.n,
      Measurable (fun x : PairMatrix p h × ℝ => x.1 + ((x.2 : ℝ) : ℂ) • (1 : PairMatrix p h)) := by
    intro h
    refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact (BlockBand.Layers.pg_entry measurable_fst a b).add
      ((Complex.measurable_ofReal.comp measurable_snd).mul measurable_const)
  have hiG : iIndepFun (fun h ω => S.G h ω) S.X.P := by
    have hc := hiid.comp
      (fun h (x : PairMatrix p h × ℝ) => x.1 + ((x.2 : ℝ) : ℂ) • (1 : PairMatrix p h)) hcomb
    convert hc using 1
    funext h ω
    exact (hdec h ω).symm
  set A : S.X.Ω → (∀ h : ↥(Finset.univ.erase g), PairMatrix p h) := fun ω h => S.G h ω with hAdef
  set B : S.X.Ω → (∀ h : ↥({g} : Finset (ZMod p.n)), PairMatrix p h) := fun ω h => S.G h ω
    with hBdef
  have hdisj : Disjoint (Finset.univ.erase g) ({g} : Finset (ZMod p.n)) :=
    Finset.disjoint_singleton_right.mpr (Finset.notMem_erase g Finset.univ)
  have hAB : IndepFun A B S.X.P :=
    hiG.indepFun_finset (Finset.univ.erase g) {g} hdisj S.measurable_G
  set Vf : S.X.Ω → p.SiteMatrix := fun ω => S.X.Hm ω - ∑ h, embedPair p h (S.G h ω) with hVfdef
  have hGm : Measurable (fun ω h => S.G h ω) := measurable_pi_iff.mpr S.measurable_G
  have hVm : Measurable Vf := by
    have h1 := pc_measurable_sum_embed (ι := S.X.Ω) Finset.univ (fun ω h => S.G h ω)
      S.measurable_G
    refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
    exact (BlockBand.Layers.pg_entry S.X.measurable_Hm x y).sub (BlockBand.Layers.pg_entry h1 x y)
  have hAm : Measurable A := measurable_pi_iff.mpr fun h => S.measurable_G h
  have hBm : Measurable B := measurable_pi_iff.mpr fun h => S.measurable_G h
  have hψ : Measurable (fun Y : (∀ h : ZMod p.n, PairMatrix p h) =>
      ((fun h : ↥(Finset.univ.erase g) => Y h), (fun h : ↥({g} : Finset (ZMod p.n)) => Y h))) :=
    (measurable_pi_iff.mpr fun h => measurable_pi_apply _).prodMk
      (measurable_pi_iff.mpr fun h => measurable_pi_apply _)
  have hVAB : IndepFun Vf (fun ω => (A ω, B ω)) S.X.P := hV.comp measurable_id hψ
  have hVA_B := pc_indepFun_prodMk_left hVm hAm hBm hVAB hAB
  set φ1 : p.SiteMatrix × (∀ h : ↥(Finset.univ.erase g), PairMatrix p h) → p.SiteMatrix :=
    fun z => z.1 + ∑ h : ↥(Finset.univ.erase g), embedPair p h (z.2 h) with hφ1def
  have hφ1 : Measurable φ1 := by
    refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
    simp only [hφ1def, Matrix.add_apply, Matrix.sum_apply]
    refine (BlockBand.Layers.pg_entry measurable_fst x y).add
      (Finset.measurable_sum _ fun h _ => ?_)
    exact BlockBand.Layers.pg_entry
      ((ctr_measurable_embedPair (h : ZMod p.n)).comp ((measurable_pi_apply h).comp measurable_snd))
      x y
  set φ2 : (∀ h : ↥({g} : Finset (ZMod p.n)), PairMatrix p h) → PairMatrix p g :=
    fun b => b ⟨g, Finset.mem_singleton_self g⟩
  have hφ2 : Measurable φ2 := measurable_pi_apply _
  have hfin := hVA_B.comp hφ1 hφ2
  have hres : (fun ω => S.X.Hm ω - embedPair p g (S.G g ω)) = φ1 ∘ fun ω => (Vf ω, A ω) := by
    funext ω
    simp only [Function.comp_apply, hφ1def, hVfdef, hAdef]
    rw [Finset.sum_coe_sort (Finset.univ.erase g) (fun h => embedPair p h (S.G h ω)),
      ← Finset.add_sum_erase Finset.univ (fun h => embedPair p h (S.G h ω)) (Finset.mem_univ g)]
    abel
  rw [hres]
  exact hfin

/-- **The pair-law integral does not depend on the extension**: for every extension carrying
the edge-`g` splitting and every Borel `F`, `E♯ F(H - G_g, H)` is the value on the extension of
`pairCenterFamily0`. -/
theorem pc_pair_integral_transfer (α : Fin p.N) (g : ZMod p.n) (X : PairExtension p model)
    {G : X.Ω → PairMatrix p g} (hG : IsCenterSplitting X G)
    (F : p.SiteMatrix × p.SiteMatrix → ℝ) (hF : Measurable F) :
    (∫ ω, F (X.Hm ω - embedPair p g (G ω), X.Hm ω) ∂extendedPairMeasure p α g X.P X.Hm) =
      ∫ ω, F ((ctrExtension p model g).Hm ω - embedPair p g ω.2, (ctrExtension p model g).Hm ω)
        ∂extendedPairMeasure p α g (ctrExtension p model g).P (ctrExtension p model g).Hm := by
  have hP := csm_isProb_ext X
  set w : p.SiteMatrix → ℝ≥0 := physicalPairWeight p α g with hwdef
  have hw : Measurable w := measurable_physicalPairWeight p α g
  set Ψ : SplitState p g × PairMatrix p g → ℝ := fun z =>
    (w (assemble p g z.1 z.2) : ℝ) •
      F (assemble p g z.1 z.2 - embedPair p g z.2, assemble p g z.1 z.2) with hΨdef
  have hasm : Measurable (fun z : SplitState p g × PairMatrix p g => assemble p g z.1 z.2) :=
    BlockBand.Layers.rsl_measurable_assemble g
  have hΨ : Measurable Ψ := by
    have hsub : Measurable (fun z : SplitState p g × PairMatrix p g =>
        assemble p g z.1 z.2 - embedPair p g z.2) := by
      have he : Measurable (fun z : SplitState p g × PairMatrix p g => embedPair p g z.2) :=
        (ctr_measurable_embedPair g).comp measurable_snd
      refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
      exact (BlockBand.Layers.pg_entry hasm x y).sub (BlockBand.Layers.pg_entry he x y)
    exact (measurable_coe_nnreal_real.comp (hw.comp hasm)).smul (hF.comp (hsub.prodMk hasm))
  -- the extension side
  set φ : X.Ω → SplitState p g × PairMatrix p g := fun ω =>
    (BlockBand.Layers.rslUnassemble g (X.Hm ω - embedPair p g (G ω)), G ω) with hφdef
  have hR := csm_measurable_res X hG.1
  have hU : Measurable (fun ω => BlockBand.Layers.rslUnassemble g (X.Hm ω - embedPair p g (G ω))) :=
    (BlockBand.Layers.rsl_measurable_unassemble g).comp hR
  have hφ : Measurable φ := hU.prodMk hG.1
  have hind : IndepFun (fun ω => BlockBand.Layers.rslUnassemble g (X.Hm ω - embedPair p g (G ω)))
      G X.P := hG.2.2.comp (BlockBand.Layers.rsl_measurable_unassemble g) measurable_id
  have hmap : X.P.map φ = (ctrExtension p model g).P := by
    have hprod := (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hG.1.aemeasurable).mp hind
    rw [hφdef, hprod, hG.2.1.map_eq]
    have huniq := BlockBand.Layers.rsl_splitting_unique g (csm_isPairSplitting X hG)
      (ctr_splitLaw_isPairSplitting p model g)
    change (csmSplitLaw X G).prod _ = (ctrSplitLaw p g).prod _
    rw [huniq]
  have hX : (∫ ω, F (X.Hm ω - embedPair p g (G ω), X.Hm ω) ∂extendedPairMeasure p α g X.P X.Hm) =
      ∫ ω, Ψ (φ ω) ∂X.P := by
    unfold extendedPairMeasure
    rw [integral_withDensity_eq_integral_smul (f := fun ω => w (X.Hm ω)) (hw.comp X.measurable_Hm)]
    refine integral_congr_ae ?_
    filter_upwards [csm_ae_good X hG] with ω hω
    have hasm' : assemble p g (BlockBand.Layers.rslUnassemble g (X.Hm ω - embedPair p g (G ω)))
        (G ω) = X.Hm ω := by
      rw [csm_assemble_unassemble hω.2.1, sub_add_cancel]
    simp only [hΨdef, hφdef, hasm']
    rfl
  rw [hX, ← integral_map hφ.aemeasurable hΨ.aestronglyMeasurable, hmap]
  unfold extendedPairMeasure
  rw [integral_withDensity_eq_integral_smul (f := fun ω => w ((ctrExtension p model g).Hm ω))
    (hw.comp (ctrExtension p model g).measurable_Hm)]
  rfl

end BlockBand.Center
