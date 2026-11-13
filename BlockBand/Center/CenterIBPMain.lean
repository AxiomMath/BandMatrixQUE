module

public import BlockBand.Center.PhysicalCenter
public import BlockBand.Center.SmoothCenter
public import BlockBand.Center.CenterIBPSpectral
public import BlockBand.Center.CenterIBPGauss
public import BlockBand.Center.CenterIBPStein
public import BlockBand.Center.CenterIBPLaw
public import BlockBand.Layers.OUCovariance
public import BlockBand.RankLocation.RankLocationLaw

/-!
# The two Gaussian integration-by-parts inputs of the physical center theorem

Main theorems: `pcEnergyPrimitive_holds : PcEnergyPrimitive` and
`pcDivergenceIsometry_holds : PcDivergenceIsometry` (statements in `PhysicalCenter`), with no
hypothesis.

Law: an exact simultaneous splitting `S` (`SimultaneousSplitting.IsExact`) of the exact physical
law, every parameter set. Write `V = H - Σ_g G_g`, `E_k = G_k⁰` (embedded traceless parts) and
`ξ = (ξ_k)_k`. §1 proves that `(V, E)` is independent of `ξ` and that `ξ` is i.i.d.
`N(0, σ²)`, `σ² = s/(2W)²` (`cib_law_decomp`, from the GUE trace/traceless split
`cib_gue_traceless_trace`), with `H = V + Σ_k (E_k + ξ_k P_{S_k})` and
`H - G_g = V + Σ_{k ≠ g} (E_k + ξ_k P_{S_k})` pointwise. §2 fixes one or two coordinates of
`ξ` (Fubini). §3 proves the energy primitive on each section `t ↦ λ_α(M + t P_{S_g})` (monotone,
`1`-Lipschitz, Hellmann–Feynman `∂_t λ_α = q_g` at every parameter with separable characteristic
polynomial, which holds for a.e. `t` on a.e. section by `ae_charpoly_separable`), through the
Lipschitz Stein identity `cib_stein_lipschitz` and the a.e. chain rule `cib_deriv_primitive_ae`
(no simplicity of the spectrum along the whole line is needed). §4 proves the divergence
isometry: the diagonal terms by independence, the off-diagonal terms by one `C¹` Stein identity
in each of `ξ_g`, `ξ_h` on each section (the integrand factorizes since `f_g` does not contain
`ξ_g` and `f_h` does not contain `ξ_h`; no second derivative is used). The `C¹` hypothesis is
used at residuals that are Hermitian, ring-banded and have invertible exterior bonds, which hold
almost surely (`cib_ae_ringBanded`, `cib_ae_bonds_det_ne`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE BlockBand.QUE.Fourier BlockBand.Model.Construction
open scoped ENNReal NNReal Interval

/-!
## 1. The splitting decomposition
-/

section Decomposition

variable {p : Parameters} {model : p.GaussianRingModel}

/-- The variance `σ² = s/(2W)²` of each auxiliary scalar `ξ_g`. -/
def cibVar (p : Parameters) : ℝ≥0 := Real.toNNReal (splitS p / (2 * (p.W : ℝ)) ^ 2)

theorem cib_var_coe : (cibVar p : ℝ) = splitS p / (2 * (p.W : ℝ)) ^ 2 :=
  Real.coe_toNNReal _ (div_nonneg ctr_splitS_pos.le (sq_nonneg _))

theorem cib_var_pos : (0 : ℝ) < cibVar p := by
  rw [cib_var_coe]
  have := pc_W_pos (p := p)
  exact div_pos ctr_splitS_pos (by positivity)

theorem cib_var_ne_zero : cibVar p ≠ 0 := by
  intro h
  have := cib_var_pos (p := p)
  rw [h] at this
  simp at this

theorem cib_var_inv : (2 * (p.W : ℝ)) ^ 2 / splitS p = ((cibVar p : ℝ))⁻¹ := by
  rw [cib_var_coe, inv_div]

instance cib_pairSite_nonempty (g : ZMod p.n) : Nonempty (PairSite p g) :=
  ⟨⟨(g, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩

theorem cib_pairTime_div (g : ZMod p.n) :
    pairTime p (splitS p) / (Fintype.card (PairSite p g) : ℝ≥0) = cibVar p := by
  apply NNReal.coe_injective
  rw [NNReal.coe_div, cib_var_coe, pairTime, Real.coe_toNNReal _
    (div_nonneg ctr_splitS_pos.le (by positivity)), NNReal.coe_natCast, ctr_card_pairSite]
  push_cast
  rw [div_div, sq]

/-- `embedPair` is additive. -/
theorem cib_embedPair_add (g : ZMod p.n) (A B : PairMatrix p g) :
    embedPair p g (A + B) = embedPair p g A + embedPair p g B := by
  ext x y
  simp only [embedPair, Matrix.add_apply]
  split_ifs <;> simp

/-- `embedPair (c I) = c P_{S_g}`. -/
theorem cib_embedPair_smul_one (g : ZMod p.n) (c : ℂ) :
    embedPair p g (c • (1 : PairMatrix p g)) = c • pairProjector p g := by
  ext x y
  simp only [embedPair, pairProjector, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    by_cases h1 : x.1 = g ∨ x.1 = g + 1
    · simp [h1]
    · simp [h1]
  · simp only [hxy, ↓reduceIte]
    by_cases h1 : x.1 = g ∨ x.1 = g + 1
    · by_cases h2 : y.1 = g ∨ y.1 = g + 1
      · have : (⟨x, h1⟩ : PairSite p g) ≠ ⟨y, h2⟩ := fun h => hxy (congrArg Subtype.val h)
        simp [h1, h2, Matrix.one_apply_ne this]
      · simp [h1, h2]
    · simp [h1]

/-- The `(V, E)` part of an exact simultaneous splitting: `V = H - Σ_g G_g` and the embedded
traceless parts `E_k = G_k⁰`. -/
def cibZ (S : SimultaneousSplitting p model) (ω : S.X.Ω) :
    p.SiteMatrix × (ZMod p.n → p.SiteMatrix) :=
  (S.X.Hm ω - ∑ g, embedPair p g (S.G g ω), fun k => embedPair p k (tracelessPart (S.G k ω)))

/-- The auxiliary scalars `ξ = (ξ_k)_k`. -/
def cibXi (S : SimultaneousSplitting p model) (ω : S.X.Ω) : ZMod p.n → ℝ := fun k => S.ξ k ω

variable (p) in
/-- Reassembly `H = V + Σ_k (E_k + x_k P_{S_k})`. -/
def cibAsm (z : p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) (x : ZMod p.n → ℝ) : p.SiteMatrix :=
  z.1 + ∑ k, (z.2 k + ((x k : ℝ) : ℂ) • pairProjector p k)

variable (p) in
/-- The residual `H^{(g)} = V + Σ_{k ≠ g} (E_k + x_k P_{S_k})`. -/
def cibRes (g : ZMod p.n) (z : p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) (x : ZMod p.n → ℝ) :
    p.SiteMatrix :=
  z.1 + ∑ k ∈ Finset.univ.erase g, (z.2 k + ((x k : ℝ) : ℂ) • pairProjector p k)

theorem cib_asm_eq_res (g : ZMod p.n) (z : p.SiteMatrix × (ZMod p.n → p.SiteMatrix))
    (x : ZMod p.n → ℝ) :
    cibAsm p z x = cibRes p g z x + (z.2 g + ((x g : ℝ) : ℂ) • pairProjector p g) := by
  unfold cibAsm cibRes
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ g)]
  abel

theorem cib_res_update_self (g : ZMod p.n) (z : p.SiteMatrix × (ZMod p.n → p.SiteMatrix))
    (x : ZMod p.n → ℝ) (t : ℝ) : cibRes p g z (Function.update x g t) = cibRes p g z x := by
  unfold cibRes
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

theorem cib_res_update_ne {g h : ZMod p.n} (hgh : h ≠ g)
    (z : p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) (x : ZMod p.n → ℝ) (u : ℝ) :
    cibRes p g z (Function.update x h u) =
      cibRes p g z (Function.update x h 0) + ((u : ℝ) : ℂ) • pairProjector p h := by
  unfold cibRes
  have hh : h ∈ Finset.univ.erase g := Finset.mem_erase.mpr ⟨hgh, Finset.mem_univ h⟩
  rw [← Finset.add_sum_erase _ _ hh, ← Finset.add_sum_erase _ _ hh]
  have hrest : ∀ y : ℝ, ∑ k ∈ (Finset.univ.erase g).erase h,
      (z.2 k + ((Function.update x h y k : ℝ) : ℂ) • pairProjector p k) =
      ∑ k ∈ (Finset.univ.erase g).erase h, (z.2 k + ((x k : ℝ) : ℂ) • pairProjector p k) := by
    intro y
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [hrest u, hrest 0]
  simp only [Function.update_self, Complex.ofReal_zero, zero_smul, add_zero]
  abel

theorem cib_asm_update (g : ZMod p.n) (z : p.SiteMatrix × (ZMod p.n → p.SiteMatrix))
    (x : ZMod p.n → ℝ) (t : ℝ) :
    cibAsm p z (Function.update x g t) =
      cibAsm p z (Function.update x g 0) + ((t : ℝ) : ℂ) • pairProjector p g := by
  rw [cib_asm_eq_res g, cib_asm_eq_res g z (Function.update x g 0), cib_res_update_self,
    cib_res_update_self]
  simp only [Function.update_self, Complex.ofReal_zero, zero_smul, add_zero]
  abel

theorem cib_continuous_asm :
    Continuous (fun y : (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) × (ZMod p.n → ℝ) =>
      cibAsm p y.1 y.2) := by
  unfold cibAsm
  fun_prop

theorem cib_continuous_res (g : ZMod p.n) :
    Continuous (fun y : (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) × (ZMod p.n → ℝ) =>
      cibRes p g y.1 y.2) := by
  unfold cibRes
  fun_prop

theorem cib_measurable_asm :
    Measurable (fun y : (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) × (ZMod p.n → ℝ) =>
      cibAsm p y.1 y.2) := by
  refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
  simp only [cibAsm, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine (BlockBand.Layers.pg_entry measurable_fst.fst a b).add
    (Finset.measurable_sum _ fun k _ => ?_)
  exact (BlockBand.Layers.pg_entry ((measurable_pi_apply k).comp measurable_fst.snd) a b).add
    ((Complex.measurable_ofReal.comp ((measurable_pi_apply k).comp measurable_snd)).mul
      measurable_const)

theorem cib_measurable_res (g : ZMod p.n) :
    Measurable (fun y : (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) × (ZMod p.n → ℝ) =>
      cibRes p g y.1 y.2) := by
  refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
  simp only [cibRes, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine (BlockBand.Layers.pg_entry measurable_fst.fst a b).add
    (Finset.measurable_sum _ fun k _ => ?_)
  exact (BlockBand.Layers.pg_entry ((measurable_pi_apply k).comp measurable_fst.snd) a b).add
    ((Complex.measurable_ofReal.comp ((measurable_pi_apply k).comp measurable_snd)).mul
      measurable_const)

end Decomposition

section Exact

variable {p : Parameters} {model : p.GaussianRingModel}

theorem cib_trace_traceless {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (G : Matrix ι ι ℂ) : (tracelessPart G).trace = 0 := by
  unfold tracelessPart
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  have : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

/-- `ξ_g = Re tr G_g / (2W)` (from `G_g = G_g⁰ + ξ_g I`). -/
theorem cib_xi_eq (S : SimultaneousSplitting p model)
    (hdec : ∀ g ω, tracelessPart (S.G g ω) + ((S.ξ g ω : ℝ) : ℂ) • 1 = S.G g ω)
    (g : ZMod p.n) (ω : S.X.Ω) :
    S.ξ g ω = (S.G g ω).trace.re / (Fintype.card (PairSite p g) : ℝ) := by
  have h := congrArg Matrix.trace (hdec g ω)
  rw [Matrix.trace_add, cib_trace_traceless, zero_add, Matrix.trace_smul, Matrix.trace_one,
    smul_eq_mul] at h
  rw [← h]
  have hc : (Fintype.card (PairSite p g) : ℝ) ≠ 0 := by
    exact_mod_cast (ctr_card_pairSite_pos (p := p) (i := g)).ne'
  rw [show ((S.ξ g ω : ℝ) : ℂ) * ((Fintype.card (PairSite p g) : ℕ) : ℂ) =
      (((S.ξ g ω) * (Fintype.card (PairSite p g) : ℝ) : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]
  field_simp

theorem cib_embed_G (S : SimultaneousSplitting p model)
    (hdec : ∀ g ω, tracelessPart (S.G g ω) + ((S.ξ g ω : ℝ) : ℂ) • 1 = S.G g ω)
    (g : ZMod p.n) (ω : S.X.Ω) :
    embedPair p g (S.G g ω) = (cibZ S ω).2 g + ((S.ξ g ω : ℝ) : ℂ) • pairProjector p g := by
  conv_lhs => rw [← hdec g ω]
  rw [cib_embedPair_add, cib_embedPair_smul_one]
  rfl

/-- `H = V + Σ_k (E_k + ξ_k P_{S_k})`. -/
theorem cib_H_eq (S : SimultaneousSplitting p model)
    (hdec : ∀ g ω, tracelessPart (S.G g ω) + ((S.ξ g ω : ℝ) : ℂ) • 1 = S.G g ω) (ω : S.X.Ω) :
    S.X.Hm ω = cibAsm p (cibZ S ω) (cibXi S ω) := by
  have hs : ∑ k, ((cibZ S ω).2 k + ((S.ξ k ω : ℝ) : ℂ) • pairProjector p k) =
      ∑ k, embedPair p k (S.G k ω) :=
    Finset.sum_congr rfl fun k _ => (cib_embed_G S hdec k ω).symm
  simp only [cibAsm, cibXi, hs]
  simp only [cibZ]
  abel

/-- `H - G_g = V + Σ_{k ≠ g} (E_k + ξ_k P_{S_k})`. -/
theorem cib_res_eq (S : SimultaneousSplitting p model)
    (hdec : ∀ g ω, tracelessPart (S.G g ω) + ((S.ξ g ω : ℝ) : ℂ) • 1 = S.G g ω)
    (g : ZMod p.n) (ω : S.X.Ω) :
    S.X.Hm ω - embedPair p g (S.G g ω) = cibRes p g (cibZ S ω) (cibXi S ω) := by
  have h1 := cib_asm_eq_res g (cibZ S ω) (cibXi S ω)
  rw [← cib_H_eq S hdec ω] at h1
  rw [h1, cib_embed_G S hdec g ω]
  simp only [cibXi, add_sub_cancel_right]

theorem cib_measurable_Z (S : SimultaneousSplitting p model) : Measurable (cibZ S) := by
  have hV : Measurable (fun ω => S.X.Hm ω - ∑ g, embedPair p g (S.G g ω)) := by
    have h1 := pc_measurable_sum_embed (ι := S.X.Ω) Finset.univ (fun ω h => S.G h ω)
      S.measurable_G
    refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
    exact (BlockBand.Layers.pg_entry S.X.measurable_Hm x y).sub
      (BlockBand.Layers.pg_entry h1 x y)
  refine hV.prodMk (measurable_pi_iff.mpr fun k => ?_)
  exact (ctr_measurable_embedPair k).comp (cib_measurable_tracelessPart.comp (S.measurable_G k))

theorem cib_measurable_Xi (S : SimultaneousSplitting p model) : Measurable (cibXi S) :=
  measurable_pi_iff.mpr fun k => S.measurable_ξ k

/-- **The splitting decomposition**: under an exact simultaneous splitting, `(V, E)` is
independent of `ξ`, and `ξ` is i.i.d. `N(0, s/(2W)²)`. -/
theorem cib_law_decomp (S : SimultaneousSplitting p model) (hS : S.IsExact) :
    S.X.P.map (fun ω => (cibZ S ω, cibXi S ω)) =
      (S.X.P.map (cibZ S)).prod (Measure.pi fun _ : ZMod p.n => gaussianReal 0 (cibVar p)) := by
  obtain ⟨hlaw, hdec, hiid, hV⟩ := hS
  have hP : IsProbabilityMeasure S.X.P := csm_isProb_ext S.X
  set γ := gaussianReal 0 (cibVar p) with hγ
  have hpair : ∀ k, HasLaw (fun ω => (tracelessPart (S.G k ω), S.ξ k ω))
      (((gueMeasure (PairSite p k) (pairTime p (splitS p))).map tracelessPart).prod γ) S.X.P := by
    intro k
    have hY : HasLaw (fun G : PairMatrix p k =>
        (tracelessPart G, G.trace.re / (Fintype.card (PairSite p k) : ℝ)))
        (((gueMeasure (PairSite p k) (pairTime p (splitS p))).map tracelessPart).prod γ)
        (gueMeasure (PairSite p k) (pairTime p (splitS p))) := by
      refine ⟨(cib_measurable_tracelessPart.prodMk cib_measurable_traceRe).aemeasurable, ?_⟩
      rw [cib_gue_traceless_trace, cib_pairTime_div]
    have := hY.comp (hlaw k)
    convert this using 1
    funext ω
    simp only [Function.comp_apply, cib_xi_eq S hdec k ω]
  have hTlm : ∀ k, Measurable (fun ω => tracelessPart (S.G k ω)) := fun k =>
    cib_measurable_tracelessPart.comp (S.measurable_G k)
  have hEm : ∀ k, Measurable (fun ω => embedPair p k (tracelessPart (S.G k ω))) := fun k =>
    (ctr_measurable_embedPair k).comp (hTlm k)
  have hξlaw : ∀ k, S.X.P.map (S.ξ k) = γ := by
    intro k
    have h := congrArg (fun μ => μ.map Prod.snd) (hpair k).map_eq
    rw [Measure.map_map measurable_snd ((hTlm k).prodMk (S.measurable_ξ k)),
      Measure.map_snd_prod, measure_univ, one_smul] at h
    exact h
  have hTllaw : ∀ k, S.X.P.map (fun ω => tracelessPart (S.G k ω)) =
      (gueMeasure (PairSite p k) (pairTime p (splitS p))).map tracelessPart := by
    intro k
    rw [← (hlaw k).map_eq, Measure.map_map cib_measurable_tracelessPart (S.measurable_G k)]
    rfl
  have hind1 : ∀ k, IndepFun (fun ω => tracelessPart (S.G k ω)) (S.ξ k) S.X.P := by
    intro k
    rw [indepFun_iff_map_prod_eq_prod_map_map (hTlm k).aemeasurable
      (S.measurable_ξ k).aemeasurable, hTllaw k, hξlaw k]
    exact (hpair k).map_eq
  set T : ∀ _ : ZMod p.n, S.X.Ω → p.SiteMatrix × ℝ :=
    fun k ω => (embedPair p k (tracelessPart (S.G k ω)), S.ξ k ω) with hTdef
  have hTm : ∀ k, Measurable (T k) := fun k => (hEm k).prodMk (S.measurable_ξ k)
  have hTlaw : ∀ k, S.X.P.map (T k) =
      (S.X.P.map (fun ω => embedPair p k (tracelessPart (S.G k ω)))).prod γ := by
    intro k
    have h : IndepFun (fun ω => embedPair p k (tracelessPart (S.G k ω))) (S.ξ k) S.X.P :=
      (hind1 k).comp (ctr_measurable_embedPair k) measurable_id
    rw [indepFun_iff_map_prod_eq_prod_map_map (hEm k).aemeasurable
      (S.measurable_ξ k).aemeasurable] at h
    rw [← hξlaw k]
    exact h
  have hiT : iIndepFun T S.X.P := by
    have hc := hiid.comp (fun k (y : PairMatrix p k × ℝ) => (embedPair p k y.1, y.2))
      (fun k => ((ctr_measurable_embedPair k).comp measurable_fst).prodMk measurable_snd)
    exact hc
  have hpi := (iIndepFun_iff_map_fun_eq_pi_map (fun k => (hTm k).aemeasurable)).mp hiT
  simp_rw [hTlaw] at hpi
  -- the joint law of `(E, ξ)`
  set E : S.X.Ω → (ZMod p.n → p.SiteMatrix) :=
    fun ω k => embedPair p k (tracelessPart (S.G k ω)) with hEdef
  have hEm' : Measurable E := measurable_pi_iff.mpr hEm
  have hjoint : S.X.P.map (fun ω => (E ω, cibXi S ω)) =
      (Measure.pi fun k => S.X.P.map (fun ω => embedPair p k (tracelessPart (S.G k ω)))).prod
        (Measure.pi fun _ : ZMod p.n => γ) := by
    have hfun : (fun ω => (E ω, cibXi S ω)) =
        (MeasurableEquiv.arrowProdEquivProdArrow p.SiteMatrix ℝ (ZMod p.n)) ∘
          (fun ω k => T k ω) := by
      funext ω
      rfl
    rw [hfun, ← Measure.map_map (MeasurableEquiv.measurable _)
      (measurable_pi_iff.mpr hTm), hpi]
    exact (measurePreserving_arrowProdEquivProdArrow p.SiteMatrix ℝ (ZMod p.n) _ _).map_eq
  have hEΞ : IndepFun E (cibXi S) S.X.P := by
    have hE : S.X.P.map E =
        Measure.pi fun k => S.X.P.map (fun ω => embedPair p k (tracelessPart (S.G k ω))) := by
      have h := congrArg (fun μ => μ.map Prod.fst) hjoint
      rw [Measure.map_map measurable_fst (hEm'.prodMk (cib_measurable_Xi S)),
        Measure.map_fst_prod, measure_univ, one_smul] at h
      exact h
    have hX : S.X.P.map (cibXi S) = Measure.pi fun _ : ZMod p.n => γ := by
      have h := congrArg (fun μ => μ.map Prod.snd) hjoint
      rw [Measure.map_map measurable_snd (hEm'.prodMk (cib_measurable_Xi S)),
        Measure.map_snd_prod, measure_univ, one_smul] at h
      exact h
    rw [indepFun_iff_map_prod_eq_prod_map_map hEm'.aemeasurable
      (cib_measurable_Xi S).aemeasurable, hE, hX]
    exact hjoint
  -- `V` is independent of `(E, ξ)`
  set Vf : S.X.Ω → p.SiteMatrix := fun ω => S.X.Hm ω - ∑ h, embedPair p h (S.G h ω) with hVfdef
  have hVm : Measurable Vf := (cib_measurable_Z S).fst
  set Φ : (∀ h : ZMod p.n, PairMatrix p h) → (ZMod p.n → p.SiteMatrix) × (ZMod p.n → ℝ) :=
    fun Y => (fun k => embedPair p k (tracelessPart (Y k)),
      fun k => (Y k).trace.re / (Fintype.card (PairSite p k) : ℝ)) with hΦdef
  have hΦ : Measurable Φ := by
    refine (measurable_pi_iff.mpr fun k => ?_).prodMk (measurable_pi_iff.mpr fun k => ?_)
    · exact (ctr_measurable_embedPair k).comp
        (cib_measurable_tracelessPart.comp (measurable_pi_apply k))
    · exact cib_measurable_traceRe.comp (measurable_pi_apply k)
  have hVEX : IndepFun Vf (fun ω => (E ω, cibXi S ω)) S.X.P := by
    have hfun : (fun ω => (E ω, cibXi S ω)) = Φ ∘ (fun ω g => S.G g ω) := by
      funext ω
      exact Prod.ext rfl (funext fun k => cib_xi_eq S hdec k ω)
    rw [hfun]
    exact hV.comp measurable_id hΦ
  have hfin := pc_indepFun_prodMk_left hVm hEm' (cib_measurable_Xi S) hVEX hEΞ
  rw [indepFun_iff_map_prod_eq_prod_map_map (hVm.prodMk hEm').aemeasurable
    (cib_measurable_Xi S).aemeasurable] at hfin
  have hXl : S.X.P.map (cibXi S) = Measure.pi fun _ : ZMod p.n => γ := by
    rw [show cibXi S = (fun ω k => S.ξ k ω) from rfl]
    have hiX : iIndepFun (fun k ω => S.ξ k ω) S.X.P := hiid.comp (fun _ y => y.2)
      (fun _ => measurable_snd)
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun k => (S.measurable_ξ k).aemeasurable)).mp hiX]
    simp_rw [hξlaw]
  rw [hXl] at hfin
  exact hfin

end Exact

/-!
## 2. Fixing coordinates of `ξ`
-/

section Fubini

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type*} [MeasurableSpace α]

omit [Fintype ι] in
theorem cib_measurable_update (g : ι) :
    Measurable (fun q : (α × (ι → ℝ)) × ℝ => (q.1.1, Function.update q.1.2 g q.2)) :=
  measurable_fst.fst.prodMk ((measurable_update' (a := g)).comp
    (measurable_fst.snd.prodMk measurable_snd))

/-- Freezing one Gaussian coordinate: `(μ ⊗ γ^ι) ⊗ γ`, pushed by
`((a, x), t) ↦ (a, x[g ↦ t])`, is `μ ⊗ γ^ι`. -/
theorem cib_map_update (μ : Measure α) [SFinite μ] (v : ℝ≥0) (g : ι) :
    ((μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v)).prod (gaussianReal 0 v)).map
        (fun q => (q.1.1, Function.update q.1.2 g q.2)) =
      μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v) := by
  set π := Measure.pi fun _ : ι => gaussianReal 0 v with hπ
  set γ := gaussianReal 0 v with hγ
  have hU : Measurable (fun q : (ι → ℝ) × ℝ => Function.update q.1 g q.2) :=
    (continuous_fst.update g continuous_snd).measurable
  have h1 : (π.prod γ).map (fun q => Function.update q.1 g q.2) = π := by
    have h := BlockBand.Layers.ou_map_update (fun _ : ι => v) g
    rw [← Measure.prod_swap (μ := γ) (ν := π), Measure.map_map hU measurable_swap]
    exact h
  have hfun : (fun q : (α × (ι → ℝ)) × ℝ => (q.1.1, Function.update q.1.2 g q.2)) =
      (Prod.map id (fun q : (ι → ℝ) × ℝ => Function.update q.1 g q.2)) ∘
        (MeasurableEquiv.prodAssoc : (α × (ι → ℝ)) × ℝ ≃ᵐ α × ((ι → ℝ) × ℝ)) := by
    funext q
    rfl
  rw [hfun, ← Measure.map_map (measurable_id.prodMap hU) MeasurableEquiv.prodAssoc.measurable,
    Measure.prodAssoc_prod, ← Measure.map_prod_map μ (π.prod γ) measurable_id hU, h1,
    Measure.map_id]

theorem cib_integral_update (μ : Measure α) [SFinite μ] (v : ℝ≥0) (g : ι)
    {F : α × (ι → ℝ) → ℝ}
    (hF : AEStronglyMeasurable F (μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v))) :
    ∫ y, F y ∂(μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v)) =
      ∫ q, F (q.1.1, Function.update q.1.2 g q.2)
        ∂((μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v)).prod (gaussianReal 0 v)) := by
  conv_lhs => rw [← cib_map_update μ v g]
  rw [integral_map (cib_measurable_update g).aemeasurable (by rwa [cib_map_update])]

theorem cib_integrable_update (μ : Measure α) [SFinite μ] (v : ℝ≥0) (g : ι)
    {F : α × (ι → ℝ) → ℝ}
    (hF : Integrable F (μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v))) :
    Integrable (fun q => F (q.1.1, Function.update q.1.2 g q.2))
      ((μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v)).prod (gaussianReal 0 v)) := by
  rw [← cib_map_update μ v g] at hF
  exact (integrable_map_measure hF.aestronglyMeasurable
    (cib_measurable_update g).aemeasurable).mp hF

theorem cib_ae_update (μ : Measure α) [SFinite μ] (v : ℝ≥0) (g : ι) {Q : α × (ι → ℝ) → Prop}
    (hQ : ∀ᵐ y ∂(μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v)), Q y) :
    ∀ᵐ q ∂((μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v)).prod (gaussianReal 0 v)),
      Q (q.1.1, Function.update q.1.2 g q.2) := by
  rw [← cib_map_update μ v g] at hQ
  exact ae_of_ae_map (cib_measurable_update g).aemeasurable hQ

end Fubini

/-!
## 3. The energy primitive
-/

section Energy

variable {p : Parameters}

/-- The diagonal of `P_{S_g}`. -/
def cibPairDiag (p : Parameters) (g : ZMod p.n) : p.Site → ℝ :=
  fun x => if x.1 = g ∨ x.1 = g + 1 then 1 else 0

theorem cib_pairDiag_nonneg (g : ZMod p.n) (x : p.Site) : 0 ≤ cibPairDiag p g x := by
  unfold cibPairDiag
  split_ifs <;> norm_num

theorem cib_pairDiag_le_one (g : ZMod p.n) (x : p.Site) : cibPairDiag p g x ≤ 1 := by
  unfold cibPairDiag
  split_ifs <;> norm_num

theorem cib_pairProjector_eq (g : ZMod p.n) : pairProjector p g = cibDiag (cibPairDiag p g) := by
  ext x y
  simp only [pairProjector, cibDiag, cibPairDiag, Matrix.diagonal_apply]
  split_ifs <;> simp

/-- The pair mass is the `P_{S_g}`-weighted mass of the selected eigenvector. -/
theorem cib_pairMass_eq (g : ZMod p.n) (α : Fin p.N) (H : p.SiteMatrix) :
    pairMass p g α H = ∑ x, cibPairDiag p g x * ‖physicalOrderedEigenvector p H α x‖ ^ 2 := by
  unfold pairMass physicalOrderedBlockMass cibPairDiag
  rw [Fintype.sum_prod_type]
  simp only [ite_mul, one_mul, zero_mul]
  have hne : g ≠ g + 1 := (cib_succ_ne g).symm
  have hk : ∀ k : ZMod p.n, (∑ a : Fin p.W, if k = g ∨ k = g + 1 then
      ‖physicalOrderedEigenvector p H α (k, a)‖ ^ 2 else 0) =
      if k = g ∨ k = g + 1 then ∑ a : Fin p.W, ‖physicalOrderedEigenvector p H α (k, a)‖ ^ 2
      else 0 := fun k => by split_ifs <;> simp
  simp_rw [hk]
  rw [← Finset.sum_filter, show Finset.univ.filter (fun k : ZMod p.n => k = g ∨ k = g + 1) =
      {g, g + 1} by ext k; simp, Finset.sum_pair hne]

theorem cib_physicalPairWeight_coe (α : Fin p.N) (g : ZMod p.n) (H : p.SiteMatrix) :
    (physicalPairWeight p α g H : ℝ) = (p.n : ℝ) / 2 * pairMass p g α H := rfl

/-- At a Hermitian matrix with separable characteristic polynomial the pair mass is at most
one. -/
theorem cib_pairMass_le_one (g : ZMod p.n) (α : Fin p.N) {H : p.SiteMatrix}
    (hH : H.IsHermitian) (hsep : H.charpoly.Separable) : pairMass p g α H ≤ 1 := by
  rw [cib_pairMass_eq]
  have hinj := orderedEigenvalue_injective_of_separable ⟨H, hH⟩ hsep
  have h1 := sum_norm_sq_orderedColumnSelection (physicalSpectralRank p α) ⟨H, hH⟩ hinj
  calc ∑ x, cibPairDiag p g x * ‖physicalOrderedEigenvector p H α x‖ ^ 2
      ≤ ∑ x, ‖physicalOrderedEigenvector p H α x‖ ^ 2 :=
        Finset.sum_le_sum fun x _ =>
          mul_le_of_le_one_left (sq_nonneg _) (cib_pairDiag_le_one g x)
    _ = 1 := by
        rw [← h1]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [physicalOrderedEigenvector, rawOrderedColumnSelection_eq _ _ hH]

theorem cib_pairMass_nonneg (g : ZMod p.n) (α : Fin p.N) (H : p.SiteMatrix) :
    0 ≤ pairMass p g α H :=
  add_nonneg (physicalOrderedBlockMass_nonneg p H α g)
    (physicalOrderedBlockMass_nonneg p H α (g + 1))

/-- **The energy primitive on one section** (deterministic `M`, the scalar `t ~ N(0, σ²)`):
for `M` Hermitian, with `M + t P_{S_g}` of separable characteristic polynomial for a.e. `t`,
`E[t ∫_{e₀}^{λ_α(M + t P)} ψ] = σ² E[q_g(M + t P) ψ(λ_α(M + t P))]`. -/
theorem cib_energy_section {M : p.SiteMatrix} (hM : M.IsHermitian) (α : Fin p.N) (g : ZMod p.n)
    {ψ : ℝ → ℝ} (hψ : Measurable ψ) (hψb : ∀ E, |ψ E| ≤ 1) (e₀ : ℝ)
    (hsep : ∀ᵐ t ∂gaussianReal 0 (cibVar p),
      (M + ((t : ℝ) : ℂ) • pairProjector p g).charpoly.Separable) :
    ∫ t, t * (∫ E in e₀..physicalOrderedEigenvalue p (M + ((t : ℝ) : ℂ) • pairProjector p g) α,
        ψ E) ∂gaussianReal 0 (cibVar p) =
      (cibVar p : ℝ) * ∫ t, pairMass p g α (M + ((t : ℝ) : ℂ) • pairProjector p g) *
        ψ (physicalOrderedEigenvalue p (M + ((t : ℝ) : ℂ) • pairProjector p g) α)
        ∂gaussianReal 0 (cibVar p) := by
  set d := cibPairDiag p g with hd
  have hd0 := cib_pairDiag_nonneg (p := p) g
  have hd1 := cib_pairDiag_le_one (p := p) g
  set lam : ℝ → ℝ := fun t =>
    physicalOrderedEigenvalue p (M + ((t : ℝ) : ℂ) • pairProjector p g) α with hlamdef
  have hlam : lam = fun t =>
      rawIncreasingEigenvalue (physicalSpectralRank p α) (M + ((t : ℝ) : ℂ) • cibDiag d) := by
    funext t
    rw [hlamdef, cib_pairProjector_eq]
    rfl
  have hmono : Monotone lam := by
    rw [hlam]
    exact cib_matrix_monotone hM hd0 _
  have hlip : LipschitzWith 1 lam := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [hlam, Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
    exact cib_matrix_lipschitz hM hd0 hd1 _ x y
  set F : ℝ → ℝ := fun t => ∫ E in e₀..lam t, ψ E with hFdef
  have hFlip : LipschitzWith 1 F := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul]
    refine (cib_primitive_abs_sub_le hψ hψb e₀ (lam y) (lam x)).trans ?_
    have := hlip.dist_le_mul x y
    rwa [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at this
  obtain ⟨-, -, hstein⟩ := cib_stein_lipschitz (cibVar p) hFlip
  change ∫ t, t * F t ∂gaussianReal 0 (cibVar p) = _
  rw [hstein]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [cib_deriv_primitive_ae (cibVar p) cib_var_ne_zero hmono hlip hψ hψb e₀, hsep]
    with t ht hs
  rw [ht]
  have hs' : (M + ((t : ℝ) : ℂ) • cibDiag d).charpoly.Separable := by
    rwa [← cib_pairProjector_eq]
  have hHF := cib_matrix_hasDerivAt hM hd0 hd1 (physicalSpectralRank p α) t hs'
  rw [← hlam] at hHF
  rw [hHF.deriv, cib_pairMass_eq, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [physicalOrderedEigenvector, cib_pairProjector_eq]

end Energy

/-!
### Measurability and moments
-/

section Aux

variable {p : Parameters}

/-- The energy primitive `(x, b) ↦ ∫_{e₀}^{b} Ψ(x, E) dE` of a jointly Borel `Ψ` is Borel. -/
theorem cib_measurable_primitive {β : Type*} [MeasurableSpace β] {Ψ : β → ℝ → ℝ}
    (hΨ : Measurable (fun x : β × ℝ => Ψ x.1 x.2)) (e₀ : ℝ) :
    Measurable (fun x : β × ℝ => ∫ E in e₀..x.2, Ψ x.1 E) := by
  have hset : ∀ lo hi : β × ℝ → ℝ, Measurable lo → Measurable hi →
      Measurable (fun x : β × ℝ => ∫ E in Set.Ioc (lo x) (hi x), Ψ x.1 E) := by
    intro lo hi hlo hhi
    have heq : (fun x : β × ℝ => ∫ E in Set.Ioc (lo x) (hi x), Ψ x.1 E) =
        fun x => ∫ E, (fun q : (β × ℝ) × ℝ =>
          if lo q.1 < q.2 ∧ q.2 ≤ hi q.1 then Ψ q.1.1 q.2 else 0) (x, E) := by
      funext x
      rw [← integral_indicator measurableSet_Ioc]
      congr 1
      funext E
      simp only [Set.indicator_apply, Set.mem_Ioc]
    rw [heq]
    have hG : Measurable (fun q : (β × ℝ) × ℝ =>
        if lo q.1 < q.2 ∧ q.2 ≤ hi q.1 then Ψ q.1.1 q.2 else 0) := by
      refine Measurable.ite ?_ (hΨ.comp (measurable_fst.fst.prodMk measurable_snd))
        measurable_const
      exact (measurableSet_lt (hlo.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hhi.comp measurable_fst))
    exact (hG.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  have h1 := hset (fun _ => e₀) (fun x => x.2) measurable_const measurable_snd
  have h2 := hset (fun x => x.2) (fun _ => e₀) measurable_snd measurable_const
  exact h1.sub h2

/-- `λ_α ∈ L²` under the exact physical law (`rkl_moment_le`, `r = 1`, `e = 0`). -/
theorem cib_integrable_eig_sq (model : p.GaussianRingModel) (α : Fin p.N) :
    Integrable (fun H => physicalOrderedEigenvalue p H α ^ 2) (model.law : Measure p.SiteMatrix) := by
  obtain ⟨K, -, hK⟩ := BlockBand.RankLocation.rkl_moment_le 1 le_rfl
  refine ⟨((measurable_physicalOrderedEigenvalue p α).pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun H => sq_nonneg _)]
  refine lt_of_le_of_lt (le_of_eq ?_) ((hK p model α 0 (by norm_num)).trans_lt ENNReal.ofReal_lt_top)
  congr 1
  funext H
  rw [sub_zero, mul_one, sq_abs]

theorem cib_integrable_sq_gauss (v : ℝ≥0) : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
  (memLp_id_gaussianReal' 2 (by simp)).integrable_sq

theorem cib_integrable_coord_sq {ι : Type} [Fintype ι] (v : ℝ≥0) (g : ι) :
    Integrable (fun x : ι → ℝ => x g ^ 2) (Measure.pi fun _ : ι => gaussianReal 0 v) := by
  have h := (measurePreserving_eval (fun _ : ι => gaussianReal 0 v) g).map_eq
  have hi := cib_integrable_sq_gauss v
  rw [← h] at hi
  exact (integrable_map_measure hi.aestronglyMeasurable (measurable_pi_apply g).aemeasurable).mp hi

theorem cib_smul_proj_isHermitian (t : ℝ) (g : ZMod p.n) :
    (((t : ℝ) : ℂ) • pairProjector p g).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_smul, cib_pairProjector_eq, cib_diag_conjTranspose, Complex.star_def,
    Complex.conj_ofReal]

theorem cib_primitive_abs_le {ψ : ℝ → ℝ} (hψ : Measurable ψ) (hψb : ∀ E, |ψ E| ≤ 1)
    (e₀ b : ℝ) : |∫ E in e₀..b, ψ E| ≤ |b| + |e₀| := by
  have h := cib_primitive_abs_sub_le hψ hψb e₀ e₀ b
  rw [intervalIntegral.integral_same, sub_zero] at h
  exact h.trans (abs_sub _ _)

end Aux

/-!
### `pcEnergyPrimitive_holds`
-/

/-- **`PcEnergyPrimitive`** (the per-edge Gaussian integration by parts with Hellmann–Feynman
behind the energy primitive identity), with no hypothesis. -/
theorem pcEnergyPrimitive_holds : PcEnergyPrimitive := by
  intro p model S hS α g Ψ hΨm hΨb e₀
  have hP : IsProbabilityMeasure S.X.P := csm_isProb_ext S.X
  have hdec := hS.2.1
  set γ := gaussianReal 0 (cibVar p) with hγ
  set π := Measure.pi fun _ : ZMod p.n => γ with hπ
  set μZ := S.X.P.map (cibZ S) with hμZ
  set ν := μZ.prod π with hν
  set ZX : S.X.Ω → (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) × (ZMod p.n → ℝ) :=
    fun ω => (cibZ S ω, cibXi S ω) with hZXdef
  have hZX : Measurable ZX := (cib_measurable_Z S).prodMk (cib_measurable_Xi S)
  have hlaw : S.X.P.map ZX = ν := cib_law_decomp S hS
  have hlawH : ν.map (fun y => cibAsm p y.1 y.2) = (model.law : Measure p.SiteMatrix) := by
    rw [← hlaw, Measure.map_map cib_measurable_asm hZX, ← S.X.map_eq]
    congr 1
    funext ω
    exact (cib_H_eq S hdec ω).symm
  set Λf : (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) × (ZMod p.n → ℝ) → ℝ :=
    fun y => physicalOrderedEigenvalue p (cibAsm p y.1 y.2) α with hΛf
  have hΛm : Measurable Λf := (measurable_physicalOrderedEigenvalue p α).comp cib_measurable_asm
  set Lf : (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) × (ZMod p.n → ℝ) → ℝ := fun y =>
    (physicalPairWeight p α g (cibAsm p y.1 y.2) : ℝ) * Ψ (cibRes p g y.1 y.2) (Λf y) with hLf
  set Rf : (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) × (ZMod p.n → ℝ) → ℝ := fun y =>
    y.2 g * ∫ E in e₀..Λf y, Ψ (cibRes p g y.1 y.2) E with hRf
  have hLm : Measurable Lf :=
    (measurable_coe_nnreal_real.comp ((measurable_physicalPairWeight p α g).comp
      cib_measurable_asm)).mul (hΨm.comp ((cib_measurable_res g).prodMk hΛm))
  have hRm : Measurable Rf := by
    have h1 : Measurable (fun y : (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) × (ZMod p.n → ℝ) =>
        y.2 g) := (measurable_pi_apply g).comp measurable_snd
    have h0 := cib_measurable_primitive hΨm e₀
    have h3 := (cib_measurable_res g).prodMk hΛm
    have h2 := h0.comp h3
    exact h1.mul h2
  have hΨE : ∀ R, Measurable (fun E => Ψ R E) := fun R =>
    hΨm.comp (measurable_const.prodMk measurable_id)
  -- the almost-sure good set
  have hgood : ∀ᵐ y ∂ν, (cibAsm p y.1 y.2).IsHermitian ∧
      (cibAsm p y.1 y.2).charpoly.Separable := by
    have hgoodH : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
        H.IsHermitian ∧ H.charpoly.Separable :=
      model.isPhysical.1.and model.ae_charpoly_separable
    rw [← hlawH] at hgoodH
    exact ae_of_ae_map cib_measurable_asm.aemeasurable hgoodH
  -- integrability on the product space
  have hLint : Integrable Lf ν := by
    refine Integrable.of_bound hLm.aestronglyMeasurable ((p.n : ℝ) / 2) ?_
    filter_upwards [hgood] with y hy
    rw [Real.norm_eq_abs, abs_mul, cib_physicalPairWeight_coe]
    have hm0 := cib_pairMass_nonneg g α (cibAsm p y.1 y.2)
    have hm1 := cib_pairMass_le_one g α hy.1 hy.2
    have hn : (0 : ℝ) ≤ (p.n : ℝ) / 2 := by positivity
    rw [abs_of_nonneg (mul_nonneg hn hm0)]
    have hb := hΨb (cibRes p g y.1 y.2) (Λf y)
    calc (p.n : ℝ) / 2 * pairMass p g α (cibAsm p y.1 y.2) * |Ψ (cibRes p g y.1 y.2) (Λf y)|
        ≤ (p.n : ℝ) / 2 * 1 * 1 := by gcongr
      _ = (p.n : ℝ) / 2 := by ring
  have hRint : Integrable Rf ν := by
    have hx : Integrable (fun y : (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) × (ZMod p.n → ℝ) =>
        y.2 g ^ 2) ν := (cib_integrable_coord_sq (cibVar p) g).comp_snd μZ
    have hl : Integrable (fun y => Λf y ^ 2) ν := by
      have h := cib_integrable_eig_sq model α
      rw [← hlawH] at h
      exact (integrable_map_measure h.aestronglyMeasurable
        cib_measurable_asm.aemeasurable).mp h
    refine Integrable.mono' ((hx.add hl).add (integrable_const (e₀ ^ 2)))
      hRm.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    have hb := cib_primitive_abs_le (hΨE (cibRes p g y.1 y.2)) (hΨb _) e₀ (Λf y)
    rw [Real.norm_eq_abs, abs_mul]
    have h0 : 0 ≤ |y.2 g| := abs_nonneg _
    calc |y.2 g| * |∫ E in e₀..Λf y, Ψ (cibRes p g y.1 y.2) E|
        ≤ |y.2 g| * (|Λf y| + |e₀|) := mul_le_mul_of_nonneg_left hb h0
      _ ≤ y.2 g ^ 2 + Λf y ^ 2 + e₀ ^ 2 := by
          nlinarith [sq_nonneg (|y.2 g| - |Λf y|), sq_nonneg (|y.2 g| - |e₀|), sq_abs (y.2 g),
            sq_abs (Λf y), sq_abs e₀]
  -- the two sides as integrals over the product space
  have hLω : ∀ ω, physicalPairWeight p α g (S.X.Hm ω) •
      Ψ (S.X.Hm ω - embedPair p g (S.G g ω)) (physicalOrderedEigenvalue p (S.X.Hm ω) α) =
      Lf (ZX ω) := by
    intro ω
    rw [cib_res_eq S hdec g ω, cib_H_eq S hdec ω, NNReal.smul_def, smul_eq_mul]
  have hRω : ∀ ω, S.ξ g ω * (∫ E in e₀..physicalOrderedEigenvalue p (S.X.Hm ω) α,
      Ψ (S.X.Hm ω - embedPair p g (S.G g ω)) E) = Rf (ZX ω) := by
    intro ω
    rw [cib_res_eq S hdec g ω, cib_H_eq S hdec ω]
    rfl
  have hRintP : Integrable (fun ω => Rf (ZX ω)) S.X.P := by
    rw [← hlaw] at hRint
    exact (integrable_map_measure hRint.aestronglyMeasurable hZX.aemeasurable).mp hRint
  refine ⟨by simpa only [hRω] using hRintP, ?_⟩
  have hLHS : (∫ ω, Ψ (S.X.Hm ω - embedPair p g (S.G g ω))
      (physicalOrderedEigenvalue p (S.X.Hm ω) α) ∂extendedPairMeasure p α g S.X.P S.X.Hm) =
      ∫ q, Lf (q.1.1, Function.update q.1.2 g q.2) ∂(ν.prod γ) := by
    unfold extendedPairMeasure
    rw [integral_withDensity_eq_integral_smul (f := fun ω => physicalPairWeight p α g (S.X.Hm ω))
      ((measurable_physicalPairWeight p α g).comp S.X.measurable_Hm)]
    simp_rw [hLω]
    rw [← integral_map hZX.aemeasurable hLm.aestronglyMeasurable, hlaw]
    exact cib_integral_update μZ (cibVar p) g hLm.aestronglyMeasurable
  have hRHS : (∫ ω, S.ξ g ω * (∫ E in e₀..physicalOrderedEigenvalue p (S.X.Hm ω) α,
      Ψ (S.X.Hm ω - embedPair p g (S.G g ω)) E) ∂S.X.P) =
      ∫ q, Rf (q.1.1, Function.update q.1.2 g q.2) ∂(ν.prod γ) := by
    simp_rw [hRω]
    rw [← integral_map hZX.aemeasurable hRm.aestronglyMeasurable, hlaw]
    exact cib_integral_update μZ (cibVar p) g hRm.aestronglyMeasurable
  rw [hLHS, hRHS, integral_prod _ (cib_integrable_update μZ (cibVar p) g hLint),
    integral_prod _ (cib_integrable_update μZ (cibVar p) g hRint), cib_var_inv,
    ← integral_const_mul]
  -- the section identity
  refine integral_congr_ae ?_
  have h3 := Measure.ae_ae_of_ae_prod (cib_ae_update μZ (cibVar p) g hgood)
  filter_upwards [h3] with q0 hq0
  set M := cibAsm p q0.1 (Function.update q0.2 g 0) with hMdef
  set R := cibRes p g q0.1 q0.2 with hRdef
  have hline : ∀ t, cibAsm p q0.1 (Function.update q0.2 g t) =
      M + ((t : ℝ) : ℂ) • pairProjector p g := fun t => cib_asm_update g q0.1 q0.2 t
  have hres : ∀ t, cibRes p g q0.1 (Function.update q0.2 g t) = R := fun t =>
    cib_res_update_self g q0.1 q0.2 t
  have hM : M.IsHermitian := by
    obtain ⟨t, ht⟩ := hq0.exists
    have h1 := ht.1
    rw [hline] at h1
    have := h1.sub (cib_smul_proj_isHermitian (p := p) t g)
    rwa [add_sub_cancel_right] at this
  have hsep : ∀ᵐ t ∂γ, (M + ((t : ℝ) : ℂ) • pairProjector p g).charpoly.Separable :=
    hq0.mono fun t ht => by rw [← hline]; exact ht.2
  have key := cib_energy_section hM α g (hΨE R) (hΨb R) e₀ hsep
  have hL' : (fun t => Lf (q0.1, Function.update q0.2 g t)) = fun t =>
      (p.n : ℝ) / 2 * (pairMass p g α (M + ((t : ℝ) : ℂ) • pairProjector p g) *
        Ψ R (physicalOrderedEigenvalue p (M + ((t : ℝ) : ℂ) • pairProjector p g) α)) := by
    funext t
    simp only [hLf, hΛf, hline, hres, cib_physicalPairWeight_coe]
    ring
  have hR' : (fun t => Rf (q0.1, Function.update q0.2 g t)) = fun t =>
      t * ∫ E in e₀..physicalOrderedEigenvalue p (M + ((t : ℝ) : ℂ) • pairProjector p g) α,
        Ψ R E := by
    funext t
    simp only [hRf, hΛf, hline, hres, Function.update_self]
  rw [hL', hR', integral_const_mul, key]
  have hv := cib_var_pos (p := p)
  field_simp

/-!
## 4. The divergence isometry
-/

/-!
### Generic second moments on the product space
-/

section DivergenceGeneric

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type*} [MeasurableSpace α]

theorem cib_integral_sq_gauss (v : ℝ≥0) : ∫ x, x ^ 2 ∂gaussianReal 0 v = v := by
  have h := variance_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simpa [integral_id_gaussianReal] using h

/-- Freezing two coordinates `g` (inner) and `h` (outer). -/
theorem cib_integral_update2 (μ : Measure α) [IsProbabilityMeasure μ] (v : ℝ≥0) (g h : ι)
    {G : α × (ι → ℝ) → ℝ}
    (hG : Integrable G (μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v))) :
    ∫ y, G y ∂(μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v)) =
      ∫ q, ∫ u, ∫ t, G (q.1, Function.update (Function.update q.2 h u) g t)
        ∂gaussianReal 0 v ∂gaussianReal 0 v
        ∂(μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v)) := by
  set ν := μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v) with hν
  have h1 := cib_integrable_update μ v g hG
  rw [cib_integral_update μ v g hG.aestronglyMeasurable, integral_prod _ h1]
  set I : α × (ι → ℝ) → ℝ := fun q => ∫ t, G (q.1, Function.update q.2 g t) ∂gaussianReal 0 v
    with hI
  have hIi : Integrable I ν := h1.integral_prod_left
  rw [cib_integral_update μ v h hIi.aestronglyMeasurable,
    integral_prod _ (cib_integrable_update μ v h hIi)]

/-- **Diagonal term**: if `K` does not depend on the coordinate `g`, then
`E[x_g² K] = σ² E K`. -/
theorem cib_diag_moment (μ : Measure α) [IsProbabilityMeasure μ] (v : ℝ≥0) (g : ι)
    {K : α × (ι → ℝ) → ℝ} (hK : Measurable K) {C : ℝ} (hKb : ∀ y, |K y| ≤ C)
    (hKg : ∀ z x t, K (z, Function.update x g t) = K (z, x)) :
    ∫ y, y.2 g ^ 2 * K y ∂(μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v)) =
      (v : ℝ) * ∫ y, K y ∂(μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v)) := by
  set ν := μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v) with hν
  have hx := ((cib_integrable_coord_sq v g).comp_snd μ).const_mul C
  have hF : Integrable (fun y : α × (ι → ℝ) => y.2 g ^ 2 * K y) ν := by
    refine Integrable.mono' hx
      ((((measurable_pi_apply g).comp measurable_snd).pow_const 2).mul hK).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hKb y) (sq_nonneg _)
  have hKi : Integrable K ν :=
    Integrable.of_bound hK.aestronglyMeasurable C (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]; exact hKb y)
  rw [cib_integral_update μ v g hF.aestronglyMeasurable,
    integral_prod _ (cib_integrable_update μ v g hF),
    cib_integral_update μ v g hKi.aestronglyMeasurable,
    integral_prod _ (cib_integrable_update μ v g hKi), ← integral_const_mul]
  congr 1
  funext q
  simp only [Function.update_self, hKg]
  rw [integral_mul_const, cib_integral_sq_gauss, integral_const]
  simp

/-- **Off-diagonal term** (two one-dimensional Stein identities on each section): if `A, A'` do
not depend on the coordinate `g`, `B, B'` do not depend on the coordinate `h ≠ g`, and on a.e.
section `A` (resp. `B`) is differentiable along `h` (resp. `g`) with derivative `A'` (resp.
`B'`), then `E[x_g x_h A B] = σ⁴ E[A' B']`. -/
theorem cib_offdiag_moment (μ : Measure α) [IsProbabilityMeasure μ] (v : ℝ≥0) {g h : ι}
    (hgh : g ≠ h) {A B A' B' : α × (ι → ℝ) → ℝ} (hA : Measurable A) (hB : Measurable B)
    (hAb : ∀ y, |A y| ≤ 1) (hBb : ∀ y, |B y| ≤ 1)
    (hAg : ∀ z x t, A (z, Function.update x g t) = A (z, x))
    (hA'g : ∀ z x t, A' (z, Function.update x g t) = A' (z, x))
    (hBh : ∀ z x t, B (z, Function.update x h t) = B (z, x))
    (hB'h : ∀ z x t, B' (z, Function.update x h t) = B' (z, x))
    (hAd : ∀ᵐ q ∂(μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v)), ∀ u,
      HasDerivAt (fun u => A (q.1, Function.update q.2 h u)) (A' (q.1, Function.update q.2 h u)) u)
    (hBd : ∀ᵐ q ∂(μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v)), ∀ t,
      HasDerivAt (fun t => B (q.1, Function.update q.2 g t)) (B' (q.1, Function.update q.2 g t)) t)
    (hA'i : Integrable A' (μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v)))
    (hB'i : Integrable B' (μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v)))
    (hT : Integrable (fun y => A' y * B' y) (μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v))) :
    ∫ y, y.2 g * y.2 h * A y * B y ∂(μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v)) =
      (v : ℝ) ^ 2 * ∫ y, A' y * B' y ∂(μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v)) := by
  set ν := μ.prod (Measure.pi fun _ : ι => gaussianReal 0 v) with hν
  have hxg := (cib_integrable_coord_sq v g).comp_snd μ
  have hxh := (cib_integrable_coord_sq v h).comp_snd μ
  have hF : Integrable (fun y : α × (ι → ℝ) => y.2 g * y.2 h * A y * B y) ν := by
    refine Integrable.mono' (hxg.add hxh)
      (((((measurable_pi_apply g).comp measurable_snd).mul
        ((measurable_pi_apply h).comp measurable_snd)).mul hA).mul hB).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have h1 := hAb y
    have h2 := hBb y
    have h3 : |y.2 g| * |y.2 h| ≤ y.2 g ^ 2 + y.2 h ^ 2 := by
      nlinarith [sq_nonneg (|y.2 g| - |y.2 h|), sq_abs (y.2 g), sq_abs (y.2 h),
        abs_nonneg (y.2 g), abs_nonneg (y.2 h)]
    have h4 : |A y| * |B y| ≤ 1 := by
      nlinarith [abs_nonneg (A y), abs_nonneg (B y)]
    calc |y.2 g| * |y.2 h| * |A y| * |B y| = (|y.2 g| * |y.2 h|) * (|A y| * |B y|) := by ring
      _ ≤ (y.2 g ^ 2 + y.2 h ^ 2) * 1 := by gcongr
      _ = y.2 g ^ 2 + y.2 h ^ 2 := by ring
  rw [cib_integral_update2 μ v g h hF, cib_integral_update2 μ v g h hT, ← integral_const_mul]
  have hAi := (cib_integrable_update μ v h hA'i).prod_right_ae
  have hBi := (cib_integrable_update μ v g hB'i).prod_right_ae
  refine integral_congr_ae ?_
  filter_upwards [hAd, hBd, hAi, hBi] with q hqA hqB hqAi hqBi
  set a : ℝ → ℝ := fun u => A (q.1, Function.update q.2 h u) with ha
  set a' : ℝ → ℝ := fun u => A' (q.1, Function.update q.2 h u) with ha'
  set b : ℝ → ℝ := fun t => B (q.1, Function.update q.2 g t) with hb
  set b' : ℝ → ℝ := fun t => B' (q.1, Function.update q.2 g t) with hb'
  have hev : ∀ u t, Function.update (Function.update q.2 h u) g t g = t := fun u t =>
    Function.update_self _ _ _
  have hev' : ∀ u t, Function.update (Function.update q.2 h u) g t h = u := fun u t => by
    rw [Function.update_of_ne hgh.symm, Function.update_self]
  have hAe : ∀ u t, A (q.1, Function.update (Function.update q.2 h u) g t) = a u := fun u t =>
    hAg _ _ _
  have hA'e : ∀ u t, A' (q.1, Function.update (Function.update q.2 h u) g t) = a' u := fun u t =>
    hA'g _ _ _
  have hBe : ∀ u t, B (q.1, Function.update (Function.update q.2 h u) g t) = b t := fun u t => by
    rw [Function.update_comm hgh.symm]
    exact hBh _ _ _
  have hB'e : ∀ u t, B' (q.1, Function.update (Function.update q.2 h u) g t) = b' t :=
    fun u t => by
      rw [Function.update_comm hgh.symm]
      exact hB'h _ _ _
  simp_rw [hev, hev', hAe, hA'e, hBe, hB'e]
  have hL : ∀ u, ∫ t, t * u * a u * b t ∂gaussianReal 0 v = (u * a u) * ∫ t, t * b t ∂gaussianReal 0 v := fun u => by
    rw [← integral_const_mul]
    congr 1
    funext t
    ring
  have hR : ∀ u, ∫ t, a' u * b' t ∂gaussianReal 0 v = a' u * ∫ t, b' t ∂gaussianReal 0 v := fun u => integral_const_mul _ _
  simp only [hL, hR]
  rw [integral_mul_const, integral_mul_const]
  -- the two Stein identities
  have hacont : Continuous a := continuous_iff_continuousAt.mpr fun u => (hqA u).continuousAt
  have hbcont : Continuous b := continuous_iff_continuousAt.mpr fun t => (hqB t).continuousAt
  have hai : Integrable a (gaussianReal 0 v) := Integrable.of_bound hacont.aestronglyMeasurable 1
    (ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact hAb _)
  have hbi : Integrable b (gaussianReal 0 v) := Integrable.of_bound hbcont.aestronglyMeasurable 1
    (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact hBb _)
  have h1 : Integrable (fun x : ℝ => |x|) (gaussianReal 0 v) :=
    ((memLp_id_gaussianReal' 1 (by simp)).integrable le_rfl).abs
  have hxa : Integrable (fun u => u * a u) (gaussianReal 0 v) := by
    refine Integrable.mono' h1 (continuous_id.mul hacont).aestronglyMeasurable
      (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hAb _)
  have hxb : Integrable (fun t => t * b t) (gaussianReal 0 v) := by
    refine Integrable.mono' h1 (continuous_id.mul hbcont).aestronglyMeasurable
      (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hBb _)
  have hSa := centered_gaussian_integration_by_parts v hqA hai hqAi hxa
  have hSb := centered_gaussian_integration_by_parts v hqB hbi hqBi hxb
  rw [hSa, hSb]
  ring

end DivergenceGeneric

/-!
### Residual regularity and shift derivatives on the product space
-/

section DivergenceSpecific

variable {p : Parameters}

variable (p) in
/-- The residual regularity used by the `C¹` hypothesis of `PcDivergenceIsometry`. -/
def cibGoodRes (g : ZMod p.n) (M : p.SiteMatrix) : Prop :=
  M.IsHermitian ∧ IsRingBanded p M ∧ ExteriorBondsInvertible p g M

variable (p) in
/-- Hermitian matrices supported on the pair block `S_g × S_g`. -/
def cibAset (g : ZMod p.n) : Set p.SiteMatrix :=
  {M | M.IsHermitian ∧ M = embedPair p g (pairBlock p g M)}

theorem cib_measurable_pairBlock (g : ZMod p.n) : Measurable (pairBlock p g) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  exact BlockBand.Layers.pg_entry measurable_id x.1 y.1

theorem cib_measurableSet_Aset (g : ZMod p.n) : MeasurableSet (cibAset p g) := by
  have h1 : MeasurableSet {M : p.SiteMatrix | M.IsHermitian} :=
    (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
  have h2 : MeasurableSet {M : p.SiteMatrix | M = embedPair p g (pairBlock p g M)} := by
    have heq : {M : p.SiteMatrix | M = embedPair p g (pairBlock p g M)} =
        ⋂ x, ⋂ y, {M : p.SiteMatrix | M x y = embedPair p g (pairBlock p g M) x y} := by
      ext M
      simp only [Set.mem_iInter]
      exact Matrix.ext_iff.symm
    rw [heq]
    refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => ?_
    exact measurableSet_eq_fun (BlockBand.Layers.pg_entry measurable_id x y)
      (BlockBand.Layers.pg_entry ((ctr_measurable_embedPair g).comp
        (cib_measurable_pairBlock g)) x y)
  exact h1.inter h2

theorem cib_traceless_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ}
    (hG : G.IsHermitian) : (tracelessPart G).IsHermitian := by
  unfold tracelessPart
  refine hG.sub ?_
  have htr : star G.trace = G.trace := by rw [← Matrix.trace_conjTranspose, hG.eq]
  unfold Matrix.IsHermitian
  rw [conjTranspose_smul, conjTranspose_one, star_mul', htr, star_inv₀, star_natCast]

theorem cib_embedPair_isHermitian {g : ZMod p.n} {G : PairMatrix p g} (hG : G.IsHermitian) :
    (embedPair p g G).IsHermitian := by
  ext x y
  simp only [conjTranspose_apply, embedPair]
  by_cases hx : x.1 = g ∨ x.1 = g + 1 <;> by_cases hy : y.1 = g ∨ y.1 = g + 1 <;>
    simp [hx, hy, hG.apply]

theorem cib_pairBlock_embedPair (g : ZMod p.n) (G : PairMatrix p g) :
    pairBlock p g (embedPair p g G) = G := by
  ext x y
  simp [pairBlock, embedPair, x.2, y.2]

/-- Regularity of the residual from that of `H` and of the pair block `E_g`. -/
theorem cib_goodRes_of (g : ZMod p.n) (y : (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) ×
    (ZMod p.n → ℝ)) (hH : (cibAsm p y.1 y.2).IsHermitian) (hB : CsmBondGood (cibAsm p y.1 y.2))
    (hE : y.1.2 g ∈ cibAset p g) : cibGoodRes p g (cibRes p g y.1 y.2) := by
  have hR0 : cibRes p g y.1 y.2 =
      cibAsm p y.1 y.2 - (y.1.2 g + ((y.2 g : ℝ) : ℂ) • pairProjector p g) := by
    rw [cib_asm_eq_res g, add_sub_cancel_right]
  have hR : cibRes p g y.1 y.2 = cibAsm p y.1 y.2 -
      embedPair p g (pairBlock p g (y.1.2 g) + ((y.2 g : ℝ) : ℂ) • 1) := by
    rw [cib_embedPair_add, cib_embedPair_smul_one, ← hE.2, hR0]
  refine ⟨?_, ?_, ?_⟩
  · rw [hR0]
    exact hH.sub (hE.1.add (cib_smul_proj_isHermitian _ g))
  · rw [hR]
    exact sc_band_res hB.1 g _
  · rw [hR]
    exact sc_bonds_res hB.2 g _

variable (p) in
/-- The shift derivative `∂_{ξ_h} Ψ_g = ∂_t Ψ_g(H^{(g)} + t P_{S_h})|_{t=0}` on the product
space. -/
def cibD (Ψ : ZMod p.n → p.SiteMatrix → ℝ) (g h : ZMod p.n)
    (y : (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) × (ZMod p.n → ℝ)) : ℝ :=
  deriv (fun t : ℝ => Ψ g (cibRes p g y.1 y.2 + ((t : ℝ) : ℂ) • pairProjector p h)) 0

/-- The `C¹` hypothesis restricted to one shift direction. -/
theorem cib_line_contDiff {Φ : p.SiteMatrix → ℝ} {H₀ : p.SiteMatrix}
    (hC : ContDiff ℝ 1 (fun x : ZMod p.n → ℝ => Φ (H₀ + ∑ k, (x k : ℂ) • pairProjector p k)))
    (h : ZMod p.n) : ContDiff ℝ 1 (fun t : ℝ => Φ (H₀ + ((t : ℝ) : ℂ) • pairProjector p h)) := by
  have hl : ContDiff ℝ 1 (fun t : ℝ => (Pi.single h t : ZMod p.n → ℝ)) := by
    refine contDiff_pi.mpr fun k => ?_
    by_cases hk : k = h
    · subst hk
      simp only [Pi.single_eq_same]
      exact contDiff_id
    · simp only [Pi.single_apply, hk, ite_false]
      exact contDiff_const
  have hcomp := hC.comp hl
  convert hcomp using 1
  funext t
  simp only [Function.comp_apply]
  rw [sc_sum_single]

theorem cib_measurable_shift (g h : ZMod p.n) (t : ℝ) :
    Measurable (fun y : (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) × (ZMod p.n → ℝ) =>
      cibRes p g y.1 y.2 + ((t : ℝ) : ℂ) • pairProjector p h) := by
  refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
  simp only [Matrix.add_apply]
  exact (BlockBand.Layers.pg_entry (cib_measurable_res g) a b).add measurable_const

/-- `cibD` is a.e. strongly measurable: on the a.s. regular set it is the limit of measurable
difference quotients. -/
theorem cib_aesm_D {μ : Measure ((p.SiteMatrix ×
    (ZMod p.n → p.SiteMatrix)) × (ZMod p.n → ℝ))} {Ψ : ZMod p.n → p.SiteMatrix → ℝ}
    (hΨm : ∀ g, Measurable (Ψ g)) {g h : ZMod p.n}
    (hgood : ∀ᵐ y ∂μ, ContDiff ℝ 1
      (fun t : ℝ => Ψ g (cibRes p g y.1 y.2 + ((t : ℝ) : ℂ) • pairProjector p h))) :
    AEStronglyMeasurable (cibD p Ψ g h) μ := by
  set fk : ℕ → (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) × (ZMod p.n → ℝ) → ℝ := fun k y =>
    slope (fun t : ℝ => Ψ g (cibRes p g y.1 y.2 + ((t : ℝ) : ℂ) • pairProjector p h)) 0
      (1 / ((k : ℝ) + 1)) with hfkdef
  have hfk : ∀ k, AEStronglyMeasurable (fk k) μ := by
    intro k
    have hm : ∀ t : ℝ, Measurable (fun y : (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) ×
        (ZMod p.n → ℝ) => Ψ g (cibRes p g y.1 y.2 + ((t : ℝ) : ℂ) • pairProjector p h)) :=
      fun t => (hΨm g).comp (cib_measurable_shift g h t)
    simp only [hfkdef, slope_def_field]
    exact (((hm _).sub (hm 0)).div_const _).aestronglyMeasurable
  refine aestronglyMeasurable_of_tendsto_ae Filter.atTop hfk ?_
  filter_upwards [hgood] with y hy
  have hder := (hy.differentiable (by simp) 0).hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at hder
  have hu : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall fun k => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; positivity
  exact hder.comp hu

/-- Along the `h`-line through a regular residual, `u ↦ Ψ_g(H^{(g)}(x[h ↦ u]))²` has derivative
`2 Ψ_g ∂_{ξ_h} Ψ_g` at every `u`. -/
theorem cib_hasDerivAt_sq_line {Ψ : ZMod p.n → p.SiteMatrix → ℝ} {g h : ZMod p.n} (hgh : h ≠ g)
    (q : (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) × (ZMod p.n → ℝ))
    (hC : ContDiff ℝ 1
      (fun t : ℝ => Ψ g (cibRes p g q.1 q.2 + ((t : ℝ) : ℂ) • pairProjector p h))) (u : ℝ) :
    HasDerivAt (fun u => Ψ g (cibRes p g q.1 (Function.update q.2 h u)) ^ 2)
      (2 * Ψ g (cibRes p g q.1 (Function.update q.2 h u)) *
        cibD p Ψ g h (q.1, Function.update q.2 h u)) u := by
  set B := cibRes p g q.1 (Function.update q.2 h 0) with hB
  have hres : ∀ w, cibRes p g q.1 (Function.update q.2 h w) =
      B + ((w : ℝ) : ℂ) • pairProjector p h := fun w => cib_res_update_ne hgh q.1 q.2 w
  set ℓ : ℝ → ℝ := fun w => Ψ g (B + ((w : ℝ) : ℂ) • pairProjector p h) with hℓ
  have hq : cibRes p g q.1 q.2 = B + ((q.2 h : ℝ) : ℂ) • pairProjector p h := by
    rw [← hres, Function.update_eq_self]
  have hℓC : ContDiff ℝ 1 ℓ := by
    have : ℓ = (fun t : ℝ => Ψ g (cibRes p g q.1 q.2 + ((t : ℝ) : ℂ) • pairProjector p h)) ∘
        (fun w => w - q.2 h) := by
      funext w
      simp only [Function.comp_apply, hℓ, hq, add_assoc, ← add_smul]
      congr 3
      push_cast
      ring
    rw [this]
    exact hC.comp (contDiff_id.sub contDiff_const)
  have hℓd : HasDerivAt ℓ (deriv ℓ u) u := (hℓC.differentiable (by simp) u).hasDerivAt
  have hD : cibD p Ψ g h (q.1, Function.update q.2 h u) = deriv ℓ u := by
    unfold cibD
    simp only [hres]
    have : (fun t : ℝ => Ψ g (B + ((u : ℝ) : ℂ) • pairProjector p h +
        ((t : ℝ) : ℂ) • pairProjector p h)) = fun t => ℓ (t + u) := by
      funext t
      simp only [hℓ, add_assoc, ← add_smul]
      congr 3
      push_cast
      ring
    rw [this, deriv_comp_add_const, zero_add]
  simp only [hres, hD]
  have := hℓd.pow 2
  convert this using 1
  simp only [hℓ]
  ring

end DivergenceSpecific

/-!
### `pcDivergenceIsometry_holds`
-/

theorem cib_abs_sq_le_one {a : ℝ} (ha : |a| ≤ 1) : |a ^ 2| ≤ 1 := by
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) ha

/-- **`PcDivergenceIsometry`** (the divergence isometry), with no hypothesis:
`E D² = σ⁻² Σ_g E f_g² + Σ_{g ≠ h} E[(∂_{ξ_h} f_g)(∂_{ξ_g} f_h)]`. -/
theorem pcDivergenceIsometry_holds : PcDivergenceIsometry := by
  intro p model S hS Ψ hΨm hΨb hC1 hL4
  have hP : IsProbabilityMeasure S.X.P := csm_isProb_ext S.X
  have hdec := hS.2.1
  set μZ := S.X.P.map (cibZ S) with hμZ
  set ν := μZ.prod (Measure.pi fun _ : ZMod p.n => gaussianReal 0 (cibVar p)) with hν
  set ZX : S.X.Ω → (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) × (ZMod p.n → ℝ) :=
    fun ω => (cibZ S ω, cibXi S ω) with hZXdef
  have hZX : Measurable ZX := (cib_measurable_Z S).prodMk (cib_measurable_Xi S)
  have hlaw : S.X.P.map ZX = ν := cib_law_decomp S hS
  have hlawH : ν.map (fun y => cibAsm p y.1 y.2) = (model.law : Measure p.SiteMatrix) := by
    rw [← hlaw, Measure.map_map cib_measurable_asm hZX, ← S.X.map_eq]
    congr 1
    funext ω
    exact (cib_H_eq S hdec ω).symm
  -- the regular set on the product space
  have hgoodH : ∀ᵐ y ∂ν, (cibAsm p y.1 y.2).IsHermitian ∧ CsmBondGood (cibAsm p y.1 y.2) := by
    have h : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), H.IsHermitian ∧ CsmBondGood H :=
      model.isPhysical.1.and (csm_ae_bondGood model)
    rw [← hlawH] at h
    exact ae_of_ae_map cib_measurable_asm.aemeasurable h
  have hgoodE : ∀ g, ∀ᵐ y ∂ν, y.1.2 g ∈ cibAset p g := by
    intro g
    have hm : Measurable (fun y : (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) ×
        (ZMod p.n → ℝ) => y.1.2 g) := (measurable_pi_apply g).comp measurable_fst.snd
    have hEm : Measurable (fun ω => embedPair p g (tracelessPart (S.G g ω))) :=
      (ctr_measurable_embedPair g).comp (cib_measurable_tracelessPart.comp (S.measurable_G g))
    have hlawE : ν.map (fun y => y.1.2 g) =
        S.X.P.map (fun ω => embedPair p g (tracelessPart (S.G g ω))) := by
      rw [← hlaw, Measure.map_map hm hZX]
      rfl
    have hE : ∀ᵐ M ∂(ν.map (fun y => y.1.2 g)), M ∈ cibAset p g := by
      rw [hlawE]
      refine (ae_map_iff (p := fun M => M ∈ cibAset p g) hEm.aemeasurable
        (cib_measurableSet_Aset g)).mpr ?_
      have hGH : ∀ᵐ ω ∂S.X.P, (S.G g ω).IsHermitian := by
        have h : ∀ᵐ G ∂(S.X.P.map (S.G g)), (G : PairMatrix p g).IsHermitian := by
          rw [(hS.1 g).map_eq]
          exact cib_gue_ae_isHermitian _
        exact ae_of_ae_map (S.measurable_G g).aemeasurable h
      filter_upwards [hGH] with ω hω
      exact ⟨cib_embedPair_isHermitian (cib_traceless_isHermitian hω),
        by rw [cib_pairBlock_embedPair]⟩
    exact ae_of_ae_map hm.aemeasurable hE
  have hgood : ∀ᵐ y ∂ν, ∀ g, cibGoodRes p g (cibRes p g y.1 y.2) := by
    have hall : ∀ᵐ y ∂ν, ∀ g, y.1.2 g ∈ cibAset p g := ae_all_iff.mpr hgoodE
    filter_upwards [hgoodH, hall] with y hy hyE g
    exact cib_goodRes_of g y hy.1 hy.2 (hyE g)
  have hline : ∀ᵐ y ∂ν, ∀ g h, ContDiff ℝ 1
      (fun t : ℝ => Ψ g (cibRes p g y.1 y.2 + ((t : ℝ) : ℂ) • pairProjector p h)) := by
    filter_upwards [hgood] with y hy g h
    exact cib_line_contDiff (hC1 g _ (hy g).1 (hy g).2.1 (hy g).2.2) h
  -- the shift derivatives
  have hDm : ∀ g h, AEStronglyMeasurable (cibD p Ψ g h) ν := fun g h =>
    cib_aesm_D hΨm (hline.mono fun y hy => hy g h)
  have hDω : ∀ g h, (fun ω => deriv (fun t : ℝ =>
      Ψ g (S.X.Hm ω - embedPair p g (S.G g ω) + (t : ℂ) • pairProjector p h)) 0) =
      cibD p Ψ g h ∘ ZX := by
    intro g h
    funext ω
    simp only [Function.comp_apply, cibD, cib_res_eq S hdec g ω]
    rfl
  have hDmω : ∀ g h, AEStronglyMeasurable (fun ω => deriv (fun t : ℝ =>
      Ψ g (S.X.Hm ω - embedPair p g (S.G g ω) + (t : ℂ) • pairProjector p h)) 0) S.X.P := by
    intro g h
    rw [hDω]
    exact AEStronglyMeasurable.comp_aemeasurable (by rw [hlaw]; exact hDm g h) hZX.aemeasurable
  refine ⟨fun g h _ => hDmω g h, ?_⟩
  have hDL2 : ∀ g h, g ≠ h → MemLp (cibD p Ψ g h) 2 ν := by
    intro g h hgh
    have h4 : MemLp (cibD p Ψ g h ∘ ZX) 4 S.X.P := by
      rw [← hDω]
      exact hL4 g h hgh
    have h4' : MemLp (cibD p Ψ g h) 4 ν := by
      rw [← hlaw]
      exact (memLp_map_measure_iff (by rw [hlaw]; exact hDm g h) hZX.aemeasurable).mpr h4
    exact h4'.mono_exponent (by norm_num)
  -- the observables on the product space
  set f : ZMod p.n → (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) × (ZMod p.n → ℝ) → ℝ :=
    fun g y => Ψ g (cibRes p g y.1 y.2) ^ 2 with hfdef
  set df : ZMod p.n → ZMod p.n → (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) ×
      (ZMod p.n → ℝ) → ℝ :=
    fun g h y => 2 * Ψ g (cibRes p g y.1 y.2) * cibD p Ψ g h y with hdfdef
  have hΨr : ∀ g, Measurable (fun y : (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) ×
      (ZMod p.n → ℝ) => Ψ g (cibRes p g y.1 y.2)) := fun g =>
    (hΨm g).comp (cib_measurable_res g)
  have hfm : ∀ g, Measurable (f g) := fun g => (hΨr g).pow_const 2
  have hfb : ∀ g y, |f g y| ≤ 1 := fun g y => cib_abs_sq_le_one (hΨb g _)
  have hdfL2 : ∀ g h, g ≠ h → MemLp (df g h) 2 ν := by
    intro g h hgh
    refine ((hDL2 g h hgh).const_mul 2).of_le
      ((measurable_const.mul (hΨr g)).aestronglyMeasurable.mul (hDm g h))
      (ae_of_all _ fun y => ?_)
    show |2 * Ψ g (cibRes p g y.1 y.2) * cibD p Ψ g h y| ≤ |2 * cibD p Ψ g h y|
    rw [abs_mul, abs_mul, abs_mul]
    have h1 := hΨb g (cibRes p g y.1 y.2)
    have h2 := abs_nonneg (cibD p Ψ g h y)
    have h3 : (0 : ℝ) ≤ |2| := abs_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  have hfg : ∀ g z x t, f g (z, Function.update x g t) = f g (z, x) := fun g z x t => by
    simp only [hfdef, cib_res_update_self]
  have hdfg : ∀ g h z x t, df g h (z, Function.update x g t) = df g h (z, x) := fun g h z x t => by
    simp only [hdfdef, cibD, cib_res_update_self]
  -- the divergence on the product space
  set c : ℝ := (2 * (p.W : ℝ)) ^ 2 / splitS p with hc
  set Dy : (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) × (ZMod p.n → ℝ) → ℝ :=
    fun y => c * ∑ g, y.2 g * f g y with hDydef
  have hDym : Measurable Dy := measurable_const.mul (Finset.measurable_sum _ fun g _ =>
    ((measurable_pi_apply g).comp measurable_snd).mul (hfm g))
  have hDyω : (fun ω => (c * ∑ g, S.ξ g ω * Ψ g (S.X.Hm ω - embedPair p g (S.G g ω)) ^ 2) ^ 2) =
      (fun y => Dy y ^ 2) ∘ ZX := by
    funext ω
    simp only [Function.comp_apply, hDydef, hfdef, cib_res_eq S hdec]
    rfl
  set term : ZMod p.n → ZMod p.n → (p.SiteMatrix × (ZMod p.n → p.SiteMatrix)) ×
      (ZMod p.n → ℝ) → ℝ := fun g h y => (y.2 g * f g y) * (y.2 h * f h y) with htermdef
  have hterm : ∀ g h, Integrable (term g h) ν := by
    intro g h
    have hxg := (cib_integrable_coord_sq (cibVar p) g).comp_snd μZ
    have hxh := (cib_integrable_coord_sq (cibVar p) h).comp_snd μZ
    refine Integrable.mono' (hxg.add hxh)
      (((((measurable_pi_apply g).comp measurable_snd).mul (hfm g)).mul
        (((measurable_pi_apply h).comp measurable_snd).mul (hfm h))).aestronglyMeasurable)
      (ae_of_all _ fun y => ?_)
    simp only [htermdef, Real.norm_eq_abs, abs_mul]
    have h1 := hfb g y
    have h2 := hfb h y
    have h3 : |y.2 g| * |y.2 h| ≤ y.2 g ^ 2 + y.2 h ^ 2 := by
      nlinarith [sq_nonneg (|y.2 g| - |y.2 h|), sq_abs (y.2 g), sq_abs (y.2 h),
        abs_nonneg (y.2 g), abs_nonneg (y.2 h)]
    have h4 : |f g y| * |f h y| ≤ 1 := by nlinarith [abs_nonneg (f g y), abs_nonneg (f h y)]
    calc |y.2 g| * |f g y| * (|y.2 h| * |f h y|) = (|y.2 g| * |y.2 h|) * (|f g y| * |f h y|) := by
          ring
      _ ≤ (y.2 g ^ 2 + y.2 h ^ 2) * 1 := by gcongr
      _ = y.2 g ^ 2 + y.2 h ^ 2 := by ring
  have hDsq : (fun y => Dy y ^ 2) = fun y => c ^ 2 * ∑ g, ∑ h, term g h y := by
    funext y
    simp only [hDydef, htermdef]
    rw [mul_pow, pow_two (∑ g, y.2 g * f g y), Finset.sum_mul_sum]
  have hDint : Integrable (fun y => Dy y ^ 2) ν := by
    rw [hDsq]
    exact (integrable_finsetSum _ fun g _ => integrable_finsetSum _ fun h _ =>
      hterm g h).const_mul _
  have hDintP : Integrable (fun ω => (c * ∑ g, S.ξ g ω *
      Ψ g (S.X.Hm ω - embedPair p g (S.G g ω)) ^ 2) ^ 2) S.X.P := by
    rw [hDyω]
    rw [← hlaw] at hDint
    exact (integrable_map_measure hDint.aestronglyMeasurable hZX.aemeasurable).mp hDint
  refine ⟨hDintP, ?_⟩
  -- the left side
  have hLHS : (∫ ω, (c * ∑ g, S.ξ g ω * Ψ g (S.X.Hm ω - embedPair p g (S.G g ω)) ^ 2) ^ 2
      ∂S.X.P) = c ^ 2 * ∑ g, ∑ h, ∫ y, term g h y ∂ν := by
    rw [hDyω]
    have hm : AEStronglyMeasurable (fun y => Dy y ^ 2) (S.X.P.map ZX) :=
      (hDym.pow_const 2).aestronglyMeasurable
    rw [show (∫ ω, ((fun y => Dy y ^ 2) ∘ ZX) ω ∂S.X.P) = ∫ y, Dy y ^ 2 ∂(S.X.P.map ZX) from
      (integral_map hZX.aemeasurable hm).symm, hlaw, hDsq, integral_const_mul]
    congr 1
    rw [integral_finsetSum _ fun g _ => integrable_finsetSum _ fun h _ => hterm g h]
    refine Finset.sum_congr rfl fun g _ => ?_
    exact integral_finsetSum _ fun h _ => hterm g h
  -- the diagonal and off-diagonal moments
  have hdiag : ∀ g, ∫ y, term g g y ∂ν = (cibVar p : ℝ) * ∫ y, f g y ^ 2 ∂ν := by
    intro g
    have h := cib_diag_moment μZ (cibVar p) g (K := fun y => f g y ^ 2) ((hfm g).pow_const 2)
      (C := 1) (fun y => cib_abs_sq_le_one (hfb g y)) (fun z x t => by rw [hfg])
    rw [← h]
    congr 1
    funext y
    simp only [htermdef]
    ring
  have hoff : ∀ g h, g ≠ h → ∫ y, term g h y ∂ν =
      (cibVar p : ℝ) ^ 2 * ∫ y, df g h y * df h g y ∂ν := by
    intro g h hgh
    have hAd : ∀ᵐ q ∂ν, ∀ u, HasDerivAt (fun u => f g (q.1, Function.update q.2 h u))
        (df g h (q.1, Function.update q.2 h u)) u := by
      filter_upwards [hline] with q hq u
      exact cib_hasDerivAt_sq_line (Ne.symm hgh) q (hq g h) u
    have hBd : ∀ᵐ q ∂ν, ∀ t, HasDerivAt (fun t => f h (q.1, Function.update q.2 g t))
        (df h g (q.1, Function.update q.2 g t)) t := by
      filter_upwards [hline] with q hq t
      exact cib_hasDerivAt_sq_line hgh q (hq h g) t
    have h := cib_offdiag_moment μZ (cibVar p) hgh (A := f g) (B := f h) (A' := df g h)
      (B' := df h g) (hfm g) (hfm h) (hfb g) (hfb h) (hfg g) (hdfg g h) (hfg h) (hdfg h g)
      hAd hBd ((hdfL2 g h hgh).integrable one_le_two)
      ((hdfL2 h g (Ne.symm hgh)).integrable one_le_two)
      ((hdfL2 g h hgh).integrable_mul (hdfL2 h g (Ne.symm hgh)))
    rw [← h]
    congr 1
    funext y
    simp only [htermdef]
    ring
  -- the right side
  have hRf : ∀ g, (∫ ω, (Ψ g (S.X.Hm ω - embedPair p g (S.G g ω)) ^ 2) ^ 2 ∂S.X.P) =
      ∫ y, f g y ^ 2 ∂ν := by
    intro g
    rw [← hlaw, integral_map hZX.aemeasurable ((hfm g).pow_const 2).aestronglyMeasurable]
    congr 1
    funext ω
    simp only [hfdef, cib_res_eq S hdec g ω]
    rfl
  have hRd : ∀ g h, (∫ ω, (2 * Ψ g (S.X.Hm ω - embedPair p g (S.G g ω)) * deriv (fun t : ℝ =>
      Ψ g (S.X.Hm ω - embedPair p g (S.G g ω) + (t : ℂ) • pairProjector p h)) 0) *
      (2 * Ψ h (S.X.Hm ω - embedPair p h (S.G h ω)) * deriv (fun t : ℝ =>
      Ψ h (S.X.Hm ω - embedPair p h (S.G h ω) + (t : ℂ) • pairProjector p g)) 0) ∂S.X.P) =
      ∫ y, df g h y * df h g y ∂ν := by
    intro g h
    have hm : AEStronglyMeasurable (fun y => df g h y * df h g y) ν :=
      ((measurable_const.mul (hΨr g)).aestronglyMeasurable.mul (hDm g h)).mul
        ((measurable_const.mul (hΨr h)).aestronglyMeasurable.mul (hDm h g))
    rw [← hlaw, integral_map hZX.aemeasurable (by rw [hlaw]; exact hm)]
    congr 1
    funext ω
    have h1 := congrFun (hDω g h) ω
    have h2 := congrFun (hDω h g) ω
    simp only [Function.comp_apply] at h1 h2
    rw [h1, h2]
    simp only [hdfdef, cib_res_eq S hdec g ω, cib_res_eq S hdec h ω]
    rfl
  rw [hLHS]
  simp_rw [hRf, hRd]
  have hsplit : ∀ g, ∑ h, ∫ y, term g h y ∂ν = (cibVar p : ℝ) * ∫ y, f g y ^ 2 ∂ν +
      (cibVar p : ℝ) ^ 2 * ∑ h ∈ Finset.univ.erase g, ∫ y, df g h y * df h g y ∂ν := by
    intro g
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ g), hdiag g, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun h hh => ?_
    exact hoff g h (Ne.symm (Finset.ne_of_mem_erase hh))
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hc, cib_var_inv]
  have hv := cib_var_pos (p := p)
  field_simp

/-- `physicalCenter_holds_of` with the two integration-by-parts inputs discharged
(`pcEnergyPrimitive_holds`, `pcDivergenceIsometry_holds`); the remaining named inputs are
`PcSplittingExists` and `PcCenterCyclic`. -/
theorem physicalCenter_holds_of_split_cyclic (hrank : RankLocationContract)
    (hsmooth : SmoothCenterContract cst0) (hsplit : PcSplittingExists) (hcyc : PcCenterCyclic) :
    ∀ (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), 0 < θ →
      PhysicalCenterContract b θ T hb hb' pairCenterFamily0 :=
  physicalCenter_holds_of hrank hsmooth hsplit pcEnergyPrimitive_holds pcDivergenceIsometry_holds
    hcyc

end BlockBand.Center
