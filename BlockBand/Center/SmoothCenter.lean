module

public import BlockBand.Center.PhysicalCenterLaw
public import BlockBand.Layers.TaggedTrace

/-!
# The smooth center (`SmoothCenterContract cst0`)

`smoothCenter_holds_of` proves `SmoothCenterContract cst0` from
* `BlockBand.Layers.TaggedTraceStatement` (the tagged trace lemma: the base bounds for `ε` and
  `λ` and the decay bound, used directly), with its width threshold `W₀`;
* `CenterDomainContract cst0` (its `small` field: the domain-exit probability at `λ_α`);
* `ScFixedWidthTaggedMoments`: the tagged moments at bounded widths;
* `ScSmoothConstruction`: the deterministic construction of the smooth center
  (full compressed inverse, continuation of the regular root by the
  implicit-function theorem, cutoffs) with the two pointwise inequalities
  `|j^{sm}_e| ≤ C ε_e` and `|∂_{ξ_g} j^{sm}_e| ≤ C(Σ_i |∂_{ξ_g} ε_{e,i}| + ε_e λ_{eg})`.

Proved here: the almost-sure regularity of `H^{(e)}` on an extension with the edge splitting
(Hermitian, banded, invertible exterior bonds: `sc_ae_good`), the measurability of the tagged
objects (`sc_aesm_xiDeriv`, `sc_measurable_lambda`), the moment and derivative bounds of the
smooth center by Hölder/AM–GM from the tagged trace lemma (`sc_moment_core`, `sc_deriv_core`),
and the replacement clause from the domain clause and the agreement field. The law is the
exact simultaneous splitting (through `pc_isCenterSplitting_of_exact`) or any edge splitting.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE BlockBand.QUE.Fourier BlockBand.Model.Construction
open BlockBand.Layers BlockBand.QUE.PairResidual
open scoped ENNReal NNReal

/-!
## 1. The deterministic construction
-/

/-- **The deterministic construction of the smooth center**. `b, ϑ`
first; then a bulk interval `bulkInterval κ'`, a constant `C ≥ 0` and a function `Φ` of
`(p, α, e, H, E)` (`j^{sm}_e(E) = Φ(H^{(e)}, E)`) with exactly the deterministic fields of
`SmoothCenterContract cst0` (bounded by one, jointly Borel, `C^∞` along every shift line through
Hermitian band matrices with invertible exterior bonds, supported in `bulkInterval κ'`, equal to
`dysonCenter` on the regular domain) and, for `ϑ`-bulk ranks and such residuals, the two
pointwise bounds, with `ε_{e,k} = tgtEps`, `∂_{ξ_g} = tgtXiDeriv` and `λ_{eg} = tgtLambda`:
* `|Φ| ≤ C(|ε_{e,e}| + |ε_{e,e+1}|)` (the contrast at `ζ₀` is a residual difference, hence
  `|j_e| ≤ Cε_e`);
* for `g ≠ e`, `|∂_{ξ_g} Φ| ≤ C(|∂_{ξ_g}ε_{e,e}| + |∂_{ξ_g}ε_{e,e+1}| + (|ε_{e,e}| + |ε_{e,e+1}|)|λ_{eg}|)`. -/
def ScSmoothConstruction : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ ϑ : ℝ, 0 < ϑ → ϑ < 1 / 2 →
    ∃ (κ' C : ℝ), 0 < κ' ∧ 0 ≤ C ∧
    ∃ Φ : ∀ (p : Parameters), Fin p.N → ZMod p.n → p.SiteMatrix → ℝ → ℝ,
      (∀ (p : Parameters) α e (H : p.SiteMatrix) (E : ℝ), |Φ p α e H E| ≤ 1) ∧
      (∀ (p : Parameters) α e, Measurable (fun x : p.SiteMatrix × ℝ => Φ p α e x.1 x.2)) ∧
      (∀ (p : Parameters) α e (H₀ : p.SiteMatrix), H₀.IsHermitian →
        IsRingBanded p H₀ → ExteriorBondsInvertible p e H₀ →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : (ZMod p.n → ℝ) × ℝ =>
            Φ p α e (H₀ + ∑ g, (x.1 g : ℂ) • pairProjector p g) x.2)) ∧
      (∀ (p : Parameters) α e (H₀ : p.SiteMatrix) (E : ℝ), E ∉ bulkInterval κ' →
        Φ p α e H₀ E = 0) ∧
      (∀ (p : Parameters), p.b = b → ∀ α, IsBulkRank p ϑ α → ∀ e (H₀ : p.SiteMatrix) (E : ℝ),
        H₀.IsHermitian → IsRingBanded p H₀ → ExteriorBondsInvertible p e H₀ →
        InCenterDomain p e cst0 α H₀ E → Φ p α e H₀ E = dysonCenter p e cst0 α H₀ E) ∧
      (∀ (p : Parameters), p.b = b → ∀ α, IsBulkRank p ϑ α → ∀ e (H₀ : p.SiteMatrix) (E : ℝ),
        H₀.IsHermitian → IsRingBanded p H₀ → ExteriorBondsInvertible p e H₀ →
        |Φ p α e H₀ E| ≤ C * (‖tgtEps p e H₀ E e‖ + ‖tgtEps p e H₀ E (e + 1)‖) ∧
        ∀ g : ZMod p.n, g ≠ e →
          |deriv (fun t : ℝ => Φ p α e (H₀ + (t : ℂ) • pairProjector p g) E) 0| ≤
            C * (‖tgtXiDeriv p (fun H => tgtEps p e H E e) g H₀‖ +
              ‖tgtXiDeriv p (fun H => tgtEps p e H E (e + 1)) g H₀‖ +
              (‖tgtEps p e H₀ E e‖ + ‖tgtEps p e H₀ E (e + 1)‖) * ‖tgtLambda p e g H₀ E‖))

/-- **Fixed-width moments of.** `b, κ, T`, the moment order `q ≥ 1` and a
width bound `W₁` first; then one `C` for all `p` with `p.b = b`, `n ≤ TW`, `W ≤ W₁` (finitely
many shapes), every model, edge `e`, extension with the edge splitting, `E ∈ bulkInterval κ`,
`g ≠ e` and `k ∈ {e, e+1}`:
`‖ε_{e,k}‖_q, ‖λ_{eg}‖_q, ‖∂_{ξ_g}ε_{e,k}‖_q ≤ C`.
Law, objects and
norms as in `TaggedTraceStatement`.
This is the bounded-`W` complement of the large-`W`
statement (whose threshold `W₀` the `SmoothCenterContract` does not have).
Open.
-/
def ScFixedWidthTaggedMoments : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ q : ℝ, 1 ≤ q → ∀ W₁ : ℝ, ∃ C : ℝ,
    ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W → (p.W : ℝ) ≤ W₁ →
    ∀ (model : p.GaussianRingModel) (e : ZMod p.n) (X : PairExtension p model)
      (G : X.Ω → PairMatrix p e), IsCenterSplitting X G → ∀ E ∈ bulkInterval κ,
      (∀ k : ZMod p.n, (k = e ∨ k = e + 1) →
        eLpNorm (fun ω => tgtEps p e (X.Hm ω - embedPair p e (G ω)) E k) (ENNReal.ofReal q) X.P ≤
          ENNReal.ofReal C) ∧
      ∀ g : ZMod p.n, g ≠ e →
        eLpNorm (fun ω => tgtLambda p e g (X.Hm ω - embedPair p e (G ω)) E) (ENNReal.ofReal q)
            X.P ≤ ENNReal.ofReal C ∧
        ∀ k : ZMod p.n, (k = e ∨ k = e + 1) →
          eLpNorm (fun ω => tgtXiDeriv p (fun H => tgtEps p e H E k) g
              (X.Hm ω - embedPair p e (G ω))) (ENNReal.ofReal q) X.P ≤ ENNReal.ofReal C

/-!
## 2. Almost-sure regularity of the residual
-/

section Regular

variable {p : Parameters}

theorem sc_two_ne_zero : (2 : ZMod p.n) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p.n) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  have := p.n_ge_four
  omega

theorem sc_embedPair_zero_of_not_band (e : ZMod p.n) (G : PairMatrix p e) (x y : p.Site)
    (hxy : ¬ (y.1 = x.1 ∨ y.1 = x.1 + 1 ∨ y.1 = x.1 - 1)) : embedPair p e G x y = 0 := by
  unfold embedPair
  split_ifs with hx hy
  · exfalso; apply hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · left; rw [hx, hy]
    · right; left; rw [hx, hy]
    · right; right; rw [hx, hy]; ring
    · left; rw [hx, hy]
  · rfl
  · rfl

/-- `H^{(e)} = H - embed G_e` is banded when `H` is. -/
theorem sc_band_res {H : p.SiteMatrix} (hH : IsRingBanded p H) (e : ZMod p.n) (G : PairMatrix p e) :
    IsRingBanded p (H - embedPair p e G) := by
  intro x y hxy
  rw [Matrix.sub_apply, hH x y hxy, sc_embedPair_zero_of_not_band e G x y hxy, sub_zero]

/-- The exterior bonds of `H^{(e)}` are those of `H`. -/
theorem sc_bonds_res {H : p.SiteMatrix} (hH : ∀ j : ZMod p.n, (csmBond H j).det ≠ 0)
    (e : ZMod p.n) (G : PairMatrix p e) : ExteriorBondsInvertible p e (H - embedPair p e G) := by
  intro k hk
  have heq : (Matrix.of fun a c : Fin p.W => (H - embedPair p e G) (k, a) (k + 1, c)) =
      csmBond H k := by
    ext a c
    simp only [Matrix.of_apply, Matrix.sub_apply, csmBond]
    have hz : embedPair p e G (k, a) (k + 1, c) = 0 := by
      unfold embedPair
      split_ifs with hx hy
      · exfalso
        simp only at hx hy
        rcases hx with hx | hx
        · exact hk hx
        · rcases hy with hy | hy
          · apply sc_two_ne_zero (p := p)
            have : k + 1 = k - 1 := by rw [hy, hx]; ring
            have h2 : (2 : ZMod p.n) = (k + 1) - (k - 1) := by ring
            rw [h2, this, sub_self]
          · rw [hx] at hy
            have : (1 : ZMod p.n) = 0 := by
              have h1 : e + 1 + 1 = e + 1 := hy
              calc (1 : ZMod p.n) = (e + 1 + 1) - (e + 1) := by ring
                _ = 0 := by rw [h1, sub_self]
            have h1 : ((1 : ℕ) : ZMod p.n) = 0 := by exact_mod_cast this
            rw [ZMod.natCast_eq_zero_iff] at h1
            have := Nat.le_of_dvd (by norm_num) h1
            have := p.n_ge_four
            omega
      · rfl
      · rfl
    rw [hz, sub_zero]
  rw [heq]
  exact hH k

variable {model : p.GaussianRingModel}

/-- **On an extension with the edge splitting, `H^{(e)}` is a.s. Hermitian, banded and has
invertible exterior bonds.** -/
theorem sc_ae_good {e : ZMod p.n} (X : PairExtension p model) {G : X.Ω → PairMatrix p e}
    (hG : IsCenterSplitting X G) :
    ∀ᵐ ω ∂X.P, (X.Hm ω - embedPair p e (G ω)).IsHermitian ∧
      IsRingBanded p (X.Hm ω - embedPair p e (G ω)) ∧
      ExteriorBondsInvertible p e (X.Hm ω - embedPair p e (G ω)) := by
  filter_upwards [csm_ae_good X hG] with ω hω
  exact ⟨hω.2.1, sc_band_res hω.2.2.1 e (G ω), sc_bonds_res hω.2.2.2 e (G ω)⟩

end Regular

/-!
## 3. Measurability of the tagged objects
-/

section Measurable

variable {p : Parameters}

theorem sc_measurable_mul {α ι κ ν : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ]
    [Fintype ν] {f : α → Matrix ι κ ℂ} {g : α → Matrix κ ν ℂ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (fun a => f a * g a) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ =>
    (BlockBand.Layers.pg_entry hf i k).mul (BlockBand.Layers.pg_entry hg k j)

theorem sc_measurable_add {α ι κ : Type*} [MeasurableSpace α] {f g : α → Matrix ι κ ℂ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun a => f a + g a) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [Matrix.add_apply]
  exact (BlockBand.Layers.pg_entry hf i j).add (BlockBand.Layers.pg_entry hg i j)

theorem sc_measurable_lambda (e g : ZMod p.n) (E : ℝ) :
    Measurable (fun H : p.SiteMatrix => tgtLambda p e g H E) := by
  have hR : Measurable (fun H : p.SiteMatrix => tgtR0 p e H E) :=
    Measurable.comp
      (g := fun y : (p.SiteMatrix × ℝ) × ℂ => compressedResolvent p e y.1.1 y.1.2 y.2)
      (f := fun H : p.SiteMatrix => ((H, E), (splitS p : ℂ) * tgtMu E))
      ctr_measurable_compressed
      ((measurable_id.prodMk measurable_const).prodMk measurable_const)
  have hC : Continuous (fun H : p.SiteMatrix => couplingBlock p e H) := by
    unfold couplingBlock; fun_prop
  have hX : Continuous (fun H : p.SiteMatrix => exteriorBlock p e H - (E : ℂ) • 1) := by
    unfold exteriorBlock; fun_prop
  have hI : Measurable (fun H : p.SiteMatrix => (exteriorBlock p e H - (E : ℂ) • 1)⁻¹) :=
    BlockBand.Layers.measurable_matrix_inv.comp hX.measurable
  have hB : Measurable (fun H : p.SiteMatrix => tgtB p e g H E) := by
    unfold tgtB
    refine sc_measurable_add measurable_const ?_
    exact sc_measurable_mul (sc_measurable_mul (sc_measurable_mul (sc_measurable_mul
      (hC.matrix_conjTranspose).measurable hI) measurable_const) hI) hC.measurable
  have hT : Continuous (fun M : PairMatrix p e => M.trace) := continuous_id.matrix_trace
  unfold tgtLambda
  refine measurable_const.mul (hT.measurable.comp ?_)
  exact sc_measurable_mul (sc_measurable_mul
    ((continuous_id.matrix_conjTranspose).measurable.comp hR) hB) hR

variable {model : p.GaussianRingModel}

/-- `∂_{ξ_g} ε_{e,k}` is a.s. equal to the measurable formula of `tgt_hasDerivAt_eps_xi`. -/
theorem sc_aesm_xiDeriv {e : ZMod p.n} (X : PairExtension p model) {G : X.Ω → PairMatrix p e}
    (hG : IsCenterSplitting X G) {κ : ℝ} (hκ : 0 < κ) {E : ℝ} (hE : E ∈ bulkInterval κ)
    (g k : ZMod p.n) :
    AEStronglyMeasurable (fun ω => tgtXiDeriv p (fun H => tgtEps p e H E k) g
      (X.Hm ω - embedPair p e (G ω))) X.P := by
  have hE2 : |E| < 2 := abs_lt_two_of_mem_bulkInterval hκ hE
  set M : X.Ω → p.SiteMatrix := fun ω =>
    ctrFull p e (X.Hm ω - embedPair p e (G ω)) E (tgtZeta p E) with hMdef
  have hres : Measurable (fun ω => X.Hm ω - embedPair p e (G ω)) := csm_measurable_res X hG.1
  have hMm : Measurable M :=
    Measurable.comp (g := fun y : (p.SiteMatrix × ℝ) × ℂ => ctrFull p e y.1.1 y.1.2 y.2)
      (f := fun ω => ((X.Hm ω - embedPair p e (G ω), E), tgtZeta p E))
      ctr_continuous_ctrFull.measurable ((hres.prodMk measurable_const).prodMk measurable_const)
  have hinv : Measurable (fun ω => (M ω)⁻¹) := BlockBand.Layers.measurable_matrix_inv.comp hMm
  have hform : Measurable (fun ω => tgtTraceCLM e k
      (-((M ω)⁻¹ * pairProjector p g * (M ω)⁻¹))) := by
    refine (tgtTraceCLM e k).continuous.measurable.comp ?_
    have h3 := sc_measurable_mul (sc_measurable_mul hinv (measurable_const (a := pairProjector p g)))
      hinv
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    simp only [Matrix.neg_apply]
    exact (BlockBand.Layers.pg_entry h3 i j).neg
  refine hform.aestronglyMeasurable.congr ?_
  filter_upwards [tgt_ae_residual_isHermitian X hG, tgt_ae_residual_exterior_det X hG E]
    with ω hH hd
  have hM := tgt_ctrFull_det_ne (e := e) hH hd (tgt_zeta_im_pos (p := p) hE2)
  exact ((tgt_hasDerivAt_eps_xi g hM k).deriv).symm

end Measurable

/-!
## 4. `L^q` cores (Hölder by AM–GM)
-/

section Core

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem sc_one_le_ofReal {q : ℝ} (hq : 1 ≤ q) : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
  simpa using ENNReal.ofReal_le_ofReal hq

theorem sc_eLpNorm_sq (f : Ω → ℂ) (hf : AEStronglyMeasurable f μ) {q : ℝ} (hq : 0 ≤ q) :
    eLpNorm (fun ω => ‖f ω‖ ^ 2) (ENNReal.ofReal q) μ =
      eLpNorm f (ENNReal.ofReal (2 * q)) μ ^ 2 := by
  have h := eLpNorm_norm_rpow (μ := μ) (p := ENNReal.ofReal q) f hf (q := 2) (by norm_num)
  simp only [Real.rpow_two, ENNReal.rpow_two] at h
  rw [h, ← ENNReal.ofReal_mul hq, mul_comm]

theorem sc_eLpNorm_const_mul {f : Ω → ℝ} {c : ℝ} (hc : 0 ≤ c) (p : ℝ≥0∞) :
    eLpNorm (fun ω => c * f ω) p μ = ENNReal.ofReal c * eLpNorm f p μ := by
  rw [show (fun ω => c * f ω) = c • f from rfl, eLpNorm_const_smul, Real.enorm_eq_ofReal hc]

/-- `‖F‖_q ≤ 2CB` from `|F| ≤ C(|e₁| + |e₂|)` and `‖eᵢ‖_q ≤ B`. -/
theorem sc_moment_core {F : Ω → ℝ} {e1 e2 : Ω → ℂ} (hF : AEStronglyMeasurable F μ)
    (h1 : AEStronglyMeasurable e1 μ) (h2 : AEStronglyMeasurable e2 μ) {q C B : ℝ} (hq : 1 ≤ q)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hae : ∀ᵐ ω ∂μ, |F ω| ≤ C * (‖e1 ω‖ + ‖e2 ω‖))
    (hb1 : eLpNorm e1 (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B)
    (hb2 : eLpNorm e2 (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B) :
    eLpNorm F (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (C * (2 * B)) := by
  have hq1 := sc_one_le_ofReal hq
  calc eLpNorm F (ENNReal.ofReal q) μ
      ≤ eLpNorm (fun ω => C * (‖e1 ω‖ + ‖e2 ω‖)) (ENNReal.ofReal q) μ :=
        eLpNorm_mono_ae_real hF (by simpa only [Real.norm_eq_abs] using hae)
    _ = ENNReal.ofReal C * eLpNorm ((fun ω => ‖e1 ω‖) + fun ω => ‖e2 ω‖) (ENNReal.ofReal q) μ :=
        sc_eLpNorm_const_mul hC _
    _ ≤ ENNReal.ofReal C * (eLpNorm e1 (ENNReal.ofReal q) μ + eLpNorm e2 (ENNReal.ofReal q) μ) := by
        gcongr
        refine (eLpNorm_add_le hq1).trans (le_of_eq ?_)
        rw [eLpNorm_norm e1 h1, eLpNorm_norm e2 h2]
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal B + ENNReal.ofReal B) := by gcongr
    _ = ENNReal.ofReal (C * (2 * B)) := by
        rw [← ENNReal.ofReal_add hB hB, ← ENNReal.ofReal_mul hC]; ring_nf

/-- `‖F‖_q ≤ C(2A + 2tB² + L²/(2t))` from
`|F| ≤ C(|d₁| + |d₂| + (|e₁| + |e₂|)|l|)`, `‖dᵢ‖_q ≤ A`, `‖eᵢ‖_{2q} ≤ B`, `‖l‖_{2q} ≤ L`, `t > 0`. -/
theorem sc_deriv_core {F : Ω → ℝ} {d1 d2 e1 e2 l : Ω → ℂ} (hF : AEStronglyMeasurable F μ)
    (hd1 : AEStronglyMeasurable d1 μ) (hd2 : AEStronglyMeasurable d2 μ)
    (he1 : AEStronglyMeasurable e1 μ) (he2 : AEStronglyMeasurable e2 μ)
    (hl : AEStronglyMeasurable l μ) {q C A B L t : ℝ} (hq : 1 ≤ q) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (ht : 0 < t)
    (hae : ∀ᵐ ω ∂μ, |F ω| ≤ C * (‖d1 ω‖ + ‖d2 ω‖ + (‖e1 ω‖ + ‖e2 ω‖) * ‖l ω‖))
    (hbd1 : eLpNorm d1 (ENNReal.ofReal q) μ ≤ ENNReal.ofReal A)
    (hbd2 : eLpNorm d2 (ENNReal.ofReal q) μ ≤ ENNReal.ofReal A)
    (hbe1 : eLpNorm e1 (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal B)
    (hbe2 : eLpNorm e2 (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal B)
    (hbl : eLpNorm l (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal L) :
    eLpNorm F (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (C * (2 * A + 2 * t * B ^ 2 + L ^ 2 / (2 * t))) := by
  have hq1 := sc_one_le_ofReal hq
  have hq0 : 0 ≤ q := by linarith
  set P := ENNReal.ofReal q
  have hpt : ∀ᵐ ω ∂μ, ‖F ω‖ ≤ C * (‖d1 ω‖ + ‖d2 ω‖ + t * ‖e1 ω‖ ^ 2 + t * ‖e2 ω‖ ^ 2 +
      (1 / (2 * t)) * ‖l ω‖ ^ 2) := by
    filter_upwards [hae] with ω hω
    rw [Real.norm_eq_abs]
    refine hω.trans (mul_le_mul_of_nonneg_left ?_ hC)
    have key : (‖e1 ω‖ + ‖e2 ω‖) * ‖l ω‖ ≤
        t * ‖e1 ω‖ ^ 2 + t * ‖e2 ω‖ ^ 2 + (1 / (2 * t)) * ‖l ω‖ ^ 2 := by
      have h2t : 0 < 2 * t := by linarith
      have hsq : 0 ≤ (t * (‖e1 ω‖ + ‖e2 ω‖) - ‖l ω‖) ^ 2 := sq_nonneg _
      have hsq2 : 0 ≤ (‖e1 ω‖ - ‖e2 ω‖) ^ 2 := sq_nonneg _
      have : (‖e1 ω‖ + ‖e2 ω‖) * ‖l ω‖ * (2 * t) ≤
          (t * ‖e1 ω‖ ^ 2 + t * ‖e2 ω‖ ^ 2) * (2 * t) + ‖l ω‖ ^ 2 := by
        nlinarith [mul_nonneg (mul_nonneg ht.le ht.le) hsq2]
      rw [← sub_nonneg]
      have hfrac : (t * ‖e1 ω‖ ^ 2 + t * ‖e2 ω‖ ^ 2 + 1 / (2 * t) * ‖l ω‖ ^ 2) -
          (‖e1 ω‖ + ‖e2 ω‖) * ‖l ω‖ =
          ((t * ‖e1 ω‖ ^ 2 + t * ‖e2 ω‖ ^ 2) * (2 * t) + ‖l ω‖ ^ 2 -
            (‖e1 ω‖ + ‖e2 ω‖) * ‖l ω‖ * (2 * t)) / (2 * t) := by
        field_simp
      rw [hfrac]
      exact div_nonneg (by linarith) h2t.le
    linarith
  have hsum : eLpNorm (fun ω => ‖d1 ω‖ + ‖d2 ω‖ + t * ‖e1 ω‖ ^ 2 + t * ‖e2 ω‖ ^ 2 +
      (1 / (2 * t)) * ‖l ω‖ ^ 2) P μ ≤
      ENNReal.ofReal A + ENNReal.ofReal A + ENNReal.ofReal t * ENNReal.ofReal B ^ 2 +
        ENNReal.ofReal t * ENNReal.ofReal B ^ 2 + ENNReal.ofReal (1 / (2 * t)) * ENNReal.ofReal L ^ 2 := by
    have k1 : eLpNorm (fun ω => ‖d1 ω‖) P μ ≤ ENNReal.ofReal A := by rw [eLpNorm_norm d1 hd1]; exact hbd1
    have k2 : eLpNorm (fun ω => ‖d2 ω‖) P μ ≤ ENNReal.ofReal A := by rw [eLpNorm_norm d2 hd2]; exact hbd2
    have k3 : eLpNorm (fun ω => t * ‖e1 ω‖ ^ 2) P μ ≤ ENNReal.ofReal t * ENNReal.ofReal B ^ 2 := by
      rw [sc_eLpNorm_const_mul ht.le, sc_eLpNorm_sq e1 he1 hq0]; gcongr
    have k4 : eLpNorm (fun ω => t * ‖e2 ω‖ ^ 2) P μ ≤ ENNReal.ofReal t * ENNReal.ofReal B ^ 2 := by
      rw [sc_eLpNorm_const_mul ht.le, sc_eLpNorm_sq e2 he2 hq0]; gcongr
    have k5 : eLpNorm (fun ω => (1 / (2 * t)) * ‖l ω‖ ^ 2) P μ ≤
        ENNReal.ofReal (1 / (2 * t)) * ENNReal.ofReal L ^ 2 := by
      rw [sc_eLpNorm_const_mul (by positivity), sc_eLpNorm_sq l hl hq0]; gcongr
    calc eLpNorm (fun ω => ‖d1 ω‖ + ‖d2 ω‖ + t * ‖e1 ω‖ ^ 2 + t * ‖e2 ω‖ ^ 2 +
          (1 / (2 * t)) * ‖l ω‖ ^ 2) P μ
        = eLpNorm ((((fun ω => ‖d1 ω‖) + fun ω => ‖d2 ω‖) + (fun ω => t * ‖e1 ω‖ ^ 2)) +
            (fun ω => t * ‖e2 ω‖ ^ 2) + fun ω => (1 / (2 * t)) * ‖l ω‖ ^ 2) P μ := rfl
      _ ≤ _ := by
        refine (eLpNorm_add_le hq1).trans (add_le_add ((eLpNorm_add_le hq1).trans
          (add_le_add ((eLpNorm_add_le hq1).trans (add_le_add ((eLpNorm_add_le hq1).trans
            (add_le_add k1 k2)) k3)) k4)) k5)
  calc eLpNorm F P μ ≤ eLpNorm (fun ω => C * (‖d1 ω‖ + ‖d2 ω‖ + t * ‖e1 ω‖ ^ 2 +
        t * ‖e2 ω‖ ^ 2 + (1 / (2 * t)) * ‖l ω‖ ^ 2)) P μ := eLpNorm_mono_ae_real hF hpt
    _ = ENNReal.ofReal C * eLpNorm (fun ω => ‖d1 ω‖ + ‖d2 ω‖ + t * ‖e1 ω‖ ^ 2 +
        t * ‖e2 ω‖ ^ 2 + (1 / (2 * t)) * ‖l ω‖ ^ 2) P μ := sc_eLpNorm_const_mul hC _
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal A + ENNReal.ofReal A + ENNReal.ofReal t * ENNReal.ofReal B ^ 2 +
        ENNReal.ofReal t * ENNReal.ofReal B ^ 2 + ENNReal.ofReal (1 / (2 * t)) * ENNReal.ofReal L ^ 2) := by
        gcongr
    _ = ENNReal.ofReal (C * (2 * A + 2 * t * B ^ 2 + L ^ 2 / (2 * t))) := by
        rw [← ENNReal.ofReal_pow hB, ← ENNReal.ofReal_pow hL, ← ENNReal.ofReal_mul ht.le,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hA hA,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hC]
        congr 1; ring

end Core

/-!
## 5. Measurability of the shift derivative of the smooth center
-/

section DerivMeas

variable {p : Parameters} {model : p.GaussianRingModel}

theorem sc_sum_single (g : ZMod p.n) (t : ℝ) :
    ∑ h, ((Pi.single g t : ZMod p.n → ℝ) h : ℂ) • pairProjector p h = (t : ℂ) • pairProjector p g := by
  rw [Finset.sum_eq_single g]
  · simp
  · intro h _ hhg; simp [hhg]
  · simp

/-- The shift derivative `∂_{ξ_g} j^{sm}_e` is a.e. strongly measurable: on the a.s. regular set
it is the limit of the measurable difference quotients. -/
theorem sc_aesm_derivPhi {e : ZMod p.n} (X : PairExtension p model) {G : X.Ω → PairMatrix p e}
    (hG : IsCenterSplitting X G) (φ : p.SiteMatrix → ℝ → ℝ)
    (hmeas : Measurable (fun x : p.SiteMatrix × ℝ => φ x.1 x.2))
    (hsm : ∀ H₀ : p.SiteMatrix, H₀.IsHermitian → IsRingBanded p H₀ →
      ExteriorBondsInvertible p e H₀ →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : (ZMod p.n → ℝ) × ℝ => φ (H₀ + ∑ h, (x.1 h : ℂ) • pairProjector p h) x.2))
    (g : ZMod p.n) (E : ℝ) :
    AEStronglyMeasurable (fun ω => deriv (fun t : ℝ =>
      φ (X.Hm ω - embedPair p e (G ω) + (t : ℂ) • pairProjector p g) E) 0) X.P := by
  set res : X.Ω → p.SiteMatrix := fun ω => X.Hm ω - embedPair p e (G ω) with hresdef
  have hres : Measurable res := csm_measurable_res X hG.1
  set fk : ℕ → X.Ω → ℝ := fun k ω =>
    slope (fun t : ℝ => φ (res ω + (t : ℂ) • pairProjector p g) E) 0 (1 / ((k : ℝ) + 1))
    with hfkdef
  have hfk : ∀ k, AEStronglyMeasurable (fk k) X.P := by
    intro k
    have hm : ∀ t : ℝ, Measurable (fun ω => φ (res ω + (t : ℂ) • pairProjector p g) E) := by
      intro t
      have hshift : Measurable (fun ω => res ω + (t : ℂ) • pairProjector p g) := by
        refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
        simp only [Matrix.add_apply]
        exact (BlockBand.Layers.pg_entry hres x y).add measurable_const
      exact hmeas.comp (hshift.prodMk measurable_const)
    simp only [hfkdef, slope_def_field]
    exact (((hm _).sub (hm 0)).div_const _).aestronglyMeasurable
  refine aestronglyMeasurable_of_tendsto_ae Filter.atTop hfk ?_
  filter_upwards [sc_ae_good X hG] with ω hω
  have hdiff : DifferentiableAt ℝ (fun t : ℝ => φ (res ω + (t : ℂ) • pairProjector p g) E) 0 := by
    have hF := (hsm (res ω) hω.1 hω.2.1 hω.2.2).differentiable (by simp)
    have hl : Differentiable ℝ (fun t : ℝ => ((Pi.single g t : ZMod p.n → ℝ), E)) :=
      (differentiable_pi.mpr fun h => by
        by_cases hh : h = g
        · subst hh; simp
        · simp only [Pi.single_apply, hh, ite_false]; exact differentiable_const _).prodMk
        (differentiable_const _)
    have hcomp := (hF.comp hl) 0
    convert hcomp using 1
    funext t
    simp only [Function.comp_apply]
    rw [sc_sum_single]
  have hder := hdiff.hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at hder
  have hu : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall fun k => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; positivity
  exact hder.comp hu

end DerivMeas

/-!
## 6. The smooth center bounds
-/

theorem sc_rpow_half_ge {W W₁ : ℝ} (hW : 1 ≤ W) (hWW : W ≤ W₁) :
    1 ≤ Real.sqrt W₁ * W ^ (-(1 / 2 : ℝ)) := by
  have hW0 : 0 < W := by linarith
  rw [Real.rpow_neg hW0.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv, one_le_div (Real.sqrt_pos.mpr hW0)]
  exact Real.sqrt_le_sqrt hWW

theorem sc_inv_le_rpow {W : ℝ} (hW : 1 ≤ W) : 1 / W ≤ W ^ (-(1 / 2 : ℝ)) := by
  have hW0 : 0 < W := by linarith
  have hs : Real.sqrt W ≤ W := by nlinarith [Real.sq_sqrt hW0.le, Real.one_le_sqrt.mpr hW]
  rw [Real.rpow_neg hW0.le, ← Real.sqrt_eq_rpow, one_div]
  exact inv_anti₀ (Real.sqrt_pos.mpr hW0) hs

/-- *Statement.* `b ∈ (0,1/2)`, `ϑ ∈ (0,1/2)`, `T` first; then `ρ < 1`, `κ' > 0` and `Φ` with the
deterministic fields (`bounded`, `measurable`, `smooth`, `support`, `agree`), the fixed-energy
`L^q` bounds `‖j^{sm}_e(E)‖_q ≤ C_q/W` and `‖∂_{ξ_g} j^{sm}_e(E)‖_q ≤ C_q(ρ^{d(e,g)} + W^{-1/2})`
(`g ≠ e`) under every exact simultaneous splitting, every `ϑ`-bulk rank and every `E`, and the
replacement bound `P♯(j^{sm}_e(λ_α) ≠ j_e(λ_α)) ≤ C_D W^{-D}` under every edge splitting.
*Law.* `S.X.P` for the moments (via `pc_isCenterSplitting_of_exact`, the edge-`e` splitting of
`S`), the pair law `extendedPairMeasure` for replacement. *Norms.* `eLpNorm` of real scalars.
*Quantifier order / uniformity.* `ρ` is the `ρ` of `TaggedTraceStatement` at `(b, κ', T)`; `C_q`
after `q`, uniform in `p` (`p.b = b`, `n ≤ TW`, all `W ≥ 1`), the model, `S`, `α`, `e`, `g`, `E`;
`C_D` after `D`, uniform in the same data.
*Hypotheses.* `TaggedTraceStatement` (at `(b, κ', T)`, orders `q` and `2q`),
`CenterDomainContract cst0` (`small` at order `D + 1`), `ScFixedWidthTaggedMoments`
(widths `W ≤ max(W₀(q), W₀(2q), 1)`), `ScSmoothConstruction` (deterministic). -/
theorem smoothCenter_holds_of (htt : TaggedTraceStatement) (hfw : ScFixedWidthTaggedMoments)
    (hdom : CenterDomainContract cst0) (hcon : ScSmoothConstruction) :
    SmoothCenterContract cst0 := by
  intro b hb hb' ϑ T hϑ0 hϑ1
  obtain ⟨κ', C, hκ', hC, Φ, hbdd, hmeas, hsm, hsupp, hagree, hpt⟩ := hcon b hb hb' ϑ hϑ0 hϑ1
  obtain ⟨ρ, hρ0, hρ1, htq⟩ := htt.1 b hb hb' κ' T hκ'
  refine ⟨ρ, κ', hρ0, hρ1, hκ', Φ, hbdd, hmeas, hsm, hsupp, hagree, ?_, ?_⟩
  · -- the moment and derivative bounds of the smooth center
    intro q hq
    have hq2 : 1 ≤ 2 * q := by linarith
    obtain ⟨C1, W1, h1⟩ := htq q hq
    obtain ⟨C2, W2, h2⟩ := htq (2 * q) hq2
    set W₁ : ℝ := max (max W1 W2) 1 with hW₁
    obtain ⟨C3, h3⟩ := hfw b hb hb' κ' T hκ' q hq W₁
    obtain ⟨C4, h4⟩ := hfw b hb hb' κ' T hκ' (2 * q) hq2 W₁
    set c1 : ℝ := max C1 0 with hc1
    set c2 : ℝ := max C2 0 with hc2
    set c3 : ℝ := max (max C3 C4) 0 with hc3
    have hc10 : 0 ≤ c1 := le_max_right _ _
    have hc20 : 0 ≤ c2 := le_max_right _ _
    have hc30 : 0 ≤ c3 := le_max_right _ _
    have hW₁1 : 1 ≤ W₁ := le_max_right _ _
    set K1 : ℝ := C * (2 * c1 + 3 * c2 ^ 2) with hK1
    set K2 : ℝ := C * (2 * c3 + 3 * c3 ^ 2) * Real.sqrt W₁ with hK2
    have hK10 : 0 ≤ K1 := by positivity
    have hK20 : 0 ≤ K2 := by positivity
    refine ⟨max (2 * C * c1) W₁ + K1 + K2, ?_⟩
    intro p hpb hnT model S hS α hα e g E
    have hP : IsProbabilityMeasure S.X.P := csm_isProb_ext S.X
    have hG := pc_isCenterSplitting_of_exact S hS e
    have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
    have hW0 : (0 : ℝ) < p.W := by linarith
    have hCq0 : 0 ≤ max (2 * C * c1) W₁ + K1 + K2 := by
      have : 0 ≤ max (2 * C * c1) W₁ := le_trans (by linarith) (le_max_right _ _)
      positivity
    have hden : 0 ≤ ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    by_cases hE : E ∈ bulkInterval κ'
    swap
    · have hz : ∀ H : p.SiteMatrix, Φ p α e H E = 0 := fun H => hsupp p α e H E hE
      refine ⟨?_, fun _ => ?_⟩
      · simp only [hz]
        rw [show (fun _ : S.X.Ω => (0 : ℝ)) = 0 from rfl, eLpNorm_zero]; exact zero_le
      · simp only [hz, deriv_const]
        rw [show (fun _ : S.X.Ω => (0 : ℝ)) = 0 from rfl, eLpNorm_zero]; exact zero_le
    set res : S.X.Ω → p.SiteMatrix := fun ω => S.X.Hm ω - embedPair p e (S.G e ω) with hresdef
    have hres : Measurable res := csm_measurable_res S.X (S.measurable_G e)
    have hgood := sc_ae_good S.X hG
    have hεm : ∀ k, AEStronglyMeasurable (fun ω => tgtEps p e (res ω) E k) S.X.P := fun k =>
      ((tgt_measurable_eps e E k).comp hres).aestronglyMeasurable
    have hΦm : AEStronglyMeasurable (fun ω => Φ p α e (res ω) E) S.X.P :=
      ((hmeas p α e).comp (hres.prodMk measurable_const)).aestronglyMeasurable
    refine ⟨?_, fun hge => ?_⟩
    · -- `‖j^{sm}_e(E)‖_q ≤ C_q/W`
      by_cases hWl : max W1 W2 < (p.W : ℝ)
      · have hb1 := h1 p hpb hnT (lt_of_le_of_lt (le_max_left _ _) hWl) model e S.X (S.G e) hG E hE
        have hk : ∀ k : ZMod p.n, (k = e ∨ k = e + 1) →
            eLpNorm (fun ω => tgtEps p e (res ω) E k) (ENNReal.ofReal q) S.X.P ≤
              ENNReal.ofReal (c1 / p.W) := fun k hk =>
          (hb1.1 k hk).trans (ENNReal.ofReal_le_ofReal
            (div_le_div_of_nonneg_right (le_max_left _ _) hW0.le))
        have hcore := sc_moment_core hΦm (hεm e) (hεm (e + 1)) hq hC (by positivity)
          (by
            filter_upwards [hgood] with ω hω
            exact (hpt p hpb α hα e (res ω) E hω.1 hω.2.1 hω.2.2).1)
          (hk e (Or.inl rfl)) (hk (e + 1) (Or.inr rfl))
        refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
        rw [show C * (2 * (c1 / p.W)) = (2 * C * c1) / p.W by ring]
        refine div_le_div_of_nonneg_right ?_ hW0.le
        have : 2 * C * c1 ≤ max (2 * C * c1) W₁ := le_max_left _ _
        linarith
      · push Not at hWl
        have hb : eLpNorm (fun ω => Φ p α e (res ω) E) (ENNReal.ofReal q) S.X.P ≤
            ENNReal.ofReal 1 := by
          refine (eLpNorm_le_of_ae_bound (C := 1) hΦm
            (Filter.Eventually.of_forall fun ω => ?_)).trans ?_
          · rw [Real.norm_eq_abs]; exact hbdd p α e _ E
          · simp
        refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
        rw [le_div_iff₀ hW0, one_mul]
        have : W₁ ≤ max (2 * C * c1) W₁ := le_max_right _ _
        have : (p.W : ℝ) ≤ W₁ := hWl.trans (le_max_left _ _)
        linarith
    · -- `‖∂_{ξ_g} j^{sm}_e(E)‖_q ≤ C_q(ρ^{d(e,g)} + W^{-1/2})`
      have hdm : ∀ k, AEStronglyMeasurable (fun ω => tgtXiDeriv p (fun H => tgtEps p e H E k) g
          (res ω)) S.X.P := fun k => sc_aesm_xiDeriv S.X hG hκ' hE g k
      have hlm : AEStronglyMeasurable (fun ω => tgtLambda p e g (res ω) E) S.X.P :=
        ((sc_measurable_lambda e g E).comp hres).aestronglyMeasurable
      have hFm := sc_aesm_derivPhi S.X hG (Φ p α e) (hmeas p α e) (hsm p α e) g E
      have hae : ∀ᵐ ω ∂S.X.P, |deriv (fun t : ℝ =>
          Φ p α e (res ω + (t : ℂ) • pairProjector p g) E) 0| ≤
          C * (‖tgtXiDeriv p (fun H => tgtEps p e H E e) g (res ω)‖ +
            ‖tgtXiDeriv p (fun H => tgtEps p e H E (e + 1)) g (res ω)‖ +
            (‖tgtEps p e (res ω) E e‖ + ‖tgtEps p e (res ω) E (e + 1)‖) *
              ‖tgtLambda p e g (res ω) E‖) := by
        filter_upwards [hgood] with ω hω
        exact (hpt p hpb α hα e (res ω) E hω.1 hω.2.1 hω.2.2).2 g hge
      by_cases hWl : max W1 W2 < (p.W : ℝ)
      · have hWa : W1 < (p.W : ℝ) := lt_of_le_of_lt (le_max_left _ _) hWl
        have hWb : W2 < (p.W : ℝ) := lt_of_le_of_lt (le_max_right _ _) hWl
        have hb1 := h1 p hpb hnT hWa model e S.X (S.G e) hG E hE
        have hb2 := h2 p hpb hnT hWb model e S.X (S.G e) hG E hE
        set A : ℝ := c1 * (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ))) with hA
        have hd : ∀ k : ZMod p.n, (k = e ∨ k = e + 1) →
            eLpNorm (fun ω => tgtXiDeriv p (fun H => tgtEps p e H E k) g (res ω))
              (ENNReal.ofReal q) S.X.P ≤ ENNReal.ofReal A := fun k hk =>
          (hb1.2.2 g hge k hk).trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hden))
        have he : ∀ k : ZMod p.n, (k = e ∨ k = e + 1) →
            eLpNorm (fun ω => tgtEps p e (res ω) E k) (ENNReal.ofReal (2 * q)) S.X.P ≤
              ENNReal.ofReal (c2 / p.W) := fun k hk =>
          (hb2.1 k hk).trans (ENNReal.ofReal_le_ofReal
            (div_le_div_of_nonneg_right (le_max_left _ _) hW0.le))
        have hl : eLpNorm (fun ω => tgtLambda p e g (res ω) E) (ENNReal.ofReal (2 * q)) S.X.P ≤
            ENNReal.ofReal c2 := (hb2.2.1 g hge).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
        have hcore := sc_deriv_core hFm (hdm e) (hdm (e + 1)) (hεm e) (hεm (e + 1)) hlm hq hC
          (by positivity) (by positivity) hc20 hW0 hae (hd e (Or.inl rfl)) (hd (e + 1) (Or.inr rfl))
          (he e (Or.inl rfl)) (he (e + 1) (Or.inr rfl)) hl
        refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
        have hinv := sc_inv_le_rpow hW1
        have hρd : 0 ≤ ρ ^ edgeDistance p e g := by positivity
        have h1W : 1 / (p.W : ℝ) ≤ ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ)) := by
          linarith
        have hkey : 2 * A + 2 * p.W * (c2 / p.W) ^ 2 + c2 ^ 2 / (2 * p.W) ≤
            (2 * c1 + 3 * c2 ^ 2) * (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ))) := by
          have e1 : 2 * (p.W : ℝ) * (c2 / p.W) ^ 2 = 2 * c2 ^ 2 * (1 / p.W) := by
            field_simp
          have e2 : c2 ^ 2 / (2 * (p.W : ℝ)) ≤ c2 ^ 2 * (1 / p.W) := by
            rw [div_le_iff₀ (by positivity)]
            have : c2 ^ 2 * (1 / (p.W : ℝ)) * (2 * p.W) = 2 * c2 ^ 2 := by field_simp
            nlinarith [sq_nonneg c2]
          rw [e1, hA]
          nlinarith [mul_le_mul_of_nonneg_left h1W (show 0 ≤ c2 ^ 2 by positivity)]
        calc C * (2 * A + 2 * p.W * (c2 / p.W) ^ 2 + c2 ^ 2 / (2 * p.W))
            ≤ C * ((2 * c1 + 3 * c2 ^ 2) *
                (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ)))) :=
              mul_le_mul_of_nonneg_left hkey hC
          _ = K1 * (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ))) := by rw [hK1]; ring
          _ ≤ (max (2 * C * c1) W₁ + K1 + K2) *
                (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ))) := by
              refine mul_le_mul_of_nonneg_right ?_ hden
              have : 0 ≤ max (2 * C * c1) W₁ := le_trans (by linarith) (le_max_right _ _)
              linarith
      · push Not at hWl
        have hWW : (p.W : ℝ) ≤ W₁ := hWl.trans (le_max_left _ _)
        have hb3 := h3 p hpb hnT hWW model e S.X (S.G e) hG E hE
        have hb4 := h4 p hpb hnT hWW model e S.X (S.G e) hG E hE
        have hc3a : C3 ≤ c3 := (le_max_left _ _).trans (le_max_left _ _)
        have hc3b : C4 ≤ c3 := (le_max_right _ _).trans (le_max_left _ _)
        have hcore := sc_deriv_core hFm (hdm e) (hdm (e + 1)) (hεm e) (hεm (e + 1)) hlm hq hC
          hc30 hc30 hc30 (t := 1) one_pos hae
          (((hb3.2 g hge).2 e (Or.inl rfl)).trans (ENNReal.ofReal_le_ofReal hc3a))
          (((hb3.2 g hge).2 (e + 1) (Or.inr rfl)).trans (ENNReal.ofReal_le_ofReal hc3a))
          ((hb4.1 e (Or.inl rfl)).trans (ENNReal.ofReal_le_ofReal hc3b))
          ((hb4.1 (e + 1) (Or.inr rfl)).trans (ENNReal.ofReal_le_ofReal hc3b))
          (((hb4.2 g hge).1).trans (ENNReal.ofReal_le_ofReal hc3b))
        refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
        have hsq := sc_rpow_half_ge hW1 hWW
        have hrp : 0 ≤ (p.W : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
        have hρd : 0 ≤ ρ ^ edgeDistance p e g := by positivity
        calc C * (2 * c3 + 2 * 1 * c3 ^ 2 + c3 ^ 2 / (2 * 1))
            ≤ C * (2 * c3 + 3 * c3 ^ 2) := by
              refine mul_le_mul_of_nonneg_left ?_ hC; nlinarith [sq_nonneg c3]
          _ ≤ C * (2 * c3 + 3 * c3 ^ 2) * (Real.sqrt W₁ * (p.W : ℝ) ^ (-(1 / 2 : ℝ))) := by
              have h0 : 0 ≤ C * (2 * c3 + 3 * c3 ^ 2) := by positivity
              exact le_mul_of_one_le_right h0 hsq
          _ = K2 * (p.W : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [hK2]; ring
          _ ≤ (max (2 * C * c1) W₁ + K1 + K2) *
                (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ))) := by
              have hM0 : 0 ≤ max (2 * C * c1) W₁ := le_trans (by linarith) (le_max_right _ _)
              have k1 : K2 * (p.W : ℝ) ^ (-(1 / 2 : ℝ)) ≤
                  (max (2 * C * c1) W₁ + K1 + K2) * (p.W : ℝ) ^ (-(1 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_right (by linarith) hrp
              have k2 : (max (2 * C * c1) W₁ + K1 + K2) * (p.W : ℝ) ^ (-(1 / 2 : ℝ)) ≤
                  (max (2 * C * c1) W₁ + K1 + K2) *
                    (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ))) :=
                mul_le_mul_of_nonneg_left (by linarith) (by linarith)
              exact k1.trans k2
  · -- replacement: `P♯(j^{sm}_e(λ_α) ≠ j_e(λ_α)) ≤ C_D W^{-D}`
    intro D
    obtain ⟨Cs, Ws, hs⟩ := hdom.small b hb hb' ϑ T hϑ0 hϑ1 (D + 1)
    set W' : ℝ := max Ws 1 with hW'
    have hW'1 : 1 ≤ W' := le_max_right _ _
    refine ⟨max Cs 0 + W' ^ |D|, ?_⟩
    intro p hpb hnT model α hα i X G hG
    have hprob : IsProbabilityMeasure (extendedPairMeasure p α i X.P X.Hm) :=
      extendedPairMeasure_isProbability p model α i X
    have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
    have hW0 : (0 : ℝ) < p.W := by linarith
    set bad := {ω | Φ p α i (X.Hm ω - embedPair p i (G ω)) (physicalOrderedEigenvalue p (X.Hm ω) α) ≠
        dysonCenter p i cst0 α (X.Hm ω - embedPair p i (G ω))
          (physicalOrderedEigenvalue p (X.Hm ω) α)} with hbad
    have hgood : ∀ᵐ ω ∂extendedPairMeasure p α i X.P X.Hm,
        (X.Hm ω - embedPair p i (G ω)).IsHermitian ∧
          IsRingBanded p (X.Hm ω - embedPair p i (G ω)) ∧
          ExteriorBondsInvertible p i (X.Hm ω - embedPair p i (G ω)) := by
      unfold extendedPairMeasure
      exact (withDensity_absolutelyContinuous _ _).ae_le (sc_ae_good X hG)
    have hsub : bad ≤ᵐ[extendedPairMeasure p α i X.P X.Hm]
        {ω | ¬ InCenterDomain p i cst0 α (X.Hm ω - embedPair p i (G ω))
          (physicalOrderedEigenvalue p (X.Hm ω) α)} := by
      filter_upwards [hgood] with ω hω hb
      intro hdomω
      exact hb (hagree p hpb α hα i _ _ hω.1 hω.2.1 hω.2.2 hdomω)
    have hmono := measure_mono_ae hsub
    have hfac : 0 ≤ (max Cs 0 + W' ^ |D|) * (p.W : ℝ) ^ (-D) := by positivity
    by_cases hWl : Ws < (p.W : ℝ)
    · refine hmono.trans ((hs p hpb hnT hWl model α hα i X G hG).trans
        (ENNReal.ofReal_le_ofReal ?_))
      rw [show (1 : ℝ) - (D + 1) = -D by ring]
      have hx : 0 ≤ (p.W : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
      have hy : 0 ≤ W' ^ |D| := Real.rpow_nonneg (by linarith) _
      exact mul_le_mul_of_nonneg_right (by linarith [le_max_left Cs 0]) hx
    · push Not at hWl
      refine (prob_le_one).trans ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have hWW : (p.W : ℝ) ≤ W' := hWl.trans (le_max_left _ _)
      have hkey : 1 ≤ W' ^ |D| * (p.W : ℝ) ^ (-D) := by
        rcases le_total 0 D with hD | hD
        · rw [abs_of_nonneg hD, Real.rpow_neg hW0.le, ← div_eq_mul_inv,
            one_le_div (Real.rpow_pos_of_pos hW0 D)]
          exact Real.rpow_le_rpow hW0.le hWW hD
        · have h1 : 1 ≤ W' ^ |D| := Real.one_le_rpow hW'1 (abs_nonneg _)
          have h2 : 1 ≤ (p.W : ℝ) ^ (-D) := Real.one_le_rpow hW1 (by linarith)
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ W' ^ |D| * (p.W : ℝ) ^ (-D) := mul_le_mul h1 h2 zero_le_one (by linarith)
      have : 0 ≤ max Cs 0 * (p.W : ℝ) ^ (-D) :=
        mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hW0.le _)
      calc (1 : ℝ) ≤ W' ^ |D| * (p.W : ℝ) ^ (-D) := hkey
        _ ≤ max Cs 0 * (p.W : ℝ) ^ (-D) + W' ^ |D| * (p.W : ℝ) ^ (-D) := by linarith
        _ = (max Cs 0 + W' ^ |D|) * (p.W : ℝ) ^ (-D) := by ring

end BlockBand.Center
