module

public import BlockBand.Layers.DiffCovarianceFamily
public import BlockBand.Layers.MatchedTraces
public import BlockBand.Layers.ClockMoments
public import BlockBand.Center.DysonCenterFamily

/-!
# The tagged trace (the tagged-trace lemma): statement, clock input, and the proved clauses

The statement of the tagged-trace lemma is `TaggedTraceStatement`, with the energy clause (the
full-energy trace bound) as the separate `FullEnergyTraceStatement`.

Objects, at the edge `e`, pair `S_e = {e, e+1}`, residual matrix
`H^{(e)} = H - G_e`, `s = min(c,b)` (`splitS`), `μ = ā` (`a = matchedA E`):
* `R_e⁰ = (K_e - sμ)⁻¹`: the compressed resolvent `compressedResolvent p e H^{(e)} E (sμ)` (equal
  to `(K_e - sμ)⁻¹` off the exterior poles, `ctr_compressed_eq_schur`);
* `ε_{e,i} = W⁻¹ Tr (R_e⁰)_{ii} - μ` for `i ∈ {e, e+1}` (`tgtEps`);
* `B_{eg} = ∂_{ξ_g} K_e = (P_g)_{SS} + H_{SR}(H_{RR} - E)⁻¹(P_g)_{RR}(H_{RR} - E)⁻¹H_{RS}` (`tgtB`;
  the derivative identity is `tgt_hasDerivAt_edgeSchur`, positivity `tgt_tgtB_posSemidef`);
* `λ_{eg} = W⁻¹ Tr (R_e⁰)* B_{eg} R_e⁰` (`tgtLambda`).

Proved here:
* `taggedClockInput_holds` — the clock input `TaggedClockInput`, from the clock-moments lemma
  (`clockMoments_holds`);
* `tgt_xi_e_hasDerivAt_zero` — `∂_{ξ_e} ε_{e,i} = 0`, and `tgt_residualOf_update` — `∂_{ξ_g} H^{(e)} =
  P_{S_g}` pointwise for `g ≠ e`;
* `tgt_hasDerivAt_edgeSchur`, `tgt_tgtB_posSemidef` — the formula for `B_{eg}` and `B_{eg} ⪰ 0`;
* `tgt_isPairSplitting` — every edge splitting (`IsCenterSplitting`) induces a pair-splitting law of
  `(H_R, C, V)` of `H^{(e)}`; `tgt_map_residual_eq`, `tgt_eLpNorm_residual_eq` — the law of
  `H^{(e)}` is the explicit image of `rpLaw ⊗ pathLaw (n-2)` (residual pair layer and exterior
  path), so every moment of a functional of `H^{(e)}` is a moment under that product law;
* `tgt_eps_base` — the first half of the tagged base case, `max_i ‖ε_{e,i}‖_p ≤ C_p/W`, from
  the matched-traces theorem (residual pair);
* `tgt_hasDerivAt_eps_xi`, `tgt_hasDerivAt_eps_energy` — the exact `ξ_g`- and energy derivatives
  of `ε_{e,k}` (`-W⁻¹Tr P_k[M⁻¹P_{S_g}M⁻¹]_{SS}`, `W⁻¹Tr P_k[M⁻¹(1 + ζ'P_S)M⁻¹]_{SS} - μ'`,
  `M = H^{(e)} - E - ζP_S`), `tgt_ctrFull_det_ne` (`M` is invertible off the exterior poles), and
  `tgt_ae_eps_energy_hasDerivAt` (the energy derivative exists a.s. at deterministic `E`);
* the scalar identities of the energy paragraph, `a' = a²/(1-a²)`, `z' = (b - a⁻²)a'`,
  `1 + (1-b)a' + z' = 0` (`tgt_hasDerivAt_matchedA`, `tgt_hasDerivAt_boundaryZ`,
  `tgt_energy_cancel` of `BlockBand.Layers.DiffCovarianceFamily`).

Stated in §7 with full statements and proved in other modules: `TgtLambdaBound` (the `λ` half of
the tagged base case, `tgtLambdaBound_holds`) and `TgtDecayBound` (the tagged decay bound,
`tgtDecayBound_holds`); assembly `taggedTrace_of_open`. The moment half of the full-energy trace
bound is `BlockBand.Center.FullEnergyTraceBound` (equivalence in
`BlockBand.Layers.TaggedTraceEnergy`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE BlockBand.Model.Construction BlockBand.Coarea
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. The objects of the tagged-trace lemma
-/

section Objects

variable (p : Parameters) (e : ZMod p.n)

/-- `μ = ā(E)`, the conjugate matched value (the tagged-trace lemma, `centerResidual`). -/
def tgtMu (E : ℝ) : ℂ := conj (matchedA E)

/-- `R_e⁰ = (K_e - sμ)⁻¹`, realized as the full compressed inverse at `ζ = sμ`
(`compressedResolvent`). -/
def tgtR0 (Hres : p.SiteMatrix) (E : ℝ) : PairMatrix p e :=
  compressedResolvent p e Hres E ((splitS p : ℂ) * tgtMu E)

/-- `ε_{e,k} = W⁻¹ Tr (R_e⁰)_{kk} - μ` for a block `k` of the pair (`k ∈ {e, e+1}`). -/
def tgtEps (Hres : p.SiteMatrix) (E : ℝ) (k : ZMod p.n) : ℂ :=
  pairBlockTrace p e (tgtR0 p e Hres E) k - tgtMu E

/-- `B_{eg} = (P_g)_{SS} + H_{SR}(H_{RR} - E)⁻¹(P_g)_{RR}(H_{RR} - E)⁻¹H_{RS}`,
with `H_{RS} = C = couplingBlock`, `H_{SR} = C*` (as in `physicalCoareaF`), `P_g = pairProjector g`.
It is `∂_{ξ_g} K_e` (`tgt_hasDerivAt_edgeSchur`). -/
def tgtB (g : ZMod p.n) (Hres : p.SiteMatrix) (E : ℝ) : PairMatrix p e :=
  pairBlock p e (pairProjector p g) +
    (couplingBlock p e Hres)ᴴ * (exteriorBlock p e Hres - (E : ℂ) • 1)⁻¹ *
      exteriorBlock p e (pairProjector p g) * (exteriorBlock p e Hres - (E : ℂ) • 1)⁻¹ *
        couplingBlock p e Hres

/-- `λ_{eg} = W⁻¹ Tr (R_e⁰)* B_{eg} R_e⁰`. -/
def tgtLambda (g : ZMod p.n) (Hres : p.SiteMatrix) (E : ℝ) : ℂ :=
  (p.W : ℂ)⁻¹ * ((tgtR0 p e Hres E)ᴴ * tgtB p e g Hres E * tgtR0 p e Hres E).trace

/-- The residual matrix as a function of the auxiliary decomposition
(the simultaneous splitting): `H^{(e)} = V + Σ_{g ≠ e} (G_g⁰ + ξ_g I_{S_g})`. -/
def tgtResidualOf (V : p.SiteMatrix) (G0 : ∀ g : ZMod p.n, PairMatrix p g) (ξ : ZMod p.n → ℝ) :
    p.SiteMatrix :=
  V + ∑ g ∈ Finset.univ.erase e, embedPair p g (G0 g + ((ξ g : ℝ) : ℂ) • 1)

/-- The `ξ_g`-derivative of a function `F` of the residual matrix at `H^{(e)}`, `g ≠ e`:
`∂_t F(H^{(e)} + t P_{S_g})` at `t = 0` (`tgt_residualOf_update`: pointwise
`∂_{ξ_g} H^{(e)} = P_{S_g}`). -/
def tgtXiDeriv (F : p.SiteMatrix → ℂ) (g : ZMod p.n) (Hres : p.SiteMatrix) : ℂ :=
  deriv (fun t : ℝ => F (Hres + (t : ℂ) • pairProjector p g)) 0

end Objects

/-!
## 2. The statements
-/

/-- **The clock input of the tagged-trace lemma**: exactly the clock bounds of the clock-moments
lemma (the tagged clock moments) used by the proof, under the path model of
`BlockBand.Layers.PathGrowth` (`growthLaw`, `grownSchur`) and `pathLaw`, at deterministic
`E ∈ bulkInterval κ`, for real `p ≥ 1`; constants `C, W₀` after `b, κ, T, p`, uniform in
`W ≥ W₀`, the core `r₀ ∈ {1,2}`, the length and the tags:
* `full`: the full (energy) clock `s_r = W⁻¹ Tr R_r* X_r' R_r` (`clkCoreSource b E (fun _ => true)`,
  `X_r' = B_p*(H_r - E)⁻²B_p`) under `pathLaw W r b`, `‖s_r‖_p ≤ C(r+1)` for `1 ≤ r ≤ TW` (used
  in the energy paragraph);
* `tagged`: every clock of the tagged clock identity (`clkClock`) along the growth with an arbitrary
  core tag and
  at most two tagged layer steps (`clkTagCount τ L ≤ 2`, "tags on ≤ 2 blocks"),
  `sup_{k ≤ L} ‖W⁻¹ Tr Y_{r₀+2k}‖_p ≤ C` (used for `‖δu‖_p ≤ C_p/W` at tagged steps, and
  for the final trace pairing with `Y`). -/
def TaggedClockInput : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → 0 < W →
      (∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * W → ∀ E ∈ bulkInterval κ,
        eLpNorm (fun ω => clkTrace (clkCoreSource b E (fun _ => true) ω)) (ENNReal.ofReal p)
          (pathLaw W r b) ≤ ENNReal.ofReal (C * ((r : ℝ) + 1))) ∧
      ∀ r₀ : ℕ, (r₀ = 1 ∨ r₀ = 2) → ∀ L : ℕ, ((r₀ + 2 * L : ℕ) : ℝ) ≤ T * W →
      ∀ E ∈ bulkInterval κ, ∀ (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool), clkTagCount τ L ≤ 2 →
        ∀ k, k ≤ L →
          eLpNorm (fun ω => clkTrace (clkClock b E τ₀ τ ω k)) (ENNReal.ofReal p)
            (growthLaw W r₀ L b) ≤ ENNReal.ofReal C

/-- **The tagged-trace lemma**: the clauses of the tagged base case, the tagged decay bound and
`∂_{ξ_e} = 0`; the energy clause (the full-energy trace bound) is `FullEnergyTraceStatement`.

*Law.* The edge splitting of the simultaneous splitting at the edge `e`: any extension `X`
carrying the exact physical law (`H = X.Hm`) with a pair Gaussian `G_e ~ GUE_{2W}(s/(2W))`,
`s = splitS p = min(c,b)`, independent of `H^{(e)} = H - G_e` (`IsCenterSplitting X G`). The full
simultaneous splitting (`SimultaneousSplitting.IsExact`) gives an edge splitting at every `e`
(`H - G_e = V + Σ_{g≠e} G_g` is independent of `G_e`; that bridge lemma is not part of this
module), and every quantity below is a function of `H^{(e)}` only. The auxiliary scalars `ξ_g`,
`g ≠ e`, enter `H^{(e)}` as `ξ_g P_{S_g}` (`tgtResidualOf`, `tgt_residualOf_update`), so `∂_{ξ_g}`
is the pointwise directional derivative along `pairProjector g` (`tgtXiDeriv`), "the same
deterministic directional derivative under the marginal independent-entry law of `H^{(e)}`".

*Domain and quantifiers.* `b ∈ (0, 1/2)`, the interval `I = bulkInterval κ` (`κ > 0`) and `T`
first; then `ρ ∈ [0,1)`; then the fixed moment order `q ≥ 1` ("every fixed `p`"); then `C_q` and
`W₀`; then uniformly in `W > W₀`, ring lengths `n ≤ TW` (`4 ≤ n` is part of `Parameters`), every
model, edge `e`,
extension with the edge splitting, deterministic `E ∈ I`, pair block `k ∈ {e, e+1}` and edge
`g ≠ e`. (`W₀` is the paper's standing large-`W` convention, as in `CenterDomainContract.small`;
the proved clause `tgt_eps_base` holds with it.)

*Norms.* `L^q(X.P)` norms (`eLpNorm`) of complex scalars (modulus).

*Clauses.*
1. (the tagged base case) `‖ε_{e,k}‖_q ≤ C_q/W` and `‖λ_{eg}‖_q ≤ C_q`;
2. (the tagged decay bound) `‖∂_{ξ_g} ε_{e,k}‖_q ≤ C_q(ρ^{d(e,g)} + W^{-1/2})`, `d = edgeDistance`;
3. (`∂_{ξ_e} = 0`) deterministic: for every decomposition `(V, G⁰, ξ)`, `ξ_e ↦ ε_{e,k}` is constant
   (derivative zero), since `H^{(e)}` does not contain `ξ_e`. -/
def TaggedTraceStatement : Prop :=
  (∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ q : ℝ, 1 ≤ q → ∃ C W₀ : ℝ,
      ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W → W₀ < (p.W : ℝ) →
      ∀ (model : p.GaussianRingModel) (e : ZMod p.n) (X : PairExtension p model)
        (G : X.Ω → PairMatrix p e), IsCenterSplitting X G → ∀ E ∈ bulkInterval κ,
        (∀ k : ZMod p.n, (k = e ∨ k = e + 1) →
          eLpNorm (fun ω => tgtEps p e (X.Hm ω - embedPair p e (G ω)) E k) (ENNReal.ofReal q) X.P ≤
            ENNReal.ofReal (C / p.W)) ∧
        (∀ g : ZMod p.n, g ≠ e →
          eLpNorm (fun ω => tgtLambda p e g (X.Hm ω - embedPair p e (G ω)) E) (ENNReal.ofReal q)
            X.P ≤ ENNReal.ofReal C) ∧
        (∀ g : ZMod p.n, g ≠ e → ∀ k : ZMod p.n, (k = e ∨ k = e + 1) →
          eLpNorm (fun ω => tgtXiDeriv p (fun H => tgtEps p e H E k) g
              (X.Hm ω - embedPair p e (G ω))) (ENNReal.ofReal q) X.P ≤
            ENNReal.ofReal (C * (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ)))))) ∧
  ∀ (p : Parameters) (e : ZMod p.n) (V : p.SiteMatrix) (G0 : ∀ g : ZMod p.n, PairMatrix p g)
    (ξ : ZMod p.n → ℝ) (E : ℝ) (k : ZMod p.n),
    HasDerivAt (fun t : ℝ => tgtEps p e (tgtResidualOf p e V G0 (Function.update ξ e t)) E k) 0
      (ξ e)

/-- **The full-energy trace bound**: `sup_{E ∈ I} max_i ‖ε'_{e,i}(E)‖_{L^p} ≤ C_p n/√W`.
Law, domain and quantifier order as in `TaggedTraceStatement` (`b, κ, T`, then `q ≥ 1`, then
`C_q, W₀`, then uniformly in `W > W₀`, `n ≤ TW`, the model, `e`, the extension with the edge
splitting, deterministic `E ∈ I`, `k ∈ {e, e+1}`). `ε'_{e,k}(E)` is the full energy derivative of
`E' ↦ ε_{e,k}(E') = W⁻¹ Tr P_k ℛ_e(E', s μ(E')) - μ(E')` at fixed `H^{(e)}` (the matrix and the
spectral parameter `sμ(E')` move together). The clause asserts that this derivative exists almost
surely and bounds its `L^q` norm. -/
def FullEnergyTraceStatement : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ q : ℝ, 1 ≤ q → ∃ C W₀ : ℝ,
    ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W → W₀ < (p.W : ℝ) →
    ∀ (model : p.GaussianRingModel) (e : ZMod p.n) (X : PairExtension p model)
      (G : X.Ω → PairMatrix p e), IsCenterSplitting X G → ∀ E ∈ bulkInterval κ,
      ∀ k : ZMod p.n, (k = e ∨ k = e + 1) →
        (∀ᵐ ω ∂X.P, DifferentiableAt ℝ
          (fun E' : ℝ => tgtEps p e (X.Hm ω - embedPair p e (G ω)) E' k) E) ∧
        eLpNorm (fun ω => deriv (fun E' : ℝ => tgtEps p e (X.Hm ω - embedPair p e (G ω)) E' k) E)
            (ENNReal.ofReal q) X.P ≤ ENNReal.ofReal (C * p.n / Real.sqrt p.W)

/-!
## 3. The clock input from the clock-moments lemma
-/

/-- `TaggedClockInput` is the `full` (path-law) and `tagged` parts of `ClockMomentsStatement`. -/
theorem taggedClockInput_of_clockMoments (h : ClockMomentsStatement) : TaggedClockInput := by
  intro b hb0 hb1 κ T hκ p hp
  obtain ⟨C, W₀, hC, hW⟩ := h b hb0 hb1 κ T hκ p hp
  refine ⟨C, W₀, hC, fun W hW₀ hW0 => ⟨(hW W hW₀ hW0).1, ?_⟩⟩
  intro r₀ hr₀ L hL E hE τ₀ τ hτ k hk
  exact ((hW W hW₀ hW0).2 r₀ hr₀ L hL E hE).2 τ₀ τ hτ k hk

/-- **The clock input** (the clock-moments lemma, `clockMoments_holds`), from
`ConditionalBlockGUECount` and `GaussianLpGradient`. -/
theorem taggedClockInput_holds (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : Internal.Contracts.Inputs.GaussianLpGradient) : TaggedClockInput :=
  taggedClockInput_of_clockMoments (clockMoments_holds hcount hgrad)

/-!
## 4. Deterministic clauses: `∂_{ξ_e} = 0`, `∂_{ξ_g} H^{(e)} = P_{S_g}`, `B_{eg}`
-/

section Deterministic

variable {p : Parameters} (e : ZMod p.n)

/-- `H^{(e)}` does not contain `ξ_e`. -/
theorem tgt_residualOf_update_self (V : p.SiteMatrix) (G0 : ∀ g : ZMod p.n, PairMatrix p g)
    (ξ : ZMod p.n → ℝ) (t : ℝ) :
    tgtResidualOf p e V G0 (Function.update ξ e t) = tgtResidualOf p e V G0 ξ := by
  unfold tgtResidualOf
  congr 1
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hg)]

/-- **`∂_{ξ_e} ε_{e,k} = 0`**: `ξ_e ↦ ε_{e,k}(H^{(e)})` is constant. -/
theorem tgt_xi_e_hasDerivAt_zero (V : p.SiteMatrix) (G0 : ∀ g : ZMod p.n, PairMatrix p g)
    (ξ : ZMod p.n → ℝ) (E : ℝ) (k : ZMod p.n) :
    HasDerivAt (fun t : ℝ => tgtEps p e (tgtResidualOf p e V G0 (Function.update ξ e t)) E k) 0
      (ξ e) := by
  have h : (fun t : ℝ => tgtEps p e (tgtResidualOf p e V G0 (Function.update ξ e t)) E k) =
      fun _ => tgtEps p e (tgtResidualOf p e V G0 ξ) E k := by
    funext t; rw [tgt_residualOf_update_self]
  rw [h]
  exact hasDerivAt_const _ _

theorem tgt_embedPair_add (g : ZMod p.n) (A B : PairMatrix p g) :
    embedPair p g (A + B) = embedPair p g A + embedPair p g B := by
  ext x y
  simp only [Matrix.add_apply, embedPair]
  split_ifs <;> simp

theorem tgt_embedPair_zero (g : ZMod p.n) : embedPair p g 0 = 0 := by
  ext x y
  simp only [embedPair, Matrix.zero_apply]
  split_ifs <;> rfl

/-- `embedPair (c I_{S_g}) = c P_{S_g}`. -/
theorem tgt_embedPair_smul_one (g : ZMod p.n) (c : ℂ) :
    embedPair p g (c • (1 : PairMatrix p g)) = c • pairProjector p g := by
  ext x y
  simp only [embedPair, pairProjector, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x.1 = g ∨ x.1 = g + 1
    · simp [hx]
    · simp [hx]
  · have hne : ∀ (hx : x.1 = g ∨ x.1 = g + 1) (hy : y.1 = g ∨ y.1 = g + 1),
        (⟨x, hx⟩ : PairSite p g) ≠ ⟨y, hy⟩ := fun _ _ h => hxy (congrArg Subtype.val h)
    split_ifs with hx hy
    · rw [Matrix.one_apply_ne (hne hx hy)]
    · simp
    · simp

/-- **`∂_{ξ_g} H^{(e)} = P_{S_g}` pointwise** for `g ≠ e`:
`H^{(e)}(ξ + t δ_g) = H^{(e)}(ξ) + t P_{S_g}`. -/
theorem tgt_residualOf_update {g : ZMod p.n} (hg : g ≠ e) (V : p.SiteMatrix)
    (G0 : ∀ g : ZMod p.n, PairMatrix p g) (ξ : ZMod p.n → ℝ) (t : ℝ) :
    tgtResidualOf p e V G0 (Function.update ξ g (ξ g + t)) =
      tgtResidualOf p e V G0 ξ + (t : ℂ) • pairProjector p g := by
  unfold tgtResidualOf
  have hmem : g ∈ Finset.univ.erase e := Finset.mem_erase.mpr ⟨hg, Finset.mem_univ g⟩
  have hterm : ∀ g' ∈ Finset.univ.erase e,
      embedPair p g' (G0 g' + ((Function.update ξ g (ξ g + t) g' : ℝ) : ℂ) • 1) =
        embedPair p g' (G0 g' + ((ξ g' : ℝ) : ℂ) • 1) +
          if g' = g then (t : ℂ) • pairProjector p g else 0 := by
    intro g' _
    by_cases h : g' = g
    · subst h
      rw [Function.update_self, ite_eq_left rfl, Complex.ofReal_add, add_smul, ← add_assoc,
        tgt_embedPair_add, tgt_embedPair_smul_one]
    · rw [Function.update_of_ne h, ite_eq_right h, add_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq' _ _ _, ite_eq_left hmem,
    add_assoc]

/-- The coupling block of `P_{S_g}` vanishes (`P_{S_g}` is diagonal). -/
theorem tgt_couplingBlock_projector (g : ZMod p.n) :
    couplingBlock p e (pairProjector p g) = 0 := by
  ext x y
  simp only [couplingBlock, pairProjector, Matrix.zero_apply]
  rw [Matrix.diagonal_apply_ne]
  intro h
  exact x.2 (h ▸ y.2)

theorem tgt_exteriorBlock_add (A B : p.SiteMatrix) :
    exteriorBlock p e (A + B) = exteriorBlock p e A + exteriorBlock p e B := rfl

theorem tgt_exteriorBlock_smul (c : ℂ) (A : p.SiteMatrix) :
    exteriorBlock p e (c • A) = c • exteriorBlock p e A := rfl

theorem tgt_couplingBlock_add (A B : p.SiteMatrix) :
    couplingBlock p e (A + B) = couplingBlock p e A + couplingBlock p e B := rfl

theorem tgt_couplingBlock_smul (c : ℂ) (A : p.SiteMatrix) :
    couplingBlock p e (c • A) = c • couplingBlock p e A := rfl

theorem tgt_pairBlock_add (A B : p.SiteMatrix) :
    pairBlock p e (A + B) = pairBlock p e A + pairBlock p e B := rfl

theorem tgt_pairBlock_smul (c : ℂ) (A : p.SiteMatrix) :
    pairBlock p e (c • A) = c • pairBlock p e A := rfl

/-- **`B_{eg} = ∂_{ξ_g} K_e`**: off the exterior poles,
`t ↦ K_e(H^{(e)} + t P_{S_g})` has derivative `tgtB` at `0`. -/
theorem tgt_hasDerivAt_edgeSchur (g : ZMod p.n) (Hres : p.SiteMatrix) (E : ℝ)
    (hdet : (exteriorBlock p e Hres - (E : ℂ) • 1).det ≠ 0) :
    HasDerivAt (fun t : ℝ => edgeSchur p e (Hres + (t : ℂ) • pairProjector p g) E)
      (tgtB p e g Hres E) 0 := by
  set N := exteriorBlock p e Hres - (E : ℂ) • 1 with hN
  set C := couplingBlock p e Hres with hC
  set Q := exteriorBlock p e (pairProjector p g) with hQ
  set P0 := pairBlock p e (pairProjector p g) with hP0
  have hform : (fun t : ℝ => edgeSchur p e (Hres + (t : ℂ) • pairProjector p g) E) =
      fun t : ℝ => (pairBlock p e Hres + (t : ℂ) • P0) - Cᴴ * (N + (t : ℂ) • Q)⁻¹ * C -
        (E : ℂ) • 1 := by
    funext t
    have hext : exteriorBlock p e (Hres + (t : ℂ) • pairProjector p g) - (E : ℂ) • 1 =
        N + (t : ℂ) • Q := by
      rw [tgt_exteriorBlock_add, tgt_exteriorBlock_smul, hN, hQ]; abel
    unfold edgeSchur physicalCoareaF physicalCoareaResolvent
    rw [hext, tgt_pairBlock_add, tgt_pairBlock_smul, tgt_couplingBlock_add, tgt_couplingBlock_smul,
      tgt_couplingBlock_projector, smul_zero, add_zero]
  rw [hform]
  have hΔ : HasDerivAt (fun t : ℝ => (t : ℂ) • Q) Q 0 := by
    have := (hasDerivAt_id (0 : ℝ)).smul_const Q
    simpa [Complex.coe_smul] using this
  have hinv := tgt_hasDerivAt_inv_family (isUnit_iff_ne_zero.mpr hdet) hΔ (by simp)
  have hmid : HasDerivAt (fun t : ℝ => Cᴴ * (N + (t : ℂ) • Q)⁻¹ * C)
      (Cᴴ * (-(N⁻¹ * Q * N⁻¹)) * C) 0 := by
    let L : Matrix (ExteriorSite p e) (ExteriorSite p e) ℂ →L[ℝ] PairMatrix p e :=
      LinearMap.toContinuousLinearMap
        { toFun := fun M => Cᴴ * M * C
          map_add' := fun A B => by rw [Matrix.mul_add, Matrix.add_mul]
          map_smul' := fun r A => by
            simp only [RingHom.id_apply]
            rw [Matrix.mul_smul, Matrix.smul_mul] }
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hinv
  have hP : HasDerivAt (fun t : ℝ => pairBlock p e Hres + (t : ℂ) • P0) P0 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const P0).const_add (pairBlock p e Hres)
    simpa [Complex.coe_smul] using this
  have h := (hP.sub hmid).sub_const ((E : ℂ) • 1)
  convert h using 1
  unfold tgtB
  rw [← hN, ← hC, ← hQ, ← hP0, Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add]
  simp only [Matrix.mul_assoc]

theorem tgt_pairBlock_projector_posSemidef (g : ZMod p.n) :
    (pairBlock p e (pairProjector p g)).PosSemidef := by
  have h : pairBlock p e (pairProjector p g) =
      Matrix.diagonal (fun x : PairSite p e => if x.1.1 = g ∨ x.1.1 = g + 1 then 1 else 0) := by
    ext x y
    simp only [pairBlock, pairProjector, Matrix.diagonal_apply, Subtype.ext_iff]
  rw [h]
  refine Matrix.posSemidef_diagonal_iff.mpr fun x => ?_
  split_ifs
  · exact zero_le_one
  · exact le_rfl

theorem tgt_exteriorBlock_projector_posSemidef (g : ZMod p.n) :
    (exteriorBlock p e (pairProjector p g)).PosSemidef := by
  have h : exteriorBlock p e (pairProjector p g) =
      Matrix.diagonal (fun x : ExteriorSite p e => if x.1.1 = g ∨ x.1.1 = g + 1 then 1 else 0) := by
    ext x y
    simp only [exteriorBlock, pairProjector, Matrix.diagonal_apply, Subtype.ext_iff]
  rw [h]
  refine Matrix.posSemidef_diagonal_iff.mpr fun x => ?_
  split_ifs
  · exact zero_le_one
  · exact le_rfl

/-- **`B_{eg} ⪰ 0`** for Hermitian `H^{(e)}` and real `E`. -/
theorem tgt_tgtB_posSemidef (g : ZMod p.n) {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) (E : ℝ) :
    (tgtB p e g Hres E).PosSemidef := by
  set N := exteriorBlock p e Hres - (E : ℂ) • 1 with hN
  set C := couplingBlock p e Hres with hC
  have hext : (exteriorBlock p e Hres).IsHermitian := by
    ext x y
    simp only [Matrix.conjTranspose_apply, exteriorBlock]
    exact hH.apply x.1 y.1
  have hNh : N.IsHermitian := by
    refine hext.sub ?_
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  have hNi : (N⁻¹).IsHermitian := hNh.inv
  have h2 : Cᴴ * N⁻¹ * exteriorBlock p e (pairProjector p g) * N⁻¹ * C =
      (N⁻¹ * C)ᴴ * exteriorBlock p e (pairProjector p g) * (N⁻¹ * C) := by
    rw [conjTranspose_mul, hNi.eq]
    simp only [Matrix.mul_assoc]
  unfold tgtB
  rw [← hN, ← hC, h2]
  exact (tgt_pairBlock_projector_posSemidef e g).add
    ((tgt_exteriorBlock_projector_posSemidef e g).conjTranspose_mul_mul_same _)

end Deterministic

/-!
## 5. The law of the residual and the base clause `‖ε_{e,i}‖_p ≤ C_p/W`
-/

section Law

variable {p : Parameters} {model : p.GaussianRingModel} {e : ZMod p.n}

/-- The split state `(H_R, C, V) = (H^{(e)}_{RR}, H^{(e)}_{RS}, H^{(e)}_{SS})` of a residual matrix. -/
def tgtSplit (e : ZMod p.n) (H : p.SiteMatrix) : SplitState p e :=
  (exteriorBlock p e H, couplingBlock p e H, pairBlock p e H)

theorem tgt_measurable_split (e : ZMod p.n) : Measurable (tgtSplit (p := p) e) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_) <;>
  exact measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y =>
    pg_entry measurable_id _ _

/-- `K_e(E)` of the residual is the pair residual of its split state. -/
theorem tgt_edgeSchur_eq (e : ZMod p.n) (H : p.SiteMatrix) (E : ℝ) :
    edgeSchur p e H E = pairResidual p e (tgtSplit e H) E := rfl

/-- Reassembly of a Hermitian residual: `assemble (H_R, C, V) G = H + embed G`. -/
theorem tgt_assemble_split {H : p.SiteMatrix} (hH : H.IsHermitian) (G : PairMatrix p e) :
    assemble p e (tgtSplit e H) G = H + embedPair p e G := by
  ext x y
  simp only [assemble, tgtSplit, embedPair, exteriorBlock, couplingBlock, pairBlock,
    Matrix.add_apply]
  split_ifs
  · rfl
  · simp only [add_zero]; exact hH.apply x y
  · simp
  · simp

theorem tgt_isProb (X : PairExtension p model) : IsProbabilityMeasure X.P := by
  constructor
  have h := congrArg (fun μ : Measure p.SiteMatrix => μ Set.univ) X.map_eq
  rw [Measure.map_apply X.measurable_Hm MeasurableSet.univ, Set.preimage_univ] at h
  rw [h]
  exact measure_univ

theorem tgt_measurable_residual (X : PairExtension p model) {G : X.Ω → PairMatrix p e}
    (hG : Measurable G) : Measurable (fun ω => X.Hm ω - embedPair p e (G ω)) :=
  X.measurable_Hm.sub ((BlockBand.Center.ctr_measurable_embedPair e).comp hG)

/-- Under an edge splitting the residual `H^{(e)} = H - G_e` is a.s. Hermitian. -/
theorem tgt_ae_residual_isHermitian (X : PairExtension p model) {G : X.Ω → PairMatrix p e}
    (hs : IsCenterSplitting X G) : ∀ᵐ ω ∂X.P, (X.Hm ω - embedPair p e (G ω)).IsHermitian := by
  obtain ⟨hGm, hlaw, -⟩ := hs
  have hH : ∀ᵐ ω ∂X.P, (X.Hm ω).IsHermitian := by
    refine ae_of_ae_map X.measurable_Hm.aemeasurable ?_
    rw [X.map_eq]
    exact model.isPhysical.1
  have hGh : ∀ᵐ ω ∂X.P, (G ω).IsHermitian := by
    refine ae_of_ae_map hGm.aemeasurable ?_
    rw [hlaw.map_eq]
    exact BlockBand.Center.ctr_ae_gue_isHermitian _
  filter_upwards [hH, hGh] with ω h1 h2
  refine h1.sub ?_
  unfold IsHermitian
  rw [BlockBand.Center.ctr_embedPair_conjTranspose, h2.eq]

/-- **The residual's split state has a pair-splitting law**: for every edge splitting
(`IsCenterSplitting`), the law of `(H_R, C, V)` of `H^{(e)} = H - G_e` is a splitting law of
the pair splitting at `s = splitS p` (and hence, by `residualSplitLaw_holds`, the explicit
`(rpLaw ⊗ pathLaw (n-2)).map rpSplitAssemble`). -/
theorem tgt_isPairSplitting (X : PairExtension p model) {G : X.Ω → PairMatrix p e}
    (hs : IsCenterSplitting X G) :
    IsPairSplitting p e model (splitS p)
      (X.P.map (fun ω => tgtSplit e (X.Hm ω - embedPair p e (G ω)))) := by
  have := tgt_isProb X
  have hs' := hs
  obtain ⟨hGm, hlaw, hind⟩ := hs'
  set F := fun ω => X.Hm ω - embedPair p e (G ω) with hFdef
  have hF : Measurable F := tgt_measurable_residual X hGm
  have hjoint : X.P.map (fun ω => (F ω, G ω)) = (X.P.map F).prod (X.P.map G) :=
    (indepFun_iff_map_prod_eq_prod_map_map hF.aemeasurable hGm.aemeasurable).mp hind
  have hsplit := tgt_measurable_split (p := p) e
  have hcomp : X.P.map (fun ω => tgtSplit e (F ω)) = (X.P.map F).map (tgtSplit e) := by
    rw [Measure.map_map hsplit hF]; rfl
  unfold IsPairSplitting
  rw [hcomp, ← hlaw.map_eq]
  have hprod : ((X.P.map F).map (tgtSplit e)).prod (X.P.map G) =
      ((X.P.map F).prod (X.P.map G)).map (Prod.map (tgtSplit e) id) := by
    rw [← Measure.map_prod_map _ _ hsplit measurable_id, Measure.map_id]
  rw [hprod, ← hjoint, Measure.map_map (Measurable.prodMap hsplit measurable_id)
      (hF.prodMk hGm), Measure.map_map (BlockBand.Layers.rsl_measurable_assemble e)
      ((Measurable.prodMap hsplit measurable_id).comp (hF.prodMk hGm)), ← X.map_eq]
  refine Measure.map_congr ?_
  filter_upwards [tgt_ae_residual_isHermitian X hs] with ω hω
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
  rw [tgt_assemble_split hω]
  exact sub_add_cancel _ _

/-- Under a pair-splitting law the exterior block is a.s. off the energy `E`. -/
theorem tgt_ae_exterior_det {s : ℝ} (hs0 : 0 < s) (hs1 : s < 2 * min (1 - 2 * p.b) p.b)
    {Pω : Measure (SplitState p e)} (hP : IsPairSplitting p e model s Pω) (E : ℝ) :
    ∀ᵐ ω ∂Pω, (ω.1 - (E : ℂ) • 1).det ≠ 0 := by
  rw [residualSplitLaw_holds p model e s hs0 hs1 Pω hP]
  have hmeasS : MeasurableSet {ω : SplitState p e | (ω.1 - (E : ℂ) • 1).det ≠ 0} := by
    have hM : Measurable (fun ω : SplitState p e => (ω.1 - (E : ℂ) • 1).det) :=
      (continuous_id.matrix_det).measurable.comp (measurable_fst.sub measurable_const)
    exact (measurableSet_singleton 0).compl.preimage hM
  rw [ae_map_iff (rp_measurable_splitAssemble e).aemeasurable hmeasS]
  have hpath := ae_isUnit_det_pathMatrix p.W (p.n - 2) p.b_lt_half E
  have hpath' : ∀ᵐ x ∂(rpLaw p.W p.b s).prod (pathLaw p.W (p.n - 2) p.b),
      IsUnit (pathMatrix x.2 - (E : ℂ) • 1).det :=
    (Measure.quasiMeasurePreserving_snd).ae hpath
  filter_upwards [hpath'] with x hx
  have h1 : (rpSplitAssemble e x).1 - (E : ℂ) • 1 =
      (pathMatrix x.2 - (E : ℂ) • 1).submatrix (rpExtEquiv e).symm (rpExtEquiv e).symm := by
    rw [show (pathMatrix x.2 - (E : ℂ) • 1).submatrix (rpExtEquiv e).symm (rpExtEquiv e).symm =
        (pathMatrix x.2).submatrix (rpExtEquiv e).symm (rpExtEquiv e).symm -
          (E : ℂ) • (1 : Matrix (Fin (p.n - 2) × Fin p.W) (Fin (p.n - 2) × Fin p.W) ℂ).submatrix
            (rpExtEquiv e).symm (rpExtEquiv e).symm from rfl, submatrix_one_equiv]
    rfl
  rw [h1, det_submatrix_equiv_self]
  exact hx.ne_zero

/-- `W⁻¹ Tr P_k M*` is the conjugate of `W⁻¹ Tr P_k M`. -/
theorem tgt_pairBlockTrace_conjTranspose (M : PairMatrix p e) (k : ZMod p.n) :
    pairBlockTrace p e Mᴴ k = conj (pairBlockTrace p e M k) := by
  unfold pairBlockTrace
  rw [map_mul, map_inv₀, map_natCast, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · rw [Matrix.conjTranspose_apply]; rfl
  · simp

/-- **Pointwise reduction of `ε` to the residual-pair observable**: for Hermitian `H^{(e)}` off the
exterior poles, `|ε_{e,k}| = |W⁻¹ Tr P_k (K_e - sa)⁻¹ - a|`. -/
theorem tgt_norm_eps_eq {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) {E : ℝ}
    (hdet : (exteriorBlock p e Hres - (E : ℂ) • 1).det ≠ 0) (k : ZMod p.n) :
    ‖tgtEps p e Hres E k‖ = ‖pairBlockTrace p e ((pairResidual p e (tgtSplit e Hres) E -
      ((splitS p : ℂ) * matchedA E) • 1)⁻¹) k - matchedA E‖ := by
  have hz : (splitS p : ℂ) * tgtMu E = conj ((splitS p : ℂ) * matchedA E) := by
    rw [tgtMu, map_mul, Complex.conj_ofReal]
  unfold tgtEps tgtR0
  rw [hz, BlockBand.Center.ctr_compressed_conj hH, tgt_pairBlockTrace_conjTranspose,
    BlockBand.Center.ctr_compressed_eq_schur hH hdet, tgt_edgeSchur_eq, tgtMu, ← map_sub,
    Complex.norm_conj]

/-- Under an edge splitting, `H^{(e)}_R - E` is a.s. invertible at every deterministic `E`. -/
theorem tgt_ae_residual_exterior_det (X : PairExtension p model) {G : X.Ω → PairMatrix p e}
    (hs : IsCenterSplitting X G) (E : ℝ) :
    ∀ᵐ ω ∂X.P, (exteriorBlock p e (X.Hm ω - embedPair p e (G ω)) - (E : ℂ) • 1).det ≠ 0 := by
  have := tgt_isProb X
  have hs0 : 0 < splitS p := BlockBand.Center.ctr_splitS_pos
  have hs1 : splitS p < 2 * min (1 - 2 * p.b) p.b := by
    have : splitS p = min (1 - 2 * p.b) p.b := rfl
    rw [this]; linarith
  have hF : Measurable (fun ω => X.Hm ω - embedPair p e (G ω)) := tgt_measurable_residual X hs.1
  have h := tgt_ae_exterior_det hs0 hs1 (tgt_isPairSplitting X hs) E
  exact ae_of_ae_map ((tgt_measurable_split e).comp hF).aemeasurable h

/-- **The law of the residual `H^{(e)}` is explicit**: under every edge splitting it is the image of
`rpLaw W b s ⊗ pathLaw W (n-2) b` (`s = min(c,b)`: the residual pair layer `V` and the exterior path
`H_R` with its port coupling `C`) under `x ↦ assemble (rpSplitAssemble x) 0`. Every remaining clause of
§7 is therefore a statement about this explicit product law (`tgt_eLpNorm_residual_eq`). -/
theorem tgt_map_residual_eq (X : PairExtension p model) {G : X.Ω → PairMatrix p e}
    (hs : IsCenterSplitting X G) :
    X.P.map (fun ω => X.Hm ω - embedPair p e (G ω)) =
      ((rpLaw p.W p.b (splitS p)).prod (pathLaw p.W (p.n - 2) p.b)).map
        (fun x => assemble p e (rpSplitAssemble e x) 0) := by
  have := tgt_isProb X
  have hs0 : 0 < splitS p := BlockBand.Center.ctr_splitS_pos
  have hs1 : splitS p < 2 * min (1 - 2 * p.b) p.b := by
    have : splitS p = min (1 - 2 * p.b) p.b := rfl
    rw [this]; linarith
  have hF : Measurable (fun ω => X.Hm ω - embedPair p e (G ω)) := tgt_measurable_residual X hs.1
  have hA : Measurable (fun ω : SplitState p e => assemble p e ω 0) :=
    (BlockBand.Layers.rsl_measurable_assemble e).comp (measurable_id.prodMk measurable_const)
  have hlaw := residualSplitLaw_holds p model e (splitS p) hs0 hs1 _ (tgt_isPairSplitting X hs)
  have h1 : X.P.map (fun ω => X.Hm ω - embedPair p e (G ω)) =
      X.P.map (fun ω => assemble p e (tgtSplit e (X.Hm ω - embedPair p e (G ω))) 0) := by
    refine Measure.map_congr ?_
    filter_upwards [tgt_ae_residual_isHermitian X hs] with ω hω
    rw [tgt_assemble_split hω, tgt_embedPair_zero, add_zero]
  have h2 : X.P.map (fun ω => assemble p e (tgtSplit e (X.Hm ω - embedPair p e (G ω))) 0) =
      (X.P.map (fun ω => tgtSplit e (X.Hm ω - embedPair p e (G ω)))).map
        (fun ω : SplitState p e => assemble p e ω 0) :=
    (Measure.map_map hA ((tgt_measurable_split e).comp hF)).symm
  rw [h1, h2, hlaw, Measure.map_map hA (rp_measurable_splitAssemble e)]
  rfl

/-- **Transfer of moments to the explicit law** (`tgt_map_residual_eq`): for every measurable
functional `Φ` of the residual, its `L^q(X.P)` norm under an edge splitting equals its norm under
`rpLaw ⊗ pathLaw (n-2)` at `H^{(e)} = assemble (rpSplitAssemble x) 0`. -/
theorem tgt_eLpNorm_residual_eq (X : PairExtension p model) {G : X.Ω → PairMatrix p e}
    (hs : IsCenterSplitting X G) {Φ : p.SiteMatrix → ℂ} (hΦ : Measurable Φ) (q : ℝ≥0∞) :
    eLpNorm (fun ω => Φ (X.Hm ω - embedPair p e (G ω))) q X.P =
      eLpNorm (fun x => Φ (assemble p e (rpSplitAssemble e x) 0)) q
        ((rpLaw p.W p.b (splitS p)).prod (pathLaw p.W (p.n - 2) p.b)) := by
  have hF : Measurable (fun ω => X.Hm ω - embedPair p e (G ω)) := tgt_measurable_residual X hs.1
  have hA : Measurable (fun x : RpSample p.W × PathSample p.W (p.n - 2) =>
      assemble p e (rpSplitAssemble e x) 0) :=
    ((BlockBand.Layers.rsl_measurable_assemble e).comp (measurable_id.prodMk measurable_const)).comp
      (rp_measurable_splitAssemble e)
  have h1 := eLpNorm_map_measure (p := q) (μ := X.P) hΦ.aestronglyMeasurable hF.aemeasurable
  have h2 := eLpNorm_map_measure (p := q)
    (μ := (rpLaw p.W p.b (splitS p)).prod (pathLaw p.W (p.n - 2) p.b))
    hΦ.aestronglyMeasurable hA.aemeasurable
  rw [tgt_map_residual_eq X hs] at h1
  rw [h1] at h2
  exact h2

theorem tgt_measurable_eps (e : ZMod p.n) (E : ℝ) (k : ZMod p.n) :
    Measurable (fun H : p.SiteMatrix => tgtEps p e H E k) := by
  have hg : Measurable (fun H : p.SiteMatrix => ((H, E), (splitS p : ℂ) * tgtMu E)) :=
    (measurable_id.prodMk measurable_const).prodMk measurable_const
  have h1 : Measurable (fun H : p.SiteMatrix => tgtR0 p e H E) :=
    Measurable.comp
      (g := fun y : (p.SiteMatrix × ℝ) × ℂ => compressedResolvent p e y.1.1 y.1.2 y.2)
      (f := fun H : p.SiteMatrix => ((H, E), (splitS p : ℂ) * tgtMu E))
      BlockBand.Center.ctr_measurable_compressed hg
  have h2 : Measurable (fun H : p.SiteMatrix => pairBlockTrace p e (tgtR0 p e H E) k) :=
    Measurable.comp (g := fun M : PairMatrix p e => pairBlockTrace p e M k)
      (f := fun H : p.SiteMatrix => tgtR0 p e H E)
      (BlockBand.Center.ctr_continuous_pairBlockTrace k).measurable h1
  exact h2.sub measurable_const

/-- **The tagged base case, first half** (`max_i ‖ε_{e,i}‖_p ≤ C_p/W`: "The base residual is
the matched-traces theorem"), for every edge splitting, from the residual-pair clause of
`MatchedTracesContract`. Constants: with `q' = max q 2` and `ε₀, C` of the residual-pair clause at
`s = min(c, b)`, `C_q = C √q'` and `W₀ = q'/ε₀`. -/
theorem tgt_eps_base (hmt : MatchedTracesContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ q : ℝ, 1 ≤ q → ∃ C W₀ : ℝ, 0 ≤ C ∧
      ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W → W₀ < (p.W : ℝ) →
      ∀ (model : p.GaussianRingModel) (e : ZMod p.n) (X : PairExtension p model)
        (G : X.Ω → PairMatrix p e), IsCenterSplitting X G → ∀ E ∈ bulkInterval κ,
        ∀ k : ZMod p.n, (k = e ∨ k = e + 1) →
          eLpNorm (fun ω => tgtEps p e (X.Hm ω - embedPair p e (G ω)) E k) (ENNReal.ofReal q)
            X.P ≤ ENNReal.ofReal (C / p.W) := by
  intro b hb0 hb1 κ T hκ q hq
  set s := min (1 - 2 * b) b with hsdef
  have hs0 : 0 < s := lt_min (by linarith) hb0
  have hs1 : s < 2 * min (1 - 2 * b) b := by linarith
  obtain ⟨ε₀, C, hε₀, hres⟩ := hmt.residualPair b hb0 hb1 κ T s hκ hs0 hs1
  set q' := max q 2 with hq'
  have hq'2 : 2 ≤ q' := le_max_right _ _
  have hqq' : q ≤ q' := le_max_left _ _
  refine ⟨max C 0 * Real.sqrt q', q' / ε₀, by positivity, ?_⟩
  intro p hpb hnT hW model e X G hs E hE k hk
  have := tgt_isProb X
  have hsp : splitS p = s := by
    rw [splitS, hsdef, ← hpb]; rfl
  have hWpos : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hqW : q' ≤ ε₀ * p.W := by
    rw [div_lt_iff₀ hε₀] at hW; linarith
  set F := fun ω => X.Hm ω - embedPair p e (G ω) with hFdef
  have hF : Measurable F := tgt_measurable_residual X hs.1
  set Pω := X.P.map (fun ω => tgtSplit e (F ω)) with hPω
  have hPs : IsPairSplitting p e model s Pω := hsp ▸ tgt_isPairSplitting X hs
  have hPprob : IsProbabilityMeasure Pω := BlockBand.Layers.rsl_isProb_of_splitting e hPs
  have hpb' : p.b = b := hpb
  have hs1' : s < 2 * min (1 - 2 * p.b) p.b := by rw [hpb']; exact hs1
  have hdet : ∀ᵐ ω ∂X.P, (exteriorBlock p e (F ω) - (E : ℂ) • 1).det ≠ 0 := by
    have h := tgt_ae_exterior_det hs0 hs1' hPs E
    exact ae_of_ae_map ((tgt_measurable_split e).comp hF).aemeasurable h
  have hpt : ∀ᵐ ω ∂X.P, ‖tgtEps p e (F ω) E k‖ ≤ ‖rpSplitObs e E s (tgtSplit e (F ω))‖ := by
    filter_upwards [tgt_ae_residual_isHermitian X hs, hdet] with ω hH hd
    have h0 : 0 ≤ rpSplitObs e E s (tgtSplit e (F ω)) := by
      unfold rpSplitObs; exact (norm_nonneg _).trans (le_max_left _ _)
    rw [tgt_norm_eps_eq hH hd, hsp, Real.norm_of_nonneg h0]
    unfold rpSplitObs
    rcases hk with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hmeasO := rp_measurable_splitObs (p := p) e E s
  calc eLpNorm (fun ω => tgtEps p e (F ω) E k) (ENNReal.ofReal q) X.P
      ≤ eLpNorm (fun ω => rpSplitObs e E s (tgtSplit e (F ω))) (ENNReal.ofReal q) X.P :=
        eLpNorm_mono_ae ((tgt_measurable_eps e E k).comp hF).aestronglyMeasurable hpt
    _ = eLpNorm (rpSplitObs e E s) (ENNReal.ofReal q) Pω := by
        have hm : AEMeasurable (fun ω => tgtSplit e (F ω)) X.P :=
          ((tgt_measurable_split e).comp hF).aemeasurable
        rw [hPω, eLpNorm_map_measure hmeasO.aestronglyMeasurable hm]
        rfl
    _ ≤ eLpNorm (rpSplitObs e E s) (ENNReal.ofReal q') Pω :=
        eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hqq')
    _ ≤ ENNReal.ofReal (C * Real.sqrt q' / p.W) :=
        hres p hpb hnT model e Pω hPs E hE q' hq'2 hqW
    _ ≤ ENNReal.ofReal (max C 0 * Real.sqrt q' / p.W) := by
        refine ENNReal.ofReal_le_ofReal ?_
        gcongr
        exact le_max_left _ _

end Law

/-!
## 6. Exact derivatives of `ε_{e,k}` (in `ξ_g` and in the energy)
-/

section Derivatives

variable {p : Parameters} {e : ZMod p.n}

/-- The spectral parameter `ζ(E) = s μ(E) = s ā(E)` of `R_e⁰`. -/
def tgtZeta (p : Parameters) (E : ℝ) : ℂ := (splitS p : ℂ) * tgtMu E

theorem tgt_zeta_im_pos {E : ℝ} (hE : |E| < 2) : 0 < (tgtZeta p E).im := by
  have hs : 0 < splitS p := BlockBand.Center.ctr_splitS_pos
  have h4 : 0 < 4 - E ^ 2 := by nlinarith [abs_lt.mp hE, sq_abs E]
  have hm : (tgtMu E).im = Real.sqrt (4 - E ^ 2) / 2 := by
    simp [tgtMu, matchedA]; ring
  rw [tgtZeta, Complex.im_ofReal_mul, hm]
  have := Real.sqrt_pos.mpr h4
  positivity

/-- `μ'(E) = conj(a'(E))`. -/
theorem tgt_hasDerivAt_mu {E : ℝ} (hE : E ∈ Set.Ioo (-2 : ℝ) 2) :
    HasDerivAt tgtMu (conj (tgtAd E)) E := by
  have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt E
    (tgt_hasDerivAt_matchedA hE)
  exact h

/-- The block trace `M ↦ W⁻¹ Tr P_k (M|_{S_e})` of a site matrix, as a real-linear map. -/
def tgtTraceCLM (e k : ZMod p.n) : p.SiteMatrix →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (p.W : ℂ)⁻¹ * ∑ x : PairSite p e, if x.1.1 = k then M x.1 x.1 else 0
      map_add' := fun A B => by
        simp only [Matrix.add_apply]
        rw [← mul_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        split_ifs <;> simp
      map_smul' := fun r A => by
        simp only [Matrix.smul_apply, RingHom.id_apply, Complex.real_smul]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        split_ifs <;> ring }

theorem tgt_eps_eq_trace (Hres : p.SiteMatrix) (E : ℝ) (k : ZMod p.n) :
    tgtEps p e Hres E k =
      tgtTraceCLM e k (BlockBand.Center.ctrFull p e Hres E (tgtZeta p E))⁻¹ - tgtMu E := rfl

/-- `y ↦ f(y)⁻¹` has derivative `-f(x)⁻¹ f'(x) f(x)⁻¹` where `f(x)` is invertible. -/
theorem tgt_hasDerivAt_inv_comp {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ℝ → Matrix ι ι ℂ}
    {f' : Matrix ι ι ℂ} {x : ℝ} (hf : HasDerivAt f f' x) (hU : IsUnit (f x).det) :
    HasDerivAt (fun y => (f y)⁻¹) (-((f x)⁻¹ * f' * (f x)⁻¹)) x := by
  have e : (fun y : ℝ => (f y)⁻¹) = fun y : ℝ => Ring.inverse (f y) := by
    funext y; rw [Matrix.nonsing_inv_eq_ringInverse]
  rw [e]
  have hU' : IsUnit (f x) := (Matrix.isUnit_iff_isUnit_det _).mpr hU
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) hU'.unit
  rw [IsUnit.unit_spec] at hinv
  have h3 := hinv.comp_hasDerivAt x hf
  have hinvN : (↑hU'.unit⁻¹ : Matrix ι ι ℂ) = (f x)⁻¹ := by
    rw [← Ring.inverse_unit, IsUnit.unit_spec, Matrix.nonsing_inv_eq_ringInverse]
  convert h3 using 1
  · rfl
  rw [_root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, hinvN]

/-- The pair residual `K_e` of a Hermitian residual is Hermitian at real energies. -/
theorem tgt_edgeSchur_isHermitian {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) (E : ℝ) :
    (edgeSchur p e Hres E).IsHermitian := by
  have hext : (exteriorBlock p e Hres).IsHermitian := by
    ext x y
    simp only [Matrix.conjTranspose_apply, exteriorBlock]
    exact hH.apply x.1 y.1
  have hpair : (pairBlock p e Hres).IsHermitian := by
    ext x y
    simp only [Matrix.conjTranspose_apply, pairBlock]
    exact hH.apply x.1 y.1
  have hE1 : ∀ {ι : Type _} [Fintype ι] [DecidableEq ι],
      ((E : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian := by
    intro ι _ _
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  have hN : ((exteriorBlock p e Hres - (E : ℂ) • 1)⁻¹).IsHermitian := (hext.sub hE1).inv
  unfold edgeSchur physicalCoareaF physicalCoareaResolvent
  refine (hpair.sub ?_).sub hE1
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hN.eq, Matrix.mul_assoc]

/-- **The full matrix `H^{(e)} - E - ζ P_S` is invertible** for Hermitian `H^{(e)}`, `Im ζ > 0`, off
the exterior poles (Schur complement: `K_e - ζ` is invertible since `K_e` is Hermitian). -/
theorem tgt_ctrFull_det_ne {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) {E : ℝ}
    (hdet : (exteriorBlock p e Hres - (E : ℂ) • 1).det ≠ 0) {ζ : ℂ} (hζ : 0 < ζ.im) :
    (BlockBand.Center.ctrFull p e Hres E ζ).det ≠ 0 := by
  intro hF
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hF
  have hext : ∀ x : ExteriorSite p e, (BlockBand.Center.ctrFull p e Hres E ζ *ᵥ v) x.1 = 0 :=
    fun x => by rw [hv]; rfl
  obtain ⟨hue, hpair⟩ := BlockBand.Center.ctr_schur_elim hH hdet ζ v hext
  have hup : (fun z : PairSite p e => v z.1) ≠ 0 := by
    intro h0
    apply hv0
    funext y
    by_cases hy : y.1 = e ∨ y.1 = e + 1
    · exact congrFun h0 ⟨y, hy⟩
    · have := congrFun hue ⟨y, hy⟩
      rw [h0, Matrix.mulVec_zero, neg_zero] at this
      exact this
  have hK : (edgeSchur p e Hres E - ζ • 1).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hup, ?_⟩
    funext x
    rw [← hpair x, hv]
    rfl
  have hU := dcv_K_isUnit (tgt_edgeSchur_isHermitian (e := e) hH E) hζ
  have hneg : edgeSchur p e Hres E - ζ • 1 = -(ζ • 1 - edgeSchur p e Hres E) := by abel
  rw [hneg, Matrix.det_neg] at hK
  exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) hU.ne_zero) hK

/-- **The `ξ_g`-derivative of `ε_{e,k}`** (exact form): where `M = H^{(e)} - E - ζP_S` is invertible,
`t ↦ ε_{e,k}(H^{(e)} + t P_{S_g})` has derivative `-W⁻¹ Tr P_k [M⁻¹ P_{S_g} M⁻¹]_{SS}` at `0`
(off the exterior poles this is `-W⁻¹ Tr P_k R_e⁰ B_{eg} R_e⁰`). -/
theorem tgt_hasDerivAt_eps_xi (g : ZMod p.n) {Hres : p.SiteMatrix} {E : ℝ}
    (hM : (BlockBand.Center.ctrFull p e Hres E (tgtZeta p E)).det ≠ 0) (k : ZMod p.n) :
    HasDerivAt (fun t : ℝ => tgtEps p e (Hres + (t : ℂ) • pairProjector p g) E k)
      (tgtTraceCLM e k (-((BlockBand.Center.ctrFull p e Hres E (tgtZeta p E))⁻¹ *
        pairProjector p g * (BlockBand.Center.ctrFull p e Hres E (tgtZeta p E))⁻¹))) 0 := by
  set M := BlockBand.Center.ctrFull p e Hres E (tgtZeta p E) with hMdef
  have hf : HasDerivAt (fun t : ℝ => M + (t : ℂ) • pairProjector p g) (pairProjector p g) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (pairProjector p g)).const_add M
    simpa [Complex.coe_smul] using this
  have hinv := tgt_hasDerivAt_inv_comp hf (by simpa using isUnit_iff_ne_zero.mpr hM)
  simp only [zero_smul, add_zero, Complex.ofReal_zero] at hinv
  have h := ((tgtTraceCLM e k).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hinv).sub_const (tgtMu E)
  have hfun : (fun t : ℝ => tgtEps p e (Hres + (t : ℂ) • pairProjector p g) E k) =
      fun t : ℝ => tgtTraceCLM e k ((M + (t : ℂ) • pairProjector p g)⁻¹) - tgtMu E := by
    funext t
    rw [tgt_eps_eq_trace]
    congr 3
    simp only [hMdef, BlockBand.Center.ctrFull]
    abel
  rw [hfun]
  exact h

/-- **The energy derivative of `ε_{e,k}`** (exact form, at the pair level): for
`E ∈ (-2, 2)` and `M = H^{(e)} - E - ζ(E) P_S` invertible, `E' ↦ ε_{e,k}(E')` has derivative
`W⁻¹ Tr P_k [M⁻¹ (1 + ζ'(E) P_S) M⁻¹]_{SS} - μ'(E)`, `ζ' = s ā'`, `μ' = ā'`, `a' = a²/(1-a²)`. -/
theorem tgt_hasDerivAt_eps_energy (Hres : p.SiteMatrix) {E : ℝ} (hE : E ∈ Set.Ioo (-2 : ℝ) 2)
    (hM : (BlockBand.Center.ctrFull p e Hres E (tgtZeta p E)).det ≠ 0) (k : ZMod p.n) :
    HasDerivAt (fun E' : ℝ => tgtEps p e Hres E' k)
      (tgtTraceCLM e k (-((BlockBand.Center.ctrFull p e Hres E (tgtZeta p E))⁻¹ *
        (-(1 : p.SiteMatrix) - ((splitS p : ℂ) * conj (tgtAd E)) • pairProjector p e) *
          (BlockBand.Center.ctrFull p e Hres E (tgtZeta p E))⁻¹)) - conj (tgtAd E)) E := by
  have hmu := tgt_hasDerivAt_mu hE
  have hzeta : HasDerivAt (tgtZeta p) ((splitS p : ℂ) * conj (tgtAd E)) E := by
    have := hmu.const_mul (splitS p : ℂ)
    exact this
  have hE' : HasDerivAt (fun E' : ℝ => ((E' : ℂ) • (1 : p.SiteMatrix))) (1 : p.SiteMatrix) E := by
    have := (hasDerivAt_id E).smul_const (1 : p.SiteMatrix)
    simpa [Complex.coe_smul] using this
  have hf : HasDerivAt (fun E' : ℝ => BlockBand.Center.ctrFull p e Hres E' (tgtZeta p E'))
      (-(1 : p.SiteMatrix) - ((splitS p : ℂ) * conj (tgtAd E)) • pairProjector p e) E := by
    have h2 := hzeta.smul_const (pairProjector p e)
    have h3 := (hE'.const_sub Hres).sub h2
    convert h3 using 1
    funext E'
    rfl
  have hinv := tgt_hasDerivAt_inv_comp hf (isUnit_iff_ne_zero.mpr hM)
  have h := ((tgtTraceCLM e k).hasFDerivAt.comp_hasDerivAt E hinv).sub hmu
  exact h

end Derivatives

/-!
## 7. Almost-sure differentiability, the remaining clauses, and the assembly
-/

section Assembly

variable {p : Parameters} {model : p.GaussianRingModel} {e : ZMod p.n}

/-- **The energy derivative exists almost surely** (first part of `FullEnergyTraceStatement`):
under an edge splitting, at deterministic `E ∈ bulkInterval κ`, a.s. `E' ↦ ε_{e,k}(E')` is
differentiable at `E` (with the exact derivative of `tgt_hasDerivAt_eps_energy`). -/
theorem tgt_ae_eps_energy_hasDerivAt (X : PairExtension p model) {G : X.Ω → PairMatrix p e}
    (hs : IsCenterSplitting X G) {κ : ℝ} (hκ : 0 < κ) {E : ℝ} (hE : E ∈ bulkInterval κ)
    (k : ZMod p.n) :
    ∀ᵐ ω ∂X.P, (BlockBand.Center.ctrFull p e (X.Hm ω - embedPair p e (G ω)) E (tgtZeta p E)).det ≠ 0 ∧
      DifferentiableAt ℝ (fun E' : ℝ => tgtEps p e (X.Hm ω - embedPair p e (G ω)) E' k) E := by
  have hE2 : |E| < 2 := abs_lt_two_of_mem_bulkInterval hκ hE
  have hEI : E ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [(abs_lt.mp hE2).1], (abs_lt.mp hE2).2⟩
  filter_upwards [tgt_ae_residual_isHermitian X hs, tgt_ae_residual_exterior_det X hs E]
    with ω hH hd
  have hM := tgt_ctrFull_det_ne (e := e) hH hd (tgt_zeta_im_pos (p := p) hE2)
  exact ⟨hM, (tgt_hasDerivAt_eps_energy _ hEI hM k).differentiableAt⟩

/-- **The `λ` bound** (the tagged base case, second half; proved by `tgtLambdaBound_holds`):
`‖λ_{eg}‖_q ≤ C_q` for `g ≠ e`. Law, domain, quantifier order as in `TaggedTraceStatement`.
Route: `λ_{eg} = W⁻¹ Tr R* (P_g)_{SS} R + W⁻¹ Tr R* C*(H_R - E)⁻¹(P_g)_{RR}(H_R - E)⁻¹C R`
(`tgtB`, `tgt_tgtB_posSemidef`); the first term is `≤ 2/(Im sμ)²`; the second is the final trace
pairing of the residual pair layer with the tagged clock `Y` of the exterior path (`P_g` covers at
most two path blocks), bounded by the tagged clock moments (`TaggedClockInput`,
`taggedClockInput_holds`) and a weighted bound for the residual pair layer. -/
def TgtLambdaBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ q : ℝ, 1 ≤ q → ∃ C W₀ : ℝ,
    ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W → W₀ < (p.W : ℝ) →
    ∀ (model : p.GaussianRingModel) (e : ZMod p.n) (X : PairExtension p model)
      (G : X.Ω → PairMatrix p e), IsCenterSplitting X G → ∀ E ∈ bulkInterval κ,
      ∀ g : ZMod p.n, g ≠ e →
        eLpNorm (fun ω => tgtLambda p e g (X.Hm ω - embedPair p e (G ω)) E) (ENNReal.ofReal q)
          X.P ≤ ENNReal.ofReal C

/-- **The tagged decay bound** (proved by `tgtDecayBound_holds`):
`‖∂_{ξ_g} ε_{e,k}‖_q ≤ C_q(ρ^{d(e,g)} + W^{-1/2})` for `g ≠ e`, with `ρ < 1` chosen after
`b, κ, T`. Law, domain, quantifier order as in `TaggedTraceStatement`. The exact derivative is
`tgt_hasDerivAt_eps_xi` (`-W⁻¹ Tr P_k [M⁻¹ P_{S_g} M⁻¹]_{SS}`). Route: the derivative
recursion `v = d + (c + b²a²)Qv` with the strict contraction (`strictContraction_holds`), the
differentiated mean equations with the covariance derivative of
the differentiated-covariance lemma (`diffCovarianceFamily_holds'`, curved families), the
filtration by exposed physical blocks of `H^{(e)}`, tagged steps by the matched-traces theorem and the
clock bounds (`taggedClockInput_holds`), iteration from the last tagged layer, and the final
residual pair with its fixed stability gap and source `B_{eg} ⪰ 0`. -/
def TgtDecayBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ q : ℝ, 1 ≤ q → ∃ C W₀ : ℝ,
      ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W → W₀ < (p.W : ℝ) →
      ∀ (model : p.GaussianRingModel) (e : ZMod p.n) (X : PairExtension p model)
        (G : X.Ω → PairMatrix p e), IsCenterSplitting X G → ∀ E ∈ bulkInterval κ,
        ∀ g : ZMod p.n, g ≠ e → ∀ k : ZMod p.n, (k = e ∨ k = e + 1) →
          eLpNorm (fun ω => tgtXiDeriv p (fun H => tgtEps p e H E k) g
              (X.Hm ω - embedPair p e (G ω))) (ENNReal.ofReal q) X.P ≤
            ENNReal.ofReal (C * (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ))))

/-- **Assembly of the tagged-trace lemma** from the proved clauses (the tagged base case for `ε`,
from the matched-traces theorem; `∂_{ξ_e} = 0`) and the two clauses `TgtLambdaBound` and
`TgtDecayBound`. `ConditionalBlockGUECount` and `GaussianLpGradient` enter through
`matchedTraces_holds`. -/
theorem taggedTrace_of_open (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : Internal.Contracts.Inputs.GaussianLpGradient) (hlam : TgtLambdaBound)
    (hdec : TgtDecayBound) : TaggedTraceStatement := by
  refine ⟨?_, fun p e V G0 ξ E k => tgt_xi_e_hasDerivAt_zero e V G0 ξ E k⟩
  intro b hb0 hb1 κ T hκ
  obtain ⟨ρ, hρ0, hρ1, hdq⟩ := hdec b hb0 hb1 κ T hκ
  refine ⟨ρ, hρ0, hρ1, fun q hq => ?_⟩
  obtain ⟨C1, W1, hC1, h1⟩ := tgt_eps_base (matchedTraces_holds hcount hgrad) b hb0 hb1 κ T hκ q hq
  obtain ⟨C2, W2, h2⟩ := hlam b hb0 hb1 κ T hκ q hq
  obtain ⟨C3, W3, h3⟩ := hdq q hq
  refine ⟨max C1 (max C2 C3), max W1 (max W2 W3), ?_⟩
  intro p hpb hnT hW model e X G hs E hE
  have hW1 : W1 < (p.W : ℝ) := lt_of_le_of_lt (le_max_left _ _) hW
  have hW2 : W2 < (p.W : ℝ) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hW
  have hW3 : W3 < (p.W : ℝ) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hW
  have hWpos : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hC1' : C1 ≤ max C1 (max C2 C3) := le_max_left _ _
  have hC2' : C2 ≤ max C1 (max C2 C3) := (le_max_left _ _).trans (le_max_right _ _)
  have hC3' : C3 ≤ max C1 (max C2 C3) := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨fun k hk => ?_, fun g hg => ?_, fun g hg k hk => ?_⟩
  · refine (h1 p hpb hnT hW1 model e X G hs E hE k hk).trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right hC1' hWpos.le
  · exact (h2 p hpb hnT hW2 model e X G hs E hE g hg).trans (ENNReal.ofReal_le_ofReal hC2')
  · refine (h3 p hpb hnT hW3 model e X G hs E hE g hg k hk).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right hC3' (by positivity)

end Assembly

end BlockBand.Layers
