module

public import BlockBand.SourceProcess.PhysApprox.IdentK.BridgeAux

/-!
# Proof of `KGBridge`

Measure: the candidate's `Q`; filtration: the raw natural filtration of `complexObs`.

* Pointwise algebra (`x_e = Ŷ_e − A_e`): `funKG = funKY − A·funK1` (`funKG_eqK`) and
  `lamKG = lamKY − A·lamK1 − β·funK1` (`lamKG_eqK`), `β = lamA χ e`.
* **Path identity** `genKG_eq_addK`: for every `ω` and `t`, `genKG = genKY + D`, with
  `D_t = ∫_0^t β X − (∫_0^t β) X_t` (`ibpK`), `X = genK1 a`, `β = betaK` (product rule for
  primitives, `ibp_algebraK`). No almost-sure condition.
* Measurability: `stronglyMeasurable_genK1K` (via the drift-free state `phiK ∘ wK`, `genK1`
  being A-blind), past measurability of `β` and of `∫_0^t β`, joint measurability of `β`;
  a.s. bound of `β` from feasibility (`exists_bound_betaK`).
* **`kGBridge_holds : KGBridge`**: `genK1` is upgraded to all times (`isTestedMart_of_off`), so
  `D` has tested increments (`isTestedMart_ibp`); then `genKY + D` off the births.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.PhysApprox.B3.Ident2
open scoped NNReal ENNReal ComplexConjugate

variable {K np : ℕ} {Ω : Type*}

/-!
## Definitions
-/

/-- The cut drift integrand `β_r = b_e(G_r) χ(s(Y_r))` (`lamA`) as a process. -/
def betaK (χ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GSt K np)
    (e : GIdx K np) (r : ℝ≥0) (ω : Ω) : ℂ :=
  lamA χ b E e (gramJ b s τ m r, gY b s τ m G r ω)

/-- The process `D_t = ∫_0^t β X − (∫_0^t β) X_t` of `isTestedMart_ibp`. -/
def ibpK (β X : ℝ≥0 → Ω → ℂ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  (∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω * X u.toNNReal ω) -
    (∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω) * X t ω

/-- The raw drift-free data `(Y_u, Y^𝒦_u, Y_0, Y^𝒦_0)`. -/
def wK (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GSt K np) (Kc : ℝ≥0 → Ω → KSt np)
    (u : ℝ≥0) (ω : Ω) : GSt K np × KSt np × GSt K np × KSt np :=
  (gY b s τ m G u ω, yKp E s τ m Kc u ω, gY b s τ m G 0 ω, yKp E s τ m Kc 0 ω)

/-- The drift-free state built from the raw data (drift slot `0`). -/
def phiK (w : GSt K np × KSt np × GSt K np × KSt np) : ZK K np :=
  ((w.1, 0, w.2.2.1), w.2.1, fun a => w.2.1 a.1 a.2 - w.2.2.2 a.1 a.2, w.2.2.2)

theorem continuous_phiK : Continuous (phiK (K := K) (np := np)) := by
  unfold phiK
  refine (continuous_fst.prodMk (continuous_const.prodMk
    (continuous_fst.comp (continuous_snd.comp continuous_snd)))).prodMk
    ((continuous_fst.comp continuous_snd).prodMk ((continuous_pi fun a => ?_).prodMk
      (continuous_snd.comp (continuous_snd.comp continuous_snd))))
  exact ((continuous_entry a).comp (continuous_fst.comp continuous_snd)).sub
    ((continuous_entry a).comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))

theorem continuous_lamAK {χ : ℝ → ℝ} (hχ : Continuous χ) (b E : ℝ) (e : GIdx K np) :
    Continuous (lamA χ b E e) :=
  ((continuous_drE b E e).comp (continuous_snd.add continuous_fst)).mul
    ((continuous_cutC hχ).comp continuous_snd)

/-!
## Pointwise algebra
-/

theorem funKG_eqK (χ ξ : ℝ → ℝ) (a : KIdx np) (e : GIdx K np) (z : ZK K np) :
    funKG χ ξ a e z = funKY χ ξ a e z - (kHatE e z - z.1.2.1 e) * funK1 χ ξ a z := by
  unfold funKG funKY funK1
  ring

theorem lamKG_eqK (χ ξ : ℝ → ℝ) (b E : ℝ) (a : KIdx np) (e : GIdx K np) (J : GSt K np)
    (z : ZK K np) :
    lamKG χ ξ b E a e (J, z) = lamKY χ ξ b E a e (J, z) -
      (kHatE e z - z.1.2.1 e) * lamK1 χ ξ b E a (J, z) -
        lamA χ b E e (J, z.1.1) * funK1 χ ξ a z := by
  simp only [lamKG, lamKY, lamK1, lamA, funK1, cutZ, cut0, kHatP, kHatE, pyG, pyG0, pyK, pyK0,
    pxK, pxG, pH]
  ring

variable {b E s : ℝ} {τ m : Fin np → ℝ} {G : ℝ≥0 → Ω → GSt K np} {Kc : ℝ≥0 → Ω → KSt np}

theorem kHatE_sub_stZK (χ : ℝ → ℝ) (e : GIdx K np) (u : ℝ≥0) (ω : Ω) :
    kHatE e (stZK χ b E s τ m G Kc u ω) - (stZK χ b E s τ m G Kc u ω).1.2.1 e =
      genA χ b E s τ m G e u ω := by
  simp only [kHatE, stZK, stZ, genX]
  ring

/-!
## The path identity
-/

section PathId

variable (hc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u)
  (hkc : ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u)
  {χ ξ : ℝ → ℝ} (hχ : Continuous χ) (hχ1 : Continuous (deriv χ))
  (hχ2 : Continuous (deriv (deriv χ))) (hξ : Continuous ξ) (hξ1 : Continuous (deriv ξ))
  (hξ2 : Continuous (deriv (deriv ξ)))
include hc hkc hχ hχ1 hχ2 hξ hξ1 hξ2

/-- **Along every path, `genKG = genKY + D`**, `D = ibpK β (genK1 a)`, `β = betaK χ e`. -/
theorem genKG_eq_addK (a : KIdx np) (e : GIdx K np) (t : ℝ≥0) (ω : Ω) :
    genKG χ ξ b E s τ m G Kc a e t ω = genKY χ ξ b E s τ m G Kc a e t ω +
      ibpK (betaK χ b E s τ m G e) (genK1 χ ξ b E s τ m G Kc a) t ω := by
  have hZ := continuous_stZK hc hkc hχ ω
  have hY : Continuous fun u => gY b s τ m G u ω := hc ω
  have hlA := continuous_lamAK (K := K) (np := np) hχ b E e
  have hl1 := continuous_lamK1 (K := K) hχ hχ1 hχ2 hξ hξ1 hξ2 b E a
  have hlY := continuous_lamKY hχ hχ1 hχ2 hξ hξ1 hξ2 b E a e
  have hf1 := continuous_funK1 (K := K) hχ hξ a
  have hprim : ∀ (g : ℝ → ℂ) (x : ℝ), 0 < x →
      ∫ u in Ioc (0 : ℝ) (x.toNNReal : ℝ), g u = ∫ u in (0 : ℝ)..x, g u := fun g x hx => by
    rw [Real.coe_toNNReal x hx.le]
    exact (intervalIntegral.integral_of_le hx.le).symm
  have key := ibp_algebraK
    (β := fun r => lamA χ b E e (gramJ b s τ m r.toNNReal, gY b s τ m G r.toNNReal ω))
    (ℓ := fun r => lamK1 χ ξ b E a (gramJ b s τ m r.toNNReal, stZK χ b E s τ m G Kc r.toNNReal ω))
    (lY := fun r =>
      lamKY χ ξ b E a e (gramJ b s τ m r.toNNReal, stZK χ b E s τ m G Kc r.toNNReal ω))
    (f := fun r => funK1 χ ξ a (stZK χ b E s τ m G Kc r.toNNReal ω))
    (A := fun r => genA χ b E s τ m G e r.toNNReal ω)
    (L := fun r => ∫ u in Ioc (0 : ℝ) r.toNNReal,
      lamK1 χ ξ b E a (gramJ b s τ m u.toNNReal, stZK χ b E s τ m G Kc u.toNNReal ω))
    (path_smK hY hlA) (path_smK hZ hl1) (path_smK hZ hlY)
    (hf1.comp (hZ.comp continuous_real_toNNReal)) (path_bddK hY hlA) (path_bddK hZ hl1)
    (path_bddK hZ hlY) (fun x _ => path_rcK hY hlA x) (fun x _ => path_rcK hZ hl1 x)
    (fun x hx => hprim _ x hx) (fun x hx => hprim _ x hx) (NNReal.coe_nonneg t)
    (At := genA χ b E s τ m G e t ω)
    (Lt := ∫ u in Ioc (0 : ℝ) t,
      lamK1 χ ξ b E a (gramJ b s τ m u.toNNReal, stZK χ b E s τ m G Kc u.toNNReal ω))
    (intervalIntegral.integral_of_le t.2).symm (intervalIntegral.integral_of_le t.2).symm
    (funKY χ ξ a e (stZK χ b E s τ m G Kc t ω)) (funK1 χ ξ a (stZK χ b E s τ m G Kc t ω))
  refine Eq.trans ?_ (key.trans rfl)
  unfold genKG genProcK
  rw [funKG_eqK, kHatE_sub_stZK]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  rw [lamKG_eqK, kHatE_sub_stZK]
  rfl

end PathId

/-!
## Measurability and bounds
-/

/-- **`genK1 a t` is strongly measurable** (it reads the drift-free state `phiK (wK …)`). -/
theorem stronglyMeasurable_genK1K [MeasurableSpace Ω] (hGm : ∀ u, StronglyMeasurable (G u))
    (hKm : ∀ u, StronglyMeasurable (Kc u))
    (hc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u)
    (hkc : ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u) {χ ξ : ℝ → ℝ}
    (hχ : Continuous χ) (hχ1 : Continuous (deriv χ)) (hχ2 : Continuous (deriv (deriv χ)))
    (hξ : Continuous ξ) (hξ1 : Continuous (deriv ξ)) (hξ2 : Continuous (deriv (deriv ξ)))
    (a : KIdx np) (t : ℝ≥0) : StronglyMeasurable (genK1 χ ξ b E s τ m G Kc a t) := by
  have hwc : ∀ ω, Continuous fun u => wK b E s τ m G Kc u ω := fun ω =>
    (hc ω).prodMk ((hkc ω).prodMk continuous_const)
  have hwm : ∀ u, StronglyMeasurable (wK b E s τ m G Kc u) := fun u =>
    ((hGm u).sub stronglyMeasurable_const).prodMk (((hKm u).sub stronglyMeasurable_const).prodMk
      (((hGm 0).sub stronglyMeasurable_const).prodMk ((hKm 0).sub stronglyMeasurable_const)))
  have hf1 := continuous_funK1 (K := K) hχ hξ a
  have hl1 := continuous_lamK1 (K := K) hχ hχ1 hχ2 hξ hξ1 hξ2 b E a
  have e : genK1 χ ξ b E s τ m G Kc a t = fun ω => funK1 χ ξ a (phiK (wK b E s τ m G Kc t ω)) -
      ∫ r in Ioc (0 : ℝ) t, lamK1 χ ξ b E a
        (gramJ b s τ m r.toNNReal, phiK (wK b E s τ m G Kc r.toNNReal ω)) := rfl
  rw [e]
  exact ((hf1.comp continuous_phiK).comp_stronglyMeasurable (hwm t)).sub
    (stronglyMeasurable_integral_gramJK (Λ := fun p => lamK1 χ ξ b E a (p.1, phiK p.2))
      (hl1.comp (continuous_fst.prodMk (continuous_phiK.comp continuous_snd))) hwc t
      fun u _ => hwm u)

/-- **`β` is a.s. bounded**, from feasibility. -/
theorem exists_bound_betaK [MeasurableSpace Ω] {Q : Measure Ω}
    (hfe : ∀ᵐ ω ∂Q, ∀ u, GramFeasible (srcSignature K (Fin np)) (G u ω))
    {χ : ℝ → ℝ} (hχ : Continuous χ) {Rχ : ℝ}
    (hR : ∀ c, Rχ < |c| → χ c = 0 ∧ deriv χ c = 0 ∧ deriv (deriv χ) c = 0) (e : GIdx K np) :
    ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ r, ‖betaK χ b E s τ m G e r ω‖ ≤ C := by
  obtain ⟨CJ, hCJ⟩ := exists_norm_gramJ_le (K := K) b s τ m
  set BY := 2 * (Rχ + (Fintype.card (SrcCol K (Fin np)) : ℝ) * CJ) + CJ
  obtain ⟨C, hC⟩ := exists_bound_finite_compact (continuous_lamAK hχ b E e)
    (finite_range_gramJ (K := K) b s τ m) (isCompact_box (K := K) (np := np) BY)
  refine ⟨max C 0, hfe.mono fun ω hω r => ?_⟩
  by_cases h0 : betaK χ b E s τ m G e r ω = 0
  · rw [h0, norm_zero]; exact le_max_right _ _
  · exact (hC _ ⟨r, rfl⟩ _ fun e' => entry_sub_le_of_feasible (hω r) (hCJ r)
      (abs_trRe_gramJ_le hCJ r) (lamA_ne_zero hR b E e h0) e').trans (le_max_left _ _)

/-!
## The bridge
-/

/-- **`KGBridge` holds.** -/
theorem kGBridge_holds : KGBridge := by
  intro hTL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hPr χ ξ hχ3 hχs hξ3 hξs a e
    h1 hY
  obtain ⟨hD, hlim, hA, hne, hφ, ⟨hQ, htm, hGm, hKm, hc, hkc⟩, hfdd⟩ := hPr
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, hs, -, hh0, -, -⟩ := id hD
  have hobs := measurable_complexObs htm hGm hKm
  have hcap := hφ.eventually (eventually_capProb_ne_zero hTL hb0 hb hE1 hE2 hlim hs hh0 hA hne)
  have hfe := ae_feasible_all hD hφ hfdd hobs hcap hc
  obtain ⟨hχc, hχd, hχdd⟩ := cut_continuity hχ3
  obtain ⟨hξc, hξd, hξdd⟩ := cut_continuity hξ3
  obtain ⟨Rχ, hRχ⟩ := exists_cut_radius hχs
  obtain ⟨Rξ, hRξ⟩ := exists_cut_radius hξs
  have hlA := continuous_lamAK (K := K) (np := np) hχc b E e
  have hf1 := continuous_funK1 (K := K) hχc hξc a
  have hl1 := continuous_lamK1 (K := K) hχc hχd hχdd hξc hξd hξdd b E a
  have hXc := continuous_genProcK hc hkc hχc hf1 hl1
  have hXb := exists_bound_genProcK (b := b) (E := E) (s := s) (τ := τ) (m := m) (Kc := Kc) hfe
    hχc hRχ hf1 hl1 (fun z hz => (KTest.k1 a).fn_cutReg hRχ hRξ hz)
    (fun p hp => (KTest.k1 a).lam_cutReg hRχ hRξ b E hp)
  have hX : IsTestedMart Q (complexObs tseq G Kc) (genK1 χ ξ b E s τ m G Kc a) :=
    isTestedMart_of_off (birthTimes_finite s τ) hobs (tendsto_complexObs_right hc hkc) hXc hXb h1
  have hDt := isTestedMart_ibp hobs hX
    (stronglyMeasurable_genK1K hGm hKm hc hkc hχc hχd hχdd hξc hξd hξdd a)
    hXc hXb (β := betaK χ b E s τ m G e)
    (fun r => hlA.comp_stronglyMeasurable
      (stronglyMeasurable_const.prodMk
        ((stronglyMeasurable_G_pastC r).sub stronglyMeasurable_const)))
    (fun t => stronglyMeasurable_integral_gramJK (mΩ := pastSigma (complexObs tseq G Kc) t) hlA
      (Z := gY b s τ m G) hc t fun u hu =>
        ((stronglyMeasurable_G_pastC u).sub stronglyMeasurable_const).mono (pastSigma_mono _ hu))
    (stronglyMeasurable_jointK hlA hc fun u => (hGm u).sub stronglyMeasurable_const)
    (exists_bound_betaK hfe hχc hRχ e)
  have heq : genKG χ ξ b E s τ m G Kc a e = fun t ω => genKY χ ξ b E s τ m G Kc a e t ω +
      ibpK (betaK χ b E s τ m G e) (genK1 χ ξ b E s τ m G Kc a) t ω :=
    funext fun t => funext fun ω => genKG_eq_addK hc hkc hχc hχd hχdd hξc hξd hξdd a e t ω
  rw [heq]
  exact isTestedMartOff_addK hobs hY (isTestedMartOff_of_testedK _ hDt)

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK
