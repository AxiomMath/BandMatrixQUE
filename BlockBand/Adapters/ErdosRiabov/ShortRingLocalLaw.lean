module

public import Mathlib
public import BlockBand.Adapters.ErdosRiabov.RingNativeLaw
public import BlockBand.Adapters.ErdosRiabov.ShortRingLocalLawDomain
public import BlockBand.Adapters.ErdosRiabov.ShortRingAdmissibility
public import BlockBand.External.ErdosRiabov.Statement

/-!
# The short-ring entrywise local law from Erdős–Riabov Theorem 3.3 (3.17)

* constants: from the fixed `b, ζ₀, δ₀, κ, C₀, D`, the parameters
  `shortRingParameters` have `ζ₀, δ₀`, phase constant `κ' = min κ 1`, `C₀`, `C_W = 1`,
  `C₂ = 1`, moment bounds `ringMomentBound` and the admissibility constants `C₁, c₂, D'` of
  `shortRingAdmissibility_holds` (at `b, δ₀, κ', C₀, D`); then `N₀` is the threshold
  of `hER` at `ξ = ε`, `D = D₁`;
* law: `ringNativeLaw` presents every physical ring as an Erdős–Riabov law on `Fin N`
  (`N = nW`), whose matrix read at the physical sites has the law of every physical model
  (`model_law_eq_ringPhys`);
* control: `polynomialControl N W D` is admissible for `ringProfile p = shortRingProfile`;
* domain: the bulk box lies in the spectral domain (`spectralDomain_of_bulk`);
* event: at `u = e_{siteIndex x}`, `v = e_{siteIndex y}` the isotropic bad event is the
  preimage of the entrywise bad event (`vectorControl_single`, `matrixPairing_single`,
  `polynomialControl_siteFinEquiv`, reindexing of the resolvent).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov

open MeasureTheory BlockBand.External BlockBand.Internal.Contracts.Inputs

/-- The ER parameters used for the short ring. -/
def shortRingParameters (ζ₀ δ₀ κ C₀ C₁ c₂ D' : ℝ) (hδ : 0 < δ₀) (hδζ : δ₀ < ζ₀)
    (hκ : 0 < κ) (hC₀ : 1 ≤ C₀) (hC₁ : 1 ≤ C₁) (hc₂ : 0 < c₂) (hD' : 0 < D') :
    ErdosRiabov.ModelParameters where
  zeta0 := ζ₀
  delta0 := δ₀
  kappa := min κ 1
  C0 := C₀
  CW := 1
  C1 := C₁
  C2 := 1
  c2 := c₂
  DPrime := D'
  momentBound := ringMomentBound
  zeta0_pos := hδ.trans hδζ
  delta0_pos := hδ
  delta0_lt_zeta0 := hδζ
  kappa_pos := lt_min hκ one_pos
  C0_ge_one := hC₀
  CW_pos := one_pos
  C1_ge_one := hC₁
  C2_pos := one_pos
  c2_pos := hc₂
  DPrime_pos := hD'

/-- The entrywise bad event is measurable (resolvent entries are measurable: `G = det⁻¹ adj`). -/
theorem measurableSet_resolventBad (p : Parameters) (c : ℝ) (z w : ℂ) (x y : p.Site) :
    MeasurableSet {H : p.SiteMatrix |
      c < ‖(H - z • (1 : p.SiteMatrix))⁻¹ x y - w‖} := by
  have hfun : (fun H : p.SiteMatrix => (H - z • (1 : p.SiteMatrix))⁻¹ x y) =
      fun H => ((H - z • (1 : p.SiteMatrix)).det)⁻¹ *
        (H - z • (1 : p.SiteMatrix)).adjugate x y := by
    funext H
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rfl
  have hc1 : Continuous fun H : p.SiteMatrix => (H - z • (1 : p.SiteMatrix)).det :=
    (continuous_id.sub continuous_const).matrix_det
  have hc2 : Continuous fun H : p.SiteMatrix => (H - z • (1 : p.SiteMatrix)).adjugate x y :=
    (continuous_id.sub continuous_const).matrix_adjugate.matrix_elem x y
  have hm : Measurable fun H : p.SiteMatrix => (H - z • (1 : p.SiteMatrix))⁻¹ x y := by
    rw [hfun]
    exact (hc1.measurable.inv).mul hc2.measurable
  exact measurableSet_lt measurable_const ((hm.sub measurable_const).norm)

/-- Resolvent entries commute with reindexing by an equivalence. -/
theorem resolvent_submatrix_apply {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix κ κ ℂ) (e : ι ≃ κ) (z : ℂ) (x y : ι) :
    (A.submatrix e e - z • (1 : Matrix ι ι ℂ))⁻¹ x y = (A - z • (1 : Matrix κ κ ℂ))⁻¹ (e x) (e y) := by
  have h : A.submatrix e e - z • (1 : Matrix ι ι ℂ) = (A - z • (1 : Matrix κ κ ℂ)).submatrix e e := by
    ext a b
    simp [Matrix.sub_apply, Matrix.one_apply, e.injective.eq_iff]
  rw [h, Matrix.inv_submatrix_equiv]
  rfl

/-- The short-ring entrywise local law `Internal.Contracts.Inputs.ShortRingLocalLaw`, with the
polynomial control. Law: every `p.GaussianRingModel` (physical
complex Gaussian ring, `n ≥ 4` blocks of width `W`, `N = nW`, bond `b`). Domain: `|e| ≤ 2 - κ`,
`N^{-1+δ₀} ≤ η`, `|e + iη| ≤ C₀`, `0 < δ₀ < ζ₀`, `W² ≥ N^{1+ζ₀}`. Bound:
`|G_xy - m_sc δ_xy| ≤ N^ε √Υ_η(x,y)` off an event of probability `≤ N^{-D₁}`, with
`Υ = (ℓη)⁻¹(1 + |x-y|_N/ℓ)^{-D}`, `D ≥ 6`, uniformly in `n, W`, realization, `e, η`, sites,
for `N ≥ N₀(b, ζ₀, δ₀, κ, C₀, D, ε, D₁)`. Inputs: the cited theorem
`hER : SourceContract` (Erdős–Riabov Theorem 3.3 (3.17), `u = e_x`, `v = e_y`) and the
admissibility `shortRingAdmissibility_holds`. -/
theorem shortRingLocalLaw_holds (hER : ErdosRiabov.SourceContract.{0}) :
    Internal.Contracts.Inputs.ShortRingLocalLaw := by
  intro b ζ₀ δ₀ κ C₀ hb0 hb hδ hδζ hκ hC₀ D hD ε D₁ hε hD₁
  have hκ' : 0 < min κ 1 := lt_min hκ one_pos
  obtain ⟨C₁, c₂, D', hC₁, hc₂, hD', hadm⟩ :=
    shortRingAdmissibility_holds b hb0 hb δ₀ (min κ 1) C₀ hδ hκ' hC₀ D hD
  set q := shortRingParameters ζ₀ δ₀ κ C₀ C₁ c₂ D' hδ hδζ hκ hC₀ hC₁ hc₂ hD' with hq
  obtain ⟨N0, -, hN0⟩ := hER q ε D₁ hε hD₁
  refine ⟨N0, ?_⟩
  intro p hpb hN hband model e η he hη hz x y
  subst hpb
  set L := ringNativeLaw q p (ringProfile_nativeProfile q le_rfl p hband) (fun _ => le_rfl)
    with hL
  have hU : ErdosRiabov.AdmissibleControl q p.N p.W L.S (polynomialControl p.N p.W D) :=
    hadm q rfl rfl rfl le_rfl le_rfl le_rfl p.n p.W p.n_ge_four p.W_pos
  set z : ℂ := (e : ℂ) + (η : ℂ) * Complex.I with hzdef
  have hzD : ErdosRiabov.SpectralDomain q p.N z :=
    spectralDomain_of_bulk q p.N p.N_pos (min_le_left κ 1)
      (lt_of_le_of_lt (min_le_right κ 1) one_lt_two) he hη hz
  have hηpos : 0 < η :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast p.N_pos) _) hη
  have hzim : |z.im| = η := by
    rw [hzdef]
    simp [abs_of_pos hηpos]
  set ex := siteFinEquiv p x
  set ey := siteFinEquiv p y
  have hbound := (hN0 p.N p.W hN L (polynomialControl p.N p.W D) hU z hzD).1
    (EuclideanSpace.single ex (1 : ℂ)) (EuclideanSpace.single ey (1 : ℂ))
  -- the entrywise bad event is the preimage of the isotropic event
  set E : Set p.SiteMatrix := {H | (p.N : ℝ) ^ ε * Real.sqrt (siteControl p D η x y) <
      ‖(H - z • (1 : p.SiteMatrix))⁻¹ x y -
        (if x = y then ErdosRiabov.semicircleM z else 0)‖} with hE
  have hmeasE : MeasurableSet E := measurableSet_resolventBad p _ z _ x y
  have hpre : ringPhysMatrix p ⁻¹' E =
      ErdosRiabov.isotropicBad L (polynomialControl p.N p.W D) z
        (EuclideanSpace.single ex (1 : ℂ)) (EuclideanSpace.single ey (1 : ℂ)) ε := by
    ext ω
    simp only [Set.mem_preimage, hE, Set.mem_ofPred_eq, ErdosRiabov.isotropicBad,
      vectorControl_single, matrixPairing_single, hzim]
    rw [ringPhysMatrix_eq_submatrix q p _ _ ω, resolvent_submatrix_apply,
      polynomialControl_siteFinEquiv]
    have hxy : (ex = ey) ↔ (x = y) := (siteFinEquiv p).injective.eq_iff
    simp only [ErdosRiabov.resolventError, ErdosRiabov.resolvent, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, hxy, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rfl
  calc (model.law : Measure p.SiteMatrix) E
      = Measure.map (ringPhysMatrix p) (ringOmegaMeasure p.N) E := by
        rw [model_law_eq_ringPhys p model]
    _ = ringOmegaMeasure p.N (ringPhysMatrix p ⁻¹' E) :=
        Measure.map_apply (measurable_ringPhysMatrix p) hmeasE
    _ = L.P (ErdosRiabov.isotropicBad L (polynomialControl p.N p.W D) z
          (EuclideanSpace.single ex (1 : ℂ)) (EuclideanSpace.single ey (1 : ℂ)) ε) := by
        rw [hpre]
        rfl
    _ ≤ ENNReal.ofReal ((p.N : ℝ) ^ (-D₁)) := hbound

end BlockBand.Adapters.ErdosRiabov
