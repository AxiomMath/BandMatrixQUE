module

public import BlockBand.SourceProcess.FullSourceCovariance.PhiSameForm

/-!
# The right Gaussian IBP of `T₃ = a*K̂𝒢D𝒢Vc'`

Gaussian integration by parts on the right factor `V` expresses `E[T₃]` through the self-energy
and the trace `tSame`.

* `tSame D G = Σ_γ s_γ (GDG)_γγ` (`s = physVar`; for `D = S̃` it is `W⁻¹Tr(S̃𝒢S̃𝒢)`);
* **`t3_ibp hA`**: `E[a*K̂𝒢D𝒢Vc'] = -E[F·tSame D 𝒢] - E[τ·a*K̂𝒢D𝒢c']` (`τ = selfTau`), with all
  three integrands integrable. Proof: `T₃ = Σ_μ (e_μ*𝒢Vc')Ψ_μ`, `Ψ_μ = (K̂ᴴa)*𝒢(De_μ)` (a resolvent
  form), `replica_right_vec` for each `μ` (hypotheses from `ibp_hyps_bulk`), then
  `Σ_μ 𝒢_μγ(𝒢De_μ)_γ = (𝒢D𝒢)_γγ` and `crossed_same_pt`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `t_D(G) = Σ_γ s_γ (GDG)_γγ`. -/
def tSame (b : ℝ) (D G : LayerMat W) : ℂ := ∑ γ, physVar W b γ * (G * D * G) γ γ

theorem vecMul_single_apply (G : LayerMat W) (μ γ : LayerSite W .oneBlockOnePort) :
    (star (Pi.single μ (1 : ℂ)) ᵥ* G) γ = G μ γ := by
  simp [vecMul, dotProduct, Pi.single_apply]

theorem vecMul_apply_single (a : LayerSite W .oneBlockOnePort → ℂ) (M : LayerMat W)
    (μ : LayerSite W .oneBlockOnePort) : (star a ᵥ* M) μ = star a ⬝ᵥ (M *ᵥ Pi.single μ 1) := by
  rw [dotProduct_mulVec]; simp [dotProduct, Pi.single_apply]

theorem single_dotProduct (μ : LayerSite W .oneBlockOnePort) (w : LayerSite W .oneBlockOnePort → ℂ) :
    star (Pi.single μ (1 : ℂ)) ⬝ᵥ w = w μ := by
  simp [dotProduct, Pi.single_apply]

/-- `T = Σ_μ (e_μ*Nc)·Ψ_μ` with `Ψ_μ = (K̂ᴴa)*𝒢(De_μ)`. -/
theorem form_split_mu (Kh G D N : LayerMat W) (a c : LayerSite W .oneBlockOnePort → ℂ) :
    star a ⬝ᵥ ((Kh * G * D * N) *ᵥ c) =
      ∑ μ, (star (Pi.single μ (1 : ℂ)) ⬝ᵥ (N *ᵥ c)) *
        (star (Khᴴ *ᵥ a) ⬝ᵥ (G *ᵥ (D *ᵥ Pi.single μ 1))) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, dotProduct]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [single_dotProduct, vecMul_apply_single, Matrix.mul_assoc Kh G D, star_dotProduct_mul_mulVec,
    ← mulVec_mulVec, mul_comm]

/-- The pointwise crossed identity. -/
theorem crossed_mu_pt (b : ℝ) (Kh G D : LayerMat W) (a c : LayerSite W .oneBlockOnePort → ℂ)
    (hc : ∀ j, c (port j) = 0) :
    ∑ μ, ∑ β, ∑ γ, c β * siteVar W b β γ * ((star (Pi.single μ (1 : ℂ)) ᵥ* G) γ *
        resFormDeriv G (Khᴴ *ᵥ a) (D *ᵥ Pi.single μ 1) (Matrix.single β γ 1)) =
      -(star a ⬝ᵥ ((Kh * G) *ᵥ c)) * tSame b D G := by
  have e : ∀ μ, ∑ β, ∑ γ, c β * siteVar W b β γ * ((star (Pi.single μ (1 : ℂ)) ᵥ* G) γ *
      resFormDeriv G (Khᴴ *ᵥ a) (D *ᵥ Pi.single μ 1) (Matrix.single β γ 1)) =
      (∑ β, c β * -(star (Khᴴ *ᵥ a) ᵥ* G) β) *
        ∑ γ, physVar W b γ * (G μ γ * (G *ᵥ (D *ᵥ Pi.single μ 1)) γ) := fun μ => by
    rw [← crossed_same_pt b c hc]
    refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun γ _ => ?_
    rw [resFormDeriv_single, vecMul_single_apply]; ring
  simp only [e]
  have hs : ∑ β, c β * -(star (Khᴴ *ᵥ a) ᵥ* G) β = -(star a ⬝ᵥ ((Kh * G) *ᵥ c)) := by
    simp only [mul_neg, Finset.sum_neg_distrib]
    rw [sum_mul_vecMul, star_dotProduct_mul_mulVec]
  rw [hs, ← Finset.mul_sum, tSame]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [mulVec_mulVec]
  simp [mulVec, dotProduct, Pi.single_apply, Matrix.mul_apply]
  ring

/-- `Σ_μ Ψ_μ·(e_μ*𝒢S[𝒢]c) = τ·a*K̂𝒢D𝒢c` for physical `c = ι₁y`. -/
theorem self_mu_pt (b : ℝ) (Kh G D : LayerMat W) (a : LayerSite W .oneBlockOnePort → ℂ)
    (y : Fin W → ℂ) :
    ∑ μ, (star (Khᴴ *ᵥ a) ⬝ᵥ (G *ᵥ (D *ᵥ Pi.single μ 1))) *
        (star (Pi.single μ (1 : ℂ)) ⬝ᵥ ((G * sdiag b G) *ᵥ physVec y)) =
      selfTau b G * (star a ⬝ᵥ ((Kh * G * D * G) *ᵥ physVec y)) := by
  have e : (G * sdiag b G) *ᵥ physVec y = selfTau b G • (G *ᵥ physVec y) := by
    rw [← mulVec_mulVec, sdiag_mulVec_physVec, mulVec_smul]
  rw [e, form_split_mu Kh G D G a (physVec y), Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [dotProduct_smul, smul_eq_mul]; ring

/-- **The right IBP of `T₃ = a*K̂𝒢D𝒢Vc'`.** -/
theorem t3_ibp (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ (D : LayerMat W) (x y' : Fin W → ℂ),
      Integrable (fun ω => fForm b E X x y' ω * tSame b D (gRes b E X ω)) (freshLaw W b) ∧
      Integrable (fun ω => selfTau b (gRes b E X ω) * (star (physVec x) ⬝ᵥ
        ((kHat b E X * gRes b E X ω * D * gRes b E X ω) *ᵥ physVec y'))) (freshLaw W b) ∧
      Integrable (fun ω => star (physVec x) ⬝ᵥ
        ((kHat b E X * gRes b E X ω * D * (gRes b E X ω * layerLin ω)) *ᵥ physVec y'))
        (freshLaw W b) ∧
      ∫ ω, star (physVec x) ⬝ᵥ
          ((kHat b E X * gRes b E X ω * D * (gRes b E X ω * layerLin ω)) *ᵥ physVec y')
          ∂freshLaw W b =
        -(∫ ω, fForm b E X x y' ω * tSame b D (gRes b E X ω) ∂freshLaw W b) -
          ∫ ω, selfTau b (gRes b E X ω) * (star (physVec x) ⬝ᵥ
            ((kHat b E X * gRes b E X ω * D * gRes b E X ω) *ᵥ physVec y')) ∂freshLaw W b := by
  obtain ⟨W₀, hh⟩ := ibp_hyps_bulk hA hb0 hb hκ
  refine ⟨W₀, fun W hW E hE X hY D x y' => ?_⟩
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  set μ := freshLaw W b
  set Kh := kHat b E X
  set a := physVec x
  set c := physVec y'
  set u := Khᴴ *ᵥ a
  set v : LayerSite W .oneBlockOnePort → LayerSite W .oneBlockOnePort → ℂ :=
    fun m => D *ᵥ Pi.single m 1
  set Ψ := fun m (ω : LayerSample W .oneBlockOnePort) => star u ⬝ᵥ (gRes b E X ω *ᵥ v m)
  set DΨ := fun m (ω : LayerSample W .oneBlockOnePort) => resFormDeriv (gRes b E X ω) u (v m)
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have hΨm : ∀ m, Measurable (Ψ m) := fun m =>
    (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)).measurable.comp hGm
  have hDm : ∀ m N, Measurable fun ω => DΨ m ω N := fun m N => by
    have e : (fun ω => DΨ m ω N) = (fun G : LayerMat W => -(star u ⬝ᵥ ((G * N * G) *ᵥ v m))) ∘
        gRes b E X := funext fun ω => resFormDeriv_apply _ _ _ _
    rw [e]
    exact (continuous_const.dotProduct (((continuous_id.matrix_mul continuous_const).matrix_mul
      continuous_id).matrix_mulVec continuous_const)).neg.measurable.comp hGm
  have hnu := PassiveCovariance.vecNorm_nonneg u
  have hbd : ∀ m ω, ‖Ψ m ω‖ ≤ (vecNorm u * vecNorm (v m)) * (1 + btFun b E X ω) ^ 1 := fun m ω => by
    rw [pow_one]
    exact (norm_form_le u (v m) _).trans (by
      have := PassiveCovariance.vecNorm_nonneg (v m)
      gcongr; exact norm_gRes_le_one_add b E X ω)
  have hbdD : ∀ m ω N, ‖DΨ m ω N‖ ≤ ((vecNorm u * vecNorm (v m)) * ‖N‖) *
      (1 + btFun b E X ω) ^ 2 := fun m ω N => by
    have := PassiveCovariance.vecNorm_nonneg (v m)
    have hG := norm_gRes_le_one_add b E X ω
    have hG0 := norm_nonneg (gRes b E X ω)
    show ‖resFormDeriv (gRes b E X ω) u (v m) N‖ ≤ _
    rw [resFormDeriv_apply, norm_neg]
    refine (norm_form_le u (v m) _).trans ?_
    have h3 : ‖gRes b E X ω * N * gRes b E X ω‖ ≤ ‖gRes b E X ω‖ * ‖N‖ * ‖gRes b E X ω‖ :=
      calc ‖gRes b E X ω * N * gRes b E X ω‖ ≤ ‖gRes b E X ω * N‖ * ‖gRes b E X ω‖ :=
            Matrix.l2_opNorm_mul _ _
        _ ≤ ‖gRes b E X ω‖ * ‖N‖ * ‖gRes b E X ω‖ :=
            mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    calc vecNorm u * vecNorm (v m) * ‖gRes b E X ω * N * gRes b E X ω‖ ≤
        vecNorm u * vecNorm (v m) * (‖gRes b E X ω‖ * ‖N‖ * ‖gRes b E X ω‖) := by gcongr
      _ ≤ vecNorm u * vecNorm (v m) * ((1 + btFun b E X ω) * ‖N‖ * (1 + btFun b E X ω)) := by
          have hB0 : 0 ≤ (1 + btFun b E X ω) * ‖N‖ := mul_nonneg (hG0.trans hG) (norm_nonneg _)
          gcongr
      _ = _ := by ring
  have hM : ∀ m, 0 ≤ vecNorm u * vecNorm (v m) := fun m =>
    mul_nonneg hnu (PassiveCovariance.vecNorm_nonneg _)
  have hyp := fun m => hh W hW E hE X hY a c _ _ (hM m) (hM m) (Ψ m) (DΨ m)
    (hΨm m) (hDm m) (hbd m) (hbdD m)
  have rr := fun m => replica_right_vec hη hY (hasLayerDeriv_resForm hη hY u (v m)) (hΨm m)
    (Pi.single m 1) c (hyp m).1 (hyp m).2.1 (hyp m).2.2.1 (hyp m).2.2.2.1
  -- the split of `T₃`
  have hT3 : (fun ω => star a ⬝ᵥ ((Kh * gRes b E X ω * D * (gRes b E X ω * layerLin ω)) *ᵥ c)) =
      fun ω => ∑ m, (star (Pi.single m (1 : ℂ)) ⬝ᵥ ((gRes b E X ω * layerLin ω) *ᵥ c)) * Ψ m ω :=
    funext fun ω => form_split_mu _ _ _ _ a c
  -- the crossed integrands
  obtain ⟨Xc, hXe⟩ : ∃ Xc : LayerSite W .oneBlockOnePort → LayerSite W .oneBlockOnePort →
      LayerSite W .oneBlockOnePort → LayerSample W .oneBlockOnePort → ℂ,
      ∀ m β γ ω, Xc m β γ ω =
        (star (Pi.single m (1 : ℂ)) ᵥ* gRes b E X ω) γ * DΨ m ω (Matrix.single β γ 1) :=
    ⟨_, fun _ _ _ _ => rfl⟩
  have hXc : ∀ m β γ, Integrable (Xc m β γ) μ := fun m β γ =>
    ((hyp m).2.1 m γ (Matrix.single β γ 1)).congr (Eventually.of_forall fun ω => by
      rw [hXe, vecMul_single_apply])
  have hcr : ∀ ω, ∑ m, ∑ β, ∑ γ, c β * siteVar W b β γ * Xc m β γ ω =
      -(fForm b E X x y' ω * tSame b D (gRes b E X ω)) := fun ω => by
    simp only [hXe]
    have := crossed_mu_pt b Kh (gRes b E X ω) D a c (physVec_port y')
    rw [fForm, ← neg_mul]; exact this
  have hiC : ∀ m, Integrable (fun ω => ∑ β, ∑ γ, c β * siteVar W b β γ * Xc m β γ ω) μ :=
    fun m => integrable_finsetSum _ fun β _ => integrable_finsetSum _ fun γ _ =>
      (hXc m β γ).const_mul _
  have hFt : Integrable (fun ω => fForm b E X x y' ω * tSame b D (gRes b E X ω)) μ :=
    ((integrable_finsetSum Finset.univ fun m _ => hiC m).neg).congr
      (Eventually.of_forall fun ω => by
        simp only [Pi.neg_apply]
        rw [hcr ω, neg_neg])
  -- the self-energy integrands
  obtain ⟨Sm, hSe⟩ : ∃ Sm : LayerSite W .oneBlockOnePort → LayerSample W .oneBlockOnePort → ℂ,
      ∀ m ω, Sm m ω = Ψ m ω *
        (star (Pi.single m (1 : ℂ)) ⬝ᵥ ((gRes b E X ω * sdiag b (gRes b E X ω)) *ᵥ c)) :=
    ⟨_, fun _ _ => rfl⟩
  have hSm : ∀ m, Integrable (Sm m) μ := fun m =>
    (integrable_finsetSum Finset.univ fun α _ => integrable_finsetSum Finset.univ fun β _ =>
      integrable_finsetSum Finset.univ fun γ _ =>
        ((hyp m).2.2.2.1 α β γ).const_mul
          (star ((Pi.single m (1 : ℂ) : LayerSite W .oneBlockOnePort → ℂ) α) * c β *
          siteVar W b β γ)).congr (Eventually.of_forall fun ω => by
      beta_reduce
      rw [hSe, sdiag_form_expand])
  have hsf : ∀ ω, ∑ m, Sm m ω = selfTau b (gRes b E X ω) *
      (star a ⬝ᵥ ((Kh * gRes b E X ω * D * gRes b E X ω) *ᵥ c)) := fun ω => by
    simp only [hSe]; exact self_mu_pt b Kh (gRes b E X ω) D a y'
  have hTS : Integrable (fun ω => selfTau b (gRes b E X ω) *
      (star a ⬝ᵥ ((Kh * gRes b E X ω * D * gRes b E X ω) *ᵥ c))) μ :=
    (integrable_finsetSum Finset.univ fun m _ => hSm m).congr (Eventually.of_forall fun ω => by
      exact hsf ω)
  have hT3i : Integrable (fun ω => star a ⬝ᵥ
      ((Kh * gRes b E X ω * D * (gRes b E X ω * layerLin ω)) *ᵥ c)) μ := by
    rw [hT3]; exact integrable_finsetSum _ fun m _ => (rr m).1
  refine ⟨hFt, hTS, hT3i, ?_⟩
  rw [hT3, integral_finsetSum _ fun m _ => (rr m).1, Finset.sum_congr rfl fun m _ => (rr m).2,
    Finset.sum_sub_distrib]
  have eC : ∑ m, ∑ β, ∑ γ, c β * siteVar W b β γ *
      ∫ ω, (star (Pi.single m (1 : ℂ)) ᵥ* gRes b E X ω) γ * DΨ m ω (Matrix.single β γ 1) ∂μ =
      -(∫ ω, fForm b E X x y' ω * tSame b D (gRes b E X ω) ∂μ) := by
    have e1 : ∀ m, ∑ β, ∑ γ, c β * siteVar W b β γ *
        ∫ ω, (star (Pi.single m (1 : ℂ)) ᵥ* gRes b E X ω) γ * DΨ m ω (Matrix.single β γ 1) ∂μ =
        ∫ ω, ∑ β, ∑ γ, c β * siteVar W b β γ * Xc m β γ ω ∂μ := fun m => by
      rw [← sum_sum_integral (fun β γ => c β * siteVar W b β γ) (Xc m) (hXc m)]
      simp only [hXe]
    rw [Finset.sum_congr rfl fun m _ => e1 m, ← integral_finsetSum _ fun m _ => hiC m,
      ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall hcr)
  have eS : ∑ m, ∫ ω, Ψ m ω * (star (Pi.single m (1 : ℂ)) ⬝ᵥ
      ((gRes b E X ω * sdiag b (gRes b E X ω)) *ᵥ c)) ∂μ =
      ∫ ω, selfTau b (gRes b E X ω) *
        (star a ⬝ᵥ ((Kh * gRes b E X ω * D * gRes b E X ω) *ᵥ c)) ∂μ := by
    have e2 : ∀ m, ∫ ω, Ψ m ω * (star (Pi.single m (1 : ℂ)) ⬝ᵥ
        ((gRes b E X ω * sdiag b (gRes b E X ω)) *ᵥ c)) ∂μ = ∫ ω, Sm m ω ∂μ := fun m => by
      simp only [hSe]
    rw [Finset.sum_congr rfl fun m _ => e2 m, ← integral_finsetSum _ fun m _ => hSm m]
    exact integral_congr_ae (Eventually.of_forall hsf)
  rw [eC, eS]

end BlockBand.SourceProcess.FullSourceCovariance
