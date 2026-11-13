module

public import BlockBand.Transmission.PassiveCovariance.LayerDeriv
public import BlockBand.Transmission.PassiveCovariance.Fluctuation

/-!
# The exact one-step replica (Schwinger–Dyson) identity of the fresh layer

Write the layer matrix as `H₀ + V`, where `V = layerLin ω` is the Gaussian part
(`layerMatrix_eq_add`), so that `V𝒢 = I - H₀𝒢` (`layerLin_mul_gRes`). For a strictly passive old
input (`Y ≻ 0`) and every test functional `Ψ` with a linear layer derivative `DΨ` (for instance,
by the product rule, any polynomial in entries of `𝒢` and `𝒢*`), Gaussian IBP gives **exactly**

* `replica_identity_phys`: `E[(V𝒢)_{xβ}Ψ] = Σ_y (c/W) E[𝒢_{yβ}DΨ(E_{yx}) - Ψ𝒢_{yy}𝒢_{xβ}]
  + Σ_y (b/W) E[𝒢_{ȳβ}DΨ(E_{ȳx}) - Ψ𝒢_{ȳȳ}𝒢_{xβ}]`;
* `replica_identity_port`: `E[(V𝒢)_{x̄β}Ψ] = Σ_y (b/W) E[𝒢_{yβ}DΨ(E_{yx̄}) - Ψ𝒢_{yy}𝒢_{x̄β}]`.

Here `x, y` are physical sites and `x̄, ȳ` port sites (`phys`, `port`). The `-Ψ𝒢𝒢` terms
form the self-energy `S(𝒢)𝒢`, with `S = diag((c/W)Tr𝒢₁₁ + (b/W)Tr𝒢₂₂, (b/W)Tr𝒢₁₁)`. The `DΨ`
terms are the crossed contractions, which carry the source `cP_top + bP_bottom`.
With `Ψ = 1` this is the mean (Schwinger–Dyson) equation. With `Ψ` a centred bilinear form of
`U = LL*` it is the first rung of the ladder. The integrability hypotheses (`L²` of
`𝒢_{γβ}Ψ`, `L¹` of the derivative terms) are discharged by `moments` of
`PassiveBoundsStatement`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Transmission
open scoped NNReal ComplexOrder

variable {W : ℕ}

abbrev phys (x : Fin W) : LayerSite W .oneBlockOnePort := Sum.inl ((0 : Fin 1), x)
abbrev port (x : Fin W) : LayerSite W .oneBlockOnePort := Sum.inr ((0 : Fin 1), x)

theorem layerA_single (x y : Fin W) :
    layerA (Matrix.single y x 1) = Matrix.single (phys y) (phys x) (1 : ℂ) := by
  ext i j
  rcases i with ⟨i1, i⟩ | ⟨i1, i⟩ <;> rcases j with ⟨j1, j⟩ | ⟨j1, j⟩ <;>
    fin_cases i1 <;> fin_cases j1 <;>
    simp [layerA, BlockBand.Internal.Contracts.Layers.blockDiag, Matrix.single_apply]

theorem lowerB_single (x y : Fin W) :
    lowerB (Matrix.single x y 1) = Matrix.single (port y) (phys x) (1 : ℂ) := by
  ext i j
  rcases i with ⟨i1, i⟩ | ⟨i1, i⟩ <;> rcases j with ⟨j1, j⟩ | ⟨j1, j⟩ <;>
    fin_cases i1 <;> fin_cases j1 <;>
    simp [lowerB, bondMatrix, Matrix.single_apply, LayerShape.incident, and_comm]

theorem upperB_single (x y : Fin W) :
    upperB (Matrix.single y x 1) = Matrix.single (phys y) (port x) (1 : ℂ) := by
  ext i j
  rcases i with ⟨i1, i⟩ | ⟨i1, i⟩ <;> rcases j with ⟨j1, j⟩ | ⟨j1, j⟩ <;>
    fin_cases i1 <;> fin_cases j1 <;>
    simp [upperB, bondMatrix, Matrix.single_apply, LayerShape.incident]

theorem mul_single_mul_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ)
    (i j γ β : ι) : (G * Matrix.single i j (1 : ℂ) * G) γ β = G γ i * G j β := by
  simp only [Matrix.mul_apply, Matrix.single_apply, Finset.sum_mul, ite_mul, mul_ite, mul_one,
    mul_zero, zero_mul]
  simp [ite_and, Finset.sum_ite_eq]

theorem sum_layerSite (f : LayerSite W .oneBlockOnePort → ℂ) :
    ∑ γ, f γ = ∑ y, f (phys y) + ∑ y, f (port y) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp

theorem layerLin_mul_phys (ω : LayerSample W .oneBlockOnePort) (G : LayerMat W) (x : Fin W)
    (β : LayerSite W .oneBlockOnePort) :
    (layerLin ω * G) (phys x) β =
      ∑ y, ω.1 0 x y * G (phys y) β + ∑ y, ω.2 0 0 x y * G (port y) β := by
  rw [Matrix.mul_apply, sum_layerSite]
  simp [layerLin, BlockBand.Internal.Contracts.Layers.blockDiag, bondMatrix, LayerShape.incident]

theorem layerLin_mul_port (ω : LayerSample W .oneBlockOnePort) (G : LayerMat W) (x : Fin W)
    (β : LayerSite W .oneBlockOnePort) :
    (layerLin ω * G) (port x) β = ∑ y, star (ω.2 0 0 y x) * G (phys y) β := by
  rw [Matrix.mul_apply, sum_layerSite]
  simp [layerLin, bondMatrix, LayerShape.incident]

theorem memLp_layer_A (b : ℝ) (x y : Fin W) :
    MemLp (fun ω : LayerSample W .oneBlockOnePort => ω.1 0 x y) 2 (layerLaw W b .oneBlockOnePort) :=
  ((memLp_gue_entry (gueVar W b) x y).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin 1 => gueMeasure (Fin W) (gueVar W b)) 0)).comp_measurePreserving
    (measurePreserving_fst (μ := Measure.pi fun _ : Fin 1 => gueMeasure (Fin W) (gueVar W b))
      (ν := Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin 1 =>
        ginibreMeasure (Fin W) (Fin W) (ginVar W b)))

theorem memLp_layer_B (b : ℝ) (x y : Fin W) :
    MemLp (fun ω : LayerSample W .oneBlockOnePort => ω.2 0 0 x y) 2 (layerLaw W b .oneBlockOnePort) :=
  (((memLp_ginibre_entry (ginVar W b) x y).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin 1 => ginibreMeasure (Fin W) (Fin W) (ginVar W b)) 0)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin 1 => Measure.pi fun _ : Fin 1 =>
      ginibreMeasure (Fin W) (Fin W) (ginVar W b)) 0)).comp_measurePreserving
    (measurePreserving_snd (μ := Measure.pi fun _ : Fin 1 => gueMeasure (Fin W) (gueVar W b))
      (ν := Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin 1 =>
        ginibreMeasure (Fin W) (Fin W) (ginVar W b)))

theorem measurable_layerRes (E : ℝ) (z : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable fun ω => layerResolvent .oneBlockOnePort E z
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω :=
  measurable_matrix_inv.comp (measurable_layerMatrix E z X)

section Master
variable (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)

/-- The fresh layer resolvent `𝒢(ω)` at `z = z_∂(E)`. -/
abbrev gRes (ω : LayerSample W .oneBlockOnePort) : LayerMat W :=
  layerResolvent .oneBlockOnePort E (boundaryZ b E) (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω

theorem stein_entry_term {Ψ : LayerSample W .oneBlockOnePort → ℂ}
    {DΨ : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ}
    (hη : 0 < etaZ b E) (hY : (passiveY X).PosDef) (hΨ : HasLayerDeriv Ψ DΨ)
    (hΨm : Measurable Ψ) (γ β : LayerSite W .oneBlockOnePort)
    (hI1 : ∀ N, Integrable (fun ω => gRes b E X ω γ β * DΨ ω N) (layerLaw W b .oneBlockOnePort))
    (hI2 : ∀ N, Integrable (fun ω => Ψ ω * (gRes b E X ω * N * gRes b E X ω) γ β)
      (layerLaw W b .oneBlockOnePort)) :
    HasLayerDeriv (fun ω => gRes b E X ω γ β * Ψ ω)
        (fun ω => gRes b E X ω γ β • DΨ ω + Ψ ω • resDeriv (gRes b E X ω) γ β) ∧
      Measurable (fun ω => gRes b E X ω γ β * Ψ ω) ∧
      ∀ N, Integrable (fun ω => (gRes b E X ω γ β • DΨ ω + Ψ ω • resDeriv (gRes b E X ω) γ β) N)
        (layerLaw W b .oneBlockOnePort) := by
  have hinv := fun ω hω => isUnit_layerMatrix_strict (E := E) hη hY ω hω
  refine ⟨(hasLayerDeriv_resolvent_entry E (boundaryZ b E) _ hinv γ β).mul hΨ,
    ((measurable_layerRes E (boundaryZ b E) X).eval_matrix).mul hΨm, fun N => ?_⟩
  have e : (fun ω => (gRes b E X ω γ β • DΨ ω + Ψ ω • resDeriv (gRes b E X ω) γ β) N) =
      fun ω => gRes b E X ω γ β * DΨ ω N - Ψ ω * (gRes b E X ω * N * gRes b E X ω) γ β := by
    funext ω; simp [resDeriv, sub_eq_add_neg]
  rw [e]; exact (hI1 N).sub (hI2 N)

/-- **Exact one-step replica (Schwinger–Dyson) identity, physical rows**:
for strictly passive `X` and every test functional `Ψ` with a linear layer derivative,
`E[(V𝒢)_{xβ} Ψ] = Σ_y (c/W) E[𝒢_{yβ} DΨ(E_{yx}) - Ψ 𝒢_{yy}𝒢_{xβ}]
  + Σ_y (b/W) E[𝒢_{ȳβ} DΨ(E_{ȳx}) - Ψ 𝒢_{ȳȳ}𝒢_{xβ}]` (`ȳ` the port copy of `y`), where
`V = layerLin ω` is the Gaussian part of the layer matrix. The `-Ψ𝒢𝒢` terms are the self-energy
`S(𝒢)𝒢`; the `DΨ` terms are the crossed contractions. -/
theorem replica_identity_phys {Ψ : LayerSample W .oneBlockOnePort → ℂ}
    {DΨ : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ}
    (hη : 0 < etaZ b E) (hY : (passiveY X).PosDef) (hΨ : HasLayerDeriv Ψ DΨ)
    (hΨm : Measurable Ψ) (x : Fin W) (β : LayerSite W .oneBlockOnePort)
    (hL2 : ∀ γ, MemLp (fun ω => gRes b E X ω γ β * Ψ ω) 2 (layerLaw W b .oneBlockOnePort))
    (hI1 : ∀ γ N, Integrable (fun ω => gRes b E X ω γ β * DΨ ω N) (layerLaw W b .oneBlockOnePort))
    (hI2 : ∀ γ N, Integrable (fun ω => Ψ ω * (gRes b E X ω * N * gRes b E X ω) γ β)
      (layerLaw W b .oneBlockOnePort)) :
    ∫ ω, (layerLin ω * gRes b E X ω) (phys x) β * Ψ ω ∂layerLaw W b .oneBlockOnePort =
      ∑ y, (gueVar W b : ℂ) * ∫ ω, (gRes b E X ω (phys y) β *
          DΨ ω (Matrix.single (phys y) (phys x) 1) -
          Ψ ω * (gRes b E X ω (phys y) (phys y) * gRes b E X ω (phys x) β))
          ∂layerLaw W b .oneBlockOnePort +
      ∑ y, (ginVar W b : ℂ) * ∫ ω, (gRes b E X ω (port y) β *
          DΨ ω (Matrix.single (port y) (phys x) 1) -
          Ψ ω * (gRes b E X ω (port y) (port y) * gRes b E X ω (phys x) β))
          ∂layerLaw W b .oneBlockOnePort := by
  set μ := layerLaw W b .oneBlockOnePort
  have hA : ∀ y, Integrable (fun ω => ω.1 0 x y * (gRes b E X ω (phys y) β * Ψ ω)) μ :=
    fun y => (memLp_layer_A b x y).integrable_mul (hL2 _)
  have hB : ∀ y, Integrable (fun ω => ω.2 0 0 x y * (gRes b E X ω (port y) β * Ψ ω)) μ :=
    fun y => (memLp_layer_B b x y).integrable_mul (hL2 _)
  have e : (fun ω => (layerLin ω * gRes b E X ω) (phys x) β * Ψ ω) = fun ω =>
      ∑ y, ω.1 0 x y * (gRes b E X ω (phys y) β * Ψ ω) +
        ∑ y, ω.2 0 0 x y * (gRes b E X ω (port y) β * Ψ ω) := by
    funext ω; rw [layerLin_mul_phys, add_mul, Finset.sum_mul, Finset.sum_mul]
    congr 1 <;> refine Finset.sum_congr rfl fun y _ => by ring
  rw [e, integral_add (integrable_finsetSum _ fun y _ => hA y) (integrable_finsetSum _ fun y _ => hB y),
    integral_finsetSum _ (fun y _ => hA y), integral_finsetSum _ (fun y _ => hB y)]
  congr 1
  · refine Finset.sum_congr rfl fun y _ => ?_
    obtain ⟨hd, hm, hi⟩ := stein_entry_term b E X hη hY hΨ hΨm (phys y) β (hI1 _) (hI2 _)
    rw [stein_layerA_lin b _ _ hd hm (hL2 _) hi x y, layerA_single]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [resDeriv, mul_single_mul_apply, sub_eq_add_neg]
  · refine Finset.sum_congr rfl fun y _ => ?_
    obtain ⟨hd, hm, hi⟩ := stein_entry_term b E X hη hY hΨ hΨm (port y) β (hI1 _) (hI2 _)
    rw [stein_layerB_lin b _ _ hd hm (hL2 _) hi x y, lowerB_single]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [resDeriv, mul_single_mul_apply, sub_eq_add_neg]

/-- **Exact one-step replica identity, port rows**:
`E[(V𝒢)_{x̄β} Ψ] = Σ_y (b/W) E[𝒢_{yβ} DΨ(E_{y x̄}) - Ψ 𝒢_{yy}𝒢_{x̄β}]`. -/
theorem replica_identity_port {Ψ : LayerSample W .oneBlockOnePort → ℂ}
    {DΨ : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ}
    (hη : 0 < etaZ b E) (hY : (passiveY X).PosDef) (hΨ : HasLayerDeriv Ψ DΨ)
    (hΨm : Measurable Ψ) (x : Fin W) (β : LayerSite W .oneBlockOnePort)
    (hL2 : ∀ γ, MemLp (fun ω => gRes b E X ω γ β * Ψ ω) 2 (layerLaw W b .oneBlockOnePort))
    (hI1 : ∀ γ N, Integrable (fun ω => gRes b E X ω γ β * DΨ ω N) (layerLaw W b .oneBlockOnePort))
    (hI2 : ∀ γ N, Integrable (fun ω => Ψ ω * (gRes b E X ω * N * gRes b E X ω) γ β)
      (layerLaw W b .oneBlockOnePort)) :
    ∫ ω, (layerLin ω * gRes b E X ω) (port x) β * Ψ ω ∂layerLaw W b .oneBlockOnePort =
      ∑ y, (ginVar W b : ℂ) * ∫ ω, (gRes b E X ω (phys y) β *
          DΨ ω (Matrix.single (phys y) (port x) 1) -
          Ψ ω * (gRes b E X ω (phys y) (phys y) * gRes b E X ω (port x) β))
          ∂layerLaw W b .oneBlockOnePort := by
  set μ := layerLaw W b .oneBlockOnePort
  have hB : ∀ y, Integrable (fun ω => star (ω.2 0 0 y x) * (gRes b E X ω (phys y) β * Ψ ω)) μ :=
    fun y => (memLp_layer_B b y x).star.integrable_mul (hL2 _)
  have e : (fun ω => (layerLin ω * gRes b E X ω) (port x) β * Ψ ω) = fun ω =>
      ∑ y, star (ω.2 0 0 y x) * (gRes b E X ω (phys y) β * Ψ ω) := by
    funext ω; rw [layerLin_mul_port, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => by ring
  rw [e, integral_finsetSum _ (fun y _ => hB y)]
  refine Finset.sum_congr rfl fun y _ => ?_
  obtain ⟨hd, hm, hi⟩ := stein_entry_term b E X hη hY hΨ hΨm (phys y) β (hI1 _) (hI2 _)
  rw [stein_layerBconj_lin b _ _ hd hm (hL2 _) hi y x, upperB_single]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp [resDeriv, mul_single_mul_apply, sub_eq_add_neg]

/-- The layer matrix is `H₀ + V`, `V = layerLin ω` its Gaussian part. -/
theorem layerMatrix_eq_add (ω : LayerSample W .oneBlockOnePort) :
    layerMatrix .oneBlockOnePort E (boundaryZ b E) (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω =
      layerMatrix .oneBlockOnePort E (boundaryZ b E) (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) 0 +
        layerLin ω := by
  have h := layerMatrix_add_smul E (boundaryZ b E) (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) 0 ω 1
  simpa using h

/-- `V𝒢 = I - H₀𝒢` at an invertible sample (so the left sides of the replica identities are
`E[(I - H₀𝒢)_{αβ} Ψ]`). -/
theorem layerLin_mul_gRes (ω : LayerSample W .oneBlockOnePort)
    (hω : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω)) :
    layerLin ω * gRes b E X ω = 1 - layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) 0 * gRes b E X ω := by
  have hH : layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω * gRes b E X ω = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hω)
  rw [layerMatrix_eq_add, Matrix.add_mul] at hH
  rw [← hH]; abel

end Master

end BlockBand.Transmission.PassiveCovariance
