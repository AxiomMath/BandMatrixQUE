module

public import BlockBand.Layers.TraceFluctuation
public import BlockBand.Layers.OUCovariance

/-!
# Schwinger–Dyson mean equations of one Gaussian layer

The integration by parts step in the proof of the layer-contraction lemma: integration by parts
in an `A` entry gives `E(A_i 𝒢_ij) = -c E(g_i 𝒢_ij)`, and for a bond it gives the corresponding
term `-b E(g_port 𝒢_ij)`; the multi-block equations are the same entry identities with a sum over
the incident bonds.

Law: `layerLaw W b σ` (fresh `A_a ~ GUE_W(c/W)`, `c = 1 - 2b`, bonds `Gin(b/W)`), every shape
`σ`, deterministic Hermitian `X`, real `E`, `Im z ≥ 0`; realized as the image of the real white
noise `gaussianProduct (tflVar W b σ)` under `tflEmbed` (`tfl_layerLaw_eq_map`). Norm: `ℓ²`
operator norm on matrices. Expectations of matrices are entrywise (`matrixExpect`), as in
`TraceMatrixContract.covariance`.

Notation. `g_a(G) = physBlockTrace G a = W⁻¹ Tr P_a G`, `g_{port j}(G) = portBlockTrace G j`,
`P_a = meqPhysProj a`, `Q_j = meqPortProj j`, `ḡ = meqMeanA/meqMeanP ν G` (means of the traces),
`𝒟 = tflConst σ E z X = diag(-E - X, z)`, and the self-energy shift `meqShift σ c b gA gP`, the
diagonal matrix with entry `c g_a + b Σ_{j ~ a} g_{port j}` on physical block `a` and
`b Σ_{a ~ j} g_a` on port `j` (incidence `meqInc σ a j` of `σ`). Covariance:
`meqCov ν f U = E[f U] - (E f) E[U]`. Residual `meqResid ν c b G =
Σ_a c Cov(g_a, P_a G) + Σ_{a,j} b·inc(a,j) (Cov(g_{port j}, P_a G) + Cov(g_a, Q_j G))`.

Results.
* `meqS_eq`: deterministic contraction `Σᵢ vᵢ Λᵢ G Λᵢ = meqShift σ (W t_A) (W t_B) (g(G))`
  over all real coordinates (`Λᵢ = ∂ᵢ𝒢⁻¹`, variances `tflVar`); `W t_A = c`, `W t_B = b`
  (`meq_coefA`, `meq_coefB`).
* `meq_ibp`: `E[Λ(x) G_κ] = -E[𝒮(G_κ) G_κ]` for `G_κ = (𝒢⁻¹ + iκ)⁻¹`, `κ > 0`
  (`ou_ibp` coordinatewise, `dG_κ = -G_κ (dΛ) G_κ`).
* `meanEquation_reg` (regularized form, every `W ≥ 1`, `κ > 0`, no moment hypothesis):
  `(𝒟 + iκ - 𝒮_{c,b}(ḡ)) E G_κ = I + meqResid ν c b G_κ`.
* `meanEquation_of_moments` (limit form): under a.s. invertibility and `‖𝒢‖ ∈ L²`,
  `(𝒟 - 𝒮_{c,b}(ḡ)) E 𝒢 = I + meqResid ν c b 𝒢` (`κ → 0`: dominated convergence with
  `‖G_κ‖ ≤ 2‖𝒢‖`, `‖𝒮(G)G‖ ≤ C_S ‖G‖²`); `meanEquation_holds`: the same from
  `GaussianAbsorptionContract` for `W ≥ W₀ = ⌈2/ε₁⌉` (only `p = 2` is used).
* Scalar forms (exact `κ = 0`): `meanEquation_port`
  `(z - b Σ_{a~j} ḡ_a) ḡ_{port j} = 1 + b Σ_{a~j} W⁻¹ Tr Q_j Cov(g_a, Q_j 𝒢)`;
  `meanEquation_top`: for `M̄ = (meqTop …)⁻¹ = (-E - X - diag(c ḡ_a + b Σ_{j~a} ḡ_{port j}))⁻¹`
  invertible, `ḡ_a = W⁻¹ Tr M̄_{aa} + W⁻¹ Tr (M̄ R_phys)_{aa}`, `R_phys = meqResidTop`.
  Separate and common ports: `meanEquation_separate_port`, `meanEquation_separate_top`,
  `meanEquation_common_port`, `meanEquation_common_top`.
* Interface with `TraceMatrixContract.covariance`: `g_a`, `g_{port j}` and `P_a G`, `Q_j G`
  are one-letter words (`meq_physBlockTrace_eq_word`, `meq_portBlockTrace_eq_word`,
  `meq_mul_eq_wordEval`) with letters of norm `≤ 1` (`meq_norm_physProj_le`,
  `meq_norm_portProj_le`); `|W⁻¹ Tr P_a M|, |W⁻¹ Tr Q_j M| ≤ ‖M‖`
  (`meq_norm_physBlockTrace_le`, `meq_norm_portBlockTrace_le`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers
open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct)
open BlockBand.Internal.Contracts.CoareaPalm (gueMeasure gueSample)
open BlockBand.SourceProcess (circularBrownianCoordinates)
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator

/-!
## 1. The deterministic Gaussian contraction `Σᵢ vᵢ Λᵢ G Λᵢ`
-/

/-- Sum over the two real directions of a Hermitian pair: `Σ_s Λ_s G Λ_s`. -/
theorem meq_sandwich {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n ℂ) (P Q : n) :
    (single P Q (1 : ℂ) + single Q P 1) * G * (single P Q 1 + single Q P 1) +
      (single P Q Complex.I + single Q P (-Complex.I)) * G *
        (single P Q Complex.I + single Q P (-Complex.I)) =
      (2 : ℂ) • (single P P (G Q Q) + single Q Q (G P P)) := by
  simp only [add_mul, mul_add, single_mul_mul_single]
  ext x y
  simp only [Matrix.add_apply, Matrix.smul_apply, single_apply, smul_eq_mul]
  split_ifs <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

variable {W : ℕ} {σ : LayerShape}

/-- The coefficient `√(t_A/2)/√2` of a block coordinate matrix. -/
def meqCA (W : ℕ) (b : ℝ) : ℂ := ((Real.sqrt ((tflTA W b : ℝ) / 2) / Real.sqrt 2 : ℝ) : ℂ)

theorem meq_lin_A0 (b : ℝ) (a : Fin σ.blocks) (α β : Fin W) :
    tflLin W b σ (Pi.single (Sum.inl (a, ((α, β), 0))) 1) =
      meqCA W b • (single (Sum.inl (a, α)) (Sum.inl (a, β)) 1 +
        single (Sum.inl (a, β)) (Sum.inl (a, α)) 1) := by
  ext p q
  rcases p with ⟨c, γ⟩ | ⟨c, γ⟩ <;> rcases q with ⟨d, δ⟩ | ⟨d, δ⟩ <;>
    simp [tflLin, tflEmbed, Internal.Contracts.Layers.blockDiag, bondMatrix, gueOfCoords,
      gueSample, circularBrownianCoordinates, bondAssemble, ginibreAssemble, Pi.single_apply,
      Matrix.single_apply, meqCA]
  rcases eq_or_ne c a with rfl | h1 <;> rcases eq_or_ne d c with rfl | h2 <;>
    rcases eq_or_ne γ α with rfl | h3 <;> rcases eq_or_ne δ β with rfl | h4 <;>
    rcases eq_or_ne δ γ with rfl | h5 <;>
    simp_all [eq_comm, and_comm] <;> (try split_ifs) <;> push_cast <;> ring

theorem meq_lin_A1 (b : ℝ) (a : Fin σ.blocks) (α β : Fin W) :
    tflLin W b σ (Pi.single (Sum.inl (a, ((α, β), 1))) 1) =
      meqCA W b • (single (Sum.inl (a, α)) (Sum.inl (a, β)) Complex.I +
        single (Sum.inl (a, β)) (Sum.inl (a, α)) (-Complex.I)) := by
  ext p q
  rcases p with ⟨c, γ⟩ | ⟨c, γ⟩ <;> rcases q with ⟨d, δ⟩ | ⟨d, δ⟩ <;>
    simp [tflLin, tflEmbed, Internal.Contracts.Layers.blockDiag, bondMatrix, gueOfCoords,
      gueSample, circularBrownianCoordinates, bondAssemble, ginibreAssemble, Pi.single_apply,
      Matrix.single_apply, meqCA]
  split_ifs <;> (try casesm* _ ∧ _) <;> subst_vars <;> simp_all <;>
    first | (right; ring) | simp | ring

theorem meq_lin_B0 (b : ℝ) (a : Fin σ.blocks) (j : Fin σ.ports) (α β : Fin W) :
    tflLin W b σ (Pi.single (Sum.inr (a, j, α, β, 0)) 1) =
      (if σ.incident a j then (1 : ℂ) else 0) • (single (Sum.inl (a, α)) (Sum.inr (j, β)) 1 +
        single (Sum.inr (j, β)) (Sum.inl (a, α)) 1) := by
  ext p q
  rcases p with ⟨c, γ⟩ | ⟨c, γ⟩ <;> rcases q with ⟨d, δ⟩ | ⟨d, δ⟩ <;>
    simp [tflLin, tflEmbed, Internal.Contracts.Layers.blockDiag, bondMatrix, gueOfCoords,
      gueSample, circularBrownianCoordinates, bondAssemble, ginibreAssemble, Pi.single_apply,
      Matrix.single_apply]
  all_goals (split_ifs <;> (try casesm* _ ∧ _) <;> subst_vars <;> simp_all)

theorem meq_lin_B1 (b : ℝ) (a : Fin σ.blocks) (j : Fin σ.ports) (α β : Fin W) :
    tflLin W b σ (Pi.single (Sum.inr (a, j, α, β, 1)) 1) =
      (if σ.incident a j then (1 : ℂ) else 0) •
        (single (Sum.inl (a, α)) (Sum.inr (j, β)) Complex.I +
          single (Sum.inr (j, β)) (Sum.inl (a, α)) (-Complex.I)) := by
  ext p q
  rcases p with ⟨c, γ⟩ | ⟨c, γ⟩ <;> rcases q with ⟨d, δ⟩ | ⟨d, δ⟩ <;>
    simp [tflLin, tflEmbed, Internal.Contracts.Layers.blockDiag, bondMatrix, gueOfCoords,
      gueSample, circularBrownianCoordinates, bondAssemble, ginibreAssemble, Pi.single_apply,
      Matrix.single_apply]
  all_goals (split_ifs <;> (try casesm* _ ∧ _) <;> subst_vars <;> simp_all)

/-- Physical block projection `P_a`. -/
def meqPhysProj (a : Fin σ.blocks) : Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  diagonal (Sum.elim (fun x => if x.1 = a then 1 else 0) (fun _ => 0))

/-- Port block projection `Q_j`. -/
def meqPortProj (j : Fin σ.ports) : Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  diagonal (Sum.elim (fun _ => 0) (fun y => if y.1 = j then 1 else 0))

/-- Bond incidence indicator as a complex number. -/
def meqInc (σ : LayerShape) (a : Fin σ.blocks) (j : Fin σ.ports) : ℂ :=
  if σ.incident a j then 1 else 0

/-- Unnormalized physical block trace. -/
def meqTrA (G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (a : Fin σ.blocks) : ℂ :=
  ∑ α : Fin W, G (Sum.inl (a, α)) (Sum.inl (a, α))

/-- Unnormalized port block trace. -/
def meqTrP (G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (j : Fin σ.ports) : ℂ :=
  ∑ α : Fin W, G (Sum.inr (j, α)) (Sum.inr (j, α))

/-- The self-energy shift. -/
def meqShift (σ : LayerShape) (c b : ℂ) (gA : Fin σ.blocks → ℂ) (gP : Fin σ.ports → ℂ) :
    Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  diagonal (Sum.elim (fun x => c * gA x.1 + b * ∑ j, meqInc σ x.1 j * gP j)
    (fun y => b * ∑ a, meqInc σ a y.1 * gA a))

theorem meq_sum_single_phys (a : Fin σ.blocks) :
    ∑ α : Fin W, single (Sum.inl (a, α) : LayerSite W σ) (Sum.inl (a, α)) (1 : ℂ) =
      meqPhysProj a := by
  ext p q
  rcases p with ⟨c, γ⟩ | ⟨c, γ⟩ <;> rcases q with ⟨d, δ⟩ | ⟨d, δ⟩ <;>
    simp [meqPhysProj, Matrix.sum_apply, single_apply, diagonal_apply, -Finset.sum_boole]
  rcases eq_or_ne c a with rfl | h1 <;> rcases eq_or_ne d c with rfl | h2 <;>
    rcases eq_or_ne δ γ with rfl | h3 <;> simp_all [eq_comm]
  norm_cast
  symm
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro x - ⟨rfl, rfl⟩
  exact h3 rfl

theorem meq_sum_single_port (j : Fin σ.ports) :
    ∑ α : Fin W, single (Sum.inr (j, α) : LayerSite W σ) (Sum.inr (j, α)) (1 : ℂ) =
      meqPortProj j := by
  ext p q
  rcases p with ⟨c, γ⟩ | ⟨c, γ⟩ <;> rcases q with ⟨d, δ⟩ | ⟨d, δ⟩ <;>
    simp [meqPortProj, Matrix.sum_apply, single_apply, diagonal_apply, -Finset.sum_boole]
  rcases eq_or_ne c j with rfl | h1 <;> rcases eq_or_ne d c with rfl | h2 <;>
    rcases eq_or_ne δ γ with rfl | h3 <;> simp_all [eq_comm]
  norm_cast
  symm
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro x - ⟨rfl, rfl⟩
  exact h3 rfl

theorem meqShift_eq_sum (c b : ℂ) (gA : Fin σ.blocks → ℂ) (gP : Fin σ.ports → ℂ) :
    (meqShift σ c b gA gP : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) =
      ∑ a, (c * gA a) • meqPhysProj a +
        ∑ a, ∑ j, (b * meqInc σ a j) • (gP j • meqPhysProj a + gA a • meqPortProj j) := by
  ext p q
  rcases p with ⟨c, γ⟩ | ⟨c, γ⟩ <;> rcases q with ⟨d, δ⟩ | ⟨d, δ⟩ <;>
    simp [meqShift, meqPhysProj, meqPortProj, Matrix.sum_apply, diagonal_apply]
  all_goals (split_ifs <;> simp [Finset.mul_sum, mul_assoc])

theorem meq_double_sum {n ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq n]
    (G : Matrix n n ℂ) (f : ι → n) (g : κ → n) :
    ∑ α, ∑ β, (single (f α) (f α) (G (g β) (g β)) + single (g β) (g β) (G (f α) (f α))) =
      (∑ β, G (g β) (g β)) • ∑ α, single (f α) (f α) (1 : ℂ) +
        (∑ α, G (f α) (f α)) • ∑ β, single (g β) (g β) (1 : ℂ) := by
  simp only [Finset.sum_add_distrib, Finset.smul_sum, Finset.sum_smul, smul_single, smul_eq_mul,
    mul_one]
  rw [Finset.sum_comm (f := fun α β => single (g β) (g β) (G (f α) (f α)))]

/-- The Gaussian contraction `Σᵢ vᵢ Λᵢ G Λᵢ` of the layer coordinates. -/
def meqS (W : ℕ) (b : ℝ) (σ : LayerShape) (G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  ∑ i : TflCoord W σ, (tflVar W b σ i : ℝ) •
    (tflLin W b σ (Pi.single i 1) * G * tflLin W b σ (Pi.single i 1))

theorem meqCA_sq (W : ℕ) (b : ℝ) : meqCA W b * meqCA W b * 2 = (((tflTA W b : ℝ) / 2 : ℝ) : ℂ) := by
  have ht := (tflTA W b).2
  have h1 : Real.sqrt ((tflTA W b : ℝ) / 2) ^ 2 = (tflTA W b : ℝ) / 2 :=
    Real.sq_sqrt (by positivity)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have : Real.sqrt ((tflTA W b : ℝ) / 2) / Real.sqrt 2 * (Real.sqrt ((tflTA W b : ℝ) / 2) /
      Real.sqrt 2) * 2 = (tflTA W b : ℝ) / 2 := by
    field_simp
    nlinarith [h1, h2]
  rw [meqCA]
  exact_mod_cast this

theorem meq_pairA (b : ℝ) (G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (a : Fin σ.blocks)
    (α β : Fin W) :
    ∑ s : Fin 2, (tflVar W b σ (Sum.inl (a, ((α, β), s))) : ℝ) •
      (tflLin W b σ (Pi.single (Sum.inl (a, ((α, β), s))) 1) * G *
        tflLin W b σ (Pi.single (Sum.inl (a, ((α, β), s))) 1)) =
      (((tflTA W b : ℝ) / 2 : ℝ) : ℂ) •
        (single (Sum.inl (a, α)) (Sum.inl (a, α)) (G (Sum.inl (a, β)) (Sum.inl (a, β))) +
          single (Sum.inl (a, β)) (Sum.inl (a, β)) (G (Sum.inl (a, α)) (Sum.inl (a, α)))) := by
  rw [Fin.sum_univ_two]
  simp only [tflVar, Sum.elim_inl, NNReal.coe_one, one_smul]
  rw [meq_lin_A0, meq_lin_A1]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← smul_add, meq_sandwich]
  rw [← meqCA_sq]

theorem meqInc_mul_self (σ : LayerShape) (a : Fin σ.blocks) (j : Fin σ.ports) :
    meqInc σ a j * meqInc σ a j = meqInc σ a j := by
  unfold meqInc; split_ifs <;> simp

theorem meq_pairB (b : ℝ) (G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (a : Fin σ.blocks)
    (j : Fin σ.ports) (α β : Fin W) :
    ∑ s : Fin 2, (tflVar W b σ (Sum.inr (a, j, α, β, s)) : ℝ) •
      (tflLin W b σ (Pi.single (Sum.inr (a, j, α, β, s)) 1) * G *
        tflLin W b σ (Pi.single (Sum.inr (a, j, α, β, s)) 1)) =
      (((tflTB W b : ℝ) : ℂ) * meqInc σ a j) •
        (single (Sum.inl (a, α)) (Sum.inl (a, α)) (G (Sum.inr (j, β)) (Sum.inr (j, β))) +
          single (Sum.inr (j, β)) (Sum.inr (j, β)) (G (Sum.inl (a, α)) (Sum.inl (a, α)))) := by
  rw [Fin.sum_univ_two]
  simp only [tflVar, Sum.elim_inr, NNReal.coe_div, NNReal.coe_ofNat]
  rw [meq_lin_B0, meq_lin_B1]
  change _ • ((meqInc σ a j • _) * G * (meqInc σ a j • _)) +
    _ • ((meqInc σ a j • _) * G * (meqInc σ a j • _)) = _
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← smul_add, meq_sandwich]
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  rw [mul_comm (meqInc σ a j) (meqInc σ a j), meqInc_mul_self]
  push_cast
  ring

theorem meqS_sum (b : ℝ) (G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    meqS W b σ G =
      ∑ a, (((tflTA W b : ℝ) : ℂ) * meqTrA G a) • meqPhysProj a +
        ∑ a, ∑ j, (((tflTB W b : ℝ) : ℂ) * meqInc σ a j) •
          (meqTrP G j • meqPhysProj a + meqTrA G a • meqPortProj j) := by
  unfold meqS
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  simp only [meq_pairA, meq_pairB,
    ← Finset.smul_sum (M := ℂ) (N := Matrix (LayerSite W σ) (LayerSite W σ) ℂ)]
  congr 1
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h := meq_double_sum G (fun α : Fin W => (Sum.inl (a, α) : LayerSite W σ))
      (fun β => Sum.inl (a, β))
    simp only at h
    rw [h, meq_sum_single_phys, ← add_smul, smul_smul]
    congr 1
    unfold meqTrA
    push_cast
    ring
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    have h := meq_double_sum G (fun α : Fin W => (Sum.inl (a, α) : LayerSite W σ))
      (fun β => Sum.inr (j, β))
    rw [h, meq_sum_single_phys, meq_sum_single_port]
    rfl

theorem meqS_eq {b : ℝ} (hW : 0 < W) (G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    meqS W b σ G = meqShift σ ((W : ℂ) * ((tflTA W b : ℝ) : ℂ)) ((W : ℂ) * ((tflTB W b : ℝ) : ℂ))
      (physBlockTrace G) (portBlockTrace G) := by
  have hW' : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hW.ne'
  rw [meqS_sum, meqShift_eq_sum]
  simp only [physBlockTrace, portBlockTrace, smul_add, smul_smul]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    unfold meqTrA
    field_simp
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    congr 2 <;> simp only [meqTrA, meqTrP] <;> field_simp

/-!
## 2. Gaussian integration by parts for the regularized resolvent
-/

/-- The operator-norm bound of the Gaussian contraction: `‖𝒮(G)‖ ≤ C_S ‖G‖`. -/
def meqCS (W : ℕ) (b : ℝ) (σ : LayerShape) : ℝ :=
  ∑ i : TflCoord W σ, (tflVar W b σ i : ℝ) * ‖tflLin W b σ (Pi.single i 1)‖ ^ 2

theorem meqCS_nonneg (W : ℕ) (b : ℝ) (σ : LayerShape) : 0 ≤ meqCS W b σ :=
  Finset.sum_nonneg fun i _ => mul_nonneg (tflVar W b σ i).2 (by positivity)

theorem meq_norm_meqS_le (b : ℝ) (G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    ‖meqS W b σ G‖ ≤ meqCS W b σ * ‖G‖ := by
  unfold meqS meqCS
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  set Λ := tflLin W b σ (Pi.single i 1)
  have hv : ‖((tflVar W b σ i : ℝ≥0) : ℝ)‖ = (tflVar W b σ i : ℝ) := by simp
  have h1 : ‖Λ * G * Λ‖ ≤ ‖Λ‖ ^ 2 * ‖G‖ :=
    calc ‖Λ * G * Λ‖ ≤ ‖Λ * G‖ * ‖Λ‖ := norm_mul_le _ _
      _ ≤ ‖Λ‖ * ‖G‖ * ‖Λ‖ := by gcongr; exact norm_mul_le _ _
      _ = ‖Λ‖ ^ 2 * ‖G‖ := by ring
  calc ‖(tflVar W b σ i : ℝ) • (Λ * G * Λ)‖ = (tflVar W b σ i : ℝ) * ‖Λ * G * Λ‖ := by
        rw [norm_smul, hv]
    _ ≤ (tflVar W b σ i : ℝ) * (‖Λ‖ ^ 2 * ‖G‖) :=
        mul_le_mul_of_nonneg_left h1 (tflVar W b σ i).2
    _ = (tflVar W b σ i : ℝ) * ‖Λ‖ ^ 2 * ‖G‖ := by ring

theorem meq_continuous_meqS (b : ℝ) :
    Continuous (fun G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ => meqS W b σ G) := by
  unfold meqS
  refine continuous_finsetSum _ fun i _ => ?_
  fun_prop

theorem meq_continuous_meqS_mul (b : ℝ) :
    Continuous (fun G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ => meqS W b σ G * G) :=
  (meq_continuous_meqS b).mul continuous_id

section Coordinates

variable (W : ℕ) (b : ℝ) (σ : LayerShape) (E : ℝ) (z : ℂ)
  (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)

/-- The coordinate-linear part of the layer matrix as a continuous linear map. -/
def meqLc : (TflCoord W σ → ℝ) →L[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  LinearMap.toContinuousLinearMap (tflLinMap W b σ)

theorem meqLc_apply (x : TflCoord W σ → ℝ) : meqLc W b σ x = tflLin W b σ x := rfl

/-- The regularized resolvent `G_κ = (𝒢⁻¹ + iκ)⁻¹` in the real coordinates. -/
def meqG (κ : ℝ) (x : TflCoord W σ → ℝ) : Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  Ring.inverse (tflPsi W b σ E z X κ x)

variable {X}

theorem meqG_hasFDerivAt (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (x : TflCoord W σ → ℝ) :
    HasFDerivAt (meqG W b σ E z X κ)
      ((-(ContinuousLinearMap.mulLeftRight ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
        (meqG W b σ E z X κ x) (meqG W b σ E z X κ x))).comp (meqLc W b σ)) x := by
  set u := (tflPsi_isUnit W b σ E z hX hz hκ x).unit with hu
  have hL : HasFDerivAt (tflPsi W b σ E z X κ) (meqLc W b σ) x :=
    (ContinuousLinearMap.hasFDerivAt _).const_add _
  have h : HasFDerivAt Ring.inverse
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) ↑u⁻¹ ↑u⁻¹))
      (tflPsi W b σ E z X κ x) := by
    have := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rwa [IsUnit.unit_spec] at this
  have hinv : (↑u⁻¹ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) = meqG W b σ E z X κ x := by
    rw [meqG, ← Ring.inverse_unit, IsUnit.unit_spec]
  rw [hinv] at h
  exact h.comp x hL

theorem meqG_contDiff (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ) :
    ContDiff ℝ 1 (meqG W b σ E z X κ) := by
  have hL : ContDiff ℝ 1 (tflPsi W b σ E z X κ) :=
    contDiff_const.add (ContinuousLinearMap.contDiff _)
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  have h := contDiffAt_ringInverse ℝ (n := 1) (tflPsi_isUnit W b σ E z hX hz hκ x).unit
  rw [IsUnit.unit_spec] at h
  exact h.comp x hL.contDiffAt

theorem meqG_norm_le (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (x : TflCoord W σ → ℝ) : ‖meqG W b σ E z X κ x‖ ≤ κ⁻¹ :=
  tflPsi_inv_le W b σ E z hX hz hκ x

theorem meq_ibp_coord (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (i : TflCoord W σ) :
    ∫ x, x i • (tflLin W b σ (Pi.single i 1) * meqG W b σ E z X κ x)
        ∂gaussianProduct (tflVar W b σ) =
      (tflVar W b σ i : ℝ) • ∫ x, -(tflLin W b σ (Pi.single i 1) * meqG W b σ E z X κ x *
        tflLin W b σ (Pi.single i 1) * meqG W b σ E z X κ x) ∂gaussianProduct (tflVar W b σ) := by
  set Λ := tflLin W b σ (Pi.single i 1) with hΛ
  set G := meqG W b σ E z X κ with hG
  have hk : ContDiff ℝ 1 (fun x => Λ * G x) :=
    (ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) Λ).contDiff.comp
      (meqG_contDiff W b σ E z hX hz hκ)
  have hder : ∀ x, HasFDerivAt (fun x => Λ * G x)
      ((ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) Λ).comp
        ((-(ContinuousLinearMap.mulLeftRight ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
          (G x) (G x))).comp (meqLc W b σ))) x :=
    fun x => ((ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
      Λ).hasFDerivAt).comp x
      (meqG_hasFDerivAt W b σ E z hX hz hκ x)
  have hκi : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  have hb : ∀ x, ‖Λ * G x‖ ≤ ‖Λ‖ * κ⁻¹ := fun x =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (meqG_norm_le W b σ E z hX hz hκ x)
      (norm_nonneg _))
  have hb' : ∀ x, ‖fderiv ℝ (fun x => Λ * G x) x‖ ≤ ‖Λ‖ * (κ⁻¹ * ‖meqLc W b σ‖ * κ⁻¹) := by
    intro x
    rw [(hder x).fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
      _root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply]
    have hGx := meqG_norm_le W b σ E z hX hz hκ x
    calc ‖Λ * -(G x * (meqLc W b σ) v * G x)‖ ≤ ‖Λ‖ * (‖G x‖ * ‖(meqLc W b σ) v‖ * ‖G x‖) := by
          refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
          rw [norm_neg]
          refine (norm_mul_le _ _).trans ?_
          gcongr
          exact norm_mul_le _ _
      _ ≤ ‖Λ‖ * (κ⁻¹ * (‖meqLc W b σ‖ * ‖v‖) * κ⁻¹) := by
          gcongr
          exact (meqLc W b σ).le_opNorm v
      _ = ‖Λ‖ * (κ⁻¹ * ‖meqLc W b σ‖ * κ⁻¹) * ‖v‖ := by ring
  rw [ou_ibp (tflVar W b σ) i hk hb hb']
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  beta_reduce
  rw [(hder x).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    _root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, meqLc_apply]
  rw [← hΛ]
  simp only [Matrix.mul_neg, Matrix.mul_assoc]

theorem meqG_continuous (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ) :
    Continuous (meqG W b σ E z X κ) :=
  (meqG_contDiff W b σ E z hX hz hκ).continuous

theorem meqG_integrable (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ) :
    Integrable (meqG W b σ E z X κ) (gaussianProduct (tflVar W b σ)) :=
  Integrable.of_bound (meqG_continuous W b σ E z hX hz hκ).aestronglyMeasurable κ⁻¹
    (ae_of_all _ fun x => meqG_norm_le W b σ E z hX hz hκ x)

theorem meq_lin_decomp (x : TflCoord W σ → ℝ) :
    tflLin W b σ x = ∑ i, x i • tflLin W b σ (Pi.single i 1) := by
  have h := LinearMap.pi_apply_eq_sum_univ (tflLinMap W b σ) x
  have hs : ∀ i : TflCoord W σ, (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 :=
    fun i => by funext j; simp [Pi.single_apply, eq_comm]
  simp only [hs] at h
  exact h

/-- **Gaussian integration by parts for the regularized resolvent**:
`E[Λ(x) G_κ] = -E[𝒮(G_κ) G_κ]`, `𝒮(G) = Σᵢ vᵢ Λᵢ G Λᵢ`. -/
theorem meq_ibp (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ) :
    ∫ x, tflLin W b σ x * meqG W b σ E z X κ x ∂gaussianProduct (tflVar W b σ) =
      -∫ x, meqS W b σ (meqG W b σ E z X κ x) * meqG W b σ E z X κ x
        ∂gaussianProduct (tflVar W b σ) := by
  set μ := gaussianProduct (tflVar W b σ)
  set G := meqG W b σ E z X κ with hG
  have hGc : Continuous G := meqG_continuous W b σ E z hX hz hκ
  have hGb : ∀ x, ‖G x‖ ≤ κ⁻¹ := meqG_norm_le W b σ E z hX hz hκ
  have hκi : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  have hdec : ∀ x, tflLin W b σ x * G x =
      ∑ i, x i • (tflLin W b σ (Pi.single i 1) * G x) := by
    intro x
    rw [meq_lin_decomp, Finset.sum_mul]
    simp only [Matrix.smul_mul]
  have hint : ∀ i : TflCoord W σ,
      Integrable (fun x => x i • (tflLin W b σ (Pi.single i 1) * G x)) μ := by
    intro i
    refine ou_integrable_of_norm_le μ
      ((continuous_apply i).smul (continuous_const.mul hGc)).aestronglyMeasurable 0
      (‖tflLin W b σ (Pi.single i 1)‖ * κ⁻¹) fun x => ?_
    rw [norm_smul, zero_add]
    have h1 : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
    have h2 : ‖tflLin W b σ (Pi.single i 1) * G x‖ ≤ ‖tflLin W b σ (Pi.single i 1)‖ * κ⁻¹ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hGb x) (norm_nonneg _))
    calc ‖x i‖ * ‖tflLin W b σ (Pi.single i 1) * G x‖
        ≤ ‖x‖ * (‖tflLin W b σ (Pi.single i 1)‖ * κ⁻¹) :=
          mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
      _ = ‖tflLin W b σ (Pi.single i 1)‖ * κ⁻¹ * ‖x‖ := by ring
  have hint2 : ∀ i : TflCoord W σ, Integrable (fun x => -(tflLin W b σ (Pi.single i 1) * G x *
      tflLin W b σ (Pi.single i 1) * G x)) μ := by
    intro i
    refine Integrable.of_bound (by fun_prop) (‖tflLin W b σ (Pi.single i 1)‖ ^ 2 * κ⁻¹ ^ 2)
      (ae_of_all _ fun x => ?_)
    set Λ := tflLin W b σ (Pi.single i 1)
    rw [norm_neg]
    calc ‖Λ * G x * Λ * G x‖ ≤ ‖Λ * G x * Λ‖ * ‖G x‖ := norm_mul_le _ _
      _ ≤ ‖Λ * G x‖ * ‖Λ‖ * ‖G x‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ‖Λ‖ * ‖G x‖ * ‖Λ‖ * ‖G x‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ‖Λ‖ * κ⁻¹ * ‖Λ‖ * κ⁻¹ := by gcongr <;> exact hGb x
      _ = ‖Λ‖ ^ 2 * κ⁻¹ ^ 2 := by ring
  have hpt : ∀ x, -(meqS W b σ (G x) * G x) = ∑ i, (tflVar W b σ i : ℝ) •
      -(tflLin W b σ (Pi.single i 1) * G x * tflLin W b σ (Pi.single i 1) * G x) := by
    intro x
    unfold meqS
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mul, smul_neg]
  have hint3 : ∀ i : TflCoord W σ, Integrable (fun x => (tflVar W b σ i : ℝ) •
      -(tflLin W b σ (Pi.single i 1) * G x * tflLin W b σ (Pi.single i 1) * G x)) μ :=
    fun i => (hint2 i).fun_smul (tflVar W b σ i : ℝ)
  rw [integral_congr_ae (ae_of_all _ hdec), integral_finsetSum _ fun i _ => hint i,
    ← integral_neg, integral_congr_ae (ae_of_all _ hpt),
    integral_finsetSum _ fun i _ => hint3 i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul]
  exact meq_ibp_coord W b σ E z hX hz hκ i

/-- **Regularized Schwinger–Dyson identity in coordinates**:
`(𝒟 + iκ) E[G_κ] - E[𝒮(G_κ) G_κ] = I`. -/
theorem meq_reg_core (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ) :
    (tflConst σ E z X + ((κ : ℂ) * Complex.I) • (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) *
        ∫ x, meqG W b σ E z X κ x ∂gaussianProduct (tflVar W b σ) -
      ∫ x, meqS W b σ (meqG W b σ E z X κ x) * meqG W b σ E z X κ x
        ∂gaussianProduct (tflVar W b σ) = 1 := by
  set μ := gaussianProduct (tflVar W b σ)
  set G := meqG W b σ E z X κ with hG
  set C := tflConst σ E z X + ((κ : ℂ) * Complex.I) •
    (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) with hC
  have hGc : Continuous G := meqG_continuous W b σ E z hX hz hκ
  have hGi : Integrable G μ := meqG_integrable W b σ E z hX hz hκ
  have hpt : ∀ x, C * G x + tflLin W b σ x * G x = 1 := by
    intro x
    rw [← add_mul]
    have : C + tflLin W b σ x = tflPsi W b σ E z X κ x := rfl
    rw [this]
    exact Ring.mul_inverse_cancel _ (tflPsi_isUnit W b σ E z hX hz hκ x)
  have hint2 : Integrable (fun x => tflLin W b σ x * G x) μ := by
    refine ou_integrable_of_norm_le μ
      (((meqLc W b σ).continuous.mul hGc).aestronglyMeasurable) 0
      (‖meqLc W b σ‖ * κ⁻¹) fun x => ?_
    rw [zero_add]
    calc ‖tflLin W b σ x * G x‖ ≤ ‖tflLin W b σ x‖ * ‖G x‖ := norm_mul_le _ _
      _ ≤ (‖meqLc W b σ‖ * ‖x‖) * κ⁻¹ := by
          gcongr
          · exact (meqLc W b σ).le_opNorm x
          · exact meqG_norm_le W b σ E z hX hz hκ x
      _ = ‖meqLc W b σ‖ * κ⁻¹ * ‖x‖ := by ring
  have h1 : ∫ x, (C * G x + tflLin W b σ x * G x) ∂μ = 1 := by
    rw [integral_congr_ae (ae_of_all _ hpt), integral_const, probReal_univ, one_smul]
  rw [integral_add (hGi.const_mul C) hint2, meq_ibp W b σ E z hX hz hκ] at h1
  have h2 : ∫ x, C * G x ∂μ = C * ∫ x, G x ∂μ :=
    (ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) C).integral_comp_comm hGi
  rw [h2] at h1
  rw [sub_eq_add_neg]
  exact h1

/-- `‖𝒮(G) G‖ ≤ C_S ‖G‖²`. -/
theorem meq_norm_meqS_mul_le (G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    ‖meqS W b σ G * G‖ ≤ meqCS W b σ * ‖G‖ ^ 2 := by
  calc ‖meqS W b σ G * G‖ ≤ ‖meqS W b σ G‖ * ‖G‖ := norm_mul_le _ _
    _ ≤ meqCS W b σ * ‖G‖ * ‖G‖ := by gcongr; exact meq_norm_meqS_le b G
    _ = meqCS W b σ * ‖G‖ ^ 2 := by ring

/-- **The `κ → 0` limit in coordinates**: if the layer matrix is a.s. invertible and
`‖𝒢‖ ∈ L¹ ∩ L²`, then `𝒟 E[𝒢] - E[𝒮(𝒢) 𝒢] = I`. -/
theorem meq_limit_core (hX : X.IsHermitian) (hz : 0 ≤ z.im)
    (hinv : ∀ᵐ x ∂gaussianProduct (tflVar W b σ),
      IsUnit (layerMatrix σ E z X (tflEmbed W b σ x)).det)
    (hG1 : Integrable (fun x => ‖layerResolvent σ E z X (tflEmbed W b σ x)‖)
      (gaussianProduct (tflVar W b σ)))
    (hG2 : Integrable (fun x => ‖layerResolvent σ E z X (tflEmbed W b σ x)‖ ^ 2)
      (gaussianProduct (tflVar W b σ))) :
    tflConst σ E z X * ∫ x, layerResolvent σ E z X (tflEmbed W b σ x)
        ∂gaussianProduct (tflVar W b σ) -
      ∫ x, meqS W b σ (layerResolvent σ E z X (tflEmbed W b σ x)) *
        layerResolvent σ E z X (tflEmbed W b σ x) ∂gaussianProduct (tflVar W b σ) = 1 := by
  set μ := gaussianProduct (tflVar W b σ)
  set Φ := tflEmbed W b σ with hΦdef
  set G0 : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun x => layerResolvent σ E z X (Φ x) with hG0
  have hG0m : Measurable G0 :=
    (measurable_layerResolvent σ E z X).comp (tfl_measurable_embed W b σ)
  set κm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hκm
  have hκpos : ∀ m, 0 < κm m := fun m => by rw [hκm]; positivity
  have hκlim : Tendsto κm atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set Gm : ℕ → (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun m => meqG W b σ E z X (κm m) with hGm
  have hGmc : ∀ m, Continuous (Gm m) := fun m => meqG_continuous W b σ E z hX hz (hκpos m)
  have hconv : ∀ᵐ x ∂μ, Tendsto (fun m => Gm m x) atTop (𝓝 (G0 x)) := by
    filter_upwards [hinv] with x hx
    set N := layerMatrix σ E z X (Φ x) with hN
    have hU : IsUnit N := (Matrix.isUnit_iff_isUnit_det N).mpr hx
    have hcN : Continuous (fun κ : ℝ => N + ((κ : ℂ) * Complex.I) •
        (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) := by fun_prop
    have h1 : Tendsto (fun m => tflPsi W b σ E z X (κm m) x) atTop (𝓝 N) := by
      have := (hcN.tendsto 0).comp hκlim
      simp only [Complex.ofReal_zero, zero_mul, zero_smul, add_zero] at this
      refine this.congr fun m => ?_
      simp only [Function.comp_apply]
      rw [tflPsi_eq, tflReg]
    have h2 : Tendsto (fun m => Ring.inverse (tflPsi W b σ E z X (κm m) x)) atTop
        (𝓝 (Ring.inverse N)) := by
      have hc := NormedRing.inverse_continuousAt hU.unit
      rw [IsUnit.unit_spec] at hc
      exact hc.tendsto.comp h1
    have hG0x : G0 x = Ring.inverse N := by
      rw [hG0]
      simp only [layerResolvent]
      rw [Matrix.nonsing_inv_eq_ringInverse]
    rw [hG0x]
    exact h2
  have hbd : ∀ m, ∀ᵐ x ∂μ, ‖Gm m x‖ ≤ 2 * ‖G0 x‖ := by
    intro m
    filter_upwards [hinv] with x hx
    exact tflPsi_inv_le_two W b σ E z hX hz (hκpos m) x hx
  have hlim1 : Tendsto (fun m => ∫ x, Gm m x ∂μ) atTop (𝓝 (∫ x, G0 x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => 2 * ‖G0 x‖)
      (fun m => (hGmc m).aestronglyMeasurable) (hG1.const_mul 2) hbd hconv
  have hbd2 : ∀ m, ∀ᵐ x ∂μ, ‖meqS W b σ (Gm m x) * Gm m x‖ ≤
      4 * meqCS W b σ * ‖G0 x‖ ^ 2 := by
    intro m
    filter_upwards [hbd m] with x hx
    refine (meq_norm_meqS_mul_le W b σ (Gm m x)).trans ?_
    have h0 : ‖Gm m x‖ ^ 2 ≤ (2 * ‖G0 x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
    have hCS := meqCS_nonneg W b σ
    nlinarith
  have hconv2 : ∀ᵐ x ∂μ, Tendsto (fun m => meqS W b σ (Gm m x) * Gm m x) atTop
      (𝓝 (meqS W b σ (G0 x) * G0 x)) :=
    hconv.mono fun x hx => ((meq_continuous_meqS_mul b).tendsto _).comp hx
  have hlim2 : Tendsto (fun m => ∫ x, meqS W b σ (Gm m x) * Gm m x ∂μ) atTop
      (𝓝 (∫ x, meqS W b σ (G0 x) * G0 x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => 4 * meqCS W b σ * ‖G0 x‖ ^ 2)
      (fun m => ((meq_continuous_meqS_mul b).comp (hGmc m)).aestronglyMeasurable)
      (hG2.const_mul _) hbd2 hconv2
  have hcC : Continuous (fun κ : ℝ => tflConst σ E z X + ((κ : ℂ) * Complex.I) •
      (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) := by fun_prop
  have hlimC : Tendsto (fun m => tflConst σ E z X + ((κm m : ℂ) * Complex.I) •
      (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) atTop (𝓝 (tflConst σ E z X)) := by
    have := (hcC.tendsto 0).comp hκlim
    simp only [Complex.ofReal_zero, zero_mul, zero_smul, add_zero] at this
    exact this
  have hlim := (hlimC.mul hlim1).sub hlim2
  have hconst : (fun m => (tflConst σ E z X + ((κm m : ℂ) * Complex.I) •
      (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) * ∫ x, Gm m x ∂μ -
        ∫ x, meqS W b σ (Gm m x) * Gm m x ∂μ) = fun _ => 1 := by
    funext m
    exact meq_reg_core W b σ E z hX hz (hκpos m)
  rw [hconst] at hlim
  exact (tendsto_nhds_unique hlim tendsto_const_nhds)

end Coordinates

/-!
## 3. Transfer to the layer law
-/

instance meq_isProbabilityMeasure_layerLaw (W : ℕ) (b : ℝ) (σ : LayerShape) :
    IsProbabilityMeasure (layerLaw W b σ) := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  unfold layerLaw
  infer_instance

/-- The regularized layer resolvent `G_κ(ω) = (𝒢(ω)⁻¹ + iκ)⁻¹` on the layer samples. -/
def meqRegResolvent {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (κ : ℝ) (ω : LayerSample W σ) :
    Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  (tflReg κ (layerMatrix σ E z X ω))⁻¹

theorem meq_measurable_regResolvent {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (κ : ℝ) :
    Measurable (meqRegResolvent σ E z X κ) := by
  have hc : Continuous (fun N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ => tflReg κ N) := by
    unfold tflReg; fun_prop
  exact measurable_matrix_inv.comp (hc.measurable.comp (measurable_layerMatrix σ E z X))

theorem meq_regResolvent_embed (W : ℕ) (b : ℝ) (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (κ : ℝ) (x : TflCoord W σ → ℝ) :
    meqRegResolvent σ E z X κ (tflEmbed W b σ x) = meqG W b σ E z X κ x :=
  (tflPsi_inv_eq W b σ E z X κ x).symm

/-- **Regularized identity on `layerLaw`** (every `W`, every `κ > 0`):
`(𝒟 + iκ) E[G_κ] - E[𝒮(G_κ) G_κ] = I` (Bochner integrals). -/
theorem meq_reg_law {W : ℕ} (b : ℝ) (σ : LayerShape) (E : ℝ) {z : ℂ}
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ}
    (hκ : 0 < κ) :
    (tflConst σ E z X + ((κ : ℂ) * Complex.I) • (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) *
        ∫ ω, meqRegResolvent σ E z X κ ω ∂layerLaw W b σ -
      ∫ ω, meqS W b σ (meqRegResolvent σ E z X κ ω) * meqRegResolvent σ E z X κ ω
        ∂layerLaw W b σ = 1 := by
  have hΦ := tfl_measurable_embed W b σ
  have hm := meq_measurable_regResolvent σ E z X κ
  rw [tfl_layerLaw_eq_map, integral_map hΦ.aemeasurable hm.aestronglyMeasurable,
    integral_map (f := fun ω => meqS W b σ (meqRegResolvent σ E z X κ ω) *
      meqRegResolvent σ E z X κ ω) hΦ.aemeasurable
      ((meq_continuous_meqS_mul b).measurable.comp hm).aestronglyMeasurable]
  simp only [meq_regResolvent_embed]
  exact meq_reg_core W b σ E z hX hz hκ

/-- `‖G‖ ∈ L¹` from `‖G‖² ∈ L¹` on a probability space. -/
theorem meq_integrable_norm_of_sq {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Ω → Matrix ι ι ℂ}
    (hGm : AEStronglyMeasurable G ν) (hG2 : Integrable (fun ω => ‖G ω‖ ^ 2) ν) :
    Integrable (fun ω => ‖G ω‖) ν := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hG2) hGm.norm
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (norm_nonneg _), Pi.add_apply]
  nlinarith [sq_nonneg (‖G ω‖ - 1), norm_nonneg (G ω)]

/-- **Exact identity on `layerLaw`** under a.s. invertibility and `‖𝒢‖ ∈ L²`:
`𝒟 E[𝒢] - E[𝒮(𝒢) 𝒢] = I` (Bochner integrals). -/
theorem meq_limit_law {W : ℕ} (b : ℝ) (σ : LayerShape) (E : ℝ) {z : ℂ}
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (hz : 0 ≤ z.im)
    (hinv : ∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det)
    (hG2 : Integrable (fun ω => ‖layerResolvent σ E z X ω‖ ^ 2) (layerLaw W b σ)) :
    tflConst σ E z X * ∫ ω, layerResolvent σ E z X ω ∂layerLaw W b σ -
      ∫ ω, meqS W b σ (layerResolvent σ E z X ω) * layerResolvent σ E z X ω
        ∂layerLaw W b σ = 1 := by
  have hΦ := tfl_measurable_embed W b σ
  have hm := measurable_layerResolvent σ E z X
  have hG1 : Integrable (fun ω => ‖layerResolvent σ E z X ω‖) (layerLaw W b σ) :=
    meq_integrable_norm_of_sq hm.aestronglyMeasurable hG2
  rw [tfl_layerLaw_eq_map] at hinv hG1 hG2 ⊢
  rw [integral_map hΦ.aemeasurable hm.aestronglyMeasurable,
    integral_map (f := fun ω => meqS W b σ (layerResolvent σ E z X ω) *
      layerResolvent σ E z X ω) hΦ.aemeasurable
      ((meq_continuous_meqS_mul b).measurable.comp hm).aestronglyMeasurable]
  rw [integrable_map_measure (g := fun ω => ‖layerResolvent σ E z X ω‖)
    (continuous_norm.measurable.comp hm).aestronglyMeasurable hΦ.aemeasurable] at hG1
  rw [integrable_map_measure (g := fun ω => ‖layerResolvent σ E z X ω‖ ^ 2)
    ((continuous_norm.pow 2).measurable.comp hm).aestronglyMeasurable hΦ.aemeasurable] at hG2
  exact meq_limit_core W b σ E z hX hz (ae_of_ae_map hΦ.aemeasurable hinv) hG1 hG2

/-!
## 4. Covariance bookkeeping
-/

section Expansion

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Matrix covariance `Cov(f, U) = E[f U] - E[f] E[U]` with entrywise expectations
(`matrixExpect`), the form bounded by `TraceMatrixContract.covariance`. -/
def meqCov {ι : Type*} (ν : Measure Ω) (f : Ω → ℂ) (U : Ω → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  matrixExpect ν (fun ω => f ω • U ω) - (∫ ω, f ω ∂ν) • matrixExpect ν U

/-- Mean normalized physical block trace `ḡ_a = E W⁻¹ Tr P_a G`. -/
def meqMeanA (ν : Measure Ω) (G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (a : Fin σ.blocks) : ℂ :=
  ∫ ω, physBlockTrace (G ω) a ∂ν

/-- Mean normalized port block trace `ḡ_{port j} = E W⁻¹ Tr Q_j G`. -/
def meqMeanP (ν : Measure Ω) (G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (j : Fin σ.ports) : ℂ :=
  ∫ ω, portBlockTrace (G ω) j ∂ν

/-- The covariance residual
`Σ_a c Cov(g_a, P_a G) + Σ_{a ~ j} b (Cov(g_{port j}, P_a G) + Cov(g_a, Q_j G))`. -/
def meqResid (ν : Measure Ω) (c b : ℂ) (G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  ∑ a, c • meqCov ν (fun ω => physBlockTrace (G ω) a) (fun ω => meqPhysProj a * G ω) +
    ∑ a, ∑ j, (b * meqInc σ a j) •
      (meqCov ν (fun ω => portBlockTrace (G ω) j) (fun ω => meqPhysProj a * G ω) +
        meqCov ν (fun ω => physBlockTrace (G ω) a) (fun ω => meqPortProj j * G ω))

theorem meq_matrixExpect_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {ν : Measure Ω}
    {U : Ω → Matrix ι ι ℂ} (hU : Integrable U ν) : matrixExpect ν U = ∫ ω, U ω ∂ν := by
  ext x y
  have h := (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℂ ℂ x y : Matrix ι ι ℂ →ₗ[ℂ] ℂ)).integral_comp_comm hU
  simpa [matrixExpect] using h

theorem meq_cov_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {ν : Measure Ω} {f : Ω → ℂ}
    {U : Ω → Matrix ι ι ℂ} (hfU : Integrable (fun ω => f ω • U ω) ν) (hU : Integrable U ν) :
    meqCov ν f U = ∫ ω, f ω • U ω ∂ν - (∫ ω, f ω ∂ν) • ∫ ω, U ω ∂ν := by
  rw [meqCov, meq_matrixExpect_eq hfU, meq_matrixExpect_eq hU]

/-- `|W⁻¹ Tr P_a M| ≤ ‖M‖`. -/
theorem meq_norm_physBlockTrace_le (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (a : Fin σ.blocks) : ‖physBlockTrace M a‖ ≤ ‖M‖ := by
  unfold physBlockTrace
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : ‖∑ α : Fin W, M (Sum.inl (a, α)) (Sum.inl (a, α))‖ ≤ W * ‖M‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ α : Fin W, ‖M (Sum.inl (a, α)) (Sum.inl (a, α))‖ ≤ ∑ _α : Fin W, ‖M‖ :=
          Finset.sum_le_sum fun α _ => tfl_entry_le M _ _
      _ = W * ‖M‖ := by simp
  calc (W : ℝ)⁻¹ * ‖∑ α : Fin W, M (Sum.inl (a, α)) (Sum.inl (a, α))‖ ≤ (W : ℝ)⁻¹ * (W * ‖M‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ‖M‖ := by field_simp

/-- `|W⁻¹ Tr Q_j M| ≤ ‖M‖`. -/
theorem meq_norm_portBlockTrace_le (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (j : Fin σ.ports) : ‖portBlockTrace M j‖ ≤ ‖M‖ := by
  unfold portBlockTrace
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : ‖∑ α : Fin W, M (Sum.inr (j, α)) (Sum.inr (j, α))‖ ≤ W * ‖M‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ α : Fin W, ‖M (Sum.inr (j, α)) (Sum.inr (j, α))‖ ≤ ∑ _α : Fin W, ‖M‖ :=
          Finset.sum_le_sum fun α _ => tfl_entry_le M _ _
      _ = W * ‖M‖ := by simp
  calc (W : ℝ)⁻¹ * ‖∑ α : Fin W, M (Sum.inr (j, α)) (Sum.inr (j, α))‖ ≤ (W : ℝ)⁻¹ * (W * ‖M‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ‖M‖ := by field_simp

theorem meq_continuous_physBlockTrace (a : Fin σ.blocks) :
    Continuous (fun M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ => physBlockTrace M a) := by
  unfold physBlockTrace
  fun_prop

theorem meq_continuous_portBlockTrace (j : Fin σ.ports) :
    Continuous (fun M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ => portBlockTrace M j) := by
  unfold portBlockTrace
  fun_prop

theorem meq_integrable_trace_smul {ν : Measure Ω} [IsFiniteMeasure ν]
    {G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hGm : AEStronglyMeasurable G ν)
    (hG2 : Integrable (fun ω => ‖G ω‖ ^ 2) ν)
    {f : Matrix (LayerSite W σ) (LayerSite W σ) ℂ → ℂ} (hf : Continuous f)
    (hfb : ∀ M, ‖f M‖ ≤ ‖M‖) (P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    Integrable (fun ω => f (G ω) • (P * G ω)) ν := by
  refine Integrable.mono' (hG2.const_mul ‖P‖)
    ((hf.comp_aestronglyMeasurable hGm).smul
      ((continuous_const.mul continuous_id).comp_aestronglyMeasurable hGm))
    (ae_of_all _ fun ω => ?_)
  rw [norm_smul]
  calc ‖f (G ω)‖ * ‖P * G ω‖ ≤ ‖G ω‖ * (‖P‖ * ‖G ω‖) :=
        mul_le_mul (hfb _) (norm_mul_le _ _) (norm_nonneg _) (norm_nonneg _)
    _ = ‖P‖ * ‖G ω‖ ^ 2 := by ring

/-- **Covariance expansion of the self-energy term**: for any probability law, any random
matrix `G` with `‖G‖ ∈ L²` and any coefficients `c, b`,
`E[𝒮_{c,b}(g(G)) G] = 𝒮_{c,b}(ḡ) E[G] + Σ_a c Cov(g_a, P_a G)
  + Σ_{a~j} b (Cov(g_{port j}, P_a G) + Cov(g_a, Q_j G))`. -/
theorem meq_expand {ν : Measure Ω} [IsProbabilityMeasure ν]
    {G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hGm : AEStronglyMeasurable G ν)
    (hG2 : Integrable (fun ω => ‖G ω‖ ^ 2) ν) (c b : ℂ) :
    ∫ ω, meqShift σ c b (physBlockTrace (G ω)) (portBlockTrace (G ω)) * G ω ∂ν =
      meqShift σ c b (meqMeanA ν G) (meqMeanP ν G) * ∫ ω, G ω ∂ν + meqResid ν c b G := by
  have hG1 := meq_integrable_norm_of_sq hGm hG2
  have hGi : Integrable G ν := Integrable.mono' hG1 hGm (ae_of_all _ fun _ => le_rfl)
  have iPA : ∀ a : Fin σ.blocks, Integrable (fun ω => meqPhysProj a * G ω) ν :=
    fun a => hGi.const_mul _
  have iPQ : ∀ j : Fin σ.ports, Integrable (fun ω => meqPortProj j * G ω) ν :=
    fun j => hGi.const_mul _
  have iAA : ∀ (a a' : Fin σ.blocks), Integrable
      (fun ω => physBlockTrace (G ω) a • (meqPhysProj a' * G ω)) ν := fun a a' =>
    meq_integrable_trace_smul hGm hG2 (meq_continuous_physBlockTrace a)
      (fun M => meq_norm_physBlockTrace_le M a) _
  have iPA' : ∀ (j : Fin σ.ports) (a : Fin σ.blocks), Integrable
      (fun ω => portBlockTrace (G ω) j • (meqPhysProj a * G ω)) ν := fun j a =>
    meq_integrable_trace_smul hGm hG2 (meq_continuous_portBlockTrace j)
      (fun M => meq_norm_portBlockTrace_le M j) _
  have iAQ : ∀ (a : Fin σ.blocks) (j : Fin σ.ports), Integrable
      (fun ω => physBlockTrace (G ω) a • (meqPortProj j * G ω)) ν := fun a j =>
    meq_integrable_trace_smul hGm hG2 (meq_continuous_physBlockTrace a)
      (fun M => meq_norm_physBlockTrace_le M a) _
  have hcomm : ∀ P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      ∫ ω, P * G ω ∂ν = P * ∫ ω, G ω ∂ν := fun P =>
    (ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) P).integral_comp_comm
      hGi
  -- pointwise expansion
  have hpt : ∀ ω, meqShift σ c b (physBlockTrace (G ω)) (portBlockTrace (G ω)) * G ω =
      ∑ a, c • (physBlockTrace (G ω) a • (meqPhysProj a * G ω)) +
        ∑ a, ∑ j, (b * meqInc σ a j) • (portBlockTrace (G ω) j • (meqPhysProj a * G ω) +
          physBlockTrace (G ω) a • (meqPortProj j * G ω)) := by
    intro ω
    rw [meqShift_eq_sum]
    simp only [Matrix.add_mul, Finset.sum_mul, Matrix.smul_mul, smul_smul]
  have hI1 : Integrable (fun ω => ∑ a, c • (physBlockTrace (G ω) a • (meqPhysProj a * G ω))) ν :=
    integrable_finsetSum _ fun a _ => (iAA a a).fun_smul c
  have hI2 : ∀ a, Integrable (fun ω => ∑ j, (b * meqInc σ a j) •
      (portBlockTrace (G ω) j • (meqPhysProj a * G ω) +
        physBlockTrace (G ω) a • (meqPortProj j * G ω))) ν := fun a =>
    integrable_finsetSum _ fun j _ => ((iPA' j a).add (iAQ a j)).fun_smul _
  have e1 : ∀ a, ∫ ω, c • (physBlockTrace (G ω) a • (meqPhysProj a * G ω)) ∂ν =
      c • ∫ ω, physBlockTrace (G ω) a • (meqPhysProj a * G ω) ∂ν := fun a => integral_smul _ _
  have e2 : ∀ a, ∫ ω, ∑ j, (b * meqInc σ a j) • (portBlockTrace (G ω) j • (meqPhysProj a * G ω) +
      physBlockTrace (G ω) a • (meqPortProj j * G ω)) ∂ν =
      ∑ j, (b * meqInc σ a j) • (∫ ω, portBlockTrace (G ω) j • (meqPhysProj a * G ω) ∂ν +
        ∫ ω, physBlockTrace (G ω) a • (meqPortProj j * G ω) ∂ν) := by
    intro a
    rw [integral_finsetSum _ fun j _ => ((iPA' j a).fun_add (iAQ a j)).fun_smul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul, integral_add (iPA' j a) (iAQ a j)]
  have hc1 : ∀ a, meqCov ν (fun ω => physBlockTrace (G ω) a) (fun ω => meqPhysProj a * G ω) =
      ∫ ω, physBlockTrace (G ω) a • (meqPhysProj a * G ω) ∂ν -
        (∫ ω, physBlockTrace (G ω) a ∂ν) • ∫ ω, meqPhysProj a * G ω ∂ν :=
    fun a => meq_cov_eq (iAA a a) (iPA a)
  have hc2 : ∀ a j, meqCov ν (fun ω => portBlockTrace (G ω) j) (fun ω => meqPhysProj a * G ω) =
      ∫ ω, portBlockTrace (G ω) j • (meqPhysProj a * G ω) ∂ν -
        (∫ ω, portBlockTrace (G ω) j ∂ν) • ∫ ω, meqPhysProj a * G ω ∂ν :=
    fun a j => meq_cov_eq (iPA' j a) (iPA a)
  have hc3 : ∀ a j, meqCov ν (fun ω => physBlockTrace (G ω) a) (fun ω => meqPortProj j * G ω) =
      ∫ ω, physBlockTrace (G ω) a • (meqPortProj j * G ω) ∂ν -
        (∫ ω, physBlockTrace (G ω) a ∂ν) • ∫ ω, meqPortProj j * G ω ∂ν :=
    fun a j => meq_cov_eq (iAQ a j) (iPQ j)
  rw [integral_congr_ae (ae_of_all _ hpt),
    integral_add hI1 (integrable_finsetSum _ fun a _ => hI2 a),
    integral_finsetSum _ fun a _ => (iAA a a).fun_smul c,
    integral_finsetSum _ fun a _ => hI2 a,
    Finset.sum_congr rfl fun a _ => e1 a, Finset.sum_congr rfl fun a _ => e2 a]
  rw [meqResid, meqShift_eq_sum]
  simp only [hc1, hc2, hc3]
  simp only [Matrix.add_mul, Finset.sum_mul, Matrix.smul_mul, hcomm, meqMeanA, meqMeanP]
  simp only [smul_sub, smul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib, smul_smul]
  abel

end Expansion

/-!
## 5. The mean equations
-/

theorem meq_coefA {W : ℕ} (hW : 0 < W) {b : ℝ} (hb : b ≤ 1 / 2) :
    (W : ℂ) * ((tflTA W b : ℝ) : ℂ) = 1 - 2 * (b : ℂ) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have h : ((tflTA W b : ℝ)) = (1 - 2 * b) / W := by
    rw [tflTA, Real.coe_toNNReal _ (div_nonneg (by linarith) hW'.le)]
  have hWc : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  rw [h]
  push_cast
  field_simp

theorem meq_coefB {W : ℕ} (hW : 0 < W) {b : ℝ} (hb : 0 ≤ b) :
    (W : ℂ) * ((tflTB W b : ℝ) : ℂ) = (b : ℂ) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have h : ((tflTB W b : ℝ)) = b / W := by
    rw [tflTB, Real.coe_toNNReal _ (div_nonneg hb hW'.le)]
  have hWc : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  rw [h]
  push_cast
  field_simp

/-- From the Bochner form `C E[G] - E[𝒮(G) G] = I` to the covariance form. -/
theorem meq_of_core {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    {σ : LayerShape} {G : LayerSample W σ → Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (hGm : AEStronglyMeasurable G (layerLaw W b σ))
    (hG2 : Integrable (fun ω => ‖G ω‖ ^ 2) (layerLaw W b σ))
    (C : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (h : C * ∫ ω, G ω ∂layerLaw W b σ -
      ∫ ω, meqS W b σ (G ω) * G ω ∂layerLaw W b σ = 1) :
    (C - meqShift σ (1 - 2 * (b : ℂ)) b (meqMeanA (layerLaw W b σ) G)
        (meqMeanP (layerLaw W b σ) G)) * matrixExpect (layerLaw W b σ) G =
      1 + meqResid (layerLaw W b σ) (1 - 2 * (b : ℂ)) b G := by
  have hG1 := meq_integrable_norm_of_sq hGm hG2
  have hGi : Integrable G (layerLaw W b σ) := Integrable.mono' hG1 hGm (ae_of_all _ fun _ => le_rfl)
  simp only [meqS_eq hW, meq_coefA hW hb1, meq_coefB hW hb0] at h
  rw [meq_expand hGm hG2] at h
  rw [meq_matrixExpect_eq hGi, sub_mul, ← h]
  abel

/-- **(1) Regularized Schwinger–Dyson mean equation** (every `W ≥ 1`, `κ > 0`):
with `G_κ = (𝒢⁻¹ + iκ)⁻¹`, `c = 1 - 2b`,
`(𝒟 + iκ - 𝒮_{c,b}(ḡ)) E G_κ = I + Σ_a c Cov(g_a, P_a G_κ)
  + Σ_{a~j} b (Cov(g_{port j}, P_a G_κ) + Cov(g_a, Q_j G_κ))`. -/
theorem meanEquation_reg {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (σ : LayerShape) {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (E : ℝ)
    {z : ℂ} (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ) :
    (tflConst σ E z X + ((κ : ℂ) * Complex.I) • (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) -
        meqShift σ (1 - 2 * (b : ℂ)) b
          (meqMeanA (layerLaw W b σ) (meqRegResolvent σ E z X κ))
          (meqMeanP (layerLaw W b σ) (meqRegResolvent σ E z X κ))) *
        matrixExpect (layerLaw W b σ) (meqRegResolvent σ E z X κ) =
      1 + meqResid (layerLaw W b σ) (1 - 2 * (b : ℂ)) b (meqRegResolvent σ E z X κ) := by
  have hΦ := tfl_measurable_embed W b σ
  have hm := meq_measurable_regResolvent σ E z X κ
  have hG2 : Integrable (fun ω => ‖meqRegResolvent σ E z X κ ω‖ ^ 2) (layerLaw W b σ) := by
    rw [tfl_layerLaw_eq_map, integrable_map_measure
      (g := fun ω => ‖meqRegResolvent σ E z X κ ω‖ ^ 2)
      ((continuous_norm.pow 2).measurable.comp hm).aestronglyMeasurable hΦ.aemeasurable]
    refine Integrable.of_bound (((continuous_norm.pow 2).comp
      (meqG_continuous W b σ E z hX hz hκ)).aestronglyMeasurable.congr
        (ae_of_all _ fun x => ?_)) (κ⁻¹ ^ 2) (ae_of_all _ fun x => ?_)
    · simp [meq_regResolvent_embed]
    · simp only [Function.comp_apply, meq_regResolvent_embed]
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (meqG_norm_le W b σ E z hX hz hκ x) 2
  exact meq_of_core hW hb0 hb1 hm.aestronglyMeasurable hG2 _ (meq_reg_law b σ E hX hz hκ)

/-- **(2) Exact Schwinger–Dyson mean equation** under a.s. invertibility and `‖𝒢‖ ∈ L²`:
`(𝒟 - 𝒮_{c,b}(ḡ)) E𝒢 = I + Σ_a c Cov(g_a, P_a 𝒢)
  + Σ_{a~j} b (Cov(g_{port j}, P_a 𝒢) + Cov(g_a, Q_j 𝒢))`, `𝒟 = diag(-E - X, z)`,
`c = 1 - 2b`. -/
theorem meanEquation_of_moments {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (σ : LayerShape) {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (E : ℝ)
    {z : ℂ} (hz : 0 ≤ z.im)
    (hinv : ∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det)
    (hG2 : Integrable (fun ω => ‖layerResolvent σ E z X ω‖ ^ 2) (layerLaw W b σ)) :
    (tflConst σ E z X - meqShift σ (1 - 2 * (b : ℂ)) b
          (meqMeanA (layerLaw W b σ) (layerResolvent σ E z X))
          (meqMeanP (layerLaw W b σ) (layerResolvent σ E z X))) *
        matrixExpect (layerLaw W b σ) (layerResolvent σ E z X) =
      1 + meqResid (layerLaw W b σ) (1 - 2 * (b : ℂ)) b (layerResolvent σ E z X) :=
  meq_of_core hW hb0 hb1 (measurable_layerResolvent σ E z X).aestronglyMeasurable hG2 _
    (meq_limit_law b σ E hX hz hinv hG2)

/-- The second moment `‖𝒢‖ ∈ L²` from `GaussianAbsorptionContract` once `2 ≤ ε₁ W`. -/
theorem meq_sq_integrable_of_eLpNorm {W : ℕ} {b : ℝ} {σ : LayerShape} {E : ℝ} {z : ℂ}
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} {C : ℝ}
    (h : eLpNorm (fun ω => ‖layerResolvent σ E z X ω‖) (ENNReal.ofReal 2) (layerLaw W b σ) ≤
      ENNReal.ofReal C) :
    Integrable (fun ω => ‖layerResolvent σ E z X ω‖ ^ 2) (layerLaw W b σ) := by
  have h2 : ENNReal.ofReal 2 = 2 := by simp
  rw [h2] at h
  have hm : MemLp (fun ω => ‖layerResolvent σ E z X ω‖) 2 (layerLaw W b σ) :=
    memLp_iff.mpr (lt_of_le_of_lt h ENNReal.ofReal_lt_top)
  exact hm.integrable_sq

/-- **(2') Exact mean equation from `GaussianAbsorptionContract`**: for `0 < b < 1/2` and
`η₀ > 0, M` there is `W₀` such that for `W ≥ W₀`, every shape, Hermitian `X`, real `E` and
`Im z ≥ η₀`, `|z| ≤ M`, the identity of `meanEquation_of_moments` holds. (`W₀ = ⌈2/ε₁⌉`,
only the second moment of `‖𝒢‖` is used.) -/
theorem meanEquation_holds (habs : GaussianAbsorptionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ η₀ M : ℝ, 0 < η₀ →
      ∃ W₀ : ℕ, ∀ W : ℕ, 0 < W → W₀ ≤ W →
        ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian →
        ∀ (E : ℝ) (z : ℂ), η₀ ≤ z.im → ‖z‖ ≤ M →
          (tflConst σ E z X - meqShift σ (1 - 2 * (b : ℂ)) b
                (meqMeanA (layerLaw W b σ) (layerResolvent σ E z X))
                (meqMeanP (layerLaw W b σ) (layerResolvent σ E z X))) *
              matrixExpect (layerLaw W b σ) (layerResolvent σ E z X) =
            1 + meqResid (layerLaw W b σ) (1 - 2 * (b : ℂ)) b (layerResolvent σ E z X) := by
  intro b hb0 hb1 η₀ M hη
  obtain ⟨ε₁, C, hε₁, hC, habs'⟩ := habs b hb0 hb1 η₀ M hη
  refine ⟨⌈2 / ε₁⌉₊, fun W hW hWW σ X hX E z hz hzM => ?_⟩
  obtain ⟨hinv, hmom⟩ := habs' W hW σ X hX E z hz hzM
  have h2 : (2 : ℝ) ≤ ε₁ * W := by
    have h1 : 2 / ε₁ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWW)
    rw [div_le_iff₀ hε₁] at h1
    linarith
  exact meanEquation_of_moments hW hb0.le hb1.le σ hX E (le_trans hη.le hz) hinv
    (meq_sq_integrable_of_eLpNorm (hmom 2 (by norm_num) h2))

/-!
## 6. Block and scalar corollaries
-/

/-- The top (physical) block of `𝒟 - 𝒮_{c,b}(g)`:
`-E - X - diag(c g_a + b Σ_{j ~ a} g_{port j})`. Its inverse is the `M̄` of
the layer-contraction lemma. -/
def meqTop (σ : LayerShape) (E : ℝ) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (c b : ℂ)
    (gA : Fin σ.blocks → ℂ) (gP : Fin σ.ports → ℂ) : Matrix (PhysSite W σ) (PhysSite W σ) ℂ :=
  -((E : ℂ) • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)) - X -
    diagonal (fun x => c * gA x.1 + b * ∑ j, meqInc σ x.1 j * gP j)

/-- The port coefficient `z - b Σ_{a ~ j} g_a` of `𝒟 - 𝒮_{c,b}(g)` on port `j`. -/
def meqPortCoef (σ : LayerShape) (z b : ℂ) (gA : Fin σ.blocks → ℂ) (j : Fin σ.ports) : ℂ :=
  z - b * ∑ a, meqInc σ a j * gA a

theorem meq_D_fromBlocks (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (c b : ℂ)
    (gA : Fin σ.blocks → ℂ) (gP : Fin σ.ports → ℂ) :
    tflConst σ E z X - meqShift σ c b gA gP =
      fromBlocks (meqTop σ E X c b gA gP) 0 0
        (diagonal fun y : PortSite W σ => meqPortCoef σ z b gA y.1) := by
  ext p q
  rcases p with p | p <;> rcases q with q | q <;>
    simp [tflConst, meqShift, meqTop, meqPortCoef, diagonal_apply, Matrix.one_apply,
      Matrix.sub_apply]
  all_goals (split_ifs <;> simp [mul_comm])

/-- The two diagonal blocks of a mean equation `(𝒟 - 𝒮_{c,b}(g)) Ḡ = I + R`. -/
theorem meq_blocks {σ : LayerShape} {E : ℝ} {z : ℂ} {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ}
    {c b : ℂ} {gA : Fin σ.blocks → ℂ} {gP : Fin σ.ports → ℂ}
    {Gbar R : Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (h : (tflConst σ E z X - meqShift σ c b gA gP) * Gbar = 1 + R) :
    meqTop σ E X c b gA gP * Gbar.toBlocks₁₁ = 1 + R.toBlocks₁₁ ∧
      ∀ y : PortSite W σ, meqPortCoef σ z b gA y.1 * Gbar (Sum.inr y) (Sum.inr y) =
        1 + R (Sum.inr y) (Sum.inr y) := by
  rw [meq_D_fromBlocks, ← fromBlocks_toBlocks Gbar, fromBlocks_multiply] at h
  constructor
  · have h1 := congrArg Matrix.toBlocks₁₁ h
    simp only [toBlocks_fromBlocks₁₁, Matrix.zero_mul, add_zero] at h1
    rw [h1]
    ext p q
    simp [toBlocks₁₁, Matrix.one_apply]
  · intro y
    have h1 := congrFun (congrFun h (Sum.inr y)) (Sum.inr y)
    simpa [fromBlocks, toBlocks₂₂, diagonal_mul, Matrix.one_apply] using h1

/-- **Port scalar equation**: `(z - b Σ_{a~j} g_a) W⁻¹Tr Q_j Ḡ = 1 + W⁻¹ Tr Q_j R`. -/
theorem meq_port_scalar (hW : 0 < W) {σ : LayerShape} {E : ℝ} {z : ℂ}
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ}
    {c b : ℂ} {gA : Fin σ.blocks → ℂ} {gP : Fin σ.ports → ℂ}
    {Gbar R : Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (h : (tflConst σ E z X - meqShift σ c b gA gP) * Gbar = 1 + R) (j : Fin σ.ports) :
    meqPortCoef σ z b gA j * portBlockTrace Gbar j = 1 + portBlockTrace R j := by
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  have h2 := (meq_blocks h).2
  unfold portBlockTrace
  rw [mul_left_comm, Finset.mul_sum]
  simp only [fun α => h2 (j, α)]
  rw [Finset.sum_add_distrib, mul_add]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [inv_mul_cancel₀ hW']

/-- `W⁻¹ Tr P_a M = blockTrace (toBlocks₁₁ M) a`. -/
theorem meq_physBlockTrace_eq_blockTrace (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (a : Fin σ.blocks) : physBlockTrace M a = blockTrace M.toBlocks₁₁ a := rfl

/-- **Top scalar equation**: if `T = -E - X - diag(c g_a + b Σ_{j~a} g_{port j})` is invertible,
then `W⁻¹ Tr P_a Ḡ = W⁻¹ Tr (T⁻¹)_{aa} + W⁻¹ Tr (T⁻¹ R_{phys})_{aa}`. -/
theorem meq_top_scalar {σ : LayerShape} {E : ℝ} {z : ℂ}
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ}
    {c b : ℂ} {gA : Fin σ.blocks → ℂ} {gP : Fin σ.ports → ℂ}
    {Gbar R : Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (h : (tflConst σ E z X - meqShift σ c b gA gP) * Gbar = 1 + R)
    (hT : IsUnit (meqTop σ E X c b gA gP).det) (a : Fin σ.blocks) :
    physBlockTrace Gbar a = blockTrace (meqTop σ E X c b gA gP)⁻¹ a +
      blockTrace ((meqTop σ E X c b gA gP)⁻¹ * R.toBlocks₁₁) a := by
  have h1 := (meq_blocks h).1
  have h2 : Gbar.toBlocks₁₁ = (meqTop σ E X c b gA gP)⁻¹ * (1 + R.toBlocks₁₁) := by
    rw [← h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hT, Matrix.one_mul]
  rw [meq_physBlockTrace_eq_blockTrace, h2, Matrix.mul_add, Matrix.mul_one]
  unfold blockTrace
  rw [← mul_add, ← Finset.sum_add_distrib]
  rfl

/-!
## 7. The residual on the diagonal blocks
-/

section Residual

variable {Ω : Type*} [MeasurableSpace Ω]

theorem meq_cov_apply {ι : Type*} (ν : Measure Ω) (f : Ω → ℂ) (U : Ω → Matrix ι ι ℂ) (x y : ι) :
    meqCov ν f U x y = (∫ ω, f ω * U ω x y ∂ν) - (∫ ω, f ω ∂ν) * ∫ ω, U ω x y ∂ν := by
  simp [meqCov, matrixExpect]

theorem meq_cov_apply_eq_zero {ι : Type*} (ν : Measure Ω) (f : Ω → ℂ) {U : Ω → Matrix ι ι ℂ}
    {x y : ι} (h : ∀ ω, U ω x y = 0) : meqCov ν f U x y = 0 := by
  simp [meq_cov_apply, h]

theorem meq_physProj_mul_inr (a : Fin σ.blocks) (U : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (p : PortSite W σ) (y : LayerSite W σ) :
    (meqPhysProj a * U : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (Sum.inr p) y = 0 := by
  simp [meqPhysProj, diagonal_mul]

theorem meq_portProj_mul_inl (j : Fin σ.ports) (U : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (p : PhysSite W σ) (y : LayerSite W σ) :
    (meqPortProj j * U : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (Sum.inl p) y = 0 := by
  simp [meqPortProj, diagonal_mul]

theorem meq_portProj_mul_inr (j : Fin σ.ports) (U : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (p : PortSite W σ) (y : LayerSite W σ) :
    (meqPortProj j * U : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (Sum.inr p) y =
      if p.1 = j then U (Sum.inr p) y else 0 := by
  simp [meqPortProj, diagonal_mul]

/-- The physical-block residual (the `Q_j` terms vanish on the physical rows):
`(Σ_a c Cov(g_a, P_a G) + Σ_{a~j} b Cov(g_{port j}, P_a G))_{phys, phys}`. -/
def meqResidTop (ν : Measure Ω) (c b : ℂ) (G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    Matrix (PhysSite W σ) (PhysSite W σ) ℂ :=
  (∑ a, c • meqCov ν (fun ω => physBlockTrace (G ω) a) (fun ω => meqPhysProj a * G ω) +
    ∑ a, ∑ j, (b * meqInc σ a j) •
      meqCov ν (fun ω => portBlockTrace (G ω) j) (fun ω => meqPhysProj a * G ω)).toBlocks₁₁

theorem meq_resid_toBlocks11 (ν : Measure Ω) (c b : ℂ)
    (G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    (meqResid ν c b G).toBlocks₁₁ = meqResidTop ν c b G := by
  ext p q
  have h0 : ∀ a j, meqCov ν (fun ω => physBlockTrace (G ω) a) (fun ω => meqPortProj j * G ω)
      (Sum.inl p) (Sum.inl q) = 0 := fun a j =>
    meq_cov_apply_eq_zero ν _ fun ω => meq_portProj_mul_inl j (G ω) p _
  simp [meqResid, meqResidTop, toBlocks₁₁, Matrix.sum_apply, h0]

/-- The port-block residual: `W⁻¹ Tr Q_j R = b Σ_{a~j} W⁻¹ Tr Q_j Cov(g_a, Q_j G)`. -/
theorem meq_resid_port (ν : Measure Ω) (c b : ℂ)
    (G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (j : Fin σ.ports) :
    portBlockTrace (meqResid ν c b G) j = b * ∑ a, meqInc σ a j *
      portBlockTrace (meqCov ν (fun ω => physBlockTrace (G ω) a)
        (fun ω => meqPortProj j * G ω)) j := by
  have h1 : ∀ a (α : Fin W), meqCov ν (fun ω => physBlockTrace (G ω) a)
      (fun ω => meqPhysProj a * G ω) (Sum.inr (j, α)) (Sum.inr (j, α)) = 0 := fun a α =>
    meq_cov_apply_eq_zero ν _ fun ω => meq_physProj_mul_inr a (G ω) _ _
  have h2 : ∀ a (j' : Fin σ.ports) (α : Fin W), meqCov ν (fun ω => portBlockTrace (G ω) j')
      (fun ω => meqPhysProj a * G ω) (Sum.inr (j, α)) (Sum.inr (j, α)) = 0 := fun a j' α =>
    meq_cov_apply_eq_zero ν _ fun ω => meq_physProj_mul_inr a (G ω) _ _
  have h3 : ∀ a (j' : Fin σ.ports) (α : Fin W), j' ≠ j →
      meqCov ν (fun ω => physBlockTrace (G ω) a) (fun ω => meqPortProj j' * G ω)
        (Sum.inr (j, α)) (Sum.inr (j, α)) = 0 := by
    intro a j' α hj
    exact meq_cov_apply_eq_zero ν _ fun ω => by
      rw [meq_portProj_mul_inr]; simp [Ne.symm hj]
  have hentry : ∀ α : Fin W, meqResid ν c b G (Sum.inr (j, α)) (Sum.inr (j, α)) =
      ∑ a, (b * meqInc σ a j) * meqCov ν (fun ω => physBlockTrace (G ω) a)
        (fun ω => meqPortProj j * G ω) (Sum.inr (j, α)) (Sum.inr (j, α)) := by
    intro α
    simp only [meqResid, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, h1,
      h2, mul_zero, Finset.sum_const_zero, zero_add]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single j]
    · intro j' _ hj'
      rw [h3 a j' α hj', mul_zero]
    · simp
  unfold portBlockTrace
  simp only [hentry]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun α _ => ?_
  ring

end Residual

/-- The normalized port trace as a continuous linear map. -/
def meqPortTraceCLM (j : Fin σ.ports) : Matrix (LayerSite W σ) (LayerSite W σ) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => portBlockTrace M j
      map_add' := fun M N => by
        simp [portBlockTrace, Finset.sum_add_distrib, mul_add]
      map_smul' := fun r M => by
        simp [portBlockTrace, Finset.mul_sum, mul_left_comm] }

/-- The normalized physical trace as a continuous linear map. -/
def meqPhysTraceCLM (a : Fin σ.blocks) : Matrix (LayerSite W σ) (LayerSite W σ) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => physBlockTrace M a
      map_add' := fun M N => by
        simp [physBlockTrace, Finset.sum_add_distrib, mul_add]
      map_smul' := fun r M => by
        simp [physBlockTrace, Finset.mul_sum, mul_left_comm] }

theorem meq_portBlockTrace_matrixExpect {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hGi : Integrable G ν) (j : Fin σ.ports) :
    portBlockTrace (matrixExpect ν G) j = meqMeanP ν G j := by
  rw [meq_matrixExpect_eq hGi, meqMeanP]
  exact ((meqPortTraceCLM j).integral_comp_comm hGi).symm

theorem meq_physBlockTrace_matrixExpect {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hGi : Integrable G ν)
    (a : Fin σ.blocks) :
    physBlockTrace (matrixExpect ν G) a = meqMeanA ν G a := by
  rw [meq_matrixExpect_eq hGi, meqMeanA]
  exact ((meqPhysTraceCLM a).integral_comp_comm hGi).symm

theorem meq_integrable_resolvent {W : ℕ} {b : ℝ} {σ : LayerShape} {E : ℝ} {z : ℂ}
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ}
    (hG2 : Integrable (fun ω => ‖layerResolvent σ E z X ω‖ ^ 2) (layerLaw W b σ)) :
    Integrable (layerResolvent σ E z X) (layerLaw W b σ) :=
  Integrable.mono'
    (meq_integrable_norm_of_sq (measurable_layerResolvent σ E z X).aestronglyMeasurable hG2)
    (measurable_layerResolvent σ E z X).aestronglyMeasurable (ae_of_all _ fun _ => le_rfl)

/-- **(3a) Port scalar mean equation** (exact, `κ = 0`): for every port `j`,
`(z - b Σ_{a~j} ḡ_a) ḡ_{port j} = 1 + b Σ_{a~j} W⁻¹ Tr Q_j Cov(g_a, Q_j 𝒢)`. -/
theorem meanEquation_port {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (σ : LayerShape) {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (E : ℝ)
    {z : ℂ} (hz : 0 ≤ z.im)
    (hinv : ∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det)
    (hG2 : Integrable (fun ω => ‖layerResolvent σ E z X ω‖ ^ 2) (layerLaw W b σ))
    (j : Fin σ.ports) :
    meqPortCoef σ z b (meqMeanA (layerLaw W b σ) (layerResolvent σ E z X)) j *
        meqMeanP (layerLaw W b σ) (layerResolvent σ E z X) j =
      1 + b * ∑ a, meqInc σ a j * portBlockTrace (meqCov (layerLaw W b σ)
        (fun ω => physBlockTrace (layerResolvent σ E z X ω) a)
        (fun ω => meqPortProj j * layerResolvent σ E z X ω)) j := by
  have h := meanEquation_of_moments hW hb0 hb1 σ hX E hz hinv hG2
  have h1 := meq_port_scalar hW h j
  rwa [meq_resid_port, meq_portBlockTrace_matrixExpect (meq_integrable_resolvent hG2)] at h1

/-- **(3b) Top scalar mean equation** (exact, `κ = 0`): with
`M̄ = (-E - X - diag(c ḡ_a + b Σ_{j~a} ḡ_{port j}))⁻¹` (`c = 1 - 2b`) invertible,
`ḡ_a = W⁻¹ Tr M̄_{aa} + W⁻¹ Tr (M̄ R_{phys})_{aa}`,
`R_{phys} = (Σ_a c Cov(g_a, P_a 𝒢) + Σ_{a~j} b Cov(g_{port j}, P_a 𝒢))_{phys,phys}`. -/
theorem meanEquation_top {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (σ : LayerShape) {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (E : ℝ)
    {z : ℂ} (hz : 0 ≤ z.im)
    (hinv : ∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det)
    (hG2 : Integrable (fun ω => ‖layerResolvent σ E z X ω‖ ^ 2) (layerLaw W b σ))
    (hT : IsUnit (meqTop σ E X (1 - 2 * (b : ℂ)) b
      (meqMeanA (layerLaw W b σ) (layerResolvent σ E z X))
      (meqMeanP (layerLaw W b σ) (layerResolvent σ E z X))).det) (a : Fin σ.blocks) :
    meqMeanA (layerLaw W b σ) (layerResolvent σ E z X) a =
      blockTrace (meqTop σ E X (1 - 2 * (b : ℂ)) b
        (meqMeanA (layerLaw W b σ) (layerResolvent σ E z X))
        (meqMeanP (layerLaw W b σ) (layerResolvent σ E z X)))⁻¹ a +
      blockTrace ((meqTop σ E X (1 - 2 * (b : ℂ)) b
        (meqMeanA (layerLaw W b σ) (layerResolvent σ E z X))
        (meqMeanP (layerLaw W b σ) (layerResolvent σ E z X)))⁻¹ *
          meqResidTop (layerLaw W b σ) (1 - 2 * (b : ℂ)) b (layerResolvent σ E z X)) a := by
  have h := meanEquation_of_moments hW hb0 hb1 σ hX E hz hinv hG2
  have h1 := meq_top_scalar h hT a
  rwa [meq_resid_toBlocks11, meq_physBlockTrace_matrixExpect (meq_integrable_resolvent hG2)] at h1

/-!
## 8. The two shapes consumed by the layer-contraction lemma
-/

theorem meq_sum_inc_separate_port (gA : Fin LayerShape.separate.blocks → ℂ)
    (j : Fin LayerShape.separate.ports) :
    ∑ a : Fin LayerShape.separate.blocks, meqInc .separate a j * gA a = gA j := by
  fin_cases j <;> simp [meqInc, LayerShape.incident, Fin.sum_univ_two]

theorem meq_sum_inc_separate_phys (gP : Fin LayerShape.separate.ports → ℂ)
    (a : Fin LayerShape.separate.blocks) :
    ∑ j : Fin LayerShape.separate.ports, meqInc .separate a j * gP j = gP a := by
  fin_cases a <;> simp [meqInc, LayerShape.incident, Fin.sum_univ_two]

theorem meq_sum_inc_common_port (gA : Fin LayerShape.common.blocks → ℂ)
    (j : Fin LayerShape.common.ports) :
    ∑ a : Fin LayerShape.common.blocks, meqInc .common a j * gA a = gA 0 + gA 1 := by
  simp [meqInc, LayerShape.incident, Fin.sum_univ_two]

theorem meq_sum_inc_common_phys (gP : Fin LayerShape.common.ports → ℂ)
    (a : Fin LayerShape.common.blocks) :
    ∑ j : Fin LayerShape.common.ports, meqInc .common a j * gP j = gP 0 := by
  simp [meqInc, LayerShape.incident]

/-- Separate ports: `𝒟 - 𝒮` on the physical block is `-E - X - diag(c ḡ_a + b ḡ_{port a})`. -/
theorem meqTop_separate (E : ℝ) (X : Matrix (PhysSite W .separate) (PhysSite W .separate) ℂ)
    (c b : ℂ) (gA : Fin LayerShape.separate.blocks → ℂ) (gP : Fin LayerShape.separate.ports → ℂ) :
    meqTop .separate E X c b gA gP =
      -((E : ℂ) • (1 : Matrix (PhysSite W .separate) (PhysSite W .separate) ℂ)) - X -
        diagonal (fun x => c * gA x.1 + b * gP x.1) := by
  unfold meqTop
  congr 2
  funext x
  rw [meq_sum_inc_separate_phys]

/-- Common port: `𝒟 - 𝒮` on the physical block is `-E - X - diag(c ḡ_a + b ḡ_port)`. -/
theorem meqTop_common (E : ℝ) (X : Matrix (PhysSite W .common) (PhysSite W .common) ℂ)
    (c b : ℂ) (gA : Fin LayerShape.common.blocks → ℂ) (gP : Fin LayerShape.common.ports → ℂ) :
    meqTop .common E X c b gA gP =
      -((E : ℂ) • (1 : Matrix (PhysSite W .common) (PhysSite W .common) ℂ)) - X -
        diagonal (fun x => c * gA x.1 + b * gP 0) := by
  unfold meqTop
  congr 2
  funext x
  rw [meq_sum_inc_common_phys]

/-- **Separate ports, port equation**: `(z - b ḡ_a) ḡ_{port a} = 1 + b W⁻¹ Tr Q_a Cov(g_a, Q_a 𝒢)`
for `a = 0, 1` (exact, `κ = 0`). -/
theorem meanEquation_separate_port {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1 / 2) {X : Matrix (PhysSite W .separate) (PhysSite W .separate) ℂ}
    (hX : X.IsHermitian) (E : ℝ) {z : ℂ} (hz : 0 ≤ z.im)
    (hinv : ∀ᵐ ω ∂layerLaw W b .separate, IsUnit (layerMatrix .separate E z X ω).det)
    (hG2 : Integrable (fun ω => ‖layerResolvent .separate E z X ω‖ ^ 2) (layerLaw W b .separate))
    (j : Fin LayerShape.separate.ports) :
    (z - b * meqMeanA (layerLaw W b .separate) (layerResolvent .separate E z X) j) *
        meqMeanP (layerLaw W b .separate) (layerResolvent .separate E z X) j =
      1 + b * portBlockTrace (meqCov (layerLaw W b .separate)
        (fun ω => physBlockTrace (layerResolvent .separate E z X ω) j)
        (fun ω => meqPortProj (σ := .separate) j * layerResolvent .separate E z X ω)) j := by
  have h := meanEquation_port hW hb0 hb1 .separate hX E hz hinv hG2 j
  rw [meqPortCoef, meq_sum_inc_separate_port, meq_sum_inc_separate_port] at h
  exact h

/-- **Common port, port equation**:
`(z - b(ḡ₀ + ḡ₁)) ḡ_port = 1 + b W⁻¹ Tr Q (Cov(g₀, Q 𝒢) + Cov(g₁, Q 𝒢))` (exact, `κ = 0`). -/
theorem meanEquation_common_port {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1 / 2) {X : Matrix (PhysSite W .common) (PhysSite W .common) ℂ}
    (hX : X.IsHermitian) (E : ℝ) {z : ℂ} (hz : 0 ≤ z.im)
    (hinv : ∀ᵐ ω ∂layerLaw W b .common, IsUnit (layerMatrix .common E z X ω).det)
    (hG2 : Integrable (fun ω => ‖layerResolvent .common E z X ω‖ ^ 2) (layerLaw W b .common)) :
    (z - b * (meqMeanA (layerLaw W b .common) (layerResolvent .common E z X) 0 +
          meqMeanA (layerLaw W b .common) (layerResolvent .common E z X) 1)) *
        meqMeanP (layerLaw W b .common) (layerResolvent .common E z X) 0 =
      1 + b * (portBlockTrace (meqCov (layerLaw W b .common)
          (fun ω => physBlockTrace (layerResolvent .common E z X ω) 0)
          (fun ω => meqPortProj 0 * layerResolvent .common E z X ω)) 0 +
        portBlockTrace (meqCov (layerLaw W b .common)
          (fun ω => physBlockTrace (layerResolvent .common E z X ω) 1)
          (fun ω => meqPortProj 0 * layerResolvent .common E z X ω)) 0) := by
  have h := meanEquation_port hW hb0 hb1 .common hX E hz hinv hG2 0
  rw [meqPortCoef, meq_sum_inc_common_port, meq_sum_inc_common_port] at h
  exact h

/-- **Separate ports, top equation**: with
`M̄ = (-E - X - diag(c ḡ_a + b ḡ_{port a}))⁻¹` invertible (`c = 1 - 2b`),
`ḡ_a = W⁻¹ Tr M̄_{aa} + W⁻¹ Tr (M̄ R_{phys})_{aa}` (exact, `κ = 0`). -/
theorem meanEquation_separate_top {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1 / 2) {X : Matrix (PhysSite W .separate) (PhysSite W .separate) ℂ}
    (hX : X.IsHermitian) (E : ℝ) {z : ℂ} (hz : 0 ≤ z.im)
    (hinv : ∀ᵐ ω ∂layerLaw W b .separate, IsUnit (layerMatrix .separate E z X ω).det)
    (hG2 : Integrable (fun ω => ‖layerResolvent .separate E z X ω‖ ^ 2) (layerLaw W b .separate))
    (hT : IsUnit (-((E : ℂ) • (1 : Matrix (PhysSite W .separate) (PhysSite W .separate) ℂ)) - X -
      diagonal (fun x : PhysSite W .separate => (1 - 2 * (b : ℂ)) *
        meqMeanA (layerLaw W b .separate) (layerResolvent .separate E z X) x.1 +
          b * meqMeanP (layerLaw W b .separate) (layerResolvent .separate E z X) x.1)).det)
    (a : Fin LayerShape.separate.blocks) :
    meqMeanA (layerLaw W b .separate) (layerResolvent .separate E z X) a =
      blockTrace (-((E : ℂ) • (1 : Matrix (PhysSite W .separate) (PhysSite W .separate) ℂ)) - X -
        diagonal (fun x : PhysSite W .separate => (1 - 2 * (b : ℂ)) *
          meqMeanA (layerLaw W b .separate) (layerResolvent .separate E z X) x.1 +
            b * meqMeanP (layerLaw W b .separate) (layerResolvent .separate E z X) x.1))⁻¹ a +
      blockTrace ((-((E : ℂ) • (1 : Matrix (PhysSite W .separate) (PhysSite W .separate) ℂ)) - X -
        diagonal (fun x : PhysSite W .separate => (1 - 2 * (b : ℂ)) *
          meqMeanA (layerLaw W b .separate) (layerResolvent .separate E z X) x.1 +
            b * meqMeanP (layerLaw W b .separate) (layerResolvent .separate E z X) x.1))⁻¹ *
          meqResidTop (layerLaw W b .separate) (1 - 2 * (b : ℂ)) b
            (layerResolvent .separate E z X)) a := by
  rw [← meqTop_separate] at hT ⊢
  exact meanEquation_top hW hb0 hb1 .separate hX E hz hinv hG2 hT a

/-- **Common port, top equation**: with `M̄ = (-E - X - diag(c ḡ_a + b ḡ_port))⁻¹` invertible,
`ḡ_a = W⁻¹ Tr M̄_{aa} + W⁻¹ Tr (M̄ R_{phys})_{aa}` (exact, `κ = 0`). -/
theorem meanEquation_common_top {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1 / 2) {X : Matrix (PhysSite W .common) (PhysSite W .common) ℂ}
    (hX : X.IsHermitian) (E : ℝ) {z : ℂ} (hz : 0 ≤ z.im)
    (hinv : ∀ᵐ ω ∂layerLaw W b .common, IsUnit (layerMatrix .common E z X ω).det)
    (hG2 : Integrable (fun ω => ‖layerResolvent .common E z X ω‖ ^ 2) (layerLaw W b .common))
    (hT : IsUnit (-((E : ℂ) • (1 : Matrix (PhysSite W .common) (PhysSite W .common) ℂ)) - X -
      diagonal (fun x : PhysSite W .common => (1 - 2 * (b : ℂ)) *
        meqMeanA (layerLaw W b .common) (layerResolvent .common E z X) x.1 +
          b * meqMeanP (layerLaw W b .common) (layerResolvent .common E z X) 0)).det)
    (a : Fin LayerShape.common.blocks) :
    meqMeanA (layerLaw W b .common) (layerResolvent .common E z X) a =
      blockTrace (-((E : ℂ) • (1 : Matrix (PhysSite W .common) (PhysSite W .common) ℂ)) - X -
        diagonal (fun x : PhysSite W .common => (1 - 2 * (b : ℂ)) *
          meqMeanA (layerLaw W b .common) (layerResolvent .common E z X) x.1 +
            b * meqMeanP (layerLaw W b .common) (layerResolvent .common E z X) 0))⁻¹ a +
      blockTrace ((-((E : ℂ) • (1 : Matrix (PhysSite W .common) (PhysSite W .common) ℂ)) - X -
        diagonal (fun x : PhysSite W .common => (1 - 2 * (b : ℂ)) *
          meqMeanA (layerLaw W b .common) (layerResolvent .common E z X) x.1 +
            b * meqMeanP (layerLaw W b .common) (layerResolvent .common E z X) 0))⁻¹ *
          meqResidTop (layerLaw W b .common) (1 - 2 * (b : ℂ)) b
            (layerResolvent .common E z X)) a := by
  rw [← meqTop_common] at hT ⊢
  exact meanEquation_top hW hb0 hb1 .common hX E hz hinv hG2 hT a

/-!
## 9. Interface with `TraceMatrixContract.covariance`
-/

/-- `‖P_a‖ ≤ 1`. -/
theorem meq_norm_physProj_le (a : Fin σ.blocks) :
    ‖(meqPhysProj a : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)‖ ≤ 1 := by
  rw [meqPhysProj, l2_opNorm_diagonal]
  refine pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun x => ?_
  rcases x with x | x <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> (try split_ifs) <;> simp

/-- `‖Q_j‖ ≤ 1`. -/
theorem meq_norm_portProj_le (j : Fin σ.ports) :
    ‖(meqPortProj j : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)‖ ≤ 1 := by
  rw [meqPortProj, l2_opNorm_diagonal]
  refine pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun x => ?_
  rcases x with x | x <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> (try split_ifs) <;> simp

/-- `P M` is the one-letter word `P · M · 1`. -/
theorem meq_mul_eq_wordEval (P M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    P * M = wordEval (ℓ := 1) (fun _ => false) ![P, 1] M := by
  simp [wordEval]

/-- `g_a = W⁻¹ Tr (P_a 𝒢)` is the normalized trace of a one-letter word. -/
theorem meq_physBlockTrace_eq_word (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (a : Fin σ.blocks) :
    physBlockTrace M a =
      (W : ℂ)⁻¹ * (wordEval (ℓ := 1) (fun _ => false) ![meqPhysProj a, 1] M).trace := by
  rw [← meq_mul_eq_wordEval]
  simp only [physBlockTrace, Matrix.trace, meqPhysProj, diagonal_mul, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Matrix.diag_apply, Sum.elim_inl, Sum.elim_inr, zero_mul,
    Finset.sum_const_zero, add_zero, ite_mul, one_mul]
  congr 1
  rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp)]
  simp

/-- `g_{port j} = W⁻¹ Tr (Q_j 𝒢)` is the normalized trace of a one-letter word. -/
theorem meq_portBlockTrace_eq_word (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (j : Fin σ.ports) :
    portBlockTrace M j =
      (W : ℂ)⁻¹ * (wordEval (ℓ := 1) (fun _ => false) ![meqPortProj j, 1] M).trace := by
  rw [← meq_mul_eq_wordEval]
  simp only [portBlockTrace, Matrix.trace, meqPortProj, diagonal_mul, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Matrix.diag_apply, Sum.elim_inl, Sum.elim_inr, zero_mul,
    Finset.sum_const_zero, zero_add, ite_mul, one_mul]
  congr 1
  rw [Finset.sum_eq_single j (fun x _ hx => by simp [hx]) (by simp)]
  simp

end BlockBand.Layers
